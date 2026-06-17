//! Foster style flow-insensitive type qualifier inference algorithm

use std::ops::Range;

use constraint_system::{BooleanLattice, Var};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_index::IndexVec;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::def_id::LocalDefId;
use rustc_type_ir::TyKind;

use crate::{
    analyses::{
        encoding,
        encoding::{encode_fns, encode_structs},
    },
    utils::rustc::RustProgram,
};

mod constraint_system;
pub mod fatness;
pub mod mutability;

pub type StructFields = encoding::StructFields<Var>;
pub type FnLocals = encoding::FnLocals<Var>;

pub struct TypeQualifiers<Qualifier> {
    struct_fields: StructFields,
    fn_locals: FnLocals,
    model: IndexVec<Var, Qualifier>,
}

fn count_ptr<'tcx>(tcx: TyCtxt<'tcx>, mut ty: Ty<'tcx>) -> usize {
    let mut cnt = 0;
    loop {
        if let Some(inner_ty) = ty.builtin_deref(true) {
            cnt += 1;
            ty = inner_ty;
            continue;
        }
        if let Some(inner_ty) = ty.builtin_index() {
            ty = inner_ty;
            continue;
        }
        match ty.kind() {
            TyKind::Tuple(tys) => {
                return cnt + tys.iter().map(|t| count_ptr(tcx, t)).sum::<usize>();
            }
            TyKind::Adt(adt_def, generic_args) if adt_def.is_enum() => {
                return cnt
                    + adt_def
                        .variants()
                        .iter()
                        .map(|variant| variant_ptr_count(tcx, variant, generic_args))
                        .sum::<usize>();
            }
            _ => {}
        }
        break cnt;
    }
}

fn enum_variant_range<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    generic_args: ty::GenericArgsRef<'tcx>,
    base: Range<Var>,
    variant_idx: VariantIdx,
) -> Range<Var> {
    let offset = adt_def
        .variants()
        .iter()
        .take(variant_idx.index())
        .map(|variant| variant_ptr_count(tcx, variant, generic_args))
        .sum::<usize>();
    let count = variant_ptr_count(tcx, adt_def.variant(variant_idx), generic_args);
    base.start + offset..base.start + offset + count
}

fn enum_variant_field_range<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
    generic_args: ty::GenericArgsRef<'tcx>,
    variant_idx: VariantIdx,
    base: Range<Var>,
    field_idx: FieldIdx,
) -> Range<Var> {
    let variant = adt_def.variant(variant_idx);
    let offset = variant
        .fields
        .iter()
        .take(field_idx.index())
        .map(|field| count_ptr(tcx, field.ty(tcx, generic_args)))
        .sum::<usize>();
    let count = count_ptr(tcx, variant.fields[field_idx].ty(tcx, generic_args));
    base.start + offset..base.start + offset + count
}

fn variant_ptr_count<'tcx>(
    tcx: TyCtxt<'tcx>,
    variant: &ty::VariantDef,
    generic_args: ty::GenericArgsRef<'tcx>,
) -> usize {
    variant
        .fields
        .iter()
        .map(|field| count_ptr(tcx, field.ty(tcx, generic_args)))
        .sum()
}

impl<Domain> TypeQualifiers<Domain>
where Domain: BooleanLattice
{
    /// construct a new `TypeQualifiers` instance with no constraints added
    pub fn new_empty(rust_program: &RustProgram) -> Self {
        let tcx = rust_program.tcx;
        let fns = &rust_program.functions[..];
        let structs = &rust_program.structs[..];

        let mut model = IndexVec::new();
        // not necessary, but need initialization anyway
        model.push(Domain::TOP);
        model.push(Domain::BOTTOM);
        let next: Var = model.next_index();

        let (struct_fields, next) = encode_structs(next, structs, tcx, |field_ty| {
            let num_ptrs = count_ptr(tcx, field_ty);
            model.extend(std::iter::repeat_n(Domain::BOTTOM, num_ptrs));
            num_ptrs
        });
        let (fn_locals, _) = encode_fns(next, fns, tcx, |local_ty| {
            let num_ptrs = count_ptr(tcx, local_ty);
            model.extend(std::iter::repeat_n(Domain::BOTTOM, num_ptrs));
            num_ptrs
        });

        Self {
            struct_fields,
            fn_locals,
            model,
        }
    }
}

impl<Qualifier> TypeQualifiers<Qualifier> {
    #[allow(unused)]
    pub fn function_facts(
        &self,
        did: LocalDefId,
        tcx: TyCtxt,
    ) -> impl Iterator<Item = &[Qualifier]> {
        let body = &*tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        self.fn_locals
            .locals(did)
            .take(body.arg_count + 1)
            .map(|vars| &self.model[vars])
    }

    pub fn function_body_facts(&self, did: LocalDefId) -> impl Iterator<Item = &[Qualifier]> {
        self.fn_locals.locals(did).map(|vars| &self.model[vars])
    }

    pub fn function_body_fact(
        &self,
        did: LocalDefId,
        local_idx: usize,
        offset: usize,
    ) -> Option<Qualifier>
    where
        Qualifier: Copy,
    {
        self.function_body_facts(did)
            .nth(local_idx)
            .and_then(|quals| quals.get(offset))
            .copied()
    }

    #[allow(unused)]
    pub fn struct_facts(&self, did: LocalDefId) -> impl Iterator<Item = &[Qualifier]> {
        self.struct_fields.fields(did).map(|vars| &self.model[vars])
    }

    #[allow(dead_code)]
    pub fn struct_field_fact(
        &self,
        did: LocalDefId,
        field_idx: usize,
        offset: usize,
    ) -> Option<Qualifier>
    where
        Qualifier: Copy,
    {
        self.struct_facts(did)
            .nth(field_idx)
            .and_then(|quals| quals.get(offset))
            .copied()
    }
}

pub struct InferCtxt<'infer, 'tcx, D> {
    local_decls: &'infer D,
    locals: &'infer [Var],
    fn_locals: &'infer FnLocals,
    struct_fields: &'infer StructFields,
    tcx: TyCtxt<'tcx>,
}
