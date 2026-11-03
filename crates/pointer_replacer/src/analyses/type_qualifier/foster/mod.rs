//! Foster style flow-insensitive type qualifier inference algorithm

pub use constraint_system::{BooleanLattice, Var};
use rustc_hir::LangItem;
use rustc_index::IndexVec;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    sym,
};
use rustc_type_ir::TyKind;

use crate::{
    analyses::{
        encoding,
        encoding::{encode_fns, encode_structs},
    },
    utils::rustc::RustProgram,
};

pub mod constraint_system;
pub mod fatness;
pub mod mutability;

#[cfg(test)]
mod tests;

pub struct StructFields {
    fields: encoding::StructFields<Var>,
    carriers: PointerCarriers,
}

impl StructFields {
    pub fn fields(&self, did: LocalDefId) -> impl Iterator<Item = std::ops::Range<Var>> + '_ {
        self.fields.fields(did)
    }

    pub fn count_ptr(&self, ty: Ty<'_>) -> usize {
        count_ptr(ty, self.carriers)
    }

    pub fn is_pointer_carrier(&self, ty: Ty<'_>) -> bool {
        self.carriers.is_carrier(ty)
    }

    pub fn preserves_carrier_cast<'tcx>(&self, source: Ty<'tcx>, target: Ty<'tcx>) -> bool {
        self.carriers.preserves_cast(source, target)
    }
}

#[derive(Clone, Copy)]
struct PointerCarriers {
    unique: Option<DefId>,
    non_null: Option<DefId>,
}

impl PointerCarriers {
    fn is_carrier(self, ty: Ty<'_>) -> bool {
        ty.is_box()
            || matches!(ty.kind(), TyKind::Adt(adt, _) if Some(adt.did()) == self.unique || Some(adt.did()) == self.non_null)
    }

    fn pointee(self, ty: Ty<'_>) -> Option<Ty<'_>> {
        if let Some(inner) = ty.builtin_deref(true) {
            return Some(inner);
        }
        let TyKind::Adt(_, arguments) = ty.kind() else { return None };
        self.is_carrier(ty).then(|| arguments.type_at(0))
    }

    fn preserves_cast<'tcx>(self, source: Ty<'tcx>, target: Ty<'tcx>) -> bool {
        (self.is_carrier(source) || self.is_carrier(target))
            && self
                .pointee(source)
                .is_some_and(|pointee| Some(pointee) == self.pointee(target))
    }
}

pub type FnLocals = encoding::FnLocals<Var>;

pub struct TypeQualifiers<Qualifier> {
    pub struct_fields: StructFields,
    pub fn_locals: FnLocals,
    pub model: IndexVec<Var, Qualifier>,
}

fn count_ptr(mut ty: Ty, carriers: PointerCarriers) -> usize {
    let mut cnt = 0;
    loop {
        if let Some(inner_ty) = carriers.pointee(ty) {
            cnt += 1;
            ty = inner_ty;
            continue;
        }
        if let Some(inner_ty) = ty.builtin_index() {
            ty = inner_ty;
            continue;
        }
        if let TyKind::Tuple(tys) = ty.kind() {
            return cnt + tys.iter().map(|t| count_ptr(t, carriers)).sum::<usize>();
        }
        break cnt;
    }
}

impl<Domain> TypeQualifiers<Domain>
where Domain: BooleanLattice
{
    /// construct a new `TypeQualifiers` instance with no constraints added
    pub fn new_empty(rust_program: &RustProgram) -> Self {
        let tcx = rust_program.tcx;
        let fns = &rust_program.functions[..];
        let structs = &rust_program.structs[..];
        let carriers = PointerCarriers {
            unique: tcx.lang_items().get(LangItem::PtrUnique),
            non_null: tcx.get_diagnostic_item(sym::NonNull),
        };

        let mut model = IndexVec::new();
        // not necessary, but need initialization anyway
        model.push(Domain::TOP);
        model.push(Domain::BOTTOM);
        let next: Var = model.next_index();

        let (struct_fields, next) = encode_structs(next, structs, tcx, |field_ty| {
            let num_ptrs = count_ptr(field_ty, carriers);
            model.extend(std::iter::repeat_n(Domain::BOTTOM, num_ptrs));
            num_ptrs
        });
        let (fn_locals, _) = encode_fns(next, fns, tcx, |local_ty| {
            let num_ptrs = count_ptr(local_ty, carriers);
            model.extend(std::iter::repeat_n(Domain::BOTTOM, num_ptrs));
            num_ptrs
        });

        Self {
            struct_fields: StructFields {
                fields: struct_fields,
                carriers,
            },
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
    pub local_decls: &'infer D,
    pub locals: &'infer [Var],
    pub fn_locals: &'infer FnLocals,
    pub struct_fields: &'infer StructFields,
    pub tcx: TyCtxt<'tcx>,
}
