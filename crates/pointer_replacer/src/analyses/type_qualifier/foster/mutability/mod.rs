use std::ops::Range;

use libc::libc_call;
use library::library_call;
use rustc_middle::mir::{
    AggregateKind, BinOp, HasLocalDecls, Location, Operand, Place, ProjectionElem, Rvalue,
    Terminator, visit::Visitor,
};
use rustc_span::source_map::Spanned;
use rustc_type_ir::TyKind;

use crate::{
    analyses::{
        lattice::{HasBottom, HasTop, Lattice},
        mir::{self, CallKind, TerminatorExt},
        type_qualifier::foster::{
            BooleanLattice, InferCtxt, StructFields, TypeQualifiers, Var,
            constraint_system::{BooleanSystem, ConstraintSystem},
        },
    },
    utils::rustc::RustProgram,
};

mod libc;
mod library;
// #[cfg(test)]
// mod test;

pub fn mutability_analysis(rust_program: &RustProgram) -> MutabilityResult {
    let mut result = MutabilityResult::new_empty(rust_program);
    let mut database = BooleanSystem::new(&result.model);
    for r#fn in &rust_program.functions {
        let body = &*rust_program
            .tcx
            .mir_drops_elaborated_and_const_checked(r#fn)
            .borrow();
        let locals = {
            let idx = result.fn_locals.0.did_idx[r#fn];
            &result.fn_locals.0.contents[idx]
        };
        let ctxt = InferCtxt {
            local_decls: body,
            locals,
            fn_locals: &result.fn_locals,
            struct_fields: &result.struct_fields,
            tcx: rust_program.tcx,
        };

        let mut analysis = MutabilityAnalysis {
            ctxt,
            database: &mut database,
        };

        analysis.visit_body(body);
    }
    database.greatest_model(&mut result.model);
    result
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// [`Mutability::Mut`] ⊑ [`Mutability::Imm`]
pub enum Mutability {
    Imm,
    Mut,
}

impl Mutability {
    #[inline]
    pub fn is_mutable(&self) -> bool {
        *self == Mutability::Mut
    }

    #[inline]
    pub fn is_immutable(&self) -> bool {
        *self == Mutability::Imm
    }
}

impl std::fmt::Display for Mutability {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Mutability::Imm => write!(f, "&read"),
            Mutability::Mut => write!(f, "&read_write"),
        }
    }
}

pub type MutabilityResult = TypeQualifiers<Mutability>;

impl From<Mutability> for bool {
    fn from(mutability: Mutability) -> Self {
        mutability == Mutability::Imm
    }
}

impl From<bool> for Mutability {
    fn from(b: bool) -> Self {
        if b { Mutability::Imm } else { Mutability::Mut }
    }
}

impl HasBottom for Mutability {
    const BOTTOM: Self = Self::Mut;
}

impl HasTop for Mutability {
    const TOP: Self = Self::Imm;
}

impl Lattice for Mutability {
    fn join(&mut self, other: &Self) -> bool {
        if let (Self::Mut, Self::Imm) = (*self, *other) {
            *self = Self::Imm;
            return true;
        }
        false
    }

    fn meet(&mut self, other: &Self) -> bool {
        if let (Self::Imm, Self::Mut) = (*self, *other) {
            *self = Self::Mut;
            return true;
        }
        true
    }
}

impl BooleanLattice for Mutability {}

pub struct MutabilityAnalysis<'infer, 'tcx, D> {
    ctxt: InferCtxt<'infer, 'tcx, D>,
    database: &'infer mut BooleanSystem<Mutability>,
}

impl<'infer, 'tcx, D: HasLocalDecls<'tcx>> Visitor<'tcx> for MutabilityAnalysis<'infer, 'tcx, D> {
    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, _location: Location) {
        let lhs = place;
        let rhs = rvalue;

        let InferCtxt {
            local_decls,
            locals,
            fn_locals: _,
            struct_fields,
            tcx,
        } = self.ctxt;
        let database = &mut *self.database;

        match rhs {
            Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs)) | Rvalue::CopyForDeref(rhs) => {
                let Some(lhs) = try_place_vars::<MutCtxt>(
                    lhs,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    database,
                ) else {
                    return;
                };
                let mut rhs_deref = None;
                let Some(rhs) = try_place_vars::<UnknownCtxt>(
                    rhs,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    &mut rhs_deref,
                ) else {
                    make_mut(lhs, database);
                    return;
                };

                // type safety
                assert_eq!(
                    lhs.end.index() - lhs.start.index(),
                    rhs.end.index() - rhs.start.index(),
                    "{:?}: {} = {:?}",
                    place,
                    local_decls.local_decls()[place.local].ty,
                    rvalue
                );

                let mut lhs_rhs = lhs.zip(rhs);
                if let Some((lhs, rhs)) = lhs_rhs.next() {
                    database.guard(lhs, rhs);
                    if let Some(rhs_deref) = rhs_deref {
                        database.guard(lhs, rhs_deref);
                    }
                }
                for (lhs, rhs) in lhs_rhs {
                    database.guard(lhs, rhs);
                    database.guard(rhs, lhs)
                }
            }
            Rvalue::Cast(_, Operand::Copy(rhs) | Operand::Move(rhs), _) => {
                // for cast, we process the head ptr only
                let Some(lhs) = try_place_vars::<MutCtxt>(
                    lhs,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    database,
                ) else {
                    return;
                };
                let mut rhs_deref = None;
                let Some(rhs) = try_place_vars::<UnknownCtxt>(
                    rhs,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    &mut rhs_deref,
                ) else {
                    make_mut(lhs, database);
                    return;
                };

                let mut lhs_rhs = lhs.zip(rhs);
                if let Some((lhs, rhs)) = lhs_rhs.next() {
                    database.guard(lhs, rhs);
                    if let Some(rhs_deref) = rhs_deref {
                        database.guard(lhs, rhs_deref)
                    }
                }
            }
            // We don't do this because mutable borrow does not necessarily means being mutable!
            // Rvalue::Ref(_, BorrowKind::Mut { .. }, rhs) | Rvalue::AddressOf(_, rhs) => {
            //     let lhs =
            //         place_vars::<EnsureNoDeref>(lhs, local_decls, locals, struct_fields, &mut ());
            //     let rhs = place_vars::<MutCtxt>(rhs, local_decls, locals, struct_fields, database);
            //     for (lhs, rhs) in lhs.skip(1).zip(rhs) {
            //         database.guard(lhs, rhs);
            //         database.guard(rhs, lhs);
            //     }
            // }
            Rvalue::BinaryOp(BinOp::Offset, box (ptr, _)) => {
                let Some(dest_vars) = try_place_vars::<MutCtxt>(
                    lhs,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    database,
                ) else {
                    return;
                };
                if let Some(arg) = ptr.place() {
                    let Some(arg_vars) = try_place_vars::<EnsureNoDeref>(
                        &arg,
                        local_decls,
                        locals,
                        struct_fields,
                        tcx,
                        &mut (),
                    ) else {
                        make_mut(dest_vars, database);
                        return;
                    };
                    let mut dest_arg = dest_vars.zip(arg_vars);

                    if let Some((dest, arg)) = dest_arg.next() {
                        database.guard(dest, arg)
                    }
                    for (dest, arg) in dest_arg {
                        database.guard(arg, dest);
                        database.guard(dest, arg);
                    }
                }
            }
            Rvalue::Ref(_, _, rhs) | Rvalue::RawPtr(_, rhs) => {
                let Some(mut lhs) = try_place_vars::<EnsureNoDeref>(
                    lhs,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    &mut (),
                ) else {
                    return;
                };
                let mut rhs_deref = None;
                let lhs_ref = lhs.next().unwrap();
                let Some(rhs) = try_place_vars::<UnknownCtxt>(
                    rhs,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    &mut rhs_deref,
                ) else {
                    database.bottom(lhs_ref);
                    if let Some(rhs_deref) = rhs_deref {
                        database.guard(lhs_ref, rhs_deref);
                    }
                    return;
                };
                if let Some(rhs_deref) = rhs_deref {
                    database.guard(lhs_ref, rhs_deref);
                }
                for (lhs, rhs) in lhs.zip(rhs) {
                    database.guard(lhs, rhs);
                    database.guard(rhs, lhs);
                }
            }
            Rvalue::Aggregate(box AggregateKind::Adt(_, variant_idx, _, _, _), fields) => {
                let Some(lhs_vars) = try_place_vars::<MutCtxt>(
                    lhs,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    database,
                ) else {
                    return;
                };
                let lhs_ty = lhs.ty(local_decls.local_decls(), tcx).ty;
                let TyKind::Adt(adt_def, generic_args) = lhs_ty.kind() else {
                    unreachable!("{lhs_ty:?}")
                };
                if !adt_def.is_enum() {
                    return;
                }
                let variant = adt_def.variant(*variant_idx);
                for ((field_idx, _), field) in variant.fields.iter_enumerated().zip(fields) {
                    let lhs = super::enum_variant_field_range(
                        tcx,
                        *adt_def,
                        generic_args,
                        *variant_idx,
                        lhs_vars.clone(),
                        field_idx,
                    );
                    let Some(rhs) = field.place() else {
                        continue;
                    };
                    let mut rhs_deref = None;
                    let Some(rhs) = try_place_vars::<UnknownCtxt>(
                        &rhs,
                        local_decls,
                        locals,
                        struct_fields,
                        tcx,
                        &mut rhs_deref,
                    ) else {
                        make_mut(lhs, database);
                        continue;
                    };

                    assert_eq!(
                        lhs.end.index() - lhs.start.index(),
                        rhs.end.index() - rhs.start.index(),
                        "{lhs:?}: {lhs_ty} = {field:?}",
                    );

                    let mut lhs_rhs = lhs.zip(rhs);
                    if let Some((lhs, rhs)) = lhs_rhs.next() {
                        database.guard(lhs, rhs);
                        if let Some(rhs_deref) = rhs_deref {
                            database.guard(lhs, rhs_deref);
                        }
                    }
                    for (lhs, rhs) in lhs_rhs {
                        database.guard(lhs, rhs);
                        database.guard(rhs, lhs)
                    }
                }
            }
            _ => {
                let _ = try_place_vars::<MutCtxt>(
                    lhs,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    database,
                );
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, _location: Location) {
        let InferCtxt {
            local_decls,
            locals,
            fn_locals,
            struct_fields,
            tcx,
        } = self.ctxt;
        let database = &mut *self.database;

        if let Some(mir::MirFunctionCall {
            func,
            args,
            ref destination,
        }) = terminator.as_call(tcx)
        {
            match func {
                CallKind::FreeStanding(callee) => {
                    let callee_body = &*tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
                    let mut callee_vars = fn_locals
                        .0
                        .contents_iter(callee)
                        .take(callee_body.arg_count + 1);

                    let dest = try_place_vars::<MutCtxt>(
                        destination,
                        local_decls,
                        locals,
                        struct_fields,
                        tcx,
                        database,
                    );
                    let ret = callee_vars.next().unwrap();

                    if let Some(dest) = dest {
                        // type safety
                        assert_eq!(
                            dest.end.index() - dest.start.index(),
                            ret.end.index() - ret.start.index()
                        );

                        let mut dest_ret = dest.zip(ret);

                        if let Some((dest, ret)) = dest_ret.next() {
                            database.guard(dest, ret)
                        }
                        for (dest, ret) in dest_ret {
                            database.guard(ret, dest);
                            database.guard(dest, ret);
                        }
                    }

                    for (arg, param_vars) in args.iter().zip(callee_vars) {
                        let Some(arg) = arg.node.place() else {
                            continue;
                        };
                        let Some(arg_vars) = try_place_vars::<EnsureNoDeref>(
                            &arg,
                            local_decls,
                            locals,
                            struct_fields,
                            tcx,
                            &mut (),
                        ) else {
                            make_mut(param_vars, database);
                            continue;
                        };

                        let mut param_arg = param_vars.zip(arg_vars);
                        if let Some((param, arg)) = param_arg.next() {
                            database.guard(param, arg);
                        }
                        for (param, arg) in param_arg {
                            database.guard(arg, param);
                            database.guard(param, arg);
                        }
                    }
                }
                CallKind::LibC(ident) => {
                    libc_call(
                        destination,
                        args,
                        ident,
                        local_decls,
                        locals,
                        struct_fields,
                        tcx,
                        database,
                    );
                }
                CallKind::RustLib(callee) => {
                    library_call(
                        destination,
                        args,
                        callee,
                        local_decls,
                        locals,
                        struct_fields,
                        database,
                        tcx,
                    );
                }
                CallKind::Impl(..) | CallKind::Closure | CallKind::Dynamic => conservative_call(
                    destination,
                    args,
                    local_decls,
                    locals,
                    struct_fields,
                    tcx,
                    database,
                ),
            }
        }
    }
}

trait PlaceContext {
    type DerefStore;

    fn on_deref(var: Var, deref_var: &mut Self::DerefStore);
}

enum MutCtxt {}

impl PlaceContext for MutCtxt {
    // <MutabilityAnalysis as Infer<'_>>::L
    type DerefStore = BooleanSystem<Mutability>;

    fn on_deref(var: Var, database: &mut Self::DerefStore) {
        database.bottom(var);
    }
}

enum UnknownCtxt {}

impl PlaceContext for UnknownCtxt {
    type DerefStore = Option<Var>;

    fn on_deref(var: Var, deref_var: &mut Self::DerefStore) {
        assert!(deref_var.is_none());
        *deref_var = Some(var);
    }
}

enum EnsureNoDeref {}

impl PlaceContext for EnsureNoDeref {
    type DerefStore = ();

    fn on_deref(_: Var, (): &mut Self::DerefStore) {
        unreachable!()
    }
}

fn make_mut(vars: Range<Var>, database: &mut BooleanSystem<Mutability>) {
    for var in vars {
        database.bottom(var);
    }
}

fn place_vars<'tcx, Ctxt: PlaceContext>(
    place: &Place<'tcx>,
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    deref_store: &mut Ctxt::DerefStore,
) -> Range<Var> {
    try_place_vars::<Ctxt>(place, local_decls, locals, struct_fields, tcx, deref_store)
        .unwrap_or_else(|| locals[place.local.index()]..locals[place.local.index()])
}

fn try_place_vars<'tcx, Ctxt: PlaceContext>(
    place: &Place<'tcx>,
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    deref_store: &mut Ctxt::DerefStore,
) -> Option<Range<Var>> {
    let mut place_vars = Range {
        start: locals[place.local.index()],
        end: locals[place.local.index() + 1],
    };
    let mut base_ty = local_decls.local_decls()[place.local].ty;
    let mut variant = None;

    for projection_elem in place.projection {
        match projection_elem {
            ProjectionElem::Deref => {
                Ctxt::on_deref(place_vars.start, deref_store);
                place_vars.start += 1;
                base_ty = base_ty.builtin_deref(true).unwrap();
                variant = None;
            }
            ProjectionElem::Field(field, ty) => match base_ty.kind() {
                TyKind::Adt(adt_def, _) => {
                    let generic_args = match base_ty.kind() {
                        TyKind::Adt(_, generic_args) => *generic_args,
                        _ => unreachable!(),
                    };
                    if let Some(variant_idx) = variant {
                        place_vars = super::enum_variant_field_range(
                            tcx,
                            *adt_def,
                            generic_args,
                            variant_idx,
                            place_vars,
                            field,
                        );
                        base_ty = ty;
                        variant = None;
                        continue;
                    }
                    assert!(place_vars.is_empty());
                    if adt_def.is_union() {
                        return None;
                    }
                    let field_vars = struct_fields
                        .fields(adt_def.did().expect_local())
                        .nth(field.index())
                        .unwrap();

                    place_vars = field_vars;

                    base_ty = ty;
                    variant = None;
                }
                TyKind::Tuple(tys) => {
                    let offset: usize = tys
                        .iter()
                        .take(field.index())
                        .map(|t| super::count_ptr(tcx, t))
                        .sum();
                    let field_count = super::count_ptr(tcx, ty);
                    place_vars = Range {
                        start: place_vars.start + offset,
                        end: place_vars.start + offset + field_count,
                    };
                    base_ty = ty;
                    variant = None;
                }
                _ => unreachable!(),
            },
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                base_ty = base_ty.builtin_index().unwrap();
                variant = None;
            }
            ProjectionElem::Subslice { .. } => unreachable!("unexpected subslicing"),
            ProjectionElem::OpaqueCast(_) => unreachable!("unexpected opaque cast"),
            ProjectionElem::Downcast(_, variant_idx) => {
                let TyKind::Adt(adt_def, generic_args) = base_ty.kind() else {
                    unreachable!("{base_ty:?}")
                };
                if !adt_def.is_enum() {
                    // happens when asserting nonnullness of fn ptrs
                    assert!(place_vars.is_empty());
                    return Some(place_vars);
                }
                place_vars =
                    super::enum_variant_range(tcx, *adt_def, generic_args, place_vars, variant_idx);
                variant = Some(variant_idx);
            }
            ProjectionElem::UnwrapUnsafeBinder(_) => unreachable!("unexpected UnwrapUnsafeBinder"),
            ProjectionElem::Subtype(_) => unreachable!("unexpected Subtype"),
        }
    }

    Some(place_vars)
}

pub(crate) fn conservative_call<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    database: &mut BooleanSystem<Mutability>,
) {
    if let Some(dest_var) = try_place_vars::<MutCtxt>(
        destination,
        local_decls,
        locals,
        struct_fields,
        tcx,
        database,
    ) {
        for var in dest_var {
            database.bottom(var);
        }
    }

    for arg in args {
        let Some(arg) = arg.node.place() else {
            continue;
        };
        let Some(arg_vars) =
            try_place_vars::<EnsureNoDeref>(&arg, local_decls, locals, struct_fields, tcx, &mut ())
        else {
            continue;
        };
        for var in arg_vars {
            database.bottom(var);
        }
    }
}
