use std::ops::Range;

use libc::libc_call;
use library::library_call;
use rustc_middle::mir::{
    AggregateKind, BinOp, HasLocalDecls, Location, Operand, Place, ProjectionElem, Rvalue,
    Terminator, TerminatorKind, visit::Visitor,
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
            def_name: rust_program.tcx.def_path_str(*r#fn),
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
    // TEMP: name of the function currently being analyzed (for CRAT_MUT_TRACE).
    def_name: String,
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
        let def_name: &str = &self.def_name;
        let database = &mut *self.database;

        if mut_trace_enabled() {
            // Log the type of the *pointer being dereferenced* at each Deref on the LHS
            // (that pointer's pointee qualifier is the one MutCtxt::on_deref bottoms).
            // This isolates genuine writes THROUGH a `*git_oid` from writes to git_oid
            // *fields* of some other container pointer.
            let mut base_ty = local_decls.local_decls()[lhs.local].ty;
            for elem in lhs.projection.iter() {
                match elem {
                    ProjectionElem::Deref => {
                        trace_mut("WRITE-deref", def_name, "", base_ty);
                        base_ty = base_ty.builtin_deref(true).unwrap_or(base_ty);
                    }
                    ProjectionElem::Field(_, ty) => {
                        base_ty = ty;
                    }
                    _ => {}
                }
            }
        }

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
                    trace_mut(
                        "USE-rhs-unresolved",
                        def_name,
                        "",
                        place.ty(local_decls.local_decls(), tcx).ty,
                    );
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
                    trace_mut(
                        "CAST-rhs-unresolved",
                        def_name,
                        "",
                        place.ty(local_decls.local_decls(), tcx).ty,
                    );
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
                        trace_mut(
                            "OFFSET-arg-unresolved",
                            def_name,
                            "",
                            place.ty(local_decls.local_decls(), tcx).ty,
                        );
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
                    trace_mut(
                        "REF-rhs-unresolved",
                        def_name,
                        "",
                        place.ty(local_decls.local_decls(), tcx).ty,
                    );
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
        let def_name: &str = &self.def_name;
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
                            if mut_trace_enabled() {
                                let callee_name = tcx.def_path_str(callee);
                                trace_mut(
                                    "CALL-arg-unresolved->param",
                                    def_name,
                                    &callee_name,
                                    arg.ty(local_decls.local_decls(), tcx).ty,
                                );
                            }
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
                CallKind::Impl(..) | CallKind::Closure | CallKind::Dynamic => {
                    // Recover the callee's declared parameter types so that conservative_call
                    // only bottoms the levels the callee may actually write. A `*const`/`&`
                    // parameter is a contract that the callee won't write through it, so we
                    // must not force the caller's argument `*mut`. Closures (rust-call tupled
                    // args) and anything we can't read a signature from fall back to None,
                    // which preserves the old fully-conservative behavior.
                    let param_tys: Option<Vec<rustc_middle::ty::Ty<'tcx>>> = match &terminator.kind
                    {
                        TerminatorKind::Call { func, .. }
                        | TerminatorKind::TailCall { func, .. } => {
                            let fty = func.ty(local_decls, tcx);
                            match fty.kind() {
                                TyKind::FnDef(..) | TyKind::FnPtr(..) => {
                                    Some(fty.fn_sig(tcx).skip_binder().inputs().to_vec())
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    };
                    conservative_call(
                        destination,
                        args,
                        param_tys.as_deref(),
                        local_decls,
                        locals,
                        struct_fields,
                        tcx,
                        database,
                    );
                }
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

// TEMP instrumentation (env-gated via CRAT_MUT_TRACE) to trace why `git_oid` pointers
// get marked Mut. Remove once the over-marking root cause is fixed.
fn mut_trace_enabled() -> bool {
    use std::sync::OnceLock;
    static EN: OnceLock<bool> = OnceLock::new();
    *EN.get_or_init(|| std::env::var_os("CRAT_MUT_TRACE").is_some())
}

fn trace_mut(site: &str, def_name: &str, extra: &str, ty: rustc_middle::ty::Ty<'_>) {
    if !mut_trace_enabled() {
        return;
    }
    let s = format!("{ty:?}");
    if s.contains("git_oid") {
        eprintln!("[MUTTRACE]\t{site}\t{def_name}\t{extra}\t{s}");
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

#[allow(clippy::too_many_arguments)]
pub(crate) fn conservative_call<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    // The callee's declared parameter types, when available. `None` (e.g. opaque calls,
    // closures, libc/library fallbacks) means "no contract" -> stay fully conservative.
    param_tys: Option<&[rustc_middle::ty::Ty<'tcx>]>,
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

    for (i, arg) in args.iter().enumerate() {
        let Some(arg) = arg.node.place() else {
            continue;
        };
        let Some(arg_vars) =
            try_place_vars::<EnsureNoDeref>(&arg, local_decls, locals, struct_fields, tcx, &mut ())
        else {
            continue;
        };

        match param_tys.and_then(|ps| ps.get(i)) {
            // Declared parameter type known: bottom only the pointer levels the callee is
            // allowed to write (`*mut`/`&mut`); skip `*const`/`&` levels. The argument's
            // qualifier vars are laid out outermost-first (one var per deref), so peeling
            // the parameter type in lockstep aligns each level with `arg_vars.start + k`.
            Some(&param_ty) => {
                let mut ty = param_ty;
                let mut var = arg_vars.start;
                while var < arg_vars.end {
                    match ty.kind() {
                        TyKind::RawPtr(inner, mutbl) | TyKind::Ref(_, inner, mutbl) => {
                            if mutbl.is_mut() {
                                if mut_trace_enabled() {
                                    trace_mut(
                                        "CONSERVATIVE-bottomed",
                                        "<conservative_call>",
                                        "",
                                        ty,
                                    );
                                }
                                database.bottom(var);
                            }
                            var += 1;
                            ty = *inner;
                        }
                        // Pointee is an aggregate with its own inner qualifier vars (rare for
                        // these args): stay conservative for the remainder.
                        _ => {
                            for v in var..arg_vars.end {
                                database.bottom(v);
                            }
                            break;
                        }
                    }
                }
            }
            // No declared type (no signature, or a variadic extra argument): stay fully
            // conservative, as before.
            None => {
                if mut_trace_enabled() {
                    trace_mut(
                        "CONSERVATIVE-noinfo",
                        "<conservative_call>",
                        "",
                        arg.ty(local_decls.local_decls(), tcx).ty,
                    );
                }
                make_mut(arg_vars, database);
            }
        }
    }
}
