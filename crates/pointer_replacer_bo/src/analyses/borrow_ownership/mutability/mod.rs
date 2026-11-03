//! BO's mutability analysis: the legacy Foster mutability analysis with era-5c's load gate
//! (R545-1, [`LoadGate`]). The libc and Rust-library tables are the legacy crate's, master's PR
//! #130 `strtod` / `strtof` / `strtold` / `strtol` / `strtoll` / `strtoul` / `strtoull` rows
//! included (the user's word in main's session 11-02).
//! The `Mutability` lattice and the Rust-library table are the legacy crate's (the master-merge
//! cleanup's legacy-copy stage, the user's word in main's session 11-02).

use std::ops::Range;

pub use pointer_replacer::analyses::type_qualifier::foster::mutability::{
    Mutability, MutabilityResult,
};
use pointer_replacer::analyses::type_qualifier::foster::mutability::{
    libc::libc_call, library::library_call,
};
use rustc_middle::mir::{
    BinOp, HasLocalDecls, Location, Operand, Place, ProjectionElem, Rvalue, Terminator,
    visit::Visitor,
};
use rustc_span::{def_id::LocalDefId, source_map::Spanned};
use rustc_type_ir::TyKind;

use crate::{
    analyses::{
        mir::{self, CallKind, TerminatorExt},
        type_qualifier::foster::{
            InferCtxt, StructFields, Var,
            constraint_system::{BooleanSystem, ConstraintSystem},
        },
    },
    utils::rustc::RustProgram,
};

// #[cfg(test)]
// mod test;

pub fn mutability_analysis(rust_program: &RustProgram) -> MutabilityResult {
    mutability_analysis_gated(rust_program, None)
}

/// era-5c R545-1: a load gate. `lhs = copy (*p)…` emits `lhs ⇒ p` (a value loaded
/// out of `*p` and used mutably needs `p`'s level mutable -- Rust's rule for
/// reborrowing `&mut` out of `*p`). The gate is asked per load; `false` drops that
/// one guard. `None` keeps every guard (the ungated analysis, byte-identical).
pub type LoadGate<'g, 'tcx> = &'g dyn Fn(LocalDefId, &Place<'tcx>) -> bool;

pub fn mutability_analysis_gated<'tcx>(
    rust_program: &RustProgram<'tcx>,
    gate: Option<LoadGate<'_, 'tcx>>,
) -> MutabilityResult {
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
            fn_did: *r#fn,
            gate,
        };

        analysis.visit_body(body);
    }
    database.greatest_model(&mut result.model);
    result
}

pub struct MutabilityAnalysis<'infer, 'tcx, D> {
    ctxt: InferCtxt<'infer, 'tcx, D>,
    database: &'infer mut BooleanSystem<Mutability>,
    fn_did: LocalDefId,
    gate: Option<LoadGate<'infer, 'tcx>>,
}

impl<'infer, 'tcx, D: HasLocalDecls<'tcx>> Visitor<'tcx> for MutabilityAnalysis<'infer, 'tcx, D> {
    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, _location: Location) {
        let lhs = place;
        let rhs = rvalue;
        // R545-1: whether a load's `lhs ⇒ p` guard is kept (see `LoadGate`).
        let keep_load = |load: &Place<'tcx>| self.gate.is_none_or(|gate| gate(self.fn_did, load));

        let InferCtxt {
            local_decls,
            locals,
            fn_locals: _,
            struct_fields,
            tcx,
        } = self.ctxt;
        let database = &mut self.database;

        match rhs {
            Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs)) | Rvalue::CopyForDeref(rhs) => {
                let keep = keep_load(rhs);
                let lhs = place_vars::<MutCtxt>(lhs, local_decls, locals, struct_fields, database);
                let mut rhs_deref = None;
                let rhs = place_vars::<UnknownCtxt>(
                    rhs,
                    local_decls,
                    locals,
                    struct_fields,
                    &mut rhs_deref,
                );

                // An unencoded projection (currently a union field) can truncate the RHS
                // qualifier range even when Rust types still agree. Bottom only the representable
                // destination: silently zipping an empty RHS would leave it incorrectly `Imm`.
                if lhs.end.index() - lhs.start.index() != rhs.end.index() - rhs.start.index() {
                    for lhs in lhs {
                        database.bottom(lhs);
                    }
                    return;
                }

                let mut lhs_rhs = lhs.zip(rhs);
                if let Some((lhs, rhs)) = lhs_rhs.next() {
                    database.guard(lhs, rhs);
                    if let Some(rhs_deref) = rhs_deref
                        && keep
                    {
                        database.guard(lhs, rhs_deref);
                    }
                }
                for (lhs, rhs) in lhs_rhs {
                    database.guard(lhs, rhs);
                    database.guard(rhs, lhs)
                }
            }
            Rvalue::Cast(_, Operand::Copy(rhs) | Operand::Move(rhs), _) => {
                let preserves_carrier = struct_fields.preserves_carrier_cast(
                    rhs.ty(local_decls, tcx).ty,
                    lhs.ty(local_decls, tcx).ty,
                );
                // Ordinary casts constrain only the head pointer; carrier casts
                // also preserve the pointee's qualifier slots.
                let keep = keep_load(rhs);
                let lhs = place_vars::<MutCtxt>(lhs, local_decls, locals, struct_fields, database);
                let mut rhs_deref = None;
                let rhs = place_vars::<UnknownCtxt>(
                    rhs,
                    local_decls,
                    locals,
                    struct_fields,
                    &mut rhs_deref,
                );

                let mut lhs_rhs = lhs.zip(rhs);
                if let Some((lhs, rhs)) = lhs_rhs.next() {
                    database.guard(lhs, rhs);
                    if let Some(rhs_deref) = rhs_deref
                        && keep
                    {
                        database.guard(lhs, rhs_deref)
                    }
                }
                if preserves_carrier {
                    for (lhs, rhs) in lhs_rhs {
                        database.guard(lhs, rhs);
                        database.guard(rhs, lhs);
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
                let dest_vars =
                    place_vars::<MutCtxt>(lhs, local_decls, locals, struct_fields, database);
                if let Some(arg) = ptr.place() {
                    let arg_vars = place_vars::<EnsureNoDeref>(
                        &arg,
                        local_decls,
                        locals,
                        struct_fields,
                        &mut (),
                    );
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
                let mut lhs =
                    place_vars::<EnsureNoDeref>(lhs, local_decls, locals, struct_fields, &mut ());
                let mut rhs_deref = None;
                let rhs = place_vars::<UnknownCtxt>(
                    rhs,
                    local_decls,
                    locals,
                    struct_fields,
                    &mut rhs_deref,
                );
                let lhs_ref = lhs.next().unwrap();
                if let Some(rhs_deref) = rhs_deref {
                    database.guard(lhs_ref, rhs_deref);
                }
                for (lhs, rhs) in lhs.zip(rhs) {
                    database.guard(lhs, rhs);
                    database.guard(rhs, lhs);
                }
            }
            _ => {
                let _ = place_vars::<MutCtxt>(lhs, local_decls, locals, struct_fields, database);
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
        let database = &mut self.database;

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

                    let dest = place_vars::<MutCtxt>(
                        destination,
                        local_decls,
                        locals,
                        struct_fields,
                        database,
                    );
                    let ret = callee_vars.next().unwrap();

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

                    for (arg, param_vars) in args.iter().zip(callee_vars) {
                        let Some(arg) = arg.node.place() else {
                            continue;
                        };
                        let arg_vars = place_vars::<EnsureNoDeref>(
                            &arg,
                            local_decls,
                            locals,
                            struct_fields,
                            &mut (),
                        );

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

fn place_vars<'tcx, Ctxt: PlaceContext>(
    place: &Place<'tcx>,
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    deref_store: &mut Ctxt::DerefStore,
) -> Range<Var> {
    let mut place_vars = Range {
        start: locals[place.local.index()],
        end: locals[place.local.index() + 1],
    };
    let mut base_ty = local_decls.local_decls()[place.local].ty;

    for projection_elem in place.projection {
        match projection_elem {
            ProjectionElem::Deref => {
                Ctxt::on_deref(place_vars.start, deref_store);
                place_vars.start += 1;
                base_ty = base_ty.builtin_deref(true).unwrap();
            }
            ProjectionElem::Field(field, ty) => {
                if struct_fields.is_pointer_carrier(base_ty) {
                    if field.index() != 0 {
                        return place_vars.end..place_vars.end;
                    }
                    base_ty = ty;
                    continue;
                }
                match base_ty.kind() {
                    TyKind::Adt(adt_def, _) => {
                        assert!(place_vars.is_empty());
                        // FIXME correctness?
                        if adt_def.is_union() {
                            return place_vars;
                        }
                        let field_vars = struct_fields
                            .fields(adt_def.did().expect_local())
                            .nth(field.index())
                            .unwrap();

                        place_vars = field_vars;

                        base_ty = ty;
                    }
                    TyKind::Tuple(tys) => {
                        let offset: usize = tys
                            .iter()
                            .take(field.index())
                            .map(|t| struct_fields.count_ptr(t))
                            .sum();
                        let field_count = struct_fields.count_ptr(ty);
                        place_vars = Range {
                            start: place_vars.start + offset,
                            end: place_vars.start + offset + field_count,
                        };
                        base_ty = ty;
                    }
                    _ => unreachable!(),
                }
            }
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                base_ty = base_ty.builtin_index().unwrap();
            }
            ProjectionElem::Subslice { .. } => unreachable!("unexpected subslicing"),
            ProjectionElem::OpaqueCast(_) => unreachable!("unexpected opaque cast"),
            ProjectionElem::Downcast(..) => {
                // happens when asserting nonnullness of fn ptrs
                assert!(place_vars.is_empty());
                return place_vars;
            }
            ProjectionElem::UnwrapUnsafeBinder(_) => unreachable!("unexpected UnwrapUnsafeBinder"),
            ProjectionElem::Subtype(_) => unreachable!("unexpected Subtype"),
        }
    }

    place_vars
}

pub(crate) fn conservative_call<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Mutability>,
) {
    let dest_var = place_vars::<MutCtxt>(destination, local_decls, locals, struct_fields, database);

    for var in dest_var {
        database.bottom(var);
    }

    for arg in args {
        let Some(arg) = arg.node.place() else {
            continue;
        };
        let arg_vars =
            place_vars::<EnsureNoDeref>(&arg, local_decls, locals, struct_fields, &mut ());
        for var in arg_vars {
            database.bottom(var);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{mutability_analysis, mutability_analysis_gated};

    #[test]
    fn pointer_carriers_preserve_nested_mutability() {
        let source = r#"
pub unsafe fn boxed(value: Box<*mut i32>) {
    **value = 1;
}
pub unsafe fn nested(value: Box<Box<*mut i32>>) {
    ***value = 1;
}
pub unsafe fn nonnull(value: std::ptr::NonNull<*mut i32>) {
    let raw: *const *mut i32 = std::mem::transmute(value);
    **raw = 1;
}
pub unsafe fn tuple(value: (std::ptr::NonNull<*mut i32>, *mut i32)) {
    let raw: *const *mut i32 = std::mem::transmute(value.0);
    **raw = 1;
    *value.1 = 2;
}
"#;
        utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = crate::utils::rustc::RustProgram {
                tcx,
                functions: tcx.hir_body_owners().collect(),
                structs: vec![],
            };
            let shared =
                pointer_replacer::analyses::type_qualifier::foster::mutability::mutability_analysis(
                    &program,
                );
            let ungated = mutability_analysis(&program);
            let gated = mutability_analysis_gated(&program, Some(&|_, _| false));
            for &function in &program.functions {
                let expected = shared.function_facts(function, tcx).nth(1).unwrap();
                let actual = ungated.function_facts(function, tcx).nth(1).unwrap();
                assert_eq!(actual, expected);
                let (layers, inner) = match tcx.item_name(function.to_def_id()).as_str() {
                    "nested" => (3, 2),
                    "tuple" => (3, 1),
                    _ => (2, 1),
                };
                assert_eq!(actual.len(), layers);
                assert!(actual[inner].is_mutable());
                assert!(actual.last().unwrap().is_mutable());
                let gated = gated.function_facts(function, tcx).nth(1).unwrap();
                assert_eq!(gated.len(), layers);
                assert!(gated[inner].is_mutable());
                assert!(gated.last().unwrap().is_mutable());
            }
        })
        .unwrap();
    }
}
