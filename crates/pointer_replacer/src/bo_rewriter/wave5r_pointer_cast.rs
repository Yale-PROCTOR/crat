//! Retain the typed raw intermediate when a promoted operand changes pointee.

use rustc_ast::{ExprKind, mut_visit::MutVisitor, ptr::P};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def::Res, intravisit};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{ast_transform, decision};

/// This consumes only surviving Ref decisions and original compiler types.
/// The boundary's existing proof is unchanged: no new subject is admitted,
/// no reference is constructed, and the intermediate is always const.
pub(super) fn apply(
    tcx: TyCtxt<'_>,
    table: &decision::DecisionTable,
    reverts: &ast_transform::RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut ast_transform::Composition,
) -> Result<(), String> {
    let subjects = table
        .entries
        .iter()
        .filter_map(|(subject, decision)| {
            let reference = match decision {
                decision::Decision::Ref { .. } => true,
                decision::Decision::InferredRef { .. }
                | decision::Decision::Cursor { .. }
                | decision::Decision::Slice { .. }
                | decision::Decision::Opt { .. }
                | decision::Decision::Box(_)
                | decision::Decision::Degraded(_) => false,
            };
            (reference && reverts.keeps_subject(subject.fn_did, subject.hir_id))
                .then_some(subject.hir_id)
        })
        .collect::<FxHashSet<_>>();
    let owners = subjects
        .iter()
        .map(|binding| binding.owner.def_id)
        .collect::<FxHashSet<_>>();
    let mut candidates = FxHashMap::default();
    for owner in owners {
        struct Find<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            owner: rustc_span::def_id::LocalDefId,
            subjects: &'a FxHashSet<rustc_hir::HirId>,
            candidates: &'a mut FxHashMap<Span, (Span, Result<String, String>)>,
        }
        impl<'tcx> intravisit::Visitor<'tcx> for Find<'_, 'tcx> {
            fn visit_expr(&mut self, expression: &'tcx rustc_hir::Expr<'tcx>) {
                intravisit::walk_expr(self, expression);
                let rustc_hir::ExprKind::Cast(operand, _) = expression.kind else { return };
                let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = operand.kind
                else {
                    return;
                };
                let Res::Local(binding) = path.res else { return };
                if !self.subjects.contains(&binding) {
                    return;
                }
                let typeck = self.tcx.typeck(self.owner);
                let TyKind::RawPtr(source, _) = *typeck.expr_ty(operand).kind() else { return };
                let TyKind::RawPtr(target, permission) = *typeck.expr_ty(expression).kind() else {
                    return;
                };
                if permission.is_mut() || source == target {
                    return;
                }
                let source =
                    if decision::declaration::pointee_is_nameable(self.tcx, self.owner, source) {
                        Ok(decision::declaration::pointee_source(self.tcx, source))
                    } else {
                        Err("pointer-cast-source-not-nameable".to_owned())
                    };
                self.candidates
                    .insert(expression.span, (operand.span, source));
            }
        }
        intravisit::Visitor::visit_body(
            &mut Find {
                tcx,
                owner,
                subjects: &subjects,
                candidates: &mut candidates,
            },
            tcx.hir_body_owned_by(owner),
        );
    }
    struct Apply<'a> {
        candidates: &'a FxHashMap<Span, (Span, Result<String, String>)>,
        guard: &'a mut ast_transform::Composition,
        error: Option<String>,
    }
    impl MutVisitor for Apply<'_> {
        fn visit_expr(&mut self, expression: &mut rustc_ast::Expr) {
            rustc_ast::mut_visit::walk_expr(self, expression);
            if self.error.is_some() {
                return;
            }
            let Some((operand_span, source)) = self.candidates.get(&expression.span) else {
                return;
            };
            let ExprKind::Cast(operand, _) = &mut expression.kind else { return };
            // Seam/use grafts own their generated operands. Only the original
            // still-surviving cast receives this syntax-preserving repair.
            if operand.span != *operand_span {
                return;
            }
            let source = match source {
                Ok(source) => source,
                Err(error) => {
                    self.error = Some(error.clone());
                    return;
                }
            };
            let mut intermediate =
                match ast_transform::graft_expr(&format!("__crat_operand as *const {source}")) {
                    Ok(expression) => expression,
                    Err(_) => {
                        self.error = Some("pointer-cast-intermediate-unparseable".to_owned());
                        return;
                    }
                };
            if !self
                .guard
                .claim(expression.id, expression.span, "pointer-cast-intermediate")
            {
                self.error = Some("pointer-cast-intermediate-collision".to_owned());
                return;
            }
            let ExprKind::Cast(inner, _) = &mut intermediate.kind else { unreachable!() };
            *inner = operand.clone();
            *operand = P(intermediate);
        }
    }
    let mut visitor = Apply {
        candidates: &candidates,
        guard,
        error: None,
    };
    visitor.visit_crate(krate);
    visitor.error.map_or(Ok(()), Err)
}

#[cfg(test)]
mod tests {
    const INPUT: &str = r#"
            #![allow(dead_code, unused_unsafe)]
            unsafe extern "C" {
                fn fwrite(buffer: *const core::ffi::c_void, size: usize,
                    count: usize, file: *mut core::ffi::c_void) -> usize;
            }
            pub unsafe fn lodepng_save_file(buffer: *const u8, file: *mut core::ffi::c_void) {
                fwrite(buffer as *const core::ffi::c_void, 1, 1, file);
            }
        "#;

    fn emitted(input: &str, revert: bool) -> String {
        let source = ::utils::compilation::run_compiler_on_str(input, |tcx| {
            let capture = super::super::ast_transform::capture_ast(tcx).unwrap();
            let (table, ctx) = super::super::decide_table_with_ctx_config(
                tcx,
                Some((
                    super::super::A5Mode::PreciseReplay,
                    Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            for (subject, decision) in &table.entries {
                println!("DECISION {} {decision:?}", subject.label);
            }
            let emission =
                super::super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
                    .unwrap();
            let mut held = emission.plan.held_classes();
            if revert {
                let owner = tcx
                    .hir_body_owners()
                    .find(|owner| tcx.def_path_str(owner.to_def_id()) == "lodepng_save_file")
                    .unwrap();
                held.insert(super::super::bridge_receipt::SignatureClassId::of(owner));
            }
            let reverts = super::super::ast_transform::revert_set_from_classes_and_atoms(
                &held,
                &Default::default(),
                &table,
            )
            .unwrap();
            super::super::ast_transform::ast_emitted_files_from(
                tcx,
                &capture,
                &reverts,
                emission.plan.root_file.as_ref(),
                &table,
                Some(&emission.plan.terminal_call_plans),
            )
            .unwrap()
            .0
            .into_values()
            .next()
            .unwrap()
        })
        .unwrap();
        println!("EMITTED\n{source}");
        assert!(
            super::super::verify::type_checks_str(&source),
            "emission must type-check: {source}"
        );
        source
    }

    #[test]
    fn wave5r_e0606_fwrite_typed_intermediate() {
        let source = emitted(INPUT, false);
        assert!(
            source.contains("buffer: &u8"),
            "fixture must promote buffer: {source}"
        );
        assert!(
            source.contains("as *const u8 as *const core::ffi::c_void"),
            "typed intermediate: {source}"
        );
    }

    #[test]
    fn wave5r_e0606_existing_typed_intermediate_unchanged() {
        let source = emitted(
            &INPUT.replace("fwrite(buffer as", "fwrite(buffer as *const u8 as"),
            false,
        );
        assert!(
            source.contains("buffer: &u8"),
            "fixture must promote buffer: {source}"
        );
        assert_eq!(
            source.matches("as *const u8").count(),
            1,
            "no redundant intermediate: {source}"
        );
    }

    #[test]
    fn wave5r_e0606_reverted_owner_keeps_raw_cast() {
        let source = emitted(INPUT, true);
        assert!(
            source.contains("buffer: *const u8"),
            "owner remains raw: {source}"
        );
        assert!(
            !source.contains("as *const u8"),
            "raw operand requires no repair: {source}"
        );
    }
}
