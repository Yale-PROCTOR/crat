//! Surface-call path witnesses and qualification.

use rustc_ast::{mut_visit::MutVisitor, ptr::P};
use rustc_hash::FxHashMap;
use rustc_hir::{def::Res, intravisit};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol, def_id::LocalDefId};

use super::ast_transform::{AstCapture, RevertSet};

/// A renamed imported call needs the helper's defining module, because its
/// original `use` still imports the raw wrapper. Bind calls by native callee
/// identity, and take paths only from helpers actually emitted this round.
pub(super) fn qualify(
    tcx: TyCtxt<'_>,
    capture: &AstCapture,
    table: &super::decision::DecisionTable,
    reverts: &RevertSet,
    krate: &mut rustc_ast::Crate,
) {
    fn helpers(
        items: &[P<rustc_ast::Item>],
        modules: &mut Vec<Symbol>,
        capture: &AstCapture,
        table: &super::decision::DecisionTable,
        reverts: &RevertSet,
        out: &mut FxHashMap<LocalDefId, Vec<Symbol>>,
    ) {
        for item in items {
            if let rustc_ast::ItemKind::Mod(_, name, rustc_ast::ModKind::Loaded(inner, _, _, _)) =
                &item.kind
            {
                modules.push(name.name);
                helpers(inner, modules, capture, table, reverts, out);
                modules.pop();
                continue;
            }
            let Some(&did) = capture.map.global_map.get(&item.id) else { continue };
            let rustc_ast::ItemKind::Fn(function) = &item.kind else { continue };
            if reverts.fns.contains(&did)
                || !matches!(
                    table.exposure.as_ref().map(|exposure| exposure.plan(did)),
                    Some(
                        super::decision::exposure::ExposureSurfacePlan::PositiveSeedShim
                            | super::decision::exposure::ExposureSurfacePlan::FnPtrRawWrapper
                    )
                )
                || !function.ident.name.as_str().starts_with("__crat_safe_")
            {
                continue;
            }
            let mut path = modules.clone();
            path.push(function.ident.name);
            out.insert(did, path);
        }
    }

    let mut produced = FxHashMap::default();
    helpers(
        &krate.items,
        &mut vec![Symbol::intern("crate")],
        capture,
        table,
        reverts,
        &mut produced,
    );
    if produced.is_empty() {
        return;
    }
    struct Calls<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        produced: &'a FxHashMap<LocalDefId, Vec<Symbol>>,
        paths: &'a mut FxHashMap<Span, Vec<Symbol>>,
    }
    impl<'tcx> intravisit::Visitor<'tcx> for Calls<'_, 'tcx> {
        fn visit_expr(&mut self, expression: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Call(callee, _) = expression.kind
                && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind
                && path.segments.len() == 1
                && let Res::Def(_, target) = path.res
                && let Some(local) = target.as_local()
                && self.tcx.parent(target) != self.tcx.parent(self.owner.to_def_id())
                && let Some(path) = self.produced.get(&local)
            {
                self.paths.insert(callee.span, path.clone());
            }
            intravisit::walk_expr(self, expression);
        }
    }
    let mut paths = FxHashMap::default();
    for owner in tcx.hir_body_owners() {
        if let Some(body) = tcx.hir_node_by_def_id(owner).body_id() {
            intravisit::Visitor::visit_body(
                &mut Calls {
                    tcx,
                    owner,
                    produced: &produced,
                    paths: &mut paths,
                },
                tcx.hir_body(body),
            );
        }
    }
    struct Qualify<'a>(&'a FxHashMap<Span, Vec<Symbol>>);
    impl MutVisitor for Qualify<'_> {
        fn visit_expr(&mut self, expression: &mut rustc_ast::Expr) {
            if let rustc_ast::ExprKind::Call(callee, _) = &mut expression.kind
                && let Some(qualified) = self.0.get(&callee.span)
                && let rustc_ast::ExprKind::Path(None, path) = &mut callee.kind
                && path.segments.len() == 1
                && path.segments.last().map(|segment| segment.ident.name)
                    == qualified.last().copied()
            {
                // Keep the renamed terminal segment and any generic arguments.
                // Only its module prefix changes; function-value uses retain the
                // raw wrapper and its original import.
                let terminal = path.segments.pop().unwrap();
                path.segments
                    .extend(qualified[..qualified.len() - 1].iter().map(|&name| {
                        rustc_ast::PathSegment {
                            ident: rustc_span::Ident::new(name, path.span),
                            id: rustc_ast::DUMMY_NODE_ID,
                            args: None,
                        }
                    }));
                path.segments.push(terminal);
            }
            rustc_ast::mut_visit::walk_expr(self, expression);
        }
    }
    Qualify(&paths).visit_crate(krate);
}

#[cfg(test)]
mod tests {
    const IMPORTED: &str = r#"
#![allow(dead_code, unused_unsafe)]
pub mod provider {
    pub unsafe fn start(p: *const i32) -> i32 { *p }
    pub fn install() { let _callback: unsafe fn(*const i32) -> i32 = start; }
    pub unsafe fn same_module(p: *const i32) -> i32 { start(p) }
}
pub mod consumer {
    use crate::provider::start;
    pub unsafe fn imported(p: *const i32) -> i32 { start(p) }
}
"#;

    fn emit(input: &str, revert_provider: bool) -> String {
        let source = ::utils::compilation::run_compiler_on_str(input, |tcx| {
            let capture = crate::bo_rewriter::ast_transform::capture_ast(tcx).unwrap();
            let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::bo_rewriter::A5Mode::PreciseReplay,
                    Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let provider = tcx
                .hir_body_owners()
                .find(|owner| tcx.def_path_str(owner.to_def_id()) == "provider::start")
                .unwrap();
            assert_eq!(
                table.exposure.as_ref().unwrap().plan(provider),
                crate::bo_rewriter::decision::exposure::ExposureSurfacePlan::PositiveSeedShim
            );
            let emission = crate::bo_rewriter::emit_files(
                tcx,
                &table,
                &Default::default(),
                &ctx.retained_c9_plans,
            )
            .unwrap();
            let mut held = emission.plan.held_classes();
            if revert_provider {
                held.insert(crate::bo_rewriter::bridge_receipt::SignatureClassId::of(
                    provider,
                ));
            }
            let reverts = crate::bo_rewriter::ast_transform::revert_set_from_classes_and_atoms(
                &held,
                &Default::default(),
                &table,
            )
            .unwrap();
            crate::bo_rewriter::ast_transform::ast_emitted_files_from(
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
            crate::bo_rewriter::verify::type_checks_str(&source),
            "{source}"
        );
        source
    }

    #[test]
    fn wave5r_e0425_imported_surface_call() {
        let source = emit(IMPORTED, false);
        assert!(source.contains("fn __crat_safe_start"), "{source}");
        assert!(
            source.contains("crate::provider::__crat_safe_start"),
            "{source}"
        );
    }

    #[test]
    fn wave5r_e0425_same_module_surface_call_control() {
        let same_module = IMPORTED.split("pub mod consumer").next().unwrap();
        let source = emit(same_module, false);
        assert!(source.contains("fn same_module"), "{source}");
        assert!(
            source.contains("unsafe fn(*const i32) -> i32 = start"),
            "{source}"
        );
    }

    #[test]
    fn wave5r_e0425_reverted_surface_has_no_helper_call() {
        let source = emit(IMPORTED, true);
        assert!(!source.contains("__crat_safe_start"), "{source}");
    }
}
