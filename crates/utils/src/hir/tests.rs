use rustc_hir::{def_id::DefId, intravisit::Visitor, *};
use rustc_middle::ty::{self, TyCtxt};

fn assert_discarded(probe: &str, expected: bool) {
    let code = format!("fn marker() -> usize {{ 7 }} fn consume(_: usize) {{}} {probe}");
    crate::compilation::run_compiler_on_str(&code, |tcx| {
        let marker = tcx
            .hir_body_owners()
            .find(|id| tcx.def_path_str(*id) == "marker")
            .unwrap()
            .to_def_id();
        let mut visitor = MarkerVisitor {
            tcx,
            marker,
            results: Vec::new(),
        };
        // Visit each body separately, including closure and async bodies.
        for owner in tcx.hir_body_owners() {
            visitor.visit_body(tcx.hir_body_owned_by(owner));
        }
        assert_eq!(visitor.results, [expected], "{probe}");
    })
    .unwrap();
}

struct MarkerVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    marker: DefId,
    results: Vec<bool>,
}

impl<'tcx> Visitor<'tcx> for MarkerVisitor<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, _) = expr.kind
            && let ty::TyKind::FnDef(did, _) =
                self.tcx.typeck(expr.hir_id.owner).expr_ty(callee).kind()
            && *did == self.marker
        {
            self.results
                .push(super::is_expr_result_discarded(expr, self.tcx));
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

#[test]
fn test_is_expr_result_discarded_blocks() {
    for body in [
        "marker();",
        "{ marker() };",
        "{ { (marker()) } };",
        "unsafe { let _setup = 1; marker() };",
    ] {
        assert_discarded(&format!("fn probe() {{ {body} }}"), true);
    }
    assert_discarded("fn probe() -> usize { { marker() } }", false);
}

#[test]
fn test_is_expr_result_discarded_consumers() {
    for body in [
        "let mut n = 0; n = { marker() };",
        "let n = { marker() };",
        "let n: usize = { marker() };",
        "let _ = marker();",
        "consume({ marker() });",
        "({ marker() } as u64);",
    ] {
        assert_discarded(&format!("fn probe() {{ {body} }}"), false);
    }
    assert_discarded("fn probe() -> usize { return { marker() }; }", false);
}

#[test]
fn test_is_expr_result_discarded_boundaries() {
    for body in [
        "'out: { if cond { break 'out 1usize; } marker() };",
        "if cond { marker() } else { 1usize };",
        "match cond { true => { marker() }, false => 1usize };",
        "loop { break { marker() }; };",
        "(|| { marker() });",
        "(|| { marker() })();",
        "async { marker() };",
    ] {
        assert_discarded(&format!("fn probe(cond: bool) {{ {body} }}"), false);
    }
    assert_discarded("fn probe() { (|| { marker(); })(); }", true);
    assert_discarded("fn probe() { 'out: { marker(); } }", true);
}
