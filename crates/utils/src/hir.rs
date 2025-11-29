use rustc_hir::*;

pub fn unwrap_drop_temps<'a, 'tcx>(expr: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    if let ExprKind::DropTemps(e) = expr.kind {
        unwrap_drop_temps(e)
    } else {
        expr
    }
}
