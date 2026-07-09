use rustc_hir::*;
use rustc_middle::ty::TyCtxt;

pub fn unwrap_drop_temps<'a, 'tcx>(expr: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    if let ExprKind::DropTemps(e) = expr.kind {
        unwrap_drop_temps(e)
    } else {
        expr
    }
}

/// peels field/index projections off a place expression, returning its base.
pub fn lhs_base<'a, 'tcx>(expr: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    if let ExprKind::Field(l, _) | ExprKind::Index(l, _, _) = expr.kind {
        lhs_base(l)
    } else {
        expr
    }
}

/// whether `expr` is (part of) the left-hand side of an assignment.
pub fn is_lhs<'tcx>(mut expr: &Expr<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    for (_, parent) in tcx.hir_parent_iter(expr.hir_id) {
        let Node::Expr(parent) = parent else { return false };
        match parent.kind {
            ExprKind::Assign(l, _, _) | ExprKind::AssignOp(_, l, _) if l.hir_id == expr.hir_id => {
                return true;
            }
            ExprKind::Field(_, _) => {}
            ExprKind::Index(l, _, _) if l.hir_id == expr.hir_id => {}
            _ => return false,
        }
        expr = parent;
    }
    panic!()
}
