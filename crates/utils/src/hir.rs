use rustc_hir::*;
use rustc_middle::ty::TyCtxt;

#[cfg(test)]
mod tests;

/// Proves that an expression's value is discarded by a semicolon statement,
/// directly or through ordinary block tails. False also covers unknown contexts.
/// This does not imply that evaluating the expression can be omitted.
pub fn is_expr_result_discarded<'tcx>(mut expr: &Expr<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    loop {
        match tcx.parent_hir_node(expr.hir_id) {
            Node::Stmt(stmt) => {
                return matches!(stmt.kind, StmtKind::Semi(e) if e.hir_id == expr.hir_id);
            }
            Node::Block(block)
                if !block.targeted_by_break
                    && block.expr.is_some_and(|e| e.hir_id == expr.hir_id) =>
            {
                let Node::Expr(parent) = tcx.parent_hir_node(block.hir_id) else {
                    return false;
                };
                if !matches!(parent.kind, ExprKind::Block(b, None) if b.hir_id == block.hir_id) {
                    return false;
                }
                expr = parent;
            }
            _ => return false,
        }
    }
}

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
