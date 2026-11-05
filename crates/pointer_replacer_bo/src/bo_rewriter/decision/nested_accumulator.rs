//! Scalar-only conditional updates to one zero-initialized f64 accumulator.
//! The enclosing rule owns unchanged local slice formations and index extent;
//! branch uses are syntactic coverage, never a claim of access on every path.
use rustc_hir::{BinOpKind, Expr, ExprKind, HirId, StmtKind, UnOp};
use rustc_middle::ty::TyKind;

use super::{LoopCheck, binding, index_binding, offset, peel};

fn value<'tcx>(check: &LoopCheck<'_, 'tcx>, expr: &'tcx Expr<'tcx>) -> bool {
    if !matches!(
        check.tcx.typeck(check.owner).expr_ty(expr).kind(),
        TyKind::Float(_)
    ) {
        return false;
    }
    match peel(expr).kind {
        ExprKind::Path(..) => binding(expr).is_some(),
        ExprKind::Lit(_) => true,
        ExprKind::Unary(UnOp::Neg, inner) => value(check, inner),
        ExprKind::Binary(op, left, right)
            if matches!(
                op.node,
                BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div
            ) =>
        {
            value(check, left) && value(check, right)
        }
        ExprKind::Unary(UnOp::Deref, inner) => {
            offset(check.tcx, check.owner, inner).is_some_and(|(receiver, index)| {
                binding(receiver).is_some_and(|id| check.rows.contains(&id))
                    && index_binding(check.tcx, check.owner, index) == Some(check.index)
            })
        }
        _ => false,
    }
}

pub(super) fn condition<'tcx>(check: &LoopCheck<'_, 'tcx>, expr: &'tcx Expr<'tcx>) -> bool {
    let ExprKind::Binary(op, left, right) = peel(expr).kind else { return false };
    matches!(
        op.node,
        BinOpKind::Eq
            | BinOpKind::Ne
            | BinOpKind::Lt
            | BinOpKind::Le
            | BinOpKind::Gt
            | BinOpKind::Ge
    ) && value(check, left)
        && value(check, right)
}

pub(super) fn update<'tcx>(
    check: &LoopCheck<'_, 'tcx>,
    branch: &'tcx Expr<'tcx>,
    accumulator: HirId,
) -> bool {
    let ExprKind::Block(block, _) = branch.kind else { return false };
    // The approved first shape is one update, including the HIR trailing
    // expression spelling. Statements/calls/locals cannot be silently skipped.
    let expression = match (block.stmts, block.expr) {
        ([stmt], None) => match stmt.kind {
            StmtKind::Expr(e) | StmtKind::Semi(e) => e,
            _ => return false,
        },
        ([], Some(e)) => e,
        _ => return false,
    };
    let ExprKind::AssignOp(op, left, right) = expression.kind else { return false };
    matches!(
        op.node,
        rustc_ast::AssignOpKind::AddAssign | rustc_ast::AssignOpKind::SubAssign
    ) && binding(left) == Some(accumulator)
        && value(check, right)
}
