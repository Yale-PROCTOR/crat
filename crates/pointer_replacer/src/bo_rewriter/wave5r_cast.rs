//! Realize a decision-owned cast peel through the original operand subtree.

pub(super) fn is_bare_cast_peel(
    spec: &super::decision::seam::GlueSpec,
    expression: &rustc_ast::Expr,
    operand: rustc_span::Span,
) -> bool {
    matches!(spec.core, super::decision::seam::GlueCore::Bare)
        && matches!(&expression.kind, rustc_ast::ExprKind::Cast(inner, _)
            if inner.span.contains(operand))
        && !operand.is_dummy()
        && operand != expression.span
}
