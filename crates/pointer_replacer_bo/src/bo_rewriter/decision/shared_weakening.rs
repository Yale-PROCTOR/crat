//! Shared-argument weakening (wave-6p, R407-5 STOP 1).
//!
//! An `&mut place` argument handed to a SHARED formal (`&T`, `Option<&T>`) is
//! emitted as `&(place)` / `Some(&(place))`. A shared formal never needs a
//! mutable borrow; the emission is a strictly weaker borrow of the same place,
//! so nothing about aliasing changes — but the mutable spelling is what made
//! `ComputeDistanceCost(cmds, n, &mut orig_params.dist, &mut orig_params.dist,
//! &mut dist_cost)` (brotli) a compile error: two `&mut` borrows of one place in
//! one call coerce to `&` and are still two mutable borrows (E0499); that one
//! error's class revert then closed over ~260 brotli functions (report 003).
//! wave-6k's `shared_read_pairs` renders the same weakening for its READ/READ
//! two-argument transaction under an A5 permission; this is the ordinary
//! seam's form and needs no permission.
//!
//! Span layer: `render` rewrites the argument text. AST layer: [`build`]
//! rewrites the `AddrOf(Mut, operand)` node to `AddrOf(Not, Paren(operand))`,
//! wrapped in `Some(..)` for an optional formal — the operand subtree is kept,
//! never re-parsed.

use rustc_hir::{
    BorrowKind, Expr, ExprKind, Mutability,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::emitability::EmitabilityFacts;

/// One weakened argument, described rather than rendered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SharedWeakening {
    pub argument_span: Span,
    pub operand_span: Span,
    /// The original argument text (`&mut place`), the render's precondition.
    pub original: String,
    /// The operand text (`place`).
    pub operand: String,
    /// Wrap in `Some(..)`: the formal is `Option<&T>`.
    pub optional: bool,
}

impl SharedWeakening {
    pub(crate) fn render(&self, text: &str) -> Option<String> {
        (compact(text) == compact(&self.original)).then(|| {
            if self.optional {
                format!("Some(&({}))", self.operand)
            } else {
                format!("&({})", self.operand)
            }
        })
    }

    pub(crate) fn key(&self) -> &'static str {
        if self.optional {
            "shared-weakening-some"
        } else {
            "shared-weakening"
        }
    }
}

fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

/// Every `&mut operand` call argument of every local call, keyed by the
/// argument span, with its operand span and text. Read once per seam
/// synthesis from the call-argument facts' callers.
#[derive(Clone, Debug, Default)]
pub(crate) struct SharedWeakenings {
    operands: rustc_hash::FxHashMap<(u32, u32), (Span, String)>,
}

impl SharedWeakenings {
    pub(crate) fn derive(tcx: TyCtxt<'_>, facts: &EmitabilityFacts) -> Self {
        let callers = facts
            .call_args
            .values()
            .flatten()
            .map(|site| site.caller)
            .collect::<rustc_hash::FxHashSet<LocalDefId>>();
        let mut operands = rustc_hash::FxHashMap::default();
        for caller in callers {
            let Some(body_id) = tcx.hir_node_by_def_id(caller).body_id() else {
                continue;
            };
            let mut collector = Collector {
                tcx,
                operands: &mut operands,
            };
            collector.visit_body(tcx.hir_body(body_id));
        }
        Self { operands }
    }

    /// The weakening for the `&mut …` argument at `argument_span`, or `None`
    /// when the argument is not literally an `&mut` borrow.
    pub(crate) fn at(
        &self,
        tcx: TyCtxt<'_>,
        argument_span: Span,
        optional: bool,
    ) -> Option<SharedWeakening> {
        let (operand_span, operand) = self
            .operands
            .get(&(argument_span.lo().0, argument_span.hi().0))?
            .clone();
        let original = tcx.sess.source_map().span_to_snippet(argument_span).ok()?;
        Some(SharedWeakening {
            argument_span,
            operand_span,
            original,
            operand,
            optional,
        })
    }
}

struct Collector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    operands: &'a mut rustc_hash::FxHashMap<(u32, u32), (Span, String)>,
}

impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, operand) = &expr.kind
            && let Ok(text) = self.tcx.sess.source_map().span_to_snippet(operand.span)
        {
            self.operands.insert(
                (expr.span.lo().0, expr.span.hi().0),
                (operand.span, text.replace(['\t', '\n', '\r'], " ")),
            );
        }
        intravisit::walk_expr(self, expr);
    }
}

/// AST rendering: `&mut operand` → `&(operand)` (or `Some(&(operand))`),
/// the operand subtree kept in place.
pub(crate) fn build(
    expr: &rustc_ast::Expr,
    weakening: &SharedWeakening,
) -> Option<rustc_ast::ExprKind> {
    use rustc_ast::ptr::P;
    if expr.span != weakening.argument_span {
        return None;
    }
    let rustc_ast::ExprKind::AddrOf(
        rustc_ast::BorrowKind::Ref,
        rustc_ast::Mutability::Mut,
        operand,
    ) = &expr.kind
    else {
        return None;
    };
    if operand.span != weakening.operand_span
        || compact(&rustc_ast_pretty::pprust::expr_to_string(operand))
            != compact(&weakening.operand)
    {
        return None;
    }
    let mut paren = (**operand).clone();
    paren.id = rustc_ast::node_id::DUMMY_NODE_ID;
    paren.attrs = Default::default();
    paren.tokens = None;
    paren.kind = rustc_ast::ExprKind::Paren(operand.clone());
    let borrow = rustc_ast::ExprKind::AddrOf(
        rustc_ast::BorrowKind::Ref,
        rustc_ast::Mutability::Not,
        P(paren),
    );
    if !weakening.optional {
        return Some(borrow);
    }
    let inner = rustc_ast::Expr {
        id: rustc_ast::node_id::DUMMY_NODE_ID,
        kind: borrow,
        span: expr.span,
        attrs: Default::default(),
        tokens: None,
    };
    let some = rustc_ast::Expr {
        id: rustc_ast::node_id::DUMMY_NODE_ID,
        kind: rustc_ast::ExprKind::Path(
            None,
            rustc_ast::Path::from_ident(rustc_span::Ident::with_dummy_span(rustc_span::sym::Some)),
        ),
        span: expr.span,
        attrs: Default::default(),
        tokens: None,
    };
    Some(rustc_ast::ExprKind::Call(
        P(some),
        thin_vec::ThinVec::from_iter([P(inner)]),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn w6p_weakening_renders_the_operand_under_a_shared_borrow() {
        let weakening = SharedWeakening {
            argument_span: Span::default(),
            operand_span: Span::default(),
            original: "&mut orig_params.dist".to_owned(),
            operand: "orig_params.dist".to_owned(),
            optional: false,
        };
        assert_eq!(
            weakening.render("&mut orig_params.dist").as_deref(),
            Some("&(orig_params.dist)")
        );
        assert_eq!(
            weakening.render("&mut  orig_params.dist").as_deref(),
            Some("&(orig_params.dist)"),
            "whitespace-insensitive precondition"
        );
        assert_eq!(
            weakening.render("&mut new_params.dist"),
            None,
            "a different argument text renders nothing"
        );
        let optional = SharedWeakening {
            optional: true,
            ..weakening
        };
        assert_eq!(
            optional.render("&mut orig_params.dist").as_deref(),
            Some("Some(&(orig_params.dist))")
        );
    }
}
