//! **R631-12 (relay 130) — the argument-order hoist, the emission premise of
//! L01¹⁰'s arm (a)** (era-5c's record `2026-09-28-l01p10-argument-order-and-
//! overlap-type-route.md` §1). The arm admits a call whose argument list reads
//! through the place a reborrow the same call receives borrows
//! (`insert_(tree, (*tree).root, …)`): nothing between the reborrow and the call
//! writes, so the read has one value wherever it runs in that window. The
//! emission owes the read as a `let` above the reborrow:
//! `{ let __crat_hoist_… = (*tree).root; insert_(tree, __crat_hoist_…, …) }`.
//!
//! A bare `&mut` local passed at a `&mut` formal is a two-phase implicit
//! reborrow, which rustc already accepts with the read beside it; an explicit
//! one (`&mut *x`, or the `Option` glue `x.as_deref_mut().unwrap()`) is E0499 /
//! E0502 / E0503. The hoist applies to every receipted call either way.
//!
//! **The fallback is E5C-3's:** a call the hoist cannot rewrite (another arm
//! owns the node, or it is no longer a call) is left as emitted, fails to
//! compile, and its function reverts. It never ships a reordered form that the
//! receipt does not license.

use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashSet;

use super::ast_transform::{Composition, graft_expr};

/// The local a received reborrow argument lends, if the argument is one: the
/// argument peels to a bare local through parentheses, `&*` / `&mut *`, and the
/// reference-view methods the glue renders.
fn received_local(argument: &rustc_ast::Expr) -> Option<rustc_span::Symbol> {
    match &argument.kind {
        rustc_ast::ExprKind::Paren(inner) => received_local(inner),
        rustc_ast::ExprKind::AddrOf(_, _, inner) => match &inner.kind {
            rustc_ast::ExprKind::Unary(rustc_ast::UnOp::Deref, place) => received_local(place),
            _ => None,
        },
        rustc_ast::ExprKind::MethodCall(call)
            if call.args.is_empty()
                && matches!(
                    call.seg.ident.name.as_str(),
                    "as_deref_mut" | "as_deref" | "as_mut" | "as_ref" | "unwrap"
                ) =>
        {
            received_local(&call.receiver)
        }
        rustc_ast::ExprKind::Path(None, path) if path.segments.len() == 1 => {
            Some(path.segments[0].ident.name)
        }
        _ => None,
    }
}

/// Whether `expression` names any of `locals`.
fn mentions(expression: &rustc_ast::Expr, locals: &[rustc_span::Symbol]) -> bool {
    struct Find<'a>(&'a [rustc_span::Symbol], bool);
    impl<'ast> rustc_ast::visit::Visitor<'ast> for Find<'_> {
        fn visit_expr(&mut self, e: &'ast rustc_ast::Expr) {
            if let rustc_ast::ExprKind::Path(None, path) = &e.kind
                && path.segments.len() == 1
                && self.0.contains(&path.segments[0].ident.name)
            {
                self.1 = true;
            }
            rustc_ast::visit::walk_expr(self, e);
        }
    }
    let mut find = Find(locals, false);
    rustc_ast::visit::Visitor::visit_expr(&mut find, expression);
    find.1
}

/// Hoists the read-through arguments of every receipted call (keyed by the
/// call's span).
pub(crate) struct HoistVisitor<'a> {
    calls: &'a FxHashSet<(u32, u32)>,
    guard: &'a mut Composition,
    applied: usize,
    held: Vec<&'static str>,
}

impl<'a> HoistVisitor<'a> {
    pub(crate) fn new(calls: &'a FxHashSet<(u32, u32)>, guard: &'a mut Composition) -> Self {
        Self {
            calls,
            guard,
            applied: 0,
            held: Vec::new(),
        }
    }

    /// The calls hoisted, and the reason each receipted call was not.
    pub(crate) fn finish(self) -> (usize, Vec<&'static str>) {
        (self.applied, self.held)
    }

    fn hoist(&mut self, expression: &mut rustc_ast::Expr) -> Result<(), &'static str> {
        let lo = expression.span.lo().0;
        let rustc_ast::ExprKind::Call(_, arguments) = &mut expression.kind else {
            return Err("not-a-call");
        };
        let received = arguments
            .iter()
            .filter_map(|argument| received_local(argument))
            .collect::<Vec<_>>();
        let reads = arguments
            .iter()
            .enumerate()
            .filter(|(_, argument)| {
                received_local(argument).is_none() && mentions(argument, &received)
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if reads.is_empty() {
            return Err("no-read-through-a-received-reborrow");
        }
        let mut lets = String::new();
        for index in reads {
            let name = format!("__crat_hoist_{lo}_{index}");
            lets.push_str(&format!(
                "let {name} = {};\n",
                pprust::expr_to_string(&arguments[index])
            ));
            arguments[index] = rustc_ast::ptr::P(graft_expr(&name).map_err(|_| "unparsable")?);
        }
        let rendered = format!("{{\n{lets}{}\n}}", pprust::expr_to_string(expression));
        let parsed = graft_expr(&rendered).map_err(|_| "unparsable")?;
        if !self
            .guard
            .claim(expression.id, expression.span, "arg-order-hoist")
        {
            return Err("node-claimed-by-another-arm");
        }
        expression.kind = parsed.kind;
        Ok(())
    }
}

impl MutVisitor for HoistVisitor<'_> {
    fn visit_expr(&mut self, expression: &mut rustc_ast::Expr) {
        // Children first: a receipted call nested in another's argument list is
        // hoisted inside it, and the outer call then sees its product.
        rustc_ast::mut_visit::walk_expr(self, expression);
        if expression.span.is_dummy()
            || !self
                .calls
                .contains(&(expression.span.lo().0, expression.span.hi().0))
        {
            return;
        }
        let pristine = expression.kind.clone();
        match self.hoist(expression) {
            Ok(()) => self.applied += 1,
            Err(why) => {
                expression.kind = pristine;
                self.held.push(why);
            }
        }
    }
}

/// The emission step: an arm-(a) receipt is hoisted while its received
/// subject is decided a reference form. A raw subject passes a raw pointer,
/// which borrows nothing, so its call is left as the input wrote it (and a
/// revert-all round stays byte-identical). A reverted function needs no check
/// here: with the subject decided `&mut`, the revert-all round stays
/// byte-identical with the hoist applied (measured; fault F5 is inert). A
/// receipt the walk cannot apply is held (the function then reverts on its own
/// compile failure); nothing aborts the program.
pub(crate) fn apply(
    table: &super::decision::DecisionTable,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) {
    let calls = table
        .arg_order_hoists
        .iter()
        .filter(|(_, caller, local)| {
            table.entries.iter().any(|(subject, decision)| {
                subject.fn_did == *caller
                    && subject.local == *local
                    && match decision {
                        super::decision::Decision::Ref { .. }
                        | super::decision::Decision::InferredRef { .. }
                        | super::decision::Decision::Cursor { .. }
                        | super::decision::Decision::NestedSlice { .. }
                        | super::decision::Decision::Slice { .. }
                        | super::decision::Decision::Opt { .. }
                        | super::decision::Decision::Box(_) => true,
                        super::decision::Decision::Degraded(_) => false,
                    }
            })
        })
        .map(|(key, _, _)| *key)
        .collect::<FxHashSet<_>>();
    if calls.is_empty() {
        return;
    }
    let mut visitor = HoistVisitor::new(&calls, guard);
    visitor.visit_crate(krate);
}
