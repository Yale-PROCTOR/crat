//! An existing forward Slice decision can keep its base and advance an index.
//! This changes presentation only after the normal use and boundary proofs.

use rustc_ast::mut_visit::{self, MutVisitor};

/// Where a spine ends: the consumer of its outermost expression.
enum SpineEnd {
    /// One argument of a call.
    Argument,
    /// The initializer of `let <binding> = …` or the value of `<binding> = …`.
    Copy {
        destination: HirId,
    },
    Other,
}

fn spine_end<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Option<(
    &'tcx Expr<'tcx>,
    Option<(bool, Span)>,
    &'tcx Expr<'tcx>,
    SpineEnd,
)> {
    let owner = expr.hir_id.owner.def_id;
    let rustc_hir::Node::Expr(call) = tcx.parent_hir_node(expr.hir_id) else {
        return None;
    };
    let ExprKind::MethodCall(segment, receiver, [delta], _) = call.kind else {
        return None;
    };
    if receiver.hir_id != expr.hir_id || !matches!(segment.ident.name.as_str(), "offset" | "add") {
        return None;
    }
    let typeck = tcx.typeck(owner);
    let callee = typeck.type_dependent_def_id(call.hir_id)?;
    if tcx.crate_name(callee.krate).as_str() != "core" {
        return None;
    }
    let mut operand = call;
    let mut borrowed = None;
    loop {
        let parent = match tcx.parent_hir_node(operand.hir_id) {
            rustc_hir::Node::Expr(parent) => parent,
            rustc_hir::Node::LetStmt(local)
                if local.init.is_some_and(|init| init.hir_id == operand.hir_id) =>
            {
                let rustc_hir::PatKind::Binding(_, destination, _, None) = local.pat.kind else {
                    return None;
                };
                return Some((operand, borrowed, delta, SpineEnd::Copy { destination }));
            }
            _ => return None,
        };
        match parent.kind {
            ExprKind::Cast(inner, _) if inner.hir_id == operand.hir_id => operand = parent,
            ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == operand.hir_id => {
                let Some(destination) = local(lhs) else {
                    return Some((operand, borrowed, delta, SpineEnd::Other));
                };
                return Some((operand, borrowed, delta, SpineEnd::Copy { destination }));
            }
            ExprKind::Unary(rustc_hir::UnOp::Deref, inner)
                if inner.hir_id == operand.hir_id && borrowed.is_none() =>
            {
                let rustc_hir::Node::Expr(borrow) = tcx.parent_hir_node(parent.hir_id) else {
                    return None;
                };
                let ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, mutability, place) = borrow.kind
                else {
                    return None;
                };
                if place.hir_id != parent.hir_id {
                    return None;
                }
                borrowed = Some((mutability == rustc_hir::Mutability::Mut, borrow.span));
                operand = borrow;
            }
            // The spine ends at the call argument: the consumer must be a
            // call, and this operand one of its arguments.
            ExprKind::Call(_, arguments) | ExprKind::MethodCall(_, _, arguments, _)
                if arguments
                    .iter()
                    .any(|argument| argument.hir_id == operand.hir_id) =>
            {
                return Some((operand, borrowed, delta, SpineEnd::Argument));
            }
            _ => return Some((operand, borrowed, delta, SpineEnd::Other)),
        }
    }
}

/// A computed sub-view copied into a LOCAL: `let q = &*p.offset(e) as *const T`
/// / `q = p.offset(e)`. The copy is the collector's body-copy raw use with the
/// view attached; the receipt planner renders it by the destination's form.
pub(crate) fn computed_body_copy_view<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
    key: (LocalDefId, HirId),
) -> Option<(SliceRawUse, ComputedArgumentView)> {
    let (operand, borrowed, delta, end) = spine_end(tcx, expr)?;
    let SpineEnd::Copy { destination } = end else {
        return None;
    };
    // A self-advance (`p = p.offset(e)`) is the classifier's reslice, not a
    // copy into another binding.
    if destination == key.1 || !forward_delta(tcx, delta) {
        return None;
    }
    let typeck = tcx.typeck(key.0);
    let target = raw_target_type(tcx, typeck.expr_ty(operand))?;
    Some((
        SliceRawUse {
            hir_id: expr.hir_id,
            span: expr.span,
            boundary_span: None,
            source_shape: "body-copy",
            target,
            native_element: false,
            destination: Some(destination),
            contract: None,
        },
        ComputedArgumentView {
            use_span: expr.span,
            argument_span: operand.span,
            index: index_text(tcx, delta)?,
            borrowed: borrowed.is_some(),
            borrow_span: borrowed.map(|(_, span)| span),
            mutable: borrowed.is_some_and(|(mutable, _)| mutable),
            argument: false,
        },
    ))
}
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::{
    Decision, DecisionTable, Degradation, DegradeReason, SubjectKind,
    emitability::{EmitabilityFacts, SliceRawUse, SliceUses, UseEdit, classify_arg, index_text},
    raw_boundary::raw_target_type,
};

/// The receipt key a computed sub-view argument carries once its seam renders
/// the suffix. Consumers that key on the original borrow/cast shapes fall to
/// their terminal-source default, which is the view the callee now receives.
pub(crate) const COMPUTED_SUFFIX_VIEW: &str = "computed-suffix-view";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ForwardParameter {
    pub(crate) node: (LocalDefId, HirId),
    pub(crate) body_span: Span,
    pub(crate) index_name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ForwardView {
    pub(crate) index_name: String,
    pub(crate) mutable: bool,
    /// wave-6s computed sub-view: the base binding's own path inside the
    /// argument. `None` shifts the whole argument (a forward parameter's bare
    /// use); `Some` shifts only that subtree and discards the arithmetic
    /// around it, so the seam's `arg_span` and its revert twin stay whole.
    pub(crate) root: Option<Span>,
}

impl ForwardView {
    pub(crate) fn render(&self, argument: &str) -> String {
        let borrow = if self.mutable { "&mut " } else { "&" };
        format!("({borrow}({argument})[{}..])", self.index_name)
    }
}

/// A computed sub-view of a delivered slice base that is itself a raw-boundary
/// argument: `&*p.offset(e)`, `&mut *p.offset(e)`, `p.offset(e) as *const T`
/// or a bare `p.offset(e)`. The boundary keeps its own disposition and
/// receipts; the seam renders the checked suffix `&p[e..]` in place of the
/// arithmetic, and the existing bridge adds `.as_ptr()` / `.as_mut_ptr()`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ComputedArgumentView {
    /// The subject's own path expression inside the argument.
    pub(crate) use_span: Span,
    /// The whole boundary argument the seam replaces.
    pub(crate) argument_span: Span,
    /// The suffix start, already typed `usize`.
    pub(crate) index: String,
    /// The spine borrowed the element (`&*` / `&mut *`) rather than passing
    /// the arithmetic itself.
    pub(crate) borrowed: bool,
    /// The `&*…` / `&mut *…` expression itself, when the spine borrows.
    pub(crate) borrow_span: Option<Span>,
    pub(crate) mutable: bool,
    /// A call argument (rendered on its seam by `lower`) rather than a body
    /// copy (rendered by the slice-use receipt planner).
    pub(crate) argument: bool,
}

/// Recognise a computed sub-view argument rooted at `expr` (the subject's
/// path). Only the exact borrow/cast spine between the arithmetic and a
/// registered boundary argument is accepted; any other consumer of the
/// arithmetic (a copy, a store, a comparison, a distance) is not a view and
/// stays with the collector's ordinary verdict.
/// The spine above the subject's arithmetic: `p.offset(e)` under any casts,
/// optionally `&*` / `&mut *` borrowed once, then casts again. Returns the
/// outermost expression of the spine, its borrow mutability and the delta.
/// Every other consumer of the arithmetic is refused here.
pub(crate) fn computed_view_spine<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Option<&'tcx Expr<'tcx>> {
    spine(tcx, expr)
        .filter(|(_, _, delta)| forward_delta(tcx, delta))
        .map(|(outer, _, _)| outer)
}

/// Where a spine ends: the consumer of its outermost expression.
enum SpineEnd {
    /// One argument of a call.
    Argument,
    /// The initializer of `let <binding> = …` or the value of `<binding> = …`.
    Copy {
        destination: HirId,
    },
    Other,
}

fn spine<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Option<(&'tcx Expr<'tcx>, Option<(bool, Span)>, &'tcx Expr<'tcx>)> {
    spine_end(tcx, expr).and_then(|(operand, borrowed, delta, end)| {
        matches!(end, SpineEnd::Argument).then_some((operand, borrowed, delta))
    })
}

fn spine_end<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Option<(
    &'tcx Expr<'tcx>,
    Option<(bool, Span)>,
    &'tcx Expr<'tcx>,
    SpineEnd,
)> {
    let owner = expr.hir_id.owner.def_id;
    let rustc_hir::Node::Expr(call) = tcx.parent_hir_node(expr.hir_id) else {
        return None;
    };
    let ExprKind::MethodCall(segment, receiver, [delta], _) = call.kind else {
        return None;
    };
    if receiver.hir_id != expr.hir_id || !matches!(segment.ident.name.as_str(), "offset" | "add") {
        return None;
    }
    let typeck = tcx.typeck(owner);
    let callee = typeck.type_dependent_def_id(call.hir_id)?;
    if tcx.crate_name(callee.krate).as_str() != "core" {
        return None;
    }
    let mut operand = call;
    let mut borrowed = None;
    loop {
        let parent = match tcx.parent_hir_node(operand.hir_id) {
            rustc_hir::Node::Expr(parent) => parent,
            rustc_hir::Node::LetStmt(local)
                if local.init.is_some_and(|init| init.hir_id == operand.hir_id) =>
            {
                let rustc_hir::PatKind::Binding(_, destination, _, None) = local.pat.kind else {
                    return None;
                };
                return Some((operand, borrowed, delta, SpineEnd::Copy { destination }));
            }
            _ => return None,
        };
        match parent.kind {
            ExprKind::Cast(inner, _) if inner.hir_id == operand.hir_id => operand = parent,
            ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == operand.hir_id => {
                let Some(destination) = local(lhs) else {
                    return Some((operand, borrowed, delta, SpineEnd::Other));
                };
                return Some((operand, borrowed, delta, SpineEnd::Copy { destination }));
            }
            ExprKind::Unary(rustc_hir::UnOp::Deref, inner)
                if inner.hir_id == operand.hir_id && borrowed.is_none() =>
            {
                let rustc_hir::Node::Expr(borrow) = tcx.parent_hir_node(parent.hir_id) else {
                    return None;
                };
                let ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, mutability, place) = borrow.kind
                else {
                    return None;
                };
                if place.hir_id != parent.hir_id {
                    return None;
                }
                borrowed = Some((mutability == rustc_hir::Mutability::Mut, borrow.span));
                operand = borrow;
            }
            // The spine ends at the call argument: the consumer must be a
            // call, and this operand one of its arguments.
            ExprKind::Call(_, arguments) | ExprKind::MethodCall(_, _, arguments, _)
                if arguments
                    .iter()
                    .any(|argument| argument.hir_id == operand.hir_id) =>
            {
                return Some((operand, borrowed, delta, SpineEnd::Argument));
            }
            _ => return Some((operand, borrowed, delta, SpineEnd::Other)),
        }
    }
}

/// A computed sub-view copied into a LOCAL: `let q = &*p.offset(e) as *const T`
/// / `q = p.offset(e)`. The copy is the collector's body-copy raw use with the
/// view attached; the receipt planner renders it by the destination's form.
pub(crate) fn computed_body_copy_view<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
    key: (LocalDefId, HirId),
) -> Option<(SliceRawUse, ComputedArgumentView)> {
    let (operand, borrowed, delta, end) = spine_end(tcx, expr)?;
    let SpineEnd::Copy { destination } = end else {
        return None;
    };
    // A self-advance (`p = p.offset(e)`) is the classifier's reslice, not a
    // copy into another binding.
    if destination == key.1 || !forward_delta(tcx, delta) {
        return None;
    }
    let typeck = tcx.typeck(key.0);
    let target = raw_target_type(tcx, typeck.expr_ty(operand))?;
    Some((
        SliceRawUse {
            hir_id: expr.hir_id,
            span: expr.span,
            boundary_span: None,
            source_shape: "body-copy",
            target,
            native_element: false,
            destination: Some(destination),
            contract: None,
        },
        ComputedArgumentView {
            use_span: expr.span,
            argument_span: operand.span,
            index: index_text(tcx, delta)?,
            borrowed: borrowed.is_some(),
            borrow_span: borrowed.map(|(_, span)| span),
            mutable: borrowed.is_some_and(|(mutable, _)| mutable),
            argument: false,
        },
    ))
}

/// Forward-only: the delta, under its `as isize` casts, is a non-negative
/// integer literal or an expression of unsigned type. A signed or negated
/// delta is the bidirectional family's (R394-2) and stays with the cursor
/// verdict. Conditional on a UB-free input, an unsigned C index added to a
/// pointer never moves it backwards.
fn forward_delta<'tcx>(tcx: TyCtxt<'tcx>, delta: &'tcx Expr<'tcx>) -> bool {
    let mut inner = delta;
    while let ExprKind::Cast(operand, _) = inner.kind {
        inner = operand;
    }
    if matches!(&inner.kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(..)))
    {
        return true;
    }
    let owner = inner.hir_id.owner.def_id;
    tcx.typeck(owner)
        .expr_ty_opt(inner)
        .is_some_and(|ty| matches!(ty.kind(), rustc_middle::ty::TyKind::Uint(_)))
}

pub(crate) fn computed_argument_view<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx Expr<'tcx>,
    key: (LocalDefId, HirId),
    raw_boundary_arguments: &FxHashSet<(LocalDefId, HirId, u32, u32)>,
) -> Option<(SliceRawUse, ComputedArgumentView)> {
    let (operand, borrowed, delta) = spine(tcx, expr)?;
    if !raw_boundary_arguments.contains(&(key.0, key.1, operand.span.lo().0, operand.span.hi().0))
        || !forward_delta(tcx, delta)
    {
        return None;
    }
    debug_assert!(computed_view_spine(tcx, expr).is_some());
    let typeck = tcx.typeck(key.0);
    let target = raw_target_type(tcx, typeck.expr_ty_adjusted(operand))?;
    let index = index_text(tcx, delta)?;
    Some((
        SliceRawUse {
            hir_id: expr.hir_id,
            span: expr.span,
            boundary_span: Some(operand.span),
            source_shape: classify_arg(tcx, operand).key(),
            target,
            native_element: false,
            destination: None,
            contract: None,
        },
        ComputedArgumentView {
            use_span: expr.span,
            argument_span: operand.span,
            index,
            borrowed: borrowed.is_some(),
            borrow_span: borrowed.map(|(_, span)| span),
            mutable: borrowed.is_some_and(|(mutable, _)| mutable),
            argument: true,
        },
    ))
}

fn local(expression: &Expr<'_>) -> Option<HirId> {
    match expression.kind {
        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
            Res::Local(binding) => Some(binding),
            _ => None,
        },
        _ => None,
    }
}

struct Advance {
    assignment: Span,
    rhs: Span,
    delta: String,
}

struct Inventory<'tcx> {
    tcx: TyCtxt<'tcx>,
    node: (LocalDefId, HirId),
    name: String,
    index_name: String,
    advances: Vec<Advance>,
    uses: Vec<Span>,
    collision: bool,
}

impl<'tcx> Visitor<'tcx> for Inventory<'tcx> {
    fn visit_pat(&mut self, pattern: &'tcx rustc_hir::Pat<'tcx>) {
        if let rustc_hir::PatKind::Binding(_, binding, ident, _) = pattern.kind {
            self.collision |= ident.name.as_str() == self.index_name
                || (ident.name.as_str() == self.name && binding != self.node.1);
        }
        intravisit::walk_pat(self, pattern);
    }

    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        if local(expression) == Some(self.node.1) {
            self.uses.push(expression.span);
        }
        if let ExprKind::Assign(lhs, rhs, _) = expression.kind
            && local(lhs) == Some(self.node.1)
            && let ExprKind::MethodCall(segment, receiver, [delta], _) = rhs.kind
            && local(receiver) == Some(self.node.1)
            && matches!(segment.ident.name.as_str(), "offset" | "add")
            && self
                .tcx
                .typeck(self.node.0)
                .type_dependent_def_id(rhs.hir_id)
                .is_some_and(|callee| self.tcx.crate_name(callee.krate).as_str() == "core")
            && let Ok(delta) = self.tcx.sess.source_map().span_to_snippet(delta.span)
        {
            self.advances.push(Advance {
                assignment: expression.span,
                rhs: rhs.span,
                delta,
            });
        }
        intravisit::walk_expr(self, expression);
    }
}

fn contains(outer: Span, inner: Span) -> bool {
    outer.lo() <= inner.lo() && inner.hi() <= outer.hi()
}

fn shifted_use(edit: &UseEdit, name: &str, view: &ForwardView) -> Option<UseEdit> {
    struct Shift<'a> {
        name: &'a str,
        replacement: rustc_ast::Expr,
        hits: usize,
    }
    impl MutVisitor for Shift<'_> {
        fn visit_expr(&mut self, expression: &mut rustc_ast::Expr) {
            if matches!(&expression.kind, rustc_ast::ExprKind::Path(None, path)
                if path.segments.len() == 1 && path.segments[0].ident.name.as_str() == self.name)
            {
                expression.kind = self.replacement.kind.clone();
                self.hits += 1;
                return;
            }
            mut_visit::walk_expr(self, expression);
        }
    }
    let (mut parsed, replacement) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        (
            ::utils::ast::parse_expr(edit.replacement.clone()),
            ::utils::ast::parse_expr(view.render(name)),
        )
    }))
    .ok()?;
    let mut shift = Shift {
        name,
        replacement,
        hits: 0,
    };
    shift.visit_expr(&mut parsed);
    (shift.hits > 0).then(|| UseEdit {
        span: edit.span,
        replacement: rustc_ast_pretty::pprust::expr_to_string(&parsed),
        bridge_kind: edit.bridge_kind,
    })
}

/// Select only complete existing Slice presentations. An uncovered occurrence
/// keeps the established reslice form; it never obtains new admission here.
pub(crate) fn lower(
    tcx: TyCtxt<'_>,
    table: &mut DecisionTable,
    advance_ok: &FxHashSet<(LocalDefId, HirId)>,
    native: &super::raw_boundary::RawBoundarySiteFacts,
    slice_uses: &FxHashMap<(LocalDefId, HirId), SliceUses>,
) -> Result<(), String> {
    lower_forward_parameters(tcx, table, advance_ok, native)?;
    lower_computed_argument_views(tcx, table, slice_uses)
}

/// Render every admitted computed sub-view argument of a Slice subject on its
/// own raw-boundary seam: the seam's operand becomes the base binding, the
/// carried view supplies `[e..]`, and the existing bridge template adds the
/// pointer conversion. A view whose seam is absent, already shifted, or of
/// the wrong mutability holds the subject typed at that site.
fn lower_computed_argument_views(
    tcx: TyCtxt<'_>,
    table: &mut DecisionTable,
    slice_uses: &FxHashMap<(LocalDefId, HirId), SliceUses>,
) -> Result<(), String> {
    use super::seam::{Form, GlueCore, GlueSpec, SeamFamily};
    for entry in 0..table.entries.len() {
        let (subject, decision) = &table.entries[entry];
        let node = (subject.fn_did, subject.hir_id);
        let mutable = match decision {
            Decision::Slice { mutable, .. } => *mutable,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => continue,
        };
        let Some(views) = slice_uses
            .get(&node)
            .map(|uses| {
                uses.computed_argument_views
                    .iter()
                    .filter(|view| view.argument)
                    .collect::<Vec<_>>()
            })
            .filter(|views| !views.is_empty())
        else {
            continue;
        };
        let Some(name) = subject.param_name.clone() else { continue };
        let enclosing_unsafe_fn = tcx
            .fn_sig(node.0)
            .skip_binder()
            .skip_binder()
            .safety
            .is_unsafe();
        let mut seams = Vec::new();
        let mut element_uses = Vec::new();
        let mut hold = None;
        for view in views {
            let carriers = table
                .seams
                .edits
                .iter()
                .enumerate()
                .filter(|(_, edit)| {
                    edit.source_node == Some(node) && edit.span == view.argument_span
                })
                .map(|(index, _)| index)
                .collect::<Vec<_>>();
            let source = Decision::Slice {
                mutable,
                uses: Vec::new(),
            };
            let forward = |view_mutable: bool| ForwardView {
                index_name: view.index.clone(),
                mutable: view_mutable,
                root: Some(view.use_span),
            };
            let index = match carriers.as_slice() {
                // No seam: a borrowed element handed to a converted THIN
                // reference parameter coerces as written, so the view is the
                // checked element `&mut p[e]`, a use edit of the subject.
                [] if view.borrowed && (!view.mutable || mutable) => {
                    let amp = if view.mutable { "&mut " } else { "&" };
                    element_uses.push(UseEdit {
                        span: view.argument_span,
                        replacement: format!("{amp}({name})[{}]", view.index),
                        bridge_kind: "subject-use",
                    });
                    continue;
                }
                [index] => *index,
                _ => {
                    hold = Some(view.use_span);
                    break;
                }
            };
            let mut edit = table.seams.edits[index].clone();
            if edit.spec.forward_slice.is_some() || edit.spec.shared_address.is_some() {
                hold = Some(view.use_span);
                break;
            }
            if let Some(endpoint) = edit.raw_outbound.as_mut() {
                // A raw callee: the operand the seam wraps is now the base
                // binding, and the bridge is the one the terminal sealing
                // derives for a SLICE source at this target. A raw-expression
                // argument previously carried a typed raw temporary, which the
                // sealing would keep; a suffix view is not a raw expression,
                // so it takes the slice template like a bare slice argument.
                let target_mutable = matches!(
                    endpoint.target.mutability,
                    super::raw_boundary::RawMutability::Mut
                );
                if target_mutable && !mutable {
                    hold = Some(view.use_span);
                    break;
                }
                endpoint.operand_expression = name.clone();
                let template = match super::raw_boundary::template_for(
                    &source,
                    &endpoint.target,
                    endpoint.ownership,
                    endpoint.negative_write,
                ) {
                    Ok(template) => template,
                    Err(_) => {
                        hold = Some(view.use_span);
                        break;
                    }
                };
                let mut spec = GlueSpec::raw_boundary_target(
                    template,
                    &endpoint.target,
                    endpoint.box_slice,
                    false,
                );
                spec.forward_slice = Some(forward(target_mutable));
                edit.spec = spec;
                edit.bridge.bridge_kind = template.key().to_owned();
            } else if edit.spec.raw_boundary.is_none()
                && let Form::Ref {
                    mutable: expected_mutable,
                } = edit.expected
                && matches!(edit.spec.core, GlueCore::Reborrow)
            {
                // The arithmetic itself reborrowed into a converted THIN
                // reference parameter: the callee accesses one element, so the
                // view is the checked element of the suffix.
                if expected_mutable && !mutable {
                    hold = Some(view.use_span);
                    break;
                }
                let mut spec = GlueSpec::core(GlueCore::Index0, expected_mutable);
                spec.forward_slice = Some(forward(expected_mutable));
                edit.spec = spec;
                edit.family = SeamFamily::Safe;
                edit.bridge.bridge_kind = "computed-suffix-view-element".to_owned();
            } else if edit.spec.raw_boundary.is_none()
                && let Form::Slice {
                    mutable: expected_mutable,
                } = edit.expected
                && matches!(edit.spec.core, GlueCore::FromRefMut)
            {
                // A borrowed element widened into a converted SLICE parameter:
                // the suffix is already that slice.
                if expected_mutable && !mutable {
                    hold = Some(view.use_span);
                    break;
                }
                let mut spec = GlueSpec::core(GlueCore::Bare, expected_mutable);
                spec.forward_slice = Some(forward(expected_mutable));
                edit.spec = spec;
                edit.family = SeamFamily::Safe;
                edit.bridge.bridge_kind = "computed-suffix-view".to_owned();
            } else {
                hold = Some(view.use_span);
                break;
            }
            edit.found = super::seam::form_of(&source);
            edit.bridge.found_form = edit.found.key().to_owned();
            edit.source_shape = COMPUTED_SUFFIX_VIEW;
            edit.replacement = edit
                .spec
                .render_in_context(&name, enclosing_unsafe_fn)
                .ok_or("computed-suffix-view:seam-render-unavailable")?;
            edit.zero_syntax = false;
            seams.push((index, edit));
        }
        if let Some(site) = hold {
            let site = EmitabilityFacts::site(tcx, site);
            table.entries[entry].1 = Decision::Degraded(Degradation {
                subject: subject.label.clone(),
                site,
                reason: DegradeReason::SliceUseUnsupported,
            });
            continue;
        }
        for (index, edit) in seams {
            table.seams.edits[index] = edit;
        }
        match &mut table.entries[entry].1 {
            Decision::Slice { uses, .. } => uses.extend(element_uses),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => unreachable!("selected slice keeps its decision"),
        }
    }
    Ok(())
}

fn lower_forward_parameters(
    tcx: TyCtxt<'_>,
    table: &mut DecisionTable,
    advance_ok: &FxHashSet<(LocalDefId, HirId)>,
    native: &super::raw_boundary::RawBoundarySiteFacts,
) -> Result<(), String> {
    for entry in 0..table.entries.len() {
        let (subject, decision) = &table.entries[entry];
        let node = (subject.fn_did, subject.hir_id);
        let uses = match decision {
            Decision::Slice {
                mutable: false,
                uses,
            } => uses,
            Decision::Slice { mutable: true, .. }
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => continue,
        };
        // Keep existing reslice presentations stable. This first rule owns
        // forward call-bearing subjects with newly proved result independence.
        if !native.sites.iter().any(|site| {
            site.node == Some(node) && native.forward_return_independent.contains_key(&site.key)
        }) {
            continue;
        }
        if !matches!(subject.kind, SubjectKind::Param { .. }) || !advance_ok.contains(&node) {
            continue;
        }
        let Some(name) = subject.param_name.as_deref() else { continue };
        let index_name = format!(
            "__crat_wave6s_pos_{}_{}",
            node.0.local_def_index.as_u32(),
            node.1.local_id.as_u32()
        );
        let body = tcx.hir_body_owned_by(node.0);
        let ExprKind::Block(block, _) = body.value.kind else { continue };
        let mut inventory = Inventory {
            tcx,
            node,
            name: name.to_owned(),
            index_name: index_name.clone(),
            advances: Vec::new(),
            uses: Vec::new(),
            collision: false,
        };
        inventory.visit_body(body);
        if inventory.collision || inventory.advances.is_empty() {
            continue;
        }
        // The existing source edit licenses each advancement. Reject nested
        // edits and nested uses in its delta rather than embedding stale text.
        if inventory.advances.iter().any(|advance| {
            uses.iter().filter(|edit| edit.span == advance.rhs).count() != 1
                || uses
                    .iter()
                    .any(|edit| edit.span != advance.rhs && contains(advance.assignment, edit.span))
                || inventory
                    .uses
                    .iter()
                    .filter(|&&span| contains(advance.assignment, span))
                    .count()
                    != 2
        }) {
            continue;
        }
        let seam_indices = table
            .seams
            .edits
            .iter()
            .enumerate()
            .filter(|(_, edit)| {
                edit.source_node == Some(node)
                    && inventory.uses.contains(&edit.arg_span)
                    && edit.spec.shared_address.is_none()
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if inventory.uses.iter().any(|&span| {
            !inventory
                .advances
                .iter()
                .any(|advance| contains(advance.assignment, span))
                && !uses.iter().any(|edit| contains(edit.span, span))
                && !seam_indices
                    .iter()
                    .any(|&index| table.seams.edits[index].arg_span == span)
        }) {
            continue;
        }
        let view = ForwardView {
            index_name: index_name.clone(),
            mutable: false,
            root: None,
        };
        let mut replacements = Vec::new();
        let mut complete = true;
        for edit in uses {
            if let Some(advance) = inventory.advances.iter().find(|a| a.rhs == edit.span) {
                replacements.push(UseEdit {
                    span: advance.assignment,
                    replacement: format!(
                        "{index_name} = {index_name}.checked_add(({}) as usize).expect(\"forward slice index overflow\")",
                        advance.delta
                    ),
                    bridge_kind: "subject-use",
                });
            } else if let Some(edit) = shifted_use(edit, name, &view) {
                replacements.push(edit);
            } else {
                complete = false;
            }
        }
        if !complete {
            continue;
        }
        let mut seams = Vec::new();
        for index in seam_indices {
            let mut edit = table.seams.edits[index].clone();
            edit.spec.forward_slice = Some(view.clone());
            let argument = tcx
                .sess
                .source_map()
                .span_to_snippet(edit.arg_span)
                .map_err(|_| "forward-slice:seam-source-unavailable")?;
            edit.replacement = edit
                .spec
                .render_in_context(
                    &argument,
                    tcx.fn_sig(node.0)
                        .skip_binder()
                        .skip_binder()
                        .safety
                        .is_unsafe(),
                )
                .ok_or("forward-slice:seam-render-unavailable")?;
            // A suffix is syntax even if the original safe argument required
            // no wrapper. Keep the same boundary owner and permission receipt.
            edit.zero_syntax = false;
            seams.push((index, edit));
        }
        match &mut table.entries[entry].1 {
            Decision::Slice { uses, .. } => *uses = replacements,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => unreachable!("selected slice keeps its decision"),
        }
        for (index, edit) in seams {
            table.seams.edits[index] = edit;
        }
        table.forward_slice_parameters.push(ForwardParameter {
            node,
            body_span: block.span,
            index_name,
        });
    }
    Ok(())
}
