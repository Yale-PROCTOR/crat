//! An existing forward Slice decision can keep its base and advance an index.
//! This changes presentation only after the normal use and boundary proofs.

use rustc_ast::mut_visit::{self, MutVisitor};
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
    /// **W6S-14.** The source span [`Self::index`] was copied from, and
    /// whether it is wrapped `(…) as usize` — so [`composed_index`] can render
    /// it with another subject's edits inside it applied.
    pub(crate) index_span: Span,
    pub(crate) index_wrap: bool,
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
            index_span: super::emitability::index_parts(tcx, delta).0,
            index_wrap: super::emitability::index_parts(tcx, delta).1,
            borrowed: borrowed.is_some(),
            borrow_span: borrowed.map(|(_, span)| span),
            mutable: borrowed.is_some_and(|(mutable, _)| mutable),
            argument: false,
        },
    ))
}

/// Forward-only: the delta is a non-negative integer literal, an expression
/// of unsigned type, or a `+` of two forward deltas (lodepng
/// `chunk.offset((8 as isize) + (length as isize))`: each summand is
/// non-negative, and a sum that left the object would already be the input's
/// UB), seen through casts that PRESERVE non-negativity: to any unsigned
/// type; to a signed type strictly wider than an unsigned source, or at least
/// as wide as a non-negative signed source; or to a signed type of pointer
/// width, since an index at or above 2^63 cannot address an object. A
/// signed or negated delta, or one narrowed through a signed cast (`length
/// as c_int as isize` with `length: u32`), is the bidirectional family's
/// (R394-2) and stays with the cursor verdict. Conditional on a UB-free
/// input, a non-negative C index added to a pointer never moves it backwards.
fn forward_delta<'tcx>(tcx: TyCtxt<'tcx>, delta: &'tcx Expr<'tcx>) -> bool {
    use rustc_middle::ty::{IntTy, TyKind, UintTy};
    let owner = delta.hir_id.owner.def_id;
    let typeck = tcx.typeck(owner);
    let pointer_bits = tcx.data_layout.pointer_size.bits();
    let width = |ty: rustc_middle::ty::Ty<'tcx>| -> Option<(bool, u64)> {
        match ty.kind() {
            TyKind::Uint(UintTy::Usize) => Some((false, pointer_bits)),
            TyKind::Int(IntTy::Isize) => Some((true, pointer_bits)),
            TyKind::Uint(u) => Some((false, u.bit_width()?)),
            TyKind::Int(i) => Some((true, i.bit_width()?)),
            _ => None,
        }
    };
    // Innermost first: the chain of casts, outermost last.
    let mut casts = Vec::new();
    let mut inner = delta;
    while let ExprKind::Cast(operand, _) = inner.kind {
        casts.push(inner);
        inner = operand;
    }
    let base_forward = if let ExprKind::Binary(op, left, right) = inner.kind
        && op.node == rustc_hir::BinOpKind::Add
    {
        forward_delta(tcx, left) && forward_delta(tcx, right)
    } else if matches!(&inner.kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(..)))
    {
        true
    } else {
        typeck
            .expr_ty_opt(inner)
            .is_some_and(|ty| matches!(ty.kind(), TyKind::Uint(_)))
    };
    if !base_forward {
        return false;
    }
    let mut source = inner;
    for cast in casts.into_iter().rev() {
        let (Some((source_signed, source_bits)), Some((target_signed, target_bits))) = (
            typeck.expr_ty_opt(source).and_then(width),
            typeck.expr_ty_opt(cast).and_then(width),
        ) else {
            return false;
        };
        let preserved = !target_signed
            || target_bits >= pointer_bits
            || if source_signed {
                target_bits >= source_bits
            } else {
                target_bits > source_bits
            };
        if !preserved {
            return false;
        }
        source = cast;
    }
    true
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
            index_span: super::emitability::index_parts(tcx, delta).0,
            index_wrap: super::emitability::index_parts(tcx, delta).1,
            borrowed: borrowed.is_some(),
            borrow_span: borrowed.map(|(_, span)| span),
            mutable: borrowed.is_some_and(|(mutable, _)| mutable),
            argument: true,
        },
    ))
}

/// **W6S-7 — the LHS of `dst = <a forward computed view of another root>`.**
///
/// The destination's own use walk sees the assignment and must decide whether
/// it is in scope. It is: the right-hand side is this lane's computed view,
/// rendered by [`super::slice_use`] from the DESTINATION's form (a slice takes
/// the suffix, an optional slice the same suffix inside `Some(..)`), so the
/// use needs no edit of its own.
///
/// Structurally the same walk as wave-6s2's
/// [`super::slice_passon::assignment_from_computed_view`], under THIS lane's
/// sign authority ([`forward_delta`]): the two coincide except on the C2Rust
/// double-cast literal (`2 as i32 as isize`), which is a non-negative literal
/// under casts that preserve non-negativity and which their narrower rule
/// refuses. The unification of the two walks is a seat question, not a silent
/// edit of a neighbour's rule.
pub(crate) fn assignment_from_forward_view<'tcx>(
    tcx: TyCtxt<'tcx>,
    use_expr: &Expr<'_>,
    key: (LocalDefId, HirId),
) -> bool {
    // Only the identity of the use is taken from the caller's borrow; every
    // expression this walk reads is re-fetched from `tcx`.
    let rustc_hir::Node::Expr(assign) = tcx.parent_hir_node(use_expr.hir_id) else {
        return false;
    };
    let ExprKind::Assign(lhs, rhs, _) = assign.kind else {
        return false;
    };
    if lhs.hir_id != use_expr.hir_id {
        return false;
    }
    let typeck = tcx.typeck(key.0);
    let Some(destination_pointee) = raw_target_type(tcx, typeck.expr_ty(lhs)) else {
        return false;
    };
    // The C2Rust spine: identity casts and the borrow-of-deref around the
    // arithmetic.
    let mut value = rhs;
    loop {
        match value.kind {
            ExprKind::Cast(inner, _) => value = inner,
            ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, _, borrowed) => {
                let ExprKind::Unary(rustc_hir::UnOp::Deref, place) = borrowed.kind else {
                    return false;
                };
                value = place;
            }
            _ => break,
        }
    }
    let ExprKind::MethodCall(segment, receiver, [delta], _) = value.kind else {
        return false;
    };
    if !matches!(segment.ident.name.as_str(), "offset" | "add") {
        return false;
    }
    let Some(callee) = typeck.type_dependent_def_id(value.hir_id) else {
        return false;
    };
    if tcx.crate_name(callee.krate).as_str() != "core" {
        return false;
    }
    // A DIFFERENT binding as the root: a self-advance is the classifier's own
    // arm, and a root that is not a binding has no subject to carry the view.
    let Some(root) = local(receiver) else {
        return false;
    };
    if root == key.1 {
        return false;
    }
    // The view's element type is the destination's; a retyping cast is the
    // void-region family's evidence to supply, not this arm's.
    if raw_target_type(tcx, typeck.expr_ty(receiver))
        .is_none_or(|root_pointee| root_pointee.pointee != destination_pointee.pointee)
    {
        return false;
    }
    forward_delta(tcx, delta)
}

/// **W6S-11 — the same assignment with an ARRAY LOCAL as the view's root.**
///
/// heman `kmQuaternionRotationMatrix`:
///
/// ```text
/// let mut pMatrix = 0 as *mut c_float;
/// let mut m4x4: [c_float; 16] = [0.; 16];
/// pMatrix = &mut *m4x4.as_mut_ptr().offset(0) as *mut c_float;
/// ```
///
/// [`assignment_from_forward_view`] refuses this because the root is not a
/// pointer BINDING — an array local carries no subject, so there is no source
/// row to hang a view on and no name for the planner to render from. It needs
/// none: the array IS the view (`&mut m4x4[e..]`), its own extent is the
/// slice's, and nothing is fabricated. The SAME view in the local's
/// initialiser already delivers (the construction family types it); this is
/// the assignment form of it.
///
/// Returns the rendered view for the right-hand side, or nothing. Every
/// refusal is another family's position: a backward delta (the bidirectional
/// family's), an element type the destination does not share (the void-region
/// family's evidence), a root that is not a local array.
pub(crate) fn assignment_from_array_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    use_expr: &Expr<'_>,
    key: (LocalDefId, HirId),
    mutable: bool,
) -> Option<(Span, String)> {
    let rustc_hir::Node::Expr(assign) = tcx.parent_hir_node(use_expr.hir_id) else {
        return None;
    };
    let ExprKind::Assign(lhs, rhs, _) = assign.kind else {
        return None;
    };
    if lhs.hir_id != use_expr.hir_id {
        return None;
    }
    let typeck = tcx.typeck(key.0);
    let rustc_middle::ty::TyKind::RawPtr(destination_pointee, _) = typeck.expr_ty(lhs).kind()
    else {
        return None;
    };
    // The C2Rust spine: identity casts and the borrow-of-deref around the
    // arithmetic.
    let mut value = rhs;
    loop {
        match value.kind {
            ExprKind::Cast(inner, _) => value = inner,
            ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, _, borrowed) => {
                let ExprKind::Unary(rustc_hir::UnOp::Deref, place) = borrowed.kind else {
                    return None;
                };
                value = place;
            }
            _ => break,
        }
    }
    let ExprKind::MethodCall(segment, receiver, [delta], _) = value.kind else {
        return None;
    };
    if !matches!(segment.ident.name.as_str(), "offset" | "add") {
        return None;
    }
    let callee = typeck.type_dependent_def_id(value.hir_id)?;
    if tcx.crate_name(callee.krate).as_str() != "core" {
        return None;
    }
    // The root: `<array local>.as_mut_ptr()` / `.as_ptr()`.
    let ExprKind::MethodCall(root_segment, array, [], _) = receiver.kind else {
        return None;
    };
    if !matches!(root_segment.ident.name.as_str(), "as_mut_ptr" | "as_ptr") {
        return None;
    }
    let name = match array.kind {
        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
            Res::Local(binding) if binding != key.1 => tcx.hir_name(binding).to_ident_string(),
            _ => return None,
        },
        _ => return None,
    };
    // A LOCAL ARRAY, and its element is the destination's own.
    let rustc_middle::ty::TyKind::Array(element, _) = typeck.expr_ty(array).kind() else {
        return None;
    };
    if element != destination_pointee {
        return None;
    }
    if !forward_delta(tcx, delta) {
        return None;
    }
    let index = index_text(tcx, delta)?;
    let amp = if mutable { "&mut " } else { "&" };
    Some((rhs.span, format!("{amp}{name}[{index}..]")))
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

/// **W6S-14 (R554-3, wave-6s 075 N1) — the view's index, rendered with the
/// other subjects' edits inside it.** A view's index is the delta's SOURCE
/// text, captured by the collector before any decision exists. When the delta
/// itself reads another subject that delivers (`*block_ids.offset(i)` with
/// `block_ids: &[u8]`), that subject's own use edit lies INSIDE the span the
/// view replaces: copied raw, the view is ill-typed (`method not found in
/// &[u8]`); kept beside the view's edit, the two overlap and the family site
/// fails. So the index is rendered here, from the decided table: every other
/// subject's use edit contained in the index span is spliced in, and returned
/// so the caller can retire it once the view is admitted (the view's edit now
/// carries it). An edit that only partly overlaps, or a seam inside the index,
/// refuses the view — `None`.
fn composed_index(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    view: &ComputedArgumentView,
    own: (LocalDefId, HirId),
) -> Option<(String, Vec<(usize, Span)>)> {
    let within = |span: Span| view.index_span.contains(span);
    let overlaps =
        |span: Span| span.lo() < view.index_span.hi() && view.index_span.lo() < span.hi();
    if table
        .seams
        .edits
        .iter()
        .any(|edit| overlaps(edit.span) && !edit.span.contains(view.index_span))
    {
        return None;
    }
    let mut inner: Vec<(usize, Span, String)> = Vec::new();
    for (entry, (subject, decision)) in table.entries.iter().enumerate() {
        if (subject.fn_did, subject.hir_id) == own {
            continue;
        }
        let uses = match decision {
            Decision::Slice { uses, .. }
            | Decision::NestedSlice { uses, .. }
            | Decision::Opt { uses, .. } => uses,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => continue,
        };
        for edit in uses {
            if within(edit.span) {
                inner.push((entry, edit.span, edit.replacement.clone()));
            } else if overlaps(edit.span) && !edit.span.contains(view.index_span) {
                return None;
            }
        }
    }
    let mut text = tcx
        .sess
        .source_map()
        .span_to_snippet(view.index_span)
        .ok()?;
    let base = view.index_span.lo().0;
    inner.sort_by_key(|(_, span, _)| std::cmp::Reverse(span.lo().0));
    let mut last_lo = u32::MAX;
    for (_, span, replacement) in &inner {
        // Nested inner edits are one subject's business; two that overlap each
        // other are not composable here.
        if span.hi().0 > last_lo {
            return None;
        }
        last_lo = span.lo().0;
        let (lo, hi) = ((span.lo().0 - base) as usize, (span.hi().0 - base) as usize);
        text.replace_range(lo..hi, replacement);
    }
    let text = if view.index_wrap {
        format!("({text}) as usize")
    } else {
        text
    };
    Some((
        text,
        inner
            .into_iter()
            .map(|(entry, span, _)| (entry, span))
            .collect(),
    ))
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
        let (mutable, optional) = match decision {
            Decision::Slice { mutable, .. } => (*mutable, false),
            // **R465-5 (relay 038).** An OPTION-presented slice base carries
            // exactly the same computed views; the only difference is that the
            // required callee contract opens it first. Taking the base's own
            // decided form here is what lets the existing
            // `(Slice, Opt { slice: true })` glue arm supply that unwrap —
            // without it the carrier is built from the base's RAW form, which
            // is a `from_raw_parts` with a fabricated extent and no unwrap, and
            // the Option family then holds the whole class
            // `option-evidence-held` (lodepng `addChunk_IHDR::data`).
            Decision::Opt {
                mutable,
                slice: true,
                ..
            } => (*mutable, true),
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
        // An optional base is admitted ALL-OR-NOTHING and never degraded here:
        // it already owns a typed disposition of its own, so a view this arm
        // cannot render leaves the subject exactly as it was.
        if optional
            && !views.iter().all(|view| {
                let carriers = table
                    .seams
                    .edits
                    .iter()
                    .filter(|edit| {
                        edit.source_node == Some(node) && edit.span == view.argument_span
                    })
                    .collect::<Vec<_>>();
                let [edit] = carriers.as_slice() else { return false };
                edit.raw_outbound.is_none()
                    && edit.spec.raw_boundary.is_none()
                    && edit.spec.forward_slice.is_none()
                    && edit.spec.shared_address.is_none()
                    && edit.spec.void_region.is_none()
                    && matches!(edit.expected, Form::Slice { mutable: expected } if mutable || !expected)
                    && matches!(edit.spec.core, GlueCore::FromRefMut | GlueCore::FromRawParts)
            })
        {
            continue;
        }
        let enclosing_unsafe_fn = tcx
            .fn_sig(node.0)
            .skip_binder()
            .skip_binder()
            .safety
            .is_unsafe();
        let mut seams = Vec::new();
        let mut element_uses = Vec::new();
        let mut retired: Vec<(usize, Span)> = Vec::new();
        let mut hold = None;
        for view in views {
            // W6S-14: the index with the other subjects' edits inside it.
            let Some((index_text, subsumed)) = composed_index(tcx, table, view, node) else {
                hold = Some(view.use_span);
                break;
            };
            retired.extend(subsumed);
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
            let source = if optional {
                Decision::Opt {
                    mutable,
                    slice: true,
                    uses: Vec::new(),
                }
            } else {
                Decision::Slice {
                    mutable,
                    uses: Vec::new(),
                }
            };
            let forward = |view_mutable: bool| ForwardView {
                index_name: index_text.clone(),
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
                        replacement: format!("{amp}({name})[{index_text}]"),
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
                && matches!(
                    edit.spec.core,
                    GlueCore::FromRefMut | GlueCore::FromRawParts
                )
                && edit.spec.void_region.is_none()
            {
                // A borrowed element widened into a converted SLICE parameter,
                // or the bare arithmetic wrapped by `from_raw_parts` with a
                // guessed length (lodepng `lodepng_set32bitInt(chunk.offset(8 +
                // length), CRC)`, where the adjacency arm had licensed `CRC`
                // as the length): the suffix is already that slice, with the
                // base's own extent.
                if expected_mutable && !mutable {
                    hold = Some(view.use_span);
                    break;
                }
                let mut spec = GlueSpec::core(GlueCore::Bare, expected_mutable);
                if optional {
                    spec = spec.with_unwrap(mutable);
                }
                spec.forward_slice = Some(forward(expected_mutable));
                edit.spec = spec;
                edit.family = SeamFamily::Safe;
                edit.bridge.bridge_kind = "computed-suffix-view".to_owned();
            } else if edit.spec.raw_boundary.is_none()
                && let Form::Slice {
                    mutable: expected_mutable,
                } = edit.expected
                && let Some(region) = edit.spec.void_region.as_ref()
                && region.reads_width()
            {
                // wave-6b: a width reader over the computed view — the
                // reader's width as a checked prefix of the suffix.
                if expected_mutable && !mutable {
                    hold = Some(view.use_span);
                    break;
                }
                let mut spec = GlueSpec::core(GlueCore::Bare, expected_mutable);
                spec.forward_slice = Some(forward(expected_mutable));
                spec.void_region = Some(region.as_prefix_of_view());
                spec.len = edit.spec.len.clone();
                edit.spec = spec;
                edit.family = SeamFamily::Safe;
                edit.bridge.bridge_kind = "computed-suffix-view-width-read".to_owned();
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
            if optional {
                continue;
            }
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
        // W6S-14: an inner subject's edit the view now carries is retired from
        // that subject, so the two never overlap.
        for (inner, span) in retired {
            match &mut table.entries[inner].1 {
                Decision::Slice { uses, .. }
                | Decision::NestedSlice { uses, .. }
                | Decision::Opt { uses, .. } => uses.retain(|edit| edit.span != span),
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Box(_)
                | Decision::Cursor { .. }
                | Decision::Degraded(_) => {}
            }
        }
        match &mut table.entries[entry].1 {
            Decision::Slice { uses, .. } => uses.extend(element_uses),
            // Every admitted view of an optional base has its own carrier, so
            // the `[]` element arm cannot fire and there is nothing to extend.
            Decision::Opt { .. } if optional && element_uses.is_empty() => {}
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
