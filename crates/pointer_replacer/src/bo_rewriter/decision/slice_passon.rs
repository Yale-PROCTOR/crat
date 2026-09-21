//! wave-6s2 — forward slice shapes at return and call positions that the
//! collectors did not spell out.
//!
//! **W6S2-2 — the C2Rust constant-reslice return.** The return family already
//! delivers `return p.offset(8)` on a delivered slice parameter as the tied
//! reslice `&p[8..]` (`ReturnExprShape::ConstantReslice`). C2Rust never
//! writes that; it writes the borrow-deref-cast spine
//! `&mut *p.offset(8 as libc::c_int as isize) as *mut T` (or `&*… as *const
//! T`), which the shape recogniser read as `Other` and the slice-use walk then
//! refused as a cursor use. The spine is the same value — the address `p + 8`
//! re-materialised as a raw pointer — so it is recognised as the same
//! `ConstantReslice` (same receiver, same literal offset) under three checks:
//! the receiver is a raw-pointer local, the literal under its `as` casts is a
//! non-negative integer, and the outer cast keeps the receiver's pointee (the
//! borrow's mutability is the cast's). Everything downstream — the return
//! permit, the tied lifetime, the wrapper — is the existing family's.

use rustc_hir::{Expr, ExprKind, HirId, QPath, def::Res};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::emitability::ReturnExprShape;

/// The C2Rust spine of a constant reslice: the receiver expression, its
/// binding, and the literal offset.
struct ResliceSpine {
    receiver_hir: HirId,
    receiver_span: rustc_span::Span,
    binding: HirId,
    offset: u64,
}

fn spine<'tcx>(tcx: TyCtxt<'tcx>, expression: &Expr<'tcx>) -> Option<ResliceSpine> {
    let typeck = tcx.typeck(expression.hir_id.owner.def_id);
    let TyKind::RawPtr(returned_pointee, _) = typeck.expr_ty(expression).kind() else {
        return None;
    };
    // `… as *mut T` — one or more casts, each keeping the pointee.
    let mut inner = expression;
    let mut saw_cast = false;
    while let ExprKind::Cast(operand, _) = inner.kind {
        saw_cast = true;
        inner = operand;
    }
    if !saw_cast {
        return None;
    }
    // `&mut *e` / `&*e`
    let ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, _, borrowed) = inner.kind else {
        return None;
    };
    let ExprKind::Unary(rustc_hir::UnOp::Deref, place) = borrowed.kind else {
        return None;
    };
    // `p.offset(<literal under casts>)`
    let ExprKind::MethodCall(_, receiver, [argument], _) = place.kind else {
        return None;
    };
    let method = typeck.type_dependent_def_id(place.hir_id)?;
    if tcx.crate_name(method.krate).as_str() != "core" || tcx.item_name(method).as_str() != "offset"
    {
        return None;
    }
    let ExprKind::Path(QPath::Resolved(_, path)) = receiver.kind else {
        return None;
    };
    let Res::Local(binding) = path.res else { return None };
    let TyKind::RawPtr(receiver_pointee, _) = typeck.expr_ty(receiver).kind() else {
        return None;
    };
    if receiver_pointee != returned_pointee {
        return None;
    }
    let mut literal = argument;
    while let ExprKind::Cast(operand, _) = literal.kind {
        literal = operand;
    }
    let ExprKind::Lit(literal) = literal.kind else { return None };
    let rustc_ast::LitKind::Int(offset, _) = literal.node else {
        return None;
    };
    let offset = u64::try_from(offset.get()).ok()?;
    Some(ResliceSpine {
        receiver_hir: receiver.hir_id,
        receiver_span: receiver.span,
        binding,
        offset,
    })
}

/// The return-shape hook: the C2Rust spine as the family's `ConstantReslice`.
pub(crate) fn c2rust_constant_reslice_return<'tcx>(
    tcx: TyCtxt<'tcx>,
    expression: &Expr<'tcx>,
) -> Option<ReturnExprShape> {
    let spine = spine(tcx, expression)?;
    Some(ReturnExprShape::ConstantReslice {
        receiver_hir: spine.receiver_hir,
        receiver_span: spine.receiver_span,
        offset: spine.offset,
    })
}

/// The return-site root hook: the reslice's binding, which the
/// borrow-then-cast argument shape does not carry.
pub(crate) fn c2rust_constant_reslice_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    expression: &Expr<'tcx>,
) -> Option<HirId> {
    spine(tcx, expression).map(|spine| spine.binding)
}

// ---------------------------------------------------------------------------
// W6S2-5 — the DESTINATION side of a computed view copied by ASSIGNMENT.
//
// wave-6s's spine recognises `dst = &*src.offset(e) as *const T` and renders
// the SOURCE's edit (the checked suffix, or its `as_ptr()` when the
// destination stays raw). The DESTINATION's own uses, however, still see the
// assignment as an unsupported use — `classify` admits an assignment to the
// subject only when the right-hand side is that same binding's own arithmetic
// (the self-advance target) — so a destination that could carry the view is
// held `slice-use-unsupported` (brotli static_dict `s`, `s_0`, `s_1`, `s_2`,
// lodepng `addChunk_IHDR::data`: the ENABLED rows of the batch-9 frame).
//
// This is the same position as the self-advance target and takes the same
// answer: the use is IN SCOPE and needs NO edit of its own — the right-hand
// side is owned by the source's receipt plan (or, for a null-initialised
// destination, by the Option value planner). Conservative by construction: a
// forward delta only, the pointee preserved, and the source must be a
// DIFFERENT local (a self-advance stays the classifier's).
// ---------------------------------------------------------------------------

/// Is this use the target of `dst = <forward computed view of another local>`?
pub(crate) fn assignment_from_computed_view(
    tcx: TyCtxt<'_>,
    use_expr: &Expr<'_>,
    key: (LocalDefId, HirId),
) -> bool {
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
    let TyKind::RawPtr(destination_pointee, _) = typeck.expr_ty(lhs).kind() else {
        return false;
    };
    // Peel the identity casts and the borrow-deref the C2Rust spine writes.
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
    // `src.offset(e)` / `src.add(e)` on a DIFFERENT local of the same pointee.
    let ExprKind::MethodCall(segment, receiver, [delta], _) = value.kind else {
        return false;
    };
    if !matches!(segment.ident.name.as_str(), "offset" | "add") {
        return false;
    }
    let Some(method) = typeck.type_dependent_def_id(value.hir_id) else {
        return false;
    };
    if tcx.crate_name(method.krate).as_str() != "core" {
        return false;
    }
    let ExprKind::Path(QPath::Resolved(_, path)) = receiver.kind else {
        return false;
    };
    let Res::Local(source) = path.res else {
        return false;
    };
    if source == key.1 {
        return false; // a self-advance is the classifier's own arm
    }
    let TyKind::RawPtr(source_pointee, _) = typeck.expr_ty(receiver).kind() else {
        return false;
    };
    if source_pointee != destination_pointee {
        return false;
    }
    forward_delta(tcx, delta)
}

/// A delta that cannot move the pointer backwards: a non-negative integer
/// literal under its `as` casts, or an unsigned-typed expression.
fn forward_delta(tcx: TyCtxt<'_>, delta: &Expr<'_>) -> bool {
    let typeck = tcx.typeck(delta.hir_id.owner.def_id);
    let mut inner = delta;
    loop {
        match inner.kind {
            ExprKind::Cast(operand, _) => {
                if typeck.expr_ty(operand).is_signed() && !literal_non_negative(operand) {
                    return unsigned_chain(tcx, operand);
                }
                inner = operand;
            }
            _ => break,
        }
    }
    literal_non_negative(inner) || !typeck.expr_ty(inner).is_signed()
}

fn unsigned_chain(tcx: TyCtxt<'_>, expr: &Expr<'_>) -> bool {
    let typeck = tcx.typeck(expr.hir_id.owner.def_id);
    !typeck.expr_ty(expr).is_signed() || literal_non_negative(expr)
}

fn literal_non_negative(expr: &Expr<'_>) -> bool {
    matches!(expr.kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(..)))
}
