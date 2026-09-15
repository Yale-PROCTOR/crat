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
