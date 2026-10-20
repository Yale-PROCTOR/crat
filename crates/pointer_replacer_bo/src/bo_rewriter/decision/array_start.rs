//! W-C6: c2rust's `&a[0]` — `&mut *A.as_mut_ptr().offset(0)` / `&*A.as_ptr()
//! .offset(0)` on a declared array `A: [T; N]` — is the array's start, spelled
//! through a one-element reference. Classified as the reference it looks like,
//! a slice parameter received `slice::from_ref(&mut *…)`: ONE element, and the
//! callee's `len().checked_sub(count)` then fails at runtime. Classified as the
//! raw expression it is, with `A.as_mut_ptr()` as the adapter operand, the seam's
//! C arm renders `from_raw_parts(A.as_mut_ptr(), LEN)` exactly as it does for a
//! spelled `A.as_mut_ptr()` — the same address, no intermediate one-element
//! reference (wave-6k's retag class avoided, not introduced).
use rustc_hir::{Expr, ExprKind, HirId};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::raw_boundary::RawMutability;

pub(crate) struct ArrayStart {
    /// `A.as_ptr()` / `A.as_mut_ptr()` — the adapter operand.
    pub operand: Span,
    pub mutability: RawMutability,
    /// The array place's root binding, when it has one.
    pub root: Option<HirId>,
    /// Whether borrowck can see the array place: it cannot when the place is
    /// reached through a dereference of a pointer that is not itself this
    /// idiom over a place it sees (`(*s).data_` with `s` raw); it can when
    /// every dereference on the way is the idiom over such a place
    /// (`(*combined_histo.as_mut_ptr().offset(j)).data_`, `combined_histo` a
    /// local array).
    pub blind: bool,
}

fn blind(place: &Expr<'_>) -> bool {
    let mut cur = peel(place);
    loop {
        match cur.kind {
            ExprKind::Field(base, _) | ExprKind::Index(base, _, _) | ExprKind::DropTemps(base) => {
                cur = peel(base);
            }
            ExprKind::Unary(rustc_hir::UnOp::Deref, base) => match peel(base).kind {
                ExprKind::MethodCall(offset, start, [_], _)
                    if offset.ident.name.as_str() == "offset" =>
                {
                    match peel(start).kind {
                        ExprKind::MethodCall(ctor, array, [], _)
                            if matches!(ctor.ident.name.as_str(), "as_ptr" | "as_mut_ptr") =>
                        {
                            cur = peel(array);
                        }
                        _ => return true,
                    }
                }
                _ => return true,
            },
            ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                return !matches!(path.res, rustc_hir::def::Res::Local(_));
            }
            _ => return true,
        }
    }
}

fn peel<'a>(mut e: &'a Expr<'a>) -> &'a Expr<'a> {
    while let ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    e
}

fn zero(e: &Expr<'_>) -> bool {
    match peel(e).kind {
        ExprKind::Lit(lit) => matches!(lit.node, rustc_ast::LitKind::Int(n, _) if n.get() == 0),
        ExprKind::Cast(inner, _) => zero(inner),
        _ => false,
    }
}

pub(crate) fn idiom(tcx: TyCtxt<'_>, expr: &Expr<'_>) -> Option<ArrayStart> {
    let ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, _, inner) = peel(expr).kind else {
        return None;
    };
    let ExprKind::Unary(rustc_hir::UnOp::Deref, place) = peel(inner).kind else {
        return None;
    };
    let ExprKind::MethodCall(offset, start, [by], _) = peel(place).kind else {
        return None;
    };
    if offset.ident.name.as_str() != "offset" || !zero(by) {
        return None;
    }
    let start = peel(start);
    let ExprKind::MethodCall(ctor, array, [], _) = start.kind else {
        return None;
    };
    let typeck = tcx.typeck(expr.hir_id.owner.def_id);
    let did = typeck.type_dependent_def_id(start.hir_id)?;
    if tcx.crate_name(did.krate).as_str() != "core" {
        return None;
    }
    let mutability = match tcx.item_name(did).as_str() {
        "as_ptr" => RawMutability::Const,
        "as_mut_ptr" => RawMutability::Mut,
        _ => return None,
    };
    let _ = ctor;
    let mut ty = typeck.expr_ty(array);
    while let TyKind::Ref(_, pointee, _) = ty.kind() {
        ty = *pointee;
    }
    if !matches!(ty.kind(), TyKind::Array(..)) {
        return None;
    }
    Some(ArrayStart {
        operand: start.span,
        mutability,
        root: super::emitability::place_root(array).0,
        blind: blind(array),
    })
}

/// The subtree the seam's adapter is built from: the array-start operand for
/// the idiom (the raw expression's own span otherwise).
pub(crate) fn text_span(arg: &super::emitability::Arg, span: Span) -> Span {
    if matches!(arg.shape, super::emitability::ArgShape::RawExpr { .. }) {
        arg.adapter_operand_span
    } else {
        span
    }
}
