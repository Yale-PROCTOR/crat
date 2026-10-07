//! **R864-1 (b) (USER; fan-out 081) — two array decays of one object.**
//!
//! `X.as_mut_ptr()` / `X.as_ptr()` over an array `X` is X's element 0. A5's
//! classifier read two decays of ONE array as "proven disjoint" (libzahl
//! `zmul`'s `zadd(b_low.as_mut_ptr(), b_low.as_mut_ptr(), …)`): the origin of
//! each `&mut b_low` temporary is the temporary itself, complete, so two
//! borrows of one array carry disjoint singleton origin sets (the trace, for
//! era-5c, in wave-5d report 141). Until that evidence is fixed:
//! - (i) two decays of the same local or static array are never disjoint,
//!   whatever any proof says;
//! - (ii) the classifier's own proof (`a5-proven-disjoint`) is not taken where
//!   either side is an array decay, except between decays of two DISTINCT
//!   local or static arrays, which are distinct objects by the program's text.

use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::Res,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::TyCtxt;

use super::{
    a5_site_proof::{A5PeerProof, A5SiteProofVerdict},
    emitability::{CallSite, peel_casts},
};

/// The reason a decay pair carries.
pub(crate) const SAME_ARRAY: &str = "same-array-decay";
/// The reason a classifier proof over a decay carries.
pub(crate) const OVER_A_DECAY: &str = "a5-proof-over-an-array-decay";

/// The array an argument decays, when it is `X.as_mut_ptr()` / `X.as_ptr()`
/// (under casts, and under `&*` / `&mut *`) with `X` an array.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DecayRoot {
    /// A local holding the array by value.
    Local(HirId),
    /// A static holding the array by value.
    Static(DefId),
    /// Any other array place (through a pointer, a field, a reference local).
    Other,
}

pub(crate) fn decay_root(tcx: TyCtxt<'_>, owner: LocalDefId, expr: &Expr<'_>) -> Option<DecayRoot> {
    let mut expr = peel_casts(expr);
    if let ExprKind::AddrOf(_, _, inner) = expr.kind
        && let ExprKind::Unary(rustc_hir::UnOp::Deref, pointer) = inner.kind
    {
        expr = peel_casts(pointer);
    }
    let ExprKind::MethodCall(segment, receiver, _, _) = expr.kind else {
        return None;
    };
    if !matches!(segment.ident.name.as_str(), "as_ptr" | "as_mut_ptr") {
        return None;
    }
    let typeck = tcx.typeck(owner);
    let mut ty = typeck.expr_ty(receiver);
    let by_value = matches!(ty.kind(), rustc_middle::ty::TyKind::Array(..));
    while let rustc_middle::ty::TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    if !matches!(ty.kind(), rustc_middle::ty::TyKind::Array(..)) {
        return None;
    }
    let root = match receiver.kind {
        ExprKind::Path(QPath::Resolved(None, path)) if by_value => match path.res {
            Res::Local(binding) => DecayRoot::Local(binding),
            Res::Def(rustc_hir::def::DefKind::Static { .. }, def_id) => DecayRoot::Static(def_id),
            _ => DecayRoot::Other,
        },
        _ => DecayRoot::Other,
    };
    Some(root)
}

/// The proof at `site` for `left` / `right`, read with both rules.
pub(crate) fn read_array_decays(
    site: &CallSite,
    left: usize,
    right: usize,
    proof: &mut A5PeerProof,
) {
    let root = |index: usize| {
        site.args
            .iter()
            .find(|argument| argument.index == index)
            .and_then(|argument| argument.array_decay)
    };
    let (l, r) = (root(left), root(right));
    let distinct_objects = |a: DecayRoot, b: DecayRoot| match (a, b) {
        (DecayRoot::Other, _) | (_, DecayRoot::Other) => false,
        (a, b) => a != b,
    };
    match (l, r) {
        // (i) one array's element 0, twice.
        (Some(a), Some(b)) if a == b && a != DecayRoot::Other => {
            proof.verdict = A5SiteProofVerdict::Overlapping;
            proof.reason = SAME_ARRAY;
            proof.family = "same-object-identity";
        }
        // (ii) the classifier's proof over a decay.
        _ if (l.is_some() || r.is_some())
            && proof.verdict == A5SiteProofVerdict::Clear
            && proof.reason == "a5-proven-disjoint"
            && !matches!((l, r), (Some(a), Some(b)) if distinct_objects(a, b)) =>
        {
            proof.verdict = A5SiteProofVerdict::Overlapping;
            proof.reason = OVER_A_DECAY;
            proof.family = "not-shown-disjoint";
        }
        _ => {}
    }
}
