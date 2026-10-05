//! **R815-6 — premise P8 `OutsideByteViewDiscipline` (R814-2) at the pair proof.**
//!
//! P8: an outside caller does not hand the program a byte (or `void`) view of
//! an object that it also hands the program typed. So at a call where both
//! arguments are formals of an exported entry that nothing in the program
//! calls, handed on bare (or as places inside them), one of byte or `void`
//! pointee and the other of a non-character pointee, the two point into
//! different outside objects: the pair is disjoint under P8, receipted
//! `pair-disjoint:premise-outside-byte-view` on the pair row.
//!
//! Not covered: two byte formals, two typed formals (W4's same-pointee arm and
//! the type route stay as they are), and an argument that is not the entry's
//! own formal (a local, even one copied from a formal, is not read through).
//!
//! It is read where the seam's site gate looks the pair's A5 proof up: that
//! proof's raw-view fallback is what makes the typed formal a raw view
//! (binn's `binn_object_blob` → `binn_object_get::psize`).

use rustc_hash::FxHashMap;
use rustc_hir::{
    HirId, PatKind,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::emitability::{ArgShape, CallSite, EmitabilityFacts};

/// The receipt on a pair row this premise certifies.
pub(crate) const RECEIPT: &str = "pair-disjoint:premise-outside-byte-view";

/// The pair proof at `site` for `left` / `right`, read under P8: a pair P8
/// certifies is clear, with the premise as its reason.
pub(crate) fn read_under_p8(
    facts: &EmitabilityFacts,
    site: &CallSite,
    left: usize,
    right: usize,
    proof: &mut super::a5_site_proof::A5PeerProof,
) {
    if proof.verdict != super::a5_site_proof::A5SiteProofVerdict::Clear
        && certifies(facts, site, left, right)
    {
        proof.verdict = super::a5_site_proof::A5SiteProofVerdict::Clear;
        proof.reason = RECEIPT;
        proof.family = "premise-outside-byte-view";
    }
}

/// Does P8 certify the pair of argument positions `left` / `right` at `site`?
pub(crate) fn certifies(
    facts: &EmitabilityFacts,
    site: &CallSite,
    left: usize,
    right: usize,
) -> bool {
    let Some(formals) = facts.outside_entry_formals.get(&site.caller) else {
        return false;
    };
    let formal = |index: usize| {
        let argument = site.args.iter().find(|argument| argument.index == index)?;
        let root = match argument.shape {
            ArgShape::BareLocal(root) => root,
            ArgShape::AddrOf {
                base: Some(base),
                through_deref: true,
                ..
            } => base,
            _ => return None,
        };
        formals.get(&root).copied()
    };
    // Two formals of different classes are two different formals.
    matches!((formal(left), formal(right)), (Some(left), Some(right)) if left != right)
}

/// The exported entries nothing in the program calls or names, each with its
/// raw-pointer formals the body never assigns: binding -> byte pointee.
/// `facts` must already hold every call and reference in the crate.
pub(crate) fn entry_formals(
    tcx: TyCtxt<'_>,
    facts: &EmitabilityFacts,
) -> FxHashMap<LocalDefId, FxHashMap<HirId, bool>> {
    let mut out = FxHashMap::default();
    for owner in tcx.hir_body_owners() {
        if tcx.def_kind(owner) != rustc_hir::def::DefKind::Fn
            || !super::exported_pair::exported(tcx, owner)
            || facts
                .call_args
                .get(&owner)
                .is_some_and(|sites| !sites.is_empty())
            || facts.referenced.contains_key(&owner)
        {
            continue;
        }
        let body = tcx.hir_body_owned_by(owner);
        let inputs = tcx
            .fn_sig(owner.to_def_id())
            .instantiate_identity()
            .skip_binder()
            .inputs();
        let mut formals = FxHashMap::default();
        for (position, param) in body.params.iter().enumerate() {
            let PatKind::Binding(_, binding, _, None) = param.pat.kind else {
                continue;
            };
            let Some(TyKind::RawPtr(pointee, _)) = inputs.get(position).map(|ty| ty.kind()) else {
                continue;
            };
            if assigned(body, binding) {
                continue;
            }
            formals.insert(binding, is_byte(tcx, *pointee));
        }
        if !formals.is_empty() {
            out.insert(owner, formals);
        }
    }
    out
}

/// A byte or `void` pointee: `u8`, `i8` (`c_char`, `c_uchar`) or `c_void`.
fn is_byte<'tcx>(tcx: TyCtxt<'tcx>, pointee: Ty<'tcx>) -> bool {
    matches!(
        pointee.kind(),
        TyKind::Int(rustc_middle::ty::IntTy::I8) | TyKind::Uint(rustc_middle::ty::UintTy::U8)
    ) || pointee.is_c_void(tcx)
}
fn assigned(body: &rustc_hir::Body<'_>, binding: HirId) -> bool {
    struct Assign {
        binding: HirId,
        found: bool,
    }
    impl<'v> Visitor<'v> for Assign {
        fn visit_expr(&mut self, expr: &'v rustc_hir::Expr<'v>) {
            if let rustc_hir::ExprKind::Assign(lhs, ..) | rustc_hir::ExprKind::AssignOp(_, lhs, _) =
                expr.kind
                && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(None, path)) = lhs.kind
                && let rustc_hir::def::Res::Local(local) = path.res
                && local == self.binding
            {
                self.found = true;
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut visitor = Assign {
        binding,
        found: false,
    };
    visitor.visit_body(body);
    visitor.found
}
