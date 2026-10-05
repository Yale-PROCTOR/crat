//! **R815-6 / R819-1 item 2 — the scope's separate-object certificate (R816-1)
//! at the pair proof.**
//!
//! In the closed program, each pointer argument of an exported entry that no
//! function of the program calls designates a separate object. So two distinct
//! formals of such an entry, handed on bare (or as places inside them) and
//! never assigned, are disjoint. The receipt names the instance:
//! - `pair-disjoint:premise-outside-byte-view`: a byte or `void` formal beside a
//!   typed one (P8 `OutsideByteViewDiscipline`, R814-2);
//! - `exported-entry:same-pointee-mut-pair`: one pointee, both mutable (W4,
//!   R462);
//! - `pair-disjoint:scope-closed-program`: the rest (two byte formals, a shared
//!   and a mutable formal of one pointee, pointees the type route cannot
//!   separate).
//!
//! Not covered: an entry the program calls or names, an unexported function,
//! an argument that is not the entry's own formal, a formal the body assigns,
//! and (R767) a formal pair the program's provided test passes one object to.
//!
//! It is read where the seam's site gate looks the pair's A5 proof up: that
//! proof's raw-view fallback is what makes a formal a raw view (binn's
//! `binn_object_blob` → `binn_object_get::psize`).

use rustc_hash::FxHashMap;
use rustc_hir::{
    HirId, PatKind,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::emitability::{ArgShape, CallSite, EmitabilityFacts};

/// The receipt of the byte-beside-typed instance (P8).
pub(crate) const RECEIPT: &str = "pair-disjoint:premise-outside-byte-view";
/// The receipt of W4's instance: one pointee, both mutable.
pub(crate) const SAME_POINTEE_MUT: &str = "exported-entry:same-pointee-mut-pair";
/// The receipt of the scope's remaining instances.
pub(crate) const SCOPE_CLOSED_PROGRAM: &str = "pair-disjoint:scope-closed-program";

/// One formal of an outside-only entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EntryFormal {
    pub position: usize,
    pub byte: bool,
    pub mutable: bool,
    pub pointee: String,
}

/// An outside-only entry's formals by binding, and the position pairs its
/// provided test aliases (R767).
#[derive(Clone, Debug, Default)]
pub(crate) struct EntryFormals {
    pub by_binding: FxHashMap<HirId, EntryFormal>,
    pub test_aliased: Vec<(usize, usize)>,
}

/// The receipt of the instance a certified pair is.
pub(crate) fn instance(left: &EntryFormal, right: &EntryFormal) -> &'static str {
    if left.byte != right.byte {
        RECEIPT
    } else if left.pointee == right.pointee && left.mutable && right.mutable {
        SAME_POINTEE_MUT
    } else {
        SCOPE_CLOSED_PROGRAM
    }
}

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
        && let Some(receipt) = certifies(facts, site, left, right)
    {
        proof.verdict = super::a5_site_proof::A5SiteProofVerdict::Clear;
        proof.reason = receipt;
        proof.family = "scope-separate-objects";
    }
}

/// The receipt of the instance when the scope certifies the pair of argument
/// positions `left` / `right` at `site`, else `None`.
pub(crate) fn certifies(
    facts: &EmitabilityFacts,
    site: &CallSite,
    left: usize,
    right: usize,
) -> Option<&'static str> {
    let entry = facts.outside_entry_formals.get(&site.caller)?;
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
        entry.by_binding.get(&root)
    };
    let (left, right) = (formal(left)?, formal(right)?);
    let pair = (
        left.position.min(right.position),
        left.position.max(right.position),
    );
    if left.position == right.position
        || entry
            .test_aliased
            .iter()
            .any(|&(a, b)| (a.min(b), a.max(b)) == pair)
    {
        return None;
    }
    Some(instance(left, right))
}

/// The exported entries nothing in the program calls or names, each with its
/// raw-pointer formals the body never assigns, and the pairs its test aliases.
/// `facts` must already hold every call and reference in the crate.
pub(crate) fn entry_formals(
    tcx: TyCtxt<'_>,
    facts: &EmitabilityFacts,
) -> FxHashMap<LocalDefId, EntryFormals> {
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
        let mut formals = EntryFormals {
            test_aliased: super::aliased_by_test::aliased_pairs(tcx, owner),
            ..Default::default()
        };
        for (position, param) in body.params.iter().enumerate() {
            let PatKind::Binding(_, binding, _, None) = param.pat.kind else {
                continue;
            };
            let Some(TyKind::RawPtr(pointee, mutability)) =
                inputs.get(position).map(|ty| ty.kind())
            else {
                continue;
            };
            if assigned(body, binding) {
                continue;
            }
            formals.by_binding.insert(
                binding,
                EntryFormal {
                    position,
                    byte: is_byte(tcx, *pointee),
                    mutable: mutability.is_mut(),
                    pointee: pointee.to_string(),
                },
            );
        }
        if !formals.by_binding.is_empty() {
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
