//! **R815-6 / R819-1 item 2 — the scope's separate-object certificate (R816-1)
//! at the pair proof.**
//!
//! In the closed program, each pointer argument of an exported entry that no
//! function of the program calls designates a separate object. So two distinct
//! formals of such an entry, handed on bare (or as places inside them) and
//! never assigned nor addressed, are disjoint. The receipt names the instance:
//! - `pair-disjoint:premise-outside-byte-view`: a byte or `void` formal beside a
//!   typed one (P8 `OutsideByteViewDiscipline`, R814-2);
//! - `exported-entry:same-pointee-mut-pair`: one pointee, both mutable (W4,
//!   R462);
//! - `pair-disjoint:scope-closed-program`: the rest (two byte formals, a shared
//!   and a mutable formal of one pointee, pointees the type route cannot
//!   separate).
//!
//! Not covered: an entry the program calls or names, an unexported function,
//! an argument that is not the entry's own formal (nor a place inside its own
//! referent), a formal the body assigns or takes the address of, an entry
//! with a closure or an extern declaration of its own symbol. A client outside
//! the program that passes one object to two formals of an entry is outside
//! the scope (R836-1: R767's exception is withdrawn).
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
/// R898-1 (the seat, on R816 / R819): an UNEXPORTED function that nothing in
/// the program calls or names (no call site, no address taken, no fn-pointer
/// web) never runs inside the closed program, so its formals are disjoint by
/// vacuity. A receipted scope fact, not a waiver.
pub(crate) const SCOPE_UNCALLED_UNEXPORTED: &str = "pair-disjoint:scope=uncalled-unexported";

/// One formal of an outside-only entry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EntryFormal {
    pub position: usize,
    pub byte: bool,
    pub mutable: bool,
    pub pointee: String,
}

/// An outside-only entry's formals by binding.
#[derive(Clone, Debug, Default)]
pub(crate) struct EntryFormals {
    pub by_binding: FxHashMap<HirId, EntryFormal>,
    /// R898-1: not exported (`#[no_mangle]` / `export_name`), so the scope
    /// covers it by vacuity rather than as an entry (R819).
    pub unexported: bool,
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
            // A place inside the formal's own referent only: reached through a
            // dereference of the formal itself, never of a pointer loaded from
            // it (`&mut (*(*l).head).next` lies in another object). F2's
            // `inside_of` stops at exactly that dereference.
            ArgShape::AddrOf {
                base: Some(base),
                through_deref: true,
                ..
            } if argument.inside_of.first() == Some(&base) => base,
            _ => return None,
        };
        entry.by_binding.get(&root)
    };
    let (left, right) = (formal(left)?, formal(right)?);
    // The roots must be two different formals: one formal handed twice, or
    // two places inside one formal, is one outside object (wave-6o 123).
    if left.position == right.position {
        return None;
    }
    if entry.unexported {
        return Some(SCOPE_UNCALLED_UNEXPORTED);
    }
    Some(instance(left, right))
}

/// The exported entries nothing in the program calls or names, each with its
/// raw-pointer formals the body never assigns nor addresses — and (R898-1) the
/// unexported functions nothing calls or names, whose formals are disjoint by
/// vacuity. `facts` must already hold every call and reference in the crate.
pub(crate) fn entry_formals(
    tcx: TyCtxt<'_>,
    facts: &EmitabilityFacts,
) -> FxHashMap<LocalDefId, EntryFormals> {
    let mut out = FxHashMap::default();
    for owner in tcx.hir_body_owners() {
        if tcx.def_kind(owner) != rustc_hir::def::DefKind::Fn
            || tcx
                .entry_fn(())
                .is_some_and(|(entry, _)| entry == owner.to_def_id())
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
        // A closure can assign a formal out of the visitor's sight, and an
        // extern declaration of the entry's own symbol is a call from inside.
        if has_closure(body) || declared_extern(tcx, owner) {
            continue;
        }
        let mut formals = EntryFormals::default();
        for (position, param) in body.params.iter().enumerate() {
            let PatKind::Binding(_, binding, _, None) = param.pat.kind else {
                continue;
            };
            let Some(TyKind::RawPtr(pointee, mutability)) =
                inputs.get(position).map(|ty| ty.kind())
            else {
                continue;
            };
            if assigned_or_addressed(body, binding) {
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
        formals.unexported = !super::exported_pair::exported(tcx, owner);
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
fn has_closure(body: &rustc_hir::Body<'_>) -> bool {
    struct Closures(bool);
    impl<'v> Visitor<'v> for Closures {
        fn visit_expr(&mut self, expr: &'v rustc_hir::Expr<'v>) {
            if matches!(expr.kind, rustc_hir::ExprKind::Closure(..)) {
                self.0 = true;
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut visitor = Closures(false);
    visitor.visit_body(body);
    visitor.0
}

/// Does the crate declare a foreign function with the entry's own symbol?
/// wave-5d 149h (the round-2 review's MED): symbols, not item names: a local
/// `#[export_name = "type"] fn type_0` and a foreign `#[link_name = "f"] fn
/// f_ext` are the same symbol as `type` / `f`.
pub(crate) fn declared_extern(tcx: TyCtxt<'_>, entry: LocalDefId) -> bool {
    let symbol = |did: rustc_hir::def_id::DefId, renamed: Option<rustc_span::Symbol>| {
        renamed.unwrap_or_else(|| tcx.item_name(did))
    };
    let entry = entry.to_def_id();
    let name = symbol(entry, tcx.codegen_fn_attrs(entry).export_name);
    tcx.hir_crate_items(()).foreign_items().any(|item| {
        let did = item.owner_id.to_def_id();
        symbol(did, tcx.codegen_fn_attrs(did).link_name) == name
    })
}

fn assigned_or_addressed(body: &rustc_hir::Body<'_>, binding: HirId) -> bool {
    struct Assign {
        binding: HirId,
        found: bool,
    }
    impl<'v> Visitor<'v> for Assign {
        fn visit_expr(&mut self, expr: &'v rustc_hir::Expr<'v>) {
            // An assignment to the binding, or its address taken (a write
            // through that address can reassign it: wave-6o 123 note 1).
            if let rustc_hir::ExprKind::Assign(lhs, ..)
            | rustc_hir::ExprKind::AssignOp(_, lhs, _)
            | rustc_hir::ExprKind::AddrOf(_, _, lhs) = expr.kind
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
