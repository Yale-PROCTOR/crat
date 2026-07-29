//! **Subject-universe classification — the ITEM axis reference.**
//!
//! # Why this exists, and why round three's version did not work
//!
//! The coverage gate's first three forms all compared the decision table
//! against something derived the same way the collector derives it:
//!
//! | round | the "independent" side | why it agreed by construction |
//! |---|---|---|
//! | S2a | `subjects.len()` | same `Vec`, one line earlier |
//! | S2a-R | a second walk of `program.functions` | same root, same filter |
//! | S2a-R2 | this file, iterating `tcx.hir_crate(()).owners` | character-identical to `collect_program` |
//!
//! Round three's module doc claimed the walk "starts from
//! `tcx.hir_crate_items(())`". It did not — that API was called nowhere in the
//! crate. **This version actually calls it**, which is the whole point:
//! `hir_crate_items` is a query whose result is built by a collector walking the
//! crate's *module tree*, while `collect_program` reads the flat owner array
//! produced by lowering. Different inputs, different lowering, different failure
//! modes — the standard §2 requires of a reference.
//!
//! # What this instrument is and is not
//!
//! It is the **item-axis** reference: *which functions exist?* It is deliberately
//! not the type-axis reference — see [`super::coverage`], where E-R1's
//! MIR-derived depth-0 parameter slots play that role.
//!
//! Neither reference alone suffices. E-R1 shares `program.functions` with the
//! collector and so is jointly blind on the item axis; this walk shares the
//! `ptr_chain_depth` predicate and so is jointly blind on the type axis. Two
//! axes, two instruments, stated because the previous three rounds each shipped
//! one and called the gate closed.
//!
//! # M1's subject universe (ruling, 2026-07-29)
//!
//! M1's subjects are **free functions with bodies** — the C2Rust output shape.
//! Everything else is out of scope *by ruling*, not by oversight:
//!
//! - **foreign items**: no body, ABI-fixed signature (M4 territory);
//! - **impl / trait items**: not a C-source shape.
//!
//! The exclusions are **attributed quantities**: they ride out on
//! [`super::super::RewriteOutcome`], so a population M1 declines to handle is
//! visible as a number rather than as an absence. There is deliberately no
//! `excluded_other` bucket — the previous one could not be incremented by any
//! `OwnerNode`, so asserting it was zero passed vacuously, which is the same
//! unfailable-check class this whole round exists to remove. Blind-spot
//! detection is done by [`super::coverage`]'s set comparison instead, which
//! *can* fail.

use rustc_hash::FxHashSet;
use rustc_hir::{def::DefKind, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

use crate::analyses::borrow_ownership::crate_slots::ptr_chain_depth;

/// Pointer-parameter counts on the item kinds M1 does not rewrite.
///
/// Copied out to [`super::super::RewriteOutcome`] so the numbers reach a
/// consumer by construction. A bucket that reaches no consumer does not exist.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Excluded {
    /// Pointer params on inherent/trait impl methods — out of scope by ruling.
    pub impl_items: usize,
    /// Pointer params on trait item declarations — out of scope by ruling.
    pub trait_items: usize,
    /// Pointer params on `extern` declarations — no body, ABI-fixed.
    pub foreign_items: usize,
}

/// The item-axis census.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct UniverseReport {
    /// Every free function in the crate, as seen through `hir_crate_items`.
    ///
    /// This is the load-bearing field: [`super::coverage`] compares it against
    /// `program.functions` as a SET. A filter placed anywhere upstream of
    /// `program.functions` shows up here as a difference — which is precisely
    /// what the impl-method case proved the old gate could not see.
    pub free_fns: FxHashSet<LocalDefId>,
    /// Pointer params on those free functions.
    pub subjects: usize,
    pub excluded: Excluded,
}

/// Pointer parameters of `did`, counted on the **resolved** signature.
///
/// Resolved rather than syntactic on purpose: a C2Rust alias
/// (`pub type lil_value_t = *mut _lil_value_t`) lowers to `TyKind::Path`, so a
/// syntactic count would report an aliased parameter as absent — the exact
/// blind spot that made the `4171/0/0/2039` census unable to detect its own
/// error.
fn ptr_params(tcx: TyCtxt<'_>, did: LocalDefId) -> usize {
    tcx.fn_sig(did)
        .skip_binder()
        .skip_binder()
        .inputs()
        .iter()
        .filter(|ty| ptr_chain_depth(**ty) > 0)
        .count()
}

/// Classify every item in the crate, by scope class.
///
/// Deliberately does NOT consult `collect_program` or `collect_subjects`: the
/// whole value of this walk is that it can disagree with them.
pub(crate) fn classify(tcx: TyCtxt<'_>) -> UniverseReport {
    let items = tcx.hir_crate_items(());
    let mut report = UniverseReport::default();

    for id in items.free_items() {
        let did = id.owner_id.def_id;
        if tcx.def_kind(did) != DefKind::Fn {
            continue;
        }
        // Inserted unconditionally, not only when it bears a pointer param:
        // the set comparison in `coverage` is over FUNCTIONS, and filtering
        // here would let a collector-invented function hide behind "it had no
        // pointer parameters anyway".
        report.free_fns.insert(did);
        report.subjects += ptr_params(tcx, did);
    }
    for id in items.impl_items() {
        let did = id.owner_id.def_id;
        if tcx.def_kind(did) == DefKind::AssocFn {
            report.excluded.impl_items += ptr_params(tcx, did);
        }
    }
    for id in items.trait_items() {
        let did = id.owner_id.def_id;
        if tcx.def_kind(did) == DefKind::AssocFn {
            report.excluded.trait_items += ptr_params(tcx, did);
        }
    }
    for id in items.foreign_items() {
        let did = id.owner_id.def_id;
        if tcx.def_kind(did) == DefKind::Fn {
            report.excluded.foreign_items += ptr_params(tcx, did);
        }
    }

    report
}
