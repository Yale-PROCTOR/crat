//! The BO-owned borrow theory engine ("fork the theory, keep the judge").
//!
//! A scoped fork of production `borrow`'s per-function
//! constraint-graph → fact-pipeline → conflict-edge extraction, self-contained under
//! `borrow_ownership/` so write-aware invalidation and signature origins can
//! extend it WITHOUT touching the byte-frozen production `borrow/`. The final validator remains
//! the UNFORKED production `borrow::borrow_conflicts[_replaying]` path, independent of this fork.
//!
//! **Thin fork.** Production `borrow::borrow_inference` (pub) already exposes every
//! pre-invalidation fact as a pub field, so this engine REUSES it and forks only the loan
//! set + invalidation walk. The fact types (`Invalidates`/`Errors`/`LoanLiveness`) are
//! `SparseBitMatrix<PointIndex, Loan>` aliases — reused by value, no struct copies.
//!
//! **Two-class copy discipline.**
//! - `places_conflict.rs` — MIRRORED LEAF: byte-identical to production, never diverges; guarded by
//!   the `fork_sync::fork_sync_places_conflict` tripwire (its drift can hide from the differential).
//! - `errors.rs` — mirrored, comment-sync only (drift is caught behaviorally by the differential).
//! - `invalidates.rs` — FORKED STAGE: DIVERGES from production (write-aware invalidation); header
//!   only, no tripwire.
//!
//! **Equivalence first:** this engine had to produce `ConflictEdge`s byte-identical to
//! production on the full fixture suite AND a corpus sweep before any semantics diverged. The
//! orchestration (`borrow_conflicts`/`borrow_conflicts_replaying`) + glue (`invalid_loan_set`/
//! `extract_conflict_edges`) keep production's exact names — the module path is the only
//! distinguisher, so diffs against production are 1:1.

// Re-exports so the copied files' verbatim `super::{BorrowSet, Loan}` imports resolve here exactly
// as they did under production `borrow` — keeps the mirrors byte-identical (no import rewiring).
pub(crate) use crate::analyses::borrow::{BorrowSet, Loan};

mod conflicts;
mod errors;
mod invalidates;
mod loan_liveness;
mod origin_replay;
mod overlap_places_conflict;
mod places_conflict;
mod traversal_targets;

// Name-parity re-exports: callers reach `borrow_engine::borrow_conflicts[_replaying]`, matching
// production `borrow::borrow_conflicts[_replaying]` (the module path is the only distinguisher).
#[cfg(test)]
pub(crate) use conflicts::{borrow_conflicts, borrow_conflicts_replaying};
pub(crate) use conflicts::{
    borrow_conflicts_replaying_with_flows, borrow_conflicts_replaying_with_flows_and_copy_lends,
    borrow_conflicts_replaying_with_flows_and_copy_lends_and_escaped,
    borrow_conflicts_replaying_with_flows_and_parameter_overlap_and_escaped,
    borrow_conflicts_replaying_witnessed, borrow_conflicts_replaying_witnessed_with_copy_lends,
    borrow_conflicts_replaying_witnessed_with_copy_lends_and_escaped,
    borrow_conflicts_replaying_witnessed_with_flows_and_parameter_overlap_and_escaped,
};
#[cfg(test)]
pub(crate) use conflicts::{
    borrow_conflicts_replaying_with_flows_and_parameter_overlap, borrow_conflicts_with_flows,
};
// The place-based routing's compose/type-check decision, re-exported so its fallback is unit-testable
// in isolation (grouping-independent).
#[cfg(test)]
pub(crate) use conflicts::{demotion_witness_census, loan_liveness_census};
#[cfg(test)]
pub(crate) use invalidates::{RoutedCompose, route_compose};
#[cfg(test)]
pub(crate) use loan_liveness::with_escaped_extension_trace;
#[cfg(test)]
pub(crate) use origin_replay::selected_copy_lend_contains;
pub(crate) use overlap_places_conflict::ParameterOverlap;
pub(crate) use places_conflict::{AccessDepth, PlaceConflictBias, places_conflict};

#[cfg(test)]
mod fork_sync {
    /// Fork-sync tripwire (the mirrored-leaf discipline): `places_conflict.rs` is copied verbatim
    /// from production and must NEVER diverge — its drift can HIDE from the equivalence differential
    /// (a subtly-changed place-conflict could agree on every current fixture yet differ elsewhere).
    /// Asserts the mirror is byte-identical to the production source below its header boundary.
    #[test]
    fn fork_sync_places_conflict() {
        const BOUNDARY: &str =
            "==== MIRROR BOUNDARY — the tripwire compares everything below this line ====\n";
        let mirror = include_str!("places_conflict.rs");
        let production = include_str!("../../borrow/places_conflict.rs");
        let body = mirror
            .split_once(BOUNDARY)
            .expect("mirror header boundary present")
            .1;
        assert_eq!(
            body, production,
            "borrow_engine/places_conflict.rs drifted from production borrow/places_conflict.rs — \
             it is a MIRRORED LEAF that must never diverge; re-copy from production verbatim \
             (keep the header)."
        );
    }
}
