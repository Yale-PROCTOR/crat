//! §NB3-3a — the BO-owned borrow theory engine ("fork the theory, keep the judge").
//!
//! A scoped fork (user ruling 2026-07-10, option (a)) of production `borrow`'s per-function
//! constraint-graph → fact-pipeline → conflict-edge extraction, self-contained under
//! `borrow_ownership/` so NB3-3b (write-aware invalidation) and NB3-3c (signature origins) can
//! extend it WITHOUT touching the byte-frozen production `borrow/`. NB6's final validator remains
//! the UNFORKED production `borrow::borrow_conflicts[_replaying]` path — that independence is D5.
//!
//! **Thin fork (task 0).** Production `borrow::borrow_inference` (pub) already exposes every
//! pre-invalidation fact as a pub field, so this engine REUSES it and forks only the loan
//! set + invalidation walk. The fact types (`Invalidates`/`Errors`/`LoanLiveness`) are
//! `SparseBitMatrix<PointIndex, Loan>` aliases — reused by value, no struct copies.
//!
//! **Two-class copy discipline (D-1).**
//! - `places_conflict.rs` — MIRRORED LEAF: byte-identical to production, never diverges; guarded by
//!   the `fork_sync::fork_sync_places_conflict` tripwire (its drift can hide from the differential).
//! - `errors.rs` — mirrored, comment-sync only (drift is caught behaviorally by the differential).
//! - `invalidates.rs` — FORKED STAGE: byte-identical at 3a, DIVERGES at 3b; header only, no tripwire.
//!
//! **3a is equivalence-first (rule 4):** this engine must produce `ConflictEdge`s byte-identical to
//! production on the full fixture suite AND a corpus sweep before any semantics diverge. The
//! orchestration (`borrow_conflicts`/`borrow_conflicts_replaying`) + glue (`invalid_loan_set`/
//! `extract_conflict_edges`) keep production's exact names — the module path is the only
//! distinguisher, so 3b/NB6 diffs are 1:1.

// TEMPORARY (until task 3 wires the orchestration that calls compute_invalidates/compute_errors):
// the copied stages are unused in isolation. Remove when `borrow_conflicts` lands.
#![allow(dead_code)]

// Re-exports so the copied files' verbatim `super::{BorrowSet, Loan}` imports resolve here exactly
// as they did under production `borrow` — keeps the mirrors byte-identical (no import rewiring).
pub(crate) use crate::analyses::borrow::{BorrowSet, Loan};

mod a5_places_conflict;
mod conflicts;
mod errors;
mod invalidates;
mod loan_liveness;
mod origin_replay;
mod places_conflict;

// Name-parity re-exports: callers reach `borrow_engine::borrow_conflicts[_replaying]`, matching
// production `borrow::borrow_conflicts[_replaying]` (the module path is the only distinguisher).
pub(crate) use a5_places_conflict::ParameterOverlap;
#[cfg(test)]
pub(crate) use conflicts::{borrow_conflicts, borrow_conflicts_replaying};
pub(crate) use conflicts::{
    borrow_conflicts_replaying_with_flows, borrow_conflicts_replaying_with_flows_and_copy_lends,
    borrow_conflicts_replaying_with_flows_and_parameter_overlap,
    borrow_conflicts_replaying_witnessed, borrow_conflicts_replaying_witnessed_with_copy_lends,
    borrow_conflicts_with_flows,
};
// §NB4-R: the compose/type-check decision, re-exported so its fallback is unit-testable in isolation
// (grouping-independent — see `nb4r_route_compose_fallback_on_type_mismatch`).
#[cfg(test)]
pub(crate) use conflicts::{demotion_witness_census, loan_liveness_census};
#[cfg(test)]
pub(crate) use invalidates::{RoutedCompose, route_compose};
#[cfg(test)]
pub(crate) use origin_replay::selected_copy_lend_contains;
pub(crate) use places_conflict::{AccessDepth, PlaceConflictBias, places_conflict};

/// §NB3-3a — routes the `borrow_verify` seam (and the `bo_c1` mirror) to the forked BO engine vs
/// the production `borrow` engine. **Default = `Fork` (flipped at 3a merge, A1).** During 3a dev the
/// default was `Production` so the equivalence differential could compare the two; the equivalence
/// row is frozen and the engines are model-equal (edge multiset ⇒ demotion set ⇒ model), so the
/// flip was free. Production is now validator-only — reachable via the switch for differentials +
/// NB6. Env `CRAT_BO_FORK_ENGINE ∈ {fork|on, production|off}`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ForkEngineMode {
    Production,
    Fork,
}

impl ForkEngineMode {
    /// Flipped to `Fork` at 3a merge (A1); production stays reachable via `CRAT_BO_FORK_ENGINE`.
    pub(crate) const DEFAULT: Self = ForkEngineMode::Fork;

    pub(crate) fn current() -> Self {
        // Reject a SET-but-invalid value (fail-loud on typos — a mistyped selector must NOT silently
        // fall back to production and mask which engine ran; 3a Codex review [high]). Unset ⇒ DEFAULT.
        match std::env::var("CRAT_BO_FORK_ENGINE") {
            Ok(v) => match v.as_str() {
                "fork" | "on" => ForkEngineMode::Fork,
                "production" | "off" => ForkEngineMode::Production,
                other => panic!(
                    "CRAT_BO_FORK_ENGINE={other:?} is not a valid selector \
                     (expected fork|on or production|off) — refusing to silently fall back"
                ),
            },
            Err(_) => Self::DEFAULT,
        }
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            ForkEngineMode::Production => "production",
            ForkEngineMode::Fork => "fork",
        }
    }
}

/// §HLZ-PORT (A2) — point-keyed `requires` + fused reachability loan-liveness inside the fork.
///
/// `Off` (the DEFAULT) runs the landed `LoanLiveAt` dataflow and the whole-body
/// `NativeConstraintGraph::requires`, so a flag-off suite must be byte-identical to the landed
/// head — that identity is this port's instrument-integrity proof.
///
/// `On` replaces both with one worklist reachability walk over `(provenance, point)` nodes that
/// emits `loan_liveness` and a point-keyed `LocalizedRequires` together, after Hanliang Zhang's
/// `hlz/flow-sensitive-borrow-inference @ 8d3878a2`. Scope is **A2**: only loan-derived reborrow
/// subset edges carry a program point; `origin_flow`'s closure-derived depth-0 value flows are
/// emitted `EdgeLocation::All` because a transitive-closure edge has no single location, and
/// locating them would mean touching `origin_flow` (that is A1, not authorized here).
///
/// Production `analyses/borrow/` is NOT edited in either mode: the point-keyed relation rides on
/// the fork's own `NativeInference` wrapper, so `borrow::borrow_conflicts` (the D5-independent NB6
/// validator) and production demotion keep their present behaviour by construction.
///
/// Env `CRAT_BO_POINT_REQUIRES ∈ {on|1, off|0}`; tests override per-thread via
/// `with_point_requires`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum PointRequiresMode {
    Off,
    On,
}

thread_local! {
    static POINT_REQUIRES_OVERRIDE: std::cell::Cell<Option<PointRequiresMode>> =
        const { std::cell::Cell::new(None) };
}

impl PointRequiresMode {
    /// PROPOSED, not landed: the port ships default-off so the branch's suite proves instrument
    /// integrity against the landed head before anything is measured.
    pub(crate) const DEFAULT: Self = PointRequiresMode::Off;

    pub(crate) fn current() -> Self {
        if let Some(mode) = POINT_REQUIRES_OVERRIDE.with(|cell| cell.get()) {
            return mode;
        }
        // Fail loud on a mistyped selector, exactly as `ForkEngineMode` does: a silent fallback
        // would mask which engine produced a measured number.
        match std::env::var("CRAT_BO_POINT_REQUIRES") {
            Ok(v) => match v.as_str() {
                "on" | "1" => PointRequiresMode::On,
                "off" | "0" => PointRequiresMode::Off,
                other => panic!(
                    "CRAT_BO_POINT_REQUIRES={other:?} is not a valid selector \
                     (expected on|1 or off|0) — refusing to silently fall back"
                ),
            },
            Err(_) => Self::DEFAULT,
        }
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            PointRequiresMode::Off => "off",
            PointRequiresMode::On => "on",
        }
    }
}

/// Run `f` with the point-keyed `requires` mode forced, restoring the previous value on the way
/// out (panic-safe). Lets one test assert BOTH modes in one process, so the witnesses do not
/// depend on how the suite's environment happens to be set.
#[cfg(test)]
pub(crate) fn with_point_requires<T>(mode: PointRequiresMode, f: impl FnOnce() -> T) -> T {
    struct Guard(Option<PointRequiresMode>);
    impl Drop for Guard {
        fn drop(&mut self) {
            POINT_REQUIRES_OVERRIDE.with(|cell| cell.set(self.0));
        }
    }
    let _guard = Guard(POINT_REQUIRES_OVERRIDE.with(|cell| cell.replace(Some(mode))));
    f()
}

/// §6.4 drop attribution sink. Env-gated (`CRAT_BO_REQUIRER_DROP_OUT`), append-only, flushed by
/// the caller. Never touched on the default path.
pub(crate) fn record_requirer_drop(line: String) {
    use std::io::Write as _;
    let Some(path) = std::env::var_os("CRAT_BO_REQUIRER_DROP_OUT") else {
        return;
    };
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        let _ = writeln!(f, "{line}");
    }
}

#[cfg(test)]
mod fork_sync {
    /// Fork-sync tripwire (D-1 mirrored-leaf discipline): `places_conflict.rs` is copied verbatim
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
