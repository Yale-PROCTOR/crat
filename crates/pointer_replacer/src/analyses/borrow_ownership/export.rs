//! BO → rewriter export surface (E-R1..E-R4).
//!
//! Specification: `docs/agents/plan/2026-07-28-m05-export-surface-spec.md`.
//! Ruling basis: Q11 (loan-level identity) and R-Q1a (kind derived fork-side).
//!
//! # Contract
//!
//! Everything here is **recording-only**. No value in this module influences a
//! constraint, a clause, a selector, an acceptance decision, or an emitted
//! model. The capture is a write-only side channel, exactly like the existing
//! [`super::solver::with_selector_trace`] diagnostic it is modelled on.
//!
//! # Why a scoped thread-local rather than threaded parameters
//!
//! The M0.5 spec proposed threading a flag and a cursor through
//! `emit_crate_ownership_constraints`, `InferCtxt`, and `extract_conflict_edges`.
//! Recon against current source found three problems with that:
//!
//! 1. `BoOwnDatabase<'opt>` borrows the `Optimize` owned by `KindSolver`, so
//!    returning it would forbid moving the solver — which several existing call
//!    sites do.
//! 2. `extract_conflict_edges` has no `LocalDefId` in scope, and widening its
//!    signature risks the ordering contract `extract_witnessed_conflict_edges`
//!    depends on (it zips against `invalid_loans.iter()`).
//! 3. The capture points in the emission path run *before* verification, so a
//!    flag resolved inside verification would be resolved too late.
//!
//! A scoped thread-local recorder solves all three: it needs no signature
//! changes, it is `None` (and therefore free) on the production path, and its
//! scope is established by the caller before any capture point runs.
//!
//! The env flag [`export_enabled_from_env`] is retained because the spec
//! mandates a fail-loud binary switch, and because a corpus worker needs to
//! request capture without a Rust-level scope.

use std::cell::RefCell;

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexVec;
use rustc_middle::mir::{Local, Location, Place};
use z3::ast::Bool;

use super::{l2::MirLocationKey, solver::SlotRef, ssa::constraint::Var};

// ---------------------------------------------------------------------------
// §1.3 Flag gating — fail loud, resolve once
// ---------------------------------------------------------------------------

/// `CRAT_BO_EXPORT ∈ {0,1}`; unset means `0`. Any other value fails loudly.
///
/// Modelled on [`super::l2::enabled_from_env`], the in-tree contract for a
/// binary switch. Callers must resolve this **once** and thread the resulting
/// `bool`; capture points never call it themselves.
pub(crate) fn export_enabled_from_env() -> bool {
    match std::env::var("CRAT_BO_EXPORT").as_deref() {
        Err(std::env::VarError::NotPresent) | Ok("0") => false,
        Ok("1") => true,
        Ok(other) => panic!("CRAT_BO_EXPORT must be 0 or 1, got {other:?}"),
        Err(error) => panic!("CRAT_BO_EXPORT is not valid Unicode: {error}"),
    }
}

// ---------------------------------------------------------------------------
// §1.2 Lifetime-free keys
// ---------------------------------------------------------------------------

/// Lifetime-free projection of a MIR [`Place`].
///
/// `Place<'tcx>` cannot escape the analysis, so it is projected here — the same
/// pattern L2 established with [`MirLocationKey`].
///
/// M1 interprets only `local` and `derefs`; `fields` is recorded for M3 and is
/// not read before then.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PlaceKey {
    pub local: Local,
    pub derefs: u8,
    pub fields: Vec<u32>,
}

impl PlaceKey {
    pub(crate) fn from_place(place: Place<'_>) -> Self {
        use rustc_middle::mir::ProjectionElem;
        let mut derefs = 0u8;
        let mut fields = Vec::new();
        for elem in place.projection {
            match elem {
                ProjectionElem::Deref => derefs = derefs.saturating_add(1),
                ProjectionElem::Field(f, _) => fields.push(f.as_u32()),
                _ => {}
            }
        }
        PlaceKey {
            local: place.local,
            derefs,
            fields,
        }
    }
}

pub(crate) fn location_key(location: Location) -> MirLocationKey {
    MirLocationKey::new(location.block.as_u32(), location.statement_index)
}

// ---------------------------------------------------------------------------
// §5.1 E-R4 — loan identity and the R-Q1a kind
// ---------------------------------------------------------------------------

/// The engine's effective per-loan kind, derived by exactly the expression the
/// invalidation path uses (R-Q1a §0.3).
///
/// **Three-valued on purpose.** The engine's guard is
/// `if let Some(p) = local_data[..] && !is_mutable(p) { continue }`, so a loan
/// whose base local has *no* provenance is **not** skipped. Collapsing that
/// case into [`LoanKind::Shared`] would invert the behaviour, which is why
/// [`LoanKind::skips_invalidation`] is the only predicate callers may branch on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LoanKind {
    /// Provenance exists and is mutable — the immutable-skip does not fire.
    Mut,
    /// Provenance exists and is immutable — the immutable-skip fires.
    Shared,
    /// No provenance for the base local — the skip does not fire.
    NoProvenance,
}

impl LoanKind {
    /// Reproduces the engine's branch at `borrow_engine/invalidates.rs`.
    ///
    /// This is the sole legal way to consume a `LoanKind` as a boolean.
    pub(crate) fn skips_invalidation(self) -> bool {
        matches!(self, LoanKind::Shared)
    }

    /// Derive from the raw provenance lookup, keeping `None` distinct.
    pub(crate) fn from_provenance_mutability(mutable: Option<bool>) -> Self {
        match mutable {
            Some(true) => LoanKind::Mut,
            Some(false) => LoanKind::Shared,
            None => LoanKind::NoProvenance,
        }
    }
}

/// Which loan this is. Orthogonal to [`LoanKind`]: it feeds the access-dependent
/// self-loan skip, not the kind derivation (R-Q1a §0.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BorrowerKind {
    Assign,
    CallArg { arg_index: usize },
}

/// Ruling Q11: borrowed place, kind, program point — all three present.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LoanIdentity {
    pub fn_did: LocalDefId,
    pub loan: usize,
    pub location: MirLocationKey,
    pub borrowed: PlaceKey,
    pub kind: LoanKind,
    pub borrower: BorrowerKind,
    /// Whether this loan was in the final round's invalid set. **Surviving
    /// loans are `false`** — those are the ones a re-route must match against.
    pub invalid: bool,
}

/// One residual conflict the accepted model tolerated, flattened to owner keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ResidualConflict {
    pub fn_did: LocalDefId,
    pub issuer: Option<SlotRef>,
    pub requirers: Vec<SlotRef>,
}

// ---------------------------------------------------------------------------
// §3 E-R2 — per-version ownership and move points
// ---------------------------------------------------------------------------

/// One consume site: a `(local, location)` pair the ownership emission visited.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct VersionSite {
    pub fn_did: LocalDefId,
    pub local: Local,
    pub location: MirLocationKey,
    pub use_var: Option<Var>,
    pub def_var: Option<Var>,
}

// ---------------------------------------------------------------------------
// §4 E-R3 — selector provenance
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BoundaryRole {
    Source,
    Sink,
}

/// The allocation or free call site behind one retractable selector.
///
/// Index-aligned with `Selectors::sources()` / `Selectors::sinks()` by
/// construction: `push_source_owning` / `push_sink_owning` are the only writers
/// of those vectors and each performs a single push.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SelectorSite {
    pub role: BoundaryRole,
    pub var: Var,
    /// The call site, when the emission walk knew it. `None` means the boundary
    /// was reached without an active call cursor — recorded rather than guessed.
    pub call: Option<CallSite>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CallSite {
    pub fn_did: LocalDefId,
    pub location: MirLocationKey,
    pub callee: String,
}

// ---------------------------------------------------------------------------
// The capture itself
// ---------------------------------------------------------------------------

/// Everything the export records during one analysis run.
#[derive(Clone, Debug, Default)]
pub(crate) struct BoExport {
    /// E-R2 consume sites, in emission order.
    pub version_sites: Vec<VersionSite>,
    /// E-R2 per-`Var` ownership, evaluated from the accepted model.
    pub version_owns: Option<IndexVec<Var, bool>>,
    /// E-R3 selector provenance, index-aligned with `Selectors`.
    pub source_sites: Vec<SelectorSite>,
    pub sink_sites: Vec<SelectorSite>,
    /// E-R4 loan identity for the complete final `BorrowSet`.
    pub loans: Vec<LoanIdentity>,
    /// E-R4 certificate: the residual conflicts the accepted model TOLERATES.
    ///
    /// **Non-empty in general.** Acceptance is `committed == 0` — a round in
    /// which no residual was *committable* — not an empty conflict set. A
    /// consumer that assumes emptiness here is reading the spec's corrected
    /// §1.2 limit 1 backwards.
    pub residual_conflicts: Vec<ResidualConflict>,
}

impl BoExport {
    /// A move point is a site where the token leaves this local.
    ///
    /// **Ownership disappearance alone is not sufficient** and this method does
    /// not claim it is: a `free` sink also forces the def version non-owning,
    /// as do returns and by-value calls. Callers must conjoin the MIR-shape
    /// check that the location is an assignment `other = this` (R-Q1a follow-on
    /// finding #7). This returns the *candidate* sites only.
    pub(crate) fn move_point_candidates(
        &self,
        fn_did: LocalDefId,
        local: Local,
    ) -> Vec<MirLocationKey> {
        let Some(owns) = self.version_owns.as_ref() else {
            return Vec::new();
        };
        let owned = |v: Option<Var>| v.is_some_and(|v| owns.get(v).copied().unwrap_or(false));
        self.version_sites
            .iter()
            .filter(|s| s.fn_did == fn_did && s.local == local)
            .filter(|s| owned(s.use_var) && !owned(s.def_var))
            .map(|s| s.location)
            .collect()
    }

    /// Surviving loans — the ones a re-route may match against (§5.3).
    pub(crate) fn surviving_loans(&self) -> impl Iterator<Item = &LoanIdentity> {
        self.loans.iter().filter(|l| !l.invalid)
    }
}

thread_local! {
    /// `None` by default: the production path performs no allocation, no
    /// collection, and no sorting. Mirrors `solver::SELECTOR_TRACE_CAPTURE`.
    static BO_EXPORT_CAPTURE: RefCell<Option<BoExport>> = const { RefCell::new(None) };
}

/// Run `f` with export capture active, returning its result and the recording.
///
/// The returned value is the exact result of `f`; the capture cannot influence
/// it. Nesting is safe — the previous capture is restored on unwind as well as
/// on normal return.
pub(crate) fn with_bo_export<T>(f: impl FnOnce() -> T) -> (T, BoExport) {
    struct Restore(Option<BoExport>);
    impl Drop for Restore {
        fn drop(&mut self) {
            BO_EXPORT_CAPTURE.with(|c| *c.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(BO_EXPORT_CAPTURE.with(|c| c.replace(Some(BoExport::default()))));
    VERSION_ASTS.with(|c| *c.borrow_mut() = None);
    let output = f();
    let captured = BO_EXPORT_CAPTURE
        .with(|c| c.borrow_mut().take())
        .unwrap_or_default();
    // Drop the non-`Send` scaffolding before the result crosses any boundary.
    VERSION_ASTS.with(|c| *c.borrow_mut() = None);
    (output, captured)
}

/// Whether capture is active. Cheap enough to call at a capture point.
pub(crate) fn capturing() -> bool {
    BO_EXPORT_CAPTURE.with(|c| c.borrow().is_some())
}

/// Mutate the active capture, or do nothing when inactive.
///
/// Every capture point funnels through here, so "zero work when off" is a
/// property of one function rather than of every call site.
pub(crate) fn record(f: impl FnOnce(&mut BoExport)) {
    BO_EXPORT_CAPTURE.with(|c| {
        if let Some(export) = c.borrow_mut().as_mut() {
            f(export);
        }
    });
}

// ---------------------------------------------------------------------------
// E-R3 call cursor
// ---------------------------------------------------------------------------
//
// The data a `SelectorSite` needs is split across two frames that never meet:
// the MIR walk knows `(fn_did, location)` at the terminator, while the callee
// name is only known one frame deeper, in the boundary dispatch. Rather than
// widen either signature, both halves are parked in scoped thread-locals and
// joined at the push site. Same shape as `solver::with_selector_trace` and
// `infer::with_own_assume_site`.

thread_local! {
    static LOCATION_CURSOR: RefCell<Option<(LocalDefId, MirLocationKey)>> =
        const { RefCell::new(None) };
    static CALLEE_CURSOR: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Set the `(fn_did, location)` half for the duration of `f`.
pub(crate) fn with_terminator_site<T>(
    fn_did: LocalDefId,
    location: Location,
    f: impl FnOnce() -> T,
) -> T {
    if !capturing() {
        return f();
    }
    struct Restore(Option<(LocalDefId, MirLocationKey)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            LOCATION_CURSOR.with(|c| *c.borrow_mut() = self.0.take());
        }
    }
    let _restore =
        Restore(LOCATION_CURSOR.with(|c| c.replace(Some((fn_did, location_key(location))))));
    f()
}

/// Set the callee-name half for the duration of `f`.
pub(crate) fn with_callee<T>(callee: &str, f: impl FnOnce() -> T) -> T {
    if !capturing() {
        return f();
    }
    struct Restore(Option<String>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CALLEE_CURSOR.with(|c| *c.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(CALLEE_CURSOR.with(|c| c.replace(Some(callee.to_owned()))));
    f()
}

/// Join both halves. `None` when either is missing — recorded as unknown rather
/// than guessed.
pub(crate) fn current_call_site() -> Option<CallSite> {
    let (fn_did, location) = LOCATION_CURSOR.with(|c| *c.borrow())?;
    let callee = CALLEE_CURSOR.with(|c| c.borrow().clone())?;
    Some(CallSite {
        fn_did,
        location,
        callee,
    })
}

/// Record one retractable selector at its push site (E-R3).
pub(crate) fn record_selector(role: BoundaryRole, var: Var) {
    record(|export| {
        let site = SelectorSite {
            role,
            var,
            call: current_call_site(),
        };
        match role {
            BoundaryRole::Source => export.source_sites.push(site),
            BoundaryRole::Sink => export.sink_sites.push(site),
        }
    });
}

/// Record one consume site during ownership emission (E-R2).
pub(crate) fn record_version_site(
    fn_did: LocalDefId,
    local: Local,
    location: Location,
    use_var: Option<Var>,
    def_var: Option<Var>,
) {
    record(|export| {
        export.version_sites.push(VersionSite {
            fn_did,
            local,
            location: location_key(location),
            use_var,
            def_var,
        })
    });
}

thread_local! {
    /// Emission scaffolding, deliberately NOT a field of [`BoExport`]:
    /// `z3::ast::Bool` is not `Send`, and `BoExport` has to cross the
    /// `run_compiler_on_str` boundary. The ASTs never leave the analysis; only
    /// the evaluated `bool`s do.
    static VERSION_ASTS: RefCell<Option<IndexVec<Var, Bool>>> = const { RefCell::new(None) };
}

/// Stash the emission's `Var -> Bool` map so the model readout can evaluate it
/// after the database has been dropped. Cloned rather than borrowed:
/// `BoOwnDatabase` borrows the `Optimize` the solver owns, but `Bool` is itself
/// lifetime-free, so the snapshot carries no borrow.
pub(crate) fn record_version_asts(asts: &IndexVec<Var, Bool>) {
    if !capturing() {
        return;
    }
    VERSION_ASTS.with(|c| *c.borrow_mut() = Some(asts.clone()));
}

/// Evaluate the stashed ASTs against a live model (E-R2).
///
/// `eval` runs only when a capture is active AND the ASTs were stashed, so the
/// model evaluation costs nothing on the production path.
pub(crate) fn record_version_owns_from(
    eval: impl FnOnce(&IndexVec<Var, Bool>) -> IndexVec<Var, bool>,
) {
    if !capturing() {
        return;
    }
    let owns = VERSION_ASTS.with(|c| c.borrow().as_ref().map(eval));
    if let Some(owns) = owns {
        record(|export| export.version_owns = Some(owns));
    }
}

/// Record one loan's identity (E-R4).
pub(crate) fn record_loan(identity: LoanIdentity) {
    record(|export| export.loans.push(identity));
}

/// Record the residual conflicts present at acceptance (E-R4 certificate).
///
/// Called at the `committed == 0` accept point, where the residual set is the
/// one the accepted model tolerates.
pub(crate) fn record_residuals(residuals: Vec<ResidualConflict>) {
    record(|export| export.residual_conflicts = residuals);
}

/// E-R1 is the accepted model itself, which existing entry points already
/// return. This alias exists so the four E-R names are all nameable.
pub(crate) type AcceptedModel = FxHashMap<SlotRef, SlotKindAlias>;
pub(crate) use super::domain::SlotKind as SlotKindAlias;

#[cfg(test)]
mod tests;
