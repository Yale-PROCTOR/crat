//! BO → rewriter export surface.
//!
//! Loan identity is loan-level, and a loan's kind is derived fork-side.
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
//! The alternative is threading a flag and a cursor through
//! `emit_crate_ownership_constraints`, `InferCtxt`, and `extract_conflict_edges`.
//! That has three problems:
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
//! # The ambient arm
//!
//! [`arm_capture`] is inert: it installs nothing, so a run that arms through it
//! pays no recording cost. [`with_bo_export`] is the explicit-scope API for a
//! caller that wants a recording.

use std::cell::RefCell;

use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexVec;
use rustc_middle::mir::{Local, Location, Place};
use z3::ast::Bool;

use super::{guarded_repair::MirLocationKey, solver::SlotRef, ssa::constraint::Var};

// ---------------------------------------------------------------------------
// Flag gating — resolve once, fail loud, default off
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Lifetime-free keys
// ---------------------------------------------------------------------------

/// One MIR projection element, lifetime-free and **total**.
///
/// A previous `PlaceKey` kept only `Deref` (as a *count*) and
/// `Field`, discarding `Index`, `ConstantIndex`, `Subslice`, `Downcast` and
/// `OpaqueCast`. That made `arr[i]` and `arr[j]` the SAME key, and — because
/// derefs were counted rather than sequenced — made `(*p).f` and `*(p.f)`
/// indistinguishable. A key built on that is not a key, so the encoding is
/// total and ordered now.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub(crate) enum ProjKey {
    Deref,
    Field(u32),
    /// The MIR `Local` holding the index. Body-scoped, which is fine because
    /// `LoanKey` is scoped by `fn_did`; do NOT "normalize" it away.
    Index(u32),
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    /// `VariantIdx`. The symbol name in the real `ProjectionElem` is not
    /// identity and is dropped deliberately.
    Downcast(u32),
    OpaqueCast,
    Subtype,
    UnwrapUnsafeBinder,
}

/// Lifetime-free, **order-preserving** projection of a MIR [`Place`].
///
/// `Place<'tcx>` cannot escape the analysis, so it is projected here — the same
/// pattern as [`MirLocationKey`].
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct PlaceKey {
    pub local: Local,
    pub proj: Vec<ProjKey>,
}

impl PlaceKey {
    pub(crate) fn from_place(place: Place<'_>) -> Self {
        use rustc_middle::mir::ProjectionElem;
        let proj = place
            .projection
            .iter()
            .map(|elem| match elem {
                ProjectionElem::Deref => ProjKey::Deref,
                ProjectionElem::Field(f, _) => ProjKey::Field(f.as_u32()),
                ProjectionElem::Index(local) => ProjKey::Index(local.as_u32()),
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => ProjKey::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                },
                ProjectionElem::Subslice { from, to, from_end } => {
                    ProjKey::Subslice { from, to, from_end }
                }
                ProjectionElem::Downcast(_, variant) => ProjKey::Downcast(variant.as_u32()),
                ProjectionElem::OpaqueCast(_) => ProjKey::OpaqueCast,
                ProjectionElem::Subtype(_) => ProjKey::Subtype,
                ProjectionElem::UnwrapUnsafeBinder(_) => ProjKey::UnwrapUnsafeBinder,
            })
            .collect();
        PlaceKey {
            local: place.local,
            proj,
        }
    }

    /// Derived view, kept so ownership-version and loan-identity consumers written
    /// against the old shape
    /// do not change. The lossy form is no longer what is STORED.
    #[cfg(test)]
    pub(crate) fn derefs(&self) -> usize {
        self.proj
            .iter()
            .filter(|p| matches!(p, ProjKey::Deref))
            .count()
    }
}

pub(crate) fn location_key(location: Location) -> MirLocationKey {
    MirLocationKey::new(location.block.as_u32(), location.statement_index)
}

// ---------------------------------------------------------------------------
// Loan identity and the loan kind
// ---------------------------------------------------------------------------

/// The engine's effective per-loan kind, derived by exactly the expression the
/// invalidation path uses.
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

/// How the loan entered BO replay. Orthogonal to mutability [`LoanKind`]: the copy-lend funnel uses this typed
/// class to apply shared CopyLend invalidation without changing older syntactic loan semantics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LoanClass {
    Existing,
    CopyLend,
}

impl LoanKind {
    /// Reproduces the engine's branch at `borrow_engine/invalidates.rs`.
    ///
    /// This is the sole legal way to consume a `LoanKind` as a boolean.
    #[cfg(test)]
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

/// Owner of an `Assign` borrow, mirrored lifetime-free with a total order.
///
/// As a display field this payload would be only a matter of precision; as a
/// **key** component it is a correctness question.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum OwnerKey {
    Local(u32),
    Field { struct_did: u32, field_index: usize },
}

impl OwnerKey {
    pub(crate) fn from_owner(owner: crate::analyses::borrow::ProvenanceOwner) -> Self {
        use crate::analyses::borrow::ProvenanceOwner;
        match owner {
            ProvenanceOwner::Local(l) => OwnerKey::Local(l.as_u32()),
            ProvenanceOwner::Field(f) => OwnerKey::Field {
                struct_did: f.struct_did.local_def_index.as_u32(),
                field_index: f.field_index,
            },
        }
    }
}

/// Which loan this is. Orthogonal to [`LoanKind`]: it feeds the access-dependent
/// self-loan skip, not the kind derivation.
///
/// Both payloads are key components. `arg_index` alone happened to separate
/// two `CallArg` loans at one terminator, but only because a terminator has one
/// callee — an accident of the current shape, not a property of the key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum BorrowerKind {
    Assign { owner: OwnerKey },
    CallArg { callee: u32, arg_index: usize },
}

/// The **stable content identity** of one loan.
///
/// `BorrowSet` loan *numbering* permutes between runs and between CEGAR
/// rounds, because `utils/dsa/union_find.rs` uses a `RandomState`-hashed
/// `HashSet` and `borrow/mod.rs` pushes sibling loans in `group()` iteration
/// order. An index into that numbering is therefore not an identity, which is
/// exactly what this key provides.
///
/// **`kind` is deliberately NOT a component.** It is a pure function of
/// `fn_did` and the borrowed base local, so it adds zero
/// discriminating power — and a *derived* component in an identity key is a
/// drift hazard: if the derivation ever moved, one loan would silently become
/// two identities. Keys are built from inputs, not from analysis outputs.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct LoanKey {
    pub fn_did: LocalDefId,
    pub place: PlaceKey,
    pub location: MirLocationKey,
    pub borrower: BorrowerKind,
}

impl LoanKey {
    /// Total order over primitives. `LocalDefId` is projected through
    /// `local_def_index.as_u32()`, the idiom `guarded_repair::StableLoanKey` already uses.
    fn ord_key(&self) -> (u32, &Local, &Vec<ProjKey>, MirLocationKey, BorrowerKind) {
        (
            self.fn_did.local_def_index.as_u32(),
            &self.place.local,
            &self.place.proj,
            self.location,
            self.borrower,
        )
    }
}

impl Ord for LoanKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.ord_key().cmp(&other.ord_key())
    }
}

impl PartialOrd for LoanKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Borrowed place, kind, program point — all three present, now
/// carried by a content key rather than by a run-local index.
///
/// `PartialEq` is **hand-written to exclude `run_local_handle`**, and that is a
/// contract requirement rather than a convenience. The handle is documented as
/// "never compare across runs"; deriving equality made the compiler compare it
/// across runs anyway, so two exports with identical CONTENT compared unequal
/// whenever the loan numbering permuted. A field that is not identity must not
/// participate in identity.
#[derive(Clone, Debug, Eq)]
pub(crate) struct LoanIdentity {
    pub key: LoanKey,
    /// Run-local handle. **NOT an identity**: `BorrowSet` numbering
    /// permutes between runs AND between CEGAR rounds. Valid only for
    /// correlating against other facts from the SAME inference — never
    /// serialize it, never compare it across runs, never use it as a map key.
    pub run_local_handle: usize,
    /// Attribute, not key — see [`LoanKey`].
    pub kind: LoanKind,
    pub class: LoanClass,
    /// Whether this loan was in the final round's invalid set. **Surviving
    /// loans are `false`** — those are the ones a re-route must match against.
    pub invalid: bool,
}

impl PartialEq for LoanIdentity {
    fn eq(&self, other: &Self) -> bool {
        // `run_local_handle` deliberately excluded — see the type doc.
        self.key == other.key
            && self.kind == other.kind
            && self.class == other.class
            && self.invalid == other.invalid
    }
}

/// One residual conflict the accepted model tolerated, flattened to owner keys.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ResidualConflict {
    pub fn_did: LocalDefId,
    pub issuer: Option<SlotRef>,
    pub requirers: Vec<SlotRef>,
}

// ---------------------------------------------------------------------------
// Per-version ownership and move points
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

/// Responsibility at a source operation, conditioned on a source realloc
/// outcome. The edge is analysis state, not a new MIR/source assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReallocVersionSite {
    pub(crate) fn_did: LocalDefId,
    pub(crate) event: super::realloc::ReallocSiteKey,
    pub(crate) outcome: super::realloc::ReallocOutcome,
    pub(crate) edge: u32,
    pub(crate) location: MirLocationKey,
    pub(crate) local: Local,
    pub(crate) use_var: Option<Var>,
    pub(crate) def_var: Var,
}

/// Outcome-qualified responsibility for an unbranched `realloc` continuation.
/// The ordinary SSA result bit is a potential-owning qualifier; failure has
/// no result claim even when that qualifier permits an owner on success.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReallocCaseReceipt {
    pub(crate) event: super::realloc::ReallocSiteKey,
    pub(crate) case: super::realloc::ReallocCase,
    pub(crate) old_before: Option<Var>,
    pub(crate) old_after: Option<Var>,
    pub(crate) result_claim: Option<Var>,
}

// ---------------------------------------------------------------------------
// Selector provenance
// ---------------------------------------------------------------------------

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub(crate) enum BoundaryRole {
    Source,
    Sink,
}

/// Stable runtime identity of one endpoint-retraction assertion. Artifact writers
/// render `fn_did` through `TyCtxt::def_path_str`; the in-process key keeps the
/// typed MIR/function identities used by construction.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct EndpointRetractionKey {
    pub(crate) fn_did: LocalDefId,
    pub(crate) function_path: String,
    pub(crate) location: MirLocationKey,
    pub(crate) callee: String,
    pub(crate) role: BoundaryRole,
    pub(crate) var: Var,
    pub(crate) realloc_outcome: Option<super::realloc::ReallocOutcome>,
    pub(crate) endpoint: Option<PlaceKey>,
}

impl EndpointRetractionKey {
    pub(crate) fn sort_key(
        &self,
    ) -> (
        &str,
        MirLocationKey,
        &str,
        BoundaryRole,
        Option<super::realloc::ReallocOutcome>,
        Option<&PlaceKey>,
        u32,
    ) {
        (
            self.function_path.as_str(),
            self.location,
            self.callee.as_str(),
            self.role,
            self.realloc_outcome,
            self.endpoint.as_ref(),
            self.var.as_u32(),
        )
    }

    pub(crate) fn label(&self) -> String {
        let role = match self.role {
            BoundaryRole::Source => "source",
            BoundaryRole::Sink => "sink",
        };
        let mut label = format!(
            "t2-assert[{role}]({}:{}:{}:{},{:?})",
            self.function_path,
            self.location.block,
            self.location.statement_index,
            self.callee,
            self.var,
        );
        if let Some(outcome) = self.realloc_outcome {
            let outcome = match outcome {
                super::realloc::ReallocOutcome::Success => "success",
                super::realloc::ReallocOutcome::Failure => "failure",
            };
            label.push_str(&format!(";realloc={outcome};endpoint={:?}", self.endpoint));
        }
        label
    }
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
    pub function_path: String,
    pub location: MirLocationKey,
    pub callee: String,
}

// ---------------------------------------------------------------------------
// The capture itself
// ---------------------------------------------------------------------------

/// Everything the export records during one analysis run.
///
/// `PartialEq` is derived so a witness can compare the WHOLE record rather than
/// a hand-picked subset of fields.
#[derive(Clone, Debug, Default, PartialEq)]
pub(crate) struct BoExport {
    /// Recording epochs, not dynamic allocation generations or proof completion.
    pub(crate) ownership_constructions: u32,
    pub(crate) stack_entry_final: Option<super::licensing::stack_export::Accepted>,
    pub(crate) ownership_licensing: Option<Vec<super::licensing::snapshot::Snapshot>>,
    pub(crate) reader_replay: Option<Vec<super::licensing::reader_replay::Receipt>>,
    pub(crate) traversal_replay: Option<Vec<super::licensing::traversal_replay::Receipt>>,
    pub(crate) ownership_equations: Option<Vec<super::ownership_evidence::Equation>>,
    pub(crate) ownership_consumes: Option<Vec<super::ownership_occurrence::Consumption>>,
    pub(crate) ownership_terminals: Option<Vec<super::ownership_occurrence::Terminal>>,
    pub(crate) ownership_boundary_substitutions:
        Option<Vec<super::ownership_boundary::Substitution>>,
    pub(crate) ownership_call_arg_registrations:
        Option<Vec<super::ownership_boundary::CallArgRegistration>>,
    /// One carried source-event inventory from construction, independent of
    /// kind selection and the optional export recorder.
    pub source_events: Option<std::sync::Arc<super::source_events::SourceEvents>>,
    pub replay_source_events: Option<std::sync::Arc<super::source_events::SourceEvents>>,
    pub entry_protection: Option<std::sync::Arc<super::protected_entry::EntryAnalysis>>,
    pub entry_accesses: Vec<super::protected_entry::SourceAccess>,
    pub entry_fact_witnesses: Vec<super::protected_entry::evidence::FactWitness>,
    pub source_retirement: Option<super::retirement::RetirementReview>,
    pub retirement_rounds: Vec<super::retirement::RetirementReview>,
    pub comparisons: Option<super::comparison::ComparisonLedger>,
    pub qualifier_facts: Option<super::qualifier_facts::QualifierFacts>,
    pub array_fields: Option<super::array_fields::ArrayFieldFacts>,
    pub demand_evidence: Option<super::demand_evidence::DemandEvidence>,
    pub realloc_version_sites: Vec<ReallocVersionSite>,
    pub realloc_cases: Vec<ReallocCaseReceipt>,
    pub realloc_coverage_holds: Vec<super::realloc_ssa::coverage_hold::Receipt>,
    /// Consume sites, in emission order.
    pub version_sites: Vec<VersionSite>,
    /// Per-`Var` ownership, evaluated from the accepted model.
    pub version_owns: Option<IndexVec<Var, bool>>,
    /// The final round's store-as-move obligations. In-process only: not in
    /// the portable export or the cache entry while the schema is unsettled.
    pub(crate) move_store_obligations: Option<Vec<super::move_store::MoveStoreObligation>>,
    /// The final round's argument-order applications, one per
    /// (call, lent pointer); `None` when the argument-order arm is off. The rewriter's hoist
    /// (`arg_order_hoists`) keys them by the call's span, caller and lent local.
    pub(crate) arg_order_applied: Option<Vec<ArgOrderApplied>>,
    /// The final round's index-range discharges (relay era-5c/267), one per
    /// (access, loan); `None` when no round was recorded.
    pub(crate) range_disjoint: Option<Vec<super::index_ranges::RangeDisjoint>>,
    /// The calls where two or more arguments are views of one subject, one
    /// of them through a copy the relaxation's call arm admits (relay
    /// era-5c/269), one per (subject, call); model-independent, recorded by
    /// the solve before its rounds. `None` when no solve was recorded.
    pub(crate) multi_view: Option<Vec<super::copy_relax::MultiView>>,
    /// Selector provenance, index-aligned with `Selectors`.
    pub source_sites: Vec<SelectorSite>,
    pub sink_sites: Vec<SelectorSite>,
    /// Loan identity for the complete final `BorrowSet`.
    pub loans: Vec<LoanIdentity>,
    /// The residual-conflict certificate: the residual conflicts the accepted model TOLERATES.
    ///
    /// **Empty on every fixture measured so far, but NOT provably empty — an
    /// earlier version of this doc claimed it was, and that claim is
    /// RETRACTED.** Acceptance is `committed == 0`, a round in which no
    /// residual was *committable*, which is weaker than "no residuals".
    ///
    /// The retracted argument ran: every conflict reaching the commit stage
    /// has a committable `Ref` owner, because a non-`Ref` FIELD residual
    /// declines (`residual_nonref_field`) and a non-`Ref` LOCAL residual trips
    /// `guard_slots_are_ref`. **Both guards are vacuous on an edge with no
    /// owners at all** — `.find()` over an empty iterator is `None`, `.all()`
    /// over an empty iterator is `true` — so they wave such an edge through,
    /// `representative` returns `None`, and it contributes nothing to
    /// `committed`. `representative`'s own doc names this case: "kept
    /// defensive (e.g. an empty edge)".
    ///
    /// Owner-less edges are producible by construction, not hypothetically: a
    /// `Borrower::CallArg` loan gets `issuer: None`
    /// (`borrow_engine/conflicts.rs`, the `Borrower::CallArg(..) => None`
    /// arm) and no membership constraint (`borrow_engine/origin_replay.rs`
    /// skips every non-`Assign` borrower), so no provenance can ever `require`
    /// it and its requirer list is necessarily empty. `map_edges_to_slots`
    /// `.map()`s rather than filters, so the empty edge reaches the conflict
    /// set intact.
    ///
    /// What is NOT established is whether such an edge can survive to an
    /// *accepting* round; no fixture exhibits one. So: empty in
    /// practice, unproven in general, and a consumer must not assume either
    /// way.
    ///
    /// **`Option`, not `Vec`.** `None` means the accept point never ran,
    /// so nothing was recorded; `Some(vec![])` means it ran and tolerated no
    /// residual. As a bare `Vec` those two states were indistinguishable, and
    /// that is exactly why no test could detect deletion of the recorder: the
    /// default value and the recorded value were the same value. A consumer
    /// must not read `None` as "no residuals". Both repairs share the accept
    /// point, so either records the certificate.
    pub residual_conflicts: Option<Vec<ResidualConflict>>,
}

impl BoExport {
    /// A move point is a site where the token leaves this local.
    ///
    /// **Ownership disappearance alone is not sufficient** and this method does
    /// not claim it is: a `free` sink also forces the def version non-owning,
    /// as do returns and by-value calls. Callers must conjoin the MIR-shape
    /// check that the location is an assignment `other = this`. This returns the *candidate* sites only.
    #[cfg(test)]
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

    /// Surviving loans — the ones a re-route may match against.
    #[cfg(test)]
    pub(crate) fn surviving_loans(&self) -> impl Iterator<Item = &LoanIdentity> {
        self.loans.iter().filter(|l| !l.invalid)
    }
}

thread_local! {
    /// `None` by default, so any path that has NOT armed performs no
    /// allocation, no collection and no sorting. Mirrors
    /// `solver::SELECTOR_TRACE_CAPTURE`.
    ///
    /// No longer the same as "the production path": `run_bo` arms the recorder
    /// around its accepted-run region, so the sweep worker does allocate and
    /// collect. See the module doc.
    static BO_EXPORT_CAPTURE: RefCell<Option<BoExport>> = const { RefCell::new(None) };
}

/// RAII arm for the **allow-list** capture discipline.
///
/// # Why an allow-list
///
/// A deny-list — suspend capture at every probe surface that must not record —
/// was tried twice, and both times the enumeration turned out to be incomplete
/// (surfaces reached through a helper were missed). Enumeration is the
/// wrong correctness input — it fails open, silently, and each new probe
/// surface is a new chance to miss one.
///
/// Inverted: capture is armed **only** around the accepted-run region. Anything
/// outside that scope — probes, helpers, `solve_with_demotion`,
/// `explain_unsat`, and every surface not yet written — records nothing **by
/// construction**, with no list to maintain and nothing to keep in sync.
///
/// Drop ends the scope, so an early `return` out of the armed region is
/// correct without restructuring the region into a closure.
pub(crate) struct CaptureArm {
    prev: Option<BoExport>,
    namespace_scope: Option<super::licensing::stack_export::CaptureScope>,
    /// `false` for the ambient arm: it installed nothing and must therefore
    /// restore nothing, or it would clobber an enclosing scope.
    armed: bool,
}

impl Drop for CaptureArm {
    fn drop(&mut self) {
        if !self.armed {
            return;
        }
        BO_EXPORT_CAPTURE.with(|c| *c.borrow_mut() = self.prev.take());
        // Non-`Send` scaffolding must not outlive the scope.
        VERSION_ASTS.with(|c| *c.borrow_mut() = None);
        self.namespace_scope.take();
    }
}

impl CaptureArm {
    /// Take the recording and end the scope, in CANONICAL order.
    ///
    /// `loans` is sorted by [`LoanKey`] before it leaves the scope. Without
    /// this the vector carries `BorrowSet` index order, which permutes
    /// between runs and between CEGAR rounds — so two analyses of the same
    /// program produced exports with identical CONTENT in different ORDER, and
    /// `BoExport`'s derived `PartialEq` compares `Vec`s order-sensitively.
    ///
    /// That was not hypothetical: it made a whole-export comparison flake,
    /// differing only in two loans swapping position. Canonicalising here is
    /// what makes loan identity reproducible
    /// for the consumer the content key was introduced for — an unordered
    /// identity set is not much use if the container it ships in is unordered
    /// too.
    ///
    /// Recording-only is unaffected: this runs after the analysis, on the way
    /// out of the scope.
    pub(crate) fn finish(self) -> BoExport {
        if !self.armed {
            return BoExport::default();
        }
        let mut captured = BO_EXPORT_CAPTURE
            .with(|c| c.borrow_mut().take())
            .unwrap_or_default();
        captured.loans.sort_by(|a, b| a.key.cmp(&b.key));
        // `self`'s Drop still runs, restoring the previous scope.
        captured
    }
}

/// The ambient arm for the accepted-run region: inert. Nothing is installed,
/// nothing is restored on drop, and `finish()` yields an empty export.
#[cfg(test)]
pub(crate) fn arm_capture() -> CaptureArm {
    CaptureArm {
        prev: None,
        namespace_scope: None,
        armed: false,
    }
}

/// Unconditional arm — the explicit-scope primitive behind [`with_bo_export`],
/// deliberately NOT flag-gated.
///
/// Witnesses of the *positional* allow-list property use this rather than
/// [`arm_capture`]: "probes outside the armed region record nothing" is
/// orthogonal to whether the ambient flag is set, and testing it through the
/// gated entry would make it pass vacuously whenever the flag is off (i.e.
/// always, by default).
pub(crate) fn arm_scope() -> CaptureArm {
    let prev = BO_EXPORT_CAPTURE.with(|c| c.replace(Some(BoExport::default())));
    VERSION_ASTS.with(|c| *c.borrow_mut() = None);
    CaptureArm {
        prev,
        namespace_scope: Some(super::licensing::stack_export::enter_capture()),
        armed: true,
    }
}

/// Run `f` with export capture active, returning its result and the recording.
///
/// The returned value is the exact result of `f`; the capture cannot influence
/// it. Nesting is safe — the previous capture is restored on unwind as well as
/// on normal return.
pub(crate) fn with_bo_export<T>(f: impl FnOnce() -> T) -> (T, BoExport) {
    let arm = arm_scope();
    let output = f();
    (output, arm.finish())
}

/// Clone the current recording after an accepted model for complete cache
/// transport. This leaves the caller's capture and AST ownership in place.
pub(crate) fn snapshot() -> Option<BoExport> {
    BO_EXPORT_CAPTURE
        .with(|capture| capture.borrow().clone())
        .map(|mut capture| {
            capture.loans.sort_by(|a, b| a.key.cmp(&b.key));
            capture
        })
}

/// Whether capture is active.
///
/// Active if and only if a scope is open — [`with_bo_export`] or
/// [`arm_capture`]. There is no env-driven enablement, and off
/// any scope this is one thread-local read of an `Option` with every capture
/// point short-circuiting on it. Inside `run_bo`'s armed region it is true.
pub(crate) fn capturing() -> bool {
    BO_EXPORT_CAPTURE.with(|c| c.borrow().is_some())
}

/// Mutate the active capture, or do nothing when inactive.
///
/// Every capture point funnels through here, so "zero work when off" is a
/// property of one function rather than of every call site.
pub(crate) fn record(f: impl FnOnce(&mut BoExport)) {
    if !capturing() {
        return;
    }
    BO_EXPORT_CAPTURE.with(|c| {
        if let Some(export) = c.borrow_mut().as_mut() {
            f(export);
        }
    });
}

/// Optional observation of one completed normative construction. Local record
/// ordinals stay qualified by construction; only the export's construction
/// namespace is adjusted when it contains several independent solver builds.
pub(crate) fn record_ownership_facts(facts: &std::rc::Rc<super::licensing::facts::Facts>) {
    record(|capture| {
        let offset = capture.ownership_constructions;
        super::licensing::stack_export::record_namespace(facts, offset);
        capture.ownership_constructions = offset
            .checked_add(facts.constructions)
            .expect("export construction count");
        macro_rules! append {
            ($target:ident,$source:ident) => {
                let target = capture.$target.get_or_insert_with(Vec::new);
                for source in &facts.$source {
                    let mut row = source.clone();
                    row.point.construction = row
                        .point
                        .construction
                        .checked_add(offset)
                        .expect("export construction identity");
                    target.push(row);
                }
            };
        }
        append!(ownership_equations, equations);
        append!(ownership_consumes, consumes);
        append!(ownership_terminals, terminals);
        append!(ownership_boundary_substitutions, boundary_substitutions);
        append!(ownership_call_arg_registrations, call_arg_registrations);
        if let Some(snapshot) = super::licensing::snapshot::Snapshot::capture(facts, offset) {
            capture
                .ownership_licensing
                .get_or_insert_with(Vec::new)
                .push(snapshot);
        }
    });
}

// ---------------------------------------------------------------------------
// Selector call cursor
// ---------------------------------------------------------------------------
//
// The data a `SelectorSite` needs is split across two frames that never meet:
// the MIR walk knows `(fn_did, location)` at the terminator, while the callee
// name is only known one frame deeper, in the boundary dispatch. Rather than
// widen either signature, both halves are parked in scoped thread-locals and
// joined at the push site. Same shape as `solver::with_selector_trace` and
// `infer::with_own_assume_site`.

thread_local! {
    static LOCATION_CURSOR: RefCell<Option<(LocalDefId, String, MirLocationKey)>> =
        const { RefCell::new(None) };
    static CALLEE_CURSOR: RefCell<Option<String>> = const { RefCell::new(None) };
    static REALLOC_ENDPOINT: RefCell<Option<(super::realloc::ReallocOutcome, PlaceKey)>> = const { RefCell::new(None) };
}

pub(crate) fn with_realloc_endpoint<T>(
    outcome: super::realloc::ReallocOutcome,
    endpoint: PlaceKey,
    f: impl FnOnce() -> T,
) -> T {
    struct Restore(Option<(super::realloc::ReallocOutcome, PlaceKey)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            REALLOC_ENDPOINT.with(|cursor| *cursor.borrow_mut() = self.0.take());
        }
    }
    let _restore =
        Restore(REALLOC_ENDPOINT.with(|cursor| cursor.replace(Some((outcome, endpoint)))));
    f()
}

/// Set the `(fn_did, location)` half for the duration of `f`.
pub(crate) fn with_terminator_site<T>(
    fn_did: LocalDefId,
    function_path: String,
    location: Location,
    f: impl FnOnce() -> T,
) -> T {
    struct Restore(Option<(LocalDefId, String, MirLocationKey)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            LOCATION_CURSOR.with(|c| *c.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(
        LOCATION_CURSOR.with(|c| c.replace(Some((fn_did, function_path, location_key(location))))),
    );
    f()
}

/// Set the callee-name half for the duration of `f`.
pub(crate) fn with_callee<T>(callee: &str, f: impl FnOnce() -> T) -> T {
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
    let (fn_did, function_path, location) = LOCATION_CURSOR.with(|c| c.borrow().clone())?;
    let callee = CALLEE_CURSOR.with(|c| c.borrow().clone())?;
    Some(CallSite {
        fn_did,
        function_path,
        location,
        callee,
    })
}

/// Join the always-scoped call cursor into the key used by endpoint-retraction construction.
/// Unlike `record_selector`, this is normative construction input and
/// therefore remains available when export capture is off.
pub(crate) fn current_endpoint_retraction_key(
    role: BoundaryRole,
    var: Var,
) -> EndpointRetractionKey {
    let call = current_call_site().unwrap_or_else(|| {
        panic!("endpoint-retraction assertion emitted outside a modeled call-site cursor")
    });
    EndpointRetractionKey {
        fn_did: call.fn_did,
        function_path: call.function_path,
        location: call.location,
        callee: call.callee,
        role,
        var,
        realloc_outcome: REALLOC_ENDPOINT
            .with(|cursor| cursor.borrow().as_ref().map(|(outcome, _)| *outcome)),
        endpoint: REALLOC_ENDPOINT.with(|cursor| {
            cursor
                .borrow()
                .as_ref()
                .map(|(_, endpoint)| endpoint.clone())
        }),
    }
}

/// Record one retractable selector at its push site.
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

/// Record one consume site during ownership emission.
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

/// Evaluate the stashed ASTs against a live model.
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

/// Record one loan's identity.
pub(crate) fn record_loan(identity: LoanIdentity) {
    record(|export| export.loans.push(identity));
}

/// Start a fresh validation round.
///
/// The borrow oracle runs once per CEGAR round, each time under a DIFFERENT
/// candidacy predicate. Without this reset `loans` would accumulate the union
/// over all rounds — including loans from models the loop went on to reject —
/// and `surviving_loans()` would mix stale pre-commit loans with accepted ones.
/// Clearing at the start of every round leaves exactly the accepted round's
/// `BorrowSet` behind when the loop exits.
///
/// Residuals are cleared with them: they are recorded at the accept point and
/// must describe the same round.
pub(crate) fn begin_round() {
    record(|export| {
        export.loans.clear();
        export.reader_replay = None;
        export.traversal_replay = None;
        export.entry_protection = None;
        export.entry_accesses.clear();
        export.entry_fact_witnesses.clear();
        export.source_retirement = None;
        export.stack_entry_final = None;
        // Back to "not recorded this round" — NOT to "recorded, none found".
        export.residual_conflicts = None;
        export.move_store_obligations = None;
        export.arg_order_applied = Some(Vec::new());
        export.range_disjoint = Some(Vec::new());
    });
}

/// One argument-order application: at `location` (the receiving call) in
/// `function`, a read of the argument list was not an invalidation of the loan
/// on `*lent`, whose reborrow `owner` the call receives. The emission owes the
/// hoist of that read above the reborrow.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ArgOrderApplied {
    pub(crate) function: LocalDefId,
    pub(crate) location: Location,
    pub(crate) span: rustc_span::Span,
    pub(crate) lent: Local,
    pub(crate) owner: Local,
}

/// Record an argument-order application in the current round, once.
pub(crate) fn record_arg_order_applied(row: ArgOrderApplied) {
    record(|export| {
        if let Some(rows) = export.arg_order_applied.as_mut()
            && !rows.contains(&row)
        {
            rows.push(row);
        }
    });
}

/// Record an index-range discharge in the current round, once.
pub(crate) fn record_range_disjoint(row: super::index_ranges::RangeDisjoint) {
    record(|export| {
        if let Some(rows) = export.range_disjoint.as_mut()
            && !rows.contains(&row)
        {
            rows.push(row);
        }
    });
}

/// The solve's `multi-view` rows (relay era-5c/269), replacing any earlier
/// solve's.
pub(crate) fn record_multi_views(rows: Vec<super::copy_relax::MultiView>) {
    record(|export| export.multi_view = Some(rows));
}

/// This round's store-as-move obligations (the final round's remain).
pub(crate) fn record_move_store_obligations(rows: &[super::move_store::MoveStoreObligation]) {
    if !capturing() {
        return;
    }
    record(|export| export.move_store_obligations = Some(rows.to_vec()));
}

// `snapshot()` and `with_capture_suspended()` were DELETED in the allow-list
// cycle, and the second deletion is not merely tidying orphaned code.
// `with_capture_suspended` IS the deny-list primitive: leaving it callable
// would let one line silently re-create the discipline this module just
// abandoned, and make the tripwire in `model_accepts_with_flows` unreachable
// for whatever it wrapped. Capture is positional now — armed around the
// accepted run, inert everywhere else — and there is deliberately no API for
// making an exception.

/// Record the residual conflicts present at acceptance (the residual-conflict certificate).
///
/// Called at the `committed == 0` accept point, where the residual set is the
/// one the accepted model tolerates.
pub(crate) fn record_residuals(residuals: Vec<ResidualConflict>) {
    record(|export| export.residual_conflicts = Some(residuals));
}

#[cfg(test)]
pub(crate) use super::domain::SlotKind as SlotKindAlias;

#[cfg(test)]
mod tests;
