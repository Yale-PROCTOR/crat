use std::{
    cell::{Cell, RefCell},
    ops::Range,
    rc::Rc,
    time::{Duration, Instant},
};

use rustc_hash::FxHashMap;
use rustc_index::IndexVec;
use rustc_span::def_id::LocalDefId;
use z3::{Model, Optimize, SatResult, Solver, ast::Bool};

use super::{
    SlotKind,
    crate_slots::CrateSlots,
    demand_evidence::{
        self, ConstructionId, EndpointKey, EpochId, EventId, FinalSelection, QueryEvent,
        QueryOutcome, QueryPhase,
    },
    execution_guard::{self, Operation, QueryStage},
    l2::{
        CommitAction, CommitActionKind, GUARDED_COMMIT_CORE_FAMILY,
        RECURRENCE_ESCALATION_CORE_FAMILY,
    },
    slots::{SlotId, SlotUniverse},
    ssa::constraint::{Database, Gen, Var},
};

/// Parameters shared by every production backend and subsequent setter.
fn fixed_query_params() -> z3::Params {
    let mut params = z3::Params::new();
    params.set_u32("timeout", execution_guard::QUERY_TIMEOUT_MS);
    params
}

/// Global identity for a flattened pointer slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SlotRef {
    Field(SlotId),
    Local(LocalDefId, SlotId),
}

struct KindVars {
    raw: Bool,
    ref_: Bool,
    own: Bool,
}

/// §NB-R — opt-in tracked-core diagnostic. When a `KindSolver` is built via
/// `new_tracked`, every HARD constraint is asserted as `track ⇒ constraint`
/// with a fresh track literal recorded here alongside a human-readable label
/// (`{context}::{family}(…)`). Solving `check(&[tracks ∪ source selectors])`
/// then yields, on UNSAT, a core whose literals map back to labeled emission
/// sites — the tool that turns the corpus's opaque `unsat-nonsource` declines
/// into a named contradicting constraint set. Soft asserts (the Ref≻Raw
/// objective) are never tracked; `push_source_owning`'s selectors stay their
/// own (retractable) assumption class and are never double-gated.
///
/// A tracked solver is meaningful ONLY under assumption-solving: its hard
/// constraints are vacuously satisfiable without the tracks. The production
/// solve paths (`model_kinds`, `model_kinds_relaxing`, `verify_to_fixpoint`)
/// carry release-active guards refusing tracked instances.
pub(crate) struct CoreTracker {
    entries: RefCell<Vec<(Bool, String)>>,
    context: RefCell<String>,
    granularity: CoreTrackingGranularity,
    purpose: CoreTrackingPurpose,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CoreTrackingGranularity {
    Assertion,
    Family,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CoreTrackingPurpose {
    ProductionMandatory,
    Diagnostic,
}

impl CoreTracker {
    fn new() -> Self {
        CoreTracker {
            entries: RefCell::new(Vec::new()),
            context: RefCell::new(String::from("init")),
            granularity: CoreTrackingGranularity::Assertion,
            purpose: CoreTrackingPurpose::Diagnostic,
        }
    }

    fn new_mandatory() -> Self {
        CoreTracker {
            entries: RefCell::new(Vec::new()),
            context: RefCell::new(String::from("init")),
            granularity: CoreTrackingGranularity::Assertion,
            purpose: CoreTrackingPurpose::ProductionMandatory,
        }
    }

    fn new_family() -> Self {
        CoreTracker {
            entries: RefCell::new(Vec::new()),
            context: RefCell::new(String::from("init")),
            granularity: CoreTrackingGranularity::Family,
            purpose: CoreTrackingPurpose::Diagnostic,
        }
    }

    fn is_mandatory(&self) -> bool {
        self.purpose == CoreTrackingPurpose::ProductionMandatory
    }

    /// Set the provenance context (e.g. the fn being emitted, or the
    /// construction phase) prefixed onto subsequent labels.
    pub(crate) fn set_context(&self, context: &str) {
        *self.context.borrow_mut() = context.to_string();
    }

    #[cfg(test)]
    pub(crate) fn with_context<T>(&self, context: &str, f: impl FnOnce() -> T) -> T {
        struct Restore<'a> {
            context: &'a RefCell<String>,
            previous: Option<String>,
        }

        impl Drop for Restore<'_> {
            fn drop(&mut self) {
                *self.context.borrow_mut() = self.previous.take().expect("saved core context");
            }
        }

        let previous = self.context.replace(context.to_owned());
        let _restore = Restore {
            context: &self.context,
            previous: Some(previous),
        };
        f()
    }

    /// Mint a fresh track literal for one hard constraint and record its label.
    fn record(&self, label: String) -> Bool {
        if self.granularity == CoreTrackingGranularity::Family {
            // R385-1: `CORE_LABEL_FAMILIES` predates era-5b's constraint
            // families (`own-fold-*`, `own-original-cell-*`,
            // `own-guarded-traversal-view-zero`, `own-traversal-license`,
            // `a5-coarse-exclusion`), so a family-tracked probe over a program
            // that emits them died on the panic instead of reporting a core.
            // Family granularity has no production caller — it is the NB-R
            // diagnostic constructor — so an unregistered label gets a family of
            // its own head here and the probe stays usable. Registering them
            // properly is the seat's call; the panic stays for every other
            // granularity.
            let derived;
            let family = match core_label_family(&label) {
                Some(family) => family,
                None => {
                    derived = format!(
                        "unregistered::{}",
                        label.split(['(', '[']).next().unwrap_or(&label)
                    );
                    derived.as_str()
                }
            };
            if let Some((track, _)) = self
                .entries
                .borrow()
                .iter()
                .find(|(_, existing)| existing.strip_prefix("family-marker::") == Some(family))
            {
                return track.clone();
            }
            let track = Bool::fresh_const("selector_family_track");
            self.entries
                .borrow_mut()
                .push((track.clone(), format!("family-marker::{family}")));
            return track;
        }
        let track = Bool::fresh_const("nbr_track");
        self.entries.borrow_mut().push((
            track.clone(),
            format!("{}::{}", self.context.borrow(), label),
        ));
        track
    }

    /// All track literals, for `check(&assumptions)`.
    pub(crate) fn tracks(&self) -> Vec<Bool> {
        self.entries
            .borrow()
            .iter()
            .map(|(track, _)| track.clone())
            .collect()
    }

    fn len(&self) -> usize {
        self.entries.borrow().len()
    }

    fn truncate(&self, len: usize) {
        self.entries.borrow_mut().truncate(len);
    }

    #[cfg(test)]
    pub(crate) fn labeled_tracks(&self) -> Vec<(Bool, String)> {
        self.entries.borrow().clone()
    }

    /// Label of a core literal (z3 node identity, valid on the shared
    /// thread-local context — same basis as `model_kinds_relaxing`'s
    /// selector matching).
    pub(crate) fn label_of(&self, literal: &Bool) -> Option<String> {
        self.entries
            .borrow()
            .iter()
            .find(|(track, _)| track == literal)
            .map(|(_, label)| label.clone())
    }
}

/// The label families `CoreTracker` emits — the parse contract for the
/// mechanism test and the corpus histogram. Kept in one place so a new
/// emission site cannot invent an unlisted family silently.
pub(crate) const CORE_LABEL_FAMILIES: &[&str] = &[
    "kind-pin",
    "kind-copy-arm",
    "kind-equate",
    // NOTE: matching is first-containment (`family_of`), so the longer
    // "field-and-rev" MUST precede its prefix "field-and".
    "field-and-rev",
    "field-and",
    "field-forbid",
    "field-ref-source",
    "field-ref-forbid",
    "field-reader-kind",
    "field-reader-support",
    "own-field-reader",
    "own-reference-effect",
    "return-ref-origin",
    "link-own",
    "own-license",
    GUARDED_COMMIT_CORE_FAMILY,
    RECURRENCE_ESCALATION_CORE_FAMILY,
    "borrow-exclusion",
    // §NB4-4c: `¬own(slot)` demotion companion to `borrow-exclusion`. No substring overlap with
    // the `own-*` families or `borrow-exclusion` (first-containment matching stays unambiguous).
    "own-exclusion",
    "one-hot",
    // §NB1 per-site safety monotonicity (no substring overlap with the others).
    "safe-mono",
    "i1-adjacency",
    "own-copy-for-deref-lend",
    "own-copy-current",
    "own-copy-lend",
    "own-linear",
    "own-assume",
    "own-equal",
    "own-le",
    "own-eqmin",
    "source-selector",
    // §NB-F: free/realloc sink selectors (no substring overlap with
    // "source-selector" — first-containment matching stays unambiguous).
    "sink-selector",
    // Diagnostic forced assignments. They are not production constraints; they
    // are named so a family-tracked probe can assume them and see them in the
    // core beside the families that refuse them. No substring overlap.
    "s23-force",
    "r385-force",
    // R390-2: era-5b's own families. Longest first where one contains another,
    // because `family_of` is first-containment; every one of these is reached
    // only after the families above, so none of them shadows an older name.
    "own-guarded-traversal-argument-legacy",
    "own-null-join",
    "allocator-contract-pairing",
    "allocator-contract-port-open",
    "own-contract-port-drop",
    "own-contract-port",
    "own-guarded-traversal-view-zero",
    "own-original-cell-legacy-frame",
    "own-original-cell-disposition",
    "own-fold-caller-permission",
    "own-fold-member-permission",
    "own-fold-caller-endpoints",
    "own-fold-member-endpoints",
    "own-traversal-license",
    "own-traversal-pending",
    "own-fold-permission",
    "own-traversal-frame",
    "a5-coarse-exclusion",
    "own-original-cell",
    "own-fold-pending",
];

pub(crate) fn core_label_family(label: &str) -> Option<&'static str> {
    CORE_LABEL_FAMILIES
        .iter()
        .copied()
        .find(|family| label.contains(family))
}

/// Diagnosis-only provenance for hard `own-assume` constraints. The wrappers
/// are present in normal builds but inline to a direct call; only the test-only
/// corpus harness stores or reads the thread-local tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OwnAssumeSite {
    OpaqueCallArg,
    LibcRule,
    LocalWrapper,
    SsaTransfer,
    TemporaryFinalization,
    AggregateNull,
    NonOwnedConstant,
    CastOrDepth,
    OtherInternal,
    /// era-5c (R409-1): the allocator-contract pairing refusal.
    AllocatorContractPairing,
}

impl OwnAssumeSite {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::OpaqueCallArg => "opaque-call-arg",
            Self::LibcRule => "libc-rule",
            Self::LocalWrapper => "local-wrapper",
            Self::SsaTransfer => "ssa-transfer",
            Self::TemporaryFinalization => "temporary-finalization",
            Self::AggregateNull => "aggregate-null",
            Self::NonOwnedConstant => "non-owned-constant",
            Self::CastOrDepth => "cast-or-depth",
            Self::OtherInternal => "other-internal",
            Self::AllocatorContractPairing => "allocator-contract-pairing",
        }
    }
}

thread_local! {
    static OWN_ASSUME_SITE: Cell<OwnAssumeSite> =
        const { Cell::new(OwnAssumeSite::OtherInternal) };
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AssumptionCheckPhase {
    Hard,
    Optimize,
    OptimizeMaterialization,
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct AssumptionCheckEvent {
    pub(crate) phase: AssumptionCheckPhase,
    pub(crate) explicit: Vec<Bool>,
    pub(crate) bundle: Vec<Bool>,
    pub(crate) labels: Vec<String>,
    pub(crate) outcome: SatResult,
}

#[cfg(test)]
thread_local! {
    static ASSUMPTION_CHECK_CAPTURE: RefCell<Option<Vec<AssumptionCheckEvent>>> =
        const { RefCell::new(None) };
}

#[cfg(test)]
pub(crate) fn with_assumption_check_trace<T>(
    f: impl FnOnce() -> T,
) -> (T, Vec<AssumptionCheckEvent>) {
    struct Restore(Option<Vec<AssumptionCheckEvent>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            ASSUMPTION_CHECK_CAPTURE.with(|capture| {
                *capture.borrow_mut() = self.0.take();
            });
        }
    }
    let _restore =
        Restore(ASSUMPTION_CHECK_CAPTURE.with(|capture| capture.replace(Some(Vec::new()))));
    let output = f();
    let events = ASSUMPTION_CHECK_CAPTURE
        .with(|capture| capture.borrow_mut().take())
        .unwrap_or_default();
    (output, events)
}

/// Test-only observation of the real emission's indexed ownership ASTs and
/// their values in each model read by the production solver.
#[cfg(test)]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct OwnershipModelObservation {
    pub(crate) snapshot_lengths: Vec<usize>,
    pub(crate) model_reads: Vec<IndexVec<Var, bool>>,
}

#[cfg(test)]
#[derive(Default)]
struct OwnershipModelCapture {
    asts: Option<IndexVec<Var, Bool>>,
    observation: OwnershipModelObservation,
}

#[cfg(test)]
thread_local! {
    static OWNERSHIP_MODEL_CAPTURE: RefCell<Option<OwnershipModelCapture>> =
        const { RefCell::new(None) };
}

/// Observe without enabling BoExport, creating ASTs, or issuing queries.
#[cfg(test)]
pub(crate) fn with_ownership_model_observation<T>(
    f: impl FnOnce() -> T,
) -> (T, OwnershipModelObservation) {
    struct Restore(Option<OwnershipModelCapture>);
    impl Drop for Restore {
        fn drop(&mut self) {
            OWNERSHIP_MODEL_CAPTURE.with(|capture| {
                *capture.borrow_mut() = self.0.take();
            });
        }
    }
    let _restore = Restore(
        OWNERSHIP_MODEL_CAPTURE
            .with(|capture| capture.replace(Some(OwnershipModelCapture::default()))),
    );
    let output = f();
    let capture = OWNERSHIP_MODEL_CAPTURE
        .with(|capture| capture.borrow_mut().take())
        .expect("active ownership model observation");
    (output, capture.observation)
}

pub(crate) fn with_own_assume_site<T>(site: OwnAssumeSite, f: impl FnOnce() -> T) -> T {
    struct Restore(OwnAssumeSite);
    impl Drop for Restore {
        fn drop(&mut self) {
            OWN_ASSUME_SITE.with(|slot| slot.set(self.0));
        }
    }
    let _restore = Restore(OWN_ASSUME_SITE.with(|slot| slot.replace(site)));
    f()
}

pub(crate) fn current_own_assume_site() -> OwnAssumeSite {
    OWN_ASSUME_SITE.with(Cell::get)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SelectorTracePhase {
    Drop,
    Reenable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SelectorTraceOutcome {
    Dropped,
    Restored,
    StayedDropped,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SelectorTraceEvent {
    pub epoch: usize,
    pub phase: SelectorTracePhase,
    pub selector_index: usize,
    pub active_before: Vec<usize>,
    pub core_selectors: Vec<usize>,
    /// Canonical diagnostic labels for every typed assumption in this core.
    /// T2 fills this with endpoint and mandatory-track labels; legacy paths
    /// leave it empty.
    pub core_labels: Vec<String>,
    pub outcome: SelectorTraceOutcome,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SelectorEpochTrace {
    pub events: Vec<SelectorTraceEvent>,
    pub final_dropped: Vec<usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SelectorTrace {
    pub n_sources: usize,
    pub total: usize,
    pub epochs: Vec<SelectorEpochTrace>,
}

thread_local! {
    /// Diagnosis-only selector retraction trace. `None` is the default and
    /// performs no allocation, collection, or sorting on the production path.
    static SELECTOR_TRACE_CAPTURE: RefCell<Option<SelectorTrace>> = const { RefCell::new(None) };
}

/// Run an untracked solve while recording its actual selector drop/re-enable
/// decisions. The returned model is the exact result of `f`; the side channel
/// is write-only and cannot influence the choice policy.
pub(crate) fn with_selector_trace<T>(f: impl FnOnce() -> T) -> (T, SelectorTrace) {
    struct Restore(Option<SelectorTrace>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SELECTOR_TRACE_CAPTURE.with(|capture| {
                *capture.borrow_mut() = self.0.take();
            });
        }
    }
    let _restore = Restore(
        SELECTOR_TRACE_CAPTURE.with(|capture| capture.replace(Some(SelectorTrace::default()))),
    );
    let output = f();
    let trace = SELECTOR_TRACE_CAPTURE
        .with(|capture| capture.borrow_mut().take())
        .unwrap_or_default();
    (output, trace)
}

struct DemandCapture {
    construction: ConstructionId,
    endpoints: Vec<EndpointKey>,
    selectors: Vec<Bool>,
    next_epoch: u32,
    epoch: Option<EpochId>,
    next_event: u32,
    last_event: Option<EventId>,
    query: Option<(QueryPhase, Option<usize>)>,
}

pub struct KindSolver {
    solver: Optimize,
    vars: FxHashMap<SlotRef, KindVars>,
    tracker: Option<CoreTracker>,
    check_sat_count: Cell<usize>,
    hard_check_count: Cell<usize>,
    optimize_materialization_count: Cell<usize>,
    lazy_plain_hard_check_count: Cell<usize>,
    lazy_tracked_recheck_count: Cell<usize>,
    lazy_plain_materialization_count: Cell<usize>,
    hard_check_elapsed: Cell<Duration>,
    optimize_materialization_elapsed: Cell<Duration>,
    /// R379-2: the return-port rows admitted at emission, in slot-key order.
    /// They are ASSERTED at materialisation, not at emission, because the
    /// refusals they must yield to — the objective, a caller's final-zero —
    /// enter the system after emission ends. Report 048 measured that.
    return_port_admitted: RefCell<Vec<(String, SlotRef)>>,
    /// One entry per materialisation round: how many of those rows survived.
    return_port_kept: RefCell<Vec<usize>>,
    mandatory_scope_lengths: RefCell<Vec<usize>>,
    round_model_failure: RefCell<Option<RoundModelFailure>>,
    demand_capture: RefCell<Option<DemandCapture>>,
    ownership_facts: RefCell<Option<Rc<super::licensing::facts::Facts>>>,
    original_cell_model: RefCell<Option<Rc<super::licensing::model_selection::Selection>>>,
}

/// R1a's private hard-query backend. It snapshots only `Optimize`'s hard
/// assertions; soft preferences remain owned by `KindSolver::solver` and are
/// consulted only by `optimized_model_under`. LIC Phase 2 activates each
/// candidate assumption set as temporary plain-hard assertions first and pays
/// for a tracked assumption recheck only when that first check is UNSAT.
pub(crate) struct HardLoopSolver {
    solver: Solver,
    synced_assertions: Cell<usize>,
}

impl HardLoopSolver {
    pub(crate) fn assertion_count(&self) -> usize {
        self.solver.get_assertions().len()
    }

    /// Append hard assertions added since the previous synchronization.
    pub(crate) fn sync_from(&self, source: &KindSolver) -> usize {
        let assertions = source.solver.get_assertions();
        let synced = self.synced_assertions.get();
        assert!(
            assertions.len() >= synced,
            "Optimize hard assertions cannot shrink during validation"
        );
        for assertion in &assertions[synced..] {
            self.solver.assert(assertion);
        }
        self.synced_assertions.set(assertions.len());
        assertions.len() - synced
    }
}

pub(crate) struct RelaxedSelectors {
    assumptions: Vec<Bool>,
    dropped: Vec<Bool>,
}

enum HardRelaxResult {
    Sat(RelaxedSelectors),
    Unsat,
    Unknown,
}

/// Observation-only first failure from the decomposed round-model path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RoundModelFailure {
    HardUnsat {
        active_t2: usize,
        core_labels: Vec<String>,
    },
    HardUnknown {
        active_t2: usize,
        reason: String,
    },
    OptimizeUnsat {
        active_t2: usize,
    },
    OptimizeUnknown {
        active_t2: usize,
        reason: String,
    },
    OptimizeMissingModel {
        active_t2: usize,
    },
}

impl RoundModelFailure {
    pub(crate) fn summary(&self) -> String {
        match self {
            Self::HardUnsat {
                active_t2,
                core_labels,
            } => format!(
                "hard-unsat active_t2={active_t2} core_labels={}",
                core_labels.join(" | ")
            ),
            Self::HardUnknown { active_t2, reason } => {
                format!("hard-unknown active_t2={active_t2} reason={reason}")
            }
            Self::OptimizeUnsat { active_t2 } => {
                format!("optimize-unsat active_t2={active_t2}")
            }
            Self::OptimizeUnknown { active_t2, reason } => {
                format!("optimize-unknown active_t2={active_t2} reason={reason}")
            }
            Self::OptimizeMissingModel { active_t2 } => {
                format!("optimize-missing-model active_t2={active_t2}")
            }
        }
    }
}

impl RelaxedSelectors {
    pub(crate) fn dropped(&self) -> &[Bool] {
        &self.dropped
    }
}

impl KindSolver {
    pub fn new(slots: &CrateSlots) -> Self {
        Self::build(slots, Some(CoreTracker::new_mandatory()), true)
    }

    /// §NB-R diagnostic constructor: every hard constraint is track-gated.
    /// The result must ONLY be driven via assumption solving (see
    /// `CoreTracker`); production solve paths refuse it.
    pub(crate) fn new_tracked(slots: &CrateSlots) -> Self {
        Self::build(slots, Some(CoreTracker::new()), true)
    }

    /// Corpus selector-leak diagnostic constructor: all hard constraints in
    /// one `CORE_LABEL_FAMILIES` family share a single assumption marker.
    /// This preserves family membership while avoiding per-assertion tracking.
    pub(crate) fn new_family_tracked(slots: &CrateSlots) -> Self {
        Self::build(slots, Some(CoreTracker::new_family()), true)
    }

    /// Measurement-only hard-SAT constructor. It emits the exact production
    /// hard universe but omits soft kind preferences, so per-assumption funnel
    /// queries answer achievability without repeatedly optimizing an irrelevant
    /// objective.
    #[cfg(test)]
    pub(crate) fn new_hard_only(slots: &CrateSlots) -> Self {
        Self::build(slots, Some(CoreTracker::new_mandatory()), false)
    }

    /// Family-core twin of [`Self::new_hard_only`].
    #[cfg(test)]
    pub(crate) fn new_family_tracked_hard_only(slots: &CrateSlots) -> Self {
        Self::build(slots, Some(CoreTracker::new_family()), false)
    }

    pub(crate) fn tracker(&self) -> Option<&CoreTracker> {
        self.tracker.as_ref()
    }

    pub(crate) fn is_diagnostic_tracked(&self) -> bool {
        self.tracker
            .as_ref()
            .is_some_and(|tracker| !tracker.is_mandatory())
    }

    fn mandatory_tracks(&self) -> Vec<Bool> {
        self.tracker
            .as_ref()
            .filter(|tracker| tracker.is_mandatory())
            .map(CoreTracker::tracks)
            .unwrap_or_default()
    }

    fn assumption_bundle(&self, assumptions: &[Bool]) -> Vec<Bool> {
        let mut bundle = self.mandatory_tracks();
        bundle.extend_from_slice(assumptions);
        bundle
    }

    fn core_labels(&self, selectors: &Selectors, core: &[Bool]) -> Vec<String> {
        let mut labels = core
            .iter()
            .filter_map(|literal| {
                selectors
                    .index_of(literal)
                    .map(|index| selectors.keys[index].label())
                    .or_else(|| {
                        self.tracker
                            .as_ref()
                            .and_then(|tracker| tracker.label_of(literal))
                    })
            })
            .collect::<Vec<_>>();
        labels.sort();
        labels.dedup();
        labels
    }

    #[cfg(test)]
    fn record_assumption_event(
        &self,
        phase: AssumptionCheckPhase,
        explicit: &[Bool],
        bundle: &[Bool],
        outcome: SatResult,
    ) {
        ASSUMPTION_CHECK_CAPTURE.with(|capture| {
            let mut capture = capture.borrow_mut();
            let Some(events) = capture.as_mut() else {
                return;
            };
            let labels = bundle
                .iter()
                .map(|literal| {
                    self.tracker
                        .as_ref()
                        .and_then(|tracker| tracker.label_of(literal))
                        .unwrap_or_else(|| literal.to_string())
                })
                .collect();
            events.push(AssumptionCheckEvent {
                phase,
                explicit: explicit.to_vec(),
                bundle: bundle.to_vec(),
                labels,
                outcome,
            });
        });
    }

    fn build(slots: &CrateSlots, tracker: Option<CoreTracker>, add_objective: bool) -> Self {
        execution_guard::require(Operation::SolverBuild);
        let solver = Optimize::new();
        solver.set_params(&fixed_query_params());
        let mut vars = FxHashMap::default();

        add_universe(
            &solver,
            tracker.as_ref(),
            &mut vars,
            &slots.field_slots,
            SlotRef::Field,
        );
        for (&fn_did, universe) in &slots.fn_local_slots {
            add_universe(&solver, tracker.as_ref(), &mut vars, universe, |slot| {
                SlotRef::Local(fn_did, slot)
            });
        }

        if add_objective {
            // Prefer Ref where hard constraints allow it, then Raw over unnecessary Owning.
            let big = vars.len() as u64 + 1;
            for kind_vars in vars.values() {
                solver.assert_soft(&kind_vars.ref_, big, None);
                solver.assert_soft(&kind_vars.raw, 1u64, None);
            }
        }

        KindSolver {
            solver,
            vars,
            tracker,
            check_sat_count: Cell::new(0),
            hard_check_count: Cell::new(0),
            optimize_materialization_count: Cell::new(0),
            lazy_plain_hard_check_count: Cell::new(0),
            lazy_tracked_recheck_count: Cell::new(0),
            lazy_plain_materialization_count: Cell::new(0),
            hard_check_elapsed: Cell::new(Duration::ZERO),
            optimize_materialization_elapsed: Cell::new(Duration::ZERO),
            return_port_admitted: RefCell::new(Vec::new()),
            return_port_kept: RefCell::new(Vec::new()),
            mandatory_scope_lengths: RefCell::new(Vec::new()),
            round_model_failure: RefCell::new(None),
            demand_capture: RefCell::new(None),
            ownership_facts: RefCell::new(None),
            original_cell_model: RefCell::new(None),
        }
    }

    /// Retain completed construction inputs without retaining an Optimize borrow.
    pub(crate) fn set_ownership_facts(&self, facts: Rc<super::licensing::facts::Facts>) {
        let mut stored = self.ownership_facts.borrow_mut();
        assert!(
            stored.is_none(),
            "ownership facts already bound to this solver"
        );
        *stored = Some(facts);
    }

    /// Shared immutable input for construction consumers and optional export.
    pub(crate) fn ownership_facts(&self) -> Option<Rc<super::licensing::facts::Facts>> {
        self.ownership_facts.borrow().clone()
    }

    /// Bind recording to this solver's actual construction, never to the last
    /// constructor that happened to run on the thread.
    pub(crate) fn set_demand_capture(&self, construction: Option<ConstructionId>) {
        *self.demand_capture.borrow_mut() = construction.map(|construction| DemandCapture {
            construction,
            endpoints: demand_evidence::endpoint_keys(construction)
                .expect("registered demand construction"),
            selectors: Vec::new(),
            next_epoch: 0,
            epoch: None,
            next_event: 0,
            last_event: None,
            query: None,
        });
    }

    fn begin_demand_epoch(&self, selectors: &Selectors) {
        let mut capture = self.demand_capture.borrow_mut();
        let Some(capture) = capture.as_mut() else { return };
        assert_eq!(
            capture.endpoints.len(),
            selectors.all().len(),
            "bound endpoint universe"
        );
        capture.selectors = selectors.all().to_vec();
        capture.epoch = Some(EpochId {
            construction: capture.construction,
            ordinal: capture.next_epoch,
        });
        capture.next_epoch = capture
            .next_epoch
            .checked_add(1)
            .expect("demand epoch ordinal");
        capture.next_event = 0;
        capture.last_event = None;
        capture.query = None;
    }

    fn demand_query_pending(&self) -> bool {
        self.demand_capture
            .borrow()
            .as_ref()
            .is_some_and(|capture| capture.query.is_some())
    }

    fn prepare_demand_query(&self, phase: QueryPhase, candidate: Option<usize>) {
        if let Some(capture) = self.demand_capture.borrow_mut().as_mut()
            && capture.epoch.is_some()
        {
            capture.query = Some((phase, candidate));
        }
    }

    fn note_demand_query(
        &self,
        active: &[Bool],
        outcome: SatResult,
        core: &[Bool],
        reason: Option<String>,
    ) {
        let mut bound = self.demand_capture.borrow_mut();
        let Some(capture) = bound.as_mut() else { return };
        let Some((phase, candidate)) = capture.query.take() else { return };
        let epoch = capture.epoch.expect("query epoch");
        let id = EventId {
            epoch,
            ordinal: capture.next_event,
        };
        capture.next_event = capture
            .next_event
            .checked_add(1)
            .expect("demand event ordinal");
        capture.last_event = Some(id);
        let endpoint = |literal: &Bool| {
            capture
                .selectors
                .iter()
                .position(|known| known == literal)
                .map(|index| capture.endpoints[index].clone())
        };
        let core_endpoints: Vec<_> = core.iter().filter_map(endpoint).collect();
        let mut mandatory_core_labels: Vec<_> = core
            .iter()
            .filter_map(|literal| {
                self.tracker
                    .as_ref()
                    .and_then(|tracker| tracker.label_of(literal))
            })
            .collect();
        mandatory_core_labels.sort();
        mandatory_core_labels.dedup();
        let result = match outcome {
            SatResult::Sat => QueryOutcome::Sat,
            SatResult::Unsat => QueryOutcome::Unsat,
            SatResult::Unknown => QueryOutcome::Unknown {
                reason: reason.unwrap_or_else(|| "reason-unavailable".to_owned()),
            },
        };
        let terminal = outcome == SatResult::Unknown
            || (outcome == SatResult::Unsat && core_endpoints.is_empty());
        let event = QueryEvent {
            id,
            phase,
            candidate: candidate.map(|index| capture.endpoints[index].clone()),
            active: active.iter().filter_map(endpoint).collect(),
            core_endpoints,
            mandatory_core_labels,
            outcome: result.clone(),
        };
        drop(bound);
        demand_evidence::record_query(event);
        if terminal {
            demand_evidence::record_final_selection(FinalSelection {
                epoch,
                dropped: None,
                outcome: result,
            });
        }
    }

    fn mark_demand_candidate(&self, index: usize) {
        let bound = self.demand_capture.borrow();
        let Some(capture) = bound.as_ref() else { return };
        if let Some(id) = capture.last_event {
            demand_evidence::mark_candidate(id, capture.endpoints[index].clone());
        }
    }

    fn finish_demand_epoch(&self, dropped: &[Bool]) {
        let bound = self.demand_capture.borrow();
        let Some(capture) = bound.as_ref() else { return };
        let epoch = capture.epoch.expect("completed selector epoch");
        let dropped = dropped
            .iter()
            .map(|literal| {
                let index = capture
                    .selectors
                    .iter()
                    .position(|known| known == literal)
                    .expect("dropped endpoint identity");
                capture.endpoints[index].clone()
            })
            .collect();
        demand_evidence::record_final_selection(FinalSelection {
            epoch,
            dropped: Some(dropped),
            outcome: QueryOutcome::Sat,
        });
    }

    pub fn assume(&self, slot: SlotRef, kind: SlotKind) {
        let vars = self
            .vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
        let bit = match kind {
            SlotKind::Raw => &vars.raw,
            SlotKind::Ref => &vars.ref_,
            SlotKind::Owning => &vars.own,
        };
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("kind-pin({slot:?},{kind:?})"),
            bit,
        );
    }

    pub fn equate(&self, a: SlotRef, b: SlotRef) {
        let va = self
            .vars
            .get(&a)
            .unwrap_or_else(|| panic!("unknown slot: {a:?}"));
        let vb = self
            .vars
            .get(&b)
            .unwrap_or_else(|| panic!("unknown slot: {b:?}"));
        let tracker = self.tracker.as_ref();
        assert_hard(
            &self.solver,
            tracker,
            || format!("kind-equate({a:?},{b:?},raw)"),
            &!va.raw.xor(&vb.raw),
        );
        assert_hard(
            &self.solver,
            tracker,
            || format!("kind-equate({a:?},{b:?},ref)"),
            &!va.ref_.xor(&vb.ref_),
        );
        assert_hard(
            &self.solver,
            tracker,
            || format!("kind-equate({a:?},{b:?},own)"),
            &!va.own.xor(&vb.own),
        );
    }

    /// A12 phase-1 depth-zero copy disjunction. The destination (`lhs`) and source (`rhs`)
    /// either keep the current equal-kind reading, or take the owner-to-shared-reference lend
    /// reading `lhs.ref && rhs.own`. The lend guard is derived from the one-hot kind bits rather
    /// than allocated as a free selector, so it adds no independent model choice.
    pub(crate) fn lend_or_equate(&self, lhs: SlotRef, rhs: SlotRef) {
        let lend = self.lend_guard(lhs, rhs);
        let lhs_vars = self
            .vars
            .get(&lhs)
            .unwrap_or_else(|| panic!("unknown slot: {lhs:?}"));
        let rhs_vars = self
            .vars
            .get(&rhs)
            .unwrap_or_else(|| panic!("unknown slot: {rhs:?}"));
        let tracker = self.tracker.as_ref();

        for (bit, equal) in [
            ("raw", !lhs_vars.raw.xor(&rhs_vars.raw)),
            ("ref", !lhs_vars.ref_.xor(&rhs_vars.ref_)),
            ("own", !lhs_vars.own.xor(&rhs_vars.own)),
        ] {
            assert_hard(
                &self.solver,
                tracker,
                || format!("kind-copy-arm({lhs:?},{rhs:?},{bit})"),
                &Bool::or(&[&lend, &equal]),
            );
        }
    }

    /// The derived A12 branch guard, shared by kind coherence and ownership transfer.
    pub(crate) fn lend_guard(&self, lhs: SlotRef, rhs: SlotRef) -> Bool {
        let lhs_vars = self
            .vars
            .get(&lhs)
            .unwrap_or_else(|| panic!("unknown slot: {lhs:?}"));
        let rhs_vars = self
            .vars
            .get(&rhs)
            .unwrap_or_else(|| panic!("unknown slot: {rhs:?}"));
        Bool::and(&[&lhs_vars.ref_, &rhs_vars.own])
    }

    /// §9.10.2 field-ownership constraint: a struct field slot is one crate-wide slot that
    /// (flow-insensitively) holds EVERY value stored into the field. It may be `Owning` — the
    /// rewriter would `Box`/free it — ONLY if every stored value is itself owned; if any store
    /// is a borrowed value the field must not be `Owning` (else it would free borrowed memory
    /// -> UAF). This asserts `field.own <=> AND(rhs.own)` over the field's stores, using BO's
    /// OWN ownership verdict for each `rhs` (so interprocedural / wrapper-returned allocations
    /// and borrowed returns are handled with no syntactic detection). Unlike a plain `equate`
    /// per store, it does NOT transitively equate the stored values to each other, so an owned
    /// source stored in one function does not drag a borrowed value stored in another to
    /// `Owning`. Empty `rhs` is a no-op (an AND over no stores is vacuously true and must not
    /// force `Owning`). Touches only the ownership bit; the borrow reading is left to the
    /// borrow constraints.
    pub(crate) fn constrain_field_own(&self, field: SlotRef, rhs: &[SlotRef]) {
        if rhs.is_empty() {
            return;
        }
        let field_own = &self
            .vars
            .get(&field)
            .unwrap_or_else(|| panic!("unknown slot: {field:?}"))
            .own;
        let rhs_own: Vec<&Bool> = rhs
            .iter()
            .map(|r| {
                &self
                    .vars
                    .get(r)
                    .unwrap_or_else(|| panic!("unknown slot: {r:?}"))
                    .own
            })
            .collect();
        // field.own => rhs_i.own for each store (freeing requires every stored value owned).
        for (slot, r) in rhs.iter().zip(&rhs_own) {
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || format!("field-and({field:?}=>{slot:?})"),
                &Bool::or(&[&!field_own, r]),
            );
        }
        // AND(rhs.own) => field.own : `field.own OR (OR ¬rhs_i.own)`.
        let negs: Vec<Bool> = rhs_own.iter().map(|&r| !r).collect();
        let mut clause: Vec<&Bool> = vec![field_own];
        clause.extend(negs.iter());
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("field-and-rev({field:?})"),
            &Bool::or(&clause),
        );
    }

    /// L01^5 (i): the leak-parity source admission, as an OBJECTIVE term.
    ///
    /// W18 measured the mechanism: bst with its `free`s deleted has NO relax core
    /// at all — nothing forbids `Owning`, the optimizer simply prefers `Ref`,
    /// because `build` weights `ref_` at `big` and `raw` at 1 and gives `own` no
    /// weight, so `Owning` happens only where a hard constraint (a free site)
    /// demands it. A program that never frees therefore never owns.
    ///
    /// Under the leak-parity waiver (USER RULING 2026-08-31) the emitted program
    /// MAY drop what the input leaked, receipted per site. So when the program has
    /// NO sink at all, prefer `Owning` over `Ref` for the FIELD slots — the Box
    /// market — and leave every hard constraint untouched: this changes what the
    /// optimizer picks among models that are already legal, never what is legal.
    pub(crate) fn prefer_owning_for_unsinked_fields(&self, slots: &CrateSlots) {
        let big = self.vars.len() as u64 + 2;
        let mut preferred = 0usize;
        for (slot, kind_vars) in &self.vars {
            if !matches!(slot, SlotRef::Field(_)) {
                continue;
            }
            self.solver.assert_soft(&kind_vars.own, big, None);
            preferred += 1;
        }
        let _ = slots;
        // NOTE: no `ownership_evidence` row — the evidence vocabulary is a
        // validated schema and this is an OBJECTIVE term, not an equation. The
        // waiver receipt the 2026-08-31 ruling requires is an EMISSION-side
        // `waiver-drop(scope-exit)` per site; it is owed by the consumer, and
        // named as owed in report 014.
        if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
            eprintln!(
                "E5C leak-parity: preferred own on {preferred} field slots (no sink in the program)"
            );
        }
    }

    /// **L01⁶ (b)** — the local-slot Owning preference, R517-12.
    ///
    /// A slot the licensing layer has already refused a reference has only
    /// `raw ∨ own` left by the one-hot, and `build` weights `raw` at 1 and gives
    /// `own` NO weight — so it settles `Raw` for want of a preference. This adds
    /// a soft `own` at weight 2: strictly above `raw`'s 1, and far below
    /// `ref_`'s `vars.len() + 1`, so it can never displace a reference anywhere
    /// and never makes an illegal model legal. Purely objective, like
    /// `prefer_owning_for_unsinked_fields`, and unlike that one it carries no
    /// program-wide sink premise -- the caller supplies exactly the slots whose
    /// reference was already refused.
    ///
    /// Era-5c report 034b priced the market before this was built: `own` is SAT
    /// for **77 of 462** measured subjects and for **7 of the 55** CROWN Box
    /// units, so this moves those and provably nothing else. The other 385 are
    /// refused by hard constraints no objective term reaches.
    pub(crate) fn prefer_owning_for_refused_reference(&self, slot: SlotRef) -> bool {
        let Some(kind_vars) = self.vars.get(&slot) else {
            return false;
        };
        self.solver.assert_soft(&kind_vars.own, 2u64, None);
        true
    }

    /// **L01⁶ arm 3, half two** (R518-2) — seat ownership on the NAMED local.
    ///
    /// Weight 3: above L01⁶ (b)'s 2 so a named local outranks an anonymous one,
    /// and still far below `ref_`'s `vars.len() + 1` so no reference is ever
    /// displaced. Without this, dropping the finalization blanket lets the
    /// optimum park the ownership token on a temporary — report 034 §1 measured
    /// that as `0/13/31 → 28/8/8`.
    pub(crate) fn prefer_owning_for_named_local(&self, slot: SlotRef) -> bool {
        let Some(kind_vars) = self.vars.get(&slot) else {
            return false;
        };
        self.solver.assert_soft(&kind_vars.own, 3u64, None);
        true
    }

    /// §9.10.2 companion to `constrain_field_own`: hard-assert a field slot is NOT `Owning`.
    /// Used when a field receives a value that is definitely not an owned heap allocation — an
    /// address-of (`Ref`/`RawPtr`) store, or a store whose RHS cannot be resolved to a slot
    /// (so its ownership is unknown). Such a store means the field can hold non-owned memory,
    /// so it must never be `Owning` (freeing it would be UAF). Conservative and sound: an
    /// unresolved/address store BLOCKS ownership rather than being silently dropped from the
    /// `AND` (which would wrongly permit `Owning`).
    pub(crate) fn forbid_field_own(&self, field: SlotRef) {
        let vars = self
            .vars
            .get(&field)
            .unwrap_or_else(|| panic!("unknown slot: {field:?}"));
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("field-forbid({field:?})"),
            &!&vars.own,
        );
    }

    /// era-5c R545-2: the formal analogue of `forbid_field_own`. A formal whose
    /// every closed-world actual is the address of a stack place or of an
    /// interior place (`mod.rs::lend_formals`) holds memory some other object
    /// owns -- freeing it is UB on a UB-free input -- so it is a LEND and must
    /// never be `Owning`. Returns whether the slot exists.
    pub(crate) fn forbid_lend_formal_own(&self, formal: SlotRef) -> bool {
        let Some(vars) = self.vars.get(&formal) else {
            return false;
        };
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("lend-formal-forbid({formal:?})"),
            &!&vars.own,
        );
        true
    }

    /// A14 field ref-worthiness: a field may be Ref only when every non-null stored value is safe
    /// (Ref or Owning). Null is handled orthogonally by §29; Raw is the only disqualifying kind.
    pub(crate) fn constrain_field_ref(&self, field: SlotRef, rhs: &[SlotRef]) {
        let field_ref = &self
            .vars
            .get(&field)
            .unwrap_or_else(|| panic!("unknown slot: {field:?}"))
            .ref_;
        for &source in rhs {
            let source_raw = &self
                .vars
                .get(&source)
                .unwrap_or_else(|| panic!("unknown slot: {source:?}"))
                .raw;
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || format!("field-ref-source({field:?}=>{source:?})"),
                &Bool::or(&[&!field_ref, &!source_raw]),
            );
        }
    }

    pub(crate) fn forbid_field_ref(&self, field: SlotRef) {
        let field_ref = &self
            .vars
            .get(&field)
            .unwrap_or_else(|| panic!("unknown slot: {field:?}"))
            .ref_;
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("field-ref-forbid({field:?})"),
            &!field_ref,
        );
    }

    /// A16-REFINE: a caller may be Ref only if the modeled-origin callee
    /// return is not Raw. This is deliberately one-way: it can demote the
    /// caller, never license Ref from the callee.
    pub(crate) fn constrain_origin_return_ref(&self, caller: SlotRef, callee: SlotRef) {
        let caller_ref = &self
            .vars
            .get(&caller)
            .unwrap_or_else(|| panic!("unknown caller slot: {caller:?}"))
            .ref_;
        let callee_raw = &self
            .vars
            .get(&callee)
            .unwrap_or_else(|| panic!("unknown callee slot: {callee:?}"))
            .raw;
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("return-ref-origin({caller:?}=>{callee:?})"),
            &Bool::or(&[&!caller_ref, &!callee_raw]),
        );
    }

    /// Solidification link: tie a slot's `own` one-hot bit to an external Bool
    /// (the disjunction of the slot's per-version ownership Bools). Mirrors the
    /// biconditional idiom in `equate`.
    pub(crate) fn link_own(&self, slot: SlotRef, external: &Bool) {
        let vars = self
            .vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("link-own({slot:?})"),
            &!vars.own.xor(external),
        );
    }

    /// F02: only an exact statically eligible occurrence may use this guard.
    /// Its false arm retains every ordinary kind equality.
    pub(crate) fn field_reader_or_equate(&self, lhs: SlotRef, rhs: SlotRef, reader: &Bool) {
        let a = &self.vars[&lhs];
        let b = &self.vars[&rhs];
        for (left, right, kind) in [
            (&a.raw, &b.raw, "raw"),
            (&a.ref_, &b.ref_, "ref"),
            (&a.own, &b.own, "own"),
        ] {
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || format!("field-reader-kind({lhs:?},{rhs:?},{kind})"),
                &Bool::or(&[reader, &!left.xor(right)]),
            );
        }
    }

    /// L01^5 (ii): the field↔field strong-update MOVE. Where `field_moves` proves
    /// the loaded place is overwritten on every path before any read of it, the
    /// crate-wide field slot cannot still be observed holding the moved value, so
    /// the kind equality between the loading local and the field slot is RELEASED
    /// — the same shape as `field_reader_or_equate`, with a must-overwrite guard
    /// instead of a reader effect. It asserts no kind: the local's own bit is then
    /// settled by the source token's flow and the store-side AND coupling, and the
    /// drop policy (R395-2: drops only at C free sites) is untouched.
    pub(crate) fn field_move_or_equate(&self, lhs: SlotRef, rhs: SlotRef) {
        let a = &self.vars[&lhs];
        let b = &self.vars[&rhs];
        // The RAW and REF bits still agree: a moved value has the same surface
        // form as the field it came out of. Only the OWN bit is released, which
        // is the one the crate-wide field slot cannot carry for a moved token.
        for (left, right, kind) in [(&a.raw, &b.raw, "raw"), (&a.ref_, &b.ref_, "ref")] {
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || format!("field-move-kind({lhs:?},{rhs:?},{kind})"),
                &!left.xor(right),
            );
        }
        super::ownership_evidence::record("field-move-release", &[], None, None);
        if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
            eprintln!("E5C field-move-release {lhs:?} <- {rhs:?} (own equality released)");
        }
    }

    pub(crate) fn reference_field_reader_or_equate(
        &self,
        lhs: SlotRef,
        rhs: SlotRef,
        effect: &Bool,
    ) {
        self.field_reader_or_equate(lhs, rhs, effect);
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("field-reader-kind-reference-effect({lhs:?},{rhs:?})"),
            &effect.implies(&self.lend_guard(lhs, rhs)),
        );
    }

    pub(crate) fn block_field_reader(&self, lhs: SlotRef, rhs: SlotRef) {
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("field-reader-kind-incomplete({lhs:?},{rhs:?})"),
            &!self.lend_guard(lhs, rhs),
        );
    }

    fn all_field_store_support(
        &self,
        facts: &super::licensing::facts::Facts,
        field: &super::licensing::field_support::FieldProof,
    ) -> anyhow::Result<Bool> {
        let own = |node: super::licensing::transport::Node| -> anyhow::Result<Bool> {
            anyhow::ensure!(
                facts.constructions == 1 && node.construction == 0,
                "field store construction mismatch"
            );
            facts
                .ownership_asts
                .get(Var::from_u32(node.var))
                .cloned()
                .ok_or_else(|| anyhow::anyhow!("field store ownership AST missing"))
        };
        let guards = |dependencies: &std::collections::BTreeMap<
            super::licensing::facts::EquationId,
            bool,
        >|
         -> anyhow::Result<Vec<Bool>> {
            dependencies
                .iter()
                .map(|(key, positive)| {
                    let predicate = &facts
                        .guards
                        .iter()
                        .find(|binding| binding.equation == *key)
                        .ok_or_else(|| anyhow::anyhow!("field store endpoint dependency missing"))?
                        .predicate;
                    Ok(if *positive {
                        predicate.clone()
                    } else {
                        !predicate
                    })
                })
                .collect()
        };
        let mut support = Vec::new();
        for store in &field.stores {
            support.push(own(store.destination_def)?);
            support.push(!own(store.source_def)?);
            support.extend(guards(&store.meet.guards)?);
        }
        for store in &field.input_stores {
            support.push(own(store.destination_def)?);
            support.push(!own(store.source_def)?);
            // Every expected caller needs one complete compatible alternative.
            for application in &store.applications {
                let mut alternatives = Vec::new();
                for alternative in &application.alternatives {
                    let mut required = vec![own(alternative.route.actual_input)?];
                    required.extend(guards(&alternative.route.guards)?);
                    required.extend(guards(&alternative.free.guards)?);
                    required.extend(guards(&alternative.forwarded.output.guards)?);
                    for forwarded in &alternative.forwarded_returns {
                        required.extend(guards(&forwarded.guards)?);
                    }
                    if !alternative.pending_outputs.is_empty() {
                        required.push(Bool::from_bool(false));
                    }
                    alternatives.push(Bool::and(&required));
                }
                support.push(Bool::or(&alternatives));
            }
            // No new input-store permission is enabled by this conditional
            // record. Compiler caller completeness and attestation remain due.
            match store.caller_coverage {
                super::licensing::field_support::CallerCoverage::PendingCompilerAndAttestation => {
                    support.push(Bool::from_bool(false))
                }
                super::licensing::field_support::CallerCoverage::CertifiedFirst
                | super::licensing::field_support::CallerCoverage::CertifiedChain => {
                    support.push(Bool::from_bool(facts.frame_attested))
                }
            }
        }
        anyhow::ensure!(
            !support.is_empty(),
            "empty field support cannot license an owner"
        );
        Ok(Bool::and(&support))
    }

    /// Necessary local G-FOLD premises only. Caller alias, all-store and
    /// source-flow closure remain separate; this does not activate transport.
    pub(crate) fn constrain_fold_permission(
        &self,
        facts: &super::licensing::facts::Facts,
        proof: &super::licensing::fold_call::Proof,
        guard: &Bool,
    ) -> anyhow::Result<()> {
        let requirements = super::licensing::fold_permission::requirements(facts, proof)
            .map_err(anyhow::Error::msg)?;
        let support = self.fold_requirement_support(facts, &requirements)?;
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("own-fold-permission({:?},{})", proof.call, proof.boundary),
            &guard.implies(&support),
        );
        Ok(())
    }

    fn fold_requirement_support(
        &self,
        facts: &super::licensing::facts::Facts,
        requirements: &super::licensing::fold_permission::Requirements,
    ) -> anyhow::Result<Bool> {
        anyhow::ensure!(
            facts.constructions == 1
                && requirements
                    .owning
                    .iter()
                    .chain(&requirements.zero)
                    .all(|node| node.construction == 0),
            "fold requirement construction differs"
        );
        let mut support = vec![Bool::from_bool(
            facts.frame_attested
                && super::licensing::stack_entry::current_world()
                    == super::licensing::stack_entry::CallWorld::ClosedProgram,
        )];
        for key in &requirements.kind_keys {
            let slot = facts
                .slot_refs
                .get(key)
                .ok_or_else(|| anyhow::anyhow!("fold kind slot missing"))?;
            support.push(
                self.vars
                    .get(slot)
                    .ok_or_else(|| anyhow::anyhow!("fold solver kind missing"))?
                    .own
                    .clone(),
            );
        }
        for (nodes, positive) in [(&requirements.owning, true), (&requirements.zero, false)] {
            for node in nodes {
                let rho = facts
                    .ownership_asts
                    .get(Var::from_u32(node.var))
                    .ok_or_else(|| anyhow::anyhow!("fold ownership AST missing"))?;
                support.push(if positive { rho.clone() } else { !rho });
            }
        }
        for (key, positive) in &requirements.guards {
            let predicate = &facts
                .guards
                .iter()
                .find(|g| g.equation == *key)
                .ok_or_else(|| anyhow::anyhow!("fold endpoint/guard AST missing"))?
                .predicate;
            support.push(if *positive {
                predicate.clone()
            } else {
                !predicate
            });
        }
        Ok(Bool::and(&support))
    }

    /// Final disposition follows complete current/frozen caller certification.
    /// Every original SSA equation, old/final-zero and field rule remains.
    pub(crate) fn constrain_fold_callers(
        &self,
        facts: &super::licensing::facts::Facts,
    ) -> anyhow::Result<()> {
        let frozen = facts
            .licensing
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("fold caller facts missing"))?;
        super::licensing::fold_declaration::validate(
            facts,
            &super::licensing::matched::guard_aliases(&facts.guards),
        )
        .map_err(anyhow::Error::msg)?;
        let current = super::licensing::fold_eligibility::plan(facts);
        anyhow::ensure!(
            current == frozen.fold_callers,
            "fold caller preflight differs"
        );
        let members = super::licensing::fold_eligibility::member_plan(facts);
        anyhow::ensure!(
            members == frozen.fold_members,
            "fold member preflight differs"
        );
        let mut clauses = Vec::new();
        for row in current.as_deref().unwrap_or_default() {
            let key = row.declaration.guard;
            let binding = |key| -> anyhow::Result<Bool> {
                let rows: Vec<_> = facts.guards.iter().filter(|g| g.equation == key).collect();
                let [row] = rows.as_slice() else {
                    anyhow::bail!("fold caller predicate missing or ambiguous")
                };
                Ok(row.predicate.clone())
            };
            let guard = binding(key)?;
            let closed = facts.frame_attested
                && super::licensing::stack_entry::current_world()
                    == super::licensing::stack_entry::CallWorld::ClosedProgram;
            // A used-child declaration is activated by its member certificate
            // instead, on the same closed-frame premise and the same two
            // clauses. Its parent free is the callee's, so its endpoint account
            // is the caller's own, carried on the certificate.
            let member = members
                .as_deref()
                .unwrap_or_default()
                .iter()
                .filter(|row| row.declaration.guard == key)
                .find_map(|row| row.outcome.as_ref().ok());
            if closed && let Ok(proof) = &row.outcome {
                anyhow::ensure!(
                    proof.required_closed_frame,
                    "fold caller frame premise missing"
                );
                let support = self.fold_requirement_support(facts, &proof.requirements)?;
                clauses.push((
                    format!("own-fold-caller-permission({key:?})"),
                    guard.implies(&support),
                ));
                // The exact four original endpoints select the one obligation;
                // the antecedent deliberately excludes the fold guard itself.
                let endpoints = [
                    proof.payload.source.endpoint,
                    proof.payload.free,
                    proof.container.source.endpoint,
                    proof.container.free,
                ];
                let predicates = endpoints
                    .into_iter()
                    .map(binding)
                    .collect::<anyhow::Result<Vec<_>>>()?;
                clauses.push((
                    format!("own-fold-caller-endpoints({key:?})"),
                    Bool::and(&predicates).implies(&guard),
                ));
            } else if closed && let Some(proof) = member {
                anyhow::ensure!(
                    proof.required_closed_frame,
                    "fold member frame premise missing"
                );
                let support = self.fold_requirement_support(facts, &proof.requirements)?;
                clauses.push((
                    format!("own-fold-member-permission({key:?})"),
                    guard.implies(&support),
                ));
                let predicates = proof
                    .endpoints
                    .iter()
                    .copied()
                    .map(&binding)
                    .collect::<anyhow::Result<Vec<_>>>()?;
                clauses.push((
                    format!("own-fold-member-endpoints({key:?})"),
                    Bool::and(&predicates).implies(&guard),
                ));
            } else {
                clauses.push((format!("own-fold-pending({key:?})"), !guard));
            }
        }
        for (label, clause) in clauses {
            assert_hard(&self.solver, self.tracker.as_ref(), || label, &clause);
        }
        Ok(())
    }

    pub(crate) fn constrain_first_permissions(
        &self,
        facts: &super::licensing::facts::Facts,
    ) -> anyhow::Result<()> {
        let frozen = facts
            .licensing
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("first-permission facts missing"))?;
        let current_matched = super::licensing::matched::MatchedTransport::build(facts);
        let current_origins = super::licensing::value_origins::ValueOrigins::build(facts);
        let mut fields = super::licensing::field_support::audit(
            facts,
            &facts.field_support_inputs,
            &current_matched,
            &current_origins,
        );
        let checked = super::licensing::first_permission::plan(
            facts,
            &mut fields,
            current_matched.guard_aliases(),
        );
        anyhow::ensure!(
            checked == frozen.first_permissions && fields == frozen.field_support,
            "first-permission preflight differs"
        );
        let mut clauses = Vec::new();
        for decision in &checked {
            let guard = &facts
                .guards
                .iter()
                .find(|g| g.equation == decision.guard)
                .ok_or_else(|| anyhow::anyhow!("first-permission guard missing"))?
                .predicate;
            let permitted = facts.frame_attested
                && super::licensing::stack_entry::current_world()
                    == super::licensing::stack_entry::CallWorld::ClosedProgram;
            if permitted && let Some(proof) = &decision.proof {
                let field = fields
                    .iter()
                    .find(|f| f.field_key == proof.candidate.field_key && f.supported())
                    .ok_or_else(|| anyhow::anyhow!("first-permission all-store proof missing"))?;
                let cell = facts
                    .slot_refs
                    .get(&proof.parameter_slot)
                    .ok_or_else(|| anyhow::anyhow!("first-permission outer slot missing"))?;
                let field_slot = facts
                    .slot_refs
                    .get(&proof.candidate.field_key)
                    .ok_or_else(|| anyhow::anyhow!("first-permission field slot missing"))?;
                let support = Bool::and(&[
                    self.vars[cell].ref_.clone(),
                    self.vars[field_slot].own.clone(),
                    self.all_field_store_support(facts, field)?,
                ]);
                clauses.push((decision.guard, true, guard.implies(&support)));
            } else if permitted && let Some(chain) = &decision.complete_chain {
                let field = fields
                    .iter()
                    .find(|field| field.field_key == chain.put.field_key && field.supported())
                    .ok_or_else(|| anyhow::anyhow!("complete-chain all-store proof missing"))?;
                anyhow::ensure!(
                    super::licensing::chain_permission::certify(
                        facts,
                        field,
                        current_matched.guard_aliases()
                    )
                    .as_ref()
                        == Some(chain.as_ref()),
                    "complete-chain current proof differs"
                );
                let field_slot = facts
                    .slot_refs
                    .get(&chain.put.field_key)
                    .ok_or_else(|| anyhow::anyhow!("complete-chain field slot missing"))?;
                let mut support = vec![
                    self.vars[field_slot].own.clone(),
                    self.all_field_store_support(facts, field)?,
                ];
                for call in &chain.effects.calls {
                    if call.callee == chain.put.call.callee
                        || call.callee == chain.release.call.callee
                        || call.caller == chain.release.call.callee
                    {
                        let argument = if call == &chain.put.call {
                            chain.put.argument
                        } else if call == &chain.release.call {
                            chain.release.argument
                        } else {
                            0
                        };
                        let boundary = facts
                            .boundary_substitutions
                            .iter()
                            .find(|b| {
                                b.point.construction == call.construction
                                    && b.point.function.as_ref() == Some(&call.caller)
                                    && b.point.block == Some(call.block)
                                    && b.point.statement == Some(call.statement)
                                    && b.callee.as_ref() == Some(&call.callee)
                                    && b.role == super::ownership_boundary::Role::CallArgument
                                    && b.argument_index == Some(argument)
                            })
                            .ok_or_else(|| {
                                anyhow::anyhow!("complete-chain parent boundary missing")
                            })?;
                        let key = format!(
                            "{}::_{}@d0",
                            call.callee,
                            boundary.formal_local.ok_or_else(|| anyhow::anyhow!(
                                "complete-chain parent local missing"
                            ))?
                        );
                        let slot = facts
                            .slot_refs
                            .get(&key)
                            .ok_or_else(|| anyhow::anyhow!("complete-chain parent slot missing"))?;
                        support.push(self.vars[slot].ref_.clone());
                    }
                }
                clauses.push((decision.guard, true, guard.implies(&Bool::and(&support))));
            } else {
                clauses.push((decision.guard, false, !guard));
            }
        }
        for (id, permitted, clause) in clauses {
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || format!("own-original-cell-disposition({id:?},{permitted})"),
                &clause,
            );
        }
        Ok(())
    }

    /// era-5c (R409-1): the allocator-contract pairing refusal — the sink's
    /// argument is assumed non-owning under the family
    /// `allocator-contract-pairing`, so the sink's selector is leaked (the free
    /// stays a raw-pointer free) and the pointer stays raw rather than being
    /// released through the wrong allocator.
    pub(crate) fn constrain_allocator_contract_pairing(
        &self,
        facts: &super::licensing::facts::Facts,
    ) {
        use super::allocator_contract::{self, AllocatorClass};
        let misusing = allocator_contract::misusing_functions(facts);
        for port in allocator_contract::ports() {
            let open = !misusing.contains(&port.function);
            if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                eprintln!("E5C contract-port {} open={open}", port.function);
            }
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || {
                    if open {
                        format!("allocator-contract-port-open({})", port.function)
                    } else {
                        format!("allocator-contract-pairing(port closed: {})", port.function)
                    }
                },
                &if open {
                    port.guard.clone()
                } else {
                    !&port.guard
                },
            );
        }
        // Both directions refuse the sink's argument; a libc release of a
        // contract allocation additionally closed the caller's ports above, so
        // the refusal is satisfiable without leaking the producer's source.
        for refusal in allocator_contract::pairing_refusals(facts) {
            let _: AllocatorClass = refusal.sink_class;
            if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                eprintln!(
                    "E5C pairing-refusal var={:?} {}",
                    refusal.var, refusal.label
                );
            }
            let x = &facts.ownership_asts[refusal.var];
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || refusal.label.clone(),
                &!x,
            );
        }
    }

    /// Complete traversal calls are borrowed only under the explicit closed
    /// frame and ordinary native replay. Unqualified declarations remain false.
    pub(crate) fn constrain_traversal_calls(
        &self,
        facts: &super::licensing::facts::Facts,
    ) -> anyhow::Result<()> {
        use std::collections::BTreeSet;

        use super::licensing::{facts::EquationId, traversal_call, traversal_correspondence};
        let frozen = facts
            .licensing
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("traversal facts absent"))?;
        let candidates = traversal_call::discover(facts);
        let proofs: Vec<_> = candidates
            .iter()
            .map(|c| traversal_correspondence::certify(facts, c))
            .collect();
        anyhow::ensure!(
            candidates == frozen.traversal_calls && proofs == frozen.traversal_correspondences,
            "traversal preflight differs from frozen evidence"
        );
        let world = facts.frame_attested
            && super::licensing::stack_entry::current_world()
                == super::licensing::stack_entry::CallWorld::ClosedProgram
            && super::licensing::caller_coverage::assess(facts)
                == super::licensing::caller_coverage::Status::Complete;
        let predicate = |id| {
            facts
                .guards
                .iter()
                .find(|g| g.equation == id)
                .map(|g| g.predicate.clone())
                .ok_or_else(|| anyhow::anyhow!("traversal predicate missing"))
        };
        let mut clauses = Vec::new();
        for declaration in facts
            .equations
            .iter()
            .filter(|e| e.operation == "guarded-traversal-call")
        {
            let id = EquationId {
                construction: declaration.point.construction,
                ordinal: declaration.ordinal,
            };
            let guard = predicate(id)?;
            let support = (|| -> Result<Bool, &'static str> {
                if !world {
                    return Err("world-not-closed");
                }
                let index = candidates
                    .iter()
                    .position(|c| c.guard == id)
                    .ok_or("candidate-missing")?;
                let callee = &candidates[index].call.callee;
                let expected: BTreeSet<_> = facts
                    .caller_coverage
                    .as_ref()
                    .ok_or("caller-coverage-absent")?
                    .local_calls
                    .iter()
                    .filter(|c| &c.target == callee)
                    .map(|c| (c.site.function.clone(), c.site.block, c.site.statement))
                    .collect();
                let group: Vec<_> = candidates
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| &c.call.callee == callee)
                    .collect();
                let observed: BTreeSet<_> = group
                    .iter()
                    .map(|(_, c)| (c.call.caller.clone(), c.call.block, c.call.statement))
                    .collect();
                if expected.is_empty() || observed != expected || group.len() != expected.len() {
                    return Err("caller-coverage-mismatch");
                }
                let mut requirements = Vec::new();
                for (index, candidate) in group {
                    let proof = proofs[index]
                        .as_ref()
                        .ok()
                        .ok_or("correspondence-refused")?;
                    let arg = facts
                        .boundary_substitutions
                        .iter()
                        .find(|b| {
                            b.point.construction == candidate.call.construction
                                && b.ordinal == candidate.argument_boundary
                        })
                        .ok_or("argument-boundary-missing")?;
                    let ret = facts
                        .boundary_substitutions
                        .iter()
                        .find(|b| {
                            b.point.construction == candidate.call.construction
                                && b.ordinal == candidate.receiver_boundary
                        })
                        .ok_or("receiver-boundary-missing")?;
                    // era-5c (E5C-2): a formal component the actual's window does
                    // not reach (the callee's `node->left` when the caller tracks
                    // `root->right` one level deep) is admissible under the arm
                    // when the licence's own `formal-zero` row covers it — the
                    // callee sees a view whose every component is non-owning,
                    // and the caller's frame keeps its tokens. Unmatched ACTUAL
                    // components and the receiver stay refused.
                    let formal_zero_covers = |var: &u32| {
                        super::null_paths::move_tracking()
                            && facts.equations.iter().any(|e| {
                                e.operation == "guarded-traversal-formal-zero"
                                    && e.guard.is_some()
                                    && e.guard == declaration.guard
                                    && e.variables == [*var]
                            })
                    };
                    if !arg.unmatched_actual_vars.is_empty()
                        || !ret.unmatched_actual_vars.is_empty()
                        || !ret.unmatched_formal_vars.is_empty()
                    {
                        return Err("boundary-unmatched-vars");
                    }
                    if !arg.unmatched_formal_vars.iter().all(formal_zero_covers) {
                        return Err("argument-formal-unmatched");
                    }
                    let target =
                        traversal_call::input_target(facts, proof).ok_or("input-target-missing")?;
                    let input = facts
                        .slot_refs
                        .get(&target.kind_key)
                        .ok_or("input-slot-missing")?;
                    requirements.push(!&self.vars[input].raw);
                    if let Some(parent) = &target.parent_key {
                        requirements.push(
                            !&self.vars
                                [facts.slot_refs.get(parent).ok_or("parent-slot-missing")?]
                            .raw,
                        );
                    }
                    for key in [
                        format!("{}::_{}@d0", callee, candidate.parameter),
                        format!("{}::_0@d0", callee),
                        format!(
                            "{}::_{}@d0",
                            candidate.call.caller, proof.native.receiver.local
                        ),
                    ] {
                        requirements.push(
                            self.vars[facts.slot_refs.get(&key).ok_or("interface-slot-missing")?]
                                .ref_
                                .clone(),
                        );
                    }
                    requirements.push(predicate(candidate.guard).ok().ok_or("guard-missing")?);
                    for reader_id in &proof.traversal.readers {
                        let equation = facts
                            .equations
                            .iter()
                            .find(|e| {
                                e.point.construction == reader_id.construction
                                    && e.ordinal == reader_id.ordinal
                            })
                            .ok_or("reader-equation-missing")?;
                        let reader = facts
                            .reader_plan
                            .candidates
                            .iter()
                            .find(|r| {
                                r.function == *callee
                                    && Some(r.block) == equation.point.block
                                    && Some(r.statement) == equation.point.statement
                            })
                            .ok_or("reader-candidate-missing")?;
                        let field = facts
                            .slot_refs
                            .get(&reader.field_key)
                            .ok_or("reader-field-slot-missing")?;
                        requirements.push(!&self.vars[field].raw);
                        requirements.push(
                            self.vars[field].own.implies(
                                &predicate(*reader_id).ok().ok_or("reader-guard-missing")?,
                            ),
                        );
                    }
                }
                Ok(Bool::and(&requirements))
            })();
            // era-5c: a pending traversal names its reason when asked.
            if let Err(reason) = &support
                && std::env::var_os("CRAT_ERA5C_DEBUG").is_some()
            {
                eprintln!("E5C traversal-pending {id:?} reason={reason}");
            }
            let licensed = support.is_ok();
            clauses.push((
                id,
                licensed,
                match support {
                    Ok(s) => guard.implies(&s),
                    Err(_) => !guard,
                },
            ));
        }
        for (id, licensed, clause) in clauses {
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || {
                    if licensed {
                        format!("own-traversal-license({id:?})")
                    } else {
                        "own-traversal-pending".into()
                    }
                },
                &clause,
            );
        }
        Ok(())
    }

    /// Permission is conditional on complete store/source/free evidence. Missing
    /// roles retain the original borrow/frame; replay checks selected Ref views.
    pub(crate) fn constrain_reference_field_effects(
        &self,
        facts: &super::licensing::facts::Facts,
    ) -> anyhow::Result<()> {
        use super::licensing::matched::{SourceLineage, TerminalTarget};
        let frozen = facts
            .licensing
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("reference-effect facts missing"))?;
        let actual_graph = super::licensing::transport::CandidateGraph::build(facts);
        let aliases = super::licensing::matched::guard_aliases(&facts.guards);
        let mut clauses = Vec::new();
        for row in facts
            .equations
            .iter()
            .filter(|row| row.operation == "guarded-reference-field")
        {
            let key = super::licensing::facts::EquationId {
                construction: row.point.construction,
                ordinal: row.ordinal,
            };
            let guard = facts
                .guards
                .iter()
                .find(|binding| binding.equation == key)
                .ok_or_else(|| anyhow::anyhow!("missing reference-effect guard"))?;
            let candidates: Vec<_> = frozen
                .reference_effects
                .candidates
                .iter()
                .filter(|candidate| {
                    row.point == candidate.formation
                        && row.variables
                            == [
                                candidate.payload_before.var,
                                candidate.cell_after.var,
                                candidate.cell_before.var,
                            ]
                })
                .collect();
            let support = (|| -> anyhow::Result<Option<Bool>> {
                let [candidate] = candidates.as_slice() else { return Ok(None) };
                // This edge requires all five actual obligations under the
                // same predicate; cached support cannot replace a missing law.
                if !actual_graph.edges.iter().any(|edge| {
                    edge.from == candidate.cell_before
                        && edge.to == candidate.payload_before
                        && edge.evidence
                            == super::licensing::transport::Evidence::ReferenceEffect(key)
                        && edge.guard.is_some_and(|guard| {
                            guard.required && aliases.get(&key) == Some(&guard.binding)
                        })
                }) {
                    return Ok(None);
                }
                let Some(field) = frozen
                    .field_support
                    .iter()
                    .find(|field| field.field_key == candidate.field_key && field.supported())
                else {
                    return Ok(None);
                };
                let stores: Vec<_> = field
                    .stores
                    .iter()
                    .filter(|store| {
                        store.site.function == candidate.function
                            && store.site.place.local == candidate.cell_place.local
                            && store.destination_def == candidate.scalar_before
                    })
                    .collect();
                let [store] = stores.as_slice() else { return Ok(None) };
                if store.meet.terminal.target != TerminalTarget::Free(candidate.free)
                    || store.meet.terminal.lineage
                        != SourceLineage::Exact(vec![candidate.call.clone()])
                    || !store.discharged_outputs.iter().any(|discharge| {
                        discharge.certificate.call == candidate.call
                            && discharge.certificate.actual_output == candidate.payload_after
                            && discharge.certificate.free == store.meet.terminal
                    })
                {
                    return Ok(None);
                }
                let Some(view) = facts.consumes.iter().find(|consume| {
                    consume.point.construction == candidate.construction
                        && consume.ordinal == candidate.scalar_view_consume
                }) else {
                    return Ok(None);
                };
                let Some(boundary) = facts.boundary_substitutions.iter().find(|boundary| {
                    boundary.point.construction == candidate.construction
                        && boundary.ordinal == candidate.boundary
                }) else {
                    return Ok(None);
                };
                let Some(formal) = boundary.formal_local else { return Ok(None) };
                let view_key = format!("{}::_{}@d0", candidate.function, view.local);
                let callee_key = format!("{}::_{}@d0", candidate.call.callee, formal);
                let (Some(view), Some(field_slot), Some(callee)) = (
                    facts.slot_refs.get(&view_key),
                    facts.slot_refs.get(&candidate.field_key),
                    facts.slot_refs.get(&callee_key),
                ) else {
                    return Ok(None);
                };
                let mut required = vec![
                    self.vars[view].ref_.clone(),
                    self.vars[field_slot].own.clone(),
                    self.vars[callee].ref_.clone(),
                ];
                required.push(self.all_field_store_support(facts, field)?);
                Ok(Some(Bool::and(&required)))
            })()?;
            clauses.push(match support {
                Some(support) => (
                    "own-reference-effect-permission",
                    guard.predicate.implies(&support),
                ),
                None => ("own-reference-effect-pending", !guard.predicate.clone()),
            });
        }
        for (label, clause) in clauses {
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || label.into(),
                &clause,
            );
        }
        Ok(())
    }

    /// An Owning declaration cannot substitute for a token in each stored
    /// occurrence. Only the new reader alternative consumes this certificate;
    /// unsupported roles retain the pre-existing transfer constraints.
    pub(crate) fn constrain_reader_field_support(
        &self,
        facts: &super::licensing::facts::Facts,
    ) -> anyhow::Result<()> {
        let frozen = facts
            .licensing
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("missing field support facts"))?;
        let mut clauses = Vec::new();
        for candidate in &frozen.reader_candidates {
            let key = format!(
                "{}::_{}@d0",
                candidate.function, candidate.destination.local
            );
            let (Some(&lhs), Some(&rhs)) = (
                facts.slot_refs.get(&key),
                facts.slot_refs.get(&candidate.field_key),
            ) else {
                continue;
            };
            let reader = self.lend_guard(lhs, rhs);
            // R388-1: under the arm, a field whose only holds are classified
            // store sources is supported CONDITIONALLY — the condition being the
            // conjunction those sources name. `reader => support` is unchanged;
            // what changes is that `support` can be a formula instead of a
            // pre-solve boolean.
            if super::licensing::facts::interface_own()
                && let Some(proof) = frozen
                    .field_support
                    .iter()
                    .find(|proof| proof.field_key == candidate.field_key && !proof.supported())
                && let Some(support) = self.classified_store_support(facts, proof)?
            {
                clauses.push((
                    format!(
                        "field-reader-support-classified({key},{})",
                        candidate.field_key
                    ),
                    reader.implies(&support),
                ));
                continue;
            }
            let Some(proof) = frozen
                .field_support
                .iter()
                .find(|proof| proof.field_key == candidate.field_key && proof.supported())
            else {
                clauses.push((
                    format!("field-reader-support-held({key},{})", candidate.field_key),
                    !reader,
                ));
                continue;
            };
            let support = self.all_field_store_support(facts, proof)?;
            clauses.push((
                format!("field-reader-support-owned({key},{})", candidate.field_key),
                reader.implies(&support),
            ));
        }
        for (label, clause) in clauses {
            assert_hard(&self.solver, self.tracker.as_ref(), || label, &clause);
        }
        Ok(())
    }

    /// R388-1: the conjunction a field's classified store sources name. `None`
    /// when the field carries a hold the classification does not cover — avl's
    /// `TerminalRoleC` and `CallerCoverageC` are exactly that — so those fields
    /// keep the pre-solve refusal and their readers stay held.
    fn classified_store_support(
        &self,
        facts: &super::licensing::facts::Facts,
        proof: &super::licensing::field_support::FieldProof,
    ) -> anyhow::Result<Option<Bool>> {
        use super::licensing::field_support::{Pending, StoreSourceOrigin};
        if proof.classified.is_empty() {
            return Ok(None);
        }
        // Every hold must be either a store this pass classified, or the
        // `EmptyOwnedSupport` that follows from them. Anything else is a premise
        // the classification does not speak to.
        let covered = proof.holds.iter().all(|hold| {
            hold.reason == Pending::EmptyOwnedSupport
                || (hold.reason == Pending::OwnedInputOrOriginC
                    && hold.site.as_ref().is_some_and(|site| {
                        proof.classified.iter().any(|store| &store.site == site)
                    }))
        });
        if !covered {
            return Ok(None);
        }
        let mut conjuncts: Vec<Bool> = Vec::new();
        for store in &proof.classified {
            match &store.origin {
                StoreSourceOrigin::Fresh | StoreSourceOrigin::Null => {}
                StoreSourceOrigin::Input(key) | StoreSourceOrigin::FieldToken(key) => {
                    let Some(&slot) = facts.slot_refs.get(key) else {
                        return Ok(None);
                    };
                    conjuncts.push(self.vars[&slot].own.clone());
                }
                StoreSourceOrigin::Unknown => return Ok(None),
            }
        }
        let refs: Vec<&Bool> = conjuncts.iter().collect();
        Ok(Some(if refs.is_empty() {
            Bool::from_bool(true)
        } else {
            Bool::and(&refs)
        }))
    }

    /// Checked O-OWN grants add responsibility through the mandatory mirror.
    /// Eligibility changes no objective weight and relaxes no SSA law.
    pub(crate) fn apply_licensing_grants(
        &self,
        facts: &super::licensing::facts::Facts,
    ) -> anyhow::Result<usize> {
        let frozen = facts
            .licensing
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("missing frozen licensing facts"))?;
        let mut resolved = Vec::new();
        for grant in &frozen.objective_grants {
            anyhow::ensure!(
                grant.discharged_gates == super::licensing::grants::HardGate::ALL,
                "grant has an incomplete or duplicated hard-gate proof inventory"
            );
            anyhow::ensure!(
                grant.carrier.construction == 0 && facts.constructions == 1,
                "grant AST must belong to this construction"
            );
            anyhow::ensure!(
                facts
                    .slot_refs
                    .get(&grant.slot_key)
                    .is_some_and(|slot| self.vars.contains_key(slot)),
                "grant has no actual kind join"
            );
            let rho = facts
                .ownership_asts
                .get(Var::from_u32(grant.carrier.var))
                .ok_or_else(|| anyhow::anyhow!("missing grant responsibility AST"))?;
            let source = frozen
                .matched
                .guard_aliases()
                .get(&grant.meet.source.endpoint)
                .ok_or_else(|| anyhow::anyhow!("missing grant source dependency"))?;
            anyhow::ensure!(
                grant.meet.guards.get(source) == Some(&true),
                "grant lost source dependency"
            );
            if let super::licensing::matched::TerminalTarget::Free(endpoint) =
                grant.meet.terminal.target
            {
                let sink = frozen
                    .matched
                    .guard_aliases()
                    .get(&endpoint)
                    .ok_or_else(|| anyhow::anyhow!("missing grant sink dependency"))?;
                anyhow::ensure!(
                    grant.meet.guards.get(sink) == Some(&true),
                    "grant lost sink dependency"
                );
            }
            let mut dependencies = Vec::new();
            for (key, required) in &grant.meet.guards {
                let predicate = &facts
                    .guards
                    .iter()
                    .find(|binding| &binding.equation == key)
                    .ok_or_else(|| anyhow::anyhow!("missing actual grant predicate"))?
                    .predicate;
                dependencies.push(if *required {
                    predicate.clone()
                } else {
                    !predicate
                });
            }
            resolved.push((grant, Bool::and(&dependencies).implies(rho)));
        }
        for (grant, clause) in &resolved {
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || {
                    format!(
                        "own-license({}:{}:{})",
                        grant.function, grant.slot_key, grant.carrier.var
                    )
                },
                clause,
            );
        }
        Ok(resolved.len())
    }

    /// §NB1 SAFE-MONO clause: `safe(target) ⇒ safe(layer)` — a safe (`¬raw`)
    /// target cannot sit behind a raw pointer `layer` that was dereferenced to
    /// reach it. `safe(x) ≡ ¬raw(x)` (one-hot), so this is `raw(target) ∨
    /// ¬raw(layer)`, a hard clause over the two slots' `raw` bits. It is
    /// `¬safe`-only: it can only push a slot toward `raw`, never force
    /// `ref`/`own` (theorems-doc invariant 7). `target` and `layer` are always
    /// distinct slots (the target is never among the layers dereferenced to
    /// reach it).
    pub(crate) fn safe_mono(&self, target: SlotRef, layer: SlotRef) {
        let t = self
            .vars
            .get(&target)
            .unwrap_or_else(|| panic!("unknown slot: {target:?}"));
        let l = self
            .vars
            .get(&layer)
            .unwrap_or_else(|| panic!("unknown slot: {layer:?}"));
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("safe-mono({target:?}=>{layer:?})"),
            &Bool::or(&[&t.raw, &!&l.raw]),
        );
    }

    /// §8 BB1 — assert a borrow-exclusion guard for one conflict edge: at least one
    /// of the involved slots must NOT be a reference. `¬ref(issuer) ∨ ⋁ ¬ref(requirer)`,
    /// a hard clause over the slots' `ref_` one-hot bits. Committing `¬ref` (not `raw`)
    /// is deliberate — a borrow conflict only refutes the *reference* reading; the
    /// slot's ownership bit may still legitimately settle `Owning`. NO-OP when no slot
    /// is supplied (an all-`Field`-owner edge that BB0's Local-only mapping dropped):
    /// an empty `Bool::or` is `false` and would force spurious UNSAT, so the
    /// field-exclusivity gap is left unconstrained here rather than crashing the
    /// solve (deferred to the struct field-slot mapping).
    ///
    /// A non-empty guard is *not* guaranteed satisfiable: it is unsatisfiable iff
    /// every involved slot is independently pinned to `Ref` by hard ownership facts
    /// (`own(d+1)` true forces `¬raw(d)` via I1, and `own(d)` false), which
    /// `model_kinds_relaxing` cannot repair — it only drops malloc source selectors.
    /// Harmless while BO output is unconsumed; once consumed (post-BB2) the caller
    /// must treat a `None` model as a real possibility, not assume guards never UNSAT.
    ///
    /// Precondition: every supplied `SlotRef` must be registered in this solver — i.e.
    /// derived from the *same* `CrateSlots` the solver was built from. A foreign slot
    /// panics (`unknown slot`). Today's callers share one `CrateSlots`; a debug-assert
    /// is unnecessary while that discipline holds, but BB2's loop must preserve it.
    ///
    /// BB2-ii's Mode-A loop also calls this with a *single* slot
    /// (`add_borrow_exclusion(Some(slot), &[])`) to commit a monotone `¬ref(slot)` —
    /// the one-literal degenerate case of the same exclusion clause.
    pub(crate) fn add_borrow_exclusion(&self, issuer: Option<SlotRef>, requirers: &[SlotRef]) {
        let not_ref = |slot: SlotRef| {
            let vars = self
                .vars
                .get(&slot)
                .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
            !&vars.ref_
        };
        let literals: Vec<Bool> = issuer
            .into_iter()
            .chain(requirers.iter().copied())
            .map(not_ref)
            .collect();
        if literals.is_empty() {
            return;
        }
        let refs: Vec<&Bool> = literals.iter().collect();
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("borrow-exclusion({issuer:?},{requirers:?})"),
            &Bool::or(&refs),
        );
    }

    /// R377-1: the return-port rule. `add_borrow_exclusion` already denies `ref`
    /// for every allocation source; this denies `raw` as well, which leaves the
    /// one-hot's `own` — "Owning at the return port". The caller inherits it
    /// through the ordinary `link_own` solidification, so nothing new is
    /// emitted on the caller's side.
    ///
    /// R379-2: the row is RECORDED here and asserted at materialisation. At
    /// emission the objective and the final-zero obligations are not in the
    /// system yet, so a check here is satisfiable and the refusal it must yield
    /// to appears only later — report 048 measured exactly that
    /// (`emitted=true` for all three of `o03`'s slots).
    pub(crate) fn require_own(&self, key: &str, slot: SlotRef) {
        assert!(self.vars.contains_key(&slot), "unknown slot: {slot:?}");
        let mut admitted = self.return_port_admitted.borrow_mut();
        if admitted.iter().all(|(existing, _)| existing != key) {
            admitted.push((key.to_owned(), slot));
            admitted.sort_by(|left, right| left.0.cmp(&right.0));
        }
    }

    /// R379-2: the rows kept by each materialisation round, and the set that was
    /// admitted at emission. The cost receipt the seat reads.
    pub(crate) fn return_port_receipt(&self) -> (Vec<String>, Vec<usize>) {
        (
            self.return_port_admitted
                .borrow()
                .iter()
                .map(|(key, _)| key.clone())
                .collect(),
            self.return_port_kept.borrow().clone(),
        )
    }

    /// R379-2: assert every admitted return-port row, then let the caller's own
    /// `check` decide. On `Unsat` the caller bisects; with none admitted this
    /// asserts nothing and the round is exactly today's.
    fn assert_return_port_rows(&self, rows: &[(String, SlotRef)]) {
        // Scope-local, so asserted the way the assumption bundle is rather than
        // through `assert_hard`: that path bumps the tracked hard-assertion
        // count, which `relax_selectors_hard_typed`'s T2 no-bypass tripwire
        // reconciles against mandatory tracks plus typed endpoints — and a
        // popped scope does not un-bump it, so the next round trips.
        for (_, slot) in rows {
            self.solver.assert(&self.vars[slot].own);
        }
    }

    /// R379-2: the admissible subset, found deterministically in slot-key order.
    /// Called ONLY when the round was `Unsat` with every row asserted, so the
    /// common case costs no extra check at all.
    ///
    /// A prefix bisection was the first shape and it is wrong: admissibility is
    /// not monotone in slot-key order, so the maximal subset is not a prefix and
    /// a bisection keeps rows a later row is refused for. This adds one row at a
    /// time inside a single scope and keeps each that leaves the system
    /// satisfiable — greedy, exact for "no kept row is refused", and at most one
    /// check per admitted row on a round that was going to fail anyway.
    fn return_port_admissible_subset(
        &self,
        rows: &[(String, SlotRef)],
        bundle: &[Bool],
    ) -> Vec<(String, SlotRef)> {
        let mut kept = Vec::new();
        self.solver.push();
        for literal in bundle {
            self.solver.assert(literal);
        }
        for row in rows {
            self.solver.push();
            self.assert_return_port_rows(std::slice::from_ref(row));
            self.check_sat_count
                .set(self.check_sat_count.get().saturating_add(1));
            if self.solver.check(&[]) == SatResult::Sat {
                // Keep it asserted: the next row is judged against a system that
                // already carries everything kept before it.
                kept.push(row.clone());
            } else {
                self.solver.pop();
            }
        }
        for _ in 0..=kept.len() {
            self.solver.pop();
        }
        kept
    }

    /// A5 coarse pricing control: a may-overlapping formal pair cannot both
    /// settle `Ref`. This is deliberately separate from precise replay and is
    /// never the proposed landing consumer.
    pub(crate) fn add_a5_coarse_exclusion(&self, left: SlotRef, right: SlotRef) {
        assert_ne!(left, right, "A5 coarse pair must contain distinct slots");
        let left_ref = &self
            .vars
            .get(&left)
            .unwrap_or_else(|| panic!("unknown A5 slot: {left:?}"))
            .ref_;
        let right_ref = &self
            .vars
            .get(&right)
            .unwrap_or_else(|| panic!("unknown A5 slot: {right:?}"))
            .ref_;
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("a5-coarse-exclusion({left:?},{right:?})"),
            &Bool::or(&[&!left_ref, &!right_ref]),
        );
    }

    /// L2 context-conditioned single-literal commit. The planner supplies a
    /// witnessed-context clause. Ref-witnessed peers and the target contribute
    /// negative `ref` literals; Raw-witnessed peers contribute positive `ref`
    /// literals. This method binds that representation to the solver's
    /// hard-assertion and tracked-core path without changing Mode-A's existing
    /// `add_borrow_exclusion` emission.
    pub(crate) fn add_l2_commit(&self, action: &CommitAction) {
        let expected_family = match action.kind {
            CommitActionKind::GuardedCommit | CommitActionKind::UnconditionalCommit => {
                GUARDED_COMMIT_CORE_FAMILY
            }
            CommitActionKind::RecurrenceEscalation => RECURRENCE_ESCALATION_CORE_FAMILY,
        };
        assert_eq!(
            action.core_family, expected_family,
            "L2 action kind/core-family mismatch"
        );
        assert!(
            action.clause.negative_refs.contains(&action.target),
            "L2 clause must contain its negative target literal"
        );

        let mut literals = action
            .clause
            .negative_refs
            .iter()
            .map(|slot| {
                let vars = self
                    .vars
                    .get(slot)
                    .unwrap_or_else(|| panic!("unknown L2 slot: {slot:?}"));
                !&vars.ref_
            })
            .collect::<Vec<_>>();
        literals.extend(action.clause.positive_refs.iter().map(|slot| {
            let vars = self
                .vars
                .get(slot)
                .unwrap_or_else(|| panic!("unknown L2 slot: {slot:?}"));
            vars.ref_.clone()
        }));
        let refs = literals.iter().collect::<Vec<_>>();
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("{expected_family}({})", action.diagnostic_label),
            &Bool::or(&refs),
        );
    }

    /// §NB5-L2 — push a solver scope. Hard clauses asserted after `push_scope` are removed by the
    /// matching `pop_scope`; the soft objective (added in `build`, before any push) persists. The
    /// commit-necessity audit uses this to reuse ONE emitted base across all leave-one-out probes:
    /// `push_scope` → `add_borrow_exclusion(C\{ci})` → `model_kinds_relaxing` → `pop_scope`. Only the
    /// non-tracked production solve path uses it (the audit builds `KindSolver::new`).
    pub(crate) fn push_scope(&self) {
        if let Some(tracker) = self
            .tracker
            .as_ref()
            .filter(|tracker| tracker.is_mandatory())
        {
            self.mandatory_scope_lengths
                .borrow_mut()
                .push(tracker.len());
        }
        self.solver.push();
    }

    /// §NB5-L2 — backtrack one scope (see `push_scope`). Precondition: balanced with `push_scope`.
    pub(crate) fn pop_scope(&self) {
        self.solver.pop();
        if let Some(tracker) = self
            .tracker
            .as_ref()
            .filter(|tracker| tracker.is_mandatory())
        {
            let len = self
                .mandatory_scope_lengths
                .borrow_mut()
                .pop()
                .expect("mandatory-track scope stack underflow");
            tracker.truncate(len);
        }
    }

    /// §NB4-4c — assert `¬own(slot)`: a monotone ownership-exclusion clause, the companion to
    /// `add_borrow_exclusion` (`¬ref`). Together (`¬ref ∧ ¬own`) they pin an unknown-poisoned slot
    /// to `Raw` by one-hot — the may-overwrite/may-retain case where a bare `¬ref` would leave an
    /// unsound `Owning` (the 3c-ii rejection of the blunt `¬ref`-only clause). *Forbid-only*: it
    /// never asserts a positive kind bit, so it only pushes toward raw — theorems-doc invariant 7
    /// intact, and it is trivially compatible with the `i1-adjacency` coupling clause (`raw(d) ⇒
    /// ¬own(d+1)` says nothing when a slot is forced non-`Owning`). When the slot ALSO carries a
    /// retractable malloc-source selector, this hard `¬own` forces that selector to LEAK under
    /// `model_kinds_relaxing` (a relaxed accept with the slot `Raw`), never a hard decline.
    ///
    /// Precondition (as `add_borrow_exclusion`): `slot` must be registered in this solver.
    ///
    /// NB4-4c: the may-supply demotion uses `¬ref` only; this `¬own` is the tool for the DEFERRED
    /// may-overwrite demotion (needs opaque-overwrite detection, which `summary.unknown` does not
    /// provide). Kept warm by `nb4_4c_add_owning_exclusion_forbids_owning`, not `allow(dead_code)`.
    pub(crate) fn add_owning_exclusion(&self, slot: SlotRef) {
        let vars = self
            .vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("own-exclusion({slot:?})"),
            &!&vars.own,
        );
    }

    /// §S2-3 DIAGNOSTIC PROBE (compute-only, no production caller). FORCE a slot `Owning` and let the
    /// caller `check()`: SAT ⇒ `own(slot)` is achievable under the hard constraints, so a zero yield in
    /// the optimized model is a SOFT (objective/retention) blocker, not a mechanism gap; UNSAT (best via
    /// `new_tracked`) ⇒ a hard constraint family forbids it and the core names it. Symmetric to
    /// `add_owning_exclusion`. Kept warm by `s23_owning_blocker_probe`.
    pub(crate) fn assert_owning(&self, slot: SlotRef) {
        let vars = self
            .vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("s23-force-own({slot:?})"),
            &vars.own,
        );
    }

    /// R385-1 companion to `assert_owning`: FORCE a slot `Ref` for the
    /// forced-assignment core probe. Compute-only, no production caller.
    pub(crate) fn assert_ref(&self, slot: SlotRef) {
        let vars = self
            .vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("r385-force-ref({slot:?})"),
            &vars.ref_,
        );
    }

    pub fn check(&self) -> SatResult {
        execution_guard::require(Operation::Query(QueryStage::OptimizeCheck));
        // §NB-R guard: a no-assumption check on a tracked solver is vacuously
        // SAT (all hard constraints are track-gated) — refuse, like the other
        // production solve paths.
        assert!(
            !self.is_diagnostic_tracked(),
            "diagnostic-tracked KindSolver must not enter check()"
        );
        self.check_with_assumptions(&[])
    }

    pub(crate) fn check_sat_count(&self) -> usize {
        self.check_sat_count.get()
    }

    pub(crate) fn hard_check_count(&self) -> usize {
        self.hard_check_count.get()
    }

    pub(crate) fn optimize_materialization_count(&self) -> usize {
        self.optimize_materialization_count.get()
    }

    pub(crate) fn lazy_plain_hard_check_count(&self) -> usize {
        self.lazy_plain_hard_check_count.get()
    }

    pub(crate) fn lazy_tracked_recheck_count(&self) -> usize {
        self.lazy_tracked_recheck_count.get()
    }

    pub(crate) fn lazy_plain_materialization_count(&self) -> usize {
        self.lazy_plain_materialization_count.get()
    }

    fn record_round_model_failure(&self, failure: RoundModelFailure) {
        let mut slot = self.round_model_failure.borrow_mut();
        if slot.is_none() {
            *slot = Some(failure);
        }
    }

    pub(crate) fn round_model_failure(&self) -> Option<RoundModelFailure> {
        self.round_model_failure.borrow().clone()
    }

    pub(crate) fn hard_check_elapsed(&self) -> Duration {
        self.hard_check_elapsed.get()
    }

    pub(crate) fn optimize_materialization_elapsed(&self) -> Duration {
        self.optimize_materialization_elapsed.get()
    }

    pub(crate) fn hard_assertion_count(&self) -> usize {
        self.solver.get_assertions().len()
    }

    pub(crate) fn hard_loop_solver(&self) -> HardLoopSolver {
        execution_guard::require(Operation::SolverBuild);
        assert!(
            !self.is_diagnostic_tracked(),
            "diagnostic-tracked KindSolver must not enter the production hard loop"
        );
        let solver = Solver::new();
        solver.set_params(&fixed_query_params());
        let assertions = self.solver.get_assertions();
        for assertion in &assertions {
            solver.assert(assertion);
        }
        HardLoopSolver {
            solver,
            synced_assertions: Cell::new(assertions.len()),
        }
    }

    pub(crate) fn check_with_assumptions(&self, assumptions: &[Bool]) -> SatResult {
        execution_guard::require(Operation::Query(QueryStage::OptimizeCheck));
        self.check_sat_count
            .set(self.check_sat_count.get().saturating_add(1));
        let bundle = self.assumption_bundle(assumptions);
        // R467-2 profile: the size of the query actually handed to z3.
        if self.check_sat_count.get() == 1 && std::env::var("CRAT_ERA5C_PROFILE").is_ok() {
            eprintln!(
                "E5C_QUERY hard={} tracks={} assumptions={} vars={}",
                self.hard_assertion_count(),
                self.mandatory_tracks().len(),
                bundle.len(),
                self.vars.len()
            );
        }
        let outcome = self.solver.check(&bundle);
        let query_reason = (outcome == SatResult::Unknown)
            .then(|| self.solver.get_reason_unknown())
            .flatten();
        let _ = execution_guard::known_query_result(
            QueryStage::OptimizeCheck,
            outcome,
            query_reason.clone(),
        );
        if self.demand_query_pending() {
            let core = (outcome == SatResult::Unsat)
                .then(|| self.solver.get_unsat_core())
                .unwrap_or_default();
            let reason = (outcome == SatResult::Unknown)
                .then(|| query_reason.clone().unwrap_or_else(|| "-".to_owned()));
            self.note_demand_query(assumptions, outcome, &core, reason);
        }
        #[cfg(test)]
        self.record_assumption_event(
            AssumptionCheckPhase::Optimize,
            assumptions,
            &bundle,
            outcome,
        );
        outcome
    }

    fn hard_check_with_assumptions(
        &self,
        hard: &HardLoopSolver,
        assumptions: &[Bool],
    ) -> SatResult {
        execution_guard::require(Operation::Query(QueryStage::HardCheck));
        self.check_sat_count
            .set(self.check_sat_count.get().saturating_add(1));
        self.hard_check_count
            .set(self.hard_check_count.get().saturating_add(1));
        let started = Instant::now();
        let bundle = self.assumption_bundle(assumptions);
        self.lazy_plain_hard_check_count
            .set(self.lazy_plain_hard_check_count.get().saturating_add(1));
        // The formulas remain the exact tracked construction, but the fixed
        // set is activated with ordinary hard assertions rather than an
        // assumption vector. On UNSAT only, repeat under assumptions so the
        // core retains its typed mandatory/T2 identities.
        hard.solver.push();
        for literal in &bundle {
            hard.solver.assert(literal);
        }
        let initial = hard.solver.check();
        let query_reason = (initial == SatResult::Unknown)
            .then(|| hard.solver.get_reason_unknown())
            .flatten();
        let _ = execution_guard::known_query_result(
            QueryStage::HardCheck,
            initial,
            query_reason.clone(),
        );
        let initial_unknown_reason =
            (initial == SatResult::Unknown).then(|| query_reason.unwrap_or_else(|| "-".to_owned()));
        hard.solver.pop(1);
        let outcome = if initial == SatResult::Unsat {
            execution_guard::require(Operation::Query(QueryStage::HardTrackedRecheck));
            self.lazy_tracked_recheck_count
                .set(self.lazy_tracked_recheck_count.get().saturating_add(1));
            let tracked = hard.solver.check_assumptions(&bundle);
            let reason = (tracked == SatResult::Unknown)
                .then(|| hard.solver.get_reason_unknown())
                .flatten();
            match execution_guard::known_query_result(
                QueryStage::HardTrackedRecheck,
                tracked,
                reason,
            ) {
                Err(unknown) => {
                    // Unknown cannot provide a retraction core. Keep the
                    // exceptional query once, then run normal housekeeping.
                    self.note_demand_query(assumptions, tracked, &[], unknown.reason.clone());
                    self.record_round_model_failure(RoundModelFailure::HardUnknown {
                        active_t2: assumptions.len(),
                        reason: unknown.reason.unwrap_or_else(|| "-".to_owned()),
                    });
                }
                Ok(known) => assert_eq!(
                    known,
                    SatResult::Unsat,
                    "lazy plain-hard UNSAT must reproduce on the tracked core backend"
                ),
            }
            tracked
        } else {
            initial
        };
        if self.demand_query_pending() {
            let core = (outcome == SatResult::Unsat)
                .then(|| hard.solver.get_unsat_core())
                .unwrap_or_default();
            self.note_demand_query(assumptions, outcome, &core, initial_unknown_reason.clone());
        }
        if let Some(reason) = initial_unknown_reason {
            self.record_round_model_failure(RoundModelFailure::HardUnknown {
                active_t2: assumptions.len(),
                reason,
            });
        }
        #[cfg(test)]
        self.record_assumption_event(AssumptionCheckPhase::Hard, assumptions, &bundle, outcome);
        self.hard_check_elapsed.set(
            self.hard_check_elapsed
                .get()
                .saturating_add(started.elapsed()),
        );
        outcome
    }

    pub(crate) fn optimize(&self) -> &Optimize {
        // The raw backend handle grants query authority to its caller.
        execution_guard::require(Operation::Query(QueryStage::OptimizeCheck));
        &self.solver
    }

    #[cfg(test)]
    pub(crate) fn set_random_seed(&self, seed: u32) {
        let mut params = fixed_query_params();
        params.set_u32("random_seed", seed);
        self.solver.set_params(&params);
    }

    #[cfg(test)]
    pub(crate) fn set_query_timeout(&self, timeout: Duration) {
        assert_eq!(
            timeout.as_millis(),
            u128::from(execution_guard::QUERY_TIMEOUT_MS),
            "the sealed query cap cannot be changed by a diagnostic setter"
        );
        self.solver.set_params(&fixed_query_params());
    }

    /// R484-1: the Raw-causal census forces `ref_` and reads the UNSAT core.
    /// Raw is the residual kind -- the objective prefers `ref_` -- so "why is
    /// this subject Raw?" is exactly "what forbids `ref_`?".
    #[cfg(test)]
    pub(crate) fn ref_literal(&self, slot: SlotRef) -> Bool {
        self.vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"))
            .ref_
            .clone()
    }

    #[cfg(test)]
    pub(crate) fn owning_literal(&self, slot: SlotRef) -> Bool {
        self.vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"))
            .own
            .clone()
    }

    /// W2 baseline-identity oracle: hold every typed endpoint assertion off
    /// while retaining the complete mandatory hard universe and objective.
    #[cfg(test)]
    pub(crate) fn model_without_t2_for_test(
        &self,
        selectors: &Selectors,
    ) -> Option<FxHashMap<SlotRef, SlotKind>> {
        let disabled = selectors
            .all()
            .iter()
            .map(|selector| !selector)
            .collect::<Vec<_>>();
        if self.check_with_assumptions(&disabled) != SatResult::Sat {
            return None;
        }
        let model = self.solver.get_model()?;
        Some(self.read_kinds(&model))
    }

    pub fn model_kinds(&self) -> Option<FxHashMap<SlotRef, SlotKind>> {
        execution_guard::require(Operation::Query(QueryStage::OptimizeCheck));
        // §NB-R guard (release-active, BB3-c style): a tracked solver's hard
        // constraints are `track ⇒ c` — without the tracks assumed they are
        // vacuously satisfiable, so this path would return a silently wrong
        // model instead of an error.
        assert!(
            !self.is_diagnostic_tracked(),
            "diagnostic-tracked KindSolver must not enter model_kinds"
        );
        if self.check() != SatResult::Sat {
            return None;
        }
        let model = self.solver.get_model()?;
        self.read_version_owns(&model);
        Some(self.read_kinds(&model))
    }

    /// Resolve the maximal selector assumption set using only the hard
    /// constraints mirrored into a plain `z3::Solver`. No model is exposed by
    /// this API; validation must call `optimized_model_under` next.
    pub(crate) fn relax_selectors_hard_reporting(
        &self,
        hard: &HardLoopSolver,
        selectors: &Selectors,
    ) -> Option<RelaxedSelectors> {
        match self.relax_selectors_hard_typed(hard, selectors) {
            HardRelaxResult::Sat(relaxed) => Some(relaxed),
            HardRelaxResult::Unsat | HardRelaxResult::Unknown => None,
        }
    }

    fn relax_selectors_hard_typed(
        &self,
        hard: &HardLoopSolver,
        selectors: &Selectors,
    ) -> HardRelaxResult {
        assert!(
            !self.is_diagnostic_tracked(),
            "diagnostic-tracked KindSolver must not enter hard selector relaxation"
        );
        hard.sync_from(self);
        let expected_hard = self.mandatory_tracks().len() + selectors.all().len();
        assert_eq!(
            self.hard_assertion_count(),
            expected_hard,
            "T2 no-bypass tripwire: every Optimize hard assertion must be either a mandatory \
             tracked constraint or a typed endpoint assertion"
        );
        assert_eq!(
            hard.assertion_count(),
            expected_hard,
            "T2 hard-loop mirror omitted or duplicated a tracked assertion"
        );
        self.begin_demand_epoch(selectors);
        let mut assumptions = selectors.all().to_vec();
        let mut dropped = Vec::new();
        let trace_epoch = SELECTOR_TRACE_CAPTURE.with(|capture| {
            let mut capture = capture.borrow_mut();
            let trace = capture.as_mut()?;
            if trace.epochs.is_empty() {
                trace.n_sources = selectors.n_sources;
                trace.total = selectors.all.len();
            } else {
                assert_eq!(trace.n_sources, selectors.n_sources);
                assert_eq!(trace.total, selectors.all.len());
            }
            let epoch = trace.epochs.len();
            trace.epochs.push(SelectorEpochTrace::default());
            Some(epoch)
        });

        let mut relax_rounds = 0usize;
        let profile_rounds = std::env::var("CRAT_ERA5C_PROFILE").is_ok();
        loop {
            // R467-2 profile: the relax loop's shape — rounds and live assumptions.
            if profile_rounds && relax_rounds % 200 == 0 {
                eprintln!(
                    "E5C_RELAX round={relax_rounds} assumptions={} dropped={} tracks={}",
                    assumptions.len(),
                    dropped.len(),
                    self.mandatory_tracks().len()
                );
            }
            relax_rounds += 1;
            self.prepare_demand_query(QueryPhase::SelectorSearch, None);
            match self.hard_check_with_assumptions(hard, &assumptions) {
                SatResult::Sat => break,
                SatResult::Unsat => {
                    let core = hard.solver.get_unsat_core();
                    let in_core = |selector: &Bool| core.iter().any(|item| item == selector);
                    let mut t2_core = assumptions
                        .iter()
                        .filter(|selector| in_core(selector))
                        .filter_map(|selector| selectors.index_of(selector))
                        .collect::<Vec<_>>();
                    let mandatory_core = core.iter().any(|literal| {
                        self.tracker
                            .as_ref()
                            .filter(|tracker| tracker.is_mandatory())
                            .and_then(|tracker| tracker.label_of(literal))
                            .is_some()
                    });
                    let core_labels = self.core_labels(selectors, &core);
                    // era-5c: name the core a leaked selector came from.
                    if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                        for label in &core_labels {
                            eprintln!("E5C relax-core {label}");
                        }
                        eprintln!("E5C relax-core-end");
                    }
                    if t2_core.is_empty() {
                        self.record_round_model_failure(RoundModelFailure::HardUnsat {
                            active_t2: assumptions.len(),
                            core_labels,
                        });
                        return HardRelaxResult::Unsat;
                    }
                    assert!(
                        mandatory_core,
                        "T2-only UNSAT core is an incomplete mandatory-track universe: {:?}",
                        self.core_labels(selectors, &core)
                    );
                    t2_core.sort_by(|left, right| {
                        selectors.keys[*left]
                            .sort_key()
                            .cmp(&selectors.keys[*right].sort_key())
                    });
                    let selector_index = t2_core[0];
                    self.mark_demand_candidate(selector_index);
                    let index = assumptions
                        .iter()
                        .position(|selector| selectors.index_of(selector) == Some(selector_index))
                        .expect("core T2 assertion is active");
                    if let Some(epoch) = trace_epoch {
                        SELECTOR_TRACE_CAPTURE.with(|capture| {
                            let mut capture = capture.borrow_mut();
                            let trace = capture.as_mut().expect("selector trace active");
                            trace.epochs[epoch].events.push(SelectorTraceEvent {
                                epoch,
                                phase: SelectorTracePhase::Drop,
                                selector_index,
                                active_before: selectors.indices_of(&assumptions),
                                core_selectors: selectors.indices_of(&core),
                                core_labels,
                                outcome: SelectorTraceOutcome::Dropped,
                            });
                        });
                    }
                    dropped.push(assumptions.swap_remove(index));
                }
                SatResult::Unknown => return HardRelaxResult::Unknown,
            }
        }

        dropped.sort_by(|left, right| {
            let left = selectors
                .index_of(left)
                .expect("dropped T2 assertion belongs to selector universe");
            let right = selectors
                .index_of(right)
                .expect("dropped T2 assertion belongs to selector universe");
            selectors.keys[left]
                .sort_key()
                .cmp(&selectors.keys[right].sort_key())
        });
        let mut index = 0;
        while index < dropped.len() {
            let selector = dropped[index].clone();
            assumptions.push(selector.clone());
            self.prepare_demand_query(QueryPhase::Restoration, selectors.index_of(&selector));
            let outcome = self.hard_check_with_assumptions(hard, &assumptions);
            if let Some(epoch) = trace_epoch {
                let selector_index = selectors
                    .index_of(&selector)
                    .expect("dropped selector belongs to selector universe");
                let core = (outcome == SatResult::Unsat)
                    .then(|| hard.solver.get_unsat_core())
                    .unwrap_or_default();
                SELECTOR_TRACE_CAPTURE.with(|capture| {
                    let mut capture = capture.borrow_mut();
                    let trace = capture.as_mut().expect("selector trace active");
                    trace.epochs[epoch].events.push(SelectorTraceEvent {
                        epoch,
                        phase: SelectorTracePhase::Reenable,
                        selector_index,
                        active_before: selectors.indices_of(&assumptions),
                        core_selectors: selectors.indices_of(&core),
                        core_labels: self.core_labels(selectors, &core),
                        outcome: if outcome == SatResult::Sat {
                            SelectorTraceOutcome::Restored
                        } else {
                            SelectorTraceOutcome::StayedDropped
                        },
                    });
                });
            }
            match outcome {
                SatResult::Sat => {
                    dropped.swap_remove(index);
                }
                SatResult::Unsat => {
                    assumptions.pop();
                    index += 1;
                }
                SatResult::Unknown => return HardRelaxResult::Unknown,
            }
        }

        if let Some(epoch) = trace_epoch {
            SELECTOR_TRACE_CAPTURE.with(|capture| {
                let mut capture = capture.borrow_mut();
                let trace = capture.as_mut().expect("selector trace active");
                trace.epochs[epoch].final_dropped = selectors.indices_of(&dropped);
            });
        }
        self.finish_demand_epoch(&dropped);
        HardRelaxResult::Sat(RelaxedSelectors {
            assumptions,
            dropped,
        })
    }

    /// Materialize the objective-selected model for one validation round after
    /// hard-only selector decisions have fixed its active set. The fixed
    /// mandatory and surviving T2 literals are temporary plain-hard assertions;
    /// the Optimize check itself carries no assumptions.
    pub(crate) fn optimized_model_under(
        &self,
        relaxed: &RelaxedSelectors,
    ) -> Option<FxHashMap<SlotRef, SlotKind>> {
        execution_guard::require(Operation::Query(QueryStage::OptimizeMaterialization));
        self.optimize_materialization_count
            .set(self.optimize_materialization_count.get().saturating_add(1));
        let started = Instant::now();
        self.check_sat_count
            .set(self.check_sat_count.get().saturating_add(1));
        let bundle = self.assumption_bundle(&relaxed.assumptions);
        self.lazy_plain_materialization_count.set(
            self.lazy_plain_materialization_count
                .get()
                .saturating_add(1),
        );
        // R379-2: the return-port rows go in HERE, where the system is complete —
        // the objective and the final-zero obligations are in it, so a refusal
        // they carry is visible and the rows yield to it. All at once, so the
        // common case costs no extra check; the bisection below runs only when
        // the round is `Unsat` with every row asserted.
        let mut rows = self.return_port_admitted.borrow().clone();
        self.solver.push();
        for literal in &bundle {
            self.solver.assert(literal);
        }
        self.assert_return_port_rows(&rows);
        self.prepare_demand_query(QueryPhase::Materialization, None);
        // R467-2 profile: the size of the materialization query handed to z3.
        if std::env::var("CRAT_ERA5C_PROFILE").is_ok() {
            eprintln!(
                "E5C_QUERY materialization#{} hard={} tracks={} bundle={} rows={} vars={}",
                self.optimize_materialization_count.get(),
                self.hard_assertion_count(),
                self.mandatory_tracks().len(),
                bundle.len(),
                rows.len(),
                self.vars.len()
            );
        }
        let mut outcome = self.solver.check(&[]);
        if outcome == SatResult::Unsat && !rows.is_empty() {
            self.solver.pop();
            rows = self.return_port_admissible_subset(&rows, &bundle);
            self.solver.push();
            for literal in &bundle {
                self.solver.assert(literal);
            }
            self.assert_return_port_rows(&rows);
            self.prepare_demand_query(QueryPhase::Materialization, None);
            self.check_sat_count
                .set(self.check_sat_count.get().saturating_add(1));
            outcome = self.solver.check(&[]);
        }
        self.return_port_kept.borrow_mut().push(rows.len());
        if std::env::var("CRAT_R377_DEBUG").is_ok() {
            eprintln!(
                "R377ROUND admitted={} kept={} outcome={outcome:?}",
                self.return_port_admitted.borrow().len(),
                rows.len()
            );
        }
        let outcome = outcome;
        let query_reason = (outcome == SatResult::Unknown)
            .then(|| self.solver.get_reason_unknown())
            .flatten();
        let _ = execution_guard::known_query_result(
            QueryStage::OptimizeMaterialization,
            outcome,
            query_reason.clone(),
        );
        let unknown_reason =
            (outcome == SatResult::Unknown).then(|| query_reason.unwrap_or_else(|| "-".to_owned()));
        if self.demand_query_pending() {
            let core = (outcome == SatResult::Unsat)
                .then(|| self.solver.get_unsat_core())
                .unwrap_or_default();
            self.note_demand_query(&relaxed.assumptions, outcome, &core, unknown_reason.clone());
        }
        #[cfg(test)]
        self.record_assumption_event(
            AssumptionCheckPhase::OptimizeMaterialization,
            &relaxed.assumptions,
            &bundle,
            outcome,
        );
        let kinds = if outcome == SatResult::Sat {
            match self.solver.get_model() {
                Some(model) => {
                    self.read_version_owns(&model);
                    Some(self.read_kinds(&model))
                }
                None => {
                    self.record_round_model_failure(RoundModelFailure::OptimizeMissingModel {
                        active_t2: relaxed.assumptions.len(),
                    });
                    None
                }
            }
        } else {
            self.record_round_model_failure(match outcome {
                SatResult::Unsat => RoundModelFailure::OptimizeUnsat {
                    active_t2: relaxed.assumptions.len(),
                },
                SatResult::Unknown => RoundModelFailure::OptimizeUnknown {
                    active_t2: relaxed.assumptions.len(),
                    reason: unknown_reason.unwrap_or_else(|| "-".to_owned()),
                },
                SatResult::Sat => unreachable!(),
            });
            None
        };
        self.solver.pop();
        self.optimize_materialization_elapsed.set(
            self.optimize_materialization_elapsed
                .get()
                .saturating_add(started.elapsed()),
        );
        kinds
    }

    pub(crate) fn model_kinds_decomposed_reporting_l2(
        &self,
        hard: &HardLoopSolver,
        selectors: &Selectors,
    ) -> L2SolveResult {
        match self.relax_selectors_hard_typed(hard, selectors) {
            HardRelaxResult::Sat(relaxed) => {
                let dropped = relaxed.dropped.clone();
                self.optimized_model_under(&relaxed)
                    .map(|kinds| L2SolveResult::Sat { kinds, dropped })
                    .unwrap_or(L2SolveResult::Unknown)
            }
            HardRelaxResult::Unsat => L2SolveResult::Unsat,
            HardRelaxResult::Unknown => L2SolveResult::Unknown,
        }
    }

    /// Solve assuming all of `selectors` (reproducing the hard sources and
    /// sinks). On UNSAT, leak a **subset-minimal** set of conflicting
    /// selectors (phase 2 proves no leaked selector is individually
    /// restorable) and return the resulting per-slot kinds, or `None` if the
    /// system is UNSAT for non-selector reasons. Subset-minimal is NOT
    /// minimum-cardinality: the §S2-1 sinks-first policy deliberately retains
    /// a source even where leaking it alone would have been fewer total
    /// leaks (a source's Owning conversion outweighs leaked frees —
    /// `nbs2_mixed_fanout_prefers_source_over_two_sinks` pins the trade).
    ///
    /// All z3 Bools share the single thread-local context (the analysis is
    /// single-threaded), so `c == s` is `Z3_is_eq_ast` node identity — valid
    /// because `Bool::clone` shares the `Z3_ast` pointer and `get_unsat_core`
    /// returns the original assumption literals.
    ///
    /// Terminates: phase 1 drops one of finitely many selectors per UNSAT round;
    /// phase 2 visits each dropped selector once. Leaking a source classifies
    /// that allocation non-Owning, which is memory-safe; leaking a sink leaves
    /// an unprovable free a raw-pointer free.
    pub(crate) fn model_kinds_relaxing(
        &self,
        selectors: &Selectors,
    ) -> Option<FxHashMap<SlotRef, SlotKind>> {
        self.model_kinds_relaxing_reporting(selectors)
            .map(|(kinds, _dropped)| kinds)
    }

    /// §NB-F reporting twin of `model_kinds_relaxing`: also returns WHICH
    /// selectors were dropped (leaked sources and/or leaked sinks — classify
    /// via `Selectors`). Same semantics; the plain fn delegates here.
    pub(crate) fn model_kinds_relaxing_reporting(
        &self,
        selectors: &Selectors,
    ) -> Option<(FxHashMap<SlotRef, SlotKind>, Vec<Bool>)> {
        if self.tracker.as_ref().is_some_and(CoreTracker::is_mandatory) {
            let hard = self.hard_loop_solver();
            let relaxed = self.relax_selectors_hard_reporting(&hard, selectors)?;
            let dropped = relaxed.dropped().to_vec();
            let model = self.optimized_model_under(&relaxed)?;
            return Some((model, dropped));
        }
        // §NB-R guard (release-active): under tracking, this loop's unsat-core
        // search would see foreign track literals in cores and its selector
        // matching would silently misbehave. Tracked instances are driven only
        // by the explain path.
        assert!(
            self.tracker.is_none(),
            "tracked KindSolver must not enter model_kinds_relaxing (constraints are track-gated)"
        );
        self.begin_demand_epoch(selectors);
        let mut assumptions: Vec<Bool> = selectors.all().to_vec();
        let mut leaked: Vec<Bool> = Vec::new();
        let trace_epoch = SELECTOR_TRACE_CAPTURE.with(|capture| {
            let mut capture = capture.borrow_mut();
            let trace = capture.as_mut()?;
            if trace.epochs.is_empty() {
                trace.n_sources = selectors.n_sources;
                trace.total = selectors.all.len();
            } else {
                assert_eq!(trace.n_sources, selectors.n_sources);
                assert_eq!(trace.total, selectors.all.len());
            }
            let epoch = trace.epochs.len();
            trace.epochs.push(SelectorEpochTrace::default());
            Some(epoch)
        });

        // Phase 1: drop conflicting selectors until SAT (or give up).
        loop {
            self.prepare_demand_query(QueryPhase::SelectorSearch, None);
            match self.check_with_assumptions(&assumptions) {
                SatResult::Sat => break,
                SatResult::Unsat => {
                    let core = self.solver.get_unsat_core();
                    // era-5c: name the core a leaked selector came from.
                    if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                        for label in self.core_labels(selectors, &core) {
                            eprintln!("E5C relax-core {label}");
                        }
                        eprintln!("E5C relax-core-end");
                    }
                    let in_core = |s: &Bool| core.iter().any(|c| c == s);
                    // §S2-1 (NB-F review F2): the drop choice on a MIXED
                    // source/sink core is a deliberate policy — drop sinks
                    // first, retain sources. A leaked sink costs a leak (the
                    // free stays a raw-pointer free); a leaked source costs
                    // Owning-conversion precision (D7's driver). On a true
                    // either/or tie phase 2 cannot undo the choice, so it must
                    // be made here. Within a class, and on cores with no sink
                    // at all, the pick stays positional — the pre-S2-1
                    // behavior exactly.
                    let idx = assumptions
                        .iter()
                        .position(|s| selectors.is_sink(s) && in_core(s))
                        .or_else(|| assumptions.iter().position(|s| in_core(s)))?;
                    self.mark_demand_candidate(
                        selectors
                            .index_of(&assumptions[idx])
                            .expect("selected endpoint"),
                    );
                    if let Some(epoch) = trace_epoch {
                        let selector_index = selectors
                            .index_of(&assumptions[idx])
                            .expect("active selector belongs to selector universe");
                        SELECTOR_TRACE_CAPTURE.with(|capture| {
                            let mut capture = capture.borrow_mut();
                            let trace = capture.as_mut().expect("selector trace active");
                            trace.epochs[epoch].events.push(SelectorTraceEvent {
                                epoch,
                                phase: SelectorTracePhase::Drop,
                                selector_index,
                                active_before: selectors.indices_of(&assumptions),
                                core_selectors: selectors.indices_of(&core),
                                core_labels: Vec::new(),
                                outcome: SelectorTraceOutcome::Dropped,
                            });
                        });
                    }
                    leaked.push(assumptions.swap_remove(idx));
                }
                SatResult::Unknown => return None,
            }
        }

        // Phase 2: restore any selector that is not actually needed, so we leak
        // the minimal set. z3's unsat core is not guaranteed minimal, so phase 1
        // may drop more than necessary; re-adding a selector that keeps the
        // system SAT proves that allocation did not need to be leaked.
        let mut i = 0;
        while i < leaked.len() {
            let selector = leaked[i].clone();
            assumptions.push(leaked[i].clone());
            self.prepare_demand_query(QueryPhase::Restoration, selectors.index_of(&selector));
            let outcome = self.check_with_assumptions(&assumptions);
            if let Some(epoch) = trace_epoch {
                let selector_index = selectors
                    .index_of(&selector)
                    .expect("leaked selector belongs to selector universe");
                let core = (outcome == SatResult::Unsat)
                    .then(|| self.solver.get_unsat_core())
                    .unwrap_or_default();
                SELECTOR_TRACE_CAPTURE.with(|capture| {
                    let mut capture = capture.borrow_mut();
                    let trace = capture.as_mut().expect("selector trace active");
                    trace.epochs[epoch].events.push(SelectorTraceEvent {
                        epoch,
                        phase: SelectorTracePhase::Reenable,
                        selector_index,
                        active_before: selectors.indices_of(&assumptions),
                        core_selectors: selectors.indices_of(&core),
                        core_labels: Vec::new(),
                        outcome: if outcome == SatResult::Sat {
                            SelectorTraceOutcome::Restored
                        } else {
                            SelectorTraceOutcome::StayedDropped
                        },
                    });
                });
            }
            match outcome {
                SatResult::Sat => {
                    leaked.swap_remove(i);
                }
                SatResult::Unsat => {
                    assumptions.pop();
                    i += 1;
                }
                SatResult::Unknown => return None,
            }
        }

        if let Some(epoch) = trace_epoch {
            SELECTOR_TRACE_CAPTURE.with(|capture| {
                let mut capture = capture.borrow_mut();
                let trace = capture.as_mut().expect("selector trace active");
                trace.epochs[epoch].final_dropped = selectors.indices_of(&leaked);
            });
        }

        self.finish_demand_epoch(&leaked);
        self.prepare_demand_query(QueryPhase::Materialization, None);
        // Final SAT model under the maximal-retention assumption set.
        match self.check_with_assumptions(&assumptions) {
            SatResult::Sat => {
                let model = self.solver.get_model()?;
                self.read_version_owns(&model);
                Some((self.read_kinds(&model), leaked))
            }
            _ => None,
        }
    }

    /// L2 reporting solve. Unlike the legacy `Option` API, this preserves the
    /// fail-closed distinction between non-selector UNSAT and Z3 Unknown so the
    /// feature-on loop can emit the ruled diagnostic without altering the
    /// feature-off solver path.
    pub(crate) fn model_kinds_relaxing_reporting_l2(&self, selectors: &Selectors) -> L2SolveResult {
        if self.tracker.as_ref().is_some_and(CoreTracker::is_mandatory) {
            let hard = self.hard_loop_solver();
            return self.model_kinds_decomposed_reporting_l2(&hard, selectors);
        }
        assert!(
            self.tracker.is_none(),
            "tracked KindSolver must not enter model_kinds_relaxing (constraints are track-gated)"
        );
        self.begin_demand_epoch(selectors);
        let mut assumptions = selectors.all().to_vec();
        let mut leaked = Vec::new();

        loop {
            self.prepare_demand_query(QueryPhase::SelectorSearch, None);
            match self.check_with_assumptions(&assumptions) {
                SatResult::Sat => break,
                SatResult::Unsat => {
                    let core = self.solver.get_unsat_core();
                    let in_core = |selector: &Bool| core.iter().any(|item| item == selector);
                    let Some(index) = assumptions
                        .iter()
                        .position(|selector| selectors.is_sink(selector) && in_core(selector))
                        .or_else(|| assumptions.iter().position(in_core))
                    else {
                        return L2SolveResult::Unsat;
                    };
                    self.mark_demand_candidate(
                        selectors
                            .index_of(&assumptions[index])
                            .expect("selected endpoint"),
                    );
                    leaked.push(assumptions.swap_remove(index));
                }
                SatResult::Unknown => return L2SolveResult::Unknown,
            }
        }

        let mut final_model_ready = true;
        let mut index = 0;
        while index < leaked.len() {
            assumptions.push(leaked[index].clone());
            self.prepare_demand_query(QueryPhase::Restoration, selectors.index_of(&leaked[index]));
            match self.check_with_assumptions(&assumptions) {
                SatResult::Sat => {
                    leaked.swap_remove(index);
                    final_model_ready = true;
                }
                SatResult::Unsat => {
                    assumptions.pop();
                    index += 1;
                    final_model_ready = false;
                }
                SatResult::Unknown => return L2SolveResult::Unknown,
            }
        }

        self.finish_demand_epoch(&leaked);
        let final_outcome = if final_model_ready {
            SatResult::Sat
        } else {
            self.prepare_demand_query(QueryPhase::Materialization, None);
            self.check_with_assumptions(&assumptions)
        };
        match final_outcome {
            SatResult::Sat => self
                .solver
                .get_model()
                .map(|model| L2SolveResult::Sat {
                    kinds: {
                        self.read_version_owns(&model);
                        self.read_kinds(&model)
                    },
                    dropped: leaked,
                })
                .unwrap_or(L2SolveResult::Unknown),
            SatResult::Unsat => L2SolveResult::Unsat,
            SatResult::Unknown => L2SolveResult::Unknown,
        }
    }

    /// E-R2 sibling of [`Self::read_kinds`]: evaluate each ownership `Var`'s
    /// Bool against the SAME live model, using the same [`is_true`] helper so
    /// the two readouts cannot disagree.
    fn read_version_owns(&self, model: &Model) {
        *self.original_cell_model.borrow_mut() = self.ownership_facts().map(|facts| {
            Rc::new(super::licensing::model_selection::Selection::from_model(
                facts,
                |predicate| {
                    model
                        .eval(predicate, true)
                        .and_then(|value| value.as_bool())
                },
            ))
        });
        super::export::record_version_owns_from(|asts| {
            asts.iter().map(|b| is_true(model, b)).collect()
        });
        #[cfg(test)]
        OWNERSHIP_MODEL_CAPTURE.with(|capture| {
            if let Some(capture) = capture.borrow_mut().as_mut() {
                let asts = capture.asts.as_ref().expect("ownership emission snapshot");
                capture
                    .observation
                    .model_reads
                    .push(asts.iter().map(|b| is_true(model, b)).collect());
            }
        });
    }

    /// Immutable carrier from the latest successful model read; never infer guards from kinds.
    pub(crate) fn original_cell_selection(
        &self,
    ) -> Option<std::rc::Rc<super::licensing::model_selection::Selection>> {
        self.original_cell_model.borrow().clone()
    }

    fn read_kinds(&self, model: &Model) -> FxHashMap<SlotRef, SlotKind> {
        let mut kinds = FxHashMap::default();
        kinds.reserve(self.vars.len());
        for (&slot, vars) in &self.vars {
            let kind = if is_true(model, &vars.own) {
                SlotKind::Owning
            } else if is_true(model, &vars.ref_) {
                SlotKind::Ref
            } else {
                SlotKind::Raw
            };
            kinds.insert(slot, kind);
        }
        kinds
    }
}

pub(crate) enum L2SolveResult {
    Sat {
        kinds: FxHashMap<SlotRef, SlotKind>,
        dropped: Vec<Bool>,
    },
    Unsat,
    Unknown,
}

fn add_universe<F>(
    solver: &Optimize,
    tracker: Option<&CoreTracker>,
    vars: &mut FxHashMap<SlotRef, KindVars>,
    universe: &SlotUniverse,
    mut slot_ref: F,
) where
    F: FnMut(SlotId) -> SlotRef,
{
    for i in 0..universe.len() {
        let id = SlotId::from_usize(i);
        let kind_vars = KindVars {
            raw: Bool::fresh_const("raw"),
            ref_: Bool::fresh_const("ref"),
            own: Bool::fresh_const("own"),
        };

        let sref = slot_ref(id);
        assert_exactly_one(solver, tracker, sref, &kind_vars);
        vars.insert(sref, kind_vars);
    }

    // §NB1: the structural `i1-adjacency` chain clause. Emitted under `Chain`
    // AND `PerSite`, skipped only under `Off`. It is NOT redundant under
    // `PerSite`: the per-site SAFE-MONO walk fires only on READ/borrow sites
    // (write destinations excluded — `safety_mono`), so this clause is what
    // still covers write-only and never-dereferenced same-owner chains. It
    // stays under `PerSite` PERMANENTLY (the NB-plan's "delete after subsumption"
    // is resolved the other way). Ablation stays clean: `Chain` = this clause
    // only; `PerSite` = this clause + the read-site walk. See `SafeMonoMode`.
    if super::SafeMonoMode::current() == super::SafeMonoMode::Off {
        return;
    }
    for i in 0..universe.len().saturating_sub(1) {
        let a = SlotId::from_usize(i);
        let b = SlotId::from_usize(i + 1);
        if universe.slot(a).owner == universe.slot(b).owner {
            let sref_a = slot_ref(a);
            let sref_b = slot_ref(b);
            let a_vars = vars
                .get(&sref_a)
                .unwrap_or_else(|| panic!("missing solver vars for slot {a:?}"));
            let b_vars = vars
                .get(&sref_b)
                .unwrap_or_else(|| panic!("missing solver vars for slot {b:?}"));
            assert_not_both(
                solver,
                tracker,
                || format!("i1-adjacency({sref_a:?},{sref_b:?})"),
                &a_vars.raw,
                &b_vars.own,
            );
        }
    }
}

fn assert_exactly_one(
    solver: &Optimize,
    tracker: Option<&CoreTracker>,
    slot: SlotRef,
    vars: &KindVars,
) {
    assert_hard(
        solver,
        tracker,
        || format!("one-hot({slot:?},exists)"),
        &Bool::or(&[&vars.raw, &vars.ref_, &vars.own]),
    );
    assert_not_both(
        solver,
        tracker,
        || format!("one-hot({slot:?},raw-ref)"),
        &vars.raw,
        &vars.ref_,
    );
    assert_not_both(
        solver,
        tracker,
        || format!("one-hot({slot:?},raw-own)"),
        &vars.raw,
        &vars.own,
    );
    assert_not_both(
        solver,
        tracker,
        || format!("one-hot({slot:?},ref-own)"),
        &vars.ref_,
        &vars.own,
    );
}

fn assert_not_both(
    solver: &Optimize,
    tracker: Option<&CoreTracker>,
    label: impl FnOnce() -> String,
    a: &Bool,
    b: &Bool,
) {
    assert_hard(solver, tracker, label, &Bool::or(&[&!a, &!b]));
}

/// §NB-R — the single hard-assert choke point. Untracked: byte-identical to a
/// plain `assert` (the label closure is never evaluated). Tracked: assert
/// `track ⇒ constraint` and record the labeled track literal.
fn assert_hard(
    solver: &Optimize,
    tracker: Option<&CoreTracker>,
    label: impl FnOnce() -> String,
    constraint: &Bool,
) {
    #[cfg(test)]
    if crate::bo_c1::ownership_diagnostic_package::removal_filter_active() {
        assert!(
            tracker.is_none(),
            "family-removal diagnosis must remain untracked"
        );
        if crate::bo_c1::ownership_diagnostic_package::suppresses_label(label) {
            return;
        }
        solver.assert(constraint);
        return;
    }
    match tracker {
        None => solver.assert(constraint),
        Some(tracker) => {
            let track = tracker.record(label());
            solver.assert(&Bool::or(&[&!&track, constraint]));
        }
    }
}

fn is_true(model: &Model, b: &Bool) -> bool {
    model
        .eval(b, true)
        .and_then(|value| value.as_bool())
        .unwrap_or(false)
}

pub(crate) struct BoOwnDatabase<'opt> {
    optimize: &'opt Optimize,
    /// §NB-R: present iff the owning `KindSolver` is tracked; every hard
    /// constraint pushed here is then track-gated with an `own-*` family
    /// label (`push_source_owning` excepted — its selectors are already
    /// their own retractable assumption class).
    tracker: Option<&'opt CoreTracker>,
    z3_ast: IndexVec<Var, Bool>,
    ownership_facts: super::licensing::facts::Builder,
    source_sink_emissions: usize,
    /// One selector literal per `source` (malloc) ownership assertion. The owning
    /// is asserted as `selector ⇒ owning`; assuming all selectors reproduces the
    /// hard source, while the relax loop can drop a selector to leak that source.
    source_selectors: Vec<Bool>,
    source_keys: Vec<super::export::T2AssertKey>,
    /// §NB-F: one selector per `sink` (free/realloc arg) ownership assertion —
    /// the sink twin of `source_selectors`. Dropping one LEAKS THE FREE (the
    /// freed value's owning is no longer forced; nothing asserts ¬own/¬ref).
    sink_selectors: Vec<Bool>,
    sink_keys: Vec<super::export::T2AssertKey>,
}

impl BoOwnDatabase<'_> {
    pub(crate) fn declare_pending_fold(&mut self, key: (u32, usize)) {
        let candidate = {
            // R353-2: era-5b's own addition; the pin had no such constraint.
            if !super::licensing::facts::joint() || super::licensing::facts::skip_joint_other() {
                return;
            }
            let facts = self.ownership_facts.borrow();
            if facts.fold_declarations.is_none() {
                return;
            }
            facts
                .boundary_substitutions
                .iter()
                .find(|b| (b.point.construction, b.ordinal) == key)
                .and_then(|b| super::licensing::fold_declaration::eligible(&facts, b))
        };
        let Some((call, argument)) = candidate else { return };
        let predicate = Bool::fresh_const("pending-subtree-fold");
        let Some(guard) =
            super::ownership_evidence::record_key("guarded-fold-call", &[], None, Some(&predicate))
        else {
            return;
        };
        super::licensing::facts::record(|facts| {
            facts
                .fold_declarations
                .as_mut()
                .expect("new fold frame")
                .push(super::licensing::fold_declaration::Declaration {
                    guard,
                    boundary: key.1,
                    call,
                    argument,
                })
        });
        // Post-freeze preflight installs either complete caller permission
        // or the same hard pending hold. Declaration syntax grants nothing.
    }

    /// One pending predicate declared before the receiver. Syntax grants no
    /// permission; keep the ordinary equations and explicitly hold the guard.
    pub(crate) fn begin_pending_traversal(&mut self, callee: &str) -> Option<(Bool, usize)> {
        let parameter =
            super::licensing::traversal_call::preliminary(&self.ownership_facts.borrow(), callee)?;
        let guard = Bool::fresh_const("traversal-call");
        super::ownership_evidence::record("guarded-traversal-call", &[], None, Some(&guard));

        Some((guard, parameter.checked_sub(1)? as usize))
    }

    pub(crate) fn traversal_view_zero(&mut self, guard: &Bool, var: Var, formal: bool) {
        let operation = if formal {
            // R353-2: era-5b's own addition; the pin had no such constraint.
            if !super::licensing::facts::joint() || super::licensing::facts::skip_joint_other() {
                return;
            }
            "guarded-traversal-formal-zero"
        } else {
            "guarded-traversal-view-zero"
        };
        super::ownership_evidence::record(operation, &[var], None, Some(guard));
        assert_hard(
            self.optimize,
            self.tracker,
            || format!("own-{operation}"),
            &guard.implies(&!&self.z3_ast[var]),
        );
    }

    pub(crate) fn traversal_caller_frame(&mut self, guard: &Bool, before: Var, after: Var) {
        super::ownership_evidence::record(
            "guarded-traversal-frame",
            &[before, after],
            None,
            Some(guard),
        );
        assert_hard(
            self.optimize,
            self.tracker,
            || "own-traversal-frame".into(),
            &guard.implies(&self.z3_ast[before].eq(&self.z3_ast[after])),
        );
    }

    pub(crate) fn pending_traversal_pair(&mut self, guard: &Bool, variables: &[Var]) {
        // R353-2: era-5b's own addition; the pin had no such constraint.
        if !super::licensing::facts::joint() || super::licensing::facts::skip_joint_other() {
            return;
        }
        let (operation, clause) = match variables {
            [a, b] => (
                "guarded-traversal-receiver-legacy",
                self.z3_ast[*a].eq(&self.z3_ast[*b]),
            ),
            [a, b, c, d] => (
                "guarded-traversal-argument-legacy",
                Bool::and(&[
                    self.z3_ast[*a].eq(&self.z3_ast[*b]),
                    self.z3_ast[*c].eq(&self.z3_ast[*d]),
                ]),
            ),
            _ => unreachable!("pending traversal legacy tuple"),
        };
        super::ownership_evidence::record(operation, variables, None, Some(guard));
        assert_hard(
            self.optimize,
            self.tracker,
            || format!("own-{operation}"),
            &guard.not().implies(&clause),
        );
    }

    /// Complete the candidate's conditional reference equations only after
    /// exact call/output occurrences have been recorded. Permission is separate.
    pub(crate) fn emit_reference_effect_obligations(&mut self) -> anyhow::Result<()> {
        use super::ownership_boundary::Variables;
        let facts = self.ownership_facts.borrow().clone();
        let plan = super::licensing::ref_effects::Plan::build(&facts);
        let mut obligations = Vec::new();
        for candidate in &plan.candidates {
            let matches: Vec<_> = facts
                .equations
                .iter()
                .filter(|row| {
                    row.point == candidate.formation
                        && row.operation == "guarded-reference-field"
                        && row.variables
                            == [
                                candidate.payload_before.var,
                                candidate.cell_after.var,
                                candidate.cell_before.var,
                            ]
                })
                .collect();
            let [formation] = matches.as_slice() else { continue };
            let key = super::licensing::facts::EquationId {
                construction: formation.point.construction,
                ordinal: formation.ordinal,
            };
            let guard = facts
                .guards
                .iter()
                .find(|binding| binding.equation == key)
                .ok_or_else(|| anyhow::anyhow!("reference-effect producer guard missing"))?
                .predicate
                .clone();
            let boundary = facts
                .boundary_substitutions
                .iter()
                .find(|row| {
                    row.point.construction == candidate.construction
                        && row.ordinal == candidate.boundary
                })
                .ok_or_else(|| anyhow::anyhow!("reference-effect call missing"))?;
            let Variables::UseDef {
                use_var: outer_before,
                def_var: outer_after,
            } = boundary
                .reference_peel
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("reference-effect peel missing"))?
                .skipped
            else {
                anyhow::bail!("reference-effect outer window missing")
            };
            for (operation, point, left, right, zeros) in [
                (
                    "guarded-reference-scalar-read",
                    candidate.scalar_read.clone(),
                    candidate.scalar_after.var,
                    candidate.scalar_before.var,
                    false,
                ),
                (
                    "guarded-reference-output",
                    boundary.point.clone(),
                    candidate.cell_after.var,
                    candidate.payload_after.var,
                    false,
                ),
                (
                    "guarded-reference-outer",
                    boundary.point.clone(),
                    outer_after,
                    outer_before,
                    true,
                ),
                (
                    "guarded-reference-view-zero",
                    candidate.scalar_read.clone(),
                    candidate.scalar_view_new.var,
                    candidate.scalar_view_old.var,
                    true,
                ),
            ] {
                let left = Var::from_u32(left);
                let right = Var::from_u32(right);
                anyhow::ensure!(
                    self.z3_ast.get(left).is_some() && self.z3_ast.get(right).is_some(),
                    "reference-effect ownership AST missing"
                );
                obligations.push((operation, point, left, right, zeros, guard.clone()));
            }
        }
        for (operation, point, left, right, zeros, guard) in obligations {
            let _function = super::ownership_evidence::function(|| point.function.clone().unwrap());
            let _location = super::ownership_evidence::location(
                &point.phase,
                point.block.unwrap(),
                point.statement,
            );
            super::ownership_evidence::record(operation, &[left, right], None, Some(&guard));
            let left = &self.z3_ast[left];
            let right = &self.z3_ast[right];
            let relation = if zeros {
                Bool::and(&[!left, !right])
            } else {
                !left.xor(right)
            };
            assert_hard(
                self.optimize,
                self.tracker,
                || format!("own-reference-effect-{operation}"),
                &guard.implies(&relation),
            );
        }
        Ok(())
    }

    /// E-R2: hand the export a snapshot of the `Var -> Bool` map so the model
    /// readout can evaluate per-version ownership after emission has ended.
    /// Recording-only; no-op unless a capture scope is active.
    pub(crate) fn snapshot_version_asts(&self) {
        super::export::record_version_asts(&self.z3_ast);
        #[cfg(test)]
        OWNERSHIP_MODEL_CAPTURE.with(|capture| {
            if let Some(capture) = capture.borrow_mut().as_mut() {
                capture.observation.snapshot_lengths.push(self.z3_ast.len());
                capture.asts = Some(self.z3_ast.clone());
            }
        });
    }
}

impl<'opt> BoOwnDatabase<'opt> {
    pub(crate) fn new(optimize: &'opt Optimize, tracker: Option<&'opt CoreTracker>) -> Self {
        let mut z3_ast = IndexVec::with_capacity(100);
        z3_ast.push(Bool::fresh_const("own_dummy"));
        BoOwnDatabase {
            optimize,
            tracker,
            z3_ast,
            ownership_facts: Rc::new(RefCell::new(super::licensing::facts::Facts::default())),
            source_sink_emissions: 0,
            source_selectors: Vec::new(),
            source_keys: Vec::new(),
            sink_selectors: Vec::new(),
            sink_keys: Vec::new(),
        }
    }

    pub(crate) fn z3_ast_len(&self) -> usize {
        self.z3_ast.len()
    }

    /// Expose this database's builder to the existing occurrence producers.
    pub(crate) fn activate_facts(&self) -> super::licensing::facts::Scope {
        super::licensing::facts::activate(&self.ownership_facts)
    }

    /// Call after ending the scope and collecting the existing stats/selectors.
    pub(crate) fn freeze_facts(self) -> Rc<super::licensing::facts::Facts> {
        super::licensing::facts::freeze(self.ownership_facts, self.z3_ast)
    }

    pub(crate) fn source_sink_emissions(&self) -> usize {
        self.source_sink_emissions
    }

    /// The per-version ownership Bool for `var` (for solidification linking).
    pub(crate) fn own_bool(&self, var: Var) -> &Bool {
        &self.z3_ast[var]
    }

    /// A12's R1 ownership disjunction for one depth-zero transfer. `lend` is the exact kind-layer
    /// expression returned by [`KindSolver::lend_guard`]. When false, these are the existing Copy
    /// linearity or Move constraints. When true, the destination cannot own and the source owns
    /// both before and after the site.
    pub(crate) fn push_guarded_copy_constraints(
        &mut self,
        lend: &Bool,
        destination_def: Var,
        source_def: Var,
        source_use: Var,
        ensure_move: bool,
    ) {
        let destination_def = &self.z3_ast[destination_def];
        let source_def = &self.z3_ast[source_def];
        let source_use = &self.z3_ast[source_use];

        if ensure_move {
            assert_hard(
                self.optimize,
                self.tracker,
                || "own-copy-current-move-equal".to_owned(),
                &Bool::or(&[lend, &!destination_def.xor(source_use)]),
            );
            assert_hard(
                self.optimize,
                self.tracker,
                || "own-copy-current-move-source-cleared".to_owned(),
                &Bool::or(&[lend, &!source_def]),
            );
        } else {
            for (clause, suffix) in [
                (Bool::or(&[&!destination_def, &!source_def]), "exclusive"),
                (Bool::or(&[&!destination_def, source_use]), "destination"),
                (
                    Bool::or(&[destination_def, source_def, &!source_use]),
                    "conservation",
                ),
                (Bool::or(&[&!source_def, source_use]), "source"),
            ] {
                assert_hard(
                    self.optimize,
                    self.tracker,
                    || format!("own-copy-current-linear-{suffix}"),
                    &Bool::or(&[lend, &clause]),
                );
            }
        }

        let not_lend = !lend;
        for (clause, suffix) in [
            (!destination_def, "destination-not-owning"),
            (source_use.clone(), "source-use-owning"),
            (source_def.clone(), "source-def-owning"),
        ] {
            assert_hard(
                self.optimize,
                self.tracker,
                || format!("own-copy-lend-{suffix}"),
                &Bool::or(&[&not_lend, &clause]),
            );
        }
    }

    pub(crate) fn push_guarded_lend_source_constraints(
        &mut self,
        lend: &Bool,
        source_def: Var,
        source_use: Var,
    ) {
        let not_lend = !lend;
        for (clause, suffix) in [
            (self.z3_ast[source_use].clone(), "source-use-owning"),
            (self.z3_ast[source_def].clone(), "source-def-owning"),
        ] {
            assert_hard(
                self.optimize,
                self.tracker,
                || format!("own-copy-for-deref-lend-{suffix}"),
                &Bool::or(&[&not_lend, &clause]),
            );
        }
    }

    /// Selector literals for the emitted `source` ownerships. Assume all of them
    /// to reproduce the hard source; the relax loop drops some on UNSAT.
    pub(crate) fn source_selectors(&self) -> &[Bool] {
        &self.source_selectors
    }

    pub(crate) fn source_keys(&self) -> &[super::export::T2AssertKey] {
        &self.source_keys
    }

    /// §NB-F: selector literals for the emitted `sink` ownerships.
    pub(crate) fn sink_selectors(&self) -> &[Bool] {
        &self.sink_selectors
    }

    pub(crate) fn sink_keys(&self) -> &[super::export::T2AssertKey] {
        &self.sink_keys
    }
}

/// §NB-F: the retractable-assumption set emission returns — malloc SOURCE
/// selectors plus free/realloc SINK selectors. Stored combined (`all` is what
/// `verify_to_fixpoint`/`model_kinds_relaxing` consume) with a typed split so
/// no caller has to remember an ordering convention.
pub(crate) struct Selectors {
    all: Vec<Bool>,
    n_sources: usize,
    keys: Vec<super::export::T2AssertKey>,
}

impl Selectors {
    pub(crate) fn new(sources: Vec<Bool>, sinks: Vec<Bool>) -> Self {
        assert!(
            sources.is_empty() && sinks.is_empty(),
            "nonempty selector construction must carry typed T2 keys"
        );
        Self::new_with_keys(sources, Vec::new(), sinks, Vec::new())
    }

    pub(crate) fn new_with_keys(
        sources: Vec<Bool>,
        source_keys: Vec<super::export::T2AssertKey>,
        sinks: Vec<Bool>,
        sink_keys: Vec<super::export::T2AssertKey>,
    ) -> Self {
        assert_eq!(sources.len(), source_keys.len());
        assert_eq!(sinks.len(), sink_keys.len());
        let n_sources = sources.len();
        let mut all = sources;
        all.extend(sinks);
        let mut keys = source_keys;
        keys.extend(sink_keys);
        Selectors {
            all,
            n_sources,
            keys,
        }
    }

    pub(crate) fn all(&self) -> &[Bool] {
        &self.all
    }

    pub(crate) fn sources(&self) -> &[Bool] {
        &self.all[..self.n_sources]
    }

    pub(crate) fn sinks(&self) -> &[Bool] {
        &self.all[self.n_sources..]
    }

    pub(crate) fn keys(&self) -> &[super::export::T2AssertKey] {
        &self.keys
    }

    /// Whether a (core/dropped) literal is a sink selector — z3 node identity,
    /// same basis as the relax loop's selector matching.
    pub(crate) fn is_sink(&self, literal: &Bool) -> bool {
        self.sinks().iter().any(|s| s == literal)
    }

    pub(crate) fn index_of(&self, literal: &Bool) -> Option<usize> {
        self.all.iter().position(|selector| selector == literal)
    }

    fn indices_of(&self, literals: &[Bool]) -> Vec<usize> {
        literals
            .iter()
            .filter_map(|literal| self.index_of(literal))
            .collect()
    }
}

impl Database for BoOwnDatabase<'_> {
    fn new_vars(&mut self, var_gen: &mut Gen, size: u32) -> Range<Var> {
        let sigs = var_gen.new_sigs(size);
        for sig in sigs.clone() {
            assert_eq!(sig, self.z3_ast.push(Bool::fresh_const("own")));
        }
        sigs
    }

    fn push_linear_impl(&mut self, x: Var, y: Var, z: Var) {
        super::ownership_evidence::record("linear", &[x, y, z], None, None);
        let label = || format!("own-linear({x:?}+{y:?}={z:?})");
        let [x, y, z] = [x, y, z].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, &!y]));
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, z]));
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[x, y, &!z]));
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!y, z]));
    }

    fn push_guarded_copy(
        &mut self,
        lend: &Bool,
        destination_def: Var,
        source_def: Var,
        source_use: Var,
        ensure_move: bool,
    ) {
        super::ownership_evidence::record(
            if ensure_move {
                "guarded-move"
            } else {
                "guarded-copy"
            },
            &[destination_def, source_def, source_use],
            None,
            Some(lend),
        );
        self.push_guarded_copy_constraints(
            lend,
            destination_def,
            source_def,
            source_use,
            ensure_move,
        );
    }

    fn push_guarded_contract_port(&mut self, guard: &Bool, dest: Var, ret: Var) {
        super::ownership_evidence::record("guarded-contract-port", &[dest, ret], None, Some(guard));
        let d = &self.z3_ast[dest];
        let r = &self.z3_ast[ret];
        assert_hard(
            self.optimize,
            self.tracker,
            || format!("own-contract-port({dest:?}={ret:?})"),
            &Bool::or(&[&!guard, &!d.xor(r)]),
        );
        assert_hard(
            self.optimize,
            self.tracker,
            || format!("own-contract-port-drop({dest:?}<={ret:?})"),
            &Bool::or(&[guard, &!d, r]),
        );
    }

    fn push_guarded_lend_source(&mut self, lend: &Bool, source_def: Var, source_use: Var) {
        super::ownership_evidence::record(
            "guarded-lend-source",
            &[source_def, source_use],
            None,
            Some(lend),
        );
        self.push_guarded_lend_source_constraints(lend, source_def, source_use);
    }

    fn push_guarded_field_reader(
        &mut self,
        reader: &Bool,
        destination_def: Var,
        source_def: Var,
        source_use: Var,
        ensure_move: bool,
    ) {
        // R353-2: era-5b's own addition; the pin had no such constraint.
        if !super::licensing::facts::joint() || super::licensing::facts::skip_joint_readers() {
            return;
        }
        super::ownership_evidence::record(
            if ensure_move {
                "guarded-reader-move"
            } else {
                "guarded-reader-copy"
            },
            &[destination_def, source_def, source_use],
            None,
            Some(reader),
        );
        let destination = &self.z3_ast[destination_def];
        let after = &self.z3_ast[source_def];
        let before = &self.z3_ast[source_use];
        let transfer = if ensure_move {
            Bool::and(&[!destination.xor(before), !after])
        } else {
            Bool::and(&[
                !Bool::and(&[destination, after]),
                destination.implies(before),
                after.implies(before),
                before.implies(&Bool::or(&[destination, after])),
            ])
        };
        let view = Bool::and(&[!destination, !after.xor(before)]);
        for (clause, role) in [
            (reader.implies(&view), "view"),
            ((!reader).implies(&transfer), "transfer"),
        ] {
            assert_hard(
                self.optimize,
                self.tracker,
                || format!("own-field-reader-{role}"),
                &clause,
            );
        }
    }

    fn push_guarded_field_reader_tail(&mut self, reader: &Bool, post: Var, pre: Var, source: bool) {
        super::ownership_evidence::record(
            if source {
                // R353-2: era-5b's own addition; the pin had no such constraint.
                if !super::licensing::facts::joint()
                    || super::licensing::facts::skip_joint_readers()
                {
                    return;
                }
                "guarded-reader-source-tail"
            } else {
                "guarded-reader-view-tail"
            },
            &[post, pre],
            None,
            Some(reader),
        );
        let post = &self.z3_ast[post];
        let pre = &self.z3_ast[pre];
        let obligation = if source {
            !post.xor(pre)
        } else {
            Bool::and(&[!post, !pre])
        };
        assert_hard(
            self.optimize,
            self.tracker,
            || "own-field-reader-precision".into(),
            &reader.implies(&obligation),
        );
    }

    fn try_original_cell_argument(
        &mut self,
        boundary: &super::ownership_boundary::Substitution,
    ) -> bool {
        // R353-2: era-5b's own addition; the pin had no such constraint.
        if !super::licensing::facts::joint() || super::licensing::facts::skip_joint_other() {
            return false;
        }
        use super::{
            licensing::{cell_effects, facts::EquationId},
            ownership_boundary::Variables,
            ownership_occurrence::Availability::Present,
        };
        let values = {
            let facts = self.ownership_facts.borrow();
            let Some(candidate) = cell_effects::at_boundary(&facts, boundary) else {
                return false;
            };
            let Some(frame) = cell_effects::frame(&facts, &candidate) else {
                return false;
            };
            let id = EquationId {
                construction: frame.point.construction,
                ordinal: frame.ordinal,
            };
            let Some(binding) = facts.guards.iter().find(|binding| binding.equation == id) else {
                return false;
            };
            let Some(original) = facts.consumes.iter().find(|row| {
                row.point.construction == candidate.call.construction
                    && row.ordinal == candidate.original_consume
            }) else {
                return false;
            };
            let Present(window) = &original.projected else {
                return false;
            };
            let [pair] = boundary.matched.as_slice() else {
                return false;
            };
            let (
                Variables::UseDef {
                    use_var: formal_pre,
                    def_var: formal_post,
                },
                Variables::UseDef {
                    use_var: legacy_pre,
                    def_var: legacy_post,
                },
            ) = (&pair.formal, &pair.actual)
            else {
                return false;
            };
            let Some(peel) = &boundary.reference_peel else { return false };
            let Variables::UseDef {
                use_var: outer_pre,
                def_var: outer_post,
            } = peel.skipped
            else {
                return false;
            };
            (
                binding.predicate.clone(),
                [
                    *formal_pre,
                    *formal_post,
                    *legacy_pre,
                    *legacy_post,
                    window.use_start,
                    window.def_start,
                    outer_pre,
                    outer_post,
                ],
            )
        };
        let (guard, raw) = values;
        let [
            formal_pre,
            formal_post,
            legacy_pre,
            legacy_post,
            cell_pre,
            cell_post,
            outer_pre,
            outer_post,
        ] = raw.map(Var::from_u32);
        for (operation, variables) in [
            (
                "guarded-original-cell-argument",
                vec![formal_pre, formal_post, cell_pre, cell_post],
            ),
            (
                "guarded-original-cell-legacy",
                vec![formal_pre, legacy_pre, formal_post, legacy_post],
            ),
            ("guarded-original-cell-outer", vec![outer_pre, outer_post]),
        ] {
            super::ownership_evidence::record(operation, &variables, None, Some(&guard));
        }
        let eq = |a: Var, b: Var| !self.z3_ast[a].xor(&self.z3_ast[b]);
        let original = Bool::and(&[eq(formal_pre, cell_pre), eq(formal_post, cell_post)]);
        let legacy = Bool::and(&[eq(formal_pre, legacy_pre), eq(formal_post, legacy_post)]);
        let outer = Bool::and(&[!&self.z3_ast[outer_pre], !&self.z3_ast[outer_post]]);
        for (role, clause) in [
            ("argument", guard.implies(&original)),
            ("legacy", (!&guard).implies(&legacy)),
            ("outer", guard.implies(&outer)),
        ] {
            assert_hard(
                self.optimize,
                self.tracker,
                || format!("own-original-cell-{role}"),
                &clause,
            );
        }
        true
    }

    fn try_original_cell_frame(
        &mut self,
        reference: &super::ssa::consume::Consume<std::ops::Range<Var>>,
        cell: &super::ssa::consume::Consume<std::ops::Range<Var>>,
    ) -> bool {
        // R353-2: era-5b's own addition; the pin had no such constraint.
        if !super::licensing::facts::joint() || super::licensing::facts::skip_joint_other() {
            return false;
        }
        use super::ownership_occurrence::Availability::Present;
        let Some(point) = super::ownership_evidence::point() else { return false };
        let Some(candidate) =
            super::licensing::cell_effects::early(&self.ownership_facts.borrow(), &point)
        else {
            return false;
        };
        if reference.r#use.end.as_u32() - reference.r#use.start.as_u32() != 2
            || cell.r#use.end.as_u32() - cell.r#use.start.as_u32() != 1
        {
            return false;
        }
        let payload = super::ssa::consume::Consume {
            r#use: reference.r#use.start + 1u32,
            def: reference.def.start + 1u32,
        };
        let original = super::ssa::consume::Consume {
            r#use: cell.r#use.start,
            def: cell.def.start,
        };
        let transfer_scope = super::ownership_occurrence::transfer(&payload, &original, false);
        let exact = super::ownership_occurrence::current_transfer().is_some_and(|transfer| {
            matches!((&transfer.source, &transfer.destination), (Present(source), Present(destination))
                if source.consume == candidate.original_consume && destination.consume == candidate.reference_consume)
        });
        drop(transfer_scope);
        if !exact {
            return false;
        }
        // The native reference is always a view. In particular a future put
        // output must never become a token owned by this temporary.
        for var in reference.r#use.clone().chain(reference.def.clone()) {
            self.push_assume_impl(var, false);
        }
        let guard = Bool::fresh_const("original_cell_effect");
        {
            let _transfer = super::ownership_occurrence::transfer(&payload, &original, false);
            super::ownership_evidence::record(
                "guarded-original-cell-frame",
                &[payload.def, original.def, original.r#use],
                None,
                Some(&guard),
            );
        }
        let before = &self.z3_ast[original.r#use];
        let after = &self.z3_ast[original.def];
        assert_hard(
            self.optimize,
            self.tracker,
            || "own-original-cell-legacy-frame".into(),
            &(!&guard).implies(&!before.xor(after)),
        );
        // Full post-freeze preflight installs either permission or !guard.
        // This declaration does not claim a disposition before all facts exist.
        super::ownership_evidence::record(
            "guarded-original-cell-declared",
            &[],
            None,
            Some(&guard),
        );
        true
    }

    fn try_reference_field_effect(
        &mut self,
        reference: &super::ssa::consume::Consume<std::ops::Range<Var>>,
        cell: &super::ssa::consume::Consume<std::ops::Range<Var>>,
    ) -> bool {
        // R353-2: era-5b's own addition; the pin had no such constraint.
        if !super::licensing::facts::joint() || super::licensing::facts::skip_joint_other() {
            return false;
        }
        use super::ownership_occurrence::{Availability::Present, PathStep};
        if !super::licensing::facts::active()
            || reference.r#use.end.as_u32() - reference.r#use.start.as_u32() != 2
            || cell.r#use.end.as_u32() - cell.r#use.start.as_u32() != 1
        {
            return false;
        }
        let payload = super::ssa::consume::Consume {
            r#use: reference.r#use.start + 1u32,
            def: reference.def.start + 1u32,
        };
        let original = super::ssa::consume::Consume {
            r#use: cell.r#use.start,
            def: cell.def.start,
        };
        let scope = super::ownership_occurrence::transfer(&payload, &original, false);
        let exact = super::ownership_occurrence::current_transfer().is_some_and(|transfer| {
            let (Present(source), Present(destination)) = (transfer.source, transfer.destination)
            else {
                return false;
            };
            source.projection.is_empty()
                && destination.projection.is_empty()
                && matches!(source.path.as_slice(), [PathStep::Field { .. }])
                && destination.path.len() == 2
                && destination.path[0] == PathStep::Deref
                && destination.path[1] == source.path[0]
        });
        drop(scope);
        if !exact {
            return false;
        }
        for old in reference.r#use.clone() {
            self.push_assume_impl(old, false);
        }
        self.push_assume_impl(reference.def.start, false);
        let effect = Bool::fresh_const("reference_field_effect");
        let _scope = super::ownership_occurrence::transfer(&payload, &original, false);
        super::ownership_evidence::record(
            "guarded-reference-field",
            &[payload.def, original.def, original.r#use],
            None,
            Some(&effect),
        );
        let input = &self.z3_ast[payload.def];
        let before = &self.z3_ast[original.r#use];
        let after = &self.z3_ast[original.def];
        // The selected effect must later connect the actual call output to
        // `after`. Until that proof is installed, the guard is held false.
        for (clause, role) in [
            (effect.implies(&!input.xor(before)), "input"),
            (
                (!&effect).implies(&Bool::and(&[!input, !after.xor(before)])),
                "legacy",
            ),
        ] {
            assert_hard(
                self.optimize,
                self.tracker,
                || format!("own-reference-effect-{role}"),
                &clause,
            );
        }
        true
    }

    fn push_assume_impl(&mut self, x: Var, sign: bool) {
        super::ownership_evidence::record("assume", &[x], Some(sign), None);
        #[cfg(test)]
        let label = || {
            let site = current_own_assume_site();
            format!("own-assume[{}]({x:?}={sign})", site.as_str())
        };
        #[cfg(not(test))]
        let label = || format!("own-assume({x:?}={sign})");
        let x = &self.z3_ast[x];
        let value = Bool::from_bool(sign);
        assert_hard(self.optimize, self.tracker, label, &!(x.xor(&value)));
    }

    fn push_equal_impl(&mut self, x: Var, y: Var) {
        // R471-3 (ii): name the emitter of one specific equality. Diagnosis only.
        if let Ok(want) = std::env::var("CRAT_ERA5C_EQ_BACKTRACE") {
            let here = format!("{x:?},{y:?}");
            let here = here.replace("Var(", "").replace(')', "");
            if here.split(',').map(str::trim).collect::<Vec<_>>().join(",") == want {
                eprintln!(
                    "E5C_EQ_BACKTRACE pair=({x:?},{y:?})\n{}",
                    std::backtrace::Backtrace::force_capture()
                );
            }
        }
        super::ownership_evidence::record("equal", &[x, y], None, None);
        let label = || format!("own-equal({x:?},{y:?})");
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &!(x.xor(y)));
    }

    fn push_less_equal_impl(&mut self, x: Var, y: Var) {
        super::ownership_evidence::record("less-equal", &[x, y], None, None);
        let label = || format!("own-le({x:?}<={y:?})");
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, y]));
    }

    /// era-5c: the phi edge whose incoming component is known null. Recorded
    /// under its own operation and family so a core names it, never as a bare
    /// `less-equal`.
    fn push_null_join_impl(&mut self, x: Var, y: Var) {
        super::ownership_evidence::record("null-join", &[x, y], None, None);
        let label = || format!("own-null-join({x:?}<={y:?})");
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, y]));
    }

    fn push_eq_min_impl(&mut self, x: Var, y: Var, z: Var) {
        super::ownership_evidence::record("eq-min", &[x, y, z], None, None);
        let label = || format!("own-eqmin({x:?}=min({y:?},{z:?}))");
        let [x, y, z] = [x, y, z].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, y]));
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, z]));
        assert_hard(
            self.optimize,
            self.tracker,
            label,
            &Bool::or(&[x, &!y, &!z]),
        );
    }

    fn record_source_sink(&mut self) {
        self.source_sink_emissions += 1;
    }

    fn push_source_owning(&mut self, var: Var) {
        // Gate the owning behind a fresh selector: `selector ⇒ owning`.
        // Assuming the selector forces owning (the hard source); the relax loop
        // can drop the selector to leak this allocation instead. The selector
        // shares `self.optimize`'s thread-local z3 context (single-threaded
        // analysis), so it matches the literal `get_unsat_core` returns.
        let selector = Bool::fresh_const("src_sel");
        let not_sel = !&selector;
        let clause = Bool::or(&[&not_sel, &self.z3_ast[var]]);
        self.optimize.assert(&clause);
        self.source_selectors.push(selector);
        let key = super::export::current_t2_assert_key(super::export::BoundaryRole::Source, var);
        super::ownership_evidence::record_endpoint(
            &key,
            self.source_selectors
                .last()
                .expect("source selector just pushed"),
        );
        self.source_keys.push(key);
        // E-R3 capture: index-aligned with `source_selectors` by construction —
        // this is the only writer and it pushes exactly once. Recording-only.
        super::export::record_selector(super::export::BoundaryRole::Source, var);
    }

    fn push_sink_owning(&mut self, var: Var) {
        // §NB-F: `selector ⇒ owning`, the sink twin of `push_source_owning` —
        // the relax loop may drop the selector to LEAK THE FREE (decline
        // becomes leak; the freed value's owning is then unconstrained: no
        // ¬own/¬ref is asserted — there is deliberately no sink analogue of
        // NB0's eager ¬ref(source)). Like source selectors, never track-gated
        // (selectors are their own assumption class).
        let selector = Bool::fresh_const("sink_sel");
        let not_sel = !&selector;
        let clause = Bool::or(&[&not_sel, &self.z3_ast[var]]);
        self.optimize.assert(&clause);
        self.sink_selectors.push(selector);
        let key = super::export::current_t2_assert_key(super::export::BoundaryRole::Sink, var);
        super::ownership_evidence::record_endpoint(
            &key,
            self.sink_selectors
                .last()
                .expect("sink selector just pushed"),
        );
        self.sink_keys.push(key);
        // E-R3 capture: sink twin of the source push above; same alignment
        // guarantee, same recording-only contract.
        super::export::record_selector(super::export::BoundaryRole::Sink, var);
    }
}
