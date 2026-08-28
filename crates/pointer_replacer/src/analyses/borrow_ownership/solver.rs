use std::{
    cell::{Cell, RefCell},
    ops::Range,
    time::{Duration, Instant},
};

use rustc_hash::FxHashMap;
use rustc_index::IndexVec;
use rustc_span::def_id::LocalDefId;
use z3::{Model, Optimize, SatResult, Solver, ast::Bool};

use super::{
    SlotKind,
    crate_slots::CrateSlots,
    l2::{
        CommitAction, CommitActionKind, GUARDED_COMMIT_CORE_FAMILY,
        RECURRENCE_ESCALATION_CORE_FAMILY,
    },
    slots::{SlotId, SlotUniverse},
    ssa::constraint::{Database, Gen, Var},
};

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
            let family = core_label_family(&label)
                .unwrap_or_else(|| panic!("unrecognized hard-constraint family: {label}"));
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
    "return-ref-origin",
    "link-own",
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
    CastOrDepth,
    OtherInternal,
}

impl OwnAssumeSite {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::OpaqueCallArg => "opaque-call-arg",
            Self::LibcRule => "libc-rule",
            Self::LocalWrapper => "local-wrapper",
            Self::SsaTransfer => "ssa-transfer",
            Self::TemporaryFinalization => "temporary-finalization",
            Self::CastOrDepth => "cast-or-depth",
            Self::OtherInternal => "other-internal",
        }
    }
}

#[cfg(test)]
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

#[cfg(test)]
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

#[cfg(not(test))]
#[inline]
pub(crate) fn with_own_assume_site<T>(_site: OwnAssumeSite, f: impl FnOnce() -> T) -> T {
    f()
}

#[cfg(test)]
pub(crate) fn current_own_assume_site() -> OwnAssumeSite {
    OWN_ASSUME_SITE.with(Cell::get)
}

#[cfg(not(test))]
#[inline]
pub(crate) fn current_own_assume_site() -> OwnAssumeSite {
    OwnAssumeSite::OtherInternal
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

pub struct KindSolver {
    solver: Optimize,
    vars: FxHashMap<SlotRef, KindVars>,
    tracker: Option<CoreTracker>,
    check_sat_count: Cell<usize>,
    hard_check_count: Cell<usize>,
    optimize_materialization_count: Cell<usize>,
    hard_check_elapsed: Cell<Duration>,
    optimize_materialization_elapsed: Cell<Duration>,
    mandatory_scope_lengths: RefCell<Vec<usize>>,
}

/// R1a's private hard-query backend. It snapshots only `Optimize`'s hard
/// assertions; soft preferences remain owned by `KindSolver::solver` and are
/// consulted only by `optimized_model_under`.
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
        let solver = Optimize::new();
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
            hard_check_elapsed: Cell::new(Duration::ZERO),
            optimize_materialization_elapsed: Cell::new(Duration::ZERO),
            mandatory_scope_lengths: RefCell::new(Vec::new()),
        }
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

    pub fn check(&self) -> SatResult {
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
        assert!(
            !self.is_diagnostic_tracked(),
            "diagnostic-tracked KindSolver must not enter the production hard loop"
        );
        let solver = Solver::new();
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
        self.check_sat_count
            .set(self.check_sat_count.get().saturating_add(1));
        let bundle = self.assumption_bundle(assumptions);
        let outcome = self.solver.check(&bundle);
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
        self.check_sat_count
            .set(self.check_sat_count.get().saturating_add(1));
        self.hard_check_count
            .set(self.hard_check_count.get().saturating_add(1));
        let started = Instant::now();
        let bundle = self.assumption_bundle(assumptions);
        let outcome = hard.solver.check_assumptions(&bundle);
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
        &self.solver
    }

    #[cfg(test)]
    pub(crate) fn set_random_seed(&self, seed: u32) {
        let mut params = z3::Params::new();
        params.set_u32("random_seed", seed);
        self.solver.set_params(&params);
    }

    #[cfg(test)]
    pub(crate) fn set_query_timeout(&self, timeout: Duration) {
        let millis = u32::try_from(timeout.as_millis())
            .expect("diagnostic query timeout must fit a Z3 u32 millisecond parameter");
        let mut params = z3::Params::new();
        params.set_u32("timeout", millis);
        self.solver.set_params(&params);
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

        loop {
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
                    if t2_core.is_empty() {
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
                    let index = assumptions
                        .iter()
                        .position(|selector| selectors.index_of(selector) == Some(selector_index))
                        .expect("core T2 assertion is active");
                    let core_labels = self.core_labels(selectors, &core);
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
        HardRelaxResult::Sat(RelaxedSelectors {
            assumptions,
            dropped,
        })
    }

    /// Materialize the objective-selected model for one validation round after
    /// hard-only selector decisions have fixed its active assumptions.
    pub(crate) fn optimized_model_under(
        &self,
        relaxed: &RelaxedSelectors,
    ) -> Option<FxHashMap<SlotRef, SlotKind>> {
        self.optimize_materialization_count
            .set(self.optimize_materialization_count.get().saturating_add(1));
        let started = Instant::now();
        self.check_sat_count
            .set(self.check_sat_count.get().saturating_add(1));
        let bundle = self.assumption_bundle(&relaxed.assumptions);
        let outcome = self.solver.check(&bundle);
        #[cfg(test)]
        self.record_assumption_event(
            AssumptionCheckPhase::OptimizeMaterialization,
            &relaxed.assumptions,
            &bundle,
            outcome,
        );
        if outcome != SatResult::Sat {
            self.optimize_materialization_elapsed.set(
                self.optimize_materialization_elapsed
                    .get()
                    .saturating_add(started.elapsed()),
            );
            return None;
        }
        let Some(model) = self.solver.get_model() else {
            self.optimize_materialization_elapsed.set(
                self.optimize_materialization_elapsed
                    .get()
                    .saturating_add(started.elapsed()),
            );
            return None;
        };
        self.read_version_owns(&model);
        let kinds = self.read_kinds(&model);
        self.optimize_materialization_elapsed.set(
            self.optimize_materialization_elapsed
                .get()
                .saturating_add(started.elapsed()),
        );
        Some(kinds)
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
            match self.check_with_assumptions(&assumptions) {
                SatResult::Sat => break,
                SatResult::Unsat => {
                    let core = self.solver.get_unsat_core();
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
        let mut assumptions = selectors.all().to_vec();
        let mut leaked = Vec::new();

        loop {
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
                    leaked.push(assumptions.swap_remove(index));
                }
                SatResult::Unknown => return L2SolveResult::Unknown,
            }
        }

        let mut final_model_ready = true;
        let mut index = 0;
        while index < leaked.len() {
            assumptions.push(leaked[index].clone());
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

        let final_outcome = if final_model_ready {
            SatResult::Sat
        } else {
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
        super::export::record_version_owns_from(|asts| {
            asts.iter().map(|b| is_true(model, b)).collect()
        });
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
    /// E-R2: hand the export a snapshot of the `Var -> Bool` map so the model
    /// readout can evaluate per-version ownership after emission has ended.
    /// Recording-only; no-op unless a capture scope is active.
    pub(crate) fn snapshot_version_asts(&self) {
        super::export::record_version_asts(&self.z3_ast);
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
        self.push_guarded_copy_constraints(
            lend,
            destination_def,
            source_def,
            source_use,
            ensure_move,
        );
    }

    fn push_guarded_lend_source(&mut self, lend: &Bool, source_def: Var, source_use: Var) {
        self.push_guarded_lend_source_constraints(lend, source_def, source_use);
    }

    fn push_assume_impl(&mut self, x: Var, sign: bool) {
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
        let label = || format!("own-equal({x:?},{y:?})");
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &!(x.xor(y)));
    }

    fn push_less_equal_impl(&mut self, x: Var, y: Var) {
        let label = || format!("own-le({x:?}<={y:?})");
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, y]));
    }

    fn push_eq_min_impl(&mut self, x: Var, y: Var, z: Var) {
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
        self.source_keys.push(super::export::current_t2_assert_key(
            super::export::BoundaryRole::Source,
            var,
        ));
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
        self.sink_keys.push(super::export::current_t2_assert_key(
            super::export::BoundaryRole::Sink,
            var,
        ));
        // E-R3 capture: sink twin of the source push above; same alignment
        // guarantee, same recording-only contract.
        super::export::record_selector(super::export::BoundaryRole::Sink, var);
    }
}
