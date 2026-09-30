//! §8 BB0 — the borrow-verifier seam.
//!
//! Runs the production borrow pipeline (`analyses::borrow::borrow_conflicts`) with a
//! ref-candidacy derived from a BO ref-predicate, and translates the resulting
//! conflict edges back into BO `SlotRef`s. This is the read-only adapter the later
//! §8 steps build on: BB1 turns these conflicts into guarded exclusion clauses, BB2
//! wraps it in the CEGAR validate loop.
//!
//! BB0 scope: **Local owners only** (`Field` owners are dropped pending the struct
//! field-slot mapping) and **depth-0** correspondence (borrow tracks one provenance
//! per `Local` = the outermost pointer ↔ BO depth-0 slot). The adapter is faithful
//! for a Round-0 (all-Ref) candidacy; partial candidacy that encodes demotions also
//! needs the `tree_borrow_local` union replay the demotion loop performs (BB2).

use std::cell::{Cell, RefCell};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::Local;
use rustc_span::def_id::LocalDefId;
use z3::ast::Bool;

use super::{
    SlotKind,
    coherence::{CopyLendPair, SelectedCopyLendLoans, selected_copy_lend_sites},
    crate_slots::CrateSlots,
    l2::{
        self, CommitAction, ConflictObservation, DeclineReason as L2DeclineReason, Planner,
        RoundPlan as L2RoundPlan, SolverDecline as L2SolverDecline,
        SolverOutcome as L2SolverOutcome, StableLoanKey,
    },
    mutability_facts::MutProvider,
    origin_flow::OriginFlowResults,
    slots::{SlotId, SlotOwner},
    solver::{HardLoopSolver, KindSolver, L2SolveResult, Selectors, SlotRef},
};
use crate::{
    analyses::borrow::{self, ConflictEdge, ProvenanceOwner},
    utils::rustc::RustProgram,
};

thread_local! {
    /// §NB5-L — test/sweep-scoped `RepairMode` override (see `RepairMode::with_override`). Wins over
    /// the env selector so ONE process can run both repair modes (the differential harness + the S7
    /// sweep). `None` ⇒ fall through to env/`DEFAULT`.
    static REPAIR_OVERRIDE: Cell<Option<RepairMode>> = const { Cell::new(None) };
}

/// §NB5-L — the repair strategy the CEGAR loop uses to discharge a residual borrow conflict.
///
/// - `ModeA`: commit one `¬ref(representative)` per residual edge — monotone, permanent (the shipped
///   loop through NB5-F2).
/// - `Lemmas` (MVP): emit `⋁¬ref(A′-menu)` per residual edge — an **empty-context, A′-restricted
///   disjunctive lemma** (`¬ref`-only, invariant 7). It does NOT dominate `ModeA`: the hoped upside
///   (spare a "sparable" requirer) never arises because A′ excludes the only sparable slot (the
///   write-issuer); the disjunction's freedom to pick a NON-minimal menu member instead becomes a
///   *downside*. The two modes are **incomparable in general** (the loop is non-confluent — different
///   commit strategies induce different lemma sets and different optima); on tested fixtures
///   `Ref(lemmas) ⊆ Ref(mode_a)` and on a high-arity fan-out strictly ⊊ (Lemmas loses ≥1 Ref). So the
///   disjunction axis is dead; `ModeA` is the shipped default and the demotion-choice mechanism.
///
/// Selected by env `CRAT_BO_REPAIR ∈ {mode_a, lemmas, guarded}` (default `ModeA`; the gate did NOT flip it),
/// or a thread-local `with_override` that WINS over env. A uniform strategy toggle, constant within an
/// override scope — no path-divergence hazard (unlike 4c's threaded origins, which were divergent DATA).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum RepairMode {
    ModeA,
    Lemmas,
    /// R617-1 (era-5c 082, approved R631-7): the guarded planner's clauses in
    /// Mode-A's loop, at the point where Mode-A commits. Everything around the
    /// commits is Mode-A's. A decline falls back to Mode-A for the program
    /// (`RoundStats::guarded_fallback`, receipted).
    Guarded,
}

impl Default for RepairMode {
    fn default() -> Self {
        Self::DEFAULT
    }
}

impl RepairMode {
    /// Default until the gate flips it on the S7 differential (NB5-L rider 2). `RoundStats` derives
    /// `Default`, so this is also the mode a default-constructed stats block reports.
    pub(crate) const DEFAULT: Self = RepairMode::ModeA;

    /// Resolve the active mode: thread-local override first, then env `CRAT_BO_REPAIR`, then `DEFAULT`.
    /// Fail-loud on a SET-but-invalid env value (a typo must not silently fall back and mask which
    /// repair ran — the `ForkEngineMode` discipline).
    pub(crate) fn current() -> Self {
        if let Some(m) = REPAIR_OVERRIDE.with(|c| c.get()) {
            return m;
        }
        let selected = match std::env::var("CRAT_BO_REPAIR") {
            Ok(v) => match v.as_str() {
                "mode_a" | "mode-a" => Some(RepairMode::ModeA),
                "lemmas" => Some(RepairMode::Lemmas),
                "guarded" => Some(RepairMode::Guarded),
                other => panic!(
                    "CRAT_BO_REPAIR={other:?} is not a valid selector (expected mode_a, lemmas or \
                     guarded) — refusing to silently fall back"
                ),
            },
            Err(_) => None,
        };
        // R617-1: `CRAT_BO_L2_GUARDED_COMMITS=1` is `guarded`'s alias. Its historical form
        // required Mode-A (`mode_a` or unset), so those select the guarded mode with it;
        // `lemmas` contradicts it and is refused.
        if super::l2::enabled_from_env() {
            assert_ne!(
                selected,
                Some(RepairMode::Lemmas),
                "CRAT_BO_L2_GUARDED_COMMITS=1 (the guarded repair's alias) contradicts \
                 CRAT_BO_REPAIR=lemmas"
            );
            return RepairMode::Guarded;
        }
        selected.unwrap_or(Self::DEFAULT)
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            RepairMode::ModeA => "mode_a",
            RepairMode::Lemmas => "lemmas",
            RepairMode::Guarded => "guarded",
        }
    }

    /// §NB5-L guard 2 — run `f` with `mode` forced on this thread, restoring the prior override on
    /// exit INCLUDING on panic (a drop-guard, not a manual reset: a panicking test must not leak its
    /// mode onto the thread for the next test). Test/sweep-only; production resolves via `current()`.
    pub(crate) fn with_override<T>(mode: RepairMode, f: impl FnOnce() -> T) -> T {
        struct Restore(Option<RepairMode>);
        impl Drop for Restore {
            fn drop(&mut self) {
                REPAIR_OVERRIDE.with(|c| c.set(self.0));
            }
        }
        let _restore = Restore(REPAIR_OVERRIDE.with(|c| c.replace(Some(mode))));
        f()
    }
}

thread_local! {
    /// §NB5-L2 commit-necessity audit — when `Some`, the CEGAR loop's **Mode-A** commit records every
    /// `(committed slot, round)` pair here. `None` (the default) = OFF, zero overhead on the sweep/suite
    /// path. Only the audit driver (`bo_c1::run::run_necessity_audit`) turns it on, via `with_capture`.
    /// Mode-A ONLY: the audit measures the shipped repair mode; the `Lemmas` branch (dead axis) is not
    /// captured. Nesting is unsupported (the audit never nests).
    static AUDIT_CAPTURE: RefCell<Option<Vec<(SlotRef, usize)>>> = const { RefCell::new(None) };
    /// Diagnosis-only detailed origin for each Mode-A commit. Kept separate
    /// from the frozen necessity-audit tuple surface.
    static SELECTOR_CORE_COMMIT_CAPTURE: RefCell<Option<Vec<ModeACommitTrace>>> =
        const { RefCell::new(None) };
}

#[derive(Clone, Debug)]
pub(crate) struct ModeACommitTrace {
    pub target: SlotRef,
    pub round: usize,
    pub conflict: SlotConflict,
}

/// §NB5-L2 — run `f` while CAPTURING Mode-A's `(slot, round)` commit events, returning
/// `(f's result, the captured events in commit order)`. Panic-safe drop-guard (like
/// `RepairMode::with_override`): the prior capture state is restored on exit including on unwind, so a
/// panicking anchor run never leaks a live buffer onto the thread. The event order is the loop's
/// natural commit order; the audit dedups to the distinct commit SET itself.
pub(crate) fn with_capture<T>(f: impl FnOnce() -> T) -> (T, Vec<(SlotRef, usize)>) {
    struct Restore(Option<Vec<(SlotRef, usize)>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            AUDIT_CAPTURE.with(|c| *c.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(AUDIT_CAPTURE.with(|c| c.replace(Some(Vec::new()))));
    let out = f();
    let captured = AUDIT_CAPTURE
        .with(|c| c.borrow_mut().take())
        .unwrap_or_default();
    (out, captured)
}

/// Diagnosis-only detailed twin of `with_capture`. It records the originating
/// conflict edge for the second-order attribution of any tracked
/// `borrow-exclusion` core member.
pub(crate) fn with_mode_a_commit_trace<T>(f: impl FnOnce() -> T) -> (T, Vec<ModeACommitTrace>) {
    struct Restore(Option<Vec<ModeACommitTrace>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SELECTOR_CORE_COMMIT_CAPTURE.with(|capture| {
                *capture.borrow_mut() = self.0.take();
            });
        }
    }
    let _restore =
        Restore(SELECTOR_CORE_COMMIT_CAPTURE.with(|capture| capture.replace(Some(Vec::new()))));
    let output = f();
    let trace = SELECTOR_CORE_COMMIT_CAPTURE
        .with(|capture| capture.borrow_mut().take())
        .unwrap_or_default();
    (output, trace)
}

/// A borrow conflict edge with its owners translated to BO `SlotRef`s. `Field` owners
/// are dropped in BB0 (Local-only); `issuer` is `None` for a non-`Assign` borrower.
#[derive(Clone, Debug)]
pub(crate) struct SlotConflict {
    pub issuer: Option<SlotRef>,
    pub requirers: Vec<SlotRef>,
    /// Exact ESC-GAP ② class marker, carried from the selected loan row. False preserves the
    /// ordinary A-prime repair menu byte-for-byte.
    pub(crate) esc_issuer_first: bool,
}

#[derive(Clone, Debug)]
struct WitnessedSlotConflict {
    conflict: SlotConflict,
    /// `None` for an A5 parameter edge (R617-1): no loan behind the conflict.
    loan: Option<usize>,
    stable_loan_key: Option<StableLoanKey>,
    invalidators: Vec<SlotRef>,
    /// R617-1: the invalidators that met the loan through an A5 overlap partner.
    overlap_invalidators: Vec<SlotRef>,
}

struct Revalidated<T> {
    conflicts: T,
    retirement: super::retirement::RetirementReview,
    reader_failures: Vec<super::licensing::reader_replay::Failure>,
    /// era-5c L01¹¹ (R668-4): with the raw-cause ledger on, each conflict's
    /// invalidating slots, in the order of `conflicts`' per-function lists (the
    /// L2 capture's, mapped as the witnessed replay maps them). Empty otherwise.
    edge_invalidators: FxHashMap<LocalDefId, Vec<Vec<SlotRef>>>,
}

fn finish_readers(
    scope: super::licensing::reader_replay::RoundScope,
) -> Vec<super::licensing::reader_replay::Failure> {
    let result = scope.finish();
    super::export::record(|export| {
        export.reader_replay = Some(result.receipts);
        export.traversal_replay = Some(result.traversal_receipts);
    });
    result.failures
}

fn finish_retirement(
    scope: super::retirement::RetirementScope,
) -> super::retirement::RetirementReview {
    let review = scope.finish();
    super::export::record(|export| {
        export.retirement_rounds.push(review.clone());
        export.source_retirement = Some(review.clone());
    });
    review
}

fn append_retirement_targets(
    conflicts: &mut FxHashMap<LocalDefId, Vec<SlotConflict>>,
    review: &super::retirement::RetirementReview,
) {
    for target in review.targets() {
        let row = review
            .conflicts
            .iter()
            .find(|row| row.target == target)
            .expect("retirement target witness");
        conflicts
            .entry(row.function)
            .or_default()
            .push(SlotConflict {
                issuer: Some(target),
                requirers: Vec::new(),
                esc_issuer_first: false,
            });
    }
}

/// Run the production borrow verifier with a ref-candidacy where a pointer local is a
/// candidate iff its depth-0 slot satisfies `is_ref`, and map the conflict edges back
/// to `SlotRef`s. `is_mutable` is applied to every pointer local (a clean conflict
/// needs mutable bases: `invalidates` skips immutable-provenance loans). Read-only.
pub(crate) fn revalidate(
    program: &RustProgram,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
    is_mutable: impl MutProvider + Copy,
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
    let origin_flows = super::origin_flow::analyze_program_origin_flow(program);
    revalidate_with_flows(program, slots, &origin_flows, is_ref, is_mutable)
}

fn revalidate_with_flows(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    is_ref: impl Fn(SlotRef) -> bool,
    is_mutable: impl MutProvider + Copy,
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
    let _entry_scope = super::protected_entry::for_model(program, slots, &is_ref);
    let retirement_scope = super::retirement::begin(program, slots, origin_flows, &is_ref);
    let is_ref = &is_ref;
    let cand = move |fn_did| {
        let universe = slots.fn_local_slots.get(&fn_did);
        move |local: Local| {
            universe
                .and_then(|u| u.slot_for_local_depth(local, 0))
                .is_some_and(|slot_id| is_ref(SlotRef::Local(fn_did, slot_id)))
        }
    };
    // §NB2: per-local mutability (was forced `true`). An immutable provenance's loan is
    // skipped by the invalidation walk, so shared reads of one base stop conflicting.
    let mutab = move |fn_did| move |local: Local| is_mutable.is_mutable(fn_did, local);
    // §NB3-3a: route to the forked BO engine or production (default = production during dev,
    // flips to Fork at 3a merge — A1). `cand`/`mutab` are `Copy` (all captures are Copy), so both
    // match arms may reference them; only one runs. Same signatures ⇒ 1:1 dispatch.
    let edges = match super::borrow_engine::ForkEngineMode::current() {
        super::borrow_engine::ForkEngineMode::Production => {
            borrow::borrow_conflicts(program, cand, mutab)
        }
        super::borrow_engine::ForkEngineMode::Fork => {
            super::borrow_engine::borrow_conflicts_with_flows(program, origin_flows, cand, mutab)
        }
    };

    let mut conflicts = map_edges_to_slots(slots, edges);
    let retirement = finish_retirement(retirement_scope);
    assert!(
        retirement.unresolved.is_empty(),
        "unresolved source retirement in diagnostic revalidation: {:?}",
        retirement.unresolved
    );
    append_retirement_targets(&mut conflicts, &retirement);
    conflicts
}

/// §8 BB2-i — the CEGAR validate seam **with union replay**. Like `revalidate` but
/// takes a *partial* candidacy: a pointer local's depth-0 slot is a `Ref` candidate
/// iff `is_ref`, induces a demotion+union iff `is_raw`, and is an `Owning`
/// non-candidate otherwise. Delegates to `borrow::borrow_conflicts_replaying`, which
/// replays the `tree_borrow_local` union the chosen `Raw` slots induce, so a partial
/// candidacy surfaces the model-dependent conflicts that `revalidate` (round-0) cannot.
/// This is the seam BB2-ii's CEGAR loop drives with the solved model's actual kinds.
pub(crate) fn revalidate_replaying(
    program: &RustProgram,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
    is_raw: impl Fn(SlotRef) -> bool,
    is_mutable: impl MutProvider + Copy,
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
    let origin_flows = super::origin_flow::analyze_program_origin_flow(program);
    revalidate_replaying_with_flows(
        program,
        slots,
        &origin_flows,
        is_ref,
        is_raw,
        is_mutable,
        None,
        None,
        None,
    )
}

pub(crate) fn revalidate_replaying_with_parameter_overlap(
    program: &RustProgram,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
    is_raw: impl Fn(SlotRef) -> bool,
    is_mutable: impl MutProvider + Copy,
    parameter_overlaps: &FxHashMap<LocalDefId, super::borrow_engine::ParameterOverlap>,
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
    let origin_flows = super::origin_flow::analyze_program_origin_flow(program);
    revalidate_replaying_with_flows(
        program,
        slots,
        &origin_flows,
        is_ref,
        is_raw,
        is_mutable,
        None,
        None,
        Some(parameter_overlaps),
    )
}

fn revalidate_replaying_with_flows(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    is_ref: impl Fn(SlotRef) -> bool,
    is_raw: impl Fn(SlotRef) -> bool,
    is_mutable: impl MutProvider + Copy,
    selected_copy_lends: Option<&SelectedCopyLendLoans>,
    escaped_copy_lends: Option<&SelectedCopyLendLoans>,
    parameter_overlaps: Option<&FxHashMap<LocalDefId, super::borrow_engine::ParameterOverlap>>,
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
    let mut reviewed = revalidate_replaying_reviewed(
        program,
        slots,
        origin_flows,
        is_ref,
        is_raw,
        is_mutable,
        selected_copy_lends,
        escaped_copy_lends,
        parameter_overlaps,
    );
    assert!(
        reviewed.reader_failures.is_empty(),
        "unresolved reader proof in diagnostic replay: {:?}",
        reviewed.reader_failures
    );
    assert!(
        reviewed.retirement.unresolved.is_empty(),
        "unresolved source retirement in diagnostic replay: {:?}",
        reviewed.retirement.unresolved
    );
    append_retirement_targets(&mut reviewed.conflicts, &reviewed.retirement);
    reviewed.conflicts
}

fn revalidate_replaying_reviewed(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    is_ref: impl Fn(SlotRef) -> bool,
    is_raw: impl Fn(SlotRef) -> bool,
    is_mutable: impl MutProvider + Copy,
    selected_copy_lends: Option<&SelectedCopyLendLoans>,
    escaped_copy_lends: Option<&SelectedCopyLendLoans>,
    parameter_overlaps: Option<&FxHashMap<LocalDefId, super::borrow_engine::ParameterOverlap>>,
) -> Revalidated<FxHashMap<LocalDefId, Vec<SlotConflict>>> {
    let reader_scope = super::licensing::reader_replay::begin_round(slots, &is_ref, &is_raw);
    let _entry_scope = super::protected_entry::for_model(program, slots, &is_ref);
    let retirement_scope = super::retirement::begin(program, slots, origin_flows, &is_ref);
    let is_ref = &is_ref;
    let is_raw = &is_raw;
    let cand = move |fn_did| {
        let universe = slots.fn_local_slots.get(&fn_did);
        move |local: Local| {
            universe
                .and_then(|u| u.slot_for_local_depth(local, 0))
                .is_some_and(|slot_id| is_ref(SlotRef::Local(fn_did, slot_id)))
        }
    };
    let raw = move |fn_did| {
        let universe = slots.fn_local_slots.get(&fn_did);
        move |local: Local| {
            universe
                .and_then(|u| u.slot_for_local_depth(local, 0))
                .is_some_and(|slot_id| is_raw(SlotRef::Local(fn_did, slot_id)))
        }
    };
    // §NB2: per-local mutability (was forced `true`). An immutable provenance's loan is
    // skipped by the invalidation walk, so shared reads of one base stop conflicting.
    let mutab = move |fn_did| move |local: Local| is_mutable.is_mutable(fn_did, local);
    // §NB5-F2 — the model's Raw FIELD slots, bridged to `borrow::StructFieldSlot`, so the fork can
    // disable their loans (the field analogue of the Local raw candidacy above). Only the Fork arm
    // consumes them; production stays frozen at its 4-arg signature.
    let raw_fields: Vec<borrow::StructFieldSlot> = (0..slots.field_slots.len())
        .map(SlotId::from_usize)
        .filter(|&sid| slots.field_slots.slot(sid).depth == 0 && is_raw(SlotRef::Field(sid)))
        .filter_map(|sid| match slots.field_slots.slot(sid).owner {
            SlotOwner::Field(f) => Some(borrow::StructFieldSlot {
                struct_did: f.struct_did,
                field_index: f.field_index,
            }),
            SlotOwner::Local(_) => None,
        })
        .collect();
    // §NB3-3a: route to the forked BO engine or production (default = production during dev,
    // flips to Fork at 3a merge — A1). All closures are `Copy`, so both arms may reference them.
    let replay = || match super::borrow_engine::ForkEngineMode::current() {
        super::borrow_engine::ForkEngineMode::Production => {
            assert!(
                selected_copy_lends.is_none_or(|selected| selected.is_empty())
                    && escaped_copy_lends.is_none_or(|selected| selected.is_empty())
                    && parameter_overlaps.is_none(),
                "CopyLend/A5 replay requires the BO fork engine"
            );
            borrow::borrow_conflicts_replaying(program, cand, raw, mutab)
        }
        super::borrow_engine::ForkEngineMode::Fork => {
            if let Some(parameter_overlaps) = parameter_overlaps {
                let empty = SelectedCopyLendLoans::default();
                super::borrow_engine::borrow_conflicts_replaying_with_flows_and_parameter_overlap_and_escaped(
                    program,
                    origin_flows,
                    cand,
                    raw,
                    mutab,
                    &raw_fields,
                    selected_copy_lends.unwrap_or(&empty),
                    escaped_copy_lends.unwrap_or(&empty),
                    parameter_overlaps,
                )
            } else {
                match selected_copy_lends {
                    Some(selected) => {
                        super::borrow_engine::borrow_conflicts_replaying_with_flows_and_copy_lends_and_escaped(
                            program,
                            origin_flows,
                            cand,
                            raw,
                            mutab,
                            &raw_fields,
                            selected,
                            escaped_copy_lends.unwrap_or(&SelectedCopyLendLoans::default()),
                        )
                    }
                    None => super::borrow_engine::borrow_conflicts_replaying_with_flows(
                        program,
                        origin_flows,
                        cand,
                        raw,
                        mutab,
                        &raw_fields,
                    ),
                }
            }
        }
    };

    // era-5c L01¹¹ (R668-4): the ledger records each Mode-A commit's clause, so
    // the replay records each edge's invalidators (observation only).
    let (edges, invalidators) = if super::raw_cause::records_invalidators() {
        super::borrow_engine::recording_edge_invalidators(replay)
    } else {
        (replay(), FxHashMap::default())
    };
    let edge_invalidators = invalidators
        .into_iter()
        .map(|(fn_did, per_edge)| {
            let per_edge = per_edge
                .into_iter()
                .map(|locals| {
                    let mut invalidators = locals
                        .into_iter()
                        .filter_map(|local| {
                            owner_to_slot(slots, fn_did, ProvenanceOwner::Local(local))
                        })
                        .collect::<Vec<_>>();
                    invalidators.sort_by_key(slotref_key);
                    invalidators.dedup();
                    invalidators
                })
                .collect();
            (fn_did, per_edge)
        })
        .collect();
    Revalidated {
        conflicts: map_edges_to_slots(slots, edges),
        edge_invalidators,
        retirement: finish_retirement(retirement_scope),
        reader_failures: finish_readers(reader_scope),
    }
}

/// L2-only replay adapter carrying the invalidating access roots captured by
/// the BO fork. The ordinary replay adapter above remains byte-for-byte on its
/// existing shape and performs no L2 collection.
fn revalidate_replaying_witnessed(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    is_ref: impl Fn(SlotRef) -> bool,
    is_raw: impl Fn(SlotRef) -> bool,
    is_mutable: impl MutProvider + Copy,
    selected_copy_lends: Option<&SelectedCopyLendLoans>,
    escaped_copy_lends: Option<&SelectedCopyLendLoans>,
    parameter_overlaps: Option<&FxHashMap<LocalDefId, super::borrow_engine::ParameterOverlap>>,
) -> Revalidated<FxHashMap<LocalDefId, Vec<WitnessedSlotConflict>>> {
    let reader_scope = super::licensing::reader_replay::begin_round(slots, &is_ref, &is_raw);
    let _entry_scope = super::protected_entry::for_model(program, slots, &is_ref);
    let retirement_scope = super::retirement::begin(program, slots, origin_flows, &is_ref);
    let is_ref = &is_ref;
    let is_raw = &is_raw;
    let cand = move |fn_did| {
        let universe = slots.fn_local_slots.get(&fn_did);
        move |local: Local| {
            universe
                .and_then(|u| u.slot_for_local_depth(local, 0))
                .is_some_and(|slot_id| is_ref(SlotRef::Local(fn_did, slot_id)))
        }
    };
    let raw = move |fn_did| {
        let universe = slots.fn_local_slots.get(&fn_did);
        move |local: Local| {
            universe
                .and_then(|u| u.slot_for_local_depth(local, 0))
                .is_some_and(|slot_id| is_raw(SlotRef::Local(fn_did, slot_id)))
        }
    };
    let mutab = move |fn_did| move |local: Local| is_mutable.is_mutable(fn_did, local);
    let raw_fields: Vec<borrow::StructFieldSlot> = (0..slots.field_slots.len())
        .map(SlotId::from_usize)
        .filter(|&sid| slots.field_slots.slot(sid).depth == 0 && is_raw(SlotRef::Field(sid)))
        .filter_map(|sid| match slots.field_slots.slot(sid).owner {
            SlotOwner::Field(f) => Some(borrow::StructFieldSlot {
                struct_did: f.struct_did,
                field_index: f.field_index,
            }),
            SlotOwner::Local(_) => None,
        })
        .collect();
    assert_eq!(
        super::borrow_engine::ForkEngineMode::current(),
        super::borrow_engine::ForkEngineMode::Fork,
        "L2 witnessed invalidator capture requires CRAT_BO_FORK_ENGINE=fork (or the unset fork default)"
    );
    let edges = match (selected_copy_lends, parameter_overlaps) {
        // R617-1: A5's overlap pairs in the witness context, as in Mode-A's replay.
        (selected, Some(parameter_overlaps)) => {
            let empty = SelectedCopyLendLoans::default();
            super::borrow_engine::borrow_conflicts_replaying_witnessed_with_flows_and_parameter_overlap_and_escaped(
                program,
                origin_flows,
                cand,
                raw,
                mutab,
                &raw_fields,
                selected.unwrap_or(&empty),
                escaped_copy_lends.unwrap_or(&empty),
                parameter_overlaps,
            )
        }
        (Some(selected), None) => {
            super::borrow_engine::borrow_conflicts_replaying_witnessed_with_copy_lends_and_escaped(
                program,
                origin_flows,
                cand,
                raw,
                mutab,
                &raw_fields,
                selected,
                escaped_copy_lends.unwrap_or(&SelectedCopyLendLoans::default()),
            )
        }
        (None, None) => super::borrow_engine::borrow_conflicts_replaying_witnessed(
            program,
            origin_flows,
            cand,
            raw,
            mutab,
            &raw_fields,
        ),
    };

    let conflicts = edges
        .into_iter()
        .map(|(fn_did, fn_edges)| {
            let translated = fn_edges
                .into_iter()
                .map(|witnessed| {
                    let loan = witnessed.loan;
                    let loan_location = witnessed.loan_location;
                    let edge = witnessed.edge;
                    let issuer = edge
                        .issuer
                        .and_then(|owner| owner_to_slot(slots, fn_did, owner));
                    let to_slots = |locals: Vec<Local>| {
                        let mut slots_of = locals
                            .into_iter()
                            .filter_map(|local| {
                                owner_to_slot(slots, fn_did, ProvenanceOwner::Local(local))
                            })
                            .collect::<Vec<_>>();
                        slots_of.sort_by_key(slotref_key);
                        slots_of.dedup();
                        slots_of
                    };
                    let invalidators = to_slots(witnessed.invalidators);
                    let overlap_invalidators = to_slots(witnessed.overlap_invalidators);
                    if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                        eprintln!(
                            "E5C witnessed-conflict fn={fn_did:?} loan={loan:?} at={loan_location:?} issuer={issuer:?} requirers={:?} invalidators={invalidators:?} via_partner={overlap_invalidators:?} esc={}",
                            edge.requirers, edge.esc_issuer_first
                        );
                    }
                    WitnessedSlotConflict {
                        conflict: SlotConflict {
                            issuer,
                            requirers: edge
                                .requirers
                                .into_iter()
                                .filter_map(|owner| owner_to_slot(slots, fn_did, owner))
                                .collect(),
                            esc_issuer_first: edge.esc_issuer_first,
                        },
                        loan,
                        stable_loan_key: issuer.zip(loan_location).map(|(issuer, location)| {
                            StableLoanKey::new(fn_did.local_def_index.as_u32(), issuer, location)
                        }),
                        invalidators,
                        overlap_invalidators,
                    }
                })
                .collect();
            (fn_did, translated)
        })
        .collect();
    Revalidated {
        conflicts,
        edge_invalidators: FxHashMap::default(),
        retirement: finish_retirement(retirement_scope),
        reader_failures: finish_readers(reader_scope),
    }
}

/// Translate borrow `ConflictEdge`s (keyed by function) into BO `SlotConflict`s,
/// mapping each `Local` owner to its depth-0 slot (`Field` owners dropped). Shared by
/// `revalidate` (round-0) and `revalidate_replaying` (CEGAR).
fn map_edges_to_slots(
    slots: &CrateSlots,
    edges: FxHashMap<LocalDefId, Vec<ConflictEdge>>,
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
    edges
        .into_iter()
        .map(|(fn_did, fn_edges)| {
            let translated = fn_edges
                .into_iter()
                .map(|e| SlotConflict {
                    issuer: e.issuer.and_then(|o| owner_to_slot(slots, fn_did, o)),
                    requirers: e
                        .requirers
                        .into_iter()
                        .filter_map(|o| owner_to_slot(slots, fn_did, o))
                        .collect(),
                    esc_issuer_first: e.esc_issuer_first,
                })
                .collect();
            (fn_did, translated)
        })
        .collect()
}

/// §8 BB1 — encode Round-0 borrow conflicts as exclusion guards on the solver. For
/// each conflict edge, assert `¬ref(issuer) ∨ ⋁¬ref(requirers)` via
/// `KindSolver::add_borrow_exclusion`. Hard clauses, applied before the single
/// `model_kinds_relaxing` solve. BB1 is one shot: it encodes the round-0 (all-Ref)
/// conflicts only — the CEGAR validate/re-solve loop that closes over the solved
/// model's actual candidacy is BB2, so BB1 alone is not yet sound on its own.
///
/// Edges with `Field` owners are partially dropped by BB0's Local-only mapping: an
/// all-`Field` edge becomes a NO-OP (the deferred field-exclusivity gap), and a mixed
/// edge keeps only its surviving `Local` literals — a *stronger* (still sound: forces
/// ≥1 off Ref) but over-constraining guard. Both resolve when the struct field-slot
/// mapping lands; a precision concern only post-BB2.
pub(crate) fn materialize_guards(
    solver: &KindSolver,
    conflicts: &FxHashMap<LocalDefId, Vec<SlotConflict>>,
) {
    for edge in conflicts.values().flatten() {
        solver.add_borrow_exclusion(edge.issuer, &edge.requirers);
    }
}

/// §8 BB2-ii — drive the CEGAR validate/re-solve loop to a fixpoint (Mode A).
///
/// The solver must arrive with ownership constraints + per-fn coherence already
/// emitted (so `selectors` are its retractable owning assumptions — §NB-F:
/// malloc SOURCES and free/realloc SINKS alike; dropping a sink LEAKS THE
/// FREE, an unprovable free staying a raw-pointer free). §NB0: the BB3-a
/// invariant (`¬ref` on every malloc-source slot — a malloc result owns heap and is
/// not a borrow; see `sources::collect_malloc_source_slots`) is now emitted EAGERLY
/// by `emit_crate_ownership_constraints`, so no model this loop ever sees can mark a
/// source `Ref` and the old lazy per-round source commit is gone. Each round: solve →
/// derive the candidacy from the model's *actual* Raw/Ref/Owning kinds → commit `¬ref`
/// on **one representative slot per residual borrow conflict** (BB2-ii — §NB4-4a **A′**: a
/// live `Ref` requirer *beyond* the issuer if one exists, else the issuer; see
/// `representative`; conflicts come from `revalidate_replaying`'s `tree_borrow_local`
/// union replay) → re-solve. Accept when no committable (currently-`Ref`) slot remains.
///
/// Mode A = *monotone single-slot commitment*, deliberately NOT BB1's disjunctive
/// `materialize_guards`. Committing one currently-`Ref` slot forces exactly that slot off
/// `Ref`, so the *committed* slot is the demotion witness `revalidate_replaying` expects.
/// (A disjunctive guard instead lets the solver satisfy `¬ref(a) ∨ ¬ref(b)` by demoting a
/// *non-minimal* slot — the reason this loop commits one slot, not guards an edge.) Note
/// this makes the *committed* slot a witness, but coherence's flow-insensitive equate
/// can still drag a non-committed slot `Raw` (a DEAD copy `let _r = p`); that is a
/// non-witness-but-*inert* slot handled by `borrow_conflicts_replaying`'s relaxed
/// inert-ness invariant, not a witness this loop produces.
///
/// No separate all-Ref round-0 step is needed: the first solve has no commitments, so
/// the MaxSMT objective settles every source-free slot to `Ref` and the first iteration
/// validates that model directly — coinciding with BB1's round-0 only in the
/// source-free case; with an ownership source the first model legitimately carries
/// `Owning` slots and we validate *those*.
///
/// Termination: each non-accepting round commits ≥1 fresh slot to `¬ref` (a slot that
/// was `Ref` this round and never can be again), so the loop runs ≤ |slots| rounds. The
/// round cap is a panic backstop, not the termination proof.
///
/// Returns `None` if a re-solve is UNSAT (every involved slot pinned `Ref` by hard
/// ownership facts — see `KindSolver::add_borrow_exclusion`); callers must treat that
/// as a real possibility.
///
/// SCOPE / SOUNDNESS: an accepted model is accepted **for the current local-only,
/// depth-0 experimental pass — NOT a proof of global borrow-validity.** Two gaps stay
/// deferred to BB3, sound only because BO output is unconsumed by codegen (the §8
/// guardrail): (1) a residual conflict all of whose owners are `Field` (dropped by the
/// Local-only mapping) has no committable slot and is accepted (the deferred struct
/// field-slot mapping); (2) an `Owning` slot issues no loan, so a conflict *caused by*
/// an `Owning` pointer is invisible to the replay and an accepted model may hide it.
pub(crate) fn verify_to_fixpoint(
    program: &RustProgram,
    slots: &CrateSlots,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    let origin_flows = super::origin_flow::analyze_program_origin_flow(program);
    verify_to_fixpoint_with_flows(program, slots, &origin_flows, solver, selectors, is_mutable)
}

pub(crate) fn verify_to_fixpoint_with_flows(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    // §NB5-M: thin wrapper over the single counting loop (model only). KEEP THIN — any logic
    // added here but not in `verify_to_fixpoint_counting` diverges the sweep's counters from what
    // the suite verifies (exactly the mirror-drift the retired bo_c1 mirror guarded; wrapper-
    // thinness is now the guard — see `verify_to_fixpoint_is_thin_wrapper`).
    verify_to_fixpoint_counting_with_flows(
        program,
        slots,
        origin_flows,
        solver,
        selectors,
        is_mutable,
    )
    .0
}

/// §NB5-M CEGAR round/commit counters, native to the fork — retires the bo_c1 mirror
/// (`mirror::verify_to_fixpoint_counting`). `None` (decline) carries the stats of the rounds that
/// ran. `verify_to_fixpoint` is the model-only wrapper over this.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RoundStats {
    /// Validate rounds run, INCLUDING the accepting round (accept-first-model ⇒ `rounds == 1`).
    pub rounds: usize,
    /// §NB0: every commit is a conflict commit (the `¬ref(source)` invariant is emitted eagerly).
    pub commits_conflict: usize,
    pub commits_per_round: Vec<usize>,
    /// Exact CopyLend loan identities handed to the final replay round. This is a wiring receipt,
    /// not a model-derived recount: suppressing replay registration must drive it to zero.
    pub copy_lend_replay_selections: usize,
    /// §NB-F: sink selectors the FINAL solve dropped (leaked frees).
    pub dropped_sinks: usize,
    /// §NB-F: source selectors the FINAL solve dropped (leaked allocs).
    pub dropped_sources: usize,
    /// §NB5-F: set when the loop declined because a residual borrow conflict named a non-`Ref`
    /// FIELD slot (the A′ principle extended to field requirers — the field is a live requirer the
    /// Local-only replay candidacy cannot soundly demote, so decline is the sound outcome). Carries
    /// the offending field slot for the sweep's per-program attribution (which field). `None` for an
    /// accept or an UNSAT-family decline (bo_c1 classifies those via its selector-core
    /// `decline_reason`).
    pub field_conflict_decline: Option<SlotRef>,
    /// Diagnostic twin of `field_conflict_decline`: the accepted round model's
    /// exact non-Ref kind for that field.
    pub field_conflict_kind: Option<SlotKind>,
    /// §NB5-L guard 3 — the `RepairMode` that produced these stats (the mode-stamp). Self-describing
    /// results: the sweep row and any `RoundStats` dump say which repair strategy ran, so the S7
    /// differential is never mode-ambiguous. Defaults to `ModeA` (= `RepairMode::DEFAULT`).
    pub repair: RepairMode,
    /// §NB5-L (Codex MEDIUM) — set when the loop declined because the `Lemmas` round cap was exhausted
    /// (the controlled backstop for a hypothetical subset-oscillation blowup, which does not manifest
    /// empirically). A distinct decline KIND: `bo_c1` must tag it before `decline_reason`, which would
    /// otherwise mislabel this relaxed-SAT decline as `sat-in-replay` and hide the cap exhaustion. Never
    /// set under `ModeA` (that path panics — its linear bound is proven).
    pub cap_exhausted: bool,
    /// L2 feature-on controlled decline. The legacy feature-off Mode-A and
    /// Lemmas paths leave this unset.
    pub l2_decline: Option<L2DeclineReason>,
    /// Typed source-retirement coverage failure, separate from solver outcome.
    pub source_retirement_decline: Vec<super::retirement::RetirementUnresolved>,
    /// R617-1 STOP 2 (R631-7): set when a `Guarded` run declined and the program
    /// fell back to Mode-A. These stats are then the Mode-A run's, stamped
    /// `repair = Guarded`; the receipt reads `repair=guarded->mode-a`.
    pub guarded_fallback: Option<GuardedFallback>,
}

/// R617-1 STOP 2: the declined guarded run behind a Mode-A fallback.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GuardedFallback {
    /// The guarded run's decline, as its receipt names it.
    pub reason: String,
    pub rounds: usize,
    pub commits: usize,
}

impl GuardedFallback {
    fn of(stats: &RoundStats) -> Self {
        let reason = if let Some(reason) = &stats.l2_decline {
            reason
                .diagnostic_label(stats.rounds)
                .rsplit_once("reason=")
                .map_or_else(|| "l2".to_owned(), |(_, detail)| detail.replace('|', ";"))
        } else if stats.field_conflict_decline.is_some() {
            "field-conflict".to_owned()
        } else if !stats.source_retirement_decline.is_empty() {
            "source-retirement".to_owned()
        } else {
            "round-decline".to_owned()
        };
        Self {
            reason,
            rounds: stats.rounds,
            commits: stats.commits_conflict,
        }
    }
}

fn record_dropped(stats: &mut RoundStats, selectors: &Selectors, dropped: &[Bool]) {
    stats.dropped_sinks = dropped
        .iter()
        .filter(|item| selectors.is_sink(item))
        .count();
    stats.dropped_sources = dropped.len() - stats.dropped_sinks;
}

#[derive(Clone, Copy)]
pub(super) enum LoopBackend {
    LegacyOptimize,
    HardCheckRoundOptimize,
}

/// era-5c R545-1: the mutability facts of one verification round. Foster's load
/// guard (`lhs = copy (*p)…` ⇒ `p` mutable) is kept unless the LOADED level is
/// `Raw` in `model`: writes through a Raw level are raw-pointer writes, so the
/// table they were loaded from is only read and its reborrow is shared. A level
/// the walk cannot map keeps the guard.
pub(crate) fn round_mutability_facts<'tcx>(
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> super::mutability_facts::MutFacts {
    let tcx = program.tcx;
    let keep_load = |fn_did: LocalDefId, load: &rustc_middle::mir::Place<'tcx>| -> bool {
        // W47 fault F2 (test builds only): the model condition dropped.
        #[cfg(test)]
        if std::env::var("CRAT_E5C_W47_FAULT").as_deref() == Ok("no-model") {
            return true;
        }
        match loaded_slot(tcx, slots, fn_did, load) {
            Some(slot) => model.get(&slot) != Some(&SlotKind::Raw),
            None => true,
        }
    };
    super::mutability_facts::MutFacts::from_program_gated(program, &keep_load)
}

/// The slot of the pointer VALUE a place names: `(*p)` is `p@d1`, `(*p).f` is
/// field `f@d0`, `(*(*p).f)` is `f@d1`; indexing keeps the level. `None` when the
/// walk leaves the slot universe (unions, tuples, downcasts, unregistered owners).
fn loaded_slot<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    place: &rustc_middle::mir::Place<'tcx>,
) -> Option<SlotRef> {
    use rustc_middle::mir::ProjectionElem;
    let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
    let mut ty = body.local_decls[place.local].ty;
    let mut field: Option<super::slots::StructFieldSlot> = None;
    let mut depth: u8 = 0;
    for elem in place.projection.iter() {
        match elem {
            ProjectionElem::Deref => {
                depth = depth.checked_add(1)?;
                ty = ty.builtin_deref(true)?;
            }
            ProjectionElem::Field(index, field_ty) => {
                let rustc_middle::ty::TyKind::Adt(adt, _) = ty.kind() else {
                    return None;
                };
                if !adt.is_struct() {
                    return None;
                }
                field = Some(super::slots::StructFieldSlot {
                    struct_did: adt.did().as_local()?,
                    field_index: index.index(),
                });
                depth = 0;
                ty = field_ty;
            }
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                ty = ty.builtin_index()?;
            }
            _ => return None,
        }
    }
    match field {
        Some(field) => slots
            .field_slots
            .slot_for_field_depth(field, depth)
            .map(SlotRef::Field),
        None => slots
            .fn_local_slots
            .get(&fn_did)?
            .slot_for_local_depth(place.local, depth)
            .map(|id| SlotRef::Local(fn_did, id)),
    }
}

fn solve_round_model(
    solver: &KindSolver,
    selectors: &Selectors,
    backend: LoopBackend,
    hard: Option<&HardLoopSolver>,
) -> Option<(FxHashMap<SlotRef, SlotKind>, Vec<Bool>)> {
    match backend {
        LoopBackend::LegacyOptimize => solver.model_kinds_relaxing_reporting(selectors),
        LoopBackend::HardCheckRoundOptimize => {
            let hard = hard.expect("R1a validation owns a hard checker");
            let relaxed = solver.relax_selectors_hard_reporting(hard, selectors)?;
            let dropped = relaxed.dropped().to_vec();
            let model = solver.optimized_model_under(&relaxed)?;
            Some((model, dropped))
        }
    }
}

fn solve_l2_round_model(
    solver: &KindSolver,
    selectors: &Selectors,
    backend: LoopBackend,
    hard: Option<&HardLoopSolver>,
) -> L2SolveResult {
    match backend {
        LoopBackend::LegacyOptimize => solver.model_kinds_relaxing_reporting_l2(selectors),
        LoopBackend::HardCheckRoundOptimize => solver.model_kinds_decomposed_reporting_l2(
            hard.expect("R1a L2 validation owns a hard checker"),
            selectors,
        ),
    }
}

/// R617-1: one round's solve. Mode-A and Lemmas solve as they always have; `Guarded` solves the
/// same system through the typed twin, so a solver decline is recorded in the planner's taxonomy.
fn solve_round(
    solver: &KindSolver,
    selectors: &Selectors,
    backend: LoopBackend,
    hard: Option<&HardLoopSolver>,
    planner: Option<&Planner>,
    stats: &mut RoundStats,
    diagnostics_enabled: bool,
) -> Option<(FxHashMap<SlotRef, SlotKind>, Vec<Bool>)> {
    let Some(planner) = planner else {
        return solve_round_model(solver, selectors, backend, hard);
    };
    let decline = match solve_l2_round_model(solver, selectors, backend, hard) {
        L2SolveResult::Sat { kinds, dropped } => return Some((kinds, dropped)),
        L2SolveResult::Unsat => L2SolverDecline::Unsat,
        L2SolveResult::Unknown => L2SolverDecline::Unknown,
    };
    record_l2_decline(
        stats,
        planner.validation_rounds(),
        L2DeclineReason::Solver(decline),
        diagnostics_enabled,
    );
    None
}

fn selected_copy_lends_for_round(
    program: &RustProgram,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    pair_lends: Option<&FxHashSet<CopyLendPair>>,
    escaped: Option<&SelectedCopyLendLoans>,
) -> SelectedCopyLendLoans {
    let mut selected = escaped.cloned().unwrap_or_default();
    // W52 fault (test builds only): the lend's loans never reach the replay.
    #[cfg(test)]
    let pair_lends =
        pair_lends.filter(|_| std::env::var("CRAT_E5C_W52_FAULT").as_deref() != Ok("no-loan"));
    if let Some(pairs) = pair_lends {
        for (fn_did, loans) in selected_copy_lend_sites(program, slots, pairs, model) {
            selected.entry(fn_did).or_default().extend(loans);
        }
    }
    selected
}

fn selected_copy_lend_count(selected: &SelectedCopyLendLoans) -> usize {
    selected.values().map(FxHashSet::len).sum()
}

/// The §8 BB2-ii CEGAR validate/re-solve loop (Mode A) with native counters. See
/// `verify_to_fixpoint`'s contract above for scope/soundness. Uses `model_kinds_relaxing_reporting`
/// (identical model to the plain twin the wrapper's callers used, plus the dropped-selector set for
/// the leak counts).
pub(crate) fn verify_to_fixpoint_counting(
    program: &RustProgram,
    slots: &CrateSlots,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    let origin_flows = super::origin_flow::analyze_program_origin_flow(program);
    verify_to_fixpoint_counting_with_flows(
        program,
        slots,
        &origin_flows,
        solver,
        selectors,
        is_mutable,
    )
}

pub(crate) fn verify_to_fixpoint_counting_with_flows(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    verify_to_fixpoint_counting_with_flows_impl(
        program,
        slots,
        origin_flows,
        solver,
        selectors,
        is_mutable,
        None,
        None,
        None,
        LoopBackend::HardCheckRoundOptimize,
    )
}

pub(crate) fn verify_to_fixpoint_counting_with_flows_and_copy_lends(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
    copy_lends: &FxHashSet<CopyLendPair>,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    verify_to_fixpoint_counting_with_flows_impl(
        program,
        slots,
        origin_flows,
        solver,
        selectors,
        is_mutable,
        Some(copy_lends),
        None,
        None,
        LoopBackend::HardCheckRoundOptimize,
    )
}

pub(crate) fn verify_to_fixpoint_counting_with_flows_and_parameter_overlaps(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
    parameter_overlaps: &FxHashMap<LocalDefId, super::borrow_engine::ParameterOverlap>,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    verify_to_fixpoint_counting_with_flows_impl(
        program,
        slots,
        origin_flows,
        solver,
        selectors,
        is_mutable,
        None,
        None,
        Some(parameter_overlaps),
        LoopBackend::HardCheckRoundOptimize,
    )
}

pub(super) fn verify_to_fixpoint_counting_with_flows_impl(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
    copy_lends: Option<&FxHashSet<CopyLendPair>>,
    escaped_copy_lends: Option<&SelectedCopyLendLoans>,
    parameter_overlaps: Option<&FxHashMap<LocalDefId, super::borrow_engine::ParameterOverlap>>,
    backend: LoopBackend,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    let _reader_facts = super::licensing::reader_replay::enter_facts(solver.ownership_facts());
    let source_inventory = super::source_events::for_construction(program);
    let _source_scope = super::source_events::enter_inventory(&source_inventory);
    super::source_events::record_replay();
    // §NB-R guard (release-active): a tracked solver's hard constraints are
    // track-gated; every solve in this loop would be vacuously SAT and the
    // accepted model meaningless. Tracked instances belong to the explain path.
    assert!(
        !solver.is_diagnostic_tracked(),
        "diagnostic-tracked KindSolver must not enter verify_to_fixpoint"
    );
    let repair = RepairMode::current();
    let rounds = |repair| {
        verify_rounds(
            program,
            slots,
            origin_flows,
            solver,
            selectors,
            is_mutable,
            copy_lends,
            escaped_copy_lends,
            parameter_overlaps,
            backend,
            repair,
        )
    };
    if repair != RepairMode::Guarded {
        return rounds(repair);
    }
    // R617-1 STOP 2 (R631-7): a guarded decline falls back to Mode-A for this program. The
    // guarded run's assertions (its clauses, pins and the field-ownership constraints the loop
    // asserts first) live in a scope that is popped before the Mode-A run, so that run sees the
    // solver exactly as a Mode-A-only run would. An accepting guarded run keeps its scope, as a
    // Mode-A run keeps its commits.
    solver.push_scope();
    let (model, guarded) = rounds(RepairMode::Guarded);
    if model.is_some() {
        return (model, guarded);
    }
    solver.pop_scope();
    let fallback = GuardedFallback::of(&guarded);
    if l2::diagnostics_enabled_from_env() {
        eprintln!(
            "[bo-l2] event=guarded_fallback|reason={}|rounds={}|commits={}",
            fallback.reason, fallback.rounds, fallback.commits
        );
    }
    let (model, mut stats) = rounds(RepairMode::ModeA);
    stats.repair = RepairMode::Guarded;
    stats.guarded_fallback = Some(fallback);
    (model, stats)
}

/// The validate/re-solve rounds of one repair mode (R617-1: the one loop). `Guarded` differs from
/// Mode-A only at the commit point, in its witnessed replay, and in its typed solver declines.
fn verify_rounds(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
    copy_lends: Option<&FxHashSet<CopyLendPair>>,
    escaped_copy_lends: Option<&SelectedCopyLendLoans>,
    parameter_overlaps: Option<&FxHashMap<LocalDefId, super::borrow_engine::ParameterOverlap>>,
    backend: LoopBackend,
    repair: RepairMode,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    // R617-1: the guarded planner lives across rounds, and is told of every round -- the
    // retirement pins' and the field-own repair's as empty ones -- so its validation counter
    // stays equal to `stats.rounds`. Its own cap (10S + 1) bounds the guarded rounds.
    let diagnostics_enabled = repair == RepairMode::Guarded && l2::diagnostics_enabled_from_env();
    let mut planner = (repair == RepairMode::Guarded).then(|| {
        let slot_count = slots
            .fn_local_slots
            .values()
            .try_fold(slots.field_slots.len(), |count, universe| {
                count.checked_add(universe.len())
            })
            .expect("L2 registered-slot count overflow");
        Planner::new(slot_count)
    });
    let cap = match &planner {
        Some(planner) => planner.validation_cap().saturating_add(1),
        None => round_cap(slots),
    };
    // §9.10.2 — constrain each struct-field slot's ownership to `field.own <=> AND(stored
    // owns)`, so a field mixing an owned source and a borrowed value settles non-Owning (the
    // flow-insensitive global-field over-claim). Must precede the first solve.
    super::coherence::constrain_field_ownership(solver, slots, program);
    let hard =
        matches!(backend, LoopBackend::HardCheckRoundOptimize).then(|| solver.hard_loop_solver());
    let mut stats = RoundStats::default();
    // §NB5-L guard 1 — resolve the repair strategy ONCE per invocation into a local; NO mid-loop
    // re-reads, so the whole fixpoint runs one consistent strategy. Guard 3 stamps it into `stats`.
    stats.repair = repair;
    let Some((mut model, dropped)) = solve_round(
        solver,
        selectors,
        backend,
        hard.as_ref(),
        planner.as_ref(),
        &mut stats,
        diagnostics_enabled,
    ) else {
        return (None, stats);
    };
    record_dropped(&mut stats, selectors, &dropped);
    // era-5c R607-1: the raw-cause ledger's inputs -- every Mode-A commit with
    // its track, and the selectors the accepted round dropped.
    let ledger = super::raw_cause::enabled();
    let mut ledger_commits: Vec<super::raw_cause::Commit> = Vec::new();
    let mut last_dropped = dropped;
    for _ in 0..cap {
        stats.rounds += 1;
        // D1: each round re-runs the oracle under a DIFFERENT candidacy
        // predicate. Reset so the export holds the FINAL round's BorrowSet,
        // not the union over rejected intermediate models.
        super::export::begin_round();
        let _original_cell_model =
            super::licensing::model_selection::enter(solver.original_cell_selection());
        let active_escaped_copy_lends = escaped_copy_lends
            .map(|escaped| super::esc_minimal::active_loans_for_model(escaped, &model));
        let _retirement_model = super::retirement::model_scope(&model);
        let selected_copy_lends = selected_copy_lends_for_round(
            program,
            slots,
            &model,
            copy_lends,
            active_escaped_copy_lends.as_ref(),
        );
        stats.copy_lend_replay_selections = selected_copy_lend_count(&selected_copy_lends);
        let selected_copy_lends =
            (stats.copy_lend_replay_selections != 0).then_some(selected_copy_lends);
        // R545-1: a table's reborrow is unique only when a Ref level below it is
        // written -- the round's facts drop the load guard where the loaded level
        // is Raw in THIS round's model (era-5c report 045).
        let round_facts =
            super::field_moves::mut_model().then(|| round_mutability_facts(program, slots, &model));
        let round_mutable = super::mutability_facts::RoundMut {
            base: is_mutable,
            round: round_facts.as_ref(),
        };
        // L01⁹ wall 4 (`CRAT_ERA5C_MOVE_STORE`): this round's qualifying stores issue
        // no loan on a local that is not `Raw` during the replay (era-5c 060a).
        let _move_store = super::field_moves::move_store().then(|| {
            super::move_store::enter_round(
                program,
                slots,
                solver.ownership_facts(),
                solver.original_cell_selection(),
                &model,
            )
        });
        let is_ref = |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref);
        // §8 BB3-b — complete-by-construction: EVERY non-`Ref` slot is a replay candidate
        // (`is_raw`), so no `Owning` slot is ever EXCLUDED from the replay. A flow-insensitive
        // depth-0 slot can be `Owning` (ownership ORs over versions) yet carry a *reference*
        // role in another version (`p = &mut a; …; p = malloc()`; or via reborrow/`offset`);
        // excluding such a slot as a non-candidate would HIDE its aliasing conflict — the
        // BB3-b under-report. Including every non-`Ref` slot makes "no hidden `Ref`-vs-`Ref`
        // aliasing" hold by construction, with no need to DETECT mixed-role locals (a tar pit:
        // any syntactic/conflict predicate must re-derive the borrow analysis's full
        // provenance flow — Ref/RawPtr, cast/copy, offset/library methods, … — and kept
        // missing paths over four adversarial rounds). Treating an `Owning` slot as a raw
        // candidate is strictly MORE conservative (its loans are included, never fewer), so it
        // cannot under-report. RESIDUAL (deferred to flow-sensitivity): a mixed-role local is
        // output `Owning` — an ownership-layer imprecision, NOT a borrow-verifier under-report
        // (the borrow contract = the surviving `Ref` slots do not alias; that holds for the
        // raw-role completeness THIS argument is about — but NOT under the NB2 mutability
        // skip, which drops immutable *interprocedural* loans from invalidation: two surviving
        // `Ref`s CAN then alias a written cell via a call-return/param/cast/offset/field alias
        // the coherence equate-closure does not unify. That is the S2-6 acceptance-level gap,
        // real today (call-return witness `nb2_cross_alias_write_uncaught_witness`;
        // production-parity), guarded ONLY by §8 and fixed by write-aware invalidation in
        // NB3-3b). The §8 guardrail (BO unconsumed) makes both the imprecision above and the
        // S2-6 gap harmless until codegen.
        //
        // §NB5-F2 (Codex HIGH fix): this predicate is used TWO ways in `revalidate_replaying` and
        // the two owner classes need OPPOSITE semantics. LOCAL replay candidacy stays the
        // conservative non-`Ref` above (an `Owning` local's loans must be INCLUDED — BB3-b). But
        // the field DISABLE list REMOVES loans, so it must be EXACT `Raw`: disabling an `Owning`
        // field's loan would delete a conflict that should decline/demote (an owning + borrow-
        // aliased field → unsound accept). So branch on the owner: fields → exactly `Raw`, locals
        // → non-`Ref`. (`Raw` fields are the only ones F2 dischargeds; `Owning` fields fall through
        // to the `residual_nonref_field` decline backstop.)
        let is_raw = |s: SlotRef| match s {
            SlotRef::Field(_) => model.get(&s) == Some(&SlotKind::Raw),
            SlotRef::Local(..) => model.get(&s) != Some(&SlotKind::Ref),
        };
        // R617-1: the guarded arm reads the witnessed replay -- the same replay with its loans and
        // invalidators, in the same A5 context and round facts -- and every step before its commit
        // point reads that replay's plain conflicts. Mode-A and Lemmas keep the reviewed replay.
        let (reviewed, witnessed) = if repair == RepairMode::Guarded {
            let Revalidated {
                conflicts,
                retirement,
                reader_failures,
                ..
            } = revalidate_replaying_witnessed(
                program,
                slots,
                origin_flows,
                is_ref,
                is_raw,
                round_mutable,
                selected_copy_lends.as_ref(),
                active_escaped_copy_lends.as_ref(),
                parameter_overlaps.filter(|_| !w69_fault(repair, "no-a5-context")),
            );
            let plain = conflicts
                .iter()
                .map(|(did, witnessed)| {
                    (
                        *did,
                        witnessed
                            .iter()
                            .map(|w| w.conflict.clone())
                            .collect::<Vec<_>>(),
                    )
                })
                .collect();
            (
                Revalidated {
                    conflicts: plain,
                    retirement,
                    reader_failures,
                    edge_invalidators: FxHashMap::default(),
                },
                Some(conflicts),
            )
        } else {
            (
                revalidate_replaying_reviewed(
                    program,
                    slots,
                    origin_flows,
                    is_ref,
                    is_raw,
                    round_mutable,
                    selected_copy_lends.as_ref(),
                    active_escaped_copy_lends.as_ref(),
                    parameter_overlaps,
                ),
                None,
            )
        };
        if !reviewed.retirement.unresolved.is_empty() {
            stats.source_retirement_decline = reviewed.retirement.unresolved;
            return (None, stats);
        }
        let raw_targets = reviewed.retirement.raw_targets();
        if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
            eprintln!(
                "E5C retirement raw_targets={raw_targets:?} demotions={} conflicts={} unresolved={}",
                reviewed.retirement.demotions.len(),
                reviewed.retirement.conflicts.len(),
                reviewed.retirement.unresolved.len()
            );
            for row in &reviewed.retirement.demotions {
                eprintln!("E5C retirement-demotion {row:?}");
            }
            for row in &reviewed.retirement.conflicts {
                eprintln!("E5C retirement-conflict {row:?}");
            }
        }
        if !raw_targets.is_empty() {
            if !planner_empty_round(planner.as_mut(), &mut stats, &model, diagnostics_enabled) {
                return (None, stats);
            }
            for target in &raw_targets {
                solver.assume(*target, SlotKind::Raw);
                if ledger && let Some(track) = solver.last_track() {
                    ledger_commits.push(super::raw_cause::Commit {
                        track,
                        slot: *target,
                        round: stats.rounds,
                        kind: super::raw_cause::CommitKind::RetirementRaw,
                        issuer: None,
                        clause: None,
                    });
                }
            }
            #[cfg(test)]
            raw_commit_trace::record(stats.rounds, false, &raw_targets);
            stats.commits_conflict += raw_targets.len();
            stats.commits_per_round.push(raw_targets.len());
            let Some((next, dropped)) = solve_round(
                solver,
                selectors,
                backend,
                hard.as_ref(),
                planner.as_ref(),
                &mut stats,
                diagnostics_enabled,
            ) else {
                return (None, stats);
            };
            model = next;
            record_dropped(&mut stats, selectors, &dropped);
            last_dropped = dropped;
            continue;
        }
        let mut conflicts = reviewed.conflicts;
        let retirement_targets: FxHashSet<SlotRef> = if ledger {
            reviewed.retirement.targets().into_iter().collect()
        } else {
            FxHashSet::default()
        };
        let reader_targets: FxHashSet<SlotRef> = reviewed
            .reader_failures
            .iter()
            .filter_map(|failure| failure.target)
            .collect();
        for failure in &reviewed.reader_failures {
            let Some(target @ SlotRef::Local(function, _)) = failure.target else {
                return (None, stats);
            };
            // A missing required proof is an obligation failure, with no
            // invented legacy Loan ID. The existing monotone Ref exclusion
            // keeps the Mode-A bound and all solver caps unchanged.
            conflicts.entry(function).or_default().push(SlotConflict {
                issuer: Some(target),
                requirers: Vec::new(),
                esc_issuer_first: false,
            });
        }
        append_retirement_targets(&mut conflicts, &reviewed.retirement);
        // §NB5-F — partition the residual-conflict guard by owner class. A non-`Ref` FIELD in a
        // residual is the A′ principle extended to field requirers: the field is a live requirer the
        // Local-only replay candidacy cannot soundly demote (committing it just regenerates the
        // conflict), so DECLINE (Option A) is the sound outcome — tagged for the sweep's attribution.
        // A non-`Ref` LOCAL residual stays a fail-closed invariant violation: the inert-ness invariant
        // (see `representative`) keeps non-witness `Raw` locals out of residual edges, so a residual
        // local is always `Ref`; a violation is a real under-report, asserted even in release (BB3-c).
        // (No Local fixture forces this arm — its coverage rests on that invariant, not a synthesized
        // case.) The field early-return runs first, so the assert now effectively guards Locals only.
        if let Some(field) = residual_nonref_field(&conflicts, &model) {
            // L01⁹ (`CRAT_ERA5C_FIELD_OWN_REPAIR`): an OWNING field in a residual
            // is demoted (`¬own`, monotone) instead of declining the program.
            if super::field_moves::field_own_repair()
                && !w69_fault(repair, "no-field-own")
                && model.get(&field) == Some(&SlotKind::Owning)
            {
                if !planner_empty_round(planner.as_mut(), &mut stats, &model, diagnostics_enabled) {
                    return (None, stats);
                }
                let owning: rustc_hash::FxHashSet<SlotRef> = conflicts
                    .values()
                    .flatten()
                    .flat_map(|c| c.issuer.into_iter().chain(c.requirers.iter().copied()))
                    .filter(|s| {
                        matches!(s, SlotRef::Field(_)) && model.get(s) == Some(&SlotKind::Owning)
                    })
                    .collect();
                for field in &owning {
                    solver.forbid_field_own(*field);
                }
                stats.commits_conflict += owning.len();
                stats.commits_per_round.push(owning.len());
                let Some((next, dropped)) = solve_round(
                    solver,
                    selectors,
                    backend,
                    hard.as_ref(),
                    planner.as_ref(),
                    &mut stats,
                    diagnostics_enabled,
                ) else {
                    return (None, stats);
                };
                model = next;
                record_dropped(&mut stats, selectors, &dropped);
                last_dropped = dropped;
                continue;
            }
            stats.field_conflict_decline = Some(field);
            stats.field_conflict_kind = model.get(&field).copied();
            return (None, stats);
        }
        assert!(
            guard_slots_are_ref(&conflicts, &model),
            "every residual conflict LOCAL slot must be Ref in the current model (fields decline above)"
        );
        let mut committed = 0;
        match repair {
            // §NB5-L Mode A (shipped through NB5-F2): one monotone `¬ref(representative)` per residual
            // edge.
            //
            // RETRACTED (§3.3, 2026-07-28): this used to read "Iteration order left on FxHash —
            // Mode-A's z3 assertion order (hence its corpus numbers) stays byte-comparable to every
            // prior row (the S5 asymmetry: sort Lemmas ONLY)". The premise was FALSE. `FxHashMap`
            // iteration is deterministic, but the inner `Vec<ConflictEdge>` follows loan-index order,
            // and loan numbering is not stable (D19). Mode-A is now sorted for the same reason the
            // Lemmas arm always was; the asymmetry is gone.
            RepairMode::ModeA => {
                // §3/R4 (D19): the inner `Vec<ConflictEdge>` follows loan-INDEX
                // order, and loan numbering permutes between runs and between
                // CEGAR rounds (`utils/dsa/union_find.rs` hashes with
                // `RandomState`; `borrow/mod.rs` pushes siblings in `group()`
                // order). So the emitted z3 assertion sequence was not stable.
                //
                // Sorted by `conflict_sort_key` — the SAME key the Lemmas arm
                // already uses — which is built from slot keys and is therefore
                // numbering-independent. Ties need no further tiebreak: two
                // conflicts with equal keys have equal issuer and requirers, so
                // `representative` returns the same slot for both and they emit
                // IDENTICAL assertions. Tie order cannot change the sequence.
                // Each conflict keeps its index in its function's list, where the
                // ledger finds its invalidators; the (stable) sort is unchanged.
                let mut ordered: Vec<(LocalDefId, usize, &SlotConflict)> = conflicts
                    .iter()
                    .flat_map(|(did, cs)| cs.iter().enumerate().map(move |(i, c)| (*did, i, c)))
                    .collect();
                ordered.sort_by(|(da, _, ca), (db, _, cb)| {
                    conflict_sort_key(*da, ca).cmp(&conflict_sort_key(*db, cb))
                });
                for (did, index, conflict) in ordered {
                    if let Some(slot) = representative(conflict, &model) {
                        // era-5c: name the conflict a Mode-A commit came from.
                        if std::env::var_os("CRAT_ERA5C_DEBUG").is_some() {
                            eprintln!(
                                "E5C mode-a-commit slot={slot:?} issuer={:?} requirers={:?} esc_issuer_first={}",
                                conflict.issuer, conflict.requirers, conflict.esc_issuer_first
                            );
                        }
                        // Single-literal exclusion = a monotone `¬ref(slot)` commitment.
                        solver.add_borrow_exclusion(Some(slot), &[]);
                        if ledger && let Some(track) = solver.last_track() {
                            use super::raw_cause::CommitKind;
                            let bare = conflict.requirers.is_empty();
                            let kind = match conflict.issuer {
                                Some(issuer) if bare && retirement_targets.contains(&issuer) => {
                                    CommitKind::RetirementConflict
                                }
                                Some(issuer) if bare && reader_targets.contains(&issuer) => {
                                    CommitKind::ReaderObligation
                                }
                                _ => CommitKind::BorrowExclusion,
                            };
                            // R668-4: the clause the guarded planner would assert here.
                            let invalidators = reviewed
                                .edge_invalidators
                                .get(&did)
                                .and_then(|per_edge| per_edge.get(index))
                                .map_or(&[][..], Vec::as_slice);
                            ledger_commits.push(super::raw_cause::Commit {
                                track,
                                slot,
                                round: stats.rounds,
                                kind,
                                issuer: conflict.issuer,
                                clause: Some(super::raw_cause::Clause::witnessed(
                                    slot,
                                    conflict.issuer,
                                    invalidators,
                                    &model,
                                )),
                            });
                        }
                        committed += 1;
                        stats.commits_conflict += 1;
                        // §NB5-L2 audit capture (gated; `None` = off, zero cost). Record `(slot, round)`
                        // — `stats.rounds` is this round (incremented at the loop top). Rider 2: the round
                        // is retained for the audit's stratification + over-pin-by-round diagnostic.
                        AUDIT_CAPTURE.with(|c| {
                            if let Some(buf) = c.borrow_mut().as_mut() {
                                buf.push((slot, stats.rounds));
                            }
                        });
                        SELECTOR_CORE_COMMIT_CAPTURE.with(|capture| {
                            if let Some(events) = capture.borrow_mut().as_mut() {
                                events.push(ModeACommitTrace {
                                    target: slot,
                                    round: stats.rounds,
                                    conflict: conflict.clone(),
                                });
                            }
                        });
                    }
                }
            }
            // §NB5-L Lemmas (MVP): one empty-context, A′-restricted disjunctive lemma `⋁¬ref(A′-menu)`
            // per residual edge. The objective can satisfy it by demoting ANY menu member, which does
            // NOT beat Mode-A — A′ excludes the only slot whose demotion would help (the issuer), and
            // the freedom to pick a non-minimal member instead LOSES Ref vs Mode-A's minimal commit on
            // high-arity edges (≤ / incomparable, not ≥; see the `RepairMode` doc). Rider 3: STABLE-SORT
            // the edges HERE ONLY (`SlotRef` is not `Ord`, so key explicitly) so the emitted lemma SET
            // is deterministic BY CONSTRUCTION (Mode-A's assertion order is left untouched).
            RepairMode::Lemmas => {
                let mut ordered: Vec<(LocalDefId, &SlotConflict)> = conflicts
                    .iter()
                    .flat_map(|(did, cs)| cs.iter().map(move |c| (*did, c)))
                    .collect();
                ordered.sort_by(|(da, ca), (db, cb)| {
                    conflict_sort_key(*da, ca).cmp(&conflict_sort_key(*db, cb))
                });
                for (_did, conflict) in ordered {
                    let menu = a_prime_menu(conflict, &model);
                    if !menu.is_empty() {
                        // `add_borrow_exclusion(None, &menu)` emits the disjunction `⋁¬ref(menu)` with
                        // NO antecedent (empty context — the context-conditioned form is NB5-L2).
                        solver.add_borrow_exclusion(None, &menu);
                        committed += 1;
                        stats.commits_conflict += 1;
                    }
                }
            }
            // R617-1: the guarded planner's clauses at Mode-A's commit point. Reader failures and
            // retirement targets are observations with an empty guard (unconditional `¬ref`,
            // Mode-A's commits); a witnessed conflict's observation carries its loan and its
            // invalidators, those met through an A5 overlap partner marked. Everything before
            // this point -- the pins, the field-own branch, the declines -- and the accept after
            // it are the loop's own.
            RepairMode::Guarded => {
                let planner = planner.as_mut().expect("the guarded arm has its planner");
                let witnessed = witnessed
                    .as_ref()
                    .expect("the guarded arm reads the witnessed replay");
                let observations = guarded_observations(
                    &reviewed.reader_failures,
                    &reviewed.retirement,
                    witnessed,
                    &model,
                    &stats,
                    diagnostics_enabled,
                );
                match planner.plan_round(L2SolverOutcome::Sat, &observations, &model) {
                    L2RoundPlan::Accept { validation_round } => {
                        assert_eq!(
                            stats.rounds, validation_round,
                            "guarded planner/fixpoint validation-round counters diverged"
                        );
                    }
                    L2RoundPlan::Continue {
                        validation_round,
                        actions,
                    } => {
                        assert_eq!(
                            stats.rounds, validation_round,
                            "guarded planner/fixpoint validation-round counters diverged"
                        );
                        for action in &actions {
                            solver.add_l2_commit(action);
                            emit_l2_action_diagnostic(action, diagnostics_enabled);
                            if ledger && let Some(track) = solver.last_track() {
                                use super::raw_cause::CommitKind;
                                let kind = match action.kind {
                                    l2::CommitActionKind::GuardedCommit => {
                                        CommitKind::GuardedCommit
                                    }
                                    l2::CommitActionKind::RecurrenceEscalation => {
                                        CommitKind::RecurrenceEscalation
                                    }
                                    l2::CommitActionKind::UnconditionalCommit
                                        if retirement_targets.contains(&action.target) =>
                                    {
                                        CommitKind::RetirementConflict
                                    }
                                    l2::CommitActionKind::UnconditionalCommit
                                        if reader_targets.contains(&action.target) =>
                                    {
                                        CommitKind::ReaderObligation
                                    }
                                    l2::CommitActionKind::UnconditionalCommit => {
                                        CommitKind::BorrowExclusion
                                    }
                                };
                                // R668-4: under the guarded repair the ledger names the clause
                                // the planner asserted (its Ref peers and Raw invalidators).
                                ledger_commits.push(super::raw_cause::Commit {
                                    track,
                                    slot: action.target,
                                    round: stats.rounds,
                                    kind,
                                    issuer: None,
                                    clause: Some(super::raw_cause::Clause {
                                        shape: match action.kind {
                                            l2::CommitActionKind::GuardedCommit => "guarded",
                                            _ => "unconditional",
                                        },
                                        ref_peers: action
                                            .clause
                                            .negative_refs
                                            .iter()
                                            .copied()
                                            .filter(|slot| *slot != action.target)
                                            .collect(),
                                        raw_invalidators: action.clause.positive_refs.clone(),
                                    }),
                                });
                            }
                            committed += 1;
                            stats.commits_conflict += 1;
                        }
                    }
                    L2RoundPlan::Decline {
                        validation_round,
                        reason,
                    } => {
                        assert_eq!(
                            stats.rounds, validation_round,
                            "guarded planner/fixpoint validation-round counters diverged"
                        );
                        record_l2_decline(
                            &mut stats,
                            validation_round,
                            reason,
                            diagnostics_enabled,
                        );
                        return (None, stats);
                    }
                }
            }
        }
        stats.commits_per_round.push(committed);
        if committed == 0 {
            // E-R4 certificate: record the residuals the accepted model
            // TOLERATES. Acceptance is `committed == 0`, not an empty conflict
            // set, so this is non-empty in general. Recording-only.
            if !w69_fault(repair, "no-certificate") {
                super::export::record_residuals(
                    conflicts
                        .iter()
                        .flat_map(|(did, cs)| {
                            cs.iter().map(move |c| super::export::ResidualConflict {
                                fn_did: *did,
                                issuer: c.issuer,
                                requirers: c.requirers.clone(),
                            })
                        })
                        .collect(),
                );
            }
            // No committable residual: a genuine fixpoint. Every non-`Ref` slot was a replay
            // candidate above, so an empty residual means the surviving `Ref` slots genuinely do not
            // alias (no `Owning` slot's reference role is hidden). §NB5-F: a `Ref` field residual is
            // committed like any `Ref` slot and a non-`Ref` field residual already declined above, so
            // this path no longer silently accepts a dropped-`Field` residual (the old Local-only gap).
            super::licensing::stack_export::accept(solver.ownership_facts());
            if ledger {
                super::raw_cause::publish(
                    program.tcx,
                    slots,
                    solver,
                    hard.as_ref(),
                    selectors,
                    &last_dropped,
                    &model,
                    &ledger_commits,
                );
            }
            return (Some(model), stats);
        }
        model = match solve_round(
            solver,
            selectors,
            backend,
            hard.as_ref(),
            planner.as_ref(),
            &mut stats,
            diagnostics_enabled,
        ) {
            Some((m, dropped)) => {
                record_dropped(&mut stats, selectors, &dropped);
                last_dropped = dropped;
                m
            }
            None => return (None, stats),
        };
    }
    // §NB5-L cap exhaustion — behaviour depends on the repair mode's termination guarantee (Codex
    // HIGH, 2026-07-18). Mode-A has a PROVEN linear bound (each round commits ≥1 fresh slot to a
    // PERMANENT `¬ref`, so ≤ |slots| rounds); reaching the cap there is a real bug → panic. Lemmas
    // has NO such bound: its disjunctions are non-monotone, so the Max-Ref optimizer could in
    // principle walk subsets of a k-requirer edge for up to ~2^k rounds (subset oscillation). That
    // worst case does NOT manifest under the pinned z3 seed — empirically a 33-requirer edge still
    // converges in 3 rounds (`nb5l_high_arity_no_panic`) — but it is not PROVEN impossible, so the
    // cap must be a CONTROLLED backstop, not a crash: return a sound decline (invariant 6 — decline
    // is always legal; the §8 guardrail keeps it harmless). This is exactly rider-1's "real
    // backstop": a rounds explosion becomes a decline the sweep surfaces, never a panic.
    match repair {
        RepairMode::ModeA => panic!(
            "Mode-A CEGAR did not converge within {cap} rounds — this violates the proven linear \
             bound (each round commits ≥1 fresh permanent ¬ref), so it is a genuine analysis bug."
        ),
        RepairMode::Lemmas => {
            // Non-monotone lemma loop hit the cap (subset oscillation): controlled decline, not panic.
            // Tag the decline KIND so `bo_c1` reports it as cap-exhaustion, not a mislabeled
            // `sat-in-replay` (Codex MEDIUM).
            stats.cap_exhausted = true;
            (None, stats)
        }
        // R617-1: the planner declines at its own cap (10S + 1) one round before this bound, so
        // reaching it is a planner defect; decline, which falls back to Mode-A.
        RepairMode::Guarded => {
            stats.cap_exhausted = true;
            (None, stats)
        }
    }
}

/// W69 faults (test builds only; era-5c 082 §3): each removes one piece of the guarded arm, and
/// only in a guarded run, so the Mode-A fallback is untouched. `no-a5-context`: the witnessed
/// replay without A5's overlap pairs. `no-field-own`: the field-own branch skipped. `no-certificate`:
/// the residual certificate not recorded at a guarded accept.
fn w69_fault(repair: RepairMode, name: &str) -> bool {
    #[cfg(test)]
    {
        repair == RepairMode::Guarded && std::env::var("CRAT_E5C_W69_FAULT").as_deref() == Ok(name)
    }
    #[cfg(not(test))]
    {
        let _ = (repair, name);
        false
    }
}

/// R617-1: tell the guarded planner of a round whose commits are not its own (the retirement
/// pins, the field-own repair), so its validation counter stays equal to `stats.rounds`. `false`
/// when the planner declines (its cap). A no-op outside the guarded mode.
fn planner_empty_round(
    planner: Option<&mut Planner>,
    stats: &mut RoundStats,
    model: &FxHashMap<SlotRef, SlotKind>,
    diagnostics_enabled: bool,
) -> bool {
    let Some(planner) = planner else {
        return true;
    };
    match planner.plan_round(L2SolverOutcome::Sat, &[], model) {
        L2RoundPlan::Accept { validation_round } => {
            assert_eq!(
                stats.rounds, validation_round,
                "guarded planner/fixpoint validation-round counters diverged"
            );
            true
        }
        L2RoundPlan::Decline {
            validation_round,
            reason,
        } => {
            record_l2_decline(stats, validation_round, reason, diagnostics_enabled);
            false
        }
        L2RoundPlan::Continue { .. } => panic!("empty L2 observations produced commit actions"),
    }
}

/// R617-1: one guarded round's observations, as the separate L2 loop built them: reader failures
/// and retirement targets with an empty guard, then every witnessed conflict with a committable
/// representative. The planner orders them canonically.
fn guarded_observations(
    reader_failures: &[super::licensing::reader_replay::Failure],
    retirement: &super::retirement::RetirementReview,
    witnessed: &FxHashMap<LocalDefId, Vec<WitnessedSlotConflict>>,
    model: &FxHashMap<SlotRef, SlotKind>,
    stats: &RoundStats,
    diagnostics_enabled: bool,
) -> Vec<ConflictObservation> {
    let mut observations = Vec::new();
    for failure in reader_failures {
        let Some(target @ SlotRef::Local(function, _)) = failure.target else {
            unreachable!("a reader failure without a local target declined before the arm");
        };
        observations.push(ConflictObservation::new(
            function.local_def_index.as_u32(),
            target,
            Some(target),
            Vec::new(),
        ));
    }
    for target in retirement.targets() {
        let row = retirement
            .conflicts
            .iter()
            .find(|row| row.target == target)
            .expect("retirement target");
        observations.push(ConflictObservation::new(
            row.function.local_def_index.as_u32(),
            target,
            Some(target),
            Vec::new(),
        ));
    }
    for (did, conflicts) in witnessed {
        for witnessed in conflicts {
            let Some(target) = representative(&witnessed.conflict, model) else {
                continue;
            };
            let mut observation = ConflictObservation::new(
                did.local_def_index.as_u32(),
                target,
                witnessed.conflict.issuer,
                witnessed.conflict.requirers.clone(),
            )
            .with_invalidators(witnessed.invalidators.clone())
            .with_overlap_invalidators(witnessed.overlap_invalidators.clone());
            if let Some(stable_loan_key) = witnessed.stable_loan_key {
                let loan = witnessed.loan.expect("a stable loan key has its loan");
                observation = observation.with_loan_identity(loan, stable_loan_key);
            }
            if diagnostics_enabled {
                eprintln!(
                    "[bo-l2] {}",
                    l2::conflict_witness_diagnostic(
                        stats.rounds,
                        did.local_def_index.as_u32(),
                        // An A5 parameter edge has no loan behind it.
                        witnessed.loan.unwrap_or(usize::MAX),
                        target,
                        witnessed.conflict.issuer,
                        &witnessed.conflict.requirers,
                        &witnessed.invalidators,
                    )
                );
                // W69c: the hazard key, with the invalidators met through an A5 partner.
                if witnessed.stable_loan_key.is_some() {
                    eprintln!(
                        "[bo-l2] event=guarded_hazard|round={}|hazard={}",
                        stats.rounds,
                        observation.hazard_key_diagnostic()
                    );
                }
            }
            observations.push(observation);
        }
    }
    observations
}

/// L2 feature-on validate/re-solve loop. This is deliberately separate from
/// the feature-off branch above: disabled Mode-A retains its original conflict
/// iteration, assertion order, cap, and `add_borrow_exclusion` calls.
#[derive(Clone)]
struct L2ActiveDiagnosticClause {
    sequence: usize,
    committed_round: usize,
    action: CommitAction,
}

#[derive(Default)]
struct L2TransitionDiagnostics {
    active: Vec<L2ActiveDiagnosticClause>,
    previous_model: Option<FxHashMap<SlotRef, SlotKind>>,
}

impl L2TransitionDiagnostics {
    fn emit_round(
        &self,
        validation_round: usize,
        planner: &Planner,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) {
        eprintln!(
            "[bo-l2] event=l2_round_state|round={validation_round}|active_clauses={}",
            self.active.len()
        );
        let previous_model = self.previous_model.as_ref().unwrap_or(model);
        for clause in &self.active {
            eprintln!(
                "[bo-l2] {}",
                l2::clause_state_diagnostic(
                    &clause.action,
                    clause.sequence,
                    clause.committed_round,
                    validation_round,
                    previous_model,
                    model,
                    |slot| planner.lifecycle(slot),
                )
            );
        }
    }

    fn record_actions(
        &mut self,
        committed_round: usize,
        actions: &[CommitAction],
        model: &FxHashMap<SlotRef, SlotKind>,
    ) {
        self.previous_model = Some(model.clone());
        for action in actions {
            self.active.push(L2ActiveDiagnosticClause {
                sequence: self.active.len() + 1,
                committed_round,
                action: action.clone(),
            });
        }
    }
}

/// R617-1: no production route reaches this loop any more. `CRAT_BO_L2_GUARDED_COMMITS=1` is the
/// alias of `RepairMode::Guarded`, the guarded arm of the one loop above; this separate loop is kept
/// as the door the existing L2 tests call directly. The rest of this note is its history.
///
/// D10: `pub(crate)` so a test can route through the L2 loop **directly**
/// instead of mutating `CRAT_BO_L2_GUARDED_COMMITS` inside a parallel test
/// binary. The env switch remains the production entry — resolved once in
/// `verify_to_fixpoint_counting_with_flows` — and this changes nothing about
/// it; it only removes the need to perturb process-wide state to reach the same
/// loop.
///
/// # Preconditions this door must carry (D17)
///
/// The env entry asserts **two** things before delegating here, and neither is
/// what an earlier version of this doc claimed:
///
/// - **`solver.tracker().is_none()`.** A tracked solver's hard constraints are
///   track-gated, so every solve here would be vacuously SAT and the accepted
///   model meaningless. Opening this door does **not** leave that unguarded:
///   `KindSolver::check`, `model_kinds`, and `model_kinds_relaxing` each carry
///   their own release-active guard, and the loop cannot extract a model
///   without passing one. The `debug_assert!` below is a *fail-earlier*
///   tripwire — it names the door in the message instead of the accessor — not
///   the only thing standing between a tracked solver and a meaningless model.
///   (The review finding that prompted this called the guard bypassed; that was
///   checked and is wrong.)
/// - **`RepairMode::current() == ModeA` — INERT here.** This loop stamps
///   `repair: RepairMode::ModeA` into its own stats and never reads
///   `RepairMode::current()`, so violating it changes nothing about what runs.
///   Documented for callers, not enforced.
///
/// An earlier version of this doc named only the inert one, and called the
/// other load-bearing.
pub(crate) fn verify_l2_to_fixpoint_counting(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
    copy_lends: Option<&FxHashSet<CopyLendPair>>,
    escaped_copy_lends: Option<&SelectedCopyLendLoans>,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    verify_l2_to_fixpoint_counting_impl(
        program,
        slots,
        origin_flows,
        solver,
        selectors,
        is_mutable,
        copy_lends,
        escaped_copy_lends,
        LoopBackend::HardCheckRoundOptimize,
    )
}

pub(super) fn verify_l2_to_fixpoint_counting_impl(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
    copy_lends: Option<&FxHashSet<CopyLendPair>>,
    escaped_copy_lends: Option<&SelectedCopyLendLoans>,
    backend: LoopBackend,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    let _reader_facts = super::licensing::reader_replay::enter_facts(solver.ownership_facts());
    let source_inventory = super::source_events::for_construction(program);
    let _source_scope = super::source_events::enter_inventory(&source_inventory);
    super::source_events::record_replay();
    // D17: re-assert the load-bearing precondition at the door, not only at the
    // env entry. `debug_assert!` rather than `assert!` so the release-path cost
    // and behaviour of the existing single choke point are unchanged.
    debug_assert!(
        !solver.is_diagnostic_tracked(),
        "diagnostic-tracked KindSolver must not enter the l2 door"
    );
    let diagnostics_enabled = l2::diagnostics_enabled_from_env();
    let mut transition_diagnostics =
        l2::transition_diagnostics_enabled_from_env().then(L2TransitionDiagnostics::default);
    let slot_count = slots
        .fn_local_slots
        .values()
        .try_fold(slots.field_slots.len(), |count, universe| {
            count.checked_add(universe.len())
        })
        .expect("L2 registered-slot count overflow");
    let mut planner = Planner::new(slot_count);

    super::coherence::constrain_field_ownership(solver, slots, program);
    let hard =
        matches!(backend, LoopBackend::HardCheckRoundOptimize).then(|| solver.hard_loop_solver());
    let mut stats = RoundStats {
        repair: RepairMode::ModeA,
        ..RoundStats::default()
    };

    let (mut model, dropped) = match solve_l2_round_model(solver, selectors, backend, hard.as_ref())
    {
        L2SolveResult::Sat { kinds, dropped } => (kinds, dropped),
        L2SolveResult::Unsat => {
            record_l2_decline(
                &mut stats,
                planner.validation_rounds(),
                L2DeclineReason::Solver(L2SolverDecline::Unsat),
                diagnostics_enabled,
            );
            return (None, stats);
        }
        L2SolveResult::Unknown => {
            record_l2_decline(
                &mut stats,
                planner.validation_rounds(),
                L2DeclineReason::Solver(L2SolverDecline::Unknown),
                diagnostics_enabled,
            );
            return (None, stats);
        }
    };
    record_dropped(&mut stats, selectors, &dropped);
    let mut diagnostic_slots = diagnostics_enabled.then(Vec::new);

    loop {
        stats.rounds += 1;
        if let Some(diagnostics) = &transition_diagnostics {
            diagnostics.emit_round(stats.rounds, &planner, &model);
        }
        // D1: same per-round reset on the L2 path.
        super::export::begin_round();
        let _original_cell_model =
            super::licensing::model_selection::enter(solver.original_cell_selection());
        let active_escaped_copy_lends = escaped_copy_lends
            .map(|escaped| super::esc_minimal::active_loans_for_model(escaped, &model));
        let _retirement_model = super::retirement::model_scope(&model);
        let selected_copy_lends = selected_copy_lends_for_round(
            program,
            slots,
            &model,
            copy_lends,
            active_escaped_copy_lends.as_ref(),
        );
        stats.copy_lend_replay_selections = selected_copy_lend_count(&selected_copy_lends);
        let selected_copy_lends =
            (stats.copy_lend_replay_selections != 0).then_some(selected_copy_lends);
        let reviewed = revalidate_replaying_witnessed(
            program,
            slots,
            origin_flows,
            |slot| model.get(&slot) == Some(&SlotKind::Ref),
            |slot| match slot {
                SlotRef::Field(_) => model.get(&slot) == Some(&SlotKind::Raw),
                SlotRef::Local(..) => model.get(&slot) != Some(&SlotKind::Ref),
            },
            is_mutable,
            selected_copy_lends.as_ref(),
            active_escaped_copy_lends.as_ref(),
            None,
        );
        if !reviewed.retirement.unresolved.is_empty() {
            stats.source_retirement_decline = reviewed.retirement.unresolved;
            emit_l2_final_diagnostics(diagnostic_slots.as_mut(), &model);
            return (None, stats);
        }
        let raw_targets = reviewed.retirement.raw_targets();
        if !raw_targets.is_empty() {
            // A typed coverage repair is independent of L2's guarded loan clauses.
            // Keep its validation-round accounting honest without inventing a loan.
            #[cfg(test)]
            if coverage_planner_fault::active() {
                planner = Planner::new(usize::MAX);
            }
            match planner.plan_round(L2SolverOutcome::Sat, &[], &model) {
                L2RoundPlan::Accept { validation_round } => {
                    assert_eq!(
                        stats.rounds, validation_round,
                        "L2 coverage/planner validation counters diverged"
                    );
                }
                L2RoundPlan::Decline {
                    validation_round,
                    reason,
                } => {
                    record_l2_decline(&mut stats, validation_round, reason, diagnostics_enabled);
                    emit_l2_final_diagnostics(diagnostic_slots.as_mut(), &model);
                    return (None, stats);
                }
                L2RoundPlan::Continue { .. } => {
                    panic!("empty L2 observations produced commit actions")
                }
            }
            for target in &raw_targets {
                solver.assume(*target, SlotKind::Raw);
            }
            #[cfg(test)]
            raw_commit_trace::record(stats.rounds, true, &raw_targets);
            stats.commits_conflict += raw_targets.len();
            stats.commits_per_round.push(raw_targets.len());
            match solve_l2_round_model(solver, selectors, backend, hard.as_ref()) {
                L2SolveResult::Sat { kinds, dropped } => {
                    model = kinds;
                    record_dropped(&mut stats, selectors, &dropped);
                    continue;
                }
                L2SolveResult::Unsat => {
                    record_l2_decline(
                        &mut stats,
                        planner.validation_rounds(),
                        L2DeclineReason::Solver(L2SolverDecline::Unsat),
                        diagnostics_enabled,
                    );
                    return (None, stats);
                }
                L2SolveResult::Unknown => {
                    record_l2_decline(
                        &mut stats,
                        planner.validation_rounds(),
                        L2DeclineReason::Solver(L2SolverDecline::Unknown),
                        diagnostics_enabled,
                    );
                    return (None, stats);
                }
            }
        }
        let conflicts = reviewed.conflicts;
        let mut observations = Vec::new();
        for failure in &reviewed.reader_failures {
            let Some(target @ SlotRef::Local(function, _)) = failure.target else {
                return (None, stats);
            };
            observations.push(ConflictObservation::new(
                function.local_def_index.as_u32(),
                target,
                Some(target),
                Vec::new(),
            ));
        }
        for target in reviewed.retirement.targets() {
            let row = reviewed
                .retirement
                .conflicts
                .iter()
                .find(|row| row.target == target)
                .expect("retirement target");
            // An obligation-only observation has an empty peer guard, hence
            // an unconditional exclusion. It invents no legacy loan identity.
            observations.push(ConflictObservation::new(
                row.function.local_def_index.as_u32(),
                target,
                Some(target),
                Vec::new(),
            ));
        }
        for (did, conflicts) in &conflicts {
            for witnessed in conflicts {
                let Some(target) = representative(&witnessed.conflict, &model) else {
                    if let Some(field) = witnessed
                        .conflict
                        .issuer
                        .into_iter()
                        .chain(witnessed.conflict.requirers.iter().copied())
                        .find(|slot| {
                            matches!(slot, SlotRef::Field(_))
                                && model.get(slot) != Some(&SlotKind::Ref)
                        })
                    {
                        stats.field_conflict_decline = Some(field);
                        stats.field_conflict_kind = model.get(&field).copied();
                        emit_l2_final_diagnostics(diagnostic_slots.as_mut(), &model);
                        return (None, stats);
                    }
                    continue;
                };
                let mut observation = ConflictObservation::new(
                    did.local_def_index.as_u32(),
                    target,
                    witnessed.conflict.issuer,
                    witnessed.conflict.requirers.clone(),
                )
                .with_invalidators(witnessed.invalidators.clone());
                if let Some(stable_loan_key) = witnessed.stable_loan_key {
                    let loan = witnessed.loan.expect("a stable loan key has its loan");
                    observation = observation.with_loan_identity(loan, stable_loan_key);
                }
                observations.push(observation);
                if diagnostics_enabled {
                    let record = if let Some(stable_loan_key) = witnessed.stable_loan_key {
                        l2::conflict_witness_diagnostic_stable(
                            stats.rounds,
                            did.local_def_index.as_u32(),
                            witnessed.loan.expect("a stable loan key has its loan"),
                            stable_loan_key,
                            target,
                            witnessed.conflict.issuer,
                            &witnessed.conflict.requirers,
                            &witnessed.invalidators,
                        )
                    } else {
                        l2::conflict_witness_diagnostic(
                            stats.rounds,
                            did.local_def_index.as_u32(),
                            // A5 parameter edge (R617-1): no loan behind it.
                            witnessed.loan.unwrap_or(usize::MAX),
                            target,
                            witnessed.conflict.issuer,
                            &witnessed.conflict.requirers,
                            &witnessed.invalidators,
                        )
                    };
                    eprintln!("[bo-l2] {}", record);
                }
            }
        }

        let actions = match planner.plan_round(L2SolverOutcome::Sat, &observations, &model) {
            L2RoundPlan::Accept { validation_round } => {
                assert_eq!(
                    stats.rounds, validation_round,
                    "L2 planner/fixpoint validation-round counters diverged"
                );
                stats.commits_per_round.push(0);
                emit_l2_final_diagnostics(diagnostic_slots.as_mut(), &model);
                super::licensing::stack_export::accept(solver.ownership_facts());
                return (Some(model), stats);
            }
            L2RoundPlan::Continue {
                validation_round,
                actions,
            } => {
                assert_eq!(
                    stats.rounds, validation_round,
                    "L2 planner/fixpoint validation-round counters diverged"
                );
                actions
            }
            L2RoundPlan::Decline {
                validation_round,
                reason,
            } => {
                assert_eq!(
                    stats.rounds, validation_round,
                    "L2 planner/fixpoint validation-round counters diverged"
                );
                record_l2_decline(&mut stats, validation_round, reason, diagnostics_enabled);
                emit_l2_final_diagnostics(diagnostic_slots.as_mut(), &model);
                return (None, stats);
            }
        };

        for action in &actions {
            if let Some(slots) = diagnostic_slots.as_mut() {
                slots.push(action.target);
                slots.extend(action.peers.iter().copied());
            }
            solver.add_l2_commit(action);
            emit_l2_action_diagnostic(action, diagnostics_enabled);
        }
        if let Some(diagnostics) = &mut transition_diagnostics {
            diagnostics.record_actions(stats.rounds, &actions, &model);
        }
        stats.commits_conflict += actions.len();
        stats.commits_per_round.push(actions.len());

        match solve_l2_round_model(solver, selectors, backend, hard.as_ref()) {
            L2SolveResult::Sat { kinds, dropped } => {
                model = kinds;
                record_dropped(&mut stats, selectors, &dropped);
            }
            L2SolveResult::Unsat => {
                record_l2_decline(
                    &mut stats,
                    planner.validation_rounds(),
                    L2DeclineReason::Solver(L2SolverDecline::Unsat),
                    diagnostics_enabled,
                );
                emit_l2_final_diagnostics(diagnostic_slots.as_mut(), &model);
                return (None, stats);
            }
            L2SolveResult::Unknown => {
                record_l2_decline(
                    &mut stats,
                    planner.validation_rounds(),
                    L2DeclineReason::Solver(L2SolverDecline::Unknown),
                    diagnostics_enabled,
                );
                emit_l2_final_diagnostics(diagnostic_slots.as_mut(), &model);
                return (None, stats);
            }
        }
    }
}

fn emit_l2_final_diagnostics(
    slots: Option<&mut Vec<SlotRef>>,
    model: &FxHashMap<SlotRef, SlotKind>,
) {
    let Some(slots) = slots else {
        return;
    };
    slots.sort_by_key(|slot| l2::SlotKey::of(*slot));
    slots.dedup();
    for &slot in slots.iter() {
        let kind = match model
            .get(&slot)
            .copied()
            .expect("every emitted L2 diagnostic slot must exist in the solved model")
        {
            SlotKind::Ref => "ref",
            SlotKind::Raw => "raw",
            SlotKind::Owning => "owning",
        };
        eprintln!(
            "[bo-l2] event=l2_final|slot={}|kind={kind}",
            l2::slotref_diagnostic(slot)
        );
    }
}

fn emit_l2_action_diagnostic(action: &CommitAction, enabled: bool) {
    if enabled {
        eprintln!(
            "[bo-l2] {}|witnessed_peers={}",
            action.diagnostic_label,
            l2::witnessed_peers_diagnostic(action)
        );
    }
}

fn record_l2_decline(
    stats: &mut RoundStats,
    validation_round: usize,
    reason: L2DeclineReason,
    diagnostics_enabled: bool,
) {
    if diagnostics_enabled {
        eprintln!("[bo-l2] {}", reason.diagnostic_label(validation_round));
    }
    stats.l2_decline = Some(reason);
}

/// §NB5-L2 (commit-necessity audit) — does `model` ACCEPT, i.e. is it a Mode-A fixpoint? True iff one
/// more validate round would commit nothing: no residual conflict names a non-`Ref` FIELD
/// (`residual_nonref_field` — the field-decline) AND every residual conflict's A′ `representative` is
/// `None` (no committable `Ref` owner, so `committed` would be 0). This is EXACTLY
/// `verify_to_fixpoint_counting`'s accept condition, factored out so the audit's "one solve + one
/// validate" classification shares the loop's accept semantics rather than a re-derived twin that could
/// drift — the `is_ref`/`is_raw` replay closures are byte-identical to the loop's (BB3-b for locals,
/// exact-`Raw` for fields, §NB5-F2). The anchor asserts `model_accepts(accepted_model)`; the
/// calibration tests (`nb5l2_probe_necessary_and_injected_overpin`,
/// `nb5l2_probe_finds_natural_accumulation_overpin`) pin both classification arms.
pub(crate) fn model_accepts(
    program: &RustProgram,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    is_mutable: impl MutProvider + Copy,
) -> bool {
    let origin_flows = super::origin_flow::analyze_program_origin_flow(program);
    model_accepts_with_flows(program, slots, &origin_flows, model, is_mutable)
}

pub(crate) fn model_accepts_with_flows(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    model: &FxHashMap<SlotRef, SlotKind>,
    is_mutable: impl MutProvider + Copy,
) -> bool {
    model_accepts_with_flows_impl(program, slots, origin_flows, model, is_mutable, None)
}

pub(crate) fn model_accepts_with_flows_and_copy_lends(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    model: &FxHashMap<SlotRef, SlotKind>,
    is_mutable: impl MutProvider + Copy,
    copy_lends: &FxHashSet<CopyLendPair>,
) -> bool {
    let selected = selected_copy_lend_sites(program, slots, copy_lends, model);
    model_accepts_with_flows_impl(
        program,
        slots,
        origin_flows,
        model,
        is_mutable,
        Some(&selected),
    )
}

fn model_accepts_with_flows_impl(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    model: &FxHashMap<SlotRef, SlotKind>,
    is_mutable: impl MutProvider + Copy,
    selected_copy_lends: Option<&SelectedCopyLendLoans>,
) -> bool {
    // ALLOW-LIST TRIPWIRE (ruling on ADV-1). This is a PROBE — an oracle run
    // outside either CEGAR loop, on a model the loop may never have accepted.
    // Under the allow-list it is outside the armed region and records nothing
    // by construction, so the previous `with_capture_suspended` here is
    // redundant.
    //
    // It is replaced by an assertion rather than deleted, and that choice is
    // deliberate: suspension would MASK a violation of the allow-list (a probe
    // that somehow ran inside the armed region would quietly record nothing and
    // look fine), whereas this fails loudly and names the invariant. A backstop
    // that hides the bug it backstops is worse than no backstop.
    debug_assert!(
        !super::export::capturing(),
        "allow-list violation: a probe entry point ran INSIDE the armed capture \
         region. Capture must be armed only around the accepted run; move the \
         arm, do not suspend here."
    );
    let _retirement_model = super::retirement::model_scope(model);
    let reviewed = revalidate_replaying_reviewed(
        program,
        slots,
        origin_flows,
        |s| model.get(&s) == Some(&SlotKind::Ref),
        |s| match s {
            SlotRef::Field(_) => model.get(&s) == Some(&SlotKind::Raw),
            SlotRef::Local(..) => model.get(&s) != Some(&SlotKind::Ref),
        },
        is_mutable,
        selected_copy_lends,
        None,
        None,
    );
    if !reviewed.retirement.unresolved.is_empty()
        || !reviewed.retirement.conflicts.is_empty()
        || !reviewed.reader_failures.is_empty()
        || !reviewed.retirement.demotions.is_empty()
    {
        return false;
    }
    let conflicts = reviewed.conflicts;
    // The loop's accept is `committed == 0` reached WITHOUT tripping either of its two guards: the
    // `residual_nonref_field` decline (non-`Ref` FIELD residual) and the `guard_slots_are_ref`
    // invariant (a residual whose owners are not all `Ref`, which the release-active loop treats as a
    // fail-closed STOP — §NB5-L2 Codex F2). A probe model CAN reach a non-`Ref`-local residual (unlike
    // the live loop), where `representative` returns `None` and the naive "no committable owner" check
    // would MIS-accept; including `guard_slots_are_ref` rejects it, matching the loop exactly.
    residual_nonref_field(&conflicts, model).is_none()
        && guard_slots_are_ref(&conflicts, model)
        && conflicts
            .values()
            .flatten()
            .all(|c| representative(c, model).is_none())
}

/// Pick the slot of a residual conflict to commit `¬ref` on (Mode A).
///
/// §NB4-4a **A′ — live-requirer discharge.** Demoting a slot discharges an edge only if it
/// removes the **conflict**, not the **requirement**. Demoting the *issuer* removes its loan
/// from the ANALYSIS (the replay disables that provenance and the loan disappears next round),
/// but a live `Ref` **requirer** of that loan still aliases the written cell — it is not made
/// safe by the issuer going `Raw`. So when a live `Ref` requirer exists **beyond** the issuer,
/// it must carry the discharge; the issuer stays in the menu only when no such requirer exists
/// (self-edges, issuer-only edges).
///
/// This RESTRICTS the commit menu — it introduces no new assertion kind, so §3 invariant 7
/// (lemmas are `¬ref`-only) is untouched. Without it, `x = id(p); …; *b = 2;` (b = p) accepts
/// `p`/`b` = `Raw` while `x` survives `Ref` — a shared reference into a cell written through a
/// raw alias (the S2-6 family, production-parity, §8-guarded). Fixtures:
/// `nb4_returned_borrow_vs_base_mutation`, `nb4_callee_write_invalidates_caller_loan`,
/// `nb4_returned_immutable_borrow_vs_base_write` (A′'s reach is a property of the edge menu, so
/// it closes the IMMUTABLE shape too — orthogonal to the immutable-loan skip).
///
/// Returns `None` only when no owner of the conflict is currently `Ref`. §NB5-F: this cannot
/// arise on the live path — a non-`Ref` field residual is decline-intercepted (`residual_nonref_field`)
/// and a non-`Ref` `Local` residual is assert-intercepted (`guard_slots_are_ref`) before this runs, so
/// every conflict reaching here has a committable `Ref` owner (`Local` OR field). A residual `Local`
/// owner is always `Ref` anyway: `borrow_conflicts_replaying`'s inert-ness invariant keeps non-witness
/// `Raw` locals out of residual edges. The `None` arm is kept defensive (e.g. an empty edge).
fn representative(
    conflict: &SlotConflict,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Option<SlotRef> {
    // §NB5-L: Mode-A's single pick is the FIRST member of the A′ menu (byte-identical refactor —
    // `find` returned the first satisfying element in both A′ branches, and `a_prime_menu`'s
    // order-preserving de-dup never changes the first element).
    a_prime_menu(conflict, model).into_iter().next()
}

/// §NB5-L — the A′-restricted commit menu as a **set** (the `Lemmas` disjunction `⋁¬ref(menu)`
/// ranges over exactly this). Same A′ discipline as `representative` (which is its first element):
/// a live `Ref` requirer BEYOND the issuer must carry the discharge, so if any exist the menu is
/// **exactly those requirers — the issuer is NOT offered** (rider 2: the disjunction's soundness
/// invariant; offering the issuer would let the solver discharge by demoting it while a live `Ref`
/// requirer keeps aliasing the written cell, the S2-6 hole). Otherwise (self-edges, issuer-only
/// edges) the menu is the `Ref` owners, issuer first. Order-preserving de-dup keeps the emitted
/// clause (and the reported lemma set) minimal. Empty iff no owner is currently `Ref` — which the
/// `residual_nonref_field` decline + `guard_slots_are_ref` assert rule out on the live path.
fn a_prime_menu(conflict: &SlotConflict, model: &FxHashMap<SlotRef, SlotKind>) -> Vec<SlotRef> {
    let is_ref = |s: &SlotRef| model.get(s) == Some(&SlotKind::Ref);
    if conflict.esc_issuer_first {
        let issuer = conflict
            .issuer
            .expect("②-selected conflict presentation must carry a resolved-source issuer");
        assert!(
            is_ref(&issuer),
            "②-selected conflict persisted after its resolved source was demoted"
        );
        return vec![issuer];
    }
    let beyond: Vec<SlotRef> = conflict
        .requirers
        .iter()
        .copied()
        .filter(|r| Some(*r) != conflict.issuer && is_ref(r))
        .collect();
    let mut menu = if beyond.is_empty() {
        conflict
            .issuer
            .into_iter()
            .chain(conflict.requirers.iter().copied())
            .filter(is_ref)
            .collect()
    } else {
        beyond
    };
    let mut seen = FxHashSet::default();
    menu.retain(|s| seen.insert(*s));
    menu
}

/// §NB5-L rider 3 — a stable total-order key for a `SlotRef` (`SlotRef: !Ord`, because `LocalDefId`
/// is not; `SlotId` IS orderable). Variant tag orders `Field < Local`; within each, by the
/// underlying id(s). Used ONLY to canonicalize the `Lemmas` emission order (Mode-A stays on FxHash).
pub(crate) fn slotref_key(s: &SlotRef) -> (u8, u32, usize) {
    match s {
        SlotRef::Field(sid) => (0, 0, sid.index()),
        SlotRef::Local(did, sid) => (1, did.local_def_index.as_u32(), sid.index()),
    }
}

/// Stable sort key for a residual conflict edge: (owning fn, issuer, requirers). Deterministic by
/// construction across runs, so the emitted LEMMA SET is comparable row-to-row without resting on
/// the FxHash iteration argument.
fn conflict_sort_key(
    did: LocalDefId,
    c: &SlotConflict,
) -> (u32, (u8, u32, usize), Vec<(u8, u32, usize)>) {
    (
        did.local_def_index.as_u32(),
        c.issuer.as_ref().map_or((2, 0, 0), slotref_key),
        c.requirers.iter().map(slotref_key).collect(),
    )
}

thread_local! {
    /// §NB5-L (Codex MEDIUM) — test-only round-cap override so a test can FORCE cap exhaustion
    /// (the oscillation blowup does not manifest naturally). `None` ⇒ the real `n + 8` bound.
    static CAP_OVERRIDE: Cell<Option<usize>> = const { Cell::new(None) };
}

/// Generous round-cap backstop for `verify_to_fixpoint`. The real bound is ≤ |slots|
/// (each round commits a fresh slot off `Ref`); `n + slack` covers it with margin. Not
/// the termination guarantee — only a panic tripwire (Mode-A) / decline backstop (Lemmas). A
/// test-only `CAP_OVERRIDE` can lower it to exercise the cap branches.
fn round_cap(slots: &CrateSlots) -> usize {
    if let Some(c) = CAP_OVERRIDE.with(|c| c.get()) {
        return c;
    }
    let n: usize = slots.field_slots.len()
        + slots
            .fn_local_slots
            .values()
            .map(|u| u.len())
            .sum::<usize>();
    n + 8
}

/// §NB5-L (Codex MEDIUM) — run `f` with the round cap forced to `cap` on this thread (test-only;
/// panic-safe drop-guard, like `RepairMode::with_override`).
#[cfg(test)]
pub(crate) fn with_cap_override<T>(cap: usize, f: impl FnOnce() -> T) -> T {
    struct Restore(Option<usize>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CAP_OVERRIDE.with(|c| c.set(self.0));
        }
    }
    let _restore = Restore(CAP_OVERRIDE.with(|c| c.replace(Some(cap))));
    f()
}

/// §NB5-F — the first `SlotRef::Field` in a residual conflict the model left non-`Ref` (a field
/// that owns/borrow-aliases a written cell). Option A declines on this: it is not a committable
/// `Ref`, and the Local-only replay candidacy cannot disable its loan, so forcing it would corrupt
/// the ownership fact / loop forever. The paired non-`Ref` `Local` case stays a fail-closed
/// invariant violation (`guard_slots_are_ref`). Returns the offending field for attribution.
fn residual_nonref_field(
    conflicts: &FxHashMap<LocalDefId, Vec<SlotConflict>>,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Option<SlotRef> {
    conflicts
        .values()
        .flatten()
        .flat_map(|c| c.issuer.into_iter().chain(c.requirers.iter().copied()))
        .find(|s| matches!(s, SlotRef::Field(_)) && model.get(s) != Some(&SlotKind::Ref))
}

/// Invariant tripwire for the loop: every slot in a residual conflict edge must be
/// `Ref` in the current model. `Raw` slots are replay-demoted (witnessed) and `Owning`
/// slots are non-candidates, so a residual edge can only name surviving `Ref`
/// candidates; a violation signals the deferred Owning-issuer / under-report cases.
/// §NB5-F: `residual_nonref_field` runs first, so any non-`Ref` slot reaching this guard
/// is a `Local` (a genuine violation).
/// Release-active (BB3-c): a violation = a model with a live residual conflict whose
/// owner slot is not `Ref`, so `representative` cannot commit it and the loop would
/// silently accept an unsound model bound for codegen — it must fail-closed even in
/// release, not compile out.
fn guard_slots_are_ref(
    conflicts: &FxHashMap<LocalDefId, Vec<SlotConflict>>,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> bool {
    conflicts.values().flatten().all(|c| {
        c.issuer
            .iter()
            .chain(c.requirers.iter())
            .all(|s| model.get(s) == Some(&SlotKind::Ref))
    })
}

/// Translate a borrow `ProvenanceOwner` to a BO `SlotRef`. A `Local` owner maps to the
/// local's depth-0 slot; a `Field` owner (§NB5-F) maps to the global struct-field slot's
/// depth-0 slot in `field_slots` (already built + solver-encoded). `SlotRef`'s variant
/// disambiguates the two per-universe `SlotId` spaces, so there is no id collision.
fn owner_to_slot(
    slots: &CrateSlots,
    fn_did: LocalDefId,
    owner: ProvenanceOwner,
) -> Option<SlotRef> {
    match owner {
        ProvenanceOwner::Local(local) => {
            let slot_id = slots
                .fn_local_slots
                .get(&fn_did)?
                .slot_for_local_depth(local, 0)?;
            Some(SlotRef::Local(fn_did, slot_id))
        }
        ProvenanceOwner::Field(field) => {
            // `borrow::StructFieldSlot` and `slots::StructFieldSlot` are structurally
            // identical but nominally distinct types (same `struct_did` / `field_index`);
            // bridge to the slot-universe key.
            let field = super::slots::StructFieldSlot {
                struct_did: field.struct_did,
                field_index: field.field_index,
            };
            let slot_id = slots.field_slots.slot_for_field_depth(field, 0)?;
            Some(SlotRef::Field(slot_id))
        }
    }
}

#[cfg(test)]
mod nb5l_a_prime_menu_tests {
    //! §NB5-L (a′) — the A′-menu-restriction invariant (rider 2), tested directly on the private
    //! `a_prime_menu` with hand-built `SlotConflict`s + models. Owner-agnostic logic, so `Field`
    //! slots (trivially constructible from a `usize`) exercise it without a compiler run.
    use super::*;

    fn field(n: usize) -> SlotRef {
        SlotRef::Field(SlotId::from_usize(n))
    }

    fn model(pairs: &[(SlotRef, SlotKind)]) -> FxHashMap<SlotRef, SlotKind> {
        pairs.iter().copied().collect()
    }

    /// The disjunction's soundness invariant: when a live `Ref` requirer exists BEYOND the issuer,
    /// the A′ menu is EXACTLY those requirers — the issuer is NOT offered, even though it is `Ref`
    /// and in the naive issuer∪requirers menu. (Offering it would let the solver discharge by
    /// demoting the issuer while a live `Ref` requirer keeps aliasing the written cell — the S2-6
    /// hole the lemma must not permit.)
    #[test]
    fn a_prime_menu_excludes_issuer_when_live_requirer() {
        let (i, r1, r2) = (field(0), field(1), field(2));
        let conflict = SlotConflict {
            issuer: Some(i),
            requirers: vec![r1, r2],
            esc_issuer_first: false,
        };
        let m = model(&[(i, SlotKind::Ref), (r1, SlotKind::Ref), (r2, SlotKind::Ref)]);
        let menu = a_prime_menu(&conflict, &m);
        assert!(
            !menu.contains(&i),
            "A′ must NOT offer the issuer when a live Ref requirer exists"
        );
        assert_eq!(
            menu,
            vec![r1, r2],
            "menu = exactly the Ref requirers beyond the issuer"
        );
        // Mode-A's single pick is the menu's first element (the byte-identical refactor).
        assert_eq!(representative(&conflict, &m), Some(r1));
    }

    /// Else-branch: no requirer beyond the issuer ⇒ the issuer IS the menu (self / issuer-only
    /// edges keep the pre-A′ behavior — A′ only RESTRICTS, it never empties a real edge).
    #[test]
    fn a_prime_menu_offers_issuer_when_no_requirer_beyond() {
        let i = field(0);
        let conflict = SlotConflict {
            issuer: Some(i),
            requirers: vec![i],
            esc_issuer_first: false,
        };
        let m = model(&[(i, SlotKind::Ref)]);
        let menu = a_prime_menu(&conflict, &m);
        assert_eq!(
            menu,
            vec![i],
            "issuer offered (order-preserving de-dup) when no requirer beyond"
        );
        assert_eq!(representative(&conflict, &m), Some(i));
    }

    /// A non-`Ref` requirer beyond the issuer is not a LIVE requirer, so it does not trip the A′
    /// "if" branch — the menu falls back to the `Ref` owners (here the issuer).
    #[test]
    fn a_prime_menu_ignores_non_ref_requirer() {
        let (i, r) = (field(0), field(1));
        let conflict = SlotConflict {
            issuer: Some(i),
            requirers: vec![r],
            esc_issuer_first: false,
        };
        let m = model(&[(i, SlotKind::Ref), (r, SlotKind::Raw)]);
        assert_eq!(a_prime_menu(&conflict, &m), vec![i]);
    }

    /// Addenda 61/65: the exact ② class has a different kill switch. Its
    /// presented source issuer is the sole guard and repair party; the escape
    /// destination is receipt-only and may be Ref or Raw.
    #[test]
    fn esc_selected_menu_is_issuer_only() {
        let (source, destination) = (field(0), field(1));
        let conflict = SlotConflict {
            issuer: Some(source),
            requirers: vec![],
            esc_issuer_first: true,
        };
        let m = model(&[(source, SlotKind::Ref), (destination, SlotKind::Raw)]);
        assert_eq!(a_prime_menu(&conflict, &m), vec![source]);
        assert_eq!(representative(&conflict, &m), Some(source));
    }
}

#[cfg(test)]
pub(crate) mod coverage_planner_fault {
    thread_local! { static ACTIVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
    pub(super) fn active() -> bool {
        ACTIVE.with(|active| active.get())
    }
    pub(crate) fn with_overflow<T>(f: impl FnOnce() -> T) -> T {
        struct Reset(bool);
        impl Drop for Reset {
            fn drop(&mut self) {
                ACTIVE.with(|active| active.set(self.0));
            }
        }
        let _reset = Reset(ACTIVE.with(|active| active.replace(true)));
        f()
    }
}

/// R258 test-only observation of the actual retirement Raw-delivery branch.
#[cfg(test)]
pub(crate) mod raw_commit_trace {
    use std::cell::RefCell;

    use super::SlotRef;
    #[derive(Clone, Debug)]
    pub(crate) struct Commit {
        pub(crate) round: usize,
        pub(crate) l2: bool,
        pub(crate) targets: Vec<SlotRef>,
    }
    thread_local! {static CAPTURE:RefCell<Option<Vec<Commit>>>=const{RefCell::new(None)};}
    pub(super) fn record(round: usize, l2: bool, targets: &[SlotRef]) {
        CAPTURE.with(|capture| {
            if let Some(rows) = capture.borrow_mut().as_mut() {
                rows.push(Commit {
                    round,
                    l2,
                    targets: targets.to_vec(),
                });
            }
        });
    }
    pub(crate) fn with_capture<T>(f: impl FnOnce() -> T) -> (T, Vec<Commit>) {
        struct Restore(Option<Vec<Commit>>);
        impl Drop for Restore {
            fn drop(&mut self) {
                CAPTURE.with(|capture| {
                    capture.replace(self.0.take());
                });
            }
        }
        let _restore = Restore(CAPTURE.with(|capture| capture.replace(Some(Vec::new()))));
        let value = f();
        let rows = CAPTURE.with(|capture| capture.borrow_mut().take().unwrap());
        (value, rows)
    }
}
