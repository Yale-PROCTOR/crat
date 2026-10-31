//! The borrow-verifier seam.
//!
//! Runs the production borrow pipeline (`analyses::borrow::borrow_conflicts`) with a
//! ref-candidacy derived from a BO ref-predicate, and translates the resulting
//! conflict edges back into BO `SlotRef`s. This is the read-only adapter the rest of
//! this module builds on: the exclusion encoding turns these conflicts into guarded
//! exclusion clauses, and the CEGAR validate loop wraps it.
//!
//! The adapter's scope: **Local owners only** (`Field` owners are dropped pending the struct
//! field-slot mapping) and **depth-0** correspondence (borrow tracks one provenance
//! per `Local` = the outermost pointer ↔ BO depth-0 slot). The adapter is faithful
//! for a Round-0 (all-Ref) candidacy; partial candidacy that encodes demotions also
//! needs the `tree_borrow_local` union replay the demotion loop performs.

use std::cell::{Cell, RefCell};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::Local;
use rustc_span::def_id::LocalDefId;
use z3::ast::Bool;

use super::{
    SlotKind,
    coherence::{CopyLendPair, SelectedCopyLendLoans, selected_copy_lend_sites},
    crate_slots::CrateSlots,
    guarded_repair::{
        self, ConflictObservation, DeclineReason as GuardedDeclineReason, Planner,
        RoundPlan as GuardedRoundPlan, SolverDecline as GuardedSolverDecline,
        SolverOutcome as GuardedSolverOutcome, StableLoanKey,
    },
    mutability_facts::MutProvider,
    origin_flow::OriginFlowResults,
    slots::{SlotId, SlotOwner},
    solver::{GuardedSolveResult, HardLoopSolver, KindSolver, Selectors, SlotRef},
};
use crate::{
    analyses::borrow::{self, ConflictEdge, ProvenanceOwner},
    utils::rustc::RustProgram,
};

thread_local! {
    /// A scoped `RepairMode` override (see `RepairMode::with_override`), so one process can run
    /// both repairs (the differential harnesses). `None` ⇒ the active repair, `Guarded`.
    static REPAIR_OVERRIDE: Cell<Option<RepairMode>> = const { Cell::new(None) };
}

/// The repair strategy the CEGAR loop uses to discharge a residual borrow conflict.
///
/// - `Plain`: commit one `¬ref(representative)` per residual edge — monotone, permanent.
/// - `Guarded`: the guarded planner's context-conditioned clauses at the same point.
///
/// The active repair is `Guarded`; a thread-local `with_override` selects another for one scope (the
/// differential harnesses). A uniform strategy toggle, constant within an override scope — no
/// path-divergence hazard (unlike threaded origins, which are divergent DATA).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum RepairMode {
    /// Each residual conflict commits `¬ref` on its representative slot.
    Plain,
    /// The guarded planner's clauses in the plain repair's loop, at the point
    /// where the plain repair commits. Everything around the commits is the
    /// plain repair's. A decline falls back to the plain repair for the program
    /// (`RoundStats::guarded_fallback`, receipted).
    Guarded,
}

impl Default for RepairMode {
    fn default() -> Self {
        Self::DEFAULT
    }
}

impl RepairMode {
    /// The default mode. `RoundStats` derives `Default`, so this is also the mode a
    /// default-constructed stats block reports.
    pub(crate) const DEFAULT: Self = RepairMode::Plain;

    /// The active mode: the thread-local override, else `Guarded`.
    pub(crate) fn current() -> Self {
        if let Some(m) = REPAIR_OVERRIDE.with(|c| c.get()) {
            return m;
        }
        RepairMode::Guarded
    }

    #[cfg(test)]
    pub(crate) fn label(self) -> &'static str {
        match self {
            RepairMode::Plain => "mode_a",
            RepairMode::Guarded => "guarded",
        }
    }

    /// Run `f` with `mode` forced on this thread, restoring the prior override on
    /// exit INCLUDING on panic (a drop-guard, not a manual reset: a panicking test must not leak its
    /// mode onto the thread for the next test). Test/sweep-only; production resolves via `current()`.
    #[cfg(test)]
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
    /// Commit-necessity audit — when `Some`, the CEGAR loop's **plain-repair** commit records every
    /// `(committed slot, round)` pair here. `None` (the default) = OFF, zero overhead on the sweep/suite
    /// path. Only the audit driver (`bo_c1::run::run_necessity_audit`) turns it on, via `with_capture`.
    /// Plain repair ONLY: the audit measures the plain repair; the `Lemmas` branch (dead axis) is not
    /// captured. Nesting is unsupported (the audit never nests).
    static AUDIT_CAPTURE: RefCell<Option<Vec<(SlotRef, usize)>>> = const { RefCell::new(None) };
    /// Diagnosis-only detailed origin for each plain-repair commit. Kept separate
    /// from the fixed necessity-audit tuple surface.
    static SELECTOR_CORE_COMMIT_CAPTURE: RefCell<Option<Vec<PlainCommitTrace>>> =
        const { RefCell::new(None) };
}

/// One commit of the plain repair: its target, its round and the conflict behind it.
#[derive(Clone, Debug)]
pub(crate) struct PlainCommitTrace {
    #[cfg(test)]
    pub target: SlotRef,
    #[cfg(test)]
    pub round: usize,
    #[cfg(test)]
    pub conflict: SlotConflict,
}

/// Run `f` while CAPTURING the plain repair's `(slot, round)` commit events, returning
/// `(f's result, the captured events in commit order)`. Panic-safe drop-guard (like
/// `RepairMode::with_override`): the prior capture state is restored on exit including on unwind, so a
/// panicking anchor run never leaks a live buffer onto the thread. The event order is the loop's
/// natural commit order; the audit dedups to the distinct commit SET itself.
#[cfg(test)]
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
#[cfg(test)]
pub(crate) fn with_plain_commit_trace<T>(f: impl FnOnce() -> T) -> (T, Vec<PlainCommitTrace>) {
    struct Restore(Option<Vec<PlainCommitTrace>>);
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

/// A borrow conflict edge with its owners translated to BO `SlotRef`s. `issuer` is
/// `None` for a non-`Assign` borrower.
#[derive(Clone, Debug)]
pub(crate) struct SlotConflict {
    pub issuer: Option<SlotRef>,
    pub requirers: Vec<SlotRef>,
    /// Exact escape-minimal class marker, carried from the selected loan row. False preserves the
    /// ordinary live-requirer repair menu byte-for-byte.
    pub(crate) esc_issuer_first: bool,
}

#[derive(Clone, Debug)]
struct WitnessedSlotConflict {
    conflict: SlotConflict,
    /// `None` for a parameter-overlap edge: no loan behind the conflict.
    loan: Option<usize>,
    stable_loan_key: Option<StableLoanKey>,
    invalidators: Vec<SlotRef>,
    /// The invalidators that met the loan through a parameter-overlap partner.
    overlap_invalidators: Vec<SlotRef>,
}

struct Revalidated<T> {
    conflicts: T,
    retirement: super::retirement::RetirementReview,
    reader_failures: Vec<super::licensing::reader_replay::Failure>,
    /// With the raw-cause ledger on, each conflict's
    /// invalidating slots, in the order of `conflicts`' per-function lists (the
    /// guarded repair's capture's, mapped as the witnessed replay maps them). Empty otherwise.
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
#[cfg(test)]
pub(crate) fn revalidate(
    program: &RustProgram,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
    is_mutable: impl MutProvider + Copy,
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
    let origin_flows = super::origin_flow::analyze_program_origin_flow(program);
    revalidate_with_flows(program, slots, &origin_flows, is_ref, is_mutable)
}

#[cfg(test)]
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
    // Per-local mutability. An immutable provenance's loan is
    // skipped by the invalidation walk, so shared reads of one base stop conflicting.
    let mutab = move |fn_did| move |local: Local| is_mutable.is_mutable(fn_did, local);
    // The forked BO engine.
    let edges =
        super::borrow_engine::borrow_conflicts_with_flows(program, origin_flows, cand, mutab);

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

/// The CEGAR validate seam **with union replay**. Like `revalidate` but
/// takes a *partial* candidacy: a pointer local's depth-0 slot is a `Ref` candidate
/// iff `is_ref`, induces a demotion+union iff `is_raw`, and is an `Owning`
/// non-candidate otherwise. Delegates to `borrow::borrow_conflicts_replaying`, which
/// replays the `tree_borrow_local` union the chosen `Raw` slots induce, so a partial
/// candidacy surfaces the model-dependent conflicts that `revalidate` (round-0) cannot.
/// This is the seam the CEGAR loop drives with the solved model's actual kinds.
#[cfg(test)]
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

#[cfg(test)]
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

#[cfg(test)]
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
    // Per-local mutability. An immutable provenance's loan is
    // skipped by the invalidation walk, so shared reads of one base stop conflicting.
    let mutab = move |fn_did| move |local: Local| is_mutable.is_mutable(fn_did, local);
    // The model's Raw FIELD slots, bridged to `borrow::StructFieldSlot`, so the fork can
    // disable their loans (the field analogue of the Local raw candidacy above). Only the Fork arm
    // consumes them; production keeps its 4-arg signature.
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
    // The forked BO engine.
    let replay = || {
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
    };

    // The ledger records each plain-repair commit's clause, so
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

/// Guarded-repair-only replay adapter carrying the invalidating access roots
/// captured by the BO fork. The ordinary replay adapter above keeps its own
/// shape and performs no guarded-repair collection.
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
    let edges = match (selected_copy_lends, parameter_overlaps) {
        // The parameter-overlap pairs in the witness context, as in the plain repair's replay.
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

/// Encode round-0 borrow conflicts as exclusion guards on the solver. For
/// each conflict edge, assert `¬ref(issuer) ∨ ⋁¬ref(requirers)` via
/// `KindSolver::add_borrow_exclusion`. Hard clauses, applied before the single
/// `model_kinds_relaxing` solve. This is one shot: it encodes the round-0 (all-Ref)
/// conflicts only — the CEGAR validate/re-solve loop (`verify_to_fixpoint`) closes over
/// the solved model's actual candidacy, so this encoding alone is not sound on its own.
///
/// Edges with `Field` owners are partially dropped by the Local-only mapping: an
/// all-`Field` edge becomes a NO-OP (the deferred field-exclusivity gap), and a mixed
/// edge keeps only its surviving `Local` literals — a *stronger* (still sound: forces
/// ≥1 off Ref) but over-constraining guard. Both resolve with a struct field-slot
/// mapping; under the CEGAR loop this is a precision concern only.
#[cfg(test)]
pub(crate) fn materialize_guards(
    solver: &KindSolver,
    conflicts: &FxHashMap<LocalDefId, Vec<SlotConflict>>,
) {
    for edge in conflicts.values().flatten() {
        solver.add_borrow_exclusion(edge.issuer, &edge.requirers);
    }
}

/// Drive the CEGAR validate/re-solve loop to a fixpoint (the plain repair).
///
/// The solver must arrive with ownership constraints + per-fn coherence already
/// emitted (so `selectors` are its retractable owning assumptions:
/// malloc SOURCES and free/realloc SINKS alike; dropping a sink LEAKS THE
/// FREE, an unprovable free staying a raw-pointer free). The malloc-source
/// invariant (`¬ref` on every malloc-source slot — a malloc result owns heap and is
/// not a borrow; see `sources::collect_malloc_source_slots`) is emitted EAGERLY
/// by `emit_crate_ownership_constraints`, so no model this loop ever sees can mark a
/// source `Ref`. Each round: solve →
/// derive the candidacy from the model's *actual* Raw/Ref/Owning kinds → commit `¬ref`
/// on **one representative slot per residual borrow conflict** (live-requirer discharge: a
/// live `Ref` requirer *beyond* the issuer if one exists, else the issuer; see
/// `representative`; conflicts come from `revalidate_replaying`'s `tree_borrow_local`
/// union replay) → re-solve. Accept when no committable (currently-`Ref`) slot remains.
///
/// The plain repair = *monotone single-slot commitment*, deliberately NOT the round-0
/// encoding's disjunctive `materialize_guards`. Committing one currently-`Ref` slot forces exactly that slot off
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
/// validates that model directly — coinciding with the round-0 encoding only in the
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
/// open, sound only because BO output is unconsumed by codegen: (1) a residual conflict all of whose owners are `Field` (dropped by the
/// Local-only mapping) has no committable slot and is accepted (the deferred struct
/// field-slot mapping); (2) an `Owning` slot issues no loan, so a conflict *caused by*
/// an `Owning` pointer is invisible to the replay and an accepted model may hide it.
#[cfg(test)]
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

#[cfg(test)]
pub(crate) fn verify_to_fixpoint_with_flows(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    // Thin wrapper over the single counting loop (model only). KEEP THIN — any logic
    // added here but not in `verify_to_fixpoint_counting` diverges the sweep's counters from what
    // the suite verifies; wrapper-thinness is the guard against that drift.
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

/// CEGAR round/commit counters, native to the fork. `None` (decline) carries the stats of the rounds that
/// ran. `verify_to_fixpoint` is the model-only wrapper over this.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RoundStats {
    /// Validate rounds run, INCLUDING the accepting round (accept-first-model ⇒ `rounds == 1`).
    pub rounds: usize,
    /// Relay main/388 O2: rounds whose model is an optimize incumbent at the budget, and incumbents
    /// refused by the hard evaluation.
    pub incumbent_rounds: usize,
    pub hard_eval_failed: usize,
    /// Every commit is a conflict commit (the `¬ref(source)` invariant is emitted eagerly).
    pub commits_conflict: usize,
    pub commits_per_round: Vec<usize>,
    /// Exact CopyLend loan identities handed to the final replay round. This is a wiring receipt,
    /// not a model-derived recount: suppressing replay registration must drive it to zero.
    pub copy_lend_replay_selections: usize,
    /// Sink selectors the FINAL solve dropped (leaked frees).
    pub dropped_sinks: usize,
    /// Source selectors the FINAL solve dropped (leaked allocs).
    pub dropped_sources: usize,
    /// Set when the loop declined because a residual borrow conflict named a non-`Ref`
    /// FIELD slot (live-requirer discharge extended to field requirers — the field is a live requirer the
    /// Local-only replay candidacy cannot soundly demote, so decline is the sound outcome). Carries
    /// the offending field slot for the sweep's per-program attribution (which field). `None` for an
    /// accept or an UNSAT-family decline (bo_c1 classifies those via its selector-core
    /// `decline_reason`).
    pub field_conflict_decline: Option<SlotRef>,
    /// Diagnostic twin of `field_conflict_decline`: the accepted round model's
    /// exact non-Ref kind for that field.
    pub field_conflict_kind: Option<SlotKind>,
    /// The `RepairMode` that produced these stats (the mode-stamp). Self-describing
    /// results: the sweep row and any `RoundStats` dump say which repair strategy ran, so a
    /// differential is never mode-ambiguous. Defaults to `Plain` (= `RepairMode::DEFAULT`).
    pub repair: RepairMode,
    /// Set when the loop declined because the `Lemmas` round cap was exhausted
    /// (the controlled backstop for a hypothetical subset-oscillation blowup, which does not manifest
    /// empirically). A distinct decline KIND: `bo_c1` must tag it before `decline_reason`, which would
    /// otherwise mislabel this relaxed-SAT decline as `sat-in-replay` and hide the cap exhaustion. Never
    /// set under `Plain` (that path panics — its linear bound is proven).
    pub cap_exhausted: bool,
    /// Guarded-repair controlled decline. The plain-repair and Lemmas paths
    /// leave this unset.
    pub guarded_decline: Option<GuardedDeclineReason>,
    /// Typed source-retirement coverage failure, separate from solver outcome.
    pub source_retirement_decline: Vec<super::retirement::RetirementUnresolved>,
    /// Set when a `Guarded` run declined and the program fell back to the plain
    /// repair. These stats are then the plain repair's run, stamped
    /// `repair = Guarded`; the receipt reads `repair=guarded->mode-a`.
    pub guarded_fallback: Option<GuardedFallback>,
}

/// The declined guarded run behind a plain-repair fallback.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GuardedFallback {
    /// The guarded run's decline, as its receipt names it.
    pub reason: String,
    pub rounds: usize,
    pub commits: usize,
}

impl GuardedFallback {
    fn of(stats: &RoundStats) -> Self {
        let reason = if let Some(reason) = &stats.guarded_decline {
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
    #[cfg(test)]
    LegacyOptimize,
    HardCheckRoundOptimize,
}

/// The mutability facts of one verification round. Foster's load
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
        #[cfg(test)]
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

/// One round's model for the guarded repair, through `backend`.
fn solve_guarded_round_model(
    solver: &KindSolver,
    selectors: &Selectors,
    backend: LoopBackend,
    hard: Option<&HardLoopSolver>,
) -> GuardedSolveResult {
    match backend {
        #[cfg(test)]
        LoopBackend::LegacyOptimize => solver.model_kinds_relaxing_reporting_guarded(selectors),
        LoopBackend::HardCheckRoundOptimize => solver.model_kinds_decomposed_reporting_guarded(
            hard.expect("R1a L2 validation owns a hard checker"),
            selectors,
        ),
    }
}

/// One round's solve. The plain repair and Lemmas solve directly; `Guarded` solves the
/// same system through the typed twin, so a solver decline is recorded in the planner's taxonomy.
fn solve_round(
    solver: &KindSolver,
    selectors: &Selectors,
    backend: LoopBackend,
    hard: Option<&HardLoopSolver>,
    planner: Option<&Planner>,
    stats: &mut RoundStats,
) -> Option<(FxHashMap<SlotRef, SlotKind>, Vec<Bool>)> {
    // Relay main/388 O2: the round's incumbent acceptances / refusals, from the solver's counts.
    let (accepted, refused) = solver.incumbent_counts();
    let solved = solve_round_counted(solver, selectors, backend, hard, planner, stats);
    let (accepted_after, refused_after) = solver.incumbent_counts();
    stats.incumbent_rounds += accepted_after - accepted;
    stats.hard_eval_failed += refused_after - refused;
    solved
}

fn solve_round_counted(
    solver: &KindSolver,
    selectors: &Selectors,
    backend: LoopBackend,
    hard: Option<&HardLoopSolver>,
    planner: Option<&Planner>,
    stats: &mut RoundStats,
) -> Option<(FxHashMap<SlotRef, SlotKind>, Vec<Bool>)> {
    if planner.is_none() {
        return solve_round_model(solver, selectors, backend, hard);
    }
    let decline = match solve_guarded_round_model(solver, selectors, backend, hard) {
        GuardedSolveResult::Sat { kinds, dropped } => return Some((kinds, dropped)),
        GuardedSolveResult::Unsat => GuardedSolverDecline::Unsat,
        GuardedSolveResult::Unknown => GuardedSolverDecline::Unknown,
    };
    record_guarded_decline(stats, GuardedDeclineReason::Solver(decline));
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

/// The CEGAR validate/re-solve loop (the plain repair) with native counters. See
/// `verify_to_fixpoint`'s contract above for scope/soundness. Uses `model_kinds_relaxing_reporting`
/// (identical model to the plain twin the wrapper's callers used, plus the dropped-selector set for
/// the leak counts).
#[cfg(test)]
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

#[cfg(test)]
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
    // Relay main/388 walls 3+4 (R1363-1): `verify:<sub>` marks, inside the baseline verify only.
    let started = std::time::Instant::now();
    let source_inventory = super::source_events::for_construction(program);
    crate::phase_log::sub("verify:inventory", "end", || {
        format!("wall={:.1}s", started.elapsed().as_secs_f64())
    });
    let started = std::time::Instant::now();
    let _source_scope = super::source_events::enter_inventory(&source_inventory);
    super::source_events::record_replay();
    // Relay main/388 verify marks (R1367-2): log only.
    crate::phase_log::sub("verify:record_replay", "end", || {
        format!("wall={:.1}s", started.elapsed().as_secs_f64())
    });
    // Release-active guard: a tracked solver's hard constraints are
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
    // A guarded decline falls back to the plain repair for this program. The guarded run's
    // assertions (its clauses, pins and the field-ownership constraints the loop asserts first)
    // live in a scope that is popped before the plain run, so that run sees the solver exactly as
    // a plain-only run would. An accepting guarded run keeps its scope, as a plain run keeps its
    // commits.
    let started = std::time::Instant::now();
    solver.push_scope();
    crate::phase_log::sub("verify:push_scope", "end", || {
        format!("wall={:.1}s", started.elapsed().as_secs_f64())
    });
    let (model, guarded) = rounds(RepairMode::Guarded);
    if model.is_some() {
        return (model, guarded);
    }
    solver.pop_scope();
    // Relay main/375 §3: a solve the analysis budget ended is not retried in the plain repair.
    if crate::analysis_budget::exceeded().is_some() {
        return (None, guarded);
    }
    let fallback = GuardedFallback::of(&guarded);
    let (model, mut stats) = rounds(RepairMode::Plain);
    stats.repair = RepairMode::Guarded;
    stats.guarded_fallback = Some(fallback);
    (model, stats)
}

/// The validate/re-solve rounds of one repair mode (one loop for every mode). `Guarded` differs
/// from the plain repair only at the commit point, in its witnessed replay, and in its typed solver
/// declines.
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
    // The guarded planner lives across rounds, and is told of every round -- the
    // retirement pins' and the field-own repair's as empty ones -- so its validation counter
    // stays equal to `stats.rounds`. Its own cap (10S + 1) bounds the guarded rounds.
    // Relay main/388 verify marks (R1367-2): the planner's set-up, the cap and the budget check, log only.
    let started = std::time::Instant::now();
    let mut planner = (repair == RepairMode::Guarded).then(|| {
        let slot_count = slots
            .fn_local_slots
            .values()
            .try_fold(slots.field_slots.len(), |count, universe| {
                count.checked_add(universe.len())
            })
            .expect("guarded-repair registered-slot count overflow");
        Planner::new(slot_count)
    });
    let cap = match &planner {
        Some(planner) => planner.validation_cap().saturating_add(1),
        None => round_cap(slots),
    };
    // Relay main/375 §3: the analysis budget, before the first solve.
    if crate::analysis_budget::over("solve:round") {
        return (
            None,
            RoundStats {
                repair,
                ..RoundStats::default()
            },
        );
    }
    crate::phase_log::sub("verify:planner", "end", || {
        format!(
            "repair={repair:?} cap={cap} wall={:.1}s",
            started.elapsed().as_secs_f64()
        )
    });
    // Constrain each struct-field slot's ownership to `field.own <=> AND(stored
    // owns)`, so a field mixing an owned source and a borrowed value settles non-Owning (the
    // flow-insensitive global-field over-claim). Must precede the first solve.
    let started = std::time::Instant::now();
    super::coherence::constrain_field_ownership(solver, slots, program);
    crate::phase_log::sub("verify:field_ownership", "end", || {
        format!("wall={:.1}s", started.elapsed().as_secs_f64())
    });
    let started = std::time::Instant::now();
    let hard =
        matches!(backend, LoopBackend::HardCheckRoundOptimize).then(|| solver.hard_loop_solver());
    crate::phase_log::sub("verify:hard_solver", "end", || {
        format!("wall={:.1}s", started.elapsed().as_secs_f64())
    });
    let mut stats = RoundStats::default();
    // Resolve the repair strategy ONCE per invocation into a local; NO mid-loop re-reads, so the
    // whole fixpoint runs one consistent strategy. It is stamped into `stats` here.
    stats.repair = repair;
    crate::phase_log::sub("verify:solve", "start", || {
        format!("round=0 repair={repair:?}")
    });
    let started = std::time::Instant::now();
    let first = solve_round(
        solver,
        selectors,
        backend,
        hard.as_ref(),
        planner.as_ref(),
        &mut stats,
    );
    crate::phase_log::sub("verify:solve", "end", || {
        format!(
            "round=0 sat={} wall={:.1}s z3={}",
            first.is_some(),
            started.elapsed().as_secs_f64(),
            crate::phase_log::z3_summary()
        )
    });
    let Some((mut model, dropped)) = first else {
        return (None, stats);
    };
    record_dropped(&mut stats, selectors, &dropped);
    // The raw-cause ledger's inputs -- every plain-repair commit with
    // its track, and the selectors the accepted round dropped.
    let ledger = super::raw_cause::enabled();
    let mut ledger_commits: Vec<super::raw_cause::Commit> = Vec::new();
    let mut last_dropped = dropped;
    for _ in 0..cap {
        // Relay main/375 §3: the analysis budget ends the solve at a round's start.
        if crate::analysis_budget::over("solve:round") {
            return (None, stats);
        }
        stats.rounds += 1;
        crate::phase_log::mark(
            "solve:round",
            "start",
            &format!("round={} repair={repair:?}", stats.rounds),
        );
        // Each round re-runs the oracle under a DIFFERENT candidacy
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
        // A table's reborrow is unique only when a Ref level below it is
        // written -- the round's facts drop the load guard where the loaded level
        // is Raw in THIS round's model.
        let round_facts = round_mutability_facts(program, slots, &model);
        let round_mutable = super::mutability_facts::RoundMut {
            base: is_mutable,
            round: &round_facts,
        };
        // This round's qualifying stores issue no loan on a local that is not
        // `Raw` during the replay.
        let _move_store = super::move_store::enter_round(
            program,
            slots,
            solver.ownership_facts(),
            solver.original_cell_selection(),
            &model,
        );
        let is_ref = |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref);
        // Complete by construction: EVERY non-`Ref` slot is a replay candidate
        // (`is_raw`), so no `Owning` slot is ever EXCLUDED from the replay. A flow-insensitive
        // depth-0 slot can be `Owning` (ownership ORs over versions) yet carry a *reference*
        // role in another version (`p = &mut a; …; p = malloc()`; or via reborrow/`offset`);
        // excluding such a slot as a non-candidate would HIDE its aliasing conflict — an
        // under-report. Including every non-`Ref` slot makes "no hidden `Ref`-vs-`Ref`
        // aliasing" hold by construction, with no need to DETECT mixed-role locals (a tar pit:
        // any syntactic/conflict predicate must re-derive the borrow analysis's full
        // provenance flow — Ref/RawPtr, cast/copy, offset/library methods, … — and such
        // predicates kept missing paths). Treating an `Owning` slot as a raw
        // candidate is strictly MORE conservative (its loans are included, never fewer), so it
        // cannot under-report. RESIDUAL (deferred to flow-sensitivity): a mixed-role local is
        // output `Owning` — an ownership-layer imprecision, NOT a borrow-verifier under-report
        // (the borrow contract = the surviving `Ref` slots do not alias; that holds for the
        // raw-role completeness THIS argument is about — but NOT under the mutability
        // skip, which drops immutable *interprocedural* loans from invalidation: two surviving
        // `Ref`s CAN then alias a written cell via a call-return/param/cast/offset/field alias
        // the coherence equate-closure does not unify. That is the cross-alias write gap at the
        // acceptance level (shared with production), closed by write-aware invalidation). BO
        // output being unconsumed by codegen makes both the imprecision above and the
        // cross-alias write gap harmless until codegen.
        //
        // This predicate is used TWO ways in `revalidate_replaying` and
        // the two owner classes need OPPOSITE semantics. LOCAL replay candidacy stays the
        // conservative non-`Ref` above (an `Owning` local's loans must be INCLUDED, as above). But
        // the field DISABLE list REMOVES loans, so it must be EXACT `Raw`: disabling an `Owning`
        // field's loan would delete a conflict that should decline/demote (an owning + borrow-
        // aliased field → unsound accept). So branch on the owner: fields → exactly `Raw`, locals
        // → non-`Ref`. (`Raw` fields are the only ones the disable list discharges; `Owning` fields fall through
        // to the `residual_nonref_field` decline backstop.)
        let is_raw = |s: SlotRef| match s {
            SlotRef::Field(_) => model.get(&s) == Some(&SlotKind::Raw),
            SlotRef::Local(..) => model.get(&s) != Some(&SlotKind::Ref),
        };
        // The guarded arm reads the witnessed replay -- the same replay with its loans and
        // invalidators, in the same parameter-overlap context and round facts -- and every step
        // before its commit point reads that replay's plain conflicts. The plain repair and Lemmas
        // keep the reviewed replay.
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
                parameter_overlaps,
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
        crate::phase_log::mark(
            "solve:round:replay",
            "end",
            &format!(
                "round={} conflict_fns={}",
                stats.rounds,
                reviewed.conflicts.len()
            ),
        );
        if !reviewed.retirement.unresolved.is_empty() {
            stats.source_retirement_decline = reviewed.retirement.unresolved;
            return (None, stats);
        }
        let raw_targets = reviewed.retirement.raw_targets();
        if !raw_targets.is_empty() {
            if !planner_empty_round(planner.as_mut(), &mut stats, &model) {
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
            stats.commits_conflict += raw_targets.len();
            stats.commits_per_round.push(raw_targets.len());
            let started = std::time::Instant::now();
            let solved = solve_round(
                solver,
                selectors,
                backend,
                hard.as_ref(),
                planner.as_ref(),
                &mut stats,
            );
            crate::phase_log::sub("verify:solve", "end", || {
                format!(
                    "round={} sat={} wall={:.1}s z3={}",
                    stats.rounds,
                    solved.is_some(),
                    started.elapsed().as_secs_f64(),
                    crate::phase_log::z3_summary()
                )
            });
            let Some((next, dropped)) = solved else {
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
            // keeps the plain repair's bound and all solver caps unchanged.
            conflicts.entry(function).or_default().push(SlotConflict {
                issuer: Some(target),
                requirers: Vec::new(),
                esc_issuer_first: false,
            });
        }
        append_retirement_targets(&mut conflicts, &reviewed.retirement);
        // Partition the residual-conflict guard by owner class. A non-`Ref` FIELD in a
        // residual is live-requirer discharge extended to field requirers: the field is a live
        // requirer the Local-only replay candidacy cannot soundly demote (committing it just
        // regenerates the conflict), so DECLINE is the sound outcome — tagged for the sweep's
        // attribution.
        // A non-`Ref` LOCAL residual stays a fail-closed invariant violation: the inert-ness invariant
        // (see `representative`) keeps non-witness `Raw` locals out of residual edges, so a residual
        // local is always `Ref`; a violation is a real under-report, asserted even in release.
        // (No Local fixture forces this arm — its coverage rests on that invariant, not a synthesized
        // case.) The field early-return runs first, so the assert now effectively guards Locals only.
        if let Some(field) = residual_nonref_field(&conflicts, &model) {
            // An OWNING field in a residual is demoted (`¬own`, monotone) instead of
            // declining the program.
            if model.get(&field) == Some(&SlotKind::Owning) {
                if !planner_empty_round(planner.as_mut(), &mut stats, &model) {
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
                let started = std::time::Instant::now();
                let solved = solve_round(
                    solver,
                    selectors,
                    backend,
                    hard.as_ref(),
                    planner.as_ref(),
                    &mut stats,
                );
                crate::phase_log::sub("verify:solve", "end", || {
                    format!(
                        "round={} sat={} wall={:.1}s z3={}",
                        stats.rounds,
                        solved.is_some(),
                        started.elapsed().as_secs_f64(),
                        crate::phase_log::z3_summary()
                    )
                });
                let Some((next, dropped)) = solved else {
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
            // The plain repair: one monotone `¬ref(representative)` per residual edge.
            RepairMode::Plain => {
                // `FxHashMap` iteration is deterministic, but the inner
                // `Vec<ConflictEdge>` follows loan-INDEX order, and loan numbering
                // permutes between runs and between CEGAR rounds
                // (`utils/dsa/union_find.rs` hashes with `RandomState`; `borrow/mod.rs` pushes siblings in `group()`
                // order). So an unsorted z3 assertion sequence would not be stable.
                //
                // Sorted by `conflict_sort_key` — the SAME key the Lemmas arm
                // uses — which is built from slot keys and is therefore
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
                        // Name the conflict a plain-repair commit came from.
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
                            // The clause the guarded planner would assert here.
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
                        // Commit-necessity audit capture (gated; `None` = off, zero cost). Record
                        // `(slot, round)` — `stats.rounds` is this round (incremented at the loop top).
                        // The round is retained for the audit's stratification + over-pin-by-round diagnostic.
                        AUDIT_CAPTURE.with(|c| {
                            if let Some(buf) = c.borrow_mut().as_mut() {
                                buf.push((slot, stats.rounds));
                            }
                        });
                        SELECTOR_CORE_COMMIT_CAPTURE.with(|capture| {
                            if let Some(events) = capture.borrow_mut().as_mut() {
                                events.push(PlainCommitTrace {
                                    #[cfg(test)]
                                    target: slot,
                                    #[cfg(test)]
                                    round: stats.rounds,
                                    #[cfg(test)]
                                    conflict: conflict.clone(),
                                });
                            }
                        });
                    }
                }
            }
            // The guarded planner's clauses at the plain repair's commit point. Reader failures and
            // retirement targets are observations with an empty guard (unconditional `¬ref`, as the
            // plain repair commits); a witnessed conflict's observation carries its loan and its
            // invalidators, those met through a parameter-overlap partner marked. Everything before
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
                );
                match planner.plan_round(GuardedSolverOutcome::Sat, &observations, &model) {
                    GuardedRoundPlan::Accept { validation_round } => {
                        assert_eq!(
                            stats.rounds, validation_round,
                            "guarded planner/fixpoint validation-round counters diverged"
                        );
                    }
                    GuardedRoundPlan::Continue {
                        validation_round,
                        actions,
                    } => {
                        assert_eq!(
                            stats.rounds, validation_round,
                            "guarded planner/fixpoint validation-round counters diverged"
                        );
                        for action in &actions {
                            solver.add_guarded_commit(action);
                            if ledger && let Some(track) = solver.last_track() {
                                use super::raw_cause::CommitKind;
                                let kind = match action.kind {
                                    guarded_repair::CommitActionKind::GuardedCommit => {
                                        CommitKind::GuardedCommit
                                    }
                                    guarded_repair::CommitActionKind::RecurrenceEscalation => {
                                        CommitKind::RecurrenceEscalation
                                    }
                                    guarded_repair::CommitActionKind::UnconditionalCommit
                                        if retirement_targets.contains(&action.target) =>
                                    {
                                        CommitKind::RetirementConflict
                                    }
                                    guarded_repair::CommitActionKind::UnconditionalCommit
                                        if reader_targets.contains(&action.target) =>
                                    {
                                        CommitKind::ReaderObligation
                                    }
                                    guarded_repair::CommitActionKind::UnconditionalCommit => {
                                        CommitKind::BorrowExclusion
                                    }
                                };
                                // Under the guarded repair the ledger names the clause
                                // the planner asserted (its Ref peers and Raw invalidators).
                                ledger_commits.push(super::raw_cause::Commit {
                                    track,
                                    slot: action.target,
                                    round: stats.rounds,
                                    kind,
                                    issuer: None,
                                    clause: Some(super::raw_cause::Clause {
                                        shape: match action.kind {
                                            guarded_repair::CommitActionKind::GuardedCommit => {
                                                "guarded"
                                            }
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
                    GuardedRoundPlan::Decline {
                        validation_round,
                        reason,
                    } => {
                        assert_eq!(
                            stats.rounds, validation_round,
                            "guarded planner/fixpoint validation-round counters diverged"
                        );
                        record_guarded_decline(&mut stats, reason);
                        return (None, stats);
                    }
                }
            }
        }
        stats.commits_per_round.push(committed);
        if committed == 0 {
            // Residual certificate: record the residuals the accepted model
            // TOLERATES. Acceptance is `committed == 0`, not an empty conflict
            // set, so this is non-empty in general. Recording-only.
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
            // No committable residual: a genuine fixpoint. Every non-`Ref` slot was a replay
            // candidate above, so an empty residual means the surviving `Ref` slots genuinely do not
            // alias (no `Owning` slot's reference role is hidden). A `Ref` field residual is
            // committed like any `Ref` slot and a non-`Ref` field residual already declined above, so
            // this path does not silently accept a dropped-`Field` residual.
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
        ) {
            Some((m, dropped)) => {
                record_dropped(&mut stats, selectors, &dropped);
                last_dropped = dropped;
                m
            }
            None => return (None, stats),
        };
    }
    // Cap exhaustion — behaviour depends on the repair mode's termination guarantee. The plain
    // repair has a PROVEN linear bound (each round commits ≥1 fresh slot to a
    // PERMANENT `¬ref`, so ≤ |slots| rounds); reaching the cap there is a real bug → panic. Lemmas
    // has NO such bound: its disjunctions are non-monotone, so the Max-Ref optimizer could in
    // principle walk subsets of a k-requirer edge for up to ~2^k rounds (subset oscillation). That
    // worst case does NOT manifest under the pinned z3 seed — empirically a 33-requirer edge still
    // converges in 3 rounds — but it is not PROVEN impossible, so the
    // cap must be a CONTROLLED backstop, not a crash: return a sound decline (a decline
    // is always legal; BO output being unconsumed keeps it harmless). So a rounds explosion becomes
    // a decline the sweep surfaces, never a panic.
    match repair {
        RepairMode::Plain => panic!(
            "Mode-A CEGAR did not converge within {cap} rounds — this violates the proven linear \
             bound (each round commits ≥1 fresh permanent ¬ref), so it is a genuine analysis bug."
        ),
        // The planner declines at its own cap (10S + 1) one round before this bound, so
        // reaching it is a planner defect; decline, which falls back to the plain repair.
        RepairMode::Guarded => {
            stats.cap_exhausted = true;
            (None, stats)
        }
    }
}

/// Tell the guarded planner of a round whose commits are not its own (the retirement
/// pins, the field-own repair), so its validation counter stays equal to `stats.rounds`. `false`
/// when the planner declines (its cap). A no-op outside the guarded mode.
fn planner_empty_round(
    planner: Option<&mut Planner>,
    stats: &mut RoundStats,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> bool {
    let Some(planner) = planner else {
        return true;
    };
    match planner.plan_round(GuardedSolverOutcome::Sat, &[], model) {
        GuardedRoundPlan::Accept { validation_round } => {
            assert_eq!(
                stats.rounds, validation_round,
                "guarded planner/fixpoint validation-round counters diverged"
            );
            true
        }
        GuardedRoundPlan::Decline { reason, .. } => {
            record_guarded_decline(stats, reason);
            false
        }
        GuardedRoundPlan::Continue { .. } => {
            panic!("empty L2 observations produced commit actions")
        }
    }
}

/// One guarded round's observations, built as the separate guarded loop builds them: reader failures
/// and retirement targets with an empty guard, then every witnessed conflict with a committable
/// representative. The planner orders them canonically.
fn guarded_observations(
    reader_failures: &[super::licensing::reader_replay::Failure],
    retirement: &super::retirement::RetirementReview,
    witnessed: &FxHashMap<LocalDefId, Vec<WitnessedSlotConflict>>,
    model: &FxHashMap<SlotRef, SlotKind>,
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
            observations.push(observation);
        }
    }
    observations
}

/// No production route reaches this loop. `RepairMode::Guarded` is the guarded arm of the one
/// loop above; this separate loop is kept as the door the guarded-repair tests call directly.
///
/// `pub(crate)` so a test can route through the guarded loop **directly**, without
/// perturbing process-wide state inside a parallel test binary.
///
/// # Preconditions this door must carry
///
/// Two preconditions:
///
/// - **`solver.tracker().is_none()`.** A tracked solver's hard constraints are
///   track-gated, so every solve here would be vacuously SAT and the accepted
///   model meaningless. Opening this door does **not** leave that unguarded:
///   `KindSolver::check`, `model_kinds`, and `model_kinds_relaxing` each carry
///   their own release-active guard, and the loop cannot extract a model
///   without passing one. The `debug_assert!` below is a *fail-earlier*
///   tripwire — it names the door in the message instead of the accessor — not
///   the only thing standing between a tracked solver and a meaningless model.
/// - **`RepairMode::current() == Plain` — INERT here.** This loop stamps
///   `repair: RepairMode::Plain` into its own stats and never reads
///   `RepairMode::current()`, so violating it changes nothing about what runs.
///   Documented for callers, not enforced.
#[cfg(test)]
pub(crate) fn verify_guarded_to_fixpoint_counting(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
    copy_lends: Option<&FxHashSet<CopyLendPair>>,
    escaped_copy_lends: Option<&SelectedCopyLendLoans>,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    verify_guarded_to_fixpoint_counting_impl(
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

/// The guarded repair's own fixpoint loop, as a separate driver.
#[cfg(test)]
pub(super) fn verify_guarded_to_fixpoint_counting_impl(
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
    // Re-assert the load-bearing precondition at the door, not only at the
    // entry. `debug_assert!` rather than `assert!` so the release-path cost
    // and behaviour of the existing single choke point are unchanged.
    debug_assert!(
        !solver.is_diagnostic_tracked(),
        "diagnostic-tracked KindSolver must not enter the guarded-repair door"
    );
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
        repair: RepairMode::Plain,
        ..RoundStats::default()
    };

    let (mut model, dropped) =
        match solve_guarded_round_model(solver, selectors, backend, hard.as_ref()) {
            GuardedSolveResult::Sat { kinds, dropped } => (kinds, dropped),
            GuardedSolveResult::Unsat => {
                record_guarded_decline(
                    &mut stats,
                    GuardedDeclineReason::Solver(GuardedSolverDecline::Unsat),
                );
                return (None, stats);
            }
            GuardedSolveResult::Unknown => {
                record_guarded_decline(
                    &mut stats,
                    GuardedDeclineReason::Solver(GuardedSolverDecline::Unknown),
                );
                return (None, stats);
            }
        };
    record_dropped(&mut stats, selectors, &dropped);

    loop {
        stats.rounds += 1;
        // Same per-round reset on the guarded path.
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
            return (None, stats);
        }
        let raw_targets = reviewed.retirement.raw_targets();
        if !raw_targets.is_empty() {
            // A typed coverage repair is independent of the guarded loan clauses.
            // Keep its validation-round accounting honest without inventing a loan.
            #[cfg(test)]
            if coverage_planner_fault::active() {
                planner = Planner::new(usize::MAX);
            }
            match planner.plan_round(GuardedSolverOutcome::Sat, &[], &model) {
                GuardedRoundPlan::Accept { validation_round } => {
                    assert_eq!(
                        stats.rounds, validation_round,
                        "L2 coverage/planner validation counters diverged"
                    );
                }
                GuardedRoundPlan::Decline { reason, .. } => {
                    record_guarded_decline(&mut stats, reason);
                    return (None, stats);
                }
                GuardedRoundPlan::Continue { .. } => {
                    panic!("empty L2 observations produced commit actions")
                }
            }
            for target in &raw_targets {
                solver.assume(*target, SlotKind::Raw);
            }
            stats.commits_conflict += raw_targets.len();
            stats.commits_per_round.push(raw_targets.len());
            match solve_guarded_round_model(solver, selectors, backend, hard.as_ref()) {
                GuardedSolveResult::Sat { kinds, dropped } => {
                    model = kinds;
                    record_dropped(&mut stats, selectors, &dropped);
                    continue;
                }
                GuardedSolveResult::Unsat => {
                    record_guarded_decline(
                        &mut stats,
                        GuardedDeclineReason::Solver(GuardedSolverDecline::Unsat),
                    );
                    return (None, stats);
                }
                GuardedSolveResult::Unknown => {
                    record_guarded_decline(
                        &mut stats,
                        GuardedDeclineReason::Solver(GuardedSolverDecline::Unknown),
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
            }
        }

        let actions = match planner.plan_round(GuardedSolverOutcome::Sat, &observations, &model) {
            GuardedRoundPlan::Accept { validation_round } => {
                assert_eq!(
                    stats.rounds, validation_round,
                    "L2 planner/fixpoint validation-round counters diverged"
                );
                stats.commits_per_round.push(0);
                super::licensing::stack_export::accept(solver.ownership_facts());
                return (Some(model), stats);
            }
            GuardedRoundPlan::Continue {
                validation_round,
                actions,
            } => {
                assert_eq!(
                    stats.rounds, validation_round,
                    "L2 planner/fixpoint validation-round counters diverged"
                );
                actions
            }
            GuardedRoundPlan::Decline {
                validation_round,
                reason,
            } => {
                assert_eq!(
                    stats.rounds, validation_round,
                    "L2 planner/fixpoint validation-round counters diverged"
                );
                record_guarded_decline(&mut stats, reason);
                return (None, stats);
            }
        };

        for action in &actions {
            solver.add_guarded_commit(action);
        }
        stats.commits_conflict += actions.len();
        stats.commits_per_round.push(actions.len());

        match solve_guarded_round_model(solver, selectors, backend, hard.as_ref()) {
            GuardedSolveResult::Sat { kinds, dropped } => {
                model = kinds;
                record_dropped(&mut stats, selectors, &dropped);
            }
            GuardedSolveResult::Unsat => {
                record_guarded_decline(
                    &mut stats,
                    GuardedDeclineReason::Solver(GuardedSolverDecline::Unsat),
                );
                return (None, stats);
            }
            GuardedSolveResult::Unknown => {
                record_guarded_decline(
                    &mut stats,
                    GuardedDeclineReason::Solver(GuardedSolverDecline::Unknown),
                );
                return (None, stats);
            }
        }
    }
}

/// Record why the guarded repair declined; the program then falls back to the plain repair.
fn record_guarded_decline(stats: &mut RoundStats, reason: GuardedDeclineReason) {
    stats.guarded_decline = Some(reason);
}

/// Commit-necessity audit — does `model` ACCEPT, i.e. is it a plain-repair fixpoint? True iff one
/// more validate round would commit nothing: no residual conflict names a non-`Ref` FIELD
/// (`residual_nonref_field` — the field-decline) AND every residual conflict's live-requirer `representative` is
/// `None` (no committable `Ref` owner, so `committed` would be 0). This is EXACTLY
/// `verify_to_fixpoint_counting`'s accept condition, factored out so the audit's "one solve + one
/// validate" classification shares the loop's accept semantics rather than a re-derived twin that could
/// drift — the `is_ref`/`is_raw` replay closures are byte-identical to the loop's (non-`Ref` for
/// locals, exact-`Raw` for fields). The anchor asserts `model_accepts(accepted_model)`; calibration
/// tests pin both classification arms.
#[cfg(test)]
pub(crate) fn model_accepts(
    program: &RustProgram,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    is_mutable: impl MutProvider + Copy,
) -> bool {
    let origin_flows = super::origin_flow::analyze_program_origin_flow(program);
    model_accepts_with_flows(program, slots, &origin_flows, model, is_mutable)
}

#[cfg(test)]
pub(crate) fn model_accepts_with_flows(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    model: &FxHashMap<SlotRef, SlotKind>,
    is_mutable: impl MutProvider + Copy,
) -> bool {
    model_accepts_with_flows_impl(program, slots, origin_flows, model, is_mutable, None)
}

#[cfg(test)]
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

#[cfg(test)]
fn model_accepts_with_flows_impl(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    model: &FxHashMap<SlotRef, SlotKind>,
    is_mutable: impl MutProvider + Copy,
    selected_copy_lends: Option<&SelectedCopyLendLoans>,
) -> bool {
    // ALLOW-LIST TRIPWIRE. This is a PROBE — an oracle run
    // outside either CEGAR loop, on a model the loop may never have accepted.
    // Under the allow-list it is outside the armed region and records nothing
    // by construction, so suspending capture here would be redundant.
    //
    // An assertion stands here instead of a suspension, and that choice is
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
    // fail-closed STOP). A probe model CAN reach a non-`Ref`-local residual (unlike
    // the live loop), where `representative` returns `None` and the naive "no committable owner" check
    // would MIS-accept; including `guard_slots_are_ref` rejects it, matching the loop exactly.
    residual_nonref_field(&conflicts, model).is_none()
        && guard_slots_are_ref(&conflicts, model)
        && conflicts
            .values()
            .flatten()
            .all(|c| representative(c, model).is_none())
}

/// Pick the slot of a residual conflict to commit `¬ref` on (the plain repair).
///
/// **Live-requirer discharge.** Demoting a slot discharges an edge only if it
/// removes the **conflict**, not the **requirement**. Demoting the *issuer* removes its loan
/// from the ANALYSIS (the replay disables that provenance and the loan disappears next round),
/// but a live `Ref` **requirer** of that loan still aliases the written cell — it is not made
/// safe by the issuer going `Raw`. So when a live `Ref` requirer exists **beyond** the issuer,
/// it must carry the discharge; the issuer stays in the menu only when no such requirer exists
/// (self-edges, issuer-only edges).
///
/// This RESTRICTS the commit menu — it introduces no new assertion kind, so the invariant that
/// lemmas are `¬ref`-only is untouched. Without it, `x = id(p); …; *b = 2;` (b = p) accepts
/// `p`/`b` = `Raw` while `x` survives `Ref` — a shared reference into a cell written through a
/// raw alias (the cross-alias write family, shared with production, harmless while BO output is
/// unconsumed). The discharge's reach is a property of the edge menu, so it closes the IMMUTABLE
/// shape too — orthogonal to the immutable-loan skip.
///
/// Returns `None` only when no owner of the conflict is currently `Ref`. This cannot
/// arise on the live path — a non-`Ref` field residual is decline-intercepted (`residual_nonref_field`)
/// and a non-`Ref` `Local` residual is assert-intercepted (`guard_slots_are_ref`) before this runs, so
/// every conflict reaching here has a committable `Ref` owner (`Local` OR field). A residual `Local`
/// owner is always `Ref` anyway: `borrow_conflicts_replaying`'s inert-ness invariant keeps non-witness
/// `Raw` locals out of residual edges. The `None` arm is kept defensive (e.g. an empty edge).
fn representative(
    conflict: &SlotConflict,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Option<SlotRef> {
    // The plain repair's single pick is the FIRST member of the live-requirer menu
    // (`a_prime_menu`'s order-preserving de-dup never changes the first element).
    a_prime_menu(conflict, model).into_iter().next()
}

/// The live-requirer-restricted commit menu as a **set** (the `Lemmas` disjunction `⋁¬ref(menu)`
/// ranges over exactly this). Same discipline as `representative` (which is its first element):
/// a live `Ref` requirer BEYOND the issuer must carry the discharge, so if any exist the menu is
/// **exactly those requirers — the issuer is NOT offered** (the disjunction's soundness
/// invariant; offering the issuer would let the solver discharge by demoting it while a live `Ref`
/// requirer keeps aliasing the written cell, the cross-alias write hole). Otherwise (self-edges, issuer-only
/// edges) the menu is the `Ref` owners, issuer first. Order-preserving de-dup keeps the emitted
/// clause (and the reported lemma set) minimal. Empty iff no owner is currently `Ref` — which the
/// `residual_nonref_field` decline + `guard_slots_are_ref` assert rule out on the live path.
fn a_prime_menu(conflict: &SlotConflict, model: &FxHashMap<SlotRef, SlotKind>) -> Vec<SlotRef> {
    let is_ref = |s: &SlotRef| model.get(s) == Some(&SlotKind::Ref);
    if conflict.esc_issuer_first {
        let issuer = conflict.issuer.expect(
            "escape-minimal selected conflict presentation must carry a resolved-source issuer",
        );
        assert!(
            is_ref(&issuer),
            "escape-minimal selected conflict persisted after its resolved source was demoted"
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

/// A stable total-order key for a `SlotRef` (`SlotRef: !Ord`, because `LocalDefId`
/// is not; `SlotId` IS orderable). Variant tag orders `Field < Local`; within each, by the
/// underlying id(s). Used to canonicalize the emission order.
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
    /// Test-only round-cap override so a test can FORCE cap exhaustion
    /// (the oscillation blowup does not manifest naturally). `None` ⇒ the real `n + 8` bound.
    static CAP_OVERRIDE: Cell<Option<usize>> = const { Cell::new(None) };
}

/// Generous round-cap backstop for `verify_to_fixpoint`. The real bound is ≤ |slots|
/// (each round commits a fresh slot off `Ref`); `n + slack` covers it with margin. Not
/// the termination guarantee — only a panic tripwire (the plain repair) / decline backstop (Lemmas). A
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

/// The first `SlotRef::Field` in a residual conflict the model left non-`Ref` (a field
/// that owns/borrow-aliases a written cell). The loop declines on this: it is not a committable
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
/// `residual_nonref_field` runs first, so any non-`Ref` slot reaching this guard
/// is a `Local` (a genuine violation).
/// Release-active: a violation = a model with a live residual conflict whose
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
/// local's depth-0 slot; a `Field` owner maps to the global struct-field slot's
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
    //! The live-requirer menu-restriction invariant, tested directly on the private
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
    /// the live-requirer menu is EXACTLY those requirers — the issuer is NOT offered, even though
    /// it is `Ref` and in the naive issuer∪requirers menu. (Offering it would let the solver
    /// discharge by demoting the issuer while a live `Ref` requirer keeps aliasing the written
    /// cell — the cross-alias write hole the lemma must not permit.)
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
        // The plain repair's single pick is the menu's first element.
        assert_eq!(representative(&conflict, &m), Some(r1));
    }

    /// Else-branch: no requirer beyond the issuer ⇒ the issuer IS the menu (self / issuer-only
    /// edges keep the unrestricted behavior — the restriction never empties a real edge).
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

    /// A non-`Ref` requirer beyond the issuer is not a LIVE requirer, so it does not trip the
    /// live-requirer "if" branch — the menu falls back to the `Ref` owners (here the issuer).
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

    /// The exact escape-minimal class has a different kill switch. Its
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
