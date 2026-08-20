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
    solver::{KindSolver, L2SolveResult, Selectors, SlotRef},
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
/// Selected by env `CRAT_BO_REPAIR ∈ {mode_a, lemmas}` (default `ModeA`; the gate did NOT flip it),
/// or a thread-local `with_override` that WINS over env. A uniform strategy toggle, constant within an
/// override scope — no path-divergence hazard (unlike 4c's threaded origins, which were divergent DATA).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum RepairMode {
    ModeA,
    Lemmas,
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
        match std::env::var("CRAT_BO_REPAIR") {
            Ok(v) => match v.as_str() {
                "mode_a" | "mode-a" => RepairMode::ModeA,
                "lemmas" => RepairMode::Lemmas,
                other => panic!(
                    "CRAT_BO_REPAIR={other:?} is not a valid selector (expected mode_a or lemmas) \
                     — refusing to silently fall back"
                ),
            },
            Err(_) => Self::DEFAULT,
        }
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            RepairMode::ModeA => "mode_a",
            RepairMode::Lemmas => "lemmas",
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
}

#[derive(Clone, Debug)]
struct WitnessedSlotConflict {
    conflict: SlotConflict,
    loan: usize,
    stable_loan_key: Option<StableLoanKey>,
    invalidators: Vec<SlotRef>,
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

    map_edges_to_slots(slots, edges)
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
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
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
    let edges = match super::borrow_engine::ForkEngineMode::current() {
        super::borrow_engine::ForkEngineMode::Production => {
            assert!(
                selected_copy_lends.is_none_or(|selected| selected.is_empty()),
                "CopyLend replay requires the BO fork engine"
            );
            borrow::borrow_conflicts_replaying(program, cand, raw, mutab)
        }
        super::borrow_engine::ForkEngineMode::Fork => match selected_copy_lends {
            Some(selected) => {
                super::borrow_engine::borrow_conflicts_replaying_with_flows_and_copy_lends(
                    program,
                    origin_flows,
                    cand,
                    raw,
                    mutab,
                    &raw_fields,
                    selected,
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
        },
    };

    map_edges_to_slots(slots, edges)
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
) -> FxHashMap<LocalDefId, Vec<WitnessedSlotConflict>> {
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
    let edges = match selected_copy_lends {
        Some(selected) => {
            super::borrow_engine::borrow_conflicts_replaying_witnessed_with_copy_lends(
                program,
                origin_flows,
                cand,
                raw,
                mutab,
                &raw_fields,
                selected,
            )
        }
        None => super::borrow_engine::borrow_conflicts_replaying_witnessed(
            program,
            origin_flows,
            cand,
            raw,
            mutab,
            &raw_fields,
        ),
    };

    edges
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
                    let mut invalidators = witnessed
                        .invalidators
                        .into_iter()
                        .filter_map(|local| {
                            owner_to_slot(slots, fn_did, ProvenanceOwner::Local(local))
                        })
                        .collect::<Vec<_>>();
                    invalidators.sort_by_key(slotref_key);
                    invalidators.dedup();
                    WitnessedSlotConflict {
                        conflict: SlotConflict {
                            issuer,
                            requirers: edge
                                .requirers
                                .into_iter()
                                .filter_map(|owner| owner_to_slot(slots, fn_did, owner))
                                .collect(),
                        },
                        loan,
                        stable_loan_key: issuer.map(|issuer| {
                            StableLoanKey::new(
                                fn_did.local_def_index.as_u32(),
                                issuer,
                                loan_location,
                            )
                        }),
                        invalidators,
                    }
                })
                .collect();
            (fn_did, translated)
        })
        .collect()
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
}

fn record_dropped(stats: &mut RoundStats, selectors: &Selectors, dropped: &[Bool]) {
    stats.dropped_sinks = dropped
        .iter()
        .filter(|item| selectors.is_sink(item))
        .count();
    stats.dropped_sources = dropped.len() - stats.dropped_sinks;
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
    )
}

fn verify_to_fixpoint_counting_with_flows_impl(
    program: &RustProgram,
    slots: &CrateSlots,
    origin_flows: &OriginFlowResults,
    solver: &KindSolver,
    selectors: &Selectors,
    is_mutable: impl MutProvider + Copy,
    copy_lends: Option<&FxHashSet<CopyLendPair>>,
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    // §NB-R guard (release-active): a tracked solver's hard constraints are
    // track-gated; every solve in this loop would be vacuously SAT and the
    // accepted model meaningless. Tracked instances belong to the explain path.
    assert!(
        solver.tracker().is_none(),
        "tracked KindSolver must not enter verify_to_fixpoint (constraints are track-gated)"
    );
    let l2_enabled = l2::enabled_from_env();
    let repair = RepairMode::current();
    if l2_enabled {
        assert_eq!(
            repair,
            RepairMode::ModeA,
            "CRAT_BO_L2_GUARDED_COMMITS=1 requires CRAT_BO_REPAIR=mode_a (or the unset Mode-A default)"
        );
        return verify_l2_to_fixpoint_counting(
            program,
            slots,
            origin_flows,
            solver,
            selectors,
            is_mutable,
            copy_lends,
        );
    }
    let cap = round_cap(slots);
    // §9.10.2 — constrain each struct-field slot's ownership to `field.own <=> AND(stored
    // owns)`, so a field mixing an owned source and a borrowed value settles non-Owning (the
    // flow-insensitive global-field over-claim). Must precede the first solve.
    super::coherence::constrain_field_ownership(solver, slots, program);
    let mut stats = RoundStats::default();
    // §NB5-L guard 1 — resolve the repair strategy ONCE per invocation into a local; NO mid-loop
    // re-reads, so the whole fixpoint runs one consistent strategy. Guard 3 stamps it into `stats`.
    stats.repair = repair;
    let Some((mut model, dropped)) = solver.model_kinds_relaxing_reporting(selectors) else {
        return (None, stats);
    };
    record_dropped(&mut stats, selectors, &dropped);
    for _ in 0..cap {
        stats.rounds += 1;
        // D1: each round re-runs the oracle under a DIFFERENT candidacy
        // predicate. Reset so the export holds the FINAL round's BorrowSet,
        // not the union over rejected intermediate models.
        super::export::begin_round();
        let selected_copy_lends =
            copy_lends.map(|pairs| selected_copy_lend_sites(program, slots, pairs, &model));
        stats.copy_lend_replay_selections = selected_copy_lends
            .as_ref()
            .map(|selected| selected.values().map(FxHashSet::len).sum())
            .unwrap_or(0);
        let conflicts = revalidate_replaying_with_flows(
            program,
            slots,
            origin_flows,
            |s| model.get(&s) == Some(&SlotKind::Ref),
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
            |s| match s {
                SlotRef::Field(_) => model.get(&s) == Some(&SlotKind::Raw),
                SlotRef::Local(..) => model.get(&s) != Some(&SlotKind::Ref),
            },
            is_mutable,
            selected_copy_lends.as_ref(),
        );
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
            stats.field_conflict_decline = Some(field);
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
                let mut ordered: Vec<(LocalDefId, &SlotConflict)> = conflicts
                    .iter()
                    .flat_map(|(did, cs)| cs.iter().map(move |c| (*did, c)))
                    .collect();
                ordered.sort_by(|(da, ca), (db, cb)| {
                    conflict_sort_key(*da, ca).cmp(&conflict_sort_key(*db, cb))
                });
                for (_did, conflict) in ordered {
                    if let Some(slot) = representative(conflict, &model) {
                        // Single-literal exclusion = a monotone `¬ref(slot)` commitment.
                        solver.add_borrow_exclusion(Some(slot), &[]);
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
        }
        stats.commits_per_round.push(committed);
        if committed == 0 {
            // E-R4 certificate: record the residuals the accepted model
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
            // alias (no `Owning` slot's reference role is hidden). §NB5-F: a `Ref` field residual is
            // committed like any `Ref` slot and a non-`Ref` field residual already declined above, so
            // this path no longer silently accepts a dropped-`Field` residual (the old Local-only gap).
            return (Some(model), stats);
        }
        model = match solver.model_kinds_relaxing_reporting(selectors) {
            Some((m, dropped)) => {
                record_dropped(&mut stats, selectors, &dropped);
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
    }
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
) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
    // D17: re-assert the load-bearing precondition at the door, not only at the
    // env entry. `debug_assert!` rather than `assert!` so the release-path cost
    // and behaviour of the existing single choke point are unchanged.
    debug_assert!(
        solver.tracker().is_none(),
        "tracked KindSolver must not enter the l2 door (constraints are track-gated)"
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
    let mut stats = RoundStats {
        repair: RepairMode::ModeA,
        ..RoundStats::default()
    };

    let (mut model, dropped) = match solver.model_kinds_relaxing_reporting_l2(selectors) {
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
        let selected_copy_lends =
            copy_lends.map(|pairs| selected_copy_lend_sites(program, slots, pairs, &model));
        stats.copy_lend_replay_selections = selected_copy_lends
            .as_ref()
            .map(|selected| selected.values().map(FxHashSet::len).sum())
            .unwrap_or(0);
        let conflicts = revalidate_replaying_witnessed(
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
        );
        let mut observations = Vec::new();
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
                    observation = observation.with_loan_identity(witnessed.loan, stable_loan_key);
                }
                observations.push(observation);
                if diagnostics_enabled {
                    let record = if let Some(stable_loan_key) = witnessed.stable_loan_key {
                        l2::conflict_witness_diagnostic_stable(
                            stats.rounds,
                            did.local_def_index.as_u32(),
                            witnessed.loan,
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
                            witnessed.loan,
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

        match solver.model_kinds_relaxing_reporting_l2(selectors) {
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
    let conflicts = revalidate_replaying_with_flows(
        program,
        slots,
        origin_flows,
        |s| model.get(&s) == Some(&SlotKind::Ref),
        |s| match s {
            SlotRef::Field(_) => model.get(&s) == Some(&SlotKind::Raw),
            SlotRef::Local(..) => model.get(&s) != Some(&SlotKind::Ref),
        },
        is_mutable,
        None,
    );
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
        };
        let m = model(&[(i, SlotKind::Ref), (r, SlotKind::Raw)]);
        assert_eq!(a_prime_menu(&conflict, &m), vec![i]);
    }
}
