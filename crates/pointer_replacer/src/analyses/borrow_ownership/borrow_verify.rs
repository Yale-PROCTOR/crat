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

use rustc_hash::FxHashMap;
use rustc_middle::mir::Local;
use rustc_span::def_id::LocalDefId;
use z3::ast::Bool;

use super::{
    SlotKind,
    crate_slots::CrateSlots,
    mutability_facts::MutProvider,
    slots::{SlotId, SlotOwner},
    solver::{KindSolver, Selectors, SlotRef},
};
use crate::{
    analyses::borrow::{self, ConflictEdge, ProvenanceOwner},
    utils::rustc::RustProgram,
};

/// A borrow conflict edge with its owners translated to BO `SlotRef`s. `Field` owners
/// are dropped in BB0 (Local-only); `issuer` is `None` for a non-`Assign` borrower.
#[derive(Clone, Debug)]
pub(crate) struct SlotConflict {
    pub issuer: Option<SlotRef>,
    pub requirers: Vec<SlotRef>,
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
            super::borrow_engine::borrow_conflicts(program, cand, mutab)
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
            borrow::borrow_conflicts_replaying(program, cand, raw, mutab)
        }
        super::borrow_engine::ForkEngineMode::Fork => {
            super::borrow_engine::borrow_conflicts_replaying(program, cand, raw, mutab, &raw_fields)
        }
    };

    map_edges_to_slots(slots, edges)
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
    // §NB5-M: thin wrapper over the single counting loop (model only). KEEP THIN — any logic
    // added here but not in `verify_to_fixpoint_counting` diverges the sweep's counters from what
    // the suite verifies (exactly the mirror-drift the retired bo_c1 mirror guarded; wrapper-
    // thinness is now the guard — see `verify_to_fixpoint_is_thin_wrapper`).
    verify_to_fixpoint_counting(program, slots, solver, selectors, is_mutable).0
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
    // §NB-R guard (release-active): a tracked solver's hard constraints are
    // track-gated; every solve in this loop would be vacuously SAT and the
    // accepted model meaningless. Tracked instances belong to the explain path.
    assert!(
        solver.tracker().is_none(),
        "tracked KindSolver must not enter verify_to_fixpoint (constraints are track-gated)"
    );
    let cap = round_cap(slots);
    // §9.10.2 — constrain each struct-field slot's ownership to `field.own <=> AND(stored
    // owns)`, so a field mixing an owned source and a borrowed value settles non-Owning (the
    // flow-insensitive global-field over-claim). Must precede the first solve.
    super::coherence::constrain_field_ownership(solver, slots, program);
    // §NB-F: classify a dropped-selector set into leak counts (native counter, was the mirror's).
    let record_dropped = |stats: &mut RoundStats, dropped: &[Bool]| {
        stats.dropped_sinks = dropped.iter().filter(|d| selectors.is_sink(d)).count();
        stats.dropped_sources = dropped.len() - stats.dropped_sinks;
    };
    let mut stats = RoundStats::default();
    let Some((mut model, dropped)) = solver.model_kinds_relaxing_reporting(selectors) else {
        return (None, stats);
    };
    record_dropped(&mut stats, &dropped);
    for _ in 0..cap {
        stats.rounds += 1;
        let conflicts = revalidate_replaying(
            program,
            slots,
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
        for conflict in conflicts.values().flatten() {
            if let Some(slot) = representative(conflict, &model) {
                // Single-literal exclusion = a monotone `¬ref(slot)` commitment.
                solver.add_borrow_exclusion(Some(slot), &[]);
                committed += 1;
                stats.commits_conflict += 1;
            }
        }
        stats.commits_per_round.push(committed);
        if committed == 0 {
            // No committable residual: a genuine fixpoint. Every non-`Ref` slot was a replay
            // candidate above, so an empty residual means the surviving `Ref` slots genuinely do not
            // alias (no `Owning` slot's reference role is hidden). §NB5-F: a `Ref` field residual is
            // committed like any `Ref` slot and a non-`Ref` field residual already declined above, so
            // this path no longer silently accepts a dropped-`Field` residual (the old Local-only gap).
            return (Some(model), stats);
        }
        model = match solver.model_kinds_relaxing_reporting(selectors) {
            Some((m, dropped)) => {
                record_dropped(&mut stats, &dropped);
                m
            }
            None => return (None, stats),
        };
    }
    panic!("BB2-ii CEGAR did not converge within {cap} rounds");
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
fn representative(conflict: &SlotConflict, model: &FxHashMap<SlotRef, SlotKind>) -> Option<SlotRef> {
    let is_ref = |s: &SlotRef| model.get(s) == Some(&SlotKind::Ref);
    // A′: a live `Ref` requirer BEYOND the issuer must carry the discharge.
    if let Some(r) = conflict
        .requirers
        .iter()
        .copied()
        .find(|r| Some(*r) != conflict.issuer && is_ref(r))
    {
        return Some(r);
    }
    // No requirer beyond the issuer ⇒ the pre-A′ menu (issuer first, then requirers).
    conflict
        .issuer
        .into_iter()
        .chain(conflict.requirers.iter().copied())
        .find(is_ref)
}

/// Generous round-cap backstop for `verify_to_fixpoint`. The real bound is ≤ |slots|
/// (each round commits a fresh slot off `Ref`); `n + slack` covers it with margin. Not
/// the termination guarantee — only a panic tripwire if the monotone bound is wrong.
fn round_cap(slots: &CrateSlots) -> usize {
    let n: usize = slots.field_slots.len()
        + slots.fn_local_slots.values().map(|u| u.len()).sum::<usize>();
    n + 8
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
fn owner_to_slot(slots: &CrateSlots, fn_did: LocalDefId, owner: ProvenanceOwner) -> Option<SlotRef> {
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
