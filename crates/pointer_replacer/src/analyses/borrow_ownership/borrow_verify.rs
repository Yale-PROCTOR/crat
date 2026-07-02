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
    solver::{KindSolver, SlotRef},
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
    is_mutable: bool,
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
    let is_ref = &is_ref;
    let edges = borrow::borrow_conflicts(
        program,
        move |fn_did| {
            let universe = slots.fn_local_slots.get(&fn_did);
            move |local: Local| {
                universe
                    .and_then(|u| u.slot_for_local_depth(local, 0))
                    .is_some_and(|slot_id| is_ref(SlotRef::Local(fn_did, slot_id)))
            }
        },
        move |_fn_did| move |_local| is_mutable,
    );

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
    is_mutable: bool,
) -> FxHashMap<LocalDefId, Vec<SlotConflict>> {
    let is_ref = &is_ref;
    let is_raw = &is_raw;
    let edges = borrow::borrow_conflicts_replaying(
        program,
        move |fn_did| {
            let universe = slots.fn_local_slots.get(&fn_did);
            move |local: Local| {
                universe
                    .and_then(|u| u.slot_for_local_depth(local, 0))
                    .is_some_and(|slot_id| is_ref(SlotRef::Local(fn_did, slot_id)))
            }
        },
        move |fn_did| {
            let universe = slots.fn_local_slots.get(&fn_did);
            move |local: Local| {
                universe
                    .and_then(|u| u.slot_for_local_depth(local, 0))
                    .is_some_and(|slot_id| is_raw(SlotRef::Local(fn_did, slot_id)))
            }
        },
        move |_fn_did| move |_local| is_mutable,
    );

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

/// §8 BB2-ii + BB3-a — drive the CEGAR validate/re-solve loop to a fixpoint (Mode A).
///
/// The solver must arrive with ownership constraints + per-fn coherence already
/// emitted (so `selectors` are its retractable malloc sources). Each round: solve →
/// derive the candidacy from the model's *actual* Raw/Ref/Owning kinds → commit `¬ref`
/// on (a) every **malloc-source slot the model still marks `Ref`** (BB3-a `Ref ⇒ loan`
/// — a malloc result owns heap and is not a borrow, so it may not be a reference; see
/// `sources::collect_malloc_source_slots`) and (b) **one representative slot per
/// residual borrow conflict** (BB2-ii — issuer if present, else a requirer, see
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
    selectors: &[Bool],
    is_mutable: bool,
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    let cap = round_cap(slots);
    // §8 BB3-a — malloc-source slots (static; computed once). A source owns heap and is
    // not a borrow, so it may not be `Ref`.
    let malloc_sources = super::sources::collect_malloc_source_slots(program, slots);
    // §9.10.2 — constrain each struct-field slot's ownership to `field.own <=> AND(stored
    // owns)`, so a field mixing an owned source and a borrowed value settles non-Owning (the
    // flow-insensitive global-field over-claim). Must precede the first solve.
    super::coherence::constrain_field_ownership(solver, slots, program);
    let mut model = solver.model_kinds_relaxing(selectors)?;
    for _ in 0..cap {
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
            // (the borrow contract = the surviving `Ref` slots do not alias; that holds). The
            // §8 guardrail (BO unconsumed) makes the imprecision harmless.
            |s| model.get(&s) != Some(&SlotKind::Ref),
            is_mutable,
        );
        assert!(
            guard_slots_are_ref(&conflicts, &model),
            "every residual conflict slot must be Ref in the current model"
        );
        let mut committed = 0;
        // §8 BB3-a `Ref ⇒ loan`: demote any malloc-source slot the model still marks
        // `Ref` (a reference to owned heap). `¬ref`, not `raw` — an unleaked source still
        // settles `Owning`; only the unbacked-`Ref` reading is forbidden. Monotone (the
        // `== Ref` gate means a committed source is never re-committed).
        for &slot in &malloc_sources {
            if model.get(&slot) == Some(&SlotKind::Ref) {
                solver.add_borrow_exclusion(Some(slot), &[]);
                committed += 1;
            }
        }
        for conflict in conflicts.values().flatten() {
            if let Some(slot) = representative(conflict, &model) {
                // Single-literal exclusion = a monotone `¬ref(slot)` commitment.
                solver.add_borrow_exclusion(Some(slot), &[]);
                committed += 1;
            }
        }
        if committed == 0 {
            // No committable residual: a genuine fixpoint, or only `Field`-owner
            // residuals (the deferred Local-only gap) — accept for this pass. Because every
            // non-`Ref` slot was a replay candidate above, an empty residual means the surviving
            // `Ref` slots genuinely do not alias (no `Owning` slot's reference role is hidden).
            return Some(model);
        }
        model = solver.model_kinds_relaxing(selectors)?;
    }
    panic!("BB2-ii CEGAR did not converge within {cap} rounds");
}

/// Pick the slot of a residual conflict to commit `¬ref` on (Mode A): the issuer if it
/// is currently `Ref`, else the first currently-`Ref` requirer. Committing the issuer
/// demotes the loan at its source; any conflict that survives surfaces next round.
/// Returns `None` only when the conflict has no committable `Local` owner — i.e. a
/// `Field`-only residual (the deferred struct field-slot gap). A residual `Local` owner
/// is always currently-`Ref`: `borrow_conflicts_replaying`'s inert-ness invariant keeps
/// non-witness `Raw` locals out of residual edges, so an "all owners already `Raw`"
/// residual cannot arise for Locals.
fn representative(conflict: &SlotConflict, model: &FxHashMap<SlotRef, SlotKind>) -> Option<SlotRef> {
    conflict
        .issuer
        .into_iter()
        .chain(conflict.requirers.iter().copied())
        .find(|s| model.get(s) == Some(&SlotKind::Ref))
}

/// Generous round-cap backstop for `verify_to_fixpoint`. The real bound is ≤ |slots|
/// (each round commits a fresh slot off `Ref`); `n + slack` covers it with margin. Not
/// the termination guarantee — only a panic tripwire if the monotone bound is wrong.
fn round_cap(slots: &CrateSlots) -> usize {
    let n: usize = slots.field_slots.len()
        + slots.fn_local_slots.values().map(|u| u.len()).sum::<usize>();
    n + 8
}

/// Invariant tripwire for the loop: every slot in a residual conflict edge must be
/// `Ref` in the current model. `Raw` slots are replay-demoted (witnessed) and `Owning`
/// slots are non-candidates, so a residual edge can only name surviving `Ref`
/// candidates; a violation signals the deferred Owning-issuer / under-report cases.
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

/// Translate a borrow `ProvenanceOwner` to a BO `SlotRef`. BB0 handles `Local` owners
/// (→ the local's depth-0 slot); `Field` owners are dropped pending the field mapping.
fn owner_to_slot(slots: &CrateSlots, fn_did: LocalDefId, owner: ProvenanceOwner) -> Option<SlotRef> {
    match owner {
        ProvenanceOwner::Local(local) => {
            let slot_id = slots
                .fn_local_slots
                .get(&fn_did)?
                .slot_for_local_depth(local, 0)?;
            Some(SlotRef::Local(fn_did, slot_id))
        }
        ProvenanceOwner::Field(_) => None,
    }
}
