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

use super::{
    crate_slots::CrateSlots,
    solver::{KindSolver, SlotRef},
};
use crate::{
    analyses::borrow::{self, ProvenanceOwner},
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
