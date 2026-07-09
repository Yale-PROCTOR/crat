//! §NB1 — per-access-site safety monotonicity (SAFE-MONO).
//!
//! `safe(x) ≡ ¬raw(x)` (one-hot: safe = Ref ∨ Owning). For every MIR place
//! access that dereferences pointer layers ℓ₀,…,ℓₖ to reach a modeled target
//! slot `s`, assert `safe(s) ⇒ safe(ℓᵢ)` for each traversed layer — a safe
//! reference/owner cannot sit behind a raw (dangling) pointer we dereferenced
//! to reach it. Encoded `¬safe(s) ∨ safe(ℓ)` (`solver::safe_mono`), it is
//! `¬safe`-only: it may only shrink the safe region, never force `ref`/`own`
//! (theorems-doc invariant 7).
//!
//! This subsumes the structural `i1-adjacency` chain clause (which forbids only
//! `raw(d) ∧ own(d+1)` on same-owner adjacent pairs): it also forbids the
//! `raw ∧ ref` inversion, and — being driven by real access sites via
//! `resolve_place`'s traversed-layer path — it spans the struct-field boundary
//! (`(*s).f` pairs the field target with the parent-pointer layer) that
//! per-universe slot adjacency cannot reach.

use rustc_hash::FxHashSet;
use rustc_middle::mir::{
    Body, Location, Place,
    visit::{MutatingUseContext, PlaceContext, Visitor},
};
use rustc_span::def_id::LocalDefId;

use super::{
    crate_slots::CrateSlots,
    resolve::{ResolvedSlot, resolve_place},
    solver::{KindSolver, SlotRef},
};

fn to_slot_ref(r: ResolvedSlot, fn_did: LocalDefId) -> SlotRef {
    match r {
        ResolvedSlot::Local(id) => SlotRef::Local(fn_did, id),
        ResolvedSlot::Field(id) => SlotRef::Field(id),
    }
}

/// §NB1: emit per-site SAFE-MONO clauses for one function body. Every place
/// accessed in a statement OR terminator that resolves to a modeled target slot
/// through ≥1 dereferenced pointer layer yields `safe(target) ⇒ safe(layer)`
/// per layer. Clauses are deduplicated within the body; crate-wide dedup is
/// unnecessary (z3 makes a repeated hard clause idempotent).
pub(crate) fn add_safety_mono<'tcx>(
    solver: &KindSolver,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
) {
    let mut walker = SafeMonoWalker {
        solver,
        slots,
        fn_did,
        body,
        seen: FxHashSet::default(),
    };
    walker.visit_body(body);
}

struct SafeMonoWalker<'a, 'tcx> {
    solver: &'a KindSolver,
    slots: &'a CrateSlots,
    fn_did: LocalDefId,
    body: &'a Body<'tcx>,
    seen: FxHashSet<(SlotRef, SlotRef)>,
}

impl<'tcx> Visitor<'tcx> for SafeMonoWalker<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _location: Location) {
        // §NB1: SAFE-MONO applies where the place's VALUE is loaded/read or a
        // reference is borrowed from it — the site where a "safe reference behind
        // the layers" is actually formed. A pure OVERWRITE destination
        // (`(*s).f = x`, `*out = malloc()`, call/yield destinations, deinit,
        // set-discriminant, asm output, drop) does NOT dereference the target's
        // old value as a reference: writing THROUGH `s` requires `s` valid, but
        // does not constrain the field/target kind by this site (the target's
        // kind is set by its reads and the field-⋀ law). Emitting there
        // spuriously coupled a crate-wide `Owning` field to every parent
        // pointer's kind and over-demoted (Codex review, 2026-07-10). Non-uses
        // (storage markers, debuginfo, user-ty ascriptions) never dereference.
        // Soundness is unaffected either way — SAFE-MONO is heuristic pruning;
        // the acceptance replay (D5) is the soundness carrier.
        let emits = matches!(
            context,
            PlaceContext::NonMutatingUse(_)
                | PlaceContext::MutatingUse(MutatingUseContext::Borrow)
        );
        if !emits {
            return;
        }
        let mut layers = Vec::new();
        let Some(target) =
            resolve_place(self.slots, self.fn_did, self.body, *place, 0, Some(&mut layers))
        else {
            return;
        };
        let target = to_slot_ref(target, self.fn_did);
        for layer in layers {
            let layer = to_slot_ref(layer, self.fn_did);
            if self.seen.insert((target, layer)) {
                self.solver.safe_mono(target, layer);
            }
        }
    }
}
