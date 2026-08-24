use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::{AggregateKind, Body, Location, Operand, PlaceElem, Rvalue, StatementKind};
use rustc_span::def_id::LocalDefId;
use z3::ast::Bool;

use super::{
    SlotKind,
    boundary_table::{self, Matcher},
    crate_slots::{CrateSlots, MAX_SLOT_DEPTH},
    export::{BorrowerKind, OwnerKey, PlaceKey},
    l2::MirLocationKey,
    resolve::{ResolvedSlot, resolve_place},
    slots::StructFieldSlot,
    solver::{KindSolver, SlotRef},
};
use crate::{
    analyses::mir::{CallKind, TerminatorExt},
    utils::rustc::RustProgram,
};

fn to_slot_ref(r: ResolvedSlot, fn_did: LocalDefId) -> SlotRef {
    match r {
        ResolvedSlot::Local(id) => SlotRef::Local(fn_did, id),
        ResolvedSlot::Field(id) => SlotRef::Field(id),
    }
}

/// A12's pair-global depth-zero eligibility result. Construction is deliberately separate from
/// coherence: the final producer combines Foster mutability, closed origin flow, and MIR liveness;
/// this type is only the narrow solver/coherence handoff.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CopyLendPair {
    pub(crate) lhs: SlotRef,
    pub(crate) rhs: SlotRef,
}

impl CopyLendPair {
    pub(crate) fn new(lhs: SlotRef, rhs: SlotRef) -> Self {
        Self { lhs, rhs }
    }
}

/// Build the ownership emitter's per-site view of the same pair-global plan coherence consumes.
/// The value is the exact kind-layer guard, so the two halves cannot choose different arms.
pub(crate) fn copy_lend_guards_for_body(
    solver: &KindSolver,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'_>,
    copy_lends: &FxHashSet<CopyLendPair>,
) -> FxHashMap<Location, Bool> {
    let mut guards = FxHashMap::default();
    for (block, bbdata) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in bbdata.statements.iter().enumerate() {
            let StatementKind::Assign(box (lhs_place, rvalue)) = &stmt.kind else {
                continue;
            };
            let rhs_place = match rvalue {
                Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))
                | Rvalue::CopyForDeref(rhs) => rhs,
                _ => continue,
            };
            let (Some(lhs), Some(rhs)) = (
                resolve_place(slots, fn_did, body, *lhs_place, 0, None),
                resolve_place(slots, fn_did, body, *rhs_place, 0, None),
            ) else {
                continue;
            };
            let pair = CopyLendPair::new(to_slot_ref(lhs, fn_did), to_slot_ref(rhs, fn_did));
            if copy_lends.contains(&pair) {
                guards.insert(
                    Location {
                        block,
                        statement_index,
                    },
                    solver.lend_guard(pair.lhs, pair.rhs),
                );
            }
        }
    }
    guards
}

/// Stable identity of the one loan synthesized by a selected copy-lend arm. Location alone is not
/// sufficient: grouped provenance can synthesize companion loans at the same statement, and those
/// retain the existing-loan invalidation semantics.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SelectedCopyLendLoan {
    pub(crate) location: MirLocationKey,
    pub(crate) borrowed: PlaceKey,
    pub(crate) borrower: BorrowerKind,
}

pub(crate) type SelectedCopyLendLoans = FxHashMap<LocalDefId, FxHashSet<SelectedCopyLendLoan>>;

/// Read the selected CopyLend sites from the same accepted kind model replay will validate.
pub(crate) fn selected_copy_lend_sites(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    copy_lends: &FxHashSet<CopyLendPair>,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> SelectedCopyLendLoans {
    let mut selected = FxHashMap::default();
    for &fn_did in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        for (block, bbdata) in body.basic_blocks.iter_enumerated() {
            for (statement_index, stmt) in bbdata.statements.iter().enumerate() {
                let StatementKind::Assign(box (lhs_place, rvalue)) = &stmt.kind else {
                    continue;
                };
                let rhs_place = match rvalue {
                    Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))
                    | Rvalue::CopyForDeref(rhs) => rhs,
                    _ => continue,
                };
                let (Some(lhs), Some(rhs)) = (
                    resolve_place(slots, fn_did, &body, *lhs_place, 0, None),
                    resolve_place(slots, fn_did, &body, *rhs_place, 0, None),
                ) else {
                    continue;
                };
                let pair = CopyLendPair::new(to_slot_ref(lhs, fn_did), to_slot_ref(rhs, fn_did));
                if copy_lends.contains(&pair)
                    && model.get(&pair.lhs) == Some(&SlotKind::Ref)
                    && model.get(&pair.rhs) == Some(&SlotKind::Owning)
                {
                    let borrowed = rhs_place.project_deeper(&[PlaceElem::Deref], program.tcx);
                    selected
                        .entry(fn_did)
                        .or_insert_with(FxHashSet::default)
                        .insert(SelectedCopyLendLoan {
                            location: MirLocationKey::new(block.as_u32(), statement_index),
                            borrowed: PlaceKey::from_place(borrowed),
                            borrower: BorrowerKind::Assign {
                                owner: OwnerKey::Local(lhs_place.local.as_u32()),
                            },
                        });
                }
            }
        }
    }
    selected
}

fn with_use_track_context<T>(_solver: &KindSolver, tag_uses: bool, f: impl FnOnce() -> T) -> T {
    #[cfg(test)]
    if tag_uses {
        return _solver
            .tracker()
            .expect("Use-track tagging requires a tracked solver")
            .with_context("coherence-use", f);
    }

    debug_assert!(!tag_uses);
    f()
}

fn add_coherence_impl<'tcx>(
    solver: &KindSolver,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    tag_uses: bool,
    copy_lends: Option<&FxHashSet<CopyLendPair>>,
    remove_copy_equates: bool,
) {
    for bbdata in body.basic_blocks.iter() {
        for stmt in &bbdata.statements {
            let StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind else {
                continue;
            };

            match rvalue {
                Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))
                | Rvalue::CopyForDeref(rhs) => {
                    with_use_track_context(solver, tag_uses, || {
                        if remove_copy_equates {
                            return;
                        }
                        for d in 0..MAX_SLOT_DEPTH {
                            if let (Some(la), Some(ra)) = (
                                resolve_place(slots, fn_did, body, *lhs, d, None),
                                resolve_place(slots, fn_did, body, *rhs, d, None),
                            ) {
                                // §9.10.2: a field STORE's depth-0 ownership is set crate-wide by
                                // `constrain_field_ownership` (`field.own <=> AND stored owns`), so
                                // skip the per-store equate here — equating multiple stores to one
                                // global field slot is what transitively dragged a borrowed value
                                // to `Owning`. (Field LOADS have a Local lhs and still equate.)
                                if d == 0 && matches!(la, ResolvedSlot::Field(_)) {
                                    continue;
                                }
                                let lhs = to_slot_ref(la, fn_did);
                                let rhs = to_slot_ref(ra, fn_did);
                                if d == 0
                                    && copy_lends.is_some_and(|pairs| {
                                        pairs.contains(&CopyLendPair::new(lhs, rhs))
                                    })
                                {
                                    solver.lend_or_equate(lhs, rhs);
                                } else {
                                    solver.equate(lhs, rhs);
                                }
                            }
                        }
                    });
                }
                Rvalue::Ref(_, _, rhs) | Rvalue::RawPtr(_, rhs) => {
                    for d in 0..MAX_SLOT_DEPTH {
                        if let (Some(la), Some(ra)) = (
                            resolve_place(slots, fn_did, body, *lhs, d + 1, None),
                            resolve_place(slots, fn_did, body, *rhs, d, None),
                        ) {
                            solver.equate(to_slot_ref(la, fn_did), to_slot_ref(ra, fn_did));
                        }
                    }
                }
                Rvalue::Aggregate(kind, operands) => {
                    let AggregateKind::Adt(def_id, _variant, _args, _, _) = kind.as_ref() else {
                        continue;
                    };
                    let Some(struct_did) = def_id.as_local() else {
                        continue;
                    };

                    for (field_idx, operand) in operands.iter_enumerated() {
                        let operand_place = match operand {
                            Operand::Copy(place) | Operand::Move(place) => *place,
                            Operand::Constant(_) => continue,
                        };
                        let field = StructFieldSlot {
                            struct_did,
                            field_index: field_idx.index(),
                        };

                        for d in 0..MAX_SLOT_DEPTH {
                            // §9.10.2: an aggregate is a field INITIALIZER; its depth-0
                            // ownership is set crate-wide by `constrain_field_ownership`.
                            if d == 0 {
                                continue;
                            }
                            if let (Some(field_slot_id), Some(operand_slot)) = (
                                slots.field_slots.slot_for_field_depth(field, d),
                                resolve_place(slots, fn_did, body, operand_place, d, None),
                            ) {
                                solver.equate(
                                    SlotRef::Field(field_slot_id),
                                    to_slot_ref(operand_slot, fn_did),
                                );
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    // §NB1: per-site SAFE-MONO is emitted alongside coherence (every consumer
    // adds coherence per body, so this is the single chokepoint). Gated to the
    // `PerSite` mode; `Chain`/`Off` skip it (the structural `i1-adjacency` in
    // `solver::add_universe` is the `Chain` arm).
    if super::SafeMonoMode::current() == super::SafeMonoMode::PerSite {
        super::safety_mono::add_safety_mono(solver, slots, fn_did, body);
    }
}

pub fn add_coherence<'tcx>(
    solver: &KindSolver,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
) {
    add_coherence_impl(solver, slots, fn_did, body, false, None, false);
}

pub(crate) fn add_coherence_with_copy_lends<'tcx>(
    solver: &KindSolver,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    copy_lends: &FxHashSet<CopyLendPair>,
) {
    add_coherence_impl(solver, slots, fn_did, body, false, Some(copy_lends), false);
}

pub(crate) fn add_coherence_removal_only<'tcx>(
    solver: &KindSolver,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
) {
    add_coherence_impl(solver, slots, fn_did, body, false, None, true);
}

#[cfg(test)]
pub(crate) fn add_coherence_tagging_uses<'tcx>(
    solver: &KindSolver,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
) {
    add_coherence_impl(solver, slots, fn_did, body, true, None, false);
}

/// §9.10.2 crate-wide field-ownership constraint. A struct field slot is ONE crate-wide slot
/// that (flow-insensitively) holds EVERY value stored into that field across the crate. The
/// per-store depth-0 `equate` is SKIPPED in `add_coherence` for field stores/aggregates (it is
/// what transitively dragged a borrowed value to `Owning` when an owned source was stored into
/// the same global field elsewhere). Instead, this collects, per depth-0 field slot, the
/// depth-0 slots of ALL its stored values crate-wide and asserts `field.own <=> AND(rhs.own)`
/// (`KindSolver::constrain_field_own`): the field may be `Owning` only if every value ever
/// stored into it is owned. This uses BO's OWN ownership verdict for each stored value, so
/// interprocedural / wrapper-returned allocations, borrowed returns, and projected loads are
/// all handled with NO syntactic detection — a field mixing an owned source and a borrowed
/// value settles non-Owning; a field populated only by owned transfers stays `Owning`.
///
/// A field write whose value is definitely NOT an owned heap allocation — an address-of
/// (`Ref`/`RawPtr`) or any store whose RHS cannot be resolved to a slot — BLOCKS the field's
/// ownership (`forbid_field_own`) rather than being dropped from the `AND` (which would
/// wrongly permit `Owning`). Value-preserving `Cast` (`malloc() as *mut T`) is followed to its
/// operand so a typed field's allocation still counts as owned.
///
/// RESIDUAL (documented, accepted): constant stores are skipped as null (`(*p).f = null` is
/// free-safe). A NON-null pointer constant (`(*p).f = 0x1000 as *mut T`) is also skipped but
/// is NOT owned, so a field mixing such a constant with a malloc elsewhere could over-claim.
/// This is exceedingly rare in C2Rust output and BO is behind the codegen guardrail; closing
/// it needs null-vs-non-null constant classification. Call-return-into-field is NOT a gap —
/// MIR routes calls through a temp, caught as a normal `Use` store.
pub(crate) fn constrain_field_ownership(
    solver: &KindSolver,
    slots: &CrateSlots,
    program: &RustProgram<'_>,
) {
    let (owned_stores, blocked) = scan_field_stores(slots, program);
    for (field, rhs) in &owned_stores {
        if !blocked.contains(field) {
            solver.constrain_field_own(*field, rhs);
        }
    }
    for &field in &blocked {
        solver.forbid_field_own(field);
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct FieldRefPlan {
    pub(crate) rows: Vec<FieldRefPlanRow>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct FieldRefPlanRow {
    pub(crate) field: SlotRef,
    pub(crate) opaque: usize,
    pub(crate) unresolved_unresolvable: usize,
    pub(crate) nullable: usize,
    pub(crate) safe: usize,
}

pub(crate) fn constrain_field_ref_worthiness(
    solver: &KindSolver,
    slots: &CrateSlots,
    program: &RustProgram<'_>,
    origin_flows: Option<&super::origin_flow::OriginFlowResults>,
    nullability: &super::nullability::NullabilityFacts,
) -> FieldRefPlan {
    let opaque_sources = origin_flows
        .map(|flows| positive_opaque_return_slots(slots, program, flows))
        .unwrap_or_default();
    let (stores, blocked) = scan_field_stores(slots, program);
    let mut fields = stores.keys().copied().collect::<FxHashSet<_>>();
    fields.extend(blocked.iter().copied());
    fields.extend(
        nullability
            .slots()
            .into_iter()
            .filter(|slot| matches!(slot, SlotRef::Field(_))),
    );
    let mut rows = Vec::new();
    for field in fields {
        let all_rhs = stores.get(&field).cloned().unwrap_or_default();
        let nullable = all_rhs
            .iter()
            .filter(|source| nullability.contains(source))
            .count()
            + usize::from(nullability.contains(&field));
        let rhs = all_rhs
            .into_iter()
            .filter(|source| !nullability.contains(source))
            .collect::<Vec<_>>();
        let opaque = rhs
            .iter()
            .filter(|source| opaque_sources.contains(source))
            .count();
        let unresolved_unresolvable = usize::from(blocked.contains(&field));
        let safe = rhs.len() - opaque;
        if opaque > 0 || unresolved_unresolvable > 0 {
            solver.forbid_field_ref(field);
        } else {
            solver.constrain_field_ref(field, &rhs);
        }
        rows.push(FieldRefPlanRow {
            field,
            opaque,
            unresolved_unresolvable,
            nullable,
            safe,
        });
    }
    rows.sort_by_key(|row| super::l2::SlotKey::of(row.field));
    FieldRefPlan { rows }
}

fn owner_slot_ref(
    slots: &CrateSlots,
    fn_did: LocalDefId,
    owner: super::slots::SlotOwner,
) -> Option<SlotRef> {
    match owner {
        super::slots::SlotOwner::Local(local) => slots.fn_local_slots[&fn_did]
            .slot_for_local_depth(local, 0)
            .map(|slot| SlotRef::Local(fn_did, slot)),
        super::slots::SlotOwner::Field(field) => slots
            .field_slots
            .slot_for_field_depth(field, 0)
            .map(SlotRef::Field),
    }
}

pub(crate) fn positive_opaque_return_slots(
    slots: &CrateSlots,
    program: &RustProgram<'_>,
    origin_flows: &super::origin_flow::OriginFlowResults,
) -> FxHashSet<SlotRef> {
    let mut opaque = FxHashSet::default();
    for &fn_did in &program.functions {
        let body_ref = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        let body = &*body_ref;
        for data in body.basic_blocks.iter() {
            let Some(call) = data
                .terminator
                .as_ref()
                .and_then(|terminator| terminator.as_call(program.tcx))
            else {
                continue;
            };
            let positive_opaque = match call.func {
                CallKind::LibC(name) => {
                    boundary_table::lookup(name.as_str(), Matcher::ForeignC).is_none()
                }
                CallKind::Impl(_) | CallKind::Closure | CallKind::Dynamic => true,
                CallKind::FreeStanding(_) | CallKind::RustLib(_) => false,
            };
            if !positive_opaque {
                continue;
            }
            if let Some(resolved) = resolve_place(slots, fn_did, body, call.destination, 0, None) {
                opaque.insert(to_slot_ref(resolved, fn_did));
            }
        }

        let flows = origin_flows[&fn_did].body.depth0_value_flows();
        let mut changed = true;
        while changed {
            changed = false;
            for &(source, target) in &flows {
                let Some(source) = owner_slot_ref(slots, fn_did, source) else {
                    continue;
                };
                let Some(target) = owner_slot_ref(slots, fn_did, target) else {
                    continue;
                };
                if opaque.contains(&source) {
                    changed |= opaque.insert(target);
                }
            }
        }
    }
    opaque
}

/// §S2-3 — the field-store ownership scan, shared by `constrain_field_ownership` (which emits the
/// `field.own <=> AND(stored owns)` constraints from it) and the sweep's field-yield histogram (which
/// counts Owning candidates from it). Returns per-field owned-store RHS places and the set of fields
/// blocked by a non-owned store. Byte-identical to the scan `constrain_field_ownership` inlined before.
fn scan_field_stores(
    slots: &CrateSlots,
    program: &RustProgram<'_>,
) -> (FxHashMap<SlotRef, Vec<SlotRef>>, FxHashSet<SlotRef>) {
    let mut owned_stores: FxHashMap<SlotRef, Vec<SlotRef>> = FxHashMap::default();
    let mut blocked: FxHashSet<SlotRef> = FxHashSet::default();

    for &fn_did in &program.functions {
        let body_ref = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        let body = &*body_ref;

        for bbdata in body.basic_blocks.iter() {
            for stmt in &bbdata.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind else {
                    continue;
                };

                // Aggregate: each operand initializes a field slot.
                if let Rvalue::Aggregate(kind, operands) = rvalue
                    && let AggregateKind::Adt(def_id, _, _, _, _) = kind.as_ref()
                    && let Some(struct_did) = def_id.as_local()
                {
                    for (field_idx, operand) in operands.iter_enumerated() {
                        let Some(fid) = slots.field_slots.slot_for_field_depth(
                            StructFieldSlot {
                                struct_did,
                                field_index: field_idx.index(),
                            },
                            0,
                        ) else {
                            continue;
                        };
                        let f = SlotRef::Field(fid);
                        match operand {
                            Operand::Copy(p) | Operand::Move(p) => {
                                match resolve_place(slots, fn_did, body, *p, 0, None) {
                                    Some(r) => owned_stores
                                        .entry(f)
                                        .or_default()
                                        .push(to_slot_ref(r, fn_did)),
                                    None => {
                                        blocked.insert(f);
                                    }
                                }
                            }
                            Operand::Constant(_) => {} // null/const: free-safe, skip
                        }
                    }
                    continue;
                }

                // Non-aggregate: is `lhs` a struct-field store?
                let Some(ResolvedSlot::Field(fid)) =
                    resolve_place(slots, fn_did, body, *lhs, 0, None)
                else {
                    continue;
                };
                let f = SlotRef::Field(fid);
                // Value-preserving stores expose an owned-capable RHS place (follow `Cast` to
                // its operand so `malloc() as *mut T` still counts as owned). A constant
                // (`null`) is free-safe and skipped; any other rvalue (address-of / computed)
                // is not an owned heap value and BLOCKS ownership.
                let rhs_place = match rvalue {
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::CopyForDeref(p)
                    | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => Some(*p),
                    Rvalue::Use(Operand::Constant(_))
                    | Rvalue::Cast(_, Operand::Constant(_), _) => {
                        continue;
                    }
                    _ => None,
                };
                match rhs_place.and_then(|p| resolve_place(slots, fn_did, body, p, 0, None)) {
                    Some(r) => owned_stores
                        .entry(f)
                        .or_default()
                        .push(to_slot_ref(r, fn_did)),
                    None => {
                        blocked.insert(f);
                    }
                }
            }
        }
    }

    (owned_stores, blocked)
}

/// §S2-3 — Owning-candidate fields (≥1 owned store and no blocking non-owned store) and the blocked
/// set, for the field-yield histogram. Derived from the same `scan_field_stores` the solver
/// constraints use, so the candidate count matches what `constrain_field_own` was applied to.
pub(crate) fn field_ownership_candidates(
    slots: &CrateSlots,
    program: &RustProgram<'_>,
) -> (FxHashSet<SlotRef>, FxHashSet<SlotRef>) {
    let (owned_stores, blocked) = scan_field_stores(slots, program);
    let candidates = owned_stores
        .keys()
        .copied()
        .filter(|f| !blocked.contains(f))
        .collect();
    (candidates, blocked)
}
