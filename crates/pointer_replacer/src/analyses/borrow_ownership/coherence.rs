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
    // R351-3: in pass 1 both maps stay empty, so the dispatch below falls
    // through to the pin's unconditional `equate`. The pin asserted one kind
    // equality here; era-5b's guarded form is the seat's prime suspect for the
    // 52 `ref -> raw`, and pass 1 is what tests that.
    // R371-2: under the repair arm both maps stay empty in the joint pass too,
    // so the dispatch falls through to the pin's unconditional `equate` — the
    // general equate is restored, never deleted.
    let joint = super::licensing::facts::Pass::current() == super::licensing::facts::Pass::Joint
        && !super::licensing::facts::repair()
        // R467-2 diagnosis: `readers` omits era-5b's field-reader / reference-reader
        // guard maps so their cost can be measured. Verdicts are NOT valid with it on.
        && !std::env::var("CRAT_ERA5C_SKIP_FAMILY").unwrap_or_default().split(',').any(|s| s.trim() == "readers");
    // L01^5 (ii): the strong-update field moves of this body (empty unless the
    // pin is on), consulted just before the pin's unconditional `equate`.
    let field_moves = super::field_moves::compute(body);
    let field_readers = solver
        .ownership_facts()
        .filter(|_| joint)
        .map(|facts| super::licensing::readers::guards_for_body(&facts, solver, fn_did, body))
        .unwrap_or_default();
    let mut reference_readers = FxHashMap::default();
    if joint
        && let Some(facts) = solver.ownership_facts()
        && let Some(frozen) = &facts.licensing
    {
        for candidate in &frozen.reference_effects.candidates {
            let Some(view) = facts.consumes.iter().find(|row| {
                row.point.construction == candidate.construction
                    && row.ordinal == candidate.scalar_view_consume
            }) else {
                continue;
            };
            let view_key = format!("{}::_{}@d0", candidate.function, view.local);
            let (Some(&lhs @ SlotRef::Local(owner, _)), Some(&rhs @ SlotRef::Field(_))) = (
                facts.slot_refs.get(&view_key),
                facts.slot_refs.get(&candidate.field_key),
            ) else {
                continue;
            };
            if owner != fn_did {
                continue;
            }
            let rows: Vec<_> = facts
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
            let [row] = rows.as_slice() else { continue };
            let key = super::licensing::facts::EquationId {
                construction: candidate.construction,
                ordinal: row.ordinal,
            };
            let Some(guard) = facts.guards.iter().find(|binding| binding.equation == key) else {
                continue;
            };
            reference_readers.insert(
                Location {
                    block: rustc_middle::mir::BasicBlock::from_u32(
                        candidate.scalar_read.block.unwrap(),
                    ),
                    statement_index: candidate.scalar_read.statement.unwrap(),
                },
                (lhs, rhs, guard.predicate.clone()),
            );
        }
    }
    for (block, bbdata) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in bbdata.statements.iter().enumerate() {
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
                                if matches!(la, ResolvedSlot::Field(id) if d == 0 || slots.field_slots.is_array_slot(id))
                                {
                                    continue;
                                }
                                let lhs = to_slot_ref(la, fn_did);
                                let rhs = to_slot_ref(ra, fn_did);
                                if d == 0
                                    && let Some((expected_lhs, expected_rhs, effect)) =
                                        reference_readers.get(&Location {
                                            block,
                                            statement_index,
                                        })
                                    && lhs == *expected_lhs
                                    && rhs == *expected_rhs
                                    && matches!(rvalue, Rvalue::CopyForDeref(_))
                                {
                                    solver.reference_field_reader_or_equate(lhs, rhs, effect);
                                } else if d == 0
                                    && let Some(reader) = field_readers.get(&Location {
                                        block,
                                        statement_index,
                                    })
                                {
                                    solver.field_reader_or_equate(lhs, rhs, reader);
                                } else if d == 0
                                    && copy_lends.is_some_and(|pairs| {
                                        pairs.contains(&CopyLendPair::new(lhs, rhs))
                                    })
                                {
                                    solver.lend_or_equate(lhs, rhs);
                                } else if d == 0
                                    && field_moves.is_move(Location {
                                        block,
                                        statement_index,
                                    })
                                {
                                    // L01^5 (ii): the load moves the field's token.
                                    solver.field_move_or_equate(lhs, rhs);
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
                            if matches!(la, ResolvedSlot::Field(id) if slots.field_slots.is_array_slot(id))
                            {
                                continue;
                            }
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
                        if slots.field_slots.is_array_field(field) {
                            continue;
                        }

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
/// Null constants are empty alternatives. Non-null or unevaluated constants
/// block ownership: a field mixing them with an allocation is not all-owned.
/// Call-return-into-field routes through a MIR temporary and is handled as a
/// normal `Use` store.
pub(crate) fn constrain_field_ownership(
    solver: &KindSolver,
    slots: &CrateSlots,
    program: &RustProgram<'_>,
) {
    let null_stores = solver
        .ownership_facts()
        .map(|facts| certified_null_stores(&facts))
        .unwrap_or_default();
    let (owned_stores, blocked) = scan_field_stores(slots, program, &null_stores);
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
    let (stores, blocked) = scan_field_stores(slots, program, &[]);
    let mut fields = stores.keys().copied().collect::<FxHashSet<_>>();
    fields.extend(blocked.iter().copied());
    fields.extend(
        nullability
            .slots()
            .into_iter()
            .filter(|slot| matches!(slot, SlotRef::Field(_))),
    );
    fields.retain(
        |field| !matches!(field, SlotRef::Field(id) if slots.field_slots.is_array_slot(*id)),
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
            if opaque > 0 {
                super::comparison::record_guard(
                    program.tcx,
                    slots,
                    field,
                    super::comparison::GuardRule::FieldOpaque,
                );
            }
            if unresolved_unresolvable > 0 {
                super::comparison::record_guard(
                    program.tcx,
                    slots,
                    field,
                    super::comparison::GuardRule::FieldUnresolved,
                );
            }
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

/// Authenticate transported None at each exact store, without confusing a
/// nullable or mixed kind slot with a definitely empty stored occurrence.
fn certified_null_stores(
    facts: &super::licensing::facts::Facts,
) -> Vec<(
    super::licensing::field_support::Site,
    super::ownership_access::PlaceSyntax,
)> {
    use super::{
        licensing::{
            field_support::StoredValue,
            transport::Node,
            value_origins::{OriginAtom, ValueOrigins},
        },
        ownership_occurrence::Availability::Present,
    };
    let Some(frozen) = &facts.licensing else {
        return Vec::new();
    };
    let observations: Vec<_> = frozen
        .field_support
        .iter()
        .flat_map(|field| field.null_stores.iter())
        .collect();
    if observations.is_empty() {
        return Vec::new();
    }
    // Reconstruct current alternatives; an old cached proof cannot erase a
    // new non-null store demand after its actual evidence changes.
    let origins = ValueOrigins::build(facts);
    let mut result = Vec::new();
    for store in &facts.field_support_inputs.stores {
        let StoredValue::Value(source) = &store.value else {
            continue;
        };
        if !observations.contains(&&store.site) {
            continue;
        }
        let rows: Vec<_> = facts
            .consumes
            .iter()
            .filter(|row| row.point.function.as_ref() == Some(&store.site.function))
            .cloned()
            .collect();
        let equations: Vec<_> = facts.equations.iter().filter(|equation| equation.point.function.as_ref() == Some(&store.site.function)
            && equation.point.block == Some(store.site.block) && equation.point.statement == Some(store.site.statement)
            && matches!(equation.operation.as_str(), "equal" | "linear") && equation.validate().is_ok()
            && equation.transfer.as_ref().is_some_and(|transfer| matches!((&transfer.destination, &transfer.source), (Present(destination), Present(rhs))
                if destination.local == store.site.place.local && destination.projection == store.site.place.projection
                    && rhs.local == source.local && rhs.projection == source.projection))).collect();
        let [equation] = equations.as_slice() else {
            continue;
        };
        if super::ownership_occurrence::validate(
            &store.site.function,
            &rows,
            &[(*equation).clone()],
        )
        .is_err()
        {
            continue;
        }
        let transfer = equation.transfer.as_ref().unwrap();
        if origins.at(Node {
            construction: equation.point.construction,
            var: transfer.source_use,
        }) != std::collections::BTreeSet::from([OriginAtom::Null])
        {
            continue;
        }
        result.push((store.site.clone(), source.clone()));
    }
    result
}

/// §S2-3 — the field-store ownership scan, shared by `constrain_field_ownership` (which emits the
/// `field.own <=> AND(stored owns)` constraints from it) and the sweep's field-yield histogram (which
/// counts Owning candidates from it). Returns per-field owned-store RHS places and the set of fields
/// blocked by a non-owned store. Production may discharge exact SSA-proved
/// None stores; callers without those facts retain the source-only scan.
fn scan_field_stores(
    slots: &CrateSlots,
    program: &RustProgram<'_>,
    null_stores: &[(
        super::licensing::field_support::Site,
        super::ownership_access::PlaceSyntax,
    )],
) -> (FxHashMap<SlotRef, Vec<SlotRef>>, FxHashSet<SlotRef>) {
    let mut owned_stores: FxHashMap<SlotRef, Vec<SlotRef>> = FxHashMap::default();
    let mut blocked: FxHashSet<SlotRef> = FxHashSet::default();

    for &fn_did in &program.functions {
        let body_ref = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        let body = &*body_ref;

        let function = program.tcx.def_path_str(fn_did);
        for (block, bbdata) in body.basic_blocks.iter_enumerated() {
            for (statement, stmt) in bbdata.statements.iter().enumerate() {
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
                                let mut destination =
                                    super::ownership_access::PlaceSyntax::from(*lhs);
                                destination
                                    .projection
                                    .push(super::export::ProjKey::Field(field_idx.as_u32()));
                                let key = super::slot_key::field_key(
                                    program.tcx,
                                    struct_did,
                                    field_idx.index(),
                                    0,
                                );
                                if null_stores.iter().any(|(site, rhs)| {
                                    site.function == function
                                        && site.block == block.as_u32()
                                        && site.statement == statement
                                        && site.field_key == key
                                        && site.place == destination
                                        && *rhs == super::ownership_access::PlaceSyntax::from(*p)
                                }) {
                                    continue;
                                }
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
                            Operand::Constant(_) => {
                                if !super::source_events::operand_is_null(operand, &[], program.tcx)
                                {
                                    blocked.insert(f);
                                }
                            }
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
                    Rvalue::Use(operand @ Operand::Constant(_))
                    | Rvalue::Cast(_, operand @ Operand::Constant(_), _) => {
                        if !super::source_events::operand_is_null(operand, &[], program.tcx) {
                            blocked.insert(f);
                        }
                        continue;
                    }
                    _ => None,
                };
                if let Some(rhs) = rhs_place
                    && let super::slots::SlotOwner::Field(field) = slots.field_slots.slot(fid).owner
                {
                    let key = super::slot_key::field_key(
                        program.tcx,
                        field.struct_did,
                        field.field_index,
                        0,
                    );
                    if null_stores.iter().any(|(site, source)| {
                        site.function == function
                            && site.block == block.as_u32()
                            && site.statement == statement
                            && site.field_key == key
                            && site.place == super::ownership_access::PlaceSyntax::from(*lhs)
                            && *source == super::ownership_access::PlaceSyntax::from(rhs)
                    }) {
                        continue;
                    }
                }
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

    // An unlicensed array summary must not add scalar reverse-AND demands
    // to the values stored into it. Its own holds are emitted separately.
    owned_stores.retain(
        |field, _| !matches!(field, SlotRef::Field(id) if slots.field_slots.is_array_slot(*id)),
    );
    blocked.retain(
        |field| !matches!(field, SlotRef::Field(id) if slots.field_slots.is_array_slot(*id)),
    );
    (owned_stores, blocked)
}

/// §S2-3 — Owning-candidate fields (≥1 owned store and no blocking non-owned store) and the blocked
/// set, for the source-only field-yield histogram. This caller has no normative
/// SSA null evidence, so its syntactic candidates are an upper bound, not the
/// refined production field-and constraint set or a measured Owning verdict.
pub(crate) fn field_ownership_candidates(
    slots: &CrateSlots,
    program: &RustProgram<'_>,
) -> (FxHashSet<SlotRef>, FxHashSet<SlotRef>) {
    let (owned_stores, blocked) = scan_field_stores(slots, program, &[]);
    let candidates = owned_stores
        .keys()
        .copied()
        .filter(|f| !blocked.contains(f))
        .collect();
    (candidates, blocked)
}
