//! Source lifecycle inventory. These identities never describe generated drops.

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};

use rustc_middle::{
    mir::{Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};

use super::export::PlaceKey;
use crate::{
    analyses::mir::{CallKind, TerminatorExt},
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SourcePhase {
    Statement,
    Call,
    Return,
    Unwind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SourceRole {
    Free,
    StorageDead,
    Drop,
    ReturnStorage,
    UnwindStorage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SourceCondition {
    Unconditional,
    StorageLive,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SourceGeneration {
    None,
    UnresolvedHeapEpoch,
    UnresolvedStorageEpoch,
    Missing,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SourceRegion {
    NoObject,
    WholeAllocation,
    WholeStorage,
    Missing,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct SourceEventKey {
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) phase: SourcePhase,
    pub(crate) role: SourceRole,
    pub(crate) storage_local: Option<u32>,
    pub(crate) condition: SourceCondition,
}

/// A static origin denotes possible dynamic generations, never one epoch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SourceObject {
    HeapThrough(PlaceKey),
    PointerStorage(PlaceKey),
    Storage(PlaceKey),
    Null,
    UnknownOperand,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Coverage {
    IrrelevantNull,
    IrrelevantPointerStorage,
    IrrelevantUnaddressedStorage,
    IrrelevantInactiveStorage,
    UnresolvedWholeObject,
    UnresolvedStorage,
    UnresolvedDropEffects,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceRetirement {
    pub(crate) key: SourceEventKey,
    pub(crate) object: SourceObject,
    pub(crate) coverage: Coverage,
    pub(crate) generation: SourceGeneration,
    pub(crate) region: SourceRegion,
}

/// A call routes an existing body event; it does not create another free.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceCallRoute {
    pub(crate) caller: String,
    pub(crate) block: u32,
    pub(crate) callee: String,
    pub(crate) events: Vec<SourceEventKey>,
    /// Vector position is the formal argument position; a constant or
    /// unrepresentable operand retains its position as explicit None.
    pub(crate) arguments: Vec<Option<PlaceKey>>,
    /// Free-event routing does not claim a callee-storage lifetime relation.
    pub(crate) storage_relation_missing: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SourceEvents {
    pub(crate) retirements: BTreeMap<SourceEventKey, SourceRetirement>,
    pub(crate) calls: Vec<SourceCallRoute>,
}

thread_local! {
    static CARRIED: RefCell<Option<Arc<SourceEvents>>> = const { RefCell::new(None) };
}

pub(crate) fn current() -> Option<Arc<SourceEvents>> {
    CARRIED.with(|inventory| inventory.borrow().clone())
}

pub(crate) fn for_construction(program: &RustProgram<'_>) -> Arc<SourceEvents> {
    current().unwrap_or_else(|| Arc::new(collect(program)))
}

pub(crate) fn with_inventory<T>(inventory: &Arc<SourceEvents>, f: impl FnOnce() -> T) -> T {
    struct Restore(Option<Arc<SourceEvents>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CARRIED.with(|inventory| *inventory.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(CARRIED.with(|carried| carried.replace(Some(inventory.clone()))));
    f()
}

pub(crate) fn record_replay() {
    if let Some(inventory) = current() {
        super::export::record(|export| export.replay_source_events = Some(inventory));
    }
}

impl SourceEvents {
    pub(crate) fn reconcile(
        &self,
        rows: &[(SourceEventKey, Coverage)],
    ) -> Result<(), ReconciliationError> {
        let mut seen = BTreeSet::new();
        for (key, coverage) in rows {
            let Some(event) = self.retirements.get(key) else {
                return Err(ReconciliationError::Unexpected(key.clone()));
            };
            if !seen.insert(key) {
                return Err(ReconciliationError::Duplicate(key.clone()));
            }
            if key != &event.key || *coverage != event.coverage {
                return Err(ReconciliationError::Mismatch(key.clone()));
            }
        }
        if let Some(missing) = self.retirements.keys().find(|key| !seen.contains(key)) {
            return Err(ReconciliationError::Missing(missing.clone()));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReconciliationError {
    Missing(SourceEventKey),
    Duplicate(SourceEventKey),
    Unexpected(SourceEventKey),
    Mismatch(SourceEventKey),
}

fn operand_is_null(operand: &Operand<'_>, state: &[bool], tcx: TyCtxt<'_>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            state[place.local.as_usize()]
        }
        Operand::Constant(value) => {
            let scalar = value.const_.try_to_scalar().or_else(|| {
                if let rustc_middle::mir::Const::Unevaluated(value, _) = &value.const_
                    && value.promoted.is_none()
                    && let Ok(rustc_middle::mir::ConstValue::Scalar(scalar)) =
                        tcx.const_eval_poly(value.def)
                {
                    return Some(scalar);
                }
                None
            });
            scalar
                .and_then(|scalar| scalar.try_to_scalar_int().ok())
                .is_some_and(|value| value.to_bits(value.size()) == 0)
        }
        _ => false,
    }
}

fn transfer_statement(
    statement: &StatementKind<'_>,
    state: &mut [bool],
    addressed: &BTreeSet<Local>,
    tcx: TyCtxt<'_>,
) {
    match statement {
        StatementKind::Assign(box (place, value)) if place.projection.is_empty() => {
            state[place.local.as_usize()] = match value {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                    operand_is_null(operand, state, tcx)
                }
                _ => false,
            };
        }
        StatementKind::Assign(..) => {
            // A projected store can overwrite an address-taken pointer local.
            for local in addressed {
                state[local.as_usize()] = false;
            }
        }
        StatementKind::StorageDead(local) => state[local.as_usize()] = false,
        _ => {}
    }
}

fn transfer_call<'tcx>(
    terminator: &rustc_middle::mir::Terminator<'tcx>,
    state: &mut [bool],
    addressed: &BTreeSet<Local>,
    tcx: TyCtxt<'tcx>,
) {
    // Drops and other terminators can run code that mutates exposed locals.
    for local in addressed {
        state[local.as_usize()] = false;
    }
    if matches!(terminator.kind, TerminatorKind::InlineAsm { .. }) {
        state.fill(false);
    }
    let Some(call) = terminator.as_call(tcx) else { return };
    if call.destination.projection.is_empty() {
        // Only the compiler-resolved non-local null constructor establishes None.
        state[call.destination.local.as_usize()] = matches!(call.func, CallKind::RustLib(did)
            if matches!(tcx.item_name(did).as_str(), "null" | "null_mut")
                && tcx.crate_name(did.krate).as_str() == "core"
                && tcx.def_path_str(did).contains("::ptr::"));
    }
}

fn null_entries<'tcx>(
    body: &Body<'tcx>,
    addressed: &BTreeSet<Local>,
    tcx: TyCtxt<'tcx>,
) -> Vec<Option<Vec<bool>>> {
    let mut entries = vec![None; body.basic_blocks.len()];
    entries[0] = Some(vec![false; body.local_decls.len()]);
    let mut queue = VecDeque::from([rustc_middle::mir::START_BLOCK]);
    while let Some(block) = queue.pop_front() {
        let data = &body.basic_blocks[block];
        let mut state = entries[block.as_usize()]
            .clone()
            .expect("reachable predecessor");
        for statement in &data.statements {
            transfer_statement(&statement.kind, &mut state, addressed, tcx);
        }
        transfer_call(data.terminator(), &mut state, addressed, tcx);
        for successor in data.terminator().successors() {
            let entry = &mut entries[successor.as_usize()];
            let changed = match entry {
                None => {
                    *entry = Some(state.clone());
                    true
                }
                Some(previous) => {
                    let mut changed = false;
                    for (old, new) in previous.iter_mut().zip(&state) {
                        if *old && !new {
                            *old = false;
                            changed = true;
                        }
                    }
                    changed
                }
            };
            if changed {
                queue.push_back(successor);
            }
        }
    }
    entries
}

fn insert(events: &mut SourceEvents, event: SourceRetirement) {
    assert!(
        events
            .retirements
            .insert(event.key.clone(), event)
            .is_none(),
        "duplicate source retirement identity"
    );
}

fn storage_entries(body: &Body<'_>) -> Vec<Option<Vec<bool>>> {
    let mut implicit = vec![true; body.local_decls.len()];
    for statement in body.basic_blocks.iter().flat_map(|block| &block.statements) {
        if let StatementKind::StorageLive(local) = statement.kind {
            implicit[local.as_usize()] = false;
        }
    }
    let mut entries = vec![None; body.basic_blocks.len()];
    entries[0] = Some(implicit);
    let mut queue = VecDeque::from([rustc_middle::mir::START_BLOCK]);
    while let Some(block) = queue.pop_front() {
        let mut live = entries[block.as_usize()]
            .clone()
            .expect("reachable storage state");
        for statement in &body.basic_blocks[block].statements {
            transfer_storage(&statement.kind, &mut live);
        }
        for successor in body.basic_blocks[block].terminator().successors() {
            let entry = &mut entries[successor.as_usize()];
            let changed = match entry {
                None => {
                    *entry = Some(live.clone());
                    true
                }
                Some(previous) => {
                    let mut changed = false;
                    for (old, new) in previous.iter_mut().zip(&live) {
                        if !*old && *new {
                            *old = true;
                            changed = true;
                        }
                    }
                    changed
                }
            };
            if changed {
                queue.push_back(successor);
            }
        }
    }
    entries
}

fn transfer_storage(statement: &StatementKind<'_>, live: &mut [bool]) {
    match statement {
        StatementKind::StorageLive(local) => live[local.as_usize()] = true,
        StatementKind::StorageDead(local) => live[local.as_usize()] = false,
        _ => {}
    }
}

fn storage_event(
    key: SourceEventKey,
    place: Place<'_>,
    body: &Body<'_>,
    addressed: &BTreeSet<Local>,
) -> SourceRetirement {
    let pointer_storage =
        place.projection.is_empty() && body.local_decls[place.local].ty.is_any_ptr();
    SourceRetirement {
        key,
        object: if pointer_storage {
            SourceObject::PointerStorage(PlaceKey::from_place(place))
        } else {
            SourceObject::Storage(PlaceKey::from_place(place))
        },
        coverage: if !addressed.contains(&place.local) {
            if pointer_storage {
                Coverage::IrrelevantPointerStorage
            } else {
                Coverage::IrrelevantUnaddressedStorage
            }
        } else {
            Coverage::UnresolvedStorage
        },
        generation: SourceGeneration::UnresolvedStorageEpoch,
        region: SourceRegion::WholeStorage,
    }
}

pub(crate) fn collect(program: &RustProgram<'_>) -> SourceEvents {
    let tcx = program.tcx;
    let mut events = SourceEvents::default();
    for &function in &program.functions {
        let function_path = tcx.def_path_str(function.to_def_id());
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let addressed: BTreeSet<_> = body
            .basic_blocks
            .iter()
            .flat_map(|block| &block.statements)
            .filter_map(|statement| {
                let StatementKind::Assign(box (
                    _,
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place),
                )) = &statement.kind
                else {
                    return None;
                };
                (!place
                    .projection
                    .iter()
                    .any(|projection| matches!(projection, ProjectionElem::Deref)))
                .then_some(place.local)
            })
            .collect();
        let entries = null_entries(&body, &addressed, tcx);
        let storage = storage_entries(&body);
        for (block, data) in body.basic_blocks.iter_enumerated() {
            // Keep even unreachable source events inventoried. No reachability
            // claim or dynamic epoch is inferred from their static site key.
            let mut state = entries[block.as_usize()]
                .clone()
                .unwrap_or_else(|| vec![false; body.local_decls.len()]);
            let mut live = storage[block.as_usize()]
                .clone()
                .unwrap_or_else(|| vec![false; body.local_decls.len()]);
            let key = |statement, phase, role, storage_local| SourceEventKey {
                function: function_path.clone(),
                block: block.as_u32(),
                statement,
                phase,
                role,
                storage_local,
                condition: SourceCondition::Unconditional,
            };
            for (index, statement) in data.statements.iter().enumerate() {
                if let StatementKind::StorageDead(local) = statement.kind {
                    let mut event = storage_event(
                        key(
                            index,
                            SourcePhase::Statement,
                            SourceRole::StorageDead,
                            Some(local.as_u32()),
                        ),
                        Place::from(local),
                        &body,
                        &addressed,
                    );
                    if !live[local.as_usize()] {
                        event.coverage = Coverage::IrrelevantInactiveStorage;
                    }
                    insert(&mut events, event);
                }
                transfer_statement(&statement.kind, &mut state, &addressed, tcx);
                transfer_storage(&statement.kind, &mut live);
            }
            let index = data.statements.len();
            let terminator = data.terminator();
            if let Some(call) = terminator.as_call(tcx) {
                match call.func {
                    CallKind::LibC(name) if name.as_str() == "free" => {
                        let object = match call.args.first().map(|argument| &argument.node) {
                            Some(operand) if operand_is_null(operand, &state, tcx) => {
                                SourceObject::Null
                            }
                            Some(Operand::Copy(place) | Operand::Move(place)) => {
                                SourceObject::HeapThrough(PlaceKey::from_place(*place))
                            }
                            _ => SourceObject::UnknownOperand,
                        };
                        let coverage = if object == SourceObject::Null {
                            Coverage::IrrelevantNull
                        } else {
                            Coverage::UnresolvedWholeObject
                        };
                        let (generation, region) = if object == SourceObject::Null {
                            (SourceGeneration::None, SourceRegion::NoObject)
                        } else {
                            (
                                SourceGeneration::UnresolvedHeapEpoch,
                                SourceRegion::WholeAllocation,
                            )
                        };
                        insert(
                            &mut events,
                            SourceRetirement {
                                key: key(index, SourcePhase::Call, SourceRole::Free, None),
                                object,
                                coverage,
                                generation,
                                region,
                            },
                        );
                    }
                    CallKind::FreeStanding(callee) | CallKind::Impl(callee) => {
                        let arguments = call
                            .args
                            .iter()
                            .map(|argument| match argument.node {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    Some(PlaceKey::from_place(place))
                                }
                                _ => None,
                            })
                            .collect();
                        events.calls.push(SourceCallRoute {
                            caller: function_path.clone(),
                            block: block.as_u32(),
                            callee: tcx.def_path_str(callee.to_def_id()),
                            events: Vec::new(),
                            arguments,
                            storage_relation_missing: true,
                        });
                    }
                    _ => {}
                }
            }
            match terminator.kind {
                TerminatorKind::Drop { place, .. } => {
                    let mut event = storage_event(
                        key(index, SourcePhase::Call, SourceRole::Drop, None),
                        place,
                        &body,
                        &addressed,
                    );
                    // A destructor can retire a pointee or execute a local body;
                    // dropping its value is not proof of stack-storage death.
                    event.coverage = Coverage::UnresolvedDropEffects;
                    event.region = SourceRegion::Missing;
                    event.generation = SourceGeneration::Missing;
                    insert(&mut events, event);
                }
                TerminatorKind::Return | TerminatorKind::UnwindResume => {
                    let (phase, role) = if matches!(terminator.kind, TerminatorKind::Return) {
                        (SourcePhase::Return, SourceRole::ReturnStorage)
                    } else {
                        (SourcePhase::Unwind, SourceRole::UnwindStorage)
                    };
                    for local in body.local_decls.indices().filter(|local| {
                        *local != rustc_middle::mir::RETURN_PLACE && live[local.as_usize()]
                    }) {
                        let mut event_key = key(index, phase, role, Some(local.as_u32()));
                        // Joins retain may-live storage. This condition prevents
                        // a static site from claiming one unconditional epoch.
                        event_key.condition = SourceCondition::StorageLive;
                        insert(
                            &mut events,
                            storage_event(event_key, Place::from(local), &body, &addressed),
                        );
                    }
                }
                _ => {}
            }
            // Continue has no cleanup successor in this body. It is still an
            // exit of this source frame if the unwind edge is taken. Terminate
            // is deliberately excluded: abort supplies no program memory event.
            if matches!(
                terminator.kind,
                TerminatorKind::Call {
                    unwind: rustc_middle::mir::UnwindAction::Continue,
                    ..
                } | TerminatorKind::Drop {
                    unwind: rustc_middle::mir::UnwindAction::Continue,
                    ..
                } | TerminatorKind::Assert {
                    unwind: rustc_middle::mir::UnwindAction::Continue,
                    ..
                } | TerminatorKind::InlineAsm {
                    unwind: rustc_middle::mir::UnwindAction::Continue,
                    ..
                }
            ) {
                for local in body.local_decls.indices().filter(|local| {
                    *local != rustc_middle::mir::RETURN_PLACE && live[local.as_usize()]
                }) {
                    let mut event_key = key(
                        index,
                        SourcePhase::Unwind,
                        SourceRole::UnwindStorage,
                        Some(local.as_u32()),
                    );
                    event_key.condition = SourceCondition::StorageLive;
                    insert(
                        &mut events,
                        storage_event(event_key, Place::from(local), &body, &addressed),
                    );
                }
            }
        }
    }
    // Resolve call routes over the finite static graph, deduplicating by the
    // original body event. Recursion does not manufacture new generations.
    let mut reachable = BTreeMap::<String, BTreeSet<SourceEventKey>>::new();
    for event in events
        .retirements
        .keys()
        .filter(|key| key.role == SourceRole::Free)
    {
        reachable
            .entry(event.function.clone())
            .or_default()
            .insert(event.clone());
    }
    loop {
        let mut changed = false;
        for route in &events.calls {
            let callee = reachable.get(&route.callee).cloned().unwrap_or_default();
            let caller = reachable.entry(route.caller.clone()).or_default();
            let before = caller.len();
            caller.extend(callee);
            changed |= caller.len() != before;
        }
        if !changed {
            break;
        }
    }
    for route in &mut events.calls {
        route.events = reachable
            .get(&route.callee)
            .into_iter()
            .flatten()
            .cloned()
            .collect();
    }
    events
        .calls
        .sort_by(|a, b| (&a.caller, a.block, &a.callee).cmp(&(&b.caller, b.block, &b.callee)));
    events
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::*;

    fn inventory(code: &str) -> SourceEvents {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let mut functions = Vec::new();
            let mut structs = Vec::new();
            for owner in tcx.hir_crate(()).owners.iter() {
                let Some(owner) = owner.as_owner() else { continue };
                let OwnerNode::Item(item) = owner.node() else { continue };
                match item.kind {
                    ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                    ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                    _ => {}
                }
            }
            collect(&RustProgram {
                tcx,
                functions,
                structs,
            })
        })
        .unwrap_or_else(|error| error.raise())
    }

    fn frees(events: &SourceEvents) -> Vec<&SourceRetirement> {
        events
            .retirements
            .values()
            .filter(|event| event.key.role == SourceRole::Free)
            .collect()
    }

    #[test]
    fn e5_p_sink_direct_free_has_source_identity() {
        let events = inventory(
            "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn f(p: *mut u8) { free(p); }",
        );
        let frees = frees(&events);
        assert_eq!(frees.len(), 1, "E5-P-SINK direct source event missing");
        assert_eq!(frees[0].key.function, "f");
        assert_eq!(frees[0].key.phase, SourcePhase::Call);
        assert!(matches!(frees[0].object, SourceObject::HeapThrough(_)));
        assert_eq!(frees[0].coverage, Coverage::UnresolvedWholeObject);
    }

    #[test]
    fn e5_p_sink_wrapper_routes_one_body_event() {
        let events = inventory(
            "unsafe extern \"C\" { fn free(p: *mut u8); } unsafe fn dispose(p: *mut u8) { free(p); } pub unsafe fn f(p: *mut u8) { dispose(p); }",
        );
        let frees = frees(&events);
        assert_eq!(frees.len(), 1, "summary and body must share one event");
        assert_eq!(frees[0].key.function, "dispose");
        let route = events
            .calls
            .iter()
            .find(|route| route.caller == "f" && route.callee == "dispose")
            .expect("body retirement route");
        assert_eq!(route.events, vec![frees[0].key.clone()]);
    }

    #[test]
    fn e5_p_sink_nonretiring_local_free_name_is_not_a_sink() {
        let events = inventory(
            "unsafe fn free(p: *mut u8) { let _ = p; } pub unsafe fn f(p: *mut u8) { free(p); }",
        );
        assert!(frees(&events).is_empty());
    }

    #[test]
    fn e5_p_sink_null_free_is_explicitly_irrelevant() {
        let events = inventory(
            "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn f() { free(0 as *mut u8); }",
        );
        let frees = frees(&events);
        assert_eq!(frees.len(), 1, "null operation is inventoried, not erased");
        assert_eq!(frees[0].object, SourceObject::Null);
        assert_eq!(frees[0].coverage, Coverage::IrrelevantNull);
    }

    #[test]
    fn e5_p_sink_pointer_storage_death_is_not_heap_death() {
        let events = inventory("pub unsafe fn f(p: *mut u8) { let q = p; let _ = q; }");
        assert!(frees(&events).is_empty());
        let storage: Vec<_> = events
            .retirements
            .values()
            .filter(|event| matches!(event.object, SourceObject::PointerStorage(_)))
            .collect();
        assert!(
            !storage.is_empty(),
            "source pointer storage requires an explicit disposition"
        );
        assert!(
            storage
                .iter()
                .all(|event| event.coverage == Coverage::IrrelevantPointerStorage)
        );
    }

    #[test]
    fn e5_p_sink_coverage_rejects_missing_duplicate_and_foreign_events() {
        let events = inventory(
            "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn f(p: *mut u8) { free(p); }",
        );
        let rows: Vec<_> = events
            .retirements
            .values()
            .map(|event| (event.key.clone(), event.coverage))
            .collect();
        assert!(events.reconcile(&rows).is_ok());
        assert!(
            events.reconcile(&rows[1..]).is_err(),
            "missing source event must fail reconciliation"
        );
        let mut duplicated = rows.clone();
        duplicated.push(rows[0].clone());
        assert!(
            events.reconcile(&duplicated).is_err(),
            "duplicate source event must fail reconciliation"
        );
        let mut foreign = rows.clone();
        foreign[0].0.function = "different_function".to_owned();
        assert!(
            events.reconcile(&foreign).is_err(),
            "foreign event must not balance a missing event"
        );
    }

    #[test]
    fn e5_p_sink_whole_object_and_unknown_epoch_are_typed() {
        let events = inventory(
            "unsafe extern \"C\" { fn free(p: *mut u8); } pub unsafe fn f(p: *mut u8) { free(p); }",
        );
        let free = frees(&events)[0];
        assert_eq!(free.generation, SourceGeneration::UnresolvedHeapEpoch);
        assert_eq!(free.region, SourceRegion::WholeAllocation);
        assert_eq!(free.key.condition, SourceCondition::Unconditional);
    }

    #[test]
    fn e5_p_sink_wrapper_keeps_ordered_actual_operands() {
        let events = inventory(
            "unsafe extern \"C\" { fn free(p: *mut u8); } unsafe fn dispose_second(a: *mut u8, b: *mut u8) { let _ = a; free(b); } pub unsafe fn f(a: *mut u8, b: *mut u8) { dispose_second(b, a); }",
        );
        let route = events
            .calls
            .iter()
            .find(|route| route.caller == "f")
            .expect("local call");
        assert_eq!(
            route.arguments.len(),
            2,
            "formal positions must not be lost"
        );
        assert_ne!(route.arguments[0], route.arguments[1]);
        assert!(
            route.storage_relation_missing,
            "heap route is not storage-lifetime evidence"
        );
    }

    #[test]
    fn e5_p_sink_scalar_storage_is_irrelevant_unless_addressed() {
        let events = inventory("pub fn f(x: i32) -> i32 { x + 1 }");
        let storage: Vec<_> = events
            .retirements
            .values()
            .filter(|event| matches!(event.object, SourceObject::Storage(_)))
            .collect();
        assert!(!storage.is_empty());
        assert!(
            storage
                .iter()
                .all(|event| event.coverage == Coverage::IrrelevantUnaddressedStorage)
        );
        let addressed = inventory("pub fn f() -> i32 { let x = 1; let p = &x; *p }");
        assert!(
            addressed
                .retirements
                .values()
                .any(|event| event.coverage == Coverage::UnresolvedStorage)
        );
    }

    #[test]
    fn e5_p_sink_exit_storage_is_guarded_by_live_epoch() {
        let events = inventory(
            "pub fn f(c: bool) { if c { let x = 1; let p = &x; core::hint::black_box(p); } }",
        );
        let exits: Vec<_> = events
            .retirements
            .values()
            .filter(|event| event.key.role == SourceRole::ReturnStorage)
            .collect();
        assert!(!exits.is_empty());
        assert!(
            exits
                .iter()
                .all(|event| event.key.condition == SourceCondition::StorageLive)
        );
        assert!(
            exits
                .iter()
                .all(|event| event.generation == SourceGeneration::UnresolvedStorageEpoch)
        );
        let ended: BTreeSet<_> = events
            .retirements
            .keys()
            .filter(|key| key.role == SourceRole::StorageDead)
            .filter_map(|key| key.storage_local)
            .collect();
        assert!(
            !ended.is_empty(),
            "fixture must contain explicit storage death"
        );
        assert!(
            exits
                .iter()
                .all(|event| !ended.contains(&event.key.storage_local.unwrap())),
            "nested-scope storage must not retire again at return"
        );
    }

    #[test]
    fn e5_p_sink_unwind_edge_without_cleanup_retires_live_storage() {
        let events = inventory(
            "pub fn f() { let x = 1; let p = &x; core::hint::black_box(p); panic!(\"source fixture\"); }",
        );
        let unwind: Vec<_> = events
            .retirements
            .values()
            .filter(|event| event.key.role == SourceRole::UnwindStorage)
            .collect();
        assert!(
            !unwind.is_empty(),
            "unwind-to-caller is a source phase even without a cleanup block"
        );
        assert!(
            unwind
                .iter()
                .all(|event| event.key.phase == SourcePhase::Unwind)
        );
        assert!(
            unwind
                .iter()
                .all(|event| event.key.condition == SourceCondition::StorageLive)
        );
    }

    #[test]
    fn e5_p_sink_null_merge_and_alias_overwrite_controls() {
        let prefix = "unsafe extern \"C\" { fn free(p: *mut u8); } ";
        let copied = inventory(&format!(
            "{prefix} pub unsafe fn f() {{ let p = 0 as *mut i32; let q = p as *mut u8; free(q); }}"
        ));
        assert_eq!(frees(&copied)[0].object, SourceObject::Null);
        let merged = inventory(&format!(
            "{prefix} pub unsafe fn f(c: bool, other: *mut u8) {{ let p = if c {{ 0 as *mut u8 }} else {{ other }}; free(p); }}"
        ));
        assert_ne!(frees(&merged)[0].object, SourceObject::Null);
        let aliased = inventory(&format!(
            "{prefix} pub unsafe fn f(other: *mut u8) {{ let mut p = 0 as *mut u8; let q = &raw mut p; *q = other; free(p); }}"
        ));
        assert_ne!(frees(&aliased)[0].object, SourceObject::Null);
    }
}
