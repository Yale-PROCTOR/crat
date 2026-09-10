//! Finite source-object flow. Roots name possible objects, not dynamic epochs.

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::{
    Body, CastKind, Local, Location, Operand, Place, Rvalue, START_BLOCK, StatementKind,
    TerminatorKind,
};
use rustc_span::def_id::LocalDefId;

use crate::{
    analyses::{
        borrow_ownership::{
            crate_slots::{CrateSlots, MAX_SLOT_DEPTH},
            export::{PlaceKey, ProjKey},
            realloc::ReallocResult,
            source_events::{self, SourceEvents},
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ObjectRoot {
    Input {
        function: LocalDefId,
        parameter: Local,
        depth: u8,
    },
    /// Born in this invocation; caller composition must rebase this root.
    Fresh {
        frame: LocalDefId,
        site: Location,
    },
    Stack {
        function: LocalDefId,
        local: Local,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ObjectSet {
    pub(crate) roots: FxHashSet<ObjectRoot>,
    pub(crate) unknown: bool,
}

impl Default for ObjectSet {
    fn default() -> Self {
        Self {
            roots: FxHashSet::default(),
            unknown: true,
        }
    }
}

impl ObjectSet {
    fn null() -> Self {
        Self {
            roots: FxHashSet::default(),
            unknown: false,
        }
    }

    fn root(root: ObjectRoot) -> Self {
        Self {
            roots: FxHashSet::from_iter([root]),
            unknown: false,
        }
    }

    fn union(&mut self, other: &Self) -> bool {
        let before = self.roots.len();
        let changed = other.unknown && !self.unknown;
        self.unknown |= other.unknown;
        self.roots.extend(other.roots.iter().copied());
        changed || before != self.roots.len()
    }
}

type State = Vec<Vec<ObjectSet>>;
type Snapshot = FxHashMap<(Local, u8), ObjectSet>;

#[derive(Default)]
pub(crate) struct ObjectFacts {
    snapshots: FxHashMap<(LocalDefId, Location), Snapshot>,
}

fn snapshot(state: &State) -> Snapshot {
    state
        .iter()
        .enumerate()
        .flat_map(|(local, row)| {
            row.iter().enumerate().filter_map(move |(depth, objects)| {
                // Null and partial roots with Unknown are meaningful. Only the
                // exact default Unknown cell can be reconstructed by absence.
                (!objects.unknown || !objects.roots.is_empty())
                    .then(|| ((Local::from_usize(local), depth as u8), objects.clone()))
            })
        })
        .collect()
}

fn pointer(state: &State, place: &PlaceKey, extra_depth: u8) -> ObjectSet {
    if !place
        .proj
        .iter()
        .all(|projection| matches!(projection, ProjKey::Deref))
    {
        return ObjectSet::default();
    }
    state
        .get(place.local.as_usize())
        .and_then(|row| row.get(place.proj.len() + usize::from(extra_depth)))
        .cloned()
        .unwrap_or_default()
}

fn storage(function: LocalDefId, state: &State, place: &PlaceKey) -> ObjectSet {
    let Some(last_deref) = place
        .proj
        .iter()
        .rposition(|projection| matches!(projection, ProjKey::Deref))
    else {
        return ObjectSet::root(ObjectRoot::Stack {
            function,
            local: place.local,
        });
    };
    // Fields/elements after the dereference stay in its containing object.
    // A subsequent dereference through a loaded field needs field-memory facts.
    pointer(
        state,
        &PlaceKey {
            local: place.local,
            proj: place.proj[..last_deref].to_vec(),
        },
        0,
    )
}

fn clobber(state: &mut State) {
    for objects in state.iter_mut().flatten() {
        objects.unknown = true;
    }
}

fn write(place: Place<'_>, values: Vec<ObjectSet>, state: &mut State) {
    let Some(local) = place.as_local() else {
        clobber(state);
        return;
    };
    let row = &mut state[local.as_usize()];
    row.fill(ObjectSet::default());
    for (cell, value) in row.iter_mut().zip(values) {
        *cell = value;
    }
}

fn operand_value(
    operand: &Operand<'_>,
    depth: u8,
    state: &State,
    tcx: rustc_middle::ty::TyCtxt<'_>,
) -> ObjectSet {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            pointer(state, &PlaceKey::from_place(*place), depth)
        }
        Operand::Constant(_) if source_events::operand_is_null(operand, &[], tcx) => {
            ObjectSet::null()
        }
        _ => ObjectSet::default(),
    }
}

fn statement_effect(
    function: LocalDefId,
    statement: &StatementKind<'_>,
    state: &mut State,
    tcx: rustc_middle::ty::TyCtxt<'_>,
) {
    match statement {
        StatementKind::Assign(box (destination, value)) => {
            let width = destination
                .as_local()
                .map(|local| state[local.as_usize()].len())
                .unwrap_or(0);
            let values = (0..width)
                .map(|depth| match value {
                    Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
                        operand_value(operand, depth as u8, state, tcx)
                    }
                    Rvalue::Cast(_, operand @ Operand::Constant(_), _)
                        if source_events::operand_is_null(operand, &[], tcx) =>
                    {
                        ObjectSet::null()
                    }
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        let place = PlaceKey::from_place(*place);
                        if depth == 0 {
                            storage(function, state, &place)
                        } else {
                            pointer(state, &place, (depth - 1) as u8)
                        }
                    }
                    _ => ObjectSet::default(),
                })
                .collect();
            write(*destination, values, state);
        }
        StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
            state[local.as_usize()].fill(ObjectSet::default());
        }
        StatementKind::Deinit(place) | StatementKind::SetDiscriminant { place, .. } => {
            write(**place, Vec::new(), state);
        }
        StatementKind::Intrinsic(
            box rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(_),
        ) => {
            // The copied memory may contain pointer cells. As with a projected
            // store, existing possible roots are no longer complete evidence.
            clobber(state);
        }
        _ => {}
    }
}

fn call_effect<'tcx>(
    program: &RustProgram<'tcx>,
    function: LocalDefId,
    body: &Body<'tcx>,
    location: Location,
    normal: bool,
    certificates: &crate::analyses::borrow_ownership::retirement::return_origin::CertificateMap,
    state: &mut State,
) {
    use crate::analyses::borrow_ownership::retirement::return_origin::{
        self, ClosedOrigin, Rejection,
    };
    let terminator = body.basic_blocks[location.block].terminator();
    let Some(call) = terminator.as_call(program.tcx) else {
        if matches!(
            terminator.kind,
            TerminatorKind::Drop { .. } | TerminatorKind::InlineAsm { .. }
        ) {
            clobber(state);
        }
        return;
    };
    let allocator = matches!(call.func, CallKind::LibC(name)
        if matches!(name.as_str(), "malloc" | "calloc" | "strdup" | "realloc"));
    let free = matches!(call.func, CallKind::LibC(name) if name.as_str() == "free");
    let core_pointer = matches!(call.func, CallKind::RustLib(did)
        if program.tcx.crate_name(did.krate).as_str() == "core"
            && program.tcx.def_path_str(did).contains("::ptr::")
            && matches!(program.tcx.item_name(did).as_str(), "null" | "null_mut" | "is_null"));
    let null = core_pointer
        && matches!(call.func, CallKind::RustLib(did)
        if matches!(program.tcx.item_name(did).as_str(), "null" | "null_mut"));
    let local_candidate = !allocator && !free && !core_pointer;
    let mut certificate = if !normal {
        Err(Rejection::NoNormalReturn)
    } else if call.destination.as_local().is_none() {
        Err(Rejection::UnsupportedProjection)
    } else if local_candidate {
        return_origin::for_call(program, certificates, &call)
    } else {
        Err(Rejection::ForeignCall)
    };
    let mut argument_index = None;
    let mut input_snapshot = None;
    if let Ok(proof) = certificate
        && let ClosedOrigin::Input(parameter) = proof.origin
    {
        let snapshot = return_origin::input_argument_index(parameter).and_then(|index| {
            let actual = call
                .args
                .get(index)
                .ok_or(Rejection::MissingActualArgument)?;
            let supported = match &actual.node {
                Operand::Copy(place) | Operand::Move(place) => {
                    place.projection.iter().all(|projection| {
                        matches!(projection, rustc_middle::mir::ProjectionElem::Deref)
                    })
                }
                Operand::Constant(_) => {
                    source_events::operand_is_null(&actual.node, &[], program.tcx)
                }
            };
            if !supported {
                return Err(Rejection::UnsupportedActual);
            }
            Ok((index, operand_value(&actual.node, 0, state, program.tcx)))
        });
        match snapshot {
            Ok((index, objects)) => {
                argument_index = Some(index);
                input_snapshot = Some(objects);
            }
            Err(reason) => certificate = Err(reason),
        }
    }
    // Return identity is not an effect summary. Retain this exact old clobber,
    // after taking any admitted actual-value snapshot and before destination write.
    if local_candidate {
        clobber(state);
    }
    if normal {
        let mut value = if allocator {
            ObjectSet::root(ObjectRoot::Fresh {
                frame: function,
                site: location,
            })
        } else if null {
            ObjectSet::null()
        } else {
            match certificate {
                Ok(proof) => match proof.origin {
                    ClosedOrigin::Fresh => ObjectSet::root(ObjectRoot::Fresh {
                        frame: function,
                        site: location,
                    }),
                    ClosedOrigin::Input(_) => input_snapshot.unwrap_or_default(),
                },
                Err(_) => ObjectSet::default(),
            }
        };
        if certificate.is_ok_and(|proof| proof.nullable) {
            // Null contributes no object. The explicit alternative lives in the
            // certificate/receipt; this union never clears an actual's Unknown.
            value.union(&ObjectSet::null());
        }
        write(call.destination, vec![value], state);
    }
    #[cfg(test)]
    if local_candidate {
        return_origin::record_transfer(|| return_origin::TransferReceipt {
            caller: function,
            callee: return_origin::direct_callee(program, &call).ok(),
            location,
            normal,
            certificate,
            argument_index,
            // Observe the actual post-write state. A projected write can discard
            // a factory value, so that value is never substituted for delivery.
            destination_objects: pointer(state, &PlaceKey::from_place(call.destination), 0),
        });
    }
}

fn join(entry: &mut Option<State>, incoming: State) -> bool {
    let Some(previous) = entry else {
        *entry = Some(incoming);
        return true;
    };
    let mut changed = false;
    for (old, new) in previous.iter_mut().flatten().zip(incoming.iter().flatten()) {
        changed |= old.union(new);
    }
    changed
}

impl ObjectFacts {
    pub(crate) fn analyze(
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        events: &SourceEvents,
        origin_flows: &crate::analyses::borrow_ownership::origin_flow::OriginFlowResults,
    ) -> Self {
        let certificates = crate::analyses::borrow_ownership::retirement::return_origin::derive(
            program,
            origin_flows,
        );
        let mut facts = Self::default();
        for &function in &program.functions {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let universe = &slots.fn_local_slots[&function];
            let initial: State = body
                .local_decls
                .indices()
                .map(|local| {
                    (0..MAX_SLOT_DEPTH)
                        .filter_map(|depth| {
                            universe.slot_for_local_depth(local, depth).map(|_| {
                                if local.as_usize() > 0 && local.as_usize() <= body.arg_count {
                                    ObjectSet::root(ObjectRoot::Input {
                                        function,
                                        parameter: local,
                                        depth,
                                    })
                                } else {
                                    ObjectSet::default()
                                }
                            })
                        })
                        .collect()
                })
                .collect();
            let function_path = program.tcx.def_path_str(function.to_def_id());
            let reallocations: Vec<_> = events
                .reallocations
                .iter()
                .filter(|site| site.key.function == function_path)
                .collect();
            let mut entries = vec![None; body.basic_blocks.len()];
            entries[START_BLOCK.as_usize()] = Some(initial);
            let mut queue = VecDeque::from([START_BLOCK]);
            let mut queued = vec![false; body.basic_blocks.len()];
            queued[START_BLOCK.as_usize()] = true;
            while let Some(block) = queue.pop_front() {
                queued[block.as_usize()] = false;
                let data = &body.basic_blocks[block];
                let mut state = entries[block.as_usize()]
                    .clone()
                    .expect("reachable object state");
                for statement in &data.statements {
                    statement_effect(function, &statement.kind, &mut state, program.tcx);
                }
                let location = Location {
                    block,
                    statement_index: data.statements.len(),
                };
                for successor in data.terminator().successors() {
                    let mut outgoing = state.clone();
                    let normal = matches!(data.terminator().kind,
                        TerminatorKind::Call { target: Some(target), .. } if target == successor);
                    call_effect(
                        program,
                        function,
                        &body,
                        location,
                        normal,
                        &certificates,
                        &mut outgoing,
                    );
                    for site in &reallocations {
                        let ReallocResult::DirectBranch(branch) = &site.result else { continue };
                        if branch.test != location
                            || (successor != branch.success && successor != branch.failure)
                        {
                            continue;
                        }
                        let failure = successor == branch.failure;
                        for local in std::iter::once(branch.result).chain(
                            branch
                                .transports
                                .iter()
                                .map(|transport| transport.destination),
                        ) {
                            let row = &mut outgoing[local.as_usize()];
                            row.fill(if failure {
                                ObjectSet::null()
                            } else {
                                ObjectSet::default()
                            });
                            if !failure && let Some(value) = row.first_mut() {
                                *value = ObjectSet::root(ObjectRoot::Fresh {
                                    frame: function,
                                    site: Location {
                                        block: rustc_middle::mir::BasicBlock::from_u32(
                                            site.key.block,
                                        ),
                                        statement_index: site.key.statement,
                                    },
                                });
                            }
                        }
                    }
                    if join(&mut entries[successor.as_usize()], outgoing)
                        && !queued[successor.as_usize()]
                    {
                        queued[successor.as_usize()] = true;
                        queue.push_back(successor);
                    }
                }
            }
            // Snapshot only after convergence: joins never retain a first-path
            // singleton as if it were the complete possible-object set.
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let Some(mut state) = entries[block.as_usize()].clone() else { continue };
                for (statement_index, statement) in data.statements.iter().enumerate() {
                    facts.snapshots.insert(
                        (
                            function,
                            Location {
                                block,
                                statement_index,
                            },
                        ),
                        snapshot(&state),
                    );
                    statement_effect(function, &statement.kind, &mut state, program.tcx);
                }
                facts.snapshots.insert(
                    (
                        function,
                        Location {
                            block,
                            statement_index: data.statements.len(),
                        },
                    ),
                    snapshot(&state),
                );
            }
        }
        facts
    }

    pub(crate) fn pointer_at(
        &self,
        function: LocalDefId,
        location: Location,
        place: &PlaceKey,
        extra_depth: u8,
    ) -> ObjectSet {
        if !place
            .proj
            .iter()
            .all(|projection| matches!(projection, ProjKey::Deref))
        {
            return ObjectSet::default();
        }
        let Ok(depth) = u8::try_from(place.proj.len() + usize::from(extra_depth)) else {
            return ObjectSet::default();
        };
        self.snapshots
            .get(&(function, location))
            .and_then(|state| state.get(&(place.local, depth)))
            .cloned()
            .unwrap_or_default()
    }

    pub(crate) fn storage_at(
        &self,
        function: LocalDefId,
        location: Location,
        place: &PlaceKey,
    ) -> ObjectSet {
        if !self.has_location(function, location) {
            return ObjectSet::default();
        }
        let Some(last_deref) = place
            .proj
            .iter()
            .rposition(|projection| matches!(projection, ProjKey::Deref))
        else {
            return ObjectSet::root(ObjectRoot::Stack {
                function,
                local: place.local,
            });
        };
        self.pointer_at(
            function,
            location,
            &PlaceKey {
                local: place.local,
                proj: place.proj[..last_deref].to_vec(),
            },
            0,
        )
    }

    pub(crate) fn has_location(&self, function: LocalDefId, location: Location) -> bool {
        self.snapshots.contains_key(&(function, location))
    }
}
