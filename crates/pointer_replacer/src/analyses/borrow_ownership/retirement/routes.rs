//! Source-event routes over finite call paths. Cyclic uncertainty propagates
//! through a finite context join; no call or allocation site proves an epoch.

use std::collections::{BTreeSet, VecDeque};

use rustc_hash::FxHashMap;
use rustc_middle::mir::{BasicBlock, Body, Location, StatementKind, TerminatorKind, UnwindAction};
use rustc_span::def_id::LocalDefId;

use super::objects::{ObjectFacts, ObjectRoot, ObjectSet};
use crate::{
    analyses::{
        borrow_ownership::{
            export::PlaceKey,
            source_events::{
                Coverage, SourceCallRoute, SourceEvents, SourceObject, SourcePhase,
                SourceRetirement, SourceRole,
            },
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RouteReason {
    UnknownFunction(String),
    InvalidEvent,
    InvalidCall,
    MissingSourceEvent,
    MissingRouteEvent,
    UnreachableRouteEvent,
    UnknownObject,
    DropEffects,
    MissingArgument { parameter: u32, depth: u8 },
    ForeignInputFrame(LocalDefId),
    Recursive(LocalDefId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct RouteStep {
    pub(crate) caller: LocalDefId,
    pub(crate) callee: LocalDefId,
    pub(crate) location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FrameEvent {
    pub(crate) source: SourceRetirement,
    pub(crate) frame: LocalDefId,
    pub(crate) location: Location,
    pub(crate) phase: SourcePhase,
    pub(crate) objects: ObjectSet,
    /// Inner-to-outer: each appended step calls the previously represented frame.
    pub(crate) route: Vec<RouteStep>,
    pub(crate) uncertainty: Option<RouteReason>,
    pub(crate) unreachable: bool,
}

/// A malformed row stays here in full, rather than acquiring invented compiler
/// identities or disappearing from the inventory. Any problem is fail-closed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RouteProblem {
    pub(crate) source: Option<SourceRetirement>,
    pub(crate) route: Option<SourceCallRoute>,
    pub(crate) reason: RouteReason,
}

#[derive(Default)]
pub(crate) struct RoutedEvents {
    pub(crate) frames: FxHashMap<LocalDefId, Vec<FrameEvent>>,
    pub(crate) problems: Vec<RouteProblem>,
}

fn valid_event<'tcx>(
    program: &RustProgram<'tcx>,
    body: &Body<'tcx>,
    event: &SourceRetirement,
    events: &SourceEvents,
    function: LocalDefId,
) -> bool {
    let key = &event.key;
    let Some(block) = body.basic_blocks.get(BasicBlock::from_u32(key.block)) else { return false };
    if let Some(local) = key.storage_local
        && local as usize >= body.local_decls.len()
    {
        return false;
    }
    if let SourceObject::HeapThrough(place)
    | SourceObject::PointerStorage(place)
    | SourceObject::Storage(place) = &event.object
        && place.local.as_usize() >= body.local_decls.len()
    {
        return false;
    }
    if key.statement < block.statements.len() {
        return key.phase == SourcePhase::Statement
            && key.role == SourceRole::StorageDead
            && matches!(block.statements[key.statement].kind, StatementKind::StorageDead(local)
                if key.storage_local == Some(local.as_u32()));
    }
    if key.statement != block.statements.len() {
        return false;
    }
    let terminator = block.terminator();
    match key.role {
        SourceRole::Free | SourceRole::ReallocOld => key.phase == SourcePhase::Call
            && events.call_targets.get(&(function, Location { block: BasicBlock::from_u32(key.block), statement_index: key.statement }))
                .is_some_and(|targets| targets.known.iter().any(|target| matches!(
                    super::source_events::call_targets::kind_for_target(program.tcx, *target),
                    CallKind::LibC(name) if name.as_str() == if key.role == SourceRole::Free { "free" } else { "realloc" }))),
        SourceRole::Drop => key.phase == SourcePhase::Call && (matches!(terminator.kind, TerminatorKind::Drop { .. })
            || events.call_targets.get(&(function, Location { block: BasicBlock::from_u32(key.block), statement_index: key.statement }))
                .is_some_and(|targets| {
                    let args = match &terminator.kind {
                        TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => args,
                        _ => return false,
                    };
                    targets.known.iter().any(|target| super::source_events::library_drop_effect(
                        program.tcx, body, *target, args.first().map(|argument| &argument.node))
                        // R308-1: the unknown-retirement event emitted for an
                        // inherent-method callee outside the scanned set. The
                        // membership test retires this disjunct by itself once
                        // impl bodies are scanned.
                        || matches!(
                            super::source_events::call_targets::kind_for_target(program.tcx, *target),
                            CallKind::Impl(callee) if !program.functions.contains(&callee)))
                })),
        SourceRole::ReturnStorage => key.phase == SourcePhase::Return
            && key.storage_local.is_some() && matches!(terminator.kind, TerminatorKind::Return),
        SourceRole::UnwindStorage => key.phase == SourcePhase::Unwind && key.storage_local.is_some()
            && matches!(terminator.kind, TerminatorKind::UnwindResume
                | TerminatorKind::Call { unwind: UnwindAction::Continue, .. }
                | TerminatorKind::Drop { unwind: UnwindAction::Continue, .. }
                | TerminatorKind::Assert { unwind: UnwindAction::Continue, .. }
                | TerminatorKind::InlineAsm { unwind: UnwindAction::Continue, .. }),
        SourceRole::StorageDead => false,
    }
}

fn substitute(
    program: &RustProgram<'_>,
    row: &FrameEvent,
    step: RouteStep,
    metadata: &SourceCallRoute,
    facts: &ObjectFacts,
) -> (ObjectSet, Option<RouteReason>) {
    let mut output = ObjectSet {
        roots: Default::default(),
        unknown: row.objects.unknown,
    };
    let mut uncertainty = row.uncertainty.clone();
    for root in &row.objects.roots {
        match *root {
            ObjectRoot::Input {
                function,
                parameter,
                depth,
            } if function == step.callee => {
                let argument = parameter
                    .as_usize()
                    .checked_sub(1)
                    .and_then(|index| metadata.arguments.get(index))
                    .and_then(Option::as_ref);
                if let Some(argument) = argument {
                    let objects = facts.pointer_at(step.caller, step.location, argument, depth);
                    output.unknown |= objects.unknown;
                    output.roots.extend(objects.roots);
                } else if depth == 0
                    && parameter.as_usize().checked_sub(1).is_some_and(|index| {
                        let body = program
                            .tcx
                            .mir_drops_elaborated_and_const_checked(step.caller)
                            .borrow();
                        body.basic_blocks[step.location.block]
                            .terminator()
                            .as_call(program.tcx)
                            .and_then(|call| call.args.get(index))
                            .is_some_and(|argument| {
                                super::source_events::operand_is_null(
                                    &argument.node,
                                    &[],
                                    program.tcx,
                                )
                            })
                    })
                {
                    // Constants have no PlaceKey. Known None contributes no
                    // retiring object, rather than a missing argument route.
                } else {
                    output.unknown = true;
                    uncertainty.get_or_insert(RouteReason::MissingArgument {
                        parameter: parameter.as_u32(),
                        depth,
                    });
                }
            }
            ObjectRoot::Input { function, .. } => {
                output.unknown = true;
                uncertainty.get_or_insert(RouteReason::ForeignInputFrame(function));
            }
            ObjectRoot::Fresh { .. } => {
                output.roots.insert(ObjectRoot::Fresh {
                    frame: step.caller,
                    site: step.location,
                });
            }
            ObjectRoot::Stack { .. } => {
                output.roots.insert(*root);
            }
            // Row (b): a field root's base names objects of THIS frame, and
            // wave 1 has no rebasing rule for it. Fail closed rather than let
            // field identity cross a frame unrebased.
            ObjectRoot::Field { .. } => {
                output.unknown = true;
            }
        }
    }
    if output.unknown {
        uncertainty.get_or_insert(RouteReason::UnknownObject);
    }
    (output, uncertainty)
}

pub(crate) fn expand(
    program: &RustProgram<'_>,
    events: &SourceEvents,
    facts: &ObjectFacts,
) -> RoutedEvents {
    let functions: FxHashMap<_, _> = program
        .functions
        .iter()
        .map(|&function| (program.tcx.def_path_str(function.to_def_id()), function))
        .collect();
    let mut result = RoutedEvents::default();
    let mut incoming = FxHashMap::<LocalDefId, Vec<(RouteStep, &SourceCallRoute)>>::default();
    for route in &events.calls {
        let caller = functions.get(&route.caller).copied();
        let callee = functions.get(&route.callee).copied();
        let (Some(caller), Some(callee)) = (caller, callee) else {
            result.problems.push(RouteProblem {
                source: None,
                route: Some(route.clone()),
                reason: RouteReason::UnknownFunction(if caller.is_none() {
                    route.caller.clone()
                } else {
                    route.callee.clone()
                }),
            });
            continue;
        };
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
        let block = BasicBlock::from_u32(route.block);
        let valid = body.basic_blocks.get(block).is_some_and(|data| {
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            let args = match &data.terminator().kind {
                TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => args,
                _ => return false,
            };
            events
                .call_targets
                .get(&(caller, location))
                .is_some_and(|targets| targets.known.contains(&callee.to_def_id()))
                && args
                    .iter()
                    .map(|argument| argument.node.place().map(PlaceKey::from_place))
                    .collect::<Vec<_>>()
                    == route.arguments
        });
        if !valid {
            result.problems.push(RouteProblem {
                source: None,
                route: Some(route.clone()),
                reason: RouteReason::InvalidCall,
            });
            continue;
        }
        if route
            .events
            .iter()
            .any(|key| !events.retirements.contains_key(key))
        {
            result.problems.push(RouteProblem {
                source: None,
                route: Some(route.clone()),
                reason: RouteReason::MissingSourceEvent,
            });
        }
        incoming.entry(callee).or_default().push((
            RouteStep {
                caller,
                callee,
                location: Location {
                    block,
                    statement_index: body.basic_blocks[block].statements.len(),
                },
            },
            route,
        ));
    }
    let mut pending = VecDeque::new();
    for (key, source) in &events.retirements {
        let Some(&frame) = functions.get(&key.function) else {
            result.problems.push(RouteProblem {
                source: Some(source.clone()),
                route: None,
                reason: RouteReason::UnknownFunction(key.function.clone()),
            });
            continue;
        };
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(frame)
            .borrow();
        if key != &source.key || !valid_event(program, &body, source, events, frame) {
            result.problems.push(RouteProblem {
                source: Some(source.clone()),
                route: None,
                reason: RouteReason::InvalidEvent,
            });
            continue;
        }
        let location = Location {
            block: BasicBlock::from_u32(key.block),
            statement_index: key.statement,
        };
        let drop_effects = source.coverage == Coverage::UnresolvedDropEffects;
        let objects = if drop_effects {
            ObjectSet::default()
        } else {
            match &source.object {
                SourceObject::HeapThrough(place) => facts.pointer_at(frame, location, place, 0),
                SourceObject::PointerStorage(place) | SourceObject::Storage(place) => {
                    facts.storage_at(frame, location, place)
                }
                SourceObject::Null => ObjectSet {
                    roots: Default::default(),
                    unknown: false,
                },
                SourceObject::UnknownOperand => ObjectSet::default(),
            }
        };
        let uncertainty = if drop_effects {
            Some(RouteReason::DropEffects)
        } else {
            objects.unknown.then_some(RouteReason::UnknownObject)
        };
        pending.push_back(FrameEvent {
            source: source.clone(),
            frame,
            location,
            phase: key.phase,
            objects,
            route: Vec::new(),
            uncertainty,
            unreachable: !facts.has_location(frame, location),
        });
    }
    let mut seen = BTreeSet::new();
    let mut recursive_seen = BTreeSet::new();
    while let Some(row) = pending.pop_front() {
        // Once recursion makes the object Unknown, propagate that fact to
        // every outer call context. Joining by event/frame/callsite terminates
        // the cycle without discarding its effects on callers outside it.
        if matches!(row.uncertainty, Some(RouteReason::Recursive(_)))
            && !recursive_seen.insert((
                row.source.key.clone(),
                row.frame.local_def_index.as_u32(),
                row.location.block.as_u32(),
                row.location.statement_index,
            ))
        {
            continue;
        }
        let path: Vec<_> = row
            .route
            .iter()
            .map(|step| {
                (
                    step.caller.local_def_index.as_u32(),
                    step.callee.local_def_index.as_u32(),
                    step.location.block.as_u32(),
                    step.location.statement_index,
                )
            })
            .collect();
        if !seen.insert((
            row.source.key.clone(),
            row.frame.local_def_index.as_u32(),
            path,
        )) {
            continue;
        }
        result
            .frames
            .entry(row.frame)
            .or_default()
            .push(row.clone());
        if !matches!(
            row.source.key.role,
            SourceRole::Free | SourceRole::ReallocOld | SourceRole::Drop
        ) {
            continue;
        }
        for &(step, metadata) in incoming.get(&row.frame).into_iter().flatten() {
            let recursive = step.caller == row.frame
                || row
                    .route
                    .iter()
                    .any(|edge| edge.caller == step.caller || edge.callee == step.caller);
            let (mut objects, mut uncertainty) = substitute(program, &row, step, metadata, facts);
            if !metadata.events.contains(&row.source.key) {
                result.problems.push(RouteProblem {
                    source: Some(row.source.clone()),
                    route: Some(metadata.clone()),
                    reason: RouteReason::MissingRouteEvent,
                });
                objects.unknown = true;
                uncertainty = Some(RouteReason::MissingRouteEvent);
            }
            if recursive {
                objects = ObjectSet::default();
                uncertainty = Some(RouteReason::Recursive(step.caller));
            }
            let mut route = row.route.clone();
            route.push(step);
            pending.push_back(FrameEvent {
                source: row.source.clone(),
                frame: step.caller,
                location: step.location,
                phase: SourcePhase::Call,
                objects,
                route,
                uncertainty,
                unreachable: row.unreachable || !facts.has_location(step.caller, step.location),
            });
        }
    }
    // A listed key must also have a path through this exact call. Merely
    // finding that key elsewhere in the program is not a valid route join.
    for edges in incoming.values() {
        for (step, metadata) in edges {
            for key in &metadata.events {
                let Some(source) = events.retirements.get(key) else { continue };
                if !result
                    .frames
                    .get(&step.caller)
                    .into_iter()
                    .flatten()
                    .any(|row| &row.source.key == key && row.route.last() == Some(step))
                {
                    result.problems.push(RouteProblem {
                        source: Some(source.clone()),
                        route: Some((*metadata).clone()),
                        reason: RouteReason::UnreachableRouteEvent,
                    });
                }
            }
        }
    }
    result
}
