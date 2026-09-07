//! Independent entry-fact check over the original MIR. This checker computes
//! predecessor intersections in whole-CFG rounds; it consumes no producer facts
//! until the final comparison.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::FxHashSet;
use rustc_middle::mir::{
    BasicBlock, Body, CastKind, Local, Location, Operand, Place, ProjectionElem, Rvalue,
    START_BLOCK, StatementKind, TerminatorKind, UnwindAction,
};
use rustc_span::def_id::LocalDefId;

use super::{
    BindingFact, CurrentBinding, EntryAnalysis, EntryCondition, EntryKey, EntryMoment,
    EntryObligation, EntryObservation, EntryRepresentation, IncomingTarget,
};
use crate::{
    analyses::borrow_ownership::{
        crate_slots::{CrateSlots, MAX_SLOT_DEPTH},
        solver::SlotRef,
        source_events::SourcePhase,
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Fact {
    Entry(EntryObligation),
    Observation(EntryObservation),
    Binding(BindingFact),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FactDelta {
    pub(crate) missing: Vec<Fact>,
    pub(crate) extra: Vec<Fact>,
    pub(crate) duplicates: Vec<Fact>,
}

// Absence means Unknown. A known target survives a join only when every
// reachable incoming edge establishes that same target for that cell.
type State = BTreeMap<(Local, u8), IncomingTarget>;

fn erase(place: Place<'_>, state: &mut State) {
    match place.as_local() {
        Some(local) => state.retain(|(owner, _), _| *owner != local),
        None => state.clear(),
    }
}

fn consume_move(operand: &Operand<'_>, state: &mut State) {
    if let Operand::Move(place) = operand {
        erase(*place, state);
    }
}

fn statement_effect(statement: &StatementKind<'_>, widths: &[u8], state: &mut State) {
    match statement {
        StatementKind::Assign(box (destination, value)) => {
            let Some(local) = destination.as_local() else {
                state.clear();
                return;
            };
            let operand = match value {
                Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
                    Some(operand)
                }
                _ => None,
            };
            let source = match value {
                Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
                    operand.place().map(|place| (place, false))
                }
                Rvalue::CopyForDeref(place) => Some((*place, false)),
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => Some((*place, true)),
                _ => None,
            }
            .and_then(|(place, address)| {
                if !place
                    .projection
                    .iter()
                    .all(|element| matches!(element, ProjectionElem::Deref))
                {
                    return None;
                }
                // Reading through k dereferences selects depth k. Taking the
                // address reverses its final dereference; &local is a storage
                // address and therefore supplies no incoming-target binding.
                let offset = place.projection.len().checked_sub(usize::from(address))?;
                Some((place.local, u8::try_from(offset).ok()?))
            });
            // Read before erasing: a moved source can be the destination itself.
            let copied = source
                .map(|(source, offset)| {
                    (0..widths[local.as_usize()])
                        .filter_map(|depth| {
                            let source_depth = depth.checked_add(offset)?;
                            state
                                .get(&(source, source_depth))
                                .map(|target| (depth, *target))
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            if let Some(operand) = operand {
                consume_move(operand, state);
            }
            erase(*destination, state);
            state.extend(
                copied
                    .into_iter()
                    .map(|(depth, target)| ((local, depth), target)),
            );
        }
        StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
            state.retain(|(owner, _), _| owner != local);
        }
        StatementKind::Deinit(place) | StatementKind::SetDiscriminant { place, .. } => {
            erase(**place, state);
        }
        StatementKind::Intrinsic(
            box rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(_),
        ) => {
            state.clear();
        }
        _ => {}
    }
}

fn terminator_effect(
    terminator: &TerminatorKind<'_>,
    exposed: &BTreeSet<Local>,
    state: &mut State,
) {
    match terminator {
        TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
            state.retain(|(local, depth), _| *depth == 0 && !exposed.contains(local));
            for argument in args {
                consume_move(&argument.node, state);
            }
        }
        TerminatorKind::Drop { place, .. } => {
            state.retain(|(local, depth), _| *depth == 0 && !exposed.contains(local));
            erase(*place, state);
        }
        TerminatorKind::InlineAsm { .. } => state.clear(),
        _ => {}
    }
}

fn intersection(accumulated: &mut Option<State>, incoming: State) {
    match accumulated {
        Some(previous) => previous.retain(|cell, target| incoming.get(cell) == Some(target)),
        None => *accumulated = Some(incoming),
    }
}

fn block_states(
    body: &Body<'_>,
    widths: &[u8],
    seed: &State,
    exposed: &BTreeSet<Local>,
) -> Vec<Option<State>> {
    let mut predecessors = vec![Vec::<BasicBlock>::new(); body.basic_blocks.len()];
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for successor in data.terminator().successors() {
            predecessors[successor.as_usize()].push(block);
        }
    }
    let mut before = vec![None::<State>; body.basic_blocks.len()];
    let mut after = before.clone();
    // None is unreachable, distinct from a reachable all-Unknown state. Each
    // newly reachable predecessor can only remove knowledge at an intersection;
    // the finite set of input-entry targets bounds subsequent decreases.
    loop {
        let mut changed = false;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let mut incoming = (block == START_BLOCK).then(|| seed.clone());
            for &predecessor in &predecessors[block.as_usize()] {
                let Some(mut edge) = after[predecessor.as_usize()].clone() else { continue };
                if let TerminatorKind::Call {
                    destination,
                    target: Some(normal),
                    ..
                } = &body.basic_blocks[predecessor].terminator().kind
                    && *normal == block
                {
                    // A failed/unwinding call never assigns its destination.
                    erase(*destination, &mut edge);
                }
                intersection(&mut incoming, edge);
            }
            if before[block.as_usize()] != incoming {
                before[block.as_usize()] = incoming.clone();
                changed = true;
            }
            let outgoing = incoming.map(|mut state| {
                for statement in &data.statements {
                    statement_effect(&statement.kind, widths, &mut state);
                }
                terminator_effect(&data.terminator().kind, exposed, &mut state);
                state
            });
            if after[block.as_usize()] != outgoing {
                after[block.as_usize()] = outgoing;
                changed = true;
            }
        }
        if !changed {
            return before;
        }
    }
}

fn phase_facts(
    facts: &mut Vec<Fact>,
    entries: &[EntryObligation],
    function: LocalDefId,
    state: &State,
    location: Location,
    phase: SourcePhase,
    moment: EntryMoment,
) {
    let live = moment == EntryMoment::AtEvent;
    for entry in entries {
        facts.push(Fact::Observation(EntryObservation {
            entry: entry.key,
            target: entry.target,
            location,
            phase,
            moment,
            live,
            demand: live.then_some(entry.key),
            current_binding: if live {
                state
                    .get(&(entry.key.parameter, entry.key.depth))
                    .copied()
                    .map(CurrentBinding::Incoming)
                    .unwrap_or(CurrentBinding::Unknown)
            } else {
                CurrentBinding::Unknown
            },
        }));
    }
    if live {
        facts.extend(state.iter().map(|(&(local, depth), &target)| {
            Fact::Binding(BindingFact {
                function,
                local,
                depth,
                location,
                phase,
                moment,
                target,
            })
        }));
    }
}

fn expected_facts(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
) -> Vec<Fact> {
    let mut facts = Vec::new();
    for &function in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let universe = &slots.fn_local_slots[&function];
        let widths: Vec<_> = body
            .local_decls
            .indices()
            .map(|local| {
                (0..MAX_SLOT_DEPTH)
                    .filter(|&depth| universe.slot_for_local_depth(local, depth).is_some())
                    .count() as u8
            })
            .collect();
        let mut seed = State::new();
        let mut entries = Vec::new();
        for parameter in body.args_iter() {
            for depth in 0..widths[parameter.as_usize()] {
                let slot = universe
                    .slot_for_local_depth(parameter, depth)
                    .expect("registered parameter depth");
                let key = EntryKey {
                    function,
                    parameter,
                    depth,
                    slot: SlotRef::Local(function, slot),
                };
                let target = IncomingTarget {
                    entry: key,
                    dereferences: depth + 1,
                };
                seed.insert((parameter, depth), target);
                if is_ref(key.slot) {
                    entries.push(EntryObligation {
                        key,
                        target,
                        condition: EntryCondition::IfNonNull,
                        representation: EntryRepresentation::MissingLegacyLoan,
                    });
                }
            }
        }
        facts.extend(entries.iter().cloned().map(Fact::Entry));
        // Derive exposure directly from MIR, independently of the producer's
        // addressed-local helper and without consulting an observed binding.
        let mut exposed = BTreeSet::new();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                if let StatementKind::Assign(box (
                    _,
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place),
                )) = &statement.kind
                    && !place
                        .projection
                        .iter()
                        .any(|element| matches!(element, ProjectionElem::Deref))
                {
                    exposed.insert(place.local);
                }
            }
        }
        let states = block_states(&body, &widths, &seed, &exposed);
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let Some(mut state) = states[block.as_usize()].clone() else { continue };
            for (statement_index, statement) in data.statements.iter().enumerate() {
                phase_facts(
                    &mut facts,
                    &entries,
                    function,
                    &state,
                    Location {
                        block,
                        statement_index,
                    },
                    SourcePhase::Statement,
                    EntryMoment::AtEvent,
                );
                statement_effect(&statement.kind, &widths, &mut state);
            }
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            let terminator = &data.terminator().kind;
            let phase = match terminator {
                TerminatorKind::Return => SourcePhase::Return,
                TerminatorKind::UnwindResume => SourcePhase::Unwind,
                TerminatorKind::Call { .. }
                | TerminatorKind::TailCall { .. }
                | TerminatorKind::Drop { .. }
                | TerminatorKind::InlineAsm { .. } => SourcePhase::Call,
                _ => SourcePhase::Statement,
            };
            phase_facts(
                &mut facts,
                &entries,
                function,
                &state,
                location,
                phase,
                EntryMoment::AtEvent,
            );
            if matches!(
                terminator,
                TerminatorKind::Return | TerminatorKind::UnwindResume
            ) {
                phase_facts(
                    &mut facts,
                    &entries,
                    function,
                    &state,
                    location,
                    phase,
                    EntryMoment::AfterExit,
                );
            }
            if matches!(
                terminator,
                TerminatorKind::Call {
                    unwind: UnwindAction::Continue,
                    ..
                } | TerminatorKind::Drop {
                    unwind: UnwindAction::Continue,
                    ..
                } | TerminatorKind::Assert {
                    unwind: UnwindAction::Continue,
                    ..
                } | TerminatorKind::InlineAsm {
                    unwind: UnwindAction::Continue,
                    ..
                }
            ) {
                terminator_effect(terminator, &exposed, &mut state);
                for moment in [EntryMoment::AtEvent, EntryMoment::AfterExit] {
                    phase_facts(
                        &mut facts,
                        &entries,
                        function,
                        &state,
                        location,
                        SourcePhase::Unwind,
                        moment,
                    );
                }
            }
        }
    }
    facts
}

pub(crate) fn check(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
    observed: &EntryAnalysis,
) -> Result<(), FactDelta> {
    let expected = expected_facts(program, slots, is_ref);
    let expected_set: FxHashSet<_> = expected.iter().cloned().collect();
    let mut seen = FxHashSet::default();
    let mut delta = FactDelta::default();
    for fact in observed
        .entries
        .iter()
        .cloned()
        .map(Fact::Entry)
        .chain(observed.observations.iter().cloned().map(Fact::Observation))
        .chain(observed.binding_facts.iter().cloned().map(Fact::Binding))
    {
        if !seen.insert(fact.clone()) {
            delta.duplicates.push(fact);
        } else if !expected_set.contains(&fact) {
            delta.extra.push(fact);
        }
    }
    delta
        .missing
        .extend(expected.into_iter().filter(|fact| !seen.contains(fact)));
    if delta.missing.is_empty() && delta.extra.is_empty() && delta.duplicates.is_empty() {
        Ok(())
    } else {
        Err(delta)
    }
}
