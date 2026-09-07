//! Incoming identities and current bindings over the original source CFG.
//!
//! Binding joins forget disagreements. The immutable incoming target and its
//! Ref demand remain live for the invocation, independently of that precision.

use std::collections::{BTreeSet, VecDeque};

use rustc_middle::mir::{
    Body, CastKind, Local, Location, Operand, Place, ProjectionElem, Rvalue, START_BLOCK,
    StatementKind, TerminatorKind, UnwindAction,
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
        source_events::{SourcePhase, addressed_locals},
    },
    utils::rustc::RustProgram,
};

type Bindings = Vec<Vec<CurrentBinding>>;

fn forget_place(place: Place<'_>, state: &mut Bindings) {
    if let Some(local) = place.as_local() {
        state[local.as_usize()].fill(CurrentBinding::Unknown);
    } else {
        // There is no field-memory/alias proof in this bounded producer. A
        // projected write must not leave a guessed incoming binding behind.
        for row in state {
            row.fill(CurrentBinding::Unknown);
        }
    }
}

fn forget_move(operand: &Operand<'_>, state: &mut Bindings) {
    if let Operand::Move(place) = operand {
        forget_place(*place, state);
    }
}

fn place_bindings(
    place: Place<'_>,
    address_of: bool,
    state: &Bindings,
) -> Option<Vec<CurrentBinding>> {
    let mut depth = 0usize;
    for projection in place.projection {
        if !matches!(projection, ProjectionElem::Deref) {
            return None;
        }
        depth += 1;
    }
    if address_of {
        depth = depth.checked_sub(1)?;
    }
    state[place.local.as_usize()]
        .get(depth..)
        .map(<[_]>::to_vec)
}

fn transfer_statement(statement: &StatementKind<'_>, state: &mut Bindings) {
    match statement {
        StatementKind::Assign(box (destination, value)) => {
            let Some(local) = destination.as_local() else {
                forget_place(*destination, state);
                return;
            };
            let operand = match value {
                Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
                    Some(operand)
                }
                _ => None,
            };
            let incoming = match value {
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    place_bindings(*place, true, state)
                }
                Rvalue::CopyForDeref(place) => place_bindings(*place, false, state),
                _ => operand
                    .and_then(|operand| operand.place())
                    .and_then(|place| place_bindings(place, false, state)),
            };
            if let Some(operand) = operand {
                forget_move(operand, state);
            }
            let row = &mut state[local.as_usize()];
            row.fill(CurrentBinding::Unknown);
            if let Some(incoming) = incoming {
                for (destination, source) in row.iter_mut().zip(incoming) {
                    *destination = source;
                }
            }
        }
        StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
            state[local.as_usize()].fill(CurrentBinding::Unknown);
        }
        StatementKind::Deinit(place) | StatementKind::SetDiscriminant { place, .. } => {
            forget_place(**place, state);
        }
        StatementKind::Intrinsic(
            box rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(_),
        ) => {
            // An unclassified memory copy can overwrite pointer-bearing cells.
            for row in state {
                row.fill(CurrentBinding::Unknown);
            }
        }
        _ => {}
    }
}

fn call_effects(state: &mut Bindings, addressed: &BTreeSet<Local>) {
    for (index, row) in state.iter_mut().enumerate() {
        if addressed.contains(&Local::from_usize(index)) {
            row.fill(CurrentBinding::Unknown);
        } else {
            // A call cannot rebind an unexposed local, but its reachable memory
            // may have changed. This is not a disjointness assertion.
            for binding in row.iter_mut().skip(1) {
                *binding = CurrentBinding::Unknown;
            }
        }
    }
}

fn terminator_effects(
    terminator: &TerminatorKind<'_>,
    state: &mut Bindings,
    addressed: &BTreeSet<Local>,
) {
    match terminator {
        TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
            call_effects(state, addressed);
            for argument in args {
                forget_move(&argument.node, state);
            }
        }
        TerminatorKind::Drop { place, .. } => {
            call_effects(state, addressed);
            forget_place(*place, state);
        }
        TerminatorKind::InlineAsm { .. } => {
            for row in state {
                row.fill(CurrentBinding::Unknown);
            }
        }
        _ => {}
    }
}

fn merge(entry: &mut Option<Bindings>, incoming: Bindings) -> bool {
    let Some(previous) = entry else {
        *entry = Some(incoming);
        return true;
    };
    let mut changed = false;
    for (old, new) in previous
        .iter_mut()
        .flatten()
        .zip(incoming.into_iter().flatten())
    {
        if *old != CurrentBinding::Unknown && *old != new {
            *old = CurrentBinding::Unknown;
            changed = true;
        }
    }
    changed
}

fn converge(
    body: &Body<'_>,
    initial: Bindings,
    addressed: &BTreeSet<Local>,
) -> Vec<Option<Bindings>> {
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
            .expect("reachable binding state");
        for statement in &data.statements {
            transfer_statement(&statement.kind, &mut state);
        }
        terminator_effects(&data.terminator().kind, &mut state, addressed);
        for successor in data.terminator().successors() {
            let mut outgoing = state.clone();
            if let TerminatorKind::Call {
                destination,
                target: Some(target),
                ..
            } = &data.terminator().kind
                && successor == *target
            {
                // A call writes its destination only on the normal return
                // edge. Its unwind edge keeps the preceding binding state.
                forget_place(*destination, &mut outgoing);
            }
            if merge(&mut entries[successor.as_usize()], outgoing) && !queued[successor.as_usize()]
            {
                queued[successor.as_usize()] = true;
                queue.push_back(successor);
            }
        }
    }
    entries
}

fn observe(
    analysis: &mut EntryAnalysis,
    entries: &[EntryObligation],
    function: LocalDefId,
    state: &Bindings,
    location: Location,
    phase: SourcePhase,
    moment: EntryMoment,
) {
    let live = moment == EntryMoment::AtEvent;
    for entry in entries {
        analysis.observations.push(EntryObservation {
            entry: entry.key,
            target: entry.target,
            location,
            phase,
            moment,
            live,
            demand: live.then_some(entry.key),
            current_binding: if live {
                state[entry.key.parameter.as_usize()][usize::from(entry.key.depth)]
            } else {
                CurrentBinding::Unknown
            },
        });
    }
    if live {
        for (local, row) in state.iter().enumerate() {
            for (depth, binding) in row.iter().enumerate() {
                if let CurrentBinding::Incoming(target) = binding {
                    analysis.binding_facts.push(BindingFact {
                        function,
                        local: Local::from_usize(local),
                        depth: depth as u8,
                        location,
                        phase,
                        moment,
                        target: *target,
                    });
                }
            }
        }
    }
}

pub(super) fn analyze(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    is_ref: impl Fn(SlotRef) -> bool,
) -> EntryAnalysis {
    let mut analysis = EntryAnalysis::default();
    for &function in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let universe = &slots.fn_local_slots[&function];
        let mut initial: Bindings = body
            .local_decls
            .indices()
            .map(|local| {
                (0..MAX_SLOT_DEPTH)
                    .filter_map(|depth| {
                        universe
                            .slot_for_local_depth(local, depth)
                            .map(|_| CurrentBinding::Unknown)
                    })
                    .collect()
            })
            .collect();
        let mut entries = Vec::new();
        for index in 1..=body.arg_count {
            let parameter = Local::from_usize(index);
            for depth in 0..MAX_SLOT_DEPTH {
                let Some(slot) = universe.slot_for_local_depth(parameter, depth) else { continue };
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
                initial[index][usize::from(depth)] = CurrentBinding::Incoming(target);
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
        analysis.entries.extend(entries.iter().cloned());
        let addressed = addressed_locals(&body);
        let states = converge(&body, initial, &addressed);
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let Some(mut state) = states[block.as_usize()].clone() else { continue };
            for (statement_index, statement) in data.statements.iter().enumerate() {
                observe(
                    &mut analysis,
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
                transfer_statement(&statement.kind, &mut state);
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
            observe(
                &mut analysis,
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
                observe(
                    &mut analysis,
                    &entries,
                    function,
                    &state,
                    location,
                    phase,
                    EntryMoment::AfterExit,
                );
            }
            // Continue leaves this frame without a cleanup block. Terminate
            // aborts instead and supplies no source memory-retirement event.
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
                terminator_effects(terminator, &mut state, &addressed);
                for moment in [EntryMoment::AtEvent, EntryMoment::AfterExit] {
                    observe(
                        &mut analysis,
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
    analysis
}

#[cfg(test)]
mod memory_effect_tests {
    use rustc_middle::mir::{CopyNonOverlapping, NonDivergingIntrinsic};

    use super::*;
    use crate::analyses::borrow_ownership::slots::SlotId;

    #[test]
    fn e5_p_copy_intrinsic_forgets_overwritable_inner_binding() {
        // Raw-MIR graph input only: no memory copy is executed. The count and
        // pointer operands are source locals, not a proven zero-length copy.
        let parameter = Local::from_u32(1);
        let entry = EntryKey {
            function: rustc_hir::def_id::CRATE_DEF_ID,
            parameter,
            depth: 1,
            slot: SlotRef::Local(rustc_hir::def_id::CRATE_DEF_ID, SlotId::from_u32(1)),
        };
        let mut state = vec![
            vec![],
            vec![
                CurrentBinding::Unknown,
                CurrentBinding::Incoming(IncomingTarget {
                    entry,
                    dereferences: 2,
                }),
            ],
            vec![CurrentBinding::Unknown],
            vec![],
        ];
        let statement = StatementKind::Intrinsic(Box::new(
            NonDivergingIntrinsic::CopyNonOverlapping(CopyNonOverlapping {
                src: Operand::Copy(Place::from(Local::from_u32(2))),
                dst: Operand::Copy(Place::from(parameter)),
                count: Operand::Copy(Place::from(Local::from_u32(3))),
            }),
        ));
        transfer_statement(&statement, &mut state);
        assert_eq!(
            state[1][1],
            CurrentBinding::Unknown,
            "a memory copy may replace the pointed-to pointer value"
        );
    }
}
