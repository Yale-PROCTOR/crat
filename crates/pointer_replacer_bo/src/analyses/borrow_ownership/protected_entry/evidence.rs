//! Receipts for independently validated, conditional source facts. These are
//! not universal Schedule evidence, dynamic-epoch proofs, or inferred ancestry.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use rustc_middle::mir::{Body, Location, TerminatorKind};
use rustc_span::def_id::LocalDefId;

use super::{EntryAnalysis, EntryKey, EntryMoment, validate::Fact};
use crate::{analyses::borrow_ownership::source_events::SourcePhase, utils::rustc::RustProgram};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FactRule {
    ParameterEntry(EntryKey),
    WholeCallReachability(EntryKey),
    FrameExit(EntryKey),
    /// A validated binding-flow fact; its MIR predecessors expose the actual
    /// transfers and kills without asserting a full provenance/epoch history.
    LocatedInputBinding(EntryKey),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SourcePoint {
    pub(crate) function: LocalDefId,
    pub(crate) location: Location,
    pub(crate) phase: SourcePhase,
    pub(crate) moment: EntryMoment,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FactWitness {
    pub(crate) fact: Fact,
    pub(crate) rule: FactRule,
    pub(crate) predecessors: Vec<SourcePoint>,
}

fn terminator_phase(terminator: &TerminatorKind<'_>) -> SourcePhase {
    match terminator {
        TerminatorKind::Return => SourcePhase::Return,
        TerminatorKind::UnwindResume => SourcePhase::Unwind,
        TerminatorKind::Call { .. }
        | TerminatorKind::TailCall { .. }
        | TerminatorKind::Drop { .. }
        | TerminatorKind::InlineAsm { .. } => SourcePhase::Call,
        _ => SourcePhase::Statement,
    }
}

fn predecessors(body: &Body<'_>, point: SourcePoint) -> Vec<SourcePoint> {
    if point.moment == EntryMoment::AfterExit {
        return vec![SourcePoint {
            moment: EntryMoment::AtEvent,
            ..point
        }];
    }
    let block = &body.basic_blocks[point.location.block];
    // An unwind-to-caller microevent follows this terminator's effects at the
    // same MIR location. It is distinct from both the call and its AfterExit.
    if point.phase == SourcePhase::Unwind
        && point.location.statement_index == block.statements.len()
        && !matches!(block.terminator().kind, TerminatorKind::UnwindResume)
    {
        return vec![SourcePoint {
            phase: terminator_phase(&block.terminator().kind),
            ..point
        }];
    }
    if point.location.statement_index > 0 {
        return vec![SourcePoint {
            location: Location {
                statement_index: point.location.statement_index - 1,
                ..point.location
            },
            phase: SourcePhase::Statement,
            ..point
        }];
    }
    body.basic_blocks.predecessors()[point.location.block]
        .iter()
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .map(|block| SourcePoint {
            function: point.function,
            location: Location {
                block,
                statement_index: body.basic_blocks[block].statements.len(),
            },
            phase: terminator_phase(&body.basic_blocks[block].terminator().kind),
            moment: EntryMoment::AtEvent,
        })
        .collect()
}

/// The caller must first obtain a successful `validate::check`. This writer
/// records every validated fact once; it does not validate facts by receipting
/// them. All predecessor operations come from the original MIR.
pub(super) fn derive(program: &RustProgram<'_>, facts: &EntryAnalysis) -> Vec<FactWitness> {
    let mut grouped = FxHashMap::<LocalDefId, Vec<Fact>>::default();
    for fact in facts
        .entries
        .iter()
        .cloned()
        .map(Fact::Entry)
        .chain(facts.observations.iter().cloned().map(Fact::Observation))
        .chain(facts.binding_facts.iter().cloned().map(Fact::Binding))
    {
        let function = match &fact {
            Fact::Entry(entry) => entry.key.function,
            Fact::Observation(observation) => observation.entry.function,
            Fact::Binding(binding) => binding.function,
        };
        grouped.entry(function).or_default().push(fact);
    }
    let mut witnesses = Vec::new();
    for &function in &program.functions {
        let Some(rows) = grouped.remove(&function) else { continue };
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        for fact in rows {
            let (rule, point) = match &fact {
                Fact::Entry(entry) => (FactRule::ParameterEntry(entry.key), None),
                Fact::Observation(observation) => (
                    if observation.moment == EntryMoment::AfterExit {
                        FactRule::FrameExit(observation.entry)
                    } else {
                        FactRule::WholeCallReachability(observation.entry)
                    },
                    Some(SourcePoint {
                        function,
                        location: observation.location,
                        phase: observation.phase,
                        moment: observation.moment,
                    }),
                ),
                Fact::Binding(binding) => (
                    FactRule::LocatedInputBinding(binding.target.entry),
                    Some(SourcePoint {
                        function,
                        location: binding.location,
                        phase: binding.phase,
                        moment: binding.moment,
                    }),
                ),
            };
            witnesses.push(FactWitness {
                fact,
                rule,
                predecessors: point
                    .map(|point| predecessors(&body, point))
                    .unwrap_or_default(),
            });
        }
    }
    assert!(
        grouped.is_empty(),
        "validated entry evidence must name original program functions"
    );
    witnesses
}
