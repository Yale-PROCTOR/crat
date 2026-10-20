//! Closed scalar responsibility routes. Broader field/call/reader roles remain
//! pending F/C. Eligibility is derived from complete evidence, never a free
//! solver Boolean. The accepted SSA laws are retained without modification.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use super::{
    super::{
        origin_evidence::{OriginAvailability, SourceCallee},
        ownership_access::Expression,
        ownership_occurrence::Availability,
    },
    facts::Facts,
    matched::{MatchedTransport, Meet, SourceLineage, TerminalTarget},
    transport::{CandidateGraph, Evidence, Node, Rule},
    value_origins::ValueOrigins,
};

/// Proof inventory for the closed scalar fragment. Each entry refers to the
/// same grant's exact scope, origins, route, terminal and zero-law evidence;
/// it is not an independently selectable permission bit. Fields, borrowed
/// roles and realloc cannot discharge these through this fragment's checker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum HardGate {
    #[serde(rename = "G-ID")]
    Identity,
    #[serde(rename = "G-LIN")]
    Linear,
    #[serde(rename = "G-ROLE")]
    Role,
    #[serde(rename = "G-ORIGIN")]
    Origin,
    #[serde(rename = "G-FIELD")]
    Field,
    #[serde(rename = "G-PROTECT")]
    Protection,
    #[serde(rename = "G-CLOSE")]
    Close,
    #[serde(rename = "G-EXIT")]
    Exit,
    #[serde(rename = "G-OUT")]
    Outcome,
    #[serde(rename = "G-VIEW")]
    View,
    #[serde(rename = "G-JUST")]
    Justification,
    #[serde(rename = "G-JOIN")]
    Join,
}

impl HardGate {
    pub(crate) const ALL: [Self; 12] = [
        Self::Identity,
        Self::Linear,
        Self::Role,
        Self::Origin,
        Self::Field,
        Self::Protection,
        Self::Close,
        Self::Exit,
        Self::Outcome,
        Self::View,
        Self::Justification,
        Self::Join,
    ];
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Grant {
    pub(crate) function: String,
    pub(crate) slot_key: String,
    pub(crate) carrier: Node,
    pub(crate) meet: Meet,
    /// One source-to-terminal route; every encountered split has one successor.
    pub(crate) route: Vec<Node>,
    pub(crate) discharged_gates: Vec<HardGate>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) enum HoldReason {
    Coverage,
    BranchOrLoop,
    FieldOrReference,
    InputContract,
    Origin,
    CallOrOutcome,
    CopyOrReaderRole,
    TerminalDisposition,
    UniqueRoute,
    KindJoin,
    ZeroLaw,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Hold {
    pub(crate) construction: u32,
    pub(crate) function: String,
    pub(crate) reasons: BTreeSet<HoldReason>,
}

/// The existing inference pass erases an argument temporary by registering
/// its source's consume. Accept only the exact non-reference, single-use free
/// proxy; a coincident Var or an arbitrary missing consume is insufficient.
fn free_proxies(facts: &Facts, construction: u32, function: &str) -> BTreeMap<u32, usize> {
    use super::super::{ownership_access::OperandSyntax, ownership_boundary::Window};
    let mut result = BTreeMap::new();
    let Some(occurrences) = facts.source_occurrences.get(function) else { return result };
    for registration in &facts.call_arg_registrations {
        if registration.point.construction != construction
            || registration.point.function.as_deref() != Some(function)
            || registration.by_reference
        {
            continue;
        }
        let Availability::Present(source) = registration.source_occurrence else { continue };
        let Some(consume) = facts.consumes.iter().find(|row| {
            row.ordinal == source && row.point == registration.point && row.projection.is_empty()
        }) else {
            continue;
        };
        let Availability::Present(window) = &consume.projected else { continue };
        if registration.window
            != (Window::UseDef {
                use_start: window.use_start,
                use_end: window.use_end,
                def_start: window.def_start,
                def_end: window.def_end,
            })
            || window.use_end != window.use_start + 1
        {
            continue;
        }
        let definition: Vec<_> = occurrences
            .iter()
            .filter(|row| {
                row.syntax.destination.local == registration.proxy_local
                    && row.syntax.destination.projection.is_empty()
            })
            .collect();
        if definition.len() != 1 {
            continue;
        }
        let definition = definition[0];
        if registration.point.block != Some(definition.site.block)
            || registration.point.statement != Some(definition.site.statement)
        {
            continue;
        }
        let Expression::Value {
            operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
        } = &definition.syntax.expression
        else {
            continue;
        };
        if place.local != consume.local || !place.projection.is_empty() {
            continue;
        }
        let key = format!("{function}::_{}@d0", registration.proxy_local);
        let users: Vec<_> = occurrences
            .iter()
            .filter(|row| {
                row.arguments
                    .iter()
                    .any(|arg| matches!(arg, OriginAvailability::Present(value) if value == &key))
            })
            .collect();
        if users.len() != 1 {
            continue;
        }
        let call = users[0];
        if !matches!(&call.callee, Some(SourceCallee::ForeignC(name)) if name == "free")
            || call.site.block != definition.site.block
            || call.site.statement <= definition.site.statement
            || !facts.equations.iter().any(|row| {
                row.operation == "sink"
                    && row.variables == [window.use_start]
                    && row.point.construction == construction
                    && row.point.function.as_deref() == Some(function)
                    && row.point.block == Some(call.site.block)
                    && row.point.statement == Some(call.site.statement)
            })
        {
            continue;
        }
        if facts
            .call_arg_registrations
            .iter()
            .filter(|row| {
                row.point.construction == construction
                    && row.point.function.as_deref() == Some(function)
                    && row.proxy_local == registration.proxy_local
            })
            .count()
            != 1
        {
            continue;
        }
        result.insert(registration.proxy_local, source);
    }
    result
}

pub(crate) fn plan(
    facts: &Facts,
    graph: &CandidateGraph,
    matched: &MatchedTransport,
    origins: &ValueOrigins,
) -> (Vec<Grant>, Vec<Hold>) {
    let mut grants = Vec::new();
    let mut holds = Vec::new();
    let carriers = origins.no_ref_carriers(facts);
    for roster in &facts.body_rosters {
        let Some(function) = &roster.point.function else { continue };
        let construction = roster.point.construction;
        let scope = |point: &super::super::ownership_evidence::Point| {
            point.construction == construction && point.function.as_ref() == Some(function)
        };
        let mut reasons = BTreeSet::new();
        let proxies = free_proxies(facts, construction, function);
        if super::coverage::validate_returns(facts, construction, function).is_err() {
            reasons.insert(HoldReason::Coverage);
        }
        let terminals: Vec<_> = facts
            .terminals
            .iter()
            .filter(|row| scope(&row.point))
            .cloned()
            .collect();
        let boundaries: Vec<_> = facts
            .boundary_substitutions
            .iter()
            .filter(|row| scope(&row.point))
            .cloned()
            .collect();
        let equations: Vec<_> = facts
            .equations
            .iter()
            .filter(|row| scope(&row.point))
            .cloned()
            .collect();
        let consumes: Vec<_> = facts
            .consumes
            .iter()
            .filter(|row| scope(&row.point))
            .cloned()
            .collect();
        if super::super::ownership_occurrence::validate(function, &consumes, &equations).is_err() {
            reasons.insert(HoldReason::Coverage);
        }
        if super::super::ownership_occurrence::validate_terminal_links(
            &terminals,
            &boundaries,
            &equations,
        )
        .is_err()
        {
            reasons.insert(HoldReason::ZeroLaw);
        }
        // A total source-order for this first fragment; no branch selection,
        // induction, or existential-path union can supply its grant proof.
        let blocks: BTreeMap<_, _> = roster
            .blocks
            .iter()
            .filter(|block| block.reachable)
            .map(|block| (block.block, block))
            .collect();
        let mut order = BTreeMap::new();
        let mut next = Some(0);
        while let Some(block) = next {
            if order.insert(block, order.len()).is_some() {
                reasons.insert(HoldReason::BranchOrLoop);
                break;
            }
            let Some(row) = blocks.get(&block) else {
                reasons.insert(HoldReason::Coverage);
                break;
            };
            if row.successors.len() > 1 {
                reasons.insert(HoldReason::BranchOrLoop);
                break;
            }
            next = row.successors.first().copied();
        }
        if order.len() != blocks.len() || !roster.phis.is_empty() {
            reasons.insert(HoldReason::BranchOrLoop);
        }
        let heads: Vec<_> = facts
            .raw_pointer_heads
            .iter()
            .filter(|head| &head.function == function)
            .collect();
        if heads
            .iter()
            .any(|head| head.local > 0 && head.local as usize <= roster.argument_count)
        {
            reasons.insert(HoldReason::InputContract);
        }
        for consume in facts.consumes.iter().filter(|row| scope(&row.point)) {
            if consume.projection.is_empty()
                && (facts
                    .unit_locals
                    .contains(&(function.clone(), consume.local))
                    || proxies.contains_key(&consume.local))
            {
                continue;
            }
            if !matches!(&consume.pointer_paths, Availability::Present(paths) if paths.iter().all(Vec::is_empty))
            {
                reasons.insert(HoldReason::FieldOrReference);
            }
        }
        for equation in facts.equations.iter().filter(|row| scope(&row.point)) {
            if equation.validate().is_err() {
                reasons.insert(HoldReason::Coverage);
            }
            if equation.operation.starts_with("guarded-") {
                reasons.insert(HoldReason::CopyOrReaderRole);
            }
            if let Some(transfer) = &equation.transfer {
                if !matches!(transfer.source, Availability::Present(_))
                    || !matches!(transfer.destination, Availability::Present(_))
                {
                    reasons.insert(HoldReason::Coverage);
                }
                let at = |row: &&super::super::ownership_evidence::Equation| {
                    row.point == equation.point && row.transfer.as_ref() == Some(transfer)
                };
                let rows: Vec<_> = facts.equations.iter().filter(at).collect();
                let zero = |var| {
                    rows.iter().any(|row| {
                        row.operation == "assume"
                            && row.value == Some(false)
                            && row.variables == [var]
                    })
                };
                let law = if transfer.by_move {
                    rows.iter().any(|row| {
                        row.operation == "equal"
                            && row.variables == [transfer.destination_def, transfer.source_use]
                    }) && zero(transfer.source_def)
                } else {
                    rows.iter().any(|row| {
                        row.operation == "linear"
                            && row.variables
                                == [
                                    transfer.destination_def,
                                    transfer.source_def,
                                    transfer.source_use,
                                ]
                    })
                };
                if !zero(transfer.destination_use) || !law {
                    reasons.insert(HoldReason::Coverage);
                }
            }
        }
        let sources: Vec<_> = graph
            .sources
            .iter()
            .filter(|row| {
                row.node.construction == construction && &row.endpoint.function == function
            })
            .collect();
        let sinks: Vec<_> = graph
            .sinks
            .iter()
            .filter(|row| {
                row.node.construction == construction && &row.endpoint.function == function
            })
            .collect();
        let exits: Vec<_> = graph
            .exits
            .iter()
            .filter(|exit| {
                exit.node.construction == construction
                    && facts
                        .terminals
                        .iter()
                        .any(|row| scope(&row.point) && row.ordinal == exit.terminal_ordinal)
            })
            .collect();
        if sources.len() != 1 || sinks.len() + exits.len() != 1 {
            reasons.insert(HoldReason::TerminalDisposition);
        }
        let occurrences = facts.source_occurrences.get(function);
        if occurrences.is_none() {
            reasons.insert(HoldReason::Coverage);
        }
        for occurrence in occurrences.into_iter().flatten() {
            if !order.contains_key(&occurrence.site.block) {
                continue;
            }
            if matches!(
                occurrence.syntax.expression,
                Expression::Borrow { .. }
                    | Expression::RawAddress { .. }
                    | Expression::Aggregate { .. }
                    | Expression::Unrepresented { .. }
                    | Expression::CopyForDeref { .. }
            ) {
                reasons.insert(HoldReason::CopyOrReaderRole);
            }
            if let Some(callee) = &occurrence.callee {
                let expected = match callee {
                    SourceCallee::ForeignC(name) if name == "malloc" => Some("source"),
                    SourceCallee::ForeignC(name) if name == "free" => Some("sink"),
                    _ => None,
                };
                if !expected.is_some_and(|operation| {
                    facts.equations.iter().any(|row| {
                        scope(&row.point)
                            && row.operation == operation
                            && row.point.block == Some(occurrence.site.block)
                            && row.point.statement == Some(occurrence.site.statement)
                            && row
                                .endpoint
                                .as_ref()
                                .is_some_and(|endpoint| endpoint.outcome.is_none())
                    })
                }) {
                    reasons.insert(HoldReason::CallOrOutcome);
                }
            }
            if let OriginAvailability::Present(key) = &occurrence.destination {
                if occurrence.syntax.destination.projection.is_empty()
                    && proxies.contains_key(&occurrence.syntax.destination.local)
                {
                    continue;
                }
                if !heads.iter().any(|head| &head.slot_key == key)
                    || !occurrence.syntax.destination.projection.is_empty()
                {
                    reasons.insert(HoldReason::FieldOrReference);
                    continue;
                }
                let definitions: Vec<_> = facts
                    .consumes
                    .iter()
                    .filter(|row| {
                        scope(&row.point)
                            && row.point.block == Some(occurrence.site.block)
                            && row.point.statement == Some(occurrence.site.statement)
                            && row.local == occurrence.syntax.destination.local
                            && row.projection.is_empty()
                    })
                    .collect();
                if definitions.len() != 1 {
                    reasons.insert(HoldReason::Coverage);
                    continue;
                }
                let Availability::Present(window) = &definitions[0].projected else {
                    reasons.insert(HoldReason::Coverage);
                    continue;
                };
                let atoms = origins.at(Node {
                    construction,
                    var: window.def_start,
                });
                if atoms.is_empty()
                    || !atoms.iter().all(|atom| {
                        matches!(
                            atom,
                            super::value_origins::OriginAtom::Fresh(_)
                                | super::value_origins::OriginAtom::Null
                        )
                    })
                {
                    reasons.insert(HoldReason::Origin);
                }
            }
        }
        if !reasons.is_empty() {
            holds.push(Hold {
                construction,
                function: function.clone(),
                reasons,
            });
            continue;
        }
        let source = sources[0];
        let (terminal, target) = if let Some(sink) = sinks.first() {
            // A source's retirement is its final recorded operation in this
            // fragment. Even copying/returning a dangling alias cannot supply
            // a second owning output after that original C free.
            let point = facts
                .equations
                .iter()
                .find(|row| scope(&row.point) && row.ordinal == sink.equation.ordinal)
                .unwrap();
            let retired = (
                order[&point.point.block.unwrap()],
                point.point.statement.unwrap(),
            );
            if occurrences.into_iter().flatten().any(|row| {
                order.get(&row.site.block).is_some_and(|&rank| {
                    (rank, row.site.statement) > retired
                        && matches!(row.destination, OriginAvailability::Present(_))
                })
            }) {
                reasons.insert(HoldReason::TerminalDisposition);
            }
            (sink.node, TerminalTarget::Free(sink.equation))
        } else {
            let exit = exits[0];
            if exit.role_certification_pending || !exit.path.is_empty() {
                reasons.insert(HoldReason::TerminalDisposition);
            }
            (
                exit.node,
                TerminalTarget::Output {
                    node: exit.node,
                    ordinal: exit.terminal_ordinal,
                },
            )
        };
        let mut edges: BTreeMap<Node, BTreeSet<Node>> = BTreeMap::new();
        for edge in &graph.edges {
            let local = match edge.evidence {
                Evidence::Frame { equation, .. }
                | Evidence::Phi(equation)
                | Evidence::Transfer(equation)
                | Evidence::TraversalFrame(equation)
                | Evidence::ReferenceEffect(equation) => facts.equations.iter().any(|row| {
                    scope(&row.point)
                        && row.ordinal == equation.ordinal
                        && equation.construction == construction
                }),
                Evidence::Boundary {
                    construction: c,
                    ordinal,
                    ..
                } => {
                    c == construction
                        && facts.boundary_substitutions.iter().any(|row| {
                            scope(&row.point)
                                && row.ordinal == ordinal
                                && row.role == super::super::ownership_boundary::Role::ExitReturn
                        })
                }
            };
            if local
                && edge.guard.is_none()
                && matches!(edge.rule, Rule::Frame | Rule::Return | Rule::Copy)
            {
                edges.entry(edge.from).or_default().insert(edge.to);
            }
        }
        // Backward demand selects the successor that can reach this exact
        // terminal. May-reach fan-out alone never licenses both copy partners.
        let mut reaches = BTreeSet::from([terminal]);
        loop {
            let before = reaches.len();
            for (&from, successors) in &edges {
                if successors.iter().any(|to| reaches.contains(to)) {
                    reaches.insert(from);
                }
            }
            if before == reaches.len() {
                break;
            }
        }
        for successors in edges.values_mut() {
            successors.retain(|to| reaches.contains(to));
        }
        let mut route = vec![source.node];
        while *route.last().unwrap() != terminal {
            let Some(out) = edges
                .get(route.last().unwrap())
                .filter(|out| out.len() == 1)
            else {
                reasons.insert(HoldReason::UniqueRoute);
                break;
            };
            let next = *out.first().unwrap();
            if route.contains(&next) {
                reasons.insert(HoldReason::UniqueRoute);
                break;
            }
            route.push(next);
        }
        for equation in facts
            .equations
            .iter()
            .filter(|row| scope(&row.point) && row.operation == "linear")
        {
            let Some(split) = &equation.transfer else {
                reasons.insert(HoldReason::Coverage);
                continue;
            };
            let node = |var| Node { construction, var };
            if route.contains(&node(split.source_use))
                && route.contains(&node(split.destination_def))
                    == route.contains(&node(split.source_def))
            {
                reasons.insert(HoldReason::UniqueRoute);
            }
        }
        let mut checked = Vec::new();
        for carrier in &carriers {
            if !heads.iter().any(|head| head.slot_key == carrier.slot_key) {
                continue;
            }
            for &node in carrier.values.iter().filter(|node| route.contains(node)) {
                let meets: Vec<_> = matched.meets_for(node).into_iter().filter(|meet|
                    meet.source.endpoint == source.equation && meet.terminal.target == target
                    && matches!(&meet.source.lineage, SourceLineage::Exact(calls) if calls.is_empty())
                    && matches!(&meet.terminal.lineage, SourceLineage::Exact(calls) if calls.is_empty())).collect();
                if meets.len() != 1 {
                    reasons.insert(HoldReason::UniqueRoute);
                    continue;
                }
                checked.push(Grant {
                    function: function.clone(),
                    slot_key: carrier.slot_key.clone(),
                    carrier: node,
                    meet: meets[0].clone(),
                    route: route.clone(),
                    discharged_gates: HardGate::ALL.to_vec(),
                });
            }
        }
        if checked.is_empty() {
            reasons.insert(HoldReason::KindJoin);
        }
        if reasons.is_empty() {
            grants.extend(checked);
        } else {
            holds.push(Hold {
                construction,
                function: function.clone(),
                reasons,
            });
        }
    }
    (grants, holds)
}
