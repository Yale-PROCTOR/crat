//! Closed scalar responsibility routes. Broader field/call/reader roles remain
//! pending F/C. Eligibility is derived from complete evidence, never a free
//! solver Boolean. The accepted SSA laws are retained without modification.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

use super::{
    super::{
        origin_evidence::{OriginAvailability, SourceCallee},
        ownership_access::Expression,
        ownership_boundary::{CallArgRegistration, Substitution},
        ownership_evidence::{Equation, Point},
        ownership_occurrence::{Availability, Consumption, Terminal, Transfer},
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
fn free_proxies(
    facts: &Facts,
    tables: &Tables<'_>,
    construction: u32,
    function: &str,
) -> BTreeMap<u32, usize> {
    use super::super::{ownership_access::OperandSyntax, ownership_boundary::Window};
    let mut result = BTreeMap::new();
    let Some(occurrences) = facts.source_occurrences.get(function) else { return result };
    // Relay main/388 walls 3+4 (G1): every table read below is the scope's own group; a row of
    // another scope never passed these predicates (`registration.point` names this scope).
    let registrations = scoped(&tables.registrations, construction, function);
    let consumes = scoped(&tables.consumes, construction, function);
    let equations = scoped(&tables.equations, construction, function);
    for registration in registrations {
        if registration.by_reference {
            continue;
        }
        let Availability::Present(source) = registration.source_occurrence else { continue };
        let Some(consume) = consumes.iter().find(|row| {
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
            || !equations.iter().any(|row| {
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
        if registrations
            .iter()
            .filter(|row| row.proxy_local == registration.proxy_local)
            .count()
            != 1
        {
            continue;
        }
        result.insert(registration.proxy_local, source);
    }
    result
}

/// Relay main/388 walls 3+4 (R1363-1), G1: a fact table's rows grouped once by (construction,
/// function), in table order. A row whose point names no function is in no group: the per-roster
/// filters this replaces (`point.construction == c && point.function == Some(f)`) never kept one.
pub(crate) type Scoped<'f, T> = FxHashMap<&'f str, FxHashMap<u32, Vec<&'f T>>>;

pub(crate) fn by_scope<'f, T>(rows: &'f [T], point: impl Fn(&'f T) -> &'f Point) -> Scoped<'f, T> {
    let mut groups: Scoped<'f, T> = FxHashMap::default();
    for row in rows {
        let point = point(row);
        if let Some(function) = point.function.as_deref() {
            groups
                .entry(function)
                .or_default()
                .entry(point.construction)
                .or_default()
                .push(row);
        }
    }
    groups
}

/// One scope's rows, in table order; empty when it has none.
pub(crate) fn scoped<'s, 'f, T>(
    groups: &'s Scoped<'f, T>,
    construction: u32,
    function: &str,
) -> &'s [&'f T] {
    groups
        .get(function)
        .and_then(|by_construction| by_construction.get(&construction))
        .map(Vec::as_slice)
        .unwrap_or(&[])
}

/// The tables `plan` reads per roster, grouped once per call (G1).
pub(crate) struct Tables<'f> {
    terminals: Scoped<'f, Terminal>,
    boundaries: Scoped<'f, Substitution>,
    equations: Scoped<'f, Equation>,
    consumes: Scoped<'f, Consumption>,
    registrations: Scoped<'f, CallArgRegistration>,
    heads: FxHashMap<&'f str, Vec<&'f super::value_origins::RawHead>>,
}

impl<'f> Tables<'f> {
    pub(crate) fn build(facts: &'f Facts) -> Self {
        let mut heads: FxHashMap<&str, Vec<_>> = FxHashMap::default();
        for head in &facts.raw_pointer_heads {
            heads.entry(head.function.as_str()).or_default().push(head);
        }
        Self {
            terminals: by_scope(&facts.terminals, |row| &row.point),
            boundaries: by_scope(&facts.boundary_substitutions, |row| &row.point),
            equations: by_scope(&facts.equations, |row| &row.point),
            consumes: by_scope(&facts.consumes, |row| &row.point),
            registrations: by_scope(&facts.call_arg_registrations, |row| &row.point),
            heads,
        }
    }
}

/// G2: the rows recorded at `equation`'s point for its `transfer`. Every such row has the point of
/// an equation of this scope, so the scope's own equations hold all of them, in table order.
fn transfer_rows<'f>(
    scoped_equations: &[&'f Equation],
    equation: &Equation,
    transfer: &Transfer,
) -> Vec<&'f Equation> {
    scoped_equations
        .iter()
        .copied()
        .filter(|row| row.point == equation.point && row.transfer.as_ref() == Some(transfer))
        .collect()
}

/// The scan [`transfer_rows`] replaces (its oracle).
#[cfg(test)]
pub(super) fn transfer_rows_by_scan<'f>(
    facts: &'f Facts,
    equation: &Equation,
    transfer: &Transfer,
) -> Vec<&'f Equation> {
    facts
        .equations
        .iter()
        .filter(|row| row.point == equation.point && row.transfer.as_ref() == Some(transfer))
        .collect()
}

/// G3: whether the scope records `operation` with an outcome-free endpoint at a site.
fn endpoint_row(
    scoped_equations: &[&Equation],
    operation: &str,
    block: u32,
    statement: usize,
) -> bool {
    scoped_equations.iter().any(|row| {
        row.operation == operation
            && row.point.block == Some(block)
            && row.point.statement == Some(statement)
            && row
                .endpoint
                .as_ref()
                .is_some_and(|endpoint| endpoint.outcome.is_none())
    })
}

/// G3: the scope's unprojected consume rows of `local` at a site, in table order.
fn definitions<'f>(
    scoped_consumes: &[&'f Consumption],
    block: u32,
    statement: usize,
    local: u32,
) -> Vec<&'f Consumption> {
    scoped_consumes
        .iter()
        .copied()
        .filter(|row| {
            row.point.block == Some(block)
                && row.point.statement == Some(statement)
                && row.local == local
                && row.projection.is_empty()
        })
        .collect()
}

/// The scans [`endpoint_row`] and [`definitions`] replace (their oracles).
#[cfg(test)]
pub(super) fn endpoint_row_by_scan(
    facts: &Facts,
    construction: u32,
    function: &str,
    operation: &str,
    block: u32,
    statement: usize,
) -> bool {
    facts.equations.iter().any(|row| {
        row.point.construction == construction
            && row.point.function.as_deref() == Some(function)
            && row.operation == operation
            && row.point.block == Some(block)
            && row.point.statement == Some(statement)
            && row
                .endpoint
                .as_ref()
                .is_some_and(|endpoint| endpoint.outcome.is_none())
    })
}

#[cfg(test)]
pub(super) fn definitions_by_scan<'f>(
    facts: &'f Facts,
    construction: u32,
    function: &str,
    block: u32,
    statement: usize,
    local: u32,
) -> Vec<&'f Consumption> {
    facts
        .consumes
        .iter()
        .filter(|row| {
            row.point.construction == construction
                && row.point.function.as_deref() == Some(function)
                && row.point.block == Some(block)
                && row.point.statement == Some(statement)
                && row.local == local
                && row.projection.is_empty()
        })
        .collect()
}

/// G4: a roster's local evidence -- the ordinals of its equations and of its exit-return
/// boundary rows -- built once, so the per-edge locality test is a lookup.
struct Locality {
    construction: u32,
    equations: FxHashSet<usize>,
    exits: FxHashSet<usize>,
}

impl Locality {
    fn build(
        construction: u32,
        scoped_equations: &[&Equation],
        scoped_boundaries: &[&Substitution],
    ) -> Self {
        Self {
            construction,
            equations: scoped_equations.iter().map(|row| row.ordinal).collect(),
            exits: scoped_boundaries
                .iter()
                .filter(|row| row.role == super::super::ownership_boundary::Role::ExitReturn)
                .map(|row| row.ordinal)
                .collect(),
        }
    }

    fn local(&self, evidence: &Evidence) -> bool {
        match *evidence {
            Evidence::Frame { equation, .. }
            | Evidence::Phi(equation)
            | Evidence::Transfer(equation)
            | Evidence::TraversalFrame(equation)
            | Evidence::ReferenceEffect(equation) => {
                equation.construction == self.construction
                    && self.equations.contains(&equation.ordinal)
            }
            Evidence::Boundary {
                construction,
                ordinal,
                ..
            } => construction == self.construction && self.exits.contains(&ordinal),
        }
    }
}

/// The scan [`Locality::local`] replaces (its oracle).
#[cfg(test)]
pub(super) fn local_by_scan(
    facts: &Facts,
    evidence: &Evidence,
    construction: u32,
    function: &str,
) -> bool {
    let scope = |point: &Point| {
        point.construction == construction && point.function.as_deref() == Some(function)
    };
    match *evidence {
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
    }
}

/// Relay main/388 walls 3+4 (R1363-1): `plan`'s own cost, per part (log only): the per-roster
/// filters, `free_proxies`, the transfer rows, the occurrences, the per-edge locality.
#[derive(Default)]
struct PlanCost {
    rosters: usize,
    held: usize,
    transfers: usize,
    occurrences: usize,
    edge_rosters: usize,
    filters: std::time::Duration,
    proxies: std::time::Duration,
    transfer_rows: std::time::Duration,
    occurrence_checks: std::time::Duration,
    locality: std::time::Duration,
}

impl PlanCost {
    fn line(&self) -> String {
        format!(
            "rosters={} held={} transfers={} occurrences={} edge_rosters={} filters={:.1}s proxies={:.1}s transfer_rows={:.1}s occurrences_wall={:.1}s locality={:.1}s",
            self.rosters,
            self.held,
            self.transfers,
            self.occurrences,
            self.edge_rosters,
            self.filters.as_secs_f64(),
            self.proxies.as_secs_f64(),
            self.transfer_rows.as_secs_f64(),
            self.occurrence_checks.as_secs_f64(),
            self.locality.as_secs_f64()
        )
    }
}

/// **Relay main/378 (c), R1324-1.** An exit belongs to the functions whose terminal carries its
/// (construction, ordinal): the graph's exits grouped by those functions once, in the graph's
/// order, instead of every terminal scanned for every exit of every function.
pub(crate) fn exits_by_function<'g>(
    facts: &'g Facts,
    graph: &'g CandidateGraph,
) -> BTreeMap<(u32, &'g str), Vec<&'g super::transport::ExitCandidate>> {
    let mut terminal_owners: BTreeMap<(u32, usize), BTreeSet<&str>> = BTreeMap::new();
    for row in &facts.terminals {
        if let Some(function) = row.point.function.as_deref() {
            terminal_owners
                .entry((row.point.construction, row.ordinal))
                .or_default()
                .insert(function);
        }
    }
    let mut exits_of: BTreeMap<(u32, &str), Vec<&super::transport::ExitCandidate>> =
        BTreeMap::new();
    for exit in &graph.exits {
        for owner in terminal_owners
            .get(&(exit.node.construction, exit.terminal_ordinal))
            .into_iter()
            .flatten()
        {
            exits_of
                .entry((exit.node.construction, owner))
                .or_default()
                .push(exit);
        }
    }
    exits_of
}

/// The scan [`exits_by_function`] replaced (378 (c)'s reference): one function's exits.
#[cfg(test)]
pub(crate) fn exits_by_scan<'g>(
    facts: &'g Facts,
    graph: &'g CandidateGraph,
    construction: u32,
    function: &str,
) -> Vec<&'g super::transport::ExitCandidate> {
    graph
        .exits
        .iter()
        .filter(|exit| {
            exit.node.construction == construction
                && facts.terminals.iter().any(|row| {
                    row.point.construction == construction
                        && row.point.function.as_deref() == Some(function)
                        && row.ordinal == exit.terminal_ordinal
                })
        })
        .collect()
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
    let exits_of = exits_by_function(facts, graph);
    // Relay main/388 walls 3+4 (R1363-1): every per-roster read of a whole table reads its scope's
    // group instead (G1-G4); the cost per part is marked (log only).
    let started = std::time::Instant::now();
    let tables = Tables::build(facts);
    let mut cost = PlanCost::default();
    crate::phase_log::sub("grants:tables", "end", || {
        format!(
            "rosters={} equations={} consumes={} edges={} wall={:.1}s",
            facts.body_rosters.len(),
            facts.equations.len(),
            facts.consumes.len(),
            graph.edges.len(),
            started.elapsed().as_secs_f64()
        )
    });
    for roster in &facts.body_rosters {
        let Some(function) = &roster.point.function else { continue };
        let construction = roster.point.construction;
        let scope = |point: &super::super::ownership_evidence::Point| {
            point.construction == construction && point.function.as_ref() == Some(function)
        };
        cost.rosters += 1;
        if cost.rosters % 500 == 0 {
            crate::phase_log::sub("grants:rosters", "tick", || cost.line());
        }
        let scoped_equations = scoped(&tables.equations, construction, function);
        let scoped_consumes = scoped(&tables.consumes, construction, function);
        let scoped_boundaries = scoped(&tables.boundaries, construction, function);
        let mut reasons = BTreeSet::new();
        let started = std::time::Instant::now();
        let proxies = free_proxies(facts, &tables, construction, function);
        cost.proxies += started.elapsed();
        let started = std::time::Instant::now();
        if super::coverage::validate_returns(facts, construction, function).is_err() {
            reasons.insert(HoldReason::Coverage);
        }
        let terminals: Vec<_> = scoped(&tables.terminals, construction, function)
            .iter()
            .map(|row| (*row).clone())
            .collect();
        let boundaries: Vec<_> = scoped_boundaries.iter().map(|row| (*row).clone()).collect();
        let equations: Vec<_> = scoped_equations.iter().map(|row| (*row).clone()).collect();
        let consumes: Vec<_> = scoped_consumes.iter().map(|row| (*row).clone()).collect();
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
        let heads: Vec<_> = tables
            .heads
            .get(function.as_str())
            .into_iter()
            .flatten()
            .copied()
            .collect();
        if heads
            .iter()
            .any(|head| head.local > 0 && head.local as usize <= roster.argument_count)
        {
            reasons.insert(HoldReason::InputContract);
        }
        for consume in scoped_consumes {
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
        cost.filters += started.elapsed();
        let started = std::time::Instant::now();
        for equation in scoped_equations {
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
                cost.transfers += 1;
                let rows = transfer_rows(scoped_equations, equation, transfer);
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
        cost.transfer_rows += started.elapsed();
        let started = std::time::Instant::now();
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
        let exits: Vec<_> = exits_of
            .get(&(construction, function.as_str()))
            .cloned()
            .unwrap_or_default();
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
                    endpoint_row(
                        scoped_equations,
                        operation,
                        occurrence.site.block,
                        occurrence.site.statement,
                    )
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
                let definitions = definitions(
                    scoped_consumes,
                    occurrence.site.block,
                    occurrence.site.statement,
                    occurrence.syntax.destination.local,
                );
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
        cost.occurrence_checks += started.elapsed();
        if !reasons.is_empty() {
            cost.held += 1;
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
            let point = scoped_equations
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
        let started = std::time::Instant::now();
        cost.edge_rosters += 1;
        let locality = Locality::build(construction, scoped_equations, scoped_boundaries);
        let mut edges: BTreeMap<Node, BTreeSet<Node>> = BTreeMap::new();
        for edge in &graph.edges {
            let local = locality.local(&edge.evidence);
            if local
                && edge.guard.is_none()
                && matches!(edge.rule, Rule::Frame | Rule::Return | Rule::Copy)
            {
                edges.entry(edge.from).or_default().insert(edge.to);
            }
        }
        // Backward demand selects the successor that can reach this exact
        // terminal. May-reach branching alone never licenses both copy partners.
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
        cost.locality += started.elapsed();
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
        for equation in scoped_equations
            .iter()
            .filter(|row| row.operation == "linear")
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
                // Relay main/387: a count-based grant -- a marker meet counts as more than one.
                if meets.len() != 1 || meets[0].guards.is_summarized() {
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
    crate::phase_log::sub("grants:rosters", "end", || cost.line());
    (grants, holds)
}

#[cfg(test)]
#[path = "grants_index_tests.rs"]
mod index_tests;
