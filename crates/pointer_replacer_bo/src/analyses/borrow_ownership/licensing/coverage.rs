//! Independent MIR/SSA coverage observations. None is a licensing proof.

use serde::{Deserialize, Serialize};

use super::super::ownership_evidence::Point;

/// The branch a block ends on, as the compiler wrote it. `targets` lists the
/// switch arms in `all_targets` order — every valued arm, then the otherwise
/// arm — so an arm is named by its position in `successors`, and a `bool`
/// discriminant reads as `[(Some(0), false arm), (None, true arm)]`. A switch
/// on anything but a bare local records `discriminant: None` and proves
/// nothing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Switch {
    pub(crate) discriminant: Option<u32>,
    pub(crate) targets: Vec<(Option<u128>, u32)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Block {
    pub(crate) block: u32,
    pub(crate) successors: Vec<u32>,
    pub(crate) reachable: bool,
    pub(crate) return_statement: Option<usize>,
    #[serde(default)]
    pub(crate) switch: Option<Switch>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Consume {
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) local: u32,
    pub(crate) use_ssa: u32,
    pub(crate) def_ssa: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum DefinitionKind {
    Entry,
    Phi,
    Mir,
    ReallocEdge,
    Missing,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Version {
    pub(crate) local: u32,
    pub(crate) ssa: u32,
    pub(crate) variables: Vec<u32>,
    pub(crate) definition: DefinitionKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Phi {
    pub(crate) block: u32,
    pub(crate) local: u32,
    pub(crate) lhs: u32,
    pub(crate) inputs: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PhiEdge {
    pub(crate) point: Point,
    pub(crate) from: u32,
    pub(crate) edge_ordinal: usize,
    pub(crate) to: u32,
    pub(crate) local: u32,
    pub(crate) input_ssa: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ReturnSelection {
    pub(crate) point: Point,
    pub(crate) locals: Vec<(u32, Option<u32>)>,
}

pub(crate) fn record_return_selection(locals: impl Iterator<Item = (u32, Option<u32>)>) {
    let Some(point) = super::super::ownership_evidence::point() else { return };
    let locals = locals.collect();
    super::facts::record(|facts| {
        facts
            .return_selections
            .push(ReturnSelection { point, locals })
    });
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BodyRoster {
    pub(crate) point: Point,
    pub(crate) argument_count: usize,
    pub(crate) return_width: usize,
    pub(crate) blocks: Vec<Block>,
    pub(crate) consumes: Vec<Consume>,
    pub(crate) versions: Vec<Version>,
    pub(crate) phis: Vec<Phi>,
}

/// Snapshot the compiler CFG and renamer tables, not the emitted equations.
/// This preserves alternatives even if an equation producer omits a branch.
pub(crate) fn record_body(
    body: &rustc_middle::mir::Body<'_>,
    summary: &super::super::infer::FnSummary,
    return_width: usize,
) {
    use std::collections::{BTreeSet, VecDeque};

    use rustc_data_structures::graph::Successors;
    use rustc_middle::mir::{START_BLOCK, TerminatorKind};

    use super::super::{ownership_evidence, ssa::consume::Voidable};

    let Some(point) = ownership_evidence::point() else { return };
    let mut reachable = BTreeSet::new();
    let mut pending = VecDeque::from([START_BLOCK]);
    while let Some(block) = pending.pop_front() {
        if reachable.insert(block) {
            pending.extend(body.basic_blocks.successors(block));
        }
    }
    let blocks = body
        .basic_blocks
        .iter_enumerated()
        .map(|(block, data)| Block {
            block: block.as_u32(),
            successors: body
                .basic_blocks
                .successors(block)
                .map(|next| next.as_u32())
                .collect(),
            reachable: reachable.contains(&block),
            return_statement: data
                .terminator
                .as_ref()
                .is_some_and(|terminal| matches!(terminal.kind, TerminatorKind::Return))
                .then_some(data.statements.len()),
            switch: data.terminator.as_ref().and_then(|terminal| {
                let TerminatorKind::SwitchInt { discr, targets } = &terminal.kind else {
                    return None;
                };
                Some(Switch {
                    discriminant: discr
                        .place()
                        .filter(|place| place.projection.is_empty())
                        .map(|place| place.local.as_u32()),
                    targets: targets
                        .iter()
                        .map(|(value, target)| (Some(value), target.as_u32()))
                        .chain([(None, targets.otherwise().as_u32())])
                        .collect(),
                })
            }),
        })
        .collect();
    let mut consumes = Vec::new();
    for (block, _) in body.basic_blocks.iter_enumerated() {
        for (statement, entries) in summary
            .ssa_state
            .consume_chain
            .of_block(block)
            .iter()
            .enumerate()
        {
            for (local, consume) in entries {
                consumes.push(Consume {
                    block: block.as_u32(),
                    statement,
                    local: local.as_u32(),
                    use_ssa: consume.r#use.as_u32(),
                    def_ssa: (!consume.def.is_void()).then_some(consume.def.as_u32()),
                });
            }
        }
    }
    let versions = summary
        .fn_body_sig
        .iter_enumerated()
        .flat_map(|(local, versions)| {
            versions
                .iter_enumerated()
                .map(move |(ssa, variables)| Version {
                    local: local.as_u32(),
                    ssa: ssa.as_u32(),
                    variables: variables.clone().map(|var| var.as_u32()).collect(),
                    definition: match summary
                        .ssa_state
                        .consume_chain
                        .locs
                        .get(local)
                        .and_then(|versions| versions.get(ssa))
                    {
                        Some(super::super::ssa::consume::RichLocation::Entry) => {
                            DefinitionKind::Entry
                        }
                        Some(super::super::ssa::consume::RichLocation::Phi) => DefinitionKind::Phi,
                        Some(super::super::ssa::consume::RichLocation::Mir) => DefinitionKind::Mir,
                        Some(super::super::ssa::consume::RichLocation::ReallocEdge) => {
                            DefinitionKind::ReallocEdge
                        }
                        None => DefinitionKind::Missing,
                    },
                })
        })
        .collect();
    let phis = summary
        .ssa_state
        .join_points
        .data
        .iter_enumerated()
        .flat_map(|(block, nodes)| {
            nodes.iter().map(move |(local, phi)| Phi {
                block: block.as_u32(),
                local: local.as_u32(),
                lhs: phi.lhs.as_u32(),
                inputs: phi.rhs.iter().map(|input| input.as_u32()).collect(),
            })
        })
        .collect();
    super::facts::record(|facts| {
        facts.body_rosters.push(BodyRoster {
            point,
            argument_count: body.arg_count,
            return_width,
            blocks,
            consumes,
            versions,
            phis,
        })
    });
}

/// Record every CFG predecessor before the ownership emitter deduplicates phi
/// SSA inputs. The edge ordinal distinguishes repeated switch successors.
pub(crate) fn record_phi_edge(from: u32, edge_ordinal: usize, to: u32, local: u32, input_ssa: u32) {
    let Some(point) = super::super::ownership_evidence::point() else { return };
    super::facts::record(|facts| {
        facts.phi_edges.push(PhiEdge {
            point,
            from,
            edge_ordinal,
            to,
            local,
            input_ssa,
        })
    });
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CoverageError {
    MissingRoster,
    MissingReturn,
    ReturnVersion,
    PhiInput,
    PhiEquation,
}

/// Structural coverage only; origin admissibility and ownership are separate.
pub(crate) fn validate_returns(
    facts: &super::facts::Facts,
    construction: u32,
    function: &str,
) -> Result<(), Vec<CoverageError>> {
    use std::collections::{BTreeMap, BTreeSet};

    use super::super::ownership_occurrence::Availability;
    let scope = |point: &Point| {
        point.construction == construction && point.function.as_deref() == Some(function)
    };
    let rosters: Vec<_> = facts
        .body_rosters
        .iter()
        .filter(|row| scope(&row.point))
        .collect();
    if rosters.len() != 1 {
        return Err(vec![CoverageError::MissingRoster]);
    }
    let roster = rosters[0];
    let mut errors = Vec::new();
    let versions: BTreeMap<_, _> = roster
        .versions
        .iter()
        .map(|row| ((row.local, row.ssa), &row.variables))
        .collect();
    if versions.len() != roster.versions.len() {
        errors.push(CoverageError::ReturnVersion);
    }
    let returns: BTreeSet<_> = roster
        .blocks
        .iter()
        .filter(|block| block.reachable)
        .filter_map(|block| {
            block
                .return_statement
                .map(|statement| (block.block, statement))
        })
        .collect();
    let terminals: Vec<_> = facts
        .terminals
        .iter()
        .filter(|row| scope(&row.point) && row.local == 0)
        .collect();
    for &(block, statement) in &returns {
        let found: Vec<_> = terminals
            .iter()
            .copied()
            .filter(|row| {
                row.point.block == Some(block)
                    && row.point.statement == Some(statement)
                    && row.role == "return-output"
            })
            .collect();
        if found.len() != 1 {
            errors.push(CoverageError::MissingReturn);
            continue;
        }
        let selected: Vec<_> = facts
            .return_selections
            .iter()
            .filter(|row| {
                scope(&row.point)
                    && row.point.block == Some(block)
                    && row.point.statement == Some(statement)
            })
            .collect();
        if selected.len() != 1 {
            errors.push(CoverageError::ReturnVersion);
            continue;
        }
        let selected_return: Vec<_> = selected[0]
            .locals
            .iter()
            .filter(|(local, _)| *local == 0)
            .collect();
        if selected_return.len() != 1 || selected_return[0].1 != found[0].ssa {
            errors.push(CoverageError::ReturnVersion);
        }
        if roster.return_width == 0 {
            continue;
        }
        let terminal = found[0];
        let Some(ssa) = terminal.ssa else {
            errors.push(CoverageError::ReturnVersion);
            continue;
        };
        let Some(expected) = versions.get(&(0, ssa)) else {
            errors.push(CoverageError::ReturnVersion);
            continue;
        };
        let Availability::Present(values) = &terminal.values else {
            errors.push(CoverageError::ReturnVersion);
            continue;
        };
        if expected.len() != roster.return_width
            || values.iter().map(|value| value.var).collect::<Vec<_>>() != **expected
            || values
                .iter()
                .any(|value| matches!(value.path, Availability::Missing(_)))
        {
            errors.push(CoverageError::ReturnVersion);
        }
    }
    for terminal in terminals {
        if !matches!((terminal.point.block, terminal.point.statement), (Some(block), Some(statement))
            if returns.contains(&(block, statement)))
        {
            errors.push(CoverageError::MissingReturn);
        }
    }
    for consume in &roster.consumes {
        if !versions.contains_key(&(consume.local, consume.use_ssa))
            || consume
                .def_ssa
                .is_some_and(|ssa| !versions.contains_key(&(consume.local, ssa)))
        {
            errors.push(CoverageError::ReturnVersion);
        }
    }
    let phi_keys: BTreeSet<_> = roster
        .phis
        .iter()
        .map(|phi| (phi.block, phi.local))
        .collect();
    if phi_keys.len() != roster.phis.len() {
        errors.push(CoverageError::PhiInput);
    }
    for edge in facts.phi_edges.iter().filter(|edge| scope(&edge.point)) {
        if !phi_keys.contains(&(edge.to, edge.local)) {
            errors.push(CoverageError::PhiInput);
        }
    }
    for version in &roster.versions {
        if version.definition == DefinitionKind::Phi
            && roster
                .phis
                .iter()
                .filter(|phi| phi.local == version.local && phi.lhs == version.ssa)
                .count()
                != 1
        {
            errors.push(CoverageError::PhiInput);
        }
    }
    for phi in &roster.phis {
        if !roster
            .blocks
            .iter()
            .any(|block| block.block == phi.block && block.reachable)
        {
            continue;
        }
        let expected_edges: BTreeSet<_> = roster
            .blocks
            .iter()
            .filter(|block| block.reachable)
            .flat_map(|block| {
                block
                    .successors
                    .iter()
                    .enumerate()
                    .filter_map(move |(ordinal, &to)| {
                        (to == phi.block).then_some((block.block, ordinal))
                    })
            })
            .collect();
        let edges: Vec<_> = facts
            .phi_edges
            .iter()
            .filter(|edge| scope(&edge.point) && edge.to == phi.block && edge.local == phi.local)
            .collect();
        let actual_edges: BTreeSet<_> = edges
            .iter()
            .map(|edge| (edge.from, edge.edge_ordinal))
            .collect();
        let inputs: BTreeSet<_> = edges.iter().map(|edge| edge.input_ssa).collect();
        if actual_edges != expected_edges
            || actual_edges.len() != edges.len()
            || inputs != phi.inputs.iter().copied().collect()
        {
            errors.push(CoverageError::PhiInput);
        }
        let Some(lhs) = versions.get(&(phi.local, phi.lhs)) else {
            errors.push(CoverageError::PhiInput);
            continue;
        };
        for &input in &phi.inputs {
            let Some(rhs) = versions.get(&(phi.local, input)) else {
                errors.push(CoverageError::PhiInput);
                continue;
            };
            if lhs.len() != rhs.len() {
                errors.push(CoverageError::PhiInput);
                continue;
            }
            if input == phi.lhs {
                continue;
            }
            for (&left, &right) in lhs.iter().zip(rhs.iter()) {
                if !facts.equations.iter().any(|row| {
                    scope(&row.point)
                        && row.point.phase == "phi"
                        && row.point.block == Some(phi.block)
                        // era-5c: a null-join is the phi relation on an edge
                        // whose incoming component is known null.
                        && matches!(row.operation.as_str(), "equal" | "null-join")
                        && row.variables == [left, right]
                }) {
                    errors.push(CoverageError::PhiEquation);
                }
            }
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}
