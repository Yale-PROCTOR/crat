//! Traversal-return metadata obligation. No call role or ownership law is enabled here.

use serde::{Deserialize, Serialize};

use super::{
    facts::{EquationId, Facts},
    transport::Node,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Proof {
    pub(crate) construction: u32,
    pub(crate) function: String,
    pub(crate) parameter: u32,
    /// Exact return block, statement and selected local-0 SSA version.
    pub(crate) return_versions: Vec<(u32, usize, u32)>,
    pub(crate) returned: Vec<Node>,
    /// Certified field-reader equations on an actual return dependency path.
    pub(crate) readers: Vec<EquationId>,
}

fn one<T>(items: impl IntoIterator<Item = T>) -> Option<T> {
    let mut i = items.into_iter();
    let value = i.next()?;
    i.next().is_none().then_some(value)
}

/// Exhaustive value-origin dependencies over actual local SSA versions. This
/// certifies a readonly traversal candidate, not its call or lifetime contract.
pub(crate) fn classify(facts: &Facts, function: &str) -> Option<Proof> {
    classify_metadata(
        facts,
        function,
        &super::matched::guard_aliases(&facts.guards),
    )
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Rejection {
    Coverage(Vec<super::coverage::CoverageError>),
    Unclassified,
}

pub(crate) fn classify_metadata(
    facts: &Facts,
    function: &str,
    aliases: &std::collections::BTreeMap<EquationId, EquationId>,
) -> Option<Proof> {
    classify_report(facts, function, aliases).ok()
}

pub(crate) fn classify_report(
    facts: &Facts,
    function: &str,
    aliases: &std::collections::BTreeMap<EquationId, EquationId>,
) -> Result<Proof, Rejection> {
    if facts.constructions != 1 {
        return Err(Rejection::Unclassified);
    }
    super::coverage::validate_returns(facts, 0, function).map_err(Rejection::Coverage)?;
    classify_covered_metadata(facts, function, aliases).ok_or(Rejection::Unclassified)
}

// Called only after coverage validation. Tests inspect the remaining obligations
// separately to ensure a coverage killer is not masked by an unrelated denial.
fn classify_covered_metadata(
    facts: &Facts,
    function: &str,
    aliases: &std::collections::BTreeMap<EquationId, EquationId>,
) -> Option<Proof> {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{
        super::{
            ownership_access::{Expression, ImmediateOrigin, OperandSyntax},
            ownership_occurrence::Availability::Present,
        },
        coverage::DefinitionKind,
        readers,
        transport::{CandidateGraph, Rule},
    };
    if facts.constructions != 1 {
        return None;
    }
    let construction = 0;
    let inputs = &facts.reader_inputs;
    let plan = readers::Plan::build(inputs);
    if plan != facts.reader_plan {
        return None;
    }
    let reader = one(plan.functions.iter().filter(|r| r.function == function))?;
    let [parameter] = reader.returned_parameters.as_slice() else { return None };
    let parameter = *parameter;
    let body = one(inputs.bodies.iter().filter(|b| b.function == function))?;
    if !body.complete_operations || &body.occurrences != facts.source_occurrences.get(function)? {
        return None;
    }
    let roster = one(facts.body_rosters.iter().filter(|b| {
        b.point.construction == construction && b.point.function.as_deref() == Some(function)
    }))?;
    let scoped = |p: &super::super::ownership_evidence::Point| {
        p.construction == construction && p.function.as_deref() == Some(function)
    };
    let equations: Vec<_> = facts
        .equations
        .iter()
        .filter(|e| scoped(&e.point))
        .cloned()
        .collect();
    let consumes: Vec<_> = facts
        .consumes
        .iter()
        .filter(|e| scoped(&e.point))
        .cloned()
        .collect();
    let boundaries: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|e| scoped(&e.point))
        .cloned()
        .collect();
    let registrations: Vec<_> = facts
        .call_arg_registrations
        .iter()
        .filter(|e| scoped(&e.point))
        .cloned()
        .collect();
    let all_terminals: Vec<_> = facts
        .terminals
        .iter()
        .filter(|e| scoped(&e.point))
        .cloned()
        .collect();
    super::super::ownership_occurrence::validate(function, &consumes, &equations).ok()?;
    super::super::ownership_occurrence::validate_terminal_links(
        &all_terminals,
        &boundaries,
        &equations,
    )
    .ok()?;
    super::super::ownership_boundary::validate_links(
        function,
        &boundaries,
        &registrations,
        &consumes,
        &equations,
    )
    .ok()?;
    use super::super::ownership_boundary::{Role, Window};
    let entry = one(boundaries
        .iter()
        .filter(|b| b.role == Role::Entry && b.formal_local == Some(parameter)))?;
    let Present(Window::Single { start, end }) = &entry.actual else { return None };
    let initial = one(roster
        .versions
        .iter()
        .filter(|v| v.local == parameter && matches!(v.definition, DefinitionKind::Entry)))?;
    if initial.variables.iter().copied().ne(*start..*end) {
        return None;
    }

    let graph = CandidateGraph::build_metadata(facts, aliases).ok()?;
    let readers = readers::audit_transfers(facts, aliases);
    let terminals: Vec<_> = facts
        .terminals
        .iter()
        .filter(|t| {
            t.point.construction == construction
                && t.point.function.as_deref() == Some(function)
                && t.local == 0
                && t.role == "return-output"
        })
        .collect();
    if terminals.is_empty() {
        return None;
    }
    let mut return_versions = Vec::new();
    let mut returned = BTreeSet::new();
    let mut pending = Vec::new();
    for terminal in terminals {
        let ssa = terminal.ssa?;
        return_versions.push((terminal.point.block?, terminal.point.statement?, ssa));
        let Present(values) = &terminal.values else { return None };
        if values.is_empty() {
            return None;
        }
        returned.extend(values.iter().map(|v| Node {
            construction,
            var: v.var,
        }));
        pending.push((0, ssa));
    }
    type Key = (u32, u32);
    let mut dependencies: BTreeMap<Key, Vec<Key>> = BTreeMap::new();
    let mut roots = BTreeSet::new();
    let mut positive_roots = BTreeSet::new();
    let mut reader_ids = BTreeSet::new();
    while let Some(key @ (local, ssa)) = pending.pop() {
        if dependencies.contains_key(&key) {
            continue;
        }
        let version = one(roster
            .versions
            .iter()
            .filter(|v| v.local == local && v.ssa == ssa))?;
        let mut parents = Vec::new();
        match version.definition {
            DefinitionKind::Entry if local == parameter => {
                roots.insert(key);
                positive_roots.insert(key);
            }
            DefinitionKind::Phi => {
                let phi = one(roster
                    .phis
                    .iter()
                    .filter(|p| p.local == local && p.lhs == ssa))?;
                if phi.inputs.is_empty() {
                    return None;
                }
                parents.extend(phi.inputs.iter().map(|&ssa| (local, ssa)));
            }
            DefinitionKind::Mir => {
                let consumed = one(roster
                    .consumes
                    .iter()
                    .filter(|c| c.local == local && c.def_ssa == Some(ssa)))?;
                let row = one(body.occurrences.iter().filter(|r| {
                    r.site.block == consumed.block && r.site.statement == consumed.statement
                }))?;
                let actual = one(facts.consumes.iter().filter(|c| {
                    c.point.construction == construction
                        && c.point.function.as_deref() == Some(function)
                        && c.point.block == Some(consumed.block)
                        && c.point.statement == Some(consumed.statement)
                        && c.local == local
                        && c.ssa_def == Some(ssa)
                        && c.ssa_use == Some(consumed.use_ssa)
                }))?;
                if row.syntax.destination.local == local {
                    if !row.syntax.destination.projection.is_empty() {
                        return None;
                    }
                    if row.syntax.immediate_origin == ImmediateOrigin::Null {
                        roots.insert(key);
                    } else {
                        let Expression::Value {
                            operand: OperandSyntax::Copy { place } | OperandSyntax::Move { place },
                        } = &row.syntax.expression
                        else {
                            return None;
                        };
                        let source = one(facts.consumes.iter().filter(|c| {
                            c.point == actual.point
                                && c.local == place.local
                                && c.projection == place.projection
                        }))?;
                        let source_ssa = source.ssa_use?;
                        if place.projection.is_empty() {
                            let transfers:Vec<_>=equations.iter().filter(|e|e.point==actual.point&&matches!(e.operation.as_str(),"linear"|"equal"|"guarded-copy")&&e.transfer.as_ref().is_some_and(|t|matches!((&t.source,&t.destination),(Present(src),Present(dst)) if src.consume==source.ordinal&&dst.consume==actual.ordinal))).collect();
                            if transfers.is_empty() {
                                return None;
                            }
                            for equation in transfers {
                                let transfer = equation.transfer.as_ref()?;
                                if !equations.iter().any(|old| {
                                    old.point == actual.point
                                        && old.operation == "assume"
                                        && old.value == Some(false)
                                        && old.variables == [transfer.destination_use]
                                        && old.transfer.as_ref() == Some(transfer)
                                }) {
                                    return None;
                                }
                            }
                        } else {
                            let proof = one(readers.iter().filter(|p| {
                                p.construction == construction
                                    && p.candidate.function == function
                                    && p.candidate.block == row.site.block
                                    && p.candidate.statement == row.site.statement
                                    && p.candidate.source == *place
                                    && p.candidate.destination == row.syntax.destination
                                    && p.candidate.origin_parameter == parameter
                            }))?;
                            let Present(ids) = &proof.coverage else { return None };
                            if ids.is_empty() {
                                return None;
                            }
                            reader_ids.extend(ids.iter().copied());
                        }
                        parents.push((place.local, source_ssa));
                    }
                } else {
                    // The outer pointer value survives a use of a descendant
                    // or a responsibility split. Require its actual head frame.
                    let previous = one(roster
                        .versions
                        .iter()
                        .filter(|v| v.local == local && v.ssa == consumed.use_ssa))?;
                    let from = Node {
                        construction,
                        var: *previous.variables.first()?,
                    };
                    let to = Node {
                        construction,
                        var: *version.variables.first()?,
                    };
                    if !graph.edges.iter().any(|edge| {
                        edge.from == from
                            && edge.to == to
                            && matches!(edge.rule, Rule::Frame | Rule::Copy)
                    }) {
                        return None;
                    }
                    parents.push((local, consumed.use_ssa));
                }
            }
            _ => return None,
        }
        pending.extend(parents.iter().copied());
        dependencies.insert(key, parents);
    }
    // All cyclic components must be anchored in a real entry or explicit None.
    // A cycle with no origin cannot certify itself merely because it is closed.
    let mut anchored = roots;
    loop {
        let before = anchored.len();
        for (&key, parents) in &dependencies {
            if parents.iter().any(|p| anchored.contains(p)) {
                anchored.insert(key);
            }
        }
        if anchored.len() == before {
            break;
        }
    }
    if positive_roots.is_empty()
        || reader_ids.is_empty()
        || dependencies.keys().any(|k| !anchored.contains(k))
    {
        return None;
    }
    return_versions.sort();
    Some(Proof {
        construction,
        function: function.into(),
        parameter,
        return_versions,
        returned: returned.into_iter().collect(),
        readers: reader_ids.into_iter().collect(),
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{
        super::{
            super::ownership_occurrence::Availability, graph_tests::with_facts, matched, readers,
        },
        *,
    };

    const LOOP: &str = r#"
pub struct Node { left: *mut Node, right: *mut Node, value: i32 }
pub unsafe fn minimum(mut node: *mut Node) -> *mut Node {
    while !(*node).left.is_null() { node = (*node).left; }
    node
}
"#;

    #[test]
    fn c04_traversal_return_records_exact_return_versions_and_reader_occurrences() {
        with_facts(LOOP, |facts| {
            let proof = classify(facts, "minimum")
                .expect("zero-iteration input and certified descendant returns need one contract");
            assert_eq!(proof.function, "minimum");
            assert_eq!(proof.parameter, 1);
            let terminals: Vec<_> = facts
                .terminals
                .iter()
                .filter(|row| {
                    row.point.construction == proof.construction
                        && row.point.function.as_deref() == Some("minimum")
                        && row.local == 0
                        && row.role == "return-output"
                })
                .collect();
            assert!(!terminals.is_empty());
            let expected_versions: BTreeSet<_> = terminals
                .iter()
                .map(|row| {
                    (
                        row.point.block.unwrap(),
                        row.point.statement.unwrap(),
                        row.ssa.unwrap(),
                    )
                })
                .collect();
            assert_eq!(
                proof
                    .return_versions
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>(),
                expected_versions
            );
            assert_eq!(proof.return_versions.len(), expected_versions.len());
            let expected_nodes: BTreeSet<_> = terminals
                .iter()
                .flat_map(|row| {
                    let Availability::Present(values) = &row.values else {
                        panic!("return coverage missing")
                    };
                    values.iter().map(|value| Node {
                        construction: proof.construction,
                        var: value.var,
                    })
                })
                .collect();
            assert_eq!(
                proof.returned.iter().copied().collect::<BTreeSet<_>>(),
                expected_nodes
            );
            assert_eq!(proof.returned.len(), expected_nodes.len());
            let aliases = matched::guard_aliases(&facts.guards);
            let certified: BTreeSet<_> = readers::audit_transfers(facts, &aliases)
                .into_iter()
                .filter(|row| {
                    row.construction == proof.construction
                        && row.candidate.function == "minimum"
                        && row.candidate.origin_parameter == 1
                })
                .flat_map(|row| match row.coverage {
                    Availability::Present(ids) => ids,
                    Availability::Missing(_) => vec![],
                })
                .collect();
            assert!(
                !proof.readers.is_empty(),
                "identity return is not a traversal contract"
            );
            assert_eq!(
                proof.readers.iter().copied().collect::<BTreeSet<_>>().len(),
                proof.readers.len()
            );
            for reader in &proof.readers {
                assert!(
                    certified.contains(reader),
                    "return reader must carry its exact certified occurrence: {reader:?}"
                );
            }
            assert!(
                facts
                    .body_rosters
                    .iter()
                    .any(|row| row.point.function.as_deref() == Some("minimum")
                        && !row.phis.is_empty()),
                "loop fixture must retain its zero-iteration/backedge join"
            );
        });
    }

    #[test]
    fn c04_traversal_return_holds_identity_discarded_and_mixed_or_opaque_origins() {
        with_facts(
            r#"
unsafe extern "C" { fn opaque() -> *mut Node; }
pub struct Node { left: *mut Node }
pub unsafe fn identity(node: *mut Node) -> *mut Node { node }
pub unsafe fn discarded(node: *mut Node) -> *mut Node {
    let child = (*node).left;
    let _present = !child.is_null();
    node
}
pub unsafe fn mixed(mut node: *mut Node, other: *mut Node, choose: bool) -> *mut Node {
    while !(*node).left.is_null() { node = (*node).left; }
    if choose { node } else { other }
}
pub unsafe fn unknown(mut node: *mut Node, choose: bool) -> *mut Node {
    while !(*node).left.is_null() { node = (*node).left; }
    if choose { node } else { opaque() }
}
"#,
            |facts| {
                assert!(
                    facts
                        .reader_plan
                        .candidates
                        .iter()
                        .any(|row| row.function == "discarded"),
                    "discarded-read control needs an actual field-reader candidate"
                );
                for function in ["identity", "discarded", "mixed", "unknown"] {
                    assert!(
                        classify(facts, function).is_none(),
                        "{function} cannot force an owning-capable return into a borrow role"
                    );
                }
            },
        );
    }

    #[test]
    fn c04_traversal_return_rejects_omitted_phi_alternative() {
        with_facts(LOOP, |facts| {
            let proof =
                classify(facts, "minimum").expect("uncorrupted loop is the positive control");
            let mut missing = facts.clone();
            let roster = missing
                .body_rosters
                .iter_mut()
                .find(|row| {
                    row.point.construction == proof.construction
                        && row.point.function.as_deref() == Some("minimum")
                })
                .unwrap();
            let phi = roster
                .phis
                .iter_mut()
                .find(|phi| phi.inputs.len() > 1)
                .expect("actual zero-iteration/backedge alternatives");
            let removed = phi.inputs.pop().unwrap();
            let (block, local, lhs) = (phi.block, phi.local, phi.lhs);
            assert!(
                classify(&missing, "minimum").is_none(),
                "missing phi alternative must invalidate the return contract: construction={}, block={}, local={}, lhs={}, removed={removed}",
                proof.construction,
                block,
                local,
                lhs
            );
        });
    }

    #[test]
    fn c04_traversal_return_rejects_omitted_selected_return() {
        with_facts(LOOP, |facts| {
            let proof =
                classify(facts, "minimum").expect("uncorrupted loop is the positive control");
            let mut missing = facts.clone();
            let index = missing
                .return_selections
                .iter()
                .position(|row| {
                    row.point.construction == proof.construction
                        && row.point.function.as_deref() == Some("minimum")
                })
                .expect("actual selected return occurrence");
            let removed = missing.return_selections.remove(index);
            assert!(
                classify(&missing, "minimum").is_none(),
                "missing return selection must invalidate the return contract: {:?}",
                removed.point
            );
        });
    }
    #[test]
    fn c04_traversal_return_holds_overwritten_traversal_and_keeps_nullable_origin() {
        with_facts(
            r#"
pub struct Node {left:*mut Node}
pub unsafe fn overwritten(node:*mut Node)->*mut Node {
    let original=node;let mut cursor=node;
    while !(*cursor).left.is_null(){cursor=(*cursor).left;}
    cursor=original;cursor
}
pub unsafe fn nullable(mut node:*mut Node,empty:bool)->*mut Node {
    if empty {return 0 as *mut Node;}
    while !(*node).left.is_null(){node=(*node).left;}
    node
}
"#,
            |facts| {
                assert!(
                    classify(facts, "overwritten").is_none(),
                    "a killed traversal does not turn identity return into a borrowed contract"
                );
                let proof = classify(facts, "nullable")
                    .expect("None is an orthogonal return alternative, not Raw origin evidence");
                assert_eq!(proof.parameter, 1);
                assert!(!proof.readers.is_empty());
            },
        );
    }
    #[test]
    fn c04_traversal_return_rejects_missing_parameter_entry() {
        with_facts(LOOP, |facts| {
            let proof = classify(facts, "minimum").unwrap();
            let mut missing = facts.clone();
            missing.boundary_substitutions.retain(|b| {
                !(b.role == super::super::super::ownership_boundary::Role::Entry
                    && b.point.function.as_deref() == Some("minimum"))
            });
            assert!(
                classify(&missing, "minimum").is_none(),
                "parameter entry obligation missing: parameter={}",
                proof.parameter
            );
        });
    }
    #[test]
    fn c04_traversal_return_rejects_missing_copy_old_zero() {
        with_facts(LOOP, |facts| {
            classify(facts, "minimum").unwrap();
            let mut missing = facts.clone();
            let equation=facts.equations.iter().find(|e|e.operation=="assume"&&e.value==Some(false)&&e.transfer.as_ref().is_some_and(|t|matches!(&t.destination,Availability::Present(d) if d.local==0&&t.destination_use==e.variables[0]))).unwrap();
            missing
                .equations
                .retain(|e| !(e.ordinal == equation.ordinal && e.point == equation.point));
            assert!(
                classify(&missing, "minimum").is_none(),
                "return copy old-zero obligation missing: {:?}/{}",
                equation.point,
                equation.ordinal
            );
        });
    }
    #[test]
    fn c04_traversal_return_rejects_missing_local_final_zero() {
        with_facts(LOOP, |facts| {
            classify(facts, "minimum").unwrap();
            let mut missing = facts.clone();
            let terminal = facts
                .terminals
                .iter()
                .find(|t| {
                    t.role == "local-final-zero"
                        && matches!(&t.values,Availability::Present(v) if !v.is_empty())
                })
                .unwrap();
            let Availability::Present(values) = &terminal.values else { unreachable!() };
            let equation = facts
                .equations
                .iter()
                .find(|e| {
                    e.point == terminal.point
                        && e.operation == "assume"
                        && e.value == Some(false)
                        && e.variables == [values[0].var]
                })
                .unwrap();
            missing
                .equations
                .retain(|e| !(e.ordinal == equation.ordinal && e.point == equation.point));
            assert!(
                classify(&missing, "minimum").is_none(),
                "final-zero obligation missing: {:?}/{}",
                equation.point,
                equation.ordinal
            );
        });
    }
    #[test]
    fn c04_traversal_return_snapshot_reconstructs_exact_proof() {
        with_facts(LOOP, |facts| {
            let snapshot = super::super::snapshot::Snapshot::capture(facts, 0).unwrap();
            assert_eq!(snapshot.traversal_returns.len(), 1);
            snapshot.validate().unwrap();
            let decoded: super::super::snapshot::Snapshot =
                serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
            decoded.validate().unwrap();
            let mut omitted = decoded.clone();
            omitted.traversal_returns.clear();
            assert!(omitted.validate().is_err());
            let mut wrong = decoded;
            wrong.traversal_returns[0].readers[0].ordinal += 1;
            assert!(wrong.validate().is_err());
        });
    }
    #[test]
    fn c04_traversal_coverage_killer_zero_iteration_retains_reader_and_typed_reason() {
        const ANCHORED: &str = r#"
pub struct Node {left:*mut Node}
pub unsafe fn minimum(mut node:*mut Node)->*mut Node {
    let original=node;
    while !(*node).left.is_null() {node=(*original).left;}
    node
}
"#;
        with_facts(ANCHORED, |facts| {
            use super::super::coverage::{CoverageError, DefinitionKind};
            let aliases = matched::guard_aliases(&facts.guards);
            let proof = classify_report(facts, "minimum", &aliases)
                .expect("uncorrupted anchored traversal");
            let mut missing = facts.clone();
            let roster = missing
                .body_rosters
                .iter_mut()
                .find(|r| r.point.function.as_deref() == Some("minimum"))
                .unwrap();
            let phi = roster
                .phis
                .iter()
                .find(|p| p.local == proof.parameter && p.inputs.len() > 1)
                .unwrap()
                .clone();
            // Identify the outside predecessor from the independent edge roster,
            // not the ordering or numeric value of an SSA version.
            let entry_blocks: std::collections::BTreeSet<_> = roster
                .blocks
                .iter()
                .filter(|b| b.block == 0)
                .map(|b| b.block)
                .collect();
            let entry_edge = facts
                .phi_edges
                .iter()
                .find(|e| {
                    e.point.function.as_deref() == Some("minimum")
                        && e.to == phi.block
                        && e.local == phi.local
                        && entry_blocks.contains(&e.from)
                })
                .expect("zero-iteration predecessor from entry block");
            let removed = entry_edge.input_ssa;
            assert!(roster.versions.iter().any(|v| v.local == phi.local
                && v.ssa == removed
                && matches!(v.definition, DefinitionKind::Entry | DefinitionKind::Mir)));
            let damaged = roster
                .phis
                .iter_mut()
                .find(|p| p.local == phi.local && p.lhs == phi.lhs)
                .unwrap();
            assert_eq!(damaged.inputs.iter().filter(|&&i| i == removed).count(), 1);
            damaged.inputs.retain(|&i| i != removed);
            let remaining=classify_covered_metadata(&missing,"minimum",&aliases).expect("coverage omission must retain all other obligations, parameter anchor and return-reaching reader");
            assert!(!remaining.readers.is_empty());
            assert_eq!(remaining.return_versions, proof.return_versions);
            let expected =
                super::super::coverage::validate_returns(&missing, 0, "minimum").unwrap_err();
            assert!(expected.contains(&CoverageError::PhiInput));
            let actual = classify_report(&missing, "minimum", &aliases);
            assert_eq!(
                actual,
                Err(Rejection::Coverage(expected)),
                "R279 typed coverage rejection required: function=minimum, phi=({},{},{}), removed={}, retained_readers={:?}",
                phi.block,
                phi.local,
                phi.lhs,
                removed,
                remaining.readers
            );
        });
    }
}
