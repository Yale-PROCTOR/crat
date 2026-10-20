//! T11 REDs over real construction facts; no solver or fixture execution.

use std::collections::BTreeSet;

use super::{
    super::ownership_boundary::{Role, Substitution, Variables},
    facts::{EquationId, Facts},
    graph_tests::with_facts,
    matched::{CallKey, MatchedTransport, SourceInstance, SourceLineage, TerminalTarget},
    transport::Node,
};

fn receivers<'a>(facts: &'a Facts, callee: &str) -> Vec<(&'a Substitution, Node)> {
    let mut rows: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|row| {
            row.role == Role::ReturnReceiver
                && row.point.function.as_deref() == Some("run")
                && row.callee.as_deref() == Some(callee)
        })
        .map(|row| {
            assert_eq!(row.matched.len(), 1, "fixture has one pointer component");
            let Variables::UseDef { def_var, .. } = row.matched[0].actual else {
                panic!("actual receiver def")
            };
            (
                row,
                Node {
                    construction: row.point.construction,
                    var: def_var,
                },
            )
        })
        .collect();
    // Both fixtures are straight-line: retain their two concrete source call
    // occurrences, rather than selecting a receiver by a numeric Var guess.
    rows.sort_by_key(|(row, _)| (row.point.block.unwrap(), row.point.statement.unwrap()));
    rows
}

fn call_key(row: &Substitution) -> CallKey {
    CallKey {
        construction: row.point.construction,
        caller: row.point.function.clone().unwrap(),
        block: row.point.block.unwrap(),
        statement: row.point.statement.unwrap(),
        callee: row.callee.clone().unwrap(),
    }
}

#[test]
fn t11_reused_identity_signature_cannot_send_heap_origin_to_stack_receiver() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn id(p: *mut i32) -> *mut i32 { p }
pub unsafe fn run() {
    let heap = malloc(4);
    let heap_result = id(heap);
    let mut stack = 0;
    let stack_pointer = &mut stack as *mut i32;
    let stack_result = id(stack_pointer);
    free(heap_result);
    *stack_result = 1;
}
"#,
        |facts| {
            let transport = MatchedTransport::build(facts);
            let calls = receivers(facts, "id");
            assert_eq!(calls.len(), 2);
            assert_ne!(call_key(calls[0].0), call_key(calls[1].0));
            let source = facts
                .equations
                .iter()
                .find(|row| {
                    row.operation == "source" && row.point.function.as_deref() == Some("run")
                })
                .expect("actual caller allocation");
            let sink = facts
                .equations
                .iter()
                .find(|row| row.operation == "sink" && row.point.function.as_deref() == Some("run"))
                .expect("actual heap-result free");
            let source_node = Node {
                construction: source.point.construction,
                var: source.variables[0],
            };
            let sink_node = Node {
                construction: sink.point.construction,
                var: sink.variables[0],
            };
            assert!(
                transport.reaches(source_node, calls[0].1),
                "heap input returns through its own id call"
            );
            assert!(
                transport.reaches(source_node, sink_node),
                "the heap result reaches its preserved free"
            );
            assert!(
                !transport.reaches(source_node, calls[1].1),
                "shared id signature Vars do not join different call applications"
            );
        },
    );
}

#[test]
fn t11_two_factory_receivers_keep_distinct_static_source_applications() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make() -> *mut i32 { let p = malloc(4); p }
pub unsafe fn run() -> *mut i32 {
    let first = make();
    let second = make();
    free(first);
    second
}
"#,
        |facts| {
            let transport = MatchedTransport::build(facts);
            let calls = receivers(facts, "make");
            assert_eq!(calls.len(), 2);
            let source = facts
                .equations
                .iter()
                .find(|row| {
                    row.operation == "source" && row.point.function.as_deref() == Some("make")
                })
                .expect("one actual allocator site inside make");
            let endpoint = EquationId {
                construction: source.point.construction,
                ordinal: source.ordinal,
            };
            let first = SourceInstance {
                endpoint,
                lineage: SourceLineage::Exact(vec![call_key(calls[0].0)]),
            };
            let second = SourceInstance {
                endpoint,
                lineage: SourceLineage::Exact(vec![call_key(calls[1].0)]),
            };
            assert_ne!(
                first, second,
                "applications distinguish the two static calls"
            );
            assert_eq!(
                transport.sources_for(calls[0].1),
                BTreeSet::from([first.clone()])
            );
            assert_eq!(
                transport.sources_for(calls[1].1),
                BTreeSet::from([second.clone()])
            );
            let sink = facts
                .equations
                .iter()
                .find(|row| row.operation == "sink" && row.point.function.as_deref() == Some("run"))
                .expect("only the first receiver is freed");
            let sink_node = Node {
                construction: sink.point.construction,
                var: sink.variables[0],
            };
            assert_eq!(transport.sources_for(sink_node), BTreeSet::from([first]));
            assert!(
                !transport.reaches(calls[1].1, sink_node),
                "the second receiver has no path to the first receiver's free"
            );
        },
    );
}

#[test]
fn t11_nested_factory_outputs_preserve_their_distinct_inner_applications() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make() -> *mut i32 { malloc(4) }
pub unsafe fn pair(a: *mut *mut i32, b: *mut *mut i32) {
    *a = make();
    *b = make();
}
pub unsafe fn run() -> *mut i32 {
    let mut a = 0 as *mut i32;
    let mut b = 0 as *mut i32;
    pair(&raw mut a, &raw mut b);
    free(a);
    b
}
"#,
        |facts| {
            let transport = MatchedTransport::build(facts);
            let mut outputs = Vec::new();
            for argument in [0, 1] {
                let row = facts
                    .boundary_substitutions
                    .iter()
                    .find(|row| {
                        row.role == Role::CallArgument
                            && row.point.function.as_deref() == Some("run")
                            && row.callee.as_deref() == Some("pair")
                            && row.argument_index == Some(argument)
                    })
                    .expect("one exact outer-call argument occurrence");
                assert_eq!(row.matched.len(), 1);
                let Variables::UseDef { def_var, .. } = row.matched[0].actual else {
                    panic!("caller output def")
                };
                outputs.push(Node {
                    construction: row.point.construction,
                    var: def_var,
                });
            }
            let first = transport.sources_for(outputs[0]);
            let second = transport.sources_for(outputs[1]);
            assert_eq!(
                first.len(),
                1,
                "first output has a concrete allocation source"
            );
            assert_eq!(
                second.len(),
                1,
                "second output has a concrete allocation source"
            );
            assert_ne!(
                first, second,
                "one outer call must not erase two distinct inner allocation applications"
            );
            let (SourceLineage::Exact(first_calls), SourceLineage::Exact(second_calls)) = (
                &first.first().unwrap().lineage,
                &second.first().unwrap().lineage,
            ) else {
                panic!("this acyclic witness needs exact static lineages");
            };
            assert_eq!(first_calls.len(), 2);
            assert_eq!(second_calls.len(), 2);
            assert_eq!(
                first_calls[0], second_calls[0],
                "the outer pair call is shared"
            );
            assert_ne!(
                first_calls[1], second_calls[1],
                "the two inner make calls remain distinct"
            );
            let sink = facts
                .equations
                .iter()
                .find(|row| row.operation == "sink" && row.point.function.as_deref() == Some("run"))
                .expect("original first-output free");
            assert_eq!(
                transport.sources_for(Node {
                    construction: sink.point.construction,
                    var: sink.variables[0]
                }),
                first
            );
        },
    );
}

#[test]
fn t11_source_and_callee_free_meet_through_the_same_actual_carrier() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make() -> *mut i32 { malloc(4) }
pub unsafe fn release(p: *mut i32) { free(p); }
pub unsafe fn run() { let p = make(); release(p); }
"#,
        |facts| {
            let transport = MatchedTransport::build(facts);
            let calls = receivers(facts, "make");
            assert_eq!(calls.len(), 1);
            let source = facts
                .equations
                .iter()
                .find(|row| row.operation == "source")
                .unwrap();
            let sink = facts
                .equations
                .iter()
                .find(|row| row.operation == "sink")
                .unwrap();
            let source_id = EquationId {
                construction: source.point.construction,
                ordinal: source.ordinal,
            };
            let sink_id = EquationId {
                construction: sink.point.construction,
                ordinal: sink.ordinal,
            };
            let release = facts
                .boundary_substitutions
                .iter()
                .find(|row| {
                    row.role == Role::CallArgument
                        && row.point.function.as_deref() == Some("run")
                        && row.callee.as_deref() == Some("release")
                })
                .unwrap();
            let meets = transport.meets_for(calls[0].1);
            let meet = meets
                .iter()
                .find(|meet| meet.terminal.target == TerminalTarget::Free(sink_id))
                .expect("forward source and backward callee-free demand need one compatible route");
            assert_eq!(meet.source.endpoint, source_id);
            assert_eq!(
                meet.source.lineage,
                SourceLineage::Exact(vec![call_key(calls[0].0)])
            );
            assert_eq!(
                meet.terminal.lineage,
                SourceLineage::Exact(vec![call_key(release)])
            );
            assert_eq!(meet.guards.get(&source_id), Some(&true));
            assert_eq!(meet.guards.get(&sink_id), Some(&true));
            assert!(
                !transport
                    .meets_selected(calls[0].1, |key| meet.guards.get(&key).copied())
                    .is_empty()
            );
            assert!(
                transport
                    .meets_selected(calls[0].1, |key| {
                        if key == sink_id {
                            Some(false)
                        } else {
                            meet.guards.get(&key).copied()
                        }
                    })
                    .is_empty(),
                "a retracted actual sink cannot seed a selected meet"
            );
            assert!(
                transport.meets_selected(calls[0].1, |_| None).is_empty(),
                "unknown selection grants nothing"
            );
            assert!(
                !transport.meets_for(calls[0].1).is_empty(),
                "candidate transport survives selection loss"
            );
        },
    );
}

#[test]
fn t11_return_only_source_meets_output_obligation_without_a_free() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn make() -> *mut i32 { malloc(4) }
"#,
        |facts| {
            let transport = MatchedTransport::build(facts);
            let source = facts
                .equations
                .iter()
                .find(|row| row.operation == "source")
                .unwrap();
            let node = Node {
                construction: source.point.construction,
                var: source.variables[0],
            };
            let meets = transport.meets_for(node);
            assert!(
                !meets.is_empty(),
                "source-only return has an escape obligation"
            );
            assert!(
                meets
                    .iter()
                    .all(|meet| matches!(meet.terminal.target, TerminalTarget::Output { .. }))
            );
            assert!(!facts.equations.iter().any(|row| row.operation == "sink"));
        },
    );
}

#[test]
fn t12_source_free_recursive_scc_cannot_bootstrap_an_allocation_from_return_demand() {
    with_facts(
        r#"
pub unsafe fn first() -> *mut i32 { second() }
pub unsafe fn second() -> *mut i32 { first() }
"#,
        |facts| {
            let transport = MatchedTransport::build(facts);
            assert!(!facts.equations.iter().any(|row| row.operation == "source"));
            let mut observed = false;
            for terminal in facts
                .terminals
                .iter()
                .filter(|row| row.role == "return-output")
            {
                let super::super::ownership_occurrence::Availability::Present(values) =
                    &terminal.values
                else {
                    panic!("recursive pointer return must retain its represented terminal");
                };
                for value in values {
                    observed = true;
                    let node = Node {
                        construction: terminal.point.construction,
                        var: value.var,
                    };
                    assert!(
                        transport.sources_for(node).is_empty(),
                        "output recursion is not an allocation anchor"
                    );
                    assert!(
                        transport.meets_for(node).is_empty(),
                        "no source means no source/terminal meet"
                    );
                }
            }
            assert!(observed);
        },
    );
}

#[test]
fn t12_recursive_return_candidates_keep_the_real_anchor_and_mark_folded_identity() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn make(n: usize) -> *mut i32 {
    if n == 0 { 0 as *mut i32 }
    else if n == 1 { malloc(4) }
    else { make(n - 1) }
}
"#,
        |facts| {
            let transport = MatchedTransport::build(facts);
            let anchors: Vec<_> = facts
                .equations
                .iter()
                .filter(|row| row.operation == "source")
                .collect();
            assert_eq!(anchors.len(), 1, "one real allocator endpoint in this body");
            let endpoint = EquationId {
                construction: anchors[0].point.construction,
                ordinal: anchors[0].ordinal,
            };
            let terminal = facts
                .terminals
                .iter()
                .find(|row| row.role == "return-output")
                .expect("actual return");
            let super::super::ownership_occurrence::Availability::Present(values) =
                &terminal.values
            else {
                panic!("represented return")
            };
            assert_eq!(values.len(), 1);
            let node = Node {
                construction: terminal.point.construction,
                var: values[0].var,
            };
            let sources = transport.sources_for(node);
            assert!(
                !sources.is_empty(),
                "recursive summaries need the real local allocation anchor"
            );
            assert!(sources.iter().all(|source| source.endpoint == endpoint));
            assert!(
                sources
                    .iter()
                    .any(|source| matches!(source.lineage, SourceLineage::Exact(_)))
            );
            assert!(
                sources
                    .iter()
                    .any(|source| matches!(source.lineage, SourceLineage::Recursive { .. })),
                "repeated static applications cannot masquerade as an exact dynamic allocation identity"
            );
            assert!(
                transport
                    .meets_for(node)
                    .iter()
                    .all(|meet| matches!(meet.terminal.target, TerminalTarget::Output { .. })),
                "recursive output demand creates no free"
            );
            assert!(
                facts.source_occurrences["make"].iter().any(|row| {
                    row.syntax.immediate_origin
                        == super::super::ownership_access::ImmediateOrigin::Null
                }),
                "the empty return alternative remains explicit for the completeness producer"
            );
        },
    );
}

#[test]
fn t12_return_roster_retains_both_phi_inputs_independently_of_emitted_equations() {
    with_facts(
        r#"
pub unsafe fn choose(p: *mut i32, select: bool) -> *mut i32 {
    if select { p } else { 0 as *mut i32 }
}
"#,
        |facts| {
            use super::super::ownership_occurrence::Availability;
            let roster = facts
                .body_rosters
                .iter()
                .find(|row| row.point.function.as_deref() == Some("choose"))
                .expect("return completeness needs an independent MIR/SSA roster");
            let returns: Vec<_> = roster
                .blocks
                .iter()
                .filter(|block| block.reachable && block.return_statement.is_some())
                .collect();
            assert!(!returns.is_empty());
            for block in returns {
                let terminal = facts
                    .terminals
                    .iter()
                    .find(|row| {
                        row.point.function == roster.point.function
                            && row.point.construction == roster.point.construction
                            && row.point.block == Some(block.block)
                            && row.point.statement == block.return_statement
                            && row.local == 0
                    })
                    .expect("every reachable return has a terminal");
                let ssa = terminal.ssa.expect("actual return SSA");
                let version = roster
                    .versions
                    .iter()
                    .find(|v| v.local == 0 && v.ssa == ssa)
                    .expect("return SSA is in the independent version table");
                let Availability::Present(values) = &terminal.values else {
                    panic!("represented return")
                };
                assert_eq!(
                    version.variables,
                    values.iter().map(|value| value.var).collect::<Vec<_>>()
                );
            }
            let phi = roster
                .phis
                .iter()
                .find(|phi| phi.local == 0 && phi.inputs.len() >= 2)
                .expect("both pointer-return branches must remain in the phi roster");
            let edges: Vec<_> = facts
                .phi_edges
                .iter()
                .filter(|edge| {
                    edge.point.function == roster.point.function
                        && edge.point.construction == roster.point.construction
                        && edge.to == phi.block
                        && edge.local == phi.local
                })
                .collect();
            assert!(edges.len() >= 2);
            assert_eq!(
                edges
                    .iter()
                    .map(|edge| edge.input_ssa)
                    .collect::<BTreeSet<_>>(),
                phi.inputs.iter().copied().collect()
            );
            for edge in edges {
                let predecessor = roster
                    .blocks
                    .iter()
                    .find(|block| block.block == edge.from)
                    .unwrap();
                assert_eq!(predecessor.successors[edge.edge_ordinal], phi.block);
                assert!(
                    roster
                        .versions
                        .iter()
                        .any(|v| v.local == phi.local && v.ssa == edge.input_ssa)
                );
            }
            let mut no_equations = facts.clone();
            no_equations.equations.clear();
            assert_eq!(
                no_equations.body_rosters, facts.body_rosters,
                "an omitted constraint cannot silently erase an incoming SSA alternative from the roster"
            );
            assert_eq!(no_equations.phi_edges, facts.phi_edges);
        },
    );
}

#[test]
fn t12_return_coverage_rejects_missing_constraints_and_observations() {
    with_facts(
        r#"
pub unsafe fn choose(p: *mut i32, select: bool) -> *mut i32 {
    if select { p } else { 0 as *mut i32 }
}
"#,
        |facts| {
            use super::coverage::validate_returns;
            assert_eq!(validate_returns(facts, 0, "choose"), Ok(()));
            let phi_equation = facts
                .equations
                .iter()
                .position(|row| {
                    row.point.function.as_deref() == Some("choose")
                        && row.point.phase == "phi"
                        && row.operation == "equal"
                })
                .expect("real emitted phi equality");
            let mut missing = facts.clone();
            missing.equations.remove(phi_equation);
            assert!(
                validate_returns(&missing, 0, "choose").is_err(),
                "a missing phi equation cannot make an alternative disappear"
            );
            let mut missing = facts.clone();
            missing.terminals.retain(|row| row.role != "return-output");
            assert!(
                validate_returns(&missing, 0, "choose").is_err(),
                "every reachable return is required"
            );
            let mut missing = facts.clone();
            assert!(missing.phi_edges.pop().is_some());
            assert!(
                validate_returns(&missing, 0, "choose").is_err(),
                "a missing predecessor is not an empty alternative"
            );
            let mut missing = facts.clone();
            missing.body_rosters[0]
                .versions
                .retain(|row| row.local != 0);
            assert!(
                validate_returns(&missing, 0, "choose").is_err(),
                "return SSA correspondence is mandatory"
            );
            let mut missing = facts.clone();
            missing.body_rosters[0].phis.clear();
            assert!(
                validate_returns(&missing, 0, "choose").is_err(),
                "dropping a phi roster cannot hide its incoming alternatives"
            );
            let mut missing = facts.clone();
            missing.body_rosters[0].phis.clear();
            missing.phi_edges.clear();
            assert!(
                validate_returns(&missing, 0, "choose").is_err(),
                "a phi SSA version still needs its definition if both observations are omitted"
            );
            let mut missing = facts.clone();
            missing.body_rosters.clear();
            assert!(
                validate_returns(&missing, 0, "choose").is_err(),
                "no roster means no coverage proof"
            );
        },
    );
}

#[test]
fn t12_coverage_rejects_an_earlier_return_version_and_missing_consume_versions() {
    with_facts(
        r#"
pub unsafe fn choose(p: *mut i32, select: bool) -> *mut i32 {
    let copy = p;
    let _value = *copy;
    if select { p } else { 0 as *mut i32 }
}
"#,
        |facts| {
            use super::{super::ownership_occurrence::Availability, coverage::validate_returns};
            assert_eq!(validate_returns(facts, 0, "choose"), Ok(()));
            let roster = &facts.body_rosters[0];
            let terminal = facts
                .terminals
                .iter()
                .position(|row| row.local == 0 && row.role == "return-output")
                .unwrap();
            let previous = roster
                .versions
                .iter()
                .find(|row| {
                    row.local == 0
                        && Some(row.ssa) != facts.terminals[terminal].ssa
                        && row.variables.len() == roster.return_width
                })
                .expect("an earlier valid return-local version");
            let mut missing = facts.clone();
            let replacement = &mut missing.terminals[terminal];
            replacement.ssa = Some(previous.ssa);
            let Availability::Present(values) = &mut replacement.values else {
                panic!("pointer return")
            };
            for (value, &variable) in values.iter_mut().zip(&previous.variables) {
                value.var = variable;
            }
            assert!(
                validate_returns(&missing, 0, "choose").is_err(),
                "an earlier consistent version/value pair is not the selected return version"
            );

            let critical: BTreeSet<_> = roster
                .phis
                .iter()
                .flat_map(|phi| {
                    std::iter::once((phi.local, phi.lhs))
                        .chain(phi.inputs.iter().map(|&ssa| (phi.local, ssa)))
                })
                .chain(
                    facts
                        .terminals
                        .iter()
                        .filter(|row| row.local == 0)
                        .filter_map(|row| row.ssa.map(|ssa| (0, ssa))),
                )
                .collect();
            let removable = roster
                .consumes
                .iter()
                .flat_map(|row| {
                    std::iter::once((row.local, row.use_ssa))
                        .chain(row.def_ssa.map(|ssa| (row.local, ssa)))
                })
                .find(|key| {
                    !critical.contains(key)
                        && roster.versions.iter().any(|v| (v.local, v.ssa) == *key)
                })
                .expect("a consumed version outside the return/phi subset");
            let mut missing = facts.clone();
            missing.body_rosters[0]
                .versions
                .retain(|row| (row.local, row.ssa) != removable);
            assert!(
                validate_returns(&missing, 0, "choose").is_err(),
                "every consume reference needs its SSA version"
            );
        },
    );
}

#[test]
fn t13_missing_transfer_correspondence_is_a_typed_hold_not_a_route() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); let q = p; free(q); }
"#,
        |facts| {
            use super::{super::ownership_occurrence::Availability, matched::DenialReason};
            let sink = facts
                .equations
                .iter()
                .find(|row| row.operation == "sink")
                .unwrap();
            let sink_node = Node {
                construction: sink.point.construction,
                var: sink.variables[0],
            };
            assert!(
                !MatchedTransport::build(facts)
                    .meets_for(sink_node)
                    .is_empty()
            );
            let index = facts
                .equations
                .iter()
                .position(|row| {
                    row.transfer.is_some()
                        && matches!(
                            row.operation.as_str(),
                            "linear" | "equal" | "guarded-copy" | "guarded-move"
                        )
                })
                .unwrap();
            let mut missing = facts.clone();
            let equation = &mut missing.equations[index];
            let id = EquationId {
                construction: equation.point.construction,
                ordinal: equation.ordinal,
            };
            equation.transfer.as_mut().unwrap().source =
                Availability::Missing("deliberate missing exact source occurrence".into());
            let transport = MatchedTransport::build(&missing);
            assert!(
                transport
                    .denials()
                    .iter()
                    .any(|denial| denial.equation == Some(id)
                        && denial.reason == DenialReason::MissingTransferBinding),
                "missing correspondence must remain explicit"
            );
            assert!(
                transport.meets_for(sink_node).is_empty(),
                "numeric equality alone is not an exact transport route"
            );
        },
    );
}

#[test]
fn t13_missing_function_roster_and_source_guard_cannot_look_complete() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); free(p); }
"#,
        |facts| {
            use super::matched::DenialReason;
            let sink = facts
                .equations
                .iter()
                .find(|row| row.operation == "sink")
                .unwrap();
            let node = Node {
                construction: sink.point.construction,
                var: sink.variables[0],
            };
            assert!(!MatchedTransport::build(facts).meets_for(node).is_empty());
            let mut missing = facts.clone();
            missing.body_rosters.clear();
            let held = MatchedTransport::build(&missing);
            assert!(
                held.denials()
                    .iter()
                    .any(|denial| denial.reason == DenialReason::ReturnCoverage),
                "an omitted whole function roster must not evade its own coverage check"
            );
            assert!(held.meets_for(node).is_empty());
            let source = facts
                .equations
                .iter()
                .find(|row| row.operation == "source")
                .unwrap();
            let source_id = EquationId {
                construction: source.point.construction,
                ordinal: source.ordinal,
            };
            let mut missing = facts.clone();
            missing.guards.retain(|guard| guard.equation != source_id);
            let held = MatchedTransport::build(&missing);
            assert!(
                held.denials()
                    .iter()
                    .any(|denial| denial.reason == DenialReason::MissingGuard
                        && denial.equation == Some(source_id))
            );
            assert!(held.meets_for(node).is_empty());
        },
    );
}

#[test]
fn t13_folded_paths_and_incomplete_call_boundaries_stay_held() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make() -> *mut i32 { let p = malloc(4); p }
pub unsafe fn run() { let p = make(); free(p); }
"#,
        |facts| {
            use super::{
                super::ownership_occurrence::{Availability, PathStep},
                matched::DenialReason,
            };
            let sink = facts
                .equations
                .iter()
                .find(|row| row.operation == "sink")
                .unwrap();
            let node = Node {
                construction: sink.point.construction,
                var: sink.variables[0],
            };
            assert!(!MatchedTransport::build(facts).meets_for(node).is_empty());
            let mut incomplete = facts.clone();
            let boundary = incomplete
                .boundary_substitutions
                .iter_mut()
                .find(|row| {
                    row.role == Role::ReturnReceiver
                        && row.point.function.as_deref() == Some("run")
                        && row.callee.as_deref() == Some("make")
                })
                .unwrap();
            let id = boundary.ordinal;
            let Variables::UseDef { def_var, .. } = boundary.matched[0].actual else {
                panic!("actual return receiver")
            };
            boundary.unmatched_actual_vars.push(def_var);
            let held = MatchedTransport::build(&incomplete);
            assert!(
                held.denials()
                    .iter()
                    .any(|denial| denial.boundary == Some(id)
                        && denial.reason == DenialReason::UnmatchedBoundary)
            );
            assert!(held.meets_for(node).is_empty());
            let mut folded = facts.clone();
            let equation = folded
                .equations
                .iter_mut()
                .find(|row| {
                    row.transfer.is_some()
                        && matches!(
                            row.operation.as_str(),
                            "linear" | "equal" | "guarded-copy" | "guarded-move"
                        )
                })
                .unwrap();
            let id = EquationId {
                construction: equation.point.construction,
                ordinal: equation.ordinal,
            };
            let Availability::Present(source) = &mut equation.transfer.as_mut().unwrap().source
            else {
                panic!("exact baseline source")
            };
            source.path.push(PathStep::ArrayElement);
            let held = MatchedTransport::build(&folded);
            assert!(
                held.denials()
                    .iter()
                    .any(|denial| denial.equation == Some(id)
                        && denial.reason == DenialReason::FoldedPointerPath)
            );
            assert!(held.meets_for(node).is_empty());
        },
    );
}
