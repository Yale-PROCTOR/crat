//! T10 output candidates from actual compiler facts, without model queries.

use super::{
    super::ownership_occurrence::{Availability, PathStep},
    graph_tests::with_facts,
    transport::{CandidateGraph, ExitRole, Node},
};

#[test]
fn t10_return_only_allocation_has_output_demand_without_a_free_sink() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn make() -> *mut i32 { let p = malloc(4); p }
pub unsafe fn wrapper() -> *mut i32 { make() }
"#,
        |facts| {
            let graph = CandidateGraph::build(facts);
            assert_eq!(graph.sources.len(), 1);
            assert!(
                graph.sinks.is_empty(),
                "owning output must not invent a free"
            );
            assert!(
                !facts
                    .equations
                    .iter()
                    .any(|equation| equation.operation == "sink")
            );
            for function in ["make", "wrapper"] {
                let terminal = facts
                    .terminals
                    .iter()
                    .find(|terminal| {
                        terminal.point.function.as_deref() == Some(function)
                            && terminal.role == "return-output"
                    })
                    .expect("actual pointer-return terminal");
                let Availability::Present(values) = &terminal.values else {
                    panic!("represented return values")
                };
                assert!(!values.is_empty());
                for value in values {
                    let Availability::Present(path) = &value.path else {
                        panic!("exact return path")
                    };
                    let expected = Node {
                        construction: terminal.point.construction,
                        var: value.var,
                    };
                    let exit = graph
                        .exits
                        .iter()
                        .find(|exit| {
                            exit.node == expected && exit.terminal_ordinal == terminal.ordinal
                        })
                        .expect("the actual returned carrier needs an L-EXIT candidate");
                    assert_eq!(exit.role, ExitRole::Return);
                    assert_eq!(exit.path, *path);
                    assert!(!exit.role_certification_pending);
                    assert!(graph.forward().contains(&exit.node));
                }
            }
            assert!(graph.backward().is_empty(), "no deallocator demand exists");
            assert!(
                graph.backward_outputs().contains(&graph.sources[0].node),
                "owning-output demand must reach the real allocation source"
            );
        },
    );
}

#[test]
fn t10_projected_parameter_field_output_keeps_role_certification_pending() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub struct Holder { ptr: *mut i32 }
pub unsafe fn install(out: &mut Holder) {
    let p = malloc(4);
    out.ptr = p;
}
"#,
        |facts| {
            let graph = CandidateGraph::build(facts);
            let terminal = facts
                .terminals
                .iter()
                .find(|terminal| {
                    terminal.point.function.as_deref() == Some("install")
                        && terminal.role == "parameter-output"
                })
                .expect("actual writable-parameter terminal");
            let Availability::Present(values) = &terminal.values else {
                panic!("represented parameter values")
            };
            let field = values.iter().find(|value| {
            matches!(&value.path, Availability::Present(path)
                if path.iter().any(|step| matches!(step, PathStep::Deref))
                    && path.iter().any(|step| matches!(step, PathStep::Field { name, .. } if name == "ptr")))
        }).expect("the projected payload has its own terminal path");
            let expected = Node {
                construction: terminal.point.construction,
                var: field.var,
            };
            let exit = graph
                .exits
                .iter()
                .find(|exit| exit.node == expected && exit.terminal_ordinal == terminal.ordinal)
                .expect("projected field output needs a candidate obligation");
            assert_eq!(
                exit.role,
                ExitRole::ProjectedParameter {
                    local: terminal.local
                }
            );
            assert!(
                exit.role_certification_pending,
                "field output is not yet a certified call role"
            );
            let Availability::Present(path) = &field.path else { unreachable!() };
            assert_eq!(exit.path, *path);
            for outer in values.iter().filter(
                |value| matches!(&value.path, Availability::Present(path) if path.is_empty()),
            ) {
                assert!(
                    !graph.exits.iter().any(|exit| exit.node
                        == Node {
                            construction: terminal.point.construction,
                            var: outer.var,
                        }),
                    "the outer struct reference is not an owning-output obligation"
                );
            }
            assert!(graph.sinks.is_empty());
            assert_eq!(graph.sources.len(), 1);
            assert!(graph.backward_outputs().contains(&graph.sources[0].node));
        },
    );
}

#[test]
fn t10_live_local_at_exit_retains_final_zero_without_an_exit_candidate_or_free() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn run() { let p = malloc(4); let _ = p; }
"#,
        |facts| {
            let graph = CandidateGraph::build(facts);
            let mut observed_final_value = false;
            for terminal in facts
                .terminals
                .iter()
                .filter(|terminal| terminal.role == "local-final-zero")
            {
                let Availability::Present(values) = &terminal.values else { continue };
                for value in values {
                    observed_final_value = true;
                    assert!(
                        facts.equations.iter().any(|equation| {
                            equation.point == terminal.point
                                && equation.operation == "assume"
                                && equation.assumption_class.as_deref()
                                    == Some("temporary-finalization")
                                && equation.value == Some(false)
                                && equation.variables == [value.var]
                        }),
                        "the actual local-final-zero law remains present"
                    );
                    assert!(
                        !graph.exits.iter().any(|exit| {
                            exit.node
                                == Node {
                                    construction: terminal.point.construction,
                                    var: value.var,
                                }
                        }),
                        "a local's final value cannot be relabelled as owning output"
                    );
                }
            }
            assert!(
                observed_final_value,
                "the fixture holds a real pointer local until exit"
            );
            assert!(graph.exits.is_empty());
            assert!(graph.sinks.is_empty());
            assert!(graph.backward_outputs().is_empty());
            assert!(
                !facts
                    .equations
                    .iter()
                    .any(|equation| equation.operation == "sink")
            );
        },
    );
}

#[test]
fn t10_null_and_source_free_recursive_outputs_cannot_seed_an_allocation_anchor() {
    with_facts(
        r#"
pub unsafe fn first(p: *mut i32, n: u32) -> *mut i32 {
    if n == 0 { 0 as *mut i32 } else if n == 1 { p } else { second(p, n - 1) }
}
pub unsafe fn second(p: *mut i32, n: u32) -> *mut i32 {
    if n == 0 { 0 as *mut i32 } else if n == 1 { p } else { first(p, n - 1) }
}
"#,
        |facts| {
            let graph = CandidateGraph::build(facts);
            assert!(
                facts
                    .terminals
                    .iter()
                    .any(|terminal| terminal.role == "return-output")
            );
            assert!(graph.sources.is_empty());
            assert!(graph.sinks.is_empty());
            assert!(
                graph.forward().is_empty(),
                "recursive output demand supplies no source anchor"
            );
            assert!(graph.forward().is_disjoint(&graph.backward_outputs()));
        },
    );
}
