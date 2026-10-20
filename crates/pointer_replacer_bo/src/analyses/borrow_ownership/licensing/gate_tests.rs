//! G controls use real compiler occurrences; fixture programs never execute.

use super::graph_tests::with_facts;

#[test]
fn g02_copy_partner_free_selects_one_responsibility_route() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); let q = p; let r = q; free(r); }
"#,
        |facts| {
            assert!(
                facts
                    .equations
                    .iter()
                    .any(|row| row.operation == "linear" && row.transfer.is_some()),
                "real copy split must be represented"
            );
            let frozen = facts.licensing.as_ref().unwrap();
            assert!(
                !frozen.objective_grants.is_empty(),
                "one partner-free route: {:?}",
                frozen.grant_holds
            );
            let route = &frozen.objective_grants[0].route;
            for row in facts
                .equations
                .iter()
                .filter(|row| row.operation == "linear")
            {
                let split = row.transfer.as_ref().unwrap();
                let node = |var| super::transport::Node {
                    construction: row.point.construction,
                    var,
                };
                if route.contains(&node(split.source_use)) {
                    assert_ne!(
                        route.contains(&node(split.destination_def)),
                        route.contains(&node(split.source_def)),
                        "exactly one successor carries this allocation's selected responsibility"
                    );
                }
            }
        },
    );
}

#[test]
fn g02_source_only_copy_return_has_an_owning_output_route() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn make() -> *mut i32 { let p = malloc(4); let q = p; q }
"#,
        |facts| {
            let frozen = facts.licensing.as_ref().unwrap();
            assert!(
                !frozen.objective_grants.is_empty(),
                "copy-return route: {:?}",
                frozen.grant_holds
            );
            assert!(facts.equations.iter().all(|row| row.operation != "sink"));
        },
    );
}

#[test]
fn g03_branching_reader_is_not_licensed_by_a_may_reach_free_route() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() -> i32 {
    let p = malloc(4); *p = 1; let q = p; let r = p; let value = *q; free(r); value
}
"#,
        |facts| {
            assert!(
                facts
                    .licensing
                    .as_ref()
                    .unwrap()
                    .objective_grants
                    .is_empty()
            );
        },
    );
}

#[test]
fn g08_missing_final_zero_law_refuses_the_grant() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); free(p); }
"#,
        |facts| {
            fn grants(facts: &super::facts::Facts) -> Vec<super::grants::Grant> {
                let graph = super::transport::CandidateGraph::build(facts);
                let matched = super::matched::MatchedTransport::build(facts);
                let origins = super::value_origins::ValueOrigins::build(facts);
                super::grants::plan(facts, &graph, &matched, &origins).0
            }
            assert!(!grants(facts).is_empty());
            let mut removed = facts.clone();
            let before = removed.equations.len();
            removed
                .equations
                .retain(|row| row.assumption_class.as_deref() != Some("temporary-finalization"));
            assert!(removed.equations.len() < before);
            assert!(
                grants(&removed).is_empty(),
                "a responsibility licence cannot rely on an incomplete final-zero system"
            );
        },
    );
}

#[test]
fn g01_two_allocation_objects_are_not_one_generation() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); let q = malloc(4); free(p); free(q); }
"#,
        |facts| {
            let source_ids: std::collections::BTreeSet<_> = facts
                .equations
                .iter()
                .filter(|row| row.operation == "source")
                .map(|row| row.ordinal)
                .collect();
            assert_eq!(source_ids.len(), 2);
            assert!(
                facts
                    .licensing
                    .as_ref()
                    .unwrap()
                    .objective_grants
                    .is_empty(),
                "multi-generation scope awaits per-generation role/terminal certification; equal allocator names do not merge it"
            );
        },
    );
}

#[test]
fn g04_mixed_stack_inflows_do_not_receive_a_licensing_grant() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() {
    let mut stack = 1; let mut p = malloc(4); let q = p; p = &mut stack; *p = 2; free(q);
}
"#,
        |facts| {
            assert!(
                facts
                    .licensing
                    .as_ref()
                    .unwrap()
                    .objective_grants
                    .is_empty()
            );
        },
    );
}

#[test]
fn g07_realloc_outcomes_do_not_enter_the_scalar_malloc_grant_rule() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn realloc(p: *mut i32, n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); let q = realloc(p, 8); free(q); }
"#,
        |facts| {
            assert!(
                facts
                    .licensing
                    .as_ref()
                    .unwrap()
                    .objective_grants
                    .is_empty(),
                "realloc needs its distinct old/new outcome contract, never a malloc-only grant"
            );
        },
    );
}

#[test]
fn g10_every_grant_exports_the_complete_hard_gate_inventory() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); free(p); }
"#,
        |facts| {
            let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            let document = serde_json::to_value(&snapshot).unwrap();
            let gates = document["objective_grants"][0]["discharged_gates"]
                .as_array()
                .expect("a grant must identify all discharged hard gates");
            assert_eq!(gates.len(), 12);
            for index in 0..gates.len() {
                let mut removed = document.clone();
                removed["objective_grants"][0]["discharged_gates"]
                    .as_array_mut()
                    .unwrap()
                    .remove(index);
                let removed: super::snapshot::Snapshot = serde_json::from_value(removed).unwrap();
                assert!(
                    removed.validate().is_err(),
                    "missing gate {index} cannot default to true"
                );
            }
        },
    );
}

#[test]
fn g01_transfer_binding_must_match_the_actual_consume() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); let q = p; let r = q; free(r); }
"#,
        |facts| {
            let transfer = facts
                .equations
                .iter()
                .find(|row| row.operation == "linear")
                .unwrap()
                .transfer
                .clone()
                .unwrap();
            let mut wrong = facts.clone();
            for equation in &mut wrong.equations {
                if equation.transfer.as_ref() == Some(&transfer) {
                    let binding = &mut equation.transfer.as_mut().unwrap().source;
                    let super::super::ownership_occurrence::Availability::Present(binding) =
                        binding
                    else {
                        panic!("actual binding")
                    };
                    binding.local += 1000;
                }
            }
            let graph = super::transport::CandidateGraph::build(&wrong);
            let matched = super::matched::MatchedTransport::build(&wrong);
            let origins = super::value_origins::ValueOrigins::build(&wrong);
            assert!(
                super::grants::plan(&wrong, &graph, &matched, &origins)
                    .0
                    .is_empty(),
                "Present and matching Vars cannot authenticate a foreign local's consume"
            );
        },
    );
}

#[test]
fn g02_accepted_copy_model_keeps_one_post_split_token_and_both_endpoints() {
    use super::super::ssa::constraint::Var;
    let fixture = super::tests::inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); let q = p; let r = q; free(r); }
"#,
    );
    fixture.assert_kind("run::p", super::super::SlotKind::Owning);
    fixture.assert_kind("run::q", super::super::SlotKind::Owning);
    let owns = fixture.export.version_owns.as_ref().unwrap();
    let equations = fixture.export.ownership_equations.as_ref().unwrap();
    let mut splits = 0;
    for equation in equations {
        if matches!(equation.operation.as_str(), "source" | "sink") {
            assert!(
                owns[Var::from_u32(equation.variables[0])],
                "licensing must not trade away the original endpoint"
            );
        }
        if equation.operation == "linear" {
            splits += 1;
            let values: Vec<_> = equation
                .variables
                .iter()
                .map(|&var| owns[Var::from_u32(var)] as u8)
                .collect();
            assert_eq!(
                values[0] + values[1],
                values[2],
                "one accepted model supplies all split valuations"
            );
        }
    }
    assert!(splits > 0);
}

#[test]
fn g10_missing_gate_refuses_emission_before_adding_any_clause() {
    super::graph_tests::with_solver_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); free(p); }
"#,
        |facts, _, slots| {
            let probe = super::super::solver::KindSolver::new(slots);
            for index in 0..super::grants::HardGate::ALL.len() {
                let mut omitted = facts.clone();
                std::rc::Rc::make_mut(omitted.licensing.as_mut().unwrap()).objective_grants[0]
                    .discharged_gates
                    .remove(index);
                let before = probe.hard_assertion_count();
                assert!(probe.apply_licensing_grants(&omitted).is_err());
                assert_eq!(probe.hard_assertion_count(), before);
            }
        },
    );
}
