//! O04 grants use actual closed construction evidence, never kind-score bonuses.

use super::graph_tests::with_facts;

#[test]
fn o04_closed_scalar_grant_retains_its_exact_source_terminal_and_carrier() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); free(p); }
"#,
        |facts| {
            let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            let document = serde_json::to_value(&snapshot).unwrap();
            if snapshot.objective_grants.is_empty() {
                eprintln!("O04_FACTS={document}");
            }
            let grants = document["objective_grants"]
                .as_array()
                .expect("O04 records checked grants");
            assert!(
                !grants.is_empty(),
                "the actual closed scalar source/free chain has eligible responsibility: {:?}",
                snapshot.grant_holds
            );
            snapshot.validate().unwrap();
            let mut omitted = document;
            omitted["objective_grants"] = serde_json::json!([]);
            let omitted: super::snapshot::Snapshot = serde_json::from_value(omitted).unwrap();
            assert!(
                omitted.validate().is_err(),
                "a granted dependency family cannot disappear from cache evidence"
            );
        },
    );
}

#[test]
fn o04_missing_or_wrong_free_proxy_and_unit_evidence_withhold_the_grant() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); free(p); }
"#,
        |facts| {
            fn has_grants(facts: &super::facts::Facts) -> bool {
                let graph = super::transport::CandidateGraph::build(facts);
                let matched = super::matched::MatchedTransport::build(facts);
                let origins = super::value_origins::ValueOrigins::build(facts);
                !super::grants::plan(facts, &graph, &matched, &origins)
                    .0
                    .is_empty()
            }
            assert!(has_grants(facts));
            let mut missing = facts.clone();
            missing.call_arg_registrations.clear();
            assert!(
                !has_grants(&missing),
                "unregistered temporary is not an erased free proxy"
            );
            let mut wrong = facts.clone();
            wrong.call_arg_registrations[0].by_reference = true;
            assert!(
                !has_grants(&wrong),
                "a borrowed call argument cannot consume responsibility"
            );
            let mut wrong_source = facts.clone();
            wrong_source.call_arg_registrations[0].source_occurrence =
                super::super::ownership_occurrence::Availability::Present(0);
            assert!(
                !has_grants(&wrong_source),
                "a same-value consume at another point is insufficient"
            );
            let mut missing_unit = facts.clone();
            missing_unit.unit_locals.clear();
            assert!(
                !has_grants(&missing_unit),
                "Missing does not prove unit type"
            );
        },
    );
}

#[test]
fn o04_direct_owning_return_uses_an_output_obligation_without_a_free() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn make() -> *mut i32 { malloc(4) }
"#,
        |facts| {
            let frozen = facts.licensing.as_ref().unwrap();
            assert!(
                !frozen.objective_grants.is_empty(),
                "direct fresh return: {:?}",
                frozen.grant_holds
            );
            assert!(facts.equations.iter().all(|row| row.operation != "sink"));
            assert!(frozen.objective_grants.iter().all(|grant| matches!(
                grant.meet.terminal.target,
                super::matched::TerminalTarget::Output { .. }
            )));
        },
    );
}

#[test]
fn o04_free_then_return_alias_has_no_owning_output_grant() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() -> *mut i32 { let p = malloc(4); let q = p; free(p); q }
"#,
        |facts| {
            assert!(
                facts
                    .licensing
                    .as_ref()
                    .unwrap()
                    .objective_grants
                    .is_empty(),
                "an earlier C free cannot become an owning-return contract by selector retraction"
            );
        },
    );
}

#[test]
fn o04_grant_is_mandatory_and_retracts_with_its_actual_endpoint_predicates() {
    use super::super::{solver::KindSolver, ssa::constraint::Var};
    super::graph_tests::with_solver_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn run() { let p = malloc(4); free(p); }
"#,
        |facts, original, slots| {
            let frozen = facts.licensing.as_ref().unwrap();
            let grant = &frozen.objective_grants[0];
            let probe = KindSolver::new(slots);
            let before = probe.hard_assertion_count();
            let emitted = probe.apply_licensing_grants(facts).unwrap();
            assert!(emitted > 0);
            assert_eq!(probe.hard_assertion_count() - before, emitted);
            assert_eq!(
                probe.hard_loop_solver().assertion_count(),
                probe.hard_assertion_count(),
                "the hard backend receives every grant clause"
            );
            let mut dependencies: Vec<_> = grant
                .meet
                .guards
                .iter()
                .map(|(key, required)| {
                    let predicate = &facts
                        .guards
                        .iter()
                        .find(|binding| &binding.equation == key)
                        .unwrap()
                        .predicate;
                    if *required {
                        predicate.clone()
                    } else {
                        !predicate
                    }
                })
                .collect();
            let rho = &facts.ownership_asts[Var::from_u32(grant.carrier.var)];
            dependencies.push(!rho);
            assert_eq!(
                probe.check_with_assumptions(&dependencies),
                z3::SatResult::Unsat,
                "the grant alone supplies responsibility under its exact dependencies"
            );
            for index in 0..dependencies.len() - 1 {
                let mut dropped = dependencies.clone();
                dropped[index] = !&dropped[index];
                assert_eq!(
                    probe.check_with_assumptions(&dropped),
                    z3::SatResult::Sat,
                    "withdrawing any endpoint removes this grant's ownership pressure"
                );
            }
            let mut missing = facts.clone();
            missing.guards.clear();
            let before = probe.hard_assertion_count();
            assert!(probe.apply_licensing_grants(&missing).is_err());
            assert_eq!(
                probe.hard_assertion_count(),
                before,
                "validate before any partial assertion"
            );
            assert_eq!(
                original.check_sat_count(),
                0,
                "construction capture itself remains query-free"
            );
        },
    );
}
