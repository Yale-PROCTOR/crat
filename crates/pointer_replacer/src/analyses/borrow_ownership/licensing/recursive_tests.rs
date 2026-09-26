//! T12 RED over real compiler construction; no solver or fixture execution.

use std::collections::BTreeSet;

use rustc_hir::{ItemKind, OwnerNode};

use super::{
    super::{
        construction::{CopyLendMode, construct_bo_into},
        crate_slots::CrateSlots,
        execution_guard,
        mutability_facts::MutFacts,
        origins::compute_origins,
        ownership_boundary::Role,
        ownership_occurrence::Availability,
        solver::KindSolver,
    },
    coverage,
    facts::EquationId,
    matched::CallKey,
    recursive::*,
};
use crate::utils::rustc::RustProgram;

#[test]
fn t12_recursive_invocations_require_fresh_binders_return_coverage_and_real_source_anchor() {
    ::utils::compilation::run_compiler_on_str(r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn fresh(n: usize) -> *mut i32 {
    if n == 0 { return 0 as *mut i32; }
    if n == 1 { return malloc(4); }
    fresh(n - 1)
}
pub unsafe fn empty(n: usize) -> *mut i32 {
    if n == 0 { return 0 as *mut i32; }
    empty(n - 1)
}
"#, |tcx| {
        let functions = tcx.hir_crate(()).owners.iter().filter_map(|owner| {
            let owner = owner.as_owner()?;
            let OwnerNode::Item(item) = owner.node() else { return None };
            matches!(item.kind, ItemKind::Fn { .. }).then_some(item.owner_id.def_id)
        }).collect();
        let program = RustProgram { tcx, functions, structs: Vec::new() };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mutability = MutFacts::from_program(&program);
        let model_entries = execution_guard::model_entries();
        let solver = KindSolver::new(&slots);
        construct_bo_into(&program, &slots, &origins, &mutability, &solver, CopyLendMode::Baseline).unwrap();
        let facts = solver.ownership_facts().expect("actual compiler construction facts");
        assert_eq!([
            solver.check_sat_count(), solver.hard_check_count(), solver.optimize_materialization_count(),
            solver.lazy_plain_hard_check_count(), solver.lazy_tracked_recheck_count(),
            solver.lazy_plain_materialization_count(),
        ], [0; 6]);
        assert_eq!(execution_guard::model_entries(), model_entries);

        for function in ["fresh", "empty"] {
            coverage::validate_returns(&facts, 0, function).expect("independent return roster is complete");
            let recursive_calls: BTreeSet<_> = facts.boundary_substitutions.iter().filter(|row| {
                row.point.function.as_deref() == Some(function)
                    && row.callee.as_deref() == Some(function)
                    && row.role == Role::ReturnReceiver
            }).map(|row| CallKey {
                construction: row.point.construction, caller: function.into(),
                block: row.point.block.unwrap(), statement: row.point.statement.unwrap(),
                callee: function.into(),
            }).collect();
            assert_eq!(recursive_calls.len(), 1, "fixture has one exact recursive application");
            let expected_returns: BTreeSet<_> = facts.terminals.iter().filter(|row| {
                row.point.function.as_deref() == Some(function) && row.role == "return-output"
            }).map(|row| ReturnKey {
                construction: row.point.construction, function: function.into(),
                block: row.point.block.unwrap(), statement: row.point.statement.unwrap(), terminal: row.ordinal,
            }).collect();
            assert!(!expected_returns.is_empty());
            let Availability::Present(certificate) = certify_invocations(&facts, 0, function) else {
                panic!("T12 must produce the recursive invocation/return certificate for {function}")
            };
            assert_eq!(certificate.applications.iter().map(|application| application.call.clone()).collect::<BTreeSet<_>>(), recursive_calls);
            assert_eq!(certificate.applications.len(), recursive_calls.len());
            let Availability::Present(returns) = certificate.returns else { panic!("all return records must be accounted for") };
            assert_eq!(returns.len(), expected_returns.len());
            assert_eq!(returns.into_iter().collect::<BTreeSet<_>>(), expected_returns);
            for application in certificate.applications {
                let Availability::Present(binder) = application.invocation else { panic!("recursive fold is not an invocation binder") };
                assert_eq!(binder.application, application.call);
                assert_eq!(binder.binding, InvocationBinding::FreshPerExecution,
                    "repeated executions of the same CallKey must introduce fresh invocation scopes");
                let Availability::Present(substitutions) = application.substitutions else { panic!("exact actual/formal substitutions required") };
                let expected: Vec<_> = facts.boundary_substitutions.iter().filter(|row| {
                    row.point.construction == application.call.construction
                        && row.point.function.as_ref() == Some(&application.call.caller)
                        && row.point.block == Some(application.call.block)
                        && row.point.statement == Some(application.call.statement)
                        && row.callee.as_ref() == Some(&application.call.callee)
                }).flat_map(|row| (0..row.matched.len()).map(move |matched| SubstitutionKey {
                    construction: row.point.construction, boundary: row.ordinal, matched,
                })).collect();
                assert!(!expected.is_empty(), "the recursive return has a real matcher pair");
                assert_eq!(substitutions, expected);
            }
            assert!(certificate.pending.contains(&PendingRequirement::OriginCompleteness));
            assert!(certificate.pending.contains(&PendingRequirement::OwnedInputContract));
            if function == "fresh" {
                let Availability::Present(anchor) = certificate.source_anchor else { panic!("base malloc supplies the real anchor") };
                assert_eq!(anchor.binding, InvocationBinding::FreshPerExecution);
                assert!(facts.equations.iter().any(|row| row.operation == "source"
                    && row.point.function.as_deref() == Some(function)
                    && anchor.equation == (EquationId { construction: row.point.construction, ordinal: row.ordinal })
                    && row.endpoint.is_some()), "anchor must reference an actual Source equation");
            } else {
                assert!(!facts.equations.iter().any(|row| row.operation == "source" && row.point.function.as_deref() == Some(function)));
                assert!(matches!(certificate.source_anchor, Availability::Missing(_)),
                    "a source-free recursive SCC must not bootstrap an allocation anchor");
            }
        }
    }).unwrap_or_else(|error| error.raise());
}

#[test]
fn t12_certificate_retains_source_instances_and_rejects_unrelated_scc_allocations() {
    super::graph_tests::with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn fresh(n: usize) -> *mut i32 {
    if n == 0 { malloc(4) } else { fresh(n - 1) }
}
pub unsafe fn unrelated(n: usize) -> *mut i32 {
    let _leaked = malloc(4);
    if n == 0 { 0 as *mut i32 } else { unrelated(n - 1) }
}
"#,
        |facts| {
            let transport = super::matched::MatchedTransport::build(facts);
            for function in ["fresh", "unrelated"] {
                let Availability::Present(certificate) = certify_invocations(facts, 0, function)
                else {
                    panic!("structural recursive record")
                };
                assert!(!certificate.value_anchors.is_empty());
                for returned in &certificate.value_anchors {
                    let expected = transport.sources_for(returned.value);
                    assert_eq!(
                        returned.instances.iter().cloned().collect::<BTreeSet<_>>(),
                        expected,
                        "allocation definition keys cannot erase scoped return-source instances"
                    );
                    if function == "fresh" {
                        assert!(!expected.is_empty());
                    } else {
                        assert!(expected.is_empty());
                    }
                }
                if function == "unrelated" {
                    assert!(facts.equations.iter().any(|row| row.operation == "source"
                        && row.point.function.as_deref() == Some(function)));
                    assert!(
                        matches!(certificate.source_anchor, Availability::Missing(_)),
                        "an unrelated allocation in the same SCC is not a return-route anchor"
                    );
                }
            }
        },
    );
}
