//! Injected execution controls plus a real compiler/KindSolver construction
//! boundary. No test invokes a real solver query under CacheOnly.

use std::{
    cell::Cell,
    panic::{AssertUnwindSafe, catch_unwind},
};

use rustc_hir::{ItemKind, OwnerNode};

use super::*;
use crate::{
    analyses::borrow_ownership::{crate_slots::CrateSlots, model_cache, solver::KindSolver},
    utils::rustc::RustProgram,
};

#[test]
fn e5_i_guard_cache_only_refuses_before_injected_model_operations() {
    with_role(ExecutionRole::CacheOnly, || {
        for operation in [
            Operation::SolverBuild,
            Operation::ModelEntry,
            Operation::Query(QueryStage::OptimizeMaterialization),
        ] {
            let called = Cell::new(false);
            let outcome = guarded(operation, || called.set(true));
            assert_eq!(
                outcome,
                Err(Refusal {
                    role: ExecutionRole::CacheOnly,
                    operation
                })
            );
            assert!(
                !called.get(),
                "rejection must precede the operation, not follow it"
            );
        }
        assert_eq!(guarded(Operation::ReadOnly, || 17), Ok(17));
    });
}

#[test]
fn e5_i_guard_model_entries_are_actual_entries_not_builds_or_memo_materializations() {
    let before = model_entries();
    let old_memo_counter = model_cache::derivations();
    with_role(ExecutionRole::Derive, || {
        enter_model().expect("permitted production model entry");
        guarded(Operation::SolverBuild, || ()).unwrap();
        guarded(Operation::SolverBuild, || ()).unwrap();
        assert_eq!(
            model_entries(),
            before + 1,
            "the internal baseline and candidate do not count as two new model entries"
        );
    });
    with_role(ExecutionRole::CacheOnly, || {
        assert_eq!(
            enter_model(),
            Err(Refusal {
                role: ExecutionRole::CacheOnly,
                operation: Operation::ModelEntry,
            })
        );
    });
    assert_eq!(
        model_entries(),
        before + 1,
        "refused entry must not increment"
    );
    assert_eq!(
        model_cache::derivations(),
        old_memo_counter,
        "the existing memo/cache-load counter has a different contract"
    );
}

#[test]
fn e5_i_guard_fixed_query_cap_and_typed_unknown_do_not_invent_outcomes() {
    assert_eq!(QUERY_TIMEOUT_MS, 600_000, "sealed I12 query budget");
    for stage in [
        QueryStage::HardCheck,
        QueryStage::HardTrackedRecheck,
        QueryStage::Restoration,
        QueryStage::OptimizeCheck,
        QueryStage::OptimizeMaterialization,
    ] {
        assert_eq!(
            known_query_result(stage, z3::SatResult::Sat, None),
            Ok(z3::SatResult::Sat)
        );
        assert_eq!(
            known_query_result(stage, z3::SatResult::Unsat, None),
            Ok(z3::SatResult::Unsat)
        );
        assert_eq!(
            known_query_result(stage, z3::SatResult::Unknown, Some("timeout".to_owned())),
            Err(QueryUnknown {
                stage,
                reason: Some("timeout".to_owned())
            })
        );
        assert_eq!(
            known_query_result(stage, z3::SatResult::Unknown, None),
            Err(QueryUnknown {
                stage,
                reason: None
            })
        );
    }
}

#[test]
fn e5_i_guard_scope_restores_role_after_unwind_without_environment_changes() {
    let original = current_role();
    with_role(ExecutionRole::Derive, || {
        let result = catch_unwind(AssertUnwindSafe(|| {
            with_role(ExecutionRole::CacheOnly, || {
                assert_eq!(current_role(), ExecutionRole::CacheOnly);
                panic!("injected scoped unwind");
            })
        }));
        assert!(result.is_err());
        assert_eq!(current_role(), ExecutionRole::Derive);
        assert!(check(Operation::SolverBuild).is_ok());
    });
    assert_eq!(current_role(), original);
}

#[test]
fn e5_i_guard_actual_kind_solver_build_rejects_cache_only_before_any_query() {
    ::utils::compilation::run_compiler_on_str(
        "pub unsafe fn identity(p: *mut u8) -> *mut u8 { p }",
        |tcx| {
            let mut functions = Vec::new();
            let mut structs = Vec::new();
            for owner in tcx.hir_crate(()).owners.iter() {
                let Some(owner) = owner.as_owner() else { continue };
                let OwnerNode::Item(item) = owner.node() else { continue };
                match item.kind {
                    ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                    ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                    _ => {}
                }
            }
            let program = RustProgram {
                tcx,
                functions,
                structs,
            };
            let slots = CrateSlots::build(&program);
            let before = model_entries();
            let result = catch_unwind(AssertUnwindSafe(|| {
                with_role(ExecutionRole::CacheOnly, || {
                    // Construction only. There is deliberately no check/model call here.
                    let _solver = KindSolver::new(&slots);
                })
            }));
            let refusal = match result {
                Ok(()) => panic!("cache-only unexpectedly entered actual KindSolver construction"),
                Err(payload) => match payload.downcast::<Refusal>() {
                    Ok(refusal) => *refusal,
                    Err(_) => {
                        panic!("an unrelated compiler/solver panic is not a typed guard refusal")
                    }
                },
            };
            assert_eq!(
                refusal,
                Refusal {
                    role: ExecutionRole::CacheOnly,
                    operation: Operation::SolverBuild
                }
            );
            assert_eq!(model_entries(), before);
        },
    )
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn e5_i_guard_last_unknown_records_only_actual_unknown_and_clears() {
    clear_unknown();
    assert_eq!(last_unknown(), None);
    assert_eq!(
        known_query_result(QueryStage::HardCheck, z3::SatResult::Sat, None),
        Ok(z3::SatResult::Sat)
    );
    assert_eq!(
        last_unknown(),
        None,
        "ordinary outcomes are not query Unknown"
    );
    let first = QueryUnknown {
        stage: QueryStage::HardTrackedRecheck,
        reason: Some("timeout at tracked core recovery".to_owned()),
    };
    assert_eq!(
        known_query_result(first.stage, z3::SatResult::Unknown, first.reason.clone()),
        Err(first.clone())
    );
    assert_eq!(
        last_unknown(),
        Some(first.clone()),
        "retain the exact actual stage and reason"
    );
    assert_eq!(
        known_query_result(QueryStage::Restoration, z3::SatResult::Unsat, None),
        Ok(z3::SatResult::Unsat)
    );
    assert_eq!(
        last_unknown(),
        Some(first),
        "a later ordinary result must not rewrite Unknown evidence"
    );
    let missing_reason = QueryUnknown {
        stage: QueryStage::OptimizeMaterialization,
        reason: None,
    };
    assert_eq!(
        known_query_result(missing_reason.stage, z3::SatResult::Unknown, None),
        Err(missing_reason.clone())
    );
    assert_eq!(
        last_unknown(),
        Some(missing_reason),
        "missing reason stays missing, not a guessed timeout"
    );
    clear_unknown();
    assert_eq!(
        last_unknown(),
        None,
        "new worker/model scope can explicitly clear stale evidence"
    );
}

#[test]
fn e5_i_guard_ambient_role_parser_is_strict() {
    assert_eq!(parse_role(None), Ok(ExecutionRole::Derive));
    assert_eq!(parse_role(Some("derive")), Ok(ExecutionRole::Derive));
    assert_eq!(parse_role(Some("cache-only")), Ok(ExecutionRole::CacheOnly));
    for value in [
        "",
        "cache_only",
        "CACHE-ONLY",
        " cache-only",
        "cache-only ",
        "unknown",
    ] {
        assert_eq!(
            parse_role(Some(value)),
            Err(RoleParseError {
                value: value.to_owned()
            })
        );
    }
}
