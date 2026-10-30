//! The query budget, the typed Unknown channel and the model-entry counter.

use super::*;
use crate::analyses::borrow_ownership::model_cache;

#[test]
fn e5_i_guard_model_entries_are_actual_entries_not_builds_or_memo_materializations() {
    let before = model_entries();
    let old_memo_counter = model_cache::derivations();
    enter_model();
    assert_eq!(model_entries(), before + 1, "one outer model entry");
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

/// Relay main/388 (R1370-1): unset, the timeout in force is the sealed 600_000 exactly; a set value
/// is honoured; an unparsable one is the sealed cap.
#[test]
fn r1370_the_query_timeout_is_the_sealed_cap_unset_and_the_switch_value_when_set() {
    assert_eq!(timeout_from(None), 600_000);
    assert_eq!(timeout_from(Some("1800000")), 1_800_000);
    assert_eq!(timeout_from(Some("ten minutes")), QUERY_TIMEOUT_MS);
    if std::env::var_os("CRAT_BO_QUERY_TIMEOUT_MS").is_none() {
        assert_eq!(
            query_timeout_ms(),
            QUERY_TIMEOUT_MS,
            "the gate's process sets nothing"
        );
    }
}
