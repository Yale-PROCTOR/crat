//! Injected callbacks only: no emitter, process, solver query or wall wait runs.
use std::cell::Cell;

use super::*;
use crate::analyses::borrow_ownership::execution_guard::{self, ExecutionRole, Operation, Refusal};

fn frozen() -> FrozenDigests {
    FrozenDigests {
        source: "1".repeat(64),
        emitter: "2".repeat(64),
        cache_inventory: "3".repeat(64),
    }
}
fn snapshot(digests: &FrozenDigests, model_entries: usize) -> Snapshot {
    Snapshot {
        digests: digests.clone(),
        model_entries,
    }
}

#[test]
fn e5_i16_frozen_read_only_invocation_runs_once() {
    let expected = frozen();
    let calls = Cell::new(0);
    let result = guarded_invoke(
        &expected,
        EMISSION_WALL_SECONDS,
        || snapshot(&expected, 0),
        || {
            calls.set(calls.get() + 1);
            Ok::<_, ()>(17)
        },
    );
    assert_eq!(result, Ok(17));
    assert_eq!(calls.get(), 1);
}

#[test]
fn e5_i16_source_and_emitter_mismatch_refuse_before_invocation() {
    for component in [Component::Source, Component::Emitter] {
        let expected = frozen();
        let mut actual = expected.clone();
        match component {
            Component::Source => actual.source = "4".repeat(64),
            Component::Emitter => actual.emitter = "4".repeat(64),
            Component::CacheInventory => unreachable!(),
        }
        let called = Cell::new(false);
        let result = guarded_invoke(
            &expected,
            EMISSION_WALL_SECONDS,
            || snapshot(&actual, 0),
            || {
                called.set(true);
                Ok::<_, ()>(())
            },
        );
        assert!(
            matches!(result, Err(Failure::Digest { phase: Phase::Before, component: observed, .. }) if observed == component)
        );
        assert!(!called.get());
    }
}

#[test]
fn e5_i16_post_source_and_cache_drift_reject_the_result() {
    for component in [Component::Source, Component::CacheInventory] {
        let expected = frozen();
        let samples = Cell::new(0);
        let calls = Cell::new(0);
        let result = guarded_invoke(
            &expected,
            EMISSION_WALL_SECONDS,
            || {
                let mut actual = expected.clone();
                if samples.get() > 0 {
                    match component {
                        Component::Source => actual.source = "5".repeat(64),
                        Component::CacheInventory => actual.cache_inventory = "5".repeat(64),
                        Component::Emitter => unreachable!(),
                    }
                }
                samples.set(samples.get() + 1);
                snapshot(&actual, 0)
            },
            || {
                calls.set(calls.get() + 1);
                Ok::<_, ()>(17)
            },
        );
        assert!(
            matches!(result, Err(Failure::Digest { phase: Phase::After, component: observed, .. }) if observed == component)
        );
        assert_eq!(calls.get(), 1);
    }
}

#[test]
fn e5_i16_reported_model_entry_change_rejects_the_result() {
    let expected = frozen();
    let samples = Cell::new(0);
    let result = guarded_invoke(
        &expected,
        EMISSION_WALL_SECONDS,
        || {
            let count = samples.get();
            samples.set(count + 1);
            snapshot(&expected, count)
        },
        || Ok::<_, ()>(()),
    );
    assert_eq!(
        result,
        Err(Failure::ModelEntries {
            before: 0,
            after: 1
        })
    );
}

#[test]
fn e5_i16_model_entry_is_blocked_inside_invocation() {
    execution_guard::with_role(ExecutionRole::Derive, || {
        let expected = frozen();
        let before = execution_guard::model_entries();
        let result = guarded_invoke(
            &expected,
            EMISSION_WALL_SECONDS,
            || snapshot(&expected, execution_guard::model_entries()),
            || execution_guard::enter_model(),
        );
        assert_eq!(
            result,
            Err(Failure::Invocation(Refusal {
                role: ExecutionRole::CacheOnly,
                operation: Operation::ModelEntry,
            }))
        );
        assert_eq!(execution_guard::model_entries(), before);
        assert_eq!(execution_guard::current_role(), ExecutionRole::Derive);
    });
}

#[test]
fn e5_i16_wall_budget_is_metadata_not_a_synchronous_timeout() {
    assert_eq!(EMISSION_WALL_SECONDS, 900);
    let expected = frozen();
    let called = Cell::new(false);
    let result = guarded_invoke(
        &expected,
        901,
        || snapshot(&expected, 0),
        || {
            called.set(true);
            Ok::<_, ()>(())
        },
    );
    assert_eq!(
        result,
        Err(Failure::Budget {
            expected_seconds: 900,
            actual_seconds: 901
        })
    );
    assert!(!called.get());
}
