//! Frozen invocation checks. The real supervisor enforces elapsed wall time;
//! this component validates the sealed budget metadata, not a fake timeout.

pub(crate) const EMISSION_WALL_SECONDS: u64 = 900;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FrozenDigests {
    pub(crate) source: String,
    pub(crate) emitter: String,
    pub(crate) cache_inventory: String,
}

/// The caller samples its actual inventory and model-entry counter. This also
/// supports a supervisor reporting a child worker's counter rather than its own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Snapshot {
    pub(crate) digests: FrozenDigests,
    pub(crate) model_entries: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Phase {
    Before,
    After,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Component {
    Source,
    Emitter,
    CacheInventory,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Failure<E> {
    Budget {
        expected_seconds: u64,
        actual_seconds: u64,
    },
    Digest {
        phase: Phase,
        component: Component,
        expected: String,
        actual: String,
    },
    ModelEntries {
        before: usize,
        after: usize,
    },
    Invocation(E),
}

fn check_digests<E>(
    phase: Phase,
    expected: &FrozenDigests,
    actual: &FrozenDigests,
) -> Result<(), Failure<E>> {
    for (component, expected, actual) in [
        (Component::Source, &expected.source, &actual.source),
        (Component::Emitter, &expected.emitter, &actual.emitter),
        (
            Component::CacheInventory,
            &expected.cache_inventory,
            &actual.cache_inventory,
        ),
    ] {
        if expected != actual {
            return Err(Failure::Digest {
                phase,
                component,
                expected: expected.to_string(),
                actual: actual.to_string(),
            });
        }
    }
    Ok(())
}

/// Validate frozen inputs before invocation and reject drift afterward, even
/// when the supplied callback returns an error. The supervisor owns wall time.
pub(crate) fn guarded_invoke<T, E>(
    expected: &FrozenDigests,
    wall_seconds: u64,
    mut sample: impl FnMut() -> Snapshot,
    invoke: impl FnOnce() -> Result<T, E>,
) -> Result<T, Failure<E>> {
    if wall_seconds != EMISSION_WALL_SECONDS {
        return Err(Failure::Budget {
            expected_seconds: EMISSION_WALL_SECONDS,
            actual_seconds: wall_seconds,
        });
    }
    super::execution_guard::with_role(super::execution_guard::ExecutionRole::CacheOnly, || {
        let local_before = super::execution_guard::model_entries();
        let before = sample();
        check_digests(Phase::Before, expected, &before.digests)?;
        let outcome = invoke();
        let after = sample();
        check_digests(Phase::After, expected, &after.digests)?;
        if before.model_entries != after.model_entries {
            return Err(Failure::ModelEntries {
                before: before.model_entries,
                after: after.model_entries,
            });
        }
        let local_after = super::execution_guard::model_entries();
        if local_before != local_after {
            return Err(Failure::ModelEntries {
                before: local_before,
                after: local_after,
            });
        }
        outcome.map_err(Failure::Invocation)
    })
}

#[cfg(test)]
mod tests;
