//! Scoped execution policy and query-budget receipts for the era5a pipeline.
//! Cache-only scopes refuse model construction and queries before they start.
//! Model-entry counts are distinct from memo/cache materialization counts.

use std::{
    cell::{Cell, RefCell},
    fmt,
};

pub(crate) const QUERY_TIMEOUT_MS: u32 = 600_000;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum ExecutionRole {
    #[default]
    Derive,
    CacheOnly,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RoleParseError {
    pub(crate) value: String,
}

/// Strict execution policy, deliberately separate from model semantic identity.
/// This pure parser does not read or mutate the environment.
pub(crate) fn parse_role(value: Option<&str>) -> Result<ExecutionRole, RoleParseError> {
    match value {
        None | Some("derive") => Ok(ExecutionRole::Derive),
        Some("cache-only") => Ok(ExecutionRole::CacheOnly),
        Some(value) => Err(RoleParseError {
            value: value.to_owned(),
        }),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum QueryStage {
    HardCheck,
    HardTrackedRecheck,
    Restoration,
    OptimizeCheck,
    OptimizeMaterialization,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Operation {
    ReadOnly,
    SolverBuild,
    ModelEntry,
    Query(QueryStage),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Refusal {
    pub(crate) role: ExecutionRole,
    pub(crate) operation: Operation,
}

impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "execution role {:?} refuses {:?}",
            self.role, self.operation
        )
    }
}
impl std::error::Error for Refusal {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct QueryUnknown {
    pub(crate) stage: QueryStage,
    /// None is an unavailable reason, not an invented timeout classification.
    pub(crate) reason: Option<String>,
}

thread_local! {
    static ROLE: Cell<Option<ExecutionRole>> = const { Cell::new(None) };
    static MODEL_ENTRIES: Cell<usize> = const { Cell::new(0) };
    static LAST_UNKNOWN: RefCell<Option<QueryUnknown>> = const { RefCell::new(None) };
}

pub(crate) fn current_role() -> ExecutionRole {
    if let Some(role) = ROLE.with(Cell::get) {
        return role;
    }
    let role = match std::env::var("CRAT_ERA5_EXECUTION_ROLE") {
        Ok(value) => parse_role(Some(&value)),
        Err(std::env::VarError::NotPresent) => parse_role(None),
        Err(std::env::VarError::NotUnicode(value)) => Err(RoleParseError {
            value: format!("{value:?}"),
        }),
    };
    match role {
        Ok(role) => role,
        Err(error) => std::panic::panic_any(error),
    }
}

/// Nested scopes restore their caller's role, including when a refusal unwinds.
/// No process-global environment or Z3 setting is changed by this carrier.
pub(crate) fn with_role<T>(role: ExecutionRole, run: impl FnOnce() -> T) -> T {
    struct Restore(Option<ExecutionRole>);
    impl Drop for Restore {
        fn drop(&mut self) {
            ROLE.with(|role| role.set(self.0));
        }
    }
    let _restore = Restore(ROLE.with(|current| current.replace(Some(role))));
    run()
}

pub(crate) fn check(operation: Operation) -> Result<(), Refusal> {
    let role = current_role();
    if role == ExecutionRole::CacheOnly && operation != Operation::ReadOnly {
        Err(Refusal { role, operation })
    } else {
        Ok(())
    }
}

/// Compatibility barrier for APIs such as KindSolver::build that return Self.
/// Normal model entrances should return check/enter_model's typed error instead.
pub(crate) fn require(operation: Operation) {
    if let Err(refusal) = check(operation) {
        std::panic::panic_any(refusal);
    }
}

pub(crate) fn guarded<T>(operation: Operation, run: impl FnOnce() -> T) -> Result<T, Refusal> {
    check(operation)?;
    Ok(run())
}

/// One outer model derivation, not each internal baseline/A5 solver instance.
pub(crate) fn enter_model() -> Result<(), Refusal> {
    check(Operation::ModelEntry)?;
    MODEL_ENTRIES.with(|entries| {
        entries.set(
            entries
                .get()
                .checked_add(1)
                .expect("model-entry counter overflow"),
        );
    });
    Ok(())
}

/// This counter deliberately does not reuse model_cache::derivations(), whose
/// historical contract includes memo insertions after cache loads.
pub(crate) fn model_entries() -> usize {
    MODEL_ENTRIES.with(Cell::get)
}

/// Actual query Unknown only; an ordinary analysis decline never writes this.
pub(crate) fn last_unknown() -> Option<QueryUnknown> {
    LAST_UNKNOWN.with(|unknown| unknown.borrow().clone())
}

pub(crate) fn clear_unknown() {
    LAST_UNKNOWN.with(|unknown| *unknown.borrow_mut() = None);
}

pub(crate) fn known_query_result(
    stage: QueryStage,
    outcome: z3::SatResult,
    reason: Option<String>,
) -> Result<z3::SatResult, QueryUnknown> {
    match outcome {
        z3::SatResult::Unknown => {
            let unknown = QueryUnknown { stage, reason };
            LAST_UNKNOWN.with(|last| *last.borrow_mut() = Some(unknown.clone()));
            Err(unknown)
        }
        known => Ok(known),
    }
}

#[cfg(test)]
mod tests;
