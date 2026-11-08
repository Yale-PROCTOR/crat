//! Query-budget receipts for the analysis: the fixed per-query timeout, the
//! typed Unknown channel, and the count of outer model derivations (distinct
//! from memo/cache materialization counts).

use std::cell::{Cell, RefCell};

pub(crate) const QUERY_TIMEOUT_MS: u32 = 600_000;

/// Relay main/388 (R1370-1): the per-query timeout in force -- `CRAT_BO_QUERY_TIMEOUT_MS` when set
/// (a measurement switch, for a run the user's word names only; never in a gate, never on the 17
/// or the 376, and not part of the model cache's key), else [`QUERY_TIMEOUT_MS`] exactly. Read once.
pub(crate) fn query_timeout_ms() -> u32 {
    static TIMEOUT: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *TIMEOUT.get_or_init(|| timeout_from(std::env::var("CRAT_BO_QUERY_TIMEOUT_MS").ok().as_deref()))
}

/// R1475-2 (4): whether each solve's hard checks run on a hard solver built at that solve's start
/// from the Optimize's assertions as they stand, the previous solve's solver dropped first --
/// `CRAT_BO_FRESH_HARD_SOLVER=on` (a measurement switch, for a run the user's word names only;
/// never in a gate, never on the 17 or the 376, and not part of the model cache's key). Unset, or
/// any other value: one hard solver per repair, synchronized at each solve. Read once.
pub(crate) fn fresh_hard_solver() -> bool {
    #[cfg(test)]
    if let Some(on) = fresh_hard_solver_hook::get() {
        return on;
    }
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| fresh_from(std::env::var("CRAT_BO_FRESH_HARD_SOLVER").ok().as_deref()))
}

/// [`fresh_hard_solver`]'s reading of the variable's value: `on` exactly, else off.
fn fresh_from(value: Option<&str>) -> bool {
    value == Some("on")
}

/// The test hook for [`fresh_hard_solver`] (tests never set the process environment).
#[cfg(test)]
pub(crate) mod fresh_hard_solver_hook {
    thread_local! {
        static SET: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
    }
    pub(super) fn get() -> Option<bool> {
        SET.with(std::cell::Cell::get)
    }
    /// Run `f` with the switch read as `on`.
    pub(crate) fn with<T>(on: bool, f: impl FnOnce() -> T) -> T {
        struct Reset(Option<bool>);
        impl Drop for Reset {
            fn drop(&mut self) {
                SET.with(|set| set.set(self.0));
            }
        }
        let _reset = Reset(SET.with(|set| set.replace(Some(on))));
        f()
    }
}

/// R1490-2 (main 326 §5): the two-process checkpoint mode's paths, `(out, in)` --
/// `CRAT_BO_CHECKPOINT_OUT=<path>` (process 1 writes the baseline checkpoint and ends `checkpointed`)
/// and `CRAT_BO_CHECKPOINT_IN=<path>` (process 2 resumes from it at the precise stage). Measurement
/// switches, for a run the user's word names only; never in a gate, never on the 17 or the 376, off
/// by default, and not part of the model cache's key. An empty value is unset. Read once.
pub(crate) fn checkpoint_paths() -> (Option<std::path::PathBuf>, Option<std::path::PathBuf>) {
    #[cfg(test)]
    if let Some(paths) = checkpoint_hook::get() {
        return paths;
    }
    static PATHS: std::sync::OnceLock<(Option<std::path::PathBuf>, Option<std::path::PathBuf>)> =
        std::sync::OnceLock::new();
    PATHS
        .get_or_init(|| {
            checkpoint_paths_from(
                std::env::var_os("CRAT_BO_CHECKPOINT_OUT"),
                std::env::var_os("CRAT_BO_CHECKPOINT_IN"),
            )
        })
        .clone()
}

/// [`checkpoint_paths`]'s reading of the two values: a path each, an empty value unset.
fn checkpoint_paths_from(
    out: Option<std::ffi::OsString>,
    input: Option<std::ffi::OsString>,
) -> (Option<std::path::PathBuf>, Option<std::path::PathBuf>) {
    let read = |value: Option<std::ffi::OsString>| {
        value
            .filter(|value| !value.is_empty())
            .map(std::path::PathBuf::from)
    };
    (read(out), read(input))
}

/// The test hook for [`checkpoint_paths`] (tests never set the process environment in-process).
#[cfg(test)]
pub(crate) mod checkpoint_hook {
    type Paths = (Option<std::path::PathBuf>, Option<std::path::PathBuf>);
    thread_local! {
        static SET: std::cell::RefCell<Option<Paths>> = const { std::cell::RefCell::new(None) };
    }
    pub(super) fn get() -> Option<Paths> {
        SET.with(|set| set.borrow().clone())
    }
    /// Run `f` with the switches read as `paths`.
    pub(crate) fn with<T>(paths: Paths, f: impl FnOnce() -> T) -> T {
        struct Reset(Option<Paths>);
        impl Drop for Reset {
            fn drop(&mut self) {
                SET.with(|set| *set.borrow_mut() = self.0.take());
            }
        }
        let _reset = Reset(SET.with(|set| set.borrow_mut().replace(paths)));
        f()
    }
}

/// Relay main/388 O2 (R1382-1 / R1383-1): whether a query's own wall reached the per-query budget in
/// force -- at least 0.99 of it, for z3's timer granularity. Keyed on the wall, never on z3's reason
/// string, which read "no reason given" at every measured timeout (main 281 / 282).
pub(crate) fn budget_hit(wall: std::time::Duration) -> bool {
    budget_hit_at(wall.as_secs_f64() * 1000.0, query_timeout_ms())
}

fn budget_hit_at(wall_ms: f64, budget_ms: u32) -> bool {
    wall_ms >= 0.99 * f64::from(budget_ms)
}

thread_local! {
    static INCUMBENTS: Cell<usize> = const { Cell::new(0) };
}

/// Relay main/388 O2: one optimize incumbent accepted as a round's model, on this thread.
pub(crate) fn note_incumbent_accepted() {
    INCUMBENTS.with(|count| count.set(count.get().saturating_add(1)));
}

fn incumbents_accepted() -> usize {
    INCUMBENTS.with(Cell::get)
}

/// Relay main/388 O2 (R1383-1 R2): runs one solve and says whether its final model may be written to
/// the model cache -- `cacheable`, and no round of the solve, in any of its verifications, accepted an
/// incumbent. An incumbent depends on the machine and its load; no key restores determinism.
pub(crate) fn solve_then_cacheable<R>(cacheable: bool, solve: impl FnOnce() -> R) -> (R, bool) {
    let before = incumbents_accepted();
    let result = solve();
    (result, cacheable && incumbents_accepted() == before)
}

/// [`query_timeout_ms`]'s reading of the variable's value, as `CRAT_BO_GUARD_BUDGET` is read:
/// unset or not a `u32`, the sealed cap.
fn timeout_from(value: Option<&str>) -> u32 {
    value
        .and_then(|value| value.parse().ok())
        .unwrap_or(QUERY_TIMEOUT_MS)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum QueryStage {
    HardCheck,
    HardTrackedRecheck,
    #[cfg(test)]
    Restoration,
    OptimizeCheck,
    OptimizeMaterialization,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct QueryUnknown {
    pub(crate) stage: QueryStage,
    /// None is an unavailable reason, not an invented timeout classification.
    pub(crate) reason: Option<String>,
}

thread_local! {
    static MODEL_ENTRIES: Cell<usize> = const { Cell::new(0) };
    static LAST_UNKNOWN: RefCell<Option<QueryUnknown>> = const { RefCell::new(None) };
}

/// One outer model derivation, not each internal baseline/overlap solver instance.
pub(crate) fn enter_model() {
    MODEL_ENTRIES.with(|entries| {
        entries.set(
            entries
                .get()
                .checked_add(1)
                .expect("model-entry counter overflow"),
        );
    });
}

/// This counter deliberately does not reuse model_cache::derivations(), whose
/// historical contract includes memo insertions after cache loads.
#[cfg(test)]
pub(crate) fn model_entries() -> usize {
    MODEL_ENTRIES.with(Cell::get)
}

/// Actual query Unknown only; an ordinary analysis decline never writes this.
#[cfg(test)]
pub(crate) fn last_unknown() -> Option<QueryUnknown> {
    LAST_UNKNOWN.with(|unknown| unknown.borrow().clone())
}

#[cfg(test)]
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
