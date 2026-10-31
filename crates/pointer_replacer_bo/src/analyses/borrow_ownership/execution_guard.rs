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
