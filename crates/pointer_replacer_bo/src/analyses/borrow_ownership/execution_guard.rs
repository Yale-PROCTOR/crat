//! Query-budget receipts for the analysis: the fixed per-query timeout, the
//! typed Unknown channel, and the count of outer model derivations (distinct
//! from memo/cache materialization counts).

use std::cell::{Cell, RefCell};

pub(crate) const QUERY_TIMEOUT_MS: u32 = 600_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum QueryStage {
    HardCheck,
    HardTrackedRecheck,
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

/// One outer model derivation, not each internal baseline/A5 solver instance.
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
