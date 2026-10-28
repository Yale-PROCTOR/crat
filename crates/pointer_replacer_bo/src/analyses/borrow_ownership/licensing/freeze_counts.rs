//! Relay main/378 (R1324-1), test-only: counters on the licensing freeze's repeated work, read by
//! `freeze_fix_tests` (the session runs on one thread, so thread-locals suffice).

use std::{
    cell::{Cell, RefCell},
    collections::BTreeMap,
};

thread_local! {
    static CALL_GRAPH_BUILDS: Cell<usize> = const { Cell::new(0) };
    static READER_PLAN_BUILDS: Cell<usize> = const { Cell::new(0) };
    static GRANT_TERMINAL_SCANS: Cell<usize> = const { Cell::new(0) };
    static VALIDATE_RETURNS: RefCell<BTreeMap<(u32, String), usize>> = RefCell::new(BTreeMap::new());
}

pub(crate) fn reset() {
    CALL_GRAPH_BUILDS.with(|c| c.set(0));
    READER_PLAN_BUILDS.with(|c| c.set(0));
    GRANT_TERMINAL_SCANS.with(|c| c.set(0));
    VALIDATE_RETURNS.with(|c| c.borrow_mut().clear());
}

pub(crate) fn call_graph_built() {
    CALL_GRAPH_BUILDS.with(|c| c.set(c.get() + 1));
}

pub(crate) fn reader_plan_built() {
    READER_PLAN_BUILDS.with(|c| c.set(c.get() + 1));
}

pub(crate) fn grant_terminal_scanned() {
    GRANT_TERMINAL_SCANS.with(|c| c.set(c.get() + 1));
}

pub(crate) fn validate_returns_computed(construction: u32, function: &str) {
    VALIDATE_RETURNS.with(|c| {
        *c.borrow_mut()
            .entry((construction, function.to_owned()))
            .or_default() += 1
    });
}

pub(crate) fn call_graph_builds() -> usize {
    CALL_GRAPH_BUILDS.with(Cell::get)
}

pub(crate) fn reader_plan_builds() -> usize {
    READER_PLAN_BUILDS.with(Cell::get)
}

pub(crate) fn grant_terminal_scans() -> usize {
    GRANT_TERMINAL_SCANS.with(Cell::get)
}

pub(crate) fn validate_returns_computations() -> BTreeMap<(u32, String), usize> {
    VALIDATE_RETURNS.with(|c| c.borrow().clone())
}
