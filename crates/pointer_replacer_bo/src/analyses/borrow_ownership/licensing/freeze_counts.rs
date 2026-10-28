//! Relay main/378 (R1324-1), test-only: counters on the licensing freeze's repeated work, read by
//! `freeze_fix_tests` (the session runs on one thread, so thread-locals suffice).

use std::{
    cell::{Cell, RefCell},
    collections::BTreeMap,
};

thread_local! {
    static CALL_GRAPH_BUILDS: Cell<usize> = const { Cell::new(0) };
    static READER_PLAN_BUILDS: Cell<usize> = const { Cell::new(0) };
    static VALIDATE_RETURNS: RefCell<BTreeMap<(u32, String), usize>> = RefCell::new(BTreeMap::new());
    static REFERENCE_SCANS: Cell<bool> = const { Cell::new(false) };
    static WASTED_CONSUMES: Cell<usize> = const { Cell::new(0) };
    static WASTED_EDGES: Cell<usize> = const { Cell::new(0) };
    static WASTED_RELATIONS: Cell<usize> = const { Cell::new(0) };
    static RESWEPT: Cell<usize> = const { Cell::new(0) };
    static RECLONED: Cell<usize> = const { Cell::new(0) };
    static REPEATED: Cell<usize> = const { Cell::new(0) };
}

/// Relay main/379 (matched, step 1): the old whole-collection scans, selected for an equality
/// witness. Off by default.
pub(crate) fn set_reference_scans(on: bool) {
    REFERENCE_SCANS.with(|c| c.set(on));
}

pub(crate) fn reference_scans() -> bool {
    REFERENCE_SCANS.with(Cell::get)
}

/// A consume examined for an `equal` equation of another (construction, function, block).
pub(crate) fn consume_wasted() {
    WASTED_CONSUMES.with(|c| c.set(c.get() + 1));
}

/// An edge examined by `paths` that does not leave the popped node.
pub(crate) fn edge_wasted() {
    WASTED_EDGES.with(|c| c.set(c.get() + 1));
}

/// A relation examined for a call whose callee is another scope.
pub(crate) fn relation_wasted() {
    WASTED_RELATIONS.with(|c| c.set(c.get() + 1));
}

pub(crate) fn wasted() -> (usize, usize, usize) {
    (
        WASTED_CONSUMES.with(Cell::get),
        WASTED_EDGES.with(Cell::get),
        WASTED_RELATIONS.with(Cell::get),
    )
}

/// A function swept again by the relation fixpoint although none of its callees gained a
/// relation in the round before.
pub(crate) fn function_reswept() {
    RESWEPT.with(|c| c.set(c.get() + 1));
}

/// `base` cloned whole by the relation fixpoint after its first round.
pub(crate) fn base_recloned() {
    RECLONED.with(|c| c.set(c.get() + 1));
}

/// Relay main/382 (b): a relation pushed a second time in one round of the relation fixpoint.
pub(crate) fn relation_repeated() {
    REPEATED.with(|c| c.set(c.get() + 1));
}

pub(crate) fn repeats() -> usize {
    REPEATED.with(Cell::get)
}

pub(crate) fn fixpoint_wasted() -> (usize, usize) {
    (RESWEPT.with(Cell::get), RECLONED.with(Cell::get))
}

pub(crate) fn reset() {
    CALL_GRAPH_BUILDS.with(|c| c.set(0));
    READER_PLAN_BUILDS.with(|c| c.set(0));
    VALIDATE_RETURNS.with(|c| c.borrow_mut().clear());
    WASTED_CONSUMES.with(|c| c.set(0));
    WASTED_EDGES.with(|c| c.set(0));
    WASTED_RELATIONS.with(|c| c.set(0));
    RESWEPT.with(|c| c.set(0));
    RECLONED.with(|c| c.set(0));
    REPEATED.with(|c| c.set(0));
}

pub(crate) fn call_graph_built() {
    CALL_GRAPH_BUILDS.with(|c| c.set(c.get() + 1));
}

pub(crate) fn reader_plan_built() {
    READER_PLAN_BUILDS.with(|c| c.set(c.get() + 1));
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

pub(crate) fn validate_returns_computations() -> BTreeMap<(u32, String), usize> {
    VALIDATE_RETURNS.with(|c| c.borrow().clone())
}
