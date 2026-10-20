//! Compiler-backed cursor admission instrument, not a production admission gate.
//! The caller supplies the frozen BO prerequisite; this module derives the
//! stronger retained-region obligations from MIR without querying a solver.

use std::collections::BTreeMap;

use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Body, Local},
    ty::TyCtxt,
};

#[path = "admission/compiler.rs"]
mod compiler;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModelKind {
    Ref,
    Raw,
    Owning,
    Missing,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Candidate {
    pub local: Local,
    pub slot_depth: usize,
    pub model_kind: ModelKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Shape {
    LocalArray,
    BorrowedSlice,
    RawParameter,
    PointerTableLoad,
    ProjectionLoad,
    MultipleRoots,
    Opaque,
    NullOnly,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Status {
    DecisionOnly,
    NeedsFact,
    OutOfScope,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Predicate {
    RetainedBase,
    GenerationWindow,
    RawEntryPrefix,
    FullRegionSchedule,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Need {
    BaseOrigin,
    /// A cursor rooted at a raw PARAMETER begins at the pointer it was handed,
    /// so it has no region below that position: an observed backward offset is
    /// a base origin this shape cannot supply, not merely one nothing derived.
    EntryWindow,
    Generation,
    Prefix,
    Schedule,
    RefAdmission,
    Initialization,
    WindowCoverage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unsupported {
    PointerDepth,
    Layout,
    Operation,
    EscapedStorage,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Proven,
    Missing(Need),
    Unsupported(Unsupported),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Site {
    pub block: usize,
    pub statement: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Finding {
    pub predicate: Predicate,
    pub outcome: Outcome,
    pub root: Option<Local>,
    pub site: Option<Site>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Admission {
    pub owner: LocalDefId,
    pub local: Local,
    pub shape: Shape,
    pub status: Status,
    /// Null literal or is_null use observed; false is not a nonnull proof.
    pub nullable: bool,
    /// Every raw local in this component must have frozen Ref authority. All
    /// accesses must be lowered with one base and administrative index copies.
    pub component: Vec<Local>,
    /// A numeric rendering of the array length when available. None on a
    /// proven local array means its typed compiler length is symbolic, not
    /// missing evidence or a fabricated extent. The root identifies that type.
    pub base_elements: Option<u64>,
    pub findings: [Finding; 4],
}

pub fn inspect<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &Body<'tcx>,
    candidate: Candidate,
    model_kinds: &BTreeMap<Local, ModelKind>,
) -> Admission {
    compiler::inspect(tcx, owner, body, candidate, model_kinds)
}

pub fn counts(rows: &[Admission]) -> BTreeMap<(Shape, Status), usize> {
    let mut counts = BTreeMap::new();
    for row in rows {
        *counts.entry((row.shape, row.status)).or_default() += 1;
    }
    counts
}
