//! field access events and rejects recorded on pointer-flow nodes, plus the
//! per-parameter query layer. events are flat lists in MIR-walk order; per-node
//! lookup is a linear filter, acceptable at per-body event counts.

use rustc_abi::FieldIdx;
use rustc_middle::mir::Location;

use crate::analyses::pointer_flow::graph::PfgNode;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldAccess {
    pub node: PfgNode,
    pub field: FieldIdx,
    pub kind: FieldAccessKind,
    pub location: Location,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FieldAccessKind {
    Read,
    Write,
    Address,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldAccessReject {
    pub node: PfgNode,
    pub kind: FieldAccessRejectKind,
    pub location: Location,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FieldAccessRejectKind {
    WholeStructUse,
    UnknownCallee,
    IncompleteCalleeSummary,
    EscapesToMemory,
    Returned,
    PointerArithmetic,
    IncompatibleCast,
    UnionFieldAccess,
}
