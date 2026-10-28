//! **Index-range disjointness** (relay era-5c/267, R1325-1; the design is
//! era-5c report 218): the RED-first scaffold. The types and the table's API the
//! witnesses read; nothing is computed and nothing is discharged, so the engine
//! behaves exactly as at `e10437227`.

use std::collections::BTreeSet;

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{Local, Location};

use crate::utils::rustc::RustProgram;

/// A consequence of §28 a bound rests on.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Premise {
    InBoundsOffset,
    IndexStepNoWrap,
    UsizeAsIsize,
}

/// `coef · n + add`, with `n` the integer formal of argument index `formal`, or
/// the constant `add`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Bound {
    pub(crate) formal: Option<u32>,
    pub(crate) coef: i64,
    pub(crate) add: i64,
}

impl Bound {
    pub(crate) const fn constant(add: i64) -> Self {
        Bound {
            formal: None,
            coef: 0,
            add,
        }
    }
}

/// What a value reaches, relative to its base.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Footprint {
    Empty,
    Bytes(Bytes),
    Unknown(&'static str),
}

/// `[lo, hi)` bytes from the base.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Bytes {
    pub(crate) lo: Bound,
    pub(crate) hi: Bound,
    pub(crate) writes: bool,
    pub(crate) premises: BTreeSet<Premise>,
    pub(crate) summaries: rustc_hash::FxHashSet<(LocalDefId, u32)>,
}

/// One discharged invalidation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RangeDisjoint {
    pub(crate) function: LocalDefId,
    pub(crate) access: Location,
    pub(crate) loan: Location,
    pub(crate) issuer: Local,
    pub(crate) base: Local,
    pub(crate) loan_bytes: Option<(i64, i64)>,
    pub(crate) loan_writes: bool,
    pub(crate) access_bytes: Option<(i64, i64)>,
    pub(crate) access_writes: bool,
    pub(crate) summaries: Vec<(LocalDefId, u32)>,
    pub(crate) premises: Vec<&'static str>,
}

/// Every receipt recorded on this thread since the last call.
#[cfg(test)]
pub(crate) fn take_receipts() -> Vec<RangeDisjoint> {
    Vec::new()
}

/// The bound sum, for the domain's unit tests.
#[cfg(test)]
pub(crate) fn test_plus(_a: Bound, _b: Bound) -> Option<Bound> {
    None
}

/// Per program: nothing yet.
pub(crate) struct IndexRanges;

impl IndexRanges {
    pub(crate) fn build(_program: &RustProgram<'_>) -> IndexRanges {
        IndexRanges
    }

    /// `Ext(g, k)`.
    pub(crate) fn ext(&self, _function: LocalDefId, _formal: u32) -> Footprint {
        Footprint::Unknown("not-built")
    }

    /// A local's base and footprint in `function`.
    #[cfg(test)]
    pub(crate) fn family(
        &self,
        _function: LocalDefId,
        _local: Local,
    ) -> Option<(Local, Footprint)> {
        None
    }
}
