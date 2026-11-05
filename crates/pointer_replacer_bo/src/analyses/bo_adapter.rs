//! Narrow adapter for constructing production-shaped provenance sets for the BO fork.
//!
//! NB5-O keeps the production borrow analysis frozen while replacing the BO path's context and
//! constraint graph. This one function preserves the existing `ProvenanceSet` shape without making
//! `borrow_ownership/` name or widen the production construction trait.

use rustc_middle::mir::{Body, Local};

use super::borrow::{HasProvenanceSet, ProvenanceSet};

pub(crate) fn provenance_set<I, J>(body: &Body<'_>, is_candidate: I, is_mutable: J) -> ProvenanceSet
where
    I: Fn(Local) -> bool,
    J: Fn(Local) -> bool,
{
    body.provenance_set(is_candidate, is_mutable)
}
