//! Local owning signatures and exact caller/formal contracts, over typed facts.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    EvidenceKey, OwnerId, SiteId,
    emission::{Grant, GrantStatus, Kind, OwnCallFacts, OwnerType, admit_call},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundaryType {
    Owner(OwnerType),
    Borrow {
        pointee: String,
        mutable: bool,
        optional: bool,
        lifetime: String,
    },
    Scalar(String),
}
impl BoundaryType {}
