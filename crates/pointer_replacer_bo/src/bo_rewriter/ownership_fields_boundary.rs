//! Local owning signatures and exact caller/formal contracts, over typed facts.
#[cfg(test)]
use std::collections::BTreeMap;
#[cfg(test)]
use std::collections::BTreeSet;

#[cfg(test)]
use super::EvidenceKey;
#[cfg(test)]
use super::OwnerId;
#[cfg(test)]
use super::SiteId;
#[cfg(test)]
use super::emission::Grant;
#[cfg(test)]
use super::emission::GrantStatus;
#[cfg(test)]
use super::emission::Kind;
#[cfg(test)]
use super::emission::OwnCallFacts;
#[cfg(test)]
use super::emission::OwnerType;
#[cfg(test)]
use super::emission::admit_call;

#[cfg(test)]
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
#[cfg(test)]
impl BoundaryType {}
