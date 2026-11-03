//! P2d scalar-read planning over a resolved argument list.
#[cfg(test)]
use std::collections::BTreeSet;

#[cfg(test)]
use super::EvidenceKey;
#[cfg(test)]
use super::SiteId;

#[cfg(test)]
#[derive(Clone, Debug)]
pub enum Argument {
    ScalarRead {
        key: EvidenceKey,
        expression: String,
    },
    Consume {
        key: EvidenceKey,
        expression: String,
    },
    Other {
        site: SiteId,
        expression: String,
    },
}
#[cfg(test)]
impl Argument {}
