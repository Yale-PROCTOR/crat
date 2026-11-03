//! P2d scalar-read planning over a resolved argument list.
use std::collections::BTreeSet;

use super::{EvidenceKey, SiteId};

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
impl Argument {}
