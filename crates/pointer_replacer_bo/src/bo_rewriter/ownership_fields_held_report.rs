//! R347 all-held Box table over supplied ledger joins and custody observations.
//! No native lookup, parser, census or emission. The caller must import exact
//! ledger identities and observe the sealed tree; absence of grants alone is
//! never evidence of zero delivered Boxes.
use std::collections::{BTreeMap, BTreeSet};

use super::{adapter::AcceptedInputs, emission::Kind, export::*};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnitKey(pub String);
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeldRow {
    pub crown_form: String,
    pub emitted_form: String,
    pub reasons: Evidence<BTreeMap<DeclarationKey, Missing>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeldTable {
    pub source_hash: Digest,
    pub rows: BTreeMap<UnitKey, HeldRow>,
    pub emitted_boxes: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReportHold {
    Evidence(Missing),
    NotAllHeld(DeclarationKey),
    UnitInventory,
    CustodyFrame,
    EmptyJoin(UnitKey),
    ForeignDeclaration(UnitKey, DeclarationKey),
    UnexpectedGrant(DeclarationKey),
    UnexpectedBox(UnitKey),
}
impl From<Missing> for ReportHold {
    fn from(value: Missing) -> Self {
        Self::Evidence(value)
    }
}

impl HeldTable {}
