//! Pure adapter preparation. No cache IO, decoding, rustc identity collection,
//! or production registration. Native integration must supply a verified
//! manifest/record inventory and invocation binding after the seat's gate.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    emission::{Grant, GrantStatus, Kind},
    export::*,
    lifecycle::CloseKind,
};

/// Supplied by the future accepted-artifact decoder. It must verify digests
/// from closed bytes, qualify frames and decode companion bodies by family.
#[derive(Clone, Debug)]
pub struct AcceptedInputs {
    pub manifest: Manifest,
    pub records: BTreeMap<RecordKey, FactFamily>,
    pub occurrences: Evidence<BTreeMap<DeclarationKey, Occurrence>>,
}

#[derive(Debug)]
pub struct Prepared<'a> {
    expected: &'a AcceptedInputs,
    rows: &'a [Row],
}
impl Prepared<'_> {}
