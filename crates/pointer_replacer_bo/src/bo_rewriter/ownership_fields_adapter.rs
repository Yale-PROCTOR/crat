//! Pure adapter preparation. No cache IO, decoding, rustc identity collection,
//! or production registration. Native integration must supply a verified
//! manifest/record inventory and invocation binding after the seat's gate.
#[cfg(test)]
use std::collections::BTreeMap;
#[cfg(test)]
use std::collections::BTreeSet;

#[cfg(test)]
use super::emission::Grant;
#[cfg(test)]
use super::emission::GrantStatus;
#[cfg(test)]
use super::emission::Kind;
#[cfg(test)]
use super::export::*;
#[cfg(test)]
use super::lifecycle::CloseKind;

#[cfg(test)]
/// Supplied by the future accepted-artifact decoder. It must verify digests
/// from closed bytes, qualify frames and decode companion bodies by family.
#[derive(Clone, Debug)]
pub struct AcceptedInputs {
    pub manifest: Manifest,
    pub records: BTreeMap<RecordKey, FactFamily>,
    pub occurrences: Evidence<BTreeMap<DeclarationKey, Occurrence>>,
}

#[cfg(test)]
#[derive(Debug)]
pub struct Prepared<'a> {
    expected: &'a AcceptedInputs,
    rows: &'a [Row],
}
#[cfg(test)]
impl Prepared<'_> {}
