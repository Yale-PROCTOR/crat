//! Compare final parser/type observations with field-interface application.
//! Observations must come from the sealed emitted tree, not the edit plan.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    FieldClassId,
    transaction::{ClassId, Finalization, StructInterface},
};

#[derive(Clone, Debug)]
pub struct Observation {
    pub source_hash: [u8; 32],
    pub field_types: BTreeMap<FieldClassId, String>,
    pub lifetimes: Vec<String>,
    pub has_copy_clone: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CustodyError {
    SourceHash,
    FieldIdentity,
    FieldType(FieldClassId),
    Lifetimes,
    CopyClone,
    DeliveredIdentity,
}

pub fn check_fields(
    expected_source_hash: [u8; 32],
    interface: &StructInterface,
    terminal: &Finalization,
    ledger_delivered: &BTreeSet<FieldClassId>,
    observed: &Observation,
) -> Result<(), CustodyError> {
    if observed.source_hash != expected_source_hash {
        return Err(CustodyError::SourceHash);
    }
    if interface.field_types.keys().ne(observed.field_types.keys()) {
        return Err(CustodyError::FieldIdentity);
    }
    for (field, expected) in &interface.field_types {
        if observed.field_types[field] != *expected {
            return Err(CustodyError::FieldType(*field));
        }
    }
    if observed.lifetimes != interface.lifetimes {
        return Err(CustodyError::Lifetimes);
    }
    if interface.remove_copy_clone && observed.has_copy_clone {
        return Err(CustodyError::CopyClone);
    }
    let delivered: BTreeSet<_> = interface
        .field_types
        .keys()
        .copied()
        .filter(|field| terminal.live.contains(&ClassId::Field(*field)))
        .collect();
    if &delivered != ledger_delivered {
        return Err(CustodyError::DeliveredIdentity);
    }
    Ok(())
}
