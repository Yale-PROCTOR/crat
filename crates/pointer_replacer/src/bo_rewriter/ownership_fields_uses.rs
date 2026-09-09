//! Field operations consume exact role evidence for the terminal interface.
//! No source-name joins or role inference occurs in this module.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    EvidenceKey, FieldClassId, SiteId,
    transaction::{ClassId, FieldForm, SiteState, StructInterface, Transaction},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StorageAccess {
    Shared,
    Exclusive,
    Owned,
}
#[derive(Clone, Debug)]
pub enum FieldOperation {
    ReadShared,
    ReadMutable,
    Take,
    Store {
        value: String,
        source: EvidenceKey,
        source_type: String,
        empty_destination: Option<EvidenceKey>,
    },
}
#[derive(Clone, Debug)]
pub struct FieldSite {
    pub field: FieldClassId,
    pub key: EvidenceKey,
    pub terminal_type: String,
    pub form: FieldForm,
    pub lifetime: Option<String>,
    pub place: String,
    pub access: StorageAccess,
    pub operation: FieldOperation,
    pub role_proof: Option<EvidenceKey>,
    pub view_proof: Option<EvidenceKey>,
    pub transfer_proof: Option<EvidenceKey>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldUsePlan {
    pub field: FieldClassId,
    pub key: EvidenceKey,
    pub code: String,
    pub role: &'static str,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldHold {
    Interface,
    Role,
    View,
    Transfer,
    Storage,
    Source,
    NonOwning,
    NonOptionalTake,
    NonEmptyDestination,
    MissingSite(SiteId),
    ExtraSite(SiteId),
}

pub fn plan_field_use(
    site: &FieldSite,
    interface: &StructInterface,
) -> Result<FieldUsePlan, FieldHold> {
    if !interface.terminal_fields.contains(&site.field)
        || interface.field_types.get(&site.field) != Some(&site.terminal_type)
    {
        return Err(FieldHold::Interface);
    }
    if site.role_proof != Some(site.key) {
        return Err(FieldHold::Role);
    }
    let (owning, mutable, optional) = match &site.form {
        FieldForm::Owning { pointee, optional } => {
            let ty = format!("Box<{pointee}>");
            let expected = if *optional {
                format!("Option<{ty}>")
            } else {
                ty
            };
            if expected != site.terminal_type {
                return Err(FieldHold::Interface);
            }
            (true, true, *optional)
        }
        FieldForm::Borrow {
            pointee,
            mutable,
            optional,
        } => {
            let lifetime = site.lifetime.as_ref().ok_or(FieldHold::Interface)?;
            if !interface.lifetimes.contains(lifetime) {
                return Err(FieldHold::Interface);
            }
            let ty = format!(
                "&'{lifetime} {}{pointee}",
                if *mutable { "mut " } else { "" }
            );
            let expected = if *optional {
                format!("Option<{ty}>")
            } else {
                ty
            };
            if expected != site.terminal_type {
                return Err(FieldHold::Interface);
            }
            (false, *mutable, *optional)
        }
    };
    let (code, role) = match &site.operation {
        FieldOperation::ReadShared => {
            if site.view_proof != Some(site.key) {
                return Err(FieldHold::View);
            }
            (
                if optional {
                    format!("({}).as_deref()", site.place)
                } else {
                    format!("&*({})", site.place)
                },
                "field-shared-view",
            )
        }
        FieldOperation::ReadMutable => {
            if !mutable || site.access == StorageAccess::Shared {
                return Err(FieldHold::Storage);
            }
            if site.view_proof != Some(site.key) {
                return Err(FieldHold::View);
            }
            (
                if optional {
                    format!("({}).as_deref_mut()", site.place)
                } else {
                    format!("&mut *({})", site.place)
                },
                "field-mutable-view",
            )
        }
        FieldOperation::Take => {
            if !owning {
                return Err(FieldHold::NonOwning);
            }
            if site.access == StorageAccess::Shared {
                return Err(FieldHold::Storage);
            }
            if site.transfer_proof != Some(site.key) {
                return Err(FieldHold::Transfer);
            }
            if optional {
                (format!("({}).take()", site.place), "field-owner-take")
            } else if site.access == StorageAccess::Owned {
                (site.place.clone(), "field-owner-move")
            } else {
                return Err(FieldHold::NonOptionalTake);
            }
        }
        FieldOperation::Store {
            value,
            source,
            source_type,
            empty_destination,
        } => {
            if site.access == StorageAccess::Shared {
                return Err(FieldHold::Storage);
            }
            if site.transfer_proof != Some(site.key) {
                return Err(FieldHold::Transfer);
            }
            if source.model != site.key.model
                || source.configuration != site.key.configuration
                || source.generation != site.key.generation
                || source_type != &site.terminal_type
            {
                return Err(FieldHold::Source);
            }
            if owning && *empty_destination != Some(site.key) {
                return Err(FieldHold::NonEmptyDestination);
            }
            if !owning && site.view_proof != Some(site.key) {
                return Err(FieldHold::View);
            }
            (format!("{} = {value};", site.place), "field-value-store")
        }
    };
    Ok(FieldUsePlan {
        field: site.field,
        key: site.key,
        code,
        role,
    })
}

/// Inventory is independent of the reported site outcomes: omission is a hold.
pub fn checked_transaction(
    id: ClassId,
    prerequisites: BTreeSet<ClassId>,
    required: &BTreeSet<SiteId>,
    outcomes: BTreeMap<SiteId, SiteState>,
) -> Result<Transaction, FieldHold> {
    for site in required {
        if !outcomes.contains_key(site) {
            return Err(FieldHold::MissingSite(*site));
        }
    }
    for site in outcomes.keys() {
        if !required.contains(site) {
            return Err(FieldHold::ExtraSite(*site));
        }
    }
    Ok(Transaction {
        id,
        prerequisites,
        sites: outcomes,
    })
}
