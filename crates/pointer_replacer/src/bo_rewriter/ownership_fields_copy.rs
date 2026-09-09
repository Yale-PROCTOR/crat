//! Source struct-copy adaptation after the existing struct-copy decision has
//! admitted removal of generated Copy/Clone. Every remaining source use must
//! already have a legal reroute; taking a field never silently erases a read.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    EvidenceKey, FieldClassId, SiteId,
    field_uses::{FieldOperation, FieldSite, plan_field_use},
    transaction::{FieldForm, StructInterface},
};

#[derive(Clone, Debug)]
pub enum CopyMember {
    Unchanged {
        field: FieldClassId,
        name: String,
        expression: String,
        terminal_type: String,
        copy_proof: Option<EvidenceKey>,
    },
    Pointer {
        name: String,
        site: FieldSite,
    },
    Scalar {
        field: FieldClassId,
        name: String,
        expression: String,
        copy_proof: Option<EvidenceKey>,
    },
}
#[derive(Clone, Debug)]
pub struct CopySite {
    pub key: EvidenceKey,
    pub source: String,
    pub destination: String,
    pub struct_name: String,
    pub all_fields: BTreeSet<FieldClassId>,
    pub members: Vec<CopyMember>,
    pub decision: Option<EvidenceKey>,
    pub remaining_source_uses: BTreeSet<SiteId>,
    pub rerouted_source_uses: BTreeSet<SiteId>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CopyHold {
    Decision,
    SourceUses,
    FieldInventory,
    FieldRole,
    ScalarProof,
    DuplicateOwner,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CopyPlan {
    pub key: EvidenceKey,
    pub code: String,
    pub fields: BTreeSet<FieldClassId>,
}
pub fn plan_struct_copy(
    site: &CopySite,
    interface: &StructInterface,
) -> Result<CopyPlan, CopyHold> {
    if site.decision != Some(site.key) || !interface.remove_copy_clone {
        return Err(CopyHold::Decision);
    }
    if site.remaining_source_uses != site.rerouted_source_uses {
        return Err(CopyHold::SourceUses);
    }
    let mut rendered = BTreeMap::new();
    let mut transferred = BTreeSet::new();
    let mut names = BTreeSet::new();
    for member in &site.members {
        let (field, name, expression) = match member {
            CopyMember::Unchanged {
                field,
                name,
                expression,
                terminal_type,
                copy_proof,
            } => {
                if interface.terminal_fields.contains(field)
                    || interface.field_types.get(field) != Some(terminal_type)
                {
                    return Err(CopyHold::FieldInventory);
                }
                if *copy_proof != Some(site.key) {
                    return Err(CopyHold::ScalarProof);
                }
                (*field, name.clone(), expression.clone())
            }
            CopyMember::Pointer { name, site: field } => {
                if field.key.model != site.key.model
                    || field.key.configuration != site.key.configuration
                    || field.key.site.owner != site.key.site.owner
                {
                    return Err(CopyHold::FieldRole);
                }
                match (&field.form, &field.operation) {
                    (FieldForm::Owning { .. }, FieldOperation::Take) => {
                        if !transferred.insert(field.key.generation) {
                            return Err(CopyHold::DuplicateOwner);
                        }
                    }
                    (FieldForm::Borrow { mutable: false, .. }, FieldOperation::ReadShared) => {}
                    (FieldForm::Borrow { mutable: true, .. }, FieldOperation::ReadMutable) => {}
                    _ => return Err(CopyHold::FieldRole),
                }
                let plan = plan_field_use(field, interface).map_err(|_| CopyHold::FieldRole)?;
                (field.field, name.clone(), plan.code)
            }
            CopyMember::Scalar {
                field,
                name,
                expression,
                copy_proof,
            } => {
                if interface.field_types.contains_key(field) {
                    return Err(CopyHold::FieldInventory);
                }
                if *copy_proof != Some(site.key) {
                    return Err(CopyHold::ScalarProof);
                }
                (*field, name.clone(), expression.clone())
            }
        };
        if !names.insert(name.clone())
            || rendered
                .insert(field, format!("{name}: {expression}"))
                .is_some()
        {
            return Err(CopyHold::FieldInventory);
        }
    }
    if rendered.keys().copied().collect::<BTreeSet<_>>() != site.all_fields
        || !interface
            .field_types
            .keys()
            .all(|f| site.all_fields.contains(f))
    {
        return Err(CopyHold::FieldInventory);
    }
    Ok(CopyPlan {
        key: site.key,
        code: format!(
            "let mut {} = {} {{ {} }};",
            site.destination,
            site.struct_name,
            rendered.values().cloned().collect::<Vec<_>>().join(", ")
        ),
        fields: site.all_fields.clone(),
    })
}
