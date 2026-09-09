use std::collections::{BTreeMap, BTreeSet};

use super::{FieldClassId, OwnerId, SiteId};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ClassId {
    Field(FieldClassId),
    Function(OwnerId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SiteState {
    Ready,
    ZeroSyntax,
    Held(String),
}

#[derive(Clone, Debug)]
pub struct Transaction {
    pub id: ClassId,
    pub prerequisites: BTreeSet<ClassId>,
    pub sites: BTreeMap<SiteId, SiteState>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Hold {
    MissingInventory,
    Site(SiteId, String),
    Prerequisite(ClassId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    DuplicateClass(ClassId),
    DuplicateField(FieldClassId),
    WrongStruct(FieldClassId),
    MissingClass(FieldClassId),
    CopyRequired,
    StaleFinalization,
    CopySiteMissing(SiteId),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Finalization {
    pub live: BTreeSet<ClassId>,
    pub held: BTreeMap<ClassId, Hold>,
}

/// Greatest prerequisite-closed set of complete transactions. Fully ready
/// cycles survive; failure propagates through their actual dependency edges.
pub fn finalize(transactions: &[Transaction]) -> Result<Finalization, Error> {
    let mut result = Finalization::default();
    let mut seen = BTreeSet::new();
    for transaction in transactions {
        if !seen.insert(transaction.id) {
            return Err(Error::DuplicateClass(transaction.id));
        }
        let hold = if transaction.sites.is_empty() {
            Some(Hold::MissingInventory)
        } else {
            transaction
                .sites
                .iter()
                .find_map(|(site, state)| match state {
                    SiteState::Held(reason) => Some(Hold::Site(*site, reason.clone())),
                    SiteState::Ready | SiteState::ZeroSyntax => None,
                })
        };
        if let Some(hold) = hold {
            result.held.insert(transaction.id, hold);
        } else {
            result.live.insert(transaction.id);
        }
    }
    loop {
        let invalid: Vec<_> = transactions
            .iter()
            .filter(|t| result.live.contains(&t.id))
            .filter_map(|t| {
                t.prerequisites
                    .iter()
                    .find(|id| !result.live.contains(id))
                    .map(|id| (t.id, *id))
            })
            .collect();
        if invalid.is_empty() {
            break;
        }
        for (id, dependency) in invalid {
            result.live.remove(&id);
            result.held.insert(id, Hold::Prerequisite(dependency));
        }
    }
    Ok(result)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldForm {
    Borrow {
        pointee: String,
        mutable: bool,
        optional: bool,
    },
    Owning {
        pointee: String,
        optional: bool,
    },
}

#[derive(Clone, Debug)]
pub struct Field {
    pub id: FieldClassId,
    pub name: String,
    pub input_type: String,
    pub candidate: FieldForm,
}

#[derive(Clone, Debug)]
pub enum CopyContract {
    Absent,
    MustPreserve,
    Removable { sites: BTreeSet<SiteId> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructInterface {
    /// Field application set that produced this exact type vector.
    pub terminal_fields: BTreeSet<FieldClassId>,
    pub field_types: BTreeMap<FieldClassId, String>,
    pub lifetimes: Vec<String>,
    pub remove_copy_clone: bool,
}

/// Render the declaration vector from terminal class outcomes. This does not
/// infer origins: borrowed candidates require the integration adapter's stored
/// origin/variance permits before entering their transaction's Ready sites.
pub fn struct_interface(
    owner: OwnerId,
    fields: &[Field],
    reserved_lifetimes: &BTreeSet<String>,
    copy: &CopyContract,
    transactions: &[Transaction],
    finalization: &Finalization,
) -> Result<StructInterface, Error> {
    // Never accept a stale caller-supplied live set after a recovery round.
    let actual = finalize(transactions)?;
    if &actual != finalization {
        return Err(Error::StaleFinalization);
    }
    let mut result = StructInterface {
        terminal_fields: BTreeSet::new(),
        field_types: BTreeMap::new(),
        lifetimes: vec![],
        remove_copy_clone: false,
    };
    let mut used = reserved_lifetimes.clone();
    let mut ordered: Vec<_> = fields.iter().collect();
    ordered.sort_by_key(|field| field.id);
    let mut incompatible_copy = BTreeSet::new();
    for field in ordered {
        if field.id.owner != owner {
            return Err(Error::WrongStruct(field.id));
        }
        if result.field_types.contains_key(&field.id) {
            return Err(Error::DuplicateField(field.id));
        }
        let id = ClassId::Field(field.id);
        if !actual.live.contains(&id) && !actual.held.contains_key(&id) {
            return Err(Error::MissingClass(field.id));
        }
        // Reserve names for the entire candidate vector, including held fields.
        let lifetime = if matches!(field.candidate, FieldForm::Borrow { .. }) {
            let base = format!("__crat_f{}", field.id.field);
            let mut name = base.clone();
            let mut suffix = 0;
            while !used.insert(name.clone()) {
                suffix += 1;
                name = format!("{base}_{suffix}");
            }
            Some(name)
        } else {
            None
        };
        let ty = if actual.live.contains(&id) {
            result.terminal_fields.insert(field.id);
            match &field.candidate {
                FieldForm::Borrow {
                    pointee,
                    mutable,
                    optional,
                } => {
                    let lifetime = lifetime.expect("borrowed candidate has reserved lifetime");
                    result.lifetimes.push(lifetime.clone());
                    if *mutable {
                        incompatible_copy.insert(id);
                    }
                    let ty = format!(
                        "&'{lifetime} {}{pointee}",
                        if *mutable { "mut " } else { "" }
                    );
                    if *optional {
                        format!("Option<{ty}>")
                    } else {
                        ty
                    }
                }
                FieldForm::Owning { pointee, optional } => {
                    incompatible_copy.insert(id);
                    let ty = format!("Box<{pointee}>");
                    if *optional {
                        format!("Option<{ty}>")
                    } else {
                        ty
                    }
                }
            }
        } else {
            field.input_type.clone()
        };
        result.field_types.insert(field.id, ty);
    }
    if !incompatible_copy.is_empty() {
        match copy {
            CopyContract::Absent => {}
            CopyContract::MustPreserve => return Err(Error::CopyRequired),
            CopyContract::Removable { sites } => {
                for site in sites {
                    let covered = incompatible_copy.iter().all(|id| {
                        transactions.iter().any(|t| {
                            t.id == *id
                                && matches!(
                                    t.sites.get(site),
                                    Some(SiteState::Ready | SiteState::ZeroSyntax)
                                )
                        })
                    });
                    if !covered {
                        return Err(Error::CopySiteMissing(*site));
                    }
                }
                result.remove_copy_clone = true;
            }
        }
    }
    Ok(result)
}
