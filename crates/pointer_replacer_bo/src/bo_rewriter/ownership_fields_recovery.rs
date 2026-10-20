//! Predecessor preservation over explicitly versioned interfaces. Dependency
//! identities include the revision: a live old field is not a new interface.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    SiteId,
    application::SiteEdit,
    transaction::{ClassId, SiteState},
};
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RevisionId {
    pub class: ClassId,
    pub revision: u32,
}
#[derive(Clone, Debug)]
pub struct Revision {
    pub id: RevisionId,
    pub introduced_at: u32,
    pub required: BTreeSet<RevisionId>,
    pub sites: BTreeMap<SiteId, SiteState>,
    pub edits: Vec<SiteEdit>,
}
#[derive(Clone, Debug)]
pub struct RevisionSet {
    pub model: [u8; 32],
    pub configuration: [u8; 32],
    pub revisions: Vec<Revision>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecoveryReason {
    Incomplete,
    Dependency(RevisionId),
    Collision(ClassId),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecoveryError {
    Frame,
    DuplicateClass,
    InvalidPredecessor,
    RevisionOrder,
    Application,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Recovered {
    pub text: String,
    pub selected: BTreeMap<ClassId, RevisionId>,
    pub fallback: BTreeMap<ClassId, RecoveryReason>,
}
fn complete(source: &str, revision: &Revision) -> bool {
    if revision.sites.is_empty() {
        return false;
    }
    let mut edits = BTreeSet::new();
    for edit in &revision.edits {
        if edit.owner != revision.id.class
            || !edits.insert(edit.site)
            || !matches!(revision.sites.get(&edit.site), Some(SiteState::Ready))
            || source.get(edit.span.lo..edit.span.hi) != Some(edit.span.text.as_str())
        {
            return false;
        }
    }
    revision.sites.iter().all(|(site, state)| match state {
        SiteState::Ready => edits.contains(site),
        SiteState::ZeroSyntax => !edits.contains(site),
        SiteState::Held(_) => false,
    })
}
fn collision(a: &SiteEdit, b: &SiteEdit) -> bool {
    a.span.lo == b.span.lo || (a.span.lo < b.span.hi && b.span.lo < a.span.hi)
}

pub fn recover(
    source: &str,
    previous: &RevisionSet,
    proposed: &RevisionSet,
) -> Result<Recovered, RecoveryError> {
    if previous.model != proposed.model || previous.configuration != proposed.configuration {
        return Err(RecoveryError::Frame);
    }
    let old: BTreeMap<_, _> = previous.revisions.iter().map(|r| (r.id.class, r)).collect();
    let new: BTreeMap<_, _> = proposed.revisions.iter().map(|r| (r.id.class, r)).collect();
    if old.len() != previous.revisions.len() || new.len() != proposed.revisions.len() {
        return Err(RecoveryError::DuplicateClass);
    }
    for revision in old.values() {
        if !complete(source, revision)
            || revision
                .required
                .iter()
                .any(|r| old.get(&r.class).map(|v| v.id) != Some(*r))
        {
            return Err(RecoveryError::InvalidPredecessor);
        }
    }
    let old_edits: Vec<_> = old.values().flat_map(|r| &r.edits).collect();
    for (i, a) in old_edits.iter().enumerate() {
        for b in &old_edits[i + 1..] {
            if collision(a, b) {
                return Err(RecoveryError::InvalidPredecessor);
            }
        }
    }
    let mut selected = old.clone();
    let mut fallback = BTreeMap::new();
    for (class, revision) in &new {
        if old.get(class).is_some_and(|previous| {
            revision.id.revision <= previous.id.revision
                || revision.introduced_at <= previous.introduced_at
        }) {
            return Err(RecoveryError::RevisionOrder);
        }
        if complete(source, revision) {
            selected.insert(*class, *revision);
        } else {
            fallback.insert(*class, RecoveryReason::Incomplete);
        }
    }
    loop {
        let mut withdraw = BTreeMap::new();
        for (class, revision) in &selected {
            for required in &revision.required {
                if selected.get(&required.class).map(|r| r.id) == Some(*required) {
                    continue;
                }
                if new.get(class).is_some_and(|r| r.id == revision.id) {
                    withdraw.insert(*class, RecoveryReason::Dependency(*required));
                } else if selected
                    .get(&required.class)
                    .is_some_and(|r| new.get(&required.class).is_some_and(|n| n.id == r.id))
                {
                    withdraw.insert(required.class, RecoveryReason::Dependency(*required));
                } else {
                    return Err(RecoveryError::InvalidPredecessor);
                }
            }
        }
        let edits: Vec<_> = selected
            .values()
            .flat_map(|r| r.edits.iter().map(move |e| (*r, e)))
            .collect();
        for (i, (a, ae)) in edits.iter().enumerate() {
            for (b, be) in &edits[i + 1..] {
                if !collision(ae, be) {
                    continue;
                }
                let a_new = new.get(&a.id.class).is_some_and(|r| r.id == a.id);
                let b_new = new.get(&b.id.class).is_some_and(|r| r.id == b.id);
                match (a_new, b_new) {
                    (false, false) => return Err(RecoveryError::InvalidPredecessor),
                    (true, false) => {
                        withdraw.insert(a.id.class, RecoveryReason::Collision(b.id.class));
                    }
                    (false, true) => {
                        withdraw.insert(b.id.class, RecoveryReason::Collision(a.id.class));
                    }
                    (true, true) => {
                        if a.introduced_at >= b.introduced_at {
                            withdraw.insert(a.id.class, RecoveryReason::Collision(b.id.class));
                        }
                        if b.introduced_at >= a.introduced_at {
                            withdraw.insert(b.id.class, RecoveryReason::Collision(a.id.class));
                        }
                    }
                }
            }
        }
        if withdraw.is_empty() {
            break;
        }
        for (class, reason) in withdraw {
            if let Some(previous) = old.get(&class) {
                selected.insert(class, *previous);
            } else {
                selected.remove(&class);
            }
            fallback.insert(class, reason);
        }
    }
    let transactions: Vec<_> = selected
        .values()
        .map(|r| super::transaction::Transaction {
            id: r.id.class,
            prerequisites: r.required.iter().map(|r| r.class).collect(),
            sites: r.sites.clone(),
        })
        .collect();
    let edits: Vec<_> = selected.values().flat_map(|r| r.edits.clone()).collect();
    let applied = super::application::apply_transactions(source, &transactions, &edits)
        .map_err(|_| RecoveryError::Application)?;
    Ok(Recovered {
        text: applied.text,
        selected: selected.into_iter().map(|(id, r)| (id, r.id)).collect(),
        fallback,
    })
}
