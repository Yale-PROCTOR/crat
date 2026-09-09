//! Apply only complete prerequisite-closed field/function transactions. Input
//! is the authoritative pre-edit text for this round, never a partly edited tree.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    SiteId,
    declaration::CapturedSpan,
    transaction::{ClassId, Finalization, SiteState, Transaction, finalize},
};
#[derive(Clone, Debug)]
pub struct SiteEdit {
    pub owner: ClassId,
    pub site: SiteId,
    pub span: CapturedSpan,
    pub replacement: String,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ApplyHold {
    Transaction,
    UnknownOwner,
    UnknownSite,
    MissingEdit(ClassId, SiteId),
    DuplicateEdit(ClassId, SiteId),
    ZeroSyntaxEdit(ClassId, SiteId),
    StaleSpan,
    Overlap(ClassId, ClassId),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Applied {
    pub text: String,
    pub terminal: Finalization,
    pub applied_sites: BTreeSet<(ClassId, SiteId)>,
}
pub fn apply_transactions(
    source: &str,
    transactions: &[Transaction],
    edits: &[SiteEdit],
) -> Result<Applied, ApplyHold> {
    let terminal = finalize(transactions).map_err(|_| ApplyHold::Transaction)?;
    let tx: BTreeMap<_, _> = transactions.iter().map(|t| (t.id, t)).collect();
    let mut indexed = BTreeMap::new();
    for edit in edits {
        let owner = tx.get(&edit.owner).ok_or(ApplyHold::UnknownOwner)?;
        if !owner.sites.contains_key(&edit.site) {
            return Err(ApplyHold::UnknownSite);
        }
        if indexed.insert((edit.owner, edit.site), edit).is_some() {
            return Err(ApplyHold::DuplicateEdit(edit.owner, edit.site));
        }
    }
    let mut active = Vec::new();
    let mut applied_sites = BTreeSet::new();
    for owner in &terminal.live {
        for (site, state) in &tx[owner].sites {
            match (state, indexed.get(&(*owner, *site))) {
                (SiteState::Ready, None) => return Err(ApplyHold::MissingEdit(*owner, *site)),
                (SiteState::ZeroSyntax, Some(_)) => {
                    return Err(ApplyHold::ZeroSyntaxEdit(*owner, *site));
                }
                (SiteState::Ready, Some(edit)) => {
                    active.push(*edit);
                    applied_sites.insert((*owner, *site));
                }
                (SiteState::ZeroSyntax, None) => {
                    applied_sites.insert((*owner, *site));
                }
                (SiteState::Held(_), _) => return Err(ApplyHold::Transaction),
            }
        }
    }
    active.sort_by_key(|e| (e.span.lo, e.span.hi));
    for edit in &active {
        if source.get(edit.span.lo..edit.span.hi) != Some(edit.span.text.as_str()) {
            return Err(ApplyHold::StaleSpan);
        }
    }
    for pair in active.windows(2) {
        if pair[0].span.hi > pair[1].span.lo || pair[0].span.lo == pair[1].span.lo {
            return Err(ApplyHold::Overlap(pair[0].owner, pair[1].owner));
        }
    }
    let mut text = source.to_owned();
    for edit in active.into_iter().rev() {
        text.replace_range(edit.span.lo..edit.span.hi, &edit.replacement);
    }
    Ok(Applied {
        text,
        terminal,
        applied_sites,
    })
}
