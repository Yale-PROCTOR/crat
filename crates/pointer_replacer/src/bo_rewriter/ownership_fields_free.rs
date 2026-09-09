//! Free-operand normalization and identity-set matching. The frontend supplies
//! resolved cast kinds and exact storage roots; source spelling is never a join.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    EvidenceKey,
    emission::{Emitted, Grant, OwnCallFacts, admit_call, explicit_free},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CastKind {
    PointerToVoid,
    IdentityPointer,
    InteriorPointer,
    Integer,
    Opaque,
}
#[derive(Clone, Debug)]
pub struct FreeSite {
    pub sink: EvidenceKey,
    pub owner: EvidenceKey,
    pub expression: String,
    pub optional_storage: bool,
    pub casts: Vec<CastKind>,
    pub exact_owner_relation: Option<(EvidenceKey, EvidenceKey)>,
    pub allocation_base: Option<EvidenceKey>,
    pub allocator_layout: Option<EvidenceKey>,
    pub grant: Grant,
    pub call: OwnCallFacts,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FreeHold {
    Missing(EvidenceKey),
    Extra(EvidenceKey),
    Duplicate(EvidenceKey),
    OwnerIdentity,
    Cast,
    Base,
    Permission,
}
pub fn plan_frees(
    expected: &BTreeSet<EvidenceKey>,
    sites: &[FreeSite],
) -> Result<BTreeMap<EvidenceKey, Emitted>, FreeHold> {
    let mut indexed = BTreeMap::new();
    for site in sites {
        if indexed.insert(site.sink, site).is_some() {
            return Err(FreeHold::Duplicate(site.sink));
        }
    }
    for key in expected {
        if !indexed.contains_key(key) {
            return Err(FreeHold::Missing(*key));
        }
    }
    for key in indexed.keys() {
        if !expected.contains(key) {
            return Err(FreeHold::Extra(*key));
        }
    }
    let mut plans = BTreeMap::new();
    for (key, site) in indexed {
        if site.exact_owner_relation != Some((site.owner, key))
            || site.owner.model != key.model
            || site.owner.configuration != key.configuration
            || site.owner.generation != key.generation
            || site.owner.site.owner != key.site.owner
        {
            return Err(FreeHold::OwnerIdentity);
        }
        if site
            .casts
            .iter()
            .any(|cast| !matches!(cast, CastKind::PointerToVoid | CastKind::IdentityPointer))
        {
            return Err(FreeHold::Cast);
        }
        if site.allocation_base != Some(key) {
            return Err(FreeHold::Base);
        }
        let permit = admit_call(&site.grant, &site.call).map_err(|_| FreeHold::Permission)?;
        let emitted = explicit_free(
            &permit,
            key,
            &site.expression,
            site.optional_storage,
            site.allocator_layout,
        )
        .map_err(|_| FreeHold::Permission)?;
        plans.insert(key, emitted);
    }
    Ok(plans)
}
