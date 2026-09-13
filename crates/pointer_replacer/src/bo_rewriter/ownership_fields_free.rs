//! Free-operand normalization and identity-set matching. The frontend supplies
//! resolved cast kinds and exact storage roots; source spelling is never a join.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    EvidenceKey,
    emission::{Emitted, Grant, OwnCallFacts, admit_call, explicit_free},
};

/// A trusted proof adapter for one exact free occurrence. The common join
/// checks inventory only: each implementation must validate its own native
/// identity, ownership, layout and emission obligations in `plan`.
/// Implementing this trait does not itself authorize a drop. In particular,
/// native source identities need not manufacture dynamic generation keys.
pub trait FreePlanSite {
    type Key: Clone + Ord;
    type Emitted;
    type Hold;

    fn key(&self) -> &Self::Key;
    fn missing(key: Self::Key) -> Self::Hold;
    fn extra(key: Self::Key) -> Self::Hold;
    fn duplicate(key: Self::Key) -> Self::Hold;
    fn plan(&self) -> Result<Self::Emitted, Self::Hold>;
}

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
/// Join a complete free inventory before invoking any per-site proof adapter.
/// Source-keyed and generation-keyed sites share this exact coverage check.
pub fn plan_frees<S: FreePlanSite>(
    expected: &BTreeSet<S::Key>,
    sites: &[S],
) -> Result<BTreeMap<S::Key, S::Emitted>, S::Hold> {
    let mut indexed = BTreeMap::new();
    for site in sites {
        if indexed.insert(site.key().clone(), site).is_some() {
            return Err(S::duplicate(site.key().clone()));
        }
    }
    for key in expected {
        if !indexed.contains_key(key) {
            return Err(S::missing(key.clone()));
        }
    }
    for key in indexed.keys() {
        if !expected.contains(key) {
            return Err(S::extra(key.clone()));
        }
    }
    let mut plans = BTreeMap::new();
    for (key, site) in indexed {
        plans.insert(key, site.plan()?);
    }
    Ok(plans)
}

impl FreePlanSite for FreeSite {
    type Emitted = Emitted;
    type Hold = FreeHold;
    type Key = EvidenceKey;

    fn key(&self) -> &EvidenceKey {
        &self.sink
    }

    fn missing(key: EvidenceKey) -> FreeHold {
        FreeHold::Missing(key)
    }

    fn extra(key: EvidenceKey) -> FreeHold {
        FreeHold::Extra(key)
    }

    fn duplicate(key: EvidenceKey) -> FreeHold {
        FreeHold::Duplicate(key)
    }

    fn plan(&self) -> Result<Emitted, FreeHold> {
        let key = self.sink;
        if self.exact_owner_relation != Some((self.owner, key))
            || self.owner.model != key.model
            || self.owner.configuration != key.configuration
            || self.owner.generation != key.generation
            || self.owner.site.owner != key.site.owner
        {
            return Err(FreeHold::OwnerIdentity);
        }
        if self
            .casts
            .iter()
            .any(|cast| !matches!(cast, CastKind::PointerToVoid | CastKind::IdentityPointer))
        {
            return Err(FreeHold::Cast);
        }
        if self.allocation_base != Some(key) {
            return Err(FreeHold::Base);
        }
        let permit = admit_call(&self.grant, &self.call).map_err(|_| FreeHold::Permission)?;
        explicit_free(
            &permit,
            key,
            &self.expression,
            self.optional_storage,
            self.allocator_layout,
        )
        .map_err(|_| FreeHold::Permission)
    }
}
