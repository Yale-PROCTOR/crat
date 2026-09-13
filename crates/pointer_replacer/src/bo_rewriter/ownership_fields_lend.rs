//! R350/R365: lend an owning subject to a formal emitted as raw or borrowed.
//! The formal's model kind is retained for custody, not used as its emitted
//! ownership role. No native proof derivation. The adapter must supply the
//! existing raw-boundary T1 proof, exact model/formal join and complete access
//! inventory, including scalar/retained-raw arguments of the same call.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    EvidenceKey, OwnerId, SiteId,
    emission::{Grant, GrantStatus, Kind, ReferenceInterval, Span},
    export::{Evidence, Missing},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EdgeKey {
    pub call: SiteId,
    pub target: OwnerId,
    pub argument: u32,
    pub actual: EvidenceKey,
    pub formal: EvidenceKey,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Payload {
    Sized(String),
    Slice(String),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormalForm {
    MutableReference,
    MutableRaw,
    /// The emitted signature admits an owner; its call needs the move rule.
    Box,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Formal {
    pub edge: EdgeKey,
    /// The unchanged analysis kind, independent of the admitted emitted form.
    pub kind: Kind,
    pub form: FormalForm,
    pub payload: Payload,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Retention {
    T1NoRetention,
    Unknown,
    Retains,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RetentionProof {
    pub edge: EdgeKey,
    pub outcome: Retention,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RequestedUse {
    Lend,
    Move,
}
#[derive(Clone, Debug)]
pub struct LendSite {
    pub edge: EdgeKey,
    pub grant: Grant,
    /// Native place spelling, evaluated once. Arbitrary effectful expressions
    /// cannot be marked as a stable place by the integration adapter.
    pub place: String,
    pub payload: Payload,
    pub requested: RequestedUse,
    pub formal: Evidence<Formal>,
    pub stable_place: Evidence<EdgeKey>,
    /// No consuming/free/retirement effect, including transitive callees.
    /// T1 NoRetention alone does not establish this property.
    pub non_consuming: Evidence<EdgeKey>,
    pub retention: Evidence<RetentionProof>,
    /// Covers view creation through the call return, not just the callee body.
    pub view: Span,
    pub call_span: Span,
    pub protector: Span,
    /// Pre-existing reference intervals; the newly emitted view is not a
    /// retained alias. The inventory must cover every other argument/access.
    pub references: Evidence<Vec<ReferenceInterval>>,
    pub reference_inventory: Evidence<EdgeKey>,
    pub peer_inventory: Evidence<EdgeKey>,
    pub permission: Evidence<EdgeKey>,
    pub continuation_inventory: Evidence<EdgeKey>,
    /// Later reads/writes/source-free sites keep the same owning generation.
    pub continuation: Evidence<Vec<EvidenceKey>>,
}
#[derive(Clone, Debug)]
pub struct CallInventory {
    pub call: SiteId,
    pub targets: BTreeSet<OwnerId>,
    /// Complete set of owning arguments being lent. Other call operands are
    /// covered by peer/reference inventory; they are not rewritten here.
    pub arguments: BTreeSet<u32>,
    /// Authenticated native A5 Clear/disjoint-owner pairs, never inferred
    /// from different names or different Owning-generation numbers. Every
    /// pair of these mutable views, per target, needs a certificate.
    pub disjoint_pairs: Evidence<BTreeSet<(EdgeKey, EdgeKey)>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LendReceipt {
    pub edge: EdgeKey,
    /// R365 preserves this even when an Owning model formal is emitted raw.
    pub formal_model_kind: Kind,
    pub form: FormalForm,
    pub view: Span,
    pub protector: Span,
    pub owner_after: EvidenceKey,
    pub continuation: Vec<EvidenceKey>,
    pub retention: Retention,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LendPlan {
    pub arguments: BTreeMap<u32, String>,
    pub receipts: Vec<LendReceipt>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LendHold {
    Missing(Missing),
    Inventory,
    Grant,
    Identity,
    OwningCallee,
    /// A native producer found a consuming/free effect. Missing evidence is
    /// still Missing; this consumer never invents a no-free proof.
    ConsumingCallee,
    Formal,
    MoveInsteadOfLend,
    Retention,
    Span,
    LiveReference,
    Protector,
    PeerAlias,
    TargetDisagreement,
}
impl From<Missing> for LendHold {
    fn from(value: Missing) -> Self {
        Self::Missing(value)
    }
}

fn need<T>(value: &Evidence<T>) -> Result<&T, LendHold> {
    value.as_ref().map_err(|v| LendHold::Missing(v.clone()))
}
fn same_frame(a: EvidenceKey, b: EvidenceKey) -> bool {
    a.model == b.model && a.configuration == b.configuration
}
fn proof(value: &Evidence<EdgeKey>, edge: EdgeKey) -> Result<(), LendHold> {
    if *need(value)? != edge {
        return Err(LendHold::Identity);
    }
    Ok(())
}
fn overlaps(a: Span, b: Span) -> bool {
    a.start < a.end && b.start < b.end && a.start < b.end && b.start < a.end
}

pub fn plan_call(inventory: &CallInventory, sites: &[LendSite]) -> Result<LendPlan, LendHold> {
    let expected: BTreeSet<_> = inventory
        .targets
        .iter()
        .flat_map(|target| inventory.arguments.iter().map(move |arg| (*target, *arg)))
        .collect();
    let found: BTreeSet<_> = sites
        .iter()
        .map(|s| (s.edge.target, s.edge.argument))
        .collect();
    if expected.is_empty() || expected != found || found.len() != sites.len() {
        return Err(LendHold::Inventory);
    }
    let mut result = LendPlan {
        arguments: BTreeMap::new(),
        receipts: Vec::new(),
    };
    let mut actuals = BTreeMap::new();
    let frame = sites[0].edge.actual;
    for site in sites {
        let e = site.edge;
        if e.call != inventory.call
            || e.actual.site.owner != e.call.owner
            || e.formal.site.owner != e.target
            || !same_frame(e.actual, e.formal)
            || !same_frame(e.actual, frame)
            || e.actual.generation != e.formal.generation
        {
            return Err(LendHold::Identity);
        }
        if site.grant.key != e.actual
            || site.grant.kind != Kind::Owning
            || site.grant.status != GrantStatus::Selected
            || site.grant.transport != Some(e.actual)
        {
            return Err(LendHold::Grant);
        }
        if site.requested != RequestedUse::Lend {
            return Err(LendHold::MoveInsteadOfLend);
        }
        let formal = need(&site.formal)?;
        if formal.edge != e {
            return Err(LendHold::Identity);
        }
        if formal.form == FormalForm::Box {
            return Err(LendHold::OwningCallee);
        }
        if formal.payload != site.payload {
            return Err(LendHold::Formal);
        }
        for fact in [
            &site.stable_place,
            &site.non_consuming,
            &site.reference_inventory,
            &site.peer_inventory,
            &site.permission,
            &site.continuation_inventory,
        ] {
            proof(fact, e)?;
        }
        let retention = need(&site.retention)?;
        if retention.edge != e {
            return Err(LendHold::Identity);
        }
        if retention.outcome != Retention::T1NoRetention {
            return Err(LendHold::Retention);
        }
        if site.call_span != sites[0].call_span
            || site.view.start > site.call_span.start
            || site.call_span.start >= site.call_span.end
            || site.view.end != site.call_span.end
            || site.protector != site.call_span
        {
            return Err(LendHold::Span);
        }
        for reference in need(&site.references)? {
            if reference.live.start > reference.live.end
                || reference.protected.is_some_and(|s| s.start > s.end)
            {
                return Err(LendHold::Span);
            }
            if reference.generation == e.actual.generation {
                if overlaps(reference.live, site.view) {
                    return Err(LendHold::LiveReference);
                }
                if reference.protected.is_some_and(|s| overlaps(s, site.view)) {
                    return Err(LendHold::Protector);
                }
            }
        }
        let continuation = need(&site.continuation)?;
        if continuation.iter().any(|k| {
            !same_frame(*k, e.actual)
                || k.generation != e.actual.generation
                || k.site.owner != e.actual.site.owner
        }) {
            return Err(LendHold::Identity);
        }
        let actual = (
            e.actual,
            site.place.clone(),
            site.payload.clone(),
            formal.form,
            site.view,
            site.protector,
            continuation.clone(),
        );
        if actuals
            .get(&e.argument)
            .is_some_and(|prior| prior != &actual)
        {
            return Err(LendHold::TargetDisagreement);
        }
        actuals.insert(e.argument, actual);
        let code = match (&site.payload, formal.form) {
            (_, FormalForm::MutableReference) => format!("&mut *({})", site.place),
            (Payload::Slice(_), FormalForm::MutableRaw) => format!("({}).as_mut_ptr()", site.place),
            (Payload::Sized(_), FormalForm::MutableRaw) => {
                format!("core::ptr::from_mut(&mut *({}))", site.place)
            }
            (_, FormalForm::Box) => return Err(LendHold::OwningCallee),
        };
        result.arguments.insert(e.argument, code);
        result.receipts.push(LendReceipt {
            edge: e,
            formal_model_kind: formal.kind,
            form: formal.form,
            view: site.view,
            protector: site.protector,
            owner_after: e.actual,
            continuation: continuation.clone(),
            retention: retention.outcome,
        });
    }
    let mut pairs = BTreeSet::new();
    for a in sites {
        for b in sites
            .iter()
            .filter(|b| b.edge.target == a.edge.target && a.edge.argument < b.edge.argument)
        {
            if a.edge.actual.generation == b.edge.actual.generation {
                return Err(LendHold::PeerAlias);
            }
            pairs.insert((a.edge, b.edge));
        }
    }
    if need(&inventory.disjoint_pairs)? != &pairs {
        return Err(LendHold::PeerAlias);
    }
    result
        .receipts
        .sort_by_key(|r| (r.edge.target, r.edge.argument));
    Ok(result)
}
