//! Cursor-related adapter matrix over terminal forms and supplied evidence.
//! This leaf produces immutable operations, not source edits or new analysis
//! facts. Every proof key must be backed by the integrating decision collector.

use std::collections::BTreeMap;

use super::{
    carrier::ExtentOrigin,
    retention::{Node, Summary, Verdict, summarize},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Raw,
    Cursor,
    Slice,
    Thin,
    Owning,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Form {
    pub kind: Kind,
    pub mutable: bool,
    pub optional: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Destination<K> {
    Call(K),
    Local(K),
    Observation(K),
    Return(K),
    Field(K),
    RawWrapper(K),
    PairPeer(K),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Entry {
    ForwardOnly,
    NeedsPrefix,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Origin<K> {
    ForwardWindow(K),
    BaseAndIndex(K),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Region {
    Base,
    Tail,
    Element,
    RawUse,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RegionProof<K> {
    pub site: K,
    pub region: Region,
    pub formation: K,
    pub schedule: K,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ExtentProof<K> {
    /// The adapter site for which this extent receipt was prepared. An inherited
    /// source receipt alone is not a current-site binding.
    pub site: K,
    /// For fallback, retain the original root but use the receipt belonging to
    /// this adapter as site_receipt. The integrating producer seals that binding.
    pub origin: ExtentOrigin<K>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Proofs<K> {
    pub origin: Option<Origin<K>>,
    pub extent: Option<ExtentProof<K>>,
    pub region: Option<RegionProof<K>>,
    pub evaluation_order: Option<K>,
    pub current_index: Option<K>,
    pub nonempty: Option<K>,
    pub present: Option<K>,
    pub same_base: Option<K>,
    pub no_shared_write: Option<K>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WaiverId {
    CAliasing20260901,
}

impl WaiverId {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::CAliasing20260901 => "c-aliasing-semantics-at-unsafe-bridges/v1@2026-09-01",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Waiver<K> {
    pub id: WaiverId,
    pub site: K,
    pub receipt: K,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PairProof<K> {
    pub site: K,
    pub primary: K,
    pub waiver_receipt: K,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExistingHold {
    FreedSlot,
    IoDomain,
    ForeignAbiStruct,
    AddressTaken,
    Layout,
    BaseAliasConflict,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Request<K> {
    pub site: K,
    pub source: Form,
    pub target: Form,
    pub destination: Destination<K>,
    pub entry: Entry,
    pub proofs: Proofs<K>,
    pub t2: Option<Waiver<K>>,
    pub pair: Option<PairProof<K>>,
    pub existing_hold: Option<ExistingHold>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Operation {
    ReborrowCursor,
    CopyIndex,
    CursorTail,
    SliceCursor,
    RawCursor,
    CursorElement,
    RawView,
    PairRawView,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum IndexFlow {
    Preserve,
    Zero,
    Decompose,
    Tail,
    Current,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NullFlow {
    Direct,
    WrapSome,
    MapOptionalReborrow,
    UnwrapReborrow,
    NullOrRawView,
    GuardRawConstructor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Tier<K> {
    NotApplicable,
    T1,
    T2(Waiver<K>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Plan<K> {
    pub site: K,
    pub source: Form,
    pub target: Form,
    pub operation: Operation,
    pub index: IndexFlow,
    pub null: NullFlow,
    pub region: Region,
    pub proofs: Proofs<K>,
    pub tier: Tier<K>,
    pub retention: Option<Summary<K>>,
    pub pair: Option<PairProof<K>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Hold {
    Inherited(ExistingHold),
    DestinationUnbuilt,
    InvalidForm,
    SharedToMutable,
    OriginPrefix,
    PrefixLost,
    FormationOrSchedule,
    EvaluationOrder,
    CurrentIndex,
    Nonempty,
    Present,
    BaseTransfer,
    Extent,
    PositiveRetention,
    RetentionUnknown,
    SharedDerivedWrite,
    MissingWriteProof,
    WaiverMissing,
    WaiverSite,
    PairMissing,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Refusal<K> {
    pub site: K,
    pub source: Form,
    pub target: Form,
    pub reason: Hold,
}

pub(crate) fn plan<K: Copy + Ord>(
    request: Request<K>,
    raw_uses: &BTreeMap<K, Node<K>>,
) -> Result<Plan<K>, Refusal<K>> {
    select(request, raw_uses).map_err(|reason| Refusal {
        site: request.site,
        source: request.source,
        target: request.target,
        reason,
    })
}

fn select<K: Copy + Ord>(
    request: Request<K>,
    raw_uses: &BTreeMap<K, Node<K>>,
) -> Result<Plan<K>, Hold> {
    let Request {
        source,
        target,
        destination,
        proofs,
        ..
    } = request;
    if let Some(hold) = request.existing_hold {
        return Err(Hold::Inherited(hold));
    }
    if (source.kind == Kind::Raw && source.optional)
        || (target.kind == Kind::Raw && target.optional)
    {
        return Err(Hold::InvalidForm);
    }
    // Classify the safe destination before considering ANY raw-use summary.
    // An unsupported safe destination must never inherit a raw alias template.
    let (mut operation, region) = match (source.kind, target.kind) {
        (Kind::Cursor, Kind::Cursor) => (Operation::ReborrowCursor, Region::Base),
        (Kind::Cursor, Kind::Slice) => (Operation::CursorTail, Region::Tail),
        (Kind::Slice, Kind::Cursor) => (Operation::SliceCursor, Region::Base),
        (Kind::Raw, Kind::Cursor) => (Operation::RawCursor, Region::Base),
        (Kind::Cursor, Kind::Thin) => (Operation::CursorElement, Region::Element),
        (Kind::Cursor, Kind::Raw) => (Operation::RawView, Region::RawUse),
        _ => return Err(Hold::DestinationUnbuilt),
    };
    let root = match destination {
        Destination::Return(_) | Destination::Field(_) => {
            return Err(if target.kind == Kind::Raw {
                Hold::PositiveRetention
            } else {
                Hold::DestinationUnbuilt
            });
        }
        Destination::RawWrapper(root) if operation == Operation::RawCursor => root,
        Destination::Observation(root) | Destination::PairPeer(root)
            if operation == Operation::RawView =>
        {
            root
        }
        Destination::Call(root) | Destination::Local(root) => root,
        Destination::RawWrapper(_) | Destination::Observation(_) | Destination::PairPeer(_) => {
            return Err(Hold::DestinationUnbuilt);
        }
    };
    if !source.mutable && target.mutable && target.kind != Kind::Raw {
        return Err(Hold::SharedToMutable);
    }
    let pair = match destination {
        Destination::PairPeer(_) => {
            let proof = request
                .pair
                .filter(|p| p.site == request.site)
                .ok_or(Hold::PairMissing)?;
            operation = Operation::PairRawView;
            Some(proof)
        }
        _ => None,
    };
    let region = if pair.is_some() { Region::Base } else { region };
    if matches!(destination, Destination::Local(_)) && operation == Operation::ReborrowCursor {
        proofs.same_base.ok_or(Hold::BaseTransfer)?;
        operation = Operation::CopyIndex;
    }
    let origin = proofs.origin.ok_or(Hold::OriginPrefix)?;
    let index = match operation {
        Operation::RawCursor | Operation::SliceCursor => match origin {
            Origin::ForwardWindow(_) if request.entry == Entry::ForwardOnly => IndexFlow::Zero,
            Origin::ForwardWindow(_) => return Err(Hold::OriginPrefix),
            Origin::BaseAndIndex(_) => IndexFlow::Decompose,
        },
        Operation::CursorTail => {
            if request.entry != Entry::ForwardOnly {
                return Err(Hold::PrefixLost);
            }
            IndexFlow::Tail
        }
        Operation::ReborrowCursor | Operation::CopyIndex => IndexFlow::Preserve,
        Operation::CursorElement | Operation::RawView | Operation::PairRawView => {
            IndexFlow::Current
        }
    };
    if source.kind == Kind::Cursor && !matches!(origin, Origin::BaseAndIndex(_)) {
        return Err(Hold::OriginPrefix);
    }
    if source.kind == Kind::Cursor || index == IndexFlow::Decompose {
        proofs.current_index.ok_or(Hold::CurrentIndex)?;
    }
    if operation == Operation::CursorElement {
        proofs.nonempty.ok_or(Hold::Nonempty)?;
    }
    let null = if source.kind == Kind::Raw && target.optional {
        NullFlow::GuardRawConstructor
    } else if target.kind == Kind::Raw && source.optional {
        NullFlow::NullOrRawView
    } else {
        match (source.optional, target.optional) {
            (false, false) => NullFlow::Direct,
            (false, true) => NullFlow::WrapSome,
            (true, true) => NullFlow::MapOptionalReborrow,
            (true, false) => {
                proofs.present.ok_or(Hold::Present)?;
                NullFlow::UnwrapReborrow
            }
        }
    };
    // A token covering an element is not a token for a retained full base.
    proofs
        .region
        .filter(|p| p.site == request.site && p.region == region)
        .ok_or(Hold::FormationOrSchedule)?;
    proofs.evaluation_order.ok_or(Hold::EvaluationOrder)?;
    proofs
        .extent
        .filter(|p| p.site == request.site)
        .ok_or(Hold::Extent)?;
    let (tier, retention) = if source.kind == Kind::Raw || target.kind == Kind::Raw {
        let summary = summarize(root, raw_uses);
        // Positive retention wins even when a different descendant is unknown
        // or a T2 waiver was supplied. Query ROOT = DESTINATION, never source.
        if summary.verdict() == Verdict::Retained {
            return Err(Hold::PositiveRetention);
        }
        let shared_derived = if source.kind == Kind::Raw {
            !target.mutable
        } else {
            !source.mutable
        };
        if shared_derived && !summary.writes_at.is_empty() {
            return Err(Hold::SharedDerivedWrite);
        }
        // Unknown retention/effects do not supply negative-write evidence.
        // Const raw syntax also permits descendants to cast and write.
        if shared_derived
            && ((target.kind == Kind::Raw && target.mutable)
                || summary.verdict() == Verdict::Unknown)
        {
            proofs.no_shared_write.ok_or(Hold::MissingWriteProof)?;
        }
        let tier = match (destination, summary.verdict()) {
            (Destination::Observation(_), Verdict::NoRetention) => Tier::NotApplicable,
            (Destination::Observation(_), Verdict::Unknown) => return Err(Hold::RetentionUnknown),
            (_, Verdict::NoRetention) => Tier::T1,
            (_, Verdict::Unknown) => {
                let waiver = request.t2.ok_or(Hold::WaiverMissing)?;
                if waiver.site != request.site {
                    return Err(Hold::WaiverSite);
                }
                Tier::T2(waiver)
            }
            (_, Verdict::Retained) => return Err(Hold::PositiveRetention),
        };
        (tier, Some(summary))
    } else {
        (Tier::NotApplicable, None)
    };
    Ok(Plan {
        site: request.site,
        source,
        target,
        operation,
        index,
        null,
        region,
        proofs,
        tier,
        retention,
        pair,
    })
}
