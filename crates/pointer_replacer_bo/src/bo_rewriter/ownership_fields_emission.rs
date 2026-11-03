//! Typed emission plans over supplied grants. This is not a grant producer or
//! an AST parser. Expressions/types are compiler-rendered inputs at integration.
use super::EvidenceKey;
#[cfg(test)]
use super::lifecycle::CloseKind;
#[cfg(test)]
use super::lifecycle::ClosePlan;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Raw,
    Ref,
    Owning,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GrantStatus {
    #[allow(dead_code)]
    Candidate,
    Selected,
    #[allow(dead_code)]
    Retracted,
}
#[derive(Clone, Debug)]
pub struct Grant {
    pub key: EvidenceKey,
    pub kind: Kind,
    pub status: GrantStatus,
    pub transport: Option<EvidenceKey>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}
#[derive(Clone, Debug)]
pub struct ReferenceInterval {
    /// Same-generation regions may overlap. Disjoint subregions require a
    /// future region proof; this consumer intentionally covers whole payloads.
    pub generation: u64,
    pub live: Span,
    pub protected: Option<Span>,
}
#[derive(Clone, Debug)]
pub struct OwnCallFacts {
    pub key: EvidenceKey,
    pub call: Span,
    pub protector: Span,
    pub whole_payload: bool,
    pub references: Vec<ReferenceInterval>,
    pub reference_inventory: Option<EvidenceKey>,
    pub helper_lowering: Option<EvidenceKey>,
    pub permission: Option<EvidenceKey>,
    pub transfer_cleanup: Option<EvidenceKey>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EmitHold {
    Grant,
    Transport,
    CallIdentity,
    CallSpan,
    Payload,
    LiveReference,
    Protector,
    MissingEvidence(&'static str),
    #[allow(dead_code)]
    WrongClose,
    SinkIdentity,
    #[allow(dead_code)]
    Construction,
}

/// Private validated permit, returned only after exact-key evidence checks.
#[derive(Clone, Debug)]
pub struct OwnCallPermit {
    key: EvidenceKey,
}

pub fn admit_call(grant: &Grant, facts: &OwnCallFacts) -> Result<OwnCallPermit, EmitHold> {
    if grant.kind != Kind::Owning || grant.status != GrantStatus::Selected {
        return Err(EmitHold::Grant);
    }
    if grant.transport != Some(grant.key) {
        return Err(EmitHold::Transport);
    }
    if grant.key != facts.key {
        return Err(EmitHold::CallIdentity);
    }
    if facts.call.start >= facts.call.end || facts.protector != facts.call {
        return Err(EmitHold::CallSpan);
    }
    if !facts.whole_payload {
        return Err(EmitHold::Payload);
    }
    for (name, evidence) in [
        ("reference-inventory", facts.reference_inventory),
        ("helper-lowering", facts.helper_lowering),
        ("permission", facts.permission),
        ("transfer-cleanup", facts.transfer_cleanup),
    ] {
        if evidence != Some(facts.key) {
            return Err(EmitHold::MissingEvidence(name));
        }
    }
    let overlaps = |span: Span| {
        span.start < span.end && span.start < facts.call.end && facts.call.start < span.end
    };
    for reference in &facts.references {
        if reference.live.start > reference.live.end
            || reference.protected.is_some_and(|s| s.start > s.end)
        {
            return Err(EmitHold::CallSpan);
        }
        if reference.generation != facts.key.generation {
            continue;
        }
        if overlaps(reference.live) {
            return Err(EmitHold::LiveReference);
        }
        if reference.protected.is_some_and(overlaps) {
            return Err(EmitHold::Protector);
        }
    }
    Ok(OwnCallPermit { key: facts.key })
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnerType {
    pub pointee: String,
    pub optional: bool,
}
#[cfg(test)]
impl OwnerType {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Emitted {
    pub code: String,
    pub key: EvidenceKey,
    pub receipt: &'static str,
}

#[cfg(test)]
/// Local-only suppression carrier. Fields keep the declared Option<Box<_>>
/// interface; field/aggregate cleanup needs a separate transaction lowering.
#[derive(Clone, Debug)]
pub struct LeakLocal {
    key: EvidenceKey,
    name: String,
    ty: OwnerType,
    suppressed_closes: Vec<ClosePlan>,
}

#[cfg(test)]
/// Complete adapter-supplied implicit-exit inventory for one local generation.
/// A single scope/overwrite receipt cannot authorize unconditional suppression.
#[derive(Clone, Debug)]
pub struct LeakCoverage {
    pub local: EvidenceKey,
    pub completeness: Option<EvidenceKey>,
    pub closes: Vec<ClosePlan>,
}

#[cfg(test)]
impl LeakCoverage {}

#[cfg(test)]
impl LeakLocal {}

pub fn consume_argument(
    permit: &OwnCallPermit,
    expression: &str,
    optional_storage: bool,
) -> Emitted {
    Emitted {
        code: if optional_storage {
            format!("({expression}).take()")
        } else {
            expression.into()
        },
        key: permit.key,
        receipt: "owning-argument-move",
    }
}

/// The integration adapter resolves transparent free-site casts to this sink.
/// This function never matches by count, source order or variable spelling.
pub fn explicit_free(
    permit: &OwnCallPermit,
    sink: EvidenceKey,
    owner: &str,
    optional_storage: bool,
    allocator_layout: Option<EvidenceKey>,
) -> Result<Emitted, EmitHold> {
    if permit.key != sink || allocator_layout != Some(sink) {
        return Err(EmitHold::SinkIdentity);
    }
    let argument = consume_argument(permit, owner, optional_storage);
    Ok(Emitted {
        code: format!("drop({});", argument.code),
        key: sink,
        receipt: "c-free-site-drop",
    })
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub struct AggregateField {
    pub field: super::FieldClassId,
    pub name: String,
    pub ty: OwnerType,
    pub generation: EvidenceKey,
}
#[cfg(test)]
#[derive(Clone, Debug)]
pub struct LeakAggregate {
    key: EvidenceKey,
    owner: super::OwnerId,
    type_name: String,
    name: String,
    fields: std::collections::BTreeMap<super::FieldClassId, AggregateField>,
}
#[cfg(test)]
impl LeakAggregate {}

#[cfg(test)]
impl LeakAggregate {}
