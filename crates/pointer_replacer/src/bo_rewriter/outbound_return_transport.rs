//! Owned J27 replay evidence, projected directly from typed native receipts.
//! Retained validation does not consult a compiler context or saved verdict.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use super::{
    RawBoundaryArtifacts,
    bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeReceiptEvent, BridgeReceiptStage,
        BridgeReceiptState, BridgeRetentionTier, BridgeSiteKey, RAW_BOUNDARY_T2_WAIVER_ID,
    },
    decision::raw_boundary::{self, RetentionVerdict},
    mechanical_receipt::{
        self, CanonicalCallee, CanonicalLocation, MechanicalExtent, MechanicalFamily,
        MechanicalMechanism, MechanicalObligationKey, MechanicalRetention, MechanicalStage,
        MechanicalState, MechanicalSubjectKey, NegativeWriteEvidence, TerminalContract,
    },
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Capture {
    pub(crate) required: Vec<Requirement>,
    pub(crate) rows: Vec<Row>,
    pub(crate) common: Vec<Common>,
    pub(crate) bridges: Vec<Bridge>,
    pub(crate) rendered_tsv: String,
    pub(crate) capture_errors: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Subject {
    pub(crate) key: String,
    pub(crate) local: Option<(u32, u32, u32)>,
    pub(crate) generated: Option<(u32, String, u32)>,
}

fn subject(value: &MechanicalSubjectKey) -> Subject {
    Subject {
        key: value.receipt_key(),
        generated: match value {
            MechanicalSubjectKey::Generated {
                owner,
                key,
                slot_depth,
            } => Some((owner.local_def_index.as_u32(), key.clone(), *slot_depth)),
            MechanicalSubjectKey::Local { .. } | MechanicalSubjectKey::Field { .. } => None,
        },
        local: match value {
            MechanicalSubjectKey::Local {
                owner,
                mir_local,
                slot_depth,
            } => Some((owner.local_def_index.as_u32(), *mir_local, *slot_depth)),
            MechanicalSubjectKey::Field { .. } | MechanicalSubjectKey::Generated { .. } => None,
        },
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Key {
    pub(crate) key: String,
    pub(crate) family: String,
    pub(crate) owner: u32,
    pub(crate) caller: u32,
    pub(crate) subject: Subject,
    pub(crate) endpoint: Option<String>,
    pub(crate) endpoint_def_id: Option<(u32, u32)>,
    pub(crate) hir_owner: Option<u32>,
    pub(crate) hir_item_local_id: Option<u32>,
    pub(crate) argument_index: Option<u32>,
    pub(crate) slot_depth: u32,
}

fn endpoint(value: &CanonicalCallee) -> String {
    value.receipt_key()
}

fn key(value: &MechanicalObligationKey) -> Key {
    Key {
        key: value.receipt_key(),
        family: value.family.key().into(),
        owner: value.owner_class.order_key(),
        caller: value.site.owner.local_def_index.as_u32(),
        subject: subject(&value.subject),
        endpoint: value.site.callee.as_ref().map(endpoint),
        endpoint_def_id: match value.site.callee.as_ref() {
            Some(CanonicalCallee::Local(did)) => Some((did.krate.as_u32(), did.index.as_u32())),
            Some(CanonicalCallee::Foreign(_) | CanonicalCallee::Generated { .. }) | None => None,
        },
        hir_owner: match value.site.location {
            CanonicalLocation::Hir { owner, .. } => Some(owner.local_def_index.as_u32()),
            CanonicalLocation::Mir { .. }
            | CanonicalLocation::Declaration { .. }
            | CanonicalLocation::Generated { .. }
            | CanonicalLocation::StaticRoot { .. } => None,
        },
        hir_item_local_id: match value.site.location {
            CanonicalLocation::Hir { item_local_id, .. } => Some(item_local_id),
            CanonicalLocation::Mir { .. }
            | CanonicalLocation::Declaration { .. }
            | CanonicalLocation::Generated { .. }
            | CanonicalLocation::StaticRoot { .. } => None,
        },
        argument_index: value.site.argument_index,
        slot_depth: value.site.slot_depth,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BridgeKey {
    pub(crate) key: String,
    pub(crate) owner: u32,
    pub(crate) caller: u32,
    pub(crate) callee: Option<u32>,
    pub(crate) endpoint: String,
    pub(crate) endpoint_def_id: Option<(u32, u32)>,
    pub(crate) arm: String,
    pub(crate) file: String,
    pub(crate) lo: u32,
    pub(crate) hi: u32,
    pub(crate) kind: String,
    pub(crate) position: String,
}

fn bridge_key(value: &BridgeSiteKey) -> BridgeKey {
    let (callee, endpoint, endpoint_def_id) = match &value.callee {
        BridgeCalleeId::Local(did) => (
            Some(did.local_def_index.as_u32()),
            endpoint(&CanonicalCallee::Local(did.to_def_id())),
            Some((
                did.to_def_id().krate.as_u32(),
                did.to_def_id().index.as_u32(),
            )),
        ),
        BridgeCalleeId::Foreign(symbol) => (None, format!("foreign:{symbol}"), None),
    };
    BridgeKey {
        key: value.receipt_key(),
        owner: value.owner_class.order_key(),
        caller: value.caller.local_def_index.as_u32(),
        callee,
        endpoint,
        endpoint_def_id,
        arm: value.arm.clone(),
        file: value.file.clone(),
        lo: value.lo,
        hi: value.hi,
        kind: value.bridge_kind.clone(),
        position: value.position.clone(),
    }
}

fn canonical_subject(value: &Subject) -> Option<String> {
    match (value.local, &value.generated) {
        (Some((owner, local, depth)), None) => Some(format!("local:{owner}:{local}:depth={depth}")),
        (None, Some((owner, key, depth))) => Some(format!("generated:{owner}:{key}:depth={depth}")),
        _ => None,
    }
}

fn canonical_obligation(value: &Key) -> Option<String> {
    let subject = canonical_subject(&value.subject)?;
    if subject != value.subject.key {
        return None;
    }
    let (krate, index) = value.endpoint_def_id?;
    let endpoint = format!("def-id:{krate}:{index}");
    if value.endpoint.as_ref() != Some(&endpoint) {
        return None;
    }
    let owner = value.hir_owner?;
    let item = value.hir_item_local_id?;
    let argument = value
        .argument_index
        .map_or_else(|| "-".into(), |index| index.to_string());
    let site = format!(
        "owner={}:location=hir:{owner}:{item}:callee={endpoint}:arg={argument}:depth={}",
        value.caller, value.slot_depth
    );
    Some(format!(
        "class={}:subject={subject}:site={site}:family={}",
        value.owner, value.family
    ))
}

fn canonical_bridge(value: &BridgeKey) -> Option<String> {
    let callee = value.callee?;
    let (krate, index) = value.endpoint_def_id?;
    if index != callee
        || krate != rustc_hir::def_id::LOCAL_CRATE.as_u32()
        || value.endpoint != format!("def-id:{krate}:{index}")
    {
        return None;
    }
    Some(format!(
        "{}:{}:local:{callee}:{}:{}:{}:{}:{}:{}",
        value.owner,
        value.caller,
        value.arm,
        value.position,
        value.file,
        value.lo,
        value.hi,
        value.kind
    ))
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum RetentionUnknownReason {
    CalleeUnresolved,
    FnPtrWeb,
    OpenBoundary,
    MultiDef,
    NontransparentDef,
    ProjectionAmbiguous,
    OutputStorage,
    FieldOrGlobalStore,
    Return,
    LocalSummaryUnknown,
    AttestationAbsent,
    AnalysisIncomplete,
    ReturnedAliasUsed,
    ReturnedAliasUnknown,
}

fn unknown(value: raw_boundary::RetentionUnknownReason) -> RetentionUnknownReason {
    use raw_boundary::RetentionUnknownReason as Native;
    match value {
        Native::CalleeUnresolved => RetentionUnknownReason::CalleeUnresolved,
        Native::FnPtrWeb => RetentionUnknownReason::FnPtrWeb,
        Native::OpenBoundary => RetentionUnknownReason::OpenBoundary,
        Native::MultiDef => RetentionUnknownReason::MultiDef,
        Native::NontransparentDef => RetentionUnknownReason::NontransparentDef,
        Native::ProjectionAmbiguous => RetentionUnknownReason::ProjectionAmbiguous,
        Native::OutputStorage => RetentionUnknownReason::OutputStorage,
        Native::FieldOrGlobalStore => RetentionUnknownReason::FieldOrGlobalStore,
        Native::Return => RetentionUnknownReason::Return,
        Native::LocalSummaryUnknown => RetentionUnknownReason::LocalSummaryUnknown,
        Native::AttestationAbsent => RetentionUnknownReason::AttestationAbsent,
        Native::AnalysisIncomplete => RetentionUnknownReason::AnalysisIncomplete,
        Native::ReturnedAliasUsed => RetentionUnknownReason::ReturnedAliasUsed,
        Native::ReturnedAliasUnknown => RetentionUnknownReason::ReturnedAliasUnknown,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum RetentionEventKind {
    Transparent,
    Return,
    OutputStorage,
    FieldOrGlobalStore,
    UnknownCall,
    KnownNoRetainCall,
    LocalCall,
    DereferenceOnly,
    Free,
    MultiDef,
    Nontransparent,
    ReturnedAlias,
    ReturnedChildSink,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct RetentionStep {
    pub(crate) location: String,
    pub(crate) kind: RetentionEventKind,
    pub(crate) detail: String,
}

fn step(value: &raw_boundary::RetentionStep) -> RetentionStep {
    use raw_boundary::RetentionEventKind as Native;
    let kind = match value.kind {
        Native::Transparent => RetentionEventKind::Transparent,
        Native::Return => RetentionEventKind::Return,
        Native::OutputStorage => RetentionEventKind::OutputStorage,
        Native::FieldOrGlobalStore => RetentionEventKind::FieldOrGlobalStore,
        Native::UnknownCall => RetentionEventKind::UnknownCall,
        Native::KnownNoRetainCall => RetentionEventKind::KnownNoRetainCall,
        Native::LocalCall => RetentionEventKind::LocalCall,
        Native::DereferenceOnly => RetentionEventKind::DereferenceOnly,
        Native::Free => RetentionEventKind::Free,
        Native::MultiDef => RetentionEventKind::MultiDef,
        Native::Nontransparent => RetentionEventKind::Nontransparent,
        Native::ReturnedAlias => RetentionEventKind::ReturnedAlias,
        Native::ReturnedChildSink => RetentionEventKind::ReturnedChildSink,
    };
    RetentionStep {
        location: value.location.clone(),
        kind,
        detail: value.detail.clone(),
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct RetentionCertificate {
    pub(crate) function: String,
    pub(crate) argument_index: usize,
    pub(crate) steps: Vec<RetentionStep>,
    pub(crate) attestation: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Retention {
    NoRetain {
        certificate: RetentionCertificate,
    },
    Retains {
        sink: RetentionStep,
        path: Vec<RetentionStep>,
    },
    Unknown {
        reason: RetentionUnknownReason,
        frontier: Vec<RetentionStep>,
    },
}

fn retention(value: &RetentionVerdict) -> Retention {
    match value {
        RetentionVerdict::NoRetain { certificate } => Retention::NoRetain {
            certificate: RetentionCertificate {
                function: certificate.function.clone(),
                argument_index: certificate.argument_index,
                steps: certificate.steps.iter().map(step).collect(),
                attestation: certificate.attestation.into(),
            },
        },
        RetentionVerdict::Retains { sink, path } => Retention::Retains {
            sink: step(sink),
            path: path.iter().map(step).collect(),
        },
        RetentionVerdict::Unknown { reason, frontier } => Retention::Unknown {
            reason: unknown(*reason),
            frontier: frontier.iter().map(step).collect(),
        },
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Requirement {
    pub(crate) key: Key,
    pub(crate) bridge: BridgeKey,
    pub(crate) adapter: String,
    pub(crate) retention: Option<Retention>,
    pub(crate) native_lifetime: Option<mechanical_receipt::NativeReturnEvidence>,
    pub(crate) origins: Vec<Subject>,
    pub(crate) terminal_interface: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Row {
    pub(crate) required: Requirement,
    pub(crate) boundary_kind: String,
    pub(crate) endpoint: String,
    pub(crate) position: String,
    pub(crate) source_form: String,
    pub(crate) target_form: String,
    pub(crate) negative_write: String,
    pub(crate) tier: String,
    pub(crate) waiver: String,
    pub(crate) pair_role: String,
    pub(crate) effect_carrier: Option<String>,
    pub(crate) stage: String,
    pub(crate) state: String,
    pub(crate) reason: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Common {
    pub(crate) key: Key,
    pub(crate) source_form: String,
    pub(crate) target_form: String,
    pub(crate) argument_kind: String,
    pub(crate) negative_write: String,
    pub(crate) tier: String,
    pub(crate) waiver: String,
    pub(crate) terminal_interface: Option<String>,
    pub(crate) return_adapter: bool,
    pub(crate) extent_none: bool,
    pub(crate) stage: String,
    pub(crate) state: String,
    pub(crate) reason: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Bridge {
    pub(crate) key: BridgeKey,
    pub(crate) source_form: String,
    pub(crate) target_form: String,
    pub(crate) argument_kind: String,
    pub(crate) tier: String,
    pub(crate) waiver: String,
    pub(crate) extent_none: bool,
    pub(crate) stage: String,
    pub(crate) state: String,
    pub(crate) reason: Option<String>,
}

fn stage(value: MechanicalStage) -> String {
    match value {
        MechanicalStage::Plan => "plan",
        MechanicalStage::Terminal => "terminal",
    }
    .into()
}

fn state(value: MechanicalState) -> String {
    match value {
        MechanicalState::Planned => "planned",
        MechanicalState::Applied => "applied",
        MechanicalState::Dropped => "dropped",
        MechanicalState::HeldNonmechanical => "held-nonmechanical",
        MechanicalState::Reclassified => "reclassified",
    }
    .into()
}

fn tier(value: &MechanicalRetention) -> (String, String) {
    let (tier, waiver) = match value {
        MechanicalRetention::None => ("none", "-"),
        MechanicalRetention::T1 => ("T1", "-"),
        MechanicalRetention::T2 { waiver_id } => ("T2", waiver_id.as_str()),
        MechanicalRetention::PositiveRetention => ("positive-retention", "-"),
    };
    (tier.into(), waiver.into())
}

fn negative(value: &NegativeWriteEvidence) -> String {
    match value {
        NegativeWriteEvidence::NotApplicable => "not-applicable".into(),
        NegativeWriteEvidence::FosterImmutable => "foster-immutable".into(),
        NegativeWriteEvidence::LibcReadOnly(contract) => format!("libc-read-only:{contract}"),
        NegativeWriteEvidence::Missing => "negative-write-absent".into(),
        NegativeWriteEvidence::Writes => "callee-writes".into(),
    }
}

pub(crate) fn capture(artifact: &RawBoundaryArtifacts) -> Capture {
    let required = artifact
        .outbound_return_required
        .iter()
        .map(|value| Requirement {
            key: key(&value.key),
            bridge: bridge_key(&value.associated_bridge),
            adapter: value.adapter.clone(),
            retention: value.retention_evidence.as_ref().map(retention),
            native_lifetime: value.native_lifetime.clone(),
            origins: value.lifetime_origin.iter().map(subject).collect(),
            terminal_interface: value.terminal_interface.clone(),
        })
        .collect();
    let rows = artifact
        .outbound_return_rows
        .iter()
        .map(|value| {
            let (tier, waiver) = tier(&value.retention);
            Row {
                required: Requirement {
                    key: key(&value.terminal.obligation_key),
                    bridge: bridge_key(&value.associated_bridge),
                    adapter: value.adapter.clone(),
                    retention: value.retention_evidence.as_ref().map(retention),
                    native_lifetime: value.native_lifetime.clone(),
                    origins: value.lifetime_origin.iter().map(subject).collect(),
                    terminal_interface: value.terminal_interface.clone(),
                },
                boundary_kind: value.boundary_kind.clone(),
                endpoint: endpoint(&value.endpoint),
                position: value.position.clone(),
                source_form: value.source_form.clone(),
                target_form: value.target_form.clone(),
                negative_write: negative(&value.negative_write),
                tier,
                waiver,
                pair_role: value.pair_role.clone(),
                effect_carrier: value.effect_carrier.as_ref().map(|site| site.receipt_key()),
                stage: stage(value.terminal.stage),
                state: state(value.terminal.state),
                reason: value.terminal.reason.as_ref().map(|reason| reason.key()),
            }
        })
        .collect();
    let common = artifact
        .mechanical_events
        .iter()
        .filter(|value| mechanical_receipt::is_outbound_return_family(value.key.family))
        .map(|value| {
            let (tier, waiver) = tier(&value.evidence.retention);
            Common {
                key: key(&value.key),
                source_form: value.found_form.clone(),
                target_form: value.expected_form.clone(),
                argument_kind: value.argument_kind.clone(),
                negative_write: negative(&value.evidence.negative_write),
                tier,
                waiver,
                terminal_interface: match &value.evidence.terminal_contract {
                    TerminalContract::Required { interface } => Some(interface.clone()),
                    TerminalContract::Optional { .. }
                    | TerminalContract::NotApplicable
                    | TerminalContract::Missing => None,
                },
                return_adapter: value.mechanism
                    == if value.key.family == MechanicalFamily::FlowsIntoRawParam {
                        MechanicalMechanism::RawParameterView
                    } else {
                        MechanicalMechanism::ReturnAdapter
                    },
                extent_none: value.evidence.extent == MechanicalExtent::None,
                stage: stage(value.stage),
                state: state(value.state),
                reason: value.terminal_reason.as_ref().map(|reason| reason.key()),
            }
        })
        .collect();
    // Independent reverse inventory: do not filter these through output rows.
    let active = artifact
        .bridge_events
        .iter()
        .filter(|value| {
            mechanical_receipt::is_return_receipt_kind(&value.site.bridge_kind)
                && value.stage == BridgeReceiptStage::Terminal
                && value.state == BridgeReceiptState::Applied
        })
        .map(|value| value.site.receipt_key())
        .collect::<BTreeSet<_>>();
    let bridges = artifact
        .bridge_events
        .iter()
        .filter(|value| active.contains(&value.site.receipt_key()))
        .map(project_bridge)
        .collect();
    let mut capture_errors = artifact
        .outbound_return_error
        .iter()
        .cloned()
        .collect::<Vec<_>>();
    if let Err(error) = mechanical_receipt::reconcile_outbound_return_rows(
        &artifact.outbound_return_required,
        &artifact.outbound_return_rows,
        &artifact.mechanical_events,
        &artifact.bridge_events,
    ) {
        capture_errors.push(error);
    }
    Capture {
        required,
        rows,
        common,
        bridges,
        rendered_tsv: mechanical_receipt::render_outbound_return_rows(
            &artifact.outbound_return_rows,
        ),
        capture_errors,
    }
}

fn project_bridge(value: &BridgeReceiptEvent) -> Bridge {
    Bridge {
        key: bridge_key(&value.site),
        source_form: value.found_form.clone(),
        target_form: value.expected_form.clone(),
        argument_kind: value.argument_kind.clone(),
        tier: match value.retention {
            BridgeRetentionTier::None => "none",
            BridgeRetentionTier::T1 => "T1",
            BridgeRetentionTier::T2 => "T2",
        }
        .into(),
        waiver: value.waiver_id.clone().unwrap_or_else(|| "-".into()),
        extent_none: value.extent == BridgeExtentKind::None,
        stage: match value.stage {
            BridgeReceiptStage::Plan => "plan",
            BridgeReceiptStage::Terminal => "terminal",
        }
        .into(),
        state: match value.state {
            BridgeReceiptState::Planned => "planned",
            BridgeReceiptState::Applied => "applied",
            BridgeReceiptState::Dropped => "dropped",
        }
        .into(),
        reason: value.drop_reason.clone(),
    }
}

fn fail(reason: &str) -> String {
    format!("outbound-return-transport:{reason}")
}

pub(crate) fn validate(capture: &Capture) -> Result<(), String> {
    if !capture.capture_errors.is_empty() {
        return Err(fail("native-capture-error"));
    }
    let mut required = BTreeMap::new();
    let mut expected_bridges = BTreeMap::new();
    for value in &capture.required {
        let key = &value.key;
        let bridge = &value.bridge;
        let expression = bridge.kind == "outbound-native-return-argument";
        let Some(callee) = bridge.callee else { return Err(fail("nonlocal-endpoint")) };
        if canonical_obligation(key).as_ref() != Some(&key.key)
            || canonical_bridge(bridge).as_ref() != Some(&bridge.key)
            || key.endpoint_def_id != bridge.endpoint_def_id
            || key.argument_index.is_some() != expression
            || key.slot_depth != 0
            || required.insert(key.key.clone(), value).is_some()
            || expected_bridges
                .insert(bridge.key.clone(), key.key.clone())
                .is_some()
            || key.family
                != if expression {
                    "flows-into-raw-param"
                } else {
                    "return-not-adapted"
                }
            || key.owner != bridge.owner
            || (!expression && bridge.owner != callee)
            || key.caller != bridge.caller
            || key.endpoint.as_ref() != Some(&bridge.endpoint)
            || key.hir_owner != Some(bridge.caller)
            || !mechanical_receipt::is_return_receipt_kind(&bridge.kind)
            || value.adapter.is_empty()
            || value.adapter == "-"
            || value.terminal_interface.is_empty()
            || value.terminal_interface == "raw"
        {
            return Err(fail("required-identity-or-evidence"));
        }
        let null = bridge.kind == "return-null-to-option";
        if bridge.kind == "return-caller-receive-raw" {
            if value.native_lifetime.is_some()
                || !matches!(value.retention, Some(Retention::Unknown { .. }))
            {
                return Err(fail("raw-receiver-evidence"));
            }
        } else if expression {
            let Some(proof) = &value.native_lifetime else {
                return Err(fail("missing-argument-lifetime"));
            };
            if proof.owner != key.owner
                || proof.lifetime.is_empty()
                || proof.plan_digest.is_empty()
                || !matches!(
                    value.retention,
                    Some(Retention::NoRetain { .. } | Retention::Unknown { .. })
                )
            {
                return Err(fail("argument-native-retention-evidence"));
            }
        } else {
            let Some(proof) = &value.native_lifetime else {
                return Err(fail("missing-native-lifetime"));
            };
            if value.retention.is_some()
                || proof.owner != callee
                || proof.lifetime.is_empty()
                || proof.plan_digest.is_empty()
                || bridge.caller != callee
            {
                return Err(fail("native-lifetime-evidence"));
            }
        }
        if expression {
            if !matches!(&key.subject.generated, Some((owner, name, 0)) if *owner == bridge.caller
                && key.hir_item_local_id.is_some_and(|hir| *name == format!("outbound-expression:{hir}")))
            {
                return Err(fail("native-argument-subject"));
            }
        } else if null {
            if !matches!(&key.subject.generated, Some((owner, name, 0)) if *owner == bridge.caller
                && key.hir_item_local_id.is_some_and(|hir| *name == format!("return-expression:{hir}")))
                || !value.origins.is_empty()
            {
                return Err(fail("null-return-subject"));
            }
        } else if !matches!(key.subject.local, Some((owner, local, 0)) if owner == bridge.caller && local > 0)
        {
            return Err(fail("borrowed-return-subject"));
        }
        let origin_owner = if expression { key.owner } else { callee };
        let mut origins = BTreeSet::new();
        if (!null && value.origins.is_empty()) || value.origins.iter().any(|origin| {
            !matches!(origin.local, Some((owner, local, 0)) if owner == origin_owner && local > 0)
                || canonical_subject(origin).as_ref() != Some(&origin.key)
                || !origins.insert(origin.key.clone())
        }) {
            return Err(fail("origin-custody"));
        }
    }
    let mut bridges = BTreeMap::new();
    for value in &capture.bridges {
        if !expected_bridges.contains_key(&value.key.key)
            || bridges
                .insert((value.key.key.clone(), value.stage.clone()), value)
                .is_some()
        {
            return Err(fail("unowned-or-duplicate-bridge"));
        }
    }
    let mut common = BTreeMap::new();
    for value in &capture.common {
        if required.get(&value.key.key).map(|required| &required.key) != Some(&value.key)
            || common
                .insert((value.key.key.clone(), value.stage.clone()), value)
                .is_some()
        {
            return Err(fail("unowned-or-duplicate-common"));
        }
    }
    let mut rows = BTreeMap::new();
    for value in &capture.rows {
        if required.get(&value.required.key.key).copied() != Some(&value.required)
            || rows
                .insert((value.required.key.key.clone(), value.stage.clone()), value)
                .is_some()
        {
            return Err(fail("unowned-duplicate-or-metadata-row"));
        }
    }
    if rows.len() != required.len() * 2 || common.len() != rows.len() || bridges.len() != rows.len()
    {
        return Err(fail("stage-cardinality"));
    }
    for (key, required) in &required {
        for (stage, state) in [("plan", "planned"), ("terminal", "applied")] {
            let tuple = (key.clone(), stage.to_owned());
            let row = rows
                .get(&tuple)
                .ok_or_else(|| fail("missing-specialized-stage"))?;
            let event = common
                .get(&tuple)
                .ok_or_else(|| fail("missing-common-stage"))?;
            let bridge = bridges
                .get(&(required.bridge.key.clone(), stage.to_owned()))
                .ok_or_else(|| fail("missing-bridge-stage"))?;
            let source_contract = match row.boundary_kind.as_str() {
                "outbound-native-return-argument" => {
                    row.source_form == required.terminal_interface
                        && row.target_form == "raw"
                        && match (&required.retention, row.tier.as_str(), row.waiver.as_str()) {
                            (Some(Retention::NoRetain { certificate }), "T1", "-") => {
                                required
                                    .key
                                    .argument_index
                                    .and_then(|index| usize::try_from(index).ok())
                                    == Some(certificate.argument_index)
                            }
                            (Some(Retention::Unknown { .. }), "T2", waiver) => {
                                waiver == RAW_BOUNDARY_T2_WAIVER_ID
                            }
                            _ => false,
                        }
                }
                "return-caller-receive-raw" => {
                    row.source_form == required.terminal_interface
                        && row.target_form == "raw"
                        && row.tier == "T2"
                        && row.waiver == RAW_BOUNDARY_T2_WAIVER_ID
                }
                "return-raw-to-ref" => {
                    row.target_form == required.terminal_interface
                        && !row.source_form.is_empty()
                        && row.target_form != "raw"
                        && row.tier == "T1"
                        && row.waiver == "-"
                }
                "return-null-to-option" => {
                    row.target_form == required.terminal_interface
                        && matches!(
                            row.target_form.as_str(),
                            "opt-ref-mut" | "opt-ref-shared" | "opt-slice-mut" | "opt-slice-shared"
                        )
                        && row.source_form == "raw"
                        && row.tier == "none"
                        && row.waiver == "-"
                }
                _ => false,
            };
            if !source_contract
                || row.state != state
                || event.state != state
                || bridge.state != state
                || row.reason.is_some()
                || event.reason.is_some()
                || bridge.reason.is_some()
                || row.boundary_kind != required.bridge.kind
                || row.endpoint != required.bridge.endpoint
                || row.position != required.bridge.position
                || row.pair_role != "not-applicable"
                || row.effect_carrier.is_some()
                || row.source_form != event.source_form
                || row.target_form != event.target_form
                || row.negative_write != event.negative_write
                || row.tier != event.tier
                || row.waiver != event.waiver
                || event.terminal_interface.as_ref() != Some(&required.terminal_interface)
                || !event.return_adapter
                || !event.extent_none
                || bridge.key != required.bridge
                || bridge.source_form != row.source_form
                || bridge.target_form != row.target_form
                || bridge.argument_kind != event.argument_kind
                || bridge.tier != row.tier
                || bridge.waiver != row.waiver
                || !bridge.extent_none
            {
                return Err(fail("common-specialized-bridge-drift"));
            }
        }
        let planned = rows[&(key.clone(), "plan".into())];
        let mut terminal = (*rows[&(key.clone(), "terminal".into())]).clone();
        terminal.stage = planned.stage.clone();
        terminal.state = planned.state.clone();
        terminal.reason = planned.reason.clone();
        if &terminal != planned {
            return Err(fail("cross-stage-metadata"));
        }
    }
    if capture.rendered_tsv != render(&capture.rows) {
        return Err(fail("rendered-sidecar-drift"));
    }
    Ok(())
}

fn render(rows: &[Row]) -> String {
    let mut lines = rows
        .iter()
        .map(|row| {
            let required = &row.required;
            let origins = required
                .origins
                .iter()
                .map(|origin| origin.key.as_str())
                .collect::<Vec<_>>()
                .join(";");
            [
                required.key.key.clone(),
                row.boundary_kind.clone(),
                row.endpoint.clone(),
                row.position.clone(),
                row.source_form.clone(),
                row.target_form.clone(),
                required.adapter.clone(),
                row.negative_write.clone(),
                match (&required.retention, &required.native_lifetime) {
                    (Some(retention), Some(native)) => {
                        format!("retention={retention:?};native_lifetime={native:?}")
                    }
                    (Some(retention), None) => format!("{retention:?}"),
                    (None, Some(native)) => format!("{native:?}"),
                    (None, None) => "-".into(),
                },
                row.tier.clone(),
                row.waiver.clone(),
                if origins.is_empty() {
                    "-".into()
                } else {
                    origins
                },
                row.pair_role.clone(),
                row.effect_carrier.clone().unwrap_or_else(|| "-".into()),
                required.terminal_interface.clone(),
                row.stage.clone(),
                row.state.clone(),
                row.reason.clone().unwrap_or_else(|| "-".into()),
            ]
            .join("\t")
        })
        .collect::<Vec<_>>();
    lines.sort();
    let mut output = mechanical_receipt::specialized_receipt_headers()
        [crate::raw_boundary_census_schema::OUTBOUND_RETURN_BRIDGE_ROWS]
        .join("\t");
    output.push('\n');
    for line in lines {
        output.push_str(&line);
        output.push('\n');
    }
    output
}

/// The retained worker packet is the independent replay input. The sidecars
/// are supplied separately by the stamped, manifest-checked file reader.
pub(crate) fn validate_sidecars(
    captured: Option<&Capture>,
    sidecar: Option<&Capture>,
    tsv: Option<&str>,
    frame: &BTreeMap<String, String>,
    normalization_roots: &[String],
) -> Result<(), String> {
    let captured = captured.ok_or_else(|| fail("missing-capture"))?;
    validate(captured)?;
    let sidecar = sidecar.ok_or_else(|| fail("missing-json-sidecar"))?;
    if sidecar != captured {
        return Err(fail("json-sidecar-mismatch"));
    }
    let text = tsv.ok_or_else(|| fail("missing-tsv-sidecar"))?;
    let mut lines = text.lines();
    let header = lines
        .next()
        .ok_or_else(|| fail("tsv-no-header"))?
        .split('\t')
        .collect::<Vec<_>>();
    let mut expected = captured.rendered_tsv.lines();
    let columns = expected
        .next()
        .ok_or_else(|| fail("capture-no-header"))?
        .split('\t')
        .collect::<Vec<_>>();
    if header.len() < columns.len()
        || header.iter().copied().collect::<BTreeSet<_>>().len() != header.len()
    {
        return Err(fail("tsv-header"));
    }
    let prefix = header.len() - columns.len();
    if header[prefix..] != columns {
        return Err(fail("tsv-header"));
    }
    for name in frame.keys().chain(std::iter::once(&"data".to_owned())) {
        if !header[..prefix].contains(&name.as_str()) {
            return Err(fail("tsv-missing-frame-column"));
        }
    }
    let mut actual = Vec::new();
    for line in lines {
        let cells = line.split('\t').collect::<Vec<_>>();
        if cells.len() != header.len() {
            return Err(fail("tsv-width"));
        }
        for (name, expected) in frame {
            let index = header[..prefix]
                .iter()
                .position(|column| *column == name)
                .unwrap();
            if cells[index] != expected {
                return Err(fail("tsv-frame-mismatch"));
            }
        }
        let data = header[..prefix]
            .iter()
            .position(|column| *column == "data")
            .unwrap();
        if !matches!(cells[data], "true" | "provisional") {
            return Err(fail("tsv-not-data"));
        }
        actual.push(cells[prefix..].join("\t"));
    }
    let expected = expected
        .map(|line| {
            normalization_roots
                .iter()
                .fold(line.to_owned(), |line, root| {
                    line.replace(root, "<program>")
                })
        })
        .collect::<Vec<_>>();
    if actual != expected {
        return Err(fail("tsv-payload-mismatch"));
    }
    Ok(())
}
