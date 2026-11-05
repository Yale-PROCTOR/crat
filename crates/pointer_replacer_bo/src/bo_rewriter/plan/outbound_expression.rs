//! Custody for native borrowed call expressions passed to raw parameters.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;

use super::super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, RAW_BOUNDARY_T2_WAIVER_ID,
        SignatureClassId,
    },
    decision::{
        DecisionTable, SubjectKind,
        lifetime::{FnSignatureRoot, FnSignatureSlot},
        outbound_expression::{OutboundExpressionPlan, OutboundExpressionPlans},
        raw_boundary::{
            NegativeWriteEvidence as RawNegativeWriteEvidence, RawBoundarySiteKey, RawMutability,
            RetentionVerdict,
        },
        seam::Form,
    },
    mechanical_receipt::{
        CanonicalCallee, CanonicalLocation, CanonicalSiteKey, MechanicalEvidence, MechanicalExtent,
        MechanicalFamily, MechanicalMechanism, MechanicalObligationEvent, MechanicalObligationKey,
        MechanicalObligationPlan, MechanicalRetention, MechanicalStage, MechanicalState,
        MechanicalSubjectKey, NativeReturnEvidence, NegativeWriteEvidence,
        OutboundReturnBridgeReceiptRow, OutboundReturnReceiptPlan, OutboundReturnRequirement,
        TerminalContract,
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Failure {
    pub(crate) key: RawBoundarySiteKey,
    pub(crate) owner_class: SignatureClassId,
    pub(crate) reason: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct OutboundExpressionReceiptPlans {
    sources: OutboundExpressionPlans,
    requirements: FxHashMap<RawBoundarySiteKey, OutboundReturnRequirement>,
    blueprints: FxHashMap<RawBoundarySiteKey, OutboundReturnReceiptPlan>,
    failures: FxHashMap<RawBoundarySiteKey, Failure>,
}

pub(crate) type Materialized = (
    Vec<OutboundReturnRequirement>,
    Vec<MechanicalObligationEvent>,
    Vec<OutboundReturnBridgeReceiptRow>,
);

fn endpoint(input: &OutboundExpressionPlan) -> CanonicalCallee {
    match &input.sink_callee {
        BridgeCalleeId::Local(callee) => CanonicalCallee::Local(callee.to_def_id()),
        BridgeCalleeId::Foreign(symbol) => CanonicalCallee::Foreign(symbol.clone()),
    }
}

fn failure(
    key: &RawBoundarySiteKey,
    owner_class: SignatureClassId,
    reason: impl Into<String>,
) -> Failure {
    Failure {
        key: key.clone(),
        owner_class,
        reason: reason.into(),
    }
}

pub(crate) fn capture(
    table: &DecisionTable,
    inputs: &OutboundExpressionPlans,
    sites: &FxHashMap<RawBoundarySiteKey, super::ClassSite>,
    owner_path: &impl Fn(LocalDefId) -> Option<String>,
) -> OutboundExpressionReceiptPlans {
    let mut plans = OutboundExpressionReceiptPlans {
        sources: inputs.clone(),
        ..Default::default()
    };
    for (key, input) in &inputs.plans {
        let result = if inputs.unavailable.contains_key(key) {
            Err("outbound-expression:input-populations-overlap".into())
        } else if input.key != *key {
            Err("outbound-expression:source-key-mismatch".into())
        } else {
            capture_one(table, input, sites.get(key), owner_path)
        };
        match result {
            Ok((requirement, blueprint)) => {
                plans.requirements.insert(key.clone(), requirement);
                plans.blueprints.insert(key.clone(), blueprint);
            }
            Err(reason) => {
                plans
                    .failures
                    .insert(key.clone(), failure(key, input.owner_class(), reason));
            }
        }
    }
    plans
}

fn capture_one(
    table: &DecisionTable,
    input: &OutboundExpressionPlan,
    site: Option<&super::ClassSite>,
    owner_path: &impl Fn(LocalDefId) -> Option<String>,
) -> Result<(OutboundReturnRequirement, OutboundReturnReceiptPlan), String> {
    if input.argument_hir.owner.def_id != input.caller
        || input.argument_span.is_dummy()
        || input.call_span.is_dummy()
        || input.source_interface.form == Form::Raw
        || input.target.depth2.is_some()
        || input.original_expression.is_empty()
        || input.temporary.is_empty()
        || input.spec.template_key() != input.template.key()
        || table.return_interfaces.functions.get(&input.source_callee)
            != Some(&input.source_interface)
    {
        return Err("outbound-expression:native-input-identity-mismatch".into());
    }
    let lifetime = table
        .lifetime_plan
        .function(input.source_callee)
        .ok_or("outbound-expression:native-lifetime-missing")?;
    let digest = lifetime.digest();
    if digest != input.source_interface.lifetime_plan_digest
        || lifetime.lifetime_for(FnSignatureSlot::RETURN)
            != Some(input.source_interface.lifetime.as_str())
    {
        return Err("outbound-expression:native-lifetime-drift".into());
    }
    let mut origins = Vec::new();
    for source in lifetime.return_sources() {
        let FnSignatureRoot::Arg(index) = source.root else {
            return Err("outbound-expression:native-origin-not-parameter".into());
        };
        if index == 0 || source.depth != 0 || source.deref_depth != 0 {
            return Err("outbound-expression:native-origin-depth-unrepresented".into());
        }
        let parameters = table
            .entries
            .iter()
            .filter(|(subject, _)| {
                subject.fn_did == input.source_callee
                    && matches!(subject.kind,
                SubjectKind::Param { hir_index }
                    if hir_index.checked_add(1).and_then(|i| u32::try_from(i).ok()) == Some(index))
            })
            .collect::<Vec<_>>();
        let [(parameter, _)] = parameters.as_slice() else {
            return Err("outbound-expression:native-origin-parameter-unmapped".into());
        };
        if parameter.local.as_u32() == 0 {
            return Err("outbound-expression:native-origin-is-return-slot".into());
        }
        origins.push(MechanicalSubjectKey::Local {
            owner: parameter.fn_did,
            mir_local: parameter.local.as_u32(),
            slot_depth: 0,
        });
    }
    origins.sort_by_key(MechanicalSubjectKey::receipt_key);
    origins.dedup();
    if origins.is_empty() {
        return Err("outbound-expression:native-origins-empty".into());
    }
    let retention = match (&input.retention, input.tier, input.waiver_id) {
        (RetentionVerdict::NoRetain { certificate }, BridgeRetentionTier::T1, None)
            if certificate.argument_index == input.key.argument_index
                && certificate.function == input.key.callee.path =>
        {
            MechanicalRetention::T1
        }
        (RetentionVerdict::Unknown { .. }, BridgeRetentionTier::T2, Some(waiver))
            if waiver == RAW_BOUNDARY_T2_WAIVER_ID =>
        {
            MechanicalRetention::T2 {
                waiver_id: waiver.into(),
            }
        }
        _ => return Err("outbound-expression:retention-evidence-mismatch".into()),
    };
    let negative_write = match input.negative_write {
        Some(RawNegativeWriteEvidence::FosterImmutable) => NegativeWriteEvidence::FosterImmutable,
        Some(RawNegativeWriteEvidence::LibcReadOnly) => {
            NegativeWriteEvidence::LibcReadOnly(input.key.callee.path.clone())
        }
        None => {
            if input.target.mutability == RawMutability::Mut
                && matches!(
                    input.source_interface.form,
                    Form::Ref { mutable: false }
                        | Form::Slice { mutable: false }
                        | Form::Opt { mutable: false, .. }
                )
            {
                return Err("outbound-expression:shared-to-mut-negative-write-missing".into());
            }
            NegativeWriteEvidence::NotApplicable
        }
    };
    let site = site.ok_or("outbound-expression:common-site-missing")?;
    let bridge = input.bridge();
    let expected = bridge.materialize(
        input.owner_class(),
        site.key.file.clone(),
        site.key.lo,
        site.key.hi,
    );
    if site.key != expected
        || !matches!(site.state, super::ClassSiteState::EditReady)
        || !site.atom_ids.is_empty()
        || site.key.lo >= site.key.hi
        || site.expected_form != bridge.expected_form
        || site.found_form != bridge.found_form
        || site.argument_kind != bridge.argument_kind
        || site.extent != BridgeExtentKind::None
        || site.retention != bridge.retention
        || site.waiver_id != bridge.waiver_id
        || site.unsafe_context != bridge.unsafe_context
    {
        return Err("outbound-expression:common-site-evidence-mismatch".into());
    }
    let argument_index = u32::try_from(input.key.argument_index)
        .map_err(|_| "outbound-expression:argument-index-overflow")?;
    let key = MechanicalObligationKey {
        owner_class: input.owner_class(),
        subject: MechanicalSubjectKey::Generated {
            owner: input.caller,
            key: format!(
                "outbound-expression:{}",
                input.argument_hir.local_id.as_u32()
            ),
            slot_depth: 0,
        },
        site: CanonicalSiteKey {
            owner: input.caller,
            location: CanonicalLocation::Hir {
                owner: input.argument_hir.owner.def_id,
                item_local_id: input.argument_hir.local_id.as_u32(),
            },
            callee: Some(endpoint(input)),
            argument_index: Some(argument_index),
            slot_depth: 0,
        },
        family: MechanicalFamily::FlowsIntoRawParam,
    };
    let required = OutboundReturnRequirement {
        key: key.clone(),
        associated_bridge: site.key.clone(),
        adapter: input.template.key().into(),
        retention_evidence: Some(input.retention.clone()),
        native_lifetime: Some(NativeReturnEvidence {
            owner: input.source_callee.local_def_index.as_u32(),
            lifetime: input.source_interface.lifetime.clone(),
            plan_digest: digest,
        }),
        lifetime_origin: origins,
        terminal_interface: input.source_interface.form.key().into(),
    };
    let owner_path = owner_path(input.source_callee)
        .filter(|path| !path.is_empty())
        .ok_or("outbound-expression:owner-path-missing")?;
    let event = MechanicalObligationEvent {
        key: key.clone(),
        owner_path,
        prior_reason: "flows-into-raw-param".into(),
        expected_form: site.expected_form.clone(),
        found_form: site.found_form.clone(),
        argument_kind: site.argument_kind.clone(),
        source_shape: "raw-expr".into(),
        required_arms: site.key.arm.clone(),
        mechanism: MechanicalMechanism::RawParameterView,
        composition_parent: None,
        dependency_classes: BTreeSet::from([key.owner_class]),
        evidence: MechanicalEvidence {
            extent: MechanicalExtent::None,
            retention: retention.clone(),
            negative_write: negative_write.clone(),
            terminal_contract: TerminalContract::Required {
                interface: required.terminal_interface.clone(),
            },
            unsafe_context: site.unsafe_context,
            ..Default::default()
        },
        stage: MechanicalStage::Plan,
        state: MechanicalState::Planned,
        terminal_reason: None,
    };
    let blueprint = OutboundReturnReceiptPlan {
        obligation: MechanicalObligationPlan {
            planned: event,
            intended_terminal_state: MechanicalState::Applied,
            intended_terminal_reason: None,
        },
        associated_bridge: required.associated_bridge.clone(),
        boundary_kind: site.key.bridge_kind.clone(),
        endpoint: endpoint(input),
        position: site.key.position.clone(),
        source_form: site.found_form.clone(),
        target_form: site.expected_form.clone(),
        adapter: required.adapter.clone(),
        negative_write,
        retention,
        retention_evidence: required.retention_evidence.clone(),
        native_lifetime: required.native_lifetime.clone(),
        lifetime_origin: required.lifetime_origin.clone(),
        pair_role: "not-applicable".into(),
        effect_carrier: None,
        terminal_interface: required.terminal_interface.clone(),
    };
    Ok((required, blueprint))
}

impl OutboundExpressionReceiptPlans {
    pub(crate) fn materialize(
        &self,
        terminal: &OutboundExpressionPlans,
        classes: &BTreeSet<SignatureClassId>,
    ) -> Result<Materialized, Vec<Failure>> {
        let (mut requirements, mut common, mut rows, mut failures) =
            (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        // Every live terminal expression needs its frozen native source even
        // if both J27 output populations, or the whole producer, were lost.
        for (key, input) in terminal
            .plans
            .iter()
            .filter(|(_, input)| input.active(classes))
        {
            if self.sources.plans.get(key) != Some(input)
                || self.sources.unavailable.contains_key(key)
            {
                failures.push(failure(
                    key,
                    input.owner_class(),
                    "outbound-expression:terminal-source-inventory-drift",
                ));
            }
        }
        for (key, input) in self.sources.unavailable.iter().chain(&terminal.unavailable) {
            let owner = SignatureClassId::of(input.source_callee);
            if !classes.contains(&owner) {
                failures.push(failure(
                    key,
                    owner,
                    "outbound-expression:live-input-unavailable",
                ));
            }
        }
        for (key, input) in self
            .sources
            .plans
            .iter()
            .filter(|(_, input)| input.active(classes))
        {
            let result = (|| {
                if terminal.plans.get(key) != Some(input) || terminal.unavailable.contains_key(key)
                {
                    return Err("outbound-expression:terminal-source-inventory-drift".into());
                }
                if let Some(failure) = self.failures.get(key) {
                    return Err(failure.reason.clone());
                }
                let required = self
                    .requirements
                    .get(key)
                    .ok_or("outbound-expression:required-metadata-missing")?;
                requirements.push(required.clone());
                let blueprint = self
                    .blueprints
                    .get(key)
                    .ok_or("outbound-expression:blueprint-missing")?;
                if required.key != blueprint.obligation.planned.key {
                    return Err("outbound-expression:selection-key-drift".into());
                }
                let (events, specialized) = blueprint.materialize(true, false);
                common.extend(events);
                rows.extend(specialized);
                Ok(())
            })();
            if let Err(reason) = result {
                failures.push(failure(key, input.owner_class(), reason));
            }
        }
        if failures.is_empty() {
            Ok((requirements, common, rows))
        } else {
            Err(failures)
        }
    }
}
