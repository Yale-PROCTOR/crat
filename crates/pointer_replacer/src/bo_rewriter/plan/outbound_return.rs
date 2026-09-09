//! J27 native borrowed results received through owned raw initializer views.
//! Requirements are captured from native inputs independently of row outputs.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::mir::Local;
use rustc_span::Span;

use super::super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, RAW_BOUNDARY_T2_WAIVER_ID,
        SignatureClassId,
    },
    decision::{
        Decision, DecisionTable, SubjectKind,
        lifetime::{FnSignatureRoot, FnSignatureSlot},
        raw_boundary::{BridgeTemplate, RetentionVerdict},
        raw_receiver::{RawReceiverPlan, RawReceiverPlans},
        receiver_input::{ReceiverInputMap, ReceiverInputPlan},
        return_interface::ReturnInterface,
        return_receiver::Node,
        seam::Form,
    },
    mechanical_receipt::{
        CanonicalCallee, CanonicalLocation, CanonicalSiteKey, MechanicalEvidence, MechanicalExtent,
        MechanicalFamily, MechanicalMechanism, MechanicalObligationEvent, MechanicalObligationKey,
        MechanicalObligationPlan, MechanicalRetention, MechanicalStage, MechanicalState,
        MechanicalSubjectKey, NegativeWriteEvidence, OutboundReturnBridgeReceiptRow,
        OutboundReturnReceiptPlan, OutboundReturnRequirement, TerminalContract,
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Failure {
    pub(crate) node: Node,
    pub(crate) key: MechanicalObligationKey,
    pub(crate) reason: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct OutboundReturnPlans {
    requirements: FxHashMap<Node, OutboundReturnRequirement>,
    blueprints: FxHashMap<Node, OutboundReturnReceiptPlan>,
    failures: FxHashMap<Node, Failure>,
}

pub(crate) type Materialized = (
    Vec<OutboundReturnRequirement>,
    Vec<MechanicalObligationEvent>,
    Vec<OutboundReturnBridgeReceiptRow>,
);

fn in_scope(input: &ReceiverInputPlan) -> bool {
    match input.receiver.candidate_interface.form {
        Form::Raw => false,
        Form::Ref { .. } | Form::Slice { .. } | Form::Opt { .. } => true,
    }
}

struct ReceiptSource<'a> {
    node: Node,
    callee: LocalDefId,
    initializer_hir: HirId,
    initializer_span: Span,
    interface: &'a ReturnInterface,
    destination: Local,
    retention: &'a RetentionVerdict,
    tier: BridgeRetentionTier,
    waiver_id: &'static str,
    template: BridgeTemplate,
    site: super::ClassSite,
}

fn obligation_key(
    node: Node,
    callee: LocalDefId,
    hir: HirId,
    destination: Local,
) -> MechanicalObligationKey {
    MechanicalObligationKey {
        owner_class: SignatureClassId::of(callee),
        subject: MechanicalSubjectKey::Local {
            owner: node.0,
            mir_local: destination.as_u32(),
            slot_depth: 0,
        },
        site: CanonicalSiteKey {
            owner: node.0,
            location: CanonicalLocation::Hir {
                owner: hir.owner.def_id,
                item_local_id: hir.local_id.as_u32(),
            },
            callee: Some(CanonicalCallee::Local(callee.to_def_id())),
            argument_index: None,
            slot_depth: 0,
        },
        family: MechanicalFamily::ReturnNotAdapted,
    }
}

fn admitted_key(input: &ReceiverInputPlan) -> MechanicalObligationKey {
    obligation_key(
        input.receiver.node,
        input.receiver.callee,
        input.receiver.initializer_hir,
        input.destination,
    )
}

fn raw_key(input: &RawReceiverPlan) -> MechanicalObligationKey {
    obligation_key(
        input.node,
        input.callee,
        input.initializer_hir,
        input.view.destination,
    )
}

pub(crate) fn capture(
    table: &DecisionTable,
    inputs: &ReceiverInputMap,
    receiver_receipts: &super::receiver_input::ReceiverReceiptMap,
    raw_inputs: &RawReceiverPlans,
    raw_sites: &FxHashMap<Node, super::ClassSite>,
    owner_path: &impl Fn(LocalDefId) -> Option<String>,
) -> OutboundReturnPlans {
    let mut plans = OutboundReturnPlans::default();
    for (&node, input) in &inputs.plans {
        if !in_scope(input) {
            continue;
        }
        let key = admitted_key(input);
        let result = (|| {
            if raw_inputs.plans.contains_key(&node) || raw_inputs.unavailable.contains_key(&node) {
                return Err("outbound-return:receiver-populations-overlap".into());
            }
            let receiver = &input.receiver;
            if receiver.node != node
                || input.selection.node != node
                || input.selection.callee != key.owner_class
                || table.return_receivers.plans.get(&node) != Some(receiver)
            {
                return Err("outbound-return:receiver-native-identity-mismatch".into());
            }
            let site = receiver_receipts
                .selected_raw_site(node, input)
                .map_err(|failure| {
                    format!("outbound-return:common-bridge-mapping:{}", failure.reason)
                })?;
            let source = ReceiptSource {
                node,
                callee: receiver.callee,
                initializer_hir: receiver.initializer_hir,
                initializer_span: receiver.initializer_span,
                interface: &receiver.candidate_interface,
                destination: input.destination,
                retention: &input.retention,
                tier: input.tier,
                waiver_id: input.waiver_id,
                template: input.template,
                site,
            };
            capture_one(table, &source, owner_path, &key)
        })();
        record(&mut plans, node, key, result);
    }
    for (&node, input) in &raw_inputs.plans {
        let key = raw_key(input);
        let result = (|| {
            if inputs.plans.contains_key(&node) || inputs.unavailable.contains_key(&node) {
                return Err("outbound-return:receiver-populations-overlap".into());
            }
            let actual = table
                .entries
                .iter()
                .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node);
            let raw = actual.is_some_and(|(_, decision)| match decision {
                Decision::Degraded(_) => true,
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_) => false,
            });
            if !raw
                || input.node != node
                || table.seams.raw_receivers.plans.get(&node) != Some(input)
                || input.view.site.node != node
                || input.view.site.callee != input.callee
                || input.view.site.initializer_span != input.initializer_span
                || input.view.site.source_interface != input.source_interface
                || input.view.site.raw_result != input.raw_result
            {
                return Err("outbound-return:raw-receiver-native-identity-mismatch".into());
            }
            let site = raw_sites
                .get(&node)
                .ok_or("outbound-return:raw-receiver-common-site-missing")?
                .clone();
            let expected = input.bridge().materialize(
                key.owner_class,
                site.key.file.clone(),
                site.key.lo,
                site.key.hi,
            );
            if site.key != expected || !matches!(site.state, super::ClassSiteState::EditReady) {
                return Err("outbound-return:raw-receiver-common-site-mismatch".into());
            }
            let source = ReceiptSource {
                node,
                callee: input.callee,
                initializer_hir: input.initializer_hir,
                initializer_span: input.initializer_span,
                interface: &input.source_interface,
                destination: input.view.destination,
                retention: &input.view.retention,
                tier: input.view.tier,
                waiver_id: input.view.waiver_id,
                template: input.view.template,
                site,
            };
            capture_one(table, &source, owner_path, &key)
        })();
        record(&mut plans, node, key, result);
    }
    plans
}

fn record(
    plans: &mut OutboundReturnPlans,
    node: Node,
    key: MechanicalObligationKey,
    result: Result<(OutboundReturnRequirement, OutboundReturnReceiptPlan), String>,
) {
    match result {
        Ok((required, blueprint)) if !plans.failures.contains_key(&node) => {
            plans.requirements.insert(node, required);
            plans.blueprints.insert(node, blueprint);
        }
        Ok(_) => {}
        Err(reason) => {
            plans.requirements.remove(&node);
            plans.blueprints.remove(&node);
            plans.failures.insert(node, Failure { node, key, reason });
        }
    }
}

fn capture_one(
    table: &DecisionTable,
    input: &ReceiptSource<'_>,
    owner_path: &impl Fn(LocalDefId) -> Option<String>,
    key: &MechanicalObligationKey,
) -> Result<(OutboundReturnRequirement, OutboundReturnReceiptPlan), String> {
    let node = input.node;
    let subject = table
        .entries
        .iter()
        .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
        .map(|(subject, _)| subject)
        .ok_or("outbound-return:receiver-subject-missing")?;
    if subject.local != input.destination
        || subject.kind != SubjectKind::Local
        || input.initializer_hir.owner.def_id != node.0
        || input.initializer_span.is_dummy()
        || table.return_interfaces.functions.get(&input.callee) != Some(input.interface)
    {
        return Err("outbound-return:receiver-native-identity-mismatch".into());
    }
    if input.tier != BridgeRetentionTier::T2
        || input.waiver_id != RAW_BOUNDARY_T2_WAIVER_ID
        || !matches!(input.retention, RetentionVerdict::Unknown { .. })
    {
        return Err("outbound-return:receiver-retention-evidence-mismatch".into());
    }
    let lifetime = table
        .lifetime_plan
        .function(input.callee)
        .ok_or("outbound-return:native-lifetime-plan-missing")?;
    if lifetime.digest() != input.interface.lifetime_plan_digest
        || lifetime.lifetime_for(FnSignatureSlot::RETURN) != Some(input.interface.lifetime.as_str())
    {
        return Err("outbound-return:native-lifetime-plan-mismatch".into());
    }
    let sources = lifetime.return_sources();
    if sources.is_empty() {
        return Err("outbound-return:native-return-origins-empty".into());
    }
    let mut origins = Vec::new();
    for source in sources {
        let FnSignatureRoot::Arg(index) = source.root else {
            return Err("outbound-return:native-origin-is-not-parameter".into());
        };
        if source.depth != 0 || source.deref_depth != 0 || index == 0 {
            return Err("outbound-return:native-origin-depth-unrepresented".into());
        }
        let parameters = table.entries.iter().filter(|(subject, _)| subject.fn_did == input.callee
            && matches!(subject.kind, SubjectKind::Param { hir_index }
                if hir_index.checked_add(1).and_then(|index| u32::try_from(index).ok()) == Some(index)))
            .collect::<Vec<_>>();
        let [(parameter, _)] = parameters.as_slice() else {
            return Err("outbound-return:native-origin-parameter-unmapped".into());
        };
        if parameter.local.as_u32() == 0 {
            return Err("outbound-return:native-origin-is-return-slot".into());
        }
        origins.push(MechanicalSubjectKey::Local {
            owner: parameter.fn_did,
            mir_local: parameter.local.as_u32(),
            slot_depth: 0,
        });
    }
    origins.sort_by_key(MechanicalSubjectKey::receipt_key);
    origins.dedup();
    let owner_path = owner_path(input.callee)
        .filter(|path| !path.is_empty())
        .ok_or("outbound-return:owner-path-missing")?;
    let site = &input.site;
    if site.key.owner_class != key.owner_class
        || site.key.caller != node.0
        || site.key.callee != BridgeCalleeId::Local(input.callee)
        || site.expected_form != "raw"
        || site.found_form != input.interface.form.key()
        || site.retention != input.tier
        || site.waiver_id.as_deref() != Some(input.waiver_id)
        || site.extent != BridgeExtentKind::None
    {
        return Err("outbound-return:common-bridge-evidence-mismatch".into());
    }
    // Capture expected metadata directly from the input/native/bridge objects
    // before constructing the independently mutable output-row blueprint.
    let required = OutboundReturnRequirement {
        key: key.clone(),
        associated_bridge: site.key.clone(),
        adapter: input.template.key().into(),
        retention_evidence: Some((*input.retention).clone()),
        native_lifetime: None,
        lifetime_origin: origins,
        terminal_interface: input.interface.form.key().into(),
    };
    let retention = MechanicalRetention::T2 {
        waiver_id: input.waiver_id.into(),
    };
    let negative_write = NegativeWriteEvidence::NotApplicable;
    let event = MechanicalObligationEvent {
        key: key.clone(),
        owner_path,
        prior_reason: "return-not-adapted".into(),
        expected_form: site.expected_form.clone(),
        found_form: site.found_form.clone(),
        argument_kind: site.argument_kind.clone(),
        source_shape: "return-call-result".into(),
        required_arms: site.key.arm.clone(),
        mechanism: MechanicalMechanism::ReturnAdapter,
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
        endpoint: CanonicalCallee::Local(input.callee.to_def_id()),
        position: site.key.position.clone(),
        source_form: site.found_form.clone(),
        target_form: site.expected_form.clone(),
        adapter: required.adapter.clone(),
        negative_write,
        retention,
        retention_evidence: required.retention_evidence.clone(),
        native_lifetime: None,
        lifetime_origin: required.lifetime_origin.clone(),
        pair_role: "not-applicable".into(),
        effect_carrier: None,
        terminal_interface: required.terminal_interface.clone(),
    };
    Ok((required, blueprint))
}

impl OutboundReturnPlans {
    pub(crate) fn materialize(
        &self,
        inputs: &ReceiverInputMap,
        raw_inputs: &RawReceiverPlans,
        normalized_classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Result<Materialized, Vec<Failure>> {
        let mut selected = inputs
            .plans
            .iter()
            .filter(|(_, input)| in_scope(input) && input.active(normalized_classes, atoms))
            .map(|(&node, input)| (node, admitted_key(input)))
            .chain(
                raw_inputs
                    .plans
                    .iter()
                    .filter(|(_, input)| input.active(normalized_classes))
                    .map(|(&node, input)| (node, raw_key(input))),
            )
            .collect::<Vec<_>>();
        selected
            .sort_by_key(|(node, _)| (node.0.local_def_index.as_u32(), node.1.local_id.as_u32()));
        let (mut required, mut common, mut rows, mut failures) =
            (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        let mut seen = BTreeSet::new();
        for (node, key) in selected {
            let identity = (node.0.local_def_index.as_u32(), node.1.local_id.as_u32());
            if !seen.insert(identity) {
                failures.push(Failure {
                    node,
                    key,
                    reason: "outbound-return:receiver-populations-overlap".into(),
                });
                continue;
            }
            if let Some(failure) = self.failures.get(&node) {
                failures.push(failure.clone());
                continue;
            }
            let Some(expectation) = self.requirements.get(&node) else {
                failures.push(Failure {
                    node,
                    key,
                    reason: "outbound-return:required-metadata-missing".into(),
                });
                continue;
            };
            required.push(expectation.clone());
            let Some(blueprint) = self.blueprints.get(&node) else {
                failures.push(Failure {
                    node,
                    key,
                    reason: "outbound-return:blueprint-missing".into(),
                });
                continue;
            };
            if expectation.key != key || blueprint.obligation.planned.key != key {
                failures.push(Failure {
                    node,
                    key,
                    reason: "outbound-return:selection-key-drift".into(),
                });
                continue;
            }
            // Active uses the same normalized selection as emission: the
            // callee owning this bridge survives even if the caller retired.
            let (events, specialized) = blueprint.materialize(true, false);
            common.extend(events);
            rows.extend(specialized);
        }
        if failures.is_empty() {
            Ok((required, common, rows))
        } else {
            Err(failures)
        }
    }
}
