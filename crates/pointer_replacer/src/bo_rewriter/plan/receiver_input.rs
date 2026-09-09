//! Exact common-receipt custody for retired borrowed-return receivers.
//! Original declaration keys come from authoritative plan data, never from
//! reconstructed receipt strings or overlapping source intervals.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::Span;

pub(crate) use super::callee_parameter_input::FailureKind;
use super::{
    super::{
        bridge_receipt::{
            BridgeCalleeId, BridgeExtentKind, BridgeReceiptEvent, BridgeReceiptStage,
            BridgeReceiptState, BridgeSiteKey, BridgeSitePlan, SignatureClassId,
        },
        decision::{
            DecisionTable,
            receiver_input::{ReceiverInputMap, ReceiverInputPlan},
            return_receiver::{Node, ReceiverDeclaration},
        },
        mechanical_receipt::UnsafeContextReceiptEvent,
    },
    ClassSite, ClassSiteState, Edit, FileKey,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MappingFailure {
    pub(crate) kind: FailureKind,
    pub(crate) node: Node,
    pub(crate) caller: SignatureClassId,
    pub(crate) callee: SignatureClassId,
    pub(crate) reason: String,
}

fn failure(node: Node, callee: SignatureClassId, reason: impl Into<String>) -> MappingFailure {
    MappingFailure {
        kind: FailureKind::MappingInvariant,
        node,
        caller: SignatureClassId::of(node.0),
        callee,
        reason: reason.into(),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LocatedReceiver {
    callee: SignatureClassId,
    initializer: (String, u32, u32),
    old_keys: Vec<BridgeSiteKey>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ReceiverReceiptMap {
    sites: FxHashMap<Node, LocatedReceiver>,
    failures: Vec<MappingFailure>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct SelectedReceipts {
    pub(crate) withdrawn: FxHashSet<BridgeSiteKey>,
    pub(crate) bridge_events: Vec<BridgeReceiptEvent>,
    pub(crate) unsafe_context_events: Vec<UnsafeContextReceiptEvent>,
    pub(crate) failures: Vec<MappingFailure>,
}

fn located(
    span: Span,
    span_to_loc: &impl Fn(Span) -> Result<(FileKey, usize, usize), &'static str>,
) -> Result<(String, u32, u32), &'static str> {
    let (file, lo, hi) = span_to_loc(span)?;
    Ok((
        super::file_key_label(&file),
        u32::try_from(lo).map_err(|_| "receiver-input-offset-overflow")?,
        u32::try_from(hi).map_err(|_| "receiver-input-offset-overflow")?,
    ))
}

impl ReceiverReceiptMap {
    pub(crate) fn selected_raw_site(
        &self,
        node: Node,
        input: &ReceiverInputPlan,
    ) -> Result<ClassSite, MappingFailure> {
        let site = self.sites.get(&node).ok_or_else(|| {
            failure(
                node,
                input.selection.callee,
                "receiver-input-mapping:selected-site-unmapped",
            )
        })?;
        if input.selection.node != node || input.selection.callee != site.callee {
            return Err(failure(
                node,
                input.selection.callee,
                "receiver-input-mapping:selection-drift",
            ));
        }
        Ok(alternative_site(input, site))
    }

    pub(crate) fn capture(
        inputs: &ReceiverInputMap,
        table: &DecisionTable,
        preclass_sites: &[ClassSite],
        by_file: &BTreeMap<FileKey, Vec<Edit>>,
        span_to_loc: &impl Fn(Span) -> Result<(FileKey, usize, usize), &'static str>,
    ) -> Self {
        let mut map = Self::default();
        let mut receivers = inputs
            .plans
            .iter()
            .map(|(&node, input)| (node, &input.receiver))
            .chain(
                inputs
                    .unavailable
                    .iter()
                    .map(|(&node, input)| (node, &input.receiver)),
            )
            .collect::<Vec<_>>();
        receivers
            .sort_by_key(|(node, _)| (node.0.local_def_index.as_u32(), node.1.local_id.as_u32()));
        let mut seen = FxHashSet::default();
        for (node, receiver) in receivers {
            let callee = SignatureClassId::of(receiver.callee);
            if !seen.insert(node) {
                map.failures.push(failure(
                    node,
                    callee,
                    "receiver-input-mapping:duplicate-outcome",
                ));
                map.sites.remove(&node);
                continue;
            }
            if table.return_receivers.plans.get(&node) != Some(receiver) || receiver.node != node {
                map.failures.push(failure(
                    node,
                    callee,
                    "receiver-input-mapping:receiver-plan-mismatch",
                ));
                continue;
            }
            let Some((subject, _)) = table
                .entries
                .iter()
                .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
            else {
                map.failures.push(failure(
                    node,
                    callee,
                    "receiver-input-mapping:subject-missing",
                ));
                continue;
            };
            let (binding, initializer) = match (
                located(subject.binding_span, span_to_loc),
                located(receiver.initializer_span, span_to_loc),
            ) {
                (Ok(binding), Ok(initializer)) => (binding, initializer),
                (Err(reason), _) | (_, Err(reason)) => {
                    map.failures.push(failure(
                        node,
                        callee,
                        format!("receiver-input-mapping:span-unlocated:{reason}"),
                    ));
                    continue;
                }
            };
            let (declaration, declaration_owner, declaration_callee, declaration_kind) =
                match receiver.declaration {
                    ReceiverDeclaration::Inferred => (
                        binding.clone(),
                        callee,
                        receiver.callee,
                        "declaration-explicit-type",
                    ),
                    ReceiverDeclaration::Existing => {
                        let Some(span) = subject.ty_span else {
                            map.failures.push(failure(
                                node,
                                callee,
                                "receiver-input-mapping:existing-declaration-type-span-missing",
                            ));
                            continue;
                        };
                        let declaration = match located(span, span_to_loc) {
                            Ok(declaration) => declaration,
                            Err(reason) => {
                                map.failures.push(failure(
                                    node,
                                    callee,
                                    format!("receiver-input-mapping:type-span-unlocated:{reason}"),
                                ));
                                continue;
                            }
                        };
                        (
                            declaration,
                            SignatureClassId::of(node.0),
                            node.0,
                            "subject-declaration",
                        )
                    }
                };
            let declaration_ref = &declaration;
            let declarations = by_file
                .iter()
                .flat_map(|(file, edits)| {
                    edits.iter().filter_map(move |edit| {
                        let bridge = edit.bridge.as_ref()?;
                        (edit.owner_class == Some(declaration_owner)
                            && bridge.caller == node.0
                            && bridge.callee == BridgeCalleeId::Local(declaration_callee)
                            && edit.edit_kind == declaration_kind
                            && bridge.bridge_kind == declaration_kind
                            && super::file_key_label(file) == declaration_ref.0
                            && edit.lo == declaration_ref.1 as usize
                            && edit.hi == declaration_ref.2 as usize)
                            .then(|| {
                                bridge.materialize(
                                    declaration_owner,
                                    declaration_ref.0.clone(),
                                    declaration_ref.1,
                                    declaration_ref.2,
                                )
                            })
                    })
                })
                .collect::<Vec<_>>();
            let receives = preclass_sites
                .iter()
                .filter(|site| {
                    site.key.owner_class == callee
                        && site.key.caller == node.0
                        && site.key.callee == BridgeCalleeId::Local(receiver.callee)
                        && site.key.bridge_kind == "return-caller-receive-ref"
                        && site.key.file == binding.0
                        && site.key.lo == binding.1
                        && site.key.hi == binding.2
                })
                .map(|site| site.key.clone())
                .collect::<Vec<_>>();
            if declarations.len() != 1 || receives.len() != 1 {
                map.failures.push(failure(node, callee, format!(
                    "receiver-input-mapping:exact-old-carrier-count:declarations={}:receives={}",
                    declarations.len(), receives.len())));
                continue;
            }
            let coercions = preclass_sites
                .iter()
                .filter(|site| {
                    site.key.owner_class == callee
                        && site.key.caller == node.0
                        && site.key.callee == BridgeCalleeId::Local(receiver.callee)
                        && site.key.bridge_kind == "return-shared-option"
                        && site.key.file == initializer.0
                        && site.key.lo == initializer.1
                        && site.key.hi == initializer.2
                })
                .map(|site| site.key.clone())
                .collect::<Vec<_>>();
            let needs_coercion = receiver.coercion
                == super::super::decision::return_receiver::ReceiverCoercion::SharedOption;
            if coercions.len() != usize::from(needs_coercion) {
                map.failures.push(failure(
                    node,
                    callee,
                    "receiver-input-mapping:coercion-count",
                ));
                continue;
            }
            map.sites.insert(
                node,
                LocatedReceiver {
                    callee,
                    initializer,
                    old_keys: declarations
                        .into_iter()
                        .chain(receives)
                        .chain(coercions)
                        .collect(),
                },
            );
        }
        map
    }

    pub(crate) fn selected(
        &self,
        inputs: &ReceiverInputMap,
        normalized_classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> SelectedReceipts {
        let mut out = SelectedReceipts::default();
        let mut nodes = inputs
            .plans
            .keys()
            .chain(inputs.unavailable.keys())
            .copied()
            .collect::<Vec<_>>();
        nodes.sort_by_key(|node| (node.0.local_def_index.as_u32(), node.1.local_id.as_u32()));
        nodes.dedup();
        for node in nodes {
            let selection = inputs
                .plans
                .get(&node)
                .map(|input| &input.selection)
                .or_else(|| inputs.unavailable.get(&node).map(|input| &input.selection))
                .unwrap();
            if !selection.active(normalized_classes, atoms) {
                continue;
            }
            let Some(site) = self.sites.get(&node) else {
                out.failures.push(
                    self.failures
                        .iter()
                        .find(|failure| failure.node == node)
                        .cloned()
                        .unwrap_or_else(|| {
                            failure(
                                node,
                                selection.callee,
                                "receiver-input-mapping:selected-site-unmapped",
                            )
                        }),
                );
                continue;
            };
            if selection.node != node || selection.callee != site.callee {
                out.failures.push(failure(
                    node,
                    selection.callee,
                    "receiver-input-mapping:selection-drift",
                ));
                continue;
            }
            out.withdrawn.extend(site.old_keys.iter().cloned());
            if let Some(unavailable) = inputs.unavailable.get(&node) {
                out.failures.push(MappingFailure {
                    kind: FailureKind::AlternativeUnavailable,
                    node,
                    caller: SignatureClassId::of(node.0),
                    callee: site.callee,
                    reason: format!("receiver-input-unavailable:{:?}", unavailable.reason),
                });
                continue;
            }
            let input = &inputs.plans[&node];
            let replacement = alternative_site(input, site);
            for (stage, state) in [
                (BridgeReceiptStage::Plan, BridgeReceiptState::Planned),
                (BridgeReceiptStage::Terminal, BridgeReceiptState::Applied),
            ] {
                out.bridge_events.push(BridgeReceiptEvent {
                    site: replacement.key.clone(),
                    expected_form: replacement.expected_form.clone(),
                    found_form: replacement.found_form.clone(),
                    argument_kind: replacement.argument_kind.clone(),
                    stage,
                    state,
                    drop_reason: None,
                    extent: replacement.extent.clone(),
                    retention: replacement.retention,
                    waiver_id: replacement.waiver_id.clone(),
                });
                if let Some(presentation) = replacement.unsafe_context {
                    out.unsafe_context_events.push(UnsafeContextReceiptEvent {
                        site: replacement.key.clone(),
                        enclosing: node.0,
                        presentation,
                        terminal_class_disposition: "ready".into(),
                        stage,
                        state,
                        drop_reason: None,
                    });
                }
            }
        }
        out
    }
}

fn alternative_site(input: &ReceiverInputPlan, located: &LocatedReceiver) -> ClassSite {
    let receiver = &input.receiver;
    let bridge = BridgeSitePlan {
        caller: receiver.node.0,
        callee: BridgeCalleeId::Local(receiver.callee),
        arm: "c".into(),
        position: format!(
            "receiver-input:{}:{}:lifetime_plan={}",
            receiver.node.0.local_def_index.as_u32(),
            receiver.node.1.local_id.as_u32(),
            receiver.candidate_interface.lifetime_plan_digest
        ),
        bridge_kind: "return-caller-receive-raw".into(),
        expected_form: "raw".into(),
        found_form: receiver.candidate_interface.form.key().into(),
        argument_kind: "return-call-result".into(),
        extent: BridgeExtentKind::None,
        retention: input.tier,
        waiver_id: Some(input.waiver_id.into()),
        // The raw view adds no unsafe operation; the initializer call retains
        // its separately owned safety presentation.
        unsafe_context: None,
    };
    ClassSite {
        atom_ids: Vec::new(),
        key: bridge.materialize(
            located.callee,
            located.initializer.0.clone(),
            located.initializer.1,
            located.initializer.2,
        ),
        edit_key: "-".into(),
        state: ClassSiteState::EditReady,
        expected_form: bridge.expected_form,
        found_form: bridge.found_form,
        argument_kind: bridge.argument_kind,
        extent: bridge.extent,
        retention: bridge.retention,
        waiver_id: bridge.waiver_id,
        unsafe_context: bridge.unsafe_context,
    }
}
