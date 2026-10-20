//! Receipt custody for exact call arguments whose callee parameter returns
//! to its input form. All span placement happens while the compiler is live;
//! subsequent selection uses only the sealed inputs and effective reverts.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::FxHashSet;
use rustc_span::Span;

use super::super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptEvent, BridgeReceiptStage, BridgeReceiptState, BridgeSiteKey,
        BridgeSitePlan, SignatureClassId,
    },
    decision::{
        callee_parameter_input::{InputPlans, Key},
        seam::SeamPlan,
    },
    mechanical_receipt::UnsafeContextReceiptEvent,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FailureKind {
    MappingInvariant,
    AlternativeUnavailable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MappingFailure {
    pub(crate) kind: FailureKind,
    pub(crate) key: Key,
    pub(crate) caller: SignatureClassId,
    pub(crate) target: SignatureClassId,
    pub(crate) reason: String,
}

fn failure(key: Key, caller: SignatureClassId, reason: impl Into<String>) -> MappingFailure {
    MappingFailure {
        kind: FailureKind::MappingInvariant,
        key,
        caller,
        target: key.0,
        reason: reason.into(),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LocatedInput {
    caller: SignatureClassId,
    file: String,
    lo: u32,
    hi: u32,
    old_keys: Vec<BridgeSiteKey>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct InputReceiptMap {
    sites: BTreeMap<Key, LocatedInput>,
    failures: Vec<MappingFailure>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct SelectedReceipts {
    /// Override only terminal events with these exact old keys. Their plan
    /// events remain, paired with a typed dropped terminal event.
    pub(crate) withdrawn: FxHashSet<BridgeSiteKey>,
    pub(crate) bridge_events: Vec<BridgeReceiptEvent>,
    pub(crate) unsafe_context_events: Vec<UnsafeContextReceiptEvent>,
    pub(crate) failures: Vec<MappingFailure>,
}

impl InputReceiptMap {
    pub(crate) fn failures(&self) -> &[MappingFailure] {
        &self.failures
    }

    pub(crate) fn capture(
        inputs: &InputPlans,
        seams: &SeamPlan,
        span_to_loc: &impl Fn(Span) -> Result<(super::FileKey, usize, usize), &'static str>,
    ) -> Self {
        let mut map = Self::default();
        for (&key, input) in inputs {
            let caller = SignatureClassId::of(input.caller);
            let exact_span = |span: Span| span.lo().0 == key.1 && span.hi().0 == key.2;
            // Ordinary C call adapters may carry the glue arm when both
            // endpoints are borrowed. A return/glue position is not argN.
            let edits = seams
                .edits
                .iter()
                .filter(|edit| {
                    edit.owner_class == key.0
                        && exact_span(edit.span)
                        && edit.bridge.caller == input.caller
                        && edit.bridge.callee == BridgeCalleeId::Local(key.0.local_def_id())
                        && matches!(edit.bridge.arm.as_str(), "c" | "glue")
                        && edit.param_index != usize::MAX
                        && edit.bridge.position == format!("arg{}", edit.param_index)
                })
                .collect::<Vec<_>>();
            let reverted_identities = seams
                .revert_found_form_edits
                .iter()
                .filter(|edit| {
                    edit.owner_class == key.0
                        && exact_span(edit.span)
                        && edit.source_node.0 == input.caller
                })
                .collect::<Vec<_>>();
            // RFF does not own a separate common bridge. Its old receipt is
            // this typed interface identity; identity calls without an RFF
            // source twin use the same exact receipt kind.
            let identities = seams
                .zero_bridges
                .iter()
                .filter(|site| {
                    site.owner_class == key.0
                        && site.caller == input.caller
                        && site.span.is_some_and(exact_span)
                        && matches!(site.arm, "c" | "glue")
                        && site.bridge_kind == "interface-call-zero-syntax"
                })
                .collect::<Vec<_>>();
            if edits.len() + identities.len() != 1 || reverted_identities.len() > 1 {
                map.failures.push(failure(key, caller, format!(
                    "callee-parameter-receipt-mapping:exact-call-carrier-count:edits={}:identities={}:rff={}",
                    edits.len(), identities.len(), reverted_identities.len())));
                continue;
            }
            if !reverted_identities.is_empty() && identities.is_empty() {
                map.failures.push(failure(
                    key,
                    caller,
                    "callee-parameter-receipt-mapping:rff-identity-missing",
                ));
                continue;
            }
            let span = edits
                .first()
                .map(|edit| edit.span)
                .or_else(|| identities.first().and_then(|site| site.span))
                .expect("one exact typed argument carrier");
            let (file, lo, hi) = match span_to_loc(span) {
                Ok((file, lo, hi)) => match (u32::try_from(lo), u32::try_from(hi)) {
                    (Ok(lo), Ok(hi)) => (super::file_key_label(&file), lo, hi),
                    _ => {
                        map.failures.push(failure(
                            key,
                            caller,
                            "callee-parameter-receipt-mapping:file-offset-overflow",
                        ));
                        continue;
                    }
                },
                Err(reason) => {
                    map.failures.push(failure(
                        key,
                        caller,
                        format!("callee-parameter-receipt-mapping:span-unlocated:{reason}"),
                    ));
                    continue;
                }
            };
            let old_keys = if let Some(edit) = edits.first() {
                vec![
                    edit.bridge
                        .materialize(edit.owner_class, file.clone(), lo, hi),
                ]
            } else {
                let site = identities[0];
                vec![BridgeSiteKey {
                    owner_class: site.owner_class,
                    caller: site.caller,
                    callee: BridgeCalleeId::Local(site.owner_class.local_def_id()),
                    arm: site.arm.to_owned(),
                    position: site.position.clone(),
                    file: file.clone(),
                    lo,
                    hi,
                    bridge_kind: site.bridge_kind.to_owned(),
                }]
            };
            map.sites.insert(
                key,
                LocatedInput {
                    caller,
                    file,
                    lo,
                    hi,
                    old_keys,
                },
            );
        }
        map
    }

    /// `effective_classes` is the same union of held/reverted classes and
    /// atom-driven closure used for the actual AST selection. Read current
    /// terminal inputs here rather than keeping a stale clone of alternatives.
    pub(crate) fn selected(
        &self,
        inputs: &InputPlans,
        effective_classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> SelectedReceipts {
        let mut out = SelectedReceipts::default();
        for (&key, input) in inputs {
            let caller = SignatureClassId::of(input.caller);
            let (selected, owner) = match input.select(effective_classes, atoms) {
                Some(selected) => (selected, caller),
                None if input.source_is_input(effective_classes, atoms) => {
                    let Some(alternative) = input.kept_target_input_source.as_ref() else {
                        continue;
                    };
                    // The existing AST source-input adapter is required by
                    // the surviving callee interface, including when the
                    // caller's own class has reverted to its input source.
                    (Ok(alternative), key.0)
                }
                None => continue,
            };
            let Some(site) = self.sites.get(&key) else {
                out.failures.push(failure(
                    key,
                    caller,
                    "callee-parameter-receipt-mapping:selected-site-unmapped",
                ));
                continue;
            };
            out.withdrawn.extend(site.old_keys.iter().cloned());
            if caller != site.caller {
                out.failures.push(failure(
                    key,
                    caller,
                    "callee-parameter-receipt-mapping:caller-changed",
                ));
                continue;
            }
            if effective_classes.contains(&owner) {
                continue;
            }
            let alternative = match selected {
                Ok(alternative) => alternative,
                Err(reason) => {
                    out.failures.push(MappingFailure {
                        kind: FailureKind::AlternativeUnavailable,
                        key,
                        caller,
                        target: key.0,
                        reason: format!("callee-parameter-input-unavailable:{reason}"),
                    });
                    continue;
                }
            };
            // A zero-syntax original expression may have no bridge at all.
            // Withdrawal still occurs; no invented alternative receipt does.
            let Some(bridge) = alternative.bridge.as_ref() else { continue };
            if SignatureClassId::of(bridge.caller) != caller {
                out.failures.push(failure(
                    key,
                    caller,
                    "callee-parameter-receipt-mapping:alternative-caller-mismatch",
                ));
                continue;
            }
            let materialized = bridge.materialize(owner, site.file.clone(), site.lo, site.hi);
            append_events(&mut out, bridge, materialized);
        }
        out
    }
}

fn append_events(out: &mut SelectedReceipts, bridge: &BridgeSitePlan, site: BridgeSiteKey) {
    for (stage, state) in [
        (BridgeReceiptStage::Plan, BridgeReceiptState::Planned),
        (BridgeReceiptStage::Terminal, BridgeReceiptState::Applied),
    ] {
        out.bridge_events.push(BridgeReceiptEvent {
            site: site.clone(),
            expected_form: bridge.expected_form.clone(),
            found_form: bridge.found_form.clone(),
            argument_kind: bridge.argument_kind.clone(),
            stage,
            state,
            drop_reason: None,
            extent: bridge.extent.clone(),
            retention: bridge.retention,
            waiver_id: bridge.waiver_id.clone(),
        });
        if let Some(presentation) = bridge.unsafe_context {
            out.unsafe_context_events.push(UnsafeContextReceiptEvent {
                site: site.clone(),
                enclosing: bridge.caller,
                presentation,
                terminal_class_disposition: "ready".to_owned(),
                stage,
                state,
                drop_reason: None,
            });
        }
    }
}
