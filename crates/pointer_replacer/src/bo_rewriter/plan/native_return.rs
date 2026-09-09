//! J27 native return-expression custody, captured before receipt materialization.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_span::Span;

use super::super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, BridgeSitePlan, SignatureClassId,
    },
    decision::{
        DecisionTable, SubjectKind,
        emitability::ReturnSiteFact,
        lifetime::{FnSignatureRoot, FnSignatureSlot},
        seam::{Form, SeamEdit, TerminalCallPlans},
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
pub(crate) enum Failure {
    Site {
        node: (LocalDefId, HirId),
        key: MechanicalObligationKey,
        reason: String,
    },
    /// An unmatched terminal seam has no authoritative expression HIR. Keep
    /// its actual typed input instead of manufacturing an obligation identity.
    TerminalSeam {
        owner_class: SignatureClassId,
        bridge: BridgeSitePlan,
        span: Span,
        reason: String,
    },
}

impl Failure {
    fn reason(&self) -> &str {
        match self {
            Self::Site { reason, .. } | Self::TerminalSeam { reason, .. } => reason,
        }
    }
}

/// The selected native input remains independent of both J27 output families.
#[derive(Clone, Debug, PartialEq, Eq)]
struct NativeSite {
    fact: ReturnSiteFact,
    key: MechanicalObligationKey,
    seam: Option<SeamEdit>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct NativeReturnPlans {
    sites: FxHashMap<CanonicalSiteKey, NativeSite>,
    requirements: FxHashMap<CanonicalSiteKey, OutboundReturnRequirement>,
    blueprints: FxHashMap<CanonicalSiteKey, OutboundReturnReceiptPlan>,
    failures: FxHashMap<CanonicalSiteKey, Failure>,
}

pub(crate) type Materialized = (
    Vec<OutboundReturnRequirement>,
    Vec<MechanicalObligationEvent>,
    Vec<OutboundReturnBridgeReceiptRow>,
);

fn site_key(site: &ReturnSiteFact) -> CanonicalSiteKey {
    CanonicalSiteKey {
        owner: site.owner,
        location: CanonicalLocation::Hir {
            owner: site.hir_id.owner.def_id,
            item_local_id: site.hir_id.local_id.as_u32(),
        },
        callee: Some(CanonicalCallee::Local(site.owner.to_def_id())),
        argument_index: None,
        slot_depth: 0,
    }
}

fn expression_subject(site: &ReturnSiteFact) -> MechanicalSubjectKey {
    MechanicalSubjectKey::Generated {
        owner: site.owner,
        key: format!("return-expression:{}", site.hir_id.local_id.as_u32()),
        slot_depth: 0,
    }
}

fn matching_seam(site: &ReturnSiteFact, seam: &SeamEdit) -> bool {
    seam.owner_class == SignatureClassId::of(site.owner)
        && seam.bridge.caller == site.owner
        && seam.bridge.callee == BridgeCalleeId::Local(site.owner)
        && seam.param_index == usize::MAX
        && seam.span == site.span
        && matches!(
            seam.bridge.bridge_kind.as_str(),
            "return-raw-to-ref" | "return-null-to-option"
        )
}

fn failure(site: &NativeSite, reason: impl Into<String>) -> Failure {
    Failure::Site {
        node: (site.fact.owner, site.fact.root.unwrap_or(site.fact.hir_id)),
        key: site.key.clone(),
        reason: reason.into(),
    }
}

fn terminal_failure(seam: &SeamEdit, reason: &str) -> Failure {
    Failure::TerminalSeam {
        owner_class: seam.owner_class,
        bridge: seam.bridge.clone(),
        span: seam.span,
        reason: reason.into(),
    }
}

pub(crate) fn capture(
    table: &DecisionTable,
    spans: &impl Fn(Span) -> Result<(super::FileKey, usize, usize), &'static str>,
    owner_path: &impl Fn(LocalDefId) -> Option<String>,
) -> NativeReturnPlans {
    let mut plans = NativeReturnPlans::default();
    for site in &table.seams.native_return_sites {
        // Raw signatures have no native borrowed-return obligation.
        if table
            .lifetime_plan
            .function(site.owner)
            .and_then(|plan| plan.lifetime_for(FnSignatureSlot::RETURN))
            .is_none()
        {
            continue;
        }
        let canonical = site_key(site);
        let mut input = NativeSite {
            fact: site.clone(),
            key: MechanicalObligationKey {
                owner_class: SignatureClassId::of(site.owner),
                subject: expression_subject(site),
                site: canonical.clone(),
                family: MechanicalFamily::ReturnNotAdapted,
            },
            seam: None,
        };
        let result = capture_one(table, &mut input, spans, owner_path);
        if plans.sites.contains_key(&canonical) {
            plans.requirements.remove(&canonical);
            plans.blueprints.remove(&canonical);
            plans.failures.insert(
                canonical,
                failure(&input, "native-return:duplicate-expression-site"),
            );
            continue;
        }
        match result {
            Ok((requirement, blueprint)) => {
                plans.requirements.insert(canonical.clone(), requirement);
                plans.blueprints.insert(canonical.clone(), blueprint);
            }
            Err(reason) => {
                plans
                    .failures
                    .insert(canonical.clone(), failure(&input, reason));
            }
        }
        plans.sites.insert(canonical, input);
    }
    plans
}

fn capture_one(
    table: &DecisionTable,
    input: &mut NativeSite,
    spans: &impl Fn(Span) -> Result<(super::FileKey, usize, usize), &'static str>,
    owner_path: &impl Fn(LocalDefId) -> Option<String>,
) -> Result<(OutboundReturnRequirement, OutboundReturnReceiptPlan), String> {
    let site = &input.fact;
    if site.hir_id.owner.def_id != site.owner || site.span.is_dummy() {
        return Err("native-return:expression-identity-mismatch".into());
    }
    let matches = table
        .seams
        .edits
        .iter()
        .filter(|seam| matching_seam(site, seam))
        .collect::<Vec<_>>();
    let [seam] = matches.as_slice() else {
        return Err("native-return:common-seam-not-unique".into());
    };
    input.seam = Some((**seam).clone());
    let interface = table
        .return_interfaces
        .functions
        .get(&site.owner)
        .ok_or("native-return:interface-missing")?;
    let lifetime = table
        .lifetime_plan
        .function(site.owner)
        .ok_or("native-return:lifetime-plan-missing")?;
    let digest = lifetime.digest();
    if digest != interface.lifetime_plan_digest
        || lifetime.lifetime_for(FnSignatureSlot::RETURN) != Some(interface.lifetime.as_str())
        || seam.lifetime_plan_digest.as_deref() != Some(digest.as_str())
        || seam.expected != interface.form
        || seam.bridge.expected_form != seam.expected.key()
        || seam.bridge.found_form != seam.found.key()
        || interface.form == Form::Raw
        || seam.call_span != site.span
        || seam.bridge.extent != BridgeExtentKind::None
        || seam.bridge.waiver_id.is_some()
    {
        return Err("native-return:native-common-evidence-mismatch".into());
    }
    let null = site.source_shape == "null-lit";
    let mut origins = Vec::new();
    let retention = if null {
        if site.root.is_some()
            || seam.bridge.bridge_kind != "return-null-to-option"
            || seam.bridge.retention != BridgeRetentionTier::None
            || seam.found != Form::Raw
            || !matches!(interface.form, Form::Opt { .. })
        {
            return Err("native-return:null-evidence-mismatch".into());
        }
        MechanicalRetention::None
    } else {
        if seam.bridge.bridge_kind != "return-raw-to-ref"
            || seam.bridge.retention != BridgeRetentionTier::T1
        {
            return Err("native-return:return-permit-bridge-mismatch".into());
        }
        let root = site.root.ok_or("native-return:source-root-missing")?;
        let roots = table
            .entries
            .iter()
            .filter(|(subject, _)| {
                subject.fn_did == site.owner
                    && subject.hir_id == root
                    && matches!(subject.kind, SubjectKind::Param { .. })
            })
            .collect::<Vec<_>>();
        let [(parameter, _)] = roots.as_slice() else {
            return Err("native-return:source-parameter-unmapped".into());
        };
        input.key.subject = MechanicalSubjectKey::Local {
            owner: site.owner,
            mir_local: parameter.local.as_u32(),
            slot_depth: 0,
        };
        for source in lifetime.return_sources() {
            let FnSignatureRoot::Arg(index) = source.root else {
                return Err("native-return:origin-is-not-parameter".into());
            };
            if source.depth != 0 || source.deref_depth != 0 || index == 0 {
                return Err("native-return:origin-depth-unrepresented".into());
            }
            let parameters = table.entries.iter().filter(|(subject, _)|
                subject.fn_did == site.owner && matches!(subject.kind,
                    SubjectKind::Param { hir_index }
                        if hir_index.checked_add(1).and_then(|i| u32::try_from(i).ok()) == Some(index)))
                .collect::<Vec<_>>();
            let [(parameter, _)] = parameters.as_slice() else {
                return Err("native-return:origin-parameter-unmapped".into());
            };
            if parameter.local.as_u32() == 0 {
                return Err("native-return:origin-is-return-slot".into());
            }
            origins.push(MechanicalSubjectKey::Local {
                owner: site.owner,
                mir_local: parameter.local.as_u32(),
                slot_depth: 0,
            });
        }
        origins.sort_by_key(MechanicalSubjectKey::receipt_key);
        origins.dedup();
        if origins.is_empty() || !origins.contains(&input.key.subject) {
            return Err("native-return:source-native-origin-missing".into());
        }
        // T1 is the existing native return permit's label, not a NoRetain
        // claim: returning a parameter is itself observable retention.
        MechanicalRetention::T1
    };
    let (file, lo, hi) = spans(site.span)?;
    let lo = u32::try_from(lo).map_err(|_| "native-return:span-offset-overflow")?;
    let hi = u32::try_from(hi).map_err(|_| "native-return:span-offset-overflow")?;
    if lo >= hi {
        return Err("native-return:empty-expression-span".into());
    }
    let owner_path = owner_path(site.owner)
        .filter(|path| !path.is_empty())
        .ok_or("native-return:owner-path-missing")?;
    let required = OutboundReturnRequirement {
        key: input.key.clone(),
        associated_bridge: seam.bridge.materialize(
            input.key.owner_class,
            super::file_key_label(&file),
            lo,
            hi,
        ),
        adapter: seam.spec.template_key().into(),
        retention_evidence: None,
        native_lifetime: Some(NativeReturnEvidence {
            owner: site.owner.local_def_index.as_u32(),
            lifetime: interface.lifetime.clone(),
            plan_digest: digest,
        }),
        lifetime_origin: origins,
        terminal_interface: interface.form.key().into(),
    };
    let negative_write = NegativeWriteEvidence::NotApplicable;
    let event = MechanicalObligationEvent {
        key: required.key.clone(),
        owner_path,
        prior_reason: "return-not-adapted".into(),
        expected_form: seam.bridge.expected_form.clone(),
        found_form: seam.bridge.found_form.clone(),
        argument_kind: seam.bridge.argument_kind.clone(),
        source_shape: site.source_shape.into(),
        required_arms: seam.bridge.arm.clone(),
        mechanism: MechanicalMechanism::ReturnAdapter,
        composition_parent: None,
        dependency_classes: BTreeSet::from([input.key.owner_class]),
        evidence: MechanicalEvidence {
            extent: MechanicalExtent::None,
            retention: retention.clone(),
            negative_write: negative_write.clone(),
            terminal_contract: TerminalContract::Required {
                interface: required.terminal_interface.clone(),
            },
            unsafe_context: seam.bridge.unsafe_context,
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
        boundary_kind: seam.bridge.bridge_kind.clone(),
        endpoint: CanonicalCallee::Local(site.owner.to_def_id()),
        position: seam.bridge.position.clone(),
        source_form: seam.bridge.found_form.clone(),
        target_form: seam.bridge.expected_form.clone(),
        adapter: required.adapter.clone(),
        negative_write,
        retention,
        retention_evidence: None,
        native_lifetime: required.native_lifetime.clone(),
        lifetime_origin: required.lifetime_origin.clone(),
        pair_role: "not-applicable".into(),
        effect_carrier: None,
        terminal_interface: required.terminal_interface.clone(),
    };
    Ok((required, blueprint))
}

impl NativeReturnPlans {
    pub(crate) fn materialize(
        &self,
        terminal: &TerminalCallPlans,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> Result<Materialized, Vec<Failure>> {
        let mut selected = self
            .sites
            .iter()
            .filter(|(_, site)| !classes.contains(&site.key.owner_class))
            .collect::<Vec<_>>();
        selected.sort_by_key(|(key, _)| key.receipt_key());
        let (mut requirements, mut common, mut rows, mut failures) =
            (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        // AST emission consumes the terminal collection. Its active native
        // seams must also be owned by the frozen input inventory; walking only
        // captured sites would miss a newly added, disjoint terminal seam.
        for seam in terminal.seam_edits.iter().filter(|seam| {
            matches!(
                seam.bridge.bridge_kind.as_str(),
                "return-raw-to-ref" | "return-null-to-option"
            ) && !classes.contains(&seam.owner_class)
                && !seam.atom_ids.iter().any(|atom| atoms.contains(atom))
        }) {
            let facts = terminal
                .native_return_sites
                .iter()
                .filter(|fact| matching_seam(fact, seam))
                .collect::<Vec<_>>();
            let [fact] = facts.as_slice() else {
                failures.push(terminal_failure(
                    seam,
                    "native-return:terminal-seam-fact-not-unique",
                ));
                continue;
            };
            let Some(site) = self.sites.get(&site_key(fact)) else {
                failures.push(terminal_failure(
                    seam,
                    "native-return:terminal-seam-captured-site-missing",
                ));
                continue;
            };
            if site.fact != **fact || site.seam.as_ref() != Some(seam) {
                failures.push(failure(
                    site,
                    "native-return:terminal-native-metadata-drift",
                ));
            }
        }
        for (canonical, site) in selected {
            let result = (|| {
                if let Some(failure) = self.failures.get(canonical) {
                    return Err(failure.reason().to_owned());
                }
                let facts = terminal
                    .native_return_sites
                    .iter()
                    .filter(|fact| site_key(fact) == *canonical)
                    .collect::<Vec<_>>();
                if facts.as_slice() != [&site.fact] {
                    return Err("native-return:terminal-expression-inventory-drift".into());
                }
                let seams = terminal
                    .seam_edits
                    .iter()
                    .filter(|seam| matching_seam(&site.fact, seam))
                    .collect::<Vec<_>>();
                let [seam] = seams.as_slice() else {
                    return Err("native-return:terminal-common-seam-not-unique".into());
                };
                if site.seam.as_ref() != Some(*seam) {
                    return Err("native-return:terminal-native-metadata-drift".into());
                }
                if seam.atom_ids.iter().any(|atom| atoms.contains(atom)) {
                    return Ok(());
                }
                let required = self
                    .requirements
                    .get(canonical)
                    .ok_or("native-return:required-metadata-missing")?;
                requirements.push(required.clone());
                let blueprint = self
                    .blueprints
                    .get(canonical)
                    .ok_or("native-return:blueprint-missing")?;
                if required.key != site.key || blueprint.obligation.planned.key != site.key {
                    return Err("native-return:selection-key-drift".into());
                }
                let (events, specialized) = blueprint.materialize(true, false);
                common.extend(events);
                rows.extend(specialized);
                Ok(())
            })();
            if let Err(reason) = result {
                failures.push(failure(site, reason));
            }
        }
        if failures.is_empty() {
            Ok((requirements, common, rows))
        } else {
            Err(failures)
        }
    }
}
