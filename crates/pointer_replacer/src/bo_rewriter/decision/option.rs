//! Item-4 Option values and per-operation evidence. No model is changed here.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ExprKind, HirId, QPath, def::Res, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::{
    super::additive::{FamilyPolicy, FamilyStage},
    Decision, DecisionTable, Subject, SubjectKind, construction, emitability, seam,
};
use crate::bo_rewriter::{bridge_receipt::SignatureClassId, mechanical_receipt::*};

fn source_binding(mut expression: &rustc_hir::Expr<'_>) -> Option<HirId> {
    while let ExprKind::Cast(inner, _) = expression.kind {
        expression = inner;
    }
    let ExprKind::Path(QPath::Resolved(_, path)) = expression.kind else { return None };
    let Res::Local(binding) = path.res else { return None };
    Some(binding)
}

fn integer_pointer_cast(tcx: TyCtxt<'_>, expression: &rustc_hir::Expr<'_>) -> bool {
    let ExprKind::Cast(inner, _) = expression.kind else { return false };
    !matches!(
        tcx.typeck(expression.hir_id.owner.def_id)
            .expr_ty(inner)
            .kind(),
        rustc_middle::ty::TyKind::RawPtr(..) | rustc_middle::ty::TyKind::Ref(..)
    )
}

fn source_form(
    table: &DecisionTable,
    owner: LocalDefId,
    binding: Option<HirId>,
) -> Result<seam::Form, &'static str> {
    let decision = binding.and_then(|binding| {
        table
            .entries
            .iter()
            .find(|(subject, _)| subject.fn_did == owner && subject.hir_id == binding)
            .map(|(_, decision)| decision)
    });
    match decision {
        Some(Decision::Ref { mutable } | Decision::InferredRef { mutable, .. }) => {
            Ok(seam::Form::Ref { mutable: *mutable })
        }
        Some(Decision::Slice { mutable, .. }) => Ok(seam::Form::Slice { mutable: *mutable }),
        Some(Decision::Opt { mutable, slice, .. }) => Ok(seam::Form::Opt {
            mutable: *mutable,
            slice: *slice,
        }),
        Some(Decision::Box(plan)) => Err(if plan.optional { "opt-box" } else { "box" }),
        Some(Decision::Degraded(_)) | None => Ok(seam::Form::Raw),
    }
}

fn casts_preserve_pointee(tcx: TyCtxt<'_>, mut expression: &rustc_hir::Expr<'_>) -> bool {
    use rustc_middle::ty::TyKind;
    let typeck = tcx.typeck(expression.hir_id.owner.def_id);
    while let ExprKind::Cast(inner, _) = expression.kind {
        match (
            typeck.expr_ty(inner).kind(),
            typeck.expr_ty(expression).kind(),
        ) {
            (TyKind::RawPtr(source, _) | TyKind::Ref(_, source, _), TyKind::RawPtr(target, _))
                if source == target => {}
            _ => return false,
        }
        expression = inner;
    }
    true
}

/// Carry an admitted slice payload through exact local Option copies before
/// lifetime and seam planning. Neither fatness alone nor a refused decision
/// supplies a source for this presentation change.
pub(crate) fn inherit_wrapped_payloads(
    ctx: &super::Ctx<'_, '_>,
    entries: &mut [(Subject, Decision)],
) {
    use rustc_middle::ty::TyKind;

    let thin_options = entries
        .iter()
        .filter(|(subject, decision)| {
            ctx.family_policy
                .enabled(subject.fn_did, FamilyStage::Option)
                && matches!(subject.kind, SubjectKind::Local)
                && match decision {
                    Decision::Opt { slice: false, .. } => true,
                    Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::Opt { slice: true, .. }
                    | Decision::Box(_)
                    | Decision::Degraded(_) => false,
                }
        })
        .count();
    if thin_options == 0 {
        return;
    }
    let raw_arguments = ctx.facts.raw_boundary_argument_paths();
    let deferred = ctx
        .slice_uses
        .iter()
        .flat_map(|(node, uses)| {
            uses.raw_uses
                .iter()
                .filter(|site| site.source_shape != "cursor")
                .map(move |site| (node.0, node.1, site.span.lo().0, site.span.hi().0))
        })
        .collect();

    // Every successful round removes at least one thin Option candidate.
    for _ in 0..thin_options {
        let candidates = entries.iter().enumerate().filter_map(|(index, (subject, decision))| {
            if !ctx.family_policy.enabled(subject.fn_did, FamilyStage::Option)
                || !matches!(subject.kind, SubjectKind::Local) {
                return None;
            }
            let mutable = match decision {
                Decision::Opt { mutable, slice: false, .. } => *mutable,
                Decision::Ref { .. } | Decision::InferredRef { .. } | Decision::Slice { .. }
                | Decision::Opt { slice: true, .. } | Decision::Box(_) | Decision::Degraded(_) => return None,
            };
            let name = subject.param_name.clone()?;
            let node = (subject.fn_did, subject.hir_id);
            let typeck = ctx.tcx.typeck(subject.fn_did);
            let rustc_hir::Node::Pat(pattern) = ctx.tcx.hir_node(subject.hir_id) else { return None };
            let TyKind::RawPtr(pointee, _) = typeck.pat_ty(pattern).kind() else { return None };
            let values = ctx.constructions.init_hirs.get(&node).into_iter().copied()
                .chain(ctx.opt_uses.get(&node).into_iter()
                    .flat_map(|uses| uses.assignments.iter().map(|site| site.rhs)));
            let inherits = values.into_iter().any(|hir| {
                let expression = ctx.tcx.hir_node(hir).expect_expr();
                if !casts_preserve_pointee(ctx.tcx, expression)
                    || !matches!(typeck.expr_ty(expression).kind(), TyKind::RawPtr(source, _) if source == pointee)
                {
                    return false;
                }
                let Some(source) = source_binding(expression) else { return false };
                match entries.iter().find(|(source_subject, _)| {
                    source_subject.fn_did == subject.fn_did && source_subject.hir_id == source
                }).map(|(_, decision)| decision) {
                    Some(Decision::Slice { mutable: source_mutable, .. }
                        | Decision::Opt { mutable: source_mutable, slice: true, .. }) => !mutable || *source_mutable,
                    Some(Decision::Ref { .. } | Decision::InferredRef { .. }
                        | Decision::Opt { slice: false, .. } | Decision::Box(_) | Decision::Degraded(_))
                        | None => false,
                }
            });
            inherits.then_some((index, node, mutable, name))
        }).collect::<Vec<_>>();
        if candidates.is_empty() {
            break;
        }

        let names = candidates
            .iter()
            .map(|(_, node, _, name)| (*node, name.clone()))
            .collect();
        let accessors = candidates
            .iter()
            .map(|(_, node, mutable, name)| {
                let repeated = ctx
                    .opt_uses
                    .get(node)
                    .is_some_and(|uses| uses.non_test_uses > 1);
                let index = if *mutable && repeated {
                    format!("{name}.as_mut().unwrap()")
                } else {
                    format!("{name}.unwrap()")
                };
                let deref = format!("(&{}{index}[0])", if *mutable { "mut " } else { "" });
                (*node, emitability::Accessor { deref, index })
            })
            .collect();
        let payload_slices = candidates
            .iter()
            .map(|(_, node, _, _)| *node)
            .collect::<FxHashSet<_>>();
        let mut owners = candidates
            .iter()
            .map(|(_, node, _, _)| node.0)
            .collect::<Vec<_>>();
        owners.sort_by_key(|owner| owner.local_def_index.as_u32());
        owners.dedup();
        let refreshed = emitability::collect_opt_uses(
            ctx.tcx,
            &owners,
            &names,
            &accessors,
            &payload_slices,
            &raw_arguments,
            &deferred,
        );
        let mut changed = false;
        for (index, node, mutable, _) in candidates {
            let uses = refreshed.get(&node).cloned().unwrap_or_default();
            if uses.unsupported.is_some() {
                continue;
            }
            entries[index].1 = Decision::Opt {
                mutable,
                slice: true,
                uses: uses.rewrites,
            };
            changed = true;
        }
        if !changed {
            break;
        }
    }
}

pub(crate) fn receipt(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    hir: HirId,
    family: MechanicalFamily,
    operation: &str,
    source: seam::Form,
    target: seam::Form,
    adapter: String,
    reason: Option<MechanicalTerminalReason>,
    evidence: MechanicalEvidence,
) -> OptionPresentationReceiptPlan {
    let owner_class = SignatureClassId::of(subject.fn_did);
    let depth = u32::from(subject.ptr_depth.saturating_sub(1));
    let event = MechanicalObligationEvent {
        key: MechanicalObligationKey {
            owner_class,
            subject: MechanicalSubjectKey::Local {
                owner: subject.fn_did,
                mir_local: subject.local.as_u32(),
                slot_depth: depth,
            },
            site: CanonicalSiteKey {
                owner: subject.fn_did,
                location: CanonicalLocation::Hir {
                    owner: hir.owner.def_id,
                    item_local_id: hir.local_id.as_u32(),
                },
                callee: None,
                argument_index: None,
                slot_depth: depth,
            },
            family,
        },
        owner_path: tcx.def_path_str(subject.fn_did.to_def_id()),
        prior_reason: family.key().to_owned(),
        expected_form: target.key().to_owned(),
        found_form: source.key().to_owned(),
        argument_kind: operation.to_owned(),
        source_shape: operation.to_owned(),
        required_arms: String::new(),
        mechanism: MechanicalMechanism::OptionPresentation,
        composition_parent: None,
        dependency_classes: BTreeSet::new(),
        evidence: evidence.clone(),
        stage: MechanicalStage::Plan,
        state: MechanicalState::Planned,
        terminal_reason: None,
    };
    OptionPresentationReceiptPlan {
        obligation: MechanicalObligationPlan {
            planned: event,
            intended_terminal_state: if reason.is_some() {
                MechanicalState::HeldNonmechanical
            } else {
                MechanicalState::Applied
            },
            intended_terminal_reason: reason,
        },
        nullability_fact: if subject.null_init {
            "construction-site-null-or-use-site-is-null"
        } else {
            "use-site-is-null-or-null-assignment"
        }
        .to_owned(),
        source_form: source.key().to_owned(),
        target_form: target.key().to_owned(),
        operation: operation.to_owned(),
        terminal_contract: evidence.terminal_contract,
        retention: evidence.retention,
        adapter,
        owner_class,
    }
}

pub(crate) fn plan_values(
    tcx: TyCtxt<'_>,
    table: &mut DecisionTable,
    constructions: &construction::ConstructionFacts,
    uses: &FxHashMap<(LocalDefId, HirId), emitability::OptUses>,
    family_policy: &FamilyPolicy,
) -> (
    Vec<OptionPresentationReceiptPlan>,
    Vec<(LocalDefId, HirId)>,
    Vec<((LocalDefId, HirId), Span)>,
) {
    let mut receipts = Vec::new();
    let mut edits = Vec::<((LocalDefId, HirId), emitability::UseEdit)>::new();
    let mut initializers = Vec::new();
    let mut composed_uses = Vec::new();
    let decisions = table
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect();
    for (subject, decision) in &table.entries {
        if !family_policy.enabled(subject.fn_did, FamilyStage::Option) {
            continue;
        }
        let (mutable, slice) = match decision {
            Decision::Opt { mutable, slice, .. } => (*mutable, *slice),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => continue,
        };
        let node = (subject.fn_did, subject.hir_id);
        let target = seam::Form::Opt { mutable, slice };
        if table.option_mut_bindings.contains(&node) {
            receipts.push(receipt(
                tcx,
                subject,
                subject.hir_id,
                MechanicalFamily::OptUseUnsupported,
                "mutable-binding",
                seam::Form::Raw,
                target,
                "mut-binding-for-scoped-reborrow".to_owned(),
                None,
                MechanicalEvidence::default(),
            ));
        }
        let mut values = Vec::<(HirId, Span, bool)>::new();
        if matches!(subject.kind, SubjectKind::Local)
            && let (Some(hir), Some(span)) = (
                constructions.init_hirs.get(&node),
                constructions.init_spans.get(&node),
            )
        {
            values.push((*hir, *span, true));
        }
        if let Some(uses) = uses.get(&node) {
            values.extend(
                uses.assignments
                    .iter()
                    .map(|site| (site.rhs, site.span, false)),
            );
            for site in &uses.sites {
                if site.operation == "deferred-boundary-or-copy" {
                    continue;
                }
                receipts.push(receipt(
                    tcx,
                    subject,
                    site.hir_id,
                    MechanicalFamily::OptUseUnsupported,
                    site.operation,
                    target,
                    target,
                    site.operation.to_owned(),
                    None,
                    MechanicalEvidence::default(),
                ));
            }
        }
        for (hir, span, initializer) in values {
            if initializer
                && let Some(receiver) =
                    super::return_receiver::active_initializer(table, node, hir, span)
                && receiver.receiver_form == target
            {
                // Consume the callee's Option value directly. Calling a raw
                // pointer constructor here would wrap/reborrow it a second time.
                let interface = format!(
                    "callee={}:type={}:lifetime-plan={}",
                    receiver.callee.local_def_index.as_u32(),
                    receiver.candidate_interface.temporary_type(),
                    receiver.candidate_interface.lifetime_plan_digest
                );
                let mut row = receipt(
                    tcx,
                    subject,
                    hir,
                    MechanicalFamily::OptLocalConstruction,
                    "borrowed-return-receive",
                    receiver.candidate_interface.form,
                    target,
                    match receiver.coercion {
                        super::return_receiver::ReceiverCoercion::Identity => {
                            "owned-borrowed-call-result"
                        }
                        super::return_receiver::ReceiverCoercion::SharedOption => {
                            "shared-option-return-map"
                        }
                    }
                    .to_owned(),
                    None,
                    MechanicalEvidence {
                        terminal_contract: TerminalContract::Optional {
                            interface: interface.clone(),
                        },
                        ..MechanicalEvidence::default()
                    },
                );
                row.nullability_fact = interface;
                receipts.push(row);
                initializers.push(node);
                continue;
            }
            let expression = tcx.hir_node(hir).expect_expr();
            let shape = emitability::classify_arg(tcx, expression);
            let null = emitability::is_zero_literal(expression);
            let family = if null {
                MechanicalFamily::NullInit
            } else {
                MechanicalFamily::OptLocalConstruction
            };
            let operation = match (initializer, null) {
                (true, true) => "null-initialization",
                (false, true) => "null-assignment",
                (true, false) => "nullable-construction",
                (false, false) => "nullable-assignment",
            };
            let found = match source_form(table, subject.fn_did, source_binding(expression)) {
                Ok(_) => seam::argument_form(subject.fn_did, &shape, &decisions),
                Err(box_form) => {
                    let mut held = receipt(
                        tcx,
                        subject,
                        hir,
                        family,
                        operation,
                        seam::Form::Raw,
                        target,
                        String::new(),
                        Some(MechanicalTerminalReason::BoxFamily),
                        MechanicalEvidence::default(),
                    );
                    held.source_form = box_form.to_owned();
                    held.obligation.planned.found_form = box_form.to_owned();
                    receipts.push(held);
                    continue;
                }
            };
            let mut evidence = MechanicalEvidence::default();
            let mut reason = (found != seam::Form::Raw && !casts_preserve_pointee(tcx, expression))
                .then(|| {
                    MechanicalTerminalReason::EvidenceMissing(
                        "option-value-cast-pointee-unbuilt".to_owned(),
                    )
                });
            let mut adapter = String::new();
            let view_span = match shape {
                emitability::ArgShape::AddrOfCast { inner, .. } => inner,
                _ => span,
            };
            let text = tcx
                .sess
                .source_map()
                .span_to_snippet(view_span)
                .unwrap_or_default();
            let composed = construction::collect_composable_edits(table, view_span);
            let text = match construction::compose_initializer(view_span, &text, &composed) {
                Ok(text) => text,
                Err(why) => {
                    reason = Some(MechanicalTerminalReason::CompositionCrossingUnhoistable(
                        why,
                    ));
                    text
                }
            };
            if table.entries.iter().any(|(inner, _)| {
                inner.fn_did == subject.fn_did
                    && inner.hir_id != subject.hir_id
                    && span.contains(inner.binding_span)
            }) {
                reason = Some(MechanicalTerminalReason::CompositionCrossingUnhoistable(
                    "option-value-encloses-declaration".to_owned(),
                ));
            }
            let unsafe_fn = tcx
                .fn_sig(subject.fn_did)
                .skip_binder()
                .skip_binder()
                .safety
                .is_unsafe();
            let same_slice = slice && found == target;
            let replacement = if reason.is_some() {
                None
            } else if initializer
                && table
                    .depth2_npo_storages
                    .iter()
                    .any(|storage| storage.node == node)
            {
                adapter = "owned-depth2-npo-storage".to_owned();
                None
            } else if null {
                adapter = "None".to_owned();
                Some("None".to_owned())
            } else if integer_pointer_cast(tcx, expression) {
                reason = Some(MechanicalTerminalReason::EvidenceMissing(
                    "option-integer-pointer-construction".to_owned(),
                ));
                None
            } else if same_slice {
                adapter = "owned-same-form-slice-carrier".to_owned();
                None
            } else if slice && initializer && found == seam::Form::Raw {
                adapter = "owned-item2-nullable-slice-construction".to_owned();
                None
            } else if slice && found == seam::Form::Raw {
                let element = subject
                    .pointee_span
                    .and_then(|span| tcx.sess.source_map().span_to_snippet(span).ok())
                    .or_else(|| {
                        table
                            .declaration_pointees
                            .get(&node)
                            .map(|ty| ty.pointee.clone())
                    })
                    .unwrap_or_else(|| "_".to_owned());
                evidence.extent = MechanicalExtent::Fallback {
                    receipt: FALLBACK_EXTENT_RECEIPT.to_owned(),
                    waiver_id: SLICE_EXTENT_WAIVER_ID.to_owned(),
                };
                adapter = "nullable-slice-assignment".to_owned();
                Some(construction::render_slice_constructor(
                    &text,
                    &element,
                    mutable,
                    true,
                    "crate::FALLBACK_SLICE_EXTENT",
                    unsafe_fn,
                    subject.local.as_u32(),
                ))
            } else {
                let text = source_binding(expression)
                    .filter(|_| found != seam::Form::Raw)
                    .and_then(|binding| {
                        table.entries.iter().find(|(source, _)| {
                            source.fn_did == subject.fn_did && source.hir_id == binding
                        })
                    })
                    .and_then(|(source, _)| source.param_name.clone())
                    .unwrap_or(text);
                // The Option type no longer supplies the source raw-pointer
                // coercion. Preserve it explicitly before the pointer API,
                // including its precedence for compound raw expressions.
                let text = if found == seam::Form::Raw {
                    let raw_type = super::raw_boundary::raw_target_type(
                        tcx,
                        tcx.typeck(subject.fn_did).node_type(subject.hir_id),
                    )
                    .expect("optional destination has an original raw pointer type");
                    format!(
                        "({text} as *{} {})",
                        if mutable { "mut" } else { "const" },
                        raw_type.pointee
                    )
                } else {
                    text
                };
                match seam::glue(target, found, None) {
                    Ok(Some((spec, _))) => {
                        adapter = spec.template_key().to_owned();
                        spec.render_in_context(&text, unsafe_fn)
                    }
                    Ok(None) => {
                        adapter = "same-form-option-copy-or-reborrow".to_owned();
                        Some(match found {
                            seam::Form::Opt { mutable: true, .. } => format!(
                                "{text}.{}()",
                                if mutable { "as_deref_mut" } else { "as_deref" }
                            ),
                            seam::Form::Raw
                            | seam::Form::Ref { .. }
                            | seam::Form::Slice { .. }
                            | seam::Form::Opt { mutable: false, .. } => text,
                        })
                    }
                    Err(block) => {
                        reason = Some(MechanicalTerminalReason::EvidenceMissing(format!(
                            "option-value:{}",
                            block.key()
                        )));
                        None
                    }
                }
            };
            let replacement = replacement.map(|replacement| {
                if initializer && let Some(pattern) = table.declaration_patterns.get(&node) {
                    let explicit =
                        super::declaration::emitted_type(decision, &pattern.pointee, None)
                            .expect("pattern construction has a decided borrowed form");
                    adapter = "typed-pattern-component".to_owned();
                    format!(
                        "{{ let {}: {explicit} = {replacement}; {} }}",
                        pattern.temporary, pattern.temporary
                    )
                } else {
                    replacement
                }
            });
            if let Some(replacement) = replacement {
                edits.push((
                    node,
                    emitability::UseEdit {
                        span,
                        replacement,
                        bridge_kind: if composed.is_empty() {
                            "option-value"
                        } else {
                            "option-value-composed"
                        },
                    },
                ));
                composed_uses.extend(composed.iter().map(|(span, _)| (node, *span)));
                if initializer {
                    initializers.push(node);
                }
            } else if adapter.is_empty() && reason.is_none() {
                reason = Some(MechanicalTerminalReason::EvidenceMissing(
                    "option-value-render-unavailable".to_owned(),
                ));
            }
            receipts.push(receipt(
                tcx, subject, hir, family, operation, found, target, adapter, reason, evidence,
            ));
        }
    }
    for (node, edit) in edits {
        let decision = &mut table
            .entries
            .iter_mut()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
            .expect("Option value subject")
            .1;
        match decision {
            Decision::Opt { uses, .. } => uses.push(edit),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => unreachable!("Option value remains optional"),
        }
    }
    receipts.sort_by_key(|receipt| receipt.obligation.planned.key.receipt_key());
    initializers.sort_by_key(|node| (node.0.local_def_index.as_u32(), node.1.local_id.as_u32()));
    initializers.dedup();
    (receipts, initializers, composed_uses)
}

fn return_handoff_is_covered(
    table: &DecisionTable,
    subject: &Subject,
    source: seam::Form,
    uses: &emitability::OptUses,
    site: &emitability::OptUseSite,
) -> bool {
    if !matches!(source, seam::Form::Opt { .. } | seam::Form::Slice { .. })
        || table
            .return_interfaces
            .failures
            .contains_key(&subject.fn_did)
    {
        return false;
    }
    let Some(interface) = table.return_interfaces.functions.get(&subject.fn_did) else {
        return false;
    };
    if interface.form != source {
        return false;
    }
    let Some(lifetime) = table.lifetime_plan.function(subject.fn_did) else { return false };
    if lifetime.digest() != interface.lifetime_plan_digest
        || lifetime.lifetime_for(super::lifetime::FnSignatureSlot::RETURN)
            != Some(interface.lifetime.as_str())
    {
        return false;
    }
    uses.return_handoffs
        .iter()
        .filter(|handoff| {
            handoff.owner == subject.fn_did
                && handoff.root == Some(subject.hir_id)
                && handoff.source_shape == "bare-local"
                && handoff.span == site.span
        })
        .count()
        == 1
}

pub(crate) fn plan_operations(
    program: &crate::utils::rustc::RustProgram<'_>,
    table: &mut DecisionTable,
    uses: &FxHashMap<(LocalDefId, HirId), emitability::OptUses>,
    raw: &super::raw_boundary::RawBoundaryDispositionIndex,
    slice_uses: &FxHashMap<(LocalDefId, HirId), emitability::SliceUses>,
    retention: &super::raw_boundary::RetentionSummaries,
    mut_facts: &crate::analyses::borrow_ownership::mutability_facts::MutFacts,
    family_policy: &FamilyPolicy,
) -> Vec<OptionPresentationReceiptPlan> {
    use super::raw_boundary::{self, RawMutability, RetentionVerdict};
    use crate::bo_rewriter::bridge_receipt::BridgeRetentionTier;
    let tcx = program.tcx;
    let mut out = Vec::new();
    let mut body_edits = Vec::new();
    for (subject, decision) in &table.entries {
        if !family_policy.enabled(subject.fn_did, FamilyStage::Option) {
            continue;
        }
        let source = match decision {
            Decision::Opt { mutable, slice, .. } => seam::Form::Opt {
                mutable: *mutable,
                slice: *slice,
            },
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => continue,
        };
        let node = (subject.fn_did, subject.hir_id);
        let Some(uses) = uses.get(&node) else { continue };
        for site in uses
            .sites
            .iter()
            .filter(|site| site.operation == "handoff-return")
        {
            if !return_handoff_is_covered(table, subject, source, uses, site) {
                out.push(receipt(
                    tcx,
                    subject,
                    site.hir_id,
                    MechanicalFamily::OptUseUnsupported,
                    site.operation,
                    source,
                    source,
                    site.operation.to_owned(),
                    Some(MechanicalTerminalReason::EvidenceMissing(
                        "handoff-return:later-return-or-sink-wave".to_owned(),
                    )),
                    MechanicalEvidence::default(),
                ));
            }
        }
        for site in uses
            .sites
            .iter()
            .filter(|site| site.operation == "deferred-boundary-or-copy")
        {
            let calls = raw
                .inventoried_sites()
                .filter(|(_, _, render)| {
                    render.node == Some(node)
                        && render
                            .span
                            .source_callsite()
                            .contains(site.span.source_callsite())
                })
                .collect::<Vec<_>>();
            if let [(key, disposition, render)] = calls.as_slice() {
                let target = if render.target_stays_raw {
                    seam::Form::Raw
                } else {
                    render.callee_local.and_then(|callee| table.entries.iter().find(|(parameter, _)| {
                        parameter.fn_did == callee && matches!(parameter.kind, SubjectKind::Param { hir_index } if hir_index == key.argument_index)
                    })).map_or(seam::Form::Raw, |(_, decision)| seam::form_of(decision))
                };
                let carriers = table
                    .seams
                    .edits
                    .iter()
                    .filter(|edit| {
                        edit.bridge.caller == subject.fn_did
                            && edit.param_index == key.argument_index
                            && edit.span.source_callsite() == render.span.source_callsite()
                    })
                    .collect::<Vec<_>>();
                let mut evidence = MechanicalEvidence::default();
                let mut reason = None;
                let mut adapter = "same-form-call".to_owned();
                let operation = match target {
                    seam::Form::Raw => "call-raw",
                    seam::Form::Ref { .. } | seam::Form::Slice { .. } => "call-required",
                    seam::Form::Opt { .. } => "call-optional",
                };
                let shared_to_mut = target == seam::Form::Raw
                    && matches!(source, seam::Form::Opt { mutable: false, .. })
                    && render.target.mutability == super::raw_boundary::RawMutability::Mut;
                if shared_to_mut {
                    evidence.negative_write = match raw.negative_write_evidence(key) {
                        Some(super::raw_boundary::NegativeWriteEvidence::FosterImmutable) => {
                            NegativeWriteEvidence::FosterImmutable
                        }
                        Some(super::raw_boundary::NegativeWriteEvidence::LibcReadOnly) => {
                            NegativeWriteEvidence::LibcReadOnly(format!("{:?}", key.callee))
                        }
                        None => NegativeWriteEvidence::Missing,
                    };
                }
                if let [carrier] = carriers.as_slice() {
                    adapter = carrier.spec.template_key().to_owned();
                    evidence.retention = match carrier.bridge.retention {
                        BridgeRetentionTier::T1 => MechanicalRetention::T1,
                        BridgeRetentionTier::T2 => MechanicalRetention::T2 {
                            waiver_id: carrier.bridge.waiver_id.clone().unwrap_or_default(),
                        },
                        BridgeRetentionTier::None => MechanicalRetention::None,
                    };
                    if operation == "call-required" && carrier.spec.unwrap.is_none() {
                        reason = Some(MechanicalTerminalReason::TerminalContractMissing);
                    }
                } else if target != source {
                    reason = Some(match disposition {
                        super::raw_boundary::RawBoundaryDisposition::Blocked {
                            reason: super::raw_boundary::RawBoundaryBlockReason::PositiveRetention,
                            ..
                        } => {
                            evidence.retention = MechanicalRetention::PositiveRetention;
                            MechanicalTerminalReason::PositiveRetention
                        }
                        super::raw_boundary::RawBoundaryDisposition::Blocked {
                            reason: super::raw_boundary::RawBoundaryBlockReason::SharedToMut,
                            ..
                        } => MechanicalTerminalReason::RbNegativeWriteAbsent,
                        _ => MechanicalTerminalReason::EvidenceMissing(format!(
                            "option-call-carrier:matches={}",
                            carriers.len()
                        )),
                    });
                }
                if operation != "call-raw" {
                    evidence.terminal_contract = TerminalContract::Missing;
                }
                let mut plan = receipt(
                    tcx,
                    subject,
                    site.hir_id,
                    MechanicalFamily::OptUseUnsupported,
                    operation,
                    source,
                    target,
                    adapter,
                    reason,
                    evidence,
                );
                plan.obligation.planned.key.site.callee = Some(match render.callee_local {
                    Some(callee) => CanonicalCallee::Local(callee.to_def_id()),
                    None => CanonicalCallee::Foreign(key.callee.path.clone()),
                });
                plan.obligation.planned.key.site.argument_index =
                    u32::try_from(key.argument_index).ok();
                if operation == "call-required" {
                    plan.obligation.planned.mechanism = MechanicalMechanism::OptionUnwrapRequired;
                } else if shared_to_mut {
                    plan.obligation.planned.mechanism = MechanicalMechanism::SharedRefToMutRaw;
                }
                if operation != "call-raw"
                    && let Some(callee) = render.callee_local
                {
                    plan.obligation
                        .planned
                        .dependency_classes
                        .insert(SignatureClassId::of(callee));
                }
                out.push(plan);
            } else if calls.is_empty() {
                if let Some(carrier) = table.slice_use_receipts.iter().find(|receipt| {
                    receipt.obligation.planned.key.subject
                        == MechanicalSubjectKey::Local {
                            owner: subject.fn_did,
                            mir_local: subject.local.as_u32(),
                            slot_depth: u32::from(subject.ptr_depth.saturating_sub(1)),
                        }
                        && receipt.use_site.location
                            == CanonicalLocation::Hir {
                                owner: site.hir_id.owner.def_id,
                                item_local_id: site.hir_id.local_id.as_u32(),
                            }
                }) {
                    let mut obligation = carrier.obligation.clone();
                    obligation.planned.key.family = MechanicalFamily::OptUseUnsupported;
                    obligation.planned.prior_reason = "opt-use-unsupported".to_owned();
                    out.push(OptionPresentationReceiptPlan {
                        obligation,
                        nullability_fact: "settled-optional-slice".to_owned(),
                        source_form: carrier.source_form.clone(),
                        target_form: carrier.target_form.clone(),
                        operation: "owned-slice-body-use".to_owned(),
                        terminal_contract: TerminalContract::NotApplicable,
                        retention: carrier.retention.clone(),
                        adapter: carrier.adapter.clone(),
                        owner_class: carrier.owner_class,
                    });
                } else {
                    // A value plan may own a same-function copy into Option.
                    // Its RHS includes any identity casts around this use.
                    let mut rhs = tcx.hir_node(site.hir_id).expect_expr();
                    while let rustc_hir::Node::Expr(parent) = tcx.parent_hir_node(rhs.hir_id)
                        && matches!(parent.kind, ExprKind::Cast(inner, _) if inner.hir_id == rhs.hir_id)
                    {
                        rhs = parent;
                    }
                    let owned = table.option_receipts.iter().find(|receipt| {
                        receipt.obligation.planned.key.site.location
                            == CanonicalLocation::Hir {
                                owner: rhs.hir_id.owner.def_id,
                                item_local_id: rhs.hir_id.local_id.as_u32(),
                            }
                            && rhs
                                .span
                                .source_callsite()
                                .contains(site.span.source_callsite())
                            && source_binding(rhs) == Some(subject.hir_id)
                            && matches!(
                                receipt.operation.as_str(),
                                "nullable-construction" | "nullable-assignment"
                            )
                    });
                    if let Some(owned) = owned {
                        let mut plan = receipt(
                            tcx,
                            subject,
                            site.hir_id,
                            MechanicalFamily::OptUseUnsupported,
                            "body-use",
                            source,
                            source,
                            "owned-option-value".to_owned(),
                            owned.obligation.intended_terminal_reason.clone(),
                            MechanicalEvidence::default(),
                        );
                        plan.obligation.intended_terminal_state =
                            owned.obligation.intended_terminal_state;
                        plan.target_form = owned.target_form.clone();
                        plan.obligation.planned.expected_form = owned.target_form.clone();
                        out.push(plan);
                        continue;
                    }
                    let observations = slice_uses
                        .get(&node)
                        .into_iter()
                        .flat_map(|uses| &uses.raw_uses)
                        .filter(|observed| {
                            observed.hir_id == site.hir_id
                                && matches!(observed.source_shape, "body-copy" | "field-store")
                        })
                        .collect::<Vec<_>>();
                    let mut evidence = MechanicalEvidence::default();
                    let mut reason = None;
                    let mut adapter = String::new();
                    let mut target_form = seam::Form::Raw.key().to_owned();
                    let mut shared_to_mut = false;
                    if let [observed] = observations.as_slice()
                        && matches!(source, seam::Form::Opt { slice: false, .. })
                    {
                        let destination = observed.destination.and_then(|binding| {
                            table.entries.iter().find(|(destination, _)| {
                                destination.fn_did == subject.fn_did
                                    && destination.hir_id == binding
                            })
                        });
                        match source_form(table, subject.fn_did, observed.destination) {
                            Err(box_form) => {
                                target_form = box_form.to_owned();
                                reason = Some(MechanicalTerminalReason::BoxFamily);
                            }
                            Ok(form) if form != seam::Form::Raw => {
                                target_form = form.key().to_owned();
                                reason = Some(MechanicalTerminalReason::EvidenceMissing(format!(
                                    "option-body-destination-unbuilt:{}",
                                    form.key()
                                )));
                            }
                            Ok(_) => {
                                // Query every copied destination, including copies from
                                // parameters, before granting the local-alias waiver.
                                let destination_retention = destination.map(|(destination, _)| {
                                    retention.copied_local_retention(
                                        program,
                                        subject.fn_did,
                                        destination.local,
                                    )
                                });
                                let positive = observed.source_shape == "field-store"
                                    || matches!(
                                        destination_retention,
                                        Some(RetentionVerdict::Retains { .. })
                                    )
                                    || match subject.kind {
                                        SubjectKind::Param { hir_index } => matches!(
                                            retention.get(subject.fn_did, hir_index),
                                            Some(RetentionVerdict::Retains { .. })
                                        ),
                                        SubjectKind::Local => false,
                                    };
                                let mutable =
                                    matches!(source, seam::Form::Opt { mutable: true, .. });
                                shared_to_mut =
                                    !mutable && observed.target.mutability == RawMutability::Mut;
                                let read_only = !mut_facts
                                    .is_defaulted(subject.fn_did, subject.local)
                                    && !mut_facts.is_mutable(subject.fn_did, subject.local);
                                if positive {
                                    evidence.retention = MechanicalRetention::PositiveRetention;
                                    reason = Some(MechanicalTerminalReason::PositiveRetention);
                                } else if !matches!(
                                    destination_retention,
                                    Some(RetentionVerdict::Unknown { .. })
                                ) {
                                    reason = Some(MechanicalTerminalReason::EvidenceMissing(
                                        "option-body-destination-retention-unavailable".to_owned(),
                                    ));
                                } else if shared_to_mut && !read_only {
                                    evidence.negative_write = NegativeWriteEvidence::Missing;
                                    reason = Some(MechanicalTerminalReason::RbNegativeWriteAbsent);
                                } else if mutable
                                    && observed.target.mutability == RawMutability::Mut
                                    && !subject.mut_binding
                                    && !table.option_mut_bindings.contains(&node)
                                {
                                    reason = Some(MechanicalTerminalReason::EvidenceMissing(
                                        "option-body-mut-binding-unavailable".to_owned(),
                                    ));
                                } else {
                                    // The edit replaces the source path, leaving its
                                    // enclosing raw casts intact. Its pointee therefore
                                    // comes from that path, not the final destination.
                                    let replacement = subject.param_name.as_deref().and_then(|name| {
                                        let mut view_target = raw_boundary::raw_target_type(tcx,
                                            tcx.typeck(subject.fn_did).expr_ty(tcx.hir_node(site.hir_id).expect_expr()))?;
                                        view_target.mutability = observed.target.mutability;
                                        raw_boundary::pair_raw_view_expression(Some(decision), &view_target, name, "bare-local")
                                            .or_else(|| (shared_to_mut && read_only).then(|| format!(
                                                "{name}.as_deref().map_or(core::ptr::null_mut::<{}>(), |value| core::ptr::from_ref(value).cast_mut())",
                                                view_target.pointee)))
                                    });
                                    if let Some(replacement) = replacement {
                                        adapter = "body-option-raw-view".to_owned();
                                        evidence.retention = MechanicalRetention::T2 {
                                            waiver_id: crate::bo_rewriter::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.to_owned(),
                                        };
                                        if shared_to_mut {
                                            evidence.negative_write =
                                                NegativeWriteEvidence::FosterImmutable;
                                        }
                                        body_edits.push((
                                            node,
                                            emitability::UseEdit {
                                                span: site.span,
                                                replacement,
                                                bridge_kind: "subject-use",
                                            },
                                        ));
                                    } else {
                                        reason = Some(MechanicalTerminalReason::EvidenceMissing(
                                            "option-body-template-unavailable".to_owned(),
                                        ));
                                    }
                                }
                            }
                        }
                    } else {
                        reason = Some(MechanicalTerminalReason::EvidenceMissing(
                            "option-body-carrier-unavailable".to_owned(),
                        ));
                    }
                    let mut plan = receipt(
                        tcx,
                        subject,
                        site.hir_id,
                        MechanicalFamily::OptUseUnsupported,
                        "body-use",
                        source,
                        seam::Form::Raw,
                        adapter,
                        reason,
                        evidence,
                    );
                    plan.target_form = target_form.clone();
                    plan.obligation.planned.expected_form = target_form;
                    if shared_to_mut {
                        plan.obligation.planned.mechanism = MechanicalMechanism::SharedRefToMutRaw;
                    }
                    out.push(plan);
                }
            } else {
                out.push(receipt(
                    tcx,
                    subject,
                    site.hir_id,
                    MechanicalFamily::OptUseUnsupported,
                    "call-ambiguous",
                    source,
                    source,
                    String::new(),
                    Some(MechanicalTerminalReason::EvidenceMissing(
                        "option-call-identity-ambiguous".to_owned(),
                    )),
                    MechanicalEvidence::default(),
                ));
            }
        }
    }
    for edit in table
        .seams
        .edits
        .iter()
        .filter(|edit| edit.spec.null_arm == seam::NullArm::LiteralNone)
    {
        if !family_policy.enabled(edit.owner_class.local_def_id(), FamilyStage::Option) {
            continue;
        }
        let crate::bo_rewriter::bridge_receipt::BridgeCalleeId::Local(callee) = edit.bridge.callee
        else {
            continue;
        };
        let Some((parameter, decision)) = table.entries.iter().find(|(subject, _)| subject.fn_did == callee
            && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == edit.param_index)) else { continue };
        let target = match decision {
            Decision::Opt { mutable, slice, .. } => seam::Form::Opt {
                mutable: *mutable,
                slice: *slice,
            },
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => continue,
        };
        let mut plan = receipt(
            tcx,
            parameter,
            parameter.hir_id,
            MechanicalFamily::ArgNullLiteral,
            "null-argument",
            seam::Form::Raw,
            target,
            "None".to_owned(),
            None,
            MechanicalEvidence::default(),
        );
        let calls = raw
            .inventoried_sites()
            .filter(|(key, _, render)| {
                render.call_span.source_callsite() == edit.call_span.source_callsite()
                    && render.callee_local == Some(callee)
                    && key.argument_index == edit.param_index
            })
            .collect::<Vec<_>>();
        let [(key, _, _)] = calls.as_slice() else {
            // This is a source-tracked call carrier, not an inferred literal
            // identity. Refuse a missing/ambiguous compiler join explicitly.
            panic!("Option null-argument MIR identity: {} matches", calls.len());
        };
        plan.obligation.planned.key.owner_class = edit.owner_class;
        plan.owner_class = edit.owner_class;
        plan.obligation.planned.key.subject = MechanicalSubjectKey::Generated {
            owner: edit.bridge.caller,
            key: format!(
                "null-argument:bb{}:s{}:arg{}",
                key.block, key.statement_index, edit.param_index
            ),
            slot_depth: 0,
        };
        plan.obligation.planned.key.site = CanonicalSiteKey {
            owner: edit.bridge.caller,
            location: CanonicalLocation::Mir {
                basic_block: key.block,
                statement_index: key.statement_index,
                terminator: true,
            },
            callee: Some(CanonicalCallee::Local(callee.to_def_id())),
            argument_index: u32::try_from(edit.param_index).ok(),
            slot_depth: 0,
        };
        plan.obligation.planned.owner_path = tcx.def_path_str(edit.bridge.caller.to_def_id());
        plan.obligation.planned.required_arms = super::Arm::C.key().to_owned();
        plan.nullability_fact = "exact-null-argument".to_owned();
        out.push(plan);
    }
    for (node, edit) in body_edits {
        let decision = &mut table
            .entries
            .iter_mut()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
            .expect("Option body source")
            .1;
        match decision {
            Decision::Opt { uses, .. } => uses.push(edit),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => unreachable!("Option body source remains optional"),
        }
    }
    out
}
