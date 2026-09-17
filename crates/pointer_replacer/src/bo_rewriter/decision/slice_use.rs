//! Receipt plans for slice uses owned by the existing raw-boundary adapters.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

use super::{
    super::additive::{FamilyPolicy, FamilyStage},
    Arm, Decision, DecisionTable, SubjectKind, emitability, raw_boundary,
    seam::Form,
};
use crate::bo_rewriter::{
    bridge_receipt::SignatureClassId,
    mechanical_receipt::{
        CanonicalCallee, CanonicalLocation, CanonicalSiteKey, MechanicalEvidence, MechanicalExtent,
        MechanicalFamily, MechanicalMechanism, MechanicalObligationEvent, MechanicalObligationKey,
        MechanicalObligationPlan, MechanicalRetention, MechanicalStage, MechanicalState,
        MechanicalSubjectKey, MechanicalTerminalReason, NegativeWriteEvidence, SliceUseReceiptPlan,
    },
};

fn safe_destination_form(decision: &Decision) -> Option<&'static str> {
    match decision {
        Decision::Ref { mutable } | Decision::InferredRef { mutable, .. } => {
            Some(Form::Ref { mutable: *mutable }.key())
        }
        Decision::Slice { mutable, .. } => Some(Form::Slice { mutable: *mutable }.key()),
        Decision::Opt { mutable, slice, .. } => Some(
            Form::Opt {
                mutable: *mutable,
                slice: *slice,
            }
            .key(),
        ),
        Decision::Box(plan) => Some(match (plan.optional, plan.shape) {
            (false, super::box_facts::BoxShape::Sized) => "box",
            (false, super::box_facts::BoxShape::Slice) => "box-slice",
            (true, super::box_facts::BoxShape::Sized) => "opt-box",
            (true, super::box_facts::BoxShape::Slice) => "opt-box-slice",
        }),
        Decision::NestedSlice {
            mutable,
            inner_mutable,
            ..
        } => Some(
            Form::NestedSlice {
                mutable: *mutable,
                inner_mutable: *inner_mutable,
            }
            .key(),
        ),
        Decision::Cursor { mutable, .. } => Some(Form::Cursor { mutable: *mutable }.key()),
        Decision::Degraded(_) => None,
    }
}

/// A same-form carrier owns the whole copy RHS, including identity pointer
/// casts. Address/projection expressions are different views, not copies.
fn same_form_copy(
    tcx: TyCtxt<'_>,
    subject: &super::Subject,
    observed: &emitability::SliceRawUse,
    source: Form,
    binding_will_be_mutable: bool,
) -> Option<(emitability::UseEdit, bool)> {
    use rustc_hir::{ExprKind, Node};
    use rustc_middle::ty::TyKind;
    let typeck = tcx.typeck(subject.fn_did);
    let mut value = tcx.hir_node(observed.hir_id).expect_expr();
    let TyKind::RawPtr(pointee, _) = typeck.expr_ty(value).kind() else { return None };
    let initializer = loop {
        match tcx.parent_hir_node(value.hir_id) {
            Node::Expr(parent) => match parent.kind {
                ExprKind::Cast(inner, _) if inner.hir_id == value.hir_id => {
                    if !matches!(typeck.expr_ty(parent).kind(), TyKind::RawPtr(target, _) if target == pointee)
                    {
                        return None;
                    }
                    value = parent;
                }
                ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == value.hir_id => {
                    if !matches!(typeck.expr_ty(lhs).kind(), TyKind::RawPtr(target, _) if target == pointee)
                    {
                        return None;
                    }
                    break false;
                }
                _ => return None,
            },
            Node::LetStmt(local) if local.init.is_some_and(|init| init.hir_id == value.hir_id) => {
                if !matches!(typeck.pat_ty(local.pat).kind(), TyKind::RawPtr(target, _) if target == pointee)
                {
                    return None;
                }
                break true;
            }
            _ => return None,
        }
    };
    let name = subject.param_name.as_deref()?;
    let replacement = match source {
        Form::Slice { mutable: false } | Form::Opt { mutable: false, .. } => name.to_owned(),
        Form::Slice { mutable: true } => format!("&mut *{name}"),
        Form::Opt { mutable: true, .. } if subject.mut_binding || binding_will_be_mutable => {
            format!("{name}.as_deref_mut()")
        }
        Form::NestedSlice { .. } | Form::Cursor { .. } => return None,
        Form::Raw | Form::Ref { .. } | Form::Opt { mutable: true, .. } => return None,
    };
    Some((
        emitability::UseEdit {
            span: value.span,
            replacement,
            bridge_kind: "subject-use",
        },
        initializer,
    ))
}

/// The destination owns this complete local initializer; the source must not
/// also materialize a raw alias at the same RHS.
fn cursor_incoming_initializer(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    source: &super::Subject,
    destination: &super::Subject,
    rhs: &rustc_hir::Expr<'_>,
) -> bool {
    use rustc_hir::{ExprKind, Node, PatKind, QPath, def::Res};

    use super::cursor_native::DeliveredBaseProvider;
    let (mutable, plan) = match table
        .entries
        .iter()
        .find(|(subject, _)| {
            subject.fn_did == destination.fn_did && subject.hir_id == destination.hir_id
        })
        .map(|(_, decision)| decision)
    {
        Some(Decision::Cursor { mutable, plan }) => (mutable, plan),
        Some(
            Decision::NestedSlice { .. }
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Degraded(_),
        )
        | None => return false,
    };
    let Some(base) = &plan.delivered_base else { return false };
    let DeliveredBaseProvider::Slice { producer } = &base.provider else { return false };
    if base.binding != source.hir_id
        || base.window_binding != source.hir_id
        || producer.node != (source.fn_did, source.hir_id)
        || (*mutable && !producer.mutable)
        || producer.nullable
        || producer.replacement.is_none()
        || producer.hold_reason.is_some()
        || !matches!(rhs.kind, ExprKind::Path(QPath::Resolved(_, path)) if path.res == Res::Local(source.hir_id))
    {
        return false;
    }
    let Node::LetStmt(local) = tcx.parent_hir_node(rhs.hir_id) else { return false };
    if !matches!(local.pat.kind, PatKind::Binding(_, hir, _, None) if hir == destination.hir_id)
        || !local.init.is_some_and(|init| init.hir_id == rhs.hir_id)
    {
        return false;
    }
    plan.uses.len() == plan.use_hirs.len()
        && plan
            .uses
            .iter()
            .zip(&plan.use_hirs)
            .filter(|(edit, hir)| {
                **hir == rhs.hir_id
                    && edit.span == rhs.span
                    && edit.bridge_kind == "cursor-constructor"
            })
            .count()
            == 1
}

fn shared_to_mut(template: raw_boundary::BridgeTemplate) -> bool {
    use raw_boundary::BridgeTemplate;
    match template {
        BridgeTemplate::VoidFromRefCastMut
        | BridgeTemplate::RefSharedToRawMut
        | BridgeTemplate::SliceToRawMut
        | BridgeTemplate::OptRefToRawMut
        | BridgeTemplate::OptRefToVoidMut
        | BridgeTemplate::VoidFromSliceCastMut
        | BridgeTemplate::OptSliceToVoidMut
        | BridgeTemplate::OptSliceToRawMut => true,
        BridgeTemplate::VoidFromCursorView
        | BridgeTemplate::Depth2NpoConst
        | BridgeTemplate::Depth2NpoMut
        | BridgeTemplate::VoidFromMut
        | BridgeTemplate::VoidFromRef
        | BridgeTemplate::VoidFromMutAsConst
        | BridgeTemplate::VoidFromSlice
        | BridgeTemplate::VoidFromSliceMut
        | BridgeTemplate::OptSliceMutToVoidMut
        | BridgeTemplate::OptSliceToVoidConst
        | BridgeTemplate::RawCastMut
        | BridgeTemplate::RawCastConst
        | BridgeTemplate::TypedRawTemporary
        | BridgeTemplate::RefMutToRawMut
        | BridgeTemplate::RefMutToRawConst
        | BridgeTemplate::RefMutToWritableRawConst
        | BridgeTemplate::SliceMutToWritableRawConst
        | BridgeTemplate::OptRefMutToWritableRawConst
        | BridgeTemplate::OptSliceMutToWritableRawConst
        | BridgeTemplate::RefSharedToRawConst
        | BridgeTemplate::SliceMutToRawMut
        | BridgeTemplate::SliceToRawConst
        | BridgeTemplate::OptRefMutToRawMut
        | BridgeTemplate::OptRefToRawConst
        | BridgeTemplate::OptRefMutToVoidMut
        | BridgeTemplate::OptRefToVoidConst
        | BridgeTemplate::OptSliceMutToVoidMut
        | BridgeTemplate::OptSliceToVoidConst
        | BridgeTemplate::OptSliceToRaw
        | BridgeTemplate::BoxBorrowViewToRaw
        | BridgeTemplate::OptionalBoxBorrowViewToRaw
        | BridgeTemplate::CursorSharedToRawConst
        | BridgeTemplate::CursorMutToRawMut
        | BridgeTemplate::CursorMutToRawConst
        | BridgeTemplate::KnownFreeDrop => false,
    }
}

pub(crate) fn receipt_plans(
    program: &crate::utils::rustc::RustProgram<'_>,
    table: &mut DecisionTable,
    uses: &FxHashMap<(LocalDefId, HirId), emitability::SliceUses>,
    raw: &raw_boundary::RawBoundaryDispositionIndex,
    retention_summaries: &raw_boundary::RetentionSummaries,
    mut_facts: &crate::analyses::borrow_ownership::mutability_facts::MutFacts,
    family_policy: &FamilyPolicy,
) -> Vec<SliceUseReceiptPlan> {
    let tcx = program.tcx;
    let mut plans = Vec::new();
    let mut body_edits = Vec::new();
    for (subject, decision) in &table.entries {
        if !family_policy.enabled_for((subject.fn_did, subject.hir_id), FamilyStage::SliceUse) {
            continue;
        }
        let mut cursor_only = false;
        let source = match decision {
            Decision::Slice { mutable, .. } => Form::Slice { mutable: *mutable },
            Decision::Opt {
                mutable,
                slice: true,
                ..
            } => Form::Opt {
                mutable: *mutable,
                slice: true,
            },
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Opt { slice: false, .. }
            | Decision::Box(_)
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. } => continue,
            Decision::Degraded(record) => match record.reason {
                super::DegradeReason::SliceCursorUse => {
                    cursor_only = true;
                    Form::Raw
                }
                _ => continue,
            },
        };
        let source_form = source.key().to_owned();
        let candidate_form = if cursor_only {
            Form::Slice {
                mutable: subject.mutable,
            }
            .key()
        } else {
            source.key()
        }
        .to_owned();
        let node = (subject.fn_did, subject.hir_id);
        let Some(uses) = uses.get(&node) else { continue };
        let owner_class = SignatureClassId::of(subject.fn_did);
        let slot_depth = u32::from(subject.ptr_depth.saturating_sub(1));
        let mut by_hir = BTreeMap::<u32, Vec<&emitability::SliceRawUse>>::new();
        for use_site in &uses.raw_uses {
            if cursor_only && use_site.source_shape != "cursor" {
                continue;
            }
            by_hir
                .entry(use_site.hir_id.local_id.as_u32())
                .or_default()
                .push(use_site);
        }
        for observations in by_hir.values() {
            let observed = observations[0];
            let mut site = CanonicalSiteKey {
                owner: subject.fn_did,
                location: CanonicalLocation::Hir {
                    owner: observed.hir_id.owner.def_id,
                    item_local_id: observed.hir_id.local_id.as_u32(),
                },
                callee: None,
                argument_index: None,
                slot_depth,
            };
            let mut target = &observed.target;
            let mut target_form_override = None;
            let mut same_form_initializer = None;
            let mut adapter = "-".to_owned();
            let mut retention = MechanicalRetention::None;
            let mut negative_write = NegativeWriteEvidence::NotApplicable;
            let mut mechanism = MechanicalMechanism::SliceRawView;
            let mut reason = None;
            let mut boundary_site = "-".to_owned();
            let mut boundary_evidence = String::new();
            let mut required_arms = table
                .arm_requirements
                .get(&node)
                .copied()
                .unwrap_or_default();
            let mut dependency_classes = table
                .seams
                .interface_dependencies
                .iter()
                .filter_map(|(dependent, dependency)| {
                    (*dependent == owner_class).then_some(*dependency)
                })
                .collect::<BTreeSet<_>>();

            if observed.source_shape == "cursor" {
                reason = Some(MechanicalTerminalReason::Cursor);
                adapter = "cursor-excluded".to_owned();
                boundary_evidence = "raw-pointer-movement;separate-cursor-wave".to_owned();
            } else if observations.iter().any(|other| *other != observed) {
                reason = Some(MechanicalTerminalReason::EvidenceMissing(format!(
                    "slice-use-conflicting-hir-observations:{}",
                    site.receipt_key()
                )));
            } else if let Some(boundary_span) = observed.boundary_span {
                // A duplicated/ambiguous MIR carrier must never select the
                // first disposition merely because its iteration order wins.
                let candidates = raw
                    .inventoried_sites()
                    .filter(|(_, _, render)| {
                        render.node == Some(node)
                            && render.span.source_callsite() == boundary_span.source_callsite()
                    })
                    .collect::<Vec<_>>();
                match candidates.as_slice() {
                    [(key, disposition, render)] => {
                        boundary_site = raw_boundary::site_atom_id(key);
                        site.callee = Some(match render.callee_local {
                            Some(callee) => CanonicalCallee::Local(callee.to_def_id()),
                            None => CanonicalCallee::Foreign(key.callee.path.clone()),
                        });
                        site.argument_index = u32::try_from(key.argument_index).ok();
                        target = &render.target;
                        if !render.target_stays_raw {
                            required_arms.insert(Arm::C);
                            boundary_evidence = "hypothetical-target-stays-raw=false".to_owned();
                            if let Some(callee) = render.callee_local {
                                dependency_classes.insert(SignatureClassId::of(callee));
                                let parameters = table.entries.iter().filter(|(parameter, _)| {
                                    parameter.fn_did == callee
                                        && matches!(parameter.kind, SubjectKind::Param { hir_index } if hir_index == key.argument_index)
                                }).collect::<Vec<_>>();
                                let settled_safe = match parameters.as_slice() {
                                    [(_, decision)] => match decision {
                                        Decision::Ref { .. }
                                        | Decision::InferredRef { .. }
                                        | Decision::Slice { .. }
                                        | Decision::Opt { .. }
                                        | Decision::Box(_)
                                        | Decision::NestedSlice { .. }
                                        | Decision::Cursor { .. } => true,
                                        Decision::Degraded(_) => false,
                                    },
                                    _ => false,
                                };
                                // wave-6a W6A-B1: a safe slice passed at a
                                // settled slice parameter needs no carrier.
                                let zero_syntax_parameter = match parameters.as_slice() {
                                    [(_, decision)] => {
                                        super::slice_local_construction::zero_syntax_slice_pass(
                                            source,
                                            super::seam::form_of(decision),
                                        )
                                    }
                                    _ => None,
                                };
                                let carriers = table
                                    .seams
                                    .edits
                                    .iter()
                                    .filter(|edit| {
                                        edit.owner_class == SignatureClassId::of(callee)
                                            && edit.bridge.caller == subject.fn_did
                                            && edit.param_index == key.argument_index
                                            && edit.span.source_callsite()
                                                == boundary_span.source_callsite()
                                    })
                                    .collect::<Vec<_>>();
                                // wave-6s: a borrowed computed sub-view
                                // (`&mut *p.offset(e)`) coerces into a
                                // converted THIN parameter with no seam of its
                                // own; the subject's element use edit
                                // `&mut p[e]` is its carrier.
                                let thin_parameter = match parameters.as_slice() {
                                    [(_, decision)] => match decision {
                                        Decision::Ref { .. } => true,
                                        Decision::InferredRef { .. }
                                        | Decision::Slice { .. }
                                        | Decision::Opt { .. }
                                        | Decision::Box(_)
                                        | Decision::NestedSlice { .. }
                                        | Decision::Cursor { .. }
                                        | Decision::Degraded(_) => false,
                                    },
                                    _ => false,
                                };
                                let element_view = carriers.is_empty()
                                    && thin_parameter
                                    && uses.computed_argument_views.iter().any(|view| {
                                        view.use_span == observed.span && view.borrowed
                                    });
                                if !settled_safe {
                                    reason = Some(MechanicalTerminalReason::EvidenceMissing(
                                        format!(
                                            "slice-use-existing-c-callee-not-settled-safe:parameters={}",
                                            parameters.len()
                                        ),
                                    ));
                                } else if element_view {
                                    adapter = "computed-suffix-view-element".to_owned();
                                    target_form_override = Some(
                                        Form::Ref {
                                            mutable: subject.mutable,
                                        }
                                        .key()
                                        .to_owned(),
                                    );
                                    boundary_evidence =
                                        "existing-c-thin-parameter:element-view".to_owned();
                                } else if let [carrier] = carriers.as_slice() {
                                    adapter = "owned-existing-c-interface".to_owned();
                                    target_form_override = Some(carrier.expected.key().to_owned());
                                    boundary_evidence = format!(
                                        "existing-c-carrier:expected={};found={}",
                                        carrier.expected.key(),
                                        carrier.found.key()
                                    );
                                } else if carriers.is_empty()
                                    && let Some(expected) = zero_syntax_parameter
                                {
                                    adapter = "owned-existing-c-interface:zero-syntax".to_owned();
                                    target_form_override = Some(expected.key().to_owned());
                                    boundary_evidence = format!(
                                        "existing-c-zero-syntax:expected={};found={}",
                                        expected.key(),
                                        source.key()
                                    );
                                } else {
                                    reason = Some(MechanicalTerminalReason::EvidenceMissing(
                                        format!(
                                            "slice-use-existing-c-interface-carrier-{}:candidates={}",
                                            if carriers.is_empty() {
                                                "unmapped"
                                            } else {
                                                "ambiguous"
                                            },
                                            carriers.len()
                                        ),
                                    ));
                                }
                            } else {
                                reason = Some(MechanicalTerminalReason::EvidenceMissing(
                                    "slice-use-existing-c-interface-callee-unresolved".to_owned(),
                                ));
                            }
                        } else {
                            match disposition {
                                raw_boundary::RawBoundaryDisposition::T1 { template, evidence }
                                | raw_boundary::RawBoundaryDisposition::T2 {
                                    template,
                                    evidence,
                                    ..
                                } => {
                                    adapter = template.key().to_owned();
                                    boundary_evidence = format!("template={template:?};{evidence}");
                                    retention = match disposition {
                                        raw_boundary::RawBoundaryDisposition::T1 { .. } => {
                                            MechanicalRetention::T1
                                        }
                                        raw_boundary::RawBoundaryDisposition::T2 {
                                            waiver_id,
                                            reason,
                                            ..
                                        } => {
                                            boundary_evidence.push_str(&format!(
                                                ";retention-reason={}",
                                                reason.key()
                                            ));
                                            MechanicalRetention::T2 {
                                                waiver_id: (*waiver_id).to_owned(),
                                            }
                                        }
                                        raw_boundary::RawBoundaryDisposition::Blocked {
                                            ..
                                        }
                                        | raw_boundary::RawBoundaryDisposition::OwnedByOtherArm {
                                            ..
                                        } => unreachable!(),
                                    };
                                    let shared_to_mut = shared_to_mut(*template);
                                    if shared_to_mut {
                                        mechanism = MechanicalMechanism::SharedRefToMutRaw;
                                    }
                                    negative_write = match raw.negative_write_evidence(key) {
                                        Some(
                                            raw_boundary::NegativeWriteEvidence::FosterImmutable,
                                        ) => NegativeWriteEvidence::FosterImmutable,
                                        Some(raw_boundary::NegativeWriteEvidence::LibcReadOnly) => {
                                            NegativeWriteEvidence::LibcReadOnly(evidence.clone())
                                        }
                                        None if shared_to_mut => {
                                            reason = Some(
                                                MechanicalTerminalReason::RbNegativeWriteAbsent,
                                            );
                                            NegativeWriteEvidence::Missing
                                        }
                                        None => NegativeWriteEvidence::NotApplicable,
                                    };
                                }
                                raw_boundary::RawBoundaryDisposition::Blocked {
                                    reason: blocked,
                                    detail,
                                } => {
                                    boundary_evidence = format!(
                                        "boundary-reason={};boundary-detail={detail}",
                                        blocked.key()
                                    );
                                    reason = Some(match blocked {
                                        raw_boundary::RawBoundaryBlockReason::PositiveRetention => {
                                            retention = MechanicalRetention::PositiveRetention;
                                            MechanicalTerminalReason::PositiveRetention
                                        }
                                        raw_boundary::RawBoundaryBlockReason::SharedToMut => {
                                            negative_write = NegativeWriteEvidence::Missing;
                                            MechanicalTerminalReason::RbNegativeWriteAbsent
                                        }
                                        blocked => MechanicalTerminalReason::EvidenceMissing(
                                            format!("{}:{detail}", blocked.key()),
                                        ),
                                    });
                                }
                                raw_boundary::RawBoundaryDisposition::OwnedByOtherArm {
                                    owner,
                                    reason,
                                } => {
                                    adapter = format!("owned-by-{owner}:{reason}");
                                    boundary_evidence =
                                        format!("boundary-owner={owner};boundary-reason={reason}");
                                }
                            }
                        }
                    }
                    candidates => {
                        reason = Some(MechanicalTerminalReason::EvidenceMissing(format!(
                            "slice-use-boundary-{}:candidates={}:hir={}:span={}..{}",
                            if candidates.is_empty() {
                                "unmapped"
                            } else {
                                "ambiguous"
                            },
                            candidates.len(),
                            observed.hir_id.local_id.as_u32(),
                            boundary_span.lo().0,
                            boundary_span.hi().0,
                        )));
                    }
                }
            } else if observed.source_shape == "pointer-distance" && observed.contract.is_some() {
                adapter = match source {
                    Form::Opt { slice: true, .. } => {
                        let name = subject
                            .param_name
                            .as_deref()
                            .expect("named optional distance operand");
                        // This edit replaces the binding beneath any existing cast.
                        // Both map_or arms must retain that binding's pointee;
                        // the surrounding source cast still supplies the sink type.
                        let expression = tcx.hir_node(observed.hir_id).expect_expr();
                        let mut binding_target = raw_boundary::raw_target_type(
                            tcx,
                            tcx.typeck(subject.fn_did).expr_ty(expression),
                        )
                        .expect("raw optional distance binding");
                        binding_target.mutability = raw_boundary::RawMutability::Const;
                        binding_target.rendered = format!("*const {}", binding_target.pointee);
                        let replacement = raw_boundary::pair_raw_view_expression(
                            Some(decision),
                            &binding_target,
                            name,
                            "bare-local",
                        )
                        .expect("optional slice has a const raw view");
                        body_edits.push((
                            node,
                            emitability::UseEdit {
                                span: observed.span,
                                replacement,
                                bridge_kind: "subject-use",
                            },
                        ));
                        "optional-slice-const-view"
                    }
                    Form::Slice { .. } => "slice-as-ptr",
                    Form::NestedSlice { .. }
                    | Form::Cursor { .. }
                    | Form::Raw
                    | Form::Ref { .. }
                    | Form::Opt { slice: false, .. } => {
                        unreachable!("slice source selected above")
                    }
                }
                .to_owned();
                retention = MechanicalRetention::T1;
                boundary_evidence = observed
                    .contract
                    .clone()
                    .expect("checked intrinsic contract");
            } else if matches!(observed.source_shape, "body-copy" | "field-store") {
                let destination = observed.destination.and_then(|binding| {
                    table.entries.iter().find(|(target, _)| {
                        target.fn_did == subject.fn_did && target.hir_id == binding
                    })
                });
                // wave-6s: a computed sub-view copied into the destination
                // (`let q = &*p.offset(e) as *const T`, `q = p.offset(e)`).
                let computed = uses
                    .computed_argument_views
                    .iter()
                    .find(|view| !view.argument && view.use_span == observed.span);
                let source_mutable_view = match source {
                    Form::Slice { mutable } => mutable,
                    Form::Opt { .. }
                    | Form::NestedSlice { .. }
                    | Form::Cursor { .. }
                    | Form::Raw
                    | Form::Ref { .. } => false,
                };
                if let Some(view) = computed
                    && let Some((_, decision)) = destination
                    && let Some(target_form) = safe_destination_form(decision)
                {
                    // The destination's own form picks the view: a thin
                    // reference takes the checked element, a slice the suffix.
                    target_form_override = Some(target_form.to_owned());
                    let name = subject.param_name.as_deref().expect("named slice use");
                    let rendered = match decision {
                        Decision::Ref { mutable } | Decision::InferredRef { mutable, .. }
                            if !*mutable || source_mutable_view =>
                        {
                            let amp = if *mutable { "&mut " } else { "&" };
                            adapter = "computed-element-copy".to_owned();
                            Some(format!("{amp}({name})[{}]", view.index))
                        }
                        Decision::Slice { mutable, .. } if !*mutable || source_mutable_view => {
                            let amp = if *mutable { "&mut " } else { "&" };
                            adapter = "computed-suffix-copy".to_owned();
                            Some(format!("{amp}({name})[{}..]", view.index))
                        }
                        Decision::Ref { .. }
                        | Decision::InferredRef { .. }
                        | Decision::Slice { .. }
                        | Decision::Opt { .. }
                        | Decision::Box(_)
                        | Decision::NestedSlice { .. }
                        | Decision::Cursor { .. }
                        | Decision::Degraded(_) => None,
                    };
                    match rendered {
                        Some(replacement) => {
                            boundary_evidence = "computed-view-copy-checked-index".to_owned();
                            // When the destination's own initializer adapter
                            // (the identity-cast peel) already owns the whole
                            // value, the view replaces the borrow it keeps.
                            let span = match view.borrow_span {
                                Some(borrow)
                                    if table
                                        .seams
                                        .body_edits
                                        .iter()
                                        .any(|edit| edit.span == view.argument_span) =>
                                {
                                    borrow
                                }
                                _ => view.argument_span,
                            };
                            body_edits.push((
                                node,
                                emitability::UseEdit {
                                    span,
                                    replacement,
                                    bridge_kind: "subject-use",
                                },
                            ));
                        }
                        None => {
                            reason = Some(MechanicalTerminalReason::EvidenceMissing(format!(
                                "computed-view-destination-unbuilt:{target_form}"
                            )));
                        }
                    }
                } else if let Some((destination, target_form)) =
                    destination.and_then(|(subject, decision)| {
                        safe_destination_form(decision).map(|form| (subject, form))
                    })
                {
                    target_form_override = Some(target_form.to_owned());
                    let mut rhs = tcx.hir_node(observed.hir_id).expect_expr();
                    while let rustc_hir::Node::Expr(parent) = tcx.parent_hir_node(rhs.hir_id)
                        && matches!(parent.kind, rustc_hir::ExprKind::Cast(inner, _) if inner.hir_id == rhs.hir_id)
                    {
                        rhs = parent;
                    }
                    let wrapping = table
                        .option_receipts
                        .iter()
                        .filter(|receipt| {
                            receipt.source_form == source.key()
                                && receipt.target_form == target_form
                                && receipt.obligation.planned.key.subject
                                    == MechanicalSubjectKey::Local {
                                        owner: destination.fn_did,
                                        mir_local: destination.local.as_u32(),
                                        slot_depth: u32::from(
                                            destination.ptr_depth.saturating_sub(1),
                                        ),
                                    }
                                && receipt.obligation.planned.key.site.location
                                    == CanonicalLocation::Hir {
                                        owner: rhs.hir_id.owner.def_id,
                                        item_local_id: rhs.hir_id.local_id.as_u32(),
                                    }
                                && matches!(
                                    receipt.operation.as_str(),
                                    "nullable-construction" | "nullable-assignment"
                                )
                        })
                        .collect::<Vec<_>>();
                    if matches!(source, Form::Slice { mutable } if !destination.mutable || mutable)
                        && cursor_incoming_initializer(tcx, table, subject, destination, rhs)
                    {
                        adapter = "owned-cursor-incoming-destination".to_owned();
                        boundary_evidence = "destination-owned-cursor-initializer".to_owned();
                        dependency_classes.insert(SignatureClassId::of(destination.fn_did));
                    } else if super::construction_values::owns_initializer(
                        tcx,
                        table,
                        subject,
                        destination,
                        rhs,
                    ) {
                        adapter = "owned-copy-value-destination".to_owned();
                        boundary_evidence = "destination-owned-checked-element-copy".to_owned();
                        dependency_classes.insert(SignatureClassId::of(destination.fn_did));
                    } else if target_form != source.key()
                        && let [carrier] = wrapping.as_slice()
                    {
                        // Item 4 owns Some(view) at the destination. Reuse its
                        // exact RHS carrier; never add a second raw-alias edit.
                        adapter = "owned-option-wrapping-destination".to_owned();
                        reason = carrier.obligation.intended_terminal_reason.clone();
                        boundary_evidence = "destination-owned-option-value".to_owned();
                    } else if target_form == source.key()
                        && let Some((edit, initializer)) = same_form_copy(
                            tcx,
                            subject,
                            observed,
                            source,
                            table.option_mut_bindings.contains(&node),
                        )
                    {
                        adapter = "body-slice-same-form".to_owned();
                        boundary_evidence = "same-form-safe-copy-or-reborrow".to_owned();
                        if initializer {
                            same_form_initializer = Some((destination.fn_did, destination.hir_id));
                        }
                        body_edits.push((node, edit));
                    } else {
                        reason = Some(MechanicalTerminalReason::SliceUseDestinationUnbuilt(
                            target_form.to_owned(),
                        ));
                    }
                } else {
                    let destination_retention = match subject.kind {
                        SubjectKind::Local => destination.map(|(destination, _)| {
                            retention_summaries.copied_local_retention(
                                program,
                                subject.fn_did,
                                destination.local,
                            )
                        }),
                        SubjectKind::Param { .. } => None,
                    };
                    let destination_retains = matches!(
                        destination_retention,
                        Some(raw_boundary::RetentionVerdict::Retains { .. })
                    );
                    let positive = observed.source_shape == "field-store"
                        || destination_retains
                        || match subject.kind {
                            SubjectKind::Param { hir_index } => matches!(
                                retention_summaries.get(subject.fn_did, hir_index),
                                Some(raw_boundary::RetentionVerdict::Retains { .. })
                            ),
                            SubjectKind::Local => false,
                        };
                    let source_mutable = match source {
                        Form::Ref { mutable }
                        | Form::Slice { mutable }
                        | Form::Opt { mutable, .. } => mutable,
                        Form::NestedSlice { .. } | Form::Cursor { .. } => false,
                        Form::Raw => false,
                    };
                    let read_only = !mut_facts.is_defaulted(subject.fn_did, subject.local)
                        && !mut_facts.is_mutable(subject.fn_did, subject.local);
                    if positive {
                        reason = Some(MechanicalTerminalReason::PositiveRetention);
                        retention = MechanicalRetention::PositiveRetention;
                        boundary_evidence = if destination_retains {
                            "copied-local-destination-retains"
                        } else {
                            "pointer-stored-or-owner-parameter-retains"
                        }
                        .to_owned();
                    } else if matches!(subject.kind, SubjectKind::Local)
                        && !matches!(
                            destination_retention,
                            Some(raw_boundary::RetentionVerdict::Unknown { .. })
                        )
                    {
                        reason = Some(MechanicalTerminalReason::EvidenceMissing(
                            "slice-use-local-destination-retention-unavailable".to_owned(),
                        ));
                    } else if !source_mutable && !read_only {
                        reason = Some(MechanicalTerminalReason::RbNegativeWriteAbsent);
                        negative_write = NegativeWriteEvidence::Missing;
                    } else {
                        let name = subject.param_name.as_deref().expect("named slice use");
                        // wave-6s: the raw alias of a computed view is the
                        // suffix's pointer, replacing the whole copied value.
                        let (alias, alias_span) = match computed {
                            Some(view) => (
                                format!(
                                    "(&{}({name})[{}..])",
                                    if source_mutable_view { "mut " } else { "" },
                                    view.index
                                ),
                                view.argument_span,
                            ),
                            None => (name.to_owned(), observed.span),
                        };
                        let name = alias.as_str();
                        let replacement = raw_boundary::pair_raw_view_expression(Some(decision), target, name, "bare-local")
                            .or_else(|| {
                                (read_only && target.mutability == raw_boundary::RawMutability::Mut).then(|| match source {
                                    Form::Slice { .. } => format!("{name}.as_ptr().cast_mut()"),
                                    Form::Opt { slice: true, .. } => format!("{name}.as_deref().map_or(core::ptr::null_mut::<{}>(), |slice| slice.as_ptr().cast_mut())", target.pointee),
                                    Form::NestedSlice { .. } | Form::Cursor { .. } | Form::Raw | Form::Ref { .. } | Form::Opt { slice: false, .. } => unreachable!("slice source selected above"),
                                })
                            });
                        if let Some(replacement) = replacement {
                            // The raw alias may remain live across later parent
                            // accesses in this body. A no-escape function summary
                            // does not license T1 for that schedule.
                            retention = MechanicalRetention::T2 {
                                waiver_id:
                                    crate::bo_rewriter::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID
                                        .to_owned(),
                            };
                            boundary_evidence = "body-local-raw-alias-schedule-unproved".to_owned();
                            if !source_mutable {
                                negative_write = NegativeWriteEvidence::FosterImmutable;
                                if target.mutability == raw_boundary::RawMutability::Mut {
                                    mechanism = MechanicalMechanism::SharedRefToMutRaw;
                                }
                            }
                            adapter = if computed.is_some() {
                                "computed-suffix-raw-view"
                            } else {
                                "body-slice-raw-view"
                            }
                            .to_owned();
                            body_edits.push((
                                node,
                                emitability::UseEdit {
                                    span: alias_span,
                                    replacement,
                                    bridge_kind: "subject-use",
                                },
                            ));
                        } else {
                            reason = Some(MechanicalTerminalReason::EvidenceMissing(
                                "slice-use-body-template-unavailable".to_owned(),
                            ));
                        }
                    }
                }
            } else if observed.source_shape == "raw-discard"
                && observed.target.mutability == raw_boundary::RawMutability::Const
                && matches!(source, Form::Slice { .. })
            {
                adapter = "slice-as-ptr".to_owned();
                retention = MechanicalRetention::T1;
                boundary_evidence = "raw-value-discarded".to_owned();
            } else {
                reason = Some(MechanicalTerminalReason::EvidenceMissing(
                    "slice-use-without-boundary-or-const-discard".to_owned(),
                ));
            }
            let intended_terminal_state = if reason.is_some() {
                MechanicalState::HeldNonmechanical
            } else {
                MechanicalState::Applied
            };
            let target_form = target_form_override.unwrap_or_else(|| target.rendered.clone());
            let access_mutability = match target.mutability {
                raw_boundary::RawMutability::Const => "const",
                raw_boundary::RawMutability::Mut => "mut",
            }
            .to_owned();
            let contract_extent = table.contract_extent_promotions.get(&node).cloned();
            let event = MechanicalObligationEvent {
                key: MechanicalObligationKey {
                    owner_class,
                    subject: MechanicalSubjectKey::Local {
                        owner: subject.fn_did,
                        mir_local: subject.local.as_u32(),
                        slot_depth,
                    },
                    site: site.clone(),
                    family: MechanicalFamily::SliceUseUnsupported,
                },
                owner_path: tcx.def_path_str(subject.fn_did.to_def_id()),
                prior_reason: "slice-use-unsupported".to_owned(),
                expected_form: target_form.clone(),
                found_form: source_form.clone(),
                argument_kind: if observed.boundary_span.is_some() {
                    if observed.native_element {
                        "call-argument-native-element"
                    } else {
                        "call-argument"
                    }
                } else {
                    "raw-discard"
                }
                .to_owned(),
                source_shape: observed.source_shape.to_owned(),
                required_arms: required_arms.render(),
                mechanism,
                composition_parent: None,
                dependency_classes,
                evidence: MechanicalEvidence {
                    extent: contract_extent
                        .as_ref()
                        .map_or(MechanicalExtent::None, |promotion| {
                            promotion.mechanical_extent()
                        }),
                    retention: retention.clone(),
                    negative_write,
                    ..MechanicalEvidence::default()
                },
                stage: MechanicalStage::Plan,
                state: MechanicalState::Planned,
                terminal_reason: None,
            };
            plans.push(SliceUseReceiptPlan {
                obligation: MechanicalObligationPlan {
                    planned: event,
                    intended_terminal_state,
                    intended_terminal_reason: reason,
                },
                use_site: site,
                source_form: source_form.clone(),
                candidate_form: candidate_form.clone(),
                same_form_initializer,
                target_form,
                access_mutability,
                adapter,
                boundary_site,
                boundary_evidence,
                retention,
                owner_class,
                contract_extent,
            });
        }
    }
    for (node, edit) in body_edits {
        let (_, decision) = table
            .entries
            .iter_mut()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
            .expect("body view source");
        match decision {
            Decision::Slice { uses, .. }
            | Decision::Opt {
                slice: true, uses, ..
            } => uses.push(edit),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Opt { slice: false, .. }
            | Decision::Box(_)
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => unreachable!("body view source remains slice"),
        }
    }
    plans.sort_by_key(|plan| plan.obligation.planned.key.receipt_key());
    plans
}
