//! Native borrowed call results consumed directly by raw call arguments.
//! The expression identity is independent of the declaration subject ledger.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId,
    def_id::LocalDefId,
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::{
    mir::Local,
    ty::{TyCtxt, TyKind},
};
use rustc_span::Span;

use super::{
    DecisionTable, SubjectKind,
    lifetime::FnSignatureSlot,
    raw_boundary::{
        self, BridgeTemplate, NegativeWriteEvidence, RawBoundaryBlockReason, RawBoundarySiteFacts,
        RawBoundarySiteKey, RawTargetType, RetentionSummaries, RetentionVerdict,
    },
    return_interface::ReturnInterface,
    seam::{self, Form, GlueSpec},
};
use crate::{
    analyses::borrow_ownership::mutability_facts::MutFacts,
    bo_rewriter::bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, BridgeSitePlan,
        RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OutboundExpressionPlan {
    pub(crate) key: RawBoundarySiteKey,
    pub(crate) caller: LocalDefId,
    pub(crate) argument_hir: HirId,
    pub(crate) argument_span: Span,
    pub(crate) call_span: Span,
    pub(crate) source_callee: LocalDefId,
    pub(crate) source_interface: ReturnInterface,
    pub(crate) sink_callee: BridgeCalleeId,
    pub(crate) target: RawTargetType,
    pub(crate) retention: RetentionVerdict,
    pub(crate) tier: BridgeRetentionTier,
    pub(crate) waiver_id: Option<&'static str>,
    pub(crate) negative_write: Option<NegativeWriteEvidence>,
    pub(crate) template: BridgeTemplate,
    pub(crate) spec: GlueSpec,
    pub(crate) original_expression: String,
    pub(crate) temporary: String,
    pub(crate) mutable_temporary: bool,
    view: String,
}

impl OutboundExpressionPlan {
    pub(crate) fn owner_class(&self) -> SignatureClassId {
        SignatureClassId::of(self.source_callee)
    }

    /// The changed return producer owns this syntax even when the caller's
    /// own declaration class is retired. Its return-origin atom closure is
    /// applied before this normalized class selection reaches either consumer.
    pub(crate) fn active(&self, classes: &BTreeSet<SignatureClassId>) -> bool {
        !classes.contains(&self.owner_class())
    }

    pub(crate) fn bridge(&self) -> BridgeSitePlan {
        BridgeSitePlan {
            caller: self.caller,
            callee: self.sink_callee.clone(),
            arm: "c".into(),
            position: format!("arg{}", self.key.argument_index),
            bridge_kind: "outbound-native-return-argument".into(),
            expected_form: Form::Raw.key().into(),
            found_form: self.source_interface.form.key().into(),
            argument_kind: "raw-expr".into(),
            extent: BridgeExtentKind::None,
            retention: self.tier,
            waiver_id: self.waiver_id.map(str::to_owned),
            unsafe_context: None,
        }
    }

    /// The input is the inner call after its argument adapters. Binding that
    /// result once inside the original argument preserves call evaluation order.
    pub(crate) fn render(&self, adapted_call: &str) -> String {
        format!(
            "{{ let {}{}: {} = ({adapted_call}); ({}) as {} }}",
            if self.mutable_temporary { "mut " } else { "" },
            self.temporary,
            self.source_interface.temporary_type(),
            self.view,
            self.target.rendered
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum OutboundExpressionFailure {
    ArgumentIdentityAmbiguous,
    NativeLifetimeUnavailable,
    NativeLifetimeDrift,
    OriginalExpressionUnavailable,
    SourcePointeeMismatch,
    TargetPointeeMismatch,
    Depth2StorageUnbuilt,
    CallCarrierCompositionUnbuilt,
    ForeignCarrierUnbuilt,
    SinkInputInterfaceUnavailable,
    RetentionSummaryUnavailable,
    PositiveRetention,
    RetentionCertificateInvalid,
    Template(RawBoundaryBlockReason),
    DuplicateSite,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OutboundExpressionUnavailable {
    pub(crate) key: RawBoundarySiteKey,
    pub(crate) caller: LocalDefId,
    pub(crate) argument_hir: HirId,
    pub(crate) argument_span: Span,
    pub(crate) call_span: Span,
    pub(crate) source_callee: LocalDefId,
    pub(crate) source_interface: ReturnInterface,
    pub(crate) sink_callee: BridgeCalleeId,
    pub(crate) target: RawTargetType,
    pub(crate) reason: OutboundExpressionFailure,
    pub(crate) retention: Option<RetentionVerdict>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct OutboundExpressionPlans {
    pub(crate) plans: BTreeMap<RawBoundarySiteKey, OutboundExpressionPlan>,
    pub(crate) unavailable: BTreeMap<RawBoundarySiteKey, OutboundExpressionUnavailable>,
}

#[derive(Clone, Copy)]
struct NativeCall {
    hir: HirId,
    callee: LocalDefId,
}

struct NativeCalls<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    table: &'a DecisionTable,
    calls: FxHashMap<Span, Vec<NativeCall>>,
}

impl<'tcx> Visitor<'tcx> for NativeCalls<'_, 'tcx> {
    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, _) = expression.kind
            && let TyKind::FnDef(definition, _) = *self
                .tcx
                .typeck(expression.hir_id.owner.def_id)
                .expr_ty(callee)
                .kind()
            && let Some(definition) = definition.as_local()
            && self
                .table
                .return_interfaces
                .functions
                .contains_key(&definition)
        {
            self.calls
                .entry(expression.span)
                .or_default()
                .push(NativeCall {
                    hir: expression.hir_id,
                    callee: definition,
                });
        }
        walk_expr(self, expression);
    }
}

fn call_carrier_owns(table: &DecisionTable, spans: &[Span]) -> bool {
    table
        .seams
        .a5_raw_calls
        .iter()
        .any(|call| spans.contains(&call.call_span))
        || table
            .seams
            .pair_raw_calls
            .iter()
            .any(|call| spans.contains(&call.call_span))
        || table
            .c9_marks
            .iter()
            .any(|mark| spans.contains(&mark.call_span))
}

pub(crate) fn plan(
    program: &RustProgram<'_>,
    table: &DecisionTable,
    facts: &RawBoundarySiteFacts,
    retention: &RetentionSummaries,
    mut_facts: &MutFacts,
) -> OutboundExpressionPlans {
    let tcx = program.tcx;
    let mut out = OutboundExpressionPlans::default();
    for &caller in &program.functions {
        let caller_path = tcx.def_path_str(caller.to_def_id());
        let sites = facts
            .sites
            .iter()
            .filter(|site| {
                site.key.caller == caller_path
                    && site.node.is_none()
                    && site.source_shape == "raw-expr"
            })
            .collect::<Vec<_>>();
        if sites.is_empty() {
            continue;
        }
        let mut originals = NativeCalls {
            tcx,
            table,
            calls: FxHashMap::default(),
        };
        originals.visit_expr(tcx.hir_body_owned_by(caller).value);
        for site in sites {
            let Some(calls) = originals.calls.get(&site.source_span) else { continue };
            let source = calls[0];
            let interface = &table.return_interfaces.functions[&source.callee];
            if interface.form == Form::Raw {
                continue;
            }
            let sink_callee = site.callee_local.map_or_else(
                || BridgeCalleeId::Foreign(site.key.callee.path.clone()),
                BridgeCalleeId::Local,
            );
            if let Some(callee) = site.callee_local
                && table.entries.iter().find(|(subject, _)| subject.fn_did == callee
                    && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == site.key.argument_index))
                    .is_some_and(|(_, decision)| seam::form_of(decision) != Form::Raw)
            {
                // A currently safe destination belongs to its existing call
                // adapter and input-form twin. This plan cannot raw-graft it.
                continue;
            }
            let unavailable = |reason, evidence| OutboundExpressionUnavailable {
                key: site.key.clone(),
                caller,
                argument_hir: source.hir,
                argument_span: site.source_span,
                call_span: site.call_span,
                source_callee: source.callee,
                source_interface: interface.clone(),
                sink_callee: sink_callee.clone(),
                target: site.target.clone(),
                reason,
                retention: evidence,
            };
            let build = || -> Result<OutboundExpressionPlan, (OutboundExpressionFailure, Option<RetentionVerdict>)> {
                let fail = |reason| (reason, None);
                if calls.len() != 1 {
                    return Err(fail(OutboundExpressionFailure::ArgumentIdentityAmbiguous));
                }
                let function = table.lifetime_plan.function(source.callee)
                    .ok_or_else(|| fail(OutboundExpressionFailure::NativeLifetimeUnavailable))?;
                if function.lifetime_for(FnSignatureSlot::RETURN) != Some(interface.lifetime.as_str())
                    || function.digest() != interface.lifetime_plan_digest
                {
                    return Err(fail(OutboundExpressionFailure::NativeLifetimeDrift));
                }
                let original_expression = tcx.sess.source_map().span_to_snippet(site.source_span)
                    .map_err(|_| fail(OutboundExpressionFailure::OriginalExpressionUnavailable))?;
                let expression = tcx.hir_node(source.hir).expect_expr();
                let source_type = raw_boundary::raw_target_type(tcx, tcx.typeck(caller).expr_ty(expression));
                if source_type.as_ref().is_none_or(|source| source.pointee != interface.pointee) {
                    return Err(fail(OutboundExpressionFailure::SourcePointeeMismatch));
                }
                if site.target.depth2.is_some() {
                    return Err(fail(OutboundExpressionFailure::Depth2StorageUnbuilt));
                }
                if site.target.pointee != interface.pointee && !site.target.is_void_pointee() {
                    return Err(fail(OutboundExpressionFailure::TargetPointeeMismatch));
                }
                if call_carrier_owns(table, &[site.source_span, site.call_span]) {
                    return Err(fail(OutboundExpressionFailure::CallCarrierCompositionUnbuilt));
                }
                let Some(callee) = site.callee_local else {
                    return Err(fail(OutboundExpressionFailure::ForeignCarrierUnbuilt));
                };
                if table.input_interfaces.parameter_forms.get(&(callee, site.key.argument_index)) != Some(&Form::Raw) {
                    return Err(fail(OutboundExpressionFailure::SinkInputInterfaceUnavailable));
                }
                let evidence = retention.get(callee, site.key.argument_index).cloned()
                    .ok_or_else(|| fail(OutboundExpressionFailure::RetentionSummaryUnavailable))?;
                let local = Local::from_usize(site.key.argument_index + 1);
                let negative_write = (!mut_facts.is_defaulted(callee, local)
                    && !mut_facts.is_mutable(callee, local)).then_some(NegativeWriteEvidence::FosterImmutable);
                let source_form = seam::decision_for_safe_form(interface.form)
                    .ok_or_else(|| (OutboundExpressionFailure::Template(RawBoundaryBlockReason::TemplateUnavailable), Some(evidence.clone())))?;
                // R-B precedes the retention tier; T2 cannot supply missing
                // permission for a shared source at a writing raw position.
                let template = raw_boundary::template_for(&source_form, &site.target, None, negative_write.is_some())
                    .map_err(|reason| (OutboundExpressionFailure::Template(reason), Some(evidence.clone())))?;
                let (tier, waiver_id) = match &evidence {
                    RetentionVerdict::NoRetain { certificate } => {
                        retention.verify_certificate(callee, site.key.argument_index, certificate)
                            .map_err(|_| (OutboundExpressionFailure::RetentionCertificateInvalid, Some(evidence.clone())))?;
                        (BridgeRetentionTier::T1, None)
                    }
                    RetentionVerdict::Unknown { .. } => (BridgeRetentionTier::T2, Some(RAW_BOUNDARY_T2_WAIVER_ID)),
                    RetentionVerdict::Retains { .. } => return Err((OutboundExpressionFailure::PositiveRetention, Some(evidence))),
                };
                let spec = GlueSpec::raw_boundary_target(template, &site.target, false, true);
                let temporary = format!("__crat_outbound_return_{}_{}", caller.local_def_index.as_u32(), source.hir.local_id.as_u32());
                let view = spec.render(&temporary).ok_or_else(|| (
                    OutboundExpressionFailure::Template(RawBoundaryBlockReason::TemplateUnavailable), Some(evidence.clone())))?;
                let mutable_temporary = matches!(interface.form, Form::Opt { mutable: true, .. });
                Ok(OutboundExpressionPlan {
                    key: site.key.clone(), caller, argument_hir: source.hir,
                    argument_span: site.source_span, call_span: site.call_span,
                    source_callee: source.callee, source_interface: interface.clone(), sink_callee: sink_callee.clone(),
                    target: site.target.clone(), retention: evidence, tier, waiver_id, negative_write,
                    template, spec, original_expression, temporary, mutable_temporary, view,
                })
            };
            if out.plans.contains_key(&site.key) || out.unavailable.contains_key(&site.key) {
                out.plans.remove(&site.key);
                out.unavailable.insert(
                    site.key.clone(),
                    unavailable(OutboundExpressionFailure::DuplicateSite, None),
                );
            } else {
                match build() {
                    Ok(plan) => {
                        out.plans.insert(site.key.clone(), plan);
                    }
                    Err((reason, evidence)) => {
                        out.unavailable
                            .insert(site.key.clone(), unavailable(reason, evidence));
                    }
                }
            }
        }
    }
    out
}
