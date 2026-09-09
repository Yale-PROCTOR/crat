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
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::Span;

use super::{
    DecisionTable, SubjectKind,
    lifetime::FnSignatureSlot,
    raw_boundary::{
        self, BridgeTemplate, NegativeWriteEvidence, RawBoundaryBlockReason, RawBoundarySiteFacts,
        RawBoundarySiteKey, RawTargetType, RetentionSummaries, RetentionVerdict,
        ReturnedChildPermissionFailure,
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
    ChildPermission(ReturnedChildPermissionFailure),
    Template(RawBoundaryBlockReason),
    DuplicateSite,
    /// The argument CONTAINS a form-changed native call instead of being one —
    /// a cast, a projection or arithmetic wrapped around it. The carrier for
    /// that shape is not built, and the site must be counted as held rather
    /// than passed over: passing over it leaves the boundary unadapted with
    /// nothing in the ledger to show for it.
    NestedNativeCarrierUnbuilt,
}

impl OutboundExpressionFailure {
    /// The outbound alias-permission gate is the one hold whose reason the
    /// class-site ledger names in full: it reports an emitted write reaching
    /// memory through a shared view of a safe subject. Every other failure
    /// keeps the debug-rendered identity its consumers already read.
    pub(crate) fn alias_permission_reason(&self) -> Option<&'static str> {
        matches!(self, Self::ChildPermission(_))
            .then_some("outbound-alias-permission:write-through-shared-view")
    }
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

/// How deep the sink's return type is walked before the answer is conceded.
const RETURN_CARRIER_WALK_DEPTH: u32 = 6;

/// A conservative compile-time walk of the sink's return type. A sink that
/// cannot return a pointer has no returned child at all, so the returned-child
/// permission and its writable carrier have no premise at that site and the
/// ordinary outgoing view stands; whether the callee writes through the
/// argument itself remains the existing negative-write evidence's question.
///
/// Only the scalar kinds that provably carry no pointer answer `false`.
/// Aggregates are walked field-wise through every variant, and everything
/// opaque, generic or past the depth budget is treated as pointer-carrying:
/// the walk fails closed.
/// The target pointer's width in bits, which is what an integer return has to
/// reach before it can carry a whole address.
fn pointer_bits(tcx: TyCtxt<'_>) -> u64 {
    tcx.data_layout.pointer_size.bits()
}

fn return_may_carry_pointer<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: u32) -> bool {
    if depth == 0 {
        return true;
    }
    match ty.kind() {
        // An integer at least as wide as the target pointer can hand the caller
        // a whole address, and a pointer reconstructed from it inherits the
        // permission the outgoing view created, so it IS a returned-child
        // carrier (addendum 256(2)). `isize`/`usize` have no fixed width here
        // and are pointer-width by definition. Narrower integers cannot hold an
        // address; reconstruction from partial values stays outside the
        // fragment.
        TyKind::Int(int) => int.bit_width().is_none_or(|bits| bits >= pointer_bits(tcx)),
        TyKind::Uint(uint) => uint
            .bit_width()
            .is_none_or(|bits| bits >= pointer_bits(tcx)),
        TyKind::Bool | TyKind::Char | TyKind::Float(_) | TyKind::Never => false,
        TyKind::Tuple(fields) => fields
            .iter()
            .any(|field| return_may_carry_pointer(tcx, field, depth - 1)),
        TyKind::Array(inner, _) | TyKind::Slice(inner) => {
            return_may_carry_pointer(tcx, *inner, depth - 1)
        }
        // A box owns its pointer, so it is a carrier without a field walk.
        TyKind::Adt(definition, arguments) if !definition.is_box() => definition
            .all_fields()
            .any(|field| return_may_carry_pointer(tcx, field.ty(tcx, arguments), depth - 1)),
        _ => true,
    }
}

/// The one form-changed native call strictly inside `argument`, when the
/// argument is not itself that call. Several such calls, or none, answer
/// `None`: the first is ambiguous and the second has nothing to adapt.
fn nested_native_source(
    originals: &NativeCalls<'_, '_>,
    table: &DecisionTable,
    argument: Span,
) -> Option<NativeCall> {
    let mut found = None;
    for (span, calls) in &originals.calls {
        if *span == argument || !argument.contains(*span) {
            continue;
        }
        for call in calls {
            if table.return_interfaces.functions[&call.callee].form == Form::Raw {
                continue;
            }
            if found.is_some() {
                return None;
            }
            found = Some(*call);
        }
    }
    found
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
            let Some(calls) = originals.calls.get(&site.source_span) else {
                if let Some(nested) = nested_native_source(&originals, table, site.source_span) {
                    out.unavailable.insert(
                        site.key.clone(),
                        OutboundExpressionUnavailable {
                            key: site.key.clone(),
                            caller,
                            argument_hir: nested.hir,
                            argument_span: site.source_span,
                            call_span: site.call_span,
                            source_callee: nested.callee,
                            source_interface: table.return_interfaces.functions[&nested.callee]
                                .clone(),
                            sink_callee: site.callee_local.map_or_else(
                                || BridgeCalleeId::Foreign(site.key.callee.path.clone()),
                                BridgeCalleeId::Local,
                            ),
                            target: site.target.clone(),
                            reason: OutboundExpressionFailure::NestedNativeCarrierUnbuilt,
                            retention: None,
                        },
                    );
                }
                continue;
            };
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
                // The returned child's permission and its carrier are queried
                // exactly as the established receiver path does: an outgoing
                // view of a mutable subject keeps a writable carrier, and a
                // shared subject holds rather than lending a read-only view to
                // a position whose child may write through it.
                let sink_may_return_child = return_may_carry_pointer(
                    tcx,
                    tcx.fn_sig(callee).skip_binder().skip_binder().output(),
                    RETURN_CARRIER_WALK_DEPTH,
                );
                if sink_may_return_child
                    && let Err(reason) = raw_boundary::returned_child_permission(&source_form, None)
                {
                    return Err((OutboundExpressionFailure::ChildPermission(reason), Some(evidence.clone())));
                }
                let base = raw_boundary::template_for(&source_form, &site.target, None, negative_write.is_some())
                    .map_err(|reason| (OutboundExpressionFailure::Template(reason), Some(evidence.clone())))?;
                let (template, child_binding_required) = if sink_may_return_child {
                    let selected = raw_boundary::returned_child_template(&source_form, &site.target, None, base)
                        .map_err(|reason| (OutboundExpressionFailure::Template(reason), Some(evidence.clone())))?;
                    (selected.template, selected.mutable_binding_required)
                } else {
                    (base, false)
                };
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
                let mutable_temporary = match interface.form {
                    Form::Opt { mutable, .. } => mutable,
                    Form::Raw | Form::Ref { .. } | Form::Slice { .. } => child_binding_required,
                };
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
