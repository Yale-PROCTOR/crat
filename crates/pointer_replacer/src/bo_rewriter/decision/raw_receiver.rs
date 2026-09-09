//! Raw destinations of native borrowed call results. These plans adapt an
//! initializer without admitting the receiving local as a safe subject.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use rustc_hir::{ExprKind, HirId, QPath, def::Res, def_id::LocalDefId};
use rustc_span::Span;

use super::{
    Decision, DecisionTable, SubjectKind,
    construction::{CallResultTarget, Construction, ConstructionFacts},
    raw_boundary::{RawTargetType, RetentionSummaries, RetentionVerdict, raw_target_type},
    receiver_input::{self, ReceiverInputFailure, ReturnedValueSite, ReturnedValueView},
    return_interface::ReturnInterface,
    return_receiver::Node,
    seam::Form,
};
use crate::{
    bo_rewriter::bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeSitePlan, SignatureClassId,
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawReceiverPlan {
    pub(crate) node: Node,
    pub(crate) callee: LocalDefId,
    pub(crate) initializer_hir: HirId,
    pub(crate) initializer_span: Span,
    pub(crate) raw_result: RawTargetType,
    pub(crate) source_interface: ReturnInterface,
    pub(crate) original_expression: String,
    pub(crate) view: ReturnedValueView,
}

impl RawReceiverPlan {
    pub(crate) fn active(&self, classes: &BTreeSet<SignatureClassId>) -> bool {
        !classes.contains(&SignatureClassId::of(self.callee))
    }

    pub(crate) fn render(&self, adapted_call: &str) -> String {
        self.view.render(adapted_call)
    }

    pub(crate) fn bridge(&self) -> BridgeSitePlan {
        BridgeSitePlan {
            caller: self.node.0,
            callee: BridgeCalleeId::Local(self.callee),
            arm: "c".into(),
            position: format!(
                "raw-receiver:{}:{}:lifetime_plan={}",
                self.node.0.local_def_index.as_u32(),
                self.node.1.local_id.as_u32(),
                self.source_interface.lifetime_plan_digest
            ),
            bridge_kind: "return-caller-receive-raw".into(),
            expected_form: "raw".into(),
            found_form: self.source_interface.form.key().into(),
            argument_kind: "return-call-result".into(),
            extent: BridgeExtentKind::None,
            retention: self.view.tier,
            waiver_id: Some(self.view.waiver_id.into()),
            unsafe_context: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RawReceiverFailure {
    InitializerUnavailable,
    InitializerNotExactDirectCall,
    OriginalExpressionUnavailable,
    ResultNotRawPointer,
    PointeePresentationMismatch,
    View(ReceiverInputFailure),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawReceiverUnavailable {
    pub(crate) node: Node,
    pub(crate) callee: LocalDefId,
    pub(crate) initializer_hir: Option<HirId>,
    pub(crate) initializer_span: Option<Span>,
    pub(crate) source_interface: ReturnInterface,
    pub(crate) reason: RawReceiverFailure,
    pub(crate) retention: Option<RetentionVerdict>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RawReceiverPlans {
    pub(crate) plans: FxHashMap<Node, RawReceiverPlan>,
    pub(crate) unavailable: FxHashMap<Node, RawReceiverUnavailable>,
}

pub(crate) fn plan(
    program: &RustProgram<'_>,
    table: &DecisionTable,
    constructions: &ConstructionFacts,
    retention: &RetentionSummaries,
) -> RawReceiverPlans {
    let tcx = program.tcx;
    let mut out = RawReceiverPlans::default();
    for (subject, decision) in &table.entries {
        let raw = match decision {
            Decision::Degraded(_) => true,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => false,
        };
        if !raw || subject.kind != SubjectKind::Local {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        if constructions.by_binding.get(&node) != Some(&Construction::CallResult) {
            continue;
        }
        let Some(&CallResultTarget::DirectLocal(callee)) =
            constructions.call_result_targets.get(&node)
        else {
            continue;
        };
        let Some(interface) = table.return_interfaces.functions.get(&callee) else { continue };
        match interface.form {
            Form::Raw => continue,
            Form::Ref { .. } | Form::Slice { .. } | Form::Opt { .. } => {}
        }
        let initializer_hir = constructions.init_hirs.get(&node).copied();
        let initializer_span = constructions.init_spans.get(&node).copied();
        let unavailable = |reason, retention| RawReceiverUnavailable {
            node,
            callee,
            initializer_hir,
            initializer_span,
            source_interface: interface.clone(),
            reason,
            retention,
        };
        let (Some(hir), Some(span)) = (initializer_hir, initializer_span) else {
            out.unavailable.insert(
                node,
                unavailable(RawReceiverFailure::InitializerUnavailable, None),
            );
            continue;
        };
        let initializer = tcx.hir_node(hir).expect_expr();
        let exact = match initializer.kind {
            ExprKind::Call(function, _) => matches!(function.kind,
                ExprKind::Path(QPath::Resolved(_, path))
                    if matches!(path.res, Res::Def(_, did) if did == callee.to_def_id())),
            _ => false,
        };
        if !exact || initializer.span != span {
            out.unavailable.insert(
                node,
                unavailable(RawReceiverFailure::InitializerNotExactDirectCall, None),
            );
            continue;
        }
        let Some(raw_result) =
            raw_target_type(tcx, tcx.typeck(subject.fn_did).expr_ty(initializer))
        else {
            out.unavailable.insert(
                node,
                unavailable(RawReceiverFailure::ResultNotRawPointer, None),
            );
            continue;
        };
        if raw_result.pointee != interface.pointee {
            out.unavailable.insert(
                node,
                unavailable(RawReceiverFailure::PointeePresentationMismatch, None),
            );
            continue;
        }
        let Ok(original_expression) = tcx.sess.source_map().span_to_snippet(span) else {
            out.unavailable.insert(
                node,
                unavailable(RawReceiverFailure::OriginalExpressionUnavailable, None),
            );
            continue;
        };
        let site = ReturnedValueSite {
            node,
            callee,
            initializer_span: span,
            source_interface: interface.clone(),
            raw_result: raw_result.clone(),
        };
        match receiver_input::plan_returned_value(program, table, retention, site, subject.local) {
            Ok(view) => {
                out.plans.insert(
                    node,
                    RawReceiverPlan {
                        node,
                        callee,
                        initializer_hir: hir,
                        initializer_span: span,
                        raw_result,
                        source_interface: interface.clone(),
                        original_expression,
                        view,
                    },
                );
            }
            Err((reason, evidence)) => {
                out.unavailable.insert(
                    node,
                    unavailable(RawReceiverFailure::View(reason), evidence),
                );
            }
        }
    }
    out
}
