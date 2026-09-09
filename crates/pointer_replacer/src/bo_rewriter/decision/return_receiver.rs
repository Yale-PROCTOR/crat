//! Candidate presentations of exact local borrowed-return receivers.
//!
//! Native permits license candidates; ordinary decision gates still decide
//! admission. Current callee interfaces are validated separately before emit.

use rustc_hash::FxHashMap;
use rustc_hir::{ExprKind, HirId, QPath, def::Res, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::{
    DecisionTable, SubjectKind,
    construction::{CallResultTarget, Construction, ConstructionFacts},
    lifetime::LifetimeEligibility,
    raw_boundary::{RawTargetType, raw_target_type},
    return_interface::ReturnInterface,
    seam::Form,
};

pub(crate) type Node = (LocalDefId, HirId);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SourceReversion {
    /// A retired receiver still calling a borrowed-return callee needs an
    /// explicit borrowed-result-to-original-raw-type initializer twin.
    BorrowedResultToRaw,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReceiverDeclaration {
    Inferred,
    Existing,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReceiverCoercion {
    Identity,
    SharedOption,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReceiverPlan {
    pub(crate) node: Node,
    pub(crate) callee: LocalDefId,
    pub(crate) initializer_hir: HirId,
    pub(crate) initializer_span: Span,
    pub(crate) candidate_interface: ReturnInterface,
    pub(crate) receiver_form: Form,
    pub(crate) declaration: ReceiverDeclaration,
    pub(crate) coercion: ReceiverCoercion,
    pub(crate) raw_result: RawTargetType,
    pub(crate) source_reversion: SourceReversion,
}

impl ReceiverPlan {
    pub(crate) fn render_coercion(&self, call: &str) -> String {
        match self.coercion {
            ReceiverCoercion::Identity => call.to_owned(),
            ReceiverCoercion::SharedOption => {
                format!("({call}).map(|__crat_receiver_shared| &*__crat_receiver_shared)")
            }
        }
    }

    pub(crate) fn receiver_type(&self) -> String {
        // The native return stays mutable when its receiving local weakens
        // to shared. Only the receiver's annotation uses this presentation.
        let mut presentation = self.candidate_interface.clone();
        presentation.form = self.receiver_form;
        presentation.temporary_type()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FailureKind {
    CalleeInterfaceUnavailable,
    InitializerUnavailable,
    InitializerNotExactDirectCall,
    ResultNotRawPointer,
    PointeePresentationMismatch,
    MutabilityPresentationUnbuilt { returned: Form, receiver: Form },
    CurrentCalleeInterfaceMissing,
    CurrentCalleeInterfaceChanged,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReceiverFailure {
    pub(crate) node: Node,
    pub(crate) callee: LocalDefId,
    pub(crate) kind: FailureKind,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ReceiverMap {
    pub(crate) plans: FxHashMap<Node, ReceiverPlan>,
    pub(crate) failures: FxHashMap<Node, ReceiverFailure>,
}

fn failure(map: &mut ReceiverMap, node: Node, callee: LocalDefId, kind: FailureKind) {
    map.failures
        .insert(node, ReceiverFailure { node, callee, kind });
}

pub(crate) fn plan(
    tcx: TyCtxt<'_>,
    prototype: &DecisionTable,
    constructions: &ConstructionFacts,
    eligibility: &LifetimeEligibility,
) -> ReceiverMap {
    let mut result = ReceiverMap::default();
    for (subject, _) in &prototype.entries {
        if subject.kind != SubjectKind::Local {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        let (callee, declaration) = if subject.ty_span.is_some() {
            let Some(permit) = eligibility.annotated_receiver_permit(node) else { continue };
            (permit.callee(), ReceiverDeclaration::Existing)
        } else {
            let Some(permit) = eligibility.inferred_permit(node) else { continue };
            (permit.callee(), ReceiverDeclaration::Inferred)
        };
        let Some(interface) = prototype.return_interfaces.functions.get(&callee) else {
            if prototype.return_interfaces.failures.contains_key(&callee) {
                failure(
                    &mut result,
                    node,
                    callee,
                    FailureKind::CalleeInterfaceUnavailable,
                );
            }
            continue;
        };
        let receiver_form = match interface.form {
            Form::Slice { .. } => Form::Slice {
                mutable: subject.mutable,
            },
            Form::Opt { slice, .. } if declaration == ReceiverDeclaration::Inferred => Form::Opt {
                mutable: subject.mutable,
                slice,
            },
            Form::Opt { .. } => {
                failure(
                    &mut result,
                    node,
                    callee,
                    FailureKind::MutabilityPresentationUnbuilt {
                        returned: interface.form,
                        receiver: Form::Slice {
                            mutable: subject.mutable,
                        },
                    },
                );
                continue;
            }
            // Keep the established scalar InferredRef path unchanged.
            Form::Raw | Form::Ref { .. } => continue,
        };
        let shared_slice_weakening = matches!(
            (interface.form, receiver_form),
            (
                Form::Slice { mutable: true },
                Form::Slice { mutable: false }
            )
        );
        let shared_option = matches!((interface.form, receiver_form),
            (Form::Opt { mutable: true, slice: source_slice },
                Form::Opt { mutable: false, slice: target_slice }) if source_slice == target_slice);
        if receiver_form != interface.form && !shared_slice_weakening && !shared_option {
            failure(
                &mut result,
                node,
                callee,
                FailureKind::MutabilityPresentationUnbuilt {
                    returned: interface.form,
                    receiver: receiver_form,
                },
            );
            continue;
        }
        if constructions.by_binding.get(&node) != Some(&Construction::CallResult)
            || constructions.call_result_targets.get(&node)
                != Some(&CallResultTarget::DirectLocal(callee))
        {
            failure(
                &mut result,
                node,
                callee,
                FailureKind::InitializerNotExactDirectCall,
            );
            continue;
        }
        let (Some(&initializer_hir), Some(&initializer_span)) = (
            constructions.init_hirs.get(&node),
            constructions.init_spans.get(&node),
        ) else {
            failure(
                &mut result,
                node,
                callee,
                FailureKind::InitializerUnavailable,
            );
            continue;
        };
        let initializer = tcx.hir_node(initializer_hir).expect_expr();
        let exact = match initializer.kind {
            ExprKind::Call(function, _) => matches!(function.kind,
                ExprKind::Path(QPath::Resolved(_, path))
                    if matches!(path.res, Res::Def(_, did) if did == callee.to_def_id())),
            _ => false,
        };
        if !exact || initializer.span != initializer_span {
            failure(
                &mut result,
                node,
                callee,
                FailureKind::InitializerNotExactDirectCall,
            );
            continue;
        }
        let Some(raw_result) =
            raw_target_type(tcx, tcx.typeck(subject.fn_did).expr_ty(initializer))
        else {
            failure(&mut result, node, callee, FailureKind::ResultNotRawPointer);
            continue;
        };
        // This first carrier does not instantiate a generic/aliased return
        // presentation in the caller or introduce a pointee conversion.
        if raw_result.pointee != interface.pointee {
            failure(
                &mut result,
                node,
                callee,
                FailureKind::PointeePresentationMismatch,
            );
            continue;
        }
        result.plans.insert(
            node,
            ReceiverPlan {
                node,
                callee,
                initializer_hir,
                initializer_span,
                candidate_interface: interface.clone(),
                receiver_form,
                declaration,
                coercion: if shared_option {
                    ReceiverCoercion::SharedOption
                } else {
                    ReceiverCoercion::Identity
                },
                raw_result,
                source_reversion: SourceReversion::BorrowedResultToRaw,
            },
        );
    }
    result
}

/// Ordinary candidate/current disagreement is a per-receiver planning result,
/// not a whole-program instrument error.
pub(crate) fn validate_current(
    candidate: &ReceiverMap,
    table: &DecisionTable,
) -> Vec<ReceiverFailure> {
    let mut failures = candidate.failures.values().cloned().collect::<Vec<_>>();
    for plan in candidate.plans.values() {
        let kind = match table.return_interfaces.functions.get(&plan.callee) {
            Some(current) if current == &plan.candidate_interface => continue,
            Some(_) => FailureKind::CurrentCalleeInterfaceChanged,
            None => FailureKind::CurrentCalleeInterfaceMissing,
        };
        failures.push(ReceiverFailure {
            node: plan.node,
            callee: plan.callee,
            kind,
        });
    }
    failures.sort_by_key(|failure| {
        (
            failure.node.0.local_def_index.as_u32(),
            failure.node.1.local_id.as_u32(),
        )
    });
    failures
}

pub(crate) fn active_initializer(
    table: &DecisionTable,
    node: Node,
    hir: HirId,
    span: Span,
) -> Option<&ReceiverPlan> {
    if table.return_receivers.failures.contains_key(&node) {
        return None;
    }
    let plan = table.return_receivers.plans.get(&node)?;
    let (_, decision) = table
        .entries
        .iter()
        .find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)?;
    if super::seam::form_of(decision) != plan.receiver_form {
        return None;
    }
    (plan.initializer_hir == hir
        && plan.initializer_span == span
        && table.return_interfaces.functions.get(&plan.callee) == Some(&plan.candidate_interface))
    .then_some(plan)
}
