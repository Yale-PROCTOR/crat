//! Owned input-form twins for retired borrowed-return receivers.
//!
//! Native lifetime permits identify the returned interface. They do not prove
//! that a raw alias derived from that result is unretained in its caller.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use rustc_middle::{
    mir::{Local, Location, TerminatorKind},
    ty::TyKind,
};

use super::{
    DecisionTable,
    raw_boundary::{
        self, BridgeTemplate, RawBoundaryBlockReason, RetentionSummaries, RetentionVerdict,
        ReturnedChildPermissionFailure,
    },
    return_alias::{self, ReturnUseObservation},
    return_receiver::{self, Node, ReceiverPlan},
    seam::GlueSpec,
};
use crate::{
    bo_rewriter::bridge_receipt::{
        BridgeRetentionTier, RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReceiverInputSelection {
    pub(crate) node: Node,
    pub(crate) callee: SignatureClassId,
    /// Exact source-subject atom identities from the existing decision table.
    pub(crate) source_atom_ids: BTreeSet<String>,
}

impl ReceiverInputSelection {
    /// Both consumers supply their normalized final class/atom selection.
    pub(crate) fn active(
        &self,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> bool {
        !classes.contains(&self.callee)
            && (classes.contains(&SignatureClassId::of(self.node.0))
                || !self.source_atom_ids.is_disjoint(atoms))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReceiverInputFailure {
    MirCallMissing,
    MirCallAmbiguous,
    MirDestinationNotReceiver,
    MirResultTypeMismatch,
    Depth2StorageEvidenceUnavailable,
    CallCarrierCompositionUnbuilt,
    PositiveRetention,
    LocalScheduleCertificateUnavailable,
    ChildPermission(ReturnedChildPermissionFailure),
    Template(RawBoundaryBlockReason),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReceiverInputUnavailable {
    pub(crate) receiver: ReceiverPlan,
    pub(crate) selection: ReceiverInputSelection,
    pub(crate) reason: ReceiverInputFailure,
    pub(crate) retention: Option<RetentionVerdict>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReceiverInputPlan {
    /// Includes the exact initializer HIR/span, raw target and native return
    /// form/pointee/lifetime-plan digest. No receipt text is re-parsed.
    pub(crate) receiver: ReceiverPlan,
    pub(crate) selection: ReceiverInputSelection,
    pub(crate) call: Location,
    pub(crate) destination: Local,
    /// Observation is descriptive; Used/Unused never substitutes for an
    /// alias-schedule or complete negative-write proof.
    pub(crate) result_use: ReturnUseObservation,
    pub(crate) retention: RetentionVerdict,
    pub(crate) tier: BridgeRetentionTier,
    pub(crate) waiver_id: &'static str,
    pub(crate) template: BridgeTemplate,
    pub(crate) spec: GlueSpec,
    pub(crate) temporary: String,
    pub(crate) mutable_temporary: bool,
    view: String,
}

impl ReceiverInputPlan {
    pub(crate) fn active(
        &self,
        classes: &BTreeSet<SignatureClassId>,
        atoms: &BTreeSet<String>,
    ) -> bool {
        self.selection.active(classes, atoms)
    }

    /// The caller passes the already-adapted initializer. Its call and argument
    /// evaluation order survive, and the returned borrowed value is bound once.
    pub(crate) fn render(&self, adapted_call: &str) -> String {
        render_returned_value(
            &self.temporary,
            self.mutable_temporary,
            &self.receiver.candidate_interface.temporary_type(),
            &self.receiver.raw_result.rendered,
            &self.view,
            adapted_call,
        )
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ReceiverInputMap {
    pub(crate) plans: FxHashMap<Node, ReceiverInputPlan>,
    pub(crate) unavailable: FxHashMap<Node, ReceiverInputUnavailable>,
}

/// Native returned-value evidence shared by admitted receiver retirement and
/// an independently inventoried raw receiver. This is not an admission token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnedValueSite {
    pub(crate) node: Node,
    pub(crate) callee: rustc_hir::def_id::LocalDefId,
    pub(crate) initializer_span: rustc_span::Span,
    pub(crate) source_interface: super::return_interface::ReturnInterface,
    pub(crate) raw_result: raw_boundary::RawTargetType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnedValueView {
    pub(crate) site: ReturnedValueSite,
    pub(crate) call: Location,
    pub(crate) destination: Local,
    pub(crate) result_use: ReturnUseObservation,
    pub(crate) retention: RetentionVerdict,
    pub(crate) tier: BridgeRetentionTier,
    pub(crate) waiver_id: &'static str,
    pub(crate) template: BridgeTemplate,
    pub(crate) spec: GlueSpec,
    pub(crate) temporary: String,
    pub(crate) mutable_temporary: bool,
    view: String,
}

fn render_returned_value(
    temporary: &str,
    mutable: bool,
    borrowed_type: &str,
    raw_type: &str,
    view: &str,
    adapted_call: &str,
) -> String {
    format!(
        "{{ let {}{temporary}: {borrowed_type} = ({adapted_call}); ({view}) as {raw_type} }}",
        if mutable { "mut " } else { "" }
    )
}

impl ReturnedValueView {
    pub(crate) fn render(&self, adapted_call: &str) -> String {
        render_returned_value(
            &self.temporary,
            self.mutable_temporary,
            &self.site.source_interface.temporary_type(),
            &self.site.raw_result.rendered,
            &self.view,
            adapted_call,
        )
    }
}

pub(crate) fn plan_returned_value(
    program: &RustProgram<'_>,
    table: &DecisionTable,
    retention: &RetentionSummaries,
    site: ReturnedValueSite,
    destination_local: Local,
) -> Result<ReturnedValueView, (ReceiverInputFailure, Option<RetentionVerdict>)> {
    let tcx = program.tcx;
    let failure = |reason| (reason, None);
    if table
        .seams
        .a5_raw_calls
        .iter()
        .any(|call| call.call_span == site.initializer_span)
        || table
            .seams
            .pair_raw_calls
            .iter()
            .any(|call| call.call_span == site.initializer_span)
        || table
            .c9_marks
            .iter()
            .any(|mark| mark.call_span == site.initializer_span)
    {
        return Err(failure(ReceiverInputFailure::CallCarrierCompositionUnbuilt));
    }
    if site.raw_result.depth2.is_some() {
        return Err(failure(
            ReceiverInputFailure::Depth2StorageEvidenceUnavailable,
        ));
    }
    let Some(source) = super::seam::decision_for_safe_form(site.source_interface.form) else {
        return Err(failure(ReceiverInputFailure::Template(
            RawBoundaryBlockReason::TemplateUnavailable,
        )));
    };
    let body = tcx
        .mir_drops_elaborated_and_const_checked(site.node.0)
        .borrow();
    let candidates = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            let terminator = data.terminator();
            let TerminatorKind::Call {
                func, destination, ..
            } = &terminator.kind
            else {
                return None;
            };
            let TyKind::FnDef(callee, _) = *func.constant()?.ty().kind() else { return None };
            (callee == site.callee.to_def_id()
                && terminator.source_info.span.source_callsite()
                    == site.initializer_span.source_callsite())
            .then_some((
                Location {
                    block,
                    statement_index: data.statements.len(),
                },
                *destination,
            ))
        })
        .collect::<Vec<_>>();
    let (call, destination) = match candidates.as_slice() {
        [(call, destination)] => (*call, *destination),
        [] => return Err(failure(ReceiverInputFailure::MirCallMissing)),
        _ => return Err(failure(ReceiverInputFailure::MirCallAmbiguous)),
    };
    if destination.as_local() != Some(destination_local) {
        return Err(failure(ReceiverInputFailure::MirDestinationNotReceiver));
    }
    if raw_boundary::raw_target_type(tcx, body.local_decls[destination_local].ty).as_ref()
        != Some(&site.raw_result)
    {
        return Err(failure(ReceiverInputFailure::MirResultTypeMismatch));
    }
    let result_use = return_alias::observe(&body, call);
    let evidence = retention.copied_local_retention(program, site.node.0, destination_local);
    match &evidence {
        RetentionVerdict::Retains { .. } => {
            return Err((ReceiverInputFailure::PositiveRetention, Some(evidence)));
        }
        // Native lifetime admission does not supply a caller alias schedule.
        RetentionVerdict::NoRetain { .. } => {
            return Err((
                ReceiverInputFailure::LocalScheduleCertificateUnavailable,
                Some(evidence),
            ));
        }
        RetentionVerdict::Unknown { .. } => {}
    }
    if let Err(reason) = raw_boundary::returned_child_permission(&source, None) {
        return Err((
            ReceiverInputFailure::ChildPermission(reason),
            Some(evidence),
        ));
    }
    let selected =
        raw_boundary::template_for(&source, &site.raw_result, None, false).and_then(|base| {
            raw_boundary::returned_child_template(&source, &site.raw_result, None, base)
        });
    let selected = match selected {
        Ok(selected) => selected,
        Err(reason) => return Err((ReceiverInputFailure::Template(reason), Some(evidence))),
    };
    let mut spec =
        GlueSpec::raw_boundary(selected.template, site.raw_result.mutability, false, true);
    if let Some(raw) = spec.raw_boundary.as_mut() {
        raw.cast_pointee = Some(site.raw_result.pointee.clone());
    }
    let temporary = format!(
        "__crat_receiver_input_{}_{}",
        site.node.0.local_def_index.as_u32(),
        site.node.1.local_id.as_u32()
    );
    let Some(view) = spec.render(&temporary) else {
        return Err((
            ReceiverInputFailure::Template(RawBoundaryBlockReason::TemplateUnavailable),
            Some(evidence),
        ));
    };
    let mutable_temporary = match site.source_interface.form {
        super::seam::Form::Opt { mutable, .. } => mutable,
        super::seam::Form::Raw
        | super::seam::Form::Ref { .. }
        | super::seam::Form::Slice { .. } => selected.mutable_binding_required,
    };
    Ok(ReturnedValueView {
        site,
        call,
        destination: destination_local,
        result_use,
        retention: evidence,
        tier: BridgeRetentionTier::T2,
        waiver_id: RAW_BOUNDARY_T2_WAIVER_ID,
        template: selected.template,
        spec,
        temporary,
        mutable_temporary,
        view,
    })
}

pub(crate) fn plan(
    program: &RustProgram<'_>,
    table: &DecisionTable,
    retention: &RetentionSummaries,
) -> ReceiverInputMap {
    let mut out = ReceiverInputMap::default();
    for receiver in table.return_receivers.plans.values() {
        if return_receiver::active_initializer(
            table,
            receiver.node,
            receiver.initializer_hir,
            receiver.initializer_span,
        )
        .is_none()
        {
            continue;
        }
        let Some((subject, _)) = table
            .entries
            .iter()
            .find(|(subject, _)| (subject.fn_did, subject.hir_id) == receiver.node)
        else {
            continue;
        };
        let selection = ReceiverInputSelection {
            node: receiver.node,
            callee: SignatureClassId::of(receiver.callee),
            source_atom_ids: table
                .seams
                .raw_boundary_atom_groups
                .get(&receiver.node)
                .into_iter()
                .flatten()
                .map(|atom| atom.id.clone())
                .collect(),
        };
        let site = ReturnedValueSite {
            node: receiver.node,
            callee: receiver.callee,
            initializer_span: receiver.initializer_span,
            source_interface: receiver.candidate_interface.clone(),
            raw_result: receiver.raw_result.clone(),
        };
        match plan_returned_value(program, table, retention, site, subject.local) {
            Ok(view) => {
                out.plans.insert(
                    receiver.node,
                    ReceiverInputPlan {
                        receiver: receiver.clone(),
                        selection,
                        call: view.call,
                        destination: view.destination,
                        result_use: view.result_use,
                        retention: view.retention,
                        tier: view.tier,
                        waiver_id: view.waiver_id,
                        template: view.template,
                        spec: view.spec,
                        temporary: view.temporary,
                        mutable_temporary: view.mutable_temporary,
                        view: view.view,
                    },
                );
            }
            Err((reason, evidence)) => {
                out.unavailable.insert(
                    receiver.node,
                    ReceiverInputUnavailable {
                        receiver: receiver.clone(),
                        selection,
                        reason,
                        retention: evidence,
                    },
                );
            }
        }
    }
    out
}
