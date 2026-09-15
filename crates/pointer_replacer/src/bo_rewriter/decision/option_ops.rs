//! Consuming raw returns of optional locals (parameter returns retain E2
//! ownership), and optional operands of pointer comparisons, whose view the
//! raw boundary's address arm supplies.

use rustc_hash::FxHashMap;
use rustc_hir::{BinOpKind, Expr, ExprKind, HirId, Node, def_id::LocalDefId};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    DecisionTable, Subject, SubjectKind,
    emitability::{OptUseSite, OptUses, UseEdit},
    lifetime::FnSignatureSlot,
    raw_boundary::{RawMutability, raw_target_type},
    seam::Form,
};
use crate::bo_rewriter::mechanical_receipt::{
    MechanicalEvidence, MechanicalFamily, MechanicalTerminalReason, OptionPresentationReceiptPlan,
};

/// Defer only an explicit, bare return of a positively identified local.
/// Final presentation and permission are checked by `plan_raw_returns`.
pub(super) fn collect_raw_return(
    tcx: TyCtxt<'_>,
    expression: &Expr<'_>,
    node: (LocalDefId, HirId),
    uses: &mut FxHashMap<(LocalDefId, HirId), OptUses>,
) -> bool {
    if !matches!(tcx.parent_hir_node(node.1), Node::LetStmt(_))
        || !matches!(tcx.parent_hir_node(expression.hir_id),
            Node::Expr(parent) if matches!(parent.kind,
                ExprKind::Ret(Some(value)) if value.hir_id == expression.hir_id))
        || !matches!(
            tcx.fn_sig(node.0)
                .skip_binder()
                .skip_binder()
                .output()
                .kind(),
            TyKind::RawPtr(..)
        )
    {
        return false;
    }
    let entry = uses.entry(node).or_default();
    entry.non_test_uses += 1;
    entry.sites.push(OptUseSite {
        hir_id: expression.hir_id,
        span: expression.span,
        operation: "return-raw",
    });
    true
}

pub(super) fn plan_raw_returns(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    subject: &Subject,
    source: Form,
    uses: &OptUses,
    receipts: &mut Vec<OptionPresentationReceiptPlan>,
    edits: &mut Vec<((LocalDefId, HirId), UseEdit)>,
) {
    for site in uses
        .sites
        .iter()
        .filter(|site| site.operation == "return-raw")
    {
        let planned = raw_return_expression(tcx, table, subject, source, site);
        let (adapter, reason) = match planned {
            Ok(replacement) => {
                edits.push((
                    (subject.fn_did, subject.hir_id),
                    UseEdit {
                        span: site.span,
                        replacement,
                        bridge_kind: "subject-use",
                    },
                ));
                ("option-to-raw-consuming-return".to_owned(), None)
            }
            Err(reason) => (
                String::new(),
                Some(MechanicalTerminalReason::EvidenceMissing(reason.to_owned())),
            ),
        };
        // This is a terminal move, not a callee retaining a view while the
        // Option is live. No retention verdict or additional waiver is inferred.
        receipts.push(super::option::receipt(
            tcx,
            subject,
            site.hir_id,
            MechanicalFamily::OptUseUnsupported,
            "return-raw",
            source,
            Form::Raw,
            adapter,
            reason,
            MechanicalEvidence::default(),
        ));
    }
}

fn raw_return_expression(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    subject: &Subject,
    source: Form,
    site: &OptUseSite,
) -> Result<String, &'static str> {
    if !matches!(subject.kind, SubjectKind::Local) || subject.ptr_depth != 1 {
        return Err("option-raw-return:local-thin-pointer-required");
    }
    if table
        .return_interfaces
        .functions
        .contains_key(&subject.fn_did)
        || table
            .lifetime_plan
            .function(subject.fn_did)
            .and_then(|plan| plan.lifetime_for(FnSignatureSlot::RETURN))
            .is_some()
    {
        return Err("option-raw-return:borrowed-interface-owned");
    }
    let Form::Opt {
        mutable,
        slice: false,
    } = source
    else {
        return Err("option-raw-return:thin-option-required");
    };
    let output = tcx
        .fn_sig(subject.fn_did)
        .skip_binder()
        .skip_binder()
        .output();
    let expression = tcx.hir_node(site.hir_id).expect_expr();
    let input = tcx.typeck(subject.fn_did).expr_ty(expression);
    let (TyKind::RawPtr(input_pointee, _), TyKind::RawPtr(output_pointee, _)) =
        (input.kind(), output.kind())
    else {
        return Err("option-raw-return:raw-signature-required");
    };
    if input_pointee != output_pointee {
        return Err("option-raw-return:pointee-mismatch");
    }
    let target = raw_target_type(tcx, output).ok_or("option-raw-return:target-unnameable")?;
    let name = subject
        .param_name
        .as_deref()
        .ok_or("option-raw-return:binding-unnameable")?;
    let (null, address) = match (mutable, target.mutability) {
        (true, RawMutability::Mut) => ("null_mut", "core::ptr::from_mut(value)"),
        (true, RawMutability::Const) => ("null", "core::ptr::from_mut(value).cast_const()"),
        (false, RawMutability::Const) => ("null", "core::ptr::from_ref(value)"),
        (false, RawMutability::Mut) => return Err("option-raw-return:shared-to-mut-held"),
    };
    Ok(format!(
        "{name}.map_or(core::ptr::{null}::<{}>(), |value| {address})",
        target.pointee
    ))
}

/// Defer a direct operand of a pointer comparison (casts peeled upward) to the
/// raw boundary's address view; `plan_address_observations` then requires that
/// view to exist. Not a use with no image, so the family is not withdrawn here.
pub(super) fn collect_address_observation(
    tcx: TyCtxt<'_>,
    expression: &Expr<'_>,
    node: (LocalDefId, HirId),
    uses: &mut FxHashMap<(LocalDefId, HirId), OptUses>,
) -> bool {
    let mut operand = expression;
    while let Node::Expr(parent) = tcx.parent_hir_node(operand.hir_id)
        && matches!(parent.kind, ExprKind::Cast(inner, _) if inner.hir_id == operand.hir_id)
    {
        operand = parent;
    }
    let Node::Expr(parent) = tcx.parent_hir_node(operand.hir_id) else { return false };
    let ExprKind::Binary(op, lhs, rhs) = parent.kind else { return false };
    if !matches!(
        op.node,
        BinOpKind::Eq
            | BinOpKind::Ne
            | BinOpKind::Lt
            | BinOpKind::Le
            | BinOpKind::Gt
            | BinOpKind::Ge
    ) || (lhs.hir_id != operand.hir_id && rhs.hir_id != operand.hir_id)
    {
        return false;
    }
    let typeck = tcx.typeck(node.0);
    if ![lhs, rhs]
        .into_iter()
        .all(|side| matches!(typeck.expr_ty(side).kind(), TyKind::RawPtr(..)))
    {
        return false;
    }
    let entry = uses.entry(node).or_default();
    entry.non_test_uses += 1;
    entry.sites.push(OptUseSite {
        hir_id: expression.hir_id,
        span: expression.span,
        operation: "address-observation",
    });
    true
}

/// An `address-observation` site is applied exactly when the seam plan carries
/// the address view for that operand; otherwise the typed hold.
pub(super) fn plan_address_observations(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    subject: &Subject,
    source: Form,
    uses: &OptUses,
    receipts: &mut Vec<OptionPresentationReceiptPlan>,
) {
    for site in uses
        .sites
        .iter()
        .filter(|site| site.operation == "address-observation")
    {
        let view = table.seams.edits.iter().find(|edit| {
            edit.source_shape == "raw-op-address-observation"
                && edit.bridge.caller == subject.fn_did
                && edit.span.source_callsite() == site.span.source_callsite()
        });
        let (adapter, reason) = match view {
            Some(view) => (view.spec.template_key().to_owned(), None),
            None => (
                String::new(),
                Some(MechanicalTerminalReason::EvidenceMissing(
                    "option-address-view:missing".to_owned(),
                )),
            ),
        };
        // A comparison observes the address only; no callee, no retention.
        receipts.push(super::option::receipt(
            tcx,
            subject,
            site.hir_id,
            MechanicalFamily::OptUseUnsupported,
            "address-observation",
            source,
            Form::Raw,
            adapter,
            reason,
            MechanicalEvidence::default(),
        ));
    }
}
