//! Consuming raw returns of optional locals (parameter returns retain E2
//! ownership), and optional operands of pointer comparisons, whose view the
//! raw boundary's address arm supplies.

use rustc_hash::FxHashMap;
use rustc_hir::{
    BinOpKind, Expr, ExprKind, HirId, Node,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    DecisionTable, Subject, SubjectKind,
    emitability::{ArgShape, EmitabilityFacts, OptUseSite, OptUses, UseEdit},
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

/// One reborrow per call: when a MUTABLE thin optional is accessed through
/// `as_mut()` at two or more places inside one call's argument list — the
/// disjoint-field views `f(&mut (*value).a, &mut (*value).b)` wave-6p
/// certifies — each access borrows the Option mutably for the whole call and
/// the compiler refuses the second (E0499). The call is wrapped in a block
/// that reborrows the Option ONCE, `let value = value.as_deref_mut().unwrap();`,
/// under which the original argument text is already right; the call's inner
/// edits are composed into the block (the same mechanism a composed Option
/// initializer uses) and the subject's own accessor edits inside it are
/// retired. The unwrap is the existing required-dereference idiom: the C code
/// dereferences the pointer at these arguments unconditionally.
pub(super) fn plan_call_reborrows(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    subject: &Subject,
    source: Form,
    receipts: &mut Vec<OptionPresentationReceiptPlan>,
    edits: &mut Vec<((LocalDefId, HirId), UseEdit)>,
    composed: &mut Vec<((LocalDefId, HirId), Span)>,
) {
    let Form::Opt {
        mutable: true,
        slice: false,
    } = source
    else {
        return;
    };
    let node = (subject.fn_did, subject.hir_id);
    let Some(name) = subject.param_name.as_deref() else { return };
    let Some((_, decision)) = table
        .entries
        .iter()
        .find(|(candidate, _)| (candidate.fn_did, candidate.hir_id) == node)
    else {
        return;
    };
    let uses = match decision {
        super::Decision::Opt { uses, .. } => uses,
        super::Decision::Ref { .. }
        | super::Decision::InferredRef { .. }
        | super::Decision::Slice { .. }
        | super::Decision::NestedSlice { .. }
        | super::Decision::Cursor { .. }
        | super::Decision::Box(_)
        | super::Decision::Degraded(_) => return,
    };
    let Some(body_id) = tcx.hir_node_by_def_id(subject.fn_did).body_id() else { return };
    struct Calls<'a>(Vec<&'a Expr<'a>>);
    impl<'tcx> Visitor<'tcx> for Calls<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Call(..) = expr.kind {
                self.0.push(expr);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut calls = Calls(Vec::new());
    calls.visit_body(tcx.hir_body(body_id));
    let sm = tcx.sess.source_map();
    let unsafe_fn = tcx
        .fn_sig(subject.fn_did)
        .skip_binder()
        .skip_binder()
        .safety
        .is_unsafe();
    for call in calls.0 {
        let ExprKind::Call(callee, _) = call.kind else { continue };
        let call_span = call.span.source_callsite();
        let inside = |span: Span| {
            let span = span.source_callsite();
            call_span.lo() <= span.lo() && span.hi() <= call_span.hi()
        };
        let own = uses
            .iter()
            .filter(|edit| inside(edit.span))
            .collect::<Vec<_>>();
        if own.len() < 2 {
            continue;
        }
        let reason = if own.iter().any(|edit| edit.bridge_kind != "subject-use") {
            Some("option-call-reborrow:non-dereference-use-inside-call")
        } else if own
            .iter()
            .any(|edit| inside(edit.span) && callee.span.contains(edit.span))
        {
            Some("option-call-reborrow:subject-in-callee-position")
        } else if own.iter().any(|edit| {
            !(edit.replacement.contains(".as_mut().unwrap()")
                || edit.replacement.contains(".as_deref_mut()"))
        }) {
            Some("option-call-reborrow:accessor-not-a-mutable-reborrow")
        } else {
            None
        };
        let own_spans = own
            .iter()
            .map(|edit| edit.span.source_callsite())
            .collect::<Vec<_>>();
        let all = super::construction::collect_composable_edits(table, call_span);
        // Everything inside the call that is not this subject's own accessor:
        // other subjects' edits, argument bridges, body adapters.
        let others = all
            .iter()
            .filter(|(span, _)| !own_spans.contains(span))
            .cloned()
            .collect::<Vec<_>>();
        let foreign_inside_bridge = others.iter().any(|(outer, _)| {
            others.iter().any(|(inner, _)| {
                inner != outer && outer.lo() <= inner.lo() && inner.hi() <= outer.hi()
            })
        });
        let original = sm.span_to_snippet(call_span).unwrap_or_default();
        let composed_text = if reason.is_some() {
            Err(String::new())
        } else if foreign_inside_bridge {
            Err("option-call-reborrow:nested-foreign-edits".to_owned())
        } else if original.is_empty() {
            Err("option-call-reborrow:call-text-unavailable".to_owned())
        } else {
            super::construction::compose_initializer(call_span, &original, &others)
                .map_err(|why| format!("option-call-reborrow:{why}"))
        };
        // A call that is not hoisted keeps its pre-existing per-access
        // rendering: that is not a failure of the Option family (the compiler
        // decides E0499 per call at verify time), so the skip is recorded on
        // the receipt's adapter and does not withdraw the owner.
        let (adapter, terminal) = match (reason, composed_text) {
            (Some(reason), _) => (format!("skipped:{reason}"), None),
            (None, Err(why)) => (format!("skipped:{why}"), None),
            (None, Ok(text)) => {
                let replacement =
                    format!("({{ let {name} = {name}.as_deref_mut().unwrap(); {text} }})");
                edits.push((
                    node,
                    UseEdit {
                        span: call_span,
                        replacement,
                        bridge_kind: "option-value-composed",
                    },
                ));
                composed.extend(all.iter().map(|(span, _)| (node, *span)));
                ("option-call-reborrow".to_owned(), None)
            }
        };
        let _ = unsafe_fn;
        receipts.push(super::option::receipt(
            tcx,
            subject,
            call.hir_id,
            MechanicalFamily::OptUseUnsupported,
            "call-reborrow",
            source,
            source,
            adapter,
            terminal,
            MechanicalEvidence::default(),
        ));
    }
}

/// Wave-6o (relay 009). A PARAMETER that some local caller passes the null
/// literal is nullable by that caller's evidence — the argument is the
/// parameter's construction site, and a null literal there is the same fact
/// as `let p = 0 as *mut T` at a local. The optional form follows (null =
/// `None`, the existing `null-argument` carrier renders the literal); a plain
/// reference at such a parameter would be `arg-null-literal` at the class
/// gate, which is what the corpus shows.
pub(super) fn param_receives_null_literal(facts: &EmitabilityFacts, subject: &Subject) -> bool {
    let SubjectKind::Param { hir_index } = subject.kind else { return false };
    facts.call_args.get(&subject.fn_did).is_some_and(|sites| {
        sites.iter().any(|site| {
            site.args
                .iter()
                .any(|arg| arg.index == hir_index && matches!(arg.shape, ArgShape::NullLit))
        })
    })
}
