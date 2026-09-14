//! Use images for the optional-slice revert class.

#[path = "wave6r_literal.rs"]
mod literal;

use rustc_hir::{Expr, ExprKind, Node, QPath, UnOp, def::Res, intravisit};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::{Subject, emitability::UseEdit};

/// Keep a raw argument's original cast, and erase an identity raw cast only
/// when its destination already has an admitted reference presentation. Both
/// operations carry their original operand span to the common AST consumer.
pub(super) fn complete_casts(
    tcx: TyCtxt<'_>,
    table: &super::DecisionTable,
    plan: &mut super::seam::SeamPlan,
) {
    literal::hold_shared_origins(tcx, plan);

    use rustc_middle::ty::TyKind;

    use super::seam::{BodyEdit, Form, GlueCore, GlueSpec, SeamFamily};
    use crate::bo_rewriter::bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, BridgeSitePlan, SignatureClassId,
    };

    for edit in &mut plan.edits {
        if edit.found != Form::Raw
            || edit.source_shape != "cast-of-local"
            || edit.raw_outbound.is_some()
        {
            continue;
        }
        let Some((owner, binding)) = edit.source_node else { continue };
        let Node::Pat(pattern) = tcx.hir_node(binding) else { continue };
        let TyKind::RawPtr(source_pointee, _) = *tcx.typeck(owner).pat_ty(pattern).kind() else {
            continue;
        };
        let BridgeCalleeId::Local(callee) = edit.bridge.callee else { continue };
        let signature = tcx.fn_sig(callee.to_def_id()).skip_binder().skip_binder();
        let Some(target) = signature.inputs().get(edit.param_index) else { continue };
        let TyKind::RawPtr(target_pointee, _) = *target.kind() else { continue };
        if source_pointee == target_pointee {
            continue;
        }
        // The original cast supplies the target pointee of RawOption/Reborrow.
        // Peeling it would construct a reference to the raw source's pointee.
        if let Ok(text) = tcx.sess.source_map().span_to_snippet(edit.span)
            && let Some(replacement) = edit.spec.render_in_context(
                &text,
                tcx.fn_sig(edit.bridge.caller.to_def_id())
                    .skip_binder()
                    .skip_binder()
                    .safety
                    .is_unsafe(),
            )
        {
            edit.arg_span = edit.span;
            edit.replacement = replacement;
        }
    }

    for (subject, decision) in &table.entries {
        let mutable = match decision {
            super::Decision::Ref { mutable } => mutable,
            super::Decision::InferredRef { .. }
            | super::Decision::Cursor { .. }
            | super::Decision::NestedSlice { .. }
            | super::Decision::Slice { .. }
            | super::Decision::Opt { .. }
            | super::Decision::Box(_)
            | super::Decision::Degraded(_) => continue,
        };
        if subject.kind != super::SubjectKind::Local {
            continue;
        }
        let Node::LetStmt(local) = tcx.parent_hir_node(subject.hir_id) else { continue };
        let Some(initializer) = local.init else { continue };
        let ExprKind::Cast(reference, _) = initializer.kind else { continue };
        if !matches!(
            reference.kind,
            ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, _, _)
        ) {
            continue;
        }
        let typeck = tcx.typeck(subject.fn_did);
        let TyKind::Ref(_, pointee, permission) = *typeck.expr_ty(reference).kind() else {
            continue;
        };
        let TyKind::RawPtr(cast_pointee, _) = *typeck.expr_ty(initializer).kind() else { continue };
        let TyKind::RawPtr(destination_pointee, _) = *typeck.pat_ty(local.pat).kind() else {
            continue;
        };
        if pointee != cast_pointee
            || pointee != destination_pointee
            || (*mutable && !permission.is_mut())
            || plan
                .body_edits
                .iter()
                .any(|edit| edit.span == initializer.span)
        {
            continue;
        }
        let Ok(replacement) = tcx.sess.source_map().span_to_snippet(reference.span) else {
            continue;
        };
        let expected = Form::Ref { mutable: *mutable };
        let found = Form::Ref {
            mutable: permission.is_mut(),
        };
        let owner_class = SignatureClassId::of(subject.fn_did);
        plan.body_blocked
            .retain(|row| row.owner_class != owner_class || row.span != initializer.span);
        plan.body_edits.push(BodyEdit {
            span: initializer.span,
            replacement,
            owner_class,
            bridge: BridgeSitePlan {
                caller: subject.fn_did,
                callee: BridgeCalleeId::Local(subject.fn_did),
                arm: "glue".to_owned(),
                position: "body:local-initializer".to_owned(),
                bridge_kind: "reference-identity-cast".to_owned(),
                expected_form: expected.key().to_owned(),
                found_form: found.key().to_owned(),
                argument_kind: "addr-of-cast".to_owned(),
                extent: BridgeExtentKind::None,
                retention: BridgeRetentionTier::None,
                waiver_id: None,
                unsafe_context: None,
            },
            owner_fn: tcx.def_path_str(subject.fn_did.to_def_id()),
            destination: subject.label.clone(),
            context: super::emitability::BodyAdapterContext::LocalInitializer,
            source_shape: "addr-of-cast",
            family: SeamFamily::Safe,
            spec: GlueSpec::core(GlueCore::Bare, *mutable),
            arg_span: reference.span,
            expected,
            found,
            root_identity: "-".to_owned(),
            blind: true,
        });
    }
}

/// A dereference selects one element even when its optional carrier holds a
/// slice. Choose this image only after the actual emitted form is settled:
/// fatness alone also describes subjects that still emit a thin reference.
pub(super) fn optional_uses(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    slice: bool,
    mut edits: Vec<UseEdit>,
) -> Vec<UseEdit> {
    if !slice {
        return edits;
    }
    struct Dereferences<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        subject: &'a Subject,
        spans: rustc_hash::FxHashMap<Span, Span>,
    }
    impl<'tcx> intravisit::Visitor<'tcx> for Dereferences<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if matches!(expr.kind, ExprKind::Path(QPath::Resolved(_, path))
                if path.res == Res::Local(self.subject.hir_id))
                && let Node::Expr(parent) = self.tcx.parent_hir_node(expr.hir_id)
                && matches!(parent.kind, ExprKind::Unary(UnOp::Deref, _))
            {
                self.spans.insert(expr.span, parent.span);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut dereferences = Dereferences {
        tcx,
        subject,
        spans: Default::default(),
    };
    if let Some(body) = tcx.hir_node_by_def_id(subject.fn_did).body_id() {
        intravisit::Visitor::visit_body(&mut dereferences, tcx.hir_body(body));
    }
    for edit in &mut edits {
        if edit.bridge_kind == "subject-use"
            && let Some(&deref) = dereferences.spans.get(&edit.span)
        {
            edit.span = deref;
            edit.replacement = format!("({})[0]", edit.replacement);
        }
    }
    edits
}
