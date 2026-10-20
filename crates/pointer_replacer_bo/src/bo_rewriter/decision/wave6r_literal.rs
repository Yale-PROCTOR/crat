//! Shared-origin safety guard for call-site mutable-reference adapters.

use rustc_hash::FxHashSet;
use rustc_hir::{Expr, ExprKind, intravisit};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::super::seam::{BlockedSeam, Form, SeamBlock, SeamPlan};
use crate::bo_rewriter::bridge_receipt::BridgeCalleeId;

fn needs_mutable_reference(form: Form) -> bool {
    matches!(
        form,
        Form::Ref { mutable: true }
            | Form::Slice { mutable: true }
            | Form::Opt { mutable: true, .. }
            | Form::Cursor { mutable: true }
            | Form::NestedSlice { mutable: true, .. }
    )
}

/// A raw pointer cast does not grant write permission over a shared referent.
/// Hold the callee class before AST construction, including byte/string literal
/// origins whose `&[u8; N]` type is otherwise hidden by multiple pointer casts.
pub(super) fn hold_shared_origins(tcx: TyCtxt<'_>, plan: &mut SeamPlan) {
    struct Origins<'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: rustc_hir::def_id::LocalDefId,
        shared: FxHashSet<Span>,
    }
    impl<'tcx> intravisit::Visitor<'tcx> for Origins<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            let mut origin = expr;
            while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) = origin.kind {
                origin = inner;
            }
            if matches!(self.tcx.typeck(self.owner).expr_ty(origin).kind(),
                TyKind::Ref(_, _, permission) if !permission.is_mut())
            {
                self.shared.insert(expr.span);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut shared = FxHashSet::default();
    let callers: FxHashSet<_> = plan
        .edits
        .iter()
        .filter(|edit| edit.found == Form::Raw && needs_mutable_reference(edit.expected))
        .map(|edit| edit.bridge.caller)
        .collect();
    for owner in callers {
        let Some(body) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        let mut origins = Origins {
            tcx,
            owner,
            shared: Default::default(),
        };
        intravisit::Visitor::visit_body(&mut origins, tcx.hir_body(body));
        shared.extend(origins.shared);
    }
    plan.edits.retain(|edit| {
        if edit.found != Form::Raw
            || !needs_mutable_reference(edit.expected)
            || !shared.contains(&edit.span)
        {
            return true;
        }
        let BridgeCalleeId::Local(callee) = edit.bridge.callee else { return true };
        plan.blocked.push(BlockedSeam {
            caller: edit.bridge.caller,
            callee,
            index: edit.param_index,
            span: edit.span,
            block: SeamBlock::SharedToMut,
            expected: Some(edit.expected),
            found: Some(edit.found),
            source_shape: edit.source_shape,
            candidate_template: edit.spec.template_key().to_owned(),
            null_arm: edit.spec.null_arm_key().to_owned(),
            extent_arm: edit.spec.extent_arm_key().to_owned(),
            root_identity: edit.root_identity.clone(),
            blind: edit.blind,
            peers: Vec::new(),
            overlap: edit.overlap.clone(),
        });
        false
    });
}

#[cfg(test)]
#[path = "wave6r_literal_tests.rs"]
mod tests;
