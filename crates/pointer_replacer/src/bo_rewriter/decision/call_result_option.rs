//! **W6L-A8-1 (relay 026, R480-4): the receiver-side null adapter.**
//!
//! The `return-not-adapted` row's largest shape is an UNANNOTATED local that
//! takes a LOCAL callee's RAW pointer return, null-tests it, and reads or
//! writes the pointee — lil `add_func`/`lil_register`, binn
//! `binn_alloc_item`, urlparser `url_get_protocol` (11 of the 15 readable
//! rows at batch 18). The form selection above already calls such a subject
//! `Opt` by the program's own null test; what is missing is a DECLARATION
//! channel, so the ladder's residual gate degrades it and
//! [`super::residual_reason`] names the owed capability from the constructor:
//! a call result, hence `return-not-adapted`.
//!
//! This is that channel, and it owes nothing to the callee: the value is the
//! raw pointer's own `as_mut()` / `as_ref()` — the null-to-Option API, already
//! in the glue vocabulary as [`seam::GlueCore::RawOption`] — and the
//! declaration is `Option<&mut T>` / `Option<&T>`. The callee keeps its raw
//! return, so no class of the callee's moves.
//!
//! **The view is untied** (`as_mut()` infers an unbounded lifetime), which is
//! R401-8's shape and carries R401-8's guard: the local may not escape. Here
//! the guard is stated positively as a closed use vocabulary — the null test,
//! a deref, a field access — so a returned, stored or handed-on local is
//! refused rather than manufactured. That keeps the untied view inside the
//! frame that created it, which is what makes it safe on a UB-free input.

use rustc_hir::{
    Expr, ExprKind, HirId, Node, PatKind, QPath, UnOp,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{Ctx, Decision, DeclShape, Subject, SubjectKind, declaration, seam};
use crate::bo_rewriter::{additive::FamilyStage, bridge_receipt::SignatureClassId};

pub(crate) struct CallResultValue {
    pub(crate) initializer: Span,
    pub(crate) pointee: String,
    pub(crate) callee: LocalDefId,
}

fn peel<'a>(mut expr: &'a Expr<'a>) -> &'a Expr<'a> {
    while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Type(inner, _) =
        expr.kind
    {
        expr = inner;
    }
    expr
}

/// The initializer is an exact direct call to a function with a body in this
/// crate. An indirect call (a function pointer) and a foreign callee are both
/// refused: the first has no single callee to reason about, and the second is
/// the allocator families' value, not this one's.
fn local_callee(tcx: TyCtxt<'_>, expr: &Expr<'_>) -> Option<LocalDefId> {
    let ExprKind::Call(function, _) = peel(expr).kind else { return None };
    let ExprKind::Path(QPath::Resolved(_, path)) = function.kind else { return None };
    let Res::Def(DefKind::Fn, did) = path.res else { return None };
    let local = did.as_local()?;
    // A declaration inside `unsafe extern "C" { .. }` is `DefKind::Fn` and IS
    // `as_local` — the extern block belongs to this crate. "Local" here means
    // a function with a BODY (wave-6a's R410-9 (b) rule, same words): a
    // foreign result carries a contract this arm does not read, and belongs to
    // the contract families. Measured: without this, libtree's `strchr` row
    // types itself (`w6l_a8_foreign_callee_result_is_refused`).
    tcx.hir_node_by_def_id(local).body_id().map(|_| local)
}

/// The closed use vocabulary. Every use of the local must be one the Option
/// form has an image for AND one that keeps the view inside this frame: the
/// null test, a dereference (`*cmd`, `(*cmd).field`), or a field access. A
/// `return`, a store, a cast and a call argument are all refused here.
struct Uses<'tcx> {
    tcx: TyCtxt<'tcx>,
    binding: HirId,
    ok: bool,
    seen_null_test: bool,
}

impl<'tcx> Uses<'tcx> {
    fn is_the_local(&self, expr: &Expr<'_>) -> bool {
        matches!(expr.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Local(hir) if hir == self.binding))
    }
}

impl<'tcx> Visitor<'tcx> for Uses<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::MethodCall(segment, receiver, args, _)
                if self.is_the_local(receiver) && segment.ident.name.as_str() == "is_null" =>
            {
                self.seen_null_test = true;
                for arg in args {
                    intravisit::walk_expr(self, arg);
                }
                return;
            }
            ExprKind::Unary(UnOp::Deref, inner) if self.is_the_local(inner) => return,
            ExprKind::Field(base, _) if self.is_the_local(base) => return,
            _ => {}
        }
        if self.is_the_local(expr) {
            // A use this vocabulary does not name.
            self.ok = false;
            return;
        }
        intravisit::walk_expr(self, expr);
    }
}

fn uses_are_closed(tcx: TyCtxt<'_>, subject: &Subject) -> bool {
    let Some(body_id) = tcx.hir_node_by_def_id(subject.fn_did).body_id() else { return false };
    let mut uses = Uses {
        tcx,
        binding: subject.hir_id,
        ok: true,
        seen_null_test: false,
    };
    uses.visit_body(tcx.hir_body(body_id));
    uses.ok && uses.seen_null_test
}

pub(crate) fn value(tcx: TyCtxt<'_>, subject: &Subject) -> Option<CallResultValue> {
    if subject.kind != SubjectKind::Local
        || subject.ty_span.is_some()
        || subject.decl_shape != DeclShape::RawPtr
        || subject.ptr_depth != 1
        || subject.null_init
        || subject.binding_span.from_expansion()
    {
        return None;
    }
    let Node::LetStmt(local) = tcx.parent_hir_node(subject.hir_id) else { return None };
    let PatKind::Binding(mode, hir, _, None) = local.pat.kind else { return None };
    if hir != subject.hir_id || mode.0 != rustc_hir::ByRef::No || local.ty.is_some() {
        return None;
    }
    let initializer = local.init?;
    if initializer.span.from_expansion() {
        return None;
    }
    let typeck = tcx.typeck(subject.fn_did);
    let TyKind::RawPtr(pointee, _) = typeck.pat_ty(local.pat).kind() else { return None };
    if typeck.expr_ty(initializer) != typeck.pat_ty(local.pat)
        || !declaration::pointee_is_nameable(tcx, subject.fn_did, *pointee)
    {
        return None;
    }
    let callee = local_callee(tcx, initializer)?;
    // The callee's own return must still be RAW. A converted return is the
    // return receiver's value (`raw_receiver`), and re-adapting it with
    // `as_mut()` would be ill-typed.
    let signature = tcx.fn_sig(callee.to_def_id()).skip_binder().skip_binder();
    if !matches!(signature.output().kind(), TyKind::RawPtr(..)) {
        return None;
    }
    if !uses_are_closed(tcx, subject) {
        return None;
    }
    Some(CallResultValue {
        initializer: initializer.span,
        pointee: declaration::pointee_source(tcx, *pointee),
        callee,
    })
}

fn thin_optional(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Opt {
            mutable,
            slice: false,
            ..
        } => Some(*mutable),
        Decision::Opt { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => None,
    }
}

pub(super) fn permits(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    ctx.family_policy
        .enabled(subject.fn_did, FamilyStage::Declaration)
        && value(ctx.tcx, subject).is_some()
}

pub(super) fn complete(tcx: TyCtxt<'_>, table: &super::DecisionTable, plan: &mut seam::SeamPlan) {
    for (subject, decision) in &table.entries {
        let Some(mutable) = thin_optional(decision) else { continue };
        let Some(value) = value(tcx, subject) else { continue };
        let node = (subject.fn_did, subject.hir_id);
        if plan.raw_boundary_atom_groups.contains_key(&node) {
            continue;
        }
        let Some(emitted_type) = declaration::emitted_type(decision, &value.pointee, None) else {
            continue;
        };
        // The Option family already renders this initializer's value — the raw
        // pointer's own `as_mut()` under a cast to the pointee. Only the
        // declaration is missing, so only the declaration is planned here; a
        // second adapter would compose over the first (measured: a doubled
        // `as_mut()`, `E0605`).
        if plan
            .explicit_declarations
            .iter()
            .any(|site| site.node == Some(node))
        {
            continue;
        }
        let owner_class = SignatureClassId::of(subject.fn_did);
        let _ = (mutable, value.callee);
        plan.explicit_declarations
            .push(seam::ExplicitDeclarationSite {
                owner_class,
                caller: subject.fn_did,
                node: Some(node),
                span: Some(subject.binding_span.shrink_to_hi()),
                category: "local",
                replacement: Some(format!(": {emitted_type}")),
                emitted_type,
                arm: "surface",
            });
    }
}

pub(crate) fn has_declaration(table: &super::DecisionTable, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    subject.ty_span.is_none()
        && table.seams.explicit_declarations.iter().any(|site| {
            site.node == Some(node)
                && site.category == "local"
                && site.owner_class == SignatureClassId::of(subject.fn_did)
        })
}
