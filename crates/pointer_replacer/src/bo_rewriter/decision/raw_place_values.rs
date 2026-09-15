//! Thin references from raw places that are valid by construction on a
//! UB-free input: a raw struct-field read (`let t = (*it)._table;`). The
//! value is the reborrow bridge `&*init` / `&mut *init` with an explicit
//! declaration; the local dies at function end (the ladder's escape and
//! retention gates ran). A static byte-string literal is NOT a source: its
//! consumers (`sprintf`, `strlen`, `strcpy`) read to the NUL, and the ladder's
//! thin-extent gate holds such a thin reference (R272-1) — the right hold.

use rustc_hir::{Expr, ExprKind, Node, PatKind, QPath, UnOp, def::Res};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{Ctx, Decision, DeclShape, Subject, SubjectKind, declaration, seam};
use crate::bo_rewriter::{
    additive::FamilyStage,
    bridge_receipt::{BridgeSitePlan, SignatureClassId},
};

const BRIDGE_KIND: &str = "raw-place-reborrow";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Source {
    /// `(*p).field` / `p.field` chains over one local: the field holds a
    /// pointer the input dereferences through this local.
    FieldRead,
}

pub(crate) struct RawPlaceValue {
    pub(crate) source: Source,
    pub(crate) initializer: Span,
    pub(crate) pointee: String,
}

fn peel<'a>(mut expr: &'a Expr<'a>) -> &'a Expr<'a> {
    while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Type(inner, _) =
        expr.kind
    {
        expr = inner;
    }
    expr
}

fn is_local_path(typeck: &rustc_middle::ty::TypeckResults<'_>, expr: &Expr<'_>) -> bool {
    matches!(&expr.kind, ExprKind::Path(path @ QPath::Resolved(..))
        if matches!(typeck.qpath_res(path, expr.hir_id), Res::Local(_)))
}

fn field_read(typeck: &rustc_middle::ty::TypeckResults<'_>, expr: &Expr<'_>) -> bool {
    match expr.kind {
        ExprKind::Field(base, _) => match base.kind {
            ExprKind::Field(..) => field_read(typeck, base),
            ExprKind::Unary(UnOp::Deref, inner) => is_local_path(typeck, inner),
            _ => is_local_path(typeck, base),
        },
        _ => false,
    }
}

pub(crate) fn value(tcx: TyCtxt<'_>, subject: &Subject) -> Option<RawPlaceValue> {
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
    let peeled = peel(initializer);
    if !field_read(typeck, peeled) {
        return None;
    }
    let source = Source::FieldRead;
    Some(RawPlaceValue {
        source,
        initializer: initializer.span,
        pointee: declaration::pointee_source(tcx, *pointee),
    })
}

fn plain_reference(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Ref { mutable } => Some(*mutable),
        Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => None,
    }
}

fn compatible(value: &RawPlaceValue, _mutable: bool) -> bool {
    value.source == Source::FieldRead
}

pub(super) fn permits(ctx: &Ctx<'_, '_>, subject: &Subject, mutable: bool) -> bool {
    ctx.family_policy
        .enabled(subject.fn_did, FamilyStage::Declaration)
        && value(ctx.tcx, subject).is_some_and(|value| compatible(&value, mutable))
}

pub(super) fn complete(tcx: TyCtxt<'_>, table: &super::DecisionTable, plan: &mut seam::SeamPlan) {
    for (subject, decision) in &table.entries {
        let Some(mutable) = plain_reference(decision) else { continue };
        let Some(value) = value(tcx, subject) else { continue };
        if !compatible(&value, mutable) {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        if plan.raw_boundary_atom_groups.contains_key(&node) {
            continue;
        }
        let Ok(text) = tcx.sess.source_map().span_to_snippet(value.initializer) else { continue };
        let spec = seam::GlueSpec::core(seam::GlueCore::Reborrow, mutable);
        let Some(replacement) = spec.render_in_context(&text, true) else { continue };
        let Some(emitted_type) = declaration::emitted_type(decision, &value.pointee, None) else {
            continue;
        };
        if plan
            .body_edits
            .iter()
            .any(|edit| edit.span == value.initializer)
            || plan
                .explicit_declarations
                .iter()
                .any(|site| site.node == Some(node))
        {
            continue;
        }
        let owner_class = SignatureClassId::of(subject.fn_did);
        let expected = seam::form_of(decision);
        let mut bridge = BridgeSitePlan::local(
            subject.fn_did,
            subject.fn_did,
            "glue",
            "body:local-initializer",
            BRIDGE_KIND,
        );
        bridge.expected_form = expected.key().to_owned();
        bridge.found_form = "raw".to_owned();
        bridge.argument_kind = match value.source {
            Source::FieldRead => "raw-field-read",
        }
        .to_owned();
        plan.body_edits.push(seam::BodyEdit {
            span: value.initializer,
            replacement,
            owner_class,
            bridge,
            owner_fn: tcx.def_path_str(subject.fn_did.to_def_id()),
            destination: subject.label.clone(),
            context: super::emitability::BodyAdapterContext::LocalInitializer,
            source_shape: match value.source {
                Source::FieldRead => "raw-field-read",
            },
            family: seam::SeamFamily::Safe,
            spec,
            arg_span: value.initializer,
            expected,
            found: seam::Form::Raw,
            root_identity: subject.label.clone(),
            blind: false,
        });
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
        && table
            .seams
            .body_edits
            .iter()
            .any(|edit| edit.destination == subject.label && edit.bridge.bridge_kind == BRIDGE_KIND)
}
