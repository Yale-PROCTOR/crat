//! Unannotated slice locals with a sealed construction plan get an explicit
//! declaration: `let d = base.offset(k);` → `let d: &mut [T] = <construction>;`.
//! The value is item 2's own constructor (evidence-backed length or the §77
//! fallback with its receipt); only the missing splice target is supplied.

use rustc_hir::{Node, PatKind};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{Ctx, Decision, DeclShape, Subject, SubjectKind, construction, declaration, seam};
use crate::bo_rewriter::{additive::FamilyStage, bridge_receipt::SignatureClassId};

/// The declaration shape this rule supplies a type for: a plain by-value
/// binding of a raw pointer local, unannotated, with an initializer, whose
/// pointee can be named at the declaration.
pub(crate) fn emitted_type(tcx: TyCtxt<'_>, subject: &Subject, mutable: bool) -> Option<String> {
    if subject.kind != SubjectKind::Local
        || subject.ty_span.is_some()
        || subject.decl_shape != DeclShape::RawPtr
        || subject.ptr_depth != 1
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
    if !declaration::pointee_is_nameable(tcx, subject.fn_did, *pointee) {
        return None;
    }
    declaration::emitted_type(
        &Decision::Slice {
            mutable,
            uses: Vec::new(),
        },
        &declaration::pointee_source(tcx, *pointee),
        None,
    )
}

fn slice_mutability(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Slice { mutable, .. } => Some(*mutable),
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => None,
    }
}

/// The Slice arm's own need and licence: every raw-only use is arithmetic
/// (the need) and fatness concludes array (the licence). A thin candidate
/// keeps its residual reason; this rule never speaks for it.
fn slice_form_evidence(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    ctx.facts.raw_only_uses.get(&node).is_some_and(|uses| {
        !uses.is_empty()
            && uses
                .iter()
                .all(|(op, _)| super::emitability::SLICE_ARITHMETIC_OPS.contains(&op.as_str()))
    }) && ctx.fat.is_array(subject.fn_did, subject.local)
}

pub(super) fn permits(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    ctx.family_policy
        .enabled(subject.fn_did, FamilyStage::Declaration)
        && ctx
            .family_policy
            .enabled(subject.fn_did, FamilyStage::SliceConstruction)
        && construction::slice_constructor_available(ctx.constructions, node)
        && slice_form_evidence(ctx, subject)
        && emitted_type(ctx.tcx, subject, subject.mutable).is_some()
}

/// After item 2 has sealed the construction plans: every unannotated slice
/// local whose plan rendered a value gets its explicit declaration.
pub(crate) fn append_declarations(tcx: TyCtxt<'_>, table: &mut super::DecisionTable) {
    let mut sites = Vec::new();
    for (subject, decision) in &table.entries {
        let Some(mutable) = slice_mutability(decision) else { continue };
        let node = (subject.fn_did, subject.hir_id);
        if !table
            .slice_constructions
            .iter()
            .any(|plan| plan.node == node && plan.replacement.is_some())
        {
            continue;
        }
        let Some(emitted_type) = emitted_type(tcx, subject, mutable) else { continue };
        if table
            .seams
            .explicit_declarations
            .iter()
            .any(|site| site.node == Some(node))
        {
            continue;
        }
        sites.push(seam::ExplicitDeclarationSite {
            owner_class: SignatureClassId::of(subject.fn_did),
            caller: subject.fn_did,
            node: Some(node),
            span: Some(subject.binding_span.shrink_to_hi()),
            category: "local",
            replacement: Some(format!(": {emitted_type}")),
            emitted_type,
            arm: "surface",
        });
    }
    table.seams.explicit_declarations.extend(sites);
}

/// An unannotated slice local whose value is a rendered construction plan and
/// whose type is an explicit local declaration site.
pub(crate) fn has_declaration(table: &super::DecisionTable, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    subject.ty_span.is_none()
        && table
            .slice_constructions
            .iter()
            .any(|plan| plan.node == node && plan.replacement.is_some())
        && table.seams.explicit_declarations.iter().any(|site| {
            site.node == Some(node)
                && site.category == "local"
                && site.owner_class == SignatureClassId::of(subject.fn_did)
        })
}
