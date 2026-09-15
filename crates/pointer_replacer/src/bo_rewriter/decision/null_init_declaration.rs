//! Wave-6o. The inserted declaration type for an UNANNOTATED null-initialized
//! local that the analysis decided a thin `Opt`:
//!
//! ```text
//! let mut val = 0 as *mut T;      ->      let mut val: Option<&mut T> = None;
//! let mut s = 0 as *const u8;     ->      let mut s: Option<&[u8]> = None;
//! ```
//!
//! `decide_one` vetoes every emitting decision on a local without a declared
//! type because nothing splices it; this module supplies the splice — the
//! type is rendered from the DECISION over the binding's own compiler type
//! (`declaration::emitted_type`), never guessed, and placed by the existing
//! `ExplicitLocalDeclVisitor` through a `category = "local"` explicit
//! declaration site, exactly as an inferred callee-return receiver is.
//!
//! Admitted only where the pointee is nameable from the owner, the pattern is
//! a plain binding, the local is not a callee-return receiver (that carrier
//! owns its own declaration) and the Declaration family is enabled for the
//! owner. An optional slice's declaration names no extent; its value plan
//! carries the extent (evidence-backed or the receipted fallback).

use rustc_hir::{Node, PatKind};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    Ctx, Decision, DecisionTable, Subject, SubjectKind,
    declaration::{emitted_type, pointee_is_nameable, pointee_source},
};
use crate::bo_rewriter::{
    additive::FamilyStage, bridge_receipt::SignatureClassId,
    decision::seam::ExplicitDeclarationSite,
};

/// An optional — thin, or a slice (relay 010: brotli's static-dictionary
/// `let mut s = 0 as *const u8; … s = &*data.offset(l) as *const u8;`
/// locals, whose form is `Option<&[u8]>`; the slice VALUE plan is the
/// existing nullable-slice construction or wave-6s's view) — is admitted;
/// every other disposition keeps the veto.
fn thin_optional(decision: &Decision) -> bool {
    match decision {
        Decision::Opt { .. } => true,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Cursor { .. }
        | Decision::Box(_)
        | Decision::Degraded(_) => false,
    }
}

/// The decision ladder's answer may stand for an unannotated local when its
/// declaration can be inserted by [`explicit_declaration`].
pub(crate) fn admits(ctx: &Ctx<'_, '_>, subject: &Subject, decision: &Decision) -> bool {
    subject.ty_span.is_none()
        && matches!(subject.kind, SubjectKind::Local)
        && subject.null_init
        && thin_optional(decision)
        && ctx
            .family_policy
            .enabled(subject.fn_did, FamilyStage::Declaration)
        && !ctx
            .declaration_patterns
            .contains_key(&(subject.fn_did, subject.hir_id))
        && ctx.return_receivers.is_none_or(|receivers| {
            !receivers
                .plans
                .contains_key(&(subject.fn_did, subject.hir_id))
        })
        && rendered_type(ctx.tcx, subject, decision).is_some()
}

/// `Option<&T>` / `Option<&mut T>` from the binding's own raw type.
fn rendered_type(tcx: TyCtxt<'_>, subject: &Subject, decision: &Decision) -> Option<String> {
    let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { return None };
    if !matches!(pattern.kind, PatKind::Binding(..)) {
        return None;
    }
    let TyKind::RawPtr(pointee, _) = tcx.typeck(subject.fn_did).pat_ty(pattern).kind() else {
        return None;
    };
    if !pointee_is_nameable(tcx, subject.fn_did, *pointee) {
        return None;
    }
    emitted_type(decision, &pointee_source(tcx, *pointee), None)
}

/// One explicit declaration site per admitted subject, carried by the owner's
/// own signature class.
pub(crate) fn explicit_declaration(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    subject: &Subject,
    decision: &Decision,
) -> Option<ExplicitDeclarationSite> {
    let node = (subject.fn_did, subject.hir_id);
    if subject.ty_span.is_some()
        || !matches!(subject.kind, SubjectKind::Local)
        || !subject.null_init
        || !thin_optional(decision)
        || table.declaration_patterns.contains_key(&node)
        || table.return_receivers.plans.contains_key(&node)
    {
        return None;
    }
    let emitted_type = rendered_type(tcx, subject, decision)?;
    let name = subject.param_name.as_deref()?;
    let binding_prefix = if table.option_mut_bindings.contains(&node) && !subject.mut_binding {
        "mut "
    } else {
        ""
    };
    Some(ExplicitDeclarationSite {
        owner_class: SignatureClassId::of(subject.fn_did),
        caller: subject.fn_did,
        node: Some(node),
        span: Some(subject.binding_span),
        category: "local",
        replacement: Some(format!("{binding_prefix}{name}: {emitted_type}")),
        emitted_type,
        arm: "glue",
    })
}

/// The site [`append_explicit_declarations`] recorded for this subject, if any.
pub(crate) fn has_explicit_declaration(
    table: &DecisionTable,
    subject: &Subject,
    decision: &Decision,
) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    subject.ty_span.is_none()
        && subject.null_init
        && thin_optional(decision)
        && table.seams.explicit_declarations.iter().any(|site| {
            site.category == "local"
                && site.node == Some(node)
                && site.owner_class == SignatureClassId::of(subject.fn_did)
        })
}

pub(crate) fn append_explicit_declarations(tcx: TyCtxt<'_>, table: &mut DecisionTable) {
    let declarations = table
        .entries
        .iter()
        .filter_map(|(subject, decision)| explicit_declaration(tcx, table, subject, decision))
        .collect::<Vec<_>>();
    table.seams.explicit_declarations.extend(declarations);
}
