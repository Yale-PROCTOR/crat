//! **wave-5d2 — locals whose type comes from their initializer's value.**
//!
//! `residual_reason` (`decision/mod.rs`) reports `copy-source-coupled` for an
//! unannotated local the ladder reached with no recognized construction: there
//! is no declared type to splice, and the local's type is whatever its
//! initializer produces. Wave-6k's `construction_values` already types one such
//! shape — a plain copy of a converting PARAMETER. This module types the shape
//! whose value needs no source at all:
//!
//! **A `'static` byte-string literal, directly or through a conditional whose
//! every arm is one** (`libtree::recurse`'s `bold_color` / `regular_color`,
//! `lil`'s `sep`): the C idiom `b"\x1B[0;35m\0" as *const u8 as *const c_char`.
//! Its referent is a `'static` array in the binary, so the local is a shared
//! reference with no extent question, no null (a literal is never null) and no
//! source to wait for. The initializer becomes `&*(<the original text>)` and
//! the binding is declared at the reference type, exactly as
//! `construction_values` does for its copies.
//!
//! Soundness: the pointee is `'static` and immutable; the deref reads a
//! literal that outlives every borrow, so the reborrow is valid for any
//! lifetime the binding needs. No extent is fabricated (the form is thin, and
//! a thin reference at a foreign counted position is refused by the existing
//! `held:thin-extent` gate, which runs before this one).

use rustc_hir::{ExprKind, HirId, Node, PatKind, def::Res};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    Ctx, Decision, DecisionTable, DeclShape, Subject, SubjectKind, box_facts::BoxShape,
    declaration, seam,
};
use crate::bo_rewriter::{
    additive::FamilyStage,
    bridge_receipt::{BridgeSitePlan, SignatureClassId},
};

struct LiteralValue {
    initializer: Span,
    pointee: String,
}

/// A local derived from another local by pointer arithmetic:
/// `let f = ff.offset(height * x);`
struct DerivedValue {
    /// The binding the arithmetic starts from.
    source: HirId,
    initializer: Span,
    /// The offset expression, verbatim.
    offset: Span,
    pointee: String,
    mutable: bool,
}

fn plain_shared_reference(decision: &Decision) -> bool {
    match decision {
        Decision::Ref { mutable } => !*mutable,
        Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::NestedSlice { .. }
        | Decision::Degraded(_) => false,
    }
}

/// Peel `as` casts and parentheses/`DropTemps` to the value the initializer
/// ultimately produces.
fn peel<'e>(mut expr: &'e rustc_hir::Expr<'e>) -> &'e rustc_hir::Expr<'e> {
    loop {
        match &expr.kind {
            ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) => expr = inner,
            _ => return expr,
        }
    }
}

/// Every value this expression can produce is a byte-string literal.
///
/// A conditional counts only when BOTH arms do (an `else`-less `if` produces
/// `()` on one path and never reaches here, but the `None` arm is refused
/// explicitly rather than by absence). A block counts by its tail expression
/// only when it has no statements — a statement could compute the value.
fn every_value_is_a_literal(expr: &rustc_hir::Expr<'_>) -> bool {
    match &peel(expr).kind {
        ExprKind::Lit(literal) => matches!(literal.node, rustc_ast::LitKind::ByteStr(..)),
        ExprKind::If(_, then, Some(otherwise)) => {
            every_value_is_a_literal(then) && every_value_is_a_literal(otherwise)
        }
        ExprKind::If(_, _, None) => false,
        ExprKind::Block(block, None) => {
            block.stmts.is_empty()
                && block
                    .expr
                    .is_some_and(|tail| every_value_is_a_literal(tail))
        }
        _ => false,
    }
}

fn literal_value(tcx: TyCtxt<'_>, subject: &Subject) -> Option<LiteralValue> {
    if subject.kind != SubjectKind::Local
        || subject.ty_span.is_some()
        || subject.decl_shape != DeclShape::RawPtr
        || subject.ptr_depth != 1
        || subject.null_init
    {
        return None;
    }
    let Node::LetStmt(local) = tcx.parent_hir_node(subject.hir_id) else {
        return None;
    };
    if !matches!(local.pat.kind, PatKind::Binding(_, hir, _, None) if hir == subject.hir_id)
        || local.ty.is_some()
    {
        return None;
    }
    let initializer = local.init?;
    if !every_value_is_a_literal(initializer) {
        return None;
    }
    let typeck = tcx.typeck(subject.fn_did);
    let input = typeck.pat_ty(local.pat);
    let TyKind::RawPtr(pointee, mutability) = input.kind() else {
        return None;
    };
    // A literal referent is read-only: a `*mut` binding over one would be a
    // write path this rule may not license.
    if mutability.is_mut()
        || typeck.expr_ty(initializer) != input
        || initializer.span.from_expansion()
        || subject.binding_span.from_expansion()
        || !declaration::pointee_is_nameable(tcx, subject.fn_did, *pointee)
    {
        return None;
    }
    Some(LiteralValue {
        initializer: initializer.span,
        pointee: declaration::pointee_source(tcx, *pointee),
    })
}

/// `base.offset(k)` over a LOCAL base, on an unannotated local of the same
/// pointer type. The offset's sign is not read here: a suffix view is licensed
/// by the source's own form and the index expression is carried verbatim, so a
/// negative offset fails the same bounds check the emitted program already
/// performs. (A negative offset on a raw pointer is UB in the input; §28.)
fn derived_value(tcx: TyCtxt<'_>, subject: &Subject) -> Option<DerivedValue> {
    if subject.kind != SubjectKind::Local
        || subject.ty_span.is_some()
        || subject.decl_shape != DeclShape::RawPtr
        || subject.ptr_depth != 1
        || subject.null_init
    {
        return None;
    }
    let Node::LetStmt(local) = tcx.parent_hir_node(subject.hir_id) else {
        return None;
    };
    if !matches!(local.pat.kind, PatKind::Binding(_, hir, _, None) if hir == subject.hir_id)
        || local.ty.is_some()
    {
        return None;
    }
    let initializer = local.init?;
    let ExprKind::MethodCall(segment, receiver, arguments, _) = &peel(initializer).kind else {
        return None;
    };
    if segment.ident.name.as_str() != "offset" || arguments.len() != 1 {
        return None;
    }
    let ExprKind::Path(path) = &receiver.kind else {
        return None;
    };
    let typeck = tcx.typeck(subject.fn_did);
    let Res::Local(source) = typeck.qpath_res(path, receiver.hir_id) else {
        return None;
    };
    let input = typeck.pat_ty(local.pat);
    let TyKind::RawPtr(pointee, mutability) = input.kind() else {
        return None;
    };
    // The derived binding and its base must be the same pointer type: a suffix
    // of the base's buffer, not a reinterpretation of it.
    if typeck.expr_ty(receiver) != input
        || initializer.span.from_expansion()
        || arguments[0].span.from_expansion()
        || subject.binding_span.from_expansion()
        || !declaration::pointee_is_nameable(tcx, subject.fn_did, *pointee)
    {
        return None;
    }
    Some(DerivedValue {
        source,
        initializer: initializer.span,
        offset: arguments[0].span,
        pointee: declaration::pointee_source(tcx, *pointee),
        mutable: mutability.is_mut(),
    })
}

/// The base of a derived local is a Box CANDIDATE of the ownership-fields
/// family (R436-3(a)): its own selection is blocked while this derived row is
/// degraded in the same class, so the candidate — not the settled decision —
/// is what types the view. The two rows then plan together and are withdrawn
/// together (the paired withdrawal, R436-3(b)).
fn derived_over_a_candidate(ctx: &Ctx<'_, '_>, subject: &Subject) -> Option<DerivedValue> {
    let value = derived_value(ctx.tcx, subject)?;
    let plan = ctx
        .ownership_fields
        .candidate_plan((subject.fn_did, value.source))?;
    (plan.shape == BoxShape::Slice && !plan.optional && plan.pointee_override.is_none())
        .then_some(value)
}

/// The decision-side half: such a local has a knowable type, so the residue
/// gate must not claim it.
pub(super) fn permits(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    ctx.family_policy
        .enabled(subject.fn_did, FamilyStage::Declaration)
        && (literal_value(ctx.tcx, subject).is_some()
            || derived_over_a_candidate(ctx, subject).is_some())
}

/// The form a derived local takes: a slice over the base's buffer, mutable
/// exactly when the binding is.
pub(super) fn derived_form(ctx: &Ctx<'_, '_>, subject: &Subject) -> Option<Decision> {
    derived_over_a_candidate(ctx, subject).map(|value| Decision::Slice {
        mutable: value.mutable,
        uses: Vec::new(),
    })
}

/// The emission half: the initializer becomes a reborrow of the literal and
/// the binding carries its reference type.
pub(super) fn complete(tcx: TyCtxt<'_>, table: &DecisionTable, plan: &mut seam::SeamPlan) {
    for (subject, decision) in &table.entries {
        if !plain_shared_reference(decision) {
            continue;
        }
        let Some(value) = literal_value(tcx, subject) else {
            continue;
        };
        let node = (subject.fn_did, subject.hir_id);
        if plan.raw_boundary_atom_groups.contains_key(&node) {
            continue;
        }
        let Ok(text) = tcx.sess.source_map().span_to_snippet(value.initializer) else {
            continue;
        };
        let spec = seam::GlueSpec::core(seam::GlueCore::Reborrow, false);
        let Some(replacement) = spec.render_in_context(&text, true) else {
            continue;
        };
        let Some(emitted_type) = declaration::emitted_type(decision, &value.pointee, None) else {
            continue;
        };
        // Another producer already owns this binding or this initializer.
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
            "static-literal-local",
        );
        bridge.expected_form = expected.key().to_owned();
        bridge.found_form = seam::Form::Raw.key().to_owned();
        bridge.argument_kind = "static-literal".to_owned();
        plan.body_edits.push(seam::BodyEdit {
            span: value.initializer,
            replacement,
            owner_class,
            bridge,
            owner_fn: tcx.def_path_str(subject.fn_did.to_def_id()),
            destination: subject.label.clone(),
            context: super::emitability::BodyAdapterContext::LocalInitializer,
            source_shape: "static-literal",
            family: seam::SeamFamily::Safe,
            spec,
            arg_span: value.initializer,
            expected,
            found: seam::Form::Raw,
            root_identity: "static-literal".to_owned(),
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

/// The emission half for a derived local: the initializer becomes a suffix
/// view of the base and the binding carries its slice type.
///
/// The candidate query is not available at seam time, and it does not need to
/// be: the ladder decided this local a slice only through `derived_form`,
/// which asked it. The base's own row is re-checked here all the same — it
/// must be the Box family's, selected (`Box`) or still held as a candidate
/// (`box-param-caller-unknown`) — so a later rule that decided some other
/// derived local a slice cannot borrow this emission.
pub(super) fn complete_derived(tcx: TyCtxt<'_>, table: &DecisionTable, plan: &mut seam::SeamPlan) {
    for (subject, decision) in &table.entries {
        let mutable = match decision {
            Decision::Slice { mutable, .. } => mutable,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Cursor { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => continue,
        };
        let Some(value) = derived_value(tcx, subject) else {
            continue;
        };
        let base_is_box_family = table.entries.iter().any(|(candidate, decision)| {
            candidate.fn_did == subject.fn_did
                && candidate.hir_id == value.source
                && match decision {
                    Decision::Box(_) => true,
                    // A base that is only HELD emits no indexable form, so a
                    // suffix view over it would not type-check. The held
                    // spelling was accepted here while the rule was designed
                    // against a blocked SELECTION; the measurement in report
                    // 019 shows the candidate is never produced at all, so
                    // the only sound base is a delivered Box.
                    Decision::Degraded(_)
                    | Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Cursor { .. }
                    | Decision::NestedSlice { .. }
                    | Decision::Slice { .. }
                    | Decision::Opt { .. } => false,
                }
        });
        if !base_is_box_family {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        if plan.raw_boundary_atom_groups.contains_key(&node) {
            continue;
        }
        let source_map = tcx.sess.source_map();
        let (Ok(base), Ok(offset)) = (
            source_map.span_to_snippet(value.initializer),
            source_map.span_to_snippet(value.offset),
        ) else {
            continue;
        };
        // `ff.offset(k)` — the base text is everything before `.offset(`.
        let Some(base) = base.split(".offset(").next().map(str::to_owned) else {
            continue;
        };
        let borrow = if *mutable { "&mut" } else { "&" };
        let replacement = format!("{borrow} {base}[({offset}) as usize..]");
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
            "derived-suffix-view",
        );
        bridge.expected_form = expected.key().to_owned();
        bridge.found_form = seam::Form::Raw.key().to_owned();
        bridge.argument_kind = "derived-offset".to_owned();
        plan.body_edits.push(seam::BodyEdit {
            span: value.initializer,
            replacement,
            owner_class,
            bridge,
            owner_fn: tcx.def_path_str(subject.fn_did.to_def_id()),
            destination: subject.label.clone(),
            context: super::emitability::BodyAdapterContext::LocalInitializer,
            source_shape: "derived-offset",
            family: seam::SeamFamily::Safe,
            spec: seam::GlueSpec::core(seam::GlueCore::Bare, *mutable),
            arg_span: value.initializer,
            expected,
            found: seam::Form::Raw,
            root_identity: "derived-offset".to_owned(),
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

/// The custody predicate for this rule's locals, the twin of
/// `construction_values::has_declaration`.
pub(crate) fn has_declaration(table: &DecisionTable, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    subject.ty_span.is_none()
        && table.seams.explicit_declarations.iter().any(|site| {
            site.node == Some(node)
                && site.category == "local"
                && site.owner_class == SignatureClassId::of(subject.fn_did)
        })
        && table.seams.body_edits.iter().any(|edit| {
            edit.destination == subject.label
                && matches!(
                    edit.bridge.bridge_kind.as_str(),
                    "static-literal-local" | "derived-suffix-view"
                )
        })
}
