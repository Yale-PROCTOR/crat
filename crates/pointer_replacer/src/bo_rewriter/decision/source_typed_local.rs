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

use rustc_hir::{ExprKind, HirId, Node, PatKind, def::Res, def_id::LocalDefId};
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
///
/// **The whole recognizer is HIR-only** (`derived_view`), because it is also
/// the predicate ownership-fields' source scan consumes: it must answer for a
/// binding their scan holds, at a point where no `Subject` exists yet. The
/// subject-side entry adds only the collector's own guards, and both go
/// through the same body so the two answers cannot drift.
fn derived_view(tcx: TyCtxt<'_>, owner: LocalDefId, binding: HirId) -> Option<DerivedValue> {
    let Node::LetStmt(local) = tcx.parent_hir_node(binding) else {
        return None;
    };
    if !matches!(local.pat.kind, PatKind::Binding(_, hir, _, None) if hir == binding)
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
    let typeck = tcx.typeck(owner);
    let Res::Local(source) = typeck.qpath_res(path, receiver.hir_id) else {
        return None;
    };
    let input = typeck.pat_ty(local.pat);
    let TyKind::RawPtr(pointee, mutability) = input.kind() else {
        return None;
    };
    // Depth 1 only: an inner raw pointer is a different subject's question.
    if matches!(pointee.kind(), TyKind::RawPtr(..)) {
        return None;
    }
    // The derived binding and its base must be the same pointer type: a suffix
    // of the base's buffer, not a reinterpretation of it.
    if typeck.expr_ty(receiver) != input
        || initializer.span.from_expansion()
        || arguments[0].span.from_expansion()
        || local.pat.span.from_expansion()
        || !declaration::pointee_is_nameable(tcx, owner, *pointee)
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

fn derived_value(tcx: TyCtxt<'_>, subject: &Subject) -> Option<DerivedValue> {
    if subject.kind != SubjectKind::Local
        || subject.ty_span.is_some()
        || subject.decl_shape != DeclShape::RawPtr
        || subject.ptr_depth != 1
        || subject.null_init
        || subject.binding_span.from_expansion()
    {
        return None;
    }
    derived_view(tcx, subject.fn_did, subject.hir_id)
}

/// **The predicate ownership-fields' native source scan consumes (R440-3).**
///
/// `ownership_fields_source::resolve` refuses an owner whose root has a raw use
/// outside its `covered` set, and `covered` is filled only from root
/// occurrences that are ARGUMENTS of a call. `let f = root.offset(k)` puts the
/// root in RECEIVER position, so the owner is refused — and the refusal is what
/// keeps the Box candidate from being produced at all, which is what keeps this
/// lane from typing `f` (wave-5d2 report 019, measured both ways).
///
/// This answers, for one occurrence of one root: **is that occurrence the
/// receiver of the `.offset(k)` that initializes a local this lane types as a
/// suffix view of the root?** When it is, the occurrence is covered by this
/// lane's own emission — the local becomes `&mut root[(k) as usize..]` and the
/// raw read of the root disappears with it — so admitting it into `covered`
/// leaves no uncovered raw use behind.
///
/// It decides nothing on its own: a `true` here is a claim about THIS lane's
/// emission, and that emission additionally requires the base to deliver a
/// `Decision::Box` (`complete_derived`). If the base is not delivered, the
/// derived local is not typed either and both rows stay as they are.
pub(crate) fn admits_offset_receiver(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    root: HirId,
    occurrence: HirId,
) -> bool {
    // The occurrence must be the receiver of an `.offset(k)` call ...
    let Node::Expr(call) = tcx.parent_hir_node(occurrence) else {
        return false;
    };
    let ExprKind::MethodCall(_, receiver, _, _) = call.kind else {
        return false;
    };
    if receiver.hir_id != occurrence {
        return false;
    }
    // ... whose value initializes a local, through casts if the source wrote
    // any (`peel` accepts the same chain on the way down).
    let mut value = call.hir_id;
    let binding = loop {
        match tcx.parent_hir_node(value) {
            Node::Expr(outer)
                if matches!(outer.kind, ExprKind::Cast(..) | ExprKind::DropTemps(..)) =>
            {
                value = outer.hir_id;
            }
            Node::LetStmt(local) => match local.pat.kind {
                PatKind::Binding(_, hir, _, None) => break hir,
                _ => return false,
            },
            _ => return false,
        }
    };
    derived_view(tcx, owner, binding).is_some_and(|view| view.source == root)
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

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode, def::Res, intravisit};

    use super::*;

    /// Every occurrence of `root` in `function` that the exported predicate
    /// admits, rendered as the source text of the call it sits in. The list is
    /// the whole answer: what is NOT in it is refused.
    fn admitted(code: &str, function: &str, root: &str) -> Vec<String> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let mut owner = None;
            for maybe in tcx.hir_crate(()).owners.iter() {
                let Some(node) = maybe.as_owner() else { continue };
                let OwnerNode::Item(item) = node.node() else {
                    continue;
                };
                if matches!(item.kind, ItemKind::Fn { .. })
                    && tcx.item_name(item.owner_id.to_def_id()).as_str() == function
                {
                    owner = Some(item.owner_id.def_id);
                }
            }
            let owner = owner.expect("fixture function");
            let body = tcx.hir_body_owned_by(owner);

            struct Walk<'tcx> {
                bindings: Vec<(String, HirId)>,
                paths: Vec<&'tcx rustc_hir::Expr<'tcx>>,
            }
            impl<'tcx> intravisit::Visitor<'tcx> for Walk<'tcx> {
                fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
                    if let PatKind::Binding(_, hir_id, ident, _) = pat.kind {
                        self.bindings.push((ident.name.to_string(), hir_id));
                    }
                    intravisit::walk_pat(self, pat);
                }

                fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
                    if matches!(expr.kind, ExprKind::Path(_)) {
                        self.paths.push(expr);
                    }
                    intravisit::walk_expr(self, expr);
                }
            }
            let mut walk = Walk {
                bindings: Vec::new(),
                paths: Vec::new(),
            };
            intravisit::walk_body(&mut walk, body);

            let (_, root_binding) = walk
                .bindings
                .iter()
                .find(|(name, _)| name == root)
                .expect("fixture root binding");
            let typeck = tcx.typeck(owner);
            let source_map = tcx.sess.source_map();
            let mut admitted = Vec::new();
            for path in walk.paths {
                let ExprKind::Path(qpath) = &path.kind else {
                    continue;
                };
                if typeck.qpath_res(qpath, path.hir_id) != Res::Local(*root_binding) {
                    continue;
                }
                if admits_offset_receiver(tcx, owner, *root_binding, path.hir_id) {
                    let call = tcx.parent_hir_node(path.hir_id);
                    let rustc_hir::Node::Expr(call) = call else {
                        unreachable!("admitted occurrence has a call parent")
                    };
                    admitted.push(
                        source_map
                            .span_to_snippet(call.span)
                            .expect("snippet")
                            .replace(char::is_whitespace, ""),
                    );
                }
            }
            admitted
        })
        .expect("fixture compiles")
    }

    const DERIVED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
extern "C" {
    fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn transform_to_coordfield(width: i32, height: i32) {
    let size = width * height;
    let mut ff = calloc(size as usize, core::mem::size_of::<f32>()) as *mut f32;
    let mut x: i32 = 0;
    while x < width {
        let mut f = ff.offset((height * x) as isize);
        let mut y: i32 = 0;
        while y < height {
            *f.offset(y as isize) = y as f32;
            y += 1;
        }
        x += 1;
    }
    free(ff as *mut core::ffi::c_void);
}
"#;

    /// The one occurrence this lane covers, and only it: the `free` argument
    /// and the reads through the derived local are other occurrences of the
    /// same root and stay outside `covered`.
    #[test]
    fn the_initializing_offset_receiver_is_admitted() {
        assert_eq!(
            admitted(DERIVED, "transform_to_coordfield", "ff"),
            vec!["ff.offset((height*x)asisize)".to_owned()]
        );
    }

    /// The derived local's OWN uses are not the root's occurrences, so the
    /// predicate says nothing about them — asked directly, it refuses.
    #[test]
    fn a_use_of_the_derived_local_is_not_admitted() {
        assert!(admitted(DERIVED, "transform_to_coordfield", "f").is_empty());
    }

    /// An annotated local has a declared type of its own; this lane does not
    /// type it, so the occurrence stays uncovered and the owner stays held.
    #[test]
    fn an_annotated_derived_local_is_not_admitted() {
        const ANNOTATED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
extern "C" {
    fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn transform_to_coordfield(width: i32, height: i32) {
    let mut ff = calloc(width as usize, core::mem::size_of::<f32>()) as *mut f32;
    let f: *mut f32 = ff.offset(width as isize);
    *f = 1.0;
    free(ff as *mut core::ffi::c_void);
}
"#;
        assert!(admitted(ANNOTATED, "transform_to_coordfield", "ff").is_empty());
    }

    /// A different arithmetic method is a different form with a different
    /// emission; only `offset` is recognized.
    #[test]
    fn a_non_offset_receiver_is_not_admitted() {
        const ADD: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
extern "C" {
    fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn transform_to_coordfield(width: i32) {
    let mut ff = calloc(width as usize, core::mem::size_of::<f32>()) as *mut f32;
    let mut f = ff.add(width as usize);
    *f = 1.0;
    free(ff as *mut core::ffi::c_void);
}
"#;
        assert!(admitted(ADD, "transform_to_coordfield", "ff").is_empty());
    }

    /// A reinterpreting cast is not a suffix of the same buffer: the derived
    /// binding must carry the base's own pointer type.
    #[test]
    fn a_retyped_derived_local_is_not_admitted() {
        const RETYPED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
extern "C" {
    fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn transform_to_coordfield(width: i32) {
    let mut ff = calloc(width as usize, core::mem::size_of::<f32>()) as *mut f32;
    let mut f = ff.offset(width as isize) as *mut u8;
    *f = 1;
    free(ff as *mut core::ffi::c_void);
}
"#;
        assert!(admitted(RETYPED, "transform_to_coordfield", "ff").is_empty());
    }
}
