//! **wave-6a rule W6A-B1 — an unannotated slice local is typed by its sealed
//! constructor.** (seat addendum 400, R400-3; charter §1(b))
//!
//! `let mut f = ff.offset(e);` has no declared type, so the dissolution's veto
//! in `decide_one` degrades its `Slice` decision to `copy-source-coupled`
//! (`slice-local-construction` before the family stage): nothing can splice
//! `: &mut [f32]` in. But the slice-construction family already rewrites the
//! initializer itself into `core::slice::from_raw_parts_mut(ff.offset(e), n)`
//! — an expression whose type is complete — so the binding needs **no**
//! declaration splice at all. This is exactly the shape Box wave 1 admits
//! through `BoxPlan::inferred_binding`: the initializer carries the type, the
//! planner places value edits and no declaration edit.
//!
//! The rule adds no form, no reason and no variant. It names the population on
//! which the veto's premise ("no splice target ⇒ cannot emit") does not hold.

use rustc_hash::FxHashMap;
use rustc_hir::{Expr, ExprKind, HirId, QPath, UnOp, def::Res, def_id::LocalDefId};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    Ctx, Decision, DecisionTable, Subject, SubjectKind,
    construction::{ConstructionFacts, slice_constructor_available},
    declaration::pointee_source,
    seam::{ExplicitDeclarationSite, Form},
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::{
        additive::{FamilyPolicy, FamilyStage},
        bridge_receipt::SignatureClassId,
    },
};

/// The decision that the sealed constructor can type from the initializer:
/// a borrowed slice, or its nullable twin (rendered as
/// `ptr.as_mut().map(|p| from_raw_parts_mut(p, n))`, also complete).
fn constructor_typed(decision: &Decision) -> bool {
    match decision {
        Decision::Slice { .. } | Decision::Opt { slice: true, .. } => true,
        Decision::Opt { slice: false, .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. }
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => false,
    }
}

/// The local binding whose MEMORY an initializer's slice would cover, through
/// casts, pointer arithmetic, address-of / dereference pairs, array decays
/// and non-pointer field places: `ff.offset(e)` → `ff`, `&*q.offset(i) as
/// *const T` → `q`, a bare copy `q` → `q`, `(*s).arr.as_mut_ptr()` → `s`
/// (the slice covers `s`'s own array field). `None` where the walk reaches a
/// raw pointer VALUE loaded from a field (`(*s).buf`: the slice covers that
/// pointer's pointee, not `s`), an allocator or other call result, a
/// literal, or any shape not listed — those carry no binding to be widened
/// or doubly viewed.
fn initializer_root(tcx: TyCtxt<'_>, owner: LocalDefId, init_hir: HirId) -> Option<HirId> {
    let typeck = tcx.typeck(owner);
    let mut expression: &Expr<'_> = tcx.hir_node(init_hir).expect_expr();
    loop {
        expression = match expression.kind {
            ExprKind::Cast(inner, _)
            | ExprKind::AddrOf(_, _, inner)
            | ExprKind::Unary(UnOp::Deref, inner) => inner,
            ExprKind::Field(inner, _) => {
                if typeck.expr_ty(expression).is_raw_ptr() {
                    return None;
                }
                inner
            }
            ExprKind::MethodCall(segment, receiver, _, _)
                if matches!(
                    segment.ident.name.as_str(),
                    "offset"
                        | "add"
                        | "sub"
                        | "wrapping_add"
                        | "wrapping_sub"
                        | "cast"
                        | "as_ptr"
                        | "as_mut_ptr"
                ) =>
            {
                receiver
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                return match path.res {
                    Res::Local(hir) => Some(hir),
                    _ => None,
                };
            }
            _ => return None,
        };
    }
}

/// **The soundness line of the rule.** A slice constructed OVER the memory of
/// a binding that itself becomes a safe reference is either a widening or a
/// second live safe view: `let p = a;` with `a: &T` delivered thin would
/// become `from_raw_parts(a, n)` — a buffer claimed from a one-element
/// reference, exactly the widening R395-2 forbids (fix-2); and
/// `from_raw_parts_mut((*s).arr.as_mut_ptr(), 704)` beside a live `s: &mut S`
/// is a `&mut [T]` aliasing `s`'s own field with no borrow relation the
/// compiler can check (R395-2: no two live aliasing safe views — the sound
/// form is the reborrow `&mut s.arr[..]`, a computed view over a delivered
/// reference, unbuilt for locals). A root the model calls `Ref` is therefore
/// never a construction source under this rule, whatever its fatness. `Raw`
/// and `Owning` roots stay raw at the initializer (an Owning root delivered
/// as a Box would fail the constructor's type check and be measured by the
/// verify loop, never silently widened); raw pointer values loaded from
/// fields, statics and allocator results carry no binding to widen.
fn root_is_a_reference_candidate(
    tcx: TyCtxt<'_>,
    model: &FxHashMap<SlotRef, SlotKind>,
    slots: &CrateSlots,
    subjects: &[Subject],
    constructions: &ConstructionFacts,
    subject: &Subject,
) -> bool {
    let Some(&init_hir) = constructions
        .init_hirs
        .get(&(subject.fn_did, subject.hir_id))
    else {
        return false;
    };
    let Some(root) = initializer_root(tcx, subject.fn_did, init_hir) else {
        return false;
    };
    let Some(source) = subjects
        .iter()
        .find(|candidate| candidate.fn_did == subject.fn_did && candidate.hir_id == root)
    else {
        return false;
    };
    let Some(universe) = slots.fn_local_slots.get(&source.fn_did) else {
        return false;
    };
    let Some(slot) = universe.slot_for_local_depth(source.local, 0) else {
        return false;
    };
    match model.get(&SlotRef::Local(source.fn_did, slot)) {
        Some(SlotKind::Ref) => true,
        Some(SlotKind::Raw | SlotKind::Owning) | None => false,
    }
}

/// The predicate shared by the decision veto and the planner.
fn inferred(
    family_policy: &FamilyPolicy,
    constructions: &ConstructionFacts,
    subject: &Subject,
    decision: &Decision,
) -> bool {
    matches!(subject.kind, SubjectKind::Local)
        && subject.ty_span.is_none()
        && constructor_typed(decision)
        && family_policy.enabled(subject.fn_did, FamilyStage::SliceConstruction)
        && slice_constructor_available(constructions, (subject.fn_did, subject.hir_id))
}

/// Decision-phase hook: the veto in `decide_one` keeps this decision.
pub(crate) fn inferred_binding(ctx: &Ctx<'_, '_>, subject: &Subject, decision: &Decision) -> bool {
    inferred(ctx.family_policy, ctx.constructions, subject, decision)
        && !root_is_a_reference_candidate(
            ctx.tcx,
            ctx.model,
            ctx.slots,
            ctx.subjects,
            ctx.constructions,
            subject,
        )
}

/// **The declaration carries its type anyway.** The delivery-custody
/// instrument (main 033, R219) reads the emitted tree and refuses a delivered
/// declaration whose type is inferred, so every binding this rule admits
/// receives an explicit `: &mut [T]` / `: &[T]` / `: Option<&mut [T]>`
/// through the existing explicit-local-declaration channel (the same one the
/// return receivers use). The planner still places no type SPLICE of its own
/// — there is no type span — the AST layer sets the local's type from this
/// site. The element type is the binding's own raw pointee, rendered as the
/// declaration family renders it.
pub(crate) fn append_explicit_declarations(tcx: TyCtxt<'_>, table: &mut DecisionTable) {
    let mut sites = Vec::new();
    for (subject, decision) in &table.entries {
        if !planner_inferred(table, subject, decision) {
            continue;
        }
        let Some(name) = subject.param_name.as_deref() else { continue };
        let node = (subject.fn_did, subject.hir_id);
        if table
            .seams
            .explicit_declarations
            .iter()
            .any(|site| site.category == "local" && site.node == Some(node))
        {
            continue;
        }
        let binding_type = tcx.typeck(subject.fn_did).node_type(subject.hir_id);
        let TyKind::RawPtr(pointee, _) = binding_type.kind() else { continue };
        let element = pointee_source(tcx, *pointee);
        let emitted_type = match decision {
            Decision::Slice { mutable, .. } => {
                format!("&{}[{element}]", if *mutable { "mut " } else { "" })
            }
            Decision::Opt {
                mutable,
                slice: true,
                ..
            } => format!("Option<&{}[{element}]>", if *mutable { "mut " } else { "" }),
            Decision::Opt { slice: false, .. }
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => continue,
        };
        sites.push(ExplicitDeclarationSite {
            owner_class: SignatureClassId::of(subject.fn_did),
            caller: subject.fn_did,
            node: Some(node),
            span: Some(subject.binding_span),
            category: "local",
            replacement: Some(format!(
                "{}{name}: {emitted_type}",
                if subject.mut_binding { "mut " } else { "" }
            )),
            emitted_type,
            arm: "surface",
        });
    }
    table.seams.explicit_declarations.extend(sites);
}

/// Plan-phase hook: the subject takes the no-declaration-splice branch when
/// a sealed construction plan carries its typed initializer.
pub(crate) fn planner_inferred(
    table: &DecisionTable,
    subject: &Subject,
    decision: &Decision,
) -> bool {
    let node: (LocalDefId, HirId) = (subject.fn_did, subject.hir_id);
    matches!(subject.kind, SubjectKind::Local)
        && subject.ty_span.is_none()
        && constructor_typed(decision)
        && table
            .slice_constructions
            .iter()
            .any(|plan| plan.node == node && plan.replacement.is_some())
}

/// A MUTABLE borrowed slice handed to a settled SHARED slice parameter is
/// Rust's own `&mut [T] → &[T]` coercion: no bridge text exists for the seam
/// to carry, so the slice-use receipt takes the parameter's form directly.
///
/// Deliberately the one pair wave-5c's equal-form carrier rule
/// (`slice_carrier.rs`, `owned-existing-c-same-slice`) does not cover: equal
/// forms complete there, over the seam's input twin. An `Option<&mut [T]>`
/// passed by value MOVES the binding and never coerces to `Option<&[T]>`, so
/// the nullable twins stay with the carrier rules.
pub(crate) fn zero_syntax_slice_pass(found: Form, expected: Form) -> Option<Form> {
    match (found, expected) {
        (Form::Slice { mutable: true }, Form::Slice { mutable: false }) => Some(expected),
        (Form::Slice { .. }, _) | (Form::Opt { .. }, _) => None,
        (Form::Raw | Form::Ref { .. } | Form::NestedSlice { .. } | Form::Cursor { .. }, _) => None,
    }
}
