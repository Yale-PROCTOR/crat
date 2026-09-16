//! The reborrow of a raw-valued initializer at a thin `Ref` local (relay
//! wave-5d/026 §2, wave-6s 012 §2).
//!
//! A local decided `Ref` is declared `&T` / `&mut T`; when its initializer is
//! an expression whose VALUE stays a raw pointer after the rewrite — the
//! element of a delivered outer slice (`inputs[k]` on `&[*const f64]`), the
//! deref of a reference-to-raw (`*p` on `&*const f64`), raw arithmetic on a
//! parameter that stays raw (`p.offset(k)`) — the declaration read
//! `let input: &f64 = inputs[(k) as usize];` and failed E0308 at verify. Wave
//! 2's body adapters (`emitability::BodyAdapterSite`) cover eight pinned
//! functions and refuse a `RawExpr` initializer as `body-unnameable-rhs`;
//! `construction_values` covers the unannotated copy of a parameter; nothing
//! covered this shape, so it was neither bridged nor held.
//!
//! The bridge is the `c` arm's own [`seam::GlueCore::Reborrow`] at the
//! declaration: `&*(<initializer>)` / `&mut *(<initializer>)`, the operand
//! parenthesised because it is an arbitrary expression. Nothing here decides a
//! form: the local's `Ref` is the ladder's verdict, and the reborrow is the
//! mechanical bridge from the raw value the input program dereferenced to the
//! reference the local was decided to be (soundness conditional on the UB-free
//! input, as at every `c` site). A call into a LOCAL function is left alone:
//! its return may be delivered in a safe form by the return family, and the
//! declaration then needs no reborrow. One owner per initializer span: a body
//! site another producer already placed or refused is not touched.

use rustc_hir::{ExprKind, Node, PatKind};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{Decision, DecisionTable, SubjectKind, emitability, seam};
use crate::bo_rewriter::bridge_receipt::{BridgeSitePlan, SignatureClassId};

pub(crate) const BRIDGE_KIND: &str = "raw-initializer-reborrow";

/// A top-level call whose callee is a function of this crate.
fn calls_local_function(tcx: TyCtxt<'_>, expression: &rustc_hir::Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = expression.kind else {
        return false;
    };
    matches!(
        tcx.typeck(expression.hir_id.owner.def_id).expr_ty(callee).kind(),
        TyKind::FnDef(definition, _) if definition.is_local()
    )
}

pub(crate) fn complete(tcx: TyCtxt<'_>, table: &DecisionTable, plan: &mut seam::SeamPlan) {
    let sm = tcx.sess.source_map();
    for (subject, decision) in &table.entries {
        // EXHAUSTIVE: a new disposition must be a compile error here, not a
        // silently skipped subject (the import denylist's rule).
        let mutable = match decision {
            Decision::Ref { mutable } => *mutable,
            Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. }
            | Decision::NestedSlice { .. }
            | Decision::Degraded(_) => continue,
        };
        if subject.kind != SubjectKind::Local || subject.ptr_depth != 1 || subject.null_init {
            continue;
        }
        let Node::LetStmt(local) = tcx.parent_hir_node(subject.hir_id) else { continue };
        if !matches!(local.pat.kind, PatKind::Binding(_, hir, _, None) if hir == subject.hir_id) {
            continue;
        }
        let Some(initializer) = local.init else { continue };
        if initializer.span.from_expansion() || calls_local_function(tcx, initializer) {
            continue;
        }
        let shape = emitability::classify_arg(tcx, initializer);
        if !matches!(shape, emitability::ArgShape::RawExpr { .. }) {
            continue;
        }
        // **The bridge exists because the initializer's VALUE stays raw after
        // the rewrite, and that is a fact about the DECISIONS, not about the
        // input's types** (which are raw either way). Proven from the place
        // the initializer reads through:
        //
        // * the root delivers no safe form (degraded / raw) — the expression
        //   is emitted unchanged, so its value is raw;
        // * the root delivers a safe form at pointer depth >= 2 — the family
        //   rewrites the expression (`*inputs.offset(k)` -> `inputs[k]`,
        //   `*p` -> `*p`) but the ELEMENT it yields is itself a raw pointer.
        //
        // Anything else is refused, and the refusal is what keeps this bridge
        // from doubling another family's: at depth 1 the slice/reference
        // family already emits a REFERENCE there (g18's rebind arm renders
        // `&(p)[1]`, wave-6f's array of references renders
        // `points[i].unwrap()`), and `&*` over it would be a second bridge on
        // a value that no longer needs one. A root that is not a subject of
        // this table (an array local, a static) carries no such proof either,
        // so it is refused too.
        let Some(root) = shape.place_root() else { continue };
        let Some((root_subject, root_decision)) = table
            .entries
            .iter()
            .find(|(candidate, _)| candidate.fn_did == subject.fn_did && candidate.hir_id == root)
        else {
            continue;
        };
        let root_yields_raw = match root_decision {
            Decision::Degraded(_) => true,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. }
            | Decision::NestedSlice { .. } => root_subject.ptr_depth >= 2,
        };
        if !root_yields_raw {
            continue;
        }
        let typeck = tcx.typeck(subject.fn_did);
        let (TyKind::RawPtr(source, _), TyKind::RawPtr(target, _)) = (
            typeck.expr_ty(initializer).kind(),
            typeck.node_type(subject.hir_id).kind(),
        ) else {
            continue;
        };
        if source != target {
            continue;
        }
        if plan
            .body_edits
            .iter()
            .any(|edit| edit.span == initializer.span)
            || plan
                .body_blocked
                .iter()
                .any(|blocked| blocked.span == initializer.span)
        {
            continue;
        }
        let Ok(text) = sm.span_to_snippet(initializer.span) else { continue };
        let spec = seam::GlueSpec::core(seam::GlueCore::Reborrow, mutable);
        let unsafe_fn = tcx
            .fn_sig(subject.fn_did.to_def_id())
            .skip_binder()
            .skip_binder()
            .safety
            .is_unsafe();
        let Some(replacement) = spec.render_in_context(&format!("({text})"), unsafe_fn) else {
            continue;
        };
        let expected = seam::Form::Ref { mutable };
        let found = seam::Form::Raw;
        let mut bridge = BridgeSitePlan::local(
            subject.fn_did,
            subject.fn_did,
            "glue",
            "body:local-initializer",
            BRIDGE_KIND,
        );
        bridge.expected_form = expected.key().to_owned();
        bridge.found_form = found.key().to_owned();
        bridge.argument_kind = shape.key().to_owned();
        bridge.unsafe_context = seam::unsafe_context_for(tcx, subject.fn_did, &spec);
        plan.body_edits.push(seam::BodyEdit {
            span: initializer.span,
            replacement,
            owner_class: SignatureClassId::of(subject.fn_did),
            bridge,
            owner_fn: tcx.def_path_str(subject.fn_did.to_def_id()),
            destination: subject.label.clone(),
            context: emitability::BodyAdapterContext::LocalInitializer,
            source_shape: shape.key(),
            family: seam::SeamFamily::Reborrow,
            spec,
            arg_span: initializer.span,
            expected,
            found,
            root_identity: "-".to_owned(),
            blind: true,
        });
    }
}
