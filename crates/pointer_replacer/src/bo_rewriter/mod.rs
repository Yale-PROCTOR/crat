//! BO rewriter — GREENFIELD module (ruling 2026-07-27, Q2).
//!
//! This module consumes the borrow+ownership (BO) analysis results and emits
//! rewritten Rust. It is a clean-room implementation: the existing
//! [`crate::rewriter`] tree is a FROZEN production baseline and this module
//! **never imports from it**.
//!
//! Design of record:
//! - `docs/agents/plan/2026-07-27-bo-rewriter-scoping.md` (post-mortem + design)
//! - `docs/agents/plan/2026-07-28-m05-export-surface-spec.md` (E-R1..E-R4)
//! - `docs/agents/plan/2026-07-28-m05-decision-matrix.md` (kind mapping)
//!
//! # Isolation rule (Q2)
//!
//! A separate crate would have forced `mod analyses` public, so this is a
//! top-level module instead. That trades compile-time isolation for a
//! discipline that has to be enforced mechanically — see [`import_denylist`].
//!
//! | Target | Policy |
//! |---|---|
//! | `crate::rewriter::*` | **forbidden** — no import, path reference, or copied file |
//! | `crate::analyses::*` | allowed, read-only |
//! | `crate::utils::*`, `::utils::*` | allowed |
//!
//! # Phase separation (M1 architecture directive, binding from the first commit)
//!
//! The module is four phases with one-way data flow and no shared mutable
//! context (E1 state visibility):
//!
//! ```text
//!   analyses + BoExport ──▶ decision ──▶ plan ──▶ apply ──▶ verify
//!                           (reads)     (data)   (blind)   (gates)
//! ```
//!
//! Each phase hands the next a finished value. No phase holds a back-pointer to
//! another, and [`apply`] is *analysis-blind* by enforced rule, not convention —
//! see [`import_denylist`] for the per-phase checks.
//!
//! # Status
//!
//! M1/S0 lands the phase skeleton, the goldens as RED, and the per-phase
//! isolation checks. The decision table, edit plan and applier arrive in S1
//! (G01 walking skeleton) and S2–S3 (breadth).

#![allow(dead_code)]

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{mir::Local, ty::TyCtxt};

use crate::{
    analyses::borrow_ownership::{
        CrateCtxt, borrow_verify::verify_to_fixpoint, coherence::add_coherence,
        crate_slots::CrateSlots, emit_crate_ownership_constraints,
        export::with_bo_export, mutability_facts::MutFacts, origins::compute_origins,
        solver::KindSolver,
    },
    utils::rustc::RustProgram,
};

pub(crate) mod apply;
pub(crate) mod decision;
pub(crate) mod plan;
pub(crate) mod verify;

#[cfg(test)]
mod goldens;
#[cfg(test)]
mod import_denylist;

/// What one M1 rewrite attempt produced.
///
/// `Degraded` is a first-class outcome, not an error: §1.6 admits only
/// conflict-non-increasing re-routes, and **everything outside that envelope
/// degrades in the decision phase with a named reason**. Making that a variant
/// rather than a panic or a silent skip is what lets S2 count envelope
/// failures — the registered commitment that decides whether
/// emission-guided refinement is ever built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RewriteOutcome {
    /// The emitted crate source.
    Emitted(String),
    /// No emission, with the reason recorded.
    ///
    /// S0 ships a `&'static str` reason and no site. S2 replaces this with the
    /// typed envelope-demotion record (reason **and** site), which is what the
    /// counters aggregate.
    Degraded { reason: &'static str },
}

/// M1 entry point: source in, rewritten source out.
///
/// The four phases run in order, each handed the previous one's finished value:
/// `decision` (the only phase that reads analyses) → `plan` (edits as data) →
/// `apply` (analysis-blind splice) → `verify` (gates).
///
/// # Capture scope
///
/// The driver opens [`with_bo_export`] explicitly. The ambient `CRAT_BO_EXPORT`
/// flag is for corpus workers; the driver **is** the consumer, so it arms
/// unconditionally and pays the capture cost by design.
///
/// # S1 scope
///
/// Depth-0 pointer *parameters* decided `Ref`. Everything else degrades in the
/// decision phase with a named reason.
pub(crate) fn rewrite_m1(input: &str) -> RewriteOutcome {
    let owned = input.to_owned();
    let result = ::utils::compilation::run_compiler_on_str(input, move |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let mut_facts = MutFacts::from_program(&program);

        // Phase 1 input: the BO run, under an explicit capture scope.
        let (model, _export) = with_bo_export(|| {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let Ok((_stats, selectors)) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            ) else {
                return None;
            };
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            verify_to_fixpoint(&program, &slots, &solver, &selectors, &mut_facts)
        });
        let Some(model) = model else {
            return Err("BO declined — no accepted model");
        };

        let subjects = collect_subjects(tcx, &program, &mut_facts);
        let subject_count = subjects.len();
        let table = decision::decide(subjects, &model, &slots);

        // Structural gate: decision coverage.
        if !table.is_total_over(subject_count) {
            return Err("decision table is not total over its subjects");
        }

        let source_map = tcx.sess.source_map();
        let plan = plan::plan(&table, &owned, |span| {
            let lo = source_map.lookup_byte_offset(span.lo()).pos.0 as usize;
            let hi = source_map.lookup_byte_offset(span.hi()).pos.0 as usize;
            (lo <= hi && hi <= owned.len()).then_some((lo, hi))
        });

        let applied = apply::apply(&owned, &plan);
        // Structural gate: rollbacks must be zero.
        if !applied.rollbacks.is_empty() {
            return Err("apply rolled back at least one edit");
        }
        Ok(applied.source)
    });

    match result {
        Ok(Ok(emitted)) => {
            // Hard gate: the emitted crate type-checks.
            if verify::type_checks(&emitted) {
                RewriteOutcome::Emitted(emitted)
            } else {
                RewriteOutcome::Degraded {
                    reason: "emitted crate failed the type-check gate",
                }
            }
        }
        Ok(Err(reason)) => RewriteOutcome::Degraded { reason },
        Err(_) => RewriteOutcome::Degraded {
            reason: "input crate did not compile",
        },
    }
}

/// Every top-level fn/struct item, in HIR owner order (the `bo_c1` shape).
fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = Vec::new();
    let mut structs = Vec::new();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }
    RustProgram {
        tcx,
        functions,
        structs,
    }
}

/// S1 subjects: each pointer-typed parameter of each local function.
///
/// The MIR local of parameter `i` is `_{i+1}` — params occupy `_1 ..= arg_count`
/// — which is what lets a HIR-side span pair with a MIR-side slot lookup.
fn collect_subjects(
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    mut_facts: &MutFacts,
) -> Vec<decision::Subject> {
    let mut subjects = Vec::new();
    for &fn_did in &program.functions {
        let Some(decl) = tcx.hir_node_by_def_id(fn_did).fn_decl() else {
            continue;
        };
        for (index, input) in decl.inputs.iter().enumerate() {
            let rustc_hir::TyKind::Ptr(mut_ty) = input.kind else {
                continue;
            };
            let local = Local::from_usize(index + 1);
            subjects.push(decision::Subject {
                fn_did,
                local,
                ty_span: input.span,
                pointee_span: mut_ty.ty.span,
                // The declared `*mut`/`*const` is a ceiling, not the decision:
                // BO's mutability facts decide whether a `&mut` is warranted.
                mutable: mut_ty.mutbl.is_mut() && mut_facts.is_mutable(fn_did, local),
            });
        }
    }
    subjects
}
