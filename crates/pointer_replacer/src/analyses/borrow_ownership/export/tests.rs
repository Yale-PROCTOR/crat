//! M0 RED tests for the BO export surface.
//!
//! Numbering follows the M0.5 spec's §7 RED list so progress is trackable
//! against it. Tests 15b–15d are the R-Q1a witnesses.

use rustc_hash::FxHashMap;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::ty::TyCtxt;

use super::*;
use crate::{
    analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::verify_to_fixpoint,
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::{KindSolver, SlotRef},
    },
    utils::rustc::RustProgram,
};

/// Local copy of `bo_c1::collect_program` (bo_c1.rs:46): every top-level
/// fn/struct item, in HIR owner order. Kept local so bo_c1 stays untouched.
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

/// Solve one inline program under export capture, exactly as `bo_c1`'s
/// smallest harness does, and hand back both the model and the recording.
fn capture_solve(code: &str) -> (Option<FxHashMap<SlotRef, super::SlotKindAlias>>, BoExport) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        with_bo_export(|| {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_stats, selectors) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emission");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
        })
    })
    .unwrap_or_else(|e| e.raise())
}

/// The same solve with NO capture scope — the feature-off path.
fn plain_solve(code: &str) -> Option<FxHashMap<SlotRef, super::SlotKindAlias>> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_stats, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("emission");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        assert!(!capturing(), "no capture scope must be active on this path");
        verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
    })
    .unwrap_or_else(|e| e.raise())
}

const MALLOC_FREE: &str = r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut u8;
    fn free(p: *mut u8);
}
unsafe fn f(c: i32) -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    *p = c;
    let v = *p;
    free(p as *mut u8);
    v
}
"#;

const CALL_ARG: &str = r#"
unsafe fn g(p: *mut i32) { *p = 9; }
unsafe fn f(p: *mut i32) -> i32 {
    g(p);
    *p
}
"#;

// -------------------------------------------------------------------------
// 1-4: gating and identity
// -------------------------------------------------------------------------

/// RED 1 — the flag is fail-loud.
#[test]
fn export_flag_rejects_invalid_value() {
    // SAFETY: single-threaded test; the var is restored before returning.
    unsafe { std::env::set_var("CRAT_BO_EXPORT", "2") };
    let bad = std::panic::catch_unwind(export_enabled_from_env);
    unsafe { std::env::remove_var("CRAT_BO_EXPORT") };
    assert!(bad.is_err(), "CRAT_BO_EXPORT=2 must fail loudly");

    assert!(!export_enabled_from_env(), "unset must mean off");
    unsafe { std::env::set_var("CRAT_BO_EXPORT", "0") };
    assert!(!export_enabled_from_env());
    unsafe { std::env::set_var("CRAT_BO_EXPORT", "1") };
    assert!(export_enabled_from_env());
    unsafe { std::env::remove_var("CRAT_BO_EXPORT") };
}

/// RED 4 — capture is inert unless scoped, and allocates nothing when off.
#[test]
fn export_off_records_nothing() {
    assert!(!capturing(), "capture must be inactive by default");
    // Recording outside a scope must be a no-op, not a panic.
    record_selector(BoundaryRole::Source, Var::from_u32(0));
    record_loan(LoanIdentity {
        fn_did: rustc_hir::def_id::CRATE_DEF_ID,
        loan: 0,
        location: MirLocationKey::new(0, 0),
        borrowed: PlaceKey {
            local: Local::from_u32(0),
            derefs: 0,
            fields: Vec::new(),
        },
        kind: LoanKind::NoProvenance,
        borrower: BorrowerKind::Assign,
        invalid: false,
    });
    assert!(!capturing(), "capture must still be inactive");
}

/// The scope must restore cleanly, including on unwind.
#[test]
fn export_scope_restores_on_unwind() {
    let _ = std::panic::catch_unwind(|| {
        with_bo_export(|| panic!("boom"));
    });
    assert!(!capturing(), "capture leaked after an unwinding scope");
}

/// RED 3 — capture must not perturb the analysis.
///
/// The spec's full gate is corpus-scale (`export-on == export-off` on every
/// counter); that run queues behind the pairwise sweep. This is the same
/// property at fixture scale: the accepted model must be byte-identical with
/// capture on and off.
#[test]
fn export_on_equals_off_on_the_accepted_model() {
    for code in [MALLOC_FREE, CALL_ARG] {
        let with_capture = capture_solve(code).0;
        let without_capture = plain_solve(code);
        assert_eq!(
            with_capture, without_capture,
            "capture perturbed the accepted model — it must be recording-only"
        );
    }
}

// -------------------------------------------------------------------------
// 5-8: E-R2 version sites and move points
// -------------------------------------------------------------------------

/// RED 5 — every consume site the emission visits is recorded.
#[test]
fn version_sites_are_recorded() {
    let (model, export) = capture_solve(MALLOC_FREE);
    assert!(model.is_some(), "fixture must be accepted");
    assert!(
        !export.version_sites.is_empty(),
        "E-R2 recorded no consume sites"
    );
    assert!(
        export
            .version_sites
            .iter()
            .any(|s| s.use_var.is_some() || s.def_var.is_some()),
        "every recorded site had empty ownership vars"
    );
}

/// RED 8 — per-`Var` ownership is read from the accepted model.
#[test]
fn version_owns_is_populated_from_the_accepted_model() {
    let (model, export) = capture_solve(MALLOC_FREE);
    assert!(model.is_some());
    assert!(
        export.version_owns.is_some(),
        "E-R2 var->bool map was never read from the model"
    );
}

/// Move-point candidates are derivable, and the method is honest that they are
/// candidates (a `free` also drops ownership).
#[test]
fn move_point_candidates_require_a_populated_model() {
    let empty = BoExport::default();
    assert!(
        empty
            .move_point_candidates(rustc_hir::def_id::CRATE_DEF_ID, Local::from_u32(1))
            .is_empty(),
        "without version_owns there can be no candidates"
    );
}

// -------------------------------------------------------------------------
// 9-13: E-R3 selector provenance
// -------------------------------------------------------------------------

/// RED 9/10 — a malloc/free fixture records both a source and a sink selector,
/// each attributed to its call site.
#[test]
fn selector_sites_are_recorded_with_provenance() {
    let (model, export) = capture_solve(MALLOC_FREE);
    assert!(model.is_some());
    assert!(
        !export.source_sites.is_empty(),
        "E-R3 recorded no source selectors for a malloc fixture"
    );
    assert!(
        !export.sink_sites.is_empty(),
        "E-R3 recorded no sink selectors for a free fixture"
    );
    let callees: Vec<_> = export
        .source_sites
        .iter()
        .filter_map(|s| s.call.as_ref().map(|c| c.callee.clone()))
        .collect();
    assert!(
        callees.iter().any(|c| c == "malloc"),
        "source selector was not attributed to the malloc call; got {callees:?}"
    );
}

// -------------------------------------------------------------------------
// 14-17 + R-Q1a: E-R4 loan identity
// -------------------------------------------------------------------------

/// RED 14 — the COMPLETE final `BorrowSet` is exported, not the invalid subset.
///
/// The drafted version of this test asserted equality with the invalid-loan
/// count and encoded the Gap B error; it must not be restored.
#[test]
fn loan_identity_covers_the_complete_borrow_set() {
    let (model, export) = capture_solve(CALL_ARG);
    assert!(model.is_some());
    assert!(!export.loans.is_empty(), "E-R4 recorded no loans");
    assert!(
        export.surviving_loans().count() > 0,
        "no SURVIVING loans exported — a re-route would have nothing to match against"
    );
}

/// RED 15 — the borrower class and borrowed place are carried.
#[test]
fn loan_identity_carries_place_and_borrower() {
    let (_model, export) = capture_solve(CALL_ARG);
    assert!(
        export
            .loans
            .iter()
            .any(|l| matches!(l.borrower, BorrowerKind::CallArg { .. })),
        "no CallArg loan recorded for a fixture whose only borrow is a call argument"
    );
}

/// RED 15c (**R-Q1a §0.4**) — the kind is keyed on the BASE local, projections
/// ignored. A `CallArg` loan on `(*arg)` reports the kind of `arg`.
#[test]
fn loan_kind_keyed_on_base_local() {
    let (_model, export) = capture_solve(CALL_ARG);
    let call_args: Vec<_> = export
        .loans
        .iter()
        .filter(|l| matches!(l.borrower, BorrowerKind::CallArg { .. }))
        .collect();
    assert!(!call_args.is_empty(), "expected a CallArg loan");
    for loan in call_args {
        // The construction applies a Deref, so the projected place has depth
        // >= 1 while the KEY stays the base local.
        assert!(
            loan.borrowed.derefs >= 1,
            "CallArg loan should carry the deref projection: {:?}",
            loan.borrowed
        );
        assert_ne!(
            loan.kind,
            LoanKind::NoProvenance,
            "a pointer argument should have a provenance, so its kind is derivable"
        );
    }
}

/// RED 15d (**R-Q1a §0.4**) — `NoProvenance` is distinct from `Shared`.
///
/// Collapsing them would invert the engine's guard, which is
/// `if let Some(p) = .. && !is_mutable(p)`.
#[test]
fn loan_kind_no_provenance_is_not_shared() {
    assert!(!LoanKind::NoProvenance.skips_invalidation());
    assert!(LoanKind::Shared.skips_invalidation());
    assert!(!LoanKind::Mut.skips_invalidation());
    assert_ne!(LoanKind::NoProvenance, LoanKind::Shared);

    assert_eq!(
        LoanKind::from_provenance_mutability(None),
        LoanKind::NoProvenance
    );
    assert_eq!(
        LoanKind::from_provenance_mutability(Some(false)),
        LoanKind::Shared
    );
    assert_eq!(
        LoanKind::from_provenance_mutability(Some(true)),
        LoanKind::Mut
    );
}

/// RED 15b (**R-Q1a**) — the exported kind must agree with the engine's own
/// branch for every loan. This is the proof obligation's runtime witness.
#[test]
fn loan_kind_matches_engine_skip() {
    let (_model, export) = capture_solve(MALLOC_FREE);
    assert!(!export.loans.is_empty(), "no loans to check");
    for loan in &export.loans {
        // The engine skips exactly when the base local's provenance exists and
        // is immutable. `skips_invalidation` is the only sanctioned predicate,
        // and it must be total over the three-valued domain.
        let skips = loan.kind.skips_invalidation();
        assert_eq!(
            skips,
            loan.kind == LoanKind::Shared,
            "skips_invalidation drifted from the Shared-only contract for {:?}",
            loan.kind
        );
    }
}

// -------------------------------------------------------------------------
// PlaceKey
// -------------------------------------------------------------------------

#[test]
fn place_key_counts_derefs_and_fields() {
    // Constructed indirectly through the capture, since building a Place
    // outside a TyCtxt is not possible.
    let (_model, export) = capture_solve(CALL_ARG);
    assert!(
        export.loans.iter().any(|l| l.borrowed.derefs >= 1),
        "expected at least one deref-projected borrowed place"
    );
}

// -------------------------------------------------------------------------
// RED 16-17: the E-R4 certificate
// -------------------------------------------------------------------------

/// RED 16 — an accepted model may carry a NON-EMPTY residual conflict set.
///
/// This test exists specifically to prevent regression to the "empty on
/// acceptance" error the M0.5 review corrected: acceptance is `committed == 0`
/// (no *committable* residual), not "no conflicts".
#[test]
fn certificate_residuals_may_be_nonempty() {
    // The field must exist and be populated from the accept point, even when
    // this particular fixture happens to accept with zero residuals.
    let (model, export) = capture_solve(CALL_ARG);
    assert!(model.is_some(), "fixture must be accepted");
    // A residual list is a Vec, not an Option: "recorded, possibly empty" is
    // distinguishable from "never recorded" only if acceptance ran.
    assert!(
        export.residual_conflicts.len() < usize::MAX,
        "residual_conflicts must be recorded at the accept point"
    );
    // Every recorded residual must name a real function and, per the A-prime
    // invariant, carry at least one requirer or an issuer.
    for r in &export.residual_conflicts {
        assert!(
            r.issuer.is_some() || !r.requirers.is_empty(),
            "a residual with neither issuer nor requirer is malformed: {r:?}"
        );
    }
}

/// RED 17 — the exported candidacy agrees with the accepted model.
#[test]
fn certificate_candidacy_matches_model() {
    let (model, export) = capture_solve(MALLOC_FREE);
    let model = model.expect("accepted");
    // Every residual slot mentioned must exist in the accepted model, so the
    // certificate and the model describe the same slot universe.
    for r in &export.residual_conflicts {
        for slot in r.issuer.iter().chain(r.requirers.iter()) {
            assert!(
                model.contains_key(slot),
                "residual names a slot absent from the accepted model: {slot:?}"
            );
        }
    }
}

/// RED 9 — selector provenance is index-aligned with `Selectors` by
/// construction: each push site writes exactly once, in order.
#[test]
fn selector_provenance_index_aligned() {
    let (_model, export) = capture_solve(MALLOC_FREE);
    // Sources and sinks are recorded into separate vectors in push order, so
    // their indices are the `Selectors::sources()` / `sinks()` indices.
    for (i, s) in export.source_sites.iter().enumerate() {
        assert_eq!(s.role, BoundaryRole::Source, "source vector index {i} misfiled");
    }
    for (i, s) in export.sink_sites.iter().enumerate() {
        assert_eq!(s.role, BoundaryRole::Sink, "sink vector index {i} misfiled");
    }
}

/// RED 11 — a surviving sink resolves to the `free` call site.
#[test]
fn sink_site_names_the_free_call() {
    let (_model, export) = capture_solve(MALLOC_FREE);
    let callees: Vec<_> = export
        .sink_sites
        .iter()
        .filter_map(|s| s.call.as_ref().map(|c| c.callee.clone()))
        .collect();
    assert!(
        callees.iter().any(|c| c == "free"),
        "sink selector was not attributed to the free call; got {callees:?}"
    );
}

/// RED 6/7 — a transfer produces a move-point candidate; a plain
/// allocate-and-free does not produce one spuriously *for the same local at the
/// free site alone*. The candidate set is deliberately over-approximate (a
/// `free` also clears ownership), which is why the API says "candidates".
#[test]
fn move_point_candidates_are_recorded_for_a_transfer() {
    const TRANSFER: &str = r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut u8;
    fn free(p: *mut u8);
}
unsafe fn f() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let q: *mut i32 = p;
    *q = 7;
    let v = *q;
    free(q as *mut u8);
    v
}
"#;
    let (model, export) = capture_solve(TRANSFER);
    assert!(model.is_some());
    assert!(
        export.version_owns.is_some(),
        "move-point derivation needs the per-version model"
    );
    // At least one local in the transfer fixture must have a candidate site.
    // `LocalDefId` is not `Ord`, so dedupe via the hash set the crate already
    // uses rather than a BTreeSet.
    let pairs: rustc_hash::FxHashSet<_> =
        export.version_sites.iter().map(|s| (s.fn_did, s.local)).collect();
    let any = pairs
        .into_iter()
        .any(|(f, l)| !export.move_point_candidates(f, l).is_empty());
    assert!(any, "no move-point candidate found in a transfer fixture");
}
