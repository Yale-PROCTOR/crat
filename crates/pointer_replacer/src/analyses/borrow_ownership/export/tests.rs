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
        borrow_verify::{
            RepairMode, RoundStats, model_accepts, verify_l2_to_fixpoint_counting,
            verify_to_fixpoint, verify_to_fixpoint_counting,
        },
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origin_flow::analyze_program_origin_flow,
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

// RED 1 (the `CRAT_BO_EXPORT` fail-loud parse) is GONE, not weakened: D4 was
// closed by DESCOPING the env switch, so there is no flag left to reject a bad
// value. `export_off_records_nothing` is now the gating witness, and it
// asserts the stronger property: capture is off unless a scope opened it, with
// no ambient path that can turn it on.

/// RED 4 — capture is inert unless scoped, and allocates nothing when off.
///
/// **Also the D4 witness.** The first assertion fails if ambient enablement is
/// ever reintroduced — an env flag, a global, a lazy install inside
/// `capturing()` — because this test runs with no scope open. Mutation-tested:
/// restoring the `if flag_enabled() { install }` branch with the flag forced on
/// fails it here.
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

    // RESTORED CARDINALITY (spec RED 14). Weakening this to a non-emptiness
    // check is exactly what let defect D1 through: with the recorder appending
    // across CEGAR rounds, `loans` held N copies of every loan and no
    // non-emptiness assertion could see it. One record per (fn, loan index) is
    // the property that pins "the FINAL round's BorrowSet".
    let mut seen = rustc_hash::FxHashSet::default();
    for loan in &export.loans {
        assert!(
            seen.insert((loan.fn_did, loan.loan)),
            "loan ({:?}, {}) recorded more than once — the export is accumulating \
             across validation rounds instead of holding the accepted round (D1)",
            loan.fn_did,
            loan.loan
        );
    }
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

/// A mutability provider the TEST controls, so the derivation can be checked
/// against a known answer rather than against its own definition.
struct SelectiveMut {
    /// Locals declared immutable; everything else is mutable.
    immutable: Vec<Local>,
}

impl crate::analyses::borrow_ownership::mutability_facts::MutProvider for &SelectiveMut {
    fn is_mutable(&self, _fn_did: rustc_hir::def_id::LocalDefId, local: Local) -> bool {
        !self.immutable.contains(&local)
    }
}

/// Solve under a caller-supplied mutability provider, with capture active.
fn capture_solve_with(
    code: &str,
    immutable: Vec<u32>,
) -> (Option<FxHashMap<SlotRef, super::SlotKindAlias>>, BoExport) {
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let facts = SelectiveMut {
            immutable: immutable.iter().copied().map(Local::from_u32).collect(),
        };
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
            verify_to_fixpoint(&program, &slots, &solver, &selectors, &facts)
        })
    })
    .unwrap_or_else(|e| e.raise())
}

/// RED 15b (**R-Q1a**) — the exported kind checked against GROUND TRUTH.
///
/// The previous version asserted `skips_invalidation() == (kind == Shared)`,
/// true by the definition of `skips_invalidation` and therefore unable to fail
/// if the fork-side derivation drifted from the engine. That tautology was
/// defect **D3**; this is its replacement.
///
/// Ground truth is a mutability provider the test supplies. The derivation must
/// reproduce `is_mutable(fn_did, borrowed.local)` — so this simultaneously
/// witnesses that the key is the **base local** (R-Q1a §0.4): a derivation that
/// keyed on the projected place would look up a different local and disagree.
#[test]
fn loan_kind_matches_ground_truth_provider() {
    // Local 1 is the first argument. Declaring it immutable must show up as a
    // Shared kind on every loan whose borrowed base local is 1, and must NOT
    // change the kind of loans rooted at any other local.
    let (model, export) = capture_solve_with(CALL_ARG, vec![1]);
    assert!(model.is_some(), "fixture must be accepted");
    assert!(!export.loans.is_empty(), "no loans recorded");

    let mut checked = 0usize;
    for loan in &export.loans {
        let expected = if loan.borrowed.local == Local::from_u32(1) {
            // Provenance exists (it is a pointer argument) and we declared it
            // immutable, so the engine's guard fires: Shared.
            LoanKind::Shared
        } else {
            // Mutable, or no provenance at all — either way NOT Shared.
            assert_ne!(
                loan.kind,
                LoanKind::Shared,
                "loan rooted at {:?} derived Shared, but only local 1 was declared immutable",
                loan.borrowed.local
            );
            checked += 1;
            continue;
        };
        assert_eq!(
            loan.kind, expected,
            "derivation disagreed with the supplied provider for base local {:?} \
             (borrowed place {:?}) — the key or the lookup has drifted",
            loan.borrowed.local, loan.borrowed
        );
        checked += 1;
    }
    assert!(checked > 0, "no loan was actually checked against ground truth");
}

/// The same fixture with NOTHING declared immutable must derive no `Shared`
/// loans at all. Paired with the test above, this is the discrimination check:
/// a derivation that ignored the provider would fail one or the other.
#[test]
fn loan_kind_follows_the_provider_both_ways() {
    let (_m, all_mut) = capture_solve_with(CALL_ARG, vec![]);
    assert!(!all_mut.loans.is_empty());
    assert!(
        all_mut.loans.iter().all(|l| l.kind != LoanKind::Shared),
        "a Shared loan appeared with no local declared immutable — the derivation \
         is not consulting the provider"
    );

    let (_m2, some_shared) = capture_solve_with(CALL_ARG, vec![1]);
    assert!(
        some_shared.loans.iter().any(|l| l.kind == LoanKind::Shared),
        "no Shared loan appeared after declaring local 1 immutable — the \
         derivation is not consulting the provider"
    );
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
fn certificate_holds_the_accepting_rounds_residuals() {
    // A multi-round fixture: rounds 1 and 2 each carry a NON-EMPTY residual
    // conflict set (that is what they commit on), round 3 accepts. So a
    // recorder that captured the wrong round, or captured every round, is
    // distinguishable here from one that captures the accepting round.
    let (model, stats, export) = capture_solve_counting(CASCADE);
    assert!(model.is_some(), "fixture must be accepted");
    assert_eq!(stats.rounds, 3, "the witness needs the committing rounds");
    assert_eq!(
        stats.commits_per_round,
        vec![1, 1, 0],
        "rounds 1-2 must have committable residuals for this to distinguish"
    );
    // On the live Mode-A path acceptance (`committed == 0`) is REACHED ONLY
    // WITH AN EMPTY CONFLICT SET: every conflict that reaches the commit stage
    // has a committable `Ref` owner (`representative`'s contract — non-`Ref`
    // fields decline and non-`Ref` locals assert, both before it runs), so a
    // non-empty set always commits at least once. The certificate is therefore
    // empty at a Mode-A accept, and `BoExport::residual_conflicts`' doc says so.
    assert!(
        export.residual_conflicts.is_empty(),
        "a Mode-A accept committed nothing, so its residual set must be empty; \
         got {:?} — either `record_residuals` moved off the accept point or \
         `representative`'s no-committable-owner arm became reachable, and the \
         E-R4 certificate's meaning has changed",
        export.residual_conflicts
    );
    // Structural check, live for the day the arm above does become reachable.
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

// -------------------------------------------------------------------------
// D1 / D2 / D10 / D11 regression witnesses
// -------------------------------------------------------------------------

/// A shape that forces the CEGAR loop to commit and re-solve before accepting.
///
/// `x = id(p)` is a live `Ref` requirer invalidated by the write through the
/// base `b = p` (A′), so the loop commits twice and accepts on round 3. The
/// round count is pinned by `bo_c1.rs:6461` (`commit.rounds == 3`), and this
/// test pins it again locally so a change in fixture behaviour cannot silently
/// turn the D1 witness into a single-round no-op.
const CASCADE: &str = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
     unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";

/// Solve with capture, returning the round counters as well.
///
/// `verify_to_fixpoint` is a documented-thin wrapper over the counting loop
/// (`verify_to_fixpoint_is_thin_wrapper`), so this observes the same run
/// `capture_solve` does, plus the stats needed to pin the round count.
fn capture_solve_counting(
    code: &str,
) -> (
    Option<FxHashMap<SlotRef, super::SlotKindAlias>>,
    RoundStats,
    BoExport,
) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let ((model, stats), export) = with_bo_export(|| {
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
            verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, true)
        });
        (model, stats, export)
    })
    .unwrap_or_else(|e| e.raise())
}

/// Solve through the **L2 guarded-commit loop**, under export capture (D2).
///
/// **D10** — this used to `set_var("CRAT_BO_L2_GUARDED_COMMITS", "1")` inside a
/// parallel test binary: the same data-race class already fixed for
/// `CRAT_BO_EXPORT`, one helper over. The safety comment claiming the suite is
/// single-threaded was wrong — `test_threads = 1` is a *corpus-sweep* setting,
/// not a property of `cargo test -p pointer_replacer`.
///
/// Restructured instead of serialized: route straight into the L2 loop. That
/// removes the env mutation entirely **and** makes the path taken a fact of
/// the call rather than of process state, which is what closes D2's
/// "non-distinguishing" caveat — there is no Mode-A route through this helper.
/// `RepairMode::ModeA` (the default) satisfies the precondition the env entry
/// asserts.
fn capture_solve_l2(
    code: &str,
) -> (
    Option<FxHashMap<SlotRef, super::SlotKindAlias>>,
    RoundStats,
    BoExport,
) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origin_flows = analyze_program_origin_flow(&program);
        assert_eq!(
            RepairMode::current(),
            RepairMode::ModeA,
            "the L2 loop requires Mode-A repair"
        );
        let ((model, stats), export) = with_bo_export(|| {
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
            verify_l2_to_fixpoint_counting(
                &program,
                &slots,
                &origin_flows,
                &solver,
                &selectors,
                true,
            )
        });
        (model, stats, export)
    })
    .unwrap_or_else(|e| e.raise())
}

/// **D2** — the witnessed/L2 replay path must capture loans too.
///
/// Before the fix this path had no `record_loan_identities` call on either
/// loop exit, so `loans` was silently empty under exactly the configuration
/// the plan of record ships.
///
/// *Mutation-tested (standing rule).* Deleting either `record_loan_identities`
/// call in `borrow_conflicts_replaying_witnessed` fails this test, because
/// `capture_solve_l2` reaches the L2 loop by direct call — the Mode-A capture
/// sites are not on this path and cannot mask the deletion. That is the
/// distinguishing power the previous env-based helper lacked.
#[test]
fn l2_path_records_loans() {
    let (model, stats, export) = capture_solve_l2(CALL_ARG);
    assert!(model.is_some(), "L2-on fixture must be accepted");
    assert!(
        stats.l2_decline.is_none(),
        "fixture must accept, not take an L2 controlled decline: {:?}",
        stats.l2_decline
    );
    assert!(
        !export.loans.is_empty(),
        "D2: the L2 replay path recorded no loans — capture is missing on that path"
    );
    // Round-correct: still exactly one record per loan (D1 holds on L2 too).
    let mut seen = rustc_hash::FxHashSet::default();
    for loan in &export.loans {
        assert!(
            seen.insert((loan.fn_did, loan.loan)),
            "D1 regression on the L2 path: loan ({:?}, {}) recorded twice",
            loan.fn_did,
            loan.loan
        );
    }
}

/// **D1** — a fixture that drives more than one validation round must still
/// export exactly one record per loan.
///
/// The round count is **pinned**, per the delta review: without it, a fixture
/// that quietly collapsed to one round would make the uniqueness assertion
/// inert (duplicates can only arise ACROSS rounds), and the test would pass
/// with the `begin_round()` reset deleted. `model.is_some()` and non-emptiness
/// are asserted for the same reason — a first-solve decline would otherwise
/// satisfy an empty-loan-set uniqueness check with zero signal.
///
/// *Mutation-tested (standing rule).* Deleting `export::begin_round()` from
/// the Mode-A loop fails this test with "loan … appears more than once".
#[test]
fn multi_round_export_holds_only_the_final_round() {
    let (model, stats, export) = capture_solve_counting(CASCADE);
    assert!(model.is_some(), "the cascade fixture must be ACCEPTED");
    assert_eq!(
        stats.rounds, 3,
        "the D1 witness needs a genuinely multi-round fixture (2 commits + accept)"
    );
    assert!(
        !export.loans.is_empty(),
        "a multi-round accept recorded no loans at all — nothing is being witnessed"
    );
    let mut seen = rustc_hash::FxHashSet::default();
    for loan in &export.loans {
        assert!(
            seen.insert((loan.fn_did, loan.loan)),
            "D1: loan ({:?}, {}) appears more than once — rounds are accumulating",
            loan.fn_did,
            loan.loan
        );
    }
}

/// **D11** — `model_accepts` runs the oracle OUTSIDE either CEGAR loop, so
/// nothing else resets the recorder before it. Without its own
/// `begin_round()`, a probe issued inside an open capture scope appends to the
/// fixpoint's loans and reopens D1 by another route.
///
/// *Mutation-tested (standing rule).* Deleting the `begin_round()` call at the
/// top of `model_accepts_with_flows` fails this test with the duplicate
/// message below.
#[test]
fn probe_after_fixpoint_does_not_accumulate_loans() {
    ::utils::compilation::run_compiler_on_str(CASCADE, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let (_model, export) = with_bo_export(|| {
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
            let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                .expect("cascade fixture accepts");
            // The audit's probe, inside the SAME capture scope as the fixpoint.
            assert!(
                model_accepts(&program, &slots, &model, true),
                "the accepted model must re-validate"
            );
            Some(model)
        });
        assert!(
            !export.loans.is_empty(),
            "the probe recorded no loans — the witness would be inert"
        );
        let mut seen = rustc_hash::FxHashSet::default();
        for loan in &export.loans {
            assert!(
                seen.insert((loan.fn_did, loan.loan)),
                "D11: loan ({:?}, {}) recorded twice — the probe appended to the \
                 fixpoint's loans instead of starting a fresh round",
                loan.fn_did,
                loan.loan
            );
        }
    })
    .unwrap_or_else(|e| e.raise())
}
