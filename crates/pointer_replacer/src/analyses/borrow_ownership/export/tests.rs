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
        construction::{
            CopyLendMode, TestValidationBackend, construct_bo_into,
            verify_bo_construction_counting, verify_bo_construction_counting_for_test,
            verify_bo_construction_l2_for_test,
        },
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints, l2,
        mutability_facts::MutFacts,
        origin_flow::analyze_program_origin_flow,
        origins::compute_origins,
        solver::{
            KindSolver, SelectorTraceOutcome, SlotRef, with_assumption_check_trace,
            with_selector_trace,
        },
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

fn function_named(program: &RustProgram<'_>, name: &str) -> rustc_span::def_id::LocalDefId {
    program
        .functions
        .iter()
        .copied()
        .find(|did| program.tcx.item_name(did.to_def_id()).as_str() == name)
        .unwrap_or_else(|| panic!("missing function {name}"))
}

fn named_depth0_slot(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    function: rustc_span::def_id::LocalDefId,
    name: &str,
) -> SlotRef {
    let local = named_local(program, function, name);
    let slot = slots.fn_local_slots[&function]
        .slot_for_local_depth(local, 0)
        .unwrap_or_else(|| panic!("missing depth-zero slot for {name}"));
    SlotRef::Local(function, slot)
}

fn named_local(
    program: &RustProgram<'_>,
    function: rustc_span::def_id::LocalDefId,
    name: &str,
) -> rustc_middle::mir::Local {
    let body = program
        .tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    body.var_debug_info
        .iter()
        .find_map(|info| {
            (info.name.as_str() == name).then(|| match info.value {
                rustc_middle::mir::VarDebugInfoContents::Place(place) => Some(place.local),
                _ => None,
            })?
        })
        .unwrap_or_else(|| panic!("missing local {name}"))
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

/// RED 4 — capture is inert unless a scope is open.
///
/// **Also the D4 witness.** The first assertion fails if ambient enablement is
/// ever reintroduced — an env flag, a global, a lazy install inside
/// `capturing()` — because this test runs with no scope open. Mutation-tested:
/// restoring the `if flag_enabled() { install }` branch with the flag forced on
/// fails it here.
///
/// D18: this doc used to add "and allocates nothing when off". It does not
/// show that — the body observes `capturing()` and that recording is a no-op,
/// and asserts nothing about allocation. The zero-allocation property rests on
/// `record`'s early return, which is an argument, not a measurement. Claim
/// narrowed to what is actually asserted.
#[test]
fn export_off_records_nothing() {
    assert!(!capturing(), "capture must be inactive by default");
    // Recording outside a scope must be a no-op, not a panic.
    record_selector(BoundaryRole::Source, Var::from_u32(0));
    record_loan(LoanIdentity {
        key: LoanKey {
            fn_did: rustc_hir::def_id::CRATE_DEF_ID,
            place: PlaceKey {
                local: Local::from_u32(0),
                proj: Vec::new(),
            },
            location: MirLocationKey::new(0, 0),
            borrower: BorrowerKind::Assign {
                owner: OwnerKey::Local(0),
            },
        },
        run_local_handle: 0,
        kind: LoanKind::NoProvenance,
        class: LoanClass::Existing,
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
            seen.insert(loan.key.clone()),
            "loan {:?} recorded more than once — the export is accumulating \
             across validation rounds instead of holding the accepted round (D1)",
            loan.key
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
            .any(|l| matches!(l.key.borrower, BorrowerKind::CallArg { .. })),
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
        .filter(|l| matches!(l.key.borrower, BorrowerKind::CallArg { .. }))
        .collect();
    assert!(!call_args.is_empty(), "expected a CallArg loan");
    for loan in call_args {
        // The construction applies a Deref, so the projected place has depth
        // >= 1 while the KEY stays the base local.
        assert!(
            loan.key.place.derefs() >= 1,
            "CallArg loan should carry the deref projection: {:?}",
            loan.key.place
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
        let expected = if loan.key.place.local == Local::from_u32(1) {
            // Provenance exists (it is a pointer argument) and we declared it
            // immutable, so the engine's guard fires: Shared.
            LoanKind::Shared
        } else {
            // Mutable, or no provenance at all — either way NOT Shared.
            assert_ne!(
                loan.kind,
                LoanKind::Shared,
                "loan rooted at {:?} derived Shared, but only local 1 was declared immutable",
                loan.key.place.local
            );
            checked += 1;
            continue;
        };
        assert_eq!(
            loan.kind, expected,
            "derivation disagreed with the supplied provider for base local {:?} \
             (borrowed place {:?}) — the key or the lookup has drifted",
            loan.key.place.local, loan.key.place
        );
        checked += 1;
    }
    assert!(
        checked > 0,
        "no loan was actually checked against ground truth"
    );
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
        export.loans.iter().any(|l| l.key.place.derefs() >= 1),
        "expected at least one deref-projected borrowed place"
    );
}

// -------------------------------------------------------------------------
// RED 16-17: the E-R4 certificate
// -------------------------------------------------------------------------

/// RED 16 — **D14**: the E-R4 certificate is RECORDED at the accept point.
///
/// This is the assertion the previous two versions could not make. As a bare
/// `Vec`, "recorded, none tolerated" and "never recorded" were the same value,
/// so `is_empty()` held with the recorder deleted and the whole suite stayed
/// green — verified by running that mutation. `Option` separates the states and
/// `is_some()` is exactly the obligation.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** removing the
/// `record_residuals` call at the accept point leaves the field `None` and
/// fails this test. Only then the weaker perturbation: recording a fabricated
/// residual fails the emptiness assertion.
///
/// The emptiness assertion is retained but is **no longer load-bearing for
/// D14** — it records an empirical fact (ledger D15: no fixture is known that
/// tolerates a residual at accept, and the claim that none *can* was retracted).
#[test]
fn certificate_is_recorded_at_the_accept_point() {
    // A multi-round fixture: rounds 1 and 2 each commit, round 3 accepts — so a
    // recorder that fired on the wrong round is distinguishable from one that
    // fires at the accept.
    let (model, stats, export) = capture_solve_counting(CASCADE);
    assert!(model.is_some(), "fixture must be accepted");
    assert_eq!(stats.rounds, 3, "the witness needs the committing rounds");
    assert_eq!(
        stats.commits_per_round,
        vec![1, 1, 0],
        "rounds 1-2 must commit for this fixture to distinguish rounds"
    );
    // F3: `verify_to_fixpoint*` dispatches on `CRAT_BO_L2_GUARDED_COMMITS`, and
    // the L2 accept never calls `record_residuals` — a documented gap (D2
    // adjacent), so `None` there is CORRECT, not a defect. The first version of
    // this test asserted `is_some()` unconditionally and therefore FAILED under
    // the plan-of-record profile while blaming the accept point. Assert the
    // behaviour each path actually has: this turns an env-sensitivity that used
    // to be invisible under `Vec` into a tested property of both paths.
    if l2::enabled_from_env() {
        assert!(
            export.residual_conflicts.is_none(),
            "the L2 accept records no certificate, so it must be None — if this \
             fires, L2 grew a `record_residuals` call and the gap is closed"
        );
        return;
    }
    let residuals = export.residual_conflicts.as_ref().expect(
        "D14: the accept point ran but recorded no certificate — `record_residuals` \
         is missing from the `committed == 0` accept, or `begin_round()` cleared it \
         afterwards. `None` means NEVER RECORDED, which is not `Some(vec![])`",
    );
    // Empirical, not a theorem: no known fixture tolerates a residual at accept,
    // but the argument that none can was retracted (ledger D13/D15).
    assert!(
        residuals.is_empty(),
        "this fixture accepted while tolerating residuals {residuals:?} — that is \
         not wrong, but it is new: it would be the first known witness for D15, \
         and `BoExport::residual_conflicts`' doc should be updated to say the \
         shape is reachable"
    );
    // D18b: a "well-formedness" loop stood here asserting every residual has an
    // issuer or a requirer. It was DELETED, not repaired, for two reasons.
    // First it was unreachable either way — it iterated a collection the assert
    // above had just required to be empty, and on failure that assert aborted
    // first. Second, and worse, it was WRONG: an owner-less residual
    // (`issuer: None, requirers: []`) is not malformed, it is precisely the
    // shape D15 is hunting, so on the one day the loop could have run it would
    // have reported the wrong diagnosis. A missing check is honest; a check
    // that would misclassify the thing it fires on is not.
}

/// **F4** — a DECLINING run records no certificate.
///
/// This is the invariant the `Option` exists to carry and the half the positive
/// witness cannot reach: `None` must mean "the accept point never ran". The
/// positive test can only show that an accepting run records `Some`.
///
/// The decline is forced with a solver contradiction (a slot both assumed
/// `Ref` and excluded from `Ref`) rather than with a fixture, because no
/// declining fixture was found — see the limitation below.
///
/// **Stated limitation, not papered over.** This exercises the *pre-loop*
/// decline (the first solve returns UNSAT), so it pins the invariant for that
/// route only. It does **not** exercise the in-loop `residual_nonref_field`
/// decline, and therefore does NOT catch the specific relocation F4 named —
/// moving `record_residuals` above that decline. Four candidate fixtures were
/// probed for an in-loop decline (field own+borrow, aliased double free,
/// cross-function field escape, address-of-local store); all four accepted.
/// Recorded as residual rather than claimed as covered.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** make the decline path
/// record a certificate — e.g. `record_residuals(vec![])` before the early
/// return — and this fails.
#[test]
fn declining_run_records_no_certificate() {
    ::utils::compilation::run_compiler_on_str(CALL_ARG, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let (model, export) = with_bo_export(|| {
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
            // Force a contradiction on some slot: assumed `Ref` and excluded
            // from `Ref` at once.
            let victim = slots
                .fn_local_slots
                .iter()
                .find(|(_, universe)| universe.len() > 0)
                .map(|(did, _)| SlotRef::Local(*did, super::super::slots::SlotId::from_usize(0)))
                .expect("fixture has at least one local slot");
            solver.assume(victim, super::SlotKindAlias::Ref);
            solver.add_borrow_exclusion(Some(victim), &[]);
            verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
        });
        assert!(
            model.is_none(),
            "the contradiction did not force a decline — witness would be inert"
        );
        assert!(
            export.residual_conflicts.is_none(),
            "F4: a DECLINING run recorded a certificate. `None` must mean the \
             accept point never ran; anything else destroys the invariant the \
             Option was introduced to carry. Got {:?}",
            export.residual_conflicts
        );
    })
    .unwrap_or_else(|e| e.raise())
}

/// RED 17 — the exported candidacy agrees with the accepted model.
#[test]
fn certificate_candidacy_matches_model() {
    let (model, export) = capture_solve(MALLOC_FREE);
    let model = model.expect("accepted");
    // F3, as above: `None` is the correct L2 behaviour.
    if l2::enabled_from_env() {
        assert!(export.residual_conflicts.is_none());
        return;
    }
    let residuals = export
        .residual_conflicts
        .as_ref()
        .expect("the accept point must have recorded a certificate");
    // Every residual slot mentioned must exist in the accepted model, so the
    // certificate and the model describe the same slot universe.
    for r in residuals {
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
        assert_eq!(
            s.role,
            BoundaryRole::Source,
            "source vector index {i} misfiled"
        );
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

/// T2-W2 (addendum-55 erratum): an exact free endpoint whose incoming value
/// has no modeled origin cannot retain the endpoint assertion. The mandatory
/// licensing clause appears beside the typed T2 label, T2 yields first,
/// restoration fails, and the post-retraction model equals the no-T2 baseline.
#[test]
fn t2_unknown_origin_free_retracts_with_named_license_core() {
    const CODE: &str = r#"
unsafe extern "C" {
    fn opaque() -> *mut i32;
    fn free(p: *mut core::ffi::c_void);
}
unsafe fn release() {
    let p = opaque();
    free(p as *mut core::ffi::c_void);
}
"#;
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mut_facts = MutFacts::from_program(&program);
        let solver = KindSolver::new(&slots);
        let construction = construct_bo_into(
            &program,
            &slots,
            &origins,
            &mut_facts,
            &solver,
            CopyLendMode::Baseline,
        )
        .expect("shared construction");
        let sink_index = construction
            .selectors
            .keys()
            .iter()
            .position(|key| key.callee == "free" && key.role == BoundaryRole::Sink)
            .expect("typed free assertion");
        let ((model, _stats), trace) = with_selector_trace(|| {
            verify_bo_construction_counting(
                &program,
                &slots,
                &origins,
                &solver,
                &construction,
                &mut_facts,
            )
        });
        let model = model.expect("T2 retraction preserves acceptance");
        let baseline = solver
            .model_without_t2_for_test(&construction.selectors)
            .expect("no-T2 baseline accepts");
        assert_eq!(
            model, baseline,
            "W2 post-retraction model must equal baseline"
        );
        let release = function_named(&program, "release");
        let p = named_depth0_slot(&program, &slots, release, "p");
        assert_eq!(model.get(&p), baseline.get(&p));

        let epoch = trace.epochs.last().expect("T2 trace epoch");
        assert!(epoch.final_dropped.contains(&sink_index));
        let dropped = epoch
            .events
            .iter()
            .find(|event| event.selector_index == sink_index && event.core_labels.len() > 1)
            .expect("typed T2+license core");
        assert!(
            dropped
                .core_labels
                .iter()
                .any(|label| label.contains("t2-assert"))
        );
        assert!(
            dropped
                .core_labels
                .iter()
                .any(|label| label.contains("own-assume") || label.contains("link-own"))
        );
        assert!(epoch.events.iter().any(|event| {
            event.selector_index == sink_index
                && event.outcome == SelectorTraceOutcome::StayedDropped
        }));
    })
    .unwrap_or_else(|error| error.raise());
}

/// T2-N1: a long move chain receives assertions at its allocation and
/// deallocation endpoints only. Chain middles remain governed exclusively by
/// existing transfer/coherence constraints.
#[test]
fn t2_chain_middles_do_not_receive_assertions() {
    const CODE: &str = r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
unsafe fn chain() {
    let p = malloc(4) as *mut i32;
    let q = p;
    let r = q;
    free(r as *mut core::ffi::c_void);
}
"#;
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let solver = KindSolver::new(&slots);
        let construction = construct_bo_into(
            &program,
            &slots,
            &origins,
            &facts,
            &solver,
            CopyLendMode::Baseline,
        )
        .expect("shared construction");
        let keys = construction.selectors.keys();
        assert_eq!(keys.len(), 2, "only malloc/free endpoints may assert");
        assert_eq!(
            keys.iter()
                .map(|key| key.callee.as_str())
                .collect::<Vec<_>>(),
            vec!["malloc", "free"]
        );
    })
    .unwrap_or_else(|error| error.raise());
}

/// T2-N2: local functions that merely reuse libc spellings are not boundary
/// rows and therefore create no endpoint assertions.
#[test]
fn t2_local_wrapper_names_do_not_match_foreign_boundaries() {
    const CODE: &str = r#"
unsafe fn malloc(_n: usize) -> *mut i32 { core::ptr::null_mut() }
unsafe fn free(_p: *mut i32) {}
unsafe fn wrapper() {
    let p = malloc(4);
    free(p);
}
"#;
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let solver = KindSolver::new(&slots);
        let construction = construct_bo_into(
            &program,
            &slots,
            &origins,
            &facts,
            &solver,
            CopyLendMode::Baseline,
        )
        .expect("shared construction");
        assert!(construction.selectors.keys().is_empty());
    })
    .unwrap_or_else(|error| error.raise());
}

/// Observation-only W1 causal-chain dump authorized after the first T2
/// MAX-3 stop. It makes no assertion about the expected repair; the diagnostic
/// output is the deliverable.
#[test]
fn t2_w1_causal_chain_diagnostic() {
    const CODE: &str = r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
unsafe fn chain() {
    let p = malloc(core::mem::size_of::<i32>()) as *mut i32;
    let q = p;
    free(q as *mut core::ffi::c_void);
}
"#;
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let arm = arm_scope();
        let solver = KindSolver::new(&slots);
        let construction = construct_bo_into(
            &program,
            &slots,
            &origins,
            &facts,
            &solver,
            CopyLendMode::Baseline,
        )
        .expect("shared construction");
        eprintln!("T2-W1 keys={}", construction.selectors.keys().len());
        for (index, (key, literal)) in construction
            .selectors
            .keys()
            .iter()
            .zip(construction.selectors.all())
            .enumerate()
        {
            eprintln!("T2-W1 key[{index}]={} literal={literal}", key.label());
        }

        let (((model, stats), checks), selector_trace) = with_selector_trace(|| {
            with_assumption_check_trace(|| {
                verify_bo_construction_counting(
                    &program,
                    &slots,
                    &origins,
                    &solver,
                    &construction,
                    &facts,
                )
            })
        });
        let export = arm.finish();
        for (index, check) in checks.iter().enumerate() {
            let t2 = construction
                .selectors
                .all()
                .iter()
                .enumerate()
                .filter(|(_, literal)| check.bundle.iter().any(|item| item == *literal))
                .map(|(index, _)| index)
                .collect::<Vec<_>>();
            eprintln!(
                "T2-W1 check[{index}] phase={:?} outcome={:?} explicit={} bundle={} t2={t2:?}",
                check.phase,
                check.outcome,
                check.explicit.len(),
                check.bundle.len(),
            );
            eprintln!("T2-W1 check[{index}] labels={:?}", check.labels);
        }
        for (epoch, trace) in selector_trace.epochs.iter().enumerate() {
            eprintln!(
                "T2-W1 epoch[{epoch}] final_dropped={:?} events={:#?}",
                trace.final_dropped, trace.events
            );
        }

        let model = model.expect("W1 accepts");
        let chain = function_named(&program, "chain");
        let p_slot = named_depth0_slot(&program, &slots, chain, "p");
        let q_slot = named_depth0_slot(&program, &slots, chain, "q");
        let owns = export.version_owns.as_ref().expect("version ownerships");
        for (name, local, slot) in [
            ("p", named_local(&program, chain, "p"), p_slot),
            ("q", named_local(&program, chain, "q"), q_slot),
        ] {
            let versions = export
                .version_sites
                .iter()
                .filter(|site| site.fn_did == chain && site.local == local)
                .map(|site| {
                    let use_value = site.use_var.map(|var| (var, owns[var]));
                    let def_value = site.def_var.map(|var| (var, owns[var]));
                    (site.location, use_value, def_value)
                })
                .collect::<Vec<_>>();
            eprintln!(
                "T2-W1 model {name}: versions={versions:?} own_bit={} kind={:?}",
                model.get(&slot) == Some(&SlotKindAlias::Owning),
                model.get(&slot)
            );
        }
        eprintln!(
            "T2-W1 stats dropped_sources={} dropped_sinks={} optimize_materializations={}",
            stats.dropped_sources,
            stats.dropped_sinks,
            solver.optimize_materialization_count(),
        );
    })
    .unwrap_or_else(|error| error.raise());
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
    let pairs: rustc_hash::FxHashSet<_> = export
        .version_sites
        .iter()
        .map(|s| (s.fn_did, s.local))
        .collect();
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

fn capture_solve_counting_backend(
    code: &str,
    backend: TestValidationBackend,
) -> (
    Option<FxHashMap<SlotRef, super::SlotKindAlias>>,
    RoundStats,
    BoExport,
) {
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mut_facts = MutFacts::from_program(&program);
        let ((model, stats), export) = with_bo_export(|| {
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &mut_facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("shared construction");
            verify_bo_construction_counting_for_test(
                &program,
                &slots,
                &origins,
                &solver,
                &construction,
                &mut_facts,
                backend,
            )
        });
        (model, stats, export)
    })
    .unwrap_or_else(|error| error.raise())
}

#[test]
fn decomposed_multi_round_model_commits_and_export_match_legacy() {
    let legacy = capture_solve_counting_backend(CASCADE, TestValidationBackend::LegacyOptimize);
    let decomposed =
        capture_solve_counting_backend(CASCADE, TestValidationBackend::HardCheckRoundOptimize);
    assert_eq!(decomposed, legacy);
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
                None,
            )
        });
        (model, stats, export)
    })
    .unwrap_or_else(|e| e.raise())
}

fn capture_solve_l2_backend(
    code: &str,
    backend: TestValidationBackend,
) -> (
    Option<FxHashMap<SlotRef, super::SlotKindAlias>>,
    RoundStats,
    BoExport,
) {
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mut_facts = MutFacts::from_program(&program);
        let ((model, stats), export) = with_bo_export(|| {
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &mut_facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("shared construction");
            verify_bo_construction_l2_for_test(
                &program,
                &slots,
                &origins,
                &solver,
                &construction,
                &mut_facts,
                backend,
            )
        });
        (model, stats, export)
    })
    .unwrap_or_else(|error| error.raise())
}

#[test]
fn decomposed_l2_model_actions_and_export_match_legacy() {
    let legacy = capture_solve_l2_backend(CASCADE, TestValidationBackend::LegacyOptimize);
    let decomposed =
        capture_solve_l2_backend(CASCADE, TestValidationBackend::HardCheckRoundOptimize);
    assert_eq!(decomposed, legacy);
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
    // D18a: an `l2_decline.is_none()` assertion stood here and was counted as
    // strengthening. It CANNOT FIRE — every `record_l2_decline` call site is
    // immediately followed by `return (None, stats)`, so it is implied by the
    // `model.is_some()` below. Removed rather than left as decoration.
    let (model, _stats, export) = capture_solve_l2(CALL_ARG);
    assert!(model.is_some(), "L2-on fixture must be accepted");
    assert!(
        !export.loans.is_empty(),
        "D2: the L2 replay path recorded no loans — capture is missing on that path"
    );
    // Round-correct: still exactly one record per loan (D1 holds on L2 too).
    let mut seen = rustc_hash::FxHashSet::default();
    for loan in &export.loans {
        assert!(
            seen.insert(loan.key.clone()),
            "D1 regression on the L2 path: loan {:?} recorded twice",
            loan.key
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
            seen.insert(loan.key.clone()),
            "D1: loan {:?} appears more than once — rounds are accumulating",
            loan.key
        );
    }
}

/// **D17** — the `pub(crate)` L2 door carries the load-bearing precondition.
///
/// A tracked solver's hard constraints are track-gated, so every solve in this
/// loop would be vacuously SAT and the accepted model meaningless. The door
/// refuses one, naming itself in the message.
///
/// **The `expected` string is deliberately door-specific.** The first version
/// matched "tracked KindSolver must not enter", and passed with the door's
/// assert DELETED — because `KindSolver::model_kinds_relaxing` carries its own
/// release-active guard whose message shares that prefix, and the loop hits it
/// moments later. That is worth stating plainly: the hazard was already guarded
/// release-active, so this door's `debug_assert!` is a fail-earlier tripwire,
/// not the thing preventing a meaningless model.
///
/// *Mutation-tested (standing rule), Rider 0 order.* **Deletion first:**
/// removing the `debug_assert!` makes this test fail — the panic that does
/// occur comes from the solver accessor and no longer matches `expected`.
#[test]
// F2: `debug_assert!` is compiled out in release, where the panic instead comes
// from `model_kinds_relaxing`'s own release-active guard with a DIFFERENT
// message — so this `expected` would not match and the test would fail on
// `cargo test --release`. Gate it on the profile that has the assert. The
// hazard itself remains guarded in release by that downstream assert, which is
// the finding that made this door's tripwire fail-earlier rather than
// load-bearing.
#[cfg(debug_assertions)]
#[should_panic(expected = "must not enter the l2 door")]
fn l2_door_rejects_a_tracked_solver() {
    ::utils::compilation::run_compiler_on_str(CALL_ARG, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origin_flows = analyze_program_origin_flow(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        // The one thing the door must refuse.
        let solver = KindSolver::new_tracked(&slots);
        let (_stats, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("emission");
        let _ = verify_l2_to_fixpoint_counting(
            &program,
            &slots,
            &origin_flows,
            &solver,
            &selectors,
            true,
            None,
        );
        None::<()>
    })
    .unwrap_or_else(|e| e.raise());
}

/// **§1.5 / D19** — loan KEYS are stable across re-inference; indices are not.
///
/// This is the witness the whole content-key change exists for. `BorrowSet`
/// numbering permutes because `utils/dsa/union_find.rs` hashes with
/// `RandomState` and `borrow/mod.rs` pushes sibling loans in `group()` order,
/// and a fresh `UnionFind` is built per inference — so two analyses of the same
/// program can number the same loans differently.
///
/// **Non-vacuity is asserted, not assumed:** the fixture must produce sibling
/// loans (more than one loan at one location), or the permutation has nothing
/// to permute and the test proves nothing.
///
/// *Mutation-tested, Rider 0 order.* The mutation actually run compares
/// `(fn_did, run_local_handle, place.local)` triples instead of `key`s:
/// **failed 8/8 runs; unmutated passed 8/8.**
///
/// **Correction to an earlier version of this note**, which said the mutation
/// was "compare `run_local_handle` sets instead of `key` sets". That recipe is
/// WEAKER than what was run and would NOT fail: handles are exactly
/// `0..n_f-1` per function in both runs (`record_loan_identities` walks
/// `loans.iter_enumerated()` with no filtering), so the bare-handle sets are
/// equal by construction. The measurement is real; the recipe as written
/// described a different mutation.
///
/// **Known gap (not fixed here):** nothing asserts a permutation actually
/// OCCURRED between the two runs, so this witness would silently stop guarding
/// if `utils/dsa/union_find.rs` ever used a deterministic hasher. The stronger
/// form is to build `handle -> key` maps for both runs and `assert_ne!` them.
#[test]
fn loan_keys_are_stable_across_reinference() {
    let first = capture_solve(CASCADE).1;
    let second = capture_solve(CASCADE).1;

    assert!(!first.loans.is_empty(), "no loans recorded — witness inert");
    // Non-vacuity: sibling loans exist (>1 loan sharing one (fn, location)).
    let mut per_site: rustc_hash::FxHashMap<_, usize> = Default::default();
    for l in &first.loans {
        *per_site.entry((l.key.fn_did, l.key.location)).or_default() += 1;
    }
    // NOTE (accepted limitation): >1 loan at one site is a PROXY for a
    // multi-member `group()`, and it is not exact — a call with two pointer
    // arguments also puts two `CallArg` loans at one terminator, and those come
    // from a deterministic `args.iter().enumerate()`, not from `group()`. For
    // CASCADE (single-argument `id`) the proxy is satisfied via group siblings,
    // but a different fixture could satisfy it with nothing permutable.
    assert!(
        per_site.values().any(|n| *n > 1),
        "fixture has no sibling loans, so nothing can permute — this witness \
         would be vacuous. Pick a fixture whose group() returns >1 member."
    );

    let keys_a: std::collections::BTreeSet<_> = first.loans.iter().map(|l| l.key.clone()).collect();
    let keys_b: std::collections::BTreeSet<_> =
        second.loans.iter().map(|l| l.key.clone()).collect();
    assert_eq!(
        keys_a, keys_b,
        "D19: loan CONTENT keys differed between two analyses of the same \
         program. The key is supposed to be numbering-independent."
    );
    assert_eq!(
        first.loans.len(),
        second.loans.len(),
        "loan COUNT differed between runs"
    );
}

/// **§1.5 (deterministic form)** — an INJECTED push-order permutation leaves
/// the key set unchanged while the handles move.
///
/// This replaces the hash-seed-dependent half of the stability witness. The
/// previous form ran the analysis twice and relied on `RandomState` actually
/// permuting `group()` between the two runs — true today (measured 8/8), but
/// contingent: it would silently stop guarding if `utils/dsa/union_find.rs`
/// ever used a deterministic hasher, and its "sibling loans exist" proxy is
/// satisfiable by two `CallArg` loans at one terminator, which come from a
/// deterministic `args.iter().enumerate()` and cannot permute at all (ADV-3).
///
/// Here the permutation is INJECTED rather than hoped for: the same loan
/// records are built twice with explicitly reversed push order. Content keys
/// must be identical as a SET; handles must actually differ, which is asserted
/// so the test cannot pass by accident on an empty or singleton set.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** put
/// `run_local_handle` back into `LoanKey` (or key the set on
/// `(key, run_local_handle)`) and the two key sets diverge — deterministically,
/// on every run, with no hash-seed reliance.
#[test]
fn injected_push_order_permutation_preserves_keys() {
    fn identity(handle: usize, local: u32, field: u32) -> LoanIdentity {
        LoanIdentity {
            key: LoanKey {
                fn_did: rustc_hir::def_id::CRATE_DEF_ID,
                place: PlaceKey {
                    local: Local::from_u32(local),
                    proj: vec![ProjKey::Deref, ProjKey::Field(field)],
                },
                location: MirLocationKey::new(1, 3),
                borrower: BorrowerKind::Assign {
                    owner: OwnerKey::Local(local),
                },
            },
            run_local_handle: handle,
            kind: LoanKind::Mut,
            class: LoanClass::Existing,
            invalid: false,
        }
    }

    // Sibling loans at ONE location, exactly the shape `group()` produces:
    // same owner, same point, distinct base locals.
    let siblings: Vec<(u32, u32)> = vec![(1, 0), (2, 1), (3, 2)];

    let forward: Vec<LoanIdentity> = siblings
        .iter()
        .enumerate()
        .map(|(h, (local, field))| identity(h, *local, *field))
        .collect();
    // The injected permutation: same loans, reversed push order, so the
    // handles land on different loans.
    let reversed: Vec<LoanIdentity> = siblings
        .iter()
        .rev()
        .enumerate()
        .map(|(h, (local, field))| identity(h, *local, *field))
        .collect();

    let keys_forward: std::collections::BTreeSet<_> =
        forward.iter().map(|l| l.key.clone()).collect();
    let keys_reversed: std::collections::BTreeSet<_> =
        reversed.iter().map(|l| l.key.clone()).collect();
    assert_eq!(
        keys_forward, keys_reversed,
        "content keys must be invariant under push-order permutation — that is \
         the whole reason LoanKey exists (D19)"
    );

    // Non-vacuity, deterministic: the permutation genuinely moved the handles.
    let pairs_forward: std::collections::BTreeSet<_> = forward
        .iter()
        .map(|l| (l.run_local_handle, l.key.place.local))
        .collect();
    let pairs_reversed: std::collections::BTreeSet<_> = reversed
        .iter()
        .map(|l| (l.run_local_handle, l.key.place.local))
        .collect();
    assert_ne!(
        pairs_forward, pairs_reversed,
        "the injected permutation did not move any handle, so the key-invariance \
         assertion above proves nothing"
    );
}

/// **§1.5** — the run-local handle must not leak into the consumer as identity.
///
/// A grep-shaped guard in the same family as the import-denylist test: the
/// greenfield rewriter module may name the content key, never the handle.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** add a single
/// `run_local_handle` mention under `bo_rewriter/` and this fails.
#[test]
fn run_local_handle_is_not_used_as_identity() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/bo_rewriter");
    let mut offenders = Vec::new();
    let mut stack = vec![root.clone()];
    let mut files_scanned = 0usize;
    while let Some(dir) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in rd.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                files_scanned += 1;
                let text = std::fs::read_to_string(&path).expect("read bo_rewriter source");
                if text.contains("run_local_handle") {
                    offenders.push(path);
                }
            }
        }
    }
    assert!(
        files_scanned > 0,
        "scanned no files under {root:?} — the guard would be vacuous"
    );
    assert!(
        offenders.is_empty(),
        "bo_rewriter names the run-local loan handle, which is NOT an identity \
         (D19 permutes it between runs and between CEGAR rounds). Use \
         `LoanIdentity::key`. Offending files: {offenders:?}"
    );
}

/// **ALLOW-LIST (ruling on ADV-1)** — probe barrage: work outside the armed
/// region records nothing, and the region's boundary is load-bearing.
///
/// Replaces the two suspension-era witnesses. Those tested a DENY-LIST — "each
/// probe surface suspends capture" — which shipped incomplete twice (F1 found
/// four surfaces; ADV-1 then found a fifth and sixth reached through a helper).
/// The property is positional now: capture is armed only around the accepted
/// run, so anything outside it records nothing with no list to maintain.
///
/// The barrage runs representatives of the shapes that corrupted the export
/// under the deny-list: a full RE-EMISSION (the `build_probe_base` shape, which
/// appended a second copy of every selector site), a SECOND full fixpoint (the
/// CHECK_REAL shape, whose `begin_round()` wiped the certificate), and a
/// COUNTERFACTUAL oracle probe (the `probe_accepts_with_ref` /
/// `measure_collateral` shape, which overwrote `version_owns`).
///
/// Two assertions, the second keeping the first honest:
/// 1. the NARROW (shipped) arm yields exactly the accepted run's export;
/// 2. a WIDE arm that swallows the barrage yields a DIFFERENT export.
///
/// (2) is the mutation, built in: it proves the barrage genuinely corrupts, so
/// (1) cannot pass vacuously. Widening the shipped arm in `run_bo` reproduces
/// case (2); this test pins case (1) as the contract.
#[test]
fn probes_outside_the_armed_region_record_nothing() {
    ::utils::compilation::run_compiler_on_str(CASCADE, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);

        let accepted_run = || {
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
                .expect("cascade fixture accepts")
        };

        // Recording shapes: safe to run in either position.
        let barrage = || {
            // (i) re-emission — the probe-base shape.
            let ctxt2 = CrateCtxt::new(&program);
            let solver2 = KindSolver::new(&slots);
            let (_s2, sel2) = emit_crate_ownership_constraints(
                &ctxt2,
                &slots,
                &compute_origins(&program),
                &solver2,
            )
            .expect("re-emission");
            // (ii) a second full fixpoint — the CHECK_REAL shape.
            let _ = verify_to_fixpoint(&program, &slots, &solver2, &sel2, true);
        };
        // (iii) the counterfactual ORACLE probe. Only legal outside the arm:
        // inside it, the allow-list tripwire in `model_accepts_with_flows`
        // fires by design (witnessed by
        // `oracle_probe_inside_the_armed_region_trips_the_wire`).
        let oracle_probe = |model: &FxHashMap<SlotRef, super::SlotKindAlias>| {
            let counterfactual: FxHashMap<SlotRef, super::SlotKindAlias> = model
                .keys()
                .map(|k| (*k, super::SlotKindAlias::Ref))
                .collect();
            let _ = model_accepts(&program, &slots, &counterfactual, true);
        };

        // (1) NARROW arm — the shipped boundary; barrage runs after finish().
        let arm = arm_scope();
        let model = accepted_run();
        let narrow = arm.finish();
        barrage();
        oracle_probe(&model);
        assert!(
            !narrow.loans.is_empty(),
            "accepted run recorded nothing — inert"
        );
        // F3 pattern: the L2 accept never calls `record_residuals` (the
        // documented D2-adjacent gap), so `None` there is CORRECT. Asserting
        // it explicitly turns that env-sensitivity into a tested property of
        // both paths instead of a failure that blames the accepted run.
        if l2::enabled_from_env() {
            assert!(
                narrow.residual_conflicts.is_none(),
                "the L2 accept records no certificate, so it must be None"
            );
        } else {
            assert!(
                narrow.residual_conflicts.is_some(),
                "accepted run recorded no certificate — inert"
            );
        }

        // Reference: the accepted run with no barrage at all.
        let arm2 = arm_scope();
        let _ = accepted_run();
        let reference = arm2.finish();
        assert_eq!(
            narrow, reference,
            "the barrage changed the export even though it ran OUTSIDE the arm"
        );

        // (2) WIDE arm — the built-in mutation.
        let arm3 = arm_scope();
        let _model3 = accepted_run();
        barrage();
        let wide = arm3.finish();
        assert_ne!(
            wide, narrow,
            "the barrage did NOT corrupt an over-wide arm, so assertion (1) \
             proves nothing — pick probes that actually record"
        );
    })
    .unwrap_or_else(|e| e.raise())
}

/// **ALLOW-LIST TRIPWIRE** — an oracle probe inside the armed region fails loud.
///
/// The `with_capture_suspended` that used to sit in `model_accepts_with_flows`
/// was replaced by an assertion rather than deleted. Suspension would MASK an
/// allow-list violation — a probe that somehow ran inside the armed region
/// would quietly record nothing and look correct; the assertion names the
/// invariant instead. A backstop that hides the bug it backstops is worse than
/// no backstop.
///
/// `#[cfg(debug_assertions)]` for the same reason as the L2 door witness: a
/// `debug_assert!` is compiled out in release, where this would not panic.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `debug_assert!` and no panic occurs, so `should_panic` is unsatisfied.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "allow-list violation")]
fn oracle_probe_inside_the_armed_region_trips_the_wire() {
    ::utils::compilation::run_compiler_on_str(CALL_ARG, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let _arm = arm_scope();
        let model: FxHashMap<SlotRef, super::SlotKindAlias> = FxHashMap::default();
        // Armed region + probe entry point = the violation the wire names.
        let _ = model_accepts(&program, &slots, &model, true);
        None::<()>
    })
    .unwrap_or_else(|e| e.raise());
}

/// **GATE (closing addendum)** — `CRAT_BO_EXPORT` is fail-loud on bad values.
///
/// Exercised through the pure parse, never by mutating the process
/// environment: the suite runs tests in parallel, and env mutation is the D10
/// race class this project has already paid for twice.
#[test]
fn export_flag_rejects_invalid_value() {
    assert!(!export_enabled_from_value(None), "unset must mean off");
    assert!(!export_enabled_from_value(Some("0")));
    assert!(export_enabled_from_value(Some("1")));
    let bad = std::panic::catch_unwind(|| export_enabled_from_value(Some("2")));
    assert!(bad.is_err(), "CRAT_BO_EXPORT=2 must fail loudly");
}

/// **GATE (closing addendum)** — with the flag OFF (the default), the ambient
/// arm records nothing.
///
/// This is what restores timing comparability for the sweep: `run_bo` arms
/// through `arm_capture`, so an unset flag means the corpus worker pays no
/// recording cost and its `t_emit_s`/`t_fixpoint_s` stay comparable to rows
/// banked before the arm existed.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `if !flag_enabled()` early return from `arm_capture` and this fails — the
/// arm installs a buffer, the accepted run records, and the export is
/// non-empty.
#[test]
fn ambient_arm_is_inert_when_the_flag_is_off() {
    assert!(
        !flag_enabled(),
        "this test characterises the DEFAULT; CRAT_BO_EXPORT is set in this \
         process, so it cannot"
    );
    ::utils::compilation::run_compiler_on_str(CALL_ARG, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let arm = arm_capture();
        // A real accepted run, so the capture points genuinely execute.
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
        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true);
        assert!(
            model.is_some(),
            "fixture must be accepted — else witness inert"
        );
        assert!(
            !capturing(),
            "flag off, yet capture is active — the ambient arm is not gated"
        );
        let export = arm.finish();
        assert_eq!(
            export,
            BoExport::default(),
            "flag off, yet the ambient arm recorded: {export:?}"
        );
        Some(())
    })
    .unwrap_or_else(|e| e.raise());
}
