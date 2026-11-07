//! Production fixpoint controls for loanless source-retirement obligations.

use std::sync::Arc;

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Location, VarDebugInfoContents};

use super::CoverageDisposition;
use crate::{
    analyses::{
        borrow_ownership::{
            SlotKind,
            borrow_verify::with_plain_commit_trace,
            construction::{
                CopyLendMode, TestValidationBackend, construct_bo_into,
                verify_bo_construction_counting_for_test, verify_bo_construction_l2_for_test,
            },
            crate_slots::CrateSlots,
            export::with_bo_export,
            mutability_facts::MutFacts,
            origins::compute_origins,
            solver::{KindSolver, SlotRef},
            source_events::{SourcePhase, SourceRole},
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn f(p: *const u8, alias: *mut u8) -> u8 {
    let v = *p;
    free(alias);
    v
}
"#;

fn check_rounds(force_ref: bool) {
    for backend in [
        TestValidationBackend::HardCheckRoundOptimize,
        TestValidationBackend::LegacyOptimize,
    ] {
        for l2 in [false, true] {
            ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
                let mut functions = Vec::new();
                let mut structs = Vec::new();
                for owner in tcx.hir_crate(()).owners.iter() {
                    let Some(owner) = owner.as_owner() else { continue };
                    let OwnerNode::Item(item) = owner.node() else { continue };
                    match item.kind {
                        ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                        ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                        _ => {}
                    }
                }
                let program = RustProgram { tcx, functions, structs };
                let function = *program.functions.iter().find(|function| tcx.item_name(function.to_def_id()).as_str() == "f").unwrap();
                let body = tcx.mir_drops_elaborated_and_const_checked(function).borrow();
                let p = body.var_debug_info.iter().find_map(|info| {
                    if info.name.as_str() != "p" { return None; }
                    let VarDebugInfoContents::Place(place) = info.value else { return None };
                    place.as_local()
                }).expect("source parameter p");
                assert!(p.as_usize() > 0 && p.as_usize() <= body.arg_count);
                let frees: Vec<_> = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
                    let call = data.terminator().as_call(tcx)?;
                    matches!(call.func, CallKind::LibC(name) if name.as_str() == "free")
                        .then_some(Location { block, statement_index: data.statements.len() })
                }).collect();
                assert_eq!(frees.len(), 1, "exact source retirement site");
                let free = frees[0];
                let slots = CrateSlots::build(&program);
                let target = SlotRef::Local(function, slots.fn_local_slots[&function].slot_for_local_depth(p, 0).unwrap());
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let ((model, stats, source, source_key, commits), export) = with_bo_export(|| {
                    let solver = KindSolver::new(&slots);
                    let construction = construct_bo_into(&program, &slots, &origins, &facts, &solver, CopyLendMode::Baseline).expect("production construction");
                    let source = construction.source_events.clone();
                    let keys: Vec<_> = source.retirements.keys().filter(|key| key.function == "f"
                        && key.block == free.block.as_u32() && key.statement == free.statement_index
                        && key.phase == SourcePhase::Call && key.role == SourceRole::Free).cloned().collect();
                    assert_eq!(keys.len(), 1);
                    let initial = solver.model_kinds_relaxing(&construction.selectors).expect("initial production model");
                    assert_eq!(initial.get(&target), Some(&SlotKind::Ref),
                        "fixture must expose a real initial Ref; do not force one to manufacture this witness");
                    if force_ref { solver.assume(target, SlotKind::Ref); }
                    let ((model, stats), commits) = with_plain_commit_trace(|| {
                        if l2 {
                            verify_bo_construction_l2_for_test(&program, &slots, &origins, &solver, &construction, &facts, backend)
                        } else {
                            verify_bo_construction_counting_for_test(&program, &slots, &origins, &solver, &construction, &facts, backend)
                        }
                    });
                    assert!(Arc::ptr_eq(&source, &construction.source_events));
                    if !force_ref {
                        // Establish that the repaired target is constrained
                        // away from Ref, rather than merely losing an objective tie.
                        solver.push_scope();
                        solver.assume(target, SlotKind::Ref);
                        let status = solver.check();
                        solver.pop_scope();
                        assert_eq!(status, z3::SatResult::Unsat, "actual exclusion of the retirement target");
                    }
                    (model, stats, source, keys[0].clone(), commits)
                });
                assert!(stats.commits_conflict > 0, "retirement must trigger a real repair round");
                assert!(stats.source_retirement_decline.is_empty(), "this fixture has complete retirement coverage");
                if !l2 {
                    assert!(commits.iter().any(|commit| commit.target == target
                        && commit.conflict.issuer == Some(target) && commit.conflict.requirers.is_empty()),
                        "Mode-A must commit the exact entry-only retirement target");
                }
                assert!(Arc::ptr_eq(export.source_events.as_ref().expect("source inventory export"), &source));
                assert!(Arc::ptr_eq(export.replay_source_events.as_ref().expect("replay inventory export"), &source));
                assert!(source.retirements.contains_key(&source_key));
                let review = export.source_retirement.as_ref().expect("final retirement review");
                assert!(review.unresolved.is_empty());
                assert_eq!(review.terminal.keys().collect::<std::collections::BTreeSet<_>>(),
                    source.retirements.keys().collect(), "one terminal disposition per original event/outcome");
                assert!(!export.retirement_rounds.is_empty(), "retain the event-to-repair chain across model rounds");
                assert_eq!(export.retirement_rounds.last(), Some(review));
                assert!(export.retirement_rounds[0].conflicts.iter().any(|row|
                    row.source == source_key && row.target == target));
                for round in &export.retirement_rounds {
                    assert_eq!(round.terminal.keys().collect::<std::collections::BTreeSet<_>>(),
                        source.retirements.keys().collect(), "repair never removes the source inventory");
                }
                let covered: Vec<_> = review.coverage.iter().filter(|row| row.source == source_key
                    && row.function == function && row.location == free && row.phase == SourcePhase::Call
                    && row.route.is_empty()).collect();
                assert_eq!(covered.len(), 1);
                assert_eq!(covered[0].disposition, CoverageDisposition::Checked);
                if force_ref {
                    assert!(model.is_none(), "an unrepaired forced Ref must decline");
                    assert_eq!(review.ordinary_error_points, 0, "the decline needs no ordinary loan conflict");
                    assert!(review.conflicts.iter().any(|row| row.target == target && row.source == source_key
                        && row.loan.is_none() && row.entry.is_some_and(|entry| entry.slot == target)),
                        "decline retains the real incoming-entry retirement witness");
                    assert!(export.residual_conflicts.is_none(), "decline must not record an acceptance certificate");
                } else {
                    let model = model.expect("repair must reach an accepted model");
                    assert_ne!(*model.get(&target).expect("accepted model retains the target slot"), SlotKind::Ref);
                    assert!(review.conflicts.is_empty(), "final retirement conflicts must be discharged");
                    if !l2 { assert_eq!(export.residual_conflicts, Some(Vec::new())); }
                }
            }).unwrap_or_else(|error| error.raise());
        }
    }
}

#[test]
fn e5_p_forced_unrepaired_entry_declines_without_an_ordinary_loan_conflict() {
    check_rounds(true);
}

/// R1459-2 (main 315, the user's word "(a)로 하자" on addendum 1407's option (A)): the final
/// retirement review and the last round's are ONE shared handle, not two deep copies of the round's
/// review. RED at `9603759bd`, where both fields own their copy.
#[test]
fn r1459_2_the_final_retirement_review_is_the_last_round_shared() {
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
        let mut functions = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            if let ItemKind::Fn { .. } = item.kind {
                functions.push(item.owner_id.def_id);
            }
        }
        let program = RustProgram {
            tcx,
            functions,
            structs: Vec::new(),
        };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let ((), export) = with_bo_export(|| {
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("production construction");
            let _ = verify_bo_construction_counting_for_test(
                &program,
                &slots,
                &origins,
                &solver,
                &construction,
                &facts,
                TestValidationBackend::HardCheckRoundOptimize,
            );
        });
        let last = export
            .retirement_rounds
            .last()
            .expect("at least one retirement round");
        let final_review = export
            .source_retirement
            .as_ref()
            .expect("final retirement review");
        assert!(
            Arc::ptr_eq(final_review, last),
            "the final review must share the last round's handle"
        );
    })
    .unwrap_or_else(|error| error.raise());
}

/// A cascade whose round-1 replay finds a conflict in both repairs, so the guarded run records a
/// review and re-solves (the shape of `null_paths_tests`' W69 cascade).
const R1468_CASCADE: &str = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
    pub unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";

fn r1468_program<'tcx>(tcx: rustc_middle::ty::TyCtxt<'tcx>) -> RustProgram<'tcx> {
    let mut functions = Vec::new();
    for owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = owner.as_owner() else { continue };
        let OwnerNode::Item(item) = owner.node() else { continue };
        if let ItemKind::Fn { .. } = item.kind {
            functions.push(item.owner_id.def_id);
        }
    }
    RustProgram {
        tcx,
        functions,
        structs: Vec::new(),
    }
}

/// R1468-2 (iii)(a) (the user's word "1로 가자." on addendum 1467's option (1)): when the guarded
/// repair declines and the plain repair restarts at round 0, the guarded run's reviews leave the
/// capture. After the plain repair accepts, the history holds the plain rounds only (one review per
/// validation round, calibrated on a plain-only solve), the final review is its last entry, and the
/// stack-entry acceptance still collects. The decline is forced (`guarded_decline_fault`) at the
/// guarded run's first re-solve after a validation round. RED at `d530d8655`, where the history
/// also holds the guarded run's reviews.
#[test]
fn r1468_2_a_the_plain_restart_holds_only_the_plain_rounds_reviews() {
    use crate::analyses::borrow_ownership::{
        borrow_verify::{RepairMode, guarded_decline_fault},
        construction::verify_bo_construction_counting,
        licensing::stack_export,
    };
    ::utils::compilation::run_compiler_on_str(R1468_CASCADE, |tcx| {
        let program = r1468_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let solve = || {
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("production construction");
            verify_bo_construction_counting(
                &program,
                &slots,
                &origins,
                &solver,
                &construction,
                &facts,
            )
        };
        // The calibration: a plain-only solve records one review per validation round.
        let ((plain_model, plain_stats), plain_export) =
            with_bo_export(|| RepairMode::with_override(RepairMode::Plain, solve));
        assert!(plain_model.is_some(), "the plain repair accepts the fixture");
        assert!(plain_stats.rounds >= 2, "{plain_stats:?}");
        assert_eq!(plain_export.retirement_rounds.len(), plain_stats.rounds);

        let (((model, stats), fired), export) =
            with_bo_export(|| guarded_decline_fault::with_decline(solve));
        let at_decline = fired.expect("the guarded run reaches a re-solve after a validation round");
        assert!(
            at_decline >= 1,
            "the guarded run recorded no review before it declined: the witness would be inert"
        );
        assert!(stats.guarded_fallback.is_some(), "{stats:?}");
        assert!(model.is_some(), "the plain repair accepts after the fallback: {stats:?}");
        assert_eq!(
            export.retirement_rounds.len(),
            stats.rounds,
            "the history holds the guarded run's {at_decline} review(s) besides the plain repair's {} rounds",
            stats.rounds
        );
        let final_review = export
            .source_retirement
            .as_ref()
            .expect("final retirement review");
        assert!(Arc::ptr_eq(
            final_review,
            export.retirement_rounds.last().expect("a plain round")
        ));
        let accepted = stack_export::collect(&export).expect("the stack-entry acceptance collects");
        assert_eq!(accepted.retirement_round + 1, stats.rounds);
    })
    .unwrap_or_else(|error| error.raise());
}

/// R1468-2 (i): the `verify:decline` line's solver detail (`KindSolver::decline_detail`, printed
/// verbatim) names a contradiction's decline as a hard Unsat in the drop loop, with its core's
/// size and the loop's counts (here the plain repair's, which runs after the guarded decline and
/// declines the same way). The line itself goes to stderr under `CRAT_BO_PHASE_LOG=on`,
/// which a test cannot read; the two Unknown arms (drop loop, restoration) have no fixture.
#[test]
fn r1468_2_i_a_contradiction_declines_as_a_hard_unsat_in_the_drop_loop() {
    use crate::analyses::borrow_ownership::{
        construction::verify_bo_construction_counting, slots::SlotId,
    };
    ::utils::compilation::run_compiler_on_str(CODE, |tcx| {
        let program = r1468_program(tcx);
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
        .expect("production construction");
        let victim = slots
            .fn_local_slots
            .iter()
            .find(|(_, universe)| universe.len() > 0)
            .map(|(did, _)| SlotRef::Local(*did, SlotId::from_usize(0)))
            .expect("a local slot");
        solver.assume(victim, SlotKind::Ref);
        solver.add_borrow_exclusion(Some(victim), &[]);
        let (model, _) = verify_bo_construction_counting(
            &program,
            &slots,
            &origins,
            &solver,
            &construction,
            &facts,
        );
        assert!(model.is_none());
        let detail = solver.decline_detail();
        let field = |key: &str| {
            detail
                .split(' ')
                .find_map(|token| token.strip_prefix(key)?.strip_prefix('='))
                .unwrap_or_else(|| panic!("no {key} in {detail}"))
                .to_owned()
        };
        assert_eq!(field("failure"), "hard-unsat", "{detail}");
        assert_eq!(field("phase"), "drop-loop", "{detail}");
        assert_eq!(field("restored"), "0", "{detail}");
        assert!(
            field("core_labels").parse::<usize>().unwrap() >= 2,
            "{detail}"
        );
        let checks: usize = field("hard_checks").parse().unwrap();
        assert_eq!(
            checks,
            field("drops").parse::<usize>().unwrap() + 1,
            "{detail}"
        );
        assert_eq!(field("rechecks"), field("hard_checks"), "{detail}");
    })
    .unwrap_or_else(|error| error.raise());
}

/// R1475-2 (4): beside `R1468_CASCADE` (three solves), a source and a sink in a genuine joint
/// conflict (`nbs2_mixed_tie_drops_sink_retains_source`'s program), so every solve's relaxation
/// drops a selector (the sink) -- the witness covers real retractions.
const R1475_TIE: &str = r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
unsafe extern "C" { fn retain_for_policy_fixture(x: *mut core::ffi::c_void); }
pub unsafe fn pass(x: *mut core::ffi::c_void) { retain_for_policy_fixture(x); }
pub unsafe fn source_side() -> *mut core::ffi::c_void {
    let m = unsafe { malloc(4) };
    unsafe { pass(m) };
    m
}
pub unsafe fn sink_side(a: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let b = a;
    unsafe { pass(b) };
    unsafe { free(a) };
    b
}
"#;

/// R1475-2 (4): one production verification of the compiled fixture in `mode`, with the fresh-hard-solver
/// switch read as `fresh` (through the test hook): the model by name (`function#slot=kind`, sorted),
/// each solve's dropped selectors, the hard-solver events, and the rounds.
struct R1475Run {
    model: Option<Vec<String>>,
    dropped: Vec<Vec<usize>>,
    trace: crate::analyses::borrow_ownership::solver::SelectorTrace,
    events: Vec<crate::analyses::borrow_ownership::solver::hard_solver_trace::Event>,
    rounds: usize,
}

fn r1475_run(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    mode: crate::analyses::borrow_ownership::borrow_verify::RepairMode,
    fresh: bool,
) -> R1475Run {
    use crate::analyses::borrow_ownership::{
        borrow_verify::RepairMode,
        construction::verify_bo_construction_counting,
        execution_guard::fresh_hard_solver_hook,
        solver::{hard_solver_trace, with_selector_trace},
    };
    let program = r1468_program(tcx);
    let slots = CrateSlots::build(&program);
    let origins = compute_origins(&program);
    let facts = MutFacts::from_program(&program);
    let ((((model, stats), trace), events), _export) = with_bo_export(|| {
        hard_solver_trace::with(|| {
            with_selector_trace(|| {
                fresh_hard_solver_hook::with(fresh, || {
                    RepairMode::with_override(mode, || {
                        let solver = KindSolver::new(&slots);
                        let construction = construct_bo_into(
                            &program,
                            &slots,
                            &origins,
                            &facts,
                            &solver,
                            CopyLendMode::Baseline,
                        )
                        .expect("production construction");
                        verify_bo_construction_counting(
                            &program,
                            &slots,
                            &origins,
                            &solver,
                            &construction,
                            &facts,
                        )
                    })
                })
            })
        })
    });
    let model = model.map(|model| {
        let mut rows: Vec<String> = model
            .iter()
            .map(|(slot, kind)| match slot {
                SlotRef::Local(function, id) => format!(
                    "{}#{}={kind:?}",
                    tcx.item_name(function.to_def_id()),
                    id.as_usize()
                ),
                SlotRef::Field(id) => format!("field#{}={kind:?}", id.as_usize()),
            })
            .collect();
        rows.sort();
        rows
    });
    let dropped = trace
        .epochs
        .iter()
        .map(|epoch| epoch.final_dropped.clone())
        .collect();
    R1475Run {
        model,
        dropped,
        trace,
        events,
        rounds: stats.rounds,
    }
}

/// R1475-2 (4), the witness (the user's word in the seat's session 11-07, "1번으로 하자.", on
/// addendum 1474's option (1)): with the switch on, every solve of the repair (plain and guarded)
/// runs on a hard solver built right before it, from the Optimize's assertions as they stand at that
/// solve's start -- one build per solve, the solve's synchronization appending nothing -- and the
/// later solves' builds copy the assertions the repair committed since; every solve retracts a
/// selector, and on this fixture the decisions, cores and model equal the switch-off run's. RED at
/// `ad45d2c71`, where one hard solver serves the repair and each later solve synchronizes it.
#[test]
fn r1475_2_switch_on_builds_one_hard_solver_per_solve_from_the_optimizes_assertions() {
    use crate::analyses::borrow_ownership::{
        borrow_verify::RepairMode, solver::hard_solver_trace::Event,
    };
    let code = format!("{R1468_CASCADE}\n{R1475_TIE}");
    ::utils::compilation::run_compiler_on_str(&code, |tcx| {
        for mode in [RepairMode::Plain, RepairMode::Guarded] {
            let on = r1475_run(tcx, mode, true);
            let off = r1475_run(tcx, mode, false);
            println!(
                "R1475_2 {mode:?} on: model={:?} dropped={:?} rounds={} | off: model={:?} dropped={:?} rounds={}",
                on.model, on.dropped, on.rounds, off.model, off.dropped, off.rounds
            );
            let solves: Vec<(usize, usize)> = on
                .events
                .iter()
                .filter_map(|event| match *event {
                    Event::Solve { optimize, hard } => Some((optimize, hard)),
                    Event::Build { .. } => None,
                })
                .collect();
            assert!(solves.len() >= 2, "{mode:?}: {:?}", on.events);
            assert_eq!(
                on.events.len(),
                2 * solves.len(),
                "{mode:?}: one build per solve: {:?}",
                on.events
            );
            for pair in on.events.chunks(2) {
                let [Event::Build { optimize: built }, Event::Solve { optimize, hard }] = *pair else {
                    panic!("{mode:?}: a solve not entered right after its own build: {:?}", on.events);
                };
                assert_eq!(
                    (built, hard),
                    (optimize, optimize),
                    "{mode:?}: the solve's solver holds the Optimize's assertions at its start: {:?}",
                    on.events
                );
            }
            assert!(
                solves.last().unwrap().0 > solves[0].0,
                "{mode:?}: a later solve's build copies the repair's commits: {:?}",
                on.events
            );
            assert!(on.model.is_some(), "{mode:?}: the fixture accepts");
            assert!(
                on.dropped.len() == solves.len() && on.dropped.iter().all(|dropped| !dropped.is_empty()),
                "{mode:?}: every solve retracts a selector: {:?}",
                on.dropped
            );
            // Here the switch changes no question: the same drop / restore decisions with the same
            // cores, and the same model. z3 lists a core in its own order, which differs here
            // between the two solvers ([1, 0] beside [0, 1]); the drop picks by sort key, so the
            // order is normalized before the comparison. On a large input a new solver may return
            // another valid core and the path may diverge (allowed, 321 §6 (4)).
            let normalized = |trace: &crate::analyses::borrow_ownership::solver::SelectorTrace| {
                let mut trace = trace.clone();
                for epoch in &mut trace.epochs {
                    for event in &mut epoch.events {
                        event.core_selectors.sort_unstable();
                    }
                }
                trace
            };
            assert_eq!(normalized(&on.trace), normalized(&off.trace), "{mode:?}");
            assert_eq!(on.model, off.model, "{mode:?}");
        }
    })
    .unwrap_or_else(|error| error.raise());
}

/// R1475-2 (4), the control: with the switch off, one hard solver per repair, synchronized at each
/// later solve (it appends the repair's commits), and the fixture's model and dropped selectors
/// pinned.
#[test]
fn r1475_2_switch_off_builds_one_hard_solver_per_repair_and_keeps_the_model() {
    use crate::analyses::borrow_ownership::{
        borrow_verify::RepairMode, solver::hard_solver_trace::Event,
    };
    let code = format!("{R1468_CASCADE}\n{R1475_TIE}");
    ::utils::compilation::run_compiler_on_str(&code, |tcx| {
        for mode in [RepairMode::Plain, RepairMode::Guarded] {
            let off = r1475_run(tcx, mode, false);
            let builds = off
                .events
                .iter()
                .filter(|event| matches!(event, Event::Build { .. }))
                .count();
            let solves: Vec<(usize, usize)> = off
                .events
                .iter()
                .filter_map(|event| match *event {
                    Event::Solve { optimize, hard } => Some((optimize, hard)),
                    Event::Build { .. } => None,
                })
                .collect();
            assert_eq!(
                builds, 1,
                "{mode:?}: one build per repair: {:?}",
                off.events
            );
            assert!(solves.len() >= 2, "{mode:?}: {:?}", off.events);
            assert!(
                solves.iter().any(|(optimize, hard)| hard < optimize),
                "{mode:?}: a later solve synchronizes the repair's commits: {:?}",
                off.events
            );
            // As printed with the switch off: f's `b` slot is `Ref` under the guarded repair only,
            // the tie's slots `Owning`, and each of the three solves drops the sink (selector 1).
            let ref_f1 = if mode == RepairMode::Guarded {
                "Ref"
            } else {
                "Raw"
            };
            let expected: Vec<String> = [
                "f#0=Raw".to_owned(),
                format!("f#1={ref_f1}"),
                "f#2=Raw".to_owned(),
                "f#3=Raw".to_owned(),
                "id#0=Ref".to_owned(),
                "id#1=Ref".to_owned(),
                "pass#0=Owning".to_owned(),
                "pass#1=Owning".to_owned(),
                "sink_side#0=Owning".to_owned(),
                "sink_side#1=Owning".to_owned(),
                "sink_side#2=Owning".to_owned(),
                "sink_side#3=Owning".to_owned(),
                "sink_side#4=Owning".to_owned(),
                "source_side#0=Owning".to_owned(),
                "source_side#1=Owning".to_owned(),
                "source_side#2=Owning".to_owned(),
            ]
            .into();
            assert_eq!(off.model, Some(expected), "{mode:?}");
            assert_eq!(off.dropped, vec![vec![1usize]; 3], "{mode:?}");
            assert_eq!(off.rounds, 3, "{mode:?}");
        }
    })
    .unwrap_or_else(|error| error.raise());
}

/// R1475-2 (I1) (I3) and (4)'s build lines, read where they are written: stderr under
/// `CRAT_BO_PHASE_LOG=on`, in a child process running this test alone. Part 1, the plain repair on
/// the contradiction of `r1468_2_i`: exactly one `verify:decline end` line, the plain repair's
/// (`repair=plain`, from `decline_detail`: a hard Unsat in the drop loop); one `z3:query stats`
/// line per scoped hard check, `n` = 1, 2, ... in order, as many as the decline counts, each with
/// the push / check / pop walls and the eight counters; and round 0's `verify:solve end` summary
/// times `hard-push` and `hard-pop` once per check. Part 2, the plain repair on `R1468_CASCADE`
/// with the switch on: one `verify:hard_solver end` line per solve (`round=0`, `1`, `2`), a
/// `start` and a `drop` line before each later build. `ad45d2c71` writes none of these lines (the
/// test was not run there: it needs this change's hook).
#[test]
fn r1475_2_the_phase_log_lines_of_i1_i3_and_the_builds() {
    use crate::analyses::borrow_ownership::{
        borrow_verify::RepairMode, construction::verify_bo_construction_counting,
        execution_guard::fresh_hard_solver_hook, slots::SlotId,
    };
    const CHILD: &str = "CRAT_R1475_2_CHILD";
    if std::env::var_os(CHILD).is_some() {
        assert!(crate::phase_log::on(), "the child runs with the log on");
        let verify = |code: &str, contradiction: bool, fresh: bool| {
            ::utils::compilation::run_compiler_on_str(code, |tcx| {
                let program = r1468_program(tcx);
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
                .expect("production construction");
                if contradiction {
                    let victim = slots
                        .fn_local_slots
                        .iter()
                        .find(|(_, universe)| universe.len() > 0)
                        .map(|(did, _)| SlotRef::Local(*did, SlotId::from_usize(0)))
                        .expect("a local slot");
                    solver.assume(victim, SlotKind::Ref);
                    solver.add_borrow_exclusion(Some(victim), &[]);
                }
                let (model, _) = fresh_hard_solver_hook::with(fresh, || {
                    RepairMode::with_override(RepairMode::Plain, || {
                        crate::phase_log::with_sub_marks(|| {
                            verify_bo_construction_counting(
                                &program,
                                &slots,
                                &origins,
                                &solver,
                                &construction,
                                &facts,
                            )
                        })
                    })
                });
                assert_eq!(model.is_none(), contradiction);
            })
            .unwrap_or_else(|error| error.raise());
        };
        eprintln!("R1475_2_PART 1");
        verify(CODE, true, false);
        eprintln!("R1475_2_PART 2");
        verify(R1468_CASCADE, false, true);
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().expect("current_exe"))
        .args([
            "analyses::borrow_ownership::retirement::tests_rounds::r1475_2_the_phase_log_lines_of_i1_i3_and_the_builds",
            "--exact",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(CHILD, "1")
        .env("CRAT_BO_PHASE_LOG", "on")
        .output()
        .expect("child test");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "child failed:\n{}\n{stderr}",
        String::from_utf8_lossy(&output.stdout)
    );
    let (part1, part2) = stderr
        .split_once("R1475_2_PART 2")
        .unwrap_or_else(|| panic!("no part 2:\n{stderr}"));
    let part1 = part1
        .split_once("R1475_2_PART 1")
        .unwrap_or_else(|| panic!("no part 1:\n{stderr}"))
        .1;
    let lines = |text: &'static str, part: &str| -> Vec<String> {
        part.lines()
            .filter(|line| line.starts_with(&format!("[bo-phase] {text} ")))
            .map(str::to_owned)
            .collect()
    };
    let field = |line: &str, key: &str| -> String {
        line.split(' ')
            .find_map(|token| token.strip_prefix(key)?.strip_prefix('='))
            .unwrap_or_else(|| panic!("no {key} in {line}"))
            .to_owned()
    };
    // (I3)
    let declines = lines("verify:decline end", part1);
    assert_eq!(declines.len(), 1, "{declines:?}");
    let decline = &declines[0];
    assert!(
        decline.contains(" repair=plain round=0 failure=hard-unsat "),
        "{decline}"
    );
    assert_eq!(field(decline, "phase"), "drop-loop", "{decline}");
    let checks: usize = field(decline, "hard_checks").parse().unwrap();
    // (I1)
    let stats = lines("z3:query stats", part1);
    assert_eq!(stats.len(), checks, "{stats:?}\n{decline}");
    for (index, line) in stats.iter().enumerate() {
        assert_eq!(field(line, "stage"), "hard-check", "{line}");
        assert_eq!(field(line, "n"), (index + 1).to_string(), "{line}");
        assert_eq!(field(line, "result"), "Unsat", "{line}");
        for key in ["push", "check", "pop"] {
            let wall = field(line, key);
            assert!(
                wall.ends_with('s') && wall.trim_end_matches('s').parse::<f64>().is_ok(),
                "{line}"
            );
        }
        for key in ["conflicts", "decisions", "propagations", "restarts"] {
            let own: u64 = field(line, key).parse().unwrap();
            let life: u64 = field(line, &format!("life_{key}")).parse().unwrap();
            assert!(own <= life, "{line}");
        }
    }
    let solve_end = lines("verify:solve end", part1);
    assert_eq!(solve_end.len(), 1, "{solve_end:?}");
    for stage in ["hard-check", "hard-push", "hard-pop"] {
        assert!(
            solve_end[0].contains(&format!("{stage}={checks}/")),
            "{stage}: {}",
            solve_end[0]
        );
    }
    // (4)'s build lines
    let builds = lines("verify:hard_solver end", part2);
    let rounds: Vec<String> = builds.iter().map(|line| field(line, "round")).collect();
    assert_eq!(rounds, ["0", "1", "2"], "{builds:?}");
    assert_eq!(lines("verify:hard_solver start", part2).len(), 2);
    let drops = lines("verify:hard_solver drop", part2);
    assert_eq!(drops.len(), 2, "{drops:?}");
    assert!(
        drops.iter().all(|line| line.contains(" uordblks=")),
        "{drops:?}"
    );
    assert!(
        lines("verify:hard_solver end", part1)
            .iter()
            .all(|line| !line.contains("round="))
    );
}
