//! Production fixpoint controls for loanless source-retirement obligations.

use std::sync::Arc;

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Location, VarDebugInfoContents};

use super::CoverageDisposition;
use crate::{
    analyses::{
        borrow_ownership::{
            SlotKind,
            borrow_verify::with_mode_a_commit_trace,
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

fn check_rounds(force_ref: bool) {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn f(p: *const u8, alias: *mut u8) -> u8 {
    let v = *p;
    free(alias);
    v
}
"#;
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
                    let ((model, stats), commits) = with_mode_a_commit_trace(|| {
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
fn e5_p_retirement_fixpoints_demote_the_actual_entry_and_keep_source_coverage() {
    check_rounds(false);
}

#[test]
fn e5_p_forced_unrepaired_entry_declines_without_an_ordinary_loan_conflict() {
    check_rounds(true);
}
