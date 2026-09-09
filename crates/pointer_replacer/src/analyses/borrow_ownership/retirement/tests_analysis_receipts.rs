//! Actual analysis receipts preceding individual harness expectation migrations.
//! No fixture expectation outside this file is changed. Decline is recorded as
//! decline, never as an accepted non-Owning or successful escape-repair verdict.

use std::collections::BTreeSet;

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::VarDebugInfoContents;

use super::{RetirementReview, UnresolvedReason};
use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        a5_overlap::WholeProgramAttestation,
        borrow_verify::with_mode_a_commit_trace,
        construction::{
            CopyLendMode, TestValidationBackend, construct_bo_into,
            solve_bo_a5_reference_reporting, verify_bo_construction_counting_for_test,
        },
        crate_slots::CrateSlots,
        esc_minimal::with_fixture_selection,
        export::{LoanClass, with_bo_export},
        mutability_facts::MutFacts,
        origins::compute_origins,
        slot_key,
        slots::SlotOwner,
        solver::{KindSolver, SlotRef},
        source_events::{SourceEvents, SourceRole},
    },
    utils::rustc::RustProgram,
};

const ESC: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; *x = 1; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

const OUTPARAM: &str = r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub unsafe fn make(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}
pub unsafe fn caller() -> *mut core::ffi::c_void {
    let mut local: *mut core::ffi::c_void = core::ptr::null_mut();
    let p = &mut local as *mut *mut core::ffi::c_void;
    let q = &mut local as *mut *mut core::ffi::c_void;
    make(p);
    *q = local;
    local
}
"#;

const DELETE_NODE: &str = include_str!("../testdata/l2_feature_off_sink_drop.rs");
const SOURCE_DROP: &str = include_str!("../testdata/l2_feature_off_source_drop.rs");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Case {
    EscSelected,
    A5Reference,
    Outparam,
    DeleteNode,
    SourceDrop,
}

fn slot_identity(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    reference: SlotRef,
) -> (String, u8) {
    match reference {
        SlotRef::Local(function, id) => {
            let slot = slots.fn_local_slots[&function].slot(id);
            let SlotOwner::Local(local) = slot.owner else { panic!("local slot owner") };
            (
                slot_key::local_key(program.tcx, function, local.as_usize(), slot.depth),
                slot.depth,
            )
        }
        SlotRef::Field(id) => {
            let slot = slots.field_slots.slot(id);
            let SlotOwner::Field(field) = slot.owner else { panic!("field slot owner") };
            (
                slot_key::field_key(program.tcx, field.struct_did, field.field_index, slot.depth),
                slot.depth,
            )
        }
    }
}

fn check_inner_decline(
    case: Case,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    source: &SourceEvents,
    review: &RetirementReview,
) {
    assert!(
        !review.unresolved.is_empty(),
        "{case:?}: decline requires typed retirement evidence"
    );
    for row in &review.unresolved {
        let UnresolvedReason::MissingInnerLoan { slot, depth } = row.reason else {
            panic!(
                "{case:?}: unrelated unresolved reason must not become an expectation migration: {row:?}"
            );
        };
        let (identity, actual_depth) = slot_identity(program, slots, slot);
        assert_eq!(depth, 1);
        assert_eq!(
            actual_depth, depth,
            "reason depth must match the actual slot"
        );
        let SlotRef::Local(function, _) = slot else {
            panic!("fixture residual is a local inner slot")
        };
        assert_eq!(
            program.tcx.item_name(function.to_def_id()).as_str(),
            "caller"
        );
        let event = row
            .source
            .as_ref()
            .expect("inner residual names its actual source event");
        assert!(source.retirements.contains_key(event));
        assert!(matches!(
            event.role,
            SourceRole::StorageDead | SourceRole::ReturnStorage | SourceRole::UnwindStorage
        ));
        assert!(row.location.is_some() && row.phase.is_some());
        println!(
            "receipt.case={case:?} status=declined reason=MissingInnerLoan slot={identity} depth={depth} source={event:?} frame_location={:?} frame_phase={:?} route={:?}",
            row.location, row.phase, row.route
        );
    }
}

fn receipt(code: &str, case: Case, backend: TestValidationBackend) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
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
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = if case == Case::Outparam { MutFacts::all_mut() } else { MutFacts::from_program(&program) };
        let (model, stats, export, commits) = if case == Case::A5Reference {
            let ((result, commits), export) = with_bo_export(|| {
                with_mode_a_commit_trace(|| with_fixture_selection(|| {
                    solve_bo_a5_reference_reporting(&program, &slots, &origins, &facts,
                        Some(WholeProgramAttestation::FrozenBenchmarkGraph))
                }))
            });
            let verified = result.expect("R245 local recovery retains the A5 reference model");
            println!("receipt.case=A5Reference status=accepted");
            assert!(export.loans.iter().all(|loan| loan.class != LoanClass::CopyLend),
                "the reference path must still exclude fixture-selected escaped CopyLends");
            (Some(verified.model), None, export, commits)
        } else {
            let (((model, stats), commits), export) = with_bo_export(|| {
                let solve = || {
                    let solver = KindSolver::new(&slots);
                    let construction = construct_bo_into(&program, &slots, &origins, &facts,
                        &solver, CopyLendMode::Baseline).expect("production analysis construction");
                    if case == Case::EscSelected {
                        assert_eq!(construction.esc_minimal.cross_stage_counts(), (1, 1, 1, 1));
                    }
                    with_mode_a_commit_trace(|| verify_bo_construction_counting_for_test(
                        &program, &slots, &origins, &solver, &construction, &facts, backend))
                };
                if case == Case::EscSelected { with_fixture_selection(solve) } else { solve() }
            });
            println!("receipt.case={case:?} status={} stats={stats:?}", if model.is_some() { "accepted" } else { "declined" });
            (model, Some(stats), export, commits)
        };
        let source = export.source_events.as_ref().expect("actual construction source inventory");
        let review = export.source_retirement.as_ref().expect("actual terminal retirement review");
        assert!(!export.retirement_rounds.is_empty(), "the receipt must include actual replay rounds");
        assert_eq!(export.retirement_rounds.last(), Some(review));
        let source_keys = source.retirements.keys().collect::<BTreeSet<_>>();
        for (index, round) in export.retirement_rounds.iter().enumerate() {
            assert_eq!(round.terminal.keys().collect::<BTreeSet<_>>(), source_keys,
                "source events remain present through every repair/decline round");
            for row in &round.conflicts {
                let (target, _) = slot_identity(&program, &slots, row.target);
                assert_eq!(row.target_key, target);
                assert!(source.retirements.contains_key(&row.source));
                println!("receipt.case={case:?} round={index} source={:?} target={target} location={:?} phase={:?} route={:?} loan={:?} entry={:?}",
                    row.source, row.location, row.phase, row.route, row.loan, row.entry);
            }
        }
        for commit in &commits {
            let (target, _) = slot_identity(&program, &slots, commit.target);
            println!("receipt.case={case:?} committed_target={target} conflict={:?}", commit.conflict);
        }
        match case {
            Case::EscSelected | Case::A5Reference => {
                let model = model.as_ref().expect("R245 coverage decline is removed");
                assert!(review.unresolved.is_empty());
                let rows = export.retirement_rounds.iter().flat_map(|round| &round.demotions).collect::<Vec<_>>();
                assert!(!rows.is_empty(), "acceptance must retain the actual local repair receipts");
                for row in rows {
                    let super::local_outcome::Reason::InnerLoanMissing { depth } = row.reason else {
                        panic!("unrelated recovery is not an expectation migration: {row:?}");
                    };
                    let (identity, actual_depth) = slot_identity(&program, &slots, row.holder);
                    assert_eq!((depth, actual_depth), (1, 1));
                    assert_eq!(program.tcx.item_name(row.function.to_def_id()).as_str(), "caller");
                    assert!(source.retirements.contains_key(&row.source));
                    assert!(matches!(row.source.role, SourceRole::StorageDead | SourceRole::ReturnStorage | SourceRole::UnwindStorage));
                    assert!(row.chain.contains(&row.holder));
                    for target in &row.chain { assert_eq!(model[target], SlotKind::Raw); }
                    println!("receipt.case={case:?} status=accepted receipt={} holder={identity} source={:?} chain={:?}", row.reason.label(), row.source, row.chain);
                }
                if case == Case::EscSelected {
                    let save = *program.functions.iter().find(|function| tcx.item_name(function.to_def_id()).as_str()=="save").unwrap();
                    let body=tcx.mir_drops_elaborated_and_const_checked(save).borrow();
                    let x=body.var_debug_info.iter().find_map(|info| {
                        if info.name.as_str()!="x" { return None; }
                        let VarDebugInfoContents::Place(place)=info.value else { return None; };
                        place.as_local()
                    }).unwrap();
                    let target=SlotRef::Local(save,slots.fn_local_slots[&save].slot_for_local_depth(x,0).unwrap());
                    assert_eq!(model[&target],SlotKind::Raw);
                    assert!(commits.iter().any(|commit| commit.target==target && commit.conflict.esc_issuer_first));
                }
                if let Some(stats) = &stats { assert!(stats.source_retirement_decline.is_empty()); }
            }
            Case::Outparam => {
                if model.is_none() {
                    check_inner_decline(case, &program, &slots, source, review);
                }
                let caller = *program.functions.iter().find(|function|
                    tcx.item_name(function.to_def_id()).as_str() == "caller").unwrap();
                let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
                for name in ["p", "q"] {
                    let local = body.var_debug_info.iter().find_map(|info| {
                        if info.name.as_str() != name { return None; }
                        let VarDebugInfoContents::Place(place) = info.value else { return None };
                        place.as_local()
                    }).expect("actual source stack-pointer alias");
                    let target = SlotRef::Local(caller, slots.fn_local_slots[&caller].slot_for_local_depth(local, 0).unwrap());
                    let (identity, _) = slot_identity(&program, &slots, target);
                    match &model {
                        Some(model) => {
                            let kind = model.get(&target).expect("accepted stack-pointer slot");
                            assert_ne!(*kind, SlotKind::Owning, "an accepted model must not own stack pointer {name}");
                            println!("receipt.case=Outparam status=accepted outer={identity} kind={kind:?} nonowning_check=passed");
                        }
                        None => println!("receipt.case=Outparam status=declined outer={identity} kind=not-produced nonowning_check=not-an-accepted-verdict"),
                    }
                }
            }
            Case::DeleteNode | Case::SourceDrop => {
                let model = model.as_ref().expect("snapshot fixture retains an accepted model");
                let stats = stats.as_ref().unwrap();
                assert!(stats.source_retirement_decline.is_empty());
                assert!(review.unresolved.is_empty());
                assert!(export.retirement_rounds.iter().any(|round| !round.conflicts.is_empty()),
                    "changed snapshot needs a concrete retirement-to-target chain");
                assert_eq!(stats.rounds, 2);
                if case == Case::DeleteNode {
                    assert_eq!((stats.dropped_sources, stats.dropped_sinks), (0, 2));
                } else {
                    assert_eq!((stats.dropped_sources, stats.dropped_sinks), (1, 0));
                }
                let mut rows = model.iter().map(|(&slot, &kind)|
                    (slot_identity(&program, &slots, slot).0, kind)).collect::<Vec<_>>();
                rows.sort_by(|left, right| left.0.cmp(&right.0));
                for (slot, kind) in rows { println!("receipt.case={case:?} model.{slot}={kind:?}"); }
            }
        }
    }).unwrap_or_else(|error| error.raise());
}

#[test]
fn e5_d_receipt_escw1_declines_on_exact_inner_coverage_before_migration() {
    for backend in [
        TestValidationBackend::HardCheckRoundOptimize,
        TestValidationBackend::LegacyOptimize,
    ] {
        receipt(ESC, Case::EscSelected, backend);
    }
}

#[test]
fn e5_d_receipt_a5_reference_declines_without_consuming_esc_selection() {
    receipt(
        ESC,
        Case::A5Reference,
        TestValidationBackend::HardCheckRoundOptimize,
    );
}

#[test]
fn e5_d_receipt_outparam_keeps_stack_nonowning_obligation_separate_from_decline() {
    receipt(
        OUTPARAM,
        Case::Outparam,
        TestValidationBackend::HardCheckRoundOptimize,
    );
}

#[test]
fn e5_d_receipt_delete_node_snapshot_has_actual_retirement_target_chains() {
    receipt(
        DELETE_NODE,
        Case::DeleteNode,
        TestValidationBackend::HardCheckRoundOptimize,
    );
}

#[test]
fn e5_d_receipt_source_drop_snapshot_has_actual_storage_retirement_target_chains() {
    receipt(
        SOURCE_DROP,
        Case::SourceDrop,
        TestValidationBackend::HardCheckRoundOptimize,
    );
}
