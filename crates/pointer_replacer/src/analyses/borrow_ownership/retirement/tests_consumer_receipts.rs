//! Analysis-side receipts for four unchanged consumer fixtures. No rewriter is
//! invoked here, and no changed consumer expectation is approved by this file.

use std::{collections::BTreeSet, sync::Arc};

use rustc_hash::FxHashMap;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::{Local, Location, Operand, Rvalue, StatementKind, VarDebugInfoContents},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use super::UnresolvedReason;
use crate::{
    analyses::{
        borrow_ownership::{
            SlotKind,
            borrow_verify::RoundStats,
            construction::{
                CopyLendMode, TestValidationBackend, construct_bo_into,
                verify_bo_construction_counting_for_test,
            },
            crate_slots::CrateSlots,
            export::{self, BoExport},
            mutability_facts::MutFacts,
            origins::compute_origins,
            slot_key,
            slots::SlotOwner,
            solver::{KindSolver, SlotRef},
            source_events::{SourceEvents, SourceObject, SourcePhase, SourceRegion, SourceRole},
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

const BOX_N5: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn memset(ptr: *mut core::ffi::c_void, value: i32, bytes: usize) -> *mut core::ffi::c_void;
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
pub unsafe fn f() {
    let p: *mut *mut i32 = malloc(core::mem::size_of::<*mut i32>()) as *mut *mut i32;
    free(p as *mut core::ffi::c_void);
}
"#;

const NPO_THIN: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe extern "C" {
    fn set_const(out: *mut *const i32, clear: bool);
    fn set_mut(out: *mut *mut i32, clear: bool);
}
pub unsafe fn caller() {
    let value = 7;
    let mut mutable_value = 9;
    let mut shared_slot: *const i32 = &value;
    let mut mut_slot: *mut i32 = &mut mutable_value;
    set_const(&mut shared_slot, false);
    set_mut(&mut mut_slot, false);
    set_const(&mut shared_slot, true);
    set_mut(&mut mut_slot, true);
}
"#;

const NPO_HELD: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
unsafe extern "C" {
    fn set_fat(out: *mut *const [i32]);
    fn set_thin(out: *mut *const i32);
}
pub struct Holder { slot: *const i32 }
pub unsafe fn caller(slice: &[i32], p: *const i32) {
    let mut fat_slot: *const [i32] = slice as *const [i32];
    let mut holder = Holder { slot: p };
    set_fat(&mut fat_slot);
    set_thin(&mut holder.slot);
}
"#;

const FREED: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
extern "C" { fn free(p: *mut core::ffi::c_void); }
pub unsafe fn releases(a: *mut i32, b: i32) -> i32 {
    let p: *mut i32 = a;
    let dead = p.read();
    if b > 0 { free(p as *mut core::ffi::c_void); }
    dead
}
"#;

fn program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
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
    RustProgram {
        tcx,
        functions,
        structs,
    }
}

fn function(program: &RustProgram<'_>, name: &str) -> LocalDefId {
    let matching: Vec<_> = program
        .functions
        .iter()
        .copied()
        .filter(|function| program.tcx.item_name(function.to_def_id()).as_str() == name)
        .collect();
    assert_eq!(matching.len(), 1);
    matching[0]
}

struct Capture {
    model: Option<FxHashMap<SlotRef, SlotKind>>,
    stats: RoundStats,
    source: Arc<SourceEvents>,
    export: BoExport,
}

fn capture(program: &RustProgram<'_>, slots: &CrateSlots) -> Capture {
    let origins = compute_origins(program);
    let facts = MutFacts::from_program(program);
    let ((model, stats, source), export) = export::with_bo_export(|| {
        let solver = KindSolver::new(slots);
        let construction = construct_bo_into(
            program,
            slots,
            &origins,
            &facts,
            &solver,
            CopyLendMode::Baseline,
        )
        .expect("exact consumer fixture must construct before the retirement review");
        let (model, stats) = verify_bo_construction_counting_for_test(
            program,
            slots,
            &origins,
            &solver,
            &construction,
            &facts,
            TestValidationBackend::HardCheckRoundOptimize,
        );
        (model, stats, construction.source_events.clone())
    });
    assert!(Arc::ptr_eq(
        export
            .source_events
            .as_ref()
            .expect("construction inventory"),
        &source
    ));
    assert!(Arc::ptr_eq(
        export
            .replay_source_events
            .as_ref()
            .expect("replay inventory"),
        &source
    ));
    Capture {
        model,
        stats,
        source,
        export,
    }
}

fn check_decline(label: &str, source: &str, name: &str, storage_only: bool) {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let program = program(tcx);
        let function = function(&program, name);
        let slots = CrateSlots::build(&program);
        let captured = capture(&program, &slots);
        assert!(
            captured.model.is_none(),
            "bank the actual current decline for {label}"
        );
        assert!(
            !captured.stats.source_retirement_decline.is_empty(),
            "decline needs typed source evidence"
        );
        let final_review = captured
            .export
            .source_retirement
            .as_ref()
            .expect("final review");
        assert_eq!(
            captured.stats.source_retirement_decline,
            final_review.unresolved
        );
        if storage_only {
            assert!(
                captured
                    .source
                    .retirements
                    .keys()
                    .all(|key| !matches!(key.role, SourceRole::Free | SourceRole::ReallocOld)),
                "ForeignC set_* is not a retirement primitive"
            );
        }
        for row in &captured.stats.source_retirement_decline {
            let UnresolvedReason::MissingInnerLoan { slot, depth } = &row.reason else {
                panic!("{label}: a different typed cause needs separate attribution: {row:?}");
            };
            assert_eq!(*depth, 1, "actual depth-one coverage residual");
            let SlotRef::Local(owner, id) = *slot else {
                panic!("unexpected nonlocal inner slot: {row:?}")
            };
            assert_eq!(owner, function);
            let actual = slots.fn_local_slots[&owner].slot(id);
            assert_eq!(actual.depth, *depth);
            let SlotOwner::Local(local) = actual.owner else { panic!("local slot owner") };
            assert_eq!(
                slots.fn_local_slots[&owner].slot_for_local_depth(local, *depth),
                Some(id)
            );
            let key = row.source.as_ref().expect("original source event identity");
            let event = captured
                .source
                .retirements
                .get(key)
                .expect("no fabricated retirement row");
            assert_eq!(row.function, Some(function));
            assert_eq!(
                row.location,
                Some(Location {
                    block: rustc_middle::mir::BasicBlock::from_u32(key.block),
                    statement_index: key.statement
                })
            );
            assert_eq!(row.phase, Some(key.phase));
            assert!(
                row.route.is_empty(),
                "these exact fixtures have no local call routing"
            );
            if storage_only {
                assert!(matches!(
                    key.role,
                    SourceRole::StorageDead | SourceRole::ReturnStorage | SourceRole::UnwindStorage
                ));
                assert_eq!(event.region, SourceRegion::WholeStorage);
                assert!(matches!(
                    event.object,
                    SourceObject::Storage(_) | SourceObject::PointerStorage(_)
                ));
            } else {
                assert_eq!(
                    key.role,
                    SourceRole::Free,
                    "BOX-N5's actual retirement is its C free"
                );
                assert!(matches!(event.object, SourceObject::HeapThrough(_)));
            }
            let target_key = slot_key::local_key(tcx, function, local.as_usize(), *depth);
            eprintln!(
                "[D-CONSUMER] fixture={label} target={target_key} event={key:?} reason={:?}",
                row.reason
            );
        }
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn e5_p_d_consumer_box_n5_has_an_exact_inner_free_decline_receipt() {
    check_decline(
        "box_n5_depth_two_local_stays_out_of_wave1",
        BOX_N5,
        "f",
        false,
    );
}

#[test]
fn e5_p_d_consumer_npo_thin_has_only_source_storage_decline_receipts() {
    check_decline(
        "br_w5b_thin_const_and_mut_depth2_storage_use_npo_bridge",
        NPO_THIN,
        "caller",
        true,
    );
}

#[test]
fn e5_p_d_consumer_npo_held_has_only_source_storage_decline_receipts() {
    check_decline(
        "br_w5b_fat_and_non_variable_depth2_storage_are_typed_holds",
        NPO_HELD,
        "caller",
        true,
    );
}

#[test]
fn e5_p_d_consumer_freed_column_keeps_the_entry_repair_and_copy_chain() {
    ::utils::compilation::run_compiler_on_str(FREED, |tcx| {
        let program = program(tcx);
        let function = function(&program, "releases");
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let named = |name: &str| {
            let locals: BTreeSet<Local> = body
                .var_debug_info
                .iter()
                .filter_map(|info| {
                    if info.name.as_str() != name {
                        return None;
                    }
                    let VarDebugInfoContents::Place(place) = info.value else { return None };
                    place.as_local()
                })
                .collect();
            assert_eq!(locals.len(), 1, "actual source binding {name}");
            *locals.iter().next().unwrap()
        };
        let a = named("a");
        let p = named("p");
        assert!(a.as_usize() > 0 && a.as_usize() <= body.arg_count);
        assert!(p.as_usize() > body.arg_count);
        assert!(
            body.basic_blocks
                .iter()
                .flat_map(|data| &data.statements)
                .any(
                    |statement| matches!(&statement.kind, StatementKind::Assign(box (destination,
                Rvalue::Use(Operand::Copy(source) | Operand::Move(source))))
                if destination.as_local() == Some(p) && source.as_local() == Some(a))
                ),
            "the original MIR must establish the actual a→p value copy"
        );
        let frees: Vec<_> = body
            .basic_blocks
            .iter_enumerated()
            .filter_map(|(block, data)| {
                let call = data.terminator().as_call(tcx)?;
                matches!(call.func, CallKind::LibC(name) if name.as_str() == "free").then_some(
                    Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                )
            })
            .collect();
        assert_eq!(frees.len(), 1);
        let slots = CrateSlots::build(&program);
        let target = |local| {
            SlotRef::Local(
                function,
                slots.fn_local_slots[&function]
                    .slot_for_local_depth(local, 0)
                    .unwrap(),
            )
        };
        let captured = capture(&program, &slots);
        let model = captured
            .model
            .as_ref()
            .expect("freed-column fixture remains accepted");
        assert_eq!(model.get(&target(a)), Some(&SlotKind::Raw));
        assert_eq!(model.get(&target(p)), Some(&SlotKind::Raw));
        assert!(captured.stats.source_retirement_decline.is_empty());
        let events: Vec<_> = captured
            .source
            .retirements
            .values()
            .filter(|event| event.key.function == "releases" && event.key.role == SourceRole::Free)
            .collect();
        assert_eq!(events.len(), 1, "the freed inventory fact remains present");
        let event = events[0];
        assert_eq!(
            (event.key.block, event.key.statement),
            (frees[0].block.as_u32(), frees[0].statement_index)
        );
        assert_eq!(event.key.phase, SourcePhase::Call);
        assert!(matches!(event.object, SourceObject::HeapThrough(_)));
        let chain: Vec<_> = captured
            .export
            .retirement_rounds
            .iter()
            .flat_map(|round| &round.conflicts)
            .filter(|row| {
                row.source == event.key
                    && row.target == target(a)
                    && row
                        .entry
                        .is_some_and(|entry| entry.parameter == a && entry.depth == 0)
            })
            .collect();
        assert!(
            !chain.is_empty(),
            "actual incoming-a repair must explain the downstream Raw copy"
        );
        assert!(captured.stats.commits_conflict > 0);
        for row in chain {
            eprintln!(
                "[D-CONSUMER] fixture=freed-column a={:?} p={:?} repair={row:?}",
                target(a),
                target(p)
            );
        }
    })
    .unwrap_or_else(|error| error.raise());
}
