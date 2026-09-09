//! R245: coverage stays local; foreign-only storage and inner-holder contrast.
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::VarDebugInfoContents;

use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        a5_overlap::{A5Mode, WholeProgramAttestation},
        construction::{
            CopyLendMode, TestValidationBackend, construct_bo_into, solve_bo_a5_config_reporting,
            verify_bo_construction_counting_for_test, verify_bo_construction_l2_for_test,
        },
        crate_slots::CrateSlots,
        export,
        mutability_facts::MutFacts,
        origins::compute_origins,
        portable_export,
        solver::{KindSolver, SlotRef},
    },
    utils::rustc::RustProgram,
};
const RAW: &str = r#"
#[repr(C)] pub struct Window{ lines:*mut *mut i32 }
unsafe extern "C" {static mut stdscr:*mut Window;fn wattr_get(w:*mut Window,a:*mut u32,p:*mut i16,x:*mut core::ffi::c_void)->i32;fn wattrset(w:*mut Window,a:i32)->i32;}
pub unsafe fn full_draw(){let mut old=0u32;let mut dummy=0i16;wattr_get(stdscr,&mut old,&mut dummy,core::ptr::null_mut());wattrset(stdscr,old as i32);}
"#;
fn with_program(code: &str, check: impl FnOnce(&RustProgram<'_>) + Send + Sync) {
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
        check(&RustProgram {
            tcx,
            functions,
            structs,
        });
    })
    .unwrap_or_else(|error| error.raise());
}
#[test]
fn e5_r245_full_draw_foreign_address_carriers_keep_model() {
    with_program(RAW, |program| {
        let slots = CrateSlots::build(program);
        let origins = compute_origins(program);
        let facts = MutFacts::from_program(program);
        let (result, capture) = export::with_bo_export(|| {
            solve_bo_a5_config_reporting(
                program,
                &slots,
                &origins,
                &facts,
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
        });
        assert!(
            result.is_ok(),
            "foreign-only storage must not decline the program: {result:?}"
        );
        let portable = portable_export::collect(program, &slots, &capture).unwrap();
        let final_row =
            &portable.families[&portable_export::ExportFamily::RetirementFinal].records[0].fields;
        let coverage = final_row["coverage"].as_array().unwrap();
        let terminal = final_row["terminal"].as_array().unwrap();
        let no_holder = coverage
            .iter()
            .filter(|row| row["receipt"] == "retirement:irrelevant-no-safe-holder")
            .count();
        let checked = terminal
            .iter()
            .filter(|row| row["receipt"] == "retirement:checked-without-conflict")
            .count();
        let native_checked = capture
            .source_retirement
            .as_ref()
            .unwrap()
            .terminal
            .values()
            .filter(|state| **state == super::EventDisposition::CheckedWithoutConflict)
            .count();
        assert_eq!(
            checked, native_checked,
            "each checked accepting source event needs its portable receipt"
        );
        assert!(
            no_holder + checked > 0,
            "R253 requires a countable accepting disposition"
        );
        assert_eq!(
            terminal.len(),
            capture.source_retirement.as_ref().unwrap().terminal.len()
        );
        assert!(
            capture
                .source_retirement
                .as_ref()
                .unwrap()
                .unresolved
                .is_empty()
        );
    });
}
#[test]
fn e5_r245_inner_holder_and_copy_chain_demote_raw_without_decline() {
    const CODE: &str = "pub unsafe fn f()->i32{let mut p:*mut i32;{let mut old=7;p=&mut old;}let q=p;let pp=&mut p as *mut *mut i32;let qq=pp;*q+**qq}";
    for backend in [
        TestValidationBackend::HardCheckRoundOptimize,
        TestValidationBackend::LegacyOptimize,
    ] {
        for l2 in [false, true] {
            with_program(CODE, |program| {
                let slots = CrateSlots::build(program);
                let origins = compute_origins(program);
                let facts = MutFacts::from_program(program);
                let function = program.functions[0];
                let body = program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let local = |name: &str| {
                    body.var_debug_info
                        .iter()
                        .find_map(|info| {
                            if info.name.as_str() == name {
                                if let VarDebugInfoContents::Place(place) = info.value {
                                    place.as_local()
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        })
                        .unwrap()
                };
                let named = |name: &str, depth| {
                    SlotRef::Local(
                        function,
                        slots.fn_local_slots[&function]
                            .slot_for_local_depth(local(name), depth)
                            .unwrap(),
                    )
                };
                let target = named("pp", 1);
                let copy = named("qq", 1);
                let ((model, _), capture) = export::with_bo_export(|| {
                    let solver = KindSolver::new(&slots);
                    let c = construct_bo_into(
                        program,
                        &slots,
                        &origins,
                        &facts,
                        &solver,
                        CopyLendMode::Baseline,
                    )
                    .unwrap();
                    let initial = solver.model_kinds_relaxing(&c.selectors).unwrap();
                    assert_eq!(
                        initial[&target],
                        SlotKind::Ref,
                        "witness requires real safe inner holder"
                    );
                    let result = if l2 {
                        verify_bo_construction_l2_for_test(
                            program, &slots, &origins, &solver, &c, &facts, backend,
                        )
                    } else {
                        verify_bo_construction_counting_for_test(
                            program, &slots, &origins, &solver, &c, &facts, backend,
                        )
                    };
                    result
                });
                let model = model.expect("missing represented inner loan must demote locally");
                assert_eq!(model[&target], SlotKind::Raw);
                assert_eq!(model[&copy], SlotKind::Raw);
                let portable = portable_export::collect(program, &slots, &capture).unwrap();
                assert!(
                    capture
                        .retirement_rounds
                        .iter()
                        .flat_map(|round| &round.demotions)
                        .any(|row| row.chain.len() > 1),
                    "fixture must retain a real copy-chain receipt"
                );
                let native_links: usize = capture
                    .retirement_rounds
                    .iter()
                    .flat_map(|round| &round.demotions)
                    .map(|row| row.chain.len())
                    .sum();
                let portable_links: usize = portable.families
                    [&portable_export::ExportFamily::RetirementRounds]
                    .records
                    .iter()
                    .flat_map(|row| row.fields["demotions"].as_array().unwrap())
                    .map(|row| row["chain"].as_array().unwrap().len())
                    .sum();
                assert_eq!(
                    portable_links, native_links,
                    "portable demotions must retain every copy-chain member"
                );
                let json = portable.canonical_json().unwrap();
                assert!(json.contains("p1s-inner-loan-missing:demote"));
                assert!(
                    capture
                        .source_retirement
                        .as_ref()
                        .unwrap()
                        .unresolved
                        .is_empty()
                );
            });
        }
    }
}

#[test]
fn e5_r245_multiple_realloc_branch_sites_hold_locally() {
    const CODE: &str = "unsafe extern \"C\"{fn realloc(p:*mut u8,n:usize)->*mut u8;fn free(p:*mut u8);}pub unsafe fn f(a:*mut u8,b:*mut u8){let p=realloc(a,16);if p.is_null(){free(a);}else{free(p);}let q=realloc(b,16);if q.is_null(){free(b);}else{free(q);}}";
    with_program(CODE, |program| {
        let slots = CrateSlots::build(program);
        let origins = compute_origins(program);
        let facts = MutFacts::from_program(program);
        let (model, capture) = export::with_bo_export(|| {
            solve_bo_a5_config_reporting(
                program,
                &slots,
                &origins,
                &facts,
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
        });
        assert!(
            model.is_ok(),
            "multiple representable calls must hold locally: {model:?}"
        );
        let json = portable_export::collect(program, &slots, &capture)
            .unwrap()
            .canonical_json()
            .unwrap();
        assert!(json.contains("realloc-ssa-coverage:hold-raw"));
    });
}
#[test]
fn e5_r245_zero_size_realloc_site_holds_without_program_decline() {
    with_program(
        "unsafe extern \"C\"{fn realloc(p:*mut u8,n:usize)->*mut u8;}pub unsafe fn f(a:*mut u8)->*mut u8{realloc(a,0)}",
        |program| {
            let slots = CrateSlots::build(program);
            let origins = compute_origins(program);
            let facts = MutFacts::from_program(program);
            let (model, capture) = export::with_bo_export(|| {
                solve_bo_a5_config_reporting(
                    program,
                    &slots,
                    &origins,
                    &facts,
                    A5Mode::PreciseReplay,
                    Some(WholeProgramAttestation::FrozenBenchmarkGraph),
                )
            });
            assert!(
                model.is_ok(),
                "zero-size lifecycle lacks an ownership representation, not a program model: {model:?}"
            );
            let json = portable_export::collect(program, &slots, &capture)
                .unwrap()
                .canonical_json()
                .unwrap();
            assert!(json.contains("realloc-ssa-coverage:hold-raw"));
        },
    );
}

#[test]
fn e5_r253_empty_realloc_inventory_fails_closed() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt, realloc, realloc_ssa, ssa::consume::initial_definitions,
    };
    with_program(
        r#"unsafe extern "C"{fn realloc(p:*mut u8,n:usize)->*mut u8;}pub unsafe fn f(p:*mut u8)->*mut u8{realloc(p,16)} pub fn no_realloc(){}"#,
        |program| {
            let ctxt = CrateCtxt::new(program);
            let sites = realloc::collect_sites(program);
            assert_eq!(sites.len(), 1);
            for &function in &program.functions {
                let body = program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let mut definitions = initial_definitions(&body, &ctxt);
                let before = definitions.def_sites.clone();
                let result = realloc_ssa::plan_body(&ctxt, &body, &mut definitions, &[]);
                if program.tcx.item_name(function.to_def_id()).as_str() == "f" {
                    let error =
                        result.expect_err("omitting every supplied realloc site must reject");
                    assert_eq!(error.site, sites[0].key);
                    assert_eq!(error.reason, realloc_ssa::ReallocSsaUnsupported::StaleSite);
                } else {
                    assert!(result.unwrap().is_empty());
                }
                assert_eq!(
                    definitions.def_sites, before,
                    "inventory rejection is transactional"
                );
            }
        },
    );
}

#[test]
fn e5_r253_l2_coverage_propagates_planner_decline_before_commit() {
    use crate::analyses::borrow_ownership::{
        borrow_verify::coverage_planner_fault, l2::DeclineReason,
    };
    const CODE: &str = "pub unsafe fn f()->i32{let mut p:*mut i32;{let mut old=7;p=&mut old;}let q=p;let pp=&mut p as *mut *mut i32;let qq=pp;*q+**qq}";
    with_program(CODE, |program| {
        let slots = CrateSlots::build(program);
        let origins = compute_origins(program);
        let facts = MutFacts::from_program(program);
        let solver = KindSolver::new(&slots);
        let c = construct_bo_into(
            program,
            &slots,
            &origins,
            &facts,
            &solver,
            CopyLendMode::Baseline,
        )
        .unwrap();
        let (model, stats) = coverage_planner_fault::with_overflow(|| {
            verify_bo_construction_l2_for_test(
                program,
                &slots,
                &origins,
                &solver,
                &c,
                &facts,
                TestValidationBackend::HardCheckRoundOptimize,
            )
        });
        assert!(model.is_none());
        assert_eq!(stats.l2_decline, Some(DeclineReason::ArithmeticOverflow));
        assert_eq!(
            stats.rounds, 1,
            "a planner decline ends this validation immediately"
        );
        assert_eq!(
            stats.commits_conflict, 0,
            "no coverage restriction after planner refusal"
        );
    });
}
