//! The branch's tests that lived in the legacy crate's `tests.rs` (moved in S1, D7): the BO
//! harness modules, the tests of the copied mutability variant, and the slot-universe tests.
//! The legacy crate keeps master's `tests.rs`.

use super::*;

mod mut_depth_robustness {
    use rustc_hir::{ItemKind, OwnerNode};

    use crate::{
        analyses::type_qualifier::foster::mutability::{Mutability, mutability_analysis},
        utils::rustc::RustProgram,
    };

    #[test]
    fn mut_depth_union_projected_pointer_load_is_conservatively_mutable() {
        ::utils::compilation::run_compiler_on_str(
            r#"
#[repr(C)]
union U { p: *mut i32, n: usize }
#[repr(C)]
struct S { p: *mut i32 }
pub unsafe fn load_union(u: U) -> *mut i32 { unsafe { u.p } }
pub unsafe fn load_struct(s: S) -> *mut i32 { s.p }
"#,
            |tcx| {
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
                let program = RustProgram {
                    tcx,
                    functions,
                    structs,
                };
                let result = mutability_analysis(&program);
                let find = |name: &str| {
                    *program
                        .functions
                        .iter()
                        .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                        .unwrap_or_else(|| panic!("missing fixture function {name}"))
                };
                assert_eq!(
                    result.function_body_fact(find("load_union"), 0, 0),
                    Some(Mutability::Mut),
                    "an unrepresentable union projection must conservatively bottom the return"
                );
                assert_eq!(
                    result.function_body_fact(find("load_struct"), 0, 0),
                    Some(Mutability::Imm),
                    "the representable non-union path must retain the existing immutable result"
                );
            },
        )
        .unwrap_or_else(|error| error.raise());
    }
}

/// The production ownership pipeline, as the legacy crate runs it: the baseline oracle of
/// `borrow_ownership_coherence` (moved from the legacy `tests.rs`'s `ownership_analysis`,
/// which master keeps private). Explicit legacy paths: under D7 the production pipeline is
/// master's, and this crate's `analyses::type_qualifier::foster::mutability` is BO's copy.
mod ownership_analysis {
    use pointer_replacer::{
        analyses::{
            output_params::compute_output_params,
            ownership::{AnalysisKind, CrateCtxt, whole_program::WholeProgramAnalysis},
            type_qualifier::foster::mutability::mutability_analysis,
        },
        utils::rustc::RustProgram,
    };
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_middle::mir::Local;
    use rustc_span::def_id::LocalDefId;

    pub(super) fn analyze_program<'tcx>(
        program: &RustProgram<'tcx>,
    ) -> pointer_replacer::analyses::ownership::whole_program::WholeProgramResults<'tcx> {
        let mutability_result = mutability_analysis(program);
        let aliases: FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>> =
            FxHashMap::default();
        let output_params = compute_output_params(program, &mutability_result, &aliases);
        let crate_ctxt = CrateCtxt::new(program);
        <WholeProgramAnalysis as AnalysisKind>::analyze(crate_ctxt, &output_params)
            .expect("ownership analysis should succeed")
    }
}

mod borrow_ownership_slots {
    use std::ops::Range;

    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{mir::Local, ty::TyCtxt};
    use rustc_span::def_id::LocalDefId;

    use crate::{
        analyses::borrow_ownership::{
            crate_slots::CrateSlots,
            slots::{SlotId, SlotOwner, StructFieldSlot},
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

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

    fn struct_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .structs
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("struct `{name}` not found"))
    }

    fn function_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .functions
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    fn slot_range_len(range: Range<SlotId>) -> usize {
        range.end.index() - range.start.index()
    }

    #[test]
    fn crate_slots_registers_struct_pointer_fields() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub a: *mut i32,
    pub b: *mut *mut i32,
}

pub unsafe fn use_s(s: *mut S) {
    let _x = (*s).a;
    let _y = (*s).b;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let a = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };
                let b = StructFieldSlot {
                    struct_did: s,
                    field_index: 1,
                };

                assert_eq!(
                    slot_range_len(slots.field_slots.slots_for_field(a).expect("field S::a")),
                    1
                );
                assert_eq!(
                    slot_range_len(slots.field_slots.slots_for_field(b).expect("field S::b")),
                    2
                );

                let a_slot = slots
                    .field_slots
                    .slot_for_field_depth(a, 0)
                    .expect("slot for field S::a depth 0");
                assert_eq!(slots.field_slots.slot(a_slot).owner, SlotOwner::Field(a));
                assert_eq!(slots.field_slots.slot(a_slot).depth, 0);
            },
        );
    }

    #[test]
    fn crate_slots_local_chain_stops_at_struct() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub a: *mut i32,
}

pub unsafe fn f(s: *mut S) {
    let _x = (*s).a;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let f = function_by_name(&program, "f");
                let local_s = Local::from_u32(1);
                let field = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };

                let local_slots = slots.fn_local_slots.get(&f).expect("slots for f");
                assert_eq!(
                    slot_range_len(local_slots.slots_for_local(local_s).expect("local _1")),
                    1
                );
                assert!(slots.field_slots.slots_for_field(field).is_some());
            },
        );
    }

    // ERA5a registers one uniform element chain for fixed array fields.
    // Array locals remain outside this registration surface; G's construction
    // controls separately prove the new field summaries carry explicit Raw holds.
    #[test]
    fn crate_slots_defers_array_of_pointer_shapes() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub arr: [*mut i32; 4],
    pub scalar: *mut i32,
}

pub unsafe fn takes_array(arr: [*mut i32; 4]) -> *mut i32 {
    arr[0]
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let arr = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };
                let scalar = StructFieldSlot {
                    struct_did: s,
                    field_index: 1,
                };

                assert!(slots.field_slots.is_array_field(arr));
                assert_eq!(
                    slot_range_len(
                        slots
                            .field_slots
                            .slots_for_field(arr)
                            .expect("array element summary")
                    ),
                    1
                );
                assert_eq!(
                    slot_range_len(
                        slots
                            .field_slots
                            .slots_for_field(scalar)
                            .expect("field S::scalar"),
                    ),
                    1
                );

                let f = function_by_name(&program, "takes_array");
                assert!(
                    slots
                        .fn_local_slots
                        .get(&f)
                        .expect("slots for takes_array")
                        .slots_for_local(Local::from_u32(1))
                        .is_none()
                );
            },
        );
    }

    #[test]
    fn crate_slots_tracks_nested_local_pointers() {
        run_compiler(
            r#"
pub unsafe fn g(pp: *mut *mut i32) -> i32 {
    **pp
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let g = function_by_name(&program, "g");
                let pp = Local::from_u32(1);

                let local_slots = slots.fn_local_slots.get(&g).expect("slots for g");
                assert_eq!(
                    slot_range_len(local_slots.slots_for_local(pp).expect("local _1")),
                    2
                );

                let depth_0 = local_slots
                    .slot_for_local_depth(pp, 0)
                    .expect("slot for pp depth 0");
                let depth_1 = local_slots
                    .slot_for_local_depth(pp, 1)
                    .expect("slot for pp depth 1");

                assert_eq!(local_slots.slot(depth_0).depth, 0);
                assert_eq!(local_slots.slot(depth_1).depth, 1);
            },
        );
    }

    #[test]
    fn crate_slots_generic_struct_field_depth() {
        run_compiler(
            r#"
#[repr(C)]
pub struct Wrap<T> {
    pub p: *mut T,
}

pub unsafe fn h(w: *mut Wrap<i32>) {
    let _z = (*w).p;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let wrap = struct_by_name(&program, "Wrap");
                let field = StructFieldSlot {
                    struct_did: wrap,
                    field_index: 0,
                };

                assert_eq!(
                    slot_range_len(
                        slots
                            .field_slots
                            .slots_for_field(field)
                            .expect("field Wrap::p"),
                    ),
                    1
                );
            },
        );
    }
}

mod borrow_ownership_solver {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{mir::Local, ty::TyCtxt};
    use rustc_span::def_id::LocalDefId;
    use z3::SatResult;

    use crate::{
        analyses::borrow_ownership::{
            SlotKind,
            crate_slots::CrateSlots,
            param_overlap::{OverlapMode, apply_coarse_constraints},
            slots::SlotId,
            solver::{KindSolver, Selectors, SlotRef},
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

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

    fn function_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .functions
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    fn with_g_slots<F>(f: F)
    where F: for<'tcx> FnOnce(&RustProgram<'tcx>, &CrateSlots, LocalDefId, SlotId, SlotId) + Send
    {
        run_compiler(
            r#"
pub unsafe fn g(pp: *mut *mut i32) -> i32 {
    **pp
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let g = function_by_name(&program, "g");
                let fn_slots = slots.fn_local_slots.get(&g).expect("slots for g");
                let pp = Local::from_u32(1);
                let d0 = fn_slots
                    .slot_for_local_depth(pp, 0)
                    .expect("pp depth 0 slot");
                let d1 = fn_slots
                    .slot_for_local_depth(pp, 1)
                    .expect("pp depth 1 slot");

                f(&program, &slots, g, d0, d1);
            },
        );
    }

    #[test]
    fn baseline_slot_encoding_is_satisfiable() {
        with_g_slots(|_, slots, _, _, _| {
            let ks = KindSolver::new(slots);

            assert_eq!(ks.check(), SatResult::Sat);
        });
    }

    #[test]
    fn max_ref_promotes_free_chain() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);
            let s0 = SlotRef::Local(g, d0);
            let s1 = SlotRef::Local(g, d1);

            assert_eq!(ks.check(), SatResult::Sat);
            let model = ks.model_kinds().expect("satisfiable model");
            assert_eq!(model.get(&s0), Some(&SlotKind::Ref));
            assert_eq!(model.get(&s1), Some(&SlotKind::Ref));
        });
    }

    #[test]
    fn hard_loop_materializes_only_the_optimized_round_model() {
        with_g_slots(|_, slots, g, d0, d1| {
            let solver = KindSolver::new(slots);
            let hard = solver.hard_loop_solver();
            let relaxed = solver
                .relax_selectors_hard_reporting(&hard, &Selectors::new(Vec::new(), Vec::new()))
                .expect("empty selector set is hard-SAT");
            let model = solver
                .optimized_model_under(&relaxed)
                .expect("optimized round model");

            assert_eq!(model.get(&SlotRef::Local(g, d0)), Some(&SlotKind::Ref));
            assert_eq!(model.get(&SlotRef::Local(g, d1)), Some(&SlotKind::Ref));
            assert_eq!(solver.hard_check_count(), 1);
            assert_eq!(solver.optimize_materialization_count(), 1);
            assert_eq!(solver.check_sat_count(), 2);
            assert!(solver.hard_check_elapsed() > std::time::Duration::ZERO);
            assert!(solver.optimize_materialization_elapsed() > std::time::Duration::ZERO);
        });
    }

    #[test]
    fn hard_loop_snapshots_and_syncs_only_hard_assertions() {
        with_g_slots(|_, slots, g, d0, _| {
            let solver = KindSolver::new(slots);
            let hard = solver.hard_loop_solver();

            assert_eq!(hard.assertion_count(), solver.hard_assertion_count());
            let before = hard.assertion_count();
            solver.add_borrow_exclusion(Some(SlotRef::Local(g, d0)), &[]);
            assert_eq!(hard.sync_from(&solver), 1);
            assert_eq!(hard.assertion_count(), before + 1);
            assert_eq!(hard.assertion_count(), solver.hard_assertion_count());
        });
    }

    #[test]
    fn max_ref_under_assumption() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);
            let s0 = SlotRef::Local(g, d0);
            let s1 = SlotRef::Local(g, d1);

            ks.assume(s0, SlotKind::Owning);

            assert_eq!(ks.check(), SatResult::Sat);
            let model = ks.model_kinds().expect("satisfiable model");
            assert_eq!(model.get(&s0), Some(&SlotKind::Owning));
            assert_eq!(model.get(&s1), Some(&SlotKind::Ref));
        });
    }

    #[test]
    fn optimal_model_is_repeatable() {
        with_g_slots(|_, slots, _, _, _| {
            let ks = KindSolver::new(slots);

            let first = ks.model_kinds().expect("first satisfiable model");
            let second = ks.model_kinds().expect("second satisfiable model");

            assert_eq!(first, second);
        });
    }

    #[test]
    fn monotonicity_rejects_raw_over_owning() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);

            ks.assume(SlotRef::Local(g, d0), SlotKind::Raw);
            ks.assume(SlotRef::Local(g, d1), SlotKind::Owning);

            assert_eq!(ks.check(), SatResult::Unsat);
        });
    }

    #[test]
    fn owning_chain_is_satisfiable() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);

            ks.assume(SlotRef::Local(g, d0), SlotKind::Owning);
            ks.assume(SlotRef::Local(g, d1), SlotKind::Owning);

            assert_eq!(ks.check(), SatResult::Sat);
        });
    }

    #[test]
    fn ref_separates_raw_from_deeper_owning() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);

            ks.assume(SlotRef::Local(g, d0), SlotKind::Ref);
            ks.assume(SlotRef::Local(g, d1), SlotKind::Owning);

            assert_eq!(ks.check(), SatResult::Sat);
        });
    }

    #[test]
    fn model_reports_assumed_raw_slots() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);
            let s0 = SlotRef::Local(g, d0);
            let s1 = SlotRef::Local(g, d1);

            ks.assume(s0, SlotKind::Raw);
            ks.assume(s1, SlotKind::Raw);

            assert_eq!(ks.check(), SatResult::Sat);
            let model = ks.model_kinds().expect("satisfiable model");
            assert_eq!(model.get(&s0), Some(&SlotKind::Raw));
            assert_eq!(model.get(&s1), Some(&SlotKind::Raw));
        });
    }

    #[test]
    fn a5_baseline_and_precise_modes_do_not_add_coarse_constraints() {
        with_g_slots(|_, slots, g, d0, d1| {
            let left = SlotRef::Local(g, d0);
            let right = SlotRef::Local(g, d1);
            let expected = KindSolver::new(slots)
                .model_kinds()
                .expect("baseline model");
            for mode in [OverlapMode::Baseline, OverlapMode::PreciseReplay] {
                let solver = KindSolver::new(slots);
                assert_eq!(apply_coarse_constraints(mode, &solver, [(left, right)]), 0);
                assert_eq!(solver.model_kinds().expect("neutral model"), expected);
            }
            assert_eq!(OverlapMode::proposed_landing(), OverlapMode::PreciseReplay);
            assert!(!OverlapMode::PreciseReplay.is_pricing_control());
        });
    }

    #[test]
    fn a5_coarse_mode_forbids_both_slots_ref() {
        with_g_slots(|_, slots, g, d0, d1| {
            let left = SlotRef::Local(g, d0);
            let right = SlotRef::Local(g, d1);
            let solver = KindSolver::new(slots);
            assert_eq!(
                apply_coarse_constraints(OverlapMode::CoarseConstraint, &solver, [(right, left)]),
                1
            );
            solver.assume(left, SlotKind::Ref);
            solver.assume(right, SlotKind::Ref);
            assert_eq!(solver.check(), SatResult::Unsat);
            assert!(OverlapMode::CoarseConstraint.is_pricing_control());
        });
    }
}

mod borrow_ownership_coherence {
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{
        mir::{Local, Location, Operand, RETURN_PLACE, Rvalue, StatementKind},
        ty::TyCtxt,
    };
    use rustc_span::def_id::LocalDefId;
    use z3::SatResult;

    use crate::{
        analyses::{
            borrow::{GBorrowInferCtxt, demote_pointers_iterative_with_fields},
            borrow_ownership::{
                CrateCtxt, SlotKind,
                borrow_engine::{
                    borrow_conflicts_replaying_with_flows_and_copy_lends,
                    borrow_conflicts_replaying_witnessed_with_copy_lends,
                    with_escaped_extension_trace,
                },
                borrow_verify::{
                    SlotConflict, materialize_guards, model_accepts, revalidate,
                    revalidate_replaying, verify_guarded_to_fixpoint_counting, verify_to_fixpoint,
                },
                coherence::{
                    CopyLendPair, add_coherence, add_coherence_with_copy_lends,
                    constrain_field_ownership, selected_copy_lend_sites,
                },
                construction::{
                    CopyLendMode, analyze_copy_lend_eligibility, construct_bo_into,
                    construct_bo_into_return_refined, solve_bo_overlap_config,
                    solve_bo_overlap_reference_reporting, verify_bo_construction_counting,
                },
                crate_slots::CrateSlots,
                emit_crate_ownership_constraints, emit_crate_ownership_constraints_with_copy_lends,
                esc_minimal::with_fixture_selection,
                export::{LoanClass, location_key, with_bo_export},
                mutability_facts::MutFacts,
                origins::{collect_no_borrow_origin_slots, compute_origins},
                param_overlap::{OverlapMode, WholeProgramAttestation},
                slots::{SlotId, SlotOwner, StructFieldSlot},
                solver::{
                    BoOwnDatabase, KindSolver, SelectorTrace, Selectors, SlotRef,
                    with_selector_trace,
                },
                sources::collect_malloc_source_slots,
                ssa::constraint::{Database, Gen, Var},
            },
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

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

    fn function_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .functions
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    fn struct_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .structs
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("struct `{name}` not found"))
    }

    fn local_slot(slots: &CrateSlots, fn_did: LocalDefId, local: Local, depth: u8) -> SlotRef {
        let slot = slots
            .fn_local_slots
            .get(&fn_did)
            .unwrap_or_else(|| panic!("slots for function {fn_did:?}"))
            .slot_for_local_depth(local, depth)
            .unwrap_or_else(|| panic!("slot for local {local:?} depth {depth}"));

        SlotRef::Local(fn_did, slot)
    }

    fn selector_final_sets(trace: &SelectorTrace) -> Vec<(Vec<usize>, Vec<usize>)> {
        trace
            .epochs
            .iter()
            .map(|epoch| {
                let mut dropped = epoch.final_dropped.clone();
                dropped.sort_unstable();
                dropped.dedup();
                let active = (0..trace.total)
                    .filter(|index| dropped.binary_search(index).is_err())
                    .collect();
                (dropped, active)
            })
            .collect()
    }

    fn dropped_selector_set(selectors: &Selectors, dropped: &[z3::ast::Bool]) -> Vec<usize> {
        let mut dropped = dropped
            .iter()
            .map(|selector| {
                selectors
                    .index_of(selector)
                    .expect("dropped selector belongs to the selector universe")
            })
            .collect::<Vec<_>>();
        dropped.sort_unstable();
        dropped.dedup();
        dropped
    }

    fn selector_trace_sidecar(case: &str, legacy: &SelectorTrace, hard: &SelectorTrace) -> String {
        let mut output = String::from(
            "case\tbackend\tepoch\tstep\tphase\tselector\tactive_before\tcore_members\toutcome\tfinal_dropped\tfinal_active\n",
        );
        for (backend, trace) in [("legacy-optimize", legacy), ("plain-solver", hard)] {
            for (epoch_index, epoch) in trace.epochs.iter().enumerate() {
                let (final_dropped, final_active) = selector_final_sets(trace)[epoch_index].clone();
                let join = |items: &[usize]| {
                    items
                        .iter()
                        .map(usize::to_string)
                        .collect::<Vec<_>>()
                        .join(",")
                };
                for (step, event) in epoch.events.iter().enumerate() {
                    let mut core = event.core_selectors.clone();
                    core.sort_unstable();
                    core.dedup();
                    output.push_str(&format!(
                        "{case}\t{backend}\t{epoch_index}\t{}\t{:?}\t{}\t{}\t{}\t{:?}\t{}\t{}\n",
                        step + 1,
                        event.phase,
                        event.selector_index,
                        join(&event.active_before),
                        join(&core),
                        event.outcome,
                        join(&final_dropped),
                        join(&final_active),
                    ));
                }
            }
        }
        output
    }

    fn maybe_write_selector_trace_sidecar(
        case: &str,
        legacy: &SelectorTrace,
        hard: &SelectorTrace,
    ) {
        let Some(directory) = std::env::var_os("CRAT_S24R1_SELECTOR_SIDECAR_DIR") else {
            return;
        };
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).expect("create S2-4-R1 selector sidecar directory");
        std::fs::write(
            directory.join(format!("{case}.tsv")),
            selector_trace_sidecar(case, legacy, hard),
        )
        .expect("write S2-4-R1 selector sidecar");
    }

    /// The `Local` whose source-level variable name is `name`, via MIR debug info.
    fn local_by_var_name(tcx: TyCtxt<'_>, did: LocalDefId, name: &str) -> Local {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        for vdi in body.var_debug_info.iter() {
            if vdi.name.as_str() == name
                && let rustc_middle::mir::VarDebugInfoContents::Place(place) = &vdi.value
                && let Some(local) = place.as_local()
            {
                return local;
            }
        }
        panic!("no local named `{name}` in {did:?}");
    }

    #[test]
    fn a16_refined_links_only_modeled_borrow_returns() {
        run_compiler(
            r#"
unsafe extern "C" { fn malloc(size: usize) -> *mut core::ffi::c_void; }
unsafe extern "C" { fn opaque(p: *mut i32) -> *mut i32; }
struct Cell { p: *mut i32 }
unsafe fn id(p: *mut i32) -> *mut i32 { p }
unsafe fn fresh() -> *mut i32 { malloc(4) as *mut i32 }
unsafe fn seed(c: *mut Cell, p: *mut i32) { (*c).p = opaque(p); }
unsafe fn tainted(c: *mut Cell) -> *mut i32 { (*c).p }
unsafe fn caller(p: *mut i32) -> i32 {
    let q = id(p);
    *q
}
unsafe fn fresh_caller() -> i32 {
    let r = fresh();
    *r
}
unsafe fn tainted_caller(c: *mut Cell) -> i32 {
    let r = tainted(c);
    *r
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let mut_facts = MutFacts::from_program(&program);
                let id = function_by_name(&program, "id");
                let caller = function_by_name(&program, "caller");
                let id_return = SlotRef::Local(
                    id,
                    slots.fn_local_slots[&id]
                        .slot_for_local_depth(RETURN_PLACE, 0)
                        .expect("id return slot"),
                );
                let q = local_slot(&slots, caller, local_by_var_name(tcx, caller, "q"), 0);

                let baseline_solver = KindSolver::new(&slots);
                let baseline = construct_bo_into(
                    &program,
                    &slots,
                    &origins,
                    &mut_facts,
                    &baseline_solver,
                    CopyLendMode::Baseline,
                )
                .expect("baseline construction");
                baseline_solver.assume(id_return, SlotKind::Raw);
                let baseline_model = verify_bo_construction_counting(
                    &program,
                    &slots,
                    &origins,
                    &baseline_solver,
                    &baseline,
                    &mut_facts,
                )
                .0
                .expect("baseline model");
                assert_eq!(baseline_model.get(&q), Some(&SlotKind::Ref));

                let refined_solver = KindSolver::new(&slots);
                let (refined, links) = construct_bo_into_return_refined(
                    &program,
                    &slots,
                    &origins,
                    &mut_facts,
                    &refined_solver,
                )
                .expect("refined construction");
                assert_eq!(links, 1, "only id's modeled return receives a link");
                refined_solver.assume(id_return, SlotKind::Raw);
                let refined_model = verify_bo_construction_counting(
                    &program,
                    &slots,
                    &origins,
                    &refined_solver,
                    &refined,
                    &mut_facts,
                )
                .0
                .expect("refined model");
                assert_ne!(refined_model.get(&q), Some(&SlotKind::Ref));
            },
        );
    }

    #[test]
    fn a16_refined_input_ub_scope_controls() {
        run_compiler(
            r#"
unsafe fn make() -> *mut i32 {
    let mut value = 1;
    let p = &mut value as *mut i32;
    p
}
pub unsafe fn f() -> i32 {
    let q = make();
    *q
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let mut_facts = MutFacts::from_program(&program);
                let solver = KindSolver::new(&slots);
                let (_, links) = construct_bo_into_return_refined(
                    &program, &slots, &origins, &mut_facts, &solver,
                )
                .expect("input-UB diagnostic construction");
                assert_eq!(
                    links, 0,
                    "a stack-local return is not a modeled argument origin"
                );
            },
        );

        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
unsafe fn inner(p: *mut i32) -> *mut i32 { p }
unsafe fn writer(p: *mut i32) { *p = 2; }
unsafe fn middle(p: *mut i32) -> *mut i32 {
    let q = inner(p);
    writer(p);
    q
}
pub unsafe fn f() -> i32 {
    let owner = malloc(4) as *mut i32;
    let q = middle(owner);
    let value = *q;
    free(owner as *mut core::ffi::c_void);
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let mut_facts = MutFacts::from_program(&program);
                let f = function_by_name(&program, "f");
                let q = local_slot(&slots, f, local_by_var_name(tcx, f, "q"), 0);

                let baseline_solver = KindSolver::new(&slots);
                let baseline = construct_bo_into(
                    &program,
                    &slots,
                    &origins,
                    &mut_facts,
                    &baseline_solver,
                    CopyLendMode::Baseline,
                )
                .expect("UB-free control baseline construction");
                let baseline_model = verify_bo_construction_counting(
                    &program,
                    &slots,
                    &origins,
                    &baseline_solver,
                    &baseline,
                    &mut_facts,
                )
                .0
                .expect("UB-free control baseline model");
                assert_eq!(baseline_model.get(&q), Some(&SlotKind::Ref));

                let refined_solver = KindSolver::new(&slots);
                let (refined, links) = construct_bo_into_return_refined(
                    &program,
                    &slots,
                    &origins,
                    &mut_facts,
                    &refined_solver,
                )
                .expect("UB-free control refined construction");
                assert_eq!(
                    links, 2,
                    "both argument-derived return boundaries are linked"
                );
                let refined_model = verify_bo_construction_counting(
                    &program,
                    &slots,
                    &origins,
                    &refined_solver,
                    &refined,
                    &mut_facts,
                )
                .0
                .expect("UB-free control refined model");
                assert_eq!(refined_model.get(&q), Some(&SlotKind::Raw));

                let production = solve_bo_overlap_config(
                    &program,
                    &slots,
                    &origins,
                    &mut_facts,
                    OverlapMode::PreciseReplay,
                    Some(WholeProgramAttestation::FrozenBenchmarkGraph),
                )
                .expect("landed precise production model");
                assert_eq!(production.model.get(&q), Some(&SlotKind::Raw));
                assert_eq!(production.return_refined_links, 2);
                assert!(
                    production
                        .receipt
                        .contains("soundness_mode=a14_a16_refined\n")
                );

                let unattested = solve_bo_overlap_config(
                    &program,
                    &slots,
                    &origins,
                    &mut_facts,
                    OverlapMode::PreciseReplay,
                    None,
                )
                .expect("unattested product fallback");
                assert_eq!(unattested.model.get(&q), Some(&SlotKind::Raw));
                assert_eq!(unattested.return_refined_links, 2);
                assert!(unattested.receipt.contains("a5_abi_guard=refused:"));
            },
        );
    }

    /// Shared §8 BB3-b assertion for a mixed-role-local fixture (a local conflated to one
    /// flow-insensitive `Owning` slot that also carries a reference role). `verify_to_fixpoint`
    /// must accept a model with **no hidden `Ref`-vs-`Ref` aliasing**: the BB3-b under-report was
    /// an `Owning` slot being EXCLUDED from the replay, hiding its reference role's conflict. The
    /// complete-by-construction candidacy (every non-`Ref` slot a replay candidate) makes that
    /// impossible, so we assert it directly — the accepted model is clean under the COMPLETE
    /// replay (`is_raw = model != Ref`), and the mixed-role local does not survive as an aliasing
    /// `Ref`. Non-vacuous: the all-`Ref` round-0 shows the shape is genuinely hazardous. (The
    /// mixed-role local is output `Owning` — an ownership-precision residual deferred to
    /// flow-sensitivity, NOT a borrow under-report.) A regression that re-excludes `Owning` slots
    /// from the replay would surface the hidden conflict at the COMPLETE-replay assertion.
    fn assert_mixed_role_no_hidden_aliasing(tcx: TyCtxt<'_>, fn_name: &str, local: &str) {
        let program = collect_program(tcx);
        let f = function_by_name(&program, fn_name);
        let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_s, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("ownership emission");
        add_coherence(&solver, &slots, f, &body);

        // Non-vacuous: the shape is genuinely hazardous (a round-0 all-Ref aliasing conflict).
        let round0 = revalidate(&program, &slots, |_| true, true);
        assert!(
            round0.get(&f).is_some_and(|e| !e.is_empty()),
            "[{fn_name}] shape must be hazardous (a round-0 all-Ref conflict)"
        );

        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
            .expect("CEGAR converges");

        // The mixed-role local must not survive as an aliasing `Ref`.
        let local_ref = local_slot(&slots, f, local_by_var_name(tcx, f, local), 0);
        assert_ne!(
            model.get(&local_ref),
            Some(&SlotKind::Ref),
            "[{fn_name}] mixed-role local `{local}` must not survive as a Ref; got {:?}",
            model.get(&local_ref)
        );

        // Contract: no hidden Ref-vs-Ref aliasing — clean under the COMPLETE replay (every
        // non-Ref slot a candidate, matching verify_to_fixpoint's own candidacy).
        let complete = revalidate_replaying(
            &program,
            &slots,
            |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref),
            |s: SlotRef| model.get(&s) != Some(&SlotKind::Ref),
            true,
        );
        assert!(
            complete.get(&f).map_or(true, |e| e.is_empty()),
            "[{fn_name}] accepted model must have no hidden aliasing under the complete replay; \
             got {complete:?}"
        );
    }

    #[test]
    fn alloc_free_emits_ownership_into_kind_solver() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_free() {
    let p = unsafe { malloc(4) };
    unsafe { free(p) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B1 ownership emission should run");

                assert!(
                    stats.z3_ast_len > 1,
                    "expected per-version ownership Bool vars to be allocated"
                );
                // 1 source from malloc + 1 sink from free.
                assert_eq!(stats.source_sink_emissions, 2);
                // §NB-F: BOTH are retractable now — 1 source selector (malloc)
                // + 1 sink selector (free).
                assert_eq!(selectors.sources().len(), 1);
                assert_eq!(selectors.sinks().len(), 1);
                assert_eq!(selectors.all().len(), 2);
                assert!(kind_solver.model_kinds_relaxing(&selectors).is_some());
            },
        );
    }

    /// Locate the destination `Local` of the first call to `callee` (e.g. the
    /// `*mut c_void` local that `malloc`'s result is written into). Robust to
    /// MIR temp renumbering — we never hardcode the index.
    fn call_destination(
        tcx: TyCtxt<'_>,
        body: &rustc_middle::mir::Body<'_>,
        callee: &str,
    ) -> Local {
        call_nth_destination(tcx, body, callee, 0)
    }

    /// Destination `Local` of the `n`-th (0-indexed, in basic-block order) call to
    /// `callee` — for functions with several calls to the same callee.
    fn call_nth_destination(
        tcx: TyCtxt<'_>,
        body: &rustc_middle::mir::Body<'_>,
        callee: &str,
        n: usize,
    ) -> Local {
        let mut seen = 0;
        for bbdata in body.basic_blocks.iter() {
            let Some(term) = &bbdata.terminator else {
                continue;
            };
            if let rustc_middle::mir::TerminatorKind::Call {
                func, destination, ..
            } = &term.kind
            {
                if let Some((def_id, _)) = func.const_fn_def() {
                    if tcx.def_path_str(def_id).rsplit("::").next() == Some(callee) {
                        if seen == n {
                            return destination.local;
                        }
                        seen += 1;
                    }
                }
            }
        }
        panic!("no call #{n} to `{callee}` found");
    }

    /// B2: the per-version ownership forced by `malloc`'s `source` hook must be
    /// solidified onto the slot — `p`'s depth-0 slot becomes `Owning`. Without
    /// the version→slot linking, the unconstrained slot would be `Ref` (max-ref).
    #[test]
    fn alloc_free_links_owning_to_slot() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_free() {
    let p = unsafe { malloc(4) };
    unsafe { free(p) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let alloc_free = function_by_name(&program, "alloc_free");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(alloc_free)
                    .borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B2 ownership emission should run");

                let p_local = call_destination(tcx, &body, "malloc");
                let p = local_slot(&slots, alloc_free, p_local, 0);

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
            },
        );
    }

    /// B2 headline (Ref-over-Owning) via a store-through-pointer `*out = malloc`.
    /// The inner (`*out`) is `Owning` — malloc's ownership solidified onto the
    /// temp slot and carried to `out`'s inner depth by coherence; the outer `out`
    /// is caller storage forced non-owning by `exit`, so §4 (`¬(raw ∧ own)`) +
    /// max-ref make it `Ref`. Without the version→slot link, `*out` is not
    /// `Owning` and this fails. NOTE: `output_params` is empty here, so this
    /// exercises the store-through-deref shape, not output-param *classification*.
    #[test]
    fn store_through_ptr_is_ref_over_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn fill(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let fill = function_by_name(&program, "fill");
                let body = tcx.mir_drops_elaborated_and_const_checked(fill).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B2 ownership emission should run");
                add_coherence(&kind_solver, &slots, fill, &body);

                // `out` is param Local 1: out[0] = borrowed caller storage,
                // out[1] = the malloc-owned inner.
                let out_outer = local_slot(&slots, fill, Local::from_u32(1), 0);
                let out_inner = local_slot(&slots, fill, Local::from_u32(1), 1);

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(
                    model.get(&out_inner),
                    Some(&SlotKind::Owning),
                    "inner *out = Owning (the malloc'd value)"
                );
                assert_eq!(
                    model.get(&out_outer),
                    Some(&SlotKind::Ref),
                    "outer out = Ref (borrowed caller storage)"
                );
            },
        );
    }

    /// B3a: a leaked allocation (its `source` owning conflicts with return
    /// finalization) makes the single solve UNSAT — `source` hard-forces the
    /// malloc'd local owning while finalize-temporaries hard-forces the same SSA
    /// version false. The relax loop drops that source's selector (leaks the
    /// allocation) and returns a SAT model. Assertion is deliberately
    /// kind-agnostic (solvable ∧ not Owning); the exact non-owning variant
    /// (Ref vs Raw) is a 3f borrow-integration concern, not pinned here.
    #[test]
    fn leaked_alloc_return_relaxes_to_sat() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { malloc(8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let leak = function_by_name(&program, "leak");
                let body = tcx.mir_drops_elaborated_and_const_checked(leak).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B3a ownership emission should run");

                // Prove the relax path is genuinely exercised: exactly one source
                // selector, and the un-relaxed solve (assuming it) is UNSAT — so a
                // broken impl that ignored selectors could not pass.
                assert_eq!(selectors.all().len(), 1);
                assert_eq!(
                    kind_solver.check_with_assumptions(selectors.all()),
                    SatResult::Unsat,
                    "the source-owning constraint must make the single solve UNSAT"
                );

                // The relax loop must leak the source and return a model.
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("relax loop should resolve the UNSAT by leaking the source");

                let p_local = call_destination(tcx, &body, "malloc");
                let p = local_slot(&slots, leak, p_local, 0);
                assert_ne!(
                    model.get(&p),
                    Some(&SlotKind::Owning),
                    "leaked allocation must not be Owning"
                );
            },
        );
    }

    /// B3a multi-source: relaxation must leak only the *conflicting* allocation.
    /// `a` is malloc'd and freed (no finalize conflict → stays `Owning`); `b` is
    /// malloc'd and leaked via `&raw mut b` (its owning conflicts with finalize).
    /// The relax loop must drop only `b`'s selector — a maximal-source-retention
    /// policy. A naive "drop any unsat-core member" loop could leak `a` too if
    /// z3's (non-minimal) core happened to include it.
    #[test]
    fn two_allocs_leaks_only_the_conflicting_one() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn two_allocs() -> *mut *mut core::ffi::c_void {
    let a = unsafe { malloc(8) };
    unsafe { free(a) };
    let mut b = unsafe { malloc(8) };
    &raw mut b
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let two = function_by_name(&program, "two_allocs");
                let body = tcx.mir_drops_elaborated_and_const_checked(two).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B3a ownership emission should run");

                // Two sources + (§NB-F) one free-sink selector; assuming all is
                // UNSAT (b conflicts with finalize — assuming more preserves it).
                assert_eq!(selectors.sources().len(), 2);
                assert_eq!(selectors.sinks().len(), 1);
                assert_eq!(
                    kind_solver.check_with_assumptions(selectors.all()),
                    SatResult::Unsat
                );

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("relax loop should leak only b");

                // `a` (freed) must remain Owning; `b` (leaked) must not.
                let a_local = call_nth_destination(tcx, &body, "malloc", 0);
                let b_local = call_nth_destination(tcx, &body, "malloc", 1);
                let a = local_slot(&slots, two, a_local, 0);
                let b = local_slot(&slots, two, b_local, 0);
                assert_eq!(
                    model.get(&a),
                    Some(&SlotKind::Owning),
                    "the freed allocation must stay Owning (not over-leaked)"
                );
                assert_ne!(
                    model.get(&b),
                    Some(&SlotKind::Owning),
                    "the leaked allocation must not be Owning"
                );
            },
        );
    }

    /// §S2-1 (NB-F review F2) — a GENUINE mixed source/sink either/or tie
    /// whose UNSAT core is EXACTLY `{source-selector, sink-selector}`, so
    /// phase-2 restoration provably cannot undo it (F2's caveat) and the
    /// phase-1 drop choice alone decides which side leaks.
    ///
    /// The fabric that admits it is B4's Output protocol: every BO pointer
    /// arg is `Param::Output`, so a call pushes EQUALITIES (`sig.use =
    /// arg.use`, `sig.def = arg.def`) — a bidirectional broadcast shared by
    /// all call sites — and an Output param's final version is EXPORTED
    /// (`exit` equates it to `sig.def`), not finalize-pinned. The empty
    /// `pass(_x)` therefore fuses `sig.use = x_v0 = sig.def` into one
    /// equality class. `source_side` puts the source-forced `m_v1` into that
    /// class and escapes `m` through its (unconsumed) return — no sink on the
    /// source's branch. `sink_side`'s copy `let b = a` emits the fabric's
    /// only exclusivity, `push_linear(b_w1, a_v1, a_v0)` with `¬(b_w1 ∧
    /// a_v1)`; `pass(b)` puts fork child `b_w1` into the same class, `b`
    /// escapes through the return, and `free(a)` pins the sibling `a_v1`.
    /// So `¬(b_w1 ∧ a_v1)` fires iff `s ∧ k` — and with only these two
    /// selectors in the crate, `{s, k}` is the whole core.
    ///
    /// The tie is PROVED inside the fixture (it can never pass vacuously):
    /// `check(H∧s∧k) = Unsat ∧ check(H∧s) = Sat ∧ check(H∧k) = Sat`.
    ///
    /// RETENTION POLICY UNDER TEST (S2-1 decided-default: drop sinks first,
    /// retain sources — source retention drives Owning conversion, and a
    /// leaked sink only costs a leak while a leaked source costs precision):
    /// the relax loop must leak exactly `{k}` and retain the source,
    /// converting `m` to Owning. The pre-fix positional phase-1 pick drops
    /// the earliest-positioned core assumption; `Selectors::new` orders
    /// sources first, so it leaks the SOURCE and retains the sink — F2's
    /// backwards outcome, which phase 2 then cannot repair.
    #[test]
    fn nbs2_mixed_tie_drops_sink_retains_source() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

// This fixture requires an unclassified contract to retain its mixed core.
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
"#,
            |tcx| {
                let program = collect_program(tcx);
                let source_side = function_by_name(&program, "source_side");
                let sink_side = function_by_name(&program, "sink_side");
                let source_body = tcx
                    .mir_drops_elaborated_and_const_checked(source_side)
                    .borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("S2-1 ownership emission should run");

                // Exactly ONE source (source_side's malloc) and ONE sink
                // (sink_side's free) exist in the crate: the mixed pair IS
                // the entire retractable-assumption set.
                assert_eq!(selectors.sources().len(), 1);
                assert_eq!(selectors.sinks().len(), 1);
                let s = selectors.sources()[0].clone();
                let k = selectors.sinks()[0].clone();

                // THE TIE PROOF (non-vacuity): jointly infeasible, each side
                // individually satisfiable — a true either/or tie that
                // phase-2 restoration cannot undo.
                assert_eq!(
                    kind_solver.check_with_assumptions(&[s.clone(), k.clone()]),
                    SatResult::Unsat,
                    "mixed pair {{source, sink}} must be a genuine joint conflict"
                );
                assert_eq!(
                    kind_solver.check_with_assumptions(&[s.clone()]),
                    SatResult::Sat,
                    "the source alone must be satisfiable (m escapes via the return)"
                );
                assert_eq!(
                    kind_solver.check_with_assumptions(&[k.clone()]),
                    SatResult::Sat,
                    "the sink alone must be satisfiable (a's unit is voluntary)"
                );

                // RETENTION under the relax loop: leak exactly the sink,
                // retain the source.
                let ((model, dropped), legacy_trace) = with_selector_trace(|| {
                    kind_solver
                        .model_kinds_relaxing_reporting(&selectors)
                        .expect("legacy relax loop must converge to SAT")
                });
                let ((hard_model, hard_dropped), hard_trace) = with_selector_trace(|| {
                    let hard = kind_solver.hard_loop_solver();
                    let relaxed = kind_solver
                        .relax_selectors_hard_reporting(&hard, &selectors)
                        .expect("hard relax loop must converge to SAT");
                    let dropped = relaxed.dropped().to_vec();
                    let model = kind_solver
                        .optimized_model_under(&relaxed)
                        .expect("hard decisions admit an optimized model");
                    (model, dropped)
                });
                assert_eq!(
                    selector_final_sets(&legacy_trace),
                    selector_final_sets(&hard_trace)
                );
                maybe_write_selector_trace_sidecar("mixed-tie", &legacy_trace, &hard_trace);
                assert_eq!(
                    dropped_selector_set(&selectors, &hard_dropped),
                    dropped_selector_set(&selectors, &dropped)
                );
                assert_eq!(hard_model, model);
                assert_eq!(
                    dropped.len(),
                    1,
                    "a true 1-vs-1 tie leaks exactly one selector"
                );
                assert!(
                    selectors.is_sink(&dropped[0]),
                    "a mixed tie must drop the SINK and retain the SOURCE (S2-1 policy)"
                );

                // Source retention drives Owning conversion: m stays Owning.
                let m_local = call_destination(tcx, &source_body, "malloc");
                let m_slot = local_slot(&slots, source_side, m_local, 0);
                assert_eq!(
                    model.get(&m_slot),
                    Some(&SlotKind::Owning),
                    "the retained source must convert m to Owning"
                );

                // OBSERVED-VALUE PIN (semantic-change comment, NB-F practice):
                // the leaked free's pointer `a` settles OWNING here — the
                // retained source forces the shared `pass` equality class
                // true, the copy's fork child `b_w1` receives it, and
                // child⇒parent (`x → z` of the linear split) pulls `a`'s
                // entry version owning. A leaked free's value kind is
                // OBSERVED, not designed (NB-F decision 3): this is a
                // synthetic instance of a leaked free settling non-Raw.
                // Cross-ref S2-2 (2026-07-04-nb-stage2-backlog.md): the
                // freed-slot kind census must find this pin, not rediscover
                // it; a freed-`Ref` (not seen here) remains the
                // soundness-critical case that gates C2. This is a BREAKABLE
                // observation, not a semantic contract: if a later phase
                // (NB3/NB4 origins, call semantics) legitimately changes the
                // value, re-derive and re-pin the observation — do not
                // preserve Owning for its own sake.
                let a_local = local_by_var_name(tcx, sink_side, "a");
                let a_slot = local_slot(&slots, sink_side, a_local, 0);
                assert_eq!(
                    model.get(&a_slot),
                    Some(&SlotKind::Owning),
                    "observed: leaked-free a pulled Owning via the broadcast + fork parent"
                );
            },
        );
    }

    /// §S2-1 adversarial-review fold (Codex F1, HIGH) — the sinks-first
    /// policy's cardinality trade, pinned as DELIBERATE: with overlapping
    /// mixed cores `{s, k1}` and `{s, k2}` (one source's broadcast opposing
    /// TWO caller frees), retaining the source costs TWO leaked sinks where
    /// the pre-S2-1 positional pick would have leaked the one source. The
    /// leak set is subset-minimal (phase 2 proves neither sink individually
    /// restorable while the source is retained) but not minimum-cardinality
    /// — D7's rationale: the source's Owning conversion is precision;
    /// leaked frees stay raw-pointer frees. Zero corpus rows changed under
    /// this policy (Phase-0 baseline sweep), so today the trade is
    /// fixture-only; if corpus data ever shows material sink-leak
    /// inflation, a cardinality-aware refinement is a stage-2 decision,
    /// not a drive-by.
    #[test]
    fn nbs2_mixed_fanout_prefers_source_over_two_sinks() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

// This fixture requires an unclassified contract to retain its mixed core.
unsafe extern "C" { fn retain_for_policy_fixture(x: *mut core::ffi::c_void); }
pub unsafe fn pass(x: *mut core::ffi::c_void) { retain_for_policy_fixture(x); }

pub unsafe fn source_side() -> *mut core::ffi::c_void {
    let m = unsafe { malloc(4) };
    unsafe { pass(m) };
    m
}

pub unsafe fn sink_side1(a1: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let b = a1;
    unsafe { pass(b) };
    unsafe { free(a1) };
    b
}

pub unsafe fn sink_side2(a2: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let b = a2;
    unsafe { pass(b) };
    unsafe { free(a2) };
    b
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let source_side = function_by_name(&program, "source_side");
                let source_body = tcx
                    .mir_drops_elaborated_and_const_checked(source_side)
                    .borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("S2-1 fan-out emission should run");

                assert_eq!(selectors.sources().len(), 1);
                assert_eq!(selectors.sinks().len(), 2);
                let s = selectors.sources()[0].clone();
                let k1 = selectors.sinks()[0].clone();
                let k2 = selectors.sinks()[1].clone();
                let check = |set: &[&z3::ast::Bool]| {
                    kind_solver
                        .check_with_assumptions(&set.iter().map(|&b| b.clone()).collect::<Vec<_>>())
                };

                // The overlapping-core structure: the source ties with EACH
                // sink separately; the two sinks do not tie with each other.
                assert_eq!(check(&[&s, &k1]), SatResult::Unsat);
                assert_eq!(check(&[&s, &k2]), SatResult::Unsat);
                assert_eq!(check(&[&k1, &k2]), SatResult::Sat);
                assert_eq!(check(&[&s]), SatResult::Sat);
                assert_eq!(check(&[&k1]), SatResult::Sat);
                assert_eq!(check(&[&k2]), SatResult::Sat);

                // POLICY PIN: both sinks leak, the source is retained — a
                // 2-leak outcome preferred over the 1-leak source drop.
                let ((model, dropped), legacy_trace) = with_selector_trace(|| {
                    kind_solver
                        .model_kinds_relaxing_reporting(&selectors)
                        .expect("legacy relax loop must converge to SAT")
                });
                let ((hard_model, hard_dropped), hard_trace) = with_selector_trace(|| {
                    let hard = kind_solver.hard_loop_solver();
                    let relaxed = kind_solver
                        .relax_selectors_hard_reporting(&hard, &selectors)
                        .expect("hard relax loop must converge to SAT");
                    let dropped = relaxed.dropped().to_vec();
                    let model = kind_solver
                        .optimized_model_under(&relaxed)
                        .expect("hard decisions admit an optimized model");
                    (model, dropped)
                });
                assert_eq!(
                    selector_final_sets(&legacy_trace),
                    selector_final_sets(&hard_trace)
                );
                let sidecar = selector_trace_sidecar("mixed-fanout", &legacy_trace, &hard_trace);
                assert!(sidecar.contains("legacy-optimize"));
                assert!(sidecar.contains("plain-solver"));
                maybe_write_selector_trace_sidecar("mixed-fanout", &legacy_trace, &hard_trace);
                assert_eq!(
                    dropped_selector_set(&selectors, &hard_dropped),
                    dropped_selector_set(&selectors, &dropped)
                );
                assert_eq!(hard_model, model);
                assert_eq!(
                    dropped.len(),
                    2,
                    "the fan-out trade leaks both sinks (subset-minimal, not min-cardinality)"
                );
                assert!(
                    dropped.iter().all(|d| selectors.is_sink(d)),
                    "every leaked selector is a sink; the source is retained"
                );

                let m_local = call_destination(tcx, &source_body, "malloc");
                let m_slot = local_slot(&slots, source_side, m_local, 0);
                assert_eq!(
                    model.get(&m_slot),
                    Some(&SlotKind::Owning),
                    "the retained source must convert m to Owning"
                );
            },
        );
    }

    /// §S2-1 control — a PURE-SOURCE tie (the plan's control): two sources
    /// force OPPOSITE children of one copy-fork through two different callee
    /// broadcasts. `f_sink(m1)` forces `sigF.use`; `f_sink(b)` routes it into
    /// fork child `b_w1`. `g_sink(m2)` forces `sigG.use`; `g_sink(a)` routes
    /// it into the sibling `a_v1`. `¬(b_w1 ∧ a_v1)` makes `{s1, s2}` jointly
    /// infeasible while each alone is SAT — proved by the same check() triple.
    /// (Cross-side sink pairs tie too — the grave-sinks demand the same
    /// broadcasts — so the maximal retention is one whole SIDE: {s2, k_g}.)
    ///
    /// CONTROL PROPERTY: the relax outcome must be IDENTICAL before and after
    /// the mixed-tie fix — the F-side falls (earliest-positioned members drop
    /// first in both policies), G-side retained, m2 Owning, m1 Raw.
    #[test]
    fn nbs2_pure_source_tie_control_unchanged() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

unsafe fn f_sink(x: *mut core::ffi::c_void) {
    unsafe { free(x) };
}

unsafe fn g_sink(x: *mut core::ffi::c_void) {
    unsafe { free(x) };
}

pub unsafe fn ctrl2(a: *mut core::ffi::c_void) {
    let m1 = unsafe { malloc(4) };
    unsafe { f_sink(m1) };
    let m2 = unsafe { malloc(8) };
    unsafe { g_sink(m2) };
    let b = a;
    unsafe { f_sink(b) };
    unsafe { g_sink(a) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let ctrl = function_by_name(&program, "ctrl2");
                let body = tcx.mir_drops_elaborated_and_const_checked(ctrl).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("S2-1 control emission should run");

                assert_eq!(selectors.sources().len(), 2);
                assert_eq!(selectors.sinks().len(), 2);
                // Sources are emitted in statement order within `ctrl2`:
                // s1 = m1's malloc, s2 = m2's malloc. Verified structurally
                // below: the two sources must tie with EACH OTHER.
                let s1 = selectors.sources()[0].clone();
                let s2 = selectors.sources()[1].clone();
                let check = |set: &[&z3::ast::Bool]| {
                    kind_solver
                        .check_with_assumptions(&set.iter().map(|&b| b.clone()).collect::<Vec<_>>())
                };

                // THE PURE-SOURCE TIE PROOF: jointly infeasible, each alone SAT.
                assert_eq!(
                    check(&[&s1, &s2]),
                    SatResult::Unsat,
                    "{{s1, s2}} must be a genuine pure-source joint conflict"
                );
                assert_eq!(check(&[&s1]), SatResult::Sat, "s1 alone must be SAT");
                assert_eq!(check(&[&s2]), SatResult::Sat, "s2 alone must be SAT");

                // CONTROL: the relax outcome is side-shaped and identical
                // under both retention policies — the F-side (s1 and f_sink's
                // grave) is dropped, the G-side retained.
                let (model, dropped) = kind_solver
                    .model_kinds_relaxing_reporting(&selectors)
                    .expect("relax loop must converge to SAT");
                assert_eq!(
                    dropped.len(),
                    2,
                    "one whole side (source + its grave-sink) must leak; got {:?}",
                    dropped.len()
                );
                assert_eq!(
                    dropped.iter().filter(|d| selectors.is_sink(d)).count(),
                    1,
                    "the dropped side is one source plus one sink"
                );
                assert!(
                    dropped.iter().any(|d| d == &s1) && !dropped.iter().any(|d| d == &s2),
                    "positional within-class order is preserved: s1 (earliest) leaks, s2 survives"
                );

                // Retained side converts: m2 Owning; leaked side does not: m1
                // non-Owning (Raw under NB0's eager ¬ref on source slots).
                let m1_local = call_nth_destination(tcx, &body, "malloc", 0);
                let m2_local = call_nth_destination(tcx, &body, "malloc", 1);
                let m1_slot = local_slot(&slots, ctrl, m1_local, 0);
                let m2_slot = local_slot(&slots, ctrl, m2_local, 0);
                assert_eq!(
                    model.get(&m2_slot),
                    Some(&SlotKind::Owning),
                    "the retained source must stay Owning"
                );
                assert_ne!(
                    model.get(&m1_slot),
                    Some(&SlotKind::Owning),
                    "the leaked source must not be Owning"
                );
            },
        );
    }

    /// §S2-1 control — a PURE-SINK tie (alias double-free): within-class
    /// retention must keep the pre-change positional behavior, byte-identical
    /// before/after the mixed-tie fix. `b = a` forks `a_v1 = b_w1 + a_v2`;
    /// the two frees pin the sibling children, so `{k1, k2}` is jointly
    /// infeasible while each free alone is satisfiable — and the source `s`
    /// allies with EITHER free (it feeds whichever consumes). The loop drops
    /// the earliest-positioned sink (k1), retains the source and k2, and
    /// phase-2 restores any spuriously dropped selector.
    ///
    /// (The plan asked for a pure-SOURCE tie control; that shape is
    /// structurally impossible in the current fabric — sources only GIVE, and
    /// two gives never clash; opposition needs a taker. Recorded as an S2-1
    /// finding in the task doc. The sink/sink tie is the constructible
    /// within-class control.)
    #[test]
    fn nbs2_pure_sink_tie_control_positional_unchanged() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn ctrl() {
    let a = unsafe { malloc(8) };
    let b = a;
    unsafe { free(a) };
    unsafe { free(b) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let ctrl = function_by_name(&program, "ctrl");
                let body = tcx.mir_drops_elaborated_and_const_checked(ctrl).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("S2-1 control emission should run");

                assert_eq!(selectors.sources().len(), 1);
                assert_eq!(selectors.sinks().len(), 2);
                let s = selectors.sources()[0].clone();
                let k1 = selectors.sinks()[0].clone();
                let k2 = selectors.sinks()[1].clone();

                // Tie proof, sink/sink: jointly infeasible, each side SAT,
                // and the source allies with either free.
                assert_eq!(
                    kind_solver.check_with_assumptions(&[k1.clone(), k2.clone()]),
                    SatResult::Unsat
                );
                assert_eq!(
                    kind_solver.check_with_assumptions(&[k1.clone()]),
                    SatResult::Sat
                );
                assert_eq!(
                    kind_solver.check_with_assumptions(&[k2.clone()]),
                    SatResult::Sat
                );
                assert_eq!(
                    kind_solver.check_with_assumptions(&[s.clone(), k1.clone()]),
                    SatResult::Sat
                );
                assert_eq!(
                    kind_solver.check_with_assumptions(&[s.clone(), k2.clone()]),
                    SatResult::Sat
                );

                // Within-class positional retention: exactly one sink leaked
                // (the earliest-positioned, k1), source retained, a Owning.
                let (model, dropped) = kind_solver
                    .model_kinds_relaxing_reporting(&selectors)
                    .expect("relax loop must converge to SAT");
                assert_eq!(dropped.len(), 1, "minimal leak set is one free");
                assert!(
                    selectors.is_sink(&dropped[0]),
                    "a pure-sink tie must leak a sink, never the source"
                );
                assert!(
                    dropped[0] == k1,
                    "within-class tie-break stays positional: the earliest sink leaks"
                );

                let a_local = call_destination(tcx, &body, "malloc");
                let a_slot = local_slot(&slots, ctrl, a_local, 0);
                assert_eq!(
                    model.get(&a_slot),
                    Some(&SlotKind::Owning),
                    "the source must stay retained (Owning) on a pure-sink tie"
                );
            },
        );
    }

    /// §NB1 test (a) — the TRANSITIVE gap. `safe(x) ≡ ¬raw(x)`. Accessing the
    /// deepest slot of a pointer chain through its shallower layers asserts,
    /// per site, `safe(deep) ⇒ safe(each traversed layer)`; so no model may
    /// leave a SAFE deep slot over a RAW shallow one — including the
    /// `raw@0 / ref@1 / own@2` inversion that the structural `i1-adjacency`
    /// (`¬(raw ∧ own)` on adjacent pairs only) PERMITS for the `ref`-deep and
    /// non-adjacent cases. Probed directly on the emitted clause: with the
    /// per-site walk, assuming `raw(ppp@0) ∧ own(ppp@2)` is UNSAT (the deep
    /// safe slot forces the shallow layer safe); the all-raw chain stays SAT
    /// (non-vacuity — the clause only forbids safe-over-raw, never forces a
    /// kind). Under the pre-NB1 `chain`/`off` behavior no such clause exists,
    /// so the inversion is satisfiable — this fixture fails until the walk lands.
    #[test]
    fn nb1_transitive_gap_rejected() {
        run_compiler(
            r#"
pub unsafe fn chain(ppp: *mut *mut *mut i32) {
    let _y = **ppp;
}
"#,
            |tcx| {
                let build = |tcx| {
                    let program = collect_program(tcx);
                    let f = function_by_name(&program, "chain");
                    let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                    let slots = CrateSlots::build(&program);
                    let solver = KindSolver::new(&slots);
                    add_coherence(&solver, &slots, f, &body);
                    let ppp = local_by_var_name(tcx, f, "ppp");
                    let s0 = local_slot(&slots, f, ppp, 0);
                    let s2 = local_slot(&slots, f, ppp, 2);
                    (solver, s0, s2)
                };

                // safe deep (own@2) over raw shallow (raw@0) is forbidden.
                let (solver, s0, s2) = build(tcx);
                solver.assume(s0, SlotKind::Raw);
                solver.assume(s2, SlotKind::Owning);
                assert_eq!(
                    solver.check(),
                    SatResult::Unsat,
                    "per-site SAFE-MONO must forbid a safe deep slot over a raw shallow layer"
                );

                // Non-vacuity: an all-raw chain is fine (the clause forbids only
                // safe-over-raw, it never forces a kind).
                let (solver, s0, s2) = build(tcx);
                solver.assume(s0, SlotKind::Raw);
                solver.assume(s2, SlotKind::Raw);
                assert_eq!(
                    solver.check(),
                    SatResult::Sat,
                    "an all-raw chain must stay satisfiable"
                );
            },
        );
    }

    /// §NB1 test (b) — the FIELD boundary the structural `i1-adjacency` cannot
    /// reach. A struct field accessed through a raw parent pointer at a site
    /// (`(*s).f`) is a per-site layer traversal: `safe(field.f@0) ⇒ safe(s@0)`.
    /// So an `Owning`-eligible field cannot stay safe when read through a raw
    /// parent. Probed: assuming `raw(s@0) ∧ ref(field.f@0)` is UNSAT with the
    /// walk (a safe field over a raw parent is forbidden); `raw(s@0) ∧
    /// raw(field.f@0)` stays SAT. The structural adjacency relates only
    /// same-owner slots within one universe, so no `chain`/`off` clause spans
    /// the Local→Field boundary — this fixture fails until the walk lands.
    #[test]
    fn nb1_raw_parent_field_site_demotes() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub f: *mut i32,
}

pub unsafe fn g(s: *mut S) {
    let _y = (*s).f;
}
"#,
            |tcx| {
                let build = |tcx| {
                    let program = collect_program(tcx);
                    let f = function_by_name(&program, "g");
                    let s_did = struct_by_name(&program, "S");
                    let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                    let slots = CrateSlots::build(&program);
                    let solver = KindSolver::new(&slots);
                    add_coherence(&solver, &slots, f, &body);
                    let s = local_by_var_name(tcx, f, "s");
                    let parent = local_slot(&slots, f, s, 0);
                    let field_id = slots
                        .field_slots
                        .slot_for_field_depth(
                            StructFieldSlot {
                                struct_did: s_did,
                                field_index: 0,
                            },
                            0,
                        )
                        .expect("field f depth-0 slot");
                    (solver, parent, SlotRef::Field(field_id))
                };

                // safe field (ref) over raw parent is forbidden.
                let (solver, parent, field) = build(tcx);
                solver.assume(parent, SlotKind::Raw);
                solver.assume(field, SlotKind::Ref);
                assert_eq!(
                    solver.check(),
                    SatResult::Unsat,
                    "per-site SAFE-MONO must demote a field read through a raw parent pointer"
                );

                // Non-vacuity: a raw field over a raw parent is fine.
                let (solver, parent, field) = build(tcx);
                solver.assume(parent, SlotKind::Raw);
                solver.assume(field, SlotKind::Raw);
                assert_eq!(
                    solver.check(),
                    SatResult::Sat,
                    "a raw field over a raw parent must stay satisfiable"
                );
            },
        );
    }

    /// §NB1 adversarial-review fold (Codex, 2026-07-10) — a pure WRITE/overwrite
    /// destination is NOT a SAFE-MONO site. `(*s).f = malloc()` writes THROUGH
    /// the parent `s` but does not dereference the field's OLD value as a
    /// reference, so this site must not couple the (crate-wide) field kind to
    /// the parent pointer's kind. Contrast `nb1_raw_parent_field_site_demotes`,
    /// where the field is READ through the parent. The field may therefore be
    /// `Owning` even when the parent is `Raw`: `raw(s@0) ∧ own(field.f@0)` must
    /// stay SAT (the store LHS emits no clause). Pre-fold, the walk emitted the
    /// clause for the store LHS too, spuriously coupling the field to every
    /// parent pointer and over-demoting on the corpus. SAFE-MONO is heuristic
    /// pruning — soundness is carried by the acceptance replay, not this clause.
    #[test]
    fn nb1_write_dest_does_not_couple_field_to_parent() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct S {
    pub f: *mut core::ffi::c_void,
}

pub unsafe fn stash(s: *mut S) {
    (*s).f = malloc(4);
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "stash");
                let s_did = struct_by_name(&program, "S");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let solver = KindSolver::new(&slots);
                add_coherence(&solver, &slots, f, &body);
                let s = local_by_var_name(tcx, f, "s");
                let parent = local_slot(&slots, f, s, 0);
                let field_id = slots
                    .field_slots
                    .slot_for_field_depth(
                        StructFieldSlot {
                            struct_did: s_did,
                            field_index: 0,
                        },
                        0,
                    )
                    .expect("field f depth-0 slot");
                let field = SlotRef::Field(field_id);

                solver.assume(parent, SlotKind::Raw);
                solver.assume(field, SlotKind::Owning);
                assert_eq!(
                    solver.check(),
                    SatResult::Sat,
                    "a store destination must not couple the field kind to the parent pointer"
                );
            },
        );
    }

    /// §NB2 — mutability hard facts, the shared-read WIN (requirement #2, coexistence).
    /// Two aliasing reborrows of one base that are only READ settle Foster `Imm`. Under
    /// fact-driven mutability, `borrow::invalidates` skips their immutable loans
    /// (`invalidates.rs:73`), so the aliasing produces no conflict and every slot stays `Ref`.
    /// The control prong (forced-mut, pre-NB2) treats the same reads as mutable and demotes
    /// >=1 slot — the two-prong design proves the mutability facts are the *sole* cause of the
    /// win (identical program, only the oracle differs). Structurally this is the `bb0`
    /// conflict with reads in place of writes.
    ///
    /// Liveness note: `errors = loan_liveness ∩ invalidates` (`errors.rs:8`), and `is_mutable`
    /// is read ONLY in `invalidates` — so an immutable loan still fully participates in
    /// liveness; only its invalidation is suppressed. That participation is structural (no
    /// fixture can break it), which is why this pair pins invalidation, not liveness.
    #[test]
    fn nb2_two_shared_reads_both_ref() {
        run_compiler(
            r#"
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut r1 = p;
    let mut r2 = r1;
    let mut q = r1;
    let a = *q;
    let b = *r1;
    let c = *r2;
    let d = *p;
    a + b + c + d
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let slot_of =
                    |name: &str| local_slot(&slots, f, local_by_var_name(tcx, f, name), 0);
                let names = ["p", "r1", "r2", "q"];

                // Control: forced-mutable (pre-NB2) — the aliasing reads are treated as
                // mutable, so the CEGAR loop demotes >=1 slot off Ref.
                let model_ctrl = {
                    let solver = KindSolver::new(&slots);
                    let (_s, selectors) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("control emission");
                    add_coherence(&solver, &slots, f, &body);
                    verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                        .expect("control accepts")
                };
                let ctrl_ref = names
                    .iter()
                    .filter(|n| model_ctrl.get(&slot_of(n)) == Some(&SlotKind::Ref))
                    .count();
                assert!(
                    ctrl_ref < names.len(),
                    "forced-mut control: aliasing reads must demote >=1 slot; all stayed Ref"
                );

                // Treatment: fact-driven — all reads ⇒ Foster Imm ⇒ immutable loans skipped ⇒
                // no conflict ⇒ every slot stays Ref.
                let facts = MutFacts::from_program(&program);
                let model_fact = {
                    let solver = KindSolver::new(&slots);
                    let (_s, selectors) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("treatment emission");
                    add_coherence(&solver, &slots, f, &body);
                    verify_to_fixpoint(&program, &slots, &solver, &selectors, &facts)
                        .expect("treatment accepts")
                };
                for n in names {
                    assert_eq!(
                        model_fact.get(&slot_of(n)),
                        Some(&SlotKind::Ref),
                        "fact-driven: `{n}` stays Ref (shared read, immutable loan skipped)"
                    );
                }
            },
        );
    }

    /// §NB2 — the write direction (requirement #2, "killed by a write"). A pointer written
    /// through ITSELF is Foster `Mut` (Foster is precise for the same-pointer case), so its
    /// loan is NOT skipped: the aliasing conflict survives fact-driven mutability exactly as
    /// under forced-mut, and >=1 slot is still demoted. Companion to
    /// `nb2_two_shared_reads_both_ref` (reads relax, writes do not). The program is the `bb0`
    /// conflict verbatim. (The cross-alias case — a cell written through a *sibling* while a
    /// read-only view stays `Imm` — is the separate S2-6 gap; see
    /// `nb2_cross_alias_write_uncaught_witness`.)
    #[test]
    fn nb2_written_base_still_conflicts() {
        run_compiler(
            r#"
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut r1 = p;
    let mut r2 = r1;
    let mut q = r1;
    *q = 1;
    *r1 = 2;
    *r2 = 3;
    *p = 4;
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let slot_of =
                    |name: &str| local_slot(&slots, f, local_by_var_name(tcx, f, name), 0);
                let names = ["p", "r1", "r2", "q"];

                let facts = MutFacts::from_program(&program);
                let model = {
                    let solver = KindSolver::new(&slots);
                    let (_s, selectors) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("emission");
                    add_coherence(&solver, &slots, f, &body);
                    verify_to_fixpoint(&program, &slots, &solver, &selectors, &facts)
                        .expect("accepts")
                };
                let ref_count = names
                    .iter()
                    .filter(|n| model.get(&slot_of(n)) == Some(&SlotKind::Ref))
                    .count();
                assert!(
                    ref_count < names.len(),
                    "fact-driven: written bases stay Mut, so the conflict survives (>=1 demoted)"
                );
            },
        );
    }

    /// §NB2 S2-6 witness — the CONFIRMED cross-alias immutable-loan invalidation gap.
    ///
    /// Rebuilt 2026-07-10 after a Codex adversarial review DISPROVED the earlier "the coherence
    /// equate-closure is the acceptance-level guard" claim. The earlier program was a *direct*
    /// copy cluster (`let xp = p; let z = xp; let b = p; *b = 5;`): p/xp/z/b are one coherence
    /// cluster, a mutable p/b conflict demotes the whole cluster in BOTH modes, so it was
    /// non-causal (the skip changed nothing — even the round-0 conflict edges were byte-identical
    /// across modes) and proved no gap. The equate-closure only unifies DIRECT copy clusters; it
    /// does NOT model interprocedural aliases.
    ///
    /// Here `x = id(p)` aliases `p` through a CALL RETURN, which coherence does not connect, so
    /// x/z/q form their own cluster carrying ONLY immutable loans (Foster marks x/z/q `Imm` —
    /// verified below — they are never written THROUGH; the write is via the mutable sibling `b`,
    /// `b = p`). `*b = 5` demotes the p/b cluster but NOT x/z/q. Result — **mode-differential**
    /// (the causal proof the skip runs, which the old witness lacked):
    ///   - forced-mut (skip OFF): x/z/q = `Raw` (their loans participate; the write demotes them);
    ///   - fact-mut  (skip ON):  x/z/q = `Ref` in STATE-2 — a shared `&T` aliasing the written cell;
    ///     NB4-R (STATE-3, 2026-07-15) now routes the write to their loan, so this is `Raw` too (the
    ///     mode differential collapses).
    ///
    /// In STATE-2 the fact-mode `Ref` was an **acceptance-level unsoundness REAL TODAY** (not merely
    /// "if flow-sensitivity is relaxed"), production-PARITY (production's own
    /// `borrow::mutable_references_no_guarantee` promotes x and q to shared `&T` on this exact program
    /// — verified), guarded ONLY by the **§8 codegen guardrail** (BO output unconsumed by codegen).
    /// NB4-R (STATE-3) removes that unsoundness for this shape by demoting x/z/q to `Raw` at analysis
    /// time — §8 is no longer the sole guard here.
    ///
    /// **NB3-3b finding (2026-07-10): write-aware invalidation does NOT close THIS case.** 3b
    /// restores the read/write distinction so an immutable loan is skipped for reads only. But the
    /// cross-alias write here is `*b = 5` with `b = p` (a copy), and `local_map.row(b)` is EMPTY —
    /// the loan is on `(*x)`/`(*p)`, not on `b`, so the write invalidates nothing. Place-conflict is
    /// structurally blind to the call-return alias (`x = id(p)`); write-awareness cannot route the
    /// write's invalidation of p's loan to x's loan. The forced-mut demotion of x/z/q rides the
    /// READ pointer-copies `z = x`/`q = x` (verified: `INSERT rw=Read borrowed=(*x)` at those
    /// points), which the read-skip soundly preserves. Closing this needed **routing** (the router is
    /// NB4-R, place-based). **NB4-R HAS LANDED (2026-07-15): this now flips to `Raw` — see the in-test
    /// STATE-3 assertions.** (The SOUND-skip proof is `nb2_two_shared_reads_both_ref`; this was its
    /// UNSOUND-skip counterpart until NB4-R.)
    ///
    /// **Decision B (2026-07-11):** the 3b write-aware fix was measured **corpus-inert** — 0
    /// shared-ref demotions across all 19 accepts (same-base immutable-written cases don't arise
    /// from real Foster facts: a written-through pointer is Foster `Mut`, so its loan is never
    /// skip-eligible). Write-awareness is inert *without* a router that makes the cross-alias write
    /// reach the aliased loan.
    ///
    /// **STATE-3: S2-6 CLOSED by NB4-R (2026-07-15).** The write's non-reach was diagnosed by dump:
    /// `*b=5` invalidates only b's own loan (`row(b)` keyed under b, empty of the loan x/z/q require,
    /// which is keyed under p). Three routers were refuted BEFORE NB4-R, each by a dump — recorded so
    /// none is re-attempted:
    ///   • 3c origins (subset edges) — invalidation is place-based, subset never changes a write's reach;
    ///   • `tree_borrow_local` copy-groups — singleton at round 0 (only unioned during demotion replay);
    ///   • `Local`-based issues→borrowed re-basing (NB4-4b `ffd90100`) — fixture-level closure but on
    ///     the corpus it CRASHED 3 programs (re-basing a projection across incompatible types) and
    ///     over-demoted −17.7% (offset conflation). REVERTED.
    /// WA is also refuted for this witness: the loan x/z/q require has base `p` which is Foster `Mut`
    /// (never skip-eligible) — routing alone flips it. NB4-R is the router that landed: **place-based
    /// cross-alias routing (before NB5) — compose-onto-`borrowed` algebra with a type-check + whole-cell
    /// fallback (no re-basing crash), `offset` excluded (no −17.7%), PRE-order bounded walk.** x/z/q
    /// now settle `Raw` in both mut modes; §8 is no longer the sole guard for this shape. (Corpus
    /// impact is measured at the NB4-R sweep gate.)
    #[test]
    fn nb2_cross_alias_write_uncaught_witness() {
        run_compiler(
            r#"
#[inline(never)]
unsafe fn id(mut p: *mut i32) -> *mut i32 { p }
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut b = p;
    let mut x = id(p);
    let mut z = x;
    let mut q = x;
    let r0 = *z + *q;
    *b = 5;
    let r1 = *z;
    r0 + r1
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let slot_of =
                    |name: &str| local_slot(&slots, f, local_by_var_name(tcx, f, name), 0);
                let local_of = |name: &str| local_by_var_name(tcx, f, name);

                let facts = MutFacts::from_program(&program);
                // x/z/q are read-only views (never written THROUGH) ⇒ Foster `Imm` ⇒ their loans
                // are skip-eligible at `invalidates.rs:73`. These ARE the real loan bases — the
                // point the earlier witness got wrong (it asserted a copy, not the loan base).
                for name in ["x", "z", "q"] {
                    assert!(
                        !facts.is_mutable(f, local_of(name)),
                        "`{name}` is a read-only view ⇒ Foster Imm ⇒ its loan is skip-eligible"
                    );
                }
                // `b` (= p) writes the cell x/z/q alias via `id` ⇒ Foster `Mut` (the writer).
                assert!(
                    facts.is_mutable(f, local_of("b")),
                    "`b` writes the aliased cell ⇒ Foster Mut (the cross-alias writer)"
                );

                let kind_of = |name: &str, mf_true: bool| {
                    let solver = KindSolver::new(&slots);
                    let (_s, selectors) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("emission");
                    add_coherence(&solver, &slots, f, &body);
                    let sid = slot_of(name);
                    if mf_true {
                        verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                            .expect("accepts")
                            .get(&sid)
                            .copied()
                    } else {
                        verify_to_fixpoint(&program, &slots, &solver, &selectors, &facts)
                            .expect("accepts")
                            .get(&sid)
                            .copied()
                    }
                };

                // §NB4-R STATE-3 (S2-6 CLOSED): place-based cross-alias routing lands and flips this
                // witness. `*b = 5` now ROUTES through `b`'s issued loan (`b = p`, borrowed=(*p)) to
                // `row(p)`, where the loan x/z/q require (the id-arg copy's main loan, borrowed=(*p),
                // keyed under `p`) lives — and invalidates it. x/z/q were the CALL-RETURN alias the
                // pre-routing engine's `row(b)`-empty lookup was blind to (state-2). They now settle
                // `Raw` in BOTH mut modes — the routed demotion does not depend on the mut-fact skip
                // (`p` is a `Mut` base, never skip-eligible) — so the state-2 mode differential
                // collapses. This is the executable proof that NB4-R closed S2-6.
                for name in ["x", "z", "q"] {
                    assert_eq!(
                        kind_of(name, true),
                        Some(SlotKind::Raw),
                        "forced-mut: `{name}`'s loan participates ⇒ Raw (unchanged from state-2)"
                    );
                    assert_eq!(
                        kind_of(name, false),
                        Some(SlotKind::Raw),
                        "fact-mut: `{name}` is now `Raw` — NB4-R routing reaches the call-return alias's \
                         loan on `(*p)` via `b`'s issued loan. S2-6 CLOSED here (was `Ref` in state-2)."
                    );
                }

                // The edge set is no longer a lone self-edge: routing adds a genuine cross-slot
                // conflict that demotes the view `z` (the CEGAR representative of the x/z/q alias
                // group) via a NON-self issuer — the concrete S2-6 closure witness. (The `b` self-edge
                // from `*b=5` on b's own cell persists alongside it.)
                let edges = revalidate_replaying(&program, &slots, |_| true, |_| false, &facts);
                let z_slot = slot_of("z");
                let fn_edges = edges.get(&f).map(Vec::as_slice).unwrap_or(&[]);
                assert!(
                    fn_edges
                        .iter()
                        .any(|e| e.requirers == vec![z_slot] && e.issuer != Some(z_slot)),
                    "state-3: a routed cross-alias edge must demote the view `z` via a non-self issuer \
                     (the S2-6 closure). Edges: {fn_edges:?}"
                );
            },
        );
    }

    /// §NB4-4c SCOPE GUARD: the demotion set is the interprocedural SIGNATURE boundary only
    /// (args/returns/fields, via `to_summary`), NEVER internal locals. An internal `Copy`/`Move` of an
    /// addr-of-local / `.offset` / plain / opaque-result pointer is body-level unknown but is NOT a
    /// signature slot, so it is not demoted — no promotion coverage is lost on intermediates. (This
    /// refutes the "source-less copies get hard `¬ref`" concern: those are internal locals.)
    #[test]
    fn nb4_4c_demotion_is_signature_boundary_only() {
        let cases: &[(&str, &str, &str)] = &[
            (
                "addrof_copy",
                "q",
                "fn f() { let mut x = 0i32; let p = &raw mut x; let q = p; unsafe { *q = 1; } }",
            ),
            (
                "offset_copy",
                "q",
                "unsafe fn f(p: *mut i32) { let r = p.offset(1); let q = r; let _ = q; }",
            ),
            (
                "plain_copy",
                "q",
                "unsafe fn f(p: *mut i32) { let q = p; let _ = q; }",
            ),
            (
                "opaque_result_local",
                "q",
                "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
              unsafe fn f(p: *mut i32) { let q = op(p); let _ = q; }",
            ),
        ];
        for (label, var, code) in cases {
            run_compiler(code, |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let set = collect_no_borrow_origin_slots(&origins, &slots);
                let local = local_by_var_name(tcx, f, var);
                let s0 = slots
                    .fn_local_slots
                    .get(&f)
                    .and_then(|u| u.slot_for_local_depth(local, 0))
                    .map(|id| SlotRef::Local(f, id));
                assert!(
                    !s0.map(|s| set.contains(&s)).unwrap_or(false),
                    "{label}: an internal local `{var}` must NOT be demoted (signature-boundary only)"
                );
            });
        }
    }

    /// §NB4-4c MARKER (§8-guarded — the Codex-F1 re-review residue, 2026-07-17). `summary.unknown`
    /// is a MAY-set, not an exclusive no-origin partition: a signature RETURN can carry BOTH a
    /// modeled borrow origin (`q = p`) AND a stale opaque may-definition (`q = op(p)`) that a later
    /// overwrite kills. Because the opaque def still MAY-reaches, the return lands in
    /// `collect_no_borrow_origin_slots`; the monotone `¬ref` demotes it, and copy-coherence drags the
    /// modeled-origin param `p` and the copy `q` to `Raw` too — COLLATERAL over-demotion of slots that
    /// have a real borrow origin. This is the strong-form failure of the NB4-4c "F1 refutation": the
    /// demotion is signature-boundary for DIRECT membership (an internal-only local is never in the
    /// set — see `nb4_4c_demotion_is_signature_boundary_only`), but a modeled-origin SIGNATURE slot
    /// CAN be, and coherence then spreads it.
    ///
    /// SOUNDNESS: this is COMPLETENESS-CLASS (precision), NOT unsoundness — `Ref → Raw` is the
    /// conservative direction (Raw is always memory-safe), the model still ACCEPTS, and BO output is
    /// unconsumed by codegen (§8). It FLIPS (`p` back to `Ref`, return out of the set) when the
    /// deferred "definitely-overwritten vs may-reach unknown-def" distinction lands (one bucket, gate
    /// = effect-row + opaque-interaction detection). Tripwire, not a regression.
    #[test]
    fn nb4_4c_marker_coherence_collateral_demotes_modeled_origin() {
        use rustc_middle::mir::RETURN_PLACE;
        // Control: pure modeled copy — return has ONLY a modeled origin, stays Ref (baseline).
        run_compiler(
            "unsafe fn f(p: *mut i32) -> *mut i32 { let q = p; q }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                let p0 = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
                assert!(
                    !collect_no_borrow_origin_slots(&origins, &slots).contains(&ret),
                    "control: a pure modeled-copy return must NOT be no-borrow-origin"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&p0),
                    Some(&SlotKind::Ref),
                    "control: modeled-origin p stays Ref"
                );
            },
        );
        // Mixed: q first opaque, then overwritten with modeled p, then returned. TODAY: the return is
        // in the set (may-set over-inclusion) and coherence collaterally demotes p to Raw.
        run_compiler(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; q }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                let p0 = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
                assert!(
                    collect_no_borrow_origin_slots(&origins, &slots).contains(&ret),
                    "TODAY: a modeled-origin return with a stale opaque may-def IS over-included \
                     (may-set); this flips when the overwrite-kill distinction lands"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&p0),
                    Some(&SlotKind::Raw),
                    "TODAY: coherence collaterally demotes the modeled-origin param p to Raw \
                     (conservative, §8-guarded); flips to Ref when the deferred fix lands"
                );
            },
        );
    }

    /// §NB4-4c-Q (Codex confirming pass, 2026-07-17): PIN the restored-output-param OUTCOME directly on
    /// `compute_origins` — the collector-output test (`overincl` 0/0) alone does not prove it. Records
    /// only the OBSERVED signature-level fact: the restore-after-opaque shape yields exactly one unknown
    /// slot and ZERO summary subset edges, so neither over-inclusion predicate can see it. The MECHANISM
    /// is deliberately NOT claimed: the earlier "poisoning drops the value-restore edge" explanation was
    /// refuted (`mark_unknown` only sets a bit; the store IS recorded), and a body-level
    /// `arg1@1 → old → arg1@1` path exists whose signature projection threads the internal local `old`.
    /// The precise reason the SIGNATURE summary carries no self-loop is untraced and belongs to item-4
    /// (the flow-sensitive analysis that will size this component-2 residual). This test guards the
    /// outcome the gate relies on (both predicates miss ⇒ summary-invisible-at-signature-level).
    #[test]
    fn nb4_4c_q_restored_summary_invisible() {
        run_compiler(
            "unsafe extern \"C\" { fn op() -> *mut i32; } \
             unsafe fn f(out: *mut *mut i32) { let old = *out; *out = op(); *out = old; }",
            |tcx| {
                let program = collect_program(tcx);
                let origins = compute_origins(&program);
                let f = function_by_name(&program, "f");
                let sum = &origins[&f];
                assert_eq!(
                    sum.unknown.count(),
                    1,
                    "restored: exactly one unknown signature slot"
                );
                let edges: usize = sum
                    .subset
                    .rows()
                    .map(|r| sum.subset.row(r).map_or(0, |b| b.iter().count()))
                    .sum();
                assert_eq!(
                    edges, 0,
                    "restored: ZERO summary subset edges — both over-inclusion predicates miss it \
                     (the summary-invisible OUTCOME; mechanism untraced, item-4's to pin)"
                );
            },
        );
    }

    /// §NB5-Z (2026-07-17): z3 determinism regression-guard. Two independent in-process BO solves of
    /// the same fixture must produce byte-identical models. This holds INHERENTLY in-process: z3 0.19's
    /// default `Context` is a `thread_local!` built ONCE per thread (`Context::new(&Config::new())`) and
    /// cloned/reused for the thread's life, so both solves share one random seed. So this is a
    /// determinism REGRESSION-GUARD, not a "fixed nondeterminism" RED (NB5-Z rider, correction #3). The
    /// z3 seed pin's real value is the cross-VERSION contract — the sweep-worker `set_global_param` plus
    /// the `z3_full_version` stamp — which a single-version suite cannot exercise, so this test does not
    /// claim to. It locks in-process determinism so a future solver/z3 change cannot silently reintroduce
    /// run-to-run drift.
    #[test]
    fn nb5z_solve_run_to_run_deterministic() {
        run_compiler(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; q }",
            |tcx| {
                let solve = || {
                    let program = collect_program(tcx);
                    let f = function_by_name(&program, "f");
                    let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                    let slots = CrateSlots::build(&program);
                    let crate_ctxt = CrateCtxt::new(&program);
                    let facts = MutFacts::from_program(&program);
                    let solver = KindSolver::new(&slots);
                    let (_s, sel) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("emission");
                    add_coherence(&solver, &slots, f, &body);
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts")
                };
                let m1 = solve();
                let m2 = solve();
                assert_eq!(
                    m1, m2,
                    "NB5-Z: two independent in-process solves must be identical (determinism guard)"
                );
            },
        );
    }

    /// §NB4-4c-Q RED (item-4 sizing gate, 2026-07-17): the coherence-collateral measurement, validated
    /// against the INDEPENDENT multi-agent derivation (user ruling 2026-07-17). Exercises the EXACT
    /// harness code (`bo_c1::measure_collateral`) the corpus sweep runs.
    ///
    /// GRANULARITY (user-ruled MIR-slot-level 2026-07-17): the collateral is measured in the `n_ref` /
    /// `n_ref_d0` metric's own units — MIR SLOTS, not source variables. The agents' source-variable
    /// derivation (Sh1=3, Sh3=4) is right at its granularity; the metric adds the coherence-equated MIR
    /// COPY-TEMPS (`_3` the `op(p)` arg copy, `_4` the call-result temp → +2 on copy-chain shapes). The
    /// gate ratio's denominator (corpus `n_ref_d0`) counts these temps too, so the ratio is honest — but
    /// per-program outlier inspection must remember temps inflate the raw copy-chain counts. Sh4 has no
    /// +2 because the depth-0 field-store equate skip (`coherence.rs:45-47`) blocks the drag.
    #[test]
    fn nb4_4c_q_collateral_shapes() {
        fn measure(code: &str) -> crate::bo_c1::CollateralMeasurement {
            let mut out = None;
            run_compiler(code, |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let mut_facts = MutFacts::from_program(&program);
                out = Some(crate::bo_c1::measure_collateral(
                    &program, &slots, &origins, &mut_facts,
                ));
            });
            out.expect("run_compiler ran the callback")
        }
        // Shape 1: definitely-overwritten copy. coherence chain p≡q≡return (2 equates, 3 slots).
        let s1 = measure(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; q }",
        );
        assert_eq!(s1.status, "ok", "Shape 1: solved");
        assert_eq!(
            s1.overincl_mit, 1,
            "Shape 1: over-inclusion (mitigated) = 1 (the return)"
        );
        // MIR-slot-level = source view (3: p,q,return) + arg/result copy-temps (2: _3,_4) = 5.
        assert_eq!(s1.collateral_mit, 5, "Shape 1: collateral = 5 (MIR slots)");
        assert_eq!(
            s1.collateral_upper, 5,
            "Shape 1: upper == mit (no restored/storage extra here)"
        );
        // Shape 3: 2-hop copy chain (+r=q). Drag SCALES with chain length: source view 4 + 2 temps = 6.
        let s3 = measure(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; let r = q; r }",
        );
        assert_eq!(s3.overincl_mit, 1, "Shape 3: over-inclusion = 1");
        assert_eq!(s3.collateral_mit, 6, "Shape 3: collateral = 6 (MIR slots)");
        // Shape 4: field store. coherence.rs:45-47 skips the depth-0 field-store equate → NO drag onto
        // p; field collateral shows in n_ref (=1) but is INVISIBLE in n_ref_d0 (=0).
        let s4 = measure(
            "#[repr(C)] pub struct S { pub g: *mut i32 } \
             unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(s: *mut S, p: *mut i32) { (*s).g = op(p); (*s).g = p; }",
        );
        assert_eq!(
            s4.overincl_mit, 1,
            "Shape 4: over-inclusion = 1 (the field)"
        );
        assert_eq!(s4.collateral_mit, 1, "Shape 4: collateral = 1 (n_ref)");
        assert_eq!(
            s4.collateral_d0_mit, 0,
            "Shape 4: collateral_d0 = 0 (field slots are invisible at depth-0)"
        );
        // Shape 2: branch-join. Predicate FIRES identically to Shape 1 (flow-insensitive), but the
        // demotion is LEGITIMATE — MINUS un-demoting it reinstates an unsound Ref. THIS IS THE PROOF
        // that MINUS is MEASUREMENT-ONLY and must never ship; item-4's definitely-overwritten kill
        // would NOT fire here.
        let s2 = measure(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32, c: bool) -> *mut i32 { let q = if c { op(p) } else { p }; q }",
        );
        assert_eq!(
            s2.overincl_mit, 1,
            "Shape 2: predicate FIRES (measurement-only; MINUS must not ship)"
        );
        assert_eq!(
            s2.collateral_mit, 4,
            "Shape 2: collateral = 4 (MIR slots). MINUS un-demoting this is UNSOUND — the `op(p)` branch \
             can return opaque memory at runtime; the shippable item-4 kill would NOT fire on a branch-join."
        );
        // SECOND measurement-only witness (the "_4 tell", user-noted 2026-07-17): in Shape 1 the flipping
        // set includes `_4`, the OPAQUE-RESULT temp — under MINUS it becomes `Ref`, which is itself
        // unsound. So even the direct copy shape carries an unsound-under-MINUS slot; MINUS is a sizing
        // measurement only, never a shippable demotion set (Shape 2 is the other witness).
        // Counterexample (amendment 1): the storage-alias false positive. `&raw mut p` makes the return
        // pointee alias `p`'s storage — a SYMMETRIC subset edge whose true (opaque) source is filtered
        // out of `unknown`, so RAW fires but MITIGATED (reverse-edge discard) does NOT. Guards the
        // predicate against storage-edge inflation.
        let cx = measure(
            "unsafe extern \"C\" { fn op() -> *mut i32; } \
             unsafe fn f(mut p: *mut i32) -> *mut *mut i32 { p = op(); &raw mut p }",
        );
        assert!(
            cx.overincl_raw >= 1,
            "counterexample: RAW predicate fires via the storage edge"
        );
        assert_eq!(
            cx.overincl_mit, 0,
            "counterexample: MITIGATED predicate must NOT fire (symmetric storage edge discarded)"
        );
        assert!(
            cx.overincl_upper >= 1,
            "counterexample: UPPER bound DOES catch it (any incoming edge, self/symmetric-inclusive)"
        );
        // RESTORED-OUTPUT-PARAM (Codex F1 + confirming pass, 2026-07-17 — component-2 residual): `*out`
        // is restored to its original value after an opaque overwrite. OBSERVED signature-level outcome
        // (pinned by `nb4_4c_q_restored_summary_invisible`): exactly one unknown slot and ZERO summary
        // subset edges, so NEITHER the mitigated NOR the upper predicate sees it (both 0). The MECHANISM
        // is NOT claimed — the earlier "poisoning drops the store" explanation was REFUTED (`mark_unknown`
        // only sets a bit; the store is recorded); the reason the `arg1@1→old→arg1@1` body path leaves no
        // SIGNATURE self-loop is untraced and belongs to item-4. (Contrast the storage counterexample
        // above: an ADDRESS alias survives to `to_summary`, so `upper` DOES catch that — value-restore
        // vs address-alias.) The gate's `collateral_upper` sizes only the summary-VISIBLE collateral;
        // this component-2 case is UNMEASURED at the summary level (COMPLETENESS — test-only, unconsumed,
        // conservative Ref→Raw; NOT asserted empirically rare) and carried to item-4's RED scope.
        let restored = measure(
            "unsafe extern \"C\" { fn op() -> *mut i32; } \
             unsafe fn f(out: *mut *mut i32) { let old = *out; *out = op(); *out = old; }",
        );
        assert_eq!(
            restored.overincl_mit, 0,
            "restored: mitigated misses it (no summary edge)"
        );
        assert_eq!(
            restored.overincl_upper, 0,
            "restored: UPPER also misses it — SUMMARY-INVISIBLE (poisoning drops the value restore); \
             this component-2 residual is item-4 territory, not sizable at the summary level"
        );
        assert_eq!(
            restored.status, "no-oi",
            "restored: no summary over-inclusion → no solve"
        );
    }

    // ---- §NB4-4c — MAY-SUPPLY DEMOTION over the NO-BORROW-ORIGIN set ----
    //
    // These were the §NB3-3c-ii NB4-boundary markers. NB4-4c lands the **may-supply demotion**: a
    // monotone `¬ref` on every NO-BORROW-ORIGIN slot (`collect_no_borrow_origin_slots`, base
    // signature slots + struct fields), wired into `emit_crate_ownership_constraints` (was:
    // marker-tests-only).
    //
    // KEY CONCEPT (dump-corrected 2026-07-16): `summary.unknown` is "NO-BORROW-ORIGIN", NOT
    // "opaque-poisoned". A slot lands there when its value has no trackable *borrow* origin — an
    // opaque-callee RESULT, OR a freshly-`malloc`'d OWNED pointer. The `malloc_only` vs `malloc_opaque`
    // ablation proves `opaque(out)` adds nothing to the set. So `¬ref`-ONLY (not `¬ref ∧ ¬own`, which
    // over-demoted owned transfers — 9 tests): it is SELF-DISCRIMINATING — an owned slot keeps
    // `Owning` (source selector), an opaque RESULT loses `Ref` → `Raw`.
    //
    // Two markers pin DEFERRED §8-guarded hazards (flip when opaque-INTERACTION detection lands, one
    // bucket): `nb4_4c_marker_may_overwrite_owning_today` (owned out@1 an opaque callee may overwrite)
    // and `nb4_4c_marker_depth0_arg_retention_open` (depth-0 arg an opaque callee may retain). The
    // GREEN tests below encode the may-supply FIX (opaque results → Raw); the controls stay `Ref`.

    /// §NB4-4c (MAY-SUPPLY): an opaque-callee-RESULT RETURN is a NO-BORROW-ORIGIN slot and is DEMOTED
    /// to **`Raw`** by the monotone `¬ref` — the FFI-edition S2-6 fix (a shared `&T` over unknown
    /// C-state the callee may retain + write is now forbidden). No owning source reaches it (opacity
    /// breaks the link), so `¬ref` settles it `Raw`.
    #[test]
    fn nb4_4c_no_origin_return_demoted_to_raw() {
        run_compiler(
            "unsafe extern \"C\" { fn opaque_dup(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { opaque_dup(p) }",
            |tcx| {
                use rustc_middle::mir::RETURN_PLACE;
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                assert!(
                    collect_no_borrow_origin_slots(&origins, &slots).contains(&ret),
                    "opaque-return must be no-borrow-origin (the hazard the 4c demotion targets)"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&ret),
                    Some(&SlotKind::Raw),
                    "NB4-4c: no-borrow-origin may-supply return must be demoted to Raw (¬ref)"
                );
            },
        );
    }

    /// §NB4-4c (negative control + PURE-READ RESIDUAL): a KNOWN provenance-preserving callee
    /// (`.offset`) has a borrow origin, so its return legitimately stays `Ref` — the demotion must leave
    /// it alone. Green before AND after 4c (the boundary gates WHO gets demoted).
    #[test]
    fn nb4_4c_known_callee_not_demoted_stays_ref() {
        run_compiler(
            "unsafe fn f(p: *mut i32) -> *mut i32 { p.offset(1) }",
            |tcx| {
                use rustc_middle::mir::RETURN_PLACE;
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                assert!(
                    !collect_no_borrow_origin_slots(&origins, &slots).contains(&ret),
                    "known provenance-preserving `.offset` must NOT poison f's return (no 4c demotion)"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&ret),
                    Some(&SlotKind::Ref),
                    "NB4-4c: an origin-carrying `.offset` return must stay Ref (demotion must not over-reach)"
                );
            },
        );
    }

    /// §NB4-4c (PURE-READ RESIDUAL): a `*mut i32` param only READ through (`*p`) is NOT a
    /// no-borrow-origin slot and stays `Ref` — the demotion must never touch an ordinary read-only
    /// pointer. Green throughout.
    #[test]
    fn nb4_4c_pure_read_preserves_ref() {
        run_compiler("unsafe fn f(p: *mut i32) -> i32 { *p }", |tcx| {
            let program = collect_program(tcx);
            let f = function_by_name(&program, "f");
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            let origins = compute_origins(&program);
            let facts = MutFacts::from_program(&program);
            let p0 = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
            assert!(
                !collect_no_borrow_origin_slots(&origins, &slots).contains(&p0),
                "a read-only param must NOT be a no-borrow-origin slot"
            );
            let solver = KindSolver::new(&slots);
            let (_s, sel) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emission");
            add_coherence(&solver, &slots, f, &body);
            let m = verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
            assert_eq!(
                m.get(&p0),
                Some(&SlotKind::Ref),
                "NB4-4c: a purely-read param must stay Ref (pure-read residual)"
            );
        });
    }

    /// §NB4-4c MARKER (§8-guarded — the DEFERRED depth-0-arg retention gap, ruled 2026-07-16): a
    /// direct depth-0 `*mut T` arg to a genuinely-opaque callee stays UN-DEMOTED (`Ref`) today. base
    /// (lifetime_flow unknown-targets) does NOT poison it — pure-read externs are correctly left
    /// alone, which is why the seed-size dump showed a blanket depth-0 extension is a firehose (~21k
    /// args, ~all pure-read: __assert_fail/printf/fprintf/str/mem). The sound-AND-precise extension
    /// is deferred to a boundary-table effect-row expansion (fragment-F/§6.4 gap + backlog; sizing =
    /// tier-2 dump, harness `CRAT_BOC1_SEED_SIZE`). This pins the OPEN behavior: if `opaque_take`
    /// RETAINS `p` and later writes `*p`, a surviving `Ref` is unsound (§8-guarded, BO unconsumed).
    /// It FLIPS to `Raw` when the effect-row-paired extension lands — a tripwire, not a regression.
    #[test]
    fn nb4_4c_marker_depth0_arg_retention_open() {
        run_compiler(
            "unsafe extern \"C\" { fn opaque_take(p: *mut i32); } \
             unsafe fn f(p: *mut i32) { opaque_take(p); }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let p0 = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
                assert!(
                    !collect_no_borrow_origin_slots(&origins, &slots).contains(&p0),
                    "base must NOT poison a depth-0 arg to an opaque callee (the deferred gap)"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&p0),
                    Some(&SlotKind::Ref),
                    "§8-guarded OPEN gap: depth-0 arg retention un-demoted today; flips to Raw when \
                     the effect-row-paired depth-0 extension lands"
                );
            },
        );
    }

    /// §NB4-4c (FIELD coverage — the F2 field extension, LANDED this row per the seed-size ruling):
    /// a struct pointer field that receives opaque-callee provenance is a no-borrow-origin slot and
    /// DEMOTED to `Raw`. Drops the `field.is_some()` seed skip and maps the signature field slot to
    /// its kind `SlotRef::Field` via `slot_for_field_depth`. NB the field slot is crate-wide
    /// flow-insensitive, so this is a GLOBAL demotion (consistent with the existing field model).
    #[test]
    fn nb4_4c_no_origin_field_demoted_to_raw() {
        run_compiler(
            "struct S { p: *mut i32 } \
             unsafe extern \"C\" { fn opaque_dup(p: *mut i32) -> *mut i32; } \
             unsafe fn f(s: *mut S, q: *mut i32) { (*s).p = opaque_dup(q); }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let s_did = struct_by_name(&program, "S");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                // Fixture validity, independent of the seed's field-skip: a field slot IS no-borrow-origin.
                assert!(
                    origins.values().any(|su| su
                        .unknown
                        .iter()
                        .any(|sl| su.slots[sl].place.field.is_some())),
                    "fixture must poison a struct-field slot"
                );
                let field = StructFieldSlot {
                    struct_did: s_did,
                    field_index: 0,
                };
                let fslot = slots
                    .field_slots
                    .slot_for_field_depth(field, 0)
                    .expect("field S::p depth-0 kind slot");
                let fref = SlotRef::Field(fslot);
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&fref),
                    Some(&SlotKind::Raw),
                    "NB4-4c: a no-borrow-origin struct-field slot must be demoted to Raw (field skip dropped)"
                );
            },
        );
    }

    /// §NB4-4c MARKER (§8-guarded — the DEFERRED may-OVERWRITE hazard, ruled 2026-07-16): `out@1`
    /// (`*out = malloc()` then `opaque(out)`) holds owned heap and is in the NO-BORROW-ORIGIN set, so
    /// it settles **`Owning` today** — unchanged by the may-supply `¬ref` (which leaves an owned slot
    /// `Owning`). If `opaque` overwrites `*out` with foreign memory, codegen dropping the "owned" slot
    /// is a UAF. This hazard is NOT targetable from `summary.unknown`: the `malloc_only` vs
    /// `malloc_opaque` ablation proves `opaque(out)` adds nothing to the set, so a `¬own` here cannot
    /// tell it apart from a SAFE `*out = malloc()` (which must stay `Owning` — `store_through_ptr_*`).
    /// It DEFERS to the effect-row/opaque-interaction bucket (with depth-0). Pins `Owning`; FLIPS to
    /// `Raw` when overwrite detection lands — a tripwire, not a regression.
    #[test]
    fn nb4_4c_marker_may_overwrite_owning_today() {
        run_compiler(
            "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; fn opaque(out: *mut *mut i32); } \
             unsafe fn f(out: *mut *mut i32) { *out = malloc(core::mem::size_of::<i32>()); opaque(out); }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let out1 = local_slot(&slots, f, local_by_var_name(tcx, f, "out"), 1);
                assert!(
                    collect_no_borrow_origin_slots(&origins, &slots).contains(&out1),
                    "the out-param pointee is in the no-borrow-origin set (owned heap, no borrow origin)"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) =
                    emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                        .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&out1),
                    Some(&SlotKind::Owning),
                    "§8-guarded: owned out@1 stays Owning under may-supply ¬ref; the may-overwrite \
                     demotion is DEFERRED (opaque overwrite is not in the no-borrow-origin set)"
                );
            },
        );
    }

    /// §NB4-4c white-box: `KindSolver::add_owning_exclusion(slot)` forbids `Owning` — the CONTRACT of
    /// the deferred may-overwrite tool (rider 3, kept warm in place of `allow(dead_code)`). On a lone
    /// `malloc`-source return (which settles `Owning` under the may-supply `¬ref`), adding `¬own` makes
    /// the retractable source selector LEAK under relaxation → the slot settles `Raw`, never `Owning`,
    /// and never a hard decline.
    #[test]
    fn nb4_4c_add_owning_exclusion_forbids_owning() {
        run_compiler(
            "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; } \
             unsafe fn f() -> *mut i32 { malloc(4) }",
            |tcx| {
                use rustc_middle::mir::RETURN_PLACE;
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                let solver = KindSolver::new(&slots);
                let (_s, sel) =
                    emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                        .expect("emission");
                // Baseline (may-supply `¬ref` already applied): the malloc'd return settles Owning.
                let base = solver.model_kinds_relaxing(&sel).expect("sat");
                assert_eq!(
                    base.get(&ret),
                    Some(&SlotKind::Owning),
                    "baseline: a malloc-source return is Owning under ¬ref-only"
                );
                // `¬own` forbids Owning → the source selector leaks → Raw (non-Owning), not a decline.
                solver.add_owning_exclusion(ret);
                let m = solver
                    .model_kinds_relaxing(&sel)
                    .expect("relaxed accept, NOT a decline");
                assert_eq!(
                    m.get(&ret),
                    Some(&SlotKind::Raw),
                    "¬own must force non-Owning; on a malloc source it leaks → Raw"
                );
            },
        );
    }

    // ================= §NB4-4a — call-site semantics: A′ (live-requirer discharge) =================
    //
    // RULED 2026-07-12 after a borrow-STRUCTURE DUMP refuted the "the destination has no loan"
    // premise (that claim was inferred from one code site and was FALSE; the dump standard exists
    // because of it). What the dump actually shows for every shape below:
    //
    //     LOAN L_(0) borrowed=(*p) assigned=Assign(<arg temp>)   ← the call's arg-temp copy
    //     REQUIRES   x → [L_(0)]                                  ← x ALREADY requires it
    //     ERROR      L_(0) live ∧ invalidated                     ← already an error
    //     EDGE       issuer=<arg temp> requirers=[x]
    //
    // So the loan, the requirement, and the error all already exist. The bug is the DISCHARGE MENU:
    // Mode-A's `representative` prefers the ISSUER, so the arg temp (≡ `p`) is demoted and the live
    // requirer `x` survives as a `Ref` aliasing a cell written through a now-`Raw` sibling.
    //
    // A′ PRINCIPLE: demoting a slot discharges an edge only if it removes the CONFLICT, not the
    // REQUIREMENT. An edge with live `Ref` requirers BEYOND the issuer is discharged by
    // `⋁¬ref(live requirers)`; the issuer stays in the menu only when no such requirer exists.
    // (This RESTRICTS the commit menu — it adds no new assertion kind, so §3 invariant 7 holds.)

    /// §ESC-W1 — ②-minimal pin transition. The save/caller escape shape:
    ///
    /// ```ignore
    /// unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; *x = 1; }
    /// // caller: save(&raw mut slot, &raw mut cell); then reads *slot
    /// ```
    ///
    /// The C-side input is UB-FREE — `cell` outlives the call, `*x = 1` writes a live cell, and
    /// the caller's later read through the escaped pointer is valid — so §28's input-UB discharge
    /// does NOT apply. There is nonetheless no valid all-references typing: `x: &mut i32` moved
    /// into `*out` cannot then be used at `*x = 1`, and reborrowing to fix that shortens the
    /// lifetime below the caller's read. **The required verdict is therefore `x = Raw`.**
    ///
    /// The ②-minimal selected feeder loan is extended through exit in the first replay. Addendum
    /// 61 repairs that class through its presented source issuer. The next round must therefore
    /// carry zero selected loans—the source is no longer Ref—and settle `x = Raw`; persistence is
    /// a release-active convergence failure in the replay engine.
    #[test]
    fn escw1_escape_shape_demotes_x_raw() {
        use crate::analyses::borrow_ownership::{
            retirement::local_outcome::Reason, source_events::SourceRole,
        };
        const CODE: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; *x = 1; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;
        run_compiler(CODE, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let facts = MutFacts::from_program(&program);
            let solver = KindSolver::new(&slots);
            let (((model, stats), export), extensions, selected_sites, source) =
                with_fixture_selection(|| {
                    let construction = construct_bo_into(
                        &program,
                        &slots,
                        &origins,
                        &facts,
                        &solver,
                        CopyLendMode::Baseline,
                    )
                    .expect("ESC-W1 shared construction");
                    let selected_sites = construction.esc_minimal.sites.len();
                    assert_eq!(
                        construction.esc_minimal.cross_stage_counts(),
                        (1, 1, 1, 1),
                        "one effective selection must feed selection, exemption, extension, and receipt"
                    );
                    let (((model, stats), export), extensions) =
                        with_escaped_extension_trace(|| {
                            with_bo_export(|| {
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
                    (
                        ((model, stats), export),
                        extensions,
                        selected_sites,
                        construction.source_events.clone(),
                    )
                });
            assert_eq!(selected_sites, 1, "ESC-W1 selects one exact N4 site");
            assert!(!extensions.is_empty(), "escaped loan was not extended");
            let model = model.expect("R245 ESC coverage recovery keeps the model");
            let save = function_by_name(&program, "save");
            let x = local_slot(&slots, save, local_by_var_name(tcx, save, "x"), 0);
            assert_eq!(
                model[&x],
                SlotKind::Raw,
                "selected escape repairs its source issuer"
            );
            {
                // R245/R253: preserve exact source/depth receipts through local repair.
                let caller = function_by_name(&program, "caller");
                let slot_storage = local_by_var_name(tcx, caller, "slot");
                let cell_storage = local_by_var_name(tcx, caller, "cell");
                let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
                let out_addresses: Vec<_> = body
                    .basic_blocks
                    .iter()
                    .flat_map(|block| &block.statements)
                    .filter_map(|statement| {
                        let StatementKind::Assign(box (destination, Rvalue::RawPtr(_, borrowed))) =
                            &statement.kind
                        else {
                            return None;
                        };
                        (borrowed.as_local() == Some(slot_storage))
                            .then(|| destination.as_local())
                            .flatten()
                    })
                    .collect();
                assert_eq!(out_addresses.len(), 1, "actual &raw mut slot temporary");
                let inner = local_slot(&slots, caller, out_addresses[0], 1);
                let review = export
                    .source_retirement
                    .as_ref()
                    .expect("typed retirement decline");
                assert_eq!(stats.source_retirement_decline, review.unresolved);
                assert!(review.unresolved.is_empty());
                let rows = export
                    .retirement_rounds
                    .iter()
                    .flat_map(|round| &round.demotions)
                    .filter(|row| row.holder == inner)
                    .collect::<Vec<_>>();
                assert!(!rows.is_empty());
                assert_eq!(model[&inner], SlotKind::Raw);
                let mut actual = std::collections::BTreeSet::new();
                for row in &rows {
                    assert_eq!(row.reason.inner_loan_depth(), Some(1));
                    assert_eq!(row.holder, inner);
                    assert!(row.chain.contains(&inner));
                    for target in &row.chain {
                        assert_eq!(model[target], SlotKind::Raw);
                    }
                    let event = &row.source;
                    assert!(source.retirements.contains_key(event));
                    assert_eq!(event.function, "caller");
                    assert_eq!(row.function, caller);
                    assert_eq!(row.phase, event.phase);
                    assert_eq!(
                        row.location,
                        Location {
                            block: rustc_middle::mir::BasicBlock::from_u32(event.block),
                            statement_index: event.statement
                        }
                    );
                    assert!(row.route.is_empty());
                    actual.insert((event.role, event.storage_local));
                }
                let expected = [cell_storage, slot_storage]
                    .into_iter()
                    .flat_map(|local| {
                        [
                            (SourceRole::UnwindStorage, Some(local.as_u32())),
                            (SourceRole::StorageDead, Some(local.as_u32())),
                        ]
                    })
                    .collect::<std::collections::BTreeSet<_>>();
                assert_eq!(actual, expected);
                assert!(stats.rounds > 1 && stats.commits_conflict > 0);
                assert_eq!(stats.copy_lend_replay_selections, 0);
                assert!(
                    export.residual_conflicts.is_some(),
                    "accepted model has its certificate"
                );
            }
        });
    }

    /// §39 addendum 65 R-a — brotli's param-deref FIELD destination shape.
    /// The selected escape row may discharge only by demoting its presented
    /// source issuer. A Raw destination field is a legal mixed-emission
    /// channel: it remains receipt evidence, never a guard/repair party.
    #[test]
    fn escw2_field_store_escape_demotes_source_and_leaves_destination_raw() {
        const CODE: &str = r#"
struct Holder { p: *mut i32 }
unsafe extern "C" { fn opaque() -> *mut i32; }
unsafe fn save(out: *mut Holder, x: *mut i32) {
    (*out).p = opaque();
    (*out).p = x;
    *x = 1;
}
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut holder = Holder { p: core::ptr::null_mut() };
    save(&raw mut holder, &raw mut cell);
    *holder.p
}
"#;
        run_compiler(CODE, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let facts = MutFacts::from_program(&program);
            let save = function_by_name(&program, "save");
            let x = local_by_var_name(tcx, save, "x");
            let x = local_slot(&slots, save, x, 0);
            let holder = struct_by_name(&program, "Holder");
            let field = slots
                .field_slots
                .slot_for_field_depth(
                    StructFieldSlot {
                        struct_did: holder,
                        field_index: 0,
                    },
                    0,
                )
                .expect("Holder::p depth-0 slot");
            let field = SlotRef::Field(field);

            let baseline_solver = KindSolver::new(&slots);
            let baseline_construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &baseline_solver,
                CopyLendMode::Baseline,
            )
            .expect("field-store baseline construction");
            assert!(baseline_construction.esc_minimal.sites.is_empty());
            let (baseline, _) = verify_bo_construction_counting(
                &program,
                &slots,
                &origins,
                &baseline_solver,
                &baseline_construction,
                &facts,
            );
            let baseline = baseline.expect("field-store baseline accepts");
            assert_eq!(baseline.get(&x), Some(&SlotKind::Ref));
            assert_eq!(baseline.get(&field), Some(&SlotKind::Raw));

            let selected_solver = KindSolver::new(&slots);
            let (((selected, stats), extensions), selected_site) = with_fixture_selection(|| {
                let construction = construct_bo_into(
                    &program,
                    &slots,
                    &origins,
                    &facts,
                    &selected_solver,
                    CopyLendMode::Baseline,
                )
                .expect("field-store selected construction");
                let selected_site = construction
                    .esc_minimal
                    .sites
                    .first()
                    .map(|site| (construction.esc_minimal.sites.len(), site.lhs));
                let ((model, stats), extensions) = with_escaped_extension_trace(|| {
                    verify_bo_construction_counting(
                        &program,
                        &slots,
                        &origins,
                        &selected_solver,
                        &construction,
                        &facts,
                    )
                });
                (((model, stats), extensions), selected_site)
            });
            assert_eq!(
                selected_site,
                Some((1, field)),
                "the destination field remains explicit receipt metadata"
            );
            assert!(!extensions.is_empty(), "selected field loan reaches exit");
            assert_eq!(stats.copy_lend_replay_selections, 0);
            let selected = selected.expect("issuer-only field-store repair accepts");
            assert_eq!(selected.get(&x), Some(&SlotKind::Raw));
            assert_eq!(
                selected.get(&field),
                baseline.get(&field),
                "the Raw destination field is receipt-only and remains untouched"
            );
        });
    }

    /// §39 addendum 65 R-b — the A5 reference solve is the c080 comparison
    /// layer. Even inside a fixture-selection scope it must not consume ②;
    /// only the subsequent candidate construction may do so.
    #[test]
    fn a5_baseline_reference_does_not_consume_esc_selection() {
        use crate::analyses::borrow_ownership::{
            retirement::local_outcome::Reason, source_events::SourceRole,
        };
        const CODE: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; *x = 1; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;
        run_compiler(CODE, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let facts = MutFacts::from_program(&program);
            let (result, export) = with_bo_export(|| {
                with_fixture_selection(|| {
                    solve_bo_overlap_reference_reporting(
                        &program,
                        &slots,
                        &origins,
                        &facts,
                        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
                    )
                })
            });
            let verified = result.expect("R245 keeps the reference model");
            let model = &verified.model;
            assert!(!export.retirement_rounds.is_empty());
            assert!(
                export
                    .loans
                    .iter()
                    .all(|loan| loan.class != LoanClass::CopyLend)
            );
            let caller = function_by_name(&program, "caller");
            let slot_storage = local_by_var_name(tcx, caller, "slot");
            let cell_storage = local_by_var_name(tcx, caller, "cell");
            let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
            let out_addresses: Vec<_> = body
                .basic_blocks
                .iter()
                .flat_map(|block| &block.statements)
                .filter_map(|statement| {
                    let StatementKind::Assign(box (destination, Rvalue::RawPtr(_, borrowed))) =
                        &statement.kind
                    else {
                        return None;
                    };
                    (borrowed.as_local() == Some(slot_storage))
                        .then(|| destination.as_local())
                        .flatten()
                })
                .collect();
            assert_eq!(out_addresses.len(), 1);
            let inner = local_slot(&slots, caller, out_addresses[0], 1);
            let source = export
                .source_events
                .as_ref()
                .expect("actual reference source inventory");
            let review = export
                .source_retirement
                .as_ref()
                .expect("typed reference decline");
            assert!(review.unresolved.is_empty());
            let rows = export
                .retirement_rounds
                .iter()
                .flat_map(|round| &round.demotions)
                .filter(|row| row.holder == inner)
                .collect::<Vec<_>>();
            assert!(!rows.is_empty());
            assert_eq!(model[&inner], SlotKind::Raw);
            let mut actual = std::collections::BTreeSet::new();
            for row in &rows {
                assert_eq!(row.reason.inner_loan_depth(), Some(1));
                assert_eq!(row.holder, inner);
                for target in &row.chain {
                    assert_eq!(model[target], SlotKind::Raw);
                }
                let event = &row.source;
                assert!(source.retirements.contains_key(event));
                assert_eq!(event.function, "caller");
                assert_eq!(row.function, caller);
                assert_eq!(row.phase, event.phase);
                assert_eq!(
                    row.location,
                    Location {
                        block: rustc_middle::mir::BasicBlock::from_u32(event.block),
                        statement_index: event.statement
                    }
                );
                assert!(row.route.is_empty());
                actual.insert((event.role, event.storage_local));
            }
            let expected = [cell_storage, slot_storage]
                .into_iter()
                .flat_map(|local| {
                    [
                        (SourceRole::UnwindStorage, Some(local.as_u32())),
                        (SourceRole::StorageDead, Some(local.as_u32())),
                    ]
                })
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(actual, expected);
            assert!(export.residual_conflicts.is_some());
        });
    }

    fn nb4_accept<'tcx>(
        tcx: TyCtxt<'tcx>,
        program: &RustProgram<'tcx>,
        fn_name: &str,
        names: &[&str],
    ) -> Vec<(Option<SlotKind>, bool)> {
        let f = function_by_name(program, fn_name);
        let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        let slots = CrateSlots::build(program);
        let crate_ctxt = CrateCtxt::new(program);
        let facts = MutFacts::from_program(program);
        let solver = KindSolver::new(&slots);
        let (_s, sel) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("emission");
        add_coherence(&solver, &slots, f, &body);
        let model = verify_to_fixpoint(program, &slots, &solver, &sel, &facts).expect("accepts");
        names
            .iter()
            .map(|n| {
                let l = local_by_var_name(tcx, f, n);
                let slot = local_slot(&slots, f, l, 0);
                (model.get(&slot).copied(), facts.is_mutable(f, l))
            })
            .collect()
    }

    /// S1 helper: solve the ordinary Mode-A path and return its accepted model.
    /// The caller owns the semantic assertion so the premise control and
    /// coverage contrasts all exercise the same setup.
    fn s1_accept_model(
        program: &RustProgram<'_>,
        f: LocalDefId,
    ) -> (CrateSlots, FxHashMap<SlotRef, SlotKind>) {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(f)
            .borrow();
        let slots = CrateSlots::build(program);
        let crate_ctxt = CrateCtxt::new(program);
        let facts = MutFacts::from_program(program);
        let solver = KindSolver::new(&slots);
        let (_stats, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(program),
            &solver,
        )
        .expect("S1 ownership emission");
        add_coherence(&solver, &slots, f, &body);
        let model = verify_to_fixpoint(program, &slots, &solver, &selectors, &facts)
            .expect("S1 fixture must reach a Mode-A acceptance");
        assert!(
            model_accepts(program, &slots, &model, &facts),
            "the model returned by Mode-A must be accepted by the same oracle"
        );
        (slots, model)
    }

    fn s1_all_ref_model(slots: &CrateSlots) -> FxHashMap<SlotRef, SlotKind> {
        let mut model = FxHashMap::default();
        for index in 0..slots.field_slots.len() {
            model.insert(SlotRef::Field(SlotId::from_usize(index)), SlotKind::Ref);
        }
        for (&did, universe) in &slots.fn_local_slots {
            for index in 0..universe.len() {
                model.insert(
                    SlotRef::Local(did, SlotId::from_usize(index)),
                    SlotKind::Ref,
                );
            }
        }
        model
    }

    /// S1 premise control: `q = p` creates a loan on `*p`, then the bare
    /// assignment `p = other` kills it.  Rust accepts the same-lifetime
    /// reference lowering while `q` remains live: replacing the reference
    /// local does not access the old pointee, which remains borrowed through
    /// `q`.  The kill is therefore the correct boundary, not a missed error.
    #[test]
    #[ignore = "S1 premise control: run explicitly with the coverage investigation"]
    fn s1_loan_kill_plain_overwrite_is_valid_ref_replacement() {
        run_compiler(
            "#[allow(unused_assignments)] \
             fn lowered<'a>(mut p: &'a mut i32, other: &'a mut i32) -> i32 { \
                 let q = &mut *p; *q = 1; p = other; *q \
             } \
             unsafe fn f(mut p: *mut i32, other: *mut i32) -> i32 { \
                 let q = p; *q = 1; p = other; *q \
             }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let (slots, model) = s1_accept_model(&program, f);
                let p = local_slot(&slots, f, p, 0);
                let q = local_slot(&slots, f, q, 0);
                eprintln!(
                    "S1 plain accepted kinds: p={:?} q={:?}",
                    model.get(&p),
                    model.get(&q)
                );
                assert_eq!(
                    (model.get(&p), model.get(&q)),
                    (Some(&SlotKind::Ref), Some(&SlotKind::Ref)),
                    "Rust accepted the explicit same-lifetime reference lowering in this same \
                     crate; Mode A should preserve the valid Ref/Ref replacement shape"
                );
            },
        );
    }

    /// S1 C-idiomatic variant.  Unlike the plain overwrite, the right-hand side
    /// reads through `p`; the existing deep-access path may catch this before
    /// the destination assignment kills loans rooted at `p`.
    #[test]
    #[ignore = "S1 boundary fixture: run explicitly with the coverage investigation"]
    fn s1_loan_kill_c_next_overwrite_must_reject_all_ref_model() {
        run_compiler(
            "#[repr(C)] struct Node { next: *mut Node, value: i32 } \
             unsafe fn f(mut p: *mut Node) -> i32 { \
                 let q = p; (*q).value = 1; p = (*p).next; (*q).value \
             }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let (slots, model) = s1_accept_model(&program, f);
                let p = local_slot(&slots, f, p, 0);
                let q = local_slot(&slots, f, q, 0);
                eprintln!(
                    "S1 C-next accepted kinds: p={:?} q={:?}",
                    model.get(&p),
                    model.get(&q)
                );
                let all_ref = s1_all_ref_model(&slots);
                let facts = MutFacts::from_program(&program);
                assert!(
                    !model_accepts(&program, &slots, &all_ref, &facts),
                    "the C-style dereferenced RHS must invalidate q's required loan before kill"
                );
            },
        );
    }

    /// S1 negative control: without the reassignment of the borrowed source,
    /// the pointer copy and exclusive use through `q` are a valid reborrow.
    #[test]
    #[ignore = "S1 negative control: run explicitly with the coverage investigation"]
    fn s1_loan_kill_no_overwrite_control_stays_accepted() {
        run_compiler(
            "unsafe fn f(p: *mut i32) -> i32 { let q = p; *q = 1; *q }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let (slots, model) = s1_accept_model(&program, f);
                eprintln!(
                    "S1 control accepted kinds: p={:?} q={:?}",
                    model.get(&local_slot(&slots, f, p, 0)),
                    model.get(&local_slot(&slots, f, q, 0))
                );
                let all_ref = s1_all_ref_model(&slots);
                let facts = MutFacts::from_program(&program);
                assert!(
                    model_accepts(&program, &slots, &all_ref, &facts),
                    "control: without a source overwrite the all-Ref reborrow remains valid"
                );
                assert_eq!(
                    (
                        model.get(&local_slot(&slots, f, p, 0)),
                        model.get(&local_slot(&slots, f, q, 0)),
                    ),
                    (Some(&SlotKind::Ref), Some(&SlotKind::Ref)),
                    "control: the no-overwrite reborrow should remain accepted as Ref/Ref"
                );
            },
        );
    }

    /// S1 nearest-shape contrast: if the use after `p = other` writes through
    /// `q`, the current provenance/`requires` routing rejects the all-Ref
    /// model even though Rust accepts the same-lifetime reference lowering.
    /// This is a conservative compensation, not evidence that the bare kill
    /// should have been an error.
    #[test]
    #[ignore = "S1 routing contrast: run explicitly with the coverage investigation"]
    fn s1_post_overwrite_write_routing_is_conservative() {
        run_compiler(
            "#[allow(unused_assignments)] \
             fn lowered<'a>(mut p: &'a mut i32, other: &'a mut i32) -> i32 { \
                 let q = &mut *p; p = other; *q = 1; *q \
             } \
             unsafe fn f(mut p: *mut i32, other: *mut i32) -> i32 { \
                 let q = p; p = other; *q = 1; *q \
             }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let (slots, model) = s1_accept_model(&program, f);
                let p = local_slot(&slots, f, p, 0);
                let q = local_slot(&slots, f, q, 0);
                eprintln!(
                    "S1 post-write accepted kinds: p={:?} q={:?}",
                    model.get(&p),
                    model.get(&q)
                );
                let all_ref = s1_all_ref_model(&slots);
                let facts = MutFacts::from_program(&program);
                assert!(
                    !model_accepts(&program, &slots, &all_ref, &facts),
                    "current boundary: provenance/requirements reject all-Ref after q writes"
                );
            },
        );
    }

    /// S1 tree-grouping contrast: force `p` Raw in replay.  Its earlier invalid
    /// loan unions `p` with `r`; rebuilding `q = p` must then add the existing
    /// bare group-member loan on `r`, so `r = other` surfaces a conflict owned
    /// and required by `q` even though the copy arm still skips bare `p`.
    #[test]
    #[ignore = "S1 grouping contrast: run explicitly with the coverage investigation"]
    fn s1_tree_group_member_contrast_catches_sibling_overwrite() {
        run_compiler(
            "unsafe fn f(mut r: *mut i32, other: *mut i32) -> i32 { \
                 let p = r; *r = 1; let q = p; r = other; *q = 2; *q \
             }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let slots = CrateSlots::build(&program);
                let p_slot = local_slot(&slots, f, p, 0);
                let q_slot = local_slot(&slots, f, q, 0);
                let conflicts = revalidate_replaying(
                    &program,
                    &slots,
                    |slot| slot != p_slot,
                    |slot| slot == p_slot,
                    true,
                );
                assert!(
                    conflicts
                        .get(&f)
                        .is_some_and(|edges| edges.iter().any(|edge| {
                            edge.issuer == Some(q_slot) || edge.requirers.contains(&q_slot)
                        })),
                    "tree-group replay must catch the sibling overwrite through q's bare group \
                     member loan; got {conflicts:?}"
                );
            },
        );
    }

    const NB4_ID: &str = "#[inline(never)] unsafe fn id(q: *mut i32) -> *mut i32 { q } ";

    /// §NB4-4a-ii — pins the six-class pointee-effect SCHEMA and the ONE `Role → Effect` mapping
    /// (rider 5: stated once; 4c consumes it unmodified). The gate that would have consumed
    /// `no-access` at invalidation time was refuted (see `nb4_no_deref_callee_still_conflicts`);
    /// the SCHEMA survives because 4c's `unknown` demotion is defined over these classes. This
    /// test keeps the mapping honest until then — it is the schema's only consumer.
    #[test]
    fn nb4_effect_schema_role_mapping() {
        use crate::analyses::borrow_ownership::boundary_table::{Effect, Role, role_effects};
        // The bottom class is exactly the roles that never touch the pointee.
        for r in [Role::Ignore, Role::Lend, Role::NullConstructor] {
            assert_eq!(
                role_effects(r),
                [Effect::NoAccess],
                "{r:?} must be no-access"
            );
        }
        // Every other role touches the pointee (read/write/free/reborrow) — never no-access.
        for r in [
            Role::Source,
            Role::Sink,
            Role::FlowTransfer,
            Role::LoanCreating,
            Role::ProvenanceFlow,
            Role::FlowSuppression,
        ] {
            assert!(
                !role_effects(r).contains(&Effect::NoAccess),
                "{r:?} accesses the pointee and must NOT be no-access"
            );
        }
        // The two effect classes 4c gates on are represented where expected.
        assert!(
            role_effects(Role::Sink).contains(&Effect::MayOverwrite),
            "free ⇒ may-overwrite"
        );
        assert!(
            role_effects(Role::Source).contains(&Effect::MaySupply),
            "alloc ⇒ may-supply"
        );
    }

    // ===== §NB4-4a NAMED RESIDUAL — "unmodeled call-boundary materialization" =====
    // (raw caller arg → `Ref` callee param.)
    //
    // Surfaced by 4a-i's WIDENED §0.1 residual-model probe. **PRE-EXISTING**: both markers below
    // hold identically before A′, so A′ neither introduces nor regresses this class — the probe
    // only made it visible.
    //
    // STATUS: accepted for this pass, **§8-guarded** (BO output is unconsumed by codegen). It is
    // NOT proven safe and no safety is claimed here. A `Ref` callee param reached from a `Raw`
    // caller arg forces the rewriter to materialize `&mut *p` at the call. That materialized
    // reborrow is never modeled: its issuer (the arg temp) is `Raw`, and a `Raw` local issues no
    // loan in the replay, so no loan exists to check. This is a **LOAN-CREATION GAP** (plan
    // fragment-F / §6.4 list: OPEN).
    //
    // MECHANISM OWNERSHIP: the candidate fix ("retain the loan when the callee param is `Ref`
    // though the caller arg is `Raw`") is ENTANGLED with the F2 copy-group routing redesign — a
    // materialized loan is inert without routing, because the invalidating access is keyed under a
    // different `Local` (the same `local_map` blindness). Investigation is assigned to **4b's
    // micro-plan**, alongside routing; the homing decision is made there, with dumps.

    /// MARKER — raw caller arg → `Ref` callee param, unmodeled. `f`'s whole cluster is correctly
    /// `Raw` under A′, yet `id`'s PARAM settles `Ref`, so the call must materialize `&mut *p` from
    /// a raw pointer. §8-guarded; must flip when the materialized reborrow is modeled.
    #[test]
    fn nb4_marker_raw_arg_ref_param_unmodeled() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let x = id(p); *x = 1; let b = p; *b = 2; *x }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let caller = nb4_accept(tcx, &program, "f", &["x", "p", "b"]);
                let sig = nb4_accept(tcx, &program, "id", &["q"]);
                for (n, k) in [("x", caller[0].0), ("p", caller[1].0), ("b", caller[2].0)] {
                    assert_eq!(k, Some(SlotKind::Raw), "A′: caller-side `{n}` is Raw");
                }
                assert_eq!(
                    sig[0].0,
                    Some(SlotKind::Ref),
                    "TODAY `id.q` settles `Ref` while every caller-side slot is `Raw` — the call \
                     materializes `&mut *p` from a raw pointer and that reborrow is UNMODELED \
                     (§8-guarded). Must flip when the materialized loan is modeled."
                );
            },
        );
    }

    /// MARKER (the SHARPEST instance) — **two aliasing args, both `Ref`**. `id2(p, p)` passes the
    /// same raw pointer twice into a callee whose params BOTH settle `Ref`, so the call site
    /// materializes **two overlapping `&mut` to one cell**. That is UB at materialization — no
    /// during-call write is even required. Accepted today; §8-guarded.
    #[test]
    fn nb4_marker_two_aliasing_args_both_ref() {
        run_compiler(
            "#[inline(never)] unsafe fn id2(a: *mut i32, b: *mut i32) -> i32 \
             { *a = 1; *b = 2; *a } \
             unsafe fn f(p: *mut i32) -> i32 { id2(p, p) }",
            |tcx| {
                let program = collect_program(tcx);
                let callee = nb4_accept(tcx, &program, "id2", &["a", "b"]);
                let caller = nb4_accept(tcx, &program, "f", &["p"]);
                assert_eq!(caller[0].0, Some(SlotKind::Raw), "the caller's `p` is Raw");
                assert_eq!(
                    (callee[0].0, callee[1].0),
                    (Some(SlotKind::Ref), Some(SlotKind::Ref)),
                    "TODAY both params of `id2` settle `Ref` while the sole caller passes ONE raw \
                     pointer to both — the call materializes two overlapping `&mut` to the same \
                     cell (UB at materialization). §8-guarded; must flip when the materialized \
                     loans are modeled."
                );
            },
        );
    }

    /// §NB4-4a RED (c) — **returned borrow vs base mutation.** `x = id(p)` aliases `(*p)` through
    /// the call return; the base is then mutated through the sibling copy `b = p`. TODAY the edge
    /// `issuer=<arg temp> requirers=[x]` is discharged via the ISSUER, so `p`/`b` go `Raw` and
    /// **`x` survives `Ref`** — a shared reference into a cell written through a raw alias (the
    /// S2-6 family, production-parity, §8-guarded). A′ must demote the live requirer `x`.
    ///
    /// §0.1 residual-model probe (WIDENED, ruled 2026-07-12): the accepted model is inspected for
    /// the WHOLE aliasing cluster, not just `x` — no slot in it may remain `Ref`, or the "fix" has
    /// merely relocated the unsoundness. Any `Ref` here is a STOP requiring a soundness argument.
    #[test]
    fn nb4_returned_borrow_vs_base_mutation() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let x = id(p); *x = 1; let b = p; *b = 2; *x }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["x", "p", "b"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "A′: `x` is a LIVE requirer of the invalidated loan on `(*p)`; demoting the \
                     issuer (the arg temp ≡ `p`) removes the CONFLICT but not x's REQUIREMENT — \
                     x must not survive `Ref`"
                );
                // §0.1 WIDENED residual-model probe: pin the FULL accepted model, not just `x` —
                // a "fix" that merely relocates the unsoundness must not pass.
                for (label, (kind, _)) in [("p", m[1]), ("b", m[2])] {
                    assert_ne!(
                        kind,
                        Some(SlotKind::Ref),
                        "residual-model probe: `{label}` aliases the written cell and must not \
                         settle `Ref` — a `Ref` here means the unsoundness moved, not closed"
                    );
                }
                // The ONE slot that does settle `Ref`: the callee PARAM. Pinned, not excused — it
                // is the named residual "unmodeled call-boundary materialization" (§8-guarded,
                // pre-existing, assigned to 4b's micro-plan). See
                // `nb4_marker_raw_arg_ref_param_unmodeled` and `nb4_marker_two_aliasing_args_both_ref`.
                let sig = nb4_accept(tcx, &program, "id", &["q"]);
                assert_eq!(
                    sig[0].0,
                    Some(SlotKind::Ref),
                    "residual-model probe: `id.q` is the sole `Ref` in the accepted model — the \
                     named call-boundary-materialization residual, NOT closed by A′"
                );
            },
        );
    }

    /// §NB4-4a RED (a) — **callee write kills the caller's alias.** Same edge shape as (c), but the
    /// invalidating write comes from a CALLEE (`writer` writes `*q`) rather than an inline base
    /// mutation. This is the INTERACTION fixture: it must hold under A′ (4a-i) *and* survive
    /// 4a-ii's effect gating, because `writer` is classified **may-write** — gating must not
    /// silently switch off a real writer's access.
    #[test]
    fn nb4_callee_write_invalidates_caller_loan() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn writer(q: *mut i32) {{ *q = 7; }} \
                 unsafe fn f(p: *mut i32) -> i32 {{ let x = id(p); *x = 1; writer(p); *x }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["x", "p"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "A′: `writer(p)` invalidates the loan `x` requires; x is the live requirer and \
                     must be demoted (today the issuer is demoted and x survives `Ref`)"
                );
                assert_ne!(
                    m[1].0,
                    Some(SlotKind::Ref),
                    "residual probe: `p` must not stay `Ref`"
                );
            },
        );
    }

    /// §NB4-4a RED (c′) — the **minimal S2-6-family** shape: the returned borrow `x` is IMMUTABLE
    /// (never written through ⇒ Foster `Imm`), and the base is written through the sibling `b = p`.
    /// A′ closes this **a phase early** — its reach is a property of the EDGE MENU, not of loan
    /// mutability, so the "immutable ⇒ needs write-awareness" intuition does not apply.
    ///
    /// ⚠ TRIPWIRE (recorded 2026-07-12): this closure rests on the pointer-copy-as-`Deep`-access
    /// OVER-APPROXIMATION — `let b = p` is a copy of the pointer VALUE, not an access to the
    /// pointee, yet it invalidates the loan `x` requires. If any future precision work gates copy
    /// accesses, this fixture goes RED and the soundness must be re-carried by the copy-group
    /// routing mechanism (the redesigned 4b closure). This test is the tripwire for exactly that.
    #[test]
    fn nb4_returned_immutable_borrow_vs_base_write() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let x = id(p); let b = p; *b = 5; *x }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["x", "p", "b"]);
                assert!(
                    !m[0].1,
                    "precondition: `x` is never written THROUGH ⇒ Foster `Imm` (this is the \
                     immutable shape — the one the Imm-skip protects at 4b)"
                );
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "A′ demotes the live requirer `x` even though its provenance is IMMUTABLE — \
                     the menu restriction is orthogonal to the immutable-loan skip"
                );
                assert_ne!(m[1].0, Some(SlotKind::Ref), "residual probe: `p`");
                assert_ne!(m[2].0, Some(SlotKind::Ref), "residual probe: `b`");
            },
        );
    }

    /// §NB4-4a-ii **CONTROL — the fixture that KILLED the no-access gate.** (Was
    /// `nb4_no_deref_callee_loan_survives`, asserting `x` stays `Ref`. That assertion was
    /// **UNSOUND**; it now pins the opposite, and exists to stop the gate being re-attempted.)
    ///
    /// `ignores` takes the pointer BY VALUE and never dereferences it, so the "spurious
    /// over-invalidation" story was: the Call arm's effect-blind `Deep` access to `(*arg)`
    /// manufactures a conflict no callee could cause ⇒ gate it and `x` survives `Ref`.
    ///
    /// **The no-call CONTROL refutes that.** Replacing `ignores(p)` with a plain value use of `p`
    /// and **no call at all** (`let v = p as usize as i32;`) demotes `x` to `Raw` *identically*.
    /// So the conflict is not about the POINTEE and not about the call: it is a **use of `p`
    /// while `x` holds an outstanding reborrow of `(*p)`**, which under the reference reading the
    /// model is deciding is a GENUINE borrowck conflict (`let x = id(p); *x = 1; /* use p */; *x`
    /// — you cannot use a `&mut` while a live reborrow derives from it).
    ///
    /// Therefore `Deep`-access-on-copy is **not** an over-approximation of pointee access — it is
    /// the correct conservative treatment of a use of a BORROWED BASE, and there is no
    /// over-invalidation class to gate at the argument level. `call_effects`'s `no-access` facts
    /// are real, but gating invalidation on them is unsound. **Do not re-add the gate.**
    #[test]
    fn nb4_no_deref_callee_still_conflicts() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn ignores(_q: *mut i32) -> i32 {{ 0 }} \
                 unsafe fn f(p: *mut i32) -> i32 \
                 {{ let x = id(p); *x = 1; let v = ignores(p); *x + v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["x"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`x` MUST be demoted: passing `p` to `ignores` is a USE of `p` while `x` holds \
                     a live reborrow of `(*p)` — a genuine conflict, independent of what the callee \
                     does with the pointee. The no-call control (`let v = p as usize`) demotes `x` \
                     identically, which is what refuted the no-access gate. Do not gate this."
                );
            },
        );
    }

    /// §NB4-R MARKER — Codex adversarial review (2026-07-15) surfaced two code-level fragilities in
    /// the routing under MULTIPLY-ASSIGNED / branch-joined MIR locals:
    ///   (F1) offset exclusion keys by `(Local, Place)` without loan-location, so a local assigned
    ///        BOTH `b = p.offset(1)` and `b = p` (same source) has its copy loan wrongly excluded;
    ///   (F2) the routing walk dedups by base `Local`, so a writer branch-joined from `h.q`/`h.r`
    ///        (both base local `h`) has one field edge dropped by the visited set.
    /// Both are in the UNDER-invalidation direction (a missed demotion → §8-guarded UAF class).
    ///
    /// This marker WITNESSES that on both flagged shapes the views settle `Raw` REGARDLESS of routing
    /// (verified `Raw` with `CRAT_NB4R_ROUTING` on AND off, 2026-07-15): the tree-borrow GROUP
    /// machinery demotes the branch/collision copies independently, so the routing edge-drop /
    /// over-exclusion is MASKED — no observable under-invalidation. The findings are latent code
    /// fragility, not an active regression. If a future change removes the grouping safety net for
    /// these shapes, this marker flips (a view goes `Ref`) and surfaces the hole. See the NB4-R task
    /// doc for the fix options (F2: dedup the walk by loan/edge, not base local; F1: disambiguate
    /// offset vs copy via a copy-signature set).
    #[test]
    fn nb4r_marker_multiassign_grouping_masked() {
        let f2 = format!(
            "{NB4_ID} #[repr(C)] struct H {{ q: *mut i32, r: *mut i32 }} \
             unsafe fn f(mut h: H, c: bool) -> i32 \
             {{ let vq = id(h.q); let vr = id(h.r); let b = if c {{ h.q }} else {{ h.r }}; \
                let r0 = *vq + *vr; *b = 5; r0 + *vq + *vr }}"
        );
        let f1 = format!(
            "{NB4_ID} unsafe fn f(mut p: *mut i32, c: bool) -> i32 \
             {{ let v = id(p); let mut b = p; if c {{ b = p.offset(1); }} \
                let r0 = *v; *b = 5; r0 + *v }}"
        );
        for (label, src, views) in [
            ("F2 branch-joined field sources", f2, &["vq", "vr"][..]),
            ("F1 offset+copy collision", f1, &["v"][..]),
        ] {
            run_compiler(&src, |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", views);
                for (i, v) in views.iter().enumerate() {
                    assert_eq!(
                        m[i].0,
                        Some(SlotKind::Raw),
                        "{label}: view `{v}` is demoted by the grouping safety net (Raw), masking the \
                         Codex-flagged routing fragility — no observable under-invalidation here."
                    );
                }
            });
        }
    }

    /// §NB4-R MARKER — the READ-direction residue that WRITE-gating could open (user probe 2026-07-16).
    /// Shape: `x = id(p)` is a LIVE MUTABLE call-return `&mut` (it writes `*x=1` later); a foreign read
    /// `v = *b` (b=p, sibling) sits between x's borrow and x's write. Under Tree Borrows the foreign
    /// read freezes x's tag → `*x=1` is UB, so x must NOT stay a safe `&mut`. Routing is WRITE-gated,
    /// so `*b` (a read) does NOT route to x's loan (keyed under p) — the worry was that this leaves x
    /// at `Ref`.
    ///
    /// WITNESS: x settles `Raw` with `CRAT_NB4R_ROUTING` on AND off (verified 2026-07-16). MECHANISM —
    /// GROUPING masks it: unlike a shared read *view* (which survives grouping and is the S2-6 hole a
    /// WRITE must route to close, e.g. `nb4r_sibling_copies`), a `&mut` view aliasing the same cell is
    /// linked through `p` to the co-aliaser `b` and demoted by the tree-borrow group conflict. So
    /// write-gating did NOT open an observable residue in the read-vs-`&mut` direction. This joins
    /// F1/F2/3b behind the grouping safety net (see NB4-R task doc §13). If a future change stops
    /// grouping from demoting a `&mut` with a live foreign read, this marker flips (x → Ref) and the
    /// residue becomes real — at which point route read-derefs but check only MUTABLE loans
    /// (borrowck's read-vs-`&mut`; the immutable-loan skip already spares read-only cells).
    #[test]
    fn nb4r_marker_read_vs_mut_grouping_masked() {
        let src = format!(
            "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
             {{ let x = id(p); let b = p; let v = *b; *x = 1; v + *x }}"
        );
        run_compiler(&src, |tcx| {
            let program = collect_program(tcx);
            let m = nb4_accept(tcx, &program, "f", &["x"]);
            assert_eq!(
                m[0].0,
                Some(SlotKind::Raw),
                "x (a &mut call-return frozen by the foreign read `*b`) is demoted to Raw by the \
                 grouping safety net — so WRITE-gating opens no observable read-vs-&mut residue."
            );
        });
    }

    /// §NB4-R WHITE-BOX (Amendment 3b, grouping-independent) — the whole-cell fallback DECISION.
    /// The end-to-end `nb4r_type_pun_invalidates` is grouping-masked (the view is `Raw` regardless), so
    /// a fallback REGRESSION (composing the ill-typed place → `places_conflict` `unreachable!`/`Disjoint`)
    /// could hide behind grouping. This tests `route_compose` directly: an `(*p):i32` edge with a
    /// `Pair`-field `rest` and `deref_ty = Pair` MUST return `WholeCell` (the whole i32 cell, later
    /// forced Deep), never `Composed` (which would feed `places_conflict` an ill-typed place). The
    /// well-typed control (`(*q):Pair` edge, same rest) MUST `Composed`. Survives grouping changes.
    #[test]
    fn nb4r_route_compose_fallback_on_type_mismatch() {
        use rustc_abi::FieldIdx;
        use rustc_middle::mir::{Place, PlaceElem};

        use crate::analyses::borrow_ownership::borrow_engine::{RoutedCompose, route_compose};
        run_compiler(
            "#[repr(C)] struct Pair { a: i32, b: i32 } \
             unsafe fn f(p: *mut i32, q: *mut Pair) { let _ = (p, q); }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let bp = Place::from(p).project_deeper(&[PlaceElem::Deref], tcx); // (*p): i32
                let bq = Place::from(q).project_deeper(&[PlaceElem::Deref], tcx); // (*q): Pair
                let i32_ty = bp.ty(&*body, tcx).ty;
                let pair_ty = bq.ty(&*body, tcx).ty;
                let field0 = [PlaceElem::Field(FieldIdx::from_usize(0), i32_ty)]; // Pair.a : i32

                // MISMATCH: edge `(*p):i32`, access derefs to `Pair` with a Pair-field rest ⇒ fallback.
                match route_compose(tcx, &*body, bp, &field0, pair_ty) {
                    RoutedCompose::WholeCell(pl) => {
                        assert_eq!(pl, bp, "fallback must be the whole borrowed cell `(*p)`")
                    }
                    RoutedCompose::Composed(_) => {
                        panic!(
                            "type mismatch MUST fall back — composing feeds places_conflict a \
                                Field-of-Pair on an i32 place (unreachable!/Disjoint→UAF)"
                        )
                    }
                }
                // WELL-TYPED control: edge `(*q):Pair`, `deref_ty=Pair`, Pair-field rest ⇒ compose.
                match route_compose(tcx, &*body, bq, &field0, pair_ty) {
                    RoutedCompose::Composed(pl) => {
                        assert_eq!(
                            pl,
                            bq.project_deeper(&field0, tcx),
                            "well-typed composition"
                        )
                    }
                    RoutedCompose::WholeCell(_) => panic!("well-typed composition MUST compose"),
                }
            },
        );
    }

    // ===== §NB4-R — place-based cross-alias-write routing (RED-first, pre-implementation) =====
    //
    // Spec: docs/agents/tasks/2026-07-15-nb4r-place-based-routing-spec.md.
    //
    // WHAT THE ROUTING HOLE ACTUALLY IS (dump 2026-07-15, corrected from the spec's assumption): the
    // existing tree-borrow-GROUP machinery already produces cross-alias conflict edges for most
    // co-located views — a DIRECT copy view (`c=p`), a 2-hop writer (`c=b=p`), a field/cast writer —
    // are demoted TODAY without routing. The genuine hole is NARROW: a grouping-BROKEN view (a call
    // return `c=id(p)`, keyed under the base cell but NOT linked to the writer by a group loan) written
    // through a SIMPLE 1-hop / deref / reconverging sibling. There, `*b=…` looks up the EMPTY `row(b)`
    // and leaves `c` at `Ref`. Routing composes the write onto the loan's BORROWED place, sends it to
    // `row(base)`, and demotes `c` to `Raw`.
    //
    // So the fixtures split two ways:
    //   * RED FLIPS (view `Ref` today, `Raw` after routing) — the isolating tests: `sibling_copies`
    //     (1-hop), `deref_chain_no_crash` (multi-level), `reconverging_dag_bounded` (multi-writer).
    //   * CRASH-SAFETY / NO-REGRESSION CONTROLS (view already `Raw`, or `Ref` in both states) — routing
    //     must FIRE on these composition shapes without panicking or regressing: `copy_of_copy`
    //     (2-hop), `field_local_source` (leading-Field — the reverted crash), `type_pun_invalidates`
    //     (cast whole-cell fallback — the `places_conflict` `unreachable!` class), `offset_excluded`
    //     (offset shape), `reborrow_self_write_survives` (self-skip → `Ref`), `no_alias_ablation`
    //     (inert → `Ref`). These are NOT RED.

    /// §NB4-R RED (Amendment 3a) — **1-hop sibling, call-return view.** `b=p` (writer) and `c=id(p)`
    /// (a call-return alias of `(*p)`) address the same cell, but `c` is NOT tree-borrow-grouped with
    /// `b` (a call return is not a copy rvalue), so `*b=5` — which looks up the EMPTY `row(b)` — leaves
    /// `c` at `Ref` today (the S2-6 hole; direct `c=p` is grouped-demoted and would NOT isolate
    /// routing — confirmed by dump 2026-07-15). Routing walks `b`'s issued loan to `row(p)` and demotes
    /// `c`. One hop (`b→p`); contrast `nb4r_copy_of_copy`.
    #[test]
    fn nb4r_sibling_copies() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let b = p; let c = id(p); let r0 = *c; *b = 5; r0 + *c }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["c"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`c` (call-return view of (*p), live across `*b=5`) must be demoted: routing sends \
                     the write through `b`'s issued loan (borrowed=(*p)) to `row(p)` (S2-6 closure, 1-hop)."
                );
            },
        );
    }

    /// §NB4-R CONTROL (crash-safety, 2-hop composition) — writer `c = b = p`; `*c=5` makes routing
    /// walk `c→b→p` (PRE-order visited discipline). The call-return view `v=id(p)` is already demoted
    /// TODAY by the group machinery (a 2-hop writer links to the view's cell via group loans), so this
    /// is NOT a flip — it guards that the multi-hop walk does not crash or regress `v` off `Raw`.
    #[test]
    fn nb4r_copy_of_copy() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let v = id(p); let b = p; let c = b; let r0 = *v; *c = 5; r0 + *v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["v"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`v` stays `Raw`: the 2-hop routing walk c→b→p must terminate cleanly and not \
                     regress the (already group-demoted) view."
                );
            },
        );
    }

    /// §NB4-R CONTROL (crash-safety, leading-Field composition) — writer `b = h.q` builds
    /// `borrowed=(*(h.q)) = [Field(q), Deref]` — LAST element `Deref` (a copy of a field pointer), so
    /// it IS a chain edge (the reverted `first==Deref` filter wrongly dropped it, §11-B). Compose
    /// routes `*b=5` onto `(*(h.q))` (type-valid); the reverted `Local` re-base produced `(*h)` (a
    /// STRUCT deref → `places_conflict` crash). The view `v=id(h.q)` is already group-demoted, so this
    /// guards that leading-Field composition routes without the crash — not a flip.
    #[test]
    fn nb4r_field_local_source() {
        run_compiler(
            &format!(
                "{NB4_ID} #[repr(C)] struct H {{ q: *mut i32 }} \
                 unsafe fn f(mut h: H) -> i32 \
                 {{ let v = id(h.q); let b = h.q; let r0 = *v; *b = 5; r0 + *v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["v"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`v` stays `Raw`: leading-Field composition onto `(*(h.q))` must route without the \
                     struct-deref crash the `Local` re-base hit."
                );
            },
        );
    }

    /// §NB4-R RED — **multi-level deref, no crash.** writer `inner = *pp` builds `borrowed=(**pp) =
    /// [Deref, Deref]` — the exact shape the reverted re-base crashed on (`places_conflict`
    /// `unreachable!`). Compose routes `*inner=5` to `(**pp)` cleanly and demotes the call-return view
    /// `v=id(*pp)` (keyed under `pp`).
    #[test]
    fn nb4r_deref_chain_no_crash() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(pp: *mut *mut i32) -> i32 \
                 {{ let inner = *pp; let v = id(*pp); let r0 = *v; *inner = 5; r0 + *v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["v"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`v` (call-return view of *pp) is demoted by `*inner=5` via the multi-level chain \
                     to `(**pp)` — routes clean where the old rule panicked."
                );
            },
        );
    }

    /// §NB4-R CONTROL (Amendment 3b — type-pun whole-cell fallback; no-crash + invalidation) — writer
    /// `b = p as *mut Pair` casts the pointee type; `(*b).a = 5` would compose `(*p):i32 ++ [Field(a)]`
    /// which is ILL-TYPED. The type-check MUST catch this and fall back to whole-cell `(*p)` Deep — if
    /// it instead emitted the composed place, `places_conflict` would `unreachable!` (panic) or return
    /// `Disjoint` (silent miss → UAF). `w=id(p)` ends `Raw` (invalidated, not silently missed).
    ///
    /// ISOLATION CAVEAT (dump 2026-07-15): the cast operand is a compiler-inserted copy of `p`
    /// (`_5=copy _1; _4=_5 as Pair`), which the group machinery links to the view's cell, so `w` is
    /// already `Raw` today. The fallback's positive effect therefore CANNOT be isolated as a `Ref→Raw`
    /// flip in a minimal fixture; this test guards the two properties that ARE testable here — the
    /// type-check prevents the `places_conflict` crash (no panic) and the write does invalidate `w`
    /// (`Raw`, not silently dropped). Reported to the user as a deviation from Amendment 3b's "isolate
    /// the fallback" wording, with this structural reason.
    #[test]
    fn nb4r_type_pun_invalidates() {
        run_compiler(
            &format!(
                "{NB4_ID} #[repr(C)] struct Pair {{ a: i32, b: i32 }} \
                 unsafe fn f(p: *mut i32) -> i32 \
                 {{ let w = id(p); let b = p as *mut Pair; let r0 = *w; (*b).a = 5; r0 + *w }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["w"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`w` stays `Raw`: the ill-typed cast composition must fall back to whole-cell `(*p)` \
                     Deep — no `places_conflict` panic, and the write is NOT silently missed."
                );
            },
        );
    }

    /// §NB4-R RED (walk-bound smoke) — reconverging copy chains (`s→a→p`, `s2→b→p`) must terminate
    /// within the N cap and still demote the call-return view `v=id(p)`. PRE-order visited-marking
    /// keeps the reconvergence at `p` from re-expanding; the impl's per-site cap asserts it.
    #[test]
    fn nb4r_reconverging_dag_bounded() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let a = p; let b = p; let s = a; let s2 = b; let v = id(p); \
                    let r0 = *v; *s = 1; *s2 = 2; r0 + *v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["v"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`v` demoted by the routed writes; the reconverging chains terminate (no hang/panic)."
                );
            },
        );
    }

    /// §NB4-R CONTROL (offset shape — no crash) — writer `r = p.offset(1)` builds the copy-identical
    /// `borrowed=(*p)` but addresses a DIFFERENT cell (`p+1`), so routing EXCLUDES it as a chain edge
    /// (§4.1 coupling guard). Here the view `c=id(p)` is already demoted by the existing engine's
    /// handling of the offset write (dump 2026-07-15: `c=Raw` today), so this shape cannot isolate the
    /// −17.7% over-demotion the exclusion prevents — that guard lives at the CORPUS gate (§8). This
    /// unit only pins that routing handles the offset shape without a crash/regression.
    #[test]
    fn nb4r_offset_excluded() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let c = id(p); let r = p.offset(1); let v0 = *c; *r = 9; v0 + *c }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["c"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`c` stays `Raw` (already demoted by the existing offset-write handling); routing \
                     with offset EXCLUDED must not crash or regress it. The over-demotion guard is the \
                     corpus gate, not this unit."
                );
            },
        );
    }

    /// §NB4-R CONTROL (self-loan skip — finding C) — `b = p; *b = 5; *b`. `b` is the SOLE alias and
    /// writes through itself; routing reaches `b`'s OWN loan in `row(p)` (keyed under p, not b), which
    /// must be SKIPPED (`assigned == Assign(b)`) or `b` self-demotes. `b` stays `Ref` (a valid `&mut`)
    /// in BOTH states. Without the skip, every `let b=&mut *p; *b=…` reborrow would regress.
    #[test]
    fn nb4r_reborrow_self_write_survives() {
        run_compiler(
            "unsafe fn f(p: *mut i32) -> i32 { let b = p; *b = 5; *b }",
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["b"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Ref),
                    "`b` writes through itself as the sole alias — a valid `&mut`. Routing must skip \
                     `b`'s own loan (self-loan skip) or it spuriously self-demotes."
                );
            },
        );
    }

    /// §NB4-R CONTROL (ablation — byte-identical) — a shared view with NO cross-alias write anywhere
    /// stays `Ref` in BOTH states. Routing must not perturb a program with nothing to route.
    #[test]
    fn nb4r_no_alias_ablation() {
        run_compiler(
            "unsafe fn f(p: *mut i32) -> i32 { let c = p; let r0 = *c; let r1 = *c; r0 + r1 }",
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["c"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Ref),
                    "no write ⇒ `c` stays a shared `&` view; routing is inert here."
                );
            },
        );
    }

    /// Multiset difference for the §NB3-3c divergence delta: `a` minus `b`, each `b` element removing
    /// exactly ONE `a` element (multiplicity-preserving, so a duplicated or dropped edge is not
    /// masked). Module-level so `nb3c_divergence_delta_multiplicity` can guard it directly.
    fn multiset_diff(a: &[String], b: &[String]) -> Vec<String> {
        let mut remaining: std::collections::BTreeMap<&String, usize> =
            std::collections::BTreeMap::new();
        for x in b {
            *remaining.entry(x).or_default() += 1;
        }
        let mut out = vec![];
        for x in a {
            match remaining.get_mut(x) {
                Some(c) if *c > 0 => *c -= 1,
                _ => out.push(x.clone()),
            }
        }
        out
    }

    /// Guards the §NB3-3c divergence DELTA (Codex F3): the multiplicity-preserving symmetric
    /// difference must (a) be empty for equal multisets, (b) CHANGE when an edge within a case
    /// changes, and (c) not mask a dropped duplicate. Without this, once 3c-ii allowlists a case,
    /// edges shifting inside it would leave the case-ID present and the gate green.
    #[test]
    fn nb3c_divergence_delta_multiplicity() {
        let s = |xs: &[&str]| xs.iter().map(|x| x.to_string()).collect::<Vec<_>>();
        // (a) equal ⇒ empty both ways.
        assert!(multiset_diff(&s(&["A", "B"]), &s(&["B", "A"])).is_empty());
        // (b) a within-case edge change (fork C→D) alters the fork-only side of the delta.
        let prod = s(&["A", "B"]);
        let before = multiset_diff(&s(&["A", "C"]), &prod); // fork_only when fork = {A,C}
        let after = multiset_diff(&s(&["A", "D"]), &prod); // fork_only when fork = {A,D}
        assert_eq!(before, s(&["C"]));
        assert_ne!(
            before, after,
            "changing an edge within a case must change the delta"
        );
        // (c) multiplicity: a dropped DUPLICATE is surfaced, not masked by the other copy.
        assert_eq!(multiset_diff(&s(&["A", "A"]), &s(&["A"])), s(&["A"]));
    }

    /// §NB3-3c EQUIVALENCE SUCCESSOR — replaces the two retired 3a byte/multiset-equivalence
    /// fixtures (`nb3a_fork_engine_edges_match_production`, `nb3a_fork_engine_multiset_matches_mixed_replay`).
    ///
    /// 3a's job was pre-divergence faithfulness: fork == production on every case. 3c is the first
    /// deliberate divergence (3c-ii injects origins), so the gate's shape changes from "fork ==
    /// production, always" to "**fork == production modulo an ENUMERATED divergence list**". This is
    /// that successor. It collects the case-ID of every (program, mode) where the fork's conflict-edge
    /// MULTISET differs from production's, and asserts that divergence set EQUALS
    /// `FORK_PRODUCTION_DIVERGENCE` — both directions, exactly as the §0.2 dependency ratchet does:
    ///   - fork≠prod on an un-enumerated case → fails (a divergence must be declared, with its cause);
    ///   - an enumerated case that no longer diverges → fails (the list must shrink to match reality).
    ///
    /// **At 3c-i the list is EMPTY:** origins are computed but NOT injected, so the fork is still
    /// byte/multiset-equal to production on every case — the successor proves itself against the (still
    /// present) 3a gate before any divergence exists, which is the correct retirement sequence. 3c-ii's
    /// injection commit adds one case-ID per program×mode its new interprocedural conflicts perturb.
    ///
    /// Covers BOTH 3a fixtures' inputs: the uniform program×mode differential (round-0 across
    /// mutability; replaying across raw-candidacy × mutability, all-Ref base) AND the mixed-Raw/Ref
    /// replay (r0/r1/r2 Raw, keep Ref). Comparison is order-INSENSITIVE (`multiset`): loan-ID / edge
    /// order is non-contractual (production's `UnionFind` walks a seed-randomized `std::HashSet`); the
    /// contractual chain is **same edge multiset per replay ⇒ same demotion set ⇒ same accepted model**.
    #[test]
    fn nb3c_fork_equals_production_modulo_divergence() {
        use std::collections::BTreeMap;

        use rustc_hash::FxHashMap;
        use rustc_span::def_id::LocalDefId;

        use crate::analyses::{
            borrow::{self, ConflictEdge},
            borrow_ownership::borrow_engine,
        };

        // 3c-i: EMPTY. 3c-ii enumerates deliberate divergences here as (case-ID, expected DELTA)
        // pairs — case-ID is "{program}/round0/mut=.." | "{program}/replay/raw=../mut=.." |
        // "mixed_replay"; the DELTA is the canonical per-case prod-vs-fork edge symmetric-difference
        // string (`case_delta`). Enumerating the DELTA (not just the ID) means edges CHANGING within
        // an already-allowed divergence still fails the gate (Codex F3).
        // §NB4-R cross-alias-WRITE routing divergence class (2026-07-15). Fork routes the write
        // `*b=5` through `b`'s issued loan to the aliased loan (the S2-6 closure); production is
        // structurally blind. SOUND DIRECTION — every entry is `prod_only=[]` (fork ⊇ production;
        // fork only ADDS conflict edges, never drops one), so the fork is strictly more conservative.
        // Surfaces only in forced-`mut=true` (the gate's all-mutable mode); the real fact-mut flip is
        // proven by `nb2_cross_alias_write_uncaught_witness` (state-3). Routing is gated to WRITE
        // accesses, so read-only cases (`raw_copies`) do NOT diverge.
        const FORK_PRODUCTION_DIVERGENCE: &[(&str, &str)] = &[
            (
                "call_return_write/round0/mut=true",
                "prod_only=[] fork_only=[\"DefId(0:4 ~ rust_out[96a3]::f) issuer=Some(Local(_4)) requirers=[\\\"Local(_5)\\\"]\"]",
            ),
            (
                "call_return_write/replay/raw=false/mut=true",
                "prod_only=[] fork_only=[\"DefId(0:4 ~ rust_out[96a3]::f) issuer=Some(Local(_4)) requirers=[\\\"Local(_5)\\\"]\"]",
            ),
        ];

        // Order-INSENSITIVE canonical edge multiset (per-fn key embedded), for prod-vs-fork equality.
        fn multiset(m: &FxHashMap<LocalDefId, Vec<ConflictEdge>>) -> Vec<String> {
            let mut out: Vec<String> = m
                .iter()
                .flat_map(|(k, edges)| {
                    edges.iter().map(move |e| {
                        let mut rs: Vec<String> =
                            e.requirers.iter().map(|o| format!("{o:?}")).collect();
                        rs.sort();
                        format!("{k:?} issuer={:?} requirers={rs:?}", e.issuer)
                    })
                })
                .collect();
            out.sort();
            out
        }

        // The per-case divergence DELTA (Codex F3): the multiplicity-preserving symmetric difference
        // of the prod vs fork edge multisets, as a canonical string. `None` ⇔ multisets equal (no
        // divergence). Comparing the DELTA (not just a case ID) makes a change to the edges WITHIN an
        // already-enumerated divergence fail the gate.
        fn case_delta(
            prod: &FxHashMap<LocalDefId, Vec<ConflictEdge>>,
            fork: &FxHashMap<LocalDefId, Vec<ConflictEdge>>,
        ) -> Option<String> {
            let (p, f) = (multiset(prod), multiset(fork));
            let prod_only = multiset_diff(&p, &f);
            let fork_only = multiset_diff(&f, &p);
            (!prod_only.is_empty() || !fork_only.is_empty())
                .then(|| format!("prod_only={prod_only:?} fork_only={fork_only:?}"))
        }

        // (stable case-ID root, source) — the 3a fixture-1 program family.
        let programs: [(&str, &str); 5] = [
            // aliasing &mut borrows of one local, both live → conflict (all-mut)
            (
                "mut_alias",
                "unsafe fn f() { let mut x = 0i32; let p = &mut x as *mut i32; \
                 let q = &mut x as *mut i32; *p = 1; *q = 2; }",
            ),
            // aliasing borrows with reads (exercises mutability-dependent conflict)
            (
                "mut_alias_reads",
                "unsafe fn f() { let mut x = 0i32; let a = &mut x as *mut i32; \
                 let b = &mut x as *mut i32; let u = *a; let v = *b; let _ = (u, v); }",
            ),
            // *mut *mut aliasing outer pointers + a call (the out-param shape)
            (
                "outparam_call",
                "unsafe fn g(o: *mut *mut i32) { let _ = o; } \
                 unsafe fn f() { let mut local: *mut i32 = core::ptr::null_mut(); \
                 let p = &mut local as *mut *mut i32; let q = &mut local as *mut *mut i32; \
                 g(p); *q = core::ptr::null_mut(); }",
            ),
            // raw-pointer copies (no borrows) → empty map (agreement on empty is still a real check)
            (
                "raw_copies",
                "unsafe fn f(mut p: *mut i32) -> i32 { let a = p; let b = p; *a + *b }",
            ),
            // call-return alias + write (the S2-6 shape — the case 3c-ii origins will diverge on)
            (
                "call_return_write",
                "#[inline(never)] unsafe fn id(mut p: *mut i32) -> *mut i32 { p } \
                 unsafe fn f(mut p: *mut i32) -> i32 { let b = p; let x = id(p); let z = x; let r0 = *z; *b = 5; r0 + *z }",
            ),
        ];

        let mut diverged: BTreeMap<String, String> = BTreeMap::new();

        // Non-vacuity guard (from 3a fixture-1): aliasing &mut borrows of one local, both live, MUST
        // produce a conflict edge — proves the differential is not comparing empty==empty.
        run_compiler(programs[0].1, |tcx| {
            let program = collect_program(tcx);
            let edges = borrow::borrow_conflicts(
                &program,
                |_: LocalDefId| |_: Local| true,
                |_: LocalDefId| |_: Local| true,
            );
            assert!(
                !edges.is_empty(),
                "non-vacuity: aliasing &mut borrows must produce a conflict edge"
            );
        });

        for (label, src) in programs {
            run_compiler(src, |tcx| {
                let program = collect_program(tcx);
                // round-0 (`borrow_conflicts`) across mutability:
                for mutb in [true, false] {
                    let prod = borrow::borrow_conflicts(
                        &program,
                        |_: LocalDefId| |_: Local| true,
                        move |_: LocalDefId| move |_: Local| mutb,
                    );
                    let fork = borrow_engine::borrow_conflicts(
                        &program,
                        |_: LocalDefId| |_: Local| true,
                        move |_: LocalDefId| move |_: Local| mutb,
                    );
                    if let Some(d) = case_delta(&prod, &fork) {
                        diverged.insert(format!("{label}/round0/mut={mutb}"), d);
                    }
                }
                // replaying across raw-candidacy × mutability, all-Ref base:
                for raw in [false, true] {
                    for mutb in [true, false] {
                        let prod = borrow::borrow_conflicts_replaying(
                            &program,
                            |_: LocalDefId| |_: Local| true,
                            move |_: LocalDefId| move |_: Local| raw,
                            move |_: LocalDefId| move |_: Local| mutb,
                        );
                        let fork = borrow_engine::borrow_conflicts_replaying(
                            &program,
                            |_: LocalDefId| |_: Local| true,
                            move |_: LocalDefId| move |_: Local| raw,
                            move |_: LocalDefId| move |_: Local| mutb,
                            &[], /* §NB5-F2: no field candidacy → fork matches production's field handling */
                        );
                        if let Some(d) = case_delta(&prod, &fork) {
                            diverged.insert(format!("{label}/replay/raw={raw}/mut={mutb}"), d);
                        }
                    }
                }
            });
        }

        // The 3a fixture-2 mixed-Raw/Ref replay (r0/r1/r2 Raw, keep Ref) — the loan-ID-order stressor.
        run_compiler(
            r#"
unsafe fn f() {
    let mut cell = 0i32;
    let r0 = &mut cell as *mut i32;
    let r1 = &mut cell as *mut i32;
    let r2 = &mut cell as *mut i32;
    let keep = &mut cell as *mut i32;
    let k0 = keep;
    *r0 = 1;
    let k1 = keep;
    *r1 = 2;
    let k2 = keep;
    *r2 = 3;
    let s = *keep;
    let _ = (k0, k1, k2, s);
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let rl: [Local; 3] = [
                    local_by_var_name(tcx, f, "r0"),
                    local_by_var_name(tcx, f, "r1"),
                    local_by_var_name(tcx, f, "r2"),
                ];
                let rl = &rl;
                let prod = borrow::borrow_conflicts_replaying(
                    &program,
                    |_: LocalDefId| |_: Local| true,
                    move |_fd: LocalDefId| move |local: Local| rl.contains(&local),
                    |_: LocalDefId| |_: Local| true,
                );
                let fork = borrow_engine::borrow_conflicts_replaying(
                    &program,
                    |_: LocalDefId| |_: Local| true,
                    move |_fd: LocalDefId| move |local: Local| rl.contains(&local),
                    |_: LocalDefId| |_: Local| true,
                    &[], // §NB5-F2: no field candidacy → fork matches production's field handling
                );
                assert!(
                    !prod.is_empty(),
                    "non-vacuity: the mixed replay must produce conflict edges"
                );
                if let Some(d) = case_delta(&prod, &fork) {
                    diverged.insert("mixed_replay".to_string(), d);
                }
            },
        );

        let expected: BTreeMap<String, String> = FORK_PRODUCTION_DIVERGENCE
            .iter()
            .map(|(id, delta)| (id.to_string(), delta.to_string()))
            .collect();
        assert_eq!(
            diverged, expected,
            "fork vs production per-case divergence DELTAs != enumerated FORK_PRODUCTION_DIVERGENCE.\n  \
             A case-ID on one side only is a new/removed divergence; a case-ID on both sides with a \
             DIFFERENT delta is a changed (possibly regressed) divergence — all fail.\n  \
             observed: {diverged:#?}\n  expected: {expected:#?}"
        );
    }

    /// B3b headline: interprocedural ownership flow across a *return* edge.
    /// `make` allocates and returns ownership; `forward` just returns `make()`'s
    /// result. `forward` contains no `malloc` and no sink, so the *only* path to
    /// ownership in `forward`'s return slot is `Boundary::call` linking
    /// `dest.def = make.ret` (and `make.ret` being owning, which requires `make`'s
    /// body to have been emitted). If that cross-function edge were absent,
    /// `forward`'s return would be soft-objective non-owning — so the assertion
    /// is non-vacuous (a local sink cannot satisfy it, unlike a `free(p)` shape).
    /// `selectors.all().len() == 1` independently proves `make`'s source was emitted by
    /// the crate driver; single-fn emission of `forward` alone would instead
    /// panic on the local call to `make` (absent from a self-entry `InterCtxt`).
    #[test]
    fn interproc_alloc_return_flows_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn make() -> *mut core::ffi::c_void {
    unsafe { malloc(4) }
}

pub unsafe fn forward() -> *mut core::ffi::c_void {
    unsafe { make() }
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let make = function_by_name(&program, "make");
                let forward = function_by_name(&program, "forward");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B3b crate emission should run");

                // The only malloc is in `make`; a selector here proves `make`'s
                // body was emitted by the crate driver (emitting `forward` alone
                // would see zero sources).
                assert_eq!(selectors.all().len(), 1);

                // Return locals (Local 0) at depth 0.
                let make_ret = local_slot(&slots, make, Local::from_u32(0), 0);
                let forward_ret = local_slot(&slots, forward, Local::from_u32(0), 0);

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                // Diagnostic: `make_ret` owning proves `make` was emitted owning;
                // `forward_ret` owning proves the cross-function return edge carried
                // it. A broken edge fails `forward_ret` while `make_ret` still holds.
                assert_eq!(
                    model.get(&make_ret),
                    Some(&SlotKind::Owning),
                    "`make` must return Owning (its malloc source emitted)"
                );
                assert_eq!(
                    model.get(&forward_ret),
                    Some(&SlotKind::Owning),
                    "ownership from `make` must flow across the call into `forward`'s return"
                );
            },
        );
    }

    /// B4 (escape-half retirement): with `output_params` retired, a pointer param
    /// the body only *reads* through must NOT be promoted to `Owning`. Escape is
    /// decided natively now — nothing forces `p` owning, so the soft objective
    /// (prefers Ref) settles its depth-0 slot to `Ref`. This is the anti-regression
    /// guard for the uniform two-slot change: it is RED if the input owning seeds
    /// are kept (they would hard-force `p` `Owning`), GREEN once they are dropped.
    #[test]
    fn read_only_input_arg_is_ref() {
        run_compiler(
            r#"
pub unsafe fn reader(p: *mut i32) -> i32 {
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let reader = function_by_name(&program, "reader");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B4 crate emission should run");

                // `p` is param Local 1; read-only, so its depth-0 slot must be Ref.
                let p = local_slot(&slots, reader, Local::from_u32(1), 0);
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Ref),
                    "a read-only input pointer param must stay Ref, not be promoted to Owning"
                );
            },
        );
    }

    /// B4b probe: a local call passing a (cast) pointer to a `*mut c_void` param.
    /// Post-B4a every arg is `Param::Output`, so the call flows through the `call`
    /// Output arm — which lacks the c_void range-narrowing the now-dead
    /// `Param::Normal` arm had. This checks the Output arm handles the c_void
    /// formal (a deeper actual cast down to c_void) without panicking, deciding
    /// whether B4b can drop the narrowing or must port it.
    #[test]
    fn c_void_local_call_arg_emits() {
        run_compiler(
            r#"
pub unsafe fn take_void(p: *mut core::ffi::c_void) {
    let _ = p;
}

pub unsafe fn caller(pp: *mut *mut i32) {
    unsafe { take_void(pp as *mut core::ffi::c_void) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let _take_void = function_by_name(&program, "take_void");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B4b: c_void local-call emission should run without panicking");

                assert!(
                    kind_solver.model_kinds_relaxing(&selectors).is_some(),
                    "the joint system stays satisfiable with a c_void local-call arg"
                );
            },
        );
    }

    /// B4b escape-half guard (Codex hardening): a pointer param passed *through*
    /// to a local callee. The `call` Output arm ties `p` to the callee's formal
    /// `q`; neither allocates nor frees, so both stay `Ref` (borrowed) — escape
    /// stays solved, not spuriously promoted to Owning across the interprocedural
    /// arg edge that B4a's uniform-Output change rewired.
    #[test]
    fn passed_through_param_stays_ref() {
        run_compiler(
            r#"
pub unsafe fn sink_it(q: *mut i32) {
    let _ = q;
}

pub unsafe fn passes_through(p: *mut i32) {
    unsafe { sink_it(p) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let sink_it = function_by_name(&program, "sink_it");
                let passes_through = function_by_name(&program, "passes_through");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B4b: pass-through emission should run");

                let p = local_slot(&slots, passes_through, Local::from_u32(1), 0);
                let q = local_slot(&slots, sink_it, Local::from_u32(1), 0);
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Ref),
                    "passed-through `p` stays Ref (no allocation escapes)"
                );
                assert_eq!(model.get(&q), Some(&SlotKind::Ref), "callee `q` stays Ref");
            },
        );
    }

    /// BB0 (§8 borrow seam): the verifier adapter. `revalidate` runs the production
    /// borrow pipeline with a BO-model-derived ref-candidacy (here all-Ref = Round-0)
    /// and maps the conflict edges back to BO `SlotRef`s. The fixture is the borrow
    /// analysis's own `proof_of_concept` conflict (production demotes `r2`), so the
    /// result must be NON-EMPTY (non-vacuous) and every involved slot must be a real
    /// depth-0 local slot of `f`. This proves candidacy-from-model + borrow_inference
    /// + error extraction + owner→SlotRef translation end-to-end.
    #[test]
    fn bb0_revalidate_maps_round0_borrow_conflict_to_slots() {
        run_compiler(
            r#"
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut r1 = p;
    let mut r2 = r1;
    let mut q = r1;
    *q = 1;
    *r1 = 2;
    *r2 = 3;
    *p = 4;
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let slots = CrateSlots::build(&program);

                // All-Ref Round-0 candidacy + all-mutable (so conflicts register —
                // `invalidates` skips immutable-base loans).
                let conflicts = revalidate(&program, &slots, |_| true, true);
                let f_conflicts = conflicts.get(&f).map(Vec::as_slice).unwrap_or(&[]);

                assert!(
                    !f_conflicts.is_empty(),
                    "all-Ref Round-0 borrow inference must surface the `r2` conflict"
                );

                // Every involved slot is a real depth-0 local of `f`.
                let involved: Vec<SlotRef> = f_conflicts
                    .iter()
                    .flat_map(|c| c.issuer.iter().chain(c.requirers.iter()).copied())
                    .collect();
                for s in &involved {
                    assert!(
                        matches!(s, SlotRef::Local(d, _) if *d == f),
                        "every involved slot is a depth-0 local of `f`, got {s:?}"
                    );
                }

                // The conflict is concretely attributed (not an empty edge): at least
                // one issuer, and `r2` — the local production ultimately demotes, so
                // necessarily a requirer of the round-0 invalid loan — is involved.
                assert!(
                    f_conflicts.iter().any(|c| c.issuer.is_some()),
                    "the conflict must carry a concrete issuer (the loan's assigned owner)"
                );
                let r2_slot = local_slot(&slots, f, local_by_var_name(tcx, f, "r2"), 0);
                assert!(
                    involved.contains(&r2_slot),
                    "`r2`'s depth-0 slot must be in the round-0 conflict; involved = {involved:?}"
                );
            },
        );
    }

    /// BB1 (§8 guard encoder): Round-0 borrow conflicts become `¬ref` exclusion
    /// clauses on the `KindSolver`. The `proof_of_concept` fixture (production demotes
    /// `r2`) has a genuine all-Ref reference-aliasing conflict but NO ownership source,
    /// so the bare BO solve (soft objective maxes Ref) makes every pointer slot `Ref`.
    /// Applying the guards must force >=1 conflict-involved slot OFF Ref. Two
    /// independent solvers prove the guard is the *sole* cause (non-vacuous): baseline
    /// = all Ref; guarded = >=1 non-Ref.
    #[test]
    fn bb1_guard_forces_conflict_slot_off_ref() {
        run_compiler(
            r#"
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut r1 = p;
    let mut r2 = r1;
    let mut q = r1;
    *q = 1;
    *r1 = 2;
    *r2 = 3;
    *p = 4;
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);

                let involved = ["p", "r1", "r2", "q"];
                let slot_of =
                    |name: &str| local_slot(&slots, f, local_by_var_name(tcx, f, name), 0);

                // Solver A — baseline (no guards). `f` has no ownership source, so the
                // soft objective settles every pointer slot to Ref. We assert on the
                // solved *model* (never `KindSolver::assume`, which is a hard constraint
                // — hard-assuming Ref then adding the exclusion would be UNSAT by
                // construction); the guard in Solver B is thus the only added hard fact.
                let solver_a = KindSolver::new(&slots);
                let (_a, selectors_a) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver_a,
                )
                .expect("BB1 baseline emission");
                add_coherence(&solver_a, &slots, f, &body);
                let model_a = solver_a
                    .model_kinds_relaxing(&selectors_a)
                    .expect("baseline satisfiable");
                for name in involved {
                    assert_eq!(
                        model_a.get(&slot_of(name)),
                        Some(&SlotKind::Ref),
                        "baseline (no guards): `{name}` should be Ref (max-ref, no source)"
                    );
                }

                // Solver B — same, plus BB1 guards from the Round-0 (all-Ref,
                // all-mutable) conflict. The guard `¬ref(issuer) ∨ ⋁¬ref(requirers)`
                // must demote >=1 involved slot off Ref.
                let solver_b = KindSolver::new(&slots);
                let (_b, selectors_b) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver_b,
                )
                .expect("BB1 guarded emission");
                add_coherence(&solver_b, &slots, f, &body);
                let conflicts = revalidate(&program, &slots, |_| true, true);
                materialize_guards(&solver_b, &conflicts);

                let model_b = solver_b
                    .model_kinds_relaxing(&selectors_b)
                    .expect("guarded satisfiable");
                let non_ref = involved
                    .iter()
                    .filter(|name| model_b.get(&slot_of(name)) != Some(&SlotKind::Ref))
                    .count();
                assert!(
                    non_ref >= 1,
                    "BB1 guards must force >=1 conflict-involved slot off Ref (all stayed Ref)"
                );
            },
        );
    }

    /// Caller-side out-param escape: a caller passes `&raw mut local` to a callee that
    /// writes `*out = malloc`. The malloc'd ownership flows back so the caller's `local`
    /// (depth-0 slot) becomes `Owning` after the call — the before/after caller state
    /// the legacy ownership analysis modeled, now carried by the uniform two-version
    /// use/def encoding at **precision 2** (the depth-1 signature var the `*out = malloc`
    /// escape flows through via the already-wired `call_args → call-matcher → exit-zip`
    /// path), rather than an output-param flag.
    ///
    /// `local` must be USED (returned) for the assertion to be non-vacuous: an unused
    /// owning `local` is a leak, which the solver models as non-owning (`Ref`) — the
    /// `bo-interproc-test-soundness` fixture trap. Closed by the §9.11 landing
    /// (precision-2 + `field ⟹ parent` suppression for struct-pointer pointees, so the
    /// escape lands without over-claiming borrowed struct pointers); the callee-side
    /// (`store_through_ptr_is_ref_over_owning`) and return-edge
    /// (`interproc_alloc_return_flows_owning`) escapes were already sound.
    #[test]
    fn caller_side_outparam_escape_flows_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn make(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}

pub unsafe fn caller() -> *mut core::ffi::c_void {
    let mut local: *mut core::ffi::c_void = core::ptr::null_mut();
    unsafe { make(&raw mut local) };
    local
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let make = function_by_name(&program, "make");
                let caller = function_by_name(&program, "caller");
                let make_body = tcx.mir_drops_elaborated_and_const_checked(make).borrow();
                let caller_body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("escape emission should run");
                add_coherence(&kind_solver, &slots, make, &make_body);
                add_coherence(&kind_solver, &slots, caller, &caller_body);

                let local = local_slot(&slots, caller, local_by_var_name(tcx, caller, "local"), 0);
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(
                    model.get(&local),
                    Some(&SlotKind::Owning),
                    "caller's `local` must become Owning after the out-param call"
                );
            },
        );
    }

    /// NON-REGRESSION (output-param contract, §9.8/§9.9): a borrowed struct pointer
    /// whose FIELD is malloc'd (`(*owner).data = malloc`) is a **field-ownership
    /// transfer**, NOT evidence that `owner` owns. Under the precision-2 escape
    /// support this must NOT over-claim `owner` as `Owning` — the `field ⟹ parent`
    /// suppression in `GlobalAssumptionApplier::apply` guarantees it. Without that
    /// suppression, global precision-2 forces `owner` `Owning` (the reverted §9.8
    /// regression, which the green suite otherwise MISSED — no other test exercises a
    /// borrowed struct-pointer param). This is the guard that keeps the escape support
    /// from re-introducing that over-claim.
    #[test]
    fn outparam_field_malloc_leaves_parent_ref() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub struct Holder {
    pub data: *mut core::ffi::c_void,
}

pub unsafe fn stash(owner: *mut Holder) {
    (*owner).data = unsafe { malloc(4) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let stash = function_by_name(&program, "stash");
                let stash_body = tcx.mir_drops_elaborated_and_const_checked(stash).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("stash emission should run");
                add_coherence(&kind_solver, &slots, stash, &stash_body);

                let owner = local_slot(&slots, stash, local_by_var_name(tcx, stash, "owner"), 0);
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_ne!(
                    model.get(&owner),
                    Some(&SlotKind::Owning),
                    "borrowed struct-pointer `owner` must NOT be Owning (field malloc is field-ownership transfer, not parent ownership)"
                );
            },
        );
    }

    /// NON-REGRESSION (precision-2 depth-chain over-claim, from a Codex adversarial
    /// review of the BB-escape landing): two aliasing `&mut local as *mut *mut T` outer
    /// pointers plus the caller-side out-param escape. The hypothesised hazard: the
    /// escape makes depth1 (`local`) Owning; a borrow conflict on `p`/`q` demotes depth0
    /// off `Ref`; the coherence invariant `¬(raw(d) ∧ own(d+1))` then forces the outer
    /// pointer (to STACK `local`) Owning — a UAF-class over-claim outside the fixed
    /// field⟹parent path.
    ///
    /// It does NOT manifest: the escape's Owning source is retractable, so the solver
    /// LEAKS the deeper allocation (`local` settles `Raw`, making `own(depth1)` false and
    /// releasing the coherence pressure) rather than over-claiming the stack pointer.
    /// Verified equal at precision 1 and 2 — precision-2 adds no new over-claim on this
    /// shape. (The non-retractable `free(local)` variant goes UNSAT and
    /// `verify_to_fixpoint` DECLINES — a sound conservative fallback, no wrong `Owning`
    /// — at BOTH precisions, i.e. pre-existing, so it is not encoded here.) This guards
    /// the outer slots against ever becoming `Owning`.
    #[test]
    fn outparam_escape_aliasing_outer_ptr_never_owning() {
        use crate::analyses::borrow_ownership::{
            borrow_engine::borrow_conflicts_with_flows, borrow_verify::verify_to_fixpoint_counting,
            origin_flow::analyze_program_origin_flow, retirement::local_outcome::Reason,
            source_events::SourceRole,
        };
        run_compiler(
            r#"
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
"#,
            |tcx| {
                let program = collect_program(tcx);
                let make = function_by_name(&program, "make");
                let caller = function_by_name(&program, "caller");
                let make_body = tcx.mir_drops_elaborated_and_const_checked(make).borrow();
                let caller_body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, make, &make_body);
                add_coherence(&solver, &slots, caller, &caller_body);

                // Preserve the ordinary alias-hazard assertion independently
                // of retirement's deliberately incomplete all-Ref inner probe.
                // This fact producer is not an acceptance/retirement bypass.
                let flows = analyze_program_origin_flow(&program);
                let round0 = borrow_conflicts_with_flows(
                    &program,
                    &flows,
                    |function| {
                        let universe = &slots.fn_local_slots[&function];
                        move |local| universe.slot_for_local_depth(local, 0).is_some()
                    },
                    |_function| |_local| true,
                );
                assert!(
                    round0.get(&caller).is_some_and(|e| !e.is_empty()),
                    "shape must be hazardous (aliasing outer-pointer borrow conflicts)"
                );

                let ((model, stats), export) = with_bo_export(|| {
                    verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, true)
                });

                let p = local_slot(&slots, caller, local_by_var_name(tcx, caller, "p"), 0);
                let q = local_slot(&slots, caller, local_by_var_name(tcx, caller, "q"), 0);
                let model = model.expect("R245 stack-holder coverage repair retains model");
                assert_ne!(model[&p], SlotKind::Owning);
                assert_ne!(model[&q], SlotKind::Owning);
                {
                    // Preserve stack non-ownership and exact deeper repair receipts.
                    let storage = local_by_var_name(tcx, caller, "local");
                    let universe = &slots.fn_local_slots[&caller];
                    let expected: FxHashSet<_> = (0..universe.len())
                        .filter_map(|index| {
                            let id = SlotId::from_usize(index);
                            (universe.slot(id).depth == 1).then_some(SlotRef::Local(caller, id))
                        })
                        .collect();
                    assert_eq!(
                        expected.len(),
                        5,
                        "the five actual deeper outer-pointer aliases"
                    );
                    let review = export
                        .source_retirement
                        .as_ref()
                        .expect("typed stack-storage decline");
                    assert_eq!(stats.source_retirement_decline, review.unresolved);
                    assert!(review.unresolved.is_empty());
                    let rows = export
                        .retirement_rounds
                        .iter()
                        .flat_map(|round| &round.demotions)
                        .collect::<Vec<_>>();
                    assert!(!rows.is_empty());
                    let mut actual = FxHashSet::default();
                    for row in &rows {
                        assert_eq!(row.reason.inner_loan_depth(), Some(1));
                        let slot = row.holder;
                        assert!(expected.contains(&slot));
                        for target in &row.chain {
                            assert_eq!(model[target], SlotKind::Raw);
                            if expected.contains(target) {
                                actual.insert(*target);
                            }
                        }
                        let event = &row.source;
                        assert_eq!(event.function, "caller");
                        assert_eq!(event.storage_local, Some(storage.as_u32()));
                        assert!(matches!(
                            event.role,
                            SourceRole::UnwindStorage | SourceRole::StorageDead
                        ));
                        assert_eq!(row.function, caller);
                        assert_eq!(row.phase, event.phase);
                        assert_eq!(
                            row.location,
                            Location {
                                block: rustc_middle::mir::BasicBlock::from_u32(event.block),
                                statement_index: event.statement
                            }
                        );
                        assert!(row.route.is_empty());
                    }
                    assert_eq!(actual, expected);
                    assert!(
                        export
                            .retirement_rounds
                            .iter()
                            .any(|round| round.conflicts.iter().any(|row| row.loan.is_some())),
                        "ordinary alias witnesses remain visible"
                    );
                    assert!(export.residual_conflicts.is_some());
                }
            },
        );
    }

    /// PROBE (headline-reframing rationale): storing a global address through `*out`
    /// does NOT produce a round-0 *borrow* conflict — `&raw mut G` is a 'static-region
    /// raw borrow of a static, not a reference-aliasing loan. This confirms the
    /// `*out = g` exclusivity hazard is an *ownership* concern (a global is a
    /// non-owning source), not a borrow one, which is why BB1's headline uses the
    /// `proof_of_concept` reference-aliasing conflict instead.
    #[test]
    fn store_global_through_outparam_no_borrow_conflict() {
        run_compiler(
            r#"
static mut G: i32 = 0;

pub unsafe fn store_global(out: *mut *mut i32) {
    *out = &raw mut G;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let store_global = function_by_name(&program, "store_global");
                let slots = CrateSlots::build(&program);

                let conflicts = revalidate(&program, &slots, |_| true, true);
                let edges = conflicts
                    .get(&store_global)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                assert!(
                    edges.is_empty(),
                    "storing a global address through `*out` is not a borrow conflict; got {edges:?}"
                );
            },
        );
    }

    /// BB2-i (§8 CEGAR validate seam, union replay) through the BO `SlotRef` API.
    /// Two `&mut local` borrows: marking `x`'s slot `Raw` (production's iteration-1
    /// demotion) must, under replay, surface `y`'s conflict via the `tree_borrow_local`
    /// union — which plain `revalidate` (round-0, no union) does not. Mirrors the
    /// borrow-side `bb2i_replay_surfaces_union_induced_conflict` through the slot space.
    #[test]
    fn bb2i_revalidate_replaying_surfaces_union_induced_slot_conflict() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut local = 0i32;
    let x = &mut local as *mut i32;
    let y = &mut local as *mut i32;
    *x = 1;
    *y = 2;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let slots = CrateSlots::build(&program);
                let x = local_slot(&slots, f, local_by_var_name(tcx, f, "x"), 0);
                let y = local_slot(&slots, f, local_by_var_name(tcx, f, "y"), 0);

                let involves_y = |conflicts: &FxHashMap<LocalDefId, Vec<_>>| {
                    conflicts.get(&f).is_some_and(|edges: &Vec<SlotConflict>| {
                        edges
                            .iter()
                            .any(|e| e.issuer == Some(y) || e.requirers.contains(&y))
                    })
                };

                // Candidacy: `x` Raw, everything else Ref.
                let is_ref = |s: SlotRef| s != x;
                let is_raw = |s: SlotRef| s == x;

                // Round-0 `revalidate` (no union): `y = &mut local` alone is sound — no
                // conflict at all for `f`. Emptiness pins the union as the sole cause.
                let bb0 = revalidate(&program, &slots, is_ref, true);
                assert!(
                    bb0.get(&f).map_or(true, |edges| edges.is_empty()),
                    "round-0 revalidate must find NO conflict for f; got {bb0:?}"
                );

                // Replay: demote `x` + union(x, local) ⇒ `y` conflicts.
                let replay = revalidate_replaying(&program, &slots, is_ref, is_raw, true);
                assert!(
                    involves_y(&replay),
                    "replay must surface the union-induced y conflict; got {replay:?}"
                );
            },
        );
    }

    /// BB2-ii (§8 CEGAR iteration loop, Mode A). On the two-`&mut local` fixture a single
    /// demotion is *insufficient*: demoting one involved slot's `Raw` union surfaces a
    /// further conflict under replay, so `verify_to_fixpoint` must iterate (commit `¬ref`
    /// on a representative → re-solve) until conflict-free. The necessity is the contrast
    /// asserted below: a single-step demotion (what a BB1 one-shot reaches) leaves a
    /// residual, while the loop's fixpoint is clean.
    ///
    /// Because both pointers share one base (`local`) and the conflict is asymmetric
    /// (creating the 2nd borrow invalidates the 1st's live loan), each monotone single-slot
    /// commit's `tree_borrow_local` union re-surfaces a fresh self-conflict, cascading until
    /// ALL of this fn's pointer slots are `Raw` — a sound but non-minimal "give up on every
    /// borrow" fixpoint. (`bb2ii_preserves_independent_borrow` shows the loop instead keeps
    /// an *independent* borrow `Ref`; that test carries the non-vacuous clean assertion.)
    #[test]
    fn bb2ii_cegar_loop_reaches_union_clean_fixpoint() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut local = 0i32;
    let x = &mut local as *mut i32;
    let y = &mut local as *mut i32;
    *x = 1;
    *y = 2;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);

                // --- Necessity (deterministic): a single round-0 guard is NOT a fixpoint. ---
                // The round-0 conflict admits a single-slot demotion — its requirer alone —
                // that a one-shot disjunctive guard could pick (a valid max-ref choice). Yet
                // demoting just that slot induces a `tree_borrow_local` union that surfaces a
                // *further* conflict under replay. Only BB2-ii's re-validation loop catches
                // that. Asserting this directly (not via the solver) is robust to z3's
                // tie-break between the equally-good issuer/requirer demotions.
                let round0 = revalidate(&program, &slots, |_| true, true);
                let requirer = *round0
                    .get(&f)
                    .and_then(|edges| edges.first())
                    .and_then(|edge| edge.requirers.first())
                    .expect("round-0 conflict with a requirer");
                let residual = revalidate_replaying(
                    &program,
                    &slots,
                    |s: SlotRef| s != requirer,
                    |s: SlotRef| s == requirer,
                    true,
                );
                assert!(
                    residual.get(&f).is_some_and(|e| !e.is_empty()),
                    "demoting the round-0 requirer alone must leave a union-induced residual \
                     (the re-validation loop is necessary); got {residual:?}"
                );

                // --- BB2-ii loop reaches the clean fixpoint. ---
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges to a SAT model");

                // Non-trivial: the conflict forced a real demotion — ≥1 pointer slot is
                // Raw. Checking `== Raw` (not `!= Ref`) attributes it to the borrow path:
                // f has no ownership source, so a borrow commit is the only Raw producer
                // (an unrelated Owning slot could satisfy `!= Ref` without any demotion).
                let demoted_to_raw = body.local_decls.indices().any(|local| {
                    slots
                        .fn_local_slots
                        .get(&f)
                        .and_then(|u| u.slot_for_local_depth(local, 0))
                        .and_then(|sid| model.get(&SlotRef::Local(f, sid)))
                        == Some(&SlotKind::Raw)
                });
                assert!(
                    demoted_to_raw,
                    "fixpoint must demote >=1 pointer slot to Raw; got {model:?}"
                );

                // The accepted model is genuinely conflict-free under replay.
                let clean = revalidate_replaying(
                    &program,
                    &slots,
                    |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref),
                    |s: SlotRef| model.get(&s) == Some(&SlotKind::Raw),
                    true,
                );
                assert!(
                    clean.get(&f).map_or(true, |e| e.is_empty()),
                    "fixpoint model must be conflict-free under replay; got {clean:?}"
                );
            },
        );
    }

    /// BB2-ii non-vacuous fixpoint: an INDEPENDENT borrow (distinct base) stays Ref while
    /// the conflicting borrows demote. `p`,`q` both borrow `a` (conflict); `s` borrows `b`
    /// (independent). The loop demotes the `a`-chain but never commits `s`, so the fixpoint
    /// keeps `s` Ref — making the conflict-free assertion load-bearing: `s` is a live Ref
    /// candidate, so an empty residual is a genuine reconciliation, not the degenerate
    /// no-Ref-candidates-left reading of the single-base `f` case.
    #[test]
    fn bb2ii_preserves_independent_borrow() {
        run_compiler(
            r#"
pub unsafe fn g() {
    let mut a = 0i32;
    let mut b = 0i32;
    let p = &mut a as *mut i32;
    let q = &mut a as *mut i32;
    let s = &mut b as *mut i32;
    *p = 1;
    *q = 2;
    *s = 3;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "g");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let s = local_slot(&slots, f, local_by_var_name(tcx, f, "s"), 0);

                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");

                // The independent borrow `s` (distinct base `b`) is never committed → Ref.
                assert_eq!(
                    model.get(&s),
                    Some(&SlotKind::Ref),
                    "independent borrow `s` must remain Ref at the fixpoint; got {:?}",
                    model.get(&s)
                );

                // Non-vacuous clean: `s` is a live Ref candidate, so an empty residual means
                // a genuine reconciliation, not the no-Ref-candidates-left degeneracy.
                let clean = revalidate_replaying(
                    &program,
                    &slots,
                    |x: SlotRef| model.get(&x) == Some(&SlotKind::Ref),
                    |x: SlotRef| model.get(&x) == Some(&SlotKind::Raw),
                    true,
                );
                assert!(
                    clean.get(&f).map_or(true, |e| e.is_empty()),
                    "fixpoint must be conflict-free under replay; got {clean:?}"
                );
            },
        );
    }

    /// BB2-ii regression: a DEAD copy of a borrowed pointer (`let _r = p;`) must NOT panic
    /// the loop. coherence's flow-insensitive `equate(_r, p)` drags `_r` to Raw when `p` is
    /// committed off Ref, but `_r` is dead at the conflict so it is never a borrow demotion
    /// witness. `borrow_conflicts_replaying`'s former hard "Raw ⟹ witness" assert tripped
    /// on it; the relaxed *inert-ness* invariant lets the loop converge (the stray Raw `_r`
    /// is provably in no residual edge). C2Rust output is full of such dead pointer copies.
    #[test]
    fn bb2ii_dead_copy_does_not_panic() {
        run_compiler(
            r#"
pub unsafe fn dcu() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let _r = p;
    let q = &mut a as *mut i32;
    *p = 1;
    *q = 2;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "dcu");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("dead copy must not panic; loop converges");

                let clean = revalidate_replaying(
                    &program,
                    &slots,
                    |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref),
                    |s: SlotRef| model.get(&s) == Some(&SlotKind::Raw),
                    true,
                );
                assert!(
                    clean.get(&f).map_or(true, |e| e.is_empty()),
                    "dead-copy fixpoint must be conflict-free under replay; got {clean:?}"
                );
            },
        );
    }

    /// BB3-a (`Ref ⇒ loan`, source-based): a malloc result owns heap — it is not a borrow,
    /// so it must never be classified `Ref` (a reference to owned memory is unsound). Here
    /// `leak` mallocs and returns `&raw mut p`; the source conflicts with return
    /// finalization so the relax loop leaks it (¬Owning), and with no enforcement the
    /// max-ref objective floats the malloc result to `Ref`. `verify_to_fixpoint` must
    /// demote the **malloc-destination** slot to `Raw` (¬Owning leaked ∧ ¬Ref source).
    #[test]
    fn bb3a_leaked_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { malloc(8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                // The malloc-destination slot (robust to whether MIR names it `p` or a temp).
                let src = local_slot(&slots, f, call_destination(tcx, &body, "malloc"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&src),
                    Some(&SlotKind::Raw),
                    "leaked malloc source must be Raw (¬Owning leaked ∧ ¬Ref source); got {:?}",
                    model.get(&src)
                );
            },
        );
    }

    /// BB3-a regression guard: a reference PARAMETER must STAY `Ref`. Its backing borrow is
    /// the caller's (no local loan), so the earlier "loanless" predicate wrongly demoted it
    /// to `Raw`. The source-based predicate must not — a param is never a malloc-call
    /// destination, so it is never a source slot.
    #[test]
    fn bb3a_param_ref_stays_ref() {
        run_compiler(
            r#"
pub unsafe fn foo(p: *mut i32) -> i32 {
    *p = 1;
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "foo");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let p = local_slot(&slots, f, Local::from_u32(1), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Ref),
                    "reference param `p` must stay Ref (not a malloc source); got {:?}",
                    model.get(&p)
                );
            },
        );
    }

    /// BB3-a regression guard (projected-store / `destination.as_local`): in `*out = malloc()`
    /// the store's base local `out` is a PARAM — `destination.local` would wrongly flag it as
    /// a source. The scan uses `destination.as_local()` (bare-local only), so `out` is never
    /// flagged and stays `Ref` (the malloc'd pointee is `Owning`, carried through `*out`).
    #[test]
    fn bb3a_store_malloc_through_outparam_keeps_param_ref() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn fill(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "fill");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                // `out` is param Local 1; its depth-0 slot is borrowed caller storage = Ref.
                let out = local_slot(&slots, f, Local::from_u32(1), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&out),
                    Some(&SlotKind::Ref),
                    "out-param `out` must stay Ref (its base is not a bare-local malloc dest); got {:?}",
                    model.get(&out)
                );
            },
        );
    }

    /// BB3-a (cast-following): the canonical C2Rust shape `let p = malloc(n) as *mut T`
    /// routes the allocation through a CAST (`_tmp = malloc()`, `_p = _tmp as *mut T`). The
    /// source scan must flag BOTH `_tmp` and the cast target, else a leaked alloc lets the
    /// cast target `p` float to `Ref` (a reference to owned heap). `p` must be `Raw`.
    #[test]
    fn bb3a_leaked_cast_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak_cast() -> *mut *mut i32 {
    let mut p = unsafe { malloc(8) } as *mut i32;
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak_cast");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                // `p` is the CAST TARGET (`malloc(...) as *mut i32`), not the call dest.
                let p = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Raw),
                    "leaked malloc CAST target `p` must be Raw (cast-following); got {:?}",
                    model.get(&p)
                );
            },
        );
    }

    /// BB3-a (allocator coverage): a leaked `calloc` source — not just `malloc` — must be
    /// demoted to `Raw`. Guards the `ALLOCATOR_NAMES` list against silently dropping an entry.
    #[test]
    fn bb3a_leaked_calloc_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn calloc(nmemb: usize, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak_calloc() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { calloc(1, 8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak_calloc");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let src = local_slot(&slots, f, call_destination(tcx, &body, "calloc"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&src),
                    Some(&SlotKind::Raw),
                    "leaked calloc source must be Raw; got {:?}",
                    model.get(&src)
                );
            },
        );
    }

    /// BB3-a (precision, `¬ref` not `raw`): an UNLEAKED malloc source (allocated then freed,
    /// no escape) must settle `Owning`, NOT be force-demoted to `Raw`. BB3-a's `== Ref` gate
    /// only fires on `Ref`-classified sources, so an `Owning` source is left alone.
    #[test]
    fn bb3a_unleaked_malloc_stays_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_free() {
    let p = unsafe { malloc(8) };
    unsafe { free(p) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "alloc_free");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let p = local_slot(&slots, f, call_destination(tcx, &body, "malloc"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Owning),
                    "unleaked malloc source must stay Owning (¬ref not raw); got {:?}",
                    model.get(&p)
                );
            },
        );
    }

    /// BB3-a (allocator coverage): `realloc` — which also sinks arg0 — must still be a
    /// source on its RESULT. Guards `ALLOCATOR_NAMES` against dropping `realloc`.
    #[test]
    fn bb3a_leaked_realloc_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak_realloc() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { realloc(core::ptr::null_mut(), 8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak_realloc");
                // R219: taking the pointer local's address is not a use of the
                // allocation. Keep both outcomes; null-old has no old claim.
                let sites = crate::analyses::borrow_ownership::realloc::collect_sites(&program);
                assert!(matches!(
                    sites[0].result,
                    crate::analyses::borrow_ownership::realloc::ReallocResult::Unobserved(_)
                ));
                let cases = crate::analyses::borrow_ownership::realloc::classify(&sites[0])
                    .expect("R219 source cases");
                assert_eq!(cases.len(), 2);
                assert!(cases.iter().all(|case| case.old
                    == crate::analyses::borrow_ownership::realloc::OldResponsibility::Absent));
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let src = local_slot(&slots, f, call_destination(tcx, &body, "realloc"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&src),
                    Some(&SlotKind::Raw),
                    "leaked realloc source must be Raw; got {:?}",
                    model.get(&src)
                );
            },
        );
    }

    /// BB3-a (allocator coverage): `strdup`. Guards `ALLOCATOR_NAMES` against dropping it.
    #[test]
    fn bb3a_leaked_strdup_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn strdup(s: *const i8) -> *mut i8;
}

pub unsafe fn leak_strdup(s: *const i8) -> *mut *mut i8 {
    let mut p = unsafe { strdup(s) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak_strdup");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let src = local_slot(&slots, f, call_destination(tcx, &body, "strdup"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&src),
                    Some(&SlotKind::Raw),
                    "leaked strdup source must be Raw; got {:?}",
                    model.get(&src)
                );
            },
        );
    }

    /// BB3-a (extern gate): a crate-LOCAL fn named `malloc` is NOT an ownership source (the
    /// boundary only sources extern `ForeignItem` callees), so its call destination must not
    /// be flagged a malloc source — else its result would be wrongly demoted off `Ref`.
    #[test]
    fn bb3a_local_fn_named_malloc_is_not_a_source() {
        run_compiler(
            r#"
unsafe fn malloc(p: *mut i32) -> *mut i32 {
    p
}

pub unsafe fn use_it(x: *mut i32) {
    let q = unsafe { malloc(x) };
    *q = 1;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let use_it = function_by_name(&program, "use_it");
                let body = tcx.mir_drops_elaborated_and_const_checked(use_it).borrow();
                let slots = CrateSlots::build(&program);

                let q = local_slot(&slots, use_it, call_destination(tcx, &body, "malloc"), 0);
                let sources = collect_malloc_source_slots(program.tcx, &program.functions, &slots);
                assert!(
                    !sources.contains(&q),
                    "a crate-local fn named `malloc` must not be flagged a source; got {sources:?}"
                );
            },
        );
    }

    /// §NB-F (flipped from NB0's `should_panic` tripwire pin, per that fixture's
    /// own flip-loudly note): the minimized uthash shape — `is_null` on
    /// `&mut local as *mut S` where S has pointer fields, c2rust's
    /// `assert(&els[i] != NULL)` — must EMIT CLEANLY and solve. `call_is_null`
    /// now peels the leading outer-reference slot of an `is_ref` arg (the
    /// established boundary/memset peel idiom) instead of asserting it
    /// impossible. History: minimized from uthash tests/test68.rs during NB-R's
    /// bisect; fix approved with option (a) at the NB-R gate.
    #[test]
    fn nbf_uthash_isnull_ref_arg_emits() {
        run_compiler(
            r#"
#[derive(Copy, Clone)]
#[repr(C)]
pub struct el {
    pub id: i32,
    pub next: *mut el,
}

pub unsafe fn f() {
    let mut e = el { id: 0, next: 0 as *mut el };
    if !(&mut e as *mut el).is_null() {}
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("the uthash is_ref shape must emit cleanly");
                assert!(
                    solver.model_kinds_relaxing(&selectors).is_some(),
                    "the shape must also solve (no hidden contradiction from the peel)"
                );
            },
        );
    }

    /// §NB0 (hoisted BB3-a): `¬ref(source)` is a candidacy-independent domain invariant
    /// emitted EAGERLY — no model, however early, may classify a malloc-source slot
    /// `Ref`. Uses the leaked-alloc shape whose source previously FLOATED to `Ref`
    /// under the max-ref objective on the raw relax-solve (the lazy loop only demoted
    /// it in a later round; post-hoist there is no such window).
    #[test]
    fn nb0_emission_source_never_ref() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { malloc(8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let leak = function_by_name(&program, "leak");
                let body = tcx.mir_drops_elaborated_and_const_checked(leak).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);
                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("NB0 emission");

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("relax loop resolves the leak");
                let p = local_slot(&slots, leak, call_destination(tcx, &body, "malloc"), 0);
                assert_ne!(
                    model.get(&p),
                    Some(&SlotKind::Ref),
                    "a malloc-source slot may never be Ref, even on the first relax-solve \
                     (eager ¬ref); got {:?}",
                    model.get(&p)
                );
            },
        );
    }

    /// BB3-b (Owning under-report — investigated → unreachable). An `Owning` slot is a
    /// **non-candidate** in the replay (`is_candidate = is_ref ∨ is_raw`), so it issues and
    /// requires NO loan — it can never be named in a conflict edge. The investigation's
    /// concern was whether a borrow hazard *caused by* an Owning pointer could thereby be
    /// MISSED (an under-report ⇒ an unsound accepted model). It cannot: every borrow conflict
    /// needs ≥1 loan, every loan is issued by a `Ref`/`Raw` candidate, and `invalidates` keys
    /// on the borrowed `Place`'s base — NOT on that base's candidacy (`invalidates.rs:65-88`:
    /// a loan is skipped only for *immutable provenance*, which an Owning base, having none,
    /// lacks) — so a hazard around an Owning base still fires, attributed to the borrowing
    /// `Ref`. The remaining no-loan cases (`Owning↔Owning` double-free, `Owning↔Raw`) are the
    /// ownership-linearity layer's concern / sound in real Rust, never a borrow loan.
    ///
    /// This pins the load-bearing half empirically with TWO candidacies over a malloc base
    /// aliased by two conflicting `&mut *p` borrows:
    ///   (A) base = `Owning` (its source slots non-candidate), aliases = `Ref`;
    ///   (B) base = `Ref` candidate too (every pointer slot `Ref`).
    /// In BOTH, the residual is non-empty (the hazard stays visible — the anti-under-report
    /// guard: were the Owning case blind, (A) would go empty) and NO conflict edge ever names
    /// the malloc base. The owners are the `&mut *p` loan-issuer temporaries, never the
    /// dereferenced base: a pointer that is *borrowed through* is a loan TARGET, not a loan
    /// OWNER (`issuer`/`requirer` come from the `&mut` LHS, `borrow/mod.rs:448-465`). So the
    /// base is absent from the edges *irrespective of its kind* — which is precisely why the
    /// under-report cannot occur: classifying a slot `Owning` removes nothing a `Ref` slot
    /// would have contributed as an owner, because the base was never an owner to begin with.
    #[test]
    fn bb3b_owning_base_hazard_surfaces_on_ref_not_owning_slot() {
        use crate::analyses::borrow_ownership::source_events::SourceRole;
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn ob() {
    let p = unsafe { malloc(4) } as *mut i32;
    let x = &mut *p as *mut i32;
    let y = &mut *p as *mut i32;
    *x = 1;
    *y = 2;
    unsafe { free(p as *mut core::ffi::c_void) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "ob");
                let slots = CrateSlots::build(&program);

                // The malloc base (call destination + its cast target) = the Owning source set.
                let sources = collect_malloc_source_slots(program.tcx, &program.functions, &slots);
                assert!(
                    !sources.is_empty(),
                    "the malloc base must be recognized as a source"
                );

                // Preserve the ordinary-loan owner rule. Retirement appends
                // separately witnessed unary target edges; subtract exactly
                // those occurrences, never all edges naming the same slot.
                let assert_hazard_excludes_base = |label: &str, base_is_ref: bool| {
                    let (residual, export) = with_bo_export(|| {
                        revalidate_replaying(
                            &program,
                            &slots,
                            // (A) base Owning ⇒ a source slot is NOT a Ref candidate; (B) base Ref.
                            |s: SlotRef| base_is_ref || !sources.contains(&s),
                            |_s: SlotRef| false,
                            true,
                        )
                    });
                    assert!(
                        residual.get(&f).is_some_and(|e| !e.is_empty()),
                        "[{label}] the alias hazard must remain visible under replay (an empty \
                         residual would BE the under-report); got {residual:?}"
                    );
                    let review = export
                        .source_retirement
                        .as_ref()
                        .expect("separate retirement channel");
                    assert!(review.unresolved.is_empty());
                    let mut ordinary = residual.clone();
                    for target in review.targets() {
                        let witness = review
                            .conflicts
                            .iter()
                            .find(|row| row.target == target)
                            .unwrap();
                        let edges = ordinary
                            .get_mut(&witness.function)
                            .expect("combined frame edges");
                        let appended = edges
                            .iter()
                            .rposition(|edge| {
                                edge.issuer == Some(target)
                                    && edge.requirers.is_empty()
                                    && !edge.esc_issuer_first
                            })
                            .expect("exact appended retirement target edge");
                        edges.remove(appended);
                        if sources.contains(&target) {
                            assert!(
                                base_is_ref,
                                "an Owning base is never a Ref retirement target"
                            );
                            assert!(
                                review.conflicts.iter().any(|row| row.target == target
                                    && row.source.function == "ob"
                                    && row.source.role == SourceRole::Free),
                                "a synthetic Ref base requires its actual source-free witness"
                            );
                        }
                    }
                    assert!(
                        ordinary.get(&f).is_some_and(|edges| !edges.is_empty()),
                        "ordinary aliasing hazard must remain visible after the exact retirement join"
                    );
                    for edge in ordinary.get(&f).into_iter().flatten() {
                        for owner in edge.issuer.iter().chain(edge.requirers.iter()) {
                            assert!(
                                !sources.contains(owner),
                                "[{label}] the malloc base must never be a conflict OWNER (it is \
                                 a loan target, not a loan owner); got {owner:?} in {edge:?}"
                            );
                        }
                    }
                };

                // (A) Base classified Owning: the hazard is still seen, attributed to the Refs.
                assert_hazard_excludes_base("base=Owning", false);
                // (B) An actual Ref base may additionally be a retirement
                // target; it still cannot become an ordinary loan owner.
                assert_hazard_excludes_base("base=Ref", true);
            },
        );
    }

    // §8 BB3-b — the mixed-role under-report and its complete-by-construction fix. The four
    // fixtures below are the four reachable shapes successive adversarial rounds produced; each
    // is a local conflated to one flow-insensitive `Owning` slot that ALSO carries a reference
    // role. With the old "exclude `Owning` from the replay" candidacy each hid a real `Ref`-vs-
    // `Ref` aliasing; under `is_raw = model != Ref` (never exclude a non-`Ref` slot) none can.
    // All assert the same contract via `assert_mixed_role_no_hidden_aliasing` — see its doc.

    /// round-1: a local reused as a borrow (`p = &mut a`, aliasing `q`) then an allocation
    /// (`p = malloc()`). The DIRECT mixed-role shape.
    #[test]
    fn bb3b_mixed_role_direct_no_hidden_aliasing() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn mixed() {
    let mut a = 0i32;
    let mut p = &mut a as *mut i32;
    let q = &mut a as *mut i32;
    *p = 1;
    *q = 2;
    p = unsafe { malloc(4) } as *mut i32;
    unsafe { free(p as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_mixed_role_no_hidden_aliasing(tcx, "mixed", "p"),
        );
    }

    /// round-2: a caller local made `Owning` by an allocator WRAPPER's owned return
    /// (`make() { malloc() }`) — `Owning` without being a direct malloc source.
    #[test]
    fn bb3b_mixed_role_owned_return_no_hidden_aliasing() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

unsafe fn make() -> *mut i32 {
    (unsafe { malloc(4) }) as *mut i32
}

pub unsafe fn mixed() {
    let mut a = 0i32;
    let mut p = &mut a as *mut i32;
    let q = &mut a as *mut i32;
    *p = 1;
    *q = 2;
    p = unsafe { make() };
    unsafe { free(p as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_mixed_role_no_hidden_aliasing(tcx, "mixed", "p"),
        );
    }

    /// round-3: a reborrow (`s = &mut *p`) whose aliasing of `a` is UNION-INDUCED — it only
    /// materializes after `p` is demoted and `p`~`a` unions, so `s` is not a round-0 conflict
    /// owner (round-0 all-`Ref` has no `tree_borrow_local` unions).
    #[test]
    fn bb3b_mixed_role_union_induced_no_hidden_aliasing() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn unioncase() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    a = 10;
    let mut s = &mut *p as *mut i32;
    let t = &mut a as *mut i32;
    *s = 1;
    *t = 2;
    s = (unsafe { malloc(4) }) as *mut i32;
    unsafe { free(s as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_mixed_role_no_hidden_aliasing(tcx, "unioncase", "s"),
        );
    }

    /// round-4: a derived pointer via `offset` (`s = p.offset(0)`) — a reference role the borrow
    /// replay propagates through a pointer-method call, which a syntactic Ref/RawPtr+cast/copy
    /// scan does not. The complete-by-construction candidacy needs no such scan.
    #[test]
    fn bb3b_mixed_role_offset_no_hidden_aliasing() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn offcase() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    a = 10;
    let mut s = unsafe { p.offset(0) };
    let t = &mut a as *mut i32;
    *s = 1;
    *t = 2;
    s = (unsafe { malloc(4) }) as *mut i32;
    unsafe { free(s as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_mixed_role_no_hidden_aliasing(tcx, "offcase", "s"),
        );
    }

    // ===================================================================================
    // §8 BB-parity-borrow — differential parity of BO's §8 borrow classification against
    // the production borrow analysis. Criterion (see task/plan docs):
    //   HA1 (hard, soundness): BO's accepted model is a replaying-borrow fixpoint
    //     (`revalidate_replaying` finds no residual) — catches BO UNDER-demotion. This is
    //     BO's own accept condition, so it is a stability/regression guard, NOT an
    //     independent oracle (the union replay is unavoidable for a partial candidacy).
    //     Blind to the RESIDUAL Owning-issuer no-loan case (an `Owning` slot issues no loan,
    //     so a conflict caused by its exclusivity is invisible to the replay AND to the
    //     production greedy driver) — inherited from BO, guardrail-tolerated. Distinct from
    //     the exclusion-based mixed-role under-report BB3-b closed by construction.
    //   Witness-specific non-vacuity (hard, production-only, INDEPENDENT): every local in
    //     `demoted` must be demoted by the production greedy driver
    //     (`demote_pointers_iterative_with_fields` from all-Ref, sharing only
    //     `borrow_inference`) — ties the gate to the fixture's INTENDED conflict witnesses
    //     (not a decoy demotion elsewhere) and proves HA1 is not vacuously clean.
    //   Control survivors (hard): every local in `kept_ref` must stay `Ref` in BO's model —
    //     enforces a control's stated claim (e.g. distinct-base borrows survive), so a
    //     wholesale all-`Raw` collapse cannot pass silently.
    //   Precision report (NON-failing): BO non-`Ref` vs production-demoted, attributed.
    //     Over-demotion (borrow-`Raw` ∉ production, e.g. coherence-drag / all-`Raw` collapse)
    //     is SAFE (precision, not soundness), so it is reported, never asserted.
    fn assert_borrow_parity(tcx: TyCtxt<'_>, fn_name: &str, demoted: &[&str], kept_ref: &[&str]) {
        let program = collect_program(tcx);
        let f = function_by_name(&program, fn_name);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_s, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("BB-parity: ownership emission");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
            .expect("BB-parity: BO CEGAR must converge (Some) on the corpus");

        // HA1 — soundness gate: no residual conflict under the COMPLETE replay (every
        // non-`Ref` slot a candidate, matching verify_to_fixpoint's own acceptance). A
        // residual would mean BO left a surviving `Ref` that still aliases (under-demotion).
        let residual = revalidate_replaying(
            &program,
            &slots,
            |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref),
            |s: SlotRef| model.get(&s) != Some(&SlotKind::Ref),
            true,
        );
        assert!(
            residual.values().all(|edges| edges.is_empty()),
            "BB-parity HA1: BO's accepted model has a residual borrow conflict (under-demotion); \
             got {residual:?}"
        );

        // Independent production greedy driver from all-Ref; map its demoted locals to depth-0
        // slots. Shares only `borrow_inference`, never `borrow_conflicts_replaying`.
        let mut ctxt = GBorrowInferCtxt::new(&program, |_| |_| true, |_| |_| true);
        let d_prod = demote_pointers_iterative_with_fields(&program, &mut ctxt);
        let mut prod_slots: rustc_hash::FxHashSet<SlotRef> = rustc_hash::FxHashSet::default();
        for (g, dem) in &d_prod.locals {
            let Some(universe) = slots.fn_local_slots.get(g) else {
                continue;
            };
            for local in dem.iter() {
                if let Some(sid) = universe.slot_for_local_depth(local, 0) {
                    prod_slots.insert(SlotRef::Local(*g, sid));
                }
            }
        }

        // Witness-specific NON-VACUITY (Codex HIGH): each named local the INDEPENDENT
        // production driver MUST demote — ties the gate to the fixture's INTENDED conflict
        // witnesses, not a decoy demotion elsewhere in the program.
        for nm in demoted {
            let sref = local_slot(&slots, f, local_by_var_name(tcx, f, nm), 0);
            assert!(
                prod_slots.contains(&sref),
                "BB-parity: fixture `{fn_name}` expected the independent production driver to \
                 demote `{nm}` (its intended conflict witness), but it did not"
            );
        }

        // CONTROL survivors (Codex MEDIUM): each named local MUST stay `Ref` in BO's model,
        // enforcing the control's stated claim so a wholesale all-`Raw` collapse cannot pass.
        for nm in kept_ref {
            let sref = local_slot(&slots, f, local_by_var_name(tcx, f, nm), 0);
            assert_eq!(
                model.get(&sref),
                Some(&SlotKind::Ref),
                "BB-parity: fixture `{fn_name}` requires `{nm}` to stay `Ref` in BO's model; \
                 got {:?}",
                model.get(&sref)
            );
        }

        // Precision report (NON-failing). Over-demotion (borrow-`Raw` ∉ production) is SAFE.
        let sources = collect_malloc_source_slots(program.tcx, &program.functions, &slots);
        let (mut borrow_raw, mut owning, mut leaked_raw, mut over_demote) = (0usize, 0, 0, 0);
        for (s, kind) in &model {
            if !matches!(s, SlotRef::Local(..)) {
                continue;
            }
            match kind {
                SlotKind::Owning => owning += 1,
                SlotKind::Raw if sources.contains(s) => leaked_raw += 1,
                SlotKind::Raw => {
                    borrow_raw += 1;
                    if !prod_slots.contains(s) {
                        over_demote += 1;
                    }
                }
                SlotKind::Ref => {}
            }
        }
        let bo_precision_wins = prod_slots
            .iter()
            .filter(|s| model.get(*s) == Some(&SlotKind::Ref))
            .count();
        eprintln!(
            "[BB-parity] borrow_raw={borrow_raw} owning={owning} leaked_raw={leaked_raw} \
             prod_demoted={} over_demote(safe)={over_demote} bo_precision_wins={bo_precision_wins}",
            prod_slots.len()
        );
    }

    /// Two `&mut` of the SAME local base alias — the canonical demote. BO collapses to
    /// all-`Raw`; production demotes both. HA1 holds; non-vacuous.
    #[test]
    fn bbparity_alias_two_mut_same_base() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let x = &mut a as *mut i32;
    let y = &mut a as *mut i32;
    *x = 1;
    *y = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["x", "y"], &[]),
        );
    }

    /// Copy-alias chain: `q = p` copies a borrow of `a` that also has a second `&mut a`.
    /// Exercises the round-0 (non-replay) conflict path. Non-vacuous.
    #[test]
    fn bbparity_alias_copy_chain() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let q = p;
    let r = &mut a as *mut i32;
    *q = 1;
    *r = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["q", "r"], &[]),
        );
    }

    /// Conflicting a-chain (p,q) alongside a DISTINCT-base borrow s that must stay live —
    /// proves the clean residual reconciles with a surviving candidate, not an all-`Raw`
    /// cascade. Non-vacuous.
    #[test]
    fn bbparity_independent_borrow_amid_conflict() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let mut b = 0i32;
    let p = &mut a as *mut i32;
    let q = &mut a as *mut i32;
    let s = &mut b as *mut i32;
    *p = 1;
    *q = 2;
    *s = 3;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["p", "q"], &["s"]),
        );
    }

    /// Reborrow-through-`*p` aliasing: `s`,`t` are both `&mut *p`, so they alias directly.
    /// Production demotes `s`,`t`; the base `p` stays `Ref` (a loan target, not an owner) —
    /// a distinct SHAPE from two `&mut` of a local, exercising reborrow provenance.
    /// NON-vacuous. NOTE round-0 already sees this conflict, so it does NOT isolate the
    /// union-replay path; a genuine union-only parity fixture (round-0-empty vs
    /// replay-non-empty) is deferred to the follow-up — `bb2i_*` covers union replay
    /// differentially today.
    #[test]
    fn bbparity_reborrow_deref_aliasing() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let s = &mut *p as *mut i32;
    let t = &mut *p as *mut i32;
    *s = 1;
    *t = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["s", "t"], &["p"]),
        );
    }

    /// Pointer-arithmetic via the WHITELISTED `offset` (is_borrowing_method): `q = p.offset(0)`
    /// aliases p, so a loan + union form and the conflict surfaces. Non-vacuous. (The `add`
    /// whitelist-miss contrast needs a no-base-loan shape; deferred to the follow-up.)
    #[test]
    fn bbparity_offset_derived_conflict() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let q = unsafe { p.offset(0) };
    *p = 1;
    *q = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["q"], &[]),
        );
    }

    /// Mixed ownership + borrow: the malloc base `p` is `Owning` (a source) while its two
    /// reborrows x,y are borrow-`Raw`. The core reconciliation — production demotes {x,y}
    /// (blind to p's ownership), BO carries `Owning` on p (filtered from the borrow axis).
    /// Non-vacuous. Byte-identical to `bb3b_owning_base_hazard`'s `ob`.
    #[test]
    fn bbparity_malloc_base_aliased() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn f() {
    let p = unsafe { malloc(4) } as *mut i32;
    let x = &mut *p as *mut i32;
    let y = &mut *p as *mut i32;
    *x = 1;
    *y = 2;
    unsafe { free(p as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["x", "y"], &[]),
        );
    }

    /// Dead copy `let _r = p`: coherence's flow-insensitive equate drags `_r` to `Raw` that
    /// production's witness-only collection leaves un-demoted (the confirmed HA2-⊆ breaker).
    /// HA1 still holds; the report's over-demote counter is non-zero (SAFE precision loss,
    /// not a soundness bug). Non-vacuous.
    #[test]
    fn bbparity_dead_copy() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let _r = p;
    let q = &mut a as *mut i32;
    *p = 1;
    *q = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["p", "q"], &[]),
        );
    }

    /// CONTROL: two `&mut` of DISTINCT local bases must both stay `Ref` — production demotes
    /// nothing. The false-positive guard (multiplicity of `&mut` alone must not demote).
    #[test]
    fn bbparity_independent_distinct_bases() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let mut b = 0i32;
    let x = &mut a as *mut i32;
    let y = &mut b as *mut i32;
    *x = 1;
    *y = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &[], &["x", "y"]),
        );
    }

    /// CONTROL: pure allocation, no borrow — production demotes {} while BO settles p
    /// `Owning`. Proves a naive set-equality gate is wrong and the ownership axis is
    /// separated from borrow. Vacuous on the borrow axis (report shows owning≥1).
    #[test]
    fn bbparity_unleaked_malloc() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn f() {
    let p = unsafe { malloc(4) };
    unsafe { free(p) };
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &[], &[]),
        );
    }

    /// CONTROL: a crate-local fn named `malloc` is NOT an allocator source (the extern gate),
    /// so `q` stays `Ref`; both drivers demote nothing. The source-detector correctness
    /// anchor. Vacuous.
    #[test]
    fn bbparity_local_fn_named_malloc() {
        run_compiler(
            r#"
unsafe fn malloc(p: *mut i32) -> *mut i32 {
    p
}

pub unsafe fn use_it(x: *mut i32) {
    let q = unsafe { malloc(x) };
    *q = 1;
}
"#,
            |tcx| assert_borrow_parity(tcx, "use_it", &[], &["q"]),
        );
    }

    /// A depth-zero local copy whose source is forced `Owning` has two sound readings:
    /// the current equal `Owning/Owning` arm, or the phase-1 shared-lend
    /// `Ref/Owning` arm. The max-Ref objective must choose the latter.
    #[test]
    fn copy_lend_owner_source_prefers_shared_destination() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let solver = KindSolver::new(&slots);

                let p = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "p"),
                    0,
                );
                let q = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "q"),
                    0,
                );
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                solver.assume(p, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
                assert_eq!(
                    model.get(&q),
                    Some(&SlotKind::Ref),
                    "an eligible owning-source local copy must select the shared lend arm"
                );
            },
        );
    }

    /// The new disjunction must not disturb the existing equal-kind reading when the source is
    /// pinned Raw: the owner-to-reference lend arm is unavailable without `rhs.own`. Pinning Raw
    /// makes this non-vacuous — without the equality arm, the max-Ref objective would choose q=Ref.
    #[test]
    fn copy_lend_nonowning_source_keeps_equal_raw() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let solver = KindSolver::new(&slots);

                let p = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "p"),
                    0,
                );
                let q = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "q"),
                    0,
                );
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                solver.assume(p, SlotKind::Raw);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&p), Some(&SlotKind::Raw));
                assert_eq!(model.get(&q), Some(&SlotKind::Raw));
            },
        );
    }

    /// Lend selection is a function of the one-hot kind model, not assertion order. Repeated
    /// solves and reversing the order in which function bodies add their copy constraints must
    /// therefore produce the same selected destination kinds.
    #[test]
    fn copy_lend_choice_is_stable_across_solves_and_function_registration_order() {
        run_compiler(
            r#"
pub unsafe fn copy_a(pa: *const i32) -> i32 {
    let qa = pa;
    let value = unsafe { *qa };
    value
}

pub unsafe fn copy_b(pb: *const i32) -> i32 {
    let qb = pb;
    let value = unsafe { *qb };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_a = function_by_name(&program, "copy_a");
                let copy_b = function_by_name(&program, "copy_b");
                let pairs = [
                    (
                        local_slot(&slots, copy_a, local_by_var_name(tcx, copy_a, "pa"), 0),
                        local_slot(&slots, copy_a, local_by_var_name(tcx, copy_a, "qa"), 0),
                    ),
                    (
                        local_slot(&slots, copy_b, local_by_var_name(tcx, copy_b, "pb"), 0),
                        local_slot(&slots, copy_b, local_by_var_name(tcx, copy_b, "qb"), 0),
                    ),
                ];

                let solve = |order: [LocalDefId; 2]| {
                    let solver = KindSolver::new(&slots);
                    let copy_lends = FxHashSet::from_iter(
                        pairs
                            .iter()
                            .map(|(source, destination)| CopyLendPair::new(*destination, *source)),
                    );
                    for did in order {
                        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                        add_coherence_with_copy_lends(&solver, &slots, did, &body, &copy_lends);
                    }
                    for (source, _) in pairs {
                        solver.assume(source, SlotKind::Owning);
                    }
                    assert_eq!(solver.check(), SatResult::Sat);
                    let first = solver.model_kinds().expect("first satisfiable model");
                    let second = solver.model_kinds().expect("repeated satisfiable model");
                    let read = |model: &FxHashMap<SlotRef, SlotKind>| {
                        pairs
                            .iter()
                            .map(|(source, destination)| {
                                (model.get(source).copied(), model.get(destination).copied())
                            })
                            .collect::<Vec<_>>()
                    };
                    assert_eq!(read(&first), read(&second), "repeated solve drifted");
                    read(&first)
                };

                let forward = solve([copy_a, copy_b]);
                let reverse = solve([copy_b, copy_a]);
                assert_eq!(
                    forward, reverse,
                    "function registration order changed the model"
                );
                assert_eq!(
                    forward,
                    vec![
                        (Some(SlotKind::Owning), Some(SlotKind::Ref)),
                        (Some(SlotKind::Owning), Some(SlotKind::Ref)),
                    ]
                );
            },
        );
    }

    /// R1 RED: once the derived lend guard is true, Copy and Move have the same ownership
    /// consequence. The destination is non-owning and the source owns both before and after the
    /// site; the current `push_linear`/move split must not remain active on this branch.
    #[test]
    fn copy_lend_guarded_ownership_keeps_source_and_forbids_destination_for_copy_and_move() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                for ensure_move in [false, true] {
                    let program = collect_program(tcx);
                    let slots = CrateSlots::build(&program);
                    let copy_local = function_by_name(&program, "copy_local");
                    let p = local_slot(
                        &slots,
                        copy_local,
                        local_by_var_name(tcx, copy_local, "p"),
                        0,
                    );
                    let q = local_slot(
                        &slots,
                        copy_local,
                        local_by_var_name(tcx, copy_local, "q"),
                        0,
                    );
                    let solver = KindSolver::new(&slots);
                    solver.lend_or_equate(q, p);
                    solver.assume(p, SlotKind::Owning);
                    let lend = solver.lend_guard(q, p);

                    let mut database = BoOwnDatabase::new(solver.optimize(), solver.tracker());
                    let mut var_gen = Gen::new();
                    let mut vars = database.new_vars(&mut var_gen, 3);
                    let destination_def = vars.next().expect("destination def");
                    let source_def = vars.next().expect("source def");
                    let source_use = vars.next().expect("source use");
                    database.push_guarded_copy(
                        &lend,
                        destination_def,
                        source_def,
                        source_use,
                        ensure_move,
                    );

                    let destination_ast = database.own_bool(destination_def).clone();
                    let source_def_ast = database.own_bool(source_def).clone();
                    let source_use_ast = database.own_bool(source_use).clone();
                    solver.link_own(q, &destination_ast);
                    solver.link_own(p, &z3::ast::Bool::or(&[&source_use_ast, &source_def_ast]));
                    drop(database);

                    assert_eq!(solver.check(), SatResult::Sat, "ensure_move={ensure_move}");
                    let model = solver.optimize().get_model().expect("ownership model");
                    let owned = |ast: &z3::ast::Bool| {
                        model
                            .eval(ast, true)
                            .and_then(|value| value.as_bool())
                            .unwrap_or(false)
                    };
                    assert!(!owned(&destination_ast), "ensure_move={ensure_move}");
                    assert!(owned(&source_use_ast), "ensure_move={ensure_move}");
                    assert!(owned(&source_def_ast), "ensure_move={ensure_move}");
                }
            },
        );
    }

    /// R1 MIR-plumbing RED: the ownership emitter and coherence must consume the same explicit
    /// pair plan. The accepted model's per-version readout at the copy site pins the lend branch,
    /// not merely the slot-global kind result.
    #[test]
    fn copy_lend_mir_transfer_exports_source_retention_and_nonowning_destination() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let p_local = local_by_var_name(tcx, copy_local, "p");
                let q_local = local_by_var_name(tcx, copy_local, "q");
                let p = local_slot(&slots, copy_local, p_local, 0);
                let q = local_slot(&slots, copy_local, q_local, 0);
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                let solver = KindSolver::new(&slots);

                let (model, export) = with_bo_export(|| {
                    let (_stats, selectors) = emit_crate_ownership_constraints_with_copy_lends(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                        &copy_lends,
                    )
                    .expect("ownership emission");
                    add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                    solver.assume(p, SlotKind::Owning);
                    solver.model_kinds_relaxing(&selectors)
                });
                let model = model.expect("lend model must be satisfiable");
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
                assert_eq!(model.get(&q), Some(&SlotKind::Ref));

                let copy_location = body
                    .basic_blocks
                    .iter_enumerated()
                    .find_map(|(block, data)| {
                        data.statements.iter().enumerate().find_map(
                            |(statement_index, statement)| {
                                let StatementKind::Assign(box (lhs, Rvalue::Use(operand))) =
                                    &statement.kind
                                else {
                                    return None;
                                };
                                let (Operand::Copy(rhs) | Operand::Move(rhs)) = operand else {
                                    return None;
                                };
                                (lhs.as_local() == Some(q_local) && rhs.as_local() == Some(p_local))
                                    .then_some(Location {
                                        block,
                                        statement_index,
                                    })
                            },
                        )
                    })
                    .expect("q = p MIR copy location");
                let copy_key = location_key(copy_location);
                let site = |local| {
                    export
                        .version_sites
                        .iter()
                        .find(|site| {
                            site.fn_did == copy_local
                                && site.local == local
                                && site.location == copy_key
                        })
                        .unwrap_or_else(|| panic!("missing version site for {local:?}"))
                };
                let q_site = site(q_local);
                let p_site = site(p_local);
                let owns = export.version_owns.as_ref().expect("per-version model");
                let owned = |var: Option<Var>| var.is_some_and(|var| owns[var]);
                assert!(!owned(q_site.def_var), "lend destination must not own");
                assert!(owned(p_site.use_var), "lend source must own before copy");
                assert!(owned(p_site.def_var), "lend source must retain ownership");
            },
        );
    }

    /// R3/R1 CopyForDeref RED at the source-only semantic seam. A rustc deref temp has no
    /// ownership signature, so this arm must preserve the source without inventing a destination
    /// ownership variable.
    #[test]
    fn copy_lend_guarded_copy_for_deref_keeps_source_ownership() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let p = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "p"),
                    0,
                );
                let q = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "q"),
                    0,
                );
                let solver = KindSolver::new(&slots);
                solver.lend_or_equate(q, p);
                solver.assume(p, SlotKind::Owning);
                let lend = solver.lend_guard(q, p);

                let mut database = BoOwnDatabase::new(solver.optimize(), solver.tracker());
                let mut var_gen = Gen::new();
                let mut vars = database.new_vars(&mut var_gen, 2);
                let source_def = vars.next().expect("source def");
                let source_use = vars.next().expect("source use");
                database.push_guarded_lend_source(&lend, source_def, source_use);

                let source_def_ast = database.own_bool(source_def).clone();
                let source_use_ast = database.own_bool(source_use).clone();
                solver.link_own(p, &z3::ast::Bool::or(&[&source_use_ast, &source_def_ast]));
                drop(database);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.optimize().get_model().expect("ownership model");
                let owned = |ast: &z3::ast::Bool| {
                    model
                        .eval(ast, true)
                        .and_then(|value| value.as_bool())
                        .unwrap_or(false)
                };
                assert!(owned(&source_use_ast));
                assert!(owned(&source_def_ast));
            },
        );
    }

    /// Required witness 1 RED: the selected lend must survive into the final replay as a typed
    /// loan at the exact copy location. A syntactic copy loan without the `CopyLend` class does not
    /// discharge R3 because later invalidation cannot apply the new semantics selectively.
    #[test]
    fn copy_lend_emits_replay_loan() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let p_local = local_by_var_name(tcx, copy_local, "p");
                let q_local = local_by_var_name(tcx, copy_local, "q");
                let p = local_slot(&slots, copy_local, p_local, 0);
                let q = local_slot(&slots, copy_local, q_local, 0);
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                let solver = KindSolver::new(&slots);

                let (model, export) = with_bo_export(|| {
                    let (_stats, selectors) = emit_crate_ownership_constraints_with_copy_lends(
                        &crate_ctxt,
                        &slots,
                        &origins,
                        &solver,
                        &copy_lends,
                    )
                    .expect("ownership emission");
                    add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                    solver.assume(p, SlotKind::Owning);
                    let model = solver
                        .model_kinds_relaxing(&selectors)
                        .expect("lend model must be satisfiable");
                    let selected = selected_copy_lend_sites(&program, &slots, &copy_lends, &model);
                    let conflicts = borrow_conflicts_replaying_with_flows_and_copy_lends(
                        &program,
                        origins.native_flows(),
                        |did| {
                            let model = &model;
                            let slots = &slots;
                            move |local| {
                                slots
                                    .fn_local_slots
                                    .get(&did)
                                    .and_then(|universe| universe.slot_for_local_depth(local, 0))
                                    .map(|slot| SlotRef::Local(did, slot))
                                    .is_some_and(|slot| model.get(&slot) == Some(&SlotKind::Ref))
                            }
                        },
                        |did| {
                            let model = &model;
                            let slots = &slots;
                            move |local| {
                                slots
                                    .fn_local_slots
                                    .get(&did)
                                    .and_then(|universe| universe.slot_for_local_depth(local, 0))
                                    .map(|slot| SlotRef::Local(did, slot))
                                    .is_some_and(|slot| model.get(&slot) != Some(&SlotKind::Ref))
                            }
                        },
                        |_| |_| false,
                        &[],
                        &selected,
                    );
                    assert!(
                        conflicts.values().all(Vec::is_empty),
                        "conflict-free copy fixture must remain clean: {conflicts:?}"
                    );
                    model
                });
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
                assert_eq!(model.get(&q), Some(&SlotKind::Ref));
                let typed = export
                    .loans
                    .iter()
                    .filter(|loan| loan.class == LoanClass::CopyLend)
                    .collect::<Vec<_>>();
                assert_eq!(
                    typed.len(),
                    1,
                    "CopyLend registration must identify one exact loan, not every companion at its location: {:?}",
                    export.loans
                );
                let typed = typed[0];
                assert_eq!(typed.key.fn_did, copy_local);
                assert_eq!(typed.key.place.local, p_local);
                assert_eq!(
                    typed.key.borrower,
                    crate::analyses::borrow_ownership::export::BorrowerKind::Assign {
                        owner: crate::analyses::borrow_ownership::export::OwnerKey::Local(
                            q_local.as_u32(),
                        ),
                    }
                );
            },
        );
    }

    /// Required witness 2 RED: CopyLend is shared, so a write through the retained owner while
    /// the destination loan is live must invalidate it even though Foster marks the destination
    /// read-only. The witnessed edge must name the source local as the invalidator.
    #[test]
    fn copy_lend_source_write_conflicts() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *mut i32) -> i32 {
    let q = p;
    unsafe { *p = 7 };
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let p_local = local_by_var_name(tcx, copy_local, "p");
                let q_local = local_by_var_name(tcx, copy_local, "q");
                let p = local_slot(&slots, copy_local, p_local, 0);
                let q = local_slot(&slots, copy_local, q_local, 0);
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                let solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints_with_copy_lends(
                    &crate_ctxt,
                    &slots,
                    &origins,
                    &solver,
                    &copy_lends,
                )
                .expect("ownership emission");
                add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                solver.assume(p, SlotKind::Owning);
                let model = solver
                    .model_kinds_relaxing(&selectors)
                    .expect("lend model must be satisfiable");
                let selected = selected_copy_lend_sites(&program, &slots, &copy_lends, &model);
                let is_ref = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) == Some(&SlotKind::Ref))
                    }
                };
                let is_raw = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) != Some(&SlotKind::Ref))
                    }
                };
                let witnessed = borrow_conflicts_replaying_witnessed_with_copy_lends(
                    &program,
                    origins.native_flows(),
                    is_ref,
                    is_raw,
                    |_| |_| false,
                    &[],
                    &selected,
                );
                let edges = witnessed
                    .get(&copy_local)
                    .expect("source write must produce a witnessed conflict");
                assert!(
                    edges
                        .iter()
                        .any(|edge| edge.invalidators.contains(&p_local)),
                    "source local was not recorded as invalidator: {edges:?}"
                );
            },
        );
    }

    /// Required witness 3 RED: the triptych's raw seam. A direct foreign-C `free(owner)` while
    /// the shared CopyLend remains live until a later alias use must be reported by the oracle.
    #[test]
    fn copy_lend_triptych_free_then_use_conflicts() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn free(p: *mut i32);
}

pub unsafe fn copy_local(p: *mut i32) -> i32 {
    let q = p;
    unsafe { free(p) };
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let p_local = local_by_var_name(tcx, copy_local, "p");
                let q_local = local_by_var_name(tcx, copy_local, "q");
                let p = local_slot(&slots, copy_local, p_local, 0);
                let q = local_slot(&slots, copy_local, q_local, 0);
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                let solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints_with_copy_lends(
                    &crate_ctxt,
                    &slots,
                    &origins,
                    &solver,
                    &copy_lends,
                )
                .expect("ownership emission");
                add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                solver.assume(p, SlotKind::Owning);
                let model = solver
                    .model_kinds_relaxing(&selectors)
                    .expect("lend model must be satisfiable");
                let selected = selected_copy_lend_sites(&program, &slots, &copy_lends, &model);
                let is_ref = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) == Some(&SlotKind::Ref))
                    }
                };
                let is_raw = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) != Some(&SlotKind::Ref))
                    }
                };
                let witnessed = borrow_conflicts_replaying_witnessed_with_copy_lends(
                    &program,
                    origins.native_flows(),
                    is_ref,
                    is_raw,
                    |_| |_| false,
                    &[],
                    &selected,
                );
                let edges = witnessed
                    .get(&copy_local)
                    .expect("free-before-use must produce a witnessed conflict");
                assert!(
                    edges
                        .iter()
                        .any(|edge| edge.invalidators.contains(&p_local)),
                    "free argument was not recorded as invalidator: {edges:?}"
                );
            },
        );
    }

    /// Targeted temporal-rule control: `free` must not acquire queue A1's global behaviour.
    /// With no selected CopyLend sites, the syntactic shared copy loan remains an existing loan
    /// class and the same foreign-C free call does not invalidate it.
    #[test]
    fn copy_lend_free_does_not_invalidate_unrelated_existing_loans() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn free(p: *mut i32);
}

pub unsafe fn copy_local(p: *mut i32) -> i32 {
    let q = p;
    unsafe { free(p) };
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let origins = compute_origins(&program);
                let selected = Default::default();
                let witnessed = borrow_conflicts_replaying_witnessed_with_copy_lends(
                    &program,
                    origins.native_flows(),
                    |_| |_| true,
                    |_| |_| false,
                    |_| |_| false,
                    &[],
                    &selected,
                );
                assert!(
                    witnessed.values().all(Vec::is_empty),
                    "an untyped existing loan changed at free: {witnessed:?}"
                );
            },
        );
    }

    /// Required witness 4: a non-conflicting copy recovers the allocation owner. The alias's last
    /// use precedes `free(p)`, so the typed loan is dead at deallocation and the oracle accepts
    /// `p=Owning, q=Ref`.
    #[test]
    fn copy_lend_recovers_owner_and_accepts() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn copy_local() -> i32 {
    let p = unsafe { malloc(core::mem::size_of::<i32>()) } as *mut i32;
    let q = p;
    let value = unsafe { *q };
    unsafe { free(p as *mut core::ffi::c_void) };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let p_local = local_by_var_name(tcx, copy_local, "p");
                let q_local = local_by_var_name(tcx, copy_local, "q");
                let p = local_slot(&slots, copy_local, p_local, 0);
                let q = local_slot(&slots, copy_local, q_local, 0);
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                let solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints_with_copy_lends(
                    &crate_ctxt,
                    &slots,
                    &origins,
                    &solver,
                    &copy_lends,
                )
                .expect("ownership emission");
                add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                let model = solver
                    .model_kinds_relaxing(&selectors)
                    .expect("owner-recovery model must be satisfiable");
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
                assert_eq!(model.get(&q), Some(&SlotKind::Ref));

                let selected = selected_copy_lend_sites(&program, &slots, &copy_lends, &model);
                let is_ref = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) == Some(&SlotKind::Ref))
                    }
                };
                let is_raw = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) != Some(&SlotKind::Ref))
                    }
                };
                let conflicts = borrow_conflicts_replaying_with_flows_and_copy_lends(
                    &program,
                    origins.native_flows(),
                    is_ref,
                    is_raw,
                    |_| |_| false,
                    &[],
                    &selected,
                );
                assert!(
                    conflicts.values().all(Vec::is_empty),
                    "dead-before-free CopyLend must be accepted: {conflicts:?}"
                );
            },
        );
    }

    /// Phase-1b gate fact retained after ruling §7a: Foster's written-through semantics leave a
    /// freed destination read-only. Eligibility must reject this shape through the unconditional
    /// S2-2-mirror rule rather than changing Foster.
    #[test]
    fn copy_lend_phase1b_fact_free_destination_remains_foster_readonly() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn free(p: *mut i32);
}

pub unsafe fn free_destination(p: *mut i32) {
    let q = p;
    unsafe { free(q) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let function = function_by_name(&program, "free_destination");
                let q = local_by_var_name(tcx, function, "q");
                let facts = MutFacts::from_program(&program);
                assert!(
                    !facts.is_mutable(function, q),
                    "ruling §7a fact drift: Foster unexpectedly classified free(q) mutable"
                );
            },
        );
    }

    /// Phase-1b gate fact retained after ruling §7b. Fresh allocation has no modeled borrow origin,
    /// so incoming `unknown_targets` contains the allocator-backed pair's genealogy. Eligibility
    /// consumes outward-live boundary events instead of this incoming membership.
    #[test]
    fn copy_lend_phase1b_fact_allocator_pair_has_incoming_unknown_genealogy() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}

pub unsafe fn copy_local() -> i32 {
    let p = unsafe { malloc(core::mem::size_of::<i32>()) } as *mut i32;
    let q = p;
    let value = unsafe { *q };
    unsafe { free(p as *mut core::ffi::c_void) };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let function = function_by_name(&program, "copy_local");
                let p = local_by_var_name(tcx, function, "p");
                let q = local_by_var_name(tcx, function, "q");
                let origins = compute_origins(&program);
                let unknown = origins.native_flows()[&function]
                    .body
                    .unknown_owner_depths();
                for local in [p, q] {
                    assert!(
                        unknown.contains(&(SlotOwner::Local(local), 0)),
                        "ruling §7b genealogy fact drift: {local:?}@d0 absent; facts={unknown:?}"
                    );
                }
            },
        );
    }

    #[test]
    fn copy_lend_phase1b_eligibility_malloc_without_outward_event_is_eligible() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn f() -> i32 {
    let p = unsafe { malloc(4) } as *mut i32;
    let q = p;
    let value = unsafe { *q };
    unsafe { free(p as *mut core::ffi::c_void) };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let function = function_by_name(&program, "f");
                let p = local_slot(&slots, function, local_by_var_name(tcx, function, "p"), 0);
                let q = local_slot(&slots, function, local_by_var_name(tcx, function, "q"), 0);
                let eligibility =
                    analyze_copy_lend_eligibility(&program, &slots, &facts, origins.native_flows());
                assert!(eligibility.pairs.contains(&CopyLendPair::new(q, p)));
            },
        );
    }

    #[test]
    fn copy_lend_phase1b_eligibility_live_outward_foreign_call_is_ineligible() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
    fn opaque(p: *mut i32);
}
pub unsafe fn f() -> i32 {
    let p = unsafe { malloc(4) } as *mut i32;
    let q = p;
    unsafe { opaque(q) };
    let value = unsafe { *q };
    unsafe { free(p as *mut core::ffi::c_void) };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let function = function_by_name(&program, "f");
                let p = local_slot(&slots, function, local_by_var_name(tcx, function, "p"), 0);
                let q = local_slot(&slots, function, local_by_var_name(tcx, function, "q"), 0);
                let eligibility =
                    analyze_copy_lend_eligibility(&program, &slots, &facts, origins.native_flows());
                assert!(!eligibility.pairs.contains(&CopyLendPair::new(q, p)));
            },
        );
    }

    #[test]
    fn copy_lend_phase1b_eligibility_free_destination_is_unconditionally_ineligible() {
        run_compiler(
            r#"
unsafe extern "C" { fn free(p: *mut i32); }
pub unsafe fn f(p: *mut i32) {
    let q = p;
    unsafe { free(q) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let function = function_by_name(&program, "f");
                let p = local_slot(&slots, function, local_by_var_name(tcx, function, "p"), 0);
                let q = local_slot(&slots, function, local_by_var_name(tcx, function, "q"), 0);
                let eligibility =
                    analyze_copy_lend_eligibility(&program, &slots, &facts, origins.native_flows());
                assert!(!eligibility.pairs.contains(&CopyLendPair::new(q, p)));
            },
        );
    }

    /// The production helper must consume exactly the same C2/C3 verdicts as the fixture-scale
    /// producer. This is a differential, not a duplicated predicate: the expected matrix pins the
    /// plain/free(source), outward-call, free(destination), and mutable-destination controls.
    #[test]
    fn copy_lend_phase1b_production_eligibility_matches_fixture_matrix() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
    fn realloc(p: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
    fn opaque(p: *const i32);
}
unsafe fn local_sink(p: *const i32) { let _ = unsafe { *p }; }
struct Holder { ptr: *const i32 }
pub unsafe fn plain() -> i32 {
    let p = unsafe { malloc(4) } as *const i32;
    let q = p;
    unsafe { *q }
}
pub unsafe fn outward() -> i32 {
    let p = unsafe { malloc(4) } as *const i32;
    let q = p;
    unsafe { opaque(q) };
    unsafe { *q }
}
pub unsafe fn ordinary_call() -> i32 {
    let p = unsafe { malloc(4) } as *const i32;
    let q = p;
    unsafe { local_sink(q) };
    unsafe { *q }
}
pub unsafe fn field_escape() -> i32 {
    let p = unsafe { malloc(4) } as *const i32;
    let q = p;
    let mut holder = Holder { ptr: core::ptr::null() };
    holder.ptr = q;
    unsafe { *holder.ptr }
}
pub unsafe fn return_escape() -> *const i32 {
    let p = unsafe { malloc(4) } as *const i32;
    let q = p;
    q
}
pub unsafe fn realloc_source() -> i32 {
    let p = unsafe { malloc(4) } as *const i32;
    let q = p;
    let _new = unsafe { realloc(p as *mut core::ffi::c_void, 8) };
    unsafe { *q }
}
pub unsafe fn free_destination() {
    let p = unsafe { malloc(4) } as *mut i32;
    let q = p;
    unsafe { free(q as *mut core::ffi::c_void) };
}
pub unsafe fn mutable_destination() -> i32 {
    let p = unsafe { malloc(4) } as *mut i32;
    let q = p;
    unsafe { *q = 1 };
    unsafe { *q }
}
pub unsafe fn free_source() -> i32 {
    let p = unsafe { malloc(4) } as *const i32;
    let q = p;
    let value = unsafe { *q };
    unsafe { free(p as *mut core::ffi::c_void) };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let fixture =
                    analyze_copy_lend_eligibility(&program, &slots, &facts, origins.native_flows());
                let solver = KindSolver::new(&slots);
                let production = construct_bo_into(
                    &program,
                    &slots,
                    &origins,
                    &facts,
                    &solver,
                    CopyLendMode::LendArm,
                )
                .expect("production construction");
                assert_eq!(production.eligibility, fixture);

                // R219 preserves this negative eligibility row: reading an
                // old alias does not imply that the realloc result succeeded.
                let realloc = production
                    .source_events
                    .reallocations
                    .iter()
                    .find(|site| site.key.function == "realloc_source")
                    .expect("realloc matrix row");
                assert!(matches!(
                    realloc.result,
                    crate::analyses::borrow_ownership::realloc::ReallocResult::Unobserved(_)
                ));
                let cases = crate::analyses::borrow_ownership::realloc::classify(realloc)
                    .expect("R219 matrix cases");
                assert!(cases.iter().any(|case| case.outcome == crate::analyses::borrow_ownership::realloc::ReallocOutcome::Failure && case.old == crate::analyses::borrow_ownership::realloc::OldResponsibility::LoseClaimIfPresent));

                for (name, expected) in [
                    ("plain", true),
                    ("outward", false),
                    ("ordinary_call", false),
                    ("field_escape", false),
                    ("return_escape", false),
                    ("realloc_source", false),
                    ("free_destination", false),
                    ("free_source", true),
                ] {
                    let function = function_by_name(&program, name);
                    let p = local_slot(&slots, function, local_by_var_name(tcx, function, "p"), 0);
                    let q_local = local_by_var_name(tcx, function, "q");
                    let q = local_slot(&slots, function, q_local, 0);
                    if name == "ordinary_call" {
                        assert!(
                            !facts.is_mutable(function, q_local),
                            "ordinary-call control must isolate C3 from the C2 gate"
                        );
                    }
                    assert_eq!(
                        fixture.pairs.contains(&CopyLendPair::new(q, p)),
                        expected,
                        "eligibility matrix drift for {name}"
                    );
                }
            },
        );
    }

    #[test]
    fn copy_lend_phase1b_l2_replay_receives_selected_loans() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn f() -> i32 {
    let p = unsafe { malloc(4) } as *mut i32;
    let q = p;
    let value = unsafe { *q };
    unsafe { free(p as *mut core::ffi::c_void) };
    value
}
"#,
            |tcx| {
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
                    CopyLendMode::LendArm,
                )
                .expect("lend construction");
                let (model, stats) = verify_guarded_to_fixpoint_counting(
                    &program,
                    &slots,
                    origins.native_flows(),
                    &solver,
                    &construction.selectors,
                    &facts,
                    Some(&construction.eligibility.pairs),
                    None,
                );
                assert_eq!(stats.copy_lend_replay_selections, 1);
                let model = model.expect("L2 must accept the dead-before-free CopyLend");
                let function = function_by_name(&program, "f");
                let p = local_slot(&slots, function, local_by_var_name(tcx, function, "p"), 0);
                let q = local_slot(&slots, function, local_by_var_name(tcx, function, "q"), 0);
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
                assert_eq!(model.get(&q), Some(&SlotKind::Ref));
            },
        );
    }

    #[test]
    fn copy_propagates_kind() {
        run_compiler(
            r#"
pub unsafe fn copy_fn(p: *mut i32) -> *mut i32 {
    p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_fn = function_by_name(&program, "copy_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(copy_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, copy_fn, &body);

                let ret = local_slot(&slots, copy_fn, Local::from_u32(0), 0);
                let p = local_slot(&slots, copy_fn, Local::from_u32(1), 0);
                solver.assume(p, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&ret), Some(&SlotKind::Owning));
            },
        );
    }

    #[test]
    fn address_of_depth_shift() {
        run_compiler(
            r#"
pub unsafe fn addr_fn(mut p: *mut i32) -> *mut *mut i32 {
    let q: *mut *mut i32 = &raw mut p;
    q
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let addr_fn = function_by_name(&program, "addr_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(addr_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, addr_fn, &body);

                let ret_depth_1 = local_slot(&slots, addr_fn, Local::from_u32(0), 1);
                let p = local_slot(&slots, addr_fn, Local::from_u32(1), 0);
                solver.assume(p, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&ret_depth_1), Some(&SlotKind::Owning));
            },
        );
    }

    #[test]
    fn all_raw_sat_with_coherence() {
        run_compiler(
            r#"
pub unsafe fn copy_fn(p: *mut i32) -> *mut i32 {
    p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_fn = function_by_name(&program, "copy_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(copy_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, copy_fn, &body);

                solver.assume(
                    local_slot(&slots, copy_fn, Local::from_u32(0), 0),
                    SlotKind::Raw,
                );
                solver.assume(
                    local_slot(&slots, copy_fn, Local::from_u32(1), 0),
                    SlotKind::Raw,
                );

                assert_eq!(solver.check(), SatResult::Sat);
            },
        );
    }

    #[test]
    fn cast_does_not_propagate_kind() {
        run_compiler(
            r#"
pub unsafe fn cast_fn(p: *mut i32) -> *mut u8 {
    p as *mut u8
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let cast_fn = function_by_name(&program, "cast_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(cast_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, cast_fn, &body);

                let ret = local_slot(&slots, cast_fn, Local::from_u32(0), 0);
                let p = local_slot(&slots, cast_fn, Local::from_u32(1), 0);
                solver.assume(p, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&ret), Some(&SlotKind::Ref));
            },
        );
    }

    #[test]
    fn aggregate_initializes_field_slot() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub p: *mut i32,
}

pub unsafe fn agg_fn(ptr: *mut i32) -> S {
    S { p: ptr }
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let agg_fn = function_by_name(&program, "agg_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(agg_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, agg_fn, &body);
                // §9.10.2: aggregate field ownership is now linked by the crate-wide
                // `constrain_field_ownership` (`S::p.own <=> ptr.own`), not the per-store
                // equate; add it so assuming `ptr` Owning makes `S::p` Owning.
                constrain_field_ownership(&solver, &slots, &program);

                let ptr = local_slot(&slots, agg_fn, Local::from_u32(1), 0);
                solver.assume(ptr, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let field_slot = slots
                    .field_slots
                    .slot_for_field_depth(
                        StructFieldSlot {
                            struct_did: s,
                            field_index: 0,
                        },
                        0,
                    )
                    .expect("slot for S::p");
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(
                    model.get(&SlotRef::Field(field_slot)),
                    Some(&SlotKind::Owning)
                );
            },
        );
    }

    // ===== BB-parity-own: ownership-slice semantic-verdict harness =====
    //
    // DEFERRED — relaxed-monotonicity IMPROVEMENT fixture (BO correctly `Owning` where
    // production is not): an empirical search over direct `free(p); return malloc` and the
    // interprocedural non-monotonic caller (`y = non_mono(x)`, non_mono frees its input and
    // returns a fresh malloc) found BO and production AGREE on every named local — BO does
    // not visibly exceed production on these simple shapes (production's monotonicity gating
    // is correctly scoped for them; some mixed alloc+out-param shapes go UNSAT and decline).
    // Per the project owner: do NOT fabricate an improvement case. A real divergence likely
    // needs a cyclic/recursive or deeper interprocedural shape and is deferred to a targeted
    // follow-up. When one is found, encode it as a gate-1 `owning` witness and confirm the
    // report shows PROD_MISSES for that witness.

    /// BB-parity-OWN: a SEMANTIC ownership-verdict harness for BO (borrow_ownership). The
    /// hard gates are pure SEMANTIC verdicts against the INTENDED ownership model (the §9.9
    /// output-param contract — a caller-visible ownership slot the callee REWRITES), NOT
    /// agreement with any implementation:
    ///   (1) each `owning` pointer BO MUST classify `Owning`;
    ///   (2) each `kept_non_owning` pointer BO must NOT over-claim `Owning` (over-claim =
    ///       `Box`/`free` on borrowed memory = double-free/UAF — the real soundness teeth).
    /// Production ownership (and, later, `output_params`) are REPORTED as DIAGNOSTICS ONLY,
    /// never gates: BO may legitimately claim MORE `Owning` than production (relaxed
    /// monotonicity is an intended improvement), so a witness production misses is REPORTED
    /// (PROD_MISSES / BO_EXTRA), not failed. Non-vacuity is intrinsic — gate 1 fails if BO
    /// does not genuinely compute `Owning`, and control slots are present in the model (so
    /// gate 2's `!= Owning` is a real verdict, not an absent-slot pass). Depth-0
    /// single-indirection only in this slice (BO syntactic depth vs production semantic depth
    /// can misalign at depth >= 1; deferred).
    /// A semantic ownership verdict target: a function `Local(name, depth)` or a struct
    /// `Field(struct_name, field_index, depth)`, at deref `depth` (0 = the slot's own
    /// value). Built via `loc` / `loc_at` / `fld`.
    #[derive(Clone, Copy, Debug)]
    enum Own<'a> {
        Local(&'a str, u8),
        Field(&'a str, usize, u8),
    }
    fn loc(name: &str) -> Own<'_> {
        Own::Local(name, 0)
    }
    fn loc_at(name: &str, depth: u8) -> Own<'_> {
        Own::Local(name, depth)
    }
    fn fld(struct_name: &str, field_index: usize) -> Own<'_> {
        Own::Field(struct_name, field_index, 0)
    }

    fn resolve_own(
        tcx: TyCtxt<'_>,
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        fn_did: LocalDefId,
        o: Own,
    ) -> SlotRef {
        match o {
            Own::Local(name, depth) => {
                local_slot(slots, fn_did, local_by_var_name(tcx, fn_did, name), depth)
            }
            Own::Field(struct_name, field_index, depth) => {
                let struct_did = struct_by_name(program, struct_name);
                let fsid = slots
                    .field_slots
                    .slot_for_field_depth(
                        StructFieldSlot {
                            struct_did,
                            field_index,
                        },
                        depth,
                    )
                    .unwrap_or_else(|| {
                        panic!("no field slot for `{struct_name}`.{field_index} depth {depth}")
                    });
                SlotRef::Field(fsid)
            }
        }
    }

    fn assert_ownership_parity(tcx: TyCtxt<'_>, fn_name: &str, owning: &[Own], non_owning: &[Own]) {
        // BO model (SUT) — identical construction to `assert_borrow_parity`.
        let program = collect_program(tcx);
        let f = function_by_name(&program, fn_name);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_s, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("BB-parity-own: ownership emission");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
            .expect("BB-parity-own: BO CEGAR must converge (Some) on the corpus");

        // Production ownership oracle — DIAGNOSTIC baseline only (NOT a gate/ceiling).
        let prod_owning = build_prod_owning(tcx, &program, &slots);

        // HARD gate 1 — positive Owning verdicts (Local OR Field, any depth): BO MUST classify
        // each `Owning`. Pure SEMANTIC verdict; production is NOT a gate. A verdict BO owns
        // that production MISSES is a relaxed-monotonicity IMPROVEMENT (reported), not a fail.
        let mut prod_agrees: Vec<Own> = Vec::new();
        let mut prod_misses: Vec<Own> = Vec::new();
        for &o in owning {
            let sref = resolve_own(tcx, &program, &slots, f, o);
            assert_eq!(
                model.get(&sref),
                Some(&SlotKind::Owning),
                "BB-parity-own: fixture `{fn_name}` requires BO to classify {o:?} Owning \
                 (semantic verdict); got {:?}",
                model.get(&sref)
            );
            // Production comparison applies to LOCAL verdicts only: `build_prod_owning` maps
            // production LOCAL ownership, not field ownership (deferred), so a `Field` verdict
            // is not a meaningful PROD_AGREES/MISSES signal.
            if matches!(o, Own::Local(..)) {
                if prod_owning.contains(&sref) {
                    prod_agrees.push(o);
                } else {
                    prod_misses.push(o);
                }
            }
        }

        // HARD gate 2 — semantic non-Owning verdicts: BO must NOT over-claim. Production is
        // not ground truth, so soundness lives HERE: over-claiming a read-only param, a
        // field-transfer parent, or a BORROWED field is a double-free/UAF.
        for &o in non_owning {
            let sref = resolve_own(tcx, &program, &slots, f, o);
            assert_ne!(
                model.get(&sref),
                Some(&SlotKind::Owning),
                "BB-parity-own: control {o:?} must NOT be Owning in BO's model \
                 (over-claim = double-free/UAF); got {:?}",
                model.get(&sref)
            );
        }

        // SOFT report (NEVER fails), over LOCAL slots (production field-granularity mapping is
        // deferred — field verdicts are hard-gated above, not compared to production here).
        // BO_EXTRA (BO-only Owning) is TRIAGED: expected relaxed-monotonicity improvement vs a
        // suspicious over-claim that should earn its own semantic control.
        let (mut covered, mut bo_extra, mut bo_owning_total) = (0usize, 0usize, 0usize);
        for (s, kind) in &model {
            if !matches!(s, SlotRef::Local(..)) || *kind != SlotKind::Owning {
                continue;
            }
            bo_owning_total += 1;
            if prod_owning.contains(s) {
                covered += 1;
            } else {
                bo_extra += 1;
            }
        }
        let bo_under = prod_owning
            .iter()
            .filter(|s| model.get(*s) != Some(&SlotKind::Owning))
            .count();
        eprintln!(
            "[BB-parity-own] {fn_name}: bo_owning(local)={bo_owning_total} prod_owning={} \
             COVERED={covered} BO_UNDER(safe)={bo_under} BO_EXTRA(triage)={bo_extra} \
             | witnesses PROD_AGREES={prod_agrees:?} PROD_MISSES(BO-improvement)={prod_misses:?}",
            prod_owning.len()
        );
    }

    /// Build the baseline ownership oracle's `Owning` set as depth-indexed BO slots, by
    /// running the ownership analysis via `analyze_program` -> `solidify` and mapping every
    /// `is_owning()` (local, depth) to a `SlotRef::Local`. BASELINE only — see
    /// `assert_ownership_parity`.
    ///
    /// PRECISION NOTE (Codex): `analyze_program` runs the ownership analysis with an EMPTY
    /// param-alias map — the same simplified reference the `ownership_analysis` tests use —
    /// NOT the Andersen points-to aliases (`find_param_aliases`) the real rewriter pipeline
    /// (`rewriter::replace_local_borrows`) feeds to `compute_output_params`. The two agree
    /// except where param aliasing changes output-param classification. The current
    /// focused-core fixtures are all non-aliasing (empty ≡ Andersen), so this is exact for
    /// them; an ALIAS-AWARE oracle (thread `find_param_aliases`) + an alias-sensitive
    /// fixture is DEFERRED with the other follow-ups (interproc / depth>=1 / field / coverage
    /// counters). Until then, do NOT add an alias-sensitive fixture expecting a faithful
    /// production comparison.
    fn build_prod_owning(
        tcx: TyCtxt<'_>,
        program: &RustProgram<'_>,
        slots: &CrateSlots,
    ) -> rustc_hash::FxHashSet<SlotRef> {
        let results = super::ownership_analysis::analyze_program(program);
        let solidified = results.solidify(program);
        let mut prod_owning = rustc_hash::FxHashSet::default();
        for &g in &program.functions {
            let Some(universe) = slots.fn_local_slots.get(&g) else {
                continue;
            };
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            let did = g.to_def_id();
            let fnr = solidified.fn_results(&did);
            for local in body.local_decls.indices() {
                for (depth, own) in fnr.local_result(local).iter().enumerate() {
                    if own.is_owning()
                        && let Some(sid) = universe.slot_for_local_depth(local, depth as u8)
                    {
                        prod_owning.insert(SlotRef::Local(g, sid));
                    }
                }
            }
        }
        prod_owning
    }

    /// BB-parity-own positive witness: a locally allocated-and-freed pointer is genuinely
    /// `Owning` in BOTH BO and the production oracle (no relaxed-monotonicity subtlety), so
    /// it seeds hard gate 1 (BO Owning) and hard gate 3 (production non-vacuity).
    #[test]
    fn boparity_alloc_free_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn f() {
    let p = malloc(4);
    free(p);
}
"#,
            |tcx| assert_ownership_parity(tcx, "f", &[loc("p")], &[]),
        );
    }

    /// BB-parity-own semantic non-Owning control: a read-only borrowed pointer param must
    /// NOT be `Owning` (over-claim = UAF on caller memory). Seeds hard gate 2.
    #[test]
    fn boparity_read_only_param_control() {
        run_compiler(
            r#"
pub unsafe fn reader(p: *mut i32) -> i32 {
    unsafe { *p }
}
"#,
            |tcx| assert_ownership_parity(tcx, "reader", &[], &[loc("p")]),
        );
    }

    /// BB-parity-own semantic non-Owning control (the §9.8 field-transfer): a borrowed
    /// struct pointer whose FIELD is malloc'd must NOT make the parent `owner` Owning —
    /// field-ownership transfer is not parent ownership (the output-param contract). This
    /// control has real teeth: at precision 2 WITHOUT the `field ⟹ parent` suppression BO
    /// over-claims `owner` (the reverted §9.8 regression), so a regression there fails here.
    #[test]
    fn boparity_field_transfer_parent_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub struct Holder {
    pub data: *mut core::ffi::c_void,
}

pub unsafe fn stash(owner: *mut Holder) {
    (*owner).data = unsafe { malloc(4) };
}
"#,
            |tcx| assert_ownership_parity(tcx, "stash", &[fld("Holder", 0)], &[loc("owner")]),
        );
    }

    /// BB-parity-own semantic non-Owning control: a pointer merely PASSED THROUGH to another
    /// function (no allocation, no free) must NOT be Owning — nothing owns it. Guards against
    /// BO's every-arg-is-Param::Output modeling over-claiming a pass-through.
    #[test]
    fn boparity_pass_through_param_control() {
        run_compiler(
            r#"
pub unsafe fn sink(q: *mut i32) -> i32 {
    unsafe { *q }
}

pub unsafe fn pass_through(p: *mut i32) -> i32 {
    unsafe { sink(p) }
}
"#,
            |tcx| assert_ownership_parity(tcx, "pass_through", &[], &[loc("p")]),
        );
    }

    /// BB-parity-own positive witness (the BB-escape win as a SEMANTIC verdict): a caller-side
    /// out-param `make(&raw mut local){ *out = malloc }` rewrites the caller-visible slot, so
    /// the caller's `local` MUST be Owning — the §9.9 output-param contract. RETURN-`local`
    /// shape so `local` is USED (an unused owning local leaks -> non-Owning, the fixture trap).
    #[test]
    fn boparity_caller_outparam_escape_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn make(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}

pub unsafe fn caller() -> *mut core::ffi::c_void {
    let mut local: *mut core::ffi::c_void = core::ptr::null_mut();
    unsafe { make(&raw mut local) };
    local
}
"#,
            |tcx| assert_ownership_parity(tcx, "caller", &[loc("local")], &[]),
        );
    }

    /// BB-parity-own positive witness (the deferred by-value depth-1 case, now working): a
    /// by-value double-pointer out-param `make_byval(pp){ *pp = malloc }` makes pp's depth-1
    /// pointee Owning while the outer pointer stays non-Owning — the depth>=1 ownership that
    /// coherence carries even though `link_versions_to_slots` is depth-0-only.
    #[test]
    fn boparity_byval_double_ptr_pointee_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub unsafe fn make_byval(pp: *mut *mut core::ffi::c_void) {
    *pp = unsafe { malloc(4) };
}
"#,
            |tcx| assert_ownership_parity(tcx, "make_byval", &[loc_at("pp", 1)], &[loc("pp")]),
        );
    }

    /// BB-parity-own positive witness (struct-field out-param transfer): a callee that mallocs
    /// into a struct field makes the FIELD slot Owning (routed to the StructFieldSlot), while
    /// the parent pointer stays non-Owning — the §9.10.2 goal, both sides.
    #[test]
    fn boparity_struct_field_outparam_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct Node {
    pub next: *mut core::ffi::c_void,
}
pub unsafe fn set_next(n: *mut Node) {
    (*n).next = unsafe { malloc(4) };
}
"#,
            |tcx| assert_ownership_parity(tcx, "set_next", &[fld("Node", 0)], &[loc("n")]),
        );
    }

    /// BB-parity-own semantic non-Owning control (borrowed field): a struct field that only
    /// ever receives a BORROWED pointer (a param, never malloc) must NOT be Owning — freeing
    /// it would be a UAF on caller memory.
    #[test]
    fn boparity_borrowed_field_control() {
        run_compiler(
            r#"
pub struct Bag {
    pub p: *mut i32,
}
pub unsafe fn stash_borrow(b: *mut Bag, src: *mut i32) {
    (*b).p = src;
}
"#,
            |tcx| {
                assert_ownership_parity(
                    tcx,
                    "stash_borrow",
                    &[],
                    &[fld("Bag", 0), loc("b"), loc("src")],
                )
            },
        );
    }

    /// BB-parity-own regression control (flow-insensitive global-field over-claim — FIXED §9.10.2).
    ///
    /// A struct field slot is a SINGLE crate-wide slot; `coherence` is flow-insensitive, so it
    /// equates that one slot to EVERY value assigned to the field. Here `cell_own` mallocs into
    /// `Cell::p` (an Owning source) and `cell_borrow` assigns a borrowed `src` into the SAME
    /// field. BEFORE the fix the malloc source forced the shared slot Owning, so `cell_borrow`
    /// over-claimed `Cell::p` and the rewriter would `Box`/free the borrowed `src` -> UAF.
    /// FIXED by the conservative field-ownership veto (`coherence::compute_borrowed_origin` +
    /// `KindSolver::veto_owning`): storing a borrowed-origin (a parameter, or a copy/cast/reborrow
    /// chain from one) value into a struct field HARD-vetoes that field slot's `own`, so it backs
    /// off to non-Owning (the retractable malloc source leaks — a safe leak, not a UAF). Guards
    /// that `Cell::p` stays non-Owning. Conservative: a field that only ever receives OWNED param
    /// transfers is also vetoed (a safe precision loss, not an over-claim).
    ///
    /// The adversarial sweep (2026-07-02, 10-family workflow probe) confirmed this was the SOLE
    /// real over-claim root cause and characterized its scope — a raw-pointer struct field
    /// (scalar `*mut T` or a multi-level `*mut *mut T` at its depth-0 slot) owned by a source
    /// (malloc/strdup/calloc) or sink (free) in one fn AND assigned a borrowed value in another;
    /// the param-origin veto covers all of them. NON-gaps (unchanged): deeper (depth>=1) chain
    /// levels UNDER-claim (safe leak); Rust array `[*mut T; N]` fields are unmodeled (no slot);
    /// unions unmodeled; realloc's arg-sink is CORRECT (realloc consumes its arg, like free).
    #[test]
    fn boparity_mixed_owned_borrowed_field_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct Cell {
    pub p: *mut core::ffi::c_void,
}
pub unsafe fn cell_own(c: *mut Cell) {
    (*c).p = unsafe { malloc(4) };
}
pub unsafe fn cell_borrow(c: *mut Cell, src: *mut core::ffi::c_void) {
    (*c).p = src;
}
"#,
            |tcx| assert_ownership_parity(tcx, "cell_borrow", &[], &[fld("Cell", 0)]),
        );
    }

    /// BB-parity-own regression control (mixed field via a PROJECTED borrowed load — Codex).
    /// The borrowed value reaches the field through `t = (*src).p` (a load through a borrowed
    /// param), not a direct param copy. `compute_borrowed_origin` propagates through the
    /// borrowed root so `t` counts as borrowed-origin; combined with `c_own`'s malloc into the
    /// same field, `C::p` is a mixed field and is vetoed to non-Owning. Without the
    /// projected-load propagation the over-claim survived (Owning).
    #[test]
    fn boparity_mixed_field_projected_borrow_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct C {
    pub p: *mut core::ffi::c_void,
}
pub unsafe fn c_own(c: *mut C) {
    (*c).p = unsafe { malloc(4) };
}
pub unsafe fn c_borrow_proj(dst: *mut C, src: *mut C) {
    let t = (*src).p;
    (*dst).p = t;
}
"#,
            |tcx| assert_ownership_parity(tcx, "c_borrow_proj", &[], &[fld("C", 0)]),
        );
    }

    /// BB-parity-own regression control (mixed field via an INTERPROC-return allocation —
    /// Codex). The owned side reaches the field via a local wrapper call `let p = d_make();
    /// (*d).p = p` (d_make returns malloc), which allocator-SOURCE detection does NOT flag.
    /// The veto uses "non-borrowed" evidence rather than allocation evidence, so the interproc
    /// alloc still counts: `D::p` is assigned a non-borrowed (`p`) value AND a borrowed (`src`)
    /// value, so it is vetoed to non-Owning. Without this the over-claim survived (Owning).
    #[test]
    fn boparity_mixed_field_interproc_alloc_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct D {
    pub p: *mut core::ffi::c_void,
}
pub unsafe fn d_make() -> *mut core::ffi::c_void {
    unsafe { malloc(4) }
}
pub unsafe fn d_own(d: *mut D) {
    let p = d_make();
    (*d).p = p;
}
pub unsafe fn d_borrow(d: *mut D, src: *mut core::ffi::c_void) {
    (*d).p = src;
}
"#,
            |tcx| assert_ownership_parity(tcx, "d_borrow", &[], &[fld("D", 0)]),
        );
    }

    /// BB-parity-own regression control (address-of / non-owned field store — Codex). A field
    /// with a malloc store (`E::p = malloc as *mut i32`, a Cast the collector follows to the
    /// owned operand) AND a direct address-of store (`(*e).p = &raw mut x`, a `RawPtr` rvalue)
    /// must NOT be Owning: it can hold a stack address, so freeing it is a UAF. The address
    /// store is not resolvable to an owned value, so `constrain_field_ownership` BLOCKS the
    /// field (`forbid_field_own`) rather than dropping it from the `AND` (which would wrongly
    /// permit Owning).
    #[test]
    fn boparity_addr_of_field_store_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct E {
    pub p: *mut i32,
}
pub unsafe fn e_own(e: *mut E) {
    (*e).p = unsafe { malloc(4) } as *mut i32;
}
pub unsafe fn e_addr(e: *mut E) {
    let mut x: i32 = 0;
    (*e).p = &raw mut x;
}
"#,
            |tcx| assert_ownership_parity(tcx, "e_addr", &[], &[fld("E", 0)]),
        );
    }

    /// BB-parity-own regression control (free-through-a-field projection — Codex). A field
    /// assigned a borrowed `src` and freed elsewhere via `free((*b).p)` must NOT drag `src`
    /// (or the field) to Owning: BO's free SINK, like its allocator sources, skips a PROJECTED
    /// argument, so `free((*b).p)` does not force the field Owning, and the borrowed store
    /// keeps it non-Owning. Guards that the field-ownership biconditional cannot be
    /// back-propagated by a field sink.
    #[test]
    fn boparity_free_through_field_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn free(ptr: *mut core::ffi::c_void);
}
pub struct F {
    pub p: *mut core::ffi::c_void,
}
pub unsafe fn f_stash(b: *mut F, src: *mut core::ffi::c_void) {
    (*b).p = src;
}
pub unsafe fn f_drop(b: *mut F) {
    free((*b).p);
}
"#,
            |tcx| assert_ownership_parity(tcx, "f_stash", &[], &[fld("F", 0), loc("src")]),
        );
    }

    /// §HLZ-PORT — witnesses for the point-keyed `requires` engine, LANDED.
    ///
    /// These shipped RED-first against a flag and asserted BOTH modes. The runtime selector was
    /// retired at landing (launch-6 precedent), so each now pins the landed engine's behaviour
    /// directly — the content the two-mode comparison used to establish, asserted as content.
    mod hlz_port_witnesses {
        use rustc_hash::FxHashMap;
        use rustc_middle::mir::Local;
        use rustc_span::def_id::LocalDefId;

        use super::{collect_program, run_compiler};
        use crate::analyses::{
            borrow::ConflictEdge,
            borrow_ownership::borrow_engine::{
                borrow_conflicts, demotion_witness_census, loan_liveness_census,
            },
        };

        /// Canonical, order-insensitive rendering of a conflict-edge map.
        fn canonical(edges: &FxHashMap<LocalDefId, Vec<ConflictEdge>>) -> Vec<String> {
            let mut out: Vec<String> = edges
                .iter()
                .flat_map(|(did, es)| {
                    es.iter().map(move |e| {
                        let mut requirers: Vec<String> =
                            e.requirers.iter().map(|o| format!("{o:?}")).collect();
                        requirers.sort();
                        format!("{did:?} issuer={:?} requirers={requirers:?}", e.issuer)
                    })
                })
                .collect();
            out.sort();
            out
        }

        fn edges(code: &str) -> Vec<String> {
            edges_with_mut(code, true)
        }

        fn edges_with_mut(code: &str, mutb: bool) -> Vec<String> {
            let mut captured = Vec::new();
            run_compiler(code, |tcx| {
                let program = collect_program(tcx);
                captured = canonical(&borrow_conflicts(
                    &program,
                    |_: LocalDefId| |_: Local| true,
                    move |_: LocalDefId| move |_: Local| mutb,
                ));
            });
            captured
        }

        /// **W1 — the edge-gate regression control.** Two reborrows of the same pointee, the
        /// first's last use strictly before the second's write. The conflict is REAL: the borrow
        /// is still in scope at the write, and an early cut of the port dropped it only because
        /// its CFG step was gated at the wrong end relative to a matrix holding EXIT liveness
        /// (port record §3.6/§4). Its `requirers=[]` signature is not a defect either — the
        /// invalidation lands one step past the borrower's last use, so the issuer carries the
        /// demotion alone.
        #[test]
        fn port_reborrow_chain_conflict_survives_the_edge_gate() {
            const CODE: &str = "unsafe fn f(p: *mut i32) -> i32 { let a = &mut *p as *mut i32; \
                 let v = *a; let b = &mut *p as *mut i32; *b = 1; v }";
            let e = edges(CODE);
            assert_eq!(
                e.len(),
                1,
                "exactly one conflict is expected here; got {e:?}"
            );
            assert!(
                e[0].ends_with("requirers=[]"),
                "the shape's signature is an issuer-only edge (no live requirer at the error \
                 row); got {e:?}"
            );
        }

        /// **W2 — the survival control.** A write while the borrow is still live is a genuine
        /// invalidation and must be reported. Without this, W1 would be satisfied by an engine
        /// that simply stopped reporting conflicts.
        #[test]
        fn port_live_requirer_conflict_survives() {
            const CODE: &str =
                "unsafe fn f() -> i32 { let mut x = 0i32; let p = &raw mut x; x = 2; *p }";
            assert!(
                !edges(CODE).is_empty(),
                "a write while the borrow is live must conflict"
            );
        }

        /// **W3 — `CallArg` inertness is structural.** The walk is seeded from `membership`
        /// alone, and `NativeConstraintGraph::new` never gives a `CallArg` loan a membership
        /// constraint (production does not either — `borrow/mod.rs` pushes membership only in
        /// `visit_assign`). So such a loan is live at NO point, where the flow-insensitive
        /// engine kept it live at exactly the one point after its call terminator ("M1
        /// temporal"). Asserted on `loan_liveness` directly: the conflict-edge surface reports an
        /// absence either way and cannot tell "never live" from "live but inert".
        #[test]
        fn port_callarg_loan_never_live() {
            const CODE: &str = "unsafe fn g(q: *mut i32) { *q = 1; } \
                                unsafe fn f() { let mut x = 0i32; let p = &raw mut x; g(p); }";
            let mut points = Vec::new();
            run_compiler(CODE, |tcx| {
                let program = collect_program(tcx);
                let census = loan_liveness_census(
                    &program,
                    |_: LocalDefId| |_: Local| true,
                    |_: LocalDefId| |_: Local| true,
                );
                points = census
                    .values()
                    .flatten()
                    .filter(|(_, is_call_arg, _)| *is_call_arg)
                    .map(|(_, _, live_points)| *live_points)
                    .collect();
                points.sort();
            });
            assert_eq!(
                points,
                vec![0],
                "seeded from `membership` alone, a CallArg loan must be live at no point at all"
            );
        }

        /// **W4 — NB4-R routed cross-alias write.** The engine never reads or writes
        /// `invalidates`, but `errors = loan_liveness ∩ invalidates`, so a routed invalidation
        /// would silently stop producing an error if the left operand lost the loan. This is the
        /// S2-6 closure shape whose routed edge the fork adds over production.
        #[test]
        fn port_cross_alias_write_still_routed() {
            const CODE: &str = "#[inline(never)] unsafe fn id(mut p: *mut i32) -> *mut i32 { p } \
                 unsafe fn f(mut p: *mut i32) -> i32 { let b = p; let x = id(p); let z = x; \
                 let r0 = *z; *b = 5; r0 + *z }";
            assert!(
                !edges(CODE).is_empty(),
                "the routed cross-alias write must still conflict"
            );
        }

        /// **W5 — the mutability axis stays flat on the read shape.** The read/write asymmetry
        /// lives in the fork's `invalidates`, which the engine does not consult; the observable is
        /// that this shape's conflict is generated identically at both mutabilities. The
        /// `mut=true` arm carries the non-vacuity.
        #[test]
        fn port_write_aware_immutable_read_still_skipped() {
            const CODE: &str = "unsafe fn f() { let mut x = 0i32; let a = &mut x as *mut i32; \
                 let b = &mut x as *mut i32; let u = *a; let v = *b; let _ = (u, v); }";
            let hot = edges_with_mut(CODE, true);
            assert!(!hot.is_empty(), "aliasing mutable borrows must conflict");
            assert_eq!(
                hot,
                edges_with_mut(CODE, false),
                "the engine must not introduce a mutability-dependent difference here"
            );
        }

        /// **W6 — monotonicity, executed rather than argued.** The engine carries a
        /// release-active subset tripwire (`loan_liveness♯ ⊆ loan_liveness` and
        /// `requires♯ ⊆ requires` after projecting the point key away) against the retained
        /// flow-insensitive reference. This drives it over the other witnesses' shapes plus the
        /// branch shapes it is most likely to catch. A fire is a STOP, not a fix.
        #[test]
        fn port_localized_facts_are_a_subset() {
            const SHAPES: &[&str] = &[
                "unsafe fn f() -> i32 { let mut x = 0i32; let p = &raw mut x; let v = *p; x = 2; v }",
                "unsafe fn f() -> i32 { let mut x = 0i32; let p = &raw mut x; x = 2; *p }",
                "unsafe fn f(cond: bool) { let mut x = 0i32; let mut y = 0i32; let a = &raw mut x; \
                 let mut b = &raw mut y; if cond { b = a; *b = 1; } else { x = 2; *b = 3; } }",
                "unsafe fn f(c: bool, p: *mut i32) -> i32 { let mut q = p; let mut t = 0i32; \
                 if c { q = &raw mut t; } *q = 1; *q }",
                "#[inline(never)] unsafe fn id(mut p: *mut i32) -> *mut i32 { p } \
                 unsafe fn f(mut p: *mut i32) -> i32 { let b = p; let x = id(p); let z = x; \
                 let r0 = *z; *b = 5; r0 + *z }",
                "unsafe fn g(q: *mut i32) { *q = 1; } \
                 unsafe fn f() { let mut x = 0i32; let p = &raw mut x; g(p); }",
            ];
            for code in SHAPES {
                // The assertion is inside the engine; reaching here without a panic IS the pass.
                let _ = edges(code);
            }
        }

        /// **W7 — conflict generation, witnessed on its own.** Pins the ACTUAL edge content, so
        /// an engine that stopped generating conflicts cannot satisfy it. Required by the
        /// adversarial review: a mutual-consistency assertion between two consumers of one
        /// relation cannot detect a required invalidation deleted on both sides.
        #[test]
        fn port_conflict_generation_is_witnessed_independently() {
            const CODE: &str = "unsafe fn f() { let mut x = 0i32; let a = &mut x as *mut i32; \
                 let b = &mut x as *mut i32; let c = &mut x as *mut i32; *a = 1; *b = 2; *c = 3; }";
            let e = edges(CODE);
            assert_eq!(
                e.len(),
                2,
                "both aliasing conflicts must be GENERATED in this three-alias shape; got {e:?}"
            );
            assert!(
                e.iter().all(|x| x.contains("issuer=Some(")),
                "each generated edge must carry an issuer; got {e:?}"
            );
            assert!(
                e.iter().any(|x| x.contains("requirers=[\"Local(")),
                "at least one generated edge must attribute a live requirer — the half the
                 point-keyed predicate could silently empty; got {e:?}"
            );
        }

        /// **W8 — demotion witnesses, observed on their own.** The other half of the review's
        /// requirement: read straight out of the forked collector, with no reference to the
        /// conflict-edge set, so the two can disagree loudly rather than fail silently together.
        #[test]
        fn port_demotion_witnesses_are_observed_independently() {
            const CODE: &str = "unsafe fn f() { let mut x = 0i32; let a = &mut x as *mut i32; \
                 let b = &mut x as *mut i32; let c = &mut x as *mut i32; *a = 1; *b = 2; *c = 3; }";
            let mut all: Vec<(usize, usize)> = Vec::new();
            run_compiler(CODE, |tcx| {
                let program = collect_program(tcx);
                let census = demotion_witness_census(
                    &program,
                    |_: LocalDefId| |_: Local| true,
                    |_: LocalDefId| |_: Local| true,
                );
                all = census.values().flatten().copied().collect();
                all.sort();
            });
            assert_eq!(
                all,
                vec![(2, 1), (3, 1), (4, 1), (5, 1)],
                "the demotion side must PRODUCE these witnesses, checked separately from the edge \
                 side so a predicate that emptied both would still be caught"
            );
        }
    }
}

mod borrow_ownership_resolve {
    use rustc_abi::FieldIdx;
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{
        mir::{Local, Place, ProjectionElem},
        ty::{Ty, TyCtxt, TyKind},
    };
    use rustc_span::def_id::LocalDefId;

    use crate::{
        analyses::borrow_ownership::{
            crate_slots::{CrateSlots, ptr_chain_depth},
            ptr::decompose_ty,
            resolve::{ResolvedSlot, resolve_place},
            slots::StructFieldSlot,
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

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

    fn struct_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .structs
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("struct `{name}` not found"))
    }

    fn function_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .functions
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    fn struct_field_ty<'tcx>(
        tcx: TyCtxt<'tcx>,
        struct_did: LocalDefId,
        field_index: usize,
    ) -> Ty<'tcx> {
        let ty = tcx.type_of(struct_did).skip_binder();
        let TyKind::Adt(adt, substs) = ty.kind() else {
            panic!("expected struct ADT type");
        };

        adt.all_fields()
            .nth(field_index)
            .unwrap_or_else(|| panic!("field index {field_index} not found"))
            .ty(tcx, substs)
    }

    #[test]
    fn resolve_local_chain_depths() {
        run_compiler(
            r#"
pub unsafe fn g(pp: *mut *mut i32) -> i32 {
    **pp
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let g = function_by_name(&program, "g");
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                let body = &*body;
                let pp = Local::from_u32(1);
                let base = Place::from(pp);
                let fn_locals = slots.fn_local_slots.get(&g).expect("slots for g");

                assert_eq!(
                    resolve_place(&slots, g, body, base, 0, None),
                    fn_locals
                        .slot_for_local_depth(pp, 0)
                        .map(ResolvedSlot::Local)
                );
                assert_eq!(
                    resolve_place(&slots, g, body, base, 1, None),
                    fn_locals
                        .slot_for_local_depth(pp, 1)
                        .map(ResolvedSlot::Local)
                );
                assert_eq!(resolve_place(&slots, g, body, base, 2, None), None);
            },
        );
    }

    /// §NB1: the `layers` out-param records every pointer slot *dereferenced*
    /// to reach the target (shallowest first), which the SAFE-MONO walk pairs
    /// with the target. The target itself is not a layer; a bare local
    /// traverses none.
    #[test]
    fn resolve_place_collects_traversed_layers() {
        run_compiler(
            r#"
pub unsafe fn g(ppp: *mut *mut *mut i32) -> i32 {
    ***ppp
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let g = function_by_name(&program, "g");
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                let body = &*body;
                let ppp = Local::from_u32(1);
                let fn_locals = slots.fn_local_slots.get(&g).expect("slots for g");
                let d = |depth| {
                    fn_locals
                        .slot_for_local_depth(ppp, depth)
                        .map(ResolvedSlot::Local)
                        .unwrap()
                };

                // `**ppp` (two real Deref projections) targets depth 2, and
                // traverses layers depth 0 then depth 1.
                let two_derefs = Place::from(ppp)
                    .project_deeper(&[ProjectionElem::Deref, ProjectionElem::Deref], tcx);
                let mut layers = Vec::new();
                let target = resolve_place(&slots, g, body, two_derefs, 0, Some(&mut layers));
                assert_eq!(target, Some(d(2)));
                assert_eq!(layers, vec![d(0), d(1)]);

                // A bare local (no deref) traverses no layers.
                let mut none = Vec::new();
                let bare = resolve_place(&slots, g, body, Place::from(ppp), 0, Some(&mut none));
                assert_eq!(bare, Some(d(0)));
                assert!(none.is_empty(), "a bare local dereferences nothing");
            },
        );
    }

    #[test]
    fn resolve_struct_field() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub a: *mut i32,
    pub b: *mut i32,
}

pub unsafe fn f(s: *mut S) {
    let _x = (*s).a;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let f = function_by_name(&program, "f");
                let s = struct_by_name(&program, "S");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let body = &*body;
                let s_local = Local::from_u32(1);
                let field_a_ty = struct_field_ty(tcx, s, 0);
                let field_a = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };
                let place = Place::from(s_local).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(0), field_a_ty),
                    ],
                    tcx,
                );

                assert_eq!(
                    resolve_place(&slots, f, body, place, 0, None),
                    slots
                        .field_slots
                        .slot_for_field_depth(field_a, 0)
                        .map(ResolvedSlot::Field)
                );
                assert_eq!(
                    resolve_place(&slots, f, body, Place::from(s_local), 0, None),
                    slots
                        .fn_local_slots
                        .get(&f)
                        .expect("slots for f")
                        .slot_for_local_depth(s_local, 0)
                        .map(ResolvedSlot::Local)
                );
            },
        );
    }

    #[test]
    fn resolve_capped_deref_then_field_is_conservative() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub a: *mut i32,
}

pub unsafe fn ok_field(q: *mut *mut *mut S) -> *mut i32 {
    (***q).a
}

pub unsafe fn deep_field(p: *mut *mut *mut *mut S) -> *mut i32 {
    (****p).a
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let ok_field = function_by_name(&program, "ok_field");
                let deep_field = function_by_name(&program, "deep_field");
                let field_a_ty = struct_field_ty(tcx, s, 0);
                let field_a = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };
                let expected_field = slots
                    .field_slots
                    .slot_for_field_depth(field_a, 0)
                    .map(ResolvedSlot::Field);

                let ok_body = tcx
                    .mir_drops_elaborated_and_const_checked(ok_field)
                    .borrow();
                let ok_body = &*ok_body;
                let q = Local::from_u32(1);
                let ok_place = Place::from(q).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(0), field_a_ty),
                    ],
                    tcx,
                );
                assert_eq!(
                    resolve_place(&slots, ok_field, ok_body, ok_place, 0, None),
                    expected_field
                );

                let deep_body = tcx
                    .mir_drops_elaborated_and_const_checked(deep_field)
                    .borrow();
                let deep_body = &*deep_body;
                let p = Local::from_u32(1);
                let deep_place = Place::from(p).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(0), field_a_ty),
                    ],
                    tcx,
                );
                assert_eq!(
                    resolve_place(&slots, deep_field, deep_body, deep_place, 0, None),
                    None
                );
            },
        );
    }

    #[test]
    fn resolve_depth_cap_conservative() {
        run_compiler(
            r#"
pub unsafe fn deep(p: *mut *mut *mut *mut i32) -> i32 {
    ****p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let deep = function_by_name(&program, "deep");
                let body = tcx.mir_drops_elaborated_and_const_checked(deep).borrow();
                let body = &*body;
                let p = Local::from_u32(1);
                let base = Place::from(p);
                let fn_locals = slots.fn_local_slots.get(&deep).expect("slots for deep");

                for depth in 0..3 {
                    assert_eq!(
                        resolve_place(&slots, deep, body, base, depth, None),
                        fn_locals
                            .slot_for_local_depth(p, depth)
                            .map(ResolvedSlot::Local)
                    );
                }
                assert_eq!(resolve_place(&slots, deep, body, base, 3, None), None);
            },
        );
    }

    #[test]
    fn resolve_array_conservative() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub arr: [*mut i32; 4],
    pub scalar: *mut i32,
}

pub unsafe fn h(s: *mut S, a: [*mut i32; 4]) {
    let _x = (*s).arr;
    let _y = a;
    let _z = (*s).scalar;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let h = function_by_name(&program, "h");
                let s = struct_by_name(&program, "S");
                let body = tcx.mir_drops_elaborated_and_const_checked(h).borrow();
                let body = &*body;
                let s_local = Local::from_u32(1);
                let array_param = Local::from_u32(2);
                let arr_ty = struct_field_ty(tcx, s, 0);
                let scalar_ty = struct_field_ty(tcx, s, 1);
                let arr_place = Place::from(s_local).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(0), arr_ty),
                    ],
                    tcx,
                );
                let scalar_place = Place::from(s_local).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(1), scalar_ty),
                    ],
                    tcx,
                );
                let scalar_field = StructFieldSlot {
                    struct_did: s,
                    field_index: 1,
                };

                assert_eq!(resolve_place(&slots, h, body, arr_place, 0, None), None);
                assert_eq!(
                    resolve_place(&slots, h, body, Place::from(array_param), 0, None),
                    None
                );
                assert_eq!(
                    resolve_place(&slots, h, body, scalar_place, 0, None),
                    slots
                        .field_slots
                        .slot_for_field_depth(scalar_field, 0)
                        .map(ResolvedSlot::Field)
                );
            },
        );
    }

    #[test]
    fn reconciliation_depth_models() {
        run_compiler(
            r#"
pub unsafe fn recon(
    chain2: *mut *mut i32,
    arr: [*mut i32; 4],
    deep: *mut *mut *mut *mut i32,
) {
    let _ = chain2;
    let _ = arr;
    let _ = deep;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let recon = function_by_name(&program, "recon");
                let body = tcx.mir_drops_elaborated_and_const_checked(recon).borrow();
                let body = &*body;
                let chain2_ty = body.local_decls[Local::from_u32(1)].ty;
                let arr_ty = body.local_decls[Local::from_u32(2)].ty;
                let deep_ty = body.local_decls[Local::from_u32(3)].ty;

                assert_eq!(ptr_chain_depth(chain2_ty), 2);
                assert_eq!(decompose_ty(chain2_ty).0, 2);

                assert_eq!(ptr_chain_depth(arr_ty), 0);
                assert_eq!(decompose_ty(arr_ty).0, 1);

                assert_eq!(ptr_chain_depth(deep_ty), 3);
                assert_eq!(decompose_ty(deep_ty).0, 4);
            },
        );
    }
}

#[test]
fn borrow_ownership_slot_universe_tracks_local_pointer_depths() {
    use rustc_middle::mir::Local;
    use rustc_span::def_id::{DefIndex, LocalDefId};

    use crate::analyses::borrow_ownership::{
        SlotKind,
        slots::{SlotId, SlotOwner, SlotUniverse, StructFieldSlot},
    };

    assert_eq!(
        SlotKind::ALL,
        [SlotKind::Raw, SlotKind::Ref, SlotKind::Owning]
    );

    let pointer = Local::from_u32(1);
    let nested_pointer = Local::from_u32(2);
    let unregistered = Local::from_u32(3);
    let field = StructFieldSlot {
        struct_did: LocalDefId {
            local_def_index: DefIndex::from_u32(42),
        },
        field_index: 1,
    };
    let mut universe = SlotUniverse::from_local_depths([(pointer, 1), (nested_pointer, 2)]);
    universe.register_field(field, 2);

    assert_eq!(universe.len(), 5);
    assert_eq!(
        universe.slots_for_local(pointer),
        Some(SlotId::from_usize(0)..SlotId::from_usize(1))
    );
    assert_eq!(
        universe.slots_for_local(nested_pointer),
        Some(SlotId::from_usize(1)..SlotId::from_usize(3))
    );
    assert_eq!(
        universe.slots_for_field(field),
        Some(SlotId::from_usize(3)..SlotId::from_usize(5))
    );

    let pointer_slot = universe
        .slot_for_local_depth(pointer, 0)
        .expect("slot for local pointer");
    assert_eq!(pointer_slot, SlotId::from_usize(0));
    assert_eq!(universe.slot(pointer_slot).owner, SlotOwner::Local(pointer));
    assert_eq!(universe.slot(pointer_slot).depth, 0);

    assert!(universe.slot_for_local_depth(pointer, 1).is_none());
    assert!(universe.slots_for_local(unregistered).is_none());
    assert!(universe.slot_for_local_depth(unregistered, 0).is_none());

    let nested_outer = universe
        .slot_for_local_depth(nested_pointer, 0)
        .expect("outer slot for nested pointer");
    let nested_inner = universe
        .slot_for_local_depth(nested_pointer, 1)
        .expect("inner slot for nested pointer");

    assert_eq!(nested_outer, SlotId::from_usize(1));
    assert_eq!(nested_inner, SlotId::from_usize(2));
    assert_eq!(
        universe.slot(nested_outer).owner,
        SlotOwner::Local(nested_pointer)
    );
    assert_eq!(
        universe.slot(nested_inner).owner,
        SlotOwner::Local(nested_pointer)
    );
    assert_eq!(universe.slot(nested_outer).depth, 0);
    assert_eq!(universe.slot(nested_inner).depth, 1);
    assert!(universe.slot_for_local_depth(nested_pointer, 2).is_none());

    let field_outer = universe
        .slot_for_field_depth(field, 0)
        .expect("outer field slot");
    let field_inner = universe
        .slot_for_field_depth(field, 1)
        .expect("inner field slot");

    assert_eq!(field_outer, SlotId::from_usize(3));
    assert_eq!(field_inner, SlotId::from_usize(4));
    assert_eq!(universe.slot(field_outer).owner, SlotOwner::Field(field));
    assert_eq!(universe.slot(field_inner).owner, SlotOwner::Field(field));
    assert_eq!(universe.slot(field_outer).depth, 0);
    assert_eq!(universe.slot(field_inner).depth, 1);
    assert!(universe.slot_for_field_depth(field, 2).is_none());
}
