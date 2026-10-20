//! E11 observes one production construction with export capture off and on.

use rustc_hir::{ItemKind, OwnerNode};

use super::super::{
    borrow_verify::{RepairMode, with_mode_a_commit_trace},
    construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
    crate_slots::CrateSlots,
    export,
    mutability_facts::MutFacts,
    origins::compute_origins,
    solver::{KindSolver, with_ownership_model_observation, with_selector_trace},
};
use crate::utils::rustc::RustProgram;

#[test]
fn e11_export_on_off_preserves_models_selectors_repairs_and_all_ownership_vars() {
    ::utils::compilation::run_compiler_on_str(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut i32);
}
pub unsafe fn make() -> *mut i32 {
    let ptr = malloc(4);
    *ptr = 7;
    ptr
}
pub unsafe fn release() {
    let ptr = make();
    free(ptr);
}
"#,
        |tcx| {
            let functions = tcx
                .hir_crate(())
                .owners
                .iter()
                .filter_map(|owner| {
                    let owner = owner.as_owner()?;
                    let OwnerNode::Item(item) = owner.node() else { return None };
                    matches!(item.kind, ItemKind::Fn { .. }).then_some(item.owner_id.def_id)
                })
                .collect();
            let program = RustProgram {
                tcx,
                functions,
                structs: Vec::new(),
            };
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let facts = MutFacts::from_program(&program);
            let run = || {
                with_ownership_model_observation(|| {
                    with_selector_trace(|| {
                        with_mode_a_commit_trace(|| {
                            RepairMode::with_override(RepairMode::ModeA, || {
                                let solver = KindSolver::new(&slots);
                                let construction = construct_bo_into(
                                    &program,
                                    &slots,
                                    &origins,
                                    &facts,
                                    &solver,
                                    CopyLendMode::Baseline,
                                )
                                .expect("E11 production construction");
                                let result = verify_bo_construction_counting(
                                    &program,
                                    &slots,
                                    &origins,
                                    &solver,
                                    &construction,
                                    &facts,
                                );
                                (result, construction.stats.z3_ast_len)
                            })
                        })
                    })
                })
            };

            assert!(!export::capturing(), "off run must have no export scope");
            let ((((off_result, off_len), off_commits), off_selectors), off_owns) = run();
            assert!(!export::capturing(), "observation must not arm export");
            let (((((on_result, on_len), on_commits), on_selectors), on_owns), captured) =
                export::with_bo_export(run);
            assert!(!export::capturing(), "on scope must restore export state");

            assert!(
                off_result.0.is_some(),
                "off run declined: {:?}",
                off_result.1
            );
            assert!(on_result.0.is_some(), "on run declined: {:?}", on_result.1);
            assert_eq!(off_result, on_result, "accepted kinds and all round stats");
            assert_eq!(off_selectors, on_selectors, "exact T2 trace");
            assert_eq!(off_selectors.n_sources, 1);
            assert_eq!(off_selectors.total, 2);
            assert!(!off_selectors.epochs.is_empty());
            assert_eq!(off_commits.len(), on_commits.len(), "repair commit count");
            for (off, on) in off_commits.iter().zip(&on_commits) {
                assert_eq!(off.target, on.target);
                assert_eq!(off.round, on.round);
                assert_eq!(off.conflict.issuer, on.conflict.issuer);
                assert_eq!(off.conflict.requirers, on.conflict.requirers);
                assert_eq!(off.conflict.esc_issuer_first, on.conflict.esc_issuer_first);
            }

            assert!(off_len > 1, "real ownership Vars beyond the dummy index");
            assert_eq!(off_len, on_len);
            assert_eq!(off_owns.snapshot_lengths, vec![off_len]);
            assert_eq!(on_owns.snapshot_lengths, vec![on_len]);
            assert!(
                !off_owns.model_reads.is_empty(),
                "a real model must be read"
            );
            for values in off_owns.model_reads.iter().chain(&on_owns.model_reads) {
                assert_eq!(values.len(), off_len, "every ownership Var is evaluated");
            }
            assert_eq!(off_owns, on_owns, "all indexed ownership model reads");
            assert_eq!(
                captured.version_owns.as_ref(),
                on_owns.model_reads.last(),
                "export records the same final ownership valuation"
            );
        },
    )
    .unwrap_or_else(|error| error.raise());
}
