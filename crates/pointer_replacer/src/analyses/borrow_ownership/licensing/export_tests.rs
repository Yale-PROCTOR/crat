//! T14 completed normative snapshots, optional export and namespace joins.
use rustc_hir::{ItemKind, OwnerNode};

use super::super::{
    construction::{CopyLendMode, construct_bo_into},
    crate_slots::CrateSlots,
    execution_guard::{self, ExecutionRole},
    export,
    mutability_facts::MutFacts,
    origin_evidence,
    origins::compute_origins,
    solver::KindSolver,
};
use crate::utils::rustc::RustProgram;

#[test]
fn t14_optional_export_copies_normative_snapshots_with_explicit_construction_offsets() {
    ::utils::compilation::run_compiler_on_str(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make() -> *mut i32 { malloc(4) }
pub unsafe fn run() { let p = make(); free(p); }
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
            let mutability = MutFacts::from_program(&program);
            let construct = || {
                let solver = KindSolver::new(&slots);
                construct_bo_into(
                    &program,
                    &slots,
                    &origins,
                    &mutability,
                    &solver,
                    CopyLendMode::Baseline,
                )
                .unwrap();
                assert_eq!(
                    [
                        solver.check_sat_count(),
                        solver.hard_check_count(),
                        solver.optimize_materialization_count(),
                        solver.lazy_plain_hard_check_count(),
                        solver.lazy_tracked_recheck_count(),
                        solver.lazy_plain_materialization_count()
                    ],
                    [0; 6]
                );
                solver.ownership_facts().unwrap()
            };
            let off = construct();
            let ((first, second), captured) = export::with_bo_export(|| (construct(), construct()));
            assert_eq!(
                off.licensing.as_ref().unwrap().matched,
                first.licensing.as_ref().unwrap().matched
            );
            assert_eq!(
                first.licensing.as_ref().unwrap().matched,
                second.licensing.as_ref().unwrap().matched
            );
            let snapshots = captured
                .ownership_licensing
                .as_ref()
                .expect("optional export must copy completed normative snapshots");
            assert_eq!(snapshots.len(), 2);
            assert_eq!(captured.ownership_constructions, 2);
            for (index, snapshot) in snapshots.iter().enumerate() {
                assert_eq!(snapshot.offset, index as u32);
                assert_eq!(snapshot.metadata.constructions, 1);
                assert!(
                    snapshot
                        .metadata
                        .equations
                        .iter()
                        .all(|row| row.point.construction == 0)
                );
                let mut flat: Vec<_> = captured
                    .ownership_equations
                    .as_ref()
                    .unwrap()
                    .iter()
                    .filter(|row| row.point.construction == snapshot.offset)
                    .cloned()
                    .collect();
                for row in &mut flat {
                    row.point.construction -= snapshot.offset;
                }
                assert_eq!(flat, snapshot.metadata.equations);
                execution_guard::with_role(ExecutionRole::CacheOnly, || snapshot.validate())
                    .unwrap();
            }
            let origin = origin_evidence::collect(&program, &slots, &origins, Some(&captured));
            assert_eq!(origin.licensing.as_ref(), Some(snapshots));
            assert!(
                origin_evidence::collect(&program, &slots, &origins, None)
                    .licensing
                    .is_none()
            );
        },
    )
    .unwrap_or_else(|error| error.raise());
}
