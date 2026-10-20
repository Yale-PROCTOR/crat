//! Normative transport inputs must exist with the optional exporter disabled.

use rustc_hir::{ItemKind, OwnerNode};

use super::super::{
    construction::{CopyLendMode, construct_bo_into},
    crate_slots::CrateSlots,
    export,
    mutability_facts::MutFacts,
    origins::compute_origins,
    solver::KindSolver,
};
use crate::utils::rustc::RustProgram;

#[test]
fn t01_actual_ownership_facts_exist_without_export_and_match_exported_observations() {
    ::utils::compilation::run_compiler_on_str(
        r#"
        unsafe extern "C" { fn malloc(n:usize)->*mut i32; fn free(p:*mut i32); }
        pub unsafe fn make()->*mut i32 { let p=malloc(4); p }
        pub unsafe fn run() { let p=make(); free(p); }
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
            let construct = || {
                let solver = KindSolver::new(&slots);
                let built = construct_bo_into(
                    &program,
                    &slots,
                    &origins,
                    &facts,
                    &solver,
                    CopyLendMode::Baseline,
                )
                .unwrap();
                assert_eq!(solver.check_sat_count(), 0);
                assert_eq!(solver.hard_check_count(), 0);
                let facts = solver
                    .ownership_facts()
                    .expect("normative facts must come from actual emission even with export off");
                assert_eq!(facts.ownership_asts.len(), built.stats.z3_ast_len);
                assert!(!facts.equations.is_empty());
                assert!(!facts.consumes.is_empty());
                assert!(!facts.terminals.is_empty());
                assert!(!facts.boundary_substitutions.is_empty());
                facts
            };
            assert!(!export::capturing());
            let off = construct();
            let (on, captured) = export::with_bo_export(construct);
            assert_eq!(
                serde_json::to_value(&off.equations).unwrap(),
                serde_json::to_value(&on.equations).unwrap()
            );
            assert_eq!(off.consumes, on.consumes);
            assert_eq!(off.terminals, on.terminals);
            assert_eq!(off.boundary_substitutions, on.boundary_substitutions);
            assert_eq!(off.call_arg_registrations, on.call_arg_registrations);
            assert_eq!(captured.ownership_equations.as_ref(), Some(&on.equations));
            let ((first, second), combined) = export::with_bo_export(|| (construct(), construct()));
            assert!(
                first
                    .equations
                    .iter()
                    .chain(&second.equations)
                    .all(|eq| eq.point.construction == 0),
                "core identities remain local to their construction"
            );
            assert_eq!(combined.ownership_constructions, 2);
            let ids: std::collections::BTreeSet<_> = combined
                .ownership_equations
                .as_ref()
                .unwrap()
                .iter()
                .map(|eq| eq.point.construction)
                .collect();
            assert_eq!(
                ids,
                [0, 1].into_iter().collect(),
                "optional export gives the two snapshots distinct namespaces"
            );
            let evidence =
                super::super::origin_evidence::collect(&program, &slots, &origins, Some(&combined));
            for function in evidence.functions {
                use super::super::origin_evidence::OriginAvailability::Present;
                let Present(equations) = function.ownership.equations else { panic!("equations") };
                let Present(consumes) = function.ownership.consumes else { panic!("consumes") };
                let Present(boundaries) = function.ownership.boundary_substitutions else {
                    panic!("boundaries")
                };
                let Present(registrations) = function.ownership.call_arg_registrations else {
                    panic!("registrations")
                };
                super::super::ownership_evidence::validate_function(&equations, &function.function)
                    .unwrap();
                super::super::ownership_occurrence::validate(
                    &function.function,
                    &consumes,
                    &equations,
                )
                .unwrap();
                super::super::ownership_boundary::validate_links(
                    &function.function,
                    &boundaries,
                    &registrations,
                    &consumes,
                    &equations,
                )
                .unwrap();
            }
        },
    )
    .unwrap_or_else(|error| error.raise());
}
