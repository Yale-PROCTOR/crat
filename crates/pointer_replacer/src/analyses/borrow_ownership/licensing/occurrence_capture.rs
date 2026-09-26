//! R237's explicitly invoked bst-only construction diagnostic. Never a model worker.

#[test]
#[ignore = "R237 bst-only zero-solve capture; requires its sealed supervisor"]
fn e06_bst_occurrence_capture() {
    use std::{io::Write, path::Path};

    use rustc_hir::{ItemKind, OwnerNode};
    use sha2::{Digest, Sha256};

    use super::super::{
        construction::construct_bo_into_a16_refined, crate_slots::CrateSlots, execution_guard,
        export, mutability_facts::MutFacts, origin_evidence, origins::compute_origins,
        solver::KindSolver,
    };
    use crate::utils::rustc::RustProgram;

    let input = Path::new("/home/p51lee/dev/crat/benchmarks/rs-crown-derived/bst/lib.rs");
    let expected = "5d84bf03e4aebd1aef2b4ef556018d3f0ebdf17be737a9a61e9785f5542c74bf";
    assert_eq!(
        format!("{:x}", Sha256::digest(std::fs::read(input).unwrap())),
        expected
    );
    let output = std::env::var("CRAT_ERA5B_OCCURRENCE_OUTPUT").expect("sealed durable output");
    assert_eq!(
        output,
        "/home/p51lee/dev/agent-worktrees/crat-docs-era5b-licensing-execution-20260908/agents/artifacts/2026-09-08-era5b-r237/bst-occurrences.json"
    );
    assert!(
        !Path::new(&output).exists(),
        "immutable diagnostic output already exists"
    );
    let payload=::utils::compilation::run_compiler_on_path(input, |tcx| {
        let mut functions=Vec::new(); let mut structs=Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner)=owner.as_owner() else { continue; };
            let OwnerNode::Item(item)=owner.node() else { continue; };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        let program=RustProgram { tcx, functions, structs };
        let slots=CrateSlots::build(&program);
        let origins=compute_origins(&program);
        let facts=MutFacts::from_program(&program);
        let entries=execution_guard::model_entries();
        let ((counts,links),captured)=export::with_bo_export(|| {
            let solver=KindSolver::new(&slots);
            let (_construction,links)=construct_bo_into_a16_refined(&program,&slots,&origins,&facts,&solver).expect("A5A construction");
            // Deliberately no verification, check, raw backend query, model, or cache call.
            let counts=[solver.check_sat_count(),solver.hard_check_count(),solver.optimize_materialization_count(),
                solver.lazy_plain_hard_check_count(),solver.lazy_tracked_recheck_count(),solver.lazy_plain_materialization_count()];
            assert_eq!(counts,[0;6],"zero-solve construction contract");
            (counts,links)
        });
        assert_eq!(execution_guard::model_entries(),entries);
        let evidence:serde_json::Value=serde_json::from_str(&origin_evidence::collect(&program,&slots,&origins,Some(&captured)).canonical_json()).unwrap();
        let mir:Vec<_>=program.functions.iter().map(|&function| {
            let body=tcx.mir_drops_elaborated_and_const_checked(function).borrow();
            let locals:Vec<_>=body.local_decls.iter_enumerated().map(|(local,decl)|serde_json::json!({"local":local.as_u32(),"type":format!("{:?}",decl.ty)})).collect();
            let blocks:Vec<_>=body.basic_blocks.iter_enumerated().map(|(bb,data)|serde_json::json!({"block":bb.as_u32(),"statements":data.statements.iter().map(|s|format!("{:?}",s.kind)).collect::<Vec<_>>(),"terminator":format!("{:?}",data.terminator)})).collect();
            serde_json::json!({"function":tcx.def_path_str(function),"locals":locals,"blocks":blocks,"debug_names":format!("{:?}",body.var_debug_info)})
        }).collect();
        serde_json::json!({"authority":"R237","frame":"fb57f0c2fcfb7bcb39c1664f89773c6acf90f55d plus E recording-only exporter",
            "input_sha256":expected,"query_counters":counts,"model_entries_delta":execution_guard::model_entries()-entries,
            "a16_links":links,"evidence":evidence,"mir":mir,"model":null,"historical_vars_are_identity":false})
    }).unwrap_or_else(|error|error.raise());
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(output)
        .unwrap();
    file.write_all(&serde_json::to_vec_pretty(&payload).unwrap())
        .unwrap();
    file.write_all(b"\n").unwrap();
    file.sync_all().unwrap();
}
