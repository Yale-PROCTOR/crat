//! R351-6 candidate #4 native RED, deliberately unregistered.
//!
//! The fixture is compiled and analyzed. Its pointer operations are never
//! executed by this witness. Production modules remain unchanged.
#![feature(rustc_private)]
#![feature(array_windows)]
#![feature(box_patterns)]
#![feature(min_specialization)]
#![feature(allocator_api)]
#![feature(step_trait)]
#![feature(trusted_step)]
#![feature(impl_trait_in_assoc_type)]
#![allow(dead_code, unused_imports, unused_extern_crates)]

extern crate either;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_const_eval;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_type_ir;
extern crate smallvec;
extern crate thin_vec;

mod analyses;
mod bo_rewriter;
mod coverage_recon;
mod raw_boundary_census_schema;
mod rewriter;
mod utils;

pub use rewriter::{
    BytemuckDependency, Config, replace_local_borrows, rewrite_array_local_provenance,
    rewrite_epoch_split, rewrite_struct_arrays,
};

const PRELUDE: &str = r#"
#![allow(dead_code, unused_unsafe)]
// SAFETY: these fixture functions are compiled and analyzed only. The witness
// does not call them. Each operation states the source pattern under review.
unsafe fn safe_target(q: *mut i32) -> i32 { *q }
unsafe fn raw_target(q: *mut i32) -> i32 {
    (q > core::ptr::null_mut()) as i32
}
"#;

const MINIMAL: &str = r#"
pub unsafe fn mixed(p: *mut i32) -> i32 {
    let own = *p;
    own + safe_target(p) + raw_target(p)
}
"#;

const RAW_ONLY: &str = r#"
pub unsafe fn raw_only(p: *mut i32) -> i32 {
    let own = *p;
    own + raw_target(p)
}
"#;

const SAFE_ONLY: &str = r#"
pub unsafe fn safe_only(p: *mut i32) -> i32 {
    let own = *p;
    own + safe_target(p)
}
"#;

const SEVEN: &str = r#"
pub unsafe fn DecodeLiteralBlockSwitchInternal(s: *mut i32) -> i32 {
    *s + safe_target(s) + raw_target(s)
}
pub unsafe fn BrotliEncoderCleanupState(m: *mut i32, collateral: *mut i32) -> i32 {
    *collateral + safe_target(m) + raw_target(m)
}
pub unsafe fn kmPlaneFromPoints(p1: *mut i32, p2: *mut i32, p3: *mut i32) -> i32 {
    *p2 + *p3 + safe_target(p1) + raw_target(p1)
}
pub unsafe fn kmQuaternionSlerp(q1: *mut i32, q2: *mut i32) -> i32 {
    safe_target(q1) + raw_target(q1) + safe_target(q2) + raw_target(q2)
}
pub unsafe fn kmVec2DegreesBetween(v1: *mut i32, v2: *mut i32) -> i32 {
    safe_target(v1) + raw_target(v1) + safe_target(v2) + raw_target(v2)
}
pub unsafe fn kmVec2Reflect(p_in: *mut i32, normal: *mut i32, collateral: *mut i32) -> i32 {
    *collateral + safe_target(p_in) + raw_target(p_in) + safe_target(normal) + raw_target(normal)
}
pub unsafe fn kmVec3Reflect(p_in: *mut i32, normal: *mut i32, collateral: *mut i32) -> i32 {
    *collateral + safe_target(p_in) + raw_target(p_in) + safe_target(normal) + raw_target(normal)
}
"#;

fn observe(input: &str) -> serde_json::Value {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = bo_rewriter::ast_transform::capture_ast(tcx).expect("AST capture first");
        let (table, _ctx) = bo_rewriter::decide_table_with_emission_config(
            tcx,
            Some((
                analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(
                    analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )),
            &bo_rewriter::EmissionRunConfig::default(),
        )
        .expect("decision table");
        let emission = bo_rewriter::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &table.c9_marks,
        )
        .expect("class plan");
        let subjects: Vec<_> = table
            .entries
            .iter()
            .map(|(subject, decision)| {
                serde_json::json!({
                    "owner": tcx.def_path_str(subject.fn_did.to_def_id()),
                    "name": subject.param_name,
                    "mir_local": subject.local.as_u32(),
                    "decision": format!("{decision:?}"),
                })
            })
            .collect();
        let classes: Vec<_> = emission
            .plan
            .class_finalization
            .classes
            .iter()
            .map(|(id, class)| {
                serde_json::json!({
                    "owner": tcx.def_path_str(id.local_def_id().to_def_id()),
                    "ready": class.is_ready(),
                    "reasons": class.hold_reasons(),
                    "sites": format!("{:?}", class.sites),
                })
            })
            .collect();
        let edits: Vec<_> = table
            .seams
            .edits
            .iter()
            .map(|edit| {
                serde_json::json!({
                    "owner": tcx.def_path_str(edit.owner_class.local_def_id().to_def_id()),
                    "caller": tcx.def_path_str(edit.bridge.caller.to_def_id()),
                    "argument_index": edit.param_index,
                    "span": bo_rewriter::decision::emitability::EmitabilityFacts::site(tcx, edit.span),
                    "expected": edit.expected.key(),
                    "found": edit.found.key(),
                    "native_arm": edit.bridge.arm,
                })
            })
            .collect();
        let held = emission.plan.held_classes();
        let reverts = bo_rewriter::ast_transform::revert_set_from_classes_and_atoms(
            &held,
            &std::collections::BTreeSet::new(),
            &table,
        )
        .expect("class reverts");
        let (files, _, _, _) = bo_rewriter::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("AST emission");
        let solve = analyses::borrow_ownership::model_cache::solve_receipt().map(|receipt| {
            serde_json::json!({
                "source": receipt.source,
                "cache_status": receipt.cache_status,
                "cache_entry": receipt.cache_entry,
                "model_sha256": receipt.model_sha256,
                "solve_wall_s": receipt.solve_wall_s,
            })
        });
        serde_json::json!({
            "subjects": subjects,
            "classes": classes,
            "edits": edits,
            "zero_bridges": table.seams.zero_bridges.len(),
            "raw_boundary_receipts": table.seams.raw_boundary_receipts,
            "interface_inventory": table.seams.interface_inventory_tsv(tcx),
            "emitted": files.into_values().next().expect("single source"),
            "solve_receipt": solve,
            "configuration": {
                "a5_mode": "precise_replay",
                "attestation": "frozen_benchmark_graph",
                "basis": "complete synthetic fixture call graph",
            },
        })
    })
    .expect("fixture compiles before rewriting")
}

fn is_target(owner: &str, fixture: &str) -> bool {
    match fixture {
        "minimal" => owner == "mixed",
        "raw-only" => owner == "raw_only",
        "safe-only" => owner == "safe_only",
        "seven" => matches!(
            owner,
            "DecodeLiteralBlockSwitchInternal"
                | "BrotliEncoderCleanupState"
                | "kmPlaneFromPoints"
                | "kmQuaternionSlerp"
                | "kmVec2DegreesBetween"
                | "kmVec2Reflect"
                | "kmVec3Reflect"
        ),
        _ => false,
    }
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(
        args.len(),
        3,
        "usage: witness <minimal|seven|raw-only|safe-only> output.json"
    );
    let body = match args[1].as_str() {
        "minimal" => MINIMAL,
        "seven" => SEVEN,
        "raw-only" => RAW_ONLY,
        "safe-only" => SAFE_ONLY,
        other => panic!("unknown fixture {other}"),
    };
    let input = format!("{PRELUDE}{body}");
    let mut observed = observe(&input);
    observed["fixture"] = args[1].clone().into();
    observed["input"] = input.into();
    std::fs::write(&args[2], serde_json::to_string_pretty(&observed).unwrap())
        .expect("write RED evidence before assertion");

    let target_subjects: Vec<_> = observed["subjects"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| is_target(row["owner"].as_str().unwrap(), &args[1]))
        .collect();
    let target_classes: Vec<_> = observed["classes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| is_target(row["owner"].as_str().unwrap(), &args[1]))
        .collect();
    assert!(!target_subjects.is_empty() && !target_classes.is_empty());
    let flow_rows: Vec<_> = target_subjects
        .iter()
        .filter(|row| {
            row["decision"]
                .as_str()
                .unwrap()
                .contains("FlowsIntoRawParam")
        })
        .collect();
    if matches!(args[1].as_str(), "raw-only" | "safe-only") {
        assert!(
            flow_rows.is_empty(),
            "one-owner control must not carry FlowsIntoRawParam: {flow_rows:?}"
        );
        assert!(target_classes.iter().all(|row| row["ready"] == true));
        println!("control GREEN");
        return;
    }

    assert!(
        !flow_rows.is_empty(),
        "authoring premise: mixed calls expose FlowsIntoRawParam"
    );
    assert!(
        observed["raw_boundary_receipts"]
            .as_str()
            .unwrap()
            .contains("\tT1\t"),
        "authoring premise: exact raw site has T1 receipt"
    );
    assert!(
        target_subjects.iter().all(|row| !row["decision"]
            .as_str()
            .unwrap()
            .contains("FlowsIntoRawParam")),
        "W4-W1: safe and raw argument obligations with exact owners must reconcile: {flow_rows:?}"
    );
    assert!(target_classes.iter().all(|row| row["ready"] == true));
    println!("W4-W1 GREEN");
}
