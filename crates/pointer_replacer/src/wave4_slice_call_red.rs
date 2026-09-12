//! Standalone native RED witness for R347-6. Not a Cargo target or production
//! module: the recorded runner links the unchanged crate modules below.
//! No cfg(test) roots are enabled, so existing suites are not duplicated.
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

const SAME_FORM: &str = r#"
unsafe fn read_bit(p: *const u8) -> u8 { *p.offset(1) }
pub unsafe fn same_form_caller(p: *const u8) -> u8 {
    let own = *p.offset(2);
    own ^ read_bit(p)
}
"#;

const READER_CHAIN: &str = r#"
unsafe fn readBitFromReversedStream(bitpointer: *mut usize, bitstream: *const u8) -> u8 {
    *bitpointer = (*bitpointer).wrapping_add(1);
    *bitstream.offset(1)
}
unsafe fn readBitsFromReversedStream(bitpointer: *mut usize, bitstream: *const u8, nbits: usize) -> u8 {
    let mut value = 0;
    let mut i = 0;
    while i < nbits {
        value ^= readBitFromReversedStream(bitpointer, bitstream);
        i += 1;
    }
    value
}
pub unsafe fn getPixelColorRGBA8(r: *mut u8, g: *mut u8, b: *mut u8, a: *mut u8, in_0: *const u8, bitdepth: usize) {
    let mut j = 0;
    let own = *in_0.offset(2);
    let value = readBitsFromReversedStream(&mut j, in_0, bitdepth);
    *r = value;
    *g = own;
    *b = own;
    *a = 255;
}
"#;

fn collect(input: &str) -> serde_json::Value {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        // Match the existing AST helper's capture-before-HIR ordering.
        let capture = bo_rewriter::ast_transform::capture_ast(tcx).expect("AST capture");
        let (table, _ctx) = bo_rewriter::decide_table_with_emission_config(
            tcx,
            Some((
                analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
            &bo_rewriter::EmissionRunConfig::default(),
        )
        .expect("fixture decisions");
        let emission = bo_rewriter::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &table.c9_marks,
        )
        .expect("fixture class plan");
        let span = |span| bo_rewriter::decision::emitability::EmitabilityFacts::site(tcx, span);
        let subjects: Vec<_> = table
            .entries
            .iter()
            .map(|(s, d)| {
                serde_json::json!({
                    "owner": tcx.def_path_str(s.fn_did.to_def_id()),
                    "name": s.param_name, "mir_local": s.local.as_u32(),
                    "decision": format!("{d:?}"),
                })
            })
            .collect();
        let edits: Vec<_> = table
            .seams
            .edits
            .iter()
            .map(|e| {
                serde_json::json!({
                    "callee": tcx.def_path_str(e.owner_class.local_def_id().to_def_id()),
                    "caller": tcx.def_path_str(e.bridge.caller.to_def_id()),
                    "argument_index": e.param_index, "span": span(e.span),
                    "expected": e.expected.key(), "found": e.found.key(),
                })
            })
            .collect();
        let zero: Vec<_> = table
            .seams
            .zero_bridges
            .iter()
            .map(|z| {
                serde_json::json!({
                    "callee": tcx.def_path_str(z.owner_class.local_def_id().to_def_id()),
                    "caller": tcx.def_path_str(z.caller.to_def_id()), "position": z.position,
                    "span": z.span.map(span), "expected": z.expected_form, "found": z.found_form,
                    "kind": z.bridge_kind, "arm": z.arm,
                })
            })
            .collect();
        let receipts: Vec<_> = table
            .slice_use_receipts
            .iter()
            .map(|r| {
                serde_json::json!({
                    "owner": tcx.def_path_str(r.owner_class.local_def_id().to_def_id()),
                    "site": r.use_site.receipt_key(), "source": r.source_form,
                    "candidate": r.candidate_form, "target": r.target_form,
                    "adapter": r.adapter, "boundary_evidence": r.boundary_evidence,
                    "boundary_site": r.boundary_site,
                    "terminal_state": format!("{:?}", r.obligation.intended_terminal_state),
                    "terminal_reason": format!("{:?}", r.obligation.intended_terminal_reason),
                })
            })
            .collect();
        let classes: Vec<_> = emission
            .plan
            .class_finalization
            .classes
            .iter()
            .map(|(id, c)| {
                serde_json::json!({
                    "owner": tcx.def_path_str(id.local_def_id().to_def_id()),
                    "ready": c.is_ready(), "reasons": c.hold_reasons(),
                    "sites": format!("{:?}", c.sites),
                })
            })
            .collect();
        let held = emission.plan.held_classes();
        let reverts = bo_rewriter::ast_transform::revert_set_from_classes_and_atoms(
            &held,
            &std::collections::BTreeSet::new(),
            &table,
        )
        .expect("fixture class reverts");
        let (files, _, _, _) = bo_rewriter::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("fixture AST emission");
        let emitted = files.into_values().next().expect("single emitted source");
        let same_form = bo_rewriter::decision::seam::Form::Slice { mutable: false };
        assert!(matches!(
            bo_rewriter::decision::seam::glue(same_form, same_form, None),
            Ok(None)
        ));
        assert!(matches!(
            bo_rewriter::decision::seam::glue(
                bo_rewriter::decision::seam::Form::Slice { mutable: true },
                same_form,
                None,
            ),
            Err(bo_rewriter::decision::seam::SeamBlock::SharedToMut)
        ));
        let solve = analyses::borrow_ownership::model_cache::solve_receipt().map(|s| {
            serde_json::json!({
                "source": s.source, "cache_status": s.cache_status, "cache_entry": s.cache_entry,
                "model_sha256": s.model_sha256, "solve_wall_s": s.solve_wall_s,
            })
        });
        serde_json::json!({ "subjects": subjects, "edits": edits, "zero_bridges": zero,
            "slice_use_receipts": receipts, "classes": classes,
            "interface_inventory": table.seams.interface_inventory_tsv(tcx),
            "emitted": emitted, "solve_receipt": solve, "same_form_glue": "Ok(None)",
            "shared_to_mut_glue": "Err(SharedToMut)",
            "configuration": { "a5_mode": "precise_replay", "attestation": "frozen_benchmark_graph",
                "basis": "complete synthetic fixture call graph supplied in input" } })
    })
    .expect("fixture compiler session")
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(
        args.len(),
        3,
        "usage: witness <same-form|reader-chain|no-call> <output.json>"
    );
    let input = match args[1].as_str() {
        "same-form" => SAME_FORM.to_owned(),
        "reader-chain" => READER_CHAIN.to_owned(),
        "no-call" => SAME_FORM.replace("own ^ read_bit(p)", "own"),
        other => panic!("unknown fixture {other}"),
    };
    let mut observed = collect(&input);
    observed["fixture"] = args[1].clone().into();
    observed["input"] = input.into();
    std::fs::write(&args[2], serde_json::to_string_pretty(&observed).unwrap())
        .expect("write RED evidence before assertion");
    let missing: Vec<_> = observed["slice_use_receipts"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|r| {
            r["terminal_reason"]
                .as_str()
                .unwrap()
                .contains("slice-use-existing-c-interface-carrier-unmapped")
        })
        .collect();
    assert!(
        missing.is_empty(),
        "W3-W1: an existing zero-syntax C carrier must satisfy its slice use; observed {missing:?}"
    );
    let owner = if args[1] == "reader-chain" {
        "getPixelColorRGBA8"
    } else {
        "same_form_caller"
    };
    let class = observed["classes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|r| r["owner"].as_str().unwrap().ends_with(owner))
        .expect("target class");
    assert_eq!(
        class["ready"], true,
        "W3-W1: target class must finalize ready: {class}"
    );
    println!("W3-W1 GREEN: no missing C carrier and target class ready");
}
