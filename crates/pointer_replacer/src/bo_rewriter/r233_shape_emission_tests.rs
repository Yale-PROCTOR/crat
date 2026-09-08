//! Bounded R233 confirmation using unchanged existing fixture programs.
//! No decision perturbation, eligibility override, or corpus entry is used.

use std::collections::BTreeSet;

use rustc_ast::{
    self as ast,
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use rustc_session::parse::ParseSess;
use rustc_span::edition::Edition;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use super::decision::seam::Form;

struct Case {
    name: &'static str,
    fixture: &'static str,
    input: String,
}

fn cases() -> Vec<Case> {
    // Exact program from sibling_overlap_tests::PARAMETER_CASE.
    let parameter = "#![allow(dead_code, unused_unsafe)]\n\
        pub struct Holder { data: *mut i32 }\n\
        pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
        pub unsafe fn caller(holder: *const Holder, src: *const i32) {\n\
            update((*holder).data, src);\n\
        }\n\
        pub unsafe fn entry() {\n\
            let mut value = 1;\n\
            let holder = Holder { data: &mut value };\n\
            caller(&holder, &value);\n\
        }\n";
    vec![
        Case {
            name: "cast",
            fixture: "seam_terminal_tests::pair_raw_parameter_outbound_case(b as *const i32)",
            input: "#![allow(dead_code, unused_unsafe)]\n\
                static FORMAT: [i8; 3] = [37, 112, 0];\n\
                extern \"C\" { fn printf(format: *const i8, ...) -> i32; }\n\
                pub unsafe fn update(a: *mut i32, b: *mut i32) {\n\
                    *a += 1; *b += 1; printf(FORMAT.as_ptr(), b as *const i32);\n\
                }\n\
                pub unsafe fn caller() { let mut x = 0; update(&mut x, &mut x); }\n".into(),
        },
        Case {
            name: "projected-referent",
            fixture: "sibling_overlap_tests::sibling_r233_coverage_projected_scalar_and_loaded_pointer_stay_distinct",
            input: "#![allow(dead_code, unused_unsafe)]\n\
                pub struct Holder { data: *mut i32, scalar: i32 }\n\
                pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
                pub unsafe fn caller(holder: *const Holder) {\n\
                    update((*holder).data, &(*holder).scalar);\n\
                }\n\
                pub unsafe fn entry() {\n\
                    let mut value = 1; let holder = Holder { data: &mut value, scalar: 2 }; caller(&holder);\n\
                }\n".into(),
        },
        Case {
            name: "pointer-view",
            fixture: "sibling_overlap_tests::sibling_r233_coverage_slice_offset_keeps_its_exact_view_identity",
            // This is the exact replacement already used by that control.
            input: parameter.replace("update((*holder).data, src);",
                "let _value = *src.offset(1); update((*holder).data, src.offset(0));"),
        },
        Case {
            name: "option-slice-local",
            fixture: "emit_tests::slu_w1_assignment_keeps_a_named_raw_alias",
            input: "#![allow(dead_code, unused_unsafe, unused_assignments)]\n\
                pub unsafe fn target(mut p: *const i32) -> isize {\n\
                    let mut base: *const i32 = 0 as *const i32;\n\
                    base = p;\n\
                    while *p != 0 { p = p.offset(1); }\n\
                    p.offset_from(base)\n\
                }\n".into(),
        },
    ]
}

fn solve_receipt() -> Value {
    super::model_cache::solve_receipt().map_or(Value::Null, |receipt| {
        json!({
            "source": receipt.source, "cache_status": receipt.cache_status,
            "fingerprint": receipt.fingerprint, "model_sha256": receipt.model_sha256,
            "cache_entry": receipt.cache_entry, "solve_wall_s": receipt.solve_wall_s,
        })
    })
}

/// Include method calls as syntax observations; the shared bridge inventory
/// deliberately inventories direct call expressions only.
fn method_spellings(source: &str) -> Result<Vec<Value>, String> {
    rustc_span::create_session_globals_then(Edition::Edition2018, &[], None, || {
        let session = ParseSess::new(rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec());
        let krate =
            super::slice_use_inventory_tests::parse_crate(&session, "shape-methods.rs", source)?;
        struct Methods(Vec<Value>);
        impl<'ast> Visitor<'ast> for Methods {
            fn visit_expr(&mut self, expression: &'ast ast::Expr) {
                if let ast::ExprKind::MethodCall(method) = &expression.kind {
                    self.0.push(json!({
                        "method_name": method.seg.ident.name.to_string(),
                        "receiver": pprust::expr_to_string(&method.receiver),
                        "arguments": method.args.iter().map(|argument| pprust::expr_to_string(argument)).collect::<Vec<_>>(),
                        "ast_spelling": pprust::expr_to_string(expression),
                    }));
                }
                visit::walk_expr(self, expression);
            }
        }
        let mut methods = Methods(Vec::new());
        visit::walk_crate(&mut methods, &krate);
        Ok(methods.0)
    })
}

fn confirm(case: &Case) -> Value {
    let input_hash = format!("{:x}", Sha256::digest(case.input.as_bytes()));
    let observed = ::utils::compilation::run_compiler_on_str(&case.input, |tcx| {
        let mut report = json!({ "solve_receipt": null, "terminal_subjects": [], "coverage": [] });
        let emission = (|| -> Result<Vec<(String, String)>, String> {
            let capture = super::ast_transform::capture_ast(tcx)?;
            let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
                crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
            )))?;
            report["solve_receipt"] = solve_receipt();
            let emission = super::emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )?;
            let held = emission.plan.held_classes();
            report["held_classes"] = json!(
                held.iter()
                    .map(|class| format!("{class:?}"))
                    .collect::<Vec<_>>()
            );
            report["class_finalization"] =
                json!(format!("{:#?}", emission.plan.class_finalization));
            report["terminal_subjects"] = json!(table.entries.iter().map(|(subject, choice)| {
                let model = ctx.slots.fn_local_slots.get(&subject.fn_did)
                    .and_then(|slots| slots.slot_for_local_depth(subject.local, 0))
                    .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)));
                json!({ "subject": subject.label, "owner": tcx.def_path_str(subject.fn_did.to_def_id()),
                    "binding": subject.param_name, "kind": format!("{:?}", subject.kind),
                    "model_kind": model.map(|kind| format!("{kind:?}")), "decision": format!("{choice:?}"),
                    "terminal_form": format!("{:?}", super::terminal_subject_form(&table, &emission.plan.class_finalization,
                        (subject.fn_did, subject.hir_id))),
                })
            }).collect::<Vec<_>>());
            report["coverage"] = json!(table.sibling_overlap_inventory.coverage.iter().map(|coverage| {
                let potential = &coverage.potential;
                let source_form = super::terminal_subject_form(&table, &emission.plan.class_finalization,
                    (potential.source.fn_did, potential.source.hir_id));
                let target_form = potential.callee.as_local().map_or(Form::Raw, |callee|
                    super::terminal_parameter_form(&table, &emission.plan.class_finalization,
                        callee, potential.site.argument_index));
                json!({ "site": super::decision::raw_boundary::site_atom_id(&potential.site), "source": potential.source.label,
                    "callee": tcx.def_path_str(potential.callee), "argument_index": potential.site.argument_index,
                    "input_argument": tcx.sess.source_map().span_to_snippet(potential.argument_span).ok(),
                    "source_evidence": format!("{:?}", coverage.evidence),
                    "source_form": format!("{source_form:?}"), "target_form": format!("{target_form:?}"),
                    "post_call_evidence": format!("{:?}", potential.local_post_call),
                    "siblings": format!("{:?}", potential.siblings),
                })
            }).collect::<Vec<_>>());
            let pending = emission.plan.pending_sibling_receipts(&held);
            report["pending_count"] = json!(pending.len());
            report["pending"] = json!(pending.iter().map(|row| json!({
                "site": format!("{:?}", row.site), "source": row.receipt.potential.source.label,
                "callee": tcx.def_path_str(row.receipt.potential.callee),
                "argument_index": row.receipt.potential.site.argument_index,
                "input_argument": tcx.sess.source_map().span_to_snippet(row.receipt.potential.argument_span).ok(),
                "source_form": format!("{:?}", row.receipt.source_form),
                "target_form": format!("{:?}", row.receipt.target_form),
                "tier": row.receipt.tier, "waiver": row.receipt.waiver,
            })).collect::<Vec<_>>());
            report["coverage_gaps"] =
                json!(format!("{:?}", emission.plan.sibling_coverage_gaps(&held)));
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
                &held,
                &BTreeSet::new(),
                &table,
            )?;
            let (files, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx,
                &capture,
                &reverts,
                emission.plan.root_file.as_ref(),
                &table,
                Some(&emission.plan.terminal_call_plans),
            )?;
            Ok(files
                .into_iter()
                .map(|(file, source)| (format!("{file:?}"), source))
                .collect())
        })();
        if report["solve_receipt"].is_null() {
            report["solve_receipt"] = solve_receipt();
        }
        (report, emission)
    });
    let mut report = json!({ "case": case.name, "fixture": case.fixture,
        "input_sha256": input_hash, "input_source": case.input, "data": false });
    let Ok((facts, emission)) = observed else {
        report["error"] = json!("compiler-context-fatal-error");
        return report;
    };
    report["observations"] = facts;
    let files = match emission {
        Ok(files) => files,
        Err(error) => {
            report["error"] = json!(error);
            return report;
        }
    };
    let [(_, output)] = files.as_slice() else {
        report["error"] = json!("fixture-did-not-produce-exactly-one-source-file");
        report["files"] = json!(files);
        return report;
    };
    report["output_source"] = json!(output);
    report["output_sha256"] = json!(format!("{:x}", Sha256::digest(output.as_bytes())));
    let type_checks = super::verify::type_checks_str(output);
    report["output_type_checks"] = json!(type_checks);
    let inspected = (|| -> Result<(), String> {
        report["actual_declarations"] = serde_json::to_value(
            super::delivery_custody::inventory_source(case.name, output)?,
        )
        .map_err(|error| error.to_string())?;
        report["actual_direct_calls"] = serde_json::to_value(
            super::bridge_custody_syntax::inventory_source(case.name, output)?.calls,
        )
        .map_err(|error| error.to_string())?;
        report["actual_method_calls"] = json!(method_spellings(output)?);
        Ok(())
    })();
    if let Err(error) = inspected {
        report["error"] = json!(error);
        return report;
    }
    report["data"] = json!(type_checks && !report["observations"]["solve_receipt"].is_null());
    report
}

#[test]
fn r233_shape_emission_confirmation() {
    let Some(output) = std::env::var_os("CRAT_R233_SHAPE_CONFIRM_OUTPUT") else { return };
    let output = std::path::PathBuf::from(output);
    assert!(
        !output.exists(),
        "do not overwrite a sealed shape confirmation"
    );
    let reports = cases().iter().map(confirm).collect::<Vec<_>>();
    let data = reports.iter().all(|report| report["data"] == true);
    std::fs::write(
        &output,
        serde_json::to_vec_pretty(&json!({ "data": data, "cases": reports })).unwrap(),
    )
    .expect("publish complete shape confirmation");
    assert!(
        data,
        "shape instrument/compile failure recorded at {}",
        output.display()
    );
}
