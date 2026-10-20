//! Deliberate-fault checks over an actual native-return transport capture.

use std::collections::BTreeSet;

use super::{
    RawBoundaryArtifacts,
    bridge_receipt::SignatureClassId,
    mechanical_receipt::render_outbound_return_rows,
    outbound_return_transport::{self, Capture},
};

const INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn target(absent: bool, p: *mut i32) -> *mut i32 {
        *p += 1;
        if absent { return core::ptr::null_mut(); }
        p
    }
    pub unsafe fn entry() -> i32 {
        let mut value = 3;
        let _ = target(true, &mut value);
        let _ = target(false, &mut value);
        value
    }
"#;

fn actual_capture() -> (RawBoundaryArtifacts, Capture) {
    let (artifacts, output) = ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let ast = super::ast_transform::capture_ast(tcx).unwrap();
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("one ordinary fixture pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("NATIVE-RETURN-REPLAY solve={solve:#?}");
        assert!(solve.is_some(), "actual fixture solve receipt is mandatory");
        let (p, _) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.label == "target::p")
            .unwrap();
        for local in [p.local, rustc_middle::mir::RETURN_PLACE] {
            let slot = ctx.slots.fn_local_slots[&p.fn_did]
                .slot_for_local_depth(local, 0)
                .unwrap();
            assert_eq!(
                ctx.model.get(&super::SlotRef::Local(p.fn_did, slot)),
                Some(&super::SlotKind::Ref)
            );
        }
        assert!(
            ctx.lifetime_eligibility
                .return_permit((p.fn_did, p.hir_id))
                .is_some()
        );
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        assert!(
            emission.plan.class_finalization.classes[&SignatureClassId::of(p.fn_did)].is_ready()
        );
        let held = emission.plan.held_classes();
        let mut artifacts = RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(
            &mut artifacts,
            &emission.plan,
            &held,
            &BTreeSet::new(),
        );
        let (files, rollbacks, _, _, _) = super::round_files(
            tcx,
            &ast,
            &emission.plan,
            &emission.texts,
            &held,
            &BTreeSet::new(),
            emission.plan.root_file.as_ref(),
            &table,
        )
        .unwrap();
        assert!(rollbacks.is_empty());
        assert_eq!(files.len(), 1);
        (artifacts, files.into_values().next().unwrap())
    })
    .expect("banked valid-stack original fixture compiles");
    assert!(
        super::verify::type_checks_str(&output),
        "actual output type/borrow-checks:\n{output}"
    );
    let capture = outbound_return_transport::capture(&artifacts);
    assert_eq!(
        capture.required.len(),
        2,
        "exact native null/parameter inventory"
    );
    assert!(
        capture
            .required
            .iter()
            .all(|required| required.native_lifetime.is_some())
    );
    replay(&capture).expect("baseline owned native-return JSON replay validates");
    (artifacts, capture)
}

fn replay(capture: &Capture) -> Result<(), String> {
    let bytes = serde_json::to_vec(capture).unwrap();
    let retained: Capture = serde_json::from_slice(&bytes).unwrap();
    outbound_return_transport::validate(&retained)
}

#[test]
fn native_return_replay_catches_coherent_dual_origin_tags() {
    let (_, baseline) = actual_capture();
    let mut changed = baseline.clone();
    for required in changed
        .required
        .iter_mut()
        .chain(changed.rows.iter_mut().map(|row| &mut row.required))
    {
        if required.bridge.kind == "return-raw-to-ref" {
            assert_eq!(required.origins.len(), 1);
            let origin = &mut required.origins[0];
            let (owner, _, _) = origin.local.expect("actual local parameter origin");
            assert!(origin.generated.is_none());
            origin.generated = Some((owner, "deliberate-fault-extra-origin-tag".into(), 0));
        }
    }
    assert_eq!(
        changed.rendered_tsv, baseline.rendered_tsv,
        "the extra DTO tag does not alter canonical TSV keys"
    );
    assert!(
        replay(&changed).is_err(),
        "dual local/generated origin metadata must be caught after JSON replay"
    );
}

#[test]
fn native_return_replay_catches_coherent_empty_source_form() {
    let (artifacts, baseline) = actual_capture();
    let mut changed = baseline.clone();
    let requirement = baseline
        .required
        .iter()
        .find(|required| required.bridge.kind == "return-raw-to-ref")
        .unwrap();
    for row in &mut changed.rows {
        if row.required.key == requirement.key {
            row.source_form.clear();
        }
    }
    for common in &mut changed.common {
        if common.key == requirement.key {
            common.source_form.clear();
        }
    }
    for bridge in &mut changed.bridges {
        if bridge.key == requirement.bridge {
            bridge.source_form.clear();
        }
    }
    let mut native_rows = artifacts.outbound_return_rows.clone();
    for row in &mut native_rows {
        if row.boundary_kind == "return-raw-to-ref" {
            row.source_form.clear();
        }
    }
    changed.rendered_tsv = render_outbound_return_rows(&native_rows);
    assert_ne!(changed.rendered_tsv, baseline.rendered_tsv);
    assert!(
        changed.capture_errors.is_empty(),
        "fault is injected after the genuine capture"
    );
    assert!(
        replay(&changed).is_err(),
        "coherent empty native source form must be caught after JSON replay"
    );
}

#[test]
fn native_return_replay_catches_native_proof_and_null_origin_corruption() {
    let (artifacts, baseline) = actual_capture();
    for fault in ["missing-proof", "wrong-proof-owner", "null-with-origin"] {
        let mut changed = baseline.clone();
        let mut native_rows = artifacts.outbound_return_rows.clone();
        let borrowed = baseline
            .required
            .iter()
            .find(|required| required.bridge.kind == "return-raw-to-ref")
            .unwrap();
        let origin = borrowed.origins[0].clone();
        let native_origin = artifacts
            .outbound_return_rows
            .iter()
            .find(|row| row.boundary_kind == "return-raw-to-ref")
            .unwrap()
            .lifetime_origin[0]
            .clone();
        for required in changed
            .required
            .iter_mut()
            .chain(changed.rows.iter_mut().map(|row| &mut row.required))
        {
            match fault {
                "missing-proof" => required.native_lifetime = None,
                "wrong-proof-owner" => required.native_lifetime.as_mut().unwrap().owner += 1,
                "null-with-origin" if required.bridge.kind == "return-null-to-option" => {
                    required.origins.push(origin.clone())
                }
                "null-with-origin" => {}
                _ => unreachable!(),
            }
        }
        for row in &mut native_rows {
            match fault {
                "missing-proof" => row.native_lifetime = None,
                "wrong-proof-owner" => row.native_lifetime.as_mut().unwrap().owner += 1,
                "null-with-origin" if row.boundary_kind == "return-null-to-option" => {
                    row.lifetime_origin.push(native_origin.clone())
                }
                "null-with-origin" => {}
                _ => unreachable!(),
            }
        }
        changed.rendered_tsv = render_outbound_return_rows(&native_rows);
        assert!(
            replay(&changed).is_err(),
            "native evidence fault must be caught after JSON replay: {fault}"
        );
    }
}
