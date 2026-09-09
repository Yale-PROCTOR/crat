//! R236 audit consumer controls. Original sibling facts come from one fixture
//! decision call; terminal-state variations are explicitly constructed inputs.

use std::collections::BTreeSet;

use super::{
    bridge_receipt::{BridgeCalleeId, BridgeSiteKey, SignatureClassId},
    decision::{
        a5_site_proof::A5SiteProofVerdict,
        raw_boundary::{RawBoundaryDisposition, site_atom_id},
        seam::Form,
        sibling_overlap::{self, LocalPostCallEvidence, TerminalSiteState},
    },
    sibling_audit::{self as audit, Input, Outcome},
};

const PARAMETER: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub struct Holder { data: *mut i32 }\n\
    pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
    pub unsafe fn caller(holder: *const Holder, src: *const i32) { update((*holder).data, src); }\n\
    pub unsafe fn entry() { let mut value = 1; let holder = Holder { data: &mut value }; caller(&holder, &value); }\n";

const DEAD_LOCAL: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub struct Holder { data: *mut i32 }\n\
    pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
    pub unsafe fn caller() -> i32 {\n\
        let mut value = 1;\n\
        let holder = Holder { data: &mut value };\n\
        let src: *const i32 = &value;\n\
        update(holder.data, src);\n\
        0\n\
    }\n";

fn inputs(source: &'static str) -> (Vec<Input>, BTreeSet<String>) {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one original fixture decision call");
        let solve = super::model_cache::solve_receipt();
        println!("SIBLING-AUDIT fixture solve={solve:#?}");
        assert!(solve.is_some(), "fixture solve receipt required");
        let t1 = ctx.raw_boundary.inventoried_sites().filter_map(|(key, disposition, _)| {
            matches!(disposition, RawBoundaryDisposition::T1 { .. }).then(|| site_atom_id(key))
        }).collect();
        let inputs = table.sibling_overlap_inventory.coverage.iter().map(|record| {
            let potential = &record.potential;
            let source_file = tcx.sess.source_map().lookup_source_file(potential.argument_span.lo());
            let file = super::file_key(&source_file.name).expect("actual argument file");
            let site = BridgeSiteKey {
                owner_class: SignatureClassId::of(potential.caller), caller: potential.caller,
                callee: potential.callee.as_local().map(BridgeCalleeId::Local)
                    .unwrap_or_else(|| BridgeCalleeId::Foreign(potential.site.callee.path.clone())),
                arm: "sibling-overlap".into(), position: format!("arg{}", potential.site.argument_index),
                file: super::bridge_custody_export::file_label(&file),
                lo: potential.argument_span.lo().0 - source_file.start_pos.0,
                hi: potential.argument_span.hi().0 - source_file.start_pos.0,
                bridge_kind: "sibling-predicate-audit".into(),
            };
            Input {
                site: Ok(site), potential: potential.clone(), source_evidence: record.evidence.clone(),
                // Constructed terminal consumer state, not a delivered-model claim.
                terminal: TerminalSiteState { source_form: Form::Ref { mutable: false }, target_form: Form::Raw, source_delivered: true },
            }
        }).collect();
        (inputs, t1)
    }).expect("original audit fixture compiles")
}

fn source_input(inputs: &[Input]) -> Input {
    let found = inputs
        .iter()
        .filter(|input| input.potential.source.label() == "caller::src")
        .collect::<Vec<_>>();
    assert_eq!(found.len(), 1, "one exact original coverage identity");
    found[0].clone()
}

#[test]
fn sibling_audit_nonpending_dead_local_t1_keeps_predicate_inputs() {
    let (inputs, t1) = inputs(DEAD_LOCAL);
    let input = source_input(&inputs);
    let id = site_atom_id(&input.potential.site);
    assert!(t1.contains(&id), "actual local T1 disposition required");
    assert!(
        matches!(&input.potential.local_post_call, LocalPostCallEvidence::DeadUnprotected { checked_locals }
        if checked_locals.contains(&input.potential.source.declared().expect("declared source control").local))
    );
    assert!(
        sibling_overlap::select_pending(std::slice::from_ref(&input.potential), |_| input.terminal)
            .is_empty()
    );
    assert!(
        input
            .potential
            .siblings
            .iter()
            .all(|sibling| sibling.argument_shape.is_some()),
        "existing call-position shapes are captured"
    );
    let rows = audit::audit(std::slice::from_ref(&input));
    assert_eq!(
        rows.len(),
        1,
        "nonpending local T1 must remain in the audit"
    );
    assert_eq!(rows[0].coverage_id, id);
    assert_eq!(rows[0].outcome, Outcome::DeadUnprotected);
    assert!(rows[0].data);
    assert!(
        matches!(&rows[0].post_call, audit::PostCall::DeadUnprotected { checked_locals }
        if checked_locals.contains(&input.potential.source.mir_local().expect("actual declared MIR local").as_u32()))
    );
    assert_eq!(rows[0].siblings.len(), input.potential.siblings.len());
    assert!(
        rows[0]
            .siblings
            .iter()
            .all(|sibling| sibling.argument_shape.is_some())
    );
}

#[test]
fn sibling_audit_known_undeterminable_is_not_missing_capture() {
    let (inputs, _) = inputs(PARAMETER);
    let mut input = source_input(&inputs);
    // Constructed audit-result contrast. No frozen model or decision is changed.
    for sibling in &mut input.potential.siblings {
        sibling.proof.verdict = A5SiteProofVerdict::Undeterminable;
        sibling.proof.reason = "constructed-completed-undeterminable-audit";
    }
    let rows = audit::audit(std::slice::from_ref(&input));
    assert_eq!(rows.len(), 1);
    assert!(
        rows[0].data,
        "an observed Undeterminable result is complete input data"
    );
    assert_eq!(rows[0].outcome, Outcome::PendingWaiver);
    assert!(
        rows[0]
            .siblings
            .iter()
            .all(|sibling| sibling.proof.outcome == audit::A5Outcome::Undeterminable)
    );
    input.site = Err("constructed-missing-source-location".into());
    let missing = audit::audit(&[input]);
    assert_eq!(missing.len(), 1, "mapping failures are retained");
    assert!(!missing[0].data);
    assert_eq!(missing[0].outcome, Outcome::IncompleteCapture);
    assert!(!missing[0].issues.is_empty());
}

#[test]
fn sibling_audit_every_owned_coverage_identity_occurs_once() {
    let (inputs, _) = inputs(PARAMETER);
    assert!(!inputs.is_empty());
    let expected = inputs
        .iter()
        .map(|input| site_atom_id(&input.potential.site))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        expected.len(),
        inputs.len(),
        "fixture has exact unique coverage IDs"
    );
    let rows = audit::audit(&inputs);
    assert_eq!(rows.len(), inputs.len());
    assert_eq!(
        rows.iter()
            .map(|row| row.coverage_id.clone())
            .collect::<BTreeSet<_>>(),
        expected
    );
}

#[test]
fn sibling_audit_terminal_class_and_atom_reversion_states_are_preserved() {
    let (inputs, _) = inputs(PARAMETER);
    let live = source_input(&inputs);
    let rows = audit::audit(std::slice::from_ref(&live));
    assert_eq!(rows.len(), 1);
    assert!(rows[0].terminal.source_delivered);
    for cause in ["class-reversion", "atom-reversion"] {
        // These are constructed terminal snapshots supplied by Plan, not a
        // test of Plan's already-existing endpoint reversion implementation.
        let mut reverted = live.clone();
        reverted.terminal.source_delivered = false;
        reverted.terminal.source_form = Form::Raw;
        let rows = audit::audit(&[reverted]);
        assert_eq!(rows.len(), 1, "{cause} must preserve its coverage row");
        assert_eq!(rows[0].coverage_id, site_atom_id(&live.potential.site));
        assert_eq!(rows[0].terminal.source_form, "raw");
        assert!(!rows[0].terminal.source_delivered);
        assert_eq!(rows[0].outcome, Outcome::SourceNotDelivered);
    }
}

#[test]
fn sibling_audit_serde_requires_proof_even_when_undeterminable_is_valid() {
    let sibling = audit::Sibling {
        argument_index: 0,
        argument_shape: Some("bare-local".into()),
        proof: audit::A5Audit {
            outcome: audit::A5Outcome::Undeterminable,
            reason: "observed-undeterminable".into(),
            family: "fixture".into(),
            location: None,
            left_site: None,
            right_site: None,
        },
        access: audit::Access::Unknown {
            reason: "observed-unknown-access".into(),
        },
        risky: true,
    };
    let mut value = serde_json::to_value(&sibling).unwrap();
    assert_eq!(
        serde_json::from_value::<audit::Sibling>(value.clone()).unwrap(),
        sibling
    );
    value.as_object_mut().unwrap().remove("proof");
    assert!(
        serde_json::from_value::<audit::Sibling>(value).is_err(),
        "missing capture cannot silently become Undeterminable"
    );
}
