//! J27 first real producer RED. The input and admission premises come from
//! the banked mutable-slice receiver reversion control, without new evidence.

use std::collections::BTreeSet;

use rustc_middle::mir::RETURN_PLACE;

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
        RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
    },
    decision::{Decision, lifetime::FnSignatureSlot, raw_boundary::RetentionVerdict, seam::Form},
    mechanical_receipt::{
        CanonicalCallee, CanonicalLocation, CanonicalSiteKey, MechanicalFamily,
        MechanicalObligationKey, MechanicalRetention, MechanicalStage, MechanicalState,
        MechanicalSubjectKey, NegativeWriteEvidence,
    },
};

// Exact Family::Slice input from return_receiver_tests.
const INPUT: &str = r#"
                #![allow(dead_code, unused_unsafe)]
                unsafe fn target(p: *mut i32) -> *mut i32 {
                    *p.offset(1) += 1;
                    p
                }
                pub unsafe fn entry() -> i32 {
                    let mut values = [3, 5, 7];
                    let q = target(values.as_mut_ptr());
                    *q.offset(0) += 2;
                    *q.offset(1) + *q.offset(0)
                }
            "#;

#[test]
fn outbound_return_receipt_selected_slice_receiver_has_required_and_specialized_rows() {
    let (baseline, reverted, artifacts, required, origin, adapter, native_digest, raw_bridge) =
        ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
            let capture = super::ast_transform::capture_ast(tcx).expect("one original J27 receiver capture");
            let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
                super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            ))).expect("one actual J27 receiver decision pipeline");
            let solve = super::model_cache::solve_receipt();
            println!("J27 actual receiver solve={solve:#?}");
            assert!(solve.is_some(), "actual fixture solve receipt is mandatory");
            let (q, decision) = table.entries.iter().find(|(subject, _)| subject.label == "entry::q")
                .expect("actual consumed receiver q");
            let (p, _) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
                .expect("actual returned parameter p");
            assert!(matches!(decision, Decision::Slice { mutable: true, .. }));
            for (owner, local) in [(q.fn_did, q.local), (p.fn_did, p.local), (p.fn_did, RETURN_PLACE)] {
                let kind = ctx.slots.fn_local_slots.get(&owner)
                    .and_then(|slots| slots.slot_for_local_depth(local, 0))
                    .and_then(|slot| ctx.model.get(&super::SlotRef::Local(owner, slot)));
                assert_eq!(kind, Some(&super::SlotKind::Ref), "actual native receiver/source/return model premise");
            }
            assert!(ctx.lifetime_eligibility.return_permit((p.fn_did, p.hir_id)).is_some(),
                "the native parameter return permit is an independent premise");
            let lifetime = table.lifetime_plan.function(p.fn_did).expect("actual native lifetime plan");
            assert_eq!(lifetime.lifetime_for(FnSignatureSlot::arg(1, 0, 0)),
                lifetime.lifetime_for(FnSignatureSlot::RETURN));
            assert!(lifetime.lifetime_for(FnSignatureSlot::RETURN).is_some());
            let flow = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
                .and_then(|flows| flows.get(&p.fn_did)).expect("actual native origin flow");
            use crate::analyses::borrow_ownership::slots::SlotOwner;
            assert!(flow.body.depth0_value_flows().contains(&(
                SlotOwner::Local(p.local), SlotOwner::Local(RETURN_PLACE))));
            let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
                .expect("actual receiver emission plan");
            let caller = SignatureClassId::of(q.fn_did);
            let callee = SignatureClassId::of(p.fn_did);
            assert_ne!(caller, callee);
            let held = emission.plan.held_classes();
            for owner in [caller, callee] {
                assert!(emission.plan.class_finalization.classes.get(&owner)
                    .is_some_and(super::plan::SignatureClassPlan::is_ready));
                assert!(!held.contains(&owner));
            }
            let node = (q.fn_did, q.hir_id);
            let input = emission.plan.terminal_call_plans.receiver_inputs.plans.get(&node)
                .expect("actual successful receiver-input plan");
            assert_eq!(input.destination, q.local);
            assert_eq!(input.receiver.callee, p.fn_did);
            assert_eq!(input.receiver.candidate_interface, table.return_interfaces.functions[&p.fn_did]);
            assert_eq!(input.receiver.candidate_interface.form, Form::Slice { mutable: true });
            assert_eq!(input.tier, BridgeRetentionTier::T2);
            assert_eq!(input.waiver_id, RAW_BOUNDARY_T2_WAIVER_ID);
            assert!(matches!(input.retention, RetentionVerdict::Unknown { .. }),
                "native return admission is not a caller alias-schedule certificate");
            let render = |classes: &BTreeSet<SignatureClassId>| {
                let (files, rollbacks, _, _) = super::round_files(tcx, &capture, &emission.plan,
                    &emission.texts, classes, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table)
                    .expect("actual J27 receiver round");
                assert!(rollbacks.is_empty());
                assert_eq!(files.len(), 1);
                files.into_values().next().unwrap()
            };
            let baseline = render(&held);
            let mut selected = held.clone();
            selected.insert(caller);
            let normalized = emission.plan.effective_reverted_classes(&selected, &BTreeSet::new());
            assert!(input.active(&normalized, &BTreeSet::new()));
            assert!(!normalized.contains(&callee), "the native returned interface survives caller reversion");
            let reverted = render(&selected);
            let (baseline_required, baseline_common, baseline_rows) = emission.plan
                .outbound_return_receipts(&held, &BTreeSet::new()).expect("inactive receiver inventory");
            assert_eq!(baseline_required.len(), 1, "native parameter return remains active without a raw receiver");
            assert_eq!(baseline_common.len(), 2);
            assert_eq!(baseline_rows.len(), 2);
            assert_eq!(baseline_required[0].associated_bridge.bridge_kind, "return-raw-to-ref");
            assert_eq!(baseline_required[0].associated_bridge.owner_class, callee);
            assert_eq!(baseline_required[0].associated_bridge.caller, p.fn_did);
            assert_eq!(baseline_required[0].lifetime_origin, vec![MechanicalSubjectKey::Local {
                owner: p.fn_did, mir_local: p.local.as_u32(), slot_depth: 0,
            }]);
            assert!(baseline_required[0].native_lifetime.is_some());
            let mut both = selected.clone(); both.insert(callee);
            let (removed_required, removed_common, removed_rows) = emission.plan
                .outbound_return_receipts(&both, &BTreeSet::new()).expect("retired callee receiver inventory");
            assert!(removed_required.is_empty() && removed_common.is_empty() && removed_rows.is_empty());
            let mut fault = emission.plan.clone();
            fault.outbound_return_plans = Default::default();
            let caught = fault.outbound_return_receipts(&selected, &BTreeSet::new())
                .expect_err("deliberate-fault: dropping the whole J27 producer cannot erase active requirements");
            assert!(caught.contains("required-metadata-missing"), "{caught}");
            println!("deliberate-fault check caught by active J27 plan custody: {caught}");
            let source_file = tcx.sess.source_map().lookup_source_file(input.receiver.initializer_span.lo());
            let original_files = std::collections::BTreeMap::from([
                (super::file_key(&source_file.name).unwrap(), INPUT.to_owned())]);
            let mut artifacts = super::RawBoundaryArtifacts {
                bridge_custody_export: super::bridge_custody_export::capture(
                    tcx, &capture, &table, &emission.plan, &original_files),
                ..Default::default()
            };
            super::refresh_raw_boundary_receipt_events(&mut artifacts, &emission.plan, &selected, &BTreeSet::new());
            let source = tcx.sess.source_map().lookup_source_file(input.receiver.initializer_span.lo());
            let file = super::bridge_custody_export::file_label(&super::file_key(&source.name).unwrap());
            let lo = input.receiver.initializer_span.lo().0 - source.start_pos.0;
            let hi = input.receiver.initializer_span.hi().0 - source.start_pos.0;
            let raw = artifacts.bridge_events.iter().filter(|event|
                event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Applied
                    && event.site.owner_class == callee && event.site.caller == q.fn_did
                    && event.site.callee == BridgeCalleeId::Local(p.fn_did)
                    && event.site.bridge_kind == "return-caller-receive-raw"
                    && event.site.file == file && event.site.lo == lo && event.site.hi == hi)
                .collect::<Vec<_>>();
            let [raw] = raw.as_slice() else { panic!("one exact actual Applied raw receiver bridge: {:#?}", artifacts.bridge_events) };
            assert_eq!(raw.expected_form, "raw");
            assert_eq!(raw.found_form, "slice-mut");
            assert_eq!(raw.retention, BridgeRetentionTier::T2);
            assert_eq!(raw.waiver_id.as_deref(), Some(RAW_BOUNDARY_T2_WAIVER_ID));
            let native_digest = input.receiver.candidate_interface.lifetime_plan_digest.clone();
            assert!(raw.site.position.contains(&native_digest));
            let required = MechanicalObligationKey {
                owner_class: callee,
                subject: MechanicalSubjectKey::Local { owner: q.fn_did, mir_local: input.destination.as_u32(), slot_depth: 0 },
                site: CanonicalSiteKey { owner: q.fn_did,
                    location: CanonicalLocation::Hir { owner: input.receiver.initializer_hir.owner.def_id,
                        item_local_id: input.receiver.initializer_hir.local_id.as_u32() },
                    callee: Some(CanonicalCallee::Local(p.fn_did.to_def_id())), argument_index: None, slot_depth: 0 },
                family: MechanicalFamily::ReturnNotAdapted,
            };
            let origin = MechanicalSubjectKey::Local { owner: p.fn_did, mir_local: p.local.as_u32(), slot_depth: 0 };
            let raw_bridge = (**raw).clone();
            let adapter = input.template.key().to_owned();
            println!("J27 real premise complete: required={required:?}; origin={origin:?}; input={input:#?}; raw_bridge={raw_bridge:#?}\nBASELINE:\n{baseline}\nREVERTED:\n{reverted}");
            (baseline, reverted, artifacts, required, origin, adapter, native_digest, raw_bridge)
        }).expect("unchanged banked receiver input compiles");
    assert!(
        super::verify::type_checks_str(&baseline),
        "banked baseline type/borrow-checks:\n{baseline}"
    );
    assert!(
        super::verify::type_checks_str(&reverted),
        "banked caller-reverted output type/borrow-checks:\n{reverted}"
    );

    // First J27 producer RED begins only after all real admission, selection,
    // common-bridge and emitted-tree premises above have succeeded.
    assert_eq!(
        artifacts
            .outbound_return_required
            .iter()
            .filter(|requirement| requirement.key == required)
            .count(),
        1,
        "J27 must independently inventory this exact required receiver obligation"
    );
    let rows = artifacts
        .outbound_return_rows
        .iter()
        .filter(|row| row.terminal.obligation_key == required)
        .collect::<Vec<_>>();
    assert_eq!(
        rows.len(),
        2,
        "J27 requires exactly one specialized Plan and Terminal row"
    );
    assert_eq!(
        rows.iter()
            .filter(|row| row.terminal.stage == MechanicalStage::Plan)
            .count(),
        1
    );
    assert_eq!(
        rows.iter()
            .filter(|row| row.terminal.stage == MechanicalStage::Terminal)
            .count(),
        1
    );
    for row in rows {
        assert_eq!(
            row.terminal.state,
            if row.terminal.stage == MechanicalStage::Plan {
                MechanicalState::Planned
            } else {
                MechanicalState::Applied
            }
        );
        assert!(row.terminal.reason.is_none());
        assert_eq!(row.endpoint, required.site.callee.clone().unwrap());
        assert_eq!(row.boundary_kind, raw_bridge.site.bridge_kind);
        assert_eq!(row.position, raw_bridge.site.position);
        assert_eq!(row.source_form, raw_bridge.found_form);
        assert_eq!(row.target_form, raw_bridge.expected_form);
        assert_eq!(row.adapter, adapter);
        assert_eq!(
            row.retention,
            MechanicalRetention::T2 {
                waiver_id: RAW_BOUNDARY_T2_WAIVER_ID.into()
            }
        );
        assert_eq!(row.negative_write, NegativeWriteEvidence::NotApplicable);
        assert_eq!(row.lifetime_origin, vec![origin.clone()]);
        assert_eq!(row.pair_role, "not-applicable");
        assert!(row.effect_carrier.is_none());
        assert_eq!(row.terminal_interface, "slice-mut");
        assert!(row.position.contains(&native_digest));
    }
    check_receipt_faults(&artifacts, &required);
    let packet = super::outbound_return_transport::capture(&artifacts);
    super::outbound_return_transport::validate(&packet).expect("typed J27 DTO validation");
    let retained = artifacts
        .bridge_custody_export
        .outbound_return
        .as_ref()
        .expect("J27 capture must travel through the actual retained export");
    assert_eq!(retained, &packet);
    check_transport_sidecars(&packet);
    let mut coherent = packet.clone();
    let move_local = |key: &mut super::outbound_return_transport::Key| {
        let (owner, local, depth) = key.subject.local.unwrap();
        key.subject.local = Some((owner, local + 1, depth));
    };
    for requirement in &mut coherent.required {
        move_local(&mut requirement.key);
    }
    for row in &mut coherent.rows {
        move_local(&mut row.required.key);
    }
    for common in &mut coherent.common {
        move_local(&mut common.key);
    }
    assert!(
        super::outbound_return_transport::validate(&coherent).is_err(),
        "deliberate-fault: coherent local metadata changes must not retain an old canonical identity"
    );
    check_retained_transport(&artifacts, &reverted);
}

fn check_receipt_faults(artifacts: &super::RawBoundaryArtifacts, key: &MechanicalObligationKey) {
    use super::mechanical_receipt::{reconcile_outbound_return_rows, render_outbound_return_rows};
    let check = |state: &super::RawBoundaryArtifacts| {
        reconcile_outbound_return_rows(
            &state.outbound_return_required,
            &state.outbound_return_rows,
            &state.mechanical_events,
            &state.bridge_events,
        )
    };
    assert!(
        artifacts.outbound_return_error.is_none(),
        "{:?}",
        artifacts.outbound_return_error
    );
    assert_eq!(
        check(artifacts),
        Ok(2),
        "native return plus selected raw receiver"
    );
    let mut cases = Vec::new();
    let mut state = artifacts.clone();
    state
        .outbound_return_rows
        .retain(|row| row.terminal.stage != MechanicalStage::Terminal);
    cases.push(("missing-specialized-terminal", state));
    let mut state = artifacts.clone();
    let row = state
        .outbound_return_rows
        .iter()
        .find(|row| row.terminal.stage == MechanicalStage::Terminal)
        .unwrap()
        .clone();
    state.outbound_return_rows.push(row);
    cases.push(("duplicate-specialized-terminal", state));
    let mut state = artifacts.clone();
    state
        .mechanical_events
        .retain(|row| row.key != *key || row.stage != MechanicalStage::Terminal);
    cases.push(("missing-common-terminal", state));
    let mut state = artifacts.clone();
    state.outbound_return_rows.clear();
    state.mechanical_events.retain(|row| row.key != *key);
    cases.push(("both-output-families-missing", state));
    let mut state = artifacts.clone();
    state.outbound_return_required.clear();
    state.outbound_return_rows.clear();
    state.mechanical_events.retain(|row| row.key != *key);
    cases.push(("all-j27-inventories-erased-with-bridge-kept", state));
    let mut state = artifacts.clone();
    for row in &mut state.outbound_return_rows {
        row.lifetime_origin.clear();
    }
    cases.push(("both-origin-vectors-corrupted", state));
    let mut state = artifacts.clone();
    for row in &mut state.outbound_return_rows {
        row.retention_evidence = None;
    }
    cases.push(("both-retention-payloads-corrupted", state));
    let mut state = artifacts.clone();
    let bridge = state.outbound_return_required[0].associated_bridge.clone();
    state
        .bridge_events
        .retain(|row| row.site != bridge || row.stage != BridgeReceiptStage::Terminal);
    cases.push(("missing-associated-bridge-terminal", state));
    for (name, state) in cases {
        let reason = check(&state).expect_err(name);
        println!("deliberate-fault check {name} caught by J27 reconciliation: {reason}");
    }
    let rendered = render_outbound_return_rows(&artifacts.outbound_return_rows);
    let lines = rendered.lines().collect::<Vec<_>>();
    assert_eq!(
        lines.len(),
        5,
        "header plus Plan/Terminal for native return and raw receiver"
    );
    assert_eq!(lines[0].split('\t').count(), 18);
    assert!(
        lines.iter().all(|line| line.split('\t').count() == 18),
        "{rendered}"
    );
    assert!(rendered.contains(RAW_BOUNDARY_T2_WAIVER_ID));
}

fn check_retained_transport(artifacts: &super::RawBoundaryArtifacts, source: &str) {
    use super::{CensusOutcomeKind, bridge_custody_export as custody};
    let sources = artifacts
        .bridge_custody_export
        .files
        .keys()
        .map(|file| (file.clone(), source.to_owned()))
        .collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(sources.len(), 1, "one actual captured source file");
    let compare = |export: &custody::Export| {
        custody::compare_capture(
            export,
            &artifacts.bridge_events,
            Some(&sources),
            CensusOutcomeKind::Emitted,
        )
    };
    let original = compare(&artifacts.bridge_custody_export);
    assert!(original.data, "{original:#?}");
    let frame = custody::ReplayFrame {
        program: "fixture:j27-receiver".into(),
        analysis_frame: "fixture:ordinary-harness".into(),
        code_frame: "fixture:j27-replay".into(),
        input_tree_sha256: "fixture-input".into(),
        emitted_tree_sha256: "fixture-output".into(),
        cache_manifest_sha256: "fixture:cache-disabled".into(),
        launch_env_sha256: "fixture:pinned-test-env".into(),
    };
    let replay = custody::RetainedReplay {
        frame: frame.clone(),
        export: artifacts.bridge_custody_export.clone(),
        applied: custody::applied_receipts(&artifacts.bridge_events),
        emitted_sources: Some(sources),
        emitted_outcome: true,
        comparison: original.clone(),
    };
    let encoded = serde_json::to_string(&replay).expect("owned replay serialization");
    let replay: custody::RetainedReplay =
        serde_json::from_str(&encoded).expect("owned replay roundtrip");
    assert_eq!(
        custody::compare_retained(Some(&replay), &frame).unwrap(),
        original
    );
    let mut changes = Vec::new();
    let mut changed = replay.clone();
    changed.export.outbound_return = None;
    changes.push(("absent-capture", changed));
    let mut changed = replay.clone();
    changed.export.outbound_return = Some(super::outbound_return_transport::capture(
        &super::RawBoundaryArtifacts::default(),
    ));
    changes.push(("entire-capture-substituted-with-empty", changed));
    let mut changed = replay.clone();
    changed.export.outbound_return.as_mut().unwrap().rows.pop();
    changes.push(("missing-row", changed));
    let mut changed = replay.clone();
    for row in &mut changed.export.outbound_return.as_mut().unwrap().rows {
        row.required.origins.clear();
    }
    changes.push(("both-origins-changed", changed));
    let mut changed = replay.clone();
    for row in &mut changed.export.outbound_return.as_mut().unwrap().rows {
        row.required.retention = None;
    }
    changes.push(("both-retention-payloads-changed", changed));
    let mut changed = replay.clone();
    let packet = changed.export.outbound_return.as_mut().unwrap();
    packet.required.clear();
    packet.rows.clear();
    packet.common.clear();
    changes.push(("all-j27-collections-erased-with-bridges-kept", changed));
    let mut changed = replay.clone();
    changed
        .export
        .outbound_return
        .as_mut()
        .unwrap()
        .rendered_tsv
        .push_str("extra-row\n");
    changes.push(("serialized-tsv-drift", changed));
    for (name, changed) in changes {
        assert_eq!(
            changed.comparison, replay.comparison,
            "saved success is preserved in the deliberate fault"
        );
        let result = custody::compare_retained(Some(&changed), &frame);
        match result {
            Ok(report) => assert!(
                !report.data
                    && report
                        .issues
                        .iter()
                        .any(|issue| issue.contains("outbound-return")),
                "{name}: {report:#?}"
            ),
            Err(reason) => assert!(reason.contains("outbound-return"), "{name}: {reason}"),
        }
        println!("deliberate-fault check {name} caught by retained J27 transport");
    }
}

fn check_transport_sidecars(packet: &super::outbound_return_transport::Capture) {
    use super::outbound_return_transport::validate_sidecars;
    let frame = std::collections::BTreeMap::from([
        ("program".into(), "fixture:j27".into()),
        ("corpus".into(), "rs-crown".into()),
        ("analysis_frame".into(), "fixture:analysis".into()),
        ("code_frame".into(), "fixture:code".into()),
        (
            "cache_manifest_sha256".into(),
            "fixture:cache-disabled".into(),
        ),
        ("launch_env_sha256".into(), "fixture:launch".into()),
    ]);
    let mut lines = packet.rendered_tsv.lines();
    let header = lines.next().unwrap();
    let prefix_header = frame
        .keys()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join("\t");
    let prefix = frame
        .values()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .join("\t");
    let mut stamped = format!("{prefix_header}\tdata\t{header}\n");
    for line in lines {
        stamped.push_str(&format!("{prefix}\tprovisional\t{line}\n"));
    }
    assert!(validate_sidecars(Some(packet), Some(packet), Some(&stamped), &frame, &[]).is_ok());
    let mut bad_packet = packet.clone();
    bad_packet.rows.clear();
    let mut wrong_frame = frame.clone();
    wrong_frame.insert("code_frame".into(), "wrong".into());
    for (name, result) in [
        (
            "missing-json",
            validate_sidecars(Some(packet), None, Some(&stamped), &frame, &[]),
        ),
        (
            "missing-tsv",
            validate_sidecars(Some(packet), Some(packet), None, &frame, &[]),
        ),
        (
            "json-mismatch",
            validate_sidecars(Some(packet), Some(&bad_packet), Some(&stamped), &frame, &[]),
        ),
        (
            "tsv-mismatch",
            validate_sidecars(Some(packet), Some(packet), Some("wrong\n"), &frame, &[]),
        ),
        (
            "tsv-frame-mismatch",
            validate_sidecars(
                Some(packet),
                Some(packet),
                Some(&stamped),
                &wrong_frame,
                &[],
            ),
        ),
    ] {
        let reason = result.expect_err(name);
        assert!(reason.contains("outbound-return"), "{reason}");
        println!("deliberate-fault check {name} caught by J27 sidecar validation: {reason}");
    }
}
