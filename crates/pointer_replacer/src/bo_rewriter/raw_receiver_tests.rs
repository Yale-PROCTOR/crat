//! Actual borrowed callee result consumed by an unadmitted raw receiver.
//! This memory-safety pattern fixture is compiled and inspected, never run.

use std::collections::BTreeSet;

use rustc_hir::{ExprKind, QPath, def::Res};
use rustc_middle::mir::RETURN_PLACE;

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
        RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
    },
    decision::{
        Decision, SubjectKind,
        construction::{CallResultTarget, Construction},
        lifetime::FnSignatureSlot,
        raw_boundary::RetentionVerdict,
        seam::Form,
    },
    mechanical_receipt::MechanicalStage,
};

const INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn target(p: *mut i32) -> *mut i32 {
        if !p.is_null() { *p += 1; }
        p
    }
    pub unsafe fn entry() -> usize {
        let mut value = 3;
        let q = target(&mut value);
        let _address = q as usize;
        0
    }
"#;

#[test]
fn raw_receiver_keeps_the_borrowed_callee_and_views_its_result_once() {
    assert!(
        super::verify::type_checks_str(INPUT),
        "unchanged valid-stack input type/borrow-checks"
    );
    let (emitted, retired) = ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original raw-receiver AST capture");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one ordinary tiny-fixture decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("RAW-RECEIVER solve={solve:#?}\nINPUT:\n{INPUT}");
        assert!(solve.is_some(), "actual fixture solve receipt is mandatory");
        let (parameter, parameter_decision) = table.entries.iter()
            .find(|(subject, _)| subject.label == "target::p").expect("actual target parameter p");
        let (receiver, receiver_decision) = table.entries.iter()
            .find(|(subject, _)| subject.label == "entry::q").expect("actual named receiver q");
        let node = (receiver.fn_did, receiver.hir_id);
        let model_kind = |owner, local| ctx.slots.fn_local_slots.get(&owner)
            .and_then(|slots| slots.slot_for_local_depth(local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(owner, slot)));
        let parameter_kind = model_kind(parameter.fn_did, parameter.local);
        let return_kind = model_kind(parameter.fn_did, RETURN_PLACE);
        let receiver_kind = model_kind(receiver.fn_did, receiver.local);
        let permit = ctx.lifetime_eligibility.return_permit((parameter.fn_did, parameter.hir_id));
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual raw-receiver emission plan");
        let caller = SignatureClassId::of(receiver.fn_did);
        let callee = SignatureClassId::of(parameter.fn_did);
        println!("RAW-RECEIVER actual model: p={parameter_kind:?}; return={return_kind:?}; q={receiver_kind:?}; p_decision={parameter_decision:#?}; q_candidate={:?}; q_final={receiver_decision:#?}; native_permit={permit:?}; potential_interface={:?}; final_interface={:?}; receiver_plan={:?}; receiver_failure={:?}; caller_hold={:?}; callee_hold={:?}",
            ctx.hypothetical.entries.iter().find(|(subject, _)| (subject.fn_did, subject.hir_id) == node).map(|(_, decision)| decision),
            ctx.hypothetical.return_interfaces.functions.get(&parameter.fn_did),
            table.return_interfaces.functions.get(&parameter.fn_did),
            table.return_receivers.plans.get(&node), table.return_receivers.failures.get(&node),
            emission.plan.class_hold_reason(caller), emission.plan.class_hold_reason(callee));
        println!("RAW-RECEIVER additive receipts={:#?}; callee class={:#?}",
            ctx.raw_boundary_artifacts.additive_family_receipts,
            emission.plan.class_finalization.classes.get(&callee));
        println!("RAW-RECEIVER raw plan={:#?}; unavailable={:#?}",
            table.seams.raw_receivers.plans.get(&node), table.seams.raw_receivers.unavailable.get(&node));
        assert_eq!(receiver.kind, SubjectKind::Local);
        assert!(receiver.ty_span.is_none(), "original q has no forced raw annotation");
        assert_eq!(ctx.constructions.by_binding.get(&node), Some(&Construction::CallResult));
        assert_eq!(ctx.constructions.call_result_targets.get(&node),
            Some(&CallResultTarget::DirectLocal(parameter.fn_did)));
        let initializer_hir = ctx.constructions.init_hirs[&node];
        let initializer = tcx.hir_node(initializer_hir).expect_expr();
        let ExprKind::Call(callee_expression, _) = initializer.kind else {
            panic!("actual receiver initializer is a direct call");
        };
        assert!(matches!(callee_expression.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Def(_, did) if did == parameter.fn_did.to_def_id())));
        assert_eq!(ctx.constructions.init_spans.get(&node), Some(&initializer.span));
        println!("RAW-RECEIVER exact initializer: hir={initializer_hir:?}; span={:?}; text={:?}",
            initializer.span, tcx.sess.source_map().span_to_snippet(initializer.span));
        let origins = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&parameter.fn_did)).expect("actual native callee origin export");
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        let origin_present = origins.body.depth0_value_flows().contains(&(
            SlotOwner::Local(parameter.local), SlotOwner::Local(RETURN_PLACE)));
        println!("RAW-RECEIVER native parameter-to-return origin={origin_present}");

        // These are actual authoring premises, not invented analysis facts.
        // q's model kind is observed above; Ref is allowed when surface use
        // causes its independent typed refusal.
        assert_eq!(parameter_kind, Some(&super::SlotKind::Ref), "authoring premise: native callee parameter Ref");
        assert_eq!(return_kind, Some(&super::SlotKind::Ref), "authoring premise: native callee return Ref");
        assert!(origin_present, "authoring premise: actual parameter-tied return origin");
        assert!(matches!(receiver_decision, Decision::Degraded(_)),
            "authoring premise: q has an observed raw surface disposition, regardless of model kind");

        // Production requirements start after the observed model, origin,
        // direct initializer and receiver-refusal premises above.
        let interface = table.return_interfaces.functions.get(&parameter.fn_did)
            .expect("the raw receiver must retain the callee's native borrowed return interface");
        assert_eq!(interface.form, Form::Opt { mutable: true, slice: false });
        assert!(permit.is_some(), "retained borrowed interface requires its native return permit");
        let lifetime = table.lifetime_plan.function(parameter.fn_did).expect("actual native callee lifetime plan");
        assert_eq!(lifetime.lifetime_for(FnSignatureSlot::RETURN), Some(interface.lifetime.as_str()));
        assert_eq!(interface.lifetime_plan_digest, lifetime.digest());
        assert!(emission.plan.class_finalization.classes.get(&callee)
            .is_some_and(super::plan::SignatureClassPlan::is_ready),
            "an adaptable raw result destination must leave the changed callee Ready");
        let held = emission.plan.held_classes();
        let mut artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(&mut artifacts, &emission.plan, &held, &BTreeSet::new());
        let source = tcx.sess.source_map().lookup_source_file(initializer.span.lo());
        let file = super::bridge_custody_export::file_label(&super::file_key(&source.name).unwrap());
        let lo = initializer.span.lo().0 - source.start_pos.0;
        let hi = initializer.span.hi().0 - source.start_pos.0;
        let bridges = artifacts.bridge_events.iter().filter(|event|
            event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Applied
                && event.site.owner_class == callee && event.site.caller == receiver.fn_did
                && event.site.callee == BridgeCalleeId::Local(parameter.fn_did)
                && event.site.bridge_kind == "return-caller-receive-raw"
                && event.site.file == file && event.site.lo == lo && event.site.hi == hi)
            .collect::<Vec<_>>();
        let [bridge] = bridges.as_slice() else { panic!("one exact raw-result bridge at the native initializer: {bridges:#?}") };
        assert_eq!(bridge.found_form, interface.form.key());
        assert_eq!(bridge.expected_form, "raw");
        assert_eq!(bridge.retention, BridgeRetentionTier::T2);
        assert_eq!(bridge.waiver_id.as_deref(), Some(RAW_BOUNDARY_T2_WAIVER_ID));
        let rows = artifacts.outbound_return_rows.iter().filter(|row|
            row.terminal.stage == MechanicalStage::Terminal && row.associated_bridge == bridge.site)
            .collect::<Vec<_>>();
        let [row] = rows.as_slice() else { panic!("exact raw receiver bridge has one terminal J27 row") };
        assert!(matches!(row.retention_evidence, Some(RetentionVerdict::Unknown { .. })),
            "T2 is backed by the owned actual retention verdict");
        assert!(artifacts.outbound_return_error.is_none());
        let mut retired_classes = held.clone(); retired_classes.insert(callee);
        let mut retired_artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(&mut retired_artifacts, &emission.plan,
            &retired_classes, &BTreeSet::new());
        assert!(retired_artifacts.outbound_return_required.is_empty());
        assert!(retired_artifacts.outbound_return_rows.is_empty());
        let retired_bridge = retired_artifacts.bridge_events.iter().find(|event|
            event.site == bridge.site && event.stage == BridgeReceiptStage::Terminal).unwrap();
        assert_eq!(retired_bridge.state, BridgeReceiptState::Dropped);
        super::outbound_return_transport::validate(&super::outbound_return_transport::capture(&retired_artifacts))
            .expect("retired raw result has no applied J27 view, while its dropped common receipt remains history");
        let (retired_files, retired_rollbacks, _, _) = super::round_files(tcx, &capture, &emission.plan,
            &emission.texts, &retired_classes, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table).unwrap();
        assert!(retired_rollbacks.is_empty());
        let retired = retired_files.into_values().next().unwrap();
        let (files, rollbacks, _, _) = super::round_files(tcx, &capture, &emission.plan,
            &emission.texts, &held, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table)
            .expect("actual raw-receiver emission round");
        assert!(rollbacks.is_empty());
        assert_eq!(files.len(), 1);
        (files.into_values().next().unwrap(), retired)
    }).expect("original memory-safety pattern fixture compiles");
    assert!(
        super::verify::type_checks_str(&retired),
        "retired callee restores the original raw result:\n{retired}"
    );
    assert!(!retired.contains("__crat_receiver_input_"));
    assert!(
        super::verify::type_checks_str(&emitted),
        "raw receiver output type/borrow-checks:\n{emitted}"
    );
    let syntax = super::bridge_custody_syntax::inventory_source("raw-receiver.rs", &emitted)
        .expect("pinned parser sees the emitted receiver initializer");
    let bindings = syntax
        .bindings
        .iter()
        .filter(|binding| binding.owner == "entry" && binding.name == "q")
        .collect::<Vec<_>>();
    let [binding] = bindings.as_slice() else { panic!("one emitted q binding") };
    let initializer = binding.init_span.expect("q retains one initializer");
    let calls = syntax
        .calls
        .iter()
        .filter(|call| {
            call.owner == "entry"
                && call.span.lo >= initializer.lo
                && call.span.hi <= initializer.hi
                && call.callee_path.as_deref() == Some("target")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        calls.len(),
        1,
        "the borrowed target result is evaluated exactly once"
    );
    let initializer_text = &emitted[initializer.lo as usize..initializer.hi as usize];
    assert!(
        initializer_text.contains("map_or") && initializer_text.contains("from_mut"),
        "the Option result has an actual null-mapped raw view:\n{initializer_text}"
    );
    assert!(
        emitted
            .split_whitespace()
            .collect::<String>()
            .contains("qasusize"),
        "q's original raw address observation survives"
    );
}

#[test]
fn raw_receiver_returned_address_keeps_the_positive_retention_hold() {
    let source = INPUT.replace("let _address = q as usize;\n        0", "q as usize");
    let emitted = ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).unwrap();
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        println!(
            "RAW-RECEIVER positive-retention contrast solve={:#?}",
            super::model_cache::solve_receipt()
        );
        let (p, _) = table
            .entries
            .iter()
            .find(|(s, _)| s.label == "target::p")
            .unwrap();
        assert!(
            ctx.raw_boundary_artifacts
                .additive_family_receipts
                .iter()
                .any(
                    |receipt| receipt.owner_local_def_id == p.fn_did.local_def_index.as_u32()
                        && receipt
                            .cause
                            .contains("raw-receiver-result:View(PositiveRetention)")
                ),
            "the observed returned-address retention hold remains attributed"
        );
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        let held = emission.plan.held_classes();
        let (files, _, _, _) = super::round_files(
            tcx,
            &capture,
            &emission.plan,
            &emission.texts,
            &held,
            &BTreeSet::new(),
            emission.plan.root_file.as_ref(),
            &table,
        )
        .unwrap();
        assert!(
            !emission
                .plan
                .bridge_events(&held)
                .iter()
                .any(|event| event.stage == BridgeReceiptStage::Terminal
                    && event.state == BridgeReceiptState::Applied
                    && event.site.bridge_kind == "return-caller-receive-raw")
        );
        files.into_values().next().unwrap()
    })
    .expect("unchanged positive-retention contrast compiles");
    assert!(super::verify::type_checks_str(&emitted));
    assert!(
        emitted
            .split_whitespace()
            .collect::<String>()
            .contains("qasusize")
    );
}
