//! Actual writer-sibling coverage for a native borrowed return expression.
//! This memory-safety pattern fixture is compiled and inspected, never run.

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::mir::{BasicBlock, RETURN_PLACE, TerminatorKind};

use super::{
    CensusOutcomeKind, bridge_custody_export as custody,
    bridge_receipt::{BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, SignatureClassId},
    decision::{
        Decision,
        lifetime::FnSignatureSlot,
        raw_boundary::site_atom_id,
        seam::Form,
        sibling_overlap::{
            self, LocalPostCallEvidence, SiblingAccess, SiblingSource, SourceBridgeEvidence,
        },
    },
    sibling_audit::{Outcome, SubjectKind},
};

const INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn raw_pair(q: *const i32, dst: *mut i32) -> i32 {
        dst.write(8);
        q.read()
    }
    unsafe fn target(p: *mut i32) -> *mut i32 {
        *p.offset(1) += 1;
        p
    }
    pub unsafe fn caller(p: *mut i32) -> i32 {
        raw_pair(target(p), p)
    }
    pub unsafe fn entry() -> i32 {
        let mut values = [3, 5, 7];
        caller(values.as_mut_ptr())
    }
"#;

#[test]
fn expression_sibling_actual_writer_keeps_native_source_and_exact_pending_custody() {
    assert!(
        super::verify::type_checks_str(INPUT),
        "unchanged valid-stack input type/borrow-checks"
    );
    let (sources, export, events, expected_id, expected_pending, pending_key) =
        ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original expression-sibling AST");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one ordinary expression-sibling fixture decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("EXPRESSION-SIBLING solve={solve:#?}\nINPUT:\n{INPUT}");
        assert!(solve.is_some(), "actual fixture solve receipt is mandatory");
        let (source, source_decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual source producer parameter");
        let (caller_parameter, caller_decision) = table.entries.iter().find(|(subject, _)| subject.label == "caller::p")
            .expect("actual caller parameter");
        let (reader, reader_decision) = table.entries.iter().find(|(subject, _)| subject.label == "raw_pair::q")
            .expect("actual outer reader parameter");
        let (writer, writer_decision) = table.entries.iter().find(|(subject, _)| subject.label == "raw_pair::dst")
            .expect("actual distinct writer parameter");
        let model = |owner, local| ctx.slots.fn_local_slots.get(&owner)
            .and_then(|slots| slots.slot_for_local_depth(local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(owner, slot)));
        let permit = ctx.lifetime_eligibility.return_permit((source.fn_did, source.hir_id));
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual expression-sibling emission plan");
        let owner = SignatureClassId::of(source.fn_did);
        println!("EXPRESSION-SIBLING source model={:?}; return model={:?}; caller model={:?}; source={source_decision:#?}; caller={caller_decision:#?}; reader={reader_decision:#?}; writer={writer_decision:#?}; permit={permit:#?}; lifetime={:#?}; interface={:#?}; source hold={:?}; sink retention={:#?}; plans={:#?}; unavailable={:#?}",
            model(source.fn_did, source.local), model(source.fn_did, RETURN_PLACE),
            model(caller_parameter.fn_did, caller_parameter.local), table.lifetime_plan.function(source.fn_did),
            table.return_interfaces.functions.get(&source.fn_did), emission.plan.class_hold_reason(owner),
            ctx.retention.get(reader.fn_did, 0), table.seams.outbound_expressions.plans,
            table.seams.outbound_expressions.unavailable);
        for local in [source.local, RETURN_PLACE] {
            assert_eq!(model(source.fn_did, local), Some(&super::SlotKind::Ref),
                "authoring premise: real native source and return remain model-Ref: {local:?}");
        }
        assert!(permit.is_some(), "authoring premise: actual native parameter return permit");
        assert!(matches!(source_decision, Decision::Slice { mutable: true, .. }),
            "authoring premise: source producer keeps its banked mutable-slice form");
        let lifetime = table.lifetime_plan.function(source.fn_did).expect("actual source native lifetime");
        let region = lifetime.lifetime_for(FnSignatureSlot::arg(1, 0, 0)).expect("actual source parameter lifetime");
        assert_eq!(lifetime.lifetime_for(FnSignatureSlot::RETURN), Some(region));
        let interface = table.return_interfaces.functions.get(&source.fn_did).expect("actual source return interface");
        assert_eq!(interface.form, Form::Slice { mutable: true });
        assert_eq!(interface.lifetime, region);
        assert_eq!(interface.lifetime_plan_digest, lifetime.digest());
        assert!(emission.plan.class_finalization.classes.get(&owner).is_some_and(super::plan::SignatureClassPlan::is_ready),
            "authoring premise: native source producer remains Ready");
        for index in [0, 1] {
            assert_eq!(super::terminal_parameter_form(&table, &emission.plan.class_finalization, reader.fn_did, index), Form::Raw,
                "authoring premise: opaque raw_pair parameter {index} stays raw");
        }
        let plans = table.seams.outbound_expressions.plans.values().filter(|plan|
            plan.caller == caller_parameter.fn_did && plan.source_callee == source.fn_did
                && plan.sink_callee == BridgeCalleeId::Local(reader.fn_did) && plan.key.argument_index == 0)
            .collect::<Vec<_>>();
        let [plan] = plans.as_slice() else { panic!("authoring premise: one exact native-result argument carrier: {plans:#?}") };
        assert_eq!(plan.owner_class(), owner);
        assert_eq!(tcx.sess.source_map().span_to_snippet(plan.argument_span).unwrap(), "target(p)");
        assert_eq!(plan.key.subject, "<unrooted>");
        let sites = ctx.raw_boundary_sites.sites.iter().filter(|site| site.key == plan.key).collect::<Vec<_>>();
        let [site] = sites.as_slice() else { panic!("one original raw-boundary fact for native expression") };
        assert!(site.node.is_none());
        let coverages = table.sibling_overlap_inventory.coverage.iter().filter(|row| row.potential.site == plan.key).collect::<Vec<_>>();
        let [coverage] = coverages.as_slice() else { panic!("one real expression sibling coverage row") };
        let potential = &coverage.potential;
        println!("EXPRESSION-SIBLING exact coverage={coverage:#?}");
        assert!(matches!(coverage.evidence, SourceBridgeEvidence::NativeReturnExpression { use_hir_id } if use_hir_id == plan.argument_hir));
        let SiblingSource::NativeReturnExpression { argument_hir, source_callee, source_interface,
            mir_argument_local, temporary } = &potential.source else {
            panic!("expression source must not impersonate a declaration");
        };
        assert_eq!(*argument_hir, plan.argument_hir);
        assert_eq!(*source_callee, source.fn_did);
        assert_eq!(source_interface, interface);
        assert_eq!(temporary, &plan.temporary);
        assert_eq!(potential.source.owner_class(), owner);
        let body = tcx.mir_drops_elaborated_and_const_checked(potential.caller).borrow();
        let data = &body.basic_blocks[BasicBlock::from_u32(site.key.block)];
        assert_eq!(site.key.statement_index as usize, data.statements.len());
        let TerminatorKind::Call { args, .. } = &data.terminator().kind else { panic!("actual outer MIR call") };
        assert_eq!(args.len(), 2);
        let actual_local = args[0].node.place().and_then(|place| place.as_local());
        assert_eq!(*mir_argument_local, actual_local);
        let caller_flow = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&potential.caller));
        println!("EXPRESSION-SIBLING actual outer MIR argument={actual_local:?}; caller parameter={:?}; caller original argument origins={:?}; post-call={:#?}",
            caller_parameter.local, caller_flow.and_then(|flow| actual_local.and_then(|local|
                flow.body.depth0_argument_origins(&body, local))), potential.local_post_call);
        match &potential.local_post_call {
            LocalPostCallEvidence::ParameterProtected => panic!("native expression cannot use a remote producer parameter as caller protection"),
            LocalPostCallEvidence::ParameterOrigin { parameters } => {
                assert_eq!(body.arg_count, 1);
                assert_eq!(parameters, &vec![caller_parameter.local.as_usize()],
                    "protection belongs to the actual caller parameter, not source producer metadata");
            }
            LocalPostCallEvidence::Live { .. } | LocalPostCallEvidence::DeadUnprotected { .. }
            | LocalPostCallEvidence::Unknown(_) => {}
        }
        let [sibling] = potential.siblings.as_slice() else { panic!("one distinct actual pointer sibling") };
        assert_eq!(sibling.argument_index, 1);
        assert_eq!(sibling.argument_shape, Some("bare-local"));
        assert_ne!(sibling.argument_index, site.key.argument_index);
        assert!(matches!(sibling.access, SiblingAccess::Foster { local, mutable: true, defaulted: false } if local == writer.local),
            "authoring premise: exact sibling parameter has native write access: {sibling:#?}");
        assert!(sibling_overlap::risky_sibling(sibling),
            "authoring premise: actual A5 verdict must leave this writing sibling risky: {sibling:#?}");
        let expected_pending = !matches!(potential.local_post_call, LocalPostCallEvidence::DeadUnprotected { .. });
        let held = emission.plan.held_classes();
        let mut artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(&mut artifacts, &emission.plan, &held, &BTreeSet::new());
        let expected_id = site_atom_id(&site.key);
        let rows = artifacts.sibling_audit_rows.iter().filter(|row| row.coverage_id == expected_id).collect::<Vec<_>>();
        let [row] = rows.as_slice() else { panic!("one actual generated-expression audit row") };
        assert_eq!(row.source.kind, SubjectKind::NativeReturnExpression);
        assert_eq!(row.source.mir_local, actual_local.map(|local| local.as_u32()));
        let native = row.source.native_return.as_ref().expect("owned native source metadata");
        assert_eq!(native.source_owner, source.fn_did.local_def_index.as_u32());
        assert_eq!(native.lifetime_plan_digest, interface.lifetime_plan_digest);
        assert_eq!(row.outcome, if expected_pending { Outcome::PendingWaiver } else { Outcome::DeadUnprotected });
        assert!(row.data && row.issues.is_empty(), "complete real predicate audit: {row:#?}");
        let pending = artifacts.pending_sibling_receipts.iter().filter(|pending| pending.receipt.potential.site == site.key).collect::<Vec<_>>();
        assert_eq!(pending.len(), usize::from(expected_pending));
        let pending_key = pending.first().map(|pending| {
            assert_eq!(pending.receipt.reason, sibling_overlap::PENDING_REASON);
            assert_eq!(pending.receipt.tier, sibling_overlap::PENDING_TIER);
            assert_eq!(pending.receipt.waiver, sibling_overlap::PENDING_WAIVER);
            let key = pending.site.as_ref().expect("exact pending site location");
            assert_eq!(key.owner_class, owner);
            assert_eq!(key.caller, caller_parameter.fn_did);
            assert_eq!(key.callee, BridgeCalleeId::Local(reader.fn_did));
            assert_eq!(key.position, "arg0");
            key.receipt_key()
        });
        assert!(artifacts.bridge_events.iter().any(|event| event.site.owner_class == owner
            && event.site.bridge_kind == "outbound-native-return-argument"
            && event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Applied));
        let original_files = tcx.sess.source_map().files().iter().filter_map(|file|
            Some((super::file_key(&file.name)?, file.src.as_ref()?.to_string()))).collect::<BTreeMap<_, _>>();
        let export = custody::capture(tcx, &capture, &table, &emission.plan, &original_files);
        let (files, rollbacks, _, _) = super::round_files(tcx, &capture, &emission.plan, &emission.texts,
            &held, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table).expect("actual writer-sibling output");
        assert!(rollbacks.is_empty(), "pending stamping does not change emission or hold a class");
        let sources = files.into_iter().map(|(file, text)| (custody::file_label(&file), text)).collect::<BTreeMap<_, _>>();
        println!("EXPRESSION-SIBLING audit={row:#?}; pending={pending:#?}; output={sources:#?}");
        (sources, export, artifacts.bridge_events, expected_id, expected_pending, pending_key)
    }).expect("original writer-sibling fixture compiles");
    assert_eq!(sources.len(), 1);
    for text in sources.values() {
        assert!(
            super::verify::type_checks_str(text),
            "actual writer-sibling output type/borrow-checks:\n{text}"
        );
    }
    let audit = export
        .sibling_audit
        .as_ref()
        .expect("owned all-site audit export");
    assert!(audit.expected_coverage_ids.contains(&expected_id));
    assert_eq!(
        audit
            .rows
            .iter()
            .filter(|row| row.coverage_id == expected_id)
            .count(),
        1
    );
    if let Some(key) = pending_key {
        assert!(expected_pending);
        assert_eq!(
            export
                .pending
                .iter()
                .filter(|descriptor| descriptor.receipt_key == key)
                .count(),
            1,
            "real pending expression has one pinned-parser custody expectation"
        );
    } else {
        assert!(
            !expected_pending,
            "a complete local exemption is the only nonpending branch of this risky-writer control"
        );
    }
    let comparison =
        custody::compare_capture(&export, &events, Some(&sources), CensusOutcomeKind::Emitted);
    assert!(
        comparison.data,
        "real emitted pending-expression custody must match its receipts: {comparison:#?}"
    );
}
