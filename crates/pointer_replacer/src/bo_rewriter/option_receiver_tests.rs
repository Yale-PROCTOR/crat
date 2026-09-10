//! Native mutable Option returns received as shared Option values.
//! The valid-stack memory-safety pattern fixture is compiled, never executed.

use std::collections::BTreeSet;

use rustc_hir::{ExprKind, QPath, def::Res};
use rustc_middle::{mir::RETURN_PLACE, ty::TyKind};

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
        RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
    },
    decision::{
        construction::{CallResultTarget, Construction},
        lifetime::FnSignatureSlot,
        raw_boundary::RetentionVerdict,
        seam::Form,
    },
    delivery_custody::TypeShape,
    mechanical_receipt::{MechanicalStage, MechanicalSubjectKey},
};

const INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn target(p: *mut i32) -> *mut i32 {
        if !p.is_null() { *p += 1; }
        p
    }
    pub unsafe fn entry() -> i32 {
        let mut value = 3;
        let q = target(&mut value);
        if !q.is_null() { *q } else { 0 }
    }
"#;

#[test]
fn option_receiver_shared_weakening_and_caller_retirement_keep_native_return_custody() {
    assert!(
        super::verify::type_checks_str(INPUT),
        "unchanged fixture type/borrow-checks"
    );
    let (baseline, retired) = ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original shared-Option receiver capture");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one ordinary tiny-fixture decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("OPTION-RECEIVER solve={solve:#?}\nINPUT:\n{INPUT}");
        assert!(solve.is_some(), "native tiny-fixture solve receipt is mandatory");
        let (p, p_decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p").unwrap();
        let (q, q_decision) = table.entries.iter().find(|(subject, _)| subject.label == "entry::q").unwrap();
        let node = (q.fn_did, q.hir_id);
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual shared-Option receiver emission plan");
        let caller = SignatureClassId::of(q.fn_did);
        let callee = SignatureClassId::of(p.fn_did);
        println!("OPTION-RECEIVER q={q:#?}; q_candidate={:?}; q_final={q_decision:#?}; p_final={p_decision:#?}; inferred_permit={:?}; receiver_failure={:?}; callee_interface={:?}; callee_hold={:?}; additive={:#?}",
            ctx.hypothetical.entries.iter().find(|(subject, _)| (subject.fn_did, subject.hir_id) == node).map(|(_, decision)| decision),
            ctx.lifetime_eligibility.inferred_permit(node), table.return_receivers.failures.get(&node),
            table.return_interfaces.functions.get(&p.fn_did), emission.plan.class_hold_reason(callee),
            ctx.raw_boundary_artifacts.additive_family_receipts);
        for (owner, local) in [(p.fn_did, p.local), (p.fn_did, RETURN_PLACE), (q.fn_did, q.local)] {
            let kind = ctx.slots.fn_local_slots.get(&owner)
                .and_then(|slots| slots.slot_for_local_depth(local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(owner, slot)));
            println!("OPTION-RECEIVER actual model {owner:?}/{local:?}={kind:?}");
            assert_eq!(kind, Some(&super::SlotKind::Ref), "actual p/return/q native Ref premise");
        }
        assert!(!q.mutable && !ctx.mut_facts.is_mutable(q.fn_did, q.local), "q is read-only by native facts");
        assert!(q.ty_span.is_none(), "q has no forced presentation annotation");
        assert_eq!(ctx.constructions.by_binding.get(&node), Some(&Construction::CallResult));
        assert_eq!(ctx.constructions.call_result_targets.get(&node), Some(&CallResultTarget::DirectLocal(p.fn_did)));
        let initializer = tcx.hir_node(ctx.constructions.init_hirs[&node]).expect_expr();
        let ExprKind::Call(function, _) = initializer.kind else { panic!("exact direct-call initializer") };
        assert!(matches!(function.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Def(_, did) if did == p.fn_did.to_def_id())));
        assert_eq!(ctx.constructions.init_spans.get(&node), Some(&initializer.span));
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        let origins = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&p.fn_did)).expect("native callee origin export");
        assert!(origins.body.depth0_value_flows().contains(&(
            SlotOwner::Local(p.local), SlotOwner::Local(RETURN_PLACE))));
        assert!(ctx.lifetime_eligibility.return_permit((p.fn_did, p.hir_id)).is_some());
        assert!(ctx.lifetime_eligibility.inferred_permit(node).is_some(), "actual receiver admission permit");
        let source_form = Form::Opt { mutable: true, slice: false };
        let target_form = Form::Opt { mutable: false, slice: false };
        let interface = table.return_interfaces.functions.get(&p.fn_did).expect("native mutable Option return");
        assert_eq!(interface.form, source_form);
        let lifetime = table.lifetime_plan.function(p.fn_did).unwrap();
        assert_eq!(lifetime.lifetime_for(FnSignatureSlot::RETURN), Some(interface.lifetime.as_str()));
        assert_eq!(interface.lifetime_plan_digest, lifetime.digest());

        // Production RED starts after the model, mutability and origin premises.
        assert_eq!(super::decision::seam::form_of(q_decision), target_form,
            "read-only receiver must consume the mutable Option return as a shared Option");
        let receiver = table.return_receivers.plans.get(&node).expect("actual admitted shared receiver");
        assert_eq!(receiver.candidate_interface, *interface);
        assert_eq!(receiver.receiver_form, target_form);
        assert!(emission.plan.class_finalization.classes[&callee].is_ready());
        assert!(emission.plan.class_finalization.classes[&caller].is_ready());
        let held = emission.plan.held_classes();
        let render = |classes: &BTreeSet<SignatureClassId>| {
            let (files, rollbacks, _, _, _) = super::round_files(tcx, &capture, &emission.plan,
                &emission.texts, classes, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table)
                .expect("actual shared-Option receiver round");
            assert!(rollbacks.is_empty());
            assert_eq!(files.len(), 1);
            files.into_values().next().unwrap()
        };
        let baseline = render(&held);
        let events = emission.plan.bridge_events(&held);
        let receives = events.iter().filter(|event| event.stage == BridgeReceiptStage::Terminal
            && event.site.owner_class == callee && event.site.caller == q.fn_did
            && event.site.callee == BridgeCalleeId::Local(p.fn_did)
            && event.site.bridge_kind == "return-caller-receive-ref").collect::<Vec<_>>();
        let [receive] = receives.as_slice() else { panic!("one exact borrowed receiver terminal row") };
        assert_eq!(receive.state, BridgeReceiptState::Applied);
        assert_eq!(receive.found_form, source_form.key());
        assert_eq!(receive.expected_form, target_form.key());
        assert_eq!(receive.retention, BridgeRetentionTier::None);
        assert!(receive.waiver_id.is_none());
        let option_rows = emission.plan.option_receipt_rows(&held);
        let rows = option_rows.iter().filter(|row| row.terminal.stage == MechanicalStage::Terminal
            && row.operation == "borrowed-return-receive"
            && matches!(row.terminal.obligation_key.subject, MechanicalSubjectKey::Local { owner, mir_local, .. }
                if owner == q.fn_did && mir_local == q.local.as_u32())).collect::<Vec<_>>();
        let [row] = rows.as_slice() else { panic!("one exact Option receiver terminal row") };
        assert_eq!(row.source_form, source_form.key());
        assert_eq!(row.target_form, target_form.key());

        let input = emission.plan.terminal_call_plans.receiver_inputs.plans.get(&node)
            .expect("native mutable-Option result has an actual receiver-retirement twin");
        assert!(matches!(input.retention, RetentionVerdict::Unknown { .. }));
        assert_eq!(input.receiver.candidate_interface.form, source_form);
        let mut selected = held.clone();
        selected.insert(caller);
        let effective = emission.plan.effective_reverted_classes(&selected, &BTreeSet::new());
        assert!(!effective.contains(&callee), "native mutable return survives caller retirement");
        assert!(input.active(&effective, &BTreeSet::new()));
        let retired = render(&selected);
        let retired_events = emission.plan.bridge_events(&selected);
        assert!(!retired_events.iter().any(|event| event.site == receive.site
            && event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Applied));
        let source_file = tcx.sess.source_map().lookup_source_file(initializer.span.lo());
        let file = super::bridge_custody_export::file_label(&super::file_key(&source_file.name).unwrap());
        let lo = initializer.span.lo().0 - source_file.start_pos.0;
        let hi = initializer.span.hi().0 - source_file.start_pos.0;
        let raw = retired_events.iter().filter(|event| event.stage == BridgeReceiptStage::Terminal
            && event.state == BridgeReceiptState::Applied && event.site.owner_class == callee
            && event.site.caller == q.fn_did && event.site.bridge_kind == "return-caller-receive-raw"
            && event.site.file == file && event.site.lo == lo && event.site.hi == hi).collect::<Vec<_>>();
        let [raw] = raw.as_slice() else { panic!("one exact raw receiver twin at the native initializer") };
        assert_eq!(raw.found_form, source_form.key());
        assert_eq!(raw.expected_form, "raw");
        assert_eq!(raw.retention, BridgeRetentionTier::T2);
        assert_eq!(raw.waiver_id.as_deref(), Some(RAW_BOUNDARY_T2_WAIVER_ID));
        (baseline, retired)
    }).expect("original shared-Option receiver fixture compiles");
    for (label, output) in [("shared", &baseline), ("retired", &retired)] {
        assert!(
            super::verify::type_checks_str(output),
            "{label} output type/borrow-checks:\n{output}"
        );
        let syntax =
            super::bridge_custody_syntax::inventory_source("option-receiver.rs", output).unwrap();
        let bindings = syntax
            .bindings
            .iter()
            .filter(|binding| binding.owner == "entry" && binding.name == "q")
            .collect::<Vec<_>>();
        let [binding] = bindings.as_slice() else { panic!("one exact q binding") };
        let initializer = binding.init_span.unwrap();
        assert_eq!(
            syntax
                .calls
                .iter()
                .filter(|call| call.owner == "entry"
                    && call.span.lo >= initializer.lo
                    && call.span.hi <= initializer.hi
                    && call.callee_path.as_deref() == Some("target"))
                .count(),
            1,
            "{label} initializer evaluates target exactly once"
        );
        let text = &output[initializer.lo as usize..initializer.hi as usize];
        if label == "shared" {
            let compact = text.split_whitespace().collect::<String>();
            assert!(
                compact.contains(".map("),
                "shared conversion consumes Option and preserves None: {text}"
            );
            assert!(
                !compact.contains(".as_deref"),
                "shared result must not borrow a temporary Option container"
            );
        } else {
            assert!(
                text.contains("map_or") && text.contains("from_mut"),
                "raw twin consumes native mutable Option: {text}"
            );
            assert!(
                !text
                    .split_whitespace()
                    .collect::<String>()
                    .contains(".map("),
                "shared conversion retires with q"
            );
        }
        ::utils::compilation::run_compiler_on_str(output, |tcx| {
            let target = tcx
                .hir_body_owners()
                .find(|owner| tcx.def_path_str(owner.to_def_id()) == "target")
                .unwrap();
            let signature = tcx.fn_sig(target).skip_binder().skip_binder();
            let TyKind::Adt(def, arguments) = *signature.output().kind() else {
                panic!("callee returns Option")
            };
            assert_eq!(tcx.item_name(def.did()).as_str(), "Option");
            assert_eq!(tcx.crate_name(def.did().krate).as_str(), "core");
            assert_eq!(
                signature.inputs()[0],
                signature.output(),
                "callee parameter and result keep identical native lifetime/type"
            );
            let TyKind::Ref(_, pointee, mutable) = *arguments.type_at(0).kind() else {
                panic!("Option payload is a native reference")
            };
            assert!(mutable.is_mut());
            assert_eq!(pointee, tcx.types.i32);
        })
        .expect("actual emitted target signature inspection; no second model solve");
    }
    let declarations =
        super::delivery_custody::inventory_source("option-receiver.rs", &baseline).unwrap();
    let receivers = declarations
        .iter()
        .filter(|row| row.owner == "entry" && row.binding == "q" && row.parameter_index.is_none())
        .collect::<Vec<_>>();
    let [receiver] = receivers.as_slice() else { panic!("one exact shared q declaration") };
    assert!(receiver.type_is_fully_explicit);
    let TypeShape::Option { payload, .. } = &receiver.type_shape else {
        panic!("q declares Option")
    };
    assert!(
        matches!(payload.as_ref(), TypeShape::Reference { mutable: false, pointee }
        if matches!(pointee.as_ref(), TypeShape::Named { path } if path == "i32"))
    );
}
