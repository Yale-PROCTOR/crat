//! Actual annotated and shared receivers of the banked mutable-slice return.

use std::collections::BTreeSet;

use rustc_hir::{ExprKind, QPath, def::Res};
use rustc_middle::{mir::RETURN_PLACE, ty::TyKind};

use super::{
    bridge_receipt::SignatureClassId,
    decision::{
        SubjectKind,
        construction::{CallResultTarget, Construction},
        lifetime::FnSignatureSlot,
        seam::Form,
    },
    delivery_custody::TypeShape,
};

#[derive(Clone, Copy, Debug)]
enum ReceiverShape {
    AnnotatedMutable,
    InferredShared,
}

impl ReceiverShape {
    fn mutable(self) -> bool {
        matches!(self, Self::AnnotatedMutable)
    }

    fn source(self) -> String {
        let declaration = match self {
            Self::AnnotatedMutable => "let q: *mut i32 = target(values.as_mut_ptr());",
            Self::InferredShared => "let q = target(values.as_mut_ptr());",
        };
        let write = if self.mutable() {
            "*q.offset(0) += 1;"
        } else {
            ""
        };
        format!(
            r#"
            #![allow(dead_code, unused_unsafe)]
            unsafe fn target(p: *mut i32) -> *mut i32 {{
                *p.offset(1) += 1;
                p
            }}
            pub unsafe fn entry() -> i32 {{
                let mut values = [3, 5, 7];
                {declaration}
                {write}
                *q.offset(0) + *q.offset(1)
            }}
        "#
        )
    }
}

fn check(shape: ReceiverShape) {
    let source = shape.source();
    let emitted = ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original receiver-shape AST capture");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one actual receiver-shape decision call");
        let solve = super::model_cache::solve_receipt();
        println!("RETURN-RECEIVER-SHAPE {shape:?} solve={solve:#?}\ninput={source}");
        assert!(solve.is_some(), "actual tiny-fixture solve receipt is mandatory");
        let (parameter, parameter_decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual banked mutable-slice source parameter");
        let (receiver, decision) = table.entries.iter().find(|(subject, _)| subject.label == "entry::q")
            .expect("actual receiver q");
        let node = (receiver.fn_did, receiver.hir_id);
        let SubjectKind::Param { hir_index } = parameter.kind else { panic!("p is a real parameter") };
        assert_eq!(receiver.kind, SubjectKind::Local);
        for (owner, local) in [(parameter.fn_did, parameter.local), (parameter.fn_did, RETURN_PLACE),
            (receiver.fn_did, receiver.local)] {
            let kind = ctx.slots.fn_local_slots.get(&owner)
                .and_then(|slots| slots.slot_for_local_depth(local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(owner, slot)));
            println!("RETURN-RECEIVER-SHAPE {shape:?} actual {owner:?}/{local:?}={kind:?}");
            assert_eq!(kind, Some(&super::SlotKind::Ref), "actual p/return/q model-Ref premise");
        }
        assert_eq!(receiver.mutable, shape.mutable(), "actual receiver access qualifier");
        assert_eq!(ctx.mut_facts.is_mutable(receiver.fn_did, receiver.local), shape.mutable(),
            "receiver mutability is an exported use fact, independent of its original raw annotation");
        match shape {
            ReceiverShape::AnnotatedMutable => {
                let span = receiver.ty_span.expect("actual explicit raw q annotation");
                let annotation = tcx.sess.source_map().span_to_snippet(span).unwrap();
                assert_eq!(annotation.chars().filter(|character| !character.is_whitespace()).collect::<String>(), "*muti32");
            }
            ReceiverShape::InferredShared => assert!(receiver.ty_span.is_none()),
        }
        assert_eq!(ctx.constructions.by_binding.get(&node), Some(&Construction::CallResult));
        assert_eq!(ctx.constructions.call_result_targets.get(&node), Some(&CallResultTarget::DirectLocal(parameter.fn_did)));
        let initializer = tcx.hir_node(ctx.constructions.init_hirs[&node]).expect_expr();
        let ExprKind::Call(callee, _) = initializer.kind else { panic!("exact original direct-call initializer") };
        assert!(matches!(callee.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Def(_, did) if did == parameter.fn_did.to_def_id())));
        assert_eq!(ctx.constructions.init_spans.get(&node), Some(&initializer.span));
        let origins = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&parameter.fn_did)).expect("actual native callee origins");
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        assert!(origins.body.depth0_value_flows().contains(&(
            SlotOwner::Local(parameter.local), SlotOwner::Local(RETURN_PLACE))));
        let permit = ctx.lifetime_eligibility.return_permit((parameter.fn_did, parameter.hir_id));
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual receiver-shape emission plan");
        let caller = SignatureClassId::of(receiver.fn_did);
        let callee_owner = SignatureClassId::of(parameter.fn_did);
        println!("RETURN-RECEIVER-SHAPE {shape:?}: q={receiver:#?}; candidate={:?}; terminal={decision:#?}; callee={parameter_decision:#?}; native_permit={permit:?}; receiver_permit={:?}; receiver_permit_failure={:?}; receiver_failure={:?}; input_unavailable={:?}; caller_hold={:?}; callee_hold={:?}",
            ctx.hypothetical.entries.iter().find(|(subject, _)| (subject.fn_did, subject.hir_id) == node).map(|(_, decision)| decision),
            ctx.lifetime_eligibility.inferred_permit(node), ctx.lifetime_eligibility.failure(node),
            table.return_receivers.failures.get(&node), table.seams.receiver_inputs.unavailable.get(&node),
            emission.plan.class_hold_reason(caller), emission.plan.class_hold_reason(callee_owner));
        println!("RETURN-RECEIVER-SHAPE {shape:?} additive-fallbacks={:#?}", ctx.raw_boundary_artifacts.additive_family_receipts);
        assert!(permit.is_some(), "the banked native callee return permit is an actual premise");
        assert_eq!(super::decision::seam::form_of(parameter_decision), Form::Slice { mutable: true });
        let interface = table.return_interfaces.functions.get(&parameter.fn_did).expect("actual mutable-slice callee return");
        assert_eq!(interface.form, Form::Slice { mutable: true });
        let lifetime_plan = table.lifetime_plan.function(parameter.fn_did).expect("actual callee lifetime plan");
        let lifetime = lifetime_plan.lifetime_for(FnSignatureSlot::arg(hir_index + 1, 0, 0)).unwrap();
        assert_eq!(lifetime_plan.lifetime_for(FnSignatureSlot::RETURN), Some(lifetime));
        assert_eq!(interface.lifetime, lifetime);
        assert_eq!(interface.lifetime_plan_digest, lifetime_plan.digest());

        // Production requirements begin after source/return/receiver model
        // facts, original declaration shape and the banked callee permit.
        assert_eq!(super::decision::seam::form_of(decision), Form::Slice { mutable: shape.mutable() },
            "annotation does not command Raw; mutable return may weaken to a shared receiver");
        assert!(emission.plan.class_finalization.classes[&caller].is_ready(), "{:#?}", emission.plan.class_finalization.classes[&caller]);
        assert!(emission.plan.class_finalization.classes[&callee_owner].is_ready());
        assert!(table.slice_constructions.iter().filter(|plan| plan.node == node)
            .all(|plan| plan.replacement.as_ref().is_none_or(|text| !text.contains("from_raw_parts"))),
            "an already borrowed callee result requires no raw-slice constructor");
        let held = emission.plan.held_classes();
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(&held, &BTreeSet::new(), &table).unwrap();
        let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
            emission.plan.root_file.as_ref(), &table, Some(&emission.plan.terminal_call_plans)).unwrap();
        assert_eq!(files.len(), 1);
        files.into_values().next().unwrap()
    }).expect("original valid-stack receiver-shape input compiles");
    assert!(
        super::verify::type_checks_str(&emitted),
        "eligible receiver-shape output must type/borrow-check: {shape:?}\n{emitted}"
    );
    let declarations =
        super::delivery_custody::inventory_source("receiver-shape.rs", &emitted).unwrap();
    let receivers = declarations
        .iter()
        .filter(|row| row.owner == "entry" && row.binding == "q" && row.parameter_index.is_none())
        .collect::<Vec<_>>();
    let [receiver] = receivers.as_slice() else { panic!("one exact emitted receiver declaration") };
    assert!(receiver.type_is_fully_explicit);
    let TypeShape::Reference { mutable, pointee } = &receiver.type_shape else {
        panic!("q actually declares a borrowed slice: {receiver:#?}")
    };
    assert_eq!(*mutable, shape.mutable());
    assert!(matches!(pointee.as_ref(), TypeShape::Slice { element }
        if matches!(element.as_ref(), TypeShape::Named { path } if path == "i32")));
    let syntax =
        super::bridge_custody_syntax::inventory_source("receiver-shape.rs", &emitted).unwrap();
    let bindings = syntax
        .bindings
        .iter()
        .filter(|binding| binding.owner == "entry" && binding.name == "q")
        .collect::<Vec<_>>();
    let [binding] = bindings.as_slice() else { panic!("one exact lexical receiver binding") };
    let initializer = binding.init_span.expect("actual emitted q initializer");
    let target_calls = syntax
        .calls
        .iter()
        .filter(|call| {
            call.owner == "entry"
                && call.span.lo >= initializer.lo
                && call.span.hi <= initializer.hi
                && call.callee_path.as_deref() == Some("target")
        })
        .collect::<Vec<_>>();
    let [target_call] = target_calls.as_slice() else {
        panic!("q initializer evaluates the native callee exactly once")
    };
    assert!(
        !syntax.calls.iter().any(|outer| outer.owner == "entry"
            && outer.span.lo >= initializer.lo
            && outer.span.hi <= initializer.hi
            && outer.span.lo <= target_call.span.lo
            && outer.span.hi >= target_call.span.hi
            && outer.callee_path.as_deref().is_some_and(|path| matches!(
                path.rsplit("::").next(),
                Some("from_raw_parts" | "from_raw_parts_mut")
            ))),
        "already-slice result must not be wrapped in a raw constructor"
    );
    ::utils::compilation::run_compiler_on_str(&emitted, |tcx| {
        let target = tcx
            .hir_body_owners()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == "target")
            .unwrap();
        let signature = tcx.fn_sig(target).skip_binder().skip_binder();
        let TyKind::Ref(region, parameter, mutable) = *signature.inputs()[0].kind() else {
            panic!("callee keeps mutable Slice parameter")
        };
        assert!(mutable.is_mut());
        assert!(matches!(parameter.kind(), TyKind::Slice(element) if *element == tcx.types.i32));
        let TyKind::Ref(return_region, returned, mutable) = *signature.output().kind() else {
            panic!("callee keeps mutable Slice return")
        };
        assert!(mutable.is_mut());
        assert_eq!(parameter, returned);
        assert_eq!(region, return_region);
        let entry = tcx
            .hir_body_owners()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == "entry")
            .unwrap();
        let body = tcx.mir_drops_elaborated_and_const_checked(entry).borrow();
        let locals = body
            .var_debug_info
            .iter()
            .filter_map(|info| {
                if info.name.as_str() != "q" {
                    return None;
                }
                let rustc_middle::mir::VarDebugInfoContents::Place(place) = &info.value else {
                    return None;
                };
                place.as_local()
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(locals.len(), 1);
        let local = *locals.iter().next().unwrap();
        let TyKind::Ref(_, slice, mutable) = *body.local_decls[local].ty.kind() else {
            panic!("q's actual initialized value is a reference")
        };
        assert_eq!(mutable.is_mut(), shape.mutable());
        assert!(matches!(slice.kind(), TyKind::Slice(element) if *element == tcx.types.i32));
    })
    .expect("actual emitted receiver/callee types; no second model entry");
    println!("RETURN-RECEIVER-SHAPE {shape:?} emitted={emitted}");
}

#[test]
fn return_receiver_shape_raw_annotation_still_admits_a_mutable_slice() {
    check(ReceiverShape::AnnotatedMutable);
}

#[test]
fn return_receiver_shape_mutable_return_weakens_to_a_shared_slice_receiver() {
    check(ReceiverShape::InferredShared);
}

fn check_caller_reversion(shape: ReceiverShape) {
    use super::{
        bridge_receipt::{
            BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
            RAW_BOUNDARY_T2_WAIVER_ID,
        },
        decision::return_receiver::ReceiverDeclaration,
    };
    let source = shape.source();
    let (baseline, reverted, callee_kept, declaration_key, receive_key, initializer, events) =
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let capture = super::ast_transform::capture_ast(tcx).expect("one original receiver-reversion capture");
            let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            ))).expect("one actual receiver-reversion decision call");
            let solve = super::model_cache::solve_receipt();
            println!("RETURN-RECEIVER-SHAPE REVERSION {shape:?} solve={solve:#?}");
            assert!(solve.is_some());
            let (subject, decision) = table.entries.iter().find(|(subject, _)| subject.label == "entry::q").unwrap();
            let (parameter, _) = table.entries.iter().find(|(subject, _)| subject.label == "target::p").unwrap();
            let node = (subject.fn_did, subject.hir_id);
            for (owner, local) in [(subject.fn_did, subject.local), (parameter.fn_did, parameter.local),
                (parameter.fn_did, RETURN_PLACE)] {
                let slot = ctx.slots.fn_local_slots[&owner].slot_for_local_depth(local, 0).unwrap();
                assert_eq!(ctx.model.get(&super::SlotRef::Local(owner, slot)), Some(&super::SlotKind::Ref));
            }
            assert_eq!(subject.mutable, shape.mutable());
            assert_eq!(super::decision::seam::form_of(decision), Form::Slice { mutable: shape.mutable() });
            assert!(ctx.lifetime_eligibility.return_permit((parameter.fn_did, parameter.hir_id)).is_some());
            let receiver = table.return_receivers.plans.get(&node).expect("actual admitted receiver carrier");
            let interface = table.return_interfaces.functions.get(&receiver.callee).unwrap();
            assert_eq!(interface.form, Form::Slice { mutable: true },
                "the actual call returns a mutable Slice before receiver weakening");
            assert_eq!(receiver.candidate_interface, *interface);
            assert_eq!(receiver.raw_result.mutability, super::decision::raw_boundary::RawMutability::Mut);
            assert_eq!(receiver.declaration, match shape {
                ReceiverShape::AnnotatedMutable => ReceiverDeclaration::Existing,
                ReceiverShape::InferredShared => ReceiverDeclaration::Inferred,
            });
            let caller = SignatureClassId::of(subject.fn_did);
            let callee = SignatureClassId::of(receiver.callee);
            let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans).unwrap();
            assert!(emission.plan.class_finalization.classes[&caller].is_ready());
            assert!(emission.plan.class_finalization.classes[&callee].is_ready());
            let held = emission.plan.held_classes();
            assert!(!held.contains(&caller) && !held.contains(&callee));
            let atoms = BTreeSet::new();
            let (files, _, _, _, _) = super::round_files(tcx, &capture, &emission.plan, &emission.texts,
                &held, &atoms, emission.plan.root_file.as_ref(), &table).unwrap();
            assert_eq!(files.len(), 1);
            let baseline = files.into_values().next().unwrap();
            let locate = |span: rustc_span::Span| {
                let file = tcx.sess.source_map().lookup_source_file(span.lo());
                (super::bridge_custody_export::file_label(&super::file_key(&file.name).unwrap()),
                    span.lo().0 - file.start_pos.0, span.hi().0 - file.start_pos.0)
            };
            let (declaration_span, declaration_owner, declaration_callee, declaration_kind) = match shape {
                ReceiverShape::AnnotatedMutable => (subject.ty_span.expect("real written q type span"),
                    caller, subject.fn_did, "subject-declaration"),
                ReceiverShape::InferredShared => {
                    assert!(subject.ty_span.is_none());
                    (subject.binding_span, callee, receiver.callee, "declaration-explicit-type")
                }
            };
            let declaration = locate(declaration_span);
            let binding = locate(subject.binding_span);
            let baseline_events = emission.plan.bridge_events(&held);
            let declarations = baseline_events.iter().filter(|event|
                event.stage == BridgeReceiptStage::Terminal && event.site.owner_class == declaration_owner
                    && event.site.caller == subject.fn_did
                    && event.site.callee == BridgeCalleeId::Local(declaration_callee)
                    && event.site.bridge_kind == declaration_kind && event.site.file == declaration.0
                    && (event.site.lo, event.site.hi) == (declaration.1, declaration.2)).collect::<Vec<_>>();
            let [declaration] = declarations.as_slice() else { panic!("one actual old declaration key with its real owner: {baseline_events:#?}") };
            assert_eq!(declaration.state, BridgeReceiptState::Applied);
            let receives = baseline_events.iter().filter(|event|
                event.stage == BridgeReceiptStage::Terminal && event.site.owner_class == callee
                    && event.site.caller == subject.fn_did && event.site.callee == BridgeCalleeId::Local(receiver.callee)
                    && event.site.bridge_kind == "return-caller-receive-ref" && event.site.file == binding.0
                    && (event.site.lo, event.site.hi) == (binding.1, binding.2)).collect::<Vec<_>>();
            let [receive] = receives.as_slice() else { panic!("one actual old receiver value handoff key") };
            assert_eq!(receive.state, BridgeReceiptState::Applied);
            let inputs = &emission.plan.terminal_call_plans.receiver_inputs;
            let native_retention = inputs.plans.get(&node).map(|input| &input.retention)
                .or_else(|| inputs.unavailable.get(&node).and_then(|input| input.retention.as_ref()));
            assert!(matches!(native_retention, Some(super::decision::raw_boundary::RetentionVerdict::Unknown { .. })),
                "the raw-result tier comes from actual copied-local retention, not callee no-retain");
            let mut selected = held.clone();
            selected.insert(caller);
            let (effective, reasons) = emission.plan.terminal_call_plans.input_reversion_closure(&selected, &atoms);
            println!("RETURN-RECEIVER-SHAPE REVERSION {shape:?}: source_return={interface:#?}; q_form={:?}; input={:#?}; unavailable={:#?}; actual_retention={native_retention:#?}; selected={selected:?}; effective={effective:?}; closure_causes={reasons:#?}",
                receiver.receiver_form, inputs.plans.get(&node), inputs.unavailable.get(&node));
            let reverted = super::round_files(tcx, &capture, &emission.plan, &emission.texts,
                &selected, &atoms, emission.plan.root_file.as_ref(), &table).map(|(files, _, _, _, _)| {
                    assert_eq!(files.len(), 1);
                    files.into_values().next().unwrap()
                });
            (baseline, reverted, !effective.contains(&callee), declaration.site.clone(), receive.site.clone(),
                (locate(receiver.initializer_span), interface.lifetime_plan_digest.clone()),
                emission.plan.bridge_events(&selected))
        }).expect("unchanged banked receiver-shape fixture compiles");
    assert!(
        super::verify::type_checks_str(&baseline),
        "baseline receiver-shape output compiles:\n{baseline}"
    );
    // Independently inspect the actual emitted call-result form before the
    // intended RED. A shared q does not make target's returned value shared.
    ::utils::compilation::run_compiler_on_str(&baseline, |tcx| {
        let target = tcx.hir_body_owners().find(|owner| tcx.def_path_str(owner.to_def_id()) == "target").unwrap();
        let output = tcx.fn_sig(target).skip_binder().skip_binder().output();
        assert!(matches!(output.kind(), TyKind::Ref(_, slice, mutable)
            if mutable.is_mut() && matches!(slice.kind(), TyKind::Slice(element) if *element == tcx.types.i32)),
            "the baseline call actually returns a mutable Slice; no negative-write fact is injected");
    }).expect("model-free actual source-result inspection");
    assert!(
        callee_kept,
        "caller-only retirement must keep the licensed native mutable Slice return: {shape:?}"
    );
    let reverted =
        reverted.expect("caller-only raw receiver initializer is mechanically available");
    assert!(
        super::verify::type_checks_str(&reverted),
        "actual raw receiver with native callee output compiles: {shape:?}\n{reverted}"
    );
    for key in [&declaration_key, &receive_key] {
        let old = events
            .iter()
            .filter(|event| event.site == *key && event.stage == BridgeReceiptStage::Terminal)
            .collect::<Vec<_>>();
        let [old] = old.as_slice() else {
            panic!("one terminal fate for each exact old declaration/receive key")
        };
        assert_eq!(
            old.state,
            BridgeReceiptState::Dropped,
            "retired old owner/key must be dropped: {old:#?}"
        );
        assert!(old.drop_reason.is_some());
    }
    let raw = events
        .iter()
        .filter(|event| {
            event.stage == BridgeReceiptStage::Terminal
                && event.site.owner_class == receive_key.owner_class
                && event.site.caller == receive_key.caller
                && event.site.callee == receive_key.callee
                && event.site.bridge_kind == "return-caller-receive-raw"
                && event.site.file == initializer.0.0
                && (event.site.lo, event.site.hi) == (initializer.0.1, initializer.0.2)
        })
        .collect::<Vec<_>>();
    let [raw] = raw.as_slice() else { panic!("one exact raw initializer receipt: {events:#?}") };
    assert_eq!(raw.state, BridgeReceiptState::Applied);
    assert_eq!(raw.found_form, (Form::Slice { mutable: true }).key());
    assert_eq!(raw.expected_form, "raw");
    assert_eq!(raw.retention, BridgeRetentionTier::T2);
    assert_eq!(raw.waiver_id.as_deref(), Some(RAW_BOUNDARY_T2_WAIVER_ID));
    assert!(raw.site.position.contains(&initializer.1));
    let declarations =
        super::delivery_custody::inventory_source("receiver-shape-reverted.rs", &reverted).unwrap();
    let q = declarations
        .iter()
        .filter(|row| row.owner == "entry" && row.binding == "q" && row.parameter_index.is_none())
        .collect::<Vec<_>>();
    let [q] = q.as_slice() else { panic!("one reverted q declaration") };
    match shape {
        ReceiverShape::AnnotatedMutable => assert!(
            matches!(q.type_shape, TypeShape::RawPointer { mutable: true, .. }),
            "the actual written raw annotation is restored"
        ),
        ReceiverShape::InferredShared => assert!(
            q.explicit_type.is_none(),
            "the original inferred declaration is restored"
        ),
    }
    ::utils::compilation::run_compiler_on_str(&reverted, |tcx| {
        let target = tcx.hir_body_owners().find(|owner| tcx.def_path_str(owner.to_def_id()) == "target").unwrap();
        let output = tcx.fn_sig(target).skip_binder().skip_binder().output();
        assert!(matches!(output.kind(), TyKind::Ref(_, slice, mutable)
            if mutable.is_mut() && matches!(slice.kind(), TyKind::Slice(element) if *element == tcx.types.i32)));
        let entry = tcx.hir_body_owners().find(|owner| tcx.def_path_str(owner.to_def_id()) == "entry").unwrap();
        let body = tcx.mir_drops_elaborated_and_const_checked(entry).borrow();
        let locals = body.var_debug_info.iter().filter_map(|info| {
            if info.name.as_str() != "q" { return None; }
            let rustc_middle::mir::VarDebugInfoContents::Place(place) = &info.value else { return None };
            place.as_local()
        }).collect::<BTreeSet<_>>();
        assert_eq!(locals.len(), 1);
        assert!(matches!(body.local_decls[*locals.iter().next().unwrap()].ty.kind(),
            TyKind::RawPtr(pointee, mutable) if mutable.is_mut() && *pointee == tcx.types.i32),
            "q's actual initialized value and original uses are raw");
    }).expect("model-free reverted receiver and surviving callee inspection");
    println!(
        "RETURN-RECEIVER-SHAPE REVERSION {shape:?}: raw_receipt={raw:#?}\nreverted={reverted}"
    );
}

#[test]
fn return_receiver_shape_annotated_caller_reversion_restores_its_raw_type_and_value() {
    check_caller_reversion(ReceiverShape::AnnotatedMutable);
}

#[test]
fn return_receiver_shape_shared_caller_reversion_uses_the_mutable_native_result() {
    check_caller_reversion(ReceiverShape::InferredShared);
}
