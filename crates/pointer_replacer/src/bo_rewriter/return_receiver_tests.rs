//! J14–J18 consumed receivers of the banked borrowed-return family fixtures.

use std::collections::BTreeSet;

use rustc_hir::{ExprKind, QPath, def::Res};
use rustc_middle::mir::RETURN_PLACE;

use super::{
    bridge_receipt::SignatureClassId,
    decision::{
        Decision, SubjectKind,
        construction::{CallResultTarget, Construction},
        lifetime::FnSignatureSlot,
        seam::Form,
    },
    delivery_custody::TypeShape,
};

#[derive(Clone, Copy, Debug)]
enum Family {
    Nullable,
    Slice,
}

impl Family {
    fn form(self) -> Form {
        match self {
            Self::Nullable => Form::Opt {
                mutable: true,
                slice: false,
            },
            Self::Slice => Form::Slice { mutable: true },
        }
    }

    fn input(self) -> &'static str {
        match self {
            Self::Nullable => {
                r#"
                #![allow(dead_code, unused_unsafe)]
                unsafe fn target(p: *mut i32) -> *mut i32 {
                    if !p.is_null() { *p += 1; }
                    p
                }
                pub unsafe fn entry() -> i32 {
                    let mut value = 3;
                    let q = target(&mut value);
                    *q += 2;
                    let result = *q;
                    let _ = target(core::ptr::null_mut());
                    result
                }
            "#
            }
            Self::Slice => {
                r#"
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
            "#
            }
        }
    }
}

fn check(family: Family) {
    let input = family.input();
    assert!(
        !input.contains("q.is_null"),
        "receiver family must come from the callee interface"
    );
    let emitted = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original receiver AST capture");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one actual receiver decision call");
        let solve = super::model_cache::solve_receipt();
        println!("RETURN-RECEIVER {family:?} solve={solve:#?}");
        assert!(solve.is_some(), "actual tiny-fixture solve receipt is mandatory");
        let (receiver, decision) = table.entries.iter().find(|(subject, _)| subject.label == "entry::q")
            .expect("actual named receiver q");
        let (parameter, _) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual target parameter");
        let node = (receiver.fn_did, receiver.hir_id);
        assert_eq!(receiver.kind, SubjectKind::Local);
        assert!(receiver.ty_span.is_none(), "the original receiver has no type annotation");
        for (owner, local) in [
            (receiver.fn_did, receiver.local),
            (parameter.fn_did, parameter.local),
            (parameter.fn_did, RETURN_PLACE),
        ] {
            let kind = ctx.slots.fn_local_slots.get(&owner)
                .and_then(|slots| slots.slot_for_local_depth(local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(owner, slot)));
            assert_eq!(kind, Some(&super::SlotKind::Ref), "actual model-Ref premise: {family:?}, {owner:?}, {local:?}");
        }
        assert!(ctx.mut_facts.is_mutable(receiver.fn_did, receiver.local),
            "the consumed receiver's mutable access is an actual exported fact");
        assert_eq!(ctx.constructions.by_binding.get(&node), Some(&Construction::CallResult));
        assert_eq!(ctx.constructions.call_result_targets.get(&node),
            Some(&CallResultTarget::DirectLocal(parameter.fn_did)));
        let initializer_hir = ctx.constructions.init_hirs[&node];
        let initializer = tcx.hir_node(initializer_hir).expect_expr();
        let ExprKind::Call(callee_expression, _) = initializer.kind else {
            panic!("the receiver must have an exact direct call initializer");
        };
        assert!(matches!(callee_expression.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Def(_, did) if did == parameter.fn_did.to_def_id())),
            "the independent HIR call must resolve to the same actual target");
        assert_eq!(ctx.constructions.init_spans.get(&node), Some(&initializer.span));
        let origins = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&parameter.fn_did)).expect("existing native callee origins");
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        assert!(origins.body.depth0_value_flows().contains(&(
            SlotOwner::Local(parameter.local), SlotOwner::Local(RETURN_PLACE))),
            "the banked callee parameter actually flows to its return");
        assert!(ctx.lifetime_eligibility.return_permit((parameter.fn_did, parameter.hir_id)).is_some(),
            "the existing native callee permit is an independent premise");
        let lifetime_plan = table.lifetime_plan.function(parameter.fn_did).expect("actual callee lifetime plan");
        let lifetime = lifetime_plan.lifetime_for(FnSignatureSlot::arg(1, 0, 0))
            .expect("actual callee origin parameter lifetime");
        assert_eq!(lifetime_plan.lifetime_for(FnSignatureSlot::RETURN), Some(lifetime));
        let interface = table.return_interfaces.functions.get(&parameter.fn_did)
            .expect("actual borrowed callee return interface");
        assert_eq!(interface.form, family.form(), "the callee's banked family must survive this receiver fixture");
        assert_eq!(interface.pointee, "i32");
        assert_eq!(interface.lifetime, lifetime);
        assert_eq!(interface.lifetime_plan_digest, lifetime_plan.digest());
        println!("RETURN-RECEIVER {family:?}: receiver={receiver:#?}; decision={decision:#?}; interface={interface:#?}; inferred_permit={:?}",
            ctx.lifetime_eligibility.inferred_permit(node));

        // Production assertions begin only after the exact model, call,
        // native permit, and callee interface premises have been established.
        let uses = match (family, decision) {
            (Family::Nullable, Decision::Opt { mutable: true, slice: false, uses })
            | (Family::Slice, Decision::Slice { mutable: true, uses }) => uses,
            (_, Decision::Ref { .. } | Decision::InferredRef { .. } | Decision::Slice { .. }
                | Decision::Opt { .. } | Decision::Box(_) | Decision::Degraded(_)) =>
                panic!("receiver must consume the full borrowed return family: {family:?}; {decision:#?}"),
        };
        assert!(!uses.is_empty(), "consumed receiver uses require their family-specific rewrites");
        let declarations = table.seams.explicit_declarations.iter()
            .filter(|site| site.category == "local" && site.node == Some(node)).collect::<Vec<_>>();
        let [declaration] = declarations.as_slice() else {
            panic!("one exact explicit receiver declaration owner: {declarations:#?}");
        };
        let callee_owner = SignatureClassId::of(parameter.fn_did);
        assert_eq!(declaration.owner_class, callee_owner, "the adapted callee owns the supplied receiver type");
        assert_eq!(declaration.caller, receiver.fn_did);
        assert_eq!(declaration.emitted_type, interface.temporary_type());
        assert!(table.slice_constructions.iter().filter(|plan| plan.node == node)
            .all(|plan| plan.replacement.as_ref().is_none_or(|text| !text.contains("from_raw_parts"))),
            "an already borrowed return cannot acquire a second raw-slice constructor");
        let receives = table.seams.zero_bridges.iter().filter(|site|
            site.caller == receiver.fn_did && site.span == Some(receiver.binding_span)
                && site.argument_kind == "return-call-result").collect::<Vec<_>>();
        let [receive] = receives.as_slice() else { panic!("one exact receiver value handoff receipt") };
        assert_eq!(receive.owner_class, callee_owner);
        assert_eq!(receive.expected_form, family.form().key());
        assert!(receive.position.contains(&interface.lifetime_plan_digest), "receiver receipt binds the actual callee lifetime plan");
        if matches!(family, Family::Nullable) {
            assert!(table.option_mut_bindings.contains(&node),
                "repeated mutable Option uses require their existing binding-reborrow plan");
        }
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual receiver emission plan");
        let receiver_owner = SignatureClassId::of(receiver.fn_did);
        let receiver_class = emission.plan.class_finalization.classes.get(&receiver_owner)
            .expect("actual receiver owner class");
        assert!(receiver_class.is_ready(), "receiver class is mechanically complete: {receiver_class:#?}");
        assert!(receiver_class.depends_on.contains(&callee_owner), "receiver retains its actual callee-owner dependency");
        assert!(emission.plan.class_finalization.classes.get(&callee_owner).is_some_and(super::plan::SignatureClassPlan::is_ready));
        let held = emission.plan.held_classes();
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(&held, &BTreeSet::new(), &table)
            .expect("actual initial receiver reverts");
        let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
            tcx, &capture, &reverts, emission.plan.root_file.as_ref(), &table,
            Some(&emission.plan.terminal_call_plans)).expect("actual receiver AST emission");
        assert_eq!(files.len(), 1);
        files.into_values().next().unwrap()
    }).expect("original receiver fixture type-checks");
    assert!(
        super::verify::type_checks_str(&emitted),
        "actual consumed receiver output must type/borrow-check: {family:?}\n{emitted}"
    );
    let declarations = super::delivery_custody::inventory_source("receiver-delivered.rs", &emitted)
        .expect("actual receiver declaration inventory");
    let receivers = declarations
        .iter()
        .filter(|row| row.owner == "entry" && row.binding == "q" && row.parameter_index.is_none())
        .collect::<Vec<_>>();
    let [receiver] = receivers.as_slice() else {
        panic!("one exact emitted q declaration: {declarations:#?}")
    };
    assert!(receiver.type_is_fully_explicit);
    let borrowed = match (family, &receiver.type_shape) {
        (Family::Nullable, TypeShape::Option { payload, .. }) => payload.as_ref(),
        (Family::Slice, shape) => shape,
        _ => panic!("the declared receiver preserves the actual return family: {receiver:#?}"),
    };
    let TypeShape::Reference {
        mutable: true,
        pointee,
    } = borrowed
    else {
        panic!("the receiver's declared payload is a mutable borrowed form: {receiver:#?}");
    };
    match (family, pointee.as_ref()) {
        (Family::Nullable, TypeShape::Named { path }) if path == "i32" => {}
        (Family::Slice, TypeShape::Slice { element }) if matches!(element.as_ref(), TypeShape::Named { path } if path == "i32") =>
            {}
        _ => panic!("the receiver has the actual native pointee shape: {receiver:#?}"),
    }
    let syntax = super::bridge_custody_syntax::inventory_source("receiver-delivered.rs", &emitted)
        .expect("actual receiver initializer inventory");
    let bindings = syntax
        .bindings
        .iter()
        .filter(|binding| binding.owner == "entry" && binding.name == "q")
        .collect::<Vec<_>>();
    let [binding] = bindings.as_slice() else { panic!("one exact lexical q binding") };
    let initializer = binding.init_span.expect("actual receiver initializer");
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
    let [call] = calls.as_slice() else {
        panic!("the receiver keeps exactly one actual target call")
    };
    assert!(
        !syntax.calls.iter().any(|outer| outer.owner == "entry"
            && outer.span.lo >= initializer.lo
            && outer.span.hi <= initializer.hi
            && outer.span != call.span
            && outer.span.lo <= call.span.lo
            && outer.span.hi >= call.span.hi),
        "the borrowed result must not be wrapped in a second value constructor"
    );
    println!("RETURN-RECEIVER {family:?} emitted={emitted}");
}

#[test]
fn return_receiver_nullable_result_supplies_option_without_a_receiver_null_test() {
    check(Family::Nullable);
}

#[test]
fn return_receiver_slice_result_supplies_the_consumed_slice_local() {
    check(Family::Slice);
}

#[derive(Clone, Copy, Debug)]
enum ReceiverWithdrawal {
    Decision,
    TypedFailure,
}

fn check_active_initializer_withdrawal(withdrawal: ReceiverWithdrawal) {
    ::utils::compilation::run_compiler_on_str(Family::Nullable.input(), |tcx| {
        let (mut table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("actual receiver decision table");
        let solve = super::model_cache::solve_receipt();
        println!("RETURN-RECEIVER admission control {withdrawal:?}: solve={solve:#?}");
        assert!(solve.is_some(), "actual tiny-fixture solve receipt is mandatory");
        let index = table.entries.iter().position(|(subject, _)| subject.label == "entry::q")
            .expect("actual receiver entry");
        let subject = table.entries[index].0.clone();
        let node = (subject.fn_did, subject.hir_id);
        let slot = ctx.slots.fn_local_slots[&subject.fn_did]
            .slot_for_local_depth(subject.local, 0).expect("actual receiver model slot");
        assert_eq!(ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)), Some(&super::SlotKind::Ref));
        assert!(matches!(&table.entries[index].1, Decision::Opt { mutable: true, slice: false, .. }),
            "the baseline receiver must be actually admitted before the consumer-state contrast");
        let receiver = table.return_receivers.plans.get(&node).expect("actual receiver carrier").clone();
        assert_eq!(ctx.constructions.call_result_targets.get(&node), Some(&CallResultTarget::DirectLocal(receiver.callee)));
        assert_eq!(ctx.constructions.init_hirs.get(&node), Some(&receiver.initializer_hir));
        assert_eq!(ctx.constructions.init_spans.get(&node), Some(&receiver.initializer_span));
        let interface = table.return_interfaces.functions.get(&receiver.callee)
            .expect("actual current callee interface").clone();
        assert_eq!(interface, receiver.candidate_interface);
        assert_eq!(super::decision::return_receiver::active_initializer(
            &table, node, receiver.initializer_hir, receiver.initializer_span), Some(&receiver),
            "baseline initializer is active under its real current interface");
        let original_model = ctx.model.clone();

        // Constructed consumer states only. Neither the original model,
        // initializer identity nor current callee interface is changed.
        match withdrawal {
            ReceiverWithdrawal::Decision => {
                table.entries[index].1 = Decision::Degraded(super::decision::Degradation {
                    subject: subject.label.clone(),
                    site: super::decision::emitability::EmitabilityFacts::site(tcx, subject.attribution_span()),
                    reason: super::decision::DegradeReason::ReturnNotAdapted,
                });
            }
            ReceiverWithdrawal::TypedFailure => {
                table.return_receivers.failures.insert(node, super::decision::return_receiver::ReceiverFailure {
                    node,
                    callee: receiver.callee,
                    kind: super::decision::return_receiver::FailureKind::CurrentCalleeInterfaceChanged,
                });
            }
        }
        assert_eq!(ctx.model, original_model, "consumer withdrawal never changes the model");
        assert_eq!(table.return_interfaces.functions.get(&receiver.callee), Some(&interface));
        assert_eq!(table.return_receivers.plans.get(&node), Some(&receiver));
        assert!(super::decision::return_receiver::active_initializer(
            &table, node, receiver.initializer_hir, receiver.initializer_span).is_none(),
            "withdrawn receiver cannot supply an already-safe initializer token: {withdrawal:?}");
    }).expect("original admission-control fixture compiles");
}

#[test]
fn return_receiver_withdrawn_decision_cannot_elide_initializer_construction() {
    check_active_initializer_withdrawal(ReceiverWithdrawal::Decision);
}

#[test]
fn return_receiver_typed_failure_cannot_elide_initializer_construction() {
    check_active_initializer_withdrawal(ReceiverWithdrawal::TypedFailure);
}

fn check_caller_class_reversion(family: Family) {
    use super::bridge_receipt::{
        BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
        RAW_BOUNDARY_T2_WAIVER_ID,
    };
    let (baseline, reverted, original_receive, refreshed, initializer_span, digest) =
        ::utils::compilation::run_compiler_on_str(family.input(), |tcx| {
            let capture = super::ast_transform::capture_ast(tcx).expect("one original reversion AST capture");
            let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            ))).expect("one actual receiver reversion decision call");
            let solve = super::model_cache::solve_receipt();
            println!("RETURN-RECEIVER caller-class reversion {family:?}: solve={solve:#?}");
            assert!(solve.is_some(), "actual tiny-fixture solve receipt is mandatory");
            let (subject, decision) = table.entries.iter().find(|(subject, _)| subject.label == "entry::q")
                .expect("actual q receiver");
            let node = (subject.fn_did, subject.hir_id);
            let receiver = table.return_receivers.plans.get(&node).expect("actual receiver carrier");
            let interface = table.return_interfaces.functions.get(&receiver.callee)
                .expect("actual borrowed callee interface");
            assert_eq!(super::decision::seam::form_of(decision), family.form());
            assert_eq!(interface.form, family.form());
            assert_eq!(receiver.candidate_interface, *interface);
            assert_eq!(receiver.source_reversion, super::decision::return_receiver::SourceReversion::BorrowedResultToRaw);
            assert_eq!(receiver.raw_result.mutability, super::decision::raw_boundary::RawMutability::Mut);
            // These exact fixtures have a mutable borrowed source and mutable
            // raw result. A shared-to-mutable permission is not presumed.
            assert!(matches!(interface.form, Form::Opt { mutable: true, .. } | Form::Slice { mutable: true }));
            let (parameter, _) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
                .expect("actual callee parameter");
            assert!(ctx.lifetime_eligibility.return_permit((parameter.fn_did, parameter.hir_id)).is_some());
            let retention = ctx.retention.get(parameter.fn_did, 0).expect("actual callee retention evidence");
            println!("RETURN-RECEIVER {family:?}: native retention={retention:#?}; interface={interface:#?}");
            let atom_ids = table.seams.raw_boundary_atom_groups.get(&node).into_iter().flatten()
                .map(|atom| atom.id.clone()).collect::<BTreeSet<_>>();
            if atom_ids.is_empty() {
                println!("RETURN-RECEIVER {family:?}: receiver-atom premise=absent; actual caller-class selection only; no synthetic atom ID");
            } else {
                println!("RETURN-RECEIVER {family:?}: existing receiver atoms={atom_ids:?}; this control selects only the actual caller class");
            }
            let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
                .expect("actual baseline receiver plan");
            let caller = SignatureClassId::of(subject.fn_did);
            let callee = SignatureClassId::of(receiver.callee);
            assert_ne!(caller, callee);
            assert!(emission.plan.class_finalization.classes.get(&caller).is_some_and(super::plan::SignatureClassPlan::is_ready));
            assert!(emission.plan.class_finalization.classes.get(&callee).is_some_and(super::plan::SignatureClassPlan::is_ready));
            let held = emission.plan.held_classes();
            assert!(!held.contains(&caller) && !held.contains(&callee));
            let baseline_reverts = super::ast_transform::revert_set_from_classes_and_atoms(&held, &BTreeSet::new(), &table)
                .expect("actual baseline reverts");
            let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx, &capture, &baseline_reverts, emission.plan.root_file.as_ref(), &table,
                Some(&emission.plan.terminal_call_plans)).expect("baseline borrowed receiver AST");
            assert_eq!(files.len(), 1);
            let baseline = files.into_values().next().unwrap();
            let events = emission.plan.bridge_events(&held);
            let receives = events.iter().filter(|event| event.stage == BridgeReceiptStage::Terminal
                && event.site.owner_class == callee && event.site.caller == subject.fn_did
                && event.argument_kind == "return-call-result"
                && event.expected_form == family.form().key()).collect::<Vec<_>>();
            let [receive] = receives.as_slice() else { panic!("one actual baseline borrowed receiver receipt") };
            assert_eq!(receive.state, BridgeReceiptState::Applied);
            let native_returns = events.iter().filter(|event| event.stage == BridgeReceiptStage::Terminal
                && event.site.owner_class == callee && event.site.caller == receiver.callee
                && event.site.bridge_kind == "return-raw-to-ref").collect::<Vec<_>>();
            let [native_return] = native_returns.as_slice() else { panic!("one actual native return receipt") };
            assert_eq!(native_return.state, BridgeReceiptState::Applied);
            assert_eq!(native_return.retention, BridgeRetentionTier::T1);
            assert!(native_return.waiver_id.is_none());
            assert!(native_return.site.position.contains(&interface.lifetime_plan_digest));

            use super::mechanical_receipt::{
                MechanicalMechanism, MechanicalStage, MechanicalState, MechanicalSubjectKey,
                reconcile_declaration_shape_rows,
            };
            let declaration_plans = emission.plan.declaration_receipt_plans.iter().filter(|plan|
                plan.owner_class == callee
                    && plan.obligation.planned.mechanism == MechanicalMechanism::DeclarationExplicitType
                    && matches!(plan.obligation.planned.key.subject,
                        MechanicalSubjectKey::Local { owner, mir_local, slot_depth: 0 }
                            if owner == subject.fn_did && mir_local == subject.local.as_u32()))
                .collect::<Vec<_>>();
            let [declaration_plan] = declaration_plans.as_slice() else {
                panic!("one exact q declaration common/specialized obligation: {declaration_plans:#?}");
            };
            let declaration_key = declaration_plan.obligation.planned.key.clone();
            let baseline_common = emission.plan.mechanical_receipts(&held).0;
            let baseline_specialized = emission.plan.declaration_receipt_rows(&held);
            reconcile_declaration_shape_rows(&baseline_specialized, &baseline_common)
                .expect("baseline declaration common/specialized reconciliation");
            let baseline_declarations = baseline_common.iter().filter(|event|
                event.key == declaration_key && event.stage == MechanicalStage::Terminal)
                .collect::<Vec<_>>();
            let [baseline_declaration] = baseline_declarations.as_slice() else {
                panic!("one actual Applied q declaration common row");
            };
            assert_eq!(baseline_declaration.state, MechanicalState::Applied);
            assert_eq!(baseline_specialized.iter().filter(|row|
                row.terminal.obligation_key == declaration_key
                    && row.terminal.stage == MechanicalStage::Terminal
                    && row.terminal.state == MechanicalState::Applied).count(), 1);

            let mut reverted_classes = held.clone();
            reverted_classes.insert(caller);
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
                &reverted_classes, &BTreeSet::new(), &table).expect("actual caller-class reversion");
            assert!(!reverts.keeps_subject(node.0, node.1));
            assert!(reverts.keeps(callee), "the callee remains active; its return type must not be retired with the caller");
            let reverted_common = emission.plan.mechanical_receipts(&reverted_classes).0;
            let reverted_specialized = emission.plan.declaration_receipt_rows(&reverted_classes);
            reconcile_declaration_shape_rows(&reverted_specialized, &reverted_common)
                .expect("caller-reverted declaration common/specialized reconciliation");
            let common = reverted_common.iter().filter(|event|
                event.key == declaration_key && event.stage == MechanicalStage::Terminal)
                .collect::<Vec<_>>();
            let specialized = reverted_specialized.iter().filter(|row|
                row.terminal.obligation_key == declaration_key
                    && row.terminal.stage == MechanicalStage::Terminal).collect::<Vec<_>>();
            let ([common], [specialized]) = (common.as_slice(), specialized.as_slice()) else {
                panic!("exact q declaration identity must retain one common and one specialized terminal fate");
            };
            assert_ne!(common.state, MechanicalState::Applied,
                "callee survival cannot keep the retired q explicit declaration Applied: {common:#?}");
            assert_ne!(specialized.terminal.state, MechanicalState::Applied);
            assert_eq!(specialized.terminal.state, common.state);
            assert_eq!(specialized.terminal_class_result, common.state);
            assert!(common.terminal_reason.is_some());
            let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx, &capture, &reverts, emission.plan.root_file.as_ref(), &table,
                Some(&emission.plan.terminal_call_plans)).expect("caller-reverted receiver AST");
            assert_eq!(files.len(), 1);
            let reverted = files.into_values().next().unwrap();
            let source_file = tcx.sess.source_map().lookup_source_file(receiver.initializer_span.lo());
            let initializer_span = (
                receiver.initializer_span.lo().0 - source_file.start_pos.0,
                receiver.initializer_span.hi().0 - source_file.start_pos.0,
            );
            (baseline, reverted, (**receive).clone(), emission.plan.bridge_events(&reverted_classes),
                initializer_span, interface.lifetime_plan_digest.clone())
        }).expect("original caller-class reversion fixture compiles");
    assert!(
        super::verify::type_checks_str(&baseline),
        "baseline borrowed receiver compiles: {family:?}\n{baseline}"
    );
    let declarations = super::delivery_custody::inventory_source("receiver-baseline.rs", &baseline)
        .expect("baseline receiver declaration custody");
    let q = declarations
        .iter()
        .filter(|row| row.owner == "entry" && row.binding == "q" && row.parameter_index.is_none())
        .collect::<Vec<_>>();
    let [q] = q.as_slice() else { panic!("one actual baseline q declaration") };
    assert!(q.type_is_fully_explicit);
    assert!(
        match (family, &q.type_shape) {
            (Family::Nullable, TypeShape::Option { payload, .. }) =>
                matches!(payload.as_ref(), TypeShape::Reference { mutable: true, .. }),
            (
                Family::Slice,
                TypeShape::Reference {
                    mutable: true,
                    pointee,
                },
            ) => matches!(pointee.as_ref(), TypeShape::Slice { .. }),
            _ => false,
        },
        "baseline q has the full borrowed family"
    );

    // Intended RED begins after actual baseline, owner, native permit and
    // retention premises. The same callee remains borrowed in this output.
    assert!(
        super::verify::type_checks_str(&reverted),
        "caller retirement needs an explicit borrowed-return-to-raw initializer twin: {family:?}\n{reverted}"
    );
    ::utils::compilation::run_compiler_on_str(&reverted, |tcx| {
        let entry = tcx.hir_body_owners().find(|owner| tcx.def_path_str(owner.to_def_id()) == "entry").unwrap();
        let target = tcx.hir_body_owners().find(|owner| tcx.def_path_str(owner.to_def_id()) == "target").unwrap();
        let output = tcx.fn_sig(target).skip_binder().skip_binder().output();
        let borrowed = match (family, output.kind()) {
            (Family::Nullable, rustc_middle::ty::TyKind::Adt(definition, arguments))
                if tcx.item_name(definition.did()).as_str() == "Option"
                    && tcx.crate_name(definition.did().krate).as_str() == "core" => arguments.type_at(0),
            (Family::Slice, _) => output,
            _ => panic!("the actual callee must keep its borrowed return family"),
        };
        assert!(matches!(borrowed.kind(), rustc_middle::ty::TyKind::Ref(_, _, mutable) if mutable.is_mut()));
        let body = tcx.mir_drops_elaborated_and_const_checked(entry).borrow();
        let locals = body.var_debug_info.iter().filter_map(|info| {
            if info.name.as_str() != "q" { return None; }
            let rustc_middle::mir::VarDebugInfoContents::Place(place) = &info.value else { return None };
            place.as_local()
        }).collect::<BTreeSet<_>>();
        assert_eq!(locals.len(), 1, "one actual receiver MIR local");
        let local = *locals.iter().next().unwrap();
        assert!(matches!(body.local_decls[local].ty.kind(),
            rustc_middle::ty::TyKind::RawPtr(pointee, mutable)
                if mutable.is_mut() && *pointee == tcx.types.i32),
            "retired q must actually be raw, not merely lose its annotation: {:?}", body.local_decls[local].ty);
    }).expect("actual raw receiver type inspection; no model entry");
    let previous = refreshed
        .iter()
        .filter(|event| {
            event.stage == BridgeReceiptStage::Terminal && event.site == original_receive.site
        })
        .collect::<Vec<_>>();
    let [previous] = previous.as_slice() else {
        panic!("one terminal fate for the original receiver receipt")
    };
    assert!(
        previous.state == BridgeReceiptState::Dropped
            || (previous.state == BridgeReceiptState::Applied && previous.expected_form == "raw"),
        "the retired receiver cannot remain Applied as a borrowed declaration: {previous:#?}"
    );
    let raw_receives = refreshed
        .iter()
        .filter(|event| {
            event.stage == BridgeReceiptStage::Terminal
                && event.state == BridgeReceiptState::Applied
                && event.site.caller == original_receive.site.caller
                && event.site.callee == original_receive.site.callee
                && matches!(event.site.callee, BridgeCalleeId::Local(_))
                && event.expected_form == "raw"
                && event.found_form == family.form().key()
                && ((event.site.lo, event.site.hi) == initializer_span
                    || event.site == original_receive.site)
        })
        .collect::<Vec<_>>();
    let [raw_receive] = raw_receives.as_slice() else {
        panic!("one exact applied raw receiver initializer receipt: {refreshed:#?}")
    };
    assert!(
        raw_receive.site.position.contains(&digest),
        "the twin must retain its actual native lifetime evidence link"
    );
    match raw_receive.retention {
        BridgeRetentionTier::T1 => assert!(raw_receive.waiver_id.is_none()),
        BridgeRetentionTier::T2 => assert_eq!(
            raw_receive.waiver_id.as_deref(),
            Some(RAW_BOUNDARY_T2_WAIVER_ID)
        ),
        BridgeRetentionTier::None => panic!("a raw receiver view needs an observed retention tier"),
    }
    println!(
        "RETURN-RECEIVER {family:?}: raw initializer receipt={raw_receive:#?}\nreverted={reverted}"
    );
}

#[test]
fn return_receiver_nullable_caller_reversion_uses_a_raw_result_twin() {
    check_caller_class_reversion(Family::Nullable);
}

#[test]
fn return_receiver_slice_caller_reversion_uses_a_raw_result_twin() {
    check_caller_class_reversion(Family::Slice);
}

#[test]
fn return_receiver_consumer_selected_unavailable_holds_only_its_interface_closure() {
    use super::decision::receiver_input::{ReceiverInputFailure, ReceiverInputUnavailable};
    let (baseline, restored) = ::utils::compilation::run_compiler_on_str(Family::Nullable.input(), |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original consumer-control capture");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one actual receiver table for the constructed consumer state");
        let solve = super::model_cache::solve_receipt();
        println!("RETURN-RECEIVER CONSUMER-ONLY unavailable-selection: solve={solve:#?}");
        assert!(solve.is_some(), "actual tiny-fixture solve receipt is mandatory");
        let (subject, _) = table.entries.iter().find(|(subject, _)| subject.label == "entry::q")
            .expect("actual q identity");
        let node = (subject.fn_did, subject.hir_id);
        let slot = ctx.slots.fn_local_slots[&subject.fn_did]
            .slot_for_local_depth(subject.local, 0).expect("actual q model slot");
        assert_eq!(ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)), Some(&super::SlotKind::Ref));
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual receiver input plan before consumer injection");
        let input = emission.plan.terminal_call_plans.receiver_inputs.plans.get(&node)
            .expect("actual admitted receiver-input identity and selection metadata").clone();
        assert!(matches!(input.retention, super::decision::raw_boundary::RetentionVerdict::Unknown { .. }),
            "native evidence stays Unknown; this test must not claim an actual positive sink");
        let caller = SignatureClassId::of(node.0);
        let callee = input.selection.callee;
        assert_eq!(input.receiver.candidate_interface, table.return_interfaces.functions[&input.receiver.callee]);
        assert!(emission.plan.class_finalization.classes[&caller].is_ready());
        assert!(emission.plan.class_finalization.classes[&callee].is_ready());
        assert!(emission.plan.class_finalization.classes[&caller].depends_on.contains(&callee),
            "the actual caller is a required interface dependent");
        let held = emission.plan.held_classes();
        let atoms = BTreeSet::new();
        assert!(!input.active(&held, &atoms));
        let mut consumer = emission.plan.clone();
        consumer.terminal_call_plans.receiver_inputs.plans.remove(&node);
        consumer.terminal_call_plans.receiver_inputs.unavailable.insert(node, ReceiverInputUnavailable {
            receiver: input.receiver.clone(), selection: input.selection.clone(),
            reason: ReceiverInputFailure::PositiveRetention,
            // Constructed policy input only: no fabricated native sink/trace.
            retention: None,
        });
        let (unselected, unselected_reasons) = consumer.terminal_call_plans.input_reversion_closure(&held, &atoms);
        assert_eq!(unselected, held, "an unselected future twin cannot hold the live interface");
        assert!(unselected_reasons.is_empty());
        let (baseline_files, _, _, _, _) = super::round_files(tcx, &capture, &consumer, &emission.texts,
            &held, &atoms, consumer.root_file.as_ref(), &table)
            .expect("unselected unavailable twin leaves baseline emission available");
        assert_eq!(baseline_files.len(), 1);
        let mut selected = held.clone();
        selected.insert(caller);
        assert!(input.active(&selected, &atoms));
        let unavailable = consumer.receiver_input_receipts.selected(
            &consumer.terminal_call_plans.receiver_inputs, &selected, &atoms);
        let [failure] = unavailable.failures.as_slice() else { panic!("one selected typed unavailable input") };
        assert_eq!(failure.kind, super::plan::receiver_input::FailureKind::AlternativeUnavailable);
        assert_eq!(failure.node, node);
        assert_eq!(failure.callee, callee);
        assert_eq!(consumer.terminal_call_plans.receiver_inputs.unavailable[&node].reason,
            ReceiverInputFailure::PositiveRetention);
        let (effective, reasons) = consumer.terminal_call_plans.input_reversion_closure(&selected, &atoms);
        assert!(effective.contains(&callee), "selected unavailable result view retires the changed callee");
        let required = super::plan::dependent_closure(&consumer.class_finalization.classes,
            &BTreeSet::from([callee]));
        assert!(required.contains(&caller));
        assert!(required.is_subset(&effective), "all actual required interface dependents are retired");
        assert!(reasons.get(&callee).is_some_and(|rows| rows.iter().any(|reason|
            reason == &format!("return-receiver-input-unavailable:caller={}:hir={}:PositiveRetention",
                node.0.local_def_index.as_u32(), node.1.local_id.as_u32()))));
        let (restored_files, _, _, _, _) = super::round_files(tcx, &capture, &consumer, &emission.texts,
            &selected, &atoms, consumer.root_file.as_ref(), &table)
            .expect("selected unavailable closure returns the original raw interfaces");
        assert_eq!(restored_files.len(), 1);
        println!("RETURN-RECEIVER CONSUMER-ONLY typed PositiveRetention (not native evidence): node={node:?}; selected={selected:?}; effective={effective:?}; reasons={reasons:?}");
        (baseline_files.into_values().next().unwrap(), restored_files.into_values().next().unwrap())
    }).expect("unchanged nullable receiver input compiles");
    assert!(
        super::verify::type_checks_str(&baseline),
        "unselected unavailable baseline compiles:\n{baseline}"
    );
    assert!(
        super::verify::type_checks_str(&restored),
        "selected unavailable original raw tree compiles:\n{restored}"
    );
}
