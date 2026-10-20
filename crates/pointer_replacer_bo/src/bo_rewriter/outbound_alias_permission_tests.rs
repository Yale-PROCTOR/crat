//! Permission probe for a native returned slice passed to a local raw aliaser.
//! The valid-stack memory-safety pattern fixture is compiled, never executed.

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::{
    mir::{BasicBlock, Body, Local, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind},
    ty::TyKind,
};

use super::{
    bridge_receipt::{BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, SignatureClassId},
    decision::{
        Decision,
        lifetime::FnSignatureSlot,
        outbound_expression::OutboundExpressionFailure,
        raw_boundary::{self, BridgeTemplate, RetentionVerdict},
        seam::{self, Form},
    },
};

const INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn target(p: *mut i32) -> *mut i32 {
        *p.offset(1) += 1;
        p
    }
    unsafe fn raw_alias(q: *const i32) -> *mut i32 {
        let _ = q.read();
        q.cast_mut()
    }
    pub unsafe fn caller() -> i32 {
        let mut values = [3_i32; 2048];
        let child = raw_alias(target(values.as_mut_ptr()));
        child.write(8);
        values[0]
    }
"#;

enum Observation {
    Guarded(String),
    Applied {
        selected: BridgeTemplate,
        required: BridgeTemplate,
        temporary: String,
    },
}

#[derive(Debug)]
struct CopyEvidence {
    definitions: BTreeMap<Local, usize>,
    copies: Vec<(Local, Local, BasicBlock, usize)>,
    descendants: BTreeSet<Local>,
}

fn unique_pointer_copies(body: &Body<'_>, root: Local) -> CopyEvidence {
    // Arguments have their compiler-declared entry definition. All subsequent
    // assignment and call definitions still count against unique identity.
    let mut definitions = body
        .args_iter()
        .map(|local| (local, 1usize))
        .collect::<BTreeMap<_, _>>();
    let mut copies = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let Some(to) = assignment.0.as_local() else { continue };
            *definitions.entry(to).or_insert(0usize) += 1;
            let Rvalue::Use(operand) = &assignment.1 else { continue };
            let Some(from) = operand.place().and_then(|place| place.as_local()) else { continue };
            if matches!(body.local_decls[from].ty.kind(), TyKind::RawPtr(..))
                && body.local_decls[from].ty == body.local_decls[to].ty
            {
                copies.push((from, to, block, index));
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && let Some(local) = destination.as_local()
        {
            *definitions.entry(local).or_insert(0usize) += 1;
        }
    }
    let mut descendants = if definitions.get(&root) == Some(&1) {
        BTreeSet::from([root])
    } else {
        BTreeSet::new()
    };
    loop {
        let before = descendants.len();
        for &(from, to, _, _) in &copies {
            if descendants.contains(&from) && definitions.get(&to) == Some(&1) {
                descendants.insert(to);
            }
        }
        if descendants.len() == before {
            break;
        }
    }
    CopyEvidence {
        definitions,
        copies,
        descendants,
    }
}

#[test]
fn outbound_alias_permission_local_const_alias_result_preserves_writable_view() {
    assert!(
        super::verify::type_checks_str(INPUT),
        "unchanged input type/borrow-checks"
    );
    let (emitted, observation) = ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original alias-permission AST");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one ordinary alias-permission fixture decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("OUTBOUND-ALIAS-PERMISSION solve={solve:#?}\nINPUT:\n{INPUT}");
        assert!(solve.is_some(), "actual fixture solve receipt is required");
        let (source, decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual native source parameter");
        let (alias, alias_decision) = table.entries.iter().find(|(subject, _)| subject.label == "raw_alias::q")
            .expect("actual local aliaser parameter");
        let (child, child_decision) = table.entries.iter().find(|(subject, _)| subject.label == "caller::child")
            .expect("actual raw returned child local");
        let model = |owner, local| ctx.slots.fn_local_slots.get(&owner)
            .and_then(|slots| slots.slot_for_local_depth(local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(owner, slot)));
        let permit = ctx.lifetime_eligibility.return_permit((source.fn_did, source.hir_id));
        let retention = ctx.retention.get(alias.fn_did, 0).expect("actual aliaser retention row");
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual alias-permission emission plan");
        let owner = SignatureClassId::of(source.fn_did);
        let held = emission.plan.held_classes();
        let alias_terminal = super::terminal_parameter_form(&table, &emission.plan.class_finalization, alias.fn_did, 0);
        println!("OUTBOUND-ALIAS-PERMISSION source model={:?}; return model={:?}; source={decision:#?}; alias={alias_decision:#?}; child={child_decision:#?}; native permit={permit:#?}; lifetime={:#?}; interface={:#?}; source hold={:?}; alias terminal={alias_terminal:?}; retention={retention:#?}; plans={:#?}; unavailable={:#?}",
            model(source.fn_did, source.local), model(source.fn_did, RETURN_PLACE),
            table.lifetime_plan.function(source.fn_did), table.return_interfaces.functions.get(&source.fn_did),
            emission.plan.class_hold_reason(owner), table.seams.outbound_expressions.plans,
            table.seams.outbound_expressions.unavailable);
        let body = tcx.mir_drops_elaborated_and_const_checked(child.fn_did).borrow();
        let alias_body = tcx.mir_drops_elaborated_and_const_checked(alias.fn_did).borrow();
        println!("OUTBOUND-ALIAS-PERMISSION ORIGINAL CALLER MIR:\n{body:#?}\nORIGINAL RAW_ALIAS MIR:\n{alias_body:#?}");
        for local in [source.local, RETURN_PLACE] {
            assert_eq!(model(source.fn_did, local), Some(&super::SlotKind::Ref),
                "authoring premise: actual native source/return model-Ref: {local:?}");
        }

        // Original MIR establishes a real pointer-returning local alias call,
        // the exact returned destination, and a later write through that child.
        let alias_calls = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
            let TerminatorKind::Call { func, destination, .. } = &data.terminator().kind else { return None };
            let TyKind::FnDef(callee, _) = *func.constant()?.ty().kind() else { return None };
            (callee == alias.fn_did.to_def_id()).then_some((block, data.statements.len(), *destination,
                data.terminator().source_info.span.source_callsite()))
        }).collect::<Vec<_>>();
        let [(alias_block, alias_statement, destination, alias_span)] = alias_calls.as_slice() else {
            panic!("one exact original raw_alias MIR call: {alias_calls:#?}")
        };
        assert_eq!(destination.as_local(), Some(child.local), "actual named child receives the alias result");
        // The compiler copies a method receiver to its own MIR temporary.
        // Follow only same-typed raw-pointer Use copies, and only when every
        // destination has exactly one definition. Call destinations count as
        // definitions too; a call result cannot masquerade as a unique copy.
        let child_copies = unique_pointer_copies(&body, child.local);
        let alias_copies = unique_pointer_copies(&alias_body, alias.local);
        println!("OUTBOUND-ALIAS-PERMISSION exact child-copy proof={child_copies:#?}; child edges={:?}; exact alias-parameter-copy proof={alias_copies:#?}; alias edges={:?}",
            child_copies.copies, alias_copies.copies);
        assert_eq!(child_copies.definitions.get(&child.local), Some(&1), "actual alias-call result is singly defined");
        let writes = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
            let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else { return None };
            let TyKind::FnDef(callee, _) = *func.constant()?.ty().kind() else { return None };
            let receiver = args.first().and_then(|argument| argument.node.place()).and_then(|place| place.as_local());
            (tcx.crate_name(callee.krate).as_str() == "core" && tcx.item_name(callee).as_str() == "write"
                && receiver.is_some_and(|local| child_copies.descendants.contains(&local) && child_copies.definitions.get(&local) == Some(&1)))
                .then_some((block, data.statements.len(), tcx.def_path_str(callee), receiver))
        }).collect::<Vec<_>>();
        assert_eq!(writes.len(), 1, "one actual core pointer write consumes the returned child: {writes:#?}");
        let casts = alias_body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
            let TerminatorKind::Call { func, args, destination, .. } = &data.terminator().kind else { return None };
            let TyKind::FnDef(callee, _) = *func.constant()?.ty().kind() else { return None };
            (tcx.crate_name(callee.krate).as_str() == "core" && tcx.item_name(callee).as_str() == "cast_mut")
                .then_some((block, data.statements.len(), tcx.def_path_str(callee),
                    args.first().and_then(|argument| argument.node.place()).and_then(|place| place.as_local()), *destination))
        }).collect::<Vec<_>>();
        println!("OUTBOUND-ALIAS-PERMISSION original alias call bb{:?}:s{alias_statement} span={alias_span:?}; destination={destination:?}; real child write={writes:#?}; original cast_mut calls={casts:#?}; alias MIR={alias_body:#?}", alias_block);
        let plans = table.seams.outbound_expressions.plans.values().filter(|plan|
            plan.source_callee == source.fn_did && plan.sink_callee == BridgeCalleeId::Local(alias.fn_did)
                && plan.caller == child.fn_did && plan.key.argument_index == 0).collect::<Vec<_>>();
        let unavailable = table.seams.outbound_expressions.unavailable.values().filter(|plan|
            plan.source_callee == source.fn_did && plan.sink_callee == BridgeCalleeId::Local(alias.fn_did)
                && plan.caller == child.fn_did && plan.key.argument_index == 0).collect::<Vec<_>>();
        let events = emission.plan.bridge_events(&held);
        let applied = events.iter().filter(|event| event.site.owner_class == owner
            && event.site.callee == BridgeCalleeId::Local(alias.fn_did)
            && event.site.bridge_kind == "outbound-native-return-argument"
            && event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Applied)
            .collect::<Vec<_>>();
        let observation = if matches!(retention, RetentionVerdict::Retains { .. }) {
            assert!(applied.is_empty(), "positive retention must not spend the T2 waiver");
            let reason = emission.plan.class_hold_reason(owner).or_else(|| {
                unavailable.iter().find(|row| row.reason == OutboundExpressionFailure::PositiveRetention)
                    .map(|row| format!("{:?}", row.reason))
            }).or_else(|| match decision {
                Decision::Degraded(record) => Some(format!("{:?}", record.reason)),
                _ => None,
            }).expect("a prevented native view has an attributed guard");
            Observation::Guarded(format!("positive-retention:{reason}"))
        } else if let Some(reason) = emission.plan.class_hold_reason(owner) {
            assert!(applied.is_empty());
            Observation::Guarded(format!("source-owner-held:{reason}"))
        } else if let Decision::Degraded(record) = decision
            && !table.return_interfaces.functions.contains_key(&source.fn_did)
        {
            assert!(applied.is_empty(), "the old typed source refusal cannot leave an Applied native-result view");
            assert!(plans.is_empty(), "a non-native source has no admitted native-result carrier");
            Observation::Guarded(format!("source-input-form:{:?}; native-return-interface-absent", record.reason))
        } else {
            assert_eq!(alias_terminal, Form::Raw, "authoring premise: local aliaser terminal parameter stays raw");
            assert!(permit.is_some(), "authoring premise: actual native return permit");
            assert!(matches!(decision, Decision::Slice { mutable: true, .. }), "authoring premise: actual source remains mutable Slice");
            assert!(emission.plan.class_finalization.classes.get(&owner).is_some_and(super::plan::SignatureClassPlan::is_ready));
            let interface = table.return_interfaces.functions.get(&source.fn_did).expect("actual borrowed return interface");
            assert_eq!(interface.form, Form::Slice { mutable: true });
            let function = table.lifetime_plan.function(source.fn_did).expect("actual native lifetime plan");
            assert_eq!(function.lifetime_for(FnSignatureSlot::RETURN), Some(interface.lifetime.as_str()));
            assert_eq!(function.digest(), interface.lifetime_plan_digest);
            assert!(matches!(retention, RetentionVerdict::Unknown { .. }),
                "the hypothesized admitted branch must carry its actual Unknown retention verdict: {retention:#?}");
            let [cast] = casts.as_slice() else { panic!("one actual unmodeled cast_mut call is the alias frontier: {casts:#?}") };
            assert!(cast.3.is_some_and(|local| alias_copies.descendants.contains(&local)
                && alias_copies.definitions.get(&local) == Some(&1)),
                "actual cast_mut receiver is q or a unique transparent q copy: {casts:#?}; {alias_copies:#?}");
            assert_eq!(cast.4.as_local(), Some(RETURN_PLACE));
            let [plan] = plans.as_slice() else { panic!("one exact admitted native-expression plan: {plans:#?}") };
            assert_eq!(applied.len(), 1, "admitted branch has one real terminal bridge");
            assert_eq!(plan.key.block, alias_block.as_u32());
            assert_eq!(plan.key.statement_index as usize, *alias_statement);
            assert_eq!(plan.call_span.source_callsite(), *alias_span);
            assert_eq!(tcx.sess.source_map().span_to_snippet(plan.argument_span).unwrap(), "target(values.as_mut_ptr())");
            assert_eq!(plan.key.subject, "<unrooted>");
            assert_eq!(plan.retention, *retention);
            let selected_source = seam::decision_for_safe_form(interface.form).expect("existing typed source-form selector");
            raw_boundary::returned_child_permission(&selected_source, None).expect("mutable source can preserve permission without invented read-only evidence");
            let required = raw_boundary::returned_child_template(&selected_source, &plan.target, None, plan.template)
                .expect("existing RB-RETALIAS writable-const carrier");
            println!("OUTBOUND-ALIAS-PERMISSION admitted plan={plan:#?}; existing required carrier={required:#?}; applied={applied:#?}");
            Observation::Applied { selected: plan.template, required: required.template, temporary: plan.temporary.clone() }
        };
        let (files, rollbacks, _, _, _) = super::round_files(tcx, &capture, &emission.plan,
            &emission.texts, &held, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table)
            .expect("full alias-permission emitted round");
        assert!(rollbacks.is_empty(), "the observed guard or carrier must own the complete rendering");
        assert_eq!(files.len(), 1);
        (files.into_values().next().unwrap(), observation)
    }).expect("original local-alias memory-safety pattern fixture compiles");
    assert!(
        super::verify::type_checks_str(&emitted),
        "complete alias-permission output type/borrow-checks:\n{emitted}"
    );
    println!("OUTBOUND-ALIAS-PERMISSION EMITTED:\n{emitted}");
    match observation {
        Observation::Guarded(reason) => {
            println!("OUTBOUND-ALIAS-PERMISSION G: {reason}; no applied native-result raw view")
        }
        Observation::Applied {
            selected,
            required,
            temporary,
        } => {
            assert!(
                emitted.contains(&temporary),
                "the observed Applied carrier has its rendered temporary"
            );
            assert_eq!(
                selected, required,
                "permission review: an admitted native mutable result with an actual raw-alias child write requires its existing writable-const carrier"
            );
            assert!(
                emitted.contains(".as_mut_ptr()") && emitted.contains(".cast_const()"),
                "the writable-const carrier must be rendered before the local raw alias call:\n{emitted}"
            );
        }
    }
}

/// The same shape with a shared native source. No writable view of the subject
/// exists at all, so the only permission-preserving disposition is a hold.
/// The input keeps mutable provenance (`as_mut_ptr().cast_const()`), so the
/// original program is UB-free and cannot discharge the obligation itself.
const SHARED_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn target(p: *const i32) -> *const i32 {
        let _ = *p.offset(1);
        p
    }
    unsafe fn raw_alias(q: *const i32) -> *mut i32 {
        let _ = q.read();
        q.cast_mut()
    }
    pub unsafe fn caller() -> i32 {
        let mut values = [3_i32; 2048];
        let child = raw_alias(target(values.as_mut_ptr().cast_const()));
        child.write(8);
        values[0]
    }
"#;

const TYPED_HOLD_REASON: &str = "outbound-alias-permission:write-through-shared-view";

#[test]
fn outbound_alias_permission_shared_source_written_child_holds_the_native_view() {
    assert!(
        super::verify::type_checks_str(SHARED_INPUT),
        "unchanged shared-source input type/borrow-checks"
    );
    let (emitted, hold) = ::utils::compilation::run_compiler_on_str(SHARED_INPUT, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original shared-source AST");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one ordinary shared-source alias-permission decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("OUTBOUND-ALIAS-PERMISSION-SHARED solve={solve:#?}\nINPUT:\n{SHARED_INPUT}");
        assert!(solve.is_some(), "actual fixture solve receipt is required");
        let (source, decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual native source parameter");
        let (alias, alias_decision) = table.entries.iter().find(|(subject, _)| subject.label == "raw_alias::q")
            .expect("actual local aliaser parameter");
        let (child, child_decision) = table.entries.iter().find(|(subject, _)| subject.label == "caller::child")
            .expect("actual raw returned child local");
        let model = |owner, local| ctx.slots.fn_local_slots.get(&owner)
            .and_then(|slots| slots.slot_for_local_depth(local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(owner, slot)));
        let permit = ctx.lifetime_eligibility.return_permit((source.fn_did, source.hir_id));
        let retention = ctx.retention.get(alias.fn_did, 0).expect("actual aliaser retention row");
        let interface = table.return_interfaces.functions.get(&source.fn_did).cloned();
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual shared-source emission plan");
        let owner = SignatureClassId::of(source.fn_did);
        let held = emission.plan.held_classes();
        let alias_terminal = super::terminal_parameter_form(&table, &emission.plan.class_finalization, alias.fn_did, 0);
        let hold_reason = emission.plan.class_hold_reason(owner);
        println!("OUTBOUND-ALIAS-PERMISSION-SHARED source model={:?}; return model={:?}; source={decision:#?}; alias={alias_decision:#?}; child={child_decision:#?}; native permit={permit:#?}; interface={interface:#?}; alias terminal={alias_terminal:?}; retention={retention:#?}; owner hold={hold_reason:?}; plans={:#?}; unavailable={:#?}",
            model(source.fn_did, source.local), model(source.fn_did, RETURN_PLACE),
            table.seams.outbound_expressions.plans, table.seams.outbound_expressions.unavailable);

        // Premise 1-2: the local aliaser's parameter stays raw and its
        // retention is Unknown, so nothing but permission can decide this site;
        // a Retains verdict would guard it for a different reason.
        //
        // The source's own shared safe form is RECORDED, not asserted, on the
        // final table. The refusal reaches it first: the additive ladder
        // withdraws the owner's family, so the settled decision is the recorded
        // fallback rather than the candidate shared form it refused.
        assert_eq!(alias_terminal, Form::Raw, "authoring premise: local aliaser terminal parameter stays raw");
        assert!(matches!(retention, RetentionVerdict::Unknown { .. }),
            "authoring premise: actual Unknown aliaser retention: {retention:#?}");

        // Premise 6: the returned child is really written.
        let body = tcx.mir_drops_elaborated_and_const_checked(child.fn_did).borrow();
        let child_copies = unique_pointer_copies(&body, child.local);
        let writes = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
            let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else { return None };
            let TyKind::FnDef(callee, _) = *func.constant()?.ty().kind() else { return None };
            let receiver = args.first().and_then(|argument| argument.node.place()).and_then(|place| place.as_local());
            (tcx.crate_name(callee.krate).as_str() == "core" && tcx.item_name(callee).as_str() == "write"
                && receiver.is_some_and(|local| child_copies.descendants.contains(&local)
                    && child_copies.definitions.get(&local) == Some(&1)))
                .then_some((block, data.statements.len(), tcx.def_path_str(callee), receiver))
        }).collect::<Vec<_>>();
        println!("OUTBOUND-ALIAS-PERMISSION-SHARED exact child-copy proof={child_copies:#?}; real child write={writes:#?}");
        assert_eq!(writes.len(), 1, "one actual core pointer write consumes the returned child: {writes:#?}");

        // The classification: a shared view may not carry a written child.
        let plans = table.seams.outbound_expressions.plans.values().filter(|plan|
            plan.source_callee == source.fn_did && plan.sink_callee == BridgeCalleeId::Local(alias.fn_did)
                && plan.caller == child.fn_did && plan.key.argument_index == 0).collect::<Vec<_>>();
        let rows = table.seams.outbound_expressions.unavailable.values().filter(|row|
            row.source_callee == source.fn_did && row.sink_callee == BridgeCalleeId::Local(alias.fn_did)
                && row.caller == child.fn_did && row.key.argument_index == 0)
            .map(|row| format!("{:?}", row.reason)).collect::<Vec<_>>();
        let events = emission.plan.bridge_events(&held);
        let applied = events.iter().filter(|event| event.site.owner_class == owner
            && event.site.callee == BridgeCalleeId::Local(alias.fn_did)
            && event.site.bridge_kind == "outbound-native-return-argument"
            && event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Applied)
            .collect::<Vec<_>>();
        let fallbacks = ctx.raw_boundary_artifacts.additive_family_receipts.iter()
            .filter(|receipt| receipt.cause.contains(TYPED_HOLD_REASON)).collect::<Vec<_>>();
        println!("OUTBOUND-ALIAS-PERMISSION-SHARED unavailable rows={rows:#?}; typed refusals={fallbacks:#?}; every additive fallback={:#?}",
            ctx.raw_boundary_artifacts.additive_family_receipts);
        assert!(plans.is_empty(),
            "a shared native view cannot be admitted at a writing raw position: {plans:#?}");
        assert!(applied.is_empty(), "a refused shared view leaves no Applied terminal bridge: {applied:#?}");
        // The typed reason reaches the ledger: the dropped class site carries
        // it verbatim, and it is the recorded cause of the owner's withdrawal.
        let [fallback] = fallbacks.as_slice() else {
            panic!("one exact typed outbound-alias-permission refusal: {:#?}",
                ctx.raw_boundary_artifacts.additive_family_receipts)
        };
        assert_eq!(fallback.owner_local_def_id, SignatureClassId::of(source.fn_did).order_key(),
            "the refusal is attributed to the native source's own class: {fallback:#?}");
        assert!(matches!(decision, Decision::Degraded(_)),
            "a refused shared source keeps no native form: {decision:#?}");
        let hold = format!("{}; source={:?}; owner-hold={hold_reason:?}", fallback.cause,
            match decision { Decision::Degraded(record) => Some(format!("{:?}", record.reason)), _ => None });
        let (files, rollbacks, _, _, _) = super::round_files(tcx, &capture, &emission.plan,
            &emission.texts, &held, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table)
            .expect("full shared-source emitted round");
        assert!(rollbacks.is_empty(), "the observed hold must own the complete rendering");
        assert_eq!(files.len(), 1);
        (files.into_values().next().unwrap(), hold)
    }).expect("original shared-source memory-safety pattern fixture compiles");
    assert!(
        super::verify::type_checks_str(&emitted),
        "complete shared-source output type/borrow-checks:\n{emitted}"
    );
    println!("OUTBOUND-ALIAS-PERMISSION-SHARED EMITTED:\n{emitted}");
    assert!(
        !emitted.contains("__crat_outbound_return_"),
        "no outbound native view is rendered for a held shared subject:\n{emitted}"
    );
    println!("OUTBOUND-ALIAS-PERMISSION-SHARED G: {hold}; no applied native-result raw view");
}

/// A sink that returns a scalar cannot return a child at all, so the ordinary
/// outgoing view stands and no writable carrier is manufactured for it.
const SCALAR_SINK_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn target(p: *mut i32) -> *mut i32 {
        *p.offset(1) += 1;
        p
    }
    unsafe fn raw_scalar(q: *const i32) -> i32 {
        q.read()
    }
    pub unsafe fn caller() -> i32 {
        let mut values = [3_i32; 2048];
        raw_scalar(target(values.as_mut_ptr()))
    }
"#;

/// A sink that returns an aggregate holding a raw pointer CAN return a child.
/// The field walk finds it, so this site takes the same carrier as a directly
/// pointer-returning sink.
const STRUCT_SINK_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub struct Holder {
        pub first: *mut i32,
    }
    unsafe fn target(p: *mut i32) -> *mut i32 {
        *p.offset(1) += 1;
        p
    }
    unsafe fn raw_holder(q: *const i32) -> Holder {
        let _ = q.read();
        Holder { first: q.cast_mut() }
    }
    pub unsafe fn caller() -> i32 {
        let mut values = [3_i32; 2048];
        let holder = raw_holder(target(values.as_mut_ptr()));
        holder.first.write(8);
        values[0]
    }
"#;

/// A sink that returns a pointer-width integer CAN return a child: the caller
/// reconstructs a pointer from the address and writes through it, and under
/// exposed-provenance semantics that reconstructed pointer inherits the
/// permission the outgoing view created. A shared `as_ptr()` view would make
/// the write UB on a UB-free input, so this shape is a carrier
/// (§39 addendum 256(2)).
const POINTER_WIDTH_INT_SINK_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn target(p: *mut i32) -> *mut i32 {
        *p.offset(1) += 1;
        p
    }
    unsafe fn raw_addr(q: *const i32) -> usize {
        q.read() as usize
    }
    pub unsafe fn caller() -> usize {
        let mut values = [3_i32; 2048];
        raw_addr(target(values.as_mut_ptr()))
    }
"#;

/// The premises the two return-shape controls share, plus the carrier that the
/// outbound expression planner actually selected for the one native site.
fn outbound_carrier(input: &'static str, sink: &str) -> (String, Option<BridgeTemplate>, String) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original return-shape AST");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("one ordinary return-shape decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("OUTBOUND-RETURN-SHAPE[{sink}] solve={solve:#?}\nINPUT:\n{input}");
        assert!(solve.is_some(), "actual fixture solve receipt is required");
        let (source, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.label == "target::p")
            .expect("actual native source parameter");
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("actual return-shape emission plan");
        let held = emission.plan.held_classes();
        let plans = table
            .seams
            .outbound_expressions
            .plans
            .values()
            .filter(|plan| plan.source_callee == source.fn_did)
            .collect::<Vec<_>>();
        println!(
            "OUTBOUND-RETURN-SHAPE[{sink}] source={decision:#?}; plans={plans:#?}; unavailable={:#?}; hold={:?}",
            table.seams.outbound_expressions.unavailable,
            emission.plan.class_hold_reason(SignatureClassId::of(source.fn_did))
        );
        assert!(
            matches!(decision, Decision::Slice { mutable: true, .. }),
            "authoring premise: actual mutable Slice source: {decision:#?}"
        );
        let carrier = match plans.as_slice() {
            [plan] => Some(plan.template),
            [] => None,
            _ => panic!("at most one native outbound site: {plans:#?}"),
        };
        let (files, rollbacks, _, _, _) = super::round_files(
            tcx,
            &capture,
            &emission.plan,
            &emission.texts,
            &held,
            &BTreeSet::new(),
            emission.plan.root_file.as_ref(),
            &table,
        )
        .expect("full return-shape emitted round");
        assert!(rollbacks.is_empty(), "the selected carrier owns the complete rendering");
        assert_eq!(files.len(), 1);
        (
            files.into_values().next().unwrap(),
            carrier,
            format!("{:?}", table.seams.outbound_expressions.unavailable.values().map(|row| format!("{:?}", row.reason)).collect::<Vec<_>>()),
        )
    })
    .expect("original return-shape memory-safety pattern fixture compiles")
}

#[test]
fn outbound_alias_permission_scalar_returning_sink_keeps_the_ordinary_view() {
    assert!(
        super::verify::type_checks_str(SCALAR_SINK_INPUT),
        "unchanged scalar-sink input type/borrow-checks"
    );
    let (emitted, carrier, unavailable) = outbound_carrier(SCALAR_SINK_INPUT, "raw_scalar -> i32");
    println!(
        "OUTBOUND-RETURN-SHAPE[raw_scalar -> i32] EMITTED:\n{emitted}\nunavailable={unavailable}"
    );
    assert!(
        super::verify::type_checks_str(&emitted),
        "complete scalar-sink output type/borrow-checks:\n{emitted}"
    );
    assert_eq!(
        carrier,
        Some(BridgeTemplate::SliceToRawConst),
        "a sink that cannot return a child keeps the ordinary shared view: {unavailable}"
    );
    assert!(
        emitted.contains(".as_ptr()") && !emitted.contains(".as_mut_ptr().cast::<i32>()"),
        "no writable carrier is manufactured where no child can exist:\n{emitted}"
    );
}

/// §39 addendum 256(2) — the adversarial-review HIGH residual. A sink whose
/// return type is an integer at least as wide as the target pointer can hand
/// the caller a reconstructable address, so it is a returned-child carrier and
/// its outgoing view must be the writable one. Narrower integers stay
/// non-carriers; `raw_scalar -> i32` above is that contrast, and it also holds
/// the pinned-parser custody correspondence the addendum-254 gate protects.
#[test]
fn outbound_alias_permission_pointer_width_integer_return_takes_the_writable_carrier() {
    assert!(
        super::verify::type_checks_str(POINTER_WIDTH_INT_SINK_INPUT),
        "unchanged pointer-width-integer-sink input type/borrow-checks"
    );
    let (emitted, carrier, unavailable) =
        outbound_carrier(POINTER_WIDTH_INT_SINK_INPUT, "raw_addr -> usize");
    println!(
        "OUTBOUND-RETURN-SHAPE[raw_addr -> usize] EMITTED:\n{emitted}\nunavailable={unavailable}"
    );
    assert!(
        super::verify::type_checks_str(&emitted),
        "complete pointer-width-integer-sink output type/borrow-checks:\n{emitted}"
    );
    assert_eq!(
        carrier,
        Some(BridgeTemplate::SliceMutToWritableRawConst),
        "an integer return at least as wide as the target pointer can carry a \
         reconstructable address, so it reaches the writable carrier: {unavailable}"
    );
    assert!(
        emitted.contains(".as_mut_ptr().cast::<i32>().cast_const()"),
        "the writable carrier must actually render:\n{emitted}"
    );
}

#[test]
fn outbound_alias_permission_pointer_field_return_takes_the_writable_carrier() {
    assert!(
        super::verify::type_checks_str(STRUCT_SINK_INPUT),
        "unchanged struct-sink input type/borrow-checks"
    );
    let (emitted, carrier, unavailable) =
        outbound_carrier(STRUCT_SINK_INPUT, "raw_holder -> Holder");
    println!(
        "OUTBOUND-RETURN-SHAPE[raw_holder -> Holder] EMITTED:\n{emitted}\nunavailable={unavailable}"
    );
    assert!(
        super::verify::type_checks_str(&emitted),
        "complete struct-sink output type/borrow-checks:\n{emitted}"
    );
    assert_eq!(
        carrier,
        Some(BridgeTemplate::SliceMutToWritableRawConst),
        "an aggregate return holding a raw pointer reaches the writable carrier: {unavailable}"
    );
    assert!(
        emitted.contains(".as_mut_ptr().cast::<i32>().cast_const()"),
        "the writable carrier is rendered before the aggregate-returning sink:\n{emitted}"
    );
}
