//! Actual ordinary-call target/source input-form combinations. No decision,
//! model, atom, or retention evidence is synthesized by these controls.

use std::collections::BTreeSet;

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptEvent, BridgeReceiptStage, BridgeReceiptState,
        BridgeRetentionTier, BridgeSiteKey, RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
    },
    decision::{Decision, raw_boundary::RetentionVerdict},
    delivery_custody::{TypeShape, inventory_source},
};

const INPUT: &str = "#![allow(dead_code, unused_unsafe)]\n\
    extern \"C\" { fn strlen(p: *const i8) -> usize; }\n\
    unsafe fn target(p: *mut i8) -> i8 { *p.offset(1) += 1; let _ = strlen(p); *p }\n\
    unsafe fn caller(q: *mut i8) -> i8 { target(q) }\n\
    pub unsafe fn entry() -> i8 {\n\
        let mut storage: [i8; 3] = [65, 66, 0]; caller(storage.as_mut_ptr())\n\
    }\n";

struct Output {
    source: String,
    events: Vec<BridgeReceiptEvent>,
    old_call: BridgeSiteKey,
    strlen: BridgeSiteKey,
    caller: SignatureClassId,
    target: SignatureClassId,
    effective: BTreeSet<SignatureClassId>,
    expected_retention: BridgeRetentionTier,
}

fn terminal<'a>(events: &'a [BridgeReceiptEvent], key: &BridgeSiteKey) -> &'a BridgeReceiptEvent {
    let matches = events
        .iter()
        .filter(|event| &event.site == key && event.stage == BridgeReceiptStage::Terminal)
        .collect::<Vec<_>>();
    let [event] = matches.as_slice() else {
        panic!("one exact terminal fate for {key:?}: {matches:#?}")
    };
    event
}

fn check(target_input: bool, source_input: bool) {
    let output = ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original ordinary-call AST");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one actual ordinary-call decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("CALLEE-INPUT target_input={target_input}, source_input={source_input}: solve={solve:#?}");
        assert!(solve.is_some(), "actual fresh-harness solve receipt is required");
        let (p, p_decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual target parameter p");
        let (q, q_decision) = table.entries.iter().find(|(subject, _)| subject.label == "caller::q")
            .expect("actual caller parameter q");
        for (subject, decision) in [(p, p_decision), (q, q_decision)] {
            let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
                .and_then(|slots| slots.slot_for_local_depth(subject.local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)));
            assert_eq!(kind, Some(&super::SlotKind::Ref), "AUTHORING PREMISE: actual model-Ref: {}", subject.label);
            assert!(if subject.fn_did == p.fn_did {
                matches!(decision, Decision::Slice { mutable: true, .. })
            } else {
                matches!(decision, Decision::Ref { mutable: true })
            }, "AUTHORING PREMISE: actual target Slice and caller Ref: {}, {decision:?}", subject.label);
        }
        let target = SignatureClassId::of(p.fn_did);
        let caller = SignatureClassId::of(q.fn_did);
        assert_ne!(target, caller, "distinct real caller and callee classes");
        let retention = ctx.retention.get(p.fn_did, 0).expect("native target argument retention row");
        println!("CALLEE-INPUT native target retention={retention:#?}");
        let expected_retention = match retention {
            RetentionVerdict::NoRetain { certificate } => {
                ctx.retention.verify_certificate(p.fn_did, 0, certificate).expect("actual native NoRetain certificate replays");
                BridgeRetentionTier::T1
            }
            RetentionVerdict::Unknown { .. } => BridgeRetentionTier::T2,
            RetentionVerdict::Retains { .. } => panic!(
                "AUTHORING PREMISE: positive retention cannot witness an admitted raw view: {retention:?}"),
        };
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual ordinary-call terminal plan");
        let held = emission.plan.held_classes();
        for owner in [target, caller] {
            assert!(emission.plan.class_finalization.classes.get(&owner)
                .is_some_and(super::plan::SignatureClassPlan::is_ready),
                "AUTHORING PREMISE: both original classes Ready: {:?}", emission.plan.class_finalization);
            assert!(!held.contains(&owner));
        }
        let p_node = (p.fn_did, p.hir_id);
        let q_node = (q.fn_did, q.hir_id);
        let strlen_sites = emission.plan.terminal_call_plans.seam_edits.iter().filter(|edit|
            edit.source_node == Some(p_node) && edit.raw_outbound.is_some()
                && edit.bridge.callee == BridgeCalleeId::Foreign("strlen".into())).collect::<Vec<_>>();
        let [strlen_site] = strlen_sites.as_slice() else { panic!("AUTHORING PREMISE: one actual p→strlen site") };
        assert_eq!(strlen_site.bridge.retention, BridgeRetentionTier::T1);
        assert!(strlen_site.bridge.waiver_id.is_none());
        let [p_atom] = strlen_site.atom_ids.as_slice() else { panic!("AUTHORING PREMISE: one actual p/strlen T1 atom") };
        assert!(table.seams.raw_boundary_atom_groups.get(&p_node).into_iter().flatten().any(|atom| &atom.id == p_atom));
        assert!(!table.seams.raw_boundary_atom_groups.get(&q_node).into_iter().flatten().any(|atom| &atom.id == p_atom),
            "the selected p atom must not directly retire q");
        let calls = ctx.facts.call_args[&p.fn_did].iter().filter(|call| call.caller == q.fn_did).collect::<Vec<_>>();
        let [call] = calls.as_slice() else { panic!("one actual caller→target call") };
        let argument = call.args.iter().find(|argument| argument.index == 0).expect("exact target argument zero");
        assert_eq!(argument.shape.place_root(), Some(q.hir_id));
        let input_key = (target, argument.span.lo().0, argument.span.hi().0);
        let input_plan = emission.plan.terminal_call_plans.callee_parameter_inputs.get(&input_key)
            .expect("the exact ordinary target-input alternative is inventoried");
        println!("CALLEE-INPUT p_atom={p_atom}; current_source={:#?}; input_source={:#?}",
            input_plan.current_source, input_plan.input_source);
        let file_for = |span: rustc_span::Span| {
            let source = tcx.sess.source_map().lookup_source_file(span.lo());
            let file = match super::file_key(&source.name).unwrap() {
                super::plan::FileKey::Real(path) => path.display().to_string(),
                super::plan::FileKey::Virtual(name) => name,
            };
            (file, span.lo().0 - source.start_pos.0, span.hi().0 - source.start_pos.0)
        };
        let (file, lo, hi) = file_for(argument.span);
        let baseline = emission.plan.bridge_events(&held);
        let old_calls = baseline.iter().filter(|event| event.stage == BridgeReceiptStage::Terminal
            && event.site.owner_class == target && event.site.caller == q.fn_did
            && event.site.callee == BridgeCalleeId::Local(p.fn_did) && event.site.position == "arg0"
            && event.site.file == file && event.site.lo == lo && event.site.hi == hi).collect::<Vec<_>>();
        let [old_call] = old_calls.as_slice() else { panic!("one exact baseline ordinary C/glue receipt: {old_calls:#?}") };
        assert_eq!(old_call.state, BridgeReceiptState::Applied);
        let (strlen_file, strlen_lo, strlen_hi) = file_for(strlen_site.span);
        let strlen = strlen_site.bridge.materialize(target, strlen_file, strlen_lo, strlen_hi);
        assert_eq!(terminal(&baseline, &strlen).state, BridgeReceiptState::Applied);
        let mut selected_classes = held.clone();
        if source_input { selected_classes.insert(caller); }
        let atoms = if target_input { BTreeSet::from([p_atom.clone()]) } else { BTreeSet::new() };
        let effective = emission.plan.effective_reverted_classes(&selected_classes, &atoms);
        let (files, rollbacks, _, _) = super::round_files(tcx, &capture, &emission.plan,
            &emission.texts, &selected_classes, &atoms, emission.plan.root_file.as_ref(), &table)
            .expect("actual selected ordinary-call emission");
        assert!(rollbacks.is_empty(), "the fixture must not hide a structural rollback");
        assert_eq!(files.len(), 1);
        let source = files.into_values().next().unwrap();
        let events = emission.plan.bridge_events_with_atoms(&selected_classes, &atoms);
        println!("CALLEE-INPUT target_input={target_input}, source_input={source_input}: effective={effective:?}; events={events:#?}\n{source}");
        Output { source, events, old_call: old_call.site.clone(), strlen, caller, target, effective, expected_retention }
    }).expect("owned NUL-array ordinary-call fixture compiles");
    assert!(
        super::verify::type_checks_str(&output.source),
        "selected output type/borrow-checks:\n{}",
        output.source
    );
    assert!(
        !output.effective.contains(&output.target),
        "a nonreturn p atom must not retire its whole target class"
    );
    assert_eq!(
        output.effective.contains(&output.caller),
        source_input,
        "retiring only the target p atom must keep the independently admitted q source"
    );
    let declarations = inventory_source("callee-input.rs", &output.source)
        .expect("actual final declaration inventory");
    for (owner, binding, raw) in [("target", "p", target_input), ("caller", "q", source_input)] {
        let declaration = declarations
            .iter()
            .find(|row| {
                row.owner == owner && row.binding == binding && row.parameter_index == Some(1)
            })
            .expect("exact final source parameter");
        assert!(
            if raw {
                matches!(
                    &declaration.type_shape,
                    TypeShape::RawPointer { mutable: true, .. }
                )
            } else {
                matches!(&declaration.type_shape, TypeShape::Reference { mutable: true, pointee }
                if (owner == "target") == matches!(pointee.as_ref(), TypeShape::Slice { .. }))
            },
            "actual terminal {owner}::{binding} form: {declaration:?}"
        );
    }
    assert_eq!(
        terminal(&output.events, &output.strlen).state,
        if target_input {
            BridgeReceiptState::Dropped
        } else {
            BridgeReceiptState::Applied
        }
    );
    let old = terminal(&output.events, &output.old_call);
    if !target_input && !source_input {
        assert_eq!(old.state, BridgeReceiptState::Applied);
        assert_eq!(old.expected_form, "slice-mut");
        assert_eq!(old.found_form, "ref-mut");
        return;
    }
    assert_eq!(
        old.state,
        BridgeReceiptState::Dropped,
        "the obsolete safe/safe adapter identity must be withdrawn"
    );
    let replacements = output
        .events
        .iter()
        .filter(|event| {
            event.stage == BridgeReceiptStage::Terminal
                && event.state == BridgeReceiptState::Applied
                && event.site != output.old_call
                && event.site.caller == output.old_call.caller
                && event.site.callee == output.old_call.callee
                && event.site.position == "arg0"
                && event.site.file == output.old_call.file
                && event.site.lo == output.old_call.lo
                && event.site.hi == output.old_call.hi
        })
        .collect::<Vec<_>>();
    if target_input && source_input {
        assert!(
            replacements.is_empty(),
            "raw/raw identity needs no invented borrowed bridge: {replacements:#?}"
        );
    } else {
        let [replacement] = replacements.as_slice() else {
            panic!("one exact selected boundary bridge: {replacements:#?}")
        };
        assert_eq!(
            replacement.site.owner_class,
            if target_input {
                output.caller
            } else {
                output.target
            }
        );
        assert_eq!(
            replacement.expected_form,
            if target_input { "raw" } else { "slice-mut" }
        );
        assert_eq!(
            replacement.found_form,
            if source_input { "raw" } else { "ref-mut" }
        );
        assert_eq!(replacement.retention, output.expected_retention);
        assert_eq!(
            replacement.waiver_id.as_deref(),
            (output.expected_retention == BridgeRetentionTier::T2)
                .then_some(RAW_BOUNDARY_T2_WAIVER_ID)
        );
        if target_input {
            assert!(
                output.source.contains("ptr::from_mut(&mut *q)"),
                "the kept reference source must have its explicit outbound view"
            );
        }
    }
}

#[test]
fn callee_input_target_kept_source_kept() {
    check(false, false);
}

#[test]
fn callee_input_target_atom_keeps_safe_source() {
    check(true, false);
}

#[test]
fn callee_input_source_class_reverted_keeps_target() {
    check(false, true);
}

#[test]
fn callee_input_target_atom_and_source_class_reverted() {
    check(true, true);
}
