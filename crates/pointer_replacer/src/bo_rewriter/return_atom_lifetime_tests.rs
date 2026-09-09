//! J17/J18 actual-premise control for an atom-reverted return-origin parameter.
//! One unchanged model/decision invocation; only the production revert set varies.

use std::collections::BTreeSet;

use rustc_ast as ast;
use rustc_ast_pretty::pprust;
use rustc_middle::mir::RETURN_PLACE;
use rustc_session::parse::ParseSess;
use rustc_span::edition::Edition;

use super::{
    bridge_receipt::{
        BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier, SignatureClassId,
    },
    decision::{Decision, lifetime::FnSignatureSlot},
    delivery_custody::{TypeShape, inventory_source},
};

// Both callees receive caller-owned live storage. strlen sees an initialized
// NUL-terminated two-byte buffer, and the chosen byte is read before scope exit.
const INPUT: &str = "#![allow(dead_code, unused_unsafe)]\n\
    extern \"C\" { fn strlen(p: *const i8) -> usize; }\n\
    unsafe fn choose(p: *const i8) -> *const i8 { let _ = strlen(p); p }\n\
    unsafe fn independent(q: *const i8) -> i8 { *q }\n\
    pub unsafe fn entry() -> i8 {\n\
        let storage: [i8; 2] = [7, 0]; let separate: i8 = 3;\n\
        *choose(storage.as_ptr()) + independent(&separate)\n\
    }\n";

fn choose_return(source: &str) -> (bool, String) {
    rustc_span::create_session_globals_then(Edition::Edition2018, &[], None, || {
        let session = ParseSess::new(rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec());
        let krate =
            super::slice_use_inventory_tests::parse_crate(&session, "return-atom.rs", source)
                .expect("actual emitted signature parses");
        let functions = krate
            .items
            .iter()
            .filter_map(|item| {
                let ast::ItemKind::Fn(function) = &item.kind else { return None };
                (function.ident.name.as_str() == "choose").then_some(function)
            })
            .collect::<Vec<_>>();
        let [function] = functions.as_slice() else { panic!("one actual choose definition") };
        let ast::FnRetTy::Ty(output) = &function.sig.decl.output else {
            panic!("explicit choose return")
        };
        let mut ty = &**output;
        while let ast::TyKind::Paren(inner) = &ty.kind {
            ty = inner;
        }
        (
            matches!(ty.kind, ast::TyKind::Ref(..)),
            pprust::ty_to_string(output),
        )
    })
}

fn require_parameter(source: &str, owner: &str, binding: &str, raw: bool) {
    let declarations = inventory_source("return-atom-parameters.rs", source)
        .expect("actual declaration inventory");
    let matching = declarations
        .iter()
        .filter(|row| {
            row.owner == owner && row.binding == binding && row.parameter_index == Some(1)
        })
        .collect::<Vec<_>>();
    let [declaration] = matching.as_slice() else { panic!("one {owner}::{binding} parameter") };
    assert!(
        matches!(&declaration.type_shape,
        TypeShape::RawPointer { mutable: false, .. } if raw)
            || matches!(&declaration.type_shape, TypeShape::Reference { mutable: false, .. } if !raw),
        "actual {owner}::{binding} declaration: {declaration:?}"
    );
}

#[test]
fn return_atom_lifetime_revert_cannot_leave_a_return_only_generated_borrow() {
    let (baseline, atom_output, strlen_state, return_state, independent_applied) =
        ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
            let capture = super::ast_transform::capture_ast(tcx).expect("one original AST capture");
            let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
                super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            ))).expect("one actual return-atom decision invocation");
            let solve = super::model_cache::solve_receipt();
            println!("J17/J18 return-atom fixture solve receipt: {solve:#?}");
            assert!(solve.is_some(), "AUTHORING PREMISE: actual solve receipt");
            let (subject, choice) = table.entries.iter().find(|(subject, _)| subject.label == "choose::p")
                .expect("actual choose parameter subject");
            assert!(matches!(choice, Decision::Ref { mutable: false }),
                "AUTHORING PREMISE: actual choose parameter must be shared Ref: {choice:?}");
            for local in [subject.local, RETURN_PLACE] {
                let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
                    .and_then(|slots| slots.slot_for_local_depth(local, 0))
                    .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)));
                assert_eq!(kind, Some(&super::SlotKind::Ref),
                    "AUTHORING PREMISE: source and return are actual model-Ref: {local:?}");
            }
            let node = (subject.fn_did, subject.hir_id);
            let permit = ctx.lifetime_eligibility.return_permit(node)
                .expect("AUTHORING PREMISE: exact native return permit");
            let flow = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
                .and_then(|flows| flows.get(&subject.fn_did)).expect("native original-input flow");
            use crate::analyses::borrow_ownership::slots::SlotOwner;
            assert!(flow.body.depth0_value_flows().contains(&(
                SlotOwner::Local(subject.local), SlotOwner::Local(RETURN_PLACE))),
                "AUTHORING PREMISE: the same source reaches the original return slot");
            let lifetime_plan = table.lifetime_plan.function(subject.fn_did)
                .expect("AUTHORING PREMISE: actual lifetime plan");
            let lifetime = lifetime_plan.lifetime_for(FnSignatureSlot::arg(1, 0, 0))
                .expect("source parameter lifetime");
            assert_eq!(lifetime_plan.lifetime_for(FnSignatureSlot::RETURN), Some(lifetime));
            println!("J17/J18 permit={permit:?}; lifetime={}", lifetime_plan.receipt());

            let (independent, independent_choice) = table.entries.iter()
                .find(|(subject, _)| subject.label == "independent::q").expect("independent parameter");
            assert!(matches!(independent_choice, Decision::Ref { mutable: false }),
                "AUTHORING PREMISE: actual independent Ref: {independent_choice:?}");
            let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
                .expect("actual return-atom terminal plan");
            let owner = SignatureClassId::of(subject.fn_did);
            let other = SignatureClassId::of(independent.fn_did);
            assert_ne!(owner, other);
            let held = emission.plan.held_classes();
            for class in [owner, other] {
                assert!(emission.plan.class_finalization.classes.get(&class)
                    .is_some_and(super::plan::SignatureClassPlan::is_ready),
                    "AUTHORING PREMISE: both real classes Ready: {:?}", emission.plan.class_finalization);
                assert!(!held.contains(&class));
            }
            let strlen = emission.plan.terminal_call_plans.seam_edits.iter().filter(|edit|
                edit.source_node == Some(node) && edit.raw_outbound.is_some()
                    && edit.bridge.callee == super::bridge_receipt::BridgeCalleeId::Foreign("strlen".into()))
                .collect::<Vec<_>>();
            let [strlen] = strlen.as_slice() else { panic!("AUTHORING PREMISE: one real strlen source seam") };
            assert_eq!(strlen.bridge.retention, BridgeRetentionTier::T1);
            assert!(strlen.bridge.waiver_id.is_none());
            let [atom] = strlen.atom_ids.as_slice() else { panic!("AUTHORING PREMISE: one exact T1 source atom") };
            let atoms = BTreeSet::from([atom.clone()]);
            let source_atoms = table.seams.raw_boundary_atom_groups.get(&node).expect("real source atom group");
            assert!(source_atoms.iter().any(|candidate| candidate.id == *atom));
            let original_events = emission.plan.bridge_events_with_atoms(&held, &BTreeSet::new());
            let returns = original_events.iter().filter(|event| event.site.owner_class == owner
                && event.stage == BridgeReceiptStage::Terminal && event.site.bridge_kind == "return-raw-to-ref")
                .collect::<Vec<_>>();
            let [returned] = returns.as_slice() else { panic!("one exact return terminal receipt") };
            assert_eq!(returned.state, BridgeReceiptState::Applied);
            let return_key = returned.site.clone();
            let source_file = tcx.sess.source_map().lookup_source_file(strlen.span.lo());
            let file = super::file_key(&source_file.name).expect("real strlen file");
            let strlen_key = strlen.bridge.materialize(owner, super::bridge_custody_export::file_label(&file),
                strlen.span.lo().0 - source_file.start_pos.0, strlen.span.hi().0 - source_file.start_pos.0);
            let render = |atoms: &BTreeSet<String>| {
                let reverts = super::ast_transform::revert_set_from_classes_and_atoms(&held, atoms, &table)
                    .expect("production atom revert closure");
                assert!(reverts.keeps_subject(independent.fn_did, independent.hir_id));
                if !atoms.is_empty() { assert!(!reverts.keeps_subject(subject.fn_did, subject.hir_id)); }
                let (files, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
                    emission.plan.root_file.as_ref(), &table, Some(&emission.plan.terminal_call_plans))
                    .expect("actual atom-filtered AST render");
                assert_eq!(files.len(), 1);
                files.into_values().next().unwrap()
            };
            let baseline = render(&BTreeSet::new());
            // Exercise the production round boundary, including normalization
            // before its revert-all check. The legacy AST-only None-plan path
            // has a smaller dependency inventory and is not this control.
            let (atom_files, atom_rollbacks, _, _) = super::round_files(tcx, &capture,
                &emission.plan, &emission.texts, &held, &atoms,
                emission.plan.root_file.as_ref(), &table).expect("production atom round render");
            assert!(atom_rollbacks.is_empty(), "atom recovery has no unowned/residual rollback");
            assert_eq!(atom_files.len(), 1);
            let atom_output = atom_files.into_values().next().unwrap();

            let original_files = std::collections::BTreeMap::from([(file.clone(), INPUT.to_owned())]);
            let mut artifacts = super::RawBoundaryArtifacts {
                bridge_custody_export: super::bridge_custody_export::capture(
                    tcx, &capture, &table, &emission.plan, &original_files),
                ..Default::default()
            };
            super::refresh_raw_boundary_receipt_events(&mut artifacts, &emission.plan,
                &held, &BTreeSet::new());
            let baseline_unsafe = artifacts.unsafe_context_events.iter().filter(|event|
                event.site == return_key && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            let [unsafe_return] = baseline_unsafe.as_slice() else { panic!("real return unsafe-context receipt") };
            assert_eq!(unsafe_return.state, BridgeReceiptState::Applied);
            assert!(artifacts.bridge_events.iter().any(|event| event.site == return_key
                && event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Applied));
            // Pass the original held set, so refresh itself must apply the
            // atom-to-return-owner closure for every receipt family it owns.
            super::refresh_raw_boundary_receipt_events(&mut artifacts, &emission.plan, &held, &atoms);
            let refreshed_return = artifacts.bridge_events.iter().filter(|event|
                event.site == return_key && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            let [refreshed_return] = refreshed_return.as_slice() else { panic!("same exact refreshed return receipt") };
            assert_eq!(refreshed_return.state, BridgeReceiptState::Dropped);
            assert_eq!(refreshed_return.drop_reason.as_deref(), Some("return-origin-atom-reverted"));
            let refreshed_unsafe = artifacts.unsafe_context_events.iter().filter(|event|
                event.site == return_key && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            let [refreshed_unsafe] = refreshed_unsafe.as_slice() else { panic!("same exact refreshed unsafe-context receipt") };
            assert_eq!(refreshed_unsafe.state, BridgeReceiptState::Dropped);
            let independent_refreshed = artifacts.bridge_events.iter().filter(|event|
                event.site.owner_class == other && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            assert!(!independent_refreshed.is_empty());
            assert!(independent_refreshed.iter().all(|event| event.state == BridgeReceiptState::Applied));

            let effective = emission.plan.effective_reverted_classes(&held, &atoms);
            let paths = emission.plan.class_finalization.classes.keys().map(|owner|
                (*owner, tcx.def_path_str(owner.local_def_id().to_def_id()))).collect();
            artifacts.final_reverts = super::render_raw_boundary_final_reverts(&effective, &atoms, &paths);
            let rows = artifacts.final_reverts.lines().skip(1)
                .map(|line| line.split('\t').collect::<Vec<_>>()).collect::<Vec<_>>();
            let choose_name = tcx.def_path_str(subject.fn_did.to_def_id());
            let independent_name = tcx.def_path_str(independent.fn_did.to_def_id());
            assert_eq!(rows.iter().filter(|row| row.as_slice() == ["function", choose_name.as_str(),
                format!("local-def-index:{}", owner.order_key()).as_str()]).count(), 1);
            assert_eq!(rows.iter().filter(|row| row.as_slice() == ["atom", atom.as_str(), "-"]).count(), 1);
            assert!(!rows.iter().any(|row| row.first() == Some(&"function") && row.get(1) == Some(&independent_name.as_str())));
            println!("J17/J18 refreshed common/unsafe receipts and final reverts:\n{}", artifacts.final_reverts);
            let events = emission.plan.bridge_events_with_atoms(&held, &atoms);
            let terminal_state = |key: &super::bridge_receipt::BridgeSiteKey| {
                let matching = events.iter().filter(|event| &event.site == key
                    && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
                let [event] = matching.as_slice() else { panic!("one exact post-atom receipt") };
                event.state
            };
            let independent_events = events.iter().filter(|event| event.site.owner_class == other
                && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            let independent_applied = !independent_events.is_empty()
                && independent_events.iter().all(|event| event.state == BridgeReceiptState::Applied);
            println!("J17/J18 selected atom={atom}; terminal events={events:#?}\nBASELINE:\n{baseline}\nATOM REVERT:\n{atom_output}");
            (baseline, atom_output, terminal_state(&strlen_key), terminal_state(&return_key), independent_applied)
        }).expect("UB-free caller-owned-storage fixture compiles");

    let baseline_checks = super::verify::type_checks_str(&baseline);
    let atom_checks = super::verify::type_checks_str(&atom_output);
    println!("J17/J18 outside-callback typechecks: baseline={baseline_checks}, atom={atom_checks}");
    assert!(
        baseline_checks && atom_checks,
        "actual emitted trees must type/borrow-check"
    );
    require_parameter(&baseline, "choose", "p", false);
    require_parameter(&atom_output, "choose", "p", true);
    require_parameter(&atom_output, "independent", "q", false);
    assert!(
        choose_return(&baseline).0,
        "baseline actually delivered a reference return"
    );
    assert_eq!(
        strlen_state,
        BridgeReceiptState::Dropped,
        "the selected source atom must actually drop its T1 receipt"
    );
    assert!(
        independent_applied,
        "the independent real class remains Applied"
    );
    let (borrowed_return, return_text) = choose_return(&atom_output);
    assert!(
        !borrowed_return && return_state == BridgeReceiptState::Dropped,
        "a raw sole origin cannot retain a generated reference return or Applied return receipt: return={return_text}, state={return_state:?}\n{atom_output}"
    );
}
