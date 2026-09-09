//! Phase J: original interface forms and actual PAIR raw-view placement.

use super::{
    bridge_receipt::SignatureClassId,
    decision::{Decision, DegradeReason, seam::Form},
    delivery_custody::{TypeShape, inventory_source},
    verify,
};

#[test]
fn r230_guarded_fix3_read_only_confirmation() {
    let Ok(output_path) = std::env::var("CRAT_R230_CONFIRM_OUTPUT") else { return };
    assert!(
        !std::path::Path::new(&output_path).exists(),
        "one-shot confirmation output"
    );
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        pub struct Holder { data: *mut i32 }\n\
        pub unsafe fn update(dst: *mut i32, src: *const i32) {\n\
            *dst = *src + 1;\n\
        }\n\
        pub unsafe fn caller(holder: *const Holder, src: *const i32) {\n\
            update((*holder).data, src);\n\
        }\n\
        pub unsafe fn entry() {\n\
            let mut value = 1;\n\
            let holder = Holder { data: &mut value };\n\
            caller(&holder, &value);\n\
        }\n";
    let observed = std::sync::Mutex::new(serde_json::Value::Null);
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(input), None, super::MAX_REVERT_ROUNDS,
        &|table| {
            let before = format!("{table:?}");
            let forms = ["caller::holder", "caller::src", "update::dst", "update::src"]
                .into_iter().map(|label| {
                    let (subject, decision) = table.entries.iter()
                        .find(|(subject, _)| subject.label == label).expect("exact required subject");
                    (label.to_owned(), serde_json::json!({
                        "decision": format!("{decision:?}"),
                        "owner_class": SignatureClassId::of(subject.fn_did).order_key(),
                        "hir": format!("{:?}", subject.hir_id),
                    }))
                }).collect::<std::collections::BTreeMap<_, _>>();
            let classes = rustc_middle::ty::tls::with(|tcx| {
                let emission = super::emit_files(tcx, table, &rustc_hash::FxHashSet::default(),
                    &table.c9_marks).expect("unchanged pre-verify plan inspection");
                format!("{:#?}", emission.plan.class_finalization)
            });
            *observed.lock().unwrap() = serde_json::json!({
                "decided_parameters": forms,
                "Holder.data": "No field DecisionTable subject; original *mut i32 declaration is retained",
                "c9_marks": format!("{:#?}", table.c9_marks),
                "planned_pair_calls": format!("{:#?}", table.seams.pair_raw_calls),
                "blocked_seams": format!("{:#?}", table.seams.blocked),
                "class_finalization": classes,
            });
            assert_eq!(format!("{table:?}"), before, "confirmation hook is read-only");
        },
        false, false, true,
        Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let mut record = observed.into_inner().unwrap();
    match outcome {
        super::RewriteOutcome::Emitted {
            source,
            raw_boundary_artifacts,
            degradations,
            reverted_count,
            verify_rounds,
            ..
        } => {
            let compiles = verify::type_checks_str(&source);
            let copy_applied = raw_boundary_artifacts.bridge_events.iter().any(|event| {
                event.site.bridge_kind == "pair-copy-snapshot"
                    && event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
                    && event.state == super::bridge_receipt::BridgeReceiptState::Applied
            });
            record["emitted_source"] = source.clone().into();
            record["type_checks"] = compiles.into();
            record["copy_snapshot_applied"] = copy_applied.into();
            record["pairs"] = raw_boundary_artifacts.pairs.into();
            record["arm_outcomes"] = raw_boundary_artifacts.arm_outcomes.into();
            record["edit_keys"] = raw_boundary_artifacts.edit_keys.into();
            record["bridge_events"] = format!("{:#?}", raw_boundary_artifacts.bridge_events).into();
            record["degradations"] = format!("{degradations:#?}").into();
            record["final_reverts"] = raw_boundary_artifacts.final_reverts.into();
            record["unresolved_classes"] = raw_boundary_artifacts.unresolved_classes.into();
            record["reverted_count"] = reverted_count.into();
            record["verify_rounds"] = verify_rounds.into();
            record["declarations"] = serde_json::to_value(
                inventory_source("r230-emitted.rs", &source).expect("pinned declaration parser"),
            )
            .unwrap();
            std::fs::write(&output_path, serde_json::to_string_pretty(&record).unwrap()).unwrap();
            assert!(compiles, "full emitted output must type/borrow-check");
            assert!(
                copy_applied && source.contains("__crat_c9_") && source.contains("&__crat_c9_"),
                "confirmation requires the site-naming applied C-9 guard; inspect the sealed record"
            );
            assert!(
                source.contains("data: *mut i32"),
                "Holder.data retains its raw input form"
            );
        }
        other => {
            record["outcome"] = format!("{other:#?}").into();
            std::fs::write(&output_path, serde_json::to_string_pretty(&record).unwrap()).unwrap();
            panic!("confirmation did not emit; inspect the sealed record");
        }
    }
}

fn original_parameter_form(input: &str, optional: bool, reverted: bool) {
    assert!(verify::type_checks_str(input), "valid original interface");
    let declarations = inventory_source("original-interface.rs", input)
        .expect("independent original declaration inventory");
    let parameter = declarations
        .iter()
        .find(|row| row.owner == "existing" && row.binding == "p" && row.parameter_index == Some(1))
        .expect("exact original parameter");
    let shared_i32 = TypeShape::Reference {
        mutable: false,
        pointee: Box::new(TypeShape::Named {
            path: "i32".to_owned(),
        }),
    };
    let expected_shape = if optional {
        TypeShape::Option {
            path: "Option".to_owned(),
            payload: Box::new(shared_i32),
        }
    } else {
        shared_i32
    };
    assert_eq!(parameter.type_shape, expected_shape);
    assert!(parameter.type_is_fully_explicit);
    let expected = if optional {
        Form::Opt {
            mutable: false,
            slice: false,
        }
    } else {
        Form::Ref { mutable: false }
    };
    ::utils::compilation::run_compiler_on_str(input, move |tcx| {
        let (table, ctx) =
            super::decide_table_with_ctx(tcx).expect("original-interface production decisions");
        let owner = tcx
            .hir_body_owners()
            .find(|did| tcx.def_path_str(did.to_def_id()) == "existing")
            .expect("existing function identity");
        let class_id = SignatureClassId::of(owner);
        let live = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("original-interface emission plan");
        let finalization = if reverted {
            assert!(
                live.plan
                    .class_finalization
                    .classes
                    .get(&class_id)
                    .is_some_and(super::plan::SignatureClassPlan::is_ready),
                "the independent raw parameter must supply an actual ready class: {:?}",
                live.plan.class_finalization
            );
            let held = super::emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::from_iter([owner]),
                &ctx.retained_c9_plans,
            )
            .expect("production pre-reverted emission plan");
            let class = held
                .plan
                .class_finalization
                .classes
                .get(&class_id)
                .expect("the actual owner class remains accounted after reversion");
            assert!(!class.is_ready());
            assert!(
                class
                    .hold_reasons()
                    .iter()
                    .any(|reason| reason == "pre-reverted-class")
            );
            held.plan.class_finalization
        } else {
            assert!(
                !live.plan.class_finalization.classes.contains_key(&class_id),
                "an unchanged original safe parameter needs no rewrite class"
            );
            live.plan.class_finalization
        };
        assert_eq!(
            super::terminal_parameter_form(&table, &finalization, owner, 0),
            expected,
            "the terminal consumer must preserve the compiler input's safe interface"
        );
    })
    .expect("original-interface compiler context");
}

#[test]
fn seam_terminal_original_reference_survives_absent_class() {
    original_parameter_form("pub fn existing(p: &i32) -> i32 { *p }", false, false);
}

#[test]
fn seam_terminal_original_option_survives_absent_class() {
    original_parameter_form(
        "pub fn existing(p: Option<&i32>) -> i32 { p.map_or(0, |p| *p) }",
        true,
        false,
    );
}

#[test]
fn seam_terminal_original_reference_survives_held_class() {
    original_parameter_form(
        "pub unsafe fn existing(p: &i32, q: *const i32) -> i32 { *p + *q }",
        false,
        true,
    );
}

#[test]
fn seam_terminal_original_option_survives_held_class() {
    original_parameter_form(
        "pub unsafe fn existing(p: Option<&i32>, q: *const i32) -> i32 { p.map_or(0, |p| *p) + *q }",
        true,
        true,
    );
}

/// RB-PLACED-FORM: PAIR chooses a raw parameter within a surviving class.
/// The printf tail has an existing sealed read-only import contract; opaque
/// foreign effects must not substitute a model-Raw case for this witness.
fn pair_raw_parameter_outbound_case(operand: &str) {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        static FORMAT: [i8; 3] = [37, 112, 0];\n\
        extern \"C\" { fn printf(format: *const i8, ...) -> i32; }\n\
        pub unsafe fn update(a: *mut i32, b: *mut i32) {\n\
            *a += 1; *b += 1; printf(FORMAT.as_ptr(), b as *const i32);\n\
        }\n\
        pub unsafe fn caller() { let mut x = 0; update(&mut x, &mut x); }\n";
    let input = input.replace("b as *const i32", operand);
    let output = assert_pair_raw_parameter_outbound(&input, None, true);
    assert!(
        output.contains("printf(FORMAT.as_ptr(),"),
        "the outbound call survives: {output}"
    );
}

fn assert_pair_raw_parameter_outbound(
    input: &str,
    required_import: Option<&'static str>,
    raw_mutable: bool,
) -> String {
    assert!(
        verify::type_checks_str(input),
        "PAIR raw-view input type-checks"
    );
    let output = ::utils::compilation::run_compiler_on_str(input, move |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("PAIR original AST");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("PAIR production decision table");
        let (subject, decision) = table.entries.iter()
            .find(|(subject, _)| subject.label == "update::b")
            .expect("PAIR selected parameter");
        let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
            .and_then(|slots| slots.slot_for_local_depth(subject.local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)))
            .copied();
        assert_eq!(kind, Some(super::SlotKind::Ref),
            "the selected parameter must remain frozen model-Ref");
        assert!(matches!(decision, Decision::Degraded(record) if record.reason == DegradeReason::PairRawView),
            "the fixture must select actual PAIR raw placement, not another refusal: {decision:?}");
        assert!(table.seams.pair_raw_calls.iter().any(|call| {
            call.callee == subject.fn_did && call.views.iter().any(|view| view.argument_index == 1)
        }), "the same-object call must carry the selected second raw parameter");
        if let Some(symbol) = required_import {
            let hypothetical = ctx.hypothetical.entries.iter()
                .find(|(candidate, _)| candidate.fn_did == subject.fn_did
                    && candidate.hir_id == subject.hir_id).map(|(_, decision)| decision)
                .expect("the exact PAIR parameter has an earlier hypothetical decision");
            assert!(matches!(hypothetical, Decision::Ref { mutable: false }),
                "the raw-boundary template must originate from an actual hypothetical Ref: {hypothetical:?}");
            let site = ctx.raw_boundary_sites.sites.iter().find(|site| {
                site.node == Some((subject.fn_did, subject.hir_id))
                    && site.key.callee.foreign && site.key.callee.symbol == symbol
                    && site.key.argument_index == 0
            }).expect("the PAIR raw parameter must reach the fixed raw-pointer import argument");
            if symbol == "strlen" {
                assert_eq!(site.target.rendered, "*const i8");
                let contract = super::decision::raw_boundary_contracts::classify_contract(
                    &site.key.callee, site.key.argument_index, &site.target)
                    .expect("the fixed pointer argument has its sealed import contract");
                assert_eq!(contract.access,
                    super::decision::raw_boundary_contracts::PointeeAccess::Read);
            } else {
                assert_eq!(symbol, "memcmp", "the void-view fixture has one exact import");
                let void_sites = ctx.raw_boundary_sites.sites.iter().filter(|site| {
                    site.node == Some((subject.fn_did, subject.hir_id))
                        && site.key.callee.foreign && site.key.callee.symbol == symbol
                        && site.key.argument_index < 2
                }).collect::<Vec<_>>();
                assert_eq!(void_sites.len(), 2, "both memcmp pointer arguments must be rooted at b");
                assert!(void_sites.iter().all(|site| {
                    site.target.is_void_pointee()
                        && site.target.mutability == super::decision::raw_boundary::RawMutability::Const
                }), "memcmp must consume compiler-resolved const void pointers");
            }
        }
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans).expect("PAIR terminal emission plan");
        let class_id = SignatureClassId::of(subject.fn_did);
        let class = emission.plan.class_finalization.classes.get(&class_id)
            .expect("PAIR update class");
        assert!(class.is_ready(), "the raw parameter must coexist with a live safe class: {class:?}");
        assert_eq!(super::terminal_parameter_form(&table, &emission.plan.class_finalization,
            subject.fn_did, 1), Form::Raw);
        let held = emission.plan.held_classes();
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &held, &std::collections::BTreeSet::new(), &table).expect("PAIR actual reverts");
        let (files, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture,
            &reverts, emission.plan.root_file.as_ref(), &table,
            Some(&emission.plan.terminal_call_plans)).expect("PAIR placed AST");
        files.into_values().next().expect("PAIR output source")
    }).expect("PAIR compiler context");
    let declarations =
        inventory_source("placed-pair.rs", &output).expect("PAIR observed declarations");
    let a = declarations
        .iter()
        .find(|row| row.owner == "update" && row.parameter_index == Some(1))
        .expect("surviving safe first parameter");
    let b = declarations
        .iter()
        .find(|row| row.owner == "update" && row.parameter_index == Some(2))
        .expect("placed raw second parameter");
    assert!(
        matches!(&a.type_shape, TypeShape::Reference { mutable: true, .. }),
        "{output}"
    );
    assert!(
        matches!(&b.type_shape, TypeShape::RawPointer { mutable, .. } if *mutable == raw_mutable),
        "{output}"
    );
    assert!(output.contains("let __crat_pair_raw_"), "{output}");
    assert!(
        verify::type_checks_str(&output),
        "the outbound adapter must consume the actually raw parameter: {output}"
    );
    output
}

#[test]
fn seam_terminal_pair_raw_parameter_drives_its_outbound_adapter() {
    // The explicit cast is the established GREEN contrast from J03.
    pair_raw_parameter_outbound_case("b as *const i32");
}

#[test]
fn seam_terminal_pair_raw_parameter_bare_operand_drives_its_outbound_adapter() {
    pair_raw_parameter_outbound_case("b");
}

#[test]
fn seam_terminal_pair_raw_parameter_fixed_read_import_uses_its_placed_form() {
    // The write touches bytes[0]; bytes[1] remains NUL for the read-only strlen.
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        extern \"C\" { fn strlen(s: *const i8) -> usize; }\n\
        pub unsafe fn update(a: *mut i8, b: *const i8) {\n\
            *a += 1; let _ = strlen(b);\n\
        }\n\
        pub unsafe fn caller() {\n\
            let mut bytes = [0i8; 3]; update(&mut bytes[0], &bytes[0]);\n\
        }\n";
    let output = assert_pair_raw_parameter_outbound(input, Some("strlen"), false);
    assert!(
        output.contains("let _ = strlen("),
        "the required pointer call survives: {output}"
    );
}

#[test]
fn seam_terminal_pair_raw_parameter_void_read_import_uses_its_placed_form() {
    // Both memcmp ranges are one initialized byte; a's write precedes the read.
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        extern \"C\" {\n\
            fn memcmp(left: *const core::ffi::c_void, right: *const core::ffi::c_void, count: usize) -> i32;\n\
        }\n\
        pub unsafe fn update(a: *mut i8, b: *const i8) {\n\
            *a += 1; let _ = memcmp(b as *const _, b as *const _, 1);\n\
        }\n\
        pub unsafe fn caller() {\n\
            let mut bytes = [0i8; 3]; update(&mut bytes[0], &bytes[0]);\n\
        }\n";
    let output = assert_pair_raw_parameter_outbound(input, Some("memcmp"), false);
    assert!(
        output.contains("let _ = memcmp("),
        "the two pointer arguments survive: {output}"
    );
}

#[test]
fn seam_terminal_pair_raw_view_uses_the_reverted_source_form() {
    r231_raw_role_case(true);
}

#[test]
fn r231_fallback_has_a_raw_callee_role_and_materialized_view() {
    r231_raw_role_case(false);
}

fn r231_raw_role_case(revert_caller: bool) -> R231CustodyFixture {
    r231_raw_role_fixture(revert_caller, false)
}

fn r231_raw_role_fixture(revert_caller: bool, unknown_source: bool) -> R231CustodyFixture {
    r231_raw_role_fixture_with_atom(revert_caller, unknown_source, false)
}

fn r231_raw_role_fixture_with_atom(
    revert_caller: bool,
    unknown_source: bool,
    revert_atom: bool,
) -> R231CustodyFixture {
    // The scalar update body matches the established PAIR Copy-without-C9
    // fixture; the entry seeds one allocation into both the field-loaded
    // primary and the direct peer at the exact caller site under test.
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        pub struct Holder { data: *mut i32 }\n\
        pub unsafe fn update(dst: *mut i32, src: *const i32) {\n\
            *dst = *src + 1;\n\
        }\n\
        pub unsafe fn caller(holder: *const Holder, src: *const i32) {\n\
            update((*holder).data, src);\n\
        }\n\
        pub unsafe fn entry() {\n\
            let mut value = 1;\n\
            let holder = Holder { data: &mut value };\n\
            caller(&holder, &value);\n\
        }\n";
    assert!(
        verify::type_checks_str(input),
        "PAIR source-reversion input type-checks"
    );
    let (output, expectations, context, pending, gaps) = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("PAIR source-reversion AST");
        let (mut table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("PAIR source-reversion production decisions");
        let solve = super::model_cache::solve_receipt();
        println!("R231 fixture solve receipt (caller_reverted={revert_caller}): {solve:#?}");
        assert!(solve.is_some(), "fixture evidence carries its solve receipt");
        if unknown_source {
            // Consumer-level custody fault: real frozen site facts stay fixed;
            // make only the source-shape correspondence unavailable.
            for coverage in &mut table.sibling_overlap_inventory.coverage {
                if coverage.potential.source.label() == "caller::src" && coverage.potential.site.callee.symbol == "update" {
                    coverage.evidence = super::decision::sibling_overlap::SourceBridgeEvidence::UnknownShape("injected-source-custody-gap");
                }
            }
            table.sibling_overlap_inventory.potentials.retain(|potential|
                !(potential.source.label() == "caller::src" && potential.site.callee.symbol == "update"));
        }
        let (source, source_decision) = table.entries.iter()
            .find(|(subject, _)| subject.label == "caller::src").expect("exact PAIR source");
        let kind = ctx.slots.fn_local_slots.get(&source.fn_did)
            .and_then(|slots| slots.slot_for_local_depth(source.local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(source.fn_did, slot)))
            .copied();
        assert_eq!(kind, Some(super::SlotKind::Ref), "the PAIR source must be frozen model-Ref");
        assert!(matches!(source_decision, Decision::Ref { mutable: false }),
            "the original production PAIR source must be a decided shared Ref: {source_decision:?}");
        let (raw_parameter, raw_decision) = table.entries.iter()
            .find(|(subject, _)| subject.label == "update::src").expect("exact PAIR raw parameter");
        assert!(matches!(raw_decision, Decision::Degraded(record) if record.reason == DegradeReason::PairRawView),
            "the callee must have the actual PAIR raw-view role: {raw_decision:?}");
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans).expect("PAIR source-reversion terminal plan");
        let caller_class = SignatureClassId::of(source.fn_did);
        let update_class = SignatureClassId::of(raw_parameter.fn_did);
        for id in [caller_class, update_class] {
            assert!(emission.plan.class_finalization.classes.get(&id)
                .is_some_and(super::plan::SignatureClassPlan::is_ready),
                "both actual classes must be ready before the source revert: {:?}",
                emission.plan.class_finalization);
        }
        let calls = emission.plan.terminal_call_plans.a5_raw_calls.iter()
            .filter(|call| call.caller == source.fn_did && call.callee == raw_parameter.fn_did)
            .collect::<Vec<_>>();
        assert_eq!(calls.len(), 1, "one canonical A5 T2 call must survive terminal planning");
        assert!(calls[0].views.iter().any(|view| view.argument_index == 1
            && view.raw_expression.contains("core::ptr::from_ref(src)")
            && view.source_node == Some((source.fn_did, source.hir_id))
            && view.expected_form == Form::Raw
            && view.adapted_expression == super::c9::A5_RAW_VALUE_PLACEHOLDER),
            "the baseline carrier must actually require the shared safe source: {:?}", calls[0]);
        assert!(emission.plan.bridge_events(&std::collections::BTreeSet::new()).iter().any(|event| {
            event.site.owner_class == update_class && event.site.bridge_kind == "a5-site-proof-t2-fallback"
                && event.retention == super::bridge_receipt::BridgeRetentionTier::T2
                && event.waiver_id.as_deref() == Some(super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID)
        }), "the raw-view selection must carry its actual T2 receipt");
        assert!(emission.plan.class_finalization.classes[&update_class].sites.iter()
            .filter(|site| site.key.bridge_kind == "a5-site-proof-t2-fallback")
            .all(|site| matches!(site.state, super::plan::ClassSiteState::EditReady)),
            "no A5 T2 obligation is a zero-syntax receipt");
        let mut withheld = emission.plan.held_classes();
        if revert_caller { withheld.insert(caller_class); }
        let atoms = if revert_atom {
            table.seams.raw_boundary_atom_groups.get(&(source.fn_did, source.hir_id))
                .into_iter().flatten().map(|atom| atom.id.clone()).collect::<std::collections::BTreeSet<_>>()
        } else { std::collections::BTreeSet::new() };
        if revert_atom { assert!(!atoms.is_empty(), "the exact source must have an actual atom group"); }
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &withheld, &atoms, &table).expect("actual caller/class/atom reversion");
        assert_eq!(reverts.keeps(caller_class), !revert_caller);
        assert!(reverts.keeps(update_class), "the target class must remain live for this RFF witness");
        let (files, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
            emission.plan.root_file.as_ref(), &table, Some(&emission.plan.terminal_call_plans))
            .expect("PAIR source-reversion emission");
        use super::bridge_custody_match::{BridgeExpectation, BridgeKind, SiteAnchor, BridgeCustodyContext};
        let source_file = tcx.sess.source_map().lookup_source_file(calls[0].call_span.lo());
        let start = source_file.start_pos.0;
        let call_span = super::delivery_custody::ByteSpan {
            lo: calls[0].call_span.lo().0 - start, hi: calls[0].call_span.hi().0 - start,
        };
        let expectations = emission.plan.bridge_events_with_atoms(&withheld, &atoms).into_iter()
            .filter(|event| event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
                && event.state == super::bridge_receipt::BridgeReceiptState::Applied
                && event.site.owner_class == update_class
                && event.site.bridge_kind == "a5-site-proof-t2-fallback")
            .map(|event| {
                let span = super::delivery_custody::ByteSpan { lo: event.site.lo, hi: event.site.hi };
                let anchor = if span == call_span {
                    SiteAnchor::Call { span, argument_indices: calls[0].views.iter().map(|view| view.argument_index).collect() }
                } else {
                    let proof = table.seams.overlap_proofs.iter().find(|proof|
                        proof.caller == source.fn_did && proof.callee == raw_parameter.fn_did
                            && proof.span.lo().0 - start == span.lo && proof.span.hi().0 - start == span.hi)
                        .expect("Applied logical argument has its exact typed proof");
                    SiteAnchor::Argument { span, argument_index: proof.index }
                };
                BridgeExpectation { pending_source: None, identity: format!("{:?}", event.site),
                    kind: BridgeKind::A5SiteProofT2Fallback,
                    caller: tcx.def_path_str(source.fn_did.to_def_id()),
                    callee: tcx.def_path_str(raw_parameter.fn_did.to_def_id()),
                    anchor, c9_stamp: None, tier: "T2".into(), waiver_id: event.waiver_id }
            }).collect::<Vec<_>>();
        assert_eq!(expectations.len(), 2, "one physical call and one logical position are Applied");
        (files.into_values().next().expect("PAIR source-reversion output"), expectations,
            BridgeCustodyContext { source_global_start: start, ..Default::default() },
            emission.plan.pending_sibling_receipts_with_atoms(&withheld, &atoms), emission.plan.sibling_coverage_gaps_with_atoms(&withheld, &atoms))
    }).expect("PAIR source-reversion compiler context");
    let declarations = inventory_source("reverted-pair-source.rs", &output)
        .expect("independent PAIR source-reversion declarations");
    let caller = declarations
        .iter()
        .find(|row| row.owner == "caller" && row.parameter_index == Some(2))
        .expect("original caller parameter survives");
    if revert_caller || revert_atom {
        assert!(
            matches!(
                &caller.type_shape,
                TypeShape::RawPointer { mutable: false, .. }
            ),
            "{output}"
        );
    } else {
        assert!(
            matches!(
                &caller.type_shape,
                TypeShape::Reference { mutable: false, .. }
            ),
            "{output}"
        );
    }
    let callee = declarations
        .iter()
        .find(|row| row.owner == "update" && row.parameter_index == Some(1))
        .expect("surviving update parameter");
    assert!(
        matches!(
            &callee.type_shape,
            TypeShape::Reference { mutable: true, .. }
        ),
        "{output}"
    );
    let raw_target = declarations
        .iter()
        .find(|row| row.owner == "update" && row.parameter_index == Some(2))
        .unwrap();
    assert!(
        matches!(
            &raw_target.type_shape,
            TypeShape::RawPointer { mutable: false, .. }
        ),
        "{output}"
    );
    if revert_caller || revert_atom {
        assert!(
            output
                .lines()
                .any(|line| line.contains("let __crat_a5_raw_") && line.contains(" = src;")),
            "the actual raw-view temporary uses its input-form twin: {output}"
        );
        assert!(!output.contains("core::ptr::from_ref(src)"), "{output}");
    } else {
        assert!(
            output.contains("let __crat_a5_raw_") && output.contains("core::ptr::from_ref(src)"),
            "{output}"
        );
    }
    println!("R231 emitted (caller_reverted={revert_caller}):\n{output}");
    assert!(
        verify::type_checks_str(&output),
        "PAIR input-form output must type/borrow-check: {output}"
    );
    R231CustodyFixture {
        input: input.into(),
        output,
        expectations,
        context,
        pending,
        gaps,
    }
}

#[test]
fn r231_restored_cast_operand_keeps_the_inner_reference() {
    let input = "unsafe fn target(p: *const i32) {} unsafe fn caller(src: *const i32, value: i32) { target(src as *const i32); target(&value as *const i32); target(src); }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let functions = tcx.hir_body_owners().collect::<Vec<_>>();
        let facts = super::decision::emitability::collect(tcx, &functions);
        let target = functions
            .into_iter()
            .find(|did| tcx.def_path_str(did.to_def_id()) == "target")
            .unwrap();
        let arguments = facts.call_args[&target]
            .iter()
            .map(|site| &site.args[0])
            .collect::<Vec<_>>();
        assert_eq!(arguments.len(), 3);
        let observed = arguments
            .iter()
            .map(|argument| {
                tcx.sess
                    .source_map()
                    .span_to_snippet(super::a5_role_operand_span(argument))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            observed,
            ["src", "&value", "src"],
            "cast restoration must share the discovery operand rule"
        );
    })
    .expect("instrument-only compiler facts, no model solve");
}

struct R231CustodyFixture {
    input: String,
    output: String,
    expectations: Vec<super::bridge_custody_match::BridgeExpectation>,
    context: super::bridge_custody_match::BridgeCustodyContext,
    pending: Vec<super::plan::sibling_overlap::PendingSite>,
    gaps: Vec<super::decision::sibling_overlap::CoverageGapReceipt>,
}

#[test]
fn r231_deliberate_fault_receipt_without_render_is_caught_by_bridge_custody() {
    use super::{bridge_custody_match as custody, bridge_custody_syntax as syntax};
    let fixture = r231_raw_role_case(false);
    let original = syntax::inventory_source("r231-input.rs", &fixture.input).unwrap();
    let emitted = syntax::inventory_source("r231-output.rs", &fixture.output).unwrap();
    let check = |output: &str, inventory: &syntax::Inventory| {
        custody::compare(custody::BridgeCustodyInput {
            original: &original,
            emitted: inventory,
            original_source: &fixture.input,
            emitted_source: output,
            expectations: &fixture.expectations,
            context: &fixture.context,
        })
    };
    let green = check(&fixture.output, &emitted);
    assert!(
        green.data && green.rows.len() == 2,
        "baseline actual emission: {green:#?}"
    );
    let binding = emitted
        .bindings
        .iter()
        .find(|binding| {
            binding.owner == "caller"
                && binding.generated == Some(syntax::GeneratedKind::RawTemporary)
        })
        .expect("one actual raw-view binding");
    let call = emitted
        .calls
        .iter()
        .find(|call| {
            call.owner == "caller"
                && call.arguments.iter().any(|argument| {
                    argument
                        .binding
                        .as_ref()
                        .is_some_and(|bound| bound.id == binding.id)
                })
        })
        .expect("raw-view actual call use");
    let argument = call
        .arguments
        .iter()
        .find(|argument| {
            argument
                .binding
                .as_ref()
                .is_some_and(|bound| bound.id == binding.id)
        })
        .unwrap();
    let mut edits = vec![(binding.declaration_span, ""), (argument.span, "src")];
    edits.sort_by_key(|(span, _)| std::cmp::Reverse(span.lo));
    let mut fault = fixture.output.clone();
    for (span, replacement) in edits {
        fault.replace_range(span.lo as usize..span.hi as usize, replacement);
    }
    assert!(
        verify::type_checks_str(&fault),
        "the deliberate fault must evade type checking: {fault}"
    );
    let fault_inventory = syntax::inventory_source("r231-fault.rs", &fault).unwrap();
    let caught = check(&fault, &fault_inventory);
    println!(
        "R231 deliberate-fault check: receipt-without-render caught by bridge custody: {caught:#?}"
    );
    assert!(
        !caught.data
            && caught
                .rows
                .iter()
                .all(|row| row.status == custody::ReceiptStatus::Missing),
        "Applied receipts without rendered views must fail closed: {caught:#?}"
    );
    assert!(
        check(&fixture.output, &emitted).data,
        "fault injection leaves the authoritative output and receipts unchanged"
    );
}

#[test]
fn r233_pending_stamp_tracks_the_actual_source_and_callee_interfaces() {
    let live = r231_raw_role_case(false);
    assert_eq!(
        live.pending.len(),
        1,
        "the delivered source parameter into the raw callee carries one pending waiver"
    );
    let receipt = &live.pending[0];
    assert!(
        receipt.site.is_ok(),
        "exact compiler site mapping: {receipt:#?}"
    );
    assert_eq!(receipt.receipt.potential.source.label(), "caller::src");
    assert_eq!(receipt.receipt.tier, "T2-pending");
    let reverted = r231_raw_role_case(true);
    assert!(
        reverted.pending.is_empty(),
        "a source reverted to raw carries no reference waiver"
    );
}

#[test]
fn r233_unknown_source_custody_survives_planning_as_a_terminal_gap() {
    let live = r231_raw_role_fixture(false, true);
    assert!(
        live.pending.is_empty(),
        "unknown source correspondence does not invent a waiver"
    );
    assert_eq!(
        live.gaps.len(),
        1,
        "planning must preserve the exact unresolved delivered site"
    );
    assert_eq!(live.gaps[0].potential.source.label(), "caller::src");
    assert_eq!(
        live.gaps[0].reason,
        "sibling-source-bridge-custody-unresolved"
    );
    let reverted = r231_raw_role_fixture(true, true);
    assert!(
        reverted.gaps.is_empty(),
        "a source returned to raw does not have reference bridge custody"
    );
}

#[test]
fn r233_actual_pending_bridge_custody_tracks_the_materialized_view() {
    use super::{bridge_custody_match as custody, bridge_custody_syntax as syntax};
    let fixture = r231_raw_role_case(false);
    assert_eq!(fixture.pending.len(), 1);
    let mut expectations = fixture.expectations.clone();
    for pending in &fixture.pending {
        let site = pending.site.as_ref().expect("exact compiler pending site");
        expectations.push(custody::BridgeExpectation {
            pending_source: None,
            identity: site.receipt_key(),
            kind: custody::BridgeKind::SiblingOverlapPending,
            caller: pending.receipt.potential.site.caller.clone(),
            callee: pending.receipt.potential.site.callee.path.clone(),
            anchor: custody::SiteAnchor::Argument {
                span: super::delivery_custody::ByteSpan {
                    lo: site.lo,
                    hi: site.hi,
                },
                argument_index: pending.receipt.potential.site.argument_index,
            },
            c9_stamp: None,
            tier: pending.receipt.tier.into(),
            waiver_id: Some(pending.receipt.waiver.into()),
        });
    }
    let original = syntax::inventory_source("r233-original.rs", &fixture.input).unwrap();
    let emitted = syntax::inventory_source("r233-emitted.rs", &fixture.output).unwrap();
    let result = custody::compare(custody::BridgeCustodyInput {
        original: &original,
        emitted: &emitted,
        original_source: &fixture.input,
        emitted_source: &fixture.output,
        expectations: &expectations,
        context: &fixture.context,
    });
    assert!(
        result.data,
        "actual S raw views and pending waiver must agree with the tree: {result:#?}"
    );
    assert_eq!(
        result
            .rows
            .iter()
            .filter(|row| row.status == custody::ReceiptStatus::MatchedRaw)
            .count(),
        2
    );
    assert_eq!(
        result
            .rows
            .iter()
            .filter(|row| row.status == custody::ReceiptStatus::WaivedPending)
            .count(),
        1
    );
}

#[test]
fn r233_source_atom_reversion_removes_only_its_pending_receipt() {
    let atom = r231_raw_role_fixture_with_atom(false, false, true);
    assert!(
        atom.pending.is_empty(),
        "the source returned to raw while its class stays ready: {:?}",
        atom.pending
    );
    assert_eq!(
        atom.expectations.len(),
        2,
        "the actual raw-view carrier remains Applied using its input twin"
    );
    let gap = r231_raw_role_fixture_with_atom(false, true, true);
    assert!(
        gap.gaps.is_empty(),
        "source atom reversion also removes an unresolved reference-custody obligation"
    );
}

#[test]
fn retalias_terminal_shared_view_rechecks_frozen_child_permission() {
    use super::decision::{
        raw_boundary::{ReturnedChildPermissionFailure, ReturnedChildSiteEvidence},
        seam::{Form, terminal_returned_child_permission},
    };
    let missing = ReturnedChildSiteEvidence {
        child: Err("fixture-missing-child-proof"),
        raw_field_parent: false,
    };
    assert_eq!(
        terminal_returned_child_permission(
            Some(&missing),
            "bare-local",
            Form::Ref { mutable: true }
        ),
        Ok(())
    );
    assert_eq!(
        terminal_returned_child_permission(Some(&missing), "bare-local", Form::Raw),
        Ok(())
    );
    assert_eq!(
        terminal_returned_child_permission(
            Some(&missing),
            "bare-local",
            Form::Ref { mutable: false }
        ),
        Err(ReturnedChildPermissionFailure::Unknown),
        "a terminal shared source needs its own child permission"
    );
}

#[test]
fn retalias_terminal_address_view_uses_its_actual_borrow_kind() {
    use super::decision::{
        raw_boundary::{ReturnedChildPermissionFailure, ReturnedChildSiteEvidence},
        seam::{Form, terminal_returned_child_permission},
    };
    let missing = ReturnedChildSiteEvidence {
        child: Err("fixture-missing-child-proof"),
        raw_field_parent: false,
    };
    assert_eq!(
        terminal_returned_child_permission(Some(&missing), "addr-of", Form::Raw),
        Err(ReturnedChildPermissionFailure::Unknown),
        "address construction is shared even when its root stays raw"
    );
    assert_eq!(
        terminal_returned_child_permission(Some(&missing), "addr-of-mut", Form::Raw),
        Ok(())
    );
}
