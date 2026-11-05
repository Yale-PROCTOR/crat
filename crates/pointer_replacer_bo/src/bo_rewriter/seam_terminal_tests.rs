//! Phase J: original interface forms and actual PAIR raw-view placement.

use super::{
    bridge_receipt::SignatureClassId,
    decision::seam::Form,
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
            crate::analyses::borrow_ownership::param_overlap::OverlapMode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::param_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
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
            &ctx.retained_copy_plans,
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
                &ctx.retained_copy_plans,
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
