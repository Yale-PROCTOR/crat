use super::{decision, mechanical_receipt as receipt, verify};

#[test]
fn r218_reclassified_option_call_stays_inactive_on_plan_replay() {
    let input = "type Ptr = *const i32; unsafe fn callee(q: *const i32) -> i32 { *q } pub unsafe fn target(delivered: *const i32, raw_slot: Ptr) -> i32 { *delivered + *raw_slot }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).unwrap();
        let (mut table, ctx) = super::decide_table_with_ctx(tcx).unwrap();
        let raw = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("raw_slot"))
            .unwrap()
            .0
            .clone();
        let callee = table
            .entries
            .iter()
            .find(|(s, _)| tcx.item_name(s.fn_did.to_def_id()).as_str() == "callee")
            .unwrap()
            .0
            .fn_did;
        let callee_class = super::bridge_receipt::SignatureClassId::of(callee);
        let mut retired = decision::option::receipt(
            tcx,
            &raw,
            raw.hir_id,
            receipt::MechanicalFamily::OptUseUnsupported,
            "call-required",
            decision::seam::Form::Raw,
            decision::seam::Form::Ref { mutable: false },
            "prior-raw-disposition:opt-use-unsupported".to_owned(),
            Some(receipt::MechanicalTerminalReason::EvidenceMissing(
                "additive-family-fallback:opt-use-unsupported".to_owned(),
            )),
            receipt::MechanicalEvidence::default(),
        );
        retired.obligation.intended_terminal_state = receipt::MechanicalState::Reclassified;
        retired.obligation.planned.key.site.callee =
            Some(receipt::CanonicalCallee::Local(callee.to_def_id()));
        retired.obligation.planned.key.site.argument_index = Some(0);
        retired
            .obligation
            .planned
            .dependency_classes
            .insert(callee_class);
        let key = retired.obligation.planned.key.clone();
        table.option_receipts.push(retired);
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::from_iter([callee]),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        let replayed = emission
            .plan
            .option_receipt_plans
            .iter()
            .find(|row| row.obligation.planned.key == key)
            .unwrap();
        assert_eq!(
            replayed.obligation.intended_terminal_state,
            receipt::MechanicalState::Reclassified,
            "terminal validation must not reactivate an obsolete Option call"
        );
        assert!(
            !emission
                .plan
                .held_classes()
                .contains(&super::bridge_receipt::SignatureClassId::of(raw.fn_did)),
            "an obsolete dependency must not hold the delivered neighbor"
        );
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &emission.plan.held_classes(),
            &std::collections::BTreeSet::new(),
            &table,
        )
        .unwrap();
        let files = super::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_a5_raw_calls),
        )
        .unwrap()
        .0;
        let emitted = files.into_values().next().unwrap();
        assert!(emitted.contains("delivered: &i32"), "{emitted}");
        assert!(verify::type_checks_str(&emitted));
    })
    .unwrap();
}

#[test]
fn r216_terminal_raw_callee_cannot_make_a_new_option_obligation_required() {
    let input = "unsafe fn required(q: *const i32) -> i32 { *q } pub unsafe fn target(p: *const i32, delivered: *const i32) -> i32 { *delivered + if p.is_null() { 0 } else { required(p) } }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx(tcx).unwrap();
        let callee = table
            .entries
            .iter()
            .find(|(subject, _)| tcx.item_name(subject.fn_did.to_def_id()).as_str() == "required")
            .unwrap()
            .0
            .fn_did;
        let mut emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        emission.plan.hold_terminal_class(
            super::bridge_receipt::SignatureClassId::of(callee),
            decision::Arm::Surface,
            "r216-held-callee",
            "r216-held-callee".to_owned(),
        );
        super::validate_terminal_option_calls(tcx, &table, &mut emission.plan);
        let requests = super::plan::additive_option_fallbacks(&table, &emission.plan);
        assert!(
            requests.iter().any(
                |(index, _)| emission.plan.option_receipt_plans[*index].operation
                    == "call-required"
            ),
            "a decided-safe but terminally raw callee must allow additive fallback: {requests:?}"
        );
    })
    .unwrap();
}

#[test]
fn r216_unsatisfied_additive_option_site_keeps_the_delivered_class() {
    let input = "pub unsafe fn target(delivered: *const i32, raw_slot: *const i32) -> i32 { raw_slot.read() + *delivered }";
    let baseline = super::emit_tests::ast_emitted_source_of(input).unwrap();
    assert!(baseline.contains("delivered: &i32"), "{baseline}");
    let emitted = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).unwrap();
        let (mut table, ctx) = super::decide_table_with_ctx(tcx).unwrap();
        let (raw, decision) = table.entries.iter().find(|(s, _)| s.param_name.as_deref() == Some("raw_slot")).unwrap();
        assert!(matches!(decision, decision::Decision::Degraded(_)), "existing raw disposition is load-bearing");
        let raw = raw.clone();
        table.option_receipts.push(decision::option::receipt(
            tcx, &raw, raw.hir_id, receipt::MechanicalFamily::OptUseUnsupported,
            "body-use", decision::seam::Form::Raw,
            decision::seam::Form::Opt { mutable: false, slice: false },
            "unbuilt-additive-option-site".to_owned(),
            Some(receipt::MechanicalTerminalReason::EvidenceMissing("r216-unbuilt-site".to_owned())),
            receipt::MechanicalEvidence::default(),
        ));
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans).unwrap();
        assert!(!emission.plan.held_classes().contains(&super::bridge_receipt::SignatureClassId::of(raw.fn_did)),
            "an unsatisfied new site must retain the old raw disposition without holding the delivered class");
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &emission.plan.held_classes(), &std::collections::BTreeSet::new(), &table,
        ).unwrap();
        super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts, emission.plan.root_file.as_ref(), &table,
            Some(&emission.plan.terminal_a5_raw_calls)).unwrap().0.into_values().next().unwrap()
    }).unwrap();
    assert_eq!(
        emitted, baseline,
        "additive fallback must retain the previously delivered rendering"
    );
    assert!(verify::type_checks_str(&emitted));
}

#[test]
fn r216_same_span_identical_option_use_is_composed_once() {
    let input = "pub unsafe fn target(p: *const i32) -> i32 { if p.is_null() { 0 } else { *p } }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (mut table, ctx) = super::decide_table_with_ctx(tcx).unwrap();
        let (_, decision) = table
            .entries
            .iter_mut()
            .find(|(s, _)| s.param_name.as_deref() == Some("p"))
            .unwrap();
        let decision::Decision::Opt { uses, .. } = decision else {
            panic!("actual Option subject required")
        };
        let edit = uses
            .iter()
            .find(|edit| edit.bridge_kind == "subject-use")
            .unwrap()
            .clone();
        uses.push(edit);
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        assert!(
            emission.rollbacks.is_empty(),
            "identical same-span Option uses must compose: {:?}",
            emission.rollbacks
        );
    })
    .unwrap();
}

#[test]
fn r216_color_tree_get_has_no_program_level_apply_rollback() {
    let input = "#[repr(C)] pub struct ColorTree { children: [*mut ColorTree; 16], index: i32 } pub unsafe fn color_tree_get(mut tree: *mut ColorTree, key: u8) -> i32 { let mut bit = 0; while bit < 8 { let i = ((key >> bit) & 1) as usize; if ((*tree).children[i]).is_null() { return -1; } else { tree = (*tree).children[i]; } bit += 1; } if !tree.is_null() { (*tree).index } else { -1 } }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx(tcx).unwrap();
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        assert!(
            emission.rollbacks.is_empty(),
            "color_tree_get overlap must compose or hold its owner: {:?}",
            emission.rollbacks
        );
    })
    .unwrap();
}
