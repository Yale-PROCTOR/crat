//! I10 RED: a by-value pattern component has no annotation site of its own.

use super::{
    decision::DeclShape, delivery_custody::inventory_source, emit_tests::ast_emitted_source_of,
    verify,
};

#[test]
fn decl_pattern_nullable_component_requires_a_typed_temporary_in_place() {
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        fn record_before(log: &mut u32) { *log = *log * 10 + 1; }\n\
        fn stamp(log: &mut u32) -> u8 { *log = *log * 10 + 2; 0 }\n\
        fn record_after(log: &mut u32) { *log = *log * 10 + 3; }\n\
        pub unsafe fn pattern_target(enabled: bool, log: &mut u32) -> u32 {\n\
            if enabled {\n\
                record_before(log);\n\
                if let (p, 0) = (0 as *const i32, stamp(log)) {\n\
                    record_after(log);\n\
                    return if p.is_null() { 0 } else { (*p).count_ones() };\n\
                }\n\
            }\n\
            0\n\
        }";
    assert!(
        verify::type_checks_str(input),
        "pattern witness input must type-check"
    );
    let receipt_temporary = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx(tcx).expect("pattern decisions");
        let subjects = table.entries.iter().filter(|(subject, _)| {
            tcx.def_path_str(subject.fn_did.to_def_id()) == "pattern_target"
                && subject.param_name.as_deref() == Some("p")
        }).collect::<Vec<_>>();
        assert_eq!(subjects.len(), 1,
            "the real collector must expose one pattern binding; never fabricate a model fact: {:?}",
            table.entries);
        let subject = &subjects[0].0;
        assert_eq!(subject.decl_shape, DeclShape::RawPtr,
            "this by-value raw binding is separate from the fixed reference exclusions");
        assert!(subject.ty_span.is_none(), "the component has no independent type annotation");
        let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
            .and_then(|slots| slots.slot_for_local_depth(subject.local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)))
            .copied();
        assert_eq!(kind, Some(super::SlotKind::Ref),
            "the original binding must have an actual model-Ref fact before presentation is tested");
        let emission = super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans).unwrap();
        let none = Default::default();
        let rows = emission.plan.declaration_receipt_rows(&none);
        let events = emission.plan.mechanical_receipts(&none).0;
        super::mechanical_receipt::reconcile_declaration_shape_rows(&rows, &events).unwrap();
        let rows = rows.iter().filter(|row| row.typed_temporary.is_some()
            && row.terminal.stage == super::mechanical_receipt::MechanicalStage::Terminal).collect::<Vec<_>>();
        assert_eq!(rows.len(), 1, "one canonical temporary obligation");
        assert_eq!(rows[0].terminal.state, super::mechanical_receipt::MechanicalState::Applied);
        rows[0].typed_temporary.clone().unwrap()
    }).expect("pattern witness compiler context");

    let output = ast_emitted_source_of(input).expect("pattern emission");
    assert!(
        verify::type_checks_str(&output),
        "pattern output must type/borrow-check: {output}"
    );
    let declarations = inventory_source("pattern-output.rs", &output)
        .expect("pattern output declaration inventory");
    let temporaries = declarations
        .iter()
        .filter(|row| {
            row.owner == "pattern_target"
                && row.local_ordinal.is_some()
                && row.binding != "p"
                && row.type_is_fully_explicit
                && row.rendered_type.as_deref().is_some_and(|ty| {
                    ty.contains("Option<") && ty.contains('&') && ty.contains("i32")
                })
        })
        .collect::<Vec<_>>();
    assert_eq!(
        temporaries.len(),
        1,
        "the nullable pattern needs one explicitly typed temporary, without annotating its leaf or admitting ref-mut exclusions: {output}"
    );
    assert!(
        output.contains("= None") || output.contains("(None,"),
        "the typed temporary must support the null-to-None presentation: {output}"
    );
    assert!(
        output.contains("p.is_none()"),
        "the by-value pattern receives the nullable safe form: {output}"
    );

    let call_positions = ["record_before(log)", "stamp(log)", "record_after(log)"].map(|call| {
        assert_eq!(
            output.matches(call).count(),
            1,
            "each scalar effect must remain exactly once: {call}\n{output}"
        );
        output.find(call).unwrap()
    });
    let guard = output
        .find("if enabled")
        .expect("the original outer guard must survive");
    assert!(
        guard < call_positions[0]
            && call_positions[0] < call_positions[1]
            && call_positions[1] < call_positions[2],
        "temporary placement must retain the guarded scalar-effect order: {output}"
    );

    let temporary = temporaries[0];
    assert_eq!(temporary.binding, receipt_temporary);
    let pattern = declarations
        .iter()
        .find(|row| row.owner == "pattern_target" && row.binding == "p")
        .unwrap();
    assert!(pattern.type_span.is_none() && !pattern.type_is_fully_explicit);
    let carrier = pattern
        .typed_component
        .as_ref()
        .expect("independent parser verifies component custody");
    assert_eq!(carrier.temporary, receipt_temporary);
    assert!(matches!(
        pattern.effective_type_shape(),
        Some(super::delivery_custody::TypeShape::Option { .. })
    ));
    let type_span = temporary.type_span.expect("explicit temporary type span");
    let mut missing_type = output.clone();
    missing_type.replace_range(
        temporary.binding_span.hi as usize..type_span.hi as usize,
        "",
    );
    assert!(
        !verify::type_checks_str(&missing_type),
        "omitting the temporary type must expose lost inference, not pass vacuously: {missing_type}"
    );
}
