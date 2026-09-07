//! Item-5 RED declaration presentation controls.

use super::{
    decision::{Decision, DegradeReason},
    delivery_custody::{Declaration, TypeShape, inventory_source},
    emit_tests::ast_emitted_source_of,
    verify,
};

fn decision_with_model(
    input: &str,
    owner: &str,
    binding: &str,
    expected: super::SlotKind,
) -> Decision {
    let owner = owner.to_owned();
    let binding = binding.to_owned();
    ::utils::compilation::run_compiler_on_str(input, move |tcx| {
        let (table, ctx) =
            super::decide_table_with_ctx(tcx).expect("declaration fixture decisions");
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.def_path_str(subject.fn_did.to_def_id()) == owner
                    && subject.param_name.as_deref() == Some(binding.as_str())
            })
            .unwrap_or_else(|| panic!("missing {owner}::{binding}: {:?}", table.entries));
        let kind = ctx
            .slots
            .fn_local_slots
            .get(&subject.fn_did)
            .and_then(|slots| slots.slot_for_local_depth(subject.local, 0))
            .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)))
            .copied();
        assert_eq!(
            kind,
            Some(expected),
            "{owner}::{binding} must exercise the intended frozen model fact"
        );
        decision.clone()
    })
    .expect("declaration compiler context")
}

fn emitted(input: &str, aliases: &[&str]) -> String {
    assert!(
        verify::type_checks_str(input),
        "declaration fixture input must type-check"
    );
    let output = ast_emitted_source_of(input).expect("declaration fixture emission");
    assert!(
        verify::type_checks_str(&output),
        "emitted declarations must type/borrow-check: {output}"
    );
    for alias in aliases {
        assert!(
            input.contains(alias),
            "the original typedef spelling must be present: {alias}"
        );
        assert!(
            output.contains(alias),
            "per-declaration emission changed the shared typedef: {alias}\n{output}"
        );
    }
    output
}

fn declaration(output: &str, owner: &str, binding: &str) -> Declaration {
    let rows =
        inventory_source("declaration-output.rs", output).expect("emitted declaration inventory");
    let matching = rows
        .into_iter()
        .filter(|row| row.owner == owner && row.binding == binding)
        .collect::<Vec<_>>();
    assert_eq!(
        matching.len(),
        1,
        "exact declaration identity {owner}::{binding}"
    );
    matching.into_iter().next().unwrap()
}

#[test]
fn decl_w1_alias_parameter_read_gets_an_explicit_reference() {
    let input = "type Ptr = *const i32; pub unsafe fn read(p: Ptr) -> i32 { *p }";
    decision_with_model(input, "read", "p", super::SlotKind::Ref);
    let output = emitted(input, &["type Ptr = *const i32;"]);
    let row = declaration(&output, "read", "p");
    assert!(
        matches!(row.type_shape, TypeShape::Reference { mutable: false, .. }),
        "{output}"
    );
    assert!(row.type_is_fully_explicit);
}

#[test]
fn decl_w1_context_lut_local_keeps_its_nullable_array_result() {
    let input = "type ContextLut = *const u8; static TABLE: [u8; 4] = [1, 2, 3, 4];\n\
        pub unsafe fn lookup() -> u8 {\n\
            let p: ContextLut = TABLE.as_ptr().offset(1) as *const u8;\n\
            if p.is_null() { 0 } else { *p }\n\
        }";
    decision_with_model(input, "lookup", "p", super::SlotKind::Ref);
    let output = emitted(input, &["type ContextLut = *const u8;"]);
    let row = declaration(&output, "lookup", "p");
    assert!(
        matches!(&row.type_shape, TypeShape::Option { payload, .. }
        if matches!(payload.as_ref(), TypeShape::Reference { mutable: false, .. })),
        "{output}"
    );
    assert!(row.type_is_fully_explicit);
    assert!(
        output.contains(".as_ref()"),
        "raw nullable construction needs its value adapter: {output}"
    );
}

#[test]
fn decl_w1_null_alias_needs_the_changed_position_type_for_inference() {
    let input = "type Ptr = *const i32; pub unsafe fn null_count() -> u32 {\n\
        let p: Ptr = 0 as *const i32;\n\
        if p.is_null() { 0 } else { (*p).count_ones() }\n\
    }";
    decision_with_model(input, "null_count", "p", super::SlotKind::Ref);
    let output = emitted(input, &["type Ptr = *const i32;"]);
    let row = declaration(&output, "null_count", "p");
    assert!(
        matches!(row.type_shape, TypeShape::Option { .. }),
        "{output}"
    );
    assert!(
        output.contains("= None"),
        "null construction must retain Option presentation: {output}"
    );
    let type_span = row
        .type_span
        .expect("the changed position must have an explicit type");
    let mut missing_type = output.clone();
    missing_type.replace_range(row.binding_span.hi as usize..type_span.hi as usize, "");
    assert!(
        !verify::type_checks_str(&missing_type),
        "this witness must actually lose inference if its explicit type is omitted: {missing_type}"
    );
}

#[test]
fn decl_w1_alias_arithmetic_parameter_gets_a_slice_only_under_its_normal_gates() {
    let input = "type Bytes = *const u8; pub unsafe fn at(p: Bytes) -> u8 { *p.offset(1) }";
    decision_with_model(input, "at", "p", super::SlotKind::Ref);
    let output = emitted(input, &["type Bytes = *const u8;"]);
    let row = declaration(&output, "at", "p");
    assert!(
        matches!(&row.type_shape, TypeShape::Reference { mutable: false, pointee }
        if matches!(pointee.as_ref(), TypeShape::Slice { .. })),
        "{output}"
    );
}

#[test]
fn decl_w1_shared_alias_changes_only_the_supported_function_declaration() {
    let input = "type Ptr = *mut i32;\n\
        pub unsafe fn read(p: Ptr) -> i32 { *p }\n\
        pub unsafe fn opaque(src: Ptr, clear: bool) -> i32 { let mut q: Ptr = 0 as *mut i32; q = src; if clear { q = 0 as *mut i32; } if q.is_null() { 0 } else { *q += 1; *q } }";
    decision_with_model(input, "read", "p", super::SlotKind::Ref);
    decision_with_model(input, "opaque", "q", super::SlotKind::Raw);
    let output = emitted(input, &["type Ptr = *mut i32;"]);
    let changed = declaration(&output, "read", "p");
    let unchanged = declaration(&output, "opaque", "q");
    assert!(
        matches!(changed.type_shape, TypeShape::Reference { .. }),
        "{output}"
    );
    assert_eq!(
        unchanged.explicit_type.as_deref(),
        Some("Ptr"),
        "the model-Raw sibling retains its alias spelling"
    );
}

#[test]
fn decl_w1_cross_module_alias_preserves_the_resolved_generic_pointee() {
    let input = "mod definitions {\n\
        #[repr(C)] pub struct Cell<T> { pub value: T }\n\
        pub type Handle = *const Cell<u16>;\n\
        }\n\
        mod client {\n\
            pub struct Cell { pub unrelated: i32 }\n\
            pub unsafe fn read(p: crate::definitions::Handle) -> u16 { (*p).value }\n\
        }";
    decision_with_model(input, "client::read", "p", super::SlotKind::Ref);
    let output = emitted(input, &["pub type Handle = *const Cell<u16>;"]);
    let row = declaration(&output, "client::read", "p");
    let TypeShape::Reference {
        mutable: false,
        pointee,
    } = row.type_shape
    else {
        panic!("cross-module alias did not become the settled reference: {output}");
    };
    assert!(
        matches!(pointee.as_ref(), TypeShape::Named { path }
        if path.ends_with("definitions::Cell<u16>")),
        "use-site Cell is a different type; the resolved path and type argument must survive: {output}"
    );
}

const ALIAS_RETURN_FLOW: &str = "type Ptr = *const i32;\n\
    unsafe fn identity(p: Ptr) -> Ptr { p }\n\
    pub unsafe fn read(src: *const i32) -> i32 { *identity(src) }";

/// Item-5 fixture-authoring premise correction 2: the existing E2 return gate
/// requires a closed-world attestation. Supply it explicitly, never by changing
/// process environment or by weakening production lifetime eligibility.
fn alias_return_output(attested: bool) -> String {
    assert!(verify::type_checks_str(ALIAS_RETURN_FLOW));
    let output = ::utils::compilation::run_compiler_on_str(ALIAS_RETURN_FLOW, move |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("alias-return AST capture");
        let attestation = attested.then_some(super::WholeProgramAttestation::FrozenBenchmarkGraph);
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((super::A5Mode::PreciseReplay, attestation)),
        )
        .expect("configured alias-return decisions");
        assert_eq!(ctx.analysis.attestation, attestation);
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.def_path_str(subject.fn_did.to_def_id()) == "identity"
                    && subject.param_name.as_deref() == Some("p")
            })
            .expect("alias-return parameter");
        let node = (subject.fn_did, subject.hir_id);
        if attested {
            assert!(
                matches!(decision, Decision::Ref { .. }),
                "attested alias parameter: {decision:?}"
            );
            assert!(
                ctx.lifetime_eligibility.return_permit(node).is_some(),
                "the positive must have a real return-origin permit"
            );
            let lifetimes = table
                .lifetime_plan
                .function(subject.fn_did)
                .expect("identity lifetime plan");
            let argument = lifetimes
                .lifetime_for(super::decision::lifetime::FnSignatureSlot::arg(1, 0, 0))
                .expect("input lifetime");
            let result = lifetimes
                .lifetime_for(super::decision::lifetime::FnSignatureSlot::RETURN)
                .expect("return lifetime");
            assert_eq!(
                argument, result,
                "identity must return a borrow of its input"
            );
        } else {
            assert!(
                ctx.lifetime_eligibility.return_permit(node).is_none(),
                "unattested return cannot acquire a permit"
            );
            assert!(
                matches!(decision, Decision::Degraded(_)),
                "unattested alias parameter: {decision:?}"
            );
        }
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("configured alias-return plan");
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &emission.plan.held_classes(),
            &std::collections::BTreeSet::new(),
            &table,
        )
        .expect("alias-return class disposition");
        super::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_a5_raw_calls),
        )
        .expect("configured alias-return emission")
        .0
        .into_values()
        .next()
        .expect("alias-return root")
    })
    .expect("configured alias-return compiler context");
    assert!(
        output.contains("type Ptr = *const i32;"),
        "the typedef stays unchanged: {output}"
    );
    assert!(
        verify::type_checks_str(&output),
        "alias-return output must type/borrow-check: {output}"
    );
    output
}

#[test]
fn decl_w1_alias_parameter_return_and_call_keep_lifetime_consistency() {
    decision_with_model(ALIAS_RETURN_FLOW, "identity", "p", super::SlotKind::Ref);
    let output = alias_return_output(true);
    let row = declaration(&output, "identity", "p");
    assert!(
        matches!(row.type_shape, TypeShape::Reference { .. }),
        "the alias parameter must survive its return/call dependency class: {output}"
    );
    assert!(
        output.contains("identity("),
        "the local call remains part of the checked witness: {output}"
    );
}

#[test]
fn decl_unattested_alias_return_keeps_its_raw_alias() {
    decision_with_model(ALIAS_RETURN_FLOW, "identity", "p", super::SlotKind::Ref);
    let output = alias_return_output(false);
    assert_eq!(
        declaration(&output, "identity", "p")
            .explicit_type
            .as_deref(),
        Some("Ptr"),
        "the declaration family must not bypass the existing return-lifetime gate: {output}"
    );
}

#[test]
fn decl_existing_reference_pattern_stays_an_excluded_reference() {
    let input = "pub unsafe fn existing(p: &mut *const i32) -> bool {\n\
        let ref mut fresh = *p; (*fresh).is_null()\n\
    }";
    let reason = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("existing-reference decisions");
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.param_name.as_deref() == Some("fresh"))
            .expect("existing ref-pattern local");
        match decision {
            Decision::Degraded(record) => record.reason.clone(),
            other => panic!("already-reference pattern must not become a promotion: {other:?}"),
        }
    })
    .expect("existing-reference compiler context");
    assert_eq!(
        reason,
        DegradeReason::UnsupportedDeclShape { shape: "reference" }
    );
    let output = emitted(input, &[]);
    assert!(output.contains("let ref mut fresh = *p;"), "{output}");
    assert!(matches!(
        declaration(&output, "existing", "p").type_shape,
        TypeShape::Reference { mutable: true, .. }
    ));
}

#[test]
fn decl_model_raw_alias_copy_stays_raw() {
    let input = "type Ptr = *mut i32; pub unsafe fn raw_alias(src: Ptr, clear: bool) -> i32 {\n\
        let mut copied: Ptr = 0 as *mut i32; copied = src; if clear { copied = 0 as *mut i32; }\n\
        if copied.is_null() { 0 } else { *copied += 1; *copied }\n\
    }";
    for binding in ["src", "copied"] {
        let decision = decision_with_model(input, "raw_alias", binding, super::SlotKind::Raw);
        assert!(
            matches!(decision, Decision::Degraded(_)),
            "model Raw cannot become safe from alias spelling"
        );
    }
    let output = emitted(input, &["type Ptr = *mut i32;"]);
    for binding in ["src", "copied"] {
        assert_eq!(
            declaration(&output, "raw_alias", binding)
                .explicit_type
                .as_deref(),
            Some("Ptr"),
            "{output}"
        );
    }
}

#[test]
fn decl_alias_with_an_inaccessible_pointee_keeps_the_usable_alias() {
    let input = "mod api { mod hidden { pub struct Payload<T> { pub value: T } } pub type Ptr = *const hidden::Payload<u8>; } mod caller { pub unsafe fn take(p: crate::api::Ptr) -> u8 { (*p).value } }";
    let decision = decision_with_model(input, "caller::take", "p", super::SlotKind::Ref);
    assert!(
        matches!(decision, Decision::Degraded(ref record) if record.reason == DegradeReason::UnsupportedDeclShape { shape: "alias" })
    );
    let output = emitted(input, &["pub type Ptr = *const hidden::Payload<u8>;"]);
    assert_eq!(
        declaration(&output, "caller::take", "p")
            .explicit_type
            .as_deref(),
        Some("crate::api::Ptr")
    );
}

#[test]
fn decl_alias_from_the_private_pointees_own_module_can_be_named() {
    let input = "mod api { mod hidden { pub struct Payload<T> { pub value: T } } pub type Ptr = *const hidden::Payload<u8>; pub unsafe fn take(p: Ptr) -> u8 { (*p).value } }";
    decision_with_model(input, "api::take", "p", super::SlotKind::Ref);
    let output = emitted(input, &["pub type Ptr = *const hidden::Payload<u8>;"]);
    assert!(matches!(
        declaration(&output, "api::take", "p").type_shape,
        TypeShape::Reference { .. }
    ));
}

#[test]
fn decl_w1_receipt_tracks_the_annotation_and_its_terminal_owner() {
    use super::mechanical_receipt::{self as receipt, MechanicalStage, MechanicalState};
    ::utils::compilation::run_compiler_on_str(
        "type Ptr = *const i32; pub unsafe fn read(p: Ptr) -> i32 { *p }",
        |tcx| {
            let (table, ctx) = super::decide_table_with_ctx(tcx).unwrap();
            let emission =
                super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
                    .unwrap();
            let none = Default::default();
            let rows = emission.plan.declaration_receipt_rows(&none);
            let events = emission.plan.mechanical_receipts(&none).0;
            assert_eq!(
                receipt::reconcile_declaration_shape_rows(&rows, &events).unwrap(),
                1
            );
            let terminal = rows
                .iter()
                .find(|row| row.terminal.stage == MechanicalStage::Terminal)
                .unwrap();
            assert_eq!(terminal.original_type_form, "Ptr");
            assert_eq!(terminal.settled_emitted_type, "&i32");
            assert_eq!(terminal.terminal.state, MechanicalState::Applied);
            assert_eq!(terminal.initializer_kind, "parameter");
            assert!(terminal.typed_temporary.is_none());
            let reverted =
                std::collections::BTreeSet::from([terminal.terminal.obligation_key.owner_class]);
            let rows = emission.plan.declaration_receipt_rows(&reverted);
            let events = emission.plan.mechanical_receipts(&reverted).0;
            receipt::reconcile_declaration_shape_rows(&rows, &events).unwrap();
            assert!(
                rows.iter()
                    .all(|row| row.terminal_class_result == MechanicalState::Dropped)
            );
        },
    )
    .unwrap();
}

#[test]
fn decl_void_alias_uses_the_real_core_type_without_renaming_a_user_type() {
    for (input, owner, expected) in [
        (
            "type Ptr = *const core::ffi::c_void; pub fn null(p: Ptr) -> bool { p.is_null() }",
            "null",
            "core::ffi::c_void",
        ),
        (
            "#[allow(non_camel_case_types)] pub struct c_void { pub value: i32 } type Ptr = *const c_void; pub unsafe fn read(p: Ptr) -> i32 { (*p).value }",
            "read",
            "crate::c_void",
        ),
    ] {
        decision_with_model(input, owner, "p", super::SlotKind::Ref);
        let output = emitted(input, &[]);
        let row = declaration(&output, owner, "p");
        assert!(row.type_is_fully_explicit);
        assert!(
            row.rendered_type
                .as_deref()
                .is_some_and(|ty| ty.contains(expected)),
            "{output}"
        );
        assert!(
            !row.rendered_type.as_deref().unwrap().contains("libc::"),
            "{output}"
        );
    }
}

#[test]
fn decl_static_and_const_alias_storage_keeps_its_own_explicit_input_type() {
    let input = "type Ptr = *const i32; static mut ROOT: Ptr = 0 as *const i32; const EMPTY: Ptr = 0 as *const i32; pub unsafe fn read(p: Ptr) -> i32 { *p }";
    decision_with_model(input, "read", "p", super::SlotKind::Ref);
    let output = emitted(input, &["type Ptr = *const i32;"]);
    assert!(matches!(
        declaration(&output, "read", "p").type_shape,
        TypeShape::Reference { .. }
    ));
    for storage in [
        "static mut ROOT: Ptr = 0 as *const i32;",
        "const EMPTY: Ptr = 0 as *const i32;",
    ] {
        assert!(
            output.contains(storage),
            "the function's changed annotation must not retarget an unrelated global declaration: {output}"
        );
    }
}
