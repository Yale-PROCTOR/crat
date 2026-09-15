//! Wave-6o reductions of binn::binn_load and binn::binn_get_int32: a thin
//! optional subject reaching a `c_void` position through a cast at a call.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe extern "C" { fn memset(p: *mut core::ffi::c_void, v: i32, n: usize) -> *mut core::ffi::c_void; }
#[repr(C)] struct Binn { header: i32, allocated: i32, ptr: *mut core::ffi::c_void }
"#;

/// The subject stays optional, its void-cast call site carries an applied
/// `option-to-raw-null-map` receipt, and the emitted program type-checks.
fn admitted_void_cast(input: &str, function: &str, binding: &str, expected_bridge: &str) {
    assert!(verify::type_checks_str(input));
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.param_name.as_deref() == Some(binding)
            })
            .expect("corpus-derived subject");
        assert!(
            matches!(decision, Decision::Opt { slice: false, .. }),
            "void cast must keep {function}::{binding} optional: {decision:?}"
        );
        assert!(
            table.option_receipts.iter().any(|receipt| {
                receipt.operation == "call-raw"
                    && receipt.adapter == "option-to-raw-null-map"
                    && receipt.obligation.intended_terminal_state
                        == super::mechanical_receipt::MechanicalState::Applied
            }),
            "void cast needs its applied option-to-raw-null-map receipt: {:?}",
            table
                .option_receipts
                .iter()
                .map(|receipt| (
                    receipt.operation.clone(),
                    receipt.adapter.clone(),
                    receipt.obligation.intended_terminal_state,
                    receipt.obligation.intended_terminal_reason.clone()
                ))
                .collect::<Vec<_>>()
        );
    })
    .expect("fixture compiler context");
    let output = ast_emitted_source_of(input).expect("native emission");
    assert!(output.contains(&format!("{binding}: Option<")), "{output}");
    assert!(
        output
            .split_whitespace()
            .collect::<String>()
            .contains(&expected_bridge.split_whitespace().collect::<String>()),
        "void bridge must map None to null and erase the pointee: {output}"
    );
    eprintln!("WAVE6O_VOID_OUTPUT_BEGIN {function}\n{output}\nWAVE6O_VOID_OUTPUT_END");
    assert!(
        verify::type_checks_str(&output),
        "emitted void cast must compile: {output}"
    );
}

#[test]
fn wave6o_binn_load_mutable_option_at_void_mut() {
    let input = format!(
        r#"{PRELUDE}
unsafe fn binn_load(value: *mut Binn) -> i32 {{
    if value.is_null() {{ return 0; }}
    memset(value as *mut core::ffi::c_void, 0, core::mem::size_of::<Binn>());
    (*value).header = 0x1f22b11f;
    return 1;
}}
"#
    );
    admitted_void_cast(
        &input,
        "binn_load",
        "value",
        "memset(value.as_deref_mut().map_or(core::ptr::null_mut::<core::ffi::c_void>(), |value| core::ptr::from_mut(value).cast::<core::ffi::c_void>()),",
    );
}

#[test]
fn wave6o_binn_get_int32_mutable_option_at_local_void_mut() {
    let input = format!(
        r#"{PRELUDE}
unsafe fn copy_int_value(psource: *mut core::ffi::c_void, pdest: *mut core::ffi::c_void, source_type: i32) -> i32 {{
    if source_type == 0 {{ *(pdest as *mut i32) = *(psource as *mut i32); return 1; }}
    return 0;
}}
unsafe fn binn_get_int32(value: *mut Binn, pint: *mut i32) -> i32 {{
    if value.is_null() || pint.is_null() {{ return 0; }}
    if (*value).header == 0xf2 {{
        return copy_int_value((*value).ptr, pint as *mut core::ffi::c_void, 0);
    }}
    *pint = (*value).allocated;
    return 1;
}}
"#
    );
    admitted_void_cast(
        &input,
        "binn_get_int32",
        "pint",
        "pint.as_deref_mut().map_or(core::ptr::null_mut::<core::ffi::c_void>(), |value| core::ptr::from_mut(value).cast::<core::ffi::c_void>()), 0)",
    );
}

#[test]
fn wave6o_shared_option_at_void_const() {
    let input = format!(
        r#"{PRELUDE}
unsafe extern "C" {{ fn observe(p: *const core::ffi::c_void); }}
unsafe fn look(value: *const Binn) -> i32 {{
    if value.is_null() {{ return 0; }}
    observe(value as *const core::ffi::c_void);
    return (*value).header;
}}
"#
    );
    admitted_void_cast(
        &input,
        "look",
        "value",
        "observe(value.as_deref().map_or(core::ptr::null::<core::ffi::c_void>(), |value| core::ptr::from_ref(value).cast::<core::ffi::c_void>()))",
    );
}

/// A shared optional at a `*mut c_void` position without negative-write
/// evidence keeps the typed shared-to-mutable hold: no `&T -> &mut T` cast.
#[test]
fn wave6o_shared_option_at_void_mut_keeps_typed_hold() {
    let input = format!(
        r#"{PRELUDE}
unsafe extern "C" {{ fn scribble(p: *mut core::ffi::c_void); }}
unsafe fn peek(value: *const Binn) -> i32 {{
    if value.is_null() {{ return 0; }}
    scribble(value as *mut core::ffi::c_void);
    return (*value).header;
}}
"#
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let table = super::decide_table(tcx).expect("typed refusal decisions");
        for (subject, decision) in &table.entries {
            eprintln!("WAVE6O_HOLD_DECISION {} {decision:?}", subject.label);
        }
        for receipt in &table.option_receipts {
            eprintln!(
                "WAVE6O_HOLD_RECEIPT {} {} {:?} {:?}",
                receipt.operation,
                receipt.adapter,
                receipt.obligation.intended_terminal_state,
                receipt.obligation.intended_terminal_reason
            );
        }
        assert!(
            !table.option_receipts.iter().any(|receipt| {
                receipt.operation == "call-raw"
                    && receipt.adapter == "option-to-raw-null-map"
                    && receipt.obligation.intended_terminal_state
                        == super::mechanical_receipt::MechanicalState::Applied
            }),
            "a shared optional must not be bridged to a writable void view: {:?}",
            table.option_receipts
        );
        // The hold is the void cell's own negative-write guard, not a later
        // gate: its typed reason names the absent evidence.
        assert!(
            table.option_receipts.iter().any(|receipt| {
                receipt.operation == "call-raw"
                    && format!("{:?}", receipt.obligation.intended_terminal_reason)
                        .contains("raw-boundary-shared-to-mut:negative-write-absent")
            }),
            "the void cell must hold on absent negative-write evidence: {:?}",
            table.option_receipts
        );
    })
    .expect("refusal compiler context");
    let output = ast_emitted_source_of(&input).expect("refusal emission");
    assert!(!output.contains("cast_mut()"), "{output}");
    assert!(verify::type_checks_str(&output), "{output}");
}
