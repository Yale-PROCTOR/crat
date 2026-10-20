//! Wave-6o (relay 009/013): the two remaining raw-return arms — a local
//! returned under a CAST (binn `compress_int`: `return pvalue as *mut c_void`)
//! and a local returned as the tail of an `if` arm (lil `lil_find_var`:
//! `return if !r.is_null() { r } else { .. }`).
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

const ALLOCATOR: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe extern "C" { fn myMalloc(size: usize) -> *mut core::ffi::c_void; }
"#;

fn admitted_return(input: &str, function: &str, binding: &str, expected: &str) {
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
            .expect("corpus-derived local");
        assert!(
            matches!(decision, Decision::Opt { slice: false, .. }),
            "the return arm must admit {function}::{binding}: {decision:?}"
        );
        assert!(
            table.option_receipts.iter().any(|receipt| {
                (receipt.operation == "return-raw" || receipt.operation == "address-observation")
                    && receipt.obligation.intended_terminal_state
                        == super::mechanical_receipt::MechanicalState::Applied
                    && receipt.obligation.planned.owner_path.ends_with(function)
            }),
            "the return needs its applied receipt (a bare / arm return: the consuming move; a cast return: the address view)"
        );
    })
    .expect("fixture compiler context");
    let output = ast_emitted_source_of(input).expect("native emission");
    assert!(
        output
            .split_whitespace()
            .collect::<String>()
            .contains(&expected.split_whitespace().collect::<String>()),
        "expected `{expected}` in\n{output}"
    );
    eprintln!("WAVE6O_RETARM_OUTPUT_BEGIN {function}\n{output}\nWAVE6O_RETARM_OUTPUT_END");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// A written-through local returned under a cast: the cast is the address
/// arm's `ptr-cast` observation — the optional operand is deferred to that
/// view (spelled in the local's own type) and the cast stays.
#[test]
fn wave6o_cast_return_bridges_the_local_and_keeps_the_cast() {
    let input = format!(
        r#"{ALLOCATOR}
unsafe fn compress_int(size: usize) -> *mut core::ffi::c_void {{
    let mut pvalue: *mut i8 = 0 as *mut i8;
    pvalue = myMalloc(size) as *mut i8;
    if !pvalue.is_null() {{ *pvalue = 0x20; }}
    return pvalue as *mut core::ffi::c_void;
}}
"#
    );
    admitted_return(
        &input,
        "compress_int",
        "pvalue",
        "return pvalue.as_deref_mut().map_or(core::ptr::null_mut::<i8>(), core::ptr::from_mut) as *mut core::ffi::c_void;",
    );
}

/// A written-through local returned as the tail of an `if` arm.
#[test]
fn wave6o_conditional_return_bridges_the_arm() {
    let input = format!(
        r#"{ALLOCATOR}
#[repr(C)] struct Var {{ id: i32 }}
unsafe extern "C" {{ fn fallback() -> *mut Var; }}
unsafe fn lil_find_var(id: i32) -> *mut Var {{
    let mut r: *mut Var = 0 as *mut Var;
    r = myMalloc(core::mem::size_of::<Var>()) as *mut Var;
    if !r.is_null() {{ (*r).id = id; }}
    return if !r.is_null() {{ r }} else if id == 0 {{ 0 as *mut Var }} else {{ fallback() }};
}}
"#
    );
    admitted_return(
        &input,
        "lil_find_var",
        "r",
        "return if r.is_some() { r.map_or(core::ptr::null_mut::<crate::Var>(), |value| core::ptr::from_mut(value)) } else if id == 0 { 0 as *mut Var } else { fallback() };",
    );
}

/// The corpus `compress_int::pvalue` itself is a pass-through (assigned from a
/// raw parameter, never written through) cast to a `*mut` at its return: a
/// shared optional's view must never become writable, so the typed hold
/// stands.
#[test]
fn wave6o_cast_return_of_a_pass_through_keeps_the_typed_hold() {
    let input = format!(
        r#"{ALLOCATOR}
unsafe fn compress_int(psource: *mut core::ffi::c_void) -> *mut core::ffi::c_void {{
    let mut pvalue: *mut i8 = 0 as *mut i8;
    pvalue = psource as *mut i8;
    if pvalue.is_null() {{ return 0 as *mut core::ffi::c_void; }}
    return pvalue as *mut core::ffi::c_void;
}}
"#
    );
    assert!(verify::type_checks_str(&input));
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let table = super::decide_table(tcx).expect("typed refusal decisions");
        assert!(
            table.option_receipts.iter().any(|receipt| {
                receipt.operation == "address-observation"
                    && format!("{:?}", receipt.obligation.intended_terminal_reason)
                        .contains("option-address-view:shared-to-mut-cast")
            }),
            "the pass-through must hold at its return: {:?}",
            table.option_receipts
        );
    })
    .expect("refusal compiler context");
    let output = ast_emitted_source_of(&input).expect("refusal emission");
    assert!(verify::type_checks_str(&output), "{output}");
}
