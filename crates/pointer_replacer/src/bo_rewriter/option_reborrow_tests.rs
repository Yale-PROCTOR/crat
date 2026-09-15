//! Wave-6o (relay 008): one reborrow per call for a mutable optional root
//! accessed at two or more argument positions — wave-6p's
//! `binn_load` → `binn_is_valid(data, &mut (*value).type_0, &mut (*value).count, ..)`
//! (its report 002 claim 8: E0499 from three `value.as_mut().unwrap()` in one call).
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
#[repr(C)] struct Binn { header: i32, type_0: i32, count: i32, size: i32 }
"#;

fn decision_and_receipts(input: &str, function: &str, binding: &str) -> (Decision, Vec<String>) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.param_name.as_deref() == Some(binding)
            })
            .expect("corpus-derived subject");
        let receipts = table
            .option_receipts
            .iter()
            .filter(|receipt| {
                receipt.operation == "call-reborrow"
                    && receipt.obligation.planned.owner_path.ends_with(function)
            })
            .map(|receipt| {
                format!(
                    "{}:{:?}:{:?}",
                    receipt.adapter,
                    receipt.obligation.intended_terminal_state,
                    receipt.obligation.intended_terminal_reason
                )
            })
            .collect();
        let _ = subject;
        (decision.clone(), receipts)
    })
    .expect("fixture compiler context")
}

fn hoisted(input: &str, function: &str, binding: &str, expected: &str) {
    assert!(verify::type_checks_str(input));
    let (decision, receipts) = decision_and_receipts(input, function, binding);
    assert!(
        matches!(
            decision,
            Decision::Opt {
                mutable: true,
                slice: false,
                ..
            }
        ),
        "{function}::{binding} must stay a mutable optional: {decision:?}"
    );
    assert!(
        receipts
            .iter()
            .any(|receipt| receipt.starts_with("option-call-reborrow:Applied:None")),
        "the call must carry its applied reborrow receipt: {receipts:?}"
    );
    let output = ast_emitted_source_of(input).expect("native emission");
    assert!(
        output
            .split_whitespace()
            .collect::<String>()
            .contains(&expected.split_whitespace().collect::<String>()),
        "the call must reborrow once: expected `{expected}` in\n{output}"
    );
    eprintln!("WAVE6O_REBORROW_OUTPUT_BEGIN {function}\n{output}\nWAVE6O_REBORROW_OUTPUT_END");
    assert!(
        verify::type_checks_str(&output),
        "emitted call must compile: {output}"
    );
}

/// A mutable field view and a value read of the same optional root in one call.
#[test]
fn wave6o_binn_load_two_accesses_of_one_optional_root_reborrow_once() {
    let input = format!(
        r#"{PRELUDE}
unsafe fn binn_is_valid(ptype: *mut i32, count: i32) -> i32 {{
    if ptype.is_null() {{ return 0; }}
    *ptype = count;
    return 1;
}}
unsafe fn binn_load(mut value: *mut Binn) -> i32 {{
    if value.is_null() {{ return 0; }}
    (*value).header = 0x1f22b11f;
    if binn_is_valid(&mut (*value).type_0, (*value).count) == 0 {{
        return 0;
    }}
    return 1;
}}
"#
    );
    hoisted(
        &input,
        "binn_load",
        "value",
        "if ({ let value = value.as_deref_mut().unwrap(); binn_is_valid(Some(&mut (*value).type_0), (*value).count) }) == 0 {",
    );
}

/// Two value reads of the root at a foreign callee, in a statement position.
#[test]
fn wave6o_two_reads_of_one_optional_root_at_a_foreign_callee_reborrow_once() {
    let input = format!(
        r#"{PRELUDE}
unsafe extern "C" {{ fn record(a: i32, b: i32); }}
unsafe fn note(mut value: *mut Binn) -> i32 {{
    if value.is_null() {{ return 0; }}
    (*value).count += 1;
    record((*value).type_0, (*value).count);
    return (*value).count;
}}
"#
    );
    hoisted(
        &input,
        "note",
        "value",
        "({ let value = value.as_deref_mut().unwrap(); record((*value).type_0, (*value).count) });",
    );
}

/// A null test of the root inside the same call is not a dereference: no
/// hoist (the block would shadow the Option); the skip is recorded on the
/// receipt and the site keeps its per-access rendering.
#[test]
fn wave6o_null_test_inside_the_call_keeps_typed_hold() {
    let input = format!(
        r#"{PRELUDE}
unsafe extern "C" {{ fn record(a: i32, b: i32); }}
unsafe fn note(mut value: *mut Binn) -> i32 {{
    if value.is_null() {{ return 0; }}
    (*value).count += 1;
    record((*value).type_0, value.is_null() as i32);
    return 1;
}}
"#
    );
    assert!(verify::type_checks_str(&input));
    let (_, receipts) = decision_and_receipts(&input, "note", "value");
    assert!(
        receipts.iter().any(|receipt| receipt
            .starts_with("skipped:option-call-reborrow:non-dereference-use-inside-call:Applied")),
        "the non-dereference use must be a recorded skip: {receipts:?}"
    );
    let output = ast_emitted_source_of(&input).expect("hold emission");
    assert!(
        !output.contains("as_deref_mut().unwrap(); record"),
        "{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}
