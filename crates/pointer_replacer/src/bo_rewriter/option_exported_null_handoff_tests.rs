//! Wave-6o (relay 113, R674-7 (2)): an exported entry's formal handed on
//! unchanged to a local callee whose own body NULL-tests it is nullable by
//! that test — the evidence sits one call down. binn's provided test passes
//! `INVALID_BINN` (NULL) to `binn_list_add`, which hands `list` to
//! `binn_list_add_raw`'s `item == NULL`; emitted as `&mut binn`, the entry
//! takes a null reference (UB; the run dies of SIGSEGV at batch 52).
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

fn decision_and_reason(input: &str, function: &str, binding: &str) -> (Decision, String) {
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
        let reason = match decision {
            Decision::Degraded(record) => record.reason.key().to_owned(),
            _ => String::new(),
        };
        (decision.clone(), reason)
    })
    .expect("fixture compiler context")
}

const INPUT: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, non_camel_case_types)]
#[repr(C)] pub struct binn { pub type_0: i32, pub writable: i32, pub count: i32 }
unsafe extern "C" fn binn_list_add_raw(mut item: *mut binn, mut value: i32) -> i32 {
    if item.is_null() || (*item).type_0 != 0xe0 as i32 || (*item).writable == 0 as i32 {
        return 0 as i32;
    }
    (*item).count += value;
    return 1 as i32;
}
#[no_mangle]
pub unsafe extern "C" fn binn_list_add(mut list: *mut binn, mut value: i32) -> i32 {
    if value < 0 as i32 { return 0 as i32; }
    return binn_list_add_raw(list, value);
}
"#;

/// The exported formal takes the optional form because the callee it is
/// handed to null-tests it; the hand-on is same-form (no `Some(..)` wrapper
/// around a reference the external caller may have passed as NULL).
#[test]
fn wave6o_exported_formal_handed_to_a_null_testing_callee_is_optional() {
    assert!(verify::type_checks_str(INPUT));
    let (decision, reason) = decision_and_reason(INPUT, "binn_list_add", "list");
    assert!(
        matches!(decision, Decision::Opt { slice: false, .. }),
        "the callee's null test makes the exported formal optional: {decision:?} {reason}"
    );
    let output = ast_emitted_source_of(INPUT).expect("native emission");
    assert!(output.contains("list: Option<&mut binn>"), "{output}");
    let flat = output.split_whitespace().collect::<String>();
    assert!(flat.contains("binn_list_add_raw(list,value)"), "{output}");
    assert!(!flat.contains("Some(list)"), "{output}");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// The control: the callee does not null-test its formal, so nothing says
/// NULL is expected and the exported formal stays a plain reference.
#[test]
fn wave6o_exported_formal_handed_to_a_non_testing_callee_stays_plain() {
    let input = INPUT.replace(
        "if item.is_null() || (*item).type_0",
        "if (*item).type_0",
    );
    assert!(verify::type_checks_str(&input));
    let (decision, reason) = decision_and_reason(&input, "binn_list_add", "list");
    assert!(
        matches!(decision, Decision::Ref { .. }),
        "no null test one call down, no optional: {decision:?} {reason}"
    );
}

/// The control on exposure: the same hand-on from a function that is NOT
/// exported stays plain — its callers are all in the program and their
/// actuals are the evidence (R462-1 (2) / P2), not the callee's test.
#[test]
fn wave6o_unexported_formal_handed_to_a_null_testing_callee_stays_plain() {
    let input = INPUT
        .replace("#[no_mangle]\npub unsafe extern \"C\" fn binn_list_add", "unsafe extern \"C\" fn binn_list_add")
        + "\nunsafe fn caller(mut b: binn) -> i32 { binn_list_add(&mut b, 1 as i32) }\n";
    assert!(verify::type_checks_str(&input));
    let (decision, reason) = decision_and_reason(&input, "binn_list_add", "list");
    assert!(
        matches!(decision, Decision::Ref { .. }),
        "an unexported formal's nullability is its callers' evidence: {decision:?} {reason}"
    );
}

/// The control on the entry's own use (the wave-6k closure fixture's `grand`):
/// an entry that dereferences the formal itself is not written to receive
/// NULL — a NULL actual is already the input's UB there (§28) — so the
/// callee's test one call down is no evidence for it.
#[test]
fn wave6o_exported_formal_dereferenced_by_the_entry_stays_plain() {
    let input = INPUT.replace(
        "if value < 0 as i32 { return 0 as i32; }",
        "if value < 0 as i32 { return 0 as i32; }\n    (*list).count = 0 as i32;",
    );
    assert!(verify::type_checks_str(&input));
    let (decision, reason) = decision_and_reason(&input, "binn_list_add", "list");
    assert!(
        matches!(decision, Decision::Ref { .. }),
        "the entry's own dereference rules NULL out: {decision:?} {reason}"
    );
}
