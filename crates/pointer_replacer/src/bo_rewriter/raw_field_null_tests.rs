//! Wave-6o (relay 096 / fan-out 008 finding 12): a local read from a RAW
//! field that the program writes the null literal into is nullable. That null
//! literal is the value's construction site, one field away. json.h's
//! `json_extract_get_{array,object}_size::element` is initialised from
//! `(*array).start`, which the parser sets to null for an empty array, and is
//! advanced by `(*element).next`, which is null on the last element. Neither
//! function tests `element` for null, because the loop is bounded by the
//! count. A plain reference there is `&*null` on a UB-free input (Miri:
//! wave-6o report 082).
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

fn decision_of(input: &str, function: &str, binding: &str) -> Decision {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.label.ends_with(&format!("::{binding}"))
            })
            .map(|(_, decision)| decision.clone())
            .expect("the fixture's subject")
    })
    .expect("fixture compiler context")
}

/// json.h's shape, reduced: the element fields stay raw (the parser carves
/// elements out of a byte arena), `start` and `next` receive the null
/// literal, and the size walk is count-bounded.
const INPUT: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_camel_case_types)]
#[derive(Copy, Clone)] #[repr(C)] pub struct value_s { pub payload: *mut u8, pub type_0: usize }
#[derive(Copy, Clone)] #[repr(C)] pub struct element_s { pub value: *mut value_s, pub next: *mut element_s }
#[derive(Copy, Clone)] #[repr(C)] pub struct array_s { pub start: *mut element_s, pub length: usize }
#[derive(Copy, Clone)] #[repr(C)] pub struct result_s { pub dom_size: usize, pub data_size: usize }
pub unsafe fn value_size(value: *const value_s) -> result_s {
    result_s { dom_size: (*value).type_0, data_size: 0 }
}
pub unsafe fn array_size(array: *const array_s) -> result_s {
    let mut result = result_s { dom_size: 0, data_size: 0 };
    let mut i: usize = 0;
    let mut element: *const element_s = (*array).start;
    while i < (*array).length {
        let value_result = value_size((*element).value);
        result.dom_size = result.dom_size.wrapping_add(value_result.dom_size);
        element = (*element).next;
        i = i.wrapping_add(1);
    }
    return result;
}
pub unsafe fn parse(array: *mut array_s, dom: *mut u8, n: usize) {
    let mut previous: *mut element_s = 0 as *mut element_s;
    let mut k: usize = 0;
    while k < n {
        let element = dom.add(k * 16) as *mut element_s;
        if previous.is_null() { (*array).start = element; } else { (*previous).next = element; }
        previous = element;
        k += 1;
    }
    if !previous.is_null() { (*previous).next = 0 as *mut element_s; }
    if n == 0 { (*array).start = 0 as *mut element_s; }
    (*array).length = n;
}
"#;

/// The local is not delivered as a plain reference: it is optional (null =
/// `None`) or it stays raw.
#[test]
fn wave6o_a_local_read_from_a_null_written_raw_field_is_not_plain() {
    assert!(verify::type_checks_str(INPUT));
    let decision = decision_of(INPUT, "array_size", "element");
    assert!(
        !matches!(decision, Decision::Ref { .. }),
        "a raw field written with null makes the local nullable: {decision:?}"
    );
    let output = ast_emitted_source_of(INPUT).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(!flat.contains("letmutelement:&element_s"), "{output}");
    assert!(!flat.contains("&*(*element).next"), "{output}");
    eprintln!("WAVE6O_RAW_FIELD_NULL_BEGIN\n{output}\nWAVE6O_RAW_FIELD_NULL_END");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// The control: no null store into either field, so no null evidence reaches
/// the local and it stays a plain reference (absence reads as non-null, §29).
#[test]
fn wave6o_without_a_null_store_the_raw_field_read_stays_plain() {
    let input = INPUT
        .replace(
            "    if !previous.is_null() { (*previous).next = 0 as *mut element_s; }\n",
            "",
        )
        .replace(
            "    if n == 0 { (*array).start = 0 as *mut element_s; }\n",
            "",
        );
    assert!(verify::type_checks_str(&input));
    let decision = decision_of(&input, "array_size", "element");
    assert!(
        matches!(decision, Decision::Ref { .. }),
        "no null evidence, no optional: {decision:?}"
    );
}

/// The struct-literal construction site counts the same as the assignment:
/// `*previous = element_s { .., next: 0 as *mut element_s }` writes the null
/// literal into `next`.
#[test]
fn wave6o_a_struct_literal_null_field_makes_the_read_nullable() {
    let input = INPUT
        .replace(
            "    if !previous.is_null() { (*previous).next = 0 as *mut element_s; }\n",
            "    if !previous.is_null() { *previous = element_s { value: (*previous).value, next: 0 as *mut element_s }; }\n",
        )
        .replace("    if n == 0 { (*array).start = 0 as *mut element_s; }\n", "");
    assert!(verify::type_checks_str(&input));
    let decision = decision_of(&input, "array_size", "element");
    assert!(
        !matches!(decision, Decision::Ref { .. }),
        "a struct literal's null field makes the local nullable: {decision:?}"
    );
}
