//! **R758-1 (2) / R763-1 (a), main 147 §2 — the thin-into-fat hand-on.** A
//! subject whose own uses carry no arithmetic, handed bare to a callee
//! parameter the program uses as an array, is itself used as an array. Before
//! the rule it took the thin form and reached the callee as a one-element
//! `core::slice::from_ref` / `from_mut` (shape (i), R416-5's defect: the callee
//! indexes past it and panics on a UB-free input).
use super::slice_input_tests::{decision, decisions};

const ALLOW: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, unused_variables, non_snake_case, non_camel_case_types)]\n";

fn emitted(input: &str) -> String {
    match crate::bo_rewriter::rewrite_m1(input) {
        crate::bo_rewriter::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("fixture must emit: {other:#?}"),
    }
}

fn is_slice(decision: &super::Decision) -> bool {
    matches!(
        decision,
        super::Decision::Slice { .. } | super::Decision::Opt { slice: true, .. }
    )
}

/// brotli `BrotliFindAllStaticDictionaryMatches::matches` (54′: 81 one-element
/// views into `AddMatch`): an exported forwarder whose one caller hands it the
/// first element of a local array.
const MATCHES: &str = r#"
unsafe fn AddMatch(distance: usize, len: usize, len_code: usize, matches: *mut u32) {
    let match_0 = (distance << 5).wrapping_add(len_code) as u32;
    if match_0 < *matches.offset(len as isize) {
        *matches.offset(len as isize) = match_0;
    }
}
#[no_mangle]
pub unsafe extern "C" fn FindAll(data: *const u8, n: usize, matches: *mut u32) -> i32 {
    let mut found = 0;
    if n > 2 && *data.offset(0) as i32 == 1 {
        AddMatch(1, 2, 2, matches);
        found = 1;
    }
    if n > 3 {
        AddMatch(3, 3, 3, matches);
        found = 1;
    }
    found
}
pub unsafe fn caller(data: *const u8, n: usize) -> u32 {
    let mut dict_matches: [u32; 38] = [0xfffffff; 38];
    if FindAll(data, n, &mut *dict_matches.as_mut_ptr().offset(0)) != 0 {
        dict_matches[3]
    } else {
        0
    }
}
"#;

#[test]
fn r758_1_a_parameter_handed_bare_to_an_array_formal_is_a_slice() {
    let input = format!("{ALLOW}{MATCHES}");
    let table = decisions(&input);
    assert!(
        is_slice(decision(&table, "FindAll::matches")),
        "{:?}",
        decision(&table, "FindAll::matches")
    );
    let source = emitted(&input);
    assert!(
        !source.contains("from_mut(matches)"),
        "no one-element view of the forwarder:\n{source}"
    );
}

/// brotli `ReadSymbol::table` → `DecodeSymbol(.., from_ref(table), ..)`: the
/// LOCAL form of the same shape.
const TABLE: &str = r#"
unsafe fn DecodeSymbol(bits: u32, table: *const u16) -> u16 {
    *table.offset((bits & 0xff) as isize)
}
pub unsafe fn ReadSymbol(tables: *const u16, bits: u32) -> u16 {
    let mut table: *const u16 = tables;
    DecodeSymbol(bits, table)
}
pub unsafe fn entry(bits: u32) -> u16 {
    let t: [u16; 256] = [1; 256];
    ReadSymbol(t.as_ptr(), bits)
}
"#;

#[test]
fn r758_1_a_local_handed_bare_to_an_array_formal_is_a_slice() {
    let input = format!("{ALLOW}{TABLE}");
    let table = decisions(&input);
    assert!(
        is_slice(decision(&table, "ReadSymbol::table")),
        "{:?}",
        decision(&table, "ReadSymbol::table")
    );
    let source = emitted(&input);
    assert!(
        !source.contains("from_ref(table)"),
        "no one-element view of the local:\n{source}"
    );
}

/// wave-6a 135 F3 / F4 (`agents/artifacts/2026-10-02-wave-6a-135/f3_f4_indent_newline.rs`):
/// json.h `json_write_pretty_value::{indent, newline}`, whose callers replace a
/// NULL before the call and whose callee walks them to the NUL.
const JSON_H: &str = r#"
pub unsafe extern "C" fn json_write_pretty_array(
    mut depth: usize,
    mut indent: *const i8,
    mut newline: *const i8,
    mut data: *mut i8,
) -> *mut i8 {
    let mut m = 0 as usize;
    while '\0' as i32 != *indent.offset(m as isize) as i32 {
        *data = *indent.offset(m as isize);
        data = data.offset(1);
        m = m.wrapping_add(1);
    }
    m = 0 as usize;
    while '\0' as i32 != *newline.offset(m as isize) as i32 {
        *data = *newline.offset(m as isize);
        data = data.offset(1);
        m = m.wrapping_add(1);
    }
    if depth > 0 as usize {
        data = json_write_pretty_value(depth.wrapping_sub(1), indent, newline, data);
    }
    return data;
}
pub unsafe extern "C" fn json_write_pretty_value(
    mut depth: usize,
    mut indent: *const i8,
    mut newline: *const i8,
    mut data: *mut i8,
) -> *mut i8 {
    return json_write_pretty_array(depth, indent, newline, data);
}
#[no_mangle]
pub unsafe extern "C" fn json_write_pretty(mut indent: *const i8, mut newline: *const i8, mut data: *mut i8) -> *mut i8 {
    if indent.is_null() {
        indent = b"  \0" as *const u8 as *const i8;
    }
    if newline.is_null() {
        newline = b"\n\0" as *const u8 as *const i8;
    }
    let mut indent_size = 0 as usize;
    while '\0' as i32 != *indent.offset(indent_size as isize) as i32 {
        indent_size = indent_size.wrapping_add(1);
    }
    return json_write_pretty_value(1 as usize, indent, newline, data);
}
"#;

#[test]
fn r758_1_json_h_indent_and_newline_are_not_one_element_views() {
    let input = format!("{ALLOW}{JSON_H}");
    let table = decisions(&input);
    for label in [
        "json_write_pretty_value::indent",
        "json_write_pretty_value::newline",
    ] {
        let decided = decision(&table, label);
        assert!(
            is_slice(decided) || matches!(decided, super::Decision::Degraded(_)),
            "{label}: {decided:?}"
        );
    }
    let source = emitted(&input);
    assert!(
        !source.contains("from_ref(indent)") && !source.contains("from_ref(newline)"),
        "no one-element view:\n{source}"
    );
}

/// The control: a thin formal handed to a THIN formal (one element read) stays
/// thin.
#[test]
fn r758_1_a_thin_formal_handed_to_a_thin_formal_stays_thin() {
    let input = format!(
        "{ALLOW}
unsafe fn read1(p: *const u32) -> u32 {{ *p }}
pub unsafe fn fwd(q: *const u32) -> u32 {{ read1(q) }}
pub unsafe fn top() -> u32 {{ let x = 5u32; fwd(&x) }}
"
    );
    let table = decisions(&input);
    assert!(
        matches!(decision(&table, "fwd::q"), super::Decision::Ref { .. }),
        "{:?}",
        decision(&table, "fwd::q")
    );
}
