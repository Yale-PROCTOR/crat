//! Reduced from libcsv csv_parse / csv_increase_buffer's optional parser calls.
const INPUT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
pub struct Parser { data: *mut u8, count: usize,
    grow: unsafe fn(*mut u8, usize) -> *mut u8 }
pub unsafe fn csv_increase_buffer(p: *mut Parser) {
    if p.is_null() { return; }
    (*p).data = ((*p).grow)((*p).data, 16);
    (*p).count += 1;
}
pub unsafe fn csv_parse(p: *mut Parser) -> usize {
    if p.is_null() { return 0; }
    csv_increase_buffer(p);
    (*p).count
}
"#;

#[test]
fn wave6r_csv_parse_growth_then_parser_read() {
    let source = super::emitted(INPUT);
    assert!(source.contains("p: Option<&mut Parser>"), "{source}");
    assert!(
        source.contains("csv_increase_buffer(p.as_deref_mut())"),
        "{source}"
    );
}

#[test]
fn wave6r_csv_parse_repeated_growth_then_parser_read() {
    let source = super::emitted(&INPUT.replace(
        "csv_increase_buffer(p);",
        "csv_increase_buffer(p); csv_increase_buffer(p);",
    ));
    assert_eq!(
        source
            .matches("csv_increase_buffer(p.as_deref_mut())")
            .count(),
        2,
        "{source}"
    );
}

#[test]
fn wave6r_csv_parse_null_argument_remains_optional() {
    let input = INPUT.replace(
        "    if p.is_null() { return 0; }\n    csv_increase_buffer(p);",
        "    csv_increase_buffer(p);\n    if p.is_null() { return 0; }",
    );
    let source = super::emitted(&input);
    assert!(
        source.contains("csv_increase_buffer(p.as_deref_mut())"),
        "{source}"
    );
}

#[test]
fn wave6r_csv_parse_reverted_caller_keeps_raw_adapter() {
    let source = super::emitted_reverting(INPUT, Some("csv_parse"));
    assert!(source.contains("p: *mut Parser"), "{source}");
    assert!(
        !source.contains("csv_increase_buffer(p.as_deref_mut())"),
        "{source}"
    );
}

#[test]
fn wave6r_csv_parse_reverted_callee_withdraws_optional_reborrow() {
    let source = super::ast_source_reverting(INPUT, Some("csv_increase_buffer"));
    assert!(
        source.contains("csv_increase_buffer(p: *mut Parser)")
            || source.contains("csv_increase_buffer(mut p: *mut Parser)"),
        "{source}"
    );
    assert!(
        !source.contains("csv_increase_buffer(p.as_deref_mut())"),
        "{source}"
    );
}

#[test]
fn wave6r_csv_parse_final_call_preserves_transfer() {
    let input = INPUT.replace(
        "    csv_increase_buffer(p);\n    (*p).count",
        "    let count = (*p).count;\n    csv_increase_buffer(p);\n    count",
    );
    let source = super::emitted(&input);
    assert!(
        source.contains("csv_increase_buffer(p);"),
        "a final transfer needs no shorter loan: {source}"
    );
}
