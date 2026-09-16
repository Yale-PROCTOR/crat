//! R418-1 witnesses (relay 024): a local callee parameter decided `Slice` by
//! its own op-facts is a multi-element REQUIREMENT on every caller argument
//! that denotes a caller subject — the thin caller takes the slice form with
//! its companion extent; unsupplied, it declines typed and the call adapts
//! raw with the companion length; `from_ref` stays for one-element readers.
//! lodepng's `adler32(data, len) → update_adler32(1, data, len)` reduced.

const ADLER: &str = r###"
unsafe fn update_adler32(mut adler: u32, data: *const u8, len: u32) -> u32 {
    let mut s1 = adler & 0xffff;
    let mut s2 = (adler >> 16) & 0xffff;
    let mut i = 0u32;
    while i < len {
        s1 = (s1 + *data.offset(i as isize) as u32) % 65521;
        s2 = (s2 + s1) % 65521;
        i = i.wrapping_add(1);
    }
    (s2 << 16) | s1
}
unsafe fn adler32(data: *const u8, len: u32) -> u32 {
    update_adler32(1, data, len)
}
pub unsafe fn entry() -> u32 {
    let buf: [u8; 32] = [7; 32];
    adler32(buf.as_ptr(), 32)
}
"###;

fn fixture(body: &str) -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{body}"
    )
}

/// `adler32::data` forwards into `update_adler32::data`, a slice by its own
/// op-facts, and carries its own companion `len`: it takes `&[u8]` and the
/// callee takes it bare. Before: `data: &u8` and
/// `update_adler32(1, core::slice::from_ref(data), len)` — a panic at
/// `len > 1` where the C program read on.
#[test]
fn w5c_reader_chain_adler32_forwarder_takes_the_slice_with_its_companion() {
    let input = fixture(ADLER);
    let table = super::slice_input_tests::decisions(&input);
    assert!(
        matches!(
            super::slice_input_tests::decision(&table, "adler32::data"),
            super::Decision::Slice { mutable: false, .. }
        ),
        "{:?}",
        super::slice_input_tests::decision(&table, "adler32::data")
    );
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let flat = emitted.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(!flat.contains("from_ref(data)"), "{flat}");
    assert!(flat.contains("update_adler32(1, data, len)"), "{flat}");
    assert!(
        flat.contains("unsafe fn adler32(data: &[u8], len: u32)"),
        "{flat}"
    );
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
}

/// The control: a one-element reader keeps `from_ref`.
#[test]
fn w5c_reader_chain_one_element_reader_keeps_from_ref() {
    let input = fixture(
        &ADLER
            .replace(
                "    while i < len {\n        s1 = (s1 + *data.offset(i as isize) as u32) % 65521;",
                "    while i < len {\n        s1 = (s1 + *data as u32) % 65521;",
            )
            .replace(
                "update_adler32(1, data, len)",
                "update_adler32(1, data, len)",
            ),
    );
    let table = super::slice_input_tests::decisions(&input);
    assert!(
        matches!(
            super::slice_input_tests::decision(&table, "adler32::data"),
            super::Decision::Ref { mutable: false }
        ),
        "{:?}",
        super::slice_input_tests::decision(&table, "adler32::data")
    );
    assert!(
        matches!(
            super::slice_input_tests::decision(&table, "update_adler32::data"),
            super::Decision::Ref { mutable: false }
        ),
        "{:?}",
        super::slice_input_tests::decision(&table, "update_adler32::data")
    );
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
}

/// The decline: a thin caller with no extent of its own (`thin_entry::p`, no
/// companion, read once) cannot take the slice form; it declines typed and
/// the call adapts raw with the callee's companion; the callee keeps its
/// slice.
#[test]
#[ignore = "R418-1 RED: the typed decline (thin-caller-argument, read against the callee's standing) resolves at the R220 owner floor on this line and the interface-path blanket withdraws the callee — the adler32 trace is wave-5d's (report 019 §3); batch 10"]
fn w5c_reader_chain_thin_caller_declines_with_the_companion_adapter() {
    let input = fixture(&format!(
        "{ADLER}pub unsafe fn thin_entry(p: *const u8) -> u32 {{ let x = *p; adler32(p, 1).wrapping_add(x as u32) }}\n"
    ));
    let table = super::slice_input_tests::decisions(&input);
    assert!(
        matches!(
            super::slice_input_tests::decision(&table, "adler32::data"),
            super::Decision::Slice { mutable: false, .. }
        ),
        "{:?}",
        super::slice_input_tests::decision(&table, "adler32::data")
    );
    let p = super::slice_input_tests::decision(&table, "thin_entry::p");
    assert!(
        matches!(
            p,
            super::Decision::Degraded(super::Degradation {
                reason: super::DegradeReason::LocalCalleeAccessExtent { access, .. },
                ..
            }) if access.detail().contains("thin-caller-argument")
        ),
        "{p:?}"
    );
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let flat = emitted.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("adler32(core::slice::from_raw_parts(p, (1) as usize), 1)"),
        "{flat}"
    );
    assert!(!flat.contains("from_ref("), "{flat}");
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
}
