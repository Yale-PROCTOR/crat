//! **R622-1 / R628-2 — the extent conjunct on the `(Slice, Ref)` glue row
//! (R416-5).** A thin argument handed to a slice formal through
//! `core::slice::from_ref` / `from_mut` is ONE element. A callee that accesses
//! that formal past its first element panics on the checked index where C read
//! on: brotli's `dist_cache` into `BrotliZopfliCreateCommands` (writes `[3]`),
//! lodepng's `&*in_0.offset(k)` into `lodepng_read32bitInt` (reads `[1..3]`).
//! The row now admits the adapter only into a formal accessed at one element
//! (`seam-one-element-into-wider-formal` otherwise).
//!
//! **R761-1 (the re-cut for 54):** the row refuses only the ELEMENT ADDRESS of a
//! raw base (shape (ii), lodepng's `&*in_0.offset(k)`); a thin subject's
//! `from_ref` (shape (i), brotli's `dist_cache`) is left to 55's thin-into-fat
//! rule, and its witness and fixture leave this file with the thin-caller hold.

use super::wave6a_allocation_tests::{compact, emitted};

/// lodepng's `lodepng_read32bitInt` shape: the address of one element of a raw
/// buffer (`&*in_0.offset(k)`) handed to a reader of four.
const READ32: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn sum4(mut buf: *const i32) -> i32 {
    let mut s: i32 = 0;
    let mut i: usize = 0;
    while i < 4 {
        s += *buf.offset(i as isize);
        i += 1;
    }
    s
}
pub unsafe fn caller(mut in_0: *const i32, mut k: isize) -> i32 {
    return sum4(&*in_0.offset(k));
}
"#;

/// Counted in the program's own text: an emitted crate that delivers a cursor
/// appends the `slice_cursor` helper module, whose own code is not a site.
fn one_element_adapters(source: &str) -> usize {
    let own = source
        .split("pub mod slice_cursor")
        .next()
        .unwrap_or(source);
    let flat = compact(own);
    flat.matches("slice::from_ref(").count() + flat.matches("slice::from_mut(").count()
}

#[test]
fn r622_1_the_address_of_one_raw_element_is_not_handed_to_a_wider_reader() {
    // The row refuses the adapter; the reader's class may then hold whole, and a
    // program with nothing else to deliver emits nothing. Either way no
    // one-element adapter reaches the reader.
    let (source, degradations) =
        match super::wave6a_allocation_tests::rewrite_precise("one-element-read32", READ32) {
            super::RewriteOutcome::Emitted {
                source,
                degradations,
                ..
            } => (source, degradations),
            super::RewriteOutcome::Degraded { degradations, .. } => {
                (READ32.to_owned(), degradations)
            }
        };
    assert_eq!(
        one_element_adapters(&source),
        0,
        "{source}\n{degradations:#?}"
    );
}

/// The emitted source, or the input when the program holds whole (a refused
/// adapter can leave nothing else to deliver).
fn emitted_or_input(name: &str, source: &str) -> (String, String) {
    match super::wave6a_allocation_tests::rewrite_precise(name, source) {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            ..
        } => (source, format!("{degradations:#?}")),
        super::RewriteOutcome::Degraded { degradations, .. } => {
            (source.to_owned(), format!("{degradations:#?}"))
        }
    }
}

/// **R641-2 (1)–(2)** — the element test reads the HIR, casts included. Each
/// shape was RED under the snippet test (main 131 §6 items 1–2): the cast
/// shapes were not in the conjunct, `&buf[k]` does not start with `*`, and
/// `&mut*p` has no space after `mut`.
const ELEMENT_SHAPES: [(&str, &str); 3] = [
    (
        "one-element-cast",
        "return sum4(&*in_0.offset(k) as *const i32);",
    ),
    (
        "one-element-array-index",
        "let mut buf: [i32; 8] = [1; 8];\n    return sum4(&buf[k as usize]);",
    ),
    (
        "one-element-deref-no-space",
        "return sum4(&mut*(in_0 as *mut i32).offset(k));",
    ),
];

#[test]
fn r641_2_an_element_address_is_read_from_the_hir_casts_included() {
    for (name, call) in ELEMENT_SHAPES {
        let input = READ32.replace("return sum4(&*in_0.offset(k));", call);
        assert_ne!(input, READ32, "{name}: the fixture edit applies");
        let (source, degradations) = emitted_or_input(name, &input);
        assert_eq!(
            one_element_adapters(&source),
            0,
            "{name}\n{source}\n{degradations}"
        );
    }
}

/// Is `callee`'s parameter `index` in the table's accessed-past-one-element set?
fn wide(src: &str, callee: &str, index: usize) -> bool {
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let table = super::decide_table(tcx).expect("the fixture decides");
        let did = tcx
            .hir_body_owners()
            .find(|did| tcx.def_path_str(did.to_def_id()) == callee)
            .unwrap_or_else(|| panic!("no fn {callee}"));
        table.wide_access_parameters.contains(&(did, index))
    })
    .expect("the fixture compiles")
}

/// **wave-6o 084a's five sites, by the callee shape that makes each wide.** The
/// corpus rows need brotli's own families to render the adapter; the extent
/// conjunct is a property of the callee, so each is pinned on the callee.
const FIVE_SITES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
unsafe fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> u32 {
    return *(p as *const u32);
}
/// `Hash14` / `HashBytesH10`: four bytes read through a cast of the formal.
unsafe fn Hash14(mut data: *const u8) -> u32 {
    let mut h = BrotliUnalignedRead32(data as *const core::ffi::c_void).wrapping_mul(0x1e35a7bd);
    return h >> 32 as i32 - 14 as i32;
}
unsafe fn HashBytesH10(mut data: *const u8) -> u32 {
    let mut h = BrotliUnalignedRead32(data as *const core::ffi::c_void).wrapping_mul(0x1e35a7bd);
    return h >> 32 as i32 - 17 as i32;
}
/// `ReplicateValue`: written at `end`, stepping down to 0.
unsafe fn ReplicateValue(mut table: *mut u32, mut step: i32, mut end: i32, mut code: u32) {
    loop {
        end -= step;
        *table.offset(end as isize) = code;
        if !(end > 0 as i32) {
            break;
        }
    }
}
/// `DecodeSymbol`: re-based by the low byte of the bits.
unsafe fn DecodeSymbol(mut bits: u32, mut table: *const u32) -> u32 {
    table = table.offset((bits & 0xff as i32 as u32) as isize);
    return *table;
}
/// `AddMatch`: written at `len`.
unsafe fn AddMatch(mut distance: usize, mut len: usize, mut len_code: usize, mut matches: *mut u32) {
    let mut m = (distance << 5 as i32).wrapping_add(len_code) as u32;
    *matches.offset(len as isize) = if *matches.offset(len as isize) < m { *matches.offset(len as isize) } else { m };
}
/// The control: one element, read and written.
unsafe fn Bump(mut p: *mut u32) {
    *p = (*p).wrapping_add(1);
}
/// R641-2: C's `p[0]`, read and written in place.
unsafe fn ZeroInPlace(mut p: *mut u32) {
    *p.offset(0 as i32 as isize) = (*p.offset(0 as i32 as isize)).wrapping_add(1);
}
/// R641-2: a literal-0 offset that is not dereferenced in place keeps the
/// conservative reading (the copy reads on).
unsafe fn ZeroCopied(mut p: *mut u32) -> u32 {
    let mut q = p.offset(0 as i32 as isize);
    return *q.offset(2 as i32 as isize);
}
"#;

#[test]
fn r631_1_hash14_reads_four_bytes_through_its_formal() {
    assert!(wide(FIVE_SITES, "Hash14", 0));
}

#[test]
fn r631_1_hash_bytes_h10_reads_four_bytes_through_its_formal() {
    assert!(wide(FIVE_SITES, "HashBytesH10", 0));
}

#[test]
fn r631_1_replicate_value_writes_past_its_first_element() {
    assert!(wide(FIVE_SITES, "ReplicateValue", 0));
}

#[test]
fn r631_1_decode_symbol_reads_past_its_first_element() {
    assert!(wide(FIVE_SITES, "DecodeSymbol", 1));
}

#[test]
fn r631_1_add_match_writes_past_its_first_element() {
    assert!(wide(FIVE_SITES, "AddMatch", 3));
}

#[test]
fn r631_1_a_formal_accessed_at_one_element_is_not_wide() {
    assert!(!wide(FIVE_SITES, "Bump", 0));
}

/// **R641-2** — RED first: guard mode read every `offset` as past the first
/// element, so C's `p[0]` held its thin callers (11 R220 controls moved, main
/// 131 §2).
#[test]
fn r641_2_c_element_zero_in_place_is_one_element() {
    assert!(!wide(FIVE_SITES, "ZeroInPlace", 0));
}

#[test]
fn r641_2_a_literal_zero_offset_that_is_copied_stays_wide() {
    assert!(wide(FIVE_SITES, "ZeroCopied", 0));
}
