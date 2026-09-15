//! wave-6b — void buffers viewed as typed regions (seat addendum 400, R400-1).
//!
//! Fixtures reduced from rs-crown/brotli: the H40 hasher's `extra` accessor
//! chain (`AddrH40` / `HeadH40` / `TinyHashH40` / `BanksH40`, one caller
//! `StoreH40`) and the unaligned width reader `BrotliUnalignedRead32` with
//! its `HashBytesH40` caller. Region sizes are shrunk (16 slots, 16 buckets)
//! so a runtime fixture stays small; the shape of every expression is the
//! corpus's, including the `(AddrH40 as unsafe extern "C" fn(..))(extra)`
//! spelling c2rust uses for the inner accessor calls.

/// The H40 accessor chain and one caller (rs-crown/brotli
/// `src::enc::backward_references::{AddrH40,HeadH40,TinyHashH40,BanksH40,StoreH40}`).
pub(super) const H40: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint16_t = u16;
pub type uint32_t = u32;
pub type size_t = usize;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct SlotH40 {
    pub delta: uint16_t,
    pub next: uint16_t,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct BankH40 {
    pub slots: [SlotH40; 16],
}
#[repr(C)]
pub struct H40 {
    pub free_slot_idx: [uint16_t; 1],
    pub max_hops: size_t,
    pub extra: *mut core::ffi::c_void,
}
unsafe extern "C" fn AddrH40(mut extra: *mut core::ffi::c_void) -> *mut uint32_t {
    return extra as *mut uint32_t;
}
unsafe extern "C" fn HeadH40(mut extra: *mut core::ffi::c_void) -> *mut uint16_t {
    return &mut *((AddrH40 as unsafe extern "C" fn(*mut core::ffi::c_void) -> *mut uint32_t)(extra))
        .offset(((1 as i32) << 4 as i32) as isize) as *mut uint32_t as *mut uint16_t;
}
unsafe extern "C" fn TinyHashH40(mut extra: *mut core::ffi::c_void) -> *mut uint8_t {
    return &mut *((HeadH40 as unsafe extern "C" fn(*mut core::ffi::c_void) -> *mut uint16_t)(extra))
        .offset(((1 as i32) << 4 as i32) as isize) as *mut uint16_t as *mut uint8_t;
}
unsafe extern "C" fn BanksH40(mut extra: *mut core::ffi::c_void) -> *mut BankH40 {
    return &mut *((TinyHashH40 as unsafe extern "C" fn(*mut core::ffi::c_void) -> *mut uint8_t)(extra))
        .offset(16 as i32 as isize) as *mut uint8_t as *mut BankH40;
}
unsafe extern "C" fn StoreH40(mut self_0: *mut H40, key: size_t, ix: size_t) {
    let mut addr = AddrH40((*self_0).extra);
    let mut head = HeadH40((*self_0).extra);
    let mut tiny_hash = TinyHashH40((*self_0).extra);
    let mut banks = BanksH40((*self_0).extra);
    let bank = key & (1 as i32 - 1 as i32) as usize;
    let ref mut fresh6 = (*self_0).free_slot_idx[bank as usize];
    let fresh7 = *fresh6;
    *fresh6 = (*fresh6).wrapping_add(1);
    let idx = (fresh7 as i32 & ((1 as i32) << 4 as i32) - 1 as i32) as size_t;
    let mut delta = ix.wrapping_sub(*addr.offset(key as isize) as usize);
    *tiny_hash.offset((ix & 15) as isize) = key as uint8_t;
    if delta > 0xffff as i32 as usize {
        delta = ({ 0xffff as i32 }) as size_t;
    }
    (*banks.offset(bank as isize)).slots[idx as usize].delta = delta as uint16_t;
    (*banks.offset(bank as isize)).slots[idx as usize].next = *head.offset(key as isize);
    *addr.offset(key as isize) = ix as uint32_t;
    *head.offset(key as isize) = idx as uint16_t;
}
"#;

/// The width reader and its thin-source caller (rs-crown/brotli
/// `src::enc::backward_references::{BrotliUnalignedRead32,HashBytesH40}`),
/// plus a caller whose source is a counted byte buffer.
pub(super) const READ32: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint32_t = u32;
pub type size_t = usize;
static mut kHashMul32: uint32_t = 0x1e35a7bd as uint32_t;
unsafe extern "C" fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> uint32_t {
    return *(p as *const uint32_t);
}
unsafe extern "C" fn HashBytesH40(mut data: *const uint8_t) -> size_t {
    let h = (BrotliUnalignedRead32(data as *const core::ffi::c_void)).wrapping_mul(kHashMul32);
    return (h >> 32 as i32 - 15 as i32) as size_t;
}
unsafe extern "C" fn sum_words(mut data: *const uint8_t, mut len: size_t) -> uint32_t {
    let mut i: size_t = 0;
    let mut acc: uint32_t = 0;
    while i.wrapping_add(4) <= len {
        acc = acc.wrapping_add(BrotliUnalignedRead32(data.offset(i as isize) as *const core::ffi::c_void));
        i = i.wrapping_add(4);
    }
    return acc;
}
"#;

fn compact(source: &str) -> String {
    source.chars().filter(|c| !c.is_whitespace()).collect()
}

fn reason(rows: &[(String, bool, String)], name: &str) -> String {
    rows.iter()
        .find(|(n, p, _)| n == name && *p)
        .unwrap_or_else(|| panic!("no parameter subject {name}: {rows:?}"))
        .2
        .clone()
}

/// Every accessor parameter of the chain delivers, the chain is emitted as
/// disjoint byte regions at the caller, and the tree type-checks.
#[test]
fn w6b_h40_accessor_chain_delivers_as_byte_regions() {
    let rows = super::emit_tests::decisions_of(H40);
    for name in ["extra"] {
        let reasons: Vec<_> = rows
            .iter()
            .filter(|(n, p, _)| n == name && *p)
            .map(|(_, _, r)| r.clone())
            .collect();
        assert_eq!(reasons.len(), 4, "four accessor parameters: {rows:?}");
        assert!(
            reasons.iter().all(|r| r == "<emitted>"),
            "every accessor `extra` must deliver: {reasons:?}"
        );
    }
    let source = super::emit_tests::ast_emitted_source_of(H40).expect("AST output");
    let flat = compact(&source);
    assert!(
        flat.contains("fnAddrH40(mutextra:&mut[u8])"),
        "the buffer parameter is a byte slice: {source}"
    );
    assert!(
        !source.contains("&mut core::ffi::c_void") && !source.contains("&mut [core::ffi::c_void]"),
        "no thin or void reference form: {source}"
    );
    // The accessor reinterprets its region; the caller receives a raw pointer
    // exactly as before (build 1: the return stays raw).
    assert!(
        flat.contains("align_of::<uint16_t>()"),
        "the head region asserts its alignment: {source}"
    );
    assert!(
        flat.contains(".cast::<BankH40>()"),
        "the banks region is reinterpreted: {source}"
    );
    // Disjoint regions at the caller: offsets 0 / 64 / 96 / 112 and the exact
    // lengths 64 / 32 / 16 of the three inner regions.
    for needle in [
        "from_raw_parts_mut((((*self_0).extra)as*mutu8),64)",
        "from_raw_parts_mut((((*self_0).extra)as*mutu8).add(64),32)",
        "from_raw_parts_mut((((*self_0).extra)as*mutu8).add(96),16)",
        "from_raw_parts_mut((((*self_0).extra)as*mutu8).add(112),crate::FALLBACK_SLICE_EXTENT*core::mem::size_of::<BankH40>())",
    ] {
        assert!(
            flat.contains(needle),
            "caller bridge {needle} missing: {source}"
        );
    }
    assert!(
        super::verify::type_checks_str(&source),
        "output compiles: {source}"
    );
}

/// The width reader's parameter delivers as a four-byte slice read with
/// `from_ne_bytes`; a raw caller bridges with the reader's own width.
#[test]
fn w6b_unaligned_read32_delivers_as_a_byte_slice() {
    let rows = super::emit_tests::decisions_of(READ32);
    assert_eq!(reason(&rows, "p"), "<emitted>", "{rows:?}");
    let source = super::emit_tests::ast_emitted_source_of(READ32).expect("AST output");
    let flat = compact(&source);
    assert!(
        flat.contains("fnBrotliUnalignedRead32(mutp:&[u8])"),
        "the reader parameter is a shared byte slice: {source}"
    );
    assert!(
        flat.contains("uint32_t::from_ne_bytes([p[0],p[1],p[2],p[3]])"),
        "the read is a from_ne_bytes over the slice: {source}"
    );
    assert!(
        flat.contains("from_raw_parts((data as*constcore::ffi::c_void)as*constu8,4)")
            || flat.contains("from_raw_parts(((dataas*constcore::ffi::c_void)as*constu8),4)"),
        "the thin-source caller bridges with the reader's width: {source}"
    );
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT"),
        "the width is evidence, never fabricated: {source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "output compiles: {source}"
    );
}

fn param_reasons(input: &str, name: &str) -> Vec<String> {
    super::emit_tests::decisions_of(input)
        .into_iter()
        .filter(|(n, p, _)| n == name && *p)
        .map(|(_, _, r)| r)
        .collect()
}

/// A region whose element type has padding is not plain old data: the chain
/// holds at that accessor, and the void hold is what it reports.
#[test]
fn w6b_padded_struct_region_keeps_the_void_hold() {
    let padded = H40
        .replace(
            "pub struct SlotH40 {\n    pub delta: uint16_t,\n    pub next: uint16_t,\n}",
            "pub struct SlotH40 {\n    pub delta: uint16_t,\n    pub next: uint32_t,\n}",
        )
        .replace(
            ".next = *head.offset(key as isize);",
            ".next = *head.offset(key as isize) as uint32_t;",
        );
    assert_ne!(padded, H40);
    let reasons = param_reasons(&padded, "extra");
    assert_eq!(reasons.len(), 4, "{reasons:?}");
    assert!(
        reasons.iter().all(|r| r == "held:void-pointee"),
        "the padded banks region keeps the void hold, and the chain it pins \
         through its fn-pointer casts holds with it: {reasons:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&padded).expect("AST output");
    assert!(
        !source.contains("cast::<BankH40>()"),
        "no reinterpretation into a padded struct: {source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "output compiles: {source}"
    );
}

/// A non-constant offset is not a region: the accessor holds, and so does the
/// inner accessor it pins through the fn-pointer cast.
#[test]
fn w6b_non_constant_offset_holds_the_chain_link() {
    let dynamic = H40
        .replace(
            "unsafe extern \"C\" fn HeadH40(mut extra: *mut core::ffi::c_void) -> *mut uint16_t {",
            "static mut HEAD_AT: isize = 16;\nunsafe extern \"C\" fn HeadH40(mut extra: *mut core::ffi::c_void) -> *mut uint16_t {",
        )
        .replace(
            ".offset(((1 as i32) << 4 as i32) as isize) as *mut uint32_t as *mut uint16_t;",
            ".offset(HEAD_AT) as *mut uint32_t as *mut uint16_t;",
        );
    assert_ne!(dynamic, H40);
    let reasons = param_reasons(&dynamic, "extra");
    assert_eq!(reasons.len(), 4, "{reasons:?}");
    assert!(
        reasons.iter().all(|r| r != "<emitted>"),
        "an unproved link holds every accessor that reaches through it: {reasons:?}"
    );
}

/// A body that is anything but the single reinterpreting return holds.
#[test]
fn w6b_body_beyond_the_single_return_holds() {
    let twice = H40.replace(
        "    return extra as *mut uint32_t;",
        "    if extra.is_null() { return 0 as *mut uint32_t; }\n    return extra as *mut uint32_t;",
    );
    assert_ne!(twice, H40);
    let reasons = param_reasons(&twice, "extra");
    assert!(
        reasons.iter().all(|r| r != "<emitted>"),
        "a null test beside the cast is a second statement: {reasons:?}"
    );
}

/// A `*const` chain becomes a shared byte slice and a shared region view.
#[test]
fn w6b_const_chain_is_a_shared_region() {
    let shared = r#"
#![allow(dead_code, unused_mut, non_snake_case, non_camel_case_types)]
pub type uint16_t = u16;
pub type uint32_t = u32;
unsafe extern "C" fn AddrC(mut extra: *const core::ffi::c_void) -> *const uint32_t {
    return extra as *const uint32_t;
}
unsafe extern "C" fn HeadC(mut extra: *const core::ffi::c_void) -> *const uint16_t {
    return &*((AddrC as unsafe extern "C" fn(*const core::ffi::c_void) -> *const uint32_t)(extra))
        .offset(8 as isize) as *const uint32_t as *const uint16_t;
}
unsafe extern "C" fn sum(mut buffer: *const core::ffi::c_void, key: usize) -> u32 {
    let addr = AddrC(buffer);
    let head = HeadC(buffer);
    return (*addr.offset(key as isize)).wrapping_add(*head.offset(key as isize) as u32);
}
"#;
    let reasons = param_reasons(shared, "extra");
    assert_eq!(reasons, vec!["<emitted>", "<emitted>"], "{reasons:?}");
    let source = super::emit_tests::ast_emitted_source_of(shared).expect("AST output");
    let flat = compact(&source);
    assert!(flat.contains("fnAddrC(mutextra:&[u8])"), "{source}");
    assert!(
        flat.contains("__crat_region.as_ptr().cast::<uint16_t>()"),
        "{source}"
    );
    assert!(
        flat.contains("from_raw_parts(((buffer)as*constu8),32)"),
        "the shared root region: {source}"
    );
    assert!(
        flat.contains("from_raw_parts(((buffer)as*constu8).add(32),crate::FALLBACK_SLICE_EXTENT*core::mem::size_of::<uint16_t>())"),
        "the shared last region: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// Two accessors over one range of one buffer, held live together by a
/// caller, would be two views of the same bytes: the caller's sites are
/// blocked, so no such pair is ever emitted.
#[test]
fn w6b_two_views_of_one_region_are_not_emitted_together() {
    let twin = H40
        .replace(
            "unsafe extern \"C\" fn StoreH40(",
            "unsafe extern \"C\" fn AddrBytesH40(mut extra: *mut core::ffi::c_void) -> *mut uint8_t {\n    return extra as *mut uint8_t;\n}\nunsafe extern \"C\" fn StoreH40(",
        )
        .replace(
            "    let mut addr = AddrH40((*self_0).extra);\n",
            "    let mut addr = AddrH40((*self_0).extra);\n    let mut addr_bytes = AddrBytesH40((*self_0).extra);\n    *addr_bytes.offset(1) = 0;\n",
        );
    assert_ne!(twin, H40);
    let source = super::emit_tests::ast_emitted_source_of(&twin).expect("AST output");
    let flat = compact(&source);
    let root_views = flat
        .matches("from_raw_parts_mut((((*self_0).extra)as*mutu8),64)")
        .count()
        + flat
            .matches("from_raw_parts_mut((((*self_0).extra)as*mutu8),crate::FALLBACK_SLICE_EXTENT")
            .count();
    assert!(
        root_views <= 1,
        "at most one live view of the root range in one caller: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}
