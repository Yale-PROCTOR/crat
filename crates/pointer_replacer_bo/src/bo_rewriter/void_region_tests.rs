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

fn local_reason(rows: &[(String, bool, String)], name: &str) -> String {
    rows.iter()
        .find(|(n, p, _)| n == name && !*p)
        .unwrap_or_else(|| panic!("no local subject {name}: {rows:?}"))
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
    // **Re-premised by wave-4's W4-LIFT (R475-2), disclosed in wave-4 report
    // 038.** Until that lift the caller stayed THIN and the seam fabricated the
    // reader's width from a one-element claim
    // (`from_raw_parts((data as *const c_void) as *const u8, 4)`). The exact
    // width this family exports now licenses the caller's own slice form, so
    // the bridge is the `region_from_slice` arm below — a CHECKED prefix of a
    // delivered slice, with no raw pointer in between. The width is still the
    // reader's four bytes; what changed is that nothing fabricates it.
    assert!(
        flat.contains("BrotliUnalignedRead32(&(data)[..4])"),
        "the delivered-slice caller bridges as a checked prefix: {source}"
    );
    assert!(
        !flat.contains("from_raw_parts"),
        "and nothing fabricates a view from a one-element claim: {source}"
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

/// A width reader whose caller's source is a delivered byte slice (rs-crown/brotli
/// `Hash14`-shaped reader over a counted buffer): the reader is bridged from the
/// slice itself, `&data[..4]`, with no raw pointer in between.
pub(super) const READ32_SLICE_SOURCE: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint32_t = u32;
pub type size_t = usize;
unsafe extern "C" fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> uint32_t {
    return *(p as *const uint32_t);
}
unsafe extern "C" fn checksum(mut data: *const uint8_t, mut len: size_t) -> uint32_t {
    let mut i: size_t = 0;
    let mut acc: uint32_t = 0;
    while i < len {
        acc = acc.wrapping_add(*data.offset(i as isize) as uint32_t);
        i = i.wrapping_add(1);
    }
    return acc ^ BrotliUnalignedRead32(data as *const core::ffi::c_void);
}
"#;

#[test]
fn w6b_width_reader_from_a_delivered_slice_source() {
    let rows = super::emit_tests::decisions_of(READ32_SLICE_SOURCE);
    assert_eq!(reason(&rows, "p"), "<emitted>", "{rows:?}");
    assert_eq!(reason(&rows, "data"), "<emitted>", "{rows:?}");
    let source = super::emit_tests::ast_emitted_source_of(READ32_SLICE_SOURCE).expect("AST output");
    let flat = compact(&source);
    assert!(
        flat.contains("fnchecksum(mutdata:&[uint8_t]"),
        "the source is a slice: {source}"
    );
    assert!(
        flat.contains("BrotliUnalignedRead32(&(data)[..4])"),
        "the reader takes a checked prefix of the slice, no raw pointer: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// H42 (rs-crown/brotli `src::enc::encode::{AddrH42,HeadH42,TinyHashH42,BanksH42,
/// PrepareH42,FindLongestMatchH42}`, reduced: 4 banks of 16 slots): a
/// multi-bank last region, a three-accessor caller that hands region pointers
/// to libc `memset` raw, and a read-only caller of all four.
pub(super) const H42: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint16_t = u16;
pub type uint32_t = u32;
pub type size_t = usize;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct SlotH42 {
    pub delta: uint16_t,
    pub next: uint16_t,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct BankH42 {
    pub slots: [SlotH42; 16],
}
#[repr(C)]
pub struct H42 {
    pub free_slot_idx: [uint16_t; 4],
    pub max_hops: size_t,
    pub extra: *mut core::ffi::c_void,
}
unsafe extern "C" fn AddrH42(mut extra: *mut core::ffi::c_void) -> *mut uint32_t {
    return extra as *mut uint32_t;
}
unsafe extern "C" fn HeadH42(mut extra: *mut core::ffi::c_void) -> *mut uint16_t {
    return &mut *((AddrH42 as unsafe extern "C" fn(*mut core::ffi::c_void) -> *mut uint32_t)(extra))
        .offset(((1 as i32) << 4 as i32) as isize) as *mut uint32_t as *mut uint16_t;
}
unsafe extern "C" fn TinyHashH42(mut extra: *mut core::ffi::c_void) -> *mut uint8_t {
    return &mut *((HeadH42 as unsafe extern "C" fn(*mut core::ffi::c_void) -> *mut uint16_t)(extra))
        .offset(((1 as i32) << 4 as i32) as isize) as *mut uint16_t as *mut uint8_t;
}
unsafe extern "C" fn BanksH42(mut extra: *mut core::ffi::c_void) -> *mut BankH42 {
    return &mut *((TinyHashH42 as unsafe extern "C" fn(*mut core::ffi::c_void) -> *mut uint8_t)(extra))
        .offset(16 as i32 as isize) as *mut uint8_t as *mut BankH42;
}
extern "C" {
    fn memset(_: *mut core::ffi::c_void, _: i32, _: usize) -> *mut core::ffi::c_void;
}
unsafe extern "C" fn PrepareH42(mut self_0: *mut H42, one_shot: i32, input_size: size_t) {
    let mut addr = AddrH42((*self_0).extra);
    let mut head = HeadH42((*self_0).extra);
    let mut tiny_hash = TinyHashH42((*self_0).extra);
    if one_shot != 0 && input_size <= 4 {
        let mut i: size_t = 0;
        while i < input_size {
            *addr.offset(i as isize) = 0xcccccccc as u32;
            *head.offset(i as isize) = 0xcccc as i32 as uint16_t;
            i = i.wrapping_add(1);
        }
    } else {
        memset(addr as *mut core::ffi::c_void, 0xcc as i32, 4 * 16);
        memset(head as *mut core::ffi::c_void, 0 as i32, 2 * 16);
    }
    memset(tiny_hash as *mut core::ffi::c_void, 0 as i32, 16);
}
unsafe extern "C" fn FindLongestMatchH42(mut self_0: *mut H42, key: size_t, cur_ix: size_t) -> size_t {
    let mut addr = AddrH42((*self_0).extra);
    let mut head = HeadH42((*self_0).extra);
    let mut tiny_hashes = TinyHashH42((*self_0).extra);
    let mut banks = BanksH42((*self_0).extra);
    let bank = key & (4 as i32 - 1 as i32) as usize;
    let mut hops = (*self_0).max_hops;
    let mut delta = cur_ix.wrapping_sub(*addr.offset(key as isize) as usize);
    let mut slot = *head.offset(key as isize) as size_t;
    let mut backward: size_t = 0;
    loop {
        let fresh = hops;
        hops = hops.wrapping_sub(1);
        if !(fresh != 0) { break; }
        let last = slot;
        backward = backward.wrapping_add(delta);
        if *tiny_hashes.offset((cur_ix & 15) as isize) as i32 != key as uint8_t as i32 { continue; }
        slot = (*banks.offset(bank as isize)).slots[last as usize].next as size_t;
        delta = (*banks.offset(bank as isize)).slots[last as usize].delta as size_t;
    }
    return backward;
}
"#;

#[test]
fn w6b_h42_multi_bank_chain_delivers() {
    let reasons = param_reasons(H42, "extra");
    assert_eq!(reasons.len(), 4, "{reasons:?}");
    assert!(reasons.iter().all(|r| r == "<emitted>"), "{reasons:?}");
    let source = super::emit_tests::ast_emitted_source_of(H42).expect("AST output");
    let flat = compact(&source);
    assert_eq!(
        flat.matches("from_raw_parts_mut((((*self_0).extra)as*mutu8).add(112),crate::FALLBACK_SLICE_EXTENT*core::mem::size_of::<BankH42>())").count(),
        1,
        "the multi-bank last region takes the fallback exactly once (FindLongestMatch): {source}"
    );
    assert_eq!(
        flat.matches("from_raw_parts_mut((((*self_0).extra)as*mutu8),64)")
            .count(),
        2,
        "both callers bridge the root region exactly: {source}"
    );
    // The raw region pointers keep flowing raw into libc memset (the corpus's PrepareH4x).
    assert!(
        flat.contains("memset(addras*mutcore::ffi::c_void,"),
        "{source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// Build 3: the accessor-result locals of a caller receive the region as a
/// typed slice — an explicit declaration, the raw result wrapped with the
/// region's exact element count, indexed uses. `addr` is model-Raw in the
/// analysis frame (as `StoreH4x::addr` is in the corpus) and keeps its raw
/// form beside the delivered three.
#[test]
fn w6b_h40_caller_locals_receive_region_slices() {
    let rows = super::emit_tests::decisions_of(H40);
    for name in ["head", "tiny_hash", "banks"] {
        let reasons: Vec<_> = rows
            .iter()
            .filter(|(n, p, _)| n == name && !*p)
            .map(|(_, _, r)| r.clone())
            .collect();
        assert_eq!(reasons, vec!["<emitted>"], "{name}: {rows:?}");
    }
    let source = super::emit_tests::ast_emitted_source_of(H40).expect("AST output");
    let flat = compact(&source);
    for needle in [
        // the caller is an `unsafe fn`: no redundant inner `unsafe` block
        "letmuthead:&mut[u16]=core::slice::from_raw_parts_mut(HeadH40(",
        "letmuttiny_hash:&mut[u8]=core::slice::from_raw_parts_mut(TinyHashH40(",
        "letmutbanks:&mut[crate::BankH40]=core::slice::from_raw_parts_mut(BanksH40(",
        // exact element counts 32/2 and 16/1; the fallback count for the last
        ".add(64),32)),16);",
        ".add(96),16)),16);",
        "crate::FALLBACK_SLICE_EXTENT*core::mem::size_of::<BankH40>())),crate::FALLBACK_SLICE_EXTENT);",
        "head[key]",
        "tiny_hash[(ix&15)]",
        "banks[bank].slots[idxasusize].delta",
    ] {
        assert!(flat.contains(needle), "{needle} missing: {source}");
    }
    assert!(
        !flat.contains("head.offset(") && !flat.contains("banks.offset("),
        "no raw arithmetic remains on the delivered locals: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// binn `copy_be64` (rs-crown/binn `lib.rs:212`): a `*mut u64` parameter
/// cast to `*mut c_uchar` and read byte by byte at `7 - i` — an 8-byte view
/// of one scalar, the byte-view-of-typed-storage shape (relay 009 / R416-7).
pub(super) const BE64: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type u64_0 = u64;
unsafe extern "C" fn copy_be64(mut pdest: *mut u64_0, mut psource: *mut u64_0) {
    let mut source = psource as *mut libc::c_uchar;
    let mut dest = pdest as *mut libc::c_uchar;
    let mut i: libc::c_int = 0;
    i = 0 as libc::c_int;
    while i < 8 as libc::c_int {
        *dest.offset(i as isize) = *source.offset((7 as libc::c_int - i) as isize);
        i += 1;
    }
}
pub unsafe extern "C" fn swap(mut a: u64_0) -> u64_0 {
    let mut b: u64_0 = 0;
    copy_be64(&mut b, &mut a);
    return b;
}
"#;

/// The byte view delivers: each local is a `size_of::<u64>()`-byte slice over
/// its parameter's own storage and the byte reads and writes index it. The
/// extent is exact although `copy_be64` indexes by a loop counter (R422-7):
/// the view is one scalar's storage, so no UB-free input indexes past it.
#[test]
fn w6b_be64_byte_view_of_a_scalar_parameter_delivers() {
    let rows = super::emit_tests::decisions_of(BE64);
    for name in ["pdest", "psource"] {
        assert_eq!(reason(&rows, name), "<emitted>", "{name}: {rows:?}");
    }
    for name in ["source", "dest"] {
        assert_eq!(local_reason(&rows, name), "<emitted>", "{name}: {rows:?}");
    }
    let source = super::emit_tests::ast_emitted_source_of(BE64).expect("AST output");
    let flat = compact(&source);
    assert!(
        flat.contains("letmutsource:&[u8]=core::slice::from_raw_parts(")
            && flat.contains("*mutlibc::c_uchar,core::mem::size_of::<u64>())"),
        "the read view is a shared byte slice of exactly the scalar's bytes: {source}"
    );
    assert!(
        flat.contains("letmutdest:&mut[u8]=core::slice::from_raw_parts_mut("),
        "the written view is a mutable byte slice: {source}"
    );
    assert!(
        flat.contains("dest[(i)asusize]=source[((7aslibc::c_int-i))asusize]"),
        "the byte accesses index the views: {source}"
    );
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT"),
        "the extent is the scalar's size, never fabricated: {source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "output compiles: {source}"
    );
}

/// The parameter used anywhere but the cast is not in the class: a safe form
/// of it alongside the view would be a second live path to the scalar.
#[test]
fn w6b_byte_view_holds_when_the_parameter_is_reused() {
    let reused = BE64.replace(
        "let mut i: libc::c_int = 0;",
        "let mut again: u64_0 = *psource;\n    let mut i: libc::c_int = 0;",
    );
    let rows = super::emit_tests::decisions_of(&reused);
    assert_eq!(
        local_reason(&rows, "source"),
        "slice-neg-or-unknown-offset",
        "the ladder's own hold stays: {rows:?}"
    );
    assert_eq!(local_reason(&rows, "dest"), "<emitted>", "{rows:?}");
}

/// A pointer to a struct viewed as bytes is not in the class: the rule reads
/// one scalar's bytes.
#[test]
fn w6b_byte_view_of_a_struct_pointer_is_not_in_the_class() {
    let structured = BE64
        .replace(
            "pub type u64_0 = u64;",
            "#[repr(C)] #[derive(Copy, Clone)] pub struct u64_0 { pub lo: u32, pub hi: u32 }",
        )
        .replace(
            "let mut b: u64_0 = 0;",
            "let mut b: u64_0 = u64_0 { lo: 0, hi: 0 };",
        );
    let rows = super::emit_tests::decisions_of(&structured);
    assert_eq!(
        local_reason(&rows, "source"),
        "slice-neg-or-unknown-offset",
        "{rows:?}"
    );
}

/// The view must be BYTES: a cast of the scalar pointer to any wider element
/// is not in the class (its indices are not byte indices).
#[test]
fn w6b_byte_view_needs_a_byte_target() {
    let wide = BE64
        .replace(
            "let mut source = psource as *mut libc::c_uchar;",
            "let mut source = psource as *mut u16;",
        )
        .replace(
            "*source.offset((7 as libc::c_int - i) as isize);",
            "*source.offset((3 as libc::c_int - i / 2) as isize) as u8;",
        );
    let rows = super::emit_tests::decisions_of(&wide);
    assert_eq!(
        local_reason(&rows, "source"),
        "slice-neg-or-unknown-offset",
        "{rows:?}"
    );
}

/// binn `copy_be16` (rs-crown/binn `lib.rs:190`): every index is a constant
/// inside the scalar, so the view is exactly `size_of::<u16>()` bytes.
pub(super) const BE16: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type u16_0 = u16;
unsafe extern "C" fn copy_be16(mut pdest: *mut u16_0, mut psource: *mut u16_0) {
    let mut source = psource as *mut libc::c_uchar;
    let mut dest = pdest as *mut libc::c_uchar;
    *dest.offset(0 as libc::c_int as isize) = *source.offset(1 as libc::c_int as isize);
    *dest.offset(1 as libc::c_int as isize) = *source.offset(0 as libc::c_int as isize);
}
pub unsafe extern "C" fn swap16(mut a: u16_0) -> u16_0 {
    let mut b: u16_0 = 0;
    copy_be16(&mut b, &mut a);
    return b;
}
"#;

#[test]
fn w6b_be16_constant_indices_make_the_view_exact() {
    let rows = super::emit_tests::decisions_of(BE16);
    for name in ["source", "dest"] {
        assert_eq!(local_reason(&rows, name), "<emitted>", "{name}: {rows:?}");
    }
    let source = super::emit_tests::ast_emitted_source_of(BE16).expect("AST output");
    let flat = compact(&source);
    assert!(
        flat.contains("letmutsource:&[u8]=core::slice::from_raw_parts(")
            && flat.contains("*mutlibc::c_uchar,core::mem::size_of::<u16>())"),
        "the read view is exactly the scalar's bytes: {source}"
    );
    assert!(
        flat.contains("letmutdest:&mut[u8]=core::slice::from_raw_parts_mut(")
            && flat.contains("dest[(0aslibc::c_int)asusize]=source[(1aslibc::c_int)asusize]"),
        "the written view indexes: {source}"
    );
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT"),
        "nothing is fabricated: {source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "output compiles: {source}"
    );
}

/// A constant index at or beyond the scalar's size does not move the extent
/// (R422-7): such a read was UB in the input; the view stays exact and the
/// emitted program's bounds check names it.
#[test]
fn w6b_byte_view_index_beyond_the_scalar_stays_exact() {
    let beyond = BE16.replace(
        "*source.offset(1 as libc::c_int as isize);",
        "*source.offset(2 as libc::c_int as isize);",
    );
    let source = super::emit_tests::ast_emitted_source_of(&beyond).expect("AST output");
    let flat = compact(&source);
    assert!(
        flat.contains("letmutsource:&[u8]=core::slice::from_raw_parts(")
            && flat.contains("letmutdest:&mut[u8]=core::slice::from_raw_parts_mut(")
            && flat
                .matches("*mutlibc::c_uchar,core::mem::size_of::<u16>())")
                .count()
                == 2
            && !source.contains("FALLBACK_SLICE_EXTENT"),
        "both views stay exact: {source}"
    );
}

/// A byte-to-byte recast (`*const c_char` as `*const c_uchar`) is a string
/// re-signing, not a scalar's byte view: not in the class. Scoped to THIS
/// lane's form — another family may well type the local (on batch 9's
/// composition one does, under its own fallback extent); what may not appear
/// is a view whose extent is the scalar's own size, this rule's spelling.
#[test]
fn w6b_byte_recast_of_a_char_pointer_is_not_in_the_class() {
    let chars = BE16.replace("pub type u16_0 = u16;", "pub type u16_0 = libc::c_char;");
    let source = super::emit_tests::ast_emitted_source_of(&chars).expect("AST output");
    assert!(
        !source.contains("size_of::<i8>()"),
        "a byte-wide scalar has no byte view: {source}"
    );
}

/// **A void element in a SAFE form is spelled `u8`** (relay 015 item 1,
/// R447-4). brotli's 49 first-cause compile failures at the census head are
/// this one disagreement: a producer that spells the element from the DECLARED
/// pointee emits `&mut [libc::c_void]` / `&[libc::c_void]` where the void
/// families' neighbours emit `&mut [u8]` / `&[u8]`, and the two are different
/// types at the same form, so the seam renders no edit and the crate stops
/// compiling. Every emitted type passes through `declaration::emitted_type`.
#[test]
fn w6b_a_void_element_is_spelled_u8_in_every_safe_form() {
    use super::decision::{Decision, declaration::emitted_type};
    let slice = Decision::Slice {
        mutable: true,
        uses: Vec::new(),
    };
    let shared = Decision::Slice {
        mutable: false,
        uses: Vec::new(),
    };
    let reference = Decision::Ref { mutable: false };
    let optional = Decision::Opt {
        mutable: true,
        slice: true,
        uses: Vec::new(),
    };
    for spelling in [
        "c_void",
        "core::ffi::c_void",
        "::core::ffi::c_void",
        "std::ffi::c_void",
        "libc::c_void",
        "::libc::c_void",
    ] {
        assert_eq!(
            emitted_type(&slice, spelling, None).as_deref(),
            Some("&mut [u8]"),
            "{spelling}"
        );
        assert_eq!(
            emitted_type(&shared, spelling, None).as_deref(),
            Some("&[u8]"),
            "{spelling}"
        );
        assert_eq!(
            emitted_type(&reference, spelling, None).as_deref(),
            Some("&u8"),
            "{spelling}"
        );
        assert_eq!(
            emitted_type(&optional, spelling, None).as_deref(),
            Some("Option<&mut [u8]>"),
            "{spelling}"
        );
    }
    // A nested form's INNER element takes the same spelling.
    let nested = Decision::NestedSlice {
        mutable: true,
        inner_mutable: false,
        uses: Vec::new(),
    };
    assert_eq!(
        emitted_type(&nested, "*const libc::c_void", None).as_deref(),
        Some("&mut [&[u8]]")
    );
    // Every other element is untouched, including one whose NAME contains the
    // void spelling.
    assert_eq!(
        emitted_type(&slice, "uint8_t", None).as_deref(),
        Some("&mut [uint8_t]")
    );
    assert_eq!(
        emitted_type(&slice, "my_c_void_t", None).as_deref(),
        Some("&mut [my_c_void_t]")
    );
}

/// The emission of one fixture with a decision INJECTED at the plan boundary —
/// `emit_tests::emit_injected`'s shape for a string fixture, so a later-stage
/// withdrawal can be witnessed without coaxing one out of source.
fn emitted_source_with(
    input: &str,
    inject: &(dyn Fn(&mut super::decision::DecisionTable) + Sync),
) -> Result<String, String> {
    match ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(input),
        |tcx| {
            let capture = super::ast_transform::capture_ast(tcx)?;
            let (mut table, ctx) = super::decide_table_with_ctx(tcx)?;
            inject(&mut table);
            let emission = super::emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )?;
            let held = emission.plan.held_classes();
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
                &held,
                &std::collections::BTreeSet::new(),
                &table,
            )?;
            let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx,
                &capture,
                &reverts,
                emission.plan.root_file.as_ref(),
                &table,
                Some(&emission.plan.terminal_call_plans),
            )?;
            files
                .into_values()
                .next()
                .ok_or_else(|| "emitted no source file".to_owned())
        },
    ) {
        Ok(inner) => inner,
        Err(why) => Err(format!("{why:?}")),
    }
}

/// **A chain is one unit at WITHDRAWAL time too** (relay 015 item 1, R447-4).
///
/// [`collect`] admits a chain only whole, but a family-stage withdrawal lands
/// after it. brotli's census head shows what that costs: `HeadH40`'s body keeps
/// `(AddrH40 as unsafe extern "C" fn(*mut c_void) -> *mut uint32_t)(extra)`
/// while `AddrH40`'s parameter has become `&mut [u8]` — 45 of the 49 `c_void` ↔
/// byte compile failures. Injected here as the withdrawal of ONE link.
#[test]
fn w6b_a_withdrawn_chain_link_takes_its_siblings() {
    let withdraw_head = |table: &mut super::decision::DecisionTable| {
        for (subject, decision) in &mut table.entries {
            if subject.label.starts_with("HeadH40::") {
                *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                    subject: subject.label.clone(),
                    site: "<injected withdrawal>".to_owned(),
                    reason: super::decision::DegradeReason::VoidPointee,
                });
            }
        }
    };
    let source = emitted_source_with(H40, &withdraw_head).expect("AST output");
    let flat = compact(&source);
    let changed_a_signature = flat.contains("fnAddrH40(mutextra:&mut[u8])")
        || flat.contains("fnHeadH40(mutextra:&mut[u8])")
        || flat.contains("fnTinyHashH40(mutextra:&mut[u8])")
        || flat.contains("fnBanksH40(mutextra:&mut[u8])");
    let names_the_old_signature = flat.contains("asunsafeextern\"C\"fn(*mutcore::ffi::c_void)");
    assert!(
        !(changed_a_signature && names_the_old_signature),
        "a link changed its signature while a sibling body still names the old \
         one — the chain must hold whole: {source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "the tree compiles with one link withdrawn: {source}"
    );
}

/// The decision table of one fixture, for a test that asks a table question.
fn table_of<T: Send>(
    input: &str,
    ask: impl Fn(&super::decision::DecisionTable) -> T + Sync,
) -> Result<T, String> {
    match ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(input),
        |tcx| {
            let (table, _) = super::decide_table_with_ctx(tcx)?;
            Ok(ask(&table))
        },
    ) {
        Ok(inner) => inner,
        Err(why) => Err(format!("{why:?}")),
    }
}

/// The width WRITER and its caller (rs-crown/brotli
/// `src::enc::brotli_bit_stream::{BrotliUnalignedWrite64, BrotliWriteBits}`),
/// the mirror of [`READ32`]. `BrotliWriteBits` extracts a byte pointer from
/// its own `array` and hands it to the writer through a `c_void` cast — the
/// shape wave-5c 023 §3 names as the reason `array` reads `kind-raw`.
pub(super) const WRITE64: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint64_t = u64;
pub type size_t = usize;
unsafe extern "C" fn BrotliUnalignedWrite64(mut p: *mut core::ffi::c_void, mut v: uint64_t) {
    *(p as *mut uint64_t) = v;
}
pub unsafe extern "C" fn BrotliWriteBits(
    mut n_bits: size_t,
    mut bits: uint64_t,
    mut pos: *mut size_t,
    mut array: *mut uint8_t,
) {
    let mut p: *mut uint8_t = &mut *array.offset((*pos >> 3 as i32) as isize) as *mut uint8_t;
    let mut v = *p as uint64_t;
    v |= bits << (*pos & 7 as i32 as size_t);
    BrotliUnalignedWrite64(p as *mut core::ffi::c_void, v);
    *pos = (*pos as size_t).wrapping_add(n_bits) as size_t;
}
"#;

/// **The write side is BUILT and the wall is the analysis's** (relay 021 §1,
/// R455-4). A `c_void` parameter whose whole body is `*(p as *mut T) = v;` is
/// a region of exactly `size_of::<T>()` bytes, written as a checked copy of
/// the value's own bytes. The contract is collected here — and the ladder
/// still refuses the subject with **`kind-raw`**, BO's verdict that a
/// reference to that slot is not sound, which this lane may not override
/// (R395-2). Measured at the record frame: all four
/// `BrotliUnalignedWrite*::p` rows and `BrotliWriteBits`' `array` / `p` carry
/// `model_kind=raw`, against `model_kind=ref` on all 14 read rows.
#[test]
fn w6b_the_width_writer_is_contracted_and_walled_by_the_model() {
    let region = table_of(WRITE64, |table| {
        table.void_region.iter().find_map(|((owner, _), region)| {
            table
                .entries
                .iter()
                .any(|(s, _)| s.fn_did == *owner && s.label.starts_with("BrotliUnalignedWrite64::"))
                .then(|| {
                    (
                        region.shape,
                        region.len_bytes,
                        region.mutable,
                        region.uses.len(),
                    )
                })
        })
    })
    .expect("the fixture yields a table")
    .expect("the writer carries a region contract");
    assert_eq!(
        region,
        (
            super::decision::void_region::Shape::WidthWrite,
            Some(8),
            true,
            1
        ),
        "an exact 8-byte MUTABLE region with one body rewrite"
    );
    let rows = super::emit_tests::decisions_of(WRITE64);
    assert_eq!(
        reason(&rows, "p"),
        "kind-raw",
        "the wall is BO's kind, not this family's hold: {rows:?}"
    );
}

/// A writer whose written VALUE reads the buffer is not in the class: the copy
/// would borrow the region while the value still reads it. Read at the
/// CONTRACT, because `kind-raw` masks every ladder reason on this shape.
#[test]
fn w6b_a_write_whose_value_reads_the_buffer_is_not_contracted() {
    let self_reading = WRITE64.replace(
        "    *(p as *mut uint64_t) = v;",
        "    *(p as *mut uint64_t) = v ^ *(p as *mut uint64_t);",
    );
    let contracts = table_of(&self_reading, |table| table.void_region.len())
        .expect("the fixture yields a table");
    assert_eq!(contracts, 0, "a self-reading write carries no region");
}

/// A body with anything beside the single write is not in the class.
#[test]
fn w6b_a_write_beside_another_statement_is_not_contracted() {
    let extra = WRITE64.replace(
        "    *(p as *mut uint64_t) = v;",
        "    let mut seen = v;\n    *(p as *mut uint64_t) = seen;",
    );
    let contracts =
        table_of(&extra, |table| table.void_region.len()).expect("the fixture yields a table");
    assert_eq!(contracts, 0, "a body beyond the write carries no region");
}

/// **The licensed width, for wave-5c's caller lift** (relay 023 §2).
///
/// The query answers with the callee parameter's EXACT byte width where this
/// family has typed it — a chain link sized by its neighbour, or a width read
/// or write — and with nothing where the extent is the addendum-77 fallback (a
/// fabricated extent licenses no companion, R408-1) or where the parameter is
/// not this family's at all.
#[test]
fn w6b_the_licensed_width_is_exact_or_absent() {
    use crate::bo_rewriter::decision::void_region::licensed_width;
    let widths = table_of(H40, |table| {
        let of = |name: &str, index: usize| {
            table.entries.iter().find_map(|(subject, _)| {
                subject
                    .label
                    .starts_with(&format!("{name}::"))
                    .then(|| licensed_width(table, subject.fn_did, index))
            })
        };
        (
            of("AddrH40", 0),
            of("HeadH40", 0),
            of("BanksH40", 0),
            of("StoreH40", 0),
            of("AddrH40", 1),
        )
    })
    .expect("the fixture yields a table");
    let (addr, head, banks, store, wrong_index) = widths;
    assert!(
        matches!(addr, Some(Some(n)) if n > 0),
        "a chain link sized by its neighbour carries an exact width: {addr:?}"
    );
    assert!(
        matches!(head, Some(Some(n)) if n > 0),
        "so does the next link: {head:?}"
    );
    assert_eq!(
        banks,
        Some(None),
        "the LAST link of a chain rides the addendum-77 fallback and licenses nothing"
    );
    assert_eq!(
        store,
        Some(None),
        "a parameter this family never typed licenses nothing"
    );
    assert_eq!(
        wrong_index,
        Some(None),
        "the width is the named PARAMETER's, not the function's"
    );
    // The width reader's own four bytes, from the other fixture.
    let reader = table_of(READ32, |table| {
        table.entries.iter().find_map(|(subject, _)| {
            subject
                .label
                .starts_with("BrotliUnalignedRead32::")
                .then(|| licensed_width(table, subject.fn_did, 0))
        })
    })
    .expect("the fixture yields a table");
    assert_eq!(reader, Some(Some(4)), "a width read is exactly its width");
}
