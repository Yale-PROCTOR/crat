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
