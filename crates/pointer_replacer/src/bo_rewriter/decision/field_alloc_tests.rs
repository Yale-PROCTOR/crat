//! wave-6l relay 071 (R697-7): the field-carried allocation length, and the
//! masked-index hold narrowed to chains whose root would take a fabricated
//! length.

use super::field_alloc::{Licence, Licences};

/// brotli's ring buffer, reduced: `RingBufferInitBuffer` allocates `2 + buflen
/// + 7`, stores it in `data_`, sets `cur_size_ = buflen` and `buffer_ = data_ +
/// 2` (C2Rust's `let ref mut` writes); `Encode` reads `buffer_` into a local
/// declared null (C89) and hands it with the mask to a reader that reads past
/// the masked index by a runtime length.
const RB: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, non_upper_case_globals)]
extern "C" {
    fn malloc(n: u64) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct RingBuffer {
    pub size_: u32,
    pub mask_: u32,
    pub cur_size_: u32,
    pub data_: *mut u8,
    pub buffer_: *mut u8,
}
#[repr(C)]
pub struct State {
    pub ringbuffer_: RingBuffer,
    pub pos: u64,
}
unsafe fn RingBufferInit(mut rb: *mut RingBuffer) {
    (*rb).cur_size_ = 0 as i32 as u32;
    let ref mut fresh63 = (*rb).data_;
    *fresh63 = 0 as *mut u8;
    let ref mut fresh64 = (*rb).buffer_;
    *fresh64 = 0 as *mut u8;
}
unsafe fn RingBufferInitBuffer(buflen: u32, mut rb: *mut RingBuffer) {
    static mut kSlackForEightByteHashingEverywhere: u64 = 7 as i32 as u64;
    let mut new_data = if ((2 as i32 as u32).wrapping_add(buflen) as u64)
        .wrapping_add(kSlackForEightByteHashingEverywhere)
        > 0 as i32 as u64
    {
        malloc(
            ((2 as i32 as u32).wrapping_add(buflen) as u64)
                .wrapping_add(kSlackForEightByteHashingEverywhere)
                .wrapping_mul(::std::mem::size_of::<u8>() as u64),
        ) as *mut u8
    } else {
        0 as *mut u8
    };
    if !((*rb).data_).is_null() {
        free((*rb).data_ as *mut core::ffi::c_void);
        let ref mut fresh65 = (*rb).data_;
        *fresh65 = 0 as *mut u8;
    }
    let ref mut fresh66 = (*rb).data_;
    *fresh66 = new_data;
    (*rb).cur_size_ = buflen;
    let ref mut fresh67 = (*rb).buffer_;
    *fresh67 = ((*rb).data_).offset(2 as i32 as isize);
}
unsafe fn Reader(mut data: *const u8, mut mask: u64, mut ix: u64, mut len: u64) -> u32 {
    let mut masked = ix & mask;
    let mut k: u64 = 0 as i32 as u64;
    let mut s: u32 = 0 as i32 as u32;
    while k < len {
        s = s.wrapping_add(*data.offset(masked.wrapping_add(k) as isize) as u32);
        k = k.wrapping_add(1);
    }
    s
}
pub unsafe fn Encode(mut s: *mut State) -> u32 {
    let mut data = 0 as *mut u8;
    data = (*s).ringbuffer_.buffer_;
    let mut mask = (*s).ringbuffer_.mask_ as u64;
    Reader(data, mask, (*s).pos, 16 as i32 as u64)
}
pub unsafe fn Setup(mut s: *mut State, mut n: u32) {
    RingBufferInit(&mut (*s).ringbuffer_);
    RingBufferInitBuffer(n, &mut (*s).ringbuffer_);
}
"#;

fn licences(input: &str) -> Vec<Licence> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| Licences::infer(tcx).licences)
        .expect("fixture compiles")
}

/// `(fn, param)` → the decision row's reason (`<emitted>` when delivered).
fn reasons(input: &str) -> Vec<(String, String, String)> {
    crate::bo_rewriter::emit_tests::artifact_rows_of(input)
        .into_iter()
        .filter(|r| r.arg_index.is_some())
        .map(|r| {
            (
                r.fn_path.rsplit("::").next().unwrap_or_default().to_owned(),
                r.param_name.clone().unwrap_or_default(),
                r.degrade_reason
                    .clone()
                    .unwrap_or_else(|| "<emitted>".to_owned()),
            )
        })
        .collect()
}

fn reason_of(rows: &[(String, String, String)], function: &str, param: &str) -> String {
    rows.iter()
        .find(|(f, p, _)| f == function && p == param)
        .map(|(_, _, r)| r.clone())
        .unwrap_or_else(|| panic!("no row {function}::{param}: {rows:#?}"))
}

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// FA1 — the licence: `buffer_` holds `cur_size_ + 7` (and `data_`, the
/// allocation itself, `cur_size_ + 9`).
#[test]
fn w6l_fa1_the_ring_buffer_licence_is_inferred() {
    assert_eq!(
        licences(RB),
        vec![
            Licence {
                strukt: "RingBuffer".to_owned(),
                pointer: "buffer_".to_owned(),
                length: "cur_size_".to_owned(),
                slack: 7,
            },
            // `data_` itself holds the whole allocation, `2 + buflen + 7`.
            Licence {
                strukt: "RingBuffer".to_owned(),
                pointer: "data_".to_owned(),
                length: "cur_size_".to_owned(),
                slack: 9,
            },
        ]
    );
}

/// FA2 — the reader is released (its root now takes a real length) and the
/// root's construction renders `cur_size_ + 7`, not the fallback.
#[test]
fn w6l_fa2_the_root_takes_the_field_length_and_the_reader_is_delivered() {
    let rows = reasons(RB);
    assert_eq!(reason_of(&rows, "Reader", "data"), "<emitted>", "{rows:#?}");
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(RB).unwrap();
    let flat = flat(&source);
    assert!(
        flat.contains(
            "core::slice::from_raw_parts(data, ((*s).ringbuffer_.cur_size_ as usize + 7) as usize)"
        ),
        "{source}"
    );
    assert!(!flat.contains("FALLBACK_SLICE_EXTENT"), "{source}");
}

/// FA-c — the licence's controls: each refuses `buffer_`'s. (`data_`'s, the
/// allocation itself, may stand: `alloc(buflen)` holds `buflen`.)
#[test]
fn w6l_fa_c_the_licence_controls_refuse_it() {
    let mut wrong = Vec::new();
    for (label, from, to) in [
        // a stray write to the length elsewhere
        (
            "stray length write",
            "pub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
            "pub unsafe fn Grow(mut s: *mut State) {\n    (*s).ringbuffer_.cur_size_ = 100000 as i32 as u32;\n}\npub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
        ),
        // the offset past the allocation: `data_ + 2` over `alloc(buflen)` is `buflen - 2`
        (
            "negative slack",
            "((2 as i32 as u32).wrapping_add(buflen) as u64)\n                .wrapping_add(kSlackForEightByteHashingEverywhere)\n                .wrapping_mul",
            "(buflen as u64)\n                .wrapping_mul",
        ),
        // a non-null pointer from a struct literal
        (
            "struct literal",
            "pub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
            "pub unsafe fn Other(mut p: *mut u8) -> RingBuffer {\n    RingBuffer { size_: 0, mask_: 0, cur_size_: 0, data_: p, buffer_: p }\n}\npub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
        ),
        // the length's address escapes
        (
            "escaped length",
            "pub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
            "unsafe fn poke(mut p: *mut u32) {\n    *p = 3 as i32 as u32;\n}\npub unsafe fn Leak(mut s: *mut State) {\n    poke(&mut (*s).ringbuffer_.cur_size_);\n}\npub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
        ),
    ] {
        let input = RB.replacen(from, to, 1);
        assert_ne!(input, RB, "{label}: the variant is in");
        let got = licences(&input);
        if got.iter().any(|l| l.pointer == "buffer_") {
            wrong.push(format!("{label}: {got:?}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// FA-u — the use site's controls: the licence holds, but the length may not
/// be read at this call, so the reader stays held.
/// - a writer called between the local's definition and the call (the field
///   reassigned between the allocation and the read);
/// - the local defined from two different objects' fields;
/// - the object's root reassigned after the local's definition;
/// - a direct read in a function that may reallocate the field.
#[test]
fn w6l_fa_u_the_use_controls_keep_the_hold() {
    let mut wrong = Vec::new();
    for (label, from, to) in [
        (
            "writer between",
            "    let mut mask = (*s).ringbuffer_.mask_ as u64;\n    Reader(",
            "    let mut mask = (*s).ringbuffer_.mask_ as u64;\n    RingBufferInitBuffer(64 as i32 as u32, &mut (*s).ringbuffer_);\n    Reader(",
        ),
        (
            "two objects",
            "pub unsafe fn Encode(mut s: *mut State) -> u32 {\n    let mut data = 0 as *mut u8;\n    data = (*s).ringbuffer_.buffer_;",
            "pub unsafe fn Encode(mut s: *mut State, mut t: *mut State, mut c: i32) -> u32 {\n    let mut data = 0 as *mut u8;\n    data = (*s).ringbuffer_.buffer_;\n    if c != 0 as i32 {\n        data = (*t).ringbuffer_.buffer_;\n    }",
        ),
        (
            "root reassigned",
            "pub unsafe fn Encode(mut s: *mut State) -> u32 {\n    let mut data = 0 as *mut u8;\n    data = (*s).ringbuffer_.buffer_;",
            "pub unsafe fn Encode(mut s: *mut State, mut t: *mut State) -> u32 {\n    let mut data = 0 as *mut u8;\n    data = (*s).ringbuffer_.buffer_;\n    s = t;",
        ),
        (
            "direct read in a writer",
            "    Reader(data, mask, (*s).pos, 16 as i32 as u64)\n}",
            "    Reader(data, mask, (*s).pos, 16 as i32 as u64)\n}\npub unsafe fn Refill(mut s: *mut State) -> u32 {\n    RingBufferInitBuffer(64 as i32 as u32, &mut (*s).ringbuffer_);\n    Reader((*s).ringbuffer_.buffer_, 4095 as i32 as u64, (*s).pos, 16 as i32 as u64)\n}",
        ),
    ] {
        let input = RB.replacen(from, to, 1);
        assert_ne!(input, RB, "{label}: the variant is in");
        let rows = reasons(&input);
        let got = reason_of(&rows, "Reader", "data");
        if got != "held:masked-index-runtime-length" {
            wrong.push(format!("{label}: {got}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
