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

/// Every call argument a licence renders a length for: `(caller, argument,
/// length)`.
fn lengths(input: &str) -> Vec<(String, String, String)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let licences = Licences::infer(tcx);
        let functions = tcx
            .hir_body_owners()
            .filter(|d| matches!(tcx.def_kind(*d), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let mut out = Vec::new();
        for calls in facts.call_args.values() {
            for call in calls {
                for arg in &call.args {
                    if let Some(length) = licences.length_at(tcx, call.caller, arg.span) {
                        out.push((
                            tcx.item_name(call.caller.to_def_id()).to_string(),
                            flat(
                                &tcx.sess
                                    .source_map()
                                    .span_to_snippet(arg.span)
                                    .unwrap_or_default(),
                            ),
                            length,
                        ));
                    }
                }
            }
        }
        out.sort();
        out
    })
    .expect("fixture compiles")
}

/// The relay 071 review's licence findings: each variant refuses `buffer_`'s
/// licence.
/// - (1) a length written beside only a null pointer write (`resize`);
/// - (2) a length atom reassigned between the allocation and the length write;
/// - (3) the allocation stored conditionally before the pointer is derived;
/// - (4) the length written unconditionally, the pointer conditionally;
/// - (6) a whole-object write (`*rb = *saved`);
/// - (7) a stray length write in a closure;
/// - (10) a signed length field.
#[test]
fn w6l_fa_r_the_review_licence_findings_refuse_it() {
    let mut wrong = Vec::new();
    for (label, from, to) in [
        (
            "(1) null-only resize",
            "pub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
            "pub unsafe fn Resize(mut rb: *mut RingBuffer, mut n: u32) {\n    if n == 0 as i32 as u32 {\n        (*rb).buffer_ = 0 as *mut u8;\n    }\n    (*rb).cur_size_ = n;\n}\npub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
        ),
        (
            "(2) atom reassigned",
            "unsafe fn RingBufferInitBuffer(buflen: u32, mut rb: *mut RingBuffer) {",
            "unsafe fn RingBufferInitBuffer(mut buflen: u32, mut rb: *mut RingBuffer) {",
        ),
        (
            "(3) conditional allocation store",
            "    let ref mut fresh66 = (*rb).data_;\n    *fresh66 = new_data;\n",
            "    if buflen > 0 as i32 as u32 {\n        let ref mut fresh66 = (*rb).data_;\n        *fresh66 = new_data;\n    }\n",
        ),
        (
            "(4) conditional pointer write",
            "    let ref mut fresh67 = (*rb).buffer_;\n    *fresh67 = ((*rb).data_).offset(2 as i32 as isize);\n",
            "    if !new_data.is_null() {\n        let ref mut fresh67 = (*rb).buffer_;\n        *fresh67 = ((*rb).data_).offset(2 as i32 as isize);\n    }\n",
        ),
        (
            "(6) whole-object write",
            "pub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
            "pub unsafe fn Restore(mut rb: *mut RingBuffer, mut saved: *const RingBuffer) {\n    *rb = core::ptr::read(saved);\n}\npub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
        ),
        (
            "(7) stray length in a closure",
            "pub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
            "pub unsafe fn Poke(mut rb: *mut RingBuffer) {\n    let mut f = || (*rb).cur_size_ = 99 as i32 as u32;\n    f();\n}\npub unsafe fn Setup(mut s: *mut State, mut n: u32) {",
        ),
        (
            "(2b) atom reassigned without a call",
            "unsafe fn RingBufferInitBuffer(buflen: u32, mut rb: *mut RingBuffer) {",
            "unsafe fn RingBufferInitBuffer(mut buflen: u32, mut rb: *mut RingBuffer) {",
        ),
        (
            "(4b) conditional length write",
            "    (*rb).cur_size_ = buflen;\n    let ref mut fresh67 = (*rb).buffer_;\n    *fresh67 = ((*rb).data_).offset(2 as i32 as isize);\n",
            "    let ref mut fresh67 = (*rb).buffer_;\n    *fresh67 = ((*rb).data_).offset(2 as i32 as isize);\n    if buflen > 0 as i32 as u32 {\n        (*rb).cur_size_ = buflen;\n    }\n",
        ),
        (
            "(10) signed length",
            "    pub cur_size_: u32,",
            "    pub cur_size_: i32,",
        ),
    ] {
        let mut input = RB.replacen(from, to, 1);
        if label == "(2) atom reassigned" {
            input = input.replacen(
                "    (*rb).cur_size_ = buflen;\n",
                "    buflen = buflen.wrapping_mul(2 as i32 as u32);\n    (*rb).cur_size_ = buflen;\n",
                1,
            );
        }
        if label == "(2b) atom reassigned without a call" {
            input = input.replacen(
                "    (*rb).cur_size_ = buflen;\n",
                "    buflen = buflen + 1 as i32 as u32;\n    (*rb).cur_size_ = buflen;\n",
                1,
            );
        }
        if label == "(10) signed length" {
            input = input
                .replace(
                    "(*rb).cur_size_ = 0 as i32 as u32;",
                    "(*rb).cur_size_ = 0 as i32;",
                )
                .replace(
                    "(*rb).cur_size_ = buflen;",
                    "(*rb).cur_size_ = buflen as i32;",
                );
        }
        assert_ne!(input, RB, "{label}: the variant is in");
        let got = licences(&input);
        if got.iter().any(|l| l.pointer == "buffer_") {
            wrong.push(format!("{label}: {got:?}"));
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// (5) the element type: `n * size_of::<u16>()` over a `*mut u32` holds `n / 2`
/// elements, not `n` (refused); `size_of::<u32>()` holds `n` (the control).
#[test]
fn w6l_fa_r5_the_element_size_is_the_pointee_s() {
    let words = |t: &str| {
        format!(
            r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
extern "C" {{
    fn malloc(n: u64) -> *mut core::ffi::c_void;
}}
pub struct Words {{
    pub w: *mut u32,
    pub n: u32,
}}
pub unsafe fn Init(mut s: *mut Words, mut n: u32) {{
    (*s).w = malloc((n as u64).wrapping_mul(::std::mem::size_of::<{t}>() as u64)) as *mut u32;
    (*s).n = n;
}}
"#
        )
    };
    assert_eq!(licences(&words("u16")), vec![], "u16 over u32");
    assert_eq!(
        licences(&words("u32")),
        vec![Licence {
            strukt: "Words".to_owned(),
            pointer: "w".to_owned(),
            length: "n".to_owned(),
            slack: 0,
        }]
    );
}

/// The review's use findings: no length is rendered at `Encode`'s call.
/// - (5) the argument cast to a wider pointee;
/// - (6) an inner dereference in the base (`(*(*s).rb).buffer_`);
/// - (7) a writer reached through a function pointer;
/// - (8) the local still possibly null at the call.
#[test]
fn w6l_fa_s_the_review_use_findings_render_no_length() {
    let control = lengths(RB);
    assert!(
        control
            .iter()
            .any(|(caller, arg, _)| caller == "Encode" && arg == "data"),
        "the control: {control:#?}"
    );
    let mut wrong = Vec::new();
    for (label, from, to) in [
        (
            "(5) wider cast",
            "    Reader(data, mask, (*s).pos, 16 as i32 as u64)\n}",
            "    Reader(data, mask, (*s).pos, 16 as i32 as u64)\n}\nunsafe fn Wide(mut w: *const u32, mut n: u64) -> u32 {\n    *w.offset(n as isize)\n}\npub unsafe fn Encode32(mut s: *mut State) -> u32 {\n    Wide((*s).ringbuffer_.buffer_ as *const u32, 3 as i32 as u64)\n}",
        ),
        (
            "(7) writer through a fn pointer",
            "    let mut mask = (*s).ringbuffer_.mask_ as u64;\n    Reader(",
            "    let mut mask = (*s).ringbuffer_.mask_ as u64;\n    let mut grow: unsafe fn(u32, *mut RingBuffer) = RingBufferInitBuffer;\n    grow(64 as i32 as u32, &mut (*s).ringbuffer_);\n    Reader(",
        ),
        (
            "(8) possibly null at the call",
            "    data = (*s).ringbuffer_.buffer_;\n",
            "    if (*s).pos > 0 as i32 as u64 {\n        data = (*s).ringbuffer_.buffer_;\n    }\n",
        ),
    ] {
        let input = RB.replacen(from, to, 1);
        assert_ne!(input, RB, "{label}: the variant is in");
        let got = lengths(&input);
        let target = if label.starts_with("(5)") {
            "Encode32"
        } else {
            "Encode"
        };
        let bad: Vec<_> = got
            .iter()
            .filter(|(caller, arg, _)| {
                caller == target && (arg == "data" || arg.contains("buffer_"))
            })
            .collect();
        if !bad.is_empty() {
            wrong.push(format!("{label}: {bad:?}"));
        }
    }
    // (6) an inner dereference: the object is reached through another pointer.
    let inner = RB
        .replace(
            "pub struct State {\n    pub ringbuffer_: RingBuffer,\n    pub pos: u64,\n}",
            "pub struct State {\n    pub ringbuffer_: RingBuffer,\n    pub pos: u64,\n}\n#[repr(C)]\npub struct Outer {\n    pub rb: *mut RingBuffer,\n}",
        )
        .replace(
            "    Reader(data, mask, (*s).pos, 16 as i32 as u64)\n}",
            "    Reader(data, mask, (*s).pos, 16 as i32 as u64)\n}\npub unsafe fn Through(mut o: *mut Outer) -> u32 {\n    Reader((*(*o).rb).buffer_, 4095 as i32 as u64, 0 as i32 as u64, 16 as i32 as u64)\n}",
        );
    let got = lengths(&inner);
    if got.iter().any(|(caller, ..)| caller == "Through") {
        wrong.push(format!("(6) inner dereference: {got:?}"));
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}
