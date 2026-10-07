//! wave-6a relay 133 (R738-1): brotli's two L01¹² E0382 rows, reduced.
//!
//! - `decode::CopyUncompressedBlockToOutput` (lib.rs:113671): the caller's
//!   optional `next_out` is handed bare to `WriteRingBuffer`'s optional formal
//!   inside the decoder's loop, so the call moves it. Two gaps in the optional
//!   reborrow pass: a call inside a loop the binding outlives has a later use
//!   (the next pass), and an A5 raw-view wrapper re-parses the call it wraps,
//!   so the argument no longer carries its source span.
//! - `common::transform::BrotliTransformDictionaryWord` (lib.rs:101357): the
//!   cursor's tail view at a slice formal (`ToUpperCase(&mut *dst.offset(k))`)
//!   was `dst.offset_by(k).as_slice_mut()`, which consumes the mutable cursor
//!   the suffix loop then writes through.

use super::wave6a_allocation_tests::{compact, rewrite_precise};
use crate::analyses::borrow_ownership::SlotKind;

const PRELUDE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn memcpy(dst: *mut core::ffi::c_void, src: *const core::ffi::c_void, n: usize) -> *mut core::ffi::c_void;
}
"#;

/// brotli `WriteRingBuffer`, reduced: `next_out` is null-tested (optional),
/// the other pointers stay raw.
const WRITE_RING_BUFFER: &str = r#"
pub struct State {
    pub ring: *mut u8,
    pub pos: i32,
    pub sub: i32,
    pub out_pos: usize,
}
unsafe extern "C" fn WriteRingBuffer(
    mut s: *mut State,
    mut available_out: *mut usize,
    mut next_out: *mut *mut u8,
    mut total_out: *mut usize,
    mut force: i32,
) -> i32 {
    let mut start = ((*s).ring).offset((*s).pos as isize);
    let mut num_written = *available_out;
    if !next_out.is_null() && (*next_out).is_null() {
        *next_out = start;
    } else if !next_out.is_null() {
        memcpy(*next_out as *mut core::ffi::c_void, start as *const core::ffi::c_void, num_written);
        *next_out = (*next_out).offset(num_written as isize);
    }
    *available_out = (*available_out).wrapping_sub(num_written);
    (*s).out_pos = (*s).out_pos.wrapping_add(num_written);
    if !total_out.is_null() {
        *total_out = (*s).out_pos;
    }
    return force;
}
"#;

/// brotli's decoder shape: `BrotliDecoderDecompressStream` nulls `next_out`
/// when there is no room, and passes it on inside its state loop — to
/// `WriteRingBuffer` directly and through `CopyUncompressedBlockToOutput`.
const RING: &str = r#"
// w6a-r738-ring-frame
unsafe extern "C" fn CopyUncompressedBlockToOutput(
    mut available_out: *mut usize,
    mut next_out: *mut *mut u8,
    mut total_out: *mut usize,
    mut s: *mut State,
) -> i32 {
    loop {
        let mut result = 0 as i32;
        result = WriteRingBuffer(s, available_out, next_out, total_out, 0 as i32);
        if result != 0 as i32 {
            return result;
        }
        (*s).sub = 0 as i32;
    }
}
pub unsafe extern "C" fn Decompress(
    mut s: *mut State,
    mut available_out: *mut usize,
    mut next_out: *mut *mut u8,
    mut total_out: *mut usize,
) -> i32 {
    let mut result = 0 as i32;
    if *available_out == 0 as usize {
        next_out = 0 as *mut *mut u8;
    }
    loop {
        if (*s).sub == 1 as i32 {
            result = WriteRingBuffer(s, available_out, next_out, total_out, 0 as i32);
            if result != 0 as i32 {
                break;
            }
        }
        result = CopyUncompressedBlockToOutput(available_out, next_out, total_out, s);
        if result != 0 as i32 {
            break;
        }
    }
    return result;
}
"#;

/// One call in a loop, no sibling bridge: the call's only later use is the
/// loop's next pass. Control: `fresh` declares its optional inside the loop,
/// so each pass moves a new binding.
const LOOP: &str = r#"
// w6a-r738-loop-frame
pub unsafe extern "C" fn pump(
    mut s: *mut State,
    mut available_out: *mut usize,
    mut next_out: *mut *mut u8,
    mut total_out: *mut usize,
) -> i32 {
    let mut result = 0 as i32;
    if *available_out == 0 as usize {
        next_out = 0 as *mut *mut u8;
    }
    while (*s).sub != 0 as i32 {
        result = WriteRingBuffer(s, available_out, next_out, total_out, 0 as i32);
        if result != 0 as i32 {
            break;
        }
    }
    return result;
}
pub unsafe extern "C" fn fresh(
    mut s: *mut State,
    mut available_out: *mut usize,
    mut total_out: *mut usize,
) -> i32 {
    let mut result = 0 as i32;
    while (*s).sub != 0 as i32 {
        let mut next_out: *mut *mut u8 = &mut (*s).ring;
        if *available_out == 0 as usize {
            next_out = 0 as *mut *mut u8;
        }
        result = WriteRingBuffer(s, available_out, next_out, total_out, 0 as i32);
        if result != 0 as i32 {
            break;
        }
    }
    return result;
}
"#;

/// The decoder's shape without its loop: the first call has a later use, and a
/// sibling argument (`total_out`, a reference both calls are handed) wraps the
/// call in an A5 raw view.
const WRAPPED: &str = r#"
// w6a-r738-wrapped-frame
unsafe extern "C" fn sink(mut available_out: *mut usize, mut next_out: *mut *mut u8, mut total_out: *mut usize, mut s: *mut State) -> i32 {
    return WriteRingBuffer(s, available_out, next_out, total_out, 1 as i32);
}
pub unsafe extern "C" fn twice(
    mut s: *mut State,
    mut available_out: *mut usize,
    mut next_out: *mut *mut u8,
    mut total_out: *mut usize,
) -> i32 {
    let mut result = 0 as i32;
    if *available_out == 0 as usize {
        next_out = 0 as *mut *mut u8;
    }
    if (*s).sub == 1 as i32 {
        result = WriteRingBuffer(s, available_out, next_out, total_out, 0 as i32);
        if result != 0 as i32 {
            return result;
        }
    }
    result = sink(available_out, next_out, total_out, s);
    return result;
}
"#;

fn pinned(marker: &str, name: &str, body: &str, locals: &[(&str, SlotKind)]) -> (String, usize) {
    let _frame = super::test_model_override::frame_lock();
    let src = format!("{PRELUDE}{WRITE_RING_BUFFER}{body}");
    let mut model = vec![
        ("WriteRingBuffer::s", SlotKind::Raw),
        ("WriteRingBuffer::available_out", SlotKind::Raw),
        ("WriteRingBuffer::next_out", SlotKind::Ref),
        ("WriteRingBuffer::total_out", SlotKind::Raw),
        ("WriteRingBuffer::start", SlotKind::Raw),
    ];
    model.extend_from_slice(locals);
    super::test_model_override::set(
        marker,
        Vec::new(),
        model.into_iter().map(|(l, k)| (l.to_owned(), k)).collect(),
    );
    let outcome = rewrite_precise(name, &src);
    super::test_model_override::clear();
    match outcome {
        super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        } => (source, reverted_count),
        super::RewriteOutcome::Degraded {
            reason,
            first_diags,
            ..
        } => panic!("{name} must emit: {reason}\n{first_diags:#?}"),
    }
}

/// The brotli rows' composed shape: both gaps at once, at the census's model
/// (`WriteRingBuffer::next_out` optional, the caller's optional, the
/// intermediate callee's formal a reference).
#[test]
fn w6a_r738_a_reborrowed_optional_out_parameter_in_the_decoder_loop_compiles() {
    let (source, reverted) = pinned(
        "w6a-r738-ring-frame",
        "r738-ring",
        RING,
        &[
            ("CopyUncompressedBlockToOutput::s", SlotKind::Ref),
            (
                "CopyUncompressedBlockToOutput::available_out",
                SlotKind::Ref,
            ),
            ("CopyUncompressedBlockToOutput::next_out", SlotKind::Ref),
            ("CopyUncompressedBlockToOutput::total_out", SlotKind::Ref),
            ("Decompress::s", SlotKind::Raw),
            ("Decompress::available_out", SlotKind::Ref),
            ("Decompress::next_out", SlotKind::Ref),
            ("Decompress::total_out", SlotKind::Ref),
        ],
    );
    let text = compact(&source);
    assert_eq!(reverted, 0, "{source}");
    assert!(
        text.contains("mutnext_out:Option<&mut*mutu8>,"),
        "the caller's optional is delivered: {source}"
    );
    assert!(
        text.contains("WriteRingBuffer(s,available_out,next_out.as_deref_mut(),"),
        "the loop's wrapped call lends: {source}"
    );
}

#[test]
fn w6a_r738_a_call_in_a_loop_the_binding_outlives_lends_its_optional() {
    // R866-1 / R870-1 (relay 302, main 194): with `fresh` beside it, `fresh`'s
    // `next_out = &mut (*s).ring` is handed to `WriteRingBuffer` beside the whole
    // `s` (contained), so `WriteRingBuffer::next_out` is held raw for every
    // caller; the loop's lend is witnessed on `pump` alone.
    let pump_only = &LOOP[..LOOP
        .find("pub unsafe extern \"C\" fn fresh(")
        .expect("fresh")];
    let (source, reverted) = pinned(
        "w6a-r738-loop-frame",
        "r738-loop",
        pump_only,
        &[
            ("pump::s", SlotKind::Raw),
            ("pump::available_out", SlotKind::Raw),
            ("pump::next_out", SlotKind::Ref),
            ("pump::total_out", SlotKind::Raw),
        ],
    );
    let text = compact(&source);
    assert_eq!(reverted, 0, "{source}");
    assert!(
        text.contains("WriteRingBuffer(s,available_out,next_out.as_deref_mut(),total_out,0asi32)"),
        "pump lends at its loop's only call: {source}"
    );
    // With the control: a binding declared inside the loop is a new binding each
    // pass, and it lies inside `s` — the containment pair holds the callee's
    // `next_out`, so both calls stay raw.
    let (source, reverted) = pinned(
        "w6a-r738-loop-frame",
        "r738-loop",
        LOOP,
        &[
            ("pump::s", SlotKind::Raw),
            ("pump::available_out", SlotKind::Raw),
            ("pump::next_out", SlotKind::Ref),
            ("pump::total_out", SlotKind::Raw),
            ("fresh::s", SlotKind::Raw),
            ("fresh::available_out", SlotKind::Raw),
            ("fresh::next_out", SlotKind::Ref),
            ("fresh::total_out", SlotKind::Raw),
        ],
    );
    let text = compact(&source);
    assert_eq!(reverted, 0, "{source}");
    // R866-1 / R870-1 (relay 302, main 194): WriteRingBuffer::next_out is held
    // (contained, at fresh); pump's lend → the raw call.
    let pump = &text[text.find("fnpump(").expect("pump")..text.find("fnfresh(").expect("fresh")];
    assert!(
        pump.contains("WriteRingBuffer(s,available_out,next_out,total_out,0asi32)"),
        "pump's call stays raw beside the held formal: {source}"
    );
    let fresh = &text[text.find("fnfresh(").expect("fresh")..];
    assert!(
        fresh.contains("WriteRingBuffer(s,available_out,next_out,total_out,0asi32)"),
        "fresh moves its own binding: {source}"
    );
}

/// Under R829-1 / R861-1 (relay 297, main 188) the sibling the A5 raw view was
/// built for is held: `twice::available_out` / `twice::total_out` (and
/// `sink`'s `s` / `available_out` / `total_out`) are borrowed into
/// `WriteRingBuffer`'s raw formals beside siblings the callee writes (`s`,
/// `available_out`, `total_out`) and are decided raw
/// (`held:pair-not-shown-disjoint`). No `__crat_a5_raw_` view wraps the first
/// call any more; the call still lends the optional, which is this witness's
/// subject.
#[test]
fn w6a_r738_a_wrapped_call_lends_its_optional() {
    let (source, reverted) = pinned(
        "w6a-r738-wrapped-frame",
        "r738-wrapped",
        WRAPPED,
        &[
            ("sink::s", SlotKind::Ref),
            ("sink::available_out", SlotKind::Ref),
            ("sink::next_out", SlotKind::Ref),
            ("sink::total_out", SlotKind::Ref),
            ("twice::s", SlotKind::Raw),
            ("twice::available_out", SlotKind::Ref),
            ("twice::next_out", SlotKind::Ref),
            ("twice::total_out", SlotKind::Ref),
        ],
    );
    let text = compact(&source);
    assert_eq!(reverted, 0, "{source}");
    // R829-1 (relay 297, main 188): twice::available_out / twice::total_out are
    // held beside the written s / available_out / total_out at WriteRingBuffer;
    // the pinned `result={let__crat_a5_raw_` view of total_out is gone, both
    // stay `*mut usize` and the first call is bare.
    assert!(
        text.contains(
            "fntwice(muts:*mutState,mutavailable_out:*mutusize,mutnext_out:Option<&mut*mutu8>,muttotal_out:*mutusize)"
        ),
        "{source}"
    );
    assert!(
        !text.contains("__crat_a5_raw_"),
        "no sibling raw view wraps the first call: {source}"
    );
    assert!(
        text.contains(
            "result=WriteRingBuffer(s,available_out,next_out.as_deref_mut(),total_out,0asi32);"
        ),
        "the first call lends: {source}"
    );
    // The final call keeps its transfer (wave-6r's rule, unchanged).
    assert_eq!(
        text.matches("next_out.as_deref_mut()").count(),
        1,
        "{source}"
    );
}

/// brotli `common::transform::BrotliTransformDictionaryWord`, reduced: the
/// c2rust idiom handed straight to slice callees, then a write through `dst`.
/// `word` is a shared cursor handed the same way (the control).
const TRANSFORM: &str = r#"
// w6a-r738-transform-frame
unsafe extern "C" fn ToUpperCase(mut p: *mut u8) -> i32 {
    if (*p.offset(0 as i32 as isize) as i32) < 0xc0 as i32 {
        *p.offset(0 as i32 as isize) = (*p.offset(0 as i32 as isize) as i32 ^ 32 as i32) as u8;
        return 1 as i32;
    }
    *p.offset(1 as i32 as isize) = (*p.offset(1 as i32 as isize) as i32 ^ 32 as i32) as u8;
    return 2 as i32;
}
unsafe extern "C" fn Shift(mut word: *mut u8, mut word_len: i32, mut parameter: u16) -> i32 {
    if word_len < 2 as i32 {
        return 1 as i32;
    }
    *word.offset(0 as i32 as isize) = (*word.offset(1 as i32 as isize) as u16 ^ parameter) as u8;
    return 2 as i32;
}
unsafe extern "C" fn Weight(mut p: *const u8, mut n: i32) -> i32 {
    let mut w = 0 as i32;
    let mut i = 0 as i32;
    while i < n {
        w += *p.offset(i as isize) as i32;
        i += 1;
    }
    return w;
}
pub unsafe extern "C" fn TransformWord(
    mut dst: *mut u8,
    mut word: *const u8,
    mut len: i32,
    mut t: i32,
    mut param: u16,
) -> i32 {
    let mut idx = 0 as i32;
    let mut i = 0 as i32;
    while i < len {
        let fresh7 = i;
        i = i + 1;
        let fresh8 = idx;
        idx = idx + 1;
        *dst.offset(fresh8 as isize) = *word.offset(fresh7 as isize);
    }
    let mut weight = Weight(&*word.offset((i - len) as isize), len);
    if t == 10 as i32 {
        ToUpperCase(&mut *dst.offset((idx - len) as isize));
    } else if t == 30 as i32 {
        Shift(&mut *dst.offset((idx - len) as isize), len, param);
    }
    let fresh12 = idx;
    idx = idx + 1;
    *dst.offset(fresh12 as isize) = weight as u8;
    return idx + *word.offset(0 as i32 as isize) as i32;
}
"#;

#[test]
fn w6a_r738_a_mutable_cursor_lends_its_tail_view_to_a_slice_callee() {
    let _frame = super::test_model_override::frame_lock();
    let src = format!("{PRELUDE}{TRANSFORM}");
    let (source, reverted) = match rewrite_precise("r738-transform", &src) {
        super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        } => (source, reverted_count),
        super::RewriteOutcome::Degraded {
            reason,
            first_diags,
            ..
        } => panic!("the transform must emit: {reason}\n{first_diags:#?}"),
    };
    let text = compact(&source);
    assert_eq!(reverted, 0, "{source}");
    assert!(
        text.contains("letmutdst=crate::slice_cursor::SliceCursorMut::new(dst);"),
        "dst is a mutable cursor: {source}"
    );
    for callee in ["ToUpperCase(", "Shift("] {
        assert!(
            text.contains(&format!("{callee}dst.as_deref_mut().offset_by(")),
            "{callee} takes a reborrowed tail view: {source}"
        );
    }
    assert!(
        text.contains("dst[(0isize).wrapping_add((fresh12asisize)asisize)]=weightasu8;"),
        "dst is written after the calls: {source}"
    );
    // Control: a shared cursor is `Copy`; its tail view needs no lend.
    assert!(
        text.contains("Weight(word.offset_by("),
        "the shared cursor's view: {source}"
    );
}
