//! wave-5d relay 205 (main 219 §4; wave-5d 150p §2.3): brotli
//! `compress_fragment_two_pass::BuildAndStoreCommandPrefixCode` passes
//! `&mut *bits.offset(64)` — `bits` a delivered slice — to
//! `BrotliConvertBitDepthsToSymbols`, whose class is held
//! (`dependency-class-held`). Planned against the callee's slice formal, the
//! argument is the callee class's computed suffix view; with that class
//! withdrawn the formal is raw again, the view goes with its class, and the
//! caller's own use of `bits` inside the argument was rendered by nobody:
//! `.offset` on `&mut [u16]` (E0599), the caller reverted.

const BITS_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
unsafe fn convert(len: usize, bits: *mut u16) {
    let mut i = 0usize;
    while i < len {
        *bits.offset(i as isize) = i as u16;
        i += 1;
    }
}
pub unsafe fn build(bits: *mut u16) {
    *bits.offset(0) = 1;
    *bits.offset(1) = 2;
    convert(64, &mut *bits.offset(64));
}
"#;

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// RED: the callee's class withdrawn (as a held class is), the caller's
/// delivered slice still renders its use inside the argument — through the
/// suffix view, sealed for the raw formal — and the caller type-checks.
#[test]
fn w5d_205_a_held_callee_keeps_the_callers_suffix_view() {
    let source = super::emitted_reverting(BITS_SHAPE, Some("convert"));
    let text = flat(&source);
    assert!(
        text.contains("bits: &mut [u16]"),
        "the caller's slice stays delivered:\n{source}"
    );
    assert!(
        text.contains("convert(len: usize, bits: *mut u16)"),
        "the withdrawn callee is its input:\n{source}"
    );
    assert!(
        !text.contains("bits.offset(64"),
        "no use of the delivered slice is left unrendered:\n{source}"
    );
}

/// Control: the callee kept, the computed suffix view is the callee class's
/// own seam edit, unchanged.
#[test]
fn w5d_205_control_a_kept_callee_takes_the_suffix_view() {
    let source = super::emitted(BITS_SHAPE);
    let text = flat(&source);
    assert!(text.contains("bits: &mut [u16]"), "{source}");
    assert!(!text.contains("bits.offset(64"), "{source}");
}
