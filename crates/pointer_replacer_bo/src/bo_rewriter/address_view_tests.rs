//! **R506-3 — nested address views, and the fat operand's thin view.**
//!
//! A pointer comparison is rendered by the raw-boundary ADDRESS VIEW: each
//! safe operand is replaced by a raw view of itself, so the comparison keeps
//! comparing addresses (`decision/mod.rs`'s gate exists because the same
//! expression on references would compare POINTEES). Two gaps, both measured
//! in report 056 and main 071c:
//!
//!  * an operand that is a CAST of a safe subject plans TWO views at nested
//!    spans — the inner subject's and the cast's own `ptr-cast` sink — and
//!    neither is applied, leaving the function byte-identical;
//!  * a FAT operand (`&[T]`) viewed with `core::ptr::from_ref` yields a fat
//!    raw pointer, and `==` on fat pointers compares the metadata too: two
//!    slices over one base with fabricated extents would compare unequal
//!    where the input compared equal.
use super::{emit_tests::ast_emitted_source_of, verify};

/// **Case C** (heman `kmVec4Assign`): the disequality's second operand is a
/// cast of the other parameter.
const CAST_OPERAND: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct V4 { pub x: f32, pub y: f32 }
pub unsafe fn kmVec4Assign(mut pOut: *mut V4, mut pIn: *const V4) -> i32 {
    if pOut != pIn as *mut V4 {} else { return 0 as i32; }
    (*pOut).x = (*pIn).x;
    (*pOut).y = (*pIn).y;
    return 1 as i32;
}
"#;

/// **Case A** — two shared operands, bare. It emits today and must keep doing so.
const BARE_SHARED: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn same(mut a: *const i32, mut b: *const i32) -> i32 {
    if a == b { return 1 as i32; }
    return *a + *b;
}
"#;

/// **Case B** — two exclusive operands, bare. Likewise.
const BARE_MUT: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct V4 { pub x: f32, pub y: f32 }
pub unsafe fn assign2(mut pOut: *mut V4, mut pIn: *mut V4) -> i32 {
    if pOut != pIn {} else { return 0 as i32; }
    (*pOut).x = (*pIn).x;
    return 1 as i32;
}
"#;

/// **The fat operand** — `buf` is indexed with arithmetic, so it takes a slice
/// form; `mark` is thin. The comparison must compare the ELEMENT addresses.
const FAT_VS_THIN: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn at_start(mut buf: *const u8, mut mark: *const u8, mut n: usize) -> i32 {
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < n { total += *buf.offset(i as isize) as i32; i = i.wrapping_add(1); }
    if buf == mark { return total; }
    return 0 as i32;
}
"#;

/// **Two fat operands** over one base: the extents may be fabricated, so the
/// metadata must not enter the comparison.
const FAT_VS_FAT: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn both(mut a: *const u8, mut b: *const u8, mut n: usize) -> i32 {
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < n {
        total += *a.offset(i as isize) as i32;
        total += *b.offset(i as isize) as i32;
        i = i.wrapping_add(1);
    }
    if a == b { return total; }
    return 0 as i32;
}
"#;

fn emitted(input: &str) -> String {
    let output = ast_emitted_source_of(input).expect("native emission");
    assert!(verify::type_checks_str(&output), "{output}");
    output
}

/// **W6O-AV-1 — the delivering witness.** The cast operand's nested views
/// compose: the inner view lands inside the cast, and the emitted comparison
/// is between two raw pointers.
#[test]
fn wave6o_a_cast_operand_composes_its_inner_address_view() {
    assert!(verify::type_checks_str(CAST_OPERAND));
    let output = emitted(CAST_OPERAND);
    assert_ne!(
        output.trim(),
        CAST_OPERAND.trim(),
        "the function is emitted, not left byte-identical"
    );
    assert!(
        output.contains("core::ptr::from_ref(pIn) as *mut V4")
            || output.contains("core::ptr::from_ref(pIn).cast_mut()"),
        "the inner view lands inside the cast: {output}"
    );
    assert!(
        output.contains("core::ptr::from_mut(&mut *pOut)")
            || output.contains("core::ptr::from_mut(pOut)"),
        "and the other operand keeps its own view, however it reborrows: {output}"
    );
    assert!(
        output.contains("pOut: &mut V4") && output.contains("pIn: &V4"),
        "both subjects are delivered as references: {output}"
    );
}

/// **Control A** — the bare shared pair keeps emitting exactly as it did.
#[test]
fn wave6o_a_bare_shared_identity_still_renders_both_views() {
    let output = emitted(BARE_SHARED);
    assert!(
        output.contains("core::ptr::from_ref(a) == core::ptr::from_ref(b)"),
        "{output}"
    );
}

/// **Control B** — the bare exclusive pair likewise.
#[test]
fn wave6o_a_bare_exclusive_identity_still_renders_both_views() {
    let output = emitted(BARE_MUT);
    assert_ne!(output.trim(), BARE_MUT.trim(), "{output}");
    assert!(
        output.contains("pOut") && output.contains("pIn"),
        "{output}"
    );
}

/// **W6O-AV-2 — a FAT operand compares on the element address.** `from_ref` of
/// a `&[T]` would carry the length into the comparison; the view must be the
/// thin pointer.
#[test]
fn wave6o_a_fat_operand_takes_the_thin_address() {
    let output = emitted(FAT_VS_THIN);
    // **Re-premised (R506-3 / main 071c): the property is that the comparison
    // is THIN, not which spelling delivers it.** `core::ptr::from_ref` of a
    // `&[T]` would carry the length into `==`; measured, this shape is the
    // CURSOR family's and it compares `buf.addr() == mark.addr()` — also thin.
    assert!(
        !output.contains("core::ptr::from_ref(buf) =="),
        "a fat operand must not be compared as a fat pointer: {output}"
    );
    assert!(
        output.contains("buf.addr()") || output.contains("buf.as_ptr()"),
        "the fat operand's comparison is on a thin address: {output}"
    );
}

/// **W6O-AV-3 — two fat operands.** Same rule on both sides, so the metadata
/// never enters the comparison.
#[test]
fn wave6o_a_two_fat_operands_compare_on_element_addresses() {
    let output = emitted(FAT_VS_FAT);
    // Re-premised with its twin: both sides thin, whichever family delivers.
    assert!(
        (output.contains("a.addr()") && output.contains("b.addr()"))
            || (output.contains("a.as_ptr()") && output.contains("b.as_ptr()")),
        "both fat operands compare on thin addresses: {output}"
    );
    assert!(
        !output.contains("core::ptr::from_ref(a) =="),
        "and neither is compared as a fat pointer: {output}"
    );
}
