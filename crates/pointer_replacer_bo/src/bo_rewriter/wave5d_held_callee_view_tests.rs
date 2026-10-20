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
    // The stand-in review's LOW-7: the sealed suffix itself, for the raw
    // formal (the source type-checks: `emitted_reverting` asserts it).
    assert!(
        text.contains("convert(64, (&mut (bits)[64..]).as_mut_ptr());"),
        "{source}"
    );
}

/// The stand-in review's HIGH-1: a held callee whose `*const` formal it
/// RETURNS, and the caller writes through the result. The input's pointer is
/// derived from `&mut *bits.offset(64)`, so it is writable; a sealed
/// `.as_ptr()` would hand out a shared-derived pointer (Frozen under Tree
/// Borrows) and the caller's write would be UB. The view must be the writable
/// one, or the caller held — never a shared view.
const RETURNED_CHILD: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
unsafe fn pick(len: usize, p: *const u16) -> *const u16 {
    let mut s = 0u16;
    let mut i = 0usize;
    while i < len {
        s = s.wrapping_add(*p.offset(i as isize));
        i += 1;
    }
    p
}
pub unsafe fn build(bits: *mut u16) {
    *bits.offset(0) = 1;
    *bits.offset(1) = 2;
    let q = pick(64, &mut *bits.offset(64)) as *mut u16;
    *q = 7;
}
"#;

#[test]
fn w5d_205_a_returned_const_child_is_never_a_shared_view() {
    let source = super::emitted_reverting(RETURNED_CHILD, Some("pick"));
    let text = flat(&source);
    assert!(!text.contains("bits.offset(64"), "{source}");
    assert!(
        !text.contains("[64..]).as_ptr()") && !text.contains("(&(bits)[64..])"),
        "a shared view of a written-through child:\n{source}"
    );
}

/// The stand-in review's MED-2: the element arm — a thin-reference callee
/// (`Index0`) — withdrawn, the caller's element address must not be left as
/// the base's pointer arithmetic either.
const ELEMENT_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
unsafe fn put(v: *mut u16) {
    *v = 9;
}
pub unsafe fn build(bits: *mut u16) {
    *bits.offset(0) = 1;
    *bits.offset(1) = 2;
    put(&mut *bits.offset(64));
}
"#;

#[test]
fn w5d_205_a_held_thin_callee_leaves_no_unrendered_element() {
    let source = super::emitted_reverting(ELEMENT_SHAPE, Some("put"));
    assert!(!flat(&source).contains("bits.offset(64"), "{source}");
}

/// The stand-in review's LOW-3: the bare arithmetic (`bits.offset(64)`, the
/// `from_raw_parts` arm) at a withdrawn callee.
const BARE_SHAPE: &str = r#"
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
    convert(64, bits.offset(64));
}
"#;

#[test]
fn w5d_205_a_bare_offset_at_a_held_callee_leaves_no_unrendered_use() {
    let source = super::emitted_reverting(BARE_SHAPE, Some("convert"));
    assert!(!flat(&source).contains("bits.offset(64"), "{source}");
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

/// **Relay 206 (152 item 1 (a)): the HIGH-1 query of the new arm, witnessed
/// where it lives.** No fixture reaches the arm with a returned child: a
/// formal decided `Slice` whose child the caller writes through degrades
/// before planning ends (`SliceCursorUse` / `SliceUseUnsupported` on every
/// shape tried — a returned `p.offset(k)` const or written, a stored child),
/// so the arm only ever meets formals with no child. The selection is
/// therefore a pure function of the view, the target and the child's access,
/// witnessed directly; dropping the query (the RED stub) returns the shared
/// base `slice-to-raw-const` for a written-through child and these go red.
mod computed_view_template {
    use crate::bo_rewriter::decision::{
        callee_parameter_input::computed_view_template,
        raw_boundary::{BridgeTemplate, RawMutability, RawTargetType},
        returned_child::ChildAccess,
        seam::Form,
    };

    fn target(mutability: RawMutability) -> RawTargetType {
        RawTargetType {
            rendered: "*const u16".to_owned(),
            pointee: "u16".to_owned(),
            mutability,
            depth2: None,
        }
    }

    fn writes() -> ChildAccess {
        ChildAccess::Writes {
            sites: Vec::new(),
            unknown_frontiers: Vec::new(),
        }
    }

    #[test]
    fn w5d_206_a_written_through_child_takes_the_writable_view() {
        let access = writes();
        assert_eq!(
            computed_view_template(
                true,
                Form::Ref { mutable: true },
                &target(RawMutability::Const),
                BridgeTemplate::SliceToRawConst,
                Some(Some(&access)),
            ),
            Ok((BridgeTemplate::SliceMutToWritableRawConst, true))
        );
    }

    #[test]
    fn w5d_206_a_shared_argument_written_through_is_refused() {
        let access = writes();
        assert!(
            computed_view_template(
                true,
                Form::Ref { mutable: false },
                &target(RawMutability::Const),
                BridgeTemplate::SliceToRawConst,
                Some(Some(&access)),
            )
            .is_err()
        );
    }

    #[test]
    fn w5d_206_a_shared_base_never_takes_the_writable_view() {
        let access = writes();
        assert!(
            computed_view_template(
                false,
                Form::Ref { mutable: true },
                &target(RawMutability::Const),
                BridgeTemplate::SliceToRawConst,
                Some(Some(&access)),
            )
            .is_err()
        );
    }

    /// An unknown access (no child evidence to read) is treated as a write:
    /// the writable view where the argument permits it, refused where the
    /// argument is a shared borrow.
    #[test]
    fn w5d_206_an_unknown_child_access_takes_the_writable_view_or_refuses() {
        assert_eq!(
            computed_view_template(
                true,
                Form::Ref { mutable: true },
                &target(RawMutability::Const),
                BridgeTemplate::SliceToRawConst,
                Some(None),
            ),
            Ok((BridgeTemplate::SliceMutToWritableRawConst, true))
        );
        assert!(
            computed_view_template(
                true,
                Form::Ref { mutable: false },
                &target(RawMutability::Const),
                BridgeTemplate::SliceToRawConst,
                Some(None),
            )
            .is_err()
        );
    }

    #[test]
    fn w5d_206_control_a_read_only_child_keeps_the_shared_base() {
        let access = ChildAccess::ReadOnly {
            checked_uses: Vec::new(),
        };
        assert_eq!(
            computed_view_template(
                true,
                Form::Ref { mutable: true },
                &target(RawMutability::Const),
                BridgeTemplate::SliceToRawConst,
                Some(Some(&access)),
            ),
            Ok((BridgeTemplate::SliceToRawConst, false))
        );
    }

    #[test]
    fn w5d_206_control_no_child_keeps_the_base() {
        assert_eq!(
            computed_view_template(
                true,
                Form::Ref { mutable: true },
                &target(RawMutability::Const),
                BridgeTemplate::SliceToRawConst,
                None,
            ),
            Ok((BridgeTemplate::SliceToRawConst, false))
        );
    }
}

/// **Relay 206 (152 item 1 (b)): the element and width-read arms, reached.**
/// The callee's formal is planned as a thin reference (`Index0`) or a byte
/// region read as a width (`u32::from_ne_bytes`), and is withdrawn: the
/// caller's computed view is recorded unsealable and the input alternative
/// refuses typed, so the caller's base is held raw and no `bits.offset(4)`
/// is left over a slice. The fault — the arm sealing them — delivers `bits`
/// through a suffix and these go red.
const ELEMENT_BARE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
unsafe fn rd(p: *const u8) -> u32 {
    *(p as *const u32)
}
pub unsafe fn build(bits: *mut u8) -> u32 {
    *bits.offset(0) = 1;
    *bits.offset(1) = 2;
    rd(bits.offset(4))
}
"#;

const WIDTH_READ: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
unsafe fn rd(p: *const core::ffi::c_void) -> u32 {
    *(p as *const u32)
}
pub unsafe fn build(bits: *mut u8) -> u32 {
    *bits.offset(0) = 1;
    *bits.offset(1) = 2;
    rd(bits.offset(4) as *const core::ffi::c_void)
}
"#;

#[test]
fn w5d_206_a_held_element_view_is_refused_typed() {
    let source = super::emitted_reverting(ELEMENT_BARE, Some("rd"));
    let text = flat(&source);
    assert!(text.contains("fn rd(p: *const u8) -> u32"), "{source}");
    assert!(
        text.contains("build(bits: *mut u8)"),
        "the base is held raw:\n{source}"
    );
    assert!(text.contains("rd(bits.offset(4))"), "{source}");
}

#[test]
fn w5d_206_a_held_width_read_view_is_refused_typed() {
    let source = super::emitted_reverting(WIDTH_READ, Some("rd"));
    let text = flat(&source);
    assert!(
        text.contains("fn rd(p: *const core::ffi::c_void) -> u32"),
        "{source}"
    );
    assert!(
        text.contains("build(bits: *mut u8)"),
        "the base is held raw:\n{source}"
    );
}
