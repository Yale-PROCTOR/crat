//! Reduced from brotli PrepareDistanceCacheH65: a shared root's field address
//! reaches a callee whose formal stays raw and is never written through.
const INPUT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
pub struct H6 { num: i32 }
pub struct HROLLING { tag: i32 }
pub struct H65 { ha: H6, hb: HROLLING }
pub unsafe fn prepare_h6(s: *mut H6, cache: *mut i32) {
    *cache = (*s).num + (s as usize) as i32;
}
pub unsafe fn prepare_hrolling(s: *mut HROLLING, cache: *mut i32) {
    *cache += (s as usize) as i32;
}
pub unsafe fn prepare_h65(s: *mut H65, cache: *mut i32) {
    prepare_h6(&mut (*s).ha, cache);
    prepare_hrolling(&mut (*s).hb, cache);
}
"#;

/// **Re-premised under R517-8 (wave-6o 061, granted).** The callees' formals
/// used to stay raw, so the caller needed `from_ref(&(*s).ha).cast_mut()` to
/// reach them. They stayed raw only because their own `(s as usize)` address
/// cast planned TWO views at one span, and the duplicate held their class —
/// which dropped every edit the class owned, silently. With one view per span
/// (`0973661df`) both formals convert and the caller hands them the reference
/// directly: +2 formals, −2 bridges. The shared root's own delivery, which is
/// what this test was written for, is unchanged and still asserted.
#[test]
fn wave6r_h65_shared_root_field_address_into_readonly_raw_formal() {
    let source = super::emitted(INPUT);
    assert!(source.contains("s: &H65"), "{source}");
    assert!(source.contains("prepare_h6(s: &H6"), "{source}");
    assert!(source.contains("prepare_hrolling(s: &HROLLING"), "{source}");
    assert!(source.contains("prepare_h6(&(*s).ha"), "{source}");
    assert!(source.contains("prepare_hrolling(&(*s).hb"), "{source}");
    assert!(!source.contains("&mut (*s)"), "{source}");
}

/// The per-function placement where the callee class is withdrawn: the
/// formal is its raw input again, the shared root still bridges read-only.
#[test]
fn wave6r_h65_withdrawn_callee_class_keeps_shared_root_bridge() {
    let source = super::emitted_reverting(INPUT, Some("prepare_hrolling"));
    assert!(source.contains("s: &H65"), "{source}");
    assert!(
        source.contains("prepare_hrolling(s: *mut HROLLING"),
        "{source}"
    );
    assert!(
        source.contains("prepare_hrolling(core::ptr::from_ref(&(*s).hb).cast_mut()"),
        "{source}"
    );
    assert!(!source.contains("&mut (*s)"), "{source}");
}

/// A raw root keeps its original mutable address: nothing to re-spell.
#[test]
fn wave6r_h65_reverted_caller_keeps_original_address() {
    let source = super::emitted_reverting(INPUT, Some("prepare_h65"));
    assert!(source.contains("s: *mut H65"), "{source}");
    // **Re-premised under R517-8.** Two things moved with `0973661df`, both
    // outside this test's subject. The CALLEES now render their own
    // `(s as usize)` address cast, so the file-global `!from_ref` is scoped to
    // the reverted caller's own body; and the caller passes `cache` through
    // the A5 raw local its certificate licensed (`revert-residue:a5-raw-local`,
    // accepted noise by the same ruling — a raw local into a raw formal opens
    // no channel), so the argument is matched by name rather than verbatim.
    let reverted = source
        .split("pub unsafe fn prepare_h65")
        .nth(1)
        .expect("the reverted caller is emitted");
    assert!(reverted.contains("prepare_h6(&mut (*s).ha,"), "{source}");
    assert!(!reverted.contains("from_ref"), "{source}");
}

/// A callee that writes through the formal makes the root mutable upstream;
/// the shared view is never selected and the mutable address stands.
#[test]
fn wave6r_h65_written_formal_keeps_mutable_root() {
    let source = super::emitted(&INPUT.replace(
        "*cache = (*s).num + (s as usize) as i32;",
        "(*s).num += 1; *cache = (s as usize) as i32;",
    ));
    assert!(source.contains("s: &mut H65"), "{source}");
    assert!(!source.contains("from_ref(&(*s).ha)"), "{source}");
}
