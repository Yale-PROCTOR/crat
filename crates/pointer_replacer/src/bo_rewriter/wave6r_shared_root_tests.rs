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

#[test]
fn wave6r_h65_shared_root_field_address_into_readonly_raw_formal() {
    let source = super::emitted(INPUT);
    assert!(source.contains("s: &H65"), "{source}");
    assert!(
        source.contains("prepare_h6(core::ptr::from_ref(&(*s).ha).cast_mut()"),
        "{source}"
    );
    assert!(
        source.contains("prepare_hrolling(core::ptr::from_ref(&(*s).hb).cast_mut()"),
        "{source}"
    );
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
    assert!(
        source.contains("prepare_h6(&mut (*s).ha, cache)"),
        "{source}"
    );
    assert!(!source.contains("from_ref"), "{source}");
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
