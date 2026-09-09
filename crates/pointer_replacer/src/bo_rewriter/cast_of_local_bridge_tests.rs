//! K19′ (§39 addendum 272, R272-2) — the `cast-of-local` bridge at a raw
//! callee whose parameter pointee is `c_void`.
//!
//! R271-1 holds every `c_void` slot, so the *callee* end of a
//! `f(x as *const c_void)` edge stops converting and the caller end leaves
//! `cast-of-converting-local` for `flows-into-raw-param`. The delivery that
//! was left on the table is the caller end itself.
//!
//! **Measured blocking cause.** The argument SHAPE was never the obstacle: a
//! `cast-of-local` site is registered, opened and rendered today — the thin
//! control below already emits `core::ptr::from_ref(data).cast::<c_void>()`,
//! the whole argument (cast included) replaced by the carrier. What blocked
//! the rest is the void branch of `template_for`, which names only the
//! reference forms: a settled `Slice` subject at a `c_void` position answered
//! `TemplateUnavailable`. R272-2's four renderings are exactly the missing
//! cells, and `.cast::<c_void>()` is how this machinery already spells the
//! `as *const c_void` the seat wrote — the same conversion, one syntax.
//!
//! The subject's own extent is what makes the bridge sound: the raw view is
//! taken from the caller's slice or reference, so the pointer carries
//! `len * size_of::<T>()` (or `size_of::<T>()`) bytes rather than the one byte
//! a `&c_void` would have carried.

fn reasons(src: &str) -> std::collections::BTreeMap<String, String> {
    super::emit_tests::decisions_of(src)
        .into_iter()
        .map(|(name, _, reason)| (name, reason))
        .collect()
}

fn emitted(src: &str) -> String {
    match super::rewrite_m1(src) {
        super::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("fixture must emit: {other:#?}"),
    }
}

/// Every fixture shares this skeleton: one raw callee whose `c_void`
/// parameter R271-1 holds, and one caller whose local converts and reaches it
/// through a cast.
fn fixture(sink: &str, declaration: &str, body: &str) -> String {
    format!(
        "#![allow(dead_code, unused_unsafe, unused_mut)]\n\
         {sink}\n\
         pub unsafe fn target({declaration}) -> i32 {{ {body} }}\n"
    )
}

const SHARED: &str = "p: *const i32";
const MUTABLE: &str = "p: *mut i32";

const READ_SINK: &str = "unsafe fn raw_read(q: *const core::ffi::c_void) -> i32 \
                         { let r = q as *const i32; r.read() }";
const WRITE_SINK: &str = "unsafe fn raw_write(q: *mut core::ffi::c_void) \
                          { let r = q as *mut i32; r.write(1); }";

/// The thin control, and the reason this file exists at all: it passes TODAY.
/// A `cast-of-local` argument is already opened and already rendered; the
/// carrier replaces the whole argument and folds the original cast into
/// `.cast::<c_void>()`.
#[test]
fn k19_thin_subject_already_bridges_through_the_void_carrier() {
    const INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub unsafe fn take(p: *const core::ffi::c_void) {
        let q = p as *const u64;
        let _ = *q;
    }
    pub unsafe fn hash(data: *const u8) {
        take(data as *const core::ffi::c_void)
    }
"#;
    let got = reasons(INPUT);
    assert_eq!(
        got.get("p").map(String::as_str),
        Some("held:void-pointee"),
        "the callee end is held: {got:#?}"
    );
    assert_eq!(
        got.get("data").map(String::as_str),
        Some("<emitted>"),
        "the caller end delivers: {got:#?}"
    );
    let source = emitted(INPUT);
    assert!(
        source.contains("core::ptr::from_ref(data).cast::<core::ffi::c_void>()"),
        "the thin carrier keeps the subject's own extent:\n{source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "emitted output type/borrow-checks:\n{source}"
    );
}

/// R272-2's slice cell at a `*const` position: `x.as_ptr()` then the cast.
#[test]
fn k19_shared_slice_subject_bridges_through_as_ptr() {
    let input = fixture(
        READ_SINK,
        SHARED,
        "let seen = *p.offset(1); seen + raw_read(p as *const core::ffi::c_void)",
    );
    let got = reasons(&input);
    assert_eq!(
        got.get("p").map(String::as_str),
        Some("<emitted>"),
        "a slice subject at a void position delivers: {got:#?}"
    );
    let source = emitted(&input);
    assert!(
        source.contains("p.as_ptr().cast::<core::ffi::c_void>()"),
        "the slice carrier spells the cast it replaced:\n{source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "emitted output type/borrow-checks:\n{source}"
    );
}

/// R272-2's `*mut` cell: `x.as_mut_ptr()` then the cast.
#[test]
fn k19_mutable_slice_subject_at_a_mut_position_uses_as_mut_ptr() {
    let input = fixture(
        WRITE_SINK,
        MUTABLE,
        "*p.offset(1) += 1; raw_write(p as *mut core::ffi::c_void); *p.offset(0)",
    );
    let got = reasons(&input);
    assert_eq!(
        got.get("p").map(String::as_str),
        Some("<emitted>"),
        "a mutable slice subject at a mutable void position delivers: {got:#?}"
    );
    let source = emitted(&input);
    assert!(
        source.contains("p.as_mut_ptr().cast::<core::ffi::c_void>()"),
        "the mutable slice carrier keeps write permission:\n{source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "emitted output type/borrow-checks:\n{source}"
    );
}

/// R272-2's mutable-subject-at-a-`*const`-position cell, through the
/// writable-const carrier R259-2 established: a mutable subject never presents
/// a shared derivation, because a pointer the callee hands back could be
/// written through.
#[test]
fn k19_mutable_slice_subject_at_a_const_position_uses_the_writable_const_carrier() {
    let input = fixture(
        READ_SINK,
        MUTABLE,
        "*p.offset(1) += 1; raw_read(p as *const core::ffi::c_void)",
    );
    let got = reasons(&input);
    assert_eq!(
        got.get("p").map(String::as_str),
        Some("<emitted>"),
        "a mutable slice subject at a const void position delivers: {got:#?}"
    );
    let source = emitted(&input);
    assert!(
        source.contains("p.as_mut_ptr().cast::<core::ffi::c_void>().cast_const()"),
        "the const position is reached through a WRITABLE derivation:\n{source}"
    );
    assert!(
        !source.contains("p.as_ptr().cast::<core::ffi::c_void>()"),
        "the shared spelling is retired for a mutable subject:\n{source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "emitted output type/borrow-checks:\n{source}"
    );
}

/// The mismatched-carrier fault, as a standing control. A SHARED subject at a
/// `*mut` position has no negative-write evidence here, so no carrier may be
/// invented for it: `SharedToMut` still holds the site.
#[test]
fn k19_shared_slice_subject_at_a_mut_position_is_still_held() {
    let input = fixture(
        WRITE_SINK,
        SHARED,
        "let seen = *p.offset(1); raw_write(p as *mut core::ffi::c_void); seen",
    );
    let got = reasons(&input);
    assert_ne!(
        got.get("p").map(String::as_str),
        Some("<emitted>"),
        "a shared subject may not manufacture a mutable raw view: {got:#?}"
    );
    let source = emitted(&input);
    assert!(
        !source.contains("as_mut_ptr"),
        "no mutable carrier is emitted for a shared subject:\n{source}"
    );
}

/// The tier fault, as a standing control. A callee that RETAINS its argument
/// may not bridge at all — the whole two-tier design is that retention decides
/// admission before any carrier is chosen.
#[test]
fn k19_retaining_callee_does_not_bridge() {
    let input = format!(
        "#![allow(dead_code, unused_unsafe, unused_mut)]\n\
         static mut SINK: *const core::ffi::c_void = core::ptr::null();\n\
         unsafe fn keep(q: *const core::ffi::c_void) {{ SINK = q; }}\n\
         pub unsafe fn target(p: *mut i32) -> i32 \
         {{ *p.offset(1) += 1; keep(p as *const core::ffi::c_void); *p.offset(0) }}\n"
    );
    let got = reasons(&input);
    assert_ne!(
        got.get("p").map(String::as_str),
        Some("<emitted>"),
        "a retained pointer forbids the bridge: {got:#?}"
    );
}
