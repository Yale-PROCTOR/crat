//! R271-1 — the void-pointee hold.
//!
//! `c_void` is `#[repr(u8)]` with two hidden variants, so it is a **one-byte**
//! type. A reference to it therefore carries one byte of provenance, while a
//! `c_void` pointer in C2Rust output is an opaque byte address whose callee's
//! first act is to cast it to the type it actually wants and access at that
//! width. Miri confirms the emitted `&c_void` form is UB under Stacked Borrows
//! at the second byte; the finding record carries the receipts.
//!
//! No reference form of `c_void` can carry the right provenance, so the pointee
//! is not convertible at any depth.

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

/// The Miri fixture's own shape: a `*const c_void` parameter that the body
/// casts and reads eight bytes through. Before the hold this emitted
/// `p: &core::ffi::c_void`, whose retag covers `[0x0..0x1)`.
const VOID_READ_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub unsafe fn read64(p: *const core::ffi::c_void) -> u64 {
        let q = p as *const u64;
        *q
    }
"#;

/// The mutable twin.
const VOID_WRITE_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub unsafe fn write64(p: *mut core::ffi::c_void, v: u64) {
        let q = p as *mut u64;
        *q = v;
    }
"#;

/// The caller end of the edge the census found 519 of. With the callee's
/// parameter no longer converting, the caller falls out of
/// `CastOfConvertingLocal` and takes the ordinary raw-boundary bridge, whose
/// pointer carries the caller subject's own full extent.
const CALLER_END_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub unsafe fn read64(p: *const core::ffi::c_void) -> u64 {
        let q = p as *const u64;
        *q
    }
    pub unsafe fn hash(data: *const u8) -> u64 {
        read64(data as *const core::ffi::c_void)
    }
"#;

/// Depth 2: the outer slot is an ordinary pointer-to-pointer, the inner one is
/// a stream of bytes. The hold is per slot, so the inner one is what stops it.
const DEPTH2_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub unsafe fn take(pp: *mut *mut core::ffi::c_void) -> u64 {
        let q = *pp as *mut u64;
        *q
    }
"#;

/// The typed control. A pointee that is NOT `c_void` still converts, so the
/// hold cannot become a blanket refusal of dereferencing pointer parameters.
const TYPED_CONTROL_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub unsafe fn read_typed(p: *const u8) -> u8 {
        *p
    }
"#;

#[test]
fn void_pointee_read_parameter_is_held() {
    let got = reasons(VOID_READ_INPUT);
    assert_eq!(
        got.get("p").map(String::as_str),
        Some("held:void-pointee"),
        "a one-byte pointee cannot carry the extent its callee reads: {got:#?}"
    );
    assert!(
        emitted(VOID_READ_INPUT).contains("p: *const core::ffi::c_void"),
        "the parameter keeps its raw form"
    );
}

/// The mutable twin. Recorded as observed rather than forced: the MODEL already
/// calls this parameter Raw (`kind-raw`) once it is written through a wider
/// cast, so it never reaches the void hold. That is a stronger refusal, not a
/// weaker one, and the property that matters is asserted directly — the
/// parameter is not delivered as `&mut c_void`.
#[test]
fn void_pointee_write_parameter_is_not_delivered_as_a_reference() {
    let got = reasons(VOID_WRITE_INPUT);
    assert_ne!(
        got.get("p").map(String::as_str),
        Some("<emitted>"),
        "a written void pointee may not take a reference form: {got:#?}"
    );
    let source = emitted(VOID_WRITE_INPUT);
    assert!(
        source.contains("p: *mut core::ffi::c_void"),
        "the parameter keeps its raw form:\n{source}"
    );
    assert!(
        !source.contains("&mut core::ffi::c_void"),
        "no mutable void reference is emitted anywhere:\n{source}"
    );
}

/// The caller end of the edge the census found 519 of.
///
/// **Expectation migrated under R217-2(a) for R364-2 (seat addendum 364).**
/// R271-1 reasoned that with the callee's parameter no longer converting, the
/// caller "takes the ordinary raw-boundary bridge, whose pointer carries the
/// caller subject's own full extent". That is exactly right and it is exactly
/// the hole: here the caller's subject is ITSELF thin, so its own full extent
/// is one byte, while `read64` casts to `*const u64` and reads eight. The
/// caller end is therefore held too, by `held:local-callee-access-extent` —
/// the sibling of `held:thin-extent` that reads a LOCAL callee's body where
/// the other reads a pinned foreign contract.
///
/// The measured note this test used to carry — that the caller left the cast
/// pair but did not deliver, because the raw-boundary bridge opens `bare-local`
/// and `addr-of` and this one is a `cast-of-local` — is now moot for this
/// fixture and is preserved in the R271-3 delta record.
#[test]
fn void_pointee_caller_end_is_held_for_its_own_extent() {
    let got = reasons(CALLER_END_INPUT);
    assert_eq!(
        got.get("p").map(String::as_str),
        Some("held:void-pointee"),
        "the callee end is held: {got:#?}"
    );
    assert_eq!(
        got.get("data").map(String::as_str),
        Some("held:local-callee-access-extent"),
        "a thin caller subject read eight bytes deep is held at its own end too: {got:#?}"
    );
    let source = emitted(CALLER_END_INPUT);
    assert!(
        source.contains("hash(data: *const u8)"),
        "the held caller subject keeps the raw form that carries the buffer:\n{source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "emitted output type/borrow-checks:\n{source}"
    );
}

#[test]
fn void_pointee_holds_per_slot_at_depth_two() {
    let got = reasons(DEPTH2_INPUT);
    assert_eq!(
        got.get("pp").map(String::as_str),
        Some("held:void-pointee"),
        "the inner slot's pointee is the stream of bytes: {got:#?}"
    );
}

#[test]
fn typed_pointee_still_converts() {
    let got = reasons(TYPED_CONTROL_INPUT);
    assert_ne!(
        got.get("p").map(String::as_str),
        Some("held:void-pointee"),
        "the hold is about `c_void`, not about pointers: {got:#?}"
    );
}
