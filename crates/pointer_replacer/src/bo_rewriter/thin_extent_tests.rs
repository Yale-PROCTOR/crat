//! R272-1 / R280-1 route (A) — thin references at multi-element foreign
//! positions.
//!
//! A thin `&T` carries provenance for one element. A foreign position whose
//! contract consumes more than one — read to a NUL, to a stated count, or to a
//! source-determined length — is handed that one-element claim and accesses
//! past it. Miri confirms it on the `strlen` shape: UB under Stacked Borrows,
//! clean under Tree Borrows, the same split `&c_void` showed.
//!
//! **The load-bearing witness is corpus-verified** (R274-1): the emission run
//! over the frozen cache on the 13 programs carrying the census's 88 sites. The
//! tests here are the shape controls around it — what the hold must NOT touch,
//! and the predicate it reads.

fn reasons(src: &str) -> std::collections::BTreeMap<String, String> {
    super::emit_tests::decisions_of(src)
        .into_iter()
        .map(|(name, _, reason)| (name, reason))
        .collect()
}

/// **The verbatim corpus transplant** (R274-3): `copyFileName` and its caller
/// copied from the derived bzip2 source with the two real argument shapes —
/// `copyFileName(inName.as_mut_ptr(), name)` over
/// `pub static mut inName: [Char; 1034]`, and a bare local `name: *mut Char`.
///
/// `from` reaches three non-one-element positions in one body: `strlen`
/// (nul-terminated), the `fprintf` `%s` tail (nul-terminated) and `strncpy`
/// (byte-count). It is one of the census's 56 subjects.
const TRANSPLANT_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe, unused_mut, non_upper_case_globals, non_snake_case)]
    pub type Char = i8;
    #[repr(C)]
    pub struct FILE {
        pub handle: i32,
    }
    extern "C" {
        fn strlen(s: *const i8) -> usize;
        fn strncpy(dest: *mut i8, src: *const i8, n: usize) -> *mut i8;
        fn fprintf(stream: *mut FILE, fmt: *const i8, ...) -> i32;
    }
    pub static mut inName: [Char; 1034] = [0; 1034];
    pub static mut outName: [Char; 1034] = [0; 1034];
    pub static mut stream: *mut FILE = 0 as *mut FILE;

    unsafe extern "C" fn copyFileName(mut to: *mut Char, mut from: *mut Char) {
        if strlen(from) > (1034 as i32 - 10 as i32) as usize {
            fprintf(stream,
                    b"bzip2: file name\n`%s'\nis suspiciously long.\n\x00" as *const u8
                        as *const i8, from,
                    1034 as i32 - 10 as i32);
            return;
        }
        strncpy(to, from, (1034 as i32 - 10 as i32) as usize);
        *to.offset((1034 as i32 - 10 as i32) as isize) = '\u{0}' as i32 as Char;
    }

    pub unsafe fn compress(mut name: *mut Char) {
        copyFileName(inName.as_mut_ptr(), name);
        copyFileName(outName.as_mut_ptr(), name);
    }
"#;

/// The control that keeps the rule about EXTENT rather than about references: a
/// subject with array evidence takes a slice form, which carries an extent, and
/// still bridges to the same counted position.
const SLICE_CONTROL_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    extern "C" {
        fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8;
    }
    pub unsafe fn fill(dest: *mut u8, src: *mut u8, n: usize) {
        *src.offset(1) = 7;
        *dest.offset(1) = 3;
        memcpy(dest, src, n);
    }
"#;

/// A ONE-ELEMENT position is exactly what a thin reference can carry, so it is
/// untouched. Without this control the hold could quietly become "no thin
/// references at libc calls at all".
const ONE_ELEMENT_CONTROL_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    #[repr(C)]
    pub struct stat_t { pub size: i64 }
    extern "C" {
        fn stat(path: *const i8, buf: *mut stat_t) -> i32;
    }
    pub unsafe fn size_of_file(buf: *mut stat_t) -> i64 {
        stat(b"f\x00" as *const u8 as *const i8, buf);
        (*buf).size
    }
"#;

/// An UNMODELED foreign position claims no extent, so it holds nothing:
/// absence of a contract is not evidence of a multi-element access.
const UNMODELED_CONTROL_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    #[repr(C)]
    pub struct widget_t { pub id: i32 }
    extern "C" {
        fn vendor_take(w: *const widget_t) -> i32;
    }
    pub unsafe fn use_widget(w: *const widget_t) -> i32 {
        vendor_take(w)
    }
"#;

#[test]
fn thin_extent_transplant_of_the_bzip2_shape() {
    let got = reasons(TRANSPLANT_INPUT);
    // **Reported as observed, and it does NOT reach the hold.** Measured:
    // `from` degrades `call-site-not-adapted` and its sibling `to` degrades
    // `slice-use-unsupported`.
    //
    // The precondition, verified rather than assumed: `LiftAdaptable`
    // (`decision/mod.rs:1762`) is NOT the blocker — `copyFileName` is
    // referenced by two `RefKind::Call` sites, so `RefKind::is_adaptable` is
    // true. The refusal is the co-conversion admission: `from` is not admitted
    // as a node and neither `node_block` nor `class_block` names a reason, so
    // it takes the `CallSiteNotAdapted` fallback arm at `decision/mod.rs:1860`.
    // What the small crate cannot adapt is the SIBLING argument —
    // `inName.as_mut_ptr()`, a raw expression over a static array — and
    // refusing that call site takes both parameters with it.
    //
    // So the assertion here is the property the transplant CAN carry: this
    // subject is not delivered as a thin reference. The load-bearing witness
    // for the identity is the corpus emission run (R274-1).
    let from = got.get("from").map(String::as_str);
    assert!(
        from.is_some(),
        "the transplant must produce a decision for `from`: {got:#?}"
    );
    assert_ne!(
        from,
        Some("<emitted>"),
        "`from` reaches strlen, an fprintf %s tail and strncpy: it may not be \
         delivered as a thin reference: {got:#?}"
    );
}

/// A slice carries its extent, so the same position is fine for it.
#[test]
fn slice_at_a_multi_element_position_still_bridges() {
    let got = reasons(SLICE_CONTROL_INPUT);
    for subject in ["dest", "src"] {
        assert_ne!(
            got.get(subject).map(String::as_str),
            Some("held:thin-extent"),
            "{subject} has array evidence and carries an extent: {got:#?}"
        );
    }
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(SLICE_CONTROL_INPUT)
    else {
        panic!("the slice control must emit")
    };
    assert!(
        super::verify::type_checks_str(&source),
        "emitted output type/borrow-checks:\n{source}"
    );
}

#[test]
fn one_element_position_is_untouched() {
    let got = reasons(ONE_ELEMENT_CONTROL_INPUT);
    assert_ne!(
        got.get("buf").map(String::as_str),
        Some("held:thin-extent"),
        "a `stat` buffer is exactly one element: {got:#?}"
    );
}

#[test]
fn unmodeled_foreign_position_is_untouched() {
    let got = reasons(UNMODELED_CONTROL_INPUT);
    assert_ne!(
        got.get("w").map(String::as_str),
        Some("held:thin-extent"),
        "no contract row means no extent claim: {got:#?}"
    );
}

/// The predicate itself, read off the pinned contract table rather than a
/// symbol list — which is what keeps one classification in one place.
#[test]
fn the_predicate_is_the_contract_extent() {
    use super::decision::{
        raw_boundary::{ForeignSymbolKey, RawMutability, RawTargetType},
        thin_extent::position_consumes_many_elements,
    };

    let callee = |name: &str| ForeignSymbolKey {
        symbol: name.to_owned(),
        path: format!("fixture::{name}"),
        abi: "C".to_owned(),
        signature: "fixture-signature".to_owned(),
        foreign: true,
    };
    let chars = RawTargetType {
        rendered: "*const i8".to_owned(),
        pointee: "i8".to_owned(),
        mutability: RawMutability::Const,
        depth2: None,
    };
    let mut_chars = RawTargetType {
        mutability: RawMutability::Mut,
        rendered: "*mut i8".to_owned(),
        ..chars.clone()
    };

    // Multi-element: the NUL-terminated family (80 of the census's 88 sites)
    // and the counted family alike.
    assert!(position_consumes_many_elements(
        &callee("strlen"),
        0,
        &chars
    ));
    assert!(position_consumes_many_elements(
        &callee("strcmp"),
        1,
        &chars
    ));
    assert!(position_consumes_many_elements(&callee("fopen"), 0, &chars));
    assert!(position_consumes_many_elements(
        &callee("strncpy"),
        1,
        &chars
    ));
    assert!(position_consumes_many_elements(
        &callee("strcpy"),
        0,
        &mut_chars
    ));
    // `%s` in a printf tail is a string, not one element.
    assert!(position_consumes_many_elements(
        &callee("printf"),
        1,
        &chars
    ));

    // One element, lifecycle, and unmodeled all answer no.
    let stat_buf = RawTargetType {
        rendered: "*mut stat_t".to_owned(),
        pointee: "stat_t".to_owned(),
        mutability: RawMutability::Mut,
        depth2: None,
    };
    assert!(!position_consumes_many_elements(
        &callee("stat"),
        1,
        &stat_buf
    ));
    assert!(!position_consumes_many_elements(
        &callee("free"),
        0,
        &mut_chars
    ));
    assert!(!position_consumes_many_elements(
        &callee("vendor_take"),
        0,
        &chars
    ));
}
