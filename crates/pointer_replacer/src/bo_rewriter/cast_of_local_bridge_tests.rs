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

/// The thin control. **Expectation migrated under R217-2(a) for R364-2, and
/// the fixture is kept exactly, because the fixture IS the finding.**
///
/// This test asserted that `data: *const u8` delivers and renders
/// `core::ptr::from_ref(data).cast::<core::ffi::c_void>()`, under the comment
/// "the thin carrier keeps the subject's own extent". Both halves were true and
/// together they are seat addendum 364's defect in miniature: the subject's own
/// extent is ONE BYTE, the carrier hands it to `take`, and `take` casts to
/// `*const u64` and reads EIGHT. The emitted program was UB under Stacked
/// Borrows at the second byte — the same thing R271-1 held the callee's own
/// parameter for, arriving from the caller's end instead.
///
/// The carrier mechanism itself is not in question and is not what changed:
/// `k19_shared_slice_subject_bridges_through_as_ptr` below still renders a
/// carrier
/// from a subject that carries a real extent. What this control now pins is
/// that the THIN subject no longer reaches it.
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
    // **Re-premised by R481-1 / R482-3 (the USER's extent-lift waiver), by
    // wave-4 under relay 057 STOP 2 — this lineage has no standing lane and the
    // arm is wave-4's.** The hold still DECIDES: every evidence arm refuses
    // this subject, which is why it reaches the waiver at all. What the waiver
    // then gives it is the fabricated-extent slice, so the claim is asserted
    // where it still states the rule — the carrier must not render a THIN
    // one-element view (below), and no evidence-backed width may be invented
    // (here). The SB defect this witness was built for is superseded for the
    // fallback form by R482-3, whose remaining hazard is the slice-length UB
    // §77 already waives.
    assert_eq!(
        got.get("data").map(String::as_str),
        Some("<emitted>"),
        "the waiver gives the refused subject the fabricated-extent form: {got:#?}"
    );
    let source = emitted(INPUT);
    assert!(
        !source.contains("core::ptr::from_ref(data)"),
        "no thin carrier is rendered for a subject the callee reads past:\n{source}"
    );
    // The claim that survives R482-3: whatever form the waiver gives the
    // subject, it is never a THIN one-element carrier — the assertion above —
    // and the emitted crate still type-checks below. The old "keeps its raw
    // form" wording stated the pre-waiver terminal outcome, not the rule.
    assert!(
        !source.contains("hash(data: &u8)") && !source.contains("hash(data: &mut u8)"),
        "no one-element carrier reaches the eight-byte reader:\n{source}"
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

/// The mismatched-carrier fault, as a standing control, and the boundary of
/// the approved arm. A SHARED subject at a `*mut` position is not one of
/// R272-2's four cells: `SharedToMut` holds the site, and it holds it
/// **unconditionally**, not merely for want of negative-write evidence.
/// Negative-write evidence describes what the CALLEE does through the
/// pointee; a pointer the callee returns and the caller then writes through
/// is a different question, and the guard that asks it (addendum 259) runs
/// only at `*const` targets. Opening this cell is the seat's call.
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

/// The tier control. Retention still decides admission before any carrier is
/// chosen — but **R481-2 (USER ruling, 2026-09-21) waives KNOWN retention**,
/// so what this control now pins is that the bridge happens *through the
/// waiver*: the site is admitted and it carries the per-site tier-2 receipt
/// naming this subject and this callee. A bridge here WITHOUT that receipt is
/// the failure the control exists to catch.
///
/// **The NAME disagrees with the assertion, deliberately.** It is kept because
/// other lanes and the reports cite `k19_retaining_callee_does_not_bridge` by
/// name; a reader who notices the disagreement should repair the name (and the
/// citations with it), never the assertion — the assertion is the ruling.
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
    assert_eq!(
        got.get("p").map(String::as_str),
        Some("<emitted>"),
        "a retained pointer bridges under the tier-2 waiver: {got:#?}"
    );
    let receipt = super::retention_waiver_tests::waived_receipt(&input, "target")
        .unwrap_or_else(|| panic!("the admitted site carries no waiver receipt: {got:#?}"));
    assert!(
        receipt.contains("retention-waiver(tier-2, kind=known, subject=target::p, callee="),
        "the receipt names the subject and the callee: {receipt}"
    );
}
