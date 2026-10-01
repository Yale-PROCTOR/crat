//! R739-1 (slicecursor relay 099) — a subject that is only ever MEASURED is
//! held raw: `held:address-observation-only`.
//!
//! brotli's `compress_fragment::EmitUncompressedMetaBlock(begin, end, ..)`
//! uses `end` once, in `end.offset_from(begin)`, and its callers hand it
//! `base`, `ip_end` and `input.offset(input_size)` — the last one past the end
//! of `input`. Decided `Ref`, `end` became `&u8`: E0599 at the difference, the
//! function reverted, and its interface partition took the five
//! `BrotliCompressFragmentFastImpl*` callers' `m` / `table` with it (L01¹²,
//! frame12: 11 rows). A bridge (`ptr::from_ref(end).offset_from(begin)`) would
//! compile and be UB at the third caller, where `&*input.offset(input_size)`
//! claims an element that does not exist (slicecursor report 091).

use super::{RewriteOutcome, decision::DegradeReason};

/// The reduction: the callee in shape (the byte copy written out, as `memcpy`'s
/// A5 proof sites need the frozen benchmark graph a fixture does not have),
/// and one caller passing the three real `end` arguments beside two parameters
/// it dereferences.
const REDUCTION: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_snake_case)]
unsafe fn EmitUncompressedMetaBlock(begin: *const u8, end: *const u8, storage: *mut u8) {
    let len = end.offset_from(begin) as usize;
    let mut i = 0usize;
    while i < len {
        *storage.offset(i as isize) = *begin.offset(i as isize);
        i += 1;
    }
}
pub unsafe fn FastImpl(
    m: *mut i32,
    input: *const u8,
    input_size: usize,
    table: *mut i32,
    storage: *mut u8,
) {
    *m += 1;
    *table = *m;
    let base = input.offset(1);
    let ip_end = input.offset(input_size as isize);
    EmitUncompressedMetaBlock(input, base, storage);
    EmitUncompressedMetaBlock(input, ip_end, storage);
    EmitUncompressedMetaBlock(input, input.offset(input_size as isize), storage);
}
"#;

fn emitted(src: &str) -> (String, Vec<super::decision::Degradation>) {
    match super::rewrite_m1(src) {
        RewriteOutcome::Emitted {
            source,
            degradations,
            ..
        } => (source, degradations),
        _ => panic!("the reduction must emit"),
    }
}

fn reason_of<'a>(
    degradations: &'a [super::decision::Degradation],
    subject: &str,
) -> Option<&'a DegradeReason> {
    degradations
        .iter()
        .find(|degradation| degradation.subject == subject)
        .map(|degradation| &degradation.reason)
}

/// **The witness.** `end` is held raw at the decision stage, the callee
/// compiles without a revert, and the caller's dereferenced parameters keep
/// their reference forms.
#[test]
fn slicecursor_a_measured_only_end_sentinel_is_held_raw() {
    let (source, degradations) = emitted(REDUCTION);
    assert_eq!(
        reason_of(&degradations, "EmitUncompressedMetaBlock::end"),
        Some(&DegradeReason::AddressObservationOnly),
        "{degradations:#?}\n{source}"
    );
    assert!(
        source.contains("end: *const u8"),
        "`end` keeps its raw form: {source}"
    );
    assert!(
        !degradations
            .iter()
            .any(|d| matches!(d.reason, DegradeReason::RevertedAfterVerifyFailure)),
        "nothing reverts: {degradations:#?}\n{source}"
    );
    for parameter in ["FastImpl::m", "FastImpl::table"] {
        assert_eq!(
            reason_of(&degradations, parameter),
            None,
            "{parameter} is delivered: {degradations:#?}\n{source}"
        );
    }
    assert!(
        !source.contains("&*input.offset("),
        "no caller claims an element at an end pointer: {source}"
    );
}

/// **The control.** One dereference beside the difference: `end` is not
/// only measured, so this arm does not hold it (what happens to it after is
/// the existing ladder's — main's census (β) sizes that class).
#[test]
fn slicecursor_a_dereferenced_end_is_not_held_as_measured_only() {
    let src = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
pub unsafe fn span_len(begin: *const u8, end: *const u8) -> isize {
    let first = *end;
    first as isize + end.offset_from(begin)
}
"#;
    let decisions = super::emit_tests::decisions_of(src);
    let end = decisions
        .iter()
        .find(|(name, is_param, _)| name == "end" && *is_param)
        .unwrap_or_else(|| panic!("no `end`: {decisions:?}"));
    assert_ne!(end.2, "held:address-observation-only", "{decisions:?}");
}

/// **The control on the other measuring ops.** A pointer that is only
/// compared and null-tested is held the same way; one that is also passed on
/// to a callee is not.
#[test]
fn slicecursor_a_compared_only_pointer_is_held_and_a_passed_one_is_not() {
    let src = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
unsafe fn sink(p: *const u8) -> u8 { *p }
pub unsafe fn compared(p: *const u8, limit: *const u8) -> bool {
    !limit.is_null() && p < limit
}
pub unsafe fn passed(p: *const u8, limit: *const u8) -> u8 {
    if p < limit { sink(limit) } else { 0 }
}
"#;
    let (source, degradations) = emitted(src);
    assert_eq!(
        reason_of(&degradations, "compared::limit"),
        Some(&DegradeReason::AddressObservationOnly),
        "{degradations:#?}\n{source}"
    );
    assert_ne!(
        reason_of(&degradations, "passed::limit"),
        Some(&DegradeReason::AddressObservationOnly),
        "{degradations:#?}\n{source}"
    );
}
