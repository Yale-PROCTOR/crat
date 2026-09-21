//! **R485-4(c) (relay 052): a nullable pointer that walks ITSELF.**
//!
//! Eight corpus rows are nullable (`is_null`-tested or null-initialised) and
//! self-advancing (`p = p.offset(1)`). Nullability gives them to the Option
//! family, which degrades them `opt-use-unsupported` because an `Option<&T>`
//! has no advance; the cursor family never sees them, because its two
//! admissions want a NEGATIVE offset (`selected`) or an offset chain rooted at
//! ANOTHER cursor (`derived_from_cursor_root`) — and these subjects are their
//! own root.
//!
//! The form they want already exists: `CursorPlan.optional` renders
//! `Option<SliceCursor<'_, T>>` with `is_none()` for the null test,
//! `as_ref().expect(..)[0isize]` for the deref and
//! `as_mut().expect(..).seek(..)` for the advance (report 040's spike). Only
//! the admission was missing.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

/// binn `is_integer` / `is_float`, reduced: a nullable parameter that tests
/// `is_null`, dereferences, and advances itself.
const SELF_ADVANCING: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn is_integer(mut p: *mut i8) -> i32 {
    let mut retval: i32 = 0;
    if p.is_null() { return 0; }
    if *p as i32 == '-' as i32 { p = p.offset(1); }
    if *p as i32 == 0 { return 0; }
    retval = 1;
    while *p != 0 {
        if (*p as i32) < '0' as i32 || *p as i32 > '9' as i32 { retval = 0; }
        p = p.offset(1);
    }
    return retval;
}
"#;

/// **Control A** — the same nullability and the same `opt-use-unsupported`
/// degradation, but the subject is assigned from another pointer and never
/// advances itself. It stays out.
const NOT_ADVANCING: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn head(mut p: *mut i8, mut q: *mut i8) -> i32 {
    if p.is_null() { return 0; }
    if *p as i32 == '-' as i32 { p = q; }
    if *p as i32 == 0 { return 0; }
    *p = 1 as i8;
    return *p as i32;
}
"#;

/// **Control B** — the same, with a real offset ON the subject so that
/// `plan`'s `Offsets` gate is satisfied. Measured outcome: the subject is
/// `kind-raw`, not `opt-use-unsupported`, so this arm never sees it either.
/// Recorded because it is why the clause's own fault could not be isolated
/// end to end (see the report): every fixture that satisfies the `Offsets`
/// gate AND assigns the subject from another pointer left the Option family.
const NOT_ADVANCING_WITH_OFFSET: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn head(mut p: *mut i8, mut q: *mut i8) -> i32 {
    if p.is_null() { return 0; }
    if *p as i32 == '-' as i32 { p = q; }
    if *p.offset(1 as isize) as i32 == 0 { return 0; }
    *p = 1 as i8;
    return *p as i32;
}
"#;

fn decision_of(input: &str, function: &str, binding: &str) -> Decision {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        table
            .entries
            .iter()
            .find(|(subject, _)| {
                subject.param_name.as_deref() == Some(binding)
                    && tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
            })
            .map(|(_, decision)| decision.clone())
            .expect("the reduced subject")
    })
    .expect("fixture compiler context")
}

/// **W6O-OC-1 — the delivering witness.** The self-advancing nullable subject
/// takes the optional cursor, and the emitted program type-checks.
#[test]
fn wave6o_a_nullable_self_advancing_pointer_takes_the_optional_cursor() {
    assert!(verify::type_checks_str(SELF_ADVANCING));
    let decision = decision_of(SELF_ADVANCING, "is_integer", "p");
    let Decision::Cursor { plan, .. } = &decision else {
        panic!("the self-advancing nullable subject must take the cursor: {decision:?}");
    };
    assert!(plan.optional, "and it must carry the Option: {plan:?}");
    let output = ast_emitted_source_of(SELF_ADVANCING).expect("native emission");
    assert!(
        output.contains("p: Option<&[i8]>") || output.contains("p: Option<&mut [i8]>"),
        "the declaration is the optional cursor's source form: {output}"
    );
    assert!(
        output.contains("SliceCursor::new"),
        "the construction maps into the cursor: {output}"
    );
    assert!(output.contains("p.is_none()"), "the null test: {output}");
    assert!(output.contains(".seek("), "the advance: {output}");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// **The control.** Nullable and `opt-use-unsupported`, but the subject never
/// advances itself — it is assigned from another pointer. This arm must leave
/// it alone.
#[test]
fn wave6o_a_nullable_subject_that_never_advances_is_not_admitted() {
    assert!(verify::type_checks_str(NOT_ADVANCING));
    let decision = decision_of(NOT_ADVANCING, "head", "p");
    assert!(
        !matches!(decision, Decision::Cursor { .. }),
        "a subject with no self-advance is not this arm's: {decision:?}"
    );
    let with_offset = decision_of(NOT_ADVANCING_WITH_OFFSET, "head", "p");
    assert!(
        !matches!(with_offset, Decision::Cursor { .. }),
        "nor is its offset-carrying twin: {with_offset:?}"
    );
}

// ---------------------------------------------------------------------------
// **R497-3(c) — the RE-SEEDED walker** (relay 063; slicecursor 052 §3's three
// conditions taken as the construction's design).
//
// Five corpus rows advance themselves AND are re-seeded once from another
// value. `self_advancing_root` wants `other == 0`, `derived_from_cursor_root`
// wants the other value to be a cursor of this family: neither covers them.
// The arm admits exactly one non-self assignment and CONSTRUCTS a fresh cursor
// there, with the extent the re-seed value can offer — §77's fabricated extent
// with the plan's `fallback` receipt where the value has no length of its own.
// ---------------------------------------------------------------------------

/// json.h `json_hexadecimal_value`, reduced: `p` is null-initialised, re-seeded
/// once from the delivered parameter `c`, and advances itself to the `size`
/// bound.
const RE_SEEDED: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn json_hexadecimal_value(mut c: *const i8, mut size: usize, mut result: *mut u64) -> i32 {
    let mut p = 0 as *const i8;
    let mut digit: i32 = 0;
    *result = 0 as u64;
    p = c;
    while (p.offset_from(c) as usize) < size {
        *result <<= 4 as i32;
        digit = *p as i32 - 48 as i32;
        if digit < 0 as i32 || digit > 15 as i32 { return 0 as i32; }
        *result |= digit as u64;
        p = p.offset(1 as isize);
    }
    return 1 as i32;
}
"#;

/// **W6O-RS-1 — the delivering witness.** The re-seeded walker takes the
/// optional cursor; the construction at the re-seed bridges the delivered
/// reference and carries the §77 extent; the emitted program type-checks.
#[test]
fn wave6o_a_re_seeded_walker_constructs_at_the_re_seed() {
    assert!(verify::type_checks_str(RE_SEEDED));
    let decision = decision_of(RE_SEEDED, "json_hexadecimal_value", "p");
    let Decision::Cursor { plan, .. } = &decision else {
        panic!("the re-seeded walker must take the cursor: {decision:?}");
    };
    assert!(plan.optional, "it is null-initialised: {plan:?}");
    assert!(
        plan.fallback,
        "the fabricated extent must be receipted (§77): {plan:?}"
    );
    let output = ast_emitted_source_of(RE_SEEDED).expect("native emission");
    assert!(
        output.contains("from_raw_parts(core::ptr::from_ref(c)"),
        "the re-seed bridges the delivered reference: {output}"
    );
    assert!(
        output.contains("crate::FALLBACK_SLICE_EXTENT"),
        "with the named fallback extent: {output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}

/// **Control A — TWO re-seeds stay out.** A second construction would reset the
/// position again, and the walker's own positions across two fresh windows are
/// incomparable with no single base to name.
#[test]
fn wave6o_a_twice_re_seeded_walker_is_not_admitted() {
    const TWICE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn twice(mut c: *const i8, mut d: *const i8, mut size: usize, mut result: *mut u64) -> i32 {
    let mut p = 0 as *const i8;
    *result = 0 as u64;
    p = c;
    while (p.offset_from(c) as usize) < size {
        *result |= *p as u64;
        p = p.offset(1 as isize);
    }
    p = d;
    *result |= *p as u64;
    return 1 as i32;
}
"#;
    assert!(verify::type_checks_str(TWICE));
    let decision = decision_of(TWICE, "twice", "p");
    assert!(
        !matches!(decision, Decision::Cursor { .. }),
        "two re-seeds are not this arm's: {decision:?}"
    );
}

/// **Control B — a walker that may move BACKWARD after the re-seed stays out**
/// (slicecursor 052 §3 (ii)). The window is fabricated forward from the re-seed
/// pointer, so a negative move would seek below position 0 and panic where the
/// input program was correct.
#[test]
fn wave6o_a_backward_re_seeded_walker_is_not_admitted() {
    const BACKWARD: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn backward(mut c: *const i8, mut size: usize, mut result: *mut u64) -> i32 {
    let mut p = 0 as *const i8;
    *result = 0 as u64;
    p = c;
    while (p.offset_from(c) as usize) < size { p = p.offset(1 as isize); }
    while *p as i32 != 47 as i32 {
        *result |= *p as u64;
        p = p.offset(-(1 as i32) as isize);
    }
    return 1 as i32;
}
"#;
    assert!(verify::type_checks_str(BACKWARD));
    let decision = decision_of(BACKWARD, "backward", "p");
    assert!(
        !matches!(&decision, Decision::Cursor { plan, .. } if plan.fallback),
        "a backward walker takes no fabricated re-seed window: {decision:?}"
    );
}

/// **Control C — the arm bridges a SHARED reference and never an exclusive
/// one.** Taking a raw `*mut` out of a live `&mut` while the cursor walks it is
/// the retained-alias channel; this arm has no evidence about it, so the
/// subject stays held rather than emitting the bridge.
#[test]
fn wave6o_a_re_seed_from_an_exclusive_reference_is_held() {
    const EXCLUSIVE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn writer(mut c: *mut i8, mut size: usize) -> i32 {
    let mut p = 0 as *mut i8;
    let mut n: i32 = 0;
    *c = 1 as i8;
    p = c;
    while (p.offset_from(c) as usize) < size {
        *p = 2 as i8;
        n += 1 as i32;
        p = p.offset(1 as isize);
    }
    return n;
}
"#;
    assert!(verify::type_checks_str(EXCLUSIVE));
    let decision = decision_of(EXCLUSIVE, "writer", "p");
    assert!(
        !matches!(decision, Decision::Cursor { .. }),
        "an exclusive re-seed source is not bridged here: {decision:?}"
    );
}
