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
