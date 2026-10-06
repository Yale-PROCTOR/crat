//! R824-2 (§29, R819-1): with the Option stage withdrawn, a subject whose OWN
//! evidence is nullable (a null literal at its construction, a null
//! assignment, a null test of it, a caller's null literal at its position) is
//! never delivered in a non-optional safe form. One witness per promotion path
//! the independent review named; the Option stage is withdrawn by the test
//! hook, as an exclusion re-derivation would.

use super::FORCED_OPTION_WITHDRAWALS;

const ALLOW: &str =
    "#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case)]\n";

/// The hook is process-global: one decision at a time, so a withdrawal one
/// test forces is never seen by another running beside it (the control, the
/// same labels with the stage enabled).
static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// The form decided for `label`, with its Option stage withdrawn or not.
fn form(input: &str, label: &str, withdrawn: bool) -> String {
    let _serial = SERIAL
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if withdrawn {
        FORCED_OPTION_WITHDRAWALS
            .lock()
            .expect("hook")
            .push(label.to_owned());
    }
    let input = format!("{ALLOW}{input}");
    let out = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let table = crate::bo_rewriter::decide_table(tcx).expect("native decisions");
        table
            .entries
            .iter()
            .find(|(subject, _)| subject.label == label)
            .map(|(_, decision)| super::seam::form_of(decision).key().to_owned())
            .unwrap_or_else(|| panic!("no subject {label}"))
    })
    .expect("input type-checks");
    if withdrawn {
        FORCED_OPTION_WITHDRAWALS
            .lock()
            .expect("hook")
            .retain(|held| held != label);
    }
    out
}

/// Path 1: the all-arithmetic array. A caller hands a null literal at the
/// formal's position.
const SUM: &str = r#"
pub unsafe fn r824_sum(mut p: *const i32, mut n: i32) -> i32 {
    let mut s = 0;
    let mut i = 0;
    while i < n {
        s += *p.offset(i as isize);
        i += 1;
    }
    s
}
pub unsafe fn r824_sum_none() -> i32 { r824_sum(0 as *const i32, 0) }
pub unsafe fn r824_sum_some(mut a: *const i32) -> i32 { r824_sum(a, 4) }
"#;

#[test]
fn r824_2_the_all_arithmetic_array_with_own_null_evidence_falls_back_to_raw() {
    assert_eq!(form(SUM, "r824_sum::p", true), "raw");
}

/// Path 2: the contract-extent promotion (a NUL-terminated read).
const LEN: &str = r#"
extern "C" { fn strlen(s: *const i8) -> usize; }
pub unsafe fn r824_len(mut s: *const i8) -> usize { strlen(s) }
pub unsafe fn r824_len_none() -> usize { r824_len(0 as *const i8) }
pub unsafe fn r824_len_some(mut a: *const i8) -> usize { r824_len(a) }
"#;

#[test]
fn r824_2_the_contract_extent_promotion_with_own_null_evidence_falls_back_to_raw() {
    assert_eq!(form(LEN, "r824_len::s", true), "raw");
}

/// Path 3: a bare hand-on to an array formal whose callers all supply
/// buffers, the subject's own evidence a null assignment. The counted /
/// supplied promotion does not fire here (two attempts: a caller's null literal
/// refuses the supplied chain, and the assignment refuses it too); what the
/// withdrawn stage delivers instead is a plain `&mut`, which the gate refuses
/// the same way.
const WRAP: &str = r#"
pub unsafe fn r824_fill(mut p: *mut i32, mut n: usize) {
    let mut i = 0;
    while i < n {
        *p.offset(i as isize) = 0;
        i += 1;
    }
}
pub unsafe fn r824_wrap(mut q: *mut i32, mut n: usize) {
    if n == 0 {
        q = 0 as *mut i32;
    }
    r824_fill(q, n)
}
pub unsafe fn r824_wrap_a() { let mut a: [i32; 4] = [0; 4]; r824_wrap(a.as_mut_ptr(), 4) }
pub unsafe fn r824_wrap_b() { let mut b: [i32; 8] = [0; 8]; r824_wrap(b.as_mut_ptr(), 8) }
"#;

#[test]
fn r824_2_a_null_assigned_formal_handed_to_an_array_formal_falls_back_to_raw() {
    assert_eq!(form(WRAP, "r824_wrap::q", true), "raw");
}

/// Control: with the Option stage enabled, the same subjects keep a safe form.
#[test]
fn r824_2_control_with_the_option_stage_enabled_the_forms_stay_safe() {
    for (input, label) in [
        (SUM, "r824_sum::p"),
        (LEN, "r824_len::s"),
        (WRAP, "r824_wrap::q"),
    ] {
        assert_ne!(form(input, label, false), "raw", "{label}");
    }
}

// The exception (R517-10's null-initialized local, whose initializer is its
// only null evidence and which is never handed on) has no witness: the local
// shapes tried were decided raw for other reasons with the stage withdrawn
// (slice-use-unsupported; kind-raw), so a control there would pass vacuously.
// It stands on the code (`declaration_owns_null_init`).
