//! **R924-1 (USER; wave-5d 148) — the pending pair holds a local proof covers.**
//! A source handed to a raw formal beside a written raw sibling stays held
//! (R829-1 / R855-1) unless the pair is shown disjoint. Where the audit and the
//! certificates ran no proof, two local ones now answer: at a FOREIGN callee the
//! certificates' own root classes for the two arguments (a fresh allocation or a
//! stack object beside storage that existed at entry), and at a local callee
//! whose caller is an exported entry nothing calls, the scope's separate-object
//! certificate for two of its own formals. A parameter beside a parameter, and
//! an entry the program calls, stay held.

use super::decision::{Decision, DegradeReason};

/// Each subject's label, whether the settled table holds it beside a pair not
/// shown disjoint, and whether it is raw at all (the attested census world).
fn held(input: &str) -> Vec<(String, bool, bool)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decisions");
        table
            .entries
            .iter()
            .map(|(subject, decision)| {
                println!("DECISION {} {decision:?}", subject.label);
                (
                    subject.label.clone(),
                    matches!(decision, Decision::Degraded(d)
                        if matches!(d.reason, DegradeReason::PairNotShownDisjoint { .. })),
                    matches!(decision, Decision::Degraded(_)),
                )
            })
            .collect()
    })
    .expect("fixture compiles")
}

fn row<'a>(rows: &'a [(String, bool, bool)], label: &str) -> &'a (String, bool, bool) {
    rows.iter()
        .find(|(l, ..)| l == label)
        .unwrap_or_else(|| panic!("no subject {label}: {rows:?}"))
}

fn is_held(rows: &[(String, bool, bool)], label: &str) -> bool {
    row(rows, label).1
}

fn is_raw(rows: &[(String, bool, bool)], label: &str) -> bool {
    row(rows, label).2
}

const FRESH: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn malloc(n: usize) -> *mut i8;
    fn strncpy(dst: *mut i8, src: *const i8, n: usize) -> *mut i8;
}
pub unsafe fn caller(p: *const i8) -> i8 {
    let mut dst = malloc(2);
    strncpy(dst, p, 2);
    *p.offset(1)
}
pub unsafe fn control(p: *const i8, q: *mut i8) -> i8 {
    strncpy(q, p, 2);
    *p.offset(1)
}
"#;

/// (1) A fresh allocation beside a parameter at a libc call: the block did
/// not exist when `p` was passed in, so the two are disjoint (distinct roots).
#[test]
fn r924_1_a_fresh_allocation_beside_a_parameter_at_a_libc_call_is_not_held() {
    let rows = held(FRESH);
    assert!(!is_held(&rows, "caller::p"), "{rows:?}");
}

/// Control: a parameter beside a parameter stays held.
#[test]
fn r924_1_control_two_parameters_at_a_libc_call_stay_held() {
    let rows = held(FRESH);
    assert!(is_held(&rows, "control::p"), "{rows:?}");
}

const STACK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" { fn strncpy(dst: *mut i8, src: *const i8, n: usize) -> *mut i8; }
pub unsafe fn caller(p: *const i8) -> i8 {
    let mut dst = [0i8; 2];
    strncpy(dst.as_mut_ptr(), p, 2);
    *p.offset(1)
}
"#;

/// (1) A stack array beside a parameter at a libc call (stack object versus
/// storage that existed at entry).
#[test]
fn r924_1_a_stack_array_beside_a_parameter_at_a_libc_call_is_not_held() {
    let rows = held(STACK);
    assert!(!is_held(&rows, "caller::p"), "{rows:?}");
}

const ENTRY: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
unsafe fn write2(a: *mut i32, b: *const i32) -> i32 {
    *a = *b;
    (b as usize) as i32
}
#[no_mangle]
pub unsafe extern "C" fn entry(x: *mut i32, y: *const i32) -> i32 {
    write2(x, y);
    *y
}
pub unsafe fn other(z: *mut i32) -> i32 {
    write2(z, z)
}
"#;

/// (2) Two of its own formals handed on by an exported entry nothing in the
/// program calls: separate outside objects (R816 / R819).
#[test]
fn r924_1_two_formals_of_an_entry_nothing_calls_are_not_held() {
    let rows = held(ENTRY);
    assert!(!is_held(&rows, "entry::y"), "{rows:?}");
}

/// Control: the same entry called inside the program with one pointer twice
/// is not certified; `y` stays raw (the pair pass's raw view takes it first).
#[test]
fn r924_1_control_an_entry_the_program_calls_stays_raw() {
    let input = format!("{ENTRY}pub unsafe fn calls_entry(q: *mut i32) -> i32 {{ entry(q, q) }}\n");
    let rows = held(&input);
    assert!(is_raw(&rows, "entry::y"), "{rows:?}");
}
