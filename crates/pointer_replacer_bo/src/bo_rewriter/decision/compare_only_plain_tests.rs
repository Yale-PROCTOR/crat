//! **R471-4 — the plain slice twin takes the compare-only fact.**
//!
//! R464-3 (+ R470-6) admits a forward-only walk whose limit is only compared.
//! It was wired into the `Opt { slice: true }` arm alone; the plain twin kept
//! its refusal because `slicecursor_fragment_fast_core_loop` pins that refusal
//! as the cursor family's hand-off point (report 028 §4). Report 031 measured
//! the trade: **14 brotli rows + binn's `IsValidBinnHeader::pbuf`** are refused
//! ONLY there, all 18 rows of that shape read `emission=unchanged` in the
//! cursor family's own records, and of the 81 rows the cursor family DOES
//! deliver, the fact admits exactly one — whose sign is `nonneg`, so this gate
//! never reads it. The hand-off is to nobody, so the twin takes the fact.
use super::super::emit_tests::decisions_of;

fn reason_for(body: &str) -> String {
    let src = format!(
        "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub unsafe fn f(mut p: *mut i32, n: usize, k: isize) -> *mut i32 {{\n{body}\n}}\n"
    );
    reason_in(&src, "p")
}

/// The reason a named parameter carries in a whole fixture.
fn reason_in(src: &str, name: &str) -> String {
    decisions_of(src)
        .into_iter()
        .find(|(subject, is_param, _)| subject == name && *is_param)
        .unwrap_or_else(|| panic!("no subject {name}"))
        .2
}

/// binn's `IsValidBinnHeader`, reduced to the two facts that decide it: the
/// limit is computed by a NON-literal offset and only compared or null-tested,
/// and the cursor advances by a literal in c2rust's spelling
/// (`4 as libc::c_int as isize`). The census refuses `pbuf#1` here with
/// `slice-neg-or-unknown-offset` and nothing else.
const HEADER_WALK: &str = r####"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn IsValidBinnHeader(mut pbuf: *mut u8, mut psize: *mut i32) -> i32 {
    let mut p = pbuf;
    let mut plimit = 0 as *mut u8;
    let mut total = 0;
    if pbuf.is_null() { return 0; }
    if !psize.is_null() && *psize > 0 { plimit = p.offset((*psize as isize) + (-(1 as isize))); }
    if !plimit.is_null() && p > plimit { return 0; }
    total += *p as i32;
    p = p.offset(4 as core::ffi::c_int as isize);
    total += *p as i32;
    return total;
}
"####;

/// **The shape** — binn's header walk, reduced: the only non-literal offset
/// produces a limit that is compared and never read, and the cursor advances by
/// a literal written in c2rust's spelling. The sign export cannot bound `k`, so
/// before R471-4 the plain twin refused a walk that moves forward only.
#[test]
fn w5c_plain_twin_admits_a_compare_only_limit_walk() {
    assert_eq!(
        reason_in(HEADER_WALK, "pbuf"),
        "<emitted>",
        "a forward-only walk whose limit is only compared must reach the plain \
         slice form, as it already reaches the optional one"
    );
}

/// **Control (i)** — report 027's 24 rows: the walk advances by a VARIABLE and
/// the cursor is then read. The refusal stands; this is what the sign bit is
/// for, and it is the half that keeps the admission a gate rather than a veto.
#[test]
fn w5c_plain_twin_refuses_a_variable_advancing_walk() {
    assert_eq!(
        reason_for("    let _v = *p.offset(k);\n    p"),
        "slice-neg-or-unknown-offset",
        "a variable advancing step must keep the refusal"
    );
}

/// **Control (ii)** — the cursor family's own shape: a BACKWARD literal step
/// that is read through. The fact refuses it, so the plain twin does not take a
/// position the cursor family is there for. Corpus-side, this is the measured
/// 80 of 81 `planned-cursor` rows the fact refuses (report 032 §1).
#[test]
fn w5c_plain_twin_leaves_a_backward_walk_to_the_cursor_family() {
    let reason = reason_for("    let _v = *p.offset(-1 as isize);\n    p");
    assert_ne!(
        reason, "<emitted>",
        "a backward walk must not become a plain slice"
    );
}

/// The pair that isolates the arm: the sign verdict comes from a CALLEE's
/// backward walk, so `may_be_negative` holds for `p` in both, and the two
/// bodies differ only in how `f` itself advances — by a literal in c2rust's
/// spelling, or by a variable. Both are refused `slice-neg-or-unknown-offset`
/// before R471-4.
const CALLEE_TOP: &str = r####"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn back(mut q: *mut i32, k: isize) -> *mut i32 { q.offset(-(k)) }
pub unsafe fn f(mut p: *mut i32, n: usize, k: isize) -> *mut i32 {
    let limit = back(p, k);
    if limit.is_null() { return p; }
    let _v = *p.offset(ADVANCE);
    p
}
"####;

/// **The shape.** Every offset this body performs on the subject takes a
/// non-negative literal; the value whose sign cannot be bounded is produced
/// elsewhere and only null-tested here. The optional twin already admits this;
/// R471-4 lets the plain twin admit it too.
#[test]
fn w5c_plain_twin_admits_a_literal_walk_under_an_unbounded_sign() {
    let reason = reason_in(
        &CALLEE_TOP.replace("ADVANCE", "4 as core::ffi::c_int as isize"),
        "p",
    );
    assert_ne!(
        reason, "slice-neg-or-unknown-offset",
        "a forward-only walk must pass the plain twin's sign refusal, as it \
         already passes the optional twin's"
    );
    // Where it lands instead, stated rather than left open: this fixture
    // returns the subject bare, so the next owed capability is the return
    // hand-off — another family's gate, not this arm's business. The corpus
    // rows this arm is for (report 031's 15) carry their own next gates, and
    // the census measures those.
    assert_eq!(reason, "slice-use-unsupported");
}

/// **Control (iii)** — the same fixture, advancing by a VARIABLE. One token
/// apart from the witness, and it must stay refused: this is report 027's
/// shape, the 24 rows the fact is not for.
#[test]
fn w5c_plain_twin_refuses_the_same_walk_advanced_by_a_variable() {
    assert_eq!(
        reason_in(&CALLEE_TOP.replace("ADVANCE", "k"), "p"),
        "slice-neg-or-unknown-offset",
        "a variable advancing step must keep the refusal"
    );
}
