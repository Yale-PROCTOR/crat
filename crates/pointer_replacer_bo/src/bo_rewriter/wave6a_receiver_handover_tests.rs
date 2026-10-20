//! wave-6a relay 140 (R776-5): a certified receiver handed to a local
//! callee's RAW formal at its last use is `callee(.., Box::into_raw(x), ..)`.
//!
//! The corpus shape is quadtree's: `test_bounds` hands its bounds to
//! `quadtree_bounds_free`, whose Box-parameter chain is held (its other caller
//! passes a model-raw field), and `quadtree_insert` hands its point to
//! `insert_`, which stores it into a node. Both are C's own calls: the owner
//! gives the pointer to a raw consumer and does not touch it again.

use super::wave6a_allocation_tests::{compact, emitted};
use crate::analyses::borrow_ownership::SlotKind;

const QUADTREE: &str = include_str!("testdata/w6a-r776-quadtree.rs");

/// The emitted tree, for the Miri drivers (`CRAT_W6A_EMIT_DIR`).
fn record(name: &str, source: &str) {
    if let Ok(dir) = std::env::var("CRAT_W6A_EMIT_DIR") {
        std::fs::write(format!("{dir}/{name}-emitted.rs"), source).unwrap();
    }
}

fn handovers(receipts: &str) -> Vec<&str> {
    receipts
        .lines()
        .filter(|l| l.contains("return-certificate-receiver-handover"))
        .collect()
}

/// The corpus file, whole: the four CROWN units deliver.
#[test]
fn w6a_r776_quadtree_hands_its_receivers_over() {
    let _frame = super::test_model_override::frame_lock();
    let out = emitted("r776-quadtree", QUADTREE);
    record("r776-quadtree", &out.source);
    let text = compact(&out.source);
    let receipts = &out.artifacts.return_certificate_receipts;
    assert_eq!(out.reverted, 0, "{}", out.source);
    for callee in [
        "src::src::bounds::quadtree_bounds_new",
        "src::src::point::quadtree_point_new",
    ] {
        assert!(
            receipts.contains(&format!("return-certificate callee={callee} ")),
            "{callee} certified:\n{receipts}"
        );
    }
    assert!(
        text.contains("quadtree_bounds_free(Box::into_raw(bounds));"),
        "test_bounds hands over: {}",
        out.source
    );
    assert!(
        text.contains("quadtree_point_free(Box::into_raw(point));"),
        "test_points hands over: {}",
        out.source
    );
    assert!(
        text.contains("Box::into_raw(point),key)"),
        "quadtree_insert hands over to insert_: {}",
        out.source
    );
    // Condition 5: bounds_new's own fill stores point_new's Box results.
    assert_eq!(
        text.matches("Box::into_raw(quadtree_point_new(").count(),
        2,
        "the fill's two stores: {}",
        out.source
    );
    let rows = handovers(receipts);
    assert_eq!(rows.len(), 3, "{receipts}");
    for (callee, index) in [
        ("src::src::bounds::quadtree_bounds_free", 0),
        ("src::src::point::quadtree_point_free", 0),
        ("src::src::quadtree::insert_", 2),
    ] {
        assert!(
            rows.iter()
                .any(|r| r.contains(&format!("callee={callee} index={index}"))),
            "{callee}#{index}: {receipts}"
        );
    }
}

const PRELUDE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
    fn stash(p: *mut P);
    fn sscanf(s: *const i8, fmt: *const i8, ...) -> i32;
}
// w6a-r776-frame
#[derive(Copy, Clone)]
#[repr(C)]
pub struct P {
    pub x: f64,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct H {
    pub p: *mut P,
}
unsafe extern "C" fn p_new(mut x: f64) -> *mut P {
    let mut p = 0 as *mut P;
    p = malloc(::std::mem::size_of::<P>()) as *mut P;
    if p.is_null() {
        return 0 as *mut P;
    }
    (*p).x = x;
    return p;
}
// `insert_`'s shape: stored on one path, handed on by recursion on another —
// a raw formal no Box-parameter chain plans.
unsafe extern "C" fn keep(mut h: *mut H, mut p: *mut P, mut depth: i32) -> i32 {
    if depth > 0 as i32 {
        return keep(h, p, depth - 1 as i32);
    }
    (*h).p = p;
    return 1 as i32;
}
unsafe extern "C" fn p_free(mut p: *mut P) {
    free(p as *mut core::ffi::c_void);
}
pub unsafe extern "C" fn h_free(mut h: *mut H) {
    p_free((*h).p);
    free(h as *mut core::ffi::c_void);
}
"#;

/// The model of record for the reductions: every pointer raw, as quadtree's.
fn run(name: &str, body: &str) -> super::wave6a_allocation_tests::Emitted {
    let _frame = super::test_model_override::frame_lock();
    let src = format!("{PRELUDE}{body}");
    let locals = [
        "p_new::p",
        "keep::h",
        "keep::p",
        "p_free::p",
        "h_free::h",
        "go::h",
        "go::p",
        "go::q",
        "go::b",
        "keep_c::h",
        "keep_c::b",
        "p_take::p",
        "keep_two::h",
        "keep_two::a",
        "keep_two::b",
    ]
    .into_iter()
    .map(|l| (l.to_owned(), SlotKind::Raw))
    .collect();
    super::test_model_override::set(
        "w6a-r776-frame",
        vec![("H".to_owned(), 0, SlotKind::Raw)],
        locals,
    );
    let out = emitted(name, &src);
    super::test_model_override::clear();
    out
}

/// A raw formal that keeps the pointer (`insert_`'s shape), and a consuming
/// formal whose chain is held (`quadtree_bounds_free`'s): both hand over.
#[test]
fn w6a_r776_a_raw_formal_at_the_last_use_takes_the_owner() {
    let out = run(
        "r776-positive",
        r#"
pub unsafe extern "C" fn go(mut h: *mut H) -> f64 {
    let mut p = p_new(1.0f64);
    let mut v = (*p).x;
    keep(h, p, 0 as i32);
    let mut q = p_new(2.0f64);
    (*q).x = 3.0f64;
    p_free(q);
    return v;
}
"#,
    );
    record("r776-positive", &out.source);
    let text = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        text.contains("keep(h,Box::into_raw(p),0asi32);"),
        "{}",
        out.source
    );
    assert!(text.contains("p_free(Box::into_raw(q));"), "{}", out.source);
    assert_eq!(
        handovers(&out.artifacts.return_certificate_receipts).len(),
        2,
        "{}",
        out.artifacts.return_certificate_receipts
    );
}

fn held(name: &str, body: &str, cause: &str) {
    let out = run(name, body);
    let receipts = &out.artifacts.return_certificate_receipts;
    assert!(handovers(receipts).is_empty(), "{receipts}\n{}", out.source);
    assert!(
        !receipts.contains("return-certificate callee=p_new "),
        "p_new must not certify: {receipts}"
    );
    assert!(receipts.contains(cause), "{cause}: {receipts}");
}

/// Condition 1: the receiver read after the hand-on stays held.
#[test]
fn w6a_r776_a_receiver_used_after_the_call_is_held() {
    held(
        "r776-used-after",
        r#"
pub unsafe extern "C" fn go(mut h: *mut H) -> f64 {
    let mut p = p_new(1.0f64);
    keep(h, p, 0 as i32);
    return (*p).x;
}
"#,
        "call-argument-not-a-lend:keep(h, p, 0 as i32)",
    );
}

/// Condition 1, on the loop's next pass: the call is the binding's last use
/// in the text, and the loop runs it again.
#[test]
fn w6a_r776_a_hand_on_in_a_loop_the_receiver_outlives_is_held() {
    held(
        "r776-loop",
        r#"
pub unsafe extern "C" fn go(mut h: *mut H, mut n: i32) {
    let mut p = p_new(1.0f64);
    let mut i = 0 as i32;
    while i < n {
        keep(h, p, 0 as i32);
        i += 1;
    }
}
"#,
        "call-argument-not-a-lend:keep(h, p, 0 as i32)",
    );
}

/// Condition 4: an optional receiver (its callee returns null on a live
/// path) is not handed over.
#[test]
fn w6a_r776_an_optional_receiver_is_held() {
    held(
        "r776-optional",
        r#"
unsafe extern "C" fn p_maybe(mut x: f64) -> *mut P {
    if x < 0.0f64 {
        return 0 as *mut P;
    }
    return p_new(x);
}
pub unsafe extern "C" fn go(mut h: *mut H) {
    let mut p = p_maybe(1.0f64);
    keep(h, p, 0 as i32);
}
"#,
        "keep(h, p, 0 as i32)",
    );
}

/// The model's raw formal at a FOREIGN callee is the contract table's, not
/// this rule's.
#[test]
fn w6a_r776_a_foreign_callee_is_held() {
    held(
        "r776-foreign",
        r#"
pub unsafe extern "C" fn go() {
    let mut p = p_new(1.0f64);
    stash(p);
}
"#,
        "call-argument-not-a-lend:stash(p)",
    );
}

/// Condition 2: a transfer whose Box-parameter chain confirms stays the
/// chain's move — the formal is a box, not a raw consumer.
#[test]
fn w6a_r776_a_confirmed_transfer_stays_a_move() {
    let out = run(
        "r776-confirmed",
        r#"
unsafe extern "C" fn p_take(mut p: *mut P) {
    free(p as *mut core::ffi::c_void);
}
pub unsafe extern "C" fn go() {
    let mut q = p_new(2.0f64);
    (*q).x = 3.0f64;
    p_take(q);
}
"#,
    );
    let text = compact(&out.source);
    let receipts = &out.artifacts.return_certificate_receipts;
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(handovers(receipts).is_empty(), "{receipts}");
    assert!(text.contains("p_take(q);"), "{}", out.source);
    assert!(text.contains("fnp_take(mutp:Box<"), "{}", out.source);
}

/// A slice owner's raw pointer is fat; its hand-over is not this rule's.
#[test]
fn w6a_r776_a_slice_owner_is_held() {
    let out = run(
        "r776-slice",
        r#"
unsafe extern "C" fn buf_new() -> *mut i8 {
    let mut b = malloc((16 as usize) * ::std::mem::size_of::<i8>()) as *mut i8;
    if b.is_null() {
        return 0 as *mut i8;
    }
    sscanf(b"http://x\0" as *const u8 as *const i8, b"%[^://]\0" as *const u8 as *const i8, b);
    return b;
}
unsafe extern "C" fn keep_c(mut h: *mut *mut i8, mut b: *mut i8, mut depth: i32) -> i32 {
    if depth > 0 as i32 {
        return keep_c(h, b, depth - 1 as i32);
    }
    *h = b;
    return 1 as i32;
}
pub unsafe extern "C" fn go(mut h: *mut *mut i8) {
    let mut b = buf_new();
    keep_c(h, b, 0 as i32);
}
"#,
    );
    let receipts = &out.artifacts.return_certificate_receipts;
    assert!(handovers(receipts).is_empty(), "{receipts}\n{}", out.source);
    assert!(
        receipts.contains("call-argument-not-a-lend:keep_c(h, b, 0 as i32)"),
        "{receipts}"
    );
}

/// Codex (R776-5 review, high): two transfers into the same formal on two
/// paths — only the second is a last use in the text — are two occurrences;
/// one ready hand-over does not cover both, so the certificate withdraws.
#[test]
fn w6a_r776_two_transfers_into_one_formal_need_two_hand_overs() {
    held(
        "r776-two-transfers",
        r#"
pub unsafe extern "C" fn go(mut n: i32) {
    let mut q = p_new(2.0f64);
    if n > 0 as i32 {
        p_free(q);
    } else {
        p_free(q);
    }
}
"#,
        "return-certificate-transfer-unconfirmed",
    );
}

/// Codex (R776-5 review, medium): the receiver passed twice in one call is
/// used after its first argument; neither occurrence is a last use.
#[test]
fn w6a_r776_a_receiver_passed_twice_in_one_call_is_held() {
    held(
        "r776-twice",
        r#"
unsafe extern "C" fn keep_two(mut h: *mut H, mut a: *mut P, mut b: *mut P, mut depth: i32) -> i32 {
    if depth > 0 as i32 {
        return keep_two(h, a, b, depth - 1 as i32);
    }
    (*h).p = a;
    return 1 as i32;
}
pub unsafe extern "C" fn go(mut h: *mut H) {
    let mut p = p_new(1.0f64);
    keep_two(h, p, p, 0 as i32);
}
"#,
        "call-argument-not-a-lend:keep_two(h, p, p, 0 as i32)",
    );
}
