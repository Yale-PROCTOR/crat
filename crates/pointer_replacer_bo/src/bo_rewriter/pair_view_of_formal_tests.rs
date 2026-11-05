//! wave-6p R482-4, rule (3): a callee whose every return is null or a view of
//! formal *k* makes a call of it a derivation of argument *k*.
//!
//! Report 019 found the rule needed for binn's `GetValue` chain and declined to
//! build it alone; report 021 priced it at 137 unproved pairs. It composes with
//! the derived-root fixpoint without a new branch: the call becomes an ordinary
//! `AssignKind::Derived`, and a SELF-derivation (`p = SearchForKey(p, ..)`, the
//! cursor idiom) is already dropped there.
//!
//! The summary itself is a fixpoint: `SearchForKey` is a view of its formal 0
//! only once `AdvanceDataPos` is known to be one.

use super::decision::pair_disjointness::{CertificateKind, PairDisjointnessIndex, Unproved};

fn verdict(
    src: &str,
    caller: &str,
    callee: &str,
    left: usize,
    right: usize,
) -> Result<CertificateKind, Unproved> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = PairDisjointnessIndex::derive(&program, &mut_facts, None);
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        out = Some(index.certify_recorded(function(caller), function(callee), left, right));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

/// binn's chain, cut down: `AdvanceDataPos` returns null or an offset of its
/// formal 0; `SearchForKey` returns null or `p`, which walks through
/// `AdvanceDataPos`; so the cursor in `search` still names the caller's own
/// buffer and is disjoint from that caller's stack scratch.
const VIEW_CHAIN: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn AdvanceDataPos(mut p: *mut u8, mut plimit: *mut u8) -> *mut u8 {
    if p > plimit { return 0 as *mut u8; }
    p = p.offset(1);
    return p;
}
pub unsafe fn SearchForKey(mut p: *mut u8, mut n: i32) -> *mut u8 {
    let mut plimit = p.offset(n as isize);
    let mut i: i32 = 0;
    while i < n {
        if *p == 7 { return p; }
        p = AdvanceDataPos(p, plimit);
        if p.is_null() { break; }
        i += 1;
    }
    return 0 as *mut u8;
}
pub unsafe fn GetValue(mut p: *mut u8, mut out: *mut i32) -> i32 {
    *out = *p as i32;
    1
}
pub unsafe fn search(mut buf: *mut u8, mut n: i32) -> i32 {
    let mut scratch: i32 = 0;
    let mut p = buf;
    p = SearchForKey(p, n);
    GetValue(p, &mut scratch)
}
"#;

#[test]
fn w6p_a_view_of_a_formal_carries_the_argument_s_root() {
    assert_eq!(
        verdict(VIEW_CHAIN, "search", "GetValue", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "the cursor still names `buf`, which is not the caller's scratch"
    );
}

/// Control (i): one return is a view of a DIFFERENT formal, so the callee is a
/// view of neither.
const TWO_FORMALS_RETURNED: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn pick(mut a: *mut u8, mut b: *mut u8, mut c: i32) -> *mut u8 {
    if c > 0 { return a.offset(1); }
    return b;
}
pub unsafe fn GetValue(mut p: *mut u8, mut out: *mut i32) -> i32 {
    *out = *p as i32;
    1
}
pub unsafe fn search(mut buf: *mut u8, mut other: *mut u8, mut n: i32) -> i32 {
    let mut scratch: i32 = 0;
    let mut p = pick(buf, other, n);
    GetValue(p, &mut scratch)
}
"#;

#[test]
fn w6p_a_callee_returning_two_formals_is_a_view_of_neither() {
    assert_ne!(
        verdict(TWO_FORMALS_RETURNED, "search", "GetValue", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "two possible sources leave the cursor's root unknown"
    );
}

/// Control (ii): one return is a fresh allocation rather than a view, so the
/// callee is not a view of its formal either.
const ONE_ALLOCATING_RETURN: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
pub unsafe fn grow(mut p: *mut u8, mut n: libc::c_ulong) -> *mut u8 {
    if n > 0 { return malloc(n) as *mut u8; }
    return p.offset(1);
}
pub unsafe fn GetValue(mut p: *mut u8, mut out: *mut i32) -> i32 {
    *out = *p as i32;
    1
}
pub unsafe fn search(mut buf: *mut u8, mut n: libc::c_ulong) -> i32 {
    let mut scratch: i32 = 0;
    let mut p = grow(buf, n);
    GetValue(p, &mut scratch)
}
"#;

#[test]
fn w6p_an_allocating_return_is_not_a_view() {
    assert_ne!(
        verdict(ONE_ALLOCATING_RETURN, "search", "GetValue", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "a callee that may allocate does not hand back its argument's root"
    );
}
