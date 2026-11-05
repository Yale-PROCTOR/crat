//! wave-6p R482-4, rule (4): a `static mut` item is a named global object, so
//! two DIFFERENT statics never overlap.
//!
//! libzahl addresses 35 `static mut` arrays through `as_mut_ptr()` and passes
//! them pairwise (`zcmp(a, libzahl_tmp_cmp.as_mut_ptr())`); `resolved_local`
//! resolves only `Res::Local`, so before this rule a static had no root at all
//! — 201 of that program's 245 unproved pairs carry at least one such side.
//!
//! The claim is deliberately partial. A static is disjoint from a *different*
//! static, from this frame's stack objects and from a fresh allocation. It is
//! NOT disjoint from a parameter's pointee: a caller may pass the static
//! itself, and 71 of libzahl's sides sit opposite exactly that.

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

/// libzahl's shape: two different `static mut` arrays, each addressed by
/// `as_mut_ptr()`, passed to one call.
const TWO_STATICS: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub static mut libzahl_tmp_cmp: [u32; 4] = [0; 4];
pub static mut libzahl_tmp_div: [u32; 4] = [0; 4];
pub unsafe fn zcmp(mut a: *mut u32, mut b: *mut u32) -> i32 {
    *a = 1;
    *b.offset(1) = 2;
    0
}
pub unsafe fn zcmpi() -> i32 {
    zcmp(libzahl_tmp_cmp.as_mut_ptr(), libzahl_tmp_div.as_mut_ptr())
}
"#;

#[test]
fn w6p_two_different_statics_are_disjoint() {
    assert_eq!(
        verdict(TWO_STATICS, "zcmpi", "zcmp", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "two named global objects are two objects"
    );
}

/// Control (i): the SAME static on both sides is one object.
const ONE_STATIC_TWICE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub static mut libzahl_tmp_cmp: [u32; 4] = [0; 4];
pub unsafe fn zcmp(mut a: *mut u32, mut b: *mut u32) -> i32 {
    *a = 1;
    *b.offset(1) = 2;
    0
}
pub unsafe fn zcmpi() -> i32 {
    zcmp(libzahl_tmp_cmp.as_mut_ptr(), libzahl_tmp_cmp.as_mut_ptr())
}
"#;

#[test]
fn w6p_the_same_static_twice_is_one_object() {
    assert_ne!(
        verdict(ONE_STATIC_TWICE, "zcmpi", "zcmp", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "one static addressed twice is still one static"
    );
}

/// Control (ii), the narrowing: a static beside a pointer PARAMETER. The
/// caller may have passed that very static, so the rule must refuse — this is
/// 71 of libzahl's 201 sides.
const STATIC_BESIDE_A_PARAMETER: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub static mut libzahl_tmp_cmp: [u32; 4] = [0; 4];
pub unsafe fn zcmp(mut a: *mut u32, mut b: *mut u32) -> i32 {
    *a = 1;
    *b.offset(1) = 2;
    0
}
pub unsafe fn zcmpi(mut a: *mut u32) -> i32 {
    zcmp(a, libzahl_tmp_cmp.as_mut_ptr())
}
pub unsafe fn outer() -> i32 {
    zcmpi(libzahl_tmp_cmp.as_mut_ptr())
}
"#;

#[test]
fn w6p_a_static_is_not_disjoint_from_a_parameter() {
    // Non-vacuous: `outer` proves the two CAN be one object.
    assert_ne!(
        verdict(STATIC_BESIDE_A_PARAMETER, "zcmpi", "zcmp", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "a caller may pass the static itself, so entry storage proves nothing"
    );
}

/// A static is disjoint from a stack object of the current frame: a global is
/// never a local.
const STATIC_AND_A_STACK_LOCAL: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub static mut libzahl_tmp_cmp: [u32; 4] = [0; 4];
pub unsafe fn zcmp(mut a: *mut u32, mut b: *mut u32) -> i32 {
    *a = 1;
    *b.offset(1) = 2;
    0
}
pub unsafe fn zcmpi() -> i32 {
    let mut scratch: [u32; 4] = [0; 4];
    zcmp(scratch.as_mut_ptr(), libzahl_tmp_cmp.as_mut_ptr())
}
"#;

#[test]
fn w6p_a_static_is_disjoint_from_a_stack_local() {
    assert_eq!(
        verdict(STATIC_AND_A_STACK_LOCAL, "zcmpi", "zcmp", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "a global is never this frame's stack"
    );
}
