//! wave-6p R483-3(f): certificate (e) extends to statics.
//!
//! Report 023 left 71 of libzahl's sides — 113 pairs corpus-wide — on the one
//! refusal `RootClass::Static` cannot answer: a static beside a parameter's
//! pointee, where a caller may have passed the static itself. That is the same
//! question R462-1 already answers for two formals, and the same closed world
//! answers it: if every in-crate call site of the function passes, at that
//! position, something whose root is known and is NOT this static, then the
//! parameter never carries it.
//!
//! Refused when any caller passes the static, when any caller's argument has
//! an unknown root, when the function has no in-crate caller at all, and when
//! the function is EXPORTED — an embedder is outside the closed world and the
//! waiver R462-1 grants for two formals says nothing about a program-internal
//! static's address.

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

/// libzahl's shape with the closed world discharging it: `zcmpi`'s only caller
/// passes a DIFFERENT static, so `zcmpi`'s formal never carries
/// `libzahl_tmp_cmp` and the pair inside it is separable.
const CALLERS_DISCHARGE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub static mut libzahl_tmp_cmp: [u32; 4] = [0; 4];
pub static mut libzahl_tmp_div: [u32; 4] = [0; 4];
pub unsafe fn zcmp(mut a: *mut u32, mut b: *mut u32) -> i32 {
    *a = 1;
    *b.offset(1) = 2;
    0
}
pub unsafe fn zcmpi(mut a: *mut u32) -> i32 {
    zcmp(a, libzahl_tmp_cmp.as_mut_ptr())
}
pub unsafe fn driver() -> i32 {
    zcmpi(libzahl_tmp_div.as_mut_ptr())
}
"#;

#[test]
fn w6p_a_static_is_disjoint_when_every_caller_passes_something_else() {
    assert_eq!(
        verdict(CALLERS_DISCHARGE, "zcmpi", "zcmp", 0, 1),
        Ok(CertificateKind::StaticVsEntry(1)),
        "the closed world sees the one caller, and it passes a different static"
    );
}

/// Control (i): one caller passes the very static. Report 023's counterexample,
/// now the refusal it should be.
const A_CALLER_PASSES_THE_STATIC: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub static mut libzahl_tmp_cmp: [u32; 4] = [0; 4];
pub static mut libzahl_tmp_div: [u32; 4] = [0; 4];
pub unsafe fn zcmp(mut a: *mut u32, mut b: *mut u32) -> i32 {
    *a = 1;
    *b.offset(1) = 2;
    0
}
pub unsafe fn zcmpi(mut a: *mut u32) -> i32 {
    zcmp(a, libzahl_tmp_cmp.as_mut_ptr())
}
pub unsafe fn driver() -> i32 {
    zcmpi(libzahl_tmp_div.as_mut_ptr()) + zcmpi(libzahl_tmp_cmp.as_mut_ptr())
}
"#;

#[test]
fn w6p_one_caller_passing_the_static_refuses_it() {
    assert!(
        !matches!(
            verdict(A_CALLER_PASSES_THE_STATIC, "zcmpi", "zcmp", 0, 1),
            Ok(CertificateKind::StaticVsEntry(_))
        ),
        "a single caller handing over the static is the whole counterexample"
    );
}

/// Control (ii): a caller whose own argument has an unknown root proves
/// nothing about what the parameter carries.
const A_CALLER_WITH_AN_UNKNOWN_ROOT: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn opaque() -> *mut u32; }
pub static mut libzahl_tmp_cmp: [u32; 4] = [0; 4];
pub unsafe fn zcmp(mut a: *mut u32, mut b: *mut u32) -> i32 {
    *a = 1;
    *b.offset(1) = 2;
    0
}
pub unsafe fn zcmpi(mut a: *mut u32) -> i32 {
    zcmp(a, libzahl_tmp_cmp.as_mut_ptr())
}
pub unsafe fn driver() -> i32 {
    zcmpi(opaque())
}
"#;

#[test]
fn w6p_an_unknown_caller_argument_refuses_it() {
    assert!(
        !matches!(
            verdict(A_CALLER_WITH_AN_UNKNOWN_ROOT, "zcmpi", "zcmp", 0, 1),
            Ok(CertificateKind::StaticVsEntry(_))
        ),
        "an unknown root may be the static"
    );
}

/// Control (iii): an EXPORTED function has callers the closed world cannot
/// see. R462-1 waives aliasing between two of an entry's own parameters; it
/// says nothing about whether one of them is a program-internal static.
const AN_EXPORTED_FUNCTION: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub static mut libzahl_tmp_cmp: [u32; 4] = [0; 4];
pub static mut libzahl_tmp_div: [u32; 4] = [0; 4];
pub unsafe fn zcmp(mut a: *mut u32, mut b: *mut u32) -> i32 {
    *a = 1;
    *b.offset(1) = 2;
    0
}
#[no_mangle]
pub unsafe extern "C" fn zcmpi(mut a: *mut u32) -> i32 {
    zcmp(a, libzahl_tmp_cmp.as_mut_ptr())
}
pub unsafe fn driver() -> i32 {
    zcmpi(libzahl_tmp_div.as_mut_ptr())
}
"#;

#[test]
fn w6p_an_exported_function_is_not_closed() {
    assert!(
        !matches!(
            verdict(AN_EXPORTED_FUNCTION, "zcmpi", "zcmp", 0, 1),
            Ok(CertificateKind::StaticVsEntry(_))
        ),
        "an embedder is outside the closed world"
    );
}

/// Control (iv): no in-crate caller at all is no evidence, not good evidence.
const NO_CALLER_AT_ALL: &str = r#"
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
"#;

#[test]
fn w6p_no_in_crate_caller_is_no_evidence() {
    assert!(
        !matches!(
            verdict(NO_CALLER_AT_ALL, "zcmpi", "zcmp", 0, 1),
            Ok(CertificateKind::StaticVsEntry(_))
        ),
        "an uncalled function's parameter is unconstrained"
    );
}
