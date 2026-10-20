//! wave-6p R672-4: the census counts every certificate that rests on an
//! exported entry's unseen callers by its receipt KEY.
//!
//! * R486-2's static waiver (`StaticVsEntryWaived`) carried its waiver id only in
//!   the lane's ledger receipt; its census key was the proven one, so libzahl's
//!   `zcmpi → zcmp` pairs were counted as proven. It has its own key now.
//! * R462-1 (2) and R672-2's fixture: once a provided test is an in-crate
//!   caller, an exported entry called with ONE argument twice refuses the pair
//!   inside it, and distinct arguments certify it on the waiver's external edge
//!   only. The fixture is shared with wave-6o's end-to-end witness (their relay
//!   112 §4): [`ZCMP_SHAPE`] plus one of [`DISTINCT_ARGUMENTS`] /
//!   [`ONE_ARGUMENT_TWICE`], so there is one fixture, not two.

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

/// libzahl's `zcmpi`: the exported entry's formal `a` beside the static
/// `libzahl_tmp_cmp`, with no in-crate caller of `zcmpi`.
const STATIC_BESIDE_AN_EXPORTED_FORMAL: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, static_mut_refs)]
pub static mut libzahl_tmp_cmp: [u32; 4] = [0; 4];
pub unsafe fn zcmp(mut a: *mut u32, mut b: *mut u32) -> i32 {
    *a = 1;
    *b.offset(1) = 2;
    0
}
#[no_mangle]
pub unsafe extern "C" fn zcmpi(mut a: *mut u32) -> i32 {
    zcmp(a, libzahl_tmp_cmp.as_mut_ptr())
}
"#;

/// R672-2's shape: libzahl's `zcmp`, an exported entry whose two formals reach
/// a callee that writes through one of them (`&mut` / `&mut` at 52).
pub(super) const ZCMP_SHAPE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct Z { pub sign: i32, pub used: u32 }
pub unsafe fn zcmpmag(mut a: *mut Z, mut b: *mut Z) -> i32 {
    (*a).used = (*b).used;
    (*a).sign - (*b).sign
}
#[no_mangle]
pub unsafe extern "C" fn zcmp(mut a: *mut Z, mut b: *mut Z) -> i32 {
    zcmpmag(a, b)
}
"#;

/// The provided test, in-crate, with two distinct operands.
pub(super) const DISTINCT_ARGUMENTS: &str = r#"
pub unsafe fn main_0() -> i32 {
    let mut x = Z { sign: 1, used: 1 };
    let mut y = Z { sign: 1, used: 2 };
    let mut p: *mut Z = &mut x;
    let mut q: *mut Z = &mut y;
    zcmp(p, q)
}
"#;

/// The provided test, in-crate, comparing a number with itself (`zcmp(a, a)`).
pub(super) const ONE_ARGUMENT_TWICE: &str = r#"
pub unsafe fn main_0() -> i32 {
    let mut x = Z { sign: 1, used: 1 };
    let mut p: *mut Z = &mut x;
    zcmp(p, p)
}
"#;

#[test]
fn w6p_r672_the_static_waiver_has_its_own_census_key() {
    let outcome = verdict(STATIC_BESIDE_AN_EXPORTED_FORMAL, "zcmpi", "zcmp", 0, 1);
    assert_eq!(
        outcome.map(CertificateKind::key),
        Ok("pair-disjoint:static-vs-entry:exported-entry-static-waiver"),
        "the census counts R486-2's sites by key"
    );
}

#[test]
fn w6p_r672_the_proven_static_key_is_unchanged() {
    assert_eq!(
        CertificateKind::StaticVsEntry(1).key(),
        "pair-disjoint:static-vs-entry"
    );
}

#[test]
fn w6p_r672_distinct_in_crate_arguments_certify_on_the_external_edge_only() {
    let src = format!("{ZCMP_SHAPE}{DISTINCT_ARGUMENTS}");
    assert_eq!(
        verdict(&src, "main_0", "zcmp", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "the in-crate call separates by evidence"
    );
    assert_eq!(
        verdict(&src, "zcmp", "zcmpmag", 0, 1),
        Ok(CertificateKind::ExportedEntryWaiver),
        "inside the entry the pair still rests on W4 for the callers no one sees"
    );
}

#[test]
fn w6p_r672_one_in_crate_argument_twice_refuses_the_pair() {
    let src = format!("{ZCMP_SHAPE}{ONE_ARGUMENT_TWICE}");
    let at_the_call = verdict(&src, "main_0", "zcmp", 0, 1);
    assert!(at_the_call.is_err(), "zcmp(p, p): got {at_the_call:?}");
    let inside = verdict(&src, "zcmp", "zcmpmag", 0, 1);
    assert!(
        inside.is_err(),
        "R462-1 (2): an in-crate aliasing call refuses the pair, waiver or not: got {inside:?}"
    );
}
