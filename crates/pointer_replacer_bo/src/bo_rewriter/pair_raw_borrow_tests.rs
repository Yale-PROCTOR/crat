//! wave-6p R624-1 (§6 of report 052): a raw borrow — `&raw mut x`, which
//! `addr_of_mut!(x)` expands to — is read exactly as `&mut x` is. Before, only
//! `BorrowKind::Ref` was matched: an argument written as a raw borrow cycled
//! between `argument_provenance_peeled` and `pointer_value_provenance` until
//! the stack overflowed, and a raw borrow of a pointer local's own slot did not
//! mark the local address-taken.

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

/// `Put` takes two formals of ONE pointee type, so the type rule refuses
/// `same-type` and the root rules are the ones under test.
const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct A { pub x: i32 }
#[repr(C)]
pub struct S { pub f1: A, pub f2: A }
pub unsafe fn Put(mut a: *mut A, mut b: *mut A) {
    (*a).x = 1;
    (*b).x = 2;
}
pub unsafe fn Retarget(mut pp: *mut *mut A, mut q: *mut A) {
    *pp = q;
}
"#;

/// W1: two raw borrows of two stack objects, as arguments.
const RAW_ARGUMENTS: &str = r#"
pub unsafe fn Raw() {
    let mut x = A { x: 0 };
    let mut y = A { x: 0 };
    Put(&raw mut x, &raw mut y);
}
"#;

/// W2: a pointer local re-pointed through a raw borrow of its own slot. After
/// `Retarget`, `p` IS `q`.
const RAW_BORROW_OF_THE_SLOT: &str = r#"
pub unsafe fn Slot(mut q: *mut A) {
    let mut a = A { x: 0 };
    let mut p: *mut A = &mut a;
    Retarget(&raw mut p, q);
    Put(p, q);
}
"#;

/// W3: two view locals taken raw — each folds to the place it is a view of.
const RAW_VIEW_LOCALS: &str = r#"
pub unsafe fn Views(mut s: *mut S) {
    let mut a = &raw mut (*s).f1;
    let mut b = &raw mut (*s).f2;
    Put(a, b);
}
"#;

/// W4: a local initialized by a raw borrow derives from the borrowed object.
const RAW_DERIVED_LOCAL: &str = r#"
pub unsafe fn Derived(mut q: *mut A) {
    let mut a = A { x: 0 };
    let mut p = &raw mut a;
    Put(p, q);
}
"#;

fn source(extra: &str) -> String {
    format!("{PRELUDE}{extra}")
}

#[test]
fn w6p_r624_a_raw_borrow_argument_reads_as_its_place() {
    assert_eq!(
        verdict(&source(RAW_ARGUMENTS), "Raw", "Put", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "`&raw mut x` and `&raw mut y` are two stack objects, as `&mut x` / `&mut y` are"
    );
}

#[test]
fn w6p_r624_a_raw_borrow_of_a_pointer_slot_takes_its_address() {
    let verdict = verdict(&source(RAW_BORROW_OF_THE_SLOT), "Slot", "Put", 0, 1);
    assert!(
        verdict.is_err(),
        "`p` may be `q` after `Retarget(&raw mut p, q)`: got {verdict:?}"
    );
}

#[test]
fn w6p_r624_raw_view_locals_fold_to_their_places() {
    assert_eq!(
        verdict(&source(RAW_VIEW_LOCALS), "Views", "Put", 0, 1),
        Ok(CertificateKind::DisjointFields),
        "`a` is `(*s).f1` and `b` is `(*s).f2`"
    );
}

#[test]
fn w6p_r624_a_raw_borrow_initializer_derives_from_its_object() {
    assert_eq!(
        verdict(&source(RAW_DERIVED_LOCAL), "Derived", "Put", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "`p` addresses the stack object `a`, which is not `q`'s entry storage"
    );
}
