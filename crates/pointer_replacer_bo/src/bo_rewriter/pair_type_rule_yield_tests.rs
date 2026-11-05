//! wave-6p R619-4 (2): the type rule yields for an (entry, internal) pair.
//!
//! Erratum 9a (i) keeps storage an exported entry supplies out of the type
//! route; for an `entry` side beside program-internal storage no waiver covers
//! the pair either, so the type rule does not certify it and the later rules
//! decide. Entry / entry keeps the type rule (counted under W4, R462-1, by its
//! receipt's root classes); internal / internal keeps it (P3, R542-1).

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

/// `Put` takes two DIFFERENT struct pointees, so the type rule alone would
/// certify every pair below; the root rules do not (a static or an admitted
/// field beside a parameter's pointee is not a root certificate).
const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, static_mut_refs)]
extern "C" {
    fn malloc(n: libc::c_ulong) -> *mut libc::c_void;
    fn ext() -> *mut B;
}
#[repr(C)]
pub struct A { pub x: i32 }
#[repr(C)]
pub struct B { pub y: i64 }
#[repr(C)]
pub struct Q { pub bs: *mut B }
pub static mut GA: A = A { x: 0 };
pub static mut GB: B = B { y: 0 };
pub unsafe fn InitQ(mut q: *mut Q) {
    (*q).bs = malloc(8) as *mut B;
}
pub unsafe fn Put(mut a: *mut A, mut b: *mut B) {
    (*a).x = 1;
    (*b).y = 2;
}
"#;

/// W1: brotli's shape — the allocator state `m` beside an admitted field's
/// block. Nothing after the type rule separates them.
const ENTRY_BESIDE_A_FIELD: &str = r#"
pub unsafe fn Mix(mut p: *mut A, mut q: *mut Q) {
    Put(p, (*q).bs);
}
"#;

/// W2: entry beside a static; static-vs-entry reads the one caller.
const ENTRY_BESIDE_A_STATIC: &str = r#"
pub unsafe fn S(mut p: *mut A) {
    Put(p, &mut GB);
}
pub unsafe fn Caller() {
    let mut a = A { x: 0 };
    S(&mut a);
}
"#;

/// C1: internal / internal — a fresh local beside an admitted field's block.
/// (A static there is a root certificate since R631-11, so it would not reach
/// the type rule.)
const INTERNAL_BESIDE_INTERNAL: &str = r#"
pub unsafe fn II(mut q: *mut Q) {
    let mut a = malloc(4) as *mut A;
    Put(a, (*q).bs);
}
"#;

/// C2: entry / entry.
const ENTRY_BESIDE_ENTRY: &str = r#"
pub unsafe fn EE(mut p: *mut A, mut r: *mut B) {
    Put(p, r);
}
"#;

/// C3: entry / other — the ruled yield is (entry, internal) only.
const ENTRY_BESIDE_OTHER: &str = r#"
pub unsafe fn EO(mut p: *mut A) {
    let mut u = ext();
    Put(p, u);
}
"#;

fn source(extra: &str) -> String {
    format!("{PRELUDE}{extra}")
}

#[test]
fn w6p_r619_the_type_rule_yields_entry_beside_internal() {
    assert_eq!(
        verdict(&source(ENTRY_BESIDE_A_FIELD), "Mix", "Put", 0, 1),
        Err(Unproved::EntryBesideInternal),
        "the type rule no longer certifies an entry side beside program storage"
    );
}

#[test]
fn w6p_r619_a_later_rule_decides_the_yielded_pair() {
    assert_eq!(
        verdict(&source(ENTRY_BESIDE_A_STATIC), "S", "Put", 0, 1),
        Ok(CertificateKind::StaticVsEntry(1)),
        "`S`'s one caller passes a stack object, not `GB`"
    );
}

#[test]
fn w6p_r619_internal_beside_internal_keeps_the_type_rule() {
    assert_eq!(
        verdict(&source(INTERNAL_BESIDE_INTERNAL), "II", "Put", 0, 1),
        Ok(CertificateKind::TypeRule)
    );
}

#[test]
fn w6p_r619_entry_beside_entry_keeps_the_type_rule() {
    assert_eq!(
        verdict(&source(ENTRY_BESIDE_ENTRY), "EE", "Put", 0, 1),
        Ok(CertificateKind::TypeRule)
    );
}

#[test]
fn w6p_r619_entry_beside_other_keeps_the_type_rule() {
    assert_eq!(
        verdict(&source(ENTRY_BESIDE_OTHER), "EO", "Put", 0, 1),
        Ok(CertificateKind::TypeRule)
    );
}
