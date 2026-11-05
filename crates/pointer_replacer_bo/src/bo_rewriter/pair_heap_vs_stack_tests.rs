//! wave-6p R631-11: an admitted field's block beside a stack object or a
//! static. Every store into an admitted field is an allocation or null
//! (R479-4a, R579-3), and an allocator never returns a stack object or a
//! static, so the two are disjoint with no store needed. brotli's shape is a
//! stack `storage_ix` beside a fresh `(*s).storage_` (report 051 §5).

use super::decision::pair_disjointness::{CertificateKind, PairDisjointnessIndex, Unproved};

fn verdict(src: &str, caller: &str) -> Result<CertificateKind, Unproved> {
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
        out = Some(index.certify_recorded(function(caller), function("Use2"), 0, 1));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

/// `storage_` is stored only by `malloc` (`Init`), so a read of it names an
/// admitted field's block. `loose` is stored from a parameter, so it is not
/// admitted. `Use2` takes two `u32` pointers: the type rule refuses
/// `same-type`, and no rule but a root rule separates the pairs below. Each
/// stack pointer takes its object's address twice, so R466-5's fresh-stack
/// certificate does not answer first.
const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, static_mut_refs)]
extern "C" {
    fn malloc(n: libc::c_ulong) -> *mut libc::c_void;
}
#[repr(C)]
pub struct Enc { pub storage_: *mut u32, pub loose: *mut u32 }
pub static mut G: u32 = 0;
pub unsafe fn Init(mut s: *mut Enc) {
    (*s).storage_ = malloc(16) as *mut u32;
}
pub unsafe fn Point(mut s: *mut Enc, mut q: *mut u32) {
    (*s).loose = q;
}
pub unsafe fn Use2(mut x: *mut u32, mut y: *mut u32) {
    *x = 1;
    *y = 2;
}
"#;

/// W1: brotli's shape — a stack `storage_ix` beside `(*s).storage_`.
const A_STACK_OBJECT: &str = r#"
pub unsafe fn Emit(mut s: *mut Enc) {
    let mut storage_ix: u32 = 0;
    let mut first: *mut u32 = &mut storage_ix;
    let mut ix: *mut u32 = &mut storage_ix;
    Use2(ix, (*s).storage_);
}
"#;

/// W2: a static beside `(*s).storage_`.
const A_STATIC: &str = r#"
pub unsafe fn Emit(mut s: *mut Enc) {
    Use2(&mut G, (*s).storage_);
}
"#;

/// C1: an entry object may itself be the block the field holds (a caller can
/// pass `(*s).storage_` as `x`), and nothing was stored here — refused, as it
/// was.
const AN_ENTRY_OBJECT: &str = r#"
pub unsafe fn Emit(mut x: *mut u32, mut s: *mut Enc) {
    Use2(x, (*s).storage_);
}
"#;

/// C2: a fresh LOCAL, not a stack object — the field is admitted through it
/// (R579-3 (c)), so it IS the field's block.
const THE_FIELDS_OWN_LOCAL: &str = r#"
pub unsafe fn Emit(mut s: *mut Enc) {
    let mut c = malloc(16) as *mut u32;
    (*s).storage_ = c;
    Use2(c, (*s).storage_);
}
"#;

/// C3: a field that is not admitted beside a stack object — `Point` may have
/// stored this very stack address into it.
const A_FIELD_NOT_ADMITTED: &str = r#"
pub unsafe fn Emit(mut s: *mut Enc) {
    let mut v: u32 = 0;
    let mut first: *mut u32 = &mut v;
    let mut p: *mut u32 = &mut v;
    Use2(p, (*s).loose);
}
"#;

fn source(extra: &str) -> String {
    format!("{PRELUDE}{extra}")
}

#[test]
fn w6p_r631_an_admitted_fields_block_is_not_a_stack_object() {
    assert_eq!(
        verdict(&source(A_STACK_OBJECT), "Emit"),
        Ok(CertificateKind::DistinctRoots),
        "no allocator returns `storage_ix`'s stack slot"
    );
}

#[test]
fn w6p_r631_an_admitted_fields_block_is_not_a_static() {
    assert_eq!(
        verdict(&source(A_STATIC), "Emit"),
        Ok(CertificateKind::DistinctRoots),
        "no allocator returns the static `G`"
    );
}

#[test]
fn w6p_r631_an_entry_object_beside_the_field_is_still_refused() {
    let verdict = verdict(&source(AN_ENTRY_OBJECT), "Emit");
    assert!(verdict.is_err(), "got {verdict:?}");
}

#[test]
fn w6p_r631_the_fields_own_fresh_local_is_still_refused() {
    let verdict = verdict(&source(THE_FIELDS_OWN_LOCAL), "Emit");
    assert!(verdict.is_err(), "got {verdict:?}");
}

#[test]
fn w6p_r631_a_field_not_admitted_beside_a_stack_object_is_refused() {
    let verdict = verdict(&source(A_FIELD_NOT_ADMITTED), "Emit");
    assert!(verdict.is_err(), "got {verdict:?}");
}
