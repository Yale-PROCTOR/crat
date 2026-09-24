//! wave-6p R550-2: rule (c), `disjoint_fields`, on a SOUND place spine
//! (Erratum 9d (ii)).
//!
//! The rule certifies two arguments disjoint when their spines share the root
//! binding, the dereference status and every projection before the first
//! differing one, and that first difference is a field projection on both
//! sides **of the same parent structure**. Before this, a projection was a
//! field NAME and every cast on the way to the root was peeled, so:
//!
//! - fields of a UNION diverged like fields of a structure and certified,
//!   although union members overlap (W1);
//! - `(*(p as *mut U)).b` beside `(*p).a` certified on the differing names,
//!   although `U.b` and `T.a` sit at the same offset (W2);
//! - the same through a folded view binding whose initializer casts (W3).
//!
//! Every fixture's callee takes two formals of ONE pointee type, so the type
//! rule refuses `same-type` and the pair reaches (c) — otherwise the type
//! route would certify first and hide the rule under test.

use super::decision::pair_disjointness::{CertificateKind, Unproved};

fn verdict_of(
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
        let index = super::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
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

const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct T { pub a: u32, pub b: u32 }
// `U.b` sits where `T.a` sits: offset 0.
#[derive(Copy, Clone)]
#[repr(C)]
pub struct U { pub b: u32, pub a: u32 }
#[derive(Copy, Clone)]
#[repr(C)]
pub union W { pub x: u32, pub y: u32 }
#[derive(Copy, Clone)]
#[repr(C)]
pub union V { pub s: T, pub z: u64 }
#[repr(C)]
pub struct Holder { pub u: W, pub v: V, pub t: T, pub arr: [T; 4] }

pub unsafe fn take2(mut p: *mut u32, mut q: *mut u32) {
    *p = 1;
    *q = 2;
}
"#;

fn source(body: &str) -> String {
    format!("{PRELUDE}{body}")
}

/// W1: two members of one union overlap; diverging at them is not a base.
const UNION_SIBLINGS: &str = r#"
pub unsafe fn UnionSiblings(mut h: *mut Holder) {
    take2(&mut (*h).u.x, &mut (*h).u.y);
}
"#;

/// W2: the root dereference base is cast to another structure; `U.b` and
/// `T.a` overlap at offset 0 although their names differ.
const ROOT_CAST: &str = r#"
pub unsafe fn RootCast(mut h: *mut T) {
    take2(&mut (*(h as *mut U)).b, &mut (*h).a);
}
"#;

/// W3: the cast hides inside a folded view binding's initializer.
const CAST_IN_VIEW: &str = r#"
pub unsafe fn CastInView(mut h: *mut Holder) {
    let mut br: *mut U = &mut (*h).t as *mut T as *mut U;
    take2(&mut (*br).b, &mut (*h).t.a);
}
"#;

/// C1: two fields of one structure — the rule's own case.
const STRUCT_FIELDS: &str = r#"
pub unsafe fn StructFields(mut h: *mut T) {
    take2(&mut (*h).a, &mut (*h).b);
}
"#;

/// C2: fields of elements of an array of structures, at different indices
/// (Erratum 9c (iii)): index projections before the divergence may differ.
const ARRAY_OF_STRUCTS: &str = r#"
pub unsafe fn ArrayOfStructs(mut h: *mut Holder, mut i: usize, mut j: usize) {
    take2(&mut (*h).arr[i].a, &mut (*h).arr[j].b);
}
"#;

/// C3: one place written two ways — once plainly, once through a round trip
/// of type-changing casts. The retyping must not defeat the same-place
/// refusal, which is keyed on the place, not on the spine rule (c) reads.
const SAME_PLACE_TWO_CASTS: &str = r#"
pub unsafe fn SamePlaceTwoCasts(mut h: *mut T) {
    take2(&mut (*h).a as *mut u32, &mut (*h).a as *mut u32 as *mut u8 as *mut u32);
}
"#;

/// C4: a union EARLIER on the shared prefix is not the divergence; the two
/// fields diverge inside one structure member of it and are disjoint there.
const UNION_ON_THE_PREFIX: &str = r#"
pub unsafe fn UnionOnThePrefix(mut h: *mut Holder) {
    take2(&mut (*h).v.s.a, &mut (*h).v.s.b);
}
"#;

#[test]
fn w6p_union_siblings_are_not_disjoint_fields() {
    assert_eq!(
        verdict_of(&source(UNION_SIBLINGS), "UnionSiblings", "take2", 0, 1),
        Err(Unproved::UnionSibling),
        "`u.x` and `u.y` are members of one union and overlap"
    );
}

#[test]
fn w6p_a_type_changing_root_cast_forms_no_spine() {
    let verdict = verdict_of(&source(ROOT_CAST), "RootCast", "take2", 0, 1);
    assert!(
        verdict.is_err(),
        "`(*(h as *mut U)).b` and `(*h).a` overlap at offset 0: got {verdict:?}"
    );
}

#[test]
fn w6p_a_cast_inside_a_folded_view_forms_no_spine() {
    let verdict = verdict_of(&source(CAST_IN_VIEW), "CastInView", "take2", 0, 1);
    assert!(
        verdict.is_err(),
        "the view retypes `(*h).t` as `U`, so `.b` overlaps `(*h).t.a`: got {verdict:?}"
    );
}

#[test]
fn w6p_two_fields_of_one_structure_still_certify() {
    assert_eq!(
        verdict_of(&source(STRUCT_FIELDS), "StructFields", "take2", 0, 1),
        Ok(CertificateKind::DisjointFields)
    );
}

#[test]
fn w6p_fields_of_array_elements_still_certify_at_different_indices() {
    assert_eq!(
        verdict_of(&source(ARRAY_OF_STRUCTS), "ArrayOfStructs", "take2", 0, 1),
        Ok(CertificateKind::DisjointFields)
    );
}

#[test]
fn w6p_the_same_place_cast_two_ways_is_still_the_same_place() {
    assert_eq!(
        verdict_of(
            &source(SAME_PLACE_TWO_CASTS),
            "SamePlaceTwoCasts",
            "take2",
            0,
            1
        ),
        Err(Unproved::SamePlace)
    );
}

#[test]
fn w6p_a_union_on_the_shared_prefix_is_not_the_divergence() {
    assert_eq!(
        verdict_of(
            &source(UNION_ON_THE_PREFIX),
            "UnionOnThePrefix",
            "take2",
            0,
            1
        ),
        Ok(CertificateKind::DisjointFields)
    );
}
