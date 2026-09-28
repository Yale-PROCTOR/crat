//! wave-6p R624-1 rule (f): allocation identity.
//!
//! brotli's `BrotliBuildMetaBlock` stores `(*mb).literal_context_map =
//! BrotliAllocate(m, ..)` and then calls `BrotliClusterHistogramsLiteral(m, ..,
//! (*mb).literal_context_map)`. The type route may not certify `m` (entry)
//! beside the map (Erratum 9a (i), R619-4's yield), but the map's block was
//! allocated after the caller's entry, when `m`'s object already existed, and an
//! allocator never returns storage overlapping a live object.

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

/// `map` and `view` are stored only by `malloc` (and `view` by an offset of
/// `map`); `Use` is brotli's shape (the allocator state beside a `u32` map),
/// `Use2` takes two `u32` pointers so the type rule refuses `same-type` and only
/// rule (f) could separate them.
const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
extern "C" {
    fn malloc(n: libc::c_ulong) -> *mut libc::c_void;
    fn ext_u32() -> *mut u32;
}
#[repr(C)]
pub struct MM { pub opaque: *mut libc::c_void }
#[repr(C)]
pub struct Split { pub map: *mut u32, pub view: *mut u32, pub n: libc::c_ulong }
pub unsafe fn Use(mut m: *mut MM, mut map: *mut u32) {
    (*m).opaque = 0 as *mut libc::c_void;
    *map = 1;
}
pub unsafe fn Use2(mut x: *mut u32, mut map: *mut u32) {
    *x = 1;
    *map = 2;
}
"#;

/// W1: `BrotliBuildMetaBlock`'s shape.
const STORED_THEN_PASSED: &str = r#"
pub unsafe fn Build(mut m: *mut MM, mut mb: *mut Split) {
    (*mb).map = if (*mb).n > 0 { malloc(16) as *mut u32 } else { 0 as *mut u32 };
    Use(m, (*mb).map);
}
"#;

/// W2: the store in an enclosing block, the call inside a loop and a branch;
/// the pointee types are the same, so no type rule is involved.
const STORED_THEN_PASSED_IN_A_LOOP: &str = r#"
pub unsafe fn Build(mut x: *mut u32, mut mb: *mut Split) {
    (*mb).map = malloc(16) as *mut u32;
    let mut i = 0;
    while i < 2 {
        if i == 1 {
            Use2(x, (*mb).map);
        }
        i += 1;
    }
}
"#;

/// C1 (the relay's control): the field is re-assigned from the entry object, so
/// it is not admitted and names no block.
const REASSIGNED_FROM_THE_ENTRY: &str = r#"
pub unsafe fn Point(mut x: *mut u32, mut mb: *mut Split) {
    (*mb).map = x;
}
pub unsafe fn Build(mut x: *mut u32, mut mb: *mut Split) {
    (*mb).map = malloc(16) as *mut u32;
    Use2(x, (*mb).map);
}
"#;

/// C2: the store comes after the call.
const STORED_AFTER: &str = r#"
pub unsafe fn Build(mut x: *mut u32, mut mb: *mut Split) {
    Use2(x, (*mb).map);
    (*mb).map = malloc(16) as *mut u32;
}
"#;

/// C3: the store runs on one branch only.
const STORED_ON_ONE_BRANCH: &str = r#"
pub unsafe fn Build(mut x: *mut u32, mut mb: *mut Split) {
    if (*mb).n > 0 {
        (*mb).map = malloc(16) as *mut u32;
    }
    Use2(x, (*mb).map);
}
"#;

/// C4: the store is into ANOTHER object's field.
const STORED_INTO_ANOTHER_OBJECT: &str = r#"
pub unsafe fn Build(mut x: *mut u32, mut mb: *mut Split, mut other: *mut Split) {
    (*other).map = malloc(16) as *mut u32;
    Use2(x, (*mb).map);
}
"#;

/// C5: `view` is offset-admitted — its block is `map`'s, allocated whenever.
const AN_OFFSET_FIELD: &str = r#"
pub unsafe fn Build(mut x: *mut u32, mut mb: *mut Split) {
    (*mb).map = malloc(16) as *mut u32;
    (*mb).view = (*mb).map.offset(1);
    Use2(x, (*mb).view);
}
"#;

/// C6: the other side has no known root, so no object is known to predate the
/// allocation.
const THE_OTHER_SIDE_UNKNOWN: &str = r#"
pub unsafe fn Build(mut mb: *mut Split) {
    (*mb).map = malloc(16) as *mut u32;
    let mut u = ext_u32();
    Use2(u, (*mb).map);
}
"#;

/// C7: `BrotliStoreMetaBlock`'s shape — the store is in a callee of the
/// CALLER, not in this body (scope of the local form; report 053).
const STORED_BY_THE_CALLERS_CALLEE: &str = r#"
pub unsafe fn Fill(mut mb: *mut Split) {
    (*mb).map = malloc(16) as *mut u32;
}
pub unsafe fn Store(mut x: *mut u32, mut mb: *mut Split) {
    Use2(x, (*mb).map);
}
pub unsafe fn Write(mut x: *mut u32) {
    let mut s = Split { map: 0 as *mut u32, view: 0 as *mut u32, n: 0 };
    Fill(&mut s);
    Store(x, &mut s);
}
"#;

/// C8: a local read BEFORE the store holds the old block.
const A_LOCAL_READ_BEFORE_THE_STORE: &str = r#"
pub unsafe fn Build(mut x: *mut u32, mut mb: *mut Split) {
    let mut v = (*mb).map;
    (*mb).map = malloc(16) as *mut u32;
    Use2(x, v);
}
"#;

/// C9: the store is into the SAME field key of the same root object, but at
/// another place — `(*t).a.map` stored, `(*t).b.map` read. `b.map`'s block may
/// predate the entry.
const STORED_INTO_A_SIBLING_PLACE: &str = r#"
#[repr(C)]
pub struct Two { pub a: Split, pub b: Split }
pub unsafe fn Build(mut x: *mut u32, mut t: *mut Two) {
    (*t).a.map = malloc(16) as *mut u32;
    Use2(x, (*t).b.map);
}
"#;

/// C10: the base pointer moves between the store and the call — `(*p).map` at
/// the call is the NEXT element's field, whose block may predate the entry.
const THE_BASE_MOVES_AFTER_THE_STORE: &str = r#"
pub unsafe fn Build(mut x: *mut u32, mut p: *mut Split) {
    (*p).map = malloc(16) as *mut u32;
    p = p.offset(1);
    Use2(x, (*p).map);
}
"#;

fn source(extra: &str) -> String {
    format!("{PRELUDE}{extra}")
}

fn refused(extra: &str, caller: &str) {
    let verdict = verdict(&source(extra), caller, "Use2", 0, 1);
    assert!(verdict.is_err(), "{caller}: got {verdict:?}");
}

#[test]
fn w6p_r624_f_a_block_stored_since_entry_is_not_the_entry_object() {
    assert_eq!(
        verdict(&source(STORED_THEN_PASSED), "Build", "Use", 0, 1),
        Ok(CertificateKind::AllocationIdentity),
        "`(*mb).map` was allocated after `Build`'s entry; `*m` existed at it"
    );
}

#[test]
fn w6p_r624_f_an_enclosing_store_dominates_a_nested_call() {
    assert_eq!(
        verdict(&source(STORED_THEN_PASSED_IN_A_LOOP), "Build", "Use2", 0, 1),
        Ok(CertificateKind::AllocationIdentity)
    );
}

#[test]
fn w6p_r624_f_a_field_reassigned_from_the_entry_is_refused() {
    refused(REASSIGNED_FROM_THE_ENTRY, "Build");
}

#[test]
fn w6p_r624_f_a_store_after_the_call_is_refused() {
    refused(STORED_AFTER, "Build");
}

#[test]
fn w6p_r624_f_a_store_on_one_branch_is_refused() {
    refused(STORED_ON_ONE_BRANCH, "Build");
}

#[test]
fn w6p_r624_f_a_store_into_another_object_is_refused() {
    refused(STORED_INTO_ANOTHER_OBJECT, "Build");
}

#[test]
fn w6p_r624_f_an_offset_field_is_refused() {
    refused(AN_OFFSET_FIELD, "Build");
}

#[test]
fn w6p_r624_f_an_unknown_other_side_is_refused() {
    refused(THE_OTHER_SIDE_UNKNOWN, "Build");
}

#[test]
fn w6p_r624_f_a_store_in_the_callers_callee_is_out_of_the_local_form() {
    refused(STORED_BY_THE_CALLERS_CALLEE, "Store");
}

#[test]
fn w6p_r624_f_a_local_read_before_the_store_is_refused() {
    refused(A_LOCAL_READ_BEFORE_THE_STORE, "Build");
}

#[test]
fn w6p_r624_f_a_store_into_a_sibling_place_is_refused() {
    refused(STORED_INTO_A_SIBLING_PLACE, "Build");
}

#[test]
fn w6p_r624_f_a_base_that_moves_after_the_store_is_refused() {
    refused(THE_BASE_MOVES_AFTER_THE_STORE, "Build");
}
