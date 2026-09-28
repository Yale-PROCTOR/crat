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

/// W3 (R628-7 f′): `BrotliStoreMetaBlock`'s shape — the store is made by a
/// callee of the CALLER (`Fill`, a must-store summary), before `Store` is
/// called; `x` is the caller's entry object.
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

/// The (f′) chain's shared part: `Store` reads `(*mb).map` beside its `x`.
const STORE: &str = r#"
pub unsafe fn Fill(mut mb: *mut Split) {
    (*mb).map = malloc(16) as *mut u32;
}
pub unsafe fn Clear(mut mb: *mut Split) {
    (*mb).map = 0 as *mut u32;
}
pub unsafe fn Store(mut x: *mut u32, mut mb: *mut Split) {
    Use2(x, (*mb).map);
}
"#;

/// W4: two levels — `Mid` passes its own formals through.
const TWO_LEVELS: &str = r#"
pub unsafe fn Mid(mut x: *mut u32, mut mb: *mut Split) {
    Store(x, mb);
}
pub unsafe fn Write(mut x: *mut u32) {
    let mut s = Split { map: 0 as *mut u32, view: 0 as *mut u32, n: 0 };
    Fill(&mut s);
    Mid(x, &mut s);
}
"#;

/// W5: brotli's `InitMetaBlockSplit` — a NULL store is a store (the block is
/// null or one allocated later), and a store both arms of an `if` make counts.
const A_NULL_STORE_AND_BOTH_ARMS: &str = r#"
pub unsafe fn Write(mut x: *mut u32, mut c: i32) {
    let mut s = Split { map: 0 as *mut u32, view: 0 as *mut u32, n: 0 };
    if c != 0 {
        Fill(&mut s);
    } else {
        Clear(&mut s);
    }
    Store(x, &mut s);
}
"#;

/// W8 (R631-11, was C11): `Store` is `#[no_mangle]`. An embedder's call is
/// unseen, and R462-1's exported-entry contract covers that external edge
/// whatever the other side's root; the in-crate caller `Write` still stores.
const EXPORTED: &str = r#"
pub unsafe fn Fill(mut mb: *mut Split) {
    (*mb).map = malloc(16) as *mut u32;
}
#[no_mangle]
pub unsafe extern "C" fn Store(mut x: *mut u32, mut mb: *mut Split) {
    Use2(x, (*mb).map);
}
pub unsafe fn Write(mut x: *mut u32) {
    let mut s = Split { map: 0 as *mut u32, view: 0 as *mut u32, n: 0 };
    Fill(&mut s);
    Store(x, &mut s);
}
"#;

/// C17: `Store` is `#[no_mangle]`, but its in-crate caller hands `mb` on
/// without storing the field: the waiver covers the embedder's calls, not this
/// one.
const EXPORTED_BUT_AN_IN_CRATE_CALLER_DOES_NOT_STORE: &str = r#"
pub unsafe fn Fill(mut mb: *mut Split) {
    (*mb).map = malloc(16) as *mut u32;
}
#[no_mangle]
pub unsafe extern "C" fn Store(mut x: *mut u32, mut mb: *mut Split) {
    Use2(x, (*mb).map);
}
pub unsafe fn Write(mut x: *mut u32, mut mb: *mut Split) {
    Store(x, mb);
}
"#;

/// C12: the callee stores on one branch only — no summary.
const A_CALLEE_THAT_MAY_NOT_STORE: &str = r#"
pub unsafe fn Maybe(mut mb: *mut Split) {
    if (*mb).n > 0 {
        (*mb).map = malloc(16) as *mut u32;
    }
}
pub unsafe fn Store(mut x: *mut u32, mut mb: *mut Split) {
    Use2(x, (*mb).map);
}
pub unsafe fn Write(mut x: *mut u32, mut mb: *mut Split) {
    Maybe(mb);
    Store(x, mb);
}
"#;

/// C13: the callee may return before its store — no summary.
const A_CALLEE_THAT_RETURNS_FIRST: &str = r#"
pub unsafe fn Early(mut mb: *mut Split) {
    if (*mb).n == 0 {
        return;
    }
    (*mb).map = malloc(16) as *mut u32;
}
pub unsafe fn Store(mut x: *mut u32, mut mb: *mut Split) {
    Use2(x, (*mb).map);
}
pub unsafe fn Write(mut x: *mut u32, mut mb: *mut Split) {
    Early(mb);
    Store(x, mb);
}
"#;

/// C14: the caller fills AFTER handing the object on.
const FILLED_AFTER_THE_CALL: &str = r#"
pub unsafe fn Write(mut x: *mut u32, mut mb: *mut Split) {
    Store(x, mb);
    Fill(mb);
}
"#;

/// C15: at the caller, the other side is not an entry object.
const THE_CALLERS_OTHER_SIDE_UNKNOWN: &str = r#"
pub unsafe fn Write(mut mb: *mut Split) {
    Fill(mb);
    let mut u = ext_u32();
    Store(u, mb);
}
"#;

/// W6: `BrotliCompressBufferQuality10`'s shape — at the caller, the other side
/// is a STACK object (`m = &mut memory_manager`), which no allocator returned.
const A_STACK_OBJECT_AT_THE_CALLER: &str = r#"
pub unsafe fn Write() {
    let mut mm: u32 = 0;
    let mut x: *mut u32 = &mut mm;
    let mut s = Split { map: 0 as *mut u32, view: 0 as *mut u32, n: 0 };
    Fill(&mut s);
    Store(x, &mut s);
}
"#;

/// W7: the local form beside a stack object. Its address is taken twice, so
/// R466-5's fresh-stack certificate (address first taken at the call) does not
/// answer first.
const A_STACK_OBJECT_LOCALLY: &str = r#"
pub unsafe fn Build(mut mb: *mut Split) {
    let mut local: u32 = 0;
    let mut first: *mut u32 = &mut local;
    let mut second: *mut u32 = &mut local;
    (*mb).map = malloc(16) as *mut u32;
    Use2(second, (*mb).map);
}
"#;

/// C16: a fresh local IS the field's block — `map` is admitted through it.
const THE_FIELDS_OWN_LOCAL: &str = r#"
pub unsafe fn Build(mut mb: *mut Split) {
    let mut c = malloc(16) as *mut u32;
    (*mb).map = c;
    Use2(c, (*mb).map);
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
fn w6p_r628_fp_a_store_by_the_callers_callee_is_seen() {
    assert_eq!(
        verdict(&source(STORED_BY_THE_CALLERS_CALLEE), "Store", "Use2", 0, 1),
        Ok(CertificateKind::AllocationIdentity),
        "`Write` stores `s.map` through `Fill` before handing `&mut s` and its entry `x` to `Store`"
    );
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

fn chain(extra: &str) -> String {
    format!("{PRELUDE}{STORE}{extra}")
}

#[test]
fn w6p_r628_fp_two_levels_up() {
    assert_eq!(
        verdict(&chain(TWO_LEVELS), "Store", "Use2", 0, 1),
        Ok(CertificateKind::AllocationIdentity)
    );
}

#[test]
fn w6p_r628_fp_a_null_store_and_a_store_both_arms_make_count() {
    assert_eq!(
        verdict(&chain(A_NULL_STORE_AND_BOTH_ARMS), "Store", "Use2", 0, 1),
        Ok(CertificateKind::AllocationIdentity)
    );
}

#[test]
fn w6p_r631_fp_an_exported_callee_rests_on_the_exported_entry_waiver() {
    assert_eq!(
        verdict(&source(EXPORTED), "Store", "Use2", 0, 1),
        Ok(CertificateKind::ExportedEntryWaiver),
        "the embedder's calls are W4's; `Write`, the in-crate caller, stores first"
    );
}

#[test]
fn w6p_r631_fp_an_exported_callees_in_crate_caller_must_still_store() {
    refused(EXPORTED_BUT_AN_IN_CRATE_CALLER_DOES_NOT_STORE, "Store");
}

#[test]
fn w6p_r628_fp_a_callee_that_may_not_store_is_refused() {
    refused(A_CALLEE_THAT_MAY_NOT_STORE, "Store");
}

#[test]
fn w6p_r628_fp_a_callee_that_returns_before_its_store_is_refused() {
    refused(A_CALLEE_THAT_RETURNS_FIRST, "Store");
}

#[test]
fn w6p_r628_fp_a_store_after_the_hand_off_is_refused() {
    let verdict = verdict(&chain(FILLED_AFTER_THE_CALL), "Store", "Use2", 0, 1);
    assert!(verdict.is_err(), "got {verdict:?}");
}

#[test]
fn w6p_r628_fp_a_callers_unknown_other_side_is_refused() {
    let verdict = verdict(
        &chain(THE_CALLERS_OTHER_SIDE_UNKNOWN),
        "Store",
        "Use2",
        0,
        1,
    );
    assert!(verdict.is_err(), "got {verdict:?}");
}

#[test]
fn w6p_r628_fp_a_stack_object_at_the_caller_is_not_an_allocation() {
    assert_eq!(
        verdict(&chain(A_STACK_OBJECT_AT_THE_CALLER), "Store", "Use2", 0, 1),
        Ok(CertificateKind::AllocationIdentity)
    );
}

#[test]
fn w6p_r628_f_a_stack_object_is_not_an_allocation() {
    assert_eq!(
        verdict(&source(A_STACK_OBJECT_LOCALLY), "Build", "Use2", 0, 1),
        Ok(CertificateKind::AllocationIdentity)
    );
}

#[test]
fn w6p_r628_f_the_fields_own_local_is_refused() {
    refused(THE_FIELDS_OWN_LOCAL, "Build");
}
