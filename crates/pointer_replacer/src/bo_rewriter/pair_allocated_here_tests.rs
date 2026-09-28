//! wave-6p R641-9: the fold. brotli's `BrotliClusterHistograms*` grow `pairs`
//! through `BROTLI_ENSURE_CAPACITY` — `pairs` is null, an allocator's result, or
//! `new_array`, itself a fresh allocation — and hand it to the combiner beside
//! the entry `out`. Every block `pairs` ever holds was allocated during this
//! activation, after its entry, so it is not `out`'s object (rule (f)'s
//! argument). It names no ONE object, though: after `pairs = new_array` the two
//! locals are one block.

use rustc_hir::def_id::LocalDefId;

use super::decision::pair_disjointness::{CertificateKind, PairDisjointnessIndex, Unproved};

fn run<R: Send>(
    src: &str,
    caller: &str,
    callee: &str,
    read: impl FnOnce(&PairDisjointnessIndex, LocalDefId, LocalDefId) -> R + Send,
) -> R {
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
        out = Some(read(&index, function(caller), function(callee)));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

fn verdict(src: &str, caller: &str, callee: &str) -> Result<CertificateKind, Unproved> {
    run(src, caller, callee, |index, caller, callee| {
        index.certify_recorded(caller, callee, 0, 1)
    })
}

fn family(src: &str, caller: &str, callee: &str) -> &'static str {
    run(src, caller, callee, |index, caller, callee| {
        index.certificate_family_recorded(caller, callee, 0, 1)
    })
}

/// `Combine` takes a `u32` and a `Pair` of `f64`s, so the type rule certifies
/// them today (brotli's 6 are `type-rule` under entry / other); `Same` takes two
/// `u32` pointers, so only a root rule can.
const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
extern "C" {
    fn malloc(n: libc::c_ulong) -> *mut libc::c_void;
    fn free(p: *mut libc::c_void);
    fn ext_u32() -> *mut u32;
}
#[repr(C)]
pub struct Pair { pub a: f64, pub b: f64 }
pub unsafe fn Combine(mut out: *mut u32, mut pairs: *mut Pair) {
    *out = (*pairs).a as u32;
}
pub unsafe fn Same(mut out: *mut u32, mut pairs: *mut u32) {
    *out = *pairs;
}
pub unsafe fn Fill(mut p: *mut *mut u32) {
    *p = ext_u32();
}
"#;

/// W1: brotli's shape — grown through a fresh `new_array`, beside the entry
/// `out`, with different pointee types.
const GROWN: &str = r#"
pub unsafe fn Cluster(mut out: *mut u32, mut n: usize) {
    let mut pairs: *mut Pair = if n > 0 { malloc(8) as *mut Pair } else { 0 as *mut Pair };
    if n > 4 {
        let mut new_array: *mut Pair = 0 as *mut Pair;
        new_array = malloc(64) as *mut Pair;
        free(pairs as *mut libc::c_void);
        pairs = 0 as *mut Pair;
        pairs = new_array;
    }
    Combine(out, pairs);
}
"#;

/// W2: the same, with ONE pointee type, so no type rule is involved.
const GROWN_SAME_TYPE: &str = r#"
pub unsafe fn Cluster(mut out: *mut u32, mut n: usize) {
    let mut pairs: *mut u32 = if n > 0 { malloc(8) as *mut u32 } else { 0 as *mut u32 };
    if n > 4 {
        let mut new_array: *mut u32 = 0 as *mut u32;
        new_array = malloc(64) as *mut u32;
        pairs = new_array;
    }
    Same(out, pairs);
}
"#;

/// C1: the grown local beside the fresh local it was grown through — after
/// `pairs = new_array` they are one block.
const BESIDE_ITS_OWN_SOURCE: &str = r#"
pub unsafe fn Cluster(mut n: usize) {
    let mut pairs: *mut u32 = malloc(8) as *mut u32;
    let mut new_array: *mut u32 = malloc(64) as *mut u32;
    pairs = new_array;
    Same(new_array, pairs);
}
"#;

/// C2: one source is the entry `other` — `pairs` may be the entry object.
const A_PARAMETER_SOURCE: &str = r#"
pub unsafe fn Cluster(mut out: *mut u32, mut other: *mut u32, mut n: usize) {
    let mut pairs: *mut u32 = malloc(8) as *mut u32;
    if n > 4 {
        pairs = other;
    }
    Same(out, pairs);
}
"#;

/// C3: its address is taken — `Fill` may re-point it anywhere.
const ADDRESS_TAKEN: &str = r#"
pub unsafe fn Cluster(mut out: *mut u32, mut n: usize) {
    let mut pairs: *mut u32 = malloc(8) as *mut u32;
    let mut new_array: *mut u32 = malloc(64) as *mut u32;
    pairs = new_array;
    Fill(&mut pairs);
    Same(out, pairs);
}
"#;

/// C4: one source is a call that is not an allocator.
const A_FOREIGN_SOURCE: &str = r#"
pub unsafe fn Cluster(mut out: *mut u32, mut n: usize) {
    let mut pairs: *mut u32 = malloc(8) as *mut u32;
    if n > 4 {
        pairs = ext_u32();
    }
    Same(out, pairs);
}
"#;

/// C5: two such locals — `copy` is grown from `pairs` — are one block.
const TWO_SUCH_LOCALS: &str = r#"
pub unsafe fn Cluster(mut n: usize) {
    let mut pairs: *mut u32 = malloc(8) as *mut u32;
    let mut new_array: *mut u32 = malloc(64) as *mut u32;
    pairs = new_array;
    let mut copy: *mut u32 = malloc(4) as *mut u32;
    copy = pairs;
    Same(copy, pairs);
}
"#;

fn source(extra: &str) -> String {
    format!("{PRELUDE}{extra}")
}

fn refused(extra: &str) {
    let verdict = verdict(&source(extra), "Cluster", "Same");
    assert!(verdict.is_err(), "got {verdict:?}");
}

#[test]
fn w6p_r641_a_local_grown_through_fresh_allocations_is_not_the_entry_object() {
    assert_eq!(
        verdict(&source(GROWN), "Cluster", "Combine"),
        Ok(CertificateKind::AllocationIdentity),
        "every block `pairs` holds was allocated after `Cluster`'s entry"
    );
}

#[test]
fn w6p_r641_the_grown_local_is_internal_storage() {
    assert_eq!(
        family(&source(GROWN), "Cluster", "Combine"),
        "pair-disjointness-certificate:roots=entry/internal",
        "no longer entry / other, so no longer counted under W4"
    );
}

#[test]
fn w6p_r641_no_type_rule_is_needed() {
    assert_eq!(
        verdict(&source(GROWN_SAME_TYPE), "Cluster", "Same"),
        Ok(CertificateKind::AllocationIdentity)
    );
}

#[test]
fn w6p_r641_the_fresh_local_it_was_grown_through_is_refused() {
    refused(BESIDE_ITS_OWN_SOURCE);
}

#[test]
fn w6p_r641_a_parameter_source_is_refused() {
    refused(A_PARAMETER_SOURCE);
}

#[test]
fn w6p_r641_an_address_taken_local_is_refused() {
    refused(ADDRESS_TAKEN);
}

#[test]
fn w6p_r641_a_foreign_source_is_refused() {
    refused(A_FOREIGN_SOURCE);
}

#[test]
fn w6p_r641_two_such_locals_are_refused() {
    refused(TWO_SUCH_LOCALS);
}
