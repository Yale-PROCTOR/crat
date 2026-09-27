//! wave-6p R603-4: R579-3's different-fields clause with ONE same-base-only
//! side, and G5.
//!
//! Two different admitted fields separate when neither was admitted through an
//! OFFSET (R579-3 (d): the field may hold another field's block) and at most
//! one through a LOCAL (R579-3 (c): one local may be stored into both). A (c)
//! field beside a field whose every store is a direct allocator call holds a
//! different allocator evaluation's block (report 049 §2). brotli's
//! `commands_` (c) beside `storage_` (direct) is the corpus's pair.
//!
//! G5: a statement-less block around an allocator call is that allocation —
//! `BrotliCompressBufferQuality10`'s `storage = { BrotliAllocate(..) }`.

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

/// `Put` takes two formals of one pointee type, so the type rule refuses
/// `same-type` and the root rules are the ones under test.
const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments, unused_braces)]
extern "C" {
    fn malloc(n: libc::c_ulong) -> *mut libc::c_void;
}
#[repr(C)]
pub struct S {
    pub direct: *mut u8,
    pub local: *mut u8,
    pub hist: [u8; 8],
}
pub unsafe fn Put(mut a: *mut u8, mut b: *mut u8) {
    *a = 1;
    *b = 2;
}
"#;

/// W1: `local` through a fresh local (c), `direct` only by direct calls.
const A_LOCAL_FIELD_BESIDE_A_DIRECT_FIELD: &str = r#"
pub unsafe fn Init(mut s: *mut S) {
    (*s).direct = malloc(8) as *mut u8;
    let mut c = malloc(8) as *mut u8;
    (*s).local = c;
}
pub unsafe fn Use(mut s: *mut S) {
    Put((*s).local, (*s).direct);
}
"#;

/// C1: ONE local stored into both fields — one block.
const ONE_LOCAL_INTO_TWO_FIELDS: &str = r#"
pub unsafe fn Init(mut s: *mut S) {
    let mut c = malloc(8) as *mut u8;
    (*s).direct = c;
    (*s).local = c;
}
pub unsafe fn Use(mut s: *mut S) {
    Put((*s).local, (*s).direct);
}
"#;

/// C2: brotli's `RingBuffer` — `buffer_ = data_ + 2`, beside `data_`, which is
/// admitted by direct calls alone. The offset field sits on the right.
const AN_OFFSET_FIELD_BESIDE_ITS_SOURCE: &str = r#"
#[repr(C)]
pub struct R {
    pub data: *mut u8,
    pub buffer: *mut u8,
}
pub unsafe fn Init(mut r: *mut R) {
    (*r).data = malloc(16) as *mut u8;
    (*r).buffer = (*r).data.offset(2);
}
pub unsafe fn Use(mut r: *mut R) {
    Put((*r).data, (*r).buffer);
}
"#;

/// C3: a self-offset field (`next_out_ <- next_out_`), on the left, beside a
/// direct field.
const A_SELF_OFFSET_FIELD: &str = r#"
pub unsafe fn Init(mut s: *mut S) {
    (*s).direct = malloc(8) as *mut u8;
    (*s).local = malloc(8) as *mut u8;
}
pub unsafe fn Advance(mut s: *mut S) {
    (*s).local = (*s).local.offset(1);
}
pub unsafe fn Use(mut s: *mut S) {
    Put((*s).local, (*s).direct);
}
"#;

/// W2: `Quality10`'s `storage` — null, a block around an allocator call, and a
/// conditional allocator.
const A_BLOCK_AROUND_AN_ALLOCATOR: &str = r#"
pub unsafe fn Use(mut s: *mut S, mut n: libc::c_ulong) {
    let mut storage = 0 as *mut u8;
    storage = 0 as *mut u8;
    if n == 0 {
        storage = { malloc(16) as *mut u8 };
    } else {
        storage = if n > 0 { malloc(n) as *mut u8 } else { 0 as *mut u8 };
    }
    Put((*s).hist.as_mut_ptr(), storage);
}
"#;

/// C4: a block WITH a statement stays outside G5.
const A_BLOCK_WITH_A_STATEMENT: &str = r#"
pub unsafe fn Use(mut s: *mut S, mut n: libc::c_ulong) {
    let mut storage = 0 as *mut u8;
    storage = {
        let k = n + 16;
        malloc(k) as *mut u8
    };
    Put((*s).hist.as_mut_ptr(), storage);
}
"#;

fn source(extra: &str) -> String {
    format!("{PRELUDE}{extra}")
}

#[test]
fn w6p_r603_a_local_admitted_field_separates_from_a_direct_field() {
    assert_eq!(
        verdict(
            &source(A_LOCAL_FIELD_BESIDE_A_DIRECT_FIELD),
            "Use",
            "Put",
            0,
            1
        ),
        Ok(CertificateKind::DistinctRoots),
        "`local`'s block came from the allocation into `c`; `direct` never receives a local"
    );
}

#[test]
fn w6p_r603_g5_a_block_around_an_allocator_is_that_allocation() {
    assert_eq!(
        verdict(&source(A_BLOCK_AROUND_AN_ALLOCATOR), "Use", "Put", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "every value of `storage` is null or a block `malloc` returned in this body"
    );
}

#[test]
fn w6p_r603_one_local_stored_into_two_fields_is_still_refused() {
    let verdict = verdict(&source(ONE_LOCAL_INTO_TWO_FIELDS), "Use", "Put", 0, 1);
    assert!(
        verdict.is_err(),
        "`local` and `direct` hold the same block: got {verdict:?}"
    );
}

#[test]
fn w6p_r603_an_offset_field_is_still_refused_beside_its_source() {
    let verdict = verdict(
        &source(AN_OFFSET_FIELD_BESIDE_ITS_SOURCE),
        "Use",
        "Put",
        0,
        1,
    );
    assert!(
        verdict.is_err(),
        "`buffer` points into `data`'s block: got {verdict:?}"
    );
}

#[test]
fn w6p_r603_a_self_offset_field_is_still_refused() {
    let verdict = verdict(&source(A_SELF_OFFSET_FIELD), "Use", "Put", 0, 1);
    assert!(
        verdict.is_err(),
        "an offset-admitted field never takes the different-fields clause: got {verdict:?}"
    );
}

#[test]
fn w6p_r603_g5_a_block_with_a_statement_is_not_an_allocation() {
    let verdict = verdict(&source(A_BLOCK_WITH_A_STATEMENT), "Use", "Put", 0, 1);
    assert!(
        verdict.is_err(),
        "G5 reads a statement-less block only: got {verdict:?}"
    );
}
