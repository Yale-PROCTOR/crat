//! wave-6p R492-3: two shared reads need no disjointness certificate.
//!
//! `&T × &T` is the one aliasing question Rust answers for us — two shared
//! borrows of the same place are legal — so a pair whose peer formals are both
//! **model-shared reads** needs nothing from this lane. wave-6k 038 stated the
//! rule and measured it; R217-2(a) puts the build with the certificate's owner,
//! which is here.
//!
//! "Model-shared read" is a conjunction, and each half is a separate refusal:
//! the formal is `*const` in the INPUT, the mutability analysis says nothing
//! writes through it, and the callee's body takes no mutable reborrow of it
//! (`&mut *p`, `p.as_mut_ptr()`, any `&mut` derivation of that root). One
//! mutable reborrow anywhere in the callee kills the licence for the pair.
//!
//! The fact is per PAIR, never per site: it is read off the callee's own
//! signature and body, so every call site of that callee gets the same answer.

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

/// brotli's shape: `StoreDataWithHuffmanCodes(…, cmd_bits, dist_depth, …)` —
/// two `*const` tables, both only read.
const TWO_SHARED_READS: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn StoreDataWithHuffmanCodes(
    mut cmd_bits: *const u16,
    mut dist_depth: *const u8,
    mut n: i32,
) -> i32 {
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        total += *cmd_bits.offset(i as isize) as i32;
        total += *dist_depth.offset(i as isize) as i32;
        i += 1;
    }
    total
}
pub unsafe fn emit(mut bits: *const u16, mut depth: *const u8, mut n: i32) -> i32 {
    StoreDataWithHuffmanCodes(bits, depth, n)
}
"#;

#[test]
fn w6p_two_shared_reads_need_no_certificate() {
    assert_eq!(
        verdict(TWO_SHARED_READS, "emit", "StoreDataWithHuffmanCodes", 0, 1),
        Ok(CertificateKind::ReadReadShared),
        "two shared borrows of one place are legal Rust, so the pair is free"
    );
}

/// Control (i): one formal is `*mut` in the input. The model may still read it
/// only, but the input's own type is half the conjunction and it fails here.
const ONE_MUT_FORMAL: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn StoreDataWithHuffmanCodes(
    mut cmd_bits: *const u16,
    mut dist_depth: *mut u8,
    mut n: i32,
) -> i32 {
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        total += *cmd_bits.offset(i as isize) as i32;
        *dist_depth.offset(i as isize) = 1;
        i += 1;
    }
    total
}
pub unsafe fn emit(mut bits: *const u16, mut depth: *mut u8, mut n: i32) -> i32 {
    StoreDataWithHuffmanCodes(bits, depth, n)
}
"#;

#[test]
fn w6p_a_mut_formal_is_not_a_shared_read() {
    assert_ne!(
        verdict(ONE_MUT_FORMAL, "emit", "StoreDataWithHuffmanCodes", 0, 1),
        Ok(CertificateKind::ReadReadShared),
        "a written formal is not a shared read"
    );
}

/// Control (ii), the guard the relay named: the body takes a MUTABLE REBORROW
/// of one formal. Nothing is written through it here, so the mutability
/// analysis alone would not refuse — the reborrow itself must.
const A_MUTABLE_REBORROW: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn peek(mut p: *mut u8) -> u8 { *p }
pub unsafe fn StoreDataWithHuffmanCodes(
    mut cmd_bits: *const u16,
    mut dist_depth: *const u8,
    mut n: i32,
) -> i32 {
    let mut total: i32 = 0;
    total += peek(dist_depth as *mut u8) as i32;
    let mut i: i32 = 0;
    while i < n {
        total += *cmd_bits.offset(i as isize) as i32;
        i += 1;
    }
    total
}
pub unsafe fn emit(mut bits: *const u16, mut depth: *const u8, mut n: i32) -> i32 {
    StoreDataWithHuffmanCodes(bits, depth, n)
}
"#;

#[test]
fn w6p_a_mutable_reborrow_kills_the_licence() {
    assert_ne!(
        verdict(
            A_MUTABLE_REBORROW,
            "emit",
            "StoreDataWithHuffmanCodes",
            0,
            1
        ),
        Ok(CertificateKind::ReadReadShared),
        "a mutable reborrow anywhere in the callee is a write the pair cannot assume away"
    );
}

/// Control (iii): the licence is shared-with-shared BOTH ways. A shared read
/// beside a formal the model writes falls back to the ordinary certificates,
/// and must not take this receipt.
const SHARED_BESIDE_A_WRITTEN_FORMAL: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn StoreDataWithHuffmanCodes(
    mut cmd_bits: *const u16,
    mut out: *mut u8,
    mut n: i32,
) -> i32 {
    *out = *cmd_bits as u8;
    n
}
pub unsafe fn emit(mut bits: *const u16, mut n: i32) -> i32 {
    let mut scratch: u8 = 0;
    StoreDataWithHuffmanCodes(bits, &mut scratch, n)
}
"#;

#[test]
fn w6p_shared_beside_a_written_formal_falls_back() {
    let outcome = verdict(
        SHARED_BESIDE_A_WRITTEN_FORMAL,
        "emit",
        "StoreDataWithHuffmanCodes",
        0,
        1,
    );
    assert_ne!(
        outcome,
        Ok(CertificateKind::ReadReadShared),
        "one written side means the ordinary certificates decide: {outcome:?}"
    );
    assert!(
        outcome.is_ok(),
        "and here they do — a fresh stack address beside an entry pointer: {outcome:?}"
    );
}

/// Control (i′), isolating the `*const` conjunct: a `*mut` formal that nothing
/// ever writes through. The mutability analysis is content — it is in
/// `immutable_formals` — so the INPUT's own type is the only thing refusing it,
/// and fault F47 (dropping that conjunct) bites here and nowhere else.
///
/// It matters because the input type is what the emitted program must honour:
/// a `*mut` formal may still be re-typed `&mut` by another lane's decision, and
/// a licence taken on today's read-only body would outlive its premise.
const A_MUT_FORMAL_NEVER_WRITTEN: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn StoreDataWithHuffmanCodes(
    mut cmd_bits: *const u16,
    mut dist_depth: *mut u8,
    mut n: i32,
) -> i32 {
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        total += *cmd_bits.offset(i as isize) as i32;
        total += *dist_depth.offset(i as isize) as i32;
        i += 1;
    }
    total
}
pub unsafe fn emit(mut bits: *const u16, mut depth: *mut u8, mut n: i32) -> i32 {
    StoreDataWithHuffmanCodes(bits, depth, n)
}
"#;

#[test]
fn w6p_a_mut_formal_never_written_is_still_not_a_shared_read() {
    assert_ne!(
        verdict(
            A_MUT_FORMAL_NEVER_WRITTEN,
            "emit",
            "StoreDataWithHuffmanCodes",
            0,
            1
        ),
        Ok(CertificateKind::ReadReadShared),
        "`*const` in the input is a conjunct in its own right"
    );
}
