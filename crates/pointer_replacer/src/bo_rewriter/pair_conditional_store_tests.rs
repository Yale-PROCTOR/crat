//! wave-6p R485-4(e): a conditional whose every arm derives from ONE base is a
//! derivation of that base.
//!
//! Report 024 split `mixed-sources` into four questions and found the largest
//! is the C2Rust conditional store — `p = if c { a.offset(k) } else { a }` —
//! 112 of brotli's 309 shape-instances. The walk is the one written for the
//! allocator-field admission at `f065993a2`: a conditional is only as good as
//! its weakest arm, and every arm must name the same object.
//!
//! A null arm contributes nothing and is ignored: null is `Option::None` and
//! the local is then "null or a view of that base", which is exactly what the
//! root classifier already tolerates for an `AssignKind::Null` beside a
//! derivation.

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

/// Both arms walk within the caller's own buffer, so the cursor still names it
/// and is disjoint from the caller's stack scratch.
const ONE_BASE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn StoreBits(mut p: *mut u8, mut out: *mut i32) -> i32 {
    *out = *p as i32;
    1
}
pub unsafe fn emit(mut storage: *mut u8, mut n: i32) -> i32 {
    let mut scratch: i32 = 0;
    let mut p = if n > 0 { storage.offset(n as isize) } else { storage };
    StoreBits(p, &mut scratch)
}
"#;

#[test]
fn w6p_a_conditional_over_one_base_keeps_its_root() {
    assert_eq!(
        verdict(ONE_BASE, "emit", "StoreBits", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "every arm walks within `storage`, so the cursor is `storage`"
    );
}

/// A null arm contributes nothing: the local is null or a view of the base.
const ONE_BASE_WITH_A_NULL_ARM: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn StoreBits(mut p: *mut u8, mut out: *mut i32) -> i32 {
    *out = *p as i32;
    1
}
pub unsafe fn emit(mut storage: *mut u8, mut n: i32) -> i32 {
    let mut scratch: i32 = 0;
    let mut p = if n > 0 { storage.offset(n as isize) } else { 0 as *mut u8 };
    StoreBits(p, &mut scratch)
}
"#;

#[test]
fn w6p_a_null_arm_does_not_spoil_the_base() {
    assert_eq!(
        verdict(ONE_BASE_WITH_A_NULL_ARM, "emit", "StoreBits", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "null is None and names no object, so the other arm governs"
    );
}

/// Control (i): the arms derive from two DIFFERENT bases, so the local names
/// neither.
const TWO_BASES: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn StoreBits(mut p: *mut u8, mut out: *mut i32) -> i32 {
    *out = *p as i32;
    1
}
pub unsafe fn emit(mut storage: *mut u8, mut other: *mut u8, mut n: i32) -> i32 {
    let mut scratch: i32 = 0;
    let mut p = if n > 0 { storage.offset(n as isize) } else { other };
    StoreBits(p, &mut scratch)
}
"#;

#[test]
fn w6p_two_bases_in_a_conditional_leave_the_root_unknown() {
    assert_ne!(
        verdict(TWO_BASES, "emit", "StoreBits", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "two possible objects are not one object"
    );
}

/// Control (ii): one arm allocates. The local is then either a fresh block or
/// a view of the base — not one object — and the rule must refuse. This is the
/// arm the ALLOCATOR-FIELD admission accepts and this rule may not: there the
/// claim is "null or fresh", here it is "one named base".
const AN_ALLOCATING_ARM: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
pub unsafe fn StoreBits(mut p: *mut u8, mut out: *mut i32) -> i32 {
    *out = *p as i32;
    1
}
pub unsafe fn emit(mut storage: *mut u8, mut n: libc::c_ulong) -> i32 {
    let mut scratch: i32 = 0;
    let mut p = if n > 0 { malloc(n) as *mut u8 } else { storage };
    StoreBits(p, &mut scratch)
}
"#;

#[test]
fn w6p_an_allocating_arm_refuses_the_conditional() {
    assert_ne!(
        verdict(AN_ALLOCATING_ARM, "emit", "StoreBits", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "a fresh block or a view of the base is two objects, not one"
    );
}

/// Control (iii): an `if` with no `else` cannot be read as one base — the
/// implicit arm is whatever the local held before.
const NO_ELSE_ARM: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn StoreBits(mut p: *mut u8, mut out: *mut i32) -> i32 {
    *out = *p as i32;
    1
}
pub unsafe fn emit(mut storage: *mut u8, mut other: *mut u8, mut n: i32) -> i32 {
    let mut scratch: i32 = 0;
    let mut p = other;
    if n > 0 {
        p = storage.offset(n as isize);
    }
    StoreBits(p, &mut scratch)
}
"#;

#[test]
fn w6p_a_missing_else_arm_is_not_one_base() {
    assert_ne!(
        verdict(NO_ELSE_ARM, "emit", "StoreBits", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "the value the local already held is the other arm"
    );
}

/// The shape that is actually there. Report 024 read its own dump as "112
/// conditional DERIVATIONS"; the arm-level dump says **113 of brotli's
/// conditionals are `call` / `null`** — `p = if n > 0 { alloc(n) } else { null }`
/// — and only 12 are derivation/derivation. This is the allocating
/// conditional, and the claim for it is the one already ratified for the
/// allocator FIELD at `f065993a2`: null or a block the allocator returned is
/// still one fresh object.
const AN_ALLOCATING_CONDITIONAL: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
pub unsafe fn StoreBits(mut p: *mut u8, mut out: *mut u8) -> i32 {
    *out = *p;
    1
}
pub unsafe fn emit(mut storage: *mut u8, mut n: libc::c_ulong) -> i32 {
    let mut scratch = if n > 0 { malloc(n) as *mut u8 } else { 0 as *mut u8 };
    StoreBits(storage, scratch)
}
"#;

#[test]
fn w6p_an_allocating_conditional_is_one_fresh_object() {
    assert_eq!(
        verdict(AN_ALLOCATING_CONDITIONAL, "emit", "StoreBits", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "null or a block the allocator returned is a fresh object either way"
    );
}

/// Control: one arm is a caller's pointer, so the local is not fresh.
const A_CONDITIONAL_WITH_A_FOREIGN_ARM: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
pub unsafe fn StoreBits(mut p: *mut u8, mut out: *mut u8) -> i32 {
    *out = *p;
    1
}
pub unsafe fn emit(mut storage: *mut u8, mut lent: *mut u8, mut n: libc::c_ulong) -> i32 {
    let mut scratch = if n > 0 { malloc(n) as *mut u8 } else { lent };
    StoreBits(storage, scratch)
}
"#;

#[test]
fn w6p_a_foreign_arm_is_not_a_fresh_object() {
    assert_ne!(
        verdict(A_CONDITIONAL_WITH_A_FOREIGN_ARM, "emit", "StoreBits", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "a caller's pointer in one arm and the local is not one fresh block"
    );
}
