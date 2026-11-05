//! wave-6p R479-4: two root rules.
//!
//! (a) **The `FreshAlloc` field root.** A pointer field whose every store in the
//! program is a directly called named allocator holds, at any read, null or a
//! block the allocator returned. (b) **The null-literal side**: null is
//! `Option::None` and aliases nothing.
//!
//! Rule (a) is built NARROWER than addendum 479 ruled it — see report 022 §2
//! and the counterexample witness at the bottom of this file. The sound claim
//! is *same-base*: the block in `(*b).f` is disjoint from `*b` and from every
//! projection of it, because `*b` was live when the allocator wrote `f` and an
//! allocator never returns storage that overlaps a live object. Against an
//! unrelated root the claim fails, because a pointer derived from the field
//! AFTER the allocation can be passed in beside it.

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

/// brotli's shape: `(*mb).command_histograms` is stored only by `malloc`, so at
/// the call it holds a block disjoint from `*mb` — and therefore from
/// `&mut (*mb).literal_split`, a place inside `*mb`.
const FRESH_FIELD: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Split { pub num_types: i32, pub alphabet_size: i32 }
#[repr(C)]
pub struct MetaBlock { pub literal_split: Split, pub command_histograms: *mut u32 }
pub unsafe fn BuildHistograms(mut split: *mut Split, mut histograms: *mut u32) {
    (*split).num_types = 1;
    *histograms.offset(1) = 2;
}
pub unsafe fn BuildMetaBlock(mut mb: *mut MetaBlock, mut n: libc::c_ulong) {
    (*mb).command_histograms = malloc(n) as *mut u32;
    BuildHistograms(&mut (*mb).literal_split, (*mb).command_histograms);
}
"#;

#[test]
fn w6p_allocator_field_is_disjoint_from_its_own_container() {
    assert_eq!(
        verdict(FRESH_FIELD, "BuildMetaBlock", "BuildHistograms", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "a field written only by malloc cannot overlap the struct that holds it"
    );
}

/// Control (i): one store that is not an allocator — a copy of a caller's
/// pointer — and the field proves nothing.
const FIELD_WITH_A_FOREIGN_STORE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Split { pub num_types: i32, pub alphabet_size: i32 }
#[repr(C)]
pub struct MetaBlock { pub literal_split: Split, pub command_histograms: *mut u32 }
pub unsafe fn BuildHistograms(mut split: *mut Split, mut histograms: *mut u32) {
    (*split).num_types = 1;
    *histograms.offset(1) = 2;
}
pub unsafe fn adopt(mut mb: *mut MetaBlock, mut borrowed: *mut u32) {
    (*mb).command_histograms = borrowed;
}
pub unsafe fn BuildMetaBlock(mut mb: *mut MetaBlock, mut n: libc::c_ulong) {
    (*mb).command_histograms = malloc(n) as *mut u32;
    BuildHistograms(&mut (*mb).literal_split, (*mb).command_histograms);
}
"#;

#[test]
fn w6p_a_field_with_one_foreign_store_is_refused() {
    assert_ne!(
        verdict(
            FIELD_WITH_A_FOREIGN_STORE,
            "BuildMetaBlock",
            "BuildHistograms",
            0,
            1
        ),
        Ok(CertificateKind::DistinctRoots),
        "one store of a caller's pointer and the field names no fresh block"
    );
}

/// Control (ii): the allocator is reached through a function pointer, so the
/// closed world cannot name it (wave-6o 036's `bzalloc` lesson).
const FIELD_WITH_AN_INDIRECT_ALLOCATOR: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Split { pub num_types: i32, pub alphabet_size: i32 }
#[repr(C)]
pub struct MetaBlock { pub literal_split: Split, pub command_histograms: *mut u32 }
pub unsafe fn BuildHistograms(mut split: *mut Split, mut histograms: *mut u32) {
    (*split).num_types = 1;
    *histograms.offset(1) = 2;
}
pub unsafe fn BuildMetaBlock(
    mut mb: *mut MetaBlock,
    mut n: libc::c_ulong,
    mut bzalloc: Option<unsafe extern "C" fn(libc::c_ulong) -> *mut libc::c_void>,
) {
    (*mb).command_histograms = (bzalloc.unwrap())(n) as *mut u32;
    BuildHistograms(&mut (*mb).literal_split, (*mb).command_histograms);
}
"#;

#[test]
fn w6p_an_indirect_allocator_does_not_admit_the_field() {
    assert_ne!(
        verdict(
            FIELD_WITH_AN_INDIRECT_ALLOCATOR,
            "BuildMetaBlock",
            "BuildHistograms",
            0,
            1
        ),
        Ok(CertificateKind::DistinctRoots),
        "a directly called NAMED allocator is what the rule rests on"
    );
}

/// Control (iii), the narrowing, and the counterexample to addendum 479 as
/// ruled: the field's block stands beside a pointer PARAMETER of the caller —
/// a known root, and not the base. The rule must refuse, because the caller's
/// caller may well have passed `(*b).items` itself:
///
/// ```text
/// outer(b) { b->items = malloc(n); caller(b, b->items); }
/// ```
///
/// `q` and `(*b).items` are then one block. Nothing in the allocator argument
/// separates them, which is why (a) certifies against the BASE alone.
const FIELD_BESIDE_A_KNOWN_STRANGER: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
#[repr(C)]
pub struct Bag { pub items: *mut u32 }
pub unsafe fn touch(mut q: *mut u32, mut items: *mut u32) {
    *q = 1;
    *items.offset(1) = 2;
}
pub unsafe fn caller(mut b: *mut Bag, mut q: *mut u32) {
    touch(q, (*b).items);
}
pub unsafe fn outer(mut b: *mut Bag, mut n: libc::c_ulong) {
    (*b).items = malloc(n) as *mut u32;
    caller(b, (*b).items);
}
"#;

#[test]
fn w6p_the_field_is_not_disjoint_from_a_known_stranger() {
    // Non-vacuous: the field IS admitted here — its only store is `malloc` —
    // so the refusal is the same-base guard and nothing else.
    assert_eq!(
        verdict(FIELD_BESIDE_A_KNOWN_STRANGER, "outer", "caller", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "the admitted field is disjoint from its own base"
    );
    assert_ne!(
        verdict(FIELD_BESIDE_A_KNOWN_STRANGER, "caller", "touch", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "a known root that is NOT the base proves nothing about the block"
    );
}

/// (b) R479-4b: a null-literal operand aliases nothing (null = `None`, R29).
const NULL_OPERAND: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn binn_read(mut p: *mut libc::c_uchar, mut value: *mut libc::c_uchar) -> i32 {
    if value.is_null() { return 0; }
    *value = *p;
    1
}
pub unsafe fn caller(mut buf: *mut libc::c_uchar) -> i32 {
    binn_read(buf, 0 as *mut libc::c_uchar)
}
"#;

#[test]
fn w6p_a_null_literal_operand_aliases_nothing() {
    assert_eq!(
        verdict(NULL_OPERAND, "caller", "binn_read", 0, 1),
        Ok(CertificateKind::NullOperand),
        "null is None and overlaps no object"
    );
}

/// Control for (b): the same call with a real pointer sibling is unproved.
const NON_NULL_SIBLING: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
pub unsafe fn binn_read(mut p: *mut libc::c_uchar, mut value: *mut libc::c_uchar) -> i32 {
    if value.is_null() { return 0; }
    *value = *p;
    1
}
pub unsafe fn caller(mut buf: *mut libc::c_uchar, mut out: *mut libc::c_uchar) -> i32 {
    binn_read(buf, out)
}
"#;

#[test]
fn w6p_a_non_null_raw_sibling_is_still_unproved() {
    assert_ne!(
        verdict(NON_NULL_SIBLING, "caller", "binn_read", 0, 1),
        Ok(CertificateKind::NullOperand),
        "two real pointers are not separated by the null rule"
    );
}

/// The C2Rust store idiom: `f = if n > 0 { alloc(n) } else { null }`. Every arm
/// is an allocation or null, so the field still holds "null or a block the
/// allocator returned" — brotli writes `(*mb).command_histograms` exactly this
/// way (lib.rs:489722).
const FIELD_STORED_CONDITIONALLY: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Split { pub num_types: i32, pub alphabet_size: i32 }
#[repr(C)]
pub struct MetaBlock { pub literal_split: Split, pub command_histograms: *mut u32 }
pub unsafe fn BuildHistograms(mut split: *mut Split, mut histograms: *mut u32) {
    (*split).num_types = 1;
    *histograms.offset(1) = 2;
}
pub unsafe fn BuildMetaBlock(mut mb: *mut MetaBlock, mut n: libc::c_ulong) {
    (*mb).command_histograms =
        if n > 0 { malloc(n) as *mut u32 } else { 0 as *mut u32 };
    BuildHistograms(&mut (*mb).literal_split, (*mb).command_histograms);
}
"#;

#[test]
fn w6p_a_conditional_allocation_still_admits_the_field() {
    assert_eq!(
        verdict(
            FIELD_STORED_CONDITIONALLY,
            "BuildMetaBlock",
            "BuildHistograms",
            0,
            1
        ),
        Ok(CertificateKind::DistinctRoots),
        "every arm an allocation or null is still null-or-fresh"
    );
}

/// Control: one arm of the conditional is a caller's pointer, and the field is
/// refused again.
const FIELD_STORED_CONDITIONALLY_WITH_A_FOREIGN_ARM: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Split { pub num_types: i32, pub alphabet_size: i32 }
#[repr(C)]
pub struct MetaBlock { pub literal_split: Split, pub command_histograms: *mut u32 }
pub unsafe fn BuildHistograms(mut split: *mut Split, mut histograms: *mut u32) {
    (*split).num_types = 1;
    *histograms.offset(1) = 2;
}
pub unsafe fn BuildMetaBlock(mut mb: *mut MetaBlock, mut n: libc::c_ulong, mut lent: *mut u32) {
    (*mb).command_histograms =
        if n > 0 { malloc(n) as *mut u32 } else { lent };
    BuildHistograms(&mut (*mb).literal_split, (*mb).command_histograms);
}
"#;

#[test]
fn w6p_a_foreign_arm_refuses_the_conditional_store() {
    assert_ne!(
        verdict(
            FIELD_STORED_CONDITIONALLY_WITH_A_FOREIGN_ARM,
            "BuildMetaBlock",
            "BuildHistograms",
            0,
            1
        ),
        Ok(CertificateKind::DistinctRoots),
        "one arm holding a caller's pointer and the field proves nothing"
    );
}

/// brotli's real shape: the field is written by `BrotliAllocate`, a wrapper
/// that allocates through `(*m).alloc_func` and is therefore admitted under
/// R409-1's CONTRACT, not proven. The certificate must say so by name.
const FIELD_STORED_BY_A_CONTRACT_ALLOCATOR: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Split { pub num_types: i32, pub alphabet_size: i32 }
#[repr(C)]
pub struct MemoryManager {
    pub alloc_func: Option<unsafe extern "C" fn(libc::c_ulong) -> *mut libc::c_void>,
}
#[repr(C)]
pub struct MetaBlock { pub literal_split: Split, pub command_histograms: *mut u32 }
pub unsafe fn BrotliAllocate(mut m: *mut MemoryManager, mut n: libc::c_ulong)
    -> *mut libc::c_void {
    ((*m).alloc_func).expect("non-null function pointer")(n)
}
extern "C" { fn malloc(n: libc::c_ulong) -> *mut libc::c_void; }
pub unsafe extern "C" fn BrotliDefaultAllocFunc(mut n: libc::c_ulong) -> *mut libc::c_void {
    malloc(n)
}
#[no_mangle]
pub unsafe extern "C" fn BrotliInitMemoryManager(
    mut m: *mut MemoryManager,
    mut alloc: Option<unsafe extern "C" fn(libc::c_ulong) -> *mut libc::c_void>,
) {
    // One resolved allocator store and one the closed world cannot see: the
    // field is an allocator UNDER the contract, exactly as brotli's is.
    if alloc.is_none() {
        (*m).alloc_func = Some(BrotliDefaultAllocFunc);
    } else {
        (*m).alloc_func = alloc;
    }
}
pub unsafe fn BuildHistograms(mut split: *mut Split, mut histograms: *mut u32) {
    (*split).num_types = 1;
    *histograms.offset(1) = 2;
}
pub unsafe fn BuildMetaBlock(
    mut mb: *mut MetaBlock,
    mut m: *mut MemoryManager,
    mut n: libc::c_ulong,
) {
    (*mb).command_histograms = BrotliAllocate(m, n) as *mut u32;
    BuildHistograms(&mut (*mb).literal_split, (*mb).command_histograms);
}
"#;

#[test]
fn w6p_a_contract_backed_allocator_certifies_under_its_contract() {
    assert_eq!(
        verdict(
            FIELD_STORED_BY_A_CONTRACT_ALLOCATOR,
            "BuildMetaBlock",
            "BuildHistograms",
            0,
            1
        ),
        Ok(CertificateKind::DistinctRootsUnderContract),
        "an allocator admitted under R409-1 never yields a proven receipt"
    );
}
