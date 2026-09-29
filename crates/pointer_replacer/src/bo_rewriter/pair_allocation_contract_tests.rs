//! wave-6p R645-10 (056a STOP 2): allocation identity resting on R409-1's
//! allocator CONTRACT is receipted as such, so the census counts it apart from
//! an in-body allocator call. A receipt refinement: the three producers of
//! `allocation-identity` — (f)'s local form, (f′)'s caller step, and the
//! allocated-here class — certify exactly what they did; only the kind names
//! the contract when the block came from a contract-backed allocator.
//! Their proven witnesses stand in `pair_allocation_identity_tests.rs` and
//! `pair_allocated_here_tests.rs`.

use super::decision::pair_disjointness::{CertificateKind, PairDisjointnessIndex, Unproved};

fn verdict(src: &str, caller: &str, callee: &str) -> Result<CertificateKind, Unproved> {
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
        out = Some(index.certify_recorded(function(caller), function(callee), 0, 1));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

/// brotli's allocator: `BrotliAllocate` allocates through `(*m).alloc_func`,
/// which `BrotliInitMemoryManager` sets from a caller-supplied pointer the
/// closed world cannot see — an allocator UNDER the contract. `Use2` takes two
/// `u32` pointers, so no type rule separates anything below.
const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
#[repr(C)]
pub struct MemoryManager {
    pub alloc_func: Option<unsafe extern "C" fn(libc::c_ulong) -> *mut libc::c_void>,
}
#[repr(C)]
pub struct Split { pub map: *mut u32, pub n: libc::c_ulong }
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
    if alloc.is_none() {
        (*m).alloc_func = Some(BrotliDefaultAllocFunc);
    } else {
        (*m).alloc_func = alloc;
    }
}
pub unsafe fn Use2(mut x: *mut u32, mut y: *mut u32) {
    *x = 1;
    *y = 2;
}
"#;

/// W1: (f)'s local form — `BrotliBuildMetaBlock`'s store through the contract
/// allocator, then the call beside the entry `x`.
const LOCAL_FORM: &str = r#"
pub unsafe fn Build(mut m: *mut MemoryManager, mut x: *mut u32, mut mb: *mut Split) {
    (*mb).map = BrotliAllocate(m, 16) as *mut u32;
    Use2(x, (*mb).map);
}
"#;

/// W2: (f′) — the caller's callee stores through the contract allocator.
const CALLER_STEP: &str = r#"
pub unsafe fn Fill(mut m: *mut MemoryManager, mut mb: *mut Split) {
    (*mb).map = BrotliAllocate(m, 16) as *mut u32;
}
pub unsafe fn Store(mut x: *mut u32, mut mb: *mut Split) {
    Use2(x, (*mb).map);
}
pub unsafe fn Write(mut m: *mut MemoryManager, mut x: *mut u32) {
    let mut s = Split { map: 0 as *mut u32, n: 0 };
    Fill(m, &mut s);
    Store(x, &mut s);
}
"#;

/// W3: the allocated-here class — `BROTLI_ENSURE_CAPACITY`'s growth through
/// the contract allocator.
const GROWN: &str = r#"
pub unsafe fn Cluster(mut m: *mut MemoryManager, mut out: *mut u32, mut n: usize) {
    let mut pairs: *mut u32 = BrotliAllocate(m, 8) as *mut u32;
    if n > 4 {
        let mut new_array: *mut u32 = 0 as *mut u32;
        new_array = BrotliAllocate(m, 64) as *mut u32;
        pairs = new_array;
    }
    Use2(out, pairs);
}
"#;

fn source(extra: &str) -> String {
    format!("{PRELUDE}{extra}")
}

#[test]
fn w6p_r645_the_local_form_names_the_contract() {
    assert_eq!(
        verdict(&source(LOCAL_FORM), "Build", "Use2"),
        Ok(CertificateKind::AllocationIdentityUnderContract)
    );
}

#[test]
fn w6p_r645_the_caller_step_names_the_contract() {
    assert_eq!(
        verdict(&source(CALLER_STEP), "Store", "Use2"),
        Ok(CertificateKind::AllocationIdentityUnderContract)
    );
}

#[test]
fn w6p_r645_the_allocated_here_class_names_the_contract() {
    assert_eq!(
        verdict(&source(GROWN), "Cluster", "Use2"),
        Ok(CertificateKind::AllocationIdentityUnderContract)
    );
}

#[test]
fn w6p_r645_the_receipt_key() {
    assert_eq!(
        CertificateKind::AllocationIdentityUnderContract.key(),
        "pair-disjoint:allocation-identity:allocator-contract"
    );
    assert_eq!(
        CertificateKind::AllocationIdentity.key(),
        "pair-disjoint:allocation-identity"
    );
}
