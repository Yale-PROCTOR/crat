//! wave-6a: the allocator-contract consumer (`decision/allocator_contract.rs`,
//! relay wave-6a/006, R409-1/3): brotli's `BrotliAllocate` / `BrotliFree` pair
//! is malloc/free-like by USER DECISION — a contract-rooted allocation local
//! is `Box<T>` / `Box<[T]>` (count from the size expression), released
//! exactly once through `BrotliFree(m, Box::into_raw(x) as *mut c_void)`;
//! NO implicit close (the global allocator must never drop memory of a
//! custom `free_func`) — a path that neither frees, transfers nor stores
//! the owner is the typed hold `contract-allocation:implicit-close`.
//!
//! Reduced from brotli `ClusterBlocksCommand` (`block_splitter_inc.h`): two
//! conditional allocations (`num_blocks > 0`), element writes, `memset`, a
//! lend to a local reader, the `BROTLI_FREE` pair (free + null store).

use super::wave6a_allocation_tests::{compact, emitted, reason_of};

const PRELUDE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn memset(s: *mut std::os::raw::c_void, c: i32, n: usize) -> *mut std::os::raw::c_void;
    fn exit(code: i32) -> !;
}
#[repr(C)]
pub struct MemoryManager {
    pub alloc_func: Option<unsafe extern "C" fn(*mut std::os::raw::c_void, usize) -> *mut std::os::raw::c_void>,
    pub free_func: Option<unsafe extern "C" fn(*mut std::os::raw::c_void, *mut std::os::raw::c_void)>,
    pub opaque: *mut std::os::raw::c_void,
}
pub unsafe extern "C" fn BrotliAllocate(mut m: *mut MemoryManager, mut n: usize) -> *mut std::os::raw::c_void {
    let mut result = ((*m).alloc_func).expect("non-null function pointer")((*m).opaque, n);
    if result.is_null() { exit(1 as i32); }
    return result;
}
pub unsafe extern "C" fn BrotliFree(mut m: *mut MemoryManager, mut p: *mut std::os::raw::c_void) {
    ((*m).free_func).expect("non-null function pointer")((*m).opaque, p);
}
pub unsafe extern "C" fn ReindexSymbols(mut symbols: *mut u32, mut n: usize) -> u32 {
    let mut i = 0 as usize;
    let mut max = 0 as u32;
    while i < n {
        if *symbols.offset(i as isize) > max { max = *symbols.offset(i as isize); }
        i = i.wrapping_add(1);
    }
    return max;
}
"#;

const CLUSTER: &str = r#"
pub unsafe extern "C" fn ClusterBlocksCommand(mut m: *mut MemoryManager, num_blocks: usize, mut split: *mut u32) {
    let mut histogram_symbols = if num_blocks > 0 as usize {
        BrotliAllocate(m, num_blocks.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    let mut block_lengths = if num_blocks > 0 as usize {
        BrotliAllocate(m, num_blocks.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    let mut i = 0 as usize;
    while i < num_blocks {
        *histogram_symbols.offset(i as isize) = i as u32;
        *block_lengths.offset(i as isize) = 0 as u32;
        i = i.wrapping_add(1);
    }
    i = 0 as usize;
    let mut max = 0 as u32;
    while i < num_blocks {
        *block_lengths.offset(i as isize) = (*block_lengths.offset(i as isize)).wrapping_add(1);
        if *histogram_symbols.offset(i as isize) > max { max = *histogram_symbols.offset(i as isize); }
        i = i.wrapping_add(1);
    }
    *split = max;
    BrotliFree(m, block_lengths as *mut std::os::raw::c_void);
    block_lengths = 0 as *mut u32;
    BrotliFree(m, histogram_symbols as *mut std::os::raw::c_void);
    histogram_symbols = 0 as *mut u32;
}
"#;

/// The ClusterBlocksCommand shape delivers: `Option<Box<[u32]>>` from the
/// conditional allocation (`None` on the else arm), element accesses through
/// the option, the `memset` lend as the R130 void bridge, the local reader
/// lent, `BrotliFree(m, x.map_or(null_mut(), |b| Box::into_raw(b) as ..))`
/// and the `BROTLI_FREE` null store as `= None`.
#[test]
fn w6a_ac_cluster_blocks_command_delivers_option_boxed_slices() {
    let out = emitted("ac-cluster", &format!("{PRELUDE}{CLUSTER}"));
    if let Ok(path) = std::env::var("W6A_DUMP_EMITTED") {
        std::fs::write(path, &out.source).expect("dump");
    }
    let text = compact(&out.source);
    for expected in [
        "letmuthistogram_symbols:Option<Box<[u32]>>=ifnum_blocks>0asusize{Some(Box::from_raw(core::ptr::slice_from_raw_parts_mut(BrotliAllocate(m,num_blocks.wrapping_mul(::core::mem::size_of::<u32>()))as*mutu32,(num_blocks)asusize)))}else{None};",
        "letmutblock_lengths:Option<Box<[u32]>>=ifnum_blocks>0asusize{Some(Box::from_raw(",
        "histogram_symbols.as_deref_mut().unwrap()[(i)asusize]=iasu32;",
        "block_lengths.as_deref_mut().unwrap()[(i)asusize]=block_lengths.as_deref().unwrap()[(i)asusize].wrapping_add(1);",
        "ifhistogram_symbols.as_deref().unwrap()[(i)asusize]>max{max=histogram_symbols.as_deref().unwrap()[(i)asusize];}",
        "BrotliFree(m,block_lengths.map_or(core::ptr::null_mut(),|b|Box::into_raw(b)as*mutstd::os::raw::c_void));",
        "block_lengths=None;",
        "BrotliFree(m,histogram_symbols.map_or(core::ptr::null_mut(),|b|Box::into_raw(b)as*mutstd::os::raw::c_void));",
        "histogram_symbols=None;",
    ] {
        assert!(
            text.contains(expected),
            "missing `{expected}`\n{}\n{:#?}",
            out.source,
            out.degradations
        );
    }
    assert!(!text.contains("drop("), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "ClusterBlocksCommand::histogram_symbols"),
        None,
        "{:#?}",
        out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "ClusterBlocksCommand::block_lengths"),
        None,
        "{:#?}",
        out.degradations
    );
    let receipts = &out.artifacts.allocator_contract_receipts;
    assert!(
        receipts.contains("allocator-contract:brotli-memory-manager/v1@2026-09-15"),
        "{receipts}"
    );
    assert!(
        receipts.contains("ClusterBlocksCommand::histogram_symbols\tadmitted\t"),
        "{receipts}"
    );
    assert_eq!(receipts.matches("waiver-drop").count(), 0, "{receipts}");
}

/// NO implicit close: an early `return` between the allocation and its
/// `BrotliFree` leaves a live owner for Rust to drop on that path — the
/// typed hold `contract-allocation:implicit-close`; the sibling without the
/// early return still delivers.
#[test]
fn w6a_ac_early_return_before_the_free_is_held_implicit_close() {
    let src = format!(
        "{PRELUDE}\
pub unsafe extern \"C\" fn early(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32;\n\
    if n > 4 as usize {{ return; }}\n\
    *syms.offset(0 as isize) = 1 as u32;\n\
    *split = *syms.offset(0 as isize);\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
}}\n\
pub unsafe extern \"C\" fn plain(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32;\n\
    *syms.offset(0 as isize) = 1 as u32;\n\
    *split = *syms.offset(0 as isize);\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
}}\n"
    );
    let out = emitted("ac-early-return", &src);
    let text = compact(&out.source);
    assert_eq!(
        reason_of(&out.degradations, "early::syms").as_deref(),
        Some("contract-allocation:implicit-close"),
        "{:#?}",
        out.degradations
    );
    assert!(
        out.artifacts
            .allocator_contract_receipts
            .contains("early::syms\theld\tcontract-allocation:implicit-close"),
        "{}",
        out.artifacts.allocator_contract_receipts
    );
    assert!(
        text.contains(
            "letmutsyms=BrotliAllocate(m,n.wrapping_mul(::core::mem::size_of::<u32>()))as*mutu32;"
        ),
        "{}",
        out.source
    );
    assert!(
        text.contains("letmutsyms:Box<[u32]>=Box::from_raw(core::ptr::slice_from_raw_parts_mut(BrotliAllocate(m,n.wrapping_mul(::core::mem::size_of::<u32>()))as*mutu32,(n)asusize));"),
        "{}\n{:#?}",
        out.source,
        out.degradations
    );
    assert!(
        text.contains("BrotliFree(m,Box::into_raw(syms)as*mutstd::os::raw::c_void);"),
        "{}",
        out.source
    );
    assert!(text.contains("syms[(0)asusize]=1asu32;"), "{}", out.source);
    assert!(text.contains("*split=syms[(0)asusize];"), "{}", out.source);
}

/// (i) `memset(x, 0, n)` follows the pinned libc table: without a `memset`
/// row the lend is unproven and the owner is a typed hold; with one (wave-4's
/// rows, relays 013 §4 / 014 — `batch-9-dry2` `4bc42b57`) the owner delivers
/// and the CAST argument takes the view (`zeroed.as_mut_ptr() as *mut
/// c_void`): the raw-boundary glue bridges a bare argument, not the operand
/// of a cast. (ii) A SLICE owner lent to a local reader whose formal converts
/// to `&[u32]` delivers through the seam's owner-view glue (R422-5):
/// `ReindexSymbols(&*lent, n)` — no `from_raw_parts` over the Box, no
/// fabricated extent at the call. (iii) The plain owner delivers. Each shape
/// sits in its own function: a typed hold holds its class.
#[test]
fn w6a_ac_memset_lend_follows_the_libc_table_and_the_slice_lend_takes_the_owner_view() {
    let src = format!(
        "{PRELUDE}\
pub unsafe extern \"C\" fn zeroing(mut m: *mut MemoryManager, n: usize) {{\n\
    let mut zeroed = BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32;\n\
    memset(zeroed as *mut std::os::raw::c_void, 0 as i32, n.wrapping_mul(::core::mem::size_of::<u32>()));\n\
    *zeroed.offset(0 as isize) = 1 as u32;\n\
    BrotliFree(m, zeroed as *mut std::os::raw::c_void);\n\
}}\n\
pub unsafe extern \"C\" fn lending(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut lent = BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32;\n\
    *lent.offset(0 as isize) = 1 as u32;\n\
    *split = ReindexSymbols(lent, n);\n\
    BrotliFree(m, lent as *mut std::os::raw::c_void);\n\
}}\n\
pub unsafe extern \"C\" fn keeping(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut kept = BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32;\n\
    *kept.offset(0 as isize) = 1 as u32;\n\
    *split = *kept.offset(0 as isize);\n\
    BrotliFree(m, kept as *mut std::os::raw::c_void);\n\
}}\n"
    );
    let out = emitted("ac-lends", &src);
    let text = compact(&out.source);
    let receipts = &out.artifacts.allocator_contract_receipts;
    // The libc table decides the `memset` lend; both outcomes are pinned.
    if receipts.contains("zeroing::zeroed\tadmitted\t") {
        assert!(
            text.contains("memset(zeroed.as_mut_ptr()as*mutstd::os::raw::c_void,"),
            "{}\n{receipts}",
            out.source
        );
        assert_eq!(
            reason_of(&out.degradations, "zeroing::zeroed"),
            None,
            "{:#?}",
            out.degradations
        );
    } else {
        assert!(
            receipts.contains(
                "zeroing::zeroed\theld\tcontract-allocation:use:call-argument-not-a-lend:memset("
            ),
            "{receipts}"
        );
        assert_eq!(
            reason_of(&out.degradations, "zeroing::zeroed").as_deref(),
            Some("contract-allocation:use"),
            "{:#?}",
            out.degradations
        );
    }
    assert!(receipts.contains("lending::lent\tadmitted\t"), "{receipts}");
    assert!(
        text.contains("*split=ReindexSymbols(&*lent,n);"),
        "{}\n{:#?}",
        out.source,
        out.degradations
    );
    assert!(
        text.contains("letmutlent:Box<[u32]>=Box::from_raw("),
        "{}\n{:#?}",
        out.source,
        out.degradations
    );
    assert!(receipts.contains("keeping::kept\tadmitted\t"), "{receipts}");
    assert!(
        text.contains("letmutkept:Box<[u32]>=Box::from_raw("),
        "{}\n{:#?}",
        out.source,
        out.degradations
    );
    assert!(
        text.contains(",Box::into_raw(kept)as*mutstd::os::raw::c_void);"),
        "{}",
        out.source
    );
    assert_eq!(
        reason_of(&out.degradations, "keeping::kept"),
        None,
        "{:#?}",
        out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "lending::lent"),
        None,
        "{:#?}",
        out.degradations
    );
}

/// An OPTIONAL owner (`Option<Box<[u32]>>`) lent to the local reader: the
/// owner view unwraps first — `&*syms.as_mut().unwrap()` is `&Box<[u32]>`,
/// which deref-coerces to the `&[u32]` formal at the call (R422-5). A
/// shared `.unwrap()` would move the owner out of its `Option`.
#[test]
fn w6a_ac_optional_owner_lent_takes_the_owner_view() {
    let src = format!(
        "{PRELUDE}\
pub unsafe extern \"C\" fn optional(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = if n > 0 as usize {{ BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32 }} else {{ 0 as *mut u32 }};\n\
    *syms.offset(0 as isize) = 7 as u32;\n\
    *split = ReindexSymbols(syms, n);\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
    syms = 0 as *mut u32;\n\
}}\n"
    );
    let out = emitted("ac-optional-lend", &src);
    let text = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    assert!(
        text.contains("*split=ReindexSymbols(&*syms.as_mut().unwrap(),n);"),
        "{}\n{:#?}",
        out.source,
        out.degradations
    );
    assert!(
        text.contains("letmutsyms:Option<Box<[u32]>>="),
        "{}",
        out.source
    );
    assert!(text.contains("syms=None;"), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "optional::syms"),
        None,
        "{:#?}",
        out.degradations
    );
}
