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

/// **Build 2 (relay wave-6a/018): the assignment receiver and the re-seated
/// owner** — brotli's `BROTLI_ENSURE_CAPACITY` idiom, the 55 rows of report
/// 008's market. The receiver is declared empty and allocated into further
/// down (`let mut new_array = 0 as *mut T; new_array = if n > 0 {
/// BrotliAllocate(..) } else { null };`), the owner it replaces is freed,
/// nulled and RE-SEATED from it (`all_histograms = new_array`), and the
/// re-seated generation is freed again at the end. The owner's generations
/// are simulated (Dead → create → Live → release → Dead) with every block it
/// touches balanced, so the moves need no edit at all and each free is the
/// contract transfer.
#[test]
fn w6a_ac_ensure_capacity_receiver_and_reseat_deliver() {
    let src = format!(
        "{PRELUDE}\
pub unsafe extern \"C\" fn cluster(mut m: *mut MemoryManager, mut n: usize, mut split: *mut u32) {{\n\
    let mut all_histograms = if n > 0 as usize {{ BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32 }} else {{ 0 as *mut u32 }};\n\
    let mut capacity = n;\n\
    if capacity < n.wrapping_add(4 as usize) {{\n\
        let mut new_size = capacity.wrapping_add(4 as usize);\n\
        let mut new_array = 0 as *mut u32;\n\
        new_array = if new_size > 0 as usize {{ BrotliAllocate(m, new_size.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32 }} else {{ 0 as *mut u32 }};\n\
        BrotliFree(m, all_histograms as *mut std::os::raw::c_void);\n\
        all_histograms = 0 as *mut u32;\n\
        all_histograms = new_array;\n\
        capacity = new_size;\n\
    }}\n\
    *all_histograms.offset(0 as isize) = 3 as u32;\n\
    *split = *all_histograms.offset(0 as isize);\n\
    BrotliFree(m, all_histograms as *mut std::os::raw::c_void);\n\
    all_histograms = 0 as *mut u32;\n\
}}\n"
    );
    let out = emitted("ac-ensure-capacity", &src);
    if let Ok(path) = std::env::var("W6A_DUMP_EMITTED") {
        std::fs::write(path, &out.source).expect("dump");
    }
    let text = compact(&out.source);
    let receipts = &out.artifacts.allocator_contract_receipts;
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    for expected in [
        "letmutall_histograms:Option<Box<[u32]>>=ifn>0asusize{Some(Box::from_raw(",
        "letmutnew_array:Option<Box<[u32]>>=None;",
        "new_array=ifnew_size>0asusize{Some(Box::from_raw(",
        "BrotliFree(m,all_histograms.map_or(core::ptr::null_mut(),|b|Box::into_raw(b)as*mutstd::os::raw::c_void));",
        "all_histograms=None;",
        "all_histograms=new_array;",
        "all_histograms.as_deref_mut().unwrap()[(0)asusize]=3asu32;",
        "*split=all_histograms.as_deref().unwrap()[(0)asusize];",
    ] {
        assert!(
            text.contains(expected),
            "missing `{expected}`\n{}\n{receipts}",
            out.source
        );
    }
    assert!(
        receipts.contains("generations=1 moves_in=1 frees=2"),
        "{receipts}"
    );
    assert!(
        receipts.contains("cluster::new_array\tadmitted\t"),
        "{receipts}"
    );
    assert_eq!(
        reason_of(&out.degradations, "cluster::all_histograms"),
        None,
        "{:#?}",
        out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "cluster::new_array"),
        None,
        "{:#?}",
        out.degradations
    );
}

/// **Build 2's generation state machine, one control per gate.** Each shape
/// sits in its own function and names the exact receipt, so exactly one hold
/// answers for exactly one gate: (1) a generation still live at the body's
/// end, (2) a block that does not leave the owner as it found it — here the
/// conditional allocation assigned inside the branch, (3) a read of the
/// owner after its release, (4) a second allocation over a live generation
/// (R434-4 §2 admitted this and the admission is WITHDRAWN — report 019 §3),
/// (5) a release before any generation exists, (6) the owner copied into a
/// local that is not itself a contract owner — a second owner this rule
/// cannot follow.
/// (5) and (6) are UB-free-input shapes only in the trivial sense; they hold
/// fail-closed either way.
#[test]
fn w6a_ac_generation_gates_each_hold_their_own_class() {
    let alloc = "BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32";
    let src = format!(
        "{PRELUDE}\
pub unsafe extern \"C\" fn live_at_exit(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = {alloc};\n\
    *syms.offset(0 as isize) = 1 as u32;\n\
    *split = *syms.offset(0 as isize);\n\
}}\n\
pub unsafe extern \"C\" fn unbalanced(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = 0 as *mut u32;\n\
    if n > 4 as usize {{ syms = {alloc}; }}\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
}}\n\
pub unsafe extern \"C\" fn read_after_release(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = {alloc};\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
    *split = *syms.offset(0 as isize);\n\
}}\n\
pub unsafe extern \"C\" fn reseat_over_live(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = {alloc};\n\
    syms = {alloc};\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
}}\n\
pub unsafe extern \"C\" fn release_first(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = 0 as *mut u32;\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
    syms = {alloc};\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
}}\n\
pub unsafe extern \"C\" fn plain_alias(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut copy = 0 as *mut u32;\n\
    copy = split;\n\
    *copy.offset(0 as isize) = 5 as u32;\n\
}}\n\
pub unsafe extern \"C\" fn copied_into_plain_local(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = {alloc};\n\
    let mut alias = 0 as *mut u32;\n\
    alias = syms;\n\
    *split = *alias.offset(0 as isize);\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
}}\n"
    );
    let out = emitted("ac-generation-gates", &src);
    let receipts = &out.artifacts.allocator_contract_receipts;
    for (subject, detail) in [
        (
            "live_at_exit::syms",
            "contract-allocation:implicit-close:live-at-exit",
        ),
        (
            "unbalanced::syms",
            "contract-allocation:implicit-close:block-unbalanced",
        ),
        (
            "read_after_release::syms",
            "contract-allocation:use:read-while-empty",
        ),
        (
            "release_first::syms",
            "contract-allocation:implicit-close:release-without-generation",
        ),
        (
            "copied_into_plain_local::syms",
            "contract-allocation:use:copied-into-local",
        ),
    ] {
        assert!(
            receipts.contains(&format!("{subject}\theld\t{detail}")),
            "missing `{subject} held {detail}`\n{receipts}"
        );
        assert!(
            reason_of(&out.degradations, subject).is_some(),
            "{subject} not degraded\n{:#?}",
            out.degradations
        );
    }
    // (4) The re-seat over a live generation: ADMITTED (R434-4 §2 under
    // R443-1), whose implicit close is well-defined because the emitted crate
    // declares the System allocator — report 020's probe measured the same
    // fixture UB without the declaration and clean with it. The control keeps
    // the shape and asserts the waiver's receipt.
    assert!(
        receipts.contains("reseat_over_live::syms\tadmitted\twaiver-drop(overwrite) site="),
        "{receipts}"
    );
    assert!(
        !receipts.contains("reseat_over_live::syms\theld\t"),
        "{receipts}"
    );
    // (7) A local assigned from something that is not a contract owner is
    // not a generation at all: the rule leaves it alone — no receipt, no
    // degradation. Every program with a contract in it holds locals like
    // this one, and the shared Option/alias families emit them.
    assert!(
        !receipts.contains("plain_alias::copy"),
        "the plain alias is not the contract's\n{receipts}"
    );
    assert_eq!(
        reason_of(&out.degradations, "plain_alias::copy")
            .filter(|r| r.starts_with("contract-allocation")),
        None,
        "{:#?}",
        out.degradations
    );
    // Exactly ONE function of this fixture delivers: `reseat_over_live`, under
    // §2's waiver. Every other gate's owner keeps its typed hold, which the
    // per-subject assertions above already name.
    assert_eq!(
        compact(&out.source).matches("Box<[u32]>").count(),
        1,
        "{}",
        out.source
    );
}

/// **The containment the batch-9 census measured** (report 014 claim 4,
/// relay wave-6a/020 (ii)): when the manager the contract allocates through is
/// RAW in the caller — brotli's shape at 26 receivers — the C arm bridges it
/// AT THE ARGUMENT, `BrotliAllocate(&mut *m, ..)`, and that one-byte edit sits
/// INSIDE the initializer this rule rewrites. A construction rendered as ONE
/// replacement of the allocation CONTAINS it, and the signature-class layer
/// holds both classes with `cross-class-interval-collision`. Rendered as two
/// insertions at the allocation's boundaries, this rule claims no interval of
/// the call at all: the bridge renders where it was planned and the collision
/// term is gone from the hold.
///
/// The fixture sources its manager from a foreign call, which is the only
/// shape that keeps a manager raw without arithmetic; that leaves this class
/// with wave-6l's own `return-not-adapted` subject, so the assertion is the
/// hold's TERMS, not the delivery. The idiom that delivers is the
/// ensure-capacity witness above, whose bytes the insertions reproduce
/// exactly.
#[test]
fn w6a_ac_the_construction_contains_no_edit_of_the_allocator_call() {
    let src = format!(
        "{PRELUDE}\
extern \"C\" {{\n\
    fn get_manager() -> *mut MemoryManager;\n\
}}\n\
pub unsafe extern \"C\" fn raw_manager(mut n: usize, mut split: *mut u32) {{\n\
    let mut m = get_manager();\n\
    let mut syms = if n > 0 as usize {{ BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32 }} else {{ 0 as *mut u32 }};\n\
    *syms.offset(0 as isize) = 3 as u32;\n\
    *split = *syms.offset(0 as isize);\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
    syms = 0 as *mut u32;\n\
}}\n"
    );
    let out = emitted("ac-raw-manager", &src);
    let text = compact(&out.source);
    // The degradation of a class-held subject carries its MIR suffix, and the
    // terms live in the reason's detail, so the hold is read whole.
    let hold = out
        .degradations
        .iter()
        .filter(|d| d.subject.starts_with("raw_manager::syms"))
        .map(|d| format!("{:?}", d.reason))
        .collect::<Vec<_>>()
        .join(";");
    assert!(
        !hold.contains("cross-class-interval-collision"),
        "this rule must claim no interval of the allocator call; hold = {hold}\n{}",
        out.source
    );
    if hold.is_empty() {
        // Wherever the class is otherwise clean, the construction is spelled
        // AROUND the call and the call's own text is untouched.
        assert!(
            text.contains("Some(Box::from_raw(core::ptr::slice_from_raw_parts_mut(BrotliAllocate("),
            "{}",
            out.source
        );
    } else {
        // On this lane's head the residue is wave-6l's `return-not-adapted`
        // on the foreign call's receiver; the bridge the C arm planned inside
        // the allocator call still renders, which is the half a containing
        // replacement used to lose.
        assert!(
            text.contains("BrotliAllocate(&mut*m,"),
            "the C arm's bridge must render at the argument; hold = {hold}\n{}",
            out.source
        );
    }
    // The rule itself admitted the subject: the residue is other families'.
    assert!(
        out.artifacts
            .allocator_contract_receipts
            .contains("raw_manager::syms\tadmitted\t"),
        "{}",
        out.artifacts.allocator_contract_receipts
    );
}

/// **The libc row** (R434-4 §3, report 017's market): libc's own allocator
/// contract — `malloc` / `calloc` / `strdup` released by `free` — read by the
/// same generation machine as brotli's. `realloc` is deliberately absent from
/// the table: it releases one generation and creates another in one call.
///
/// `strdup`'s extent is the contract's POSTCONDITION (§1): the block is a
/// NUL-terminated copy, so the construction binds it and measures IT — the
/// count never mentions the allocator's argument, so no other family's
/// rendering of that argument can make it stale, and no length is fabricated.
const LIBC_OWNERS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types)]
extern "C" {
    fn malloc(size: std::os::raw::c_ulong) -> *mut core::ffi::c_void;
    fn calloc(n: std::os::raw::c_ulong, size: std::os::raw::c_ulong) -> *mut core::ffi::c_void;
    fn strdup(s: *const std::os::raw::c_char) -> *mut std::os::raw::c_char;
    fn free(ptr: *mut core::ffi::c_void);
    fn strcmp(a: *const std::os::raw::c_char, b: *const std::os::raw::c_char) -> i32;
}
pub unsafe extern "C" fn counted(mut n: usize, mut out: *mut u32) -> i32 {
    let mut buf = malloc((n as std::os::raw::c_ulong).wrapping_mul(::std::mem::size_of::<u32>() as std::os::raw::c_ulong)) as *mut u32;
    if buf.is_null() {
        return 0 as i32;
    }
    *buf.offset(0 as isize) = 7 as u32;
    *out = *buf.offset(0 as isize);
    free(buf as *mut core::ffi::c_void);
    return 1 as i32;
}
pub unsafe extern "C" fn zeroed(mut n: usize, mut out: *mut u32) -> i32 {
    let mut grid = calloc(n as std::os::raw::c_ulong, ::std::mem::size_of::<u32>() as std::os::raw::c_ulong) as *mut u32;
    if grid.is_null() {
        return 0 as i32;
    }
    *out = *grid.offset(0 as isize);
    free(grid as *mut core::ffi::c_void);
    return 1 as i32;
}
#[repr(C, align(32))]
pub struct Wide {
    pub a: u64,
    pub b: u64,
}
pub unsafe extern "C" fn over_aligned(mut n: usize) -> u64 {
    let mut w = malloc(::std::mem::size_of::<Wide>() as std::os::raw::c_ulong) as *mut Wide;
    if w.is_null() {
        return 0 as u64;
    }
    (*w).a = n as u64;
    let mut seen = (*w).a;
    free(w as *mut core::ffi::c_void);
    return seen;
}
pub unsafe extern "C" fn region(mut n: usize) -> usize {
    let mut mem = malloc((n as std::os::raw::c_ulong).wrapping_mul(::std::mem::size_of::<u32>() as std::os::raw::c_ulong)) as *mut u32;
    if mem.is_null() {
        return 0 as usize;
    }
    let mut seen = span_of(mem as *const core::ffi::c_void, n);
    free(mem as *mut core::ffi::c_void);
    return seen;
}
pub unsafe extern "C" fn span_of(mut p: *const core::ffi::c_void, mut n: usize) -> usize {
    return (p as usize).wrapping_add(n);
}
pub unsafe extern "C" fn copied(mut src: *const std::os::raw::c_char) -> i32 {
    let mut dup = strdup(src);
    if dup.is_null() {
        return 0 as i32;
    }
    let mut same = strcmp(dup, src);
    free(dup as *mut core::ffi::c_void);
    return same;
}
"#;

#[test]
fn w6a_ac_the_libc_row_owns_malloc_calloc_and_strdup_locals() {
    let out = emitted("ac-libc", LIBC_OWNERS);
    if let Ok(path) = std::env::var("W6A_DUMP_EMITTED") {
        std::fs::write(path, &out.source).expect("dump");
    }
    let text = compact(&out.source);
    let receipts = &out.artifacts.allocator_contract_receipts;
    assert_eq!(
        out.reverted, 0,
        "{}\n{:#?}\n{receipts}",
        out.source, out.degradations
    );
    for expected in [
        // malloc: the byte count is `n * size_of::<T>()`, so the count is `n`.
        "letmutbuf:Box<[u32]>=Box::from_raw(core::ptr::slice_from_raw_parts_mut(malloc(",
        "buf[(0)asusize]=7asu32;",
        "free(Box::into_raw(buf)as*mutcore::ffi::c_void);",
        // calloc: the count is the element argument, the size the pointee's.
        "letmutgrid:Box<[u32]>=Box::from_raw(core::ptr::slice_from_raw_parts_mut(calloc(nasstd::os::raw::c_ulong,",
        "free(Box::into_raw(grid)as*mutcore::ffi::c_void);",
        // strdup: the contract's postcondition, measured on the block itself —
        // the count never mentions `src`. The ARGUMENT's spelling is not this
        // rule's: a composition may hand `strdup` a view of `src`
        // (`src.as_ptr()`, wave-6s 057) without touching the claim, so the
        // opening and the postcondition are asserted apart (R217-2(a)).
        "letmutdup:Box<[i8]>={let__crat_alloc=strdup(",
        ");Box::from_raw(core::ptr::slice_from_raw_parts_mut(__crat_alloc,core::ffi::CStr::from_ptr(__crat_alloc).to_bytes().len().wrapping_add(1)))};",
        "free(Box::into_raw(dup)as*mutcore::ffi::c_void);",
    ] {
        assert!(
            text.contains(expected),
            "missing `{expected}`\n{}\n{:#?}\n{receipts}",
            out.source,
            out.degradations
        );
    }
    for subject in ["counted::buf", "zeroed::grid", "copied::dup"] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}\n{:#?}",
            out.degradations
        );
        assert!(
            receipts.contains(&format!("{subject}\tadmitted\t")),
            "{receipts}"
        );
    }
    assert!(
        receipts.contains("allocator-contract:libc/v1@2026-09-17"),
        "{receipts}"
    );
    // CONTROL (R443-1): the one shape the System declaration does not cover.
    // libc guarantees alignment for any fundamental type; `System`'s dealloc of
    // an over-aligned layout is not `free`, so an over-aligned pointee keeps a
    // typed hold rather than a Box whose release would not match its
    // allocation.
    assert!(
        receipts.contains(
            "over_aligned::w\tyielded\tcontract-allocation:use:box-over-aligned-pointee:32"
        ),
        "{receipts}"
    );
    assert!(
        !compact(&out.source).contains("letmutw:Box<"),
        "{}",
        out.source
    );
    // CONTROL: **a refusal of the libc row is a RECEIPT, never a decision.**
    // `region::mem` is handed to a local callee this rule cannot prove a lend
    // of, so the row yields — and because it yields rather than holding, the
    // subject stays available to whichever family does claim it, which is what
    // kept seven witnesses of this lane and two of wave-6v's green when the
    // row arrived.
    assert!(
        receipts.contains("region::mem\tyielded\tcontract-allocation:use:"),
        "{receipts}"
    );
    assert!(
        !receipts.contains("region::mem\theld\t"),
        "a libc refusal must not degrade the subject\n{receipts}"
    );
    assert!(
        !compact(&out.source).contains("letmutmem:Box<"),
        "{}",
        out.source
    );
}

/// **The overwrite of a live unique owner** (R434-4 §2, withdrawn on Miri's
/// evidence in report 019 and RE-ADMITTED under R443-1): `dup = strdup(src)`
/// over a generation the owner still holds. The input LEAKS the first block;
/// the emitted program closes it with Rust's ordinary overwrite drop, which
/// is what the leak-parity waiver licenses (addendum 101) — and which is
/// well-defined because the emitted crate declares the System allocator, so
/// Rust's deallocation IS the contract's `free` (report 020's probe: the same
/// fixture is UB without the declaration and `ok r=0` with it, leaking 0 where
/// the input leaks 1). The site carries `waiver-drop(overwrite)`.
///
/// Uniqueness is not assumed: a copy into another local, an unproven lend or
/// an unbridged cast each refuse the subject before the simulation runs.
const OVERWRITTEN_OWNER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types)]
extern "C" {
    fn malloc(size: std::os::raw::c_ulong) -> *mut core::ffi::c_void;
    fn strdup(s: *const std::os::raw::c_char) -> *mut std::os::raw::c_char;
    fn strcmp(a: *const std::os::raw::c_char, b: *const std::os::raw::c_char) -> i32;
    fn free(ptr: *mut core::ffi::c_void);
}
pub unsafe extern "C" fn twice(mut src: *const std::os::raw::c_char) -> i32 {
    let mut dup = strdup(src);
    if dup.is_null() {
        return 0 as i32;
    }
    let mut first = strcmp(dup, src);
    dup = strdup(src);
    let mut second = strcmp(dup, src);
    free(dup as *mut core::ffi::c_void);
    return first + second;
}
"#;

#[test]
fn w6a_ac_an_overwrite_of_a_live_owner_takes_the_leak_parity_waiver() {
    let out = emitted("ac-overwrite", OVERWRITTEN_OWNER);
    if let Ok(path) = std::env::var("W6A_DUMP_EMITTED") {
        std::fs::write(path, &out.source).expect("dump");
    }
    let text = compact(&out.source);
    let receipts = &out.artifacts.allocator_contract_receipts;
    assert_eq!(
        out.reverted, 0,
        "{}\n{:#?}\n{receipts}",
        out.source, out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "twice::dup"),
        None,
        "{:#?}\n{receipts}",
        out.degradations
    );
    for expected in [
        // The argument's spelling is a composition's (wave-6s 057's
        // `src.as_ptr()`); the generation and its waiver are this rule's.
        "letmutdup:Option<Box<[i8]>>=Some({let__crat_alloc=strdup(",
        "ifdup.is_none(){return0asi32;}",
        // The overwrite itself: a new generation assigned over a live one.
        "dup=Some({let__crat_alloc=strdup(",
        "free(dup.map_or(core::ptr::null_mut(),|b|Box::into_raw(b)as*mutcore::ffi::c_void));",
    ] {
        assert!(
            text.contains(expected),
            "missing `{expected}`\n{}\n{receipts}",
            out.source
        );
    }
    // One overwritten generation, one waiver receipt.
    assert_eq!(
        receipts.matches("waiver-drop(overwrite) site=").count(),
        1,
        "{receipts}"
    );
    assert!(receipts.contains("generations=2"), "{receipts}");
}

/// **The optional owner lent at a LOCAL callee's raw formal** (relay
/// wave-6a/029, R451-3): brotli's `BrotliHistogramCombine{Literal,Distance,
/// Command}` shape. The callee keeps a raw formal, so the seam's owner-view
/// glue (which converts) does not apply and the ordinary raw bridge renders
/// `x.as_mut_ptr()` — on an `Option`, 27 of batch 10's 44 reverts. The owner's
/// own view is spelled here instead, keyed on its decision FORM:
/// `.as_deref_mut().map_or(core::ptr::null_mut(), |s| s.as_mut_ptr())`, under
/// the argument's own casts (the `*mut u8` vs `*mut c_void` spelling, 18 more).
const LOCAL_RAW_FORMAL: &str = r#"
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
pub unsafe extern "C" fn combine_void(mut region: *mut std::os::raw::c_void, mut n: usize) -> u32 {
    let mut words = region as *mut u32;
    let mut i = 0 as usize;
    let mut acc = 0 as u32;
    while i < n {
        acc = acc.wrapping_add(*words.offset(i as isize));
        i = i.wrapping_add(1);
    }
    return acc;
}
pub unsafe extern "C" fn cluster_combine(mut m: *mut MemoryManager, mut n: usize, mut split: *mut u32) {
    let mut syms = if n > 0 as usize { BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32 } else { 0 as *mut u32 };
    *syms.offset(0 as isize) = 3 as u32;
    *split = combine_void(syms as *mut std::os::raw::c_void, n);
    BrotliFree(m, syms as *mut std::os::raw::c_void);
    syms = 0 as *mut u32;
}
"#;

#[test]
fn w6a_ac_an_optional_owner_lent_at_a_local_raw_formal_takes_its_own_view() {
    let out = emitted("ac-local-raw-formal", LOCAL_RAW_FORMAL);
    if let Ok(path) = std::env::var("W6A_DUMP_EMITTED") {
        std::fs::write(path, &out.source).expect("dump");
    }
    let text = compact(&out.source);
    let receipts = &out.artifacts.allocator_contract_receipts;
    assert_eq!(
        out.reverted, 0,
        "{}\n{:#?}\n{receipts}",
        out.source, out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "cluster_combine::syms"),
        None,
        "{:#?}\n{receipts}",
        out.degradations
    );
    assert!(
        text.contains("combine_void(syms.as_deref_mut().map_or(core::ptr::null_mut(),|s|s.as_mut_ptr())as*mutstd::os::raw::c_void,n)"),
        "the owner's own raw view, under the argument's cast\n{}",
        out.source
    );
}

/// **The four Box cells of the raw-view vocabulary** (R452-3(3)). One template
/// used to render every owner — `core::ptr::from_mut(X.as_mut())` — which is
/// right for exactly one of the four shapes. A fat owner's raw view is the
/// SLICE's (the whole allocation, not a pointer to the `Box`), and an OPTIONAL
/// owner must be opened before it is viewed, with `None` as the null pointer.
/// Batch 10 measured the cost of the missing cells: 27 brotli reverts reading
/// `no method named as_mut_ptr found for enum Option`, and wave-6f's three
/// `verify-reverted` roots (their report 031 §6).
#[test]
fn w6a_glue_each_box_shape_renders_its_own_raw_view() {
    use super::decision::{
        Decision,
        box_facts::{BoxPlan, BoxShape},
        raw_boundary::{BridgeRender, BridgeTemplate, RawMutability, RawTargetType, template_for},
    };

    let plan = |shape: BoxShape, optional: bool| {
        Decision::Box(BoxPlan {
            shape,
            optional,
            expr_edits: Vec::new(),
            delete_statements: Vec::new(),
            receipts: Vec::new(),
            fabricated_extent: false,
            pointee_override: None,
            inferred_binding: false,
            overwrite_spans: Vec::new(),
            retained_sink: false,
            implicit_scope_close: false,
        })
    };
    let target = |mutability: RawMutability| RawTargetType {
        rendered: format!(
            "*{} u32",
            if mutability == RawMutability::Mut {
                "mut"
            } else {
                "const"
            }
        ),
        pointee: "u32".to_owned(),
        mutability,
        depth2: None,
    };
    let render = |shape: BoxShape, optional: bool, mutability: RawMutability| {
        let decision = plan(shape, optional);
        let template = template_for(&decision, &target(mutability), None, false)
            .expect("a Box owner has a raw view");
        let slice = shape == BoxShape::Slice;
        match template
            .render("x", mutability, slice, Some("u32"))
            .expect("the cell renders")
        {
            BridgeRender::Edit(text) => (template, text),
            other => panic!("{other:?}"),
        }
    };

    // The selection is by the owner's FORM, and the census receipts name it.
    let (t, text) = render(BoxShape::Sized, false, RawMutability::Mut);
    assert_eq!(t, BridgeTemplate::BoxBorrowViewToRaw);
    assert_eq!(text, "core::ptr::from_mut(x.as_mut())");

    let (t, text) = render(BoxShape::Slice, false, RawMutability::Mut);
    assert_eq!(t, BridgeTemplate::BoxBorrowViewToRaw);
    assert_eq!(text, "x.as_mut_ptr()");

    let (t, text) = render(BoxShape::Sized, true, RawMutability::Mut);
    assert_eq!(t, BridgeTemplate::OptionalBoxBorrowViewToRaw);
    assert_eq!(
        text,
        "x.as_deref_mut().map_or(core::ptr::null_mut(), core::ptr::from_mut)"
    );

    let (t, text) = render(BoxShape::Slice, true, RawMutability::Mut);
    assert_eq!(t, BridgeTemplate::OptionalBoxBorrowViewToRaw);
    assert_eq!(
        text,
        "x.as_deref_mut().map_or(core::ptr::null_mut(), |s| s.as_mut_ptr())"
    );

    // …and the four shared twins.
    assert_eq!(
        render(BoxShape::Sized, false, RawMutability::Const).1,
        "core::ptr::from_ref(x.as_ref())"
    );
    assert_eq!(
        render(BoxShape::Slice, false, RawMutability::Const).1,
        "x.as_ptr()"
    );
    assert_eq!(
        render(BoxShape::Sized, true, RawMutability::Const).1,
        "x.as_deref().map_or(core::ptr::null(), core::ptr::from_ref)"
    );
    assert_eq!(
        render(BoxShape::Slice, true, RawMutability::Const).1,
        "x.as_deref().map_or(core::ptr::null(), |s| s.as_ptr())"
    );
}

const MOVE_INTO_HELD_OWNER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
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
pub unsafe extern "C" fn ensure_capacity(mut m: *mut MemoryManager, mut n: usize) -> *mut u32 {
    let mut all_values = if n > 0 as usize {
        BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    let mut new_array = if n > 0 as usize {
        BrotliAllocate(m, n.wrapping_mul(2 as usize).wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    *new_array.offset(0 as isize) = *all_values.offset(0 as isize);
    BrotliFree(m, all_values as *mut std::os::raw::c_void);
    all_values = new_array;
    return all_values;
}
pub unsafe extern "C" fn ensure_capacity_freed(mut m: *mut MemoryManager, mut n: usize) {
    let mut all_values = if n > 0 as usize {
        BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    let mut new_array = if n > 0 as usize {
        BrotliAllocate(m, n.wrapping_mul(2 as usize).wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    *new_array.offset(0 as isize) = *all_values.offset(0 as isize);
    BrotliFree(m, all_values as *mut std::os::raw::c_void);
    all_values = new_array;
    BrotliFree(m, all_values as *mut std::os::raw::c_void);
    all_values = 0 as *mut u32;
}
"#;

/// **A move's destination must be an owner this rule ADMITS, not merely a
/// candidate** (report 027). `new_array` hands its generation to
/// `all_values` — brotli's ensure-capacity shape — and `all_values` is HELD
/// (here by its return; on the corpus by `use:call-argument-not-a-lend` at
/// `BrotliHistogramCombine*`). Admitting the mover alone assigns an
/// `Option<Box<[T]>>` into a place that stays raw, which is exactly the one
/// diagnostic each of batch 12's six `verify-reverted` Box classes carried:
/// `expected raw pointer *mut HistogramLiteral, found enum
/// Option<Box<[HistogramLiteral]>>` (24 of brotli's 45 reverted Box rows, and
/// the 20 `closure:partition` rows behind them).
///
/// One fault: let the destination be any candidate (the pre-fix `move_ok`) and
/// `new_array` is admitted again — the receipt flips to `admitted` and the
/// emitted text carries the Box into the raw place.
#[test]
fn w6a_ac_a_move_into_a_held_owner_is_refused() {
    let out = emitted("ac-move-into-held", MOVE_INTO_HELD_OWNER);
    let receipts = &out.artifacts.allocator_contract_receipts;
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    assert!(
        receipts.contains(
            "ensure_capacity::new_array\theld\tcontract-allocation:use:moved-into-unadmitted-owner:ensure_capacity::all_values"
        ),
        "the mover is held with its destination\n{receipts}"
    );
    assert!(
        !receipts.contains("ensure_capacity::new_array\tadmitted"),
        "no admission for the mover\n{receipts}"
    );
    let text = compact(&out.source);
    let held_fn = &text[text
        .find("fnensure_capacity(")
        .expect("the held-destination function")
        ..text.find("fnensure_capacity_freed").expect("the sibling")];
    assert!(
        held_fn.contains("all_values=new_array;"),
        "the move keeps its text\n{}",
        out.source
    );
    assert!(
        !held_fn.contains("Box<"),
        "no Box anywhere in the held-destination function\n{}",
        out.source
    );
    // The fix is a condition on the destination, not a ban on moves: the
    // sibling whose destination this rule DOES admit (it frees the moved
    // generation here) keeps both owners and the move's own text.
    assert!(
        receipts.contains("ensure_capacity_freed::new_array\tadmitted"),
        "a move into an admitted owner still delivers\n{receipts}"
    );
    assert!(
        text.contains("fnensure_capacity_freed")
            && text.contains("letmutall_values:Option<Box<[u32]>>"),
        "the admitted destination is the Box\n{}",
        out.source
    );
}

const OPTIONAL_SLICE_DEREF: &str = r#"
#[repr(C)]
pub struct Cmd {
    pub arity: i32,
    pub used: i32,
}
pub unsafe extern "C" fn add_func(mut m: *mut MemoryManager, mut n: usize) -> i32 {
    let mut cmd = if n > 0 as usize {
        BrotliAllocate(m, (1 as usize).wrapping_mul(::core::mem::size_of::<Cmd>())) as *mut Cmd
    } else { 0 as *mut Cmd };
    (*cmd).arity = 2 as i32;
    (*cmd).used = 1 as i32;
    let mut seen = (*cmd).arity;
    BrotliFree(m, cmd as *mut std::os::raw::c_void);
    cmd = 0 as *mut Cmd;
    return seen;
}
"#;

/// **A4 / R483-3(i): `*b` on an `Option<Box<[T]>>` is its first element.** The
/// walk refused this shape (`use:optional-slice-deref`) although the
/// rendering is the one the `.offset` arm already writes with an index of
/// zero. The corpus's two rows are lil's `add_func::cmd` and
/// `lil_clone_value::val` — `calloc(1, size_of::<T>())` owners whose every use
/// is `(*cmd).field` — and this fixture is that shape over the brotli
/// contract, with a write and a read of the same owner.
///
/// The write must be seen THROUGH the field projection: `(*cmd).name = name`
/// writes the owner, so the view is `as_deref_mut()`; the read beside it takes
/// `as_deref()`. One fault: refuse the shape again and the owner degrades.
#[test]
fn w6a_ac_an_optional_slice_owner_derefs_to_its_first_element() {
    let out = emitted(
        "ac-optional-deref",
        &format!("{PRELUDE}{OPTIONAL_SLICE_DEREF}"),
    );
    let receipts = &out.artifacts.allocator_contract_receipts;
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    assert!(
        receipts.contains("add_func::cmd\tadmitted"),
        "the deref is a rendering, not a refusal\n{receipts}"
    );
    assert!(!receipts.contains("optional-slice-deref"), "{receipts}");
    let text = compact(&out.source);
    // The writes take the mutable view, through the projection …
    assert!(
        text.contains("cmd.as_deref_mut().unwrap()[0].arity=2asi32;"),
        "{}",
        out.source
    );
    assert!(
        text.contains("cmd.as_deref_mut().unwrap()[0].used=1asi32;"),
        "{}",
        out.source
    );
    // … and the read beside them takes the shared one.
    assert!(
        text.contains("letmutseen=cmd.as_deref().unwrap()[0].arity;"),
        "{}",
        out.source
    );
    // The free stays at the C free site.
    assert!(
        text.contains("BrotliFree(m,cmd.map_or(core::ptr::null_mut(),|b|Box::into_raw(b)as*mutstd::os::raw::c_void));"),
        "{}",
        out.source
    );
}

/// **A4 part 1's second half (R485-2): a body may prove a lend the model does
/// not.** The oracle required the callee's formal to be model-`Ref`; the 37
/// `contract-allocation:use:call-argument-not-a-lend` rows at batch 16 — 18 of
/// them `BrotliHistogramCombine{Literal,Distance,Command}` — are owners whose
/// callee the model calls `Raw`, which is the absence of a verdict, not a
/// claim of ownership. `LendWalk` is the evidence there: a free, a store, a
/// return or a copy of the formal each refuse it.
///
/// `Owning` is a positive claim and is NOT superseded by this walk, and a
/// formal with no slot answers nothing. This witness pins those four answers;
/// the end-to-end effect is the next census's to measure, because no small
/// fixture of this lane holds a formal at model-`Raw` (five shapes tried
/// across reports 024 and 039).
#[test]
fn w6a_a_body_proves_a_lend_for_every_slotted_formal() {
    use super::{
        super::analyses::borrow_ownership::SlotKind,
        decision::return_certificate::model_admits_lend,
    };

    // The model's own lend verdict, and the absence the body may fill.
    assert!(model_admits_lend(Some(SlotKind::Ref)));
    assert!(model_admits_lend(Some(SlotKind::Raw)));
    // **Restated for W6A-A1-e** (relay wave-6a/049). Report 039 read the
    // `Owning` case as a claim a use walk may not supersede. That reading was
    // about the FORMAL — and this oracle does not touch the formal. It answers
    // one question for the CALLER, whether its certificate survives the call,
    // and the formal keeps its kind, its raw form and its own family
    // (ownership-fields emits exactly these as raw views with the `Owning`
    // label recorded beside them). Nothing is overturned, so the claim is
    // admitted and the body walk alone decides.
    assert!(model_admits_lend(Some(SlotKind::Owning)));
    // A formal the model never slotted answers nothing, in every reading.
    assert!(!model_admits_lend(None));
}

/// **R551-5 joint (a) (relay wave-6a/083–084).** A Box owner lent to a local
/// callee whose converted formal falls back to its raw input form. brotli's
/// `ClusterBlocks*` pass `histogram_symbols` to `BrotliHistogramCombine*`, a
/// class the A5 site proof holds; the caller's partition reverted because
/// `callee_parameter_input` refused any source decided `Box`. The owner now
/// supplies its raw view, tiered by the raw boundary's own disposition of
/// the site, through the template every raw-boundary Box site renders.
///
/// Returns the emitted tree with the CALLEE's class reverted, and the
/// callee-parameter input plan's current source for `callee`'s argument
/// from `caller`: its bridge kind and tier, or its refusal key.
fn box_source_at_reverted_callee(
    name: &str,
    src: &str,
    caller: &str,
    callee: &str,
) -> (
    String,
    Result<(String, super::bridge_receipt::BridgeRetentionTier), &'static str>,
) {
    let (source, input) = ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original AST");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("one decision pipeline");
        let function = |name: &str| {
            table
                .entries
                .iter()
                .map(|(subject, _)| subject.fn_did)
                .find(|did| {
                    tcx.def_path_str(did.to_def_id())
                        .ends_with(&format!("::{name}"))
                        || tcx.def_path_str(did.to_def_id()) == name
                })
                .unwrap_or_else(|| panic!("function {name} has subjects"))
        };
        let (caller, callee) = (function(caller), function(callee));
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("one terminal plan");
        let inputs = emission
            .plan
            .terminal_call_plans
            .callee_parameter_inputs
            .values()
            .filter(|input| input.caller == caller && input.node.0 == callee)
            .collect::<Vec<_>>();
        let [input] = inputs.as_slice() else {
            panic!("{name}: one callee-parameter input for {callee:?}: {inputs:#?}")
        };
        let input = input
            .current_source
            .as_ref()
            .map_err(|reason| *reason)
            .map(|alternative| {
                let bridge = alternative
                    .bridge
                    .as_ref()
                    .expect("an adapter carries its bridge");
                (bridge.bridge_kind.clone(), bridge.retention)
            });
        let mut reverted = emission.plan.held_classes();
        reverted.insert(super::bridge_receipt::SignatureClassId::of(callee));
        let (files, rollbacks, ..) = super::round_files(
            tcx,
            &capture,
            &emission.plan,
            &emission.texts,
            &reverted,
            &std::collections::BTreeSet::new(),
            emission.plan.root_file.as_ref(),
            &table,
        )
        .expect("the reverted-callee emission");
        assert!(
            rollbacks.is_empty(),
            "{name}: no structural rollback: {rollbacks:#?}"
        );
        (files.into_values().next().expect("one file"), input)
    })
    .expect("the fixture compiles");
    (source, input)
}

const LENT_TO_A_REVERTED_CALLEE: &str = r#"
pub unsafe extern "C" fn lending(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {
    let mut lent = BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32;
    *lent.offset(0 as isize) = 1 as u32;
    *split = ReindexSymbols(lent, n);
    BrotliFree(m, lent as *mut std::os::raw::c_void);
}
"#;

/// The owner's raw view at the fallen-back formal: `lent.as_mut_ptr()`,
/// `box-borrow-view-to-raw` at tier 1 (`ReindexSymbols` only reads), and the
/// tree type-checks with the callee raw and the owner still `Box<[u32]>`.
#[test]
fn w6a_r551_a_box_owner_lends_its_raw_view_to_a_reverted_callee() {
    let (source, input) = box_source_at_reverted_callee(
        "r551-box-source",
        &format!("{PRELUDE}{LENT_TO_A_REVERTED_CALLEE}"),
        "lending",
        "ReindexSymbols",
    );
    assert_eq!(
        input,
        Ok((
            "box-borrow-view-to-raw".to_owned(),
            super::bridge_receipt::BridgeRetentionTier::T1
        )),
        "{source}"
    );
    let text = compact(&source);
    assert!(text.contains("letmutlent:Box<[u32]>="), "{source}");
    assert!(
        text.contains("*split=ReindexSymbols(lent.as_mut_ptr(),n);"),
        "{source}"
    );
    assert!(
        text.contains("fnReindexSymbols(mutsymbols:*mutu32,"),
        "{source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// Control: an OPTIONAL owner (the conditional allocation) lends the R130
/// optional view — `None` is the null the raw formal already accepts.
#[test]
fn w6a_r551_an_optional_owner_lends_the_optional_raw_view() {
    let src = format!(
        "{PRELUDE}\
pub unsafe extern \"C\" fn optional(mut m: *mut MemoryManager, n: usize, mut split: *mut u32) {{\n\
    let mut syms = if n > 0 as usize {{\n\
        BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32\n\
    }} else {{ 0 as *mut u32 }};\n\
    if n > 0 as usize {{ *syms.offset(0 as isize) = 1 as u32; }}\n\
    *split = ReindexSymbols(syms, n);\n\
    BrotliFree(m, syms as *mut std::os::raw::c_void);\n\
}}\n"
    );
    let (source, input) =
        box_source_at_reverted_callee("r551-optional-source", &src, "optional", "ReindexSymbols");
    assert_eq!(
        input,
        Ok((
            "optional-box-borrow-view-to-raw".to_owned(),
            super::bridge_receipt::BridgeRetentionTier::T1
        )),
        "{source}"
    );
    let text = compact(&source);
    assert!(text.contains("letmutsyms:Option<Box<[u32]>>="), "{source}");
    assert!(
        text.contains(
            "ReindexSymbols(syms.as_deref_mut().map_or(core::ptr::null_mut(),|s|s.as_mut_ptr()),n)"
        ),
        "{source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

const ELEMENTS: &str = r#"
#[repr(C)]
#[derive(Copy, Clone)]
pub struct Hist { pub data_: [u32; 4], pub total_count_: usize }
pub unsafe extern "C" fn HistogramAdd(mut self_0: *mut Hist, mut val: usize) {
    (*self_0).data_[val] = ((*self_0).data_[val]).wrapping_add(1 as u32);
    (*self_0).total_count_ = ((*self_0).total_count_).wrapping_add(1 as usize);
}
pub unsafe extern "C" fn BitsEntropy(mut population: *const u32, mut size: usize) -> u32 {
    let mut sum = 0 as u32;
    let mut i = 0 as usize;
    while i < size { sum = sum.wrapping_add(*population.offset(i as isize)); i = i.wrapping_add(1); }
    return sum;
}
pub unsafe extern "C" fn adding(mut m: *mut MemoryManager, n: usize, mut out: *mut usize) {
    let mut histograms = if n > 0 as usize {
        BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<Hist>())) as *mut Hist
    } else { 0 as *mut Hist };
    let mut j = 0 as usize;
    while j < n {
        (*histograms.offset(j as isize)).total_count_ = 0 as usize;
        HistogramAdd(&mut *histograms.offset(j as isize), j & 3 as usize);
        j = j.wrapping_add(1);
    }
    if n > 0 as usize { *out = (*histograms.offset(0 as isize)).total_count_; }
    BrotliFree(m, histograms as *mut std::os::raw::c_void);
}
pub unsafe extern "C" fn entropy(mut m: *mut MemoryManager, n: usize, mut out: *mut u32) {
    let mut combined = if n > 0 as usize {
        BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<Hist>())) as *mut Hist
    } else { 0 as *mut Hist };
    if n > 0 as usize {
    (*combined.offset(0 as isize)).total_count_ = 0 as usize;
    *out = BitsEntropy(&mut *((*combined.offset(0 as isize)).data_).as_mut_ptr().offset(0 as isize), 4 as usize);
    }
    BrotliFree(m, combined as *mut std::os::raw::c_void);
}
"#;

/// **R555-1 joint (d).** An element address of a Box owner —
/// `&mut *histograms.offset(j)` at a `&mut Hist` formal — is `&mut T` once the
/// Box plan renders the element (`histograms.as_deref_mut().unwrap()[j]`).
/// The owner-view glue (R422-5) is the OWNER's view and applies to the owner
/// passed bare; keyed on the place root it also wrapped this element as
/// `&mut (&mut ..[j]).as_mut().unwrap()[0]` (E0599 — brotli `ClusterBlocks*`'s
/// fifteen, `ContextBlockSplitterFinishBlock`).
#[test]
fn w6a_r555_an_element_address_of_a_box_owner_passes_as_written() {
    let out = emitted("r555-element", &format!("{PRELUDE}{ELEMENTS}"));
    let text = compact(&out.source);
    for subject in [
        "adding::histograms",
        "HistogramAdd::self_0",
        "entropy::combined",
        "BitsEntropy::population",
    ] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}\n{:#?}\n{}",
            out.degradations,
            out.source
        );
    }
    assert!(!text.contains(".as_mut().unwrap()[0]"), "{}", out.source);
    assert!(
        text.contains("HistogramAdd(&muthistograms.as_deref_mut().unwrap()[(j)asusize],"),
        "{}",
        out.source
    );
    assert!(
        text.contains("fnHistogramAdd(mutself_0:&mutHist,"),
        "{}",
        out.source
    );
    assert!(
        text.contains("fnBitsEntropy(mutpopulation:&[u32],"),
        "{}",
        out.source
    );
    // A write through the element's projection opens the owner mutably.
    assert!(
        text.contains("histograms.as_deref_mut().unwrap()[(j)asusize].total_count_=0asusize;"),
        "{}",
        out.source
    );
    // The array start of an element's array field is the array-start seam's
    // own rendering (W-C6: `from_raw_parts(A.as_mut_ptr(), LEN)`, here at the
    // receipted §77 fallback extent — no companion is licensed), not a
    // one-element slice; the `&mut self` `as_mut_ptr` opens the owner mutably.
    assert!(
        text.contains(
            "BitsEntropy(core::slice::from_raw_parts((combined.as_deref_mut().unwrap()[(0)asusize].data_).as_mut_ptr(),crate::FALLBACK_SLICE_EXTENT),4asusize);"
        ),
        "{}",
        out.source
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
}

/// Joint (a)'s owner view is likewise the owner's: an element address of a Box
/// owner at a callee formal that falls back to raw keeps the refusal (it is a
/// reference to one element, not the owner, and has no raw-view rendering of
/// the owner's).
#[test]
fn w6a_r555_an_element_address_does_not_take_the_owner_raw_view() {
    let (source, input) = box_source_at_reverted_callee(
        "r555-element-reverted",
        &format!("{PRELUDE}{ELEMENTS}"),
        "adding",
        "HistogramAdd",
    );
    assert_eq!(
        input,
        Err("callee-parameter-input-owned-or-inferred-source-unbuilt"),
        "{source}"
    );
}

/// **R557-4: the element-address classifier's home.** `&mut *X.offset(i)` /
/// `&*X.offset(i)` over a bare local `X` is the address of one element of
/// `X`: `box_facts::box_element_address` names the owner, the index and the
/// mutability — the owner walk's offset arm, the 089 seam restriction and
/// wave-5d's joint (c) call this one function. A bare owner, a field place and
/// an offset that is not dereferenced are not element addresses.
#[test]
fn w6a_r557_the_element_address_classifier_names_owner_index_and_mutability() {
    let src = format!("{PRELUDE}{ELEMENTS}");
    let rows = ::utils::compilation::run_compiler_on_str(&src, |tcx| {
        struct V<'tcx> {
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
            rows: Vec<String>,
        }
        impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for V<'tcx> {
            fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
                if matches!(
                    expr.kind,
                    rustc_hir::ExprKind::AddrOf(..) | rustc_hir::ExprKind::Path(..)
                ) {
                    let sm = self.tcx.sess.source_map();
                    let text = sm.span_to_snippet(expr.span).unwrap_or_default();
                    let got = super::decision::box_facts::box_element_address(expr).map(
                        |(owner, index, mutable)| {
                            format!(
                                "{}|{}|{mutable}",
                                self.tcx.hir_name(owner),
                                sm.span_to_snippet(index.span).unwrap_or_default()
                            )
                        },
                    );
                    self.rows.push(format!("{text} => {got:?}"));
                }
                rustc_hir::intravisit::walk_expr(self, expr);
            }
        }
        let mut v = V {
            tcx,
            rows: Vec::new(),
        };
        for owner in tcx.hir_body_owners() {
            rustc_hir::intravisit::Visitor::visit_body(&mut v, tcx.hir_body_owned_by(owner));
        }
        v.rows
    })
    .expect("the fixture compiles");
    let find = |text: &str| {
        rows.iter()
            .find(|row| row.starts_with(&format!("{text} => ")))
            .unwrap_or_else(|| panic!("{text}\n{rows:#?}"))
            .clone()
    };
    assert_eq!(
        find("&mut *histograms.offset(j as isize)"),
        "&mut *histograms.offset(j as isize) => Some(\"histograms|j as isize|true\")"
    );
    assert_eq!(
        find("&mut *((*combined.offset(0 as isize)).data_).as_mut_ptr().offset(0 as isize)"),
        "&mut *((*combined.offset(0 as isize)).data_).as_mut_ptr().offset(0 as isize) => None",
        "the element's field array is not an element address of `combined`"
    );
    assert_eq!(find("histograms"), "histograms => None");
}
