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
        // the count never mentions `src`.
        "letmutdup:Box<[i8]>={let__crat_alloc=strdup(src);Box::from_raw(core::ptr::slice_from_raw_parts_mut(__crat_alloc,core::ffi::CStr::from_ptr(__crat_alloc).to_bytes().len().wrapping_add(1)))};",
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
        "letmutdup:Option<Box<[i8]>>=Some({let__crat_alloc=strdup(src);",
        "ifdup.is_none(){return0asi32;}",
        // The overwrite itself: a new generation assigned over a live one.
        "dup=Some({let__crat_alloc=strdup(src);",
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
