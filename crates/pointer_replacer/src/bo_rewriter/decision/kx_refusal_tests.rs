//! wave-6l relay 063 (R645-5 item 2): the 46 companions the reader chain
//! licensed that were never the extent (the extent record's KX rows) are
//! refused by a named list; (item 6) a mask is never taken as a count.

const PREPARE_H35: &str = r###"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_camel_case_types, unused_unsafe)]
pub mod src {
    pub mod enc {
        pub mod encode {
            unsafe extern "C" fn BrotliUnalignedRead64(mut p: *const core::ffi::c_void) -> u64 {
                return *(p as *const u64);
            }
            unsafe extern "C" fn HashBytesH3(mut data: *const u8) -> u32 {
                let h = (BrotliUnalignedRead64(data as *const core::ffi::c_void) << 24)
                    .wrapping_mul(0x1e35a7bd);
                return (h >> 48) as u32;
            }
            pub struct H3 {
                pub buckets_: *mut u32,
            }
            pub struct H35 {
                pub ha: H3,
            }
            unsafe extern "C" fn PrepareH3(mut self_0: *mut H3, mut one_shot: i32, mut input_size: u64, mut data: *const u8) {
                let mut buckets = (*self_0).buckets_;
                if one_shot != 0 && input_size <= 2048 {
                    let mut i: u64 = 0;
                    while i < input_size {
                        let key = HashBytesH3(&*data.offset(i as isize));
                        *buckets.offset((key & 65535) as isize) = 0;
                        i = i.wrapping_add(1);
                    }
                }
            }
            unsafe extern "C" fn PrepareH35(mut self_0: *mut H35, mut one_shot: i32, mut input_size: u64, mut data: *const u8) {
                PrepareH3(&mut (*self_0).ha, one_shot, input_size, data);
            }
            pub unsafe fn HasherPrepare(mut h: *mut H35, mut one_shot: i32, mut input_size: u64, mut data: *const u8) -> usize {
                let tag = data as usize;
                PrepareH35(h, one_shot, input_size, data);
                tag
            }
        }
    }
}
"###;

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The seam edits' `(replacement, extent receipt)` for one fixture.
fn edits(input: &str) -> Vec<(String, String)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).expect("decisions");
        table
            .seams
            .edits
            .iter()
            .map(|edit| (flat(&edit.replacement), format!("{:?}", edit.bridge.extent)))
            .collect::<Vec<_>>()
    })
    .expect("fixture compiles")
}

/// KX1 (item 2) — `PrepareH35`'s `input_size` licence is the KX list's: the
/// eight-byte hashes read to `input_size + 6`. The root takes the fallback,
/// and the receipt names the list.
#[test]
fn w6l_kx1_a_listed_licence_is_refused_and_receipted() {
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(PREPARE_H35).unwrap();
    let flat_source = flat(&source);
    assert!(!flat_source.contains("(input_size) as usize"), "{source}");
    assert!(
        flat_source.contains("core::slice::from_raw_parts(data, crate::FALLBACK_SLICE_EXTENT)"),
        "{source}"
    );
    let edits = edits(PREPARE_H35);
    assert!(
        edits.iter().any(
            |(replacement, extent)| replacement.contains("from_raw_parts(data,")
                && extent.contains("kx-list:src::enc::encode::PrepareH35::data")
        ),
        "{edits:#?}"
    );
}

/// KXc — a list, not a rule: the same shape under a name the list does not
/// carry keeps the reader chain's licence.
#[test]
fn w6l_kxc_an_unlisted_twin_keeps_its_licence() {
    let input = PREPARE_H35.replace("PrepareH35", "PrepareH36");
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(flat(&source).contains("(input_size) as usize"), "{source}");
}

/// The following-argument arm handed a mask (wave-5d 096 STOP 3): the
/// forwarder's callee masks its index through a compound update the reader
/// chain does not read as a mask, so the chain licenses `ring_buffer_mask` as
/// a COUNT at the forwarder; the caller's buffer comes from an integer, so
/// the caller stays raw.
const MASK_AS_COUNT: &str = r###"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case, unused_unsafe)]
unsafe extern "C" fn StoreAndFindMatchesH10(mut data: *const u8, mut ring_buffer_mask: usize, mut cur_ix: usize) -> u32 {
    let mut prev_ix = cur_ix.wrapping_sub(1);
    prev_ix &= ring_buffer_mask;
    *data.offset(prev_ix as isize) as u32
}
unsafe extern "C" fn FindAllMatchesH10(mut data: *const u8, mut ring_buffer_mask: usize, mut cur_ix: usize) -> u32 {
    StoreAndFindMatchesH10(data, ring_buffer_mask, cur_ix)
}
pub unsafe fn Create(mut addr: usize, mut ringbuffer_mask: usize, mut n: usize) -> u32 {
    let mut ringbuffer = addr as *const u8;
    FindAllMatchesH10(ringbuffer, ringbuffer_mask, n)
}
"###;

/// MK1 (item 6) — a mask is not a count: the root takes the fallback, and the
/// receipt says why.
#[test]
fn w6l_mk1_a_mask_is_not_taken_as_a_count() {
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(MASK_AS_COUNT).unwrap();
    assert!(
        !flat(&source).contains("(ringbuffer_mask) as usize"),
        "{source}"
    );
    let edits = edits(MASK_AS_COUNT);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:ringbuffer_mask")),
        "{edits:#?}"
    );
}

/// MKc — the control: the same call with a count that is not a mask keeps it.
#[test]
fn w6l_mkc_a_count_that_is_not_a_mask_stays_licensed() {
    let input = MASK_AS_COUNT
        .replace("ring_buffer_mask", "ring_buffer_len")
        .replace("ringbuffer_mask", "ringbuffer_len");
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        flat(&source).contains("(ringbuffer_len) as usize"),
        "{source}"
    );
}

/// MKm — item 6's second control: R477-6's MASKED arm licenses `mask + 1` on
/// its own proof (the callee's indexes are masked by the companion), and the
/// mask-as-count refusal leaves it alone.
#[test]
fn w6l_mkm_the_masked_arm_keeps_mask_plus_one() {
    let input = r###"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case, unused_unsafe)]
unsafe extern "C" fn StoreH2(mut data: *const u8, mut mask: usize, mut ix: usize) -> u32 {
    (*data.offset((ix & mask) as isize) as u32).wrapping_add(*data.offset(((ix & mask) + 1) as isize) as u32)
}
unsafe extern "C" fn StitchH2(mut ringbuffer: *const u8, mut ringbuffer_mask: usize, mut position: usize) -> u32 {
    StoreH2(ringbuffer, ringbuffer_mask, position)
}
pub unsafe fn Top(mut addr: usize, mut ringbuffer_mask: usize, mut n: usize) -> u32 {
    let mut ringbuffer = addr as *const u8;
    StitchH2(ringbuffer, ringbuffer_mask, n)
}
"###;
    let edits = edits(input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && replacement.contains("ringbuffer_mask")
            && extent.contains("MaskPlusOne")),
        "{edits:#?}"
    );
}

/// MK2 (the review's L3) — a mask reached through a plain alias
/// (`let m = ringbuffer_mask;`) is still a mask.
#[test]
fn w6l_mk2_a_mask_through_an_alias_is_not_a_count() {
    let input = MASK_AS_COUNT.replace(
        "    FindAllMatchesH10(ringbuffer, ringbuffer_mask, n)",
        "    let mut m = ringbuffer_mask;\n    FindAllMatchesH10(ringbuffer, m, n)",
    );
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:m")),
        "{edits:#?}"
    );
}

/// MK3 (the review's L3) — the callee's own formal names the mask: a caller
/// argument spelled otherwise is still handed to `ring_buffer_mask`.
#[test]
fn w6l_mk3_a_count_handed_to_a_mask_formal_is_refused() {
    let input = MASK_AS_COUNT.replace("ringbuffer_mask", "window");
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:window")),
        "{edits:#?}"
    );
}
