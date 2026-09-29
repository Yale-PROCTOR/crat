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
    prev_ix = prev_ix.wrapping_add(4);
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
/// receipt says why. Relay 065: the callee's masking is NOT provable here (the
/// index is re-assigned, `prev_ix + 4`, after the `&=`), so R477-6's masked arm
/// does not take it first (MK4 is the proven shape).
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

/// `MASK_AS_COUNT` with a callee the integer really bounds (a loop to it).
/// The original callee reads `((cur_ix - 1) & n) + 4`, past `n`: under relay
/// 068's licence the reader chain refuses it before the seam sees a count, so
/// the controls below that ask the SEAM's question use this one.
fn mask_as_count_bounded() -> String {
    let input = MASK_AS_COUNT.replace(
        "    let mut prev_ix = cur_ix.wrapping_sub(1);\n    prev_ix &= ring_buffer_mask;\n    prev_ix = prev_ix.wrapping_add(4);\n    *data.offset(prev_ix as isize) as u32\n",
        "    let mut i: usize = 0;\n    let mut s: u32 = 0;\n    while i < ring_buffer_mask {\n        s = s.wrapping_add(*data.offset(i as isize) as u32);\n        i = i.wrapping_add(1);\n    }\n    s\n",
    );
    assert_ne!(input, MASK_AS_COUNT, "the bounded callee is in");
    input
}

/// MKc — the control: the same call with a count that is not a mask keeps it
/// (re-pinned by relay 068 onto `mask_as_count_bounded`).
#[test]
fn w6l_mkc_a_count_that_is_not_a_mask_stays_licensed() {
    let input = mask_as_count_bounded()
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
/// (`let m = ringbuffer_mask;`) is still a mask (re-pinned by relay 068 onto
/// `mask_as_count_bounded`).
#[test]
fn w6l_mk2_a_mask_through_an_alias_is_not_a_count() {
    // The callee's formal is renamed so only the caller's alias names the mask.
    let input = mask_as_count_bounded()
        .replace("ring_buffer_mask", "window")
        .replace(
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

/// Relay 065 (R653-1, STOP 1): MK1's shape as 062 had it, the index masked in
/// place by the formal (`prev_ix &= ring_buffer_mask`) and read unchanged.
const MASK_PROVEN: &str = r###"
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

/// MK4 (relay 065, STOP 1) — a mask offered as a count goes to R477-6's masked
/// arm FIRST: the callee's index is masked by that same operand (`prev_ix &=
/// ring_buffer_mask`, read unchanged), so the arm's own proof holds and the
/// length is `mask + 1`, evidence-backed, not the fallback.
#[test]
fn w6l_mk4_a_proven_mask_takes_mask_plus_one() {
    let edits = edits(MASK_PROVEN);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && replacement.contains("ringbuffer_mask")
            && extent.contains("MaskPlusOne")),
        "{edits:#?}"
    );
    assert!(
        !edits
            .iter()
            .any(|(_, extent)| extent.contains("mask-as-count")),
        "{edits:#?}"
    );
}

/// MK6 (relay 065, STOP 1) — the masking must reach the read: a write to the
/// index AFTER the read, inside the loop that holds it, reaches the next
/// iteration's read, so the proof fails and the refusal stands.
#[test]
fn w6l_mk6_a_loop_write_after_the_read_is_not_a_proof() {
    let input = MASK_PROVEN.replace(
        "    let mut prev_ix = cur_ix.wrapping_sub(1);\n    prev_ix &= ring_buffer_mask;\n    *data.offset(prev_ix as isize) as u32\n",
        "    let mut prev_ix = cur_ix & ring_buffer_mask;\n    let mut sum = 0u32;\n    while sum < 8 {\n        sum = sum.wrapping_add(*data.offset(prev_ix as isize) as u32);\n        prev_ix = prev_ix.wrapping_add(1);\n    }\n    sum\n",
    );
    assert_ne!(input, MASK_PROVEN, "the loop replaces the body");
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:ringbuffer_mask")),
        "{edits:#?}"
    );
}

/// MK7 (relay 065, STOP 1) — a mask whose index is borrowed mutably between the
/// `&=` and the read is not proven: the borrow may write it.
#[test]
fn w6l_mk7_a_mutably_borrowed_index_is_not_a_proof() {
    let input = MASK_PROVEN
        .replace(
            "    prev_ix &= ring_buffer_mask;\n    *data",
            "    prev_ix &= ring_buffer_mask;\n    bump(&mut prev_ix);\n    *data",
        )
        .replace(
            "unsafe extern \"C\" fn FindAllMatchesH10",
            "unsafe fn bump(mut p: *mut usize) {\n    *p = (*p).wrapping_add(4);\n}\nunsafe extern \"C\" fn FindAllMatchesH10",
        );
    assert!(input.contains("bump(&mut prev_ix)"), "the borrow is in");
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:ringbuffer_mask")),
        "{edits:#?}"
    );
}

/// MK8 (relay 065, STOP 1) — a constant added to the masked local reads past
/// `mask`, so `mask + 1` does not cover it: not proven, the refusal stands.
#[test]
fn w6l_mk8_a_constant_past_the_masked_local_is_not_a_proof() {
    let input = MASK_PROVEN.replace(
        "*data.offset(prev_ix as isize)",
        "*data.offset((prev_ix + 1) as isize)",
    );
    assert_ne!(input, MASK_PROVEN, "the constant is in");
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:ringbuffer_mask")),
        "{edits:#?}"
    );
}

/// MK9 (relay 065 review, finding 3) — the proof is the function's, not one
/// read's: `data[prev_ix]` beside `data[prev_ix + 3]` reads past `mask`, so
/// the masked arm does not take it and the refusal stands.
#[test]
fn w6l_mk9_one_unproven_read_fails_the_function() {
    let input = MASK_PROVEN.replace(
        "    *data.offset(prev_ix as isize) as u32\n",
        "    (*data.offset(prev_ix as isize) as u32)\n        .wrapping_add(*data.offset((prev_ix + 3) as isize) as u32)\n",
    );
    assert_ne!(input, MASK_PROVEN, "the second read is in");
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:ringbuffer_mask")),
        "{edits:#?}"
    );
}

/// MK10 (relay 065 review, finding 6) — the in-place proof is for a MASK: a
/// companion whose formal is not mask-named (`window`) is a count, and
/// `v & window` does not make it `window + 1`.
#[test]
fn w6l_mk10_a_count_formal_is_not_made_a_mask() {
    let input = MASK_PROVEN
        .replace("ring_buffer_mask", "window")
        .replace("ringbuffer_mask", "ringbuffer_window");
    let edits = edits(&input);
    assert!(
        !edits
            .iter()
            .any(|(_, extent)| extent.contains("MaskPlusOne")),
        "{edits:#?}"
    );
}

/// MK11 (relay 065 review, finding 5) — the companion re-assigned in the
/// callee is not the caller's argument: not proven, the refusal stands.
#[test]
fn w6l_mk11_a_reassigned_companion_is_not_a_proof() {
    let input = MASK_PROVEN.replace(
        "    prev_ix &= ring_buffer_mask;\n",
        "    ring_buffer_mask = ring_buffer_mask.wrapping_mul(2).wrapping_add(1);\n    prev_ix &= ring_buffer_mask;\n",
    );
    assert_ne!(input, MASK_PROVEN, "the re-assignment is in");
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:ringbuffer_mask")),
        "{edits:#?}"
    );
}

/// MK12 (relay 065 review, finding 5) — a closure that captures the index may
/// write it: not proven, the refusal stands.
#[test]
fn w6l_mk12_a_captured_index_is_not_a_proof() {
    let input = MASK_PROVEN.replace(
        "    prev_ix &= ring_buffer_mask;\n",
        "    prev_ix &= ring_buffer_mask;\n    let mut bump = || prev_ix = prev_ix.wrapping_add(4);\n    bump();\n",
    );
    assert_ne!(input, MASK_PROVEN, "the closure is in");
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:ringbuffer_mask")),
        "{edits:#?}"
    );
}

/// MK13 (relay 065, the third review's B-2) — an inline pure mask of a local
/// (`data[(v & mask)]`) beside the in-place one is a proven read, not an
/// unproven one: the function keeps `mask + 1`.
#[test]
fn w6l_mk13_an_inline_local_mask_beside_the_in_place_one_keeps_mask_plus_one() {
    let input = MASK_PROVEN.replace(
        "    *data.offset(prev_ix as isize) as u32\n",
        "    let mut next_ix = cur_ix.wrapping_add(2);\n    (*data.offset(prev_ix as isize) as u32)\n        .wrapping_add(*data.offset((next_ix & ring_buffer_mask) as isize) as u32)\n",
    );
    assert_ne!(input, MASK_PROVEN, "the inline read is in");
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("MaskPlusOne")),
        "{edits:#?}"
    );
}

/// MK14 (relay 065; the final probe on brotli's `FindLongestMatchHROLLING_FAST`)
/// — a masked read proves one element only IN PLACE: `&*data.offset(prev_ix)`
/// handed to a callee that reads on (`FindMatchLengthWithLimit`), or a wide
/// read through a cast, reads past `mask`, so the in-place proof fails and
/// the refusal stands.
#[test]
fn w6l_mk14_a_masked_address_handed_on_is_not_a_proof() {
    let input = MASK_PROVEN
        .replace(
            "    *data.offset(prev_ix as isize) as u32\n",
            "    peek4(&*data.offset(prev_ix as isize))\n",
        )
        .replace(
            "unsafe extern \"C\" fn FindAllMatchesH10",
            "unsafe fn peek4(mut p: *const u8) -> u32 {\n    *(p as *const u32)\n}\nunsafe extern \"C\" fn FindAllMatchesH10",
        );
    assert!(input.contains("peek4(&*data"), "the hand-on is in");
    let edits = edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("mask-as-count:ringbuffer_mask")),
        "{edits:#?}"
    );
}

/// MK15 (relay 066, R666-2 STOP 1) — a NO-OP mask: brotli's
/// `BrotliCompressBufferQuality10` passes `let mask = !0 >> 1` over a flat
/// input. The callee's masking proof holds (MK4's shape), but `mask + 1` is a
/// §77 claim founded on a ring buffer of `mask + 1` elements, and a constant
/// mask says nothing about any buffer (`!0 >> 1` renders 2^63, past
/// `from_raw_parts`' `isize::MAX`). The seam refuses it under
/// `no-op-mask:<argument>`. MK15c — a ring mask computed from a formal keeps
/// `mask + 1`.
#[test]
fn w6l_mk15_mk15c_a_constant_mask_is_refused_a_ring_mask_is_not() {
    let no_op = MASK_PROVEN.replace(
        "    FindAllMatchesH10(ringbuffer, ringbuffer_mask, n)",
        "    let mut mask = !(0 as i32 as usize) >> 1 as i32;\n    FindAllMatchesH10(ringbuffer, mask, n)",
    );
    assert_ne!(no_op, MASK_PROVEN, "the constant mask is in");
    let edits = edits(&no_op);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("no-op-mask:mask")),
        "{edits:#?}"
    );
    assert!(
        !edits
            .iter()
            .any(|(_, extent)| extent.contains("MaskPlusOne")),
        "{edits:#?}"
    );
    let ring = MASK_PROVEN.replace(
        "    FindAllMatchesH10(ringbuffer, ringbuffer_mask, n)",
        "    let mut mask = (1 as usize) << ringbuffer_mask;\n    mask = mask.wrapping_sub(1);\n    FindAllMatchesH10(ringbuffer, mask, n)",
    );
    let ring_edits = self::edits(&ring);
    assert!(
        ring_edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("MaskPlusOne")),
        "{ring_edits:#?}"
    );
}

/// MK16 / MK17 / MK18 (relay 066 review, A1) — the no-op mask the seam must see
/// beyond a local initialized at the call:
/// - MK16: through the caller's FORMAL (brotli Quality10's `mask` reaches
///   inner seams as `ringbuffer_mask`): `Mid(addr, mask, n)` builds the slice
///   with its formal `mask`, and `Top` passes `!0 >> 1`;
/// - MK17: C89's declare-then-assign (`let mut mask = 0; mask = !0 >> 1;`);
/// - MK18: a constant path (`usize::MAX >> 1`).
#[test]
fn w6l_mk16_mk17_mk18_a_no_op_mask_through_a_formal_an_assignment_or_a_path() {
    let mid = MASK_PROVEN.replace(
        "pub unsafe fn Create(mut addr: usize, mut ringbuffer_mask: usize, mut n: usize) -> u32 {\n    let mut ringbuffer = addr as *const u8;\n    FindAllMatchesH10(ringbuffer, ringbuffer_mask, n)\n}",
        "unsafe fn Mid(mut addr: usize, mut ringbuffer_mask: usize, mut n: usize) -> u32 {\n    let mut ringbuffer = addr as *const u8;\n    FindAllMatchesH10(ringbuffer, ringbuffer_mask, n)\n}\npub unsafe fn Top(mut addr: usize, mut n: usize) -> u32 {\n    Mid(addr, !(0 as i32 as usize) >> 1 as i32, n)\n}",
    );
    assert_ne!(mid, MASK_PROVEN, "Mid and Top are in");
    let mid_edits = self::edits(&mid);
    assert!(
        mid_edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("no-op-mask:ringbuffer_mask")),
        "MK16: {mid_edits:#?}"
    );
    for (label, local) in [
        (
            "MK17",
            "    let mut mask: usize = 0 as i32 as usize;\n    mask = !(0 as i32 as usize) >> 1 as i32;\n",
        ),
        (
            "MK18",
            "    let mut mask: usize = usize::MAX >> 1 as i32;\n",
        ),
    ] {
        let input = MASK_PROVEN.replace(
            "    FindAllMatchesH10(ringbuffer, ringbuffer_mask, n)",
            &format!("{local}    FindAllMatchesH10(ringbuffer, mask, n)"),
        );
        let edits = self::edits(&input);
        assert!(
            edits.iter().any(|(replacement, extent)| replacement
                .contains("from_raw_parts(ringbuffer,")
                && extent.contains("no-op-mask:mask")),
            "{label}: {edits:#?}"
        );
    }
}

/// MK19 (relay 066 review, A1's control) — declare-then-assign with a RUNTIME
/// value is not a constant: the ring mask keeps `mask + 1`.
#[test]
fn w6l_mk19_a_runtime_mask_assigned_after_declaration_keeps_mask_plus_one() {
    let input = MASK_PROVEN.replace(
        "    FindAllMatchesH10(ringbuffer, ringbuffer_mask, n)",
        "    let mut mask: usize = 0 as i32 as usize;\n    mask = ringbuffer_mask;\n    FindAllMatchesH10(ringbuffer, mask, n)",
    );
    assert_ne!(input, MASK_PROVEN, "the assignment is in");
    let edits = self::edits(&input);
    assert!(
        edits.iter().any(|(replacement, extent)| replacement
            .contains("from_raw_parts(ringbuffer,")
            && extent.contains("MaskPlusOne")),
        "{edits:#?}"
    );
}
