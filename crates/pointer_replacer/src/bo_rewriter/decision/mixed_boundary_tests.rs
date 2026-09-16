//! W-C4: a subject whose calls mix converting targets (the seam's safe→safe
//! edges) with raw targets (T1 / T2 bridges). Reduced from brotli's decoder
//! `SafeReadSymbolCodeLengths` → `ProcessSingleCodeLength` (`h`, the arena
//! pointer, at `54e9a786`: `borrowed-into-raw-param`).

const DECODE: &str = r###"
#[repr(C)]
pub struct BrotliMetablockHeaderArena {
    pub repeat_code_len: u32, pub prev_code_len: u32, pub symbol: u32, pub repeat: u32, pub space: u32,
    pub symbol_lists: *mut u16, pub symbols_lists_array: [u16; 720], pub next_symbol: [i32; 32],
    pub code_length_histo: [u16; 16],
}
#[repr(C)]
pub struct BrotliBitReader { pub val_: u64, pub bit_pos_: u32 }
#[repr(C)]
pub struct BrotliDecoderStateStruct { pub br: BrotliBitReader, pub arena: BrotliMetablockHeaderArena }
unsafe fn ProcessSingleCodeLength(code_len: u32, symbol: *mut u32, repeat: *mut u32, space: *mut u32,
    prev_code_len: *mut u32, symbol_lists: *mut u16, code_length_histo: *mut u16, next_symbol: *mut i32) {
    *repeat = 0;
    if code_len != 0 {
        *symbol_lists.offset(*next_symbol.offset(code_len as isize) as isize) = *symbol as u16;
        *next_symbol.offset(code_len as isize) = *symbol as i32;
        *prev_code_len = code_len;
        *space = (*space).wrapping_sub(32768u32 >> code_len);
        *code_length_histo.offset(code_len as isize) = (*code_length_histo.offset(code_len as isize)).wrapping_add(1);
    }
    *symbol = (*symbol).wrapping_add(1);
}
unsafe fn BrotliGetBitsUnmasked(br: *mut BrotliBitReader) -> u32 { ((*br).val_ >> (*br).bit_pos_) as u32 }
unsafe fn BrotliDropBits(br: *mut BrotliBitReader, n: u32) { (*br).bit_pos_ = (*br).bit_pos_.wrapping_add(n); }
pub unsafe fn SafeReadSymbolCodeLengths(alphabet_size: u32, s: *mut BrotliDecoderStateStruct) -> i32 {
    let br: *mut BrotliBitReader = &mut (*s).br;
    let h: *mut BrotliMetablockHeaderArena = &mut (*s).arena;
    while (*h).symbol < alphabet_size && (*h).space > 0 {
        let code_len = BrotliGetBitsUnmasked(br) & 15;
        BrotliDropBits(br, 4);
        if code_len < 16 {
            ProcessSingleCodeLength(code_len, &mut (*h).symbol, &mut (*h).repeat, &mut (*h).space,
                &mut (*h).prev_code_len, (*h).symbol_lists, ((*h).code_length_histo).as_mut_ptr(),
                ((*h).next_symbol).as_mut_ptr());
        } else {
            return 0;
        }
    }
    1
}
"###;

fn fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{DECODE}"
    )
}

/// Reduced from brotli's decoder `CopyUncompressedBlockToOutput` (`s`, at
/// `54e9a786`: `borrowed-into-raw-param`): `s` converts at
/// `BrotliEnsureRingBuffer(s)` / `WriteRingBuffer(s, …)`, its `br` field is
/// borrowed into `BrotliCopyBytes(…, &mut (*s).br, n)` whose parameter stays raw.
const OUTPUT: &str = r###"
#[repr(C)]
pub struct BrotliBitReader { pub val_: u64, pub bit_pos_: u32, pub next_in: *const u8, pub avail_in: usize }
#[repr(C)]
pub struct BrotliDecoderStateInternal { pub br: BrotliBitReader, pub substate_uncompressed: i32, pub meta_block_remaining_len: i32,
    pub pos: i32, pub ringbuffer_size: i32, pub window_bits: i32, pub ringbuffer: *mut u8 }
unsafe fn BrotliEnsureRingBuffer(s: *mut BrotliDecoderStateInternal) -> i32 { if (*s).ringbuffer_size == 0 { (*s).ringbuffer_size = 1 << (*s).window_bits; } 1 }
unsafe fn BrotliGetRemainingBytes(br: *mut BrotliBitReader) -> u32 { ((*br).avail_in as u32).wrapping_add(8) }
unsafe fn BrotliCopyBytes(dest: *mut u8, br: *mut BrotliBitReader, num: usize) {
    let mut i: usize = 0;
    let src: *const u8 = (*br).next_in;
    while i < num {
        *dest.offset(i as isize) = *src.offset(i as isize);
        i = i.wrapping_add(1);
    }
    (*br).next_in = src.offset(num as isize);
    (*br).avail_in = (*br).avail_in.wrapping_sub(num);
}
unsafe fn WriteRingBuffer(s: *mut BrotliDecoderStateInternal, available_out: *mut usize, force: i32) -> i32 {
    if *available_out < (*s).pos as usize { return 2; }
    *available_out = (*available_out).wrapping_sub((*s).pos as usize);
    (*s).pos = 0;
    1
}
pub unsafe fn CopyUncompressedBlockToOutput(available_out: *mut usize, s: *mut BrotliDecoderStateInternal) -> i32 {
    if BrotliEnsureRingBuffer(s) == 0 { return 3; }
    loop {
        if (*s).substate_uncompressed == 0 {
            let mut nbytes = BrotliGetRemainingBytes(&mut (*s).br) as i32;
            if nbytes > (*s).meta_block_remaining_len { nbytes = (*s).meta_block_remaining_len; }
            if (*s).pos + nbytes > (*s).ringbuffer_size { nbytes = (*s).ringbuffer_size - (*s).pos; }
            BrotliCopyBytes(&mut *((*s).ringbuffer).offset((*s).pos as isize), &mut (*s).br, nbytes as usize);
            (*s).pos += nbytes;
            (*s).meta_block_remaining_len -= nbytes;
            if (*s).pos < (1i32) << (*s).window_bits {
                if (*s).meta_block_remaining_len == 0 { return 1; }
                return 4;
            }
            (*s).substate_uncompressed = 1;
        }
        let result = WriteRingBuffer(s, available_out, 0);
        if result != 1 { return result; }
        (*s).substate_uncompressed = 0;
    }
}
"###;

fn output_fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{OUTPUT}"
    )
}

fn decisions(input: &str) -> Vec<(String, super::Decision)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        crate::bo_rewriter::decide_table(tcx)
            .unwrap()
            .entries
            .iter()
            .map(|(s, d)| (s.label.clone(), d.clone()))
            .collect()
    })
    .unwrap()
}
fn decision<'a>(table: &'a [(String, super::Decision)], label: &str) -> &'a super::Decision {
    &table
        .iter()
        .find(|(l, _)| l == label)
        .unwrap_or_else(|| panic!("{label}"))
        .1
}
fn flat(emitted: &str) -> String {
    emitted.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// `h` mixes converting targets (`symbol`) with raw targets (`symbol_lists`):
/// the raw sites are bridged, the converting sites are the seam's.
#[test]
fn w5c_mixed_boundary_decoder_arena_view_delivers() {
    let input = fixture();
    let table = decisions(&input);
    assert!(
        matches!(
            decision(&table, "SafeReadSymbolCodeLengths::h"),
            super::Decision::Ref { mutable: true }
        ),
        "{:?}",
        decision(&table, "SafeReadSymbolCodeLengths::h")
    );
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let text = flat(&emitted);
    assert!(
        text.contains("let h: &mut BrotliMetablockHeaderArena = &mut (*s).arena;"),
        "{emitted}"
    );
    assert!(
        text.contains("let __crat_raw: *mut u16 = ((*h).symbol_lists) as *mut u16;"),
        "{emitted}"
    );
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    if let Ok(root) = std::env::var("CRAT_W5C_FIXTURE_CAPTURE") {
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(format!("{root}/decoder-arena-original.rs"), &input).unwrap();
        std::fs::write(format!("{root}/decoder-arena-emitted.rs"), &emitted).unwrap();
    }
}

/// `s` is borrowed through (`&mut (*s).br`, `&mut *((*s).ringbuffer).offset(…)`)
/// into targets that convert to other safe forms; those are their families'
/// adapter questions, never a raw seam of `s`.
#[test]
fn w5c_mixed_boundary_output_state_delivers() {
    let input = output_fixture();
    let table = decisions(&input);
    assert!(
        matches!(
            decision(&table, "CopyUncompressedBlockToOutput::s"),
            super::Decision::Ref { mutable: true }
        ),
        "{:?}",
        decision(&table, "CopyUncompressedBlockToOutput::s")
    );
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let text = flat(&emitted);
    // Where the owner's class is NOT applied (this reduction alone: its
    // `available_out` sibling flows into `WriteRingBuffer`'s raw parameter)
    // the decided form shows at the bridged call, `&mut *s`; where the
    // composition applies it (batch 9's frame: `s: &mut …` in the signature)
    // the argument is already `&mut` and needs no bridge. Both are this
    // rule's claim — `s` reaches the converting callee as a reference.
    assert!(
        text.contains("BrotliEnsureRingBuffer(&mut *s) == 0")
            || text.contains("BrotliEnsureRingBuffer(s) == 0"),
        "{emitted}"
    );
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    if let Ok(root) = std::env::var("CRAT_W5C_FIXTURE_CAPTURE") {
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(format!("{root}/output-state-original.rs"), &input).unwrap();
        std::fs::write(format!("{root}/output-state-emitted.rs"), &emitted).unwrap();
    }
}

/// A raw site the boundary cannot bridge still refuses the node, even when
/// the hypothetical table converts the callee's parameter: `keep::p` degrades
/// `escapes-via-static-store` in production, so the site is a raw target at
/// the terminal and its positive-retention block must vote.
#[test]
fn w5c_mixed_boundary_retained_raw_site_still_refuses() {
    let input = fixture()
        .replace(
            "unsafe fn BrotliGetBitsUnmasked",
            "static mut KEPT: *mut u32 = 0 as *mut u32;\nunsafe fn keep(p: *mut u32) { KEPT = p; }\nunsafe fn BrotliGetBitsUnmasked",
        )
        .replace("        if code_len < 16 {", "        keep(&mut (*h).space);\n        if code_len < 16 {");
    let table = decisions(&input);
    assert!(
        matches!(
            decision(&table, "keep::p"),
            super::Decision::Degraded(super::Degradation {
                reason: super::DegradeReason::SilentCoercion { .. },
                ..
            })
        ),
        "{:?}",
        decision(&table, "keep::p")
    );
    assert!(
        matches!(
            decision(&table, "SafeReadSymbolCodeLengths::h"),
            super::Decision::Degraded(super::Degradation {
                reason: super::DegradeReason::SilentCoercion { .. },
                ..
            })
        ),
        "{:?}",
        decision(&table, "SafeReadSymbolCodeLengths::h")
    );
}
