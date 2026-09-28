//! wave-6l relay 061 (R631-4): the seam never licenses an only-zero companion
//! (iv), and a pointer read past a masked index by a runtime length stays raw
//! under `held:masked-index-runtime-length` (the ring-buffer audit's (a)).

fn fixture(body: &str) -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{body}"
    )
}

fn reason(rows: &[(String, bool, String)], name: &str) -> String {
    rows.iter()
        .find(|(n, p, _)| n == name && *p)
        .map(|(_, _, r)| r.clone())
        .unwrap_or_else(|| panic!("no parameter {name}: {rows:?}"))
}

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// brotli's H10 readers, reduced: `StoreAndFindMatches` reads
/// `data[cur_ix_masked + len]`; `FindAllMatches` hands `&data[cur_ix_masked]`
/// to `FindMatchLengthWithLimit`, which walks `limit` bytes; `StoreH10` and
/// `StoreRange` hand `data` on bare.
const RING: &str = r###"
unsafe fn FindMatchLengthWithLimit(mut s1: *const u8, mut s2: *const u8, mut limit: usize) -> usize {
    let mut matched = 0usize;
    while matched < limit && *s1.offset(matched as isize) == *s2 {
        s2 = s2.offset(1);
        matched = matched.wrapping_add(1);
    }
    matched
}
unsafe fn StoreAndFindMatches(data: *const u8, cur_ix: usize, ring_buffer_mask: usize, max_length: usize) -> usize {
    let cur_ix_masked = cur_ix & ring_buffer_mask;
    let mut len = 0usize;
    while len < max_length && *data.offset(cur_ix_masked.wrapping_add(len) as isize) != 0 {
        len = len.wrapping_add(1);
    }
    len
}
unsafe fn StoreH10(data: *const u8, mask: usize, ix: usize) -> usize {
    StoreAndFindMatches(data, ix, mask, 128)
}
unsafe fn StoreRange(data: *const u8, mask: usize, ix_start: usize, ix_end: usize) {
    let mut i = ix_start;
    while i < ix_end {
        StoreH10(data, mask, i);
        i = i.wrapping_add(1);
    }
}
unsafe fn FindAllMatches(data: *const u8, ring_buffer_mask: usize, cur_ix: usize, max_length: usize) -> usize {
    let cur_ix_masked = cur_ix & ring_buffer_mask;
    let prev_ix = cur_ix.wrapping_sub(1) & ring_buffer_mask;
    FindMatchLengthWithLimit(&*data.offset(prev_ix as isize), &*data.offset(cur_ix_masked as isize), max_length)
}
pub struct Ring {
    pub buffer: [u8; 4224],
}
pub unsafe fn Compress(r: *mut Ring, n: usize) -> usize {
    let data = ((*r).buffer).as_ptr();
    StoreRange(data, 4095, 0, n);
    FindAllMatches(data, 4095, n, 128)
}
"###;

/// M1 — every reader of the chain is held, and the reason names it.
#[test]
fn w6l_mask_m1_a_read_past_a_masked_index_by_a_runtime_length_is_held() {
    let rows = crate::bo_rewriter::emit_tests::decisions_of(&fixture(RING));
    for name in ["data"] {
        let held: Vec<_> = rows
            .iter()
            .filter(|(n, p, _)| n == name && *p)
            .map(|(_, _, r)| r.clone())
            .collect();
        assert_eq!(held.len(), 4, "{rows:#?}");
        assert!(
            held.iter().all(|r| r == "held:masked-index-runtime-length"),
            "{rows:#?}"
        );
    }
}

/// C1 — R477-6's own arm: a masked index plus a CONSTANT is not this hold's.
#[test]
fn w6l_mask_c1_a_masked_index_plus_a_constant_is_not_held() {
    let input = fixture(
        r###"
unsafe fn Store(data: *const u8, mask: usize, ix: usize) -> u32 {
    let at = (ix & mask) as isize;
    (*data.offset(at) as u32).wrapping_add(*data.offset(at + 3) as u32)
}
unsafe fn Range(data: *const u8, mask: usize, n: usize) -> u32 {
    let mut i = 0usize;
    let mut s = 0u32;
    while i < n {
        s = s.wrapping_add(Store(data, mask, i));
        i = i.wrapping_add(1);
    }
    s
}
pub unsafe fn run(n: usize) -> u32 {
    let buf: [u8; 4096] = [7; 4096];
    Range(buf.as_ptr(), 4095, n)
}
"###,
    );
    let rows = crate::bo_rewriter::emit_tests::decisions_of(&input);
    for (name, row) in rows.iter().filter(|(_, p, _)| *p).map(|(n, _, r)| (n, r)) {
        assert_ne!(row, "held:masked-index-runtime-length", "{name}: {rows:#?}");
    }
}

/// C2 — a pointer at a masked index handed to a FIXED-width reader (brotli's
/// `HashBytesH10`: one `u32`) is not a runtime length.
#[test]
fn w6l_mask_c2_a_fixed_width_reader_at_a_masked_index_is_not_held() {
    let input = fixture(
        r###"
unsafe fn HashBytes(data: *const u8) -> u32 {
    *(data as *const u32)
}
unsafe fn Store(data: *const u8, mask: usize, ix: usize) -> u32 {
    let cur_ix_masked = ix & mask;
    HashBytes(&*data.offset(cur_ix_masked as isize))
}
pub unsafe fn run(n: usize) -> u32 {
    let buf: [u8; 4096] = [7; 4096];
    Store(buf.as_ptr(), 4091, n)
}
"###,
    );
    let rows = crate::bo_rewriter::emit_tests::decisions_of(&input);
    for (name, row) in rows.iter().filter(|(_, p, _)| *p).map(|(n, _, r)| (n, r)) {
        assert_ne!(row, "held:masked-index-runtime-length", "{name}: {rows:#?}");
    }
}

/// The reduced Zopfli root (batch 50's `(gap) as usize`, `gap = 0`): a
/// chain whose companion is licensed, handed a local only ever `0`.
const ZERO_ROOT: &str = r###"
unsafe fn Evaluate(gap: usize, c: *const i32) -> i32 {
    *c.offset(3 as isize)
}
unsafe fn Iterate(n: usize, gap: usize, mut dist_cache: *const i32) -> i32 {
    let s = *dist_cache.offset(0 as isize);
    s.wrapping_add(Evaluate(gap, dist_cache))
}
pub struct State {
    pub dc: *mut i32,
}
pub unsafe fn Hq(n: usize, s: *mut State) -> i32 {
    let mut gap = 0 as usize;
    Iterate(n, gap, (*s).dc)
}
pub unsafe fn Other(n: usize, s: *mut State, g: usize) -> i32 {
    Iterate(n, g, (*s).dc)
}
"###;

/// Z1 (iv) — a companion only ever `0` is not licensed: the root takes the
/// receipted fallback, never an empty slice.
#[test]
fn w6l_mask_z1_an_only_zero_companion_is_not_licensed() {
    let source =
        crate::bo_rewriter::emit_tests::ast_emitted_source_of(&fixture(ZERO_ROOT)).unwrap();
    let flat = flat(&source);
    assert!(!flat.contains("(gap) as usize"), "{flat}");
    assert!(
        crate::bo_rewriter::verify::type_checks_str(&source),
        "{source}"
    );
}

/// Z2 (iv) — the literal `0` spelled at the call is not licensed either.
#[test]
fn w6l_mask_z2_a_literal_zero_companion_is_not_licensed() {
    let input = fixture(&ZERO_ROOT.replace(
        "    let mut gap = 0 as usize;\n    Iterate(n, gap, (*s).dc)",
        "    Iterate(n, 0 as usize, (*s).dc)",
    ));
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let flat = flat(&source);
    assert!(!flat.contains("(0 as usize) as usize"), "{flat}");
}

/// Zc (iv) — the control: a companion that is not only `0` keeps its licence.
#[test]
fn w6l_mask_zc_a_companion_that_may_be_nonzero_stays_licensed() {
    let source =
        crate::bo_rewriter::emit_tests::ast_emitted_source_of(&fixture(ZERO_ROOT)).unwrap();
    assert!(flat(&source).contains("(g) as usize"), "{source}");
}

/// Zc2 (iv)'s control — a local initialized `0` and later assigned a runtime
/// value may be non-zero: its licence stands.
#[test]
fn w6l_mask_zc2_a_zero_initialized_local_assigned_later_stays_licensed() {
    let input = fixture(&ZERO_ROOT.replace(
        "    let mut gap = 0 as usize;\n    Iterate(n, gap, (*s).dc)",
        "    let mut gap = 0 as usize;\n    if n > 3 {\n        gap = n;\n    }\n    Iterate(n, gap, (*s).dc)",
    ));
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(flat(&source).contains("(gap) as usize"), "{source}");
}

/// Zc3 (iv)'s control — a borrowed local may be written through the borrow:
/// its licence stands.
#[test]
fn w6l_mask_zc3_a_borrowed_zero_local_stays_licensed() {
    let input = fixture(&ZERO_ROOT.replace(
        "    let mut gap = 0 as usize;\n    Iterate(n, gap, (*s).dc)",
        "    let mut gap = 0 as usize;\n    Widen(&mut gap, n);\n    Iterate(n, gap, (*s).dc)",
    ).replace(
        "pub unsafe fn Other(",
        "unsafe fn Widen(g: *mut usize, n: usize) {\n    *g = n;\n}\npub unsafe fn Other(",
    ));
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(flat(&source).contains("(gap) as usize"), "{source}");
}

/// M2 — the runtime-length read inside a closure the function runs is the
/// function's read.
#[test]
fn w6l_mask_m2_a_read_in_a_closure_is_held() {
    let input = fixture(
        r###"
unsafe fn Reader(data: *const u8, ix: usize, mask: usize, len: usize) -> u8 {
    let at = ix & mask;
    let read = |k: usize| *data.offset(at.wrapping_add(k) as isize);
    read(len)
}
pub unsafe fn run(n: usize) -> u8 {
    let buf: [u8; 4096] = [7; 4096];
    Reader(buf.as_ptr(), n, 4095, 3)
}
"###,
    );
    let rows = crate::bo_rewriter::emit_tests::decisions_of(&input);
    assert_eq!(
        reason(&rows, "data"),
        "held:masked-index-runtime-length",
        "{rows:#?}"
    );
}
