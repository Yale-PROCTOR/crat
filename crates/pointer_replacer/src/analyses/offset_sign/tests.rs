use rustc_hash::FxHashMap;
use rustc_hir::{self as hir, ItemKind, OwnerNode, PatKind, intravisit};

use super::sign::offset_sign_analysis;
use crate::{analyses::mir_variable_grouping::SourceVarGroups, utils::rustc::RustProgram};

fn build_rust_program(tcx: rustc_middle::ty::TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = vec![];
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        if matches!(item.kind, ItemKind::Fn { .. }) {
            functions.push(item.owner_id.def_id);
        }
    }
    RustProgram {
        tcx,
        functions,
        structs: vec![],
    }
}

fn collect_bindings(body: &hir::Body<'_>) -> FxHashMap<hir::HirId, String> {
    struct BindingVisitor(FxHashMap<hir::HirId, String>);

    impl<'tcx> intravisit::Visitor<'tcx> for BindingVisitor {
        fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
            if let PatKind::Binding(_, hir_id, ident, _) = pat.kind {
                self.0.insert(hir_id, ident.name.to_string());
            }
            intravisit::walk_pat(self, pat);
        }
    }

    let mut v = BindingVisitor(FxHashMap::default());
    intravisit::walk_body(&mut v, body);
    v.0
}

fn run_analysis(code: &str) -> FxHashMap<(String, String), bool> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let rust_program = build_rust_program(tcx);
        let result = offset_sign_analysis(&rust_program);
        let source_var_groups = SourceVarGroups::new(&rust_program);
        let result = source_var_groups.postprocess_offset_signs(result.access_signs);
        let mut map = FxHashMap::default();
        for (&did, cursor_locals) in &result {
            let fn_name = tcx.item_name(did.to_def_id()).to_string();
            let hir_to_mir = utils::ir::map_thir_to_mir(did, false, tcx);
            let body = tcx.hir_body_owned_by(did);
            let bindings = collect_bindings(body);
            for (hir_id, local) in &hir_to_mir.binding_to_local {
                if cursor_locals.contains(*local) {
                    if let Some(var_name) = bindings.get(hir_id) {
                        map.insert((fn_name.clone(), var_name.clone()), true);
                    }
                }
            }
        }
        map
    })
    .unwrap()
}

fn needs_cursor(map: &FxHashMap<(String, String), bool>, fn_name: &str, var: &str) -> Option<bool> {
    map.get(&(fn_name.to_string(), var.to_string())).copied()
}

#[test]
fn lit_neg_needs_cursor() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32) {
            let _ = *p.offset(-1);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        Some(true),
        "p.offset(-1) should need a cursor"
    );
}

#[test]
fn lit_pos_is_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32) {
            let _ = *p.offset(1);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(1) should be safe"
    );
}

#[test]
fn named_const_pos_is_safe() {
    let map = run_analysis(
        "
        const SPX_OFFSET_LAYER: i32 = 3;

        pub unsafe fn f(p: *const i32) {
            let _ = *p.offset(SPX_OFFSET_LAYER as isize);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(SPX_OFFSET_LAYER as isize) with SPX_OFFSET_LAYER=3 should be safe"
    );
}

#[test]
fn lit_zero_is_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32) {
            let _ = *p.offset(0);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(0) should be safe"
    );
}

#[test]
fn usize_var_is_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, n: usize) {
            let _ = *p.offset(n as isize);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(n as isize) with n: usize should be safe"
    );
}

#[test]
fn isize_var_needs_cursor() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, n: isize) {
            let _ = *p.offset(n);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        Some(true),
        "p.offset(n) with unknown isize n should need a cursor"
    );
}

#[test]
fn isize_pos_is_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32) {
            let n: isize = 5;
            let _ = *p.offset(n);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(n) with n: isize = 5 should be safe"
    );
}

#[test]
fn isize_neg_needs_cursor() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32) {
            let n: isize = -3;
            let _ = *p.offset(n);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        Some(true),
        "p.offset(n) with n: isize = -3 should need a cursor"
    );
}

#[test]
fn loop_idx_is_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, len: usize) {
            for i in 0..len {
                let _ = *p.offset(i as isize);
            }
        }
        ",
    );
    // `i` starts at 0 and increments (usize), cast to isize → NonNeg → safe.
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(i as isize) in for i in 0..len should be safe"
    );
}

#[test]
fn mixed_needs_cursor() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32) {
            let _ = *p.offset(0);
            let _ = *p.offset(-1);
        }
        ",
    );
    // p.offset(0) ⊔ p.offset(-1) → NonPos → needs cursor
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        Some(true),
        "p.offset(0) then p.offset(-1) should need a cursor"
    );
}

#[test]
fn neg_cast_needs_cursor() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, n: usize) {
            let _ = *p.offset(-(n as isize));
        }
        ",
    );
    // -(n as isize) where n: usize → negate(NonNeg) = NonPos → needs cursor
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        Some(true),
        "p.offset(-(n as isize)) should need a cursor"
    );
}

#[test]
fn multi_ptr_p_needs_cursor_q_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, q: *const i32) {
            let _ = *p.offset(-1);
            let _ = *q.offset(1);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        Some(true),
        "p.offset(-1) should need a cursor"
    );
    assert_eq!(
        needs_cursor(&map, "f", "q"),
        None,
        "q.offset(1) should be safe"
    );
}

// ---------------------------------------------------------------------------
// Corpus tests — based on B01_organic real-world translated C code
// ---------------------------------------------------------------------------

/// bin2hex_lib: usize (size_t) loop counter → NonNeg → both pointers safe.
#[test]
fn corpus_bin2hex_usize_loop_safe() {
    let map = run_analysis(
        "
        pub type size_t = usize;

        pub unsafe fn bin2hex(
            mut hex: *mut u8,
            _hex_maxlen: size_t,
            mut bin: *const u8,
            bin_len: size_t,
        ) -> *mut u8 {
            let mut i: size_t = 0;
            while i < bin_len {
                let _ = *bin.offset(i as isize);
                *hex.offset((i * 2) as isize) = 0u8;
                *hex.offset((i * 2 + 1) as isize) = 0u8;
                i = i.wrapping_add(1);
            }
            *hex.offset((i * 2) as isize) = 0u8;
            hex
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "bin2hex", "bin"),
        None,
        "bin: usize loop index → NonNeg → safe"
    );
    assert_eq!(
        needs_cursor(&map, "bin2hex", "hex"),
        None,
        "hex: usize loop index *2 → NonNeg → safe"
    );
}

/// normalize_lib: c_int loop counter starting at 0, incremented via `i = i + 1`.
/// Fixpoint: Zero ⊔ (Zero+Pos=Pos) → NonNeg → safe.
#[test]
fn corpus_normalize_cint_loop_safe() {
    let map = run_analysis(
        "
        pub unsafe fn normalize(dest: *mut f32, src: *const f32, size: i32) {
            let mut sum = 0.0_f32;
            let mut i: i32 = 0;
            while i < size {
                sum += *src.offset(i as isize) * *src.offset(i as isize);
                i = i + 1;
            }
            if sum > 0.0 {
                let mut i: i32 = 0;
                while i < size {
                    *dest.offset(i as isize) = *src.offset(i as isize) * sum;
                    i = i + 1;
                }
            }
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "normalize", "src"),
        None,
        "src: c_int loop from 0 → NonNeg → safe"
    );
    assert_eq!(
        needs_cursor(&map, "normalize", "dest"),
        None,
        "dest: c_int loop from 0 → NonNeg → safe"
    );
}

/// merge_sort_lib: c_int parameters lo/split used directly as indices.
/// Unknown c_int param → Top → both input and output arrays need cursor.
#[test]
fn corpus_merge_sort_param_index_cursor() {
    let map = run_analysis(
        "
        #[derive(Copy, Clone)]
        pub struct Sprite {
            pub id: u64,
            pub bits: i32,
        }

        pub unsafe fn merge_sort_iter(
            a: *mut Sprite,
            lo: i32,
            split: i32,
            hi: i32,
            b: *mut Sprite,
        ) {
            let mut i: i32 = lo;
            let mut j: i32 = split;
            let mut k: i32 = lo;
            while k < hi {
                if i < split {
                    *b.offset(k as isize) = *a.offset(i as isize);
                    i += 1;
                } else {
                    *b.offset(k as isize) = *a.offset(j as isize);
                    j += 1;
                }
                k += 1;
            }
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "merge_sort_iter", "a"),
        Some(true),
        "a: offset by lo (unknown c_int param) → Top → needs cursor"
    );
    assert_eq!(
        needs_cursor(&map, "merge_sort_iter", "b"),
        Some(true),
        "b: offset by lo/k (unknown c_int param) → Top → needs cursor"
    );
}

/// hdr_compare_lib: only literal constant offsets 0, 1, 2.
/// All Zero/Pos → NonNeg → both header pointers safe.
#[test]
fn corpus_hdr_compare_literal_offsets_safe() {
    let map = run_analysis(
        "
        pub unsafe fn hdr_valid(h: *const u8) -> bool {
            *h.offset(0) == 0xff
                && (*h.offset(1) & 0xf0 == 0xf0 || *h.offset(1) & 0xfe == 0xe2)
                && (*h.offset(1) >> 1 & 3 != 0)
                && (*h.offset(2) >> 4 != 15)
                && (*h.offset(2) >> 2 & 3 != 3)
        }

        pub unsafe fn hdr_compare(h1: *const u8, h2: *const u8) -> i32 {
            (hdr_valid(h2)
                && (*h1.offset(1) ^ *h2.offset(1)) & 0xfe == 0
                && (*h1.offset(2) ^ *h2.offset(2)) & 0xc == 0) as i32
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "hdr_valid", "h"),
        None,
        "h: literal offsets 0..2 → NonNeg → safe"
    );
    assert_eq!(
        needs_cursor(&map, "hdr_compare", "h1"),
        None,
        "h1: literal offsets → safe"
    );
    assert_eq!(
        needs_cursor(&map, "hdr_compare", "h2"),
        None,
        "h2: literal offsets → safe"
    );
}

/// dequantize_granule_lib: choff alternates 576 ↔ (18−576 = −558).
/// Fixpoint: Pos ⊔ sign(18−Pos) = Pos ⊔ Top = Top → dst needs cursor.
#[test]
fn corpus_dequantize_alternating_choff_cursor() {
    let map = run_analysis(
        "
        pub unsafe fn dequantize(dst: *mut f32, _group_size: i32) {
            let mut choff: i32 = 576;
            let mut j: i32 = 0;
            while j < 4 {
                let _ = *dst.offset(choff as isize);
                choff = 18 - choff;
                j += 1;
            }
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "dequantize", "dst"),
        Some(true),
        "dst: choff alternates positive/negative → Top → needs cursor"
    );
}

/// synth_pair_lib: z accessed with large positive literal offsets (safe);
/// pcm accessed with (16*nch) where nch is unknown i32 param (Top → cursor).
#[test]
fn corpus_synth_pair_mixed() {
    let map = run_analysis(
        "
        pub unsafe fn synth_pair(pcm: *mut i16, nch: i32, z: *const f32) {
            let mut a = (*z.offset((14 * 64) as isize) - *z.offset(0)) * 29.0_f32;
            a += (*z.offset((1 * 64) as isize) + *z.offset((13 * 64) as isize)) * 213.0_f32;
            a += (*z.offset((12 * 64) as isize) - *z.offset((2 * 64) as isize)) * 459.0_f32;
            a += *z.offset((7 * 64) as isize) * 75038.0_f32;
            *pcm.offset(0) = a as i16;
            *pcm.offset((16 * nch) as isize) = a as i16;
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "synth_pair", "z"),
        None,
        "z: large positive literal offsets → NonNeg → safe"
    );
    assert_eq!(
        needs_cursor(&map, "synth_pair", "pcm"),
        Some(true),
        "pcm: offset by 16*nch (unknown c_int) → Top → needs cursor"
    );
}

/// flip_horizontal_lib: pix accessed with (w*i) and (w*(h−i−1)); w and h are
/// unknown i32 params → Top → pix needs cursor.
/// Local cursors a, b advanced with literal +1 → safe.
#[test]
fn corpus_flip_horizontal_mixed() {
    let map = run_analysis(
        "
        #[derive(Copy, Clone)]
        pub struct Pixel {
            pub r: u8,
            pub g: u8,
            pub b: u8,
            pub a: u8,
        }

        pub unsafe fn flip_horizontal(pix: *mut Pixel, w: i32, h: i32) {
            let flips = h / 2;
            let mut i: i32 = 0;
            while i < flips {
                let mut a = pix.offset((w * i) as isize);
                let mut b = pix.offset((w * (h - i - 1)) as isize);
                let mut j: i32 = 0;
                while j < w {
                    let t = *a;
                    *a = *b;
                    *b = t;
                    a = a.offset(1);
                    b = b.offset(1);
                    j += 1;
                }
                i += 1;
            }
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "flip_horizontal", "pix"),
        Some(true),
        "pix: (w*(h-i-1)) involves unknown i32 params → Top → needs cursor"
    );
    assert_eq!(
        needs_cursor(&map, "flip_horizontal", "a"),
        None,
        "a: advanced by literal +1 → Pos → safe"
    );
    assert_eq!(
        needs_cursor(&map, "flip_horizontal", "b"),
        None,
        "b: advanced by literal +1 → Pos → safe"
    );
}

/// wcscat_lib: ptr/src advanced by literal +1 (Pos → safe);
/// dst accessed with usize numElem (NonNeg → safe) and literal 0 (Zero → safe).
#[test]
fn corpus_wcscat_all_safe() {
    let map = run_analysis(
        "
        pub type size_t = usize;
        pub type wchar_t = i32;

        pub unsafe fn wcscat(
            mut dst: *mut wchar_t,
            numElem: size_t,
            mut src: *const wchar_t,
        ) -> i32 {
            let mut ptr: *mut wchar_t = dst;
            while ptr < dst.offset(numElem as isize) && *ptr != 0 {
                ptr = ptr.offset(1);
            }
            while ptr < dst.offset(numElem as isize) {
                let fresh = *src;
                src = src.offset(1);
                *ptr = fresh;
                ptr = ptr.offset(1);
                if fresh == 0 {
                    return 0;
                }
            }
            *dst.offset(0_i32 as isize) = 0;
            34
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "wcscat", "dst"),
        None,
        "dst: offset(numElem as isize) usize → NonNeg → safe"
    );
    assert_eq!(
        needs_cursor(&map, "wcscat", "ptr"),
        None,
        "ptr: offset(1) → Pos → safe"
    );
    assert_eq!(
        needs_cursor(&map, "wcscat", "src"),
        None,
        "src: offset(1) → Pos → safe"
    );
}

/// ima_parse_lib: chunk.offset(1) → Pos (safe), but then
/// chunk.offset(chunk_size as isize) where chunk_size is i64 param → Top.
/// Joined: Pos ⊔ Top = Top → chunk needs cursor.
#[test]
fn corpus_ima_parse_signed_stride_cursor() {
    let map = run_analysis(
        "
        pub type ima_s64_t = i64;

        pub unsafe fn ima_parse(mut chunk: *const u8, chunk_size: ima_s64_t) {
            // stride over a fixed-size header: literal 1 → Pos
            let _ = *chunk.offset(1_i32 as isize);
            // advance by signed chunk_size (unknown at compile time) → Top
            chunk = chunk.offset(chunk_size as isize);
            let _ = *chunk;
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "ima_parse", "chunk"),
        Some(true),
        "chunk: mixed literal+signed-param offsets → Top → needs cursor"
    );
}

// ---------------------------------------------------------------------------
// B02 corpus tests
// ---------------------------------------------------------------------------

/// fallcalc_lib (B02_synthetic):
/// process_array_reverse walks backward with ptr.offset(-1) → Neg → needs cursor.
/// foreach_sum uses idx: i32 starting at 0, incremented with += 1 → NonNeg → safe.
#[test]
fn corpus_fallcalc_reverse_walk_cursor() {
    let map = run_analysis(
        "
        pub unsafe fn process_array_reverse(end: *mut i32, count: i32) -> i32 {
            let mut sum = 0_i32;
            let mut ptr = end;
            let mut i = 0_i32;
            while i < count {
                sum += *ptr;
                ptr = ptr.offset(-1);
                i += 1;
            }
            sum
        }

        pub unsafe fn foreach_sum(array: *mut i32, count: i32) -> i32 {
            let mut total = 0_i32;
            let mut idx = 0_i32;
            while idx < count {
                total += *array.offset(idx as isize);
                idx += 1;
            }
            total
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "process_array_reverse", "ptr"),
        Some(true),
        "ptr: literal offset(-1) → Neg → needs cursor"
    );
    assert_eq!(
        needs_cursor(&map, "foreach_sum", "array"),
        None,
        "array: idx i32 init 0, += 1 tracked → NonNeg → safe"
    );
}

/// jumpnode_lib (B02_synthetic): process_backward mixes a usize and an unknown
/// i32 offset on the same pointer.
/// array: NonNeg (size:usize) ⊔ Top (start_offset:i32) = Top → needs cursor.
/// ptr: literal offset(-1) → Neg → needs cursor.
#[test]
fn corpus_jumpnode_mixed_offsets_cursor() {
    let map = run_analysis(
        "
        pub unsafe fn process_backward(
            array: *mut i32,
            size: usize,
            start_offset: i32,
        ) -> i32 {
            let mut sum = 0_i32;
            let mut ptr = array.offset(size as isize);
            let start = array.offset(start_offset as isize);
            while ptr > start {
                ptr = ptr.offset(-1);
                sum += *ptr;
            }
            sum
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "process_backward", "array"),
        Some(true),
        "array: usize offset (NonNeg) joined with i32 param (Top) → Top → needs cursor"
    );
    assert_eq!(
        needs_cursor(&map, "process_backward", "ptr"),
        Some(true),
        "ptr: literal offset(-1) → Neg → needs cursor"
    );
}

/// arr_del_lib (B02_organic) — stb_ds "header before data" pattern.
/// arr_header_access: offset(-1) literal → Neg → data needs cursor.
/// arr_skip_header:   offset(sizeof(Header) as usize) → NonNeg → raw safe.
/// arr_prev_elem:     offset(-(elemsize as isize)) where elemsize:usize → NonPos → needs cursor.
#[test]
fn corpus_arr_del_header_pattern() {
    let map = run_analysis(
        "
        #[repr(C)]
        pub struct ArrayHeader {
            pub length: usize,
            pub capacity: usize,
        }

        pub unsafe fn arr_header_access(data: *mut u8) -> usize {
            let hdr = (data as *mut ArrayHeader).offset(-1);
            (*hdr).length
        }

        pub unsafe fn arr_skip_header(raw: *mut u8) -> *mut u8 {
            raw.offset(core::mem::size_of::<ArrayHeader>() as usize as isize)
        }

        pub unsafe fn arr_prev_elem(a: *mut u8, elemsize: usize) {
            let _ = (a as *mut u8).offset(-(elemsize as isize));
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "arr_header_access", "data"),
        Some(true),
        "data: offset(-1) → Neg → needs cursor"
    );
    assert_eq!(
        needs_cursor(&map, "arr_skip_header", "raw"),
        None,
        "raw: offset(sizeof as usize) → NonNeg → safe"
    );
    assert_eq!(
        needs_cursor(&map, "arr_prev_elem", "a"),
        Some(true),
        "a: offset(-(elemsize as isize)) → NonPos → needs cursor"
    );
}

/// AssignOp fix: `i += 1` is now captured as a binding for `i`.
/// Fixpoint: Zero (init) ⊔ Pos (rhs=1) = NonNeg → p accessed with NonNeg → safe.
#[test]
fn assignop_loop_is_safe() {
    let map = run_analysis(
        "
        pub unsafe fn sum_forward(p: *const i32, len: i32) -> i32 {
            let mut total = 0_i32;
            let mut i = 0_i32;
            while i < len {
                total += *p.offset(i as isize);
                i += 1;
            }
            total
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "sum_forward", "p"),
        None,
        "p: i+=1 loop counter → NonNeg → safe"
    );
}

/// branch condition narrowing: p.offset(x) inside `if x > 0 { }` is safe
#[test]
fn branch_gt_zero_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, x: i32) {
            if x > 0 {
                let _ = *p.offset(x as isize);
            }
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(x) inside if x > 0 should be safe (x is Pos)"
    );
}

/// branch condition: p.offset(x) outside a guard still needs cursor
#[test]
fn branch_signed_param_outside_guard_needs_cursor() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, x: i32) {
            let _ = *p.offset(x as isize);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        Some(true),
        "p.offset(x) with unconstrained i32 x should need cursor"
    );
}

/// ternary pattern: count = if param > 0 { param } else { 5 }
/// count is always positive, so p.offset(count) is safe
#[test]
fn branch_ternary_always_positive_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, param: i32) {
            let count = if param > 0 { param } else { 5 };
            let _ = *p.offset(count as isize);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(count) where count = if param > 0 {{ param }} else {{ 5 }} should be safe"
    );
}

/// caller passes positive constant, callee uses it inside a guard: safe
#[test]
fn branch_caller_positive_callee_guarded_safe() {
    let map = run_analysis(
        "
        unsafe fn inner(p: *const i32, shift: i32) {
            if shift > 0 {
                let _ = *p.offset(shift as isize);
            }
        }
        pub unsafe fn outer(p: *const i32) {
            inner(p, 3);
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "inner", "p"),
        None,
        "inner: shift=3 from caller, used inside if shift>0, should be safe"
    );
}

/// root_local fix: `(*s).buf.offset(n)` — root_local detects (*deref).field and
/// returns None, so `s` is never attributed any offset and never flagged.
#[test]
fn struct_field_deref_not_flagged() {
    let map = run_analysis(
        "
        pub struct Buf {
            pub buf: *mut i32,
            pub len: i32,
        }

        pub unsafe fn use_field(s: *mut Buf, n: i32) -> i32 {
            *(*s).buf.offset(n as isize)
        }
        ",
    );
    // `s` should NOT appear in the offset-sign output at all (root_local → None).
    assert_ne!(
        needs_cursor(&map, "use_field", "s"),
        Some(true),
        "s: struct pointer — (*s).buf.offset should not be attributed to s"
    );
}

/// false-edge narrowing: else branch of `if x < 0` implies x >= 0, so offset is safe.
#[test]
fn branch_false_edge_ge_zero_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, x: i32) {
            if x < 0 {
                let _ = 0;
            } else {
                let _ = *p.offset(x as isize);
            }
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(x) in else branch of if x < 0 should be safe (x is NonNeg)"
    );
}

/// local-vs-local condition: if x > y and y == 0, then x is positive on true branch.
#[test]
fn branch_local_rhs_zero_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, x: i32) {
            let y: i32 = 0;
            if x > y {
                let _ = *p.offset(x as isize);
            }
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(x) inside if x > y with y=0 should be safe"
    );
}

/// flipped extraction: `0 < x` should normalize to `x > 0` and narrow x to positive.
#[test]
fn branch_flipped_constant_lhs_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, x: i32) {
            if 0 < x {
                let _ = *p.offset(x as isize);
            }
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "p.offset(x) inside if 0 < x should be safe"
    );
}

/// copy-cycle robustness: copy-equivalence collection should not loop and should
/// narrow all alias locals together on the guarded branch.
#[test]
fn branch_copy_cycle_aliases_safe() {
    let map = run_analysis(
        "
        pub unsafe fn f(p: *const i32, x: i32) {
            let mut a = x;
            let mut b = x;
            a = b;
            b = a;
            if a > 0 {
                let _ = *p.offset(b as isize);
            }
        }
        ",
    );
    assert_eq!(
        needs_cursor(&map, "f", "p"),
        None,
        "copy-related aliases in guarded branch should stay non-negative for offset use"
    );
}
