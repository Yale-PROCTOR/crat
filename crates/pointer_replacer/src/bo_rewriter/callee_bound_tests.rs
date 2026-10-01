//! **R707 / R717-1 — wave-4 build 1: `len-callee-bound`.** The extent a
//! function's own accesses prove, at the three call points: the seam's
//! raw-argument arm, the exposure wrapper's view of an entry formal, and the
//! declaration planner (whose nested rows N1 relocates to the wrapper).
//!
//! `W4CB-*` are the RED witnesses (each one emitted `FALLBACK_SLICE_EXTENT` at
//! the base `2961c2ec0`). `W4CB-F*` are the fault controls: each one fails when
//! the guard it names is removed from `decision/callee_bound.rs`.

use super::{A5Mode, WholeProgramAttestation};

const PRE: &str =
    "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments)]\n";

/// The production rewrite/verify entry on a single-file program.
fn emitted(src: &str) -> String {
    match super::rewrite_m1(src) {
        super::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("fixture must survive production verify: {other:?}"),
    }
}

/// The same entry under the frozen benchmark's closed world, which is what
/// gives a function-pointer table's members their exposure wrappers.
fn emitted_closed_world(src: &str) -> String {
    let dir = std::env::temp_dir().join(format!(
        "crat-callee-bound-{}-{}",
        std::process::id(),
        src.len()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, src).unwrap();
    let outcome = super::rewrite_m1_path_a5_injected(
        &root,
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        &|_| {},
    );
    std::fs::remove_dir_all(&dir).unwrap();
    let super::RewriteOutcome::Emitted { source, .. } = outcome else {
        panic!("closed-world emission unavailable: {outcome:?}");
    };
    source
}

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

// ---------------------------------------------------------------------------
// The seam's raw-argument arm.
// ---------------------------------------------------------------------------

/// **W4CB-1 — seam × (a) constant, `may`.** The callee reads elements 0 and 2,
/// behind a branch: the raw argument takes `3`, not the fallback. The signed
/// delta `k` keeps the argument a raw expression (R394-2), so this is the raw
/// arm and not the forward view.
#[test]
fn w4cb_1_seam_constant_indices_bound_a_raw_argument() {
    let src = format!(
        "{PRE}\
         pub unsafe fn pick(flag: i32, p: *const i32) -> i32 {{\n\
         \x20   if flag > 0 {{ *p.offset(0) + *p.offset(2) }} else {{ 0 }}\n\
         }}\n\
         pub unsafe fn caller(base: *const i32, k: isize) -> i32 {{ pick(1, base.offset(k)) }}\n"
    );
    let out = flat(&emitted(&src));
    assert!(
        out.contains("from_raw_parts(base.offset(k), (3i128.max(0) as usize))"),
        "{out}"
    );
    assert!(
        !out.contains(
            "pick(1, core::slice::from_raw_parts(base.offset(k), crate::FALLBACK_SLICE_EXTENT))"
        ),
        "{out}"
    );
}

/// **W4CB-2 — seam × (a) constant, `must`.** A straight-line callee (R677-6's
/// shape): every access runs on every call, so the tag is `must`.
#[test]
fn w4cb_2_seam_straight_line_constant_is_must() {
    let src = format!(
        "{PRE}\
         pub unsafe fn read32(buffer: *const u8) -> u32 {{\n\
         \x20   return (*buffer.offset(0 as i32 as isize) as u32) << 24\n\
         \x20       | *buffer.offset(3 as i32 as isize) as u32;\n\
         }}\n\
         pub unsafe fn caller(in_0: *mut u8, k: isize) -> u32 {{ read32(in_0.offset(k)) }}\n"
    );
    let out = flat(&emitted(&src));
    assert!(
        out.contains("from_raw_parts(in_0.offset(k), (4i128.max(0) as usize))"),
        "{out}"
    );
}

/// **W4CB-3 — seam × (b) loop.** `while i < n` bounds every index; `n` is not
/// adjacent to the pointer, so no companion licence answers first. The call's
/// own argument instantiates the bound.
#[test]
fn w4cb_3_seam_loop_bound_is_instantiated_with_the_call_s_argument() {
    let src = format!(
        "{PRE}\
         pub unsafe fn total(n: usize, flag: i32, p: *const i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: usize = 0;\n\
         \x20   while i < n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn caller(base: *const i32, count: usize, k: isize) -> i32 {{\n\
         \x20   total(count, 1, base.offset(k))\n\
         }}\n"
    );
    let out = flat(&emitted(&src));
    assert!(
        out.contains("from_raw_parts(base.offset(k), (((count) as i128).max(0) as usize))"),
        "{out}"
    );
}

/// **W4CB-4 — seam × (c) composition.** `outer` passes its pointer on to a
/// local callee whose loop bound is its own second parameter; `outer` passes
/// the literal `4` there, so `outer`'s bound is `4`.
#[test]
fn w4cb_4_seam_bound_composes_through_a_local_callee() {
    let src = format!(
        "{PRE}\
         pub unsafe fn inner(q: *const i32, flag: i32, m: usize) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: usize = 0;\n\
         \x20   while i < m {{ s += *q.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn outer(flag: i32, p: *const i32) -> i32 {{ inner(p, flag, 4) }}\n\
         pub unsafe fn caller(base: *const i32, k: isize) -> i32 {{ outer(1, base.offset(k)) }}\n"
    );
    let out = flat(&emitted(&src));
    assert!(
        out.contains(
            "outer(1, core::slice::from_raw_parts(base.offset(k), (4i128.max(0) as usize)))"
        ),
        "{out}"
    );
}

// ---------------------------------------------------------------------------
// The exposure wrapper and the nested rows (tulip's shape).
// ---------------------------------------------------------------------------

/// tulip's indicator shape: entries reached only through a function-pointer
/// table, so each is emitted behind an exposure wrapper.
const TULIP: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments)]\n\
pub mod indicators {\n\
    pub mod sma {\n\
        pub unsafe extern \"C\" fn ti_sma_start(mut options: *const std::os::raw::c_double) -> std::os::raw::c_int {\n\
            return *options.offset(0 as std::os::raw::c_int as isize) as std::os::raw::c_int - 1 as std::os::raw::c_int;\n\
        }\n\
        pub unsafe extern \"C\" fn ti_sma(\n\
            mut size: std::os::raw::c_int,\n\
            mut inputs: *const *const std::os::raw::c_double,\n\
            mut options: *const std::os::raw::c_double,\n\
            mut outputs: *const *mut std::os::raw::c_double,\n\
        ) -> std::os::raw::c_int {\n\
            let mut input: *const std::os::raw::c_double = *inputs.offset(0 as std::os::raw::c_int as isize);\n\
            let period: std::os::raw::c_int = *options.offset(0 as std::os::raw::c_int as isize) as std::os::raw::c_int;\n\
            let mut output: *mut std::os::raw::c_double = *outputs.offset(0 as std::os::raw::c_int as isize);\n\
            if period < 1 as std::os::raw::c_int { return 1 as std::os::raw::c_int; }\n\
            if size <= ti_sma_start(options) { return 0 as std::os::raw::c_int; }\n\
            let mut val: std::os::raw::c_double = 0.0;\n\
            let mut i: std::os::raw::c_int = 0;\n\
            while i < size {\n\
                val = val + *input.offset(i as isize);\n\
                *output.offset(i as isize) = val;\n\
                i += 1\n\
            }\n\
            return 0 as std::os::raw::c_int;\n\
        }\n\
    }\n\
}\n\
pub type Indicator = Option<unsafe extern \"C\" fn(std::os::raw::c_int, *const *const std::os::raw::c_double, *const std::os::raw::c_double, *const *mut std::os::raw::c_double) -> std::os::raw::c_int>;\n\
pub type Start = Option<unsafe extern \"C\" fn(*const std::os::raw::c_double) -> std::os::raw::c_int>;\n\
#[derive(Copy, Clone)]\n\
pub struct IndicatorInfo { pub indicator: Indicator, pub start: Start }\n\
pub static mut INDICATORS: [IndicatorInfo; 1] = [IndicatorInfo {\n\
    indicator: Some(indicators::sma::ti_sma as unsafe extern \"C\" fn(std::os::raw::c_int, *const *const std::os::raw::c_double, *const std::os::raw::c_double, *const *mut std::os::raw::c_double) -> std::os::raw::c_int),\n\
    start: Some(indicators::sma::ti_sma_start as unsafe extern \"C\" fn(*const std::os::raw::c_double) -> std::os::raw::c_int),\n\
}];\n";

fn wrapper<'a>(source: &'a str, owner: &str) -> &'a str {
    source
        .split(&format!("fn {owner}("))
        .nth(1)
        .unwrap_or_else(|| panic!("{owner} in the emitted tree:\n{source}"))
        .split("fn __crat_safe_")
        .next()
        .expect("wrapper region")
}

/// **W4CB-5 — exposure wrapper × (a) constant and (c) composition.**
/// `ti_sma_start` reads `options[0]` on every call (`must:1`); `ti_sma` reads
/// `options[0]` and passes it to `ti_sma_start` behind branches (`may:1`). Both
/// wrappers' `options` views take `1`, not the fallback.
#[test]
fn w4cb_5_exposure_wrapper_views_take_the_entry_s_own_bound() {
    let source = emitted_closed_world(TULIP);
    let start = flat(wrapper(&source, "ti_sma_start"));
    assert!(
        start.contains("from_raw_parts(options, (1i128.max(0) as usize))"),
        "{start}"
    );
    let sma = flat(wrapper(&source, "ti_sma"));
    assert!(
        sma.contains("from_raw_parts(options, (1i128.max(0) as usize))"),
        "{sma}"
    );
    assert!(!start.contains("FALLBACK_SLICE_EXTENT"), "{start}");
}

/// **W4CB-6 — the nested row × (b) loop.** `ti_sma`'s input row is read at
/// `i < size`: the declaration planner sizes it `size` and N1 relocates that
/// length to the wrapper, where the formal carries the same name.
#[test]
fn w4cb_6_nested_row_takes_the_loop_bound_in_the_wrapper() {
    let source = emitted_closed_world(TULIP);
    let sma = flat(wrapper(&source, "ti_sma"));
    assert!(
        sma.contains("(((size) as i128).max(0) as usize)"),
        "the input row's view is sized by `size`:\n{sma}"
    );
}

/// **W4CB-7 — the declaration planner × (b) loop, in a body.** A row loaded
/// into a local and read under `i < n` is constructed with `n`, not the
/// fallback.
#[test]
fn w4cb_7_declaration_planner_sizes_a_local_by_its_loop() {
    let src = format!(
        "{PRE}\
         pub unsafe fn sum_row(t: *const *const f64, n: i32) -> f64 {{\n\
         \x20   let mut row: *const f64 = *t.offset(0 as i32 as isize);\n\
         \x20   let mut s: f64 = 0.0; let mut i: i32 = 0;\n\
         \x20   while i < n {{ s += *row.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n"
    );
    let out = flat(&emitted(&src));
    assert!(out.contains("(((n) as i128).max(0) as usize)"), "{out}");
}
