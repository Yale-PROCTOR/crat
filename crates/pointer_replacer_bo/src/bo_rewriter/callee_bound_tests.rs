//! **R707 / R717-1 / R923-1 — wave-4 build 1: `len-callee-bound`, narrowed
//! (relay 112).** The extent a function's own loop proves, at the three call
//! points: the seam's raw-argument arm, the exposure wrapper's view of an
//! entry formal, and the declaration planner (whose nested rows N1 relocates
//! to the wrapper).
//!
//! `W4CB-*` are the witnesses: the shapes the narrowed rule keeps take their
//! bound (each one emitted `FALLBACK_SLICE_EXTENT` at the base `2961c2ec0`);
//! the shapes it gave up (constant indices, `must`) are pinned back to the
//! fallback. `W4CB-F*` are the fault controls: each one fails when the guard it
//! names is removed from `decision/callee_bound.rs`.

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
    // One directory per call: witnesses run in parallel and must not share it.
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "crat-callee-bound-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
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

/// `len-callee-bound:<must|may>:<expr>` for parameter `index` of `function`,
/// or `None` where the module proves no bound.
fn receipt(src: &str, function: &str, index: usize) -> Option<String> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let def = tcx
            .hir_body_owners()
            .find(|d| {
                matches!(tcx.def_kind(d.to_def_id()), rustc_hir::def::DefKind::Fn)
                    && tcx.item_name(d.to_def_id()).as_str() == function
            })
            .unwrap_or_else(|| panic!("{function} in the fixture"));
        out = super::decision::callee_bound::of_parameter(tcx, def, index)
            .map(|bound| bound.receipt(&super::decision::callee_bound::parameter_names(tcx, def)));
    })
    .expect("fixture compiles");
    out
}

// ---------------------------------------------------------------------------
// The seam's raw-argument arm.
// ---------------------------------------------------------------------------

/// **W4CB-1 — seam × (a) constant, `may`.** The callee reads elements 0 and 2,

// ---------------------------------------------------------------------------
// The seam's raw-argument arm.
// ---------------------------------------------------------------------------

/// **W4CB-1 — constant indices give no bound (R923-1).** The callee reads
/// elements 0 and 2, behind a branch: a literal index is no length the caller
/// passes, so the raw argument keeps the fallback. The signed delta `k` keeps
/// the argument a raw expression (R394-2), so this is the raw arm and not the
/// forward view.
#[test]
fn w4cb_1_seam_constant_indices_keep_the_fallback() {
    let src = format!(
        "{PRE}\
         pub unsafe fn pick(flag: i32, p: *const i32) -> i32 {{\n\
         \x20   if flag > 0 {{ *p.offset(0) + *p.offset(2) }} else {{ 0 }}\n\
         }}\n\
         pub unsafe fn caller(base: *const i32, k: isize) -> i32 {{ pick(1, base.offset(k)) }}\n"
    );
    assert_eq!(receipt(&src, "pick", 1), None);
    let out = flat(&emitted(&src));
    assert!(
        out.contains(
            "pick(1, core::slice::from_raw_parts(base.offset(k), crate::FALLBACK_SLICE_EXTENT))"
        ),
        "{out}"
    );
}

/// **W4CB-2 — no `must` (R923-1, relay 112 R3-9).** A straight-line callee
/// (R677-6's shape) reads two literal indices: the callee bound gives nothing,
/// and R677-6 (ahead of it, R780-2) answers as on the record.
#[test]
fn w4cb_2_seam_straight_line_constant_is_not_the_callee_bound_s() {
    let src = format!(
        "{PRE}\
         pub unsafe fn read32(buffer: *const u8) -> u32 {{\n\
         \x20   return (*buffer.offset(0 as i32 as isize) as u32) << 24\n\
         \x20       | *buffer.offset(3 as i32 as isize) as u32;\n\
         }}\n\
         pub unsafe fn caller(in_0: *mut u8, k: isize) -> u32 {{ read32(in_0.offset(k)) }}\n"
    );
    assert_eq!(receipt(&src, "read32", 0), None);
    let out = flat(&emitted(&src));
    assert!(!out.contains("len-callee-bound"), "{out}");
}

/// **W4CB-3 — seam × the loop.** `while i < n` bounds every index; `n` is not
/// adjacent to the pointer, so no companion licence answers first. The call's
/// own argument, a plain name, instantiates the bound.
#[test]
fn w4cb_3_seam_loop_bound_is_instantiated_with_the_call_s_argument() {
    let src = format!(
        "{PRE}\
         pub unsafe fn total(n: i32, flag: i32, p: *const i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn caller(base: *const i32, count: i32, k: isize) -> i32 {{\n\
         \x20   total(count, 1, base.offset(k))\n\
         }}\n"
    );
    assert_eq!(
        receipt(&src, "total", 2).as_deref(),
        Some("len-callee-bound:may:n")
    );
    let out = flat(&emitted(&src));
    assert!(
        out.contains("from_raw_parts(base.offset(k), (((count) as i128).max(0)) as usize)"),
        "{out}"
    );
}

/// **W4CB-4 — seam × composition, the pointer passed unchanged.** `outer`
/// reads `p` under `i < 2` and passes `p` on to a local callee whose loop bound
/// is its own third parameter; `outer` passes the literal `4` there, so
/// `outer`'s bound is `max(2, 4) = 4`. (`outer` reads `p` itself so that its
/// own decision is a slice.)
#[test]
fn w4cb_4_seam_bound_composes_through_a_local_callee() {
    let src = format!(
        "{PRE}\
         pub unsafe fn inner(q: *const i32, flag: i32, m: i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < m {{ s += *q.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn outer(flag: i32, p: *const i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < 2 {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s + inner(p, flag, 4)\n\
         }}\n\
         pub unsafe fn caller(base: *const i32, k: isize) -> i32 {{ outer(1, base.offset(k)) }}\n"
    );
    assert_eq!(
        receipt(&src, "outer", 1).as_deref(),
        Some("len-callee-bound:may:4")
    );
    let out = flat(&emitted(&src));
    assert!(
        out.contains("outer(1, core::slice::from_raw_parts(base.offset(k), (4) as usize))"),
        "{out}"
    );
}

/// **W4CB-N1 — a length parameter passed through unchanged (R923-1).**
/// `outer`'s own parameter `m` reaches `inner`'s loop limit as it is, so
/// `outer`'s bound is `m`.
#[test]
fn w4cb_n1_a_length_parameter_passed_through_is_the_bound() {
    let src = format!(
        "{PRE}\
         pub unsafe fn inner(q: *const i32, flag: i32, m: i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < m {{ s += *q.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn outer(p: *const i32, len: i32) -> i32 {{ inner(p, 0, len) }}\n"
    );
    assert_eq!(
        receipt(&src, "outer", 0).as_deref(),
        Some("len-callee-bound:may:len")
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

/// **W4CB-5 — the exposure wrapper × constant indices (R923-1).**
/// `ti_sma_start` reads `options[0]` and `ti_sma` reads `options[0]` and passes
/// it on: literal indices, so neither gives a bound and both wrappers' `options`
/// views keep the fallback.
#[test]
fn w4cb_5_exposure_wrapper_constant_views_keep_the_fallback() {
    assert_eq!(receipt(TULIP, "ti_sma_start", 0), None);
    assert_eq!(receipt(TULIP, "ti_sma", 2), None);
    let source = emitted_closed_world(TULIP);
    let start = flat(wrapper(&source, "ti_sma_start"));
    assert!(!start.contains("len-callee-bound"), "{start}");
    assert!(
        !start.contains("from_raw_parts(options, (1) as usize)"),
        "{start}"
    );
}

/// **W4CB-6 — the nested row × the loop.** `ti_sma`'s input row is read only at
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

/// **W4CB-7 — the declaration planner × the loop, in a body.** A row loaded
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

// ---------------------------------------------------------------------------
// Fault controls: each fails when the named guard is removed.
// ---------------------------------------------------------------------------

/// **W4CB-F1 — an index with arithmetic refuses (R923-1).** `p[i + 1]` under
/// `i < n` would need `n + 1`. Guard: `counter` admits the bare counter only.
#[test]
fn w4cb_f1_an_index_with_arithmetic_refuses() {
    let src = format!(
        "{PRE}\
         pub unsafe fn shift(p: *mut i32, n: i32) {{\n\
         \x20   let mut i: i32 = 0;\n\
         \x20   while i < n {{ *p.offset((i + 1) as isize) = 0; i += 1 }}\n\
         \x20   }}\n"
    );
    assert_eq!(receipt(&src, "shift", 0), None);
}

/// **W4CB-F2 — an index read from memory proves nothing.** Guard: `counter`.
#[test]
fn w4cb_f2_an_index_from_memory_refuses() {
    let src = format!(
        "{PRE}\
         pub unsafe fn lookup(p: *const i32, q: *const i32) -> i32 {{ *p.offset(*q as isize) }}\n"
    );
    assert_eq!(receipt(&src, "lookup", 0), None);
}

/// **W4CB-F3 — a bound on a global refuses.** Guard: `bound_param` admits
/// parameters only.
#[test]
fn w4cb_f3_a_global_bound_refuses() {
    let src = format!(
        "{PRE}\
         pub static mut LIMIT: i32 = 8;\n\
         pub unsafe fn scan(p: *const i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < LIMIT {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n"
    );
    assert_eq!(receipt(&src, "scan", 0), None);
}

/// **W4CB-F4 — a pointer passed on composes through a local callee and refuses
/// through a foreign one.** Guard: `compose`'s local-body requirement.
#[test]
fn w4cb_f4_passed_onward_composes_locally_and_refuses_foreign() {
    let src = format!(
        "{PRE}\
         extern \"C\" {{ fn ext(p: *const i32) -> i32; }}\n\
         pub unsafe fn two(q: *const i32, m: i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < m {{ s += *q.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn local(p: *const i32) -> i32 {{ two(p, 2) }}\n\
         pub unsafe fn foreign(p: *const i32) -> i32 {{ ext(p) }}\n"
    );
    assert_eq!(
        receipt(&src, "local", 0).as_deref(),
        Some("len-callee-bound:may:2")
    );
    assert_eq!(receipt(&src, "foreign", 0), None);
}

/// **W4CB-F5 — the loop variable written before the access refuses.** After
/// `i += 1` inside the body, `i < n` no longer holds at the access. Guard: the
/// last-statement check in `loop_bound`.
#[test]
fn w4cb_f5_a_counter_written_before_the_access_refuses() {
    let src = format!(
        "{PRE}\
         pub unsafe fn early(p: *const i32, n: i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < n {{ i += 1; s += *p.offset(i as isize); }}\n\
         \x20   s\n\
         }}\n"
    );
    assert_eq!(receipt(&src, "early", 0), None);
}

/// **W4CB-F6 — the bound's parameter reassigned refuses.** The bound would name
/// the entry value. Guard: `bound_param`'s write check.
#[test]
fn w4cb_f6_a_reassigned_bound_parameter_refuses() {
    let src = format!(
        "{PRE}\
         pub unsafe fn grow(p: *const i32, mut n: i32) -> i32 {{\n\
         \x20   n += 4;\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n"
    );
    assert_eq!(receipt(&src, "grow", 0), None);
}

/// **W4CB-F7 — only a literal or a never-written local of the caller is
/// copied into a length, and only when no argument of the call has an effect
/// (R923-1, relay 112 S1-M1).** Guard: `at_call_site`'s argument checks and
/// `effect_free`.
#[test]
fn w4cb_f7_an_argument_that_is_not_a_plain_local_keeps_the_fallback() {
    let total = "pub unsafe fn total(n: i32, flag: i32, p: *const i32) -> i32 {\n\
        let mut s = 0; let mut i: i32 = 0;\n\
        while i < n { s += *p.offset(i as isize); i += 1 }\n\
        s }\n";
    for caller in [
        "pub unsafe fn next() -> i32 { 3 }\n\
         pub unsafe fn caller(base: *const i32, k: isize) -> i32 { total(next(), 1, base.offset(k)) }\n",
        "pub unsafe fn caller(base: *const i32, c: i32, k: isize) -> i32 { total(c + 1, 1, base.offset(k)) }\n",
        "pub unsafe fn caller(base: *const i32, mut c: i32, k: isize) -> i32 { c += 1; total(c, 1, base.offset(k)) }\n",
        "pub static mut C: i32 = 4;\n\
         pub unsafe fn caller(base: *const i32, k: isize) -> i32 { total(C, 1, base.offset(k)) }\n",
        "pub unsafe fn caller(base: *const i32, c: i32, k: isize) -> i32 { total(c as i32, 1, base.offset(k)) }\n",
    ] {
        let out = flat(&emitted(&format!("{PRE}{total}{caller}")));
        assert!(
            out.contains("from_raw_parts(base.offset(k), crate::FALLBACK_SLICE_EXTENT)"),
            "{caller}\n{out}"
        );
    }
    let kept =
        "pub unsafe fn caller(base: *const i32, k: isize) -> i32 { total(7, 1, base.offset(k)) }\n";
    let out = flat(&emitted(&format!("{PRE}{total}{kept}")));
    assert!(
        out.contains("from_raw_parts(base.offset(k), (((7) as i128).max(0)) as usize)"),
        "{out}"
    );
}

/// **W4CB-F8 — a negative instantiated bound is an empty slice.** The rendering
/// clamps at zero in `i128`, never `usize::MAX`. Guard: `Bound::render_count`'s
/// `.max(0)`.
#[test]
fn w4cb_f8_a_negative_bound_renders_an_empty_slice() {
    let src = format!(
        "{PRE}\
         pub unsafe fn total(n: i32, flag: i32, p: *const i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn caller(base: *const i32, c: i32, k: isize) -> i32 {{ total(c, 1, base.offset(k)) }}\n"
    );
    let out = flat(&emitted(&src));
    assert!(out.contains("(((c) as i128).max(0)) as usize"), "{out}");
    // The rendered arithmetic itself, evaluated at `c = -5`.
    assert_eq!(((-5i32 as i128).max(0)) as usize, 0);
}

/// **W4CB-F9 — arithmetic on the limit refuses.** Guard: `term` admits no
/// method or operator.
#[test]
fn w4cb_f9_arithmetic_on_the_limit_refuses() {
    let src = format!(
        "{PRE}\
         pub unsafe fn head(p: *const u8, n: i32) -> u32 {{\n\
         \x20   let mut s = 0u32; let mut i: i32 = 0;\n\
         \x20   while i < n - 1 {{ s += *p.offset(i as isize) as u32; i += 1 }}\n\
         \x20   s\n\
         }}\n"
    );
    assert_eq!(receipt(&src, "head", 0), None);
}

/// **W4CB-F10 — a cast on the limit refuses (R923-1).** Guard: `term` admits
/// a cast of a literal only.
#[test]
fn w4cb_f10_a_cast_limit_refuses() {
    let src = format!(
        "{PRE}\
         pub unsafe fn widen(p: *const i32, n: i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i64 = 0;\n\
         \x20   while i < n as i64 {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n"
    );
    assert_eq!(receipt(&src, "widen", 0), None);
}

/// **W4CB-F11 — `<=` refuses (the bound would be `n + 1`).** Guard:
/// `loop_bound`'s `Lt` / `Gt` only.
#[test]
fn w4cb_f11_an_inclusive_limit_refuses() {
    let src = format!(
        "{PRE}\
         pub unsafe fn incl(p: *const i32, n: i32) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i <= n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n"
    );
    assert_eq!(receipt(&src, "incl", 0), None);
}

/// **W4CB-F12 — a literal index beside the loop refuses the whole bound**
/// (`p[0]` read when `n = 0` would need `1`, not `n`). Guard: the bare `*p` /
/// literal index refuses.
#[test]
fn w4cb_f12_a_constant_access_beside_the_loop_refuses() {
    let src = format!(
        "{PRE}\
         pub unsafe fn first(p: *const i32, n: i32) -> i32 {{\n\
         \x20   let mut s = *p.offset(0 as isize); let mut i: i32 = 0;\n\
         \x20   while i < n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn bare(p: *const i32, n: i32) -> i32 {{\n\
         \x20   let mut s = *p; let mut i: i32 = 0;\n\
         \x20   while i < n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n"
    );
    assert_eq!(receipt(&src, "first", 0), None);
    assert_eq!(receipt(&src, "bare", 0), None);
}

/// **W4CB-F13 — an index cast that changes signedness refuses** (`usize as
/// isize`), and so does a counter stepped by `wrapping_add`. Guard: `counter`'s
/// value-preserving casts and `steps_by_one`'s two forms.
#[test]
fn w4cb_f13_a_sign_changing_index_cast_and_a_wrapping_step_refuse() {
    let src = format!(
        "{PRE}\
         pub unsafe fn sized(p: *const i32, n: usize) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: usize = 0;\n\
         \x20   while i < n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn wrapped(p: *const i32, n: isize) -> i32 {{\n\
         \x20   let mut s = 0; let mut i: isize = 0;\n\
         \x20   while i < n {{ s += *p.offset(i); i = i.wrapping_add(1) }}\n\
         \x20   s\n\
         }}\n"
    );
    assert_eq!(receipt(&src, "sized", 0), None);
    assert_eq!(receipt(&src, "wrapped", 0), None);
}

/// **W4CB-F14 — a limit written through a `ref mut` binding or a `&mut self`
/// autoref refuses.** Guard: `Writes`' pattern and adjustment checks.
#[test]
fn w4cb_f14_a_limit_written_through_a_hidden_borrow_refuses() {
    let src = format!(
        "{PRE}\
         pub unsafe fn by_ref(p: *const i32, n: i32) -> i32 {{\n\
         \x20   let mut m = n; let ref mut r = m; *r += 0;\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n\
         pub unsafe fn by_autoref(p: *const i32, mut n: i32) -> i32 {{\n\
         \x20   use core::ops::AddAssign; n.add_assign(4);\n\
         \x20   let mut s = 0; let mut i: i32 = 0;\n\
         \x20   while i < n {{ s += *p.offset(i as isize); i += 1 }}\n\
         \x20   s\n\
         }}\n"
    );
    assert_eq!(receipt(&src, "by_ref", 0), None);
    assert_eq!(receipt(&src, "by_autoref", 0), None);
}
