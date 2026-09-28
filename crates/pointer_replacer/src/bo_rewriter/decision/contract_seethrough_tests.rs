//! wave-6l relay 062 (R641): a foreign contract reached THROUGH a local
//! callee's parameter.
//!
//! (item 2) brotli's `CopyStat::input_path` reaches `stat`, which C2Rust
//! defines locally as glibc's inline wrapper `stat(p, b) { __xstat(1, p, b) }`.
//! The NUL contract is `__xstat`'s, one call deeper, so the thin-extent hold
//! never saw it: the thin optional reached `stat` unbridged (batch 51's E0308).
//!
//! (item 5, main 131 §6 finding 6) a thin caller handed to a local callee that
//! passes its parameter on to `memcpy(dst as *mut c_void, .., 16)`: the counted
//! footprint is the callee's access extent.

fn reason(rows: &[(String, bool, String)], name: &str) -> String {
    rows.iter()
        .find(|(n, p, _)| n == name && *p)
        .map(|(_, _, r)| r.clone())
        .unwrap_or_else(|| panic!("no parameter {name}: {rows:?}"))
}

/// brotli `CopyStat`, reduced, with glibc's inline `stat` as C2Rust emits it.
const COPY_STAT: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_camel_case_types)]
extern "C" {
    fn __xstat(__ver: i32, __filename: *const i8, __stat_buf: *mut StatBuf) -> i32;
    fn utime(__file: *const i8, __file_times: *const Times) -> i32;
}
#[repr(C)]
pub struct StatBuf {
    pub st_mode: u32,
}
#[repr(C)]
pub struct Times {
    pub actime: i64,
    pub modtime: i64,
}
unsafe extern "C" fn stat(mut __path: *const i8, mut __statbuf: *mut StatBuf) -> i32 {
    return __xstat(1 as i32, __path, __statbuf);
}
unsafe fn CopyStat(mut input_path: *const i8, mut output_path: *const i8) {
    let mut statbuf = StatBuf { st_mode: 0 };
    let mut times = Times { actime: 0, modtime: 0 };
    if input_path.is_null() || output_path.is_null() {
        return;
    }
    if stat(input_path, &mut statbuf) != 0 as i32 {
        return;
    }
    utime(output_path, &mut times);
}
pub struct Context {
    pub current_input_path: *const i8,
    pub current_output_path: *const i8,
}
pub unsafe fn CloseFiles(mut context: *mut Context) {
    CopyStat((*context).current_input_path, (*context).current_output_path);
}
"#;

/// S1 (item 2) — the NUL contract one wrapper deep holds `input_path`
/// `thin-extent`, and 054's nullable lift takes it as `Option<&[c_char]>`,
/// exactly as `output_path` at `utime`.
#[test]
fn w6l_seethrough_s1_a_nul_contract_behind_a_local_wrapper_lifts_the_thin_optional() {
    let rows = crate::bo_rewriter::emit_tests::decisions_of(COPY_STAT);
    assert_eq!(reason(&rows, "input_path"), "<emitted>", "{rows:#?}");
    assert_eq!(reason(&rows, "output_path"), "<emitted>", "{rows:#?}");
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(COPY_STAT).unwrap();
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("fn CopyStat(mut input_path: Option<&[i8]>, mut output_path: Option<&[i8]>)"),
        "{flat}"
    );
    assert!(
        crate::bo_rewriter::verify::type_checks_str(&source),
        "{source}"
    );
}

/// S1c (item 2's control) — a thin optional at a ONE-element position behind
/// the same wrapper (`stat`'s buffer) stays the thin optional.
#[test]
fn w6l_seethrough_s1c_a_one_element_position_behind_the_wrapper_stays_thin() {
    let input = COPY_STAT.replace(
        "pub unsafe fn CloseFiles(mut context: *mut Context) {",
        "pub unsafe fn Look(mut buf: *mut StatBuf) -> i32 {\n    if buf.is_null() {\n        return 0;\n    }\n    stat(b\"/\\0\" as *const u8 as *const i8, buf)\n}\npub unsafe fn CloseFiles(mut context: *mut Context) {",
    );
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("fn Look(mut buf: Option<&mut StatBuf>)"),
        "{flat}"
    );
}

/// S2 (item 2, the fixpoint) — the same NUL walk two local forwarders deep:
/// `CopyStat` calls the program's own `my_stat`, which calls the wrapper.
#[test]
fn w6l_seethrough_s2_the_contract_is_followed_through_two_forwarders() {
    let input = COPY_STAT
        .replace(
            "unsafe fn CopyStat(",
            "unsafe fn my_stat(mut p: *const i8, mut b: *mut StatBuf) -> i32 {\n    stat(p, b)\n}\nunsafe fn CopyStat(",
        )
        .replace("if stat(input_path, &mut statbuf)", "if my_stat(input_path, &mut statbuf)");
    assert_ne!(input, COPY_STAT, "the witness must change the fixture");
    let source = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("fn CopyStat(mut input_path: Option<&[i8]>, mut output_path: Option<&[i8]>)"),
        "{flat}"
    );
    assert!(
        crate::bo_rewriter::verify::type_checks_str(&source),
        "{source}"
    );
}

/// main 131 §6 finding 6, reduced: a thin caller handed to a local callee that
/// hands its parameter on to a COUNTED foreign footprint; the control hands it
/// to a NUL walk.
const FOOTPRINT: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
    fn strlen(s: *const i8) -> u64;
}
unsafe fn fill(mut dst: *mut u8, mut src: *const u8) {
    memcpy(dst as *mut core::ffi::c_void, src as *const core::ffi::c_void, 16 as u64);
}
unsafe fn measure(mut s: *const i8) -> u64 {
    strlen(s)
}
pub struct Pair {
    pub a: *mut u8,
    pub b: *const u8,
    pub s: *const i8,
}
pub unsafe fn caller(mut p: *mut Pair) -> u64 {
    let mut d = (*p).a;
    let mut n = (*p).s;
    fill(d, (*p).b);
    measure(n)
}
"#;

/// The local-callee access map, keyed by the caller subject's label.
fn access_map(input: &str) -> Vec<(String, String)> {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let (_table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx)?;
        let map = super::local_callee_extent::collect(
            tcx,
            &ctx.subjects,
            &ctx.facts,
            &Default::default(),
            &Default::default(),
            None,
            None,
        );
        Ok::<_, String>(
            ctx.subjects
                .iter()
                .filter_map(|subject| {
                    map.get(&(subject.fn_did, subject.hir_id))
                        .map(|access| (subject.label.clone(), access.detail()))
                })
                .collect::<Vec<_>>(),
        )
    })
    .expect("fixture compiles")
    .expect("decision table")
}

/// F1 (item 5) — the counted footprint behind `fill`'s parameter is the
/// callee's access extent: the thin caller is in the map, under the contract.
#[test]
fn w6l_seethrough_f1_a_counted_foreign_footprint_is_the_callee_extent() {
    let map = access_map(FOOTPRINT);
    let row = map
        .iter()
        .find(|(label, _)| label == "caller::d")
        .unwrap_or_else(|| panic!("caller::d is not held: {map:#?}"));
    assert!(
        row.1.ends_with("foreign-contract:memcpy:0:byte-count"),
        "{map:#?}"
    );
}

/// F1c (item 5's control) — a NUL walk (`strlen`) is not a counted footprint:
/// the caller of `measure` is not in the map.
#[test]
fn w6l_seethrough_f1c_a_nul_walk_is_not_a_counted_footprint() {
    let map = access_map(FOOTPRINT);
    assert!(
        !map.iter().any(|(label, _)| label == "caller::n"),
        "{map:#?}"
    );
}
