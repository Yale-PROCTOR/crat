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

/// Codex 062 (finding 3): the counted footprint through a cast between two
/// forwarders. (`fill_raw`, an uncast `c_void` wrapper, is finding 2's shape:
/// whether its 16 bytes pass one element depends on the CALLER's element, so
/// the callee-side arm leaves it to the caller-aware conjunct.)
const FOOTPRINT_HOPS: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
unsafe fn fill_raw(mut dst: *mut core::ffi::c_void, mut src: *const core::ffi::c_void) {
    memcpy(dst, src, 16 as u64);
}
unsafe fn fill(mut dst: *mut u8, mut src: *const u8) {
    memcpy(dst as *mut core::ffi::c_void, src as *const core::ffi::c_void, 16 as u64);
}
unsafe fn relay(mut dst: *mut u8, mut src: *const u8) {
    fill(dst as *mut u8, src);
}
pub struct Pair {
    pub a: *mut u8,
    pub b: *const u8,
    pub c: *mut u8,
}
pub unsafe fn caller(mut p: *mut Pair) {
    let mut v = (*p).a;
    fill_raw(v as *mut core::ffi::c_void, (*p).b as *const core::ffi::c_void);
    let mut r = (*p).c;
    relay(r, (*p).b);
}
"#;

/// F3 (Codex 062 finding 3) — the counted footprint is followed through a
/// cast between two forwarders, as the NUL see-through follows casts.
#[test]
fn w6l_seethrough_f3_the_counted_footprint_crosses_a_cast_between_forwarders() {
    let map = access_map(FOOTPRINT_HOPS);
    let row = map
        .iter()
        .find(|(label, _)| label == "caller::r")
        .unwrap_or_else(|| panic!("caller::r is not held: {map:#?}"));
    assert!(
        row.1.ends_with("foreign-contract:memcpy:0:byte-count"),
        "{map:#?}"
    );
}

/// Relay 063 (R645-5 item 3): the walk through LOCAL COPIES. A parameter
/// copied into a local (`let q = p;`, `q = p;`) that reaches a many-element
/// foreign position reaches it too.
const COPIES: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
    fn strlen(s: *const i8) -> u64;
}
unsafe fn scan(mut p: *const i8) -> u64 {
    let mut q = p;
    strlen(q)
}
unsafe fn load(mut buffer: *const u8, mut dst: *mut u8) {
    let mut buf: *const u8 = 0 as *const u8;
    buf = buffer;
    memcpy(dst as *mut core::ffi::c_void, buf as *const core::ffi::c_void, 16 as u64);
}
unsafe fn peek(mut p: *const i8) -> i8 {
    let mut q = p;
    *q
}
pub unsafe fn top(mut s: *const i8) -> u64 {
    scan(s)
}
"#;

/// The thin-extent set's labels for one fixture.
fn held(input: &str) -> Vec<String> {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let (_table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx)?;
        let held = super::thin_extent::collect(tcx, &ctx.facts);
        let mut labels = ctx
            .subjects
            .iter()
            .filter(|subject| held.contains(&(subject.fn_did, subject.hir_id)))
            .map(|subject| subject.label.clone())
            .collect::<Vec<_>>();
        labels.sort();
        Ok::<_, String>(labels)
    })
    .expect("fixture compiles")
    .expect("decision table")
}

/// C1 (item 3) — `scan::p` reaches `strlen` through `let q = p`, and the walk
/// carries on to `scan`'s caller; `load::buffer` reaches `memcpy`'s 16 bytes
/// through `buf = buffer`.
#[test]
fn w6l_seethrough_c1_a_copy_carries_the_foreign_extent_to_its_source() {
    let held = held(COPIES);
    for label in ["scan::p", "top::s", "load::buffer"] {
        assert!(held.iter().any(|l| l == label), "{label}: {held:?}");
    }
}

/// C1c (item 3's control) — a copy read one element at a time holds nothing.
#[test]
fn w6l_seethrough_c1c_a_copy_read_one_element_holds_nothing() {
    let held = held(COPIES);
    assert!(
        !held.iter().any(|l| l == "peek::p" || l == "peek::q"),
        "{held:?}"
    );
}

/// Relay 063 (R645-5 item 4): the footprint of an UNCAST `c_void` wrapper is
/// the caller's question — 16 bytes pass one `u8`, 4 bytes do not pass one
/// `i32`.
const VOID_FOOTPRINT: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
extern "C" {
    fn memset(d: *mut core::ffi::c_void, c: i32, n: u64) -> *mut core::ffi::c_void;
}
unsafe fn clear16(mut d: *mut core::ffi::c_void) {
    memset(d, 0, 16 as u64);
}
unsafe fn clear4(mut d: *mut core::ffi::c_void) {
    memset(d, 0, 4 as u64);
}
pub struct S {
    pub a: *mut u8,
    pub b: *mut i32,
    pub c: *mut u8,
}
pub unsafe fn caller(mut s: *mut S) {
    let mut bytes = (*s).a;
    clear16(bytes as *mut core::ffi::c_void);
    let mut word = (*s).b;
    clear4(word as *mut core::ffi::c_void);
    let mut small = (*s).c;
    clear4(small as *mut core::ffi::c_void);
}
"#;

/// V1 (item 4) — a `u8` caller into a 16-byte `memset` is held, and so is a
/// `u8` caller into a 4-byte one.
#[test]
fn w6l_seethrough_v1_an_uncast_void_footprint_past_the_callers_element_is_held() {
    let map = access_map(VOID_FOOTPRINT);
    for label in ["caller::bytes", "caller::small"] {
        let row = map
            .iter()
            .find(|(l, _)| l == label)
            .unwrap_or_else(|| panic!("{label} is not held: {map:#?}"));
        assert!(
            row.1.ends_with("foreign-contract:memset:0:byte-count"),
            "{map:#?}"
        );
    }
}

/// V1c (item 4's control) — an `i32` caller into a 4-byte `memset` is one
/// element: not held (wave-6o's `binn_get_int32` shape).
#[test]
fn w6l_seethrough_v1c_an_uncast_void_footprint_of_one_element_is_kept() {
    let map = access_map(VOID_FOOTPRINT);
    assert!(
        !map.iter().any(|(label, _)| label == "caller::word"),
        "{map:#?}"
    );
}

/// V2c (item 4) — the footprint rides a forwarding chain: an `i32` caller of a
/// forwarder into the 4-byte `memset` is still one element, kept.
#[test]
fn w6l_seethrough_v2c_the_footprint_is_carried_through_a_forwarder() {
    let input = VOID_FOOTPRINT.replace(
        "pub struct S {",
        "unsafe fn relay32(mut p: *mut i32) {\n    clear4(p as *mut core::ffi::c_void);\n}\npub unsafe fn outer(mut w: *mut i32) {\n    relay32(w);\n}\npub struct S {",
    );
    let map = access_map(&input);
    assert!(
        !map.iter()
            .any(|(label, _)| label == "outer::w" || label == "relay32::p"),
        "{map:#?}"
    );
}

/// The line A review (relay 063): the footprint is JOINED over every counted
/// site and every forwarding target, never the first one found.
const FOOTPRINT_JOIN: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
extern "C" {
    fn memset(d: *mut core::ffi::c_void, c: i32, n: u64) -> *mut core::ffi::c_void;
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
unsafe fn clear4(mut d: *mut core::ffi::c_void) {
    memset(d, 0, 4 as u64);
}
unsafe fn fill64(mut d: *mut u8) {
    memset(d as *mut core::ffi::c_void, 0, 64 as u64);
}
unsafe fn both(mut d: *mut core::ffi::c_void, mut s: *const core::ffi::c_void) {
    memset(d, 0, 4 as u64);
    memcpy(d, s, 64 as u64);
}
unsafe fn relay(mut p: *mut i32) {
    clear4(p as *mut core::ffi::c_void);
    fill64(p as *mut u8);
}
unsafe fn zero(mut q: *mut core::ffi::c_void, mut n: u64) {
    memset(q, 0, n);
}
unsafe fn wipe(mut p: *mut core::ffi::c_void) {
    zero(p, 64 as u64);
}
unsafe fn clear_n(mut d: *mut core::ffi::c_void, mut n: u64) {
    memset(d, 0, n);
}
unsafe fn clear_at(mut d: *mut core::ffi::c_void) {
    memset(d.offset(4), 0, 4 as u64);
}
pub struct S {
    pub a: *mut i32,
    pub b: *mut i32,
    pub c: *mut i32,
    pub d: *mut i32,
    pub e: *mut i32,
    pub s: *const u8,
}
pub unsafe fn caller(mut s: *mut S, mut n: u64) {
    let mut two = (*s).a;
    both(two as *mut core::ffi::c_void, (*s).s as *const core::ffi::c_void);
    let mut fwd = (*s).b;
    relay(fwd);
    let mut vv = (*s).c;
    wipe(vv as *mut core::ffi::c_void);
    let mut rt = (*s).d;
    clear_n(rt as *mut core::ffi::c_void, n);
    let mut off = (*s).e;
    clear_at(off as *mut core::ffi::c_void);
}
"#;

/// V3 — two counted sites at one `c_void` parameter (4 and 64 bytes): the
/// footprint is 64, and an `i32` caller is held. V4 — a forwarder into a
/// 4-byte and a 64-byte writer holds its `i32` caller. V5 — a `c_void`
/// forwarder into a `c_void` writer with a runtime count holds. V6 — a
/// runtime count holds an `i32` caller. V7 — a count at `d.offset(4)` is not
/// measured from the base: held.
#[test]
fn w6l_seethrough_v3_v7_the_footprint_is_joined_and_holds_where_it_passes() {
    let map = access_map(FOOTPRINT_JOIN);
    for label in [
        "caller::two",
        "caller::fwd",
        "caller::vv",
        "caller::rt",
        "caller::off",
    ] {
        assert!(
            map.iter().any(|(l, _)| l == label),
            "{label} is not held: {map:#?}"
        );
    }
}

/// Relay 063 review (line A): the copy walk through a copy that does its own
/// arithmetic, and through C2Rust's ternary.
const COPIES_MORE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case)]
extern "C" {
    fn strlen(s: *const i8) -> u64;
}
unsafe fn walk(mut p: *const i8) -> u64 {
    let mut q = p;
    q = q.offset(1);
    strlen(q)
}
unsafe fn pick(mut p: *const i8, mut r: *const i8, mut c: bool) -> u64 {
    let mut q = if c { p } else { r };
    strlen(q)
}
pub unsafe fn top(mut s: *const i8, mut t: *const i8) -> u64 {
    walk(s).wrapping_add(pick(s, t, true))
}
"#;

/// C2 — a copy that steps (`q = q.offset(1)`) before the NUL walk: the
/// arithmetic gate is a PARAMETER's (its callers are the local callee's
/// hold's), not a local copy's, so `walk::p` and its caller are held. C3 — a
/// ternary copy holds both sources.
#[test]
fn w6l_seethrough_c2_c3_an_arithmetic_copy_and_a_ternary_carry_the_walk() {
    let held = held(COPIES_MORE);
    for label in ["walk::p", "pick::p", "pick::r", "top::s", "top::t"] {
        assert!(held.iter().any(|l| l == label), "{label}: {held:?}");
    }
}

/// G1 (relay 064, R650-5 item 1) — the surviving path: main's R416-5 guard
/// reads `local_callee_extent::accessed_past_one_element` (guard mode), and a
/// counted FOREIGN contract position behind a local callee reaches it only
/// through `AccessReason::ForeignContract` (`fill(dst) { memcpy(dst as *mut
/// c_void, .., 16) }`). Guard mode follows cast hops into LOCAL callees; no
/// other arm sees a foreign counted position. The NUL walk (`measure`) is not
/// this set's (the thin-extent set's, item 2).
#[test]
fn w6l_seethrough_g1_the_guard_reaches_the_foreign_contract_arm() {
    let set = ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(FOOTPRINT),
        |tcx| {
            let (_table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx)?;
            let set = super::local_callee_extent::accessed_past_one_element(
                tcx,
                &ctx.subjects,
                &ctx.facts,
            );
            let mut names = set
                .iter()
                .map(|(function, index)| format!("{}:{index}", tcx.item_name(function.to_def_id())))
                .collect::<Vec<_>>();
            names.sort();
            Ok::<_, String>(names)
        },
    )
    .expect("fixture compiles")
    .expect("decision table");
    assert!(set.iter().any(|name| name == "fill:0"), "{set:?}");
    assert!(!set.iter().any(|name| name == "measure:0"), "{set:?}");
}
