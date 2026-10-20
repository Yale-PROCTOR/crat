//! wave-6l relay 077 (R776-4, STOP 2) — the NUL-walk extent for a C string
//! handed to a callee whose reads stop at or before its NUL.
//!
//! - **(A)** the callee reaches a string-contract position (`strcmp`,
//!   `strlen`, `fprintf("%s")`, …) on EVERY path through it: on a UB-free
//!   input (§28) the argument is then a terminated, initialized string at the
//!   call, whatever the base.
//! - **(B)** the callee's reads stop at or before the NUL on the paths that
//!   read, and the BASE is a C string by provenance: a command-line `argv`
//!   element, a string literal, a null-tested `strdup` / `getenv` result, or a
//!   `sscanf` `%s` / `%[` destination under a dominating test of that call's
//!   return value covering the conversion.
//!
//! The length is `strlen + 1`; the receipt names the arm and the provenance
//! (`nul-walk:<arm>:<provenance>`). Every other shape keeps the fallback.

const PRE: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
use std::ffi::c_char;
use std::ffi::c_int;
use std::ffi::c_void;
extern "C" {
    fn strcmp(a: *const c_char, b: *const c_char) -> c_int;
    fn strlen(s: *const c_char) -> usize;
    fn strcpy(d: *mut c_char, s: *const c_char) -> *mut c_char;
    fn strrchr(s: *const c_char, c: c_int) -> *mut c_char;
    fn sscanf(s: *const c_char, f: *const c_char, ...) -> c_int;
    fn malloc(n: usize) -> *mut c_void;
    fn memcpy(d: *mut c_void, s: *const c_void, n: usize) -> *mut c_void;
    fn strncmp(a: *const c_char, b: *const c_char, n: usize) -> c_int;
    fn strchr(s: *const c_char, c: c_int) -> *mut c_char;
    fn strdup(s: *const c_char) -> *mut c_char;
    fn printf(f: *const c_char, ...) -> c_int;
    fn exit(code: c_int) -> !;
}
"#;

fn source(body: &str) -> String {
    format!("{PRE}{body}")
}

fn emitted(body: &str) -> String {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "crat-w6l-nulwalk-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("fixture directory");
    let root = dir.join("lib.rs");
    std::fs::write(&root, source(body)).expect("fixture file");
    let outcome = super::rewrite_m1_path(&root);
    let seams = ::utils::compilation::run_compiler_on_path(&root, |tcx| {
        super::seam_tsv(tcx).expect("seam receipt")
    })
    .expect("fixture compiles");
    let _ = std::fs::remove_dir_all(&dir);
    match outcome {
        super::RewriteOutcome::Emitted { source, .. } => format!("{seams}\n=====\n{source}"),
        other => panic!("fixture must emit: {other:?}"),
    }
}

/// The emitted call `<callee>(…)` binds `<base>` once and takes the
/// binding's `strlen + 1`.
fn takes_strlen(out: &str, callee: &str, base: &str) -> bool {
    let flat = out.split_whitespace().collect::<String>();
    let base = base.split_whitespace().collect::<String>();
    flat.contains(&format!("{callee}("))
        && flat.contains(&format!("let__crat_nul_walk_base={base};"))
        && flat.contains("CStr::from_ptr(__crat_nul_walk_baseas*constcore::ffi::c_char)")
}

fn takes_fallback(out: &str) -> bool {
    out.contains("FALLBACK_SLICE_EXTENT")
}

// ---- (A): an unconditional string-contract read ----

/// buffer `equal`: `strcmp` in the `if` condition reads both strings on every
/// path; `(*buf).data` takes `strlen + 1` whatever its provenance.
const A_CONTRACT: &str = r#"
unsafe fn equal(a: *mut c_char, b: *mut c_char) -> c_int {
    if strcmp(a, b) != 0 { 1 } else { 0 }
}
pub struct Buf { pub data: *mut c_char }
pub unsafe fn caller(buf: *mut Buf, s: *mut c_char) -> c_int {
    equal(s, (*buf).data)
}
"#;

#[test]
fn w6l_nulwalk_a_an_unconditional_contract_read_takes_strlen() {
    let out = emitted(A_CONTRACT);
    assert!(takes_strlen(&out, "equal", "(*buf).data"), "{out}");
    assert!(!takes_fallback(&out), "{out}");
    // R780-3: the receipt names the contract function and position.
    assert!(
        out.contains("nul-walk:A:contract:strcmp:1"),
        "the receipt names the arm, the function and the position: {out}"
    );
}

// ---- (B): a bounded callee and a C string by provenance ----

/// brotli `ParseInt` from `ParseParams`: the walk may stop before the NUL
/// (`i < 5`), and the base is a command-line `argv` element.
const B_ARGV: &str = r#"
unsafe fn parse_int(s: *const c_char) -> c_int {
    let mut v = 0;
    let mut i = 0;
    while i < 5 {
        let c = *s.offset(i as isize);
        if c as c_int == 0 { break; }
        v = v * 10 + (c as c_int - '0' as i32);
        i += 1;
    }
    v
}
unsafe fn main_0(argc: c_int, argv: *mut *mut c_char) -> c_int {
    if argc > 1 { parse_int(*argv.offset(1)) } else { 0 }
}
"#;

#[test]
fn w6l_nulwalk_b_an_argv_element_into_an_early_stop_walk_takes_strlen() {
    let out = emitted(B_ARGV);
    assert!(
        takes_strlen(&out, "parse_int", "argv[1]")
            || takes_strlen(&out, "parse_int", "*argv.offset(1)"),
        "{out}"
    );
    assert!(!takes_fallback(&out), "{out}");
    assert!(out.contains("nul-walk:B:argv"), "{out}");
}

/// urlparser `main_0`: a local bound once to a string literal, into a callee
/// whose walk may stop before the NUL (`i < 5`): (B), not (A).
fn b_literal() -> String {
    B_ARGV.replace(
        "unsafe fn main_0(argc: c_int, argv: *mut *mut c_char) -> c_int {\n    if argc > 1 { parse_int(*argv.offset(1)) } else { 0 }\n}",
        "pub unsafe fn main_1() -> c_int {\n    let mut url: *mut c_char = b\"12\\0\" as *const u8 as *const c_char as *mut c_char;\n    let mut addr = url as usize;\n    parse_int(url)\n}",
    )
}

#[test]
fn w6l_nulwalk_b_a_literal_bound_local_takes_strlen() {
    let literal = b_literal();
    assert_ne!(literal, B_ARGV, "the literal caller is in");
    let out = emitted(&literal);
    // `url` is decided thin and reverted (its literal initializer does not
    // type at `&c_char`); the construction is the input-form twin's, which
    // only the binding form (`SeamLen::NulWalk`, receipt
    // `nul-walk:B:literal`) renders. The decision-time row is the thin one.
    assert!(takes_strlen(&out, "parse_int", "url"), "{out}");
    assert!(!takes_fallback(&out), "{out}");
}

/// An `sscanf` `%[` destination, read only where that `sscanf` returned 1 —
/// the one conversion that writes it.
const B_SSCANF_CHECKED: &str = r#"
unsafe fn is_proto(p: *mut c_char) -> c_int {
    if p.is_null() { 0 } else { (strcmp(p, b"http\0" as *const u8 as *const c_char) == 0) as c_int }
}
pub unsafe fn get(url: *const c_char) -> c_int {
    let mut p: *mut c_char = malloc(16) as *mut c_char;
    let mut addr = p as usize;
    if sscanf(url, b"%[^:]\0" as *const u8 as *const c_char, p) == 1 { is_proto(p) } else { 0 }
}
"#;

#[test]
fn w6l_nulwalk_b_a_checked_sscanf_destination_takes_strlen() {
    let out = emitted(B_SSCANF_CHECKED);
    // An optional formal: the checked adapter binds `p` first, and the
    // NUL-walk binds the checked pointer.
    assert!(
        takes_strlen(&out, "is_proto", "__crat_call_adapter_ptr"),
        "{out}"
    );
    assert!(out.contains("nul-walk:B:sscanf"), "{out}");
}

// ---- controls: each keeps the fallback ----

/// urlparser `url_get_protocol`: the `sscanf` result is not tested.
#[test]
fn w6l_nulwalk_c_an_unchecked_sscanf_destination_keeps_the_fallback() {
    let out = emitted(&B_SSCANF_CHECKED.replace(
        "if sscanf(url, b\"%[^:]\\0\" as *const u8 as *const c_char, p) == 1 { is_proto(p) } else { 0 }",
        "sscanf(url, b\"%[^:]\\0\" as *const u8 as *const c_char, p);\n    is_proto(p)",
    ));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// An early-stop walk whose base is a raw field: no provenance.
#[test]
fn w6l_nulwalk_c_an_early_stop_walk_of_a_parameter_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "unsafe fn main_0(argc: c_int, argv: *mut *mut c_char) -> c_int {\n    if argc > 1 { parse_int(*argv.offset(1)) } else { 0 }\n}",
        "pub struct H { pub p: *mut c_char }\npub unsafe fn other(h: *mut H) -> c_int {\n    parse_int((*h).p)\n}",
    ));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// A callee that copies a counted 16 bytes: not bounded by the NUL. Restated
/// (R829-1, relay 297): `copy16::s` is the source beside `memcpy`'s written
/// destination `d.as_mut_ptr()` (arg0, the callee's own array through a
/// method call, not shown disjoint), so it is held raw; the caller hands
/// `url` raw and no slice is constructed, so no fallback either.
#[test]
fn w6l_nulwalk_c_a_counted_callee_keeps_the_fallback() {
    let out = emitted(&b_literal().replace(
        "unsafe fn parse_int(s: *const c_char) -> c_int {",
        "unsafe fn copy16(s: *const c_char) -> c_int {\n    let mut d = [0u8; 16];\n    memcpy(d.as_mut_ptr() as *mut c_void, s as *const c_void, 16);\n    d[0] as c_int + *s.offset(1) as c_int\n}\nunsafe fn parse_int(s: *const c_char) -> c_int {",
    ).replace("    parse_int(url)\n", "    copy16(url)\n"));
    assert!(!out.contains("nul-walk:"), "{out}");
    // R829-1 (relay 297, main 188): copy16::s is held beside `d.as_mut_ptr()` (arg0) at memcpy; the fallback construction → the raw formal and a raw `copy16(url)`.
    assert!(
        out.contains("unsafe fn copy16(s: *const c_char) -> c_int {"),
        "the held source keeps its raw formal: {out}"
    );
    assert!(out.contains("copy16(url)"), "{out}");
    assert!(
        !takes_fallback(&out),
        "no slice is constructed for a raw formal: {out}"
    );
}

/// A suffix of an `argv` element (`strrchr(arg, '=') + 1`) is not on the
/// ruled list.
#[test]
fn w6l_nulwalk_c_an_argv_suffix_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "if argc > 1 { parse_int(*argv.offset(1)) } else { 0 }",
        "if argc > 1 {\n        let mut value: *mut c_char = strrchr(*argv.offset(1), '=' as i32);\n        if value.is_null() { 0 } else { parse_int(value.offset(1)) }\n    } else { 0 }",
    ));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// A contract read behind an early `return` is not on every path, and a
/// parameter base has no provenance.
#[test]
fn w6l_nulwalk_c_a_contract_read_behind_an_early_return_keeps_the_fallback() {
    let out = emitted(&A_CONTRACT.replace(
        "if strcmp(a, b) != 0 { 1 } else { 0 }",
        "if a.is_null() { return 0; }\n    if strcmp(a, b) != 0 { 1 } else { 0 }",
    ));
    assert!(!out.contains("nul-walk:A:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// `strcpy`'s DESTINATION is written past its own NUL: not a string read.
#[test]
fn w6l_nulwalk_c_a_strcpy_destination_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "unsafe fn parse_int(s: *const c_char) -> c_int {",
        "unsafe fn fill(d: *mut c_char) -> c_int {\n    strcpy(d, b\"0123456789\\0\" as *const u8 as *const c_char);\n    0\n}\nunsafe fn parse_int(s: *const c_char) -> c_int {",
    ).replace("parse_int(*argv.offset(1))", "fill(*argv.offset(1))"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// `argv` is `main_0`'s only: the same shape in another function has no
/// provenance.
#[test]
fn w6l_nulwalk_c_an_argv_shaped_parameter_outside_main_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace("unsafe fn main_0(", "unsafe fn other_0("));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// A test of the `sscanf` result that does not cover the conversion (`== 0`:
/// nothing was written).
#[test]
fn w6l_nulwalk_c_an_sscanf_test_that_misses_the_conversion_keeps_the_fallback() {
    let out =
        emitted(&B_SSCANF_CHECKED.replace(") == 1 { is_proto(p) }", ") == 0 { is_proto(p) }"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// A literal with a NUL inside it is longer than its `strlen + 1`.
#[test]
fn w6l_nulwalk_c_a_literal_with_an_inner_nul_keeps_the_fallback() {
    let literal = b_literal().replace("b\"12\\0\"", "b\"1\\02\\0\"");
    assert_ne!(literal, b_literal(), "the inner NUL is in");
    let out = emitted(&literal);
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// An indexed walk that steps without testing for the NUL reads past it.
/// R923-1 (wave-4 relay 112): without the `break`, `while i < 5` reads
/// `s[0..5)` on every path that runs the loop, so the narrowed callee bound
/// (behind the NUL walk, ahead of §77) takes `5` — never the NUL walk.
#[test]
fn w6l_nulwalk_c_an_indexed_walk_without_a_nul_test_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace("        if c as c_int == 0 { break; }\n", ""));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        !takes_fallback(&out) && out.contains("(5) as usize"),
        "the control constructs the slice with the loop's own bound: {out}"
    );
}

/// A cursor that steps without testing for the NUL is not R491-7's walk.
#[test]
fn w6l_nulwalk_c_a_cursor_without_a_nul_test_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "unsafe fn parse_int(s: *const c_char) -> c_int {",
        "unsafe fn skip3(mut s: *const c_char) -> c_int {\n    let mut n = 0;\n    while n < 3 {\n        s = s.offset(1);\n        n += 1;\n    }\n    *s as c_int\n}\nunsafe fn parse_int(s: *const c_char) -> c_int {",
    ).replace("parse_int(*argv.offset(1))", "skip3(*argv.offset(1))"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

// ---- the relay 077 review's findings, as controls ----

const LIT: &str = "b\"x\\0\" as *const u8 as *const c_char";

/// Review 1: a call that never returns (`exit`) before the read.
#[test]
fn w6l_nulwalk_r1_an_exit_before_the_read_keeps_the_fallback() {
    let out = emitted(&A_CONTRACT.replace(
        "if strcmp(a, b) != 0 { 1 } else { 0 }",
        "if a.is_null() { exit(1); }\n    if strcmp(a, b) != 0 { 1 } else { 0 }",
    ));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// Review 2: the callee writes the string through an alias (a global) before
/// it reads it; at the call the bytes may be uninitialized.
#[test]
fn w6l_nulwalk_r2_a_write_through_an_alias_before_the_read_keeps_the_fallback() {
    let out = emitted(&format!(
        "static mut G: *mut c_char = 0 as *mut c_char;\nunsafe fn f(v: *mut c_char) -> c_int {{\n    strcpy(G, {LIT});\n    if strcmp(v, {LIT}) != 0 {{ 1 }} else {{ 0 }}\n}}\npub struct Buf {{ pub data: *mut c_char }}\npub unsafe fn caller(buf: *mut Buf) -> c_int {{\n    G = (*buf).data;\n    f((*buf).data)\n}}\n"
    ));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// Review 2 (the call site): a later argument writes the string after the
/// walk would have read it.
#[test]
fn w6l_nulwalk_r2b_a_later_argument_that_writes_keeps_the_fallback() {
    let out = emitted(&format!(
        "unsafe fn g(v: *mut c_char, n: c_int) -> c_int {{\n    if strcmp(v, {LIT}) != 0 {{ 1 }} else {{ n }}\n}}\nunsafe fn fill(p: *mut c_char) -> c_int {{\n    *p = 0;\n    0\n}}\npub struct Buf {{ pub data: *mut c_char }}\npub unsafe fn caller(buf: *mut Buf) -> c_int {{\n    g((*buf).data, fill((*buf).data))\n}}\n"
    ));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// Review 3: a forwarding cycle whose other member writes past the NUL.
#[test]
fn w6l_nulwalk_r3_a_cycle_with_a_writing_member_keeps_the_fallback() {
    for (first, second) in [("a", "b"), ("b", "a")] {
        let out = emitted(&format!(
            "unsafe fn {first}(p: *mut c_char, n: c_int) -> c_int {{\n    if n > 0 {{ {second}(p, n - 1); }}\n    *p.offset(7) = 1;\n    if strncmp(p, {LIT}, 1) == 0 {{ 1 }} else {{ 0 }}\n}}\nunsafe fn {second}(p: *mut c_char, n: c_int) -> c_int {{\n    {first}(p, n)\n}}\nunsafe fn main_0(argc: c_int, argv: *mut *mut c_char) -> c_int {{\n    if argc > 1 {{ b(*argv.offset(1), 1) + a(*argv.offset(1), 0) }} else {{ 0 }}\n}}\n"
        ));
        assert!(!out.contains("nul-walk:"), "{first}/{second}: {out}");
        assert!(
            takes_fallback(&out),
            "the control constructs the slice with the fallback: {out}"
        );
    }
}

/// Review 4: a read at a literal offset after a NUL test of element 0.
#[test]
fn w6l_nulwalk_r4_a_literal_offset_after_a_nul_test_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "unsafe fn parse_int(s: *const c_char) -> c_int {",
        "unsafe fn sixth(s: *const c_char, n: c_int) -> c_int {\n    if *s as c_int == 0 { return 0; }\n    if n > 0 { *s.offset(5) as c_int } else { 0 }\n}\nunsafe fn parse_int(s: *const c_char) -> c_int {",
    ).replace("parse_int(*argv.offset(1))", "sixth(*argv.offset(1), argc)"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// Review 5 (a): the index is a parameter, never tested.
#[test]
fn w6l_nulwalk_r5a_a_parameter_index_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "unsafe fn parse_int(s: *const c_char) -> c_int {",
        "unsafe fn get(s: *const c_char, i: c_int) -> c_int {\n    *s.offset(i as isize) as c_int\n}\nunsafe fn parse_int(s: *const c_char) -> c_int {",
    ).replace("parse_int(*argv.offset(1))", "get(*argv.offset(1), 3)"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// Review 5 (b): two increments after one test step over the NUL.
#[test]
fn w6l_nulwalk_r5b_a_double_increment_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace("        i += 1;\n", "        i += 1;\n        i += 1;\n"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// Review 5 (c): the test reads a byte read once, before the loop.
#[test]
fn w6l_nulwalk_r5c_a_stale_test_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "unsafe fn parse_int(s: *const c_char) -> c_int {",
        "unsafe fn stale(s: *const c_char) -> c_int {\n    let mut i = 0;\n    let c = *s.offset(i as isize);\n    loop {\n        if c as c_int == 0 { break; }\n        i += 1;\n        if i > 9 { break; }\n    }\n    *s.offset(i as isize) as c_int\n}\nunsafe fn parse_int(s: *const c_char) -> c_int {",
    ).replace("parse_int(*argv.offset(1))", "stale(*argv.offset(1))"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// Review 6: the `strdup` string is written before the call (byte 3 is its
/// NUL when it is three bytes long).
#[test]
fn w6l_nulwalk_r6_a_strdup_string_written_before_the_call_keeps_the_fallback() {
    let out = emitted(&format!(
        "unsafe fn first(p: *mut c_char) -> c_int {{\n    if p.is_null() {{ 0 }} else {{ strcmp(p, {LIT}) }}\n}}\npub unsafe fn caller(x: *const c_char) -> c_int {{\n    let mut s: *mut c_char = strdup(x);\n    if s.is_null() {{ return 0; }}\n    *s.offset(3) = '/' as i32 as c_char;\n    first(s)\n}}\n"
    ));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// Review 7: a pointer `strchr` derives from the string is read past the NUL.
#[test]
fn w6l_nulwalk_r7_a_strchr_result_read_past_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "unsafe fn parse_int(s: *const c_char) -> c_int {",
        "unsafe fn after(s: *const c_char) -> c_int {\n    let q = strchr(s, '=' as i32);\n    if q.is_null() { 0 } else { *q.offset(3) as c_int }\n}\nunsafe fn parse_int(s: *const c_char) -> c_int {",
    ).replace("parse_int(*argv.offset(1))", "after(*argv.offset(1))"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// Review 9: `%ls` is not a byte string.
#[test]
fn w6l_nulwalk_r9_a_wide_string_conversion_keeps_the_fallback() {
    let out = emitted(&A_CONTRACT.replace(
        "if strcmp(a, b) != 0 { 1 } else { 0 }",
        "printf(b\"%ls\\0\" as *const u8 as *const c_char, b);\n    if strcmp(a, a) != 0 { 1 } else { 0 }",
    ));
    assert!(!out.contains("nul-walk:A:contract"), "{out}");
}

/// Review 6 (`argv`): an element replaced before the call by a buffer with no
/// NUL is not the command line's string.
#[test]
fn w6l_nulwalk_r6b_a_replaced_argv_element_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "if argc > 1 { parse_int(*argv.offset(1)) } else { 0 }",
        "let mut b: [c_char; 4] = [49, 50, 51, 52];\n    *argv.offset(1) = b.as_mut_ptr();\n    if argc > 1 { parse_int(*argv.offset(1)) } else { 0 }",
    ));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// A callee that writes through the pointer (`*p = 0`) is not bounded.
#[test]
fn w6l_nulwalk_c_a_callee_that_writes_keeps_the_fallback() {
    let out = emitted(&B_ARGV.replace(
        "unsafe fn parse_int(s: *const c_char) -> c_int {",
        "unsafe fn zap(p: *mut c_char) -> c_int {\n    if strcmp(p, b\"x\\0\" as *const u8 as *const c_char) == 0 { *p = 0; }\n    0\n}\nunsafe fn parse_int(s: *const c_char) -> c_int {",
    ).replace("parse_int(*argv.offset(1))", "zap(*argv.offset(1))"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

// ---- R780-3 item 3: R491-7's caller-side clause ----

/// The caller's own `strlen(s)` licenses `strlen + 1` (R491-7, relay 060)
/// only where nothing writes through `s` before the call: here the NUL is
/// overwritten after it (review r6's first shape), and the walk would run past
/// the old end.
#[test]
fn w6l_nulwalk_s3_a_nul_overwritten_after_the_callers_strlen_keeps_the_fallback() {
    let out = emitted(&format!(
        "unsafe fn first(p: *mut c_char) -> c_int {{\n    if p.is_null() {{ 0 }} else {{ strcmp(p, {LIT}) }}\n}}\npub unsafe fn caller(x: *const c_char) -> c_int {{\n    let mut s: *mut c_char = strdup(x);\n    if s.is_null() {{ return 0; }}\n    *s.offset(strlen(s) as isize) = '/' as i32 as c_char;\n    first(s)\n}}\n"
    ));
    assert!(!out.contains("len-elsewhere"), "{out}");
    assert!(!out.contains("CStr::from_ptr("), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
    );
}

/// The clause still holds where the caller only reads the string.
#[test]
fn w6l_nulwalk_s3_the_callers_strlen_without_a_write_still_licenses() {
    let out = emitted(&format!(
        "unsafe fn first(p: *mut c_char) -> c_int {{\n    if p.is_null() {{ 0 }} else {{ strcmp(p, {LIT}) }}\n}}\npub unsafe fn caller(x: *const c_char) -> c_int {{\n    let mut s: *mut c_char = strdup(x);\n    if s.is_null() {{ return 0; }}\n    let mut n = strlen(s);\n    first(s)\n}}\n"
    ));
    assert!(out.contains("CStr::from_ptr("), "{out}");
    assert!(!takes_fallback(&out), "{out}");
}
