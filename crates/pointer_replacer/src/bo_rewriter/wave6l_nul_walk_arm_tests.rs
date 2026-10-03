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

/// The emitted call `<callee>(…)` carries `strlen + 1` of `<base>`.
fn takes_strlen(out: &str, callee: &str, base: &str) -> bool {
    let flat = out.split_whitespace().collect::<String>();
    let base = base.split_whitespace().collect::<String>();
    flat.contains(&format!("{callee}(")) && flat.contains(&format!("CStr::from_ptr({base}"))
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
    assert!(
        out.contains("nul-walk:A:"),
        "the receipt names the arm: {out}"
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
    assert!(takes_strlen(&out, "parse_int", "url"), "{out}");
    assert!(out.contains("nul-walk:B:literal"), "{out}");
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
    assert!(takes_strlen(&out, "is_proto", "p"), "{out}");
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

/// A callee that copies a counted 16 bytes: not bounded by the NUL.
#[test]
fn w6l_nulwalk_c_a_counted_callee_keeps_the_fallback() {
    let out = emitted(&b_literal().replace(
        "unsafe fn parse_int(s: *const c_char) -> c_int {",
        "unsafe fn copy16(s: *const c_char) -> c_int {\n    let mut d = [0u8; 16];\n    memcpy(d.as_mut_ptr() as *mut c_void, s as *const c_void, 16);\n    d[0] as c_int + *s.offset(1) as c_int\n}\nunsafe fn parse_int(s: *const c_char) -> c_int {",
    ).replace("    parse_int(url)\n", "    copy16(url)\n"));
    assert!(!out.contains("nul-walk:"), "{out}");
    assert!(
        takes_fallback(&out),
        "the control constructs the slice with the fallback: {out}"
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
