//! **A literal at the call selects the width (wave-6b, R607-1 leg B).**
//!
//! binn's value API hands a thin typed out-pointer to a `void *` writer whose
//! width a sibling type tag selects: `binn_get_int32(value, pint)` calls
//! `copy_int_value(value->ptr, pint as *mut c_void, value->type, 0x61)`
//! (rs-crown-derived/binn/lib.rs:3283), and `copy_int_value` writes `pdest`
//! only as `*(pdest as *mut T) = ..` inside the `match dest_type` arm of each
//! literal (:2178). At THAT call the literal `0x61` selects the `c_int` arm:
//! four bytes, at offset zero, into a four-byte `c_int`. The one-element claim
//! covers the access, so `local_callee_extent`'s hold has nothing to protect at
//! that site. Nothing is widened and no extent is fabricated: the width is the
//! callee's own arm, read at the literal the call passes.
//!
//! Fixtures are reduced from the same two functions; the model calls `pdest`
//! Raw here as it does in the corpus, so the caller's bridge is into a raw
//! formal.

/// Whitespace-free view of an emitted source, for shape assertions.
fn compact(source: &str) -> String {
    source.chars().filter(|c| !c.is_whitespace()).collect()
}

fn reason(rows: &[(String, bool, String)], name: &str) -> String {
    rows.iter()
        .find(|(n, p, _)| n == name && *p)
        .map(|(_, _, r)| r.clone())
        .unwrap_or_else(|| panic!("no parameter {name}: {rows:?}"))
}

fn run_binary(source: &str) -> Vec<u8> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("crat-w6b-literal-{}-{id}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let input = dir.join("main.rs");
    let binary = dir.join("main");
    std::fs::write(&input, source).unwrap();
    let compiled = std::process::Command::new("rustc")
        .args(["--edition=2021", "-Awarnings"])
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "runtime build: {}\n{source}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let run = std::process::Command::new(&binary).output().unwrap();
    assert!(
        run.status.success(),
        "runtime: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(&dir).unwrap();
    run.stdout
}

/// binn.rs:2144 `copy_int_value`, both matches kept: the source width by
/// `source_type`, the destination width by `dest_type`.
const CALLEE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
unsafe fn copy_int_value(mut psource: *mut core::ffi::c_void,
    mut pdest: *mut core::ffi::c_void, mut source_type: i32, mut dest_type: i32) -> i32 {
    let mut vint64: i64 = 0;
    match source_type {
        33 => { vint64 = *(psource as *mut i8) as i64; }
        65 => { vint64 = *(psource as *mut i16) as i64; }
        97 => { vint64 = *(psource as *mut i32) as i64; }
        129 => { vint64 = *(psource as *mut i64); }
        _ => return 0 as i32,
    }
    match dest_type {
        33 => { *(pdest as *mut i8) = vint64 as i8; }
        65 => { *(pdest as *mut i16) = vint64 as i16; }
        97 => { *(pdest as *mut i32) = vint64 as i32; }
        129 => { *(pdest as *mut i64) = vint64; }
        _ => return 0 as i32,
    }
    return 1 as i32;
}
"#;

/// binn.rs:3279 `binn_get_int32`, reduced: a null-tested `*mut c_int` written
/// directly on one path and handed to the writer under a literal on the other.
fn caller(pointee: &str, discriminant: &str) -> String {
    format!(
        "pub unsafe fn get_value(mut pint: *mut {pointee}, mut raw: i64, mut kind: i32) -> i32 {{
    let mut v: i64 = raw;
    if pint.is_null() {{ return 0 as i32; }}
    if raw > 100 {{ *pint = 100 as {pointee}; return 1 as i32; }}
    return copy_int_value(&mut v as *mut i64 as *mut core::ffi::c_void,
        pint as *mut core::ffi::c_void, 129, {discriminant});
}}
"
    )
}

fn fixture(callee: &str, pointee: &str, discriminant: &str) -> String {
    format!("{callee}\n{}", caller(pointee, discriminant))
}

/// [`CALLEE`] with one edit, which must apply: a control whose edit silently
/// missed would pass on the base's own hold and prove nothing.
fn edited(from: &str, to: &str) -> String {
    assert!(CALLEE.contains(from), "the control's edit applies: {from}");
    CALLEE.replace(from, to)
}

/// The driver both runs share. The original takes the raw out-pointer and the
/// emitted form its optional reference; the body is the same four calls.
fn main_of(some: &str, none: &str) -> String {
    format!(
        r#"fn main() {{ unsafe {{
        let mut a: i32 = -1; let mut b: i32 = -1; let mut c: i32 = -1;
        let ra = get_value({some}(&mut a), 7, 0);
        let rb = get_value({some}(&mut b), 1000, 0);
        let rc = get_value({some}(&mut c), -5, 0);
        let rn = get_value({none}, 7, 0);
        println!("{{ra}} {{a}} {{rb}} {{b}} {{rc}} {{c}} {{rn}}");
    }}}}"#
    )
}

/// The positive: `0x61` (97) selects the four-byte arm for a four-byte `i32`.
/// On the base this is `held:local-callee-access-extent` (the writer casts its
/// `void *` away, which the hold reads as an access of unbounded width).
#[test]
fn w6b_a_literal_selecting_the_roots_width_discharges_the_hold() {
    let input = fixture(CALLEE, "i32", "97");
    let rows = super::emit_tests::decisions_of(&input);
    assert_eq!(
        reason(&rows, "pint"),
        "<emitted>",
        "the thin out-pointer delivers: {rows:?}"
    );
    assert_eq!(
        reason(&rows, "pdest"),
        "kind-raw",
        "the writer's own parameter is not this rule's: the model calls it Raw, as it does the corpus's: {rows:?}"
    );
    let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
    let c = compact(&source);
    assert!(
        c.contains("fnget_value(mutpint:Option<&muti32>,"),
        "the caller takes its thin optional form: {source}"
    );
    assert!(
        c.contains("*(pdestas*muti32)=vint64asi32;"),
        "the writer's four-byte arm is unchanged: {source}"
    );
    assert!(
        c.contains("mutpdest:*mutcore::ffi::c_void"),
        "the writer stays raw, so the call bridges into it: {source}"
    );
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT") && !c.contains("from_raw_parts"),
        "nothing is widened or fabricated: {source}"
    );
    assert!(super::verify::type_checks_str(&source));
    let original = run_binary(&format!(
        "{input}\n{}",
        main_of("core::ptr::from_mut", "core::ptr::null_mut()")
    ));
    assert_eq!(original, b"1 7 1 100 1 -5 0\n".to_vec());
    assert_eq!(
        original,
        run_binary(&format!("{source}\n{}", main_of("Some", "None")))
    );
}

/// A NARROWER arm (`65`, two bytes into a four-byte `i32`) is covered too, and
/// a literal that selects NO arm reaches only the writer's `_ => return` — no
/// access at all through the pointer.
#[test]
fn w6b_a_narrower_or_absent_arm_is_covered_by_the_root() {
    for discriminant in ["65", "1"] {
        let input = fixture(CALLEE, "i32", discriminant);
        let rows = super::emit_tests::decisions_of(&input);
        assert_eq!(
            reason(&rows, "pint"),
            "<emitted>",
            "literal {discriminant}: the access fits one i32: {rows:?}"
        );
        let source = super::emit_tests::ast_emitted_source_of(&input).unwrap();
        assert!(super::verify::type_checks_str(&source), "{source}");
    }
}

/// Every control keeps the caller held with its own reason: the rule never
/// answers for a width it did not read at the call.
#[test]
fn w6b_a_width_the_call_does_not_select_keeps_the_hold() {
    let cases: Vec<(&str, String)> = vec![
        // a WIDER arm: 97 writes four bytes through a two-byte i16
        ("wider-arm", fixture(CALLEE, "i16", "97")),
        // no literal at the call: the tag is a variable
        ("non-literal", fixture(CALLEE, "i32", "kind")),
        // an access outside every arm
        (
            "unguarded-access",
            fixture(
                &edited(
                    "let mut vint64: i64 = 0;",
                    "let mut vint64: i64 = 0; *(pdest as *mut i8) = 0;",
                ),
                "i32",
                "97",
            ),
        ),
        // the pointer is handed on
        (
            "pass-on",
            fixture(
                &edited(
                    "return 1 as i32;\n}",
                    "sink(pdest); return 1 as i32;\n}\nunsafe fn sink(p: *mut core::ffi::c_void) {}",
                ),
                "i32",
                "97",
            ),
        ),
        // an access at an offset
        (
            "offset",
            fixture(
                &edited(
                    "97 => { *(pdest as *mut i32) = vint64 as i32; }",
                    "97 => { *(pdest as *mut i32).offset(1) = vint64 as i32; }",
                ),
                "i32",
                "97",
            ),
        ),
        // the discriminant is written before the match
        (
            "discriminant-written",
            fixture(
                &edited(
                    "let mut vint64: i64 = 0;",
                    "let mut vint64: i64 = 0; dest_type = source_type;",
                ),
                "i32",
                "97",
            ),
        ),
        // an access under ANOTHER tag's match: source_type 129 (the call's
        // literal there) writes eight bytes whatever dest_type selects
        (
            "two-tags",
            fixture(
                &edited(
                    "129 => { vint64 = *(psource as *mut i64); }",
                    "129 => { vint64 = *(psource as *mut i64); *(pdest as *mut i64) = 0; }",
                ),
                "i32",
                "97",
            ),
        ),
        // the place is borrowed, not read or written in place
        (
            "borrowed-place",
            fixture(
                &edited(
                    "97 => { *(pdest as *mut i32) = vint64 as i32; }",
                    "97 => { let r = &mut *(pdest as *mut i32); *r = vint64 as i32; }",
                ),
                "i32",
                "97",
            ),
        ),
        // the wildcard arm accesses: an access under no literal
        (
            "wildcard-access",
            fixture(
                &edited(
                    "129 => { *(pdest as *mut i64) = vint64; }\n        _ => return 0 as i32,",
                    "129 => { *(pdest as *mut i64) = vint64; }\n        _ => { *(pdest as *mut i64) = 0; return 0 as i32; }",
                ),
                "i32",
                "97",
            ),
        ),
    ];
    for (name, input) in cases {
        let rows = super::emit_tests::decisions_of(&input);
        assert_eq!(
            reason(&rows, "pint"),
            "held:local-callee-access-extent",
            "{name}: the caller stays held: {rows:?}"
        );
    }
}
