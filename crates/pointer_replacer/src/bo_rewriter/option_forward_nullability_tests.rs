//! Wave-6o (relay 125, R744-1): forward nullability, actual → formal (§29's
//! "propagated to the formal"). A formal takes `Option` when some caller's
//! actual carries nullability evidence (its own `is_null` use, a null-literal
//! construction, or its own optional decision) and the callee does not
//! dereference the formal itself; the hand-on into a raw formal is bridged by
//! the CALLER's class, thin only under a pointee-only access, else held at the
//! caller (092). Corpus: brotli's class 2452 (`BrotliEncoderCompressStream::
//! total_out`, the tool's `CompressFile` passes `0 as *mut size_t`, the
//! hand-on targets model-Raw) and 133's four hand-on formals (json.h
//! `json_write_pretty_value::indent` / `newline`, brotli
//! `CopyUncompressedBlockToOutput::next_out`,
//! `BuildAndStoreBlockSwitchEntropyCodes::tree`).
use super::{emit_tests::ast_emitted_source_of, verify};

const STREAM: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
#[repr(C)] pub struct S { pub total: usize }
unsafe fn Inject(mut s: *mut S, mut total_out: *mut usize) -> i32 {
    if !total_out.is_null() { total_out.write((*s).total); }
    return 1 as i32;
}
unsafe fn Stream(mut s: *mut S, mut total_out: *mut usize) -> i32 {
    return Inject(s, total_out);
}
unsafe fn CompressFile(mut s: *mut S) -> i32 {
    let mut out: usize = 0;
    Stream(s, 0 as *mut usize) + Stream(s, &mut out)
}
"#;

/// 093 §2: `Inject`'s formal stays raw (its own `write`, standing in for the
/// model's Raw) and accesses only its pointee; `Stream::total_out` receives
/// the null literal, so it is optional, the literal call renders `None`, and
/// the hand-on is the caller-owned thin bridge.
#[test]
fn wave6o_null_literal_formal_handed_to_a_pointee_only_raw_formal_is_optional() {
    assert!(verify::type_checks_str(STREAM));
    let output = ast_emitted_source_of(STREAM).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(flat.contains("total_out:Option<&mutusize>"), "{output}");
    assert!(flat.contains("Stream(s,None)"), "{output}");
    assert!(
        flat.contains(
            "total_out.as_deref_mut().map_or(core::ptr::null_mut::<usize>(),core::ptr::from_mut)"
        ),
        "{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}

/// The control: `Inject` offsets its formal (more than one element), so the
/// thin bridge is refused; `Stream::total_out` is held at the caller (raw),
/// the null literal passes unchanged, and nothing else in `Stream`'s class is
/// blocked by it.
#[test]
fn wave6o_null_literal_formal_handed_to_a_wider_raw_formal_stays_raw() {
    let input = STREAM.replace(
        "if !total_out.is_null() { total_out.write((*s).total); }",
        "if !total_out.is_null() { *total_out.offset(1 as isize) = (*s).total; }",
    );
    assert!(verify::type_checks_str(&input));
    let output = ast_emitted_source_of(&input).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(flat.contains("fnStream(muts:"), "{output}");
    assert!(flat.contains("muttotal_out:*mutusize"), "{output}");
    assert!(!flat.contains("Option<&mutusize>"), "{output}");
    assert!(verify::type_checks_str(&output), "{output}");
}

const PRETTY: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn write_indent(mut indent: *const i8) -> i32 {
    if !indent.is_null() { return *indent as i32; }
    return 0 as i32;
}
unsafe fn pretty_value(mut depth: i32, mut indent: *const i8) -> i32 {
    if depth == 0 as i32 { return 0 as i32; }
    return write_indent(indent);
}
unsafe fn write_pretty(mut depth: i32, mut indent: *const i8) -> i32 {
    if indent.is_null() { return -(1 as i32); }
    return pretty_value(depth, indent);
}
"#;

/// 133's shape (json.h `json_write_pretty_value::indent`): the caller's
/// actual is null-tested (its own evidence), `pretty_value` only hands the
/// formal on, so the formal is `Option<&i8>` and the call passes it
/// same-form, with no `.unwrap()` that would panic where C continues.
#[test]
fn wave6o_hand_on_formal_receiving_a_nullable_actual_is_optional() {
    assert!(verify::type_checks_str(PRETTY));
    let output = ast_emitted_source_of(PRETTY).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(
        flat.contains("fnpretty_value(mutdepth:i32,mutindent:Option<&i8>"),
        "{output}"
    );
    // the hand-on is same-form at both calls: no unwrap where C continues with NULL
    assert!(flat.contains("returnwrite_indent(indent)"), "{output}");
    assert!(
        flat.contains("returnpretty_value(depth,indent)"),
        "{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}

/// The control: `pretty_value` dereferences the formal itself, so a NULL there
/// is the input's UB (§28); the formal keeps `&i8` and the caller's unwrap.
#[test]
fn wave6o_dereferenced_formal_receiving_a_nullable_actual_stays_plain() {
    let input = PRETTY.replace(
        "    if depth == 0 as i32 { return 0 as i32; }\n",
        "    if depth == 0 as i32 { return 0 as i32; }\n    if *indent == 0 as i8 { return 1 as i32; }\n",
    );
    assert!(verify::type_checks_str(&input));
    let output = ast_emitted_source_of(&input).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(
        !flat.contains("fnpretty_value(mutdepth:i32,mutindent:Option<&i8>"),
        "{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}

/// Relay 127 (wave-6a 135's cascade): the hand-on target indexes the formal
/// one level down (`*indent.offset(1)`), so an optional made here would meet a
/// slice formal. The rule leaves the formal to main's 55 flow rule (a flow into
/// a fat formal is an array use): `pretty_value::indent` is not made optional.
#[test]
fn wave6o_hand_on_into_an_indexing_formal_is_left_alone() {
    let input = PRETTY.replace(
        "    if !indent.is_null() { return *indent as i32; }\n",
        "    let mut k: isize = 0 as isize;\n    while *indent.offset(k) != 0 as i8 { k += 1 as isize; }\n    return k as i32;\n",
    );
    assert!(verify::type_checks_str(&input));
    let output = ast_emitted_source_of(&input).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(
        !flat.contains("fnpretty_value(mutdepth:i32,mutindent:Option<&i8>"),
        "{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}

/// The same, two levels down (brotli F2's chain: `BuildAndStoreBlockSwitchEntropyCodes`
/// → `BuildAndStoreBlockSplitCode` → the tree builders' `*tree.offset(k)`).
#[test]
fn wave6o_hand_on_into_an_indexing_formal_two_levels_down_is_left_alone() {
    let input = PRETTY
        .replace(
            "    if !indent.is_null() { return *indent as i32; }\n",
            "    let mut k: isize = 0 as isize;\n    while *indent.offset(k) != 0 as i8 { k += 1 as isize; }\n    return k as i32;\n",
        )
        .replace(
            "unsafe fn pretty_value(",
            "unsafe fn mid(mut indent: *const i8) -> i32 {\n    return write_indent(indent);\n}\nunsafe fn pretty_value(",
        )
        .replace("    return write_indent(indent);\n}\nunsafe fn write_pretty", "    return mid(indent);\n}\nunsafe fn write_pretty");
    assert!(verify::type_checks_str(&input));
    let output = ast_emitted_source_of(&input).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(
        flat.contains("returnmid(indent)"),
        "fixture shape: {output}"
    );
    assert!(
        !flat.contains("fnpretty_value(mutdepth:i32,mutindent:Option<&i8>"),
        "{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}

/// Relay 309 (wave-5d 146b §2.2): a crossing the seam blocks (here the unattested world's
/// `seam-a5-attestation-absent` at a pair one blind argument makes the seam ask) holds the
/// callee's class, which reverts to raw; the caller's delivered argument planned for the
/// kept formal must then be bridged (the raw view at the call) or the caller reverted with
/// the class — never left in its kept-world form (E0308).
const BLOCKED_INTO_REVERTED: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
#[repr(C)] pub struct S { pub total: usize }
unsafe fn Inject(mut out: *mut usize, mut s: *mut S) -> i32 { *out = (*s).total; return 1 as i32; }
unsafe fn Stream(mut s: *mut S) -> i32 { let mut x: usize = 0; return Inject(&mut x as *mut usize, s); }
"#;

#[test]
fn r309_a_blocked_crossing_into_a_reverted_class_bridges_or_reverts_its_caller() {
    assert!(verify::type_checks_str(BLOCKED_INTO_REVERTED));
    let output = ast_emitted_source_of(BLOCKED_INTO_REVERTED).expect("native emission");
    let flat = output.split_whitespace().collect::<String>();
    assert!(
        flat.contains("fnInject(mutout:*mutusize,muts:*mutS)"),
        "the premise: the blocked crossing holds Inject's class raw: {output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}
