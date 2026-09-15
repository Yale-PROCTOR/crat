//! Wave-6o (relay 006, R402-8): the thin-extent holds — R272-1 at a foreign
//! multi-element position, R364-2 at a local callee that accesses wider than
//! one element — extended from the thin `Ref` form to the thin `Opt` form.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

fn decision_and_reason(input: &str, function: &str, binding: &str) -> (Decision, String) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.param_name.as_deref() == Some(binding)
            })
            .expect("corpus-derived subject");
        let reason = match decision {
            Decision::Degraded(record) => record.reason.key().to_owned(),
            _ => String::new(),
        };
        (decision.clone(), reason)
    })
    .expect("fixture compiler context")
}

fn held_thin(input: &str, function: &str, binding: &str, reason: &str) {
    assert!(verify::type_checks_str(input));
    let (decision, key) = decision_and_reason(input, function, binding);
    assert_eq!(
        key, reason,
        "a thin optional at a multi-element position must hold {function}::{binding}: {decision:?}"
    );
    let output = ast_emitted_source_of(input).expect("hold emission");
    assert!(
        !output.contains(&format!("{binding}: Option<&")),
        "no one-element view may reach the position: {output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}

/// rgba::rgba_from_rgb_string — a nullable `*const c_char` handed to
/// `strstr`, which reads to the NUL: the R272-1 shape, previously bridged
/// from `Option<&i8>` (report 004 claim 9).
#[test]
fn wave6o_thin_optional_at_a_nul_foreign_position_holds() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe extern "C" { fn strstr(h: *const i8, n: *const i8) -> *mut i8; }
unsafe fn rgba_from_rgb_string(str: *const i8) -> i32 {
    if str.is_null() { return 0; }
    let p = strstr(str, b"rgb(\0".as_ptr() as *const i8);
    if p.is_null() { return 1; }
    return *str as i32;
}
"#;
    held_thin(input, "rgba_from_rgb_string", "str", "held:thin-extent");
}

/// A nullable thin pointer handed to a LOCAL callee whose `c_void` parameter
/// is cast to a wider type and read (brotli `Hash14` → `BrotliUnalignedRead32`,
/// R364-2's own witness): the twin, previously bridged from `Option<&u8>`.
#[test]
fn wave6o_thin_optional_at_a_wide_local_callee_holds() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn BrotliUnalignedRead32(p: *const core::ffi::c_void) -> u32 { *(p as *const u32) }
unsafe fn Hash14(data: *const u8) -> u32 {
    if data.is_null() { return 0; }
    let h = BrotliUnalignedRead32(data as *const core::ffi::c_void);
    return h.wrapping_add(*data as u32);
}
"#;
    held_thin(input, "Hash14", "data", "held:local-callee-access-extent");
}

/// The control: a one-element foreign position (`toupper` takes a value, but
/// a pointer contract of extent one is the point) — a nullable thin pointer at
/// a position whose contract fits one element still delivers as an Option.
#[test]
fn wave6o_thin_optional_at_a_one_element_position_still_delivers() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe extern "C" { fn observe(p: *const i32); }
unsafe fn look(value: *const i32) -> i32 {
    if value.is_null() { return 0; }
    observe(value);
    return *value;
}
"#;
    assert!(verify::type_checks_str(input));
    let (decision, key) = decision_and_reason(input, "look", "value");
    assert!(
        matches!(decision, Decision::Opt { slice: false, .. }),
        "an unmodeled one-element position keeps the optional: {decision:?} {key}"
    );
    let output = ast_emitted_source_of(input).expect("native emission");
    assert!(output.contains("value: Option<&i32>"), "{output}");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// The other control: an optional SLICE carries its own extent and is not
/// held at a NUL position (R272-1's "slices and Options of slices" clause).
#[test]
fn wave6o_optional_slice_at_a_nul_foreign_position_is_not_held() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe extern "C" { fn strstr(h: *const i8, n: *const i8) -> *mut i8; }
unsafe fn scan(str: *const i8) -> i32 {
    if str.is_null() { return 0; }
    let p = strstr(str, b"rgb(\0".as_ptr() as *const i8);
    if p.is_null() { return 1; }
    return (*str.offset(1)) as i32;
}
"#;
    assert!(verify::type_checks_str(input));
    let (decision, key) = decision_and_reason(input, "scan", "str");
    eprintln!("WAVE6O_SLICE_CONTROL {decision:?} {key}");
    assert_ne!(
        key, "held:thin-extent",
        "an optional slice is not thin: {decision:?}"
    );
    assert_ne!(key, "held:local-callee-access-extent", "{decision:?}");
}
