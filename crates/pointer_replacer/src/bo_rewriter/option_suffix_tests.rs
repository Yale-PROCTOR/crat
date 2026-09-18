//! Wave-6o (relay 024 / R447-5): the SUFFIX of a delivered slice.
//!
//! `s = &*data.offset(l) as *const u8` where `data` is delivered as a slice
//! assigns that slice's suffix. The value planner used to have only the
//! one-element `from_ref` carrier for the shape, which is why a destination
//! read at `*s.offset(0)` AND `*s.offset(1)` was held
//! (`option-slice-value:one-element-carrier`) rather than delivered.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

/// wave-6s2's witness shape (brotli `BrotliFindAllStaticDictionaryMatches::
/// {s, s_0, s_1, s_2}`, lodepng `addChunk_IHDR::data`), reduced by them and
/// used verbatim here.
const COMPUTED_VIEW: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn FindMatches(mut data: *const u8, max_length: usize, mut out: *mut u32) -> i32 {
    let mut s = 0 as *const u8;
    let mut l: usize = 0;
    let mut found = 0;
    while l < max_length {
        if *data.offset(l as isize) as i32 == ' ' as i32 { l = l.wrapping_add(1); continue; }
        s = &*data.offset(l as isize) as *const u8;
        if *s.offset(0 as isize) as i32 == 'a' as i32 { *out.offset(found as isize) = l as u32; found += 1; }
        if *s.offset(1 as isize) as i32 == 'b' as i32 { found += 1; }
        l = l.wrapping_add(1);
    }
    found
}
"#;

/// **Both frames, under R217-2(a).** Which frame this runs on decides what is
/// assertable, so the witness spells both rather than pinning one:
///
/// * **lane frame** — `&*data.offset(l)` is itself the use that walls the base
///   into the cursor family (`slice-cursor-use`), so there is no delivered
///   slice to take a suffix of: the destination keeps its typed hold and this
///   arm adds no rendering of its own. This is the control that the arm is
///   inert without a delivered base.
/// * **composed frame** (wave-6s2's line in: `batch-11-dry10`) — the base
///   delivers, and then the invariant is the one this arm exists for: the
///   destination is NEVER a one-element `from_ref` carrier for a shape read
///   past its first element; it is either still held (before wave-5d's
///   supersession retirement, R448-4) or the suffix.
///
/// Measured on both: lane head `403f20e5`, and `batch-11-dry10` (`52c53f1d`).
#[test]
fn wave6o_suffix_arm_is_inert_without_a_delivered_base() {
    assert!(verify::type_checks_str(COMPUTED_VIEW));
    let base_delivers = ::utils::compilation::run_compiler_on_str(COMPUTED_VIEW, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        let reason = |name: &str| {
            table
                .entries
                .iter()
                .find(|(subject, _)| subject.param_name.as_deref() == Some(name))
                .map(|(_, decision)| match decision {
                    Decision::Degraded(degradation) => degradation.reason.key().to_owned(),
                    other => format!("{other:?}").chars().take(20).collect::<String>(),
                })
                .unwrap_or_else(|| "<absent>".to_owned())
        };
        let base = reason("data");
        if base == "slice-cursor-use" {
            assert_eq!(
                reason("s"),
                "null-init",
                "lane frame: no delivered base, so the destination keeps its hold"
            );
            false
        } else {
            assert!(
                base.starts_with("Slice"),
                "composed frame: the base delivers as a slice, got {base}"
            );
            true
        }
    })
    .expect("fixture compiler context");
    let output = ast_emitted_source_of(COMPUTED_VIEW).expect("native emission");
    assert!(
        !output.contains("from_ref"),
        "a destination read past its first element is never a one-element carrier:\n{output}"
    );
    if !base_delivers {
        assert!(!output.contains("Option<&[u8]>"), "{output}");
    }
    assert!(verify::type_checks_str(&output), "{output}");
}

/// **The delivering half.** Where the base DOES deliver — wave-6s2's line
/// lifts the wall, this lane's declaration types the destination — the value
/// is `Some(&data[l..])` and the two reads become `s[0]` / `s[1]`.
///
/// `#[ignore]`d with its frame: measured on `batch-10-dry8` (`2bdee574b`) plus
/// this arm, where `data` does deliver (`mut data: &[u8]`) — and there the row
/// is blocked one stage EARLIER than this arm: the Option family for the owner
/// falls back because the source's `computed-suffix-raw-view` slice-use
/// adapter (boundary evidence `body-local-raw-alias-schedule-unproved`) is
/// DROPPED as `slice-use-evidence-held` when the Option stage re-derives its
/// exclusions, so the destination never reaches the value planner. Report 016
/// STOP 1 routes that; this witness turns live when it is answered.
#[test]
#[ignore = "blocked upstream of this arm: on dry8 the owner's Option family falls back on the source's computed-suffix-raw-view adapter being dropped (slice-use-evidence-held) — report 016 STOP 1"]
fn wave6o_computed_view_of_a_delivered_slice_is_the_suffix() {
    let output = ast_emitted_source_of(COMPUTED_VIEW).expect("native emission");
    assert!(
        output.contains("let mut s: Option<&[u8]> = None"),
        "the destination is declared optional-slice: {output}"
    );
    assert!(
        output.contains("s = Some(&data[(l) as usize..])")
            || output.contains("s = Some(&data[l..])"),
        "the value is the suffix, not a one-element carrier: {output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}
/// **The forward-delta control (relay 034).** NOT a fault catcher — see report 023 claim 6: The same shape with
/// a SIGNED delta — `k: i32`, which may run backwards — must never take the
/// suffix: a backward view belongs to the cursor family. Dropping the guard in
/// `forward_delta` makes this fixture render `Some(&data[(k) as usize..])`,
/// which is what the fault must break.
const SIGNED_DELTA: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn FindSigned(mut data: *const u8, max_length: usize, mut k: i32) -> i32 {
    let mut s = 0 as *const u8;
    let mut l: usize = 0;
    let mut found = 0;
    while l < max_length {
        if *data.offset(l as isize) as i32 == ' ' as i32 { l = l.wrapping_add(1); continue; }
        s = &*data.offset(k as isize) as *const u8;
        if *s.offset(0 as isize) as i32 == 'a' as i32 { found += 1; }
        if *s.offset(1 as isize) as i32 == 'b' as i32 { found += 1; }
        l = l.wrapping_add(1);
    }
    found
}
"#;

#[test]
fn wave6o_signed_delta_never_takes_the_suffix() {
    assert!(verify::type_checks_str(SIGNED_DELTA));
    let output = ast_emitted_source_of(SIGNED_DELTA).expect("native emission");
    assert!(
        !output.contains("Some(&data["),
        "a signed delta may run backwards: the suffix arm must refuse it:\n{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}
