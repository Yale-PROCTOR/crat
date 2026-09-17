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

/// **The arm is inert where the base does not deliver.** On this lane's own
/// frame `data` is walled into the cursor family by the very
/// `&*data.offset(l)` use (`slice-cursor-use`), so there is no delivered slice
/// to take a suffix of: the destination keeps its existing typed hold and the
/// emitted tree is unchanged. This is the control that the new arm adds no
/// rendering of its own without a delivered base.
#[test]
fn wave6o_suffix_arm_is_inert_without_a_delivered_base() {
    assert!(verify::type_checks_str(COMPUTED_VIEW));
    ::utils::compilation::run_compiler_on_str(COMPUTED_VIEW, |tcx| {
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
        assert_eq!(
            reason("data"),
            "slice-cursor-use",
            "the base is not delivered on this frame, so the suffix arm has nothing to build from"
        );
        assert_eq!(
            reason("s"),
            "null-init",
            "and the destination keeps its existing hold"
        );
    })
    .expect("fixture compiler context");
    let output = ast_emitted_source_of(COMPUTED_VIEW).expect("native emission");
    assert!(
        !output.contains("Option<&[u8]>") && verify::type_checks_str(&output),
        "{output}"
    );
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
