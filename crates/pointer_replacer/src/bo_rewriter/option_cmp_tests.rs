//! Wave-6o reductions of rgba::rgba_from_rgb_string and heman::kmVec2Assign:
//! a pointer EQUALITY whose other operand is not a safe subject (a foreign
//! call result; an analysis-raw partner) keeps that operand raw and gives the
//! safe subject an explicit address view.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

fn decision_of(input: &str, function: &str, binding: &str) -> Decision {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.param_name.as_deref() == Some(binding)
            })
            .map(|(_, decision)| decision.clone())
            .expect("corpus-derived subject")
    })
    .expect("fixture compiler context")
}

fn admitted_comparison(input: &str, function: &str, binding: &str, expected: &str) {
    assert!(verify::type_checks_str(input));
    let decision = decision_of(input, function, binding);
    assert!(
        !matches!(decision, Decision::Degraded(_)),
        "the comparison must not degrade {function}::{binding}: {decision:?}"
    );
    let output = ast_emitted_source_of(input).expect("native emission");
    assert!(
        output
            .split_whitespace()
            .collect::<String>()
            .contains(&expected.split_whitespace().collect::<String>()),
        "the safe operand must receive its address view: expected `{expected}` in\n{output}"
    );
    eprintln!("WAVE6O_CMP_OUTPUT_BEGIN {function}\n{output}\nWAVE6O_CMP_OUTPUT_END");
    assert!(
        verify::type_checks_str(&output),
        "emitted comparison must compile: {output}"
    );
}

/// rgba::rgba_from_rgb_string — `str == strstr(str, "rgb(")`: the other
/// operand is a foreign call result, not a subject.
#[test]
fn wave6o_rgba_shared_subject_equals_foreign_call_result() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe extern "C" { fn strstr(h: *const i8, n: *const i8) -> *mut i8; }
unsafe fn rgba_from_rgb_string(str: *const i8) -> i32 {
    if str.is_null() { return 0; }
    if str == strstr(str, b"rgb(\0".as_ptr() as *const i8) as *const i8 {
        return 1;
    }
    return *str as i32;
}
"#;
    admitted_comparison(
        input,
        "rgba_from_rgb_string",
        "str",
        "if str.as_deref().map_or(core::ptr::null::<i8>(), core::ptr::from_ref) == strstr(",
    );
}

/// heman::kmVec2Assign — `pOut == pIn as *mut kmVec2`: the partner is an
/// analysis-raw parameter (it is read through a raw-only operation), so it
/// stays raw while the mutable subject receives an explicit `from_mut` view.
/// (The corpus function also RETURNS `pOut`, its own co-blocker — the
/// reduction returns an integer so the witness is about the comparison.)
#[test]
fn wave6o_heman_mutable_subject_equals_raw_partner() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
#[repr(C)] struct KmVec2 { x: f32, y: f32 }
unsafe fn kmVec2Assign(pOut: *mut KmVec2, pIn: *const KmVec2) -> i32 {
    if pOut == pIn as *mut KmVec2 { return 0; }
    (*pOut).x = pIn.read().x;
    (*pOut).y = pIn.read().y;
    return 1;
}
"#;
    assert!(verify::type_checks_str(input));
    assert!(
        matches!(
            decision_of(input, "kmVec2Assign", "pIn"),
            Decision::Degraded(_)
        ),
        "the fixture partner must stay raw"
    );
    admitted_comparison(
        input,
        "kmVec2Assign",
        "pOut",
        "if core::ptr::from_mut(&mut *pOut) == pIn as *mut KmVec2 {",
    );
}

/// An ORDERING comparison is a cursor shape (wave-6s / slicecursor): a subject
/// that is also advanced by `offset` keeps its hold here.
#[test]
fn wave6o_ordering_on_an_advanced_pointer_keeps_its_hold() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn ShannonEntropy(mut population: *const u32, size: usize) -> u32 {
    let mut sum = 0u32;
    let population_end = population.offset(size as isize);
    while population < population_end {
        sum = sum.wrapping_add(*population);
        population = population.offset(1);
    }
    return sum;
}
"#;
    assert!(verify::type_checks_str(input));
    let decision = decision_of(input, "ShannonEntropy", "population");
    assert!(
        matches!(decision, Decision::Degraded(_)),
        "an advanced pointer under an ordering comparison is not this lane's: {decision:?}"
    );
    // An ORDERING against a raw partner is not opened one-sidedly either:
    // the value-only partner keeps its hold.
    let ordered = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn before(a: *const u32, end: *const u32) -> u32 {
    if a < end { return 1; }
    return a.read();
}
"#;
    assert!(verify::type_checks_str(ordered));
    assert!(matches!(
        decision_of(ordered, "before", "a"),
        Decision::Degraded(_)
    ));
    let partner = decision_of(ordered, "before", "end");
    assert!(
        matches!(partner, Decision::Degraded(_)),
        "an ordering partner of a raw pointer keeps its hold: {partner:?}"
    );
    let output = ast_emitted_source_of(input).expect("hold emission");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// An optional operand whose comparison receives NO address view (an ordering
/// against a raw expression) keeps its hold rather than an applied receipt the
/// emitter cannot honour.
#[test]
fn wave6o_option_ordering_without_a_view_keeps_typed_hold() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe extern "C" { fn limit() -> *const i8; }
unsafe fn below_limit(str: *const i8) -> i32 {
    if str.is_null() { return 0; }
    if str < limit() { return 1; }
    return *str as i32;
}
"#;
    assert!(verify::type_checks_str(input));
    let (decision, receipts) = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("typed hold decisions");
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.param_name.as_deref() == Some("str"))
            .expect("subject");
        (
            decision.clone(),
            table
                .option_receipts
                .iter()
                .map(|receipt| {
                    format!(
                        "{}:{:?}:{:?}",
                        receipt.operation,
                        receipt.obligation.intended_terminal_state,
                        receipt.obligation.intended_terminal_reason
                    )
                })
                .collect::<Vec<_>>(),
        )
    })
    .expect("hold compiler context");
    // The ladder's comparison gate and the address arm are the same predicate,
    // so an ordering against a raw expression never reaches the Option family:
    // the hold is the ladder's `ptr-comparison`, with no applied receipt.
    assert!(matches!(decision, Decision::Degraded(_)), "{decision:?}");
    assert!(
        !receipts
            .iter()
            .any(|receipt| receipt.starts_with("address-observation:")
                && receipt.contains("Applied")),
        "no operand without a view may be applied: {receipts:?}"
    );
    let output = ast_emitted_source_of(input).expect("hold emission");
    assert!(verify::type_checks_str(&output), "{output}");
}
