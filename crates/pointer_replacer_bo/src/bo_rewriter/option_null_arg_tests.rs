//! Wave-6o (relay 009): a parameter that some caller passes the NULL LITERAL
//! is nullable by that caller's evidence and takes the optional form —
//! brotli `BrotliEncoderCompressStream::total_out` (passed on to null-testing
//! local callees; `CompressFiles` passes `0 as *mut size_t`).
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

const INPUT: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
#[repr(C)] struct State { total: usize }
unsafe fn InjectFlushOrPushOutput(s: *mut State, total_out: *mut usize) -> i32 {
    if !total_out.is_null() { *total_out = (*s).total; }
    return 1;
}
unsafe fn BrotliEncoderCompressStream(s: *mut State, total_out: *mut usize) -> i32 {
    if s.is_null() { return 0; }
    return InjectFlushOrPushOutput(s, total_out);
}
unsafe fn CompressFiles(s: *mut State) -> i32 {
    if s.is_null() { return 0; }
    let mut out: usize = 0;
    if BrotliEncoderCompressStream(s, 0 as *mut usize) == 0 { return 0; }
    return BrotliEncoderCompressStream(s, &mut out);
}
"#;

/// The pass-through parameter takes the optional form because a caller
/// passes it the null literal; the null-literal caller renders `None`, the
/// `&mut` caller `Some(&mut out)`, and the pass-on to the null-testing
/// callee is same-form.
#[test]
fn wave6o_null_literal_argument_makes_the_parameter_optional() {
    assert!(verify::type_checks_str(INPUT));
    let (decision, reason) = decision_and_reason(INPUT, "BrotliEncoderCompressStream", "total_out");
    assert!(
        matches!(decision, Decision::Opt { slice: false, .. }),
        "a null-literal caller makes the parameter optional: {decision:?} {reason}"
    );
    let output = ast_emitted_source_of(INPUT).expect("native emission");
    assert!(output.contains("total_out: Option<&mut usize>"), "{output}");
    let flat = output.split_whitespace().collect::<String>();
    assert!(
        flat.contains("BrotliEncoderCompressStream(s,None)"),
        "{output}"
    );
    assert!(
        flat.contains("BrotliEncoderCompressStream(s,Some(&mutout))"),
        "{output}"
    );
    eprintln!("WAVE6O_NULLARG_OUTPUT_BEGIN\n{output}\nWAVE6O_NULLARG_OUTPUT_END");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// The control: with no null-literal caller the parameter stays a plain
/// reference (no optional is invented).
#[test]
fn wave6o_without_a_null_literal_caller_the_parameter_stays_plain() {
    let input = INPUT.replace(
        "if BrotliEncoderCompressStream(s, 0 as *mut usize) == 0 { return 0; }\n",
        "",
    );
    assert!(verify::type_checks_str(&input));
    let (decision, reason) =
        decision_and_reason(&input, "BrotliEncoderCompressStream", "total_out");
    assert!(
        matches!(decision, Decision::Ref { .. }),
        "no null evidence, no optional: {decision:?} {reason}"
    );
}
