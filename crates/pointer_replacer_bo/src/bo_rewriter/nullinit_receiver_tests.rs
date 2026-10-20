//! **W6S-16 (R609-4, wave-6s 088 N1a) — a null-initialised C-string receiver
//! of a raw-returning local callee.** lil's `fnc_charat::str`,
//! `fnc_rename::oldname`, …: `let mut s = 0 as *const c_char;` re-assigned from
//! a local callee whose return stays raw (`lil_to_string`), handed to a libc
//! string function and indexed. The form is an optional SLICE; the refusal
//! that kept it `null-init` is the assignment clause of
//! `slice_local_construction::refuses`, and the value's extent is the string's
//! own (R491-7), never the fallback.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_assignments)]
unsafe extern "C" { fn strlen(s: *const i8) -> usize; }
#[repr(C)] pub struct Value { d: *mut i8, l: usize }
pub unsafe fn to_string(v: *mut Value) -> *const i8 {
    return if !v.is_null() && !(*v).d.is_null() { (*v).d as *const i8 } else { b"\0" as *const u8 as *const i8 };
}
"#;

/// lil's `fnc_charat::str`: licensed by `strlen`, indexed.
const INDEXED: &str = r#"
pub unsafe fn charat(v: *mut Value, index: usize) -> i8 {
    let mut s = 0 as *const i8;
    s = to_string(v);
    if index >= strlen(s) { return 0; }
    return *s.offset(index as isize);
}
"#;

/// lil's `fnc_rename::oldname`: null-tested, licensed by `strlen`.
const NULL_TESTED: &str = r#"
pub unsafe fn rename(v: *mut Value) -> usize {
    let mut s = 0 as *const i8;
    s = to_string(v);
    if s.is_null() { return 0; }
    return strlen(s);
}
"#;

/// Control: the same receiver, indexed, but no libc string function reads it,
/// so nothing establishes the terminator and no extent exists.
const UNLICENSED: &str = r#"
pub unsafe fn second(v: *mut Value) -> i8 {
    let mut s = 0 as *const i8;
    s = to_string(v);
    if s.is_null() { return 0; }
    return *s.offset(1 as isize);
}
"#;

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
            .expect("the fixture local")
    })
    .expect("fixture compiler context")
}

fn delivers(body: &str, function: &str) {
    let input = format!("{PRELUDE}{body}");
    assert!(verify::type_checks_str(&input));
    let decision = decision_of(&input, function, "s");
    assert!(
        matches!(
            decision,
            Decision::Opt {
                mutable: false,
                slice: true,
                ..
            }
        ),
        "{function}::s must deliver an optional shared slice: {decision:?}"
    );
    let output = ast_emitted_source_of(&input).expect("native emission");
    assert!(
        output.contains("let mut s: Option<&[i8]> = None;"),
        "the declaration: {output}"
    );
    assert!(
        output.contains("core::ffi::CStr::from_ptr(") && !output.contains("FALLBACK_SLICE_EXTENT"),
        "the extent is the string's own, never the fallback: {output}"
    );
    eprintln!("W6S16_EMITTED_BEGIN {function}\n{output}\nW6S16_EMITTED_END");
    assert!(verify::type_checks_str(&output), "emitted: {output}");
}

#[test]
fn w6s16_an_indexed_c_string_receiver_takes_its_own_extent() {
    delivers(INDEXED, "charat");
}

#[test]
fn w6s16_a_null_tested_c_string_receiver_takes_its_own_extent() {
    delivers(NULL_TESTED, "rename");
}

#[test]
fn w6s16_control_a_receiver_no_string_function_reads_keeps_null_init() {
    let input = format!("{PRELUDE}{UNLICENSED}");
    let decision = decision_of(&input, "second", "s");
    assert!(
        matches!(&decision, Decision::Degraded(d) if d.reason.key() == "null-init"),
        "{decision:?}"
    );
}

/// Control: the callee's return is CONVERTED (it returns its parameter, a
/// native return permit, as `option_receiver_tests`' `target`) — the receiver
/// carrier's value, which a constructor over it would mistype. The C-string arm
/// must not take it.
const CONVERTED: &str = r#"
unsafe fn same(p: *mut i8) -> *mut i8 { if !p.is_null() { *p += 1; } p }
pub unsafe fn user() -> usize {
    let mut value: i8 = 3;
    let mut s = 0 as *const i8;
    s = same(&mut value) as *const i8;
    if s.is_null() { return 0; }
    return strlen(s);
}
"#;

#[test]
fn w6s16_control_a_converted_return_keeps_the_carriers_form() {
    let input = format!("{PRELUDE}{CONVERTED}");
    let (permit, interface) = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let same = tcx
            .hir_body_owners()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == "same")
            .expect("the callee");
        (
            ctx.lifetime_eligibility.thin_return_permit(same),
            table
                .return_interfaces
                .functions
                .get(&same)
                .map(|i| format!("{:?}", i.form)),
        )
    })
    .expect("fixture compiler context");
    eprintln!("W6S16_CONVERTED permit={permit} interface={interface:?}");
    assert!(permit, "the control's premise: `same`'s return converts");
    let output = ast_emitted_source_of(&input).expect("native emission");
    assert!(!output.contains("__crat_cstr_ptr_"), "{output}");
    assert!(verify::type_checks_str(&output), "emitted: {output}");
}
