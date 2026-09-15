//! Wave-4 candidate #1 production witnesses.

const CE_W01_STRLEN: &str = r#"
#![allow(dead_code, unused_unsafe)]
extern "C" {
    fn strlen(value: *const i8) -> usize;
}

pub unsafe fn ce_w01_strlen(value: *const i8) -> usize {
    strlen(value)
}
"#;

#[test]
fn ce_w01_strlen_contract_promotes_the_arr_subject_and_receipts_fallback() {
    let decisions = super::emit_tests::decisions_of(CE_W01_STRLEN);
    let value = decisions
        .iter()
        .find(|(name, is_param, _)| name == "value" && *is_param)
        .expect("CE-W01 value subject");
    assert_eq!(value.2, "<emitted>", "CE-W01 stayed RED: {decisions:#?}");

    let promotion = ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(CE_W01_STRLEN),
        |tcx| {
            let table = super::decide_table(tcx)?;
            table
                .contract_extent_promotions
                .values()
                .next()
                .cloned()
                .ok_or_else(|| "CE-W01 promotion receipt missing".to_owned())
        },
    )
    .expect("CE-W01 fixture compiles")
    .expect("CE-W01 decision table");
    assert_eq!(
        promotion.length,
        super::decision::contract_extent::LengthPlan::Fallback(
            super::decision::contract_extent::FallbackReason::NulTerminated
        )
    );

    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(CE_W01_STRLEN) else {
        panic!("CE-W01 must emit");
    };
    assert!(source.contains("value: &[i8]"), "{source}");
    assert!(source.contains("strlen(value.as_ptr())"), "{source}");
    assert!(super::verify::type_checks_str(&source), "{source}");
}

#[test]
fn ce_w01_terminal_slice_use_receipt_owns_the_contract_promotion() {
    let super::RewriteOutcome::Emitted {
        raw_boundary_artifacts,
        ..
    } = super::rewrite_m1(CE_W01_STRLEN)
    else {
        panic!("CE-W01 receipt fixture must emit");
    };
    let rows = raw_boundary_artifacts
        .slice_use_rows
        .iter()
        .filter(|row| row.contract_extent.is_some())
        .collect::<Vec<_>>();
    assert_eq!(rows.len(), 2, "one plan and one terminal row: {rows:#?}");
    let terminal = rows
        .iter()
        .find(|row| row.terminal.stage == super::mechanical_receipt::MechanicalStage::Terminal)
        .expect("terminal contract-extent row");
    assert_eq!(
        terminal.terminal.state,
        super::mechanical_receipt::MechanicalState::Applied
    );
    assert_eq!(
        terminal.retention,
        super::mechanical_receipt::MechanicalRetention::T1
    );
    let promotion = terminal
        .contract_extent
        .as_ref()
        .expect("promotion payload");
    assert_eq!(
        promotion.length,
        super::decision::contract_extent::LengthPlan::Fallback(
            super::decision::contract_extent::FallbackReason::NulTerminated
        )
    );
}

fn promotions(source: &str) -> Vec<super::decision::contract_extent::Promotion> {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(source), |tcx| {
        let table = super::decide_table(tcx)?;
        Ok::<_, String>(table.contract_extent_promotions.into_values().collect())
    })
    .expect("contract-extent fixture compiles")
    .expect("contract-extent decision table")
}

fn fact_debug(source: &str) -> String {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(source), |tcx| {
        let (table, ctx) = super::decide_table_with_ctx(tcx)?;
        Ok::<_, String>(format!(
            "paths={:#?}\nforeign={:#?}\ndecisions={:#?}",
            ctx.facts.raw_boundary_argument_paths(),
            ctx.facts.foreign_call_args,
            (
                table.entries,
                ctx.raw_boundary_artifacts.additive_family_receipts
            ),
        ))
    })
    .expect("slice-use debug fixture compiles")
    .expect("slice-use debug table")
}

fn emitted(source: &str) -> String {
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(source) else {
        panic!("contract-extent fixture must emit")
    };
    assert!(super::verify::type_checks_str(&source), "{source}");
    source
}

#[test]
#[ignore = "candidate #1b (R384-3): exact-count entry transport"]
fn ce_w02_memcpy_exact_count_keeps_both_initialized_byte_slices_evidence_backed() {
    let source = r#"
        #![allow(dead_code, unused_unsafe, unused_mut)]
        extern "C" { fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8; }
        unsafe fn copy(dest: *mut u8, src: *const u8, n: usize) {
            memcpy(dest, src, n);
        }
        pub unsafe fn caller(n: usize) -> u8 {
            let mut dest = [0u8; 8];
            let src = [1u8; 8];
            copy(dest.as_mut_ptr(), src.as_ptr(), n);
            dest[0]
        }
    "#;
    let plans = promotions(source);
    assert_eq!(
        plans.len(),
        2,
        "plans={plans:#?}\ndecisions={:#?}\nslice_uses={}",
        super::emit_tests::decisions_of(source),
        fact_debug(source),
    );
    assert!(
        plans.iter().all(|plan| matches!(
            &plan.length,
            super::decision::contract_extent::LengthPlan::Evidence {
                elements,
                source: super::decision::contract_extent::LengthSource::ExactContract {
                    argument_index: 2,
                    ..
                },
            } if elements.trim() == "n"
        )),
        "{plans:#?}"
    );
    let output = emitted(source);
    assert!(output.contains("dest: &mut [u8]"), "{output}");
    assert!(output.contains("src: &[u8]"), "{output}");
    assert!(!output.contains("FALLBACK_SLICE_EXTENT"), "{output}");
    assert!(
        output.contains("memcpy(dest_ptr.as_mut_ptr(), src_ptr.as_ptr(), n)"),
        "{output}"
    );
}

#[test]
fn ce_w03_one_element_contract_does_not_create_a_slice_promotion() {
    let source = r#"
        #![allow(dead_code, unused_unsafe)]
        #[repr(C)] pub struct Stat { size: i64 }
        extern "C" { fn stat(path: *const i8, value: *mut Stat) -> i32; }
        pub unsafe fn read(value: *mut Stat) -> i64 {
            stat(b"x\0".as_ptr() as *const i8, value);
            (*value).size
        }
    "#;
    assert!(promotions(source).is_empty());
    assert!(!emitted(source).contains("value: &mut [Stat]"));
}

#[test]
fn ce_w04_arithmetic_slice_keeps_its_original_owner_and_length_path() {
    let source = r#"
        #![allow(dead_code, unused_unsafe)]
        extern "C" { fn strlen(value: *const i8) -> usize; }
        pub unsafe fn indexed(value: *mut i8) -> i8 {
            *value.offset(1) = 7;
            let _ = strlen(value);
            *value
        }
    "#;
    assert!(
        promotions(source).is_empty(),
        "the arithmetic arm owns this Slice"
    );
    let output = emitted(source);
    assert!(output.contains("value: &mut [i8]"), "{output}");
    assert!(output.contains("value[1] = 7"), "{output}");
}

#[test]
fn ce_w05_contract_extent_cannot_bypass_raw_use_or_exist_without_an_operation() {
    let raw = r#"
        #![allow(dead_code, unused_unsafe)]
        extern "C" { fn strlen(value: *const i8) -> usize; }
        pub unsafe fn opaque(value: *const i8) -> usize {
            let address = value.addr();
            strlen(value) + address
        }
    "#;
    assert!(promotions(raw).is_empty());
    assert!(
        super::emit_tests::decisions_of(raw)
            .iter()
            .any(|(name, _, reason)| name == "value" && reason != "<emitted>")
    );

    let arithmetic_only = r#"
        #![allow(dead_code, unused_unsafe)]
        pub unsafe fn indexed(value: *const i8) -> i8 { *value.offset(1) }
    "#;
    assert!(promotions(arithmetic_only).is_empty());
    assert!(emitted(arithmetic_only).contains("value: &[i8]"));
}

#[test]
fn ce_w06_nullable_contract_subject_uses_an_optional_slice_without_null_construction() {
    let source = r#"
        #![allow(dead_code, unused_unsafe)]
        extern "C" { fn strlen(value: *const i8) -> usize; }
        pub unsafe fn maybe_len(value: *const i8) -> usize {
            if value.is_null() { 0 } else { strlen(value) }
        }
    "#;
    let plans = promotions(source);
    assert_eq!(plans.len(), 1, "{plans:#?}");
    assert!(plans[0].nullable, "{plans:#?}");
    let output = emitted(source);
    assert!(output.contains("value: Option<&[i8]>"), "{output}");
    assert!(output.contains("value.is_none()"), "{output}");
    assert!(output.contains("slice.as_ptr()"), "{output}");
    assert!(
        !output.contains("from_raw_parts"),
        "no slice is constructed inside the nullable callee: {output}"
    );

    let zero_count = r#"
        #![allow(dead_code, unused_unsafe)]
        extern "C" { fn snprintf(dest: *mut i8, n: usize, fmt: *const i8, ...) -> i32; }
        pub unsafe fn size() -> i32 { snprintf(core::ptr::null_mut(), 0, b"x\0".as_ptr() as *const i8) }
    "#;
    assert!(promotions(zero_count).is_empty());
    assert!(emitted(zero_count).contains("snprintf(core::ptr::null_mut(), 0"));
}

#[test]
fn ce_w07_strncpy_source_count_is_an_upper_bound_and_never_exact_evidence() {
    let source = r#"
        #![allow(dead_code, unused_unsafe)]
        extern "C" { fn strncpy(dest: *mut i8, src: *const i8, n: usize) -> *mut i8; }
        pub unsafe fn bounded(src: *const i8, n: usize) {
            let mut dest = [0i8; 8];
            strncpy(dest.as_mut_ptr(), src, n);
        }
    "#;
    let plans = promotions(source);
    assert_eq!(
        plans.len(),
        1,
        "only the readable source is eligible: {plans:#?}"
    );
    assert_eq!(
        plans[0].length,
        super::decision::contract_extent::LengthPlan::Fallback(
            super::decision::contract_extent::FallbackReason::UpperBound
        )
    );
}

#[test]
fn multiline_count_expression_is_single_line_only_in_the_receipt() {
    let source = r#"
        #![allow(dead_code, unused_unsafe)]
        extern "C" { fn strncpy(dest: *mut i8, src: *const i8, n: usize) -> *mut i8; }
        pub unsafe fn copy_file_name(src: *const i8) {
            let mut dest = [0i8; 1034];
            strncpy(dest.as_mut_ptr(), src, (1034usize - 10usize) as
                usize);
        }
    "#;
    let plans = promotions(source);
    assert_eq!(
        plans.len(),
        1,
        "only the readable source promotes: {plans:#?}"
    );
    assert_eq!(
        plans[0].length,
        super::decision::contract_extent::LengthPlan::Fallback(
            super::decision::contract_extent::FallbackReason::UpperBound
        )
    );
    let count_expression = plans[0]
        .sites
        .iter()
        .find_map(|site| match &site.requirement {
            super::decision::contract_extent::Requirement::UpperBound(Some(count)) => {
                count.elements.as_ref().ok()
            }
            _ => None,
        })
        .expect("upper-bound count operand");
    assert!(
        count_expression.contains('\n'),
        "the compiler fact retains the original expression: {count_expression:?}"
    );

    let super::RewriteOutcome::Emitted {
        source: output,
        raw_boundary_artifacts,
        ..
    } = super::rewrite_m1(source)
    else {
        panic!("multiline-count fixture must emit")
    };
    assert!(output.contains("strncpy("), "{output}");
    assert_eq!(output.matches("1034usize - 10usize").count(), 1, "{output}");

    let rendered =
        super::mechanical_receipt::render_slice_use_rows(&raw_boundary_artifacts.slice_use_rows);
    let lines = rendered.lines().collect::<Vec<_>>();
    assert_eq!(
        lines.len(),
        raw_boundary_artifacts.slice_use_rows.len() + 1,
        "one physical TSV line per logical receipt row:\n{rendered}"
    );
    let width = lines[0].split('\t').count();
    assert_eq!(width, 23, "specialized Slice-use schema width");
    assert!(
        lines[1..]
            .iter()
            .all(|line| line.split('\t').count() == width),
        "every data row keeps the header width:\n{rendered}"
    );
}

#[test]
#[ignore = "candidate #1b (R384-3): exact-count entry transport"]
fn ce_w08_conditional_count_expression_is_evaluated_once_at_the_original_call() {
    let source = r#"
        #![allow(dead_code, unused_unsafe, static_mut_refs)]
        extern "C" { fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8; }
        static mut CALLS: usize = 0;
        unsafe fn next_n() -> usize { CALLS += 1; 2 }
        unsafe fn copy(dest: *mut u8, src: *const u8, n: usize) {
            memcpy(dest, src, n);
        }
        pub unsafe fn conditional(run: bool) {
            let mut dest = [0u8; 4];
            let src = [1u8; 4];
            if run { copy(dest.as_mut_ptr(), src.as_ptr(), next_n()); }
        }
    "#;
    let plans = promotions(source);
    assert_eq!(
        plans.len(),
        2,
        "plans={plans:#?}\ndecisions={:#?}",
        super::emit_tests::decisions_of(source)
    );
    let output = emitted(source);
    assert_eq!(output.matches("next_n()").count(), 1, "{output}");
    let if_pos = output.find("if run").expect("conditional remains");
    let count_pos = output.find("next_n()").expect("count remains");
    assert!(count_pos > if_pos, "the count was hoisted: {output}");
}

#[test]
fn ce_w09_non_length_and_identity_failures_remain_held() {
    let uninitialized = r#"
        #![allow(dead_code, unused_unsafe)]
        extern "C" { fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8; }
        pub unsafe fn copy(dest: *mut u8, src: *const u8, n: usize) { memcpy(dest, src, n); }
    "#;
    let plans = promotions(uninitialized);
    assert_eq!(
        plans.len(),
        1,
        "the write-only parameter must not promote: {plans:#?}"
    );
    let decisions = super::emit_tests::decisions_of(uninitialized);
    assert!(
        decisions
            .iter()
            .any(|(name, _, reason)| name == "dest" && reason != "<emitted>"),
        "{decisions:#?}"
    );

    let wrong_signature = r#"
        #![allow(dead_code, unused_unsafe)]
        extern "C" { fn memcpy(dest: *mut u8, src: *const u8) -> *mut u8; }
        pub unsafe fn wrong(dest: *mut u8, src: *const u8) { let _ = memcpy(dest, src); }
    "#;
    assert!(promotions(wrong_signature).is_empty());

    let local_name = r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe fn memcpy(value: *const u8) -> u8 { *value }
        pub unsafe fn caller(value: *const u8) -> u8 { memcpy(value) }
    "#;
    assert!(promotions(local_name).is_empty());
}

// ---------------------------------------------------------------------------
// R397-6(b) — the up-front decline, and R395-2 at a contract-extent callee.
// ---------------------------------------------------------------------------

/// `from` is a NUL-terminated contract candidate that is ALSO handed to a
/// local callee that RETAINS it. Attempted, the candidate reaches the
/// slice-use adapter's local-callee site, finds positive retention there and
/// terminally reclassifies (`slice-use-evidence-held`; brotli 3021 / 3022 /
/// 3024 at the third census — 10 of 10 corpus contract candidates with a
/// local-callee use reclassified, 0 delivered); the owner's family transaction
/// then withdraws it. Declined up front, the candidate is never attempted: the
/// subject keeps the thin-extent backstop instead of a terminal
/// `slice-use-unsupported`, the typed receipt names the cause, and the sibling
/// `to` is delivered with no transaction at all.
const CE_D01_LOCAL_CALLEE_BOUNDARY: &str = r#"
#![allow(dead_code, unused_unsafe)]
extern "C" {
    fn strlen(s: *const i8) -> usize;
}
static mut SAVED: *const i8 = 0 as *const i8;
unsafe fn keep(p: *const i8) {
    SAVED = p;
}
pub unsafe fn ce_d01(to: *mut i8, from: *const i8) -> usize {
    *to.offset(1) = 0;
    keep(from);
    strlen(from)
}
"#;

#[test]
fn ce_d01_local_callee_boundary_declines_the_candidate_up_front() {
    let decisions = super::emit_tests::decisions_of(CE_D01_LOCAL_CALLEE_BOUNDARY);
    let reason = |name: &str| {
        decisions
            .iter()
            .find(|(subject, is_param, _)| subject == name && *is_param)
            .map(|(_, _, reason)| reason.as_str())
            .unwrap_or_else(|| panic!("no parameter {name}: {decisions:#?}"))
    };
    assert_eq!(
        reason("from"),
        "held:thin-extent",
        "a declined candidate resumes the ladder at the thin-extent backstop: {decisions:#?}"
    );
    assert_eq!(reason("to"), "<emitted>", "{decisions:#?}");
    let super::RewriteOutcome::Emitted {
        raw_boundary_artifacts,
        source,
        ..
    } = super::rewrite_m1(CE_D01_LOCAL_CALLEE_BOUNDARY)
    else {
        panic!("CE-D01 must emit");
    };
    let declines = &raw_boundary_artifacts.contract_candidate_declines;
    let rows = declines.lines().skip(1).collect::<Vec<_>>();
    assert_eq!(
        rows.len(),
        2,
        "one declined candidate, receipted under both forms: {declines}"
    );
    for (row, form) in rows.iter().zip(["nullable", "plain"]) {
        assert!(
            row.starts_with("ce_d01\tce_d01::from\t")
                && row.contains(&format!(
                    "\t{form}\tcontract-candidate-declined:local-callee-boundary\t"
                ))
                && row.ends_with("\tstrlen:pinned-libc-0.2.184:0:nul-terminated"),
            "the typed receipt names the subject, the form, the cause and the contract: {declines}"
        );
    }
    // Never attempted: no family transaction touches the owner.
    assert!(
        raw_boundary_artifacts
            .additive_family_receipts
            .iter()
            .all(|receipt| receipt.owner_path != "ce_d01"),
        "{:#?}",
        raw_boundary_artifacts.additive_family_receipts
    );
    assert!(source.contains("to: &mut [i8]"), "{source}");
    assert!(source.contains("from: *const i8"), "{source}");
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// The lil shape (third census, `lil_find_var::name#3` → `lil_find_local_var::
/// name#3`): the callee's parameter is promoted to a contract-extent slice
/// because `strcmp` reads it to the NUL, and the caller's THIN `&i8` was then
/// widened into it with `core::slice::from_ref` — one element of provenance
/// handed to a NUL-terminated read through `as_ptr()`. R395-2 forbids exactly
/// that widening; the caller is held as fix-2 holds a caller of a body-indexing
/// parameter, and the callee's raw wrapper takes the pointer's full provenance
/// under the slice-extent waiver instead.
const CE_D02_CALLER_THIN: &str = r#"
#![allow(dead_code, unused_unsafe)]
extern "C" {
    fn strcmp(a: *const i8, b: *const i8) -> i32;
}
unsafe fn find_local(name: *const i8) -> i32 {
    strcmp(name, b"x\0".as_ptr() as *const i8)
}
pub unsafe fn find(name: *const i8) -> i32 {
    find_local(name)
}
"#;

#[test]
fn ce_d02_a_thin_caller_argument_is_held_instead_of_widened_into_the_contract_slice() {
    let decisions = super::emit_tests::decisions_of(CE_D02_CALLER_THIN);
    let reason = |name: &str| {
        decisions
            .iter()
            .find(|(subject, is_param, _)| subject == name && *is_param)
            .map(|(_, _, reason)| reason.as_str())
            .unwrap_or_else(|| panic!("no parameter {name}: {decisions:#?}"))
    };
    // Both parameters are named `name`; the callee's is decided first in
    // source order, so distinguish by position in the artifact rows.
    let names = decisions
        .iter()
        .filter(|(subject, is_param, _)| subject == "name" && *is_param)
        .map(|(_, _, reason)| reason.as_str())
        .collect::<Vec<_>>();
    assert_eq!(names.len(), 2, "{decisions:#?}");
    let _ = reason;
    assert!(
        names.contains(&"<emitted>"),
        "the callee's contract slice is delivered: {decisions:#?}"
    );
    assert!(
        names.contains(&"held:local-callee-access-extent"),
        "the caller's thin argument is held, not widened: {decisions:#?}"
    );
    let detail = ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(CE_D02_CALLER_THIN),
        |tcx| {
            let table = super::decide_table(tcx)?;
            Ok::<_, String>(
                table
                    .entries
                    .iter()
                    .filter_map(|(_, decision)| match decision {
                        super::decision::Decision::Degraded(record) => Some(record.reason.detail()),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
            )
        },
    )
    .expect("CE-D02 fixture compiles")
    .expect("CE-D02 decision table");
    assert!(
        detail.iter().any(|detail| {
            detail.starts_with("find_local:name:read:foreign-contract:")
                && detail.contains("strcmp")
        }),
        "the hold names the callee, the parameter and the foreign contract: {detail:#?}"
    );
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(CE_D02_CALLER_THIN)
    else {
        panic!("CE-D02 must emit");
    };
    assert!(
        !source.contains("from_ref(name)") && !source.contains("from_mut(name)"),
        "no thin reference is widened at the local callee:\n{source}"
    );
    assert!(
        source.contains("core::slice::from_raw_parts(name, crate::FALLBACK_SLICE_EXTENT)"),
        "the callee's raw wrapper carries the pointer's own provenance:\n{source}"
    );
    assert!(source.contains("strcmp(name.as_ptr()"), "{source}");
    assert!(super::verify::type_checks_str(&source), "{source}");
}
