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

/// The corpus configuration: precise A5 replay under the frozen-graph
/// attestation, so a pair of distinct array-decay arguments is PROVEN disjoint
/// by the analysis rather than left undeterminable (the fixture default).
fn attested_promotions(source: &str) -> Vec<super::decision::contract_extent::Promotion> {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(source), |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )?;
        Ok::<_, String>(table.contract_extent_promotions.into_values().collect())
    })
    .expect("attested contract-extent fixture compiles")
    .expect("attested contract-extent decision table")
}

fn attested_emitted(source: &str) -> String {
    let super::RewriteOutcome::Emitted { source, .. } = attested_rewrite(source) else {
        panic!("attested contract-extent fixture must emit")
    };
    assert!(super::verify::type_checks_str(&source), "{source}");
    source
}

fn attested_rewrite(source: &str) -> super::RewriteOutcome {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "crat-wave4-attested-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("attested fixture directory");
    let root = dir.join("lib.rs");
    std::fs::write(&root, source).expect("attested fixture file");
    let outcome = super::rewrite_m1_path_a5_injected(
        &root,
        super::A5Mode::PreciseReplay,
        Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        &|_| {},
    );
    let _ = std::fs::remove_dir_all(&dir);
    outcome
}

#[test]
fn ce_w02_memcpy_exact_count_keeps_both_initialized_byte_slices_evidence_backed() {
    // #1b: `memcpy` returns its destination, so the destination is admitted
    // only where the caller discards the return (`memcpy(..);`); both
    // array-decay arguments then take the exact count from the contract's own
    // count argument (`n`, licensed because it spells no call), under the
    // corpus's attested A5 mode which proves the two arrays disjoint.
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
    let plans = attested_promotions(source);
    assert_eq!(plans.len(), 2, "plans={plans:#?}");
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
    let output = attested_emitted(source);
    assert!(output.contains("dest: &mut [u8]"), "{output}");
    assert!(output.contains("src: &[u8]"), "{output}");
    assert!(!output.contains("FALLBACK_SLICE_EXTENT"), "{output}");
    assert!(
        output.contains("memcpy(dest.as_mut_ptr(), src.as_ptr(), n)"),
        "{output}"
    );
    assert!(
        output.contains("core::slice::from_raw_parts_mut(dest.as_mut_ptr(), (n) as usize)")
            && output.contains("core::slice::from_raw_parts(src.as_ptr(), (n) as usize)"),
        "both constructions carry the exact count from the contract's own argument:\n{output}"
    );

    // The companion is the callee's PARAMETER that spells the count, found by
    // name, not the foreign call's own argument position.
    let reordered = r#"
        #![allow(dead_code, unused_unsafe, unused_mut)]
        extern "C" { fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8; }
        unsafe fn copy(count: usize, dest: *mut u8, src: *const u8) {
            memcpy(dest, src, count);
        }
        pub unsafe fn caller(count: usize) -> u8 {
            let mut dest = [0u8; 8];
            let src = [1u8; 8];
            copy(count, dest.as_mut_ptr(), src.as_ptr());
            dest[0]
        }
    "#;
    let output = attested_emitted(reordered);
    assert!(
        output.contains(
            "copy(count, core::slice::from_raw_parts_mut(dest.as_mut_ptr(), (count) as usize),"
        ) || output.contains("from_raw_parts_mut(dest.as_mut_ptr(), (count) as usize)"),
        "{output}"
    );
    assert!(!output.contains("FALLBACK_SLICE_EXTENT"), "{output}");

    // A USED return keeps the destination out (its returned alias needs the
    // returned-child custody #1b does not carry); the source still promotes.
    let used_return = r#"
        #![allow(dead_code, unused_unsafe, unused_mut)]
        extern "C" { fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8; }
        unsafe fn copy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8 {
            memcpy(dest, src, n)
        }
        pub unsafe fn caller(n: usize) -> u8 {
            let mut dest = [0u8; 8];
            let src = [1u8; 8];
            copy(dest.as_mut_ptr(), src.as_ptr(), n);
            dest[0]
        }
    "#;
    let plans = attested_promotions(used_return);
    assert_eq!(plans.len(), 1, "{plans:#?}");
    assert!(
        plans[0].subject.contains("binding=4"),
        "the source, not the destination: {plans:#?}"
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
fn ce_w08_conditional_count_expression_is_evaluated_once_at_the_original_call() {
    // A count that spells a CALL is not licensed as the constructions' length
    // (each construction would evaluate it again): both constructions take
    // the fabricated extent under the waiver and the count stays the single,
    // original scalar argument inside its conditional.
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
    let plans = attested_promotions(source);
    assert_eq!(plans.len(), 2, "plans={plans:#?}");
    let output = attested_emitted(source);
    assert_eq!(
        output.matches("next_n()").count(),
        2,
        "the declaration and the one call: {output}"
    );
    let if_pos = output.find("if run").expect("conditional remains");
    let count_pos = output.rfind("next_n()").expect("count remains");
    assert!(count_pos > if_pos, "the count was hoisted: {output}");
    assert_eq!(
        output.matches("crate::FALLBACK_SLICE_EXTENT").count(),
        2,
        "both constructions take the waived extent rather than re-evaluating the count:\n{output}"
    );
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
/// because `strcmp` reads it to the NUL. Under #1a the caller's THIN `&i8` was
/// widened into it with `core::slice::from_ref` — one element of provenance
/// handed to a NUL-terminated read (R395-2). Under #1b the callee's requirement
/// is propagated to the caller as a `via-local-callee` site (the reader chain
/// of relay 005 §2): BOTH take the slice form, the call is the zero-syntax
/// same-form carrier, and only the raw wrapper at the top of the chain takes
/// the pointer's own provenance under the slice-extent waiver.
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
fn ce_d02_a_thin_caller_argument_takes_the_slice_form_with_its_callee() {
    let decisions = super::emit_tests::decisions_of(CE_D02_CALLER_THIN);
    let names = decisions
        .iter()
        .filter(|(subject, is_param, _)| subject == "name" && *is_param)
        .map(|(_, _, reason)| reason.as_str())
        .collect::<Vec<_>>();
    assert_eq!(names, ["<emitted>", "<emitted>"], "{decisions:#?}");
    let plans = promotions(CE_D02_CALLER_THIN);
    assert_eq!(plans.len(), 2, "callee and caller both promote: {plans:#?}");
    assert!(
        plans.iter().any(|plan| plan
            .sites
            .iter()
            .any(|site| site.contract.starts_with("via-local-callee:"))),
        "the caller's site is the propagated requirement: {plans:#?}"
    );
    let super::RewriteOutcome::Emitted {
        raw_boundary_artifacts,
        source,
        ..
    } = super::rewrite_m1(CE_D02_CALLER_THIN)
    else {
        panic!("CE-D02 must emit");
    };
    assert_eq!(
        raw_boundary_artifacts
            .contract_candidate_declines
            .lines()
            .count(),
        1,
        "no decline: {}",
        raw_boundary_artifacts.contract_candidate_declines
    );
    assert!(
        !source.contains("from_ref(") && !source.contains("from_mut("),
        "no thin reference is widened at the local callee:\n{source}"
    );
    assert!(source.contains("fn find_local(name: &[i8])"), "{source}");
    assert!(source.contains("find_local(name)"), "{source}");
    assert!(
        source.contains("pub unsafe fn find(name: &[i8])"),
        "{source}"
    );
    // The same-form call is wave-5c's equal-slice interface carrier (landed
    // with batch 4); this lane adds no carrier of its own.
    let carriers = raw_boundary_artifacts
        .slice_use_rows
        .iter()
        .filter(|row| row.adapter == "owned-existing-c-same-slice")
        .collect::<Vec<_>>();
    assert_eq!(
        carriers.len(),
        2,
        "one plan and one terminal row: {carriers:#?}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// The same callee with a RAW caller argument (a static array's pointer, no
/// caller subject at all) promotes: the raw wrapper takes the pointer's own
/// provenance under the slice-extent waiver — the receipt is the fallback
/// extent, never a widened reference.
const CE_D03_RAW_CALLER: &str = r#"
#![allow(dead_code, unused_unsafe)]
extern "C" {
    fn strcmp(a: *const i8, b: *const i8) -> i32;
}
static KEY: [i8; 2] = [120, 0];
unsafe fn find_local(name: *const i8) -> i32 {
    strcmp(name, b"x\0".as_ptr() as *const i8)
}
pub unsafe fn find() -> i32 {
    find_local(KEY.as_ptr())
}
"#;

#[test]
fn ce_d03_a_raw_caller_argument_keeps_the_promotion() {
    let plans = promotions(CE_D03_RAW_CALLER);
    assert_eq!(plans.len(), 1, "{plans:#?}");
    let super::RewriteOutcome::Emitted {
        raw_boundary_artifacts,
        source,
        ..
    } = super::rewrite_m1(CE_D03_RAW_CALLER)
    else {
        panic!("CE-D03 must emit");
    };
    assert_eq!(
        raw_boundary_artifacts
            .contract_candidate_declines
            .lines()
            .count(),
        1,
        "no decline: {}",
        raw_boundary_artifacts.contract_candidate_declines
    );
    assert!(source.contains("name: &[i8]"), "{source}");
    assert!(
        source.contains("core::slice::from_raw_parts(KEY.as_ptr(), crate::FALLBACK_SLICE_EXTENT)"),
        "the raw argument takes the waived fallback extent at the call, never a widened reference:\n{source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// Three hops: the requirement travels `strcmp` → `find_local::name` →
/// `find::name`; the top caller hands a raw pointer, so exactly one fallback
/// construction exists and every hop between is zero-syntax.
const CE_D04_CHAIN: &str = r#"
#![allow(dead_code, unused_unsafe)]
extern "C" {
    fn strcmp(a: *const i8, b: *const i8) -> i32;
}
static KEY: [i8; 2] = [120, 0];
unsafe fn find_local(name: *const i8) -> i32 {
    strcmp(name, b"x\0".as_ptr() as *const i8)
}
unsafe fn find(name: *const i8) -> i32 {
    find_local(name)
}
pub unsafe fn top() -> i32 {
    find(KEY.as_ptr())
}
"#;

#[test]
fn ce_d04_the_requirement_propagates_along_the_whole_chain() {
    let plans = promotions(CE_D04_CHAIN);
    assert_eq!(plans.len(), 2, "{plans:#?}");
    let source = emitted(CE_D04_CHAIN);
    assert!(source.contains("fn find_local(name: &[i8])"), "{source}");
    assert!(source.contains("fn find(name: &[i8])"), "{source}");
    assert!(source.contains("find_local(name)"), "{source}");
    assert_eq!(
        source.matches("FALLBACK_SLICE_EXTENT").count(),
        2,
        "one construction at the top plus the constant's declaration:\n{source}"
    );
    assert!(!source.contains("from_ref("), "{source}");
}

/// A caller that CANNOT take the slice form stays thin, so its callee is
/// declined (`thin-caller-argument`) rather than widened: here the caller
/// also hands `name` to a retaining local callee, which declines its own
/// candidate (`local-callee-boundary`) and so leaves it a thin `&i8`.
const CE_D05_THIN_CALLER_STAYS: &str = r#"
#![allow(dead_code, unused_unsafe)]
extern "C" {
    fn strcmp(a: *const i8, b: *const i8) -> i32;
}
static mut SAVED: *const i8 = 0 as *const i8;
unsafe fn keep(p: *const i8) {
    SAVED = p;
}
unsafe fn find_local(name: *const i8) -> i32 {
    strcmp(name, b"x\0".as_ptr() as *const i8)
}
pub unsafe fn find(name: *const i8) -> i32 {
    keep(name);
    find_local(name)
}
"#;

#[test]
fn ce_d05_a_caller_that_stays_thin_declines_its_callee() {
    assert!(promotions(CE_D05_THIN_CALLER_STAYS).is_empty());
    let super::RewriteOutcome::Emitted {
        raw_boundary_artifacts,
        source,
        ..
    } = super::rewrite_m1(CE_D05_THIN_CALLER_STAYS)
    else {
        panic!("CE-D05 must emit");
    };
    let declines = &raw_boundary_artifacts.contract_candidate_declines;
    assert!(
        declines.contains("find_local\tfind_local::name\t")
            && declines.contains("\tplain\tcontract-candidate-declined:thin-caller-argument\t"),
        "{declines}"
    );
    assert!(
        declines.contains("find\tfind::name\t")
            && declines.contains("\tplain\tcontract-candidate-declined:local-callee-boundary\t"),
        "{declines}"
    );
    assert!(
        source.contains("fn find_local(name: *const i8)"),
        "{source}"
    );
    assert!(
        !source.contains("from_ref(") && !source.contains("from_mut("),
        "{source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

// ---------------------------------------------------------------------------
// #1b rider (R386-3): the counted-foreign contract for `fwrite` / `fread`.
// ---------------------------------------------------------------------------

/// The lodepng shape (wave-5r's finding): `fwrite(buffer as *const c_void, 1,
/// buffersize, file)` with `buffer: &c_uchar` read `buffersize` bytes through
/// a one-byte reference. With the row, the position is a counted contract
/// (`size * nmemb` bytes; a unit size is the count itself): the subject is
/// promoted to `&[u8]` with the EXACT count `buffersize`, and the local
/// caller's construction takes that count from the callee's own parameter.
const CE_F01_FWRITE_UNIT_SIZE: &str = r#"
#![allow(dead_code, unused_unsafe)]
#[repr(C)]
pub struct FILE {
    pub handle: i32,
}
extern "C" {
    fn fwrite(ptr: *const ::core::ffi::c_void, size: usize, nmemb: usize, stream: *mut FILE) -> usize;
}
pub static mut OUT: *mut FILE = 0 as *mut FILE;
unsafe fn save(buffer: *const u8, buffersize: usize) -> usize {
    fwrite(buffer as *const ::core::ffi::c_void, 1, buffersize, OUT)
}
pub unsafe fn caller(n: usize) -> usize {
    let bytes = [7u8; 16];
    save(bytes.as_ptr(), n)
}
"#;

#[test]
fn ce_f01_fwrite_unit_size_promotes_with_the_exact_element_count() {
    let plans = attested_promotions(CE_F01_FWRITE_UNIT_SIZE);
    assert_eq!(plans.len(), 1, "{plans:#?}");
    assert!(
        matches!(
            &plans[0].length,
            super::decision::contract_extent::LengthPlan::Evidence { elements, .. }
                if elements.trim() == "buffersize"
        ),
        "{plans:#?}"
    );
    let output = attested_emitted(CE_F01_FWRITE_UNIT_SIZE);
    assert!(output.contains("buffer: &[u8]"), "{output}");
    assert!(
        output.contains("fwrite(buffer.as_ptr().cast::<core::ffi::c_void>(), 1, buffersize, OUT)"),
        "{output}"
    );
    assert!(
        output.contains("core::slice::from_raw_parts(bytes.as_ptr(), (n) as usize)"),
        "the caller's construction takes the callee's own count parameter by name:\n{output}"
    );
    assert!(!output.contains("FALLBACK_SLICE_EXTENT"), "{output}");
}

/// A size that is NOT the element size (`fwrite(bytes, 4, n, f)` on a byte
/// pointer) writes `4 * n` bytes: the count is composed, never `n` alone.
/// This is R386-3's deliberate-fault shape made a witness — reading the count
/// as the element count would fabricate a slice one quarter of what is read.
const CE_F02_FWRITE_COMPOSED_SIZE: &str = r#"
#![allow(dead_code, unused_unsafe)]
#[repr(C)]
pub struct FILE {
    pub handle: i32,
}
extern "C" {
    fn fwrite(ptr: *const ::core::ffi::c_void, size: usize, nmemb: usize, stream: *mut FILE) -> usize;
}
pub static mut OUT: *mut FILE = 0 as *mut FILE;
unsafe fn save(buffer: *const u8, n: usize) -> usize {
    fwrite(buffer as *const ::core::ffi::c_void, 4, n, OUT)
}
pub unsafe fn caller(n: usize) -> usize {
    let bytes = [7u8; 16];
    save(bytes.as_ptr(), n)
}
"#;

#[test]
fn ce_f02_fwrite_composes_a_non_unit_size_into_the_count() {
    let plans = attested_promotions(CE_F02_FWRITE_COMPOSED_SIZE);
    assert_eq!(plans.len(), 1, "{plans:#?}");
    assert!(
        matches!(
            &plans[0].length,
            super::decision::contract_extent::LengthPlan::Evidence { elements, .. }
                if elements.trim() == "(4) * (n)"
        ),
        "{plans:#?}"
    );
    // The composed spelling is not a single parameter, so no caller argument
    // carries it: the caller's construction takes the fallback extent, and the
    // callee's own bridge still reads `4 * n` bytes of a slice that is at least
    // that long under the waiver.
    let output = attested_emitted(CE_F02_FWRITE_COMPOSED_SIZE);
    assert!(output.contains("buffer: &[u8]"), "{output}");
    assert!(output.contains("crate::FALLBACK_SLICE_EXTENT"), "{output}");
}

/// A non-byte element (`fwrite(values, 8, n, f)` over `*const f64`) keeps
/// the units unproved: the position is a contract, the subject promotes, and
/// the length is the typed count-gap fallback, never `8 * n` elements.
const CE_F03_FWRITE_NON_BYTE: &str = r#"
#![allow(dead_code, unused_unsafe)]
#[repr(C)]
pub struct FILE {
    pub handle: i32,
}
extern "C" {
    fn fwrite(ptr: *const ::core::ffi::c_void, size: usize, nmemb: usize, stream: *mut FILE) -> usize;
}
pub static mut OUT: *mut FILE = 0 as *mut FILE;
unsafe fn save(values: *const f64, n: usize) -> usize {
    fwrite(values as *const ::core::ffi::c_void, 8, n, OUT)
}
pub unsafe fn caller(n: usize) -> usize {
    let values = [0.5f64; 4];
    save(values.as_ptr(), n)
}
"#;

#[test]
fn ce_f03_fwrite_over_a_non_byte_element_keeps_the_units_gap() {
    let plans = attested_promotions(CE_F03_FWRITE_NON_BYTE);
    assert_eq!(plans.len(), 1, "{plans:#?}");
    assert_eq!(
        plans[0].length,
        super::decision::contract_extent::LengthPlan::Fallback(
            super::decision::contract_extent::FallbackReason::CountGap(
                super::decision::contract_extent::CountGap::UnitsUnproved
            )
        ),
        "{plans:#?}"
    );
}

/// R407-14 (contract-alone): bzip2's `fopen_output_safely` shape — `open` and
/// `fdopen` are not in the fatness libc table, so both parameters read `Ptr`,
/// and their ONLY uses are foreign NUL-terminated contract positions.
const CE_A01_CONTRACT_ALONE: &str = r#"
#![allow(dead_code, unused_unsafe)]
extern "C" {
    fn open(path: *const i8, flags: i32, mode: i32) -> i32;
    fn fdopen(fd: i32, mode: *const i8) -> *mut u8;
}
static mut OUT_NAME: [i8; 8] = [0; 8];
unsafe fn fopen_output_safely(name: *mut i8, mode: *const i8) -> *mut u8 {
    let fh = open(name, 1, 0o600);
    if fh == -1 {
        return 0 as *mut u8;
    }
    fdopen(fh, mode)
}
pub unsafe fn compress() -> *mut u8 {
    fopen_output_safely(OUT_NAME.as_mut_ptr(), b"wb\0".as_ptr() as *const i8)
}
"#;

#[test]
fn ce_a01_a_nul_contract_alone_parameter_promotes_over_ptr_fatness() {
    let plans = attested_promotions(CE_A01_CONTRACT_ALONE);
    assert_eq!(
        plans.len(),
        2,
        "both NUL-only parameters promote: {plans:#?}"
    );
    for plan in &plans {
        assert!(plan.contract_alone, "{plan:#?}");
        assert_eq!(
            plan.length,
            super::decision::contract_extent::LengthPlan::Fallback(
                super::decision::contract_extent::FallbackReason::NulTerminated
            )
        );
    }
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        ..
    } = attested_rewrite(CE_A01_CONTRACT_ALONE)
    else {
        panic!("CE-A01 must emit");
    };
    assert!(source.contains("name: &[i8]"), "{source}");
    assert!(source.contains("mode: &[i8]"), "{source}");
    assert!(source.contains("open(name.as_ptr(), 1, 0o600)"), "{source}");
    assert!(source.contains("fdopen(fh, mode.as_ptr())"), "{source}");
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains(
            "core::slice::from_raw_parts(OUT_NAME.as_mut_ptr(), crate::FALLBACK_SLICE_EXTENT)"
        ),
        "the array-decay caller takes the waived fallback extent:\n{source}"
    );
    assert!(
        flat.contains(
            "core::slice::from_raw_parts(b\"wb\\0\".as_ptr() as *const i8, crate::FALLBACK_SLICE_EXTENT)"
        ),
        "the literal caller takes the waived fallback extent:\n{source}"
    );
    let rendered =
        super::mechanical_receipt::render_slice_use_rows(&raw_boundary_artifacts.slice_use_rows);
    assert_eq!(
        rendered
            .lines()
            .filter(|line| line.contains("\tcontract-alone\tterminal\tapplied\t"))
            .count(),
        2,
        "the fatness column names the contract-alone admission at both terminal sites:\n{rendered}"
    );
    assert!(!rendered.contains("\tarr\t"), "{rendered}");
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// The negative half of R407-14: one dereference beside the NUL position and
/// the parameter is no longer contract-alone; `Ptr` fatness holds it.
const CE_A02_NOT_ALONE: &str = r#"
#![allow(dead_code, unused_unsafe)]
extern "C" {
    fn open(path: *const i8, flags: i32, mode: i32) -> i32;
}
unsafe fn open_nonempty(name: *const i8) -> i32 {
    if *name == 0 {
        return -1;
    }
    open(name, 1, 0o600)
}
"#;

#[test]
fn ce_a02_a_dereference_beside_the_nul_position_keeps_the_fatness_hold() {
    let plans = promotions(CE_A02_NOT_ALONE);
    assert!(plans.is_empty(), "{plans:#?}");
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(CE_A02_NOT_ALONE) else {
        panic!("CE-A02 must emit");
    };
    assert!(!source.contains("[i8]"), "{source}");
}

/// The model gate (wave-6v 008): a caller-side contract never outruns the
/// model's kind of the callee it forwards to. `find_local::name` is `Raw` to
/// the model (the mutable/reset copy shape of R213), so its `strcmp` position
/// carries no caller: `find::name`'s local boundary use is not carried into a
/// parameter that cannot promote, and `find::name` is declined at that
/// boundary instead of taking a slice it would bridge raw.
const CE_D06_RAW_CALLEE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments)]
extern "C" {
    fn strcmp(a: *const i8, b: *const i8) -> i32;
}
static mut KEY: [i8; 2] = [120, 0];
unsafe fn find_local(name: *mut i8, clear: bool) -> i32 {
    let mut dst: *mut i8 = 0 as *mut i8;
    dst = name;
    if clear {
        dst = 0 as *mut i8;
    }
    if dst.is_null() {
        return 0;
    }
    *dst += 1;
    strcmp(name, b"x\0".as_ptr() as *const i8)
}
unsafe fn find(name: *mut i8, clear: bool) -> i32 {
    find_local(name, clear)
}
pub unsafe fn top() -> i32 {
    find(KEY.as_mut_ptr(), false)
}
"#;

#[test]
fn ce_d06_a_model_raw_callee_carries_no_caller() {
    let decisions = super::emit_tests::decisions_of(CE_D06_RAW_CALLEE);
    let find_local = decisions
        .iter()
        .find(|(name, is_param, reason)| name == "name" && *is_param && reason == "kind-raw")
        .is_some();
    assert!(
        find_local,
        "the callee parameter is model-Raw: {decisions:#?}"
    );
    let plans = promotions(CE_D06_RAW_CALLEE);
    assert!(plans.is_empty(), "{plans:#?}");
    let super::RewriteOutcome::Emitted {
        source,
        raw_boundary_artifacts,
        ..
    } = super::rewrite_m1(CE_D06_RAW_CALLEE)
    else {
        panic!("CE-D06 must emit");
    };
    assert!(
        raw_boundary_artifacts
            .contract_candidate_declines
            .lines()
            .any(|line| line.starts_with("find\t")
                && line.contains("contract-candidate-declined:local-callee-boundary")
                && line.contains("via-local-callee:")),
        "{}",
        raw_boundary_artifacts.contract_candidate_declines
    );
    assert!(!source.contains("&[i8]"), "{source}");
    assert!(!source.contains("&mut [i8]"), "{source}");
}
