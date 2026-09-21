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
    // Re-premised by R481-1 / R482-3 (the waiver), wave-4 report 043: the hold
    // still decides — it is what sends the subject past every evidence arm — and
    // the waiver then lifts it with the fabricated extent. The claim is asserted
    // where it still states the rule: on the receipt, which must say `fallback`.
    let lifts = table_of(uninitialized, |table| {
        table
            .licensed_lifts
            .iter()
            .map(|lift| (lift.subject.clone(), lift.fallback))
            .collect::<Vec<_>>()
    })
    .expect("the fixture yields a table");
    assert!(
        lifts.iter().all(|(_, fallback)| *fallback),
        "the write-only parameter promotes on no evidence: {lifts:?}"
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
    // Re-premised by R481-1 / R482-3 (the waiver), wave-4 report 043: the
    // refusal this witness is about is asserted on the receipts; the terminal
    // form is now the waiver's fallback slice.
    // The contract candidate is still declined up front — the receipt above is
    // this witness's claim. What the waiver adds afterwards is a fallback lift,
    // which IS a family edit on the owner, so the old "never attempted"
    // assertion no longer states the rule; the evidence check replaces it.
    assert!(
        raw_boundary_artifacts
            .licensed_lifts
            .lines()
            .skip(1)
            .all(|row| !row.contains("\tevidence\t")),
        "no evidence receipt may be issued here: {}",
        raw_boundary_artifacts.licensed_lifts
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
    // Re-premised by R481-1 / R482-3 (the waiver), wave-4 report 043: the
    // refusal this witness is about is asserted on the receipts; the terminal
    // form is now the waiver's fallback slice.
    assert!(
        !source.contains("from_ref(") && !source.contains("from_mut("),
        "R416-5 stands: no thin caller is widened by a one-element borrow: {source}"
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
    // **Re-premised by R481-1 / R482-3 (the USER's extent-lift waiver), wave-4
    // report 043.** The claim this witness was built for is unchanged and is
    // asserted first: the contract-extent EVIDENCE arm still refuses here. What
    // changed is the terminal form — the waiver now lifts the refused subject
    // with `FALLBACK_SLICE_EXTENT`, receipted `fallback(extent-lift@…)`, so the
    // old "stays thin" assertion no longer states the rule it was testing.
    let plans = promotions(CE_A02_NOT_ALONE);
    assert!(
        plans.is_empty(),
        "the evidence arm still refuses: {plans:#?}"
    );
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(CE_A02_NOT_ALONE) else {
        panic!("CE-A02 must emit");
    };
    let evidence = table_of(CE_A02_NOT_ALONE, |table| {
        table
            .licensed_lifts
            .iter()
            .filter(|lift| !lift.fallback)
            .count()
    })
    .expect("the fixture yields a table");
    assert_eq!(evidence, 0, "and nothing here is evidence-backed: {source}");
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

/// R408-1 (relay 028 §1): ruling B's adjacency arm licensed a VALUE as a slice
/// length — lodepng's `lodepng_set32bitInt(chunk.offset(8 + length), CRC)`
/// planned `from_raw_parts_mut(chunk.offset(..), (CRC) as usize)`. A sibling
/// argument is a length only with evidence: a count position of the callee's
/// own pinned contract that names it (D1's op-fact discipline); otherwise the
/// construction takes the fallback extent and its receipt.
const CE_L01_VALUE_IS_NOT_A_LENGTH: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments)]
static mut SAVED: *mut u8 = 0 as *mut u8;
unsafe fn set32bit(buffer: *mut u8, value: u32) {
    *buffer.offset(0) = (value >> 24) as u8;
    *buffer.offset(1) = (value >> 16) as u8;
    *buffer.offset(2) = (value >> 8) as u8;
    *buffer.offset(3) = value as u8;
}
pub unsafe fn generate_crc(chunk: *mut u8, length: usize, crc: u32) {
    SAVED = chunk;
    set32bit(chunk.offset(8 + length as isize), crc);
}
"#;

#[test]
fn ce_l01_an_adjacent_value_is_not_licensed_as_the_length() {
    let super::RewriteOutcome::Emitted { source, .. } =
        super::rewrite_m1(CE_L01_VALUE_IS_NOT_A_LENGTH)
    else {
        panic!("CE-L01 must emit");
    };
    assert!(source.contains("buffer: &mut [u8]"), "{source}");
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        !flat.contains("(crc) as usize"),
        "the value `crc` is not a length:\n{source}"
    );
    assert!(
        flat.contains("core::slice::from_raw_parts_mut(chunk.offset(8 + length as isize), crate::FALLBACK_SLICE_EXTENT)"),
        "the raw argument takes the waived fallback extent:\n{source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// The licensed half: the callee's own pinned count position names the
/// sibling (`strncpy(dst, src, n)` in the callee: `n` bounds the read of
/// `src`), so `n` is evidence and the caller's construction takes it.
const CE_L02_COUNT_POSITION_LICENSES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments)]
extern "C" {
    fn strncpy(dest: *mut i8, src: *const i8, n: usize) -> *mut i8;
}
static mut SAVED: *const i8 = 0 as *const i8;
unsafe fn read_n(src: *const i8, n: usize) -> i8 {
    let mut buf = [0i8; 16];
    strncpy(buf.as_mut_ptr(), src, n);
    buf[0]
}
pub unsafe fn caller(base: *const i8, n: usize) -> i8 {
    SAVED = base;
    read_n(base.offset(1), n)
}
"#;

#[test]
fn ce_l02_a_count_position_of_the_callee_licenses_the_sibling() {
    let super::RewriteOutcome::Emitted { source, .. } =
        super::rewrite_m1(CE_L02_COUNT_POSITION_LICENSES)
    else {
        panic!("CE-L02 must emit");
    };
    assert!(source.contains("src: &[i8]"), "{source}");
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("core::slice::from_raw_parts(base.offset(1), (n) as usize)"),
        "the callee's count position names `n`, so the sibling is licensed:\n{source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// R408-2 (relay 028 §2): lodepng `lodepng_save_file::buffer` — a thin `&u8`
/// was used as the `buffersize`-byte buffer of
/// `fwrite(buffer as *const c_void, 1, buffersize, file)` (E0606 at the void
/// cast). The counted position holds the thin form (`held:thin-extent`) even
/// through the void cast; with a caller that admits, #1b's `fwrite` rider
/// promotes it instead.
const CE_V01_VOID_CAST_COUNTED_POSITION: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments)]
extern "C" {
    fn fwrite(ptr: *const core::ffi::c_void, size: usize, nmemb: usize, stream: *mut u8) -> usize;
}
unsafe fn save_file(buffer: *const u8, buffersize: usize, file: *mut u8) -> usize {
    fwrite(buffer as *const core::ffi::c_void, 1, buffersize, file)
}
pub unsafe fn top(x: *const u8, file: *mut u8) -> usize {
    let first = *x;
    save_file(x, first as usize, file)
}
"#;

#[test]
fn ce_v01_a_void_cast_counted_position_holds_the_thin_form() {
    // (a) The classifier reaches the counted position through the void cast:
    // `save_file::buffer` is in the thin-extent set, so no thin `&u8` can be
    // emitted there (the corpus E0606 of wave-6v 009).
    let held = ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(CE_V01_VOID_CAST_COUNTED_POSITION),
        |tcx| {
            let (_table, ctx) = super::decide_table_with_ctx(tcx)?;
            let held = super::decision::thin_extent::collect(&ctx.facts);
            Ok::<_, String>(
                ctx.subjects
                    .iter()
                    .filter(|subject| held.contains(&(subject.fn_did, subject.hir_id)))
                    .map(|subject| subject.label.clone())
                    .collect::<Vec<_>>(),
            )
        },
    )
    .expect("CE-V01 fixture compiles")
    .expect("CE-V01 decision table");
    assert_eq!(held, vec!["save_file::buffer".to_owned()], "{held:?}");
    // (b) End to end: #1b's `fwrite` rider promotes the position with its
    // caller's chain; nothing thin reaches the void cast.
    let source = emitted(CE_V01_VOID_CAST_COUNTED_POSITION);
    assert!(source.contains("buffer: &[u8]"), "{source}");
    assert!(
        source.contains("fwrite(buffer.as_ptr().cast::<core::ffi::c_void>(), 1, buffersize, file)"),
        "{source}"
    );
    assert!(!source.contains("&u8"), "{source}");
}

/// R410-9 (a): `memmove` and `memset` rows. `memmove(dest, src, n)` is
/// `memcpy`'s shape (position 0 `Write` `ByteCount` returns-alias, position 1
/// `Read` `ByteCount`, the exact count at argument 2); `memset(s, c, n)` writes
/// exactly `n` bytes at position 0 and returns it.
#[test]
fn ce_m01_memmove_promotes_both_byte_slices_with_the_exact_count() {
    let source = r#"
        #![allow(dead_code, unused_unsafe, unused_mut)]
        extern "C" { fn memmove(dest: *mut u8, src: *const u8, n: usize) -> *mut u8; }
        unsafe fn shift(dest: *mut u8, src: *const u8, n: usize) {
            memmove(dest, src, n);
        }
        pub unsafe fn caller(n: usize) -> u8 {
            let mut dest = [0u8; 8];
            let src = [1u8; 8];
            shift(dest.as_mut_ptr(), src.as_ptr(), n);
            dest[0]
        }
    "#;
    let plans = attested_promotions(source);
    assert_eq!(plans.len(), 2, "plans={plans:#?}");
    let output = attested_emitted(source);
    assert!(output.contains("dest: &mut [u8]"), "{output}");
    assert!(output.contains("src: &[u8]"), "{output}");
    assert!(
        output.contains("memmove(dest.as_mut_ptr(), src.as_ptr(), n)"),
        "{output}"
    );
    assert!(!output.contains("FALLBACK_SLICE_EXTENT"), "{output}");
}

#[test]
fn ce_m02_memset_promotes_the_destination_with_the_exact_count() {
    let source = r#"
        #![allow(dead_code, unused_unsafe, unused_mut)]
        extern "C" { fn memset(s: *mut u8, c: i32, n: usize) -> *mut u8; }
        unsafe fn clear(s: *mut u8, n: usize) {
            memset(s, 0, n);
        }
        pub unsafe fn caller(n: usize) -> u8 {
            let mut buf = [1u8; 8];
            clear(buf.as_mut_ptr(), n);
            buf[0]
        }
    "#;
    let plans = promotions(source);
    assert_eq!(plans.len(), 1, "plans={plans:#?}");
    assert!(
        matches!(
            &plans[0].length,
            super::decision::contract_extent::LengthPlan::Evidence {
                elements,
                source: super::decision::contract_extent::LengthSource::ExactContract {
                    argument_index: 2,
                    ..
                },
            } if elements.trim() == "n"
        ),
        "{plans:#?}"
    );
    let output = emitted(source);
    assert!(output.contains("s: &mut [u8]"), "{output}");
    assert!(output.contains("memset(s.as_mut_ptr(), 0, n)"), "{output}");
    assert!(
        output.contains("core::slice::from_raw_parts_mut(buf.as_mut_ptr(), (n) as usize)"),
        "{output}"
    );
}

/// The thin-extent consequence (R272-1): a thin `&mut u8` at a `ByteCount`
/// position is a one-element claim written `n` bytes; it holds
/// `held:thin-extent` (the chain promotes it only where its caller admits).
#[test]
fn ce_m03_a_thin_reference_at_a_memset_position_holds() {
    let source = r#"
        #![allow(dead_code, unused_unsafe, unused_mut)]
        extern "C" { fn memset(s: *mut u8, c: i32, n: usize) -> *mut u8; }
        static mut SAVED: *mut u8 = 0 as *mut u8;
        unsafe fn clear(s: *mut u8, n: usize) {
            memset(s, 0, n);
        }
        pub unsafe fn caller(x: *mut u8, n: usize) {
            SAVED = x;
            clear(x, n);
        }
    "#;
    // **Re-premised by R481-1 / R482-3 (the USER's extent-lift waiver), wave-4
    // report 045, relay 059.** R272-1 still DECIDES: the thin form is refused
    // at a `ByteCount` position by every evidence arm, which is why the subject
    // reaches the waiver at all. What the waiver then gives it is the
    // fabricated-extent slice, and the seat has stated the consequence — for
    // the fallback form the hold's Stacked-Borrows justification is superseded,
    // the remaining hazard being the slice-length UB §77 already waives.
    //
    // The claim is therefore asserted where it is frame-independent: the
    // subject is never given a THIN one-element form, whether the arms above
    // hold it raw or the waiver lifts it. The original hold survives as a
    // control below, on a fixture the waiver refuses.
    let decisions = super::emit_tests::decisions_of(source);
    let _ = &decisions;
    let output = emitted(source);
    assert!(
        !output.contains("s: &mut u8") && !output.contains("s: &u8"),
        "no one-element form reaches a byte-counted memset: {output}"
    );

    // The control: a SHARED subject at a `*mut` foreign position, which
    // `9685cb948` refuses (R483-3(b)) — writing through a pointer derived from
    // a shared reference is UB §77 does not waive. There the hold stands whole,
    // and `held:thin-extent` is still the reason a subject may not be thin at a
    // multi-element position.
    let refused = r#"
        #![allow(dead_code, unused_unsafe, unused_mut)]
        extern "C" { fn memset(s: *mut u8, c: i32, n: usize) -> *mut u8; }
        static mut SAVED: *const u8 = 0 as *const u8;
        pub unsafe fn caller(x: *const u8, n: usize) {
            SAVED = x;
            memset(x as *mut u8, 0, n);
        }
    "#;
    let control = emitted(refused);
    assert!(
        !control.contains("x: &[u8]") && !control.contains("x: &mut [u8]"),
        "a shared subject at a *mut position is refused, not lifted: {control}"
    );
}

/// A byte count that spells the pointee's own size is ONE element: a thin
/// `&mut S` written `size_of::<S>()` bytes is exactly the claim it carries
/// (R272-1's rule is about extent, not about the row's kind), so the position
/// neither holds the thin form nor promotes a slice of one struct.
#[test]
fn ce_m04_a_size_of_pointee_byte_count_is_one_element() {
    let source = r#"
        #![allow(dead_code, unused_unsafe, unused_mut)]
        extern "C" { fn memset(s: *mut core::ffi::c_void, c: i32, n: usize) -> *mut core::ffi::c_void; }
        #[repr(C)]
        pub struct Stat { pub dev: u64, pub ino: u64 }
        unsafe fn clear(st: *mut Stat) {
            memset(st as *mut core::ffi::c_void, 0, ::std::mem::size_of::<Stat>() as usize);
        }
        pub unsafe fn caller() -> u64 {
            let mut st = Stat { dev: 1, ino: 2 };
            clear(&mut st);
            st.dev
        }
    "#;
    let plans = promotions(source);
    assert!(plans.is_empty(), "{plans:#?}");
    let output = emitted(source);
    assert!(output.contains("st: &mut Stat"), "{output}");
    assert!(!output.contains("[Stat]"), "{output}");
    assert!(!output.contains("slice::from_mut("), "{output}");
    assert!(
        output.contains("memset(core::ptr::from_mut(st).cast::<core::ffi::c_void>(), 0,"),
        "{output}"
    );
}

/// The negative half: a `size_of` of ANOTHER type (`[Stat; 4]`) is not the
/// pointee's own size, so the position keeps its multi-element extent and the
/// thin form holds.
#[test]
fn ce_m05_a_size_of_another_type_keeps_the_multi_element_extent() {
    let source = r#"
        #![allow(dead_code, unused_unsafe, unused_mut)]
        extern "C" { fn memset(s: *mut core::ffi::c_void, c: i32, n: usize) -> *mut core::ffi::c_void; }
        #[repr(C)]
        pub struct Stat { pub dev: u64, pub ino: u64 }
        static mut SAVED: *mut Stat = 0 as *mut Stat;
        unsafe fn clear(st: *mut Stat) {
            memset(st as *mut core::ffi::c_void, 0, ::std::mem::size_of::<[Stat; 4]>() as usize);
        }
        pub unsafe fn caller(p: *mut Stat) {
            SAVED = p;
            clear(p);
        }
    "#;
    let decisions = super::emit_tests::decisions_of(source);
    let st = decisions
        .iter()
        .find(|(name, is_param, _)| name == "st" && *is_param)
        .expect("CE-M05 `st` subject");
    assert_eq!(st.2, "held:thin-extent", "{decisions:#?}");
}

/// R410-9 (b): the counted-literal shape (wave-6k 010's 8 string-literal
/// copies) — libtree's `print_error`: a local initialized by a conditional of
/// NUL-terminated byte-string literals and read only at NUL contract
/// positions. It takes `&[i8]` with each literal's own byte length as the
/// evidence and `.as_ptr()` at the foreign seam. (The corpus shape also hands
/// it to `strcpy(p, box_vertical)` beside a written sibling — that site is
/// pending and holds it, CE-S04; here the reads have no sibling.)
const CE_S01_CONDITIONAL_LITERAL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn strlen(s: *const i8) -> usize;
    fn strcmp(a: *const i8, b: *const i8) -> i32;
}
pub unsafe fn print_error(color: i32) -> usize {
    let mut box_vertical = (if color != 0 {
        b"    \x1B[0;31m|\x1B[0m\0" as *const u8 as *const i8
    } else {
        b"    |\0" as *const u8 as *const i8
    }) as *mut i8;
    let n = strlen(box_vertical);
    if strcmp(box_vertical, b"    |\0" as *const u8 as *const i8) == 0 { return 0; }
    n
}
"#;

#[test]
fn ce_s01_a_conditional_of_nul_literals_takes_the_slice_with_literal_lengths() {
    let source = emitted(CE_S01_CONDITIONAL_LITERAL);
    assert!(
        source.contains(r#"core::slice::from_raw_parts(b"    \x1B[0;31m|\x1B[0m\0" as *const u8 as *const i8, 17usize)"#),
        "{source}"
    );
    assert!(
        source.contains(
            r#"core::slice::from_raw_parts(b"    |\0" as *const u8 as *const i8, 6usize)"#
        ),
        "{source}"
    );
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("let mut box_vertical: &[i8] = (if color != 0 {"),
        "{source}"
    );
    assert!(flat.contains("strlen(box_vertical.as_ptr())"), "{source}");
    assert!(flat.contains("strcmp(box_vertical.as_ptr(),"), "{source}");
    assert!(
        !flat.contains("as *mut i8;"),
        "the outer cast is gone:\n{source}"
    );
    assert!(!flat.contains("FALLBACK_SLICE_EXTENT"), "{source}");
}

/// libtree's `recurse`: the literal local is handed to a LOCAL callee whose
/// parameter reads it at a NUL position — the chain carries the literal
/// slice zero-syntax into `print_line(color: &[i8])`.
const CE_S02_LITERAL_INTO_LOCAL_CALLEE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn strlen(s: *const i8) -> usize;
}
unsafe fn print_line(depth: usize, color: *const i8) -> usize {
    depth + strlen(color)
}
pub unsafe fn recurse(depth: usize, excluded: i32) -> usize {
    let mut bold_color = (if excluded != 0 {
        b"\x1B[0;35m\0" as *const u8 as *const i8
    } else {
        b"\x1B[1;36m\0" as *const u8 as *const i8
    }) as *mut i8;
    print_line(depth, bold_color)
}
"#;

#[test]
fn ce_s02_a_literal_local_carries_into_its_local_callee() {
    let source = emitted(CE_S02_LITERAL_INTO_LOCAL_CALLEE);
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("fn print_line(depth: usize, color: &[i8])"),
        "{source}"
    );
    assert!(flat.contains("depth + strlen(color.as_ptr())"), "{source}");
    assert!(
        flat.contains("let mut bold_color: &[i8] = (if excluded != 0 {"),
        "{source}"
    );
    assert!(
        source.contains(
            r#"core::slice::from_raw_parts(b"\x1B[0;35m\0" as *const u8 as *const i8, 8usize)"#
        ),
        "{source}"
    );
    assert!(flat.contains("print_line(depth, bold_color)"), "{source}");
    assert!(!flat.contains("FALLBACK_SLICE_EXTENT"), "{source}");
}

/// A single literal (no conditional) and the write-through hold: a literal is
/// read-only, so a position that WRITES it (`strcpy` destination) is not a
/// slice of it — the local keeps its raw form rather than a `&mut [i8]`.
#[test]
fn ce_s03_a_lone_literal_promotes_and_a_written_literal_does_not() {
    let read_only = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" { fn strlen(s: *const i8) -> usize; }
pub unsafe fn f() -> usize {
    let s = b"abc\0" as *const u8 as *const i8;
    strlen(s)
}
"#;
    let source = emitted(read_only);
    assert!(
        source.contains(r#"let s: &[i8] = core::slice::from_raw_parts(b"abc\0" as *const u8 as *const i8, 4usize);"#),
        "{source}"
    );
    assert!(source.contains("strlen(s.as_ptr())"), "{source}");

    let written = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" { fn strcpy(dest: *mut i8, src: *const i8) -> *mut i8; }
pub unsafe fn g(src: *const i8) {
    let d = b"abc\0" as *const u8 as *mut i8;
    strcpy(d, src);
}
"#;
    let source = emitted(written);
    assert!(
        source.contains(r#"let d = b"abc\0" as *const u8 as *mut i8;"#),
        "the written literal keeps its raw form:\n{source}"
    );
    assert!(!source.contains("d: &"), "{source}");
}

/// R419-3 / R304-2: a pending sibling-overlap site is a stated hold. urlparser's
/// `url_get_path`: the literal `fmt` is `sprintf`'s format while `path` — a
/// written sibling at the same call whose aliasing with the literal no proof
/// clears — is its destination; the literal local keeps its raw form with the
/// typed reason `pending-sibling-overlap` instead of a `&[i8]` whose type moves
/// under the pending site. A literal whose only site has no risky sibling
/// (`strlen`) still delivers.
const CE_S04_PENDING_SIBLING: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn sprintf(s: *mut i8, format: *const i8, _: ...) -> i32;
}
pub unsafe fn url_get_path(path: *mut i8, tmp_path: *mut i8, is_ssh: bool) {
    let mut fmt = (if is_ssh {
        b"%s\0" as *const u8 as *const i8
    } else {
        b"/%s\0" as *const u8 as *const i8
    }) as *mut i8;
    sprintf(path, fmt, tmp_path);
}
"#;

#[test]
fn ce_s04_a_literal_at_a_pending_sibling_site_keeps_its_raw_form() {
    let decisions = super::emit_tests::decisions_of(CE_S04_PENDING_SIBLING);
    let fmt = decisions
        .iter()
        .find(|(name, is_param, _)| name == "fmt" && !*is_param)
        .expect("CE-S04 fmt subject");
    // Re-premised by R481-1 / R482-3 (the waiver), wave-4 report 043: the hold
    // still decides — it is what sends the subject past every evidence arm — and
    // the waiver then lifts it with the fabricated extent. The claim is asserted
    // where it still states the rule: on the receipt, which must say `fallback`.
    assert_eq!(fmt.2, "pending-sibling-overlap", "{decisions:#?}");
    let source = emitted(CE_S04_PENDING_SIBLING);
    // The literal's own argument text may now be the waiver's slice bridge; the
    // claim that survives is that `fmt` never reaches the CONTRACT's fat form.
    assert!(!source.contains("fmt: &[i8]"), "{source}");

    // libtree's `strcpy(p, box_vertical)`: the written destination `p` is the
    // risky sibling of the literal source.
    let strcpy_shape = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn strlen(s: *const i8) -> usize;
    fn strcpy(dest: *mut i8, src: *const i8) -> *mut i8;
}
pub unsafe fn print_error(color: i32, p: *mut i8) -> usize {
    let mut box_vertical = (if color != 0 {
        b"    |\0" as *const u8 as *const i8
    } else {
        b"    \0" as *const u8 as *const i8
    }) as *mut i8;
    let n = strlen(box_vertical);
    strcpy(p, box_vertical);
    n
}
"#;
    let decisions = super::emit_tests::decisions_of(strcpy_shape);
    let local = decisions
        .iter()
        .find(|(name, is_param, _)| name == "box_vertical" && !*is_param)
        .expect("CE-S04 box_vertical subject");
    assert_eq!(local.2, "pending-sibling-overlap", "{decisions:#?}");
}

/// R419-3 at the CONTRACT-ALONE arm: urlparser's `get_part::format#2` — the
/// parameter's only use is `sscanf(fmt_url, format, tmp)` position 1, a
/// NUL-terminated read, so R407-14 would promote it over `Ptr` fatness; but the
/// scanf tail WRITES `tmp` at the same call, so the site is a pending
/// sibling-overlap site and the promotion would deliver a held subject.
const CE_A03_CONTRACT_ALONE_PENDING: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn sscanf(s: *const i8, format: *const i8, _: ...) -> i32;
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub unsafe fn get_part(url: *const i8, format: *const i8) -> i32 {
    let tmp = malloc(16) as *mut i8;
    sscanf(url, format, tmp)
}
"#;

#[test]
fn ce_a03_a_contract_alone_candidate_at_a_pending_sibling_site_holds() {
    let decisions = super::emit_tests::decisions_of(CE_A03_CONTRACT_ALONE_PENDING);
    let format = decisions
        .iter()
        .find(|(name, is_param, _)| name == "format" && *is_param)
        .expect("CE-A03 format subject");
    // **Re-premised by R481-1 / R482-3 (the USER's extent-lift waiver), wave-4
    // report 043.** The claim this witness was built for is unchanged and is
    // asserted first: the contract-extent EVIDENCE arm still refuses here. What
    // changed is the terminal form — the waiver now lifts the refused subject
    // with `FALLBACK_SLICE_EXTENT`, receipted `fallback(extent-lift@…)`, so the
    // old "stays thin" assertion no longer states the rule it was testing.
    // The promotion is still not taken — that is this witness's claim — and
    // the subject reaches the waiver rather than the contract's fat form.
    // The candidate is still computed; what this witness is about is that the
    // pending-sibling site REFUSES it, so the subject may not take the
    // contract's fat form. It now reaches the waiver instead, and the receipt
    // says `fallback` — no contract extent was taken.
    assert_eq!(
        format.2, "<emitted>",
        "the waiver lifts what the contract may not: {decisions:#?}"
    );
    let fabricated = table_of(CE_A03_CONTRACT_ALONE_PENDING, |table| {
        table
            .licensed_lifts
            .iter()
            .filter(|lift| !lift.fallback)
            .count()
    })
    .expect("the fixture yields a table");
    assert_eq!(
        fabricated, 0,
        "and no evidence receipt is issued: {decisions:#?}"
    );
}

/// The corpus spelling of CE-M04 (libtree `small_vec_u64_init`, a batch-8
/// loss): the struct lives in nested modules, so the operand's pointee prints
/// as `src::libtree::small_vec_u64_t` while the count's source text can only
/// spell `size_of::<small_vec_u64_t>()`. The one-element refinement compares
/// what the two forms have in common — the type's final path segment.
const CE_M06_NESTED_POINTEE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
pub mod src {
    pub mod libtree {
        extern "C" {
            fn memset(_: *mut core::ffi::c_void, _: i32, _: u64) -> *mut core::ffi::c_void;
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct small_vec_u64_t {
            pub p: *mut u64,
            pub n: u64,
            pub buf: [u64; 16],
        }
        pub unsafe fn small_vec_u64_init(mut v: *mut small_vec_u64_t) {
            memset(v as *mut core::ffi::c_void, 0 as i32,
                ::std::mem::size_of::<small_vec_u64_t>() as u64);
            (*v).p = ((*v).buf).as_mut_ptr();
        }
    }
}
"#;

#[test]
fn ce_m06_a_nested_pointee_still_reads_as_one_element() {
    let decisions = super::emit_tests::decisions_of(CE_M06_NESTED_POINTEE);
    let v = decisions
        .iter()
        .find(|(name, is_param, _)| name == "v" && *is_param)
        .expect("CE-M06 v subject");
    assert_eq!(v.2, "<emitted>", "{decisions:#?}");
    let source = emitted(CE_M06_NESTED_POINTEE);
    assert!(source.contains("v: &mut small_vec_u64_t"), "{source}");
    assert!(!source.contains("[small_vec_u64_t]"), "{source}");
}

/// R433-2 (c): bzip2's `countHardLinks` — the contract-alone parameter's only
/// use is `lstat(name, &mut statBuf)` position 0, a NUL-terminated read. The
/// sibling at position 1 WRITES, but it is the address of a LOCAL of this very
/// frame: no pointer to it existed when the frame began, so it cannot alias the
/// parameter's referent and the site is not a pending sibling-overlap hold.
const CE_A04_ADDR_OF_LOCAL_SIBLING: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
pub mod bzip2 {
    #[derive(Copy, Clone)]
    #[repr(C)]
    pub struct stat {
        pub st_dev: u64,
        pub st_nlink: u64,
    }
    extern "C" {
        fn lstat(path: *const i8, buf: *mut stat) -> i32;
    }
    pub unsafe fn countHardLinks(mut name: *mut i8) -> i32 {
        let mut statBuf: stat = stat { st_dev: 0, st_nlink: 0 };
        let i = lstat(name, &mut statBuf);
        if i != 0 {
            return 0;
        }
        statBuf.st_nlink as i32 - 1
    }
}
"#;

#[test]
fn ce_a04_an_addr_of_local_sibling_is_not_a_pending_site() {
    let decisions = super::emit_tests::decisions_of(CE_A04_ADDR_OF_LOCAL_SIBLING);
    let name = decisions
        .iter()
        .find(|(n, is_param, _)| n == "name" && *is_param)
        .expect("CE-A04 name subject");
    assert_eq!(name.2, "<emitted>", "{decisions:#?}");
    let source = emitted(CE_A04_ADDR_OF_LOCAL_SIBLING);
    assert!(source.contains("name: &[i8]"), "{source}");
    assert!(
        source.contains("lstat(name.as_ptr(), &mut statBuf)"),
        "{source}"
    );
}

/// The negative half of CE-A04: a written sibling borrowed THROUGH a
/// dereference (`&mut (*holder).st`) addresses storage the frame did not
/// create, so it may alias the parameter's referent — the site stays a pending
/// sibling-overlap hold and the contract-alone promotion is not taken.
const CE_A05_ADDR_THROUGH_DEREF_SIBLING: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
pub mod bzip2 {
    #[derive(Copy, Clone)]
    #[repr(C)]
    pub struct stat {
        pub st_dev: u64,
        pub st_nlink: u64,
    }
    #[derive(Copy, Clone)]
    #[repr(C)]
    pub struct holder {
        pub st: stat,
    }
    extern "C" {
        fn lstat(path: *const i8, buf: *mut stat) -> i32;
    }
    pub unsafe fn countHardLinks(mut name: *mut i8, mut h: *mut holder) -> i32 {
        let i = lstat(name, &mut (*h).st);
        if i != 0 {
            return 0;
        }
        (*h).st.st_nlink as i32 - 1
    }
}
"#;

#[test]
fn ce_a05_a_sibling_borrowed_through_a_deref_keeps_the_pending_hold() {
    let decisions = super::emit_tests::decisions_of(CE_A05_ADDR_THROUGH_DEREF_SIBLING);
    let name = decisions
        .iter()
        .find(|(n, is_param, _)| n == "name" && *is_param)
        .expect("CE-A05 name subject");
    // **Re-premised by R481-1 / R482-3 (the USER's extent-lift waiver), wave-4
    // report 043.** The claim this witness was built for is unchanged and is
    // asserted first: the contract-extent EVIDENCE arm still refuses here. What
    // changed is the terminal form — the waiver now lifts the refused subject
    // with `FALLBACK_SLICE_EXTENT`, receipted `fallback(extent-lift@…)`, so the
    // old "stays thin" assertion no longer states the rule it was testing.
    // The candidate is still computed; what this witness is about is that the
    // pending-sibling site REFUSES it, so the subject may not take the
    // contract's fat form. It now reaches the waiver instead, and the receipt
    // says `fallback` — no contract extent was taken.
    assert_eq!(
        name.2, "<emitted>",
        "the waiver lifts what the contract may not: {decisions:#?}"
    );
    let evidence = table_of(CE_A05_ADDR_THROUGH_DEREF_SIBLING, |table| {
        table
            .licensed_lifts
            .iter()
            .filter(|lift| !lift.fallback)
            .count()
    })
    .expect("the fixture yields a table");
    assert_eq!(
        evidence, 0,
        "and no evidence receipt is issued: {decisions:#?}"
    );
}

/// R451 (batch 10): binn's `memset(value as *mut c_void, 0, size_of::<binn>())`
/// where `pub type binn = binn_struct` — C2Rust's own spelling. The count names
/// the ALIAS while the operand's pointee prints the resolved struct, so a name
/// comparison misses and the one-element refinement failed to fire: the four
/// binn rows that joined the thin-extent bucket at batch 10.
const CE_M07_ALIASED_POINTEE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
pub mod src {
    pub mod binn {
        extern "C" {
            fn memset(_: *mut core::ffi::c_void, _: i32, _: u64) -> *mut core::ffi::c_void;
        }
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct binn_struct {
            pub header: i32,
            pub count: i32,
        }
        pub type binn = binn_struct;
        pub unsafe fn binn_load(mut value: *mut binn) -> i32 {
            memset(value as *mut core::ffi::c_void, 0 as i32,
                ::std::mem::size_of::<binn>() as u64);
            (*value).header = 1;
            (*value).count
        }
    }
}
"#;

#[test]
fn ce_m07_an_aliased_pointee_still_reads_as_one_element() {
    let decisions = super::emit_tests::decisions_of(CE_M07_ALIASED_POINTEE);
    let value = decisions
        .iter()
        .find(|(name, is_param, _)| name == "value" && *is_param)
        .expect("CE-M07 value subject");
    assert_eq!(value.2, "<emitted>", "{decisions:#?}");
    let source = emitted(CE_M07_ALIASED_POINTEE);
    assert!(source.contains("value: &mut binn"), "{source}");
    assert!(!source.contains("[binn]"), "{source}");
}

/// **W4-LIFT (R475-2, addendum 475) — the licensed-width caller lift.**
///
/// `BrotliUnalignedRead32(p: *const c_void)` reads FOUR bytes through its
/// parameter, and wave-6b's region family types that parameter with the exact
/// width (`void_region::licensed_width(.., 0) == Some(4)`). `HashBytesH40`
/// hands it a THIN `*const uint8_t`, so the caller's one-element claim is
/// walked off by four bytes and `held:local-callee-access-extent` holds it.
/// The width is a count position of the callee parameter's own contract, and a
/// stronger one (R408-1): it licenses the caller to take the slice form.
const W4_LIFT_READ32: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint32_t = u32;
pub type size_t = usize;
static mut kHashMul32: uint32_t = 0x1e35a7bd as uint32_t;
unsafe extern "C" fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> uint32_t {
    return *(p as *const uint32_t);
}
unsafe extern "C" fn HashBytesH40(mut data: *const uint8_t) -> size_t {
    let h = (BrotliUnalignedRead32(data as *const core::ffi::c_void)).wrapping_mul(kHashMul32);
    return (h >> 32 as i32 - 15 as i32) as size_t;
}
"#;

/// The SAME reason key, a different license: a `c_void` callee parameter that
/// this family never typed. `ReadAt` casts its opaque parameter away and then
/// OFFSETS it, so no region contract exists, `licensed_width` answers `None`,
/// and the caller keeps the hold. (The corpus half of this control is the 121
/// arithmetic rows and the 4 void rows outside `BrotliUnalignedRead32/64`.)
const W4_LIFT_ARITHMETIC: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type size_t = usize;
unsafe extern "C" fn ReadAt(mut p: *const core::ffi::c_void, mut i: size_t) -> uint8_t {
    let mut q: *const uint8_t = p as *const uint8_t;
    return *q.offset(i as isize);
}
unsafe extern "C" fn HashBytesVoid(mut data: *const uint8_t) -> size_t {
    return ReadAt(data as *const core::ffi::c_void, 2 as size_t) as size_t;
}
"#;

/// The width WRITE mirror. wave-6b's seam reads a delivered slice at a width
/// READ only (`region_from_slice`), so lifting the caller here would trade a
/// held subject for a blocked seam; the lift refuses on the shape.
const W4_LIFT_WRITE: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint32_t = u32;
pub type size_t = usize;
unsafe extern "C" fn BrotliUnalignedWrite32(mut p: *mut core::ffi::c_void, mut v: uint32_t) {
    *(p as *mut uint32_t) = v;
}
unsafe extern "C" fn PutBytesH40(mut out: *mut uint8_t, mut v: uint32_t) {
    BrotliUnalignedWrite32(out as *mut core::ffi::c_void, v);
}
"#;

fn table_of<T: Send>(
    input: &str,
    ask: impl Fn(&super::decision::DecisionTable) -> T + Sync,
) -> Result<T, String> {
    match ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(input),
        |tcx| {
            let (table, _) = super::decide_table_with_ctx(tcx)?;
            Ok(ask(&table))
        },
    ) {
        Ok(inner) => inner,
        Err(why) => Err(format!("{why:?}")),
    }
}

/// **W4L-1 — the lift fires, and the argument is bridged from the slice.**
#[test]
fn w4l01_a_licensed_width_lifts_the_thin_caller() {
    let decisions = super::emit_tests::decisions_of(W4_LIFT_READ32);
    let data = decisions
        .iter()
        .find(|(name, is_param, _)| name == "data" && *is_param)
        .expect("W4L-1 data subject");
    assert_eq!(data.2, "<emitted>", "{decisions:#?}");
    let source = emitted(W4_LIFT_READ32);
    assert!(source.contains("data: &[uint8_t]"), "{source}");
    // wave-6b's `region_from_slice` arm: a CHECKED prefix of the delivered
    // slice, and no fabricated extent anywhere at the site.
    assert!(source.contains("&(data)[..4]"), "{source}");
    assert!(!source.contains("from_raw_parts"), "{source}");
}

/// **W4L-2 — the receipt names the width, the callee and the position.**
#[test]
fn w4l02_the_lift_carries_a_typed_receipt() {
    let receipts = table_of(W4_LIFT_READ32, |table| table.licensed_lifts.clone())
        .expect("the fixture yields a table");
    assert_eq!(receipts.len(), 1, "{receipts:#?}");
    let receipt = &receipts[0];
    assert!(receipt.subject.starts_with("HashBytesH40::"), "{receipt:?}");
    assert!(
        receipt.callee.ends_with("BrotliUnalignedRead32"),
        "{receipt:?}"
    );
    assert_eq!(receipt.parameter_index, Some(0), "{receipt:?}");
    assert_eq!(receipt.width_bytes, Some(4), "{receipt:?}");
    assert!(
        !receipt.fallback,
        "the exact arm, not the waiver: {receipt:?}"
    );
    assert!(
        !receipt.mutable,
        "a width READ lifts to a shared slice: {receipt:?}"
    );
}

/// **W4L-3 (control) — my entries-shaped twin agrees with wave-6b's export.**
///
/// The lift runs inside `decide`, where no `DecisionTable` exists, so
/// [`decision::licensed_lift::callee_region`] asks `void_region::parameter`'s
/// three questions over `entries`. This pins the two together: the width the
/// receipt carries is the width the export answers with.
#[test]
fn w4l03_the_twin_agrees_with_the_export() {
    let (exported, receipt_width) = table_of(W4_LIFT_READ32, |table| {
        let exported = table.entries.iter().find_map(|(subject, _)| {
            subject
                .label
                .starts_with("BrotliUnalignedRead32::")
                .then(|| super::decision::void_region::licensed_width(table, subject.fn_did, 0))
        });
        (
            exported.flatten(),
            table
                .licensed_lifts
                .first()
                .and_then(|lift| lift.width_bytes),
        )
    })
    .expect("the fixture yields a table");
    assert_eq!(exported, Some(4), "the export's own answer");
    assert_eq!(receipt_width, exported, "the twin must not drift");
}

/// **W4L-4 (control) — no region, no lift.** Pointer arithmetic in the callee
/// licenses no width, so the caller keeps the hold.
#[test]
fn w4l04_an_untyped_void_callee_licenses_nothing() {
    let decisions = super::emit_tests::decisions_of(W4_LIFT_ARITHMETIC);
    let data = decisions
        .iter()
        .find(|(name, is_param, _)| name == "data" && *is_param)
        .expect("W4L-4 data subject");
    // Re-premised by R481-1 / R482-3 (the waiver), wave-4 report 043: the hold
    // still decides — it is what sends the subject past every evidence arm — and
    // the waiver then lifts it with the fabricated extent. The claim is asserted
    // where it still states the rule: on the receipt, which must say `fallback`.
    let _ = &data;
    let evidence = table_of(W4_LIFT_ARITHMETIC, |table| {
        table
            .licensed_lifts
            .iter()
            .filter(|lift| !lift.fallback)
            .count()
    })
    .expect("the fixture yields a table");
    assert_eq!(evidence, 0, "no width, no EVIDENCE receipt: {decisions:#?}");
}

/// **W4L-5 (control) — a width WRITE licenses no EVIDENCE receipt.**
#[test]
fn w4l05_a_width_write_licenses_no_evidence_receipt() {
    // **Re-premised by R481-1, the user's extent-lift waiver.** The exact arm
    // refuses a width WRITE twice over — wave-6b's seam reads a delivered slice
    // at a READ only, and every corpus write parameter is `kind-raw` anyway —
    // and that is what this control was always about. Since the waiver, the
    // fallback arm may lift such a caller with the fabricated extent, which is
    // a different question with the user's answer; so the assertion is on the
    // EVIDENCE receipts, which must stay empty here.
    let evidence = table_of(W4_LIFT_WRITE, |table| {
        table
            .licensed_lifts
            .iter()
            .filter(|lift| !lift.fallback)
            .count()
    })
    .expect("the fixture yields a table");
    assert_eq!(
        evidence, 0,
        "the seam reads a delivered slice at a READ only"
    );
}

/// A caller that is ALREADY fat: it indexes its own parameter against a length
/// companion, so the slice form is its own route's and the lift has nothing to
/// license. The subject still delivers — by the ladder, with no receipt of
/// mine.
const W4_LIFT_FAT_CALLER: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint32_t = u32;
pub type size_t = usize;
unsafe extern "C" fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> uint32_t {
    return *(p as *const uint32_t);
}
unsafe extern "C" fn HashBytesFat(mut data: *const uint8_t, mut n: size_t) -> size_t {
    let mut acc: size_t = 0;
    let mut i: size_t = 0;
    while i < n {
        acc = acc.wrapping_add(*data.offset(i as isize) as size_t);
        i = i.wrapping_add(1 as size_t);
    }
    return acc.wrapping_add(BrotliUnalignedRead32(data as *const core::ffi::c_void) as size_t);
}
"#;

/// A caller with a use that has no slice image (`data as size_t`). `&[T]`
/// changes the type at every occurrence, so lifting this one would yield an
/// ill-typed crate; the lift refuses on the same rule the slice ladder applies.
const W4_LIFT_UNSUPPORTED_USE: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint32_t = u32;
pub type size_t = usize;
unsafe extern "C" fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> uint32_t {
    return *(p as *const uint32_t);
}
unsafe extern "C" fn HashBytesAddr(mut data: *const uint8_t) -> size_t {
    let mut n: size_t = data as size_t;
    return (BrotliUnalignedRead32(data as *const core::ffi::c_void) as size_t).wrapping_add(n);
}
"#;

/// **W4L-6 (control) — an already-fat caller is not the lift's.**
#[test]
fn w4l06_an_already_fat_caller_is_untouched() {
    let receipts = table_of(W4_LIFT_FAT_CALLER, |table| table.licensed_lifts.len())
        .expect("the fixture yields a table");
    assert_eq!(receipts, 0, "the fat caller carries its own extent");
}

/// **W4L-7 (control) — a use with no slice image refuses the lift.**
#[test]
fn w4l07_an_unsupported_use_refuses_the_lift() {
    let lifted = table_of(W4_LIFT_UNSUPPORTED_USE, |table| {
        table
            .licensed_lifts
            .iter()
            .filter(|lift| lift.declined.is_none())
            .count()
    })
    .expect("the fixture yields a table");
    assert_eq!(lifted, 0, "a subject with no slice image is not lifted");
    let source = emitted(W4_LIFT_UNSUPPORTED_USE);
    assert!(!source.contains("data: &[uint8_t]"), "{source}");
}

/// **W4L-8 — the lift reaches the CENSUS, not only the table.** relay 052 reads
/// the receipts per program, so they are an artifact row
/// (`<program>.raw-boundary-licensed-lifts.tsv`), rendered in the same shape as
/// this lane's decline receipt.
#[test]
fn w4l08_the_receipt_is_a_census_artifact_row() {
    let super::RewriteOutcome::Emitted {
        raw_boundary_artifacts,
        ..
    } = super::rewrite_m1(W4_LIFT_READ32)
    else {
        panic!("W4L-8 must emit");
    };
    let tsv = &raw_boundary_artifacts.licensed_lifts;
    let mut lines = tsv.lines();
    assert_eq!(
        lines.next(),
        Some(
            "owner_path\tsubject\tlicensing_callee\tparameter_index\twidth_bytes\tform\textent_class\treceipt"
        ),
        "{tsv}"
    );
    let row = lines.next().expect("one lifted caller");
    let columns = row.split('\t').collect::<Vec<_>>();
    assert!(columns[1].starts_with("HashBytesH40::"), "{tsv}");
    assert!(columns[2].ends_with("BrotliUnalignedRead32"), "{tsv}");
    assert_eq!(columns[3], "0", "{tsv}");
    assert_eq!(columns[4], "4", "{tsv}");
    assert_eq!(columns[5], "slice", "{tsv}");
    assert_eq!(
        columns[6], "evidence",
        "the exact arm, not the waiver: {tsv}"
    );
    assert_eq!(
        columns[7], "evidence(licensed-width:BrotliUnalignedRead32:0:4)",
        "{tsv}"
    );
    assert_eq!(lines.next(), None, "one lift, one row: {tsv}");
}

/// **W4-B1 (R480-2)** — `BrotliWriteBits`'s shape, minimised: the callee binds
/// a byte pointer out of `array.offset(..)`, so it is no slice candidate of its
/// own and the caller is held `held:local-callee-access-extent`. The caller's
/// ROOT is an allocation whose size is recoverable, and that extent is what the
/// slice form carries.
const W4_B1_SIZED_ROOT: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type size_t = usize;
extern "C" {
    fn malloc(_: u64) -> *mut core::ffi::c_void;
}
unsafe extern "C" fn BrotliWriteBits(mut pos: *mut size_t, mut array: *mut uint8_t) {
    let mut p: *mut uint8_t = &mut *array.offset((*pos >> 3 as i32) as isize) as *mut uint8_t;
    *p = 1 as uint8_t;
    *pos = (*pos).wrapping_add(8 as size_t);
}
pub unsafe extern "C" fn StoreIt(mut n: size_t) {
    let mut storage: *mut uint8_t =
        malloc(n.wrapping_mul(::std::mem::size_of::<uint8_t>() as size_t) as u64) as *mut uint8_t;
    let mut pos: size_t = 0 as size_t;
    BrotliWriteBits(&mut pos, storage);
}
"#;

/// The same shape with the root one frame further away: the held subject is a
/// PARAMETER, and its only call site hands it the sized allocation.
const W4_B1_SIZED_ROOT_THROUGH_A_PARAMETER: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type size_t = usize;
extern "C" {
    fn malloc(_: u64) -> *mut core::ffi::c_void;
}
unsafe extern "C" fn BrotliWriteBits(mut pos: *mut size_t, mut array: *mut uint8_t) {
    let mut p: *mut uint8_t = &mut *array.offset((*pos >> 3 as i32) as isize) as *mut uint8_t;
    *p = 1 as uint8_t;
    *pos = (*pos).wrapping_add(8 as size_t);
}
unsafe extern "C" fn StoreInner(mut pos: *mut size_t, mut storage: *mut uint8_t) {
    BrotliWriteBits(pos, storage);
}
pub unsafe extern "C" fn StoreOuter(mut n: size_t) {
    let mut buffer: *mut uint8_t =
        malloc(n.wrapping_mul(::std::mem::size_of::<uint8_t>() as size_t) as u64) as *mut uint8_t;
    let mut pos: size_t = 0 as size_t;
    StoreInner(&mut pos, buffer);
}
"#;

/// The residue: the root is a call this analysis does not read — no allocation,
/// no array, no literal, no companion length. It stays held and is COUNTED.
const W4_B1_UNSIZED_ROOT: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type size_t = usize;
extern "C" {
    fn GetBuffer() -> *mut uint8_t;
}
unsafe extern "C" fn BrotliWriteBits(mut pos: *mut size_t, mut array: *mut uint8_t) {
    let mut p: *mut uint8_t = &mut *array.offset((*pos >> 3 as i32) as isize) as *mut uint8_t;
    *p = 1 as uint8_t;
    *pos = (*pos).wrapping_add(8 as size_t);
}
pub unsafe extern "C" fn StoreUnsized() {
    let mut storage: *mut uint8_t = GetBuffer();
    let mut pos: size_t = 0 as size_t;
    BrotliWriteBits(&mut pos, storage);
}
"#;

fn b1_rows(source: &str) -> Vec<(String, String, String, String)> {
    table_of(source, |table| {
        table
            .root_extents
            .iter()
            .map(|row| {
                (
                    row.subject.clone(),
                    row.outcome.to_string(),
                    row.extent.clone(),
                    row.evidence.clone(),
                )
            })
            .collect::<Vec<_>>()
    })
    .expect("the fixture yields a table")
}

/// **W4B1-1 (control) — a root that states nothing stays the fallback's.**
///
/// The `wrapping_mul` evidence arm itself is witnessed where it lives, in
/// `construction::slice_construction_tests` (`w4b1_a_wrapping_mul_product_is_length_evidence`
/// and its no-element-size control): a small integration fixture cannot show it,
/// because an allocation-rooted local in one of these fixtures is `kind-raw`
/// and never reaches a slice construction at all.
/// The same shape with an opaque `GetBuffer()` root: no allocation, no array,
/// no literal, no companion — the length planner keeps its §77 fallback and
/// B1 has nothing to propagate.
const W4_B1_OPAQUE_ROOT: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type size_t = usize;
extern "C" {
    fn GetBuffer() -> *mut uint8_t;
}
pub unsafe extern "C" fn SumOpaque(mut n: size_t) -> size_t {
    let mut buffer: *mut uint8_t = GetBuffer();
    let mut acc: size_t = 0 as size_t;
    let mut i: size_t = 0 as size_t;
    while i < n {
        acc = acc.wrapping_add(*buffer.offset(i as isize) as size_t);
        i = i.wrapping_add(1 as size_t);
    }
    return acc;
}
"#;

#[test]
fn w4b101_an_opaque_root_states_no_extent() {
    let plans = table_of(W4_B1_OPAQUE_ROOT, |table| {
        table
            .slice_constructions
            .iter()
            .map(|plan| (plan.element_type.clone(), plan.length.source.receipt_key()))
            .collect::<Vec<_>>()
    })
    .expect("the fixture yields a table");
    let buffer = plans
        .iter()
        .find(|(element, _)| element.contains("uint8_t"))
        .unwrap_or_else(|| panic!("no uint8_t construction: {plans:?}"));
    assert!(
        buffer.1.starts_with("fabricated-extent"),
        "nothing to propagate: {plans:?}"
    );
}

/// **W4B1-3 — the residue is COUNTED, with its reason.** The held row records
/// what its root said (`none`) separately from why it was not lifted, because
/// the first column is the seat's Decision A input and the second is this
/// build's own gate.
#[test]
fn w4b103_the_residue_is_counted_with_its_reason() {
    let rows = b1_rows(W4_B1_UNSIZED_ROOT);
    let storage = rows
        .iter()
        .find(|(subject, ..)| subject.starts_with("StoreUnsized::storage"))
        .unwrap_or_else(|| panic!("no StoreUnsized::storage row: {rows:?}"));
    assert_eq!(storage.1, "held", "{rows:?}");
    // The column now names the SHAPE the root has instead of an extent, so the
    // next build is chosen on the distribution rather than on a guess: here an
    // opaque `GetBuffer()` call result.
    assert_eq!(
        storage.2, "none:call-result",
        "no extent to propagate: {rows:?}"
    );
    assert_eq!(storage.3, "root-states-no-extent", "{rows:?}");
}

/// **W4W-1 (R481-1, the USER's extent-lift waiver) — a root with no extent is
/// lifted anyway, and the receipt says so.**
///
/// `BrotliWriteBits`'s shape over an opaque `GetBuffer()` root: nothing bounds
/// the access, so no arm above this one can answer — not wave-6b's exact width,
/// not wave-5c's mask companion, not the root walk. The user ruled the subject
/// takes the slice form regardless, with `FALLBACK_SLICE_EXTENT`.
///
/// **What is waived** is a checked index past 1024 panicking where the C
/// program read on (behaviour, accepted by the user on the record, addendum
/// 481) AND — the part not to soften — the slice-length UB that constructing a
/// 1024-element view of an object of unproven size can commit, which the
/// 2026-08-30 user+advisor ruling already put out of scope under this same
/// fallback extent. This arm extends that waiver to a new population; it does
/// not open a new hole, and it does not avoid one either.
#[test]
fn w4w01_a_root_with_no_extent_is_lifted_under_the_waiver() {
    let lifts = table_of(W4_B1_UNSIZED_ROOT, |table| {
        table
            .licensed_lifts
            .iter()
            .map(|lift| (lift.subject.clone(), lift.fallback, lift.key()))
            .collect::<Vec<_>>()
    })
    .expect("the fixture yields a table");
    let storage = lifts
        .iter()
        .find(|(subject, ..)| subject.starts_with("StoreUnsized::storage"))
        .unwrap_or_else(|| panic!("the waiver must lift it: {lifts:?}"));
    assert!(
        storage.1,
        "and it must say the extent was fabricated: {lifts:?}"
    );
    assert!(
        storage.2.starts_with("fallback(extent-lift@addendum-77:"),
        "with the receipt the seat counts: {lifts:?}"
    );
}

/// **W4W-2 (control) — where a width IS licensed, the exact arm wins and no
/// fallback receipt is issued.** Order is the discipline of the waiver.
#[test]
fn w4w02_the_exact_arm_wins_over_the_waiver() {
    let lifts = table_of(W4_LIFT_READ32, |table| {
        table
            .licensed_lifts
            .iter()
            .map(|lift| (lift.subject.clone(), lift.fallback))
            .collect::<Vec<_>>()
    })
    .expect("the fixture yields a table");
    let data = lifts
        .iter()
        .find(|(subject, _)| subject.starts_with("HashBytesH40::data"))
        .unwrap_or_else(|| panic!("no HashBytesH40::data lift: {lifts:?}"));
    assert!(!data.1, "the exact width answers first: {lifts:?}");
    assert_eq!(
        lifts.iter().filter(|(_, fallback)| *fallback).count(),
        0,
        "and nothing here is fabricated: {lifts:?}"
    );
}

/// **W4W-3 (control) — a caller already DELIVERED is untouched by the waiver.**
/// The waiver's population is the degraded rows; a subject the ladder already
/// gave a form carrying its own extent is not reconsidered, and issues no
/// receipt.
#[test]
fn w4w03_a_delivered_caller_is_untouched() {
    let fallbacks = table_of(W4_LIFT_FAT_CALLER, |table| {
        table
            .licensed_lifts
            .iter()
            .filter(|lift| lift.fallback)
            .count()
    })
    .expect("the fixture yields a table");
    assert_eq!(fallbacks, 0, "the delivered caller carries its own extent");
}

/// **W4W-4 (wave-6b 025 §1, their ask) — the raw-source bridge still renders on
/// an UNLIFTED caller.**
///
/// With `w6b_unaligned_read32_delivers_as_a_byte_slice` re-premised onto the
/// checked-prefix form, nothing else witnessed that
/// `from_raw_parts((data as *const c_void) as *const u8, 4)` — the path every
/// un-lifted caller takes — renders at all. Since R481-1 the waiver lifts most
/// held callers, so the fixture has to be one the waiver itself refuses: a
/// caller with a use that has no slice image stays raw, and the region bridge
/// fabricates the reader's four bytes exactly as it always did.
#[test]
fn w4w04_the_raw_source_bridge_still_renders_on_an_unlifted_caller() {
    let source = emitted(W4_LIFT_UNSUPPORTED_USE);
    let flat = source
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect::<String>();
    assert!(
        !source.contains("data: &[uint8_t]"),
        "the caller stays raw: {source}"
    );
    assert!(
        flat.contains("from_raw_parts(((dataas*constcore::ffi::c_void)as*constu8),4)")
            || flat.contains("from_raw_parts((dataas*constcore::ffi::c_void)as*constu8,4)"),
        "and the region bridge renders the reader's width: {source}"
    );
}

/// A shared subject at a `*mut` foreign position: `printf("%s", p)` where the
/// pinned contract types the position `*mut i8`. The thin-extent hold sends it
/// past every evidence arm, and the waiver must NOT take it — lifting a shared
/// subject there makes the seam bridge `p.as_ptr().cast_mut()`, and a write
/// through a pointer derived from a shared reference is UB §77 does not waive.
const W4_W_SHARED_AT_A_MUT_POSITION: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
extern "C" {
    fn printf(_: *mut i8, _: ...) -> i32;
}
static mut FMT: [i8; 3] = [37, 115, 0];
pub unsafe extern "C" fn print_arg(mut p: *const i8) -> i32 {
    printf(FMT.as_mut_ptr(), p)
}
"#;

/// **W4W-5 (R483-3(b)) — the mutability half, for `held:thin-extent` rows.**
#[test]
fn w4w05_a_shared_subject_at_a_mut_foreign_position_is_refused() {
    let lifts = table_of(W4_W_SHARED_AT_A_MUT_POSITION, |table| {
        table
            .licensed_lifts
            .iter()
            .map(|lift| lift.subject.clone())
            .collect::<Vec<_>>()
    })
    .expect("the fixture yields a table");
    assert!(
        !lifts
            .iter()
            .any(|subject| subject.starts_with("print_arg::p")),
        "a shared subject may not be lifted into a cast_mut bridge: {lifts:?}"
    );
    let source = emitted(W4_W_SHARED_AT_A_MUT_POSITION);
    assert!(!source.contains(".cast_mut()"), "{source}");
}

/// A parameter with no recorded call site: `pub` and never called in the crate.
/// Its extent cannot be proven from callers, but that is a gap in what was
/// OBSERVED, not a root that states nothing — R489-3(b) gives it its own
/// outcome so Decision A's residue means what it says.
const W4_B1_NO_CALL_SITE: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type size_t = usize;
unsafe extern "C" fn BrotliWriteBits(mut pos: *mut size_t, mut array: *mut uint8_t) {
    let mut p: *mut uint8_t = &mut *array.offset((*pos >> 3 as i32) as isize) as *mut uint8_t;
    *p = 1 as uint8_t;
    *pos = (*pos).wrapping_add(8 as size_t);
}
#[no_mangle]
pub unsafe extern "C" fn StoreExported(mut pos: *mut size_t, mut storage: *mut uint8_t) {
    BrotliWriteBits(pos, storage);
}
"#;

/// **W4B1-4 (R489-3(b)) — unmeasured is not evidence-absent.**
#[test]
fn w4b104_a_parameter_with_no_call_site_is_unmeasured_not_held() {
    let rows = b1_rows(W4_B1_NO_CALL_SITE);
    let storage = rows
        .iter()
        .find(|(subject, ..)| subject.starts_with("StoreExported::storage"))
        .unwrap_or_else(|| panic!("no StoreExported::storage row: {rows:?}"));
    assert_eq!(storage.1, "unmeasured", "{rows:?}");
    assert_eq!(storage.3, "no-call-site-read", "{rows:?}");
    // And Decision A's residue — the rows whose ROOT states nothing — leaves it out.
    assert!(
        !rows.iter().any(
            |(subject, outcome, ..)| subject.starts_with("StoreExported::storage")
                && outcome == "held"
        ),
        "{rows:?}"
    );
}

/// **W4W-6 (wave-4 report 047) — a refusal is a decision and carries its
/// reason.** Until this column existed the waiver receipted only its lifts, so
/// a census could say how many extents were fabricated but never why a held row
/// was passed over — which is the question C5 asked of batch 24 and the
/// artifacts could not answer. The unsupported-use fixture is the cheapest
/// shape that reaches a refusal.
#[test]
fn w4w06_a_refused_row_carries_its_reason() {
    let rows = table_of(W4_LIFT_UNSUPPORTED_USE, |table| {
        table
            .licensed_lifts
            .iter()
            .map(|lift| (lift.subject.clone(), lift.declined, lift.key()))
            .collect::<Vec<_>>()
    })
    .expect("the fixture yields a table");
    let declined = rows
        .iter()
        .find(|(_, declined, _)| declined.is_some())
        .unwrap_or_else(|| panic!("the refusal must be receipted: {rows:?}"));
    assert_eq!(declined.1, Some("slice-use-unsupported"), "{rows:?}");
    assert!(declined.2.starts_with("declined(extent-lift:"), "{rows:?}");
}
