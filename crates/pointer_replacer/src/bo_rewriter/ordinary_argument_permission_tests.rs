//! Seat addendum 259 — the returned-child permission rule at the ORDINARY
//! argument seam, where a settled safe subject is passed directly as a call
//! argument.
//!
//! The predicate, as the adversarial review tightened it: a write through a
//! pointer derived from a **shared-reference view** of non-`UnsafeCell` bytes
//! is UB under both Stacked Borrows and Tree Borrows, regardless of whether
//! the parent reference is still live. So a `*const` position may not be fed
//! `as_ptr()` when a pointer derived from it can reach a write.
//!
//! Rule (1): a **mutable** subject at a `*const` position always takes the
//! writable-const carrier, which costs no holds because a writable derivation
//! satisfies the const parameter type. Rule (2): a **shared** subject holds
//! when the callee can return or output a pointer and no contract row proves
//! otherwise.
//!
//! Every fixture is a valid-stack memory-safety pattern: compiled, never run.

use super::decision::seam::Form;

struct ArgumentOutcome {
    emitted: String,
    subject_form: Form,
    subject_reason: String,
    withdrawals: Vec<String>,
}

fn argument_outcome(input: &str, subject: &str, label: &str) -> ArgumentOutcome {
    assert!(
        super::verify::type_checks_str(input),
        "{label}: unchanged input type/borrow-checks"
    );
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original AST capture");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("one ordinary decision pipeline");
        assert!(
            super::model_cache::solve_receipt().is_some(),
            "actual fixture solve receipt is required"
        );
        let (_, decision) = table
            .entries
            .iter()
            .find(|(entry, _)| entry.label == subject)
            .unwrap_or_else(|| panic!("{label}: actual subject {subject}"));
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("actual emission plan");
        let held = emission.plan.held_classes();
        let (files, rollbacks, _, _) = super::round_files(
            tcx,
            &capture,
            &emission.plan,
            &emission.texts,
            &held,
            &std::collections::BTreeSet::new(),
            emission.plan.root_file.as_ref(),
            &table,
        )
        .expect("one emitted round");
        assert!(rollbacks.is_empty(), "{label}: the arm owns its rendering");
        ArgumentOutcome {
            emitted: files.into_values().next().expect("one emitted file"),
            subject_form: super::decision::seam::form_of(decision),
            subject_reason: match decision {
                super::decision::Decision::Degraded(record) => format!("{:?}", record.reason),
                other => format!("{other:?}"),
            },
            // The typed hold reason travels as the blocked disposition's
            // detail into the slice-use receipt's boundary evidence, which is
            // what the class-site ledger reads. The additive withdrawal row
            // names the family that could not be satisfied, not the reason the
            // boundary refused, so it is the wrong place to look.
            withdrawals: table
                .slice_use_receipts
                .iter()
                .map(|receipt| receipt.boundary_evidence.clone())
                .filter(|evidence| evidence.contains("ordinary-argument-permission"))
                .collect(),
        }
    })
    .expect("original argument fixture compiles")
}

/// The load-bearing witness. A LOCAL callee makes the derivation explicit —
/// `q.cast_mut()` on the argument — so there is no question whether the
/// returned pointer descends from what we handed over.
const LOCAL_CHILD_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn dup(q: *const i32) -> *mut i32 { let _ = q.read(); q.cast_mut() }
    pub unsafe fn entry() -> i32 {
        let mut values = [3, 5, 7];
        let p: *mut i32 = values.as_mut_ptr();
        *p.offset(1) += 1;
        let child = dup(p);
        child.write(8);
        values[0]
    }
"#;

/// The corpus-realistic shape. An `extern` signature alone proves neither
/// UB-freedom nor that the result descends from the argument, so this fixture
/// does not stand on its own; it is here because it is the shape that occurs.
const FOREIGN_CHILD_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    extern "C" {
        fn dup(p: *const i32) -> *mut i32;
    }
    pub unsafe fn entry() -> i32 {
        let mut values = [3, 5, 7];
        let p: *mut i32 = values.as_mut_ptr();
        *p.offset(1) += 1;
        let child = dup(p);
        child.write(8);
        values[0]
    }
"#;

/// A SHARED subject at a callee that can return a pointer. No mutable view
/// exists to upgrade to, so the only sound disposition is a hold.
const SHARED_SUBJECT_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn dup(q: *const i32) -> *mut i32 { let _ = q.read(); q.cast_mut() }
    pub unsafe fn entry(p: *const i32) -> i32 {
        let first = *p.offset(1);
        let child = dup(p);
        child.write(8);
        first
    }
"#;

/// The price control. The same shared subject at a callee that CANNOT yield a
/// pointer keeps its ordinary presentation: rule (2) must not become a blanket
/// refusal of shared subjects at raw positions.
const SHARED_SCALAR_SINK_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn total(q: *const i32) -> i32 { q.read() }
    pub unsafe fn entry(p: *const i32) -> i32 {
        let first = *p.offset(1);
        first + total(p)
    }
"#;

#[test]
fn ordinary_argument_local_child_takes_the_writable_const_carrier() {
    let outcome = argument_outcome(LOCAL_CHILD_INPUT, "entry::p", "local returning child");
    println!(
        "ORDINARY-ARGUMENT[local child] form={:?} reason={}\n{}",
        outcome.subject_form, outcome.subject_reason, outcome.emitted
    );
    assert_eq!(
        outcome.subject_form,
        Form::Slice { mutable: true },
        "the subject still promotes -- the carrier costs no hold"
    );
    assert!(
        outcome
            .emitted
            .contains("dup(p.as_mut_ptr().cast::<i32>().cast_const())"),
        "a mutable subject at a const position keeps write permission:\n{}",
        outcome.emitted
    );
    assert!(
        !outcome.emitted.contains("dup(p.as_ptr())"),
        "the shared view is retired at this seam:\n{}",
        outcome.emitted
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "emitted output type/borrow-checks:\n{}",
        outcome.emitted
    );
}

#[test]
fn ordinary_argument_foreign_child_takes_the_writable_const_carrier() {
    let outcome = argument_outcome(FOREIGN_CHILD_INPUT, "entry::p", "foreign returning child");
    println!(
        "ORDINARY-ARGUMENT[foreign child] form={:?} reason={}\n{}",
        outcome.subject_form, outcome.subject_reason, outcome.emitted
    );
    assert_eq!(outcome.subject_form, Form::Slice { mutable: true });
    assert!(
        outcome
            .emitted
            .contains("dup(p.as_mut_ptr().cast::<i32>().cast_const())"),
        "the corpus-realistic shape takes the same carrier:\n{}",
        outcome.emitted
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "emitted output type/borrow-checks:\n{}",
        outcome.emitted
    );
}

#[test]
fn ordinary_argument_shared_subject_holds_with_its_typed_reason() {
    let outcome = argument_outcome(SHARED_SUBJECT_INPUT, "entry::p", "shared subject");
    println!(
        "ORDINARY-ARGUMENT[shared subject] form={:?} reason={} withdrawals={:#?}\n{}",
        outcome.subject_form, outcome.subject_reason, outcome.withdrawals, outcome.emitted
    );
    assert_eq!(
        outcome.subject_form,
        Form::Raw,
        "a shared subject with a writable descendant may not promote: {}",
        outcome.subject_reason
    );
    let typed = outcome
        .withdrawals
        .iter()
        .filter(|row| row.contains("ordinary-argument-permission:write-through-shared-view"))
        .count();
    assert_eq!(
        typed, 1,
        "the hold names itself exactly once: {:#?}",
        outcome.withdrawals
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "a held site leaves a compiling tree:\n{}",
        outcome.emitted
    );
}

#[test]
fn ordinary_argument_shared_subject_at_a_scalar_sink_still_emits() {
    let outcome = argument_outcome(
        SHARED_SCALAR_SINK_INPUT,
        "entry::p",
        "shared subject, scalar sink",
    );
    println!(
        "ORDINARY-ARGUMENT[shared scalar sink] form={:?} reason={}\n{}",
        outcome.subject_form, outcome.subject_reason, outcome.emitted
    );
    assert_eq!(
        outcome.subject_form,
        Form::Slice { mutable: false },
        "a sink that cannot yield a pointer must not hold a shared subject: {}",
        outcome.subject_reason
    );
    assert!(
        outcome.emitted.contains("total(p.as_ptr())"),
        "the ordinary shared presentation survives where there is no hazard:\n{}",
        outcome.emitted
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "emitted output type/borrow-checks:\n{}",
        outcome.emitted
    );
}
