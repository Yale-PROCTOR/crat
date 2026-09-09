//! J22–J25 — the escape seams: a settled safe subject that still has to reach a
//! foreign argument, a stored field, or a raw return.
//!
//! Design §10.3: "Every call/foreign/field-store/return sink is a required
//! expression-level site... No-retention evidence yields T1; retention-unknown
//! yields the exact T2 waiver; positive retention is a typed nonmechanical
//! hold." Each fixture is a valid-stack memory-safety pattern, compiled and
//! never executed.

use super::decision::seam::Form;

struct EscapeOutcome {
    emitted: String,
    subject_form: Form,
    subject_reason: String,
}

/// Runs one escape fixture through the ordinary pipeline and reports what the
/// named subject settled and what the emitted tree looks like.
fn escape_outcome(input: &str, subject: &str, label: &str) -> EscapeOutcome {
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
        EscapeOutcome {
            emitted: files.into_values().next().expect("one emitted file"),
            subject_form: super::decision::seam::form_of(decision),
            subject_reason: match decision {
                super::decision::Decision::Degraded(record) => format!("{:?}", record.reason),
                other => format!("{other:?}"),
            },
        }
    })
    .expect("original escape fixture compiles")
}

const FOREIGN_ARG_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    extern "C" {
        fn consume(p: *const i32);
    }
    pub unsafe fn entry() {
        let mut values = [3, 5, 7];
        let p: *mut i32 = values.as_mut_ptr();
        *p.offset(1) += 1;
        consume(p);
    }
"#;

const FIELD_STORE_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub struct Holder {
        pub first: *mut i32,
    }
    pub unsafe fn entry(p: *mut i32, h: *mut Holder) {
        *p.offset(1) += 1;
        (*h).first = p;
    }
"#;

/// J23 — a foreign argument is an ordinary pointer seam: the subject keeps its
/// settled slice form and the boundary takes a raw view of it. The view's
/// mutability follows the foreign parameter, which is what keeps a `*const`
/// position from receiving a mutable derivation it was never promised.
#[test]
fn escape_seam_foreign_argument_takes_a_raw_view_of_the_settled_subject() {
    let outcome = escape_outcome(FOREIGN_ARG_INPUT, "entry::p", "foreign argument");
    println!(
        "ESCAPE-SEAM[foreign argument] form={:?} reason={}\n{}",
        outcome.subject_form, outcome.subject_reason, outcome.emitted
    );
    assert_eq!(
        outcome.subject_form,
        Form::Slice { mutable: true },
        "the escape does not degrade the subject"
    );
    assert!(
        outcome.emitted.contains("consume(p.as_ptr())"),
        "the const foreign position takes the shared view:\n{}",
        outcome.emitted
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "a foreign-argument escape must leave a compiling tree:\n{}",
        outcome.emitted
    );
}

/// J23 mutability contrast — a `*mut` foreign position takes the mutable view.
#[test]
fn escape_seam_foreign_mut_argument_takes_the_mutable_view() {
    let outcome = escape_outcome(FOREIGN_MUT_INPUT, "entry::p", "foreign mut argument");
    println!(
        "ESCAPE-SEAM[foreign mut argument] form={:?} reason={}\n{}",
        outcome.subject_form, outcome.subject_reason, outcome.emitted
    );
    assert_eq!(outcome.subject_form, Form::Slice { mutable: true });
    assert!(
        outcome.emitted.contains("fill(p.as_mut_ptr())"),
        "a writing foreign position must not receive a shared derivation:\n{}",
        outcome.emitted
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "a mutable foreign escape must leave a compiling tree:\n{}",
        outcome.emitted
    );
}

/// J24 — a field store is positive retention: the field keeps the pointer past
/// every span the subject's safe form could justify, so the subject is held
/// rather than given a fabricated raw view. Design §10.3 permits a raw view at
/// a store only "under permitted retention semantics", and this shape has none.
/// The neighbouring `h` still promotes, so the hold is the narrow one.
#[test]
fn escape_seam_field_store_holds_its_subject_and_promotes_the_neighbour() {
    let outcome = escape_outcome(FIELD_STORE_INPUT, "entry::p", "field store");
    println!(
        "ESCAPE-SEAM[field store] form={:?} reason={}\n{}",
        outcome.subject_form, outcome.subject_reason, outcome.emitted
    );
    assert_eq!(
        outcome.subject_form,
        Form::Raw,
        "a stored pointer keeps its raw form: {}",
        outcome.subject_reason
    );
    assert!(
        outcome.emitted.contains("h: &mut Holder"),
        "the hold is narrow -- the unstored neighbour still promotes:\n{}",
        outcome.emitted
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "a field-store escape must leave a compiling tree:\n{}",
        outcome.emitted
    );
}

const FOREIGN_MUT_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    extern "C" {
        fn fill(p: *mut i32);
    }
    pub unsafe fn entry() -> i32 {
        let mut values = [3, 5, 7];
        let p: *mut i32 = values.as_mut_ptr();
        *p.offset(1) += 1;
        fill(p);
        values[0]
    }
"#;
