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
                super::OverlapMode::PreciseReplay,
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
            &ctx.retained_copy_plans,
        )
        .expect("actual emission plan");
        let held = emission.plan.held_classes();
        let (files, rollbacks, _, _, _) = super::round_files(
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

/// J25 — a safe subject that escapes through a RAW return position.
const RETURN_ESCAPE_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub unsafe fn entry(p: *mut i32) -> *mut i32 {
        *p.offset(1) += 1;
        p
    }
"#;

/// J25 — a safe subject escaping through a raw RETURN position is adapted by
/// the return class, not by a raw view: the signature's return form follows the
/// subject and reuses the origin parameter's lifetime rather than inventing a
/// return-only one. A raw view is only needed where the return type must stay
/// raw, which is the surface/fn-pointer case that item 6's wrapper arm owns.
#[test]
fn escape_seam_return_escape_reuses_the_origin_parameter_lifetime() {
    let outcome = escape_outcome(RETURN_ESCAPE_INPUT, "entry::p", "return escape");
    println!(
        "ESCAPE-SEAM[return escape] form={:?} reason={}\n{}",
        outcome.subject_form, outcome.subject_reason, outcome.emitted
    );
    assert_eq!(outcome.subject_form, Form::Slice { mutable: true });
    assert!(
        outcome
            .emitted
            .contains("pub unsafe fn entry<'a>(p: &'a mut [i32]) -> &'a mut [i32]"),
        "one lifetime, taken from the origin parameter:\n{}",
        outcome.emitted
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "emitted output type/borrow-checks:\n{}",
        outcome.emitted
    );
}
