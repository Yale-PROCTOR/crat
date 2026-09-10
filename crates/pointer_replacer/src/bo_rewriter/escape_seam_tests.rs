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
/// settled slice form and the boundary takes a raw view of it.
///
/// Expectation migrated under addendum 259(1) with this receipt. The original
/// assertion read `consume(p.as_ptr())`, on the reasoning that the view's
/// mutability should follow the foreign parameter. That reasoning was the
/// defect: a `*const` position says what the callee's type promises, not what
/// permission the derivation may carry, and a pointer derived from a shared
/// view of non-`UnsafeCell` bytes may never be written through -- by the callee,
/// or by anything it hands back. A mutable subject therefore takes the writable
/// carrier here, which satisfies the const parameter type and costs no hold.
/// The mutability contrast below keeps its own meaning: `*mut` still selects
/// the plain mutable view rather than the const-cast one.
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
        outcome
            .emitted
            .contains("consume(p.as_mut_ptr().cast::<i32>().cast_const())"),
        "a mutable subject keeps write permission even at a const position:\n{}",
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

/// J25 — a safe subject that escapes through a RAW return position.
const RETURN_ESCAPE_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub unsafe fn entry(p: *mut i32) -> *mut i32 {
        *p.offset(1) += 1;
        p
    }
"#;

/// J26 — one call carrying both an ordinary pointer position and a sealed
/// stdio stream position. `fgets` is the shape the design names: argument 0 is
/// a buffer and an ordinary seam, argument 2 is the stream and belongs to the
/// permanent io-domain boundary.
const IO_DOMAIN_INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    pub struct FILE {
        _private: [u8; 0],
    }
    extern "C" {
        fn fgets(buf: *mut i8, n: i32, stream: *mut FILE) -> *mut i8;
    }
    pub unsafe fn entry(stream: *mut FILE) -> i32 {
        let mut buf = [0i8; 64];
        let p: *mut i8 = buf.as_mut_ptr();
        *p.offset(1) = 65;
        let _ = fgets(p, 64, stream);
        buf[0] as i32
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

/// J26 — one call carrying both an ordinary pointer position and a sealed stdio
/// stream position. The buffer is an ordinary seam and takes its raw view; the
/// stream argument is passed through untouched, with no adapter of any kind.
///
/// Observation recorded rather than asserted: the stream ARGUMENT is
/// intercepted here by `family_contract`'s `PointeeAccess::Stream`, which runs
/// before the generic table, but the stream-typed PARAMETER of the enclosing
/// function is still promoted to `&mut FILE` by the ordinary subject decision.
/// In the corpus that promotion is governed by the sealed io-domain identity
/// set, which a synthetic `FILE` struct is not part of, so this fixture cannot
/// say whether real exposure exists. It is a question for the seat, not a
/// finding, and it is recorded in the lane's working ledger.
#[test]
fn escape_seam_stream_position_is_not_re_presented() {
    let outcome = escape_outcome(IO_DOMAIN_INPUT, "entry::p", "io domain");
    println!(
        "ESCAPE-SEAM[io domain] form={:?} reason={}\n{}",
        outcome.subject_form, outcome.subject_reason, outcome.emitted
    );
    assert_eq!(
        outcome.subject_form,
        Form::Slice { mutable: true },
        "the non-stream buffer position is an ordinary seam"
    );
    assert!(
        outcome
            .emitted
            .contains("pub unsafe fn entry(stream: *mut FILE)"),
        "the stream-typed binding is held by type, not promoted:\n{}",
        outcome.emitted
    );
    assert!(
        outcome
            .emitted
            .contains("fgets(p.as_mut_ptr(), 64, stream)"),
        "the buffer takes its raw view and the stream is passed through \
         unadapted:\n{}",
        outcome.emitted
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "emitted output type/borrow-checks:\n{}",
        outcome.emitted
    );
}
