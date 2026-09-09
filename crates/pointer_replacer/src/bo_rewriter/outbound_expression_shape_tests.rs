//! J20 — the non-subject outbound argument shapes that are not a bare call.
//!
//! Design §10.3: "Every call/foreign/field-store/return sink is a required
//! expression-level site, including projections, casts, temporaries,
//! address-of, and call results." The call-result arm has its own file
//! (`outbound_expression_tests`); this matrix covers the arguments that
//! *contain* a changed native call rather than *being* one. Every fixture is a
//! valid-stack memory-safety pattern, compiled and never executed.

use super::decision::seam::Form;

/// The one skeleton every arm shares. `target` is the native source whose
/// settled form changes; `raw_read` is the raw sink that still needs a pointer.
fn fixture(argument: &str) -> String {
    format!(
        r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn raw_read(q: *const i32) -> i32 {{ q.read() }}
    unsafe fn target(p: *mut i32) -> *mut i32 {{
        *p.offset(1) += 1;
        p
    }}
    pub unsafe fn entry() -> i32 {{
        let mut values = [3, 5, 7];
        raw_read({argument})
    }}
"#
    )
}

struct ShapeOutcome {
    emitted: String,
    plans: usize,
    unavailable: Vec<String>,
    source_form: Form,
    withdrawals: Vec<String>,
}

/// Runs one arm through the ordinary pipeline and reports what the outbound
/// expression planner actually did with it.
fn shape_outcome(input: &str, label: &str) -> ShapeOutcome {
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
            .find(|(subject, _)| subject.label == "target::p")
            .expect("actual native source parameter");
        let source_form = super::decision::seam::form_of(decision);
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
        ShapeOutcome {
            withdrawals: format!("{:#?}", ctx.raw_boundary_artifacts.additive_family_receipts)
                .lines()
                .map(str::trim)
                .filter(|line| line.contains("unsatisfied-family-site"))
                .map(str::to_owned)
                .collect(),
            emitted: files.into_values().next().expect("one emitted file"),
            plans: table.seams.outbound_expressions.plans.len(),
            unavailable: table
                .seams
                .outbound_expressions
                .unavailable
                .values()
                .map(|row| format!("{:?}", row.reason))
                .collect(),
            source_form,
        }
    })
    .expect("original shape fixture compiles")
}

/// The control: the argument IS the changed call. This is the shape the
/// expression planner was built for, and it must stay GREEN across this matrix.
#[test]
fn outbound_shape_bare_call_result_is_bridged() {
    let input = fixture("target(values.as_mut_ptr())");
    let outcome = shape_outcome(&input, "bare call result");
    println!(
        "OUTBOUND-SHAPE[bare call result] form={:?} plans={} unavailable={:?}\n{}",
        outcome.source_form, outcome.plans, outcome.unavailable, outcome.emitted
    );
    assert_eq!(
        outcome.source_form,
        Form::Slice { mutable: true },
        "authoring premise: the native source settles a mutable slice"
    );
    assert_eq!(outcome.plans, 1, "one outbound expression plan");
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "emitted output type/borrow-checks:\n{}",
        outcome.emitted
    );
}

/// The contract every CONTAINING shape must satisfy today: the site is
/// dispositioned, not passed over.
///
/// A cast, a projection or arithmetic wrapped around the changed call is a
/// required expression-level site (design §10.3), but its carrier is not built:
/// the planner keys its native-call lookup on the argument span, and a
/// containing argument is not itself a call. What must never happen is the
/// third outcome — no plan, no hold, and an unadapted boundary left in an
/// emitted tree that no longer compiles. The family withdraws instead, naming
/// the shape in its receipt, and the emitted tree is the untouched original.
///
/// The premise that this shape really does have something to adapt is carried
/// by two facts, not asserted twice: `outbound_shape_bare_call_result_is_bridged`
/// runs the identical skeleton with a bare call argument and settles a mutable
/// slice, and the withdrawal receipt below exists at all — a family was formed
/// for this site and then dropped, naming the shape.
///
/// When the nested carrier is built (recorded as a sized deferral, since it
/// needs a custody-contract extension), these two witnesses become the
/// bridged-and-safe assertions their names promise; the fail-closed contract
/// they pin now is what makes that change measurable.
fn assert_containing_shape_holds_and_leaves_the_input_intact(
    outcome: &ShapeOutcome,
    input: &str,
    label: &str,
) {
    assert_eq!(
        outcome.source_form,
        Form::Raw,
        "{label}: the unsatisfiable site must withdraw its family, not promote"
    );
    assert_eq!(outcome.plans, 0, "{label}: no plan is manufactured");
    let nested = outcome
        .withdrawals
        .iter()
        .filter(|row| row.contains("NestedNativeCarrierUnbuilt"))
        .count();
    assert_eq!(
        nested, 1,
        "{label}: exactly one typed withdrawal names the unbuilt nested \
         carrier: {:#?}",
        outcome.withdrawals
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "{label}: a held site must leave a compiling tree:\n{}",
        outcome.emitted
    );
    assert_eq!(
        outcome.emitted.replace(char::is_whitespace, ""),
        input.replace(char::is_whitespace, ""),
        "{label}: the withdrawn family leaves the original program"
    );
}

/// A cast WRAPPING the changed call.
#[test]
fn outbound_shape_cast_over_a_call_result_holds_with_its_own_reason() {
    let input = fixture("target(values.as_mut_ptr()) as *const i32");
    let outcome = shape_outcome(&input, "cast over call result");
    println!(
        "OUTBOUND-SHAPE[cast over call result] form={:?} plans={} unavailable={:?} withdrawals={:#?}\n{}",
        outcome.source_form,
        outcome.plans,
        outcome.unavailable,
        outcome.withdrawals,
        outcome.emitted
    );
    assert_containing_shape_holds_and_leaves_the_input_intact(
        &outcome,
        &input,
        "cast over call result",
    );
}

/// Pointer arithmetic APPLIED TO the changed call, the other containing shape.
#[test]
fn outbound_shape_offset_over_a_call_result_holds_with_its_own_reason() {
    let input = fixture("target(values.as_mut_ptr()).offset(1)");
    let outcome = shape_outcome(&input, "offset over call result");
    println!(
        "OUTBOUND-SHAPE[offset over call result] form={:?} plans={} unavailable={:?} withdrawals={:#?}\n{}",
        outcome.source_form,
        outcome.plans,
        outcome.unavailable,
        outcome.withdrawals,
        outcome.emitted
    );
    assert_containing_shape_holds_and_leaves_the_input_intact(
        &outcome,
        &input,
        "offset over call result",
    );
}
