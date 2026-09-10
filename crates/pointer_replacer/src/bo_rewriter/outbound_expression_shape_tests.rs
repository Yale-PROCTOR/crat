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
    fixture_with_sink("q.read()", argument)
}

/// The same skeleton with the sink's body chosen by the caller, which is how
/// the retention tier at this seam is varied.
fn fixture_with_sink(sink_body: &str, argument: &str) -> String {
    format!(
        r#"
    #![allow(dead_code, unused_unsafe, unused_variables)]
    unsafe fn raw_read(q: *const i32) -> i32 {{ {sink_body} }}
    unsafe fn target(p: *mut i32) -> *mut i32 {{
        *p.offset(1) += 1;
        p
    }}
    static mut SINK: *const i32 = core::ptr::null();
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
    tiers: Vec<String>,
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
            .find(|(subject, _)| subject.label.ends_with("::p"))
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
        ShapeOutcome {
            tiers: table
                .seams
                .outbound_expressions
                .plans
                .values()
                .map(|plan| format!("{:?}/{:?}", plan.tier, plan.retention))
                .collect(),
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

/// The contract every CONTAINING shape satisfies: the changed call is bridged
/// where it stands, and the cast, projection or arithmetic wrapped around it is
/// left exactly as written.
///
/// The block restores the inner call's OWN raw type rather than converting to
/// the sink's parameter type, which is what lets the outer expression apply to
/// exactly what it applied to before. A required site therefore never has the
/// third outcome -- no plan, no hold, and an unadapted boundary in a tree that
/// no longer compiles.
fn assert_containing_shape_is_bridged(outcome: &ShapeOutcome, original: &str, label: &str) {
    assert_eq!(
        outcome.source_form,
        Form::Slice { mutable: true },
        "{label}: the native source keeps its settled form"
    );
    assert_eq!(outcome.plans, 1, "{label}: one nested outbound plan");
    assert!(
        outcome.unavailable.is_empty(),
        "{label}: nothing is held: {:?}",
        outcome.unavailable
    );
    assert!(
        outcome.withdrawals.is_empty(),
        "{label}: no family withdraws: {:#?}",
        outcome.withdrawals
    );
    assert!(
        outcome.emitted.contains(original),
        "{label}: the enclosing expression survives verbatim:\n{}",
        outcome.emitted
    );
    assert!(
        super::verify::type_checks_str(&outcome.emitted),
        "{label}: emitted output type/borrow-checks:\n{}",
        outcome.emitted
    );
}

/// A cast WRAPPING the changed call.
#[test]
fn outbound_shape_cast_over_a_call_result_is_bridged() {
    let input = fixture("target(values.as_mut_ptr()) as *const i32");
    let outcome = shape_outcome(&input, "cast over call result");
    println!(
        "OUTBOUND-SHAPE[cast over call result] form={:?} plans={} unavailable={:?}\n{}",
        outcome.source_form, outcome.plans, outcome.unavailable, outcome.emitted
    );
    assert_containing_shape_is_bridged(&outcome, "} as *const i32)", "cast over call result");
    assert!(
        outcome.emitted.contains(".as_mut_ptr()) as *mut i32"),
        "the block reproduces the inner call's own raw type:\n{}",
        outcome.emitted
    );
}

/// Pointer arithmetic APPLIED TO the changed call, the other containing shape.
#[test]
fn outbound_shape_offset_over_a_call_result_is_bridged() {
    let input = fixture("target(values.as_mut_ptr()).offset(1)");
    let outcome = shape_outcome(&input, "offset over call result");
    println!(
        "OUTBOUND-SHAPE[offset over call result] form={:?} plans={} unavailable={:?}\n{}",
        outcome.source_form, outcome.plans, outcome.unavailable, outcome.emitted
    );
    assert_containing_shape_is_bridged(&outcome, "}.offset(1))", "offset over call result");
}

// Two changed calls inside one argument are held rather than resolved by
// traversal order (`nested_native_source` refuses to choose). That branch is
// deliberately UNWITNESSED here, and the two authoring attempts are recorded
// rather than a third contrived one: one root called twice makes neither call
// promote, so the fixture witnesses nothing; two roots with two callees
// promoted only one of the two calls, so the finder correctly saw a single
// candidate and planned it. The branch is fail-closed -- it holds -- so the
// cost of leaving it unwitnessed is bounded, and it is recorded in the lane's
// working ledger as an open witness rather than a satisfied one.
