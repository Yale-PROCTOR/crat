//! Relay 033 (α): the A5 raw-view wrapper takes a selected argument from the
//! INNER class's rendered product instead of re-rendering it from the source
//! form — the symmetric twin of wave-6a's (ii).
//!
//! The wrapper's per-argument declaration used to be built from the plan-time
//! `raw_expression`, which is derived from the ORIGINAL argument text. When
//! another class owns a real edit at exactly that argument's interval, the two
//! renderings are two different products of one region, so the planner held
//! both classes (`cross-class-interval-collision`) rather than let the wrapper
//! overwrite the inner's bridge. Because the seam pass grafts before the A5
//! pass, the argument subtree ALREADY carries the inner's product when the
//! wrapper is built; taking the walked argument text is therefore the whole of
//! (α), and the planner then composes the pair with the outer depending on the
//! inner.
use super::{A5Mode, RewriteOutcome, WholeProgramAttestation};

#[path = "a5_inner_argument_fixture.rs"]
mod fixture;

fn rewrite(input: &str) -> RewriteOutcome {
    super::rewrite_core_injected(
        ::utils::compilation::str_to_input(input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        Some((
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    )
}

/// The census shape: `BrotliFree(m, (*self_0).literal_costs_ as *mut c_void)`.
/// The callee's wrapper owns the call, the caller's class owns the argument.
#[test]
fn the_wrapper_takes_the_inner_class_product_as_its_raw_value() {
    let outcome = rewrite(fixture::A5_INNER_ARGUMENT);
    let RewriteOutcome::Emitted {
        source,
        degradations,
        reverted_count,
        raw_boundary_artifacts,
        ..
    } = outcome
    else {
        panic!("the (α) fixture degraded: {outcome:?}")
    };
    assert_eq!(reverted_count, 0, "{source}");
    assert!(
        raw_boundary_artifacts.class_collisions.lines().count() <= 1,
        "the pair must compose, not collide:\n{}",
        raw_boundary_artifacts.class_collisions
    );
    assert!(
        !degradations
            .iter()
            .any(|d| format!("{d:?}").contains("cross-class-interval-collision")),
        "{degradations:#?}"
    );
    let text = source.split_whitespace().collect::<String>();
    // The callee delivers `&mut MemoryManager`, so the wrapper is materialized
    // around the call; its raw value is the caller's own typed raw temporary,
    // not a re-rendering of `(*self_0).literal_costs_`.
    assert!(text.contains("let__crat_a5_raw_"), "{source}");
    assert!(
        text.contains("__crat_raw"),
        "the inner's product must survive inside the wrapper: {source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "the composed emission must type/borrow-check: {source}"
    );
}

/// **The intra-class arm (relay 034).** A PAIR raw-view call and an A5 T2
/// fallback that render the SAME call for the same class are two whole-call
/// rewrites of one interval — lodepng's `lodepng_assign_icc` at the batch-9
/// census (`pair-t2-raw-view` and `a5-site-proof-t2-fallback` both owning
/// 272439..272561, one of the 22 `intra-class-interval-overlap` subjects). The
/// fallback yields to the rendering it is a fallback for; its per-argument
/// proof sites ride that carrier through `link_a5_fallback_carriers`.
///
/// Witnessed on the plan: with both calls present for one span, exactly ONE
/// whole-call edit is planned and no class carries the intra-class hold.
#[test]
fn the_a5_fallback_yields_to_a_pair_rendering_of_the_same_call() {
    ::utils::compilation::run_compiler_on_str(fixture::A5_INNER_ARGUMENT, |tcx| {
        let (mut table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        assert_eq!(
            table.seams.a5_raw_calls.len(),
            1,
            "the fixture plans exactly one A5 raw-view call"
        );
        // The same call, rendered by the PAIR machinery: the arm's premise.
        let a5 = table.seams.a5_raw_calls[0].clone();
        table
            .seams
            .pair_raw_calls
            .push(super::decision::seam::PairRawViewCall {
                owner_class: a5.owner_class,
                caller: a5.caller,
                callee: a5.callee,
                call_span: a5.call_span,
                views: a5
                    .views
                    .iter()
                    .map(|view| super::decision::seam::PairRawViewTemp {
                        argument_index: view.argument_index,
                        argument_expression: view.argument_expression.clone(),
                        argument_shape: view.argument_shape,
                        raw_expression: view.raw_expression.clone(),
                        target_type: view.target_type.clone(),
                        target: view.target.clone(),
                        source_node: view.source_node,
                        input_rendering: None,
                    })
                    .collect(),
                reasons: Vec::new(),
                atom_ids: Vec::new(),
            });
        let emitted = super::emit_files(tcx, &table, &Default::default(), &[]).unwrap();
        let a5_whole_call_edits = emitted
            .plan
            .by_file
            .values()
            .flatten()
            .filter(|edit| {
                edit.edit_kind == "a5-proof-site-raw-view"
                    && edit.lo == usize::try_from(a5.call_span.lo().0).unwrap()
                    && edit.hi == usize::try_from(a5.call_span.hi().0).unwrap()
            })
            .count();
        assert_eq!(
            a5_whole_call_edits, 0,
            "the fallback plans no second rendering of the call it is a fallback for: {:#?}",
            emitted.plan.by_file
        );
        assert!(
            !emitted
                .plan
                .class_finalization
                .classes
                .values()
                .any(|class| class
                    .hold_reasons()
                    .iter()
                    .any(|reason| reason.contains("intra-class-interval-overlap"))),
            "{:#?}",
            emitted.plan.class_finalization.classes
        );
    })
    .unwrap();
}
