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
