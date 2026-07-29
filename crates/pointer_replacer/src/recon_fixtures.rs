//! **C.1 — fixture reconciliation.** The first live producer-A vs producer-B
//! comparison.
//!
//! # Why this module exists, rather than living in either producer's home
//!
//! The placement is forced by two rules that together exclude both obvious
//! locations:
//!
//! - the comparison may not live in `bo_rewriter/` (ruling: the gate moves out
//!   of the module it checks), and
//! - `coverage_recon/**` may not reference `bo_rewriter` (amendment (b):
//!   producer B must not be able to inherit producer A's model).
//!
//! So the integration point is a third place — here. That is not a loophole in
//! amendment (b): the rule protects *producer B's module* from A's model, and a
//! test that drives both is exactly the seam where they are supposed to meet.

use crate::{
    bo_rewriter::artifact_rows,
    coverage_recon::{
        compare::{Verdict, compare},
        producer_b,
    },
};

/// Run both producers over one source in a single compiler session and
/// reconcile them.
fn reconcile(src: &str) -> Verdict {
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let a = artifact_rows(tcx).expect("producer A produced a decision table");
        let b = producer_b::rows(tcx);
        compare(&a, &b)
    })
    .expect("fixture compiles")
}

/// Every golden reconciles clean between the two producers.
///
/// **This is the gate the whole apparatus move exists to provide**, running for
/// the first time on real inputs. A disagreement here is a FINDING — it goes to
/// the reviewer with both derivations, and which side is wrong is a ruling. It
/// is never patched by adjusting producer B until it agrees, which would
/// destroy the only property producer B exists to provide.
#[test]
fn every_golden_reconciles_between_the_two_producers() {
    for golden in crate::bo_rewriter::goldens_for_reconciliation() {
        let verdict = reconcile(golden.1);
        assert!(
            verdict.passed(),
            "{}: producers disagree — VIOLATIONS: {:#?}",
            golden.0,
            verdict.violations
        );
        assert!(
            verdict.findings.is_empty(),
            "{}: producers disagree — FINDINGS: {:#?}",
            golden.0,
            verdict.findings
        );
    }
}

/// Non-vacuity: the reconciliation is comparing a non-empty population.
///
/// Without this, a golden set that produced no rows at all would reconcile
/// "clean" and the gate above would be asserting nothing — the same vacuous
/// pass this milestone has been chasing.
#[test]
fn the_reconciliation_compares_a_non_empty_population() {
    let src = "#![allow(dead_code)]\npub unsafe fn f(p: *mut i32, q: *const u8) -> i32 { *p }\n";
    let rows = ::utils::compilation::run_compiler_on_str(src, |tcx| producer_b::rows(tcx))
        .expect("fixture compiles");
    assert_eq!(rows.len(), 2, "fixture must yield two rows: {rows:#?}");
    assert!(reconcile(src).passed());
}
