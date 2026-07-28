//! **Phase 4 — verify.** Gates on the emitted crate.
//!
//! Hard gate: the emitted crate type-checks. Structural gates: decision
//! coverage (`|decisions| == |subjects|`) and apply-time rollbacks == 0.
//! Behavioral gate: the designed harness on the applicable subset (S4).
//!
//! # E1 state visibility
//!
//! Gates on the EMITTED crate and on values the earlier phases handed over. It
//! does not re-consult an analysis: a gate that asked the same analysis that
//! produced the decision would agree with it by construction, which is not a
//! gate.

/// Hard gate — the emitted crate passes `tcx.analysis(())`.
///
/// Runs a full compiler invocation over the emitted source. A type error is a
/// gate failure, not a panic to be caught: `run_compiler_on_str` surfaces a
/// `FatalError`, and the emitted crate failing to type-check is exactly the
/// condition this gate exists to report.
pub(crate) fn type_checks(emitted: &str) -> bool {
    ::utils::compilation::run_compiler_on_str(emitted, |tcx| {
        ::utils::type_check(tcx);
    })
    .is_ok()
}
