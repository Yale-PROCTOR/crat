//! **Phase 4 — verify.** Gates on the emitted crate.
//!
//! Hard gate: the emitted crate type-checks (`utils::type_check`, i.e.
//! `tcx.analysis(())`). Structural gates: decision coverage
//! (`|decisions| == |subjects|`) and apply-time rollbacks == 0. Behavioral
//! gate: the designed harness on the applicable subset.
//!
//! # Status
//!
//! S0 lands the phase boundary only.
