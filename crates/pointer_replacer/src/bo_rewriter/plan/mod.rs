//! **Phase 2 — plan.** Decision table in, edits-as-data out. No AST mutation.
//!
//! An edit is a value, and it carries **its own justification**: a re-route
//! carries the `LoanKey` that licenses it (§1.6 admissibility is a content
//! lookup, so the licensing loan is nameable), and a drop-form edit carries the
//! selector site that motivated it. That is what lets [`super::apply`] be
//! analysis-blind — it never has to ask *why*, because the edit says so.
//!
//! # E1 state visibility
//!
//! Reads the decision table by value. Does NOT read analyses, the export, or
//! decision internals. Hands `apply` a plan by value.
//!
//! # Status
//!
//! S0 lands the phase boundary only. The `Edit` enum is designed against all
//! ten goldens' expected text in S1, with the G01 arm live first.
