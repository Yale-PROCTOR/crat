//! **Harness-level coverage reconciliation (S2a-H).**
//!
//! Design of record: `docs/agents/plan/2026-07-29-s2a-h-harness-reconciliation-design.md`.
//!
//! # Why this lives outside `bo_rewriter/`
//!
//! Four rounds of M1 shipped an in-process coverage gate that could not fail.
//! The diagnosis was not arithmetic but structural: the gate and the collector
//! were written by one author, in one session, against one mental model, so the
//! gate encoded whatever partial notion the collector did. The last instance —
//! F1 — is the sharpest: the gate compared `(fn_did, local)` membership and its
//! docs claimed it guarded the HIR↔MIR *mapping*. It guarded **domain
//! membership, not pairing**, and an in-domain permutation passed it silently.
//!
//! So the comparison moved out, and it compares **artifacts**: two files,
//! independently produced, diffed as data. What that buys over an in-process
//! assertion is that the **evidence outlives the process** — a verdict is
//! reproducible from committed rows rather than only observable inside a run.
//!
//! # What relocation does NOT buy, stated first
//!
//! Moving the comparison does not by itself fix F1. A permutation is invisible
//! to *any* comparison keyed on `(fn_path, mir_local)` unless the rows **carry
//! the pairing**. Location and content are independent choices: the ruling
//! fixed location, [`schema::Row`]'s `param_name`/`arg_index` fix content, and
//! the witness that proves it is the permutation case in [`witnesses`].
//!
//! # Import direction is one-way and mechanized
//!
//! `bo_rewriter` → `coverage_recon::schema` is licensed; the reverse is
//! **forbidden**. Producer B is the point of that rule: an import from
//! `bo_rewriter` into the independent reference walker is exactly the
//! conceptual leakage the authorship split exists to prevent, in mechanically
//! detectable form. Enforced by
//! `bo_rewriter::import_denylist::coverage_recon_never_imports_from_bo_rewriter`.

pub(crate) mod compare;
pub(crate) mod producer_b;
pub(crate) mod schema;

#[cfg(test)]
mod witnesses;
