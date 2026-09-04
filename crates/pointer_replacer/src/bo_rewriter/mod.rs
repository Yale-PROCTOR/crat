//! BO rewriter — GREENFIELD module (ruling 2026-07-27, Q2).
//!
//! This module consumes the borrow+ownership (BO) analysis results and emits
//! rewritten Rust. It is a clean-room implementation: the existing
//! [`crate::rewriter`] tree is a FROZEN production baseline and this module
//! **never imports from it**.
//!
//! Design of record:
//! - `docs/agents/plan/2026-07-27-bo-rewriter-scoping.md` (post-mortem + design)
//! - `docs/agents/plan/2026-07-28-m05-export-surface-spec.md` (E-R1..E-R4)
//! - `docs/agents/plan/2026-07-28-m05-decision-matrix.md` (kind mapping)
//!
//! # Isolation rule (Q2)
//!
//! A separate crate would have forced `mod analyses` public, so this is a
//! top-level module instead. That trades compile-time isolation for a
//! discipline that has to be enforced mechanically — see [`import_denylist`].
//!
//! | Target | Policy |
//! |---|---|
//! | `crate::rewriter::*` | **forbidden** — no import, path reference, or copied file |
//! | `crate::analyses::*` | allowed, read-only |
//! | `crate::utils::*`, `::utils::*` | allowed |
//!
//! # Phase separation (M1 architecture directive, binding from the first commit)
//!
//! The module is four phases with one-way data flow and no shared mutable
//! context (E1 state visibility):
//!
//! ```text
//!   analyses + BoExport ──▶ decision ──▶ plan ──▶ apply ──▶ verify
//!                           (reads)     (data)   (blind)   (gates)
//! ```
//!
//! Each phase hands the next a finished value. No phase holds a back-pointer to
//! another, and [`apply`] is *analysis-blind* by enforced rule, not convention —
//! see [`import_denylist`] for the per-phase checks.
//!
//! # Status
//!
//! M1/S0 lands the phase skeleton, the goldens as RED, and the per-phase
//! isolation checks. The decision table, edit plan and applier arrive in S1
//! (G01 walking skeleton) and S2–S3 (breadth).
//!
//! **Substrate of record.** Every corpus number attributed to this module
//! derives from the post-`expand`→`extern`→`preprocess` form; see
//! `docs/agents/2026-08-06-substrate-of-record.md`.

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::Local,
    ty::{Mutability, TyCtxt, TyKind},
};

use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        a5_overlap::{A5Mode, WholeProgramAttestation},
        a5_producer::PlannedC9Mark,
        construction::{cached_precise_rewriter_payload, solve_bo_a5_config},
        crate_slots::{CrateSlots, ptr_chain_depth},
        export::with_bo_export,
        model_cache,
        mutability_facts::MutFacts,
        origin_summary::OriginSummaries,
        origins::compute_origins,
        solver::SlotRef,
    },
    utils::rustc::RustProgram,
};

pub(crate) mod apply;
pub(crate) mod artifact;
pub(crate) mod bridge_receipt;
pub(crate) mod c9;
pub(crate) mod decision;
pub(crate) mod fat_facts;
pub(crate) mod plan;
pub(crate) mod sign_facts;
pub(crate) mod use_census;
pub(crate) mod verify;

/// **The AST application layer's bridge** — phases 1–2 of the migration back to
/// standing decision 3. Test-only while the bar is measured; it becomes
/// production when phase 3 ports the edit vocabulary onto it.
///
/// **GRADUATED (M-2/A task 3, 2026-08-18)** — the verify loop now emits through
/// this layer, so the condition this doc named is met.
pub(crate) mod ast_bridge;
/// **Phase 3** — the edit vocabulary as node transforms, with the fail-closed
/// composition guard built beside its first arm.
pub(crate) mod ast_transform;
#[cfg(test)]
mod emit_tests;
#[cfg(test)]
mod goldens;
#[cfg(test)]
mod import_denylist;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct E1EditContext {
    pub(crate) file: String,
    pub(crate) lo_line: usize,
    pub(crate) hi_line: usize,
    pub(crate) shape: String,
    pub(crate) replacement_head: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum E1DiagnosticSite {
    CallBoundary,
    BodyExpression,
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct E1RevertDiagnostic {
    pub(crate) function: String,
    pub(crate) diagnostic: verify::Diag,
    pub(crate) site_kind: E1DiagnosticSite,
    pub(crate) attribution: String,
    pub(crate) edits: Vec<E1EditContext>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(
    dead_code,
    reason = "Item E's corpus worker is cfg(test); this transport crosses the production rewriter callback only for that measurement"
)]
pub(crate) struct E1Capture {
    pub(crate) observed_root: std::path::PathBuf,
    pub(crate) reverts: Vec<E1RevertDiagnostic>,
    /// Exact call-adapter rows rendered from the SAME `DecisionTable` consumed
    /// by the one E1 emission iteration.
    pub(crate) adapter_receipt: String,
    /// Every subject and item-axis exclusion from that same table/plan.
    pub(crate) subject_receipt: String,
    pub(crate) e2_artifacts: E2Artifacts,
    pub(crate) raw_boundary_artifacts: RawBoundaryArtifacts,
    pub(crate) novel_error_count: usize,
    pub(crate) baseline_keys: usize,
    pub(crate) baseline_errors: usize,
    pub(crate) baseline_msg_env: usize,
    pub(crate) attempted_placements: usize,
    pub(crate) files_touched: usize,
    pub(crate) unplaceable: usize,
    pub(crate) a5_receipt: String,
    /// D4's emitted-MIR Box-drop reconciliation. Empty on non-census paths.
    pub(crate) box_drop_receipt: String,
    pub(crate) solve_receipt: model_cache::SolveReceipt,
    /// Terminal verify-loop outcome. Kept distinct from the diagnostic count:
    /// a degraded program may leave an empty final-revert ledger.
    pub(crate) outcome_kind: CensusOutcomeKind,
    /// Exact, untruncated escalation/reason payload for the census observer.
    pub(crate) escalation: String,
    pub(crate) bisect_probes: usize,
    pub(crate) verify_rounds: usize,
    pub(crate) reverted_count: usize,
    /// The complete emitted Rust-file map on success. A degraded outcome has
    /// no delivered tree and therefore carries `None`, never an empty map.
    pub(crate) emitted_files: Option<std::collections::BTreeMap<plan::FileKey, String>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CensusOutcomeKind {
    Emitted,
    Degraded,
}

impl CensusOutcomeKind {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::Emitted => "emitted",
            Self::Degraded => "degraded",
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct E2Artifacts {
    pub(crate) subjects: String,
    pub(crate) functions: String,
    pub(crate) failures: String,
    pub(crate) seams: String,
    pub(crate) pb_web: String,
    pub(crate) timings: E2Timings,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct E2Timings {
    pub(crate) cache_load_wall_s: String,
    pub(crate) origin_derivation_wall_s: String,
    pub(crate) pb_web_wall_s: String,
    pub(crate) eligibility_wall_s: String,
    pub(crate) finalization_wall_s: String,
    pub(crate) seam_wall_s: String,
    pub(crate) ast_placement_wall_s: String,
    pub(crate) receipt_render_wall_s: String,
    pub(crate) compiler_verification_wall_s: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RawBoundaryArtifacts {
    pub(crate) exposure: String,
    pub(crate) d4_edges: String,
    pub(crate) pairs: String,
    pub(crate) addresses: String,
    pub(crate) arm_outcomes: String,
    pub(crate) edit_keys: String,
    pub(crate) sites: String,
    pub(crate) retention: String,
    pub(crate) dispositions: String,
    pub(crate) subjects: String,
    pub(crate) atoms: String,
    pub(crate) atom_outcomes: String,
    pub(crate) final_reverts: String,
    pub(crate) bridge_events: Vec<bridge_receipt::BridgeReceiptEvent>,
    pub(crate) class_costs: String,
    pub(crate) class_collisions: String,
    pub(crate) unresolved_classes: String,
    pub(crate) degraded_output_receipt: String,
    pub(crate) per_arm_timers_status: String,
    pub(crate) timings: RawBoundaryTimings,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EmissionRunConfig {
    pub(crate) configured_exposure: decision::exposure::ConfiguredExposureInput,
}

impl Default for EmissionRunConfig {
    fn default() -> Self {
        Self {
            configured_exposure: decision::exposure::ConfiguredExposureInput::explicit_empty(
                "bo-rewriter-default-explicit-empty",
            ),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RawBoundaryTimings {
    pub(crate) site_derivation_wall_s: String,
    pub(crate) retention_fixpoint_wall_s: String,
    pub(crate) certificate_replay_wall_s: String,
    pub(crate) decision_wall_s: String,
    pub(crate) render_wall_s: String,
    pub(crate) receipt_wall_s: String,
    pub(crate) initial_verify_wall_s: String,
    pub(crate) atom_reverify_wall_s: String,
}

/// What one M1 rewrite attempt produced.
///
/// `Degraded` is a first-class outcome, not an error: §1.6 admits only
/// conflict-non-increasing re-routes, and **everything outside that envelope
/// degrades in the decision phase with a named reason**. Making that a variant
/// rather than a panic or a silent skip is what lets S2 count envelope
/// failures — the registered commitment that decides whether
/// emission-guided refinement is ever built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RewriteOutcome {
    /// The emitted crate source, **with the degradations that accompanied it**.
    ///
    /// Degradations ride along with a successful emission on purpose: a crate
    /// can emit while most of its subjects were degraded, and an `Emitted` that
    /// did not say so would let a 100%-degraded program count as a success.
    /// `emitted_count` is how a caller tells a real rewrite from a no-op.
    Emitted {
        /// The crate **root's** final text. For a single-file crate this is the
        /// whole emitted crate; for a multi-file crate it is the root only, and
        /// [`Self::Emitted::files`] carries every file the rewrite changed.
        ///
        /// Read back from the materialized copy rather than reconstructed, so it
        /// is correct whether or not the root itself was edited.
        source: String,
        /// The files this outcome emits, keyed by file.
        ///
        /// ⚠ **NOT "every file the rewrite changed" — that is what this said,
        /// and it was false on the AST layer** (2026-08-18). The AST emission
        /// map is SEEDED with every file holding a function, because a crate
        /// with no surviving edits must still emit its original text rather
        /// than an empty file (the g09 fix). So on that layer `files` can
        /// contain a file whose bytes are IDENTICAL to the substrate.
        ///
        /// Consequently **`files.len()` is not `files_touched`**, and the stale
        /// wording here is what licensed a consumer to re-derive it that way.
        /// Use [`Self::Emitted::files_touched`].
        files: std::collections::BTreeMap<plan::FileKey, String>,
        /// **Files with at least one SURVIVING EDIT** (ruling 2026-08-18),
        /// carried from the loop rather than re-derived from `files`.
        ///
        /// It exists because it was already computed and then DROPPED here:
        /// `OutcomeFacts` held the ruled value, `emitted()` did not pass it on,
        /// and the reporting site recovered a number by measuring `files`
        /// instead — a second derivation that agreed with the first only on the
        /// span layer, where `render` returns edited files only.
        files_touched: usize,
        degradations: Vec<decision::Degradation>,
        emitted_count: usize,
        /// Pointer parameters on item kinds M1 does not rewrite. Carried out
        /// here so the exclusions reach a consumer **by construction** — the
        /// previous buckets were written and read by nothing outside one test,
        /// while the ledger claimed they "flow into S2b's counters".
        excluded: decision::universe::Excluded,
        emitted_sites: Vec<EmittedSite>,
        /// Bisect probes spent. **0 means the revert loop converged on its own**;
        /// nonzero means attribution failed, the detector fired, and (C) found
        /// the culprit the containing-function heuristic could not.
        bisect_probes: usize,
        /// Main verify-loop compiler invocations, excluding bisect probes.
        verify_rounds: usize,
        /// Why the loop escalated, when it did. `None` means it never had to.
        /// Carried on the SUCCESS outcome because a crate recovered by bisect is
        /// still a crate whose attribution was wrong — collapsing that into a
        /// plain success would hide the very case (C) exists for.
        escalated: Option<String>,
        /// Subjects the verify loop took back.
        reverted_count: usize,
        /// Edit owners invisible to span attribution.
        attribution_blind: usize,
        /// The first verify's diagnostics.
        first_diags: Vec<verify::Diag>,
        /// The temp-copy root those diagnostics' paths are absolute within.
        /// Captured with them, from the SAME round — each revert round
        /// materializes its own temp directory, so a later round's root would
        /// not canonicalize the first round's paths.
        observed_root: Option<std::path::PathBuf>,
        baseline_keys: usize,
        baseline_errors: usize,
        baseline_msg_env: usize,
        /// Decisions that could not be turned into a placed edit — a
        /// macro-generated span, a span straddling two files, a file with no
        /// editable identity. Carried out for the same reason as `excluded`:
        /// counted and attributed, never silently dropped. Expected zero on the
        /// frozen corpus; a nonzero count is a finding to rule on.
        unplaceable: Vec<plan::Unplaceable>,
        /// Resolved A5 construction and selected-model identity.
        a5_receipt: String,
        /// E1's single-iteration diagnostic rows. Empty on ordinary runs.
        e1_reverts: Vec<E1RevertDiagnostic>,
        /// E1's adapter receipt, empty on ordinary runs.
        e1_adapter_receipt: String,
        /// E1's identity-bearing subject seed, empty on ordinary runs.
        e1_subject_receipt: String,
        e2_artifacts: E2Artifacts,
        raw_boundary_artifacts: RawBoundaryArtifacts,
        /// Baseline-subtracted error count from the one verify invocation.
        e1_novel_error_count: usize,
        /// D4's emitted-MIR Box-drop reconciliation.
        e1_box_drop_receipt: String,
        /// Cache/solve receipt captured inside the compiler callback.
        solve_receipt: Option<model_cache::SolveReceipt>,
    },
    /// No emission, with whatever attribution was available.
    Degraded {
        reason: String,
        degradations: Vec<decision::Degradation>,
        excluded: decision::universe::Excluded,
        /// **Observability of the ATTEMPT.** A crate that fails the gate still
        /// rewrote subjects — that is usually WHY it failed. Reporting zero here
        /// is the "deferral recorded, never zeroed" rule violated at the
        /// instrument, and it blocked S2b.0's span-bucket axis outright.
        emitted_count: usize,
        files_touched: usize,
        /// The rewritten subjects' own functions, so a verify diagnostic can be
        /// attributed to one.
        emitted_sites: Vec<EmittedSite>,
        /// Bisect probes spent before giving up.
        bisect_probes: usize,
        /// Main verify-loop compiler invocations, excluding bisect probes.
        verify_rounds: usize,
        /// Subjects the verify loop took back. **Measured, never zeroed** — the
        /// defect this structure exists to prevent.
        reverted_count: usize,
        /// Edit owners invisible to span attribution.
        attribution_blind: usize,
        /// The first verify's diagnostics.
        first_diags: Vec<verify::Diag>,
        /// The temp-copy root those diagnostics' paths are absolute within.
        /// Captured with them, from the SAME round — each revert round
        /// materializes its own temp directory, so a later round's root would
        /// not canonicalize the first round's paths.
        observed_root: Option<std::path::PathBuf>,
        baseline_keys: usize,
        baseline_errors: usize,
        baseline_msg_env: usize,
        /// Decisions that could not be turned into a placed edit. **Measured,
        /// never zeroed** — carried here for exactly the reason `emitted_count`
        /// and `reverted_count` above are.
        ///
        /// This is the THIRD instance of the shape those two document, and it
        /// survived the structure built to prevent a third: [`OutcomeFacts`]
        /// stopped any site from *hand-filling* a field, but `degraded()` could
        /// still DROP one, because the variant had nowhere to put it. A
        /// one-filling-site rule constrains how a field is written and says
        /// nothing about whether it is written at all.
        ///
        /// The reported zero was a constant on every FAIL row from `fb82552e`
        /// until S2b.3, which made two S2b.0 claims — `unplaceable` "sound on
        /// every row" and "0 on all 20" — hold over 10 programs rather than 20.
        /// A pin on the constant would have been unfailable precisely where it
        /// matters, so this is the precondition for S2b.3's `unplaceable == 0`
        /// gate rather than a tidy-up.
        unplaceable: Vec<plan::Unplaceable>,
        /// Resolved A5 construction and selected-model identity.
        a5_receipt: String,
        /// E1's single-iteration diagnostic rows. Empty on ordinary runs.
        e1_reverts: Vec<E1RevertDiagnostic>,
        /// E1's adapter receipt, empty on ordinary runs.
        e1_adapter_receipt: String,
        /// E1's identity-bearing subject seed, empty on ordinary runs.
        e1_subject_receipt: String,
        e2_artifacts: E2Artifacts,
        raw_boundary_artifacts: RawBoundaryArtifacts,
        /// Baseline-subtracted error count from the one verify invocation.
        e1_novel_error_count: usize,
        /// D4's emitted-MIR Box-drop reconciliation.
        e1_box_drop_receipt: String,
        /// Cache/solve receipt captured inside the compiler callback.
        solve_receipt: Option<model_cache::SolveReceipt>,
    },
}

/// M1 entry point: source in, rewritten source out.
///
/// The four phases run in order, each handed the previous one's finished value:
/// `decision` (the only phase that reads analyses) → `plan` (edits as data) →
/// `apply` (analysis-blind splice) → `verify` (gates).
///
/// # Capture scope
///
/// The driver opens [`with_bo_export`] explicitly. The ambient `CRAT_BO_EXPORT`
/// flag is for corpus workers; the driver **is** the consumer, so it arms
/// unconditionally and pays the capture cost by design.
///
/// # S1 scope
///
/// Depth-0 pointer *parameters* decided `Ref`. Everything else degrades in the
/// decision phase with a named reason.
#[allow(
    dead_code,
    reason = "M1's only entry point, and it has no non-test caller until the \
              rewriter is wired into the pipeline. The allow is HERE, on one \
              item, rather than module-wide: seeding this as a live root keeps \
              dead_code active over everything reachable from it, which is what \
              the module-wide blanket switched off — it hid the two dead \
              universe fields the lint exists to catch."
)]
pub(crate) fn rewrite_m1(input: &str) -> RewriteOutcome {
    // **The single-file case of the general path — not a second path.** The
    // input is staged as a one-file crate and handed to `rewrite_m1_path`, so
    // the ten goldens exercise exactly the mechanism the corpus will. A parallel
    // string pipeline is the hazard class this milestone exists to remove: it
    // would be exercised by every test and by nothing real.
    rewrite_core(
        ::utils::compilation::str_to_input(input),
        None,
        MAX_REVERT_ROUNDS,
    )
}

/// **THE SWITCHOVER ARTIFACT's string entry** — the AST layer, emitting a
/// program.
///
/// The counterpart of [`rewrite_m1`] on the new layer. It runs no verify loop
/// and no revert rounds: those live in `rewrite_core` around the SPAN layer, and
/// phase 5's question is what the AST layer emits, not how the loop converges
/// over it. Wiring the loop to this layer is the M1-close merge list's business.
///
/// ⚠ **ORDERING**: `ast_emitted_source` captures the AST as its first action,
/// before `decide_table_with_ctx` touches HIR — the constraint `ast_bridge`'s
/// module doc states. Nothing here may run a query ahead of it.
#[cfg(test)]
pub(crate) fn ast_emitted_source_of(input: &str) -> Result<String, String> {
    match ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(input),
        |tcx| {
            // The string entry emits the UN-reverted program: it runs no verify
            // loop, so there is no revert set to honour. Named, not defaulted.
            ast_transform::ast_emitted_source(tcx, &ast_transform::RevertSet::default())
                .map(|(source, _stats)| source)
        },
    ) {
        Ok(inner) => inner,
        Err(why) => Err(format!("{why:?}")),
    }
}

/// **W1's entry — the AST layer emitting under a NON-EMPTY revert set.**
///
/// Every cross-layer witness before this one ran with `RevertSet::default()`, a
/// gap registered at the fabrication close. The loop this layer is being wired
/// into reverts on every round but the first, so *"does the AST layer honour a
/// revert set"* is the swap's precondition — and it could not be settled by
/// reading, because the comment that answered it was stale.
///
/// ⚠ **ORDER IS LOAD-BEARING, and it is the loop's order too.** `capture_ast`
/// must run before anything touches HIR; `oracle_reverts` queries
/// `hir_body_owners`. Capture first, resolve second, emit third.
///
/// `reverts_text` is the oracle's own format (`{fn_path}::{param}#{mir_local}`,
/// one per line) parsed by the production resolver — not a test-only shortcut,
/// so this exercises revert RESOLUTION as well as revert honouring.
#[cfg(test)]
pub(crate) fn ast_emitted_source_of_reverting(
    input: &str,
    reverts_text: &str,
) -> Result<String, String> {
    match ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(input),
        |tcx| {
            let capture = ast_transform::capture_ast(tcx)?;
            let reverts = ast_transform::oracle_reverts(tcx, reverts_text, "w1-fixture")?;
            ast_transform::ast_emitted_source_from(tcx, &capture, &reverts)
                .map(|(source, _stats)| source)
        },
    ) {
        Ok(inner) => inner,
        Err(why) => Err(format!("{why:?}")),
    }
}

/// **The one-capture-per-session fact, as an entry a test can call twice.**
///
/// Returns `(first, second)` outcomes of `capture_ast` in ONE session. The
/// loop's design rests on this: it captures once and re-emits per round, and
/// the reason is that the second capture cannot work, not that re-capturing
/// would be slow.
#[cfg(test)]
pub(crate) fn two_captures_in_one_session(input: &str) -> Result<(bool, bool), String> {
    match ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(input),
        |tcx| {
            let first = ast_transform::capture_ast(tcx).is_ok();
            let second = ast_transform::capture_ast(tcx).is_ok();
            Ok((first, second))
        },
    ) {
        Ok(inner) => inner,
        Err(why) => Err(format!("{why:?}")),
    }
}

/// M1's **general** entry point: a crate rooted at `root`, rewritten into a temp
/// copy and gated there.
#[allow(
    dead_code,
    reason = "no caller until 0a.4's corpus smoke; `rewrite_m1` reaches the same               core through the other entry. Targeted here rather than               module-wide so the lint stays live over everything reachable."
)]
pub(crate) fn rewrite_m1_path(root: &std::path::Path) -> RewriteOutcome {
    rewrite_core(
        ::utils::compilation::path_to_input(root),
        Some(root),
        MAX_REVERT_ROUNDS,
    )
}

/// **The one emission path.** Both entry points funnel here; they differ only in
/// the compiler input and in what the emitted files are materialized *onto*.
///
/// # Why the string entry is not staged to disk first
///
/// Staging it would make every span render against a temp directory — an
/// absolute, machine-specific path containing a pid and a counter. Sites would
/// stop being reproducible between runs, which is the D19 failure again: a
/// report whose values permute between runs is not comparable. Compiling the
/// string as `<main.rs>` keeps attribution stable, and the emission logic below
/// is shared regardless, which is what the one-path ruling is actually about.
/// **(C) — threshold bisect.** Escalation path when attribution is wrong.
///
/// Binary-searches the smallest `k` such that reverting the first `k` candidates
/// (in deterministic sorted order) makes the crate compile. Reverting ALL of
/// them always compiles — that is the original program — so the search always
/// terminates, in `ceil(log2(n+1))` probes.
///
/// **NOT minimal-set ddmin, and deliberately so.** The result depends on the
/// candidate order, so it may revert more than strictly necessary. What it buys
/// is a bounded, terminating escalation that does not trust attribution — which
/// is exactly what the detector escalated for. A minimal-set search is
/// `O(n log n)` probes in the bad case, and at brotli's 566 s per compile that
/// is not affordable; the non-minimality is the price of the budget.
fn bisect(
    candidates: &[bridge_receipt::SignatureClassId],
    base: &std::collections::BTreeSet<bridge_receipt::SignatureClassId>,
    mut compiles: impl FnMut(&std::collections::BTreeSet<bridge_receipt::SignatureClassId>) -> bool,
) -> (
    std::collections::BTreeSet<bridge_receipt::SignatureClassId>,
    usize,
) {
    let (mut lo, mut hi) = (0usize, candidates.len());
    let mut probes = 0usize;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let mut trial = base.clone();
        trial.extend(candidates[..mid].iter().cloned());
        probes += 1;
        if compiles(&trial) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    let mut result = base.clone();
    result.extend(candidates[..lo].iter().cloned());
    (result, probes)
}

/// Test-only entry that lowers the round cap, so the CAP arm of the dual
/// termination can be witnessed without manufacturing a looping fixture.
/// A parameter rather than an env knob: no production seam.
/// Test-only: force decisions at the phase boundary, reproducing a shape the
/// decision phase would not itself emit.
#[cfg(test)]
pub(crate) fn rewrite_m1_path_injected(
    root: &std::path::Path,
    max_rounds: usize,
    inject: &(dyn Fn(&mut decision::DecisionTable) + Sync),
) -> RewriteOutcome {
    rewrite_core_injected(
        ::utils::compilation::path_to_input(root),
        Some(root),
        max_rounds,
        inject,
        false,
        false,
        false,
        None,
    )
}

#[cfg(test)]
pub(crate) fn rewrite_m1_path_a5_injected(
    root: &std::path::Path,
    mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
    inject: &(dyn Fn(&mut decision::DecisionTable) + Sync),
) -> RewriteOutcome {
    rewrite_core_injected(
        ::utils::compilation::path_to_input(root),
        Some(root),
        MAX_REVERT_ROUNDS,
        inject,
        false,
        false,
        false,
        Some((mode, attestation)),
    )
}

#[cfg(test)]
pub(crate) fn rewrite_m1_path_with_emission_config(
    root: &std::path::Path,
    mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
    run_config: &EmissionRunConfig,
) -> RewriteOutcome {
    rewrite_core_injected_with_config(
        ::utils::compilation::path_to_input(root),
        Some(root),
        MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        Some((mode, attestation)),
        run_config,
    )
}

fn rewrite_core(
    input: rustc_session::config::Input,
    tree_base: Option<&std::path::Path>,
    max_rounds: usize,
) -> RewriteOutcome {
    rewrite_core_injected(
        input,
        tree_base,
        max_rounds,
        &|_| {},
        false,
        false,
        false,
        None,
    )
}

/// [`rewrite_core`] with a hook applied to the finished decision table at the
/// PHASE BOUNDARY, before `plan` sees it.
///
/// No-op in production. It exists so a test can hand the downstream phases a
/// shape A1's envelope normally prevents — the `decide_table_perturbed`
/// precedent, at the table rather than the subject. **Not a production fault
/// seam:** a parameter with a no-op default, not an env-gated branch.
fn rewrite_core_injected(
    input: rustc_session::config::Input,
    tree_base: Option<&std::path::Path>,
    max_rounds: usize,
    inject: &(dyn Fn(&mut decision::DecisionTable) + Sync),
    probe_only: bool,
    census_once: bool,
    raw_boundary_full: bool,
    a5_override: Option<(A5Mode, Option<WholeProgramAttestation>)>,
) -> RewriteOutcome {
    rewrite_core_injected_with_config(
        input,
        tree_base,
        max_rounds,
        inject,
        probe_only,
        census_once,
        raw_boundary_full,
        a5_override,
        &EmissionRunConfig::default(),
    )
}

#[allow(clippy::too_many_arguments)]
fn rewrite_core_injected_with_config(
    input: rustc_session::config::Input,
    tree_base: Option<&std::path::Path>,
    max_rounds: usize,
    inject: &(dyn Fn(&mut decision::DecisionTable) + Sync),
    probe_only: bool,
    census_once: bool,
    raw_boundary_full: bool,
    a5_override: Option<(A5Mode, Option<WholeProgramAttestation>)>,
    run_config: &EmissionRunConfig,
) -> RewriteOutcome {
    // The string entry's original text, so a baseline exists for it too.
    let virtual_original = match &input {
        rustc_session::config::Input::Str { input, .. } => Some(input.clone()),
        rustc_session::config::Input::File(_) => None,
    };
    let root_hint = tree_base;
    let result = ::utils::compilation::run_compiler_on_input(input, |tcx| {
        // **THE ONE AST CAPTURE PER SESSION — hoisted here, and this position is
        // the whole point** (M-2/A task 3, 2026-08-18).
        //
        // `capture_ast` succeeds at most once per session: `expanded_ast` panics
        // once the HIR is built, and the capture builds it. `decide_table` on
        // the very next line is HIR work, so a capture taken any later — at
        // `emit_files`, or per round inside the verify loop — is already too
        // late and returns `Err("AST capture panicked")`.
        //
        // The verify loop therefore re-emits from THIS pristine capture on every
        // round rather than re-capturing; `transform_with` transforms a clone,
        // so the capture stays reusable. Witnessed at
        // `a_second_capture_in_one_session_fails` — the constraint is measured,
        // not asserted.
        //
        // ⚠ Nothing may run a query ahead of this line.
        let capture = ast_transform::capture_ast(tcx)?;
        let (mut table, decide_ctx) =
            decide_table_with_emission_config(tcx, a5_override, run_config)?;
        let retained_c9_plans = decide_ctx.retained_c9_plans.clone();
        let a5_receipt = decide_ctx.a5_receipt.clone();
        inject(&mut table);
        let table = table;
        let emission = emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &retained_c9_plans,
        )?;
        let (emission_plan, emission_texts) = (emission.plan.clone(), emission.texts.clone());
        // Structural gate: rollbacks must be zero.
        if !emission.rollbacks.is_empty() {
            // IDENTITY, not just a reason. The previous message mapped to
            // `r.reason` alone, so a 17-edit rollback rendered as seventeen
            // copies of one string with no way to tell WHICH edits collided —
            // the plan defect it reports was undiagnosable from the row that
            // reported it. Each rollback now names its owner and byte range.
            return Err(format!(
                "apply rolled back {} edit(s): [{}]",
                emission.rollbacks.len(),
                emission
                    .rollbacks
                    .iter()
                    .map(|r| format!(
                        "{} @{}..{} owner={} just={:?}",
                        r.reason, r.edit.lo, r.edit.hi, r.edit.owner_path, r.edit.justification
                    ))
                    .collect::<Vec<_>>()
                    .join(" | ")
            ));
        }
        let e1_subject_receipt = if census_once {
            e1_subject_seed_tsv(tcx, &table, &decide_ctx, &emission.unplaceable)?
        } else {
            String::new()
        };
        let e1_box_drop_policies = if census_once {
            box_mir_drop_policies(tcx, &table, &emission.unplaceable)
        } else {
            Vec::new()
        };
        let degradations: Vec<decision::Degradation> = table.degradations().cloned().collect();
        let mut emitted_sites: Vec<EmittedSite> = Vec::new();
        // One entry per EMITTED SUBJECT (not per function), so a revert can move
        // exactly the right number of subjects from emitted to degraded and the
        // accounting identity survives the loop.
        let mut emitted_subjects: Vec<EmittedSubject> = Vec::new();
        // PLACEMENT-TRUTH (S2b.3). A `Ref` decision that `plan` could not place
        // produced no edit, so counting it as emitted over-reports the rewrite
        // by exactly the unplaceable set. Exposure is zero on the frozen corpus
        // today, which is the reason to fix the derivation NOW: a counter that
        // is right by measurement rather than by construction is one corpus
        // change away from being wrong, and the wrongness would present as a
        // yield number rather than as a failure.
        //
        // Subtracted here, at the one place `emitted_subjects` is built, rather
        // than from the total afterwards: `emitted_sites` is derived in the same
        // loop, and a function whose only subject went unplaced is NOT a
        // rewritten site — attributing a verify diagnostic to it would blame a
        // function this run never touched.
        let unplaceable_subjects: std::collections::BTreeSet<&str> = emission
            .unplaceable
            .iter()
            .map(|u| u.subject.as_str())
            .collect();
        let mut seen_fns = rustc_hash::FxHashSet::default();
        for (subject, decision) in &table.entries {
            // EXHAUSTIVE (S3.0, ruling 5). A `matches!` here compiled clean
            // against a third `Decision` variant and silently dropped the
            // subject from `emitted_subjects` — measured with a variant probe
            // before the repair. A `match` makes the next disposition a compile
            // error at this site.
            match decision {
                decision::Decision::Ref { .. }
                | decision::Decision::InferredRef { .. }
                | decision::Decision::Slice { .. }
                | decision::Decision::Opt { .. }
                | decision::Decision::Box(_) => {}
                decision::Decision::Degraded(_) => continue,
            }
            let owner = tcx.def_path_str(subject.fn_did.to_def_id());
            // S3.0′: the SAME key `plan` stamped into `Unplaceable::subject`.
            // Built here by hand until S3.0′, beside an identical hand-built
            // copy in `plan` — and both keyed on the NAME, so two subjects that
            // render the same name in one function collapsed into one.
            let key = subject.identity_key(&owner);
            if unplaceable_subjects.contains(key.as_str()) {
                continue;
            }
            emitted_subjects.push(EmittedSubject {
                owner_class: bridge_receipt::SignatureClassId::of(subject.fn_did),
                owner_path: owner.clone(),
                subject: key,
                site: decision::emitability::EmitabilityFacts::site(
                    tcx,
                    subject.attribution_span(),
                ),
                atoms: table
                    .seams
                    .raw_boundary_atom_groups
                    .get(&(subject.fn_did, subject.hir_id))
                    .map(|atoms| atoms.iter().map(|atom| atom.id.clone()).collect())
                    .unwrap_or_default(),
            });
            if !seen_fns.insert(subject.fn_did) {
                continue;
            }
            // The signature span ALONE is not the function: `hir_span` on a fn
            // returns its header, so `ht_iterator` measured as lines 207..207
            // while the error it caused sat at 214. Every diagnostic then fell
            // outside every extent and the own-fn bucket was unfailable by
            // construction — it could only ever report zero. Union with the
            // body's span.
            let signature = tcx.hir_span(tcx.local_def_id_to_hir_id(subject.fn_did));
            let fn_span = signature.to(tcx.hir_body_owned_by(subject.fn_did).value.span);
            let source_map = tcx.sess.source_map();
            let (lo, hi) = (
                source_map.lookup_char_pos(fn_span.lo()),
                source_map.lookup_char_pos(fn_span.hi()),
            );
            let Some(key) = file_key(&lo.file.name) else {
                continue;
            };
            emitted_sites.push(EmittedSite {
                owner_class: bridge_receipt::SignatureClassId::of(subject.fn_did),
                file: match key {
                    plan::FileKey::Real(path) => path.display().to_string(),
                    plan::FileKey::Virtual(name) => name,
                },
                fn_path: tcx.def_path_str(subject.fn_did.to_def_id()),
                lo_line: lo.line,
                hi_line: hi.line,
            });
        }
        // The crate ROOT's final text: its emitted version if the root was
        // edited, otherwise its original source. Computed here because only the
        // compiler session can supply the unedited text.
        let source_map = tcx.sess.source_map();
        let root_text = source_map
            .files()
            .iter()
            .find_map(|sf| {
                let key = file_key(&sf.name)?;
                let is_root = match &key {
                    plan::FileKey::Virtual(_) => true,
                    plan::FileKey::Real(path) => Some(path.as_path()) == root_hint,
                };
                if !is_root {
                    return None;
                }
                emission
                    .files
                    .get(&key)
                    .cloned()
                    .or_else(|| sf.src.as_ref().map(|src| src.to_string()))
            })
            .unwrap_or_default();
        // **THE LOOP RUNS HERE NOW** (M-2/A) — inside the session, so `tcx` is
        // live for every revert round. `emitted_subjects.len()` is NOT a count
        // of `Ref` decisions (which is what the deleted `emitted_count()`
        // computed): it is the placed set, already filtered above, so `emitted`
        // names what the rewrite actually did to the source.
        Ok(verify_and_revert(
            tcx,
            &capture,
            &table,
            tree_base,
            virtual_original,
            max_rounds,
            probe_only,
            census_once,
            raw_boundary_full,
            emission.files,
            emission_plan,
            emission_texts,
            emission.unplaceable,
            degradations,
            emitted_subjects.len(),
            root_text,
            emitted_sites,
            emitted_subjects,
            a5_receipt,
            e1_subject_receipt,
            decide_ctx.e2_artifacts.clone(),
            decide_ctx.raw_boundary_artifacts.clone(),
            e1_box_drop_policies,
        ))
    });

    match result {
        Ok(Ok(outcome)) => outcome,
        // Nothing was decided, so the facts are genuinely empty here — the one
        // place a zero is the measurement rather than an omission.
        Ok(Err(reason)) => OutcomeFacts::default().degraded(reason),
        Err(_) => OutcomeFacts::default().degraded("input crate did not compile".to_owned()),
    }
}

/// **THE VERIFY/REVERT LOOP — RELOCATED INSIDE THE COMPILER SESSION** (M-2/A).
///
/// It used to run AFTER `run_compiler_on_input` returned, consuming ten values
/// across the closure boundary. That worked only because `render` consumes
/// PRE-COMPUTED data — a plan and file texts. The AST emitter cannot: it
/// RE-DERIVES from `tcx`, and calling it outside the session is the `scoped-tls`
/// panic four corpus programs already paid for.
///
/// So the loop moved to the data rather than the data to the loop.
///
/// ⚠ **NOT behaviour-preserving by construction.** Relocated control flow
/// cannot be proven unchanged by its shape. The suite is the interim shield;
/// the PROOF is the acceptance gate's byte/digest reproduction of the pinned
/// oracle verdicts.
#[allow(clippy::too_many_arguments)]
/// **THE ROUND'S FILE SET — ONE derivation, BOTH call sites.**
///
/// The per-round re-render, the bisect probes, and **the bisect's final
/// emission** must agree on which layer produced the program, because the
/// bisect ATTRIBUTES diagnostics to functions: probing a span-layer program to
/// explain a diagnostic observed on an AST-layer program compares against a
/// program that was never verified. That is not a variant, it is a defect — so
/// all three sites call this and none renders.
///
/// ⚠ **This doc said "both sites" and there were three** (corrected
/// 2026-08-18). The third — the final emission after bisect — called `render`
/// directly, so under `CRAT_M1_AST_EMIT` every escalating program emitted span
/// text while its probes ran on the AST layer. The count is not small: on the
/// corpus, 12 of 20 programs escalate.
///
/// The AST path returns **no rollbacks**, and that is structural rather than
/// optimistic: rollbacks are byte-offset collisions between edits applied to one
/// text, and a structural transform has no byte offsets to collide. The callers'
/// rollback branches are therefore unreachable on this path — recorded here
/// because "the check never fires" and "the check cannot fire" read identically
/// at the call site.
#[allow(clippy::too_many_arguments)]
fn round_files(
    tcx: TyCtxt<'_>,
    capture: &ast_transform::AstCapture,
    emission_plan: &plan::Plan,
    emission_texts: &std::collections::BTreeMap<plan::FileKey, String>,
    reverted: &std::collections::BTreeSet<bridge_receipt::SignatureClassId>,
    reverted_atoms: &std::collections::BTreeSet<String>,
    root_key: Option<&plan::FileKey>,
    table: &decision::DecisionTable,
) -> Result<
    (
        std::collections::BTreeMap<plan::FileKey, String>,
        Vec<apply::Rollback>,
        // **`files_touched`'s value — files with >=1 SURVIVING EDIT** (ruling
        // 2026-08-18), NOT the emission map's size. On the span layer the two
        // coincide because `render` returns only edited files; on the AST layer
        // they do not, because the map is seeded (see `SubstStats`).
        usize,
        // **I-31**: emitted→original line translation, per file, from whichever
        // splicer produced this round. `attribute` cannot key a diagnostic to a
        // function without it once the emitter reflows.
        std::collections::BTreeMap<plan::FileKey, apply::LineMap>,
    ),
    String,
> {
    let reverts =
        ast_transform::revert_set_from_classes_and_atoms(reverted, reverted_atoms, table)?;
    // **PER-FILE (A1, revived 2026-08-18).** The one-entry map that stood here
    // was licensed by C-20's corpus measurement — 20/20 single crate-source
    // file — and that measurement still holds. What it did not cover is the
    // verify loop's own end-to-end witnesses, which ARE multi-file, and which
    // it silently collapsed. The corpus emission is unchanged by this: a
    // single-file crate yields a single-entry map either way.
    let (files, stats, maps) =
        ast_transform::ast_emitted_files_from(tcx, capture, &reverts, root_key, table)?;
    Ok((files, Vec::new(), stats.files_with_edits, maps))
}

fn verify_and_revert(
    tcx: TyCtxt<'_>,
    capture: &ast_transform::AstCapture,
    table: &decision::DecisionTable,
    tree_base: Option<&std::path::Path>,
    virtual_original: Option<String>,
    max_rounds: usize,
    probe_only: bool,
    census_once: bool,
    raw_boundary_full: bool,
    files: std::collections::BTreeMap<plan::FileKey, String>,
    emission_plan: plan::Plan,
    emission_texts: std::collections::BTreeMap<plan::FileKey, String>,
    unplaceable: Vec<plan::Unplaceable>,
    degradations: Vec<decision::Degradation>,
    emitted_count: usize,
    root_text: String,
    emitted_sites: Vec<EmittedSite>,
    emitted_subjects: Vec<EmittedSubject>,
    a5_receipt: String,
    e1_subject_receipt: String,
    e2_artifacts: E2Artifacts,
    raw_boundary_artifacts: RawBoundaryArtifacts,
    e1_box_drop_policies: Vec<verify::BoxMirDropPolicy>,
) -> RewriteOutcome {
    // `excluded` is a LOCAL again: the loop holds `tcx`, so a value that used
    // to cross the boundary is simply computed here. One of the ten, retired.
    let excluded = decision::universe::classify(tcx).excluded;
    // Built ONCE. Every return below goes through `facts.emitted(..)`
    // or `facts.degraded(..)`; no site hand-fills a field.
    let site_owners = emitted_sites
        .iter()
        .map(|site| site.owner_class)
        .collect::<std::collections::BTreeSet<_>>();
    let attribution_blind = emission_plan
        .by_file
        .values()
        .flatten()
        .filter_map(|edit| edit.owner_class)
        .collect::<std::collections::BTreeSet<_>>()
        .difference(&site_owners)
        .count();
    let mut class_paths = std::collections::BTreeMap::new();
    for edit in emission_plan.by_file.values().flatten() {
        if let Some(class) = edit.owner_class {
            class_paths
                .entry(class)
                .or_insert_with(|| edit.owner_path.clone());
        }
    }
    for site in &emitted_sites {
        class_paths
            .entry(site.owner_class)
            .or_insert_with(|| site.fn_path.clone());
    }
    for subject in &emitted_subjects {
        class_paths
            .entry(subject.owner_class)
            .or_insert_with(|| subject.owner_path.clone());
    }
    // BASELINE-DIFFERENTIAL GATE. The gate judges what the REWRITE
    // introduced, not what the input already reported: brotli's frozen
    // source trips a deny-by-default lint unedited, which made
    // revert-all — the bisect base case — impossible to satisfy under an
    // absolute gate. Excluding lints wholesale would instead blind the
    // gate to rewrite-INTRODUCED violations of exactly our risk class
    // (reference casting), so the baseline is subtracted, not the class.
    // NOT COMPUTED HERE — see the loop, below the `probe_only` return.
    // `baseline_of` COMPILES the unmodified crate, and its diagnostics
    // are forwarded to the same stderr an instrument's consumer reads.
    // Computed on the instrument path it would be dead work (probe mode
    // returns before `novel` is ever consulted) whose only effect is to
    // contaminate that stderr with a second crate's diagnostics — which
    // is exactly what it did to brotli: 4 frozen-tree entries appeared
    // on the rendered side of a transfer that measures the temp copy.
    //
    // The placement is the enforcement. A predicate here would work
    // today and be one careless edit from unconditional again; below
    // the return, "gate machinery does not run on instrument paths"
    // holds by position.
    let compute_baseline = || match (tree_base, &virtual_original) {
        (Some(root), _) => verify::baseline_of(root),
        (None, Some(text)) => match verify::materialize_single_file(text) {
            Ok(staged) => verify::baseline_of(staged.root()),
            Err(_) => verify::Baseline::default(),
        },
        (None, None) => verify::Baseline::default(),
    };
    // **S3.6-1 task 2.** Built ONCE, from the same plan and texts every
    // revert round re-renders from, so attribution and rendering cannot
    // drift apart across rounds — the divergence class that cost a
    // brotli sweep when `candidates` and `emitted_sites` were derived
    // two different ways.
    // The round-0 emitted file — the key every later round re-emits into on the
    // AST path. Taken from the map production already built, never re-derived.
    let root_key: Option<plan::FileKey> = files.keys().next().cloned();
    // Round 0 comes from `emit_files`, which returns only files it edited, so
    // the seed is already the ruled definition.
    let mut files_edited = files.len();
    let planned_edit_sites = edit_sites(&emission_plan, &emission_texts);
    let nested_seam_composition = emission_plan.by_file.values().any(|edits| {
        edits
            .iter()
            .enumerate()
            .any(|(index, _)| nested_kind_under_seam(edits, index))
    });
    let e1_edit_contexts = if census_once {
        e1_edit_contexts(&emission_plan, &emission_texts)
    } else {
        Vec::new()
    };
    let mut baseline: Option<verify::Baseline> = None;
    let mut facts = OutcomeFacts {
        degradations,
        excluded,
        emitted_count,
        files_touched: files_edited,
        reverted_count: 0,
        emitted_sites,
        unplaceable,
        bisect_probes: 0,
        verify_rounds: 0,
        escalated: None,
        attribution_blind,
        first_diags: Vec::new(),
        observed_root: None,
        // Filled below, on the gate path, when the baseline is
        // actually computed. Probe mode HAS no baseline — its payload
        // is the raw capture — so zero here is "not applicable in this
        // mode", not a measured value that was zeroed.
        baseline_keys: 0,
        baseline_errors: 0,
        baseline_msg_env: 0,
        a5_receipt,
        e1_reverts: Vec::new(),
        e1_adapter_receipt: if census_once {
            seam_tsv_from_table(tcx, table)
        } else {
            String::new()
        },
        e1_subject_receipt,
        e2_artifacts,
        raw_boundary_artifacts,
        e1_novel_error_count: 0,
        e1_box_drop_receipt: String::new(),
        solve_receipt: model_cache::solve_receipt(),
    };
    facts.raw_boundary_artifacts.edit_keys = {
        let mut keys = planned_edit_sites
            .iter()
            .map(|edit| edit.edit_id.clone())
            .collect::<Vec<_>>();
        keys.sort();
        keys.dedup();
        let mut out = String::from("edit_key\n");
        for key in keys {
            out.push_str(&key);
            out.push('\n');
        }
        out
    };
    let crate_dir = tree_base
        .and_then(|root| root.parent())
        .map(|d| d.to_path_buf());
    let mut reverted: std::collections::BTreeSet<bridge_receipt::SignatureClassId> =
        std::collections::BTreeSet::new();
    let mut reverted_atoms: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut atom_reverify_count = 0usize;
    let mut pending_atom_retry: Option<(String, Vec<String>)> = None;
    let mut census_captured = false;
    // **ROUND 0 THROUGH THE SWITCH — the FOURTH site** (ruling 2026-08-18).
    //
    // `files` arrives from `emit_files`, whose product is `render`'s: the SPAN
    // layer, unconditionally. The loop's first act is to materialize it, so
    // until a revert occurred nothing switched — and a program that converges
    // with ZERO reverts returns this map unchanged. On the corpus that is **7
    // programs and 35 of the 64 emissions**, every one of them emitting span
    // text while the AST arm reported agreement, because the three counters
    // cannot see text. libcsv is the measured witness: 50,440 bytes on the AST
    // layer against 55,764 on the span layer, same converged (empty) revert
    // set, identical counters.
    //
    // Re-emitting round 0 here puts every exit shape behind the one derivation.
    // The incoming `files` is still what `root_key` is taken from and what the
    // pre-loop rollback gate judged — that gate validates the PLAN (byte-offset
    // collisions), which is layer-independent, so it keeps its meaning.
    let ast_started = std::time::Instant::now();
    let (mut files, mut files_edited, mut line_maps) = match round_files(
        tcx,
        capture,
        &emission_plan,
        &emission_texts,
        &std::collections::BTreeSet::new(),
        &std::collections::BTreeSet::new(),
        root_key.as_ref(),
        table,
    ) {
        Ok((round0, rollbacks, edited, maps)) => {
            if !rollbacks.is_empty() {
                // The pre-loop structural gate already rejected a non-empty
                // rollback set for this plan, so this is a DISAGREEMENT between
                // the two, not a plan defect — loud, never silent.
                facts.files_touched = files_edited;
                return facts.degraded(format!(
                    "round-0 re-emit produced {} rollback(s) after the                      structural gate accepted the plan",
                    rollbacks.len()
                ));
            }
            (round0, edited, maps)
        }
        Err(why) => {
            facts.files_touched = files_edited;
            return facts.degraded(format!("round-0 emit failed: {why}"));
        }
    };
    facts.e2_artifacts.timings.ast_placement_wall_s =
        format!("{:.6}", ast_started.elapsed().as_secs_f64());
    facts.files_touched = files_edited;
    let mut rounds = 0usize;
    let mut previous_errors: Option<usize> = None;
    let mut probe_secs = 0.0f64;
    let escalation: Option<String>;

    loop {
        let materialized = match tree_base {
            Some(root) => verify::materialize(root, &files),
            // String fixtures use the SAME AST round product as file-backed
            // production. `root_text` is only the no-edit fallback; selecting it
            // unconditionally here bypassed the use→seam composition the round
            // had just built and made the test entry a second emitter.
            None if nested_seam_composition => verify::materialize_single_file(
                files
                    .values()
                    .next()
                    .map_or(root_text.as_str(), String::as_str),
            ),
            None => verify::materialize_single_file(&root_text),
        };
        let staged = match materialized {
            Ok(staged) => staged,
            Err(err) => {
                facts.files_touched = files_edited;
                facts.reverted_count = reverted.len();
                return facts.degraded(format!("could not materialize the emitted crate: {err}"));
            }
        };
        let probe_started = std::time::Instant::now();
        facts.verify_rounds += 1;
        let diagnosis = verify::diagnose_crate(staged.root());
        let probe_wall_s = probe_started.elapsed().as_secs_f64();
        if atom_reverify_count > 0 {
            facts.raw_boundary_artifacts.timings.atom_reverify_wall_s =
                format!("{probe_wall_s:.6}");
        } else if facts.raw_boundary_artifacts.timings.initial_verify_wall_s == "pending" {
            facts.raw_boundary_artifacts.timings.initial_verify_wall_s =
                format!("{probe_wall_s:.6}");
        }
        probe_secs = probe_secs.max(probe_wall_s);
        if census_once && !census_captured {
            facts.e2_artifacts.timings.compiler_verification_wall_s = format!("{probe_wall_s:.6}");
        }
        if probe_only {
            // INSTRUMENTS MEASURE THE CAPTURE; GATES CONSUME THE
            // FILTERED VIEW. The probe payload is the RAW diagnosis and
            // gets its own assignment statement here, above the early
            // return; the gate's baseline-subtracted `novel` is assigned
            // separately below. The two never share an assignment site
            // again.
            //
            // This is not a style preference. The payloads were shared
            // once: the differential gate rewrote the single assignment
            // to `novel`, which needs a root and a baseline, so it had
            // to move BELOW this return — and the return did not move
            // with it. `diagnose_once` then returned empty and
            // `run_m1_diag` reported `struct_diags=0 status=ok` for
            // every program, a zeroed payload wearing an ok status.
            //
            // Raw is also the SEMANTICALLY required payload, not merely
            // the restored one: the transfer harness compares these
            // against the child's unfiltered stderr, so subtracting a
            // baseline from one side of that comparison would bias it.
            // Baseline diagnostics appear on both sides, which is what
            // makes the equality mean anything.
            facts.first_diags = diagnosis.diags.clone();
            facts.observed_root = Some(
                staged
                    .root()
                    .parent()
                    .unwrap_or(staged.root())
                    .to_path_buf(),
            );
            facts.files_touched = files_edited;
            return facts.degraded("probe-only: first diagnose recorded".to_owned());
        }
        // GATE MACHINERY STARTS HERE. Everything below the probe
        // return belongs to the differential; the baseline compile is
        // the first of it, computed once and reused across rounds.
        let baseline = baseline.get_or_insert_with(|| compute_baseline());
        facts.baseline_keys = baseline.keys.values().sum();
        facts.baseline_errors = baseline.errors;
        facts.baseline_msg_env = baseline.messages_embedding_root;
        let observed_root = staged
            .root()
            .parent()
            .unwrap_or(staged.root())
            .to_path_buf();
        let novel: Vec<verify::Diag> = baseline
            .novel(&diagnosis.diags, &observed_root)
            .into_iter()
            .cloned()
            .collect();
        let novel_errors = diagnosis.errors.saturating_sub(baseline.errors);
        if facts.first_diags.is_empty() {
            facts.first_diags = novel.clone();
            facts.observed_root = Some(observed_root.clone());
        }
        if census_once && !census_captured {
            census_captured = true;
            facts.first_diags = novel.clone();
            facts.observed_root = Some(observed_root.clone());
            facts.e1_novel_error_count = novel_errors;
            facts.e1_box_drop_receipt =
                match verify::box_mir_drops_path(staged.root(), &e1_box_drop_policies) {
                    Ok(mut drops) => {
                        drops.retain(|drop| {
                            e1_box_drop_policies.iter().any(|policy| {
                                policy.function == drop.function
                                    && policy.local_name == drop.local_name
                            })
                        });
                        match verify::reconcile_box_mir_drop_policies(&drops, &e1_box_drop_policies)
                        {
                            Ok(tsv) => {
                                format!("status=ok\ndata=provisional\nrows={}\n{tsv}", drops.len())
                            }
                            Err(error) => format!(
                                "status=error\ndata=false\ndetail={}\n",
                                error.replace(['\t', '\r', '\n'], " ")
                            ),
                        }
                    }
                    Err(error) => format!(
                        "status=error\ndata=false\ndetail={}\n",
                        error.replace(['\t', '\r', '\n'], " ")
                    ),
                };
            for diagnostic in &novel {
                let mut owners = attribute(
                    std::slice::from_ref(diagnostic),
                    &line_maps,
                    &observed_root,
                    &facts.emitted_sites,
                    &planned_edit_sites,
                    &reverted,
                    crate_dir.as_deref().unwrap_or(std::path::Path::new("")),
                );
                let mut attribution = "standard";
                if owners.is_empty() {
                    let original_root = crate_dir.as_deref().unwrap_or(std::path::Path::new(""));
                    if let Some(original_line) =
                        e1_bijective_line(diagnostic, &line_maps, &observed_root, original_root)
                    {
                        let mut remapped = diagnostic.clone();
                        remapped.line = original_line;
                        owners = attribute(
                            std::slice::from_ref(&remapped),
                            &std::collections::BTreeMap::new(),
                            &observed_root,
                            &facts.emitted_sites,
                            &planned_edit_sites,
                            &reverted,
                            original_root,
                        );
                        if !owners.is_empty() {
                            attribution = "equal-line-segment";
                        }
                    }
                }
                if owners.is_empty() {
                    let original_root = crate_dir.as_deref().unwrap_or(std::path::Path::new(""));
                    for related in &diagnostic.related {
                        let mut related_diagnostic = verify::Diag {
                            file: related.file.clone(),
                            line: related.line,
                            message: related.message.clone(),
                            direction: verify::Direction::Other,
                            code: diagnostic.code.clone(),
                            related: Vec::new(),
                        };
                        let mut related_owners = attribute(
                            std::slice::from_ref(&related_diagnostic),
                            &line_maps,
                            &observed_root,
                            &facts.emitted_sites,
                            &planned_edit_sites,
                            &reverted,
                            original_root,
                        );
                        if related_owners.is_empty()
                            && let Some(original_line) = e1_bijective_line(
                                &related_diagnostic,
                                &line_maps,
                                &observed_root,
                                original_root,
                            )
                        {
                            related_diagnostic.line = original_line;
                            related_owners = attribute(
                                std::slice::from_ref(&related_diagnostic),
                                &std::collections::BTreeMap::new(),
                                &observed_root,
                                &facts.emitted_sites,
                                &planned_edit_sites,
                                &reverted,
                                original_root,
                            );
                        }
                        if related_owners.is_empty() {
                            related_owners = e1_region_owners(
                                &related_diagnostic,
                                &line_maps,
                                &observed_root,
                                original_root,
                                &facts.emitted_sites,
                                &planned_edit_sites,
                            );
                        }
                        owners.extend(related_owners);
                    }
                    if !owners.is_empty() {
                        attribution = "related-span";
                    }
                }
                if owners.is_empty() {
                    let original_root = crate_dir.as_deref().unwrap_or(std::path::Path::new(""));
                    owners = e1_region_owners(
                        diagnostic,
                        &line_maps,
                        &observed_root,
                        original_root,
                        &facts.emitted_sites,
                        &planned_edit_sites,
                    );
                    if !owners.is_empty() {
                        attribution = "region-span";
                    }
                }
                if owners.is_empty() {
                    facts.e1_reverts.push(E1RevertDiagnostic {
                        function: "<unattributed>".to_owned(),
                        diagnostic: diagnostic.clone(),
                        site_kind: e1_diagnostic_site(diagnostic),
                        attribution: "unattributed".to_owned(),
                        edits: Vec::new(),
                    });
                    continue;
                }
                for owner in owners {
                    let edits = e1_edit_contexts
                        .iter()
                        .filter(|(candidate, _, _)| *candidate == owner)
                        .map(|(_, _, edit)| edit.clone())
                        .collect();
                    facts.e1_reverts.push(E1RevertDiagnostic {
                        function: class_paths
                            .get(&owner)
                            .cloned()
                            .unwrap_or_else(|| format!("local-def-index:{}", owner.order_key())),
                        diagnostic: diagnostic.clone(),
                        site_kind: e1_diagnostic_site(diagnostic),
                        attribution: attribution.to_owned(),
                        edits,
                    });
                }
            }
            if novel_errors > 0 && facts.e1_reverts.is_empty() {
                facts.e1_reverts.push(E1RevertDiagnostic {
                    function: "<unattributed>".to_owned(),
                    diagnostic: verify::Diag {
                        file: "<spanless>".to_owned(),
                        line: 0,
                        message: format!(
                            "{novel_errors} baseline-subtracted error(s) carried no located diagnostic"
                        ),
                        direction: verify::Direction::Other,
                        code: None,
                        related: Vec::new(),
                    },
                    site_kind: E1DiagnosticSite::Other,
                    attribution: "spanless".to_owned(),
                    edits: Vec::new(),
                });
            }
            facts.files_touched = files_edited;
            if !raw_boundary_full {
                return facts.degraded(
                    "e1-single-iteration: first differential diagnose recorded".to_owned(),
                );
            }
        }
        if novel.is_empty() && novel_errors == 0 {
            if let Some((reason, atoms)) = pending_atom_retry.take() {
                facts
                    .raw_boundary_artifacts
                    .atom_outcomes
                    .push_str(&format!(
                        "atom-succeeded\t{}\t{}\n",
                        reason,
                        atoms.join(";")
                    ));
            }
            let source = std::fs::read_to_string(staged.root()).unwrap_or_default();
            let (kept, taken): (Vec<_>, Vec<_>) = emitted_subjects.iter().partition(|subject| {
                !reverted.contains(&subject.owner_class)
                    && subject
                        .atoms
                        .iter()
                        .all(|atom| !reverted_atoms.contains(atom))
            });
            // ACCOUNTING: a reverted subject moves from emitted to
            // degraded under its OWN reason key, so
            // `emitted_final + degraded == row count` survives the loop.
            for subject in &taken {
                facts.degradations.push(decision::Degradation {
                    subject: subject.subject.clone(),
                    site: subject.site.clone(),
                    reason: decision::DegradeReason::RevertedAfterVerifyFailure,
                });
            }
            facts.emitted_count = kept.len();
            facts.reverted_count = taken.len();
            facts.files_touched = files_edited;
            facts.raw_boundary_artifacts.final_reverts =
                render_raw_boundary_final_reverts(&reverted, &reverted_atoms, &class_paths);
            return facts.emitted(source, files);
        }

        // Raw-boundary subject-atom pass: exactly one compiler reverify. The
        // edit-span index is filtered by the same function/atom predicates as
        // rendering before attribution, so a removed atom cannot be selected
        // again through stale plan metadata.
        if atom_reverify_count < MAX_ATOM_REVERIFIES {
            let live_atom_sites = planned_edit_sites
                .iter()
                .filter(|edit| {
                    edit.owner_class
                        .is_some_and(|class| !reverted.contains(&class))
                        && edit
                            .atom_ids
                            .iter()
                            .all(|atom| !reverted_atoms.contains(atom))
                })
                .cloned()
                .collect::<Vec<_>>();
            let selection = select_subject_atoms(
                &novel,
                &line_maps,
                &observed_root,
                &live_atom_sites,
                crate_dir.as_deref().unwrap_or(std::path::Path::new("")),
            );
            if matches!(
                selection.kind,
                AtomSelectionKind::Exact
                    | AtomSelectionKind::GroupAtomic
                    | AtomSelectionKind::BisectGroup
            ) {
                atom_reverify_count += 1;
                let selected_atoms = selection.atoms.into_iter().collect::<Vec<_>>();
                reverted_atoms.extend(selected_atoms.iter().cloned());
                pending_atom_retry = Some((selection.reason.to_owned(), selected_atoms));
                let (next_files, rollbacks, next_edited, next_maps) = match round_files(
                    tcx,
                    capture,
                    &emission_plan,
                    &emission_texts,
                    &reverted,
                    &reverted_atoms,
                    root_key.as_ref(),
                    table,
                ) {
                    Ok(quad) => quad,
                    Err(why) => {
                        escalation =
                            Some(format!("escalation-required: atom re-emit failed: {why}"));
                        break;
                    }
                };
                if !rollbacks.is_empty() {
                    escalation = Some(format!(
                        "escalation-required: atom re-render rolled back {} edit(s)",
                        rollbacks.len()
                    ));
                    break;
                }
                files = next_files;
                files_edited = next_edited;
                line_maps = next_maps;
                // The atom retry is its own bounded phase; its result must be
                // allowed to fall through to ordinary function attribution
                // rather than tripping the general no-progress detector.
                previous_errors = None;
                continue;
            }
            if !live_atom_sites.is_empty() {
                facts
                    .raw_boundary_artifacts
                    .atom_outcomes
                    .push_str(&format!(
                        "atom-ambiguous-fallback\t{}\t-\n",
                        selection.reason
                    ));
            }
        } else if let Some((reason, atoms)) = pending_atom_retry.take() {
            facts
                .raw_boundary_artifacts
                .atom_outcomes
                .push_str(&format!(
                    "atom-second-verify-fallback\t{}\t{}\n",
                    reason,
                    atoms.join(";")
                ));
        }

        // DUAL TERMINATION, both arms. Neither alone: a no-progress
        // detector can be starved by a loop that keeps finding new
        // attributions, and a cap alone burns every round on a case
        // that stopped improving after the first.
        let outstanding = novel.len().max(novel_errors);
        if previous_errors.is_some_and(|prev| outstanding >= prev) {
            escalation = Some(format!(
                "escalation-required: no progress ({} error(s) after \
                 reverting {} function(s)) — attribution is wrong here \
                 and (C) bisect must take over",
                outstanding,
                reverted.len()
            ));
            break;
        }
        previous_errors = Some(outstanding);
        rounds += 1;
        if rounds > max_rounds {
            escalation = Some(format!(
                "escalation-required: round cap {max_rounds} reached with \
                 {} error(s) outstanding",
                outstanding
            ));
            break;
        }

        let newly = attribute(
            &novel,
            // The map of the round whose program produced these diagnostics.
            &line_maps,
            &observed_root,
            &facts.emitted_sites,
            &planned_edit_sites,
            &reverted,
            crate_dir.as_deref().unwrap_or(std::path::Path::new("")),
        )
        .difference(&reverted)
        .cloned()
        .collect::<std::collections::BTreeSet<_>>();
        if newly.is_empty() {
            escalation = Some(format!(
                "escalation-required: {} error(s) attributed to no rewritten \
                 function",
                outstanding
            ));
            break;
        }
        // BATCH revert: the union of this round's attributions, not one
        // at a time — one compile per round rather than one per function.
        reverted.extend(newly);
        let (next_files, rollbacks, next_edited, next_maps) = match round_files(
            tcx,
            capture,
            &emission_plan,
            &emission_texts,
            &reverted,
            &reverted_atoms,
            root_key.as_ref(),
            table,
        ) {
            Ok(quad) => quad,
            Err(why) => {
                escalation = Some(format!("escalation-required: re-emit failed: {why}"));
                break;
            }
        };
        if !rollbacks.is_empty() {
            escalation = Some(format!(
                "escalation-required: re-render rolled back {} edit(s)",
                rollbacks.len()
            ));
            break;
        }
        files = next_files;
        files_edited = next_edited;
        line_maps = next_maps;
    }

    // ---- (C) BISECT: the escalation path ----
    // Reaching here means the loop BROKE, and only the gate path can
    // break: probe mode returns from inside it. So the baseline exists
    // by construction — and it is asserted rather than defaulted,
    // because a `Baseline::default()` fallback here would silently turn
    // the differential into an absolute gate, which is the exact defect
    // brotli's frozen source exposed in the first place.
    let baseline = baseline.expect(
        "the gate path computes a baseline on its first round; reaching \
         the post-loop stages without one means the loop was exited by a \
         path that skipped it",
    );

    let escalation = escalation.unwrap_or_else(|| "escalation-required".to_owned());
    // Candidates come from the PLAN's `owner_fn` domain — the exact key
    // `render` filters on — so `base ∪ candidates` drops EVERY edit and
    // the base case (revert-all compiles) holds BY CONSTRUCTION.
    //
    // They were previously derived from `emitted_sites`, a DIFFERENT
    // derivation: it skips a subject whose enclosing function's span has
    // no editable file identity, while the edit is keyed on the
    // subject's own `ty_span`. brotli found the divergence (2026-07-31):
    // reverting every candidate left edits standing, the crate still
    // failed, and bisect returned a non-compiling set. Two derivations
    // assumed identical — the founding class.
    let candidates: Vec<bridge_receipt::SignatureClassId> = emission_plan
        .by_file
        .values()
        .flatten()
        .filter_map(|edit| edit.owner_class)
        .filter(|owner| !reverted.contains(owner))
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect();

    // ESCALATION BUDGET. A bisect that cannot finish inside the worker
    // budget is DEFERRED LOUDLY with its attribution state, never
    // silently truncated — a truncated bisect returns a wrong answer
    // that looks like a right one.
    let projected = (candidates.len() + 1).next_power_of_two().trailing_zeros() as f64;
    let budget_secs = std::env::var("CRAT_BOC1_EMIT_TIMEOUT_SECS")
        .ok()
        .and_then(|v| v.parse::<f64>().ok())
        .unwrap_or(900.0);
    if projected * probe_secs > budget_secs {
        facts.files_touched = files_edited;
        facts.reverted_count = reverted.len();
        facts.escalated = Some(escalation.clone());
        return facts.degraded(format!(
            "escalation-deferred: {escalation}; bisect needs ~{projected} probe(s)                          at ~{probe_secs:.1}s each against a {budget_secs:.0}s budget, with                          {} function(s) already reverted",
            reverted.len()
        ));
    }

    let (final_reverted, probes) = bisect(&candidates, &reverted, |trial| {
        let Ok((trial_files, rollbacks, _, _)) = round_files(
            tcx,
            capture,
            &emission_plan,
            &emission_texts,
            trial,
            &reverted_atoms,
            root_key.as_ref(),
            table,
        ) else {
            return false;
        };
        if !rollbacks.is_empty() {
            return false;
        }
        let materialized = match tree_base {
            Some(root) => verify::materialize(root, &trial_files),
            None => verify::materialize_single_file(&root_text),
        };
        let Ok(staged) = materialized else {
            return false;
        };
        let probe = verify::diagnose_crate(staged.root());
        let probe_root = staged.root().parent().unwrap_or(staged.root());
        baseline.novel(&probe.diags, probe_root).is_empty()
            && probe.errors.saturating_sub(baseline.errors) == 0
    });

    // **THE THIRD SITE — routed through `round_files` like the other two**
    // (ruling 2026-08-18). This called `render` directly, with no layer
    // switch, so under `CRAT_M1_AST_EMIT` every program that escalated
    // emitted SPAN text: the bisect PROBES above ran on the selected layer
    // and the emission that followed did not. That is precisely the defect
    // `round_files`' own doc names — a program returned that is not the
    // program the probes verified — and it also left M-3 with an escalation
    // path that has no implementation once `render` is deleted.
    let (final_files, rollbacks, final_edited, _final_maps) = match round_files(
        tcx,
        capture,
        &emission_plan,
        &emission_texts,
        &final_reverted,
        &reverted_atoms,
        root_key.as_ref(),
        table,
    ) {
        Ok(quad) => quad,
        Err(why) => {
            // The bisect already found a compiling set; failing to re-emit it
            // is a loud degrade, never a silent fall back to the other layer.
            facts.files_touched = files_edited;
            facts.reverted_count = final_reverted.len();
            facts.bisect_probes = probes;
            facts.escalated = Some(escalation.clone());
            return facts.degraded(format!("{escalation}; final re-emit failed: {why}"));
        }
    };
    let materialized = match tree_base {
        Some(root) => verify::materialize(root, &final_files),
        None => verify::materialize_single_file(&root_text),
    };
    // INCIDENT-PROVEN DEFENSE — not a control over an unreachable case.
    //
    // `type_checks_crate` here can never be the thing that fails:
    // `bisect` only ever assigns `hi` a `mid` it just tested true, so
    // the returned `k` either compiled under test or equals
    // `candidates.len()` — reverting every owner, which drops every
    // edit and reduces the crate to the original input. The input
    // compiled, or `decide_table` would not have produced a table.
    // Non-monotonicity costs MINIMALITY, never correctness.
    //
    // `rollbacks` likewise cannot fire here: `render` applies a SUBSET
    // of the edits that produced no rollbacks initially, and dropping
    // edits cannot create an overlap, an out-of-bounds range, or a
    // char-boundary violation.
    //
    // **This guard FIRED on brotli, 2026-07-31**, when `candidates` was
    // derived from `emitted_sites` rather than from the plan's
    // `owner_fn` domain: the two sets diverged, revert-all left edits
    // standing, and bisect returned a set that did not compile. The
    // derivation is fixed above; the guard stays because it is what
    // turned a silently wrong emission into a loud `Degraded`.
    //
    // The `rollbacks` arm remains unreachable (a SUBSET of edits that
    // produced no rollbacks cannot produce new ones); the reachable
    // rollback path is the pre-loop structural gate, witnessed there.
    match materialized {
        Ok(staged)
            if rollbacks.is_empty() && {
                facts.verify_rounds += 1;
                let final_diag = verify::diagnose_crate(staged.root());
                let final_root = staged.root().parent().unwrap_or(staged.root());
                baseline.novel(&final_diag.diags, final_root).is_empty()
                    && final_diag.errors.saturating_sub(baseline.errors) == 0
            } =>
        {
            let source = std::fs::read_to_string(staged.root()).unwrap_or_default();
            let (kept, taken): (Vec<_>, Vec<_>) = emitted_subjects.iter().partition(|subject| {
                !final_reverted.contains(&subject.owner_class)
                    && subject
                        .atoms
                        .iter()
                        .all(|atom| !reverted_atoms.contains(atom))
            });
            for subject in &taken {
                facts.degradations.push(decision::Degradation {
                    subject: subject.subject.clone(),
                    site: subject.site.clone(),
                    reason: decision::DegradeReason::RevertedAfterVerifyFailure,
                });
            }
            facts.emitted_count = kept.len();
            facts.reverted_count = taken.len();
            // The RULED value from the same derivation the other exits use —
            // not the map size, which is seeded on the AST layer.
            facts.files_touched = final_edited;
            facts.bisect_probes = probes;
            facts.escalated = Some(escalation);
            facts.raw_boundary_artifacts.final_reverts =
                render_raw_boundary_final_reverts(&final_reverted, &reverted_atoms, &class_paths);
            facts.emitted(source, final_files)
        }
        _ => {
            facts.files_touched = files_edited;
            facts.reverted_count = final_reverted.len();
            facts.bisect_probes = probes;
            facts.escalated = Some(escalation.clone());
            facts.degraded(format!("{escalation}; bisect did not recover the crate"))
        }
    }
}

/// Every top-level fn/struct item, in HIR owner order (the `bo_c1` shape).
fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = Vec::new();
    let mut structs = Vec::new();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }
    RustProgram {
        tcx,
        functions,
        structs,
    }
}

/// M1 subjects: each pointer-typed parameter of each local function, decided on
/// the **resolved** type.
///
/// # Why resolved, not syntactic (R-A)
///
/// The previous collector matched `rustc_hir::TyKind::Ptr` on the syntactic HIR
/// type node. A C2Rust type alias — `pub type lil_value_t = *mut _lil_value_t`
/// — lowers to `TyKind::Path`, so a parameter declared `val: lil_value_t` was
/// not a subject at all: BO decided it (MIR types are resolved) and the
/// rewriter discarded that decision with no `Decision`, no `Degradation`, no
/// site and no reason. That is the "unrewritten and unattributed" class the
/// whole A1 layer exists to retire, and it is present in the evaluation corpus.
///
/// The predicate is now [`ptr_chain_depth`] over `tcx.fn_sig`'s inputs — the
/// same in-tree function `CrateSlots` builds the slot universe from. **HIR
/// supplies where, tcx supplies whether:** the plan edits source bytes, so the
/// declaration span and the pointee span still come from HIR.
///
/// R-A rules these subjects **collected, not excluded** — they are real C
/// pointer parameters. Whether each *emits* is A1's per-subject decision like
/// any other, and the alias-specific emission obstacle (the alias already
/// contains the `*mut`, so there is no pointee text to copy) degrades with its
/// own attributed reason in [`decision::decide_one`].
///
/// The MIR local of parameter `i` is `_{i+1}` — params occupy `_1 ..= arg_count`
/// — which is what lets a HIR-side span pair with a MIR-side slot lookup. That
/// mapping is what [`decision::coverage`]'s fail-loud arm guards.
fn collect_subjects(
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    mut_facts: &MutFacts,
) -> Vec<decision::Subject> {
    let mut subjects = Vec::new();
    for &fn_did in &program.functions {
        let node = tcx.hir_node_by_def_id(fn_did);
        let (Some(decl), Some(body_id)) = (node.fn_decl(), node.body_id()) else {
            continue;
        };
        let body = tcx.hir_body(body_id);
        let fn_name = tcx.item_name(fn_did.to_def_id());
        let sig = tcx.fn_sig(fn_did).skip_binder().skip_binder();
        for (index, param_ty) in sig.inputs().iter().enumerate() {
            if ptr_chain_depth(*param_ty) == 0 {
                continue;
            }
            // F3: these used to `continue`, dropping the subject from BOTH the
            // table and the count it was checked against — a double-sided drop
            // no self-comparison could see. A mismatch here is a collector bug
            // rather than a degradation, so it fails loudly instead of
            // shrinking the work silently.
            let Some(input) = decl.inputs.get(index) else {
                panic!(
                    "resolved signature of {fn_did:?} has input {index} but the HIR \
                     declaration has only {} — parameter mapping broken",
                    decl.inputs.len()
                );
            };
            // The parameter's BINDING, so a use can be attributed to it without
            // relying on a name that might be shadowed in an inner scope.
            let Some(param) = body.params.get(index) else {
                panic!(
                    "HIR fn_decl has input {index} but the body has no matching \
                     param binding for {fn_did:?} — collector invariant broken"
                );
            };
            let (decl_shape, pointee_span) = match input.kind {
                rustc_hir::TyKind::Ptr(mut_ty) => {
                    (decision::DeclShape::RawPtr, Some(mut_ty.ty.span))
                }
                rustc_hir::TyKind::Ref(_, mut_ty) => {
                    (decision::DeclShape::Reference, Some(mut_ty.ty.span))
                }
                rustc_hir::TyKind::Path(_) => (decision::DeclShape::Alias, None),
                _ => (decision::DeclShape::Other, None),
            };
            let local = Local::from_usize(index + 1);
            let name = param_name(param);
            subjects.push(decision::Subject {
                fn_did,
                local,
                hir_id: param.pat.hir_id,
                param_name: name.clone(),
                kind: decision::SubjectKind::Param { hir_index: index },
                ptr_depth: ptr_chain_depth(*param_ty),
                label: format!("{fn_name}::{}", name.as_deref().unwrap_or("<pattern>")),
                ty_span: Some(input.span),
                binding_span: param.pat.span,
                pointee_span,
                decl_shape,
                // The declared mutability is a ceiling, not the decision: BO's
                // mutability facts decide whether a `&mut` is warranted. Read
                // off the RESOLVED type so it sees through an alias exactly as
                // the pointer predicate above does.
                mutable: matches!(
                    param_ty.kind(),
                    TyKind::RawPtr(_, Mutability::Mut) | TyKind::Ref(_, _, Mutability::Mut)
                ) && mut_facts.is_mutable(fn_did, local),
                // Stamped in `finish_decide`, once, over both universes.
                freed_at: None,
                len_recovered: false,
                null_init: false,
                mut_binding: false,
                ctor: None,
            });
        }
    }
    subjects
}

/// M1 subjects, second universe: each **named pointer local** of each local
/// function (S3.1).
///
/// # The universe rule — depth + named binding, and nothing else
///
/// A local is a subject iff its type has pointer depth > 0 **and** at least one
/// `var_debug_info` entry keys to it. There is deliberately **no third
/// condition**: a local BO has no slot for is collected and *degraded with a
/// reason*, never omitted. The rule is structurally identical to the reference
/// walker's, and that identity of shape is what makes a producer-B-only row a
/// clean signal instead of an expected difference.
///
/// **Zero entries is the universe exclusion**, and it is what keeps MIR
/// temporaries out: measured, the `*mut c_void` a `malloc` call lands in carries
/// no debug entry at all, while being a depth-1 pointer. Depth alone would
/// admit it, and it has no source binding anyone could rewrite.
///
/// # Mapping a MIR local back to its declaration
///
/// The `var_debug_info` entry's span **is** the HIR binding pattern's span —
/// measured on this toolchain, `mut` included (`let mut p` reports `4:9:4:14` on
/// both sides). So a map from simple-binding `let` pattern spans to their type
/// annotation resolves the declaration exactly, without a name lookup that
/// shadowing would break.
///
/// A local not found in that map has no declared type of its own: it is either
/// unannotated, or a component of a destructuring pattern whose annotation
/// belongs to the pattern. Both carry `ty_span: None`, which means the plan
/// phase has no splice target — but **not** that nothing is known about the
/// declaration: the SHAPE still comes from the resolved type, and the
/// dissolution pass reads it there.
fn collect_local_subjects(
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    mut_facts: &MutFacts,
) -> Vec<decision::Subject> {
    use rustc_hir::intravisit::Visitor;

    /// Two maps over the same body, with **deliberately different predicates**.
    ///
    /// They are not merged into one entry, and must not be: they answer
    /// different questions and their correct domains differ.
    ///
    /// - [`Self::by_pat_span`] — *what type was DECLARED here.* Simple-binding
    ///   `let`s only, because a destructuring pattern's annotation belongs to
    ///   the pattern and not to any component.
    /// - [`Self::binding_hir`] — *which HIR binding IS this.* **Every** binding
    ///   pattern, wherever it appears: destructuring components, `match` arms,
    ///   `for` bindings. A binding has an identity even where it has no
    ///   annotation of its own.
    ///
    /// Merging them would silently narrow the identity map to simple `let`s and
    /// leave every other binding unattributable — the same shape of defect as
    /// the placeholder this slice repairs, one level down.
    struct Lets<'hir> {
        by_pat_span: rustc_hash::FxHashMap<rustc_span::Span, Option<&'hir rustc_hir::Ty<'hir>>>,
        binding_hir: rustc_hash::FxHashMap<rustc_span::Span, rustc_hir::HirId>,
    }
    impl<'hir> Visitor<'hir> for Lets<'hir> {
        fn visit_stmt(&mut self, stmt: &'hir rustc_hir::Stmt<'hir>) {
            if let rustc_hir::StmtKind::Let(local) = stmt.kind
                && matches!(local.pat.kind, rustc_hir::PatKind::Binding(..))
            {
                // Only SIMPLE bindings: a destructuring pattern's annotation is
                // the pattern's, not any component's, so recording it here would
                // hand a component a type it does not have.
                self.by_pat_span.insert(local.pat.span, local.ty);
            }
            rustc_hir::intravisit::walk_stmt(self, stmt);
        }

        fn visit_pat(&mut self, pat: &'hir rustc_hir::Pat<'hir>) {
            // `hir_id` here is exactly the id `Res::Local` resolves a *use* to,
            // which is what makes the A1 emitability lookup hit. S3.1 shipped a
            // `CRATE_HIR_ID` placeholder instead, and both gates were dead over
            // every local as a result.
            if let rustc_hir::PatKind::Binding(..) = pat.kind {
                self.binding_hir.insert(pat.span, pat.hir_id);
            }
            rustc_hir::intravisit::walk_pat(self, pat);
        }
    }

    let mut subjects = Vec::new();
    for &fn_did in &program.functions {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let mut lets = Lets {
            by_pat_span: rustc_hash::FxHashMap::default(),
            binding_hir: rustc_hash::FxHashMap::default(),
        };
        lets.visit_body(tcx.hir_body(body_id));

        let mir = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        let fn_name = tcx.item_name(fn_did.to_def_id());

        // Entries per local, so the one-vs-more split is a count and not a
        // first-match. Deterministic order: BTreeMap keyed by local index.
        let mut entries: std::collections::BTreeMap<
            Local,
            Vec<&rustc_middle::mir::VarDebugInfo<'_>>,
        > = std::collections::BTreeMap::new();
        for info in &mir.var_debug_info {
            if let rustc_middle::mir::VarDebugInfoContents::Place(place) = info.value
                && let Some(local) = place.as_local()
            {
                entries.entry(local).or_default().push(info);
            }
        }

        for (local, infos) in entries {
            // Locals are `_(arg_count + 1) ..`; `_0` is the return place and
            // `_1 ..= arg_count` is the parameter universe. Stated as a bound on
            // the local rather than as "not a parameter", so the two universes
            // are disjoint by construction rather than by filtering.
            if local.index() <= mir.arg_count {
                continue;
            }
            let ty = mir.local_decls[local].ty;
            if ptr_chain_depth(ty) == 0 {
                continue;
            }
            // The contradiction case: `argument_index` is set only on parameter
            // locals. One here would mean the toolchain changed what it means,
            // and reclassifying silently would hide that. Measured across plain
            // locals, shadowing pairs, temporaries, tuple-pattern components and
            // a reference pattern: never `Some` off the parameter universe.
            for info in &infos {
                assert!(
                    info.argument_index.is_none(),
                    "non-parameter local {local:?} of {fn_did:?} carries \
                     argument_index {:?} — `var_debug_info`'s meaning has \
                     changed and the locals universe rule must be re-derived",
                    info.argument_index
                );
            }
            let binding_span = infos[0].source_info.span;
            // Exactly one entry names the local; more than one is defensive and
            // NOT known to be reachable, so it declines to name rather than
            // picking. `param_name: None` is what makes the artifact report Low.
            let name = (infos.len() == 1).then(|| infos[0].name.to_string());
            let declared = name
                .is_some()
                .then(|| lets.by_pat_span.get(&binding_span).copied())
                .flatten()
                .flatten();
            let (decl_shape, pointee_span, ty_span) = match declared.map(|t| (t, t.kind)) {
                Some((t, rustc_hir::TyKind::Ptr(mut_ty))) => (
                    decision::DeclShape::RawPtr,
                    Some(mut_ty.ty.span),
                    Some(t.span),
                ),
                Some((t, rustc_hir::TyKind::Ref(_, mut_ty))) => (
                    decision::DeclShape::Reference,
                    Some(mut_ty.ty.span),
                    Some(t.span),
                ),
                Some((t, rustc_hir::TyKind::Path(_))) => {
                    (decision::DeclShape::Alias, None, Some(t.span))
                }
                Some((t, _)) => (decision::DeclShape::Other, None, Some(t.span)),
                // No declared type of its own — unannotated, or a destructuring
                // component. **The shape is still knowable**, from the resolved
                // type: the universe filter above admits this local only when
                // `ptr_chain_depth(ty) > 0`, which is `RawPtr` or `Ref` and
                // nothing else.
                //
                // Reporting `Other` here — as every vintage before the
                // dissolution did — asserted a syntax the subject does not
                // have, and it HID a population: 51 of these locals are
                // C2Rust's `let ref mut fresh…` temporaries, whose resolved
                // type is already `&mut T`. They are not unconvertible, they
                // are already converted, and `unsupported-decl-shape` with
                // shape `reference` is the existing key that says so. Keyed on
                // the resolved type rather than on the construction class,
                // because 51-of-52 is a correlation and the type is the fact.
                //
                // `Alias` is deliberately unreachable here: an alias is a
                // syntactic spelling, the resolved type has none, and there is
                // no alias in the source for a rewrite to preserve.
                None => (
                    match ty.kind() {
                        TyKind::RawPtr(..) => decision::DeclShape::RawPtr,
                        TyKind::Ref(..) => decision::DeclShape::Reference,
                        // Not reachable through the universe filter; attributed
                        // rather than folded into either arm, so a widened
                        // filter shows up as a reason and not as a silent
                        // reclassification.
                        _ => decision::DeclShape::Other,
                    },
                    None,
                    None,
                ),
            };
            // Attribution, not a placeholder. Absence is a contradiction, not a
            // fallback: this local HAS a `var_debug_info` span, and a
            // `CRATE_HIR_ID` here is what made both A1 gates dead for every
            // local. Loud, on the same reasoning as the `argument_index` assert
            // above — a silent default would restore the defect exactly.
            let Some(&hir_id) = lets.binding_hir.get(&binding_span) else {
                panic!(
                    "local {local:?} of {fn_did:?} has debug-info span \
                     {binding_span:?} matching no binding pattern in the body — \
                     `var_debug_info`'s relationship to HIR bindings has changed \
                     and the locals attribution rule must be re-derived"
                );
            };
            subjects.push(decision::Subject {
                fn_did,
                local,
                hir_id,
                param_name: name.clone(),
                kind: decision::SubjectKind::Local,
                ptr_depth: ptr_chain_depth(ty),
                label: format!("{fn_name}::{}", name.as_deref().unwrap_or("<unnamed>")),
                ty_span,
                binding_span,
                pointee_span,
                decl_shape,
                mutable: matches!(
                    ty.kind(),
                    TyKind::RawPtr(_, Mutability::Mut) | TyKind::Ref(_, _, Mutability::Mut)
                ) && mut_facts.is_mutable(fn_did, local),
                // Stamped in `finish_decide`, once, over both universes.
                freed_at: None,
                len_recovered: false,
                null_init: false,
                mut_binding: false,
                ctor: None,
            });
        }
    }
    subjects
}

/// **Census of the collector's own predicate** (§3, census discipline).
///
/// The ledger's `4171/0/0/2039` census came from an uncommitted scratchpad
/// `syn` walk applying the same syntactic `*mut`/`*const` test as the
/// classifier — so it inherited the alias blind spot and *could not have
/// detected it*. A number enters the ledger only via a committed, in-tree code
/// path; this is that path, and it runs the shipping collector.
///
/// `resolved - syntactic_ptr` is the population the retired predicate could not
/// see, broken down by declaration shape so the alias class is a datum rather
/// than a residual.
// `cfg(test)` rather than `allow(dead_code)`: the only consumer is `bo_c1`'s
// corpus harness, which is itself `cfg(test)`. Saying so is more honest than
// silencing the lint, and it keeps the lint working here.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct CollectorCensus {
    /// Subjects the shipping (resolved-type) collector produces.
    pub resolved: usize,
    /// What the retired syntactic `TyKind::Ptr` predicate would have produced.
    pub syntactic_ptr: usize,
    /// Resolved-only, declared through a path — **the C2Rust alias class**.
    pub resolved_only_alias: usize,
    /// Resolved-only, already a reference in source.
    pub resolved_only_reference: usize,
    /// Resolved-only, some other declaration form.
    pub resolved_only_other: usize,
}

/// Run the shipping collector over `tcx` and count what it sees.
#[cfg(test)]
pub(crate) fn census(tcx: TyCtxt<'_>) -> CollectorCensus {
    let program = collect_program(tcx);
    let mut_facts = MutFacts::from_program(&program);
    let mut census = CollectorCensus::default();
    for subject in collect_subjects(tcx, &program, &mut_facts) {
        census.resolved += 1;
        match subject.decl_shape {
            decision::DeclShape::RawPtr => census.syntactic_ptr += 1,
            decision::DeclShape::Alias => census.resolved_only_alias += 1,
            decision::DeclShape::Reference => census.resolved_only_reference += 1,
            decision::DeclShape::Other => census.resolved_only_other += 1,
        }
    }
    census
}

/// Source name of a parameter binding.
///
/// `None` rather than a `"<pattern>"` placeholder: this feeds the artifact's
/// `param_name` pairing term, and a placeholder would compare *equal* between
/// two different pattern parameters — a pairing term that silently agrees is
/// the F1 failure mode in miniature. The placeholder is applied only where it
/// belongs, in the human-readable `label`.
fn param_name(param: &rustc_hir::Param<'_>) -> Option<String> {
    match param.pat.kind {
        rustc_hir::PatKind::Binding(_, _, ident, _) => Some(ident.name.to_string()),
        _ => None,
    }
}

/// The analysis front-end: everything from BO's model to a finished decision
/// table, with the structural self-check and the coverage gate applied.
///
/// Extracted so producer A's artifact is reachable without a second copy of the
/// pipeline — and, deliberately, **without moving any comparison into this
/// module**. `bo_rewriter` emits; `coverage_recon` compares.
fn decide_table<'tcx>(tcx: TyCtxt<'tcx>) -> Result<decision::DecisionTable, String> {
    decide_table_perturbed(tcx, |_| {}).map(|(table, _ctx)| table)
}

/// [`decide_table`], keeping the pipeline's by-products (**R1**).
///
/// Exists so a caller that needs the slots, the accepted model or the
/// emitability facts gets **the ones the table was built from**, instead of
/// re-deriving them — which for the facts join meant a second BO solve per
/// program. Kept as a sibling rather than by widening `decide_table`, so the
/// existing call sites (and their witnesses) are untouched.
fn decide_table_with_ctx<'tcx>(
    tcx: TyCtxt<'tcx>,
) -> Result<(decision::DecisionTable, DecideCtx), String> {
    decide_table_perturbed(tcx, |_| {})
}

#[cfg(test)]
pub(crate) fn cache_decide_receipt_for_test(tcx: TyCtxt<'_>) -> Result<String, String> {
    decide_table_with_ctx(tcx).map(|(_, context)| context.a5_receipt)
}

#[cfg(test)]
pub(crate) fn cache_fingerprint_for_test(tcx: TyCtxt<'_>) -> String {
    let program = collect_program(tcx);
    model_cache::fingerprint(
        &program,
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
    )
}

fn decide_table_with_ctx_config<'tcx>(
    tcx: TyCtxt<'tcx>,
    a5_override: Option<(A5Mode, Option<WholeProgramAttestation>)>,
) -> Result<(decision::DecisionTable, DecideCtx), String> {
    decide_table_perturbed_config(tcx, |_| {}, a5_override, &EmissionRunConfig::default())
}

pub(crate) fn decide_table_with_emission_config<'tcx>(
    tcx: TyCtxt<'tcx>,
    a5_override: Option<(A5Mode, Option<WholeProgramAttestation>)>,
    run_config: &EmissionRunConfig,
) -> Result<(decision::DecisionTable, DecideCtx), String> {
    decide_table_perturbed_config(tcx, |_| {}, a5_override, run_config)
}

/// **Validation-transfer entry.** One emit, one diagnose, no revert loop.
///
/// The loop's `.err` log concatenates every round's compile, so a structural-vs-
/// rendered comparison cannot be made 1:1 against it. This reproduces S2b.0's
/// conditions exactly — a single verify of the fully-emitted crate — so the two
/// extraction paths can be compared on the same diagnostics.
#[allow(
    dead_code,
    reason = "reached only from bo_c1's `m1-diag` validation-transfer driver, \
              which is #[cfg(test)]. Correct this reason if a non-test consumer \
              appears."
)]
pub(crate) fn diagnose_once(
    root: &std::path::Path,
) -> Result<(std::path::PathBuf, Vec<verify::Diag>), String> {
    // Routes through `rewrite_core` in probe mode rather than calling
    // `emit_files` itself: a second call site would be a second emission path,
    // which the one-path scan correctly rejected when this was first written
    // that way.
    let outcome = rewrite_core_injected(
        ::utils::compilation::path_to_input(root),
        Some(root),
        MAX_REVERT_ROUNDS,
        &|_| {},
        true,
        false,
        false,
        None,
    );
    let (observed_root, diags) = outcome.into_capture();
    // FAIL-CLOSED. A capture without its frame cannot be canonicalized, and the
    // only remaining way to compare it against rendered output would be to
    // invent a normalization at the consumer — the exact move that produced a
    // second and a third canonicalizer. An error here is loud; a fallback would
    // be silent and would key distinct files alike.
    let observed_root = observed_root.ok_or_else(|| {
        "the probe returned diagnostics with no observed root; their paths \
         cannot be canonicalized"
            .to_owned()
    })?;
    Ok((observed_root, diags))
}

/// Item E's one-iteration differential verifier. It runs the ordinary round-0
/// emission and baseline-subtracted compile, records every attribution, and
/// returns before any revert, re-render, or bisect step can execute.
#[allow(
    dead_code,
    reason = "Item E's cfg(test) corpus worker is the sole consumer of this one-iteration instrument"
)]
pub(crate) fn diagnose_e1_once(root: &std::path::Path) -> Result<E1Capture, String> {
    rewrite_core_injected(
        ::utils::compilation::path_to_input(root),
        Some(root),
        MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        false,
        None,
    )
    .into_e1_capture()
}

/// Raw-boundary census entry: capture the one-iteration diagnostic payload,
/// then allow exactly the production atom/function verifier to converge. It is
/// one decision/emission pass and therefore one cache load, not two stitched
/// measurements.
#[allow(
    dead_code,
    reason = "consumed by the cfg(test) raw-boundary corpus worker"
)]
pub(crate) fn diagnose_raw_boundary_census(root: &std::path::Path) -> Result<E1Capture, String> {
    rewrite_core_injected(
        ::utils::compilation::path_to_input(root),
        Some(root),
        MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        true,
        None,
    )
    .into_e1_capture()
}

pub(crate) fn diagnose_raw_boundary_census_with_config(
    root: &std::path::Path,
    run_config: &EmissionRunConfig,
) -> Result<E1Capture, String> {
    rewrite_core_injected_with_config(
        ::utils::compilation::path_to_input(root),
        Some(root),
        MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        true,
        None,
        run_config,
    )
    .into_e1_capture()
}

/// Everything BOTH outcomes carry, built once and filled in one place.
///
/// # Why this exists
///
/// The outcome variants used to be hand-filled at seven construction sites, and
/// twice a `Degraded` arm hardcoded a field to `0` that had a real value —
/// S2b.0's `emitted_count` (which blocked the span-bucket axis outright) and
/// then `reverted_count`, introduced while repairing the first. Two instances of
/// one shape is a pattern; the third is prevented STRUCTURALLY rather than by
/// another patch. Every field is filled here, once, and the constructors below
/// are the only places the variants may be built — enforced by a scan.
#[derive(Clone, Debug, Default)]
struct OutcomeFacts {
    degradations: Vec<decision::Degradation>,
    excluded: decision::universe::Excluded,
    /// Subjects still emitted. **Observability of the ATTEMPT** on a failure —
    /// a crate that fails the gate still rewrote subjects; that is usually why.
    emitted_count: usize,
    files_touched: usize,
    /// Subjects the verify loop took back. Measured on BOTH arms.
    reverted_count: usize,
    emitted_sites: Vec<EmittedSite>,
    unplaceable: Vec<plan::Unplaceable>,
    bisect_probes: usize,
    /// Main verify-loop compiler invocations, excluding bisect probes.
    verify_rounds: usize,
    escalated: Option<String>,
    /// The FIRST verify's diagnostics, before any revert round. The validation
    /// transfer compares these against the rendered parser 1:1.
    first_diags: Vec<verify::Diag>,
    /// What the UNMODIFIED input already reported — the differential's masking
    /// power per program, and the scope measurement for how many programs
    /// beyond brotli carry a load-bearing baseline.
    baseline_keys: usize,
    baseline_errors: usize,
    /// Baseline messages embedding their own crate root. Expected zero.
    baseline_msg_env: usize,
    /// Edit owners with no `emitted_sites` entry: they carry edits but are
    /// invisible to span attribution. brotli's divergence class, now counted.
    attribution_blind: usize,
    /// The crate root the diagnostics above were OBSERVED against — the temp
    /// copy's root, not the input tree's.
    ///
    /// Carried with [`Self::first_diags`] because the two are one fact: those
    /// paths are absolute inside a per-run temp directory, so a consumer that
    /// receives the payload without its frame cannot canonicalize them and is
    /// left inventing a normalization. That is precisely how a second and then
    /// a third path canonicalizer came to exist.
    observed_root: Option<std::path::PathBuf>,
    a5_receipt: String,
    e1_reverts: Vec<E1RevertDiagnostic>,
    e1_adapter_receipt: String,
    e1_subject_receipt: String,
    e2_artifacts: E2Artifacts,
    raw_boundary_artifacts: RawBoundaryArtifacts,
    e1_novel_error_count: usize,
    e1_box_drop_receipt: String,
    solve_receipt: Option<model_cache::SolveReceipt>,
}

impl RewriteOutcome {
    /// The first verify's diagnostics, whichever way the run ended.
    ///
    /// An accessor rather than a `match` at the call site: the one-filling-site
    /// scan is textual and cannot tell a construction from a destructuring, so
    /// every avoidable naming of a variant outside the two constructors is one
    /// less false positive for a guard that is otherwise exact.
    ///
    /// Hands out the payload and its frame **together** — a caller that could
    /// take the diagnostics alone would have to invent a normalization for
    /// their temp-absolute paths, which is how the second and third path
    /// canonicalizers came to exist.
    ///
    /// No `#[allow(dead_code)]`, and the reason is measured rather than
    /// assumed: `mod bo_c1` IS `#[cfg(test)]`, so in a non-test build the only
    /// caller is gone — but `diagnose_once` carries its own `allow`, and
    /// rustc's dead-code pass treats an `allow`ed item as a live root, which
    /// keeps this reachable. `cargo check` on the non-test build is clean.
    fn into_capture(self) -> (Option<std::path::PathBuf>, Vec<verify::Diag>) {
        // ONE LINE PER PATTERN, deliberately: the one-filling-site scan skips a
        // line carrying `..`, so a destructuring split across lines leaves
        // `RewriteOutcome::Emitted {` alone on a line and is counted as a
        // construction. That direction is safe — a multi-line CONSTRUCTION is
        // still caught by its own first line — but it does fail the guard, as
        // it did here. Keep these patterns single-line.
        match self {
            RewriteOutcome::Emitted {
                first_diags,
                observed_root,
                ..
            }
            | RewriteOutcome::Degraded {
                first_diags,
                observed_root,
                ..
            } => (observed_root, first_diags),
        }
    }

    #[allow(
        dead_code,
        reason = "consumed only by Item E's cfg(test) one-iteration corpus worker"
    )]
    fn into_e1_capture(self) -> Result<E1Capture, String> {
        let (
            observed_root,
            e1_reverts,
            e1_adapter_receipt,
            e1_subject_receipt,
            e2_artifacts,
            raw_boundary_artifacts,
            novel_error_count,
            e1_box_drop_receipt,
            baseline_keys,
            baseline_errors,
            baseline_msg_env,
            attempted_placements,
            files_touched,
            unplaceable,
            a5_receipt,
            solve_receipt,
            outcome_reason,
            outcome_kind,
            escalation,
            bisect_probes,
            verify_rounds,
            reverted_count,
            emitted_files,
        ) = match self {
            RewriteOutcome::Emitted {
                files,
                observed_root,
                e1_reverts,
                e1_adapter_receipt,
                e1_subject_receipt,
                e2_artifacts,
                raw_boundary_artifacts,
                e1_novel_error_count,
                e1_box_drop_receipt,
                baseline_keys,
                baseline_errors,
                baseline_msg_env,
                emitted_count,
                files_touched,
                unplaceable,
                a5_receipt,
                solve_receipt,
                escalated,
                bisect_probes,
                verify_rounds,
                reverted_count,
                ..
            } => (
                observed_root,
                e1_reverts,
                e1_adapter_receipt,
                e1_subject_receipt,
                e2_artifacts,
                raw_boundary_artifacts,
                e1_novel_error_count,
                e1_box_drop_receipt,
                baseline_keys,
                baseline_errors,
                baseline_msg_env,
                emitted_count,
                files_touched,
                unplaceable.len(),
                a5_receipt,
                solve_receipt,
                "emitted".to_owned(),
                CensusOutcomeKind::Emitted,
                escalated.unwrap_or_default(),
                bisect_probes,
                verify_rounds,
                reverted_count,
                Some(files),
            ),
            RewriteOutcome::Degraded {
                reason,
                observed_root,
                e1_reverts,
                e1_adapter_receipt,
                e1_subject_receipt,
                e2_artifacts,
                raw_boundary_artifacts,
                e1_novel_error_count,
                e1_box_drop_receipt,
                baseline_keys,
                baseline_errors,
                baseline_msg_env,
                emitted_count,
                files_touched,
                unplaceable,
                a5_receipt,
                solve_receipt,
                bisect_probes,
                verify_rounds,
                reverted_count,
                ..
            } => (
                observed_root,
                e1_reverts,
                e1_adapter_receipt,
                e1_subject_receipt,
                e2_artifacts,
                raw_boundary_artifacts,
                e1_novel_error_count,
                e1_box_drop_receipt,
                baseline_keys,
                baseline_errors,
                baseline_msg_env,
                emitted_count,
                files_touched,
                unplaceable.len(),
                a5_receipt,
                solve_receipt,
                reason.clone(),
                CensusOutcomeKind::Degraded,
                reason,
                bisect_probes,
                verify_rounds,
                reverted_count,
                None,
            ),
        };
        Ok(E1Capture {
            observed_root: observed_root
                .ok_or_else(|| format!("E1 capture has no observed root: {outcome_reason}"))?,
            reverts: e1_reverts,
            adapter_receipt: e1_adapter_receipt,
            subject_receipt: e1_subject_receipt,
            e2_artifacts,
            raw_boundary_artifacts,
            novel_error_count,
            baseline_keys,
            baseline_errors,
            baseline_msg_env,
            attempted_placements,
            files_touched,
            unplaceable,
            a5_receipt,
            box_drop_receipt: e1_box_drop_receipt,
            solve_receipt: solve_receipt
                .ok_or_else(|| "E1 capture has no solve receipt".to_owned())?,
            outcome_kind,
            escalation,
            bisect_probes,
            verify_rounds,
            reverted_count,
            emitted_files,
        })
    }

    #[cfg(test)]
    pub(crate) fn a5_receipt(&self) -> &str {
        match self {
            Self::Emitted { a5_receipt, .. } | Self::Degraded { a5_receipt, .. } => a5_receipt,
        }
    }

    #[cfg(test)]
    pub(crate) fn reverted_count(&self) -> usize {
        match self {
            Self::Emitted { reverted_count, .. } | Self::Degraded { reverted_count, .. } => {
                *reverted_count
            }
        }
    }
}

impl OutcomeFacts {
    fn emitted(
        self,
        source: String,
        files: std::collections::BTreeMap<plan::FileKey, String>,
    ) -> RewriteOutcome {
        RewriteOutcome::Emitted {
            source,
            files,
            files_touched: self.files_touched,
            degradations: self.degradations,
            emitted_count: self.emitted_count,
            excluded: self.excluded,
            emitted_sites: self.emitted_sites,
            bisect_probes: self.bisect_probes,
            verify_rounds: self.verify_rounds,
            escalated: self.escalated,
            unplaceable: self.unplaceable,
            reverted_count: self.reverted_count,
            attribution_blind: self.attribution_blind,
            first_diags: self.first_diags,
            observed_root: self.observed_root,
            baseline_keys: self.baseline_keys,
            baseline_errors: self.baseline_errors,
            baseline_msg_env: self.baseline_msg_env,
            a5_receipt: self.a5_receipt,
            e1_reverts: self.e1_reverts,
            e1_adapter_receipt: self.e1_adapter_receipt,
            e1_subject_receipt: self.e1_subject_receipt,
            e2_artifacts: self.e2_artifacts,
            raw_boundary_artifacts: self.raw_boundary_artifacts,
            e1_novel_error_count: self.e1_novel_error_count,
            e1_box_drop_receipt: self.e1_box_drop_receipt,
            solve_receipt: self.solve_receipt,
        }
    }

    fn degraded(self, reason: String) -> RewriteOutcome {
        RewriteOutcome::Degraded {
            reason,
            degradations: self.degradations,
            excluded: self.excluded,
            emitted_count: self.emitted_count,
            files_touched: self.files_touched,
            emitted_sites: self.emitted_sites,
            bisect_probes: self.bisect_probes,
            verify_rounds: self.verify_rounds,
            unplaceable: self.unplaceable,
            reverted_count: self.reverted_count,
            attribution_blind: self.attribution_blind,
            first_diags: self.first_diags,
            observed_root: self.observed_root,
            baseline_keys: self.baseline_keys,
            baseline_errors: self.baseline_errors,
            baseline_msg_env: self.baseline_msg_env,
            a5_receipt: self.a5_receipt,
            e1_reverts: self.e1_reverts,
            e1_adapter_receipt: self.e1_adapter_receipt,
            e1_subject_receipt: self.e1_subject_receipt,
            e2_artifacts: self.e2_artifacts,
            raw_boundary_artifacts: self.raw_boundary_artifacts,
            e1_novel_error_count: self.e1_novel_error_count,
            e1_box_drop_receipt: self.e1_box_drop_receipt,
            solve_receipt: self.solve_receipt,
        }
    }
}

/// Hard ceiling on revert rounds. Paired with the no-progress detector, never
/// relied on alone: a cap that fires is a loop that stopped being understood.
const MAX_REVERT_ROUNDS: usize = 8;
/// Raw-boundary atom mode is one bounded retry, never a repair loop.
const MAX_ATOM_REVERIFIES: usize = 1;

/// Where one planned edit landed, in the lines a diagnostic is reported in.
///
/// **S3.6-1 task 2.** The plan's edits are byte ranges into the original text;
/// a diagnostic carries a line. The conversion is done once, in the driver,
/// from the texts the plan was rendered against — no compiler session, and no
/// second derivation of either quantity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EditSite {
    pub file: String,
    /// Direct signature-class ownership. `None` is only the derived crate-level
    /// fallback extent declaration.
    pub owner_class: Option<bridge_receipt::SignatureClassId>,
    /// Display-only path for receipts.
    pub fn_path: String,
    pub lo_line: usize,
    pub hi_line: usize,
    /// Stable plan-edit identity used only in atom coverage/receipts.
    pub edit_id: String,
    /// Already-expanded subject dependency group.
    pub atom_ids: Vec<String>,
    /// False means another edit under this owner has no atom coverage, so the
    /// verifier must use the established function fallback.
    pub atom_covered: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct EditKey {
    owner: String,
    subject: String,
    arms: String,
    kind: &'static str,
    file: String,
    lo: usize,
    hi: usize,
    replacement_sha256: String,
}

impl EditKey {
    fn render(&self) -> String {
        format!(
            "owner={}|subject={}|arms={}|kind={}|interval={}:{}:{}|replacement_sha256={}",
            self.owner,
            self.subject,
            self.arms,
            self.kind,
            self.file,
            self.lo,
            self.hi,
            self.replacement_sha256,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AtomSelectionKind {
    Exact,
    GroupAtomic,
    BisectGroup,
    Fallback,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AtomSelection {
    pub kind: AtomSelectionKind,
    pub atoms: std::collections::BTreeSet<String>,
    pub reason: &'static str,
}

fn atom_fallback(reason: &'static str) -> AtomSelection {
    AtomSelection {
        kind: AtomSelectionKind::Fallback,
        atoms: std::collections::BTreeSet::new(),
        reason,
    }
}

fn render_raw_boundary_final_reverts(
    functions: &std::collections::BTreeSet<bridge_receipt::SignatureClassId>,
    atoms: &std::collections::BTreeSet<String>,
    display_paths: &std::collections::BTreeMap<bridge_receipt::SignatureClassId, String>,
) -> String {
    let mut out = String::from("kind\tidentity\tclass_id\n");
    for &function in functions {
        let path = display_paths
            .get(&function)
            .map_or("<unknown-local-class>", String::as_str);
        out.push_str(&format!(
            "function\t{path}\tlocal-def-index:{}\n",
            function.order_key()
        ));
    }
    for atom in atoms {
        out.push_str(&format!("atom\t{atom}\t-\n"));
    }
    out
}

/// Pure selection over original-source lines. Production first translates
/// rustc's emitted lines back to these coordinates; the unit witnesses use it
/// directly so exact-vs-group-vs-fallback is observable without a compiler.
pub(crate) fn select_atoms_on_original_lines(
    diags: &[verify::Diag],
    edits: &[EditSite],
) -> AtomSelection {
    let mut files = edits
        .iter()
        .map(|edit| edit.file.as_str())
        .collect::<Vec<_>>();
    files.sort_unstable();
    files.dedup();
    let single_file = files.len() <= 1;
    let at = |file: &str, line: usize| {
        edits
            .iter()
            .filter(|edit| {
                (single_file || edit.file == file) && edit.lo_line <= line && line <= edit.hi_line
            })
            .collect::<Vec<_>>()
    };
    let mut selected = std::collections::BTreeSet::new();
    let mut grouped = false;
    for diagnostic in diags {
        let primary = at(&diagnostic.file, diagnostic.line);
        if primary.is_empty() {
            return atom_fallback("atom-attribution-ambiguous");
        }
        if primary
            .iter()
            .any(|edit| !edit.atom_covered || edit.atom_ids.is_empty())
        {
            return atom_fallback("atom-coverage-incomplete");
        }
        let alias_group = matches!(diagnostic.code.as_deref(), Some("E0499" | "E0502"));
        let primary_groups = primary
            .iter()
            .map(|edit| edit.atom_ids.as_slice())
            .collect::<std::collections::BTreeSet<_>>();
        if !alias_group && primary_groups.len() != 1 {
            let groups = primary_groups
                .into_iter()
                .map(|group| group.to_vec())
                .collect::<Vec<_>>();
            if groups.len() < 2 {
                return atom_fallback("atom-attribution-ambiguous");
            }
            // One deterministic half only. The following compiler pass is the
            // sole experiment: success keeps the sibling half, failure falls
            // back to the established function-level revert. There is no
            // recursive search and MAX_ATOM_REVERIFIES remains one.
            let take = groups.len().div_ceil(2);
            let atoms = groups
                .into_iter()
                .take(take)
                .flatten()
                .collect::<std::collections::BTreeSet<_>>();
            return AtomSelection {
                kind: AtomSelectionKind::BisectGroup,
                atoms,
                reason: "atom-bounded-group-bisection",
            };
        }
        for edit in primary {
            selected.extend(edit.atom_ids.iter().cloned());
        }
        if alias_group {
            grouped = true;
            for related in &diagnostic.related {
                let related_sites = at(&related.file, related.line);
                if related_sites
                    .iter()
                    .any(|edit| !edit.atom_covered || edit.atom_ids.is_empty())
                {
                    return atom_fallback("atom-coverage-incomplete");
                }
                for edit in related_sites {
                    selected.extend(edit.atom_ids.iter().cloned());
                }
            }
        }
    }
    if selected.is_empty() {
        return atom_fallback("atom-attribution-ambiguous");
    }
    AtomSelection {
        kind: if grouped || selected.len() > 1 {
            AtomSelectionKind::GroupAtomic
        } else {
            AtomSelectionKind::Exact
        },
        atoms: selected,
        reason: if grouped {
            "atom-related-span-group"
        } else {
            "atom-exact"
        },
    }
}

fn select_subject_atoms(
    diags: &[verify::Diag],
    line_maps: &std::collections::BTreeMap<plan::FileKey, apply::LineMap>,
    observed_root: &std::path::Path,
    edits: &[EditSite],
    original_root: &std::path::Path,
) -> AtomSelection {
    let maps = line_maps
        .iter()
        .map(|(key, map)| {
            let original = match key {
                plan::FileKey::Real(path) => path.display().to_string(),
                plan::FileKey::Virtual(name) => name.clone(),
            };
            (
                verify::crate_relative(&original, original_root),
                original,
                map,
            )
        })
        .collect::<Vec<_>>();
    let edit_files = edits
        .iter()
        .map(|edit| edit.file.clone())
        .collect::<std::collections::BTreeSet<_>>();
    let translate = |file: &str, line: usize| {
        let relative = verify::crate_relative(file, observed_root);
        let matched = maps
            .iter()
            .filter(|(candidate, _, _)| *candidate == relative)
            .collect::<Vec<_>>();
        if let [(_, original, map)] = matched.as_slice() {
            return ((*original).clone(), map.to_original(line));
        }
        if maps.len() == 1 {
            return (maps[0].1.clone(), maps[0].2.to_original(line));
        }
        let matching_files = edit_files
            .iter()
            .filter(|candidate| verify::crate_relative(candidate, original_root) == relative)
            .cloned()
            .collect::<Vec<_>>();
        if let [original] = matching_files.as_slice() {
            (original.clone(), line)
        } else {
            (file.to_owned(), line)
        }
    };
    let translated = diags
        .iter()
        .map(|diagnostic| {
            let (file, line) = translate(&diagnostic.file, diagnostic.line);
            let related = diagnostic
                .related
                .iter()
                .map(|related| {
                    let (file, line) = translate(&related.file, related.line);
                    verify::RelatedDiag {
                        file,
                        line,
                        message: related.message.clone(),
                    }
                })
                .collect();
            verify::Diag {
                file,
                line,
                message: diagnostic.message.clone(),
                direction: diagnostic.direction,
                code: diagnostic.code.clone(),
                related,
            }
        })
        .collect::<Vec<_>>();
    select_atoms_on_original_lines(&translated, edits)
}

#[cfg(test)]
pub(crate) fn atom_surviving_edit_ids(
    edits: &[EditSite],
    reverted: &std::collections::BTreeSet<String>,
) -> std::collections::BTreeSet<String> {
    edits
        .iter()
        .filter(|edit| edit.atom_ids.iter().all(|atom| !reverted.contains(atom)))
        .map(|edit| edit.edit_id.clone())
        .collect()
}

/// Line range of a byte range in `text`, 1-based, inclusive.
fn line_span(text: &str, lo: usize, hi: usize) -> (usize, usize) {
    let count = |upto: usize| {
        text.get(..upto.min(text.len()))
            .map_or(1, |s| s.matches('\n').count() + 1)
    };
    (count(lo), count(hi))
}

/// Every planned edit, located in lines.
fn edit_sites(
    planned: &plan::Plan,
    texts: &std::collections::BTreeMap<plan::FileKey, String>,
) -> Vec<EditSite> {
    let mut owners_with_atoms = std::collections::BTreeSet::new();
    let mut owners_with_uncovered_edits = std::collections::BTreeSet::new();
    for edit in planned.by_file.values().flatten() {
        let Some(owner_class) = edit.owner_class else {
            continue;
        };
        if edit.atom_ids.is_empty() {
            owners_with_uncovered_edits.insert(owner_class);
        } else {
            owners_with_atoms.insert(owner_class);
        }
    }
    let mut out = Vec::new();
    for (key, edits) in &planned.by_file {
        let Some(text) = texts.get(key) else {
            continue;
        };
        let file = match key {
            plan::FileKey::Real(path) => path.display().to_string(),
            plan::FileKey::Virtual(name) => name.clone(),
        };
        for edit in edits {
            let (lo_line, hi_line) = line_span(text, edit.lo, edit.hi);
            let replacement_sha256 = {
                use sha2::{Digest, Sha256};
                format!("{:x}", Sha256::digest(edit.replacement.as_bytes()))
            };
            let edit_key = EditKey {
                owner: edit.owner_path.clone(),
                subject: edit.subject_id.clone(),
                arms: edit.required_arms.clone(),
                kind: edit.edit_kind,
                file: file.clone(),
                lo: edit.lo,
                hi: edit.hi,
                replacement_sha256,
            };
            out.push(EditSite {
                file: file.clone(),
                owner_class: edit.owner_class,
                fn_path: edit.owner_path.clone(),
                lo_line,
                hi_line,
                edit_id: edit_key.render(),
                atom_ids: edit.atom_ids.clone(),
                atom_covered: !edit.atom_ids.is_empty()
                    && edit
                        .owner_class
                        .is_some_and(|owner| owners_with_atoms.contains(&owner))
                    && edit
                        .owner_class
                        .is_some_and(|owner| !owners_with_uncovered_edits.contains(&owner)),
            });
        }
    }
    out
}

fn e1_edit_contexts(
    planned: &plan::Plan,
    texts: &std::collections::BTreeMap<plan::FileKey, String>,
) -> Vec<(bridge_receipt::SignatureClassId, String, E1EditContext)> {
    let mut out = Vec::new();
    for (key, edits) in &planned.by_file {
        let Some(text) = texts.get(key) else {
            continue;
        };
        let file = match key {
            plan::FileKey::Real(path) => path.display().to_string(),
            plan::FileKey::Virtual(name) => name.clone(),
        };
        for edit in edits {
            let Some(owner_class) = edit.owner_class else {
                continue;
            };
            let (lo_line, hi_line) = line_span(text, edit.lo, edit.hi);
            let replacement_head = edit
                .replacement
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ")
                .chars()
                .take(160)
                .collect();
            out.push((
                owner_class,
                edit.owner_path.clone(),
                E1EditContext {
                    file: file.clone(),
                    lo_line,
                    hi_line,
                    shape: format!("{:?}", edit.justification),
                    replacement_head,
                },
            ));
        }
    }
    out.sort_by(|left, right| {
        (
            left.0,
            left.1.as_str(),
            left.2.file.as_str(),
            left.2.lo_line,
            left.2.hi_line,
            left.2.shape.as_str(),
        )
            .cmp(&(
                right.0,
                right.1.as_str(),
                right.2.file.as_str(),
                right.2.lo_line,
                right.2.hi_line,
                right.2.shape.as_str(),
            ))
    });
    out
}

/// Functions whose own rewrite is implicated by these diagnostics.
///
/// Direction is recorded on the diagnostic and reported, but is deliberately
/// NOT consulted here: it is diagnostic, not a router — the no-progress
/// detector decides escalation, so a mis-attribution is caught by measurement
/// rather than pre-empted by a heuristic that could be wrong.
///
/// # The S3 repair (task 2), and what it does and does not fix
///
/// Attribution used to be span containment against each rewritten subject's own
/// **function extent**, and nothing else. That is sound only while every edit
/// sits inside a function that holds a subject — true through S3.2′, and
/// **false the moment call-site adaptation emits into a caller file**: the
/// diagnostic then lands in a function that may hold no subject at all, so it
/// attributes to nobody, the revert loop cannot converge on the culprit, and it
/// falls through to bisect, which "may revert more than strictly necessary".
///
/// So an **edit range is consulted first**: a diagnostic inside a planned
/// edit's own lines names the subject that justifies that edit — which is
/// `Edit::owner_fn`, the CALLEE, even when the edit is in the caller's file.
/// Function-extent containment stays as the fallback, because most diagnostics
/// land near an edit rather than on it.
///
/// **Stated as a residual rather than claimed away:** a diagnostic in a caller
/// function that holds neither an edit nor a subject — the zero-text adaptation
/// case, where the caller's argument needs no change at all — still attributes
/// to nobody. That case is what escalation and bisect exist for, and
/// `attribution_blind` is what counts it.
fn e1_bijective_line(
    diagnostic: &verify::Diag,
    line_maps: &std::collections::BTreeMap<plan::FileKey, apply::LineMap>,
    observed_root: &std::path::Path,
    original_root: &std::path::Path,
) -> Option<usize> {
    let diagnostic_file = verify::crate_relative(&diagnostic.file, observed_root);
    let mut candidates = line_maps
        .iter()
        .filter_map(|(key, map)| match key {
            plan::FileKey::Real(path)
                if verify::crate_relative(&path.display().to_string(), original_root)
                    == diagnostic_file =>
            {
                Some(map)
            }
            plan::FileKey::Virtual(name) if *name == diagnostic_file => Some(map),
            _ => None,
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() && line_maps.len() == 1 {
        candidates.extend(line_maps.values());
    }
    if candidates.len() != 1 {
        return None;
    }
    candidates[0].to_original_if_bijective(diagnostic.line)
}

fn e1_region_owners(
    diagnostic: &verify::Diag,
    line_maps: &std::collections::BTreeMap<plan::FileKey, apply::LineMap>,
    observed_root: &std::path::Path,
    original_root: &std::path::Path,
    sites: &[EmittedSite],
    edits: &[EditSite],
) -> std::collections::BTreeSet<bridge_receipt::SignatureClassId> {
    let diagnostic_file = verify::crate_relative(&diagnostic.file, observed_root);
    let mut maps = line_maps
        .iter()
        .filter_map(|(key, map)| match key {
            plan::FileKey::Real(path)
                if verify::crate_relative(&path.display().to_string(), original_root)
                    == diagnostic_file =>
            {
                Some(map)
            }
            plan::FileKey::Virtual(name) if *name == diagnostic_file => Some(map),
            _ => None,
        })
        .collect::<Vec<_>>();
    if maps.is_empty() && line_maps.len() == 1 {
        maps.extend(line_maps.values());
    }
    let Some((lo, hi)) = (maps.len() == 1)
        .then(|| maps[0].original_region(diagnostic.line))
        .flatten()
    else {
        return std::collections::BTreeSet::new();
    };
    let single_file = line_maps.len() == 1;
    let same_file =
        |file: &str| single_file || verify::crate_relative(file, original_root) == diagnostic_file;
    let mut owners = edits
        .iter()
        .filter(|edit| same_file(&edit.file) && edit.lo_line <= hi && lo <= edit.hi_line)
        .filter_map(|edit| edit.owner_class)
        .collect::<std::collections::BTreeSet<_>>();
    if owners.is_empty() {
        owners.extend(
            sites
                .iter()
                .filter(|site| same_file(&site.file) && site.lo_line <= hi && lo <= site.hi_line)
                .map(|site| site.owner_class),
        );
    }
    owners
}

fn e1_diagnostic_site(diagnostic: &verify::Diag) -> E1DiagnosticSite {
    let callee_relation = diagnostic.message.contains("function defined here")
        || diagnostic
            .related
            .iter()
            .any(|related| related.message.contains("function defined here"));
    if callee_relation {
        E1DiagnosticSite::CallBoundary
    } else if diagnostic.direction == verify::Direction::RawIntoRewritten
        || (matches!(diagnostic.code.as_deref(), Some("E0308" | "ErrCode(308)"))
            && diagnostic.message.contains("found raw pointer"))
    {
        E1DiagnosticSite::BodyExpression
    } else {
        E1DiagnosticSite::Other
    }
}

#[cfg(test)]
fn e1_call_site_not_adapted(diagnostic: &verify::Diag) -> bool {
    e1_diagnostic_site(diagnostic) == E1DiagnosticSite::CallBoundary
}

fn attribute(
    diags: &[verify::Diag],
    // **I-31**: emitted→original line translation, per file, produced by the
    // splicer that emitted this round. Without it the comparison below matches
    // a line in the EMITTED program against ranges measured in the ORIGINAL.
    line_maps: &std::collections::BTreeMap<plan::FileKey, apply::LineMap>,
    observed_root: &std::path::Path,
    sites: &[EmittedSite],
    edits: &[EditSite],
    reverted: &std::collections::BTreeSet<bridge_receipt::SignatureClassId>,
    original_root: &std::path::Path,
) -> std::collections::BTreeSet<bridge_receipt::SignatureClassId> {
    // **ONLY THE EDITS THIS ROUND ACTUALLY APPLIED.**
    //
    // `edit_sites` is built once from the whole plan, but `render` keeps an
    // edit only while its direct owner class is live. Attributing through
    // the unfiltered list is therefore a SECOND derivation of "which edits are
    // live", and the two diverge the moment anything is reverted: a stale edit
    // matches a later round's diagnostic, contributes only an already-reverted
    // owner, short-circuits the extent pass below, and is then removed by the
    // caller's `.difference(&reverted)` — leaving the diagnostic attributed to
    // nobody and sending a convergent run to bisect.
    //
    // Two derivations assumed identical is this module's founding defect class
    // (it cost a brotli sweep when `candidates` and `emitted_sites` diverged),
    // so attribution filters by the SAME predicate `render` filters by.
    let edits: Vec<&EditSite> = edits
        .iter()
        .filter(|edit| {
            edit.owner_class
                .is_some_and(|class| !reverted.contains(&class))
        })
        .collect();
    // The SAME canonicalizer as the differential gate, each side against its own
    // root: sites were recorded in the original tree, diagnostics come from the
    // temp copy. A second normalization here would drift attribution away from
    // the gate — the same defect class, one layer over.
    //
    // The single-file shortcut is computed over the UNION of both site kinds:
    // computing it over `sites` alone would let a caller-file edit be matched
    // file-blind whenever the subject functions happen to share one file, which
    // is precisely the multi-file case this repair is for.
    let single_file = {
        let mut files: Vec<&str> = sites
            .iter()
            .map(|s| s.file.as_str())
            .chain(edits.iter().map(|e| e.file.as_str()))
            .collect();
        files.sort_unstable();
        files.dedup();
        files.len() <= 1
    };
    let mut owners = std::collections::BTreeSet::new();
    // Crate-relative keys, so a diagnostic's file can find its map: the maps
    // are keyed by the ORIGINAL path, the diagnostic names a path in the
    // materialized copy.
    let maps_by_rel: std::collections::BTreeMap<String, &apply::LineMap> = line_maps
        .iter()
        .filter_map(|(key, map)| match key {
            plan::FileKey::Real(path) => Some((
                verify::crate_relative(&path.display().to_string(), original_root),
                map,
            )),
            plan::FileKey::Virtual(name) => Some((name.clone(), map)),
        })
        .collect();
    for diag in diags {
        let diag_rel = verify::crate_relative(&diag.file, observed_root);
        // **THE TRANSLATION** (I-31). `diag.line` indexes the EMITTED document;
        // every range below was measured in the ORIGINAL. `render` kept the two
        // within a line, so this was invisible for the whole span era;
        // `pprust` reprints whole functions and the drift reaches −36 on
        // libtree, which silently reverts functions that did nothing wrong.
        //
        // Single-file crates (all 20, C-20) have exactly one map, so the
        // lookup falls back to it rather than failing on a path mismatch —
        // and a MISSING map means "no splice happened", where the identity is
        // correct, not a reason to skip attribution.
        let diag_line = maps_by_rel
            .get(&diag_rel)
            .or(if maps_by_rel.len() == 1 {
                maps_by_rel.values().next()
            } else {
                None
            })
            .map_or(diag.line, |map| map.to_original(diag.line));
        let mut by_edit = std::collections::BTreeSet::new();
        for edit in &edits {
            let same_file =
                single_file || verify::crate_relative(&edit.file, original_root) == diag_rel;
            if same_file && edit.lo_line <= diag_line && diag_line <= edit.hi_line {
                if let Some(owner_class) = edit.owner_class {
                    by_edit.insert(owner_class);
                }
            }
        }
        if !by_edit.is_empty() {
            owners.extend(by_edit);
            continue;
        }
        for site in sites {
            let same_file =
                single_file || verify::crate_relative(&site.file, original_root) == diag_rel;
            if same_file && site.lo_line <= diag_line && diag_line <= site.hi_line {
                owners.insert(site.owner_class);
            }
        }
    }
    owners
}

/// Where a rewritten subject's own function lives, for attributing a verify
/// diagnostic to it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EmittedSite {
    pub owner_class: bridge_receipt::SignatureClassId,
    pub file: String,
    pub fn_path: String,
    pub lo_line: usize,
    pub hi_line: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct EmittedSubject {
    owner_class: bridge_receipt::SignatureClassId,
    owner_path: String,
    subject: String,
    site: String,
    atoms: Vec<String>,
}

/// The rewritten source of every file the plan touched, plus what could not be
/// placed. **This is the general emission path**; the string entry point is its
/// single-file case.
#[allow(
    dead_code,
    reason = "`plan` and `texts` are read by S2b.1.2's revert loop, landing in \
              this slice; extracted here so a round needs no second compiler \
              session. Correct this reason when the loop lands."
)]
pub(crate) struct Emission {
    pub files: std::collections::BTreeMap<plan::FileKey, String>,
    pub rollbacks: Vec<apply::Rollback>,
    pub unplaceable: Vec<plan::Unplaceable>,
    /// **Extracted once, inside the single compiler session.** The verify loop's
    /// rounds re-render from these rather than re-planning, so a round needs no
    /// second session — nesting one rustc session inside another was rejected
    /// for lack of soundness evidence. Re-planning degenerates to re-RENDERING,
    /// which is the phase architecture's own claim taken seriously: `plan`
    /// produces edits as DATA.
    pub plan: plan::Plan,
    pub texts: std::collections::BTreeMap<plan::FileKey, String>,
}

/// Apply a plan's edits, minus the reverted owners, to the original texts.
///
/// Pure: no compiler session, no analysis. This is what a revert round runs.
/// # THE EMISSION SITES ARE GONE — this is PLAN VALIDATION (M-3, 2026-08-18)
///
/// This was `render`, the span layer's emitter. Four emission sites routed
/// through it and each was found one at a time, after the previous was called
/// the last: the bisect final emission (`:1069`), then round 0 — the largest,
/// carrying 35 of the corpus's 64 emissions. M-3 deleted the span layer, so
/// **there is no longer an emission path here at all**, and the class of defect
/// that table existed to prevent is now unrepresentable rather than merely
/// absent: the only emitter is the AST layer, reached through `round_files`.
///
/// What survives is the part that was never layer-specific. `emit_files` calls
/// this once, with **no revert set**, to answer one question: does the PLAN
/// apply — are its byte ranges in bounds, on char boundaries, and mutually
/// non-overlapping? Those rollbacks feed the pre-loop structural gate. That
/// gate judges the plan, not a layer, which is why it was kept when its
/// emitter was deleted.
///
/// ⚠ **Its `files` are NOT an emission.** They exist so the caller can pick a
/// `root_key`, and nothing verifies or ships them.
///
/// Not this function and never were: the `.render(…)` METHODS on `fat_facts`,
/// `sign_facts` and `decision::seam`, which share only the name.
pub(crate) fn validate_plan(
    planned: &plan::Plan,
    texts: &std::collections::BTreeMap<plan::FileKey, String>,
) -> (
    std::collections::BTreeMap<plan::FileKey, String>,
    Vec<apply::Rollback>,
    // **I-31**: per-file emitted→original line translation, from the splicer.
    std::collections::BTreeMap<plan::FileKey, apply::LineMap>,
) {
    let mut files = std::collections::BTreeMap::new();
    let mut rollbacks = Vec::new();
    let mut maps = std::collections::BTreeMap::new();
    // Revert by JUSTIFICATION, not geography: an edit survives only if the
    // subject that justifies it has not been taken back.
    let mut kept_by_file: std::collections::BTreeMap<plan::FileKey, Vec<plan::Edit>> =
        planned.by_file.clone();
    // **The fabricated-extent const is DERIVED FROM THE SURVIVORS** (marker
    // ruling, 2026-08-15), which is why it is computed here and not in `plan`:
    // this is the one place that knows which adapters a given revert set
    // leaves standing, and `render` is called once per revert round.
    //
    // No surviving fabricated adapter ⇒ no const, so no dead item; one or many
    // ⇒ exactly one, in the crate root, so no `E0433` when a single fabricated
    // site's function reverts and its siblings do not.
    if kept_by_file.values().flatten().any(|e| {
        matches!(
            e.justification,
            plan::Justification::SeamAdapter {
                fabricated: true,
                ..
            }
        )
    }) && let Some(root) = planned.root_file.clone()
        && let Some(item) = planned.len_const_item.as_deref()
        && let Some(source) = texts.get(&root)
    {
        // Appended at END OF FILE — the one offset both emitters compute
        // identically without parsing. A crate-level `const` is legal there
        // whatever the file's inner attributes, outer attributes or trailing
        // comments look like, and every alternative anchor (after the last
        // inner attribute; before the first item) needs a parse that the span
        // layer, running after HIR is built, cannot redo.
        let at = source.len();
        kept_by_file.entry(root).or_default().push(plan::Edit {
            lo: at,
            hi: at,
            replacement: format!("\n{item}\n"),
            justification: plan::Justification::FabricatedLenConst,
            // Added AFTER the revert filter, so this name is never matched
            // against the revert set — it is not a sentinel that must be kept
            // out of it, it is simply not subject to it.
            owner_class: None,
            owner_path: "<crate>".to_owned(),
            atom_ids: Vec::new(),
            subject_id: "<crate>".to_owned(),
            required_arms: "-".to_owned(),
            edit_kind: "fabricated-length-const",
        });
    }
    for (key, kept) in &kept_by_file {
        if kept.is_empty() {
            continue;
        }
        let Some(source) = texts.get(key) else {
            continue;
        };
        // Wave-1 call adapters make one previously-zero composition live: a
        // seam can strictly contain an ordinary `KindDecision` use edit. The AST
        // choke point applies use first and seam second; this span projection is
        // validation-only and cannot represent nesting. Suppress exactly the
        // contained inner use from the obsolete splice projection while keeping
        // both edits in the real plan for attribution, reverts, and AST
        // consumption. Every other overlap still reaches `apply` and rolls back.
        let validation_edits = kept
            .iter()
            .enumerate()
            .filter(|(inner_index, inner)| {
                (!matches!(
                    inner.justification,
                    plan::Justification::KindDecision { .. }
                ) || !nested_kind_under_seam(kept, *inner_index))
                    && (!matches!(
                        inner.justification,
                        plan::Justification::KindDecision { .. }
                    ) || !exact_kind_composed_by_seam(kept, *inner_index))
                    && !nested_c9_over_seam(kept, *inner_index)
            })
            .map(|(_, edit)| edit.clone())
            .collect::<Vec<_>>();
        let applied = apply::apply(source, &validation_edits);
        rollbacks.extend(applied.rollbacks);
        maps.insert(key.clone(), applied.line_map);
        files.insert(key.clone(), applied.source);
    }
    (files, rollbacks, maps)
}

/// Exactly the one nested plan class the AST pass orders deliberately:
/// ordinary `KindDecision` use first, strictly enclosing call seam second.
/// Equal spans and every other justification remain ordinary overlap failures.
fn nested_kind_under_seam(edits: &[plan::Edit], inner_index: usize) -> bool {
    let inner = &edits[inner_index];
    matches!(
        inner.justification,
        plan::Justification::KindDecision { .. }
    ) && edits.iter().enumerate().any(|(outer_index, outer)| {
        outer_index != inner_index
            && matches!(outer.justification, plan::Justification::SeamAdapter { .. })
            && outer.lo <= inner.lo
            && inner.hi <= outer.hi
            && (outer.lo < inner.lo || inner.hi < outer.hi)
    })
}

/// The AST path has a typed use-to-seam handoff for one exact-span seam. This
/// projection cannot represent sequential ownership of one byte range, so it
/// omits the use projection only when the plan proves the handoff is unique.
fn exact_kind_composed_by_seam(edits: &[plan::Edit], kind_index: usize) -> bool {
    let kind = &edits[kind_index];
    matches!(kind.justification, plan::Justification::KindDecision { .. })
        && edits
            .iter()
            .enumerate()
            .filter(|(seam_index, seam)| {
                *seam_index != kind_index
                    && matches!(seam.justification, plan::Justification::SeamAdapter { .. })
                    && seam.edit_kind != "body-adapter"
                    && seam.lo == kind.lo
                    && seam.hi == kind.hi
            })
            .count()
            == 1
}

/// C-9 owns the enclosing call while a seam owns one argument. The AST choke
/// point composes those structural edits; the byte-splice validator cannot.
/// Suppress only the enclosing C-9 projection when it strictly contains a seam
/// and keep both edits in the authoritative plan and receipts.
fn nested_c9_over_seam(edits: &[plan::Edit], c9_index: usize) -> bool {
    let c9 = &edits[c9_index];
    matches!(c9.justification, plan::Justification::C9Mark)
        && edits.iter().enumerate().any(|(seam_index, seam)| {
            seam_index != c9_index
                && matches!(seam.justification, plan::Justification::SeamAdapter { .. })
                && c9.lo <= seam.lo
                && seam.hi <= c9.hi
                && (c9.lo < seam.lo || seam.hi < c9.hi)
        })
}

/// A source file's identity for editing. `None` for anything not written back
/// to a nameable file (macro-expansion contexts, synthetic inputs).
fn file_key(name: &rustc_span::FileName) -> Option<plan::FileKey> {
    match name {
        rustc_span::FileName::Real(real) => real
            .local_path()
            .map(|path| plan::FileKey::Real(path.to_path_buf())),
        rustc_span::FileName::Custom(name) => Some(plan::FileKey::Virtual(name.clone())),
        _ => None,
    }
}

/// Plan and apply, **grouped by file**.
///
/// Grouping is what makes the offsets meaningful: `lookup_byte_offset` yields
/// *file-relative* positions, so two edits in different files can carry
/// identical `(lo, hi)`. Applying them against one string would splice each into
/// whichever file happened to be passed — silently, and with a plausible result.
pub(crate) fn emit_files<'tcx>(
    tcx: TyCtxt<'tcx>,
    table: &decision::DecisionTable,
    reverted: &rustc_hash::FxHashSet<rustc_hir::def_id::LocalDefId>,
    retained_c9_plans: &[PlannedC9Mark],
) -> Result<Emission, String> {
    let source_map = tcx.sess.source_map();
    let text_of = |key: &plan::FileKey| -> Option<String> {
        source_map
            .files()
            .iter()
            .find(|sf| file_key(&sf.name).as_ref() == Some(key))
            .and_then(|sf| sf.src.as_ref().map(|src| src.to_string()))
    };
    let span_to_loc =
        |span: rustc_span::Span| -> Result<(plan::FileKey, usize, usize), &'static str> {
            // A macro-generated span points into an expansion, not into source
            // anyone can edit. Splicing it would corrupt the file it nominally
            // resolves to.
            if span.from_expansion() {
                return Err("span is macro-generated and cannot be spliced into source");
            }
            let lo = source_map.lookup_byte_offset(span.lo());
            let hi = source_map.lookup_byte_offset(span.hi());
            let (Some(lo_key), Some(hi_key)) = (file_key(&lo.sf.name), file_key(&hi.sf.name))
            else {
                return Err("span resolves to a file with no editable identity");
            };
            if lo_key != hi_key {
                return Err("span straddles two source files");
            }
            let (lo, hi) = (lo.pos.0 as usize, hi.pos.0 as usize);
            if lo > hi {
                return Err("span bounds are inverted");
            }
            Ok((lo_key, lo, hi))
        };

    let mut planned = plan::plan(
        table,
        text_of,
        span_to_loc,
        |subject| tcx.def_path_str(subject.fn_did.to_def_id()),
        &|subject: &decision::Subject| reverted.contains(&subject.fn_did),
    );
    for mark in retained_c9_plans {
        if reverted.contains(&mark.owner_did) {
            continue;
        }
        let (file, lo, hi) = span_to_loc(mark.call_span)
            .map_err(|why| format!("unplaceable retained C-9 mark: {why}"))?;
        let source = text_of(&file)
            .ok_or_else(|| format!("no source text for retained C-9 mark file {file:?}"))?;
        let original = source
            .get(lo..hi)
            .ok_or_else(|| "retained C-9 mark span is outside its source file".to_owned())?;
        let replacement = c9::render_marked_source(&mark.key, original)?;
        planned.by_file.entry(file).or_default().push(plan::Edit {
            lo,
            hi,
            replacement,
            justification: plan::Justification::C9Mark,
            owner_class: Some(bridge_receipt::SignatureClassId::of(mark.owner_did)),
            owner_path: mark.owner_fn.clone(),
            atom_ids: Vec::new(),
            subject_id: mark.owner_fn.clone(),
            required_arms: "-".to_owned(),
            edit_kind: "c9-mark",
        });
    }
    // **The crate root, asked of the compiler rather than guessed** — not
    // `files()[0]`, which is source-map insertion order, and not the first
    // planned file, which is whichever file happened to hold an edit.
    // `crate::FALLBACK_SLICE_EXTENT` resolves from exactly one module.
    planned.root_file = {
        let root = tcx.def_span(rustc_hir::def_id::CRATE_DEF_ID);
        file_key(&source_map.lookup_byte_offset(root.lo()).sf.name)
    };
    // **Produced HERE, where a `TyCtxt` provably exists.** `render` runs three
    // more times inside the verify/revert loop, which is OUTSIDE the compiler
    // session — parsing or printing there panics `scoped-tls`. Built
    // unconditionally: it is one small string, and making it conditional would
    // put a second copy of the survivor rule in a place that cannot see the
    // survivors.
    planned.len_const_item = Some(decision::seam::fabricated_len_item());

    let mut texts = std::collections::BTreeMap::new();
    for key in planned.by_file.keys() {
        let Some(source) = text_of(key) else {
            return Err(format!("no source text for planned file {key:?}"));
        };
        texts.insert(key.clone(), source);
    }
    // The root is included even when it holds no edit: a crate whose only
    // fabricated adapters land in other files still declares the const at its
    // root, and `render` cannot splice a file whose text it was not given.
    //
    // ⚠ **Its absence is NOT fatal** (ADV-FAB-09). Folding the root into the
    // loop above made an unreadable root text fail the WHOLE emission — for
    // every crate, including the fourteen that fabricate nothing. A feature that
    // may never fire in a program must not be able to stop that program from
    // emitting. Missing root text fail-closes the const alone: `render`'s
    // `texts.get(&root)` misses, no insertion happens, and the fabricated
    // adapters that name it fail `verify` and revert.
    if let Some(root) = planned.root_file.clone()
        && !texts.contains_key(&root)
        && let Some(source) = text_of(&root)
    {
        texts.insert(root, source);
    }
    let (files, rollbacks, _) = validate_plan(&planned, &texts);
    Ok(Emission {
        files,
        rollbacks,
        unplaceable: planned.unplaceable.clone(),
        plan: planned,
        texts,
    })
}

/// [`decide_table`] with a hook applied to the collector's real output at the
/// PHASE BOUNDARY, before `decide` runs.
///
/// The hook is a no-op in production (`decide_table` passes `|_| {}`) and exists
/// so a test can inject the exact defect this axis guards — a mis-associated
/// span on the collector's own `Subject` type — and then drive it through the
/// real `decide → artifact → encode → decode → compare` path.
///
/// **This is deliberately not a production fault seam.** A `CRAT_*`-gated seam
/// inside decision-phase code was considered and DENIED; a collector fault
/// manifests as exactly the mis-associated output a boundary hook injects, so
/// the verification power is the same at zero production-code cost. That is the
/// phase-separated architecture paying for itself.
fn decide_table_perturbed<'tcx>(
    tcx: TyCtxt<'tcx>,
    perturb: impl FnOnce(&mut Vec<decision::Subject>),
) -> Result<(decision::DecisionTable, DecideCtx), String> {
    decide_table_perturbed_config(tcx, perturb, None, &EmissionRunConfig::default())
}

/// Read-only analysis inputs carried across the solve/cache boundary without
/// shaping them for a particular rewriter consumer.
///
/// A5 site proofs are the first reader. E2-FN is ruled to reuse this same
/// carrier: in particular, the complete `OriginSummaries` object remains
/// intact rather than being projected into an A5-specific export.
struct DecisionAnalysisCarrier {
    origins: Option<OriginSummaries>,
    a5_mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
    cache_load_wall_s: f64,
    origin_derivation_wall_s: f64,
}

fn cached_rewriter_plans(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    mut_facts: &MutFacts,
    a5_mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
    cached: &model_cache::CachedModel,
) -> Result<(Vec<PlannedC9Mark>, Option<OriginSummaries>, f64), String> {
    match a5_mode {
        A5Mode::Baseline => Ok((Vec::new(), None, 0.0)),
        A5Mode::PreciseReplay => {
            let origin_started = std::time::Instant::now();
            let origins = compute_origins(program);
            let origin_derivation_wall_s = origin_started.elapsed().as_secs_f64();
            let plans = cached_precise_rewriter_payload(
                program,
                slots,
                &origins,
                mut_facts,
                &cached.baseline_model,
                &cached.model,
                attestation,
                &cached.a5_receipt,
            )?;
            Ok((plans, Some(origins), origin_derivation_wall_s))
        }
        A5Mode::CoarseConstraint => {
            Err("the pricing-only coarse A5 mode is not cacheable".to_owned())
        }
    }
}

fn decide_table_perturbed_config<'tcx>(
    tcx: TyCtxt<'tcx>,
    perturb: impl FnOnce(&mut Vec<decision::Subject>),
    a5_override: Option<(A5Mode, Option<WholeProgramAttestation>)>,
    run_config: &EmissionRunConfig,
) -> Result<(decision::DecisionTable, DecideCtx), String> {
    let program = collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let mut_facts = MutFacts::from_program(&program);
    let (a5_mode, attestation) =
        a5_override.unwrap_or_else(|| (A5Mode::production(), WholeProgramAttestation::current()));

    // Phase 1 input: the BO run, under an explicit capture scope.
    //
    // The cache is consulted FIRST and is fail-closed: `load` returns `None` on
    // absence, corruption, fingerprint mismatch or an unresolvable key, and
    // `None` can only be answered by solving. Dev iteration reads it; every
    // gate sweep bypasses it and refreshes it.
    // ONE fingerprint computation, shared by the memo and the on-disk cache —
    // they are two tiers of the same question, so they must not disagree about
    // which program this is.
    let fp = model_cache::fingerprint(&program, a5_mode, attestation);
    let cacheable = matches!(a5_mode, A5Mode::Baseline | A5Mode::PreciseReplay);
    let cache_started = std::time::Instant::now();

    // Tier 1: the in-process memo. The recon worker has three independent
    // consumers of the decision table, and before this each ran the entire
    // pipeline — `total ≈ 3 × solve` on every program. Reusing the model here
    // makes a consumer's cost its own work, not another whole solve.
    if cacheable
        && let Some(cached) = model_cache::memo_get(&fp)
        && let Ok((retained_c9_plans, origins, origin_derivation_wall_s)) =
            cached_rewriter_plans(&program, &slots, &mut_facts, a5_mode, attestation, &cached)
    {
        return finish_decide(
            tcx,
            program,
            slots,
            mut_facts,
            cached.model,
            retained_c9_plans,
            cached.a5_receipt,
            DecisionAnalysisCarrier {
                origins,
                a5_mode,
                attestation,
                cache_load_wall_s: cache_started.elapsed().as_secs_f64(),
                origin_derivation_wall_s,
            },
            run_config,
            perturb,
        );
    }

    // Tier 2: the on-disk cache.
    if cacheable
        && let Some(cached) = model_cache::load(tcx, &program, &slots, a5_mode, attestation)
        && let Ok((retained_c9_plans, origins, origin_derivation_wall_s)) =
            cached_rewriter_plans(&program, &slots, &mut_facts, a5_mode, attestation, &cached)
    {
        let model_sha256 = model_cache::model_bytes_sha256(tcx, &slots, &cached.model)
            .ok_or_else(|| "cached model contains an unrenderable slot key".to_owned())?;
        model_cache::record_solve(model_cache::SolveProvenance {
            source: "cache",
            cache_status: "hit",
            fingerprint: fp.clone(),
            model_sha256,
            cache_entry: model_cache::configured_entry_path(&fp)
                .map(|path| path.display().to_string()),
            solve_secs: 0.0,
        });
        model_cache::memo_put(&fp, &cached);
        return finish_decide(
            tcx,
            program,
            slots,
            mut_facts,
            cached.model,
            retained_c9_plans,
            cached.a5_receipt,
            DecisionAnalysisCarrier {
                origins,
                a5_mode,
                attestation,
                cache_load_wall_s: cache_started.elapsed().as_secs_f64(),
                origin_derivation_wall_s,
            },
            run_config,
            perturb,
        );
    }
    let solve_t0 = std::time::Instant::now();
    let origin_started = std::time::Instant::now();
    let origins = compute_origins(&program);
    let origin_derivation_wall_s = origin_started.elapsed().as_secs_f64();
    let (verified, _export) = with_bo_export(|| {
        solve_bo_a5_config(&program, &slots, &origins, &mut_facts, a5_mode, attestation)
    });
    let Some(verified) = verified else {
        return Err("BO declined — no accepted model".to_owned());
    };
    let solve_secs = solve_t0.elapsed().as_secs_f64();
    let model_sha256 = model_cache::model_bytes_sha256(tcx, &slots, &verified.model)
        .ok_or_else(|| "fresh model contains an unrenderable slot key".to_owned())?;
    let cached = model_cache::CachedModel {
        model: verified.model.clone(),
        baseline_model: verified.baseline_model.clone(),
        a5_receipt: verified.receipt.clone(),
    };
    let cache_entry = if cacheable {
        model_cache::memo_put(&fp, &cached);
        model_cache::store(tcx, &program, &slots, &cached, a5_mode, attestation)
            .map(|path| path.display().to_string())
    } else {
        None
    };
    // Write-through on every real solve, so a bypassed gate sweep refreshes
    // what dev iteration reads next.
    model_cache::record_solve(model_cache::SolveProvenance {
        source: "real",
        cache_status: if model_cache::read_enabled() {
            "miss"
        } else {
            "bypass"
        },
        fingerprint: fp.clone(),
        model_sha256,
        cache_entry,
        solve_secs,
    });

    finish_decide(
        tcx,
        program,
        slots,
        mut_facts,
        verified.model,
        verified.retained_c9_plans,
        verified.receipt,
        DecisionAnalysisCarrier {
            origins: Some(origins),
            a5_mode,
            attestation,
            cache_load_wall_s: cache_started.elapsed().as_secs_f64(),
            origin_derivation_wall_s,
        },
        run_config,
        perturb,
    )
}

/// The phases after the solve, shared by the cached and real-solve paths.
///
/// Extracted so the two paths cannot drift: everything downstream of the model
/// runs from one body, and a cache hit differs from a real solve **only** in
/// where the model came from. That is what makes the byte-identity acceptance
/// meaningful rather than a coincidence.
fn finish_decide<'tcx>(
    tcx: TyCtxt<'tcx>,
    program: RustProgram<'tcx>,
    slots: CrateSlots,
    mut_facts: MutFacts,
    model: rustc_hash::FxHashMap<SlotRef, SlotKind>,
    mut retained_c9_plans: Vec<PlannedC9Mark>,
    a5_receipt: String,
    analysis: DecisionAnalysisCarrier,
    run_config: &EmissionRunConfig,
    perturb: impl FnOnce(&mut Vec<decision::Subject>),
) -> Result<(decision::DecisionTable, DecideCtx), String> {
    fn decision_is_safe(decision: &decision::Decision) -> bool {
        match decision {
            decision::Decision::Ref { .. }
            | decision::Decision::InferredRef { .. }
            | decision::Decision::Slice { .. }
            | decision::Decision::Opt { .. }
            | decision::Decision::Box(_) => true,
            decision::Decision::Degraded(_) => false,
        }
    }
    let box_facts = decision::box_facts::BoxOwnershipFacts::derive(&program, &slots, &model)?;
    let mut subjects = collect_subjects(tcx, &program, &mut_facts);
    // S3.1: the second universe. Appended rather than merged into
    // `collect_subjects` so the parameter census keeps measuring the parameter
    // predicate — a census whose denominator silently gained a population is not
    // the same instrument.
    subjects.extend(collect_local_subjects(tcx, &program, &mut_facts));

    // The freed-slot fact, stamped over BOTH universes from ONE walk of the
    // production recognizer — the same `free_sites` the S2-2 census asks. Two
    // properties follow by construction rather than by test: the parameter and
    // locals populations cannot acquire different freed-ness, and the gate
    // cannot disagree with the census about which bindings are freed.
    //
    // BEFORE `perturb`, so a test hook can perturb this field like any other.
    let freed =
        decision::FreedBindings::from_resolved(&free_sites(tcx, &program.functions).resolved);
    // U-2′'s length recovery, from the SAME construction recognizer the facts
    // join reports `len_class` from — one authority, so the flag and the census
    // cannot disagree about which subjects have a recovered length.
    let ctors = decision::construction::collect(tcx, &program.functions);
    for subject in &mut subjects {
        subject.freed_at = freed.site_of(subject.fn_did, subject.hir_id);
        subject.len_recovered = !matches!(subject.kind, decision::SubjectKind::Param { .. })
            && ctors
                .by_binding
                .get(&(subject.fn_did, subject.hir_id))
                .is_some_and(|c| matches!(c.len_class(), "array-len" | "alloc-count"));
        // **S3.2′-3** — the two facts the optional forms need, from the same
        // pass, for the same reason: one authority per fact.
        subject.null_init = ctors
            .by_binding
            .get(&(subject.fn_did, subject.hir_id))
            .is_some_and(|c| matches!(c, decision::construction::Construction::NullLit));
        // **The dissolution** — the class itself, from the same lookup the two
        // booleans above already make. A parameter has no construction site in
        // this crate, and the map has no entry for one, so this reads `None`
        // for the whole parameter universe without a `kind` test.
        subject.ctor = ctors
            .by_binding
            .get(&(subject.fn_did, subject.hir_id))
            .cloned();
        subject.mut_binding = matches!(
            tcx.hir_node(subject.hir_id),
            rustc_hir::Node::Pat(pat) if matches!(
                pat.kind,
                rustc_hir::PatKind::Binding(
                    rustc_hir::BindingMode(_, rustc_hir::Mutability::Mut),
                    ..
                )
            )
        );
    }

    perturb(&mut subjects);
    let facts = decision::emitability::collect(tcx, &program.functions);
    // S3.2′-2: the fatness LICENSE and the use-site rewrites, both consumed
    // here in the decision phase and nowhere later — E1's rule that no phase
    // after this one asks an analysis a question.
    let fat = fat_facts::FatFacts::from_program(&program);
    let names: rustc_hash::FxHashMap<_, _> = subjects
        .iter()
        .filter_map(|s| s.param_name.clone().map(|n| ((s.fn_did, s.hir_id), n)))
        .collect();
    // **S3.2′-2b.** The self-advance arm's two gates, decided where their facts
    // live: the NON-NEGATIVE sign verdict (the negative class is `SliceCursor`'s,
    // which S3.2′-5 owns) and a `mut` binding, which `p = …` needs. `SignFacts`
    // becomes load-bearing here — it shipped entry-validated at -3 and read by
    // nothing.
    let sign = sign_facts::SignFacts::from_program(&program);
    let mutable_of: rustc_hash::FxHashSet<_> = subjects
        .iter()
        .filter(|s| s.mutable)
        .map(|s| (s.fn_did, s.hir_id))
        .collect();
    let advance_ok: rustc_hash::FxHashSet<_> = subjects
        .iter()
        .filter(|s| s.mut_binding && !sign.may_be_negative(s.fn_did, s.local))
        .map(|s| (s.fn_did, s.hir_id))
        .collect();
    let slice_uses = decision::emitability::collect_slice_uses(
        tcx,
        &program.functions,
        &names,
        &mutable_of,
        &advance_ok,
    );
    // **S3.2′-3.** The accessor a subject's uses are rewritten through, chosen
    // per subject by the idiom rule (micro-plan §9c): `unwrap()` where the
    // optional is `Copy` or used once, `as_mut()` otherwise. It has to be
    // decided HERE because it depends on the use count, which is what the
    // collector is about to produce — so the count is taken from the raw walk
    // and the collector is handed the answer.
    //
    // `deref` and `index` differ by one `*`: `Option<&mut T>::as_mut().unwrap()`
    // is `&mut &mut T`, two derefs from the pointee, where `unwrap()` is one.
    let opt_accessors: rustc_hash::FxHashMap<_, _> = subjects
        .iter()
        .filter_map(|s| {
            let name = s.param_name.clone()?;
            let uses = decision::emitability::non_test_use_count(tcx, s.fn_did, s.hir_id);
            let as_mut = s.mutable && uses > 1;
            Some((
                (s.fn_did, s.hir_id),
                decision::emitability::Accessor {
                    deref: if as_mut {
                        format!("*{name}.as_mut().unwrap()")
                    } else {
                        format!("{name}.unwrap()")
                    },
                    index: if as_mut {
                        format!("{name}.as_mut().unwrap()")
                    } else {
                        format!("{name}.unwrap()")
                    },
                },
            ))
        })
        .collect();
    let opt_fat: rustc_hash::FxHashSet<_> = subjects
        .iter()
        .filter(|s| fat.is_array(s.fn_did, s.local))
        .map(|s| (s.fn_did, s.hir_id))
        .collect();
    let raw_boundary_argument_paths = facts.raw_boundary_argument_paths();
    let opt_uses = decision::emitability::collect_opt_uses(
        tcx,
        &program.functions,
        &names,
        &opt_accessors,
        &opt_fat,
        &raw_boundary_argument_paths,
    );
    let ctx_of = |gate, coconv, lifetime_eligibility, raw_boundary, exposure| decision::Ctx {
        tcx,
        model: &model,
        slots: &slots,
        facts: &facts,
        fat: &fat,
        sign: &sign,
        slice_uses: &slice_uses,
        opt_uses: &opt_uses,
        box_facts: &box_facts,
        constructions: &ctors,
        subjects: &subjects,
        gate,
        coconv,
        lifetime_eligibility,
        raw_boundary,
        exposure,
    };

    let web_started = std::time::Instant::now();
    let fnptr_web = decision::lifetime::derive_fn_ptr_web(&program, analysis.attestation);
    let fnptr_web_wall_s = web_started.elapsed().as_secs_f64();
    let exposure_seed = decision::exposure::ExposureSeed::derive(
        &program,
        &run_config.configured_exposure,
        fnptr_web.as_ref().ok(),
    )
    .map_err(|error| format!("raw-boundary exposure seed: {error:?}"))?;
    let surface_world_attested =
        analysis.attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph);
    let all_functions = if surface_world_attested {
        program.functions.iter().copied().collect()
    } else {
        rustc_hash::FxHashSet::default()
    };
    let preliminary_exposure = decision::exposure::ExposurePolicy::derive(
        &program,
        &exposure_seed,
        fnptr_web.as_ref().ok(),
        &all_functions,
    );

    // **S3.6-1 task 2 — the co-conversion classes.**
    //
    // Built from a SECOND run of the same ladder under
    // `RefGate::LiftAdaptable`, which answers *"what would convert if the gate
    // were lifted for the adaptable population?"*. The real `decide_one` and
    // never a replay of it: micro-plan §1b measured a `facts.tsv`-only replay
    // reporting 2,133 against a true 2,075, and retracted it.
    //
    // **The production table above is built first**, so nothing here can move a
    // decision — the S3.6-0 pattern that makes zero corpus delta structural
    // rather than lucky. ⚠ **This said "and from `BlockAll`"; that was true of
    // task 2 only.** Production has passed `LiftAdaptable` since S3.6-1 and the
    // `BlockAll` variant was deleted at M-3 (X-3). Task 3 is where the verdict
    // reaches a gate.
    let hypothetical = decision::decide(
        &ctx_of(
            decision::RefGate::LiftAdaptable,
            None,
            None,
            None,
            Some(&preliminary_exposure),
        ),
        &subjects,
    );
    // Escapes are computed BEFORE the classes now: P1 makes them a gate, not a
    // report, so `build` consumes them rather than the census reading them
    // alongside.
    let escapes = decision::co_conversion::escapes(tcx, &program.functions, &subjects);
    let lifetime_eligibility = decision::lifetime::derive_return_eligibility(
        &program,
        &slots,
        &model,
        analysis.origins.as_ref(),
        &hypothetical,
        &subjects,
        &ctors,
        &escapes,
        fnptr_web.clone(),
        fnptr_web_wall_s,
        &preliminary_exposure,
    );
    let e2_hypothetical = decision::decide(
        &ctx_of(
            decision::RefGate::LiftAdaptable,
            None,
            Some(&lifetime_eligibility),
            None,
            Some(&preliminary_exposure),
        ),
        &subjects,
    );
    let converting_signature_functions = e2_hypothetical
        .entries
        .iter()
        .filter(|(subject, decision)| {
            matches!(subject.kind, decision::SubjectKind::Param { .. })
                && decision_is_safe(decision)
        })
        .map(|(subject, _)| subject.fn_did)
        .collect::<rustc_hash::FxHashSet<_>>();
    let no_surface_functions = rustc_hash::FxHashSet::default();
    let candidate_surface_functions = if surface_world_attested {
        &converting_signature_functions
    } else {
        &no_surface_functions
    };
    let candidate_exposure = decision::exposure::ExposurePolicy::derive(
        &program,
        &exposure_seed,
        fnptr_web.as_ref().ok(),
        candidate_surface_functions,
    );
    let raw_boundary_sites_started = std::time::Instant::now();
    let raw_boundary_sites = decision::raw_boundary::RawBoundarySiteFacts::derive(&program, &facts);
    let raw_boundary_site_derivation_wall_s = raw_boundary_sites_started.elapsed().as_secs_f64();
    let retention_started = std::time::Instant::now();
    let retention = decision::raw_boundary::RetentionSummaries::derive(
        &program,
        analysis.origins.as_ref(),
        analysis.attestation,
    );
    let retention_fixpoint_wall_s = retention_started.elapsed().as_secs_f64();
    let raw_boundary_decision_started = std::time::Instant::now();
    let raw_boundary = decision::raw_boundary::RawBoundaryDispositionIndex::derive(
        &raw_boundary_sites,
        &retention,
        &e2_hypothetical,
        &facts,
    );
    let raw_boundary_decision_wall_s = raw_boundary_decision_started.elapsed().as_secs_f64();
    // Derive the attested A5 site index once, before PAIR, and pass the same
    // immutable object to the settled seam. No downstream arm reclassifies a
    // pair or pays the global setup twice.
    let a5_site_proofs = decision::a5_site_proof::A5SeamProofIndex::derive(
        &program,
        &slots,
        analysis.origins.as_ref(),
        analysis.a5_mode,
        analysis.attestation,
    );
    let coconv =
        decision::co_conversion::build_with_c9_marks_lifetimes_raw_boundary_and_pair_proofs(
            &facts,
            &subjects,
            &e2_hypothetical,
            &escapes,
            decision::co_conversion::OverlapRule::BlindOnly,
            &retained_c9_plans,
            &lifetime_eligibility,
            &raw_boundary,
            Some(&a5_site_proofs),
            &retention,
        );
    // **Production is decided AFTER the classes**, because step 2's gate reads
    // them. No cycle: the hypothetical above was decided with `None`.
    // **S3.6-1 step 3 — THE LIFT.** Production decides under `LiftAdaptable`
    // with the class verdict in hand: the adaptable population passes the
    // `referenced` gate, and the class gate then governs every node uniformly.
    // The pinned population still blocks inside `LiftAdaptable`.
    let mut table = decision::decide(
        &ctx_of(
            decision::RefGate::LiftAdaptable,
            Some(&coconv),
            Some(&lifetime_eligibility),
            Some(&raw_boundary),
            Some(&candidate_exposure),
        ),
        &subjects,
    );
    // Surface policies are provisional until the full ladder settles. A raw
    // wrapper or entry shim exists only when at least one signature subject
    // survives every arm; blocked functions retain their seed/web evidence but
    // receive NotApplicable and therefore no pointless surface edit.
    let settled_signature_functions = table
        .entries
        .iter()
        .filter(|(subject, decision)| {
            matches!(subject.kind, decision::SubjectKind::Param { .. })
                && decision_is_safe(decision)
        })
        .map(|(subject, _)| subject.fn_did)
        .collect::<rustc_hash::FxHashSet<_>>();
    let exposure = decision::exposure::ExposurePolicy::derive(
        &program,
        &exposure_seed,
        fnptr_web.as_ref().ok(),
        if surface_world_attested {
            &settled_signature_functions
        } else {
            &no_surface_functions
        },
    );
    table.exposure = Some(exposure.clone());

    // Use-edit nesting is a property of a PAIR of edits, so it cannot be seen by
    // `decide_one`, which is handed one subject at a time. Runs here, over the
    // finished table, where both the within-subject and the cross-subject case
    // are visible — a per-subject check left 15 of brotli's 17 collisions
    // standing, measured.
    decision::refuse_nested_use_edits(tcx, &mut table);

    let finalization_started = std::time::Instant::now();
    table.lifetime_plan = decision::lifetime::finalize(
        &program,
        analysis.origins.as_ref(),
        &lifetime_eligibility,
        &table,
    )?;
    let finalization_wall_s = finalization_started.elapsed().as_secs_f64();

    // **S3.6-1 seam adapters.** Runs AFTER every gate that can still refuse a
    // subject, including the nesting pass above: a seam is computed from the
    // forms both ends actually settle on, so a subject withdrawn later would
    // leave glue bridging to a form that no longer exists.
    let seam_started = std::time::Instant::now();
    table.seams = decision::seam::synthesize_with_raw_boundary(
        tcx,
        &facts,
        &subjects,
        &table,
        &retained_c9_plans,
        &a5_site_proofs,
        &raw_boundary,
        &coconv,
    );
    table.arm_requirements = derive_arm_requirements(&subjects, &coconv, &raw_boundary, &exposure);
    let seam_wall_s = seam_started.elapsed().as_secs_f64();
    let raw_boundary_render_wall_s = seam_started.elapsed().as_secs_f64();
    retained_c9_plans.retain(|mark| {
        let call_span = mark.call_span.source_callsite();
        let caller = tcx.def_path_str(mark.caller_did.to_def_id());
        let nested_reborrow = table.seams.edits.iter().any(|edit| {
            edit.caller_fn == caller
                && edit.family == decision::seam::SeamFamily::Reborrow
                && call_span.contains(edit.span.source_callsite())
        });
        let params = mark.key.pair.params();
        !nested_reborrow
            && [params.first(), params.second()].into_iter().all(|param| {
                let local = Local::from_usize(param as usize);
                table.entries.iter().any(|(subject, decision)| {
                    let is_ref = match decision {
                        decision::Decision::Ref { .. } | decision::Decision::InferredRef { .. } => {
                            true
                        }
                        decision::Decision::Slice { .. }
                        | decision::Decision::Opt { .. }
                        | decision::Decision::Box(_)
                        | decision::Decision::Degraded(_) => false,
                    };
                    subject.fn_did == mark.owner_did && subject.local == local && is_ref
                })
            })
    });
    table.c9_marks = retained_c9_plans.clone();
    let table = table;

    // Structural self-check: the table matches the subjects it was handed. NOT
    // the coverage gate — every comparison in it is against the collector's own
    // output.
    if let Err(why) = table.is_self_consistent_over(&subjects) {
        return Err(format!("decision table self-consistency: {why}"));
    }
    let receipt_started = std::time::Instant::now();
    let mut e2_artifacts =
        e2_artifacts_from_table(tcx, &table, &hypothetical, &lifetime_eligibility)?;
    e2_artifacts.timings = E2Timings {
        cache_load_wall_s: format!("{:.6}", analysis.cache_load_wall_s),
        origin_derivation_wall_s: format!("{:.6}", analysis.origin_derivation_wall_s),
        pb_web_wall_s: format!("{:.6}", lifetime_eligibility.web_wall_s()),
        eligibility_wall_s: format!("{:.6}", lifetime_eligibility.derive_wall_s()),
        finalization_wall_s: format!("{finalization_wall_s:.6}"),
        seam_wall_s: format!("{seam_wall_s:.6}"),
        ast_placement_wall_s: "pending".to_owned(),
        receipt_render_wall_s: format!("{:.6}", receipt_started.elapsed().as_secs_f64()),
        compiler_verification_wall_s: "pending".to_owned(),
    };
    let raw_boundary_receipt_started = std::time::Instant::now();
    let raw_boundary_artifacts = RawBoundaryArtifacts {
        exposure: exposure.receipts_tsv(),
        d4_edges: coconv.edge_receipts_tsv(tcx, &subjects),
        pairs: coconv.pair_receipts_tsv(tcx),
        addresses: raw_boundary.addresses_tsv(tcx),
        arm_outcomes: arm_outcomes_tsv(tcx, &subjects, &table, &coconv, &raw_boundary),
        edit_keys: String::from("edit_key\n"),
        sites: raw_boundary_sites.to_tsv(),
        retention: retention.to_tsv(),
        dispositions: raw_boundary.receipts_tsv(),
        subjects: raw_boundary_subjects_tsv(tcx, &hypothetical, &table, &coconv, &raw_boundary),
        atoms: raw_boundary.atoms_tsv(),
        atom_outcomes: {
            let mut out = String::from("outcome\treason\tatoms\n");
            for (atom, reason) in &table.seams.raw_boundary_edit_region_owned {
                out.push_str(&format!("edit-region-owned\t{reason}\t{atom}\n"));
            }
            out
        },
        final_reverts: String::from("kind\tidentity\tclass_id\n"),
        bridge_events: Vec::new(),
        class_costs: bridge_receipt::class_cost_header(),
        class_collisions: bridge_receipt::class_collision_header(),
        unresolved_classes: bridge_receipt::unresolved_class_header(),
        degraded_output_receipt: "not-applicable".to_owned(),
        per_arm_timers_status: "queued-no-free-column".to_owned(),
        timings: RawBoundaryTimings {
            site_derivation_wall_s: format!("{raw_boundary_site_derivation_wall_s:.6}"),
            retention_fixpoint_wall_s: format!("{retention_fixpoint_wall_s:.6}"),
            certificate_replay_wall_s: format!("{:.6}", raw_boundary.certificate_replay_wall_s()),
            decision_wall_s: format!("{raw_boundary_decision_wall_s:.6}"),
            render_wall_s: format!("{raw_boundary_render_wall_s:.6}"),
            receipt_wall_s: format!(
                "{:.6}",
                raw_boundary_receipt_started.elapsed().as_secs_f64()
            ),
            initial_verify_wall_s: "pending".to_owned(),
            atom_reverify_wall_s: "0.000000".to_owned(),
        },
    };

    // C.2: the in-process coverage gate is GONE. Its replacement is the
    // harness reconciliation in `coverage_recon`, driven from outside this
    // module — see `recon_fixtures` (C.1) and the corpus mode (C.4).
    //
    // Deleted rather than demoted to a smoke check: a weakened gate that still
    // READS like a coverage gate is the hazard itself. Four rounds of this
    // milestone were spent on apparatus that claimed more than it checked, and
    // leaving a demoted version behind preserves the claim while removing the
    // substance.
    Ok((
        table,
        DecideCtx {
            slots,
            model,
            facts,
            coconv,
            lifetime_eligibility,
            escapes,
            subjects,
            hypothetical,
            retained_c9_plans,
            a5_receipt,
            analysis,
            a5_site_proofs,
            box_facts,
            constructions: ctors,
            raw_boundary_sites,
            retention,
            raw_boundary,
            exposure,
            raw_boundary_artifacts,
            e2_artifacts,
        },
    ))
}

fn derive_arm_requirements(
    subjects: &[decision::Subject],
    coconv: &decision::co_conversion::CoConv,
    raw_boundary: &decision::raw_boundary::RawBoundaryDispositionIndex,
    exposure: &decision::exposure::ExposurePolicy,
) -> rustc_hash::FxHashMap<
    (rustc_hir::def_id::LocalDefId, rustc_hir::HirId),
    decision::RequiredArmSet,
> {
    use decision::{Arm, SubjectKind};
    subjects
        .iter()
        .map(|subject| {
            let key = (subject.fn_did, subject.hir_id);
            let mut required = coconv.required_arms(key);
            if matches!(subject.kind, SubjectKind::Param { .. })
                && !matches!(
                    exposure.plan(subject.fn_did),
                    decision::exposure::ExposureSurfacePlan::NotApplicable
                )
            {
                required.insert(Arm::Surface);
            }
            if raw_boundary
                .address_sites()
                .iter()
                .any(|site| site.node == key)
            {
                required.insert(Arm::Addr);
            }
            (key, required)
        })
        .collect()
}

fn arm_outcomes_tsv(
    tcx: TyCtxt<'_>,
    subjects: &[decision::Subject],
    table: &decision::DecisionTable,
    coconv: &decision::co_conversion::CoConv,
    raw_boundary: &decision::raw_boundary::RawBoundaryDispositionIndex,
) -> String {
    use decision::{Arm, ArmState, Decision, SubjectKind};

    let decisions = table
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect::<rustc_hash::FxHashMap<_, _>>();
    let mut rows = Vec::new();
    for subject in subjects {
        let key = (subject.fn_did, subject.hir_id);
        let required = table
            .arm_requirements
            .get(&key)
            .copied()
            .unwrap_or_default();

        let mut ready = required;
        let mut blocked_arm = None;
        let mut blocked_reason = "-".to_owned();
        if coconv.node_block(key).is_some() {
            let arm = if coconv.pair_sites().iter().any(|row| {
                row.subject == key && row.role == decision::co_conversion::PairRole::Blocked
            }) {
                Arm::Pair
            } else {
                Arm::D4
            };
            ready.remove(arm);
            blocked_arm = Some(arm);
            blocked_reason = coconv
                .node_block(key)
                .map_or_else(|| "-".to_owned(), |reason| reason.key().to_owned());
        }
        if let SubjectKind::Param { hir_index } = subject.kind
            && let Some(block) = table
                .seams
                .blocked
                .iter()
                .find(|block| block.callee == subject.fn_did && block.index == hir_index)
        {
            let arm = if block.block == decision::seam::SeamBlock::SiteOverlap {
                Arm::Pair
            } else {
                Arm::Glue
            };
            ready.remove(arm);
            if blocked_arm.is_none() {
                blocked_arm = Some(arm);
                blocked_reason = block.block.key().to_owned();
            }
        }
        if let Some(reason) = raw_boundary.block_reason(key) {
            ready.remove(Arm::C);
            if blocked_arm.is_none() {
                blocked_arm = Some(Arm::C);
                blocked_reason = reason.key().to_owned();
            }
        }
        let decision = decisions.get(&key).copied();
        let decision_degraded = decision.is_some_and(|decision| match decision {
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => false,
            Decision::Degraded(_) => true,
        });
        if decision_degraded && blocked_arm.is_none() {
            let arm = Arm::ALL
                .into_iter()
                .find(|&arm| required.contains(arm))
                .unwrap_or(Arm::D4);
            ready.remove(arm);
            blocked_arm = Some(arm);
            blocked_reason = "decision-degraded".to_owned();
        }
        let terminal = if blocked_arm.is_some() {
            "blocked"
        } else if decision_degraded {
            "typed-excluded"
        } else {
            "planned"
        };
        let states = Arm::ALL
            .into_iter()
            .map(|arm| {
                if !required.contains(arm) {
                    ArmState::NotRequired
                } else if ready.contains(arm) {
                    ArmState::Ready
                } else {
                    ArmState::Blocked
                }
                .key()
            })
            .collect::<Vec<_>>();
        let owner = tcx.def_path_str(subject.fn_did.to_def_id());
        let identity = subject.identity_key(&owner);
        rows.push((
            identity.clone(),
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                identity,
                owner,
                required.render(),
                ready.render(),
                ready.render(),
                states[0],
                states[1],
                states[2],
                states[3],
                states[4],
                states[5],
                terminal,
                blocked_arm.map_or("-", Arm::key),
                blocked_reason,
            ),
        ));
    }
    rows.sort_by(|left, right| left.0.cmp(&right.0));
    let mut out = String::from(
        "subject_identity\towner\trequired_arms\tready_arms\tapplied_arms\tsurface_state\td4_state\tc_state\tpair_state\tglue_state\taddr_state\tterminal\tblocking_arm\tblocking_reason\n",
    );
    for (_, row) in rows {
        out.push_str(&row);
    }
    out
}

fn raw_boundary_subjects_tsv(
    tcx: TyCtxt<'_>,
    hypothetical: &decision::DecisionTable,
    settled: &decision::DecisionTable,
    coconv: &decision::co_conversion::CoConv,
    raw_boundary: &decision::raw_boundary::RawBoundaryDispositionIndex,
) -> String {
    let decision_key = |decision: &decision::Decision| match decision {
        decision::Decision::Ref { .. } => "ref",
        decision::Decision::InferredRef { .. } => "inferred-ref",
        decision::Decision::Slice { .. } => "slice",
        decision::Decision::Opt { .. } => "optional",
        decision::Decision::Box(_) => "box",
        decision::Decision::Degraded(_) => "degraded",
    };
    let settled = settled
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect::<rustc_hash::FxHashMap<_, _>>();
    let mut rows = Vec::new();
    for (subject, hypothetical_decision) in &hypothetical.entries {
        let node = (subject.fn_did, subject.hir_id);
        let owner = tcx.def_path_str(subject.fn_did.to_def_id());
        let identity = subject.identity_key(&owner);
        let direct = raw_boundary.node_dispositions(node);
        let tiers = direct
            .iter()
            .map(|(_, disposition)| disposition.tier())
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
            .join(";");
        let class_block = coconv.class_block(node).map_or("-", |reason| reason.key());
        let node_block = coconv.node_block(node).map_or("-", |reason| reason.key());
        let settled_decision = settled.get(&node).copied();
        rows.push((
            identity.clone(),
            format!(
                "{identity}\t{owner}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                subject.local.as_u32(),
                match subject.kind {
                    decision::SubjectKind::Param { .. } => "param",
                    decision::SubjectKind::Local => "local",
                },
                decision_key(hypothetical_decision),
                settled_decision.map_or("missing", |decision| decision_key(decision)),
                direct.len(),
                if tiers.is_empty() { "-" } else { &tiers },
                u8::from(raw_boundary.opens_node(node)),
                coconv
                    .class_of(node)
                    .map_or_else(|| "-".to_owned(), |id| id.to_string()),
                u8::from(coconv.admits(node)),
                class_block,
                node_block,
                subject.ptr_depth,
            ),
        ));
    }
    rows.sort_by(|left, right| left.0.cmp(&right.0));
    let mut out = String::from(
        "subject_identity\towner\tmir_local\tsubject_kind\thypothetical\tsettled\tdirect_site_count\tdirect_tiers\traw_open\tclass_id\tclass_admits\tclass_block\tnode_block\tptr_depth\n",
    );
    for (_, row) in rows {
        out.push_str(&row);
    }
    out
}

/// **R1 — the pipeline's by-products, returned instead of recomputed.**
///
/// `facts_join_tsv` used to re-derive all of this itself, which meant the recon
/// worker ran the **BO solve twice per program**. That was affordable until the
/// fatness pass landed on top of it and three programs blew the 3,000 s cap.
/// The duplicate is removed by handing the caller what the pipeline already
/// built, not by making the second copy cheaper.
pub(crate) struct DecideCtx {
    slots: CrateSlots,
    model: rustc_hash::FxHashMap<SlotRef, SlotKind>,
    facts: decision::emitability::EmitabilityFacts,
    /// **S3.6-1 task 2.** Carried out with the table rather than recomputed by
    /// the census exporter, for R1's reason: the second derivation is what made
    /// the recon worker solve BO twice per program.
    coconv: decision::co_conversion::CoConv,
    lifetime_eligibility: decision::lifetime::LifetimeEligibility,
    /// The escape shapes, measured **separately and deliberately not gated**.
    ///
    /// The handoff's boundary, kept: the pinned-callee flow is the hazard this
    /// slice CREATES and is gated in `co_conversion`; a `static mut` store, a
    /// field store and a return are **pre-existing and orthogonal** — the
    /// already-emitting 562 carry the same shape, since a parameter of an
    /// uncalled function escapes just as readily. S3.6-1 multiplies the
    /// population ~4× but does not introduce the class. Measured here so it is
    /// neither folded in silently nor omitted silently.
    escapes: Vec<decision::co_conversion::Escape>,
    /// **P2 measurement.** The inputs the class builder consumed, kept so an
    /// alternative overlap rule can be priced without a second front-end pass —
    /// R1's rule, the one that stopped the recon worker solving BO twice.
    subjects: Vec<decision::Subject>,
    hypothetical: decision::DecisionTable,
    retained_c9_plans: Vec<PlannedC9Mark>,
    a5_receipt: String,
    analysis: DecisionAnalysisCarrier,
    a5_site_proofs: decision::a5_site_proof::A5SeamProofIndex,
    box_facts: decision::box_facts::BoxOwnershipFacts,
    constructions: decision::construction::ConstructionFacts,
    raw_boundary_sites: decision::raw_boundary::RawBoundarySiteFacts,
    retention: decision::raw_boundary::RetentionSummaries,
    raw_boundary: decision::raw_boundary::RawBoundaryDispositionIndex,
    exposure: decision::exposure::ExposurePolicy,
    raw_boundary_artifacts: RawBoundaryArtifacts,
    e2_artifacts: E2Artifacts,
}

impl DecideCtx {
    /// The escape records, for the witness that each shape is recognised.
    ///
    /// A test accessor rather than a `pub` field: the production consumer is
    /// `coconv_tsv`, and widening the field would invite a second reader that
    /// counts them a second way.
    #[cfg(test)]
    pub(crate) fn escapes_for_test(&self) -> &[decision::co_conversion::Escape] {
        &self.escapes
    }
}

pub(crate) struct BoxFactArtifacts {
    pub(crate) endpoints: String,
    pub(crate) version_sites: String,
    pub(crate) equations: String,
    pub(crate) subjects: String,
    pub(crate) receipt: String,
}

/// Render the production derive-on-load Box facts for external differential
/// controls. The derivation itself runs unconditionally in `finish_decide`;
/// this accessor does not create a second MIR walk.
pub(crate) fn box_fact_artifacts(tcx: TyCtxt<'_>) -> Result<BoxFactArtifacts, String> {
    let (_table, ctx) = decide_table_with_ctx(tcx)?;
    let mut subject_rows = ctx
        .subjects
        .iter()
        .filter(|subject| e1_subject_model_kind(&ctx, subject) == Some(SlotKind::Owning))
        .map(|subject| {
            let owner = tcx.def_path_str(subject.fn_did.to_def_id());
            let slot = ctx.slots.fn_local_slots[&subject.fn_did]
                .slot_for_local_depth(subject.local, 0)
                .expect("Owning subject has a depth-0 slot");
            let slot = decision::box_facts::slot_label(SlotRef::Local(subject.fn_did, slot));
            let arg_index = match subject.kind {
                decision::SubjectKind::Param { hir_index } => (hir_index + 1).to_string(),
                decision::SubjectKind::Local => "-".to_owned(),
            };
            (
                subject.identity_key(&owner),
                format!(
                    "{}\t{}\t{}\t{}\t{}\t{}",
                    subject.identity_key(&owner),
                    owner,
                    subject.local.as_u32(),
                    arg_index,
                    subject.ptr_depth,
                    slot,
                ),
            )
        })
        .collect::<Vec<_>>();
    subject_rows.sort_by(|left, right| left.0.cmp(&right.0));
    let mut subjects =
        String::from("subject_key\towner_fn\tmir_local\targ_index\tptr_depth\tslot\n");
    for (_, row) in subject_rows {
        subjects.push_str(&row);
        subjects.push('\n');
    }
    let receipt = format!(
        "box_fact_schema=box-facts-v1\nbox_fact_sha256={}\nbox_replay_error={}\nbox_endpoints={}\nbox_owning_subjects={}\n",
        ctx.box_facts.canonical_sha256(),
        ctx.box_facts.replay_error().unwrap_or("none"),
        ctx.box_facts.endpoints().len(),
        subjects.lines().skip(1).count(),
    );
    Ok(BoxFactArtifacts {
        endpoints: ctx.box_facts.endpoints_tsv(),
        version_sites: ctx.box_facts.version_sites_tsv(),
        equations: ctx.box_facts.equations_tsv(),
        subjects,
        receipt,
    })
}

pub(crate) struct BoxPlanArtifact {
    pub(crate) tsv: String,
    pub(crate) bridges: String,
    pub(crate) default_fill_candidates: String,
    pub(crate) endpoints: String,
    pub(crate) subjects: String,
    pub(crate) a5_global_setup_wall_s: f64,
    pub(crate) a5_pair_classification_wall_s: f64,
    pub(crate) a5_receipt_render_wall_s: f64,
}

fn box_mir_drop_policies(
    tcx: TyCtxt<'_>,
    table: &decision::DecisionTable,
    unplaceable: &[plan::Unplaceable],
) -> Vec<verify::BoxMirDropPolicy> {
    let unplaceable = unplaceable
        .iter()
        .map(|row| row.subject.as_str())
        .collect::<std::collections::BTreeSet<_>>();
    let mut policies = table
        .entries
        .iter()
        .filter_map(|(subject, decision)| {
            let plan = match decision {
                decision::Decision::Box(plan) => plan,
                decision::Decision::Ref { .. }
                | decision::Decision::InferredRef { .. }
                | decision::Decision::Slice { .. }
                | decision::Decision::Opt { .. }
                | decision::Decision::Degraded(_) => return None,
            };
            let function = tcx.def_path_str(subject.fn_did.to_def_id());
            let subject_key = subject.identity_key(&function);
            if unplaceable.contains(subject_key.as_str()) {
                return None;
            }
            Some(verify::BoxMirDropPolicy {
                subject: subject_key,
                function,
                local_name: subject.param_name.clone(),
                overwrite_sites: plan
                    .overwrite_spans
                    .iter()
                    .map(|span| decision::emitability::EmitabilityFacts::site(tcx, *span))
                    .collect(),
                retained_sink: plan.retained_sink,
                optional: plan.optional,
                implicit_scope_close: plan.implicit_scope_close,
            })
        })
        .collect::<Vec<_>>();
    policies.sort_by(|left, right| left.subject.cmp(&right.subject));
    policies
}

pub(crate) fn box_plan_artifact(tcx: TyCtxt<'_>) -> Result<BoxPlanArtifact, String> {
    let (table, ctx) = decide_table_with_ctx(tcx)?;
    let bridges = ctx.box_facts.construction_bridges_tsv(
        tcx,
        &ctx.subjects,
        &ctx.slots,
        &ctx.constructions,
        &ctx.model,
    );
    let endpoints = ctx.box_facts.endpoints_tsv();
    let default_fill_candidates = ctx.box_facts.default_fill_candidates_tsv(
        tcx,
        &ctx.subjects,
        &ctx.slots,
        &ctx.constructions,
        &ctx.model,
    );
    let a5_global_setup_wall_s = ctx.a5_site_proofs.global_setup_wall_s();
    let a5_pair_classification_wall_s = ctx.a5_site_proofs.pair_classification_wall_s();
    let receipt_started = std::time::Instant::now();
    let _receipt = seam_tsv_from_table(tcx, &table);
    let a5_receipt_render_wall_s = receipt_started.elapsed().as_secs_f64();
    let decisions = table
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.local), decision))
        .collect::<rustc_hash::FxHashMap<_, _>>();
    let mut rows = Vec::new();
    let mut subject_rows = Vec::new();
    for subject in ctx
        .subjects
        .iter()
        .filter(|subject| e1_subject_model_kind(&ctx, subject) == Some(SlotKind::Owning))
    {
        let owner = tcx.def_path_str(subject.fn_did.to_def_id());
        let subject_slot = ctx.slots.fn_local_slots[&subject.fn_did]
            .slot_for_local_depth(subject.local, 0)
            .expect("Owning subject has a depth-0 slot");
        let subject_slot =
            decision::box_facts::slot_label(SlotRef::Local(subject.fn_did, subject_slot));
        subject_rows.push((
            subject.identity_key(&owner),
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}",
                subject.identity_key(&owner),
                owner,
                subject.local.as_u32(),
                match subject.kind {
                    decision::SubjectKind::Param { hir_index } => (hir_index + 1).to_string(),
                    decision::SubjectKind::Local => "-".to_owned(),
                },
                subject.ptr_depth,
                subject_slot,
            ),
        ));
        let decision = decisions[&(subject.fn_did, subject.local)];
        let (outcome, reason, shape, optional, edits, deletes, fabricated, receipts) =
            match decision {
                decision::Decision::Box(plan) => (
                    "planned",
                    "-",
                    match plan.shape {
                        decision::box_facts::BoxShape::Sized => "sized",
                        decision::box_facts::BoxShape::Slice => "slice",
                    },
                    u8::from(plan.optional),
                    plan.expr_edits.len(),
                    plan.delete_statements.len(),
                    u8::from(plan.fabricated_extent),
                    plan.receipts.join(" | "),
                ),
                decision::Decision::Degraded(record) => (
                    "filtered",
                    record.reason.key(),
                    "-",
                    0,
                    0,
                    0,
                    0,
                    record.reason.detail(),
                ),
                decision::Decision::Ref { .. }
                | decision::Decision::InferredRef { .. }
                | decision::Decision::Slice { .. }
                | decision::Decision::Opt { .. } => {
                    return Err(format!(
                        "Owning subject {} received non-Box safe form",
                        subject.label
                    ));
                }
            };
        rows.push((
            subject.identity_key(&owner),
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                subject.identity_key(&owner),
                owner,
                subject.local.as_u32(),
                u8::from(matches!(subject.kind, decision::SubjectKind::Param { .. })),
                subject.ptr_depth,
                outcome,
                reason,
                shape,
                optional,
                edits,
                deletes,
                fabricated,
            ) + &format!("\t{}", receipts.replace(['\t', '\r', '\n'], " ")),
        ));
    }
    rows.sort_by(|left, right| left.0.cmp(&right.0));
    let mut output = String::from(
        "subject_key\towner_fn\tmir_local\tis_param\tptr_depth\toutcome\treason\tshape\toptional\texpr_edits\tstatement_deletes\tfabricated_extent\treceipts\n",
    );
    for (_, row) in rows {
        output.push_str(&row);
        output.push('\n');
    }
    subject_rows.sort_by(|left, right| left.0.cmp(&right.0));
    let mut subjects =
        String::from("subject_key\towner_fn\tmir_local\targ_index\tptr_depth\tslot\n");
    for (_, row) in subject_rows {
        subjects.push_str(&row);
        subjects.push('\n');
    }
    Ok(BoxPlanArtifact {
        tsv: output,
        bridges,
        default_fill_candidates,
        endpoints,
        subjects,
        a5_global_setup_wall_s,
        a5_pair_classification_wall_s,
        a5_receipt_render_wall_s,
    })
}

fn e1_subject_model_kind(ctx: &DecideCtx, subject: &decision::Subject) -> Option<SlotKind> {
    let universe = ctx.slots.fn_local_slots.get(&subject.fn_did)?;
    let slot = universe.slot_for_local_depth(subject.local, 0)?;
    ctx.model
        .get(&SlotRef::Local(subject.fn_did, slot))
        .copied()
}

fn e1_subject_family(
    model: Option<SlotKind>,
    decision: &decision::Decision,
    hypothetical: Option<&decision::Decision>,
) -> &'static str {
    match model {
        Some(SlotKind::Raw) => "raw",
        Some(SlotKind::Owning) => "box",
        None => "unmodeled",
        Some(SlotKind::Ref) => {
            let form = match decision {
                decision::Decision::Ref { .. } | decision::Decision::InferredRef { .. } => {
                    Some("ref")
                }
                decision::Decision::Slice { .. } => Some("slice"),
                decision::Decision::Opt { .. } => Some("optional"),
                decision::Decision::Box(_) => Some("box"),
                decision::Decision::Degraded(_) => match hypothetical {
                    Some(decision::Decision::Ref { .. })
                    | Some(decision::Decision::InferredRef { .. }) => Some("ref"),
                    Some(decision::Decision::Slice { .. }) => Some("slice"),
                    Some(decision::Decision::Opt { .. }) => Some("optional"),
                    Some(decision::Decision::Box(_)) => Some("box"),
                    Some(decision::Decision::Degraded(_)) | None => None,
                },
            };
            form.unwrap_or_else(|| match decision {
                decision::Decision::Degraded(record) => match record.reason {
                    decision::DegradeReason::SliceUseUnsupported
                    | decision::DegradeReason::SliceNegOrUnknownOffset
                    | decision::DegradeReason::SliceLocalConstruction => "slice",
                    decision::DegradeReason::NullInit
                    | decision::DegradeReason::OptUseUnsupported
                    | decision::DegradeReason::OptLocalConstruction
                    | decision::DegradeReason::OptNeedsMutBinding => "optional",
                    _ => "ref",
                },
                decision::Decision::Ref { .. }
                | decision::Decision::InferredRef { .. }
                | decision::Decision::Slice { .. }
                | decision::Decision::Opt { .. }
                | decision::Decision::Box(_) => unreachable!("emitting form mapped above"),
            })
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum E2TerminalDisposition<'a> {
    Planned,
    Failure(decision::lifetime::LifetimeFailure),
    SecondaryDegradation(&'a decision::Degradation),
    NotE2,
}

#[derive(Clone, Copy, Debug)]
struct E2DispositionInvariant<'a> {
    record: &'a decision::Degradation,
}

impl E2DispositionInvariant<'_> {
    fn key(self) -> &'static str {
        "lifetime-invariant-permitted-own-primary"
    }

    fn payload(self) -> (String, String) {
        (
            self.record.reason.key().to_owned(),
            self.record.reason.detail(),
        )
    }

    fn message(self, subject_key: &str) -> String {
        let (reason, detail) = self.payload();
        format!(
            "{}: subject={subject_key} reason={reason} detail={detail} site={}",
            self.key(),
            self.record.site.replace(['\t', '\r', '\n'], " "),
        )
    }
}

impl E2TerminalDisposition<'_> {
    fn key(self) -> &'static str {
        match self {
            Self::Planned => "planned",
            Self::Failure(failure) => failure.key(),
            Self::SecondaryDegradation(_) => "lifetime-secondary-degradation",
            Self::NotE2 => "not-e2",
        }
    }

    fn secondary_payload(self) -> (String, String) {
        match self {
            Self::SecondaryDegradation(record) => {
                (record.reason.key().to_owned(), record.reason.detail())
            }
            Self::Planned | Self::Failure(_) | Self::NotE2 => ("-".to_owned(), "-".to_owned()),
        }
    }
}

fn e2_terminal_disposition<'a>(
    planned: bool,
    has_lifetime_permit: bool,
    failure: Option<decision::lifetime::LifetimeFailure>,
    final_decision: &'a decision::Decision,
) -> Result<E2TerminalDisposition<'a>, E2DispositionInvariant<'a>> {
    use decision::lifetime::LifetimeFailure as F;

    // Fixed classification order: tranche holds and origin failures through
    // conflict are known before the final decision. A secondary blocker first
    // exists after that decision, and therefore precedes AST/seam placement.
    if let Some(
        failure @ (F::FieldHeld
        | F::ExternalContractAbsent
        | F::FnPtrWebHeld
        | F::OriginUnknown
        | F::OriginAbsent
        | F::OriginConflict),
    ) = failure
    {
        return Ok(E2TerminalDisposition::Failure(failure));
    }

    // ClassBlocked is collateral by construction: `via` belongs to a
    // classmate. Hoist it above the row-local permit test so a permit-less
    // class member preserves the secondary reason and payload.
    let class_coupling = match final_decision {
        decision::Decision::Degraded(record)
            if matches!(record.reason, decision::DegradeReason::ClassBlocked { .. }) =>
        {
            Some(record)
        }
        decision::Decision::Degraded(_)
        | decision::Decision::Ref { .. }
        | decision::Decision::InferredRef { .. }
        | decision::Decision::Slice { .. }
        | decision::Decision::Opt { .. }
        | decision::Decision::Box(_) => None,
    };
    if let Some(record) = class_coupling {
        return Ok(E2TerminalDisposition::SecondaryDegradation(record));
    }

    if has_lifetime_permit {
        match final_decision {
            decision::Decision::Degraded(record) => match &record.reason {
                decision::DegradeReason::SilentCoercion {
                    via: decision::co_conversion::BlockReason::EscapesViaReturn,
                } => return Err(E2DispositionInvariant { record }),
                // `ClassBlocked { via }` is class coupling: `via` belongs to a
                // classmate, so this row always reports a secondary blocker.
                _ => return Ok(E2TerminalDisposition::SecondaryDegradation(record)),
            },
            decision::Decision::Ref { .. }
            | decision::Decision::InferredRef { .. }
            | decision::Decision::Slice { .. }
            | decision::Decision::Opt { .. }
            | decision::Decision::Box(_) => {}
        }
    }

    if let Some(failure @ (F::AstUnplaceable | F::SeamIncompatible)) = failure {
        return Ok(E2TerminalDisposition::Failure(failure));
    }
    if planned {
        Ok(E2TerminalDisposition::Planned)
    } else {
        Ok(E2TerminalDisposition::NotE2)
    }
}

fn e2_artifacts_from_table(
    tcx: TyCtxt<'_>,
    table: &decision::DecisionTable,
    ordinary: &decision::DecisionTable,
    eligibility: &decision::lifetime::LifetimeEligibility,
) -> Result<E2Artifacts, String> {
    let ordinary = ordinary
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect::<rustc_hash::FxHashMap<_, _>>();
    let mut subject_rows = Vec::new();
    let mut failure_rows = Vec::new();
    for (subject, final_decision) in &table.entries {
        let key = (subject.fn_did, subject.hir_id);
        let owner = tcx.def_path_str(subject.fn_did.to_def_id());
        let subject_key = subject.identity_key(&owner);
        let plan = table.lifetime_plan.function(subject.fn_did);
        let has_lifetime_permit = eligibility.return_permit(key).is_some()
            || eligibility.inferred_permit(key).is_some()
            || eligibility.is_output_source(key);
        let planned = plan.is_some() && has_lifetime_permit;
        let fallback_failure = match final_decision {
            decision::Decision::Degraded(record) => match &record.reason {
                decision::DegradeReason::SilentCoercion { via }
                | decision::DegradeReason::ClassBlocked { via } => match via {
                    decision::co_conversion::BlockReason::EscapesViaFieldStore => {
                        Some(decision::lifetime::LifetimeFailure::FieldHeld)
                    }
                    decision::co_conversion::BlockReason::EscapesViaForeignArg
                    | decision::co_conversion::BlockReason::BorrowedIntoRawParam => {
                        Some(decision::lifetime::LifetimeFailure::ExternalContractAbsent)
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
        let failure = eligibility.failure(key).or(fallback_failure);
        let disposition =
            e2_terminal_disposition(planned, has_lifetime_permit, failure, final_decision)
                .map_err(|invariant| invariant.message(&subject_key))?;
        let (secondary_reason, secondary_detail) = disposition.secondary_payload();
        let ordinary_decision = ordinary.get(&key).copied();
        let ordinary_key = match ordinary_decision {
            Some(decision::Decision::Ref { .. }) => "ref",
            Some(decision::Decision::InferredRef { .. }) => "inferred-ref",
            Some(decision::Decision::Slice { .. }) => "slice",
            Some(decision::Decision::Opt { .. }) => "optional",
            Some(decision::Decision::Box(_)) => "box",
            Some(decision::Decision::Degraded(record)) => record.reason.key(),
            None => "missing",
        };
        let final_key = match final_decision {
            decision::Decision::Ref { .. } => "ref",
            decision::Decision::InferredRef { .. } => "inferred-ref",
            decision::Decision::Slice { .. } => "slice",
            decision::Decision::Opt { .. } => "optional",
            decision::Decision::Box(_) => "box",
            decision::Decision::Degraded(record) => record.reason.key(),
        };
        let digest = plan.map_or_else(|| "-".to_owned(), |plan| plan.digest());
        let justification = if planned {
            plan::Justification::LifetimePlan {
                digest: digest.clone(),
            }
        } else {
            plan::Justification::KindDecision { kind: "none" }
        };
        let justification_key = match justification {
            plan::Justification::LifetimePlan { .. } => "lifetime-plan",
            _ => "-",
        };
        let construction = subject
            .ctor
            .as_ref()
            .map_or("-", decision::construction::Construction::key);
        subject_rows.push(format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            subject_key,
            owner,
            subject.local.as_u32(),
            subject.ptr_depth,
            construction,
            ordinary_key,
            final_key,
            disposition.key(),
            justification_key,
            digest,
            secondary_reason,
            secondary_detail,
        ));
        if let Some(failure) = failure {
            failure_rows.push(format!(
                "{}\t{}\t{}\t{}",
                subject_key,
                owner,
                failure.key(),
                construction,
            ));
        }
    }
    subject_rows.sort();
    failure_rows.sort();

    let mut function_rows = table
        .lifetime_plan
        .functions()
        .map(|(did, function)| {
            format!(
                "{}\t{}\t{}\t{}\t{}",
                tcx.def_path_str(did.to_def_id()),
                function.digest(),
                function.sccs.len(),
                function.outlives.len(),
                function.receipt().replace('\n', " | "),
            )
        })
        .collect::<Vec<_>>();
    function_rows.sort();
    let mut pb_rows = Vec::new();
    for root in eligibility.web_roots() {
        pb_rows.push(format!("root\t{root}\tadjusted-fnptr"));
    }
    for (member, reason) in eligibility.web_members() {
        pb_rows.push(format!("closure\t{member}\t{reason}"));
    }
    pb_rows.sort();

    Ok(E2Artifacts {
        subjects: format!(
            "subject_key\towner_fn\tmir_local\tptr_depth\tconstruction\tordinary_decision\tfinal_decision\te2_disposition\tjustification\tlifetime_plan_digest\tsecondary_reason\tsecondary_reason_detail\n{}{}",
            subject_rows.join("\n"),
            if subject_rows.is_empty() { "" } else { "\n" },
        ),
        functions: format!(
            "function\tlifetime_plan_digest\tsccs\toutlives\tplan_receipt\n{}{}",
            function_rows.join("\n"),
            if function_rows.is_empty() { "" } else { "\n" },
        ),
        failures: format!(
            "subject_key\towner_fn\tfailure\tconstruction\n{}{}",
            failure_rows.join("\n"),
            if failure_rows.is_empty() { "" } else { "\n" },
        ),
        seams: seam_tsv_from_table(tcx, table),
        pb_web: format!(
            "unit\tfunction\treason\n{}{}",
            pb_rows.join("\n"),
            if pb_rows.is_empty() { "" } else { "\n" },
        ),
        timings: E2Timings::default(),
    })
}

/// Addendum 90's identity seed, produced inside the one E1 compiler callback
/// from the exact table and plan that emission consumes.  Classification of
/// first-pass reverts happens after verification, but no subject or model fact
/// is re-derived there.
fn e1_subject_seed_tsv(
    tcx: TyCtxt<'_>,
    table: &decision::DecisionTable,
    ctx: &DecideCtx,
    unplaceable: &[plan::Unplaceable],
) -> Result<String, String> {
    let mut unplaced = unplaceable
        .iter()
        .map(|row| (row.subject.as_str(), row.reason))
        .collect::<std::collections::BTreeMap<_, _>>();
    let hypothetical = ctx
        .hypothetical
        .entries
        .iter()
        .map(|(subject, decision)| {
            (
                (subject.fn_did.local_def_index.as_u32(), subject.local),
                decision,
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    let mut rows = Vec::new();
    for (subject, decision) in &table.entries {
        let owner = tcx.def_path_str(subject.fn_did.to_def_id());
        let key = subject.identity_key(&owner);
        let model = e1_subject_model_kind(ctx, subject);
        let family = e1_subject_family(
            model,
            decision,
            hypothetical
                .get(&(subject.fn_did.local_def_index.as_u32(), subject.local))
                .copied(),
        );
        let model_key = match model {
            Some(SlotKind::Raw) => "raw",
            Some(SlotKind::Ref) => "ref",
            Some(SlotKind::Owning) => "owning",
            None => "unmodeled",
        };
        let (decision_key, reason, reason_detail, site) = match decision {
            decision::Decision::Ref { .. } => (
                "ref",
                "-",
                "-".to_owned(),
                decision::emitability::EmitabilityFacts::site(tcx, subject.attribution_span()),
            ),
            decision::Decision::InferredRef { callee, .. } => (
                "inferred-ref",
                "-",
                tcx.def_path_str(callee.to_def_id()),
                decision::emitability::EmitabilityFacts::site(tcx, subject.attribution_span()),
            ),
            decision::Decision::Slice { .. } => (
                "slice",
                "-",
                "-".to_owned(),
                decision::emitability::EmitabilityFacts::site(tcx, subject.attribution_span()),
            ),
            decision::Decision::Opt { .. } => (
                "optional",
                "-",
                "-".to_owned(),
                decision::emitability::EmitabilityFacts::site(tcx, subject.attribution_span()),
            ),
            decision::Decision::Box(_) => (
                "box",
                "-",
                "-".to_owned(),
                decision::emitability::EmitabilityFacts::site(tcx, subject.attribution_span()),
            ),
            decision::Decision::Degraded(record) => (
                "degraded",
                record.reason.key(),
                record.reason.detail(),
                record.site.clone(),
            ),
        };
        let unplaced_reason = unplaced.remove(key.as_str());
        let emits = match decision {
            decision::Decision::Ref { .. }
            | decision::Decision::InferredRef { .. }
            | decision::Decision::Slice { .. }
            | decision::Decision::Opt { .. }
            | decision::Decision::Box(_) => true,
            decision::Decision::Degraded(_) => false,
        };
        let placed = emits && unplaced_reason.is_none();
        let exclusion = unplaced_reason
            .map(|reason| format!("unplaceable:{reason}"))
            .unwrap_or_else(|| "-".to_owned());
        let arg_index = match subject.kind {
            decision::SubjectKind::Param { hir_index } => (hir_index + 1).to_string(),
            decision::SubjectKind::Local => "-".to_owned(),
        };
        rows.push((
            key.clone(),
            format!(
                "{key}\t{owner}\t{}\t{arg_index}\t{}\t{family}\t{model_key}\t{decision_key}\t{reason}\t{}\t{}\t{}\t{exclusion}",
                subject.local.as_u32(),
                subject.ptr_depth,
                reason_detail.replace(['\t', '\r', '\n'], " "),
                site.replace(['\t', '\r', '\n'], " "),
                u8::from(placed),
            ),
        ));
    }
    if !unplaced.is_empty() {
        return Err(format!(
            "unplaceable subject(s) absent from decision table: {}",
            unplaced.keys().copied().collect::<Vec<_>>().join(",")
        ));
    }

    let universe = decision::universe::classify(tcx);
    for subject in universe.excluded_subjects {
        let owner = tcx.def_path_str(subject.did.to_def_id());
        let key = format!("{owner}::arg#{}@d0", subject.arg_index);
        rows.push((
            key.clone(),
            format!(
                "{key}\t{owner}\t{}\t{}\t{}\tunmodeled\tunmodeled\texcluded\t-\t-\t-\t0\t{}",
                subject.arg_index, subject.arg_index, subject.ptr_depth, subject.reason
            ),
        ));
    }
    rows.sort_by(|left, right| left.0.cmp(&right.0));
    let mut seen = std::collections::BTreeSet::new();
    for (key, _) in &rows {
        if !seen.insert(key) {
            return Err(format!("duplicate E1 subject seed identity {key}"));
        }
    }
    let mut out = String::from(
        "subject_key\towner_fn\tmir_local\targ_index\tptr_depth\tfamily\tmodel_kind\tdecision\treason\treason_detail\tsite\tplaced\texclusion\n",
    );
    for (_, row) in rows {
        out.push_str(&row);
        out.push('\n');
    }
    Ok(out)
}

/// **Producer A's artifact** for the crate in `tcx`.
///
/// The reconciliation's caller lives outside this module; this only emits.
#[allow(
    dead_code,
    reason = "producer A's artifact has no non-test consumer until the rewriter \
              is wired into the pipeline — the same standing as `rewrite_m1`. \
              Its test consumers are the C.1 reconciliation and C.4's corpus \
              mode. Targeted so dead_code stays live over everything reachable."
)]
pub(crate) fn artifact_rows(
    tcx: TyCtxt<'_>,
) -> Result<Vec<crate::coverage_recon::schema::Row>, String> {
    decide_table(tcx).map(|table| artifact::rows(tcx, &table))
}

/// **S3.2′-0 — the FACTS-SIDE JOIN.** One TSV row per subject, reporting the
/// analysis facts *directly*, before `decide_one`'s ordering collapses them.
///
/// # Why the artifact cannot answer these questions
///
/// `decide_one` returns at the **first** failing predicate, so its reason names
/// the earliest test that fired, not the set of facts that hold. Any
/// reason-field measurement therefore inherits that ordering and is blind to
/// every population filtered earlier — which is how a predicate reads as "never
/// fires" when it is merely never reached. That is the shape the locals-A1
/// defect wore, and the same trap made `degrade_reason == "kind-owning"` a
/// circular instrument for the box-candidate split.
///
/// | column | question |
/// |---|---|
/// | `is_param`, `annotated` | which population the subject belongs to |
/// | `slot` | does BO have a depth-0 slot — the **`no-slot`** cell, measured zero in **all four** populations |
/// | `kind` | BO's verdict, independent of whether the decision reached it |
/// | `raw_op` | the raw-only operation — the **op split** `key()` collapses |
/// | `ptr_cmp` | whether a comparison fact exists — the **`ptr-comparison` × locals** cell |
/// | `arg_shapes`, `arg_sites` | **S3.6-1**: what direct call sites supply at this parameter's position, and how many do. `-`/0 for locals and for uncalled functions |
///
/// `raw_op` and `ptr_cmp` are both reported per subject, so masking is readable
/// rather than inferred: the order-swap probe showed masking is real for
/// parameters and absent for locals, and this makes that visible per row.
///
/// MEASUREMENT ONLY. Nothing branches on it; no gate reads it.
#[allow(
    dead_code,
    reason = "S3.2'-0 measurement instrument; consumed by the corpus worker \
              behind an env var and by the test that pins its header. Not part \
              of the pipeline."
)]
pub(crate) fn facts_join_tsv(tcx: TyCtxt<'_>) -> Result<String, String> {
    let (table, ctx) = decide_table_with_ctx(tcx)?;
    let ctors = decision::construction::collect(tcx, &collect_program(tcx).functions);

    let mut out = String::from(
        "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\treferenced\tref_kinds\tref_class\tctor\tlen_class\tsize_expr\targ_shapes\targ_sites\n",
    );
    for (s, _decision) in &table.entries {
        let slot = ctx
            .slots
            .fn_local_slots
            .get(&s.fn_did)
            .and_then(|u| u.slot_for_local_depth(s.local, 0));
        let kind = slot
            .and_then(|id| ctx.model.get(&SlotRef::Local(s.fn_did, id)))
            .map(|k| match k {
                SlotKind::Ref => "ref",
                SlotKind::Raw => "raw",
                SlotKind::Owning => "owning",
            })
            .unwrap_or("-");
        let raw_op = ctx
            .facts
            .raw_only_uses
            .get(&(s.fn_did, s.hir_id))
            // FIRST, as before: the reported op and site are unchanged byte for
            // byte by the vector change.
            .and_then(|uses| uses.first())
            .map(|(op, _)| op.as_str())
            .unwrap_or("-");
        let is_param = matches!(s.kind, decision::SubjectKind::Param { .. });
        // **S3.6-1 task 0.** What the call sites actually supply at THIS
        // subject's parameter position, reported per subject and independent of
        // whether the decision reached the gate — the same discipline
        // `referenced` is reported under, and for the same reason: the reason
        // field names the earliest gate, never the whole blocker set.
        //
        // Locals get `-`/0: a local is not a parameter position, so no call
        // site supplies it. That is a different fact from "no call sites", and
        // conflating them would read 283 blocked locals as an adaptation market.
        let (arg_shapes, arg_sites) = match s.kind {
            decision::SubjectKind::Param { hir_index } => {
                let mut shapes: Vec<&'static str> = Vec::new();
                let mut sites = 0usize;
                for site in ctx.facts.call_args.get(&s.fn_did).into_iter().flatten() {
                    if let Some(arg) = site.args.iter().find(|a| a.index == hir_index) {
                        shapes.push(arg.shape.key());
                        sites += 1;
                    }
                }
                shapes.sort_unstable();
                shapes.dedup();
                let rendered = if shapes.is_empty() {
                    "-".to_owned()
                } else {
                    shapes.join(",")
                };
                (rendered, sites)
            }
            decision::SubjectKind::Local => ("-".to_owned(), 0),
        };
        let ctor = ctors.by_binding.get(&(s.fn_did, s.hir_id));
        let (ctor_key, len_class, size_expr) = match (is_param, ctor) {
            (true, _) => ("param", "param-no-site", String::new()),
            (false, Some(c)) => (
                c.key(),
                c.len_class(),
                match c {
                    decision::construction::Construction::Alloc { size, count, .. } => count
                        .clone()
                        .map_or_else(|| size.clone(), |n| format!("{n} x {size}")),
                    _ => String::new(),
                },
            ),
            (false, None) => ("-", "no-init", String::new()),
        };
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{kind}\t{raw_op}\t{}\t{}\t{}\t{}\t{ctor_key}\t{len_class}\t{size_expr}\t{arg_shapes}\t{arg_sites}\n",
            tcx.def_path_str(s.fn_did.to_def_id()),
            s.local.as_u32(),
            u8::from(is_param),
            u8::from(s.ty_span.is_some()),
            u8::from(slot.is_some()),
            u8::from(ctx.facts.ptr_comparisons.contains_key(&(s.fn_did, s.hir_id))),
            // **S3.2′-2 task 1.** A1's `referenced` gate, reported per subject
            // and INDEPENDENT of whether the decision reached it.
            //
            // It fires after `raw-pointer-operation`, so for the whole slice
            // market the reason field is silent about it and the market's true
            // size is unknowable from the artifact — which is exactly where the
            // raw-form reference blindness (291 params decided `Ref` behind
            // foreign-`DefId` extern blocks) hid. Measured, not inferred.
            //
            // A per-FUNCTION fact, restated per subject: the gate degrades every
            // subject of a referenced function, so a subject-level column is the
            // form the market join needs.
            u8::from(ctx.facts.referenced.contains_key(&s.fn_did)),
            // **S3.6-0** — the split, exported beside the boolean rather than
            // replacing it: every pinned number and every prior analysis of
            // `referenced` keeps meaning what it meant.
            match ctx.facts.referenced.get(&s.fn_did) {
                None => "-".to_owned(),
                Some(refs) => {
                    let mut kinds: Vec<_> = refs
                        .iter()
                        .map(|(k, _)| k.key())
                        .collect::<std::collections::BTreeSet<_>>()
                        .into_iter()
                        .collect();
                    kinds.sort_unstable();
                    kinds.join(",")
                }
            },
            match ctx.facts.referenced.get(&s.fn_did) {
                None => "-",
                Some(refs) if decision::emitability::RefKind::is_adaptable(refs) => "adaptable",
                Some(_) => "pinned",
            },
        ));
    }
    Ok(out)
}

/// **S3.6-1 task 2 — the CO-CONVERSION CLASS CENSUS.**
///
/// One row per class **member**, not per class. The per-class view is a
/// grouping of this one; the reverse is not true, and a per-class row carrying
/// a member list would either truncate a 104-node class or be unreadable —
/// silent caps being the thing this project's own rails forbid.
///
/// | column | question |
/// |---|---|
/// | `class_id`, `class_size` | which component, and how big |
/// | `admissible` | does the whole class convert |
/// | `class_block` | the reason the CLASS carries — one blocked member blocks it |
/// | `node_block` | the reason THIS member contributed, `-` if it contributed none |
/// | `sites` | how many direct call sites supply this parameter position |
/// | `escapes` | the escape shapes this member's binding carries, measured and **not gated** |
///
/// The two block columns are separate because they answer different questions:
/// the class one says why the component cannot convert, the node one says which
/// member is responsible. A census with only the first cannot be acted on, and
/// one with only the second cannot be summed.
///
/// MEASUREMENT ONLY. Nothing branches on it; no gate reads it.
#[allow(
    dead_code,
    reason = "S3.6-1 task 2 measurement instrument; consumed by the corpus \
              worker behind the artifact dir and by the test that pins its \
              header. Not part of the pipeline."
)]
pub(crate) fn coconv_tsv(tcx: TyCtxt<'_>) -> Result<String, String> {
    let (table, ctx) = decide_table_with_ctx(tcx)?;
    let mut escapes_of: rustc_hash::FxHashMap<_, Vec<&'static str>> =
        rustc_hash::FxHashMap::default();
    for escape in &ctx.escapes {
        let bucket = escapes_of.entry(escape.subject).or_default();
        if !bucket.contains(&escape.kind.key()) {
            bucket.push(escape.kind.key());
        }
    }
    // **P2 measurement columns.** The two candidate overlap rules, priced at
    // CLASS level by re-running the whole builder under each — not estimated
    // from position counts, because blocking a node blocks its class and a
    // per-node count is not a bound on a per-class outcome (the 831 → 788
    // lesson, banked).
    //
    // `storage_aliases` is deliberately absent: it is a MUST-alias relation, so
    // it can confirm an overlap and never refute one. Using it to PASS a pair
    // would be unsound, and was refused in advance by ruling.
    let blind_only = decision::co_conversion::build(
        &ctx.facts,
        &ctx.subjects,
        &ctx.hypothetical,
        &ctx.escapes,
        decision::co_conversion::OverlapRule::BlindOnly,
    );
    let all_pairs = decision::co_conversion::build(
        &ctx.facts,
        &ctx.subjects,
        &ctx.hypothetical,
        &ctx.escapes,
        decision::co_conversion::OverlapRule::AllPairs,
    );
    let mut out = String::from(
        "fn_path\tmir_local\tis_param\tclass_id\tclass_size\tadmissible\tclass_block\tnode_block\tmember_admissible\tedge_routes\trequired_arms\tsites\tescapes\tp2_blind_only\tp2_all_pairs\n",
    );
    for (s, _decision) in &table.entries {
        let key = (s.fn_did, s.hir_id);
        // Every subject gets a row, node or not: "this subject is not in any
        // class" is a fact the market join needs, and dropping such rows would
        // make the census's denominator its own node set — an instrument that
        // can only ever report full coverage of itself.
        let (class_id, class_size, admissible, class_block) = match ctx.coconv.class_of(key) {
            Some(id) => {
                let class = &ctx.coconv.classes()[id];
                (
                    id.to_string(),
                    class.members.len().to_string(),
                    u8::from(class.blocked.is_none()).to_string(),
                    class.blocked.map_or("-", |r| r.key()).to_owned(),
                )
            }
            None => (
                "-".to_owned(),
                "0".to_owned(),
                "-".to_owned(),
                "-".to_owned(),
            ),
        };
        let sites = match s.kind {
            decision::SubjectKind::Param { hir_index } => {
                ctx.facts.call_args.get(&s.fn_did).map_or(0, |sites| {
                    sites
                        .iter()
                        .filter(|site| site.args.iter().any(|a| a.index == hir_index))
                        .count()
                })
            }
            decision::SubjectKind::Local => 0,
        };
        let mut escapes = escapes_of.get(&key).cloned().unwrap_or_default();
        escapes.sort_unstable();
        // `-` where the subject is not a node under the production build, so
        // the two columns are never read as a verdict on a non-member.
        let verdict = |c: &decision::co_conversion::CoConv| match c.class_of(key) {
            Some(_) => u8::from(c.admits(key)).to_string(),
            None => "-".to_owned(),
        };
        let (p2_blind, p2_all) = (verdict(&blind_only), verdict(&all_pairs));
        let member_admissible = ctx.coconv.class_of(key).map_or_else(
            || "-".to_owned(),
            |_| u8::from(ctx.coconv.admits(key)).to_string(),
        );
        let edge_routes = ctx.coconv.edge_routes(key);
        let edge_routes = if edge_routes.is_empty() {
            "-".to_owned()
        } else {
            edge_routes.join(",")
        };
        let required_arms = ctx.coconv.required_arms(key).render();
        out.push_str(&format!(
            "{}\t{}\t{}\t{class_id}\t{class_size}\t{admissible}\t{class_block}\t{}\t{member_admissible}\t{edge_routes}\t{required_arms}\t{sites}\t{}\t{p2_blind}\t{p2_all}\n",
            tcx.def_path_str(s.fn_did.to_def_id()),
            s.local.as_u32(),
            u8::from(matches!(s.kind, decision::SubjectKind::Param { .. })),
            ctx.coconv.node_block(key).map_or("-", |r| r.key()),
            if escapes.is_empty() {
                "-".to_owned()
            } else {
                escapes.join(",")
            },
        ));
    }
    Ok(out)
}

/// Diagnostic-only view of the exact raw-boundary facts consumed by the final
/// decision. It returns production's carried artifacts; it does not re-derive
/// a site or read a control file.
#[cfg(test)]
pub(crate) fn raw_boundary_trace_artifacts(
    tcx: TyCtxt<'_>,
) -> Result<RawBoundaryArtifacts, String> {
    decide_table_with_ctx(tcx).map(|(_, ctx)| ctx.raw_boundary_artifacts)
}

/// **S2-2 — the freed-slot kind census.**
///
/// A leaked free's value kind is *observed, not designed* (backlog S2-2,
/// 2026-07-04): a leaked free can in principle settle `Ref`, and a freed-`Ref`
/// consumed by codegen is a reference to freed memory. The sink-slot collector
/// the item asked for was never built and **no `freed_ref` count has ever been
/// taken**. This takes it.
///
/// Reuses [`decide_table_with_ctx`] so no extra BO solve runs (R1), and is its
/// own pass so a failure here voids nothing else (R2).
///
/// # Why the argument shape is read at HIR
///
/// The cast arm — `free(p as *mut c_void)` versus `free(p)` on an already-`*mut
/// c_void` local — is a **syntactic** question, and only HIR answers it. It
/// matters because the cast is what A1 degrades on, which is the incidental
/// mitigation the reconciliation refused to treat as a discharge.
///
/// # No silent caps
///
/// An argument that does not resolve to a subject — `free((*s).field)`,
/// `free(arr[i])`, `free(f())` — is recorded with its cause, never dropped.
/// **An unresolved argument is not evidence of absence**, and a census that
/// counted only the easy shapes would under-report in exactly the direction
/// that makes the gate look discharged.
#[allow(
    dead_code,
    reason = "S2-2 measurement pass; consumed by the corpus worker behind the \
              artifact dir. Not part of the pipeline."
)]
pub(crate) fn freed_slots_tsv(tcx: TyCtxt<'_>) -> Result<String, String> {
    let (table, ctx) = decide_table_with_ctx(tcx)?;
    let program = collect_program(tcx);
    let sites = free_sites(tcx, &program.functions);
    freed_slots_tsv_from(tcx, table, ctx, sites)
}

const DEALLOCATORS: &[&str] = &["free", "xfree", "cfree", "g_free"];

/// Free sites, from HIR alone.
///
/// Split out of `freed_slots_tsv` so the substrate sanity census can ask
/// "do the deallocator recognizers still resolve?" **without** paying for a BO
/// solve — and, more importantly, so it asks that question of THIS recognizer
/// rather than a second copy of the name table that could drift from it.
pub(crate) struct FreeSites {
    /// `(hir_id_of_resolved_local, had_cast, call_span)` and the unresolved
    /// tally.
    ///
    /// The span is the **free call's**, not the binding's: it is what the
    /// freed-slot gate attributes a degradation to, exactly as A1's other gates
    /// attribute to the offending use rather than to the declaration.
    pub(crate) resolved: Vec<(rustc_hir::HirId, bool, rustc_span::Span)>,
    pub(crate) unresolved: Vec<UnresolvedFree>,
}

/// A free whose argument did not resolve to a binding — `free((*s).f)`,
/// `free(arr[i])`, `free(g())`.
///
/// Carries the bindings referenced **anywhere inside** the argument expression,
/// which is what the overlap check measures: the resolved arm can only see
/// arguments that *are* a binding, so a subject reachable through a field or an
/// index projection would otherwise be invisible to it. Collected here rather
/// than by a second walk so the overlap check and the census cannot disagree
/// about which sites are unresolved.
pub(crate) struct UnresolvedFree {
    pub(crate) cause: &'static str,
    pub(crate) site: String,
    pub(crate) locals: Vec<(rustc_hir::def_id::LocalDefId, rustc_hir::HirId)>,
}

pub(crate) fn free_sites(tcx: TyCtxt<'_>, fns: &[rustc_hir::def_id::LocalDefId]) -> FreeSites {
    use rustc_hir::intravisit::Visitor;

    /// Every binding a subexpression resolves to, in source order.
    struct Bindings(Vec<rustc_hir::HirId>);
    impl<'tcx> Visitor<'tcx> for Bindings {
        fn visit_expr(&mut self, e: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = &e.kind
                && let rustc_hir::def::Res::Local(hid) = path.res
            {
                self.0.push(hid);
            }
            rustc_hir::intravisit::walk_expr(self, e);
        }
    }

    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        out: &'a mut FreeSites,
    }
    impl V<'_, '_> {
        fn unresolved(
            &mut self,
            cause: &'static str,
            e: &rustc_hir::Expr<'_>,
            arg: &rustc_hir::Expr<'_>,
        ) {
            let mut bindings = Bindings(Vec::new());
            bindings.visit_expr(arg);
            let mut locals: Vec<_> = bindings
                .0
                .into_iter()
                .map(|hid| (hid.owner.def_id, hid))
                .collect();
            locals.sort_by_key(|(_, hid)| hid.local_id.as_u32());
            locals.dedup();
            self.out.unresolved.push(UnresolvedFree {
                cause,
                site: self.tcx.sess.source_map().span_to_diagnostic_string(e.span),
                locals,
            });
        }
    }
    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, e: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Call(callee, args) = &e.kind
                && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, p)) = &callee.kind
                && let Some(seg) = p.segments.last()
                && DEALLOCATORS.contains(&seg.ident.name.to_string().as_str())
                && let Some(arg) = args.first()
            {
                let mut inner = arg;
                let mut cast = false;
                while let rustc_hir::ExprKind::Cast(i, _) = &inner.kind {
                    cast = true;
                    inner = i;
                }
                match &inner.kind {
                    rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                        if let rustc_hir::def::Res::Local(hid) = path.res {
                            self.out.resolved.push((hid, cast, e.span));
                        } else {
                            self.unresolved("non-local-path", e, inner);
                        }
                    }
                    rustc_hir::ExprKind::Field(..) => self.unresolved("field", e, inner),
                    rustc_hir::ExprKind::Index(..) => self.unresolved("index", e, inner),
                    _ => self.unresolved("other", e, inner),
                }
            }
            rustc_hir::intravisit::walk_expr(self, e);
        }
    }

    let mut sites = FreeSites {
        resolved: Vec::new(),
        unresolved: Vec::new(),
    };
    for &fn_did in fns {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let mut v = V {
            tcx,
            out: &mut sites,
        };
        v.visit_body(tcx.hir_body(body_id));
    }
    sites
}

/// **The unresolved-overlap check.** Does any M1 subject hide inside a free
/// whose argument the census could not resolve?
///
/// The freed-slot gate keys on [`FreeSites::resolved`], so its completeness over
/// the free population is exactly the question of whether the *unresolved* arm
/// hides a subject. `free((*s).buf)` frees a struct field, not `s` — but if `s`
/// is itself a subject, a reader of the census cannot tell from the outside
/// whether the gate missed something, because the unresolved rows carry only a
/// cause and a span.
///
/// So this reports the join: every subject referenced **anywhere inside** an
/// unresolved free argument, with the site that referenced it. That is the
/// **broad** reading deliberately — the strict one ("the argument IS a subject")
/// is vacuously zero, since such an argument would have resolved and landed in
/// the other arm. A check that cannot fail is not a check.
///
/// Runs **no BO solve**: subject collection needs the program and `MutFacts`
/// only, so this is affordable in the recon worker beside the census.
pub(crate) struct FreeOverlap {
    /// One entry per (unresolved site × referenced subject) pair.
    pub(crate) hits: Vec<FreeOverlapHit>,
    /// Unresolved sites examined — the denominator, so a zero can be told apart
    /// from a walk that found nothing to examine.
    pub(crate) sites: usize,
}

pub(crate) struct FreeOverlapHit {
    pub(crate) cause: &'static str,
    pub(crate) site: String,
    pub(crate) fn_path: String,
    pub(crate) mir_local: u32,
    pub(crate) is_param: bool,
}

pub(crate) fn free_overlap(tcx: TyCtxt<'_>) -> FreeOverlap {
    let program = collect_program(tcx);
    let mut_facts = MutFacts::from_program(&program);
    let mut subjects = collect_subjects(tcx, &program, &mut_facts);
    subjects.extend(collect_local_subjects(tcx, &program, &mut_facts));
    let by_binding: rustc_hash::FxHashMap<_, _> =
        subjects.iter().map(|s| ((s.fn_did, s.hir_id), s)).collect();

    let sites = free_sites(tcx, &program.functions);
    let mut hits = Vec::new();
    for u in &sites.unresolved {
        for key in &u.locals {
            let Some(s) = by_binding.get(key) else {
                continue;
            };
            hits.push(FreeOverlapHit {
                cause: u.cause,
                site: u.site.clone(),
                fn_path: tcx.def_path_str(s.fn_did.to_def_id()),
                mir_local: s.local.as_u32(),
                is_param: matches!(s.kind, decision::SubjectKind::Param { .. }),
            });
        }
    }
    FreeOverlap {
        hits,
        sites: sites.unresolved.len(),
    }
}

/// §2's recognizer populations, from HIR alone.
///
/// `extern_resolver` rewrites `extern` items into `use` declarations, and the
/// callee-name recognizers key on the resolved path's last segment. A silent
/// collapse there is the migration's most dangerous failure mode, because every
/// downstream census would still run and would simply report fewer sites — a
/// number that looks like a finding rather than like a broken recognizer.
///
/// So this asks the production recognizers themselves: `free_sites` for the
/// deallocator family and `construction::collect` for the allocator family. It
/// deliberately does not restate either name table.
///
/// No solve — which is the point: the answer is needed BEFORE anything is
/// re-pinned, on both substrates, for all 20 programs.
pub(crate) struct SubstrateSanity {
    pub(crate) functions: usize,
    pub(crate) free_resolved: usize,
    pub(crate) free_unresolved: usize,
    pub(crate) alloc_bindings: usize,
    pub(crate) alloc_by_callee: Vec<(String, usize)>,
    pub(crate) ctor_bindings: usize,
    pub(crate) fn_paths: Vec<String>,
    pub(crate) referenced_fns: usize,
    pub(crate) referenced_paths: Vec<String>,
}

pub(crate) fn substrate_sanity(tcx: TyCtxt<'_>) -> SubstrateSanity {
    let program = collect_program(tcx);
    let sites = free_sites(tcx, &program.functions);
    let ctors = decision::construction::collect(tcx, &program.functions);
    // A1's `referenced` set: any path reference to a local fn, from ANY body
    // including static initializers. This is what gates CallSiteNotAdapted.
    let emit = decision::emitability::collect(tcx, &program.functions);

    let mut by_callee: std::collections::BTreeMap<String, usize> = Default::default();
    let mut alloc_bindings = 0;
    for c in ctors.by_binding.values() {
        if let decision::construction::Construction::Alloc { callee, .. } = c {
            alloc_bindings += 1;
            *by_callee.entry(callee.clone()).or_default() += 1;
        }
    }

    SubstrateSanity {
        functions: program.functions.len(),
        free_resolved: sites.resolved.len(),
        free_unresolved: sites.unresolved.len(),
        alloc_bindings,
        alloc_by_callee: by_callee.into_iter().collect(),
        ctor_bindings: ctors.by_binding.len(),
        referenced_fns: emit.referenced.len(),
        referenced_paths: {
            let mut v: Vec<_> = emit
                .referenced
                .keys()
                .map(|&f| tcx.def_path_str(f.to_def_id()))
                .collect();
            v.sort();
            v
        },
        fn_paths: {
            let mut v: Vec<_> = program
                .functions
                .iter()
                .map(|&f| tcx.def_path_str(f.to_def_id()))
                .collect();
            v.sort();
            v
        },
    }
}

fn freed_slots_tsv_from(
    tcx: TyCtxt<'_>,
    table: decision::DecisionTable,
    ctx: DecideCtx,
    sites: FreeSites,
) -> Result<String, String> {
    // Subjects indexed by their HIR binding — the same key A1 uses.
    let by_hir: rustc_hash::FxHashMap<_, _> = table
        .entries
        .iter()
        .map(|(s, _)| ((s.fn_did, s.hir_id), s))
        .collect();

    // The DECISION for each subject, keyed as the artifact keys it. S2-2's
    // hazard is a freed-`Ref` **consumed by codegen**, and the settled kind
    // alone does not say that: a subject can settle `Ref` in the model and
    // still be degraded at decision time (A1's as-cast arm, for one). Without
    // this column the census would answer a question adjacent to the gate's.
    let decision_of: rustc_hash::FxHashMap<_, _> = table
        .entries
        .iter()
        .map(|(s, d)| {
            (
                (s.fn_did, s.local),
                match d {
                    decision::Decision::Ref { .. } => "emitted-ref".to_owned(),
                    decision::Decision::InferredRef { .. } => "inferred-ref".to_owned(),
                    decision::Decision::Slice { .. } => "emitted-slice".to_owned(),
                    decision::Decision::Opt { slice, .. } => {
                        if *slice {
                            "emitted-opt-slice".to_owned()
                        } else {
                            "emitted-opt-ref".to_owned()
                        }
                    }
                    decision::Decision::Box(_) => "emitted-box".to_owned(),
                    decision::Decision::Degraded(r) => r.reason.key().to_owned(),
                },
            )
        })
        .collect();

    let mut out = String::from("fn_path\tmir_local\tcast\tkind\toutcome\tresolution\tdetail\n");
    for (hid, cast, _) in &sites.resolved {
        let owner = hid.owner.def_id;
        let Some(s) = by_hir.get(&(owner, *hid)) else {
            out.push_str(&format!(
                "-\t-\t{}\t-\t-\tunmapped\tno subject for the binding\n",
                u8::from(*cast)
            ));
            continue;
        };
        let kind = ctx
            .slots
            .fn_local_slots
            .get(&s.fn_did)
            .and_then(|u| u.slot_for_local_depth(s.local, 0))
            .and_then(|id| ctx.model.get(&SlotRef::Local(s.fn_did, id)))
            .map(|k| match k {
                SlotKind::Ref => "ref",
                SlotKind::Raw => "raw",
                SlotKind::Owning => "owning",
            })
            .unwrap_or("-");
        let outcome = decision_of
            .get(&(s.fn_did, s.local))
            .map_or("-", String::as_str);
        out.push_str(&format!(
            "{}\t{}\t{}\t{kind}\t{outcome}\tsubject\t\n",
            tcx.def_path_str(s.fn_did.to_def_id()),
            s.local.as_u32(),
            u8::from(*cast),
        ));
    }
    for u in &sites.unresolved {
        out.push_str(&format!(
            "-\t-\t-\t-\t-\tnon-local\t{} @ {}\n",
            u.cause, u.site
        ));
    }
    Ok(out)
}

/// **R2 — the fatness measurement, as its OWN pass.**
///
/// Split out for a reason measured the hard way: when fatness rode inside the
/// facts join, `fatness_analysis` panicking on one program took down the whole
/// invariant sweep, and three more programs timed out behind it. **One
/// program's analysis failure must not be able to void twenty programs of
/// invariant evidence.**
///
/// It runs **no BO solve** — fatness needs only the program — so it is far
/// cheaper than the pass it was extracted from, and its failure is now
/// recoverable at the call site rather than fatal to the sweep.
///
/// The raw lookup is reported, `None` included (`-`): ruling A-1′ maps `None`
/// to thin **at the decision layer**, never at measurement time. Instruments
/// measure the capture.
pub(crate) fn fatness_tsv(tcx: TyCtxt<'_>) -> Result<String, String> {
    let program = collect_program(tcx);
    let mut_facts = MutFacts::from_program(&program);
    let fat = fat_facts::FatFacts::from_program(&program);

    let mut subjects = collect_subjects(tcx, &program, &mut_facts);
    subjects.extend(collect_local_subjects(tcx, &program, &mut_facts));

    let mut out = String::from("fn_path\tmir_local\tis_param\tfatness\n");
    for s in &subjects {
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\n",
            tcx.def_path_str(s.fn_did.to_def_id()),
            s.local.as_u32(),
            u8::from(matches!(s.kind, decision::SubjectKind::Param { .. })),
            fat.render(s.fn_did, s.local),
        ));
    }
    Ok(out)
}

/// **S3.2′-3 task 0 — the use-class census, as its own pass.**
///
/// Runs **no BO solve** (the `fatness_tsv` precedent): the subject universe
/// needs the program and `MutFacts`, and the classification is HIR-only. So the
/// census is cheap enough to sweep on its own rather than riding the recon
/// worker, which keeps a measurement out of the gate's critical path.
///
/// One row per subject, counts parallel to [`use_census::CLASSES`]. The
/// split-back criterion is **not** evaluated here — see the module doc.
pub(crate) fn use_census_tsv(tcx: TyCtxt<'_>) -> Result<String, String> {
    let program = collect_program(tcx);
    let mut_facts = MutFacts::from_program(&program);
    let mut subjects = collect_subjects(tcx, &program, &mut_facts);
    subjects.extend(collect_local_subjects(tcx, &program, &mut_facts));

    let uses = use_census::collect(tcx, &program.functions);
    // **Task 2's other axis.** The sign rides the census artifact and NOT the
    // facts join, because §6 pins every `.facts.tsv` byte-identical except the
    // one column task 3 adds — a measurement must not spend a pre-registration
    // it did not ask for. The RAW capture is what lands here (`render`), so the
    // `None`-is-conservative decision policy never reaches an instrument.
    let sign = sign_facts::SignFacts::from_program(&program);

    let mut out = String::from("fn_path\tmir_local\tis_param\tsign\tn_uses");
    for c in use_census::CLASSES {
        out.push('\t');
        out.push_str(c);
    }
    out.push('\n');

    for s in &subjects {
        let counts = uses.get(&(s.fn_did, s.hir_id));
        let total: u32 = counts.map(|c| c.iter().sum()).unwrap_or(0);
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{total}",
            tcx.def_path_str(s.fn_did.to_def_id()),
            s.local.as_u32(),
            u8::from(matches!(s.kind, decision::SubjectKind::Param { .. })),
            sign.render(s.fn_did, s.local),
        ));
        for i in 0..use_census::CLASSES.len() {
            out.push('\t');
            out.push_str(&counts.map(|c| c[i]).unwrap_or(0).to_string());
        }
        out.push('\n');
    }
    Ok(out)
}

/// The golden inputs, for the out-of-module reconciliation harness (C.1).
///
/// Exposed as `(name, source)` pairs rather than by making `goldens` public:
/// the harness needs the INPUTS, not the golden machinery, and a narrower
/// surface is a narrower coupling.
#[cfg(test)]
pub(crate) fn goldens_for_reconciliation() -> Vec<(&'static str, &'static str)> {
    goldens::GOLDENS.iter().map(|g| (g.name, g.input)).collect()
}

/// The item-axis census, for the corpus harness (C.6's owed exclusion numbers).
#[cfg(test)]
pub(crate) fn classify_universe(tcx: TyCtxt<'_>) -> decision::universe::UniverseReport {
    decision::universe::classify(tcx)
}

/// Producer A's artifact with the span association SWAPPED between the first two
/// subjects of the crate — injected at the phase boundary, on the collector's
/// real `Subject` type, then driven through the real pipeline.
#[cfg(test)]
pub(crate) fn artifact_rows_span_swapped(
    tcx: TyCtxt<'_>,
) -> Result<Vec<crate::coverage_recon::schema::Row>, String> {
    decide_table_perturbed(tcx, |subjects| {
        if subjects.len() >= 2 {
            let (lo, hi) = (subjects[0].ty_span, subjects[1].ty_span);
            subjects[0].ty_span = hi;
            subjects[1].ty_span = lo;
        }
    })
    .map(|(table, _ctx)| artifact::rows(tcx, &table))
}

/// Every subject's decision with `ty_span` ERASED on the collector's real
/// output — the dissolution's terminal veto, driven through the real pipeline.
///
/// The veto is **corpus-unreachable by construction**: a parameter always has a
/// declared type, and an unannotated local cannot reach an emitting `Slice` or
/// `Opt` because the two local-construction gates fire first. That is exactly
/// why it needs a hook. A guard whose only evidence is that nothing has ever
/// hit it is not a guard, and the veto exists precisely so that "zero decision
/// flips" does not rest on those two gates staying where they are.
///
/// Injected at the phase boundary on `Subject`, like the span swap above,
/// rather than through a production seam — same reasoning, same zero
/// production-code cost.
#[cfg(test)]
pub(crate) fn decisions_with_ty_span_erased(
    tcx: TyCtxt<'_>,
) -> Result<Vec<crate::coverage_recon::schema::Row>, String> {
    decide_table_perturbed(tcx, |subjects| {
        for s in subjects {
            s.ty_span = None;
        }
    })
    .map(|(table, _ctx)| artifact::rows(tcx, &table))
}

/// **S3.6-1 — the SEAM COLUMN** (ruling item 3, 2026-08-11): every adapter site
/// and every refused one, with its reason.
///
/// A separate artifact rather than a column on `a.jsonl`, deliberately. A seam
/// is a property of an argument POSITION, not of a subject: one subject can be
/// served by many call sites and one site adapts many positions. Folding it into
/// the per-subject row would need an aggregation that discards exactly the thing
/// the ruling asks to see, and it would couple this to the reconciliation schema
/// producer B is compared against.
///
/// **Per-subject accounting is unchanged**, which this artifact makes checkable:
/// glue settles no subject, so a raw argument's own subject still reads
/// `degraded` with its own reason in `a.jsonl` while appearing here as an
/// adapted position.
pub(crate) fn seam_tsv(tcx: TyCtxt<'_>) -> Result<String, String> {
    let (table, _ctx) = decide_table_with_ctx(tcx)?;
    Ok(seam_tsv_from_table(tcx, &table))
}

/// Render adapter receipts from the table production already accepted. E1
/// calls this inside its sole compiler callback, so receipt production cannot
/// trigger a second analysis or solve.
fn seam_tsv_from_table(tcx: TyCtxt<'_>, table: &decision::DecisionTable) -> String {
    let sm = tcx.sess.source_map();
    let mut out = String::from(
        "kind\towner_fn\tfamily_or_reason\tsite\tlen_arm\tglue_shape\tcaller\tparam_index\ttemplate\tnull_arm\textent_arm\tadapter_key\tsource_shape\tcontext\tdestination\texpected_form\tfound_form\tcandidate_template\tpeer_pairs\troot_identity\tblind\toverlap_verdict\toverlap_reason\tresolved_call_location\ta5_peer_proofs\toverlap_a5_world\toverlap_a5_abi_guard\tlifetime_plan_digest\n",
    );
    for edit in &table.seams.edits {
        let family = match edit.family {
            decision::seam::SeamFamily::Safe => "safe",
            decision::seam::SeamFamily::Reborrow => "reborrow",
        };
        // The evidence arm rides the PLACED row (ruling B): the
        // bound-verification follow-up certifies or corrects each selection,
        // and it can only be surgical if a `following` selection is
        // distinguishable from a `preceding` one without re-deriving it.
        let arm = edit.len_arm.map_or("-", |a| a.key());
        // The glue SHAPE, so the placed population is countable by FORM and not
        // only by family. Without it "does the unwrap arm ever fire?" is
        // unanswerable from the census, and a golden could ratify a form with
        // zero market -- the -4/-5 precedent.
        //
        // **CARRIED, not inferred** — condition 5 of the option-A ruling
        // (2026-08-13). This was ten `starts_with`/`contains` tests over
        // `edit.replacement`, which is a string the ARGUMENT's own text
        // contributes to: an `Index0` adapter over an argument spelled `*q`
        // renders `Some(&*q[0])`, and the prefix test called that
        // `some_reborrow`. Same column, same ten-word vocabulary, and the shape
        // is now read from the decision rather than recovered from a rendering
        // of it. **Schema semantics changed; the column did not** — see
        // `GlueSpec::shape_key`, which reproduces the classifier's two ordering
        // quirks deliberately so the movement is only where it was wrong.
        let shape = edit.spec.shape_key();
        let site = sm.span_to_diagnostic_string(edit.span);
        let adapter_key = format!(
            "{}=>{}#{}@{}",
            edit.caller_fn, edit.owner_fn, edit.param_index, site
        );
        out.push_str(&format!(
            "placed\t{}\t{}\t{}\t{arm}\t{shape}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\tcall-argument\tparam:{}\t{}\t{}\t{}\t-\t{}\t{}",
            edit.owner_fn,
            family,
            site,
            edit.caller_fn,
            edit.param_index,
            edit.spec.template_key(),
            edit.spec.null_arm_key(),
            edit.spec.extent_arm_key(),
            adapter_key,
            edit.source_shape,
            edit.param_index,
            edit.expected.key(),
            edit.found.key(),
            edit.spec.template_key(),
            edit.root_identity,
            u8::from(edit.blind),
        ));
        push_overlap_columns(
            &mut out,
            edit.overlap.as_ref(),
            edit.lifetime_plan_digest.as_deref().unwrap_or("-"),
        );
    }
    // **`owner_fn` is the REVERT KEY on every row kind** (2026-08-12). It was
    // the callee on `placed` rows and the CALLER on these, so the two kinds
    // disagreed about what the column meant and no consumer could ask "which
    // functions would gain if this refusal went away" — the refusal costs the
    // CALLEE's conversion, which is why `SeamEdit::owner_fn` is the callee.
    // The caller is real information and moves to its own column rather than
    // being dropped.
    for blocked in &table.seams.blocked {
        let caller = tcx.def_path_str(blocked.caller.to_def_id());
        let callee = tcx.def_path_str(blocked.callee.to_def_id());
        let site = sm.span_to_diagnostic_string(blocked.span);
        let adapter_key = format!("{caller}=>{callee}#{}@{site}", blocked.index);
        let peers = if blocked.peers.is_empty() {
            "-".to_owned()
        } else {
            blocked
                .peers
                .iter()
                .map(decision::seam::PeerConflict::key)
                .collect::<Vec<_>>()
                .join(";")
        };
        out.push_str(&format!(
            "blocked\t{}\t{}\t{}\t-\t-\t{}\t{}\t{}\t{}\t{}\t{}\t{}\tcall-argument\tparam:{}\t{}\t{}\t{}\t{}\t{}\t{}",
            callee,
            blocked.block.key(),
            site,
            caller,
            blocked.index,
            blocked.candidate_template,
            blocked.null_arm,
            blocked.extent_arm,
            adapter_key,
            blocked.source_shape,
            blocked.index,
            blocked.expected.map_or("-", decision::seam::Form::key),
            blocked.found.map_or("-", decision::seam::Form::key),
            blocked.candidate_template,
            peers,
            blocked.root_identity,
            u8::from(blocked.blind),
        ));
        push_overlap_columns(&mut out, blocked.overlap.as_ref(), "-");
    }
    for edit in &table.seams.body_edits {
        let family = match edit.family {
            decision::seam::SeamFamily::Safe => "safe",
            decision::seam::SeamFamily::Reborrow => "reborrow",
        };
        let site = sm.span_to_diagnostic_string(edit.span);
        let adapter_key = format!("{}#{}@{}", edit.owner_fn, edit.context.key(), site);
        out.push_str(&format!(
            "body-placed\t{}\t{}\t{}\t-\t{}\t{}\t-\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t-\t{}\t{}",
            edit.owner_fn,
            family,
            site,
            edit.spec.shape_key(),
            edit.owner_fn,
            edit.spec.template_key(),
            edit.spec.null_arm_key(),
            edit.spec.extent_arm_key(),
            adapter_key,
            edit.source_shape,
            edit.context.key(),
            edit.destination,
            edit.expected.key(),
            edit.found.key(),
            edit.spec.template_key(),
            edit.root_identity,
            u8::from(edit.blind),
        ));
        push_overlap_columns(&mut out, None, "-");
    }
    for blocked in &table.seams.body_blocked {
        let site = sm.span_to_diagnostic_string(blocked.span);
        let adapter_key = format!("{}#{}@{}", blocked.owner_fn, blocked.context.key(), site);
        out.push_str(&format!(
            "body-blocked\t{}\t{}\t{}\t-\t-\t{}\t-\t{}\t-\t-\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t-\t{}\t{}",
            blocked.owner_fn,
            blocked.block.key(),
            site,
            blocked.owner_fn,
            blocked.candidate_template.unwrap_or("-"),
            adapter_key,
            blocked.source_shape,
            blocked.context.key(),
            blocked.destination,
            blocked.expected.key(),
            blocked.found.map_or("-", decision::seam::Form::key),
            blocked.candidate_template.unwrap_or("-"),
            blocked.root_identity,
            u8::from(blocked.blind),
        ));
        push_overlap_columns(&mut out, None, "-");
    }
    // Item 4a: companion-length coverage, one row per LENGTH-GATED POSITION.
    for (callee, index, evidence) in &table.seams.length_evidence {
        out.push_str(&format!(
            "lengated\t{callee}\t{}\t#{index}\t-\t-\t-\t{index}\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-",
            evidence.key()
        ));
        push_overlap_columns(&mut out, None, "-");
    }
    // Rule 1 (2026-08-11): a pair that fired with no census row is REPORTED.
    // The census is a prioritization overlay and has already been shown
    // incomplete twice; a silent adaptation would hide the third case.
    for (found, expected) in &table.seams.uncensused {
        out.push_str(&format!(
            "uncensused\t-\t{found:?} -> {expected:?}\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-\t-"
        ));
        push_overlap_columns(&mut out, None, "-");
    }
    for proof in &table.seams.overlap_proofs {
        let caller = tcx.def_path_str(proof.caller.to_def_id());
        let callee = tcx.def_path_str(proof.callee.to_def_id());
        let site = sm.span_to_diagnostic_string(proof.span);
        let adapter_key = format!("{caller}=>{callee}#{}@{site}", proof.index);
        out.push_str(&format!(
            "overlap-proof\t{callee}\t{}\t{site}\t-\t-\t{caller}\t{}\t{}\t-\t-\t{adapter_key}\t-\tcall-argument\tparam:{}\t-\t-\t{}\t-\t-\t-",
            proof.reason,
            proof.index,
            proof.candidate_template,
            proof.index,
            proof.candidate_template,
        ));
        push_overlap_columns(&mut out, Some(proof), "-");
    }
    out
}

fn push_overlap_columns(
    output: &mut String,
    proof: Option<&decision::seam::A5PositionProof>,
    lifetime_plan_digest: &str,
) {
    if let Some(proof) = proof {
        output.push_str(&format!(
            "\t{}\t{}\t{}\t{}\t{}\t{}\t{lifetime_plan_digest}\n",
            proof.verdict.key(),
            proof.reason,
            proof.locations,
            proof.peer_receipts,
            proof.world,
            proof.guard,
        ));
    } else {
        output.push_str(&format!("\t-\t-\t-\t-\t-\t-\t{lifetime_plan_digest}\n"));
    }
}

#[cfg(test)]
mod raw_boundary_atom_tests {
    use super::{
        AtomSelectionKind, EditSite, atom_surviving_edit_ids, bridge_receipt, edit_sites,
        select_atoms_on_original_lines, verify,
    };

    fn diag(line: usize, code: &str, related: &[usize]) -> verify::Diag {
        verify::Diag {
            file: "fixture.rs".to_owned(),
            line,
            message: "fixture diagnostic".to_owned(),
            direction: verify::Direction::Other,
            code: Some(code.to_owned()),
            related: related
                .iter()
                .map(|line| verify::RelatedDiag {
                    file: "fixture.rs".to_owned(),
                    line: *line,
                    message: "related fixture span".to_owned(),
                })
                .collect(),
        }
    }

    fn site(line: usize, id: &str, group: &[&str], covered: bool) -> EditSite {
        EditSite {
            owner_class: Some(bridge_receipt::SignatureClassId::of(
                rustc_hir::def_id::CRATE_DEF_ID,
            )),
            file: "fixture.rs".to_owned(),
            fn_path: "crate::f".to_owned(),
            lo_line: line,
            hi_line: line,
            edit_id: id.to_owned(),
            atom_ids: group.iter().map(|id| (*id).to_owned()).collect(),
            atom_covered: covered,
        }
    }

    /// RB-W11: an exact failure removes its dependency group and preserves an
    /// independent raw-boundary atom in the same function.
    #[test]
    fn rb_w11_exact_atom_preserves_independent_atom() {
        let sites = vec![
            site(2, "a-edit", &["a-site"], true),
            site(3, "b-edit", &["b-site"], true),
        ];
        let selected = select_atoms_on_original_lines(&[diag(2, "E0308", &[])], &sites);
        assert_eq!(selected.kind, AtomSelectionKind::Exact);
        assert_eq!(selected.atoms, ["a-site".to_owned()].into_iter().collect());
        assert_eq!(
            atom_surviving_edit_ids(&sites, &selected.atoms),
            ["b-edit".to_owned()].into_iter().collect()
        );
    }

    /// RB-W12: alias diagnostics consume primary and related spans as one
    /// canonically sorted group, never one side selected by traversal order.
    #[test]
    fn rb_w12_alias_diagnostic_reverts_related_atoms_as_one_group() {
        let sites = vec![
            site(2, "left", &["left-site"], true),
            site(5, "right", &["right-site"], true),
        ];
        let selected = select_atoms_on_original_lines(&[diag(2, "E0499", &[5])], &sites);
        assert_eq!(selected.kind, AtomSelectionKind::GroupAtomic);
        assert_eq!(
            selected.atoms,
            ["left-site".to_owned(), "right-site".to_owned()]
                .into_iter()
                .collect()
        );
    }

    /// RB-N4: an unowned or uncovered diagnostic cannot guess an atom.
    #[test]
    fn rb_n4_ambiguous_atom_routes_to_function_fallback() {
        let sites = vec![site(2, "known", &["known-site"], true)];
        let selected = select_atoms_on_original_lines(&[diag(9, "E0308", &[])], &sites);
        assert_eq!(selected.kind, AtomSelectionKind::Fallback);
        assert_eq!(selected.reason, "atom-attribution-ambiguous");
        assert!(selected.atoms.is_empty());
    }

    #[test]
    fn atom_w2_same_line_groups_use_one_deterministic_bisection() {
        let sites = vec![
            site(2, "a-edit", &["a-site"], true),
            site(2, "b-edit", &["b-site"], true),
        ];
        let selected = select_atoms_on_original_lines(&[diag(2, "E0308", &[])], &sites);
        assert_eq!(selected.kind, AtomSelectionKind::BisectGroup);
        assert_eq!(selected.atoms, ["a-site".to_owned()].into_iter().collect());
        assert_eq!(selected.reason, "atom-bounded-group-bisection");
    }

    #[test]
    fn atom_w1_edit_key_carries_subject_arms_kind_interval_and_digest() {
        use std::collections::BTreeMap;

        use crate::bo_rewriter::plan::{Edit, FileKey, Justification, Plan};

        let file = FileKey::Virtual("fixture.rs".to_owned());
        let mut plan = Plan::default();
        plan.by_file.insert(
            file.clone(),
            vec![Edit {
                lo: 0,
                hi: 1,
                replacement: "y".to_owned(),
                justification: Justification::KindDecision { kind: "Ref" },
                owner_class: Some(bridge_receipt::SignatureClassId::of(
                    rustc_hir::def_id::CRATE_DEF_ID,
                )),
                owner_path: "crate::f".to_owned(),
                atom_ids: vec!["atom-1".to_owned()],
                subject_id: "crate::f::p#1".to_owned(),
                required_arms: "d4+c+pair".to_owned(),
                edit_kind: "subject-declaration",
            }],
        );
        let rows = edit_sites(&plan, &BTreeMap::from([(file, "x".to_owned())]));
        let key = &rows[0].edit_id;
        assert!(
            key.contains("owner=crate::f|subject=crate::f::p#1"),
            "{key}"
        );
        assert!(
            key.contains("arms=d4+c+pair|kind=subject-declaration"),
            "{key}"
        );
        assert!(key.contains("interval=fixture.rs:0:1"), "{key}");
        assert!(key.contains("replacement_sha256="), "{key}");
    }

    #[test]
    fn raw_boundary_atom_reverify_is_bounded_to_one() {
        assert_eq!(super::MAX_ATOM_REVERIFIES, 1);
    }
}
