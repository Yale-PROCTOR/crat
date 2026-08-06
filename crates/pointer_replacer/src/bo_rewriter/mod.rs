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

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::Local,
    ty::{Mutability, TyCtxt, TyKind},
};

use crate::{
    analyses::borrow_ownership::{
        CrateCtxt, SlotKind, borrow_verify::verify_to_fixpoint, coherence::add_coherence,
        crate_slots::{CrateSlots, ptr_chain_depth},
        emit_crate_ownership_constraints, export::with_bo_export, mutability_facts::MutFacts,
        origins::compute_origins,
        solver::{KindSolver, SlotRef},
    },
    utils::rustc::RustProgram,
};

pub(crate) mod apply;
pub(crate) mod artifact;
pub(crate) mod decision;
pub(crate) mod fat_facts;
pub(crate) mod plan;
pub(crate) mod verify;

#[cfg(test)]
mod emit_tests;
#[cfg(test)]
mod goldens;
#[cfg(test)]
mod import_denylist;

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
        /// Every file the rewrite changed, keyed by file.
        files: std::collections::BTreeMap<plan::FileKey, String>,
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
    rewrite_core(::utils::compilation::str_to_input(input), None, MAX_REVERT_ROUNDS)
}

/// M1's **general** entry point: a crate rooted at `root`, rewritten into a temp
/// copy and gated there.
#[allow(
    dead_code,
    reason = "no caller until 0a.4's corpus smoke; `rewrite_m1` reaches the same               core through the other entry. Targeted here rather than               module-wide so the lint stays live over everything reachable."
)]
pub(crate) fn rewrite_m1_path(root: &std::path::Path) -> RewriteOutcome {
    rewrite_core(::utils::compilation::path_to_input(root), Some(root), MAX_REVERT_ROUNDS)
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
    candidates: &[String],
    base: &std::collections::BTreeSet<String>,
    mut compiles: impl FnMut(&std::collections::BTreeSet<String>) -> bool,
) -> (std::collections::BTreeSet<String>, usize) {
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
    )
}

#[cfg(test)]
pub(crate) fn rewrite_m1_path_with_cap(
    root: &std::path::Path,
    max_rounds: usize,
) -> RewriteOutcome {
    rewrite_core(::utils::compilation::path_to_input(root), Some(root), max_rounds)
}

fn rewrite_core(
    input: rustc_session::config::Input,
    tree_base: Option<&std::path::Path>,
    max_rounds: usize,
) -> RewriteOutcome {
    rewrite_core_injected(input, tree_base, max_rounds, &|_| {}, false)
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
) -> RewriteOutcome {
    // The string entry's original text, so a baseline exists for it too.
    let virtual_original = match &input {
        rustc_session::config::Input::Str { input, .. } => Some(input.clone()),
        rustc_session::config::Input::File(_) => None,
    };
    let root_hint = tree_base;
    let result = ::utils::compilation::run_compiler_on_input(input, |tcx| {
        let mut table = decide_table(tcx)?;
        inject(&mut table);
        let table = table;
        let emission = emit_files(tcx, &table, &rustc_hash::FxHashSet::default())?;
        let (emission_plan, emission_texts) = (emission.plan.clone(), emission.texts.clone());
        // Structural gate: rollbacks must be zero.
        if !emission.rollbacks.is_empty() {
            return Err(format!(
                "apply rolled back {} edit(s): {:?}",
                emission.rollbacks.len(),
                emission.rollbacks.iter().map(|r| r.reason).collect::<Vec<_>>()
            ));
        }
        let degradations: Vec<decision::Degradation> = table.degradations().cloned().collect();
        let mut emitted_sites: Vec<EmittedSite> = Vec::new();
        // One entry per EMITTED SUBJECT (not per function), so a revert can move
        // exactly the right number of subjects from emitted to degraded and the
        // accounting identity survives the loop.
        let mut emitted_subjects: Vec<(String, String, String)> = Vec::new();
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
                decision::Decision::Ref { .. } => {}
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
            emitted_subjects.push((
                owner.clone(),
                key,
                decision::emitability::EmitabilityFacts::site(tcx, subject.attribution_span()),
            ));
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
        Ok((
            emission.files,
            emission_plan,
            emission_texts,
            emission.unplaceable,
            degradations,
            // NOT a count of `Ref` DECISIONS (which is what the deleted
            // `emitted_count()` computed). This
            // is the placed set, already filtered above, so `emitted` names
            // what the rewrite actually did to the source.
            emitted_subjects.len(),
            decision::universe::classify(tcx).excluded,
            root_text,
            emitted_sites,
            emitted_subjects,
        ))
    });

    match result {
        Ok(Ok((
            files,
            emission_plan,
            emission_texts,
            unplaceable,
            degradations,
            emitted_count,
            excluded,
            root_text,
            emitted_sites,
            emitted_subjects,
        ))) => {
            // Built ONCE. Every return below goes through `facts.emitted(..)`
            // or `facts.degraded(..)`; no site hand-fills a field.
            let site_owners: std::collections::BTreeSet<&str> =
                emitted_sites.iter().map(|s| s.fn_path.as_str()).collect();
            let attribution_blind = emission_plan
                .by_file
                .values()
                .flatten()
                .map(|edit| edit.owner_fn.as_str())
                .collect::<std::collections::BTreeSet<_>>()
                .difference(&site_owners)
                .count();
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
            let mut baseline: Option<verify::Baseline> = None;
            let mut facts = OutcomeFacts {
                degradations,
                excluded,
                emitted_count,
                files_touched: files.len(),
                reverted_count: 0,
                emitted_sites,
                unplaceable,
                bisect_probes: 0,
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
            };
            let crate_dir = tree_base.and_then(|root| root.parent()).map(|d| d.to_path_buf());
            let mut reverted: std::collections::BTreeSet<String> =
                std::collections::BTreeSet::new();
            let mut files = files;
            let mut rounds = 0usize;
            let mut previous_errors: Option<usize> = None;
            let mut probe_secs = 0.0f64;
            let escalation: Option<String>;

            loop {
                let materialized = match tree_base {
                    Some(root) => verify::materialize(root, &files),
                    None => verify::materialize_single_file(&root_text),
                };
                let staged = match materialized {
                    Ok(staged) => staged,
                    Err(err) => {
                        facts.files_touched = files.len();
                        facts.reverted_count = reverted.len();
                        return facts
                            .degraded(format!("could not materialize the emitted crate: {err}"));
                    }
                };
                let probe_started = std::time::Instant::now();
                let diagnosis = verify::diagnose_crate(staged.root());
                probe_secs = probe_secs.max(probe_started.elapsed().as_secs_f64());
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
                    facts.observed_root =
                        Some(staged.root().parent().unwrap_or(staged.root()).to_path_buf());
                    facts.files_touched = files.len();
                    return facts.degraded("probe-only: first diagnose recorded".to_owned());
                }
                // GATE MACHINERY STARTS HERE. Everything below the probe
                // return belongs to the differential; the baseline compile is
                // the first of it, computed once and reused across rounds.
                let baseline = baseline.get_or_insert_with(|| compute_baseline());
                facts.baseline_keys = baseline.keys.values().sum();
                facts.baseline_errors = baseline.errors;
                facts.baseline_msg_env = baseline.messages_embedding_root;
                let observed_root = staged.root().parent().unwrap_or(staged.root()).to_path_buf();
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
                if novel.is_empty() && novel_errors == 0 {
                    let source = std::fs::read_to_string(staged.root()).unwrap_or_default();
                    let (kept, taken): (Vec<_>, Vec<_>) = emitted_subjects
                        .iter()
                        .partition(|(owner, _, _)| !reverted.contains(owner));
                    // ACCOUNTING: a reverted subject moves from emitted to
                    // degraded under its OWN reason key, so
                    // `emitted_final + degraded == row count` survives the loop.
                    for (_, subject, site) in &taken {
                        facts.degradations.push(decision::Degradation {
                            subject: subject.clone(),
                            site: site.clone(),
                            reason: decision::DegradeReason::RevertedAfterVerifyFailure,
                        });
                    }
                    facts.emitted_count = kept.len();
                    facts.reverted_count = taken.len();
                    facts.files_touched = files.len();
                    return facts.emitted(source, files);
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
                    &observed_root,
                    &facts.emitted_sites,
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
                let (next_files, rollbacks) = render(&emission_plan, &emission_texts, &reverted);
                if !rollbacks.is_empty() {
                    escalation = Some(format!(
                        "escalation-required: re-render rolled back {} edit(s)",
                        rollbacks.len()
                    ));
                    break;
                }
                files = next_files;
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
            let candidates: Vec<String> = emission_plan
                .by_file
                .values()
                .flatten()
                .map(|edit| edit.owner_fn.clone())
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
                facts.files_touched = files.len();
                facts.reverted_count = reverted.len();
                facts.escalated = Some(escalation.clone());
                return facts.degraded(format!(
                    "escalation-deferred: {escalation}; bisect needs ~{projected} probe(s)                          at ~{probe_secs:.1}s each against a {budget_secs:.0}s budget, with                          {} function(s) already reverted",
                    reverted.len()
                ));
            }

            let (final_reverted, probes) = bisect(&candidates, &reverted, |trial| {
                let (trial_files, rollbacks) = render(&emission_plan, &emission_texts, trial);
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

            let (final_files, rollbacks) =
                render(&emission_plan, &emission_texts, &final_reverted);
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
                        let final_diag = verify::diagnose_crate(staged.root());
                        let final_root =
                            staged.root().parent().unwrap_or(staged.root());
                        baseline.novel(&final_diag.diags, final_root).is_empty()
                            && final_diag.errors.saturating_sub(baseline.errors) == 0
                    } =>
                {
                    let source = std::fs::read_to_string(staged.root()).unwrap_or_default();
                    let (kept, taken): (Vec<_>, Vec<_>) = emitted_subjects
                        .iter()
                        .partition(|(owner, _, _)| !final_reverted.contains(owner));
                    for (_, subject, site) in &taken {
                        facts.degradations.push(decision::Degradation {
                            subject: subject.clone(),
                            site: site.clone(),
                            reason: decision::DegradeReason::RevertedAfterVerifyFailure,
                        });
                    }
                    facts.emitted_count = kept.len();
                    facts.reverted_count = taken.len();
                    facts.files_touched = final_files.len();
                    facts.bisect_probes = probes;
                    facts.escalated = Some(escalation);
                    facts.emitted(source, final_files)
                }
                _ => {
                    facts.files_touched = files.len();
                    facts.reverted_count = final_reverted.len();
                    facts.bisect_probes = probes;
                    facts.escalated = Some(escalation.clone());
                    facts.degraded(format!("{escalation}; bisect did not recover the crate"))
                }
            }
        }
        // Nothing was decided, so the facts are genuinely empty here — the one
        // place a zero is the measurement rather than an omission.
        Ok(Err(reason)) => OutcomeFacts::default().degraded(reason),
        Err(_) => {
            OutcomeFacts::default().degraded("input crate did not compile".to_owned())
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
/// belongs to the pattern. Both carry `ty_span: None` and degrade with
/// [`decision::DegradeReason::NoDeclaredType`].
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
        let mut entries: std::collections::BTreeMap<Local, Vec<&rustc_middle::mir::VarDebugInfo<'_>>> =
            std::collections::BTreeMap::new();
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
                // component. `decide_one` degrades on `ty_span.is_none()` before
                // it ever consults the shape.
                None => (decision::DeclShape::Other, None, None),
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
            RewriteOutcome::Emitted { first_diags, observed_root, .. }
            | RewriteOutcome::Degraded { first_diags, observed_root, .. } => {
                (observed_root, first_diags)
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
            degradations: self.degradations,
            emitted_count: self.emitted_count,
            excluded: self.excluded,
            emitted_sites: self.emitted_sites,
            bisect_probes: self.bisect_probes,
            escalated: self.escalated,
            unplaceable: self.unplaceable,
            reverted_count: self.reverted_count,
            attribution_blind: self.attribution_blind,
            first_diags: self.first_diags,
            observed_root: self.observed_root,
            baseline_keys: self.baseline_keys,
            baseline_errors: self.baseline_errors,
            baseline_msg_env: self.baseline_msg_env,
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
            unplaceable: self.unplaceable,
            reverted_count: self.reverted_count,
            attribution_blind: self.attribution_blind,
            first_diags: self.first_diags,
            observed_root: self.observed_root,
            baseline_keys: self.baseline_keys,
            baseline_errors: self.baseline_errors,
            baseline_msg_env: self.baseline_msg_env,
        }
    }
}

/// Hard ceiling on revert rounds. Paired with the no-progress detector, never
/// relied on alone: a cap that fires is a loop that stopped being understood.
const MAX_REVERT_ROUNDS: usize = 8;

/// Functions whose own rewrite is implicated by these diagnostics.
///
/// Attribution is by SPAN CONTAINMENT against each rewritten subject's own
/// function. Direction is recorded on the diagnostic and reported, but is
/// deliberately NOT consulted here: it is diagnostic, not a router — the
/// no-progress detector decides escalation, so a mis-attribution is caught by
/// measurement rather than pre-empted by a heuristic that could be wrong.
fn attribute(
    diags: &[verify::Diag],
    observed_root: &std::path::Path,
    sites: &[EmittedSite],
    original_root: &std::path::Path,
) -> std::collections::BTreeSet<String> {
    // The SAME canonicalizer as the differential gate, each side against its own
    // root: sites were recorded in the original tree, diagnostics come from the
    // temp copy. A second normalization here would drift attribution away from
    // the gate — the same defect class, one layer over.
    let single_file = {
        let mut files: Vec<&str> = sites.iter().map(|s| s.file.as_str()).collect();
        files.sort_unstable();
        files.dedup();
        files.len() <= 1
    };
    let mut owners = std::collections::BTreeSet::new();
    for diag in diags {
        let diag_rel = verify::crate_relative(&diag.file, observed_root);
        for site in sites {
            let same_file =
                single_file || verify::crate_relative(&site.file, original_root) == diag_rel;
            if same_file && site.lo_line <= diag.line && diag.line <= site.hi_line {
                owners.insert(site.fn_path.clone());
            }
        }
    }
    owners
}

/// Where a rewritten subject's own function lives, for attributing a verify
/// diagnostic to it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EmittedSite {
    pub file: String,
    pub fn_path: String,
    pub lo_line: usize,
    pub hi_line: usize,
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
pub(crate) fn render(
    planned: &plan::Plan,
    texts: &std::collections::BTreeMap<plan::FileKey, String>,
    reverted: &std::collections::BTreeSet<String>,
) -> (
    std::collections::BTreeMap<plan::FileKey, String>,
    Vec<apply::Rollback>,
) {
    let mut files = std::collections::BTreeMap::new();
    let mut rollbacks = Vec::new();
    for (key, edits) in &planned.by_file {
        // Revert by JUSTIFICATION, not geography: an edit survives only if the
        // subject that justifies it has not been taken back.
        let kept: Vec<plan::Edit> = edits
            .iter()
            .filter(|edit| !reverted.contains(&edit.owner_fn))
            .cloned()
            .collect();
        if kept.is_empty() {
            continue;
        }
        let Some(source) = texts.get(key) else {
            continue;
        };
        let applied = apply::apply(source, &kept);
        rollbacks.extend(applied.rollbacks);
        files.insert(key.clone(), applied.source);
    }
    (files, rollbacks)
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

    let planned = plan::plan(
        table,
        text_of,
        span_to_loc,
        |subject| tcx.def_path_str(subject.fn_did.to_def_id()),
        &|subject: &decision::Subject| reverted.contains(&subject.fn_did),
    );

    let mut texts = std::collections::BTreeMap::new();
    for key in planned.by_file.keys() {
        let Some(source) = text_of(key) else {
            return Err(format!("no source text for planned file {key:?}"));
        };
        texts.insert(key.clone(), source);
    }
    let (files, rollbacks) = render(&planned, &texts, &std::collections::BTreeSet::new());
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
    let program = collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let mut_facts = MutFacts::from_program(&program);

    // Phase 1 input: the BO run, under an explicit capture scope.
    let (model, _export) = with_bo_export(|| {
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let Ok((_stats, selectors)) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        ) else {
            return None;
        };
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        verify_to_fixpoint(&program, &slots, &solver, &selectors, &mut_facts)
    });
    let Some(model) = model else {
        return Err("BO declined — no accepted model".to_owned());
    };

    let mut subjects = collect_subjects(tcx, &program, &mut_facts);
    // S3.1: the second universe. Appended rather than merged into
    // `collect_subjects` so the parameter census keeps measuring the parameter
    // predicate — a census whose denominator silently gained a population is not
    // the same instrument.
    subjects.extend(collect_local_subjects(tcx, &program, &mut_facts));
    perturb(&mut subjects);
    let facts = decision::emitability::collect(tcx, &program.functions);
    let table = decision::decide(tcx, &subjects, &model, &slots, &facts);

    // Structural self-check: the table matches the subjects it was handed. NOT
    // the coverage gate — every comparison in it is against the collector's own
    // output.
    if let Err(why) = table.is_self_consistent_over(&subjects) {
        return Err(format!("decision table self-consistency: {why}"));
    }

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
        },
    ))
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
        "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\tctor\tlen_class\tsize_expr\n",
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
            .map(|(op, _)| op.as_str())
            .unwrap_or("-");
        let is_param = matches!(s.kind, decision::SubjectKind::Param { .. });
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
            "{}\t{}\t{}\t{}\t{}\t{kind}\t{raw_op}\t{}\t{ctor_key}\t{len_class}\t{size_expr}\n",
            tcx.def_path_str(s.fn_did.to_def_id()),
            s.local.as_u32(),
            u8::from(is_param),
            u8::from(s.ty_span.is_some()),
            u8::from(slot.is_some()),
            u8::from(ctx.facts.ptr_comparisons.contains_key(&(s.fn_did, s.hir_id))),
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
