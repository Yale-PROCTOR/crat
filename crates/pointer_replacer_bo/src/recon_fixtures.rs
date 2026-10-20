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
        // **The population-pinned class is ASKED ABOUT, never hand-excluded.**
        //
        // `expects_zero` is the ONE definition of "does a nonzero count in this
        // class mean failure", and `compare.rs` says in as many words that a
        // consumer testing the class name itself will be forgotten. This gate
        // was a FOURTH by-hand copy — it demanded `findings.is_empty()` outright
        // — and no golden exposed it because every golden before g19 is
        // annotated.
        //
        // `span-check-not-evaluable-local` is STRUCTURAL, not a disagreement: an
        // unannotated `let` has no declared type, so producer A has no span to
        // point at, and synthesizing one was REJECTED (`compare.rs:79-81`)
        // because it would put a non-splice-target into the field whose doc says
        // the audited number IS the edit target. The corpus gate has tolerated
        // it through the per-program table since ruling F; this gate now agrees
        // with it instead of contradicting it.
        //
        // **The gate is not weakened**: a finding of any other class still fails
        // here, which is what the mutation witness below pins.
        let unexpected: Vec<_> = verdict
            .findings
            .iter()
            .filter(|f| crate::coverage_recon::compare::expects_zero(&f.class))
            .collect();
        assert!(
            unexpected.is_empty(),
            "{}: producers disagree — FINDINGS: {:#?}",
            golden.0,
            unexpected
        );
    }
}

/// The fixture gate still fails on a NON-pinned finding.
///
/// Without this, relaxing the assertion above to `expects_zero` could not be
/// told apart from deleting it. Synthesizes a finding of an ordinary class and
/// checks the same predicate the gate uses.
#[test]
fn the_fixture_gate_still_rejects_an_ordinary_finding() {
    use crate::coverage_recon::compare::expects_zero;
    assert!(
        expects_zero("ptr-depth-mismatch"),
        "an ordinary class must still be expected-zero, or the gate above \
         tolerates real disagreements"
    );
    assert!(
        !expects_zero("span-check-not-evaluable-local"),
        "the population-pinned class must be the ONLY tolerated one; if this \
         flips, the gate above silently starts failing every unannotated local"
    );
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

// ---------------------------------------------------------------------------
// T1.4 (i)–(iii) — the ENFORCEMENT witnesses
// ---------------------------------------------------------------------------
//
// Before Track 1 the corpus path recorded `recon=FAIL` and exited green. These
// drive the real worker through the real fault seams and assert the PROCESS
// result, because a verdict that does not change an exit code is a report.

use std::{path::PathBuf, process::Command};

/// Run the `m1-recon` worker on a tiny fixture crate, returning (success, log).
fn run_worker(tag: &str, fault: Option<&str>, artifact_dir: &PathBuf) -> (bool, String) {
    let src_dir = std::env::temp_dir().join(format!("crat-recon-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&src_dir);
    std::fs::create_dir_all(&src_dir).expect("fixture dir");
    let input = src_dir.join("lib.rs");
    std::fs::write(
        &input,
        "#![allow(dead_code)]\npub unsafe fn f(p: *mut i32, q: *mut u8) -> i32 { *p }\n",
    )
    .expect("write fixture");

    let mut cmd = Command::new(std::env::current_exe().expect("current_exe"));
    cmd.args(["bo_c1::boc1_run_one", "--exact", "--ignored", "--nocapture"])
        .env("CRAT_BOC1_INPUT", &input)
        .env("CRAT_BOC1_MODE", "m1-recon")
        .env("CRAT_BOC1_NAME", tag)
        .env("CRAT_BOC1_ARTIFACT_DIR", artifact_dir)
        .env("DIR", env!("CARGO_MANIFEST_DIR"));
    if let Some(f) = fault {
        cmd.env("CRAT_BOC1_RECON_FAULT", f);
    }
    let out = cmd.output().expect("worker runs");
    let log = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    (out.status.success(), log)
}

fn artifact_dir(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("crat-recon-art-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).expect("artifact dir");
    d
}

/// **(i) A verdict failure fails the PROCESS.**
///
/// *Mutation-tested (Rider 0, deletion first):* delete the derived
/// `row.set("status", …)` in `run_m1_recon` (restoring an unconditional `ok`)
/// and this passes — which is precisely the report-only defect.
#[test]
#[ignore = "spawns a worker process"]
fn an_injected_row_drop_fails_the_worker_process() {
    let art = artifact_dir("drop");
    let (ok, log) = run_worker("faulty", Some("drop-a-row"), &art);
    assert!(
        !ok,
        "the worker exited GREEN on a failed reconciliation — the verdict is \
         report-only:\n{log}"
    );
    assert!(
        log.contains("recon=FAIL"),
        "no FAIL verdict recorded:\n{log}"
    );
}

/// **(ii-a) A syntactically corrupt ARTIFACT fails through the DECODE path.**
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the decode-error arm
/// fails this.
#[test]
#[ignore = "spawns a worker process"]
fn a_corrupted_artifact_fails_the_verdict() {
    let art = artifact_dir("corrupt");
    let (ok, log) = run_worker("corrupt", Some("corrupt-a-file"), &art);
    assert!(!ok, "a corrupted artifact did not fail:\n{log}");
    assert!(
        log.contains("artifact-a-undecodable"),
        "the failure did not come through the DECODE path:\n{log}"
    );
}

/// **(ii-b) An ALTERED artifact — valid JSONL, different value — fails the
/// verdict.**
///
/// This is the witness that actually proves the comparison reads the FILE.
/// (ii-a) does not: a syntactic corruption is caught by the decode step alone,
/// so rerouting `compare` to the in-memory rows leaves (ii-a) passing — which
/// it demonstrably did, as a SURVIVING mutant, until this test existed.
///
/// The fault here writes a well-formed row with a different `param_name`, so
/// decode succeeds and only the comparison's *input* decides the outcome.
///
/// *Mutation-tested (Rider 0, deletion first):* rerouting `compare` to
/// `(&a, &b)` — the in-memory rows — fails this.
#[test]
#[ignore = "spawns a worker process"]
fn an_altered_artifact_fails_the_verdict_through_the_file() {
    let art = artifact_dir("alter");
    let (ok, log) = run_worker("alter", Some("alter-a-file"), &art);
    assert!(
        !ok,
        "an altered-but-valid artifact did not fail — the comparison is reading \
         the in-memory rows, not the files:\n{log}"
    );
    assert!(
        log.contains("pairing-mismatch") || log.contains("recon=FAIL"),
        "the failure did not come through the COMPARISON:\n{log}"
    );
}

/// **(iii) An artifact WRITE failure fails loudly at the write call site.**
///
/// The artifact directory itself is valid, but the producer-A artifact path is
/// pre-created as a directory. `create_dir_all` therefore succeeds and the
/// first `std::fs::write` is the operation that must fail.
///
/// *Mutation-tested:* swallowing that write with `.is_ok()` moves the panic to
/// the later read-back and fails the call-site assertions below. Rider 5
/// reachability is the original panic at `bo_c1.rs` with `not writable`.
#[test]
#[ignore = "spawns a worker process"]
fn an_unwritable_artifact_dir_fails_loudly() {
    let art = artifact_dir("unwritable");
    std::fs::create_dir(art.join("unwritable.a.jsonl")).expect("pre-create A path as directory");
    let (ok, log) = run_worker("unwritable", None, &art);
    eprintln!("write-failure reachability:\n{log}");
    assert!(
        !ok,
        "a write failure was SWALLOWED — the verdict would rest on artifacts \
         that were never persisted:\n{log}"
    );
    assert!(
        log.contains("unwritable.a.jsonl") && log.contains("not writable"),
        "the failure did not come from the producer-A write call:\n{log}"
    );
    assert!(
        log.contains("crates/pointer_replacer/src/bo_c1.rs:"),
        "the panic did not cite the write call site:\n{log}"
    );
}

/// The clean path still passes, so the three negatives above are not passing
/// because the worker always fails.
///
/// **Positive control; no deletion mutation fails it** — stated rather than
/// dressed up.
#[test]
#[ignore = "spawns a worker process"]
fn the_clean_worker_path_still_succeeds() {
    let art = artifact_dir("clean");
    let (ok, log) = run_worker("clean", None, &art);
    assert!(ok, "the unfaulted worker failed:\n{log}");
    assert!(log.contains("recon=PASS"), "no PASS verdict:\n{log}");
}

// ---------------------------------------------------------------------------
// T2.4b / T2.4d — the SPAN axis, live path
// ---------------------------------------------------------------------------

/// **T2.4b — the between-phase LIVE witness.**
///
/// The span association is swapped on the collector's real `Subject` output at
/// the phase boundary, then driven through the **real** pipeline:
/// `decide → artifact → encode → decode → compare`. Nothing is hand-built
/// except the perturbation itself, and the perturbation is the exact defect
/// this axis guards.
///
/// The ruled alternative — a `CRAT_*` fault seam inside decision-phase code —
/// was denied and is not needed: a collector fault manifests as precisely this
/// mis-associated output, so the verification power is the same at zero
/// production-code cost.
///
/// **Residual, recorded honestly:** collector-internal failure modes that do
/// *not* manifest as output mis-association are outside this witness — and, by
/// the axis's own definition, outside its scope. The seam question reopens only
/// on evidence of such a mode.
///
/// *Mutation-tested (Rider 0):* deleting the interleave block in `compare`
/// fails this.
///
/// **Stand-in DELETED 2026-07-31**, at the `binding_span` follow-on's merge.
/// Until then this witness filled producer B's binding spans itself; both halves
/// are now real, so it consumes B's actual rows end-to-end. The deletion mutation
/// was re-run after the swap — a witness that passed against a stand-in has not
/// been shown to bite against the real producer.
#[test]
#[ignore = "runs the full BO pipeline twice"]
fn a_live_span_swap_is_caught_end_to_end() {
    let src =
        "#![allow(dead_code)]\npub unsafe fn f(p: *mut i32, q: *const u8) -> i32 { *p as i32 }\n";
    let (verdict, active) = ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let a = crate::bo_rewriter::artifact_rows_span_swapped(tcx).expect("producer A");
        let b = producer_b::rows(tcx);
        let active = crate::coverage_recon::compare::span_axis_active(&b);
        let encoded_a = crate::coverage_recon::schema::encode(&a);
        let encoded_b = crate::coverage_recon::schema::encode(&b);
        let a = crate::coverage_recon::schema::decode(&encoded_a).expect("A decodes");
        let b = crate::coverage_recon::schema::decode(&encoded_b).expect("B decodes");
        (crate::coverage_recon::compare::compare(&a, &b), active)
    })
    .expect("fixture compiles");

    assert!(
        active,
        "the span axis must be ACTIVE for this witness to mean anything"
    );
    assert!(
        verdict
            .violations
            .iter()
            .any(|v| v.class == "span-interleave-breach"),
        "a LIVE span swap reached the artifact and was accepted — the splice \
         target is not under gate: {verdict:#?}"
    );
}

/// **T2.4d — PRE-DECLARED RED.** Producer B does not yet emit `binding_span`,
/// so the span axis is INACTIVE on its real artifact.
///
/// Booked with the six S3 goldens as a known-red: it flips GREEN when the gated
/// Codex follow-on lands producer B's binding spans, and then **stays forever**
/// as the post-activation regression guard — a broken fill re-REDs it.
///
/// **S2a-H cannot close while this is red**, by rule. The dormant window is
/// bounded by the round itself rather than by anyone remembering.
#[test]
fn span_axis_is_active_on_producer_b() {
    let src =
        "#![allow(dead_code)]\npub unsafe fn f(p: *mut i32, q: *const u8) -> i32 { *p as i32 }\n";
    let rows = ::utils::compilation::run_compiler_on_str(src, |tcx| producer_b::rows(tcx))
        .expect("fixture compiles");
    assert!(
        crate::coverage_recon::compare::span_axis_active(&rows),
        "producer B emits no binding_span, so the SPAN AXIS IS INACTIVE. This \
         test is pre-declared RED and flips green with the gated follow-on; \
         S2a-H cannot close while it is red."
    );
}
