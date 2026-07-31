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
    assert!(log.contains("recon=FAIL"), "no FAIL verdict recorded:\n{log}");
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
