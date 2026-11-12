//! R1520-2 (main 336 §A5) and R1523-2: the model checkpoint's witnesses W0–W10. W3, W5 and W10 run in
//! this process.
//! The others run the whole rewrite in child processes of this test binary, because the switches
//! are read once per process. The child harness is shared with `fact_marks_tests` (WB1–WB3).

use std::{
    ffi::OsString,
    path::{Path, PathBuf},
};

use rustc_hash::FxHashMap;
use rustc_hir::{ItemKind, OwnerNode};
use serde::{Deserialize, Serialize};

use super::*;
use crate::analyses::borrow_ownership::{
    crate_slots::CrateSlots,
    execution_guard, model_cache,
    param_overlap::{OverlapMode, WholeProgramAttestation},
};

/// main 322's fixture: three solves in one repair, beside a source / sink tie.
pub(crate) const CASCADE_TIE: &str = r#"
unsafe fn id(p: *mut i32) -> *mut i32 { p }
pub unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
unsafe extern "C" { fn retain_for_policy_fixture(x: *mut core::ffi::c_void); }
pub unsafe fn pass(x: *mut core::ffi::c_void) { retain_for_policy_fixture(x); }
pub unsafe fn source_side() -> *mut core::ffi::c_void {
    let m = unsafe { malloc(4) };
    unsafe { pass(m) };
    m
}
pub unsafe fn sink_side(a: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let b = a;
    unsafe { pass(b) };
    unsafe { free(a) };
    b
}
"#;

/// An effective may-overlap pair: the precise stage changes the model away from the baseline.
const OVERLAP: &str = r#"
pub unsafe fn two(x: *mut i32, y: *mut i32) { *x = 1; *y = 2; }
pub unsafe fn caller(p: *mut i32) -> i32 { two(p, p); *p }
"#;

/// quadtree's own file, whose model carries argument-order receipts (era-5c's `e5c_w72`).
const QUADTREE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../benchmarks/rs-crown-derived/quadtree/lib.rs"
);

const FROZEN: Option<WholeProgramAttestation> = Some(WholeProgramAttestation::FrozenBenchmarkGraph);

fn program<'tcx>(tcx: rustc_middle::ty::TyCtxt<'tcx>) -> RustProgram<'tcx> {
    let mut functions = Vec::new();
    for owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = owner.as_owner() else { continue };
        let OwnerNode::Item(item) = owner.node() else { continue };
        if let ItemKind::Fn { .. } = item.kind {
            functions.push(item.owner_id.def_id);
        }
    }
    RustProgram {
        tcx,
        functions,
        structs: Vec::new(),
    }
}

pub(crate) fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("crat-r1520-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Every slot of the universe at one kind: a whole-universe model for the format witnesses.
fn all(slots: &CrateSlots, kind: SlotKind) -> FxHashMap<SlotRef, SlotKind> {
    let mut model = FxHashMap::default();
    for (&function, universe) in &slots.fn_local_slots {
        for index in 0..universe.len() {
            model.insert(
                SlotRef::Local(
                    function,
                    crate::analyses::borrow_ownership::slots::SlotId::from_usize(index),
                ),
                kind,
            );
        }
    }
    model
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ChildResult {
    pub(crate) kind: String,
    pub(crate) reason: Option<String>,
    pub(crate) source: String,
    pub(crate) files: Vec<String>,
    pub(crate) overlap_receipt: String,
    pub(crate) model_sha256: Option<String>,
    pub(crate) solve_source: Option<String>,
    pub(crate) solve_status: Option<String>,
}

impl ChildResult {
    /// Everything but where the model came from (the solve receipt's two fields).
    pub(crate) fn decision(&self) -> (String, String, Vec<String>, String, Option<String>) {
        (
            self.kind.clone(),
            self.source.clone(),
            self.files.clone(),
            self.overlap_receipt.clone(),
            self.model_sha256.clone(),
        )
    }
}

const CHILD_OUT: &str = "CRAT_R1520_2_CHILD_OUT";
const CHILD_ROOT: &str = "CRAT_R1520_2_CHILD_ROOT";
const CHILD_ATTEST: &str = "CRAT_R1520_2_CHILD_ATTEST";

/// In a child: run the whole rewrite on `CHILD_ROOT` and write the result to `CHILD_OUT`.
pub(crate) fn child() -> bool {
    let Some(out) = std::env::var_os(CHILD_OUT) else {
        return false;
    };
    let root = PathBuf::from(std::env::var_os(CHILD_ROOT).expect("child root"));
    let attestation = match std::env::var(CHILD_ATTEST).as_deref() {
        Ok("none") => None,
        _ => FROZEN,
    };
    let outcome = crate::bo_rewriter::rewrite_m1_path_with_emission_config(
        &root,
        OverlapMode::PreciseReplay,
        attestation,
        &crate::bo_rewriter::EmissionRunConfig::default(),
    );
    let result = match outcome {
        crate::bo_rewriter::RewriteOutcome::Emitted {
            source,
            files,
            overlap_receipt,
            solve_receipt,
            ..
        } => ChildResult {
            kind: "emitted".into(),
            reason: None,
            source,
            files: files.into_values().collect(),
            overlap_receipt,
            model_sha256: solve_receipt.as_ref().map(|r| r.model_sha256.clone()),
            solve_source: solve_receipt.as_ref().map(|r| r.source.clone()),
            solve_status: solve_receipt.as_ref().map(|r| r.cache_status.clone()),
        },
        crate::bo_rewriter::RewriteOutcome::Degraded { reason, source, .. } => ChildResult {
            kind: "degraded".into(),
            reason: Some(reason),
            source,
            files: Vec::new(),
            overlap_receipt: String::new(),
            model_sha256: None,
            solve_source: None,
            solve_status: None,
        },
    };
    std::fs::write(out, serde_json::to_vec(&result).unwrap()).unwrap();
    true
}

/// In the parent: run `test` in a child on a fresh copy of `code`, with `env`. Returns the result
/// and the child's stderr.
pub(crate) fn spawn(
    test: &str,
    code: &str,
    tag: &str,
    attest: &str,
    env: &[(&str, OsString)],
) -> (ChildResult, String) {
    let dir = scratch(tag);
    std::fs::write(dir.join("lib.rs"), code).unwrap();
    let out = dir.join("result.json");
    let mut command = std::process::Command::new(std::env::current_exe().expect("current_exe"));
    command
        .args([
            test,
            "--exact",
            "--include-ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env_clear()
        // No CRAT_* variable of this process reaches the child: neither a switch nor one another witness
        // sets in-process for a moment (e.g. CRAT_W6A_CERTIFY_TRACE under the frame lock). The child gets
        // the rest of the environment, its own three, and the witness's own switches.
        .envs(std::env::vars_os().filter(|(name, _)| !name.to_string_lossy().starts_with("CRAT_")))
        .env(CHILD_OUT, &out)
        .env(CHILD_ROOT, dir.join("lib.rs"))
        .env(CHILD_ATTEST, attest);
    for (name, value) in env {
        command.env(name, value);
    }
    let output = command.output().expect("child");
    assert!(
        output.status.success(),
        "child {tag} failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let result =
        serde_json::from_slice(&std::fs::read(&out).unwrap_or_else(|e| panic!("{tag}: {e}")))
            .unwrap();
    (result, String::from_utf8_lossy(&output.stderr).into_owned())
}

fn os(path: &Path) -> OsString {
    path.as_os_str().to_owned()
}

/// The lines this module writes (`[bo-model-checkpoint] …`).
fn lines(stderr: &str) -> Vec<&str> {
    stderr
        .lines()
        .filter(|line| line.starts_with(LINE_HEAD))
        .collect()
}

fn stored(path: &Path) -> ModelCheckpoint {
    serde_json::from_slice(
        &std::fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display())),
    )
    .unwrap()
}

/// The position of the first phase line `<phase> <edge>` in `stderr`.
pub(crate) fn phase_at(stderr: &str, phase: &str, edge: &str) -> Option<usize> {
    stderr.lines().position(|line| {
        let mut words = line.split_whitespace();
        words.next() == Some("[bo-phase]")
            && words.next() == Some(phase)
            && words.next() == Some(edge)
    })
}

/// Writer and reader on `code`: the writer with `OUT`, the reader with `IN` and the phase log on.
fn write_then_read(
    test: &str,
    code: &str,
    tag: &str,
    extra: &[(&str, OsString)],
) -> (ChildResult, String, ChildResult, String, ModelCheckpoint) {
    let file = scratch(&format!("{tag}-file")).join("model.json");
    let mut out = extra.to_vec();
    out.push(("CRAT_BO_MODEL_CHECKPOINT_OUT", os(&file)));
    out.push(("CRAT_BO_PHASE_LOG", "on".into()));
    let (w, w_err) = spawn(test, code, &format!("{tag}-w"), "frozen", &out);
    assert!(
        file.exists(),
        "{tag}: no model checkpoint written:\n{w_err}"
    );
    let checkpoint = stored(&file);
    let mut input = extra.to_vec();
    input.push(("CRAT_BO_MODEL_CHECKPOINT_IN", os(&file)));
    input.push(("CRAT_BO_PHASE_LOG", "on".into()));
    let (r, r_err) = spawn(test, code, &format!("{tag}-r"), "frozen", &input);
    (w, w_err, r, r_err, checkpoint)
}

/// The reader decided from the file: no solve, its line names the same binary.
fn assert_read_without_solve(r: &ChildResult, r_err: &str, w: &ChildResult) {
    assert_eq!(r.kind, "emitted", "{r:?}\n{r_err}");
    assert_eq!(r.decision(), w.decision());
    assert_eq!(w.solve_source.as_deref(), Some("real"));
    assert_eq!(r.solve_source.as_deref(), Some("model-checkpoint"), "{r:?}");
    assert_eq!(r.solve_status.as_deref(), Some("read-same-exe"), "{r:?}");
    assert!(
        phase_at(r_err, "decide:solve", "start").is_none(),
        "the reader solved:\n{r_err}"
    );
    let read = lines(r_err);
    assert!(
        read.len() == 1 && read[0].contains(" read path=") && read[0].ends_with(" exe=same"),
        "{read:?}"
    );
}

/// W0: with both switches unset nothing is read or written and no line is written. And `OUT` does
/// not move the decision: a writer's emitted tree, receipt and model equal an unset run's. RED at
/// `f1dcb012b`: `OUT` is not read, so the writer writes no line and no file.
#[test]
fn r1520_2_w0_unset_changes_nothing_and_out_moves_no_decision() {
    if child() {
        return;
    }
    assert_eq!(paths(), (None, None), "a switch is set in the test process");
    assert_eq!(
        switches(OverlapMode::Baseline, None, (None, None)),
        Ok((None, None))
    );
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w0_unset_changes_nothing_and_out_moves_no_decision";
    let (a, a_err) = spawn(test, CASCADE_TIE, "w0-a", "frozen", &[]);
    assert_eq!(a.kind, "emitted", "{a:?}");
    assert!(lines(&a_err).is_empty(), "{a_err}");
    let file = scratch("w0-file").join("model.json");
    let (b, b_err) = spawn(
        test,
        CASCADE_TIE,
        "w0-b",
        "frozen",
        &[("CRAT_BO_MODEL_CHECKPOINT_OUT", os(&file))],
    );
    assert_eq!(b, a);
    let written = lines(&b_err);
    assert!(
        written.len() == 1 && written[0].contains(" write path=") && !written[0].contains("error="),
        "{b_err}"
    );
    assert!(file.exists());
}

/// W1: `OUT` writes the accepted model after the solve and before `finish_decide` starts. The file's
/// digest is the solve receipt's. RED at `f1dcb012b`: nothing is written. R1523-2 (F3): what the
/// write needs from outside the solve is taken before the solve starts. RED at `11aeb1613`: no
/// start mark.
#[test]
fn r1520_2_w1_out_writes_the_accepted_model_before_finish_decide() {
    if child() {
        return;
    }
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w1_out_writes_the_accepted_model_before_finish_decide";
    let file = scratch("w1-file").join("model.json");
    let (w, w_err) = spawn(
        test,
        CASCADE_TIE,
        "w1",
        "frozen",
        &[
            ("CRAT_BO_MODEL_CHECKPOINT_OUT", os(&file)),
            ("CRAT_BO_PHASE_LOG", "on".into()),
        ],
    );
    assert_eq!(w.kind, "emitted", "{w:?}");
    let started = phase_at(&w_err, "decide:model_checkpoint", "start").expect("the start's mark");
    let solving = phase_at(&w_err, "decide:solve", "start").expect("decide:solve start");
    let solved = phase_at(&w_err, "decide:solve", "end").expect("decide:solve end");
    let written = phase_at(&w_err, "decide:model_checkpoint", "end").expect("the write's mark");
    let finish = phase_at(&w_err, "finish_decide", "start").expect("finish_decide start");
    assert!(
        started < solving && solving < solved && solved < written && written < finish,
        "{w_err}"
    );
    let checkpoint = stored(&file);
    assert_eq!(checkpoint.schema, SCHEMA);
    assert_eq!(Some(checkpoint.model_sha256.clone()), w.model_sha256);
    assert!(!checkpoint.model.is_empty());
    assert_eq!(checkpoint.model.len(), checkpoint.baseline.len());
    assert_eq!(checkpoint.overlap_receipt, w.overlap_receipt);
    assert_eq!(checkpoint.provenance.baseline_checkpoint, None);
    assert!(!checkpoint.provenance.incumbent);
    let line = lines(&w_err);
    assert!(
        line.len() == 1
            && line[0].contains(&format!("slots={}", checkpoint.model.len()))
            && line[0].contains(&format!("model_sha256={}", checkpoint.model_sha256))
            && line[0].ends_with(" incumbent=false"),
        "{line:?}"
    );
}

/// W2 (a): a reader with `IN` gives the writer's emitted tree, overlap receipt and model, from the
/// file, without solving. RED at `f1dcb012b`: `IN` is not read, so the reader solves.
#[test]
fn r1520_2_w2a_in_decides_from_the_file_as_the_writer_did() {
    if child() {
        return;
    }
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w2a_in_decides_from_the_file_as_the_writer_did";
    let (w, _, r, r_err, _) = write_then_read(test, CASCADE_TIE, "w2a", &[]);
    assert_read_without_solve(&r, &r_err, &w);
}

/// W2 (b): the same where the precise stage moved the model away from the baseline, so the file's
/// two maps differ.
#[test]
fn r1520_2_w2b_in_decides_from_the_file_where_the_precise_replay_moved_the_model() {
    if child() {
        return;
    }
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w2b_in_decides_from_the_file_where_the_precise_replay_moved_the_model";
    let (w, _, r, r_err, checkpoint) = write_then_read(test, OVERLAP, "w2b", &[]);
    assert_ne!(
        checkpoint.model, checkpoint.baseline,
        "the precise stage did not move the model: the witness would be vacuous"
    );
    assert_read_without_solve(&r, &r_err, &w);
}

/// W3: the file round-trips, and every difference but the binary's is refused, each with its field
/// named. In process, on the module (it passes at the RED stage: the module is the new code).
#[test]
fn r1520_2_w3_every_difference_but_the_binary_is_refused() {
    ::utils::compilation::run_compiler_on_str(CASCADE_TIE, |tcx| {
        let program = program(tcx);
        let slots = CrateSlots::build(&program);
        let model = all(&slots, SlotKind::Raw);
        let baseline = all(&slots, SlotKind::Ref);
        let path = scratch("w3").join("model.json");
        let rows: Result<Vec<_>, String> = Err("not recorded".into());
        let taken = start(&program, &slots, OverlapMode::PreciseReplay, FROZEN).unwrap();
        let bytes = write(
            &path, &program, &slots, &model, &baseline, "receipt", &taken, rows, true, 1.5,
        )
        .unwrap();
        assert_eq!(bytes as u64, std::fs::metadata(&path).unwrap().len());
        let names = std::fs::read_dir(path.parent().unwrap())
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect::<Vec<_>>();
        assert_eq!(
            names,
            vec![path.file_name().unwrap().to_owned()],
            "no temporary left"
        );
        let loaded = read(&path, &program, &slots, OverlapMode::PreciseReplay, FROZEN).unwrap();
        assert_eq!(loaded.cached.model, model);
        assert_eq!(loaded.cached.baseline_model, baseline);
        assert_eq!(loaded.cached.overlap_receipt, "receipt");
        assert_eq!(
            loaded.arg_order,
            ArgOrder::NotRecorded("not recorded".into())
        );
        assert!(loaded.same_exe && loaded.incumbent);
        assert_eq!(loaded.slots, model.len());
        assert_eq!(
            Some(loaded.model_sha256.clone()),
            model_cache::model_bytes_sha256(tcx, &slots, &model)
        );

        let original: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        let first_key = original["model"]
            .as_object()
            .unwrap()
            .keys()
            .next()
            .unwrap()
            .clone();
        let tampered = |edit: &dyn Fn(&mut serde_json::Value)| {
            let mut value = original.clone();
            edit(&mut value);
            let file = path.with_file_name("tampered.json");
            std::fs::write(&file, serde_json::to_vec(&value).unwrap()).unwrap();
            read(&file, &program, &slots, OverlapMode::PreciseReplay, FROZEN)
        };
        let refused_at = |result: Result<Loaded, String>, field: &str| {
            let error = result.err().unwrap_or_else(|| panic!("{field}: accepted"));
            assert!(
                error.starts_with(&format!("{REFUSED_HEAD}{field} (")),
                "{field}: {error}"
            );
        };
        refused_at(
            tampered(&|v| v["schema"] = "bo-model-checkpoint-v0".into()),
            "schema",
        );
        refused_at(
            tampered(&|v| v["identity"]["semantic_key"] = "x".into()),
            "semantic_key",
        );
        refused_at(
            tampered(&|v| v["identity"]["compiler"]["edition"] = "x".into()),
            "compiler",
        );
        refused_at(
            tampered(&|v| v["identity"]["universe_sha256"] = "x".into()),
            "universe",
        );
        refused_at(
            tampered(&|v| v["identity"]["config"]["query_timeout_ms"] = 7.into()),
            "config",
        );
        refused_at(
            tampered(&|v| v["model"][first_key.as_str()] = "ref".into()),
            "model_sha256",
        );
        refused_at(
            tampered(&|v| {
                let kind = v["model"]
                    .as_object_mut()
                    .unwrap()
                    .remove(&first_key)
                    .unwrap();
                v["model"]["no::such::slot@d0"] = kind;
            }),
            "model",
        );
        refused_at(
            tampered(&|v| v["model"][first_key.as_str()] = "bogus".into()),
            "model",
        );
        refused_at(
            tampered(&|v| v["model_sha256"] = "x".into()),
            "model_sha256",
        );
        refused_at(
            tampered(&|v| v["baseline_sha256"] = "x".into()),
            "baseline_sha256",
        );
        // The binary is recorded, not refused; the reader says it is another.
        let other = tampered(&|v| v["identity"]["exe_sha256"] = "x".into()).unwrap();
        assert!(!other.same_exe);
        let garbage = path.with_file_name("garbage.json");
        std::fs::write(&garbage, b"{").unwrap();
        refused_at(
            read(
                &garbage,
                &program,
                &slots,
                OverlapMode::PreciseReplay,
                FROZEN,
            ),
            "format",
        );
        refused_at(
            read(
                &path.with_file_name("absent.json"),
                &program,
                &slots,
                OverlapMode::PreciseReplay,
                FROZEN,
            ),
            "file",
        );

        // The rows round-trip whole.
        let row: crate::analyses::borrow_ownership::portable_export::ArgOrderRow =
            serde_json::from_value(serde_json::json!({
                "function": "f",
                "call": {"block": 1, "statement": 0},
                "span": {"file": "lib.rs", "lo": 1, "hi": 2},
                "lent": 1,
                "owner": 2
            }))
            .unwrap_or_else(|e| panic!("the row's fields: {e}"));
        write(
            &path,
            &program,
            &slots,
            &model,
            &baseline,
            "receipt",
            &taken,
            Ok(vec![row.clone()]),
            false,
            0.0,
        )
        .unwrap();
        let loaded = read(&path, &program, &slots, OverlapMode::PreciseReplay, FROZEN).unwrap();
        assert_eq!(loaded.arg_order, ArgOrder::Rows(vec![row]));
        assert!(!loaded.incumbent);
    });

    // The switches, each refused pair and mode named.
    let p = || Some(PathBuf::from("x.json"));
    let refused_at = |result: Result<(Option<PathBuf>, Option<PathBuf>), String>, field: &str| {
        let error = result.err().unwrap_or_else(|| panic!("{field}: accepted"));
        assert!(
            error.starts_with(&format!("{REFUSED_HEAD}{field} (")),
            "{error}"
        );
    };
    refused_at(
        switches(OverlapMode::PreciseReplay, FROZEN, (p(), p())),
        "switches",
    );
    refused_at(
        switches(OverlapMode::Baseline, FROZEN, (None, p())),
        "a5_mode",
    );
    refused_at(
        switches(OverlapMode::PreciseReplay, None, (p(), None)),
        "attestation",
    );
    refused_at(
        execution_guard::checkpoint_hook::with((None, p()), || {
            switches(OverlapMode::PreciseReplay, FROZEN, (None, p()))
        }),
        "switches",
    );
    refused_at(
        execution_guard::checkpoint_hook::with((p(), None), || {
            switches(OverlapMode::PreciseReplay, FROZEN, (p(), None))
        }),
        "switches",
    );
    refused_at(
        model_cache::with_test_config(&scratch("w3-cache"), || {
            switches(OverlapMode::PreciseReplay, FROZEN, (None, p()))
        }),
        "switches",
    );
    assert_eq!(
        execution_guard::checkpoint_hook::with((None, p()), || {
            switches(OverlapMode::PreciseReplay, FROZEN, (p(), None))
        }),
        Ok((p(), None)),
        "OUT goes with process 2"
    );
}

/// W3 (b): a refusal in the decide is the run's typed error and never a solve: a tampered receipt
/// (the cache-hit path's own check), `IN` beside a baseline checkpoint, and `IN` outside the frozen
/// graph. RED at `f1dcb012b`: `IN` is not read, so each reader solves and emits.
#[test]
fn r1520_2_w3b_a_refusal_in_the_decide_never_solves() {
    if child() {
        return;
    }
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w3b_a_refusal_in_the_decide_never_solves";
    let file = scratch("w3b-file").join("model.json");
    spawn(
        test,
        CASCADE_TIE,
        "w3b-w",
        "frozen",
        &[("CRAT_BO_MODEL_CHECKPOINT_OUT", os(&file))],
    );
    let mut value: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&file).unwrap()).unwrap();
    let receipt = value["overlap_receipt"].as_str().unwrap().to_owned();
    assert!(receipt.contains("selected_model_sha256="), "{receipt}");
    value["overlap_receipt"] = receipt
        .lines()
        .map(|line| {
            if line.starts_with("selected_model_sha256=") {
                "selected_model_sha256=0".to_owned()
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
        .into();
    let bad = file.with_file_name("bad-receipt.json");
    std::fs::write(&bad, serde_json::to_vec(&value).unwrap()).unwrap();
    let cases: [(&str, &str, Vec<(&str, OsString)>, &str); 3] = [
        (
            "receipt",
            "frozen",
            vec![("CRAT_BO_MODEL_CHECKPOINT_IN", os(&bad))],
            "receipt (",
        ),
        (
            "baseline",
            "frozen",
            vec![
                ("CRAT_BO_MODEL_CHECKPOINT_IN", os(&file)),
                (
                    "CRAT_BO_CHECKPOINT_IN",
                    os(&file.with_file_name("baseline.json")),
                ),
            ],
            "switches (",
        ),
        (
            "unattested",
            "none",
            vec![("CRAT_BO_MODEL_CHECKPOINT_IN", os(&file))],
            "attestation (",
        ),
    ];
    for (tag, attest, mut env, field) in cases {
        env.push(("CRAT_BO_PHASE_LOG", "on".into()));
        let (r, r_err) = spawn(test, CASCADE_TIE, &format!("w3b-{tag}"), attest, &env);
        assert_eq!(r.kind, "degraded", "{tag}: {r:?}");
        let reason = r.reason.clone().unwrap();
        assert!(
            reason.contains(&format!("{REFUSED_HEAD}{field}")),
            "{tag}: {reason}"
        );
        assert_eq!(r.source, CASCADE_TIE, "{tag}: the tree is the input");
        assert!(
            phase_at(&r_err, "decide:solve", "start").is_none(),
            "{tag}: solved:\n{r_err}"
        );
    }
}

/// W4: the argument-order rows ride across. On quadtree, whose model carries them, the reader's
/// emitted tree equals the writer's, and both lines name the same rows. RED by construction:
/// without the rows the reader's hoist set is empty (`mod.rs`'s `unwrap_or_default`), and at
/// `f1dcb012b` no file is written at all.
#[test]
fn r1520_2_w4_the_argument_order_rows_ride_across() {
    if child() {
        return;
    }
    let Ok(code) = std::fs::read_to_string(QUADTREE) else {
        eprintln!("corpus absent; skipping");
        return;
    };
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w4_the_argument_order_rows_ride_across";
    let (w, w_err, r, r_err, checkpoint) = write_then_read(test, &code, "w4", &[]);
    let ArgOrder::Rows(rows) = &checkpoint.arg_order else {
        panic!(
            "quadtree's model records no argument-order rows: {:?}",
            checkpoint.arg_order
        );
    };
    assert!(
        rows.iter()
            .any(|row| row.function.contains("quadtree_insert")),
        "{rows:?}"
    );
    let label = format!("arg_order=ok:{}", rows.len());
    assert!(
        lines(&w_err).iter().any(|line| line.contains(&label)),
        "{w_err}"
    );
    assert!(
        lines(&r_err).iter().any(|line| line.contains(&label)),
        "{r_err}"
    );
    assert_read_without_solve(&r, &r_err, &w);
}

/// W5: the copy of the hoist conversion equals `model_cache`'s on the same rows (the drift pin, main
/// 336 §A6). In process, on quadtree's rows. It passes at the RED stage: the copy is new code.
#[test]
fn r1520_2_w5_the_hoist_copy_equals_model_cache_s() {
    if !Path::new(QUADTREE).is_file() {
        eprintln!("corpus absent; skipping");
        return;
    }
    // An in-process decide: the frame locks, in their order (the crate-wide one, then ownership-fields'),
    // so no witness that sets a frame switch or a model override in-process overlaps it.
    let _frame = super::super::test_model_override::frame_lock();
    let _fields = super::super::decision::ownership_fields_native::field_form_override::LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    ::utils::compilation::run_compiler_on_path(Path::new(QUADTREE), |tcx| {
        super::super::decide_table(tcx).expect("quadtree decides");
        let program = super::super::collect_program(tcx);
        let fp = model_cache::fingerprint(&program, OverlapMode::PreciseReplay, FROZEN);
        let rows = model_cache::prepared_arg_order_applied(&fp).expect("rows recorded");
        assert!(!rows.is_empty());
        let original = model_cache::prepared_arg_order_hoists(tcx, &fp).unwrap();
        assert!(!original.is_empty());
        assert_eq!(hoists(tcx, &rows).unwrap(), original);
    });
}

/// W6: a model whose solve accepted an optimize incumbent is written with `incumbent=true`, and the
/// reader says so. Timing-dependent (an incumbent at a 12-ms query budget), as R1490-2's W8.
#[test]
#[ignore = "timing-dependent (an optimize incumbent at a 12-ms query budget); run explicitly"]
fn r1520_2_w6_an_incumbent_model_is_written_and_read_as_one() {
    if child() {
        return;
    }
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w6_an_incumbent_model_is_written_and_read_as_one";
    let mut code = String::new();
    for k in 0..60 {
        code.push_str(&format!(
            "pub unsafe fn f{k}(p: *mut i32, q: *mut i32) -> i32 {{ let a = p; let b = q; *a = *b + {k}; *a }}\n"
        ));
    }
    code.push_str("pub unsafe fn driver(p: *mut i32, q: *mut i32) -> i32 { let mut s = 0;");
    for k in 0..60 {
        code.push_str(&format!(" s += f{k}(p, q);"));
    }
    code.push_str(" s }\n");
    let timeout = [("CRAT_BO_QUERY_TIMEOUT_MS", OsString::from("12"))];
    let (w, w_err, r, r_err, checkpoint) = write_then_read(test, &code, "w6", &timeout);
    assert!(
        checkpoint.provenance.incumbent,
        "no round accepted an incumbent: the witness would be vacuous"
    );
    assert!(
        lines(&w_err)
            .iter()
            .any(|line| line.ends_with(" incumbent=true")),
        "{w_err}"
    );
    assert!(
        lines(&r_err)
            .iter()
            .any(|line| line.contains(" incumbent=true ")),
        "{r_err}"
    );
    assert_read_without_solve(&r, &r_err, &w);
}

/// W7: in a two-process solve, process 2 writes the model checkpoint and names the baseline
/// checkpoint it resumed from by its digest; a reader then decides as process 2 did.
#[test]
fn r1520_2_w7_process_two_names_its_baseline_checkpoint() {
    if child() {
        return;
    }
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w7_process_two_names_its_baseline_checkpoint";
    let dir = scratch("w7-files");
    let baseline = dir.join("baseline.json");
    let model = dir.join("model.json");
    let (p1, _) = spawn(
        test,
        CASCADE_TIE,
        "w7-p1",
        "frozen",
        &[("CRAT_BO_CHECKPOINT_OUT", os(&baseline))],
    );
    assert_eq!(p1.kind, "degraded", "process 1 ends checkpointed: {p1:?}");
    let (p2, _) = spawn(
        test,
        CASCADE_TIE,
        "w7-p2",
        "frozen",
        &[
            ("CRAT_BO_CHECKPOINT_IN", os(&baseline)),
            ("CRAT_BO_MODEL_CHECKPOINT_OUT", os(&model)),
        ],
    );
    assert_eq!(p2.kind, "emitted", "{p2:?}");
    let checkpoint = stored(&model);
    let source = checkpoint
        .provenance
        .baseline_checkpoint
        .clone()
        .expect("the baseline checkpoint named");
    assert_eq!(source.path, baseline.display().to_string());
    assert_eq!(
        source.sha256,
        format!(
            "{:x}",
            <sha2::Sha256 as sha2::Digest>::digest(std::fs::read(&baseline).unwrap())
        )
    );
    assert_eq!(Some(checkpoint.model_sha256.clone()), p2.model_sha256);
    let (r, r_err) = spawn(
        test,
        CASCADE_TIE,
        "w7-r",
        "frozen",
        &[
            ("CRAT_BO_MODEL_CHECKPOINT_IN", os(&model)),
            ("CRAT_BO_PHASE_LOG", "on".into()),
        ],
    );
    assert_eq!(r.decision(), p2.decision(), "{r_err}");
    assert_eq!(r.solve_source.as_deref(), Some("model-checkpoint"));
}

/// W8: a write that fails is one line with its error, and the decide goes on: the emitted tree,
/// receipt and model equal an unset run's. RED at `f1dcb012b`: no line.
#[test]
fn r1520_2_w8_a_failed_write_is_one_line_and_the_decide_goes_on() {
    if child() {
        return;
    }
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w8_a_failed_write_is_one_line_and_the_decide_goes_on";
    let (a, _) = spawn(test, CASCADE_TIE, "w8-a", "frozen", &[]);
    let nowhere = scratch("w8-file").join("absent-dir").join("model.json");
    let (b, b_err) = spawn(
        test,
        CASCADE_TIE,
        "w8-b",
        "frozen",
        &[("CRAT_BO_MODEL_CHECKPOINT_OUT", os(&nowhere))],
    );
    assert_eq!(b, a);
    let line = lines(&b_err);
    assert!(
        line.len() == 1 && line[0].contains(" write path=") && line[0].contains(" error="),
        "{b_err}"
    );
    assert!(!nowhere.exists());
}

/// W9 (R1523-2, F1): the baseline checkpoint a process resumes from is read and hashed once, at the
/// decide's start, and the write reads no file. Here the path under `CRAT_BO_CHECKPOINT_IN` can be
/// opened exactly twice: the first open reads the checkpoint's bytes, the second reads the same
/// checkpoint with one trailing newline (only so that the witness can tell which read was hashed),
/// and after the second open the path is gone. The decide's start takes the first read and the solve
/// the second; the model checkpoint is written with the path gone and names the first read's digest.
/// RED at `11aeb1613`: the solve takes the first read and the write hashes the second.
#[test]
fn r1520_2_w9_the_baseline_source_is_taken_at_the_decide_s_start() {
    if child() {
        return;
    }
    let test = "bo_rewriter::model_checkpoint::model_checkpoint_tests::r1520_2_w9_the_baseline_source_is_taken_at_the_decide_s_start";
    let dir = scratch("w9-files");
    let baseline = dir.join("baseline.json");
    let model = dir.join("model.json");
    let (p1, _) = spawn(
        test,
        CASCADE_TIE,
        "w9-p1",
        "frozen",
        &[("CRAT_BO_CHECKPOINT_OUT", os(&baseline))],
    );
    assert_eq!(p1.kind, "degraded", "process 1 ends checkpointed: {p1:?}");
    let first = std::fs::read(&baseline).unwrap();
    let mut second = first.clone();
    second.push(b'\n');

    // The path is a symbolic link to a pipe. A pipe's `open` for writing returns when the reader has
    // opened it, so the server below knows of each open and moves the link before it writes a byte.
    let (pipe1, pipe2) = (dir.join("first.pipe"), dir.join("second.pipe"));
    let made = std::process::Command::new("mkfifo")
        .args([&pipe1, &pipe2])
        .status()
        .expect("mkfifo");
    assert!(made.success());
    let input = dir.join("baseline-in.json");
    std::os::unix::fs::symlink(&pipe1, &input).unwrap();
    let (served, serves) = std::sync::mpsc::channel();
    // Not joined: when the child does not open the path, this thread stays in its `open`.
    std::thread::spawn({
        let (input, next) = (input.clone(), dir.join("baseline-in.next"));
        let (first, second) = (first.clone(), second.clone());
        move || {
            use std::io::Write;
            let open = |pipe: &Path| std::fs::OpenOptions::new().write(true).open(pipe);
            let Ok(mut pipe) = open(&pipe1) else { return };
            // The first open has happened. The next open of the path reads the second pipe.
            let moved = std::os::unix::fs::symlink(&pipe2, &next)
                .and_then(|()| std::fs::rename(&next, &input));
            if moved.is_err() {
                return;
            }
            let _ = pipe.write_all(&first);
            drop(pipe);
            let _ = served.send(1);
            let Ok(mut pipe) = open(&pipe2) else { return };
            // The second open has happened. No third open finds the path.
            if std::fs::remove_file(&input).is_err() {
                return;
            }
            let _ = pipe.write_all(&second);
            drop(pipe);
            let _ = served.send(2);
        }
    });
    let (p2, p2_err) = spawn(
        test,
        CASCADE_TIE,
        "w9-p2",
        "frozen",
        &[
            ("CRAT_BO_CHECKPOINT_IN", os(&input)),
            ("CRAT_BO_MODEL_CHECKPOINT_OUT", os(&model)),
        ],
    );
    let wait = std::time::Duration::from_secs(10);
    assert_eq!(serves.recv_timeout(wait), Ok(1), "{p2_err}");
    assert_eq!(
        serves.recv_timeout(wait),
        Ok(2),
        "the path was opened once only:\n{p2_err}"
    );
    assert_eq!(p2.kind, "emitted", "{p2:?}\n{p2_err}");
    assert!(
        std::fs::symlink_metadata(&input).is_err(),
        "the path is gone"
    );
    let checkpoint = stored(&model);
    let source = checkpoint
        .provenance
        .baseline_checkpoint
        .clone()
        .expect("the baseline checkpoint named");
    assert_eq!(source.path, input.display().to_string());
    assert_eq!(
        source.sha256,
        sha256_hex(&first),
        "the write hashed a later read of the file (the second read's digest is {})",
        sha256_hex(&second)
    );
    assert_eq!(Some(checkpoint.model_sha256.clone()), p2.model_sha256);
}

/// W10 (R1523-2, F3): the identity the file carries is the one taken at the decide's start, and the
/// write computes none. Here the binary's digest (a part of the identity) reads as one value at the
/// start and as another at the write: the file carries the start's. An identity that cannot be taken
/// refuses `OUT`, typed, at the start (on the start's seam: no input makes the identity fail in a
/// whole run). And F1's other half: a baseline checkpoint that cannot be read at the start is
/// recorded as that, the write (which reads no file) still happens, and the file reads back.
/// RED at `11aeb1613`: `write` took the mode and the attestation, computed the identity itself and
/// read the baseline checkpoint's file (an absent one dropped the write).
#[test]
fn r1520_2_w10_the_identity_is_taken_at_the_decide_s_start() {
    use crate::analyses::borrow_ownership::baseline_checkpoint::hooks::with_exe_sha256;
    ::utils::compilation::run_compiler_on_str(CASCADE_TIE, |tcx| {
        let program = program(tcx);
        let slots = CrateSlots::build(&program);
        let model = all(&slots, SlotKind::Raw);
        let baseline = all(&slots, SlotKind::Ref);
        let dir = scratch("w10");
        let path = dir.join("model.json");
        let absent = dir.join("absent-baseline.json");
        let taken = with_exe_sha256("at-the-start", || {
            execution_guard::checkpoint_hook::with((None, Some(absent.clone())), || {
                start(&program, &slots, OverlapMode::PreciseReplay, FROZEN)
            })
        })
        .unwrap();
        let source = taken
            .baseline_checkpoint
            .clone()
            .expect("the baseline checkpoint named");
        assert_eq!(source.path, absent.display().to_string());
        assert!(
            source.sha256.starts_with("unreadable: "),
            "{}",
            source.sha256
        );
        assert_eq!(
            taken.label(),
            format!(
                "baseline_checkpoint={} sha256={}",
                source.path, source.sha256
            )
        );

        let rows: Result<Vec<_>, String> = Err("not recorded".into());
        with_exe_sha256("at-the-write", || {
            write(
                &path, &program, &slots, &model, &baseline, "receipt", &taken, rows, false, 0.0,
            )
        })
        .unwrap();
        let file = stored(&path);
        assert_eq!(
            file.identity.exe_sha256, "at-the-start",
            "the write computed an identity"
        );
        assert_eq!(file.provenance.baseline_checkpoint, Some(source));
        let same = with_exe_sha256("at-the-start", || {
            read(&path, &program, &slots, OverlapMode::PreciseReplay, FROZEN)
        })
        .unwrap();
        assert!(same.same_exe);
        assert_eq!(same.cached.model, model);
        let later = with_exe_sha256("at-the-write", || {
            read(&path, &program, &slots, OverlapMode::PreciseReplay, FROZEN)
        })
        .unwrap();
        assert!(!later.same_exe);

        // No baseline checkpoint: none named, no file read.
        let plain = start(&program, &slots, OverlapMode::PreciseReplay, FROZEN).unwrap();
        assert_eq!(plain.baseline_checkpoint, None);
        assert_eq!(plain.label(), "baseline_checkpoint=none");
    })
    .unwrap_or_else(|_| panic!("the fixture compiles"));

    let error = start_with(Err("boom".into()), None)
        .err()
        .expect("an identity that cannot be taken is refused");
    assert_eq!(
        error,
        format!("{REFUSED_HEAD}identity (computable != boom)")
    );
}
