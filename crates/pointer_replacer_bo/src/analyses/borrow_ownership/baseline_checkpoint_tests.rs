//! R1490-2 (main 326 §7): the two-process checkpoint mode's witnesses. W3 / W4 / W6 / W7 run in
//! process; W1 / W2 / W8 run the whole rewrite in child processes of this test binary (the switches
//! are read once per process, and the rewrite runs its compiler session on its own thread).

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

/// 322's fixture: `R1468_CASCADE` (three solves in one repair) beside the source / sink tie.
const CASCADE_TIE: &str = r#"
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

/// An effective may-overlap parameter pair: `two` writes through both formals, and `caller` passes
/// one pointer twice. `two` is `pub`, so without the frozen-graph attestation the ABI guard refuses.
const OVERLAP: &str = r#"
pub unsafe fn two(x: *mut i32, y: *mut i32) { *x = 1; *y = 2; }
pub unsafe fn caller(p: *mut i32) -> i32 { two(p, p); *p }
"#;

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

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("crat-r1490-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Every slot `Raw`: a model over the whole universe, for the format witnesses.
fn all_raw(slots: &CrateSlots) -> FxHashMap<SlotRef, SlotKind> {
    let mut model = FxHashMap::default();
    for (&function, universe) in &slots.fn_local_slots {
        for index in 0..universe.len() {
            model.insert(
                SlotRef::Local(function, super::super::slots::SlotId::from_usize(index)),
                SlotKind::Raw,
            );
        }
    }
    model
}

fn stats() -> RoundStats {
    RoundStats {
        repair: RepairMode::Guarded,
        guarded_fallback: Some(GuardedFallback {
            reason: "solver-unknown".to_owned(),
            rounds: 2,
            commits: 5,
        }),
        incumbent_rounds: 2,
        hard_eval_failed: 1,
        rounds: 3,
        commits_conflict: 7,
        ..RoundStats::default()
    }
}

const FROZEN: Option<WholeProgramAttestation> = Some(WholeProgramAttestation::FrozenBenchmarkGraph);

/// W4: the checkpoint round-trips the model by slot key, the receipt's stats and the incumbent flag.
#[test]
fn r1490_2_w4_the_checkpoint_round_trips_the_model_stats_and_flag() {
    ::utils::compilation::run_compiler_on_str(CASCADE_TIE, |tcx| {
        let program = program(tcx);
        let slots = CrateSlots::build(&program);
        let model = all_raw(&slots);
        let here = identity(&program, &slots, OverlapMode::PreciseReplay, FROZEN).unwrap();
        // The extern inputs carry their locations.
        assert!(
            here.compiler
                .externs
                .iter()
                .any(|name| name.contains(".rlib")),
            "{:?}",
            here.compiler.externs
        );
        let digest = super::super::construction::model_digest(&model);
        let only = |path: &Path| {
            let names = std::fs::read_dir(path.parent().unwrap())
                .unwrap()
                .map(|entry| entry.unwrap().file_name())
                .collect::<Vec<_>>();
            assert_eq!(
                names,
                vec![path.file_name().unwrap().to_owned()],
                "no temporary left"
            );
        };
        // A destination named like a temporary file is written and replaced whole as well.
        let tmp_named = scratch("w4-tmp").join("baseline.tmp");
        for _ in 0..2 {
            write(
                &tmp_named,
                &program,
                &slots,
                OverlapMode::PreciseReplay,
                FROZEN,
                &here,
                &model,
                digest.clone(),
                &stats(),
            )
            .expect("write");
            only(&tmp_named);
            read(
                &tmp_named,
                &program,
                &slots,
                &here,
                super::super::construction::model_digest,
            )
            .expect("read");
        }
        let path = scratch("w4").join("baseline.json");
        let bytes = write(
            &path,
            &program,
            &slots,
            OverlapMode::PreciseReplay,
            FROZEN,
            &here,
            &model,
            digest.clone(),
            &stats(),
        )
        .expect("write");
        assert!(bytes > 0);
        only(&path);
        let loaded = read(
            &path,
            &program,
            &slots,
            &here,
            super::super::construction::model_digest,
        )
        .expect("read");
        assert_eq!(loaded.model, model);
        assert_eq!(loaded.slots, model.len());
        assert!(loaded.incumbent, "incumbent_rounds 2 > 0");
        assert_eq!(Stats::of(&loaded.stats), Stats::of(&stats()));
        let checkpoint: Checkpoint =
            serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        assert_eq!(checkpoint.schema, SCHEMA);
        assert_eq!(checkpoint.model_sha256, digest);
    })
    .unwrap_or_else(|error| error.raise());
}

/// W3: a stale or mismatched checkpoint is refused, naming the field; nothing is loaded.
#[test]
fn r1490_2_w3_a_stale_or_mismatched_checkpoint_is_refused() {
    ::utils::compilation::run_compiler_on_str(CASCADE_TIE, |tcx| {
        let program = program(tcx);
        let slots = CrateSlots::build(&program);
        let model = all_raw(&slots);
        let digest = super::super::construction::model_digest(&model);
        let dir = scratch("w3");
        let good = dir.join("good.json");
        let here = identity(&program, &slots, OverlapMode::PreciseReplay, FROZEN).unwrap();
        write(
            &good,
            &program,
            &slots,
            OverlapMode::PreciseReplay,
            FROZEN,
            &here,
            &model,
            digest.clone(),
            &stats(),
        )
        .unwrap();
        let load = |path: &Path| {
            read(
                path,
                &program,
                &slots,
                &here,
                super::super::construction::model_digest,
            )
            .map(|_| ())
        };
        assert_eq!(load(&good), Ok(()));
        let original: Checkpoint = serde_json::from_slice(&std::fs::read(&good).unwrap()).unwrap();
        let mutated = |name: &str, change: &dyn Fn(&mut Checkpoint)| {
            let mut checkpoint = original.clone();
            change(&mut checkpoint);
            let path = dir.join(format!("{name}.json"));
            std::fs::write(&path, serde_json::to_vec(&checkpoint).unwrap()).unwrap();
            path
        };
        let refused_on = |path: PathBuf, field: &str| {
            let error = load(&path).expect_err(field);
            assert!(
                error.starts_with(&format!("{REFUSED_HEAD}{field} (")),
                "{field}: {error}"
            );
        };
        refused_on(
            mutated("schema", &|c| c.schema = "bo-baseline-checkpoint-v0".into()),
            "schema",
        );
        refused_on(
            mutated("key", &|c| c.identity.semantic_key.push('0')),
            "semantic_key",
        );
        // The compiler configuration changes while the sources and the slot universe stay the same.
        refused_on(
            mutated("cfg", &|c| {
                c.identity.compiler.cfgs.push("feature=\"r1490\"".into())
            }),
            "compiler",
        );
        refused_on(
            mutated("deps", &|c| {
                c.identity.compiler.search_files_sha256.push('0')
            }),
            "compiler",
        );
        refused_on(
            mutated("universe", &|c| c.identity.universe_sha256.push('0')),
            "universe",
        );
        refused_on(mutated("exe", &|c| c.identity.exe_sha256.push('0')), "exe");
        refused_on(
            mutated("config", &|c| {
                c.identity.config.fresh_hard_solver = !c.identity.config.fresh_hard_solver
            }),
            "config",
        );
        refused_on(
            mutated("dropped", &|c| {
                let first = c.model.keys().next().unwrap().clone();
                c.model.remove(&first);
            }),
            "slots",
        );
        refused_on(
            mutated("foreign", &|c| {
                let first = c.model.keys().next().unwrap().clone();
                let kind = c.model.remove(&first).unwrap();
                c.model.insert("not::a::slot::_0@d0".into(), kind);
            }),
            "slot",
        );
        refused_on(
            mutated("kind", &|c| {
                let first = c.model.keys().next().unwrap().clone();
                c.model.insert(first, "box".into());
            }),
            "kind",
        );
        refused_on(
            mutated("digest", &|c| c.model_sha256.push('0')),
            "model_sha256",
        );
        let truncated = dir.join("truncated.json");
        let bytes = std::fs::read(&good).unwrap();
        std::fs::write(&truncated, &bytes[..bytes.len() / 2]).unwrap();
        refused_on(truncated, "format");
        refused_on(dir.join("absent.json"), "file");
        // The binary's identity, through the hook: written by one binary, read by another.
        let other = dir.join("other-exe.json");
        hooks::with_exe_sha256("0".repeat(64).as_str(), || {
            let start = identity(&program, &slots, OverlapMode::PreciseReplay, FROZEN).unwrap();
            write(
                &other,
                &program,
                &slots,
                OverlapMode::PreciseReplay,
                FROZEN,
                &start,
                &model,
                digest.clone(),
                &stats(),
            )
            .unwrap();
        });
        refused_on(other, "exe");
        // The configuration, through the fresh-solver hook.
        let fresh = dir.join("fresh-on.json");
        execution_guard::fresh_hard_solver_hook::with(true, || {
            let start = identity(&program, &slots, OverlapMode::PreciseReplay, FROZEN).unwrap();
            write(
                &fresh,
                &program,
                &slots,
                OverlapMode::PreciseReplay,
                FROZEN,
                &start,
                &model,
                digest.clone(),
                &stats(),
            )
            .unwrap();
        });
        refused_on(fresh, "config");
        // An input that changed during the baseline solve: the identity computed at its start differs
        // from the one at the write, so nothing is published.
        let changed = dir.join("changed.json");
        let mut stale = here.clone();
        stale.compiler.search_files_sha256.push('0');
        let error = write(
            &changed,
            &program,
            &slots,
            OverlapMode::PreciseReplay,
            FROZEN,
            &stale,
            &model,
            digest.clone(),
            &stats(),
        )
        .expect_err("changed during the solve");
        assert!(
            error.starts_with(&format!("{REFUSED_HEAD}compiler (")),
            "{error}"
        );
        assert!(!changed.exists());
    })
    .unwrap_or_else(|error| error.raise());
}

/// W6: the surface. Unset is off; both set, a model cache configured, or another A5 mode is refused.
#[test]
fn r1490_2_w6_the_switches_refuse_both_a_cache_and_other_modes() {
    let path = PathBuf::from("/nonexistent/checkpoint.json");
    if execution_guard::checkpoint_paths() == (None, None) {
        assert_eq!(mode(OverlapMode::PreciseReplay), Ok(Mode::Off));
    }
    execution_guard::checkpoint_hook::with((Some(path.clone()), None), || {
        assert_eq!(
            mode(OverlapMode::PreciseReplay),
            Ok(Mode::Write(path.clone()))
        );
        let refused = mode(OverlapMode::Baseline).unwrap_err();
        assert!(
            refused.starts_with(&format!("{REFUSED_HEAD}a5_mode (")),
            "{refused}"
        );
        let refused = mode(OverlapMode::CoarseConstraint).unwrap_err();
        assert!(
            refused.starts_with(&format!("{REFUSED_HEAD}a5_mode (")),
            "{refused}"
        );
        model_cache::with_scratch_cache(|| {
            let refused = mode(OverlapMode::PreciseReplay).unwrap_err();
            assert!(
                refused.starts_with(&format!("{REFUSED_HEAD}cache (")),
                "{refused}"
            );
        });
    });
    execution_guard::checkpoint_hook::with((None, Some(path.clone())), || {
        assert_eq!(
            mode(OverlapMode::PreciseReplay),
            Ok(Mode::Read(path.clone()))
        );
    });
    execution_guard::checkpoint_hook::with((Some(path.clone()), Some(path.clone())), || {
        let refused = mode(OverlapMode::PreciseReplay).unwrap_err();
        assert!(
            refused.starts_with(&format!("{REFUSED_HEAD}switches (")),
            "{refused}"
        );
    });
}

/// W7: a checkpoint whose baseline accepted an incumbent makes process 2's solve uncacheable, as one
/// process's count over the whole solve does; without one, the verdict is the solve's own.
#[test]
fn r1490_2_w7_a_baseline_incumbent_makes_the_resumed_solve_uncacheable() {
    let (_, cacheable) = execution_guard::solve_then_cacheable(true, || seed_incumbent(true));
    assert!(!cacheable);
    let (_, cacheable) = execution_guard::solve_then_cacheable(true, || seed_incumbent(false));
    assert!(cacheable);
}

/// What one child of the two-process witnesses reports.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct ChildResult {
    kind: String,
    reason: Option<String>,
    source: String,
    files: Vec<String>,
    overlap_receipt: String,
    model_sha256: Option<String>,
}

const CHILD_OUT: &str = "CRAT_R1490_2_CHILD_OUT";
const CHILD_ROOT: &str = "CRAT_R1490_2_CHILD_ROOT";
const CHILD_ATTEST: &str = "CRAT_R1490_2_CHILD_ATTEST";

const CHILD_PASS: &str = "CRAT_R1490_2_CHILD_PASS";

/// In a child: run the whole rewrite on `CHILD_ROOT` and write the result to `CHILD_OUT`. With
/// `CHILD_PASS`, the pass instead (`bo_pipeline::rewrite_bo_with_artifacts`), its receipt mapped
/// onto the same fields: `kind` = the outcome, `reason` = the status, `overlap_receipt` = the
/// receipt's `solve`, `files` = the two tree digests, `source` = the file after the pass.
fn child() -> bool {
    let Some(out) = std::env::var_os(CHILD_OUT) else {
        return false;
    };
    let root = PathBuf::from(std::env::var_os(CHILD_ROOT).expect("child root"));
    if std::env::var_os(CHILD_PASS).is_some() {
        let result = match crate::bo_pipeline::rewrite_bo_with_artifacts(
            &root,
            std::iter::empty::<String>(),
            None,
        ) {
            Ok(receipt) => ChildResult {
                kind: receipt.outcome.to_owned(),
                reason: Some(format!(
                    "{} files_changed={}",
                    receipt.status, receipt.files_changed
                )),
                source: std::fs::read_to_string(&root).unwrap(),
                files: vec![receipt.input_tree_sha256, receipt.emitted_tree_sha256],
                overlap_receipt: receipt.solve,
                model_sha256: None,
            },
            Err(error) => ChildResult {
                kind: "error".into(),
                reason: Some(error),
                source: std::fs::read_to_string(&root).unwrap(),
                files: Vec::new(),
                overlap_receipt: String::new(),
                model_sha256: None,
            },
        };
        std::fs::write(out, serde_json::to_vec(&result).unwrap()).unwrap();
        return true;
    }
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
            model_sha256: solve_receipt.map(|receipt| receipt.model_sha256),
        },
        crate::bo_rewriter::RewriteOutcome::Degraded { reason, source, .. } => ChildResult {
            kind: "degraded".into(),
            reason: Some(reason),
            source,
            files: Vec::new(),
            overlap_receipt: String::new(),
            model_sha256: None,
        },
    };
    std::fs::write(out, serde_json::to_vec(&result).unwrap()).unwrap();
    true
}

/// In the parent: run `test` in a child on a fresh copy of `code`, with `env`.
fn spawn(test: &str, code: &str, tag: &str, attest: &str, env: &[(&str, OsString)]) -> ChildResult {
    spawn_with_stderr(test, code, tag, attest, env).0
}

/// [`spawn`], with the child's stderr (the phase log's lines).
fn spawn_with_stderr(
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
        .env(CHILD_OUT, &out)
        .env(CHILD_ROOT, dir.join("lib.rs"))
        .env(CHILD_ATTEST, attest)
        .env_remove("CRAT_BO_CHECKPOINT_OUT")
        .env_remove("CRAT_BO_CHECKPOINT_IN")
        .env_remove("CRAT_BO_CACHE_DIR");
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

/// One process (A) beside two (B1 writes, B2 resumes), on `code`. Returns A, B2 and the checkpoint.
fn one_against_two(
    test: &str,
    code: &str,
    tag: &str,
    attest: &str,
    extra: &[(&str, OsString)],
) -> (ChildResult, ChildResult, Checkpoint) {
    let checkpoint = scratch(&format!("{tag}-ckpt")).join("baseline.json");
    let a = spawn(test, code, &format!("{tag}-a"), attest, extra);
    let mut out = extra.to_vec();
    out.push((
        "CRAT_BO_CHECKPOINT_OUT",
        checkpoint.clone().into_os_string(),
    ));
    let b1 = spawn(test, code, &format!("{tag}-b1"), attest, &out);
    // W2: process 1's typed status -- not a decline -- with the tree left as the input.
    assert_eq!(b1.kind, "degraded", "{b1:?}");
    let reason = b1.reason.clone().unwrap();
    assert!(reason.contains(HEAD), "{reason}");
    assert_eq!(b1.source, code);
    assert!(checkpoint.exists(), "process 1 wrote no checkpoint");
    let stored: Checkpoint = serde_json::from_slice(&std::fs::read(&checkpoint).unwrap()).unwrap();
    assert_eq!(stored.schema, SCHEMA);
    assert!(
        reason.contains(&format!("{} slots", stored.model.len())),
        "{reason}"
    );
    let mut input = extra.to_vec();
    input.push(("CRAT_BO_CHECKPOINT_IN", checkpoint.into_os_string()));
    let b2 = spawn(test, code, &format!("{tag}-b2"), attest, &input);
    (a, b2, stored)
}

/// W1 (a) + W2: on the cascade-and-tie fixture, two processes give one process's emitted tree,
/// receipt and model; process 1 ends `checkpointed` with the tree left as the input. RED at
/// `cd1c6897e`: the switch is not read, so process 1 emits and writes no checkpoint.
#[test]
fn r1490_2_w1a_two_processes_equal_one_on_the_cascade_and_tie() {
    if child() {
        return;
    }
    let test = "analyses::borrow_ownership::baseline_checkpoint::tests::r1490_2_w1a_two_processes_equal_one_on_the_cascade_and_tie";
    let (a, b2, _) = one_against_two(test, CASCADE_TIE, "w1a", "frozen", &[]);
    assert_eq!(a.kind, "emitted", "{a:?}");
    assert_eq!(b2, a);
}

/// W1 (b): on a fixture with an effective may-overlap pair, the precise stage changes the model
/// (the baseline model in the checkpoint differs from the accepted one), and two processes give
/// one process's result.
#[test]
fn r1490_2_w1b_two_processes_equal_one_where_the_precise_replay_changes_the_model() {
    if child() {
        return;
    }
    let test = "analyses::borrow_ownership::baseline_checkpoint::tests::r1490_2_w1b_two_processes_equal_one_where_the_precise_replay_changes_the_model";
    let (a, b2, stored) = one_against_two(test, OVERLAP, "w1b", "frozen", &[]);
    assert_eq!(a.kind, "emitted", "{a:?}");
    assert_eq!(b2, a);
    assert!(
        a.overlap_receipt.contains("a5_abi_guard=permitted"),
        "{}",
        a.overlap_receipt
    );
    assert!(a.model_sha256.is_some(), "{a:?}");
    assert_ne!(
        Some(&stored.model_sha256),
        a.model_sha256.as_ref(),
        "the precise replay must change the model, or the witness is vacuous"
    );
}

/// W1 (c): without the attestation the ABI guard refuses; under `PreciseReplay` the refined branch
/// re-constructs and re-verifies (it never returns the baseline model), and two processes give one
/// process's result.
#[test]
fn r1490_2_w1c_two_processes_equal_one_through_the_abi_refusal() {
    if child() {
        return;
    }
    let test = "analyses::borrow_ownership::baseline_checkpoint::tests::r1490_2_w1c_two_processes_equal_one_through_the_abi_refusal";
    let (a, b2, stored) = one_against_two(test, OVERLAP, "w1c", "none", &[]);
    assert_eq!(a.kind, "emitted", "{a:?}");
    assert!(
        a.overlap_receipt.contains("a5_abi_guard=refused:"),
        "{}",
        a.overlap_receipt
    );
    assert!(
        a.overlap_receipt.contains("soundness_mode=a14_a16_refined"),
        "{}",
        a.overlap_receipt
    );
    assert_eq!(b2, a);
    assert_eq!(stored.identity.config.attestation, "None");
}

/// W8: a baseline that accepted an optimize incumbent is transferred: the checkpoint carries the
/// incumbent rounds and the flag, and the resumed receipt counts at least those rounds. The models
/// are not compared: incumbents need not repeat. An incumbent needs an optimize that misses its
/// query budget while every hard check meets it: 60 functions at a 12-ms budget (3 of 3 on an idle
/// machine; 30 functions at 5-7 ms and 60 at 10-15 ms also pass, smaller budgets decline, larger
/// ones finish in time). Timing-dependent by nature -- an incumbent depends on the machine and its
/// load (main 388 O2) -- so it is ignored in the suite and run explicitly; `CRAT_R1490_2_W8_FNS` /
/// `CRAT_R1490_2_W8_MS` override the two numbers.
#[test]
#[ignore = "timing-dependent (an optimize incumbent at a 12-ms query budget); run explicitly"]
fn r1490_2_w8_an_incumbent_baseline_is_transferred() {
    if child() {
        return;
    }
    let test = "analyses::borrow_ownership::baseline_checkpoint::tests::r1490_2_w8_an_incumbent_baseline_is_transferred";
    // A budget the optimize cannot meet while each hard check, a propagation, still does.
    let budget_ms = std::env::var("CRAT_R1490_2_W8_MS").unwrap_or_else(|_| "12".into());
    let functions: usize = std::env::var("CRAT_R1490_2_W8_FNS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(60);
    let timeout = [(
        "CRAT_BO_QUERY_TIMEOUT_MS",
        OsString::from(budget_ms.clone()),
    )];
    let mut code = String::new();
    for k in 0..functions {
        code.push_str(&format!(
            "pub unsafe fn f{k}(p: *mut i32, q: *mut i32) -> i32 {{ let a = p; let b = q; *a = *b + {k}; *a }}\n"
        ));
    }
    code.push_str("pub unsafe fn driver(p: *mut i32, q: *mut i32) -> i32 { let mut s = 0;");
    for k in 0..functions {
        code.push_str(&format!(" s += f{k}(p, q);"));
    }
    code.push_str(" s }\n");
    let (_, b2, stored) = one_against_two(test, &code, "w8", "frozen", &timeout);
    assert!(
        stored.stats.incumbent_rounds >= 1 && stored.incumbent,
        "no baseline round accepted an incumbent: the witness would be vacuous: {:?}",
        stored.stats
    );
    assert_eq!(
        stored.identity.config.query_timeout_ms.to_string(),
        budget_ms
    );
    let rounds = b2
        .overlap_receipt
        .lines()
        .find_map(|line| line.strip_prefix("incumbent_rounds="))
        .unwrap_or_else(|| panic!("{b2:?}"))
        .parse::<usize>()
        .unwrap();
    assert!(
        rounds >= stored.stats.incumbent_rounds,
        "{rounds} {:?}",
        stored.stats
    );
}

/// Task 36 (324 (v-a)): with the phase log on, the precise verify writes its `verify:` sub-marks
/// between its own `start` and `end` lines, as the baseline verify does (log only). RED at
/// `cd1c6897e`: the precise verify ran outside `with_sub_marks`, so no sub-mark fell there.
#[test]
fn r1490_2_t36_the_precise_verify_writes_its_sub_marks() {
    if child() {
        return;
    }
    let test = "analyses::borrow_ownership::baseline_checkpoint::tests::r1490_2_t36_the_precise_verify_writes_its_sub_marks";
    let log = [("CRAT_BO_PHASE_LOG", OsString::from("on"))];
    let (result, stderr) = spawn_with_stderr(test, OVERLAP, "t36", "frozen", &log);
    assert_eq!(result.kind, "emitted", "{result:?}");
    let lines: Vec<&str> = stderr
        .lines()
        .filter(|line| line.starts_with("[bo-phase] "))
        .collect();
    let at = |edge: &str| {
        lines
            .iter()
            .position(|line| line.starts_with(&format!("[bo-phase] solve:precise_verify {edge} ")))
            .unwrap_or_else(|| panic!("no precise_verify {edge}:\n{stderr}"))
    };
    let (start, end) = (at("start"), at("end"));
    let inside = lines[start..end]
        .iter()
        .filter(|line| line.starts_with("[bo-phase] verify:solve "))
        .count();
    assert!(
        inside > 0,
        "no verify:solve sub-mark inside the precise verify:\n{stderr}"
    );
}

/// W2 at the pass: process 1's receipt is `checkpointed` / `baseline-checkpoint` with the input's
/// tree and nothing written (the pass returns `Ok`, so `crat` exits 0); a refused checkpoint is an
/// error (`crat` exits 1) and nothing is written either.
#[test]
fn r1490_2_w2_the_pass_ends_checkpointed_with_the_input_tree_and_a_refusal_fails() {
    if child() {
        return;
    }
    let test = "analyses::borrow_ownership::baseline_checkpoint::tests::r1490_2_w2_the_pass_ends_checkpointed_with_the_input_tree_and_a_refusal_fails";
    let checkpoint = scratch("w2p-ckpt").join("baseline.json");
    let pass = ("CRAT_R1490_2_CHILD_PASS", OsString::from("1"));
    let out = (
        "CRAT_BO_CHECKPOINT_OUT",
        checkpoint.clone().into_os_string(),
    );
    let b1 = spawn(test, CASCADE_TIE, "w2p-b1", "frozen", &[pass.clone(), out]);
    assert_eq!(b1.kind, "checkpointed", "{b1:?}");
    assert_eq!(
        b1.reason.as_deref(),
        Some("baseline-checkpoint files_changed=0")
    );
    assert_eq!(b1.files[0], b1.files[1], "the tree is the input's");
    assert_eq!(b1.source, CASCADE_TIE);
    assert!(
        b1.overlap_receipt
            .starts_with("BaselineCheckpoint(\"checkpointed ("),
        "{b1:?}"
    );
    assert!(checkpoint.exists());
    // A checkpoint of another program is refused at the semantic key; the pass fails.
    let other = format!("{CASCADE_TIE}\npub fn r1490_extra() {{}}\n");
    let input = ("CRAT_BO_CHECKPOINT_IN", checkpoint.into_os_string());
    let refused = spawn(test, &other, "w2p-refused", "frozen", &[pass, input]);
    assert_eq!(refused.kind, "error", "{refused:?}");
    assert!(
        refused
            .reason
            .as_deref()
            .is_some_and(|reason| reason.contains(&format!("{REFUSED_HEAD}semantic_key ("))),
        "{refused:?}"
    );
    assert_eq!(refused.source, other);
    // A refusal whose text names process 1's marker -- an OUT path that cannot be written -- is an
    // error, never a checkpoint.
    let marker = scratch("w2p-marker")
        .join("absent")
        .join("checkpointed (run.json");
    let pass = ("CRAT_R1490_2_CHILD_PASS", OsString::from("1"));
    let out = ("CRAT_BO_CHECKPOINT_OUT", marker.clone().into_os_string());
    let failed = spawn(test, CASCADE_TIE, "w2p-marker-b1", "frozen", &[pass, out]);
    assert_eq!(failed.kind, "error", "{failed:?}");
    assert!(
        failed
            .reason
            .as_deref()
            .is_some_and(|reason| reason.contains(&format!("{REFUSED_HEAD}write ("))),
        "{failed:?}"
    );
    assert!(!marker.exists());
}

/// The compiler identity digests the crate files of the `-L` directories only: a checkpoint or any
/// other file beside them changes nothing; a changed crate file changes the digest.
#[test]
fn r1490_2_the_search_digest_reads_crate_files_only() {
    let dir = scratch("digest");
    std::fs::write(dir.join("libdep-1.rlib"), b"rlib").unwrap();
    std::fs::write(dir.join("libdep-1.rmeta"), b"rmeta").unwrap();
    let dirs = [dir.clone()];
    let before = files_digest(&dirs).unwrap();
    std::fs::write(dir.join("baseline.json"), b"{}").unwrap();
    std::fs::write(dir.join("dep-1.d"), b"deps").unwrap();
    assert_eq!(files_digest(&dirs).unwrap(), before);
    std::fs::write(dir.join("libdep-1.rlib"), b"rlib2").unwrap();
    assert_ne!(files_digest(&dirs).unwrap(), before);
}
