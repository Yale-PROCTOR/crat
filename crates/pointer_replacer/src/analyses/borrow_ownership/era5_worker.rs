//! Ignored evaluation-host worker. No ambient/default job can enter a model.
//! This harness is registered only under cfg(test); it is not a rewriter entry.

use std::{
    collections::BTreeMap,
    fs,
    io::Write,
    path::{Component, Path, PathBuf},
};

use rustc_hir::{ItemKind, OwnerNode};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use super::{
    a5_overlap::{A5Mode, WholeProgramAttestation},
    cache_contract::{self, CompleteEntry, SemanticInputs},
    construction::solve_bo_a5_config_reporting,
    crate_slots::CrateSlots,
    era5_instruments::{REQUIRED_PROGRAMS, ResourceSeal, validate_resources},
    execution_guard::{self, ExecutionRole},
    export,
    model_cache::{self, CachedModel},
    mutability_facts::MutFacts,
    origins::compute_origins,
};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct FileSeal {
    path: PathBuf,
    sha256: String,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SemanticSeal {
    analysis: String,
    toolchain: String,
    dependencies: String,
    configuration: String,
}
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Job {
    schema: String,
    admission: String,
    program: String,
    host: String,
    host_role: String,
    input: FileSeal,
    input_root: PathBuf,
    input_manifest: FileSeal,
    source: FileSeal,
    toolchain: FileSeal,
    dependencies: FileSeal,
    launch: FileSeal,
    binary: FileSeal,
    semantic: SemanticSeal,
    expected_inputs: Option<SemanticInputs>,
    expected_key: Option<String>,
    resources: ResourceSeal,
    reservation: String,
    environment: BTreeMap<String, String>,
    cache_dir: PathBuf,
    cache_namespace: String,
    receipt: PathBuf,
}

fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}
fn read_sealed(seal: &FileSeal) -> Result<Vec<u8>, String> {
    if !seal.path.is_absolute() || !hex(&seal.sha256) {
        return Err("invalid sealed file identity".into());
    }
    let bytes = fs::read(&seal.path).map_err(|error| error.to_string())?;
    if sha(&bytes) != seal.sha256 {
        return Err(format!("sealed file changed: {}", seal.path.display()));
    }
    Ok(bytes)
}

fn validate(job: &Job) -> Result<BTreeMap<String, String>, String> {
    if job.schema != "era5a-model-job-v1"
        || job.admission != "era5a-freeze-seat-accepted"
        || !REQUIRED_PROGRAMS.contains(&job.program.as_str())
        || job.host_role != "evaluation"
        || job
            .host
            .split('.')
            .next()
            .is_some_and(|host| host.starts_with("lambda7"))
        || job.cache_namespace != "era5a-candidate"
        || !job.cache_dir.is_absolute()
        || !job.receipt.is_absolute()
        || !job.input_root.is_absolute()
    {
        return Err("job lacks the sealed evaluation-host admission".into());
    }
    let host =
        fs::read_to_string("/proc/sys/kernel/hostname").map_err(|error| error.to_string())?;
    if host.trim() != job.host || job.resources.host != job.host {
        return Err("actual evaluation host mismatch".into());
    }
    let memory = fs::read_to_string("/proc/meminfo").map_err(|error| error.to_string())?;
    let total = memory
        .lines()
        .find_map(|line| {
            line.strip_prefix("MemTotal:")?
                .split_whitespace()
                .next()?
                .parse::<u64>()
                .ok()
        })
        .ok_or("missing physical-memory attestation")?
        / 1024;
    if total != job.resources.physical_mib {
        return Err("physical-memory seal changed".into());
    }
    validate_resources(&job.resources, &[job.reservation.clone()])
        .map_err(|error| format!("resource seal: {error:?}"))?;
    if execution_guard::QUERY_TIMEOUT_MS != 600_000 {
        return Err("query guard changed".into());
    }
    for seal in [
        &job.input,
        &job.source,
        &job.toolchain,
        &job.dependencies,
        &job.launch,
        &job.binary,
    ] {
        read_sealed(seal)?;
    }
    if sha(
        &fs::read(std::env::current_exe().map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?,
    ) != job.binary.sha256
    {
        return Err("running binary is not the sealed worker".into());
    }
    if [
        &job.semantic.analysis,
        &job.semantic.toolchain,
        &job.semantic.dependencies,
        &job.semantic.configuration,
    ]
    .iter()
    .any(|value| !hex(value))
        || job.semantic.toolchain != job.toolchain.sha256
        || job.semantic.dependencies != job.dependencies.sha256
        || job.expected_key.as_ref().is_some_and(|key| !hex(key))
    {
        return Err("missing semantic digest attestation".into());
    }
    for (key, expected) in &job.environment {
        if std::env::var(key).ok().as_ref() != Some(expected) {
            return Err(format!("sealed environment mismatch: {key}"));
        }
    }
    for (key, expected) in [
        ("CRAT_ERA5_EXECUTION_ROLE", "derive".to_owned()),
        ("CRAT_ERA5_PROGRAM", job.program.clone()),
        ("CRAT_ERA5_INPUT_ROOT", job.input_root.display().to_string()),
        ("CRAT_ERA5_TOOLCHAIN_DIGEST", job.semantic.toolchain.clone()),
        (
            "CRAT_ERA5_DEPENDENCY_DIGEST",
            job.semantic.dependencies.clone(),
        ),
        ("CRAT_ERA5_LAUNCH_DIGEST", job.launch.sha256.clone()),
    ] {
        if std::env::var(key).ok() != Some(expected) {
            return Err(format!("missing worker environment: {key}"));
        }
    }
    let manifest: BTreeMap<String, String> = serde_json::from_value(super::strict_json::parse(
        &read_sealed(&job.input_manifest)?,
    )?)
    .map_err(|error| error.to_string())?;
    let root = job
        .input_root
        .canonicalize()
        .map_err(|error| error.to_string())?;
    if manifest.is_empty() {
        return Err("empty input-file manifest".into());
    }
    for (logical, digest) in &manifest {
        if !hex(digest)
            || logical.is_empty()
            || !Path::new(logical)
                .components()
                .all(|part| matches!(part, Component::Normal(_)))
        {
            return Err("noncanonical input manifest path or digest".into());
        }
        let path = root
            .join(logical)
            .canonicalize()
            .map_err(|error| error.to_string())?;
        if !path.starts_with(&root)
            || sha(&fs::read(path).map_err(|error| error.to_string())?) != *digest
        {
            return Err(format!("input manifest mismatch: {logical}"));
        }
    }
    let entry = job
        .input
        .path
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let logical = entry
        .strip_prefix(&root)
        .map_err(|_| "input lies outside its sealed root")?
        .to_str()
        .ok_or("non-UTF8 input")?;
    if manifest.get(logical) != Some(&job.input.sha256) {
        return Err("entry input absent from manifest".into());
    }
    Ok(manifest)
}

#[derive(Debug, Serialize)]
struct Failure {
    kind: &'static str,
    detail: String,
}
#[derive(Debug, Serialize)]
struct Completed {
    key: String,
    inputs: SemanticInputs,
    cache_entry: PathBuf,
    entry_sha256: String,
    payload_sha256: String,
    export_sha256: String,
    model_entries: usize,
}

fn derive(job: &Job, manifest: &BTreeMap<String, String>) -> Result<Completed, Failure> {
    let invalid = |detail: String| Failure {
        kind: "invalid",
        detail,
    };
    ::utils::compilation::run_compiler_on_path(&job.input.path, |tcx| {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let mode = A5Mode::PreciseReplay;
        let attestation = Some(WholeProgramAttestation::FrozenBenchmarkGraph);
        if model_cache::current_analysis_digest() != job.semantic.analysis {
            return Err(invalid("analysis tree changed before derivation".into()));
        }
        let inputs = model_cache::semantic_inputs(&program, mode, attestation).map_err(&invalid)?;
        if inputs.program != job.program
            || inputs.analysis != job.semantic.analysis
            || inputs.toolchain != job.semantic.toolchain
            || inputs.dependencies != job.semantic.dependencies
            || inputs.configuration != job.semantic.configuration
            || inputs
                .files
                .iter()
                .any(|(path, digest)| manifest.get(path) != Some(digest))
            || job
                .expected_inputs
                .as_ref()
                .is_some_and(|expected| expected != &inputs)
        {
            return Err(invalid(
                "compiler semantic inputs differ from the sealed job".into(),
            ));
        }
        let key = cache_contract::semantic_key(&inputs).map_err(&invalid)?;
        if job
            .expected_key
            .as_ref()
            .is_some_and(|expected| expected != &key)
        {
            return Err(invalid("optional exact key mismatch".into()));
        }
        model_cache::with_test_config(false, &job.cache_dir, || {
            if model_cache::configured_entry_path(&key).is_some_and(|path| path.exists()) {
                return Err(invalid(
                    "candidate entry already exists; no overwrite or rerun".into(),
                ));
            }
            execution_guard::with_role(ExecutionRole::Derive, || {
                execution_guard::clear_unknown();
                let before = execution_guard::model_entries();
                let (result, _) = export::with_bo_export(|| {
                    let slots = CrateSlots::build(&program);
                    let origins = compute_origins(&program);
                    let mutability = MutFacts::from_program(&program);
                    let solved = solve_bo_a5_config_reporting(
                        &program,
                        &slots,
                        &origins,
                        &mutability,
                        mode,
                        attestation,
                    );
                    if model_cache::current_analysis_digest() != job.semantic.analysis {
                        return Err(invalid("analysis tree changed during derivation".into()));
                    }
                    if validate(job).map_err(&invalid)? != *manifest {
                        return Err(invalid("source seals changed during derivation".into()));
                    }
                    let verified =
                        solved.map_err(|error| match execution_guard::last_unknown() {
                            Some(unknown) => Failure {
                                kind: "unknown",
                                detail: format!("{unknown:?}"),
                            },
                            None => Failure {
                                kind: "decline",
                                detail: format!("{error:?}"),
                            },
                        })?;
                    let cached = CachedModel {
                        model: verified.model,
                        baseline_model: verified.baseline_model,
                        a5_receipt: verified.receipt,
                    };
                    let path =
                        model_cache::store(tcx, &program, &slots, &cached, mode, attestation)
                            .ok_or_else(|| invalid("complete-entry publication failed".into()))?;
                    let bytes = fs::read(&path).map_err(|error| invalid(error.to_string()))?;
                    let entry: CompleteEntry = cache_contract::decode(&bytes).map_err(&invalid)?;
                    let delta = execution_guard::model_entries()
                        .checked_sub(before)
                        .ok_or_else(|| invalid("model counter decreased".into()))?;
                    if delta != 1 || entry.inputs != inputs || entry.key != key {
                        return Err(invalid("entry/key/model-entry custody mismatch".into()));
                    }
                    let payload =
                        serde_json::to_vec(&(&entry.model, &entry.baseline, &entry.receipt))
                            .map_err(|error| invalid(error.to_string()))?;
                    let exports = serde_json::to_vec(&(&entry.exports, &entry.origin))
                        .map_err(|error| invalid(error.to_string()))?;
                    Ok(Completed {
                        key: key.clone(),
                        inputs: inputs.clone(),
                        cache_entry: path,
                        entry_sha256: sha(&bytes),
                        payload_sha256: sha(&payload),
                        export_sha256: sha(&exports),
                        model_entries: delta,
                    })
                });
                result
            })
        })
    })
    .map_err(|error| Failure {
        kind: "compiler",
        detail: format!("{error:?}"),
    })?
}

#[test]
#[ignore = "sealed evaluation-host model job only; never run during source phases"]
fn era5_model_worker() {
    let path = std::env::var("CRAT_ERA5_JOB_PATH")
        .expect("explicit sealed job required; no default worker");
    let expected = std::env::var("CRAT_ERA5_JOB_SHA256").expect("detached job digest required");
    let bytes = fs::read(path).expect("read sealed job");
    assert!(
        hex(&expected) && sha(&bytes) == expected,
        "job digest mismatch"
    );
    let job: Job =
        serde_json::from_value(super::strict_json::parse(&bytes).expect("unique job keys"))
            .expect("sealed job schema");
    let outcome = validate(&job)
        .map_err(|detail| Failure {
            kind: "validation",
            detail,
        })
        .and_then(|manifest| derive(&job, &manifest));
    let receipt = serde_json::json!({"schema":"era5a-worker-receipt-v1", "program":job.program,
        "host":job.host,"job_sha256":expected,"source_sha256":job.source.sha256,
        "toolchain_sha256":job.toolchain.sha256,"launch_sha256":job.launch.sha256,
        "status":if outcome.is_ok(){"complete"}else{"failure"},
        "completed":outcome.as_ref().ok(),"failure":outcome.as_ref().err()});
    assert!(
        job.receipt.is_absolute(),
        "receipt path must be sealed and absolute"
    );
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&job.receipt)
        .expect("create new worker receipt");
    file.write_all(&serde_json::to_vec(&receipt).unwrap())
        .expect("write worker receipt");
    file.sync_all().expect("sync worker receipt");
    assert!(outcome.is_ok(), "worker failed: {receipt}");
}
