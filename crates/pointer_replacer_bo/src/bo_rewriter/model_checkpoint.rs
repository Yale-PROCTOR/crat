//! R1520-2 (main 336 §A; the user's word in the seat's session 11-12, "1로 하자."): the model
//! checkpoint. The accepted model is put on disk at the `decide:store` point, before `finish_decide`
//! starts, so that a later process can run the decision stage again from it without any solver.
//!
//! - `CRAT_BO_MODEL_CHECKPOINT_OUT=<path>`: after the solve, write one JSON file
//!   (`bo-model-checkpoint-v1`). It holds this process's identity, the accepted model, the overlap
//!   baseline (both by slot key), the overlap receipt, the argument-order receipts the emission's
//!   hoist reads, and the provenance.
//! - `CRAT_BO_MODEL_CHECKPOINT_IN=<path>`: before the memo and the disk cache, read that file,
//!   check it, and go to `finish_decide` the way a cache hit does (`cached_rewriter_plans`: the
//!   overlap plan is re-derived from the baseline and checked against the receipt, with no solver).
//!   Every difference is a typed refusal. A refusal never falls through to a solve.
//!
//! Both are measurement switches, for a run the user's word names only: never in a gate, never on
//! the 17 or the 376, off by default, and not part of the model cache's key. An empty value counts
//! as unset. Both are read once per process.
//!
//! The binary's identity (`exe_sha256`) is recorded, not refused (main 336 §A6, the user's choice
//! R1520-1). The reader reports whether the writer's binary equals its own, in its line and in the
//! solve receipt's `cache_status`. A model read under another binary is a measurement, never a
//! number of record.
//!
//! This module lives outside `src/analyses`, so the analysis fingerprint of record is unchanged.
//! The argument-order rows are turned into hoist keys by a copy of `model_cache`'s loader
//! ([`hoists`]), which witness W5 pins against the original.

use std::{
    collections::BTreeMap,
    io::Write,
    path::{Path, PathBuf},
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        baseline_checkpoint::{self, Identity},
        crate_slots::CrateSlots,
        model_cache,
        param_overlap::{OverlapMode, WholeProgramAttestation},
        portable_export::ArgOrderRow,
        solver::SlotRef,
    },
    utils::rustc::RustProgram,
};

/// The file's schema.
pub(crate) const SCHEMA: &str = "bo-model-checkpoint-v1";

/// The head of every refusal.
pub(crate) const REFUSED_HEAD: &str = "model checkpoint refused: ";

/// The head of the one stderr line each switch writes (whether or not the phase log is on).
pub(crate) const LINE_HEAD: &str = "[bo-model-checkpoint]";

/// The argument-order receipts as `model_cache::prepared_arg_order_applied` returned them: the rows,
/// or the reason they were not recorded. Kept exactly, so the reader's hoists equal the writer's.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum ArgOrder {
    Rows(Vec<ArgOrderRow>),
    NotRecorded(String),
}

impl ArgOrder {
    fn of(result: Result<Vec<ArgOrderRow>, String>) -> Self {
        match result {
            Ok(rows) => Self::Rows(rows),
            Err(reason) => Self::NotRecorded(reason),
        }
    }

    fn result(&self) -> Result<Vec<ArgOrderRow>, String> {
        match self {
            Self::Rows(rows) => Ok(rows.clone()),
            Self::NotRecorded(reason) => Err(reason.clone()),
        }
    }

    /// For the lines: `ok:<rows>` or `not-recorded`.
    pub(crate) fn label(&self) -> String {
        match self {
            Self::Rows(rows) => format!("ok:{}", rows.len()),
            Self::NotRecorded(_) => "not-recorded".to_owned(),
        }
    }
}

/// The baseline checkpoint a two-process solve resumed from.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BaselineSource {
    pub(crate) path: String,
    /// SHA-256 of the file's bytes.
    pub(crate) sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Provenance {
    /// `Some` when the writing process resumed from a baseline checkpoint (`CRAT_BO_CHECKPOINT_IN`).
    pub(crate) baseline_checkpoint: Option<BaselineSource>,
    /// Whether any round of the solve accepted an optimize incumbent (the solve was not cacheable).
    pub(crate) incumbent: bool,
    /// The solve's wall, as the solve receipt writes it.
    pub(crate) solve_wall_s: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ModelCheckpoint {
    pub(crate) schema: String,
    /// `baseline_checkpoint::identity` at the write.
    pub(crate) identity: Identity,
    /// The accepted model: slot key -> kind label (`model_cache::model_map`).
    pub(crate) model: BTreeMap<String, String>,
    /// `model_cache::model_bytes_sha256` of the accepted model (the solve receipt's own digest).
    pub(crate) model_sha256: String,
    /// The overlap planning baseline, the same way.
    pub(crate) baseline: BTreeMap<String, String>,
    pub(crate) baseline_sha256: String,
    /// The construction receipt of the solve, verbatim.
    pub(crate) overlap_receipt: String,
    pub(crate) arg_order: ArgOrder,
    pub(crate) provenance: Provenance,
}

/// What the reader hands the decide.
pub(crate) struct Loaded {
    pub(crate) cached: model_cache::CachedModel,
    pub(crate) arg_order: ArgOrder,
    pub(crate) model_sha256: String,
    /// Whether the writer's binary is this one.
    pub(crate) same_exe: bool,
    pub(crate) incumbent: bool,
    pub(crate) slots: usize,
}

/// The two switches, `(out, in)`, read once. An empty value is unset.
pub(crate) fn paths() -> (Option<PathBuf>, Option<PathBuf>) {
    static PATHS: std::sync::OnceLock<(Option<PathBuf>, Option<PathBuf>)> =
        std::sync::OnceLock::new();
    PATHS
        .get_or_init(|| {
            let read = |name: &str| {
                std::env::var_os(name)
                    .filter(|value| !value.is_empty())
                    .map(PathBuf::from)
            };
            (
                read("CRAT_BO_MODEL_CHECKPOINT_OUT"),
                read("CRAT_BO_MODEL_CHECKPOINT_IN"),
            )
        })
        .clone()
}

fn refused(field: &str, expected: &str, found: &str) -> String {
    format!("{REFUSED_HEAD}{field} ({expected} != {found})")
}

/// The switches as this decide reads them, refused before anything is solved or read. `IN` stands
/// alone: not with `OUT`, a baseline checkpoint switch or a model cache. `OUT` does not go with
/// process 1 (`CRAT_BO_CHECKPOINT_OUT`), which ends before any model is accepted. Either needs the
/// frame's mode (`PreciseReplay` over the frozen graph), the only mode the cache-hit path rebuilds.
pub(crate) fn switches(
    a5_mode: OverlapMode,
    attestation: Option<WholeProgramAttestation>,
    (out, input): (Option<PathBuf>, Option<PathBuf>),
) -> Result<(Option<PathBuf>, Option<PathBuf>), String> {
    if out.is_none() && input.is_none() {
        return Ok((None, None));
    }
    let (baseline_out, baseline_in) =
        crate::analyses::borrow_ownership::execution_guard::checkpoint_paths();
    if input.is_some() {
        if out.is_some() {
            return Err(refused(
                "switches",
                "CRAT_BO_MODEL_CHECKPOINT_IN alone",
                "with CRAT_BO_MODEL_CHECKPOINT_OUT",
            ));
        }
        if baseline_out.is_some() || baseline_in.is_some() {
            return Err(refused(
                "switches",
                "CRAT_BO_MODEL_CHECKPOINT_IN alone",
                "with CRAT_BO_CHECKPOINT_OUT / _IN",
            ));
        }
        if model_cache::dir().is_some() {
            return Err(refused(
                "switches",
                "CRAT_BO_MODEL_CHECKPOINT_IN alone",
                "with CRAT_BO_CACHE_DIR",
            ));
        }
    }
    if out.is_some() && baseline_out.is_some() {
        return Err(refused(
            "switches",
            "CRAT_BO_MODEL_CHECKPOINT_OUT without CRAT_BO_CHECKPOINT_OUT",
            "both",
        ));
    }
    if a5_mode != OverlapMode::PreciseReplay {
        return Err(refused(
            "a5_mode",
            OverlapMode::PreciseReplay.label(),
            a5_mode.label(),
        ));
    }
    if attestation != Some(WholeProgramAttestation::FrozenBenchmarkGraph) {
        return Err(refused(
            "attestation",
            "FrozenBenchmarkGraph",
            &format!("{attestation:?}"),
        ));
    }
    Ok((out, input))
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Write the model checkpoint to `path`, atomically (a temporary file beside it, then a rename).
/// Returns the file's size in bytes.
#[allow(clippy::too_many_arguments)]
pub(crate) fn write(
    path: &Path,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    baseline: &FxHashMap<SlotRef, SlotKind>,
    overlap_receipt: &str,
    a5_mode: OverlapMode,
    attestation: Option<WholeProgramAttestation>,
    arg_order: Result<Vec<ArgOrderRow>, String>,
    incumbent: bool,
    solve_secs: f64,
) -> Result<usize, String> {
    let tcx = program.tcx;
    let identity = baseline_checkpoint::identity(program, slots, a5_mode, attestation)?;
    let rendered = |map: &FxHashMap<SlotRef, SlotKind>, what: &str| {
        model_cache::model_map(tcx, slots, map)
            .ok_or_else(|| format!("{what}: an unrenderable slot key"))
    };
    let digest = |map: &FxHashMap<SlotRef, SlotKind>, what: &str| {
        model_cache::model_bytes_sha256(tcx, slots, map)
            .ok_or_else(|| format!("{what}: an unrenderable slot key"))
    };
    let baseline_checkpoint =
        match crate::analyses::borrow_ownership::execution_guard::checkpoint_paths().1 {
            Some(input) => Some(BaselineSource {
                path: input.display().to_string(),
                sha256: sha256_hex(
                    &std::fs::read(&input).map_err(|e| format!("{}: {e}", input.display()))?,
                ),
            }),
            None => None,
        };
    let checkpoint = ModelCheckpoint {
        schema: SCHEMA.to_owned(),
        identity,
        model: rendered(model, "model")?,
        model_sha256: digest(model, "model")?,
        baseline: rendered(baseline, "baseline")?,
        baseline_sha256: digest(baseline, "baseline")?,
        overlap_receipt: overlap_receipt.to_owned(),
        arg_order: ArgOrder::of(arg_order),
        provenance: Provenance {
            baseline_checkpoint,
            incumbent,
            solve_wall_s: format!("{solve_secs:.6}"),
        },
    };
    let text = serde_json::to_vec(&checkpoint).map_err(|e| format!("serialize: {e}"))?;
    let name = path
        .file_name()
        .ok_or_else(|| format!("{}: no file name", path.display()))?;
    let temporary = path.with_file_name(format!(
        ".{}.{}.partial",
        name.to_string_lossy(),
        std::process::id()
    ));
    {
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
            .map_err(|e| format!("{}: {e}", temporary.display()))?;
        if let Err(error) = file.write_all(&text).and_then(|()| file.sync_all()) {
            let _ = std::fs::remove_file(&temporary);
            return Err(format!("{}: {error}", temporary.display()));
        }
    }
    if let Err(error) = std::fs::rename(&temporary, path) {
        let _ = std::fs::remove_file(&temporary);
        return Err(format!("{}: {error}", path.display()));
    }
    let parent = match path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => parent,
        _ => Path::new("."),
    };
    std::fs::File::open(parent)
        .and_then(|directory| directory.sync_all())
        .map_err(|e| format!("{}: {e}", parent.display()))?;
    Ok(text.len())
}

/// Read the model checkpoint at `path` and check it against this process. Refused: an unreadable
/// or unparsable file, another schema, an identity that differs in anything but the binary
/// (`semantic_key`, `compiler`, `universe`, `config`), a slot key this program does not have, a kind
/// label that does not parse, or a model or baseline whose digest differs from the file's.
pub(crate) fn read(
    path: &Path,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    a5_mode: OverlapMode,
    attestation: Option<WholeProgramAttestation>,
) -> Result<Loaded, String> {
    let tcx = program.tcx;
    let text = std::fs::read(path).map_err(|e| refused("file", "readable", &e.to_string()))?;
    let checkpoint: ModelCheckpoint = serde_json::from_slice(&text)
        .map_err(|e| refused("format", SCHEMA, &format!("unparsable: {e}")))?;
    if checkpoint.schema != SCHEMA {
        return Err(refused("schema", SCHEMA, &checkpoint.schema));
    }
    let here = baseline_checkpoint::identity(program, slots, a5_mode, attestation)?;
    let found = &checkpoint.identity;
    if found.semantic_key != here.semantic_key {
        return Err(refused(
            "semantic_key",
            &here.semantic_key,
            &found.semantic_key,
        ));
    }
    if found.compiler != here.compiler {
        return Err(refused(
            "compiler",
            &format!("{:?}", here.compiler),
            &format!("{:?}", found.compiler),
        ));
    }
    if found.universe_sha256 != here.universe_sha256 {
        return Err(refused(
            "universe",
            &here.universe_sha256,
            &found.universe_sha256,
        ));
    }
    if found.config != here.config {
        return Err(refused(
            "config",
            &format!("{:?}", here.config),
            &format!("{:?}", found.config),
        ));
    }
    let keys = model_cache::universe(tcx, slots)
        .ok_or_else(|| refused("universe", "renderable", "an unrenderable slot key"))?;
    let decode = |rows: &BTreeMap<String, String>,
                  what: &str|
     -> Result<FxHashMap<SlotRef, SlotKind>, String> {
        rows.iter()
            .map(|(key, kind)| {
                let slot = *keys
                    .get(key)
                    .ok_or_else(|| refused(what, "a slot of this program", key))?;
                let kind = model_cache::parse_kind(kind)
                    .ok_or_else(|| refused(what, "a kind label", kind))?;
                Ok((slot, kind))
            })
            .collect()
    };
    let model = decode(&checkpoint.model, "model")?;
    let baseline = decode(&checkpoint.baseline, "baseline")?;
    let digest = |map: &FxHashMap<SlotRef, SlotKind>, what: &str| {
        model_cache::model_bytes_sha256(tcx, slots, map)
            .ok_or_else(|| refused(what, "renderable", "an unrenderable slot key"))
    };
    let model_sha256 = digest(&model, "model_sha256")?;
    if model_sha256 != checkpoint.model_sha256 {
        return Err(refused(
            "model_sha256",
            &checkpoint.model_sha256,
            &model_sha256,
        ));
    }
    let baseline_sha256 = digest(&baseline, "baseline_sha256")?;
    if baseline_sha256 != checkpoint.baseline_sha256 {
        return Err(refused(
            "baseline_sha256",
            &checkpoint.baseline_sha256,
            &baseline_sha256,
        ));
    }
    Ok(Loaded {
        slots: model.len(),
        cached: model_cache::CachedModel {
            model,
            baseline_model: baseline,
            overlap_receipt: checkpoint.overlap_receipt,
        },
        arg_order: checkpoint.arg_order,
        model_sha256,
        same_exe: found.exe_sha256 == here.exe_sha256,
        incumbent: checkpoint.provenance.incumbent,
    })
}

thread_local! {
    /// The argument-order receipts of the model this decide read from a model checkpoint; `None`
    /// when the model did not come from one (the hoists then come from `model_cache`, as before).
    static LOADED_ARG_ORDER: std::cell::RefCell<Option<ArgOrder>> = const { std::cell::RefCell::new(None) };
}

/// At the start of every decide: no receipts from an earlier decide on this thread.
pub(crate) fn clear_loaded() {
    LOADED_ARG_ORDER.with(|loaded| *loaded.borrow_mut() = None);
}

pub(crate) fn set_loaded(arg_order: ArgOrder) {
    LOADED_ARG_ORDER.with(|loaded| *loaded.borrow_mut() = Some(arg_order));
}

/// The emission's hoist keys when the model came from a model checkpoint (`None` otherwise). An
/// unrecorded family or a row that does not resolve gives the empty set, as `model_cache`'s loader
/// does under the decide's `unwrap_or_default`.
pub(crate) fn loaded_hoists(
    tcx: TyCtxt<'_>,
) -> Option<
    FxHashSet<(
        (u32, u32),
        rustc_span::def_id::LocalDefId,
        rustc_middle::mir::Local,
    )>,
> {
    let arg_order = LOADED_ARG_ORDER.with(|loaded| loaded.borrow().clone())?;
    Some(
        arg_order
            .result()
            .and_then(|rows| hoists(tcx, &rows))
            .unwrap_or_default(),
    )
}

/// A copy of `model_cache::prepared_arg_order_hoists`'s conversion (`model_cache.rs:533–571` at
/// `f1dcb012b`), kept here so that nothing under `src/analyses` changes. W5 pins it against the
/// original: the rows' keys `((lo, hi), caller, lent)`, each call's span re-read from THIS
/// session's MIR at the receipt's location.
pub(crate) fn hoists(
    tcx: TyCtxt<'_>,
    rows: &[ArgOrderRow],
) -> Result<
    FxHashSet<(
        (u32, u32),
        rustc_span::def_id::LocalDefId,
        rustc_middle::mir::Local,
    )>,
    String,
> {
    let by_path: FxHashMap<String, rustc_span::def_id::LocalDefId> = tcx
        .hir_body_owners()
        .filter(|did| tcx.def_kind(*did).is_fn_like())
        .map(|did| (tcx.def_path_str(did.to_def_id()), did))
        .collect();
    rows.iter()
        .map(|row| {
            let caller = *by_path
                .get(&row.function)
                .ok_or_else(|| format!("arg-order receipt names no local fn: {}", row.function))?;
            let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
            let block = body
                .basic_blocks
                .get(rustc_middle::mir::BasicBlock::from_u32(row.call.block))
                .ok_or("arg-order receipt's block is out of range")?;
            match &block.terminator().kind {
                rustc_middle::mir::TerminatorKind::Call { fn_span, .. }
                    if row.call.statement == block.statements.len() =>
                {
                    Ok((
                        (fn_span.lo().0, fn_span.hi().0),
                        caller,
                        rustc_middle::mir::Local::from_u32(row.lent),
                    ))
                }
                _ => Err(format!(
                    "arg-order receipt is not at a call: {}:bb{}[{}]",
                    row.function, row.call.block, row.call.statement
                )),
            }
        })
        .collect()
}

#[cfg(test)]
#[path = "model_checkpoint_tests.rs"]
pub(super) mod model_checkpoint_tests;
