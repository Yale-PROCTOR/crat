//! R1490-2 (main 326, the user's word "승인." on addendum 1489's option (1)): the two-process
//! checkpoint mode. Process 1 (`CRAT_BO_CHECKPOINT_OUT=<path>`) runs the baseline stage of the overlap
//! solve and writes what the precise stage reads from it -- the baseline model by slot key, the round
//! stats the receipt reads, whether a baseline round took an optimize incumbent -- with the identity
//! of everything it was solved from, then ends with the typed `checkpointed` outcome. Process 2
//! (`CRAT_BO_CHECKPOINT_IN=<path>`), a fresh process on the same input, refuses a checkpoint whose
//! identity differs and otherwise resumes at the precise stage. `PreciseReplay` only; refused with a
//! model cache configured. Measurement switches (`execution_guard::checkpoint_paths`).

use std::{
    cell::RefCell,
    collections::BTreeMap,
    io::Write,
    path::{Path, PathBuf},
};

use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{
    SlotKind,
    borrow_verify::{GuardedFallback, RepairMode, RoundStats},
    crate_slots::CrateSlots,
    param_overlap::{OverlapMode, WholeProgramAttestation},
    solver::SlotRef,
};
use crate::utils::rustc::RustProgram;

/// The checkpoint file's schema.
pub(crate) const SCHEMA: &str = "bo-baseline-checkpoint-v1";

/// The head of process 1's typed outcome text (display only: the pass reads [`take_written`]).
pub(crate) const HEAD: &str = "checkpointed (";

/// The head of a refused checkpoint's error.
pub(crate) const REFUSED_HEAD: &str = "checkpoint refused: ";

/// Everything a checkpoint was solved from. Process 2 recomputes it and refuses any difference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Identity {
    /// The model cache's key: the crate name, every local source by content, the analysis code
    /// fingerprint, the toolchain file and the lockfile (`model_cache::fingerprint`).
    pub(crate) semantic_key: String,
    /// The analysis session's compiler invocation and its extern inputs.
    pub(crate) compiler: Compiler,
    /// The sorted slot keys of this program's slot universe, digested.
    pub(crate) universe_sha256: String,
    /// The running binary.
    pub(crate) exe_sha256: String,
    pub(crate) config: Config,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Compiler {
    pub(crate) edition: String,
    pub(crate) target: String,
    pub(crate) crate_types: String,
    /// The session's `--cfg` set (features included), sorted.
    pub(crate) cfgs: Vec<String>,
    /// The `--extern` entries with their locations, sorted.
    pub(crate) externs: Vec<String>,
    /// The `-L` directories, sorted.
    pub(crate) search_paths: Vec<String>,
    /// Every crate file (`.rlib`, `.rmeta`, a shared library) under the `-L` directories by name,
    /// size and content.
    pub(crate) search_files_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Config {
    pub(crate) a5_mode: String,
    pub(crate) attestation: String,
    pub(crate) copy_lend_mode: String,
    pub(crate) repair_mode: String,
    pub(crate) query_timeout_ms: u32,
    pub(crate) fresh_hard_solver: bool,
    /// The construction's other measurement variables, raw (`licensing/matched.rs`).
    pub(crate) matched_probe: Option<String>,
    pub(crate) guard_budget: Option<String>,
    pub(crate) lineage_depth: Option<String>,
}

/// The baseline verification's stats that the precise stage's receipt reads (`repair_keys`,
/// `incumbent_keys`), and two counts for the marks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Stats {
    pub(crate) repair: String,
    pub(crate) guarded_fallback: Option<(String, usize, usize)>,
    pub(crate) incumbent_rounds: usize,
    pub(crate) hard_eval_failed: usize,
    pub(crate) rounds: usize,
    pub(crate) commits_conflict: usize,
}

impl Stats {
    pub(crate) fn of(stats: &RoundStats) -> Self {
        Self {
            repair: format!("{:?}", stats.repair),
            guarded_fallback: stats
                .guarded_fallback
                .as_ref()
                .map(|fallback| (fallback.reason.clone(), fallback.rounds, fallback.commits)),
            incumbent_rounds: stats.incumbent_rounds,
            hard_eval_failed: stats.hard_eval_failed,
            rounds: stats.rounds,
            commits_conflict: stats.commits_conflict,
        }
    }

    fn round_stats(&self) -> Option<RoundStats> {
        let repair = match self.repair.as_str() {
            "Plain" => RepairMode::Plain,
            "Guarded" => RepairMode::Guarded,
            _ => return None,
        };
        Some(RoundStats {
            repair,
            guarded_fallback: self
                .guarded_fallback
                .as_ref()
                .map(|(reason, rounds, commits)| GuardedFallback {
                    reason: reason.clone(),
                    rounds: *rounds,
                    commits: *commits,
                }),
            incumbent_rounds: self.incumbent_rounds,
            hard_eval_failed: self.hard_eval_failed,
            rounds: self.rounds,
            commits_conflict: self.commits_conflict,
            ..RoundStats::default()
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Checkpoint {
    pub(crate) schema: String,
    pub(crate) identity: Identity,
    /// The baseline model: slot key -> kind label.
    pub(crate) model: BTreeMap<String, String>,
    /// `construction::model_digest` of the baseline model.
    pub(crate) model_sha256: String,
    pub(crate) stats: Stats,
    /// Whether any baseline round accepted an optimize incumbent (the solve's cacheable verdict).
    pub(crate) incumbent: bool,
}

/// What process 2 binds in place of the baseline stage.
pub(crate) struct Loaded {
    pub(crate) model: FxHashMap<SlotRef, SlotKind>,
    pub(crate) stats: RoundStats,
    pub(crate) incumbent: bool,
    pub(crate) slots: usize,
}

/// Which side of the mode this process is on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Mode {
    Off,
    Write(PathBuf),
    Read(PathBuf),
}

/// The switches as this solve reads them. Both set, a model cache configured, or a mode other than
/// `PreciseReplay` is refused before anything is solved.
pub(crate) fn mode(overlap: OverlapMode) -> Result<Mode, String> {
    let (out, input) = super::execution_guard::checkpoint_paths();
    let mode = match (out, input) {
        (None, None) => return Ok(Mode::Off),
        (Some(_), Some(_)) => {
            return Err(refused(
                "switches",
                "one of CRAT_BO_CHECKPOINT_OUT / _IN",
                "both",
            ));
        }
        (Some(path), None) => Mode::Write(path),
        (None, Some(path)) => Mode::Read(path),
    };
    if super::model_cache::dir().is_some() {
        return Err(refused("cache", "no CRAT_BO_CACHE_DIR", "set"));
    }
    if overlap != OverlapMode::PreciseReplay {
        return Err(refused(
            "a5_mode",
            OverlapMode::PreciseReplay.label(),
            overlap.label(),
        ));
    }
    Ok(mode)
}

fn refused(field: &str, expected: &str, found: &str) -> String {
    format!("{REFUSED_HEAD}{field} ({expected} != {found})")
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Whether the compiler can load `path` as a crate: the extern inputs, not a checkpoint or a `.d`
/// file beside them.
fn is_crate_file(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|extension| extension.to_str()),
        Some("rlib" | "rmeta" | "so" | "dylib" | "dll")
    )
}

/// The digest of every crate file under `dirs`: by directory, then file name, its size and content.
fn files_digest(dirs: &[PathBuf]) -> Result<String, String> {
    let mut hasher = Sha256::new();
    for dir in dirs {
        let Ok(entries) = std::fs::read_dir(dir) else {
            hasher.update(format!("{}\tabsent\n", dir.display()).as_bytes());
            continue;
        };
        let mut files = entries
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| path.is_file() && is_crate_file(path))
            .collect::<Vec<_>>();
        files.sort();
        for file in files {
            let bytes = std::fs::read(&file).map_err(|e| format!("{}: {e}", file.display()))?;
            hasher.update(
                format!(
                    "{}\t{}\t{}\n",
                    file.display(),
                    bytes.len(),
                    sha256_hex(&bytes)
                )
                .as_bytes(),
            );
        }
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn compiler(program: &RustProgram<'_>) -> Result<Compiler, String> {
    let sess = program.tcx.sess;
    let mut cfgs = sess
        .psess
        .config
        .iter()
        .map(|(name, value)| match value {
            Some(value) => format!("{name}={value:?}"),
            None => name.to_string(),
        })
        .collect::<Vec<_>>();
    cfgs.sort();
    let mut externs = sess
        .opts
        .externs
        .iter()
        .map(|(name, entry)| format!("{name}={:?}", entry.location))
        .collect::<Vec<_>>();
    externs.sort();
    let mut dirs = sess
        .opts
        .search_paths
        .iter()
        .map(|path| path.dir.clone())
        .collect::<Vec<_>>();
    dirs.sort();
    dirs.dedup();
    Ok(Compiler {
        edition: format!("{:?}", sess.opts.edition),
        target: format!("{:?}", sess.opts.target_triple),
        crate_types: format!("{:?}", sess.opts.crate_types),
        cfgs,
        externs,
        search_paths: dirs.iter().map(|dir| dir.display().to_string()).collect(),
        search_files_sha256: files_digest(&dirs)?,
    })
}

fn universe_sha256(program: &RustProgram<'_>, slots: &CrateSlots) -> Result<String, String> {
    let universe = super::model_cache::universe(program.tcx, slots)
        .ok_or("the slot universe has an unrenderable or duplicate key")?;
    let mut hasher = Sha256::new();
    for key in universe.keys() {
        hasher.update(key.as_bytes());
        hasher.update(b"\n");
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn exe_sha256() -> Result<String, String> {
    #[cfg(test)]
    if let Some(sha) = hooks::exe_sha256() {
        return Ok(sha);
    }
    // The loaded image (`/proc/self/exe`, not the path it was started from, which may have been
    // replaced since), read once per process: the image does not change under it.
    static EXE: std::sync::OnceLock<Result<String, String>> = std::sync::OnceLock::new();
    EXE.get_or_init(|| {
        let exe = if cfg!(target_os = "linux") {
            PathBuf::from("/proc/self/exe")
        } else {
            std::env::current_exe().map_err(|e| format!("current_exe: {e}"))?
        };
        let bytes = std::fs::read(&exe).map_err(|e| format!("{}: {e}", exe.display()))?;
        Ok(sha256_hex(&bytes))
    })
    .clone()
}

fn config(overlap: OverlapMode, attestation: Option<WholeProgramAttestation>) -> Config {
    let raw = |name: &str| std::env::var(name).ok();
    Config {
        a5_mode: overlap.label().to_owned(),
        attestation: format!("{attestation:?}"),
        copy_lend_mode: format!("{:?}", super::construction::CopyLendMode::current()),
        repair_mode: format!("{:?}", RepairMode::current()),
        query_timeout_ms: super::execution_guard::query_timeout_ms(),
        fresh_hard_solver: super::execution_guard::fresh_hard_solver(),
        matched_probe: raw("CRAT_BO_MATCHED_PROBE"),
        guard_budget: raw("CRAT_BO_GUARD_BUDGET"),
        lineage_depth: raw("CRAT_BO_LINEAGE_DEPTH"),
    }
}

/// This process's identity for `program`. The solve computes it once at its start (before the
/// baseline stage), so a checkpoint names the inputs its solve began from.
pub(crate) fn identity(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    overlap: OverlapMode,
    attestation: Option<WholeProgramAttestation>,
) -> Result<Identity, String> {
    Ok(Identity {
        semantic_key: super::model_cache::fingerprint(program, overlap, attestation),
        compiler: compiler(program)?,
        universe_sha256: universe_sha256(program, slots)?,
        exe_sha256: exe_sha256()?,
        config: config(overlap, attestation),
    })
}

/// The first identity field in which `found` differs from `expected`, as a refusal.
fn identity_difference(expected: &Identity, found: &Identity) -> Option<String> {
    let field = |name: &str, expected: &dyn std::fmt::Debug, found: &dyn std::fmt::Debug| {
        Some(refused(
            name,
            &format!("{expected:?}"),
            &format!("{found:?}"),
        ))
    };
    if found.semantic_key != expected.semantic_key {
        return field("semantic_key", &expected.semantic_key, &found.semantic_key);
    }
    if found.compiler != expected.compiler {
        return field("compiler", &expected.compiler, &found.compiler);
    }
    if found.universe_sha256 != expected.universe_sha256 {
        return field(
            "universe",
            &expected.universe_sha256,
            &found.universe_sha256,
        );
    }
    if found.exe_sha256 != expected.exe_sha256 {
        return field("exe", &expected.exe_sha256, &found.exe_sha256);
    }
    if found.config != expected.config {
        return field("config", &expected.config, &found.config);
    }
    None
}

/// Process 1: write the checkpoint with the identity the solve started from (`start`), after
/// computing it again: an input that changed during the baseline solve is refused and nothing is
/// published. Atomic: a uniquely named temporary file beside the destination, created exclusively,
/// synced, renamed over the destination, then the directory synced.
#[allow(clippy::too_many_arguments)]
pub(crate) fn write(
    path: &Path,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    overlap: OverlapMode,
    attestation: Option<WholeProgramAttestation>,
    start: &Identity,
    model: &FxHashMap<SlotRef, SlotKind>,
    model_sha256: String,
    stats: &RoundStats,
) -> Result<usize, String> {
    let now = identity(program, slots, overlap, attestation)?;
    if let Some(difference) = identity_difference(start, &now) {
        return Err(difference);
    }
    let rendered = super::model_cache::model_map(program.tcx, slots, model)
        .ok_or("the baseline model has an unrenderable slot key")?;
    let checkpoint = Checkpoint {
        schema: SCHEMA.to_owned(),
        identity: now,
        model: rendered,
        model_sha256,
        stats: Stats::of(stats),
        incumbent: stats.incumbent_rounds > 0,
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

/// Process 2: read and check the checkpoint against this process's identity (`here`, computed at
/// the solve's start); every difference is refused.
pub(crate) fn read(
    path: &Path,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    here: &Identity,
    digest: impl Fn(&FxHashMap<SlotRef, SlotKind>) -> String,
) -> Result<Loaded, String> {
    let text = std::fs::read(path).map_err(|e| refused("file", "readable", &e.to_string()))?;
    let checkpoint: Checkpoint = serde_json::from_slice(&text)
        .map_err(|e| refused("format", SCHEMA, &format!("unparsable: {e}")))?;
    if checkpoint.schema != SCHEMA {
        return Err(refused("schema", SCHEMA, &checkpoint.schema));
    }
    if let Some(difference) = identity_difference(here, &checkpoint.identity) {
        return Err(difference);
    }
    let universe = super::model_cache::universe(program.tcx, slots)
        .ok_or_else(|| refused("universe", "renderable", "unrenderable"))?;
    if universe.len() != checkpoint.model.len() {
        return Err(refused(
            "slots",
            &universe.len().to_string(),
            &checkpoint.model.len().to_string(),
        ));
    }
    let mut model = FxHashMap::default();
    for (key, label) in &checkpoint.model {
        let slot = universe
            .get(key)
            .ok_or_else(|| refused("slot", "a key of this universe", key))?;
        let kind = super::model_cache::parse_kind(label)
            .ok_or_else(|| refused("kind", "ref|raw|owning", label))?;
        model.insert(*slot, kind);
    }
    let found = digest(&model);
    if found != checkpoint.model_sha256 {
        return Err(refused("model_sha256", &checkpoint.model_sha256, &found));
    }
    let stats = checkpoint
        .stats
        .round_stats()
        .ok_or_else(|| refused("stats", "Plain|Guarded", &checkpoint.stats.repair))?;
    Ok(Loaded {
        slots: model.len(),
        model,
        stats,
        incumbent: checkpoint.incumbent,
    })
}

/// Process 2: one process counts optimize incumbents over the whole solve, the baseline's included,
/// for the cacheable verdict (`execution_guard::solve_then_cacheable`); the resumed solve counts the
/// checkpoint's baseline as one.
pub(crate) fn seed_incumbent(incumbent: bool) {
    if incumbent {
        super::execution_guard::note_incumbent_accepted();
    }
}

thread_local! {
    /// The typed outcome the decide reads when the solve returned no model: process 1's
    /// `checkpointed (…)` or a refusal's text.
    static OUTCOME: RefCell<Option<String>> = const { RefCell::new(None) };
}

pub(crate) fn record_outcome(text: String) {
    OUTCOME.with(|outcome| *outcome.borrow_mut() = Some(text));
}

/// The recorded outcome, taken.
pub(crate) fn take_outcome() -> Option<String> {
    OUTCOME.with(|outcome| outcome.borrow_mut().take())
}

/// Process 1's outcome text.
pub(crate) fn checkpointed(path: &Path, slots: usize, bytes: usize) -> String {
    format!("{HEAD}{}, {slots} slots, {bytes} bytes)", path.display())
}

/// Process 1's published checkpoint, process-wide (the pass runs on another thread than the
/// solve): set only after the checkpoint was written and synced, so the pass never reads an error's
/// text to decide that a checkpoint exists.
static WRITTEN: std::sync::Mutex<Option<String>> = std::sync::Mutex::new(None);

pub(crate) fn note_written(text: String) {
    *WRITTEN
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(text);
}

/// The published checkpoint's outcome text, taken.
pub(crate) fn take_written() -> Option<String> {
    WRITTEN
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .take()
}

#[cfg(test)]
pub(crate) mod hooks {
    thread_local! {
        static EXE: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
    }
    pub(super) fn exe_sha256() -> Option<String> {
        EXE.with(|exe| exe.borrow().clone())
    }
    /// Run `f` with the binary's identity read as `sha`.
    pub(crate) fn with_exe_sha256<T>(sha: &str, f: impl FnOnce() -> T) -> T {
        struct Reset(Option<String>);
        impl Drop for Reset {
            fn drop(&mut self) {
                EXE.with(|exe| *exe.borrow_mut() = self.0.take());
            }
        }
        let _reset = Reset(EXE.with(|exe| exe.borrow_mut().replace(sha.to_owned())));
        f()
    }
}

#[cfg(test)]
#[path = "baseline_checkpoint_tests.rs"]
mod tests;
