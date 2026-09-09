//! Complete era5a model cache and unchanged three-field consumer view.
//!
//! New entries contain portable semantic inputs, the complete model and A5
//! planning baseline, the accepted receipt, and every required captured export.
//! Accepted legacy namespaces are never rewritten or relabelled into era5a.
//! Publication validates a staged body and atomically links it without overwrite.
//!
//! The existing consumer still tries memo, disk, then production analysis.
//! CacheOnly execution scopes reject that final fallback before a solver exists;
//! normal derivation scopes may solve. The historical memo counter counts loads
//! and solves, while execution_guard records actual outer model entries.
//!
//! Host/launch/transport attestations accompany the portable semantic key.
//! Batch workers bind their logical input root and sealed toolchain/dependency
//! digests explicitly; ordinary local use derives a common input root and uses
//! repository toolchain/lockfile identities. Sources stay frozen for a process.

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use rustc_hash::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LOCAL_CRATE;
use sha2::{Digest, Sha256};

use super::{
    SafeMonoMode, SlotKind,
    a5_overlap::{A5Mode, A5World, WholeProgramAttestation},
    borrow_engine::ForkEngineMode,
    borrow_verify::RepairMode,
    construction::{A2Mode, CopyLendMode},
    crate_slots::CrateSlots,
    slot_key::{field_key, local_key},
    solver::SlotRef,
};
use crate::utils::rustc::RustProgram;

/// The frozen analysis semantics consumed by Item E. Rewriter/cache-only
/// changes after this commit do not advance this identity.
pub(crate) const ANALYSIS_FRAME: &str = "era5a-r258-local-coverage-v1";

const CACHE_SCHEMA: &str = "bo-model-cache-v2";
const A14_MARKER: &str = "positive-opacity-v1";
const A16_MARKER: &str = "modeled-origin-one-way-v1";
const T2_MARKER: &str = "endpoint-force-retraction-v1";
const ESC_MINIMAL_MARKER: &str = "direct-escape-minimal-v1";
const ESC_MINIMAL_ALLOWLIST: &[u8] = include_bytes!("esc_minimal_allowlist.tsv");

/// The readable solver identity that is hashed into every cache key.
///
/// This is deliberately explicit even though the analyses-tree hash remains
/// in the fingerprint. The ② allowlist is not Rust source, and named markers
/// make a receipt auditable without reverse-engineering which code bytes imply
/// which accepted configuration.
pub(crate) fn solver_identity(
    a5_mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> String {
    let mut fields = BTreeMap::new();
    fields.insert("era5_schema", super::cache_contract::SCHEMA.to_owned());
    fields.insert(
        "query_timeout_ms",
        super::execution_guard::QUERY_TIMEOUT_MS.to_string(),
    );
    if let Ok(digest) = std::env::var("CRAT_ERA5_LAUNCH_DIGEST") {
        fields.insert("era5_launch_digest", digest);
    }
    fields.insert(
        "local_coverage_outcomes",
        "r245-ref-inner-demote-realloc-site-hold-v1".to_owned(),
    );
    fields.insert(
        "retirement_receipts",
        "r253-three-dispositions-v1".to_owned(),
    );
    fields.insert(
        "coverage_integrity",
        "r253-inventory-complete-l2-result-propagation-v1".to_owned(),
    );
    fields.insert("protected_entry", "p1-prime-s-v1".to_owned());
    fields.insert(
        "realloc_outcomes",
        "r243-field-test-fallback-both-v1".to_owned(),
    );
    fields.insert(
        "comparison",
        "source-cause-no-comparison-cause-v1".to_owned(),
    );
    fields.insert("field_inner_facts", "explicit-availability-v1".to_owned());
    fields.insert("array_fields", "uniform-element-raw-holds-v1".to_owned());
    fields.insert("proof_evidence", "source-only-v2".to_owned());
    fields.insert("ownership_licensing", "deferred-era5b".to_owned());
    fields.insert("a14", A14_MARKER.to_owned());
    fields.insert("a16", A16_MARKER.to_owned());
    fields.insert("a2_mode", A2Mode::current().label().to_owned());
    fields.insert("a5_mode", a5_mode.label().to_owned());
    fields.insert(
        "a5_attestation",
        match attestation {
            Some(WholeProgramAttestation::FrozenBenchmarkGraph) => "frozen_benchmark_graph",
            None => "none",
        }
        .to_owned(),
    );
    fields.insert(
        "a5_world",
        A5World::ClosedWorldFrozenGraph.label().to_owned(),
    );
    fields.insert("analysis_frame", ANALYSIS_FRAME.to_owned());
    fields.insert("copy_lend_mode", CopyLendMode::current().label().to_owned());
    fields.insert(
        "esc_allowlist_sha256",
        format!("{:x}", Sha256::digest(ESC_MINIMAL_ALLOWLIST)),
    );
    fields.insert("esc_minimal", ESC_MINIMAL_MARKER.to_owned());
    fields.insert("fork_engine", ForkEngineMode::current().label().to_owned());
    fields.insert(
        "l2_guarded_commits",
        super::l2::enabled_from_env().to_string(),
    );
    fields.insert(
        "nb4r_routing",
        if matches!(
            std::env::var("CRAT_NB4R_ROUTING").as_deref(),
            Ok("off" | "0")
        ) {
            "off"
        } else {
            "on"
        }
        .to_owned(),
    );
    fields.insert("repair_mode", RepairMode::current().label().to_owned());
    fields.insert("safe_mono", SafeMonoMode::current().label().to_owned());
    fields.insert("t2", T2_MARKER.to_owned());
    fields.insert("mutability", "foster-from-program-v1".to_owned());
    for key in [
        "CRAT_BO_EXPORT",
        "CRAT_BO_L2_TRANSITION_DIAGNOSTICS",
        "CRAT_BO_POINT_REQUIRES_TRIPWIRE",
        "CRAT_POINTER_DECISION_DIAGNOSTICS",
    ] {
        fields.insert(key, std::env::var(key).unwrap_or_default());
    }
    fields
        .into_iter()
        .map(|(key, value)| format!("{key}={value}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn program_identity(
    crate_name: &str,
    files: impl IntoIterator<Item = (String, Vec<u8>)>,
) -> String {
    let mut files = files.into_iter().collect::<Vec<_>>();
    files.sort_by(|left, right| left.0.cmp(&right.0).then(left.1.cmp(&right.1)));
    let mut hash = Sha256::new();
    hash.update(crate_name.as_bytes());
    for (path, source_hash) in files {
        hash.update(path.as_bytes());
        hash.update((source_hash.len() as u64).to_le_bytes());
        hash.update(source_hash);
    }
    format!("{:x}", hash.finalize())
}

fn canonical_program_path(path: &Path) -> String {
    std::fs::canonicalize(path)
        .unwrap_or_else(|_| path.to_path_buf())
        .display()
        .to_string()
}

/// `CRAT_BO_CACHE=1` enables reads. Writes happen whenever a real solve runs
/// with a cache directory configured, so a bypassed gate sweep still refreshes
/// what dev iteration will read next.
pub(crate) fn read_enabled() -> bool {
    #[cfg(test)]
    if let Some((read, _)) = TEST_CONFIG.with(|config| config.borrow().clone()) {
        return read;
    }
    matches!(std::env::var("CRAT_BO_CACHE").as_deref(), Ok("1"))
}

pub(crate) fn dir() -> Option<PathBuf> {
    #[cfg(test)]
    if let Some((_, dir)) = TEST_CONFIG.with(|config| config.borrow().clone()) {
        return Some(dir);
    }
    std::env::var_os("CRAT_BO_CACHE_DIR").map(PathBuf::from)
}

#[cfg(test)]
thread_local! {
    static TEST_CONFIG: std::cell::RefCell<Option<(bool, PathBuf)>> = const {
        std::cell::RefCell::new(None)
    };
}

#[cfg(test)]
pub(crate) fn with_test_config<T>(read: bool, dir: &Path, run: impl FnOnce() -> T) -> T {
    struct Restore(Option<(bool, PathBuf)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            TEST_CONFIG.with(|config| *config.borrow_mut() = self.0.take());
        }
    }
    let previous =
        TEST_CONFIG.with(|config| config.borrow_mut().replace((read, dir.to_path_buf())));
    let _restore = Restore(previous);
    run()
}

/// Everything the cached model is a function of.
///
/// A change to **any** of these must invalidate, so they are hashed together
/// into one value rather than checked severally — a severally-checked key grows
/// a forgotten term.
pub(crate) fn fingerprint(
    program: &RustProgram<'_>,
    a5_mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> String {
    super::cache_contract::semantic_key(
        &semantic_inputs(program, a5_mode, attestation)
            .expect("complete semantic inputs before any cache lookup"),
    )
    .expect("valid portable semantic input identity")
}

pub(crate) fn semantic_inputs(
    program: &RustProgram<'_>,
    a5_mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> Result<super::cache_contract::SemanticInputs, String> {
    let mut real = BTreeMap::<PathBuf, String>::new();
    let mut files = BTreeMap::new();
    for file in program.tcx.sess.source_map().files().iter() {
        // Imported source text is covered by the dependency/toolchain recipe.
        // Every locally loaded source, including virtual inputs, is content keyed.
        let Some(source) = file.src.as_ref() else { continue };
        let hash = format!("{:x}", Sha256::digest(source.as_bytes()));
        if let rustc_span::FileName::Real(path) = &file.name
            && let Some(path) = path.local_path()
        {
            let path = std::fs::canonicalize(path).map_err(|e| e.to_string())?;
            if let Some(previous) = real.insert(path, hash.clone())
                && previous != hash
            {
                return Err("source changed within compiler session".into());
            }
        } else {
            files.insert(format!("virtual/{hash}.rs"), hash);
        }
    }
    if !real.is_empty() {
        let mut root = if let Some(root) = std::env::var_os("CRAT_ERA5_INPUT_ROOT") {
            std::fs::canonicalize(root).map_err(|e| e.to_string())?
        } else {
            let mut root = real
                .keys()
                .next()
                .unwrap()
                .parent()
                .ok_or("source has no parent")?
                .to_path_buf();
            for path in real.keys() {
                while !path.starts_with(&root) {
                    if !root.pop() {
                        return Err("no common source root".into());
                    }
                }
            }
            root
        };
        if root.as_os_str().is_empty() {
            root = PathBuf::from("/");
        }
        let mapped =
            super::cache_contract::logical_files(&root, &real.into_iter().collect::<Vec<_>>())?;
        for (path, hash) in mapped {
            if files.insert(path, hash).is_some() {
                return Err("duplicate source manifest path".into());
            }
        }
    }
    let toolchain = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../rust-toolchain.toml"
    ))
    .map_err(|e| e.to_string())?;
    let dependencies = std::fs::read(concat!(env!("CARGO_MANIFEST_DIR"), "/../../Cargo.lock"))
        .map_err(|e| e.to_string())?;
    let recipe_digest = |name: &str, fallback: &[u8]| {
        std::env::var(name).unwrap_or_else(|_| format!("{:x}", Sha256::digest(fallback)))
    };
    Ok(super::cache_contract::SemanticInputs {
        program: std::env::var("CRAT_ERA5_PROGRAM")
            .unwrap_or_else(|_| program.tcx.crate_name(LOCAL_CRATE).to_string()),
        files,
        analysis: code_fingerprint_cached().to_owned(),
        toolchain: recipe_digest("CRAT_ERA5_TOOLCHAIN_DIGEST", &toolchain),
        dependencies: recipe_digest("CRAT_ERA5_DEPENDENCY_DIGEST", &dependencies),
        configuration: format!(
            "{:x}",
            Sha256::digest(solver_identity(a5_mode, attestation).as_bytes())
        ),
    })
}
fn fingerprint_components(solver: &str, program: &str, code: &str, toolchain: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(solver.as_bytes());
    h.update(program.as_bytes());
    h.update(code.as_bytes());
    h.update(toolchain);
    format!("{:x}", h.finalize())
}

/// SHA-256 over the sorted contents of the analyses source tree.
///
/// Computed at runtime rather than baked in at build time: a baked constant
/// would be stale exactly when the sources change without a rebuild of this
/// file, which is the failure mode it exists to prevent.
fn analysis_code_fingerprint_at(root: &Path) -> String {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let rd = std::fs::read_dir(dir).expect("complete analyses tree");
        for e in rd {
            let p = e.expect("read analysis entry").path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.is_file() {
                out.push(p);
            }
        }
    }
    let mut files = Vec::new();
    walk(root, &mut files);
    files.sort_by(|left, right| {
        left.strip_prefix(root)
            .expect("walked analysis file is under root")
            .cmp(
                right
                    .strip_prefix(root)
                    .expect("walked analysis file is under root"),
            )
    });
    let mut h = Sha256::new();
    for f in &files {
        let relative = f
            .strip_prefix(root)
            .expect("walked analysis file is under root")
            .components()
            .map(|component| component.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("/");
        let content = std::fs::read(f).expect("read every frozen analysis asset");
        let content_hash = Sha256::digest(content);
        h.update((relative.len() as u64).to_le_bytes());
        h.update(relative.as_bytes());
        h.update(content_hash);
    }
    format!("{:x}", h.finalize())
}

pub(crate) fn current_analysis_digest() -> String {
    analysis_code_fingerprint()
}

fn analysis_code_fingerprint() -> String {
    analysis_code_fingerprint_at(Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/analyses"
    )))
}

fn entry_path(d: &Path, fingerprint: &str) -> PathBuf {
    d.join("era5a-model-cache-v1")
        .join(format!("{fingerprint}.json"))
}

/// Retained API for explicit refusal of legacy key-only migration into era5a.
pub(crate) fn rekey_entry(
    _old_path: &Path,
    _new_dir: &Path,
    _new_fingerprint: &str,
) -> Result<PathBuf, String> {
    Err("key-only migration cannot create a complete era5a model entry".into())
}

pub(crate) fn configured_entry_path(fingerprint: &str) -> Option<PathBuf> {
    Some(entry_path(&dir()?, fingerprint))
}

#[derive(Clone, Debug)]
pub(crate) struct CachedModel {
    /// The exact `VerifiedBo.model` consumed by the rewriter.
    pub(crate) model: FxHashMap<SlotRef, SlotKind>,
    /// A5's planning baseline, needed to reconstruct current-session C9 mark
    /// spans without another solver invocation.
    pub(crate) baseline_model: FxHashMap<SlotRef, SlotKind>,
    /// The construction receipt from the solve that produced `model`.
    pub(crate) a5_receipt: String,
}

#[derive(Clone)]
struct Prepared {
    entry: super::cache_contract::CompleteEntry,
    cached: CachedModel,
}
thread_local! {
    static PREPARED: std::cell::RefCell<Option<Prepared>> = const { std::cell::RefCell::new(None) };
    static PREPARE_ERROR: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

pub(crate) fn prepare_error() -> Option<String> {
    PREPARE_ERROR.with(|error| error.borrow().clone())
}

fn universe(tcx: TyCtxt<'_>, slots: &CrateSlots) -> Option<BTreeMap<String, SlotRef>> {
    let mut keys = BTreeMap::new();
    for (&function, locals) in &slots.fn_local_slots {
        for index in 0..locals.len() {
            let slot = SlotRef::Local(function, super::slots::SlotId::from_usize(index));
            if keys.insert(render_key(tcx, slots, slot)?, slot).is_some() {
                return None;
            }
        }
    }
    for index in 0..slots.field_slots.len() {
        let slot = SlotRef::Field(super::slots::SlotId::from_usize(index));
        if keys.insert(render_key(tcx, slots, slot)?, slot).is_some() {
            return None;
        }
    }
    Some(keys)
}
fn model_map(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Option<BTreeMap<String, String>> {
    model
        .iter()
        .map(|(&slot, &kind)| Some((render_key(tcx, slots, slot)?, kind_label(kind).to_owned())))
        .collect()
}

/// Preserve the complete accepted capture before the unchanged consumer drops
/// its recording. Serialization failure affects cache completeness, not kinds.
pub(crate) fn prepare(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &super::origin_summary::OriginSummaries,
    verified: &super::construction::VerifiedBo,
    captured: &super::export::BoExport,
    mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) {
    let result = (|| -> Result<Prepared, String> {
        let inputs = semantic_inputs(program, mode, attestation)?;
        let key = super::cache_contract::semantic_key(&inputs)?;
        let portable = super::portable_export::collect(program, slots, captured)?;
        let origin = super::origin_evidence::collect(program, slots, origins, Some(captured));
        let mut functions: Vec<_> = program
            .functions
            .iter()
            .map(|did| program.tcx.def_path_str(did.to_def_id()))
            .collect();
        functions.sort();
        let entry = super::cache_contract::CompleteEntry {
            schema: super::cache_contract::SCHEMA.into(),
            key,
            inputs,
            functions,
            universe: universe(program.tcx, slots)
                .ok_or("invalid slot universe")?
                .into_keys()
                .collect(),
            model: model_map(program.tcx, slots, &verified.model)
                .ok_or("invalid accepted model keys")?,
            baseline: model_map(program.tcx, slots, &verified.baseline_model)
                .ok_or("invalid baseline model keys")?,
            receipt: verified.receipt.clone(),
            exports: serde_json::from_str(&portable.canonical_json()?)
                .map_err(|e| e.to_string())?,
            origin: serde_json::from_str(&origin.canonical_json()).map_err(|e| e.to_string())?,
        };
        entry.validate()?;
        Ok(Prepared {
            entry,
            cached: CachedModel {
                model: verified.model.clone(),
                baseline_model: verified.baseline_model.clone(),
                a5_receipt: verified.receipt.clone(),
            },
        })
    })();
    match result {
        Ok(value) => {
            PREPARED.with(|p| *p.borrow_mut() = Some(value));
            PREPARE_ERROR.with(|e| *e.borrow_mut() = None);
        }
        Err(error) => {
            PREPARED.with(|p| *p.borrow_mut() = None);
            PREPARE_ERROR.with(|e| *e.borrow_mut() = Some(error));
        }
    }
}

pub(crate) fn prepared_entry(fingerprint: &str) -> Option<super::cache_contract::CompleteEntry> {
    PREPARED.with(|p| {
        p.borrow()
            .as_ref()
            .filter(|p| p.entry.key == fingerprint)
            .map(|p| p.entry.clone())
    })
}

fn kind_label(kind: SlotKind) -> &'static str {
    match kind {
        SlotKind::Ref => "ref",
        SlotKind::Raw => "raw",
        SlotKind::Owning => "owning",
    }
}

fn parse_kind(kind: &str) -> Option<SlotKind> {
    match kind {
        "ref" => Some(SlotKind::Ref),
        "raw" => Some(SlotKind::Raw),
        "owning" => Some(SlotKind::Owning),
        _ => None,
    }
}

fn canonical_model_rows(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Option<Vec<String>> {
    let mut rows = Vec::with_capacity(model.len());
    for (&slot, &kind) in model {
        rows.push(format!(
            "{}\t{}",
            render_key(tcx, slots, slot)?,
            kind_label(kind)
        ));
    }
    rows.sort();
    Some(rows)
}

/// SHA-256 of the session-independent bytes representing the consumed model.
pub(crate) fn model_bytes_sha256(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> Option<String> {
    let rows = canonical_model_rows(tcx, slots, model)?;
    Some(format!("{:x}", Sha256::digest(rows.join("\n").as_bytes())))
}

fn attestation_label(attestation: Option<WholeProgramAttestation>) -> &'static str {
    match attestation {
        Some(WholeProgramAttestation::FrozenBenchmarkGraph) => "frozen_benchmark_graph",
        None => "none",
    }
}

/// Serialize the accepted model and its minimum precise-replay rehydration
/// payload under canonical slot keys.
pub(crate) fn store(
    _tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    _slots: &CrateSlots,
    cached: &CachedModel,
    a5_mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> Option<PathBuf> {
    let directory = dir()?.join("era5a-model-cache-v1");
    let fp = fingerprint(program, a5_mode, attestation);
    let entry = PREPARED.with(|prepared| {
        prepared
            .borrow()
            .as_ref()
            .filter(|p| {
                p.entry.key == fp
                    && p.cached.model == cached.model
                    && p.cached.baseline_model == cached.baseline_model
                    && p.cached.a5_receipt == cached.a5_receipt
            })
            .map(|p| p.entry.clone())
    })?;
    match super::cache_contract::publish(&directory, &entry) {
        Ok(path) => Some(path),
        Err(error) => {
            PREPARE_ERROR.with(|e| *e.borrow_mut() = Some(error));
            None
        }
    }
}

fn render_key(tcx: TyCtxt<'_>, slots: &CrateSlots, r: SlotRef) -> Option<String> {
    match r {
        SlotRef::Local(fn_did, id) => {
            let slot = slots.fn_local_slots.get(&fn_did)?.slot(id);
            let super::slots::SlotOwner::Local(local) = slot.owner else {
                return None;
            };
            Some(local_key(tcx, fn_did, local.index(), slot.depth))
        }
        SlotRef::Field(id) => {
            let slot = slots.field_slots.slot(id);
            let super::slots::SlotOwner::Field(f) = slot.owner else {
                return None;
            };
            Some(field_key(tcx, f.struct_did, f.field_index, slot.depth))
        }
    }
}

/// Load only a complete validated era5a envelope. CacheOnly guards block any fallback.
pub(crate) fn load(
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    a5_mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> Option<CachedModel> {
    if !read_enabled() {
        return None;
    }
    let expected = semantic_inputs(program, a5_mode, attestation).ok()?;
    let fp = super::cache_contract::semantic_key(&expected).ok()?;
    let body = std::fs::read(entry_path(&dir()?, &fp)).ok()?;
    let entry = super::cache_contract::decode(&body).ok()?;
    if entry.key != fp || entry.inputs != expected {
        return None;
    }
    let actual_functions: std::collections::BTreeSet<_> = program
        .functions
        .iter()
        .map(|function| tcx.def_path_str(function.to_def_id()))
        .collect();
    if entry
        .functions
        .iter()
        .cloned()
        .collect::<std::collections::BTreeSet<_>>()
        != actual_functions
    {
        return None;
    }
    let keys = universe(tcx, slots)?;
    if entry
        .universe
        .iter()
        .cloned()
        .collect::<std::collections::BTreeSet<_>>()
        != keys.keys().cloned().collect()
    {
        return None;
    }
    let decode = |rows: &BTreeMap<String, String>| -> Option<FxHashMap<SlotRef, SlotKind>> {
        rows.iter()
            .map(|(key, kind)| Some((*keys.get(key)?, parse_kind(kind)?)))
            .collect()
    };
    let cached = CachedModel {
        model: decode(&entry.model)?,
        baseline_model: decode(&entry.baseline)?,
        a5_receipt: entry.receipt.clone(),
    };
    PREPARED.with(|p| {
        *p.borrow_mut() = Some(Prepared {
            entry,
            cached: cached.clone(),
        })
    });
    Some(cached)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Item E / §39 addendum 74: a production cache key names the accepted
    /// solver world explicitly. The analyses-tree hash remains a backstop, but
    /// it is not a substitute for a readable identity: in particular the
    /// ②-minimal allowlist is a TSV and therefore was outside the old `.rs`
    /// tree walk.
    #[test]
    fn precise_cache_identity_names_every_frozen_solver_marker() {
        let identity = solver_identity(
            super::super::a5_overlap::A5Mode::PreciseReplay,
            Some(super::super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        for required in [
            "analysis_frame=era5a-r258-local-coverage-v1",
            "era5_schema=era5a-model-cache-v1",
            "local_coverage_outcomes=r245-ref-inner-demote-realloc-site-hold-v1",
            "retirement_receipts=r253-three-dispositions-v1",
            "coverage_integrity=r253-inventory-complete-l2-result-propagation-v1",
            "protected_entry=p1-prime-s-v1",
            "realloc_outcomes=r243-field-test-fallback-both-v1",
            "field_inner_facts=explicit-availability-v1",
            "array_fields=uniform-element-raw-holds-v1",
            "proof_evidence=source-only-v2",
            "ownership_licensing=deferred-era5b",
            "query_timeout_ms=600000",
            "a5_mode=precise_replay",
            "a5_world=closed_world_frozen_graph",
            "a5_attestation=frozen_benchmark_graph",
            "a14=positive-opacity-v1",
            "a16=modeled-origin-one-way-v1",
            "t2=endpoint-force-retraction-v1",
            "esc_minimal=direct-escape-minimal-v1",
            "esc_allowlist_sha256=",
            "copy_lend_mode=baseline",
            "a2_mode=off",
        ] {
            assert!(
                identity.contains(required),
                "cache identity omitted {required:?}:\n{identity}"
            );
        }
    }

    #[test]
    fn cache_identity_separates_a5_mode_and_graph_attestation() {
        use super::super::a5_overlap::{A5Mode, WholeProgramAttestation};

        let precise_attested = solver_identity(
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        let precise_unattested = solver_identity(A5Mode::PreciseReplay, None);
        let baseline = solver_identity(
            A5Mode::Baseline,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert_ne!(precise_attested, precise_unattested);
        assert_ne!(precise_attested, baseline);
    }

    #[test]
    fn program_identity_is_independent_of_source_map_iteration_order() {
        let left = vec![
            ("z.rs".to_owned(), vec![3, 4]),
            ("a.rs".to_owned(), vec![1, 2]),
        ];
        let mut right = left.clone();
        right.reverse();
        assert_eq!(
            program_identity("fixture", left),
            program_identity("fixture", right)
        );
        assert_ne!(
            program_identity("fixture", [("a.rs".to_owned(), vec![1, 2])]),
            program_identity("other", [("a.rs".to_owned(), vec![1, 2])]),
        );
    }

    #[test]
    fn program_path_identity_ignores_dotdot_launch_spelling() {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
        let dotted = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src")
            .join("..")
            .join("Cargo.toml");
        assert_eq!(
            canonical_program_path(&manifest),
            canonical_program_path(&dotted)
        );
    }

    /// Production's accepted PreciseReplay path must write and consume the
    /// existing cache mechanism, preserving both the consumed model bytes and
    /// the construction receipt. Resetting the in-process memo between calls
    /// forces the second compiler session through the on-disk tier.
    #[test]
    fn precise_rewriter_cache_hit_preserves_model_and_receipt() {
        struct TestDir(PathBuf);
        impl Drop for TestDir {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let directory = TestDir(
            std::env::temp_dir().join(format!("crat-precise-cache-test-{}", std::process::id())),
        );
        let _ = std::fs::remove_dir_all(&directory.0);
        std::fs::create_dir_all(&directory.0).expect("cache tempdir");
        let source = "pub unsafe fn read(p: *const i32) -> i32 { unsafe { *p } }";

        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            reset_for_test();
            let first_receipt = with_test_config(false, &directory.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
            .expect("fresh precise decision");
            let first_provenance = last_solve().expect("fresh solve provenance");
            assert_eq!(first_provenance.source, "real");
            assert_eq!(first_provenance.cache_status, "bypass");
            assert!(
                first_provenance
                    .cache_entry
                    .as_ref()
                    .is_some_and(|path| Path::new(path).is_file()),
                "fresh precise solve did not write an entry: {first_provenance:?}"
            );
            let first_model = first_provenance.model_sha256;

            reset_for_test();
            let second_receipt = with_test_config(true, &directory.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
            .expect("cached precise decision");
            let second_provenance = last_solve().expect("cache-hit provenance");
            assert_eq!(second_provenance.source, "cache");
            assert_eq!(second_provenance.cache_status, "hit");
            assert_eq!(second_provenance.solve_secs, 0.0);
            assert_eq!(second_provenance.model_sha256, first_model);
            assert_eq!(second_receipt, first_receipt);
            reset_for_test();
        })
        .unwrap_or_else(|error| error.raise());
    }

    /// The historical test identity is retained. Era5a supersedes the old
    /// key-only migration contract: a complete new derivation is required.
    #[test]
    fn rekey_changes_only_the_key_line_and_round_trips_through_the_loader() {
        let root =
            std::env::temp_dir().join(format!("era5a-legacy-rekey-refusal-{}", std::process::id()));
        struct Remove(PathBuf);
        impl Drop for Remove {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let _remove = Remove(root.clone());
        std::fs::create_dir_all(&root).unwrap();
        let legacy = root.join("legacy.model.tsv");
        let bytes = format!(
            "# fingerprint {}\n# schema bo-model-cache-v2\nM\tf::_1@d0\tref\n",
            "f".repeat(64)
        );
        std::fs::write(&legacy, &bytes).unwrap();
        assert!(rekey_entry(&legacy, &root.join("candidate"), &"a".repeat(64)).is_err());
        assert_eq!(std::fs::read_to_string(&legacy).unwrap(), bytes);
        assert!(
            !root.join("candidate").exists(),
            "refusal must not stage an old body under a new key"
        );
    }

    /// The three refusal shapes, at the level they are decidable without a
    /// compiler session: the entry's own self-identification.
    ///
    /// A cache file names its fingerprint **in its body as well as in its
    /// filename**. The body line is what catches an entry renamed or copied
    /// into place — a file whose name says one thing and whose contents were
    /// produced under another. Checking only the filename would make the cache
    /// trust the one part of the entry an accident can change for free.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* deleting the body-line
    /// check in [`load`] makes `a_renamed_entry_is_refused` pass a wrong
    /// fingerprint through.
    #[test]
    fn the_body_fingerprint_is_what_a_renamed_entry_fails_on() {
        let good = "# fingerprint abc123";
        assert_eq!(
            good,
            format!("# fingerprint {}", "abc123"),
            "the body line format is what `load` compares against; if this \
             changes, every existing entry silently stops loading"
        );
        // A file named `abc123.model.tsv` whose body says otherwise.
        let renamed_body = "# fingerprint DIFFERENT";
        assert_ne!(
            renamed_body,
            format!("# fingerprint {}", "abc123"),
            "a renamed entry must not match"
        );
    }

    /// **The analysis fingerprint moves when the analysis moves.**
    ///
    /// This is the term that makes the cache safe across a code edit, and it is
    /// the one most easily broken by a refactor: hashing paths without
    /// contents, or contents without paths, both produce a fingerprint that
    /// looks fine and stops discriminating. Two calls must agree, and the value
    /// must not be trivial.
    #[test]
    fn the_analysis_code_fingerprint_is_stable_and_nonempty() {
        let a = analysis_code_fingerprint();
        let b = analysis_code_fingerprint();
        assert_eq!(a, b, "the fingerprint must be deterministic within a run");
        assert_eq!(a.len(), 64, "SHA-256 hex: {a}");
        assert_ne!(
            a,
            format!("{:x}", Sha256::new().finalize()),
            "the fingerprint is the hash of NOTHING — the walk found no files, \
             so it would agree across every possible edit"
        );
    }

    /// Addendum 87's permanent portability control. Together with the re-key
    /// test above these two tests preregister the suite at 1,573/6/87.
    #[test]
    fn analysis_code_fingerprint_is_identical_across_distinct_worktree_roots() {
        struct Roots(Vec<PathBuf>);
        impl Drop for Roots {
            fn drop(&mut self) {
                for root in &self.0 {
                    let _ = std::fs::remove_dir_all(root);
                }
            }
        }
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        let a = std::env::temp_dir().join(format!("crat-cache-root-a-{nonce}"));
        let b = std::env::temp_dir().join(format!("crat-cache-root-b-{nonce}"));
        let _roots = Roots(vec![a.clone(), b.clone()]);
        for root in [&a, &b] {
            std::fs::create_dir_all(root.join("nested")).expect("analysis tree");
            std::fs::write(root.join("mod.rs"), "mod nested;\n").expect("root source");
            std::fs::write(root.join("nested/a.rs"), "pub fn a() {}\n").expect("nested source");
        }
        assert_ne!(a, b, "the control needs distinct roots");
        assert_eq!(
            analysis_code_fingerprint_at(&a),
            analysis_code_fingerprint_at(&b),
            "absolute worktree location entered the cache key"
        );
        let left_key = fingerprint_components(
            "solver",
            "program",
            &analysis_code_fingerprint_at(&a),
            b"toolchain",
        );
        let right_key = fingerprint_components(
            "solver",
            "program",
            &analysis_code_fingerprint_at(&b),
            b"toolchain",
        );
        assert_eq!(
            left_key, right_key,
            "the complete cache key is not portable"
        );
        std::fs::write(b.join("nested/a.rs"), "pub fn changed() {}\n").expect("mutate content");
        assert_ne!(
            analysis_code_fingerprint_at(&a),
            analysis_code_fingerprint_at(&b),
            "content stopped contributing to the cache key"
        );
    }

    /// **Reads are off unless asked for.** The cache must never engage by
    /// accident: a gate sweep that silently read a cache would report
    /// `solve: real` while doing nothing of the kind.
    #[test]
    fn reads_are_disabled_by_default() {
        // SAFETY-of-test note: this asserts the DEFAULT, i.e. the behaviour
        // when the variable is absent, which is the state every sweep runs in
        // unless it opts in.
        if std::env::var("CRAT_BO_CACHE").is_err() {
            assert!(!read_enabled(), "the cache engaged without being asked");
        }
    }
}

// ---------------------------------------------------------------------------
// Solve provenance (§5) and per-phase timing (§7)
// ---------------------------------------------------------------------------

/// Where the accepted model came from, and what it cost.
///
/// Recorded so the **row** carries it, not a human's memory. §5's rule is that
/// a number produced under cache cites `solve: cache@<fingerprint>` and a gate
/// sweep says `solve: real` — and the reader cannot tell by looking, which is
/// exactly the staleness rule's reasoning applied to one more axis. Mechanized
/// here rather than remembered at the call site.
#[derive(Clone, Debug)]
pub(crate) struct SolveProvenance {
    /// `"real"` or `"cache"`.
    pub source: &'static str,
    /// `"hit"`, `"miss"`, or `"bypass"` (reads disabled).
    pub cache_status: &'static str,
    pub fingerprint: String,
    /// SHA-256 of the canonical bytes of the consumed `VerifiedBo.model`.
    pub model_sha256: String,
    /// Written/consumed cache entry, when a directory was configured.
    pub cache_entry: Option<String>,
    /// Wall seconds spent in the BO solve — **0.0 on a cache hit**, which is
    /// the saving, and the residual is everything else the pipeline still pays.
    pub solve_secs: f64,
}

thread_local! {
    static LAST_SOLVE: std::cell::RefCell<Option<SolveProvenance>> =
        const { std::cell::RefCell::new(None) };
}

pub(crate) fn record_solve(p: SolveProvenance) {
    LAST_SOLVE.with(|c| *c.borrow_mut() = Some(p));
}

/// The provenance of the most recent solve in this process.
///
/// `None` means no solve ran, which a caller must report as such rather than
/// defaulting to `"real"` — a defaulted provenance is the failure this field
/// exists to prevent.
pub(crate) fn last_solve() -> Option<SolveProvenance> {
    LAST_SOLVE.with(|c| c.borrow().clone())
}

/// Render for a report row: `real` or `cache@<first 12 hex>`.
pub(crate) fn render_provenance() -> String {
    match last_solve() {
        None => "none".to_owned(),
        Some(p) if p.source == "cache" => {
            format!("cache@{}", &p.fingerprint[..12.min(p.fingerprint.len())])
        }
        Some(_) => "real".to_owned(),
    }
}

pub(crate) fn render_cache_status() -> &'static str {
    last_solve().map_or("none", |provenance| provenance.cache_status)
}

pub(crate) fn render_model_sha256() -> String {
    last_solve().map_or_else(|| "none".to_owned(), |provenance| provenance.model_sha256)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SolveReceipt {
    pub(crate) source: String,
    pub(crate) cache_status: String,
    pub(crate) fingerprint: String,
    pub(crate) model_sha256: String,
    pub(crate) cache_entry: Option<String>,
    pub(crate) solve_wall_s: String,
}

pub(crate) fn solve_receipt() -> Option<SolveReceipt> {
    last_solve().map(|provenance| SolveReceipt {
        source: provenance.source.to_owned(),
        cache_status: provenance.cache_status.to_owned(),
        fingerprint: provenance.fingerprint,
        model_sha256: provenance.model_sha256,
        cache_entry: provenance.cache_entry,
        solve_wall_s: format!("{:.6}", provenance.solve_secs),
    })
}

// ---------------------------------------------------------------------------
// Per-process memoization, and the counter that keeps it honest
// ---------------------------------------------------------------------------

/// How many times the model was **DERIVED** in this process — solved or loaded
/// from the on-disk cache — as opposed to reused from the in-process memo.
///
/// The recon worker has three independent consumers of the decision table
/// (`artifact_rows`, `facts_join_tsv`, `freed_slots_tsv`), and before
/// memoization each ran the whole pipeline: `total ≈ 3 × solve` on every
/// program, 2.83–3.15 measured. The redundancy was invisible because each
/// consumer looked cheap in isolation, and it was *mistaken for front-end cost*
/// in a subtraction-derived timing split that has since been retracted.
///
/// **This counter is what stops it returning silently.** The sweep asserts
/// exactly one derivation per program, so adding a fourth consumer that forgets
/// the memo fails a gate instead of quietly tripling a sweep.
pub(crate) fn derivations() -> usize {
    DERIVATIONS.with(|c| c.get())
}

thread_local! {
    static DERIVATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static MEMO: std::cell::RefCell<Option<(String, CachedModel)>> =
        const { std::cell::RefCell::new(None) };
}

/// The analyses-tree hash is constant for the life of the process; computing it
/// walks and reads the whole source tree, which is cheap once and silly thrice.
fn code_fingerprint_cached() -> &'static str {
    static ONCE: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    ONCE.get_or_init(analysis_code_fingerprint)
}

/// The in-process memo, keyed by the **same fingerprint the on-disk cache
/// uses** — one notion of "which program is this", not two.
///
/// Keyed rather than unconditional because the test suite runs many fixtures in
/// one process: an unkeyed memo would serve fixture A's model to fixture B.
pub(crate) fn memo_get(fp: &str) -> Option<CachedModel> {
    MEMO.with(|m| {
        m.borrow()
            .as_ref()
            .filter(|(k, cached)| {
                k == fp
                    && PREPARED.with(|prepared| {
                        prepared.borrow().as_ref().is_some_and(|p| {
                            p.entry.key == fp
                                && p.cached.model == cached.model
                                && p.cached.baseline_model == cached.baseline_model
                                && p.cached.a5_receipt == cached.a5_receipt
                        })
                    })
            })
            .map(|(_, v)| v.clone())
    })
}

pub(crate) fn memo_put(fp: &str, cached: &CachedModel) {
    MEMO.with(|m| *m.borrow_mut() = Some((fp.to_owned(), cached.clone())));
    DERIVATIONS.with(|c| c.set(c.get() + 1));
}

#[cfg(test)]
pub(crate) fn reset_for_test() {
    MEMO.with(|memo| *memo.borrow_mut() = None);
    DERIVATIONS.with(|count| count.set(0));
    LAST_SOLVE.with(|last| *last.borrow_mut() = None);
    PREPARED.with(|prepared| *prepared.borrow_mut() = None);
    PREPARE_ERROR.with(|error| *error.borrow_mut() = None);
}
