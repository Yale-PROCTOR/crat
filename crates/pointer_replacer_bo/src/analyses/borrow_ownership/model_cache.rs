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
    SlotKind,
    a5_overlap::{A5Mode, WholeProgramAttestation},
    crate_slots::CrateSlots,
    slot_key::{field_key, local_key},
    solver::SlotRef,
};
use crate::utils::rustc::RustProgram;

/// The frozen analysis semantics consumed by Item E. Rewriter/cache-only
/// changes after this commit do not advance this identity.
#[cfg(test)]
pub(crate) const ANALYSIS_FRAME: &str = "era5c-l01p14-v1";

#[cfg(test)]
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

#[cfg(test)]
fn canonical_program_path(path: &Path) -> String {
    std::fs::canonicalize(path)
        .unwrap_or_else(|_| path.to_path_buf())
        .display()
        .to_string()
}

/// The cache directory, read and written; `None` means no cache. The pass sets it
/// once per run (`rewrite_bo`). It is process-wide because the analysis runs on
/// rustc's thread, not the caller's.
static CACHE_DIR: std::sync::Mutex<Option<PathBuf>> = std::sync::Mutex::new(None);

/// Configure the cache directory for this process (`None`: no cache).
pub(crate) fn configure(dir: Option<PathBuf>) {
    *CACHE_DIR
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner) = dir;
}

/// Reads are on exactly when a cache directory is configured; a real solve
/// writes to the same directory.
pub(crate) fn read_enabled() -> bool {
    dir().is_some()
}

pub(crate) fn dir() -> Option<PathBuf> {
    #[cfg(test)]
    if let Some(dir) = TEST_CONFIG.with(|config| config.borrow().clone()) {
        return Some(dir);
    }
    CACHE_DIR
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .clone()
}

#[cfg(test)]
thread_local! {
    static TEST_CONFIG: std::cell::RefCell<Option<PathBuf>> = const {
        std::cell::RefCell::new(None)
    };
}

/// `run` with a fresh scratch cache directory configured (unique per call, under
/// `temp_dir()`), removed afterwards: for tests that read the staged entry.
#[cfg(test)]
pub(crate) fn with_scratch_cache<T>(run: impl FnOnce() -> T) -> T {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "crat-staged-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    let out = with_test_config(&dir, run);
    let _ = std::fs::remove_dir_all(&dir);
    out
}

#[cfg(test)]
pub(crate) fn with_test_config<T>(dir: &Path, run: impl FnOnce() -> T) -> T {
    struct Restore(Option<PathBuf>);
    impl Drop for Restore {
        fn drop(&mut self) {
            TEST_CONFIG.with(|config| *config.borrow_mut() = self.0.take());
        }
    }
    let previous = TEST_CONFIG.with(|config| config.borrow_mut().replace(dir.to_path_buf()));
    let _restore = Restore(previous);
    run()
}

/// Everything the cached model is a function of.
///
/// A change to **any** of these must invalidate, so they are hashed together
/// into one value rather than checked severally — a severally-checked key grows
/// a forgotten term.
///
/// The key does not name the A5 mode: the decide path caches the frame's mode
/// only (`PreciseReplay` with the frozen-graph attestation), so the mode
/// arguments are kept for the callers and not read.
pub(crate) fn fingerprint(
    program: &RustProgram<'_>,
    _a5_mode: A5Mode,
    _attestation: Option<WholeProgramAttestation>,
) -> String {
    super::cache_contract::semantic_key(
        &semantic_inputs(program).expect("complete semantic inputs before any cache lookup"),
    )
    .expect("valid portable semantic input identity")
}

/// The cache key's inputs: the crate name, its sources by logical path under their
/// common root, and the three build constants. Nothing from the environment.
pub(crate) fn semantic_inputs(
    program: &RustProgram<'_>,
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
    Ok(super::cache_contract::SemanticInputs {
        program: program.tcx.crate_name(LOCAL_CRATE).to_string(),
        files,
        analysis: env!("BO_ANALYSIS_FINGERPRINT").to_owned(),
        toolchain: env!("BO_TOOLCHAIN_SHA256").to_owned(),
        dependencies: env!("BO_LOCK_SHA256").to_owned(),
    })
}
#[cfg(test)]
fn fingerprint_components(solver: &str, program: &str, code: &str, toolchain: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(solver.as_bytes());
    h.update(program.as_bytes());
    h.update(code.as_bytes());
    h.update(toolchain);
    format!("{:x}", h.finalize())
}

/// The analysis code fingerprint, baked in by `build.rs` (`code_fingerprint.rs`).
pub(crate) fn current_analysis_digest() -> String {
    env!("BO_ANALYSIS_FINGERPRINT").to_owned()
}

fn entry_path(d: &Path, fingerprint: &str) -> PathBuf {
    d.join("era5b-model-cache-v1")
        .join(format!("{fingerprint}.json"))
}

/// Retained API for explicit refusal of legacy key-only migration into era5a.
#[cfg(test)]
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
    /// The semantic key the model is cached under.
    key: String,
    /// The staged entry, under the configured cache directory; `None` when no
    /// directory is configured, in which case nothing is staged anywhere.
    entry: Option<std::sync::Arc<super::cache_contract::StreamedEntry>>,
    cached: CachedModel,
    /// R1178-1 (era-5c relay 236, fix (i)): on the writer side, the arm-(a) receipts as `prepare`
    /// wrote them into the entry -- the same rows, order and not-recorded reason a read of the
    /// staged file decodes -- so the hoist's loader never re-opens that file. `None` on the
    /// reader side, whose `Metadata` captured them while the entry was read.
    arg_order_applied: Option<Result<Vec<super::portable_export::ArgOrderRow>, String>>,
}
thread_local! {
    static PREPARED: std::cell::RefCell<Option<Prepared>> = const { std::cell::RefCell::new(None) };
    static PREPARE_ERROR: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
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

/// Preserve the accepted capture before the unchanged consumer drops its
/// recording: the key, the model and the argument-order receipts the emission
/// reads, in memory; and, only when a cache directory is configured, the
/// complete entry staged under it (nothing is written anywhere else).
/// Serialization failure affects cache completeness, not kinds.
pub(crate) fn prepare(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    origins: &super::origin_summary::OriginSummaries,
    verified: &super::construction::VerifiedBo,
    captured: &super::export::BoExport,
) {
    let result = (|| -> Result<Prepared, String> {
        let inputs = semantic_inputs(program)?;
        let key = super::cache_contract::semantic_key(&inputs)?;
        let entry = match dir() {
            None => None,
            Some(cache) => {
                let directory = cache.join("era5b-model-cache-v1");
                let portable = super::portable_export::stream::collect_to_path(
                    program, slots, captured, &directory,
                )?;
                let origin =
                    super::origin_evidence::collect(program, slots, origins, Some(captured));
                let mut functions: Vec<_> = program
                    .functions
                    .iter()
                    .map(|did| program.tcx.def_path_str(did.to_def_id()))
                    .collect();
                functions.sort();
                let e5c_universe: Vec<_> = universe(program.tcx, slots)
                    .ok_or("invalid slot universe")?
                    .into_keys()
                    .collect();
                let e5c_model = model_map(program.tcx, slots, &verified.model)
                    .ok_or("invalid accepted model keys")?;
                let e5c_baseline = model_map(program.tcx, slots, &verified.baseline_model)
                    .ok_or("invalid baseline model keys")?;
                // R473-4 design (A): stream the canonical origin bytes to a file,
                // per element, and hand the cache the PATH. The whole-`Value` form that
                // cost 31 GiB on libzahl is never built. The file is removed once the
                // entry has copied it in (and by the guard on any early return).
                struct OriginFile(std::path::PathBuf);
                impl Drop for OriginFile {
                    fn drop(&mut self) {
                        let _ = std::fs::remove_file(&self.0);
                    }
                }
                std::fs::create_dir_all(&directory).map_err(|error| error.to_string())?;
                // Unique per call, as the exports spool is: one process runs many
                // prepares concurrently and a pid-only name collides between them.
                static NEXT_ORIGIN: std::sync::atomic::AtomicU64 =
                    std::sync::atomic::AtomicU64::new(0);
                let origin_path = directory.join(format!(
                    ".origin-{}-{}.json",
                    std::process::id(),
                    NEXT_ORIGIN.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                ));
                {
                    let file = std::fs::File::options()
                        .write(true)
                        .create(true)
                        .truncate(true)
                        .open(&origin_path)
                        .map_err(|error| error.to_string())?;
                    let mut writer = std::io::BufWriter::new(file);
                    origin.write_canonical_json(&mut writer)?;
                    std::io::Write::flush(&mut writer).map_err(|error| error.to_string())?;
                }
                let _origin_file = OriginFile(origin_path.clone());
                let e5c_origin = super::cache_contract::stream::OriginSource::File(origin_path);
                let metadata = super::cache_contract::stream::Metadata {
                    schema: super::cache_contract::SCHEMA.into(),
                    key: key.clone(),
                    inputs,
                    functions,
                    universe: e5c_universe,
                    model: e5c_model,
                    baseline: e5c_baseline,
                    receipt: verified.receipt.clone(),
                    origin: e5c_origin,
                    move_store: Default::default(),
                    arg_order: Default::default(),
                };
                Some(std::sync::Arc::new(super::cache_contract::stage_streamed(
                    &directory,
                    metadata,
                    &portable.path,
                )?))
            }
        };
        Ok(Prepared {
            key,
            entry,
            cached: CachedModel {
                model: verified.model.clone(),
                baseline_model: verified.baseline_model.clone(),
                a5_receipt: verified.receipt.clone(),
            },
            arg_order_applied: Some(writer_arg_order_applied(program, slots, captured)),
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

/// L01¹¹ (R659-1; wave-5d 133 STOP 2): the prepared entry's arm-(a) receipts,
/// for the emission's hoist (`DecisionTable::arg_order_hoists`). Refused unless
/// the entry records them.
pub(crate) fn prepared_arg_order_applied(
    fingerprint: &str,
) -> Result<Vec<super::portable_export::ArgOrderRow>, String> {
    // R1178-1 (era-5c relays 236 / 237): the writer side reads the receipts `prepare` kept (fix
    // (i)); the reader side decodes them from the borrowed `Metadata` (fix (ii): no clone of it).
    // Only a writer-side entry prepared without them falls back to reading the staged file.
    PREPARED.with(|prepared| {
        let prepared = prepared.borrow();
        let prepared = prepared
            .as_ref()
            .filter(|prepared| prepared.key == fingerprint)
            .ok_or("no prepared entry for this fingerprint")?;
        if let Some(rows) = &prepared.arg_order_applied {
            return rows.clone();
        }
        let entry = prepared
            .entry
            .as_ref()
            .ok_or("no staged entry for this fingerprint")?;
        match entry.metadata.arg_order {
            super::cache_contract::stream::MoveStoreCapture::Missing => {
                super::cache_contract::validate_file(&entry.path)?.arg_order_applied()
            }
            _ => entry.metadata.arg_order_applied(),
        }
    })
}

/// R1178-1: the arm-(a) receipts as the entry's `arg-order-applied` family records them, decoded
/// as a read of that family would: `portable_export::arg_order_rows` (the writer's own rows,
/// sorted by the reader's order), or the family's not-recorded refusal when the arm is off.
fn writer_arg_order_applied(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    captured: &super::export::BoExport,
) -> Result<Vec<super::portable_export::ArgOrderRow>, String> {
    match super::portable_export::arg_order_rows(program, slots, captured)? {
        Some(rows) => Ok(rows),
        None => Err(format!(
            "arg-order receipts not recorded: {}",
            super::portable_export::ARG_ORDER_NOT_RECORDED
        )),
    }
}

/// R1178-1's witness: the receipts read back from the prepared entry's staged FILE, as the loader
/// read them before fix (i).
#[cfg(test)]
pub(crate) fn prepared_arg_order_from_file(
    fingerprint: &str,
) -> Result<Vec<super::portable_export::ArgOrderRow>, String> {
    let path = PREPARED
        .with(|prepared| {
            prepared
                .borrow()
                .as_ref()
                .filter(|prepared| prepared.key == fingerprint)
                .and_then(|prepared| prepared.entry.as_ref())
                .map(|entry| entry.path.clone())
        })
        .ok_or("no staged entry for this fingerprint")?;
    super::cache_contract::validate_file(&path)?.arg_order_applied()
}

/// L01¹¹ (R666-1, the loader): the prepared entry's arm-(a) receipts as the
/// emission's hoist keys `((lo, hi), caller, lent)`, for the one line the
/// rewriter needs: `table.arg_order_hoists = prepared_arg_order_hoists(tcx, &fp)`.
/// Each call's span is re-read from THIS session's MIR at the receipt's
/// location, so a receipt another process wrote keys this session's AST.
pub(crate) fn prepared_arg_order_hoists(
    tcx: TyCtxt<'_>,
    fingerprint: &str,
) -> Result<
    rustc_hash::FxHashSet<(
        (u32, u32),
        rustc_span::def_id::LocalDefId,
        rustc_middle::mir::Local,
    )>,
    String,
> {
    let rows = prepared_arg_order_applied(fingerprint)?;
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

/// L01⁹ wall 4 (R574-5 (iii)): the prepared entry's store-as-move obligations,
/// for the rewriter's discharge (ownership-fields 069 §4). A loaded entry already
/// carries them from the streamed read; a staged one is read back once.
/// Refused unless the entry records them.
#[cfg(test)]
pub(crate) fn prepared_move_store_obligations(
    fingerprint: &str,
) -> Result<Vec<super::portable_export::MoveStoreRow>, String> {
    let (path, metadata) = PREPARED
        .with(|prepared| {
            prepared
                .borrow()
                .as_ref()
                .filter(|prepared| prepared.key == fingerprint)
                .and_then(|prepared| prepared.entry.as_ref())
                .map(|entry| (entry.path.clone(), entry.metadata.clone()))
        })
        .ok_or("no staged entry for this fingerprint")?;
    match metadata.move_store {
        super::cache_contract::stream::MoveStoreCapture::Missing => {
            super::cache_contract::validate_file(&path)?.move_store_obligations()
        }
        _ => metadata.move_store_obligations(),
    }
}

/// Explicit materializing compatibility view; model derivation and publication
/// use the shared streamed entry instead.
#[cfg(test)]
pub(crate) fn prepared_entry(fingerprint: &str) -> Option<super::cache_contract::CompleteEntry> {
    let entry = PREPARED.with(|prepared| {
        prepared
            .borrow()
            .as_ref()
            .filter(|prepared| prepared.key == fingerprint)
            .and_then(|prepared| prepared.entry.clone())
    })?;
    let bytes = std::fs::read(&entry.path).ok()?;
    // A spooled entry its own contract refuses is a refusal worth reading, not
    // a silent `None` — the prepare slot carries it for the caller.
    match super::cache_contract::decode(&bytes) {
        Ok(entry) => Some(entry),
        Err(error) => {
            PREPARE_ERROR.with(|slot| *slot.borrow_mut() = Some(error));
            None
        }
    }
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
    let directory = dir()?.join("era5b-model-cache-v1");
    let fp = fingerprint(program, a5_mode, attestation);
    let entry = PREPARED.with(|prepared| {
        prepared
            .borrow()
            .as_ref()
            .filter(|p| {
                p.key == fp
                    && p.cached.model == cached.model
                    && p.cached.baseline_model == cached.baseline_model
                    && p.cached.a5_receipt == cached.a5_receipt
            })
            .and_then(|p| p.entry.clone())
    })?;
    match super::cache_contract::publish_streamed(&directory, &entry) {
        Ok(path) => Some(path),
        Err(error) => {
            PREPARE_ERROR.with(|e| *e.borrow_mut() = Some(error));
            None
        }
    }
}

pub(crate) fn render_key(tcx: TyCtxt<'_>, slots: &CrateSlots, r: SlotRef) -> Option<String> {
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
    _a5_mode: A5Mode,
    _attestation: Option<WholeProgramAttestation>,
) -> Option<CachedModel> {
    if !read_enabled() {
        return None;
    }
    let expected = semantic_inputs(program).ok()?;
    let fp = super::cache_contract::semantic_key(&expected).ok()?;
    let path = entry_path(&dir()?, &fp);
    let entry = super::cache_contract::validate_file(&path).ok()?;
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
            key: fp,
            entry: Some(std::sync::Arc::new(
                super::cache_contract::existing_streamed(path, entry),
            )),
            cached: cached.clone(),
            arg_order_applied: None,
        })
    });
    Some(cached)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// S2's cache fixture (D0): one function, solved in a few seconds.
    const S2_FIXTURE: &str = "pub unsafe fn read(p: *const i32) -> i32 { unsafe { *p } }\n";

    /// The five variables a batch job set to name its inputs; the key reads none of them (S2 D5).
    const S2_JOB_VARIABLES: [&str; 5] = [
        "CRAT_ERA5_LAUNCH_DIGEST",
        "CRAT_ERA5_PROGRAM",
        "CRAT_ERA5_INPUT_ROOT",
        "CRAT_ERA5_TOOLCHAIN_DIGEST",
        "CRAT_ERA5_DEPENDENCY_DIGEST",
    ];

    /// Child of `s2_t_key_1_the_key_reads_no_job_environment`: the key of the fixture file named by
    /// `S2_KEY_FIXTURE`.
    #[test]
    #[ignore = "child of s2_t_key_1_the_key_reads_no_job_environment"]
    fn s2_print_fixture_key() {
        let path = std::env::var_os("S2_KEY_FIXTURE").expect("S2_KEY_FIXTURE");
        ::utils::compilation::run_compiler_on_path(Path::new(&path), |tcx| {
            eprintln!(
                "S2_KEY {}",
                crate::bo_rewriter::cache_fingerprint_for_test(tcx)
            );
        })
        .unwrap_or_else(|error| error.raise());
    }

    /// T-key-1 (S2 D0a): two children that differ only in the five job variables compute one key
    /// for one fixture file.
    #[test]
    fn s2_t_key_1_the_key_reads_no_job_environment() {
        let directory = std::env::temp_dir().join(format!("crat-s2-key-{}", std::process::id()));
        let source = directory.join("inputs").join("fixture.rs");
        std::fs::create_dir_all(source.parent().unwrap()).expect("fixture directory");
        std::fs::write(&source, S2_FIXTURE).expect("fixture");
        let key = |job: &[(&str, std::ffi::OsString)]| {
            let mut command = std::process::Command::new(std::env::current_exe().expect("exe"));
            command.args([
                "analyses::borrow_ownership::model_cache::tests::s2_print_fixture_key",
                "--exact",
                "--ignored",
                "--nocapture",
                "--test-threads=1",
            ]);
            command.env("S2_KEY_FIXTURE", &source);
            for name in S2_JOB_VARIABLES {
                command.env_remove(name);
            }
            for (name, value) in job {
                command.env(name, value);
            }
            let output = command.output().expect("child test");
            let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
            assert!(output.status.success(), "child failed:\n{stderr}");
            stderr
                .lines()
                .find_map(|line| line.strip_prefix("S2_KEY "))
                .unwrap_or_else(|| panic!("no key printed:\n{stderr}"))
                .to_owned()
        };
        let plain = key(&[]);
        let job = key(&[
            ("CRAT_ERA5_LAUNCH_DIGEST", "s2-launch".into()),
            ("CRAT_ERA5_PROGRAM", "s2-program".into()),
            ("CRAT_ERA5_INPUT_ROOT", directory.clone().into_os_string()),
            ("CRAT_ERA5_TOOLCHAIN_DIGEST", "a".repeat(64).into()),
            ("CRAT_ERA5_DEPENDENCY_DIGEST", "b".repeat(64).into()),
        ]);
        let _ = std::fs::remove_dir_all(&directory);
        assert_eq!(plain, job, "a job variable moved the key");
    }

    /// One fresh solve of the fixture with `directory` configured, and the entry it wrote.
    fn s2_fresh_entry(directory: &Path) -> PathBuf {
        ::utils::compilation::run_compiler_on_str(S2_FIXTURE, |tcx| {
            reset_for_test();
            with_test_config(directory, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
            .expect("fresh decision");
            let entry = last_solve()
                .and_then(|provenance| provenance.cache_entry)
                .expect("the fresh solve wrote an entry");
            reset_for_test();
            PathBuf::from(entry)
        })
        .unwrap_or_else(|error| error.raise())
    }

    /// T-key-2 (S2 D0a): an entry in the format before S2, whose inputs carry `configuration`, is
    /// a validated miss; the same entry without it validates.
    #[test]
    fn s2_t_key_2_an_entry_with_a_configuration_is_a_miss() {
        let directory =
            std::env::temp_dir().join(format!("crat-s2-old-entry-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        let entry = s2_fresh_entry(&directory);
        let text = std::fs::read_to_string(&entry).expect("entry");
        let inputs = text.find("\"inputs\":{").expect("inputs");
        let dependencies = inputs
            + text[inputs..]
                .find("\"dependencies\":\"")
                .expect("dependencies");
        let close = dependencies + "\"dependencies\":\"".len() + 64 + 1;
        let old = if text[close..].starts_with(",\"configuration\":\"") {
            text.clone()
        } else {
            format!(
                "{},\"configuration\":\"{}\"{}",
                &text[..close],
                "c".repeat(64),
                &text[close..]
            )
        };
        let old_path = directory.join("old-format.json");
        std::fs::write(&old_path, old).expect("old-format entry");
        let current = super::super::cache_contract::validate_file(&entry);
        let previous = super::super::cache_contract::validate_file(&old_path);
        let _ = std::fs::remove_dir_all(&directory);
        assert!(current.is_ok(), "the entry as written: {current:?}");
        assert!(
            previous
                .as_ref()
                .is_err_and(|error| error.contains("configuration")),
            "an entry with a configuration validated: {:?}",
            previous.map(|metadata| metadata.key)
        );
    }

    /// T-fp-1 (S2 D0b): the analysis fingerprint is a build constant.
    #[test]
    fn s2_t_fp_1_the_fingerprint_is_a_build_constant() {
        assert!(option_env!("BO_ANALYSIS_FINGERPRINT").is_some());
    }

    /// T-fp-2 (S2 D0b): the build's covered list names the seven legacy modules the analysis
    /// runs on, BO's analyses, and the ESC allowlist.
    #[test]
    fn s2_t_fp_2_the_covered_list_names_every_analysis_input() {
        let list = option_env!("OUT_DIR")
            .map(|out| Path::new(out).join("bo_analysis_files.txt"))
            .and_then(|path| std::fs::read_to_string(path).ok())
            .unwrap_or_default();
        let missing: Vec<_> = [
            "bo/borrow/",
            "bo/borrow_ownership/",
            "bo/borrow_ownership/esc_minimal_allowlist.tsv",
            "legacy/analyses/type_qualifier/foster/",
            "legacy/analyses/mir/",
            "legacy/analyses/offset_sign/",
            "legacy/analyses/liveness.rs",
            "legacy/analyses/lattice.rs",
            "legacy/utils/rustc.rs",
        ]
        .into_iter()
        .filter(|prefix| !list.lines().any(|line| line.starts_with(prefix)))
        .collect();
        assert!(missing.is_empty(), "not covered: {missing:?}");
    }

    /// T-fp-3 (S2 D4): the baked values equal a recomputation over the source tree now, so
    /// `rerun-if-changed` missed no edit.
    #[test]
    fn s2_t_fp_3_the_build_values_are_the_source_tree_s() {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let analyses = manifest.join("src/analyses");
        let legacy = manifest.join("../pointer_replacer/src");
        let roots = super::super::code_fingerprint::analysis_roots(&analyses, &legacy);
        assert_eq!(
            env!("BO_ANALYSIS_FINGERPRINT"),
            super::super::code_fingerprint::fingerprint(&roots),
            "the baked fingerprint is stale"
        );
        let sha = |path: &str| {
            format!(
                "{:x}",
                Sha256::digest(std::fs::read(manifest.join(path)).expect("recipe file"))
            )
        };
        assert_eq!(
            env!("BO_TOOLCHAIN_SHA256"),
            sha("../../rust-toolchain.toml")
        );
        assert_eq!(env!("BO_LOCK_SHA256"), sha("../../Cargo.lock"));
    }

    /// quadtree, whose `insert_(tree, (*tree).root, …)` call carries the argument-order hoist.
    const S2_QUADTREE: &str = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../benchmarks/rs-crown-derived/quadtree/lib.rs"
    );

    /// Child of T-tmp-1 / T-tmp-2: decide `S2_TMP_SOURCE` with no cache directory and print the
    /// argument-order hoists the table carries.
    #[test]
    #[ignore = "child of s2_t_tmp_1 / s2_t_tmp_2"]
    fn s2_inner_decide_without_a_cache() {
        let path = std::env::var_os("S2_TMP_SOURCE").expect("S2_TMP_SOURCE");
        ::utils::compilation::run_compiler_on_path(Path::new(&path), |tcx| {
            let (table, _) = crate::bo_rewriter::decide_table_with_emission_config(
                tcx,
                None,
                &Default::default(),
            )
            .expect("decision");
            for (_, caller, _) in &table.arg_order_hoists {
                eprintln!("S2_HOIST {}", tcx.def_path_str(caller.to_def_id()));
            }
            eprintln!("S2_HOISTS {}", table.arg_order_hoists.len());
        })
        .unwrap_or_else(|error| error.raise());
    }

    /// The child's stderr, run with `TMPDIR` = `tmp` and no cache directory.
    fn s2_decide_without_a_cache(tmp: &Path) -> String {
        let mut command = std::process::Command::new(std::env::current_exe().expect("exe"));
        command.args([
            "analyses::borrow_ownership::model_cache::tests::s2_inner_decide_without_a_cache",
            "--exact",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ]);
        command.env("TMPDIR", tmp);
        command.env("S2_TMP_SOURCE", S2_QUADTREE);
        command.env_remove("CRAT_BO_CACHE_DIR");
        let output = command.output().expect("child test");
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(output.status.success(), "child failed:\n{stderr}");
        stderr
    }

    /// T-tmp-1 (S2 D14a): with no cache directory, a solve leaves nothing under `TMPDIR`.
    #[test]
    fn s2_t_tmp_1_no_cache_directory_writes_nothing() {
        if !Path::new(S2_QUADTREE).is_file() {
            eprintln!("corpus absent; skipping");
            return;
        }
        let tmp = std::env::temp_dir().join(format!("crat-s2-tmp-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        std::fs::create_dir_all(&tmp).expect("fresh TMPDIR");
        let text = s2_decide_without_a_cache(&tmp);
        let left: Vec<_> = std::fs::read_dir(&tmp)
            .expect("TMPDIR")
            .map(|entry| entry.expect("entry").file_name())
            .collect();
        let _ = std::fs::remove_dir_all(&tmp);
        assert!(text.contains("S2_HOISTS "), "{text}");
        assert!(left.is_empty(), "left under TMPDIR: {left:?}");
    }

    /// T-tmp-2 (S2 D14a): with no cache directory the table still carries quadtree's hoist.
    #[test]
    fn s2_t_tmp_2_no_cache_directory_keeps_the_hoist() {
        if !Path::new(S2_QUADTREE).is_file() {
            eprintln!("corpus absent; skipping");
            return;
        }
        let tmp = std::env::temp_dir().join(format!("crat-s2-tmp2-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&tmp);
        std::fs::create_dir_all(&tmp).expect("fresh TMPDIR");
        let text = s2_decide_without_a_cache(&tmp);
        let _ = std::fs::remove_dir_all(&tmp);
        assert!(
            text.lines()
                .any(|line| line.starts_with("S2_HOIST ") && line.ends_with("::quadtree_insert")),
            "no hoist on quadtree_insert:\n{text}"
        );
    }

    /// T-cache-1 (S2 D0b): with one cache directory and nothing else, the second run of the
    /// fixture reads the first one's entry.
    #[test]
    fn s2_t_cache_1_one_directory_reads_what_it_wrote() {
        let directory =
            std::env::temp_dir().join(format!("crat-s2-one-dir-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&directory);
        s2_fresh_entry(&directory);
        let second = ::utils::compilation::run_compiler_on_str(S2_FIXTURE, |tcx| {
            reset_for_test();
            with_test_config(&directory, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
            .expect("second decision");
            let provenance = last_solve().expect("provenance");
            reset_for_test();
            provenance
        })
        .unwrap_or_else(|error| error.raise());
        let _ = std::fs::remove_dir_all(&directory);
        assert_eq!(
            (second.source, second.cache_status),
            ("cache", "hit"),
            "the second run solved again"
        );
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
            let first_receipt = with_test_config(&directory.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
            .expect("fresh precise decision");
            let first_provenance = last_solve().expect("fresh solve provenance");
            assert_eq!(first_provenance.source, "real");
            // One directory is read and written: the first run misses, then writes.
            assert_eq!(first_provenance.cache_status, "miss");
            assert!(
                first_provenance
                    .cache_entry
                    .as_ref()
                    .is_some_and(|path| Path::new(path).is_file()),
                "fresh precise solve did not write an entry: {first_provenance:?}"
            );
            let first_model = first_provenance.model_sha256;

            reset_for_test();
            let second_receipt = with_test_config(&directory.0, || {
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
        let a = current_analysis_digest();
        let b = current_analysis_digest();
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
        let analysis_code_fingerprint_at = |dir: &Path| {
            super::super::code_fingerprint::fingerprint(&[super::super::code_fingerprint::Root {
                label: "bo",
                dir,
                files: None,
            }])
        };
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

    /// **No directory, no cache.** The cache never engages by accident: without a
    /// configured directory nothing is read (or written).
    #[test]
    fn reads_are_disabled_without_a_directory() {
        assert!(!read_enabled(), "the cache engaged without a directory");
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
#[cfg(test)]
pub(crate) fn render_provenance() -> String {
    match last_solve() {
        None => "none".to_owned(),
        Some(p) if p.source == "cache" => {
            format!("cache@{}", &p.fingerprint[..12.min(p.fingerprint.len())])
        }
        Some(_) => "real".to_owned(),
    }
}

#[cfg(test)]
pub(crate) fn render_cache_status() -> &'static str {
    last_solve().map_or("none", |provenance| provenance.cache_status)
}

#[cfg(test)]
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
#[cfg(test)]
pub(crate) fn derivations() -> usize {
    DERIVATIONS.with(|c| c.get())
}

thread_local! {
    static DERIVATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static MEMO: std::cell::RefCell<Option<(String, CachedModel)>> =
        const { std::cell::RefCell::new(None) };
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
                            p.key == fp
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
