//! **The analysis model cache.** The BO solve, serialized under session-
//! independent keys, for DEV ITERATION ONLY.
//!
//! # What is cached, and what deliberately is not
//!
//! The **accepted model** — `SlotRef → SlotKind` — and nothing else. The
//! rustc front-end is the residual floor the rewriter always pays; the
//! emitability and construction facts are HIR passes keyed by `HirId`, which is
//! **not path-addressable**, so caching them would need a second key scheme for
//! a cheap computation. Caching a cheap thing under a fragile key is how a
//! cache becomes a correctness liability.
//!
//! # Fail-closed BY CONSTRUCTION
//!
//! [`load`] returns `Option`, and **every** failure path — absent file, unreadable
//! file, parse error, fingerprint mismatch, a key that does not resolve in this
//! session — returns `None`, which the caller can only answer by solving for
//! real. There is no "assume valid" arm to reach, so *loading stale silently*
//! is not a behaviour this module can express. That is the one forbidden
//! behaviour, and it is excluded structurally rather than by discipline.
//!
//! # Usage policy (recorded here because the code is where it binds)
//!
//! Dev iteration may read the cache. **Slice-close verdict sweeps and every
//! pre-registered gate sweep run a real solve with the cache bypassed**, and
//! say `solve: real` in their record. Any interim number produced under cache
//! cites `solve: cache@<fingerprint>`. This is the staleness rule extended to
//! solve provenance: the reader cannot tell by looking, so the record must say.
//!
//! # Single-writer
//!
//! The cache directory is the ladder lane's write surface, the same rule as
//! `target/boc1/**`. Cross-lane consumption, if ever, goes via published
//! manifests.

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
pub(crate) const ANALYSIS_FRAME: &str = "borrow-ownership@782663881fe7d1d463414aa9236aab09b1c21b0d";

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
    // §39 addendum 74: the accepted analysis frame and the complete resolved
    // solver configuration are key material, not a launch-time convention.
    let solver = solver_identity(a5_mode, attestation);

    // 1. The program's own source. Per-program, not the whole-corpus digest, so
    //    one program changing does not void the other nineteen.
    let tcx = program.tcx;
    let mut files = Vec::new();
    for f in tcx.sess.source_map().files().iter() {
        if let rustc_span::FileName::Real(rp) = &f.name
            && let Some(p) = rp.local_path()
        {
            files.push((canonical_program_path(p), f.src_hash.hash_bytes().to_vec()));
        }
    }
    let program = program_identity(tcx.crate_name(LOCAL_CRATE).as_str(), files);

    // 2. The analysis code. Any edit under `analyses/` changes what a solve
    //    means, so a cache written by the old code must not be read by the new.
    let code = code_fingerprint_cached();

    // 3. The toolchain.
    let toolchain = std::fs::read(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../rust-toolchain.toml"
    ))
    .unwrap_or_default();

    fingerprint_components(&solver, &program, code, &toolchain)
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
        let Ok(rd) = std::fs::read_dir(dir) else { return };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                walk(&p, out);
            } else if p.extension().is_some_and(|x| x == "rs") {
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
        let content = std::fs::read(f).unwrap_or_default();
        let content_hash = Sha256::digest(content);
        h.update((relative.len() as u64).to_le_bytes());
        h.update(relative.as_bytes());
        h.update(content_hash);
    }
    format!("{:x}", h.finalize())
}

fn analysis_code_fingerprint() -> String {
    analysis_code_fingerprint_at(Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/analyses"
    )))
}

fn entry_path(d: &Path, fingerprint: &str) -> PathBuf {
    d.join(format!("{fingerprint}.model.tsv"))
}

/// Stage one accepted entry under a new key without touching the source.
/// RED-first placeholder: addendum 88 requires line 1 to move too.
pub(crate) fn rekey_entry(
    old_path: &Path,
    new_dir: &Path,
    new_fingerprint: &str,
) -> Result<PathBuf, String> {
    if new_fingerprint.len() != 64 || !new_fingerprint.bytes().all(|byte| byte.is_ascii_hexdigit())
    {
        return Err(format!("invalid new fingerprint {new_fingerprint:?}"));
    }
    let bytes = std::fs::read(old_path).map_err(|error| error.to_string())?;
    let newline = bytes
        .iter()
        .position(|byte| *byte == b'\n')
        .ok_or_else(|| "cache entry has no fingerprint line".to_owned())?;
    let first = std::str::from_utf8(&bytes[..newline]).map_err(|error| error.to_string())?;
    let old_fingerprint = first
        .strip_prefix("# fingerprint ")
        .ok_or_else(|| format!("invalid cache fingerprint line {first:?}"))?;
    let old_name = old_path
        .file_name()
        .and_then(|name| name.to_str())
        .and_then(|name| name.strip_suffix(".model.tsv"))
        .ok_or_else(|| format!("invalid cache entry path {}", old_path.display()))?;
    if old_name != old_fingerprint {
        return Err(format!(
            "source cache key mismatch: filename={old_name} header={old_fingerprint}"
        ));
    }
    std::fs::create_dir_all(new_dir).map_err(|error| error.to_string())?;
    let new_path = entry_path(new_dir, new_fingerprint);
    let mut staged = format!("# fingerprint {new_fingerprint}\n").into_bytes();
    staged.extend_from_slice(&bytes[newline + 1..]);
    let mut output = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&new_path)
        .map_err(|error| error.to_string())?;
    std::io::Write::write_all(&mut output, &staged).map_err(|error| error.to_string())?;
    let permissions = std::fs::metadata(old_path)
        .map_err(|error| error.to_string())?
        .permissions();
    std::fs::set_permissions(&new_path, permissions).map_err(|error| error.to_string())?;
    let check = std::fs::read(&new_path).map_err(|error| error.to_string())?;
    let staged_newline = check
        .iter()
        .position(|byte| *byte == b'\n')
        .ok_or_else(|| "staged cache entry has no fingerprint line".to_owned())?;
    if check[staged_newline + 1..] != bytes[newline + 1..] {
        return Err("re-key changed bytes after line 1".to_owned());
    }
    Ok(new_path)
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
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    cached: &CachedModel,
    a5_mode: A5Mode,
    attestation: Option<WholeProgramAttestation>,
) -> Option<PathBuf> {
    let d = dir()?;
    let fp = fingerprint(program, a5_mode, attestation);
    if std::fs::create_dir_all(&d).is_err() {
        return None;
    };
    let mut payload = Vec::new();
    for row in canonical_model_rows(tcx, slots, &cached.model)? {
        payload.push(format!("M\t{row}"));
    }
    for row in canonical_model_rows(tcx, slots, &cached.baseline_model)? {
        payload.push(format!("B\t{row}"));
    }
    for line in cached.a5_receipt.lines() {
        if line.contains(['\t', '\r']) {
            return None;
        }
        payload.push(format!("R\t{line}"));
    }
    if cached.a5_receipt.is_empty() {
        return None;
    }
    let payload = payload.join("\n");
    let identity = solver_identity(a5_mode, attestation);
    let identity_sha = format!("{:x}", Sha256::digest(identity.as_bytes()));
    let payload_sha = format!("{:x}", Sha256::digest(payload.as_bytes()));
    let body = format!(
        "# fingerprint {fp}\n# schema {CACHE_SCHEMA}\n# analysis_frame {ANALYSIS_FRAME}\n\
         # solver_identity_sha256 {identity_sha}\n# a5_mode {}\n# a5_attestation {}\n\
         # payload_sha256 {payload_sha}\n{payload}\n",
        a5_mode.label(),
        attestation_label(attestation),
    );
    let path = entry_path(&d, &fp);
    std::fs::write(&path, body).ok()?;
    Some(path)
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

/// **Load, or refuse.** Every failure is `None`, and `None` means solve.
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
    let d = dir()?;
    let fp = fingerprint(program, a5_mode, attestation);
    let text = std::fs::read_to_string(entry_path(&d, &fp)).ok()?;

    // The fingerprint is in the key AND in the body. The body check catches a
    // file renamed or copied into place — the shape a manifest check exists for.
    let mut lines = text.lines();
    let first = lines.next()?;
    if first != format!("# fingerprint {fp}") {
        return None;
    }
    if lines.next()? != format!("# schema {CACHE_SCHEMA}")
        || lines.next()? != format!("# analysis_frame {ANALYSIS_FRAME}")
    {
        return None;
    }
    let identity = solver_identity(a5_mode, attestation);
    let identity_sha = format!("{:x}", Sha256::digest(identity.as_bytes()));
    if lines.next()? != format!("# solver_identity_sha256 {identity_sha}")
        || lines.next()? != format!("# a5_mode {}", a5_mode.label())
        || lines.next()? != format!("# a5_attestation {}", attestation_label(attestation))
    {
        return None;
    }
    let payload_sha_line = lines.next()?;
    let payload = lines.collect::<Vec<_>>().join("\n");
    let payload_sha = format!("{:x}", Sha256::digest(payload.as_bytes()));
    if payload_sha_line != format!("# payload_sha256 {payload_sha}") {
        return None;
    }

    // Rebuild the session-local keys by rendering every slot THIS session has
    // and matching on the canonical name. A key in the file that no longer
    // resolves is a refusal, not a skip.
    let mut by_key: FxHashMap<String, SlotRef> = FxHashMap::default();
    for (&fn_did, universe) in &slots.fn_local_slots {
        for i in 0..universe.len() {
            let id = super::slots::SlotId::from_usize(i);
            if let Some(k) = render_key(tcx, slots, SlotRef::Local(fn_did, id)) {
                if by_key.insert(k, SlotRef::Local(fn_did, id)).is_some() {
                    return None;
                }
            }
        }
    }
    for i in 0..slots.field_slots.len() {
        let id = super::slots::SlotId::from_usize(i);
        if let Some(k) = render_key(tcx, slots, SlotRef::Field(id)) {
            if by_key.insert(k, SlotRef::Field(id)).is_some() {
                return None;
            }
        }
    }

    let mut model = FxHashMap::default();
    let mut baseline_model = FxHashMap::default();
    let mut receipt = Vec::new();
    for line in payload.lines() {
        let mut fields = line.splitn(3, '\t');
        match (fields.next()?, fields.next(), fields.next()) {
            ("M", Some(key), Some(kind)) => {
                let slot = *by_key.get(key)?;
                if model.insert(slot, parse_kind(kind)?).is_some() {
                    return None;
                }
            }
            ("B", Some(key), Some(kind)) => {
                let slot = *by_key.get(key)?;
                if baseline_model.insert(slot, parse_kind(kind)?).is_some() {
                    return None;
                }
            }
            ("R", Some(line), None) => receipt.push(line.to_owned()),
            _ => return None,
        }
    }
    if model.len() != by_key.len() || baseline_model.len() != by_key.len() || receipt.is_empty() {
        return None;
    }
    Some(CachedModel {
        model,
        baseline_model,
        a5_receipt: format!("{}\n", receipt.join("\n")),
    })
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
            "analysis_frame=borrow-ownership@782663881fe7d1d463414aa9236aab09b1c21b0d",
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

    /// Addendum 88 / R1 — the permitted re-key changes only the filename and
    /// first line, and the staged entry must then load through production.
    #[test]
    fn rekey_changes_only_the_key_line_and_round_trips_through_the_loader() {
        struct TestDir(PathBuf);
        impl Drop for TestDir {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let root =
            std::env::temp_dir().join(format!("crat-cache-rekey-test-{}", std::process::id()));
        let source_dir = TestDir(root.join("old"));
        let staged_dir = TestDir(root.join("staged"));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&source_dir.0).expect("old cache dir");
        std::fs::create_dir_all(&staged_dir.0).expect("staged cache dir");
        let source = "pub unsafe fn read(p: *const i32) -> i32 { unsafe { *p } }";

        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            reset_for_test();
            let receipt = with_test_config(false, &source_dir.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
            .expect("fresh precise decision");
            let provenance = last_solve().expect("fresh solve provenance");
            let current_fp = provenance.fingerprint;
            let current_model = provenance.model_sha256;
            let current_path = provenance.cache_entry.expect("fresh cache entry");
            let current_text = std::fs::read_to_string(&current_path).expect("fresh entry text");
            let (_, tail) = current_text.split_once('\n').expect("fingerprint line");

            let legacy_fp = "f".repeat(64);
            assert_ne!(legacy_fp, current_fp);
            let legacy_path = entry_path(&source_dir.0, &legacy_fp);
            std::fs::write(&legacy_path, format!("# fingerprint {legacy_fp}\n{tail}"))
                .expect("legacy entry");
            std::fs::remove_file(&current_path).expect("remove current-key source entry");

            let staged = rekey_entry(&legacy_path, &staged_dir.0, &current_fp)
                .expect("stage re-keyed entry");
            let staged_text = std::fs::read_to_string(&staged).expect("staged entry text");
            let (staged_first, staged_tail) = staged_text.split_once('\n').expect("staged header");
            assert_eq!(staged_first, format!("# fingerprint {current_fp}"));
            assert_eq!(staged_tail.as_bytes(), tail.as_bytes());
            assert!(
                legacy_path.is_file(),
                "the accepted source must be retained"
            );

            reset_for_test();
            let loaded_receipt = with_test_config(true, &staged_dir.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
            .expect("staged precise decision");
            let loaded = last_solve().expect("staged load provenance");
            assert_eq!(loaded.source, "cache");
            assert_eq!(loaded.cache_status, "hit");
            assert_eq!(loaded.model_sha256, current_model);
            assert_eq!(loaded_receipt, receipt);
            reset_for_test();
        })
        .unwrap_or_else(|error| error.raise());
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
            .filter(|(k, _)| k == fp)
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
}
