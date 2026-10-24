//! The `bo` pass: the emission path the censuses ran (`diagnose_raw_boundary_census_with_config`)
//! behind a non-test entry, with the worker's emitted-tree persistence applied in place.

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use sha2::{Digest, Sha256};

use crate::{
    analyses::borrow_ownership::model_cache,
    bo_rewriter::{
        self, E1Capture, EmissionRunConfig, decision::exposure::ConfiguredExposureInput,
        plan::FileKey,
    },
};

/// The `[pointer]` table of crat's configuration: the settings of the pointer pass.
#[derive(Debug, Default, Clone, serde::Deserialize)]
pub struct Config {
    #[serde(default)]
    pub c_exposed_fns: rustc_hash::FxHashSet<String>,
}

/// What a `bo` run reports: the outcome, the identity the frame check reads, the solve's
/// provenance, and the per-file digests of the emission.
pub struct BoReceipt {
    pub outcome: &'static str,
    pub status: &'static str,
    pub analysis_fingerprint: String,
    pub input_tree_sha256: String,
    pub emitted_tree_sha256: String,
    pub files_changed: usize,
    pub files_total: usize,
    pub verify_rounds: usize,
    pub reverted_count: usize,
    pub solve: String,
    pub file_rows: String,
    /// R1295-1: configured exposure names that matched no local function (ignored).
    pub configured_unmatched: Vec<String>,
    /// R1295-1: configured names that matched several local functions (every match configured).
    pub configured_ambiguous: Vec<(String, usize)>,
    /// R1298-1 (b): exposed owning parameters whose inbound wrapper cannot be placed; each
    /// keeps its raw formal (`<parameter>\t<reason>` from the Box-parameter receipts).
    pub inbound_wrapper_unplaceable: Vec<String>,
}

impl BoReceipt {
    pub fn summary(&self) -> String {
        format!(
            "outcome={} status={} analysis_fingerprint={} files_changed={}/{} verify_rounds={} reverted={} input_tree_sha256={} emitted_tree_sha256={} configured_unmatched={} configured_ambiguous={} inbound_wrapper_unplaceable={} solve={}",
            self.outcome,
            self.status,
            self.analysis_fingerprint,
            self.files_changed,
            self.files_total,
            self.verify_rounds,
            self.reverted_count,
            self.input_tree_sha256,
            self.emitted_tree_sha256,
            self.configured_unmatched.len(),
            self.configured_ambiguous.len(),
            self.inbound_wrapper_unplaceable.len(),
            self.solve,
        )
    }

    pub fn render(&self) -> String {
        let mut out = format!("{}\n{}", self.summary(), self.file_rows);
        if !self.file_rows.ends_with('\n') {
            out.push('\n');
        }
        out.push_str(&format!(
            "configured-unmatched: {}\t{}\n",
            self.configured_unmatched.len(),
            self.configured_unmatched.join(" ")
        ));
        out.push_str(&format!(
            "configured-ambiguous: {}\t{}\n",
            self.configured_ambiguous.len(),
            self.configured_ambiguous
                .iter()
                .map(|(name, matches)| format!("{name}:{matches}"))
                .collect::<Vec<_>>()
                .join(" ")
        ));
        out.push_str(&format!(
            "inbound-wrapper-unplaceable: {}\t{}\n",
            self.inbound_wrapper_unplaceable.len(),
            self.inbound_wrapper_unplaceable.join(" ")
        ));
        out
    }
}

/// The Box-parameter receipts' `held` rows whose reason is `inbound-wrapper-unplaceable`.
pub(crate) fn inbound_wrapper_unplaceable(box_param_receipts: &str) -> Vec<String> {
    box_param_receipts
        .lines()
        .filter_map(|line| {
            let mut cells = line.split('\t');
            let (parameter, kind, detail) = (cells.next()?, cells.next()?, cells.next()?);
            (kind == "held" && detail.starts_with("inbound-wrapper-unplaceable"))
                .then(|| parameter.to_owned())
        })
        .collect()
}

/// Sets every `export KEY=VALUE` line of a frame env file that is not already set in the
/// process environment. Host-local names are skipped, so are values that expand a variable;
/// an inline comment after the value is ignored.
pub fn env_from_file(path: &Path) -> Result<usize, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|error| format!("read {}: {error}", path.display()))?;
    let mut set = 0;
    for line in text.lines() {
        let Some(rest) = line.trim().strip_prefix("export ") else {
            continue;
        };
        let Some((key, value)) = rest.split_once('=') else {
            continue;
        };
        let key = key.trim();
        if matches!(
            key,
            "SYSROOT" | "LD_LIBRARY_PATH" | "RUSTUP_TOOLCHAIN" | "TMPDIR"
        ) {
            continue;
        }
        let value = value
            .split_whitespace()
            .next()
            .unwrap_or("")
            .trim_matches('"');
        if value.is_empty() || value.starts_with('#') || value.contains('$') {
            continue;
        }
        if std::env::var_os(key).is_none() {
            // Safety: called on the driver's main thread before the analysis starts any
            // thread; nothing else reads the environment concurrently.
            unsafe { std::env::set_var(key, value) };
            set += 1;
        }
    }
    Ok(set)
}

/// Runs the emission path of record on the crate whose root file is `input` and writes the
/// emitted files over the program's own tree.
pub fn rewrite_bo(
    input: &Path,
    c_exposed_fns: impl IntoIterator<Item = String>,
) -> Result<BoReceipt, String> {
    // The per-program worker pinned both seeds before its first z3 call; the driver states the
    // pin rather than relying on the library's default.
    z3::set_global_param("smt.random_seed", "0");
    z3::set_global_param("sat.random_seed", "0");

    // The cache directory, read and written; no directory, no cache. One environment read at
    // the pass boundary until the driver passes `--pointer-cache-dir` (S3).
    model_cache::configure(
        std::env::var_os("CRAT_BO_CACHE_DIR")
            .filter(|dir| !dir.is_empty())
            .map(PathBuf::from),
    );
    let analysis_fingerprint = model_cache::current_analysis_digest();

    let configured_exposure =
        ConfiguredExposureInput::from_names("configured-c-exposed-fns", c_exposed_fns)
            .map_err(|failure| format!("exposed function names: {failure:?}"))?;
    let run_config = EmissionRunConfig {
        configured_exposure,
    };
    let capture = bo_rewriter::diagnose_raw_boundary_census_with_config(input, &run_config)?;
    persist_in_place(input, &capture, analysis_fingerprint)
}

fn rust_files(root: &Path) -> Result<Vec<PathBuf>, String> {
    fn visit(root: &Path, directory: &Path, output: &mut Vec<PathBuf>) -> Result<(), String> {
        let mut entries = std::fs::read_dir(directory)
            .map_err(|error| format!("read {}: {error}", directory.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("read {} entry: {error}", directory.display()))?;
        entries.sort_by_key(std::fs::DirEntry::file_name);
        for entry in entries {
            let file_type = entry
                .file_type()
                .map_err(|error| format!("stat {}: {error}", entry.path().display()))?;
            if file_type.is_dir() {
                visit(root, &entry.path(), output)?;
            } else if file_type.is_file()
                && entry
                    .path()
                    .extension()
                    .is_some_and(|extension| extension == "rs")
            {
                output.push(
                    entry
                        .path()
                        .strip_prefix(root)
                        .map_err(|error| {
                            format!(
                                "{} is outside {}: {error}",
                                entry.path().display(),
                                root.display()
                            )
                        })?
                        .to_path_buf(),
                );
            }
        }
        Ok(())
    }

    let mut files = Vec::new();
    visit(root, root, &mut files)?;
    files.sort();
    Ok(files)
}

fn tree_digest(files: &[(PathBuf, Vec<u8>)]) -> String {
    let mut hash = Sha256::new();
    for (path, bytes) in files {
        let path = path.to_string_lossy();
        hash.update((path.len() as u64).to_le_bytes());
        hash.update(path.as_bytes());
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
    format!("{:x}", hash.finalize())
}

fn emitted_relative_path(program_root: &Path, key: &FileKey) -> Result<PathBuf, String> {
    let FileKey::Real(path) = key else {
        return Err("virtual emitted file in a file-backed run".to_owned());
    };
    if let Ok(relative) = path.strip_prefix(program_root) {
        return Ok(relative.to_path_buf());
    }
    let root = program_root
        .canonicalize()
        .map_err(|error| format!("canonicalize {}: {error}", program_root.display()))?;
    let canonical_path = path
        .canonicalize()
        .map_err(|error| format!("canonicalize {}: {error}", path.display()))?;
    canonical_path
        .strip_prefix(&root)
        .map(Path::to_path_buf)
        .map_err(|error| {
            format!(
                "emitted file {} is outside program root {}: {error}",
                path.display(),
                program_root.display()
            )
        })
}

fn persist_in_place(
    input: &Path,
    capture: &E1Capture,
    analysis_fingerprint: String,
) -> Result<BoReceipt, String> {
    let program_root = input
        .parent()
        .ok_or_else(|| format!("{} has no program root", input.display()))?;
    let relative_files = rust_files(program_root)?;
    let input_files = relative_files
        .iter()
        .map(|relative| {
            std::fs::read(program_root.join(relative))
                .map(|bytes| (relative.clone(), bytes))
                .map_err(|error| format!("read {}: {error}", program_root.join(relative).display()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let input_tree_sha256 = tree_digest(&input_files);
    let outcome = capture.outcome_kind.key();
    let solve = format!("{:?}", capture.solve_receipt);
    let header = "file\tinput_sha256\temitted_sha256\tstate\n";
    let Some(files) = capture.emitted_files.as_ref() else {
        return Ok(BoReceipt {
            outcome,
            status: "absent-degraded",
            analysis_fingerprint,
            emitted_tree_sha256: input_tree_sha256.clone(),
            input_tree_sha256,
            files_changed: 0,
            files_total: relative_files.len(),
            verify_rounds: capture.verify_rounds,
            reverted_count: capture.reverted_count,
            solve,
            file_rows: header.to_owned(),
            configured_unmatched: capture.raw_boundary_artifacts.configured_unmatched.clone(),
            configured_ambiguous: capture.raw_boundary_artifacts.configured_ambiguous.clone(),
            inbound_wrapper_unplaceable: inbound_wrapper_unplaceable(
                &capture.raw_boundary_artifacts.box_param_receipts,
            ),
        });
    };

    let mut overlays = BTreeMap::new();
    for (key, text) in files {
        let relative = emitted_relative_path(program_root, key)?;
        if overlays
            .insert(relative.clone(), text.as_bytes().to_vec())
            .is_some()
        {
            return Err(format!("duplicate emitted file {}", relative.display()));
        }
    }
    let mut emitted_files = Vec::new();
    let mut file_rows = header.to_owned();
    let mut files_changed = 0;
    for (relative, input_bytes) in &input_files {
        let emitted_bytes = overlays
            .remove(relative)
            .unwrap_or_else(|| input_bytes.clone());
        let state = if &emitted_bytes == input_bytes {
            "byte-identical"
        } else {
            let output_path = program_root.join(relative);
            std::fs::write(&output_path, &emitted_bytes)
                .map_err(|error| format!("write {}: {error}", output_path.display()))?;
            files_changed += 1;
            "changed"
        };
        file_rows.push_str(&format!(
            "{}\t{:x}\t{:x}\t{}\n",
            relative.display(),
            Sha256::digest(input_bytes),
            Sha256::digest(&emitted_bytes),
            state,
        ));
        emitted_files.push((relative.clone(), emitted_bytes));
    }
    if !overlays.is_empty() {
        return Err(format!(
            "emitted map contains files absent from the input tree: {:?}",
            overlays.keys().collect::<Vec<_>>()
        ));
    }
    let emitted_tree_sha256 = tree_digest(&emitted_files);
    Ok(BoReceipt {
        outcome,
        status: "present",
        analysis_fingerprint,
        input_tree_sha256,
        emitted_tree_sha256,
        files_changed,
        files_total: relative_files.len(),
        verify_rounds: capture.verify_rounds,
        reverted_count: capture.reverted_count,
        solve,
        file_rows,
        configured_unmatched: capture.raw_boundary_artifacts.configured_unmatched.clone(),
        configured_ambiguous: capture.raw_boundary_artifacts.configured_ambiguous.clone(),
        inbound_wrapper_unplaceable: inbound_wrapper_unplaceable(
            &capture.raw_boundary_artifacts.box_param_receipts,
        ),
    })
}
