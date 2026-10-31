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

/// Relay main/388 O2 (R1386-1, the user's word): `--bo-query-timeout <SECS>`'s value as the
/// milliseconds `CRAT_BO_QUERY_TIMEOUT_MS` carries -- 1 to 4,294,967 s, so `SECS x 1000` fits a `u32`.
/// The driver sets the variable before [`env_from_file`] runs, which never overwrites a set variable,
/// so the flag outranks the variable, which outranks the `--bo-env` file, which outranks 600 s.
pub fn query_timeout_env_value(secs: u32) -> Result<String, String> {
    if secs == 0 {
        return Err("--bo-query-timeout must be at least 1 second".to_owned());
    }
    secs.checked_mul(1000)
        .map(|ms| ms.to_string())
        .ok_or_else(|| {
            format!(
                "--bo-query-timeout {secs} exceeds {} seconds (the budget is u32 milliseconds)",
                u32::MAX / 1000
            )
        })
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
///
/// **R1305-1 (relay main/367): `CRAT_BO_ARTIFACT_DIR=<dir>`** makes the pass also write its
/// per-subject rows and receipt strings there ([`write_artifacts`]). Read once, here, at the
/// pass boundary; unset or empty, nothing is written.
pub fn rewrite_bo(
    input: &Path,
    c_exposed_fns: impl IntoIterator<Item = String>,
) -> Result<BoReceipt, String> {
    let artifact_dir = std::env::var_os("CRAT_BO_ARTIFACT_DIR")
        .filter(|dir| !dir.is_empty())
        .map(PathBuf::from);
    rewrite_bo_with_artifacts(input, c_exposed_fns, artifact_dir.as_deref())
}

/// [`rewrite_bo`] with the artifact directory passed in rather than read from the environment.
/// The files are written after the tree is persisted, from the capture alone: they never decide
/// anything, and a failure to write them is reported on stderr, never returned.
pub(crate) fn rewrite_bo_with_artifacts(
    input: &Path,
    c_exposed_fns: impl IntoIterator<Item = String>,
    artifact_dir: Option<&Path>,
) -> Result<BoReceipt, String> {
    // The per-program worker pinned both seeds before its first z3 call; the driver states the
    // pin rather than relying on the library's default.
    crate::phase_log::begin();
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
        analysis_budget: crate::analysis_budget::Budget::from_env()?,
    };
    let capture = match bo_rewriter::diagnose_raw_boundary_census_with_config(input, &run_config) {
        Ok(capture) => capture,
        // Relay main/375 §3: the analysis budget ended the solve. The program is degraded with
        // the typed reason and the tree is left as the input; the pass succeeds, so the chain's
        // later arms run.
        Err(error) => match crate::analysis_budget::reason_in(&error) {
            Some(reason) => {
                eprintln!("pointer: degraded: {reason}");
                return budget_receipt(input, reason, analysis_fingerprint);
            }
            None => return Err(error),
        },
    };
    crate::phase_log::mark("census", "end", "");
    let receipt = persist_in_place(input, &capture, analysis_fingerprint)?;
    crate::phase_log::mark("persist", "end", "");
    declare_bytemuck(input, &capture);
    if let Some(dir) = artifact_dir
        && let Err(error) = write_artifacts(dir, input, &capture)
    {
        eprintln!(
            "pointer: artifacts not written to {}: {error}",
            dir.display()
        );
    }
    Ok(receipt)
}

/// **R1313-2 (relay main/371 step 2) — the byte view's dependency.** A tree the byte view reaches
/// names `bytemuck`; its crate declares it as the lab's passes do (`bytemuck = "1.24.0"`, the
/// version `deps_crate` carries), unless it already does. The manifest is the input's own directory's
/// or its parent's (`<crate>/lib.rs`, `<crate>/src/lib.rs`), and only one with a `[dependencies]`
/// table is edited; anything else (a bare file, as in the unit fixtures) is left as it is.
fn declare_bytemuck(input: &Path, capture: &E1Capture) {
    let Some(files) = capture.emitted_files.as_ref() else {
        return;
    };
    if !files.values().any(|text| text.contains("bytemuck::")) {
        return;
    }
    let Some(root) = input
        .ancestors()
        .skip(1)
        .take(2)
        .find(|dir| dir.join("Cargo.toml").is_file())
    else {
        return;
    };
    let declares_dependencies = std::fs::read_to_string(root.join("Cargo.toml"))
        .is_ok_and(|text| text.lines().any(|line| line.trim() == "[dependencies]"));
    if declares_dependencies && !utils::has_dependency(root, "bytemuck") {
        utils::add_dependency(root, "bytemuck", "1.24.0");
    }
}

/// **R1305-1 (relay main/367) — the per-subject writer.** Writes into `dir`, from the capture
/// the pass already holds and nothing else:
/// - `subjects.tsv`: the census subject seed (`subject_receipt`: one row per decided subject
///   plus the universe's excluded ones, with the model kind, the decision and its first
///   failing reason), joined by `subject_key` to the subject facts (name, owner kind,
///   fatness, mutability, raw-only operations, pointer comparison, null initializer), with
///   the program and two columns derived here: `outcome` (`delivered` / `reverted` / `held`
///   / `excluded`) and `first_hold_reason`;
/// - `reverted.tsv`: the verify loop's revert diagnostics (function, site, attribution, the
///   diagnostic's first line); `final_reverts.tsv`: its reverted classes, verbatim;
/// - the receipt strings verbatim, one file each.
///
/// `outcome`: an excluded subject is `excluded`; one the plan did not place is `held`; a
/// placed one is `reverted` when the outcome's final degradations take it back after a
/// failed verify (or the whole program degraded), `held` when they hold it for another
/// reason, else `delivered`.
fn write_artifacts(dir: &Path, input: &Path, capture: &E1Capture) -> Result<(), String> {
    std::fs::create_dir_all(dir).map_err(|error| format!("create {}: {error}", dir.display()))?;
    let write = |name: &str, text: &str| {
        std::fs::write(dir.join(name), text)
            .map_err(|error| format!("write {}: {error}", dir.join(name).display()))
    };
    let program = input
        .parent()
        .and_then(Path::file_name)
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| "-".to_owned());
    let clean = |text: &str| text.replace(['\t', '\r', '\n'], " ");

    let mut facts_lines = capture.raw_boundary_artifacts.subject_facts.lines();
    let facts_header = facts_lines.next().unwrap_or("subject_key");
    let facts_width = facts_header.split('\t').count().saturating_sub(1);
    let facts = facts_lines
        .filter_map(|line| line.split_once('\t'))
        .collect::<BTreeMap<_, _>>();
    let final_degradations = capture
        .final_degradations
        .iter()
        .map(|d| (d.subject.as_str(), d))
        .collect::<BTreeMap<_, _>>();
    let degraded_program = matches!(
        capture.outcome_kind,
        bo_rewriter::CensusOutcomeKind::Degraded
    );

    let mut seed = capture.subject_receipt.lines();
    let seed_header = seed.next().unwrap_or_default();
    let columns = seed_header.split('\t').collect::<Vec<_>>();
    let column = |name: &str| columns.iter().position(|c| *c == name);
    let (Some(key_at), Some(decision_at), Some(reason_at), Some(placed_at), Some(exclusion_at)) = (
        column("subject_key"),
        column("decision"),
        column("reason"),
        column("placed"),
        column("exclusion"),
    ) else {
        return Err(format!(
            "subject receipt header lacks a column: {seed_header}"
        ));
    };
    let detail_at = column("reason_detail");
    // R1314-1 (relay main/372): the subjects premise P12 decides carry `premise:P12` in
    // their `reason_detail`, as their receipt row in `p12_receipts.tsv` does.
    let p12_subjects = capture
        .raw_boundary_artifacts
        .p12_receipts
        .lines()
        .filter(|line| !line.starts_with('#') && !line.starts_with("subject_key\t"))
        .filter_map(|line| line.split('\t').next())
        .collect::<std::collections::BTreeSet<_>>();
    let mut out = format!(
        "program\t{seed_header}\t{}\toutcome\tfirst_hold_reason\n",
        facts_header.split_once('\t').map_or("", |(_, rest)| rest)
    );
    for line in seed {
        let marked;
        let mut cells = line.split('\t').collect::<Vec<_>>();
        if let Some(at) = detail_at
            && cells
                .get(key_at)
                .is_some_and(|key| p12_subjects.contains(key))
            && at < cells.len()
        {
            marked = match cells[at] {
                "-" => "premise:P12".to_owned(),
                detail => format!("{detail};premise:P12"),
            };
            cells[at] = &marked;
        }
        let line = cells.join("\t");
        let line = line.as_str();
        let cell = |at: usize| cells.get(at).copied().unwrap_or("-");
        let key = cell(key_at);
        let (outcome, reason) = if cell(decision_at) == "excluded" {
            ("excluded", cell(exclusion_at).to_owned())
        } else if cell(placed_at) != "1" {
            let reason = if cell(decision_at) == "degraded" {
                match detail_at.map(cell).filter(|d| *d != "-") {
                    Some(detail) => format!("{}:{detail}", cell(reason_at)),
                    None => cell(reason_at).to_owned(),
                }
            } else if cell(exclusion_at) != "-" {
                cell(exclusion_at).to_owned()
            } else {
                "not-placed".to_owned()
            };
            ("held", reason)
        } else if let Some(degradation) = final_degradations.get(key) {
            let reason = degradation.reason.key().to_owned();
            if matches!(
                degradation.reason,
                bo_rewriter::decision::DegradeReason::RevertedAfterVerifyFailure
            ) {
                ("reverted", reason)
            } else {
                ("held", reason)
            }
        } else if degraded_program {
            ("reverted", "program-degraded".to_owned())
        } else {
            ("delivered", "-".to_owned())
        };
        let facts_cells = facts
            .get(key)
            .map(|rest| rest.to_string())
            .unwrap_or_else(|| vec!["-"; facts_width].join("\t"));
        out.push_str(&format!(
            "{program}\t{line}\t{facts_cells}\t{outcome}\t{}\n",
            clean(&reason)
        ));
    }
    write("subjects.tsv", &out)?;

    let mut reverted = String::from("function\tsite_kind\tattribution\tcode\tdiagnostic\n");
    for revert in &capture.reverts {
        reverted.push_str(&format!(
            "{}\t{:?}\t{}\t{}\t{}\n",
            clean(&revert.function),
            revert.site_kind,
            clean(&revert.attribution),
            revert.diagnostic.code.as_deref().unwrap_or("-"),
            clean(revert.diagnostic.message.lines().next().unwrap_or_default()),
        ));
    }
    write("reverted.tsv", &reverted)?;

    let receipts = &capture.raw_boundary_artifacts;
    for (name, text) in [
        ("final_reverts.tsv", &receipts.final_reverts),
        ("box_param_receipts.tsv", &receipts.box_param_receipts),
        (
            "return_certificate_receipts.tsv",
            &receipts.return_certificate_receipts,
        ),
        (
            "flexible_tail_receipts.tsv",
            &receipts.flexible_tail_receipts,
        ),
        (
            "counted_void_call_receipts.tsv",
            &receipts.counted_void_call_receipts,
        ),
        ("entry_window_receipts.tsv", &receipts.entry_window_receipts),
        ("settled_hold_receipts.tsv", &receipts.settled_hold_receipts),
        ("exposure.tsv", &receipts.exposure),
        ("class_collisions.tsv", &receipts.class_collisions),
        ("p12_receipts.tsv", &receipts.p12_receipts),
        ("byte_view_receipts.tsv", &receipts.byte_view_receipts),
        ("cast_strip_receipts.tsv", &receipts.cast_strip_receipts),
    ] {
        write(name, text)?;
    }

    // Last, so no file above depends on it: the raw-cause ledger, when it ran. One row
    // per slot the model settles not Ref, led by `subjects.tsv`'s own `program` and
    // `subject_key` so the two files join row for row on that pair (a ledger row's
    // function, MIR local and depth are a subject's `owner_fn`, `mir_local` and
    // `ptr_depth` less one; a slot that is no subject -- a temporary, a field -- has
    // `subject_key` `-`).
    if let Some(rows) = &capture.raw_boundary_artifacts.session_raw_cause_ledger {
        let subject_keys = match (column("owner_fn"), column("mir_local"), column("ptr_depth")) {
            (Some(owner_at), Some(local_at), Some(depth_at)) => capture
                .subject_receipt
                .lines()
                .skip(1)
                .filter_map(|line| {
                    let cells = line.split('\t').collect::<Vec<_>>();
                    if cells.get(decision_at) == Some(&"excluded") {
                        return None;
                    }
                    let depth = cells.get(depth_at)?.parse::<u8>().ok()?.checked_sub(1)?;
                    Some((
                        (
                            *cells.get(owner_at)?,
                            *cells.get(local_at)?,
                            depth.to_string(),
                        ),
                        *cells.get(key_at)?,
                    ))
                })
                .collect::<BTreeMap<_, _>>(),
            _ => {
                return Err(format!(
                    "subject receipt header lacks owner_fn / mir_local / ptr_depth: {seed_header}"
                ));
            }
        };
        let mut ledger = format!(
            "program\tsubject_key\t{}\n",
            crate::analyses::borrow_ownership::raw_cause::HEADER
                .split_once('\t')
                .map_or("", |(_, rest)| rest)
        );
        for row in rows {
            let mut cells = row.splitn(4, '\t');
            let (function, local, depth) = (
                cells.next().unwrap_or("-"),
                cells.next().unwrap_or("-"),
                cells.next().unwrap_or("-").to_owned(),
            );
            let subject_key = subject_keys
                .get(&(function, local, depth))
                .copied()
                .unwrap_or("-");
            ledger.push_str(&format!("{program}\t{subject_key}\t{row}\n"));
        }
        write("raw-cause-ledger.tsv", &ledger)?;
    } else {
        let _ = std::fs::remove_file(dir.join("raw-cause-ledger.tsv"));
    }
    Ok(())
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

/// Relay main/375 §3: the receipt of a program the analysis budget degraded -- nothing
/// written, `status=analysis-budget`, the verdict in `solve`.
fn budget_receipt(
    input: &Path,
    reason: &str,
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
    Ok(BoReceipt {
        outcome: "degraded",
        status: "analysis-budget",
        analysis_fingerprint,
        emitted_tree_sha256: input_tree_sha256.clone(),
        input_tree_sha256,
        files_changed: 0,
        files_total: relative_files.len(),
        verify_rounds: 0,
        reverted_count: 0,
        solve: format!("AnalysisBudget({reason:?})"),
        file_rows: "file\tinput_sha256\temitted_sha256\tstate\n".to_owned(),
        configured_unmatched: Vec::new(),
        configured_ambiguous: Vec::new(),
        inbound_wrapper_unplaceable: Vec::new(),
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

#[cfg(test)]
mod query_timeout_flag_tests {
    use super::*;

    /// Relay main/388 O2 (R1386-1, R3): the flag's seconds become the variable's milliseconds; 0 and
    /// a value whose milliseconds overflow a `u32` are refused.
    #[test]
    fn r1386_flag_seconds_become_the_millisecond_variable() {
        assert_eq!(query_timeout_env_value(1).as_deref(), Ok("1000"));
        assert_eq!(query_timeout_env_value(600).as_deref(), Ok("600000"));
        assert_eq!(
            query_timeout_env_value(4_294_967).as_deref(),
            Ok("4294967000")
        );
        assert!(query_timeout_env_value(0).is_err());
        assert!(query_timeout_env_value(4_294_968).is_err());
    }

    /// Relay main/388 O2 (R1386-1): a variable already set -- the flag's, or the caller's -- outranks
    /// the `--bo-env` file, which sets it only when unset. A variable of this test's own is used, so
    /// the process's `CRAT_BO_QUERY_TIMEOUT_MS` (read once by the solver) is never touched.
    #[test]
    fn r1386_a_set_variable_outranks_the_bo_env_file() {
        const KEY: &str = "CRAT_BO_R1386_PRECEDENCE_TEST";
        let file = std::env::temp_dir().join(format!("r1386-precedence-{}.sh", std::process::id()));
        std::fs::write(&file, format!("export {KEY}=from-file\n")).unwrap();
        // Safety: a variable no other code or test reads; set and removed on this test's thread.
        unsafe { std::env::set_var(KEY, "from-flag") };
        env_from_file(&file).unwrap();
        assert_eq!(
            std::env::var(KEY).as_deref(),
            Ok("from-flag"),
            "the set variable wins"
        );
        // Safety: as above.
        unsafe { std::env::remove_var(KEY) };
        env_from_file(&file).unwrap();
        assert_eq!(
            std::env::var(KEY).as_deref(),
            Ok("from-file"),
            "unset, the file sets it"
        );
        // Safety: as above.
        unsafe { std::env::remove_var(KEY) };
        let _ = std::fs::remove_file(&file);
    }
}

#[cfg(test)]
mod artifact_tests {
    //! **R1305-1 (relay main/367) — the per-subject writer's witnesses.** The writer reads the
    //! capture and decides nothing: unset, it writes no file; set, it writes its files and the
    //! emitted tree is byte-identical to the unset run's.

    use std::path::{Path, PathBuf};

    const FIXTURE: &str = "#![allow(dead_code, unused_mut, unused_unsafe, unused_assignments)]
pub unsafe fn get(mut p: *mut i32) -> i32 { *p }
pub unsafe fn sum(mut v: *const i32, mut n: usize) -> i32 {
    let mut s = 0;
    let mut i = 0;
    while i < n { s += *v.offset(i as isize); i += 1; }
    s
}
pub unsafe fn addr(mut p: *mut i32) -> usize { p as usize }
pub unsafe fn caller() -> i32 {
    let mut x = [1, 2, 3];
    let mut y = 5;
    get(&mut y) + sum(x.as_ptr(), 3) + addr(&mut y) as i32
}
";

    fn fixture(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("crat-r1305-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("lib.rs"), FIXTURE).unwrap();
        dir
    }

    fn files(dir: &Path) -> Vec<String> {
        let mut names = std::fs::read_dir(dir)
            .map(|entries| {
                entries
                    .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        names.sort();
        names
    }

    #[test]
    fn r1305_1_unset_writes_nothing_set_writes_the_files_and_the_tree_is_identical() {
        let (unset, set) = (fixture("unset"), fixture("set"));
        let artifacts = set.join("artifacts");
        let a = super::rewrite_bo_with_artifacts(&unset.join("lib.rs"), [], None).unwrap();
        let b =
            super::rewrite_bo_with_artifacts(&set.join("lib.rs"), [], Some(&artifacts)).unwrap();
        assert_eq!(
            files(&unset),
            ["lib.rs"],
            "unset: nothing beside the program"
        );
        assert_eq!(
            std::fs::read(unset.join("lib.rs")).unwrap(),
            std::fs::read(set.join("lib.rs")).unwrap(),
            "the emitted tree is byte-identical with and without the writer"
        );
        assert_eq!(a.emitted_tree_sha256, b.emitted_tree_sha256);
        assert_ne!(
            a.emitted_tree_sha256, a.input_tree_sha256,
            "the fixture is edited"
        );
        let written = files(&artifacts);
        for name in [
            "subjects.tsv",
            "reverted.tsv",
            "final_reverts.tsv",
            "box_param_receipts.tsv",
            "return_certificate_receipts.tsv",
            "flexible_tail_receipts.tsv",
            "counted_void_call_receipts.tsv",
            "entry_window_receipts.tsv",
            "settled_hold_receipts.tsv",
            "exposure.tsv",
        ] {
            assert!(
                written.iter().any(|w| w == name),
                "{name} missing from {written:?}"
            );
        }
        let _ = std::fs::remove_dir_all(&unset);
        let _ = std::fs::remove_dir_all(&set);
    }

    /// Relay main/375 §3: the session's error read back as the budget's verdict, and the
    /// receipt of the program it degraded -- nothing written, the input's tree.
    #[test]
    fn r375_a_budget_error_is_a_degraded_receipt_with_the_input_tree() {
        let error = "E1 capture has no observed root: degraded: analysis budget (0 s, 0.1 GB, bc:source_events)";
        let reason = crate::analysis_budget::reason_in(error).unwrap();
        assert_eq!(reason, "analysis budget (0 s, 0.1 GB, bc:source_events)");
        assert!(crate::analysis_budget::reason_in("BO declined — no accepted model").is_none());
        let root = fixture("budget");
        let before = std::fs::read(root.join("lib.rs")).unwrap();
        let receipt = super::budget_receipt(&root.join("lib.rs"), reason, "fp".to_owned()).unwrap();
        assert_eq!(
            (receipt.outcome, receipt.status),
            ("degraded", "analysis-budget")
        );
        assert_eq!(receipt.input_tree_sha256, receipt.emitted_tree_sha256);
        assert_eq!(receipt.files_changed, 0);
        assert!(
            receipt
                .summary()
                .contains("solve=AnalysisBudget(\"analysis budget (0 s")
        );
        assert_eq!(std::fs::read(root.join("lib.rs")).unwrap(), before);
    }

    #[test]
    fn r1305_1_subjects_tsv_has_one_row_per_table_entry_each_with_a_model_kind() {
        let root = fixture("rows");
        let artifacts = root.join("artifacts");
        let config = crate::bo_rewriter::EmissionRunConfig {
            configured_exposure:
                crate::bo_rewriter::decision::exposure::ConfiguredExposureInput::from_names(
                    "configured-c-exposed-fns",
                    std::iter::empty::<String>(),
                )
                .unwrap(),
            analysis_budget: crate::analysis_budget::Budget::default(),
        };
        // The table the pass decides, from the program before it is rewritten in place.
        let entries = ::utils::compilation::run_compiler_on_path(&root.join("lib.rs"), |tcx| {
            crate::bo_rewriter::decide_table_with_emission_config(tcx, None, &config)
                .map(|(table, _)| table.entries.len())
        })
        .unwrap()
        .unwrap();
        super::rewrite_bo_with_artifacts(&root.join("lib.rs"), [], Some(&artifacts)).unwrap();
        let text = std::fs::read_to_string(artifacts.join("subjects.tsv")).unwrap();
        let mut lines = text.lines();
        let header = lines.next().unwrap().split('\t').collect::<Vec<_>>();
        let column = |name: &str| header.iter().position(|h| *h == name).unwrap();
        let (kind, decision, outcome) =
            (column("model_kind"), column("decision"), column("outcome"));
        let rows = lines
            .map(|l| l.split('\t').collect::<Vec<_>>())
            .collect::<Vec<_>>();
        assert!(rows.iter().all(|r| r.len() == header.len()), "{text}");
        assert_eq!(
            rows.iter().filter(|r| r[decision] != "excluded").count(),
            entries,
            "{text}"
        );
        assert!(entries >= 2, "the fixture's subjects: {text}");
        assert!(
            rows.iter()
                .all(|r| ["raw", "ref", "owning", "unmodeled"].contains(&r[kind])),
            "{text}"
        );
        assert!(
            rows.iter()
                .all(|r| ["delivered", "reverted", "held", "excluded"].contains(&r[outcome])),
            "{text}"
        );
        assert!(rows.iter().any(|r| r[outcome] == "delivered"), "{text}");
        assert!(rows.iter().any(|r| r[outcome] == "held"), "{text}");
        let _ = std::fs::remove_dir_all(&root);
    }

    /// The ledger witness's fixture: a callee dropping a `Box::from_raw` (a release
    /// whose objects are unknown, so it excludes Ref at its caller's by-reference
    /// formal), a raw cast, and the writer fixture's lend.
    const LEDGER_FIXTURE: &str =
        "#![allow(dead_code, unused_mut, unused_unsafe, unused_assignments)]
pub unsafe fn leaf(mut out: *mut u8, mut p: *mut u8) {
    *out = *p;
    let _b: Box<u8> = Box::from_raw(p);
}
pub unsafe fn mid(mut ctx: *const u8, mut out: *mut u8) { leaf(out, Box::into_raw(Box::new(*ctx))); }
pub unsafe fn get(mut p: *mut i32) -> i32 { *p }
pub unsafe fn addr(mut p: *mut i32) -> usize { p as usize }
pub unsafe fn caller() -> i32 {
    let mut y = 5;
    let mut c = 3u8;
    let mut o = 0u8;
    mid(&mut c, &mut o);
    get(&mut y) + addr(&mut y) as i32 + o as i32
}
";

    /// The child of the ledger witness: the pass on `CRAT_E5C_LEDGER_TREE/lib.rs` with the
    /// writer beside it, and the receipt's stable fields (every field but the solve's wall).
    #[test]
    #[ignore = "a child of e5c_w67_g_the_ledger_leaves_the_tree_and_the_receipts_unchanged"]
    fn e5c_inner_ledger_tree() {
        let dir = PathBuf::from(std::env::var("CRAT_E5C_LEDGER_TREE").unwrap());
        let receipt =
            super::rewrite_bo_with_artifacts(&dir.join("lib.rs"), [], Some(&dir.join("artifacts")))
                .unwrap();
        let model = receipt
            .solve
            .split("model_sha256: \"")
            .nth(1)
            .and_then(|rest| rest.split('"').next())
            .unwrap_or("-")
            .to_owned();
        let stable = format!(
            "{} {} {} {} {} {}/{} {} {} {model}\n{}",
            receipt.outcome,
            receipt.status,
            receipt.analysis_fingerprint,
            receipt.input_tree_sha256,
            receipt.emitted_tree_sha256,
            receipt.files_changed,
            receipt.files_total,
            receipt.verify_rounds,
            receipt.reverted_count,
            receipt.file_rows,
        );
        std::fs::write(dir.join("receipt-stable.txt"), stable).unwrap();
    }

    /// W67g: the ledger observes and never decides. The pass with the ledger off and on:
    /// the emitted tree, the receipt (model digest included) and every file the writer
    /// writes are byte-identical; on, the writer adds `raw-cause-ledger.tsv`, whose rows
    /// join `subjects.tsv` on (`program`, `subject_key`): each Raw and each Owning subject
    /// has exactly one row, of its kind.
    #[test]
    fn e5c_w67_g_the_ledger_leaves_the_tree_and_the_receipts_unchanged() {
        // One path for both runs (the writer's `program` is the tree's directory and its
        // `site` column the file's path): each run's outputs are moved aside after it.
        let base = std::env::temp_dir().join(format!("crat-e5c-w67g-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        let dir = base.join("program");
        let run = |ledger: &str| -> PathBuf {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(dir.join("lib.rs"), LEDGER_FIXTURE).unwrap();
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "bo_pipeline::artifact_tests::e5c_inner_ledger_tree",
                    "--exact",
                    "--ignored",
                    "--nocapture",
                    "--test-threads=1",
                ])
                .env("CRAT_E5C_LEDGER_TREE", &dir)
                .env("CRAT_ERA5C_RAW_CAUSE_LEDGER", ledger)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let kept = base.join(ledger);
            std::fs::rename(&dir, &kept).unwrap();
            kept
        };
        let (off, on) = (run("off"), run("on"));
        let read = |dir: &Path, name: &str| std::fs::read(dir.join(name)).unwrap();
        assert_eq!(
            read(&off, "lib.rs"),
            read(&on, "lib.rs"),
            "the emitted tree"
        );
        assert_eq!(
            read(&off, "receipt-stable.txt"),
            read(&on, "receipt-stable.txt"),
            "the receipt"
        );
        let (off_files, on_files) = (files(&off.join("artifacts")), files(&on.join("artifacts")));
        assert!(
            !off_files.iter().any(|f| f == "raw-cause-ledger.tsv"),
            "{off_files:?}"
        );
        assert_eq!(
            on_files
                .iter()
                .filter(|f| *f != "raw-cause-ledger.tsv")
                .collect::<Vec<_>>(),
            off_files.iter().collect::<Vec<_>>()
        );
        for name in &off_files {
            assert_eq!(
                read(&off.join("artifacts"), name),
                read(&on.join("artifacts"), name),
                "{name}"
            );
        }
        let table = |name: &str| -> (Vec<String>, Vec<Vec<String>>) {
            let text = std::fs::read_to_string(on.join("artifacts").join(name)).unwrap();
            let mut lines = text.lines();
            let header = lines
                .next()
                .unwrap()
                .split('\t')
                .map(str::to_owned)
                .collect();
            let rows = lines
                .map(|l| l.split('\t').map(str::to_owned).collect())
                .collect();
            (header, rows)
        };
        let (subject_header, subjects) = table("subjects.tsv");
        let (ledger_header, ledger) = table("raw-cause-ledger.tsv");
        let at = |header: &[String], name: &str| header.iter().position(|h| h == name).unwrap();
        let (s_program, s_key, s_kind) = (
            at(&subject_header, "program"),
            at(&subject_header, "subject_key"),
            at(&subject_header, "model_kind"),
        );
        let (l_program, l_key, l_kind) = (
            at(&ledger_header, "program"),
            at(&ledger_header, "subject_key"),
            at(&ledger_header, "model_kind"),
        );
        assert!(ledger.iter().all(|r| r.len() == ledger_header.len()));
        let settled: Vec<_> = subjects
            .iter()
            .filter(|r| r[s_kind] == "raw" || r[s_kind] == "owning")
            .collect();
        assert!(
            settled.iter().any(|r| r[s_kind] == "raw")
                && settled.iter().any(|r| r[s_key].starts_with("mid::ctx")),
            "{subjects:?}"
        );
        for subject in settled {
            let joined: Vec<_> = ledger
                .iter()
                .filter(|r| r[l_program] == subject[s_program] && r[l_key] == subject[s_key])
                .collect();
            assert_eq!(joined.len(), 1, "{subject:?}: {ledger:?}");
            assert_eq!(joined[0][l_kind], subject[s_kind], "{subject:?}");
        }
        let _ = std::fs::remove_dir_all(&base);
    }
}
