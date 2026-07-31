//! **Phase 4 — verify.** Gates on the emitted crate.
//!
//! Hard gate: the emitted crate type-checks. Structural gates: decision
//! coverage (`|decisions| == |subjects|`) and apply-time rollbacks == 0.
//! Behavioral gate: the designed harness on the applicable subset (S4).
//!
//! # E1 state visibility
//!
//! Gates on the EMITTED crate and on values the earlier phases handed over. It
//! does not re-consult an analysis: a gate that asked the same analysis that
//! produced the decision would agree with it by construction, which is not a
//! gate.

use std::{
    collections::BTreeMap,
    fs, io,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

use super::plan::FileKey;

/// Hard gate — the emitted crate passes `tcx.analysis(())`.
///
/// Runs a full compiler invocation over the emitted source. A type error is a
/// gate failure, not a panic to be caught: `run_compiler_on_str` surfaces a
/// `FatalError`, and the emitted crate failing to type-check is exactly the
/// condition this gate exists to report.
pub(crate) fn type_checks(emitted: &str) -> bool {
    ::utils::compilation::run_compiler_on_str(emitted, |tcx| {
        ::utils::type_check(tcx);
    })
    .is_ok()
}

/// The same hard gate, over a crate **rooted at a path**.
///
/// A multi-file crate cannot be handed to the string gate: its modules resolve
/// relative to the root's directory, so the crate only exists as a tree. This is
/// the general form; the string gate is its single-file case.
///
/// The gate stays **whole-crate** here by ruling — per-function granularity is
/// S2b.1's business, after the measurement that chooses its mechanism.
#[allow(
    dead_code,
    reason = "no NON-TEST consumer until 0a.3 routes `rewrite_m1` through the \
              path-based flow; the string gate is still the live one. Targeted \
              on the entry points rather than module-wide so the lint stays \
              active over everything reachable from them — `TempCrate`, \
              `copy_tree` and the counter are seeded live through these two. If \
              0a.3 lands and this is still needed, CORRECT the reason rather \
              than leaving it: this crate already carries one EXPIRY-CORRECTED \
              note from a dated promise that came due and did not settle."
)]
pub(crate) fn type_checks_crate(root: &Path) -> bool {
    ::utils::compilation::run_compiler_on_path(root, |tcx| {
        ::utils::type_check(tcx);
    })
    .is_ok()
}

static NEXT_TEMP: AtomicUsize = AtomicUsize::new(0);

/// A rewritten copy of a crate, on disk, deleted when dropped.
///
/// # Why a copy
///
/// The gate needs a crate it can compile, and the tree it must not modify is the
/// input — for the evaluation corpus, a **frozen** tree whose digest is a
/// standing invariant. Verifying in place would make the gate destructive of the
/// very thing it measures.
pub(crate) struct TempCrate {
    dir: PathBuf,
    root: PathBuf,
}

impl TempCrate {
    /// The crate root inside the copy — hand this to [`type_checks_crate`].
    pub(crate) fn root(&self) -> &Path {
        &self.root
    }
}

impl Drop for TempCrate {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.dir);
    }
}

fn copy_tree(from: &Path, to: &Path) -> io::Result<()> {
    fs::create_dir_all(to)?;
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let target = to.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_tree(&entry.path(), &target)?;
        } else {
            fs::copy(entry.path(), &target)?;
        }
    }
    Ok(())
}

/// Copy the crate rooted at `original_root`, then write the rewritten files into
/// **the copy**. The original tree is never opened for writing.
#[allow(
    dead_code,
    reason = "no NON-TEST consumer until 0a.3 routes `rewrite_m1` through the \
              path-based flow; the string gate is still the live one. Targeted \
              on the entry points rather than module-wide so the lint stays \
              active over everything reachable from them — `TempCrate`, \
              `copy_tree` and the counter are seeded live through these two. If \
              0a.3 lands and this is still needed, CORRECT the reason rather \
              than leaving it: this crate already carries one EXPIRY-CORRECTED \
              note from a dated promise that came due and did not settle."
)]
pub(crate) fn materialize(
    original_root: &Path,
    files: &BTreeMap<FileKey, String>,
) -> io::Result<TempCrate> {
    let crate_dir = original_root.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "crate root has no parent directory",
        )
    })?;
    let sequence = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("crat-verify-{}-{sequence}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    copy_tree(crate_dir, &dir)?;

    for (key, text) in files {
        let FileKey::Real(path) = key else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("cannot materialize a virtual file into a crate tree: {key:?}"),
            ));
        };
        let relative = path.strip_prefix(crate_dir).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("rewritten file {path:?} is outside the crate directory {crate_dir:?}"),
            )
        })?;
        fs::write(dir.join(relative), text)?;
    }

    let root_name = original_root.file_name().ok_or_else(|| {
        io::Error::new(io::ErrorKind::InvalidInput, "crate root has no file name")
    })?;
    let root = dir.join(root_name);
    Ok(TempCrate { dir, root })
}
