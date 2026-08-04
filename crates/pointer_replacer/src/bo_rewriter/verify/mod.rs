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
    // Routed through `diagnose_crate` so there is ONE diagnostic path. A gate
    // that counted errors differently from the loop that attributes them would
    // be two sources of truth about the same compile.
    diagnose_crate(root).errors == 0
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
    #[allow(
        dead_code,
        reason = "same expiry as `materialize`: reached only from witnesses \
                  until 0a.3 wires the path-based flow. Correct this reason \
                  when that lands rather than leaving it standing."
    )]
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

/// Stage a single-file crate from emitted text, so the whole-crate gate can run
/// on it. The virtual counterpart of [`materialize`].
#[allow(
    dead_code,
    reason = "same expiry as `materialize`: the string entry point's gate path. \
              Correct this reason when the rewriter is wired into the pipeline."
)]
pub(crate) fn materialize_single_file(source: &str) -> io::Result<TempCrate> {
    let sequence = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("crat-verify1-{}-{sequence}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir)?;
    let root = dir.join("lib.rs");
    fs::write(&root, source)?;
    Ok(TempCrate { dir, root })
}

// ---------------------------------------------------------------------------
// S2b.1.1 — STRUCTURAL diagnostic capture.
//
// Extracted from `DiagInner`, not from rendered text: eliminating the
// parse-failure class beats guarding it. A dropped diagnostic would lower the
// error count and fake progress for 1.2's no-progress detector, so the COUNT is
// derived from `Level` ALONE — an unrenderable message degrades the TEXT, never
// the COUNT.
//
// **FIXTURE-VALIDATED.** This path does NOT inherit the rendered parser's
// 86-diagnostic corpus credit; the cross-check against it runs at 1.4.
// ---------------------------------------------------------------------------

/// Which way a type error points — what distinguishes *whose* rewrite caused it.
/// Span containment alone cannot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Direction {
    /// `expected raw pointer, found reference` — a rewritten value flowing into
    /// an unrewritten context, so the CONTAINING function's own rewrite is the
    /// culprit and reverting it fixes the error.
    RewrittenIntoRaw,
    /// `expected reference, found raw pointer` — a rewritten CALLEE with an
    /// unrewritten caller. Reverting the containing function does NOT fix it.
    /// Measured once corpus-wide, on heman.
    RawIntoRewritten,
    Other,
}

fn classify(message: &str) -> Direction {
    let expects_raw = message.contains("expected raw pointer");
    let found_ref = message.contains("found reference") || message.contains("found `&");
    let expects_ref = message.contains("expected reference") || message.contains("expected `&");
    let found_raw = message.contains("found raw pointer");
    if expects_raw && found_ref {
        Direction::RewrittenIntoRaw
    } else if expects_ref && found_raw {
        Direction::RawIntoRewritten
    } else {
        Direction::Other
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Diag {
    pub file: String,
    pub line: usize,
    pub message: String,
    pub direction: Direction,
}

#[derive(Clone, Debug, Default)]
#[allow(
    dead_code,
    reason = "`diags` and `unrenderable` are read by S2b.1.2's revert loop, \
              which is the next slice; `errors` is live now through \
              `type_checks_crate`. Correct this reason when 1.2 lands rather \
              than leaving it standing."
)]
pub(crate) struct Diagnosis {
    /// Error-level diagnostics, counted from `Level` **alone**.
    pub errors: usize,
    /// Located diagnostics. **Fewer than `errors` in practice**: rustc emits a
    /// spanless error-level summary ("aborting due to N previous errors") that
    /// is counted and not located. Measured 2 vs 1 on the fixture below, which
    /// is what makes the count-independence witness able to fail.
    pub diags: Vec<Diag>,
    /// Counted diagnostics that carried no `Str` content. Loud rather than
    /// silent: the text degraded, the count did not.
    ///
    /// **Currently unexercised**: both probed error kinds (E0308 mismatch, E0425
    /// unresolved name) carry `Str` messages, so no fixture yet drives this
    /// above zero. Recorded as a fixture gap rather than given a witness that
    /// could not fail.
    pub unrenderable: usize,
}

struct Capture {
    diags: std::sync::Arc<std::sync::Mutex<Vec<Diag>>>,
    errors: std::sync::Arc<std::sync::Mutex<usize>>,
    unrenderable: std::sync::Arc<std::sync::Mutex<usize>>,
    source_map: std::sync::Arc<rustc_span::source_map::SourceMap>,
    /// **Measured unreached in this design** (setting it to `unimplemented!()`
    /// does not panic, because nothing here delegates to an inner emitter).
    /// Kept because the trait requires the method and a future emission path
    /// may call it — but deliberately NOT given a witness: no mutation of it
    /// can fail, so a witness would be a manufactured one. Stated control.
    translator: rustc_errors::translation::Translator,
    /// Forwards to stderr as the default emitter did.
    ///
    /// Installing `Capture` REPLACES the session's emitter, so without this the
    /// rendered diagnostics stop existing — the worker logs go silent and the
    /// rendered extraction path has nothing to validate against. Both paths must
    /// be live for the 1.4 validation transfer, and restoring stderr also
    /// restores the behaviour the corpus logs had before structural capture
    /// landed.
    inner: rustc_errors::emitter::HumanEmitter,
}

impl rustc_errors::emitter::Emitter for Capture {
    fn source_map(&self) -> Option<&rustc_span::source_map::SourceMap> {
        Some(&self.source_map)
    }

    fn translator(&self) -> &rustc_errors::translation::Translator {
        &self.translator
    }

    fn emit_diagnostic(
        &mut self,
        diag: rustc_errors::DiagInner,
        _registry: &rustc_errors::registry::Registry,
    ) {
        if !matches!(
            diag.level(),
            rustc_errors::Level::Fatal | rustc_errors::Level::Error
        ) {
            return;
        }
        // COUNT FIRST, from Level alone. Nothing below can reduce it.
        *self.errors.lock().unwrap() += 1;

        let mut message = String::new();
        for (msg, _) in &diag.messages {
            if let rustc_errors::DiagMessage::Str(text) = msg {
                message.push_str(text);
            }
        }
        for child in &diag.children {
            for (msg, _) in &child.messages {
                if let rustc_errors::DiagMessage::Str(text) = msg {
                    message.push(' ');
                    message.push_str(text);
                }
            }
        }
        if message.is_empty() {
            *self.unrenderable.lock().unwrap() += 1;
        }
        if let Some(span) = diag.span.primary_span() {
            let loc = self.source_map.lookup_char_pos(span.lo());
            let direction = classify(&message);
            self.diags.lock().unwrap().push(Diag {
                file: loc.file.name.prefer_local().to_string(),
                line: loc.line,
                message,
                direction,
            });
        }
        // Forward LAST: extraction borrows, rendering consumes.
        self.inner.emit_diagnostic(diag, _registry);
    }
}

/// Type-check the crate at `root` and return its error-level diagnostics.
pub(crate) fn diagnose_crate(root: &Path) -> Diagnosis {
    let diags = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let errors = std::sync::Arc::new(std::sync::Mutex::new(0usize));
    let unrenderable = std::sync::Arc::new(std::sync::Mutex::new(0usize));

    let mut config = ::utils::compilation::make_config(::utils::compilation::path_to_input(root));
    let (d, e, u) = (diags.clone(), errors.clone(), unrenderable.clone());
    config.psess_created = Some(Box::new(move |psess| {
        let source_map = psess.clone_source_map();
        let source_map2 = psess.clone_source_map();
        psess.dcx().set_emitter(Box::new(Capture {
            diags: d.clone(),
            errors: e.clone(),
            unrenderable: u.clone(),
            source_map,
            translator: rustc_driver::default_translator(),
            inner: rustc_errors::emitter::HumanEmitter::new(
                rustc_errors::emitter::stderr_destination(rustc_errors::ColorConfig::Never),
                rustc_driver::default_translator(),
            )
            .sm(Some(source_map2)),
        }));
    }));

    let ran = ::utils::compilation::run_compiler(config, |tcx| {
        ::utils::type_check(tcx);
    });
    let mut errors = *errors.lock().unwrap();
    // A fatal abort that emitted nothing still means the crate failed.
    if ran.is_err() && errors == 0 {
        errors = 1;
    }
    Diagnosis {
        errors,
        diags: diags.lock().unwrap().clone(),
        unrenderable: *unrenderable.lock().unwrap(),
    }
}
