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

/// One reachable MIR `Drop` terminator whose dropped local contains a Box.
///
/// Explicit `drop(value)` calls are not rows: they consume the value through a
/// call terminator. This ledger observes only compiler-inserted cleanup, which
/// is exactly the population that addendum 101 D4 requires to carry a retained
/// C-sink identity or an explicit waiver receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BoxMirDrop {
    pub(crate) function: String,
    pub(crate) local: u32,
    pub(crate) local_name: Option<String>,
    pub(crate) file: String,
    pub(crate) site: String,
    pub(crate) line: usize,
    pub(crate) cleanup: bool,
    pub(crate) optional: bool,
}

/// One production authorization for a compiler-inserted Box drop.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BoxMirDropAllowance {
    pub(crate) function: String,
    pub(crate) local_name: Option<String>,
    pub(crate) line: Option<usize>,
    pub(crate) cleanup: Option<bool>,
    pub(crate) site: Option<String>,
    pub(crate) reason: String,
}

/// The pre-emission authorization carried by one accepted Box plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BoxMirDropPolicy {
    pub(crate) subject: String,
    pub(crate) function: String,
    pub(crate) local_name: Option<String>,
    pub(crate) overwrite_sites: Vec<String>,
    pub(crate) retained_sink: bool,
    pub(crate) optional: bool,
    pub(crate) implicit_scope_close: bool,
}

fn box_container_kind(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    ty: rustc_middle::ty::Ty<'_>,
) -> Option<bool> {
    if ty.is_box() {
        return Some(false);
    }
    let rustc_middle::ty::TyKind::Adt(def, args) = ty.kind() else {
        return None;
    };
    if !tcx.is_diagnostic_item(rustc_span::sym::Option, def.did()) {
        return None;
    }
    args.types().any(|inner| inner.is_box()).then_some(true)
}

fn collect_box_mir_drops(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    functions: Option<&std::collections::BTreeSet<String>>,
) -> Vec<BoxMirDrop> {
    use rustc_middle::mir::{TerminatorKind, VarDebugInfoContents};

    let mut rows = Vec::new();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let rustc_hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        if !matches!(item.kind, rustc_hir::ItemKind::Fn { .. }) {
            continue;
        }
        let did = item.owner_id.def_id;
        let function = tcx.def_path_str(did.to_def_id());
        if functions.is_some_and(|functions| !functions.contains(&function)) {
            continue;
        }
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Drop { place, .. } = &data.terminator().kind else {
                continue;
            };
            let Some(optional) = box_container_kind(tcx, body.local_decls[place.local].ty) else {
                continue;
            };
            let names = body
                .var_debug_info
                .iter()
                .filter_map(|info| match info.value {
                    VarDebugInfoContents::Place(debug_place)
                        if debug_place.as_local() == Some(place.local) =>
                    {
                        Some(info.name.to_string())
                    }
                    _ => None,
                })
                .collect::<std::collections::BTreeSet<_>>();
            let span = data.terminator().source_info.span.source_callsite();
            let pos = tcx.sess.source_map().lookup_char_pos(span.lo());
            rows.push(BoxMirDrop {
                function: function.clone(),
                local: place.local.as_u32(),
                local_name: (names.len() == 1).then(|| names.iter().next().unwrap().clone()),
                file: pos.file.name.prefer_local().to_string(),
                site: tcx.sess.source_map().span_to_diagnostic_string(span),
                line: pos.line,
                cleanup: body.basic_blocks[block].is_cleanup,
                optional,
            });
        }
    }
    rows.sort_by(|left, right| {
        (
            left.function.as_str(),
            left.local,
            left.line,
            left.cleanup,
            left.site.as_str(),
        )
            .cmp(&(
                right.function.as_str(),
                right.local,
                right.line,
                right.cleanup,
                right.site.as_str(),
            ))
    });
    rows
}

/// Reconcile observations against the accepted Box plan and render the D4
/// receipt rows. The emitted sites themselves are exact; each overwrite row is
/// paired in lexical order with the plan's exact original-source overwrite
/// site, so the receipt carries both coordinate frames without asking a
/// whole-function AST line map to invent an interior offset.
pub(crate) fn reconcile_box_mir_drop_policies(
    drops: &[BoxMirDrop],
    policies: &[BoxMirDropPolicy],
) -> Result<String, String> {
    let mut grouped: std::collections::BTreeMap<usize, Vec<BoxMirDrop>> =
        std::collections::BTreeMap::new();
    for drop in drops {
        let candidates = policies
            .iter()
            .enumerate()
            .filter(|policy| {
                policy.1.function == drop.function && policy.1.local_name == drop.local_name
            })
            .collect::<Vec<_>>();
        let [(policy_index, _)] = candidates.as_slice() else {
            return Err(format!(
                "Box MIR Drop policy identity is ambiguous: function={} local={} name={} policies={}",
                drop.function,
                drop.local,
                drop.local_name.as_deref().unwrap_or("<unnamed>"),
                candidates.len(),
            ));
        };
        grouped.entry(*policy_index).or_default().push(drop.clone());
    }

    let mut allowances = Vec::new();
    let mut plan_sites =
        std::collections::BTreeMap::<(String, u32, usize, bool, String), String>::new();
    for (policy_index, policy) in policies.iter().enumerate() {
        let mut observed = grouped.remove(&policy_index).unwrap_or_default();
        observed.sort_by(|left, right| {
            (left.cleanup, left.line, left.site.as_str()).cmp(&(
                right.cleanup,
                right.line,
                right.site.as_str(),
            ))
        });
        let normal = observed
            .iter()
            .filter(|drop| !drop.cleanup)
            .cloned()
            .collect::<Vec<_>>();
        let terminal_close =
            usize::from(policy.implicit_scope_close || (policy.optional && policy.retained_sink));
        let expected_normal = policy.overwrite_sites.len() + terminal_close;
        if normal.len() != expected_normal {
            return Err(format!(
                "unreceipted Box MIR Drop population: subject={} function={} name={} expected_normal={} got_normal={} overwrites={} terminal_close={}",
                policy.subject,
                policy.function,
                policy.local_name.as_deref().unwrap_or("<unnamed>"),
                expected_normal,
                normal.len(),
                policy.overwrite_sites.len(),
                terminal_close,
            ));
        }
        for (index, drop) in normal.iter().enumerate() {
            let (reason, plan_site) = if let Some(site) = policy.overwrite_sites.get(index) {
                ("waiver-drop(overwrite)", site.clone())
            } else if policy.implicit_scope_close {
                ("waiver-drop(scope-exit)", "function-exit".to_owned())
            } else {
                (
                    "retained-c-sink(empty-option-close)",
                    "retained-c-sink".to_owned(),
                )
            };
            allowances.push(BoxMirDropAllowance {
                function: drop.function.clone(),
                local_name: drop.local_name.clone(),
                line: Some(drop.line),
                cleanup: Some(drop.cleanup),
                site: Some(drop.site.clone()),
                reason: reason.to_owned(),
            });
            plan_sites.insert(
                (
                    drop.function.clone(),
                    drop.local,
                    drop.line,
                    drop.cleanup,
                    drop.site.clone(),
                ),
                plan_site,
            );
        }
        for drop in observed.iter().filter(|drop| drop.cleanup) {
            allowances.push(BoxMirDropAllowance {
                function: drop.function.clone(),
                local_name: drop.local_name.clone(),
                line: Some(drop.line),
                cleanup: Some(drop.cleanup),
                site: Some(drop.site.clone()),
                reason: "waiver-drop(unwind)".to_owned(),
            });
            plan_sites.insert(
                (
                    drop.function.clone(),
                    drop.local,
                    drop.line,
                    drop.cleanup,
                    drop.site.clone(),
                ),
                "compiler-cleanup-edge".to_owned(),
            );
        }
    }
    debug_assert!(grouped.is_empty());
    let matched = reconcile_box_mir_drops(drops, &allowances)?;
    let mut output = String::from(
        "function\tlocal\tlocal_name\temitted_site\temitted_line\tcleanup\toptional\treceipt\tplan_site\n",
    );
    for (drop, receipt) in matched {
        let plan_site = plan_sites
            .get(&(
                drop.function.clone(),
                drop.local,
                drop.line,
                drop.cleanup,
                drop.site.clone(),
            ))
            .ok_or_else(|| "matched Box drop lost its plan-site receipt".to_owned())?;
        output.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            drop.function,
            drop.local,
            drop.local_name.as_deref().unwrap_or("<unnamed>"),
            drop.site.replace(['\t', '\r', '\n'], " "),
            drop.line,
            u8::from(drop.cleanup),
            u8::from(drop.optional),
            receipt,
            plan_site.replace(['\t', '\r', '\n'], " "),
        ));
    }
    Ok(output)
}

#[cfg(test)]
pub(crate) fn box_mir_drops_str(source: &str) -> Result<Vec<BoxMirDrop>, String> {
    ::utils::compilation::run_compiler_on_str(source, |tcx| collect_box_mir_drops(tcx, None))
        .map_err(|_| "emitted source failed before the Box MIR drop observer".to_owned())
}

#[allow(
    dead_code,
    reason = "Box wave-1's cfg(test) corpus worker is the first path consumer"
)]
pub(crate) fn box_mir_drops_path(
    root: &Path,
    policies: &[BoxMirDropPolicy],
) -> Result<Vec<BoxMirDrop>, String> {
    let functions = policies
        .iter()
        .map(|policy| policy.function.clone())
        .collect::<std::collections::BTreeSet<_>>();
    if functions.is_empty() {
        return Ok(Vec::new());
    }
    ::utils::compilation::run_compiler_on_path(root, |tcx| {
        collect_box_mir_drops(tcx, Some(&functions))
    })
    .map_err(|_| "emitted crate failed before the Box MIR drop observer".to_owned())
}

/// Fail closed when any compiler-inserted Box drop lacks a named authorization.
///
/// A `None` allowance line is deliberately broad only in the coordinate axis:
/// it still matches an exact function and binding identity. Production uses it
/// for the empty `Option<Box<_>>` shell left after `drop(p.take())`, whose
/// allocation generation is already closed at the retained C sink.
pub(crate) fn reconcile_box_mir_drops(
    drops: &[BoxMirDrop],
    allowances: &[BoxMirDropAllowance],
) -> Result<Vec<(BoxMirDrop, String)>, String> {
    let mut matched = Vec::new();
    for drop in drops {
        let candidates = allowances
            .iter()
            .filter(|allowance| {
                allowance.function == drop.function
                    && allowance.local_name == drop.local_name
                    && allowance.line.is_none_or(|line| line == drop.line)
                    && allowance
                        .cleanup
                        .is_none_or(|cleanup| cleanup == drop.cleanup)
                    && allowance
                        .site
                        .as_ref()
                        .is_none_or(|site| site == &drop.site)
            })
            .collect::<Vec<_>>();
        let [allowance] = candidates.as_slice() else {
            return Err(format!(
                "unreceipted Box MIR Drop: function={} local={} name={} site={} cleanup={} candidates={}",
                drop.function,
                drop.local,
                drop.local_name.as_deref().unwrap_or("<unnamed>"),
                drop.site,
                drop.cleanup,
                candidates.len(),
            ));
        };
        matched.push((drop.clone(), allowance.reason.clone()));
    }
    Ok(matched)
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
    // Routed through `diagnose_crate` so there is ONE diagnostic path. A gate
    // that counted errors differently from the loop that attributes them would
    // be two sources of truth about the same compile.
    diagnose_crate(root).errors == 0
}

/// The whole-crate compile observer for an in-memory single-file fixture.
///
/// This is deliberately routed through the same diagnostic counter as the
/// path gate: `run_compiler_on_str(..., |_| {})` only parses and enters the
/// global context, so it cannot serve as a borrow-check verdict.
#[cfg(test)]
pub(crate) fn type_checks_str(source: &str) -> bool {
    diagnose_input(::utils::compilation::str_to_input(source)).errors == 0
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
pub(crate) struct RelatedDiag {
    pub file: String,
    pub line: usize,
    pub column: usize,
    pub end_line: usize,
    pub end_column: usize,
    pub message: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Diag {
    pub file: String,
    pub line: usize,
    pub column: usize,
    pub end_line: usize,
    pub end_column: usize,
    pub message: String,
    pub direction: Direction,
    /// `E0308` and the like. `None` for lint errors, which carry no code — the
    /// distinction that made S2b.0's `error[`-counting instrument blind to
    /// deny-by-default lints.
    pub code: Option<String>,
    /// Located child notes, notably rustc's callee-definition span for an
    /// unadapted call argument. Diagnostic identity deliberately ignores these;
    /// E1 consumes them only when the primary span names no rewrite owner.
    pub related: Vec<RelatedDiag>,
}

/// Identity of a diagnostic that is STABLE UNDER LINE DRIFT.
///
/// Keyed on file, code and message — never the line, which every edit above it
/// moves. Compared as a MULTISET so a second occurrence of the same lint class
/// in the same file is novel rather than masked: the gate must judge the
/// rewrite's delta without going blind to rewrite-introduced violations of
/// exactly the class it is masking (reference casting).
pub(crate) fn baseline_key(diag: &Diag, crate_root: &Path) -> (String, String, String) {
    (
        crate_relative(&diag.file, crate_root),
        diag.code.clone().unwrap_or_default(),
        diag.message.clone(),
    )
}

/// A path relative to the crate root it belongs to.
///
/// # This is a CANONICALIZATION, not a derivation
///
/// Both sides of the differential — the baseline compiled in the original tree
/// and the observed crate compiled in a temp copy — must compute the SAME key
/// for the same logical file, each from its own root. A second implementation
/// here does not create a comparison, it destroys one: S2a-H duplicates
/// derivations because disagreement is the signal; a canonicalizer is shared
/// because disagreement is the defect.
///
/// It had two implementations, which disagreed. The baseline side split on a
/// hardcoded `/rs-crown/` and the observed side stripped a `crat-verify` temp
/// prefix, so the same file keyed as `brotli/src/enc/encode.rs` against
/// `src/enc/encode.rs` and the gate masked NOTHING on the corpus while passing
/// its flat fixture, whose basename fallback made both sides agree by accident.
///
/// **No directory layout is known here.** The root is passed in; there is no
/// corpus name, no temp-prefix pattern, and NO BASENAME FALLBACK — a basename
/// merges distinct files into one key, which would let a novel error in one file
/// read as another file's baseline. The gate would fail OPEN. A path not under
/// the given root keys as itself.
pub(crate) fn crate_relative(path: &str, crate_root: &Path) -> String {
    match Path::new(path).strip_prefix(crate_root) {
        Ok(relative) => relative.display().to_string(),
        Err(_) => path.to_owned(),
    }
}

/// Multiset of baseline diagnostic identities for an UNMODIFIED crate.
pub(crate) fn baseline_of(root: &Path) -> Baseline {
    let crate_root = root.parent().unwrap_or(root).to_path_buf();
    let diagnosis = diagnose_crate(root);
    let mut keys = std::collections::BTreeMap::new();
    let root_text = crate_root.display().to_string();
    let mut messages_embedding_root = 0usize;
    for diag in &diagnosis.diags {
        if diag.message.contains(&root_text) {
            messages_embedding_root += 1;
        }
        *keys
            .entry(baseline_key(diag, &crate_root))
            .or_insert(0usize) += 1;
    }
    Baseline {
        keys,
        errors: diagnosis.errors,
        messages_embedding_root,
    }
}

/// What the UNMODIFIED input already reports. The gate judges the rewrite's
/// DELTA against this, never the absolute count.
#[derive(Clone, Debug, Default)]
pub(crate) struct Baseline {
    pub keys: std::collections::BTreeMap<(String, String, String), usize>,
    /// Includes spanless error-level diagnostics, which have no key.
    pub errors: usize,
    /// Baseline messages that EMBED THEIR OWN CRATE ROOT.
    ///
    /// The key's message component is comparable across the two sides only if no
    /// message carries its environment: the baseline compiles in the original
    /// tree and the observed side in a temp copy, so an embedded path would
    /// diverge the key exactly as the file component did. Measured rather than
    /// assumed; expected zero.
    pub messages_embedding_root: usize,
}

impl Baseline {
    /// Diagnostics NOT already present in the unmodified input.
    /// `observed_root` is the crate root the OBSERVED diagnostics were compiled
    /// under — the temp copy's directory, not the original's. Each side
    /// canonicalizes against its own root, which is what makes the keys
    /// comparable at all.
    pub(crate) fn novel<'a>(&self, diags: &'a [Diag], observed_root: &Path) -> Vec<&'a Diag> {
        let mut seen: std::collections::BTreeMap<(String, String, String), usize> =
            std::collections::BTreeMap::new();
        diags
            .iter()
            .filter(|diag| {
                let key = baseline_key(diag, observed_root);
                let count = seen.entry(key.clone()).or_insert(0);
                *count += 1;
                // MULTISET: the Nth occurrence is novel once it exceeds the
                // baseline's N, so a rewrite-introduced repeat of a masked lint
                // class still gates.
                *count > *self.keys.get(&key).unwrap_or(&0)
            })
            .collect()
    }
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
        let related = diag
            .children
            .iter()
            .filter_map(|child| {
                let span = child.span.primary_span()?;
                let loc = self.source_map.lookup_char_pos(span.lo());
                let end = self.source_map.lookup_char_pos(span.hi());
                let message = child
                    .messages
                    .iter()
                    .filter_map(|(message, _)| match message {
                        rustc_errors::DiagMessage::Str(text) => Some(text.as_ref()),
                        _ => None,
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                Some(RelatedDiag {
                    file: loc.file.name.prefer_local().to_string(),
                    line: loc.line,
                    column: loc.col_display + 1,
                    end_line: end.line,
                    end_column: end.col_display + 1,
                    message,
                })
            })
            .collect();
        if let Some(span) = diag.span.primary_span() {
            let loc = self.source_map.lookup_char_pos(span.lo());
            let end = self.source_map.lookup_char_pos(span.hi());
            let direction = classify(&message);
            self.diags.lock().unwrap().push(Diag {
                file: loc.file.name.prefer_local().to_string(),
                line: loc.line,
                column: loc.col_display + 1,
                end_line: end.line,
                end_column: end.col_display + 1,
                message,
                direction,
                code: diag.code.map(|c| format!("{c:?}")),
                related,
            });
        }
        // Forward LAST: extraction borrows, rendering consumes.
        self.inner.emit_diagnostic(diag, _registry);
    }
}

/// Type-check the crate at `root` and return its error-level diagnostics.
pub(crate) fn diagnose_crate(root: &Path) -> Diagnosis {
    diagnose_input(::utils::compilation::path_to_input(root))
}

fn diagnose_input(input: rustc_session::config::Input) -> Diagnosis {
    let diags = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let errors = std::sync::Arc::new(std::sync::Mutex::new(0usize));
    let unrenderable = std::sync::Arc::new(std::sync::Mutex::new(0usize));

    let mut config = ::utils::compilation::make_config(input);
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

#[cfg(test)]
#[test]
fn call_mismatch_capture_retains_the_callee_definition_span() {
    let diagnosis = diagnose_input(::utils::compilation::str_to_input(
        "fn callee(_: &i32) {} fn caller(p: *const i32) { callee(p); }",
    ));
    let mismatch = diagnosis
        .diags
        .iter()
        .find(|diagnostic| matches!(diagnostic.code.as_deref(), Some("E0308" | "ErrCode(308)")))
        .expect("E0308 mismatch diagnostic");
    assert!(
        mismatch.column > 1
            && (mismatch.end_line, mismatch.end_column) >= (mismatch.line, mismatch.column),
        "primary diagnostic point range was not captured: {mismatch:?}"
    );
    assert!(
        mismatch.related.iter().any(|related| {
            related.message.contains("function defined here")
                && related.column > 0
                && (related.end_line, related.end_column) >= (related.line, related.column)
        }),
        "callee-definition span was discarded: {mismatch:?}"
    );
}
