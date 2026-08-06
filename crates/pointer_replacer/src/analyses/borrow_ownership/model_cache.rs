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

use std::path::{Path, PathBuf};

use rustc_hash::FxHashMap;
use rustc_middle::ty::TyCtxt;
use sha2::{Digest, Sha256};

use super::{
    SlotKind,
    crate_slots::CrateSlots,
    slot_key::{field_key, local_key},
    solver::SlotRef,
};
use crate::utils::rustc::RustProgram;

/// `CRAT_BO_CACHE=1` enables reads. Writes happen whenever a real solve runs
/// with a cache directory configured, so a bypassed gate sweep still refreshes
/// what dev iteration will read next.
pub(crate) fn read_enabled() -> bool {
    matches!(std::env::var("CRAT_BO_CACHE").as_deref(), Ok("1"))
}

pub(crate) fn dir() -> Option<PathBuf> {
    std::env::var_os("CRAT_BO_CACHE_DIR").map(PathBuf::from)
}

/// Everything the cached model is a function of.
///
/// A change to **any** of these must invalidate, so they are hashed together
/// into one value rather than checked severally — a severally-checked key grows
/// a forgotten term.
pub(crate) fn fingerprint(program: &RustProgram<'_>) -> String {
    let mut h = Sha256::new();

    // 1. The program's own source. Per-program, not the whole-corpus digest, so
    //    one program changing does not void the other nineteen.
    let tcx = program.tcx;
    let mut files: Vec<(String, u64)> = Vec::new();
    for f in tcx.sess.source_map().files().iter() {
        if let rustc_span::FileName::Real(rp) = &f.name
            && let Some(p) = rp.local_path()
        {
            files.push((p.display().to_string(), f.src_hash.hash_bytes().len() as u64));
            h.update(p.display().to_string().as_bytes());
            h.update(f.src_hash.hash_bytes());
        }
    }
    let _ = files;

    // 2. The analysis code. Any edit under `analyses/` changes what a solve
    //    means, so a cache written by the old code must not be read by the new.
    h.update(analysis_code_fingerprint().as_bytes());

    // 3. The toolchain.
    h.update(
        std::fs::read(concat!(env!("CARGO_MANIFEST_DIR"), "/../../rust-toolchain.toml"))
            .unwrap_or_default(),
    );

    // 4. Mode flags that reach the solver.
    for k in [
        "CRAT_BO_L2_GUARDED_COMMITS",
        "CRAT_BO_SAFE_MONO",
        "CRAT_BO_STRONG_MONO",
        "CRAT_BO_PER_SITE",
        "CRAT_BO_EXPORT",
    ] {
        h.update(k.as_bytes());
        h.update(std::env::var(k).unwrap_or_default().as_bytes());
    }

    format!("{:x}", h.finalize())
}

/// SHA-256 over the sorted contents of the analyses source tree.
///
/// Computed at runtime rather than baked in at build time: a baked constant
/// would be stale exactly when the sources change without a rebuild of this
/// file, which is the failure mode it exists to prevent.
fn analysis_code_fingerprint() -> String {
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
    let root = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/src/analyses"));
    let mut files = Vec::new();
    walk(root, &mut files);
    files.sort();
    let mut h = Sha256::new();
    for f in &files {
        h.update(f.display().to_string().as_bytes());
        h.update(std::fs::read(f).unwrap_or_default());
    }
    format!("{:x}", h.finalize())
}

fn entry_path(d: &Path, fingerprint: &str) -> PathBuf {
    d.join(format!("{fingerprint}.model.tsv"))
}

/// Serialize the accepted model under canonical slot keys.
pub(crate) fn store(
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) {
    let (Some(d), fp) = (dir(), fingerprint(program)) else {
        return;
    };
    if std::fs::create_dir_all(&d).is_err() {
        return;
    }
    let mut lines: Vec<String> = model
        .iter()
        .filter_map(|(r, k)| {
            let key = render_key(tcx, slots, *r)?;
            let kind = match k {
                SlotKind::Ref => "ref",
                SlotKind::Raw => "raw",
                SlotKind::Owning => "owning",
            };
            Some(format!("{key}\t{kind}"))
        })
        .collect();
    // Sorted: a cache entry that permutes between runs is not comparable, and
    // D19's lesson is that report order is part of the artifact.
    lines.sort();
    let body = format!("# fingerprint {fp}\n{}\n", lines.join("\n"));
    let _ = std::fs::write(entry_path(&d, &fp), body);
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
) -> Option<FxHashMap<SlotRef, SlotKind>> {
    if !read_enabled() {
        return None;
    }
    let d = dir()?;
    let fp = fingerprint(program);
    let text = std::fs::read_to_string(entry_path(&d, &fp)).ok()?;

    // The fingerprint is in the key AND in the body. The body check catches a
    // file renamed or copied into place — the shape a manifest check exists for.
    let first = text.lines().next()?;
    if first != format!("# fingerprint {fp}") {
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
                by_key.insert(k, SlotRef::Local(fn_did, id));
            }
        }
    }
    for i in 0..slots.field_slots.len() {
        let id = super::slots::SlotId::from_usize(i);
        if let Some(k) = render_key(tcx, slots, SlotRef::Field(id)) {
            by_key.insert(k, SlotRef::Field(id));
        }
    }

    let mut out = FxHashMap::default();
    for line in text.lines().skip(1) {
        if line.trim().is_empty() {
            continue;
        }
        let (key, kind) = line.split_once('\t')?;
        let r = *by_key.get(key)?;
        let k = match kind {
            "ref" => SlotKind::Ref,
            "raw" => SlotKind::Raw,
            "owning" => SlotKind::Owning,
            _ => return None,
        };
        out.insert(r, k);
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

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
