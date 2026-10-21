//! The analysis code fingerprint: SHA-256 over the source files the model is a
//! function of. `build.rs` includes this file by `#[path]` and bakes the value in
//! as `BO_ANALYSIS_FINGERPRINT`; the tests recompute it over the same roots. It
//! uses std and `sha2` only, nothing of this crate.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

/// The legacy crate's files the analysis runs on, relative to its `src/`: the
/// modules BO's non-test analysis code names, closed over those modules' own
/// non-test `crate::` / `super::` references. Every file of a
/// covered module is hashed, its tests included. A new legacy reference from
/// `src/analyses/**` needs its module here.
pub(crate) const LEGACY_FILES: &[&str] = &[
    "analyses/borrow/errors.rs",
    "analyses/borrow/invalidates.rs",
    "analyses/borrow/killed.rs",
    "analyses/borrow/lifetime_flow.rs",
    "analyses/borrow/loan_liveness.rs",
    "analyses/borrow/mod.rs",
    "analyses/borrow/places_conflict.rs",
    "analyses/borrow/provenance_liveness.rs",
    "analyses/borrow/requires.rs",
    "analyses/borrow/subset_closure.rs",
    "analyses/borrow/tests.rs",
    "analyses/encoding.rs",
    "analyses/fn_ptr_groups.rs",
    "analyses/fn_ptr_rewrite_decision.rs",
    "analyses/lattice.rs",
    "analyses/liveness.rs",
    "analyses/mir/mod.rs",
    "analyses/mir/terminator.rs",
    "analyses/mir/ty.rs",
    "analyses/offset_sign/sign.rs",
    "analyses/output_params/eliminable_temporaries.rs",
    "analyses/output_params/mod.rs",
    "analyses/ownership/assoc.rs",
    "analyses/ownership/call_graph.rs",
    "analyses/ownership/discretization.rs",
    "analyses/ownership/infer.rs",
    "analyses/ownership/infer/boundary.rs",
    "analyses/ownership/infer/boundary/libc.rs",
    "analyses/ownership/infer/boundary/library.rs",
    "analyses/ownership/mod.rs",
    "analyses/ownership/ptr.rs",
    "analyses/ownership/solidify.rs",
    "analyses/ownership/ssa/constants.rs",
    "analyses/ownership/ssa/constraint.rs",
    "analyses/ownership/ssa/constraint/infer.rs",
    "analyses/ownership/ssa/consume.rs",
    "analyses/ownership/ssa/dom.rs",
    "analyses/ownership/ssa/join_points.rs",
    "analyses/ownership/ssa/mod.rs",
    "analyses/ownership/ssa/state.rs",
    "analyses/ownership/struct_ctxt.rs",
    "analyses/ownership/vec_vec.rs",
    "analyses/ownership/whole_program.rs",
    "analyses/ownership/whole_program/state.rs",
    "analyses/struct_copy/mod.rs",
    "analyses/type_qualifier/foster/constraint_system.rs",
    "analyses/type_qualifier/foster/fatness/libc.rs",
    "analyses/type_qualifier/foster/fatness/library.rs",
    "analyses/type_qualifier/foster/fatness/mod.rs",
    "analyses/type_qualifier/foster/mod.rs",
    "analyses/type_qualifier/foster/mutability/libc.rs",
    "analyses/type_qualifier/foster/mutability/library.rs",
    "analyses/type_qualifier/foster/mutability/mod.rs",
    "rewriter/collector.rs",
    "rewriter/decision.rs",
    "rewriter/diagnostics.rs",
    "rewriter/lifetimes.rs",
    "rewriter/transform/mod.rs",
    "utils/dsa/fixed_shape.rs",
    "utils/dsa/union_find.rs",
    "utils/rustc.rs",
];

/// One root: the files under `dir` (all of them, recursively, when `files` is
/// `None`), each named `label/<path under dir>` with `/` separators.
pub(crate) struct Root<'a> {
    pub(crate) label: &'a str,
    pub(crate) dir: &'a Path,
    pub(crate) files: Option<&'a [&'a str]>,
}

/// The two roots of the analysis: this crate's `src/analyses` (every byte) and
/// the legacy crate's listed files.
pub(crate) fn analysis_roots<'a>(bo_analyses: &'a Path, legacy_src: &'a Path) -> [Root<'a>; 2] {
    [
        Root {
            label: "bo",
            dir: bo_analyses,
            files: None,
        },
        Root {
            label: "legacy",
            dir: legacy_src,
            files: Some(LEGACY_FILES),
        },
    ]
}

fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir).expect("complete analyses tree");
    for entry in entries {
        let path = entry.expect("read analysis entry").path();
        if path.is_dir() {
            walk(&path, out);
        } else if path.is_file() {
            out.push(path);
        }
    }
}

/// The covered files by name, in the order the fingerprint hashes them.
pub(crate) fn covered(roots: &[Root<'_>]) -> Vec<(String, PathBuf)> {
    let mut out = Vec::new();
    for root in roots {
        match root.files {
            Some(files) => out.extend(
                files
                    .iter()
                    .map(|file| (format!("{}/{file}", root.label), root.dir.join(file))),
            ),
            None => {
                let mut found = Vec::new();
                walk(root.dir, &mut found);
                for path in found {
                    let relative = path
                        .strip_prefix(root.dir)
                        .expect("walked file is under its root")
                        .components()
                        .map(|component| component.as_os_str().to_string_lossy())
                        .collect::<Vec<_>>()
                        .join("/");
                    out.push((format!("{}/{relative}", root.label), path));
                }
            }
        }
    }
    out.sort();
    out
}

/// SHA-256 over every covered file's name length, name and content hash, in name
/// order. The names are relative, so the value does not depend on where the tree
/// is checked out.
pub(crate) fn fingerprint(roots: &[Root<'_>]) -> String {
    let mut hash = Sha256::new();
    for (name, path) in covered(roots) {
        let content = std::fs::read(&path)
            .unwrap_or_else(|error| panic!("read covered file {}: {error}", path.display()));
        hash.update((name.len() as u64).to_le_bytes());
        hash.update(name.as_bytes());
        hash.update(Sha256::digest(content));
    }
    format!("{:x}", hash.finalize())
}
