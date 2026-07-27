//! Mechanical enforcement of the greenfield isolation rule (design §6.3).
//!
//! The 2026-07-27 ruling makes `bo_rewriter/` a top-level module rather than a
//! separate crate, because a crate would have forced `mod analyses` public. The
//! cost of that choice is losing compile-time isolation from
//! [`crate::rewriter`]: sibling modules can see each other's `pub(crate)` items
//! freely, so nothing in the type system stops an import.
//!
//! This test buys that isolation back.
//!
//! # Why a filesystem walk rather than `include_str!`
//!
//! The in-tree precedent (`analyses/borrow_ownership/borrow_engine/mod.rs`'s
//! `fork_sync` tripwire) uses `include_str!`, which requires naming every file
//! by hand — so a newly added file silently escapes the scan. Walking the
//! directory at test time catches new files automatically, which is the
//! property that matters for a module expected to grow through M1–M4.

use std::{fs, path::Path};

/// Path fragments that would breach the isolation rule. Matching is textual and
/// deliberately over-broad: a false positive is a rename away, a false negative
/// is a silent architectural regression.
const FORBIDDEN: &[&str] = &[
    "crate::rewriter",
    "super::rewriter",
    "use rewriter",
    "::rewriter::",
];

fn module_root() -> &'static Path {
    // `CARGO_MANIFEST_DIR` is the crate root, so this resolves inside whichever
    // checkout/worktree is running the test.
    Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/src/bo_rewriter"))
}

fn collect_rs_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
    let entries = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("bo_rewriter module directory unreadable at {dir:?}: {e}"));
    for entry in entries {
        let entry = entry.expect("readable directory entry");
        let path = entry.path();
        if path.is_dir() {
            collect_rs_files(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

/// Every `.rs` file under `bo_rewriter/` must be free of any reference to the
/// frozen `rewriter` tree.
#[test]
fn bo_rewriter_never_references_the_frozen_rewriter() {
    let root = module_root();
    let mut files = Vec::new();
    collect_rs_files(root, &mut files);

    // Fail loudly rather than vacuously: an empty scan would "pass" while
    // checking nothing, which is exactly how this class of test rots.
    assert!(
        !files.is_empty(),
        "no .rs files found under {root:?} — the denylist scan would pass vacuously"
    );

    let mut breaches = Vec::new();
    for file in &files {
        // This file necessarily *spells* the forbidden fragments — in its
        // `FORBIDDEN` table and in the synthetic-breach fixture — so it cannot
        // scan itself without indicting its own implementation.
        if is_denylist_self_reference(file, root) {
            continue;
        }
        let text = fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("bo_rewriter source unreadable at {file:?}: {e}"));
        for (lineno, line) in text.lines().enumerate() {
            // Comments cannot import. Documentation is expected to name the
            // frozen tree in order to explain the rule, so scanning comments
            // would make the module undocumentable.
            if is_comment(line) {
                continue;
            }
            if let Some(needle) = FORBIDDEN.iter().find(|needle| line.contains(**needle)) {
                breaches.push(format!(
                    "{}:{}: matched {:?} in: {}",
                    file.display(),
                    lineno + 1,
                    needle,
                    line.trim()
                ));
            }
        }
    }

    assert!(
        breaches.is_empty(),
        "bo_rewriter/ must never reference the frozen `rewriter` tree \
         (greenfield ruling 2026-07-27). Offending lines:\n{}",
        breaches.join("\n")
    );
}

/// This module is the one file allowed to contain the forbidden fragments,
/// because it has to spell them to search for them.
fn is_denylist_self_reference(file: &Path, root: &Path) -> bool {
    file == root.join("import_denylist.rs")
}

/// Line comments and doc comments, which cannot import anything.
///
/// Deliberately does **not** handle block comments: `/* … */` spanning an
/// import would be dead code that still reads as a breach, and flagging it is
/// the safer error.
fn is_comment(line: &str) -> bool {
    line.trim_start().starts_with("//")
}

/// The scan must actually reach files — guards against a path typo silently
/// turning the real test into a no-op.
#[test]
fn denylist_scan_reaches_the_module_sources() {
    let root = module_root();
    let mut files = Vec::new();
    collect_rs_files(root, &mut files);
    let names: Vec<_> = files
        .iter()
        .filter_map(|p| p.file_name().and_then(|n| n.to_str()))
        .collect();
    assert!(
        names.contains(&"mod.rs"),
        "expected bo_rewriter/mod.rs in the scan, found {names:?}"
    );
}

/// The denylist itself must be able to catch a breach. Without this, a broken
/// matcher would let every real test pass.
#[test]
fn denylist_matches_a_synthetic_breach() {
    let sample = "use crate::rewriter::decision::PtrKind;";
    assert!(
        FORBIDDEN.iter().any(|needle| sample.contains(needle)),
        "denylist failed to match a known-bad import line"
    );
}
