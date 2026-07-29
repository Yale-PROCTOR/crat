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

// ---------------------------------------------------------------------------
// Per-phase rules (M1 architecture directive)
// ---------------------------------------------------------------------------

/// One phase's import restrictions.
///
/// The directive names one rule explicitly — `apply/` is analysis-blind and may
/// see plan structs and the AST only. The remaining rules encode E1 state
/// visibility's *one-way flow*: a phase may not name a phase downstream of it,
/// because a back-pointer is exactly how "hands the next phase a finished
/// value" decays into a shared mutable context.
struct PhaseRule {
    /// Directory under `bo_rewriter/`.
    phase: &'static str,
    forbidden: &'static [&'static str],
    why: &'static str,
}

const PHASE_RULES: &[PhaseRule] = &[
    PhaseRule {
        phase: "apply",
        forbidden: &[
            "crate::analyses",
            "super::decision",
            "crate::bo_rewriter::decision",
            "BoExport",
            "export::",
        ],
        why: "apply is ANALYSIS-BLIND: it imports plan structs and the AST only. \
              A question that arises here and is not answered by the plan is a \
              PLAN defect — importing an analysis to answer it is the failure \
              this rule exists to prevent",
    },
    PhaseRule {
        phase: "decision",
        forbidden: &["super::apply", "super::verify"],
        why: "E1 one-way flow: decision hands plan a finished table and holds no \
              back-pointer to a later phase",
    },
    PhaseRule {
        phase: "verify",
        forbidden: &["crate::analyses"],
        why: "verify gates on the EMITTED crate and on values the earlier phases               handed it — `utils::type_check` plus the structural counters.               Re-consulting an analysis here would make a gate agree with the               decision that produced it, which is not a gate",
    },
    PhaseRule {
        phase: "artifact",
        forbidden: &["super::apply", "super::verify", "super::plan"],
        why: "producer A SERIALIZES the decision table and compares nothing. It \
              may read `decision` (that is its input) and \
              `coverage_recon::schema` (the wire contract), and nothing else — \
              a comparison appearing here would put the gate back beside the \
              collector, which is the co-location this whole slice moved out",
    },
    PhaseRule {
        phase: "plan",
        forbidden: &["crate::analyses", "super::apply", "super::verify"],
        why: "E1 one-way flow: plan consumes the decision table by value and may \
              not re-consult an analysis, nor name a later phase",
    },
];

fn phase_dir(phase: &str) -> std::path::PathBuf {
    module_root().join(phase)
}

/// Each phase directory obeys its own import restrictions.
#[test]
fn phases_obey_their_import_rules() {
    for rule in PHASE_RULES {
        let dir = phase_dir(rule.phase);
        assert!(
            dir.is_dir(),
            "phase directory {dir:?} is missing — the phase separation is part of \
             the architecture, not an optional layout"
        );
        let mut files = Vec::new();
        collect_rs_files(&dir, &mut files);
        assert!(
            !files.is_empty(),
            "no .rs files under {dir:?}; this check would pass vacuously"
        );
        for file in &files {
            let text = fs::read_to_string(file)
                .unwrap_or_else(|e| panic!("unreadable phase source {file:?}: {e}"));
            let name = file.file_name().unwrap_or_default().to_string_lossy().into_owned();

            // (a) IMPORTS — resolved from the use-tree, so a brace-merged form
            // is matched on its full path rather than on the text of one line.
            for path in imported_paths(&text) {
                for fragment in rule.forbidden {
                    assert!(
                        !path.contains(fragment),
                        "{}/{name} imports {path:?}, which contains {fragment:?} \
                         and this phase may not import it.\n{}",
                        rule.phase,
                        rule.why
                    );
                }
            }

            // (b) NON-IMPORT references — an inline path expression such as
            // `crate::rewriter::f()` is not a use-tree, so the textual scan is
            // still needed. It is sound HERE because a path expression cannot be
            // split across lines by the formatter the way a use-tree can.
            for (lineno, line) in text.lines().enumerate() {
                if is_comment(line) || line.trim_start().starts_with("use ") {
                    continue;
                }
                for fragment in rule.forbidden {
                    assert!(
                        !line.contains(fragment),
                        "{}/{name} line {} names {fragment:?} outside an import.\n{}",
                        rule.phase,
                        lineno + 1,
                        rule.why
                    );
                }
            }
        }
    }
}

/// Every per-phase rule must actually fire on a breach.
///
/// Mutation coverage in test form: a rule whose matcher never matches is a rule
/// that is not enforcing anything, and the whole point of this file is that the
/// isolation is mechanical rather than aspirational.
#[test]
fn every_phase_rule_matches_a_synthetic_breach() {
    for rule in PHASE_RULES {
        for fragment in rule.forbidden {
            let breach = format!("use {fragment}Something;");
            assert!(
                breach.contains(fragment),
                "phase rule {}/{fragment:?} does not match its own synthetic \
                 breach — the matcher is broken",
                rule.phase
            );
            assert!(
                !is_comment(&breach),
                "synthetic breach was classified as a comment, so the scan would \
                 skip it"
            );
        }
    }
}

/// The phase set is complete: every directory under `bo_rewriter/` that holds a
/// phase has a rule, so a new phase cannot be added silently unregulated.
#[test]
fn every_phase_directory_has_a_rule() {
    let mut dirs: Vec<String> = fs::read_dir(module_root())
        .expect("module root readable")
        .flatten()
        .filter(|e| e.path().is_dir())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|name| name != "testdata")
        .collect();
    dirs.sort();
    let mut ruled: Vec<String> = PHASE_RULES.iter().map(|r| r.phase.to_owned()).collect();
    ruled.sort();
    assert_eq!(
        dirs, ruled,
        "a phase directory exists with no import rule (or a rule names a \
         directory that does not exist). Every phase is regulated, or the \
         architecture claim is unenforced."
    );
}

// ---------------------------------------------------------------------------
// Syntax-aware import resolution (H1)
// ---------------------------------------------------------------------------

/// Fully-qualified import paths for one source file, with **merged and braced
/// use-trees flattened**.
///
/// # Why this replaced a line scan
///
/// The previous matcher tested `line.contains(fragment)`. This repository's
/// `rustfmt.toml` sets `imports_granularity = "Crate"`, which merges sibling
/// imports into a braced tree and wraps it — so `use crate::analyses::X;`
/// becomes
///
/// ```text
/// use crate::{
///     analyses::X,
///     utils::Y,
/// };
/// ```
///
/// and **no line contains `crate::analyses`**. Every `crate::`-prefixed rule
/// evaded simultaneously, and not hypothetically: `bo_rewriter/mod.rs` already
/// carries exactly that form, so the rule was already blind to a real import at
/// the moment it was written. A rule that cannot see the shape its own
/// formatter produces is not enforcement.
///
/// Resolving the use-tree removes the formatter from the trust chain entirely:
/// `use crate::{analyses::X}` and `use crate::analyses::X;` flatten to the same
/// path, so how the source is wrapped stops mattering.
fn imported_paths(text: &str) -> Vec<String> {
    let Ok(file) = syn::parse_file(text) else {
        // A file that does not parse cannot be cleared by this check. Returning
        // a sentinel keeps the failure loud rather than silently vacuous.
        return vec!["<unparseable — import check could not run>".to_owned()];
    };
    let mut out = Vec::new();
    collect_use_items(&file.items, &mut out);
    out
}

fn collect_use_items(items: &[syn::Item], out: &mut Vec<String>) {
    for item in items {
        match item {
            syn::Item::Use(use_item) => flatten_use_tree(&use_item.tree, String::new(), out),
            syn::Item::Mod(m) => {
                if let Some((_, inner)) = &m.content {
                    collect_use_items(inner, out);
                }
            }
            _ => {}
        }
    }
}

fn flatten_use_tree(tree: &syn::UseTree, prefix: String, out: &mut Vec<String>) {
    let join = |prefix: &str, seg: &str| {
        if prefix.is_empty() {
            seg.to_owned()
        } else {
            format!("{prefix}::{seg}")
        }
    };
    match tree {
        syn::UseTree::Path(p) => {
            flatten_use_tree(&p.tree, join(&prefix, &p.ident.to_string()), out)
        }
        syn::UseTree::Name(n) => out.push(join(&prefix, &n.ident.to_string())),
        syn::UseTree::Rename(r) => out.push(join(&prefix, &r.ident.to_string())),
        syn::UseTree::Glob(_) => out.push(join(&prefix, "*")),
        syn::UseTree::Group(g) => {
            for item in &g.items {
                flatten_use_tree(item, prefix.clone(), out);
            }
        }
    }
}

/// **H1 regression witness.** The matcher must catch BOTH breach shapes —
/// the brace-merged form the formatter actually produces, and the single-line
/// form. The old line scan caught only the second.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** revert
/// `phases_obey_their_import_rules` to a line scan and the merged case here
/// stops being detected.
#[test]
fn matcher_catches_both_breach_shapes() {
    let single_line = "use crate::analyses::borrow_ownership::SlotKind;\nfn f() {}\n";
    let brace_merged = "use crate::{\n    analyses::borrow_ownership::SlotKind,\n    utils::rustc::RustProgram,\n};\nfn f() {}\n";

    for (label, src) in [("single-line", single_line), ("brace-merged", brace_merged)] {
        let paths = imported_paths(src);
        assert!(
            paths.iter().any(|p| p.contains("crate::analyses")),
            "{label} breach was NOT resolved to a crate::analyses path; \
             resolved paths were {paths:?}"
        );
    }

    // And the shape that defeated the old matcher must be one no LINE contains.
    assert!(
        !brace_merged
            .lines()
            .any(|l| l.contains("crate::analyses")),
        "the brace-merged fixture no longer exercises the evasion it exists to \
         reproduce — a line scan would catch it, so this witness is inert"
    );
}

/// **H1's first real input.** The matcher is pointed at the merged import that
/// was already in the tree and already invisible to the line scan.
///
/// `mod.rs` is the driver, not a phase, so importing analyses there is
/// legitimate — what is asserted is that the MATCHER SEES IT. If this stops
/// resolving, the enforcement has gone blind again in exactly the way H1
/// described.
#[test]
fn matcher_resolves_the_existing_merged_import_in_mod_rs() {
    let mod_rs = module_root().join("mod.rs");
    let text = fs::read_to_string(&mod_rs).expect("driver source readable");
    let paths = imported_paths(&text);
    assert!(
        paths.iter().any(|p| p.starts_with("crate::analyses")),
        "the matcher did not resolve the driver's brace-merged analyses import; \
         resolved paths were {paths:?}"
    );
    // The property that made H1 a HIGH: no single LINE carries the fragment.
    assert!(
        !text
            .lines()
            .filter(|l| !is_comment(l))
            .any(|l| l.contains("crate::analyses")),
        "the driver's import is now on one line, so this file no longer \
         witnesses the evasion H1 was about — pick another real input"
    );
}

// ---------------------------------------------------------------------------
// R-C: the `if let` ban on outcome inspection, mechanized
// ---------------------------------------------------------------------------

/// **`if let RewriteOutcome::` is banned in this module tree.**
///
/// Twice a witness placed its load-bearing assertion inside
/// `if let RewriteOutcome::Degraded { .. } = …` with no `else`, in a fixture
/// that returns `Emitted` — so the assertion never ran. The second instance was
/// written *in the commit that repaired the first*. A rule violated twice by
/// the same author in consecutive rounds is the signature of something that
/// needs a machine rather than a review note (R-C).
///
/// The check is deliberately narrow, and that is what makes it exact: clippy
/// has no "if let without else" lint (`single_match_else` is the opposite
/// shape), but the *type name* makes this shape unambiguous. Inspecting an
/// outcome uses an exhaustive `match`, with every arm either asserting or
/// documenting why it is unreachable.
///
/// A `let …else` (`let RewriteOutcome::Emitted { .. } = x else { panic!() }`)
/// is NOT banned: its else branch is mandatory and diverging, so the
/// unexecuted-assertion failure mode cannot arise.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the violation loop
/// makes `if_let_ban_matches_a_synthetic_breach` fail.
#[test]
fn witnesses_never_inspect_an_outcome_with_a_bare_if_let() {
    let root = module_root();
    let mut files = Vec::new();
    collect_rs_files(root, &mut files);
    assert!(!files.is_empty(), "no sources scanned");

    let mut violations = Vec::new();
    for file in &files {
        if is_denylist_self_reference(file, root) {
            continue;
        }
        let text = fs::read_to_string(file).expect("source file is readable");
        for (index, line) in text.lines().enumerate() {
            if is_comment(line) {
                continue;
            }
            if let Some(offense) = if_let_offense(line) {
                violations.push(format!(
                    "{}:{}: {offense}",
                    file.strip_prefix(root).unwrap_or(file).display(),
                    index + 1
                ));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "witnesses inspecting a RewriteOutcome must use an exhaustive `match` \
         (or a diverging `let …else`), never a bare `if let` — the body is \
         skipped for the arm the fixture actually takes, which is how two \
         load-bearing assertions shipped unexecuted:\n  {}",
        violations.join("\n  ")
    );
}

/// The banned shape on one line, or `None`.
fn if_let_offense(line: &str) -> Option<&'static str> {
    let trimmed = line.trim_start();
    if !trimmed.starts_with("if let ") {
        return None;
    }
    if !trimmed.contains("RewriteOutcome::") {
        return None;
    }
    Some("bare `if let` on a RewriteOutcome")
}

/// The R-C check must reject a real violation, not merely pass on clean code.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the
/// `trimmed.contains("RewriteOutcome::")` guard in [`if_let_offense`] makes the
/// negative cases below fail; deleting the `starts_with` guard makes the
/// `match`/`let …else` cases fail.
#[test]
fn if_let_ban_matches_a_synthetic_breach() {
    // The shape that shipped twice.
    assert!(
        if_let_offense("    if let RewriteOutcome::Degraded { reason, .. } = rewrite_m1(&src) {")
            .is_some(),
        "the exact shape this ban exists for was not detected"
    );
    // Indentation must not matter.
    assert!(
        if_let_offense("if let RewriteOutcome::Emitted { .. } = outcome {").is_some(),
        "detection is indentation-sensitive"
    );
    // Permitted shapes.
    assert!(
        if_let_offense("    match rewrite_m1(&src) {").is_none(),
        "an exhaustive match must not be flagged"
    );
    assert!(
        if_let_offense("    let RewriteOutcome::Emitted { source, .. } = out else {").is_none(),
        "a diverging `let …else` must not be flagged — its else branch is \
         mandatory, so the unexecuted-assertion failure mode cannot arise"
    );
    assert!(
        if_let_offense("    if let Some(span) = spans.first() {").is_none(),
        "an `if let` on an unrelated type must not be flagged"
    );
}

// ---------------------------------------------------------------------------
// S2a-H amendment (b): the import direction is ONE-WAY
// ---------------------------------------------------------------------------

/// **`coverage_recon/` imports NOTHING from `bo_rewriter`.**
///
/// Only the reverse direction is licensed — `bo_rewriter::artifact` reads
/// `coverage_recon::schema`, the wire contract. **Producer B is the point of
/// this rule.** An import from `bo_rewriter` into the independent reference
/// walker is exactly the conceptual leakage the authorship split exists to
/// prevent, and unlike the leakage that can hide in a specification, this form
/// is mechanically detectable — so it is mechanized.
///
/// This is the compensating control for keeping `coverage_recon` in-crate
/// rather than behind a crate boundary: the boundary is enforced by test
/// instead of by the module system.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the violation
/// accumulation makes `coverage_recon_rule_matches_a_synthetic_breach` fail.
#[test]
fn coverage_recon_never_imports_from_bo_rewriter() {
    let root = module_root()
        .parent()
        .expect("bo_rewriter has a parent")
        .join("coverage_recon");
    let mut files = Vec::new();
    collect_rs_files(&root, &mut files);
    assert!(
        !files.is_empty(),
        "no coverage_recon sources scanned at {root:?} — the rule would pass \
         vacuously"
    );

    let mut violations = Vec::new();
    for file in &files {
        let text = fs::read_to_string(file).expect("source file is readable");
        for (index, line) in text.lines().enumerate() {
            if is_comment(line) {
                continue;
            }
            if let Some(offense) = bo_rewriter_reference(line) {
                violations.push(format!(
                    "{}:{}: {offense}",
                    file.strip_prefix(&root).unwrap_or(file).display(),
                    index + 1
                ));
            }
        }
    }
    assert!(
        violations.is_empty(),
        "coverage_recon must not reference bo_rewriter — producer B's \
         independence is the point of this rule:\n  {}",
        violations.join("\n  ")
    );
}

/// A reference to `bo_rewriter` on one line, or `None`.
fn bo_rewriter_reference(line: &str) -> Option<&'static str> {
    if line.contains("bo_rewriter") {
        return Some("reference to bo_rewriter");
    }
    None
}

/// The one-way rule must reject a real breach, not merely pass on clean code.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `line.contains`
/// check in [`bo_rewriter_reference`] fails this.
#[test]
fn coverage_recon_rule_matches_a_synthetic_breach() {
    assert!(
        bo_rewriter_reference("use crate::bo_rewriter::decision::Subject;").is_some(),
        "a direct import from bo_rewriter was not detected"
    );
    assert!(
        bo_rewriter_reference("    let x = super::super::bo_rewriter::rewrite_m1(s);").is_some(),
        "a path reference to bo_rewriter was not detected"
    );
    assert!(
        bo_rewriter_reference("use crate::analyses::borrow_ownership::SlotKind;").is_none(),
        "an unrelated import must not be flagged"
    );
}
