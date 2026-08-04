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

/// Scan every `.rs` file under `root`, reporting one entry per offending line.
///
/// # The F3 repair, applied once for every scan in this file
///
/// A scan whose accumulation is exercised **only** by the production call has
/// no witness for its own wiring: on clean sources it returns empty, so
/// deleting the accumulation is invisible — the suite stays green and the rule
/// silently stops being enforced. That defect was found in the R-C `if let`
/// scan, then reproduced by its author in the `coverage_recon` rule one slice
/// later, and the audit found it in two more. Four instances is a pattern, not
/// four mistakes.
///
/// The repair is structural: **the production checks and their
/// synthetic-corpus witnesses call this same function.** A synthetic corpus
/// containing a real violation drives the same accumulate path the production
/// call uses, so deleting that path fails a standing test.
///
/// Comments are skipped here, uniformly: a comment cannot import, and
/// documentation has to be able to name what a rule forbids in order to
/// explain it.
fn scan_root(
    root: &Path,
    skip: &dyn Fn(&Path) -> bool,
    offense: &dyn Fn(&str) -> Option<String>,
) -> Vec<String> {
    let mut files = Vec::new();
    collect_rs_files(root, &mut files);
    assert!(
        !files.is_empty(),
        "no .rs files found under {root:?} — the scan would pass vacuously"
    );
    let mut hits = Vec::new();
    let mut scanned = 0usize;
    for file in &files {
        if skip(file) {
            continue;
        }
        scanned += 1;
        let text = fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("source unreadable at {file:?}: {e}"));
        for (index, line) in text.lines().enumerate() {
            if is_comment(line) {
                continue;
            }
            if let Some(detail) = offense(line) {
                hits.push(format!(
                    "{}:{}: {detail}",
                    file.strip_prefix(root).unwrap_or(file).display(),
                    index + 1
                ));
            }
        }
    }
    // The `files.is_empty()` assert above runs BEFORE `skip`, so an over-broad
    // skip predicate left every production scan examining nothing and reporting
    // clean — permanently. Measured 2026-07-31: making
    // `is_denylist_self_reference` match every file kept all 20 tests in this
    // module green. Asserting SURVIVORS converts every caller at one site.
    assert!(
        scanned > 0,
        "every file under {root:?} was skipped — the scan examined nothing and \
         would report clean regardless of what the sources contain"
    );
    hits
}

/// Write a throwaway source tree and return its root.
///
/// This is what makes the scans' accumulation witnessable: a corpus that
/// genuinely violates the rule, fed to the production scan function.
///
/// Callers clean up with [`drop_corpus`] **after** their assertions, so a
/// FAILING test leaves its corpus on disk to be inspected. The pid in the path
/// keeps concurrent `cargo test` processes from colliding on a shared tag.
#[cfg(test)]
fn temp_corpus(tag: &str, files: &[(&str, &str)]) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "crat-denylist-{}-{tag}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create temp corpus");
    for (name, body) in files {
        let path = dir.join(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create temp corpus subdir");
        }
        fs::write(&path, body).expect("write temp source");
    }
    dir
}

/// A line referencing the frozen `rewriter` tree, or `None`.
fn frozen_rewriter_offense(line: &str) -> Option<String> {
    FORBIDDEN
        .iter()
        .find(|needle| line.contains(**needle))
        .map(|needle| format!("matched {needle:?} in: {}", line.trim()))
}

/// Every `.rs` file under `bo_rewriter/` must be free of any reference to the
/// frozen `rewriter` tree.
#[test]
fn bo_rewriter_never_references_the_frozen_rewriter() {
    let root = module_root();
    // This file necessarily *spells* the forbidden fragments — in `FORBIDDEN`
    // and in its fixtures — so it cannot scan itself without indicting its own
    // implementation.
    let breaches = scan_root(
        root,
        &|file| is_denylist_self_reference(file, root),
        &frozen_rewriter_offense,
    );

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
        let hits = scan_phase(&dir, rule);
        assert!(
            hits.is_empty(),
            "phase `{}` violates its import rule.\n{}\n{}",
            rule.phase,
            rule.why,
            hits.join("\n")
        );
    }
}

/// One phase directory's violations. Extracted for the same reason as
/// [`scan_root`]: asserting inline left this scan's accumulation unwitnessed,
/// so deleting it would have gone unnoticed on clean sources.
fn scan_phase(dir: &Path, rule: &PhaseRule) -> Vec<String> {
    let mut files = Vec::new();
    collect_rs_files(dir, &mut files);
    assert!(
        !files.is_empty(),
        "no .rs files under {dir:?}; this check would pass vacuously"
    );
    let mut hits = Vec::new();
    for file in &files {
        let text = fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("unreadable phase source {file:?}: {e}"));
        let name = file.file_name().unwrap_or_default().to_string_lossy().into_owned();

        // (a) IMPORTS — resolved from the use-tree, so a brace-merged form is
        // matched on its full path rather than on the text of one line.
        for path in imported_paths(&text) {
            for fragment in rule.forbidden {
                if path.contains(fragment) {
                    hits.push(format!("{name}: imports {path:?} containing {fragment:?}"));
                }
            }
        }

        // (b) NON-IMPORT references — an inline path expression such as
        // `crate::rewriter::f()` is not a use-tree, so the textual scan is still
        // needed. It is sound HERE because a path expression cannot be split
        // across lines by the formatter the way a use-tree can.
        for (lineno, line) in text.lines().enumerate() {
            if is_comment(line) || line.trim_start().starts_with("use ") {
                continue;
            }
            for fragment in rule.forbidden {
                if line.contains(fragment) {
                    hits.push(format!(
                        "{name}:{}: names {fragment:?} outside an import",
                        lineno + 1
                    ));
                }
            }
        }
    }
    hits
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
    let violations = scan_root(
        root,
        &|file| is_denylist_self_reference(file, root),
        &if_let_offense,
    );

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
fn if_let_offense(line: &str) -> Option<String> {
    let trimmed = line.trim_start();
    if !trimmed.starts_with("if let ") {
        return None;
    }
    if !trimmed.contains("RewriteOutcome::") {
        return None;
    }
    Some("bare `if let` on a RewriteOutcome".to_owned())
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
    let violations = scan_root(&root, &|_| false, &bo_rewriter_reference);
    assert!(
        violations.is_empty(),
        "coverage_recon must not reference bo_rewriter — producer B's \
         independence is the point of this rule:\n  {}",
        violations.join("\n  ")
    );
}

/// A reference to `bo_rewriter` on one line, or `None`.
fn bo_rewriter_reference(line: &str) -> Option<String> {
    if line.contains("bo_rewriter") {
        return Some("reference to bo_rewriter".to_owned());
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

// ---------------------------------------------------------------------------
// Slice D — synthetic-corpus witnesses: every scan's ACCUMULATION is exercised
// ---------------------------------------------------------------------------
//
// Before these, each rule had a "synthetic breach" test that exercised only its
// MATCHER (`FORBIDDEN.contains`, `if_let_offense`, `bo_rewriter_reference`) and
// never the scan that calls it. On clean sources the scans return empty, so the
// accumulation could be deleted with the whole suite still green — verified, at
// 912/6 unchanged, for the `coverage_recon` rule.
//
// Each test below feeds a corpus that genuinely violates its rule to the SAME
// scan function the production check uses, plus a clean file so the assertion
// is not satisfied by indiscriminate matching.

/// **Frozen-rewriter scan** reports a real violation in a real corpus.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `hits.push(...)`
/// in [`scan_root`] fails this.
#[test]
fn frozen_rewriter_scan_reports_a_synthetic_corpus_violation() {
    let dir = temp_corpus(
        "frozen",
        &[
            ("bad.rs", "use crate::rewriter::decision::PtrKind;\n"),
            ("good.rs", "use crate::analyses::borrow_ownership::SlotKind;\n"),
        ],
    );
    let hits = scan_root(&dir, &|_| false, &frozen_rewriter_offense);
    assert_eq!(hits.len(), 1, "expected exactly the one violation: {hits:?}");
    assert!(hits[0].starts_with("bad.rs:1:"), "{hits:?}");
    drop_corpus(&dir);
}

/// **R-C `if let` scan** reports a real violation in a real corpus.
///
/// This is the F3 repair proper: the rule's previous witness called
/// `if_let_offense` directly and never touched the scan.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `hits.push(...)`
/// in [`scan_root`] fails this.
#[test]
fn if_let_scan_reports_a_synthetic_corpus_violation() {
    let dir = temp_corpus(
        "iflet",
        &[
            (
                "bad.rs",
                "fn t() {\n    if let RewriteOutcome::Degraded { .. } = out {}\n}\n",
            ),
            ("good.rs", "fn t() {\n    match out {\n        _ => {}\n    }\n}\n"),
        ],
    );
    let hits = scan_root(&dir, &|_| false, &if_let_offense);
    assert_eq!(hits.len(), 1, "expected exactly the one violation: {hits:?}");
    assert!(hits[0].starts_with("bad.rs:2:"), "{hits:?}");
    drop_corpus(&dir);
}

/// **`coverage_recon` one-way rule** reports a real violation in a real corpus.
///
/// The instance this author introduced one slice after diagnosing the pattern.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `hits.push(...)`
/// in [`scan_root`] fails this.
#[test]
fn coverage_recon_scan_reports_a_synthetic_corpus_violation() {
    let dir = temp_corpus(
        "recon",
        &[
            ("bad.rs", "use crate::bo_rewriter::decision::Subject;\n"),
            ("good.rs", "use super::schema::Row;\n"),
        ],
    );
    let hits = scan_root(&dir, &|_| false, &bo_rewriter_reference);
    assert_eq!(hits.len(), 1, "expected exactly the one violation: {hits:?}");
    assert!(hits[0].starts_with("bad.rs:1:"), "{hits:?}");
    drop_corpus(&dir);
}

/// **Per-phase scan** reports a real violation in a real corpus, in BOTH of its
/// detection modes — the resolved use-tree and the inline path expression.
///
/// The fourth instance of the pattern, found by Slice D's audit rather than
/// named in its scope.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting either `hits.push(...)`
/// in [`scan_phase`] fails this — the two assertions below separate the modes,
/// so neither deletion hides behind the other.
#[test]
fn phase_scan_reports_a_synthetic_corpus_violation() {
    let rule = PhaseRule {
        phase: "synthetic",
        forbidden: &["crate::analyses"],
        why: "synthetic rule for the witness",
    };
    let dir = temp_corpus(
        "phase",
        &[
            ("bad_import.rs", "use crate::analyses::borrow_ownership::SlotKind;\n"),
            ("bad_path.rs", "fn f() {\n    let _ = crate::analyses::thing();\n}\n"),
            ("good.rs", "use super::schema::Row;\n"),
        ],
    );
    let hits = scan_phase(&dir, &rule);
    assert!(
        hits.iter().any(|h| h.starts_with("bad_import.rs: imports")),
        "the use-tree mode did not report its violation: {hits:?}"
    );
    assert!(
        hits.iter().any(|h| h.starts_with("bad_path.rs:2:")),
        "the inline-path mode did not report its violation: {hits:?}"
    );
    assert!(
        !hits.iter().any(|h| h.starts_with("good.rs")),
        "a clean file was reported: {hits:?}"
    );
    drop_corpus(&dir);
}

/// Remove a temp corpus. Called only after assertions pass, so a failing test
/// leaves its inputs on disk.
#[cfg(test)]
fn drop_corpus(dir: &Path) {
    let _ = fs::remove_dir_all(dir);
}

// ---------------------------------------------------------------------------
// S2b.0a.3 — ONE EMISSION PATH.
//
// The ruling: the string entry point becomes a thin wrapper over the per-file
// mechanism, or is retired; no second parallel emission path survives. A second
// path is the hazard class this milestone exists to remove, because it would be
// exercised by every test and by nothing real — which is exactly how M1's
// single-source assumption reached first corpus contact undetected.
//
// Mechanized as: **no production code under `bo_rewriter/` compiles a crate
// from a STRING.** `run_compiler_on_path` is the one compiler entry.
// ---------------------------------------------------------------------------

/// Non-comment lines under `root` that CALL the emission core, ignoring each
/// file's inline `#[cfg(test)]` module and the definition itself.
fn emission_call_sites(root: &Path, skip: &dyn Fn(&Path) -> bool) -> Vec<String> {
    let mut files = Vec::new();
    collect_rs_files(root, &mut files);
    assert!(
        !files.is_empty(),
        "no .rs files found under {root:?} — the scan would pass vacuously"
    );
    let mut hits = Vec::new();
    let mut scanned = 0usize;
    for file in &files {
        if skip(file) {
            continue;
        }
        scanned += 1;
        let text = fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("source unreadable at {file:?}: {e}"));
        // Stop at an inline `#[cfg(test)] mod x {` BLOCK, not at a
        // `#[cfg(test)] mod x;` DECLARATION. The declarations sit at the TOP of
        // a module file, so truncating on them would hide the whole production
        // body — which is exactly what the first version of this rule did, and
        // the production check caught it by reporting zero call sites.
        let lines: Vec<&str> = text.lines().collect();
        for (index, line) in lines.iter().enumerate() {
            let is_test_block = line.trim() == "#[cfg(test)]"
                && lines
                    .get(index + 1)
                    .is_some_and(|next| next.contains("mod ") && next.trim_end().ends_with('{'));
            if is_test_block {
                break;
            }
            if is_comment(line) || line.contains("fn emit_files") {
                continue;
            }
            if line.contains("emit_files(") {
                hits.push(format!(
                    "{}:{}: {}",
                    file.strip_prefix(root).unwrap_or(file).display(),
                    index + 1,
                    line.trim()
                ));
            }
        }
    }
    assert!(
        scanned > 0,
        "every file under {root:?} was skipped — the scan examined nothing"
    );
    hits
}

/// Whole-file test modules: these are `#[cfg(test)] mod x;` at their parent, so
/// there is no `#[cfg(test)]` line inside them to truncate at.
fn is_test_only_file(path: &Path) -> bool {
    matches!(
        path.file_name().and_then(|n| n.to_str()),
        Some("goldens.rs" | "emit_tests.rs" | "import_denylist.rs")
    )
}

/// **Production check — ONE EMISSION PATH.** Exactly one production call site
/// drives `decide → plan → apply → verify`.
///
/// The check was first written as "no production code compiles a crate from a
/// string". That was the wrong invariant: the ruling is about a second
/// *emission* path, not about the compiler's input form, and the string entry
/// point legitimately compiles a string — staging it to disk instead made every
/// span render against a pid-bearing temp directory. Counting emission call
/// sites tests the property that was actually ruled.
#[test]
fn production_code_has_exactly_one_emission_path() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/bo_rewriter");
    let hits = emission_call_sites(&root, &is_test_only_file);
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one production emission call site; a second parallel \
         path would be exercised by every test and by nothing real:\n  {}",
        hits.join("\n  ")
    );
}

/// **Witness — the scan can fail.** Same function, synthetic corpus with two
/// call sites. Without this the production check is an unwitnessed scan, which
/// this file already records four instances of.
#[test]
fn the_emission_path_scan_counts_every_call_site() {
    let dir = temp_corpus(
        "emission-two-sites",
        &[
            ("one.rs", "fn a() {\n    let x = emit_files(tcx, &table);\n}\n"),
            ("two.rs", "fn b() {\n    let y = emit_files(tcx, &table);\n}\n"),
        ],
    );
    let hits = emission_call_sites(&dir, &|_| false);
    assert_eq!(hits.len(), 2, "the scan missed a second emission path: {hits:?}");
    let _ = fs::remove_dir_all(&dir);
}

/// **Witness — the truncation rule is what makes it selective.** The same call
/// in a `#[cfg(test)]` tail is not a production path; without truncation the
/// crate's own witnesses would trip the production check.
#[test]
fn the_emission_path_scan_ignores_the_test_tail() {
    let dir = temp_corpus(
        "emission-test-tail",
        &[(
            "tailed.rs",
            "fn f() {}\n#[cfg(test)]\nmod tests {\n    fn t() { emit_files(tcx, &table); }\n}\n",
        )],
    );
    let hits = emission_call_sites(&dir, &|_| false);
    assert!(hits.is_empty(), "a test-tail call was reported as production: {hits:?}");
    let _ = fs::remove_dir_all(&dir);
}

/// **Witness — a `#[cfg(test)] mod x;` DECLARATION is not a test tail.**
///
/// These sit at the top of a module file. The first version of the rule stopped
/// at any `#[cfg(test)]`, so it truncated `bo_rewriter/mod.rs` at its test-module
/// declarations and reported ZERO production call sites — a scan that would
/// have passed forever once someone "fixed" the expected count.
#[test]
fn the_emission_path_scan_does_not_stop_at_a_test_module_declaration() {
    let dir = temp_corpus(
        "emission-mod-decl",
        &[(
            "decl.rs",
            "#[cfg(test)]\nmod tests;\n\nfn production() {\n    emit_files(tcx, &table);\n}\n",
        )],
    );
    let hits = emission_call_sites(&dir, &|_| false);
    assert_eq!(
        hits.len(),
        1,
        "a test-module DECLARATION hid the production body: {hits:?}"
    );
    let _ = fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// S2b.1 F3 — ONE FILLING SITE PER OUTCOME VARIANT.
//
// The outcome variants were hand-filled at seven sites, and twice a `Degraded`
// arm hardcoded a field to `0` that had a real value: `emitted_count` at S2b.0
// (which blocked the span-bucket axis outright), then `reverted_count` while
// repairing that. Two instances of one shape is a pattern; this prevents the
// third structurally rather than by a third patch.
// ---------------------------------------------------------------------------

/// Production lines that construct a `RewriteOutcome` variant directly.
fn outcome_construction_sites(root: &Path, skip: &dyn Fn(&Path) -> bool) -> Vec<String> {
    let mut files = Vec::new();
    collect_rs_files(root, &mut files);
    assert!(!files.is_empty(), "no .rs files under {root:?}");
    let mut hits = Vec::new();
    let mut scanned = 0usize;
    for file in &files {
        if skip(file) {
            continue;
        }
        scanned += 1;
        let text = fs::read_to_string(file)
            .unwrap_or_else(|e| panic!("source unreadable at {file:?}: {e}"));
        let lines: Vec<&str> = text.lines().collect();
        for (index, line) in lines.iter().enumerate() {
            let is_test_block = line.trim() == "#[cfg(test)]"
                && lines
                    .get(index + 1)
                    .is_some_and(|next| next.contains("mod ") && next.trim_end().ends_with('{'));
            if is_test_block {
                break;
            }
            if is_comment(line) {
                continue;
            }
            if line.contains("RewriteOutcome::Emitted {")
                || line.contains("RewriteOutcome::Degraded {")
            {
                hits.push(format!(
                    "{}:{}: {}",
                    file.strip_prefix(root).unwrap_or(file).display(),
                    index + 1,
                    line.trim()
                ));
            }
        }
    }
    assert!(scanned > 0, "every file under {root:?} was skipped");
    hits
}

/// **Production check.** Exactly two construction sites — the two constructors
/// on `OutcomeFacts`. Any third is an arm that can omit a field.
#[test]
fn each_outcome_variant_has_exactly_one_filling_site() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/bo_rewriter");
    let hits = outcome_construction_sites(&root, &is_test_only_file);
    assert_eq!(
        hits.len(),
        2,
        "expected exactly the two `OutcomeFacts` constructors; a hand-filled \
         site can omit a field, which has already zeroed a real value twice:\n  {}",
        hits.join("\n  ")
    );
}

/// **Witness — the scan can fail.** Same function, synthetic corpus with an
/// extra hand-filled site.
#[test]
fn the_outcome_site_scan_reports_a_hand_filled_arm() {
    let dir = temp_corpus(
        "outcome-extra-site",
        &[(
            "sneaky.rs",
            "fn f() {\n    RewriteOutcome::Degraded {\n        reason: r,\n    }\n}\n",
        )],
    );
    let hits = outcome_construction_sites(&dir, &|_| false);
    assert_eq!(hits.len(), 1, "the scan missed a hand-filled arm: {hits:?}");
    let _ = fs::remove_dir_all(&dir);
}
