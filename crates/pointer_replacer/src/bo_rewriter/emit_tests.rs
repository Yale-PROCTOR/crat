//! **S2b.0a witnesses — multi-file emission.**
//!
//! These exist because M1's ten goldens are all single-source: the string entry
//! point was fully exercised by its own suite and simultaneously unexercised
//! against the shape it will be run on. 10 of the 20 frozen-corpus programs
//! carry subjects across 2–110 files, so "which file does this edit belong to"
//! is not a question the goldens could ever have asked.

use std::{
    collections::BTreeMap,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

use super::{Emission, decide_table, emit_files, plan::FileKey, verify};

static NEXT_FIXTURE: AtomicUsize = AtomicUsize::new(0);

/// A throwaway multi-file crate on disk. Removed on drop.
struct Fixture(PathBuf);

impl Fixture {
    fn new(files: &[(&str, &str)]) -> Self {
        let sequence = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "crat-emit-fixture-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).expect("create emission fixture directory");
        for (name, text) in files {
            let path = dir.join(name);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).expect("create fixture subdirectory");
            }
            fs::write(path, text).expect("write emission fixture file");
        }
        Self(dir)
    }

    fn root(&self) -> PathBuf {
        self.0.join("lib.rs")
    }

    /// Every file in the fixture tree, by relative path, with its bytes.
    /// Compared in-process rather than shelling out — a byte comparison here is
    /// the evidence, not a tool's summary of one.
    fn snapshot(&self) -> BTreeMap<PathBuf, Vec<u8>> {
        fn walk(dir: &std::path::Path, base: &std::path::Path, out: &mut BTreeMap<PathBuf, Vec<u8>>) {
            for entry in fs::read_dir(dir).expect("fixture tree readable") {
                let entry = entry.expect("fixture entry");
                let path = entry.path();
                if entry.file_type().expect("file type").is_dir() {
                    walk(&path, base, out);
                } else {
                    let key = path.strip_prefix(base).expect("under base").to_path_buf();
                    out.insert(key, fs::read(&path).expect("fixture file readable"));
                }
            }
        }
        let mut out = BTreeMap::new();
        walk(&self.0, &self.0, &mut out);
        out
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn emit(fixture: &Fixture) -> Emission {
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let table = decide_table(tcx).expect("fixture yields a decision table");
        emit_files(tcx, &table, &rustc_hash::FxHashSet::default()).expect("emission succeeds")
    })
    .expect("fixture compiles")
}

/// Emitted text for a file, matched on the file's *name* so the assertion does
/// not depend on how the compiler canonicalized the fixture's path.
fn text_for<'a>(emission: &'a Emission, name: &str) -> Option<&'a String> {
    emission.files.iter().find_map(|(key, text)| match key {
        FileKey::Real(path) if path.file_name()?.to_str()? == name => Some(text),
        _ => None,
    })
}

const ROOT_WITH_MODULE: &str = "#![allow(dead_code, unused_unsafe)]\npub mod m;\n";
const MODULE_SUBJECT: &str =
    "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n";

/// **RED (i).** A crate root plus a module, with the subject in the *module*:
/// the module's text is rewritten and the root — which has no subject — is not
/// emitted at all.
///
/// This is the shape 10 corpus programs have and no golden has: the file that
/// gets edited is not the file the compiler was pointed at.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `files.insert(..)` in `emit_files`'s per-file loop and this fails — nothing
/// is emitted for the module.
#[test]
fn a_subject_in_a_module_is_emitted_into_that_module() {
    let fixture = Fixture::new(&[("lib.rs", ROOT_WITH_MODULE), ("m.rs", MODULE_SUBJECT)]);
    let emission = emit(&fixture);

    let module = text_for(&emission, "m.rs").expect("the module was emitted");
    assert!(
        module.contains("p: &mut i32"),
        "the module's subject was not rewritten: {module}"
    );
    assert!(
        text_for(&emission, "lib.rs").is_none(),
        "the crate root has no subject and must not be emitted: {:?}",
        emission.files.keys().collect::<Vec<_>>()
    );
    assert!(emission.rollbacks.is_empty(), "{:?}", emission.rollbacks);
    assert!(emission.unplaceable.is_empty(), "{:?}", emission.unplaceable);
}

/// **RED (ii) — the file-collapse witness.** Subjects in BOTH files, with
/// *different pointee types*, so an edit landing in the wrong file is visible
/// rather than merely mis-positioned.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** collapse the grouping
/// in `emit_files` — key every edit under one `FileKey` — and this fails. That
/// is the exact defect the map shape exists to make unrepresentable: offsets are
/// file-relative, so a collapsed plan splices one file's ranges into another's
/// text and produces a plausible-looking result.
#[test]
fn each_edit_lands_in_its_own_file() {
    let fixture = Fixture::new(&[
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod other;\npub unsafe fn root_bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
        (
            "other.rs",
            "pub unsafe fn other_bump(q: *mut i64) -> i64 {\n    *q += 1;\n    *q\n}\n",
        ),
    ]);
    let emission = emit(&fixture);

    assert_eq!(
        emission.files.len(),
        2,
        "both files carry a subject, so both must be emitted: {:?}",
        emission.files.keys().collect::<Vec<_>>()
    );
    let root = text_for(&emission, "lib.rs").expect("root emitted");
    let other = text_for(&emission, "other.rs").expect("module emitted");

    assert!(
        root.contains("p: &mut i32"),
        "the root's own subject was not rewritten in the root: {root}"
    );
    assert!(
        other.contains("q: &mut i64"),
        "the module's own subject was not rewritten in the module: {other}"
    );
    // The discriminator: each file kept ITS pointee type. A collapsed grouping
    // splices the other file's range and cannot preserve both.
    assert!(
        !root.contains("i64"),
        "the module's edit leaked into the root: {root}"
    );
    assert!(
        !other.contains("i32"),
        "the root's edit leaked into the module: {other}"
    );
    assert!(emission.rollbacks.is_empty(), "{:?}", emission.rollbacks);
}

/// **RED (iii) — the unplaceable guard.** A macro-generated declaration has no
/// source range anyone can splice; it is recorded with its reason and
/// attribution rather than silently skipped.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `span.from_expansion()` guard in `emit_files`'s `span_to_loc` and this fails
/// — `unplaceable` is empty and the decision disappears without a trace.
#[test]
fn a_macro_generated_declaration_is_recorded_as_unplaceable() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\nmacro_rules! mk {\n    () => {\n        pub unsafe fn mac_bump(p: *mut i32) -> i32 {\n            *p += 1;\n            *p\n        }\n    };\n}\nmk!();\n",
    )]);
    let emission = emit(&fixture);

    assert_eq!(
        emission.unplaceable.len(),
        1,
        "the macro-generated subject must be recorded, not dropped: {:?}",
        emission.unplaceable
    );
    assert_eq!(
        emission.unplaceable[0].reason,
        "span is macro-generated and cannot be spliced into source"
    );
    assert!(
        emission.unplaceable[0].detail.contains('p'),
        "the record must attribute the subject: {:?}",
        emission.unplaceable[0]
    );
    assert!(
        emission.files.is_empty(),
        "nothing is emitted for an unplaceable subject: {:?}",
        emission.files.keys().collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// S2b.0a.2 — verify from a temp copy. The isolation witness lands HERE, before
// any corpus contact, by ruling: the frozen tree's digest is a standing
// invariant, so the guard that protects it must exist before the first run that
// could threaten it.
// ---------------------------------------------------------------------------

/// **RED.** A rewritten two-file crate compiles *as a crate* from the temp copy
/// — which the string gate cannot express, because modules resolve relative to
/// the root's directory.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the overwrite
/// loop in `materialize` and this fails. The `contains` assertion is what makes
/// that deletion detectable: the untouched copy still type-checks, so a witness
/// that only asserted the gate passed would survive the deletion — the
/// outcome-counting shape that already cost one repair this slice.
#[test]
fn a_rewritten_two_file_crate_type_checks_from_a_temp_copy() {
    let fixture = Fixture::new(&[("lib.rs", ROOT_WITH_MODULE), ("m.rs", MODULE_SUBJECT)]);
    let emission = emit(&fixture);
    let temp = verify::materialize(&fixture.root(), &emission.files).expect("materialize");

    let copied = fs::read_to_string(temp.root().parent().expect("temp dir").join("m.rs"))
        .expect("module present in the copy");
    assert!(
        copied.contains("p: &mut i32"),
        "the copy does not carry the rewrite: {copied}"
    );
    assert!(
        verify::type_checks_crate(temp.root()),
        "the rewritten crate must type-check as a crate"
    );
}

/// **Non-vacuity.** The temp-copy gate can FAIL. Without this, every passing
/// result above is compatible with a gate that always says yes.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** make
/// `type_checks_crate` return `true` unconditionally and this fails.
#[test]
fn a_broken_rewrite_fails_the_temp_copy_gate() {
    let fixture = Fixture::new(&[("lib.rs", ROOT_WITH_MODULE), ("m.rs", MODULE_SUBJECT)]);
    let mut emission = emit(&fixture);
    for text in emission.files.values_mut() {
        *text = "pub unsafe fn bump(p: &mut i32) -> i32 {\n    let _x: u8 = \"not a u8\";\n    *p\n}\n"
            .to_owned();
    }
    let temp = verify::materialize(&fixture.root(), &emission.files).expect("materialize");

    assert!(
        !verify::type_checks_crate(temp.root()),
        "a crate with a type error passed the hard gate"
    );
}

/// **THE ISOLATION WITNESS.** Emitting and verifying leaves the input tree
/// byte-identical.
///
/// This is the guard standing between the rewriter and the frozen `rs-crown`
/// corpus, whose digest is an invariant of the whole evaluation. It is asserted
/// on a throwaway fixture precisely so it never has to be discovered on the
/// corpus.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** point `materialize`'s
/// write at the ORIGINAL path instead of the copy and this fails.
#[test]
fn materializing_never_touches_the_original_tree() {
    let fixture = Fixture::new(&[("lib.rs", ROOT_WITH_MODULE), ("m.rs", MODULE_SUBJECT)]);
    let before = fixture.snapshot();

    let emission = emit(&fixture);
    let temp = verify::materialize(&fixture.root(), &emission.files).expect("materialize");
    let _ = verify::type_checks_crate(temp.root());

    let after = fixture.snapshot();
    assert_eq!(
        before, after,
        "the input tree was modified by emit+verify; the frozen corpus would be next"
    );
}

// ---------------------------------------------------------------------------
// S2b.0a.4 — CORPUS SMOKE. First contact between emission and a real
// multi-file program. rgba is the smallest genuinely CROSS-FILE program in the
// frozen corpus (14 subject rows over 2 files); bst and avl are multi-file
// crates whose subjects all sit in one file, so they would not exercise
// grouping at all.
//
// Guards, per ruling: temp copies only, and the frozen tree is asserted
// byte-identical afterwards. The corpus-wide digest is checked by the
// invocation around this test.
// ---------------------------------------------------------------------------

/// Bytes of every `.rs` file under `dir`, by path.
fn tree_snapshot(dir: &std::path::Path) -> BTreeMap<PathBuf, Vec<u8>> {
    fn walk(dir: &std::path::Path, out: &mut BTreeMap<PathBuf, Vec<u8>>) {
        for entry in fs::read_dir(dir).expect("corpus dir readable") {
            let entry = entry.expect("corpus entry");
            let path = entry.path();
            if entry.file_type().expect("file type").is_dir() {
                walk(&path, out);
            } else {
                out.insert(path.clone(), fs::read(&path).expect("corpus file readable"));
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(dir, &mut out);
    out
}

#[test]
#[ignore = "S2b.0a.4 corpus smoke: reads the frozen rs-crown tree"]
fn rgba_smoke_emits_and_verifies_from_a_temp_copy() {
    let crate_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/rs-crown/rgba");
    let root = crate_dir.join("lib.rs");
    assert!(root.is_file(), "frozen corpus input missing: {root:?}");

    let before = tree_snapshot(&crate_dir);
    let outcome = super::rewrite_m1_path(&root);
    let after = tree_snapshot(&crate_dir);

    assert_eq!(
        before, after,
        "THE FROZEN CORPUS WAS MODIFIED by an emission run — temp copies only"
    );

    match outcome {
        super::RewriteOutcome::Emitted {
            files,
            emitted_count,
            degradations,
            unplaceable,
            ..
        } => {
            println!(
                "RGBA-SMOKE emitted_count={emitted_count} files_touched={} \
                 degradations={} unplaceable={}",
                files.len(),
                degradations.len(),
                unplaceable.len()
            );
            for key in files.keys() {
                println!("RGBA-SMOKE file={key:?}");
            }
            assert!(
                unplaceable.is_empty(),
                "unplaceable is expected-zero on this corpus: {unplaceable:?}"
            );
            // The POINT of this smoke: emission reached more than one file of a
            // real program. Without these two, the witness passes on an
            // emission that touched nothing — the outcome-counting shape that
            // has already cost two repairs in this slice sequence.
            assert!(
                emitted_count >= 1,
                "the smoke must emit at least one subject, not merely succeed"
            );
            assert!(
                files.len() >= 2,
                "rgba's subjects span two files; a run that touched {} file(s) \
                 did not exercise cross-file emission at all",
                files.len()
            );
        }
        super::RewriteOutcome::Degraded { reason, degradations, .. } => {
            panic!(
                "rgba did not emit: {reason} ({} degradation(s))",
                degradations.len()
            );
        }
    }
}

/// **S2b.1.2 RED — the batch revert loop.** A crate with one GOOD rewrite and
/// one that breaks type-checking: the bad one is taken back, the good one
/// survives, and the crate emits.
///
/// This is the whole point of the per-function gate. Under the old whole-crate
/// verdict this crate produced NOTHING — one bad subject discarded every good
/// rewrite in the program, which S2b.0 measured as 10 of 20 corpus programs.
///
/// `bad.rs` mirrors `ht`'s real corpus shape (a rewritten parameter stored into
/// a raw-pointer struct field); `good.rs` mirrors `g01`.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove
/// `reverted.extend(newly)` so nothing is ever taken back — the loop makes no
/// progress, escalates, and this fails.
#[test]
fn a_bad_rewrite_is_reverted_and_the_good_one_survives() {
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n"),
        ("good.rs", "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n"),
        ("bad.rs", BREAKS_ON_REWRITE),
    ]);

    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            files,
            emitted_count,
            degradations,
            ..
        } => {
            let reverted: Vec<_> = degradations
                .iter()
                .filter(|d| {
                    d.reason == super::decision::DegradeReason::RevertedAfterVerifyFailure
                })
                .collect();
            assert!(
                !reverted.is_empty(),
                "nothing was recorded as reverted, so the crate passed for some \
                 other reason: {degradations:?}"
            );
            assert!(
                emitted_count >= 1,
                "the GOOD rewrite was discarded too — the loop reverted more \
                 than the error attributed"
            );
            let good = files
                .iter()
                .find(|(k, _)| format!("{k:?}").contains("good.rs"))
                .map(|(_, text)| text.clone())
                .expect("good.rs was emitted");
            assert!(
                good.contains("p: &mut i32"),
                "the good rewrite did not survive: {good}"
            );
            let bad = files.iter().find(|(k, _)| format!("{k:?}").contains("bad.rs"));
            assert!(
                bad.is_none_or(|(_, text)| !text.contains("value: &")),
                "the bad rewrite survived the revert: {bad:?}"
            );
        }
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("the loop failed to recover a partially-bad crate: {reason}")
        }
    }
}

/// **S2b.1.2 RED — ACCOUNTING through the loop.** A reverted subject moves from
/// emitted to degraded under its own reason key, so
/// `emitted_final + degraded` still equals the subject count.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** stop pushing the
/// `RevertedAfterVerifyFailure` degradations and this fails — the identity
/// loses exactly the reverted subjects.
#[test]
fn the_accounting_identity_survives_a_revert() {
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n"),
        ("good.rs", "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n"),
        ("bad.rs", BREAKS_ON_REWRITE),
    ]);
    // Subject count from a NO-LOOP emission: what the decision phase decided,
    // which the loop must not change.
    // PLACED subjects only, as of S2b.3. `emitted` counts placements, so an
    // unplaceable decision belongs to neither side of this identity — it is
    // accounted for in the corpus identity `emitted + degraded + unplaceable`,
    // not in the loop's. Zero on this fixture either way; the derivation is
    // corrected so it stays true when it is not.
    let subjects = {
        let emission = emit(&fixture);
        emission.plan.by_file.values().map(Vec::len).sum::<usize>()
    };

    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            emitted_count,
            degradations,
            ..
        } => {
            let reverted = degradations
                .iter()
                .filter(|d| {
                    d.reason == super::decision::DegradeReason::RevertedAfterVerifyFailure
                })
                .count();
            assert_eq!(
                emitted_count + reverted,
                subjects,
                "emitted {emitted_count} + reverted {reverted} != {subjects} \
                 planned subjects — the loop lost or invented one"
            );
        }
        super::RewriteOutcome::Degraded { reason, .. } => panic!("{reason}"),
    }
}


// ---------------------------------------------------------------------------
// S2b.1.1 witnesses — structural diagnostic capture. FIXTURE-VALIDATED; the
// cross-check against the rendered parser's 86 corpus diagnostics runs at 1.4.
// ---------------------------------------------------------------------------

/// The two-file crate whose rewrite breaks it, mirroring `ht`'s corpus shape:
/// a rewritten parameter stored into a raw-pointer struct field.
const BREAKS_ON_REWRITE: &str = "pub struct Holder {\n    pub slot: *mut i32,\n}\npub unsafe fn stash(value: *mut i32, holder: *mut Holder) {\n    (*holder).slot = value;\n}\n";

fn diagnose_after_rewrite(files: &[(&str, &str)]) -> (verify::Diagnosis, Fixture) {
    let fixture = Fixture::new(files);
    let emission = emit(&fixture);
    let temp = verify::materialize(&fixture.root(), &emission.files).expect("materialize");
    let diagnosis = verify::diagnose_crate(temp.root());
    (diagnosis, fixture)
}

/// **RED.** A type error is located structurally — file and line, straight from
/// the diagnostic's primary span, with no rendered text parsed.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `diags.lock().push(..)` in `Capture::emit_diagnostic` and this fails.
#[test]
fn structural_capture_locates_a_type_error() {
    let (d, _fixture) = diagnose_after_rewrite(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod m;\n"),
        ("m.rs", BREAKS_ON_REWRITE),
    ]);
    assert_eq!(d.diags.len(), 1, "expected one located diagnostic: {d:?}");
    assert_eq!(d.diags[0].line, 5, "the store is on line 5: {:?}", d.diags[0]);
    assert!(
        d.diags[0].file.ends_with("m.rs"),
        "located in the wrong file: {:?}",
        d.diags[0]
    );
}

/// **RED — COUNT INDEPENDENCE.** The error count comes from `Level` alone, never
/// from extraction. rustc emits a spanless error-level summary alongside the
/// located error, so the counts genuinely differ: **2 counted, 1 located**.
///
/// That gap is what makes this witness able to fail at all — without a naturally
/// spanless diagnostic, `errors == diags.len()` would hold either way and the
/// mutation below would be ineffective.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** derive the count from
/// extraction (`errors: diags.len()`) and this fails, 1 against 2.
#[test]
fn the_error_count_comes_from_level_not_from_extraction() {
    let (d, _fixture) = diagnose_after_rewrite(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod m;\n"),
        ("m.rs", BREAKS_ON_REWRITE),
    ]);
    assert_eq!(d.errors, 2, "error count must come from Level: {d:?}");
    assert_eq!(
        d.diags.len(),
        1,
        "one of the two errors is spanless and cannot be located — that is \
         precisely why the count must not be derived from extraction: {d:?}"
    );
    assert!(
        d.errors > d.diags.len(),
        "a dropped diagnostic would lower the count and fake progress for the \
         no-progress detector"
    );
}

/// **RED.** Direction is what distinguishes whose rewrite caused the error;
/// containment only says where it is.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** swap the two arms of
/// `classify` and this fails.
#[test]
fn direction_identifies_a_rewritten_value_flowing_into_a_raw_context() {
    let (d, _fixture) = diagnose_after_rewrite(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod m;\n"),
        ("m.rs", BREAKS_ON_REWRITE),
    ]);
    assert_eq!(
        d.diags[0].direction,
        verify::Direction::RewrittenIntoRaw,
        "the rewritten parameter flows INTO a raw context, so the containing \
         function's own rewrite is the culprit: {:?}",
        d.diags[0]
    );
}

/// **Non-vacuity, and the WARNING filter.** A crate that type-checks yields no
/// errors — without this, every count above is compatible with a capture that
/// reports errors unconditionally.
///
/// The fixture **deliberately emits a warning** (`unused_variables`, with no
/// crate-level `allow`) so that the `Level` filter is load-bearing here.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** drop the `Level` filter
/// in `emit_diagnostic` and this fails — the warning is counted as an error.
///
/// **Written after the first version SURVIVED that deletion.** It used the
/// `ROOT_WITH_MODULE` fixture, whose `#![allow(dead_code, unused_unsafe)]`
/// suppresses every warning, so there was nothing for the filter to filter and
/// the doc comment's claim that "the fixture emits warnings" was simply untrue.
#[test]
fn a_clean_crate_yields_no_diagnostics() {
    let (d, _fixture) = diagnose_after_rewrite(&[
        ("lib.rs", "pub mod m;\n"),
        (
            "m.rs",
            "pub unsafe fn bump(p: *mut i32) -> i32 {\n    let unused_thing = 5;\n    *p += 1;\n    *p\n}\n",
        ),
    ]);
    assert_eq!(d.errors, 0, "a clean rewrite reported errors: {d:?}");
    assert!(d.diags.is_empty(), "{d:?}");
    assert_eq!(d.unrenderable, 0, "{d:?}");
}

/// **S2b.1.3 — the CAP arm of the dual termination, witnessed.**
///
/// The cap is configured to its boundary (0 rounds) on a fixture that genuinely
/// needs one, so reaching the cap is real behaviour rather than a manufactured
/// loop.
///
/// **Why the boundary rather than a multi-round fixture.** The coupled shape
/// (`outer` calls `inner`, both rewritten, `inner`'s body carrying the error)
/// was built and MEASURED: it converges in ONE round, `reverted=2`, because
/// BATCH-revert takes every attributed function in the same round. Constraint
/// (a) is precisely what collapses a cascade into one round, so multi-round
/// convergence is rare *by design* and the cap is hard to reach naturally. That
/// is the mechanism working, not a gap in the fixture.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** disable the cap check
/// and this fails — the loop converges and returns `Emitted`.
#[test]
fn the_round_cap_stops_the_loop() {
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n"),
        ("good.rs", "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n"),
        ("bad.rs", BREAKS_ON_REWRITE),
    ]);
    match super::rewrite_m1_path_with_cap(&fixture.root(), 0) {
        super::RewriteOutcome::Emitted { escalated, bisect_probes, .. } => {
            let reason = escalated.expect("the cap must have escalated");
            assert!(
                reason.contains("round cap"),
                "escalated for the wrong reason: {reason}"
            );
            assert!(bisect_probes > 0, "escalation did not reach bisect");
        }
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("bisect failed to recover after the cap fired: {reason}")
        }
    }
}

/// `caller` passes one rewritten parameter (`q`) through and one raw parameter
/// (`r`) to `callee`, which IS rewritten. That is heman's inverted shape: the
/// culprit is the CALLEE, while the error lands inside the caller.
const INVERTED: &str = "pub unsafe fn callee(p: *mut i32) -> i32 {\n    *p\n}\npub unsafe fn caller(q: *mut i32, r: *mut i32) -> i32 {\n    *q + callee(r)\n}\n";

/// Force `caller`'s `r` to stay raw, so the rewritten `callee` is reached with a
/// raw pointer. A1's `CallSiteNotAdapted` normally prevents this — which is why
/// it is injected at the phase boundary rather than written as source.
fn keep_r_raw(table: &mut super::decision::DecisionTable) {
    for (subject, decision) in &mut table.entries {
        // Force the CALLEE to be rewritten — A1 degrades it precisely because
        // its call site is unadapted, which is the guard this injection exists
        // to step around.
        if subject.param_name.as_deref() == Some("p") {
            *decision = super::decision::Decision::Ref { mutable: false };
        }
        if subject.param_name.as_deref() == Some("q") {
            *decision = super::decision::Decision::Ref { mutable: false };
        }
        if subject.param_name.as_deref() == Some("r") {
            *decision = super::decision::Decision::Degraded(super::decision::Degradation {
                subject: "caller::r".to_owned(),
                site: "<injected>".to_owned(),
                reason: super::decision::DegradeReason::CallSiteNotAdapted,
            });
        }
    }
}

/// **S2b.1.3 — the NO-PROGRESS DETECTOR arm, witnessed.**
///
/// The inverted-direction shape: the error lands inside `caller`, so span
/// attribution reverts `caller` — but the culprit is `callee`, and the error
/// survives. The detector sees the error count fail to fall and escalates.
///
/// **Why injection is legitimate here.** This is a DERIVED breach shape, not an
/// invention: reality emits it (1 of 86 corpus diagnostics, in heman), and A1's
/// `CallSiteNotAdapted` is exactly what normally prevents it — so it cannot be
/// written as ordinary source. The between-phase hook exists to test downstream
/// phases against shapes the upstream guard suppresses.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** disable the
/// no-progress check and this fails — the loop no longer escalates.
#[test]
fn the_no_progress_detector_escalates_when_attribution_is_wrong() {
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod m;\n"),
        ("m.rs", INVERTED),
    ]);
    match super::rewrite_m1_path_injected(&fixture.root(), 8, &keep_r_raw) {
        super::RewriteOutcome::Emitted { escalated, bisect_probes, .. } => {
            let reason = escalated.expect(
                "the loop converged on a shape whose culprit it cannot \
                 attribute — attribution silently got away with it",
            );
            assert!(
                reason.contains("no progress"),
                "escalated, but not via the detector: {reason}"
            );
            assert!(
                bisect_probes > 0,
                "the detector fired but (C) never ran: {reason}"
            );
        }
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("bisect failed to recover the inverted shape: {reason}")
        }
    }
}

/// Duplicate every entry, so `plan` emits two identical edits per subject and
/// `apply` must reject the second as overlapping.
fn duplicate_entries(table: &mut super::decision::DecisionTable) {
    let cloned = table.entries.clone();
    table.entries.extend(cloned);
}

/// **S2b.1.3 — the ROLLBACK guard, witnessed where it actually fires.**
///
/// An incoherent plan (two identical edits per subject) is rejected by the
/// PRE-LOOP structural gate, before any revert round and before bisect —
/// `bisect_probes == 0` is what proves it never got that far.
///
/// **This also locates the arm.** The post-bisect guard's `rollbacks` check was
/// suspected unwitnessed; measuring shows it is *unreachable* rather than
/// untested, because `render` applies a SUBSET of edits that already produced no
/// rollbacks, and dropping edits cannot create an overlap, an out-of-bounds
/// range, or a char-boundary violation. That arm is a stated control at its
/// guard; this witness covers the arm that can fire.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `emission.rollbacks` check and this fails — the deduped edit set emits and
/// type-checks, so an incoherent plan passes silently.
#[test]
fn an_incoherent_plan_is_rejected_before_the_loop() {
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod m;\n"),
        ("m.rs", MODULE_SUBJECT),
    ]);
    match super::rewrite_m1_path_injected(&fixture.root(), 8, &duplicate_entries) {
        super::RewriteOutcome::Degraded { reason, bisect_probes, .. } => {
            assert!(
                reason.contains("rolled back"),
                "rejected for the wrong reason: {reason}"
            );
            assert_eq!(
                bisect_probes, 0,
                "an incoherent plan reached bisect instead of being rejected"
            );
        }
        super::RewriteOutcome::Emitted { .. } => {
            panic!("an incoherent plan emitted")
        }
    }
}

/// **S2b.1 F3 — a FAILING outcome carries what the run attempted.**
///
/// Both outcome variants are built at exactly one site each (enforced by
/// `each_outcome_variant_has_exactly_one_filling_site`), so this witnesses the
/// field at the site every `Degraded` flows through.
///
/// **Why not an end-to-end brotli-shaped fixture.** brotli's `Degraded` arose
/// because bisect returned a non-compiling set — the F2 defect. With candidates
/// derived from the plan's `owner_fn` domain the base case holds by
/// construction, so that shape should no longer be reachable; the remaining
/// `Degraded`-with-reverted paths are the budget deferral and a materialize IO
/// error, neither constructible in a unit test without an env knob or an
/// injected filesystem failure. Witnessing the filling site is the honest
/// substitute, and the corpus re-run is what checks the shape is gone.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** re-zero
/// `reverted_count` in `OutcomeFacts::degraded` and this fails.
#[test]
fn a_failing_outcome_carries_its_reverted_count() {
    let facts = super::OutcomeFacts {
        emitted_count: 7,
        reverted_count: 3,
        files_touched: 2,
        attribution_blind: 1,
        ..Default::default()
    };
    match facts.degraded("escalation-deferred: budget".to_owned()) {
        super::RewriteOutcome::Degraded {
            emitted_count,
            reverted_count,
            files_touched,
            attribution_blind,
            ..
        } => {
            assert_eq!(
                reverted_count, 3,
                "a failing outcome zeroed its revert count — the defect this \
                 structure exists to prevent, twice over"
            );
            assert_eq!(emitted_count, 7, "the ATTEMPT must survive the failure");
            assert_eq!(files_touched, 2);
            assert_eq!(attribution_blind, 1);
        }
        super::RewriteOutcome::Emitted { .. } => panic!("degraded() built an Emitted"),
    }
}

/// **brotli investigation (a) — PRISTINE-COPY CONTROL.**
///
/// Materialize brotli with ZERO edits and type-check the copy. This is the
/// `k == candidates.len()` base case in isolation: if an unedited copy does not
/// compile, the base case was never testable for brotli and the failure is an
/// environment/temp-copy defect rather than a loop defect.
#[test]
#[ignore = "brotli control: one full type-check of the frozen corpus program"]
fn zz_brotli_pristine_copy_control() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/rs-crown/brotli/lib.rs");
    assert!(root.is_file(), "frozen input missing: {root:?}");

    // IN PLACE, no copy: distinguishes "the temp copy breaks it" from "the
    // input never passed this gate".
    let in_place = verify::diagnose_crate(&root);
    println!(
        "BROTLI-CONTROL in_place errors={} diags={}",
        in_place.errors,
        in_place.diags.len()
    );
    let empty = BTreeMap::new();
    let temp = verify::materialize(&root, &empty).expect("materialize pristine copy");
    let d = verify::diagnose_crate(temp.root());
    println!(
        "BROTLI-CONTROL pristine errors={} diags={} unrenderable={}",
        d.errors,
        d.diags.len(),
        d.unrenderable
    );
    // The OLD gate semantics: FatalError propagation only, which is what
    // `type_checks_crate` meant before 1.1 routed it through `diagnose_crate`.
    let old_gate = ::utils::compilation::run_compiler_on_path(temp.root(), |tcx| {
        ::utils::type_check(tcx);
    })
    .is_ok();
    println!("BROTLI-CONTROL old_gate_is_ok={old_gate} new_gate_passes={}", d.errors == 0);
    for x in d.diags.iter().take(8) {
        println!("BROTLI-CONTROL diag {}:{} {:?}", x.file, x.line, x.direction);
        println!("BROTLI-CONTROL   msg={}", &x.message[..x.message.len().min(160)]);
    }
}

/// **S2b.2 repair — the probe instrument must carry its payload.**
///
/// `diagnose_once` returns what the verify compile CAPTURED. This pins that it
/// is non-empty for a fixture with a known diagnostic — the test that did not
/// exist when the differential gate moved the payload assignment below the
/// `probe_only` early return, leaving `run_m1_diag` reporting
/// `struct_diags=0 status=ok` for every program from 2026-08-04 14:49 until
/// this repair.
///
/// # Why this fixture cannot go quiet
///
/// Non-emptiness rests on a **pre-existing** `invalid_reference_casting` error
/// in the unmodified source, not on the rewriter producing one. A witness that
/// depended on the rewrite emitting a *bad* rewrite would go silently vacuous
/// the moment the rewriter improved — which is the failure shape this file
/// already records four instances of. Probe mode returns the RAW capture, so
/// the baseline diagnostic is exactly what reaches the assertion.
///
/// # Branch taken (Rider 7)
///
/// `tree_base = Some(root)` — a real multi-file tree materialized to a temp
/// copy, returning through the `probe_only` arm on the loop's FIRST iteration.
/// **This is the corpus's branch**: `run_m1_diag` drives every one of the 20
/// programs through the same path. The string-entry branch
/// (`materialize_single_file`) is not exercised here and is not what the
/// transfer measures.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** delete
/// `facts.first_diags = diagnosis.diags.clone()` from the `probe_only` block —
/// reproducing the regression exactly — and this fails on an empty set.
#[test]
fn diagnose_once_returns_the_captured_diagnostics_not_an_empty_set() {
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod m;\n"),
        (
            "m.rs",
            "pub unsafe fn preexisting(v: &i32) {\n    *(v as *const i32 as *mut i32) = 7;\n}\npub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
    ]);

    let (observed_root, diags) = super::diagnose_once(&fixture.root()).expect("the probe ran");

    assert!(
        !diags.is_empty(),
        "the probe returned an empty capture for a fixture with a known \
         diagnostic — this is the zeroed payload wearing an ok status, and it \
         is what `run_m1_diag` reported for all 20 programs"
    );
    assert!(
        diags.iter().any(|d| d.line > 0 && !d.file.is_empty()),
        "the payload carries no located diagnostic, so the transfer would have \
         nothing to compare: {diags:?}"
    );
    // The FRAME must fit the payload. A root that does not canonicalize its own
    // diagnostics is worse than no root: every path would key as itself and the
    // transfer would compare absolute paths while believing it compared
    // relative ones.
    assert!(
        diags.iter().any(|d| {
            let relative = verify::crate_relative(&d.file, &observed_root);
            relative != d.file && !relative.starts_with('/')
        }),
        "no diagnostic is under the observed root {observed_root:?}, so the \
         frame does not describe the capture: {diags:?}"
    );
}

/// **S2b.1 — a BASELINE-MASKED error must not gate.**
///
/// The fixture denies `unused_variables`, so its UNMODIFIED source already
/// reports an error-level diagnostic. The rewrite does not add one, so the crate
/// must still emit — brotli's shape in miniature, where an absolute gate made
/// even revert-all unsatisfiable.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** gate on the absolute
/// count (`diagnosis.errors == 0`) instead of the differential and this fails.
#[test]
fn a_baseline_error_does_not_gate_the_rewrite() {
    // Mirrors brotli's ACTUAL baseline diagnostic: `invalid_reference_casting`
    // is deny-by-default and, unlike a crate-level `#![deny(..)]`, does not
    // abort the decision-phase compile — which is why brotli decides 126
    // subjects and only fails at verify.
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod m;\n"),
        (
            "m.rs",
            "pub unsafe fn preexisting(v: &i32) {\n    *(v as *const i32 as *mut i32) = 7;\n}\npub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
    ]);
    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            files,
            bisect_probes,
            escalated,
            ..
        } => {
            let text = text_for_any(&files).expect("something was emitted");
            assert!(
                text.contains("p: &mut i32"),
                "the rewrite was withheld because of a pre-existing error: {text}"
            );
            // It must emit on the LOOP's clean exit, not be recovered by bisect.
            // The differential lives at three sites (loop exit, bisect probe,
            // final guard); without pinning the path, mutating one leaves the
            // fixture recoverable by the others and the witness survives.
            assert_eq!(
                bisect_probes, 0,
                "the baseline error forced an escalation instead of being masked"
            );
            assert!(
                escalated.is_none(),
                "escalated on a baseline-masked error: {escalated:?}"
            );
        }
        super::RewriteOutcome::Degraded { reason, .. } => panic!(
            "a pre-existing baseline error gated the rewrite — the absolute-gate \
             failure mode that made brotli's base case unsatisfiable: {reason}"
        ),
    }
}

fn text_for_any(files: &BTreeMap<FileKey, String>) -> Option<String> {
    files.values().next().cloned()
}

/// **S2b.1 — a NEW error of a MASKED class must still gate.**
///
/// Multiset semantics, witnessed directly: one occurrence of a key is masked by
/// a baseline of one; a SECOND occurrence is novel. Without this the gate would
/// go blind to rewrite-introduced violations of exactly the class it masks,
/// which for the real corpus is reference casting.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** compare presence rather
/// than count in `Baseline::novel` and this fails — the repeat is masked.
#[test]
fn a_repeat_of_a_masked_class_is_still_novel() {
    let root = std::path::Path::new("/p/crate");
    let diag = |line: usize| verify::Diag {
        file: "/p/crate/src/x.rs".to_owned(),
        line,
        message: "reference casting".to_owned(),
        direction: verify::Direction::Other,
        code: None,
    };
    let baseline = verify::Baseline {
        keys: std::iter::once((verify::baseline_key(&diag(1), root), 1)).collect(),
        errors: 1,
        messages_embedding_root: 0,
    };

    // One occurrence: masked — and at a DIFFERENT line, so the key is stable
    // under the line drift every edit above it causes.
    assert!(
        baseline.novel(&[diag(42)], root).is_empty(),
        "a baseline error moved by an edit was reported as novel"
    );
    // Two occurrences: the second is novel.
    let pair = [diag(42), diag(99)];
    let novel = baseline.novel(&pair, root);
    assert_eq!(
        novel.len(),
        1,
        "a rewrite-introduced repeat of a masked class was masked too"
    );
    assert_eq!(novel[0].line, 99);
}

// ---------------------------------------------------------------------------
// F.1 — the canonicalizer's KEY AGREEMENT. Rider 7: each fixture names the
// branch it exercises, and the corpus branch is covered.
// ---------------------------------------------------------------------------

/// **W1 — the two sides key the same logical file identically.**
///
/// **Rider 7 branch: UNDER-ROOT — the branch the corpus takes.** The roots are
/// deliberately CORPUS-SHAPED: one carries `rs-crown` as a path component, the
/// other a `crat-verify`-style temp name. With neutral roots a resurrected
/// string special case would take its magic branch on neither side and this
/// witness would pass while the resurrection survived.
///
/// *Mutation-tested, Rider 0 order.* **Deletions, each must fail:**
/// (i) reintroduce a basename normalization on one side;
/// (ii) reintroduce the `/rs-crown/` split.
#[test]
fn both_sides_key_the_same_file_identically() {
    let original_root = std::path::Path::new("/home/u/dev/benchmarks/rs-crown/brotli");
    let observed_root = std::path::Path::new("/var/folders/T/crat-verify-4242-0");

    let key_of = |path: &str, root: &std::path::Path| {
        verify::baseline_key(
            &verify::Diag {
                file: path.to_owned(),
                line: 1,
                message: "same message".to_owned(),
                direction: verify::Direction::Other,
                code: None,
            },
            root,
        )
    };

    let baseline = key_of("/home/u/dev/benchmarks/rs-crown/brotli/src/enc/encode.rs", original_root);
    let observed = key_of("/var/folders/T/crat-verify-4242-0/src/enc/encode.rs", observed_root);
    assert_eq!(
        baseline, observed,
        "the two sides key the same file differently — the baseline masks \
         nothing and the gate silently no-ops on the corpus"
    );
    assert_eq!(baseline.0, "src/enc/encode.rs", "key is relative to the crate root");
}

/// **W2 — a path NOT under the given root keys as ITSELF.**
///
/// **Rider 7 branch: FALLBACK.** Never a basename: basenames merge distinct
/// files into one key, so a novel error in `a/x.rs` could read as the baseline
/// of `b/x.rs` and the gate would fail OPEN.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** restore a basename
/// fallback and this fails.
#[test]
fn a_path_outside_the_crate_root_keys_as_itself() {
    let root = std::path::Path::new("/home/u/dev/benchmarks/rs-crown/brotli");
    let outside = "/somewhere/else/src/enc/encode.rs";
    assert_eq!(
        verify::crate_relative(outside, root),
        outside,
        "a path outside the root was rewritten — a basename here would merge \
         distinct files into one key"
    );
    // And two distinct files sharing a basename must NOT collide.
    assert_ne!(
        verify::crate_relative("/p/a/x.rs", root),
        verify::crate_relative("/p/b/x.rs", root),
        "distinct files collapsed to one key"
    );
}

/// **S2b.2 repair-2 — gate machinery does not run on instrument paths.**
///
/// `baseline_of` COMPILES the unmodified crate. Probe mode returns before
/// `novel` is ever consulted, so on that path the compile is dead work — and
/// not harmlessly: its diagnostics are forwarded to the SAME stderr the
/// validation transfer parses as its rendered side, which put four
/// frozen-tree entries against a structural side that measures the temp copy.
///
/// # What this asserts, and what it does not
///
/// The stderr contamination is not observable in-process — the emitter writes
/// to the process's own stderr, not to anything a test can capture. So this
/// pins the CAUSE rather than the symptom: no baseline is computed at all on
/// the probe path. That implies the absence of leakage (a compile that does
/// not run emits nothing) and is strictly narrower than "only-rendered is
/// empty", which the corpus transfer checks end-to-end. Stated rather than
/// substituted silently.
///
/// **Rider 7 branch: the PROBE path on a baseline-dirty input — brotli's
/// shape**, nested two components below the root so the gate path genuinely
/// has a baseline to find.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** restore the
/// unconditional `baseline_of` above the `probe_only` return — in the shape it
/// actually had, feeding the `OutcomeFacts` literal — and this fails.
///
/// **A residual, measured rather than assumed.** A first mutation that computed
/// the baseline eagerly but left the counters assigned below the return
/// **survived**: the assertion reads the reported counters, so it detects "a
/// baseline reached the outcome", not "a compile executed". A compile whose
/// result is discarded would evade it and still contaminate stderr. Catching
/// that needs an execution counter — a test-only seam in shipping code, which
/// this track has ruled against where a data-level route exists; here there is
/// no data-level route, so the residual is stated and left to the corpus
/// transfer, which observes the stderr end-to-end.
///
/// **That coverage is compelled, not hoped for.** Under the staleness rule, a
/// change touching the probe or baseline path makes every prior transfer result
/// stale, so the transfer must be re-run before its numbers are cited again —
/// which is exactly the change class that could reintroduce a discarded
/// compile. The residual is therefore a MANAGED one: the only edits that can
/// open it are the edits that force the run that would close it.
#[test]
fn a_probe_does_not_compile_the_baseline_it_never_consults() {
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod deep;\n"),
        ("deep.rs", "pub mod inner;\n"),
        (
            "deep/inner.rs",
            "pub unsafe fn preexisting(v: &i32) {\n    *(v as *const i32 as *mut i32) = 7;\n}\npub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
    ]);

    // NON-VACUITY CONTROL, first: the GATE path on this same fixture must see a
    // real baseline. Without it, a fixture that simply has no baseline would
    // satisfy the probe assertion below and the witness would pin nothing.
    let gate_baseline_errors = match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted { baseline_errors, .. } => baseline_errors,
        super::RewriteOutcome::Degraded { baseline_errors, .. } => baseline_errors,
    };
    assert!(
        gate_baseline_errors > 0,
        "the fixture is not baseline-dirty, so the probe assertion below would \
         hold vacuously"
    );

    // THE PROBE, on the same input: no baseline is computed at all.
    let probe = super::rewrite_core_injected(
        ::utils::compilation::path_to_input(&fixture.root()),
        Some(&fixture.root()),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        true,
    );
    match probe {
        super::RewriteOutcome::Degraded {
            baseline_keys,
            baseline_errors,
            ..
        } => {
            assert_eq!(
                (baseline_keys, baseline_errors),
                (0, 0),
                "probe mode compiled a baseline it returns before consulting. \
                 That compile's diagnostics reach the SAME stderr an \
                 instrument's consumer parses, which is how four frozen-tree \
                 entries appeared on the rendered side of a transfer that \
                 measures the temp copy"
            );
        }
        super::RewriteOutcome::Emitted { .. } => {
            panic!("probe mode returns before emission and cannot report Emitted")
        }
    }
}

/// **F.2 — the differential gate, END-TO-END on a NESTED crate.**
///
/// **Rider 7 branch: UNDER-ROOT — the branch the corpus takes.** The subject
/// lives at `deep/inner.rs`, two components below the crate root, so no basename
/// accident can make the two sides agree: the flat fixture keyed `m.rs` on both
/// sides even while the canonicalizer was broken, which is exactly how the
/// corpus defect survived its own witness.
///
/// The baseline dirt is `invalid_reference_casting` — brotli's real class,
/// deny-by-default at verify and harmless to the decision phase.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** gate on the absolute
/// count instead of the differential and this fails.
#[test]
fn a_nested_crate_masks_its_baseline_and_still_emits() {
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod deep;\n"),
        ("deep.rs", "pub mod inner;\n"),
        (
            "deep/inner.rs",
            "pub unsafe fn preexisting(v: &i32) {\n    *(v as *const i32 as *mut i32) = 7;\n}\npub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
    ]);

    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            files,
            bisect_probes,
            escalated,
            ..
        } => {
            let nested = files
                .iter()
                .find(|(k, _)| format!("{k:?}").contains("inner.rs"))
                .map(|(_, text)| text.clone())
                .expect("the nested module was emitted");
            assert!(
                nested.contains("p: &mut i32"),
                "the rewrite was withheld by the nested crate's baseline: {nested}"
            );
            // PATH-PINNED, as in the flat witness: it must emit on the loop's
            // clean exit, not be recovered by bisect.
            assert_eq!(
                bisect_probes, 0,
                "the nested baseline forced an escalation instead of being masked"
            );
            assert!(escalated.is_none(), "escalated: {escalated:?}");
        }
        super::RewriteOutcome::Degraded { reason, .. } => panic!(
            "a nested crate's baseline gated its rewrite — the corpus shape, \
             which the flat fixture could not detect: {reason}"
        ),
    }
}

/// **S2b.3 Item 0 — `unplaceable` SURVIVES A `Degraded` OUTCOME.**
///
/// Two pre-existing facts, which until S2b.3 could not both be observed: a
/// macro-generated declaration has no spliceable range and is recorded as
/// `Unplaceable`, and probe mode returns `Degraded` before the gate. The second
/// discarded the first — `RewriteOutcome::Degraded` had no field to carry it,
/// so `OutcomeFacts::degraded` dropped it and `run_m1_emit`'s FAIL arm wrote a
/// literal `0usize` in its place.
///
/// The fixture is the one from
/// `a_macro_generated_declaration_is_recorded_as_unplaceable`, but driven
/// through the **full pipeline** rather than `emit_files` alone. That
/// reachability was checked before this witness was written, per the ruling that
/// a fixture which does not produce a nonzero count through the shipping
/// pipeline is a finding to report and not a fixture to force.
///
/// The `> 0` assertion is a NON-VACUITY guard, not decoration: a zero would mean
/// the fixture had stopped producing an `Unplaceable` at all, at which point the
/// equality below would hold for the wrong reason.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove
/// `unplaceable: self.unplaceable` from `OutcomeFacts::degraded` — the variant
/// then has an unfilled field and the BUILD fails, which is the strongest form
/// this witness can take. Deletion cannot produce a running-but-wrong binary
/// here, so the semantically faithful mutation follows it: `Vec::new()` in that
/// same position restores the original defect exactly, and this test fails on
/// the count.
#[test]
fn a_degraded_outcome_still_reports_its_unplaceable_decisions() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\nmacro_rules! mk {\n    () => {\n        pub unsafe fn mac_bump(p: *mut i32) -> i32 {\n            *p += 1;\n            *p\n        }\n    };\n}\nmk!();\n",
    )]);

    // The reference value, from the phase that produces it.
    let planned = emit(&fixture).unplaceable;
    assert!(
        !planned.is_empty(),
        "the fixture no longer yields an Unplaceable, so this witness would \
         pass on a zero == zero comparison"
    );

    let probe = super::rewrite_core_injected(
        ::utils::compilation::path_to_input(&fixture.root()),
        Some(&fixture.root()),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        true,
    );
    match probe {
        super::RewriteOutcome::Degraded { unplaceable, .. } => {
            assert_eq!(
                unplaceable.len(),
                planned.len(),
                "the Degraded arm lost the plan's unplaceable decisions — the \
                 shape that made every FAIL row's count a constant"
            );
            assert_eq!(
                unplaceable[0].reason, planned[0].reason,
                "the count survived but the attribution did not"
            );
        }
        super::RewriteOutcome::Emitted { .. } => {
            panic!("probe mode returns before emission and cannot report Emitted")
        }
    }
}

/// **S2b.3 Item 1 — `emitted` COUNTS PLACEMENTS, NOT DECISIONS.**
///
/// The reported `emitted` was `DecisionTable::emitted_count()`, a count of `Ref`
/// decisions. A decision `plan` cannot place produces no edit, so the two
/// numbers differ by exactly the unplaceable set and the source is unchanged in
/// that difference. Corpus exposure is zero, which is *why* this is fixed at the
/// derivation: a counter right by measurement is one corpus change from wrong,
/// and it would present as a yield figure rather than as a failure.
///
/// The macro fixture is the discriminating case — its single subject IS a `Ref`
/// decision (the non-`Ref` arm returns before the span is ever located), so the
/// old derivation reports **1** for a run that edited nothing.
///
/// The emptiness assertions are the anchor: they are what make `0` the RIGHT
/// answer rather than merely the expected one.
///
/// # Both arms, because the count reaches them by different routes
///
/// On a success path `facts.emitted_count` is **overwritten** by `kept.len()`,
/// which derives from the already-filtered `emitted_subjects`. The value built
/// at the tuple site therefore survives only on a `Degraded` return — the FAIL
/// rows. A witness on the emitting arm alone leaves the tuple site uncovered,
/// and the fix would be half-applied: placement-true on PASS rows and
/// decision-shaped on FAIL rows, the same arm asymmetry Item 0 repaired one
/// field over. So this drives the same fixture down both routes.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** delete the
/// `unplaceable_subjects.contains(..)` skip in `rewrite_core_injected` and this
/// fails 1 vs 0 on the emitting leg. Second: put the decision count back at
/// the tuple site — `entries.iter().filter(|(_, d)| matches!(d, Decision::Ref { .. })).count()` — **this SURVIVED the emitting leg alone**, which is how the
/// second route was found; it fails the probe leg below.
#[test]
fn emitted_counts_placements_not_ref_decisions() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\nmacro_rules! mk {\n    () => {\n        pub unsafe fn mac_bump(p: *mut i32) -> i32 {\n            *p += 1;\n            *p\n        }\n    };\n}\nmk!();\n",
    )]);

    // NON-VACUITY: the subject must reach `plan` as a `Ref` decision and fail to
    // place. A fixture that degraded it earlier would satisfy the count below
    // for a reason that has nothing to do with placement.
    let planned = emit(&fixture);
    assert_eq!(
        planned.unplaceable.len(),
        1,
        "the fixture stopped producing an unplaceable Ref decision, so the \
         count below no longer discriminates: {:?}",
        planned.unplaceable
    );

    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            emitted_count,
            files,
            unplaceable,
            ..
        } => {
            assert!(
                files.is_empty(),
                "nothing should have been written: {:?}",
                files.keys().collect::<Vec<_>>()
            );
            assert_eq!(unplaceable.len(), 1, "{unplaceable:?}");
            assert_eq!(
                emitted_count, 0,
                "a decision that produced no edit was counted as emitted — \
                 `emitted` is still decision-shaped"
            );
        }
        super::RewriteOutcome::Degraded { reason, .. } => {
            panic!("an unplaceable-only crate emits nothing and still passes: {reason}")
        }
    }
}

/// **S2b.3 Item 1, second leg — the `Degraded` arm's `emitted_count`.**
///
/// See `emitted_counts_placements_not_ref_decisions` for why this is a separate
/// route rather than a second assertion: the success paths overwrite
/// `facts.emitted_count` with `kept.len()`, so only a non-emitting return
/// reports the value the tuple site built. Probe mode is the reachable
/// non-emitting return that does not require manufacturing a gate failure.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** the tuple site's
/// `emitted_subjects.len()` has no deletion that compiles, so the faithful
/// mutation is the original expression — put the decision count back,
/// `entries.iter().filter(|(_, d)| matches!(d, Decision::Ref { .. })).count()`, and this fails 1 vs 0. That mutation SURVIVES the emitting leg, which is exactly
/// why this leg exists.
#[test]
fn a_degraded_outcome_reports_placements_too() {
    let fixture = Fixture::new(&[(
        "lib.rs",
        "#![allow(dead_code, unused_unsafe)]\nmacro_rules! mk {\n    () => {\n        pub unsafe fn mac_bump(p: *mut i32) -> i32 {\n            *p += 1;\n            *p\n        }\n    };\n}\nmk!();\n",
    )]);
    // NON-VACUITY, as on the emitting leg: one unplaceable `Ref` decision, or
    // the zero below means nothing.
    assert_eq!(emit(&fixture).unplaceable.len(), 1);

    let probe = super::rewrite_core_injected(
        ::utils::compilation::path_to_input(&fixture.root()),
        Some(&fixture.root()),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        true,
    );
    match probe {
        super::RewriteOutcome::Degraded { emitted_count, .. } => assert_eq!(
            emitted_count, 0,
            "the non-emitting arm still reports Ref DECISIONS — placement-truth \
             stopped at the success paths"
        ),
        super::RewriteOutcome::Emitted { .. } => {
            panic!("probe mode returns before emission and cannot report Emitted")
        }
    }
}

/// **S3.0′ — two subjects that render the SAME NAME stay distinct.**
///
/// `mixed` has two anonymous pointer parameters, so both carry
/// `param_name: None`. Both reach `Decision::Ref` (measured, not assumed), and
/// the second one's type comes from a macro, so its span cannot be spliced and
/// `plan` records it as unplaceable. That is the shape a name-keyed identity
/// cannot represent: both parameters render `mixed::<unnamed>`, the driver's
/// unplaceable subtraction matches the FIRST one against the SECOND one's
/// record, and skips a placement that actually happened.
///
/// Measured at `ebeb99fd`, before the key was repaired: `emitted_count == 0`
/// while the emitted source read `fn mixed(_: &i32, _: ty2!())` — the rewrite is
/// right there in the output — and the ratified identity
/// `emitted + degraded + unplaceable == rows` failed `0 + 0 + 1 != 2`.
///
/// **Reachability (Rider 5) is shown, not asserted:** the assertion below is on
/// `emitted_count`, the driver's real counter, reached through `rewrite_m1` —
/// the same path the corpus sweep uses. The corpus has never exposed this only
/// because `unplaceable == 0` there, so the `contains` check never matches.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `#{mir_local}`
/// suffix from [`Subject::identity_key`] — i.e. reverting to the name-only key —
/// makes this fail with `emitted_count` 0 instead of 1.
#[test]
fn two_subjects_with_the_same_rendered_name_stay_distinct() {
    let src = "#![allow(dead_code, unused_unsafe)]\nmacro_rules! ty2 { () => { *mut i32 } }\npub unsafe fn mixed(_: *mut i32, _: ty2!()) -> i32 { 0 }\n";
    let super::RewriteOutcome::Emitted {
        emitted_count,
        unplaceable,
        degradations,
        source,
        ..
    } = super::rewrite_m1(src)
    else {
        panic!("fixture must emit");
    };

    assert_eq!(
        unplaceable.len(),
        1,
        "the macro-typed parameter is the unplaceable one: {unplaceable:?}"
    );
    assert_eq!(
        emitted_count, 1,
        "the PLACEABLE parameter must still be counted — a name-keyed identity \
         matches it against the other parameter's unplaceable record and drops \
         it. Emitted source was:\n{source}"
    );
    assert!(
        source.contains("_: &i32"),
        "the placement the count claims must be visible in the output:\n{source}"
    );
    // The identity the corpus pin enforces, on the fixture that breaks it.
    assert_eq!(
        emitted_count + degradations.len() + unplaceable.len(),
        2,
        "emitted + degraded + unplaceable == rows, over 2 subjects"
    );
}

// ---------------------------------------------------------------------------
// S3.1 A-side — the locals subject universe
// ---------------------------------------------------------------------------

/// Decision-table rows for a fixture, as `(mir_local, name, reason)`.
fn locals_of(src: &str) -> Vec<(u32, Option<String>, String)> {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let table = super::decide_table(tcx).expect("fixture yields a decision table");
        let rows = super::artifact::rows(tcx, &table);
        rows.iter()
            .filter(|r| r.arg_index.is_none())
            .map(|r| {
                (
                    r.mir_local,
                    r.param_name.clone(),
                    r.degrade_reason.clone().unwrap_or_else(|| "<emitted>".to_owned()),
                )
            })
            .collect::<Vec<_>>()
    })
    .expect("fixture compiles")
}

const MALLOC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments)]\nextern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; }\n";

/// **A named pointer local is a subject; a MIR temporary is not.**
///
/// Both halves in one witness because they share a fixture and the interesting
/// property is the BOUNDARY between them: `p` is a named binding and becomes a
/// subject, while the `*mut c_void` the `malloc` call lands in is a depth-1
/// pointer with no debug entry and must not. Depth alone would admit it.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the locals range from
/// `collect_local_subjects` yields zero rows; deleting the entry-count guard
/// admits the temporary.
#[test]
fn a_named_pointer_local_is_a_subject_and_a_temporary_is_not() {
    let got = locals_of(&format!(
        "{MALLOC}pub unsafe fn f() -> i32 {{ let p: *mut i32 = malloc(4) as *mut i32; *p = 1; *p }}\n"
    ));
    assert_eq!(
        got.iter().map(|(l, n, _)| (*l, n.as_deref())).collect::<Vec<_>>(),
        // `_1`, not `_2`: this fn has no parameters, so `arg_count == 0` and the
        // locals range opens at `_1`. The malloc temporary is absent because it
        // carries no debug entry, which is the half of this witness that depth
        // alone would get wrong.
        vec![(1, Some("p"))],
        "exactly the named local, and no temporary: {got:?}"
    );
}

/// **Two shadowing locals are two subjects.** Name is not a key.
///
/// *Mutation-tested:* keying the universe by name collapses these to one row.
#[test]
fn two_shadowing_locals_are_two_subjects() {
    let got = locals_of(&format!(
        "{MALLOC}pub unsafe fn f() -> i32 {{ let p: *mut i32 = malloc(4) as *mut i32; *p = 1; \
         let p: *mut i32 = malloc(4) as *mut i32; *p = 2; *p }}\n"
    ));
    let names: Vec<_> = got.iter().map(|(_, n, _)| n.as_deref()).collect();
    assert_eq!(got.len(), 2, "two distinct locals, both named p: {got:?}");
    assert_eq!(names, vec![Some("p"), Some("p")]);
    assert_ne!(got[0].0, got[1].0, "distinct mir_locals: {got:?}");
}

/// **An unannotated pointer local degrades with its OWN reason**, and carries no
/// `arg_index`.
///
/// The dominant corpus shape: 2628 of 3142 locals are C2Rust bindings with no
/// declared type. Routing them through the decl-shape arm would attribute them
/// to a syntax they do not have, which is why `NoDeclaredType` is tested first.
///
/// *Mutation-tested:* removing the `ty_span.is_none()` arm in `decide_one`
/// re-routes this to `unsupported-decl-shape`.
#[test]
fn an_unannotated_pointer_local_degrades_with_its_own_reason() {
    let got = locals_of(&format!(
        "{MALLOC}pub unsafe fn f() -> i32 {{ let p = malloc(4) as *mut i32; *p = 1; *p }}\n"
    ));
    assert_eq!(got.len(), 1, "{got:?}");
    assert_eq!(got[0].2, "no-declared-type", "{got:?}");
}

/// **A locals row carries `arg_index: None`** — *not a parameter*, never
/// *unpaired* — while the parameter beside it keeps its 1-based index.
///
/// *Mutation-tested:* removing the `SubjectKind::Local => None` arm in
/// `artifact::rows` is a compile error; returning `Some(0)` fails this.
#[test]
fn a_locals_row_carries_no_arg_index_while_a_parameter_keeps_one() {
    let src = format!(
        "{MALLOC}pub unsafe fn f(q: *mut i32) -> i32 {{ let p: *mut i32 = malloc(4) as *mut i32; *p = 1; *p + *q }}\n"
    );
    let fixture = Fixture::new(&[("lib.rs", &src)]);
    let pairs = ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let table = super::decide_table(tcx).expect("table");
        super::artifact::rows(tcx, &table)
            .iter()
            .map(|r| (r.mir_local, r.arg_index))
            .collect::<Vec<_>>()
    })
    .expect("compiles");
    assert!(pairs.contains(&(1, Some(1))), "the parameter keeps its index: {pairs:?}");
    assert!(pairs.contains(&(2, None)), "the local carries None: {pairs:?}");
}
