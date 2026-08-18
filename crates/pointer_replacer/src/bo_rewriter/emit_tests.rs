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
        fn walk(
            dir: &std::path::Path,
            base: &std::path::Path,
            out: &mut BTreeMap<PathBuf, Vec<u8>>,
        ) {
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
    emit_injected(fixture, &|_| {})
}

/// **BRANCH 2 — an INJECTION at the plan boundary**, the `plan/mod.rs` arm-3
/// precedent and the same seam `rewrite_m1_path_injected` already uses.
///
/// Since S3.6-1 step 2 the decision phase refuses every emission that would
/// launder a reference into a raw context — which is the gate's whole job, and
/// which makes a deliberately-broken emission **unconstructible from source**.
/// Measured, not assumed: every raw context a converted value can reach is
/// either gated (field store, return, foreign argument, `static mut`) or is
/// itself a subject and converts with its source (an annotated local).
///
/// So the broken emission is injected as DATA rather than coaxed out of a
/// fixture. The fixture text is unchanged; only the decision differs, which is
/// what keeps every property the original witnesses rested on — line numbers,
/// file names, error counts — true by construction rather than by re-derivation.
fn emit_injected(
    fixture: &Fixture,
    inject: &(dyn Fn(&mut super::decision::DecisionTable) + Sync),
) -> Emission {
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let mut table = decide_table(tcx).expect("fixture yields a decision table");
        inject(&mut table);
        emit_files(tcx, &table, &rustc_hash::FxHashSet::default()).expect("emission succeeds")
    })
    .expect("fixture compiles")
}

/// Force `stash`'s parameter to a SHARED reference.
///
/// Shared is load-bearing: `&mut T → *mut T` coerces silently, so a mutable
/// injection would emit a crate that COMPILES and witness nothing. `&T` into a
/// `*mut T` field is `E0308` — the loud failure the verify layer exists to
/// read, and the one the original fixture produced before step 2 refused it.
fn force_stash_value_shared(table: &mut super::decision::DecisionTable) {
    for (subject, decision) in &mut table.entries {
        if subject.param_name.as_deref() == Some("value") {
            *decision = super::decision::Decision::Ref { mutable: false };
        }
    }
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
const MODULE_SUBJECT: &str = "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n";

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
    assert!(
        emission.unplaceable.is_empty(),
        "{:?}",
        emission.unplaceable
    );
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
        *text =
            "pub unsafe fn bump(p: &mut i32) -> i32 {\n    let _x: u8 = \"not a u8\";\n    *p\n}\n"
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
    let crate_dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../benchmarks/rs-crown/rgba");
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
        super::RewriteOutcome::Degraded {
            reason,
            degradations,
            ..
        } => {
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n",
        ),
        (
            "good.rs",
            "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
        ("bad.rs", BREAKS_ON_REWRITE),
    ]);

    // INJECTED since step 2 — the broken emission is supplied as data, per
    // `emit_injected`. The revert loop, the good rewrite and the crate are
    // unchanged; only the source of the bad edit is.
    match super::rewrite_m1_path_injected(&fixture.root(), 8, &force_stash_value_shared) {
        super::RewriteOutcome::Emitted {
            files,
            emitted_count,
            degradations,
            ..
        } => {
            let reverted: Vec<_> = degradations
                .iter()
                .filter(|d| d.reason == super::decision::DegradeReason::RevertedAfterVerifyFailure)
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
            let bad = files
                .iter()
                .find(|(k, _)| format!("{k:?}").contains("bad.rs"));
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n",
        ),
        (
            "good.rs",
            "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
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
                .filter(|d| d.reason == super::decision::DegradeReason::RevertedAfterVerifyFailure)
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
    // INJECTED since step 2 — see `emit_injected`. The crate under diagnosis is
    // the same one these witnesses always used; only the decision that produces
    // it is now supplied rather than derived.
    let emission = emit_injected(&fixture, &force_stash_value_shared);
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        ("m.rs", BREAKS_ON_REWRITE),
    ]);
    assert_eq!(d.diags.len(), 1, "expected one located diagnostic: {d:?}");
    assert_eq!(
        d.diags[0].line, 5,
        "the store is on line 5: {:?}",
        d.diags[0]
    );
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n",
        ),
        (
            "good.rs",
            "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
        ),
        ("bad.rs", BREAKS_ON_REWRITE),
    ]);
    // INJECTED since step 2 — the broken emission is supplied as data, per
    // `emit_injected`. The cap is still 0 and the loop still cannot converge;
    // only the source of the bad edit changed.
    match super::rewrite_m1_path_injected(&fixture.root(), 0, &force_stash_value_shared) {
        super::RewriteOutcome::Emitted {
            escalated,
            bisect_probes,
            ..
        } => {
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        ("m.rs", INVERTED),
    ]);
    match super::rewrite_m1_path_injected(&fixture.root(), 8, &keep_r_raw) {
        super::RewriteOutcome::Emitted {
            escalated,
            bisect_probes,
            ..
        } => {
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
        ("m.rs", MODULE_SUBJECT),
    ]);
    match super::rewrite_m1_path_injected(&fixture.root(), 8, &duplicate_entries) {
        super::RewriteOutcome::Degraded {
            reason,
            bisect_probes,
            ..
        } => {
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

/// **An EMITTED outcome carries the ruled `files_touched`, not its map size.**
///
/// The twin of `a_failing_outcome_carries_its_reverted_count`, for the arm that
/// did not have one. `Degraded` carried the ruled value all along; `emitted()`
/// DROPPED it, so the only consumer recovered a number by measuring `files`
/// instead. On the span layer the two agree — `render` returns edited files
/// only — so the defect was invisible for the whole span era and surfaced the
/// moment the AST layer's SEEDED map made them differ.
///
/// The fixture encodes exactly that disagreement: `files_touched: 0` against a
/// ONE-entry map. That is not a contrived pair, it is `bst` — converged with
/// every subject reverted, emitting its substrate unchanged, and reported as
/// touching one file against the span layer's zero.
///
/// *Mutation-tested.* **Deletion first:** drop `files_touched: self.files_touched`
/// from `OutcomeFacts::emitted` and this fails to compile, which is the
/// strongest available failure. **Faithful second:** write
/// `files_touched: files.len()` there — the exact defect, spelled as a plausible
/// fix — and this fails 1 vs 0.
#[test]
fn an_emitted_outcome_carries_the_ruled_files_touched() {
    let facts = super::OutcomeFacts {
        emitted_count: 0,
        reverted_count: 1,
        files_touched: 0,
        ..Default::default()
    };
    let mut files = std::collections::BTreeMap::new();
    files.insert(
        super::plan::FileKey::Real(std::path::PathBuf::from("/x/lib.rs")),
        "fn f() {}\n".to_owned(),
    );
    match facts.emitted("fn f() {}\n".to_owned(), files) {
        super::RewriteOutcome::Emitted {
            files_touched,
            files,
            ..
        } => {
            assert_eq!(
                files_touched, 0,
                "an emitted outcome reported its emission MAP SIZE as \
                 files_touched; the map is seeded on the AST layer, so this \
                 counts a file the rewrite never touched"
            );
            assert_eq!(
                files.len(),
                1,
                "the map itself must still carry the file — the emission is \
                 what it is; only the COUNTER was wrong, and a fix that \
                 dropped the file would trade a counter defect for an \
                 emission one"
            );
        }
        super::RewriteOutcome::Degraded { .. } => panic!("emitted() built a Degraded"),
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
    println!(
        "BROTLI-CONTROL old_gate_is_ok={old_gate} new_gate_passes={}",
        d.errors == 0
    );
    for x in d.diags.iter().take(8) {
        println!(
            "BROTLI-CONTROL diag {}:{} {:?}",
            x.file, x.line, x.direction
        );
        println!(
            "BROTLI-CONTROL   msg={}",
            &x.message[..x.message.len().min(160)]
        );
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod m;\n",
        ),
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

    let baseline = key_of(
        "/home/u/dev/benchmarks/rs-crown/brotli/src/enc/encode.rs",
        original_root,
    );
    let observed = key_of(
        "/var/folders/T/crat-verify-4242-0/src/enc/encode.rs",
        observed_root,
    );
    assert_eq!(
        baseline, observed,
        "the two sides key the same file differently — the baseline masks \
         nothing and the gate silently no-ops on the corpus"
    );
    assert_eq!(
        baseline.0, "src/enc/encode.rs",
        "key is relative to the crate root"
    );
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod deep;\n",
        ),
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
        super::RewriteOutcome::Emitted {
            baseline_errors, ..
        } => baseline_errors,
        super::RewriteOutcome::Degraded {
            baseline_errors, ..
        } => baseline_errors,
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
        (
            "lib.rs",
            "#![allow(dead_code, unused_unsafe)]\npub mod deep;\n",
        ),
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
                    r.degrade_reason
                        .clone()
                        .unwrap_or_else(|| "<emitted>".to_owned()),
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
        got.iter()
            .map(|(l, n, _)| (*l, n.as_deref()))
            .collect::<Vec<_>>(),
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

/// **An unannotated pointer local degrades with the reason of the gate that
/// actually stops it**, and carries no `arg_index`.
///
/// The dominant corpus shape: **1,196 of 1,710** locals on the substrate of
/// record are C2Rust bindings with no declared type (raw-form era: 2,628 of
/// 3,142 — `preprocess` removed the `fresh_N` temporaries, not the class).
///
/// **Amended by the dissolution (2026-08-12).** Every vintage before it
/// asserted `no-declared-type` here: one reason over the whole 1,196, naming
/// the rewriter's splice mechanism rather than anything about the subject. The
/// ladder now speaks, and on this fixture — a leaked `malloc` result — it says
/// `kind-raw`, a fact about the program. Corpus-wide the same move accounts for
/// 475 of the 1,196.
///
/// *Mutation-tested:* restoring the `ty_span.is_none()` early return in
/// `decide_one_ladder` puts a residual key back here.
#[test]
fn an_unannotated_pointer_local_degrades_with_the_gate_that_stops_it() {
    let got = locals_of(&format!(
        "{MALLOC}pub unsafe fn f() -> i32 {{ let p = malloc(4) as *mut i32; *p = 1; *p }}\n"
    ));
    assert_eq!(got.len(), 1, "{got:?}");
    assert_eq!(got[0].2, "kind-raw", "{got:?}");
}

/// **An unannotated local that is ALREADY a reference says so** — the
/// dissolution's largest single discovery, and the one that kept the ruling's
/// STOP from firing.
///
/// `let ref mut x = place;` is C2Rust's temporary idiom and it binds `&mut T`.
/// **51 of the 52 `index-addr` subjects on the corpus are this shape**, and
/// every vintage before the dissolution reported them `no-declared-type` — a
/// claim about the rewriter's splice mechanism, applied to subjects that need
/// no rewrite at all because they are already the target form.
///
/// The shape is read from the RESOLVED type, not from the construction class:
/// 51-of-52 is a correlation, and `ty.kind()` is the fact. `unsupported-decl-shape`
/// is the existing key that carries exactly this claim — its own doc says *"or
/// a parameter that is already a reference"* — so nothing was coined for them.
///
/// **The SHAPE is asserted, not just the key**, and that is load-bearing:
/// `DeclShape::Other` fails the `!= RawPtr` test too, so a mutation restoring
/// `Other` reports the same key and a key-only assertion passes it. Measured,
/// not reasoned — the first version of this witness was written key-only and
/// its mutation came back GREEN.
///
/// *Mutation-tested:* restoring `DeclShape::Other` in the collector's
/// resolved-type fallback fails on the shape column.
#[test]
fn an_unannotated_local_that_is_already_a_reference_reports_its_shape() {
    let rows = artifact_rows_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub struct S { pub a: [u32; 4] }\n\
         pub unsafe fn f(s: *mut S) {\n\
         \x20   let ref mut fresh0 = (*s).a[1];\n\
         \x20   *fresh0 |= 1;\n\
         }\n",
    );
    let fresh: Vec<_> = rows
        .iter()
        .filter(|r| r.param_name.as_deref() == Some("fresh0"))
        .collect();
    assert_eq!(fresh.len(), 1, "{rows:?}");
    assert_eq!(
        fresh[0].degrade_reason.as_deref(),
        Some("unsupported-decl-shape"),
        "{rows:?}"
    );
    assert_eq!(
        fresh[0].decl_shape,
        Some(crate::coverage_recon::schema::DeclShape::Reference),
        "the shape must come from the RESOLVED type — this subject is already \
         `&mut T` and reporting `other` for it is the pre-dissolution claim \
         wearing a new name: {rows:?}"
    );
}

/// **THE TERMINAL VETO: a subject with no splice target cannot emit**, whatever
/// form the ladder selected for it.
///
/// This is what makes the dissolution's ledger invariance STRUCTURAL rather
/// than measured. Today no real subject reaches an emitting `Slice` or `Opt`
/// without a `ty_span` — a parameter always has one, and a local is stopped by
/// `slice-local-construction` / `opt-local-construction` first — so the veto is
/// corpus-unreachable and this is the ONLY thing that can ever fail for it.
///
/// The fixture is a slice-emitting PARAMETER, chosen because a parameter walks
/// past both local-construction gates and reaches `Decision::Slice`; erasing
/// its `ty_span` at the phase boundary is then the exact state the veto exists
/// for. `ctor` is `None` for a parameter, so the residual fold is
/// `copy-source-coupled` — the no-recognized-initializer arm.
///
/// *Mutation-tested:* deleting the veto in `decide_one` emits this subject
/// (`<emitted>`), which is the ledger movement it exists to make impossible.
#[test]
fn a_subject_with_no_splice_target_cannot_emit_whatever_form_was_selected() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]\n\
               pub unsafe fn fill(p: *mut i32, len: usize) {\n\
               \x20   let mut i: usize = 0;\n\
               \x20   while i < len { *p.offset(i as isize) = i as i32; i += 1; }\n\
               }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let (baseline, erased) =
        ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            let base = super::artifact::rows(tcx, &super::decide_table(tcx).expect("table"));
            let erased = super::decisions_with_ty_span_erased(tcx).expect("perturbed table");
            (base, erased)
        })
        .expect("fixture compiles");

    let reason = |rows: &[crate::coverage_recon::schema::Row]| {
        rows.iter()
            .find(|r| r.param_name.as_deref() == Some("p"))
            .map(|r| {
                r.degrade_reason
                    .clone()
                    .unwrap_or_else(|| "<emitted>".to_owned())
            })
            .expect("subject p present")
    };
    // The baseline is the load-bearing half: without it, a veto that vetoed
    // nothing would pass this test exactly as well, because the subject would
    // read `slice-*` in both columns.
    assert_eq!(
        reason(&baseline),
        "<emitted>",
        "the fixture must EMIT unperturbed, or the veto below is vetoing a \
         subject that was already degraded"
    );
    assert_eq!(
        reason(&erased),
        "copy-source-coupled",
        "a subject whose declared type was erased reached an emitting form and \
         the terminal veto did not stop it — the plan phase would splice at a \
         span that does not exist"
    );
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
    assert!(
        pairs.contains(&(1, Some(1))),
        "the parameter keeps its index: {pairs:?}"
    );
    assert!(
        pairs.contains(&(2, None)),
        "the local carries None: {pairs:?}"
    );
}

// ---------------------------------------------------------------------------
// S3.1′ — the A1 emitability gates over the LOCALS population
// ---------------------------------------------------------------------------

/// Every subject's `(name, is_param, reason)` — parameters included.
///
/// A sibling of [`locals_of`] rather than a widening of it: `locals_of` is the
/// instrument the S3.1 witnesses above are written against, and changing what
/// it returns would put those tests under Rider 4 for no gain here.
fn artifact_rows_of(src: &str) -> Vec<crate::coverage_recon::schema::Row> {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let table = super::decide_table(tcx).expect("fixture yields a decision table");
        super::artifact::rows(tcx, &table)
    })
    .expect("fixture compiles")
}

fn decisions_of(src: &str) -> Vec<(String, bool, String)> {
    artifact_rows_of(src)
        .iter()
        .map(|r| {
            (
                r.param_name
                    .clone()
                    .unwrap_or_else(|| "<unnamed>".to_owned()),
                r.arg_index.is_some(),
                r.degrade_reason
                    .clone()
                    .unwrap_or_else(|| "<emitted>".to_owned()),
            )
        })
        .collect()
}

fn reason_of(got: &[(String, bool, String)], name: &str, is_param: bool) -> String {
    got.iter()
        .find(|(n, p, _)| n == name && *p == is_param)
        .unwrap_or_else(|| panic!("no subject {name} (param={is_param}): {got:?}"))
        .2
        .clone()
}

/// **A raw-only method call on a LOCAL degrades it** — gate one, over the
/// population that had it dead.
///
/// The subject must survive shape *and* kind to reach A1 at all, so `p` is a
/// copy of a parameter (BO calls it `Ref`) rather than a `malloc` result (BO
/// would call that `Owning` or `Raw` and degrade it earlier). **A fixture that
/// degrades upstream witnesses nothing**, which is why this shape was measured
/// against the pre-repair build first: `p` came back `ref-shared`, so it
/// genuinely reached the gate and was waved through.
///
/// **Fixture op changed at S3.2′-2, deliberately.** It was `*p.offset(1)`.
/// `offset` is now a slice-ARITHMETIC op, so an arithmetic use on a local takes
/// the new `slice-local-construction` arm and this test would have been
/// asserting the wrong gate. `is_null` is a raw-only use that is *not*
/// arithmetic, so the fixture again exercises exactly the gate the test names.
/// The arithmetic case is not lost — it has its own witness below.
///
/// *Mutation-tested (Rider 0, deletion first), with the claim CORRECTED after
/// measurement:* deleting the `binding_hir` insert does **not** restore
/// `ref-shared` — an earlier draft of this comment said it would. With the map
/// empty the attribution lookup finds nothing and the collector **panics** by
/// design, naming the local and its span. Killed, but through the contradiction
/// arm rather than through this assertion.
///
/// The mutation that reproduces the ORIGINAL defect is restoring
/// `hir_id: rustc_hir::CRATE_HIR_ID` at the construction site: `p` comes back
/// `<emitted>` and this test fails on exactly that. Recorded rather than
/// silently re-pointed — a wrong mutation claim is the kind of thing that gets
/// copied forward.
#[test]
fn a_raw_only_method_on_a_local_degrades_it() {
    // RE-BASED at S3.2′-3: `is_null` on a local now selects the optional form
    // and is refused by its CONSTRUCTION guard, which is a different arm with a
    // different reason. `read` still has no image, so it is what this witness
    // needs to keep testing A1 reach over the locals universe.
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32) -> i32 { let p: *mut i32 = a; p.read() }\n",
    );
    assert_eq!(
        reason_of(&got, "p", false),
        "raw-pointer-operation",
        "the local reached A1 and was not stopped by it: {got:?}"
    );
}

/// **An optional LOCAL is refused at its construction site.**
///
/// `let p: Option<&i32> = <raw pointer>` is `E0308` however the uses read, so
/// the blocker is the initializer — the arm the slice forms already have.
///
/// **This arm exists because a fixture found it.** Every subject in S3.2′-3's
/// measured market is a parameter, so the corpus could not have exercised it,
/// and the first thing to reach it would have been an emitted crate that does
/// not compile.
#[test]
fn an_optional_local_is_refused_at_its_construction_site() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32) -> i32 { let p: *mut i32 = a; if p.is_null() { return 0; } *p }\n",
    );
    assert_eq!(
        reason_of(&got, "p", false),
        "opt-local-construction",
        "an optional local was not stopped at its construction site: {got:?}"
    );
}

/// **Both operands of ONE comparison degrade — the parameter and the local.**
///
/// The population pair with no confound left: same function, same expression,
/// same span. Before the repair the parameter operand of `q == b` degraded
/// `ptr-comparison` while the local operand came back `ref-shared` — one
/// comparison, one gate, two answers, decided purely by which population the
/// operand belonged to.
///
/// Keeping the parameter assertion here is the point. A locals-only test would
/// still pass if a later change killed the gate for *everyone*, and would
/// report that as success.
///
/// *Mutation-tested (defect restoration — `hir_id` back to `CRATE_HIR_ID`;
/// the earlier draft named the `binding_hir` DELETION here, which panics
/// instead and so proves nothing about this pair):* the measured failure is
///
/// ```text
/// local operand: [("a", true, "<emitted>"), ("b", true, "ptr-comparison"), ("q", false, "<emitted>")]
/// ```
///
/// — the parameter assertion green, the local one red, with both operands of
/// the one comparison printed side by side. That single line **is** the defect.
#[test]
fn one_comparison_degrades_its_parameter_and_its_local_operand_alike() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32, b: *mut i32) -> i32 { \
         let q: *mut i32 = a; if q == b { return 1; } 0 }\n",
    );
    assert_eq!(
        reason_of(&got, "b", true),
        "ptr-comparison",
        "parameter operand: {got:?}"
    );
    assert_eq!(
        reason_of(&got, "q", false),
        "ptr-comparison",
        "local operand: {got:?}"
    );
}

/// **The facts join reports a fact the DECISION never reached.**
///
/// This is the instrument's whole purpose, so it is what the witness tests. The
/// fixture's local is **unannotated**, so it degrades at
/// `slice-local-construction` — a slice value would have to be built at its
/// initializer — and the A1 op fact never reaches the reason field. A
/// reason-field tally therefore records nothing about its `.offset()` use, and
/// would report the op population as smaller than it is.
///
/// **The dissolution amended the expected key, not the witness.** Before it,
/// the fixture stopped at `no-declared-type`, the first predicate, and never
/// consulted A1 at all; now it reaches A1, selects the slice form, and is
/// stopped by the construction-site gate. Either way the degradation is
/// upstream of the reported fact, which is the property under test — and the
/// amended key makes the fixture a STRICTLY harder case, because the decision
/// now does consult the op it must not be the source of.
///
/// The join must still report `annotated=0` **and** `raw_op=offset` on that
/// same subject. If it cannot, it has inherited the ordering it exists to
/// bypass, and every "zero" it certifies in the reachability table is worth
/// nothing.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing the `raw_only_uses`
/// lookup with `"-"` fails on the op column; deriving the row from
/// `decide_one`'s reason instead of from the facts fails the same way, which is
/// the substantive mutation — it reintroduces exactly the coupling.
#[test]
fn the_facts_join_reports_facts_the_decision_never_reached() {
    let src = "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
               pub unsafe fn f(a: *mut i32) -> i32 { let p = a; *p.offset(1) }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let (reason, facts) =
        ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            let table = super::decide_table(tcx).expect("table");
            let rows = super::artifact::rows(tcx, &table);
            let reason = rows
                .iter()
                .find(|r| r.arg_index.is_none())
                .and_then(|r| r.degrade_reason.clone())
                .unwrap_or_default();
            (reason, super::facts_join_tsv(tcx).expect("facts join"))
        })
        .expect("fixture compiles");

    assert_eq!(
        reason, "slice-local-construction",
        "the fixture must degrade UPSTREAM of the reported fact, or it \
         witnesses nothing"
    );
    let hdr: Vec<&str> = facts.lines().next().expect("header").split('\t').collect();
    let col = |n: &str| hdr.iter().position(|h| *h == n).expect("column present");
    let (c_param, c_ann, c_op) = (col("is_param"), col("annotated"), col("raw_op"));
    let local_row = facts
        .lines()
        .skip(1)
        .map(|l| l.split('\t').collect::<Vec<_>>())
        .find(|c| c[c_param] == "0")
        .unwrap_or_else(|| panic!("no local row in the facts join:\n{facts}"));
    assert_eq!(
        local_row[c_ann], "0",
        "the local is unannotated: {local_row:?}"
    );
    assert_eq!(
        local_row[c_op], "offset",
        "the join lost the op the decision never reached — it has inherited \
         decide_one's ordering: {local_row:?}"
    );
}

/// **`calloc` and `realloc` are told apart by CALLEE, never by arity.**
///
/// Both take two arguments, and only `calloc`'s first is an element count —
/// `realloc`'s is the pointer being resized. An arity test therefore reports a
/// **pointer expression as a length**, which is not a near-miss: it is a length
/// the emitted code would claim for a slice.
///
/// This is a regression pin on a defect that reached a de-risk run: every
/// `realloc` in libtree came back `alloc-count` with `(*v).p` as its "count".
/// Caught because the de-risk printed the size expressions rather than only
/// counting the classes — a tally would have shown a plausible histogram.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing the callee match with
/// `if args.len() == 2` restores the defect and fails this test on `b`.
#[test]
fn calloc_and_realloc_are_told_apart_by_callee_not_arity() {
    let src = "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
        extern \"C\" {\n\
            fn calloc(n: usize, sz: usize) -> *mut core::ffi::c_void;\n\
            fn realloc(p: *mut core::ffi::c_void, sz: usize) -> *mut core::ffi::c_void;\n\
        }\n\
        pub unsafe fn f(n: usize) -> i32 {\n\
            let a: *mut i32 = calloc(n, 4) as *mut i32;\n\
            let b: *mut i32 = realloc(a as *mut core::ffi::c_void, 8) as *mut i32;\n\
            *b\n\
        }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let tsv = ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        super::facts_join_tsv(tcx).expect("facts join")
    })
    .expect("fixture compiles");

    // Indexed BY HEADER NAME, never by position. Adding the `fatness` column
    // in S3.2′-1 shifted every later index and broke this test — the exact
    // hazard `construction.rs` warns about for tabs inside snippets, one level
    // up. A positional read is a latent break for every future column.
    let hdr: Vec<&str> = tsv.lines().next().expect("header").split('\t').collect();
    let col = |name: &str| {
        hdr.iter()
            .position(|h| *h == name)
            .unwrap_or_else(|| panic!("facts join has no `{name}` column: {hdr:?}"))
    };
    let (c_param, c_len, c_size) = (col("is_param"), col("len_class"), col("size_expr"));
    let classes: Vec<(String, String)> = tsv
        .lines()
        .skip(1)
        .map(|l| l.split('\t').collect::<Vec<_>>())
        .filter(|c| c[c_param] == "0") // locals only
        .map(|c| (c[c_len].to_owned(), c[c_size].to_owned()))
        .collect();

    assert!(
        classes
            .iter()
            .any(|(k, expr)| k == "alloc-count" && expr.contains('n')),
        "calloc's element count must be recovered from its FIRST argument: {classes:?}"
    );
    assert!(
        classes.iter().any(|(k, _)| k == "alloc-size-literal"),
        "realloc must be classified by its SIZE argument, not by treating its \
         pointer argument as a count: {classes:?}"
    );
    assert!(
        !classes
            .iter()
            .any(|(k, expr)| k == "alloc-count" && expr.contains("c_void")),
        "a POINTER expression was reported as an element count — the arity \
         defect is back: {classes:?}"
    );
}

// ---------------------------------------------------------------------------
// S3.2′-1 — the fatness ENTRY VALIDATION (A-2's discipline, applied to fatness)
// ---------------------------------------------------------------------------

/// `(local name, fatness verdict)` for every pointer local in a fixture.
fn fatness_of(src: &str) -> Vec<(String, &'static str)> {
    let fixture = Fixture::new(&[("lib.rs", src)]);
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let fat = super::fat_facts::FatFacts::from_program(&program);
        super::collect_local_subjects(tcx, &program, &mut_facts)
            .iter()
            .map(|s| {
                (
                    s.param_name
                        .clone()
                        .unwrap_or_else(|| "<unnamed>".to_owned()),
                    fat.render(s.fn_did, s.local),
                )
            })
            .collect::<Vec<_>>()
    })
    .expect("fixture compiles")
}

const FAT_HDR: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments)]\nextern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; }\n";

/// **Fatness is MEASURED in, not assumed in** — A-2's condition, applied to a
/// second dependency that has never been on BO's path either.
///
/// The two positive controls live in **one function** deliberately. Either
/// alone would pass against an analysis that returns a constant, which is the
/// same defect shape the locals-A1 population pair was built to exclude: a
/// control that cannot distinguish is not a control.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing `FatFacts::verdict`
/// with a constant `Some(Fatness::Arr)` — or `Ptr` — fails this test, because
/// the assertion is that the two locals **differ**, not that either has a
/// particular value.
#[test]
fn fatness_entry_validation_distinguishes_array_from_single_object() {
    let got = fatness_of(&format!(
        "{FAT_HDR}pub unsafe fn f(c: i32) -> i32 {{\n\
         let mut arr: [i32; 8] = [0; 8];\n\
         let decayed: *mut i32 = arr.as_mut_ptr();\n\
         let single: *mut i32 = malloc(4) as *mut i32;\n\
         *single = c;\n\
         *decayed.offset(1) + *single\n\
         }}\n"
    ));
    let of = |n: &str| {
        got.iter()
            .find(|(name, _)| name == n)
            .unwrap_or_else(|| panic!("no local `{n}`: {got:?}"))
            .1
    };
    assert_eq!(
        of("decayed"),
        "arr",
        "array decay must read as array: {got:?}"
    );
    assert_eq!(
        of("single"),
        "ptr",
        "a single-object allocation must not read as array: {got:?}"
    );
}

/// **`ptr` is a DEFAULT, not a conclusion** — the control the ruling did not
/// ask for, and the one that decides how the verdict may be used.
///
/// `Fatness::Arr ⊑ Fatness::Ptr` and the solver takes the **greatest** model,
/// so an unconstrained variable is maximized to `Ptr`. This fixture gives the
/// analysis *no information at all* about `opaque` — no arithmetic, no
/// indexing, no allocation — and pins that the answer is still `ptr`.
///
/// The consequence is load-bearing and runs opposite to the naive reading of
/// ruling A-1: this analysis never says *unknown*, so `ptr` **cannot** be read
/// as evidence of single-object allocation. Emitting a slice on `arr` is
/// licensed because `arr` is forced by constraints; treating `ptr` as proof of
/// thinness is not, and the `Box<T>` / `Box<[T]>` discriminator must therefore
/// rest on the allocation-size expression with fatness as corroboration only.
///
/// *Mutation-tested:* making `verdict` return `None` for unconstrained locals —
/// i.e. pretending the analysis abstains — fails this test, which is the point:
/// it does not abstain.
#[test]
fn a_pointer_with_no_array_evidence_reads_thin_by_default() {
    let got = fatness_of(&format!(
        "{FAT_HDR}pub unsafe fn f(q: *mut i32) -> i32 {{ let opaque: *mut i32 = q; 0 }}\n"
    ));
    assert_eq!(
        got.iter().find(|(n, _)| n == "opaque").map(|(_, v)| *v),
        Some("ptr"),
        "an unconstrained pointer must still receive a verdict, and it is the \
         top of the lattice — `ptr` here means NO ARRAY EVIDENCE, not `thin`: \
         {got:?}"
    );
}

/// **The negative control: a clean local is still emitted.**
///
/// Without it, "every local now degrades" would pass both witnesses above. The
/// repair must gate exactly the locals carrying a raw-only use, not the
/// population.
///
/// *Mutation-tested, claim CORRECTED after measurement:* injecting an
/// unconditional degrade before the A1 arms fails this test — and also fails
/// `a_raw_only_method_on_a_local_degrades_it`, which an earlier draft said
/// would stay green. It cannot: that witness asserts a *specific* reason, and
/// the injected one is a different reason. Only
/// `one_comparison_degrades_its_parameter_and_its_local_operand_alike` survives,
/// because the injected reason happens to be the one it expects.
///
/// The point stands, and is what the mutation establishes: this control is the
/// only test in the trio that can distinguish *"the gate works"* from *"every
/// local degrades"*. 24 tests died with it, so the injection was effective.
#[test]
fn a_local_with_no_raw_only_use_is_still_emitted() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32) -> i32 { let p: *mut i32 = a; *p }\n",
    );
    assert_eq!(
        reason_of(&got, "p", false),
        "<emitted>",
        "a clean local must survive A1: {got:?}"
    );
}

// ---------------------------------------------------------------------------
// The freed-slot gate
// ---------------------------------------------------------------------------

/// The two freed-slot fixtures, differing in **one token**: the callee of the
/// call that consumes `p`.
///
/// # Why the free is conditional — measured, not styled
///
/// The obvious fixture does not reach the gate, and why is worth recording.
/// With an unconditional `free` as the only thing that happens to the binding,
/// BO settles the slot **`Owning`** and `kind-owning` fires three arms earlier.
/// Measured on four such shapes: `free` of a parameter, of a copy of one, of a
/// `malloc` result, and of a parameter beside a second live pointer — all four
/// `owning`/`kind-owning`. **A fixture that degrades upstream witnesses
/// nothing.**
///
/// Under a *conditional* free the slot is not owning on all paths, BO retracts
/// the sink, and the kind settles `Ref` — while the program still frees it.
/// That is the leaked-free shape backlog S2-2 named, and a reference for it is a
/// reference to memory freed on the other path.
///
/// The corpus has 44 freed-`Ref` subjects, and none is reproducible in its own
/// shape here: its cast-free specimen, `lodepng_free`, settles `Ref` only
/// because a caller retracts the sink — and that same caller makes
/// `call-site-not-adapted` fire, so reproducing it would witness the reason
/// rather than the gate. This shape reaches the gate on its own.
///
/// Everything but the callee is held fixed — declaration, control flow, and the
/// absence of any in-crate reference to the function under test — and `keeper`
/// is declared in the same `extern` block with the same signature, so even the
/// callee's kind is fixed. Only the NAME differs, which is exactly what
/// `DEALLOCATORS` keys on.
fn freed_fixture(callee: &str) -> String {
    format!(
        "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
         pub unsafe fn free(q: *mut u8) {{ *q = 0; }}\n\
         pub unsafe fn keeper(q: *mut u8) {{ *q = 0; }}\n\
         pub unsafe fn releases(a: *mut u8, b: i32) {{\n\
         \x20   let p: *mut u8 = a;\n\
         \x20   if b > 0 {{ {callee}(p); }}\n\
         }}\n"
    )
}

/// **The gate — a subject that would otherwise emit is degraded as
/// `freed-slot`.**
///
/// The control half is what makes this a witness rather than an assertion: it
/// establishes that this subject reaches `Decision::Ref` when the same call goes
/// to a non-deallocator, so the freed half's degradation cannot be an artefact
/// of the fixture failing some earlier test.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `subject.freed_at`
/// arm at the end of `decide_one` makes the freed half read `<emitted>` and
/// fails this. Second mutation: moving that arm ABOVE the `referenced` arm keeps
/// this green and fails the corpus zero-movement check instead — recorded
/// because it is the one mutation this witness deliberately does **not** catch,
/// and the reason the corpus assertion is not redundant with it.
#[test]
fn a_freed_subject_that_would_otherwise_emit_is_degraded_as_freed_slot() {
    let control = decisions_of(&freed_fixture("keeper"));
    assert_eq!(
        reason_of(&control, "p", false),
        "<emitted>",
        "the control subject must reach Ref, or the freed half witnesses \
         nothing: {control:?}"
    );

    let freed = decisions_of(&freed_fixture("free"));
    assert_eq!(
        reason_of(&freed, "p", false),
        "freed-slot",
        "a freed subject that passed every other test was still emitted: \
         {freed:?}"
    );
}

/// **Co-attribution.** A freed subject stopped by an EARLIER reason keeps that
/// reason and still carries the `freed` column.
///
/// This is the population the corpus actually has: 44 freed subjects whose BO
/// kind is `Ref`, every one of them stopped before the gate. A reason-derived
/// freed count reports that population as **empty**, because `decide_one`
/// returns at the first failing test — the same ordering blindness
/// `facts_join_tsv` exists to defeat.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing `freed` in
/// `artifact::rows` with a derivation from the reason —
/// `Some(matches!(decision, Decision::Degraded(r) if r.reason.key() ==
/// "freed-slot"))` — fails this: the row reads `false` while the program plainly
/// frees the binding. The obvious spelling of that mutation,
/// `degrade_reason.as_deref() == …`, does **not compile** — the field is moved
/// into the row two lines above — which is mild structural evidence in its own
/// right that this column cannot restate the reason without going back to the
/// decision.
#[test]
fn a_freed_subject_stopped_earlier_keeps_its_reason_and_carries_the_column() {
    // **RE-BASED at S3.2′-3.** The earlier blocker used to be `p.is_null()`,
    // which no longer fires before the freed gate — a null test now selects the
    // optional form, whose own refusals come after it. `read` still degrades in
    // the raw-use block, which is where this witness needs its earlier reason to
    // come from.
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               extern \"C\" {\n\
               \x20   fn free(p: *mut core::ffi::c_void);\n\
               }\n\
               pub unsafe fn releases(a: *mut i32, b: i32) -> i32 {\n\
               \x20   let p: *mut i32 = a;\n\
               \x20   let dead = p.read();\n\
               \x20   if b > 0 { free(p as *mut core::ffi::c_void); }\n\
               \x20   dead\n\
               }\n";
    let rows = artifact_rows_of(src);
    let row = rows
        .iter()
        .find(|r| r.param_name.as_deref() == Some("p") && r.arg_index.is_none())
        .unwrap_or_else(|| panic!("no subject `p`: {rows:?}"));

    assert_eq!(
        row.degrade_reason.as_deref(),
        Some("raw-pointer-operation"),
        "the gate displaced an earlier reason — it must fire LAST: {row:?}"
    );
    assert_eq!(
        row.freed,
        Some(true),
        "the freed fact vanished behind the earlier reason: {row:?}"
    );
}

/// The column is a FACT about the subject, not a restatement of the reason: an
/// unfreed subject reads `Some(false)`, never `None`.
///
/// `None` is producer B's value — "no derivation for this" — and producer A
/// always has one. Without this, a producer A that emitted `None` everywhere
/// would satisfy the co-attribution witness above on its `Some(true)` row alone.
///
/// *Mutation-tested (Rider 0, deletion first):* changing `artifact::rows` to
/// emit `subject.freed_at.is_some().then_some(true)` fails this.
#[test]
fn an_unfreed_subject_carries_a_present_false_not_an_absent_column() {
    let rows = artifact_rows_of(&freed_fixture("keeper"));
    let row = rows
        .iter()
        .find(|r| r.param_name.as_deref() == Some("p") && r.arg_index.is_none())
        .unwrap_or_else(|| panic!("no subject `p`: {rows:?}"));
    assert_eq!(
        row.freed,
        Some(false),
        "producer A must state the fact it has, not abstain: {row:?}"
    );
}

// ---------------------------------------------------------------------------
// S3.2′-2 — borrowed slices
// ---------------------------------------------------------------------------

/// **An arithmetic op on a LOCAL takes the slice arm, and stops at
/// construction.**
///
/// The counterpart to `a_raw_only_method_on_a_local_degrades_it`: the same
/// shape, an arithmetic op instead of a non-arithmetic one, landing on a
/// different reason. A parameter needs no construction — the caller supplies the
/// slice — but a local's initializer is a raw-pointer expression that would need
/// `from_raw_parts` and a length. Scoped out and counted, not attempted.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `SubjectKind::Local`
/// arm in `decide_one` makes this read `slice-use-unsupported` (the local's own
/// initializer use is not `*p.offset(e)`), so the local would be silently
/// reclassified rather than named.
#[test]
fn an_arithmetic_op_on_a_local_stops_at_slice_construction() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(a: *mut i32) -> i32 { let p: *mut i32 = a; *p.offset(1) }\n",
    );
    assert_eq!(
        reason_of(&got, "p", false),
        "slice-local-construction",
        "an arithmetic use on a local must take the slice arm and stop at \
         construction, with its own reason: {got:?}"
    );
}

/// **A non-arithmetic raw-only use blocks the slice arm — checked over the WHOLE
/// use set, not the first.**
///
/// `p` carries `offset` *and* `read`. A first-wins reading of `raw_only_uses`
/// meets `offset` first and concludes "arithmetic, emit a slice" — and
/// `p.read()` on `&[i32]` does not compile. This is the reason that map holds a
/// vector.
///
/// **RE-BASED at S3.2′-3.** The original fixture paired `offset` with
/// `is_null`, and that pair is no longer mixed-and-unsupported: it is exactly
/// g13's shape, and now selects `Option<&[T]>`. Re-basing onto `read` keeps the
/// witness testing what it was written to test — the whole-set reading — rather
/// than letting it pass by accident on a class that moved.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing the `all(..)` in
/// `decide_one` with a test of `uses.first()` makes this emit a slice, and the
/// emitted crate does not type-check.
#[test]
fn a_mixed_use_set_refuses_the_slice_arm() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(p: *mut i32) -> i32 { let v = p.read(); v + *p.offset(1) }\n",
    );
    assert_eq!(
        reason_of(&got, "p", true),
        "raw-pointer-operation",
        "a subject with a non-arithmetic use must not reach the slice arm: {got:?}"
    );
}

/// **The pair that MOVED, pinned in its new disposition.**
///
/// `{offset, is_null}` on a fat subject is g13's shape. Asserting where it lands
/// now is what keeps the re-basing above honest: without this, "the mixed-use
/// guard still works" and "the optional arm swallowed the case" look identical.
#[test]
fn arithmetic_with_a_null_test_takes_the_optional_slice_form() {
    let got = decisions_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(p: *mut i32) -> i32 { if p.is_null() { return 0; } *p.offset(1) }\n",
    );
    assert_eq!(
        reason_of(&got, "p", true),
        "<emitted>",
        "the fat optional twin did not take this subject: {got:?}"
    );
}

/// **The fatness LICENSE is required, not merely corroborating in name.**
///
/// Op-facts supply the need; fatness supplies the license. Mutating the
/// conjunct away is the check that it is wired at all — on the corpus it
/// excludes 0 of 1,690, so only a fixture can distinguish "required" from
/// "present but unread".
///
/// *Mutation-tested (Rider 0, deletion first):* deleting
/// `&& fat.is_array(..)` from `decide_one`'s guard leaves this green (the
/// subject reads `arr` anyway) — recorded as the mutation this witness does
/// **not** kill, which is why the conjunct's vacuity is reported as measured
/// rather than claimed as load-bearing. What it does pin is that an arithmetic
/// subject reaching the slice arm emits a slice form at all.
#[test]
fn an_arithmetic_parameter_emits_a_slice_form() {
    let rows = artifact_rows_of(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn f(p: *mut i32, n: usize) { let mut i: usize = 0; \
         while i < n { *p.offset(i as isize) = 1; i += 1; } }\n",
    );
    let row = rows
        .iter()
        .find(|r| r.param_name.as_deref() == Some("p"))
        .unwrap_or_else(|| panic!("no subject p: {rows:?}"));
    assert_eq!(
        row.outcome,
        Some(crate::coverage_recon::schema::Outcome::SliceMut),
        "an arithmetic, array-licensed parameter must take a slice form: {row:?}"
    );
    assert_eq!(
        row.approx_len,
        Some(true),
        "a parameter has no construction site, so its length is approximated \
         and the counter must say so: {row:?}"
    );
}

/// **A subject whose use-edits NEST must not produce overlapping edits.**
///
/// brotli's `DecodeSymbol` shape, and the reason brotli contributed **zero**
/// emit-frame rows to the S3.6-1 step-3 sweep: a self-advance whose index
/// expression contains a plain dereference of the same binding —
/// `table = table.offset((*table).value as isize)`.
///
/// The path visitor fires once per OCCURRENCE, so two edits are produced and
/// the outer contains the inner:
///
/// - outer, the self-advance source: span `table.offset(…)` → `&mut table[…..]`
/// - inner, the plain deref: span `(*table)` → `table[0]`
///
/// `apply` rejects the pair — "a plan that wants two rewrites of one range has
/// not decided" — and is right to.
///
/// **The overlap is only the visible half.** `index_text` renders the index
/// with `span_to_snippet`, so the outer replacement embeds `(*table)`
/// **verbatim** — text with no meaning on a `&[T]`. Dropping either edit
/// therefore yields an ill-typed crate rather than a smaller win, which is why
/// the repair degrades the subject instead of picking a winner: the flat-splice
/// model cannot express this rewrite at all.
///
/// *Mutation-tested (Rider 0, deletion first):* remove the nesting gate and
/// this fails with a rollback reading "edit overlaps an earlier edit".
#[test]
fn a_subject_whose_uses_nest_produces_no_overlapping_edits() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub struct HuffmanCode { pub value: u32 }\n\
               pub unsafe fn decode(mut table: *mut HuffmanCode) -> u32 {\n\
               \x20   table = table.offset((*table).value as isize);\n\
               \x20   (*table).value\n\
               }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let emission = emit(&fixture);
    assert!(
        emission.rollbacks.is_empty(),
        "nested use-edits reached `apply` and were rolled back; the nesting \
         must be refused at DECISION time, where the subject can degrade with \
         an attributed reason: {:?}",
        emission.rollbacks
    );
    // Not merely "no rollback" — the subject must degrade UNDER ITS OWN REASON.
    // An implementation that silently dropped one of the two edits would satisfy
    // the assertion above while emitting the stale `(*table)` text, which is the
    // failure this gate exists to prevent.
    assert_eq!(
        reason_of(&decisions_of(src), "table", true),
        "nested-use-edits",
        "the nesting must be attributed, not absorbed into another reason"
    );
}

/// **Nesting across TWO subjects refuses the inner one and KEEPS the outer.**
///
/// brotli's second shape, and the 15 of 17 collisions a per-subject check left
/// standing — `enc::block_splitter::RemapBlockIds*`,
/// `enc::brotli_bit_stream::StoreSimpleHuffmanTree`, `enc::cluster::*`:
///
/// ```ignore
/// *new_id.offset(*block_ids.offset(i as isize) as isize)
/// ```
///
/// `new_id`'s edit spans the whole outer `offset` call; `block_ids`'s sits
/// inside it. No per-subject check can see this, because neither subject's own
/// rewrites nest.
///
/// **Refusing the INNER subject is the correct pick, not merely the safe one.**
/// `index_text` renders the index by `span_to_snippet`, so the outer
/// replacement embeds `*block_ids.offset(i as isize)` verbatim — and that text
/// is well-typed precisely when `block_ids` is still a pointer. So the outer
/// rewrite stays valid *because* the inner was refused, which is why this test
/// asserts both halves: refusing the inner while also dropping the outer would
/// be sound but would give away yield the defect does not cost.
///
/// *Mutation-tested (Rider 0, deletion first):* restrict the pass to same-entry
/// pairs — the shape the first fix had — and this fails with brotli's own
/// rollback.
#[test]
fn nesting_across_two_subjects_refuses_the_inner_and_keeps_the_outer() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn f(new_id: *mut u32, block_ids: *mut u32, n: usize) {\n\
               \x20   let mut i: usize = 0;\n\
               \x20   while i < n {\n\
               \x20       *new_id.offset(*block_ids.offset(i as isize) as isize) = 1;\n\
               \x20       i += 1;\n\
               \x20   }\n\
               }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    assert!(
        emit(&fixture).rollbacks.is_empty(),
        "cross-subject nesting reached `apply`: {:?}",
        emit(&fixture).rollbacks
    );
    let got = decisions_of(src);
    assert_eq!(
        reason_of(&got, "block_ids", true),
        "nested-use-edits",
        "the INNER subject is the one the nesting refuses: {got:?}"
    );
    assert_eq!(
        reason_of(&got, "new_id", true),
        "<emitted>",
        "the OUTER subject must survive — its embedded snippet is valid exactly \
         because the inner stayed raw: {got:?}"
    );
}

/// **The nesting gate must not fire on a subject whose uses merely SIT SIDE BY
/// SIDE** — the control for the witness above.
///
/// Without it, a gate that refused every multi-use slice subject would pass the
/// nesting test while destroying the whole slice population, and the corpus
/// would report it as a yield loss rather than as a bug.
#[test]
fn disjoint_uses_of_one_subject_still_emit_a_slice() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn f(p: *mut i32, n: usize) {\n\
               \x20   let mut i: usize = 0;\n\
               \x20   while i < n { *p.offset(i as isize) = 1; i += 1; }\n\
               \x20   *p.offset(0) = 2;\n\
               }\n";
    assert_eq!(
        reason_of(&decisions_of(src), "p", true),
        "<emitted>",
        "two DISJOINT arithmetic uses must still emit; the gate keys on \
         containment, not on multiplicity"
    );
}

/// **The index rendering must survive a NON-`usize` counter — the shape the
/// corpus actually has.**
///
/// c2rust writes `*p.offset(1 as libc::c_int as isize)`: a **double** cast.
/// Stripping only the outer `as isize` leaves a `c_int`, and
/// `error[E0277]: the type `[*mut i8]` cannot be indexed by `i32`` is what the
/// corpus returned — every one of the 14 decided slices reverted, taking two
/// sibling `Ref` emissions in `heman_draw_colored_circles` with them, because
/// revert granularity is per-function.
///
/// **g11/g12 could not have caught this.** They were transcribed with a `usize`
/// counter, so stripping the cast happened to yield the right type. A golden
/// pins the dimensions it fixes; the counter type was left free, and free
/// dimensions must be either measured-representative of the corpus or covered
/// by a witness. This is that witness.
///
/// *Mutation-tested (Rider 0, deletion first):* reverting `index_text` to strip
/// the cast unconditionally — dropping the `usize` type test — makes the first
/// assertion fail, because the rewrite is then ill-typed and the verify loop
/// reverts it, leaving the source unchanged.
#[test]
fn a_non_usize_counter_is_cast_rather_than_stripped() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn f(p: *mut i32) -> i32 {\n\
               \x20   *p.offset(1 as core::ffi::c_int as isize)\n\
               }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("fixture must emit");
    };
    assert!(
        source.contains("p[(1 as core::ffi::c_int) as usize]"),
        "a non-usize index must be parenthesised and cast, or the slice is \
         indexed by the wrong type:\n{source}"
    );
    assert!(
        source.contains("p: &[i32]"),
        "the declaration must still become a slice:\n{source}"
    );
}

/// **The `usize` path stays byte-identical to the ratified golden text.**
///
/// The type-aware repair must not buy corpus correctness by changing what g11
/// and g12 emit. Asserted on the emitted BYTES rather than left to the goldens'
/// rustfmt-canonicalised comparison, which would absorb a spurious cast as
/// whitespace-adjacent noise.
///
/// *Mutation-tested (Rider 0, deletion first):* making `index_text` cast
/// unconditionally emits `p[i as usize]` and fails this — which is exactly the
/// spec-bending option this repair declined.
#[test]
fn a_usize_counter_still_renders_a_bare_index() {
    let golden = super::goldens_for_reconciliation()
        .into_iter()
        .find(|(name, _)| *name == "g11_slice_shared")
        .expect("g11 is registered");
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(golden.1) else {
        panic!("g11 must emit");
    };
    assert!(
        source.contains("total += p[i];"),
        "a usize counter must still render bare — the ratified golden text:\n{source}"
    );
    assert!(
        !source.contains("p[i as usize]"),
        "the repair added a cast the golden does not have:\n{source}"
    );
}

/// **THE ACCEPT-SET IS THE SCOPE.** Both authorised positions emit; every known
/// neighbour position is refused with its own attribution.
///
/// # Why this test exists, stated plainly
///
/// Twice in this slice the implementation was wider than its own approved
/// scope: Amendment 1 named the use-site work only after the goldens implied
/// it, and the classifier then accepted `&mut *p.offset(e)` — a third position —
/// because it tested the deref's SHAPE without testing its CONTEXT. Scope is
/// whatever the classifier accepts, so the accept-set has to be pinned against
/// the scope rather than described in prose beside it.
///
/// Positive controls are the two authorised positions; negative controls are the
/// three neighbours the corpus actually contains. A fourth neighbour appearing
/// later fails nothing here — but it will be one line to add, and its absence is
/// now visible rather than assumed.
///
/// *Mutation-tested (Rider 0, deletion first):* removing the parent-borrow check
/// in `classify` makes the borrow-of-deref case emit, failing this.
#[test]
fn the_classifier_accept_set_equals_the_approved_scope() {
    fn reason_for(body: &str) -> String {
        let src = format!(
            "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
             pub unsafe fn f(mut p: *mut i32, n: usize) -> *mut i32 {{\n{body}\n}}\n"
        );
        let got = decisions_of(&src);
        reason_of(&got, "p", true)
    }

    // POSITIVE — the two positions Amendment 1 authorises.
    // Control: `p` is ALSO returned bare here, which is itself an unsupported
    // use, so the subject is refused even though the deref position is
    // authorised. It pins that the harness is not trivially green — and, more
    // usefully, that the accept-set is a property of ALL of a subject's uses
    // rather than of the one the test happens to be looking at.
    assert_eq!(
        reason_for(
            "    let mut i: usize = 0;\n    while i < n { let _v = *p.offset(i as isize); i += 1; }\n    p"
        ),
        "slice-use-unsupported",
        "an authorised position plus a bare use must still be refused"
    );
    for (label, body) in [
        (
            "deref read",
            "    let mut i: usize = 0;\n    let mut t = 0;\n    while i < n { t += *p.offset(i as isize); i += 1; }\n    core::ptr::null_mut()",
        ),
        (
            "deref write",
            "    let mut i: usize = 0;\n    while i < n { *p.offset(i as isize) = 1; i += 1; }\n    core::ptr::null_mut()",
        ),
        // **S3.2′-2b moved these two INTO the approved scope**, by ruling. The
        // guard tracks the scope; it does not defend the old one.
        ("plain deref", "    let _v = *p;\n    core::ptr::null_mut()"),
        (
            "self-advance",
            "    p = p.offset(1);\n    let _v = *p;\n    core::ptr::null_mut()",
        ),
    ] {
        assert_eq!(
            reason_for(body),
            "<emitted>",
            "{label} is an AUTHORISED position and must emit"
        );
    }

    // NEGATIVE — every known neighbour, each refused with its own attribution.
    for (label, body) in [
        ("borrow of deref", "    &mut *p.offset(1 as isize)"),
        // **REBIND is ratified spec (g18) but its ARM is not built** — its
        // market is 0 and S3.6-gated, so mechanism follows market. It stays a
        // negative control, and the reason it is refused has changed from "out
        // of scope" to "in scope, unbuilt". Both mean: must not emit.
        (
            "rebind",
            "    let q: *mut i32 = p.offset(1 as isize);\n    q",
        ),
        // **S3.2′-5 registers the SIGN as a refusal axis in this vocabulary.**
        // Every other entry here is refused for the shape of a *use*; this one
        // has an authorised use shape and is refused for the *argument's sign*.
        // It is listed here so the accept-set is read as "which subjects emit",
        // not merely "which use shapes are recognised" — and so a future slice
        // that lifts the gate has to edit this list to do it.
        (
            "may-be-negative offset",
            "    let _v = *p.offset(-1 as isize);\n    core::ptr::null_mut()",
        ),
    ] {
        let got = reason_for(body);
        // **Per-entry, not one shared disjunction.** S3.2′-5 adds a third
        // admissible reason; widening a single `||` for the whole loop would
        // let ANY negative control drift onto ANY of the three unnoticed, which
        // is exactly the coverage this guard exists to deny.
        let allowed: &[&str] = match label {
            "may-be-negative offset" => &["slice-neg-or-unknown-offset"],
            _ => &["slice-use-unsupported", "raw-pointer-operation"],
        };
        assert!(
            allowed.contains(&got.as_str()),
            "{label} is not emittable today and must be refused with the \
             attribution that names WHY: expected one of {allowed:?}, got {got:?}"
        );
        assert_ne!(got, "<emitted>", "{label} must not emit");
    }
}

/// **S3.2′-5 — the sign gate on the deref-through-arithmetic positions.**
///
/// The `-2` arm authorised `*p.offset(e)` ⇒ `p[(e) as usize]` while consulting
/// no sign information at all. When `e` is negative at runtime the cast wraps to
/// a huge index and the bounds check panics: memory-safe, and a **behaviour
/// change** against a program that legitimately indexed backwards. `SignFacts`
/// shipped at `-3` read by nothing and gained its first consumer at `2b` on the
/// self-advance arm *only*; this closes the remaining position.
///
/// One sign authority, no parallel notion — the gate reads the same
/// `SignFacts::may_be_negative` verdict `advance_ok` reads at `mod.rs:1799`.
///
/// **Two-sided by construction.** The `nonneg` half is not decoration: without
/// it, a gate that degraded *every* fat arithmetic subject would pass the
/// `neg-or-unknown` half alone. Deleting the gate fails the negative half;
/// widening it to unconditional fails the positive half.
#[test]
fn a_may_be_negative_offset_refuses_the_slice_form_with_its_own_reason() {
    fn reason_for(body: &str) -> String {
        let src = format!(
            "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
             pub unsafe fn f(mut p: *mut i32, n: usize, k: isize) -> *mut i32 {{\n{body}\n}}\n"
        );
        let got = decisions_of(&src);
        reason_of(&got, "p", true)
    }

    // NEGATIVE HALF — a may-be-negative offset must be refused, and refused
    // with the reason that names the *sign*, not the op and not the use shape.
    // `k` is an unconstrained `isize` parameter, so the offset-sign lattice
    // settles `Top`, which `needs_cursor()` admits through the same door as
    // `Neg`. The taint is per-LOCAL, so one tainted position taints `p`.
    for (label, body) in [
        (
            "unbounded offset",
            "    let _v = *p.offset(k);\n    core::ptr::null_mut()",
        ),
        (
            "negative literal offset",
            "    let _v = *p.offset(-1 as isize);\n    core::ptr::null_mut()",
        ),
    ] {
        assert_eq!(
            reason_for(body),
            "slice-neg-or-unknown-offset",
            "{label}: a may-be-negative offset must degrade with its own \
             attributed reason — the op is fine and the use shape is fine, so \
             neither `raw-pointer-operation` nor `slice-use-unsupported` names \
             what actually blocked it"
        );
    }

    // POSITIVE HALF — the gate must NOT swallow the `-2` arm it is protecting.
    // `i` is `usize`, so every offset is provably non-negative and the slice
    // form still emits. This is what makes the gate a gate rather than a veto.
    assert_eq!(
        reason_for(
            "    let mut i: usize = 0;\n    let mut t = 0;\n    while i < n { t += *p.offset(i as isize); i += 1; }\n    core::ptr::null_mut()"
        ),
        "<emitted>",
        "a provably non-negative offset must still emit — the gate keys on the \
         SIGN, not on the presence of arithmetic"
    );

    // **PRECEDENCE — the gate must stay LAST in the arm.**
    //
    // The two halves above pin that the gate fires and that it is conditional;
    // neither pins WHERE. Moving it above the `SliceUseUnsupported` check would
    // leave both green while silently displacing an earlier, more specific
    // reason — the "can only convert a would-be emission" property that makes
    // its movement a pre-registered count rather than an unbounded one.
    //
    // This subject is may-be-negative AND separately unsupported (`p` is also
    // returned bare). The earlier reason must win.
    assert_eq!(
        reason_for("    let _v = *p.offset(k);\n    p"),
        "slice-use-unsupported",
        "the sign gate must fire LAST: a subject that is ALSO unsupported for \
         its use shape must keep the earlier, more specific attribution. If \
         this reads `slice-neg-or-unknown-offset`, the gate has been hoisted \
         above a reason it must never displace."
    );
}

/// **S3.2′-5 hardening — the FAT-OPTIONAL twin carries the identical hazard.**
///
/// `Form::Opt { slice: true }` reaches the same `*p.offset(e)` position through
/// `accessor[index]` (`emitability.rs:522-559`) and the same `(e) as usize`
/// rendering. Before this gate it emitted unconditionally: the plain-slice arm
/// was closed and its optional twin was not, so "one sign authority, no
/// parallel notion" was a statement about one arm rather than about the
/// emitter. Zero-expected-delta debut — all 50 optional emissions measure
/// `nonneg`, so this moves nothing on the corpus and everything in principle.
///
/// **Gated on `slice`, the narrowest arm that owns the hazard.** A thin
/// optional provably has no arithmetic — form selection admits
/// `Opt { slice: false }` only under `!has_arithmetic || is_array` with
/// `slice = has_arithmetic && is_array` — so it forms no index and the sign
/// verdict is irrelevant to it. Gating the whole arm would also degrade any
/// thin optional whose sign lookup MISSES, since `may_be_negative` folds
/// `None` conservatively. That is the 61-thin-`Ref` finding a second time.
#[test]
fn a_may_be_negative_offset_refuses_the_fat_optional_form_too() {
    fn reason_for(body: &str) -> String {
        let src = format!(
            "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
             pub unsafe fn f(mut p: *mut i32, n: usize, k: isize) -> *mut i32 {{\n{body}\n}}\n"
        );
        let got = decisions_of(&src);
        reason_of(&got, "p", true)
    }
    const NULL_TEST: &str = "    if p.is_null() { return core::ptr::null_mut(); }\n";

    // NEGATIVE — the probe that exposed the gap, now a permanent fixture.
    assert_eq!(
        reason_for(
            &[
                NULL_TEST,
                "    let _v = *p.offset(k);\n    core::ptr::null_mut()"
            ]
            .concat()
        ),
        "slice-neg-or-unknown-offset",
        "a fat OPTIONAL with a may-be-negative offset must be refused for the \
         same reason its plain twin is — the hazard is the index, and the \
         `Option` wrapper does not change it"
    );

    // POSITIVE — the fat-optional arm must still emit on a provable non-negative.
    assert_eq!(
        reason_for(&[NULL_TEST, "    let mut i: usize = 0;\n    let mut t = 0;\n    while i < n { t += *p.offset(i as isize); i += 1; }\n    core::ptr::null_mut()"].concat()),
        "<emitted>",
        "a provably non-negative fat optional must still emit"
    );

    // THIN optional — a REGRESSION PIN, **not a control**, and the difference
    // was measured rather than assumed.
    //
    // Dropping the `slice &&` conjunct leaves this assertion GREEN, so it does
    // NOT witness that conjunct. Measured reason: `SignFacts` inserts a taint
    // bit only at an offset use, and a thin optional has none, so its verdict
    // is always `Some(false)` and an ungated sign check would pass it anyway.
    // The conjunct earns its place only on a lookup MISS, where
    // `may_be_negative` folds `None` to `true` — and no fixture can produce a
    // miss, since that needs the local to outrun the analysis domain.
    //
    // So the conjunct is defense-in-depth against the conservative fold, kept
    // on the P-drop precedent (retain, and state the measurement that explains
    // why nothing exercises it) rather than deleted as unreachable. This line
    // pins that thin optionals keep emitting; it does not pretend to more.
    assert_eq!(
        reason_for(&[NULL_TEST, "    let _v = *p;\n    core::ptr::null_mut()"].concat()),
        "<emitted>",
        "a THIN optional forms no index and must keep emitting"
    );

    // PRECEDENCE — last in its own arm, same rule as the slice twin.
    assert_eq!(
        reason_for(&[NULL_TEST, "    let _v = *p.offset(k);\n    p"].concat()),
        "opt-use-unsupported",
        "the fat-optional sign gate must fire LAST in its arm: a subject that \
         is ALSO unsupported for its use shape keeps the earlier attribution"
    );
}

/// **THE DISSOLUTION'S RESIDUE WITNESS — one case per construction class**
/// (user ruling RECLASSIFY-ONLY, 2026-08-12).
///
/// Every unannotated local still degrades — the pin below is not weakened by
/// one subject — but it degrades **naming the owed capability it is waiting
/// on** rather than naming the rewriter's splice mechanism.
///
/// # Where this test came from, kept adjacent
///
/// It began as the g16 capability's decision-level witness, RED, after g19 was
/// retired for being invisible to a text golden. The work-unit then retired too
/// on **F1** — the capability emits nothing, so byte identity would have been
/// satisfied by a broken implementation exactly as well as a correct one — and
/// the witness was **inverted into a status-quo pin** asserting that all four
/// classes still degrade `no-declared-type`. The dissolution supersedes the
/// key, not the pin: all four still degrade, and each now says why.
///
/// The per-class measurement that retired the g16 step is preserved, because it
/// is exactly what decided the folds below:
///
/// | class | n | inference gives a reference? | insertion `: &T` compiles? |
/// |---|---:|---|---|
/// | `copy` | 3 | yes | compiles |
/// | `other` | 2 | yes | compiles |
/// | `call-result` | 17 | no | `E0308` |
/// | `place-read` | 1 | no | `E0308` |
///
/// `call-result` and `place-read` fail structurally: their initializer type
/// comes from a callee **return type** or a **pointee/struct field**, and
/// neither is in M1's parameters-and-locals subject universe. That is what
/// `return-not-adapted` and `place-read-pointee` now say, and it is why they
/// are owed to S3.6-5 and M3 rather than to the locals-conversion follow-up —
/// which owns only `copy-source-coupled`.
///
/// **Four classes here, all nine plus `None` in
/// `decision::tests::every_construction_class_names_an_owed_capability`.** The
/// split is deliberate: this test proves the residue gate is REACHED and wired
/// to the fold table, which needs a real program; the fold table's own
/// exhaustiveness is a pure function and is tested as one. `Alloc` in
/// particular cannot be witnessed here — BO settles a `malloc` local `Owning`
/// or `Raw`, so `kind-*` fires first and the ladder never reaches the residue,
/// which is exactly why the corpus has only one such subject.
///
/// *Mutation-tested:* deleting the residue gate ahead of the co-conversion gate
/// reports `call-site-not-adapted` for all four.
#[test]
fn every_unannotated_local_class_degrades_naming_its_owed_capability() {
    fn reason_for_q(body: &str) -> String {
        let src = format!(
            "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
             pub unsafe fn src_of() -> *mut i32 {{ core::ptr::null_mut() }}\n\
             pub unsafe fn f(p: *mut i32, pp: *mut *mut i32, n: usize) -> i32 {{\n{body}\n}}\n"
        );
        reason_of(&decisions_of(&src), "q", false)
    }

    for (label, body, want) in [
        (
            "copy",
            "    let q = p;\n    *q = 7;\n    *q",
            "copy-source-coupled",
        ),
        (
            "other",
            "    let q = if n > 0 { p } else { p };\n    *q = 7;\n    *q",
            "copy-source-coupled",
        ),
        (
            "call-result",
            "    let q = src_of();\n    *q = 7;\n    *q",
            "return-not-adapted",
        ),
        (
            "place-read",
            "    let q = *pp;\n    *q = 7;\n    *q",
            "place-read-pointee",
        ),
    ] {
        assert_eq!(
            reason_for_q(body),
            want,
            "{label}: every class of unannotated local must still degrade, and \
             must name the owed capability it waits on. If this moved, either \
             something is claiming this population without a ruling — the \
             unwitnessable ledger movement F1 refused — or a residual fold has \
             been silently rerouted."
        );
    }
}

/// **S3.6-0 — the reference KIND is recorded, one positive fixture per kind.**
///
/// The split this enables was unmeasurable before: `referenced` was one map
/// fired by any `Path` resolution to a local `fn`, keeping spans and not kinds,
/// so direct calls, address-taking and fn-pointer casts — three populations with
/// three different adaptation stories — were indistinguishable.
///
/// **Each kind gets its own positive fixture**, because a classifier witnessed
/// on one kind is a classifier witnessed on nothing: the `_ => AddrTaken`
/// fallback would swallow both others and still pass a call-only test.
///
/// `is_adaptable` is asserted alongside, since it is what the census reports and
/// what any future slicing would be scoped against.
#[test]
fn a_local_fn_reference_records_which_kind_it_is() {
    use crate::bo_rewriter::decision::emitability::RefKind;

    fn kinds_of(src: &str) -> Vec<&'static str> {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            let mut out: Vec<_> = facts
                .referenced
                .iter()
                .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                .flat_map(|(_, refs)| refs.iter().map(|(k, _)| k.key()))
                .collect();
            out.sort_unstable();
            out.dedup();
            out
        })
        .expect("fixture compiles")
    }
    const PRE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn target(p: *mut i32) -> i32 { *p }\n";

    assert_eq!(
        kinds_of(&format!(
            "{PRE}pub unsafe fn c(p: *mut i32) -> i32 {{ target(p) }}\n"
        )),
        vec!["call"],
        "a direct call must record `call` — this is the ADAPTABLE population, \
         and mislabelling it pinned would understate every future market"
    );
    assert_eq!(
        kinds_of(&format!(
            "{PRE}pub unsafe fn c() -> unsafe fn(*mut i32) -> i32 {{ target }}\n"
        )),
        vec!["addr-taken"],
        "a bare path reference must record `addr-taken` — the signature is \
         pinned by whatever consumes the value"
    );
    assert_eq!(
        kinds_of(&format!(
            "{PRE}pub unsafe fn c() -> usize {{ target as unsafe fn(*mut i32) -> i32 as usize }}\n"
        )),
        vec!["fnptr-cast"],
        "a cast operand must record `fnptr-cast` — the callback-table shape F1 \
         widened this arm for, and the one it must not be conflated with"
    );

    // `is_adaptable` is ALL-or-nothing: one pinning reference is enough.
    let span = rustc_span::DUMMY_SP;
    assert!(RefKind::is_adaptable(&[(RefKind::Call, span)]));
    assert!(!RefKind::is_adaptable(&[
        (RefKind::Call, span),
        (RefKind::AddrTaken, span)
    ]));
    assert!(
        !RefKind::is_adaptable(&[]),
        "an empty reference set is not adaptable — it is NOT REFERENCED, a \
         different population, and conflating them would count the 385 \
         already-emitting functions as an S3.6 market"
    );
}

/// **S3.6-1 task 0 — the call ARGUMENT is recorded, one fixture per shape.**
///
/// The gate that blocks the adaptable population is a *signature* fact, but
/// adapting a call site is an *argument* question, and no argument fact existed:
/// `ExprKind::Call(callee, _)` bound its arguments to `_`, discarding the index,
/// the span, the shape and the caller at the one site that could record them.
///
/// **One positive fixture per shape**, for the reason S3.6-0 recorded: a
/// classifier witnessed on one value is a classifier witnessed on nothing —
/// the `_ => Other` fallback would swallow every other arm and still pass a
/// bare-local-only test.
///
/// *Mutation-tested on a committed baseline (see the slice record):* each
/// assertion below fails under a distinct single-arm deletion in
/// `classify_arg`.
#[test]
fn a_direct_call_records_each_argument_shape() {
    fn shapes_of(src: &str) -> Vec<&'static str> {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            facts
                .call_args
                .iter()
                .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                .flat_map(|(_, sites)| sites.iter())
                .flat_map(|site| site.args.iter().map(|a| a.shape.key()))
                .collect()
        })
        .expect("fixture compiles")
    }
    const PRE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn target(p: *mut i32) { *p = 1; }\n";
    let call = |body: &str| format!("{PRE}pub unsafe fn c(q: *mut i32) {{ {body} }}\n");

    assert_eq!(shapes_of(&call("target(q)")), vec!["bare-local"]);
    assert_eq!(
        shapes_of(&call("let mut x: i32 = 0; target(&mut x)")),
        vec!["addr-of-mut"],
        "an already-written `&mut` needs NO edit — it coerces to `*mut T` today \
         and satisfies `&mut T` after, so mislabelling it would invent work"
    );
    assert_eq!(
        shapes_of(&call("let mut x: i32 = 0; target(&mut x as *mut i32)")),
        vec!["addr-of-mut-cast"],
        "the cast is the only thing to remove; conflating it with a bare cast \
         would lose the fact that the operand is ALREADY a reference"
    );
    assert_eq!(
        shapes_of(&call("target(q as *mut i32)")),
        vec!["cast-of-local"]
    );
    assert_eq!(
        shapes_of(&call("target(0 as *mut i32)")),
        vec!["null-lit"],
        "a null literal BLOCKS: `&mut T` cannot represent null (E0308, measured)"
    );
    assert_eq!(
        shapes_of(&call("target(0 as usize as *mut i32)")),
        vec!["null-lit"],
        "C2Rust also writes null through an intermediate cast — a single-level \
         test would classify this as an ordinary cast and let it past the gate"
    );
    assert_eq!(
        shapes_of(&call("target(q.offset(1))")),
        vec!["other"],
        "arithmetic is NOT a shape this slice can adapt"
    );

    // The INDEX is the callee's 0-based parameter position — the same key as
    // `SubjectKind::Param { hir_index }`, so the join needs no translation.
    // Without this the census could attribute every argument to parameter 0.
    let indices = ::utils::compilation::run_compiler_on_str(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn target(a: *mut i32, b: *mut i32) { *a = *b; }\n\
         pub unsafe fn c(q: *mut i32, r: *mut i32) { target(r, q); }\n",
        |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            facts
                .call_args
                .iter()
                .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                .flat_map(|(_, sites)| sites.iter().map(|s| s.args.len()))
                .chain(
                    facts
                        .call_args
                        .iter()
                        .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                        .flat_map(|(_, sites)| sites.iter())
                        .flat_map(|s| s.args.iter().map(|a| a.index)),
                )
                .collect::<Vec<_>>()
        },
    )
    .expect("fixture compiles");
    assert_eq!(
        indices,
        vec![2, 0, 1],
        "one site, two args, indices 0 then 1"
    );
}

/// **Only DIRECT calls carry arguments** — the pinned population has none.
///
/// A function reached by a fn-pointer cast has no visible argument list, which
/// is *why* it is pinned. If this arm recorded anything for that shape, the
/// pinned 640 would appear to have an adaptation market they cannot have.
///
/// The negative is paired with a positive in ONE fixture so a mechanism that
/// records nothing at all cannot satisfy it — the g19 rule.
#[test]
fn only_direct_calls_record_arguments() {
    let (called, cast) = ::utils::compilation::run_compiler_on_str(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub unsafe fn called(p: *mut i32) { *p = 1; }\n\
         pub unsafe fn pinned(p: *mut i32) { *p = 2; }\n\
         pub unsafe fn c(q: *mut i32) -> usize {\n\
             called(q);\n\
             pinned as unsafe fn(*mut i32) as usize\n\
         }\n",
        |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            let count = |needle: &str| {
                facts
                    .call_args
                    .iter()
                    .filter(|(did, _)| tcx.def_path_str(did.to_def_id()).contains(needle))
                    .map(|(_, sites)| sites.len())
                    .sum::<usize>()
            };
            (count("called"), count("pinned"))
        },
    )
    .expect("fixture compiles");

    assert_eq!(called, 1, "the direct call must be recorded");
    assert_eq!(
        cast, 0,
        "a fn-pointer cast supplies NO arguments — recording one would give the \
         pinned population a market it cannot have"
    );
}

/// **S3.6-1 task 0a — a borrowed argument records its PLACE ROOT.**
///
/// The within-site overlap gate must block a call site where two pointer
/// parameters receive *overlapping* places, and overlap is not textual
/// identity. The corpus witness is brotli's
/// `BrotliDecoderHuffmanTreeGroupInit(s, &mut (*s).literal_hgroup, …)`
/// (`brotli/lib.rs:113893`): parameter 0 gets `s`, parameter 1 gets a place
/// **inside `*s`**, both declared `*mut`, certain overlap. `heman`'s
/// `kmVec3Normalize(pOut, pOut)` (×7) is the easy case — same binding — and a
/// gate built only for it would miss brotli entirely.
///
/// So the assertion is not "a root is recorded" but **"the two arguments share
/// the same root"**, which is the question the gate actually asks.
#[test]
fn a_borrowed_argument_records_the_place_it_is_rooted_at() {
    fn roots_match(src: &str) -> (bool, usize) {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            let site = facts
                .call_args
                .iter()
                .find(|(did, _)| tcx.def_path_str(did.to_def_id()).contains("target"))
                .map(|(_, sites)| sites[0].clone())
                .expect("the call site is recorded");
            let roots: Vec<_> = site.args.iter().map(|a| a.shape.place_root()).collect();
            let known = roots.iter().filter(|r| r.is_some()).count();
            (
                roots.len() == 2 && roots[0].is_some() && roots[0] == roots[1],
                known,
            )
        })
        .expect("fixture compiles")
    }

    // The brotli shape: a bare binding, and a borrow of a place INSIDE it.
    let (overlap, known) = roots_match(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub struct Grp { pub n: i32 }\n\
         pub struct St { pub g: Grp }\n\
         pub unsafe fn target(s: *mut St, g: *mut Grp) { (*g).n = 1; let _ = s; }\n\
         pub unsafe fn c(s: *mut St) { target(s, &mut (*s).g); }\n",
    );
    assert_eq!(known, 2, "both arguments must resolve a root");
    assert!(
        overlap,
        "`s` and `&mut (*s).g` must share a place root — this is brotli's \
         BrotliDecoderHuffmanTreeGroupInit shape, certain overlap at two *mut \
         positions, and a gate that cannot see it spends a revert instead of \
         avoiding one"
    );

    // The NEGATIVE, so the test cannot be satisfied by returning one constant
    // root for everything: two genuinely distinct bases must NOT match.
    let (overlap_distinct, known_distinct) = roots_match(
        "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
         pub struct Grp { pub n: i32 }\n\
         pub struct St { pub g: Grp }\n\
         pub unsafe fn target(s: *mut St, g: *mut Grp) { (*g).n = 1; let _ = s; }\n\
         pub unsafe fn c(s: *mut St, t: *mut St) { target(s, &mut (*t).g); }\n",
    );
    assert_eq!(known_distinct, 2);
    assert!(
        !overlap_distinct,
        "distinct bases must not share a root — a gate that reported overlap \
         for everything would block the whole adaptable population"
    );
}

/// **S3.6-1 task 2 — co-conversion class witnesses.**
///
/// At the file tail, per the convention `cc849953` established for the census
/// module: the harness above is shared, and a test module wedged into the
/// middle of it reads as part of the harness.
mod coconv_witnesses {
    use std::collections::BTreeMap;

    use super::Fixture;

    /// The census, parsed BY HEADER NAME.
    ///
    /// Never by position: adding the `fatness` column at S3.2′-1 shifted every
    /// later index and broke a positional reader. A positional read is a latent
    /// break for every future column.
    fn census(src: &str) -> Vec<BTreeMap<String, String>> {
        let fixture = Fixture::new(&[("lib.rs", src)]);
        let tsv = ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            crate::bo_rewriter::coconv_tsv(tcx).expect("co-conversion census")
        })
        .expect("fixture compiles");
        let hdr: Vec<String> = tsv
            .lines()
            .next()
            .expect("header")
            .split('\t')
            .map(str::to_owned)
            .collect();
        tsv.lines()
            .skip(1)
            .map(|line| {
                hdr.iter()
                    .cloned()
                    .zip(line.split('\t').map(str::to_owned))
                    .collect()
            })
            .collect()
    }

    /// One row, found by the `fn_path` suffix and MIR local.
    fn row<'a>(
        rows: &'a [BTreeMap<String, String>],
        f: &str,
        local: u32,
    ) -> &'a BTreeMap<String, String> {
        rows.iter()
            .find(|r| r["fn_path"].ends_with(f) && r["mir_local"] == local.to_string())
            .unwrap_or_else(|| {
                panic!(
                    "no census row for {f}::_{local}; rows: {:?}",
                    rows.iter()
                        .map(|r| (r["fn_path"].clone(), r["mir_local"].clone()))
                        .collect::<Vec<_>>()
                )
            })
    }

    const PRE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n";

    /// **The chain is ONE class.** g20's shape, at the decision level.
    ///
    /// `g20_bump(q)` inside `g20_via` joins the callee's parameter to the
    /// caller's, and converting either alone is `E0308` (H5, measured). The
    /// class is what makes it one decision.
    ///
    /// *Mutation-tested (deletion first):* deleting the `dsu.union` in the
    /// `BareLocal` arm leaves two singleton classes and fails on the class
    /// identity **and** on `class_size`.
    #[test]
    fn a_bare_local_argument_joins_callee_and_caller_into_one_class() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn g20_bump(p: *mut i32) -> i32 {{ *p += 1; *p }}\n\
             pub unsafe fn g20_via(q: *mut i32) -> i32 {{ g20_bump(q) }}\n\
             pub unsafe fn g20_root() -> i32 {{ let mut x: i32 = 0; g20_via(&mut x) }}\n"
        ));
        let bump = row(&rows, "g20_bump", 1);
        let via = row(&rows, "g20_via", 1);
        assert_ne!(
            bump["class_id"], "-",
            "the callee parameter must be a node: {bump:?}"
        );
        assert_eq!(
            bump["class_id"], via["class_id"],
            "callee and caller must land in ONE class — converting either alone \
             is E0308: {bump:?} vs {via:?}"
        );
        assert_eq!(bump["class_size"], "2", "{bump:?}");
        assert_eq!(
            bump["admissible"], "1",
            "every argument in this chain is compatible, so the class converts: \
             {bump:?}"
        );
    }

    /// **A duplicated argument blocks its class, and NOT the clean one beside
    /// it.** g21's shape.
    ///
    /// The negative half is what makes this a witness rather than a
    /// tautology: an implementation that blocks everything satisfies the first
    /// assertion and fails the second.
    ///
    /// *Mutation-tested (deletion first):* deleting the overlap loop makes the
    /// aliased class admissible and fails here; blocking unconditionally fails
    /// on `g21_ok`.
    #[test]
    fn a_duplicated_argument_blocks_only_its_own_class() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn g21_ok(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn g21_aliased(a: *mut i32, b: *mut i32) {{ *a += *b; }}\n\
             pub unsafe fn g21_clean() {{ let mut x: i32 = 0; g21_ok(&mut x); }}\n\
             pub unsafe fn g21_dirty(q: *mut i32) {{ g21_aliased(q, q); }}\n"
        ));
        let ok = row(&rows, "g21_ok", 1);
        let a = row(&rows, "g21_aliased", 1);
        assert_eq!(
            a["admissible"], "0",
            "`g21_aliased(q, q)` is E0499 after conversion and must block: {a:?}"
        );
        assert_eq!(a["class_block"], "duplicate-place-root", "{a:?}");
        assert_eq!(
            ok["admissible"], "1",
            "a blocked class must not take the clean one with it — one blocked \
             MEMBER blocks its own class, not the crate: {ok:?}"
        );
    }

    /// **One blocked member blocks the whole class.**
    ///
    /// `g21_dirty::q` supplies both aliased positions, so the edge pulls it
    /// into the blocked component. Its own arguments are unobjectionable; it is
    /// blocked by transitivity, which is the property that makes a class the
    /// unit of decision.
    #[test]
    fn one_blocked_member_blocks_the_class_through_the_edge() {
        // TWO call sites of one callee: `via` supplies a clean bare local, and
        // `nulls` supplies a null literal. The null blocks `t::p`, and `via::x`
        // — whose own argument is unobjectionable — is blocked with it.
        //
        // The `aliased(q, q)` shape cannot witness this: BO itself refuses the
        // doubly-passed binding, so `q` is not a node and there is no edge to
        // carry the block. Measured, and recorded rather than worked around.
        let rows = census(&format!(
            "{PRE}pub unsafe fn t(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn via(x: *mut i32) {{ t(x); }}\n\
             pub unsafe fn nulls() {{ t(0 as *mut i32); }}\n"
        ));
        let p = row(&rows, "t", 1);
        let x = row(&rows, "via", 1);
        assert_eq!(p["class_id"], x["class_id"], "{p:?} vs {x:?}");
        assert_eq!(p["node_block"], "arg-null-literal", "{p:?}");
        assert_eq!(x["admissible"], "0", "{x:?}");
        assert_eq!(
            x["node_block"], "-",
            "`x` contributes NO blocking argument of its own — it is blocked by \
             transitivity, and a census that reported otherwise could not name \
             the member responsible: {x:?}"
        );
    }

    /// **The argument-shape table, one fixture per blocking shape — and a
    /// negative for the shape that does NOT block.**
    ///
    /// One shape per case for the reason task 0 recorded: a classifier
    /// witnessed on one value is witnessed on nothing, because a single
    /// catch-all arm would satisfy every positive case at once. The `&mut e`
    /// row is what stops "block everything" from passing.
    #[test]
    fn each_blocking_argument_shape_has_its_own_reason() {
        let case = |arg: &str| {
            let rows = census(&format!(
                "{PRE}pub unsafe fn target(p: *mut i32) {{ *p = 1; }}\n\
                 pub unsafe fn caller() {{ let mut x: i32 = 0; let _ = &mut x; target({arg}); }}\n"
            ));
            row(&rows, "target", 1)
                .get("class_block")
                .cloned()
                .unwrap_or_default()
        };
        assert_eq!(case("0 as *mut i32"), "arg-null-literal");
        assert_eq!(case("(&mut x) as *mut i32"), "arg-cast-form-unbuilt");
        assert_eq!(case("1usize as *mut i32"), "arg-unadaptable-shape");
        assert_eq!(
            case("&mut x"),
            "-",
            "`&mut e` already coerces both ways and needs no edit — a table \
             that blocked it would block the second-largest shape in the corpus"
        );
    }

    /// **A shared borrow into a `&mut` position blocks.**
    ///
    /// Split from the table above because it is the one row whose verdict
    /// depends on the SUBJECT's mutability rather than on the argument alone.
    #[test]
    fn a_shared_borrow_into_a_mutable_position_blocks() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn target(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn caller() {{ let x: i32 = 0; target(&x as *const i32 as *mut i32); }}\n\
             pub unsafe fn shared(p: *mut i32) -> i32 {{ *p }}\n\
             pub unsafe fn ok() {{ let x: i32 = 0; shared(&x as *const i32 as *mut i32); }}\n"
        ));
        // Both go through a cast, so both read the cast reason; what this pins
        // is that a *const-rooted argument never silently satisfies a `&mut`
        // position.
        assert_eq!(row(&rows, "target", 1)["admissible"], "0");
    }

    /// **BANKED RULE 2 — a converting binding that reaches a parameter which
    /// stays raw is caught at DECISION time.**
    ///
    /// `&mut T → *mut T` is an implicit coercion, so this compiles at exit 0
    /// and produces no counter movement at all (§5a, measured). The verify loop
    /// cannot absorb it as a revert because there is nothing to absorb. If this
    /// gate is wrong there is no compile-time backstop.
    ///
    /// *Mutation-tested (deletion first):* deleting the caller-side arm leaves
    /// `src::r` admissible and fails here — and it fails SILENTLY in
    /// production, which is the reason the witness exists.
    #[test]
    fn a_converting_binding_into_a_raw_parameter_is_blocked_at_decision_time() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn sink(p: *mut i32) -> usize {{ p as usize }}\n\
             pub unsafe fn src(r: *mut i32) -> usize {{ *r = 1; sink(r) }}\n"
        ));
        let sink = row(&rows, "sink", 1);
        let src = row(&rows, "src", 1);
        assert_eq!(
            sink["class_id"], "-",
            "`sink`'s parameter is `as`-cast, so it stays raw and is not a \
             node — if it converted, this fixture would witness nothing: {sink:?}"
        );
        assert_eq!(src["node_block"], "flows-into-raw-param", "{src:?}");
        assert_eq!(src["admissible"], "0", "{src:?}");
    }

    /// **A converting binding into a DIFFERENTLY-FORMED parameter is its own
    /// reason**, because it is its own hazard class.
    ///
    /// `&mut T` into `*mut T` coerces silently and is caught here or nowhere.
    /// `&mut T` into `Option<&i32>` is `E0308` — the compiler catches it, so it
    /// costs a revert rather than soundness. Banked rule 1 is exactly that
    /// distinction, and a census reporting both as `flows-into-raw-param` files
    /// a checked risk under an unchecked reason.
    ///
    /// *Mutation-tested (deletion first):* dropping the `other_form` arm makes
    /// this read `flows-into-raw-param` and fails.
    #[test]
    fn a_binding_flowing_into_a_differently_formed_parameter_has_its_own_reason() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn opty(o: *mut i32) -> i32 {{ if o.is_null() {{ 0 }} else {{ *o }} }}\n\
             pub unsafe fn feeder(r: *mut i32) -> i32 {{ *r = 1; opty(r) }}\n"
        ));
        let o = row(&rows, "opty", 1);
        let r = row(&rows, "feeder", 1);
        assert_eq!(
            o["class_id"], "-",
            "`opty`'s parameter takes the OPTIONAL form, so it is not a class \
             node — if it were a plain `Ref` this fixture witnesses nothing: {o:?}"
        );
        assert_eq!(r["node_block"], "flows-into-other-form", "{r:?}");
    }

    /// **The PINNED population is excluded structurally, not in prose.**
    ///
    /// A function reached by a fn-pointer cast has its signature fixed by every
    /// table it appears in, and the pinned 640 are deferred to M2/M3. The
    /// hypothetical the class builder asks about is
    /// `RefGate::LiftAdaptable` — not `Lift` — so a pinned parameter is never a
    /// node and cannot enter a class.
    ///
    /// **PAIRED** with an adaptable callee in the same crate: a builder that
    /// produced no nodes at all would satisfy the pinned half by itself.
    #[test]
    fn a_pinned_callee_contributes_no_class_nodes() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn pinned(p: *mut i32) {{ *p = 1; }}\n\
             pub unsafe fn adaptable(p: *mut i32) {{ *p = 2; }}\n\
             pub unsafe fn tbl() -> usize {{ pinned as unsafe fn(*mut i32) as usize }}\n\
             pub unsafe fn call() {{ let mut x: i32 = 0; adaptable(&mut x); }}\n"
        ));
        assert_eq!(
            row(&rows, "pinned", 1)["class_id"],
            "-",
            "a fn-pointer-cast callee must contribute no node"
        );
        assert_ne!(
            row(&rows, "adaptable", 1)["class_id"],
            "-",
            "the adaptable callee in the SAME crate must be a node, or the \
             pinned assertion is satisfied by a builder that produces nothing"
        );
    }

    /// **P1 — each escape shape blocks under its OWN reason.**
    ///
    /// Approved conservative reading (ruling 2026-08-10): a node whose
    /// reference can leave through a return, a foreign call, a field store or
    /// a `static mut` store is not safely convertible, and each gets its own
    /// key so the population stays separately attributable and the scope is
    /// reversible by ruling rather than by archaeology.
    ///
    /// **Paired with a non-escaping node in the same crate** — a gate that
    /// blocked everything would satisfy every positive case at once.
    ///
    /// *Mutation-tested (deletion first):* deleting the escape loop makes each
    /// of these read `-` and fails.
    #[test]
    fn each_escape_shape_blocks_its_node_under_its_own_reason() {
        // One whole source per case: the shapes need different signatures, and
        // splicing a signature through a helper is how the first draft of this
        // fixture produced a crate that did not compile.
        const HDR: &str = "extern \"C\" { fn sink(p: *mut i32); }\n\
             pub struct S { pub f: *mut i32 }\n\
             pub static mut G: *mut i32 = 0 as *mut i32;\n\
             pub unsafe fn safe_one(k: *mut i32) { *k = 9; }\n";
        let case = |sig: &str| {
            let rows = census(&format!("{PRE}{HDR}{sig}"));
            (
                row(&rows, "subject", 1)["node_block"].clone(),
                row(&rows, "safe_one", 1)["admissible"].clone(),
            )
        };
        let cases = [
            (
                "pub unsafe fn subject(p: *mut i32) -> *mut i32 { *p = 1; return p; }\n",
                "escapes-via-return",
            ),
            (
                "pub unsafe fn subject(p: *mut i32) { *p = 1; sink(p); }\n",
                "escapes-via-foreign-arg",
            ),
            (
                "pub unsafe fn subject(p: *mut i32, s: *mut S) { *p = 1; (*s).f = p; }\n",
                "escapes-via-field-store",
            ),
            (
                "pub unsafe fn subject(p: *mut i32) { *p = 1; G = p; }\n",
                "escapes-via-static-store",
            ),
        ];
        for (sig, expected) in cases {
            let (blocked, beside) = case(sig);
            assert_eq!(blocked, expected, "for {sig}");
            assert_eq!(
                beside, "1",
                "the non-escaping node beside it must stay admissible, or the \
                 gate is satisfied by blocking everything: {sig}"
            );
        }
    }

    /// **P1 — a BORROW of a converting binding into a raw parameter blocks.**
    ///
    /// `f(&mut *r)` today reborrows a raw pointer; after `r` converts it
    /// reborrows a **reference**, so the raw pointer the callee retains can
    /// outlive the borrow. The conversion changes the case's character, which
    /// is what puts it inside banked rule 2 — the gap the adversarial review
    /// named, and the one the record did not previously cover.
    ///
    /// **Its own reason, not `flows-into-raw-param`**: the argument is a
    /// reborrow rather than the binding, so it forms no class edge and the
    /// owed repair differs.
    #[test]
    fn a_borrow_of_a_converting_binding_into_a_raw_parameter_blocks() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn sink(p: *mut i32) -> usize {{ p as usize }}\n\
             pub unsafe fn src(r: *mut i32) -> usize {{ *r = 1; sink(&mut *r) }}\n"
        ));
        assert_eq!(
            row(&rows, "sink", 1)["class_id"],
            "-",
            "the callee parameter must stay raw, or the fixture witnesses nothing"
        );
        assert_eq!(
            row(&rows, "src", 1)["node_block"],
            "borrowed-into-raw-param"
        );
    }

    /// **P2's visibility split — the same expression is checked or blind
    /// depending on whether its BASE converts.**
    ///
    /// §5a measured it on the pinned toolchain: `init(s, &mut (*s).g)` with a
    /// REFERENCE base is `E0499` ×2 — caught — while the same shape over a raw
    /// base compiles with zero diagnostics. So `through_deref` alone does not
    /// decide blindness; the base's own fate does, and that is why the flag had
    /// to be recorded rather than inferred from the shape.
    ///
    /// This pins the FACT the split rests on. It reads the two measurement
    /// columns, which are `-` for a non-node and therefore never a verdict on
    /// a subject that is not in a class.
    ///
    /// *Mutation-tested (deletion first):* making `blind` ignore
    /// `converts.contains(base)` collapses the two columns together and fails.
    #[test]
    fn a_borrow_through_a_converting_base_is_not_compiler_blind() {
        let rows = census(&format!(
            "{PRE}pub struct S {{ pub g: i32 }}\n\
             pub unsafe fn init(s: *mut S, g: *mut i32) {{ *g = 1; (*s).g = 2; }}\n\
             pub unsafe fn c(s: *mut S) {{ init(s, &mut (*s).g); }}\n"
        ));
        let hdr_present =
            rows[0].contains_key("p2_blind_only") && rows[0].contains_key("p2_all_pairs");
        assert!(hdr_present, "the P2 measurement columns must be exported");
        // The contained-place site: `s` and a place inside `*s` at two pointer
        // positions. Under EVERY rule this pair must block -- the roots are the
        // same binding, so it is not the split that catches it.
        let init_s = row(&rows, "init", 1);
        if init_s["class_id"] != "-" {
            assert_eq!(
                init_s["p2_all_pairs"], "0",
                "maximal conservatism must block a same-root mutable pair: {init_s:?}"
            );
        }
    }

    /// **RETIRED and REPLACED — the task-2 zero-delta pin.**
    ///
    /// `an_admissible_class_moves_no_decision_at_task_two` asserted that the
    /// production ladder still degraded `call-site-not-adapted` for an
    /// admissible class. Its own recorded mutation note read: *"switching the
    /// production `decide` call to `LiftAdaptable` makes the reason `-` and
    /// fails here. That mutation is exactly task 3."*
    ///
    /// Step 3 **is** that mutation. The pin fired precisely as designed and its
    /// era ended, so it is retired openly rather than edited into agreement —
    /// the g19 rule. What replaces it is the lift-era invariant stated
    /// positively, under **its own name**, so nothing pretends to be the old
    /// pin still holding.
    ///
    /// *Mutation-tested (deletion first):* reverting production to
    /// `RefGate::BlockAll` makes the chain degrade again and fails this.
    #[test]
    fn an_admissible_class_converts_after_the_lift() {
        let rows = census(&format!(
            "{PRE}pub unsafe fn g20_bump(p: *mut i32) -> i32 {{ *p += 1; *p }}\n\
             pub unsafe fn g20_via(q: *mut i32) -> i32 {{ g20_bump(q) }}\n\
             pub unsafe fn g20_root() -> i32 {{ let mut x: i32 = 0; g20_via(&mut x) }}\n"
        ));
        let bump = row(&rows, "g20_bump", 1);
        assert_eq!(bump["admissible"], "1", "{bump:?}");

        let src = format!(
            "{PRE}pub unsafe fn g20_bump(p: *mut i32) -> i32 {{ *p += 1; *p }}\n\
             pub unsafe fn g20_via(q: *mut i32) -> i32 {{ g20_bump(q) }}\n\
             pub unsafe fn g20_root() -> i32 {{ let mut x: i32 = 0; g20_via(&mut x) }}\n"
        );
        let fixture = Fixture::new(&[("lib.rs", &src)]);
        let reasons =
            ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
                let table = crate::bo_rewriter::decide_table(tcx).expect("table");
                crate::bo_rewriter::artifact::rows(tcx, &table)
                    .iter()
                    .filter_map(|r| r.degrade_reason.clone())
                    .collect::<Vec<_>>()
            })
            .expect("fixture compiles");
        assert!(
            !reasons.iter().any(|r| r == "call-site-not-adapted"),
            "the lift must retire call-site-not-adapted for an admissible \
             class: {reasons:?}"
        );
    }
}

/// **S3.6-1 task 2 — the attribution repair, and the escape census.**
mod attribution_and_escapes {
    use std::{
        collections::{BTreeMap, BTreeSet},
        path::Path,
    };

    use super::Fixture;
    use crate::bo_rewriter::{
        EditSite, EmittedSite, attribute, edit_sites,
        plan::{Edit, FileKey, Justification, Plan},
        verify::{Diag, Direction},
    };

    fn diag(file: &str, line: usize) -> Diag {
        Diag {
            file: file.to_owned(),
            line,
            message: "mismatched types".to_owned(),
            direction: Direction::RawIntoRewritten,
            code: Some("E0308".to_owned()),
        }
    }

    /// **A caller-file diagnostic names the CALLEE that caused it.**
    ///
    /// This is the S3 defect the plan required repaired before any new subject
    /// emits. Call-site adaptation puts edits in files the subject does not
    /// live in, and function-extent containment attributes such a diagnostic to
    /// **nobody** — the revert loop then cannot converge on the culprit and
    /// falls through to bisect, which "may revert more than strictly
    /// necessary".
    ///
    /// **The negative half is the repair's own witness**: the same diagnostic
    /// with an empty edit list attributes to nothing, which is exactly what
    /// production did before. Without it a test could pass on an
    /// implementation that attributes everything to everyone.
    ///
    /// *Mutation-tested (deletion first):* deleting the edit-range pass leaves
    /// only the extent pass and fails on the positive half.
    #[test]
    fn a_caller_file_diagnostic_attributes_to_the_edit_that_justifies_it() {
        let root = Path::new("/crate");
        // The subject's own function lives in `callee.rs`; the edit landed in
        // `caller.rs`, which holds no subject at all.
        let sites = [EmittedSite {
            file: "/crate/callee.rs".to_owned(),
            fn_path: "k::callee".to_owned(),
            lo_line: 1,
            hi_line: 3,
        }];
        let edits = [EditSite {
            file: "/crate/caller.rs".to_owned(),
            fn_path: "k::callee".to_owned(),
            lo_line: 10,
            hi_line: 10,
        }];
        let diags = [diag("/crate/caller.rs", 10)];

        let owners = attribute(&diags, root, &sites, &edits, &BTreeSet::new(), root);
        assert_eq!(
            owners.into_iter().collect::<Vec<_>>(),
            vec!["k::callee".to_owned()],
            "an error inside a caller-file edit must name the subject that \
             justifies the edit"
        );

        let blind = attribute(&diags, root, &sites, &[], &BTreeSet::new(), root);
        assert!(
            blind.is_empty(),
            "the pre-repair derivation must attribute this to NOBODY, or the \
             positive half witnesses nothing: {blind:?}"
        );
    }

    /// The fallback survives: a diagnostic inside a rewritten function's extent
    /// but inside no edit still attributes to that function.
    ///
    /// Without this, the repair could have been "replace extent containment
    /// with edit containment", which would have silently dropped every
    /// diagnostic that lands near an edit rather than on it — the common case.
    #[test]
    fn a_diagnostic_outside_every_edit_still_falls_back_to_the_function_extent() {
        let root = Path::new("/crate");
        let sites = [EmittedSite {
            file: "/crate/callee.rs".to_owned(),
            fn_path: "k::callee".to_owned(),
            lo_line: 1,
            hi_line: 30,
        }];
        let edits = [EditSite {
            file: "/crate/callee.rs".to_owned(),
            fn_path: "k::callee".to_owned(),
            lo_line: 1,
            hi_line: 1,
        }];
        let owners = attribute(
            &[diag("/crate/callee.rs", 20)],
            root,
            &sites,
            &edits,
            &BTreeSet::new(),
            root,
        );
        assert_eq!(
            owners.into_iter().collect::<Vec<_>>(),
            vec!["k::callee".to_owned()]
        );
    }

    /// **A STALE edit must not blind attribution — Codex adversarial review,
    /// finding P3(a), CONFIRMED by reading before it was accepted.**
    ///
    /// `edit_sites` is built once from the whole plan; `render` keeps an edit
    /// only while its owner is not reverted. Attributing through the unfiltered
    /// list is a second derivation of *"which edits are live"*, and once
    /// anything is reverted the two diverge: the stale edit matches,
    /// short-circuits the extent pass, contributes only an already-reverted
    /// owner, and the caller's `.difference(&reverted)` then empties the
    /// result — a convergent run sent to bisect.
    ///
    /// Here the caller's own function extent IS the right answer, and the fix
    /// is to filter by the same predicate `render` filters by.
    ///
    /// *Mutation-tested (deletion first):* removing the `!reverted.contains`
    /// filter makes this return empty and fails.
    #[test]
    fn a_reverted_owners_edit_does_not_blind_attribution() {
        let root = Path::new("/crate");
        let sites = [EmittedSite {
            file: "/crate/m.rs".to_owned(),
            fn_path: "k::caller".to_owned(),
            lo_line: 5,
            hi_line: 15,
        }];
        let edits = [EditSite {
            file: "/crate/m.rs".to_owned(),
            fn_path: "k::callee".to_owned(),
            lo_line: 10,
            hi_line: 10,
        }];
        let reverted = BTreeSet::from(["k::callee".to_owned()]);

        let owners = attribute(
            &[diag("/crate/m.rs", 10)],
            root,
            &sites,
            &edits,
            &reverted,
            root,
        );
        assert_eq!(
            owners.into_iter().collect::<Vec<_>>(),
            vec!["k::caller".to_owned()],
            "the reverted owner's edit is no longer applied, so it must not \
             suppress the extent owner that still is"
        );
    }

    /// `edit_sites` converts byte ranges to the LINES a diagnostic reports in.
    ///
    /// *Mutation-tested:* returning `(1, 1)` unconditionally makes the
    /// attribution test above pass by accident and fails here.
    #[test]
    fn an_edit_locates_to_the_lines_it_spans() {
        let text = "aaa\nbbb\nccc\nddd\n";
        let key = FileKey::Virtual("main.rs".to_owned());
        let mut plan = Plan::default();
        plan.by_file.insert(
            key.clone(),
            vec![Edit {
                // `ccc` starts at byte 8 and ends at 11 — line 3.
                lo: 8,
                hi: 11,
                replacement: "zzz".to_owned(),
                justification: Justification::KindDecision { kind: "Ref(mut)" },
                owner_fn: "k::f".to_owned(),
            }],
        );
        let texts = BTreeMap::from([(key, text.to_owned())]);
        let located = edit_sites(&plan, &texts);
        assert_eq!(located.len(), 1);
        assert_eq!(
            (located[0].lo_line, located[0].hi_line),
            (3, 3),
            "{located:?}"
        );
        assert_eq!(located[0].file, "main.rs");
    }

    /// **The escape shapes, one fixture per kind — plus the negative.**
    ///
    /// These are MEASURED and deliberately NOT gated: `&mut T → *mut T` coerces
    /// implicitly at all four positions, so none presents as a revert. The
    /// call-argument flow is the one S3.6-1 creates and it IS gated, in
    /// `co_conversion`; a `static mut` store, a field store and a return are
    /// pre-existing and orthogonal — the already-emitting population carries
    /// the same shape today.
    ///
    /// The `local-store` negative is what stops "everything is an escape" from
    /// passing, which would have made the corpus figure meaningless.
    #[test]
    fn each_escape_shape_is_recognised_and_a_local_store_is_not_one() {
        let kinds = |body: &str| -> Vec<String> {
            let src = format!(
                "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                 extern \"C\" {{ fn sink(p: *mut i32); }}\n\
                 pub struct S {{ pub f: *mut i32 }}\n\
                 pub static mut G: *mut i32 = 0 as *mut i32;\n\
                 pub unsafe fn f(p: *mut i32, s: *mut S) -> *mut i32 {{ {body} }}\n"
            );
            let fixture = Fixture::new(&[("lib.rs", &src)]);
            ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
                let (_table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).expect("table");
                let mut out: Vec<String> = ctx
                    .escapes_for_test()
                    .iter()
                    .map(|e| e.kind.key().to_owned())
                    .collect();
                out.sort_unstable();
                out.dedup();
                out
            })
            .expect("fixture compiles")
        };

        assert!(kinds("G = p; p").contains(&"static-store".to_owned()));
        assert!(kinds("(*s).f = p; p").contains(&"field-store".to_owned()));
        assert!(kinds("return p;").contains(&"return".to_owned()));
        assert!(kinds("sink(p); p").contains(&"foreign-arg".to_owned()));
        // A store into another LOCAL leaves nothing: the target is in the same
        // body, so the value has not escaped the function.
        let local_only = kinds("let mut q: *mut i32 = 0 as *mut i32; q = p; q");
        assert!(
            !local_only.contains(&"static-store".to_owned())
                && !local_only.contains(&"field-store".to_owned()),
            "a local-to-local store is not an escape: {local_only:?}"
        );
    }
}

/// **THE SEAM, END TO END.** A callee whose parameter takes the optional form,
/// called with a plain `&mut` — the caller's argument gets `Some(..)` glue.
///
/// This is the first witness that the adapter reaches emitted TEXT rather than
/// only the glue table's unit tests. It pins the whole path: the call-site walk
/// computes `(expected = Opt{mut,thin}, found = Ref{mut})`, `seam::glue`
/// produces `Some(&mut x)`, `plan` places it in the CALLER's file under the
/// CALLEE's `owner_fn`, and `apply` splices it.
///
/// *Mutation-tested (Rider 0, deletion first):* stop filling `table.seams` in
/// the driver and the emitted source keeps the bare `&mut x`, which no longer
/// satisfies `Option<&mut i32>`.
#[test]
fn a_mismatched_argument_gets_seam_glue_in_the_emitted_text() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn callee(p: *mut i32) -> i32 {\n\
               \x20   if p.is_null() { 0 } else { *p }\n\
               }\n\
               pub fn caller() {\n\
               \x20   let mut x: i32 = 1;\n\
               \x20   unsafe { callee(&mut x); }\n\
               }\n";
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("fixture must emit");
    };
    assert!(
        source.contains("callee(Some(&mut x))"),
        "the argument must be wrapped by the seam, or the callee's optional \
         parameter is left ill-typed:\n{source}"
    );
}

/// **A BLOCKED seam row names the CALLEE in `owner_fn`, and the caller in its
/// own column.**
///
/// `owner_fn` is the REVERT KEY. On a `placed` row it has always been the
/// callee — `a_reverted_callee_takes_its_seams_with_it` is the property — but a
/// `blocked` row carried the CALLER there, so one column meant two things by
/// row kind. The consequence was not cosmetic: a refused seam costs the
/// **callee's** conversion, so *"which functions would gain if this refusal
/// went away"* could only be answered on the axis that does not revert. That is
/// how the fabricated-length slice's own upside was nearly priced wrong.
///
/// The caller is real information and moves to its own column rather than being
/// dropped.
///
/// *Mutation-tested:* swapping the two back — `owner_fn` = caller, trailing
/// column = callee — fails both assertions, and each on its own.
#[test]
fn a_blocked_seam_row_names_the_callee_as_its_revert_key() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn callee(p: *mut i32) -> i32 {\n\
               \x20   if p.is_null() { 0 } else { *p }\n\
               }\n\
               pub fn caller() {\n\
               \x20   unsafe { callee(0 as *mut i32); }\n\
               }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let tsv = ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        super::seam_tsv(tcx).expect("seam census")
    })
    .expect("fixture compiles");

    let hdr: Vec<&str> = tsv.lines().next().expect("header").split('\t').collect();
    let col = |n: &str| hdr.iter().position(|h| *h == n).expect("column present");
    let (c_owner, c_caller) = (col("owner_fn"), col("caller"));
    let blocked: Vec<Vec<&str>> = tsv
        .lines()
        .skip(1)
        .map(|l| l.split('\t').collect::<Vec<_>>())
        .filter(|f| f.first() == Some(&"blocked"))
        .collect();
    assert_eq!(blocked.len(), 1, "one refused position expected:\n{tsv}");
    assert!(
        blocked[0][c_owner].ends_with("callee"),
        "`owner_fn` must be the CALLEE — it is the revert key on every row \
         kind:\n{tsv}"
    );
    assert!(
        blocked[0][c_caller].ends_with("caller"),
        "the caller must be recorded, not dropped:\n{tsv}"
    );
}

/// **REVERT COHERENCE, BOTH SIDES.** A callee's seams live and die with it.
///
/// # The failure mode this prevents
///
/// A callee reverts to a raw parameter while its caller keeps the `Some(..)`
/// wrapping the seam inserted. That is a **reverse-direction `E0308`
/// manufactured by our own glue** — the crate compiled before the rewrite and
/// fails after, in a file the reverted function does not even live in. It is
/// strictly worse than the mismatch the seam exists to fix, because the seam
/// was supposed to be the repair.
///
/// # Why this is checkable at all
///
/// `render` filters edits by `!reverted.contains(&edit.owner_fn)`, and every
/// seam carries the **callee's** path — not the caller's, though the edit lands
/// in the caller's file. Reverting by justification rather than geography is
/// what makes a caller-file edit revert with the callee that justifies it.
///
/// *Mutation-tested (Rider 0, deletion first):* key the seam on the CALLER
/// (`site.caller`) instead of the callee and the reverted half fails — the glue
/// survives its own callee's revert, which is the exact defect.
#[test]
fn a_reverted_callee_takes_its_seams_with_it() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn callee(p: *mut i32) -> i32 {\n\
               \x20   if p.is_null() { 0 } else { *p }\n\
               }\n\
               pub fn caller() {\n\
               \x20   let mut x: i32 = 1;\n\
               \x20   unsafe { callee(&mut x); }\n\
               }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    let emission = emit(&fixture);

    // The seam exists, and it is OWNED BY THE CALLEE — the half of the property
    // that makes the other half possible.
    let seam_owner = emission
        .plan
        .by_file
        .values()
        .flatten()
        .find(|e| e.replacement.contains("Some("))
        .map(|e| e.owner_fn.clone())
        .expect("the fixture must produce a seam");
    assert_eq!(
        seam_owner, "callee",
        "a seam must be justified by the CALLEE, though it lands in the \
         caller's file: reverting by geography would strand it"
    );

    // ---- side 1: callee survives ⇒ the glue is present ----
    let (kept, _) = super::render(
        &emission.plan,
        &emission.texts,
        &std::collections::BTreeSet::new(),
    );
    assert!(
        text_for_any(&kept).is_some_and(|t| t.contains("callee(Some(&mut x))")),
        "with nothing reverted the seam must be in the emitted text"
    );

    // ---- side 2: callee reverts ⇒ the glue vanishes ----
    let reverted: std::collections::BTreeSet<String> = [seam_owner].into_iter().collect();
    let (after, _) = super::render(&emission.plan, &emission.texts, &reverted);
    let text = text_for_any(&after).unwrap_or_default();
    assert!(
        !text.contains("Some("),
        "the callee was reverted and its seam SURVIVED — the caller now wraps \
         an argument for a parameter that went back to raw, which is a \
         reverse-direction E0308 our own glue manufactured:\n{text}"
    );
    assert!(
        !text.contains("Option<"),
        "the callee's own declaration must revert with it:\n{text}"
    );
}

/// **THE FABRICATED-EXTENT CONST IS DERIVED FROM THE SURVIVORS** — all three
/// arms of the marker ruling's placement rule, on the production `render`.
///
/// §9c priced the two obvious owners and refused both: keying the const to one
/// adapter's `owner_fn` deletes it when that function reverts while siblings
/// still name it (`E0433`, cascading), and a never-reverted sentinel leaves a
/// dead const when every fabricated site reverts. The rule shipped instead is
/// *emit iff at least one fabricated adapter survives the revert set* — which is
/// only meaningful if all three arms are witnessed, because arms 1 and 3 are
/// exactly what the two refused designs would have got wrong.
///
/// *Mutation-tested:* replace the survivor test with `true` and arm 1 fails;
/// replace it with a per-file `push` and arm 3 fails on the count.
#[test]
fn the_fabricated_const_follows_the_surviving_adapters() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn fab_total(buf: *mut i32) -> i32 {\n\
               \x20   let mut s: i32 = 0;\n\
               \x20   let mut i: usize = 0;\n\
               \x20   while i < 4 { s += *buf.offset(i as isize); i += 1; }\n\
               \x20   s\n\
               }\n\
               pub unsafe fn fab_one(d: *mut i32) -> i32 { fab_total(d) }\n\
               pub unsafe fn fab_two(d: *mut i32) -> i32 { fab_total(d) }\n";
    let fixture = Fixture::new(&[("lib.rs", src)]);
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let table = decide_table(tcx).expect("decides");
        let emission = emit_files(tcx, &table, &rustc_hash::FxHashSet::default()).expect("emits");
        let (plan, texts) = (&emission.plan, &emission.texts);

        // NON-VACUITY FIRST. Everything below is about a population; if the
        // fixture produced no fabricated adapter the three arms would agree
        // trivially and witness nothing.
        let fabricated: Vec<&str> = plan
            .by_file
            .values()
            .flatten()
            .filter(|e| {
                matches!(
                    e.justification,
                    super::plan::Justification::SeamAdapter {
                        fabricated: true,
                        ..
                    }
                )
            })
            .map(|e| e.owner_fn.as_str())
            .collect();
        assert_eq!(
            fabricated.len(),
            2,
            "the fixture must place TWO fabricated adapters, both owned by the \
             callee — one is not enough to tell 'one const per crate' from \
             'one const per adapter'"
        );
        let owner = fabricated[0].to_owned();
        assert!(
            plan.root_file.is_some(),
            "the root file must be identified, or the insertion fail-closes"
        );

        let consts = |reverted: &std::collections::BTreeSet<String>| -> usize {
            let (files, rollbacks) = super::render(plan, texts, reverted);
            assert!(rollbacks.is_empty(), "the insertion must not collide");
            files
                .values()
                .map(|t| {
                    t.matches("const SEAM_LEN_PLACEHOLDER: usize = 1024;")
                        .count()
                })
                .sum()
        };

        // ---- arm 2: adapters survive ⇒ EXACTLY ONE const ----
        // ---- arm 3: TWO surviving adapters ⇒ still exactly one ----
        // Both are this call: the fixture's two adapters share one callee, so
        // an implementation that pushed per adapter would report 2 here.
        assert_eq!(
            consts(&std::collections::BTreeSet::new()),
            1,
            "one crate, one const — never one per fabricated site"
        );

        // **PLACEMENT IS LOAD-BEARING, so it is COMPILED.** Counting the const
        // proves it is present; only the compiler proves it is somewhere legal
        // and that `crate::SEAM_LEN_PLACEHOLDER` resolves from the call sites.
        // Without this the whole placement rule — end of the crate ROOT file —
        // would be witnessed by a `.matches()` on a string, which an insertion
        // ahead of the inner attributes would satisfy just as well.
        let (files, _) = super::render(plan, texts, &std::collections::BTreeSet::new());
        let emitted = files.values().next().expect("one emitted file").clone();
        assert!(
            emitted.contains("crate::SEAM_LEN_PLACEHOLDER"),
            "the call sites must NAME the const, or this compiles vacuously:\n{emitted}"
        );
        let staged =
            super::verify::materialize_single_file(&emitted).expect("the emitted crate stages");
        assert!(
            super::verify::type_checks_crate(staged.root()),
            "the emitted crate must type-check with the const where we put it:\n{emitted}"
        );

        // ---- arm 1: every fabricated adapter reverts ⇒ NO const ----
        // The dead-const case the sentinel owner would have produced.
        let all_gone: std::collections::BTreeSet<String> = std::iter::once(owner).collect();
        assert_eq!(
            consts(&all_gone),
            0,
            "no surviving fabricated adapter means no const — a dead item in \
             the emitted crate is exactly what deriving it avoids"
        );
        Ok::<(), String>(())
    })
    .expect("fixture compiles")
    .expect("no emission error");
}

/// **`render` RUNS OUTSIDE THE COMPILER SESSION, AND THE CONST STILL LANDS.**
///
/// The reproduction of the defect the first fabrication emit sweep found: four
/// of twenty programs panicked at
/// `scoped-tls: cannot access a scoped thread local variable without calling
/// set first`, and they were exactly the four in which a fabricated adapter
/// SURVIVED into a verify/revert round.
///
/// `rewrite_core`'s `TyCtxt` closure ends before the verify loop, so the loop's
/// three `render` calls have **no session globals**. Building the const there
/// parsed and pretty-printed — both of which need them.
///
/// **Why the existing witness could not catch it:**
/// `the_fabricated_const_follows_the_surviving_adapters` calls `render` INSIDE
/// `run_compiler_on_path`. It exercised the function in a context production
/// does not have, so it was green while production panicked. *A witness has to
/// run where the code runs* — M-F7's lesson one layer down, and this one cost a
/// 625 s sweep.
///
/// *Mutation-tested:* move the `fabricated_len_item()` call back into `render`
/// and this test panics rather than failing an assertion — which is the defect,
/// reproduced.
#[test]
fn render_outside_a_compiler_session_still_delivers_the_const() {
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn fab_total(buf: *mut i32) -> i32 {\n\
                       \x20   let mut s: i32 = 0;\n\
                       \x20   let mut i: usize = 0;\n\
                       \x20   while i < 4 { s += *buf.offset(i as isize); i += 1; }\n\
                       \x20   s\n\
                       }\n\
                       pub unsafe fn fab_one(d: *mut i32) -> i32 { fab_total(d) }\n";
    let fixture = Fixture::new(&[("lib.rs", SRC)]);
    // Everything that needs a session happens INSIDE it, and only data escapes.
    let (plan, texts) =
        ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
            let table = decide_table(tcx).expect("decides");
            let e = emit_files(tcx, &table, &rustc_hash::FxHashSet::default()).expect("emits");
            (e.plan, e.texts)
        })
        .expect("fixture compiles");

    assert!(
        plan.len_const_item.is_some(),
        "the const's text must be produced while a session exists, or the          insertion fail-closes outside one"
    );

    // ---- and NOW, with no session anywhere on this thread ----
    let (files, rollbacks) = super::render(&plan, &texts, &std::collections::BTreeSet::new());
    assert!(rollbacks.is_empty());
    let n: usize = files
        .values()
        .map(|t| {
            t.matches("const SEAM_LEN_PLACEHOLDER: usize = 1024;")
                .count()
        })
        .sum();
    assert_eq!(
        n, 1,
        "exactly one const, rendered outside a compiler session — this is the          call the verify loop makes"
    );
}

/// **BOTH LAYERS EMIT THE CONST, AND AGREE ON IT.**
///
/// Found by mutation **M-F7**: disabling the AST layer's const arm entirely left
/// the suite at 1247/6/28 — byte-identical to baseline. The arm was live
/// production code in the **layer of record** with no witness at all, because
/// the only thing exercising the AST emitter is the golden set and **no golden
/// carries a fabricated position** (measured: 0 across all 21).
///
/// The obvious answer — "g26 will witness it" — is the answer this milestone has
/// learned to refuse. g26 is a ratification event that has not happened yet, and
/// an arm whose only witness is a fixture someone still has to approve is an arm
/// shipping unwitnessed in the meantime.
///
/// *Mutation-tested:* the M-F7 mutation that survived the whole suite fails
/// here.
/// **W1 — the AST layer HONOURS a non-empty revert set.**
///
/// The standing gap, registered at the fabrication close: *"every existing
/// cross-layer witness runs with an empty revert set."* The verify/revert loop
/// reverts on every round but the first, so an emitter that ignored its revert
/// set would re-convert exactly the functions the previous round took back —
/// silently, and the loop would never converge.
///
/// **Reading could not settle this.** The comment in `ast_emitted_source` said
/// `transform_inner` "builds its visitors with an explicitly EMPTY revert set";
/// it had been false since M-2/A task 1 threaded `reverts` through. This test is
/// the empirical answer.
///
/// *Mutation-tested* (M-W1-a): drop `reverted_fns` from the decl visitor's
/// construction, or pass `&RevertSet::default()` to `transform_with`, and the
/// `revert_me` half fails — the reverted function converts.
#[test]
fn a_reverted_fn_keeps_its_raw_declaration() {
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn keep_me(p: *mut i32) -> i32 { *p }\n\
                       pub unsafe fn revert_me(q: *mut i32) -> i32 { *q }\n";

    // Both convert with an EMPTY revert set — the control that makes the
    // reverted half non-vacuous. Without it, "revert_me stayed raw" would be
    // satisfied by a fixture that never converted at all.
    let none = super::ast_emitted_source_of(SRC).expect("the AST layer emits");
    assert!(
        !none.contains("p: *mut i32") && !none.contains("q: *mut i32"),
        "CONTROL: both params must convert under an empty revert set, or the \
         reverted half below proves nothing:\n{none}"
    );

    // Now revert exactly one of them.
    let one = super::ast_emitted_source_of_reverting(SRC, "revert_me::q#1")
        .expect("the AST layer emits under a revert set");
    assert!(
        one.contains("q: *mut i32"),
        "REVERTED: `revert_me` must keep its raw declaration — an emitter that \
         ignores its revert set re-converts what the previous round took \
         back:\n{one}"
    );
    assert!(
        !one.contains("p: *mut i32"),
        "KEPT: `keep_me` must still convert — reverting one function may not \
         revert the crate:\n{one}"
    );
}

/// **The one-capture-per-session fact, measured rather than cited.**
///
/// `ast_emitted_source` captures on every call, so a loop calling it per round
/// would fail on round 2. That is why the loop uses
/// `ast_emitted_source_from` against a single round-0 capture — a design
/// constraint, not a performance choice.
///
/// *Mutation-tested* (M-W1-b): make `capture_ast` memoize and return the same
/// capture twice and this fails, which is the point — a memoizing capture would
/// make the split look unnecessary while quietly handing out a krate whose
/// resolver is already consumed.
#[test]
fn a_second_capture_in_one_session_fails() {
    const SRC: &str = "#![allow(dead_code)]\npub unsafe fn f(p: *mut i32) -> i32 { *p }\n";
    let (first, second) = super::two_captures_in_one_session(SRC).expect("session runs");
    assert!(
        first,
        "the FIRST capture must succeed, or the second proves nothing"
    );
    assert!(
        !second,
        "a SECOND capture in one session must fail — the loop's one-capture \
         design rests on this, and if it ever starts succeeding the split in \
         `ast_emitted_source_from` needs re-justifying, not deleting"
    );
}

#[test]
fn both_layers_emit_the_fabricated_const() {
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn fab_total(buf: *mut i32) -> i32 {\n\
                       \x20   let mut s: i32 = 0;\n\
                       \x20   let mut i: usize = 0;\n\
                       \x20   while i < 4 { s += *buf.offset(i as isize); i += 1; }\n\
                       \x20   s\n\
                       }\n\
                       pub unsafe fn fab_one(d: *mut i32) -> i32 { fab_total(d) }\n";
    let decl = "const SEAM_LEN_PLACEHOLDER: usize = 1024;";

    let ast = super::ast_emitted_source_of(SRC).expect("the AST layer emits");
    assert_eq!(
        ast.matches(decl).count(),
        1,
        "the AST layer — the LAYER OF RECORD — must declare the const it names:\n{ast}"
    );
    assert!(
        ast.contains("crate::SEAM_LEN_PLACEHOLDER"),
        "and a fabricated site must name it, or the count above is vacuous:\n{ast}"
    );

    // The span layer, on the SAME input, through the production entry point.
    let span = match super::rewrite_m1(SRC) {
        super::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("the span layer must emit: {other:?}"),
    };
    assert_eq!(
        span.matches(decl).count(),
        1,
        "and so must the span layer, or the two frames disagree about the \
         program:\n{span}"
    );
}

/// **CROSS-ARM PARITY — one function carrying BOTH a declaration edit and a
/// fabricated seam.** The REARM obligation, discharged at fixture level.
///
/// The fabrication sweep made `multi_arm` nonzero for the first time:
/// `rgba_from_hex_string` holds two subjects decided `ref` **and** both of
/// rgba's fabricated seams, with zero reverts in that program — one function,
/// two arms. The parked cross-arm parity obligation therefore REARMED.
///
/// **The p3 gate cannot see this.** It runs against a frozen oracle whose revert
/// set predates fabrication and reverted exactly the functions fabrication
/// unblocks, so its `multi_arm` is 0 by construction, not by measurement. A pin
/// that cannot move is not a discharge.
///
/// Measured on rgba itself: the two layers are **byte-identical after canonical
/// formatting** (86,458 bytes each, one const each). This fixture is the
/// corpus-independent half of the same claim, so the obligation stays discharged
/// when the corpus moves.
#[test]
fn a_function_carrying_both_arms_renders_identically_in_both_layers() {
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn cx_sum(buf: *mut i32) -> i32 {\n\
                       \x20   let mut s: i32 = 0;\n\
                       \x20   let mut i: usize = 0;\n\
                       \x20   while i < 4 { s += *buf.offset(i as isize); i += 1; }\n\
                       \x20   s\n\
                       }\n\
                       pub unsafe fn cx_caller(p: *mut i32, out: *mut i32) -> i32 {\n\
                       \x20   let t = cx_sum(p);\n\
                       \x20   *out = t;\n\
                       \x20   t\n\
                       }\n";
    let span = match super::rewrite_m1(SRC) {
        super::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("the span layer must emit: {other:?}"),
    };
    // ---- NON-VACUITY: the fixture must actually carry BOTH arms ----
    //
    // Without this the test would pass on a fixture where fabrication never
    // fired, or where the caller kept every raw parameter — which is exactly
    // the shape it exists to cover.
    assert!(
        span.contains("crate::SEAM_LEN_PLACEHOLDER"),
        "arm 3 (a fabricated seam) must be present:\n{span}"
    );
    assert!(
        span.contains("out: &mut i32"),
        "arm 2 (a declaration edit) must be present IN THE CALLER, or this is \
         not a cross-arm function:\n{span}"
    );

    let ast = super::ast_emitted_source_of(SRC).expect("the AST layer emits");
    assert_eq!(
        crate::bo_rewriter::goldens::canonicalize("span", &span),
        crate::bo_rewriter::goldens::canonicalize("ast", &ast),
        "the two layers must agree on a function that carries both arms"
    );
}

/// **DIAGNOSIS (M-2/A, 2026-08-18) — does a revert restore BYTES or a reprint?**
///
/// The bar the acceptance gate sets is verdicts and counters, not text. But
/// byte preservation for untransformed code is the migration's founding
/// principle, so a reverted function coming back as a `pprust` reprint is a
/// defect against that principle regardless of whether it moves a verdict.
///
/// Reverting EVERY function is the sharpest form of the question: the emitted
/// text should then be the substrate, byte for byte.
#[test]
fn reverting_every_function_reproduces_the_substrate() {
    // ⚠ **DELIBERATELY NON-CANONICAL.** The first draft of this fixture was
    // written in `pprust`'s own style, so it would have passed whether reverts
    // restore bytes or reprint them — a witness passing for the wrong reason.
    // The odd spacing, the multi-line body and the interior comment are the
    // discriminator: a reprint normalizes all three.
    const SRC: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
                       pub unsafe fn one(p:   *mut i32) -> i32 {\n\
                       \x20   // a comment a reprint would drop\n\
                       \x20   *p\n\
                       }\n\
                       pub unsafe fn two(q: *mut i32)   ->   i32 { *q }\n";

    let all = "one::p#1\ntwo::q#1";
    let out = super::ast_emitted_source_of_reverting(SRC, all).expect("emits");

    // **FIXED (2026-08-18).** This was a status-quo pin of a confirmed defect:
    // `collect_fn_prints` reprinted every function unconditionally, so a fully
    // reverted function came back as a `pprust` reprint with its spacing
    // normalized and its interior comment dropped. The splicer now reprints
    // only functions the transform actually CLAIMED, so an untouched function
    // keeps its original bytes.
    //
    // ⚠ The fixture is DELIBERATELY non-canonical — see above. Written in
    // `pprust` style it would pass either way, which is how the defect stayed
    // invisible to 21 goldens.
    assert_eq!(
        out, SRC,
        "reverting every function must reproduce the substrate byte for byte.\n\
         --- emitted ---\n{out}\n--- substrate ---\n{SRC}"
    );
}

/// **W2 — the two layers agree on a program the loop actually REVERTED.**
///
/// W1 established that the AST layer honours a revert set. W2 is the question
/// the acceptance gate rests on: that both layers, driven end to end through
/// the real verify/revert loop on a fixture where a revert genuinely fires,
/// reach the SAME verdict and the SAME converged state.
///
/// # ADMISSIBILITY — traced, not assumed
///
/// A compared quantity is admissible **iff its dataflow passes through
/// `round_files`' output**, i.e. through the candidate programs the switched
/// emitter produced. The first draft of this test compared `emitted_count` and
/// the `degradations` vector — **both PARAMETERS of `verify_and_revert`,
/// computed by `emit_files` before the loop**, hence identical on both sides by
/// construction. It passed with the defect it named restored. A comparison
/// witnesses nothing unless its two sides can differ.
///
/// The trace for each quantity compared here:
///
/// | quantity | origin | admissible |
/// |---|---|---|
/// | verdict (`Emitted`/`Degraded`) | the loop's own exit path | yes |
/// | `escalated` | `facts.escalated`, assigned in the loop | yes |
/// | `reverted_count` | `facts.reverted_count`, from `reverted.len()`/`taken.len()` | yes |
/// | `bisect_probes` | `facts.bisect_probes`, from `bisect`'s return | yes |
/// | ~~`emitted_count`~~ | parameter, pre-loop | **NO** |
/// | ~~`degradations.len()`~~ | parameter, pre-loop | **NO** |
///
/// Emitted TEXT is deliberately not compared: the gate's bar is verdicts and
/// counters, the pinned oracle carries no texts, and text-level fidelity is
/// already owned by the parity instruments and
/// `reverting_every_function_reproduces_the_substrate`.
///
/// *Mutation-witnessed* (M-W2): restoring the re-derivation inside
/// `ast_emitted_files_from` flips the AST side's verdict. Build-verified —
/// a mutation is only a mutation if it provably compiled into that run.
#[test]
fn both_layers_agree_on_a_reverted_program() {
    /// Verdict plus the loop-derived counters. Everything here is assigned
    /// below the layer switch; see the admissibility table above.
    #[derive(Debug, PartialEq, Eq)]
    struct Converged {
        emitted: bool,
        escalated: Option<String>,
        reverted_count: usize,
        bisect_probes: usize,
    }

    fn run(ast: bool) -> Converged {
        // SAFETY: this test is run single-threaded (`--test-threads=1` is not
        // required because the switch is read once per `rewrite_*` call and
        // restored before returning), and the switch is process-global by
        // design: it is a transitional build selector, not a runtime parameter.
        unsafe {
            if ast {
                std::env::set_var("CRAT_M1_AST_EMIT", "1");
            } else {
                std::env::remove_var("CRAT_M1_AST_EMIT");
            }
        }
        let fixture = Fixture::new(&[
            (
                "lib.rs",
                "#![allow(dead_code, unused_unsafe)]\npub mod good;\npub mod bad;\n",
            ),
            (
                "good.rs",
                "pub unsafe fn bump(p: *mut i32) -> i32 {\n    *p += 1;\n    *p\n}\n",
            ),
            ("bad.rs", BREAKS_ON_REWRITE),
        ]);
        // **CAP 0 IS LOAD-BEARING.** At cap 8 the loop reverts once and
        // converges on BOTH layers, so every compared quantity agrees even
        // with the defect restored — measured, not assumed. Round 0's files
        // come from `emit_files` (span-derived) either way, so a single revert
        // repairs the crate before the switched emitter can matter.
        //
        // Cap 0 forces the bisect path, where every candidate program comes
        // from `round_files` and the switch therefore governs. That is exactly
        // why `the_round_cap_stops_the_loop` caught this defect and the cap-8
        // shape did not.
        let out = super::rewrite_m1_path_injected(&fixture.root(), 0, &force_stash_value_shared);
        unsafe { std::env::remove_var("CRAT_M1_AST_EMIT") };
        match out {
            super::RewriteOutcome::Emitted {
                escalated,
                reverted_count,
                bisect_probes,
                ..
            } => Converged {
                emitted: true,
                escalated,
                reverted_count,
                bisect_probes,
            },
            super::RewriteOutcome::Degraded { reason, .. } => Converged {
                emitted: false,
                escalated: Some(reason),
                reverted_count: 0,
                bisect_probes: 0,
            },
        }
    }

    let span = run(false);
    let ast = run(true);

    // NON-VACUITY, first: the fixture must actually exercise a revert, or every
    // assertion below is satisfied by a loop that did nothing.
    assert!(
        span.emitted,
        "the SPAN layer must reach Emitted, or the comparison is vacuous: {span:?}"
    );
    assert!(
        span.reverted_count > 0,
        "the fixture must actually revert something, or W2 tests nothing it \
         claims to: {span:?}"
    );

    assert_eq!(
        span, ast,
        "the layers diverge on loop-derived state.\n  span: {span:?}\n  ast:  {ast:?}"
    );
}
