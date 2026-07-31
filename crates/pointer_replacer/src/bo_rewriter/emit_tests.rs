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
            fs::write(dir.join(name), text).expect("write emission fixture file");
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

/// **S2b.0 instrument repair.** A crate that FAILS the gate still reports what
/// it attempted.
///
/// S2b.0's first sweep reported `emitted=0` for all ten failing programs,
/// because the `Degraded` arm carried no counts — so the corpus emission yield
/// was an undercount and the span-bucket axis was blocked outright. The failing
/// programs had of course emitted subjects; that is what broke their crates.
///
/// The fixture mirrors `ht`'s real shape: a rewritten parameter stored into a
/// raw-pointer struct field.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** re-zero the `Degraded`
/// arm (`emitted_count: 0`, `emitted_sites: Vec::new()`) and this fails.
#[test]
fn a_crate_that_fails_the_gate_still_reports_what_it_attempted() {
    let fixture = Fixture::new(&[
        ("lib.rs", "#![allow(dead_code, unused_unsafe)]\npub mod m;\n"),
        (
            "m.rs",
            "pub struct Holder {\n    pub slot: *mut i32,\n}\npub unsafe fn stash(value: *mut i32, holder: *mut Holder) {\n    (*holder).slot = value;\n}\n",
        ),
    ]);

    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Degraded {
            emitted_count,
            files_touched,
            emitted_sites,
            reason,
            ..
        } => {
            assert!(
                reason.contains("type-check gate"),
                "this witness needs a GATE failure, got: {reason}"
            );
            assert!(
                emitted_count >= 1,
                "a failing crate reported {emitted_count} emitted subjects — the \
                 attempt is unobservable and the yield figure is an undercount"
            );
            assert!(files_touched >= 1, "files_touched was zeroed: {files_touched}");
            assert!(
                !emitted_sites.is_empty(),
                "no emitted sites recorded — the span-bucket axis stays blocked"
            );
            let site = &emitted_sites[0];
            assert!(
                site.fn_path.contains("stash"),
                "site does not name the rewritten subject's own fn: {site:?}"
            );
            // THE EXTENT MUST COVER THE BODY. `stash` is declared on line 4 of
            // `m.rs` and the offending store is on line 5. A signature-only span
            // measures 4..4, so every diagnostic falls outside every extent and
            // the own-fn bucket can only ever report zero — which is exactly
            // what the first re-sweep produced, uniformly and plausibly.
            assert!(
                site.lo_line <= 5 && 5 <= site.hi_line,
                "the fn extent {}..{} does not contain its own body line 5 — the \
                 own-fn bucket would be unfailable by construction: {site:?}",
                site.lo_line,
                site.hi_line
            );
        }
        super::RewriteOutcome::Emitted { .. } => {
            panic!("the fixture must FAIL the gate for this witness to mean anything")
        }
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
