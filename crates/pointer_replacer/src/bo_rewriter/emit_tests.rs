//! **S2b.0a witnesses — multi-file emission.**
//!
//! These exist because M1's ten goldens are all single-source: the string entry
//! point was fully exercised by its own suite and simultaneously unexercised
//! against the shape it will be run on. 10 of the 20 frozen-corpus programs
//! carry subjects across 2–110 files, so "which file does this edit belong to"
//! is not a question the goldens could ever have asked.

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

use super::{Emission, decide_table, emit_files, plan::FileKey};

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

}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn emit(fixture: &Fixture) -> Emission {
    ::utils::compilation::run_compiler_on_path(&fixture.0.join("lib.rs"), |tcx| {
        let table = decide_table(tcx).expect("fixture yields a decision table");
        emit_files(tcx, &table).expect("emission succeeds")
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
