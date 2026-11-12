//! R1520-2 (main 336 §B3): the fact stretch's marks, WB1–WB3. They run the whole rewrite in child
//! processes of this test binary (the phase log's switch is read once per process), with the model
//! checkpoint's child harness.

use std::ffi::OsString;

use super::model_checkpoint::model_checkpoint_tests::{CASCADE_TIE, child, spawn};

/// The end marks between `finish_decide start` and `finish_decide:facts end`, in order (main 336
/// §B2: one after each collection of `mod.rs`'s fact stretch at `f1dcb012b`).
const END_MARKS: [&str; 43] = [
    "subjects",
    "box_facts",
    "free_sites",
    "constructions",
    "subject_stamp",
    "declaration",
    "field_alloc",
    "counted_void",
    "io_domain",
    "void_pointee",
    "declaration_pattern",
    "interface",
    "emitability",
    "void_region",
    "thin_extent",
    "fat",
    "sign",
    "slice_uses:full",
    "cursor_candidates",
    "local_callee_extent",
    "slice_uses:returns",
    "slice_uses:prior",
    "opt_accessors",
    "opt_uses:provisional",
    "opt_uses:prior",
    "opt_uses:full",
    "opt_uses:returns",
    "contract_extent",
    "a5_site_proofs",
    "fnptr_web",
    "pair_disjointness",
    "void_region_pair_gate",
    "exposure",
    "flexible_tails",
    "retained_access",
    "consuming_formals",
    "exported_pairs",
    "return_certificates",
    "allocator_contracts",
    "box_params",
    "confirm_transfers",
    "certificate_clones",
    "released_indirect",
];

/// The three per-subject loops with progress lines (main 336 §B2, rows 5, 17, 20).
const PROGRESS: [&str; 3] = ["subject_stamp", "cursor_candidates", "opt_accessors"];

/// One phase line: `(phase, edge, the words after t= … as key=value)`.
fn phase_lines(stderr: &str) -> Vec<(String, String, Vec<(String, String)>)> {
    stderr
        .lines()
        .filter_map(|line| {
            let mut words = line.split_whitespace();
            (words.next() == Some("[bo-phase]")).then_some(())?;
            let phase = words.next()?.to_owned();
            let edge = words.next()?.to_owned();
            let fields = words
                .filter_map(|word| word.split_once('='))
                .map(|(k, v)| (k.to_owned(), v.to_owned()))
                .collect();
            Some((phase, edge, fields))
        })
        .collect()
}

fn field<'a>(fields: &'a [(String, String)], key: &str) -> Option<&'a str> {
    fields
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.as_str())
}

/// The first fact stretch's lines: strictly between `finish_decide start` and `finish_decide:facts end`,
/// with the end line's `subjects=` count.
fn stretch(stderr: &str) -> (Vec<(String, String, Vec<(String, String)>)>, usize) {
    let all = phase_lines(stderr);
    let start = all
        .iter()
        .position(|(p, e, _)| p == "finish_decide" && e == "start")
        .unwrap_or_else(|| panic!("no finish_decide start:\n{stderr}"));
    let end = start
        + all[start..]
            .iter()
            .position(|(p, e, _)| p == "finish_decide:facts" && e == "end")
            .unwrap_or_else(|| panic!("no finish_decide:facts end:\n{stderr}"));
    let subjects = field(&all[end].2, "subjects")
        .and_then(|n| n.parse().ok())
        .expect("the facts end's subjects=");
    (all[start + 1..end].to_vec(), subjects)
}

fn logged(
    test: &str,
    tag: &str,
) -> (
    super::model_checkpoint::model_checkpoint_tests::ChildResult,
    String,
) {
    spawn(
        test,
        CASCADE_TIE,
        tag,
        "frozen",
        &[("CRAT_BO_PHASE_LOG", OsString::from("on"))],
    )
}

/// WB1: with the phase log on, the fact stretch writes one `finish_decide:facts:<name> end` line
/// after each collection, in the order of `mod.rs`, and one progress line at the last subject of
/// each per-subject loop, before that loop's end line. RED at `f1dcb012b`: no line falls there.
#[test]
fn r1520_2_wb1_the_fact_stretch_writes_its_marks_in_order() {
    if child() {
        return;
    }
    let test =
        "bo_rewriter::fact_marks_tests::r1520_2_wb1_the_fact_stretch_writes_its_marks_in_order";
    let (result, stderr) = logged(test, "wb1");
    assert_eq!(result.kind, "emitted", "{result:?}");
    let (lines, _) = stretch(&stderr);
    let ends: Vec<&str> = lines
        .iter()
        .filter(|(_, e, _)| e == "end")
        .map(|(p, _, _)| {
            p.strip_prefix("finish_decide:facts:")
                .unwrap_or_else(|| panic!("a foreign line in the stretch: {p}"))
        })
        .collect();
    assert_eq!(ends, END_MARKS.to_vec());
    for name in PROGRESS {
        let phase = format!("finish_decide:facts:{name}");
        let progress = lines
            .iter()
            .position(|(p, e, _)| *p == phase && e == "progress")
            .unwrap_or_else(|| panic!("{name}: no progress line"));
        let end = lines
            .iter()
            .position(|(p, e, _)| *p == phase && e == "end")
            .unwrap();
        assert!(progress < end, "{name}");
    }
    assert!(
        lines.iter().all(|(_, e, _)| e == "end" || e == "progress"),
        "{lines:?}"
    );
}

/// WB2: the counts are the collections' lengths: the `subjects` line's count is the facts end line's,
/// and each per-subject loop's last progress line reads `done=N of=N` with that N.
#[test]
fn r1520_2_wb2_the_counts_are_the_collections_lengths() {
    if child() {
        return;
    }
    let test = "bo_rewriter::fact_marks_tests::r1520_2_wb2_the_counts_are_the_collections_lengths";
    let (_, stderr) = logged(test, "wb2");
    let (lines, subjects) = stretch(&stderr);
    assert!(subjects > 0);
    let at = |name: &str, edge: &str| {
        lines
            .iter()
            .rfind(|(p, e, _)| *p == format!("finish_decide:facts:{name}") && e == edge)
            .map(|(_, _, fields)| fields.clone())
            .unwrap_or_else(|| panic!("{name} {edge}"))
    };
    let n = subjects.to_string();
    assert_eq!(field(&at("subjects", "end"), "subjects"), Some(n.as_str()));
    for name in PROGRESS {
        let fields = at(name, "progress");
        assert_eq!(field(&fields, "done"), Some(n.as_str()), "{name}");
        assert_eq!(field(&fields, "of"), Some(n.as_str()), "{name}");
    }
}

/// WB3: the marks change nothing. The emitted tree, receipt and model are the same with the log on
/// and off, and with it off stderr carries no phase line. (It passes at the RED stage: the marks are
/// log only.)
#[test]
fn r1520_2_wb3_the_marks_change_nothing() {
    if child() {
        return;
    }
    let test = "bo_rewriter::fact_marks_tests::r1520_2_wb3_the_marks_change_nothing";
    let (on, _) = logged(test, "wb3-on");
    let (off, off_err) = spawn(test, CASCADE_TIE, "wb3-off", "frozen", &[]);
    assert_eq!(on.kind, "emitted", "{on:?}");
    assert_eq!(on, off);
    assert!(!off_err.contains("[bo-phase]"), "{off_err}");
}
