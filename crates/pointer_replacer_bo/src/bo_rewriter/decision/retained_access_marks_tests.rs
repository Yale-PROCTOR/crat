//! R1543-2 (main 343 §8, B4): the points loop's marks, M0–M2. They run the whole rewrite in child
//! processes of this test binary (the phase log's switch is read once per process), with the model
//! checkpoint's child harness.

use std::ffi::OsString;

use crate::bo_rewriter::model_checkpoint::model_checkpoint_tests::{CASCADE_TIE, child, spawn};

/// CASCADE_TIE with copies of memory: a struct assignment through pointers and a `memcpy`.
fn fixture() -> String {
    format!(
        "{CASCADE_TIE}{}",
        r#"
#[derive(Clone, Copy)]
pub struct Holder { p: *mut i32 }
unsafe extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: usize) -> *mut core::ffi::c_void;
}
pub unsafe fn copy_holder(a: *mut Holder, b: *mut Holder) {
    *a = *b;
    memcpy(a as *mut core::ffi::c_void, b as *const core::ffi::c_void, 8);
}
pub unsafe fn through(x: *mut i32) -> i32 {
    let mut s = Holder { p: x };
    let mut t = Holder { p: core::ptr::null_mut() };
    copy_holder(&mut t, &mut s);
    *t.p
}
"#
    )
}

/// The harness's child marker (`model_checkpoint_tests::CHILD_OUT`): set only in a child.
fn in_child() -> bool {
    std::env::var_os("CRAT_R1520_2_CHILD_OUT").is_some()
}

/// The `[bo-phase]` lines of one phase: the words after the edge, as key=value.
fn lines(stderr: &str, phase: &str) -> Vec<Vec<(String, String)>> {
    stderr
        .lines()
        .filter_map(|line| {
            let mut words = line.split_whitespace();
            (words.next() == Some("[bo-phase]")).then_some(())?;
            (words.next() == Some(phase)).then_some(())?;
            assert_eq!(words.next(), Some("progress"), "{line}");
            Some(
                words
                    .filter_map(|word| word.split_once('='))
                    .map(|(k, v)| (k.to_owned(), v.to_owned()))
                    .collect(),
            )
        })
        .collect()
}

fn get<'a>(fields: &'a [(String, String)], key: &str) -> &'a str {
    fields
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.as_str())
        .unwrap_or_else(|| panic!("no {key}= in {fields:?}"))
}

fn num(fields: &[(String, String)], key: &str) -> usize {
    get(fields, key)
        .parse()
        .unwrap_or_else(|e| panic!("{key}: {e} in {fields:?}"))
}

fn secs(fields: &[(String, String)], key: &str) -> f64 {
    get(fields, key)
        .parse()
        .unwrap_or_else(|e| panic!("{key}: {e} in {fields:?}"))
}

fn logged(test: &str, tag: &str) -> String {
    let (result, stderr) = spawn(
        test,
        &fixture(),
        tag,
        "frozen",
        &[("CRAT_BO_PHASE_LOG", OsString::from("on"))],
    );
    assert_eq!(result.kind, "emitted", "{result:?}");
    stderr
}

/// M0: the marks change nothing. The emitted tree, receipt and model are the same with the log on
/// and off; off, stderr carries no phase line. (It passes at the RED stage: the marks are log only.)
#[test]
fn r1543_2_m0_unset_writes_no_mark_and_changes_nothing() {
    if child() {
        return;
    }
    let test = "bo_rewriter::decision::retained_access::marks_tests::r1543_2_m0_unset_writes_no_mark_and_changes_nothing";
    let (on, on_err) = spawn(
        test,
        &fixture(),
        "r1543-m0-on",
        "frozen",
        &[("CRAT_BO_PHASE_LOG", OsString::from("on"))],
    );
    let (off, off_err) = spawn(test, &fixture(), "r1543-m0-off", "frozen", &[]);
    assert_eq!(on.kind, "emitted", "{on:?}");
    assert_eq!(on, off);
    assert!(!off_err.contains("[bo-phase]"), "{off_err}");
    assert!(on_err.contains("[bo-phase]"), "{on_err}");
}

/// M1: with the log on, every relation writes its stages in order, every `solve_points` call writes
/// a start line, one line per round (rounds 1..n, the last one changing no function) and an end line
/// with `rounds=n`, and every pass writes an end line. RED at `611a85aae`: no such line.
#[test]
fn r1543_2_m1_every_points_call_writes_its_rounds() {
    if child() {
        return;
    }
    let test = "bo_rewriter::decision::retained_access::marks_tests::r1543_2_m1_every_points_call_writes_its_rounds";
    let stderr = logged(test, "r1543-m1");
    let stages = lines(&stderr, "retained_access:relation");
    let relations: Vec<usize> = stages
        .iter()
        .filter(|f| get(f, "stage") == "setup")
        .map(|f| num(f, "relation"))
        .collect();
    assert!(!relations.is_empty(), "no relation:\n{stderr}");
    assert_eq!(
        relations,
        (1..=relations.len()).collect::<Vec<_>>(),
        "{stderr}"
    );
    let points = lines(&stderr, "retained_access:points");
    for &relation in &relations {
        let order: Vec<&str> = stages
            .iter()
            .filter(|f| num(f, "relation") == relation)
            .map(|f| get(f, "stage"))
            .collect();
        assert_eq!(order[..3], ["setup", "points", "escapes"], "{order:?}");
        assert!(order.contains(&"accesses"), "{order:?}");
        let mine: Vec<&Vec<(String, String)>> = points
            .iter()
            .filter(|f| num(f, "relation") == relation)
            .collect();
        let calls = mine.iter().map(|f| num(f, "call")).max().unwrap();
        assert_eq!(
            calls,
            order.iter().filter(|s| s.starts_with("points")).count(),
            "one call per points stage: {order:?}"
        );
        for call in 1..=calls {
            let at: Vec<&Vec<(String, String)>> = mine
                .iter()
                .copied()
                .filter(|f| num(f, "call") == call)
                .collect();
            assert_eq!(get(at[0], "at"), "start");
            assert!(num(at[0], "functions") > 0);
            let end = at.last().unwrap();
            assert_eq!(get(end, "at"), "end");
            let rounds = &at[1..at.len() - 1];
            assert!(!rounds.is_empty());
            assert_eq!(num(end, "rounds"), rounds.len());
            for (i, round) in rounds.iter().enumerate() {
                assert_eq!(get(round, "at"), "round");
                assert_eq!(num(round, "round"), i + 1);
                assert!(secs(round, "wall") >= 0.0);
                for key in ["points", "contents", "fresh", "fresh_backed", "copies"] {
                    num(round, key);
                }
                get(round, "slowest_fn");
                if cfg!(all(target_os = "linux", target_env = "gnu")) {
                    num(round, "uordblks");
                    num(round, "fordblks");
                }
            }
            assert_eq!(num(rounds.last().unwrap(), "changed_fns"), 0);
        }
    }
    let passes = lines(&stderr, "retained_access:pass");
    assert_eq!(
        passes
            .iter()
            .map(|f| num(f, "relation"))
            .collect::<Vec<_>>(),
        relations
    );
}

/// M2: m2 and m3 name the call. With the limits at zero (the child of this test only), every
/// `copy_memory` call writes its line with the body, the block, the call site (a line of
/// `retained_access.rs` that calls `copy_memory`) and its tally, and every `flow_body` call writes
/// one, so each round of each call has one line per function. The release limits are 10 s and 60 s.
/// RED at `611a85aae`: no such line.
#[test]
fn r1543_2_m2_the_slow_lines_name_the_call() {
    assert_eq!((super::SLOW_COPY_S, super::SLOW_BODY_S), (10, 60));
    if in_child() {
        super::MARKS_SLOW_ZERO.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    if child() {
        return;
    }
    let test = "bo_rewriter::decision::retained_access::marks_tests::r1543_2_m2_the_slow_lines_name_the_call";
    let stderr = logged(test, "r1543-m2");
    let source = include_str!("retained_access.rs");
    let source: Vec<&str> = source.lines().collect();
    let copies = lines(&stderr, "retained_access:copy_memory");
    assert!(!copies.is_empty(), "no copy line:\n{stderr}");
    for copy in &copies {
        let line = num(copy, "line");
        assert!(
            source[line - 1].contains("copy_memory("),
            "line {line}: {}",
            source[line - 1]
        );
        assert!(get(copy, "block").starts_with("bb"), "{copy:?}");
        assert_ne!(get(copy, "fn"), "-");
        assert!(num(copy, "grew") <= num(copy, "stores"));
        assert!(num(copy, "max_set") <= num(copy, "objs"));
        for key in ["from", "to", "sources", "targets", "keys"] {
            num(copy, key);
        }
    }
    assert!(
        copies.iter().any(|c| num(c, "keys") > 0),
        "no copy of held memory: {copies:?}"
    );
    let points = lines(&stderr, "retained_access:points");
    let bodies = lines(&stderr, "retained_access:flow_body");
    for start in points.iter().filter(|f| get(f, "at") == "start") {
        let (relation, call) = (num(start, "relation"), num(start, "call"));
        let functions = num(start, "functions");
        let rounds = points
            .iter()
            .find(|f| {
                get(f, "at") == "end" && num(f, "relation") == relation && num(f, "call") == call
            })
            .map(|f| num(f, "rounds"))
            .unwrap();
        for round in 1..=rounds {
            let n = bodies
                .iter()
                .filter(|f| {
                    num(f, "relation") == relation
                        && num(f, "call") == call
                        && num(f, "round") == round
                })
                .count();
            assert_eq!(
                n, functions,
                "relation {relation} call {call} round {round}"
            );
        }
    }
}
