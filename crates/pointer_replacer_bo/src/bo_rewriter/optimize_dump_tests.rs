//! R1529-2 (main 338): the optimize dump's witnesses D1–D7. They run the whole rewrite in child
//! processes of this test binary, because the dump's switches are read once per process. The child
//! harness is the model checkpoint's.

use std::{
    ffi::OsString,
    path::{Path, PathBuf},
};

use super::model_checkpoint::model_checkpoint_tests::{
    CASCADE_TIE, child, phase_at, scratch, spawn,
};

const DIR: &str = "CRAT_BO_OPTIMIZE_DUMP_DIR";
const CHECKS: &str = "CRAT_BO_OPTIMIZE_DUMP_CHECKS";
const HEAD: &str = "[bo-dump]";
/// D9's child runs its own solve when this is set.
const D9_CHILD: &str = "R1529_2_D9_CHILD";

/// An effective may-overlap pair: the precise verify runs and moves the model (the model checkpoint's
/// `OVERLAP`).
const OVERLAP: &str = r#"
pub unsafe fn two(x: *mut i32, y: *mut i32) { *x = 1; *y = 2; }
pub unsafe fn caller(p: *mut i32) -> i32 { two(p, p); *p }
"#;

fn test(name: &str) -> String {
    format!("bo_rewriter::optimize_dump_tests::{name}")
}

fn os(path: &Path) -> OsString {
    path.as_os_str().to_owned()
}

/// The lines the dump writes (`[bo-dump] …`).
fn dump_lines(stderr: &str) -> Vec<&str> {
    stderr
        .lines()
        .filter(|line| line.starts_with(HEAD))
        .collect()
}

fn names(dir: &Path) -> Vec<String> {
    let mut names = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    names.sort();
    names
}

/// `index.tsv` as (header, rows), each row by column name.
fn index(dir: &Path) -> Vec<std::collections::BTreeMap<String, String>> {
    let text = std::fs::read_to_string(dir.join("index.tsv"))
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()));
    let mut lines = text.lines();
    let header = lines
        .next()
        .expect("index header")
        .split('\t')
        .map(str::to_owned)
        .collect::<Vec<_>>();
    lines
        .map(|line| {
            let cells = line.split('\t').collect::<Vec<_>>();
            assert_eq!(cells.len(), header.len(), "{line}");
            header
                .iter()
                .cloned()
                .zip(cells.into_iter().map(str::to_owned))
                .collect()
        })
        .collect()
}

/// The optimum of a dumped text read back in this process: z3's model of the text, scored on the
/// text's own soft terms (the sum of the weights of the terms the model makes false). The text's
/// `set-option` lines (the query's timeout) are left out, so the parse sets no option in this
/// process; they are no part of the problem.
fn read_back(text: &str) -> (z3::SatResult, u64) {
    let problem = text
        .lines()
        .filter(|line| !line.starts_with("(set-option ") && !line.starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n");
    let optimize = z3::Optimize::new();
    optimize.from_string(problem);
    let result = optimize.check(&[]);
    let model = optimize.get_model().expect("a model of the read-back text");
    let mut objective = 0u64;
    for line in text
        .lines()
        .filter(|line| line.starts_with("(assert-soft "))
    {
        let words = line["(assert-soft ".len()..]
            .trim_end_matches(')')
            .split_whitespace()
            .collect::<Vec<_>>();
        assert!(words.len() == 3 && words[1] == ":weight", "{line}");
        let weight: u64 = words[2].parse().unwrap();
        let term = z3::ast::Bool::new_const(words[0]);
        let value = model
            .eval(&term, true)
            .and_then(|value| value.as_bool())
            .unwrap_or_else(|| panic!("{line}: no value"));
        if !value {
            objective += weight;
        }
    }
    (result, objective)
}

fn count_lines(text: &str, head: &str) -> usize {
    text.lines().filter(|line| line.starts_with(head)).count()
}

fn dump_dir(tag: &str) -> PathBuf {
    scratch(&format!("{tag}-dump"))
}

/// D1: with no switch nothing is dumped or printed, also with the phase log on.
#[test]
fn r1529_2_d1_unset_prints_no_dump_line_and_no_dump_mark() {
    if child() {
        return;
    }
    let (r, err) = spawn(
        &test("r1529_2_d1_unset_prints_no_dump_line_and_no_dump_mark"),
        CASCADE_TIE,
        "r1529-d1",
        "frozen",
        &[("CRAT_BO_PHASE_LOG", "on".into())],
    );
    assert_eq!(r.kind, "emitted", "{r:?}");
    assert!(dump_lines(&err).is_empty(), "{err}");
    assert!(!err.contains("dump:optimize"), "{err}");
}

/// D2: `baseline:0` writes exactly the baseline verify's first optimize check, and its row. The
/// text's counts are the row's, and the text read back in this process has the row's optimum: the
/// objective of the model the solve took. RED at `c408c29c7`: nothing is written.
#[test]
fn r1529_2_d2_one_selected_check_is_written_and_reads_back_to_its_optimum() {
    if child() {
        return;
    }
    let dir = dump_dir("r1529-d2");
    let (r, err) = spawn(
        &test("r1529_2_d2_one_selected_check_is_written_and_reads_back_to_its_optimum"),
        CASCADE_TIE,
        "r1529-d2",
        "frozen",
        &[(DIR, os(&dir)), (CHECKS, "baseline:0".into())],
    );
    assert_eq!(r.kind, "emitted", "{r:?}");
    assert_eq!(
        names(&dir),
        ["baseline-guarded-r00-optimize.smt2", "index.tsv"],
        "{err}"
    );
    let rows = index(&dir);
    assert_eq!(rows.len(), 1, "{rows:?}");
    let row = &rows[0];
    assert_eq!(row["name"], "baseline-guarded-r00-optimize");
    assert_eq!(
        row["result"], "sat",
        "a fixture whose solve is not cut: {row:?}"
    );
    assert_eq!(row["model"], "sat", "{row:?}");
    let text = std::fs::read_to_string(dir.join("baseline-guarded-r00-optimize.smt2")).unwrap();
    assert_eq!(row["bytes"], text.len().to_string());
    assert_eq!(row["hard"], count_lines(&text, "(assert ").to_string());
    assert_eq!(row["soft"], count_lines(&text, "(assert-soft ").to_string());
    assert!(count_lines(&text, "(assert-soft ") > 0, "{text}");
    let slots: usize = ["ref", "own", "raw"]
        .iter()
        .map(|kind| row[*kind].parse::<usize>().unwrap())
        .sum();
    assert_eq!(row["soft"], (2 * slots).to_string(), "{row:?}");
    let (result, objective) = read_back(&text);
    assert_eq!(result, z3::SatResult::Sat);
    assert_eq!(objective.to_string(), row["objective"], "{row:?}");
    let line = dump_lines(&err);
    assert!(
        line.len() == 1
            && line[0].contains("name=baseline-guarded-r00-optimize ")
            && line[0].contains(&format!(" objective={} ", row["objective"]))
            && !line[0].contains("error="),
        "{err}"
    );
}

/// D3: `precise:*` writes the precise verify's checks only, each named `precise-<repair>-rNN-<stage>`, one
/// row per file. RED at `c408c29c7`: nothing is written.
#[test]
fn r1529_2_d3_the_selection_names_the_precise_verify_only() {
    if child() {
        return;
    }
    let dir = dump_dir("r1529-d3");
    let (r, err) = spawn(
        &test("r1529_2_d3_the_selection_names_the_precise_verify_only"),
        OVERLAP,
        "r1529-d3",
        "frozen",
        &[(DIR, os(&dir)), (CHECKS, "precise:*".into())],
    );
    assert_eq!(r.kind, "emitted", "{r:?}");
    let files = names(&dir);
    let dumps = files
        .iter()
        .filter(|name| name.ends_with(".smt2"))
        .collect::<Vec<_>>();
    assert!(!dumps.is_empty(), "{err}");
    assert!(files.contains(&"index.tsv".to_owned()), "{files:?}");
    assert_eq!(dumps.len() + 1, files.len(), "{files:?}");
    assert!(
        dumps
            .iter()
            .any(|name| *name == "precise-guarded-r00-optimize.smt2"),
        "{files:?}"
    );
    for name in &dumps {
        let stem = name.trim_end_matches(".smt2");
        let rest = stem
            .strip_prefix("precise-")
            .unwrap_or_else(|| panic!("{name}"));
        let (repair, rest) = rest.split_once("-r").unwrap();
        assert!(repair == "guarded" || repair == "plain", "{name}");
        let (round, stage) = rest.split_once('-').unwrap();
        assert!(
            round.len() == 2 && round.bytes().all(|b| b.is_ascii_digit()),
            "{name}"
        );
        assert!(stage == "optimize" || stage == "optimize-subset", "{name}");
    }
    let rows = index(&dir);
    let mut row_names = rows
        .iter()
        .map(|row| format!("{}.smt2", row["name"]))
        .collect::<Vec<_>>();
    row_names.sort();
    assert_eq!(row_names.iter().collect::<Vec<_>>(), dumps);
    assert_eq!(dump_lines(&err).len(), rows.len(), "{err}");
}

/// D4: the dump changes no decision: dump on against off, on both fixtures, with every check of
/// both verifies selected. (A guard: green before the build, where nothing is dumped.)
#[test]
fn r1529_2_d4_dump_on_and_off_decide_the_same() {
    if child() {
        return;
    }
    let name = test("r1529_2_d4_dump_on_and_off_decide_the_same");
    for (code, tag) in [
        (CASCADE_TIE, "r1529-d4-cascade"),
        (OVERLAP, "r1529-d4-overlap"),
    ] {
        let (off, _) = spawn(&name, code, &format!("{tag}-off"), "frozen", &[]);
        let dir = dump_dir(tag);
        let (on, on_err) = spawn(
            &name,
            code,
            &format!("{tag}-on"),
            "frozen",
            &[(DIR, os(&dir)), (CHECKS, "baseline:*;precise:*".into())],
        );
        assert_eq!(on.decision(), off.decision(), "{tag}: {on_err}");
        assert_eq!(on.reason, off.reason, "{tag}");
    }
}

/// D5: a failed write is one stderr line, and the decision is the one without the switch. The
/// directory is a regular file. RED at `c408c29c7`: no line.
#[test]
fn r1529_2_d5_a_failed_write_is_one_line_and_moves_nothing() {
    if child() {
        return;
    }
    let name = test("r1529_2_d5_a_failed_write_is_one_line_and_moves_nothing");
    let (off, _) = spawn(&name, CASCADE_TIE, "r1529-d5-off", "frozen", &[]);
    let not_a_dir = scratch("r1529-d5-file").join("plain-file");
    std::fs::write(&not_a_dir, b"not a directory").unwrap();
    let (on, err) = spawn(
        &name,
        CASCADE_TIE,
        "r1529-d5-on",
        "frozen",
        &[(DIR, os(&not_a_dir)), (CHECKS, "baseline:0".into())],
    );
    assert_eq!(on.decision(), off.decision(), "{err}");
    let line = dump_lines(&err);
    assert!(
        line.len() == 1
            && line[0].contains("name=baseline-guarded-r00-optimize ")
            && line[0].contains(" error="),
        "{err}"
    );
    assert_eq!(std::fs::read(&not_a_dir).unwrap(), b"not a directory");
}

/// D6: a directory without a selection, or a selection that does not parse, is one stderr line and
/// no file. RED at `c408c29c7`: no line.
#[test]
fn r1529_2_d6_no_selection_or_a_bad_one_is_one_line_and_no_file() {
    if child() {
        return;
    }
    let name = test("r1529_2_d6_no_selection_or_a_bad_one_is_one_line_and_no_file");
    for (tag, checks) in [
        ("r1529-d6-unset", None),
        ("r1529-d6-solve", Some("final:0")),
        ("r1529-d6-round", Some("precise:x")),
        ("r1529-d6-empty", Some("")),
    ] {
        let dir = dump_dir(tag);
        let mut env = vec![(DIR, os(&dir))];
        if let Some(checks) = checks {
            env.push((CHECKS, checks.into()));
        }
        let (r, err) = spawn(&name, CASCADE_TIE, tag, "frozen", &env);
        assert_eq!(r.kind, "emitted", "{tag}: {r:?}");
        let line = dump_lines(&err);
        assert!(
            line.len() == 1 && line[0].contains(" off: ") && line[0].contains(CHECKS),
            "{tag}: {err}"
        );
        assert!(names(&dir).is_empty(), "{tag}: {:?}", names(&dir));
    }
}

/// D7: the dump has its own phase marks, start and end, and they close before the check's model
/// is read: both precede `decide:solve end`. RED at `c408c29c7`: no mark.
#[test]
fn r1529_2_d7_the_dump_has_its_own_marks() {
    if child() {
        return;
    }
    let dir = dump_dir("r1529-d7");
    let (r, err) = spawn(
        &test("r1529_2_d7_the_dump_has_its_own_marks"),
        CASCADE_TIE,
        "r1529-d7",
        "frozen",
        &[
            (DIR, os(&dir)),
            (CHECKS, "baseline:0".into()),
            ("CRAT_BO_PHASE_LOG", "on".into()),
        ],
    );
    assert_eq!(r.kind, "emitted", "{r:?}");
    let start = phase_at(&err, "dump:optimize", "start").expect("the dump's start mark");
    let end = phase_at(&err, "dump:optimize", "end").expect("the dump's end mark");
    let solved = phase_at(&err, "decide:solve", "end").expect("decide:solve end");
    assert!(start < end && end < solved, "{err}");
    assert_eq!(
        err.matches("[bo-phase] dump:optimize start").count(),
        1,
        "{err}"
    );
    let row = &index(&dir)[0];
    assert!(row["dump_wall_s"].parse::<f64>().is_ok(), "{row:?}");
}

/// D9 (review E1): a guarded run that declines falls back to the plain repair inside the same
/// verify, from round 0; the plain run's checks have their own names, and no name is written twice.
/// The decline is the test fault `guarded_decline_fault` (at the guarded run's first re-solve after a
/// validation round), armed on the thread that solves: the child runs one baseline verify on
/// `R1468_CASCADE` (`retirement/tests_rounds.rs`'s r1468_2_a) inside the compiler callback. RED at
/// `2b446b787`: the plain run's first solve took the guarded run's last round, so a later plain
/// round collided (an error line) and no name told the two runs apart.
#[test]
fn r1529_2_d9_a_guarded_decline_s_plain_run_has_its_own_names() {
    use rustc_hir::{ItemKind, OwnerNode};

    use crate::analyses::borrow_ownership::{
        borrow_verify::guarded_decline_fault,
        construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
        crate_slots::CrateSlots,
        mutability_facts::MutFacts,
        origins::compute_origins,
        solver::KindSolver,
    };
    const R1468_CASCADE: &str = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
        pub unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";
    let name = test("r1529_2_d9_a_guarded_decline_s_plain_run_has_its_own_names");
    if std::env::var_os(D9_CHILD).is_some() {
        ::utils::compilation::run_compiler_on_str(R1468_CASCADE, |tcx| {
            let mut functions = Vec::new();
            for owner in tcx.hir_crate(()).owners.iter() {
                let Some(owner) = owner.as_owner() else { continue };
                let OwnerNode::Item(item) = owner.node() else { continue };
                if let ItemKind::Fn { .. } = item.kind {
                    functions.push(item.owner_id.def_id);
                }
            }
            let program = crate::utils::rustc::RustProgram {
                tcx,
                functions,
                structs: Vec::new(),
            };
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let facts = MutFacts::from_program(&program);
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("production construction");
            crate::optimize_dump::enter_verify(crate::optimize_dump::Solve::Baseline);
            let ((model, stats), fired) = guarded_decline_fault::with_decline(|| {
                verify_bo_construction_counting(
                    &program,
                    &slots,
                    &origins,
                    &solver,
                    &construction,
                    &facts,
                )
            });
            assert!(fired.is_some(), "the guarded decline never fired");
            assert!(stats.guarded_fallback.is_some(), "{stats:?}");
            assert!(model.is_some(), "the plain repair accepts: {stats:?}");
        })
        .expect("D9's child compiles the fixture");
        return;
    }
    let dir = dump_dir("r1529-d9");
    let output = std::process::Command::new(std::env::current_exe().expect("current_exe"))
        .args([
            name.as_str(),
            "--exact",
            "--include-ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env_clear()
        .envs(std::env::vars_os().filter(|(name, _)| !name.to_string_lossy().starts_with("CRAT_")))
        .env(D9_CHILD, "1")
        .env(DIR, &dir)
        .env(CHECKS, "baseline:*")
        .output()
        .expect("child");
    let err = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "{}\n{err}",
        String::from_utf8_lossy(&output.stdout)
    );
    let files = names(&dir);
    for expected in [
        "baseline-guarded-r00-optimize.smt2",
        "baseline-plain-r00-optimize.smt2",
        "baseline-plain-r01-optimize.smt2",
    ] {
        assert!(
            files.contains(&expected.to_owned()),
            "{expected}: {files:?}\n{err}"
        );
    }
    let lines = dump_lines(&err);
    assert!(
        lines.iter().all(|line| !line.contains("error=")),
        "{lines:#?}"
    );
    let dumps = files.iter().filter(|name| name.ends_with(".smt2")).count();
    assert_eq!(index(&dir).len(), dumps, "{files:?}");
    assert_eq!(lines.len(), dumps, "{lines:#?}");
}
