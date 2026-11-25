//! R1543-2 Part 2 (main 346 §4; the seat's R1543-4): the external MaxSAT path's witnesses P1–P5.
//! P1's fixtures, P2's hook half, P3 and P5 run the whole rewrite in child processes of this test
//! binary (the switches are read once per process), with the model checkpoint's child harness. The
//! rest runs here, with test-built shell scripts in place of a solver: no external binary but P5's.

use std::{
    ffi::OsString,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

use z3::{
    Model, Optimize, SatResult, Solver,
    ast::{Bool, Int},
};

use super::model_checkpoint::model_checkpoint_tests::{
    CASCADE_TIE, ChildResult, child, scratch, spawn,
};
use crate::maxsat::{Cause, Check, Report, RunLine, Wcnf, attempt, encode, hand_back, soft_cost};

const SWITCH: &str = "CRAT_BO_MAXSAT_CMD";
const DUMP_DIR: &str = "CRAT_BO_OPTIMIZE_DUMP_DIR";
const DUMP_CHECKS: &str = "CRAT_BO_OPTIMIZE_DUMP_CHECKS";
/// Every optimize check of every verify.
const ALL_CHECKS: &str = "baseline:*;precise:*;refined:*;coarse:*";

/// An effective may-overlap pair (the model checkpoint's `OVERLAP`).
const OVERLAP: &str = r#"
pub unsafe fn two(x: *mut i32, y: *mut i32) { *x = 1; *y = 2; }
pub unsafe fn caller(p: *mut i32) -> i32 { two(p, p); *p }
"#;

/// P5's fixture: no allocation and no free, so no ownership tie.
const UNIQUE: &str = r#"
pub unsafe fn get(p: *const i32) -> i32 { *p }
pub unsafe fn set(p: *mut i32, v: i32) { *p = v; }
pub unsafe fn both(p: *mut i32) -> i32 { set(p, 1); get(p) }
"#;

fn test(name: &str) -> String {
    format!("bo_rewriter::maxsat_tests::{name}")
}

fn os(path: &Path) -> OsString {
    path.as_os_str().to_owned()
}

/// The phase-log lines of `phase`.
fn lines<'a>(stderr: &'a str, phase: &str) -> Vec<&'a str> {
    let head = format!("[bo-phase] {phase} ");
    stderr
        .lines()
        .filter(|line| line.starts_with(&head))
        .collect()
}

fn holds(model: &Model, term: &Bool) -> bool {
    model.eval(term, true).and_then(|value| value.as_bool()) == Some(true)
}

fn index(lit: i32) -> usize {
    usize::try_from(lit.unsigned_abs()).unwrap() - 1
}

fn true_under(values: &[bool], lit: i32) -> bool {
    values[index(lit)] == (lit > 0)
}

/// The WCNF as written to its file, read back: (hard clauses, soft terms).
fn written(wcnf: &Wcnf) -> (Vec<Vec<i32>>, Vec<(u64, i32)>) {
    let mut bytes = Vec::new();
    wcnf.write_to(&mut bytes).unwrap();
    let text = String::from_utf8(bytes).unwrap();
    let mut hard = Vec::new();
    let mut soft = Vec::new();
    for line in text.lines().filter(|line| !line.starts_with('c')) {
        let mut words = line.split_whitespace();
        let head = words.next().expect("a word");
        let mut lits: Vec<i32> = words.map(|word| word.parse().unwrap()).collect();
        assert_eq!(lits.pop(), Some(0), "{line}");
        assert!(
            lits.iter().all(|&lit| lit != 0 && lit.abs() <= wcnf.vars),
            "{line}"
        );
        if head == "h" {
            hard.push(lits);
        } else {
            assert_eq!(lits.len(), 1, "{line}");
            soft.push((head.parse().unwrap(), lits[0]));
        }
    }
    assert_eq!(hard.len(), wcnf.hard_count);
    assert_eq!(soft.len(), wcnf.soft.len());
    (hard, soft)
}

/// The WCNF's cost under `values` (every variable), the folded weight in.
fn wcnf_cost(wcnf: &Wcnf, soft: &[(u64, i32)], values: &[bool]) -> u64 {
    wcnf.offset
        + soft
            .iter()
            .filter(|(_, lit)| !true_under(values, *lit))
            .map(|(weight, _)| *weight)
            .sum::<u64>()
}

/// An optimal assignment of the written WCNF, by z3 over the file's clauses alone: it reads nothing
/// of the encoder but the clauses. `None` when the clauses are unsatisfiable.
fn solve_written(vars: usize, hard: &[Vec<i32>], soft: &[(u64, i32)]) -> Option<Vec<bool>> {
    let x: Vec<Bool> = (1..=vars)
        .map(|i| Bool::new_const(format!("r1543_2_wcnf_{i}")))
        .collect();
    let lit = |lit: i32| {
        if lit > 0 {
            x[index(lit)].clone()
        } else {
            !&x[index(lit)]
        }
    };
    let optimize = Optimize::new();
    for clause in hard {
        let lits: Vec<Bool> = clause.iter().map(|&l| lit(l)).collect();
        optimize.assert(&Bool::or(&lits));
    }
    for &(weight, l) in soft {
        optimize.assert_soft(&lit(l), weight, None);
    }
    match optimize.check(&[]) {
        SatResult::Sat => {}
        SatResult::Unsat => return None,
        SatResult::Unknown => panic!("z3 on the written WCNF: unknown"),
    }
    let model = optimize.get_model().unwrap();
    Some(x.iter().map(|b| holds(&model, b)).collect())
}

/// z3's `Optimize` on the problem itself: its optimum, `None` when the hard part is unsatisfiable.
fn z3_optimum(hard: &[Bool], soft: &[(Bool, u64)]) -> Option<u64> {
    let optimize = Optimize::new();
    for assertion in hard {
        optimize.assert(assertion);
    }
    for (term, weight) in soft {
        optimize.assert_soft(term, *weight, None);
    }
    match optimize.check(&[]) {
        SatResult::Sat => Some(soft_cost(&optimize.get_model().unwrap(), soft)),
        SatResult::Unsat => None,
        SatResult::Unknown => panic!("z3 on the problem: unknown"),
    }
}

/// Unit propagation from the mapped originals' values (`(index, value)`). Every auxiliary variable
/// is a Tseitin gate's output, which its inputs force, so the assignment ends total, or a clause is
/// violated (`None`).
fn propagate(vars: usize, hard: &[Vec<i32>], fixed: &[(usize, bool)]) -> Option<Vec<bool>> {
    let mut value: Vec<Option<bool>> = vec![None; vars];
    for &(at, v) in fixed {
        value[at] = Some(v);
    }
    loop {
        let mut changed = false;
        for clause in hard {
            let mut open = Vec::new();
            let mut satisfied = false;
            for &lit in clause {
                match value[index(lit)] {
                    Some(v) if v == (lit > 0) => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => open.push(lit),
                }
            }
            if satisfied {
                continue;
            }
            match open.as_slice() {
                [] => return None,
                [lit] => {
                    value[index(*lit)] = Some(*lit > 0);
                    changed = true;
                }
                _ => {}
            }
        }
        if !changed {
            break;
        }
    }
    let values: Vec<bool> = value
        .into_iter()
        .map(|v| v.expect("a Tseitin output left open"))
        .collect();
    hard.iter()
        .all(|clause| clause.iter().any(|&lit| true_under(&values, lit)))
        .then_some(values)
}

/// Every operator the encoder takes, each top-level shape, two units and the folds: six mapped
/// variables (`a`–`f`), two fixed by units (`g` true, `h` false). Two assignments are feasible:
/// a0 b0 c1 d1 e1 f0 (cost 9, the optimum) and a1 b0 c0 d1 e0 f1 (cost 14).
fn operator_problem() -> (Vec<Bool>, Vec<(Bool, u64)>) {
    let v = |name: &str| Bool::new_const(format!("r1543_2_p1_{name}"));
    let (a, b, c, d, e, f, g, h) = (
        v("a"),
        v("b"),
        v("c"),
        v("d"),
        v("e"),
        v("f"),
        v("g"),
        v("h"),
    );
    let hard = vec![
        g.clone(),
        !&h,
        Bool::from_bool(true),
        Bool::or(&[a.clone(), b.xor(&c)]),
        a.implies(!Bool::and(&[b.clone(), d.clone()])),
        c.iff(d.ite(&e, &f)),
        !Bool::and(&[e.clone(), f.clone(), g.clone()]),
        !!Bool::or(&[d.clone(), e.clone(), h.clone()]),
        !a.xor(&f),
        d.eq(e.xor(&f)),
        a.implies(&b).implies(&c),
        Bool::and(&[
            Bool::or(&[a.clone(), b.clone(), c.clone()]),
            Bool::or(&[c.clone(), d.clone()]),
        ]),
        !d.implies(&h),
        !Bool::or(&[h.clone(), Bool::and(&[b.clone(), e.clone()])]),
    ];
    let soft = vec![
        (a.clone(), 3),
        (b.clone(), 2),
        (Bool::and(&[c.clone(), d.clone()]), 5),
        (e.clone(), 1),
        (h.clone(), 4),
        (g.clone(), 7),
        (!&f, 2),
    ];
    (hard, soft)
}

/// P1 on one problem: the written WCNF's optimum is z3's on the problem, and its optimal assignment
/// handed back is `Sat`, every mapped variable reading back its value, at the same soft cost.
fn differential(name: &str, hard: &[Bool], soft: &[(Bool, u64)]) {
    let optimum = z3_optimum(hard, soft);
    let wcnf = match encode(hard, soft) {
        Ok(wcnf) => wcnf,
        Err(Cause::HardFalse) => {
            assert_eq!(optimum, None, "{name}: the encoding folds to false");
            return;
        }
        Err(cause) => panic!("{name}: {cause:?}"),
    };
    let (clauses, wsoft) = written(&wcnf);
    let vars = usize::try_from(wcnf.vars).unwrap();
    let Some(values) = solve_written(vars, &clauses, &wsoft) else {
        assert_eq!(optimum, None, "{name}: the WCNF is unsatisfiable");
        return;
    };
    let cost = wcnf_cost(&wcnf, &wsoft, &values);
    assert_eq!(Some(cost), optimum, "{name}: the optimum");
    let model = hand_back(&Solver::new(), 0, hard, &wcnf, &values)
        .unwrap_or_else(|cause| panic!("{name}: {cause:?}"));
    for (symbol, at) in &wcnf.originals {
        let want = values[usize::try_from(*at - 1).unwrap()];
        assert_eq!(holds(&model, symbol), want, "{name}: {symbol:?}");
    }
    assert_eq!(
        soft_cost(&model, soft),
        cost,
        "{name}: the handed-back cost"
    );
}

/// A problem as the optimize dump wrote it: (file, hard assertions, soft terms).
type Dumped = (String, Vec<Bool>, Vec<(Bool, u64)>);

/// A dumped text read back here: z3 parses its hard part; its soft terms are its `assert-soft` lines.
/// The `set-option` lines (the query's timeout) are left out (the optimize dump's own read-back).
fn read_problem(text: &str) -> (Vec<Bool>, Vec<(Bool, u64)>) {
    let problem = text
        .lines()
        .filter(|line| !line.starts_with("(set-option ") && !line.starts_with(';'))
        .collect::<Vec<_>>()
        .join("\n");
    let optimize = Optimize::new();
    optimize.from_string(problem);
    let soft = text
        .lines()
        .filter(|line| line.starts_with("(assert-soft "))
        .map(|line| {
            let words = line["(assert-soft ".len()..]
                .trim_end_matches(')')
                .split_whitespace()
                .collect::<Vec<_>>();
            assert!(words.len() == 3 && words[1] == ":weight", "{line}");
            (Bool::new_const(words[0]), words[2].parse().unwrap())
        })
        .collect();
    (optimize.get_assertions(), soft)
}

/// `code`'s rewrite in a child with every optimize check dumped: its result, and the problems.
fn dumped(test: &str, code: &str, tag: &str) -> (ChildResult, Vec<Dumped>) {
    let dir = scratch(&format!("{tag}-dump"));
    let (result, _) = spawn(
        test,
        code,
        tag,
        "frozen",
        &[(DUMP_DIR, os(&dir)), (DUMP_CHECKS, ALL_CHECKS.into())],
    );
    assert_eq!(result.kind, "emitted", "{result:?}");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "smt2")
        })
        .collect();
    files.sort();
    let problems = files
        .into_iter()
        .map(|path| {
            let (hard, soft) = read_problem(&std::fs::read_to_string(&path).unwrap());
            let name = path.file_name().unwrap().to_string_lossy().into_owned();
            (name, hard, soft)
        })
        .collect();
    (result, problems)
}

/// P1 (RED before the encoder exists): the encoding keeps the optimum, and its assignment hands back.
/// On a problem of every operator, every assignment of the mapped variables is feasible in the
/// WCNF exactly when it is in the problem, at the same cost. On the fixtures' optimize problems (as
/// the optimize dump writes them), the written WCNF's optimum -- found by z3 over the file's clauses
/// alone -- equals z3's on the problem, and that assignment handed back is `Sat` with every mapped
/// variable read back equal and the same soft cost.
#[test]
fn r1543_2_p1_the_encoding_keeps_every_optimum_and_hands_it_back() {
    if child() {
        return;
    }
    let (hard, soft) = operator_problem();
    let wcnf = encode(&hard, &soft).expect("every operator is supported");
    assert_eq!(wcnf.units, 2);
    assert_eq!(wcnf.offset, 4, "h folds false");
    assert_eq!(wcnf.originals.len(), 6);
    let (clauses, wsoft) = written(&wcnf);
    let vars = usize::try_from(wcnf.vars).unwrap();
    let solver = Solver::new();
    for assertion in &hard {
        solver.assert(assertion);
    }
    let mut feasible = Vec::new();
    for mask in 0u32..1 << wcnf.originals.len() {
        let fixed: Vec<(usize, bool)> = wcnf
            .originals
            .iter()
            .enumerate()
            .map(|(k, (_, at))| (usize::try_from(*at - 1).unwrap(), (mask >> k) & 1 == 1))
            .collect();
        let assumptions: Vec<Bool> = wcnf
            .originals
            .iter()
            .zip(&fixed)
            .map(|((symbol, _), &(_, value))| if value { symbol.clone() } else { !symbol })
            .collect();
        match (
            solver.check_assumptions(&assumptions),
            propagate(vars, &clauses, &fixed),
        ) {
            (SatResult::Sat, Some(values)) => {
                let cost = soft_cost(&solver.get_model().unwrap(), &soft);
                assert_eq!(wcnf_cost(&wcnf, &wsoft, &values), cost, "mask {mask:06b}");
                feasible.push(cost);
            }
            (SatResult::Unsat, None) => {}
            (original, encoded) => panic!(
                "mask {mask:06b}: the problem {original:?}, the WCNF {}",
                encoded.is_some()
            ),
        }
    }
    feasible.sort_unstable();
    assert_eq!(feasible, [9, 14]);
    assert_eq!(z3_optimum(&hard, &soft), Some(9));
    differential("operators", &hard, &soft);

    let name = test("r1543_2_p1_the_encoding_keeps_every_optimum_and_hands_it_back");
    let mut problems = 0;
    for (tag, code) in [("cascade", CASCADE_TIE), ("overlap", OVERLAP)] {
        let (_, dumps) = dumped(&name, code, &format!("r1543-p1-{tag}"));
        for (file, hard, soft) in &dumps {
            assert!(!soft.is_empty(), "{tag} {file}: no objective");
            differential(&format!("{tag} {file}"), hard, soft);
            problems += 1;
        }
    }
    assert!(problems >= 2, "{problems} problems");
}

/// The operator problem's optimal answer, as a solver prints it: the `o` value and the `v` string.
fn answer(wcnf: &Wcnf) -> (u64, String) {
    let (clauses, wsoft) = written(wcnf);
    let values =
        solve_written(usize::try_from(wcnf.vars).unwrap(), &clauses, &wsoft).expect("satisfiable");
    let o = wcnf_cost(wcnf, &wsoft, &values) - wcnf.offset;
    let bits = values.iter().map(|&v| if v { '1' } else { '0' }).collect();
    (o, bits)
}

/// A shell script under `dir`, run as `/bin/sh <script> {wcnf}` (so it is read, never executed:
/// no "text file busy" beside another test's fork).
fn script(dir: &Path, name: &str, body: &str) -> String {
    let path = dir.join(format!("{name}.sh"));
    std::fs::write(&path, format!("{body}\n")).unwrap();
    format!("/bin/sh {} {{wcnf}}", path.display())
}

/// The P2 / P4 cases on the operator problem: `(tag, run line, limit, the hand-back solver's own
/// assertion, synced, the scope's extra assertion, expected)`; `Ok(())` is a handed-back model.
struct Case {
    tag: &'static str,
    line: String,
    limit: Duration,
    base: Option<Bool>,
    synced: Option<usize>,
    extra: Option<Bool>,
    dir: Option<PathBuf>,
    expected: Result<(), Cause>,
}

fn cases(dir: &Path, wcnf: &Wcnf) -> Vec<Case> {
    let (o, bits) = answer(wcnf);
    let found = format!("echo 'o {o}'; echo 's OPTIMUM FOUND'; echo 'v {bits}'");
    let present = "test -f \"$1\" || { echo 'no file' >&2; exit 3; }";
    let case = |tag: &'static str, body: &str, expected: Result<(), Cause>| Case {
        tag,
        line: script(dir, tag, body),
        limit: Duration::from_secs(60),
        base: None,
        synced: None,
        extra: None,
        dir: None,
        expected,
    };
    let vars = usize::try_from(wcnf.vars).unwrap();
    let not_a_dir = dir.join("a-file");
    std::fs::write(&not_a_dir, "").unwrap();
    vec![
        case(
            "found",
            &format!("{present}; echo 'c test'; {found}"),
            Ok(()),
        ),
        // R1543-4 (2): the `s` line decides, not the exit code (30 is MaxSAT's "optimum").
        case("found-exit-30", &format!("{found}; exit 30"), Ok(())),
        case(
            "unsat",
            "echo 's UNSATISFIABLE'",
            Err(Cause::Status("UNSATISFIABLE".into())),
        ),
        case(
            "no-s",
            "echo 'c nothing'",
            Err(Cause::Status("none".into())),
        ),
        case(
            "unknown",
            "echo 's UNKNOWN'",
            Err(Cause::Status("UNKNOWN".into())),
        ),
        case(
            "satisfiable",
            &format!("echo 'o {o}'; echo 's SATISFIABLE'; echo 'v {bits}'"),
            Err(Cause::Status("SATISFIABLE".into())),
        ),
        Case {
            limit: Duration::from_secs(1),
            ..case("limit", "exec sleep 30", Err(Cause::Limit))
        },
        case("signal", "kill -9 $$", Err(Cause::Signal(9))),
        case(
            "short-v",
            &format!("echo 'o {o}'; echo 's OPTIMUM FOUND'; echo 'v 0'"),
            Err(Cause::Values { got: 1, want: vars }),
        ),
        case(
            "no-o",
            &format!("echo 's OPTIMUM FOUND'; echo 'v {bits}'"),
            Err(Cause::NoCost),
        ),
        // R1543-4 (5a): an `o` line the handed-back model does not cost.
        case(
            "cost",
            &format!(
                "echo 'o {}'; echo 's OPTIMUM FOUND'; echo 'v {bits}'",
                o + 1
            ),
            Err(Cause::Cost {
                model: o + wcnf.offset,
                line: o + 1 + wcnf.offset,
            }),
        ),
        Case {
            line: "/nonexistent/r1543-2-solver {wcnf}".to_owned(),
            ..case("spawn", "", Err(Cause::Spawn(String::new())))
        },
        Case {
            dir: Some(not_a_dir.join("sub")),
            ..case("write", &found, Err(Cause::Write(String::new())))
        },
        Case {
            extra: Some(Int::new_const("r1543_2_p2_n").eq(Int::from_i64(1))),
            ..case(
                "unsupported",
                &found,
                Err(Cause::Unsupported(String::new())),
            )
        },
        Case {
            extra: Some(Bool::from_bool(false)),
            ..case("hard-false", &found, Err(Cause::HardFalse))
        },
        // The optimum has a = false; a hand-back solver that holds a cannot take it.
        Case {
            base: Some(Bool::new_const("r1543_2_p1_a")),
            ..case("handback", &found, Err(Cause::HandBack("unsat".into())))
        },
        Case {
            synced: Some(usize::MAX),
            ..case("sync", &found, Err(Cause::Sync))
        },
    ]
}

/// One case through [`attempt`]: its result, its wall, and whether its directory is gone after.
fn run(
    case: &Case,
    dir: &Path,
    hard: &[Bool],
    soft: &[(Bool, u64)],
) -> (Result<Model, Cause>, Duration, bool) {
    let mut scope = hard.to_vec();
    scope.extend(case.extra.clone());
    let solver = Solver::new();
    if let Some(base) = &case.base {
        solver.assert(base);
    }
    let check = Check {
        scope: &scope,
        soft,
        solver: &solver,
        synced: case.synced.unwrap_or(0),
    };
    let dir = case.dir.clone().unwrap_or_else(|| dir.join(case.tag));
    let line = RunLine::parse(&case.line).expect("a run line");
    let started = Instant::now();
    let result = attempt(&line, &dir, case.limit, &check, &mut Report::default());
    (result, started.elapsed(), !dir.exists())
}

/// The same cause, ignoring the text of an I/O error or a term kind.
fn same_cause(found: &Cause, expected: &Cause) -> bool {
    match (found, expected) {
        (Cause::Spawn(_), Cause::Spawn(_))
        | (Cause::Write(_), Cause::Write(_))
        | (Cause::Unsupported(_), Cause::Unsupported(_)) => true,
        _ => found == expected,
    }
}

/// P2: every fallback cause of main 346 §3 step 5 (and R1543-4's (2) and (5a)) is named, and at the
/// hook it leaves the round's model z3's: the same decision as without the switch, with a
/// `maxsat:fallback` line naming the cause and no `maxsat:check` line.
#[test]
fn r1543_2_p2_every_fallback_cause_leaves_the_check_to_z3() {
    if child() {
        return;
    }
    let dir = scratch("r1543-p2");
    let (hard, soft) = operator_problem();
    let wcnf = encode(&hard, &soft).expect("supported");
    for case in cases(&dir, &wcnf) {
        let (result, wall, _) = run(&case, &dir, &hard, &soft);
        match (&result, &case.expected) {
            (Ok(model), Ok(())) => assert_eq!(soft_cost(model, &soft), 9, "{}", case.tag),
            (Err(found), Err(expected)) => {
                assert!(same_cause(found, expected), "{}: {found:?}", case.tag);
            }
            _ => panic!("{}: {:?}", case.tag, result.as_ref().map(|_| ())),
        }
        if case.expected == Err(Cause::Limit) {
            assert!(wall < Duration::from_secs(10), "{}: {wall:?}", case.tag);
        }
    }

    let name = test("r1543_2_p2_every_fallback_cause_leaves_the_check_to_z3");
    let (off, _) = spawn(&name, CASCADE_TIE, "r1543-p2-off", "frozen", &[]);
    assert_eq!(off.kind, "emitted", "{off:?}");
    for (tag, body, cause) in [
        (
            "hook-unsat",
            "echo 's UNSATISFIABLE'",
            "status:UNSATISFIABLE",
        ),
        ("hook-signal", "kill -9 $$", "signal:9"),
    ] {
        let line = script(&dir, tag, body);
        let (on, err) = spawn(
            &name,
            CASCADE_TIE,
            &format!("r1543-p2-{tag}"),
            "frozen",
            &[(SWITCH, line.into()), ("CRAT_BO_PHASE_LOG", "on".into())],
        );
        assert_eq!(on.decision(), off.decision(), "{tag}");
        let fallbacks = lines(&err, "maxsat:fallback");
        let named = format!("cause={cause} ");
        assert!(
            !fallbacks.is_empty() && fallbacks.iter().all(|line| line.contains(&named)),
            "{tag}:\n{err}"
        );
        assert!(lines(&err, "maxsat:check").is_empty(), "{tag}:\n{err}");
    }
}

/// P3: with the switch unset nothing starts and nothing is written: no `maxsat:` line with the log
/// on, no `crat-maxsat-*` entry under the child's temporary directory, and the result equal to the
/// log-off run's. An empty or blank value is unset.
#[test]
fn r1543_2_p3_unset_starts_no_process_and_writes_no_file() {
    if child() {
        return;
    }
    assert!(RunLine::parse("").is_none());
    assert!(RunLine::parse(" \t ").is_none());
    let name = test("r1543_2_p3_unset_starts_no_process_and_writes_no_file");
    let tmp = scratch("r1543-p3-tmp");
    let (on, on_err) = spawn(
        &name,
        CASCADE_TIE,
        "r1543-p3-on",
        "frozen",
        &[("CRAT_BO_PHASE_LOG", "on".into()), ("TMPDIR", os(&tmp))],
    );
    let (off, off_err) = spawn(&name, CASCADE_TIE, "r1543-p3-off", "frozen", &[]);
    assert_eq!(on.kind, "emitted", "{on:?}");
    assert_eq!(on, off);
    assert!(on_err.contains("[bo-phase]"), "{on_err}");
    assert!(!on_err.contains("maxsat:"), "{on_err}");
    assert!(!off_err.contains("maxsat:"), "{off_err}");
    let left: Vec<String> = std::fs::read_dir(&tmp)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .filter(|name| name.starts_with("crat-maxsat-"))
        .collect();
    assert!(left.is_empty(), "{left:?}");
}

/// P4: the WCNF file is gone after every check -- on the handed-back path (the script checks the
/// file is there while it runs) and on every fallback -- and its directory with it.
#[test]
fn r1543_2_p4_the_file_is_gone_after_every_check() {
    let dir = scratch("r1543-p4");
    let (hard, soft) = operator_problem();
    let wcnf = encode(&hard, &soft).expect("supported");
    let mut handed_back = 0;
    for case in cases(&dir, &wcnf) {
        let (result, _, gone) = run(&case, &dir, &hard, &soft);
        handed_back += usize::from(result.is_ok());
        assert!(gone, "{}: {}", case.tag, dir.join(case.tag).display());
    }
    assert_eq!(handed_back, 2, "found, found-exit-30");
}

/// The problem's optimum is unique over its soft terms: with z3's optimal assignment of them
/// blocked, no assignment reaches the same cost. An unsatisfiable check has nothing to compare.
fn assert_unique(file: &str, hard: &[Bool], soft: &[(Bool, u64)]) {
    let optimize = Optimize::new();
    for assertion in hard {
        optimize.assert(assertion);
    }
    for (term, weight) in soft {
        optimize.assert_soft(term, *weight, None);
    }
    match optimize.check(&[]) {
        SatResult::Sat => {}
        SatResult::Unsat => return,
        SatResult::Unknown => panic!("{file}: unknown"),
    }
    let model = optimize.get_model().unwrap();
    let cost = soft_cost(&model, soft);
    let same: Vec<Bool> = soft
        .iter()
        .map(|(term, _)| {
            if holds(&model, term) {
                term.clone()
            } else {
                !term
            }
        })
        .collect();
    optimize.push();
    optimize.assert(&!Bool::and(&same));
    match optimize.check(&[]) {
        SatResult::Unsat => {}
        SatResult::Sat => assert!(
            soft_cost(&optimize.get_model().unwrap(), soft) > cost,
            "{file}: a second optimum"
        ),
        SatResult::Unknown => panic!("{file}: unknown"),
    }
    optimize.pop();
}

/// P5 (the one switch-on test; the gate runs it by name with `CRAT_BO_MAXSAT_CMD` set to the archived
/// UWrMaxSat line of main 346 §1, its binary's sha256 checked first): on a fixture whose every
/// dumped optimum is unique, the external path emits the z3 run's model, every check handed back
/// (a fallback only where z3 too finds the check unsatisfiable).
#[test]
#[ignore = "needs the solver CRAT_BO_MAXSAT_CMD names; the gate runs it by name"]
fn r1543_2_p5_uwrmaxsat_on_a_fixture() {
    if child() {
        return;
    }
    let line = std::env::var(SWITCH).expect("CRAT_BO_MAXSAT_CMD names the solver");
    let name = test("r1543_2_p5_uwrmaxsat_on_a_fixture");
    let (z3_run, dumps) = dumped(&name, UNIQUE, "r1543-p5-z3");
    assert!(!dumps.is_empty(), "no optimize check dumped");
    for (file, hard, soft) in &dumps {
        assert_unique(file, hard, soft);
    }
    let (external, err) = spawn(
        &name,
        UNIQUE,
        "r1543-p5-ext",
        "frozen",
        &[(SWITCH, line.into()), ("CRAT_BO_PHASE_LOG", "on".into())],
    );
    assert_eq!(external.kind, "emitted", "{external:?}");
    assert_eq!(external.model_sha256, z3_run.model_sha256, "{err}");
    let checks = lines(&err, "maxsat:check");
    assert!(
        !checks.is_empty() && checks.iter().all(|line| line.contains(" status=OPTIMUM ")),
        "{err}"
    );
    for line in lines(&err, "maxsat:fallback") {
        assert!(
            line.contains("cause=hard-false ") || line.contains("cause=status:UNSATISFIABLE "),
            "{line}"
        );
    }
}
