//! R1543-2 Part 2 (main 346 §4; the seat's R1543-4): the external MaxSAT path's witnesses P1–P5;
//! P6–P9 come from the review of 9595db605. R1555-2 (main 357): no z3 after the answer -- P1, P2
//! amended (the circuit against z3's own evaluation, z3 the oracle in tests only); P10–P12 new.
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
use crate::maxsat::{Answer, Cause, Check, Report, RunLine, Wcnf, accept, attempt, encode};

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

/// The weight of the soft terms `model` does not make true (z3 as the tests' oracle).
fn soft_cost(model: &Model, soft: &[(Bool, u64)]) -> u64 {
    soft.iter()
        .filter(|(term, _)| !holds(model, term))
        .map(|(_, weight)| *weight)
        .sum()
}

/// The weight of the soft terms an accepted answer leaves false (crat's own values).
fn answer_cost(answer: &Answer, soft: &[(Bool, u64)]) -> u64 {
    answer
        .soft
        .iter()
        .zip(soft)
        .filter(|(value, _)| !**value)
        .map(|(_, (_, weight))| *weight)
        .sum()
}

/// The circuit's values of the hard and soft roots under the WCNF values `values`.
fn circuit_roots(wcnf: &Wcnf, values: &[bool]) -> (Vec<bool>, Vec<bool>) {
    let nodes = wcnf.circuit.values(values);
    let at = |roots: &[u32]| roots.iter().map(|&root| nodes[root as usize]).collect();
    (at(&wcnf.circuit.hard), at(&wcnf.circuit.soft))
}

fn index(lit: i32) -> usize {
    usize::try_from(lit.unsigned_abs()).unwrap() - 1
}

fn true_under(values: &[bool], lit: i32) -> bool {
    values[index(lit)] == (lit > 0)
}

/// The highest index the written file holds: a 2022+ solver's variable count (the format has no
/// header).
fn top_written(wcnf: &Wcnf) -> usize {
    let (clauses, wsoft) = written(wcnf);
    clauses
        .iter()
        .flatten()
        .chain(wsoft.iter().map(|(_, lit)| lit))
        .map(|&lit| index(lit) + 1)
        .max()
        .unwrap_or(0)
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
/// is accepted by the circuit (R1555-2) at the same soft cost; z3's own model of that assignment (the
/// oracle) gives every hard and soft term the circuit's value.
fn differential(name: &str, hard: &[Bool], soft: &[(Bool, u64)]) {
    let optimum = z3_optimum(hard, soft);
    let wcnf = match encode(hard, soft, &[]) {
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
    let answer = accept(&wcnf, soft, cost - wcnf.offset, &values)
        .unwrap_or_else(|cause| panic!("{name}: {cause:?}"));
    assert_eq!(
        answer_cost(&answer, soft),
        cost,
        "{name}: the answer's cost"
    );
    let oracle = Solver::new();
    for assertion in hard {
        oracle.assert(assertion);
    }
    let fixed: Vec<Bool> = wcnf
        .originals
        .iter()
        .map(|(symbol, at)| {
            if values[usize::try_from(*at - 1).unwrap()] {
                symbol.clone()
            } else {
                !symbol
            }
        })
        .collect();
    assert_eq!(oracle.check_assumptions(&fixed), SatResult::Sat, "{name}");
    let model = oracle.get_model().unwrap();
    let (hard_values, soft_values) = circuit_roots(&wcnf, &values);
    for (term, value) in hard.iter().zip(&hard_values) {
        assert_eq!(holds(&model, term), *value, "{name}: {term:?}");
    }
    for ((term, _), value) in soft.iter().zip(&soft_values) {
        assert_eq!(holds(&model, term), *value, "{name}: soft {term:?}");
    }
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

/// P1 (RED before the encoder exists): the encoding keeps the optimum, and its assignment is accepted
/// (R1555-2: the circuit, every root equal to z3's own evaluation on every assignment).
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
    let wcnf = encode(&hard, &soft, &[]).expect("every operator is supported");
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
                let model = solver.get_model().unwrap();
                let cost = soft_cost(&model, &soft);
                assert_eq!(wcnf_cost(&wcnf, &wsoft, &values), cost, "mask {mask:06b}");
                let (hard_values, soft_values) = circuit_roots(&wcnf, &values);
                assert!(hard_values.iter().all(|&v| v), "mask {mask:06b}");
                for ((term, _), value) in soft.iter().zip(&soft_values) {
                    assert_eq!(holds(&model, term), *value, "mask {mask:06b}: {term:?}");
                }
                feasible.push(cost);
            }
            (SatResult::Unsat, None) => {
                // R1555-2: every symbol is mapped or unit-fixed, so an infeasible assignment
                // leaves a hard root false in the circuit.
                let mut values = vec![false; vars];
                for &(at, value) in &fixed {
                    values[at] = value;
                }
                let (hard_values, _) = circuit_roots(&wcnf, &values);
                assert!(hard_values.iter().any(|&v| !v), "mask {mask:06b}");
            }
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

/// The P2 / P4 cases on the operator problem: `(tag, run line, limit, the scope's extra assertion,
/// expected)`; `Ok(())` is an accepted answer.
struct Case {
    tag: &'static str,
    line: String,
    limit: Duration,
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
        extra: None,
        dir: None,
        expected,
    };
    let top = top_written(wcnf);
    // R1555-2: the optimum with `a` flipped (a1 b0 c1 d1 e1 f0) is no feasible assignment, so a
    // hard root of the circuit is false under it.
    let a = Bool::new_const("r1543_2_p1_a");
    let (_, a_at) = wcnf
        .originals
        .iter()
        .find(|(symbol, _)| *symbol == a)
        .unwrap();
    let mut flipped: Vec<char> = bits.chars().collect();
    let at = usize::try_from(*a_at - 1).unwrap();
    flipped[at] = if flipped[at] == '1' { '0' } else { '1' };
    let flipped: String = flipped.into_iter().collect();
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
            Err(Cause::Values { got: 1, want: top }),
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
        // R1555-2: the circuit refuses an answer that breaks a hard assertion.
        case(
            "hard-eval",
            &format!("echo 'o {o}'; echo 's OPTIMUM FOUND'; echo 'v {flipped}'"),
            Err(Cause::HardEval),
        ),
    ]
}

/// One case through [`attempt`]: its result, its wall, and whether its directory is gone after.
fn run(
    case: &Case,
    dir: &Path,
    hard: &[Bool],
    soft: &[(Bool, u64)],
) -> (Result<Answer, Cause>, Duration, bool) {
    let mut scope = hard.to_vec();
    scope.extend(case.extra.clone());
    let check = Check {
        scope: &scope,
        soft,
        reads: &[],
        started: Instant::now(),
        prepare: 0.0,
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
    let wcnf = encode(&hard, &soft, &[]).expect("supported");
    for case in cases(&dir, &wcnf) {
        let (result, wall, _) = run(&case, &dir, &hard, &soft);
        match (&result, &case.expected) {
            (Ok(answer), Ok(())) => assert_eq!(answer_cost(answer, &soft), 9, "{}", case.tag),
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
    let wcnf = encode(&hard, &soft, &[]).expect("supported");
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
    // R1555-2 (main 357 §5): the pieces of the path with no z3 after the answer.
    for line in &checks {
        check_fields(line);
    }
    for line in lines(&err, "maxsat:fallback") {
        assert!(
            line.contains("cause=hard-false ") || line.contains("cause=status:UNSATISFIABLE "),
            "{line}"
        );
    }
}

/// P6 (the review of 9595db605, defect 1): on a fallback the check's wall -- the input of the budget
/// predicate for an `Unknown` -- is z3's check alone, as today. A run line that sleeps 2 s and
/// prints no `s` line makes every optimize check of the fixture fall back; the optimize dump's
/// `check_wall_s` of each stays under 1 s.
#[test]
fn r1543_2_p6_a_fallback_check_wall_is_z3s_alone() {
    if child() {
        return;
    }
    let name = test("r1543_2_p6_a_fallback_check_wall_is_z3s_alone");
    let dir = scratch("r1543-p6");
    let dump = scratch("r1543-p6-dump");
    let line = script(&dir, "slow-no-s", "sleep 2");
    let (on, err) = spawn(
        &name,
        CASCADE_TIE,
        "r1543-p6-on",
        "frozen",
        &[
            (SWITCH, line.into()),
            ("CRAT_BO_PHASE_LOG", "on".into()),
            (DUMP_DIR, os(&dump)),
            (DUMP_CHECKS, ALL_CHECKS.into()),
        ],
    );
    assert_eq!(on.kind, "emitted", "{on:?}");
    let fallbacks = lines(&err, "maxsat:fallback");
    assert!(
        !fallbacks.is_empty()
            && fallbacks
                .iter()
                .all(|line| line.contains("cause=status:none ")),
        "{err}"
    );
    let index = std::fs::read_to_string(dump.join("index.tsv")).unwrap();
    let mut rows = index.lines();
    let head: Vec<&str> = rows.next().unwrap().split('\t').collect();
    let at = head
        .iter()
        .position(|column| *column == "check_wall_s")
        .unwrap();
    let walls: Vec<f64> = rows
        .map(|row| row.split('\t').nth(at).unwrap().parse().unwrap())
        .collect();
    assert!(walls.len() >= fallbacks.len(), "{index}");
    assert!(walls.iter().all(|&wall| wall < 1.0), "{index}");
}

/// P7 (the review, defect 2): the limit holds when the run line forks. The shell runs `sleep 30` as
/// its own child (not by `exec`), so the pipes stay open after the shell is killed at the limit; the
/// check still ends near the limit, with `Limit`, and its file is gone.
#[test]
fn r1543_2_p7_the_limit_holds_when_the_line_forks() {
    let dir = scratch("r1543-p7");
    let (hard, soft) = operator_problem();
    let case = Case {
        tag: "limit-fork",
        line: script(&dir, "limit-fork", "sleep 30; true"),
        limit: Duration::from_secs(1),
        extra: None,
        dir: None,
        expected: Err(Cause::Limit),
    };
    let (result, wall, gone) = run(&case, &dir, &hard, &soft);
    assert!(
        matches!(result, Err(Cause::Limit)),
        "{:?}",
        result.as_ref().map(|_| ())
    );
    assert!(wall < Duration::from_secs(10), "{wall:?}");
    assert!(gone);
}

/// P8 (the review, defect 3): an index the encoder handed out but wrote in no clause is not asked of
/// the solver. `or(c, true)` gives `c` the highest index and folds away, so a 2022+ solver reads two
/// variables from the file and answers two values; in either `v` form the answer is handed back
/// (`c`, in no clause, takes false).
#[test]
fn r1543_2_p8_an_unwritten_top_index_is_not_asked_for() {
    let dir = scratch("r1543-p8");
    let a = Bool::new_const("r1543_2_p8_a");
    let b = Bool::new_const("r1543_2_p8_b");
    let c = Bool::new_const("r1543_2_p8_c");
    let hard = vec![
        Bool::or(&[a.clone(), b.clone()]),
        Bool::or(&[c, Bool::from_bool(true)]),
    ];
    let soft = vec![(a, 1), (b, 2)];
    let wcnf = encode(&hard, &soft, &[]).expect("supported");
    assert_eq!(
        (wcnf.vars, top_written(&wcnf)),
        (3, 2),
        "c's index is the highest and unwritten"
    );
    for (tag, values) in [("bits", "11"), ("lits", "1 2")] {
        let case = Case {
            tag,
            line: script(
                &dir,
                tag,
                &format!("echo 'o 0'; echo 's OPTIMUM FOUND'; echo 'v {values}'"),
            ),
            limit: Duration::from_secs(60),
            extra: None,
            dir: None,
            expected: Ok(()),
        };
        let (result, _, gone) = run(&case, &dir, &hard, &soft);
        let answer = result.unwrap_or_else(|cause| panic!("{tag}: {cause:?}"));
        assert_eq!(answer_cost(&answer, &soft), 0, "{tag}");
        assert!(gone, "{tag}");
    }
}

/// P9 (the review, note 6; R1547-3 §4): crat writes and removes only inside a directory it made for
/// the check. A name already taken -- here a symlink to another directory, planted where the
/// check's directory goes -- is refused (`Write`), and nothing under the symlink's target is
/// written or removed.
#[cfg(unix)]
#[test]
fn r1543_2_p9_a_planted_directory_is_refused() {
    let dir = scratch("r1543-p9");
    let target = dir.join("target");
    std::fs::create_dir(&target).unwrap();
    std::fs::write(target.join("keep"), "keep").unwrap();
    std::os::unix::fs::symlink(&target, dir.join("planted")).unwrap();
    let (hard, soft) = operator_problem();
    let wcnf = encode(&hard, &soft, &[]).expect("supported");
    let (o, bits) = answer(&wcnf);
    let case = Case {
        tag: "planted",
        line: script(
            &dir,
            "planted",
            &format!("echo 'o {o}'; echo 's OPTIMUM FOUND'; echo 'v {bits}'"),
        ),
        limit: Duration::from_secs(60),
        extra: None,
        dir: None,
        expected: Err(Cause::Write(String::new())),
    };
    let (result, _, _) = run(&case, &dir, &hard, &soft);
    assert!(
        matches!(result, Err(Cause::Write(_))),
        "{:?}",
        result.as_ref().map(|_| ())
    );
    let mut left: Vec<String> = std::fs::read_dir(&target)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    left.sort();
    assert_eq!(left, ["keep"]);
    assert!(
        dir.join("planted")
            .symlink_metadata()
            .unwrap()
            .file_type()
            .is_symlink()
    );
}

/// R1555-2 (main 357 §5): a `maxsat:check end` line carries the path's pieces and none of the z3
/// hand-back's.
fn check_fields(line: &str) {
    for field in [
        " prepare=",
        " encode=",
        " circuit=",
        " write=",
        " solve=",
        " eval=",
        " readers=",
        " total=",
        " nodes=",
        " reads=",
    ] {
        assert!(line.contains(field), "{field}: {line}");
    }
    for gone in ["handback=", " model="] {
        assert!(!line.contains(gone), "{gone}: {line}");
    }
}

/// P10 (R1555-2, main 357 §2 / §5 / §6): the circuit's leaves and the line. A symbol fixed by a
/// top-level unit and used elsewhere reads the unit's value; an index in no clause reads false; a
/// symbol the encoder never saw (a reader's) reads false, z3's model completion; a reader's
/// compound term is evaluated; a reader's term of an unknown kind is a typed `Unsupported`, before
/// any process starts. The fields of the line are the path's. `maxsat.rs` holds no z3 solver,
/// model or evaluation (the ratchet).
#[test]
fn r1555_2_p10_the_circuit_reads_units_unseen_symbols_and_readers() {
    let dir = scratch("r1555-p10");
    let a = Bool::new_const("r1555_2_p10_a");
    let b = Bool::new_const("r1555_2_p10_b");
    let c = Bool::new_const("r1555_2_p10_c");
    let d = Bool::new_const("r1555_2_p10_d");
    let hard = vec![
        a.clone(),
        Bool::or(&[!&a, b.clone()]),
        Bool::or(&[c.clone(), Bool::from_bool(true)]),
    ];
    // `c` is in no soft term, so its index is above the file's highest.
    let soft = vec![(b.clone(), 1), (a.clone(), 4)];
    let reads = vec![
        d.clone(),
        Bool::and(&[a.clone(), b.clone()]),
        c.clone(),
        !&d,
    ];
    let wcnf = encode(&hard, &soft, &reads).expect("supported");
    assert_eq!(wcnf.units, 1);
    assert_eq!((wcnf.vars, top_written(&wcnf)), (2, 1), "b written, c not");
    let line = RunLine::parse(&script(
        &dir,
        "units",
        "echo 'o 0'; echo 's OPTIMUM FOUND'; echo 'v 1'",
    ))
    .unwrap();
    let check = Check {
        scope: &hard,
        soft: &soft,
        reads: &reads,
        started: Instant::now(),
        prepare: 0.0,
    };
    let mut report = Report::default();
    let answer = attempt(
        &line,
        &dir.join("units"),
        Duration::from_secs(60),
        &check,
        &mut report,
    )
    .unwrap_or_else(|cause| panic!("{cause:?}"));
    assert_eq!(
        answer.soft,
        [true, true],
        "b from the answer, a from its unit"
    );
    assert_eq!(answer.reads, [false, true, false, true]);
    assert_eq!(answer_cost(&answer, &soft), 0);
    let fields = format!(" {}", report.fields());
    check_fields(&fields);
    assert!(fields.contains(" reads=4 "), "{fields}");

    let unknown = vec![Bool::or(&[
        a.clone(),
        Int::new_const("r1555_2_p10_n").eq(Int::from_i64(1)),
    ])];
    let check = Check {
        scope: &hard,
        soft: &soft,
        reads: &unknown,
        started: Instant::now(),
        prepare: 0.0,
    };
    let result = attempt(
        &line,
        &dir.join("unknown"),
        Duration::from_secs(60),
        &check,
        &mut Report::default(),
    );
    assert!(
        matches!(result, Err(Cause::Unsupported(_))),
        "{:?}",
        result.as_ref().map(|_| ())
    );
    assert!(!dir.join("unknown").exists(), "no file before a known kind");

    let source = include_str!("../maxsat.rs");
    for word in [
        "Solver",
        "Model",
        "SatResult",
        ".eval(",
        "push()",
        "pop(1)",
        "check_assumptions",
        "HardLoopSolver",
    ] {
        assert!(!source.contains(word), "maxsat.rs holds {word:?}");
    }
}

const TEST_SOLVER_FILE: &str = "R1555_2_TEST_SOLVER_WCNF";

/// R1555-2, test-only: a MaxSAT solver for P11, z3 over the file's clauses (z3 as the tests'
/// oracle; the path under test calls no z3 after the answer). It runs as the run line's process:
/// the file in `R1555_2_TEST_SOLVER_WCNF`, the answer on stdout in the 2022+ format. Without the
/// variable it does nothing.
#[test]
#[ignore = "the test solver of r1555_2_p11; run by its run line"]
fn r1555_2_test_solver() {
    let Some(file) = std::env::var_os(TEST_SOLVER_FILE) else {
        return;
    };
    let text = std::fs::read_to_string(file).unwrap();
    let mut hard = Vec::new();
    let mut soft = Vec::new();
    for line in text.lines().filter(|line| !line.starts_with('c')) {
        let mut words = line.split_whitespace();
        let head = words.next().expect("a word");
        let mut lits: Vec<i32> = words.map(|word| word.parse().unwrap()).collect();
        assert_eq!(lits.pop(), Some(0), "{line}");
        if head == "h" {
            hard.push(lits);
        } else {
            soft.push((head.parse::<u64>().unwrap(), lits[0]));
        }
    }
    let top = hard
        .iter()
        .flatten()
        .chain(soft.iter().map(|(_, lit)| lit))
        .map(|&lit| index(lit) + 1)
        .max()
        .unwrap_or(0);
    match solve_written(top, &hard, &soft) {
        Some(values) => {
            let o: u64 = soft
                .iter()
                .filter(|(_, lit)| !true_under(&values, *lit))
                .map(|(weight, _)| *weight)
                .sum();
            let bits: String = values.iter().map(|&v| if v { '1' } else { '0' }).collect();
            // The leading newline: libtest prints `test … ` before the output, on the same line.
            println!("\no {o}\ns OPTIMUM FOUND\nv {bits}");
        }
        None => println!("\ns UNSATISFIABLE"),
    }
}

/// The run line of the test solver: a script that runs this test binary's `r1555_2_test_solver`.
fn test_solver_line(dir: &Path) -> String {
    let exe = std::env::current_exe().unwrap();
    script(
        dir,
        "test-solver",
        &format!(
            "exec env {TEST_SOLVER_FILE}=\"$1\" '{}' bo_rewriter::maxsat_tests::r1555_2_test_solver --exact --ignored --nocapture --test-threads=1",
            exe.display()
        ),
    )
}

/// P11 (R1555-2, main 357 §3 / §6): the whole rewrite with the switch on and the test solver, on
/// P5's fixture (every dumped optimum unique) and on the cascade fixture: every check is accepted
/// (`OPTIMUM`, no fallback), the line carries the path's pieces, the readers' terms were replayed
/// (`reads=` above 0 on some check), and on the unique fixture the emitted model is the z3 run's.
#[test]
fn r1555_2_p11_the_readers_replay_to_the_z3_runs_model() {
    if child() {
        return;
    }
    let name = test("r1555_2_p11_the_readers_replay_to_the_z3_runs_model");
    let dir = scratch("r1555-p11");
    let line = test_solver_line(&dir);
    let mut replayed = 0;
    for (tag, code) in [("unique", UNIQUE), ("cascade", CASCADE_TIE)] {
        let (off, _) = spawn(&name, code, &format!("r1555-p11-{tag}-off"), "frozen", &[]);
        let (on, err) = spawn(
            &name,
            code,
            &format!("r1555-p11-{tag}-on"),
            "frozen",
            &[
                (SWITCH, line.clone().into()),
                ("CRAT_BO_PHASE_LOG", "on".into()),
            ],
        );
        assert_eq!(on.kind, "emitted", "{tag}: {on:?}");
        assert!(lines(&err, "maxsat:fallback").is_empty(), "{tag}:\n{err}");
        // R1556-2 (main 358 H1): every relaxation is the external solver's, with its fields.
        assert!(
            lines(&err, "maxsat:relax-fallback").is_empty(),
            "{tag}:\n{err}"
        );
        let relaxations = lines(&err, "maxsat:relax");
        assert!(!relaxations.is_empty(), "{tag}:\n{err}");
        for line in &relaxations {
            assert!(line.contains(" status=OPTIMUM "), "{line}");
            assert!(
                line.contains(" selectors=") && line.contains(" dropped="),
                "{line}"
            );
            check_fields(line);
        }
        let checks = lines(&err, "maxsat:check");
        assert!(!checks.is_empty(), "{tag}:\n{err}");
        for line in &checks {
            assert!(line.contains(" status=OPTIMUM "), "{line}");
            check_fields(line);
            replayed += usize::from(!line.contains(" reads=0 "));
        }
        if tag == "unique" {
            assert_eq!(on.model_sha256, off.model_sha256, "{tag}:\n{err}");
            assert_eq!(on.decision(), off.decision(), "{tag}");
        }
    }
    assert!(replayed > 0, "no check had a reader's term");
}

/// P12's synthetic problem (R1555-2 §2(ii)): r470's first check had 1,925,748 WCNF variables (about
/// 1.77 M mapped), `units=2871041`, `hard=4908652` clauses and 295,335 soft terms written.
const P12_SYMBOLS: usize = 1_770_000;
const P12_UNITS: usize = 2_871_041;
const P12_COMPOUND: usize = 2_900_000;
const P12_SLOTS: usize = 147_669;
const P12_READS: usize = 150_000;

fn p12_hash(i: usize, salt: u64) -> usize {
    let x =
        (i as u64 ^ salt.wrapping_mul(0x9E37_79B9_7F4A_7C15)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    usize::try_from((x ^ (x >> 31)) >> 1).unwrap()
}

/// P12's hard part (R1555-2 §2(ii)): P12_SYMBOLS symbols with their reference values, P12_UNITS unit
/// assertions over their own symbols (`u_k` true when `k % 3 == 0`), and P12_COMPOUND compound
/// assertions of P02's shapes, each true under the reference values. Symbols are named by `tag`.
fn p12_hard(tag: &str) -> (Vec<Bool>, Vec<bool>, Vec<Bool>, Vec<Bool>) {
    let s: Vec<Bool> = (0..P12_SYMBOLS)
        .map(|k| Bool::new_const(format!("r1555_2_{tag}_s{k}")))
        .collect();
    let value: Vec<bool> = (0..P12_SYMBOLS).map(|k| p12_hash(k, 7) % 5 < 2).collect();
    let u: Vec<Bool> = (0..P12_UNITS)
        .map(|k| Bool::new_const(format!("r1555_2_{tag}_u{k}")))
        .collect();
    let unit = |k: usize| k % 3 == 0;
    let mut hard: Vec<Bool> = (0..P12_UNITS)
        .map(|k| if unit(k) { u[k].clone() } else { !&u[k] })
        .collect();
    let pick = |i: usize, salt: u64| p12_hash(i, salt) % P12_SYMBOLS;
    for i in 0..P12_COMPOUND {
        let (a, b, c, d) = (pick(i, 1), pick(i, 2), pick(i, 3), pick(i, 4));
        let w = p12_hash(i, 5) % P12_UNITS;
        let (term, truth) = match i % 6 {
            0 => (Bool::or(&[!&s[a], s[b].clone()]), !value[a] || value[b]),
            1 => (
                Bool::or(&[s[a].clone(), s[b].clone(), !&s[c]]),
                value[a] || value[b] || !value[c],
            ),
            2 => (
                s[a].implies(Bool::and(&[s[b].clone(), !&s[c]])),
                !value[a] || (value[b] && !value[c]),
            ),
            3 => (s[a].iff(&s[b]), value[a] == value[b]),
            4 => (
                Bool::or(&[!&s[a], s[b].clone(), s[c].clone(), !&u[w]]),
                !value[a] || value[b] || value[c] || !unit(w),
            ),
            _ => (
                s[a].ite(&s[b], &s[c].xor(&s[d])),
                if value[a] {
                    value[b]
                } else {
                    value[c] ^ value[d]
                },
            ),
        };
        hard.push(if truth { term } else { !term });
    }
    (s, value, u, hard)
}

/// P12 (R1555-2 §2(ii), main 357 §6; ignored, run by name): the path's own pieces at P02's size on
/// synthetic terms of P02's shapes, all true under one assignment. The walls of the encoding, the
/// circuit, the acceptance (`eval`) and the readers (the kinds of 147,669 slots and a replay of
/// 150,000 values) are printed; `eval` + `readers` must stay within 40 s.
#[test]
#[ignore = "R1555-2 size test (≈ 7.5 M terms); run by name"]
fn r1555_2_p12_the_path_after_the_answer_at_p02_size() {
    let started = Instant::now();
    let (s, value, _u, hard) = p12_hard("p12");
    let pick = |i: usize, salt: u64| p12_hash(i, salt) % P12_SYMBOLS;
    let weight = u64::try_from(P12_SLOTS + 1).unwrap();
    let soft: Vec<(Bool, u64)> = (0..P12_SLOTS)
        .flat_map(|k| [(s[2 * k].clone(), weight), (s[2 * k + 1].clone(), 1)])
        .collect();
    let reads: Vec<Bool> = (0..P12_READS)
        .map(|i| {
            if i % 10 == 0 {
                Bool::and(&[s[pick(i, 6)].clone(), !&s[pick(i, 7)]])
            } else {
                s[pick(i, 8)].clone()
            }
        })
        .collect();
    let by_symbol: rustc_hash::FxHashMap<Bool, bool> =
        s.iter().cloned().zip(value.iter().copied()).collect();
    let setup = started.elapsed();

    let started = Instant::now();
    let wcnf = encode(&hard, &soft, &reads).expect("supported");
    let encode_wall = started.elapsed().as_secs_f64() - wcnf.circuit_wall;
    let mut values = vec![false; usize::try_from(wcnf.vars).unwrap()];
    for (symbol, at) in &wcnf.originals {
        values[usize::try_from(*at - 1).unwrap()] = by_symbol[symbol];
    }
    let line_cost: u64 = soft
        .iter()
        .zip((0..P12_SLOTS).flat_map(|k| [value[2 * k], value[2 * k + 1]]))
        .filter(|(_, v)| !*v)
        .map(|((_, weight), _)| *weight)
        .sum();

    let started = Instant::now();
    let answer = accept(&wcnf, &soft, line_cost - wcnf.offset, &values)
        .unwrap_or_else(|cause| panic!("{cause:?}"));
    let eval = started.elapsed();

    let started = Instant::now();
    let kinds: Vec<u8> = answer
        .soft
        .chunks_exact(2)
        .map(|pair| if pair[1] { 2 } else { u8::from(pair[0]) })
        .collect();
    let mut replay = answer.reads.iter();
    let mut asked = 0usize;
    let mut read = |_: &Bool| {
        asked += 1;
        replay.next().copied()
    };
    let replayed: usize = reads.iter().filter_map(&mut read).filter(|&v| v).count();
    let readers = started.elapsed();
    assert_eq!(asked, P12_READS);
    assert_eq!(kinds.len(), P12_SLOTS);
    println!(
        "r1555-2 p12: setup {:.3} s, encode {:.3} s, circuit {:.3} s, eval {:.3} s, readers {:.3} s; \
         vars {} hard {} soft {} units {} nodes {} reads {} (true {replayed})",
        setup.as_secs_f64(),
        encode_wall,
        wcnf.circuit_wall,
        eval.as_secs_f64(),
        readers.as_secs_f64(),
        wcnf.vars,
        wcnf.hard_count,
        wcnf.soft.len(),
        wcnf.units,
        wcnf.circuit.node_count(),
        wcnf.circuit.reads.len(),
    );
    assert!(
        eval + readers <= Duration::from_secs(40),
        "eval {eval:?} + readers {readers:?}"
    );
}

/// P13 (R1556-3 §3, main 358 §4; ignored, run by name with `CRAT_BO_MAXSAT_CMD` set to the archived
/// UWrMaxSat line): one relaxation call at P02's size. P12's hard part plus 2,000 selectors
/// `sel_j => clause`; the 1,988 with a clause true under the reference values can all hold, the 12
/// with `sel_j => !u` (u a hard unit) cannot. The call must drop exactly those 12, and its own pieces
/// (encode, circuit, write, solve, eval) must stay within 60 s.
#[test]
#[ignore = "R1556-3 relaxation size test; needs the solver CRAT_BO_MAXSAT_CMD names; run by name"]
fn r1556_2_p13_one_relaxation_at_p02_size() {
    const SELECTORS: usize = 2_000;
    const BLOCKED: usize = 12;
    let line = RunLine::parse(&std::env::var(SWITCH).expect("CRAT_BO_MAXSAT_CMD names the solver"))
        .expect("a run line");
    let (s, value, u, mut hard) = p12_hard("p13");
    let selectors: Vec<Bool> = (0..SELECTORS)
        .map(|j| Bool::new_const(format!("r1556_2_p13_sel{j}")))
        .collect();
    for (j, selector) in selectors.iter().enumerate() {
        let consequence = if j < BLOCKED {
            // u_{3j} is asserted true (k % 3 == 0), so this selector cannot hold.
            !&u[3 * j]
        } else {
            let k = p12_hash(j, 9) % P12_SYMBOLS;
            let m = p12_hash(j, 10) % P12_SYMBOLS;
            let a = if value[k] { s[k].clone() } else { !&s[k] };
            Bool::or(&[a, s[m].clone()])
        };
        hard.push(selector.implies(&consequence));
    }
    let soft: Vec<(Bool, u64)> = selectors.iter().map(|sel| (sel.clone(), 1)).collect();
    let dir = scratch("r1556-p13");
    let check = Check {
        scope: &hard,
        soft: &soft,
        reads: &[],
        started: Instant::now(),
        prepare: 0.0,
    };
    let mut report = Report::default();
    let answer = attempt(
        &line,
        &dir.join("relax"),
        Duration::from_secs(600),
        &check,
        &mut report,
    )
    .unwrap_or_else(|cause| panic!("{cause:?}"));
    let dropped: Vec<usize> = answer
        .soft
        .iter()
        .enumerate()
        .filter(|(_, keep)| !**keep)
        .map(|(j, _)| j)
        .collect();
    let fields = report.fields();
    println!("\nr1556-2 p13: {fields} dropped={}", dropped.len());
    assert_eq!(dropped, (0..BLOCKED).collect::<Vec<_>>(), "{fields}");
    let wall: f64 = ["encode=", "circuit=", "write=", "solve=", "eval="]
        .iter()
        .map(|key| {
            let at = fields.find(key).unwrap() + key.len();
            fields[at..]
                .split_whitespace()
                .next()
                .unwrap()
                .parse::<f64>()
                .unwrap()
        })
        .sum();
    assert!(wall <= 60.0, "{wall} s: {fields}");
}

/// P14's fixtures beyond P5's and P11's: main 322's cascade (a source / sink tie), the may-overlap
/// pair, and the demand evidence's realloc shapes.
const P14_REALLOC: &str = "unsafe extern \"C\" { fn realloc(p: *mut u8, n: usize) -> *mut u8; fn free(p: *mut u8); } pub unsafe fn f(p: *mut u8) { let q = realloc(p, 8); if q.is_null() { free(p); } else { free(q); } }";
const P14_OPAQUE: &str = "unsafe extern \"C\" { fn opaque() -> *mut u8; fn realloc(p: *mut u8, n: usize) -> *mut u8; } pub unsafe fn f() { let p = opaque(); let _q = realloc(p, 8); }";
const P14_MALLOC: &str = "unsafe extern \"C\" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); } pub unsafe fn f() { let p = malloc(8); let q = p; free(q); }";

/// P14 (R1556-3 §4(c)): on each fixture, every relaxation runs both ways on the same problem -- the
/// external one (H1, with the test solver) and today's z3 drop loop, whose result the run keeps.
/// H1 never falls back, its kept set is accepted by the circuit, and it never drops more than z3's
/// loop; the fixtures where the two kept sets differ are printed, and at least one relaxation drops
/// something (so the comparison is not empty).
#[test]
fn r1556_2_p14_h1_drops_no_more_than_the_z3_loop() {
    if child() {
        return;
    }
    let name = test("r1556_2_p14_h1_drops_no_more_than_the_z3_loop");
    let dir = scratch("r1556-p14");
    let line = test_solver_line(&dir);
    let mut compared = 0;
    let mut dropping = 0;
    let mut differ = Vec::new();
    for (tag, code) in [
        ("cascade", CASCADE_TIE),
        ("overlap", OVERLAP),
        ("unique", UNIQUE),
        ("realloc", P14_REALLOC),
        ("opaque", P14_OPAQUE),
        ("malloc", P14_MALLOC),
    ] {
        let (on, err) = spawn(
            &name,
            code,
            &format!("r1556-p14-{tag}"),
            "frozen",
            &[
                (SWITCH, line.clone().into()),
                (
                    crate::analyses::borrow_ownership::solver::DUAL_RELAXATION,
                    "on".into(),
                ),
                ("CRAT_BO_PHASE_LOG", "on".into()),
            ],
        );
        assert_eq!(on.kind, "emitted", "{tag}: {on:?}");
        for dual in err.lines().filter(|line| line.starts_with("[r1556-dual] ")) {
            let field = |key: &str| {
                let at = dual.find(key).unwrap() + key.len();
                dual[at..].split(' ').next().unwrap().to_owned()
            };
            let (z3, h1) = (field(" z3="), field(" h1="));
            assert!(
                z3.starts_with('['),
                "{tag}: the z3 loop was not Sat: {dual}"
            );
            assert!(
                h1.starts_with('['),
                "{tag}: H1 fell back or was unsat: {dual}"
            );
            let count = |list: &str| list.matches(',').count() + usize::from(list != "[]");
            assert!(count(&h1) <= count(&z3), "{tag}: H1 drops more: {dual}");
            compared += 1;
            dropping += usize::from(z3 != "[]" || h1 != "[]");
            if field(" same=") != "true" {
                differ.push(format!("{tag}: z3 {z3} h1 {h1}"));
            }
        }
    }
    eprintln!(
        "r1556-2 p14: {compared} relaxations compared, {dropping} with drops, differing: {differ:?}"
    );
    assert!(
        compared > 0 && dropping > 0,
        "{compared} compared, {dropping} dropping"
    );
}

/// P15 (R1556-3 §4(f)): a relaxation whose external call fails falls back to today's z3 drop loop on
/// a hard solver copied only then. A run line that answers `s UNKNOWN` makes every relaxation and
/// every optimize check fall back: one `maxsat:relax-fallback` line per relaxation (cause named),
/// no `maxsat:relax end` line, and the decision equal to the switch-off run's.
#[test]
fn r1556_2_p15_a_failed_relaxation_falls_back_to_the_z3_loop() {
    if child() {
        return;
    }
    let name = test("r1556_2_p15_a_failed_relaxation_falls_back_to_the_z3_loop");
    let dir = scratch("r1556-p15");
    let unknown = script(&dir, "unknown", "echo 's UNKNOWN'");
    let (off, _) = spawn(&name, CASCADE_TIE, "r1556-p15-off", "frozen", &[]);
    let (on, err) = spawn(
        &name,
        CASCADE_TIE,
        "r1556-p15-on",
        "frozen",
        &[(SWITCH, unknown.into()), ("CRAT_BO_PHASE_LOG", "on".into())],
    );
    assert_eq!(on.decision(), off.decision(), "{err}");
    let fallbacks = lines(&err, "maxsat:relax-fallback");
    assert!(
        !fallbacks.is_empty()
            && fallbacks
                .iter()
                .all(|line| line.contains("cause=status:UNKNOWN ")),
        "{err}"
    );
    assert!(lines(&err, "maxsat:relax").is_empty(), "{err}");
}
