//! R1529-2 (main 338): a default-off dump of the optimize problem, file output and log lines only.
//!
//! `CRAT_BO_OPTIMIZE_DUMP_DIR=<dir>` turns it on; `CRAT_BO_OPTIMIZE_DUMP_CHECKS=<solve>:<rounds>[;…]`
//! selects the checks (`solve` = `baseline` | `precise` | `refined` | `coarse`, the verify that
//! holds the check; `rounds` = a comma list of integers or `*`). A selected check is written just
//! before z3 runs it, as z3 prints the `Optimize` (`Z3_optimize_to_string`): every declaration,
//! every hard assertion now asserted (a pushed scope flattened), every soft term with its weight,
//! the query's parameters and `(check-sat)`. The file is `<dir>/<solve>-<repair>-r<NN>-<stage>.smt2`:
//! `repair` = `guarded` | `plain`, the repair run inside the verify (a declined guarded run falls back
//! to a plain run from round 0, review E1); `NN` = the run's validation round, 00 for its first solve,
//! then the round of `solve:round start` (three digits from round 100). After the check one row goes
//! to `<dir>/index.tsv` and the same fields to one stderr line.
//!
//! Nothing here changes a solver call. With the directory unset, the switch is read once and
//! nothing else happens. A failed write is one stderr line, no file is left under the check's name,
//! and the check runs as it would without the switch. The dump ends before the check's clock
//! starts; its wall still counts against `CRAT_BO_ANALYSIS_BUDGET_S` (wall time since the start).

use std::{
    cell::Cell,
    io::Write,
    path::{Path, PathBuf},
    sync::OnceLock,
    time::{Duration, Instant},
};

use z3::SatResult;

use crate::analyses::borrow_ownership::SlotKind;

const DIR_VAR: &str = "CRAT_BO_OPTIMIZE_DUMP_DIR";
const CHECKS_VAR: &str = "CRAT_BO_OPTIMIZE_DUMP_CHECKS";
const LINE_HEAD: &str = "[bo-dump]";
const INDEX: &str = "index.tsv";
const COLUMNS: [&str; 14] = [
    "name",
    "file",
    "bytes",
    "dump_wall_s",
    "hard",
    "soft",
    "result",
    "check_wall_s",
    "model",
    "ref",
    "own",
    "raw",
    "objective",
    "reason",
];

/// The verify that holds a check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Solve {
    Baseline,
    Precise,
    Refined,
    Coarse,
}

impl Solve {
    fn label(self) -> &'static str {
        match self {
            Self::Baseline => "baseline",
            Self::Precise => "precise",
            Self::Refined => "refined",
            Self::Coarse => "coarse",
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Rounds {
    All,
    These(Vec<usize>),
}

#[derive(Debug, PartialEq, Eq)]
struct Switch {
    dir: PathBuf,
    select: Vec<(Solve, Rounds)>,
}

impl Switch {
    fn selects(&self, solve: Solve, round: usize) -> bool {
        self.select.iter().any(|(s, rounds)| {
            *s == solve
                && match rounds {
                    Rounds::All => true,
                    Rounds::These(these) => these.contains(&round),
                }
        })
    }
}

/// `CRAT_BO_OPTIMIZE_DUMP_CHECKS`: `<solve>:<rounds>` items separated by `;`.
fn parse_checks(text: &str) -> Result<Vec<(Solve, Rounds)>, String> {
    let mut select = Vec::new();
    for item in text
        .split(';')
        .map(str::trim)
        .filter(|item| !item.is_empty())
    {
        let (solve, rounds) = item
            .split_once(':')
            .ok_or_else(|| format!("`{item}` is not <solve>:<rounds>"))?;
        let solve = match solve.trim() {
            "baseline" => Solve::Baseline,
            "precise" => Solve::Precise,
            "refined" => Solve::Refined,
            "coarse" => Solve::Coarse,
            other => return Err(format!("unknown solve `{other}`")),
        };
        let rounds = match rounds.trim() {
            "*" => Rounds::All,
            list => Rounds::These(
                list.split(',')
                    .map(|round| {
                        round
                            .trim()
                            .parse::<usize>()
                            .map_err(|_| format!("`{round}` is not a round"))
                    })
                    .collect::<Result<_, _>>()?,
            ),
        };
        select.push((solve, rounds));
    }
    if select.is_empty() {
        return Err("no check selected".to_owned());
    }
    Ok(select)
}

/// Read once per process. Unset or empty directory: off, silently. A directory without a
/// selection, or a selection that does not parse: off, with one stderr line.
fn switch() -> Option<&'static Switch> {
    static SWITCH: OnceLock<Option<Switch>> = OnceLock::new();
    SWITCH
        .get_or_init(|| {
            let dir = std::env::var_os(DIR_VAR).filter(|dir| !dir.is_empty())?;
            let checks = std::env::var(CHECKS_VAR).unwrap_or_default();
            match parse_checks(&checks) {
                Ok(select) => Some(Switch {
                    dir: PathBuf::from(dir),
                    select,
                }),
                Err(error) => {
                    eprintln!(
                        "{LINE_HEAD} off: {DIR_VAR} is set and {CHECKS_VAR}={checks:?} selects nothing ({error})"
                    );
                    None
                }
            }
        })
        .as_ref()
}

/// The check's place: the verify, the repair run inside it, the run's round.
#[derive(Clone, Copy)]
struct Context {
    solve: Solve,
    repair: Option<&'static str>,
    round: usize,
}

thread_local! {
    /// Where the next optimize check belongs (set only while the switch is on). A check outside a
    /// verify's repair run (no run entered since the verify started) is never selected.
    static CONTEXT: Cell<Option<Context>> = const { Cell::new(None) };
}

/// A verify starts. Its repair run is entered next ([`enter_run`]).
pub(crate) fn enter_verify(solve: Solve) {
    if switch().is_some() {
        CONTEXT.set(Some(Context {
            solve,
            repair: None,
            round: 0,
        }));
    }
}

/// A repair run of the current verify starts (`guarded` or `plain`): its first solve is round 0.
pub(crate) fn enter_run(repair: &'static str) {
    if switch().is_some() {
        CONTEXT.with(|context| {
            if let Some(current) = context.get() {
                context.set(Some(Context {
                    repair: Some(repair),
                    round: 0,
                    ..current
                }));
            }
        });
    }
}

/// A validation round of the current run starts.
pub(crate) fn enter_round(round: usize) {
    if switch().is_some() {
        CONTEXT.with(|context| {
            if let Some(current) = context.get() {
                context.set(Some(Context { round, ..current }));
            }
        });
    }
}

/// A written dump whose check has not returned yet.
pub(crate) struct Pending {
    name: String,
    path: PathBuf,
    bytes: u64,
    dump_wall: f64,
    hard: usize,
    soft: usize,
}

/// Just before a check of `optimize`: write it if the switch selects this check. `soft` = the soft
/// terms the solver's build asserted.
pub(crate) fn before_check(
    optimize: &z3::Optimize,
    stage: &'static str,
    soft: usize,
) -> Option<Pending> {
    let switch = switch()?;
    let Context {
        solve,
        repair: Some(repair),
        round,
    } = CONTEXT.get()?
    else {
        return None;
    };
    if !switch.selects(solve, round) {
        return None;
    }
    let name = format!("{}-{repair}-r{round:02}-{stage}", solve.label());
    let path = switch.dir.join(format!("{name}.smt2"));
    crate::phase_log::mark("dump:optimize", "start", &format!("name={name}"));
    let started = Instant::now();
    let written = write_text(optimize, &path);
    // z3 keeps the text it returned in the context's string buffer until the next string it
    // returns: a short one frees it now (measured: `uordblks` back to its value before the dump,
    // main 338 §4).
    let _ = z3::ast::Bool::from_bool(true).to_string();
    // The count only for a written text (review E6).
    let hard = written
        .as_ref()
        .map_or(0, |_| optimize.get_assertions().len());
    let dump_wall = started.elapsed().as_secs_f64();
    crate::phase_log::mark(
        "dump:optimize",
        "end",
        &format!(
            "name={name} wall={dump_wall:.1}s bytes={}",
            written.as_ref().map_or(0, |bytes| *bytes)
        ),
    );
    match written {
        Ok(bytes) => Some(Pending {
            name,
            path,
            bytes,
            dump_wall,
            hard,
            soft,
        }),
        Err(error) => {
            eprintln!(
                "{LINE_HEAD} name={name} file={} error={}",
                one_line(&path.display().to_string()),
                one_line(&error.to_string())
            );
            None
        }
    }
}

/// Writes the text to a new file. A failure after the file was created removes it, so no file is
/// left under the check's name (review E5). An error from z3's `Display` (no text, or text that is
/// not UTF-8) and an empty text are errors, not a panic (review E4).
fn write_text(optimize: &z3::Optimize, path: &Path) -> std::io::Result<u64> {
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)?;
    let written = write_into(optimize, file);
    if written.is_err() {
        let _ = std::fs::remove_file(path);
    }
    written
}

fn write_into(optimize: &z3::Optimize, file: std::fs::File) -> std::io::Result<u64> {
    /// `fmt::Write` over the file that keeps the I/O error, so a formatting error is told apart.
    struct Sink<W: Write> {
        inner: W,
        error: Option<std::io::Error>,
    }
    impl<W: Write> std::fmt::Write for Sink<W> {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            self.inner.write_all(text.as_bytes()).map_err(|error| {
                self.error = Some(error);
                std::fmt::Error
            })
        }
    }
    let mut sink = Sink {
        inner: std::io::BufWriter::new(file),
        error: None,
    };
    if std::fmt::write(&mut sink, format_args!("{optimize}")).is_err() {
        return Err(sink
            .error
            .take()
            .unwrap_or_else(|| std::io::Error::other("z3 returned no text for the Optimize")));
    }
    sink.inner.flush()?;
    let bytes = sink.inner.get_ref().metadata()?.len();
    if bytes == 0 {
        return Err(std::io::Error::other(
            "z3 returned an empty text for the Optimize",
        ));
    }
    Ok(bytes)
}

/// The check's outcome and the model taken from it (a Sat model or an accepted incumbent; `None` =
/// no model). `objective_ref_weight` is the Ref term's weight (the Own term weighs 1).
pub(crate) fn after_check<'a>(
    pending: Option<Pending>,
    outcome: SatResult,
    check_wall: Duration,
    reason: Option<&str>,
    model: Option<impl IntoIterator<Item = &'a SlotKind>>,
    objective_ref_weight: Option<u64>,
) {
    let Some(pending) = pending else { return };
    let result = match outcome {
        SatResult::Sat => "sat",
        SatResult::Unsat => "unsat",
        SatResult::Unknown => "unknown",
    };
    let (taken, counts) = match model {
        Some(kinds) => {
            let mut counts = [0usize; 3];
            for kind in kinds {
                counts[match kind {
                    SlotKind::Ref => 0,
                    SlotKind::Owning => 1,
                    SlotKind::Raw => 2,
                }] += 1;
            }
            let taken = if outcome == SatResult::Sat {
                "sat"
            } else {
                "incumbent"
            };
            (taken, Some(counts))
        }
        None => ("none", None),
    };
    let objective = match (counts, objective_ref_weight) {
        (Some([r, o, w]), Some(weight)) => {
            let slots = (r + o + w) as u64;
            (weight * (slots - r as u64) + (slots - o as u64)).to_string()
        }
        _ => "-".to_owned(),
    };
    let count = |i: usize| counts.map_or("-".to_owned(), |counts| counts[i].to_string());
    let cells = [
        pending.name.clone(),
        one_line(&pending.path.display().to_string()),
        pending.bytes.to_string(),
        format!("{:.3}", pending.dump_wall),
        pending.hard.to_string(),
        pending.soft.to_string(),
        result.to_owned(),
        format!("{:.3}", check_wall.as_secs_f64()),
        taken.to_owned(),
        count(0),
        count(1),
        count(2),
        objective,
        reason.map_or("-".to_owned(), one_line),
    ];
    eprintln!(
        "{LINE_HEAD} {}",
        COLUMNS
            .iter()
            .zip(&cells)
            .map(|(column, cell)| format!("{column}={cell}"))
            .collect::<Vec<_>>()
            .join(" ")
    );
    if let Err(error) = append_row(&pending.path, &cells) {
        eprintln!(
            "{LINE_HEAD} name={} index error={}",
            pending.name,
            one_line(&error.to_string())
        );
    }
}

fn append_row(dump: &Path, cells: &[String]) -> std::io::Result<()> {
    let index = dump.with_file_name(INDEX);
    let mut file = std::fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(&index)?;
    let mut text = String::new();
    if file.metadata()?.len() == 0 {
        text.push_str(&COLUMNS.join("\t"));
        text.push('\n');
    }
    text.push_str(&cells.join("\t"));
    text.push('\n');
    file.write_all(text.as_bytes())
}

/// A cell or a line field: no tab, no newline.
fn one_line(text: &str) -> String {
    text.replace(['\t', '\n', '\r'], " ")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The selection's grammar (GREEN-only: written with the build).
    #[test]
    fn r1529_2_d8_the_selection_parses_as_documented() {
        assert_eq!(
            parse_checks("baseline:0;precise:0,5, 10"),
            Ok(vec![
                (Solve::Baseline, Rounds::These(vec![0])),
                (Solve::Precise, Rounds::These(vec![0, 5, 10])),
            ])
        );
        assert_eq!(
            parse_checks(" precise:* ;"),
            Ok(vec![(Solve::Precise, Rounds::All)])
        );
        assert_eq!(
            parse_checks("refined:*;coarse:1"),
            Ok(vec![
                (Solve::Refined, Rounds::All),
                (Solve::Coarse, Rounds::These(vec![1])),
            ])
        );
        for bad in [
            "",
            ";",
            "precise",
            "final:0",
            "precise:x",
            "precise:1,,2",
            "precise:-1",
        ] {
            assert!(parse_checks(bad).is_err(), "{bad:?}");
        }
        let switch = Switch {
            dir: PathBuf::new(),
            select: parse_checks("baseline:0;precise:5,10").unwrap(),
        };
        assert!(switch.selects(Solve::Baseline, 0));
        assert!(!switch.selects(Solve::Baseline, 5));
        assert!(switch.selects(Solve::Precise, 10));
        assert!(!switch.selects(Solve::Precise, 0));
    }
}
