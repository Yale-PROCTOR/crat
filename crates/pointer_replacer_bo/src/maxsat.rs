//! R1543-2 Part 2 (main 346; the seat's R1543-4): the round's `optimize` check through an external
//! MaxSAT process. RED: the witnesses' interface only; nothing is encoded, run or handed back yet,
//! and no check reaches this module.

use std::{io::Write, path::Path, time::Duration};

use z3::{Model, Solver, ast::Bool};

/// The switch's run line.
pub(crate) struct RunLine {
    _words: Vec<String>,
}

impl RunLine {
    /// `None` for an empty or blank value (the switch unset).
    pub(crate) fn parse(text: &str) -> Option<Self> {
        let words: Vec<String> = text.split_whitespace().map(str::to_owned).collect();
        (!words.is_empty()).then_some(RunLine { _words: words })
    }
}

/// Why a check falls back to z3's `Optimize`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Cause {
    Unsupported(String),
    HardFalse,
    TooLarge,
    Write(String),
    Spawn(String),
    Limit,
    Signal(i32),
    Status(String),
    Values { got: usize, want: usize },
    NoCost,
    Sync,
    HandBack(String),
    Cost { model: u64, line: u64 },
}

/// One check's WCNF.
pub(crate) struct Wcnf {
    pub(crate) vars: i32,
    pub(crate) hard: Vec<i32>,
    pub(crate) hard_count: usize,
    pub(crate) soft: Vec<(u64, i32)>,
    pub(crate) offset: u64,
    pub(crate) originals: Vec<(Bool, i32)>,
    pub(crate) units: usize,
}

impl Wcnf {
    pub(crate) fn write_to(&self, _out: &mut impl Write) -> std::io::Result<()> {
        Ok(())
    }
}

/// RED: no encoder yet.
pub(crate) fn encode(_hard: &[Bool], _soft: &[(Bool, u64)]) -> Result<Wcnf, Cause> {
    Err(Cause::Unsupported("unbuilt".to_owned()))
}

/// One check, as the hook hands it over.
pub(crate) struct Check<'a> {
    pub(crate) scope: &'a [Bool],
    pub(crate) soft: &'a [(Bool, u64)],
    pub(crate) solver: &'a Solver,
    pub(crate) synced: usize,
}

/// RED: no hand-back yet.
pub(crate) fn hand_back(
    _solver: &Solver,
    _synced: usize,
    _scope: &[Bool],
    _wcnf: &Wcnf,
    _values: &[bool],
) -> Result<Model, Cause> {
    Err(Cause::HandBack("unbuilt".to_owned()))
}

/// The weight of the soft terms `model` does not make true.
pub(crate) fn soft_cost(model: &Model, soft: &[(Bool, u64)]) -> u64 {
    soft.iter()
        .filter(|(term, _)| model.eval(term, true).and_then(|value| value.as_bool()) != Some(true))
        .map(|(_, weight)| *weight)
        .sum()
}

/// One check's walls and sizes, for its line.
#[derive(Default)]
pub(crate) struct Report;

/// RED: no check runs yet.
pub(crate) fn attempt(
    _line: &RunLine,
    _dir: &Path,
    _limit: Duration,
    _check: &Check<'_>,
    _report: &mut Report,
) -> Result<Model, Cause> {
    Err(Cause::Unsupported("unbuilt".to_owned()))
}
