//! R1543-2 Part 2 (main 346; the seat's R1543-4): the round's `optimize` check through an external
//! MaxSAT process.
//!
//! `CRAT_BO_MAXSAT_CMD=<run line>` turns it on: a measurement switch, unset by default, refused by
//! the gate but in its one switch-on test. The words are split on whitespace, the first is the
//! binary, and the word `{wcnf}` is replaced by the problem's file (without it, the file is the last
//! argument). Unset or empty, [`run_line`] is `None`, nothing here runs, and the check is z3's
//! `Optimize` as before.
//!
//! One check, with the switch set and the objective built ([`optimum`]):
//! 1. the scope's hard assertions and the objective's soft terms are encoded as WCNF (the 2022+
//!    format): a top-level unit assertion on a symbol fixes it (unit substitution), the top level
//!    becomes clauses where its shape allows, and every compound term below gets a full Tseitin
//!    definition, hash-consed (main 341's `smt2wcnf.py`, over the z3 terms instead of their text);
//! 2. the file `<temp>/crat-maxsat-<pid>-<n>/problem.wcnf` is written in a directory the check
//!    makes new (mode 0700; a name that exists is refused, a `Write` fallback), and the run line's
//!    process solves it under its own address-space limit and crat's query limit (its pipes are read
//!    up to the same limit); the file and the directory go when the process ends, on every path;
//! 3. only `s OPTIMUM FOUND` with a `v` line over every index the file holds goes on (the `s` line
//!    is read, never the exit code; an index in no clause takes false): the assignment is handed back
//!    to a z3 solver that holds the same assertions (the round's hard solver, or a plain one), with
//!    every WCNF-mapped original variable fixed, and that solver's model is the round's model when
//!    its soft cost equals the `o` line plus the weight of the soft terms folded to false.
//!
//! Anything else is a fallback: the check runs on z3's `Optimize` exactly as today, and one
//! `[bo-phase] maxsat:fallback` line names the cause. Lines are written with the phase log on only.

use std::{
    io::{Read, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
    time::{Duration, Instant},
};

use rustc_hash::FxHashMap;
use z3::{
    DeclKind, Model, SatResult, Solver,
    ast::{Ast, Bool},
};

const VAR: &str = "CRAT_BO_MAXSAT_CMD";
/// The run line's word that stands for the problem's file.
const WCNF_WORD: &str = "{wcnf}";
/// The child's own address-space limit: P02's dumps peaked at 1,015 MiB RSS under UWrMaxSat (main
/// 342).
const CHILD_ADDRESS_SPACE: u64 = 8 << 30;
/// The tail of the child's stderr that a fallback line carries.
const STDERR_KEEP: usize = 4096;
/// How often the parent looks at the child while it runs.
const POLL: Duration = Duration::from_millis(5);

/// The switch's run line.
pub(crate) struct RunLine {
    /// The value as set.
    text: String,
    /// The words, split on whitespace; the first is the binary.
    words: Vec<String>,
}

impl RunLine {
    /// `None` for an empty or blank value (the switch unset).
    pub(crate) fn parse(text: &str) -> Option<Self> {
        let words: Vec<String> = text.split_whitespace().map(str::to_owned).collect();
        (!words.is_empty()).then(|| RunLine {
            text: text.to_owned(),
            words,
        })
    }

    /// The command for `file`: the word `{wcnf}` replaced by it, or it appended when no word is.
    fn command(&self, file: &Path) -> Command {
        let mut command = Command::new(&self.words[0]);
        let mut placed = false;
        for word in &self.words[1..] {
            if word == WCNF_WORD {
                command.arg(file);
                placed = true;
            } else {
                command.arg(word);
            }
        }
        if !placed {
            command.arg(file);
        }
        command
    }
}

/// The switch, read once.
pub(crate) fn run_line() -> Option<&'static RunLine> {
    static LINE: OnceLock<Option<RunLine>> = OnceLock::new();
    LINE.get_or_init(|| std::env::var(VAR).ok().as_deref().and_then(RunLine::parse))
        .as_ref()
}

/// The checkpoint's `config` entry (main 346 §2): the run line and its binary's sha256, so a
/// checkpoint written under one solver is refused under another; `None` with the switch unset.
pub(crate) fn config() -> Option<String> {
    static CONFIG: OnceLock<Option<String>> = OnceLock::new();
    CONFIG
        .get_or_init(|| {
            run_line().map(|line| format!("{} sha256={}", line.text, binary_sha256(&line.words[0])))
        })
        .clone()
}

fn binary_sha256(binary: &str) -> String {
    use sha2::{Digest, Sha256};
    match std::fs::read(binary) {
        Ok(bytes) => format!("{:x}", Sha256::digest(bytes)),
        Err(error) => format!("unreadable:{}", word(&error.to_string())),
    }
}

/// Why a check falls back to z3's `Optimize`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Cause {
    /// A term outside not / or / and / xor / => / = / ite / true / false and Bool symbols.
    Unsupported(String),
    /// The hard part folds to false (z3 owns every `Unsat`).
    HardFalse,
    /// More variables than a WCNF literal holds.
    TooLarge,
    /// The file could not be written.
    Write(String),
    /// The process could not be started (or waited for).
    Spawn(String),
    /// The process reached the wall limit and was killed.
    Limit,
    /// The process ended by a signal.
    Signal(i32),
    /// The `s` line, when it is not `OPTIMUM FOUND` (`none` without one).
    Status(String),
    /// A `v` line of the wrong length.
    Values { got: usize, want: usize },
    /// No `o` line.
    NoCost,
    /// The hand-back solver holds more assertions than the scope (assertions only grow).
    Sync,
    /// The hand-back check was not `Sat`.
    HandBack(String),
    /// The handed-back model's soft cost differs from the `o` line plus the folded weight.
    Cost { model: u64, line: u64 },
}

impl Cause {
    /// One word for the line.
    fn label(&self) -> String {
        match self {
            Cause::Unsupported(kind) => format!("unsupported:{}", word(kind)),
            Cause::HardFalse => "hard-false".to_owned(),
            Cause::TooLarge => "too-large".to_owned(),
            Cause::Write(error) => format!("write:{}", word(error)),
            Cause::Spawn(error) => format!("spawn:{}", word(error)),
            Cause::Limit => "limit".to_owned(),
            Cause::Signal(signal) => format!("signal:{signal}"),
            Cause::Status(status) => format!("status:{}", word(status)),
            Cause::Values { got, want } => format!("values:{got}/{want}"),
            Cause::NoCost => "no-o".to_owned(),
            Cause::Sync => "sync".to_owned(),
            Cause::HandBack(outcome) => format!("handback:{}", word(outcome)),
            Cause::Cost { model, line } => format!("cost:{model}/{line}"),
        }
    }
}

/// `text` as one word (whitespace runs joined by `_`), for a `key=value` field.
fn word(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join("_")
}

/// One check's WCNF.
pub(crate) struct Wcnf {
    /// The highest variable index.
    pub(crate) vars: i32,
    /// The hard clauses, each ended by `0`.
    pub(crate) hard: Vec<i32>,
    pub(crate) hard_count: usize,
    /// `(weight, literal)` for every soft term not folded to a constant.
    pub(crate) soft: Vec<(u64, i32)>,
    /// The weight of the soft terms folded to false: every assignment pays it.
    pub(crate) offset: u64,
    /// Every original symbol that got an index, with its index.
    pub(crate) originals: Vec<(Bool, i32)>,
    /// The symbols a top-level unit fixed: in no clause, fixed by the same unit at the hand-back.
    pub(crate) units: usize,
}

impl Wcnf {
    /// The highest index the file holds. The 2022+ format has no header, so a solver reads its
    /// variable count from it; an index above it went into no clause (it was folded away), and any
    /// value of it satisfies the file (the review of 9595db605).
    pub(crate) fn written_vars(&self) -> i32 {
        self.hard
            .iter()
            .chain(self.soft.iter().map(|(_, lit)| lit))
            .map(|lit| lit.abs())
            .max()
            .unwrap_or(0)
    }

    /// The file's text: a comment, the hard clauses (`h … 0`), then the soft terms (`w lit 0`).
    pub(crate) fn write_to(&self, out: &mut impl Write) -> std::io::Result<()> {
        writeln!(
            out,
            "c crat maxsat vars {} hard {} soft {} offset {}",
            self.vars,
            self.hard_count,
            self.soft.len(),
            self.offset
        )?;
        let mut open = false;
        for &lit in &self.hard {
            if !open {
                out.write_all(b"h")?;
                open = true;
            }
            if lit == 0 {
                out.write_all(b" 0\n")?;
                open = false;
            } else {
                write!(out, " {lit}")?;
            }
        }
        for &(weight, lit) in &self.soft {
            writeln!(out, "{weight} {lit} 0")?;
        }
        Ok(())
    }
}

/// A term's value while encoding: a constant, or a WCNF literal (a signed 1-based index).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Val {
    Const(bool),
    Lit(i32),
}

impl std::ops::Not for Val {
    type Output = Val;

    fn not(self) -> Val {
        match self {
            Val::Const(value) => Val::Const(!value),
            Val::Lit(lit) => Val::Lit(-lit),
        }
    }
}

fn signed(value: Val, negated: bool) -> Val {
    if negated { !value } else { value }
}

fn decl_kind(term: &Bool) -> Option<DeclKind> {
    term.safe_decl().ok().map(|decl| decl.kind())
}

/// A Bool symbol: an uninterpreted constant.
fn is_symbol(term: &Bool) -> bool {
    term.is_const() && decl_kind(term) == Some(DeclKind::UNINTERPRETED)
}

/// The symbol under a `not`, when `term` is the negation of one.
fn negated_symbol(term: &Bool) -> Option<Bool> {
    if decl_kind(term) != Some(DeclKind::NOT) {
        return None;
    }
    let child = term.nth_child(0)?.as_bool()?;
    is_symbol(&child).then_some(child)
}

fn bool_children(term: &Bool) -> Result<Vec<Bool>, Cause> {
    term.children()
        .iter()
        .map(|child| {
            child
                .as_bool()
                .ok_or_else(|| Cause::Unsupported("non-bool".to_owned()))
        })
        .collect()
}

#[derive(Default)]
struct Encoder {
    /// The symbols a top-level unit fixed.
    consts: FxHashMap<Bool, bool>,
    /// The other symbols, by index.
    var: FxHashMap<Bool, i32>,
    originals: Vec<(Bool, i32)>,
    /// Every compound term met, by term identity (z3 shares equal terms).
    memo: FxHashMap<Bool, Val>,
    or_memo: FxHashMap<Vec<i32>, i32>,
    xor_memo: FxHashMap<(i32, i32), i32>,
    n: i32,
    hard: Vec<i32>,
    hard_count: usize,
}

impl Encoder {
    fn fresh(&mut self) -> Result<i32, Cause> {
        self.n = self.n.checked_add(1).ok_or(Cause::TooLarge)?;
        Ok(self.n)
    }

    fn clause(&mut self, lits: &[i32]) {
        self.hard.extend_from_slice(lits);
        self.hard.push(0);
        self.hard_count += 1;
    }

    fn symbol(&mut self, term: &Bool) -> Result<Val, Cause> {
        if let Some(&value) = self.consts.get(term) {
            return Ok(Val::Const(value));
        }
        if let Some(&index) = self.var.get(term) {
            return Ok(Val::Lit(index));
        }
        let index = self.fresh()?;
        self.var.insert(term.clone(), index);
        self.originals.push((term.clone(), index));
        Ok(Val::Lit(index))
    }

    /// `term` as a constant or a literal; a compound term gets its definition once.
    fn enc(&mut self, term: &Bool) -> Result<Val, Cause> {
        if let Some(value) = term.as_bool() {
            return Ok(Val::Const(value));
        }
        if is_symbol(term) {
            return self.symbol(term);
        }
        if let Some(&value) = self.memo.get(term) {
            return Ok(value);
        }
        let kind =
            decl_kind(term).ok_or_else(|| Cause::Unsupported(format!("{:?}", term.kind())))?;
        let children = bool_children(term)?;
        let value = match kind {
            DeclKind::NOT if children.len() == 1 => !self.enc(&children[0])?,
            DeclKind::OR => {
                let values = self.enc_all(&children)?;
                self.mk_or(values)?
            }
            DeclKind::AND => {
                let values = self.enc_all(&children)?;
                self.mk_and(values)?
            }
            DeclKind::IMPLIES if !children.is_empty() => {
                let values = self.enc_all(&children)?;
                let (last, init) = values.split_last().expect("children");
                let mut value = *last;
                for &premise in init.iter().rev() {
                    value = self.mk_or(vec![!premise, value])?;
                }
                value
            }
            DeclKind::XOR => {
                let values = self.enc_all(&children)?;
                self.mk_xor(values)?
            }
            DeclKind::EQ | DeclKind::IFF if children.len() >= 2 => {
                let values = self.enc_all(&children)?;
                let mut equal = Vec::with_capacity(values.len() - 1);
                for pair in values.windows(2) {
                    equal.push(!self.mk_xor(vec![pair[0], pair[1]])?);
                }
                self.mk_and(equal)?
            }
            DeclKind::ITE if children.len() == 3 => {
                let condition = self.enc(&children[0])?;
                let then = self.enc(&children[1])?;
                let otherwise = self.enc(&children[2])?;
                let then = self.mk_and(vec![condition, then])?;
                let otherwise = self.mk_and(vec![!condition, otherwise])?;
                self.mk_or(vec![then, otherwise])?
            }
            other => {
                return Err(Cause::Unsupported(format!("{other:?}/{}", children.len())));
            }
        };
        self.memo.insert(term.clone(), value);
        Ok(value)
    }

    fn enc_all(&mut self, terms: &[Bool]) -> Result<Vec<Val>, Cause> {
        terms.iter().map(|term| self.enc(term)).collect()
    }

    fn mk_or(&mut self, values: Vec<Val>) -> Result<Val, Cause> {
        let mut lits = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Val::Const(true) => return Ok(Val::Const(true)),
                Val::Const(false) => {}
                Val::Lit(lit) => lits.push(lit),
            }
        }
        lits.sort_unstable();
        lits.dedup();
        if lits.iter().any(|lit| lits.binary_search(&-lit).is_ok()) {
            return Ok(Val::Const(true));
        }
        match lits.as_slice() {
            [] => return Ok(Val::Const(false)),
            [lit] => return Ok(Val::Lit(*lit)),
            _ => {}
        }
        if let Some(&aux) = self.or_memo.get(&lits) {
            return Ok(Val::Lit(aux));
        }
        let aux = self.fresh()?;
        for &lit in &lits {
            self.clause(&[aux, -lit]);
        }
        let mut long = Vec::with_capacity(lits.len() + 1);
        long.push(-aux);
        long.extend_from_slice(&lits);
        self.clause(&long);
        self.or_memo.insert(lits, aux);
        Ok(Val::Lit(aux))
    }

    fn mk_and(&mut self, values: Vec<Val>) -> Result<Val, Cause> {
        let negated = values.into_iter().map(|value| !value).collect();
        Ok(!self.mk_or(negated)?)
    }

    fn mk_xor(&mut self, values: Vec<Val>) -> Result<Val, Cause> {
        let mut parity = false;
        let mut vars = Vec::with_capacity(values.len());
        for value in values {
            match value {
                Val::Const(value) => parity ^= value,
                Val::Lit(lit) => {
                    parity ^= lit < 0;
                    vars.push(lit.abs());
                }
            }
        }
        // A variable met twice cancels.
        vars.sort_unstable();
        let mut kept: Vec<i32> = Vec::with_capacity(vars.len());
        for var in vars {
            if kept.last() == Some(&var) {
                kept.pop();
            } else {
                kept.push(var);
            }
        }
        let Some((&first, rest)) = kept.split_first() else {
            return Ok(Val::Const(parity));
        };
        let mut value = first;
        for &next in rest {
            let (a, b) = if value < next {
                (value, next)
            } else {
                (next, value)
            };
            value = match self.xor_memo.get(&(a, b)) {
                Some(&aux) => aux,
                None => {
                    let aux = self.fresh()?;
                    self.clause(&[-aux, a, b]);
                    self.clause(&[-aux, -a, -b]);
                    self.clause(&[aux, -a, b]);
                    self.clause(&[aux, a, -b]);
                    self.xor_memo.insert((a, b), aux);
                    aux
                }
            };
        }
        Ok(Val::Lit(if parity { -value } else { value }))
    }

    /// Assert `term` (its negation when `negated`): clauses directly where the shape allows.
    fn top(&mut self, term: &Bool, negated: bool) -> Result<(), Cause> {
        if let Some(value) = term.as_bool() {
            return if value != negated {
                Ok(())
            } else {
                Err(Cause::HardFalse)
            };
        }
        if !is_symbol(term)
            && let Some(kind) = decl_kind(term)
        {
            let children = bool_children(term)?;
            match (kind, negated) {
                (DeclKind::NOT, _) if children.len() == 1 => {
                    return self.top(&children[0], !negated);
                }
                (DeclKind::AND, false) | (DeclKind::OR, true) => {
                    for child in &children {
                        self.top(child, negated)?;
                    }
                    return Ok(());
                }
                (DeclKind::OR, false) | (DeclKind::AND, true) => {
                    let items: Vec<(Bool, bool)> =
                        children.into_iter().map(|child| (child, negated)).collect();
                    return self.top_or(&items);
                }
                (DeclKind::IMPLIES, false) if children.len() == 2 => {
                    return self
                        .top_or(&[(children[0].clone(), true), (children[1].clone(), false)]);
                }
                (DeclKind::IMPLIES, true) if children.len() == 2 => {
                    self.top(&children[0], false)?;
                    return self.top(&children[1], true);
                }
                (DeclKind::EQ | DeclKind::IFF, false) | (DeclKind::XOR, true)
                    if children.len() == 2 =>
                {
                    let a = self.enc(&children[0])?;
                    let b = self.enc(&children[1])?;
                    return self.equiv(a, b);
                }
                _ => {}
            }
        }
        match signed(self.enc(term)?, negated) {
            Val::Const(true) => Ok(()),
            Val::Const(false) => Err(Cause::HardFalse),
            Val::Lit(lit) => {
                self.clause(&[lit]);
                Ok(())
            }
        }
    }

    /// Assert the disjunction of `items` (each negated when its flag says so).
    fn top_or(&mut self, items: &[(Bool, bool)]) -> Result<(), Cause> {
        let mut lits = Vec::with_capacity(items.len());
        let mut compounds = Vec::new();
        for (item, negated) in items {
            if !(is_symbol(item) || negated_symbol(item).is_some()) {
                compounds.push((item, *negated));
                continue;
            }
            match signed(self.enc(item)?, *negated) {
                Val::Const(true) => return Ok(()),
                Val::Const(false) => {}
                Val::Lit(lit) => lits.push(lit),
            }
        }
        if lits.is_empty()
            && let [(item, negated)] = compounds.as_slice()
        {
            return self.top(item, *negated);
        }
        for (item, negated) in compounds {
            match signed(self.enc(item)?, negated) {
                Val::Const(true) => return Ok(()),
                Val::Const(false) => {}
                Val::Lit(lit) => lits.push(lit),
            }
        }
        lits.sort_unstable();
        lits.dedup();
        if lits.iter().any(|lit| lits.binary_search(&-lit).is_ok()) {
            return Ok(());
        }
        if lits.is_empty() {
            return Err(Cause::HardFalse);
        }
        self.clause(&lits);
        Ok(())
    }

    fn equiv(&mut self, a: Val, b: Val) -> Result<(), Cause> {
        match (a, b) {
            (Val::Const(a), Val::Const(b)) => {
                if a == b {
                    Ok(())
                } else {
                    Err(Cause::HardFalse)
                }
            }
            (Val::Lit(lit), Val::Const(value)) | (Val::Const(value), Val::Lit(lit)) => {
                self.clause(&[if value { lit } else { -lit }]);
                Ok(())
            }
            (Val::Lit(a), Val::Lit(b)) if a == b => Ok(()),
            (Val::Lit(a), Val::Lit(b)) if a == -b => Err(Cause::HardFalse),
            (Val::Lit(a), Val::Lit(b)) => {
                self.clause(&[-a, b]);
                self.clause(&[a, -b]);
                Ok(())
            }
        }
    }
}

/// Encode `hard` (the scope's assertions) and `soft` (`(term, weight)`) as WCNF.
pub(crate) fn encode(hard: &[Bool], soft: &[(Bool, u64)]) -> Result<Wcnf, Cause> {
    let mut encoder = Encoder::default();
    // A top-level unit on a symbol fixes it: exact, since the unit is hard.
    let mut units = 0;
    for assertion in hard {
        let (symbol, value) = if is_symbol(assertion) {
            (assertion.clone(), true)
        } else if let Some(symbol) = negated_symbol(assertion) {
            (symbol, false)
        } else {
            continue;
        };
        match encoder.consts.insert(symbol, value) {
            Some(previous) if previous != value => return Err(Cause::HardFalse),
            Some(_) => {}
            None => units += 1,
        }
    }
    for assertion in hard {
        encoder.top(assertion, false)?;
    }
    let mut soft_lits = Vec::with_capacity(soft.len());
    let mut offset = 0u64;
    for (term, weight) in soft {
        match encoder.enc(term)? {
            Val::Const(true) => {}
            Val::Const(false) => offset = offset.saturating_add(*weight),
            Val::Lit(lit) => soft_lits.push((*weight, lit)),
        }
    }
    Ok(Wcnf {
        vars: encoder.n,
        hard: encoder.hard,
        hard_count: encoder.hard_count,
        soft: soft_lits,
        offset,
        originals: encoder.originals,
        units,
    })
}

/// The check's file in the directory this check made, both removed when dropped (on every path, a
/// panic too). It is built only after the directory is made, so it never removes anything else.
struct WcnfFile(PathBuf);

impl Drop for WcnfFile {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
        if let Some(dir) = self.0.parent() {
            let _ = std::fs::remove_dir(dir);
        }
    }
}

/// A new directory name for one check: `<temp>/crat-maxsat-<pid>-<n>`.
fn wcnf_dir() -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    std::env::temp_dir().join(format!(
        "crat-maxsat-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ))
}

/// Makes `dir` new, never accepting one that exists (a symlink planted at the name included), with
/// mode 0700 on Unix (the review of 9595db605, note 6).
fn make_dir(dir: &Path) -> std::io::Result<()> {
    let mut builder = std::fs::DirBuilder::new();
    #[cfg(unix)]
    std::os::unix::fs::DirBuilderExt::mode(&mut builder, 0o700);
    builder.create(dir)
}

fn write_file(wcnf: &Wcnf, dir: &Path) -> Result<(WcnfFile, u64), Cause> {
    let error = |error: std::io::Error| Cause::Write(error.to_string());
    make_dir(dir).map_err(error)?;
    let file = WcnfFile(dir.join("problem.wcnf"));
    let created = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&file.0)
        .map_err(error)?;
    let mut out = std::io::BufWriter::with_capacity(1 << 22, created);
    wcnf.write_to(&mut out).map_err(error)?;
    out.flush().map_err(error)?;
    drop(out);
    let bytes = std::fs::metadata(&file.0).map_err(error)?.len();
    Ok((file, bytes))
}

/// R1543-4 (3): the child's own `RLIMIT_AS`, through a hand-declared `setrlimit` on Linux / glibc
/// (as `phase_log` declares `mallinfo2`). Elsewhere no limit is set, and the line says
/// `as_limit=none`.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
mod address_limit {
    use std::{ffi::c_int, os::unix::process::CommandExt};

    /// glibc's `struct rlimit` (`sys/resource.h`): the soft and the hard limit, each an `rlim_t`
    /// (`unsigned long`, the width of `usize` on Linux). Read only by the system call.
    #[repr(C)]
    struct Rlimit {
        _rlim_cur: usize,
        _rlim_max: usize,
    }

    /// `RLIMIT_AS` on Linux (`asm-generic/resource.h`).
    const RLIMIT_AS: c_int = 9;

    // SAFETY: this is glibc's `int setrlimit(__rlimit_resource_t resource, const struct rlimit
    // *rlim)`. `__rlimit_resource_t` is an `int`-sized enum, and `Rlimit` above is `struct rlimit`
    // field for field, so the declaration has the C signature. glibc provides the symbol (2.42 on the
    // build and run hosts), and `std` already links it.
    unsafe extern "C" {
        fn setrlimit(resource: c_int, rlim: *const Rlimit) -> c_int;
    }

    /// The child's address space limited to `bytes` (the soft and the hard limit); its label.
    pub(super) fn set(command: &mut std::process::Command, bytes: u64) -> String {
        let bytes = usize::try_from(bytes).unwrap_or(usize::MAX);
        let limit = Rlimit {
            _rlim_cur: bytes,
            _rlim_max: bytes,
        };
        // SAFETY: the closure runs in the forked child between `fork` and `exec`, where only
        // async-signal-safe work is allowed. It makes one `setrlimit` call (in glibc one `prlimit64`
        // system call: no lock, no allocation) on `limit`, a plain value the closure owns, and on a
        // failure reads `errno` through `io::Error::last_os_error`, which does not allocate. It
        // touches no other state of the parent.
        unsafe {
            command.pre_exec(move || {
                if setrlimit(RLIMIT_AS, &limit) == 0 {
                    Ok(())
                } else {
                    Err(std::io::Error::last_os_error())
                }
            });
        }
        bytes.to_string()
    }
}

#[cfg(not(all(target_os = "linux", target_env = "gnu")))]
mod address_limit {
    /// No limit off Linux / glibc: the label says so.
    pub(super) fn set(_command: &mut std::process::Command, _bytes: u64) -> String {
        "none".to_owned()
    }
}

/// The child's stdout, or why there is none; its stderr's tail either way; the limit it ran under.
struct ChildRun {
    stdout: Result<String, Cause>,
    stderr: String,
    as_limit: String,
}

fn run_child(line: &RunLine, file: &Path, limit: Duration) -> ChildRun {
    let mut command = line.command(file);
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let as_limit = address_limit::set(&mut command, CHILD_ADDRESS_SPACE);
    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(error) => {
            return ChildRun {
                stdout: Err(Cause::Spawn(error.to_string())),
                stderr: String::new(),
                as_limit,
            };
        }
    };
    let stdout = child.stdout.take().map(drain);
    let stderr = child.stderr.take().map(drain);
    let started = Instant::now();
    let ended = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Ok(status),
            Ok(None) if started.elapsed() >= limit => {
                // R1543-4 (5b): SIGKILL, through `Child::kill` only; then the child is reaped.
                let _ = child.kill();
                let _ = child.wait();
                break Err(Cause::Limit);
            }
            Ok(None) => std::thread::sleep(POLL),
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                break Err(Cause::Spawn(format!("wait: {error}")));
            }
        }
    };
    // The review of 9595db605: a run line that forks (a wrapper that does not `exec`) can leave a
    // process holding the pipes after the child is gone. The drains are waited for up to the limit
    // only; a pipe still open then is left to its thread, and the check is a `Limit`.
    let deadline = started.checked_add(limit);
    let stdout = match stdout {
        Some(handle) => collect(handle, deadline),
        None => Some(Vec::new()),
    };
    let stderr = tail(
        &stderr
            .and_then(|handle| collect(handle, deadline))
            .unwrap_or_default(),
    );
    let stdout = ended.and_then(|status| match signal(&status) {
        Some(signal) => Err(Cause::Signal(signal)),
        None => stdout
            .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
            .ok_or(Cause::Limit),
    });
    ChildRun {
        stdout,
        stderr,
        as_limit,
    }
}

fn drain(mut pipe: impl Read + Send + 'static) -> std::thread::JoinHandle<Vec<u8>> {
    std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let _ = pipe.read_to_end(&mut bytes);
        bytes
    })
}

fn join(handle: std::thread::JoinHandle<Vec<u8>>) -> Vec<u8> {
    handle.join().unwrap_or_default()
}

/// A drain's bytes, or `None` when its pipe is still open at `deadline` (the thread is left to end
/// on its own). No deadline (a limit past `Instant`'s range) waits as long as the pipe is open.
fn collect(handle: std::thread::JoinHandle<Vec<u8>>, deadline: Option<Instant>) -> Option<Vec<u8>> {
    while !handle.is_finished() {
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return None;
        }
        std::thread::sleep(POLL);
    }
    Some(join(handle))
}

#[cfg(unix)]
fn signal(status: &std::process::ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;
    status.signal()
}

#[cfg(not(unix))]
fn signal(_status: &std::process::ExitStatus) -> Option<i32> {
    None
}

/// The last [`STDERR_KEEP`] bytes, on one line.
fn tail(bytes: &[u8]) -> String {
    let start = bytes.len().saturating_sub(STDERR_KEEP);
    String::from_utf8_lossy(&bytes[start..])
        .trim()
        .replace('\n', " | ")
}

/// The `o` line and the values of the variables `1..=vars`, when the `s` line is `OPTIMUM FOUND`
/// (R1543-4 (2): the `s` line decides, never the exit code). A `v` line is one 0/1 string (the
/// 2022+ format) or signed literals over one or more lines. It must give `1..=written`, the indices
/// the file holds; it may give more, up to `vars`; the rest, in no clause, take false.
fn parse_answer(stdout: &str, written: usize, vars: usize) -> Result<(u64, Vec<bool>), Cause> {
    let mut status = None;
    let mut cost = None;
    let mut bodies = Vec::new();
    for line in stdout.lines() {
        if let Some(rest) = line.strip_prefix("s ") {
            status = Some(rest.trim());
        } else if let Some(rest) = line.strip_prefix("o ") {
            if let Ok(value) = rest.trim().parse::<u64>() {
                cost = Some(value);
            }
        } else if line == "v" || line.starts_with("v ") {
            bodies.push(line[1..].trim());
        }
    }
    match status {
        Some("OPTIMUM FOUND") => {}
        other => return Err(Cause::Status(other.unwrap_or("none").to_owned())),
    }
    let values = parse_values(&bodies, written, vars)?;
    let cost = cost.ok_or(Cause::NoCost)?;
    Ok((cost, values))
}

fn parse_values(bodies: &[&str], written: usize, vars: usize) -> Result<Vec<bool>, Cause> {
    if let [body] = bodies
        && !body.is_empty()
        && body.bytes().all(|byte| byte == b'0' || byte == b'1')
    {
        if !(written..=vars).contains(&body.len()) {
            return Err(Cause::Values {
                got: body.len(),
                want: written,
            });
        }
        let mut values: Vec<bool> = body.bytes().map(|byte| byte == b'1').collect();
        values.resize(vars, false);
        return Ok(values);
    }
    let mut values = vec![None; vars];
    for token in bodies.iter().flat_map(|body| body.split_whitespace()) {
        let lit: i64 = token.parse().map_err(|_| Cause::Values {
            got: 0,
            want: written,
        })?;
        if lit == 0 {
            continue;
        }
        let index = usize::try_from(lit.unsigned_abs()).unwrap_or(usize::MAX);
        let slot = values.get_mut(index.wrapping_sub(1)).ok_or(Cause::Values {
            got: index,
            want: written,
        })?;
        *slot = Some(lit > 0);
    }
    let got = values[..written]
        .iter()
        .filter(|value| value.is_some())
        .count();
    if got != written {
        return Err(Cause::Values { got, want: written });
    }
    Ok(values
        .into_iter()
        .map(|value| value == Some(true))
        .collect())
}

/// One check, as the hook hands it over.
pub(crate) struct Check<'a> {
    /// The `Optimize`'s hard assertions in the check's scope (the bundle, the rows, the demand
    /// query's literals in).
    pub(crate) scope: &'a [Bool],
    /// The objective's soft terms as the build asserted them: per slot, `ref` (its weight) then
    /// `own` (1).
    pub(crate) soft: &'a [(Bool, u64)],
    /// The hand-back solver: a plain z3 solver whose first `synced` assertions are the scope's
    /// first `synced`.
    pub(crate) solver: &'a Solver,
    pub(crate) synced: usize,
}

/// R1543-4 (1): the hand-back. `solver` takes the rest of the scope in a pushed scope and is checked
/// with every WCNF-mapped original variable fixed at the external value; the symbols a unit fixed
/// are in no clause, and the same units fix them here. Its model, after the pop, is the check's.
pub(crate) fn hand_back(
    solver: &Solver,
    synced: usize,
    scope: &[Bool],
    wcnf: &Wcnf,
    values: &[bool],
) -> Result<Model, Cause> {
    let Some(rest) = scope.get(synced..) else {
        return Err(Cause::Sync);
    };
    let assumptions: Vec<Bool> = wcnf
        .originals
        .iter()
        .map(|(symbol, index)| {
            let index = usize::try_from(*index - 1).expect("a WCNF index is positive");
            if values[index] {
                symbol.clone()
            } else {
                !symbol
            }
        })
        .collect();
    solver.push();
    for assertion in rest {
        solver.assert(assertion);
    }
    let outcome = solver.check_assumptions(&assumptions);
    let model = if outcome == SatResult::Sat {
        solver.get_model()
    } else {
        None
    };
    let reason = (outcome == SatResult::Unknown)
        .then(|| solver.get_reason_unknown())
        .flatten();
    solver.pop(1);
    model.ok_or_else(|| {
        Cause::HandBack(match outcome {
            SatResult::Sat => "no-model".to_owned(),
            SatResult::Unsat => "unsat".to_owned(),
            SatResult::Unknown => format!("unknown:{}", reason.unwrap_or_else(|| "-".to_owned())),
        })
    })
}

fn holds(model: &Model, term: &Bool) -> bool {
    model.eval(term, true).and_then(|value| value.as_bool()) == Some(true)
}

/// The weight of the soft terms `model` does not make true.
pub(crate) fn soft_cost(model: &Model, soft: &[(Bool, u64)]) -> u64 {
    soft.iter()
        .filter(|(term, _)| !holds(model, term))
        .map(|(_, weight)| *weight)
        .sum()
}

/// One check's walls and sizes, for its line.
#[derive(Default)]
pub(crate) struct Report {
    encode: f64,
    write: f64,
    solve: f64,
    handback: f64,
    bytes: u64,
    vars: i32,
    hard: usize,
    soft: usize,
    units: usize,
    offset: u64,
    o: u64,
    as_limit: String,
    stderr: String,
}

impl Report {
    fn fields(&self) -> String {
        format!(
            "encode={:.3} write={:.3} solve={:.3} handback={:.3} wcnf_bytes={} vars={} hard={} \
             soft={} units={} offset={} as_limit={}",
            self.encode,
            self.write,
            self.solve,
            self.handback,
            self.bytes,
            self.vars,
            self.hard,
            self.soft,
            self.units,
            self.offset,
            if self.as_limit.is_empty() {
                "-"
            } else {
                self.as_limit.as_str()
            },
        )
    }
}

/// One check through the run line: the handed-back model, or why not. `dir` holds the file.
pub(crate) fn attempt(
    line: &RunLine,
    dir: &Path,
    limit: Duration,
    check: &Check<'_>,
    report: &mut Report,
) -> Result<Model, Cause> {
    let started = Instant::now();
    let wcnf = encode(check.scope, check.soft)?;
    report.encode = started.elapsed().as_secs_f64();
    report.vars = wcnf.vars;
    report.hard = wcnf.hard_count;
    report.soft = wcnf.soft.len();
    report.units = wcnf.units;
    report.offset = wcnf.offset;
    let started = Instant::now();
    let (file, bytes) = write_file(&wcnf, dir)?;
    report.write = started.elapsed().as_secs_f64();
    report.bytes = bytes;
    let started = Instant::now();
    let run = run_child(line, &file.0, limit);
    drop(file);
    report.solve = started.elapsed().as_secs_f64();
    report.as_limit = run.as_limit;
    report.stderr = run.stderr;
    let vars = usize::try_from(wcnf.vars).expect("a variable count is not negative");
    let written = usize::try_from(wcnf.written_vars()).expect("an index is not negative");
    let (cost, values) = parse_answer(&run.stdout?, written, vars)?;
    report.o = cost;
    let started = Instant::now();
    let model = hand_back(check.solver, check.synced, check.scope, &wcnf, &values)?;
    report.handback = started.elapsed().as_secs_f64();
    // R1543-4 (5a): the handed-back model's soft cost is the `o` line's, plus the folded weight.
    let model_cost = soft_cost(&model, check.soft);
    let line_cost = cost.saturating_add(wcnf.offset);
    if model_cost != line_cost {
        return Err(Cause::Cost {
            model: model_cost,
            line: line_cost,
        });
    }
    Ok(model)
}

/// The check's model from the run line's process, handed back to z3; `None` is a fallback (its
/// line written), and the caller runs today's check. `limit` is crat's query limit.
pub(crate) fn optimum(line: &RunLine, check: &Check<'_>, limit: Duration) -> Option<Model> {
    let mut report = Report::default();
    match attempt(line, &wcnf_dir(), limit, check, &mut report) {
        Ok(model) => {
            crate::phase_log::mark("maxsat:check", "end", &{
                let (refs, owns, raws) = kinds(&model, check.soft);
                format!(
                    "{} status=OPTIMUM o={} ref={refs} own={owns} raw={raws}",
                    report.fields(),
                    report.o
                )
            });
            Some(model)
        }
        Err(cause) => {
            crate::phase_log::mark(
                "maxsat:fallback",
                "progress",
                &format!(
                    "cause={} {}{}",
                    cause.label(),
                    report.fields(),
                    if report.stderr.is_empty() {
                        String::new()
                    } else {
                        format!(" stderr={}", report.stderr)
                    }
                ),
            );
            None
        }
    }
}

/// The handed-back kinds, counted from the soft pairs (per slot, `ref` then `own`; neither is Raw).
fn kinds(model: &Model, soft: &[(Bool, u64)]) -> (usize, usize, usize) {
    let (mut refs, mut owns, mut raws) = (0, 0, 0);
    for pair in soft.chunks_exact(2) {
        if holds(model, &pair[0].0) {
            refs += 1;
        } else if holds(model, &pair[1].0) {
            owns += 1;
        } else {
            raws += 1;
        }
    }
    (refs, owns, raws)
}
