//! **Relay main/374 (R1319-1) — the phase / RSS instrument.** With `CRAT_BO_PHASE_LOG=on` the pass
//! writes one stderr line per phase boundary:
//! `[bo-phase] <phase> <start|end> t=<s since the pass began> rss=<VmRSS MB> hwm=<VmHWM MB> <detail>`.
//! Off by default; off, it writes nothing and changes nothing.

use std::sync::{
    OnceLock,
    atomic::{AtomicUsize, Ordering},
};

static ON: OnceLock<bool> = OnceLock::new();
static T0: OnceLock<std::time::Instant> = OnceLock::new();
static SESSIONS: AtomicUsize = AtomicUsize::new(0);

pub(crate) fn on() -> bool {
    *ON.get_or_init(|| std::env::var("CRAT_BO_PHASE_LOG").as_deref() == Ok("on"))
}

/// The pass's start: `t=` counts from here.
pub(crate) fn begin() {
    if on() {
        T0.get_or_init(std::time::Instant::now);
        mark("pass", "start", "");
    }
}

/// One boundary line.
pub(crate) fn mark(phase: &str, edge: &str, detail: &str) {
    if !on() {
        return;
    }
    let t = T0
        .get_or_init(std::time::Instant::now)
        .elapsed()
        .as_secs_f64();
    let (rss, hwm) = status();
    // SAFETY: `Z3_get_estimated_alloc_size` reads z3's global allocation counter; it takes no
    // argument, touches no context, and the symbol is the one z3-sys already links (libz3).
    let z3 = unsafe { Z3_get_estimated_alloc_size() } >> 20;
    eprintln!("[bo-phase] {phase} {edge} t={t:.1} rss={rss} hwm={hwm} z3={z3} {detail}");
}

unsafe extern "C" {
    fn Z3_get_estimated_alloc_size() -> u64;
}

thread_local! {
    static SUB_MARKS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Relay main/379 (R1328-1 §1): a step's sub-marks ([`sub`]) are written only while `f` runs, so
/// the freeze's own `matched` is marked and the other builds of the same code stay silent.
pub(crate) fn with_sub_marks<T>(f: impl FnOnce() -> T) -> T {
    if !on() {
        return f();
    }
    let previous = SUB_MARKS.replace(true);
    let result = f();
    SUB_MARKS.set(previous);
    result
}

/// Relay main/384: whether a sub-mark would be written now (log on, inside [`with_sub_marks`]).
pub(crate) fn sub_marks_on() -> bool {
    on() && SUB_MARKS.get()
}

/// One sub-mark inside [`with_sub_marks`]; `detail` is called only when the line is written.
pub(crate) fn sub(phase: &str, edge: &str, detail: impl FnOnce() -> String) {
    if on() && SUB_MARKS.get() {
        mark(phase, edge, &detail());
    }
}

/// Relay main/375: inside a per-function loop, a `tick` line every [`TICK`] functions (the
/// running count, so a quadratic step shows as a slope), and a `slow` line for one function
/// whose own step took at least [`SLOW_S`] seconds or grew RSS by [`SLOW_MB`] MB, with its
/// MIR's size.
pub(crate) const TICK: usize = 250;
pub(crate) const SLOW_S: f64 = 2.0;
pub(crate) const SLOW_MB: u64 = 256;

/// A per-function step's probe: [`Probe::begin`] before, [`Probe::end`] after.
pub(crate) struct Probe {
    at: std::time::Instant,
    rss: u64,
}

impl Probe {
    pub(crate) fn begin() -> Option<Self> {
        on().then(|| Self {
            at: std::time::Instant::now(),
            rss: status().0,
        })
    }

    /// `index` of `total` in `phase`; `describe` names the function and its size, called only
    /// for a `slow` line.
    pub(crate) fn end(
        probe: Option<Self>,
        phase: &str,
        index: usize,
        total: usize,
        describe: impl FnOnce() -> String,
    ) {
        let Some(probe) = probe else { return };
        let wall = probe.at.elapsed().as_secs_f64();
        let grown = status().0.saturating_sub(probe.rss);
        if wall >= SLOW_S || grown >= SLOW_MB {
            mark(
                phase,
                "slow",
                &format!(
                    "{index}/{total} wall={wall:.1} grown_mb={grown} {}",
                    describe()
                ),
            );
        }
        if (index + 1) % TICK == 0 || index + 1 == total {
            mark(phase, "tick", &format!("{}/{total}", index + 1));
        }
    }
}

/// One MIR body's size for a `slow` line: locals, basic blocks, statements, calls.
pub(crate) fn body_size(body: &rustc_middle::mir::Body<'_>) -> String {
    let statements: usize = body
        .basic_blocks
        .iter()
        .map(|data| data.statements.len())
        .sum();
    let calls = body
        .basic_blocks
        .iter()
        .filter(|data| {
            matches!(
                data.terminator().kind,
                rustc_middle::mir::TerminatorKind::Call { .. }
            )
        })
        .count();
    format!(
        "locals={} blocks={} statements={statements} calls={calls}",
        body.local_decls.len(),
        body.basic_blocks.len()
    )
}

/// A nested rustc session is about to start; returns its ordinal (1-based) for the line.
pub(crate) fn session() -> usize {
    SESSIONS.fetch_add(1, Ordering::Relaxed) + 1
}

/// `VmRSS` and `VmHWM` in MB from `/proc/self/status`; `0` where unreadable.
fn status() -> (u64, u64) {
    let Ok(text) = std::fs::read_to_string("/proc/self/status") else {
        return (0, 0);
    };
    let field = |name: &str| {
        text.lines()
            .find_map(|line| line.strip_prefix(name))
            .and_then(|rest| rest.split_whitespace().next())
            .and_then(|kb| kb.parse::<u64>().ok())
            .map_or(0, |kb| kb / 1024)
    };
    (field("VmRSS:"), field("VmHWM:"))
}
