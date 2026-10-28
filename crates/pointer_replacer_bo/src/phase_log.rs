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
    eprintln!("[bo-phase] {phase} {edge} t={t:.1} rss={rss} hwm={hwm} {detail}");
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
