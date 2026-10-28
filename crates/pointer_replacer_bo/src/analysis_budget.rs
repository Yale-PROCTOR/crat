//! **Relay main/375 §3 (R1320-3; main 257's option 1) — the analysis budget with a typed
//! degrade.** `CRAT_BO_ANALYSIS_BUDGET_S` (wall seconds) and `CRAT_BO_ANALYSIS_BUDGET_GB` (RSS,
//! GB) bound the BO analysis; both unset (the default) is no budget, and every boundary below
//! is then a no-op. The limits are read at the analysis's boundaries -- the solve's stages, the
//! baseline construction's steps and its per-function loops, each validation round -- so a
//! limit ends the solve at the first boundary past it, never inside a step. The program is then
//! `degraded: analysis budget (<wall> s, <rss> GB, <boundary>)`: no rewrite, the tree left as
//! the input, the pass's ordinary degraded receipt.
//!
//! The limits ride [`crate::bo_rewriter::EmissionRunConfig`] into the compiler session (its
//! closure runs on a thread `run_compiler` spawns) and are entered there, on that thread, for
//! the decide.

use std::{cell::RefCell, time::Instant};

/// The two limits, in milliseconds and MB (integers, so the run config stays `Eq`); `None` =
/// that limit off.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Budget {
    pub(crate) wall_ms: Option<u64>,
    pub(crate) rss_mb: Option<u64>,
}

impl Budget {
    /// `CRAT_BO_ANALYSIS_BUDGET_S` / `_GB`; unset or empty = that limit off.
    pub(crate) fn from_env() -> Result<Self, String> {
        let read = |name: &str, unit: f64| -> Result<Option<u64>, String> {
            match std::env::var(name) {
                Ok(value) if !value.is_empty() => value
                    .parse::<f64>()
                    .ok()
                    .filter(|limit| limit.is_finite() && *limit >= 0.0)
                    .map(|limit| Some((limit * unit).round() as u64))
                    .ok_or_else(|| format!("{name}={value:?} is not a non-negative number")),
                _ => Ok(None),
            }
        };
        Ok(Self {
            wall_ms: read("CRAT_BO_ANALYSIS_BUDGET_S", 1000.0)?,
            rss_mb: read("CRAT_BO_ANALYSIS_BUDGET_GB", 1024.0)?,
        })
    }

    fn is_off(&self) -> bool {
        self.wall_ms.is_none() && self.rss_mb.is_none()
    }
}

/// Where and at what cost the budget ended the analysis.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Exceeded {
    pub(crate) wall_s: f64,
    pub(crate) rss_gb: f64,
    pub(crate) boundary: String,
}

/// The head of [`Exceeded::reason`]: the pass reads the verdict back from the session's
/// error by it (the session's thread, and its record, are gone by then).
pub(crate) const REASON_HEAD: &str = "analysis budget (";

impl Exceeded {
    /// The degraded program's reason.
    pub(crate) fn reason(&self) -> String {
        format!(
            "{REASON_HEAD}{:.0} s, {:.1} GB, {})",
            self.wall_s, self.rss_gb, self.boundary
        )
    }
}

/// The budget's verdict inside a session error, if that is what ended it.
pub(crate) fn reason_in(error: &str) -> Option<&str> {
    error.find(REASON_HEAD).map(|at| &error[at..])
}

struct Active {
    budget: Budget,
    started: Instant,
    exceeded: Option<Exceeded>,
}

thread_local! {
    static ACTIVE: RefCell<Option<Active>> = const { RefCell::new(None) };
}

/// The budget in force on this thread until it drops; the wall counts from [`enter`].
pub(crate) struct Scope {
    previous: Option<Active>,
}

pub(crate) fn enter(budget: Budget) -> Scope {
    let active = (!budget.is_off()).then(|| Active {
        budget,
        started: Instant::now(),
        exceeded: None,
    });
    Scope {
        previous: ACTIVE.with(|cell| cell.replace(active)),
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        let previous = self.previous.take();
        ACTIVE.with(|cell| *cell.borrow_mut() = previous);
    }
}

/// One boundary: `Err` with the typed reason once the budget is exceeded, here or at an
/// earlier boundary; `Ok` with no budget in force.
pub(crate) fn check(boundary: &str) -> anyhow::Result<()> {
    ACTIVE.with(|cell| {
        let mut cell = cell.borrow_mut();
        let Some(active) = cell.as_mut() else {
            return Ok(());
        };
        if let Some(exceeded) = &active.exceeded {
            return Err(anyhow::anyhow!(exceeded.reason()));
        }
        let wall_s = active.started.elapsed().as_secs_f64();
        let rss_gb = vm_rss_gb();
        if active
            .budget
            .wall_ms
            .is_some_and(|limit| wall_s * 1000.0 >= limit as f64)
            || active
                .budget
                .rss_mb
                .is_some_and(|limit| rss_gb * 1024.0 >= limit as f64)
        {
            let exceeded = Exceeded {
                wall_s,
                rss_gb,
                boundary: boundary.to_owned(),
            };
            let reason = exceeded.reason();
            active.exceeded = Some(exceeded);
            return Err(anyhow::anyhow!(reason));
        }
        Ok(())
    })
}

/// [`check`] where the boundary cannot return an error: `true` = stop.
pub(crate) fn over(boundary: &str) -> bool {
    check(boundary).is_err()
}

/// The budget's verdict on this thread, once a boundary found it exceeded.
pub(crate) fn exceeded() -> Option<Exceeded> {
    ACTIVE.with(|cell| {
        cell.borrow()
            .as_ref()
            .and_then(|active| active.exceeded.clone())
    })
}

/// `VmRSS` in GB from `/proc/self/status`; `0` where unreadable.
fn vm_rss_gb() -> f64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|status| {
            status
                .lines()
                .find_map(|line| line.strip_prefix("VmRSS:"))
                .and_then(|rest| rest.split_whitespace().next())
                .and_then(|kb| kb.parse::<f64>().ok())
        })
        .map_or(0.0, |kb| kb / (1024.0 * 1024.0))
}

#[cfg(test)]
mod tests {
    use super::Budget;
    use crate::{
        analyses::borrow_ownership::param_overlap::{OverlapMode, WholeProgramAttestation},
        bo_rewriter::{EmissionRunConfig, RewriteOutcome, rewrite_m1_path_with_emission_config},
    };

    const FIXTURE: &str = "#![allow(dead_code, unused_mut, unused_unsafe)]
pub unsafe fn read(p: *const i32) -> i32 {
    *p
}
pub unsafe fn entry() -> i32 {
    let x: i32 = 3;
    read(&x)
}
";

    fn rewrite(tag: &str, analysis_budget: Budget) -> RewriteOutcome {
        let dir = std::env::temp_dir().join(format!("crat-r375-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("lib.rs");
        std::fs::write(&root, FIXTURE).unwrap();
        rewrite_m1_path_with_emission_config(
            &root,
            OverlapMode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            &EmissionRunConfig {
                analysis_budget,
                ..Default::default()
            },
        )
    }

    /// Off by default: every boundary passes and nothing is recorded.
    #[test]
    fn r375_no_budget_every_boundary_passes() {
        let _scope = super::enter(Budget::default());
        assert!(super::check("bc:coherence").is_ok());
        assert!(super::exceeded().is_none());
    }

    /// A wall of 0 s ends at the first boundary, names it, and every later boundary
    /// fails with the same verdict; the scope's end restores no budget.
    #[test]
    fn r375_a_zero_wall_ends_at_the_first_boundary() {
        {
            let _scope = super::enter(Budget {
                wall_ms: Some(0),
                rss_mb: None,
            });
            let first = super::check("bc:source_events").unwrap_err().to_string();
            assert!(
                first.starts_with("analysis budget (") && first.ends_with(", bc:source_events)"),
                "{first}"
            );
            assert_eq!(super::check("own:bodies").unwrap_err().to_string(), first);
            assert!(super::over("solve:round"));
            assert_eq!(super::exceeded().unwrap().boundary, "bc:source_events");
        }
        assert!(super::check("bc:source_events").is_ok());
    }

    /// The witness (relay main/375 §3): under `_S=0` the program degrades with the
    /// typed reason and the input untouched; without the budget the same fixture
    /// delivers as before.
    #[test]
    fn r375_the_budget_degrades_the_program_with_a_typed_reason() {
        let budgeted = rewrite(
            "s0",
            Budget {
                wall_ms: Some(0),
                rss_mb: None,
            },
        );
        let RewriteOutcome::Degraded { reason, source, .. } = &budgeted else {
            panic!("a zero budget must degrade the program: {budgeted:#?}");
        };
        assert!(
            reason.starts_with("degraded: analysis budget (") && reason.ends_with(')'),
            "{reason}"
        );
        assert_eq!(source, FIXTURE);
        let RewriteOutcome::Emitted { source, .. } = rewrite("off", Budget::default()) else {
            panic!("the fixture must deliver without a budget");
        };
        assert!(source.contains("p: &i32"), "{source}");
    }
}
