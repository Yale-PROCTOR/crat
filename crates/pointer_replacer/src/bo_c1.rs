//! C1-lite corpus runner for the experimental BO (borrow_ownership) analysis.
//!
//! Harness ONLY: nothing under `analyses/**` is touched. Runs BO exactly as
//! `tests::borrow_ownership_coherence::assert_ownership_parity` constructs it
//! (tests.rs `collect_program` → `CrateSlots::build` → `CrateCtxt::new` →
//! `KindSolver::new` → `emit_crate_ownership_constraints` → per-fn
//! `add_coherence` → fixpoint with `is_mutable = true`) over the CROWN/Laertes
//! benchmark programs in `benchmarks/rs/`, and reports per program: wall-clock,
//! CEGAR rounds + commits, Ref/Raw/Owning counts, leaked sources, and
//! decline/timeout/oom/panic classification. Also runs the production borrow
//! baseline (`demote_pointers_iterative_with_fields` from all-Ref, the same
//! independent driver `assert_borrow_parity` uses) for the BO-vs-prod Ref delta.
//!
//! RECORDED DECISION (mirror over instrumentation): `verify_to_fixpoint` does
//! not expose its round count, and a ~5-line counter inside it would be
//! behavior-neutral — but it would break the `analyses/**` freeze whose diff
//! audit is deliberately trivial. Since NB5 replaces that loop and NB7 brings
//! real instrumentation, this harness instead carries a verbatim MIRROR of the
//! loop (`mirror::verify_to_fixpoint_counting`), and the non-ignored
//! `boc1_mirror_matches_real_*` tests enforce model equality against the real
//! `verify_to_fixpoint` on fixtures covering the accept, conflict-cascade,
//! source-commit, and selector-drop (leak) paths. If those tests fail after an
//! `analyses/**` change, update the mirror to match — never the reverse.
//!
//! Entry points (all `#[ignore]`d except the guards):
//!   worker:      CRAT_BOC1_INPUT=<crate-root.rs> [CRAT_BOC1_MODE=bo|prod]
//!                cargo test -p pointer_replacer --release bo_c1::boc1_run_one \
//!                  -- --exact --ignored --nocapture
//!   orchestrator: cargo test -p pointer_replacer --release bo_c1::boc1_corpus \
//!                  -- --exact --ignored --nocapture
//!                env: CRAT_BOC1_PROGRAMS=a,b,c  CRAT_BOC1_TIMEOUT_SECS=900
//!                     CRAT_BOC1_PROD_TIMEOUT_SECS=900  CRAT_BOC1_PROD=0
//!                     CRAT_BOC1_MEM_MB=8192  CRAT_BOC1_OUT=<dir>

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::ty::TyCtxt;

use crate::utils::rustc::RustProgram;

/// Copy of tests.rs `borrow_ownership_coherence::collect_program` (kept local so
/// tests.rs stays untouched): every top-level fn/struct item, in HIR owner order.
fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = Vec::new();
    let mut structs = Vec::new();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }

    RustProgram {
        tcx,
        functions,
        structs,
    }
}

/// Ordered key=value row. Generic on purpose (crude harness): the worker emits
/// whatever metrics its mode produced; the orchestrator/table render `-` for
/// missing keys. Keys and values must be space-free (see `sanitize`).
mod report {
    #[derive(Clone, Debug, Default, PartialEq)]
    pub struct Row(pub Vec<(String, String)>);

    pub const SENTINEL: &str = "BOC1 ";

    impl Row {
        pub fn get(&self, key: &str) -> Option<&str> {
            self.0
                .iter()
                .find(|(k, _)| k == key)
                .map(|(_, v)| v.as_str())
        }

        /// Insert or replace. Values are sanitized to keep the KV line parseable.
        pub fn set(&mut self, key: &str, value: impl ToString) {
            let value = sanitize(&value.to_string());
            match self.0.iter_mut().find(|(k, _)| k == key) {
                Some((_, v)) => *v = value,
                None => self.0.push((key.to_string(), value)),
            }
        }
    }

    /// Space/quote/newline-free so one row is exactly one whitespace-split line.
    pub fn sanitize(v: &str) -> String {
        let mut s: String = v
            .chars()
            .map(|c| if c.is_whitespace() || c == '"' || c == '=' { '_' } else { c })
            .collect();
        s.truncate(120);
        s
    }

    pub fn to_kv_line(row: &Row) -> String {
        let body: Vec<String> = row.0.iter().map(|(k, v)| format!("{k}={v}")).collect();
        format!("{SENTINEL}{}", body.join(" "))
    }

    pub fn parse_kv_line(line: &str) -> Option<Row> {
        let body = line.trim().strip_prefix(SENTINEL)?;
        let mut row = Row::default();
        for tok in body.split_whitespace() {
            let (k, v) = tok.split_once('=')?;
            row.0.push((k.to_string(), v.to_string()));
        }
        Some(row)
    }

    /// One JSON object per row; values that parse as finite numbers are unquoted.
    pub fn to_json_line(row: &Row) -> String {
        let body: Vec<String> = row
            .0
            .iter()
            .map(|(k, v)| {
                let numeric = v.parse::<f64>().map(|x| x.is_finite()).unwrap_or(false);
                if numeric {
                    format!("\"{k}\":{v}")
                } else {
                    format!("\"{k}\":\"{v}\"")
                }
            })
            .collect();
        format!("{{{}}}", body.join(","))
    }

    pub fn render_markdown(rows: &[Row], cols: &[&str]) -> String {
        let mut out = String::new();
        out.push_str(&format!("| {} |\n", cols.join(" | ")));
        out.push_str(&format!("|{}\n", "---|".repeat(cols.len())));
        for row in rows {
            let cells: Vec<&str> = cols.iter().map(|c| row.get(c).unwrap_or("-")).collect();
            out.push_str(&format!("| {} |\n", cells.join(" | ")));
        }
        out
    }

    /// Header = union of keys in first-appearance order; missing cells empty.
    pub fn render_csv(rows: &[Row]) -> String {
        let mut cols: Vec<String> = Vec::new();
        for row in rows {
            for (k, _) in &row.0 {
                if !cols.iter().any(|c| c == k) {
                    cols.push(k.clone());
                }
            }
        }
        let mut out = String::new();
        out.push_str(&cols.join(","));
        out.push('\n');
        for row in rows {
            let cells: Vec<&str> = cols.iter().map(|c| row.get(c).unwrap_or("")).collect();
            out.push_str(&cells.join(","));
            out.push('\n');
        }
        out
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn sample() -> Row {
            let mut r = Row::default();
            r.set("program", "bst");
            r.set("mode", "bo");
            r.set("status", "ok");
            r.set("rounds", 3usize);
            r.set("t_fixpoint_s", format!("{:.3}", 0.5f64));
            r
        }

        #[test]
        fn boc1_kv_roundtrip() {
            let row = sample();
            let line = to_kv_line(&row);
            assert!(line.starts_with(SENTINEL));
            assert_eq!(parse_kv_line(&line).expect("parse"), row);
            // Sanitizer keeps hostile values single-token (so the line stays parseable).
            let mut hostile = Row::default();
            hostile.set("err", "two words \"quoted\" a=b");
            let line = to_kv_line(&hostile);
            let back = parse_kv_line(&line).expect("parse sanitized");
            assert_eq!(back.0.len(), 1);
            assert!(!back.get("err").unwrap().contains(' '));
            // Non-sentinel and malformed lines are rejected, not misparsed.
            assert_eq!(parse_kv_line("running 1 test"), None);
            assert_eq!(parse_kv_line("BOC1 novalue"), None);
        }

        #[test]
        fn boc1_report_format() {
            let full = sample();
            let mut sparse = Row::default();
            sparse.set("program", "brotli");
            sparse.set("mode", "bo");
            sparse.set("status", "timeout");
            let md = render_markdown(&[full.clone(), sparse.clone()], &["program", "status", "rounds"]);
            assert!(md.contains("| bst | ok | 3 |"));
            assert!(md.contains("| brotli | timeout | - |"), "missing cells render `-`:\n{md}");
            let json = to_json_line(&full);
            assert!(json.contains("\"rounds\":3"), "numbers unquoted: {json}");
            assert!(json.contains("\"status\":\"ok\""), "strings quoted: {json}");
            let csv = render_csv(&[full, sparse]);
            let mut lines = csv.lines();
            assert_eq!(lines.next(), Some("program,mode,status,rounds,t_fixpoint_s"));
            assert_eq!(lines.next(), Some("bst,bo,ok,3,0.500"));
            assert_eq!(lines.next(), Some("brotli,bo,timeout,,"));
        }
    }
}

/// Provenance stamp for `results.jsonl` — a line-1 `{"_provenance":{...}}` object carrying
/// the commit SHA a sweep was produced at, so a killed run that leaves a stale file cannot
/// masquerade as current data (the phantom −97.7% regression postmortem, 2026-07-10). Pure
/// and unit-tested here; the git + filesystem glue lives in `orchestrate` / `boc1_corpus`.
mod provenance {
    /// The line-1 object prepended to `results.jsonl`. Hand-built (not `to_json_line`) so it
    /// never collides with a data row; `dirty`/`unix` are informational, `sha` is the key.
    pub fn line(sha: &str, dirty: bool, unix: u64) -> String {
        format!("{{\"_provenance\":{{\"sha\":\"{sha}\",\"dirty\":{dirty},\"unix\":{unix}}}}}")
    }

    /// Extract the stamped SHA from a candidate first line; `None` if it is not a provenance
    /// stamp (e.g. a pre-guard data row `{"program":...}`).
    pub fn parse_sha(first_line: &str) -> Option<String> {
        let line = first_line.trim();
        if !line.starts_with("{\"_provenance\":") {
            return None;
        }
        let sha = line.split("\"sha\":\"").nth(1)?.split('"').next()?;
        (!sha.is_empty()).then(|| sha.to_string())
    }

    /// Decide whether an existing `results.jsonl` must be moved aside before a sweep writes.
    /// `Some(suffix)` ⇒ rename to `results.jsonl.stale-<suffix>` (SHA mismatch → the stale
    /// file's short SHA; pre-guard file with no stamp → `nostamp`). `None` ⇒ keep (no file,
    /// or the stamp matches the current SHA). Rename, never delete — preserves the forensic
    /// trail that made the phantom-regression postmortem possible.
    pub fn stale_verdict(existing_first_line: Option<&str>, current_sha: &str) -> Option<String> {
        let line = existing_first_line?;
        match parse_sha(line) {
            Some(sha) if sha == current_sha => None,
            Some(sha) => Some(sha.chars().take(8).collect()),
            None => Some("nostamp".to_string()),
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn boc1_provenance_stamp_and_stale_verdict() {
            let l = line("d2c4f828abcdef", false, 1_700_000_000);
            assert!(l.starts_with("{\"_provenance\":"), "line-1 object: {l}");
            assert_eq!(parse_sha(&l).as_deref(), Some("d2c4f828abcdef"));
            assert!(line("abc", true, 1).contains("\"dirty\":true"), "dirty flag carried");
            // A data row is not a provenance stamp.
            assert_eq!(parse_sha("{\"program\":\"bst\",\"mode\":\"bo\"}"), None);
            // Fresh (SHA matches) → keep; no file → keep.
            assert_eq!(stale_verdict(Some(&l), "d2c4f828abcdef"), None);
            assert_eq!(stale_verdict(None, "d2c4f828abcdef"), None);
            // SHA mismatch → move aside under the STALE file's short SHA.
            assert_eq!(stale_verdict(Some(&l), "ffffffffffff").as_deref(), Some("d2c4f828"));
            // Pre-guard file (no stamp) → move aside as `nostamp` (the phantom-regression case).
            assert_eq!(
                stale_verdict(Some("{\"program\":\"bst\"}"), "d2c4f828abcdef").as_deref(),
                Some("nostamp"),
            );
        }
    }
}

/// MIRROR of `analyses::borrow_ownership::borrow_verify::verify_to_fixpoint`
/// (plus its private helpers `round_cap`, `representative`,
/// `guard_slots_are_ref`) with round/commit counters added. MUST stay
/// semantically identical to the original — enforced by the non-ignored
/// `boc1_mirror_matches_real_*` tests below. On divergence, fix the mirror.
mod mirror {
    use rustc_hash::FxHashMap;
    use rustc_span::def_id::LocalDefId;
    use z3::ast::Bool;

    use crate::analyses::borrow_ownership::{
        SlotKind,
        borrow_verify::{SlotConflict, revalidate_replaying},
        coherence::constrain_field_ownership,
        crate_slots::CrateSlots,
        mutability_facts::MutProvider,
        solver::{KindSolver, Selectors, SlotRef},
    };
    use crate::utils::rustc::RustProgram;

    #[derive(Clone, Debug, Default)]
    pub struct RoundStats {
        /// Validate rounds run, INCLUDING the accepting round (a fixture that
        /// accepts its first model has `rounds == 1`).
        pub rounds: usize,
        /// §NB0: source commits no longer exist — the BB3-a `¬ref(source)`
        /// invariant is emitted eagerly, so every commit is a conflict commit.
        pub commits_conflict: usize,
        pub commits_per_round: Vec<usize>,
        /// §NB-F: sink selectors the FINAL solve dropped (leaked frees).
        /// Observation-only, from `model_kinds_relaxing_reporting` (whose
        /// plain twin the real loop uses with identical semantics); stored as
        /// counts, not `Bool`s, so results stay `Send` across `run_compiler`.
        pub dropped_sinks: usize,
        /// §NB-F: source selectors the FINAL solve dropped (leaked allocs).
        pub dropped_sources: usize,
    }

    /// Mirror of `borrow_verify::verify_to_fixpoint`. Differences: the round
    /// loop counts into `RoundStats`, and `None` (decline) carries the stats of
    /// the rounds that did run.
    pub fn verify_to_fixpoint_counting(
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        solver: &KindSolver,
        selectors: &Selectors,
        is_mutable: impl MutProvider + Copy,
    ) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
        // §NB-R guard — mirrors the real loop's release-active refusal of
        // tracked solvers (kept in lockstep with borrow_verify.rs).
        assert!(
            solver.tracker().is_none(),
            "tracked KindSolver must not enter verify_to_fixpoint (constraints are track-gated)"
        );
        // §NB-F: classify a dropped-selector set into leak counts.
        let record_dropped = |stats: &mut RoundStats, dropped: &[Bool]| {
            stats.dropped_sinks = dropped.iter().filter(|d| selectors.is_sink(d)).count();
            stats.dropped_sources = dropped.len() - stats.dropped_sinks;
        };
        let mut stats = RoundStats::default();
        let cap = round_cap(slots);
        constrain_field_ownership(solver, slots, program);
        let Some((mut model, dropped)) =
            solver.model_kinds_relaxing_reporting(selectors)
        else {
            return (None, stats);
        };
        record_dropped(&mut stats, &dropped);
        for _ in 0..cap {
            stats.rounds += 1;
            let conflicts = revalidate_replaying(
                program,
                slots,
                |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref),
                |s: SlotRef| model.get(&s) != Some(&SlotKind::Ref),
                is_mutable,
            );
            assert!(
                guard_slots_are_ref(&conflicts, &model),
                "every residual conflict slot must be Ref in the current model"
            );
            let mut committed = 0;
            for conflict in conflicts.values().flatten() {
                if let Some(slot) = representative(conflict, &model) {
                    solver.add_borrow_exclusion(Some(slot), &[]);
                    committed += 1;
                    stats.commits_conflict += 1;
                }
            }
            stats.commits_per_round.push(committed);
            if committed == 0 {
                return (Some(model), stats);
            }
            model = match solver.model_kinds_relaxing_reporting(selectors) {
                Some((m, dropped)) => {
                    record_dropped(&mut stats, &dropped);
                    m
                }
                None => return (None, stats),
            };
        }
        panic!("BOC1 mirror: CEGAR did not converge within {cap} rounds");
    }

    /// Copy of `borrow_verify::representative` — INCLUDING §NB4-4a A′ (live-requirer discharge).
    /// Must stay byte-equivalent in behavior to the original or the corpus sweep silently reports
    /// a different model than the suite verifies (the mirror-drift liability NB7 retires).
    fn representative(
        conflict: &SlotConflict,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> Option<SlotRef> {
        let is_ref = |s: &SlotRef| model.get(s) == Some(&SlotKind::Ref);
        // A′: a live `Ref` requirer BEYOND the issuer must carry the discharge.
        if let Some(r) = conflict
            .requirers
            .iter()
            .copied()
            .find(|r| Some(*r) != conflict.issuer && is_ref(r))
        {
            return Some(r);
        }
        conflict
            .issuer
            .into_iter()
            .chain(conflict.requirers.iter().copied())
            .find(is_ref)
    }

    /// Copy of `borrow_verify::round_cap`.
    fn round_cap(slots: &CrateSlots) -> usize {
        let n: usize = slots.field_slots.len()
            + slots.fn_local_slots.values().map(|u| u.len()).sum::<usize>();
        n + 8
    }

    /// Copy of `borrow_verify::guard_slots_are_ref`.
    fn guard_slots_are_ref(
        conflicts: &FxHashMap<LocalDefId, Vec<SlotConflict>>,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> bool {
        conflicts.values().flatten().all(|c| {
            c.issuer
                .iter()
                .chain(c.requirers.iter())
                .all(|s| model.get(s) == Some(&SlotKind::Ref))
        })
    }
}

/// Per-mode analysis drivers producing report rows.
mod run {
    use std::time::{Duration, Instant};

    use rustc_hash::FxHashSet;
    use rustc_middle::ty::TyCtxt;
    use z3::{SatResult, ast::Bool};

    use super::{collect_program, mirror, report::Row};
    use crate::analyses::{
        borrow::{GBorrowInferCtxt, demote_pointers_iterative_with_fields},
        borrow_ownership::{
            CrateCtxt, SafeMonoMode, SlotKind,
            borrow_verify::verify_to_fixpoint,
            coherence::add_coherence,
            crate_slots::CrateSlots,
            emit_crate_ownership_constraints,
            mutability_facts::{MutFacts, MutFactsMode},
            origins::compute_origins,
            slots::{SlotId, SlotOwner},
            solver::{KindSolver, Selectors, SlotRef},
            sources::collect_malloc_source_slots,
        },
    };

    fn secs(d: Duration) -> String {
        format!("{:.3}", d.as_secs_f64())
    }

    fn phase(name: &str, since: Instant) {
        eprintln!("BOC1PHASE {name} t={:.2}", since.elapsed().as_secs_f64());
    }

    /// BO mode: the exact `assert_ownership_parity` construction, with the
    /// mirrored fixpoint loop for round/commit counts, per-phase timings, and
    /// the model readout (kind tallies + leaked sources).
    pub fn run_bo(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));

        let program = collect_program(tcx);
        row.set("fn_count", program.functions.len());
        row.set("struct_count", program.structs.len());

        // §NB3-3c-i: signature-origin summaries — computed ONCE per program here, kind-independent,
        // and NOT yet injected into the borrow replay (compute-only; fork == production preserved).
        // This is the single driver call site the runs-once invariant (`ORIGIN_WRAP_COUNT`) pins;
        // 3c-ii threads `_origins` into the replay's subset input. `t_origins_s` is reported so the
        // sweep can watch origin-derivation cost (brotli specifically — plan §3d numeric stop).
        let t = Instant::now();
        let origins = compute_origins(&program);
        row.set("t_origins_s", secs(t.elapsed()));
        // §NB3-3c-i brotli-scale stop instrumentation (plan §3d). `origin_slots` IS the origin-count
        // metric for the stop (≤ ~10× signature slots): at 3c-i origins reuse `lifetime_flow`'s
        // signature slots 1:1, so origin_slots == the signature-slot count (ratio 1.0). `subset_edges`
        // reports the transitive-closure size (the real space concern at brotli scale). Both are
        // read-only over the still-UNINJECTED summaries — no effect on the replay / n_ref.
        row.set("origin_slots", origins.values().map(|s| s.slots.len()).sum::<usize>());
        row.set(
            "origin_subset_edges",
            origins
                .values()
                .map(|s| {
                    s.subset.rows().map(|r| s.subset.row(r).map_or(0, |b| b.iter().count())).sum::<usize>()
                })
                .sum::<usize>(),
        );
        // §NB3-3c-i F5 (Codex): the other retained-footprint dimension besides slots/subset edges is
        // the poisoned-slot set. (Storage is no longer a separate matrix — it folds into subset, F4 —
        // so there is no separate storage-edge count to report.)
        row.set("origin_unknown_slots", origins.values().map(|s| s.unknown.count()).sum::<usize>());
        let _origins = origins; // uninjected at 3c-i; 3c-ii threads this into the replay's subset input

        // §NB3-3c-i measurement seam: origins-only mode returns before the fixpoint solve, so the
        // origin-derivation cost (t_origins) and size (origin_slots/origin_subset_edges) can be
        // sampled at brotli scale without paying the ~minutes-long z3 fixpoint. Off by default —
        // no effect on any normal sweep run. Reused verbatim at 3c-ii's double-sweep origins-watch.
        if std::env::var_os("CRAT_BOC1_ORIGINS_ONLY").is_some() {
            row.set("status", "origins-only");
            return row;
        }

        // MIR warm-up: forces the (memoized) query per fn so `t_slots`/`t_emit`
        // below time the analysis, not rustc's MIR pipeline. Result-neutral.
        let t = Instant::now();
        for &g in &program.functions {
            let _ = tcx.mir_drops_elaborated_and_const_checked(g);
        }
        row.set("t_mir_s", secs(t.elapsed()));
        phase("mir_done", t0);

        let t = Instant::now();
        let slots = CrateSlots::build(&program);
        row.set("t_slots_s", secs(t.elapsed()));
        let slots_total: usize = slots.field_slots.len()
            + slots.fn_local_slots.values().map(|u| u.len()).sum::<usize>();
        row.set("slots_total", slots_total);
        phase("slots_done", t0);

        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let t = Instant::now();
        let (stats, selectors) =
            match emit_crate_ownership_constraints(&crate_ctxt, &slots, &solver) {
                Ok(x) => x,
                Err(e) => {
                    row.set("status", "emit-error");
                    row.set("err", format!("{e:#}"));
                    return row;
                }
            };
        row.set("t_emit_s", secs(t.elapsed()));
        row.set("z3_ast_len", stats.z3_ast_len);
        row.set("source_sink_emissions", stats.source_sink_emissions);
        row.set("selectors", selectors.all().len());
        // §NB1: record the active safety-monotonicity mode so the ablation
        // sweeps (per_site vs chain) are self-labeling in the results.
        row.set("safe_mono", SafeMonoMode::current().label());
        // §NB2: record the active mutability-facts mode (on = fact-driven immutability from
        // Foster; off = pre-NB2 forced-mut) so the dual-mode sweep is self-labeling.
        row.set("mut_facts", MutFactsMode::current().label());
        phase("emit_done", t0);

        let t = Instant::now();
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        row.set("t_coherence_s", secs(t.elapsed()));
        phase("coherence_done", t0);

        // §NB2: build the per-local mutability oracle once (production-parity map). Mode Off
        // reproduces pre-NB2 forced-mut; the borrow replay reads it per pointer local.
        let t = Instant::now();
        let mut_facts = match MutFactsMode::current() {
            MutFactsMode::Off => MutFacts::all_mut(),
            MutFactsMode::On => MutFacts::from_program(&program),
        };
        row.set("t_mut_facts_s", secs(t.elapsed()));

        let t = Instant::now();
        let (model, rstats) =
            mirror::verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, &mut_facts);
        row.set("t_fixpoint_s", secs(t.elapsed()));
        phase("fixpoint_done", t0);

        row.set("rounds", rstats.rounds);
        row.set("commits_conflict", rstats.commits_conflict);
        row.set(
            "commits_per_round",
            rstats
                .commits_per_round
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join("/"),
        );

        let sources = collect_malloc_source_slots(program.tcx, &program.functions, &slots);
        row.set("sources_total", sources.len());

        // §NB-F: selector-level leak accounting (SLOT-level `sources_leaked`
        // below is unchanged). `sinks_leaked` counts frees the relax loop
        // dropped — leak-the-free semantics, the stage-1 headline metric.
        row.set("sinks_total", selectors.sinks().len());
        row.set("sinks_leaked", rstats.dropped_sinks);
        row.set("sources_leaked_sel", rstats.dropped_sources);

        match &model {
            None => {
                row.set("status", "decline");
                row.set("decline_reason", decline_reason(&solver, &selectors));
                // §NB-R (opt-in): explain the decline via a second, TRACKED
                // construction — labeled minimal core (or family histogram at
                // scale). Never on the default path: doubles solve cost.
                if std::env::var("CRAT_BOC1_EXPLAIN").map(|v| v == "1").unwrap_or(false) {
                    let t = Instant::now();
                    match super::explain::explain_unsat(tcx) {
                        super::explain::Explained::Unsat { core, minimized } => {
                            row.set("core_size", core.len());
                            row.set("core_minimized", minimized);
                            row.set(
                                "core_families",
                                super::explain::family_histogram(&core),
                            );
                            for label in &core {
                                eprintln!("NBRCORE {label}");
                            }
                        }
                        super::explain::Explained::Sat => {
                            row.set("core_families", "sat-in-tracked-replay");
                        }
                        super::explain::Explained::Unknown => {
                            row.set("core_families", "z3-unknown-in-tracked-replay");
                        }
                    }
                    row.set("t_explain_s", secs(t.elapsed()));
                    phase("explain_done", t0);
                }
            }
            Some(m) => {
                let (mut n_ref, mut n_raw, mut n_own) = (0usize, 0usize, 0usize);
                let (mut n_ref_d0, mut n_raw_d0, mut n_own_d0) = (0usize, 0usize, 0usize);
                // §NB2: split depth-0 Ref into shared (&T) vs mut (&mut T) via the fact map,
                // and count depth-0 slots that defaulted to Mut for lack of a fact
                // (missing-data guard — requirement #1; ~0 when the map is complete).
                let (mut n_ref_shared_d0, mut n_ref_mut_d0, mut mut_default_fires) =
                    (0usize, 0usize, 0usize);
                for (s, kind) in m {
                    match kind {
                        SlotKind::Ref => n_ref += 1,
                        SlotKind::Raw => n_raw += 1,
                        SlotKind::Owning => n_own += 1,
                    }
                    // Depth-0 LOCAL slots only: the accounting `n_ref_prod`
                    // (production baseline) is comparable with.
                    if let SlotRef::Local(fn_did, sid) = s
                        && let Some(u) = slots.fn_local_slots.get(fn_did)
                        && u.slot(*sid).depth == 0
                    {
                        match kind {
                            SlotKind::Ref => n_ref_d0 += 1,
                            SlotKind::Raw => n_raw_d0 += 1,
                            SlotKind::Owning => n_own_d0 += 1,
                        }
                        if let SlotOwner::Local(local) = u.slot(*sid).owner {
                            if mut_facts.is_defaulted(*fn_did, local) {
                                mut_default_fires += 1;
                            }
                            if *kind == SlotKind::Ref {
                                if mut_facts.is_mutable(*fn_did, local) {
                                    n_ref_mut_d0 += 1;
                                } else {
                                    n_ref_shared_d0 += 1;
                                }
                            }
                        }
                    }
                }
                let leaked = sources
                    .iter()
                    .filter(|s| m.get(s) != Some(&SlotKind::Owning))
                    .count();
                row.set("status", "ok");
                row.set("n_ref", n_ref);
                row.set("n_raw", n_raw);
                row.set("n_own", n_own);
                row.set("n_ref_d0", n_ref_d0);
                row.set("n_raw_d0", n_raw_d0);
                row.set("n_own_d0", n_own_d0);
                // §NB2: &T vs &mut split of n_ref_d0 (shared + mut == n_ref_d0), plus the
                // count of depth-0 slots that fell back to the Mut default.
                row.set("n_ref_shared_d0", n_ref_shared_d0);
                row.set("n_ref_mut_d0", n_ref_mut_d0);
                row.set("mut_default_fires", mut_default_fires);
                row.set("sources_leaked", leaked);
            }
        }

        // Optional corpus-level fidelity cross-check (CRAT_BOC1_CHECK_REAL=1):
        // run the REAL `verify_to_fixpoint` on a second fresh construction and
        // compare. Doubles the solve cost — off by default; the orchestrator
        // does not set it. Same mitigation as the fixture equivalence tests,
        // extended to real inputs on demand.
        if std::env::var("CRAT_BOC1_CHECK_REAL").map(|v| v == "1").unwrap_or(false) {
            let t = Instant::now();
            let real = {
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                match emit_crate_ownership_constraints(&crate_ctxt, &slots, &solver) {
                    Ok((_s, selectors)) => {
                        for &g in &program.functions {
                            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                            add_coherence(&solver, &slots, g, &body);
                        }
                        // §NB2: same oracle as the mirror above, so the fidelity check
                        // compares like with like (mirror facts vs real facts).
                        Some(verify_to_fixpoint(&program, &slots, &solver, &selectors, &mut_facts))
                    }
                    Err(_) => None,
                }
            };
            phase("check_real_done", t0);
            match real {
                None => row.set("real_status", "emit-error"),
                Some(real) => {
                    row.set(
                        "real_status",
                        if real.is_some() { "ok" } else { "decline" },
                    );
                    row.set(
                        "mirror_matches_real",
                        (real == model).to_string(),
                    );
                }
            }
            row.set("t_check_real_s", secs(t.elapsed()));
        }

        row.set("t_total_s", secs(t0.elapsed() + t_tcx));
        row
    }

    /// Harness-side diagnostic for a `decline` (Codex review F7): distinguish
    /// "the constraint system is UNSAT for non-source reasons" from "z3 gave
    /// up (Unknown)" by replaying `model_kinds_relaxing`'s phase-1 selector
    /// dropping read-only (`check` with assumptions asserts nothing). Runs on
    /// the solver state at the moment of decline, so for a round-0 decline it
    /// replays exactly the failing first solve. §S2-1: the replay mirrors the
    /// real loop's sinks-first drop priority (lockstep with `solver.rs`).
    pub(super) fn decline_reason(solver: &KindSolver, selectors: &Selectors) -> &'static str {
        // §NB-R guard (Codex F1): this replay assumes ONLY selectors; under a
        // tracked solver the hard constraints would be disabled and the reply
        // would be a bogus "sat-in-replay".
        assert!(
            solver.tracker().is_none(),
            "tracked KindSolver must not enter decline_reason (constraints are track-gated)"
        );
        let mut assumptions: Vec<Bool> = selectors.all().to_vec();
        loop {
            match solver.optimize().check(&assumptions) {
                // Should not happen (relaxing declined); a nondeterministic
                // Unknown->Sat flip lands here rather than lying.
                SatResult::Sat => return "sat-in-replay",
                SatResult::Unknown => return "z3-unknown",
                SatResult::Unsat => {
                    let core = solver.optimize().get_unsat_core();
                    let in_core = |s: &Bool| core.iter().any(|c| c == s);
                    match assumptions
                        .iter()
                        .position(|s| selectors.is_sink(s) && in_core(s))
                        .or_else(|| assumptions.iter().position(|s| in_core(s)))
                    {
                        Some(i) => {
                            assumptions.swap_remove(i);
                        }
                        None => return "unsat-nonsource",
                    }
                }
            }
        }
    }

    /// Production baseline: the independent greedy driver `assert_borrow_parity`
    /// uses (tests.rs) — `demote_pointers_iterative_with_fields` from all-Ref —
    /// mapped to depth-0 slots with the same accounting as `n_ref_d0`.
    pub fn run_prod(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));

        let program = collect_program(tcx);
        let t = Instant::now();
        for &g in &program.functions {
            let _ = tcx.mir_drops_elaborated_and_const_checked(g);
        }
        row.set("t_mir_s", secs(t.elapsed()));
        phase("mir_done", t0);

        // Same slot universe as BO mode so depth-0 accounting is identical.
        let slots = CrateSlots::build(&program);
        let mut n_slots_d0 = 0usize;
        for u in slots.fn_local_slots.values() {
            for i in 0..u.len() {
                let slot = u.slot(SlotId::from_usize(i));
                if slot.depth == 0 && matches!(slot.owner, SlotOwner::Local(_)) {
                    n_slots_d0 += 1;
                }
            }
        }
        row.set("n_slots_d0", n_slots_d0);
        phase("slots_done", t0);

        let t = Instant::now();
        let mut ctxt = GBorrowInferCtxt::new(&program, |_| |_| true, |_| |_| true);
        let d_prod = demote_pointers_iterative_with_fields(&program, &mut ctxt);
        row.set("t_prod_s", secs(t.elapsed()));
        phase("prod_done", t0);

        // Verbatim mapping from tests.rs `assert_borrow_parity`.
        let mut prod_slots: FxHashSet<SlotRef> = FxHashSet::default();
        for (g, dem) in &d_prod.locals {
            let Some(universe) = slots.fn_local_slots.get(g) else {
                continue;
            };
            for local in dem.iter() {
                if let Some(sid) = universe.slot_for_local_depth(local, 0) {
                    prod_slots.insert(SlotRef::Local(*g, sid));
                }
            }
        }
        row.set("n_demoted_prod", prod_slots.len());
        row.set("n_ref_prod", n_slots_d0 - prod_slots.len());
        row.set("status", "ok");
        row.set("t_total_s", secs(t0.elapsed() + t_tcx));
        row
    }

    /// §NB3-3c-i runs-once invariant: the driver (`run_bo`) computes signature origins EXACTLY ONCE
    /// per program, kind-independent. `ORIGIN_WRAP_COUNT` is thread-local, so this before/after delta
    /// around a single `run_bo` call — all on one compiler-callback thread — is race-free under the
    /// suite's parallel (thread-local rustc-session) test execution. Guards against a future refactor
    /// that recomputes origins per-kind / per-fn / per-query (which would push the delta above 1).
    #[test]
    fn origins_runs_once_per_program() {
        use crate::analyses::borrow_ownership::origins::ORIGIN_WRAP_COUNT;
        ::utils::compilation::run_compiler_on_str(
            "unsafe fn id(p: *mut i32) -> *mut i32 { p }\n\
             unsafe fn f(p: *mut i32) -> *mut i32 { id(p) }",
            |tcx| {
                let before = ORIGIN_WRAP_COUNT.with(|c| c.get());
                let _row = run_bo(tcx, Duration::ZERO);
                let delta = ORIGIN_WRAP_COUNT.with(|c| c.get()) - before;
                assert_eq!(
                    delta, 1,
                    "compute_origins must run exactly once per program on the analysis path \
                     (kind-independent); the driver made {delta} calls"
                );
            },
        )
        .unwrap_or_else(|e| e.raise());
    }
}

// ---------------------------------------------------------------------------
// Mirror-fidelity guards (non-ignored: they run in every `cargo test`).
// ---------------------------------------------------------------------------

/// What `assert_mirror_matches` observed, for fixture-specific assertions.
#[cfg(test)]
struct MirrorOutcome {
    accepted: bool,
    stats: mirror::RoundStats,
    /// Malloc-source slots (propagation-closed count).
    sources: usize,
    /// Source slots whose final kind is not `Owning`.
    leaked: usize,
    /// Source slots whose final kind is `Ref` — must be 0 in every accepted
    /// model (§NB0 eager `¬ref`); combined with `leaked`, proves a leaked
    /// source settled `Raw`.
    sources_ref: usize,
    /// §NB-F: sink selectors the final solve dropped (leaked frees).
    dropped_sinks: usize,
    /// §NB-F: source selectors the final solve dropped (leaked allocs).
    dropped_sources: usize,
}

/// Runs both the REAL `verify_to_fixpoint` and the mirror on independent fresh
/// constructions over one compiled snippet; asserts model equality; returns the
/// mirror's stats + source/leak accounting for fixture-specific assertions.
#[cfg(test)]
fn assert_mirror_matches(code: &str) -> MirrorOutcome {
    use crate::analyses::borrow_ownership::{
        CrateCtxt, SlotKind, borrow_verify::verify_to_fixpoint, coherence::add_coherence,
        crate_slots::CrateSlots, emit_crate_ownership_constraints, solver::KindSolver,
        sources::collect_malloc_source_slots,
    };

    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = collect_program(tcx);
        // One slot universe: `CrateSlots::build` is deterministic, but sharing
        // it removes any doubt that SlotIds line up across the two models.
        let slots = CrateSlots::build(&program);

        let real = {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, selectors) = emit_crate_ownership_constraints(&crate_ctxt, &slots, &solver)
                .expect("real: emission");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
        };

        let (mirrored, stats) = {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, selectors) = emit_crate_ownership_constraints(&crate_ctxt, &slots, &solver)
                .expect("mirror: emission");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            mirror::verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, true)
        };

        match (&real, &mirrored) {
            (Some(a), Some(b)) => {
                if a != b {
                    for (s, k) in a {
                        if b.get(s) != Some(k) {
                            eprintln!("mirror diff at {s:?}: real={k:?} mirror={:?}", b.get(s));
                        }
                    }
                    panic!("mirror model != real model");
                }
            }
            (None, None) => {}
            _ => panic!(
                "mirror accept/decline mismatch: real={} mirror={}",
                real.is_some(),
                mirrored.is_some()
            ),
        }

        let sources = collect_malloc_source_slots(program.tcx, &program.functions, &slots);
        let count_kind = |pred: &dyn Fn(Option<&SlotKind>) -> bool| {
            mirrored
                .as_ref()
                .map(|m| sources.iter().filter(|s| pred(m.get(s))).count())
                .unwrap_or(0)
        };
        let (dropped_sinks, dropped_sources) = (stats.dropped_sinks, stats.dropped_sources);
        MirrorOutcome {
            accepted: mirrored.is_some(),
            stats,
            sources: sources.len(),
            leaked: count_kind(&|k| k != Some(&SlotKind::Owning)),
            sources_ref: count_kind(&|k| k == Some(&SlotKind::Ref)),
            dropped_sinks,
            dropped_sources,
        }
    })
    .unwrap_or_else(|e| e.raise())
}

/// (a) Accept-first-model path: alloc+free settles Owning with no commits.
#[test]
fn boc1_mirror_matches_real_alloc_free() {
    let o = assert_mirror_matches(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn f() {
    let p = malloc(4);
    free(p);
}
"#,
    );
    assert!(o.accepted);
    assert_eq!(o.stats.rounds, 1, "first model accepted: exactly one validate round");
    assert_eq!(o.stats.commits_conflict, 0);
    // `sources_total` counts source SLOTS (propagation-closed), not allocations:
    // the one malloc yields its destination `p` PLUS the `free(p)` call-arg temp.
    assert_eq!((o.sources, o.leaked), (2, 0), "the freed alloc is retained, not leaked");
}

/// (b) Conflict-commit cascade: two `&mut` of one base force iterated commits.
#[test]
fn boc1_mirror_matches_real_conflict_cascade() {
    let o = assert_mirror_matches(
        r#"
pub unsafe fn f() {
    let mut local = 0i32;
    let x = &mut local as *mut i32;
    let y = &mut local as *mut i32;
    *x = 1;
    *y = 2;
}
"#,
    );
    assert!(o.accepted);
    assert!(o.stats.rounds >= 2, "cascade must iterate; got {} rounds", o.stats.rounds);
    assert!(o.stats.commits_conflict >= 1, "at least one conflict commit");
}

/// (c) Selector-drop (leak) path under §NB0's EAGER `¬ref(source)`: the leaked
/// malloc's selector is dropped by `model_kinds_relaxing`, and — because the
/// hoisted BB3-a constraint is present from emission — the source can never
/// float to `Ref`: it is `Raw` from the very first model. That first model's
/// union replay (source now a raw candidate in round 1, where the old
/// trajectory only reached this state after its round-1 source commit)
/// surfaces ONE borrow conflict, whose commit yields the accepted round-2
/// model: rounds == 2, commits_conflict == 1, no source commits (the field is
/// gone). Guards the headline `sources_leaked` accounting end-to-end.
/// (Final-kind `Raw` on the real path is independently pinned by
/// tests.rs::bb3a_leaked_source_forced_raw.)
#[test]
fn boc1_mirror_matches_real_leaked_source() {
    let o = assert_mirror_matches(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { malloc(8) };
    &raw mut p
}
"#,
    );
    assert!(o.accepted);
    assert_eq!(
        (o.stats.rounds, o.stats.commits_conflict),
        (2, 1),
        "eager ¬ref: round-1 model has the source Raw; its union replay surfaces \
         one conflict, committed into the accepted round-2 model"
    );
    assert_eq!((o.sources, o.leaked), (1, 1), "the leaked alloc must be counted leaked");
    assert_eq!(o.sources_ref, 0, "a source may never end Ref (leaked ⇒ Raw)");
}

/// (d) Maximal-source-retention: of two allocations only the conflicting one
/// leaks (1-of-2 accounting).
#[test]
fn boc1_mirror_matches_real_two_allocs_one_leak() {
    let o = assert_mirror_matches(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn two_allocs() -> *mut *mut core::ffi::c_void {
    let a = unsafe { malloc(8) };
    unsafe { free(a) };
    let mut b = unsafe { malloc(8) };
    &raw mut b
}
"#,
    );
    assert!(o.accepted);
    // Slot-level source accounting: `a` + its `free(a)` call-arg temp + `b` = 3
    // source slots for 2 allocations; only `b`'s slot leaks (kind != Owning).
    assert_eq!((o.sources, o.leaked), (3, 1), "exactly the conflicting alloc leaks");
    assert_eq!(o.sources_ref, 0, "no source may end Ref");
}

/// The smallest confirmed real-corpus decliner (bst `deleteNode`, bisect-
/// minimized) — shared by the decline fixture and the §NB-R explain tests.
#[cfg(test)]
const DELETE_NODE_WITNESS: &str = r#"
unsafe extern "C" {
    fn free(ptr: *mut core::ffi::c_void);
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct node {
    pub key: i32,
    pub left: *mut node,
    pub right: *mut node,
}

pub unsafe fn delete_node(mut root: *mut node, mut key: i32) -> *mut node {
    if root.is_null() {
        return root;
    }
    if key < (*root).key {
        (*root).left = delete_node((*root).left, key);
    } else if key > (*root).key {
        (*root).right = delete_node((*root).right, key);
    } else {
        if ((*root).left).is_null() {
            let mut temp: *mut node = (*root).right;
            free(root as *mut core::ffi::c_void);
            return temp;
        } else if ((*root).right).is_null() {
            let mut temp_0: *mut node = (*root).left;
            free(root as *mut core::ffi::c_void);
            return temp_0;
        }
        let mut temp_1: *mut node = (*root).right;
        (*root).key = (*temp_1).key;
        (*root).right = delete_node((*root).right, (*temp_1).key);
    }
    return root;
}
"#;

/// §NB-F stage 1 — the deleteNode witness under LEAK-THE-FREES semantics.
/// (Flipped from NB-R's decline fixture when sinks became retractable —
/// option (a), approved at the NB-R gate. History: this shape was the
/// bisect-minimized Family-A witness; NB-R's core showed its ONLY forced
/// owning was the free sink, so retraction dissolves the UNSAT.)
/// The relax loop drops both free-sink selectors (an unprovable free stays a
/// raw free); with no malloc there are no source selectors; mirror and real
/// loop must agree and ACCEPT. The freed value's final kind is an OBSERVED
/// pin (see the assertion comment), not a design guarantee: dropping a sink
/// selector asserts neither ¬own nor ¬ref.
#[test]
fn boc1_mirror_matches_real_delete_node_leaked_frees() {
    use rustc_middle::mir::Local;

    use crate::analyses::borrow_ownership::{
        CrateCtxt, SlotKind, borrow_verify::verify_to_fixpoint, coherence::add_coherence,
        crate_slots::CrateSlots, emit_crate_ownership_constraints,
        solver::{KindSolver, SlotRef},
    };

    let o = assert_mirror_matches(DELETE_NODE_WITNESS);
    assert!(o.accepted, "retractable sinks: the witness must accept");
    assert_eq!(
        (o.dropped_sinks, o.dropped_sources),
        (2, 0),
        "exactly the two frees leak; there are no sources to leak"
    );
    assert_eq!(o.sources, 0, "no malloc in the shape");

    // The freed-value observation (stage-2 residual, recorded not fixed): what
    // does leaked-free `root` settle to under the max-ref objective?
    ::utils::compilation::run_compiler_on_str(DELETE_NODE_WITNESS, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_s, selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &solver).expect("emission");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
            .expect("accepts under retractable sinks");
        let f = program.functions[0];
        let root = SlotRef::Local(
            f,
            slots.fn_local_slots[&f]
                .slot_for_local_depth(Local::from_u32(1), 0)
                .expect("root (_1) has a depth-0 slot"),
        );
        // OBSERVED pin (2026-07-04, not a design guarantee): leaked-free
        // `root` settles `Raw` — the CEGAR replay polices the `Ref` reading
        // even with the sink retracted (root-as-Ref surfaces aliasing
        // conflicts through the recursion). A leaked free CAN in principle
        // settle `Ref` where no conflict surfaces — the named stage-2
        // residual; the corpus sweep counts freed-`Ref` occurrences before
        // codegen may trust this.
        assert_eq!(
            model.get(&root),
            Some(&SlotKind::Raw),
            "observed leaked-free kind changed — revisit the stage-2 residual note"
        );
    })
    .unwrap_or_else(|e| e.raise());
}

/// §NB-F stage 1 (option (a), approved at the NB-R gate) — the CAUSAL flip:
/// with `free`/`realloc` sink owning selector-gated, the deleteNode witness
/// must ACCEPT under the REAL `verify_to_fixpoint` — the relax loop drops the
/// two free-sink selectors (leak-the-frees: an unprovable free stays a raw
/// free) and, with no malloc in the shape, nothing else forces owning.
/// Deliberately NO assertion on the freed values' final kinds: dropping a sink
/// selector removes forced owning but asserts neither ¬own nor ¬ref (there is
/// no sink analogue of NB0's eager ¬ref(source), by design) — the observed
/// final kind is recorded in the task doc, not pinned here.
#[test]
fn nbf_sink_retractable_delete_node() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt, borrow_verify::verify_to_fixpoint, coherence::add_coherence,
        crate_slots::CrateSlots, emit_crate_ownership_constraints, solver::KindSolver,
    };

    ::utils::compilation::run_compiler_on_str(DELETE_NODE_WITNESS, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_s, selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &solver).expect("emission");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true);
        assert!(
            model.is_some(),
            "retractable sinks: the witness must ACCEPT (its only forced owning \
             was the free sink, now selector-dropped)"
        );
    })
    .unwrap_or_else(|e| e.raise());
}

// ---------------------------------------------------------------------------
// §NB-R — tracked-core explain driver (diagnosis only; no analysis change).
// ---------------------------------------------------------------------------

/// Explains why the BO system is infeasible on a crate, using a TRACKED
/// `KindSolver` (`new_tracked`): every hard constraint is `track ⇒ c`, the
/// solve is `check(&[tracks ∪ source selectors])`, and on UNSAT the core's
/// track literals map back to labeled emission sites.
mod explain {
    use rustc_middle::ty::TyCtxt;
    use z3::{SatResult, ast::Bool};

    use super::collect_program;
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        coherence::{add_coherence, constrain_field_ownership},
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        solver::{CORE_LABEL_FAMILIES, KindSolver},
    };

    pub enum Explained {
        Sat,
        Unknown,
        Unsat {
            /// Labeled core (`{context}::{family}(…)` strings). When
            /// `minimized`, this set has been drop-restore minimized AND
            /// re-checked UNSAT on its own (a raw z3 core is not minimal;
            /// an unverified "minimal" core would poison the diagnosis).
            core: Vec<String>,
            /// False only when the size cap was hit (histogram-scale core);
            /// the labels are then the RAW core.
            minimized: bool,
        },
    }

    /// Cap above which minimization is skipped (brotli-scale safety) and the
    /// raw core is returned for histogram use only.
    pub const MINIMIZE_CAP: usize = 50;

    /// Build the full tracked BO system over the crate (emission + coherence +
    /// the §9.10.2 field law — exactly what the real pipeline has asserted by
    /// the time of its FIRST solve inside `verify_to_fixpoint`, which is where
    /// every round-0 corpus decline happens) and explain that first solve.
    pub fn explain_unsat(tcx: TyCtxt<'_>) -> Explained {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new_tracked(&slots);
        let (_stats, selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &solver)
                .expect("NB-R: tracked emission");
        let tracker = solver.tracker().expect("new_tracked");
        tracker.set_context("coherence");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        tracker.set_context("field-law");
        constrain_field_ownership(&solver, &slots, &program);

        // Solve with EVERY track assumed (⇔ the untracked hard system) plus
        // the source selectors (the hard-source reading, as in the real
        // pipeline's first solve).
        let tracks = tracker.tracks();
        let mut assumptions: Vec<Bool> = tracks;
        assumptions.extend(selectors.all().iter().cloned());
        match solver.optimize().check(&assumptions) {
            SatResult::Sat => Explained::Sat,
            SatResult::Unknown => Explained::Unknown,
            SatResult::Unsat => {
                let mut core: Vec<Bool> = solver.optimize().get_unsat_core();
                let minimized = if core.len() <= MINIMIZE_CAP {
                    // Destructive drop-restore minimization: keep a literal
                    // only if removing it makes the rest SAT (i.e. it is
                    // load-bearing). z3 cores are NOT minimal (the in-repo
                    // relaxing loop documents this) — an unminimized set
                    // would over-report the contradiction. Codex F3: an
                    // Unknown on a candidate keeps the literal but forfeits
                    // the 1-minimality claim (`minimized` = false then).
                    let mut saw_unknown = false;
                    let mut i = 0;
                    while i < core.len() {
                        let mut candidate = core.clone();
                        candidate.swap_remove(i);
                        match solver.optimize().check(&candidate) {
                            SatResult::Unsat => {
                                core = candidate; // literal was redundant; slot i
                                // now holds the (unvisited) former last element.
                            }
                            SatResult::Sat => i += 1,
                            SatResult::Unknown => {
                                saw_unknown = true;
                                i += 1;
                            }
                        }
                    }
                    assert_eq!(
                        solver.optimize().check(&core),
                        SatResult::Unsat,
                        "minimized core must re-check UNSAT on its own"
                    );
                    !saw_unknown
                } else {
                    false
                };
                let labels = core
                    .iter()
                    .map(|literal| {
                        tracker.label_of(literal).unwrap_or_else(|| {
                            // Non-track core literals are selectors; §NB-F
                            // splits them by identity so a leaked-free MUS
                            // reads differently from a leaked-alloc MUS.
                            if selectors.is_sink(literal) {
                                "sink-selector".to_string()
                            } else {
                                "source-selector".to_string()
                            }
                        })
                    })
                    .collect();
                Explained::Unsat {
                    core: labels,
                    minimized,
                }
            }
        }
    }

    /// The family a label belongs to, if any (the parse contract: every label
    /// the tracker emits must contain exactly one known family tag).
    pub fn family_of(label: &str) -> Option<&'static str> {
        CORE_LABEL_FAMILIES
            .iter()
            .copied()
            .find(|family| label.contains(family))
    }

    /// KV-safe family histogram of a labeled core: `fam:count/fam:count`,
    /// ordered by count desc then name asc (deterministic).
    pub fn family_histogram(core: &[String]) -> String {
        let mut counts: Vec<(&'static str, usize)> = Vec::new();
        for label in core {
            let family = family_of(label).unwrap_or("unknown");
            match counts.iter_mut().find(|(f, _)| *f == family) {
                Some((_, n)) => *n += 1,
                None => counts.push((family, 1)),
            }
        }
        counts.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        counts
            .iter()
            .map(|(f, n)| format!("{f}:{n}"))
            .collect::<Vec<_>>()
            .join("/")
    }
}

/// §NB-R histogram format contract (pure; mechanism-only).
#[test]
fn nbr_family_histogram_format() {
    let labels: Vec<String> = vec![
        "f::own-assume(1=true)".into(),
        "g::kind-equate(x,y,own)".into(),
        "f::own-assume(2=false)".into(),
        "weird label".into(),
    ];
    assert_eq!(
        explain::family_histogram(&labels),
        "own-assume:2/kind-equate:1/unknown:1"
    );
}

/// §NB-R MECHANISM-ONLY guard on the explain driver (deliberately no
/// family-content assertions: which families appear in the witness core is
/// R2a's FINDING, recorded in the task doc — baking the pre-registered
/// hypothesis into CI would turn the most interesting outcome into a red
/// build. After R2a confirms the diagnosis, a SEPARATE regression fixture
/// pins it).
#[test]
fn nbr_core_extraction_delete_node() {
    ::utils::compilation::run_compiler_on_str(DELETE_NODE_WITNESS, |tcx| {
        match explain::explain_unsat(tcx) {
            explain::Explained::Unsat { core, minimized } => {
                assert!(!core.is_empty(), "an UNSAT explanation must name constraints");
                assert!(
                    minimized,
                    "the witness-scale core must go through drop-restore minimization \
                     (with its UNSAT re-check)"
                );
                for label in &core {
                    assert!(
                        explain::family_of(label).is_some(),
                        "core label does not parse to a known family: {label}"
                    );
                }
            }
            _ => panic!("the deleteNode witness must be UNSAT under tracks ∪ selectors"),
        }
    })
    .unwrap_or_else(|e| e.raise());
}

/// §NB-R R2a REGRESSION fixture (frozen AFTER the diagnosis was confirmed —
/// deliberately separate from the mechanism-only test above). Pins the
/// verified family composition of the witness's minimal core: the free
/// sink's owning — since §NB-F a RETRACTABLE `sink-selector` literal, no
/// longer a hard `own-assume(=true)` — reaches a never-owning temp's
/// version-zero (`own-assume(=false)`, still the sole hard pole) through
/// kind-coherence over the `node.right` field slot and both `link-own`
/// biconditionals. Explain assumes ALL selectors, so the core is still UNSAT
/// (master lemma) even though the production relax path now accepts this
/// witness by dropping the sinks. If an emission change alters this
/// contradiction surface, this fails loudly and the diagnosis in
/// docs/agents/tasks/2026-07-04-nbr-unsat-root-cause.md must be re-derived.
/// (Family HISTOGRAM only — var indices shift with MIR details and are
/// deliberately not pinned.)
#[test]
fn nbr_witness_core_family_regression() {
    ::utils::compilation::run_compiler_on_str(DELETE_NODE_WITNESS, |tcx| {
        let explain::Explained::Unsat { core, minimized } = explain::explain_unsat(tcx) else {
            panic!("witness must be UNSAT");
        };
        assert!(minimized);
        eprintln!("NBFOBS regression histogram: {}", explain::family_histogram(&core));
        assert_eq!(
            explain::family_histogram(&core),
            "kind-equate:4/link-own:2/own-equal:2/own-assume:1/own-linear:1/sink-selector:1",
            "the witness diagnosis changed — re-derive the root-cause analysis"
        );
        let trues = core.iter().filter(|l| l.contains("own-assume") && l.ends_with("=true)")).count();
        let falses = core.iter().filter(|l| l.contains("own-assume") && l.ends_with("=false)")).count();
        // §NB-F re-derivation: the sink-owning pole is now the retractable
        // `sink-selector` literal (asserted in the histogram above), so the
        // remaining hard own-assume is the version-zero alone.
        assert_eq!(
            (trues, falses),
            (0, 1),
            "the version-zero remains the hard pole; the sink pole is the sink-selector"
        );
    })
    .unwrap_or_else(|e| e.raise());
}

/// §NB-R R2a — manual core printer for the deleteNode witness. `#[ignore]`d:
/// run explicitly to (re)produce the diagnosis recorded in the task doc.
#[test]
#[ignore = "NB-R diagnosis printer: run with --exact bo_c1::nbr_print_witness_core --ignored --nocapture"]
fn nbr_print_witness_core() {
    ::utils::compilation::run_compiler_on_str(DELETE_NODE_WITNESS, |tcx| {
        match explain::explain_unsat(tcx) {
            explain::Explained::Unsat { core, minimized } => {
                eprintln!(
                    "NBRCORE witness delete_node: {} literals (minimized={minimized})",
                    core.len()
                );
                let mut sorted = core.clone();
                sorted.sort();
                for label in &sorted {
                    eprintln!("NBRCORE   {label}");
                }
            }
            explain::Explained::Sat => eprintln!("NBRCORE witness: SAT?!"),
            explain::Explained::Unknown => eprintln!("NBRCORE witness: UNKNOWN"),
        }
    })
    .unwrap_or_else(|e| e.raise());
}

/// §NB-R tracked-instance guard: a tracked solver reaching a production solve
/// path is a hard error, not a silently-vacuous solve.
#[test]
#[should_panic(expected = "tracked KindSolver must not enter model_kinds_relaxing")]
fn nbr_tracked_solver_guard_panics() {
    use crate::analyses::borrow_ownership::{crate_slots::CrateSlots, solver::KindSolver};

    ::utils::compilation::run_compiler_on_str(
        "pub unsafe fn f(p: *mut i32) { *p = 1; }",
        |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let solver = KindSolver::new_tracked(&slots);
            let _ = solver.model_kinds_relaxing(
                &crate::analyses::borrow_ownership::solver::Selectors::new(Vec::new(), Vec::new()),
            );
        },
    )
    .unwrap_or_else(|e| e.raise());
}

// ---------------------------------------------------------------------------
// Worker (one program, one mode, one process).
// ---------------------------------------------------------------------------

#[test]
#[ignore = "C1-lite worker: spawned per program by boc1_corpus (needs CRAT_BOC1_INPUT)"]
fn boc1_run_one() {
    use std::path::Path;
    use std::time::Instant;

    let Ok(input) = std::env::var("CRAT_BOC1_INPUT") else {
        eprintln!("BOC1 worker: CRAT_BOC1_INPUT unset; no-op (did you mean boc1_corpus?)");
        return;
    };
    let mode = std::env::var("CRAT_BOC1_MODE").unwrap_or_else(|_| "bo".to_string());
    let name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_string());

    let t0 = Instant::now();
    let result = ::utils::compilation::run_compiler_on_path(Path::new(&input), |tcx| {
        let t_tcx = t0.elapsed();
        match mode.as_str() {
            "bo" => run::run_bo(tcx, t_tcx),
            "prod" => run::run_prod(tcx, t_tcx),
            other => panic!("unknown CRAT_BOC1_MODE `{other}`"),
        }
    });

    let mut row = match result {
        Ok(row) => row,
        Err(_fatal) => {
            // rustc reported fatal diagnostics on stderr (in the child log).
            let mut row = report::Row::default();
            row.set("status", "compile-error");
            row.set("t_total_s", format!("{:.3}", t0.elapsed().as_secs_f64()));
            row
        }
    };
    // Prepend identity keys so every sentinel line is self-describing.
    let mut ident = report::Row::default();
    ident.set("program", &name);
    ident.set("mode", &mode);
    ident.0.extend(row.0.drain(..));
    println!("{}", report::to_kv_line(&ident));
}

// ---------------------------------------------------------------------------
// Orchestrator (spawns one worker process per program × mode).
// ---------------------------------------------------------------------------

/// CROWN/Laertes corpus present under `benchmarks/rs/`, smallest-first.
/// (crown_name, dir_name, total .rs SLOC, is_extra). `uthash` is NOT in the
/// CROWN 20 — kept as a marked extra. `lodepng` is the benchmark where CROWN
/// lost to Laertes (key point of comparison for C3).
const CORPUS: &[(&str, &str, usize, bool)] = &[
    ("bst", "bst", 96, false),
    ("avl", "avl", 121, false),
    ("ht", "ht", 271, false),
    ("buffer", "buffer-0.4.0", 1157, false),
    ("quadtree", "quadtree-0.1.0", 1167, false),
    ("urlparser", "urlparser", 1366, false),
    ("robotfindskitten", "robotfindskitten", 1511, false),
    ("genann", "genann-1.0.0", 1888, false),
    ("rgba", "rgba", 2141, false),
    ("libtree", "libtree-3.1.1", 2638, false),
    ("libcsv", "libcsv", 3102, false),
    ("json.h", "json.h", 3838, false),
    ("lil", "lil", 5616, false),
    ("bzip2", "bzip2", 14129, false),
    ("lodepng", "lodepng", 14306, false),
    ("heman", "heman", 15189, false),
    ("libzahl", "libzahl-1.0", 17604, false),
    ("tulipindicators", "tulipindicators", 24175, false),
    ("binn", "binn-3.0", 64385, false),
    ("uthash", "uthash", 82289, true),
    ("brotli", "brotli-1.0.9", 129451, false),
];

#[cfg(test)]
mod orchestrate {
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};

    use super::report::{self, Row};

    pub struct ChildOutcome {
        /// Orchestrator-level classification: ok | decline | compile-error |
        /// emit-error (from the sentinel), or timeout | oom-kill | panic |
        /// crash | no-output (from process supervision).
        pub status: String,
        pub row: Option<Row>,
        pub wall_s: f64,
        pub note: String,
    }

    fn env_u64(key: &str, default: u64) -> u64 {
        std::env::var(key)
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(default)
    }

    pub fn workspace_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    pub fn out_dir() -> PathBuf {
        std::env::var("CRAT_BOC1_OUT")
            .map(PathBuf::from)
            .unwrap_or_else(|_| workspace_root().join("target/boc1"))
    }

    /// Current commit SHA of the parent code repo, for the `results.jsonl` provenance stamp.
    /// Best-effort: `unknown` if git is unavailable.
    pub fn git_sha() -> String {
        Command::new("git")
            .args(["rev-parse", "HEAD"])
            .current_dir(workspace_root())
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "unknown".to_string())
    }

    /// Whether the working tree is dirty (informational — sweeps often run on WIP branches,
    /// so this warns rather than refuses).
    pub fn git_dirty() -> bool {
        Command::new("git")
            .args(["status", "--porcelain"])
            .current_dir(workspace_root())
            .output()
            .ok()
            .filter(|o| o.status.success())
            .map(|o| !String::from_utf8_lossy(&o.stdout).trim().is_empty())
            .unwrap_or(false)
    }

    pub fn now_unix() -> u64 {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0)
    }

    fn rss_kb(pid: u32) -> Option<u64> {
        let out = Command::new("ps")
            .args(["-o", "rss=", "-p", &pid.to_string()])
            .output()
            .ok()?;
        String::from_utf8_lossy(&out.stdout).trim().parse().ok()
    }

    /// Spawn one worker (this test binary, `--exact bo_c1::boc1_run_one`) with
    /// file-redirected stdio; supervise with deadline + RSS cap; classify.
    pub fn run_child(program: &str, input: &Path, mode: &str, timeout: Duration) -> ChildOutcome {
        let mem_cap_kb = env_u64("CRAT_BOC1_MEM_MB", 8192) * 1024;
        let logs = out_dir().join("logs");
        fs::create_dir_all(&logs).expect("create log dir");
        let out_path = logs.join(format!("{program}.{mode}.out"));
        let err_path = logs.join(format!("{program}.{mode}.err"));
        let out_file = fs::File::create(&out_path).expect("create .out log");
        let err_file = fs::File::create(&err_path).expect("create .err log");

        let exe = std::env::current_exe().expect("current_exe");
        let t0 = Instant::now();
        let mut child = Command::new(exe)
            .args(["bo_c1::boc1_run_one", "--exact", "--ignored", "--nocapture"])
            .env("CRAT_BOC1_INPUT", input)
            .env("CRAT_BOC1_MODE", mode)
            .env("CRAT_BOC1_NAME", program)
            .env("DIR", workspace_root())
            .stdin(Stdio::null())
            .stdout(Stdio::from(out_file))
            .stderr(Stdio::from(err_file))
            .spawn()
            .expect("spawn worker");

        let mut killed_for: Option<&str> = None;
        let status = loop {
            match child.try_wait().expect("try_wait") {
                Some(status) => break status,
                None => {
                    if t0.elapsed() >= timeout && killed_for.is_none() {
                        killed_for = Some("timeout");
                        let _ = child.kill();
                    } else if killed_for.is_none()
                        && t0.elapsed().as_millis() % 1000 < 200
                        && rss_kb(child.id()).is_some_and(|kb| kb > mem_cap_kb)
                    {
                        killed_for = Some("oom-kill");
                        let _ = child.kill();
                    }
                    std::thread::sleep(Duration::from_millis(200));
                }
            }
        };
        let wall_s = t0.elapsed().as_secs_f64();

        let stdout = fs::read_to_string(&out_path).unwrap_or_default();
        let stderr = fs::read_to_string(&err_path).unwrap_or_default();
        let row = stdout.lines().rev().find_map(report::parse_kv_line);
        let last_phase = stderr
            .lines()
            .filter(|l| l.starts_with("BOC1PHASE"))
            .next_back()
            .unwrap_or("BOC1PHASE none")
            .to_string();

        // A child that completed (exit 0 + sentinel) beats a raced kill: the
        // deadline/RSS branch can fire in the same poll window in which the
        // child exits, leaving `killed_for` set on an already-dead process.
        let classification = if status.code() == Some(0) && row.is_some() {
            row.as_ref()
                .and_then(|r| r.get("status"))
                .unwrap_or("no-status")
                .to_string()
        } else if let Some(reason) = killed_for {
            reason.to_string()
        } else if let Some(row) = &row {
            row.get("status").unwrap_or("no-status").to_string()
        } else {
            match status.code() {
                Some(0) => "no-output".to_string(),
                Some(_) => "panic".to_string(),
                None => "crash".to_string(),
            }
        };
        let note = if matches!(classification.as_str(), "timeout" | "oom-kill" | "panic" | "crash") {
            let tail: String = stderr
                .lines()
                .rev()
                .take(3)
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .collect::<Vec<_>>()
                .join(" | ");
            format!("{last_phase} ;; {tail}")
        } else {
            String::new()
        };

        ChildOutcome {
            status: classification,
            row,
            wall_s,
            note,
        }
    }
}

#[test]
#[ignore = "C1-lite corpus sweep: run explicitly with --exact bo_c1::boc1_corpus --ignored --nocapture"]
fn boc1_corpus() {
    use std::fs;
    use std::time::Duration;

    use orchestrate::{out_dir, run_child, workspace_root};
    use report::Row;

    let root = workspace_root();
    let deps = root.join("deps_crate/target/debug/deps");
    assert!(
        deps.is_dir(),
        "deps_crate not built at {deps:?} — run `cargo build --manifest-path deps_crate/Cargo.toml` first"
    );

    let timeout = Duration::from_secs(
        std::env::var("CRAT_BOC1_TIMEOUT_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(900),
    );
    let prod_timeout = Duration::from_secs(
        std::env::var("CRAT_BOC1_PROD_TIMEOUT_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(900),
    );
    let prod_enabled = std::env::var("CRAT_BOC1_PROD").map(|v| v != "0").unwrap_or(true);
    let only: Option<Vec<String>> = std::env::var("CRAT_BOC1_PROGRAMS")
        .ok()
        .map(|v| v.split(',').map(|s| s.trim().to_string()).collect());

    fs::create_dir_all(out_dir().join("logs")).expect("create out dir");

    // Provenance guard (NB2, 2026-07-10): stamp this run's SHA into results.jsonl (line 1)
    // and move any SHA-mismatched / unstamped prior file aside so a killed sweep cannot
    // masquerade as current data. Rename, not delete — forensic trail. See the NB2 task doc.
    let sha = orchestrate::git_sha();
    let dirty = orchestrate::git_dirty();
    let unix = orchestrate::now_unix();
    if dirty {
        eprintln!("[boc1] WARNING: working tree dirty — provenance sha {sha} is approximate");
    }
    {
        let results = out_dir().join("results.jsonl");
        let first_line = results
            .is_file()
            .then(|| fs::read_to_string(&results).ok())
            .flatten()
            .and_then(|s| s.lines().next().map(|l| l.to_string()));
        if let Some(suffix) = provenance::stale_verdict(first_line.as_deref(), &sha) {
            let stale = out_dir().join(format!("results.jsonl.stale-{suffix}"));
            fs::rename(&results, &stale).expect("rename stale results.jsonl aside");
            eprintln!("[boc1] moved stale results.jsonl aside to {stale:?} (sweep sha {sha})");
        }
    }

    let mut raw_rows: Vec<Row> = Vec::new();
    let mut merged: Vec<Row> = Vec::new();

    for &(crown_name, dir_name, sloc, extra) in CORPUS {
        if let Some(only) = &only
            && !only.iter().any(|p| p == crown_name || p == dir_name)
        {
            continue;
        }
        let input = root.join("benchmarks/rs").join(dir_name).join("c2rust-lib.rs");
        assert!(input.is_file(), "missing crate root {input:?}");

        eprintln!("[boc1] {crown_name} ({dir_name}, {sloc} SLOC): bo mode...");
        let bo = run_child(crown_name, &input, "bo", timeout);

        let mut m = Row::default();
        m.set("program", crown_name);
        m.set("dir", dir_name);
        m.set("sloc", sloc);
        if extra {
            m.set("extra", "yes");
        }
        m.set("status", &bo.status);
        m.set("wall_s", format!("{:.1}", bo.wall_s));
        if let Some(row) = &bo.row {
            for (k, v) in &row.0 {
                if !matches!(k.as_str(), "program" | "mode" | "status") {
                    m.set(k, v);
                }
            }
            raw_rows.push(row.clone());
        }
        if !bo.note.is_empty() {
            m.set("note", &bo.note);
        }

        if prod_enabled {
            eprintln!("[boc1] {crown_name}: prod mode...");
            let prod = run_child(crown_name, &input, "prod", prod_timeout);
            m.set("prod_status", &prod.status);
            m.set("prod_wall_s", format!("{:.1}", prod.wall_s));
            if let Some(row) = &prod.row {
                for key in ["n_slots_d0", "n_demoted_prod", "n_ref_prod", "t_prod_s"] {
                    if let Some(v) = row.get(key) {
                        m.set(key, v);
                    }
                }
                raw_rows.push(row.clone());
            }
            if let (Some(bo_ref), Some(prod_ref)) = (
                m.get("n_ref_d0").and_then(|v| v.parse::<i64>().ok()),
                m.get("n_ref_prod").and_then(|v| v.parse::<i64>().ok()),
            ) {
                m.set("d_ref_d0", bo_ref - prod_ref);
            }
        }

        eprintln!("[boc1] {crown_name}: {}", report::to_kv_line(&m));
        merged.push(m);

        // Persist incrementally so partial sweeps still leave artifacts. Line 1 is the
        // provenance stamp (guard above); data rows follow.
        let mut jsonl = provenance::line(&sha, dirty, unix) + "\n";
        for r in &raw_rows {
            jsonl.push_str(&report::to_json_line(r));
            jsonl.push('\n');
        }
        fs::write(out_dir().join("results.jsonl"), jsonl).expect("write jsonl");
        fs::write(out_dir().join("results.csv"), report::render_csv(&merged)).expect("write csv");
        fs::write(out_dir().join("report.md"), render_report(&merged)).expect("write report");
    }

    println!("\n{}", render_report(&merged));
}

#[cfg(test)]
fn render_report(merged: &[report::Row]) -> String {
    let cols = [
        "program",
        "sloc",
        "status",
        "wall_s",
        "t_fixpoint_s",
        "t_origins_s",
        "rounds",
        "commits_conflict",
        "slots_total",
        "n_ref",
        "n_raw",
        "n_own",
        "n_ref_d0",
        "n_ref_shared_d0",
        "n_ref_mut_d0",
        "mut_facts",
        "mut_default_fires",
        "n_ref_prod",
        "d_ref_d0",
        "sources_total",
        "sources_leaked",
        "sinks_total",
        "sinks_leaked",
        "decline_reason",
        "core_families",
        "core_minimized",
        "prod_status",
    ];
    let mut out = String::from("# C1-lite BO corpus report\n\n");
    out.push_str(
        "Corpus: CROWN 20 (Laertes set) present in `benchmarks/rs/`, smallest-first, plus \
         `uthash` as a marked extra. Name mapping: binn→binn-3.0, buffer→buffer-0.4.0, \
         quadtree→quadtree-0.1.0, genann→genann-1.0.0, libtree→libtree-3.1.1, \
         libzahl→libzahl-1.0, brotli→brotli-1.0.9 (others 1:1). `lodepng` is the benchmark \
         where CROWN lost to Laertes — key for the C3 head-to-head.\n\n\
         `d_ref_d0` = BO depth-0 local Ref count minus the production baseline's \
         (`demote_pointers_iterative_with_fields` from all-Ref, same accounting). \
         `decline_reason` separates non-source UNSAT from z3 Unknown (harness-side \
         phase-1 replay). `sources_total`/`sources_leaked` count malloc-source SLOTS \
         (propagation-closed over copies/moves/casts, so one allocation can contribute \
         several slots, e.g. its `free` call-arg temp); a slot is leaked when its final \
         kind is not Owning. `commits_conflict` counts exclusion assertions exactly as the real \
         loop's `committed` does — the same slot can be committed by several conflicts \
         in one round, so this is commit OPERATIONS, not unique slots. `d_ref_d0` is a \
         Ref-count delta, not a pure borrow-precision delta: BO's non-Ref includes \
         Owning (a win) and leaked-source Raw — read it together with `n_own`. \
         `wall_s` is supervision-level (includes up to ~200ms poll latency); \
         `t_total_s` in the CSV/JSONL is the child-measured time.\n\n",
    );
    out.push_str(&report::render_markdown(merged, &cols));
    out
}
