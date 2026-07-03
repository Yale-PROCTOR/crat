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
        solver::{KindSolver, SlotRef},
        sources::collect_malloc_source_slots,
    };
    use crate::utils::rustc::RustProgram;

    #[derive(Clone, Debug, Default)]
    pub struct RoundStats {
        /// Validate rounds run, INCLUDING the accepting round (a fixture that
        /// accepts its first model has `rounds == 1`).
        pub rounds: usize,
        pub commits_source: usize,
        pub commits_conflict: usize,
        pub commits_per_round: Vec<usize>,
    }

    /// Mirror of `borrow_verify::verify_to_fixpoint`. Differences: the round
    /// loop counts into `RoundStats`, and `None` (decline) carries the stats of
    /// the rounds that did run.
    pub fn verify_to_fixpoint_counting(
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        solver: &KindSolver,
        selectors: &[Bool],
        is_mutable: bool,
    ) -> (Option<FxHashMap<SlotRef, SlotKind>>, RoundStats) {
        let mut stats = RoundStats::default();
        let cap = round_cap(slots);
        let malloc_sources = collect_malloc_source_slots(program, slots);
        constrain_field_ownership(solver, slots, program);
        let Some(mut model) = solver.model_kinds_relaxing(selectors) else {
            return (None, stats);
        };
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
            for &slot in &malloc_sources {
                if model.get(&slot) == Some(&SlotKind::Ref) {
                    solver.add_borrow_exclusion(Some(slot), &[]);
                    committed += 1;
                    stats.commits_source += 1;
                }
            }
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
            model = match solver.model_kinds_relaxing(selectors) {
                Some(m) => m,
                None => return (None, stats),
            };
        }
        panic!("BOC1 mirror: CEGAR did not converge within {cap} rounds");
    }

    /// Copy of `borrow_verify::representative`.
    fn representative(
        conflict: &SlotConflict,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> Option<SlotRef> {
        conflict
            .issuer
            .into_iter()
            .chain(conflict.requirers.iter().copied())
            .find(|s| model.get(s) == Some(&SlotKind::Ref))
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
            CrateCtxt, SlotKind,
            borrow_verify::verify_to_fixpoint,
            coherence::add_coherence,
            crate_slots::CrateSlots,
            emit_crate_ownership_constraints,
            slots::{SlotId, SlotOwner},
            solver::{KindSolver, SlotRef},
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
        row.set("selectors", selectors.len());
        phase("emit_done", t0);

        let t = Instant::now();
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        row.set("t_coherence_s", secs(t.elapsed()));
        phase("coherence_done", t0);

        let t = Instant::now();
        let (model, rstats) =
            mirror::verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, true);
        row.set("t_fixpoint_s", secs(t.elapsed()));
        phase("fixpoint_done", t0);

        row.set("rounds", rstats.rounds);
        row.set("commits_source", rstats.commits_source);
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

        let sources = collect_malloc_source_slots(&program, &slots);
        row.set("sources_total", sources.len());

        match &model {
            None => {
                row.set("status", "decline");
                row.set("decline_reason", decline_reason(&solver, &selectors));
            }
            Some(m) => {
                let (mut n_ref, mut n_raw, mut n_own) = (0usize, 0usize, 0usize);
                let (mut n_ref_d0, mut n_raw_d0, mut n_own_d0) = (0usize, 0usize, 0usize);
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
                        Some(verify_to_fixpoint(&program, &slots, &solver, &selectors, true))
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
    /// replays exactly the failing first solve.
    pub(super) fn decline_reason(solver: &KindSolver, selectors: &[Bool]) -> &'static str {
        let mut assumptions: Vec<Bool> = selectors.to_vec();
        loop {
            match solver.optimize().check(&assumptions) {
                // Should not happen (relaxing declined); a nondeterministic
                // Unknown->Sat flip lands here rather than lying.
                SatResult::Sat => return "sat-in-replay",
                SatResult::Unknown => return "z3-unknown",
                SatResult::Unsat => {
                    let core = solver.optimize().get_unsat_core();
                    match assumptions.iter().position(|s| core.iter().any(|c| c == s)) {
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
}

// ---------------------------------------------------------------------------
// Mirror-fidelity guards (non-ignored: they run in every `cargo test`).
// ---------------------------------------------------------------------------

/// Runs both the REAL `verify_to_fixpoint` and the mirror on independent fresh
/// constructions over one compiled snippet; asserts model equality; returns the
/// mirror's stats + leak count for fixture-specific assertions.
#[cfg(test)]
fn assert_mirror_matches(code: &str) -> (bool, mirror::RoundStats, usize, usize) {
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

        let sources = collect_malloc_source_slots(&program, &slots);
        let leaked = mirrored
            .as_ref()
            .map(|m| {
                sources
                    .iter()
                    .filter(|s| m.get(s) != Some(&SlotKind::Owning))
                    .count()
            })
            .unwrap_or(0);
        (mirrored.is_some(), stats, sources.len(), leaked)
    })
    .unwrap_or_else(|e| e.raise())
}

/// (a) Accept-first-model path: alloc+free settles Owning with no commits.
#[test]
fn boc1_mirror_matches_real_alloc_free() {
    let (accepted, stats, sources, leaked) = assert_mirror_matches(
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
    assert!(accepted);
    assert_eq!(stats.rounds, 1, "first model accepted: exactly one validate round");
    assert_eq!(stats.commits_source + stats.commits_conflict, 0);
    // `sources_total` counts source SLOTS (propagation-closed), not allocations:
    // the one malloc yields its destination `p` PLUS the `free(p)` call-arg temp.
    assert_eq!((sources, leaked), (2, 0), "the freed alloc is retained, not leaked");
}

/// (b) Conflict-commit cascade: two `&mut` of one base force iterated commits.
#[test]
fn boc1_mirror_matches_real_conflict_cascade() {
    let (accepted, stats, _sources, _leaked) = assert_mirror_matches(
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
    assert!(accepted);
    assert!(stats.rounds >= 2, "cascade must iterate; got {} rounds", stats.rounds);
    assert!(stats.commits_conflict >= 1, "at least one conflict commit");
}

/// (c) Selector-drop (leak) + BB3-a source-commit path: the leaked malloc's
/// selector is dropped by `model_kinds_relaxing` AND the max-ref objective's
/// float to `Ref` is committed away (`Ref ⇒ loan`). Guards the headline
/// `sources_leaked` accounting.
#[test]
fn boc1_mirror_matches_real_leaked_source() {
    let (accepted, stats, sources, leaked) = assert_mirror_matches(
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
    assert!(accepted);
    assert!(stats.commits_source >= 1, "BB3-a must commit the floated source");
    assert_eq!((sources, leaked), (1, 1), "the leaked alloc must be counted leaked");
}

/// (d) Maximal-source-retention: of two allocations only the conflicting one
/// leaks (1-of-2 accounting).
#[test]
fn boc1_mirror_matches_real_two_allocs_one_leak() {
    let (accepted, _stats, sources, leaked) = assert_mirror_matches(
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
    assert!(accepted);
    // Slot-level source accounting: `a` + its `free(a)` call-arg temp + `b` = 3
    // source slots for 2 allocations; only `b`'s slot leaks (kind != Owning).
    assert_eq!((sources, leaked), (3, 1), "exactly the conflicting alloc leaks");
}

/// Decline path end-to-end, on the smallest confirmed real-corpus decliner:
/// bst's `deleteNode` with the `minValueNode` call inlined to a field load
/// (bisect result — `free(param)` alone, `free(cast)` alone, and the
/// single-free non-recursive variant all ACCEPT; the recursive
/// `root->left = f(root->left)` flow-through plus conditional frees is what
/// contradicts). There is NO malloc in this shape, so the UNSAT has zero
/// retractable source selectors — non-source UNSAT by construction. The
/// mirror must (a) agree with the real `verify_to_fixpoint`'s `None` and
/// (b) diagnose `unsat-nonsource`, not `z3-unknown`.
#[test]
fn boc1_mirror_matches_real_delete_node_decline() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt, coherence::add_coherence, crate_slots::CrateSlots,
        emit_crate_ownership_constraints, solver::KindSolver,
    };

    let code = r#"
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
    let (accepted, stats, sources, _leaked) = assert_mirror_matches(code);
    assert!(!accepted, "the deleteNode shape must decline (non-source UNSAT)");
    assert_eq!(stats.rounds, 0, "decline at the first solve, before any round");
    assert_eq!(sources, 0, "no malloc: the UNSAT cannot be source-retractable");

    ::utils::compilation::run_compiler_on_str(code, |tcx| {
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
        let (model, _stats) =
            mirror::verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, true);
        assert!(model.is_none());
        assert_eq!(run::decline_reason(&solver, &selectors), "unsat-nonsource");
    })
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

        // Persist incrementally so partial sweeps still leave artifacts.
        let jsonl: String = raw_rows.iter().map(|r| report::to_json_line(r) + "\n").collect();
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
        "rounds",
        "commits_source",
        "commits_conflict",
        "slots_total",
        "n_ref",
        "n_raw",
        "n_own",
        "n_ref_d0",
        "n_ref_prod",
        "d_ref_d0",
        "sources_total",
        "sources_leaked",
        "decline_reason",
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
         kind is not Owning. `commits_*` count exclusion assertions exactly as the real \
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
