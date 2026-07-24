//! C1-lite corpus runner for the experimental BO (borrow_ownership) analysis.
//!
//! Harness ONLY: nothing under `analyses/**` is touched. Runs BO exactly as
//! `tests::borrow_ownership_coherence::assert_ownership_parity` constructs it
//! (tests.rs `collect_program` → `CrateSlots::build` → `CrateCtxt::new` →
//! `KindSolver::new` → `emit_crate_ownership_constraints` → per-fn
//! `add_coherence` → fixpoint with `is_mutable = true`) over the CROWN/Laertes
//! benchmark programs in `benchmarks/rs-crown/`, and reports per program: wall-clock,
//! CEGAR rounds + commits, Ref/Raw/Owning counts, leaked sources, and
//! decline/timeout/oom/panic classification. Also runs the production borrow
//! baseline (`demote_pointers_iterative_with_fields` from all-Ref, the same
//! independent driver `assert_borrow_parity` uses) for the BO-vs-prod Ref delta.
//!
//! §NB5-M — NATIVE COUNTERS (mirror retired). The BO fork's
//! `borrow_ownership::borrow_verify::verify_to_fixpoint_counting` exposes the round/commit/leak
//! counters directly (`RoundStats`); `verify_to_fixpoint` is its model-only wrapper. The fork is
//! NOT under the `analyses/**` freeze, so the old "mirror over instrumentation" tradeoff (a counter
//! would break the frozen diff audit) never applied here. The former verbatim MIRROR of the loop
//! (`mirror::verify_to_fixpoint_counting`) is DELETED — its parity was proven at the NB5-M gate
//! (native == mirror, byte-identical to the NB5-Z baseline on all 19 accepts, both profiles) before
//! retirement. Wrapper-thinness (no logic added to the wrapper that would diverge the sweep's
//! counters from what the suite verifies) is now guarded by `verify_to_fixpoint_is_thin_wrapper`.
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

/// §L2 RED — frozen base counts and the certified 26-slot recovery inventory.
///
/// This is test-harness-only. It reads accepted Mode-A models but never changes
/// the solver, validation loop, or emitted output.
mod l2_red_gate {
    use std::collections::{BTreeMap, BTreeSet};

    use super::{CorpusProgram, report::Row};

    const BASE: &str =
        include_str!("analyses/borrow_ownership/testdata/l2_rs_crown_base_ae6f334.csv");
    const TARGETS: &str =
        include_str!("analyses/borrow_ownership/testdata/l2_rs_crown_targets.csv");
    pub const ENV: &str = "CRAT_BOC1_L2_RED_GATE";

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct BaseRow {
        pub program: String,
        pub n_ref: usize,
        pub n_ref_d0: usize,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Target {
        pub program: String,
        pub slot: String,
        pub audit_round: usize,
    }

    pub fn enabled() -> bool {
        match std::env::var(ENV).as_deref() {
            Err(std::env::VarError::NotPresent) | Ok("0") => false,
            Ok("1") => true,
            Ok(other) => panic!("{ENV} must be 0 or 1, got {other:?}"),
            Err(error) => panic!("{ENV} is not valid Unicode: {error}"),
        }
    }

    fn data_lines(input: &str) -> impl Iterator<Item = &str> {
        input
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
    }

    pub fn bases() -> Vec<BaseRow> {
        let mut lines = data_lines(BASE);
        assert_eq!(
            lines.next(),
            Some("program,n_ref,n_ref_d0"),
            "L2 RED base fixture header drifted"
        );
        lines
            .map(|line| {
                let fields: Vec<&str> = line.split(',').collect();
                assert_eq!(fields.len(), 3, "malformed L2 RED base row: {line}");
                BaseRow {
                    program: fields[0].to_string(),
                    n_ref: fields[1]
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid n_ref in L2 RED base row: {line}")),
                    n_ref_d0: fields[2]
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid n_ref_d0 in L2 RED base row: {line}")),
                }
            })
            .collect()
    }

    pub fn targets() -> Vec<Target> {
        let mut lines = data_lines(TARGETS);
        assert_eq!(
            lines.next(),
            Some("program,slot,audit_round"),
            "L2 RED target fixture header drifted"
        );
        lines
            .map(|line| {
                let fields: Vec<&str> = line.split(',').collect();
                assert_eq!(fields.len(), 3, "malformed L2 RED target row: {line}");
                Target {
                    program: fields[0].to_string(),
                    slot: fields[1].to_string(),
                    audit_round: fields[2]
                        .parse()
                        .unwrap_or_else(|_| panic!("invalid audit round in L2 RED target row: {line}")),
                }
            })
            .collect()
    }

    pub fn base_for(program: &str) -> BaseRow {
        bases()
            .into_iter()
            .find(|row| row.program == program)
            .unwrap_or_else(|| panic!("L2 RED base fixture has no row for {program}"))
    }

    pub fn targets_for(program: &str) -> Vec<Target> {
        targets()
            .into_iter()
            .filter(|target| target.program == program)
            .collect()
    }

    pub fn assert_fixtures(corpus: &[CorpusProgram]) {
        let bases = bases();
        let corpus_names: Vec<&str> = corpus.iter().map(|program| program.name).collect();
        let base_names: Vec<&str> = bases.iter().map(|row| row.program.as_str()).collect();
        assert_eq!(
            base_names, corpus_names,
            "L2 RED base fixture must cover the exact frozen corpus in catalog order"
        );
        assert_eq!(
            bases.iter().map(|row| row.n_ref).sum::<usize>(),
            52_810,
            "L2 RED aggregate base n_ref drifted"
        );
        assert_eq!(
            bases.iter().map(|row| row.n_ref_d0).sum::<usize>(),
            49_459,
            "L2 RED aggregate base n_ref_d0 drifted"
        );

        let targets = targets();
        assert_eq!(targets.len(), 26, "L2 RED inventory must remain certified N=26");
        let mut seen = BTreeSet::new();
        let mut by_program = BTreeMap::<String, usize>::new();
        let mut by_round = BTreeMap::<usize, usize>::new();
        for target in &targets {
            assert!(
                corpus_names.contains(&target.program.as_str()),
                "L2 RED target names unknown program {}",
                target.program
            );
            assert!(
                seen.insert((target.program.clone(), target.slot.clone())),
                "duplicate L2 RED target {}/{}",
                target.program,
                target.slot
            );
            *by_program.entry(target.program.clone()).or_default() += 1;
            *by_round.entry(target.audit_round).or_default() += 1;
        }
        assert_eq!(
            by_program.into_iter().collect::<Vec<_>>(),
            vec![
                ("binn".to_string(), 7),
                ("bzip2".to_string(), 5),
                ("libtree".to_string(), 7),
                ("lodepng".to_string(), 7),
            ],
            "L2 RED inventory program split drifted"
        );
        assert_eq!(
            by_round.into_iter().collect::<Vec<_>>(),
            vec![(1, 18), (2, 7), (3, 1)],
            "L2 RED inventory audit-round split drifted"
        );
    }

    fn usize_field(row: &Row, key: &str) -> usize {
        row.get(key)
            .unwrap_or_else(|| panic!("L2 RED row missing {key}: {row:?}"))
            .parse()
            .unwrap_or_else(|_| panic!("L2 RED row has non-numeric {key}: {row:?}"))
    }

    fn signed_field(row: &Row, key: &str) -> i64 {
        row.get(key)
            .unwrap_or_else(|| panic!("L2 RED row missing {key}: {row:?}"))
            .parse()
            .unwrap_or_else(|_| panic!("L2 RED row has non-numeric {key}: {row:?}"))
    }

    pub fn summary(rows: &[Row]) -> String {
        let accepted = rows.iter().filter(|row| row.get("status") == Some("ok")).count();
        let found = rows
            .iter()
            .filter_map(|row| row.get("l2_targets_found"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let expected = rows
            .iter()
            .filter_map(|row| row.get("l2_targets_expected"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let recovered = rows
            .iter()
            .filter_map(|row| row.get("l2_targets_ref"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let n_ref = rows
            .iter()
            .filter_map(|row| row.get("n_ref"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let base_n_ref = rows
            .iter()
            .filter_map(|row| row.get("l2_base_n_ref"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        let regressions = rows
            .iter()
            .filter(|row| {
                row.get("l2_n_ref_delta")
                    .and_then(|value| value.parse::<i64>().ok())
                    .is_some_and(|delta| delta < 0)
            })
            .count();
        let check_sat = rows
            .iter()
            .filter_map(|row| row.get("check_sat_count"))
            .filter_map(|value| value.parse::<usize>().ok())
            .sum::<usize>();
        format!(
            "L2RED accepted={accepted}/{} found={found}/{expected} recovered={recovered}/{expected} \
             n_ref={n_ref}/{base_n_ref} delta={} per_program_regressions={regressions} \
             check_sat={check_sat}",
            rows.len(),
            n_ref as i64 - base_n_ref as i64,
        )
    }

    pub fn assert_results(rows: &[Row], corpus: &[CorpusProgram]) {
        assert_eq!(
            rows.len(),
            corpus.len(),
            "L2 RED must run the complete frozen rs-crown corpus"
        );
        let actual_names: Vec<&str> = rows
            .iter()
            .map(|row| row.get("program").expect("L2 RED row has program"))
            .collect();
        let expected_names: Vec<&str> = corpus.iter().map(|program| program.name).collect();
        assert_eq!(
            actual_names, expected_names,
            "L2 RED corpus order/content drifted"
        );

        let non_accepts: Vec<(&str, &str)> = rows
            .iter()
            .filter_map(|row| {
                let status = row.get("status").unwrap_or("missing");
                (status != "ok").then(|| (row.get("program").unwrap_or("missing"), status))
            })
            .collect();
        assert!(
            non_accepts.is_empty(),
            "L2 RED requires 20/20 accepted Mode-A rows; non-accepts={non_accepts:?}"
        );
        for row in rows {
            assert_eq!(row.get("repair"), Some("mode_a"), "L2 RED row is not Mode-A: {row:?}");
            assert_eq!(row.get("l2_feature"), Some("on"), "L2 flag did not reach worker: {row:?}");
            assert_eq!(row.get("l2_diag"), Some("raw"), "L2 diagnostics did not reach worker: {row:?}");
            assert_eq!(
                row.get("safe_mono"),
                Some("per_site"),
                "L2 RED row did not use the frozen per-site safety profile: {row:?}"
            );
            assert_eq!(
                row.get("mut_facts"),
                Some("on"),
                "L2 RED row did not use the frozen mutability-facts profile: {row:?}"
            );
            assert_eq!(
                row.get("z3_full_version"),
                Some("4.15.4.0"),
                "L2 RED row did not use the frozen Z3 version: {row:?}"
            );
            assert!(
                usize_field(row, "check_sat_count") > 0,
                "L2 RED row did not report solver check-sat activity: {row:?}"
            );
        }

        let expected_targets = rows
            .iter()
            .map(|row| usize_field(row, "l2_targets_expected"))
            .sum::<usize>();
        assert_eq!(expected_targets, 26, "L2 RED target denominator drifted");
        let found_targets = rows
            .iter()
            .map(|row| usize_field(row, "l2_targets_found"))
            .sum::<usize>();
        assert_eq!(
            found_targets, expected_targets,
            "L2 RED inventory slot missing or renamed; re-anchor is required"
        );

        let actual_n_ref = rows.iter().map(|row| usize_field(row, "n_ref")).sum::<usize>();
        let base_n_ref = rows
            .iter()
            .map(|row| usize_field(row, "l2_base_n_ref"))
            .sum::<usize>();
        assert_eq!(base_n_ref, 52_810, "L2 RED aggregate base n_ref drifted");
        assert!(
            actual_n_ref >= base_n_ref,
            "L2 RED violates the corpus-wide n_ref non-regression gate: \
             actual={actual_n_ref} base={base_n_ref}"
        );
        let reported_delta = rows
            .iter()
            .map(|row| signed_field(row, "l2_n_ref_delta"))
            .sum::<i64>();
        assert_eq!(
            reported_delta,
            actual_n_ref as i64 - base_n_ref as i64,
            "L2 RED per-program n_ref deltas do not sum to the aggregate delta"
        );

        let recovered = rows
            .iter()
            .map(|row| usize_field(row, "l2_targets_ref"))
            .sum::<usize>();
        assert!(
            recovered >= 22,
            "L2 RED: recovered {recovered}/26; implementation merge bar is 22/26"
        );
    }
}


// §NB4-4c-Q: re-export the collateral measurement so the RED shape tests (in `tests.rs`, outside this
// private module) validate the EXACT harness code the sweep runs, not a copy.
#[cfg(test)]
pub(crate) use run::{CollateralMeasurement, measure_collateral};

/// Per-mode analysis drivers producing report rows.
mod run {
    use std::time::{Duration, Instant};

    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_middle::ty::TyCtxt;
    use z3::{SatResult, ast::Bool};

    use super::{collect_program, report::Row};
    use crate::analyses::{
        borrow::{GBorrowInferCtxt, demote_pointers_iterative_with_fields},
        borrow_ownership::{
            CrateCtxt, SafeMonoMode, SlotKind,
            borrow_verify::{
                RepairMode, model_accepts, slotref_key, verify_to_fixpoint,
                verify_to_fixpoint_counting, with_capture,
            },
            coherence::{add_coherence, constrain_field_ownership, field_ownership_candidates},
            crate_slots::CrateSlots,
            emit_crate_ownership_constraints,
            mutability_facts::{MutFacts, MutFactsMode, MutProvider},
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

    // ───────────────────────── §NB4-4c-Q collateral measurement (item-4 sizing) ─────────────────────
    //
    // Sizes the coherence-collateral Ref-loss from over-including modeled-origin slots in the
    // may-supply demotion set (Codex re-review 2026-07-17). Runs TWO real solves per program in-process
    // (the CHECK_REAL second-solver pattern): FULL demotes the whole no-borrow-origin set (the shipped
    // behavior); MINUS demotes that set with the MITIGATED over-inclusion removed. The n_ref delta
    // (MINUS − FULL) is the collateral. **MEASUREMENT-ONLY** — MINUS must NEVER ship: it un-demotes
    // legitimately-may-reach branch-joins (see `collect_overincluded_modeled_origin_slots`), so the
    // measured collateral is an UPPER BOUND on what the precise item-4 fix would recover.

    pub(crate) struct CollateralMeasurement {
        /// "no-oi" (no over-inclusion → collateral 0, no solves), "ok" (solved + anchorable), or
        /// "real-decline" (a REAL solve declined/unknown — the number is NOT trustworthy; the sweep
        /// surfaces it, post-sweep audit must see none). Codex F2a: never silently skip a decline.
        pub status: &'static str,
        pub overincl_raw: usize,
        pub overincl_mit: usize,
        /// Codex F1: the self-inclusive UPPER-BOUND over-inclusion (catches restored self-origins the
        /// mitigated set misses). `mitigated ⊆ upper`, so `collateral_upper ≥ collateral_mit`.
        pub overincl_upper: usize,
        /// FULL model counts — `Some` only when `status == "ok"` (a real FULL solve ran). The sweep
        /// anchors BOTH to the shipped MIRROR (Codex F2b: n_ref AND n_ref_d0, not just n_ref).
        pub nref_full: Option<usize>,
        pub nref_d0_full: Option<usize>,
        /// collateral = n_ref(MINUS) − n_ref(FULL); may be negative (do NOT assert ≥ 0). `_mit` uses the
        /// mitigated over-inclusion (tighter, storage-excluded), `_upper` the maximal set (the gate).
        pub collateral_mit: i64,
        pub collateral_d0_mit: i64,
        pub collateral_upper: i64,
        pub collateral_d0_upper: i64,
    }

    /// Count Ref slots (all depths) and Ref slots at depth-0 LOCAL only — the exact accounting
    /// `run_bo` uses for `n_ref` / `n_ref_d0` (field slots contribute to `n_ref` but NOT `n_ref_d0`,
    /// which is why field collateral is invisible in the d0 metric).
    fn count_refs(model: &FxHashMap<SlotRef, SlotKind>, slots: &CrateSlots) -> (usize, usize) {
        let (mut n_ref, mut n_ref_d0) = (0usize, 0usize);
        for (s, kind) in model {
            if *kind == SlotKind::Ref {
                n_ref += 1;
                if let SlotRef::Local(fn_did, sid) = s
                    && let Some(u) = slots.fn_local_slots.get(fn_did)
                    && u.slot(*sid).depth == 0
                {
                    n_ref_d0 += 1;
                }
            }
        }
        (n_ref, n_ref_d0)
    }

    /// Emit with EMPTY origins (no in-emit demotion), manually `¬ref` exactly `demote`, add coherence,
    /// and solve with the REAL `verify_to_fixpoint`. `emit_crate_ownership_constraints` reads `origins`
    /// ONLY for its demotion loop, so this reproduces the shipped pipeline with a SWAPPED demotion set.
    fn solve_with_demotion(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        demote: &[SlotRef],
        mut_facts: &MutFacts,
    ) -> Option<FxHashMap<SlotRef, SlotKind>> {
        let empty = crate::analyses::borrow_ownership::origin_summary::OriginSummaries::default();
        let crate_ctxt = CrateCtxt::new(program);
        let solver = KindSolver::new(slots);
        let (_stats, selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, slots, &empty, &solver).ok()?;
        for slot in demote {
            solver.add_borrow_exclusion(Some(*slot), &[]);
        }
        for &g in &program.functions {
            let body = program.tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, slots, g, &body);
        }
        verify_to_fixpoint(program, slots, &solver, &selectors, mut_facts)
    }

    /// Measure the collateral. Returns a status-tagged struct (never panics on decline — Codex F2a).
    /// FULL preserves the SHIPPED Vec order/multiplicity (Codex F2c). Short-circuits with no solves
    /// when there is no over-inclusion (the common corpus case). Asserts every over-inclusion set ⊆
    /// FULL and `mitigated ⊆ upper` (mapping/invariant drift = hard STOP).
    pub(crate) fn measure_collateral(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
        mut_facts: &MutFacts,
    ) -> CollateralMeasurement {
        use crate::analyses::borrow_ownership::origins::{
            collect_no_borrow_origin_slots, collect_overincluded_modeled_origin_slots,
            collect_upperbound_overincluded_slots,
        };
        // FULL demotion set = the SHIPPED Vec (preserve order + multiplicity — F2c).
        let full_vec = collect_no_borrow_origin_slots(origins, slots);
        let full_set: FxHashSet<SlotRef> = full_vec.iter().copied().collect();
        let raw_set: FxHashSet<SlotRef> =
            collect_overincluded_modeled_origin_slots(origins, slots, false).into_iter().collect();
        let mit_set: FxHashSet<SlotRef> =
            collect_overincluded_modeled_origin_slots(origins, slots, true).into_iter().collect();
        let upper_set: FxHashSet<SlotRef> =
            collect_upperbound_overincluded_slots(origins, slots).into_iter().collect();
        assert!(
            raw_set.is_subset(&full_set)
                && mit_set.is_subset(&full_set)
                && upper_set.is_subset(&full_set),
            "NB4-4c-Q: an over-inclusion set ⊄ FULL demotion set (mapping drift)"
        );
        assert!(mit_set.is_subset(&upper_set), "NB4-4c-Q: mitigated ⊄ upper (invariant)");
        let (n_raw, n_mit, n_upper) = (raw_set.len(), mit_set.len(), upper_set.len());
        let build = |status, nf: Option<usize>, nd0, cm, cdm, cu, cdu| CollateralMeasurement {
            status,
            overincl_raw: n_raw,
            overincl_mit: n_mit,
            overincl_upper: n_upper,
            nref_full: nf,
            nref_d0_full: nd0,
            collateral_mit: cm,
            collateral_d0_mit: cdm,
            collateral_upper: cu,
            collateral_d0_upper: cdu,
        };
        // Short-circuit: no over-inclusion ⇒ MINUS == FULL for both variants ⇒ collateral 0, no solves.
        if upper_set.is_empty() {
            return build("no-oi", None, None, 0, 0, 0, 0);
        }
        // Real FULL solve — for the like-with-like delta AND the anchor (both solves are REAL, so the
        // collateral is not confounded by an impl difference; F2b anchors real FULL to run_bo's model).
        let Some(full_model) = solve_with_demotion(program, slots, &full_vec, mut_facts) else {
            return build("real-decline", None, None, 0, 0, 0, 0);
        };
        let (nref_full, nref_d0_full) = count_refs(&full_model, slots);
        let minus = |exclude: &FxHashSet<SlotRef>| -> Option<(usize, usize)> {
            let v: Vec<SlotRef> = full_vec.iter().copied().filter(|s| !exclude.contains(s)).collect();
            solve_with_demotion(program, slots, &v, mut_facts).map(|m| count_refs(&m, slots))
        };
        let Some((nref_mu, nref_d0_mu)) = minus(&upper_set) else {
            return build("real-decline", Some(nref_full), Some(nref_d0_full), 0, 0, 0, 0);
        };
        // MINUS_mit: reuse FULL if `mit` empty, reuse `upper`'s solve if the sets are equal, else solve.
        let (nref_mm, nref_d0_mm) = if mit_set.is_empty() {
            (nref_full, nref_d0_full)
        } else if mit_set == upper_set {
            (nref_mu, nref_d0_mu)
        } else {
            match minus(&mit_set) {
                Some(x) => x,
                None => return build("real-decline", Some(nref_full), Some(nref_d0_full), 0, 0, 0, 0),
            }
        };
        build(
            "ok",
            Some(nref_full),
            Some(nref_d0_full),
            nref_mm as i64 - nref_full as i64,
            nref_d0_mm as i64 - nref_d0_full as i64,
            nref_mu as i64 - nref_full as i64,
            nref_d0_mu as i64 - nref_d0_full as i64,
        )
    }

    /// §NB5-L2 commit-necessity probe verdict for one leave-one-out.
    pub(crate) enum ProbeOutcome {
        /// The re-solve without this commit ACCEPTS with `slot_i` still `Ref` — the commit was
        /// removable (given the other demotions asserted on the base).
        OverPin,
        /// The re-solve declined, or left `slot_i` non-`Ref`, or failed to accept — counted necessary.
        Necessary,
    }

    /// §NB5-L2 — build `run_bo`'s EXACT solver base ONCE: `emit_crate_ownership_constraints(origins)`
    /// with the REAL seed (NOT `solve_with_demotion`'s `&empty`) → `add_coherence` per fn →
    /// `constrain_field_ownership` (the field constraints the loop adds before its first solve). The
    /// audit reuses this base across every probe via `push_scope`/`pop_scope`, so brotli's ~683-commit
    /// exhaustive leave-one-out pays the emit cost once, not per probe. `None` on emit error.
    fn build_probe_base(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
    ) -> Option<(KindSolver, Selectors)> {
        let crate_ctxt = CrateCtxt::new(program);
        let solver = KindSolver::new(slots);
        let (_stats, selectors) =
            emit_crate_ownership_constraints(&crate_ctxt, slots, origins, &solver).ok()?;
        for &g in &program.functions {
            let body = program.tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, slots, g, &body);
        }
        constrain_field_ownership(&solver, slots, program);
        Some((solver, selectors))
    }

    /// §NB5-L2 — the leave-one-out primitive on a PREBUILT base (the ratified Q2 MECHANISM: ONE solve +
    /// ONE validate, NOT a CEGAR re-run). Pushes a scope, asserts `¬ref(d)` for every `d ∈ demote`,
    /// solves ONCE, validates ONCE, then pops — so the base is untouched for the next probe. Returns
    /// true iff the model ACCEPTS (`model_accepts`) AND leaves `target` `Ref` (dropping `target`'s
    /// commit still accepts with `target` a borrow).
    ///
    /// Rider 4 (push/pop determinism): reusing the incremental solver may tie-break OTHER slots
    /// differently than a fresh `KindSolver` would, and `model_kinds_relaxing` may relax selectors
    /// differently than the anchor fixpoint did. Neither matters: this is a CLASSIFICATION only
    /// (accept ∧ `target`==`Ref`), never a model comparison — so do NOT "fix" it to fresh solves for a
    /// parity that is irrelevant here.
    fn probe_accepts_with_ref(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        base: &KindSolver,
        selectors: &Selectors,
        is_mutable: impl MutProvider + Copy,
        demote: &[SlotRef],
        target: SlotRef,
    ) -> bool {
        base.push_scope();
        for &d in demote {
            base.add_borrow_exclusion(Some(d), &[]);
        }
        let verdict = match base.model_kinds_relaxing(selectors) {
            Some(model) => {
                model.get(&target) == Some(&SlotKind::Ref)
                    && model_accepts(program, slots, &model, is_mutable)
            }
            // UNSAT even without `target` ⇒ `target` is not the reason it declines; NOT removable.
            None => false,
        };
        base.pop_scope();
        verdict
    }

    /// §NB5-L2 — single-shot leave-one-out (build base + one probe). The audit driver builds the base
    /// once and calls `probe_accepts_with_ref` directly; this wrapper keeps the calibration-test API
    /// (`commit_set`, `i`) rebuilding the base per call, which is fine at test scale. `commit_set[i]` is
    /// an OVER-PIN iff a solve over `commit_set \ {commit_set[i]}` accepts with `slot_i` `Ref`.
    pub(crate) fn necessity_probe(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
        is_mutable: impl MutProvider + Copy,
        commit_set: &[SlotRef],
        i: usize,
    ) -> ProbeOutcome {
        let Some((base, selectors)) = build_probe_base(program, slots, origins) else {
            return ProbeOutcome::Necessary;
        };
        let demote: Vec<SlotRef> = commit_set
            .iter()
            .enumerate()
            .filter_map(|(j, &c)| (j != i).then_some(c))
            .collect();
        if probe_accepts_with_ref(program, slots, &base, &selectors, is_mutable, &demote, commit_set[i]) {
            ProbeOutcome::OverPin
        } else {
            ProbeOutcome::Necessary
        }
    }

    /// §NB5-L2 — format a slot for the over-pin inventory: `def_path::_local@dN` (locals) /
    /// `def_path::fieldK@dN` (struct fields). The L2 RED inventory reads these back.
    pub(super) fn fmt_slot(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        s: SlotRef,
    ) -> String {
        match s {
            SlotRef::Local(fn_did, sid) => {
                let sl = slots.fn_local_slots.get(&fn_did).map(|u| *u.slot(sid));
                let (local, depth) = match sl.map(|s| (s.owner, s.depth)) {
                    Some((SlotOwner::Local(l), d)) => (l.as_u32(), d),
                    other => (u32::MAX, other.map_or(0, |(_, d)| d)),
                };
                format!("{}::_{}@d{}", program.tcx.def_path_str(fn_did.to_def_id()), local, depth)
            }
            SlotRef::Field(sid) => {
                let sl = slots.field_slots.slot(sid);
                match sl.owner {
                    SlotOwner::Field(f) => format!(
                        "{}::field{}@d{}",
                        program.tcx.def_path_str(f.struct_did.to_def_id()),
                        f.field_index,
                        sl.depth
                    ),
                    SlotOwner::Local(_) => format!("field?@d{}", sl.depth),
                }
            }
        }
    }

    fn record_l2_red_inventory(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        model: &FxHashMap<SlotRef, SlotKind>,
        repair: RepairMode,
        n_ref: usize,
        row: &mut Row,
    ) {
        if !super::l2_red_gate::enabled() {
            return;
        }
        assert!(
            crate::analyses::borrow_ownership::l2::enabled_from_env(),
            "L2 RED gate requires CRAT_BO_L2_GUARDED_COMMITS=1"
        );
        assert_eq!(repair, RepairMode::ModeA, "L2 RED gate is Mode-A-only");
        let diagnostics = std::env::var("CRAT_POINTER_DECISION_DIAGNOSTICS")
            .expect("L2 RED gate requires decision diagnostics");
        assert_eq!(
            diagnostics, "raw",
            "L2 RED gate requires CRAT_POINTER_DECISION_DIAGNOSTICS=raw"
        );
        assert_eq!(
            crate::rewriter::diagnostics::DiagnosticsMode::from_env_value(Some(&diagnostics)),
            crate::rewriter::diagnostics::DiagnosticsMode::Raw,
        );

        let program_name =
            std::env::var("CRAT_BOC1_NAME").expect("L2 RED worker requires CRAT_BOC1_NAME");
        let expected = super::l2_red_gate::targets_for(&program_name);
        let mut model_by_name = FxHashMap::default();
        for (&slot, &kind) in model {
            let name = fmt_slot(program, slots, slot);
            assert!(
                model_by_name.insert(name.clone(), kind).is_none(),
                "L2 RED model has duplicate canonical slot {name}"
            );
        }

        let mut found = 0usize;
        let mut recovered = 0usize;
        for target in &expected {
            let Some(kind) = model_by_name.get(&target.slot).copied() else {
                continue;
            };
            found += 1;
            recovered += usize::from(kind == SlotKind::Ref);
            let kind = match kind {
                SlotKind::Ref => "ref",
                SlotKind::Raw => "raw",
                SlotKind::Owning => "owning",
            };
            eprintln!(
                "L2TARGET program={} slot={} audit_round={} kind={kind}",
                target.program, target.slot, target.audit_round
            );
        }

        let base = super::l2_red_gate::base_for(&program_name);
        row.set("l2_feature", "on");
        row.set("l2_diag", "raw");
        row.set("l2_targets_expected", expected.len());
        row.set("l2_targets_found", found);
        row.set("l2_targets_ref", recovered);
        row.set("l2_base_n_ref", base.n_ref);
        row.set("l2_n_ref_delta", n_ref as i64 - base.n_ref as i64);
    }

    /// §NB5-L2 commit-necessity audit driver — measure the L2 headroom Mode-A leaves (env-gated by
    /// `CRAT_BOC1_NECESSITY_AUDIT`; called from `run_bo`). FULL-ANCHOR first: the audit's baseline IS
    /// `run_bo`'s own accepted `model`, so only measure if it accepted, assert it satisfies
    /// `model_accepts` (anti-drift), and record `na_anchor_nref[_d0]` for the post-run cross-check
    /// against the merged NB5-L `mode_a` sweep row.
    ///
    /// Then TWO leave-one-out passes over the distinct commit set `C`, both EXHAUSTIVE (no sampling —
    /// the base is emitted once and every probe reuses it via `push_scope`/`pop_scope`, so even brotli's
    /// full `C` is affordable):
    /// - **Independent** (`na_indep_overpins`): each `ci` tested against the full `C\{ci}`. NOT a bound
    ///   and INCOMPARABLE with the gate number — it OVER-counts alternative-repair pairs (both reported
    ///   though only one Ref is jointly recoverable, Codex F1) AND UNDER-counts joint recoveries (a slot
    ///   removable only while other removed slots stay `Ref` is missed, since independent demotes them
    ///   all — e.g. coherence-equated slots; this is why `na_overpins` can EXCEED `na_indep_overpins`,
    ///   as on libtree 3 → 7). A labeled diagnostic for continuity with the pre-redesign partial; do
    ///   NOT gate on it and do NOT assume any ≤/≥ relation to `na_overpins`.
    /// - **Witnessed-joint greedy** (`na_overpins` — THE gate number): in ROUND ORDER (rider 3), retain
    ///   all commits and test removing each given the CURRENT retained set (already-removed commits left
    ///   un-demoted, so removability is tested GIVEN the recovered set); a success is made PERMANENT. The
    ///   removed set is certified JOINTLY recoverable by a final witness solve (`na_joint_witnessed`:
    ///   demote ONLY the final retained set → every removed slot `Ref` + accept) — a TRUE lower bound on
    ///   recoverable Refs, sound regardless of any push/pop tie-breaking (the witness is the certificate).
    ///   CAVEAT (rider 2): still blind to joint-ONLY pins (neither member individually removable given
    ///   the retained set — greedy never enters), so "close the line" still carries "joint-only headroom
    ///   unmeasured". Order-dependent: A witnessed lower bound, not THE maximum removable set; round order
    ///   is the diagnostic choice (late-round commits sit on more accumulation — the round DISTRIBUTION
    ///   of the removed set is a first-class output).
    ///
    /// Emits per-program counts + the `NAOVERPIN` slot inventory for the witnessed-joint set (rider 4:
    /// runs under the seed-pinned worker env; the push/pop reuse is classification-only).
    pub(crate) fn run_necessity_audit(
        program: &crate::utils::rustc::RustProgram,
        slots: &CrateSlots,
        origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
        is_mutable: impl MutProvider + Copy,
        model: &Option<FxHashMap<SlotRef, SlotKind>>,
        events: &[(SlotRef, usize)],
        row: &mut Row,
    ) {
        // FULL-ANCHOR: no anchor model ⇒ nothing to measure; surface it, never a silent skip.
        let Some(model) = model else {
            row.set("na_status", "anchor-declined");
            return;
        };
        assert!(
            model_accepts(program, slots, model, is_mutable),
            "necessity audit: the anchor's accepted model must satisfy model_accepts (drift STOP)"
        );
        let (anchor_nref, anchor_nref_d0) = count_refs(model, slots);
        row.set("na_anchor_nref", anchor_nref);
        row.set("na_anchor_nref_d0", anchor_nref_d0);
        // Distinct commit set C (dedup by slot, keep the FIRST round each slot was committed), then
        // ROUND ORDER (round, slotref_key) — the greedy processing order (rider 3), deterministic.
        let mut seen = FxHashSet::default();
        let mut commit_set: Vec<(SlotRef, usize)> = Vec::new();
        for &(s, r) in events {
            if seen.insert(s) {
                commit_set.push((s, r));
            }
        }
        commit_set.sort_by(|a, b| (a.1, slotref_key(&a.0)).cmp(&(b.1, slotref_key(&b.0))));
        let n = commit_set.len();
        row.set("na_commits_total", n);
        if n == 0 {
            row.set("na_status", "no-commits");
            row.set("na_indep_overpins", 0);
            row.set("na_overpins", 0);
            return;
        }
        // Emit the probe base ONCE; every probe reuses it via push/pop (rider 4 / cost).
        let Some((base, selectors)) = build_probe_base(program, slots, origins) else {
            row.set("na_status", "base-error");
            return;
        };
        let slots_only: Vec<SlotRef> = commit_set.iter().map(|(s, _)| *s).collect();
        let program_name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_string());

        // --- Independent pass (over-count diagnostic; each ci vs the FULL C\{ci}). It is exactly `n`
        // extra solves on top of the greedy pass, so for the largest programs it is the difference
        // between feasible and not. `CRAT_BOC1_NA_GREEDY_ONLY` skips it (the GATE metric is the greedy
        // witnessed-joint below; independent is only a labeled diagnostic — rider 5's "continuity" is
        // about the small/mid programs, which keep both passes). Emits `na_indep_overpins=skipped`. ---
        if std::env::var_os("CRAT_BOC1_NA_GREEDY_ONLY").is_some() {
            row.set("na_indep_overpins", "skipped");
        } else {
            let mut indep_overpins = 0usize;
            for i in 0..n {
                let demote: Vec<SlotRef> = (0..n).filter(|&j| j != i).map(|j| slots_only[j]).collect();
                if probe_accepts_with_ref(program, slots, &base, &selectors, is_mutable, &demote, slots_only[i]) {
                    indep_overpins += 1;
                }
            }
            row.set("na_indep_overpins", indep_overpins);
        }

        // --- Witnessed-joint greedy (THE gate number), round order. Buffer the removed set; the
        // NAOVERPIN inventory + na_overpins publish ONLY after the joint witness certifies it (F1). ---
        let mut retained = vec![true; n];
        let mut removed: Vec<(SlotRef, usize)> = Vec::new();
        for i in 0..n {
            // Demote every STILL-retained commit except the candidate; the already-removed commits are
            // left un-demoted (Ref-eligible), so removability is tested GIVEN the recovered set.
            let demote: Vec<SlotRef> =
                (0..n).filter(|&j| j != i && retained[j]).map(|j| slots_only[j]).collect();
            if probe_accepts_with_ref(program, slots, &base, &selectors, is_mutable, &demote, slots_only[i]) {
                retained[i] = false;
                removed.push(commit_set[i]);
            }
        }

        // F1 (Codex): certify the JOINT property FAIL-CLOSED before publishing anything. HARD-PIN every
        // removed slot `Ref` (not a passive optimum inspection — tie-breaking could otherwise miss a
        // valid witness), demote ONLY the final retained set, and require an ACCEPTING model. On success
        // the removed set is provably jointly recoverable → publish the gate number + inventory + `ok`.
        // On failure (a sequential-removal hole, or the pins are UNSAT) the gate metric is SUPPRESSED and
        // the status is `witness-failed` — a never-silent, never-trusted uncertified count.
        let final_demote: Vec<SlotRef> = (0..n).filter(|&j| retained[j]).map(|j| slots_only[j]).collect();
        base.push_scope();
        for &(s, _) in &removed {
            base.assume(s, SlotKind::Ref);
        }
        for &d in &final_demote {
            base.add_borrow_exclusion(Some(d), &[]);
        }
        let witnessed = match base.model_kinds_relaxing(&selectors) {
            // Removed slots are hard-pinned `Ref`, so a SAT model has them all `Ref` by construction;
            // only acceptance remains to check.
            Some(m) => model_accepts(program, slots, &m, is_mutable),
            // UNSAT under the pins ⇒ the removed set is NOT jointly `Ref`-recoverable (unless empty).
            None => removed.is_empty(),
        };
        base.pop_scope();
        row.set("na_joint_witnessed", witnessed);

        if !witnessed {
            // Fail-closed: suppress the gate metric; do NOT emit `na_overpins` or the inventory.
            row.set("na_status", "witness-failed");
            return;
        }

        // Certified. Publish the gate number, the RED inventory, and the round distribution.
        row.set("na_overpins", removed.len());
        for &(s, r) in &removed {
            // Grep-able RED inventory (the `NBRCORE` pattern): one line per CERTIFIED over-pin.
            eprintln!("NAOVERPIN {program_name} {} round={r}", fmt_slot(program, slots, s));
        }
        let mut by_round: FxHashMap<usize, usize> = FxHashMap::default();
        for &(_, r) in &removed {
            *by_round.entry(r).or_default() += 1;
        }
        let mut rounds: Vec<(usize, usize)> = by_round.into_iter().collect();
        rounds.sort();
        row.set(
            "na_overpins_by_round",
            rounds.iter().map(|(r, c)| format!("{r}:{c}")).collect::<Vec<_>>().join("/"),
        );
        row.set("na_status", "ok");
    }

    /// BO mode: the exact `assert_ownership_parity` construction, with the native fixpoint loop's
    /// round/commit counts (`verify_to_fixpoint_counting`), per-phase timings, and the model readout
    /// (kind tallies + leaked sources).
    pub fn run_bo(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
        let t0 = Instant::now();
        let mut row = Row::default();
        row.set("t_tcx_s", secs(t_tcx));

        // §NB5-Z (2026-07-17): stamp the z3 library version on every BO row — provenance for the seed
        // pin. The PIN itself lives at the ignored `boc1_run_one` worker entry (see there for why it
        // must NOT live here or in the solver — both are reached by the parallel suite). Unconditional
        // now (was `CRAT_BOC1_COLLATERAL`-gated in NB4-4c-Q).
        row.set("z3_full_version", z3::full_version().to_string());

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

        // §NB4-4c SEED-SIZE GATE (amendment 1): compute-only poisoned-slot tiers + untabled-extern
        // histogram, then return BEFORE the emit/solve. Sizes the F2 arg/field extensions so the
        // demotion row cannot be catastrophic "for the wrong reason" (a printf/fprintf-class untabled
        // extern making every pointer arg it touches Raw). Off by default; no effect on normal sweeps.
        //   tier-1 `poison_base`             = current `collect_no_borrow_origin_slots` (fields skipped)
        //   tier-2 `poison_arg0_extern_delta`= depth-0 raw-ptr args to UNTABLED externs, NEW over base
        //   tier-3 `poison_field_sig`        = `summary.unknown` field-slots (count only; the kind-slot
        //                                      bridge is the deferred RED-5 spike, not needed for sizing)
        //   `untabled_externs`              = "name:ptr_arg_calls" histogram, top 12 by frequency
        if std::env::var_os("CRAT_BOC1_SEED_SIZE").is_some() {
            use crate::analyses::borrow_ownership::{
                boundary_table::{self, Matcher},
                origins::collect_no_borrow_origin_slots,
            };
            use rustc_hash::{FxHashMap, FxHashSet};
            use rustc_middle::mir::TerminatorKind;

            let slots = CrateSlots::build(&program);
            // The full no-borrow-origin set (base signature slots + mapped fields). Decompose it into
            // the two tiers so they don't double-count (the diagnostic's job is to isolate the field
            // extension): `poison_base` = unique Local members, `poison_field` = unique mapped
            // `SlotRef::Field` members. `all` (both) is the membership set the arg0-tier delta checks.
            let all: FxHashSet<SlotRef> =
                collect_no_borrow_origin_slots(&origins, &slots).into_iter().collect();
            let base: FxHashSet<SlotRef> = all
                .iter()
                .copied()
                .filter(|s| matches!(s, SlotRef::Local(..)))
                .collect();
            row.set("poison_base", base.len());
            row.set(
                "poison_field",
                all.iter().filter(|s| matches!(s, SlotRef::Field(_))).count(),
            );

            // c2rust emits cross-module *local* callees as `extern "C"` DECLARATIONS (ForeignItems
            // with no body) at their call sites, while the DEFINITION lives elsewhere in the crate.
            // Those are summary-covered, NOT opaque — exclude them by name so "opaque" means a
            // genuine foreign symbol (no crate-local definition), matching lifetime_flow's notion.
            let crate_fn_names: FxHashSet<String> = program
                .functions
                .iter()
                .map(|f| tcx.item_name(f.to_def_id()).to_string())
                .collect();

            let mut arg0_new: FxHashSet<SlotRef> = FxHashSet::default();
            let mut hist: FxHashMap<String, usize> = FxHashMap::default();
            for &fn_did in &program.functions {
                let Some(universe) = slots.fn_local_slots.get(&fn_did) else {
                    continue;
                };
                let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
                for bb in body.basic_blocks.iter() {
                    let Some(term) = &bb.terminator else { continue };
                    let TerminatorKind::Call { func, args, .. } = &term.kind else {
                        continue;
                    };
                    // Untabled extern = a crate-local `ForeignItem` decl with no ForeignC row
                    // (mirrors `sources.rs::is_allocator_call` gating). Opaque = worst-case.
                    let Some((def_id, _)) = func.const_fn_def() else { continue };
                    let Some(local_did) = def_id.as_local() else { continue };
                    let rustc_hir::Node::ForeignItem(fi) = tcx.hir_node_by_def_id(local_did) else {
                        continue;
                    };
                    let name = fi.ident.as_str();
                    if boundary_table::lookup(name, Matcher::ForeignC).is_some() {
                        continue; // tabled — a known effect row, not opaque
                    }
                    if crate_fn_names.contains(name) {
                        continue; // cross-module crate-local decl — summary-covered, not opaque
                    }
                    let mut ptr_args = 0usize;
                    for a in args.iter() {
                        let Some(place) = a.node.place() else { continue };
                        if !place.ty(&*body, tcx).ty.is_raw_ptr() {
                            continue;
                        }
                        ptr_args += 1;
                        if let Some(base_local) = place.as_local()
                            && let Some(id) = universe.slot_for_local_depth(base_local, 0)
                        {
                            let sref = SlotRef::Local(fn_did, id);
                            if !base.contains(&sref) {
                                arg0_new.insert(sref);
                            }
                        }
                    }
                    if ptr_args > 0 {
                        *hist.entry(name.to_string()).or_default() += ptr_args;
                    }
                }
            }
            row.set("poison_arg0_extern_delta", arg0_new.len());

            let field_sig: usize = origins
                .values()
                .map(|s| {
                    s.unknown
                        .iter()
                        .filter(|slot| s.slots[*slot].place.field.is_some())
                        .count()
                })
                .sum();
            row.set("poison_field_sig", field_sig);

            let mut hv: Vec<(String, usize)> = hist.into_iter().collect();
            hv.sort_by(|x, y| y.1.cmp(&x.1).then(x.0.cmp(&y.0)));
            let hs = hv
                .iter()
                .take(12)
                .map(|(n, c)| format!("{n}:{c}"))
                .collect::<Vec<_>>()
                .join(",");
            row.set("untabled_externs", hs);
            row.set("status", "seed-size");
            return row;
        }

        // §NB4-4c: `origins` is now THREADED into `emit_crate_ownership_constraints` below (F3) —
        // computed ONCE here (the `ORIGIN_WRAP_COUNT` runs-once site), passed by reference. No longer
        // the pre-4c uninjected `_origins`.

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

        // §NB4-4c per-class demotion counts (rider 5): the no-borrow-origin slots the may-supply
        // `¬ref` demotes, split base (Local) vs struct field. The honest per-class sweep columns.
        {
            let demoted =
                crate::analyses::borrow_ownership::origins::collect_no_borrow_origin_slots(
                    &origins, &slots,
                );
            let field_ct = demoted
                .iter()
                .filter(|s| matches!(s, SlotRef::Field(_)))
                .count();
            row.set("nb4c_demoted_base", demoted.len() - field_ct);
            row.set("nb4c_demoted_field", field_ct);
        }

        // §NB4-4c-Q COUNT-ONLY (compute-only, no solve): the over-inclusion COUNTS for programs whose
        // collateral SOLVE times out (binn/brotli under the 3-solve collateral mode). If a program's
        // upper over-inclusion is 0, its collateral is 0 by construction (no slot removed) — the gate is
        // complete without the expensive solve. Off by default; returns before emit/fixpoint.
        if std::env::var_os("CRAT_BOC1_COLLATERAL_COUNT").is_some() {
            use crate::analyses::borrow_ownership::origins::{
                collect_overincluded_modeled_origin_slots, collect_upperbound_overincluded_slots,
            };
            let dedup = |v: Vec<SlotRef>| v.into_iter().collect::<FxHashSet<_>>().len();
            row.set("nb4c_overincl_raw", dedup(collect_overincluded_modeled_origin_slots(&origins, &slots, false)));
            row.set("nb4c_overincl_mit", dedup(collect_overincluded_modeled_origin_slots(&origins, &slots, true)));
            row.set("nb4c_overincl_upper", dedup(collect_upperbound_overincluded_slots(&origins, &slots)));
            row.set("status", "collateral-count");
            return row;
        }

        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let t = Instant::now();
        let (stats, selectors) =
            match emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver) {
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
        // §NB5-M: native fork counters (the bo_c1 mirror is RETIRED — parity was proven at the NB5-M
        // gate, byte-identical to the NB5-Z baseline on all 19 both profiles). `verify_to_fixpoint_counting`
        // is the single CEGAR loop; `verify_to_fixpoint` is its model-only wrapper.
        // §NB5-L2: under `CRAT_BOC1_NECESSITY_AUDIT`, wrap the SAME solve in `with_capture` so Mode-A's
        // `(slot, round)` commits are recorded — a side-channel, so `(model, rstats)` are byte-identical
        // to the non-audit branch (the sweep numbers do not move whether or not the audit is on).
        let audit = std::env::var_os("CRAT_BOC1_NECESSITY_AUDIT").is_some();
        let ((model, rstats), captured) = if audit {
            let (mr, events) = with_capture(|| {
                verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, &mut_facts)
            });
            (mr, Some(events))
        } else {
            (
                verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, &mut_facts),
                None,
            )
        };
        row.set("t_fixpoint_s", secs(t.elapsed()));
        phase("fixpoint_done", t0);

        // §NB5-L guard 3 — mode-stamp the sweep row with the repair strategy that produced it, so the
        // S7 both-mode differential is never mode-ambiguous in the log.
        row.set("repair", rstats.repair.label());
        row.set("rounds", rstats.rounds);
        row.set("commits_conflict", rstats.commits_conflict);
        row.set("check_sat_count", solver.check_sat_count());
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

        // §S2-3 field-yield histogram (NB5-F). Model-independent buckets: `fields_total` = depth-0
        // pointer field slots (denominator); `stores_owned` = Owning CANDIDATES (≥1 owned store, no
        // blocking non-owned store) from the same scan the field-ownership constraints use; `blocked`
        // = fields with a non-owned store (upstream cause). `owning_model` (the S2-3 gate numerator —
        // fields that come out `Owning` in the accepted model) is emitted in the accept arm below.
        let s23_fields_total = (0..slots.field_slots.len())
            .filter(|&i| slots.field_slots.slot(SlotId::from_usize(i)).depth == 0)
            .count();
        let (s23_candidates, s23_blocked) = field_ownership_candidates(&slots, &program);
        row.set("s23_fields_total", s23_fields_total);
        row.set("s23_stores_owned", s23_candidates.len());
        row.set("s23_blocked", s23_blocked.len());

        match &model {
            None => {
                row.set("status", "decline");
                // §NB5-F: a field-conflict decline is SAT-with-a-non-`Ref`-field-residual, NOT an
                // UNSAT — running `decline_reason` (a selector-core replay) would misreport it as
                // `sat-in-replay`. Intercept it from the native stats FIRST, tag it distinctly, and
                // attribute it to the offending field for the sweep's per-program accounting (rider 1).
                // Only genuine UNSAT-family declines fall through to `decline_reason` + the explain path.
                // §NB5-L (Codex MEDIUM): a `Lemmas` cap-exhaustion decline is a relaxed-SAT model that
                // hit the round cap — NOT an UNSAT. Intercept it FIRST so `decline_reason` (a
                // selector-core replay) does not mislabel it `sat-in-replay` and hide the cap exhaustion.
                if let Some(reason) = &rstats.l2_decline {
                    row.set("decline_reason", "l2");
                    row.set("l2_decline", reason.diagnostic_label(rstats.rounds));
                } else if rstats.cap_exhausted {
                    row.set("decline_reason", "cap-exhausted");
                } else if let Some(field_slot) = rstats.field_conflict_decline {
                    row.set("decline_reason", "field-conflict");
                    if let SlotRef::Field(id) = field_slot
                        && let SlotOwner::Field(f) = slots.field_slots.slot(id).owner
                    {
                        row.set(
                            "decline_field",
                            format!("{}::field{}", tcx.def_path_str(f.struct_did.to_def_id()), f.field_index),
                        );
                    }
                } else {
                    row.set("decline_reason", decline_reason(&solver, &selectors));
                }
                // §NB-R (opt-in): explain the decline via a second, TRACKED
                // construction — labeled minimal core (or family histogram at
                // scale). Never on the default path: doubles solve cost. §NB5-F/L: skip for
                // field-conflict and cap-exhaustion declines (both are SAT, so the tracked replay
                // would not be UNSAT).
                if rstats.field_conflict_decline.is_none()
                    && !rstats.cap_exhausted
                    && std::env::var("CRAT_BOC1_EXPLAIN").map(|v| v == "1").unwrap_or(false) {
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
                // §S2-3 numerator: depth-0 struct-field slots that come out `Owning` in the accepted
                // model — the field-ownership yield the S2-3 gate ("still zero after NB5") consumes.
                // §NB5-F2: `s23_fields_raw` counts depth-0 field slots settled `Raw` — the direct
                // measure of the crate-wide field-demotion hammer (a Raw field's loans are disabled in
                // every function). These are INVISIBLE in `n_ref_d0`/`n_raw_d0` (Local-only), so this is
                // the column that shows the row's real field cost (pre-load 3).
                let mut s23_owning_model = 0usize;
                let mut s23_fields_raw = 0usize;
                for (s, kind) in m {
                    if let SlotRef::Field(id) = s
                        && slots.field_slots.slot(*id).depth == 0
                    {
                        match kind {
                            SlotKind::Owning => s23_owning_model += 1,
                            SlotKind::Raw => s23_fields_raw += 1,
                            SlotKind::Ref => {}
                        }
                    }
                }
                row.set("s23_owning_model", s23_owning_model);
                row.set("s23_fields_raw", s23_fields_raw);
                record_l2_red_inventory(
                    &program,
                    &slots,
                    m,
                    rstats.repair,
                    n_ref,
                    &mut row,
                );
            }
        }

        // §NB5-L2 commit-necessity audit (CRAT_BOC1_NECESSITY_AUDIT=1): leave-one-out over Mode-A's
        // captured commit set → the over-pin count = L2 headroom (a LOWER BOUND). MEASUREMENT-ONLY, off
        // by default; the `captured` events are `Some` only under the same gate.
        if let Some(events) = captured {
            // F3 (Codex): the audit measures Mode-A's commit set, and `with_capture` only records in the
            // Mode-A commit branch — so under any other `CRAT_BO_REPAIR` the events would be empty and the
            // audit would report a plausible-but-meaningless zero. Refuse it with an explicit status and no
            // numeric audit fields, rather than contaminating a comparative sweep.
            if rstats.repair != RepairMode::ModeA {
                row.set("na_status", "wrong-repair-mode");
            } else {
                let t = Instant::now();
                run_necessity_audit(&program, &slots, &origins, &mut_facts, &model, &events, &mut row);
                row.set("t_necessity_s", secs(t.elapsed()));
                phase("necessity_done", t0);
            }
        }

        // §NB4-4c-Q collateral measurement (CRAT_BOC1_COLLATERAL=1): size the coherence-collateral
        // Ref-loss from over-including modeled-origin slots (Codex re-review 2026-07-17). Two extra
        // real solves in-process (FULL then MINUS); MEASUREMENT-ONLY. Off by default. Gate metric =
        // `nb4c_collateral_d0` (net corpus-wide); `nb4c_collateral` (full n_ref) reported alongside
        // because FIELD collateral is invisible at depth-0.
        if std::env::var_os("CRAT_BOC1_COLLATERAL").is_some() {
            let t = Instant::now();
            let cm = measure_collateral(&program, &slots, &origins, &mut_facts);
            row.set("nb4c_collateral_status", cm.status);
            row.set("nb4c_overincl_raw", cm.overincl_raw);
            row.set("nb4c_overincl_mit", cm.overincl_mit);
            row.set("nb4c_overincl_upper", cm.overincl_upper);
            row.set("nb4c_collateral_mit", cm.collateral_mit); // n_ref delta, may be < 0
            row.set("nb4c_collateral_d0_mit", cm.collateral_d0_mit);
            row.set("nb4c_collateral_upper", cm.collateral_upper); // the GATE numerator (upper bound)
            row.set("nb4c_collateral_d0_upper", cm.collateral_d0_upper);
            // ANCHOR (amendment 4a + Codex F2b): when the measurement actually solved FULL, it must
            // reproduce the shipped n_ref AND n_ref_d0 — validates emit(empty)+manual-demotion ≡ the
            // shipped pipeline here. A mismatch is a hard STOP. (Committed-row anchor is the external
            // check, post-sweep; a "real-decline" status is surfaced, never silent — F2a.) §NB5-M:
            // "shipped" is now run_bo's NATIVE `verify_to_fixpoint_counting` model (mirror retired).
            if let (Some(nf), Some(nd0), Some(m)) = (cm.nref_full, cm.nref_d0_full, &model) {
                let (shipped_nref, shipped_nref_d0) = count_refs(m, &slots);
                assert_eq!(
                    nf, shipped_nref,
                    "NB4-4c-Q ANCHOR: FULL n_ref ({nf}) != shipped n_ref ({shipped_nref})"
                );
                assert_eq!(
                    nd0, shipped_nref_d0,
                    "NB4-4c-Q ANCHOR: FULL n_ref_d0 ({nd0}) != shipped n_ref_d0 ({shipped_nref_d0})"
                );
            }
            row.set("t_collateral_s", secs(t.elapsed()));
            phase("collateral_done", t0);
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
                // §NB4-4c F3: CHECK_REAL reuses run_bo's `origins` — the SAME demotion seed as run_bo's
                // native solve, so the fidelity cross-check compares identical clause sets.
                match emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver) {
                    Ok((_s, selectors)) => {
                        for &g in &program.functions {
                            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                            add_coherence(&solver, &slots, g, &body);
                        }
                        // §NB2: same oracle as run_bo's native solve above, so the fidelity check
                        // compares like with like (shipped facts vs a fresh real solve).
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
                        "real_matches_model",
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

/// Shared C2Rust delete-node fixture (was defined among the retired mirror tests; several surviving
/// NB-F / leak tests below use it).
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

// ---------------------------------------------------------------------------
// §NB5-M wrapper-thinness guard (replaces the retired mirror-fidelity tests).
// ---------------------------------------------------------------------------

/// §NB5-M: guards WRAPPER-THINNESS. `verify_to_fixpoint` is a model-only wrapper over
/// `verify_to_fixpoint_counting` (the single CEGAR loop). This is a near-tautology today — the
/// wrapper literally returns `verify_to_fixpoint_counting(..).0` — and that is exactly its purpose:
/// if anyone later adds logic to the wrapper (a filter, retry, or a different solve), the sweep's
/// NATIVE counters would silently diverge from the model the suite verifies through the wrapper (the
/// mirror-drift the retired `boc1_mirror_matches_real_*` tests guarded). It runs an accept-no-commit
/// and an accept-with-commit shape so the loop is exercised; decline yields the same wrapper==native
/// by construction (both are the same loop).
#[test]
fn verify_to_fixpoint_is_thin_wrapper() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{verify_to_fixpoint, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    let shapes = [
        // accept, no commit (rounds == 1).
        "unsafe fn f(p: *mut i32) -> *mut i32 { let q = p; q }",
        // accept with a commit (coherence drags the modeled-origin param to Raw).
        "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
         unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; q }",
    ];
    for code in shapes {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let build = || {
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                for &g in &program.functions {
                    let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                    add_coherence(&solver, &slots, g, &body);
                }
                (solver, selectors)
            };
            let (ws, wsel) = build();
            let wrapper = verify_to_fixpoint(&program, &slots, &ws, &wsel, true);
            let (ns, nsel) = build();
            let native = verify_to_fixpoint_counting(&program, &slots, &ns, &nsel, true).0;
            assert_eq!(
                wrapper, native,
                "§NB5-M: verify_to_fixpoint (wrapper) must equal verify_to_fixpoint_counting(..).0 — \
                 keep the wrapper thin"
            );
        })
        .unwrap_or_else(|e| e.raise());
    }
}

/// §NB5-M counter contract (Codex RE-4 fold): pins native `RoundStats` so a counter regression can
/// NOT pass the suite silently. The retired mirror-fidelity tests + the parity-window dual-compute
/// asserted these counters; the wrapper-thinness test guards only the model, so this is now the sole
/// counter guard. Covers accept-no-commit, accept-with-commit, sink-drop, and source-drop; the
/// decline paths (rounds carried on `None`) are structural (rounds only increments inside the loop)
/// and were checked in the NB5-M review (RE-3).
#[test]
fn nb5m_native_round_stats_contract() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{RoundStats, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    fn stats_of(code: &str) -> RoundStats {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, selectors) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emission");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            verify_to_fixpoint_counting(&program, &slots, &solver, &selectors, true).1
        })
        .unwrap_or_else(|e| e.raise())
    }
    // (a) accept-first-model, no commit.
    let accept = stats_of("unsafe fn f(p: *mut i32) -> *mut i32 { let q = p; q }");
    assert_eq!(accept.rounds, 1, "accept: one round");
    assert_eq!(accept.commits_conflict, 0, "accept: no commits");
    assert_eq!(accept.commits_per_round, vec![0], "accept: [0]");
    assert_eq!(accept.dropped_sinks, 0, "accept: no sinks");
    assert_eq!(accept.dropped_sources, 0, "accept: no sources");
    // §NB5-F: an accept never carries a field-conflict decline. Under NB5-F2 the field-conflict
    // path now RESTORES (field loan disabled → accept with the field Raw; see
    // `nb5f2_field_conflict_restores`); `field_conflict_decline` stays reachable only as the backstop
    // for genuinely un-dischargeable field residuals.
    assert_eq!(accept.field_conflict_decline, None, "accept: no field-conflict decline");
    // (b) accept WITH a conflict CASCADE: `x = id(p)` is a live Ref requirer invalidated by the write
    // through the base `b = p` (A′), committed `¬ref` over two commit rounds + the accepting round.
    let commit = stats_of(
        "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
         unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }",
    );
    assert_eq!(commit.rounds, 3, "cascade: 2 commit rounds + accepting round");
    assert_eq!(commit.commits_conflict, 2, "cascade: two commits");
    assert_eq!(commit.commits_per_round, vec![1, 1, 0], "cascade: one commit/round then accept");
    assert_eq!(commit.dropped_sinks, 0);
    assert_eq!(commit.dropped_sources, 0);
    // (c) sink drop: the delete-node witness commits 3 conflicts, then the final solve leaks its two
    // free sinks. `dropped_sources == 0` here guards the `record_dropped` is_sink split (a regression
    // counting the 2 sinks as sources would make this 2). Genuine source-leak COUNTING
    // (`dropped_sources > 0`) is exercised across the corpus and was verified at the NB5-M parity gate.
    let sink = stats_of(DELETE_NODE_WITNESS);
    assert_eq!(sink.rounds, 2);
    assert_eq!(sink.commits_conflict, 3);
    assert_eq!(sink.commits_per_round, vec![3, 0]);
    assert_eq!(sink.dropped_sinks, 2, "delete-node leaks its two free sinks");
    assert_eq!(sink.dropped_sources, 0, "the two dropped selectors are BOTH sinks (is_sink split)");
    // (d) POSITIVE source drop (Codex RR-2): `&raw mut p` escapes the address of a malloc'd local,
    // so the alloc cannot be proven Owning; the eager `¬ref(source)` round-1 model surfaces one
    // conflict, committed into the accepting round-2 model, and the final solve DROPS the source
    // selector. This is the ONLY shape that pins `dropped_sources > 0` (the others pin it at 0).
    let source = stats_of(
        "unsafe extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; } \
         pub unsafe fn leak() -> *mut *mut core::ffi::c_void { let mut p = malloc(8); &raw mut p }",
    );
    assert_eq!(source.rounds, 2, "source-drop: eager ¬ref round-1 + accepting round-2");
    assert_eq!(source.commits_conflict, 1, "source-drop: one commit");
    assert_eq!(source.commits_per_round, vec![1, 0]);
    assert_eq!(source.dropped_sinks, 0, "no free in this shape");
    assert_eq!(source.dropped_sources, 1, "the leaked alloc drops its source selector (POSITIVE)");
}

/// §NB5-F — field-universe expansion makes struct-field borrow conflicts visible to the BO
/// verifier (`owner_to_slot` no longer drops `Field` owners). Because the replay candidacy is
/// Local-only, a field requirer cannot be soundly demoted (its loan is not model-gated), so the
/// A′ principle extended to field requirers yields a DECLINE (Option A) rather than an unsound
/// discharge. This fixture is also the empirical test of the three-fact mechanism reading:
/// pre-partition it fails as the guard PANIC (`borrow_verify.rs` "every residual conflict slot
/// must be Ref"); post-partition it declines with the offending field tagged. Both shapes assert
/// the FINAL semantics: model `None` + `field_conflict_decline = Some(the field)`.
#[test]
fn nb5f2_field_conflict_restores() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt, SlotKind,
        borrow_verify::verify_to_fixpoint_counting,
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        slots::{SlotId, SlotOwner},
        solver::{KindSolver, SlotRef},
    };
    // §NB5-F2: run the BO verifier and report (accepted?, kinds of every depth-0 FIELD slot in the
    // accepted model, the tagged decline field if it declined). F2 extends the fork's demotion loop to
    // DISABLE a Raw field's loan (via the manifest-widened `disable_owner(Field)`) — so a field
    // conflict that F CB-declined now clears and ACCEPTS with the field `Raw`, exactly like a local.
    struct Outcome {
        accepted: bool,
        field_kinds: Vec<(String, SlotKind)>,
    }
    fn run(code: &str) -> Outcome {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, sel) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emission");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            let field_name = |id: SlotId| match slots.field_slots.slot(id).owner {
                SlotOwner::Field(f) => {
                    format!("{}::field{}", tcx.item_name(f.struct_did.to_def_id()), f.field_index)
                }
                SlotOwner::Local(_) => "LOCAL-owner(bug)".to_string(),
            };
            let (model, _stats) =
                verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true);
            let mut field_kinds = Vec::new();
            if let Some(m) = &model {
                for (s, kind) in m {
                    if let SlotRef::Field(id) = s
                        && slots.field_slots.slot(*id).depth == 0
                    {
                        field_kinds.push((field_name(*id), *kind));
                    }
                }
            }
            Outcome { accepted: model.is_some(), field_kinds }
        })
        .unwrap_or_else(|e| e.raise())
    }

    // (1) PURE field conflict (the F fixture, flipped): `h.p` borrows `x`, `x = 1` invalidates that
    // loan, `*h.p` uses it after. Under F this DECLINED (field requirer un-dischargeable); under F2 the
    // demotion loop disables `Holder::field0`'s loan → the conflict clears → ACCEPT with the field Raw.
    let o = run(
        "struct Holder { p: *mut i32 } \
         unsafe fn f() { let mut x = 0i32; let mut h = Holder { p: core::ptr::null_mut() }; \
         h.p = &raw mut x; x = 1; *h.p = 2; }",
    );
    assert!(o.accepted, "F2: pure field conflict must now ACCEPT (field loan disabled), not decline");
    assert!(
        o.field_kinds.contains(&("Holder::field0".to_string(), SlotKind::Raw)),
        "F2: the restored field settles Raw (its loan was disabled); got {:?}",
        o.field_kinds
    );

    // (2) MIXED edge (local `v` + field `h.p` both alias `x`, both written after): under F2 the field
    // is disabled AND the local `v` demotes on its own path → ACCEPT with the field Raw.
    let o = run(
        "struct Holder { p: *mut i32 } \
         unsafe fn f() { let mut x = 0i32; let mut h = Holder { p: core::ptr::null_mut() }; \
         let v = &raw mut x; h.p = &raw mut x; x = 1; *h.p = 2; *v = 3; }",
    );
    assert!(o.accepted, "F2: mixed local+field conflict must now ACCEPT, not decline");
    assert!(
        o.field_kinds.contains(&("Holder::field0".to_string(), SlotKind::Raw)),
        "F2: the restored field settles Raw; got {:?}",
        o.field_kinds
    );

    // (3) BACKSTOP TRIPWIRE (Codex NB5-F2 HIGH). The fix: F2 disables only EXACT-`Raw` fields, so an
    // `Owning` field is NEVER disabled — it falls through to the `residual_nonref_field` decline. A
    // POSITIVE owning-field-decline fixture is NOT constructible: an owning field is all-malloc-store
    // (no `&`-loan), so it cannot BE in a borrow conflict, and the solver prefers `Ref`/`Raw` over
    // `Owning` anyway (corpus-wide `s23_owning_model == 0`). So this is a defensive tripwire, not a
    // positive exercise (rider-3: don't synthesize). Codex's shape (a malloc'd pointer stored into
    // `H::p`, then aliased+written) DOES produce a field conflict; the field settles `Raw` and F2
    // restores it. The invariant we guard: **no accepted model of a field-conflict shape may carry an
    // `Owning` field** — that would be the unsound owning-field-aliased accept the exact-`Raw` guard
    // exists to prevent. Coverage of the owning branch rests on the exact-`Raw` predicate itself (cf.
    // the NB5-F Local-assert arm), not a synthesized case.
    let o = run(
        "unsafe extern \"C\" { fn malloc(n: usize) -> *mut core::ffi::c_void; } \
         struct H { p: *mut i32 } \
         unsafe fn f() { let mut h = H { p: core::ptr::null_mut() }; \
         let p = malloc(4) as *mut i32; h.p = p; *p = 1; let _ = *h.p; }",
    );
    assert!(
        !(o.accepted && o.field_kinds.iter().any(|(_, k)| *k == SlotKind::Owning)),
        "F2 BACKSTOP: an accepted field-conflict model must not carry an Owning field (exact-Raw \
         guard regressed → owning-field disable → unsound accept); got {:?}",
        o.field_kinds
    );
}

/// §S2-3 DIAGNOSTIC PROBE (NB5-F2 carried item 2; compute-only, no fixes). The corpus histogram shows
/// 155 owning-store field CANDIDATES but 0 field-`Owning` in-model, with `s23_blocked == 0` everywhere —
/// so the ⋀-law store-block (family (a)) is ruled out. This probe answers the remaining question on an
/// owning-CAPABLE field (malloc store + `free` sink, the corpus candidate pattern): is `own(field)`
/// **achievable** (SAT ⇒ the zero yield is a SOFT objective/retention blocker — `Ref ≻ Raw ≻ Owning` +
/// leak-minimal drops the source/sink rather than paying `Owning`), or **hard-blocked** (UNSAT ⇒ a
/// constraint family forbids it)? Reports the verdict; not a fix.
#[test]
#[ignore = "S2-3 diagnostic probe (compute-only); run explicitly"]
fn s23_owning_blocker_probe() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        coherence::{add_coherence, constrain_field_ownership},
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        slots::{SlotId, SlotOwner},
        solver::{KindSolver, SlotRef},
    };
    use z3::{SatResult, ast::Bool};
    ::utils::compilation::run_compiler_on_str(
        "unsafe extern \"C\" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); } \
         struct H { p: *mut i32 } \
         unsafe fn f() { let mut h = H { p: core::ptr::null_mut() }; \
         h.p = malloc(4) as *mut i32; free(h.p as *mut core::ffi::c_void); }",
        |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            // TRACKED solver so an UNSAT core maps to labeled constraint families (per `explain_unsat`).
            let solver = KindSolver::new_tracked(&slots);
            let (_s, selectors) = emit_crate_ownership_constraints(
                &crate_ctxt, &slots, &compute_origins(&program), &solver,
            ).expect("emission");
            let tracker = solver.tracker().expect("new_tracked");
            tracker.set_context("coherence");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            tracker.set_context("field-law");
            constrain_field_ownership(&solver, &slots, &program);
            let field = (0..slots.field_slots.len())
                .map(SlotId::from_usize)
                .find(|&sid| {
                    slots.field_slots.slot(sid).depth == 0
                        && matches!(slots.field_slots.slot(sid).owner, SlotOwner::Field(_))
                })
                .map(SlotRef::Field)
                .expect("H::p depth-0 field slot");
            tracker.set_context("s23-force-own");
            solver.assert_owning(field);
            // Assume every track (⇔ the untracked hard system) + all source/sink selectors retained.
            let mut assumptions: Vec<Bool> = tracker.tracks();
            assumptions.extend(selectors.all().iter().cloned());
            match solver.optimize().check(&assumptions) {
                SatResult::Sat => eprintln!("S23_PROBE field={field:?} force_own=SAT (SOFT blocker: own achievable, objective/retention settles it lower)"),
                SatResult::Unknown => eprintln!("S23_PROBE field={field:?} force_own=UNKNOWN"),
                SatResult::Unsat => {
                    let core = solver.optimize().get_unsat_core();
                    let labels: Vec<String> = core.iter().map(|l| {
                        tracker.label_of(l).unwrap_or_else(|| {
                            if selectors.is_sink(l) { "sink-selector".to_string() }
                            else { "source-selector".to_string() }
                        })
                    }).collect();
                    eprintln!(
                        "S23_PROBE field={field:?} force_own=UNSAT (HARD blocker) core_labels={labels:?}"
                    );
                }
            }
        },
    )
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
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &crate::analyses::borrow_ownership::origins::compute_origins(&program), &solver).expect("emission");
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
            emit_crate_ownership_constraints(&crate_ctxt, &slots, &crate::analyses::borrow_ownership::origins::compute_origins(&program), &solver)
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

    // §NB5-Z (2026-07-17): pin z3's random seeds for the BO sweep — HERE, at the ignored per-program
    // worker entry, before ANY z3 op in this fresh process. z3 0.19's `Context` is a per-thread
    // `thread_local!` built once as `Context::new(&Config::new())` and reused; `set_global_param` only
    // feeds a context created AFTER it fires, so the pin must precede this process's first z3 touch.
    // This is the ONLY correct site: `run_bo` and `solver.rs` are both reached by NON-ignored suite
    // tests (e.g. `origins_runs_once_per_program` calls `run_bo` directly), so pinning there would leak
    // this PROCESS-GLOBAL param into the PARALLEL test runner (Codex NB5-Z finding). `boc1_run_one` is
    // `#[ignore]` and spawned one-per-program as a fresh single-threaded process, so the pin fires once
    // per program and never under the parallel suite. Gated to `bo` mode — NB5-Z's scope is BO
    // determinism; `prod` is the frozen production reference, left untouched. Expected behavior-neutral
    // (z3's default seed is already 0 — the NB5-Z re-baseline is byte-identical on both profiles); its
    // value is the explicit cross-VERSION contract, recorded as the `z3_full_version` stamp on each BO row.
    if mode == "bo" {
        z3::set_global_param("smt.random_seed", "0");
        z3::set_global_param("sat.random_seed", "0");
    }

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

/// Evaluation corpus under `benchmarks/rs-crown/`, smallest-first by measured Rust SLOC.
/// SLOC is cloc 2.00's `code` total over each program's `.rs` files, excluding `build.rs` and
/// `target/`, with duplicate files counted. The development boundary is inclusive of brotli.
#[derive(Clone, Copy, Debug)]
struct CorpusProgram {
    name: &'static str,
    lib_root: &'static str,
    sloc: usize,
}

impl CorpusProgram {
    fn input_path(self, root: &std::path::Path) -> std::path::PathBuf {
        root.join("benchmarks/rs-crown")
            .join(self.name)
            .join(self.lib_root)
    }
}

const BROTLI_SLOC: usize = 537_692;

const fn is_resource_deferred(sloc: usize) -> bool {
    sloc > BROTLI_SLOC
}

const CORPUS: &[CorpusProgram] = &[
    CorpusProgram {
        name: "bst",
        lib_root: "lib.rs",
        sloc: 102,
    },
    CorpusProgram {
        name: "avl",
        lib_root: "lib.rs",
        sloc: 133,
    },
    CorpusProgram {
        name: "ht",
        lib_root: "lib.rs",
        sloc: 251,
    },
    CorpusProgram {
        name: "libcsv",
        lib_root: "lib.rs",
        sloc: 963,
    },
    CorpusProgram {
        name: "buffer",
        lib_root: "lib.rs",
        sloc: 1_104,
    },
    CorpusProgram {
        name: "quadtree",
        lib_root: "lib.rs",
        sloc: 1_184,
    },
    CorpusProgram {
        name: "urlparser",
        lib_root: "lib.rs",
        sloc: 1_363,
    },
    CorpusProgram {
        name: "robotfindskitten",
        lib_root: "lib.rs",
        sloc: 1_476,
    },
    CorpusProgram {
        name: "rgba",
        lib_root: "lib.rs",
        sloc: 1_823,
    },
    CorpusProgram {
        name: "genann",
        lib_root: "lib.rs",
        sloc: 2_302,
    },
    CorpusProgram {
        name: "libtree",
        lib_root: "lib.rs",
        sloc: 2_578,
    },
    CorpusProgram {
        name: "json.h",
        lib_root: "lib.rs",
        sloc: 3_847,
    },
    CorpusProgram {
        name: "binn",
        lib_root: "lib.rs",
        sloc: 4_413,
    },
    CorpusProgram {
        name: "libzahl",
        lib_root: "lib.rs",
        sloc: 4_642,
    },
    CorpusProgram {
        name: "lil",
        lib_root: "lib.rs",
        sloc: 5_638,
    },
    CorpusProgram {
        name: "heman",
        lib_root: "lib.rs",
        sloc: 13_750,
    },
    CorpusProgram {
        name: "bzip2",
        lib_root: "c2rust-lib.rs",
        sloc: 13_967,
    },
    CorpusProgram {
        name: "lodepng",
        lib_root: "lib.rs",
        sloc: 14_140,
    },
    CorpusProgram {
        name: "tulipindicators",
        lib_root: "c2rust-lib.rs",
        sloc: 19_760,
    },
    CorpusProgram {
        name: "brotli",
        lib_root: "lib.rs",
        sloc: BROTLI_SLOC,
    },
];

#[test]
fn rs_crown_catalog_contract() {
    let expected = [
        ("bst", "lib.rs", 102),
        ("avl", "lib.rs", 133),
        ("ht", "lib.rs", 251),
        ("libcsv", "lib.rs", 963),
        ("buffer", "lib.rs", 1_104),
        ("quadtree", "lib.rs", 1_184),
        ("urlparser", "lib.rs", 1_363),
        ("robotfindskitten", "lib.rs", 1_476),
        ("rgba", "lib.rs", 1_823),
        ("genann", "lib.rs", 2_302),
        ("libtree", "lib.rs", 2_578),
        ("json.h", "lib.rs", 3_847),
        ("binn", "lib.rs", 4_413),
        ("libzahl", "lib.rs", 4_642),
        ("lil", "lib.rs", 5_638),
        ("heman", "lib.rs", 13_750),
        ("bzip2", "c2rust-lib.rs", 13_967),
        ("lodepng", "lib.rs", 14_140),
        ("tulipindicators", "c2rust-lib.rs", 19_760),
        ("brotli", "lib.rs", 537_692),
    ];
    let actual: Vec<_> = CORPUS
        .iter()
        .map(|program| (program.name, program.lib_root, program.sloc))
        .collect();

    assert_eq!(CORPUS.len(), 20);
    assert_eq!(actual.as_slice(), expected.as_slice());
    assert_eq!(BROTLI_SLOC, 537_692);
    assert!(!is_resource_deferred(BROTLI_SLOC));
    assert!(is_resource_deferred(BROTLI_SLOC + 1));
    assert!(CORPUS
        .iter()
        .all(|program| !is_resource_deferred(program.sloc)));

    let root = orchestrate::workspace_root();
    for program in CORPUS {
        let input = program.input_path(&root);
        assert!(
            input.is_file(),
            "missing rs-crown input for {}: {input:?}",
            program.name
        );
        assert!(input.starts_with(root.join("benchmarks/rs-crown")));

        let expected_root = if matches!(program.name, "bzip2" | "tulipindicators") {
            "c2rust-lib.rs"
        } else {
            "lib.rs"
        };
        assert_eq!(
            input.file_name().and_then(|name| name.to_str()),
            Some(expected_root)
        );
    }
}

#[test]
fn rs_crown_report_contract() {
    let mut row = report::Row::default();
    row.set("program", "bst");
    row.set("status", "ok");
    row.set("repair", "mode_a");
    row.set("z3_full_version", "test-version");
    row.set("sources_leaked_sel", 1);
    row.set("sinks_leaked", 2);
    row.set("s23_stores_owned", 3);
    row.set("s23_owning_model", 4);

    let rendered = render_report(&[row]);
    assert!(rendered.contains("repair=mode_a; smt.random_seed=0; sat.random_seed=0"));
    assert!(rendered.contains("z3_full_version=test-version"));
    for column in [
        "sources_leaked_sel",
        "sinks_leaked",
        "s23_stores_owned",
        "s23_owning_model",
    ] {
        assert!(
            rendered.contains(column),
            "missing report column {column}:\n{rendered}"
        );
    }
}

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
    let l2_gate = l2_red_gate::enabled();
    if l2_gate {
        l2_red_gate::assert_fixtures(CORPUS);
        for name in [
            "CRAT_BO_SAFE_MONO",
            "CRAT_BO_MUT_FACTS",
            "CRAT_BO_FORK_ENGINE",
            "CRAT_NB4R_ROUTING",
        ] {
            assert!(
                std::env::var_os(name).is_none(),
                "L2 RED requires the frozen base contract with {name} unset"
            );
        }
        assert_eq!(
            crate::analyses::borrow_ownership::SafeMonoMode::current(),
            crate::analyses::borrow_ownership::SafeMonoMode::PerSite,
            "L2 RED requires the frozen per-site safety profile"
        );
        assert_eq!(
            crate::analyses::borrow_ownership::mutability_facts::MutFactsMode::current(),
            crate::analyses::borrow_ownership::mutability_facts::MutFactsMode::On,
            "L2 RED requires the frozen mutability-facts profile"
        );
        assert_eq!(
            crate::analyses::borrow_ownership::borrow_engine::ForkEngineMode::current(),
            crate::analyses::borrow_ownership::borrow_engine::ForkEngineMode::Fork,
            "L2 RED requires the frozen fork-engine profile"
        );
        assert_eq!(
            std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
            Ok("1"),
            "L2 RED requires CRAT_BO_L2_GUARDED_COMMITS=1"
        );
        assert!(
            crate::analyses::borrow_ownership::l2::enabled_from_env(),
            "L2 RED feature flag did not resolve on"
        );
        assert_eq!(
            std::env::var("CRAT_BO_REPAIR").as_deref(),
            Ok("mode_a"),
            "L2 RED requires CRAT_BO_REPAIR=mode_a"
        );
        assert_eq!(
            crate::analyses::borrow_ownership::borrow_verify::RepairMode::current(),
            crate::analyses::borrow_ownership::borrow_verify::RepairMode::ModeA,
        );
        assert_eq!(
            std::env::var("CRAT_POINTER_DECISION_DIAGNOSTICS").as_deref(),
            Ok("raw"),
            "L2 RED requires CRAT_POINTER_DECISION_DIAGNOSTICS=raw"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_TIMEOUT_SECS").as_deref(),
            Ok("900"),
            "L2 RED requires the official 900-second worker timeout"
        );
        assert_eq!(
            timeout,
            Duration::from_secs(900),
            "L2 RED effective timeout drifted"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
            Ok("8192"),
            "L2 RED requires the official 8192-MiB memory cap"
        );
        assert_eq!(
            std::env::var("CRAT_BOC1_PROD").as_deref(),
            Ok("0"),
            "L2 RED must run only the Mode-A BO worker"
        );
        assert!(!prod_enabled, "L2 RED production-baseline child must be disabled");
        assert!(
            only.is_none(),
            "L2 RED must not set CRAT_BOC1_PROGRAMS; run all 20 frozen programs"
        );
        assert_eq!(CORPUS.len(), 20, "L2 RED frozen corpus size drifted");
        assert_eq!(
            CORPUS.last().map(|program| program.name),
            Some("brotli"),
            "L2 RED must include brotli as the final development-boundary row"
        );
        assert!(
            CORPUS
                .iter()
                .all(|program| !is_resource_deferred(program.sloc)),
            "L2 RED cannot resource-defer any frozen rs-crown program"
        );
    }

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

    for &program in CORPUS {
        if let Some(only) = &only
            && !only.iter().any(|p| p == program.name)
        {
            continue;
        }
        let input = program.input_path(&root);
        assert!(input.is_file(), "missing crate root {input:?}");

        let mut m = Row::default();
        m.set("program", program.name);
        m.set("dir", program.name);
        m.set("sloc", program.sloc);

        if is_resource_deferred(program.sloc) {
            m.set("status", "resource-deferred");
            m.set("note", format!("sloc_gt_brotli_{BROTLI_SLOC}"));
            eprintln!(
                "[boc1] {} ({}, {} SLOC): resource-deferred (> brotli {})",
                program.name, program.lib_root, program.sloc, BROTLI_SLOC
            );
        } else {
            eprintln!(
                "[boc1] {} ({}, {} SLOC): bo mode...",
                program.name, program.lib_root, program.sloc
            );
            let bo = run_child(program.name, &input, "bo", timeout);
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
                eprintln!("[boc1] {}: prod mode...", program.name);
                let prod = run_child(program.name, &input, "prod", prod_timeout);
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
        }

        eprintln!("[boc1] {}: {}", program.name, report::to_kv_line(&m));
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
    if l2_gate {
        l2_red_gate::assert_results(&merged, CORPUS);
    }
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
        "check_sat_count",
        "slots_total",
        "n_ref",
        "n_raw",
        "n_own",
        "n_ref_d0",
        "n_own_d0",
        "n_ref_shared_d0",
        "n_ref_mut_d0",
        "mut_facts",
        "mut_default_fires",
        "n_ref_prod",
        "d_ref_d0",
        "l2_base_n_ref",
        "l2_n_ref_delta",
        "l2_targets_expected",
        "l2_targets_found",
        "l2_targets_ref",
        "sources_total",
        "sources_leaked",
        "sources_leaked_sel",
        "sinks_total",
        "sinks_leaked",
        "s23_stores_owned",
        "s23_owning_model",
        "s23_blocked",
        "decline_reason",
        "l2_decline",
        "core_families",
        "core_minimized",
        "prod_status",
    ];
    let repair = merged
        .iter()
        .find_map(|row| row.get("repair"))
        .unwrap_or("pending");
    let z3_version = merged
        .iter()
        .find_map(|row| row.get("z3_full_version"))
        .unwrap_or("pending");
    let deferred = CORPUS
        .iter()
        .filter(|program| is_resource_deferred(program.sloc))
        .count();
    let mut out = String::from("# rs-crown BO baseline report\n\n");
    out.push_str(&format!(
        "Run contract: repair={repair}; smt.random_seed=0; sat.random_seed=0; \
         z3_full_version={z3_version}.\n\n\
         Corpus: the 20 programs in `benchmarks/rs-crown/`, smallest-first by Rust SLOC. \
         Brotli is the inclusive development boundary at {BROTLI_SLOC} SLOC; \
         resource-deferred means strictly greater than brotli ({deferred} programs in this catalog).\n\n"
    ));
    out.push_str(
        "`d_ref_d0` = BO depth-0 local Ref count minus the optional production baseline's \
         (`demote_pointers_iterative_with_fields` from all-Ref, same accounting). \
         `decline_reason` separates non-source UNSAT from z3 Unknown (harness-side \
         phase-1 replay). `sources_total`/`sources_leaked` count malloc-source SLOTS \
         (propagation-closed over copies/moves/casts, so one allocation can contribute \
         several slots, e.g. its `free` call-arg temp); a slot is leaked when its final \
         kind is not Owning. `sources_leaked_sel` and `sinks_leaked` count dropped source/sink \
         SELECTORS. `s23_stores_owned` counts field owning-store candidates; \
         `s23_owning_model` counts those emerging Owning in an accepted model. \
         `commits_conflict` counts exclusion assertions exactly as the real \
         loop's `committed` does — the same slot can be committed by several conflicts \
         in one round, so this is commit OPERATIONS, not unique slots. `d_ref_d0` is a \
         Ref-count delta, not a pure borrow-precision delta: BO's non-Ref includes \
         Owning (a win) and leaked-source Raw — read it together with `n_own`. \
         `wall_s` is supervision-level (includes up to ~200ms poll latency); \
         `t_total_s` in the CSV/JSONL is the child-measured time.\n\n",
    );
    out.push_str(&report::render_markdown(merged, &cols));
    if merged.iter().any(|row| row.get("l2_feature") == Some("on")) {
        out.push_str("\n\n");
        out.push_str(&l2_red_gate::summary(merged));
        out.push('\n');
    }
    out
}

/// §NB5-L — the empty-context disjunctive lemma vs Mode-A, per-slot (first-touch dump 2026-07-18; the
/// original "≡ Mode-A" claim was an AGGREGATE-COUNT claim, REFUTED by this per-slot check — Codex-
/// demanded). **This is an EMPIRICAL observation on these fixtures + the pinned seed, NOT a universal
/// law** (Codex re-review): the loop is NON-CONFLUENT, so the two models are **incomparable in
/// general** — there is no proof `Ref(lemmas) ⊆ Ref(mode_a)` always holds. What IS established: on the
/// fixtures below the inclusion holds, and on a 33-requirer fan-out it is STRICT — Lemmas loses ≥1 Ref
/// by demoting a NON-MINIMAL menu member (`nb5l_high_arity_lemmas_converges_no_panic`), the hazard
/// `verify_to_fixpoint`'s doc names ("Mode A = monotone single-slot commitment, deliberately NOT
/// disjunctive"). So the disjunction has no established upside and a demonstrated downside — the
/// disjunction axis is DEAD; the positive win, if any, is NB5-L2's orthogonal context axis
/// (context-conditioned SINGLE-LITERAL commits, hazard-free), gated behind the commit-necessity audit.
/// Non-vacuity: at least one shape emits a genuine ≥2-literal A′ menu (distinct requirers ≠ issuer), so
/// the disjunction path is actually exercised (not a trivial singleton ≡ Mode-A).
#[cfg(test)]
#[test]
fn nb5l_lemma_ref_subset_mode_a_on_fixtures() {
    use rustc_hash::{FxHashMap, FxHashSet};

    use crate::analyses::borrow_ownership::{
        CrateCtxt, SlotKind,
        borrow_verify::{RepairMode, revalidate, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::{KindSolver, SlotRef},
    };
    struct Outcome {
        model: FxHashMap<SlotRef, SlotKind>,
    }
    // Returns (mode_a, lemmas, max_a_prime_menu_len) for `code`. The menu-len witness mirrors
    // `a_prime_menu` at the round-0 all-Ref model: the count of DISTINCT requirers r with r ≠ issuer
    // (the Lemmas disjunction's ACTUAL literal set). NOT raw `requirers.len()` — that counts the
    // issuer as a self-requirer and any duplicate owners, over-reporting arity so the non-vacuity
    // guard could pass on singleton menus (Codex MEDIUM 2026-07-18).
    fn run(code: &str) -> (Outcome, Outcome, usize) {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = collect_program(tcx);
            let slots = CrateSlots::build(&program);
            let max_menu = revalidate(&program, &slots, |_s: SlotRef| true, true)
                .values()
                .flatten()
                .map(|e| {
                    let mut seen = FxHashSet::default();
                    e.requirers
                        .iter()
                        .filter(|r| Some(**r) != e.issuer)
                        .filter(|r| seen.insert(**r))
                        .count()
                })
                .max()
                .unwrap_or(0);
            let solve = |mode: RepairMode| {
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emit");
                for &g in &program.functions {
                    let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                    add_coherence(&solver, &slots, g, &body);
                }
                let (model, stats) = RepairMode::with_override(mode, || {
                    verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true)
                });
                assert_eq!(stats.repair, mode, "mode-stamp (guard 3) must record the active repair");
                Outcome { model: model.expect("fixture must accept under both modes") }
            };
            (solve(RepairMode::ModeA), solve(RepairMode::Lemmas), max_menu)
        })
        .unwrap_or_else(|e| e.raise())
    }
    // Shapes: a single-requirer cascade plus three that produce genuine ≥2-requirer edges (a shared
    // reborrow aliased by several interproc copies, all live at one invalidating write).
    let shapes: [(&str, &str); 4] = [
        (
            "single_req_cascade",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }",
        ),
        (
            "two_requirer",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let base = id(p); let a = id(base); let b = id(base); \
             let w = p; *w = 9; *a + *b }",
        ),
        (
            "three_requirer",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let bb = p; let x = id(p); let z = id(x); let q = id(x); \
             *bb = 5; *x + *z + *q }",
        ),
        (
            "asymmetric",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let a = id(p); let b = id(p); let d = id(b); \
             *a = 1; *b = 2; *d = 3; let w = p; *w = 4; *a + *b + *d }",
        ),
    ];
    let ref_of = |m: &FxHashMap<SlotRef, SlotKind>| -> FxHashSet<SlotRef> {
        m.iter().filter(|(_, k)| **k == SlotKind::Ref).map(|(s, _)| *s).collect()
    };
    let mut max_menu_seen = 0usize;
    for (tag, code) in shapes {
        let (a, l, max_menu) = run(code);
        // EMPIRICAL per-slot relation on these fixtures (per-slot — the granularity Codex demanded;
        // aggregate counts hid the high-arity divergence). Lemmas' Ref-set ⊆ Mode-A's here: the
        // disjunction keeps no MORE Ref than Mode-A's minimal unit commit and CAN keep fewer (the
        // high-arity witness). This inclusion is an OBSERVATION on these fixtures + the pinned seed,
        // NOT a universal law — the loop is non-confluent, so the models are incomparable in general.
        assert!(
            ref_of(&l.model).is_subset(&ref_of(&a.model)),
            "{tag}: on this fixture Lemmas Ref-set should be ⊆ Mode-A's; a Lemmas-only Ref would mean \
             the modes are incomparable here (still not a regression-in-our-favor — see the row doc)"
        );
        // NOTE: no path-cost assertion. `commits`/`rounds` are NOT ordered between the modes in general
        // (non-confluence — Lemmas could converge in fewer or more rounds on a given program); asserting
        // `≥` would be an unsupported dominance claim (Codex). The counts are reported by the sweep.
        max_menu_seen = max_menu_seen.max(max_menu);
    }
    // Non-vacuity: at least one shape must emit a genuine ≥2-literal A′ menu (≥2 DISTINCT requirers
    // ≠ issuer). Without this the equality could hold trivially because every emitted lemma is a
    // singleton ≡ Mode-A, leaving the disjunction path — the whole point of the row — untested.
    assert!(
        max_menu_seen >= 2,
        "non-vacuity: no shape emitted a ≥2-literal A′ menu (max distinct requirers≠issuer = {max_menu_seen}); \
         the disjunction path is untested"
    );
}

/// §NB5-L high-arity regression (Codex HIGH, 2026-07-18). One loan required by a large fan-out of
/// live requirers is the shape whose disjunction could, in the abstract, drive subset oscillation up
/// to ~2^k rounds against the linear cap. This test pins the EMPIRICAL reality under the NB5-Z seed:
/// even a 33-distinct-requirer edge **converges in a handful of rounds under Lemmas and never panics**
/// — the 2^k worst case does not manifest. It is also the **≤-regression witness**: here `Ref(lemmas)`
/// is a STRICT subset of `Ref(mode_a)` (Lemmas loses ≥1 Ref to non-minimal demotion), so the modes do
/// NOT match per-slot. The cap-exhaustion path is a CONTROLLED decline (not a panic) for Lemmas
/// regardless (see `verify_to_fixpoint_counting` + `nb5l_cap_exhaustion_declines_not_panics`), so even
/// if a future solver/seed did oscillate, the outcome is a sound decline, never a crash.
#[test]
fn nb5l_high_arity_lemmas_converges_no_panic() {
    use rustc_hash::{FxHashMap, FxHashSet};

    use crate::analyses::borrow_ownership::{
        CrateCtxt, SlotKind,
        borrow_verify::{RepairMode, revalidate, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::{KindSolver, SlotRef},
    };
    let n = 32usize; // 32 aliases + x ⇒ a 33-distinct-requirer single-loan edge.
    let aliases: String =
        (0..n).map(|i| format!("let a{i} = id(x);")).collect::<Vec<_>>().join(" ");
    let uses: String = (0..n).map(|i| format!("*a{i}")).collect::<Vec<_>>().join(" + ");
    let code = format!(
        "unsafe fn id(p: *mut i32) -> *mut i32 {{ p }} \
         unsafe fn f(p: *mut i32) -> i32 {{ let bb = p; let x = id(p); {aliases} *bb = 5; {uses} + *x }}"
    );
    ::utils::compilation::run_compiler_on_str(&code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        // Confirm the shape actually has the high-arity edge (else the regression is vacuous).
        let max_menu = revalidate(&program, &slots, |_s: SlotRef| true, true)
            .values()
            .flatten()
            .map(|e| e.requirers.iter().filter(|r| Some(**r) != e.issuer).count())
            .max()
            .unwrap_or(0);
        assert!(max_menu >= 16, "regression must build a high-arity edge; got menu {max_menu}");
        let run = |mode: RepairMode| {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, sel) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emit");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            RepairMode::with_override(mode, || {
                verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true)
            })
        };
        let (am, ast) = run(RepairMode::ModeA);
        let (lm, lst) = run(RepairMode::Lemmas);
        // No panic (we reached here). Lemmas converges (accepts) — the 2^k oscillation worst case does
        // NOT fire under the pinned seed.
        let am = am.expect("Mode-A must accept the high-arity fan-out");
        let lm = lm.expect("Lemmas must converge (accept), not oscillate to the cap, on high arity");
        assert!(
            lst.rounds <= ast.rounds + 4,
            "high-arity: Lemmas rounds ({}) must stay near Mode-A ({}) — no subset-oscillation blowup",
            lst.rounds, ast.rounds
        );
        // THE HAZARD WITNESS (Codex HIGH follow-through). ≤ law: Lemmas' Ref-set ⊆ Mode-A's. And here
        // the inclusion is STRICT — Lemmas demotes ≥1 slot Mode-A keeps Ref (non-minimal demotion), so
        // `n_ref(lemmas) < n_ref(mode_a)`. This fixture is the shipped regression witness that the
        // empty-context disjunction is ≤ Mode-A, NOT ≡, and that the loss is real (not just theoretical).
        let ref_of = |m: &FxHashMap<SlotRef, SlotKind>| -> FxHashSet<SlotRef> {
            m.iter().filter(|(_, k)| **k == SlotKind::Ref).map(|(s, _)| *s).collect()
        };
        let (ra, rl) = (ref_of(&am), ref_of(&lm));
        assert!(rl.is_subset(&ra), "high-arity: Lemmas Ref-set must be ⊆ Mode-A's (the ≤ law)");
        assert!(
            rl.len() < ra.len(),
            "high-arity: expected Lemmas to lose ≥1 Ref via non-minimal demotion (the regression \
             witness); Mode-A Ref={}, Lemmas Ref={}",
            ra.len(), rl.len()
        );
    })
    .unwrap_or_else(|e| e.raise())
}

/// §NB5-L (Codex MEDIUM) — the cap backstop is repair-mode-dependent: `Lemmas` returns a CONTROLLED
/// decline tagged `cap_exhausted` (the oscillation blowup does not manifest, but Lemmas has no proven
/// linear bound), while `ModeA` PANICS (its linear bound is proven, so a cap hit is a genuine bug).
/// The natural oscillation never reaches the cap, so this forces it with a test-only cap override.
#[test]
fn nb5l_cap_exhaustion_declines_not_panics() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{RepairMode, verify_to_fixpoint_counting, with_cap_override},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    // An alias cascade that genuinely needs >1 CEGAR round (so cap=1 exhausts).
    let code = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
                unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let solve = |mode: RepairMode, cap: usize| {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, sel) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emit");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            with_cap_override(cap, || {
                RepairMode::with_override(mode, || {
                    verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true)
                })
            })
        };
        // Sanity: the fixture needs >1 round, else cap=1 would not exhaust.
        let (_m, natural) = solve(RepairMode::ModeA, 999);
        assert!(natural.rounds > 1, "fixture must need >1 round (got {})", natural.rounds);
        // Lemmas at cap=1 ⇒ controlled decline, tagged cap_exhausted (NOT a panic, NOT mislabeled).
        let (model, stats) = solve(RepairMode::Lemmas, 1);
        assert!(
            model.is_none() && stats.cap_exhausted,
            "Lemmas cap-exhaustion must be a tagged decline (model={:?}, cap_exhausted={})",
            model.is_some(), stats.cap_exhausted
        );
        // Mode-A at cap=1 ⇒ PANIC (proven linear bound; a hit is a real bug). Drop-guards restore the
        // cap/mode on unwind, so this does not leak state into later tests.
        let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            solve(RepairMode::ModeA, 1)
        }))
        .is_err();
        assert!(panicked, "Mode-A cap-exhaustion must PANIC (its linear bound is proven)");
    })
    .unwrap_or_else(|e| e.raise())
}

/// §NB5-L2 commit-necessity audit — helper: run Mode-A to fixpoint capturing the distinct commit set
/// `C` (dedup by slot, first-seen order) and the accepted model. Panics if the fixture declines.
#[cfg(test)]
fn nb5l2_anchor<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> (
    crate::utils::rustc::RustProgram<'tcx>,
    crate::analyses::borrow_ownership::crate_slots::CrateSlots,
    crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
    rustc_hash::FxHashMap<
        crate::analyses::borrow_ownership::solver::SlotRef,
        crate::analyses::borrow_ownership::SlotKind,
    >,
    Vec<(crate::analyses::borrow_ownership::solver::SlotRef, usize)>,
) {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{self, RepairMode, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    let program = collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let origins = compute_origins(&program);
    let crate_ctxt = CrateCtxt::new(&program);
    let solver = KindSolver::new(&slots);
    let (_s, sel) =
        emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver).expect("emit");
    for &g in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
        add_coherence(&solver, &slots, g, &body);
    }
    let ((model, _stats), events) = RepairMode::with_override(RepairMode::ModeA, || {
        borrow_verify::with_capture(|| {
            verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true)
        })
    });
    let model = model.expect("fixture must accept under Mode-A");
    // FULL-anchor anti-drift: the accepted model must satisfy model_accepts.
    assert!(
        borrow_verify::model_accepts(&program, &slots, &model, true),
        "anchor's accepted model must satisfy model_accepts (drift check)"
    );
    (program, slots, origins, model, events)
}

/// §NB5-L2 — distinct commit set (dedup by slot, first-seen order) from the raw `(slot, round)` events.
#[cfg(test)]
fn nb5l2_distinct(events: &[(crate::analyses::borrow_ownership::solver::SlotRef, usize)])
    -> Vec<crate::analyses::borrow_ownership::solver::SlotRef> {
    let mut seen = rustc_hash::FxHashSet::default();
    events.iter().map(|(s, _)| *s).filter(|s| seen.insert(*s)).collect()
}

/// §NB5-L2 — calibrate the probe's two verdicts deterministically on `single_req_cascade`.
/// NECESSARY arm (singleton probe): probing `[ci]` at index 0 leaves the EMPTY commit set, so the
/// re-solve reproduces the anchor's round-1 (pre-commit) state — which HAD a conflict (Mode-A
/// committed ≥1), so it does NOT accept → NECESSARY. Guaranteed for any `ci`, no `|C|` dependence.
/// OVER-PIN arm (injected): append a surviving-`Ref` slot (∉ `C`) to the FULL commit set and probe it
/// — leaving it out keeps the real `C`, so the re-solve reproduces the anchor's ACCEPTING state with
/// that slot `Ref` → OVER-PIN. Both arms fire; the OverPin assertion cannot pass vacuously.
#[cfg(test)]
#[test]
fn nb5l2_probe_necessary_and_injected_overpin() {
    use crate::analyses::borrow_ownership::SlotKind;
    let code = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
                unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let (program, slots, origins, model, events) = nb5l2_anchor(tcx);
        let commit_set = nb5l2_distinct(&events);
        assert!(!commit_set.is_empty(), "cascade must yield >=1 Mode-A commit");
        // NECESSARY arm: singleton probe of any real commit → empty leave-one-out → conflict returns.
        let singleton = [commit_set[0]];
        assert!(
            matches!(
                run::necessity_probe(&program, &slots, &origins, true, &singleton, 0),
                run::ProbeOutcome::Necessary
            ),
            "singleton probe of a genuine commit must be NECESSARY (∅ leave-one-out re-exposes the \
             round-1 conflict)"
        );
        // OVER-PIN arm: inject a surviving-Ref slot (∉ C) as a spurious commit on the FULL set.
        let injected = model
            .iter()
            .filter(|(_, k)| **k == SlotKind::Ref)
            .map(|(s, _)| *s)
            .find(|s| !commit_set.contains(s))
            .expect("fixture must leave >=1 surviving Ref slot outside C");
        let mut with_spurious = commit_set.clone();
        with_spurious.push(injected);
        let spurious_idx = with_spurious.len() - 1;
        assert!(
            matches!(
                run::necessity_probe(&program, &slots, &origins, true, &with_spurious, spurious_idx),
                run::ProbeOutcome::OverPin
            ),
            "a spurious ¬ref on a surviving Ref slot must probe OVER-PIN (dropping it still accepts, \
             slot Ref)"
        );
    })
    .unwrap_or_else(|e| e.raise())
}

/// §NB5-L2 — the probe finds a GENUINE accumulation over-pin (not just an injected one).
/// `single_req_cascade` drives Mode-A to `|C|=2`: the round-1 commit induces a second, but demoting
/// only the second (keeping the first `Ref`) still accepts — so the first is a real over-pin. This is
/// exactly the L2 headroom the audit measures, and it pins that a natural Mode-A commit set contains
/// over-pins the probe detects. At least one real commit must probe OVER-PIN and at least one NECESSARY
/// (an all-necessary or all-over-pin verdict here would signal the probe collapsed a distinction).
#[cfg(test)]
#[test]
fn nb5l2_probe_finds_natural_accumulation_overpin() {
    let code = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
                unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let (program, slots, origins, _model, events) = nb5l2_anchor(tcx);
        let commit_set = nb5l2_distinct(&events);
        assert!(commit_set.len() >= 2, "cascade must yield >=2 commits (got {})", commit_set.len());
        let (mut overpins, mut necessary) = (0usize, 0usize);
        for i in 0..commit_set.len() {
            match run::necessity_probe(&program, &slots, &origins, true, &commit_set, i) {
                run::ProbeOutcome::OverPin => overpins += 1,
                run::ProbeOutcome::Necessary => necessary += 1,
            }
        }
        assert!(
            overpins >= 1,
            "the cascade must contain >=1 natural accumulation over-pin (found {overpins})"
        );
        assert!(
            necessary >= 1,
            "the cascade must retain >=1 necessary commit (found {necessary}) — else the probe \
             collapsed the distinction"
        );
    })
    .unwrap_or_else(|e| e.raise())
}

/// §NB5-L2 — the witnessed-joint greedy set is a CERTIFIED lower bound: `na_joint_witnessed=true`
/// (one solve with only the retained set demoted leaves EVERY removed slot `Ref` and accepts), and the
/// count is bounded by `|C|`. The certificate — NOT any relation to the independent count — is the
/// soundness property: whatever set the greedy commits to, the witness proves it is jointly recoverable.
///
/// Greedy and independent are INCOMPARABLE (do not assert `joint ≤ indep`): independent demotes ALL
/// other commits at once, so it MISSES a slot recoverable only while other removed slots stay `Ref`
/// (e.g. coherence-equated slots — demoting the partner forces the slot `¬ref`, but keeping it `Ref`
/// does not). The greedy, un-demoting removals as it goes, captures those JOINT recoveries — so
/// `joint > indep` occurs at corpus scale (libtree: indep 3, witnessed-joint 7, all certified). It can
/// also be `<` if the greedy order spends a removal that blocks two others. The witness is what makes
/// the count sound regardless of direction; the independent count is a labeled diagnostic only.
#[cfg(test)]
#[test]
fn nb5l2_greedy_witnessed_joint_certified() {
    let fixtures: [(&str, &str); 3] = [
        (
            "single_req_cascade",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }",
        ),
        (
            "two_requirer",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let base = id(p); let a = id(base); let b = id(base); \
             let w = p; *w = 9; *a + *b }",
        ),
        (
            "asymmetric",
            "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
             unsafe fn f(p: *mut i32) -> i32 { let a = id(p); let b = id(p); let d = id(b); \
             *a = 1; *b = 2; *d = 3; let w = p; *w = 4; *a + *b + *d }",
        ),
    ];
    for (tag, code) in fixtures {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let (program, slots, origins, model, events) = nb5l2_anchor(tcx);
            let mut row = report::Row::default();
            run::run_necessity_audit(&program, &slots, &origins, true, &Some(model), &events, &mut row);
            let get = |k: &str| {
                row.get(k).unwrap_or_else(|| panic!("{tag}: audit did not emit {k}")).to_string()
            };
            assert_eq!(get("na_status"), "ok", "{tag}: audit status");
            // The CERTIFICATE: the greedy removed set is jointly realizable (all removed Ref + accept).
            assert_eq!(
                get("na_joint_witnessed"),
                "true",
                "{tag}: the greedy removed set must be jointly witnessed (all removed Ref + accept)"
            );
            let joint: usize = get("na_overpins").parse().unwrap();
            let total: usize = get("na_commits_total").parse().unwrap();
            assert!(joint <= total, "{tag}: witnessed-joint ({joint}) must be <= |C| ({total})");
            // Both counts are emitted (rider 5) — the independent as a labeled diagnostic.
            assert!(row.get("na_indep_overpins").is_some(), "{tag}: independent count must be emitted");
        })
        .unwrap_or_else(|e| e.raise())
    }
}

/// §NB5-L2 (Codex F3) — the audit capture is Mode-A-ONLY: under `CRAT_BO_REPAIR=lemmas` the CEGAR loop
/// takes the `Lemmas` branch, which does NOT record commit events, so `with_capture` returns empty. The
/// `run_bo` guard rests on this — it refuses `repair != ModeA` with `na_status=wrong-repair-mode` rather
/// than publishing a plausible-but-meaningless zero audit. Mode-A on the same fixture DOES capture.
#[cfg(test)]
#[test]
fn nb5l2_capture_is_mode_a_only() {
    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{self, RepairMode, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        origins::compute_origins,
        solver::KindSolver,
    };
    let code = "unsafe fn id(p: *mut i32) -> *mut i32 { p } \
                unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }";
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let run_mode = |mode: RepairMode| {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_s, sel) =
                emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver).expect("emit");
            for &g in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                add_coherence(&solver, &slots, g, &body);
            }
            let ((_model, stats), events) = RepairMode::with_override(mode, || {
                borrow_verify::with_capture(|| {
                    verify_to_fixpoint_counting(&program, &slots, &solver, &sel, true)
                })
            });
            (stats.repair, events)
        };
        let (mode_a_repair, mode_a_events) = run_mode(RepairMode::ModeA);
        assert_eq!(mode_a_repair, RepairMode::ModeA, "Mode-A run must stamp ModeA");
        assert!(!mode_a_events.is_empty(), "Mode-A must capture commits on a conflict fixture");
        let (lemmas_repair, lemmas_events) = run_mode(RepairMode::Lemmas);
        assert_eq!(lemmas_repair, RepairMode::Lemmas, "Lemmas run must stamp Lemmas");
        assert!(
            lemmas_events.is_empty(),
            "Lemmas must capture NO commit events — the audit is Mode-A-only (got {} events)",
            lemmas_events.len()
        );
    })
    .unwrap_or_else(|e| e.raise())
}

// ---------------------------------------------------------------------------
// §L2 RED — feature-off base golden captured at ae6f334.
// ---------------------------------------------------------------------------

const L2_FEATURE_OFF_BASE_SHA: &str = "ae6f334eca78cbaa254bfb3afc65e3c31130153d";
const L2_FEATURE_OFF_OUTPUT_LEN: usize = 212;
const L2_FEATURE_OFF_OUTPUT_SHA256: &str =
    "7e625bb8120839583f7cf64d19c6b87a342d2525bca5bf36dfc115e4a003a17a";
const L2_FEATURE_OFF_SOURCE_DROP: &str =
    include_str!("analyses/borrow_ownership/testdata/l2_feature_off_source_drop.rs");
const L2_FEATURE_OFF_SINK_DROP: &str =
    include_str!("analyses/borrow_ownership/testdata/l2_feature_off_sink_drop.rs");

fn l2_feature_off_capture_program(fixture: &str, source: &str) -> String {
    use std::fmt::Write;

    use crate::analyses::borrow_ownership::{
        CrateCtxt,
        borrow_verify::{RepairMode, model_accepts, verify_to_fixpoint_counting},
        coherence::add_coherence,
        crate_slots::CrateSlots,
        emit_crate_ownership_constraints,
        mutability_facts::MutFacts,
        origins::compute_origins,
        solver::KindSolver,
    };

    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let program = collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mut rendered = String::new();

        for (mutability, mut_facts) in [
            ("from_program", MutFacts::from_program(&program)),
            ("all_mut", MutFacts::all_mut()),
        ] {
            let crate_ctxt = CrateCtxt::new(&program);
            let solver = KindSolver::new(&slots);
            let (_emission, selectors) =
                emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                    .expect("L2 feature-off golden emission");
            for &fn_did in &program.functions {
                let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
                add_coherence(&solver, &slots, fn_did, &body);
            }

            let (model, stats) = RepairMode::with_override(RepairMode::ModeA, || {
                verify_to_fixpoint_counting(
                    &program,
                    &slots,
                    &solver,
                    &selectors,
                    &mut_facts,
                )
            });
            let model = model.unwrap_or_else(|| {
                panic!("{fixture}/{mutability}: base Mode-A must accept")
            });
            let accepted = model_accepts(&program, &slots, &model, &mut_facts);
            assert!(
                accepted,
                "{fixture}/{mutability}: accepted model must satisfy model_accepts"
            );

            let (reported_model, dropped) = solver
                .model_kinds_relaxing_reporting(&selectors)
                .unwrap_or_else(|| {
                    panic!("{fixture}/{mutability}: reporting solve must remain SAT")
                });
            assert_eq!(
                reported_model, model,
                "{fixture}/{mutability}: reporting solve must reproduce the accepted model"
            );

            let dropped_selectors = l2_feature_off_dropped_selectors(&selectors, &dropped);
            assert_eq!(
                stats.dropped_sources,
                dropped_selectors
                    .iter()
                    .filter(|selector| selector.starts_with("source:"))
                    .count(),
                "{fixture}/{mutability}: source-drop counter/reporting mismatch"
            );
            assert_eq!(
                stats.dropped_sinks,
                dropped_selectors
                    .iter()
                    .filter(|selector| selector.starts_with("sink:"))
                    .count(),
                "{fixture}/{mutability}: sink-drop counter/reporting mismatch"
            );

            let mut kinds: Vec<(String, _)> = model
                .iter()
                .map(|(&slot, &kind)| (run::fmt_slot(&program, &slots, slot), kind))
                .collect();
            kinds.sort_by(|(left, _), (right, _)| left.cmp(right));

            writeln!(rendered, "case={fixture}/{mutability}").unwrap();
            writeln!(rendered, "accepted={accepted}").unwrap();
            writeln!(rendered, "stats.repair={}", stats.repair.label()).unwrap();
            writeln!(rendered, "stats.rounds={}", stats.rounds).unwrap();
            writeln!(
                rendered,
                "stats.commits_conflict={}",
                stats.commits_conflict
            )
            .unwrap();
            writeln!(
                rendered,
                "stats.commits_per_round={:?}",
                stats.commits_per_round
            )
            .unwrap();
            writeln!(
                rendered,
                "stats.dropped_sources={}",
                stats.dropped_sources
            )
            .unwrap();
            writeln!(rendered, "stats.dropped_sinks={}", stats.dropped_sinks).unwrap();
            let field_decline = stats
                .field_conflict_decline
                .map(|slot| run::fmt_slot(&program, &slots, slot))
                .unwrap_or_else(|| "-".to_string());
            writeln!(
                rendered,
                "stats.field_conflict_decline={field_decline}"
            )
            .unwrap();
            writeln!(rendered, "stats.cap_exhausted={}", stats.cap_exhausted).unwrap();
            writeln!(
                rendered,
                "dropped_selectors={}",
                if dropped_selectors.is_empty() {
                    "-".to_string()
                } else {
                    dropped_selectors.join(",")
                }
            )
            .unwrap();
            for (slot, kind) in kinds {
                writeln!(rendered, "model.{slot}={kind:?}").unwrap();
            }
            writeln!(rendered, "end_case").unwrap();
        }

        rendered
    })
    .unwrap_or_else(|error| error.raise())
}

fn l2_feature_off_dropped_selectors(
    selectors: &crate::analyses::borrow_ownership::solver::Selectors,
    dropped: &[z3::ast::Bool],
) -> Vec<String> {
    let mut names = Vec::new();
    for literal in dropped {
        if let Some(index) = selectors
            .sources()
            .iter()
            .position(|selector| selector == literal)
        {
            names.push(format!("source:{index}"));
        } else if let Some(index) = selectors
            .sinks()
            .iter()
            .position(|selector| selector == literal)
        {
            names.push(format!("sink:{index}"));
        } else {
            panic!("L2 feature-off reporting solve returned an unknown selector");
        }
    }
    names.sort();
    names
}

fn l2_feature_off_capture() -> (String, String, crate::BytemuckDependency) {
    use std::{fmt::Write, process::Command};

    let rustc = Command::new("rustc")
        .arg("--version")
        .output()
        .expect("query rustc version for L2 base golden");
    assert!(rustc.status.success(), "rustc --version must succeed");
    let rustc = String::from_utf8(rustc.stdout)
        .expect("rustc version must be UTF-8")
        .trim()
        .to_string();

    let mut snapshot = String::new();
    writeln!(snapshot, "base.sha={L2_FEATURE_OFF_BASE_SHA}").unwrap();
    writeln!(snapshot, "toolchain.rustc={rustc}").unwrap();
    writeln!(snapshot, "z3.full_version={}", z3::full_version()).unwrap();
    writeln!(snapshot, "z3.smt.random_seed=0").unwrap();
    writeln!(snapshot, "z3.sat.random_seed=0").unwrap();
    snapshot.push_str(&l2_feature_off_capture_program(
        "source_drop",
        L2_FEATURE_OFF_SOURCE_DROP,
    ));
    snapshot.push_str(&l2_feature_off_capture_program(
        "sink_drop",
        L2_FEATURE_OFF_SINK_DROP,
    ));
    let (output, bytemuck) = ::utils::compilation::run_compiler_on_str(
        L2_FEATURE_OFF_SOURCE_DROP,
        |tcx| crate::replace_local_borrows(&crate::Config::default(), tcx),
    )
    .unwrap_or_else(|error| error.raise());
    writeln!(snapshot, "rewrite.source_drop.bytemuck={bytemuck:?}").unwrap();
    (snapshot, output, bytemuck)
}

fn l2_decode_hex(encoded: &str) -> Vec<u8> {
    fn nibble(byte: u8) -> u8 {
        match byte {
            b'0'..=b'9' => byte - b'0',
            b'a'..=b'f' => byte - b'a' + 10,
            b'A'..=b'F' => byte - b'A' + 10,
            _ => panic!("L2 feature-off golden contains non-hex byte {byte:?}"),
        }
    }

    let digits: Vec<u8> = encoded
        .bytes()
        .filter(|byte| !byte.is_ascii_whitespace())
        .collect();
    assert_eq!(
        digits.len() % 2,
        0,
        "L2 feature-off golden contains an odd number of hex digits"
    );
    digits
        .chunks_exact(2)
        .map(|pair| (nibble(pair[0]) << 4) | nibble(pair[1]))
        .collect()
}

fn l2_sha256_hex(input: &[u8]) -> String {
    const ROUND: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
        0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
        0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
        0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
        0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let mut state = [
        0x6a09e667u32,
        0xbb67ae85,
        0x3c6ef372,
        0xa54ff53a,
        0x510e527f,
        0x9b05688c,
        0x1f83d9ab,
        0x5be0cd19,
    ];
    let bit_len = u64::try_from(input.len())
        .expect("L2 feature-off golden length fits u64")
        .checked_mul(8)
        .expect("L2 feature-off golden bit length fits u64");
    let mut padded = input.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());

    for block in padded.chunks_exact(64) {
        let mut words = [0u32; 64];
        for (word, bytes) in words[..16].iter_mut().zip(block.chunks_exact(4)) {
            *word = u32::from_be_bytes(bytes.try_into().expect("four-byte SHA-256 word"));
        }
        for index in 16..64 {
            let s0 = words[index - 15].rotate_right(7)
                ^ words[index - 15].rotate_right(18)
                ^ (words[index - 15] >> 3);
            let s1 = words[index - 2].rotate_right(17)
                ^ words[index - 2].rotate_right(19)
                ^ (words[index - 2] >> 10);
            words[index] = words[index - 16]
                .wrapping_add(s0)
                .wrapping_add(words[index - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for index in 0..64 {
            let sum1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choose = (e & f) ^ (!e & g);
            let temp1 = h
                .wrapping_add(sum1)
                .wrapping_add(choose)
                .wrapping_add(ROUND[index])
                .wrapping_add(words[index]);
            let sum0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = sum0.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        for (slot, value) in state
            .iter_mut()
            .zip([a, b, c, d, e, f, g, h])
        {
            *slot = slot.wrapping_add(value);
        }
    }

    state
        .iter()
        .map(|word| format!("{word:08x}"))
        .collect()
}

#[test]
fn l2_red_feature_off_matches_base_ae6f334() {
    let explicit_off = match std::env::var("CRAT_BO_L2_GUARDED_COMMITS") {
        Ok(value) => {
            assert_eq!(
                value, "0",
                "the feature-off base-golden test requires CRAT_BO_L2_GUARDED_COMMITS=0"
            );
            true
        }
        Err(std::env::VarError::NotPresent) => false,
        Err(error) => panic!("CRAT_BO_L2_GUARDED_COMMITS is not valid Unicode: {error}"),
    };
    assert!(
        !crate::analyses::borrow_ownership::l2::enabled_from_env(),
        "CRAT_BO_L2_GUARDED_COMMITS=0 must resolve feature-off"
    );
    // The exact RED evidence command sets the feature flag explicitly and filters
    // this test into a fresh, single-threaded process. Pin both seeds before its
    // first z3 operation, matching the official Mode-A worker contract. An
    // ordinary full-suite run leaves the flag absent and retains z3's defaults,
    // avoiding a process-global write in the parallel runner.
    if explicit_off {
        z3::set_global_param("smt.random_seed", "0");
        z3::set_global_param("sat.random_seed", "0");
    }

    let (actual_snapshot, actual_output, actual_bytemuck) = l2_feature_off_capture();
    assert_eq!(
        actual_snapshot,
        include_str!("analyses/borrow_ownership/testdata/l2_feature_off_base_ae6f334.snap"),
        "feature-off Mode-A semantics drifted from the approved ae6f334 base"
    );
    assert_eq!(
        actual_bytemuck,
        crate::BytemuckDependency::None,
        "source-drop BytemuckDependency drifted from the approved ae6f334 base"
    );
    // Storage-encoding contract: the authoritative 212-byte capture is hex so
    // editors, Git, and CI cannot normalize its terminal byte. Never normalize
    // either side or replace this with raw-text include_bytes!: both alternatives
    // weaken the exact base anchor.
    let golden_output = l2_decode_hex(include_str!(
        "analyses/borrow_ownership/testdata/l2_feature_off_base_ae6f334.output.hex"
    ));
    assert_eq!(
        l2_sha256_hex(b""),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "L2 feature-off SHA-256 helper failed its standard empty-input vector"
    );
    assert_eq!(
        golden_output.len(),
        L2_FEATURE_OFF_OUTPUT_LEN,
        "encoded feature-off golden no longer decodes to the authoritative capture length"
    );
    assert_eq!(
        l2_sha256_hex(&golden_output),
        L2_FEATURE_OFF_OUTPUT_SHA256,
        "encoded feature-off golden no longer matches the captured artifact's SHA-256"
    );
    assert_eq!(
        actual_output.as_bytes(),
        golden_output,
        "feature-off generated output is not byte-identical to the approved ae6f334 base"
    );
}
