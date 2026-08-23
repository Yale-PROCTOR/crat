//! A12 retention funnel: test-only, measurement-only S0 -> S4 accounting.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    time::{Duration, Instant},
};

use rustc_hash::FxHashSet;
use rustc_middle::ty::TyCtxt;
use z3::{SatResult, ast::Bool};

use super::{CORE_LABEL_FAMILIES, CORPUS, collect_program, orchestrate, provenance, report::Row};
use crate::analyses::borrow_ownership::{
    SafeMonoMode, SlotKind,
    borrow_verify::RepairMode,
    coherence::{constrain_field_ownership, selected_copy_lend_sites},
    construction::{
        CopyLendMode, CopyLendPairCandidate, analyze_copy_lend_candidates, construct_bo_into,
        verify_bo_construction_counting,
    },
    crate_slots::CrateSlots,
    l2::slotref_diagnostic,
    mutability_facts::{MutFacts, MutFactsMode},
    origins::compute_origins,
    solver::{CoreTracker, KindSolver, SlotRef},
};

const CORPUS_DIGEST: &str = "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";
const SAMPLE_K: usize = 8;
const QUERY_TIMEOUT: Duration = Duration::from_secs(600);

fn program_bound_seconds(pairs: usize) -> u64 {
    14_400u64.max(
        u64::try_from(pairs)
            .expect("funnel pair count fits u64")
            .saturating_mul(300),
    )
}

fn sample_loss_indices(losses: &[usize]) -> Vec<usize> {
    losses.iter().copied().take(SAMPLE_K).collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum QueryVerdict {
    Sat,
    Unsat,
    Unknown,
}

impl QueryVerdict {
    fn label(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
            Self::Unknown => "unknown",
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct StageBits {
    s0: bool,
    s1: bool,
    s2: bool,
    s3: bool,
    s4: bool,
    initial_selected: bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct StageCounts {
    s0: usize,
    s1: usize,
    s2: usize,
    s3: usize,
    s4: usize,
    initial_selected: usize,
    pre_replay_not_selected: usize,
    replay_lost: usize,
}

fn summarize(rows: &[StageBits]) -> StageCounts {
    for row in rows {
        assert!(!row.s1 || row.s0, "S1 must be a subset of S0: {row:?}");
        assert!(!row.s2 || row.s1, "S2 must be a subset of S1: {row:?}");
        assert!(!row.s3 || row.s2, "S3 must be a subset of S2: {row:?}");
        assert!(!row.s4 || row.s3, "S4 must be a subset of S3: {row:?}");
        assert!(
            !row.initial_selected || row.s3,
            "an initially selected pair must be lend-SAT: {row:?}"
        );
        assert!(
            !row.s4 || row.initial_selected,
            "the preregistered S3->S4 partition requires final selection to have been initial"
        );
    }
    let s0 = rows.iter().filter(|row| row.s0).count();
    let s1 = rows.iter().filter(|row| row.s1).count();
    let s2 = rows.iter().filter(|row| row.s2).count();
    let s3 = rows.iter().filter(|row| row.s3).count();
    let s4 = rows.iter().filter(|row| row.s4).count();
    let initial_selected = rows.iter().filter(|row| row.initial_selected).count();
    StageCounts {
        s0,
        s1,
        s2,
        s3,
        s4,
        initial_selected,
        pre_replay_not_selected: s3 - initial_selected,
        replay_lost: initial_selected - s4,
    }
}

fn seeded_family_order() -> Vec<&'static str> {
    let mut seen = BTreeSet::new();
    let mut answer = Vec::new();
    for family in ["kind-equate", "own-linear"]
        .into_iter()
        .chain(CORE_LABEL_FAMILIES.iter().copied())
    {
        if seen.insert(family) {
            answer.push(family);
        }
    }
    answer
}

fn sort_families(families: &mut Vec<String>) {
    let order = seeded_family_order();
    families.sort_by_key(|family| {
        order
            .iter()
            .position(|candidate| *candidate == family)
            .unwrap_or(usize::MAX)
    });
    families.dedup();
}

fn hard_query(
    solver: &KindSolver,
    tracker: &CoreTracker,
    tracks: &[Bool],
    force: Bool,
) -> (QueryVerdict, Vec<String>) {
    let mut assumptions = tracks.to_vec();
    assumptions.push(force.clone());
    match solver.check_with_assumptions(&assumptions) {
        SatResult::Sat => (QueryVerdict::Sat, Vec::new()),
        SatResult::Unknown => (QueryVerdict::Unknown, Vec::new()),
        SatResult::Unsat => {
            let mut families = Vec::new();
            for literal in solver.optimize().get_unsat_core() {
                if literal == force {
                    continue;
                }
                let label = tracker
                    .label_of(&literal)
                    .unwrap_or_else(|| panic!("unrecognized funnel core literal: {literal}"));
                let family = label
                    .strip_prefix("family-marker::")
                    .unwrap_or_else(|| panic!("non-family funnel track label: {label}"));
                families.push(family.to_owned());
            }
            sort_families(&mut families);
            assert!(
                !families.is_empty(),
                "UNSAT funnel query must name at least one hard family"
            );
            (QueryVerdict::Unsat, families)
        }
    }
}

fn untracked_query(solver: &KindSolver, force: Bool) -> QueryVerdict {
    match solver.check_with_assumptions(&[force]) {
        SatResult::Sat => QueryVerdict::Sat,
        SatResult::Unsat => QueryVerdict::Unsat,
        SatResult::Unknown => QueryVerdict::Unknown,
    }
}

fn kind_label(kind: Option<&SlotKind>) -> &'static str {
    match kind {
        Some(SlotKind::Raw) => "raw",
        Some(SlotKind::Ref) => "ref",
        Some(SlotKind::Owning) => "owning",
        None => "missing",
    }
}

fn join_families(families: &[String]) -> String {
    if families.is_empty() {
        "none".to_owned()
    } else {
        families.join(",")
    }
}

fn clean_cell(value: &str) -> String {
    value.replace(['\t', '\n', '\r'], "_")
}

struct Measurement {
    bits: Vec<StageBits>,
    ledger: String,
    s0_sites: usize,
    s1_sites: usize,
    s2_unknown: usize,
    s3_unknown: usize,
    s2_sampled_losses: usize,
    s3_sampled_losses: usize,
    sampled_core_unknown: usize,
    tracked_checks: usize,
    final_selected_sites: usize,
}

struct PairStage {
    candidate: CopyLendPairCandidate,
    s2: QueryVerdict,
    s3: Option<QueryVerdict>,
    s2_core: Vec<String>,
    s3_core: Vec<String>,
    s2_core_scope: &'static str,
    s3_core_scope: &'static str,
    s2_core_status: &'static str,
    s3_core_status: &'static str,
}

fn measure_program(tcx: TyCtxt<'_>, program_name: &str) -> Measurement {
    assert_eq!(CopyLendMode::current(), CopyLendMode::LendArm);
    assert_eq!(RepairMode::current(), RepairMode::ModeA);
    assert_eq!(MutFactsMode::current(), MutFactsMode::On);
    assert_eq!(SafeMonoMode::current(), SafeMonoMode::PerSite);
    assert!(
        !crate::analyses::borrow_ownership::l2::enabled_from_env(),
        "A12 funnel requires L2 off"
    );

    let program = collect_program(tcx);
    let origins = compute_origins(&program);
    let slots = CrateSlots::build(&program);
    let mut_facts = MutFacts::from_program(&program);
    let candidates =
        analyze_copy_lend_candidates(&program, &slots, &mut_facts, origins.native_flows());
    let s0_sites = candidates
        .iter()
        .map(|candidate| candidate.sites.len())
        .sum::<usize>();

    let stage_solver = KindSolver::new_hard_only(&slots);
    stage_solver.set_random_seed(0);
    stage_solver.set_query_timeout(QUERY_TIMEOUT);
    let stage_construction = construct_bo_into(
        &program,
        &slots,
        &origins,
        &mut_facts,
        &stage_solver,
        CopyLendMode::LendArm,
    )
    .expect("A12 funnel hard-only construction");
    constrain_field_ownership(&stage_solver, &slots, &program);

    let candidate_eligible = candidates
        .iter()
        .filter(|candidate| candidate.drop.is_none())
        .map(|candidate| candidate.pair)
        .collect::<FxHashSet<_>>();
    assert_eq!(
        candidate_eligible, stage_construction.eligibility.pairs,
        "funnel classifier and production eligibility diverged"
    );

    let mut stages = candidates
        .into_iter()
        .map(|candidate| {
            let s2 = if candidate.drop.is_none() {
                untracked_query(
                    &stage_solver,
                    stage_solver.owning_literal(candidate.pair.rhs),
                )
            } else {
                QueryVerdict::Unsat
            };
            let s3 = if s2 == QueryVerdict::Sat {
                Some(untracked_query(
                    &stage_solver,
                    stage_solver.lend_guard(candidate.pair.lhs, candidate.pair.rhs),
                ))
            } else {
                None
            };
            PairStage {
                candidate,
                s2,
                s3,
                s2_core: Vec::new(),
                s3_core: Vec::new(),
                s2_core_scope: "na",
                s3_core_scope: "na",
                s2_core_status: "na",
                s3_core_status: "na",
            }
        })
        .collect::<Vec<_>>();

    let s2_losses = stages
        .iter()
        .enumerate()
        .filter_map(|(index, stage)| {
            (stage.candidate.drop.is_none() && stage.s2 == QueryVerdict::Unsat).then_some(index)
        })
        .collect::<Vec<_>>();
    let s3_losses = stages
        .iter()
        .enumerate()
        .filter_map(|(index, stage)| {
            (stage.s2 == QueryVerdict::Sat && stage.s3 == Some(QueryVerdict::Unsat))
                .then_some(index)
        })
        .collect::<Vec<_>>();
    let s2_sample = sample_loss_indices(&s2_losses);
    let s3_sample = sample_loss_indices(&s3_losses);
    let mut sampled_core_unknown = 0usize;
    let tracked_checks = if s2_sample.is_empty() && s3_sample.is_empty() {
        0
    } else {
        let tracked = KindSolver::new_family_tracked_hard_only(&slots);
        tracked.set_random_seed(0);
        tracked.set_query_timeout(QUERY_TIMEOUT);
        let tracked_construction = construct_bo_into(
            &program,
            &slots,
            &origins,
            &mut_facts,
            &tracked,
            CopyLendMode::LendArm,
        )
        .expect("A12 funnel sampled family construction");
        assert_eq!(
            tracked_construction.eligibility.pairs, stage_construction.eligibility.pairs,
            "sampled family construction eligibility diverged"
        );
        let tracker = tracked.tracker().expect("A12 funnel family tracker");
        tracker.set_context("field-law");
        constrain_field_ownership(&tracked, &slots, &program);
        let tracks = tracker.tracks();
        let s2_scope = if s2_losses.len() <= SAMPLE_K {
            "exhaustive"
        } else {
            "sampled"
        };
        let s3_scope = if s3_losses.len() <= SAMPLE_K {
            "exhaustive"
        } else {
            "sampled"
        };
        for index in s2_sample.iter().copied() {
            let pair = stages[index].candidate.pair;
            let (verdict, families) =
                hard_query(&tracked, tracker, &tracks, tracked.owning_literal(pair.rhs));
            assert_ne!(verdict, QueryVerdict::Sat, "sampled S2 loss became SAT");
            sampled_core_unknown += usize::from(verdict == QueryVerdict::Unknown);
            stages[index].s2_core = families;
            stages[index].s2_core_scope = s2_scope;
            stages[index].s2_core_status = verdict.label();
        }
        for index in s3_sample.iter().copied() {
            let pair = stages[index].candidate.pair;
            let (verdict, families) = hard_query(
                &tracked,
                tracker,
                &tracks,
                tracked.lend_guard(pair.lhs, pair.rhs),
            );
            assert_ne!(verdict, QueryVerdict::Sat, "sampled S3 loss became SAT");
            sampled_core_unknown += usize::from(verdict == QueryVerdict::Unknown);
            stages[index].s3_core = families;
            stages[index].s3_core_scope = s3_scope;
            stages[index].s3_core_status = verdict.label();
        }
        tracked.check_sat_count()
    };
    let s2_sample_set = s2_sample.into_iter().collect::<BTreeSet<_>>();
    let s3_sample_set = s3_sample.into_iter().collect::<BTreeSet<_>>();
    for index in s2_losses.iter().copied() {
        if !s2_sample_set.contains(&index) {
            stages[index].s2_core_scope = "unsampled";
            stages[index].s2_core_status = "unsampled";
        }
    }
    for index in s3_losses.iter().copied() {
        if !s3_sample_set.contains(&index) {
            stages[index].s3_core_scope = "unsampled";
            stages[index].s3_core_status = "unsampled";
        }
    }

    let initial_solver = KindSolver::new(&slots);
    initial_solver.set_random_seed(0);
    initial_solver.set_query_timeout(QUERY_TIMEOUT);
    let initial_construction = construct_bo_into(
        &program,
        &slots,
        &origins,
        &mut_facts,
        &initial_solver,
        CopyLendMode::LendArm,
    )
    .expect("A12 funnel initial construction");
    constrain_field_ownership(&initial_solver, &slots, &program);
    let initial_model = initial_solver
        .model_kinds_relaxing(&initial_construction.selectors)
        .expect("A12 funnel initial optimized model");

    let final_solver = KindSolver::new(&slots);
    final_solver.set_random_seed(0);
    final_solver.set_query_timeout(QUERY_TIMEOUT);
    let final_construction = construct_bo_into(
        &program,
        &slots,
        &origins,
        &mut_facts,
        &final_solver,
        CopyLendMode::LendArm,
    )
    .expect("A12 funnel final construction");
    let (final_model, _stats) = verify_bo_construction_counting(
        &program,
        &slots,
        &origins,
        &final_solver,
        &final_construction,
        &mut_facts,
    );
    let final_model = final_model.expect("A12 funnel production model declined");
    let final_selected_sites = selected_copy_lend_sites(
        &program,
        &slots,
        &final_construction.eligibility.pairs,
        &final_model,
    )
    .values()
    .map(FxHashSet::len)
    .sum::<usize>();

    let mut ledger = String::from(
        "program\tfunction\tlhs\trhs\tsite_count\tsites\ts0\ts1\ts2\ts3\ts4\t\
         s0_s1_reason\ts2_query\ts3_query\ts2_core_families\ts3_core_families\t\
         s2_core_scope\ts3_core_scope\ts2_core_status\ts3_core_status\tinitial_lhs_kind\t\
         initial_rhs_kind\tinitial_selected\tfinal_lhs_kind\tfinal_rhs_kind\t\
         final_selected\ts3_s4_reason\tcopy_lend_mode\tsmt_seed\tsat_seed\n",
    );
    let mut bits = Vec::with_capacity(stages.len());
    let mut s2_unknown = 0usize;
    let mut s3_unknown = 0usize;
    for PairStage {
        candidate: CopyLendPairCandidate { pair, sites, drop },
        s2: s2_verdict,
        s3: s3_verdict,
        s2_core,
        s3_core,
        s2_core_scope,
        s3_core_scope,
        s2_core_status,
        s3_core_status,
    } in stages
    {
        let s1 = drop.is_none();
        let s2 = s1 && s2_verdict == QueryVerdict::Sat;
        let s3 = s2 && s3_verdict == Some(QueryVerdict::Sat);
        s2_unknown += usize::from(s1 && s2_verdict == QueryVerdict::Unknown);
        s3_unknown += usize::from(s2 && s3_verdict == Some(QueryVerdict::Unknown));
        let initial_lhs = initial_model.get(&pair.lhs);
        let initial_rhs = initial_model.get(&pair.rhs);
        let initial_selected =
            s3 && initial_lhs == Some(&SlotKind::Ref) && initial_rhs == Some(&SlotKind::Owning);
        let final_lhs = final_model.get(&pair.lhs);
        let final_rhs = final_model.get(&pair.rhs);
        let s4 = s3 && final_lhs == Some(&SlotKind::Ref) && final_rhs == Some(&SlotKind::Owning);
        let stage = StageBits {
            s0: true,
            s1,
            s2,
            s3,
            s4,
            initial_selected,
        };
        // Enforce each row's nesting immediately; the aggregate checks again.
        let _ = summarize(&[stage]);
        let s3_s4_reason = if !s3 || s4 {
            "none".to_owned()
        } else if initial_selected {
            "replay-repair-lost".to_owned()
        } else {
            format!(
                "optimized-equal-arm-{}-{}",
                kind_label(initial_lhs),
                kind_label(initial_rhs)
            )
        };
        let fn_did = match pair.lhs {
            SlotRef::Local(fn_did, _) => fn_did,
            SlotRef::Field(_) => unreachable!("S0 contains local endpoints only"),
        };
        let locations = sites
            .iter()
            .map(|site| format!("{}:{}", site.location.block, site.location.statement_index))
            .collect::<Vec<_>>()
            .join(",");
        let cells = vec![
            clean_cell(program_name),
            clean_cell(&tcx.def_path_str(fn_did.to_def_id())),
            slotref_diagnostic(pair.lhs),
            slotref_diagnostic(pair.rhs),
            sites.len().to_string(),
            locations,
            "1".to_owned(),
            usize::from(s1).to_string(),
            usize::from(s2).to_string(),
            usize::from(s3).to_string(),
            usize::from(s4).to_string(),
            drop.map_or("eligible", |reason| reason.label()).to_owned(),
            if s1 { s2_verdict.label() } else { "na" }.to_owned(),
            s3_verdict.map_or("na", QueryVerdict::label).to_owned(),
            if s1 && s2_verdict == QueryVerdict::Unsat {
                join_families(&s2_core)
            } else {
                "na".to_owned()
            },
            if s3_verdict == Some(QueryVerdict::Unsat) {
                join_families(&s3_core)
            } else {
                "na".to_owned()
            },
            s2_core_scope.to_owned(),
            s3_core_scope.to_owned(),
            s2_core_status.to_owned(),
            s3_core_status.to_owned(),
            kind_label(initial_lhs).to_owned(),
            kind_label(initial_rhs).to_owned(),
            usize::from(initial_selected).to_string(),
            kind_label(final_lhs).to_owned(),
            kind_label(final_rhs).to_owned(),
            usize::from(s4).to_string(),
            s3_s4_reason,
            "lend_arm".to_owned(),
            "0".to_owned(),
            "0".to_owned(),
        ];
        assert_eq!(cells.len(), 30, "A12 funnel ledger schema drifted");
        ledger.push_str(&cells.join("\t"));
        ledger.push('\n');
        bits.push(stage);
    }

    Measurement {
        s1_sites: final_construction.eligibility.sites.len(),
        s2_unknown,
        s3_unknown,
        s2_sampled_losses: s2_sample_set.len(),
        s3_sampled_losses: s3_sample_set.len(),
        sampled_core_unknown,
        tracked_checks,
        bits,
        ledger,
        s0_sites,
        final_selected_sites,
    }
}

pub(crate) fn run_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
    let t0 = Instant::now();
    let program_name =
        std::env::var("CRAT_BOC1_NAME").expect("A12 funnel worker requires CRAT_BOC1_NAME");
    let artifact = std::env::var("CRAT_BOC1_FUNNEL_PAIR_ARTIFACT")
        .expect("A12 funnel worker requires CRAT_BOC1_FUNNEL_PAIR_ARTIFACT");
    let measurement = measure_program(tcx, &program_name);
    fs::write(&artifact, &measurement.ledger).expect("write A12 funnel pair ledger");
    let counts = summarize(&measurement.bits);

    let mut row = Row::default();
    let has_unknown = measurement.s2_unknown > 0 || measurement.s3_unknown > 0;
    row.set("status", if has_unknown { "unknown" } else { "ok" });
    row.set("data", if has_unknown { "false" } else { "true" });
    row.set("copy_lend_mode", CopyLendMode::current().label());
    row.set("repair", RepairMode::current().label());
    row.set("l2", "0");
    row.set("safe_mono", SafeMonoMode::current().label());
    row.set("mut_facts", MutFactsMode::current().label());
    row.set("z3_full_version", z3::full_version().to_string());
    row.set("smt_seed", 0);
    row.set("sat_seed", 0);
    row.set("funnel_query_timeout_s", QUERY_TIMEOUT.as_secs());
    row.set("funnel_program_bound_s", program_bound_seconds(counts.s1));
    row.set("funnel_sample_k", SAMPLE_K);
    row.set("funnel_attribution_scope", "sampled-option-a");
    row.set("funnel_s0", counts.s0);
    row.set("funnel_s1", counts.s1);
    row.set("funnel_s2", counts.s2);
    row.set("funnel_s3", counts.s3);
    row.set("funnel_s4", counts.s4);
    row.set("funnel_s2_unknown", measurement.s2_unknown);
    row.set("funnel_s3_unknown", measurement.s3_unknown);
    row.set("funnel_s2_sampled_losses", measurement.s2_sampled_losses);
    row.set("funnel_s3_sampled_losses", measurement.s3_sampled_losses);
    row.set(
        "funnel_sampled_core_unknown",
        measurement.sampled_core_unknown,
    );
    row.set("funnel_s0_sites", measurement.s0_sites);
    row.set("funnel_s1_sites", measurement.s1_sites);
    row.set("funnel_initial_selected", counts.initial_selected);
    row.set(
        "funnel_pre_replay_not_selected",
        counts.pre_replay_not_selected,
    );
    row.set("funnel_replay_lost", counts.replay_lost);
    row.set(
        "funnel_final_selected_sites",
        measurement.final_selected_sites,
    );
    row.set("funnel_tracked_checks", measurement.tracked_checks);
    row.set("pair_artifact", artifact);
    row.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    row.set(
        "t_total_s",
        format!("{:.3}", (t_tcx + t0.elapsed()).as_secs_f64()),
    );
    row
}

pub(crate) fn run_subject_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> Row {
    let t0 = Instant::now();
    assert_eq!(CopyLendMode::current(), CopyLendMode::LendArm);
    let program = collect_program(tcx);
    let origins = compute_origins(&program);
    let slots = CrateSlots::build(&program);
    let mut_facts = MutFacts::from_program(&program);
    let candidates =
        analyze_copy_lend_candidates(&program, &slots, &mut_facts, origins.native_flows());
    let s1 = candidates
        .iter()
        .filter(|candidate| candidate.drop.is_none())
        .count();
    let mut row = Row::default();
    row.set("status", "ok");
    row.set("data", "false");
    row.set("measurement", "funnel-bound-preflight");
    row.set("copy_lend_mode", CopyLendMode::current().label());
    row.set("smt_seed", 0);
    row.set("sat_seed", 0);
    row.set("funnel_s0", candidates.len());
    row.set("funnel_s1", s1);
    row.set("funnel_program_bound_s", program_bound_seconds(s1));
    row.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    row.set(
        "t_total_s",
        format!("{:.3}", (t_tcx + t0.elapsed()).as_secs_f64()),
    );
    row
}

fn usize_field(row: &Row, key: &str) -> usize {
    row.get(key)
        .unwrap_or_else(|| panic!("A12 funnel row lacks {key}: {row:?}"))
        .parse()
        .unwrap_or_else(|error| panic!("A12 funnel row has invalid {key}: {error}"))
}

fn aggregate_stage_counts(rows: &[Row]) -> StageCounts {
    StageCounts {
        s0: rows.iter().map(|row| usize_field(row, "funnel_s0")).sum(),
        s1: rows.iter().map(|row| usize_field(row, "funnel_s1")).sum(),
        s2: rows.iter().map(|row| usize_field(row, "funnel_s2")).sum(),
        s3: rows.iter().map(|row| usize_field(row, "funnel_s3")).sum(),
        s4: rows.iter().map(|row| usize_field(row, "funnel_s4")).sum(),
        initial_selected: rows
            .iter()
            .map(|row| usize_field(row, "funnel_initial_selected"))
            .sum(),
        pre_replay_not_selected: rows
            .iter()
            .map(|row| usize_field(row, "funnel_pre_replay_not_selected"))
            .sum(),
        replay_lost: rows
            .iter()
            .map(|row| usize_field(row, "funnel_replay_lost"))
            .sum(),
    }
}

fn append_ledger(combined: &mut String, ledger: &str) {
    let mut lines = ledger.lines();
    let header = lines.next().expect("A12 funnel pair header");
    if combined.is_empty() {
        combined.push_str(header);
        combined.push('\n');
    }
    for line in lines {
        combined.push_str(line);
        combined.push('\n');
    }
}

fn aggregate_ledger(ledger: &str) -> BTreeMap<(String, String), usize> {
    let mut lines = ledger.lines();
    let header = lines.next().expect("A12 funnel pair ledger header");
    let columns = header.split('\t').collect::<Vec<_>>();
    let index = |name: &str| {
        columns
            .iter()
            .position(|column| *column == name)
            .unwrap_or_else(|| panic!("A12 funnel ledger lacks {name}"))
    };
    let (s1_i, s2_i, s3_i, s4_i) = (index("s1"), index("s2"), index("s3"), index("s4"));
    let reason_i = index("s0_s1_reason");
    let s2_core_i = index("s2_core_families");
    let s3_core_i = index("s3_core_families");
    let s3_s4_i = index("s3_s4_reason");
    let mut counts = BTreeMap::new();
    for line in lines.filter(|line| !line.is_empty()) {
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields[s1_i] == "0" {
            *counts
                .entry(("S0->S1".to_owned(), fields[reason_i].to_owned()))
                .or_default() += 1;
        } else if fields[s2_i] == "0" {
            for family in fields[s2_core_i].split(',') {
                if matches!(family, "none" | "na") {
                    continue;
                }
                *counts
                    .entry(("S1->S2".to_owned(), family.to_owned()))
                    .or_default() += 1;
            }
        } else if fields[s3_i] == "0" {
            for family in fields[s3_core_i].split(',') {
                if matches!(family, "none" | "na") {
                    continue;
                }
                *counts
                    .entry(("S2->S3".to_owned(), family.to_owned()))
                    .or_default() += 1;
            }
        } else if fields[s4_i] == "0" {
            *counts
                .entry(("S3->S4".to_owned(), fields[s3_s4_i].to_owned()))
                .or_default() += 1;
        }
    }
    counts
}

fn sampled_attribution_tables(ledgers: &[(String, String)]) -> (String, String) {
    let mut tsv = String::from(
        "program\ttransition\tscope\tpopulation_losses\tsampled_losses\tcore_unknown\t\
         family\tincidence\tpercent_of_sample\tcopy_lend_mode\tsample_k\n",
    );
    let mut markdown = String::from(
        "| program | transition | scope | population losses | sampled | core Unknown | family | incidence | sample % |\n\
         |---|---|---|---:|---:|---:|---|---:|---:|\n",
    );
    let mut aggregate_population = BTreeMap::<String, usize>::new();
    let mut aggregate_sampled = BTreeMap::<String, usize>::new();
    let mut aggregate_unknown = BTreeMap::<String, usize>::new();
    let mut aggregate_exhaustive = BTreeMap::<String, bool>::new();
    let mut aggregate_families = BTreeMap::<(String, String), usize>::new();

    for (program, ledger) in ledgers {
        let mut lines = ledger.lines();
        let header = lines.next().expect("Option-A funnel ledger header");
        let columns = header.split('\t').collect::<Vec<_>>();
        let index = |name: &str| {
            columns
                .iter()
                .position(|column| *column == name)
                .unwrap_or_else(|| panic!("Option-A funnel ledger lacks {name}"))
        };
        let records = lines
            .filter(|line| !line.is_empty())
            .map(|line| line.split('\t').collect::<Vec<_>>())
            .collect::<Vec<_>>();
        for (transition, from, to, scope_name, status_name, families_name) in [
            (
                "S1->S2",
                "s1",
                "s2",
                "s2_core_scope",
                "s2_core_status",
                "s2_core_families",
            ),
            (
                "S2->S3",
                "s2",
                "s3",
                "s3_core_scope",
                "s3_core_status",
                "s3_core_families",
            ),
        ] {
            let (from_i, to_i) = (index(from), index(to));
            let (scope_i, status_i, families_i) =
                (index(scope_name), index(status_name), index(families_name));
            let losses = records
                .iter()
                .filter(|record| record[from_i] == "1" && record[to_i] == "0")
                .collect::<Vec<_>>();
            let sampled = losses
                .iter()
                .copied()
                .filter(|record| matches!(record[scope_i], "sampled" | "exhaustive"))
                .collect::<Vec<_>>();
            let scope = if losses.len() <= SAMPLE_K {
                "EXHAUSTIVE"
            } else {
                "SAMPLED"
            };
            assert_eq!(
                sampled.len(),
                losses.len().min(SAMPLE_K),
                "{program} {transition} deterministic sample size drifted"
            );
            let unknown = sampled
                .iter()
                .filter(|record| record[status_i] == "unknown")
                .count();
            let mut families = BTreeMap::<String, usize>::new();
            for record in sampled.iter().filter(|record| record[status_i] == "unsat") {
                for family in record[families_i].split(',') {
                    if !matches!(family, "none" | "na") {
                        *families.entry(family.to_owned()).or_default() += 1;
                    }
                }
            }
            if families.is_empty() {
                families.insert("none".to_owned(), 0);
            }
            *aggregate_population
                .entry(transition.to_owned())
                .or_default() += losses.len();
            *aggregate_sampled.entry(transition.to_owned()).or_default() += sampled.len();
            *aggregate_unknown.entry(transition.to_owned()).or_default() += unknown;
            aggregate_exhaustive
                .entry(transition.to_owned())
                .and_modify(|all| *all &= scope == "EXHAUSTIVE")
                .or_insert(scope == "EXHAUSTIVE");
            for (family, incidence) in &families {
                if family != "none" {
                    *aggregate_families
                        .entry((transition.to_owned(), family.clone()))
                        .or_default() += incidence;
                }
                let percent = if sampled.is_empty() {
                    0.0
                } else {
                    *incidence as f64 * 100.0 / sampled.len() as f64
                };
                tsv.push_str(&format!(
                    "{program}\t{transition}\t{scope}\t{}\t{}\t{unknown}\t{family}\t{incidence}\t{percent:.2}\tlend_arm\t{SAMPLE_K}\n",
                    losses.len(),
                    sampled.len(),
                ));
                markdown.push_str(&format!(
                    "| {program} | {transition} | {scope} | {} | {} | {unknown} | {family} | {incidence} | {percent:.2} |\n",
                    losses.len(),
                    sampled.len(),
                ));
            }
        }
    }

    for transition in ["S1->S2", "S2->S3"] {
        let population = aggregate_population.get(transition).copied().unwrap_or(0);
        let sampled = aggregate_sampled.get(transition).copied().unwrap_or(0);
        let unknown = aggregate_unknown.get(transition).copied().unwrap_or(0);
        let scope = if aggregate_exhaustive
            .get(transition)
            .copied()
            .unwrap_or(true)
        {
            "EXHAUSTIVE"
        } else {
            "SAMPLED"
        };
        let families = aggregate_families
            .iter()
            .filter(|((candidate, _), _)| candidate == transition)
            .map(|((_, family), incidence)| (family.clone(), *incidence))
            .collect::<Vec<_>>();
        let families = if families.is_empty() {
            vec![("none".to_owned(), 0)]
        } else {
            families
        };
        for (family, incidence) in families {
            let percent = if sampled == 0 {
                0.0
            } else {
                incidence as f64 * 100.0 / sampled as f64
            };
            tsv.push_str(&format!(
                "ALL_FIVE\t{transition}\t{scope}\t{population}\t{sampled}\t{unknown}\t{family}\t{incidence}\t{percent:.2}\tlend_arm\t{SAMPLE_K}\n"
            ));
            markdown.push_str(&format!(
                "| **ALL FIVE** | {transition} | **{scope}** | {population} | {sampled} | {unknown} | {family} | {incidence} | {percent:.2} |\n"
            ));
        }
    }
    (tsv, markdown)
}

fn route_for(counts: StageCounts) -> &'static str {
    let losses = [
        (counts.s0 - counts.s1, "S1-dominated:eligibility-revisit"),
        (counts.s1 - counts.s2, "S2-dominated:A5-execute"),
        (counts.s2 - counts.s3, "S3-dominated:price-C4-relaxation"),
        (counts.s3 - counts.s4, "S4-dominated:price-objective-reward"),
    ];
    let max = losses.iter().map(|(loss, _)| *loss).max().unwrap_or(0);
    let winners = losses
        .iter()
        .filter(|(loss, _)| *loss == max)
        .map(|(_, route)| *route)
        .collect::<Vec<_>>();
    assert_eq!(
        winners.len(),
        1,
        "A12 funnel routing has a tied dominant loss: {winners:?}"
    );
    winners[0]
}

fn render_report(rows: &[Row], aggregate: StageCounts, attribution: &str, route: &str) -> String {
    let columns = [
        "program",
        "sloc",
        "status",
        "copy_lend_mode",
        "funnel_s0",
        "funnel_s1",
        "funnel_s2",
        "funnel_s3",
        "funnel_s4",
        "funnel_initial_selected",
        "funnel_pre_replay_not_selected",
        "funnel_replay_lost",
        "wall_s",
        "peak_rss_kb",
    ];
    format!(
        "# A12 CopyLend funnel\n\n\
         Contract: mode=lend_arm; repair=mode_a; L2=0; seeds=0; exact attributions; \
         derived corpus digest `{CORPUS_DIGEST}`.\n\n\
         {}\n\
         **TOTAL:** S0={} / S1={} / S2={} / S3={} / S4={}; initial selected={}; \
         pre-replay nonselection={}; replay lost={}.\n\n\
         **Route:** `{route}`.\n\n\
         ## Exact drop attribution\n\n\
         | transition | reason/family | incidence |\n|---|---|---:|\n{}",
        super::report::render_markdown(rows, &columns),
        aggregate.s0,
        aggregate.s1,
        aggregate.s2,
        aggregate.s3,
        aggregate.s4,
        aggregate.initial_selected,
        aggregate.pre_replay_not_selected,
        aggregate.replay_lost,
        attribution,
    )
}

#[test]
#[ignore = "A12 retained-mechanism funnel; deterministic 20-program measurement"]
fn a12_copy_lend_funnel_corpus() {
    assert_eq!(CopyLendMode::current(), CopyLendMode::LendArm);
    assert_eq!(std::env::var("CRAT_BO_REPAIR").as_deref(), Ok("mode_a"));
    assert_eq!(
        std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
        Ok("0")
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_TIMEOUT_SECS").as_deref(),
        Ok("900")
    );
    assert_eq!(std::env::var("CRAT_BOC1_MEM_MB").as_deref(), Ok("49152"));
    assert!(
        std::env::var_os("CRAT_BOC1_PROGRAMS").is_none(),
        "A12 funnel must cover all 20 programs"
    );
    assert_eq!(CORPUS.len(), 20);

    let root = orchestrate::workspace_root();
    assert!(root.join("benchmarks/rs-crown-derived").is_dir());
    assert!(root.join("deps_crate/target/debug/deps").is_dir());
    let out = orchestrate::out_dir();
    let pair_dir = out.join("pairs");
    fs::create_dir_all(&pair_dir).expect("create A12 funnel output");

    let mut rows = Vec::new();
    let mut combined = String::new();
    for program in CORPUS {
        let pair_path = pair_dir.join(format!("{}.tsv", program.name));
        let outcome = orchestrate::run_child_env(
            program.name,
            &program.input_path(&root),
            "copy-lend-funnel",
            Duration::from_secs(900),
            &[(
                "CRAT_BOC1_FUNNEL_PAIR_ARTIFACT",
                pair_path.display().to_string(),
            )],
        );
        assert_eq!(
            outcome.status, "ok",
            "{} A12 funnel failed: {}",
            program.name, outcome.note
        );
        let mut row = outcome.row.expect("A12 funnel worker row");
        assert_eq!(row.get("copy_lend_mode"), Some("lend_arm"));
        row.set("program", program.name);
        row.set("sloc", program.sloc);
        row.set("wall_s", format!("{:.3}", outcome.wall_s));
        row.set("peak_rss_kb", outcome.peak_rss_kb);
        let ledger = fs::read_to_string(&pair_path).expect("read A12 funnel pair ledger");
        let mut lines = ledger.lines();
        let header = lines.next().expect("A12 funnel pair header");
        if combined.is_empty() {
            combined.push_str(header);
            combined.push('\n');
        }
        for line in lines {
            combined.push_str(line);
            combined.push('\n');
        }
        rows.push(row);
    }

    let aggregate = StageCounts {
        s0: rows.iter().map(|row| usize_field(row, "funnel_s0")).sum(),
        s1: rows.iter().map(|row| usize_field(row, "funnel_s1")).sum(),
        s2: rows.iter().map(|row| usize_field(row, "funnel_s2")).sum(),
        s3: rows.iter().map(|row| usize_field(row, "funnel_s3")).sum(),
        s4: rows.iter().map(|row| usize_field(row, "funnel_s4")).sum(),
        initial_selected: rows
            .iter()
            .map(|row| usize_field(row, "funnel_initial_selected"))
            .sum(),
        pre_replay_not_selected: rows
            .iter()
            .map(|row| usize_field(row, "funnel_pre_replay_not_selected"))
            .sum(),
        replay_lost: rows
            .iter()
            .map(|row| usize_field(row, "funnel_replay_lost"))
            .sum(),
    };
    assert!(aggregate.s0 >= aggregate.s1);
    assert!(aggregate.s1 >= aggregate.s2);
    assert!(aggregate.s2 >= aggregate.s3);
    assert!(aggregate.s3 >= aggregate.s4);
    assert_eq!(aggregate.s1, 911, "A12 funnel S1 anchor drifted");
    assert_eq!(aggregate.s4, 0, "A12 funnel S4 anchor drifted");
    assert_eq!(
        aggregate.pre_replay_not_selected + aggregate.replay_lost,
        aggregate.s3 - aggregate.s4,
        "S3->S4 attribution does not partition the loss"
    );

    let attribution = aggregate_ledger(&combined);
    let mut attribution_tsv =
        String::from("transition\treason_or_family\tincidence\tcopy_lend_mode\n");
    let mut attribution_md = String::new();
    for ((transition, reason), count) in attribution {
        attribution_tsv.push_str(&format!("{transition}\t{reason}\t{count}\tlend_arm\n"));
        attribution_md.push_str(&format!("| {transition} | {reason} | {count} |\n"));
    }
    let route = route_for(aggregate);

    fs::write(out.join("pair-ledger.tsv"), &combined).expect("write combined A12 pair ledger");
    fs::write(out.join("drop-attribution.tsv"), &attribution_tsv)
        .expect("write A12 funnel attribution");
    fs::write(out.join("results.csv"), super::report::render_csv(&rows))
        .expect("write A12 funnel results CSV");
    let mut jsonl = provenance::line(
        &orchestrate::git_sha(),
        orchestrate::git_dirty(),
        orchestrate::now_unix(),
    );
    jsonl.push('\n');
    for row in &rows {
        jsonl.push_str(&super::report::to_json_line(row));
        jsonl.push('\n');
    }
    fs::write(out.join("results.jsonl"), jsonl).expect("write A12 funnel results JSONL");
    fs::write(
        out.join("report.md"),
        render_report(&rows, aggregate, &attribution_md, route),
    )
    .expect("write A12 funnel report");
    fs::write(
        out.join("receipt.txt"),
        format!(
            "schema=a12-copy-lend-funnel-v1\nstatus=ok\ndata=true\nanalysis_head={}\n\
             analysis_dirty={}\nderived_substrate_digest={CORPUS_DIGEST}\nprograms=20\n\
             execution=sequential\ncopy_lend_mode=lend_arm\ndefault_mode=baseline\nrepair=mode_a\n\
             l2=0\nsafe_mono=per_site\nmut_facts=on\nfork_engine=fork\nnb4r_routing=on\n\
             smt_random_seed=0\nsat_random_seed=0\ntimeout_seconds=900\nmemory_mib=49152\n\
             attribution=exact-primary-eligibility-plus-exact-raw-family-core-incidence\n\
             s0={}\ns1={}\ns2={}\ns3={}\ns4={}\ninitial_selected={}\n\
             pre_replay_not_selected={}\nreplay_lost={}\nroute={}\n",
            orchestrate::git_sha(),
            orchestrate::git_dirty(),
            aggregate.s0,
            aggregate.s1,
            aggregate.s2,
            aggregate.s3,
            aggregate.s4,
            aggregate.initial_selected,
            aggregate.pre_replay_not_selected,
            aggregate.replay_lost,
            route,
        ),
    )
    .expect("write A12 funnel receipt");

    println!(
        "{}",
        render_report(&rows, aggregate, &attribution_md, route)
    );
}

#[test]
#[ignore = "A12 Option-A completion: retain 15 exact shards, run remaining five"]
fn a12_copy_lend_funnel_option_a_completion() {
    const PRIOR: &[&str] = &[
        "bst",
        "avl",
        "ht",
        "libcsv",
        "buffer",
        "quadtree",
        "urlparser",
        "robotfindskitten",
        "rgba",
        "genann",
        "libtree",
        "json.h",
        "binn",
        "libzahl",
        "lil",
    ];
    const REMAINING: &[&str] = &["heman", "bzip2", "lodepng", "tulipindicators", "brotli"];
    assert_eq!(CopyLendMode::current(), CopyLendMode::LendArm);
    assert_eq!(std::env::var("CRAT_BO_REPAIR").as_deref(), Ok("mode_a"));
    assert_eq!(
        std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
        Ok("0")
    );
    assert_eq!(std::env::var("CRAT_BOC1_MEM_MB").as_deref(), Ok("49152"));
    assert_eq!(CORPUS.len(), 20);
    assert_eq!(PRIOR.len() + REMAINING.len(), CORPUS.len());

    let prior_root = std::env::var("CRAT_BOC1_FUNNEL_PRIOR_ROOT")
        .map(std::path::PathBuf::from)
        .expect("Option A requires CRAT_BOC1_FUNNEL_PRIOR_ROOT");
    let root = orchestrate::workspace_root();
    assert!(root.join("benchmarks/rs-crown-derived").is_dir());
    assert!(root.join("deps_crate/target/debug/deps").is_dir());
    let out = orchestrate::out_dir();
    let pair_dir = out.join("pairs-option-a");
    fs::create_dir_all(&pair_dir).expect("create Option-A output");

    let mut rows = Vec::new();
    let mut prior_ledgers = Vec::<(String, String)>::new();
    let mut new_ledgers = Vec::<(String, String)>::new();
    let mut combined_new = String::new();
    let mut bounds = String::from(
        "program\ts1_pairs\tprogram_bound_seconds\tpreflight_wall_seconds\t\
         worker_wall_seconds\tcopy_lend_mode\n",
    );
    for program in CORPUS {
        if PRIOR.contains(&program.name) {
            let stdout_path = prior_root
                .join("logs")
                .join(format!("{}.copy-lend-funnel.out", program.name));
            let stdout = fs::read_to_string(&stdout_path)
                .unwrap_or_else(|error| panic!("read {}: {error}", stdout_path.display()));
            let mut row = stdout
                .lines()
                .find_map(super::report::parse_kv_line)
                .unwrap_or_else(|| panic!("{} prior row missing", program.name));
            assert_eq!(row.get("status"), Some("ok"));
            assert_eq!(row.get("copy_lend_mode"), Some("lend_arm"));
            row.set("program", program.name);
            row.set("sloc", program.sloc);
            row.set("shard_scope", "prior-exhaustive");
            row.set("shard_head", "c46a4cb9ea266615436771649eaa931066e5f38a");
            let ledger_path = prior_root
                .join("pairs")
                .join(format!("{}.tsv", program.name));
            let ledger = fs::read_to_string(&ledger_path)
                .unwrap_or_else(|error| panic!("read {}: {error}", ledger_path.display()));
            prior_ledgers.push((program.name.to_owned(), ledger));
            rows.push(row);
            continue;
        }
        assert!(REMAINING.contains(&program.name));
        let preflight = orchestrate::run_child(
            program.name,
            &program.input_path(&root),
            "copy-lend-funnel-subjects",
            Duration::from_secs(14_400),
        );
        assert_eq!(
            preflight.status, "ok",
            "{} Option-A preflight failed: {}",
            program.name, preflight.note
        );
        let preflight_row = preflight.row.expect("Option-A preflight row");
        assert_eq!(preflight_row.get("copy_lend_mode"), Some("lend_arm"));
        let s1 = usize_field(&preflight_row, "funnel_s1");
        let bound = program_bound_seconds(s1);
        assert_eq!(
            usize_field(&preflight_row, "funnel_program_bound_s"),
            usize::try_from(bound).expect("bound fits usize")
        );
        let pair_path = pair_dir.join(format!("{}.tsv", program.name));
        let outcome = orchestrate::run_child_env(
            program.name,
            &program.input_path(&root),
            "copy-lend-funnel",
            Duration::from_secs(bound),
            &[(
                "CRAT_BOC1_FUNNEL_PAIR_ARTIFACT",
                pair_path.display().to_string(),
            )],
        );
        assert_eq!(
            outcome.status, "ok",
            "{} Option-A worker failed: {}",
            program.name, outcome.note
        );
        let mut row = outcome.row.expect("Option-A worker row");
        assert_eq!(row.get("copy_lend_mode"), Some("lend_arm"));
        assert_eq!(usize_field(&row, "funnel_s1"), s1);
        assert_eq!(usize_field(&row, "funnel_s2_unknown"), 0);
        assert_eq!(usize_field(&row, "funnel_s3_unknown"), 0);
        row.set("program", program.name);
        row.set("sloc", program.sloc);
        row.set("wall_s", format!("{:.3}", outcome.wall_s));
        row.set("peak_rss_kb", outcome.peak_rss_kb);
        row.set("shard_scope", "option-a-sampled");
        row.set("shard_head", orchestrate::git_sha());
        bounds.push_str(&format!(
            "{}\t{s1}\t{bound}\t{:.3}\t{:.3}\tlend_arm\n",
            program.name, preflight.wall_s, outcome.wall_s
        ));
        let ledger = fs::read_to_string(&pair_path).expect("read Option-A pair ledger");
        append_ledger(&mut combined_new, &ledger);
        new_ledgers.push((program.name.to_owned(), ledger));
        rows.push(row);
    }

    let corpus_names = rows
        .iter()
        .map(|row| row.get("program").expect("program row"))
        .collect::<Vec<_>>();
    assert_eq!(
        corpus_names,
        CORPUS
            .iter()
            .map(|program| program.name)
            .collect::<Vec<_>>()
    );
    let aggregate = aggregate_stage_counts(&rows);
    let exact_unknown = rows
        .iter()
        .map(|row| {
            row.get("funnel_s2_unknown")
                .and_then(|value| value.parse::<usize>().ok())
                .unwrap_or(0)
                + row
                    .get("funnel_s3_unknown")
                    .and_then(|value| value.parse::<usize>().ok())
                    .unwrap_or(0)
        })
        .sum::<usize>();
    assert_eq!(exact_unknown, 0, "exact funnel contains typed Unknown rows");
    assert_eq!(
        aggregate.s1, 911,
        "A12 funnel S1 residual against three-way"
    );
    assert_eq!(aggregate.s4, 0, "A12 funnel S4 anchor drifted");
    assert_eq!(
        aggregate.pre_replay_not_selected + aggregate.replay_lost,
        aggregate.s3 - aggregate.s4,
        "S3->S4 attribution does not partition the full loss"
    );

    let mut prior_combined = String::new();
    for (_, ledger) in &prior_ledgers {
        append_ledger(&mut prior_combined, ledger);
    }
    let prior_counts = aggregate_ledger(&prior_combined);
    let new_counts = aggregate_ledger(&combined_new);
    let mut exact_edges = BTreeMap::<(String, String), usize>::new();
    for (key, count) in prior_counts.iter().chain(new_counts.iter()) {
        if matches!(key.0.as_str(), "S0->S1" | "S3->S4") {
            *exact_edges.entry(key.clone()).or_default() += count;
        }
    }
    let mut exact_edges_tsv =
        String::from("transition\treason\tincidence\tscope\tcopy_lend_mode\n");
    let mut exact_edges_md = String::new();
    for ((transition, reason), incidence) in exact_edges {
        exact_edges_tsv.push_str(&format!(
            "{transition}\t{reason}\t{incidence}\tEXHAUSTIVE\tlend_arm\n"
        ));
        exact_edges_md.push_str(&format!(
            "| {transition} | {reason} | {incidence} | EXHAUSTIVE |\n"
        ));
    }

    let prior_stage = aggregate_stage_counts(
        &rows
            .iter()
            .filter(|row| row.get("shard_scope") == Some("prior-exhaustive"))
            .cloned()
            .collect::<Vec<_>>(),
    );
    let prior_s2_losses = prior_stage.s1 - prior_stage.s2;
    let mut prior_family_tsv = String::from(
        "transition\tfamily\tincidence\tloss_denominator\tpercent\tscope\tcopy_lend_mode\n",
    );
    let mut prior_family_md = String::new();
    for ((transition, family), incidence) in &prior_counts {
        if transition != "S1->S2" && transition != "S2->S3" {
            continue;
        }
        let denominator = if transition == "S1->S2" {
            prior_s2_losses
        } else {
            prior_stage.s2 - prior_stage.s3
        };
        let percent = if denominator == 0 {
            0.0
        } else {
            *incidence as f64 * 100.0 / denominator as f64
        };
        prior_family_tsv.push_str(&format!(
            "{transition}\t{family}\t{incidence}\t{denominator}\t{percent:.2}\tEXHAUSTIVE\tlend_arm\n"
        ));
        prior_family_md.push_str(&format!(
            "| {transition} | {family} | {incidence}/{denominator} | {percent:.2} | EXHAUSTIVE |\n"
        ));
    }
    let (sample_tsv, sample_md) = sampled_attribution_tables(&new_ledgers);

    let columns = [
        "program",
        "funnel_s0",
        "funnel_s1",
        "funnel_s2",
        "funnel_s3",
        "funnel_s4",
        "funnel_initial_selected",
        "funnel_pre_replay_not_selected",
        "funnel_replay_lost",
        "shard_scope",
    ];
    let report = format!(
        "# A12 CopyLend funnel — Option A completion\n\n\
         Mode `lend_arm`, default remains `baseline`; seeds 0/0; exact S0–S4; \
         first 15 family cores exhaustive; remaining-five family cores K={SAMPLE_K} sampled.\n\n\
         {}\n\
         **TOTAL:** S0={} / S1={} / S2={} / S3={} / S4={}; initial selected={}; \
         pre-replay nonselection={}; replay lost={}; exact Unknown={exact_unknown}.\n\n\
         Transition losses: S0→S1={}, S1→S2={}, S2→S3={}, S3→S4={}.\n\n\
         ## Exact edge attribution\n\n\
         | transition | reason | incidence | scope |\n|---|---|---:|---|\n{exact_edges_md}\n\
         ## First-15 family attribution\n\n\
         | transition | family | incidence/denominator | % | scope |\n|---|---|---:|---:|---|\n{prior_family_md}\n\
         ## Remaining-five family attribution\n\n{sample_md}\n\
         The first-15 S3→S4 Ref/Ref result is correct behavior, not evidence for an objective reward. \
         Loop-2 routing is reserved to the user.\n",
        super::report::render_markdown(&rows, &columns),
        aggregate.s0,
        aggregate.s1,
        aggregate.s2,
        aggregate.s3,
        aggregate.s4,
        aggregate.initial_selected,
        aggregate.pre_replay_not_selected,
        aggregate.replay_lost,
        aggregate.s0 - aggregate.s1,
        aggregate.s1 - aggregate.s2,
        aggregate.s2 - aggregate.s3,
        aggregate.s3 - aggregate.s4,
    );

    fs::write(out.join("option-a-pair-ledger.tsv"), &combined_new)
        .expect("write Option-A pair ledger");
    fs::write(out.join("exact-edge-attribution.tsv"), exact_edges_tsv)
        .expect("write exact edge attribution");
    fs::write(
        out.join("prior-exhaustive-family-attribution.tsv"),
        prior_family_tsv,
    )
    .expect("write prior family attribution");
    fs::write(
        out.join("option-a-sampled-family-attribution.tsv"),
        sample_tsv,
    )
    .expect("write sampled family attribution");
    fs::write(out.join("program-bounds.tsv"), bounds).expect("write Option-A bounds");
    fs::write(out.join("results.csv"), super::report::render_csv(&rows))
        .expect("write Option-A results CSV");
    let mut jsonl = provenance::line(
        &orchestrate::git_sha(),
        orchestrate::git_dirty(),
        orchestrate::now_unix(),
    );
    jsonl.push('\n');
    for row in &rows {
        jsonl.push_str(&super::report::to_json_line(row));
        jsonl.push('\n');
    }
    fs::write(out.join("results.jsonl"), jsonl).expect("write Option-A results JSONL");
    fs::write(out.join("report.md"), &report).expect("write Option-A report");
    fs::write(
        out.join("receipt.txt"),
        format!(
            "schema=a12-copy-lend-funnel-option-a-v1\nstatus=ok\ndata=true\nanalysis_head={}\n\
             analysis_dirty={}\nprior_head=c46a4cb9ea266615436771649eaa931066e5f38a\n\
             prior_root={}\nderived_substrate_digest={CORPUS_DIGEST}\nprograms=20\nprior_exact_programs=15\n\
             option_a_programs=5\ncopy_lend_mode=lend_arm\ndefault_mode=baseline\nrepair=mode_a\nl2=0\n\
             smt_random_seed=0\nsat_random_seed=0\nquery_timeout_seconds=600\n\
             program_bound_formula=max(14400,S1_pairs*300)\nsample_k={SAMPLE_K}\nsample_rule=first-K-by-pinned-pair-order\n\
             s0={}\ns1={}\ns2={}\ns3={}\ns4={}\nexact_unknown={exact_unknown}\n\
             initial_selected={}\npre_replay_not_selected={}\nreplay_lost={}\nloop2_route=user-reserved\n",
            orchestrate::git_sha(),
            orchestrate::git_dirty(),
            prior_root.display(),
            aggregate.s0,
            aggregate.s1,
            aggregate.s2,
            aggregate.s3,
            aggregate.s4,
            aggregate.initial_selected,
            aggregate.pre_replay_not_selected,
            aggregate.replay_lost,
        ),
    )
    .expect("write Option-A receipt");
    println!("{report}");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn funnel_stage_summary_is_nested_and_partitions_s3_to_s4() {
        let rows = [
            StageBits {
                s0: true,
                ..StageBits::default()
            },
            StageBits {
                s0: true,
                s1: true,
                ..StageBits::default()
            },
            StageBits {
                s0: true,
                s1: true,
                s2: true,
                s3: true,
                ..StageBits::default()
            },
            StageBits {
                s0: true,
                s1: true,
                s2: true,
                s3: true,
                initial_selected: true,
                ..StageBits::default()
            },
            StageBits {
                s0: true,
                s1: true,
                s2: true,
                s3: true,
                s4: true,
                initial_selected: true,
            },
        ];
        assert_eq!(
            summarize(&rows),
            StageCounts {
                s0: 5,
                s1: 4,
                s2: 3,
                s3: 3,
                s4: 1,
                initial_selected: 2,
                pre_replay_not_selected: 1,
                replay_lost: 1,
            }
        );
    }

    #[test]
    fn l14_seed_families_are_named_first_without_losing_registered_families() {
        let order = seeded_family_order();
        assert_eq!(order.get(0), Some(&"kind-equate"));
        assert_eq!(order.get(1), Some(&"own-linear"));
        for family in CORE_LABEL_FAMILIES {
            assert_eq!(
                order
                    .iter()
                    .filter(|candidate| *candidate == family)
                    .count(),
                1,
                "registered family {family} must occur exactly once"
            );
        }
    }

    #[test]
    fn option_a_sample_is_the_first_k_losses_in_pinned_order() {
        let losses = (10..22).collect::<Vec<_>>();
        assert_eq!(sample_loss_indices(&losses), (10..18).collect::<Vec<_>>());
        assert_eq!(sample_loss_indices(&losses[..5]), losses[..5]);
    }

    #[test]
    fn option_a_program_bound_inherits_the_census_formula() {
        assert_eq!(program_bound_seconds(0), 14_400);
        assert_eq!(program_bound_seconds(48), 14_400);
        assert_eq!(program_bound_seconds(49), 14_700);
        assert_eq!(program_bound_seconds(171), 51_300);
    }

    #[test]
    fn l14_seed_is_attributed_before_lend_sat() {
        ::utils::compilation::run_compiler_on_str(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn f() -> i32 {
    let p = unsafe { malloc(4) } as *mut i32;
    let r = p;
    let q = p;
    unsafe { *r = 1 };
    let value = unsafe { *q };
    unsafe { free(p as *mut core::ffi::c_void) };
    value
}
"#,
            |tcx| {
                CopyLendMode::LendArm.with_override(|| {
                    let measurement = measure_program(tcx, "l14-seed");
                    let counts = summarize(&measurement.bits);
                    assert_eq!(counts.s1, 1);
                    assert_eq!(counts.s2, 0, "{}", measurement.ledger);
                    assert_eq!(counts.s3, 0);
                    assert_eq!(counts.initial_selected, 0);
                    assert_eq!(counts.s4, 0);
                    assert!(
                        measurement.ledger.contains("kind-equate"),
                        "{}",
                        measurement.ledger
                    );
                    assert!(measurement.ledger.contains("\tlend_arm\t0\t0"));
                    assert_eq!(seeded_family_order()[1], "own-linear");
                    assert_eq!(CopyLendMode::current().label(), "lend_arm");
                });
            },
        )
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn c4_multisite_guard_separates_s2_from_s3() {
        use crate::analyses::borrow_ownership::{
            solver::BoOwnDatabase,
            ssa::constraint::{Database, Gen},
        };

        ::utils::compilation::run_compiler_on_str(
            r#"
pub unsafe fn f(p: *const i32) -> i32 {
    let q = p;
    unsafe { *q }
}
"#,
            |tcx| {
                CopyLendMode::LendArm.with_override(|| {
                    let program = collect_program(tcx);
                    let origins = compute_origins(&program);
                    let slots = CrateSlots::build(&program);
                    let mut_facts = MutFacts::from_program(&program);
                    let pair = analyze_copy_lend_candidates(
                        &program,
                        &slots,
                        &mut_facts,
                        origins.native_flows(),
                    )
                    .into_iter()
                    .find(|candidate| candidate.drop.is_none())
                    .expect("one eligible copy pair")
                    .pair;
                    let solver = KindSolver::new(&slots);
                    solver.lend_or_equate(pair.lhs, pair.rhs);
                    let lend = solver.lend_guard(pair.lhs, pair.rhs);

                    let mut database = BoOwnDatabase::new(solver.optimize(), solver.tracker());
                    let mut generator = Gen::new();
                    let vars = database.new_vars(&mut generator, 6).collect::<Vec<_>>();
                    database.push_guarded_copy_constraints(&lend, vars[0], vars[1], vars[2], false);
                    database.push_guarded_copy_constraints(&lend, vars[3], vars[4], vars[5], false);
                    let source_owns = Bool::or(&[
                        database.own_bool(vars[1]),
                        database.own_bool(vars[2]),
                        database.own_bool(vars[4]),
                        database.own_bool(vars[5]),
                    ]);
                    let destination_owns =
                        Bool::or(&[database.own_bool(vars[0]), database.own_bool(vars[3])]);
                    let second_site_source_use = database.own_bool(vars[5]).clone();
                    solver.link_own(pair.rhs, &source_owns);
                    solver.link_own(pair.lhs, &destination_owns);
                    solver.optimize().assert(&!second_site_source_use);
                    drop(database);

                    assert_eq!(
                        solver.check_with_assumptions(&[solver.owning_literal(pair.rhs)]),
                        SatResult::Sat,
                        "S2 permits source ownership through the equal arm"
                    );
                    assert_eq!(
                        solver.check_with_assumptions(&[lend]),
                        SatResult::Unsat,
                        "S3 activates both site obligations, including the impossible second site"
                    );
                });
            },
        )
        .unwrap_or_else(|error| error.raise());
    }
}
