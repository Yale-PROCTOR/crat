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
) -> (bool, Vec<String>) {
    let mut assumptions = tracks.to_vec();
    assumptions.push(force.clone());
    match solver.check_with_assumptions(&assumptions) {
        SatResult::Sat => (true, Vec::new()),
        SatResult::Unknown => panic!("A12 funnel hard assumption query returned Unknown"),
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
            (false, families)
        }
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
    tracked_checks: usize,
    final_selected_sites: usize,
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

    let tracked = KindSolver::new_family_tracked(&slots);
    tracked.set_random_seed(0);
    let tracked_construction = construct_bo_into(
        &program,
        &slots,
        &origins,
        &mut_facts,
        &tracked,
        CopyLendMode::LendArm,
    )
    .expect("A12 funnel tracked construction");
    let tracker = tracked.tracker().expect("A12 funnel family tracker");
    tracker.set_context("field-law");
    constrain_field_ownership(&tracked, &slots, &program);
    let tracks = tracker.tracks();

    let candidate_eligible = candidates
        .iter()
        .filter(|candidate| candidate.drop.is_none())
        .map(|candidate| candidate.pair)
        .collect::<FxHashSet<_>>();
    assert_eq!(
        candidate_eligible, tracked_construction.eligibility.pairs,
        "funnel classifier and production eligibility diverged"
    );

    let initial_solver = KindSolver::new(&slots);
    initial_solver.set_random_seed(0);
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
         s0_s1_reason\ts2_core_families\ts3_core_families\tinitial_lhs_kind\t\
         initial_rhs_kind\tinitial_selected\tfinal_lhs_kind\tfinal_rhs_kind\t\
         final_selected\ts3_s4_reason\tcopy_lend_mode\tsmt_seed\tsat_seed\n",
    );
    let mut bits = Vec::with_capacity(candidates.len());
    for CopyLendPairCandidate { pair, sites, drop } in candidates {
        let s1 = drop.is_none();
        let (s2, s2_core) = if s1 {
            hard_query(&tracked, tracker, &tracks, tracked.owning_literal(pair.rhs))
        } else {
            (false, Vec::new())
        };
        let (s3, s3_core) = if s2 {
            hard_query(
                &tracked,
                tracker,
                &tracks,
                tracked.lend_guard(pair.lhs, pair.rhs),
            )
        } else {
            (false, Vec::new())
        };
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
        ledger.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t1\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\tlend_arm\t0\t0\n",
            clean_cell(program_name),
            clean_cell(&tcx.def_path_str(fn_did.to_def_id())),
            slotref_diagnostic(pair.lhs),
            slotref_diagnostic(pair.rhs),
            sites.len(),
            locations,
            usize::from(s1),
            usize::from(s2),
            usize::from(s3),
            usize::from(s4),
            drop.map_or("eligible", |reason| reason.label()),
            if s1 { join_families(&s2_core) } else { "na".to_owned() },
            if s2 { join_families(&s3_core) } else { "na".to_owned() },
            kind_label(initial_lhs),
            kind_label(initial_rhs),
            usize::from(initial_selected),
            kind_label(final_lhs),
            kind_label(final_rhs),
            usize::from(s4),
            s3_s4_reason,
        ));
        bits.push(stage);
    }

    Measurement {
        s1_sites: final_construction.eligibility.sites.len(),
        tracked_checks: tracked.check_sat_count(),
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
    row.set("status", "ok");
    row.set("data", "true");
    row.set("copy_lend_mode", CopyLendMode::current().label());
    row.set("repair", RepairMode::current().label());
    row.set("l2", "0");
    row.set("safe_mono", SafeMonoMode::current().label());
    row.set("mut_facts", MutFactsMode::current().label());
    row.set("z3_full_version", z3::full_version().to_string());
    row.set("smt_seed", 0);
    row.set("sat_seed", 0);
    row.set("funnel_s0", counts.s0);
    row.set("funnel_s1", counts.s1);
    row.set("funnel_s2", counts.s2);
    row.set("funnel_s3", counts.s3);
    row.set("funnel_s4", counts.s4);
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

fn usize_field(row: &Row, key: &str) -> usize {
    row.get(key)
        .unwrap_or_else(|| panic!("A12 funnel row lacks {key}: {row:?}"))
        .parse()
        .unwrap_or_else(|error| panic!("A12 funnel row has invalid {key}: {error}"))
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
                *counts
                    .entry(("S1->S2".to_owned(), family.to_owned()))
                    .or_default() += 1;
            }
        } else if fields[s3_i] == "0" {
            for family in fields[s3_core_i].split(',') {
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
    assert_eq!(
        std::env::var("CRAT_BO_COPY_LEND_MODE").as_deref(),
        Ok("lend_arm")
    );
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
