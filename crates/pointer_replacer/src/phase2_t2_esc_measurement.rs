//! Phase-2 T2 + ESC-GAP ②-minimal acceptance batch.
//!
//! Test-only measurement code. The worker wraps the production A5 model solve with the existing
//! selector/export observers; the orchestrator runs one serialized rs-crown configuration and
//! compares only against the accepted landed artifacts supplied as comparison targets.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Duration,
};

use rustc_middle::{mir::Local, ty::TyCtxt};
use sha2::{Digest, Sha256};

use super::{CORPUS, orchestrate, report};
use crate::{
    analyses::borrow_ownership::{
        construction::VerifiedBo,
        crate_slots::CrateSlots,
        esc_minimal,
        export::{BoExport, BoundaryRole, SelectorSite},
        l2::SlotKey,
        solver::{SelectorTrace, SelectorTraceOutcome, SelectorTracePhase, SlotRef},
    },
    utils::rustc::RustProgram,
};

const DERIVED_DIGEST: &str = "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";
const OFFICIAL_DIGEST: &str = "7aa16d5b63ff39e6aaabd3590ec2be9c88c9d8a753bd9f74cd4e6056d9974fd7";
const C080_REPIN_RECEIPT_SHA256: &str =
    "d130ade6780caa7755ffd079c8763cee0a5f9db18c10f24d168aa04d2672d8c7";

fn number(row: &report::Row, key: &str) -> usize {
    row.get(key)
        .unwrap_or_else(|| panic!("phase-2 row lacks {key}"))
        .parse()
        .unwrap_or_else(|error| panic!("phase-2 row {key} is not numeric: {error}"))
}

fn slot_label(slot: SlotRef) -> String {
    let key = SlotKey::of(slot);
    match key.variant {
        0 => format!("field:{}:{}", key.owner, key.slot),
        1 => format!("local:{}:{}", key.owner, key.slot),
        other => panic!("unexpected SlotKey variant {other}"),
    }
}

fn endpoint_slot(
    slots: &CrateSlots,
    export: &BoExport,
    site: &SelectorSite,
) -> Result<SlotRef, String> {
    let call = site.call.as_ref().ok_or_else(|| {
        format!(
            "selector {:?}/{:?} lacks call identity",
            site.role, site.var
        )
    })?;
    let mut locals = export
        .version_sites
        .iter()
        .filter(|row| row.fn_did == call.fn_did)
        .filter(|row| match site.role {
            BoundaryRole::Source => row.def_var == Some(site.var),
            BoundaryRole::Sink => row.r#use_var == Some(site.var),
        })
        .map(|row| row.local)
        .collect::<BTreeSet<Local>>();
    if locals.len() != 1 {
        return Err(format!(
            "selector {:?} {}:{}:{}:{} var={:?} maps to {} locals: {locals:?}",
            site.role,
            call.function_path,
            call.location.block,
            call.location.statement_index,
            call.callee,
            site.var,
            locals.len(),
        ));
    }
    let local = locals.pop_first().expect("one endpoint local");
    let slot = slots
        .fn_local_slots
        .get(&call.fn_did)
        .and_then(|universe| universe.slot_for_local_depth(local, 0))
        .ok_or_else(|| {
            format!(
                "selector endpoint {}::{local:?}@d0 has no BO slot",
                call.function_path
            )
        })?;
    Ok(SlotRef::Local(call.fn_did, slot))
}

fn assume_sites(labels: &BTreeSet<String>) -> String {
    let mut sites = labels
        .iter()
        .filter_map(|label| {
            let rest = label.split_once("own-assume[")?.1;
            Some(rest.split_once(']')?.0.to_owned())
        })
        .collect::<BTreeSet<_>>();
    if labels.iter().any(|label| label.contains("link-own")) {
        sites.insert("link-own".to_owned());
    }
    sites.into_iter().collect::<Vec<_>>().join(";")
}

/// Add the T2/② observer artifacts to the existing production model worker. The observer is armed
/// only by `CRAT_PHASE2_T2_ESC_CAPTURE`; its inputs are the exact accepted model and construction
/// trace, and it cannot alter either.
pub(super) fn write_worker_artifacts(
    _tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    verified: &VerifiedBo,
    trace: &SelectorTrace,
    export: &BoExport,
    artifact_dir: &Path,
    row: &mut report::Row,
) {
    let source_count = verified.selector_sources;
    let sink_count = verified.selector_sinks;
    let endpoint_count = source_count + sink_count;
    assert!(
        export.source_sites.len() >= source_count && export.sink_sites.len() >= sink_count,
        "phase-2 selector export is shorter than the final construction"
    );
    let mut sites = export.source_sites[export.source_sites.len() - source_count..].to_vec();
    sites.extend_from_slice(&export.sink_sites[export.sink_sites.len() - sink_count..]);
    assert_eq!(sites.len(), endpoint_count);
    assert_eq!(trace.n_sources, source_count);
    assert_eq!(trace.total, endpoint_count);

    let rounds = verified.round_stats.rounds;
    assert!(rounds != 0 && trace.epochs.len() >= rounds);
    let final_epochs = &trace.epochs[trace.epochs.len() - rounds..];
    let final_epoch = final_epochs.last().expect("final T2 selector epoch");
    let final_dropped = final_epoch
        .final_dropped
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();

    let mut endpoint_tsv = String::from(
        "program\tindex\trole\tfunction\tblock\tstatement\tcallee\tvar\tslot\tfinal_kind\tstate\trestoration\tcore_labels\tlicense_classes\n",
    );
    let mut core_tsv = String::from(
        "program\tepoch\tindex\trole\tfunction\tblock\tstatement\tcallee\toutcome\tlicense_core\tassume_sites\tcore_labels\n",
    );
    let mut retained = 0usize;
    let mut retracted = 0usize;
    let mut core_events = 0usize;
    let mut license_core_events = 0usize;

    for (index, site) in sites.iter().enumerate() {
        let call = site.call.as_ref().expect("T2 endpoint call identity");
        let endpoint_slot = endpoint_slot(slots, export, site)
            .unwrap_or_else(|error| panic!("phase-2 endpoint mapping STOP: {error}"));
        let final_kind = verified
            .model
            .get(&endpoint_slot)
            .unwrap_or_else(|| panic!("T2 endpoint model lacks {endpoint_slot:?}"));
        let state = if final_dropped.contains(&index) {
            retracted += 1;
            "retracted"
        } else {
            retained += 1;
            "active"
        };
        let mut labels = BTreeSet::new();
        let mut restoration = "not-needed";
        for event in final_epochs
            .iter()
            .flat_map(|epoch| &epoch.events)
            .filter(|event| event.selector_index == index)
        {
            labels.extend(event.core_labels.iter().cloned());
            if event.phase == SelectorTracePhase::Reenable {
                restoration = match event.outcome {
                    SelectorTraceOutcome::Restored => "restored",
                    SelectorTraceOutcome::StayedDropped => "stayed-dropped",
                    SelectorTraceOutcome::Dropped => {
                        panic!("drop outcome recorded in restoration phase")
                    }
                };
            }
            if event.phase == SelectorTracePhase::Drop {
                core_events += 1;
                let event_labels = event.core_labels.iter().cloned().collect::<BTreeSet<_>>();
                let license_core = event_labels
                    .iter()
                    .any(|label| label.contains("own-assume") || label.contains("link-own"));
                license_core_events += usize::from(license_core);
                core_tsv.push_str(&format!(
                    "{}\t{}\t{}\t{:?}\t{}\t{}\t{}\t{}\t{:?}\t{}\t{}\t{}\n",
                    std::env::var("CRAT_BOC1_NAME").expect("program name"),
                    event.epoch,
                    index,
                    site.role,
                    call.function_path,
                    call.location.block,
                    call.location.statement_index,
                    call.callee,
                    event.outcome,
                    u8::from(license_core),
                    assume_sites(&event_labels),
                    event_labels.into_iter().collect::<Vec<_>>().join(" | "),
                ));
            }
        }
        endpoint_tsv.push_str(&format!(
            "{}\t{}\t{:?}\t{}\t{}\t{}\t{}\t{:?}\t{}\t{:?}\t{}\t{}\t{}\t{}\n",
            std::env::var("CRAT_BOC1_NAME").expect("program name"),
            index,
            site.role,
            call.function_path,
            call.location.block,
            call.location.statement_index,
            call.callee,
            site.var,
            slot_label(endpoint_slot),
            final_kind,
            state,
            restoration,
            labels.iter().cloned().collect::<Vec<_>>().join(" | "),
            assume_sites(&labels),
        ));
    }
    fs::write(artifact_dir.join("t2-endpoints.tsv"), endpoint_tsv)
        .expect("write phase-2 endpoint ledger");
    fs::write(artifact_dir.join("t2-core-events.tsv"), core_tsv)
        .expect("write phase-2 core ledger");

    let esc = esc_minimal::select(program, slots);
    let mut esc_tsv = String::from(
        "program\tfunction\tstore_block\tstore_statement\tresolved_origin_slot\tdestination_place\tsource_slot\tdestination_slot\tloan_location\tloan_borrowed\tloan_borrower\n",
    );
    for site in &esc.sites {
        esc_tsv.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}:{}\t{:?}\t{:?}\n",
            site.key.program,
            site.key.function,
            site.key.location.block,
            site.key.location.statement_index,
            site.key.resolved_origin_slot,
            site.key.destination_place,
            slot_label(site.rhs),
            slot_label(site.lhs),
            site.loan.location.block,
            site.loan.location.statement_index,
            site.loan.borrowed,
            site.loan.borrower,
        ));
    }
    fs::write(artifact_dir.join("esc-selected-sites.tsv"), esc_tsv)
        .expect("write phase-2 ESC ledger");

    row.set("t2_endpoints", endpoint_count);
    row.set("t2_sources", source_count);
    row.set("t2_sinks", sink_count);
    row.set("t2_active", retained);
    row.set("t2_retracted", retracted);
    row.set("t2_core_events", core_events);
    row.set("t1_unknown_origin_core_incidence", license_core_events);
    row.set("esc_selected_sites", esc.sites.len());
    row.set(
        "esc_selected_loans",
        esc.loans.values().map(|set| set.len()).sum::<usize>(),
    );
    row.set("esc_liveness_tripwire", "passed");
}

fn sha256(path: &Path) -> String {
    format!(
        "{:x}",
        Sha256::digest(
            fs::read(path).unwrap_or_else(|error| { panic!("hash {}: {error}", path.display()) })
        )
    )
}

fn parse_model(path: &Path) -> BTreeMap<String, String> {
    let input = fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("read model {}: {error}", path.display()));
    let mut lines = input.lines();
    assert_eq!(lines.next(), Some("variant\towner\tslot\tkind"));
    lines
        .map(|line| {
            let fields = line.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 4, "model row width: {line}");
            let prefix = match fields[0] {
                "0" => "field",
                "1" => "local",
                other => panic!("model variant {other}"),
            };
            (
                format!("{prefix}:{}:{}", fields[1], fields[2]),
                fields[3].to_owned(),
            )
        })
        .collect()
}

fn projection_counts(path: &Path) -> (usize, usize) {
    let input = fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("read projection {}: {error}", path.display()));
    let mut lines = input.lines();
    assert!(
        lines
            .next()
            .is_some_and(|header| header.starts_with("declaration_key\tmapping\toutcome\t"))
    );
    let mut total = 0;
    let mut safe = 0;
    for line in lines {
        let fields = line.split('\t').collect::<Vec<_>>();
        assert_eq!(fields.len(), 9);
        total += 1;
        safe += usize::from(matches!(
            fields[2],
            "predicted-eliminated-ref-backed" | "predicted-eliminated-owning-backed"
        ));
    }
    (total, safe)
}

fn endpoint_owning_regressed(baseline: &str, phase2: &str) -> bool {
    baseline == "Owning" && phase2 != "Owning"
}

#[test]
fn reframed_t2_gate_rejects_only_an_owning_regression() {
    assert!(!endpoint_owning_regressed("Owning", "Owning"));
    assert!(endpoint_owning_regressed("Owning", "Raw"));
    assert!(endpoint_owning_regressed("Owning", "Ref"));
    assert!(!endpoint_owning_regressed("Raw", "Ref"));
    assert!(!endpoint_owning_regressed("Ref", "Raw"));
}

fn table_rows(path: &Path, header_prefix: &str, key_columns: usize) -> BTreeMap<String, String> {
    let input = fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("read table {}: {error}", path.display()));
    let mut saw_header = false;
    let mut rows = BTreeMap::new();
    for line in input.lines() {
        if !saw_header {
            if line.starts_with(header_prefix) {
                saw_header = true;
            }
            continue;
        }
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        assert!(fields.len() >= key_columns, "short table row: {line}");
        let key = fields[..key_columns].join("|");
        assert!(
            rows.insert(key, line.to_owned()).is_none(),
            "duplicate table key"
        );
    }
    assert!(saw_header, "missing table header in {}", path.display());
    rows
}

fn append_table_deltas(
    output: &mut String,
    program: &str,
    family: &str,
    baseline: &Path,
    current: &Path,
    header: &str,
    key_columns: usize,
) -> usize {
    let old = table_rows(baseline, header, key_columns);
    let new = table_rows(current, header, key_columns);
    let keys = old
        .keys()
        .chain(new.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut changed = 0;
    for key in keys {
        let left = old.get(&key);
        let right = new.get(&key);
        if left == right {
            continue;
        }
        changed += 1;
        let class = right
            .or(left)
            .and_then(|line| line.split('\t').nth(4))
            .unwrap_or("-");
        output.push_str(&format!(
            "{program}\t{family}\t{class}\t{key}\t{}\t{}\n",
            left.map_or("<absent>".to_owned(), |line| line.replace('\t', " | ")),
            right.map_or("<absent>".to_owned(), |line| line.replace('\t', " | ")),
        ));
    }
    changed
}

#[test]
#[ignore = "Phase-2 serialized T2 + ESC-GAP ②-minimal rs-crown batch"]
fn phase2_t2_esc_batch_corpus() {
    assert_eq!(
        std::env::var("CRAT_BOC1_SUBSTRATE").as_deref(),
        Ok("derived")
    );
    assert_eq!(std::env::var("CRAT_BOC1_MEM_MB").as_deref(), Ok("49152"));
    assert_eq!(
        std::env::var("CRAT_BOC1_TIMEOUT_SECS").as_deref(),
        Ok("14400")
    );
    assert_eq!(CORPUS.len(), 20);

    let root = orchestrate::workspace_root();
    let output = orchestrate::out_dir().join("phase2-t2-esc-batch");
    fs::create_dir_all(&output).expect("create phase-2 output");
    let snapshot = PathBuf::from(
        std::env::var_os("CRAT_A5_SNAPSHOT").expect("phase-2 batch requires A5 snapshot"),
    );
    let baseline = PathBuf::from(
        std::env::var_os("CRAT_PHASE2_BASELINE_ROOT")
            .expect("phase-2 batch requires comparison target"),
    );
    let ownlost = PathBuf::from(
        std::env::var_os("CRAT_PHASE2_OWNLOST_LEDGER")
            .expect("phase-2 batch requires LIC-P1 OwnLost ledger"),
    );
    assert!(snapshot.is_dir() && baseline.is_dir() && ownlost.is_file());
    let baseline_repin = baseline.join("repin-receipt.txt");
    assert_eq!(
        sha256(&baseline_repin),
        C080_REPIN_RECEIPT_SHA256,
        "phase-2 baseline target must carry the c080 repin receipt"
    );
    let baseline_repin_text = fs::read_to_string(&baseline_repin).expect("read c080 repin receipt");
    assert!(baseline_repin_text.contains("analysis_head=c080e9e7\n"));
    assert!(baseline_repin_text.contains("spot_semantic_artifacts=33/33\n"));

    let official_link = root.join("benchmarks/rs-crown-transformed/evaluation.tsv");
    let official_target = fs::read_link(&official_link).expect("official artifact symlink");
    assert!(official_target.is_absolute());
    assert_eq!(sha256(&official_link), OFFICIAL_DIGEST);
    let official_root = official_target.parent().expect("official root");
    fs::write(
        output.join("preflight-receipt.txt"),
        format!(
            "status=ready\ndata=false\nanalysis_head={}\ncorpus=rs-crown\nprograms=20\nmode=phase2-t2-esc\na5_mode=precise_replay\na5_world=closed_world_frozen_graph\na5_abi_guard=permitted:measurement-frozen-graph-attested\ncopy_lend_mode=baseline\na2_mode=off\nderived_substrate_sha256={DERIVED_DIGEST}\nofficial_evaluation_sha256={OFFICIAL_DIGEST}\nbaseline_target={}\nbaseline_target_frame=c080e9e7\nbaseline_repin_receipt_sha256={C080_REPIN_RECEIPT_SHA256}\nownlost_ledger={}\n",
            orchestrate::git_sha(),
            baseline.display(),
            ownlost.display(),
        ),
    )
    .expect("write phase-2 preflight receipt");

    let timeout = Duration::from_secs(14_400);
    let mut rows = Vec::new();
    for program in CORPUS {
        let input = program.input_path(&root);
        let shard = output.join(program.name);
        fs::create_dir_all(&shard).expect("create phase-2 shard");
        let common = vec![
            (
                "CRAT_BO_A5_ATTESTATION",
                "frozen_benchmark_graph".to_owned(),
            ),
            ("CRAT_BO_A2_MODE", "off".to_owned()),
            ("CRAT_BO_REPAIR", "mode_a".to_owned()),
            ("CRAT_PHASE2_T2_ESC_CAPTURE", "1".to_owned()),
            ("CRAT_A5_SNAPSHOT", snapshot.display().to_string()),
            ("CRAT_A5_BATCH_SHARD_DIR", shard.display().to_string()),
            (
                "CRAT_BOC1_PROJECTION_SNAPSHOT",
                shard.join("model-projection.tsv").display().to_string(),
            ),
            (
                "CRAT_BOC1_CROWN_ARTIFACT",
                official_root.display().to_string(),
            ),
            (
                "CRAT_A5_OFFICIAL_EVALUATION",
                official_link.display().to_string(),
            ),
            (
                "CRAT_A5_OFFICIAL_EVALUATION_SHA256",
                OFFICIAL_DIGEST.to_owned(),
            ),
        ];
        eprintln!("[phase2] {}/model", program.name);
        let model = orchestrate::run_child_labeled(
            program.name,
            &input,
            "a5-batch-model",
            "phase2-model",
            timeout,
            &common,
        );
        let model_row = model.row.clone().unwrap_or_default();
        if model.status != "ok" || model_row.get("status") != Some("ok") {
            fs::write(
                output.join("receipt.txt"),
                format!(
                    "status=failed\ndata=false\nprogram={}\nphase=model\nchild_status={}\nnote={}\n",
                    program.name, model.status, model.note
                ),
            )
            .expect("write phase-2 failure receipt");
            panic!("phase-2 STOP: {}/model: {}", program.name, model.note);
        }
        eprintln!("[phase2] {}/rewriter", program.name);
        let rewrite = orchestrate::run_child_labeled(
            program.name,
            &input,
            "m1-emit",
            "phase2-rewriter",
            timeout,
            &common,
        );
        let rewrite_row = rewrite.row.clone().unwrap_or_default();
        if rewrite.status != "ok" || rewrite_row.get("status") != Some("ok") {
            fs::write(
                output.join("receipt.txt"),
                format!(
                    "status=failed\ndata=false\nprogram={}\nphase=rewriter\nchild_status={}\nnote={}\n",
                    program.name, rewrite.status, rewrite.note
                ),
            )
            .expect("write phase-2 failure receipt");
            panic!("phase-2 STOP: {}/rewriter: {}", program.name, rewrite.note);
        }
        let mut combined = model_row;
        combined.set("program", program.name);
        combined.set("model_wall_s", format!("{:.3}", model.wall_s));
        combined.set("model_peak_rss_kb", model.peak_rss_kb);
        for (key, value) in &rewrite_row.0 {
            combined.set(&format!("rw_{key}"), value);
        }
        rows.push(combined);
        fs::write(output.join("per-program.csv"), report::render_csv(&rows))
            .expect("write phase-2 partial table");
        fs::write(
            output.join("partial-receipt.txt"),
            format!(
                "status=running\ndata=false\ncompleted={}/20\nlast_program={}\n",
                rows.len(),
                program.name,
            ),
        )
        .expect("write phase-2 partial receipt");
    }
    assert_eq!(rows.len(), 20);
    assert_eq!(sha256(&official_link), OFFICIAL_DIGEST);

    let mut movement = String::from("program\tslot\tbaseline_kind\tphase2_kind\tmovement\n");
    let mut pair_deltas =
        String::from("program\tfamily\tclass\tidentity\tbaseline_row\tphase2_row\n");
    let mut total_ref = 0usize;
    let mut total_raw = 0usize;
    let mut total_own = 0usize;
    let mut old_ref = 0usize;
    let mut old_raw = 0usize;
    let mut old_own = 0usize;
    let mut official_den = 0usize;
    let mut official_before = 0usize;
    let mut official_after = 0usize;
    let mut esc_sites = 0usize;
    let mut endpoints = 0usize;
    let mut retracted = 0usize;
    let mut t1_cores = 0usize;
    let mut model_wall = 0.0f64;
    let mut optimize_wall = 0.0f64;
    let mut objective_checks = 0usize;
    let mut lazy_plain_hard_checks = 0usize;
    let mut lazy_tracked_rechecks = 0usize;
    let mut lazy_plain_materializations = 0usize;
    let mut changed_pairs = 0usize;
    let mut baseline_models = BTreeMap::new();
    let mut phase2_models = BTreeMap::new();
    for row in &rows {
        let program = row.get("program").expect("program row");
        total_ref += number(row, "n_ref");
        total_raw += number(row, "n_raw");
        total_own += number(row, "n_own");
        esc_sites += number(row, "esc_selected_sites");
        endpoints += number(row, "t2_endpoints");
        retracted += number(row, "t2_retracted");
        t1_cores += number(row, "t1_unknown_origin_core_incidence");
        model_wall += row
            .get("model_wall_s")
            .expect("model wall")
            .parse::<f64>()
            .expect("numeric model wall");
        optimize_wall += row
            .get("t_optimize_materialization_s")
            .expect("objective wall")
            .parse::<f64>()
            .expect("numeric objective wall");
        objective_checks += number(row, "optimize_materialization_count");
        lazy_plain_hard_checks += number(row, "lazy_plain_hard_check_count");
        lazy_tracked_rechecks += number(row, "lazy_tracked_recheck_count");
        lazy_plain_materializations += number(row, "lazy_plain_materialization_count");

        let old_dir = baseline.join(program);
        let new_dir = output.join(program);
        let old_model = parse_model(&old_dir.join("model.tsv"));
        let new_model = parse_model(&new_dir.join("model.tsv"));
        assert_eq!(
            old_model.keys().collect::<Vec<_>>(),
            new_model.keys().collect::<Vec<_>>()
        );
        old_ref += old_model
            .values()
            .filter(|kind| kind.as_str() == "Ref")
            .count();
        old_raw += old_model
            .values()
            .filter(|kind| kind.as_str() == "Raw")
            .count();
        old_own += old_model
            .values()
            .filter(|kind| kind.as_str() == "Owning")
            .count();
        for (slot, old_kind) in &old_model {
            let new_kind = &new_model[slot];
            if old_kind != new_kind {
                movement.push_str(&format!(
                    "{program}\t{slot}\t{old_kind}\t{new_kind}\t{old_kind}->{new_kind}\n"
                ));
            }
        }
        let (old_den, old_safe) = projection_counts(&old_dir.join("model-projection.tsv"));
        let (new_den, new_safe) = projection_counts(&new_dir.join("model-projection.tsv"));
        assert_eq!(old_den, new_den);
        official_den += new_den;
        official_before += old_safe;
        official_after += new_safe;

        changed_pairs += append_table_deltas(
            &mut pair_deltas,
            program,
            "w14-pair",
            &old_dir.join("w14-pair-ledger.tsv"),
            &new_dir.join("w14-pair-ledger.tsv"),
            "program\tsite\t",
            8,
        );
        changed_pairs += append_table_deltas(
            &mut pair_deltas,
            program,
            "mark",
            &old_dir.join("marks.tsv"),
            &new_dir.join("marks.tsv"),
            "caller\tblock\t",
            6,
        );
        assert!(
            baseline_models
                .insert(program.to_owned(), old_model)
                .is_none()
        );
        assert!(
            phase2_models
                .insert(program.to_owned(), new_model)
                .is_none()
        );
    }
    assert_eq!((old_ref, old_raw, old_own), (48_901, 10_458, 239));
    assert_eq!((official_before, official_den), (1_609, 2_414));
    assert_eq!(esc_sites, 36, "② exact allowlist join");
    fs::write(output.join("model-movement.tsv"), &movement).expect("write movement ledger");
    fs::write(output.join("a5-pair-mark-deltas.tsv"), &pair_deltas).expect("write A5 delta ledger");

    let ownlost_input = fs::read_to_string(&ownlost).expect("read OwnLost ledger");
    let mut endpoint_states = BTreeMap::<(String, String), BTreeSet<String>>::new();
    let mut endpoint_slots = BTreeSet::<(String, String)>::new();
    for program in CORPUS {
        let endpoint_input = fs::read_to_string(output.join(program.name).join("t2-endpoints.tsv"))
            .expect("read per-program T2 endpoints");
        for line in endpoint_input.lines().skip(1) {
            let fields = line.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 14, "T2 endpoint row width");
            endpoint_states
                .entry((fields[0].to_owned(), fields[8].to_owned()))
                .or_default()
                .insert(fields[10].to_owned());
            endpoint_slots.insert((fields[0].to_owned(), fields[8].to_owned()));
        }
    }
    let mut endpoint_gate = String::from(
        "program\tslot\tbaseline_kind\tphase2_kind\tbaseline_owning\tregressed\tendpoint_states\n",
    );
    let mut endpoint_baseline_owning = 0usize;
    let mut endpoint_regressions = 0usize;
    for (program, slot) in &endpoint_slots {
        let baseline_kind = &baseline_models[program][slot];
        let phase2_kind = &phase2_models[program][slot];
        let baseline_owning = baseline_kind == "Owning";
        let regressed = endpoint_owning_regressed(baseline_kind, phase2_kind);
        endpoint_baseline_owning += usize::from(baseline_owning);
        endpoint_regressions += usize::from(regressed);
        endpoint_gate.push_str(&format!(
            "{program}\t{slot}\t{baseline_kind}\t{phase2_kind}\t{}\t{}\t{}\n",
            u8::from(baseline_owning),
            u8::from(regressed),
            endpoint_states[&(program.clone(), slot.clone())]
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .join(";"),
        ));
    }
    fs::write(output.join("endpoint-no-regression.tsv"), endpoint_gate)
        .expect("write endpoint no-regression gate");
    let mut ownlost_join = String::from(
        "program\tslot\tidentity\tpartner_free\tbaseline_kind\tphase2_kind\tflip_to_owning\towning_regression\tdirect_endpoint_state\n",
    );
    let mut ownlost_rows = 0usize;
    let mut ownlost_flips = 0usize;
    let mut ownlost_retractions = 0usize;
    let mut ownlost_baseline_owning = 0usize;
    let mut ownlost_regressions = 0usize;
    for line in ownlost_input.lines().skip(1) {
        let fields = line.split('\t').collect::<Vec<_>>();
        assert!(fields.len() >= 4);
        let program = fields[0];
        let slot = fields[1];
        let old_kind = baseline_models[program]
            .get(slot)
            .unwrap_or_else(|| panic!("OwnLost baseline lacks {slot}"));
        let new_kind = phase2_models[program]
            .get(slot)
            .unwrap_or_else(|| panic!("OwnLost phase2 lacks {slot}"));
        let flipped = old_kind != "Owning" && new_kind == "Owning";
        let regressed = endpoint_owning_regressed(old_kind, new_kind);
        let endpoint_state = endpoint_states
            .get(&(program.to_owned(), slot.to_owned()))
            .map(|states| states.iter().cloned().collect::<Vec<_>>().join(";"))
            .unwrap_or_else(|| "chain-middle".to_owned());
        ownlost_retractions +=
            usize::from(endpoint_state.split(';').any(|state| state == "retracted"));
        ownlost_flips += usize::from(flipped);
        ownlost_baseline_owning += usize::from(old_kind == "Owning");
        ownlost_regressions += usize::from(regressed);
        ownlost_rows += 1;
        ownlost_join.push_str(&format!(
            "{program}\t{slot}\t{}\t{}\t{old_kind}\t{new_kind}\t{}\t{}\t{endpoint_state}\n",
            fields[2],
            fields[3],
            u8::from(flipped),
            u8::from(regressed),
        ));
    }
    assert_eq!(ownlost_rows, 114, "LIC-P1 OwnLost join population");
    fs::write(output.join("ownlost-join.tsv"), &ownlost_join).expect("write OwnLost join");

    let movement_rows = movement.lines().count().saturating_sub(1);
    let expected = ownlost_baseline_owning == ownlost_rows
        && ownlost_regressions == 0
        && endpoint_regressions == 0;
    fs::write(
        output.join("aggregate.tsv"),
        format!(
            "metric\tbaseline\tphase2\tdelta\nRef\t{old_ref}\t{total_ref}\t{}\nRaw\t{old_raw}\t{total_raw}\t{}\nOwning\t{old_own}\t{total_own}\t{}\nofficial\t{official_before}\t{official_after}\t{}\nofficial_denominator\t{official_den}\t{official_den}\t0\n",
            total_ref as isize - old_ref as isize,
            total_raw as isize - old_raw as isize,
            total_own as isize - old_own as isize,
            official_after as isize - official_before as isize,
        ),
    )
    .expect("write phase-2 aggregate");
    fs::write(
        output.join("receipt.txt"),
        format!(
            "status=complete\ndata={}\nanalysis_head={}\ncorpus=rs-crown\nprograms=20/20\nmode=phase2-t2-esc\na5_mode=precise_replay\na5_world=closed_world_frozen_graph\na5_abi_guard=permitted:measurement-frozen-graph-attested\ncopy_lend_mode=baseline\na2_mode=off\nderived_substrate_sha256={DERIVED_DIGEST}\nofficial_evaluation_sha256={OFFICIAL_DIGEST}\nmodel_movement_rows={movement_rows}\nownlost_rows={ownlost_rows}\nownlost_flips_observed={ownlost_flips}\nownlost_direct_retractions={ownlost_retractions}\nownlost_baseline_owning={ownlost_baseline_owning}\nownlost_owning_regressions={ownlost_regressions}\nendpoint_slots={}\nendpoint_baseline_owning={endpoint_baseline_owning}\nendpoint_owning_regressions={endpoint_regressions}\nt2_endpoints={endpoints}\nt2_retracted_global={retracted}\nt1_unknown_origin_core_incidence={t1_cores}\nesc_selected_sites={esc_sites}\na5_changed_pair_mark_rows={changed_pairs}\nobjective_bearing_checks={objective_checks}\nobjective_model_wall_s={optimize_wall:.3}\nlazy_plain_hard_checks={lazy_plain_hard_checks}\nlazy_tracked_rechecks={lazy_tracked_rechecks}\nlazy_plain_materializations={lazy_plain_materializations}\nworker_model_wall_s={model_wall:.3}\nrn1_matched19_baseline_wall_s=212.147\nreframed_no_owning_regression={}\n",
            if expected { "true" } else { "false" },
            orchestrate::git_sha(),
            endpoint_slots.len(),
            if expected { "passed" } else { "deviation-needs-analysis" },
        ),
    )
    .expect("write phase-2 receipt");
    assert!(
        expected,
        "phase-2 no-Own-regression deviation: OwnLost baseline-own={ownlost_baseline_owning}/{ownlost_rows} regressions={ownlost_regressions}; endpoint baseline-own={endpoint_baseline_owning}/{} regressions={endpoint_regressions}; observed flips={ownlost_flips}; row-level artifacts preserved",
        endpoint_slots.len(),
    );
}
