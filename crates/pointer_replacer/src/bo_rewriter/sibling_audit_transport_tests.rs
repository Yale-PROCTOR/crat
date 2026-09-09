//! R236 all-coverage transport controls over the accepted capture fixture.

use std::collections::{BTreeMap, BTreeSet};

use sha2::{Digest, Sha256};

use super::{
    CensusOutcomeKind,
    bridge_custody_export::{
        self as custody, CheckpointReport, Export, ReplayFrame, RetainedReplay,
    },
    bridge_receipt::BridgeReceiptEvent,
    decision::raw_boundary::site_atom_id,
    sibling_audit::Outcome,
};

const INPUT: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub struct Holder { data: *mut i32 }\n\
    pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
    pub unsafe fn caller(holder: *const Holder, src: *const i32) { update((*holder).data, src); }\n\
    pub unsafe fn entry() { let mut value = 1; let holder = Holder { data: &mut value }; caller(&holder, &value); }\n";

struct Captured {
    export: Export,
    events: Vec<BridgeReceiptEvent>,
    sources: BTreeMap<String, String>,
    expected_ids: BTreeSet<String>,
    comparison: CheckpointReport,
}

fn captured() -> Captured {
    let (export, events, sources, expected_ids, expected_count, solve) =
        ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
            let ast_capture =
                super::ast_transform::capture_ast(tcx).expect("accepted fixture AST capture");
            let (table, context) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    super::A5Mode::PreciseReplay,
                    Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("accepted fixture test-harness decisions");
            // Independent expectation: this reads the table's original coverage
            // universe, never the audit producer's rows or pending-only subset.
            let expected_ids = table
                .sibling_overlap_inventory
                .coverage
                .iter()
                .map(|coverage| site_atom_id(&coverage.potential.site))
                .collect::<BTreeSet<_>>();
            let expected_count = table.sibling_overlap_inventory.coverage.len();
            assert!(
                !expected_ids.is_empty(),
                "actual all-coverage inventory must be nonempty"
            );
            assert_eq!(
                expected_ids.len(),
                expected_count,
                "fixture coverage identities must be unique"
            );
            let original_files = tcx
                .sess
                .source_map()
                .files()
                .iter()
                .filter_map(|file| {
                    let key = super::file_key(&file.name)?;
                    Some((key, file.src.as_ref()?.to_string()))
                })
                .collect::<BTreeMap<_, _>>();
            let emission = super::emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &context.retained_c9_plans,
            )
            .expect("accepted fixture emission plan");
            let held = emission.plan.held_classes();
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
                &held,
                &BTreeSet::new(),
                &table,
            )
            .expect("accepted fixture reverts");
            let (files, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx,
                &ast_capture,
                &reverts,
                emission.plan.root_file.as_ref(),
                &table,
                Some(&emission.plan.terminal_call_plans),
            )
            .expect("accepted fixture AST emission");
            let planned_rows = emission
                .plan
                .sibling_audit_rows_with_atoms(&BTreeSet::new(), &BTreeSet::new());
            let export =
                custody::capture(tcx, &ast_capture, &table, &emission.plan, &original_files);
            let audit = export
                .sibling_audit
                .as_ref()
                .expect("actual audit capture must be present");
            assert_eq!(
                audit.expected_coverage_ids, expected_ids,
                "capture expectations must come from the independent table universe"
            );
            assert_eq!(audit.rows, planned_rows, "actual rows must come from Plan");
            let events = emission.plan.bridge_events(&BTreeSet::new());
            let sources = files
                .into_iter()
                .map(|(file, source)| (custody::file_label(&file), source))
                .collect::<BTreeMap<_, _>>();
            (
                export,
                events,
                sources,
                expected_ids,
                expected_count,
                super::model_cache::solve_receipt(),
            )
        })
        .expect("accepted fixture compiler callback");
    assert!(
        solve.is_some(),
        "ordinary fixture evidence must retain its actual solve receipt"
    );
    println!("R236 audit-transport fixture solve receipt: {solve:#?}");
    assert!(
        super::verify::type_checks_str(&sources["main.rs"]),
        "accepted emitted fixture compiles"
    );
    let audit = export
        .sibling_audit
        .as_ref()
        .expect("owned audit transport exists");
    assert_eq!(audit.rows.len(), expected_count);
    assert_eq!(
        audit
            .rows
            .iter()
            .map(|row| row.coverage_id.clone())
            .collect::<BTreeSet<_>>(),
        expected_ids
    );
    assert!(
        audit
            .rows
            .iter()
            .all(|row| row.data && row.issues.is_empty()),
        "completed captured outcomes, including Undeterminable, are data: {audit:#?}"
    );
    assert!(
        audit
            .rows
            .iter()
            .any(|row| !matches!(row.outcome, Outcome::PendingWaiver | Outcome::CoverageGap)),
        "the audit must include a real nonpending site"
    );
    let comparison =
        custody::compare_capture(&export, &events, Some(&sources), CensusOutcomeKind::Emitted);
    assert!(
        comparison.data,
        "baseline actual capture must reconcile: {comparison:#?}"
    );
    assert!(
        !comparison.applied_receipts.is_empty(),
        "the real raw-view receipt must survive"
    );
    Captured {
        export,
        events,
        sources,
        expected_ids,
        comparison,
    }
}

fn remove_nonpending_row(export: &mut Export) -> String {
    let audit = export
        .sibling_audit
        .as_mut()
        .expect("present audit before deliberate-fault check");
    let index = audit
        .rows
        .iter()
        .position(|row| !matches!(row.outcome, Outcome::PendingWaiver | Outcome::CoverageGap))
        .expect("actual nonpending audit row");
    let removed = audit.rows.remove(index).coverage_id;
    assert!(
        audit.expected_coverage_ids.contains(&removed),
        "the independent expected identity must survive row removal"
    );
    removed
}

fn assert_bridge_export_unchanged(before: &Export, after: &Export) {
    let mut before = before.clone();
    let mut after = after.clone();
    before.sibling_audit = None;
    after.sibling_audit = None;
    assert_eq!(
        before, after,
        "the deliberate-fault check changes only audit transport"
    );
}

fn assert_missing_row_caught(report: &CheckpointReport, missing: &str) {
    assert!(
        !report.data,
        "missing all-coverage audit row must be caught: {report:#?}"
    );
    assert!(
        report
            .issues
            .iter()
            .any(|issue| issue.contains("sibling-audit") && issue.contains(missing)),
        "the missing independent identity needs an attributed audit issue: {missing}; {report:#?}"
    );
}

#[test]
fn sibling_audit_transport_actual_capture_retains_every_coverage_identity() {
    let capture = captured();
    let encoded = serde_json::to_vec(&capture.export).expect("owned capture serializes");
    let decoded: Export = serde_json::from_slice(&encoded).expect("owned capture deserializes");
    assert_eq!(decoded, capture.export);
    assert_eq!(
        decoded
            .sibling_audit
            .as_ref()
            .unwrap()
            .expected_coverage_ids,
        capture.expected_ids
    );
    let report = custody::compare_capture(
        &decoded,
        &capture.events,
        Some(&capture.sources),
        CensusOutcomeKind::Emitted,
    );
    assert_eq!(
        report, capture.comparison,
        "serialized audit transport preserves actual custody"
    );
}

#[test]
fn sibling_audit_transport_removed_nonpending_row_is_caught_by_capture_comparison() {
    let capture = captured();
    let mut changed = capture.export.clone();
    let missing = remove_nonpending_row(&mut changed);
    assert_bridge_export_unchanged(&capture.export, &changed);
    assert_eq!(
        changed
            .sibling_audit
            .as_ref()
            .unwrap()
            .expected_coverage_ids,
        capture.expected_ids
    );
    let report = custody::compare_capture(
        &changed,
        &capture.events,
        Some(&capture.sources),
        CensusOutcomeKind::Emitted,
    );
    assert_missing_row_caught(&report, &missing);
}

fn digest(value: &impl serde::Serialize) -> String {
    format!(
        "{:x}",
        Sha256::digest(serde_json::to_vec(value).expect("fixture frame serialization"))
    )
}

#[test]
fn sibling_audit_transport_reaggregate_rechecks_rows_despite_saved_success() {
    let capture = captured();
    // These metadata labels identify a constructed consumer-test frame, not a
    // corpus launch. Original/emitted byte maps below are the actual capture.
    let frame = ReplayFrame {
        program: "fixture:sibling-audit-transport".into(),
        analysis_frame: "fixture:ordinary-model-harness".into(),
        code_frame: "fixture:r236-transport-control".into(),
        input_tree_sha256: digest(&capture.export.files),
        emitted_tree_sha256: digest(&capture.sources),
        cache_manifest_sha256: digest(&"fixture:no-corpus-cache-manifest"),
        launch_env_sha256: digest(&"fixture:ordinary-test-harness"),
    };
    let mut retained = RetainedReplay {
        frame: frame.clone(),
        export: capture.export.clone(),
        applied: custody::applied_receipts(&capture.events),
        emitted_sources: Some(capture.sources.clone()),
        emitted_outcome: true,
        comparison: capture.comparison.clone(),
    };
    assert_eq!(
        custody::compare_retained(Some(&retained), &frame).expect("unmodified retained replay"),
        capture.comparison
    );
    let missing = remove_nonpending_row(&mut retained.export);
    assert_bridge_export_unchanged(&capture.export, &retained.export);
    assert_eq!(retained.applied, custody::applied_receipts(&capture.events));
    assert_eq!(retained.emitted_sources.as_ref(), Some(&capture.sources));
    assert_eq!(
        retained.comparison, capture.comparison,
        "saved success is deliberately unchanged"
    );
    match custody::compare_retained(Some(&retained), &frame) {
        Ok(report) => assert_missing_row_caught(&report, &missing),
        Err(reason) => assert!(
            reason.contains("sibling-audit") && reason.contains(&missing),
            "reaggregate must attribute the missing audit identity: {reason}"
        ),
    }
}

fn assert_missing_capture(absent: bool) {
    let capture = captured();
    let mut changed = capture.export.clone();
    if absent {
        changed.sibling_audit = None;
    } else {
        changed.sibling_audit.as_mut().unwrap().rows.clear();
    }
    assert_bridge_export_unchanged(&capture.export, &changed);
    let report = custody::compare_capture(
        &changed,
        &capture.events,
        Some(&capture.sources),
        CensusOutcomeKind::Emitted,
    );
    assert!(
        !report.data,
        "absent={absent}: missing audit capture cannot be interpreted as zero coverage"
    );
    assert!(
        report
            .issues
            .iter()
            .any(|issue| issue.contains("sibling-audit")),
        "absent={absent}: missing audit capture needs a typed issue: {report:#?}"
    );
    if !absent {
        assert_eq!(
            changed
                .sibling_audit
                .as_ref()
                .unwrap()
                .expected_coverage_ids,
            capture.expected_ids
        );
    }
}

#[test]
fn sibling_audit_transport_absent_capture_is_not_zero_coverage() {
    assert_missing_capture(true);
}

#[test]
fn sibling_audit_transport_empty_rows_are_not_zero_coverage() {
    assert_missing_capture(false);
}
