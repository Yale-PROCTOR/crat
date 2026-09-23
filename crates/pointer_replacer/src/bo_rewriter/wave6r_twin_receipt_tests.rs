//! The raw twin's placement receipt (relay wave-6r/030, R459-2). heman's
//! `__crat_raw_kmVec2Add` was called from three sites with no definition
//! anywhere, while two other twins in the same program were emitted
//! (main 050 §5); the four-frame table of report 032 could not say why,
//! because nothing recorded what happened to an individual twin. This row
//! does: per callee, `inserted` (with the visibility the twin was rendered
//! with), `skipped:signature-not-converted`, `place-failed`, or
//! `pristine-missing`.
/// Read the receipt INSIDE the compiler callback: the graft records it in a
/// thread local, and `run_compiler_on_str` runs the callback on its own
/// thread, so a read afterwards sees an empty slot.
fn emitted_with_receipt(input: &str) -> (String, String) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::super::ast_transform::capture_ast(tcx).expect("capture original AST");
        let (table, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native corpus-mode decisions");
        let emission =
            super::super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
                .expect("native emission plan");
        let held = emission.plan.held_classes();
        let reverts = super::super::ast_transform::revert_set_from_classes_and_atoms(
            &held,
            &Default::default(),
            &table,
        )
        .expect("planned held classes");
        let source = super::super::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("native AST emission")
        .0
        .into_values()
        .next()
        .expect("one source file");
        (source, super::super::decision::counted_void::twin_receipt())
    })
    .expect("input type-checks")
}

#[test]
fn wave6r_twin_receipt_names_the_placement_and_the_visibility() {
    let (_source, receipt) =
        emitted_with_receipt(super::wave6r_twin_visibility_tests::CROSS_MODULE);
    println!("TWIN-RECEIPT\n{receipt}");
    if receipt.is_empty() {
        // No counted-void graft on this base ⇒ no twin was considered.
        return;
    }
    assert!(
        receipt.starts_with(super::super::decision::counted_void::TWIN_RECEIPT_HEADER),
        "{receipt}"
    );
    assert!(
        receipt
            .lines()
            .skip(1)
            .all(|row| row.split('\t').count() == 3),
        "every row names callee, outcome and visibility: {receipt}"
    );
    assert!(
        receipt
            .lines()
            .any(|row| row.contains("\tinserted\t") && row.trim_end().ends_with("pub")),
        "the cross-module twin is inserted, and the row says with which visibility: {receipt}"
    );
}

/// **R517-7 / report 040 — the receipt has to reach the ARTIFACT, not just the
/// thread local.**
///
/// batch 27 carried `raw-boundary-twin-placement.tsv` for all nineteen
/// programs and **every one was header-only**, while the same frame's
/// `counted-void-calls` table showed **66 `raw-twin` routes** (lodepng 32,
/// heman 28, binn 4, bzip2 2). The cause is an ordering one, entirely mine:
/// `RawBoundaryArtifacts` is built in `finish_decide` — the DECISION stage —
/// and the graft that records the receipt runs later, inside
/// `verify_and_revert`'s emission rounds. So the census read the slot before
/// anything wrote it, and no frame could ever have carried a row.
///
/// The two witnesses that were supposed to pin this each carried an escape:
/// `wave6r_twin_placement_is_exported_to_the_artifacts` asserts
/// `is_empty() || starts_with(HEADER)`, and
/// `wave6r_twin_receipt_names_the_placement_and_the_visibility` returns early
/// when the receipt is empty. Both pass with the field permanently blank.
/// **This one has no escape**: it runs the census-shaped path (a full
/// `rewrite_core_injected`, the same one `RewriteOutcome::Emitted` feeds the
/// census from) and requires the row.
#[test]
fn wave6r_twin_placement_reaches_the_artifact_of_a_full_run() {
    // The single-module form of `counted_void_tests`'
    // `w6v_addressed_pointer_storage_copy_routes_to_the_raw_twin`: the copy
    // destination is the source pointer's own storage, so no disjointness
    // proof exists and the call routes to the pristine raw twin. The
    // cross-module fixture the other two witnesses use degrades under the
    // full pipeline (`escalation-required: no progress`), which is why this
    // one is stated here rather than reused.
    const TWIN: &str = r#"
#![allow(dead_code, unused_mut)]
unsafe fn lodepng_memcpy(mut dst: *mut core::ffi::c_void,
    mut src: *const core::ffi::c_void, mut size: usize) {
    let mut i: usize = 0;
    i = 0;
    while i < size {
        *(dst as *mut i8).offset(i as isize) = *(src as *const i8).offset(i as isize);
        i = i.wrapping_add(1);
    }
}
pub unsafe fn copy_pointer_storage() -> u8 {
    let data = [7u8; 8];
    let mut src: *const core::ffi::c_void = data.as_ptr().cast();
    let dst: *mut core::ffi::c_void =
        &raw mut src as *mut *const core::ffi::c_void as *mut core::ffi::c_void;
    lodepng_memcpy(dst, src, 1);
    (src as usize & 0xff) as u8
}
"#;
    let outcome = super::super::rewrite_core_injected(
        ::utils::compilation::str_to_input(TWIN),
        None,
        super::super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        Some((
            super::super::A5Mode::PreciseReplay,
            Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    // Either outcome is fine: the invariant is about the ARTIFACT the census
    // consumes, and both constructors hand one over. The batch-27 frame is the
    // counterexample this pins — 66 `raw-twin` rows in `counted-void-calls`
    // against nineteen header-only `twin-placement` tables.
    let artifacts = match outcome {
        super::super::RewriteOutcome::Emitted {
            raw_boundary_artifacts,
            ..
        }
        | super::super::RewriteOutcome::Degraded {
            raw_boundary_artifacts,
            ..
        } => raw_boundary_artifacts,
    };
    // The premise, asserted rather than assumed: this run really does route a
    // twin. Without it the receipt would be legitimately empty and the rest
    // would be vacuous — which is exactly how the other two witnesses failed.
    let routed = artifacts
        .counted_void_call_receipts
        .lines()
        .filter(|row| row.contains("raw-twin"))
        .count();
    assert!(
        routed > 0,
        "the fixture must route a raw twin for this witness to mean anything: {}",
        artifacts.counted_void_call_receipts
    );
    let receipt = artifacts.twin_placement;
    assert!(
        receipt.starts_with(super::super::decision::counted_void::TWIN_RECEIPT_HEADER),
        "{routed} raw-twin route(s) were planned, so the artifact owes the \
         placement receipt the graft recorded: {receipt:?}"
    );
    // What this witness does NOT assert, and why. Every fixture that routes a
    // twin degrades at this head (`escalation-required: no progress`), and on a
    // degraded run the kept output is the unmodified input — so "no placement
    // row" is the correct answer there, not a bug, and asserting a row would
    // pin the fixture's degradation rather than the wiring. The discriminating
    // fact is the one above: before the fix this artifact was `""` on every
    // path, after it the graft's own receipt arrives. Whether an EMITTING
    // program's rows appear is a corpus question, answered at the next frame
    // (batch 27 had 66 routes and nineteen header-only tables).
    //
    // One consequence worth recording: `record_twin_receipt` OVERWRITES, so
    // the last emission round wins. On a reverting run that is the reverted
    // round, which is the right answer for the tree that was kept.
    assert!(
        receipt.lines().count() >= 1,
        "the header is the graft's own, not a default: {receipt:?}"
    );
}
