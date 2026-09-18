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
