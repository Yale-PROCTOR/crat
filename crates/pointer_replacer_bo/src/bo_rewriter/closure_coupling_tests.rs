//! **R815-7 item 2 (wave-6a 150 §2, F1) — the closure coupling for the native
//! lends.** A function whose Box owner lends a view at a call through its
//! native plan leaves no input twin at that argument: the seam registers the
//! native-owned argument as a zero-syntax interface site, `(callee, caller)`
//! in `seams.interface_dependencies`. `TerminalCallPlans`'s reversion closure
//! did not read those edges, so a caller-only rollback left the callee's slice
//! formal beside the caller's original raw argument: the tree did not
//! type-check and rolled back further. heman's `transform_to_coordfield` lends
//! `f` / `d` to `edt_with_payload` (the clean twin, class_split's fixture).

/// heman's `transform_to_coordfield` with the callee whose offsets are
/// non-negative: class_split's clean twin, verbatim.
const CLEAN: &str = include_str!("testdata/r815-coordfield-clean.rs");

fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

/// wave-6a's saved witness (`r813-caller-retraction-witness.diff`), as the
/// regression: reverting `transform_to_coordfield` alone reverts
/// `edt_with_payload` too, and the tree type-checks.
#[test]
fn r815_7_a_caller_only_retraction_reverts_the_callee_and_type_checks() {
    use crate::bo_rewriter::{self as bo, bridge_receipt::SignatureClassId};
    ::utils::compilation::run_compiler_on_str(CLEAN, |tcx| {
        let capture = bo::ast_transform::capture_ast(tcx).unwrap();
        let (table, _) = bo::decide_table_with_ctx_config(
            tcx,
            Some((
                bo::OverlapMode::PreciseReplay,
                Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let class_of = |name: &str| {
            table
                .entries
                .iter()
                .map(|(subject, _)| subject.fn_did)
                .find(|did| tcx.def_path_str(did.to_def_id()) == name)
                .map(SignatureClassId::of)
                .unwrap()
        };
        let (caller, callee) = (
            class_of("transform_to_coordfield"),
            class_of("edt_with_payload"),
        );
        assert!(
            table
                .seams
                .interface_dependencies
                .contains(&(callee, caller)),
            "the native lend's interface edge: {:?}",
            table.seams.interface_dependencies
        );
        let emission = bo::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &[]).unwrap();
        let reverted = std::collections::BTreeSet::from([caller]);
        let atoms = std::collections::BTreeSet::new();
        assert!(
            emission
                .plan
                .terminal_call_plans
                .effective_reverted_classes(&reverted, &atoms)
                .contains(&callee),
            "the terminal closure takes the callee with its caller"
        );
        let reverts =
            bo::ast_transform::revert_set_from_classes_and_atoms(&reverted, &atoms, &table)
                .unwrap();
        let (files, _, _, _) = bo::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .unwrap();
        let emitted = files.into_values().next().unwrap();
        let text = compact(&emitted);
        assert!(
            text.contains("unsafeextern\"C\"fnedt_with_payload(mutf:*mutlibc::c_float"),
            "the callee reverted with its caller:\n{emitted}"
        );
        assert!(bo::verify::type_checks_str(&emitted), "{emitted}");
    })
    .unwrap();
}
