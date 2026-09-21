//! W-C2 controls of existing bridge evidence; no extent producer or admission.

#[cfg(test)]
mod tests {
    const INPUT: &str = r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe fn local_read(p: *const u8, n: usize) -> u8 {
            let end = p.wrapping_add(n);
            *end.wrapping_sub(1)
        }
        pub unsafe fn caller(p: *const u8, n: usize) -> u8 {
            *p.offset(1) + local_read(p, n)
        }
    "#;

    #[test]
    fn w5c_wc2_existing_slice_to_raw_local_counted_call() {
        let (table, trace) = ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
            let table = crate::bo_rewriter::decide_table(tcx).unwrap();
            let trace = crate::bo_rewriter::raw_boundary_trace_artifacts(tcx).unwrap();
            (table, trace)
        })
        .unwrap();
        let receipts = table
            .slice_use_receipts
            .iter()
            .filter(|r| r.adapter == "slice-to-raw-const")
            .collect::<Vec<_>>();
        assert_eq!(receipts.len(), 1);
        assert_eq!(receipts[0].source_form, "slice-shared");
        assert_eq!(receipts[0].target_form, "*const u8");
        assert!(
            matches!(&receipts[0].retention, crate::bo_rewriter::mechanical_receipt::MechanicalRetention::T2 { waiver_id } if waiver_id == crate::bo_rewriter::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID)
        );
        assert!(trace.dispositions.contains("retention-attestation-absent"));
        let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(INPUT).unwrap();

        let compact = emitted.split_whitespace().collect::<String>();
        assert!(compact.contains("fncaller(p:&[u8]"), "{emitted}");
        assert!(compact.contains("fnlocal_read(p:*constu8"), "{emitted}");
        assert!(compact.contains(".as_ptr()"), "{emitted}");
        assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
        if let Some(dir) = std::env::var_os("CRAT_W5C_ARTIFACT_DIR") {
            let dir = std::path::PathBuf::from(dir);
            std::fs::write(dir.join("wc2-input.rs"), INPUT).unwrap();
            std::fs::write(dir.join("wc2-emitted.rs"), emitted).unwrap();
            let rows = receipts
                .iter()
                .flat_map(|p| p.materialize(true, false).1)
                .collect::<Vec<_>>();
            std::fs::write(
                dir.join("wc2-receipts.tsv"),
                crate::bo_rewriter::mechanical_receipt::render_slice_use_rows(&rows),
            )
            .unwrap();
        }
    }
    #[test]
    fn w5c_wc2_attestation_does_not_replace_local_retention_proof() {
        ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
            let (table, _) = crate::bo_rewriter::decide_table_with_ctx_config(tcx, Some((crate::bo_rewriter::A5Mode::PreciseReplay, Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph)))).unwrap();

            let rows = table.slice_use_receipts.iter().filter(|p| p.adapter=="slice-to-raw-const").collect::<Vec<_>>();
            assert_eq!(rows.len(),1);
            assert!(matches!(&rows[0].retention, crate::bo_rewriter::mechanical_receipt::MechanicalRetention::T2 { waiver_id } if waiver_id == crate::bo_rewriter::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID));
            assert!(rows[0].boundary_evidence.contains("retention-open-boundary"));
        }).unwrap();
    }

    /// **The count is never the thin source's extent** — restated for both
    /// frames (R217-2(a)).
    ///
    /// The original claim was that the caller stays thin and emits
    /// `p: *const u8`. Wave-4's extent-lift waiver (R481-1 / R482-3, the
    /// user's ruling) gives this population the §77 fallback slice instead, so
    /// the FORM is frame-dependent and the claim this witness owns is not:
    /// `local_read(p, n)` must never make `n` the extent of `p`. In this frame
    /// the subject is held; under the waiver arm it is a `FALLBACK_SLICE_EXTENT`
    /// view. Neither is `n`, and the emitted program type-checks either way.
    #[test]
    fn w5c_wc2_count_does_not_widen_a_thin_source() {
        let input = INPUT.replace("*p.offset(1) + local_read(p, n)", "local_read(p, n)");
        let table = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
            crate::bo_rewriter::decide_table(tcx).unwrap()
        })
        .unwrap();
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.label == "caller::p")
            .unwrap();
        let held = matches!(decision, super::super::Decision::Degraded(d) if matches!(d.reason, super::super::DegradeReason::LocalCalleeAccessExtent { .. }));
        let waived = matches!(decision, super::super::Decision::Slice { .. });
        assert!(
            held || waived,
            "the thin source is held, or lifted by the waiver — nothing else: {subject:?} {decision:?}"
        );
        let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
        let flat = emitted.split_whitespace().collect::<String>();
        assert!(
            !flat.contains("from_raw_parts(p,(n)asusize)")
                && !flat.contains("from_raw_parts_mut(p,(n)asusize)"),
            "the callee's count must not become the caller's extent: {emitted}"
        );
        if waived {
            // The lifted form is a slice PARAMETER; whatever extent its own
            // callers construct is theirs (the ruled fallback where nothing
            // licenses one), and the only thing this witness asserts about it
            // is the line above: it is not `n`.
            assert!(flat.contains("fncaller(p:&[u8]"), "{emitted}");
        } else {
            assert!(flat.contains("fncaller(p:*constu8"), "{emitted}");
        }
        assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    }

    #[test]
    fn w5c_wc2_existing_t1_counted_foreign_control() {
        let input = r#"
            #![allow(dead_code, unused_unsafe)]
            extern "C" { fn strncpy(dst: *mut i8, src: *const i8, n: usize) -> *mut i8; }
            pub unsafe fn caller(p: *const i8) -> i8 {
                let mut dst = [0i8; 2];
                strncpy(dst.as_mut_ptr(), p, 2);
                *p.offset(1)
            }
        "#;
        let table = ::utils::compilation::run_compiler_on_str(input, |tcx| {
            crate::bo_rewriter::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::bo_rewriter::A5Mode::PreciseReplay,
                    Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap()
            .0
        })
        .unwrap();
        let rows = table
            .slice_use_receipts
            .iter()
            .filter(|p| p.source_form == "slice-shared")
            .collect::<Vec<_>>();
        assert_eq!(rows.len(), 1, "{:#?}", table.slice_use_receipts);
        assert_eq!(
            rows[0].retention,
            crate::bo_rewriter::mechanical_receipt::MechanicalRetention::T1
        );
        let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(input).unwrap();
        assert!(
            emitted
                .split_whitespace()
                .collect::<String>()
                .contains("fncaller(p:&[i8]"),
            "{emitted}"
        );
        assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    }
}
