//! W-C7 witnesses: the `StoreRangeH2 → StoreH2` shape (brotli's hash readers:
//! a thin forwarder between a slice-holding caller and a reading callee),
//! reduced with a delivered-slice root.
use super::slice_input::Extent;

const CHAIN: &str = r###"
#[repr(C)]
pub struct H2 { pub buckets_: [u32; 65536] }
unsafe fn StoreH2(self_0: *mut H2, data: *const u8, mask: usize, ix: usize) {
    // `HashBytesH2(&*data.offset((ix & mask) as isize))` in the corpus — the
    // computed view wave-6s lands in batch 8; the four masked reads inline
    // are the same accesses past one element.
    let at = (ix & mask) as isize;
    let h = ((*data.offset(at) as u64) | ((*data.offset(at + 1) as u64) << 8) | ((*data.offset(at + 2) as u64) << 16) | ((*data.offset(at + 3) as u64) << 24)).wrapping_mul(0x1e35a7bd);
    let key = (h >> 16) as u32 & 65535;
    (*self_0).buckets_[key as usize] = ix as u32;
}
unsafe fn StoreRangeH2(self_0: *mut H2, data: *const u8, mask: usize, ix_start: usize, ix_end: usize) {
    let mut i = ix_start;
    while i < ix_end {
        StoreH2(self_0, data, mask, i);
        i = i.wrapping_add(1);
    }
}
unsafe fn StitchToPreviousBlockH2(self_0: *mut H2, num_bytes: usize, position: usize, ringbuffer: *const u8, ringbuffer_mask: usize) {
    if num_bytes >= 4 && position >= 3 {
        StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(3));
        StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(2));
        StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(1));
        StoreRangeH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(3), position);
    }
}
unsafe fn run(self_0: *mut H2, buf: *const u8, n: usize) -> u32 {
    let mut i = 0usize;
    let mut acc = 0u32;
    while i < n { acc = acc.wrapping_add(*buf.offset(i as isize) as u32); i = i.wrapping_add(1); }
    StitchToPreviousBlockH2(self_0, n, n, buf, 4095);
    acc
}
pub unsafe fn entry(self_0: *mut H2) -> u32 {
    let buf: [u8; 4096] = [7; 4096];
    run(self_0, buf.as_ptr(), 4096)
}
"###;

fn fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{CHAIN}"
    )
}

pub(super) fn decisions(input: &str) -> Vec<(String, super::Decision)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        crate::bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::bo_rewriter::A5Mode::PreciseReplay,
                Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap()
        .0
        .entries
        .iter()
        .map(|(s, d)| (s.label.clone(), d.clone()))
        .collect()
    })
    .unwrap()
}
pub(super) fn decision<'a>(
    table: &'a [(String, super::Decision)],
    label: &str,
) -> &'a super::Decision {
    &table
        .iter()
        .find(|(l, _)| l == label)
        .unwrap_or_else(|| panic!("{label}"))
        .1
}

pub(super) fn proofs(input: &str) -> Vec<(String, Result<usize, super::slice_input::Hold>)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = crate::bo_rewriter::decide_table(tcx).unwrap();
        let functions = tcx
            .hir_body_owners()
            .filter(|d| matches!(tcx.def_kind(*d), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let program = crate::bo_rewriter::collect_program(tcx);
        let fat = crate::bo_rewriter::fat_facts::FatFacts::from_program(&program);
        table
            .entries
            .iter()
            .filter(|(s, _)| matches!(s.kind, super::SubjectKind::Param { .. }) && s.ptr_depth == 1)
            .map(|(s, _)| {
                (
                    s.label.clone(),
                    super::slice_input::prove(tcx, s, &facts, &fat).map(|p| p.members.len()),
                )
            })
            .collect()
    })
    .unwrap()
}
pub(super) fn input_extents(
    input: &str,
) -> Vec<(String, Result<Extent, super::slice_input::Hold>)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = crate::bo_rewriter::decide_table(tcx).unwrap();
        let functions = tcx
            .hir_body_owners()
            .filter(|d| matches!(tcx.def_kind(*d), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let program = crate::bo_rewriter::collect_program(tcx);
        let fat = crate::bo_rewriter::fat_facts::FatFacts::from_program(&program);
        table
            .entries
            .iter()
            .filter(|(s, _)| matches!(s.kind, super::SubjectKind::Param { .. }) && s.ptr_depth == 1)
            .map(|(s, _)| {
                (
                    s.label.clone(),
                    super::slice_input::prove(tcx, s, &facts, &fat).map(|p| p.extent),
                )
            })
            .collect()
    })
    .unwrap()
}
pub(super) fn extent_of<'a>(
    extents: &'a [(String, Result<Extent, super::slice_input::Hold>)],
    label: &str,
) -> &'a Result<Extent, super::slice_input::Hold> {
    &extents
        .iter()
        .find(|(l, _)| l == label)
        .unwrap_or_else(|| panic!("{label}"))
        .1
}
pub(super) fn proof_of<'a>(
    proofs: &'a [(String, Result<usize, super::slice_input::Hold>)],
    label: &str,
) -> &'a Result<usize, super::slice_input::Hold> {
    &proofs
        .iter()
        .find(|(l, _)| l == label)
        .unwrap_or_else(|| panic!("{label}"))
        .1
}

/// Both forwarders are supplied from the delivered-slice root through the
/// chain; the reading end and the root are typed out of scope of the rule.
#[test]
fn w5c_slice_input_forwarders_are_supplied_from_the_slice_root() {
    use super::slice_input::Hold;
    let proofs = proofs(&fixture());
    assert_eq!(
        proof_of(&proofs, "StitchToPreviousBlockH2::ringbuffer"),
        &Ok(1)
    );
    // through `StitchToPreviousBlockH2::ringbuffer`, itself a supplied forwarder
    assert_eq!(proof_of(&proofs, "StoreRangeH2::data"), &Ok(2));
    assert_eq!(proof_of(&proofs, "StoreH2::data"), &Err(Hold::CalleeNotFat));
    // `run::buf` is a slice by its own arithmetic; as a forwarder it is not
    // supplied (`entry` passes `buf.as_ptr()`) but carries its companion `n`
    // (R418-1).
    assert_eq!(proof_of(&proofs, "run::buf"), &Ok(1));
    assert_eq!(
        extent_of(&input_extents(&fixture()), "run::buf"),
        &Ok(Extent::Companion(super::seam::LenEvidence::Following))
    );
    assert_eq!(
        extent_of(&input_extents(&fixture()), "StoreRangeH2::data"),
        &Ok(Extent::Supplied)
    );
}

/// A caller that supplies no buffer no longer refuses a forwarder that
/// carries its own companion (R418-1): `run` passes a local pointer it made
/// itself, `ringbuffer` takes the slice with `ringbuffer_mask` as its extent,
/// and the call adapts raw with it. (The thin `p` itself is the decline's —
/// `reader_chain_tests`.) Without a companion the chain still refuses.
#[test]
fn w5c_slice_input_unsupplied_caller_adapts_with_the_companion() {
    use super::slice_input::Hold;
    let input = fixture().replace(
        "    StitchToPreviousBlockH2(self_0, n, n, buf, 4095);",
        "    let x: u8 = acc as u8;\n    let p: *const u8 = &x;\n    StitchToPreviousBlockH2(self_0, n, n, p, 4095);",
    );
    assert_eq!(
        extent_of(
            &input_extents(&input),
            "StitchToPreviousBlockH2::ringbuffer"
        ),
        &Ok(Extent::Companion(super::seam::LenEvidence::Following))
    );
    // …and `StoreRangeH2::data`, no longer supplied through `ringbuffer`,
    // stands on its own companion `mask`.
    assert_eq!(
        extent_of(&input_extents(&input), "StoreRangeH2::data"),
        &Ok(Extent::Companion(super::seam::LenEvidence::Following))
    );
    let no_companion = input
        .replace(
            "position: usize, ringbuffer: *const u8, ringbuffer_mask: usize)",
            "position: usize, _head: *const u8, ringbuffer: *const u8, _tail: *const u8, ringbuffer_mask: usize)",
        )
        .replace(
            "StitchToPreviousBlockH2(self_0, n, n, p, 4095);",
            "StitchToPreviousBlockH2(self_0, n, n, p, p, p, 4095);",
        );
    let proofs = proofs(&no_companion);
    assert_eq!(
        proof_of(&proofs, "StitchToPreviousBlockH2::ringbuffer"),
        &Err(Hold::CallerNotSupplied)
    );
    // `StoreRangeH2::data` keeps its own companion `mask` either way.
    assert_eq!(proof_of(&proofs, "StoreRangeH2::data"), &Ok(1));
}

/// Under the corpus attestation the propagation takes both forwarders off the
/// extent hold: `ringbuffer` is DECIDED a shared slice; `data` — the buffer
/// beside the hasher's `&mut self_0` at `StoreH2(self_0, data, …)` inside
/// `StoreRangeH2` — is assigned the PAIR raw-view role (T2), the corpus pairs
/// table's `raw-view T2 overlapping` verdict (309 of 375 rows at `dc601707`).
/// The root's own conversion (`run::buf`) fires and is withdrawn at the same
/// pair gate at `entry → run`. Delivery of the raw-view rows is wave-6p's
/// distinct-allocation certificate, not a carrier.
#[test]
fn w5c_slice_input_forwarders_leave_the_extent_hold_under_the_corpus_attestation() {
    let input = fixture();
    let table = decisions(&input);
    assert!(
        matches!(
            decision(&table, "StitchToPreviousBlockH2::ringbuffer"),
            super::Decision::Slice { mutable: false, .. }
        ),
        "{:?}",
        decision(&table, "StitchToPreviousBlockH2::ringbuffer")
    );
    assert!(
        matches!(
            decision(&table, "StoreRangeH2::data"),
            super::Decision::Degraded(super::Degradation {
                reason: super::DegradeReason::PairRawView,
                ..
            })
        ),
        "{:?}",
        decision(&table, "StoreRangeH2::data")
    );
    let receipts = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (_, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::bo_rewriter::A5Mode::PreciseReplay,
                Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        ctx.raw_boundary_artifacts
            .additive_family_receipts
            .iter()
            .filter(|r| r.family == "SliceUse" && r.owner_path == "run")
            .map(|r| (r.cause.clone(), r.subjects.clone()))
            .collect::<Vec<_>>()
    })
    .unwrap();
    let (cause, subjects) = receipts.first().unwrap_or_else(|| panic!("{receipts:?}"));
    assert!(
        subjects
            .iter()
            .any(|(s, prior, candidate)| s == "run::buf#2"
                && prior == "raw"
                && candidate == "slice-shared"),
        "{subjects:?}"
    );
    assert!(
        cause.contains("a5-raw-view-template-unavailable"),
        "{cause}"
    );
}

/// The delivery itself: RED until the pair beside the hasher is certified
/// disjoint (report 016 §2).
#[test]
#[ignore = "W-C7 RED: the PAIR raw-view role beside the hasher's &mut self_0 (wave-6p's distinct-allocation certificate; report 016)"]
fn w5c_slice_input_forwarders_deliver() {
    let input = fixture();
    let table = decisions(&input);
    for label in ["StitchToPreviousBlockH2::ringbuffer", "StoreRangeH2::data"] {
        assert!(
            matches!(
                decision(&table, label),
                super::Decision::Slice { mutable: false, .. }
            ),
            "{label}: {:?}",
            decision(&table, label)
        );
    }
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(
        emitted.contains("unsafe fn StoreRangeH2(self_0: &mut H2, data: &[u8]"),
        "{emitted}"
    );
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
}
