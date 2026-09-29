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
/// extent hold — the rule's claim, and what this witness pins. Their END
/// states are the composition's: `data` — the buffer beside the hasher's
/// `&mut self_0` at `StoreH2(self_0, data, …)` inside `StoreRangeH2` — takes
/// the PAIR raw-view role (T2), the corpus pairs table's `raw-view T2
/// overlapping` verdict (309 of 375 rows at `dc601707`); `ringbuffer` is a
/// shared slice on this lane's own line and falls back to the thin `Ref` in
/// batch 9's frame, where wave-5d's primitive excludes its never-applied
/// candidate per subject at the Restore anchor (`[9, 8]`, their report 019).
/// A thin `Ref` there is the `from_ref`-into-a-wide-reader hole R418-1 closes
/// (report 019 §1); it is named here, not asserted away.
/// The root's own conversion (`run::buf`) fires and is withdrawn at the same
/// pair gate at `entry → run`. Delivery of the raw-view rows is wave-6p's
/// distinct-allocation certificate, not a carrier.
#[test]
fn w5c_slice_input_forwarders_leave_the_extent_hold_under_the_corpus_attestation() {
    let input = fixture();
    let table = decisions(&input);
    let held = |label: &str| {
        matches!(
            decision(&table, label),
            super::Decision::Degraded(super::Degradation {
                reason: super::DegradeReason::LocalCalleeAccessExtent { .. },
                ..
            })
        )
    };
    assert!(
        !held("StitchToPreviousBlockH2::ringbuffer"),
        "{:?}",
        decision(&table, "StitchToPreviousBlockH2::ringbuffer")
    );
    assert!(
        !held("StoreRangeH2::data"),
        "{:?}",
        decision(&table, "StoreRangeH2::data")
    );
    assert!(
        matches!(
            decision(&table, "StitchToPreviousBlockH2::ringbuffer"),
            super::Decision::Slice { mutable: false, .. } | super::Decision::Ref { mutable: false }
        ),
        "{:?}",
        decision(&table, "StitchToPreviousBlockH2::ringbuffer")
    );
    // **The end state is the frame's, the claim is the hold's** (R217-2(a)
    // under R465-4). `StoreRangeH2::data` is the buffer beside the hasher's
    // `&mut self_0`: uncertified, the overlap machinery takes it as the pair's
    // raw view; with wave-6p's certificate (e) in the frame it is the shared
    // slice this lane's propagation asked for (their report 015 §5 — report
    // 025 §3's "delivery is wave-6p's certificate", arriving). Both are off
    // the extent hold, which is what W-C7 claims.
    assert!(
        matches!(
            decision(&table, "StoreRangeH2::data"),
            super::Decision::Slice { mutable: false, .. }
                | super::Decision::Degraded(super::Degradation {
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
    // Where the pair is certified there is no withdrawal to receipt at all:
    // the root's candidate stands. Where it is not, the receipt names it.
    let Some((cause, subjects)) = receipts.first() else {
        return;
    };
    assert!(
        subjects
            .iter()
            .any(|(s, prior, candidate)| s == "run::buf#2"
                && prior == "raw"
                && candidate == "slice-shared"),
        "{subjects:?}"
    );
    // The gate the candidate dies at: the PAIR's missing A5 raw-view template
    // on this lane's own line; in batch 9's frame wave-5d's primitive
    // re-derives the exclusion from the Restore anchor at
    // `StitchToPreviousBlockH2` (`exclusion-rederivation:anchor=8:…[8, 9]`,
    // their report 019) and records that instead. Either way the root's
    // `raw → slice-shared` candidate is withdrawn, which is the claim.
    assert!(
        cause.contains("a5-raw-view-template-unavailable")
            || cause.contains("exclusion-rederivation"),
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

/// **R477-6 — the corpus spelling of the same masked read.** The lane's
/// `CHAIN` binds the masked index to a local (`let at = (ix & mask) as isize`)
/// and `index_bound_by_companion` admits it: a local is not another parameter.
/// brotli writes it INLINE — `HashBytesH2(&*data.offset((ix & mask) as isize))`
/// — so the index expression names the parameter `ix`, the "reached through
/// another parameter" test fires, and all 34 corpus rows of this shape read
/// `Err(CompanionNotIndexBound)` (report 033).
///
/// The mask is what decides it: `ix & mask <= mask`, whatever `ix` is, so the
/// companion bounds every index the callee forms — at `mask + 1` elements, not
/// `mask`.
fn masked_inline() -> String {
    let inlined = fixture()
        .replace("    let at = (ix & mask) as isize;\n", "")
        .replace("*data.offset(at)", "*data.offset((ix & mask) as isize)")
        .replace(
            "*data.offset(at + 1)",
            "*data.offset(((ix & mask) + 1) as isize)",
        )
        .replace(
            "*data.offset(at + 2)",
            "*data.offset(((ix & mask) + 2) as isize)",
        )
        .replace(
            "*data.offset(at + 3)",
            "*data.offset(((ix & mask) + 3) as isize)",
        );
    assert!(
        !inlined.contains("let at = "),
        "the fixture must inline the index"
    );
    inlined
}

/// The same unsupplied root the companion witness above uses, so the extent
/// question is the forwarder's own and not its callers'.
fn masked_inline_unsupplied() -> String {
    masked_inline().replace(
        "    StitchToPreviousBlockH2(self_0, n, n, buf, 4095);",
        "    let x: u8 = acc as u8;\n    let p: *const u8 = &x;\n    StitchToPreviousBlockH2(self_0, n, n, p, 4095);",
    )
}

#[test]
fn w5c_slice_input_a_masked_index_is_bounded_by_its_mask() {
    assert_eq!(
        extent_of(
            &input_extents(&masked_inline_unsupplied()),
            "StoreRangeH2::data"
        ),
        &Ok(Extent::CompanionMask(super::seam::LenEvidence::Following))
    );
}

/// **Control (i)** — the same chain with the index bound the ordinary way (the
/// lane's own `CHAIN`, whose masked index is bound to a local): the extent is
/// the companion itself, with no `+ 1`. One rule, two arms, and the arms are
/// told apart by the spelling that decides them.
#[test]
fn w5c_slice_input_an_unmasked_companion_keeps_its_own_length() {
    let unsupplied = fixture().replace(
        "    StitchToPreviousBlockH2(self_0, n, n, buf, 4095);",
        "    let x: u8 = acc as u8;\n    let p: *const u8 = &x;\n    StitchToPreviousBlockH2(self_0, n, n, p, 4095);",
    );
    assert_eq!(
        extent_of(&input_extents(&unsupplied), "StoreRangeH2::data"),
        &Ok(Extent::Companion(super::seam::LenEvidence::Following))
    );
}

/// **Control (ii)** — an index reached through a SECOND pointer parameter
/// (lodepng's `bitstream[*bitpointer >> 3]`, report 019 §1's false companion):
/// no mask dominates it, so the refusal stands exactly as before.
#[test]
fn w5c_slice_input_an_index_through_another_pointer_is_still_refused() {
    use super::slice_input::Hold;
    let through_pointer = masked_inline_unsupplied().replace(
        "*data.offset((ix & mask) as isize)",
        "*data.offset((ix.wrapping_add(mask)) as isize)",
    );
    assert_ne!(
        through_pointer,
        masked_inline_unsupplied(),
        "the control must change the fixture"
    );
    assert_eq!(
        extent_of(&input_extents(&through_pointer), "StoreRangeH2::data"),
        &Err(Hold::CompanionNotIndexBound)
    );
}

/// **The emission half of R477-6**, at the one place both halves are visible:
/// the masked length renders exactly like a licensed one — it IS a call-site
/// expression — and the receipt says fabricated, because the mask bounds the
/// callee's indexes and neither its read width nor the allocation.
#[test]
fn w5c_slice_input_a_masked_length_renders_derived_and_receipts_fabricated() {
    use super::seam::{GlueCore, GlueSpec, SeamLen, receipt_extent};
    let spec =
        GlueSpec::core(GlueCore::FromRawParts, false).with_len("(ringbuffer_mask).wrapping_add(1)");
    let licensed = spec.clone();
    let masked = GlueSpec {
        len: Some(SeamLen::MaskDerived(
            "(ringbuffer_mask).wrapping_add(1)".to_owned(),
        )),
        ..spec
    };
    assert_eq!(
        masked.render("p"),
        licensed.render("p"),
        "the derived length is emitted as the expression it is"
    );
    assert!(
        masked
            .render("p")
            .is_some_and(|text| text.contains("(ringbuffer_mask).wrapping_add(1)")),
        "the mask's own `+ 1` must reach the constructed slice"
    );
    assert_eq!(
        super::seam::masked_len_text("ringbuffer_mask".to_owned(), true),
        "(ringbuffer_mask).wrapping_add(1)",
        "the mask's length is the mask plus one"
    );
    assert_eq!(
        super::seam::masked_len_text("n".to_owned(), false),
        "n",
        "and an ordinary companion is untouched"
    );
    assert_eq!(masked.extent_arm_key(), "mask-plus-one@addendum-77");
    assert!(
        masked
            .len
            .as_ref()
            .is_some_and(super::seam::SeamLen::is_fabricated),
        "a masked extent is counted with the fabricated ones (§77)"
    );
    assert_ne!(
        format!("{:?}", receipt_extent(&masked)),
        format!("{:?}", receipt_extent(&licensed)),
        "and its receipt is not the licensed one"
    );
}

/// **Control (iii)** — masked by the WRONG integer. The index is `ix & ix_end`,
/// a mask formed from another parameter, which bounds the index by something
/// the companion does not name. The refusal stands: it is the COMPANION's mask
/// that licenses the companion's length.
#[test]
fn w5c_slice_input_a_mask_by_another_parameter_is_still_refused() {
    use super::slice_input::Hold;
    let wrong_mask = masked_inline_unsupplied()
        .replace(
            "unsafe fn StoreH2(self_0: *mut H2, data: *const u8, mask: usize, ix: usize) {",
            "unsafe fn StoreH2(self_0: *mut H2, data: *const u8, mask: usize, ix: usize, ix_end: usize) {",
        )
        .replace("(ix & mask)", "(ix & ix_end)")
        .replace("StoreH2(self_0, data, mask, i);", "StoreH2(self_0, data, mask, i, ix_end);")
        .replace(
            "StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(3));",
            "StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(3), position);",
        )
        .replace(
            "StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(2));",
            "StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(2), position);",
        )
        .replace(
            "StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(1));",
            "StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(1), position);",
        );
    assert!(
        wrong_mask.contains("ix & ix_end"),
        "the control must change the fixture"
    );
    assert_eq!(
        extent_of(&input_extents(&wrong_mask), "StoreRangeH2::data"),
        &Err(Hold::CompanionNotIndexBound)
    );
}
