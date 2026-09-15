//! Native two-half counted-source witnesses, derived from brotli entropy chains.
pub(crate) const ENTROPY: &str = r###"
            unsafe extern "C" fn ShannonEntropy(mut population:
                    *const u32, mut size: usize, mut total: *mut usize)
                -> f64 {
                let mut current_block: u64;
                let mut sum = 0 as i32 as usize;
                let mut retval = 0 as i32 as f64;
                let mut population_end = population.offset(size as isize);
                let mut p: usize = 0;
                if size & 1 as i32 as usize != 0 {
                    current_block = 15800646830660818732;
                } else { current_block = 715039052867723359; }
                loop {
                    match current_block {
                        715039052867723359 => {
                            if !(population < population_end) { break; }
                            let fresh0 = *population;
                            population = population.offset(1);
                            p = fresh0 as usize;
                            sum =
                                (sum as usize).wrapping_add(p) as usize as usize;
                            retval -= p as f64 * FastLog2(p);
                            current_block = 15800646830660818732;
                        }
                        _ => {
                            let fresh1 = *population;
                            population = population.offset(1);
                            p = fresh1 as usize;
                            sum =
                                (sum as usize).wrapping_add(p) as usize as usize;
                            retval -= p as f64 * FastLog2(p);
                            current_block = 715039052867723359;
                        }
                    }
                }
                if sum != 0 {
                    retval += sum as f64 * FastLog2(sum);
                }
                *total = sum;
                return retval;
            }
            #[inline(always)]
            unsafe extern "C" fn BitsEntropy(mut population: *const u32,
                mut size: usize) -> f64 {
                let mut sum: usize = 0;
                let mut retval = ShannonEntropy(population, size, &mut sum);
                if retval < sum as f64 {
                    retval = sum as f64;
                }
                return retval;
            }
            
unsafe fn FastLog2(x:usize)->f64 { if x == 0 {0.0} else {(x as f64).log2()} }
"###;
fn fixture(n: usize, name: &str) -> String {
    let entropy = if n == 256 {
        ENTROPY.replace("15800646830660818732", "18167736425092750904")
    } else {
        ENTROPY.to_owned()
    };
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,non_snake_case)]\n{}\npub unsafe fn {}()->f64 {{let depth_histo:[u32;{}]=[1;{}]; BitsEntropy(depth_histo.as_ptr(), {}usize)}}",
        entropy, name, n, n, n
    )
}
#[test]
fn w5c_thin_count_depth_histogram18_red() {
    emitted_slice(18, "BrotliPopulationCostCommand");
}
#[test]
fn w5c_thin_count_literal_histogram256_red() {
    emitted_slice(256, "BrotliPopulationCostLiteral");
}
fn emitted_slice(n: usize, name: &str) {
    let input = fixture(n, name);
    let table = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        crate::bo_rewriter::decide_table(tcx).unwrap()
    })
    .unwrap();
    for label in ["BitsEntropy::population", "ShannonEntropy::population"] {
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.label == label)
            .unwrap();
        assert!(
            matches!(decision, super::Decision::Slice { mutable: false, .. }),
            "{label}: {decision:?}"
        );
    }
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(emitted.contains("population: &[u32]"));
    assert!(emitted.contains("population.len().checked_sub"));
    assert!(!emitted.contains("FALLBACK_SLICE_EXTENT"));
    if let Ok(root) = std::env::var("CRAT_W5C_FIXTURE_CAPTURE") {
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(format!("{root}/{n}-original.rs"), &input).unwrap();
        std::fs::write(format!("{root}/{n}-emitted.rs"), &emitted).unwrap();
    }
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
}

fn proof(input: &str) -> Result<super::thin_counted::Proof, super::thin_counted::Hold> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = crate::bo_rewriter::decide_table(tcx).unwrap();
        let functions = tcx
            .hir_body_owners()
            .filter(|d| matches!(tcx.def_kind(*d), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let (subject, _) = table
            .entries
            .iter()
            .find(|(s, _)| s.label == "BitsEntropy::population")
            .unwrap();
        super::thin_counted::prove(tcx, subject, &facts)
    })
    .unwrap()
}
#[test]
fn w5c_thin_count_zero_odd_and_short_prefix() {
    for count in [0, 1, 17, 18] {
        let input = fixture(18, "run").replace("18usize)", &format!("{count}usize)"));
        let p = proof(&input).unwrap();
        assert_eq!((p.count_parameter, p.callers), (1, 1));
        let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
        assert!(emitted.contains("population: &[u32]"));
        assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
        if let Ok(root) = std::env::var("CRAT_W5C_FIXTURE_CAPTURE") {
            std::fs::create_dir_all(&root).unwrap();
            std::fs::write(format!("{root}/prefix-{count}-original.rs"), &input).unwrap();
            std::fs::write(format!("{root}/prefix-{count}-emitted.rs"), &emitted).unwrap();
        }
    }
}
#[test]
fn w5c_thin_count_short_buffer_and_narrowing_hold() {
    use super::thin_counted::Hold;
    for count in [
        "19usize",
        "(256usize as u8) as usize",
        "(255usize as i8) as usize",
    ] {
        assert_eq!(
            proof(&fixture(18, "run").replace("18usize)", &format!("{count})"))).unwrap_err(),
            Hold::CallerCount
        );
    }
}
#[test]
fn w5c_thin_count_unknown_source_and_extra_caller_hold() {
    use super::thin_counted::Hold;
    let extra = "\npub unsafe fn uncovered(p:*const u32,n:usize)->f64 {BitsEntropy(p,n)}";
    assert_eq!(
        proof(&(fixture(18, "run") + extra)).unwrap_err(),
        Hold::CallerSource
    );
    let other_reader = "\npub unsafe fn uncovered(p:*const u32,n:usize,total:*mut usize)->f64 {ShannonEntropy(p,n,total)}";
    assert_eq!(
        proof(&(fixture(18, "run") + other_reader)).unwrap_err(),
        Hold::CallerSource
    );
}
#[test]
fn w5c_thin_count_mutated_count_and_unknown_helper_hold() {
    use super::thin_counted::Hold;
    let changed = fixture(18, "run").replace(
        "let mut retval = ShannonEntropy",
        "size = 1; let mut retval = ShannonEntropy",
    );
    assert!(matches!(proof(&changed), Err(Hold::CalleeAccess(_))));
    // A count the caller computes at runtime is admitted, typed as such: the
    // reader walks exactly `count` elements (§28), and its `checked_sub` guards.
    let unknown = fixture(18, "run").replace("18usize)", "opaque())")
        + "\nunsafe fn opaque()->usize {static mut N:usize=18;N}";
    assert_eq!(
        proof(&unknown).unwrap().count,
        super::thin_counted::Count::Runtime
    );
    let fallback = fixture(18, "run").replace("18usize)", "1024usize)");
    assert_eq!(proof(&fallback).unwrap_err(), Hold::CallerCount);
}
#[test]
fn w5c_thin_count_callee_parity_and_extra_access_hold() {
    use super::thin_counted::Hold;
    for (from, to) in [
        ("size & 1", "size & 0"),
        ("population.offset(1)", "population.offset(2)"),
        ("*total = sum", "let _extra = *population; *total = sum"),
        (
            "let mut population_end =",
            "let mut population_end: *const u32 =",
        ),
    ] {
        assert!(
            matches!(
                proof(&fixture(18, "run").replace(from, to)),
                Err(Hold::CalleeAccess(_))
            ),
            "{to}"
        );
    }
}
#[test]
fn w5c_thin_count_exported_or_address_taken_hold() {
    use super::thin_counted::Hold;
    let input = fixture(18, "run");
    assert_eq!(
        proof(&input.replace(
            "unsafe extern \"C\" fn BitsEntropy",
            "pub unsafe extern \"C\" fn BitsEntropy"
        ))
        .unwrap_err(),
        Hold::IncompleteCallers
    );
    let input =
        input + "\npub fn address()->unsafe extern \"C\" fn(*const u32,usize)->f64 {BitsEntropy}";
    assert_eq!(proof(&input).unwrap_err(), Hold::IncompleteCallers);
}
#[test]
fn w5c_thin_count_missing_half_is_receipted() {
    let input = fixture(18, "run").replace("18usize)", "19usize)");
    let table = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        crate::bo_rewriter::decide_table(tcx).unwrap()
    })
    .unwrap();
    let (_, decision) = table
        .entries
        .iter()
        .find(|(s, _)| s.label == "BitsEntropy::population")
        .unwrap();
    let super::Decision::Degraded(d) = decision else { panic!("{decision:?}") };
    assert!(
        d.reason
            .detail()
            .contains("held:local-callee-access-extent:caller-count"),
        "{:?}",
        d.reason
    );
}

#[test]
fn w5c_thin_count_configured_private_entry_stays_held() {
    use sha2::{Digest, Sha256};
    for name in ["BitsEntropy", "ShannonEntropy"] {
        let input = fixture(18, "run");
        let config = crate::bo_rewriter::EmissionRunConfig {
            configured_exposure: super::exposure::ConfiguredExposureInput::checked(
                "counted-private-entry",
                [name.to_owned()],
                format!("{:x}", Sha256::digest(name.as_bytes())),
            )
            .unwrap(),
            ..Default::default()
        };
        let table = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
            crate::bo_rewriter::decide_table_with_emission_config(tcx, None, &config)
                .unwrap()
                .0
        })
        .unwrap();
        for label in ["BitsEntropy::population", "ShannonEntropy::population"] {
            let (_, decision) = table
                .entries
                .iter()
                .find(|(s, _)| s.label == label)
                .unwrap();
            assert!(
                !matches!(decision, super::Decision::Slice { .. }),
                "configured {name}, {label}: {decision:?}"
            );
        }
    }
}
#[test]
fn w5c_thin_count_reader_family_withdrawal_holds_wrapper() {
    use crate::bo_rewriter::{
        additive::{FamilyPolicy, FamilyStage},
        bridge_receipt::SignatureClassId,
    };
    ::utils::compilation::run_compiler_on_str(&fixture(18, "run"), |tcx| {
        let table = crate::bo_rewriter::decide_table(tcx).unwrap();
        let functions = tcx
            .hir_body_owners()
            .filter(|d| matches!(tcx.def_kind(*d), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let (wrapper, _) = table
            .entries
            .iter()
            .find(|(s, _)| s.label == "BitsEntropy::population")
            .unwrap();
        let (reader, _) = table
            .entries
            .iter()
            .find(|(s, _)| s.label == "ShannonEntropy::population")
            .unwrap();
        let mut policy = FamilyPolicy::at(FamilyStage::SliceUse);
        policy
            .withdrawn
            .insert((FamilyStage::SliceUse, SignatureClassId::of(reader.fn_did)));
        assert!(super::thin_counted::enabled_proof(tcx, wrapper, &facts, &policy, None).is_none());
    })
    .unwrap();
}
#[test]
fn w5c_thin_count_other_reader_gate_holds_wrapper() {
    let table = ::utils::compilation::run_compiler_on_str(&fixture(18, "run"), |tcx| {
        crate::bo_rewriter::decide_table_perturbed(tcx, |subjects| {
            let reader = subjects
                .iter_mut()
                .find(|s| s.label == "ShannonEntropy::population")
                .unwrap();
            reader.freed_at = Some(reader.attribution_span());
        })
        .unwrap()
        .0
    })
    .unwrap();
    let (_, decision) = table
        .entries
        .iter()
        .find(|(s, _)| s.label == "BitsEntropy::population")
        .unwrap();
    assert!(
        !matches!(decision, super::Decision::Slice { .. }),
        "{decision:?}"
    );
}

/// `src::enc::metablock::BlockSplitterFinishBlockLiteral`, reduced: the count
/// is the splitter's runtime field `alphabet_size_`; the sources are histogram
/// field arrays behind the splitter's raw pointer and a local pair, one of them
/// spelled `&mut *(…).data_.as_mut_ptr().offset(0)`.
const METABLOCK: &str = r###"
#[derive(Copy, Clone)]
#[repr(C)]
pub struct HistogramLiteral { pub data_: [u32; 256], pub total_count_: usize, pub bit_cost_: f64 }
#[repr(C)]
pub struct BlockSplitterLiteral { pub alphabet_size_: usize, pub num_blocks_: usize, pub block_size_: usize,
    pub curr_histogram_ix_: usize, pub last_histogram_ix_: [usize; 2], pub last_entropy_: [f64; 2],
    pub histograms_: *mut HistogramLiteral, pub split_threshold_: f64 }
unsafe fn HistogramAddHistogramLiteral(self_0: *mut HistogramLiteral, v: *const HistogramLiteral) {
    let mut i: usize = 0;
    (*self_0).total_count_ = (*self_0).total_count_.wrapping_add((*v).total_count_);
    while i < 256 {
        (*self_0).data_[i] = (*self_0).data_[i].wrapping_add((*v).data_[i]);
        i = i.wrapping_add(1);
    }
}
unsafe fn BlockSplitterFinishBlockLiteral(self_0: *mut BlockSplitterLiteral, is_final: i32) {
    let last_entropy = ((*self_0).last_entropy_).as_mut_ptr();
    let histograms = (*self_0).histograms_;
    if (*self_0).num_blocks_ == 0 {
        *last_entropy.offset(0) = BitsEntropy(((*histograms.offset(0)).data_).as_ptr(), (*self_0).alphabet_size_);
        *last_entropy.offset(1) = *last_entropy.offset(0);
        (*self_0).num_blocks_ = (*self_0).num_blocks_.wrapping_add(1);
    } else if (*self_0).block_size_ > 0 {
        let entropy = BitsEntropy(((*histograms.offset((*self_0).curr_histogram_ix_ as isize)).data_).as_ptr(), (*self_0).alphabet_size_);
        let mut combined_histo: [HistogramLiteral; 2] = [HistogramLiteral { data_: [0; 256], total_count_: 0, bit_cost_: 0. }; 2];
        let mut combined_entropy: [f64; 2] = [0.; 2];
        let mut j: usize = 0;
        while j < 2 {
            let last_histogram_ix = (*self_0).last_histogram_ix_[j];
            combined_histo[j] = *histograms.offset((*self_0).curr_histogram_ix_ as isize);
            HistogramAddHistogramLiteral(&mut *combined_histo.as_mut_ptr().offset(j as isize), &mut *histograms.offset(last_histogram_ix as isize));
            combined_entropy[j] = BitsEntropy(&mut *((*combined_histo.as_mut_ptr().offset(j as isize)).data_).as_mut_ptr().offset(0), (*self_0).alphabet_size_);
            j = j.wrapping_add(1);
        }
        (*self_0).split_threshold_ = combined_entropy[0] - entropy - *last_entropy.offset(0);
    }
}
pub unsafe fn run(self_0: *mut BlockSplitterLiteral) { BlockSplitterFinishBlockLiteral(self_0, 0); BlockSplitterFinishBlockLiteral(self_0, 1); }
"###;
fn metablock_fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case)]\n{ENTROPY}\n{METABLOCK}"
    )
}
#[test]
fn w5c_thin_count_runtime_field_count_admits_array_sources() {
    // The two `data_.as_ptr()` sites alone: `alphabet_size_` is a runtime field.
    let input = metablock_fixture().replace(
        "combined_entropy[j] = BitsEntropy(&mut *((*combined_histo.as_mut_ptr().offset(j as isize)).data_).as_mut_ptr().offset(0), (*self_0).alphabet_size_);",
        "combined_entropy[j] = combined_histo[j].bit_cost_;",
    );
    let p = proof(&input).unwrap();
    assert_eq!(
        (p.count_parameter, p.callers, p.count),
        (1, 2, super::thin_counted::Count::Runtime)
    );
    let table = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        crate::bo_rewriter::decide_table(tcx).unwrap()
    })
    .unwrap();
    for label in ["BitsEntropy::population", "ShannonEntropy::population"] {
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.label == label)
            .unwrap();
        assert!(
            matches!(decision, super::Decision::Slice { mutable: false, .. }),
            "{label}: {decision:?}"
        );
    }
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    assert!(emitted.contains("population: &[u32]"));
    let flat = emitted.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains(
            "BitsEntropy(core::slice::from_raw_parts(((*histograms.offset(0)).data_).as_ptr(), ((*self_0).alphabet_size_) as usize), (*self_0).alphabet_size_)"
        ),
        "{emitted}"
    );
    assert!(
        flat.contains("population.len().checked_sub(size as usize)"),
        "{emitted}"
    );
    assert!(!emitted.contains("FALLBACK_SLICE_EXTENT"));
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    if let Ok(root) = std::env::var("CRAT_W5C_FIXTURE_CAPTURE") {
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(format!("{root}/metablock-original.rs"), &input).unwrap();
        std::fs::write(format!("{root}/metablock-emitted.rs"), &emitted).unwrap();
    }
}
#[test]
fn w5c_thin_count_first_element_reference_source_delivers_over_the_array_start() {
    // c2rust's `&a[0]` at the third metablock site: the seam renders the array
    // start, never a one-element `slice::from_ref` (W-C6).
    let input = metablock_fixture();
    let p = proof(&input).unwrap();
    assert_eq!(
        (p.count_parameter, p.callers, p.count),
        (1, 3, super::thin_counted::Count::Runtime)
    );
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let flat = emitted.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("population: &[u32]"), "{emitted}");
    // On the call, not the file: slicecursor's verbatim prelude carries a
    // `slice::from_ref` helper once a cursor wrapper survives.
    assert!(
        !flat.contains("BitsEntropy(core::slice::from_ref"),
        "{emitted}"
    );
    assert!(
        flat.contains("BitsEntropy(core::slice::from_raw_parts(((*combined_histo.as_mut_ptr().offset(j as isize)).data_).as_mut_ptr(), ((*self_0).alphabet_size_) as usize), (*self_0).alphabet_size_)"),
        "{emitted}"
    );
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    if let Ok(root) = std::env::var("CRAT_W5C_FIXTURE_CAPTURE") {
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(format!("{root}/metablock-full-original.rs"), &input).unwrap();
        std::fs::write(format!("{root}/metablock-full-emitted.rs"), &emitted).unwrap();
    }
}
#[test]
fn w5c_thin_count_offset_zero_array_start_source() {
    use super::thin_counted::Hold;
    let start =
        fixture(18, "run").replace("depth_histo.as_ptr()", "depth_histo.as_ptr().offset(0)");
    let p = proof(&start).unwrap();
    assert_eq!(
        (p.callers, p.count),
        (1, super::thin_counted::Count::Constant)
    );
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&start).unwrap();
    assert!(emitted.contains("population: &[u32]"));
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    let past = fixture(18, "run").replace("depth_histo.as_ptr()", "depth_histo.as_ptr().offset(1)");
    assert_eq!(proof(&past).unwrap_err(), Hold::CallerSource);
}

/// The `encode` histogram copy: `ShouldCompress` forwards its 256-array with
/// the constant count, and `ShouldUseComplexStaticContextMap` calls the reader
/// DIRECTLY with c2rust's `&a[0]` over a nested array (`[[u32; 32]; 13]`) and
/// the constant 32 — the corpus `caller-source` hold of report 009 §5.
const ENCODE_CONTEXT: &str = r###"
unsafe extern "C" fn ShouldUseComplexStaticContextMap(mut input: *const u8, mut start_pos: usize,
    mut length: usize, mut mask: usize) -> i32 {
    let mut entropy: [f64; 3] = [0.; 3];
    let mut context_histo: [[u32; 32]; 13] = [[0; 32]; 13];
    let mut i: usize = 0;
    let mut dummy: usize = 0;
    let end_pos = start_pos.wrapping_add(length);
    while start_pos.wrapping_add(64) <= end_pos {
        let stride_end_pos = start_pos.wrapping_add(64);
        let mut context = 0usize;
        let mut pos = start_pos.wrapping_add(1);
        while pos < stride_end_pos {
            let data = *input.offset((pos & mask) as isize);
            context = (data as usize) & 7;
            context_histo[context][(data >> 3) as usize & 31] =
                context_histo[context][(data >> 3) as usize & 31].wrapping_add(1);
            pos = pos.wrapping_add(1);
        }
        start_pos = start_pos.wrapping_add(4096);
    }
    entropy[2] = 0.0;
    i = 0;
    while i < 13 {
        entropy[2] += ShannonEntropy(&mut *(*context_histo.as_mut_ptr().offset(i as isize)).as_mut_ptr().offset(0), 32usize, &mut dummy);
        i = i.wrapping_add(1);
    }
    (entropy[2] > 0.0) as i32
}
"###;
const SHOULD_COMPRESS: &str = r###"
unsafe extern "C" fn ShouldCompress(mut data: *const u8,
    mask: usize, last_flush_pos: u64, bytes: usize,
    num_literals: usize, num_commands: usize) -> i32 {
    if bytes <= 2 as i32 as usize {
        return 0 as i32;
    }
    if num_commands <
            (bytes >>
                        8 as
                            i32).wrapping_add(2 as i32 as usize)
        {
        if num_literals as f64 >
                0.99f64 * bytes as f64 {
            let mut literal_histo: [u32; 256] =
                [0 as i32 as u32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0];
            static mut kSampleRate: u32 =
                13 as i32 as u32;
            static mut kMinEntropy: f64 = 7.92f64;
            let bit_cost_threshold =
                bytes as f64 * kMinEntropy /
                    kSampleRate as f64;
            let mut t =
                bytes.wrapping_add(kSampleRate as
                                usize).wrapping_sub(1 as i32 as
                            usize).wrapping_div(kSampleRate as usize);
            let mut pos = last_flush_pos as u32;
            let mut i: usize = 0;
            i = 0 as i32 as usize;
            while i < t {
                literal_histo[*data.offset((pos as usize & mask) as
                                        isize) as usize] =
                    (literal_histo[*data.offset((pos as usize & mask) as
                                                isize) as usize]).wrapping_add(1);
                pos =
                    (pos as u32).wrapping_add(kSampleRate) as u32
                        as u32;
                i = i.wrapping_add(1);
            }
            if BitsEntropy(literal_histo.as_ptr(),
                        256 as i32 as usize) > bit_cost_threshold {
                return 0 as i32;
            }
        }
    }
    return 1 as i32;
}
"###;
fn encode_fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_upper_case_globals)]\n{ENTROPY}\n{SHOULD_COMPRESS}\n{ENCODE_CONTEXT}\npub unsafe fn run(data:*const u8)->i32 {{ ShouldCompress(data, 1023, 0, 1000, 999, 3) + ShouldUseComplexStaticContextMap(data, 0, 1000, 1023) }}"
    )
}
#[test]
fn w5c_thin_count_direct_reader_caller_over_a_nested_array_start() {
    let input = encode_fixture();
    let p = proof(&input).unwrap();
    assert_eq!(
        (p.count_parameter, p.callers, p.count),
        (1, 1, super::thin_counted::Count::Constant)
    );
    let table = ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        crate::bo_rewriter::decide_table(tcx).unwrap()
    })
    .unwrap();
    for label in ["BitsEntropy::population", "ShannonEntropy::population"] {
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.label == label)
            .unwrap();
        assert!(
            matches!(decision, super::Decision::Slice { mutable: false, .. }),
            "{label}: {decision:?}"
        );
    }
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let flat = emitted.split_whitespace().collect::<Vec<_>>().join(" ");
    // (The driver's own thin `data` still takes g24's `from_ref`; the two
    // histogram calls below are what this witness is about.)
    assert!(
        !flat.contains("ShannonEntropy(core::slice::from_ref"),
        "{emitted}"
    );
    assert!(flat.contains("ShannonEntropy(core::slice::from_raw_parts((*context_histo.as_mut_ptr().offset(i as isize)).as_mut_ptr(), (32usize) as usize), 32usize, &mut dummy)"), "{emitted}");
    assert!(flat.contains("BitsEntropy(core::slice::from_raw_parts(literal_histo.as_ptr(), (256 as i32 as usize) as usize), 256 as i32 as usize)"), "{emitted}");
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
    if let Ok(root) = std::env::var("CRAT_W5C_FIXTURE_CAPTURE") {
        std::fs::create_dir_all(&root).unwrap();
        std::fs::write(format!("{root}/encode-context-original.rs"), &input).unwrap();
        std::fs::write(format!("{root}/encode-context-emitted.rs"), &emitted).unwrap();
    }
}
