//! Native two-half counted-source witnesses, derived from brotli entropy chains.
const ENTROPY: &str = r###"
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
    let unknown = fixture(18, "run").replace("18usize)", "opaque())")
        + "\nunsafe fn opaque()->usize {static mut N:usize=18;N}";
    assert_eq!(proof(&unknown).unwrap_err(), Hold::CallerCount);
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
