//! R379-6 evidence checkpoint. No nested emission or alias proof is installed.
//! The three requested_* tests are explicit RED work items, not standing pins.

use std::sync::OnceLock;

use super::{A5Mode, SlotKind, SlotRef, WholeProgramAttestation, decision::Decision};

#[allow(dead_code, unused_assignments, unused_mut)]
#[path = "wave5d_ti_abs.rs"]
mod original;

const SOURCE: &str = include_str!("wave5d_ti_abs.rs");
const PAIRS: &str = include_str!("wave5d_accepted_pairs.tsv");
const CONSTRUCTIONS: &str = include_str!("wave5d_accepted_constructions.tsv");
const ARM_OUTCOMES: &str = include_str!("wave5d_accepted_arm_outcomes.tsv");

fn emitted() -> &'static str {
    static SOURCE_AFTER: OnceLock<String> = OnceLock::new();
    SOURCE_AFTER.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("crat-wave5d-abs-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("lib.rs");
        std::fs::write(&root, SOURCE).unwrap();
        let outcome = super::rewrite_m1_path_a5_injected(
            &root,
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            &|_| {},
        );
        std::fs::remove_dir_all(&dir).unwrap();
        let super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        } = outcome
        else {
            panic!("W-D-ABS emission unavailable; compiler diagnostics precede this assertion");
        };
        assert_eq!(reverted_count, 0);
        println!("W-D-ABS-EMITTED\n{source}\nW-D-ABS-END");
        source
    })
}

#[test]
fn w5d_native_abs_market_keeps_both_depths_ref() {
    ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let mut count = 0;
        for (s, decision) in &table.entries {
            if tcx.def_path_str(s.fn_did.to_def_id()) != "indicators::abs::ti_abs" {
                continue;
            }
            if !matches!(s.param_name.as_deref(), Some("inputs" | "outputs")) {
                continue;
            }
            assert_eq!(s.ptr_depth, 2);
            let body = tcx
                .mir_drops_elaborated_and_const_checked(s.fn_did)
                .borrow();
            let count_ty = body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty;
            assert_eq!(count_ty.to_string(), "i32", "signed C size argument");
            println!(
                "W-D-EXTENT count=_1 type={count_ty}; outer table demand=1; inner access bound=size"
            );
            for depth in 0..2 {
                let slot = ctx.slots.fn_local_slots[&s.fn_did]
                    .slot_for_local_depth(s.local, depth)
                    .unwrap();
                let kind = ctx.model.get(&SlotRef::Local(s.fn_did, slot));
                println!("W-D-ABS-KIND {} depth={depth} kind={kind:?}", s.label);
                assert_eq!(kind, Some(&SlotKind::Ref), "no injected model kinds");
            }
            assert!(matches!(decision, Decision::Slice { .. }), "{decision:?}");
            count += 1;
        }
        assert_eq!(count, 2);
    })
    .unwrap();
}

#[test]
fn w5d_storage_negative_retains_raw_elements_without_reinterpretation() {
    let source = emitted();
    assert!(
        source.contains("&[*const std::os::raw::c_double]"),
        "{source}"
    );
    assert!(
        source.contains("&[*mut std::os::raw::c_double]"),
        "{source}"
    );
    assert!(!source.contains("as *const &["));
    assert!(!source.contains("as *mut &mut ["));
}

#[test]
fn w5d_requested_whole_chain_is_red_before_storage_admission() {
    assert!(
        emitted().contains("&[&[std::os::raw::c_double]]"),
        "W-D-STORAGE: nested storage not admitted"
    );
}

#[test]
fn w5d_requested_inner_extent_is_red_before_relocation() {
    let source = emitted();
    let helper = source
        .split("fn __crat_safe_ti_abs(")
        .nth(1)
        .expect("real raw ABI wrapper");
    assert!(
        !helper.contains("crate::FALLBACK_SLICE_EXTENT"),
        "W-D-EXTENT: fabricated inner extents remain"
    );
}

#[test]
fn w5d_nonpositive_source_control_keeps_dormant_nulls() {
    let inputs = [std::ptr::null::<f64>()];
    let outputs = [std::ptr::null_mut::<f64>()];
    for size in [i32::MIN, -1, 0] {
        // Safety: both pointer-table cells are initialized and readable. The
        // original loop executes zero times, so no inner pointer is accessed.
        let result = unsafe {
            original::INDICATOR.indicator.unwrap()(
                size,
                inputs.as_ptr(),
                std::ptr::null(),
                outputs.as_ptr(),
            )
        };
        assert_eq!(result, 0);
    }
}

#[test]
fn w5d_source_controls_use_size_and_allow_in_place_data() {
    let mut output = [0.0; 3];
    let input = [-3.0, 2.0, -1.0];
    let inputs = [input.as_ptr()];
    let outputs = [output.as_mut_ptr()];
    // Safety: one readable pointer in each table and three initialized doubles
    // in each pointed-to array, with the output writable for this call.
    unsafe {
        original::INDICATOR.indicator.unwrap()(
            3,
            inputs.as_ptr(),
            std::ptr::null(),
            outputs.as_ptr(),
        );
    }
    assert_eq!(output, [3.0, 2.0, 1.0]);
    let mut same = [-3.0, 2.0, -1.0];
    let raw = same.as_mut_ptr();
    let inputs = [raw.cast_const()];
    let outputs = [raw];
    // Safety: the source uses raw pointers, reads element i before replacing
    // element i, and accesses only the three initialized writable elements.
    unsafe {
        original::INDICATOR.indicator.unwrap()(
            3,
            inputs.as_ptr(),
            std::ptr::null(),
            outputs.as_ptr(),
        );
    }
    assert_eq!(same, [3.0, 2.0, 1.0]);
}

#[derive(Debug, PartialEq, Eq)]
enum EvidenceHold {
    InheritedPairAbsent {
        input_formation: &'static str,
        output_formation: &'static str,
    },
}

fn inherited_pair_at_local_formations() -> Result<(), EvidenceHold> {
    // Frozen evidence checkpoint only. No pair verdict may be reconstructed
    // from terminal slice delivery or a formation/extent receipt.
    assert_eq!(
        PAIRS.lines().count(),
        1,
        "re-audit if the frozen pair inventory changes"
    );
    Err(EvidenceHold::InheritedPairAbsent {
        input_formation: "local:79:6:hir:79:17:depth=0",
        output_formation: "local:79:11:hir:79:41:depth=0",
    })
}

#[test]
fn w5d_missing_inherited_pair_is_typed_while_outer_delivery_stays() {
    assert_eq!(
        CONSTRUCTIONS.lines().count(),
        5,
        "two planned and two applied"
    );
    assert_eq!(
        ARM_OUTCOMES.lines().count(),
        6,
        "all five delivered subject rows"
    );
    assert!(CONSTRUCTIONS.contains("hir:79:17"));
    assert!(CONSTRUCTIONS.contains("hir:79:41"));
    let pair_column = ARM_OUTCOMES
        .lines()
        .next()
        .unwrap()
        .split('\t')
        .position(|column| column == "pair_state")
        .unwrap();
    assert!(
        ARM_OUTCOMES
            .lines()
            .skip(1)
            .all(|row| row.split('\t').nth(pair_column) == Some("not-required"))
    );
    let waiver_column = CONSTRUCTIONS
        .lines()
        .next()
        .unwrap()
        .split('\t')
        .position(|column| column == "waiver_id")
        .unwrap();
    assert!(
        CONSTRUCTIONS
            .lines()
            .skip(1)
            .all(|row| row.split('\t').nth(waiver_column)
                == Some("slice-extent-out-of-scope@addendum-77"))
    );
    assert!(matches!(
        inherited_pair_at_local_formations(),
        Err(EvidenceHold::InheritedPairAbsent { .. })
    ));
}

#[test]
fn w5d_requested_pair_evidence_is_red_at_the_existing_rows() {
    assert!(
        inherited_pair_at_local_formations().is_ok(),
        "W-D-PAIR: no inherited local formation pair verdict"
    );
}

#[test]
fn w5d_source_control_allows_partial_overlap_without_a_reference_pair() {
    let mut data = [-3.0, 2.0, -1.0, 4.0];
    let raw = data.as_mut_ptr();
    let inputs = [raw.cast_const()];
    // Safety: the output starts at element one of a four-element array; three
    // writes and three reads stay in that array. No reference pair is formed.
    let outputs = [unsafe { raw.add(1) }];
    unsafe {
        original::INDICATOR.indicator.unwrap()(
            3,
            inputs.as_ptr(),
            std::ptr::null(),
            outputs.as_ptr(),
        );
    }
    assert_eq!(data, [-3.0, 3.0, 3.0, 3.0]);
}
