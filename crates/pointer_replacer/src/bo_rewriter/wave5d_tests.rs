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
        println!("W5D-NATIVE-PLANS {:?}", table.nested_receipts);
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
            assert!(
                matches!(
                    decision,
                    Decision::Slice { .. } | Decision::NestedSlice { .. }
                ),
                "{decision:?}"
            );
            count += 1;
        }
        assert_eq!(count, 2);
    })
    .unwrap();
}

fn held_native(source: &str) {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let receipt = table
            .nested_receipts
            .iter()
            .find(|r| tcx.def_path_str(r.owner.to_def_id()) == "indicators::abs::ti_abs")
            .expect("typed nested outcome");
        println!("W5D-HELD {:?}", receipt.result);
        // Relay 042 (ruling (A) round 2): the claim is that the PAIR arm does
        // not admit `ti_abs`. A receipt carrying another producer's plan
        // (R435-1's N1, `count_guard == false`) is not this arm admitting it.
        assert!(
            receipt.result.as_ref().map_or(true, |p| !p.count_guard),
            "the pair arm must not admit: {:?}",
            receipt.result
        );
        // **Relay 041 ruling (A).** Scoped to `ti_abs`'s own subjects. While the
        // pair rule was the only nested producer this was the same statement as
        // the receipt check above; R435-1 chartered a second one (the `nested`
        // lane's N1), and a `NestedSlice` decision in ANOTHER owner is not what
        // this control is about.
        assert!(
            !table
                .entries
                .iter()
                .any(|(s, d)| matches!(d, Decision::NestedSlice { .. })
                    && tcx.def_path_str(s.fn_did.to_def_id()) == "indicators::abs::ti_abs")
        );
    })
    .unwrap();
}

#[test]
fn w5d_storage_negative_retains_raw_elements_without_reinterpretation() {
    let source = SOURCE.replace(
        "while i < size {",
        "* (outputs as *mut *mut std::os::raw::c_double) = output; while i < size {",
    );
    // **Relay 041 ruling (A).** This control is about the `outputs` table — the
    // one the mutation writes through — so it is pinned to that subject. N1
    // REFUSES `outputs` here (which is the control's point) and admits the
    // sibling `inputs`; an owner-wide assertion would read that sibling as a
    // failure of this control.
    held_native_subject(&source, "outputs");
}

/// `held_native`, narrowed to ONE parameter of `ti_abs`.
fn held_native_subject(source: &str, parameter: &str) {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        assert!(
            !table
                .entries
                .iter()
                .any(|(s, d)| matches!(d, Decision::NestedSlice { .. })
                    && tcx.def_path_str(s.fn_did.to_def_id()) == "indicators::abs::ti_abs"
                    && s.param_name.as_deref() == Some(parameter)),
            "{parameter} must not be admitted as a nested slice"
        );
    })
    .unwrap();
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

fn inherited_pair_at_local_formations(required: bool) -> Result<(), EvidenceHold> {
    // Frozen evidence checkpoint only. No pair verdict may be reconstructed
    // from terminal slice delivery or a formation/extent receipt.
    assert_eq!(
        PAIRS.lines().count(),
        1,
        "re-audit if the frozen pair inventory changes"
    );
    if !required {
        return Ok(());
    }
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
        inherited_pair_at_local_formations(true),
        Err(EvidenceHold::InheritedPairAbsent { .. })
    ));
}

#[test]
fn w5d_requested_pair_evidence_is_red_at_the_existing_rows() {
    assert!(
        inherited_pair_at_local_formations(false).is_ok(),
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

#[test]
fn w5d_count_rebinding_is_not_an_extent() {
    held_native(&SOURCE.replace("i += 1", "size += 1; i += 1"));
}
#[test]
fn w5d_narrowed_index_is_not_the_original_count() {
    held_native(&SOURCE.replace("i as isize", "(i as u8) as isize"));
}
#[test]
fn w5d_index_increment_before_access_is_held() {
    held_native(
        &SOURCE
            .replace(
                "*output.offset(i as isize) =",
                "i += 1; *output.offset(i as isize) =",
            )
            .replace("                i += 1\n", ""),
    );
}
#[test]
fn w5d_conditional_increment_is_held() {
    held_native(&SOURCE.replace("i += 1", "if size > 1 { i += 1; }"));
}
#[test]
fn w5d_generated_parameter_collision_is_held() {
    held_native(&SOURCE.replace("mut options:", "mut __crat_nested_33_raw:"));
}
#[test]
fn w5d_count_mutating_method_is_held() {
    let source = SOURCE.replace("i += 1", "size.clone_from(&1); i += 1");
    held_native(&source);
}
#[test]
fn w5d_closure_capture_is_held() {
    held_native(&SOURCE.replace(
        "i += 1",
        "let mut update = || { size += 1; }; update(); i += 1",
    ));
}

#[test]
fn w5d_preloop_side_effect_is_not_skipped_on_nonpositive_size() {
    let source = format!(
        "static mut STATE: i32 = 1;\n{}",
        SOURCE.replace("let mut in1:", "crate::STATE = 0; let mut in1:")
    );
    held_native(&source);
}

#[test]
fn w5d_each_nested_subject_withdraws_the_whole_function() {
    ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).unwrap();
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let plan = table
            .nested_receipts
            .iter()
            .find_map(|r| r.result.as_ref().ok())
            .expect("native nested plan");
        for node in plan.required_nodes() {
            let mut reverts = super::ast_transform::RevertSet::default();
            reverts.atom_subjects.insert((plan.owner, node));
            super::ast_transform::close_nested_reverts(&table, &mut reverts);
            let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx, &capture, &reverts, None, &table, None,
            )
            .expect("whole-class rollback, not partial nested output");
            let source = files.into_values().collect::<String>();
            assert!(!source.contains("__crat_nested_"), "{source}");
            assert!(!source.contains("fn __crat_safe_ti_abs"), "{source}");
            assert!(super::verify::type_checks_str(&source));
        }
    })
    .unwrap();
}

#[test]
fn w5d_nonpositive_emitted_path_and_typed_caller_execute() {
    let source = format!(
        r#"{}
fn main() {{
    let options = 0.0;
    let none_in = [::std::ptr::null::<f64>()];
    let none_out = [::std::ptr::null_mut::<f64>()];
    for n in [i32::MIN, -1, 0] {{
        unsafe {{ assert_eq!(INDICATOR.indicator.unwrap()(n, none_in.as_ptr(), ::std::ptr::null(), none_out.as_ptr()), 0); }}
    }}
    let input = [-3.0, 2.0, -1.0];
    let mut output = [0.0; 3];
    let inputs = [input.as_ptr()];
    let outputs = [output.as_mut_ptr()];
    unsafe {{ INDICATOR.indicator.unwrap()(3, inputs.as_ptr(), &options, outputs.as_ptr()); }}
    assert_eq!(output, [3.0, 2.0, 1.0]);
    output.fill(0.0);
    let inputs = [&input[..]];
    let mut outputs = [&mut output[..]];
    unsafe {{ indicators::abs::__crat_safe_ti_abs(3, &inputs, &options, &mut outputs); }}
    assert_eq!(output, [3.0, 2.0, 1.0]);
}}
"#,
        emitted()
    );
    let root = std::env::temp_dir().join(format!("crat-wave5d-runtime-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let input = root.join("main.rs");
    let binary = root.join("run");
    std::fs::write(&input, source).unwrap();
    let compiled = std::process::Command::new("rustc")
        .arg("--edition=2021")
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let run = std::process::Command::new(&binary).output().unwrap();
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn w5d_unbuilt_nested_seams_remain_typed() {
    use super::decision::seam::{Form, SeamBlock, glue};
    for mutable in [false, true] {
        for inner_mutable in [false, true] {
            let form = Form::NestedSlice {
                mutable,
                inner_mutable,
            };
            assert!(matches!(
                glue(Form::Raw, form, None),
                Err(SeamBlock::NestedBoundaryUnbuilt)
            ));
            assert!(matches!(
                glue(form, Form::Raw, None),
                Err(SeamBlock::NestedBoundaryUnbuilt)
            ));
        }
    }
}
#[test]
fn w5d_outer_optional_level_is_held_without_changing_null_kind() {
    held_native(&SOURCE.replace(
        "let mut in1:",
        "if inputs.is_null() { return 0; } let mut in1:",
    ));
}
#[test]
fn w5d_inner_optional_level_is_held_without_eager_construction() {
    held_native(&SOURCE.replace(
        "let mut output:",
        "if in1.is_null() { return 0; } let mut output:",
    ));
}
#[test]
fn w5d_inner_raw_access_boundary_is_not_flattened() {
    let source = SOURCE
        .replace(
            "fn fabs(value:",
            "fn sink(p: *const f64) -> f64; fn fabs(value:",
        )
        .replace("i += 1", "sink(in1); i += 1");
    held_native(&source);
}

#[test]
fn w5d_surface_atom_withdrawal_closes_both_nested_parameters() {
    ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).unwrap();
        let (mut table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let plan = table
            .nested_receipts
            .iter()
            .find_map(|r| r.result.as_ref().ok())
            .unwrap()
            .clone();
        for parameter in &plan.parameters {
            let argument = table
                .seams
                .surface_arguments
                .iter_mut()
                .find(|a| a.node == (plan.owner, parameter.hir))
                .unwrap();
            argument.atom_ids.push("w5d-withdrawal-control".into());
            let mut reverts = super::ast_transform::RevertSet::default();
            reverts.atom_names.insert("w5d-withdrawal-control".into());
            super::ast_transform::close_nested_reverts(&table, &mut reverts);
            assert!(reverts.fns.contains(&plan.owner));
            let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx, &capture, &reverts, None, &table, None,
            )
            .unwrap();
            let source = files.into_values().collect::<String>();
            assert!(!source.contains("__crat_nested_"));
            assert!(!source.contains("fn __crat_safe_ti_abs"));
            table
                .seams
                .surface_arguments
                .iter_mut()
                .find(|a| a.node == (plan.owner, parameter.hir))
                .unwrap()
                .atom_ids
                .clear();
        }
    })
    .unwrap();
}

#[test]
fn w5d_nonpositive_guard_precedes_all_inner_formations() {
    let source = emitted();
    let guard = source.find("if size <= 0").unwrap();
    let early_return = source.find("return 0").unwrap();
    let formation = source.find("::core::slice::from_raw_parts").unwrap();
    assert!(guard < early_return && early_return < formation);
}
#[test]
fn w5d_mutable_inner_access_is_an_explicit_reborrow() {
    let source = emitted().split_whitespace().collect::<String>();
    assert!(source.contains("=&mut*outputs[0]"), "{source}");
}
#[test]
fn w5d_required_pair_cannot_inherit_not_required() {
    use super::decision::{
        Arm, RequiredArmSet,
        nested_slice::{Hold, inherited_pair},
    };
    let empty = RequiredArmSet::default();
    assert_eq!(inherited_pair(empty), Ok(()));
    let mut required = empty;
    required.insert(Arm::Pair);
    assert_eq!(inherited_pair(required), Err(Hold::PairRequired));
}
