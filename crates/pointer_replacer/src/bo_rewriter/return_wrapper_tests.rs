//! J18 actual Option/Slice return-wrapper controls. No model or decision injection.

use std::collections::BTreeSet;

use rustc_middle::mir::RETURN_PLACE;
use sha2::{Digest, Sha256};

use super::{
    bridge_receipt::{
        BridgeExtentKind, BridgeReceiptEvent, BridgeReceiptStage, BridgeReceiptState,
        BridgeRetentionTier, SignatureClassId,
    },
    decision::{
        Decision,
        exposure::{ConfiguredExposureInput, ExposureSurfacePlan},
        lifetime::FnSignatureSlot,
    },
    delivery_custody::{TypeShape, inventory_source},
    mechanical_receipt::{
        FALLBACK_EXTENT_RECEIPT, MechanicalExtent, MechanicalObligationEvent, MechanicalStage,
        MechanicalState, MechanicalSubjectKey, SLICE_EXTENT_WAIVER_ID,
    },
};

#[derive(Clone, Copy, Debug)]
enum Family {
    Nullable,
    Slice,
}

fn input(family: Family) -> &'static str {
    // Exact existing return_family_tests programs, including their callers.
    match family {
        Family::Nullable => {
            r#"
            #![allow(dead_code, unused_unsafe)]
            unsafe fn target(p: *mut i32) -> *mut i32 {
                if !p.is_null() { *p += 1; }
                p
            }
            pub unsafe fn entry() -> i32 {
                let mut value = 3;
                let _ = target(&mut value);
                let _ = target(core::ptr::null_mut());
                value
            }
        "#
        }
        Family::Slice => {
            r#"
            #![allow(dead_code, unused_unsafe)]
            unsafe fn target(p: *mut i32) -> *mut i32 {
                *p.offset(1) += 1;
                p
            }
            pub unsafe fn entry() -> i32 {
                let mut values = [3, 5, 7];
                let _ = target(values.as_mut_ptr());
                values[1]
            }
        "#
        }
    }
}

struct Output {
    source: String,
    held: Option<String>,
    owner: SignatureClassId,
    parameter_local: u32,
    input_call_count: usize,
    events: Vec<BridgeReceiptEvent>,
    mechanical: Vec<MechanicalObligationEvent>,
    held_events: Vec<BridgeReceiptEvent>,
}

fn emit(family: Family, hold_owner: bool) -> Output {
    emit_source(input(family), family, hold_owner)
}

fn emit_source(source: &str, family: Family, hold_owner: bool) -> Output {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original wrapper AST");
        let configured_exposure = ConfiguredExposureInput::checked("fixture-config", ["target".to_owned()],
            format!("{:x}", Sha256::digest(b"target"))).expect("existing checked exposure mechanism");
        let (table, ctx) = super::decide_table_with_emission_config(tcx,
            Some((super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph))),
            &super::EmissionRunConfig { configured_exposure }).expect("one actual wrapper decision invocation");
        let solve = super::model_cache::solve_receipt();
        println!("J18 wrapper {family:?} hold={hold_owner}: solve={solve:#?}");
        assert!(solve.is_some(), "actual fixture solve receipt");
        let (subject, choice) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual returning parameter");
        for local in [subject.local, RETURN_PLACE] {
            let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
                .and_then(|slots| slots.slot_for_local_depth(local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)));
            assert_eq!(kind, Some(&super::SlotKind::Ref), "AUTHORING PREMISE: {family:?} source/return model-Ref");
        }
        assert!(match choice {
            Decision::Opt { mutable: true, slice: false, .. } => matches!(family, Family::Nullable),
            Decision::Slice { mutable: true, .. } => matches!(family, Family::Slice),
            Decision::Ref { .. } | Decision::InferredRef { .. } | Decision::Opt { .. }
            | Decision::Slice { .. } | Decision::Box(_) | Decision::Degraded(_) => false,
        }, "AUTHORING PREMISE: actual return family survives exposure: {choice:?}");
        let node = (subject.fn_did, subject.hir_id);
        let permit = ctx.lifetime_eligibility.return_permit(node).expect("actual native return permit");
        let lifetime = table.lifetime_plan.function(subject.fn_did).expect("actual tied return lifetime");
        let parameter_lifetime = lifetime.lifetime_for(FnSignatureSlot::arg(1, 0, 0)).expect("parameter lifetime");
        assert_eq!(lifetime.lifetime_for(FnSignatureSlot::RETURN), Some(parameter_lifetime));
        assert_eq!(table.exposure.as_ref().unwrap().plan(subject.fn_did), ExposureSurfacePlan::PositiveSeedShim);
        println!("J18 {family:?}: permit={permit:?}; lifetime={}", lifetime.receipt());
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual wrapper terminal plan");
        let owner = SignatureClassId::of(subject.fn_did);
        let input_call_count = ctx.facts.call_args.get(&subject.fn_did).map_or(0, Vec::len);
        assert!(emission.plan.class_finalization.classes.get(&owner)
            .is_some_and(super::plan::SignatureClassPlan::is_ready), "wrapper class must be Ready before rendering");
        let held = emission.plan.held_classes();
        assert!(!held.contains(&owner));
        let render = |reverted: &BTreeSet<SignatureClassId>| {
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(reverted, &BTreeSet::new(), &table)
                .expect("actual owner revert set");
            let (files, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
                emission.plan.root_file.as_ref(), &table, Some(&emission.plan.terminal_call_plans))
                .expect("actual wrapper AST rendering");
            assert_eq!(files.len(), 1);
            files.into_values().next().unwrap()
        };
        let source = render(&held);
        let events = emission.plan.bridge_events(&held);
        let mechanical = emission.plan.mechanical_receipts(&held).0;
        println!("J18 {family:?} wrapper output:\n{source}\ncommon={events:#?}\nmechanical={mechanical:#?}");
        let mut held_events = Vec::new();
        let held_source = hold_owner.then(|| {
            let mut reverted = held.clone();
            reverted.insert(owner);
            held_events = emission.plan.bridge_events(&reverted);
            render(&reverted)
        });
        Output { source, held: held_source, owner, parameter_local: subject.local.as_u32(), input_call_count,
            events, mechanical, held_events }
    }).expect("unchanged owned-storage wrapper fixture compiles")
}

fn full_type(shape: &TypeShape, family: Family) -> bool {
    let reference = match (family, shape) {
        (Family::Nullable, TypeShape::Option { payload, .. }) => &**payload,
        (Family::Slice, _) => shape,
        _ => return false,
    };
    let TypeShape::Reference {
        mutable: true,
        pointee,
    } = reference
    else {
        return false;
    };
    match (family, &**pointee) {
        (Family::Nullable, TypeShape::Named { path }) => path == "i32",
        (Family::Slice, TypeShape::Slice { element }) => {
            matches!(&**element, TypeShape::Named { path } if path == "i32")
        }
        _ => false,
    }
}

fn require_result_type(output: &Output, family: Family) {
    let declarations =
        inventory_source("return-wrapper.rs", &output.source).expect("actual wrapper declarations");
    let result = declarations
        .iter()
        .filter(|row| row.owner == "target" && row.binding == "__crat_result")
        .collect::<Vec<_>>();
    let [result] = result.as_slice() else { panic!("exactly one actual wrapper result temporary") };
    assert!(
        result.type_is_fully_explicit && full_type(&result.type_shape, family),
        "the wrapper result must retain the complete {family:?} return form: {result:?}"
    );
    let inner = declarations
        .iter()
        .find(|row| {
            row.owner == "__crat_safe_target"
                && row.binding == "p"
                && row.parameter_index == Some(1)
        })
        .expect("actual generated inner parameter");
    assert!(full_type(&inner.type_shape, family), "{inner:?}");
    let wrapper = declarations
        .iter()
        .find(|row| row.owner == "target" && row.binding == "p" && row.parameter_index == Some(1))
        .expect("original raw wrapper parameter");
    assert!(matches!(
        wrapper.type_shape,
        TypeShape::RawPointer { mutable: true, .. }
    ));
}

#[test]
fn return_wrapper_nullable_result_keeps_its_full_option_type() {
    let output = emit(Family::Nullable, false);
    let type_checks = super::verify::type_checks_str(&output.source);
    println!("J18 nullable output type-checks: {type_checks}");
    require_result_type(&output, Family::Nullable);
    assert!(
        type_checks,
        "actual nullable wrapper must type/borrow-check:\n{}",
        output.source
    );
}

fn require_slice_extent(output: &Output) {
    assert_eq!(
        output.source.matches("const FALLBACK_SLICE_EXTENT").count(),
        1,
        "the generated wrapper's extent must have exactly one definition:\n{}",
        output.source
    );
    let common = output
        .events
        .iter()
        .filter(|event| {
            event.site.owner_class == output.owner
                && event.site.arm == "surface"
                && event.site.position == "generated-wrapper-arg0"
                && event.stage == BridgeReceiptStage::Terminal
                && event.extent == BridgeExtentKind::Fallback
        })
        .collect::<Vec<_>>();
    let [common] = common.as_slice() else {
        panic!(
            "one exact typed surface fallback receipt: {:?}",
            output.events
        )
    };
    assert_eq!(common.state, BridgeReceiptState::Applied);
    assert_eq!(common.retention, BridgeRetentionTier::T1);
    assert!(
        common.waiver_id.is_none(),
        "extent waiver must not occupy the retention waiver column"
    );
    let mechanical = output
        .mechanical
        .iter()
        .filter(|event| {
            event.stage == MechanicalStage::Terminal
                && event.argument_kind == "generated-wrapper-argument"
                && event.key.site.argument_index == Some(0)
                && matches!(&event.key.subject, MechanicalSubjectKey::Local { owner, mir_local, .. }
            if *owner == output.owner.local_def_id() && *mir_local == output.parameter_local)
                && event.evidence.extent.is_fallback()
        })
        .collect::<Vec<_>>();
    let [receipt] = mechanical.as_slice() else {
        panic!(
            "one parameter-owned mechanical fallback receipt: {:?}",
            output.mechanical
        )
    };
    assert_eq!(receipt.state, MechanicalState::Applied);
    let MechanicalExtent::Fallback {
        receipt, waiver_id, ..
    } = &receipt.evidence.extent
    else {
        unreachable!()
    };
    assert_eq!(receipt, FALLBACK_EXTENT_RECEIPT);
    assert_eq!(waiver_id, SLICE_EXTENT_WAIVER_ID);
}

#[test]
fn return_wrapper_slice_result_and_parameter_have_receipted_extent() {
    let output = emit(Family::Slice, false);
    let type_checks = super::verify::type_checks_str(&output.source);
    println!("J18 slice output type-checks: {type_checks}");
    require_slice_extent(&output);
    require_result_type(&output, Family::Slice);
    assert!(
        type_checks,
        "actual slice wrapper must type/borrow-check:\n{}",
        output.source
    );
}

#[test]
fn return_wrapper_only_slice_owns_its_fallback_constant_and_receipt() {
    // Same existing target body, deliberately without an internal caller.
    // This is an actual model-premise probe, not a constructed consumer table.
    let source = r#"
            #![allow(dead_code, unused_unsafe)]
            unsafe fn target(p: *mut i32) -> *mut i32 {
                *p.offset(1) += 1;
                p
            }
        "#;
    let output = emit_source(source, Family::Slice, false);
    assert_eq!(
        output.input_call_count, 0,
        "AUTHORING PREMISE: no ordinary call site may supply the wrapper's fallback"
    );
    assert!(
        !output
            .events
            .iter()
            .any(|event| event.stage == BridgeReceiptStage::Terminal
                && event.extent == BridgeExtentKind::Fallback
                && event.site.arm != "surface"),
        "an ordinary fallback receipt would mask this wrapper-only control: {:?}",
        output.events
    );
    let type_checks = super::verify::type_checks_str(&output.source);
    println!("J18 wrapper-only slice: no internal calls; output type-checks={type_checks}");
    require_slice_extent(&output);
    require_result_type(&output, Family::Slice);
    assert!(
        type_checks,
        "actual wrapper-only source must type/borrow-check:\n{}",
        output.source
    );
}

#[test]
fn return_wrapper_owner_revert_restores_raw_function_and_drops_receipts() {
    let output = emit(Family::Slice, true);
    assert!(
        output.source.contains("fn __crat_safe_target"),
        "baseline actually generated the inner function"
    );
    let before = output
        .events
        .iter()
        .filter(|event| {
            event.site.owner_class == output.owner && event.stage == BridgeReceiptStage::Terminal
        })
        .collect::<Vec<_>>();
    assert!(
        !before.is_empty()
            && before
                .iter()
                .all(|event| event.state == BridgeReceiptState::Applied)
    );
    let after = output
        .held_events
        .iter()
        .filter(|event| {
            event.site.owner_class == output.owner && event.stage == BridgeReceiptStage::Terminal
        })
        .collect::<Vec<_>>();
    assert_eq!(after.len(), before.len());
    assert!(
        after
            .iter()
            .all(|event| event.state == BridgeReceiptState::Dropped)
    );
    for event in before {
        assert!(after.iter().any(|after| after.site == event.site));
    }
    let held = output.held.as_ref().unwrap();
    assert!(
        super::verify::type_checks_str(held),
        "held original raw function must type-check:\n{held}"
    );
    assert!(!held.contains("__crat_safe_target") && !held.contains("__crat_result"));
    assert!(
        held.contains("fn target(p: *mut i32) -> *mut i32") && held.contains("*p.offset(1) += 1;"),
        "{held}"
    );
    let declarations = inventory_source("held-return-wrapper.rs", held).unwrap();
    let parameter = declarations
        .iter()
        .find(|row| row.owner == "target" && row.binding == "p" && row.parameter_index == Some(1))
        .expect("retained original raw parameter");
    assert!(matches!(
        parameter.type_shape,
        TypeShape::RawPointer { mutable: true, .. }
    ));
    assert_eq!(
        held.matches("const FALLBACK_SLICE_EXTENT").count(),
        0,
        "no held wrapper extent survives"
    );
}

#[test]
fn return_wrapper_nonreturn_parameter_atom_drops_only_its_construction() {
    check_nonreturn_parameter_atom(false);
}

#[test]
fn return_wrapper_missing_selected_input_receipt_map_is_caught() {
    check_nonreturn_parameter_atom(true);
}

fn check_nonreturn_parameter_atom(check_missing_receipt: bool) {
    let source = "#![allow(dead_code, unused_unsafe)]\n\
        extern \"C\" { fn strlen(p: *const i8) -> usize; }\n\
        unsafe fn target(p: *mut i8) -> i8 { *p.offset(1) += 1; let _ = strlen(p); *p }\n\
        pub unsafe fn entry() -> i8 {\n\
            let mut storage: [i8; 3] = [65, 66, 0]; target(storage.as_mut_ptr())\n\
        }\n";
    let (baseline, atom_output, common_state, unsafe_state, mechanical_dropped, receipt_map_fault) =
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let capture = super::ast_transform::capture_ast(tcx).expect("one nonreturn original AST");
            let configured_exposure = ConfiguredExposureInput::checked("fixture-config", ["target".to_owned()],
                format!("{:x}", Sha256::digest(b"target"))).expect("checked target exposure");
            let (table, ctx) = super::decide_table_with_emission_config(tcx,
                Some((super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph))),
                &super::EmissionRunConfig { configured_exposure }).expect("one actual nonreturn decision call");
            let solve = super::model_cache::solve_receipt();
            println!("J18 nonreturn parameter-atom solve={solve:#?}");
            assert!(solve.is_some(), "actual fixture solve receipt");
            let (subject, choice) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
                .expect("actual target parameter");
            let slot = ctx.slots.fn_local_slots.get(&subject.fn_did)
                .and_then(|slots| slots.slot_for_local_depth(subject.local, 0)).expect("actual source slot");
            assert_eq!(ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)), Some(&super::SlotKind::Ref),
                "AUTHORING PREMISE: actual source is model-Ref");
            assert!(matches!(choice, Decision::Slice { mutable: true, .. }),
                "AUTHORING PREMISE: actual mutable Slice source: {choice:?}");
            assert!(table.lifetime_plan.function(subject.fn_did)
                .is_none_or(|plan| plan.lifetime_for(FnSignatureSlot::RETURN).is_none()),
                "AUTHORING PREMISE: scalar output has no generated reference-return dependency");
            assert_eq!(table.exposure.as_ref().unwrap().plan(subject.fn_did), ExposureSurfacePlan::PositiveSeedShim);
            let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
                .expect("actual nonreturn surface plan");
            let owner = SignatureClassId::of(subject.fn_did);
            let held = emission.plan.held_classes();
            assert!(emission.plan.class_finalization.classes.get(&owner)
                .is_some_and(super::plan::SignatureClassPlan::is_ready));
            assert!(!held.contains(&owner));
            let node = (subject.fn_did, subject.hir_id);
            let seams = emission.plan.terminal_call_plans.seam_edits.iter().filter(|edit|
                edit.source_node == Some(node) && edit.raw_outbound.is_some()
                    && edit.bridge.callee == super::bridge_receipt::BridgeCalleeId::Foreign("strlen".into()))
                .collect::<Vec<_>>();
            let [strlen] = seams.as_slice() else { panic!("AUTHORING PREMISE: one exact strlen source site") };
            assert_eq!(strlen.bridge.retention, BridgeRetentionTier::T1);
            assert!(strlen.bridge.waiver_id.is_none());
            let [atom] = strlen.atom_ids.as_slice() else { panic!("AUTHORING PREMISE: one actual T1 source atom") };
            let atoms = BTreeSet::from([atom.clone()]);
            assert!(!emission.plan.effective_reverted_classes(&held, &atoms).contains(&owner),
                "this nonreturn atom must not acquire a return-owner class dependency");
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(&held, &atoms, &table).unwrap();
            assert!(reverts.keeps(owner));
            assert!(!reverts.keeps_subject(subject.fn_did, subject.hir_id));
            let source_file = tcx.sess.source_map().lookup_source_file(strlen.span.lo());
            let file = super::file_key(&source_file.name).unwrap();
            let original_files = std::collections::BTreeMap::from([(file, source.to_owned())]);
            let mut artifacts = super::RawBoundaryArtifacts {
                bridge_custody_export: super::bridge_custody_export::capture(tcx, &capture, &table, &emission.plan, &original_files),
                ..Default::default()
            };
            super::refresh_raw_boundary_receipt_events(&mut artifacts, &emission.plan, &held, &BTreeSet::new());
            let parameters = artifacts.bridge_events.iter().filter(|event| event.site.owner_class == owner
                && event.site.arm == "surface" && event.site.position == "generated-wrapper-arg0"
                && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            let [parameter] = parameters.as_slice() else { panic!("one actual surface parameter receipt") };
            assert_eq!(parameter.state, BridgeReceiptState::Applied);
            assert_eq!(parameter.extent, BridgeExtentKind::Fallback);
            let parameter_key = parameter.site.clone();
            let mechanical = artifacts.mechanical_events.iter().filter(|event| event.stage == MechanicalStage::Terminal
                && event.argument_kind == "generated-wrapper-argument" && event.key.site.argument_index == Some(0)
                && matches!(&event.key.subject, MechanicalSubjectKey::Local { owner, mir_local, .. }
                    if *owner == subject.fn_did && *mir_local == subject.local.as_u32()))
                .collect::<Vec<_>>();
            let [mechanical] = mechanical.as_slice() else { panic!("one actual typed parameter construction receipt") };
            assert_eq!(mechanical.state, MechanicalState::Applied);
            let mechanical_key = mechanical.key.clone();
            let unsafe_before = artifacts.unsafe_context_events.iter().filter(|event| event.site == parameter_key
                && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            let [unsafe_before] = unsafe_before.as_slice() else { panic!("one actual parameter unsafe-context receipt") };
            assert_eq!(unsafe_before.state, BridgeReceiptState::Applied);
            let render = |atoms: &BTreeSet<String>| {
                let (files, rollbacks, _, _) = super::round_files(tcx, &capture, &emission.plan,
                    &emission.texts, &held, atoms, emission.plan.root_file.as_ref(), &table)
                    .expect("actual parameter-atom round");
                assert!(rollbacks.is_empty());
                assert_eq!(files.len(), 1);
                files.into_values().next().unwrap()
            };
            let baseline = render(&BTreeSet::new());
            let atom_output = render(&atoms);
            let receipt_map_fault = if check_missing_receipt {
                let mut faulty = emission.plan.clone();
                assert!(!faulty.terminal_call_plans.callee_parameter_inputs.is_empty(),
                    "deliberate-fault premise: the actual target input plan exists");
                faulty.callee_parameter_input_receipts = Default::default();
                super::round_files(tcx, &capture, &faulty, &emission.texts, &held, &atoms,
                    faulty.root_file.as_ref(), &table).err()
            } else { None };
            super::refresh_raw_boundary_receipt_events(&mut artifacts, &emission.plan, &held, &atoms);
            let common = artifacts.bridge_events.iter().filter(|event| event.site == parameter_key
                && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            let [common] = common.as_slice() else { panic!("same exact parameter terminal receipt after atom") };
            let unsafe_after = artifacts.unsafe_context_events.iter().filter(|event| event.site == parameter_key
                && event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            let [unsafe_after] = unsafe_after.as_slice() else { panic!("same exact parameter unsafe receipt after atom") };
            let mechanical = artifacts.mechanical_events.iter().filter(|event| event.key == mechanical_key
                && event.stage == MechanicalStage::Terminal).collect::<Vec<_>>();
            let [mechanical] = mechanical.as_slice() else { panic!("same exact parameter construction after atom") };
            let mechanical_dropped = mechanical.state != MechanicalState::Applied && mechanical.terminal_reason.is_some();
            assert!(artifacts.bridge_events.iter().any(|event| event.site.owner_class == owner
                && event.site.bridge_kind == "surface-unsafe-context-inner-call"
                && event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Applied),
                "the wrapper's independent inner-call receipt remains live");
            println!("J18 nonreturn atom={atom}; common={common:?}; unsafe={unsafe_after:?}; mechanical={mechanical:?}\nBASELINE:\n{baseline}\nATOM:\n{atom_output}");
            (baseline, atom_output, common.state, unsafe_after.state, mechanical_dropped, receipt_map_fault)
        }).expect("caller-owned NUL-storage fixture compiles");
    let baseline_checks = super::verify::type_checks_str(&baseline);
    let atom_checks = super::verify::type_checks_str(&atom_output);
    println!(
        "J18 nonreturn outside-callback typechecks: baseline={baseline_checks}, atom={atom_checks}"
    );
    let baseline_declarations =
        inventory_source("nonreturn-wrapper-baseline.rs", &baseline).unwrap();
    let baseline_parameter = baseline_declarations
        .iter()
        .find(|row| {
            row.owner == "__crat_safe_target"
                && row.binding == "p"
                && row.parameter_index == Some(1)
        })
        .expect("actual live inner parameter");
    assert!(
        matches!(&baseline_parameter.type_shape, TypeShape::Reference { mutable: true, pointee }
        if matches!(&**pointee, TypeShape::Slice { .. })),
        "{baseline_parameter:?}"
    );
    let declarations = inventory_source("nonreturn-wrapper-atom.rs", &atom_output).unwrap();
    let parameter = declarations
        .iter()
        .find(|row| {
            row.owner == "__crat_safe_target"
                && row.binding == "p"
                && row.parameter_index == Some(1)
        })
        .expect("owner remains live with its generated inner definition");
    assert!(
        matches!(
            parameter.type_shape,
            TypeShape::RawPointer { mutable: true, .. }
        ),
        "{parameter:?}"
    );
    assert!(
        !atom_output.contains("from_raw_parts") && !atom_output.contains("FALLBACK_SLICE_EXTENT"),
        "an atom-reverted raw parameter has no surviving wrapper construction or extent:\n{atom_output}"
    );
    assert_eq!(common_state, BridgeReceiptState::Dropped);
    assert_eq!(unsafe_state, BridgeReceiptState::Dropped);
    assert!(
        mechanical_dropped,
        "the exact parameter construction must have a typed non-Applied terminal reason"
    );
    assert!(
        baseline_checks && atom_checks,
        "both actual output trees must type/borrow-check"
    );
    if check_missing_receipt {
        let reason = receipt_map_fault
            .expect("deliberate-fault check: missing selected receipt map must be caught");
        assert!(
            reason.starts_with("callee-parameter-input-custody:"),
            "{reason}"
        );
        println!("deliberate-fault check caught by selected input receipt custody: {reason}");
    }
}
