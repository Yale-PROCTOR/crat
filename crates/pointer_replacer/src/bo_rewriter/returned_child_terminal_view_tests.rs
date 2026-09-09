//! Counterfactual consumer controls for the actual terminal outbound sealer.
//! Root decisions and missing child evidence are explicitly constructed inputs;
//! no test claims that the fixture model admitted these forms.

use std::collections::BTreeMap;

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, BridgeSitePlan,
        RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
    },
    decision::{
        Arm, Decision, Degradation, DegradeReason, RequiredArmSet,
        raw_boundary::{BridgeTemplate, RawMutability, RawTargetType, ReturnedChildSiteEvidence},
        seam::{Form, GlueSpec, RawOutboundEndpoint, SeamEdit, SeamFamily, SeamInputRendering},
    },
    plan::{ClassInput, ClassSite, Edit, Justification, Plan},
};

const SOURCE: &str = "#![allow(dead_code, unused_mut)]\nextern \"C\" { fn strchr(p: *const i8, c: i32) -> *mut i8; }\nunsafe fn caller(mut p: *mut i8) { let _ = strchr(&mut *p, 0); }";

#[derive(Clone, Copy, Debug)]
enum RootForm {
    Ref,
    Slice,
    Option,
    Reverted,
}

fn check(form: RootForm, shared_address: bool) {
    let (ready, reasons, replacement, declaration, expected_operand, binding_requirement, found, receipt_found, terminal_found) = ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
        let (mut table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("fixture compiler IDs and input forms");
        let solve = super::model_cache::solve_receipt();
        println!("RETURNED-CHILD-TERMINAL-VIEW {form:?} shared={shared_address} solve={solve:#?}");
        assert!(solve.is_some(), "tiny fixture solve receipt required");
        let index = table.entries.iter().position(|(subject, _)| subject.label == "caller::p").expect("real caller parameter");
        let subject = table.entries[index].0.clone();
        let node = (subject.fn_did, subject.hir_id);
        let owner = SignatureClassId::of(subject.fn_did);
        assert_eq!(table.input_interfaces.subject_forms.get(&node), Some(&Form::Raw));
        assert!(subject.mut_binding, "input already declares the binding mutable");
        let (decision, declaration, operand) = match form {
            RootForm::Ref => (Decision::Ref { mutable: true }, "mut p: &mut i8", "&mut *p"),
            RootForm::Slice if shared_address => (Decision::Slice { mutable: true, uses: Vec::new() }, "mut p: &mut [i8]", "&p[0]"),
            RootForm::Slice => (Decision::Slice { mutable: true, uses: Vec::new() }, "mut p: &mut [i8]", "&mut p[0]"),
            RootForm::Option => (Decision::Opt { mutable: true, slice: false, uses: Vec::new() }, "mut p: Option<&mut i8>", "&mut **p.as_mut().unwrap()"),
            RootForm::Reverted => (Decision::Degraded(Degradation { subject: subject.label.clone(), site: "constructed-terminal-source-reversion".into(), reason: DegradeReason::RevertedAfterVerifyFailure }), "mut p: *mut i8", "&mut *p"),
        };
        // The explicit decision below is a consumer input. The model and
        // analysis facts remain exactly those produced for SOURCE.
        table.entries[index].1 = decision;
        table.option_mut_bindings.remove(&node);
        let sites = ctx.raw_boundary.inventoried_sites().filter(|(key, _, site)| {
            key.callee.symbol == "strchr" && key.argument_index == 0 && site.node == Some(node)
        }).collect::<Vec<_>>();
        let [(site_key, _, site)] = sites.as_slice() else { panic!("one actual foreign argument span required") };
        let target = RawTargetType { rendered: "*const i8".into(), pointee: "i8".into(), mutability: RawMutability::Const, depth2: None };
        let argument_shape = if shared_address { "addr-of" } else { "addr-of-mut" };
        let template = BridgeTemplate::RefMutToWritableRawConst;
        let spec = GlueSpec::raw_boundary_target(template, &target, false, false);
        let operand = format!("({operand})");
        let replacement = spec.render_in_context(&operand, true).expect("initial explicit scalar-address adapter");
        let original = tcx.sess.source_map().span_to_snippet(site.span).unwrap();
        assert_eq!(original, "&mut *p");
        let bridge = BridgeSitePlan {
            caller: subject.fn_did, callee: BridgeCalleeId::Foreign(site_key.callee.path.clone()),
            arm: "c".into(), position: "arg0".into(), bridge_kind: template.key().into(),
            expected_form: "raw".into(), found_form: "ref-mut".into(), argument_kind: argument_shape.into(),
            extent: BridgeExtentKind::None, retention: BridgeRetentionTier::T2,
            waiver_id: Some(RAW_BOUNDARY_T2_WAIVER_ID.into()), unsafe_context: None,
        };
        let seam = SeamEdit {
            raw_outbound: Some(RawOutboundEndpoint {
                returned_child: Some(ReturnedChildSiteEvidence { child: Err("constructed-unknown-child-access"), raw_field_parent: false }),
                mutable_binding_required: false, target: target.clone(), original_expression: original.clone(), operand_expression: operand.clone(),
                ownership: None, negative_write: true, box_slice: false, enclosing_unsafe_fn: true,
                callee_may_yield_pointer: true,
                child_access: None,
            }),
            zero_syntax: false, span: site.span, call_span: site.call_span, replacement: replacement.clone(),
            owner_class: owner, bridge: bridge.clone(), owner_fn: subject.label.clone(), lifetime_plan_digest: None,
            caller_fn: site_key.caller.clone(), param_index: 0, source_shape: argument_shape, family: SeamFamily::Safe, len_arm: None,
            spec, arg_span: site.span, expected: Form::Raw, found: Form::Ref { mutable: true }, source_node: Some(node),
            input_rendering: Some(SeamInputRendering::ZeroSyntax { found: Form::Raw }), root_identity: subject.label.clone(), blind: false,
            overlap: None, atom_ids: Vec::new(),
        };
        let source_file = tcx.sess.source_map().lookup_source_file(site.span.lo());
        let file = super::file_key(&source_file.name).unwrap();
        let file_label = super::bridge_custody_export::file_label(&file);
        let lo = (site.span.lo().0 - source_file.start_pos.0) as usize;
        let hi = (site.span.hi().0 - source_file.start_pos.0) as usize;
        let mut class_site = ClassSite::edit(owner, owner, Arm::C, &file_label, lo as u32, hi as u32, template.key());
        class_site.key = bridge.materialize(owner, file_label, lo as u32, hi as u32);
        class_site.expected_form = bridge.expected_form.clone();
        class_site.found_form = bridge.found_form.clone();
        class_site.argument_kind = bridge.argument_kind.clone();
        class_site.extent = bridge.extent.clone();
        class_site.retention = bridge.retention;
        class_site.waiver_id = bridge.waiver_id.clone();
        let mut input = ClassInput::new(owner, RequiredArmSet::default());
        input.sites.push(class_site);
        let edit = Edit { lo, hi, replacement, justification: Justification::SeamAdapter { family: "safe", fabricated: false },
            owner_class: Some(owner), owner_path: subject.label.clone(), bridge: Some(bridge), atom_ids: Vec::new(),
            subject_id: subject.label.clone(), required_arms: "c".into(), edit_kind: "seam-adapter" };
        let mut plan = Plan { by_file: BTreeMap::from([(file, vec![edit])]),
            class_finalization: super::plan::finalize_class_inputs(vec![input]), ..Default::default() };
        plan.terminal_call_plans.seam_edits.push(seam);
        assert!(plan.class_finalization.classes[&owner].is_ready(), "constructed plan starts ready");
        super::seal_terminal_outbound_calls(tcx, &table, &mut plan).expect("actual terminal sealer");
        let class = &plan.class_finalization.classes[&owner];
        let sealed = &plan.terminal_call_plans.seam_edits[0];
        let terminal_found = plan.bridge_events(&plan.held_classes()).into_iter().find(|event| {
            event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
                && event.site.owner_class == owner && event.site.lo == lo as u32 && event.site.hi == hi as u32
        }).expect("exact final class receipt").found_form;
        (class.is_ready(), class.hold_reasons().to_vec(), sealed.replacement.clone(), declaration.to_owned(),
            if matches!(form, RootForm::Reverted) { original } else { operand }, sealed.raw_outbound.as_ref().unwrap().mutable_binding_required,
            sealed.found, sealed.bridge.found_form.clone(), terminal_found)
    }).expect("original raw fixture compiles");
    if shared_address {
        assert!(
            !ready,
            "shared scalar address with unknown child access must be held"
        );
        assert!(
            reasons
                .iter()
                .any(|reason| reason.contains("returned-child-permission")),
            "{reasons:?}"
        );
        assert!(
            super::verify::type_checks_str(SOURCE),
            "held control preserves its original source"
        );
        return;
    }
    assert!(
        ready,
        "effective mutable scalar address must keep its class ready: {form:?}, {reasons:?}"
    );
    let expected_form = if matches!(form, RootForm::Reverted) {
        Form::Raw
    } else {
        Form::Ref { mutable: true }
    };
    assert_eq!(
        found, expected_form,
        "found form describes the effective address, not its Slice/Option root"
    );
    assert_eq!(
        receipt_found,
        expected_form.key(),
        "receipt uses the same effective form"
    );
    assert_eq!(
        terminal_found,
        expected_form.key(),
        "materialized terminal event uses the effective form"
    );
    assert!(
        !binding_requirement,
        "scalar-address adapter must not invent an Option binding obligation"
    );
    let emitted = format!(
        "#![allow(dead_code, unused_mut)]\nextern \"C\" {{ fn strchr(p: *const i8, c: i32) -> *mut i8; }}\nunsafe fn caller({declaration}) {{ let _ = strchr({replacement}, 0); }}"
    );
    assert!(
        super::verify::type_checks_str(&emitted),
        "terminal adapter must operate on the scalar address: {form:?}\n{emitted}"
    );
    if matches!(form, RootForm::Reverted) {
        assert_eq!(
            replacement, expected_operand,
            "source reversion selects exact original expression"
        );
    } else {
        assert!(
            replacement.contains("core::ptr::from_mut") && replacement.contains("cast_const"),
            "{replacement}"
        );
        assert!(
            replacement.contains(&expected_operand),
            "the exact scalar operand remains the adapter input: {replacement}"
        );
    }
}

#[test]
fn returned_child_terminal_view_ref_address_control() {
    check(RootForm::Ref, false);
}

#[test]
fn returned_child_terminal_view_slice_root_uses_scalar_address() {
    check(RootForm::Slice, false);
}

#[test]
fn returned_child_terminal_view_option_root_needs_no_outer_option_adapter() {
    check(RootForm::Option, false);
}

#[test]
fn returned_child_terminal_view_shared_address_remains_held() {
    check(RootForm::Slice, true);
}

#[test]
fn returned_child_terminal_view_reverted_source_uses_original_expression() {
    check(RootForm::Reverted, false);
}
