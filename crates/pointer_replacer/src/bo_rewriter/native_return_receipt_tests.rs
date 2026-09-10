//! J27 exact ordinary return sites, independent of receiver adaptation.
//! The valid-stack memory-safety pattern fixture is compiled, never executed.

use std::collections::BTreeSet;

use rustc_hir::{
    Expr, HirId,
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::mir::RETURN_PLACE;
use rustc_span::Span;

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
        SignatureClassId,
    },
    decision::{
        SubjectKind, lifetime::FnSignatureSlot, raw_boundary::RetentionVerdict, seam::Form,
    },
    mechanical_receipt::{
        CanonicalCallee, CanonicalLocation, MechanicalFamily, MechanicalRetention, MechanicalStage,
        MechanicalState, MechanicalSubjectKey,
    },
};

const INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn target(absent: bool, p: *mut i32) -> *mut i32 {
        *p += 1;
        if absent { return core::ptr::null_mut(); }
        p
    }
    pub unsafe fn entry() -> i32 {
        let mut value = 3;
        let _ = target(true, &mut value);
        let _ = target(false, &mut value);
        value
    }
"#;

struct ExactExpressions {
    spans: Vec<Span>,
    expressions: Vec<(Span, HirId)>,
}

impl<'tcx> Visitor<'tcx> for ExactExpressions {
    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        if self.spans.contains(&expression.span) {
            self.expressions.push((expression.span, expression.hir_id));
        }
        walk_expr(self, expression);
    }
}

#[test]
fn native_return_receipts_inventory_both_null_and_parameter_branches() {
    assert!(
        super::verify::type_checks_str(INPUT),
        "unchanged valid-stack input type/borrow-checks"
    );
    let (emitted, artifacts, expected, reverse_inventory_result, omitted_producer_error) =
        ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original native-return capture");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one ordinary native-return fixture pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("NATIVE-RETURN-J27 solve={solve:#?}\nINPUT:\n{INPUT}");
        assert!(solve.is_some(), "actual fixture solve receipt is mandatory");
        let (p, _) = table.entries.iter().find(|(subject, _)| subject.label == "target::p").unwrap();
        let SubjectKind::Param { hir_index } = p.kind else { panic!("p is an actual parameter") };
        assert_eq!(hir_index, 1);
        for local in [p.local, RETURN_PLACE] {
            let kind = ctx.slots.fn_local_slots.get(&p.fn_did)
                .and_then(|slots| slots.slot_for_local_depth(local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(p.fn_did, slot)));
            println!("NATIVE-RETURN-J27 model {local:?}={kind:?}");
            assert_eq!(kind, Some(&super::SlotKind::Ref), "actual parameter/return model premise");
        }
        let origins = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&p.fn_did)).unwrap();
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        assert!(origins.body.depth0_value_flows().contains(&(
            SlotOwner::Local(p.local), SlotOwner::Local(RETURN_PLACE))));
        let permit = ctx.lifetime_eligibility.return_permit((p.fn_did, p.hir_id));
        assert!(permit.is_some());
        let lifetime = table.lifetime_plan.function(p.fn_did).unwrap();
        let region = lifetime.lifetime_for(FnSignatureSlot::arg(hir_index + 1, 0, 0)).unwrap();
        assert_eq!(lifetime.lifetime_for(FnSignatureSlot::RETURN), Some(region));
        let interface = table.return_interfaces.functions.get(&p.fn_did).unwrap();
        assert_eq!(interface.form, Form::Opt { mutable: true, slice: false });
        assert_eq!(interface.lifetime, region);
        assert_eq!(interface.lifetime_plan_digest, lifetime.digest());
        let retention = ctx.retention.get(p.fn_did, hir_index);
        println!("NATIVE-RETURN-J27 native origin permit={permit:?}; lifetime={lifetime:#?}; parameter retention={retention:#?}");
        assert!(matches!(retention, Some(RetentionVerdict::Retains { .. })),
            "a native parameter-tied return must not invent a NoRetain certificate");
        let sites = ctx.facts.return_sites.iter().filter(|site| site.owner == p.fn_did).collect::<Vec<_>>();
        assert_eq!(sites.len(), 2, "exact null and parameter return-site inventory");
        let mut hir = ExactExpressions { spans: sites.iter().map(|site| site.span).collect(), expressions: Vec::new() };
        hir.visit_expr(tcx.hir_body_owned_by(p.fn_did).value);
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual native-return emission plan");
        let owner = SignatureClassId::of(p.fn_did);
        assert!(emission.plan.class_finalization.classes[&owner].is_ready());
        let held = emission.plan.held_classes();
        assert!(!held.contains(&owner));
        let mut artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(&mut artifacts, &emission.plan, &held, &BTreeSet::new());
        let mut expected = Vec::new();
        for site in sites {
            let ids = hir.expressions.iter().filter(|(span, _)| *span == site.span).map(|(_, hir)| *hir).collect::<Vec<_>>();
            let [expression] = ids.as_slice() else { panic!("one actual HIR expression at each native return span: {ids:?}") };
            assert_eq!(expression.owner.def_id, p.fn_did);
            let file = tcx.sess.source_map().lookup_source_file(site.span.lo());
            let file_key = super::bridge_custody_export::file_label(&super::file_key(&file.name).unwrap());
            let lo = site.span.lo().0 - file.start_pos.0;
            let hi = site.span.hi().0 - file.start_pos.0;
            let (kind, tier, source_form, expected_origins) = match site.source_shape {
                "null-lit" => {
                    assert!(site.root.is_none());
                    ("return-null-to-option", BridgeRetentionTier::None, Form::Raw, Vec::new())
                }
                "bare-local" => {
                    assert_eq!(site.root, Some(p.hir_id));
                    ("return-raw-to-ref", BridgeRetentionTier::T1, Form::Ref { mutable: true },
                        vec![MechanicalSubjectKey::Local { owner: p.fn_did, mir_local: p.local.as_u32(), slot_depth: 0 }])
                }
                shape => panic!("unexpected banked native return shape {shape}"),
            };
            let common = artifacts.bridge_events.iter().filter(|event|
                event.site.owner_class == owner && event.site.caller == p.fn_did
                    && event.site.callee == BridgeCalleeId::Local(p.fn_did) && event.site.bridge_kind == kind
                    && event.site.file == file_key && event.site.lo == lo && event.site.hi == hi).collect::<Vec<_>>();
            assert_eq!(common.len(), 2, "one exact Plan and Terminal native bridge");
            let terminal = common.iter().filter(|event| event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
            let [terminal] = terminal.as_slice() else { panic!("one terminal native bridge") };
            assert_eq!(terminal.state, BridgeReceiptState::Applied);
            assert_eq!(terminal.retention, tier);
            assert!(terminal.waiver_id.is_none());
            assert_eq!(terminal.found_form, source_form.key());
            assert_eq!(terminal.expected_form, interface.form.key());
            assert!(terminal.site.position.contains(&interface.lifetime_plan_digest));
            println!("NATIVE-RETURN-J27 exact site={site:#?}; original_hir={expression:?}; common={common:#?}; origins={expected_origins:?}");
            expected.push((*expression, (***terminal).clone(), expected_origins));
        }
        let (files, rollbacks, _, _, _) = super::round_files(tcx, &capture, &emission.plan, &emission.texts,
            &held, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table).unwrap();
        assert!(rollbacks.is_empty());
        assert_eq!(files.len(), 1);

        // Corrupt only custody carriers after all original native premises and
        // the unchanged complete emission have been established above.
        let null_sites = emission.plan.terminal_call_plans.native_return_sites.iter()
            .filter(|site| site.owner == p.fn_did && site.source_shape == "null-lit")
            .collect::<Vec<_>>();
        let [null_site] = null_sites.as_slice() else { panic!("one real null return expression") };
        let null_site = (**null_site).clone();
        let null_seams = emission.plan.terminal_call_plans.seam_edits.iter()
            .filter(|seam| seam.owner_class == owner && seam.span == null_site.span
                && seam.bridge.bridge_kind == "return-null-to-option")
            .collect::<Vec<_>>();
        let [null_seam] = null_seams.as_slice() else { panic!("one real null return seam") };
        let null_seam = (**null_seam).clone();
        let parameter_site = emission.plan.terminal_call_plans.native_return_sites.iter()
            .find(|site| site.owner == p.fn_did && site.root == Some(p.hir_id)).unwrap();
        assert_ne!(null_site.hir_id, parameter_site.hir_id);
        assert_ne!(null_site.span, parameter_site.span);

        // Freeze a one-site J27 control, then restore the untouched second
        // native terminal input. Its original HIR/span and proof are retained;
        // no replacement span, model verdict or native lifetime is invented.
        let mut partial_table = table.clone();
        partial_table.seams.native_return_sites.retain(|site| site.hir_id != null_site.hir_id);
        let mut reverse_plan = emission.plan.clone();
        reverse_plan.native_return_plans = super::plan::native_return::capture(
            &partial_table,
            &|span| {
                let file = tcx.sess.source_map().lookup_source_file(span.lo());
                let key = super::file_key(&file.name).ok_or("test-original-file-unavailable")?;
                Ok((key, (span.lo().0 - file.start_pos.0) as usize,
                    (span.hi().0 - file.start_pos.0) as usize))
            },
            &|owner| Some(tcx.def_path_str(owner.to_def_id())),
        );
        reverse_plan.terminal_call_plans.native_return_sites.retain(|site| site.hir_id != null_site.hir_id);
        reverse_plan.terminal_call_plans.seam_edits.retain(|seam| seam != &null_seam);
        let (partial_required, _, _) = reverse_plan.outbound_return_receipts(&held, &BTreeSet::new())
            .expect("one-site native producer and terminal inventory agree before drift");
        assert_eq!(partial_required.iter().filter(|required| required.native_lifetime.is_some()).count(), 1);
        reverse_plan.terminal_call_plans.native_return_sites.push(null_site);
        reverse_plan.terminal_call_plans.seam_edits.push(null_seam);
        let reverse_inventory_result = reverse_plan.outbound_return_receipts(&held, &BTreeSet::new())
            .map(|(required, _, _)| required.len());

        let mut omitted = emission.plan.clone();
        omitted.native_return_plans = Default::default();
        let mut omitted_artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(&mut omitted_artifacts, &omitted, &held, &BTreeSet::new());
        let omitted_producer_error = omitted_artifacts.outbound_return_error;

        let mut retired = held.clone();
        retired.insert(owner);
        let mut retired_artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(&mut retired_artifacts, &emission.plan, &retired, &BTreeSet::new());
        assert!(retired_artifacts.outbound_return_error.is_none(), "retired owner has no live J27 obligation");
        assert!(retired_artifacts.outbound_return_required.is_empty());
        assert!(retired_artifacts.outbound_return_rows.is_empty());
        let retired_returns = retired_artifacts.bridge_events.iter().filter(|event|
            event.site.owner_class == owner && event.stage == BridgeReceiptStage::Terminal
                && matches!(event.site.bridge_kind.as_str(), "return-raw-to-ref" | "return-null-to-option"))
            .collect::<Vec<_>>();
        assert_eq!(retired_returns.len(), 2);
        assert!(retired_returns.iter().all(|event| event.state == BridgeReceiptState::Dropped));

        (files.into_values().next().unwrap(), artifacts, expected,
            reverse_inventory_result, omitted_producer_error)
    }).expect("original native-return fixture compiles");
    assert!(
        super::verify::type_checks_str(&emitted),
        "native mixed-return output type/borrow-checks:\n{emitted}"
    );

    // First J27 RED follows all actual native, common-bridge and emitted-tree premises.
    assert_eq!(expected.len(), 2);
    for (hir, bridge, origins) in expected {
        let required = artifacts
            .outbound_return_required
            .iter()
            .filter(|required| required.associated_bridge == bridge.site)
            .collect::<Vec<_>>();
        let [required] = required.as_slice() else {
            panic!("each native return needs its independent J27 requirement: {bridge:#?}")
        };
        assert_eq!(required.key.family, MechanicalFamily::ReturnNotAdapted);
        assert_eq!(required.key.owner_class, bridge.site.owner_class);
        assert_eq!(
            required.key.site.location,
            CanonicalLocation::Hir {
                owner: hir.owner.def_id,
                item_local_id: hir.local_id.as_u32()
            }
        );
        assert_eq!(
            required.key.site.callee,
            Some(CanonicalCallee::Local(hir.owner.def_id.to_def_id()))
        );
        assert_eq!(required.lifetime_origin, origins);
        let rows = artifacts
            .outbound_return_rows
            .iter()
            .filter(|row| row.associated_bridge == bridge.site)
            .collect::<Vec<_>>();
        assert_eq!(
            rows.len(),
            2,
            "one specialized Plan and Terminal per native return"
        );
        for row in rows {
            assert_eq!(row.terminal.obligation_key, required.key);
            assert_eq!(row.source_form, bridge.found_form);
            assert_eq!(row.target_form, bridge.expected_form);
            assert_eq!(row.position, bridge.site.position);
            assert_eq!(row.lifetime_origin, origins);
            assert_eq!(
                row.retention,
                if bridge.retention == BridgeRetentionTier::T1 {
                    MechanicalRetention::T1
                } else {
                    MechanicalRetention::None
                }
            );
            assert_eq!(
                row.terminal.state,
                match row.terminal.stage {
                    MechanicalStage::Plan => MechanicalState::Planned,
                    MechanicalStage::Terminal => MechanicalState::Applied,
                }
            );
            assert!(row.terminal.reason.is_none());
        }
    }
    assert!(
        omitted_producer_error.is_some(),
        "refresh must reject loss of the entire native J27 producer"
    );
    assert!(
        reverse_inventory_result.is_err(),
        "a restored real terminal native return absent from captured J27 inventory must fail reverse custody: {reverse_inventory_result:?}"
    );
}
