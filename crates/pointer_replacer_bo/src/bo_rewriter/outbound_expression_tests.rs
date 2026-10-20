//! J20 expression-level outbound calls with a native borrowed return source.
//! The valid-stack memory-safety pattern fixture is compiled, never executed.

use std::collections::BTreeSet;

use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::Res,
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::{
    mir::{RETURN_PLACE, TerminatorKind},
    ty::TyKind,
};
use rustc_span::Span;

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
        RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
    },
    decision::{
        Decision, emitability::ArgShape, lifetime::FnSignatureSlot, raw_boundary::RetentionVerdict,
        seam::Form,
    },
};

const INPUT: &str = r#"
    #![allow(dead_code, unused_unsafe)]
    unsafe fn raw_read(q: *const i32) -> i32 { q.read() }
    unsafe fn target(p: *mut i32) -> *mut i32 {
        *p.offset(1) += 1;
        p
    }
    pub unsafe fn entry() -> i32 {
        let mut values = [3, 5, 7];
        raw_read(target(values.as_mut_ptr()))
    }
"#;

struct ExactArgument {
    span: Span,
    expressions: Vec<HirId>,
}

struct ExpressionAudit {
    rows: Vec<super::sibling_audit::Row>,
    capture: super::bridge_custody_export::SiblingAuditCapture,
    expected_id: String,
    expected_receipt: super::bridge_receipt::BridgeSiteKey,
    expected_hir: (u32, u32),
    declaration_identities: BTreeSet<String>,
    pending_count: usize,
    export: super::bridge_custody_export::Export,
    events: Vec<super::bridge_receipt::BridgeReceiptEvent>,
    sources: std::collections::BTreeMap<String, String>,
}

impl<'tcx> Visitor<'tcx> for ExactArgument {
    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        if expression.span == self.span {
            self.expressions.push(expression.hir_id);
        }
        walk_expr(self, expression);
    }
}

#[test]
fn outbound_expression_native_slice_return_to_raw_argument_has_one_owned_view() {
    assert!(
        super::verify::type_checks_str(INPUT),
        "unchanged valid-stack input type/borrow-checks"
    );
    let (emitted, caller_retired, source_retired, expression_audit) = ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original outbound-expression AST capture");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one ordinary tiny-fixture decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("OUTBOUND-EXPRESSION solve={solve:#?}\nINPUT:\n{INPUT}");
        assert!(solve.is_some(), "actual fixture solve receipt is mandatory");
        let (p, p_decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual target parameter p");
        let (q, q_decision) = table.entries.iter().find(|(subject, _)| subject.label == "raw_read::q")
            .expect("actual raw-read parameter q");
        let permit = ctx.lifetime_eligibility.return_permit((p.fn_did, p.hir_id));
        let retention = ctx.retention.get(q.fn_did, 0).expect("actual raw callee retention summary");
        println!("OUTBOUND-EXPRESSION p={p_decision:#?}; q={q_decision:#?}; permit={permit:#?}; retention={retention:#?}; potential interface={:#?}; final interface={:#?}; additive={:#?}",
            ctx.hypothetical.return_interfaces.functions.get(&p.fn_did),
            table.return_interfaces.functions.get(&p.fn_did),
            ctx.raw_boundary_artifacts.additive_family_receipts);

        // Original HIR and MIR independently identify the nested expression;
        // no named receiver or ledger subject is introduced for its result.
        let calls = ctx.facts.call_args.get(&q.fn_did).expect("raw-read HIR call inventory");
        let [call] = calls.as_slice() else { panic!("one actual raw-read call: {calls:#?}") };
        let [argument] = call.args.as_slice() else { panic!("one raw-read argument") };
        assert_eq!(argument.index, 0);
        assert!(matches!(argument.shape, ArgShape::RawExpr { root: None }),
            "authoring premise: nested call result has no local source root: {argument:#?}");
        assert_eq!(tcx.sess.source_map().span_to_snippet(argument.span).unwrap(), "target(values.as_mut_ptr())");
        let mut visitor = ExactArgument { span: argument.span, expressions: Vec::new() };
        visitor.visit_expr(tcx.hir_body_owned_by(call.caller).value);
        let [argument_hir] = visitor.expressions.as_slice() else {
            panic!("one independently visited original argument HIR: {:?}", visitor.expressions)
        };
        let expression = tcx.hir_node(*argument_hir).expect_expr();
        let ExprKind::Call(callee, _) = expression.kind else { panic!("nested argument is a direct call") };
        assert!(matches!(callee.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Def(_, did) if did == p.fn_did.to_def_id())));
        assert!(!table.entries.iter().any(|(subject, _)| subject.hir_id == *argument_hir),
            "argument expression itself is not a declaration subject");
        let body = tcx.mir_drops_elaborated_and_const_checked(call.caller).borrow();
        let mir_sites = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
            let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else { return None };
            let constant = func.constant()?;
            let TyKind::FnDef(callee, _) = *constant.ty().kind() else { return None };
            (callee == q.fn_did.to_def_id()).then_some((block.as_u32(), data.statements.len() as u32,
                data.terminator().source_info.span.source_callsite(), args.len()))
        }).collect::<Vec<_>>();
        let [(block, statement_index, mir_span, count)] = mir_sites.as_slice() else {
            panic!("one independently visited raw-read MIR call: {mir_sites:?}")
        };
        assert_eq!(*count, 1);
        assert!(mir_span.contains(argument.span.source_callsite()));
        let sites = ctx.raw_boundary_sites.sites.iter().filter(|site|
            site.callee_local == Some(q.fn_did) && site.key.argument_index == 0
                && site.source_span == argument.span && site.call_span == call.span)
            .collect::<Vec<_>>();
        let [site] = sites.as_slice() else { panic!("one exact expression-level raw-boundary fact: {sites:#?}") };
        assert_eq!(site.key.block, *block);
        assert_eq!(site.key.statement_index, *statement_index);
        assert!(site.node.is_none());
        assert_eq!(site.key.subject, "<unrooted>");
        assert_eq!(site.source_shape, "raw-expr");
        println!("OUTBOUND-EXPRESSION HIR={argument_hir:?}; MIR={mir_sites:?}; site={site:#?}; disposition={:#?}",
            ctx.raw_boundary.disposition(&site.key));

        // Frozen-model, origin, lifetime and raw-destination premises precede
        // the new outgoing carrier requirement. No kind or tier is injected.
        for local in [p.local, RETURN_PLACE] {
            let kind = ctx.slots.fn_local_slots.get(&p.fn_did)
                .and_then(|slots| slots.slot_for_local_depth(local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(p.fn_did, slot)));
            assert_eq!(kind, Some(&super::SlotKind::Ref), "actual source/return model premise: {local:?}");
        }
        let origins = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&p.fn_did)).expect("native target origin export");
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        assert!(origins.body.depth0_value_flows().contains(&(
            SlotOwner::Local(p.local), SlotOwner::Local(RETURN_PLACE))));
        assert!(permit.is_some(), "actual parameter-tied native return permit");
        assert!(matches!(p_decision, Decision::Slice { mutable: true, .. }),
            "actual returning source remains a mutable slice: {p_decision:#?}");
        assert!(matches!(q_decision, Decision::Degraded(_)),
            "raw-read's banked method-call surface must remain raw: {q_decision:#?}");
        let function = table.lifetime_plan.function(p.fn_did).expect("actual native target lifetime plan");
        let lifetime = function.lifetime_for(FnSignatureSlot::arg(1, 0, 0)).expect("native parameter lifetime");
        assert_eq!(function.lifetime_for(FnSignatureSlot::RETURN), Some(lifetime));
        let interface = table.return_interfaces.functions.get(&p.fn_did).expect("actual native target return interface");
        assert_eq!(interface.form, Form::Slice { mutable: true });
        assert_eq!(interface.lifetime, lifetime);
        assert_eq!(interface.lifetime_plan_digest, function.digest());
        let expected_tier = match retention {
            RetentionVerdict::NoRetain { certificate } => {
                ctx.retention.verify_certificate(q.fn_did, 0, certificate).expect("native no-retention certificate replays");
                BridgeRetentionTier::T1
            }
            RetentionVerdict::Unknown { .. } => BridgeRetentionTier::T2,
            RetentionVerdict::Retains { .. } => panic!("authoring premise: retaining callee cannot witness an admitted view"),
        };
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual outbound-expression emission plan");
        assert_eq!(super::terminal_parameter_form(&table, &emission.plan.class_finalization, q.fn_did, 0), Form::Raw);
        let target_owner = SignatureClassId::of(p.fn_did);
        let held = emission.plan.held_classes();
        println!("OUTBOUND-EXPRESSION target hold={:?}; outgoing seams={:#?}",
            emission.plan.class_hold_reason(target_owner),
            emission.plan.terminal_call_plans.seam_edits.iter().filter(|edit|
                edit.bridge.caller == call.caller && edit.bridge.callee == BridgeCalleeId::Local(q.fn_did))
                .collect::<Vec<_>>());

        // Production RED: the kept native result needs an owned raw view at
        // this non-subject argument, not a retirement of the return producer.
        assert!(emission.plan.class_finalization.classes.get(&target_owner)
            .is_some_and(super::plan::SignatureClassPlan::is_ready),
            "an adaptable non-subject raw argument must keep its native return class Ready");
        assert!(!held.contains(&target_owner));
        let original_file = tcx.sess.source_map().lookup_source_file(argument.span.lo());
        let file = super::bridge_custody_export::file_label(&super::file_key(&original_file.name).unwrap());
        let lo = argument.span.lo().0 - original_file.start_pos.0;
        let hi = argument.span.hi().0 - original_file.start_pos.0;
        let events = emission.plan.bridge_events(&held);
        let exact = events.iter().filter(|event| event.site.caller == call.caller
            && event.site.callee == BridgeCalleeId::Local(q.fn_did) && event.site.position == "arg0"
            && event.site.file == file && event.site.lo == lo && event.site.hi == hi
            && event.found_form == interface.form.key() && event.expected_form == Form::Raw.key())
            .collect::<Vec<_>>();
        assert_eq!(exact.iter().filter(|event| event.stage == BridgeReceiptStage::Plan).count(), 1,
            "one exact non-subject outbound plan: {events:#?}");
        let terminal = exact.iter().filter(|event| event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
        let [terminal] = terminal.as_slice() else { panic!("one exact terminal outgoing view: {events:#?}") };
        assert_eq!(terminal.state, BridgeReceiptState::Applied);
        assert_eq!(terminal.retention, expected_tier);
        assert_eq!(terminal.waiver_id.as_deref(),
            (expected_tier == BridgeRetentionTier::T2).then_some(RAW_BOUNDARY_T2_WAIVER_ID));
        assert_eq!(terminal.argument_kind, "raw-expr");
        super::bridge_receipt::reconcile_bridge_events(&events).expect("exact common outgoing receipts reconcile");
        let mut artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(&mut artifacts, &emission.plan, &held, &BTreeSet::new());
        assert!(artifacts.outbound_return_error.is_none(), "{:?}", artifacts.outbound_return_error);
        let required = artifacts.outbound_return_required.iter().filter(|required|
            required.associated_bridge == terminal.site).collect::<Vec<_>>();
        let [required] = required.as_slice() else { panic!("one independent exact expression requirement") };
        use super::mechanical_receipt::{CanonicalCallee, CanonicalLocation, MechanicalFamily, MechanicalSubjectKey};
        assert_eq!(required.key.family, MechanicalFamily::FlowsIntoRawParam);
        assert_eq!(required.key.owner_class, target_owner);
        assert_eq!(required.key.subject, MechanicalSubjectKey::Generated {
            owner: call.caller, key: format!("outbound-expression:{}", argument_hir.local_id.as_u32()), slot_depth: 0,
        });
        assert_eq!(required.key.site.location, CanonicalLocation::Hir {
            owner: call.caller, item_local_id: argument_hir.local_id.as_u32(),
        });
        assert_eq!(required.key.site.argument_index, Some(0));
        assert_eq!(required.key.site.callee, Some(CanonicalCallee::Local(q.fn_did.to_def_id())));
        let native = required.native_lifetime.as_ref().expect("actual source native proof is distinct from sink retention");
        assert_eq!(native.owner, p.fn_did.local_def_index.as_u32());
        assert_eq!(native.lifetime, interface.lifetime);
        assert_eq!(native.plan_digest, interface.lifetime_plan_digest);
        assert_eq!(required.retention_evidence.as_ref(), Some(retention));
        assert_eq!(required.lifetime_origin, vec![MechanicalSubjectKey::Local {
            owner: p.fn_did, mir_local: p.local.as_u32(), slot_depth: 0,
        }]);
        let packet = super::outbound_return_transport::capture(&artifacts);
        let bytes = serde_json::to_vec(&packet).unwrap();
        let retained = serde_json::from_slice(&bytes).unwrap();
        super::outbound_return_transport::validate(&retained).expect("native source and sink evidence survive JSON replay");
        let mut missing = artifacts.clone();
        missing.outbound_return_required.retain(|row| row.key != required.key);
        missing.outbound_return_rows.retain(|row| row.terminal.obligation_key != required.key);
        missing.mechanical_events.retain(|row| row.key != required.key);
        assert!(super::mechanical_receipt::reconcile_outbound_return_rows(
            &missing.outbound_return_required, &missing.outbound_return_rows,
            &missing.mechanical_events, &missing.bridge_events).is_err(),
            "deliberate-fault: erasing every expression output leaves the independent Applied bridge and is caught");

        let (files, rollbacks, _, _, _) = super::round_files(tcx, &capture, &emission.plan,
            &emission.texts, &held, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table)
            .expect("actual outbound-expression rendering");
        assert!(rollbacks.is_empty(), "new outgoing site cannot retire its native producer");
        assert_eq!(files.len(), 1);
        let sources = files.iter().map(|(file, source)|
            (super::bridge_custody_export::file_label(file), source.clone()))
            .collect::<std::collections::BTreeMap<_, _>>();
        let emitted = files.into_values().next().unwrap();
        let render_reverted = |classes: &BTreeSet<SignatureClassId>| {
            let (files, rollbacks, _, _, _) = super::round_files(tcx, &capture, &emission.plan,
                &emission.texts, classes, &BTreeSet::new(), emission.plan.root_file.as_ref(), &table).unwrap();
            assert!(rollbacks.is_empty());
            assert_eq!(files.len(), 1);
            files.into_values().next().unwrap()
        };
        let mut caller_classes = held.clone();
        caller_classes.insert(SignatureClassId::of(call.caller));
        let effective = emission.plan.effective_reverted_classes(&caller_classes, &BTreeSet::new());
        assert!(!effective.contains(&target_owner), "caller retirement must keep the independent native return producer");
        let caller_retired = render_reverted(&caller_classes);
        let mut caller_artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(&mut caller_artifacts, &emission.plan, &caller_classes, &BTreeSet::new());
        assert!(caller_artifacts.outbound_return_error.is_none());
        assert!(caller_artifacts.bridge_events.iter().any(|event| event.site == terminal.site
            && event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Applied));
        assert!(caller_artifacts.outbound_return_required.iter().any(|row| row == *required));

        let mut source_classes = held.clone();
        source_classes.insert(target_owner);
        let source_retired = render_reverted(&source_classes);
        let mut source_artifacts = super::RawBoundaryArtifacts::default();
        super::refresh_raw_boundary_receipt_events(&mut source_artifacts, &emission.plan, &source_classes, &BTreeSet::new());
        assert!(source_artifacts.outbound_return_error.is_none());
        assert!(source_artifacts.outbound_return_required.is_empty());
        assert!(source_artifacts.outbound_return_rows.is_empty());
        assert!(source_artifacts.bridge_events.iter().any(|event| event.site == terminal.site
            && event.stage == BridgeReceiptStage::Terminal && event.state == BridgeReceiptState::Dropped));
        println!("OUTBOUND-EXPRESSION terminal={terminal:#?}\nEMITTED:\n{emitted}\nCALLER RETIRED:\n{caller_retired}\nSOURCE RETIRED:\n{source_retired}");
        let original_files = tcx.sess.source_map().files().iter().filter_map(|file| {
            Some((super::file_key(&file.name)?, file.src.as_ref()?.to_string()))
        }).collect::<std::collections::BTreeMap<_, _>>();
        let export = super::bridge_custody_export::capture(tcx, &capture, &table, &emission.plan, &original_files);
        let mut expected_receipt = terminal.site.clone();
        assert_eq!(expected_receipt.owner_class, target_owner, "existing outgoing bridge belongs to its actual native producer");
        expected_receipt.arm = "sibling-overlap".into();
        expected_receipt.bridge_kind = super::decision::sibling_overlap::PENDING_REASON.into();
        let expression_audit = ExpressionAudit {
            rows: artifacts.sibling_audit_rows.clone(),
            capture: export.sibling_audit.as_ref().expect("the all-site audit capture is present").clone(),
            // This expectation comes directly from the original MIR/HIR fact
            // already proved above, not from audit rows or pending receipts.
            expected_id: super::decision::raw_boundary::site_atom_id(&site.key),
            expected_receipt,
            expected_hir: (call.caller.local_def_index.as_u32(), argument_hir.local_id.as_u32()),
            declaration_identities: table.entries.iter().map(|(subject, _)| {
                subject.identity_key(&tcx.def_path_str(subject.fn_did.to_def_id()))
            }).collect(),
            pending_count: artifacts.pending_sibling_receipts.iter()
                .filter(|pending| pending.receipt.potential.site == site.key).count(),
            export,
            events: events.clone(),
            sources,
        };
        (emitted, caller_retired, source_retired, expression_audit)
    }).expect("original memory-safety pattern fixture compiles");
    assert!(
        super::verify::type_checks_str(&emitted),
        "actual outgoing view type/borrow-checks:\n{emitted}"
    );
    for (label, text) in [("caller", &caller_retired), ("source", &source_retired)] {
        assert!(
            super::verify::type_checks_str(text),
            "{label} retirement type/borrow-checks:\n{text}"
        );
    }
    assert!(
        caller_retired.contains("__crat_outbound_return_"),
        "caller retirement keeps the source-owned view"
    );
    assert!(
        !source_retired.contains("__crat_outbound_return_"),
        "source retirement drops its raw-result view"
    );
    assert!(
        source_retired.contains("fn target(p: *mut i32) -> *mut i32"),
        "source retirement restores its original signature:\n{source_retired}"
    );
    let syntax = super::bridge_custody_syntax::inventory_source("outbound-expression.rs", &emitted)
        .expect("pinned parser sees emitted call structure");
    for callee in ["target", "raw_read"] {
        assert_eq!(
            syntax
                .calls
                .iter()
                .filter(|call| call.owner == "entry" && call.callee_path.as_deref() == Some(callee))
                .count(),
            1,
            "outgoing adapter evaluates each original call exactly once: {callee}\n{emitted}"
        );
    }
    assert_eq!(
        emitted.matches(".as_ptr()").count() + emitted.matches(".as_mut_ptr()").count(),
        2,
        "one original array data-pointer call plus one borrowed-result raw view:\n{emitted}"
    );

    // R236 instrument RED follows all banked model/native-lifetime, bridge,
    // reversion, output type-check and pinned-parser premises above. A source
    // expression with no pointer sibling still requires an explicit audit row.
    let audit = expression_audit;
    let rows = audit
        .rows
        .iter()
        .filter(|row| row.coverage_id == audit.expected_id)
        .collect::<Vec<_>>();
    assert_eq!(
        rows.len(),
        1,
        "one exact generated-expression sibling coverage row is required even without pointer siblings: expected={}; rows={:#?}",
        audit.expected_id,
        audit.rows
    );
    let row = rows[0];
    assert_eq!(row.outcome, super::sibling_audit::Outcome::NoRiskySibling);
    assert!(row.siblings.is_empty());
    assert!(
        row.data && row.issues.is_empty(),
        "complete no-sibling predicate inputs: {row:#?}"
    );
    assert_eq!(
        audit.pending_count, 0,
        "no sibling means no pending-overlap stamp"
    );
    assert_eq!(
        row.receipt_key.as_deref(),
        Some(audit.expected_receipt.receipt_key().as_str()),
        "audit custody must keep the actual native producer owner and actual raw sink endpoint"
    );
    assert_eq!(
        (row.source.hir_owner, row.source.hir_local),
        audit.expected_hir
    );
    assert!(
        !audit.declaration_identities.contains(&row.source.identity),
        "the generated argument expression must not borrow a declaration identity"
    );
    assert_eq!(row.source.argument_shape, "raw-expr");
    assert_eq!(row.terminal.source_form, "slice-mut");
    assert_eq!(row.terminal.target_form, "raw");
    assert!(row.terminal.source_delivered);
    assert!(
        audit
            .capture
            .expected_coverage_ids
            .contains(&audit.expected_id),
        "the independent exported universe must retain the original expression identity"
    );
    let retained = audit
        .capture
        .rows
        .iter()
        .filter(|captured| captured.coverage_id == audit.expected_id)
        .collect::<Vec<_>>();
    assert_eq!(
        retained,
        vec![row],
        "the exact owned expression row survives the custody capture"
    );

    // Deliberate-fault RED: a successful source descriptor must still agree
    // with the independently retained J27 source producer and actual events.
    let baseline = super::bridge_custody_export::compare_capture(
        &audit.export,
        &audit.events,
        Some(&audit.sources),
        super::CensusOutcomeKind::Emitted,
    );
    assert!(
        baseline.data,
        "actual complete expression capture validates before the fault: {baseline:#?}"
    );
    let bytes = serde_json::to_vec(&audit.export).unwrap();
    let mut changed: super::bridge_custody_export::Export = serde_json::from_slice(&bytes).unwrap();
    let changed_audit = changed.sibling_audit.as_mut().unwrap();
    assert_eq!(
        changed_audit.expected_coverage_ids,
        audit.capture.expected_coverage_ids
    );
    let changed_row = changed_audit
        .rows
        .iter_mut()
        .find(|candidate| candidate.coverage_id == audit.expected_id)
        .unwrap();
    assert!(changed_row.data && changed_row.issues.is_empty());
    let native = changed_row
        .source
        .native_return
        .as_mut()
        .expect("actual native expression source descriptor");
    assert_eq!(
        native.source_owner,
        audit.expected_receipt.owner_class.order_key(),
        "the baseline descriptor names the actual outgoing source producer"
    );
    native.source_owner = native.source_owner.checked_add(1).unwrap();
    assert!(
        changed_row.data && changed_row.issues.is_empty(),
        "saved success flags are deliberately preserved"
    );
    assert_eq!(
        changed.outbound_return, audit.export.outbound_return,
        "independent J27 evidence stays unchanged"
    );
    assert_eq!(
        changed.outbound_return_bridge_keys, audit.export.outbound_return_bridge_keys,
        "independent outgoing bridge inventory stays unchanged"
    );
    let caught = super::bridge_custody_export::compare_capture(
        &changed,
        &audit.events,
        Some(&audit.sources),
        super::CensusOutcomeKind::Emitted,
    );
    assert!(
        !caught.data,
        "wrong native source owner must be caught against independent J27 evidence after JSON replay: {caught:#?}"
    );
}
