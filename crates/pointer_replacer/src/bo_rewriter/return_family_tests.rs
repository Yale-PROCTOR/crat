//! J13 first return-family carrier controls over actual fixture decisions.
//! Results are discarded by callers; call-result receiver adaptation is not
//! part of this first stage. No model or decision is injected.

use std::collections::BTreeSet;

use rustc_middle::mir::RETURN_PLACE;

use super::{
    bridge_receipt::{
        BridgeCalleeId, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
        SignatureClassId,
    },
    decision::{Decision, lifetime::FnSignatureSlot, seam::Form},
};

#[derive(Clone, Copy, Debug)]
enum Family {
    Nullable,
    Slice,
}

fn input(family: Family) -> &'static str {
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
        // Deliberate probe-shape change: the body still needs a mutable slice,
        // but the returned value is bare p. Returning p.offset(1) remains a
        // separate, unbuilt return-reslice carrier; this test does not admit it.
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

fn check(family: Family) {
    let source = input(family);
    let (emitted, lifetime) = ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("original fixture AST");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one return-family decision call");
        let solve = super::model_cache::solve_receipt();
        println!("RETURN-FAMILY {family:?} solve={solve:#?}\ninput={source}");
        assert!(solve.is_some(), "tiny fixture solve receipt required");
        let (subject, decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual source parameter");
        let node = (subject.fn_did, subject.hir_id);
        let candidate = ctx.hypothetical.entries.iter().find(|(subject, _)| (subject.fn_did, subject.hir_id) == node)
            .map(|(_, decision)| decision);
        for local in [subject.local, RETURN_PLACE] {
            let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
                .and_then(|slots| slots.slot_for_local_depth(local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)));
            assert_eq!(kind, Some(&super::SlotKind::Ref), "actual source/return model premise: {family:?}, {local:?}");
        }
        let flow = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&subject.fn_did)).expect("retained native return-flow facts");
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        assert!(flow.body.depth0_value_flows().contains(&(
            SlotOwner::Local(subject.local), SlotOwner::Local(RETURN_PLACE))), "actual native parameter-to-return premise");
        let return_sites = ctx.facts.return_sites.iter().filter(|site| site.owner == subject.fn_did
            && site.root == Some(subject.hir_id)).collect::<Vec<_>>();
        let [return_site] = return_sites.as_slice() else { panic!("one exact bare parameter return site") };
        assert_eq!(return_site.source_shape, "bare-local");
        assert_eq!(tcx.sess.source_map().span_to_snippet(return_site.span).unwrap(), "p");
        let permit = ctx.lifetime_eligibility.return_permit(node);
        println!("RETURN-FAMILY {family:?}: candidate={candidate:?}; final={decision:?}; permit={permit:?}; failure={:?}; raw_uses={:?}",
            ctx.lifetime_eligibility.failure(node), ctx.facts.raw_only_uses.get(&node));

        // Production requirements start here. The existing no-permit/use hold
        // is the intended RED, not a failed model-admission premise.
        assert!(permit.is_some(), "return-family carrier must obtain its real native-origin permit: {family:?}; candidate={candidate:?}; final={decision:?}");
        let expected = match family {
            Family::Nullable => Form::Opt { mutable: true, slice: false },
            Family::Slice => Form::Slice { mutable: true },
        };
        let family_matches = match decision {
            Decision::Opt { mutable, slice, .. } => matches!(family, Family::Nullable) && *mutable && !*slice,
            Decision::Slice { mutable, .. } => matches!(family, Family::Slice) && *mutable,
            Decision::Ref { .. } | Decision::InferredRef { .. } | Decision::Box(_) | Decision::Degraded(_) => false,
        };
        assert!(family_matches, "returning preserves the real source family: {decision:?}");
        let function_plan = table.lifetime_plan.function(subject.fn_did).expect("parameter-tied return lifetime plan");
        let lifetime = function_plan.lifetime_for(FnSignatureSlot::arg(1, 0, 0)).expect("source parameter lifetime").to_owned();
        assert_eq!(function_plan.lifetime_for(FnSignatureSlot::RETURN), Some(lifetime.as_str()));
        assert!(function_plan.receipt().contains("return_lifetime_reused=true"));
        let digest = function_plan.digest();
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual return-family emission plan");
        let owner = SignatureClassId::of(subject.fn_did);
        assert!(emission.plan.class_finalization.classes.get(&owner).is_some_and(super::plan::SignatureClassPlan::is_ready));
        let held = emission.plan.held_classes();
        assert!(!held.contains(&owner));
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(&held, &BTreeSet::new(), &table).unwrap();
        let (files, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
            emission.plan.root_file.as_ref(), &table, Some(&emission.plan.terminal_call_plans)).expect("actual family AST emission");
        assert_eq!(files.len(), 1);
        let emitted = files.into_values().next().unwrap();
        let source_file = tcx.sess.source_map().lookup_source_file(return_site.span.lo());
        let file = super::bridge_custody_export::file_label(&super::file_key(&source_file.name).unwrap());
        let lo = return_site.span.lo().0 - source_file.start_pos.0;
        let hi = return_site.span.hi().0 - source_file.start_pos.0;
        let events = emission.plan.bridge_events(&held);
        let exact = events.iter().filter(|event| event.site.owner_class == owner && event.site.caller == subject.fn_did
            && event.site.callee == BridgeCalleeId::Local(subject.fn_did) && event.site.arm == "glue"
            && event.site.file == file && event.site.lo == lo && event.site.hi == hi
            && event.site.bridge_kind == "return-raw-to-ref").collect::<Vec<_>>();
        assert_eq!(exact.iter().filter(|event| event.stage == BridgeReceiptStage::Plan).count(), 1, "one exact return plan: {events:#?}");
        let terminal = exact.iter().filter(|event| event.stage == BridgeReceiptStage::Terminal).collect::<Vec<_>>();
        let [terminal] = terminal.as_slice() else { panic!("one exact terminal return receipt: {events:#?}") };
        assert_eq!(terminal.state, BridgeReceiptState::Applied);
        assert_eq!(terminal.expected_form, expected.key());
        assert_eq!(terminal.retention, BridgeRetentionTier::T1);
        assert!(terminal.waiver_id.is_none());
        assert!(terminal.site.position.contains(&digest), "return receipt binds its actual lifetime plan");
        println!("RETURN-FAMILY {family:?}: return_receipt={terminal:#?}\nemitted={emitted}");
        (emitted, lifetime)
    }).expect("original owned-storage return fixture type-checks");
    assert!(
        super::verify::type_checks_str(&emitted),
        "actual emitted return-family tree must type/borrow-check: {family:?}\n{emitted}"
    );
    rustc_span::create_session_globals_then(
        rustc_span::edition::Edition::Edition2018,
        &[],
        None,
        || {
            let session = rustc_session::parse::ParseSess::new(
                rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec(),
            );
            let krate = super::slice_use_inventory_tests::parse_crate(
                &session,
                "return-family-delivered.rs",
                &emitted,
            )
            .unwrap();
            let functions = krate
                .items
                .iter()
                .filter_map(|item| match &item.kind {
                    rustc_ast::ItemKind::Fn(function)
                        if function.ident.name.as_str() == "target" =>
                    {
                        Some(function)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            let [function] = functions.as_slice() else { panic!("one actual target declaration") };
            let rustc_ast::FnRetTy::Ty(return_type) = &function.sig.decl.output else {
                panic!("explicit emitted return type")
            };
            let compact = |ty: &rustc_ast::Ty| {
                rustc_ast_pretty::pprust::ty_to_string(ty)
                    .chars()
                    .filter(|character| !character.is_whitespace())
                    .collect::<String>()
            };
            let expected = match family {
                Family::Nullable => format!("Option<&'{lifetime}muti32>"),
                Family::Slice => format!("&'{lifetime}mut[i32]"),
            };
            assert_eq!(
                compact(&function.sig.decl.inputs[0].ty),
                expected,
                "complete parameter family declaration"
            );
            assert_eq!(
                compact(return_type),
                expected,
                "return declaration reuses the exact parameter family and lifetime"
            );
        },
    );
}

#[test]
fn return_family_nullable_mutable_parameter_return_is_tied() {
    check(Family::Nullable);
}

#[test]
fn return_family_mutable_slice_bare_parameter_return_is_tied() {
    check(Family::Slice);
}

#[test]
fn return_family_null_constructor_uses_compiler_identity() {
    use rustc_hir::{
        Expr, ExprKind,
        intravisit::{Visitor, walk_expr},
    };
    let source = r#"
        #![allow(dead_code)]
        static mut VALUE: i32 = 1;
        unsafe fn null_mut() -> *mut i32 { &raw mut VALUE }
        unsafe fn receive(_: *mut i32) {}
        unsafe fn caller() {
            receive(core::ptr::null_mut());
            receive(core::ptr::null::<i32>() as *mut i32);
            receive(null_mut());
        }
    "#;
    let shapes = ::utils::compilation::run_compiler_on_str(source, |tcx| {
        struct V<'tcx> {
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
            shapes: Vec<&'static str>,
        }
        impl<'tcx> Visitor<'tcx> for V<'tcx> {
            fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
                if let ExprKind::Call(callee, arguments) = expression.kind
                    && let rustc_middle::ty::TyKind::FnDef(did, _) =
                        *self.tcx.typeck(callee.hir_id.owner).expr_ty(callee).kind()
                    && self.tcx.item_name(did).as_str() == "receive"
                {
                    assert_eq!(arguments.len(), 1);
                    self.shapes.push(
                        super::decision::emitability::classify_arg(self.tcx, &arguments[0]).key(),
                    );
                }
                walk_expr(self, expression);
            }
        }
        let caller = tcx
            .hir_body_owners()
            .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "caller")
            .unwrap();
        let mut visitor = V {
            tcx,
            shapes: Vec::new(),
        };
        visitor.visit_body(tcx.hir_body_owned_by(caller));
        visitor.shapes
    })
    .expect("compiler-identity control type-checks");
    assert_eq!(shapes, ["null-lit", "null-lit", "raw-expr"]);
}
