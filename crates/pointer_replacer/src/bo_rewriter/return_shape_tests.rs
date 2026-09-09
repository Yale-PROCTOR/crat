//! J13–J15 mixed null/parameter returns, with real native model premises.

use std::collections::BTreeSet;

use rustc_hir::{
    Expr, ExprKind, QPath,
    def::Res,
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::{
    mir::RETURN_PLACE,
    ty::{TyCtxt, TyKind},
};

use super::{
    bridge_receipt::SignatureClassId,
    decision::{Decision, SubjectKind, lifetime::FnSignatureSlot, seam::Form},
};

#[test]
fn return_shape_mixed_null_and_parameter_keeps_a_required_parameter() {
    let source = r#"
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
    let (emitted, argument_index) = ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original mixed-return AST capture");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one actual mixed-return decision call");
        let solve = super::model_cache::solve_receipt();
        println!("RETURN-SHAPE mixed-null-parameter solve={solve:#?}\ninput={source}");
        assert!(solve.is_some(), "actual tiny-fixture solve receipt is mandatory");
        let (parameter, decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual pointer source parameter");
        let SubjectKind::Param { hir_index } = parameter.kind else { panic!("p is a real parameter") };
        assert_eq!(hir_index, 1, "the boolean occupies argument zero");
        let node = (parameter.fn_did, parameter.hir_id);
        for local in [parameter.local, RETURN_PLACE] {
            let kind = ctx.slots.fn_local_slots.get(&parameter.fn_did)
                .and_then(|slots| slots.slot_for_local_depth(local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(parameter.fn_did, slot)));
            println!("RETURN-SHAPE actual native kind {local:?}={kind:?}");
            assert_eq!(kind, Some(&super::SlotKind::Ref), "actual source/return model-Ref premise");
        }
        let sites = ctx.facts.return_sites.iter().filter(|site| site.owner == parameter.fn_did)
            .collect::<Vec<_>>();
        println!("RETURN-SHAPE exact original return sites={sites:#?}");
        assert_eq!(sites.len(), 2, "exact explicit-null and tail-parameter return identity set");
        let nulls = sites.iter().filter(|site| site.source_shape == "null-lit").collect::<Vec<_>>();
        let values = sites.iter().filter(|site| site.source_shape == "bare-local").collect::<Vec<_>>();
        let ([null], [value]) = (nulls.as_slice(), values.as_slice()) else {
            panic!("one null-lit and one bare-local return site");
        };
        assert!(null.root.is_none());
        assert_eq!(value.root, Some(parameter.hir_id));
        assert_eq!(tcx.sess.source_map().span_to_snippet(null.span).unwrap(), "core::ptr::null_mut()");
        assert_eq!(tcx.sess.source_map().span_to_snippet(value.span).unwrap(), "p");
        let origins = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&parameter.fn_did)).expect("existing native origin facts");
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        let native_flows = origins.body.depth0_value_flows();
        println!("RETURN-SHAPE native flows={native_flows:?}");
        assert!(native_flows.contains(&(SlotOwner::Local(parameter.local), SlotOwner::Local(RETURN_PLACE))),
            "actual parameter-to-return native origin");
        let permit = ctx.lifetime_eligibility.return_permit(node);
        println!("RETURN-SHAPE candidate={:?}; terminal={decision:#?}; permit={permit:?}; permit_failure={:?}; raw_uses={:?}; return_interface={:?}; interface_failure={:?}",
            ctx.hypothetical.entries.iter().find(|(subject, _)| (subject.fn_did, subject.hir_id) == node).map(|(_, decision)| decision),
            ctx.lifetime_eligibility.failure(node), ctx.facts.raw_only_uses.get(&node),
            table.return_interfaces.functions.get(&parameter.fn_did), table.return_interfaces.failures.get(&parameter.fn_did));
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual mixed-return emission plan");
        let owner = SignatureClassId::of(parameter.fn_did);
        println!("RETURN-SHAPE owner={owner:?}; class={:#?}; hold_reasons={:?}",
            emission.plan.class_finalization.classes.get(&owner), emission.plan.class_hold_reason(owner));
        assert!(permit.is_some(), "the real non-null parameter origin already licenses its returned branch");
        let lifetime_plan = table.lifetime_plan.function(parameter.fn_did)
            .expect("actual native lifetime plan for the parameter and returned origin");
        let lifetime = lifetime_plan.lifetime_for(FnSignatureSlot::arg(hir_index + 1, 0, 0))
            .expect("lifetime of the actual pointer parameter position");
        assert_eq!(lifetime_plan.lifetime_for(FnSignatureSlot::RETURN), Some(lifetime));
        println!("RETURN-SHAPE native lifetime={lifetime}; digest={}", lifetime_plan.digest());

        // The mixed-shape production requirements follow all native premises.
        let required_parameter = match decision {
            Decision::Ref { mutable: true } => true,
            Decision::Ref { mutable: false } | Decision::InferredRef { .. }
            | Decision::Slice { .. } | Decision::Opt { .. } | Decision::Box(_)
            | Decision::Degraded(_) => false,
        };
        assert!(required_parameter, "return nullability must not make the always-dereferenced parameter optional: {decision:#?}");
        let interface = table.return_interfaces.functions.get(&parameter.fn_did)
            .expect("mixed return has a complete terminal borrowed interface");
        assert_eq!(interface.form, Form::Opt { mutable: true, slice: false },
            "null belongs to the return's Option independently of p's required Ref form");
        assert_eq!(interface.pointee, "i32");
        assert_eq!(interface.lifetime, lifetime);
        assert_eq!(interface.lifetime_plan_digest, lifetime_plan.digest());
        assert!(emission.plan.class_finalization.classes[&owner].is_ready(),
            "both return branches are mechanically placed");
        let held = emission.plan.held_classes();
        assert!(!held.contains(&owner));
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(&held, &BTreeSet::new(), &table)
            .expect("actual mixed-return final class selection");
        let (files, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
            emission.plan.root_file.as_ref(), &table, Some(&emission.plan.terminal_call_plans))
            .expect("actual mixed-return AST emission");
        assert_eq!(files.len(), 1);
        (files.into_values().next().unwrap(), hir_index)
    }).expect("original valid-stack mixed-return fixture compiles");
    assert!(
        super::verify::type_checks_str(&emitted),
        "mixed return output must type/borrow-check:\n{emitted}"
    );
    ::utils::compilation::run_compiler_on_str(&emitted, |tcx| {
        let target = tcx
            .hir_body_owners()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == "target")
            .expect("actual emitted target");
        let signature = tcx.fn_sig(target).skip_binder().skip_binder();
        let TyKind::Ref(parameter_region, parameter_pointee, parameter_mutability) =
            *signature.inputs()[argument_index].kind()
        else {
            panic!("actual emitted p remains a required reference");
        };
        assert!(parameter_mutability.is_mut());
        assert_eq!(parameter_pointee, tcx.types.i32);
        let TyKind::Adt(option, arguments) = *signature.output().kind() else {
            panic!("actual emitted return is Option")
        };
        assert_eq!(tcx.item_name(option.did()).as_str(), "Option");
        assert_eq!(tcx.crate_name(option.did().krate).as_str(), "core");
        let TyKind::Ref(return_region, pointee, mutable) = *arguments.type_at(0).kind() else {
            panic!("Option payload is a reference")
        };
        assert!(mutable.is_mut());
        assert_eq!(pointee, tcx.types.i32);
        assert_eq!(
            return_region, parameter_region,
            "the emitted return reuses the existing p lifetime"
        );
        let body = tcx.hir_body_owned_by(target);
        let rustc_hir::PatKind::Binding(_, parameter_hir, _, _) =
            body.params[argument_index].pat.kind
        else {
            panic!("actual emitted plain p binding");
        };
        struct Branches<'tcx> {
            tcx: TyCtxt<'tcx>,
            owner: rustc_hir::def_id::LocalDefId,
            option: rustc_hir::def_id::DefId,
            parameter: rustc_hir::HirId,
            null_returns: usize,
            some_parameter: usize,
        }
        impl<'tcx> Visitor<'tcx> for Branches<'tcx> {
            fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
                if let ExprKind::Ret(Some(value)) = expression.kind
                    && let ExprKind::Path(QPath::Resolved(_, path)) = value.kind
                    && path
                        .segments
                        .last()
                        .is_some_and(|segment| segment.ident.name.as_str() == "None")
                    && matches!(path.res, Res::Def(..))
                    && matches!(self.tcx.typeck(self.owner).expr_ty(value).kind(),
                        TyKind::Adt(definition, _) if definition.did() == self.option)
                {
                    self.null_returns += 1;
                }
                if let ExprKind::Call(callee, [argument]) = expression.kind
                    && let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind
                    && path
                        .segments
                        .last()
                        .is_some_and(|segment| segment.ident.name.as_str() == "Some")
                    && matches!(path.res, Res::Def(..))
                    && let ExprKind::Path(QPath::Resolved(_, argument_path)) = argument.kind
                    && argument_path.res == Res::Local(self.parameter)
                    && matches!(self.tcx.typeck(self.owner).expr_ty(expression).kind(),
                        TyKind::Adt(definition, _) if definition.did() == self.option)
                {
                    self.some_parameter += 1;
                }
                walk_expr(self, expression);
            }
        }
        let mut branches = Branches {
            tcx,
            owner: target,
            option: option.did(),
            parameter: parameter_hir,
            null_returns: 0,
            some_parameter: 0,
        };
        branches.visit_expr(body.value);
        assert_eq!(
            branches.null_returns, 1,
            "the explicit null return is actually None"
        );
        assert_eq!(
            branches.some_parameter, 1,
            "the returned p branch is actually Some(p)"
        );
    })
    .expect("actual emitted signature and branch inspection; no model entry");
    println!("RETURN-SHAPE mixed-null-parameter emitted={emitted}");
}

#[test]
fn return_shape_constant_parameter_offset_returns_the_remaining_slice() {
    let source = r#"
        #![allow(dead_code, unused_unsafe)]
        unsafe fn target(p: *mut i32) -> *mut i32 {
            *p.offset(1) += 1;
            p.offset(1)
        }
        pub unsafe fn entry() -> i32 {
            let mut values = [3, 5, 7];
            let q = target(values.as_mut_ptr());
            *q.offset(0) += 1;
            *q.offset(0) + *q.offset(1)
        }
    "#;
    let (emitted, argument_index) = ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original reslice AST capture");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("one actual reslice decision call");
        let solve = super::model_cache::solve_receipt();
        println!("RETURN-SHAPE constant-reslice solve={solve:#?}\ninput={source}");
        assert!(solve.is_some(), "actual tiny-fixture solve receipt is mandatory");
        let (parameter, decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p")
            .expect("actual reslice parameter");
        let (receiver, receiver_decision) = table.entries.iter().find(|(subject, _)| subject.label == "entry::q")
            .expect("actual consumed suffix receiver");
        let SubjectKind::Param { hir_index } = parameter.kind else { panic!("p is a parameter") };
        let node = (parameter.fn_did, parameter.hir_id);
        for (owner, local) in [(parameter.fn_did, parameter.local), (parameter.fn_did, RETURN_PLACE),
            (receiver.fn_did, receiver.local)] {
            let kind = ctx.slots.fn_local_slots.get(&owner)
                .and_then(|slots| slots.slot_for_local_depth(local, 0))
                .and_then(|slot| ctx.model.get(&super::SlotRef::Local(owner, slot)));
            println!("RETURN-SHAPE constant-reslice native kind {owner:?}/{local:?}={kind:?}");
            assert_eq!(kind, Some(&super::SlotKind::Ref), "actual source/return/receiver model-Ref premise");
        }
        let sites = ctx.facts.return_sites.iter().filter(|site| site.owner == parameter.fn_did)
            .collect::<Vec<_>>();
        println!("RETURN-SHAPE constant-reslice exact sites={sites:#?}");
        let [site] = sites.as_slice() else { panic!("one exact constant-offset return site") };
        assert_eq!(site.source_shape, "raw-expr");
        assert_eq!(site.root, Some(parameter.hir_id));
        assert_eq!(tcx.sess.source_map().span_to_snippet(site.span).unwrap(), "p.offset(1)");
        let body = tcx.hir_body_owned_by(parameter.fn_did);
        let ExprKind::Block(block, _) = body.value.kind else { panic!("actual target body block") };
        let tail = block.expr.expect("actual returned offset expression");
        assert_eq!(tail.span, site.span);
        let ExprKind::MethodCall(method, base, [offset], _) = tail.kind else { panic!("exact original offset method") };
        assert_eq!(method.ident.name.as_str(), "offset");
        assert!(matches!(base.kind, ExprKind::Path(QPath::Resolved(_, path))
            if path.res == Res::Local(parameter.hir_id)));
        assert!(matches!(offset.kind, ExprKind::Lit(_)), "only this positive constant offset is exercised");
        assert_eq!(tcx.sess.source_map().span_to_snippet(offset.span).unwrap(), "1");
        let origins = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
            .and_then(|flows| flows.get(&parameter.fn_did)).expect("actual native reslice origins");
        use crate::analyses::borrow_ownership::slots::SlotOwner;
        let flows = origins.body.depth0_value_flows();
        println!("RETURN-SHAPE constant-reslice native flows={flows:?}");
        assert!(flows.contains(&(SlotOwner::Local(parameter.local), SlotOwner::Local(RETURN_PLACE))),
            "the returned pointer actually originates in p");
        let permit = ctx.lifetime_eligibility.return_permit(node);
        println!("RETURN-SHAPE constant-reslice candidate={:?}; final={decision:#?}; receiver={receiver_decision:#?}; permit={permit:?}; failure={:?}; return_interface={:?}; raw_uses={:?}",
            ctx.hypothetical.entries.iter().find(|(subject, _)| (subject.fn_did, subject.hir_id) == node).map(|(_, decision)| decision),
            ctx.lifetime_eligibility.failure(node), table.return_interfaces.functions.get(&parameter.fn_did),
            ctx.facts.raw_only_uses.get(&node));
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans)
            .expect("actual reslice emission plan");
        let owner = SignatureClassId::of(parameter.fn_did);
        println!("RETURN-SHAPE constant-reslice class={:#?}; hold={:?}",
            emission.plan.class_finalization.classes.get(&owner), emission.plan.class_hold_reason(owner));

        // Production assertions follow real model, offset, and origin facts.
        assert!(permit.is_some(), "positive constant native parameter reslice requires its actual lifetime permit");
        assert_eq!(super::decision::seam::form_of(decision), Form::Slice { mutable: true });
        let interface = table.return_interfaces.functions.get(&parameter.fn_did)
            .expect("native reslice return interface");
        assert_eq!(interface.form, Form::Slice { mutable: true });
        let lifetimes = table.lifetime_plan.function(parameter.fn_did).expect("native source lifetime plan");
        let lifetime = lifetimes.lifetime_for(FnSignatureSlot::arg(hir_index + 1, 0, 0)).unwrap();
        assert_eq!(lifetimes.lifetime_for(FnSignatureSlot::RETURN), Some(lifetime));
        assert_eq!(interface.lifetime, lifetime);
        assert_eq!(interface.lifetime_plan_digest, lifetimes.digest());
        assert_eq!(super::decision::seam::form_of(receiver_decision), Form::Slice { mutable: true },
            "consumed q inherits the complete suffix interface");
        assert!(emission.plan.class_finalization.classes[&owner].is_ready());
        assert!(emission.plan.class_finalization.classes[&SignatureClassId::of(receiver.fn_did)].is_ready());
        let held = emission.plan.held_classes();
        let source_file = tcx.sess.source_map().lookup_source_file(site.span.lo());
        let lo = site.span.lo().0 - source_file.start_pos.0;
        let hi = site.span.hi().0 - source_file.start_pos.0;
        let events = emission.plan.bridge_events(&held);
        let returns = events.iter().filter(|event| event.site.owner_class == owner
            && event.site.caller == parameter.fn_did && event.site.lo == lo && event.site.hi == hi
            && event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
            && event.expected_form == (Form::Slice { mutable: true }).key()).collect::<Vec<_>>();
        let [returned] = returns.as_slice() else { panic!("one exact native reslice terminal receipt: {events:#?}") };
        assert_eq!(returned.state, super::bridge_receipt::BridgeReceiptState::Applied);
        assert_ne!(returned.extent, super::bridge_receipt::BridgeExtentKind::Fallback,
            "reslicing an existing Slice uses its remaining extent");
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(&held, &BTreeSet::new(), &table).unwrap();
        let (files, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
            emission.plan.root_file.as_ref(), &table, Some(&emission.plan.terminal_call_plans)).unwrap();
        assert_eq!(files.len(), 1);
        (files.into_values().next().unwrap(), hir_index)
    }).expect("original in-bounds constant-reslice fixture compiles");
    assert!(
        super::verify::type_checks_str(&emitted),
        "consumed native suffix output type/borrow-checks:\n{emitted}"
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
                "native-reslice.rs",
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
                        Some((item, function))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            let [(item, function)] = functions.as_slice() else {
                panic!("one actual emitted target")
            };
            let body = function.body.as_ref().expect("emitted target body");
            let rustc_ast::StmtKind::Expr(tail) =
                &body.stmts.last().expect("emitted return tail").kind
            else {
                panic!("reslice remains a native tail expression");
            };
            let rustc_ast::ExprKind::AddrOf(
                rustc_ast::BorrowKind::Ref,
                rustc_ast::Mutability::Mut,
                slice,
            ) = &tail.kind
            else {
                panic!("returned suffix is an actual mutable native slice borrow: {tail:#?}");
            };
            let rustc_ast::ExprKind::Index(base, range, _) = &slice.kind else {
                panic!("native reslice indexes its source slice")
            };
            let rustc_ast::ExprKind::Path(None, base_path) = &base.kind else {
                panic!("native reslice base is p")
            };
            assert_eq!(base_path.segments.last().unwrap().ident.name.as_str(), "p");
            let rustc_ast::ExprKind::Range(Some(start), None, rustc_ast::RangeLimits::HalfOpen) =
                &range.kind
            else {
                panic!("native suffix preserves the source slice's remaining bound");
            };
            assert!(matches!(start.kind, rustc_ast::ExprKind::Lit(_)));
            let start = rustc_ast_pretty::pprust::expr_to_string(start);
            let lower: usize = start
                .trim_end_matches("usize")
                .parse()
                .expect("literal native suffix lower bound");
            assert_eq!(lower, 1);
            // Structural RangeFrom semantics: a known length-3 borrowed input has
            // exactly 3-1 remaining elements. This does not execute the fixture or
            // assert that its separate legacy raw-to-slice call adapter has len=3.
            assert_eq!(3usize.checked_sub(lower), Some(2));
            let body_text = rustc_ast_pretty::pprust::item_to_string(item);
            assert!(
                !body_text.contains("from_raw_parts")
                    && !body_text.contains("FALLBACK_SLICE_EXTENT"),
                "native reslice must not reconstruct or fabricate a slice extent"
            );
        },
    );
    ::utils::compilation::run_compiler_on_str(&emitted, |tcx| {
        let target = tcx
            .hir_body_owners()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == "target")
            .unwrap();
        let signature = tcx.fn_sig(target).skip_binder().skip_binder();
        let TyKind::Ref(source_region, source_slice, source_mutability) =
            *signature.inputs()[argument_index].kind()
        else {
            panic!("native source slice reference")
        };
        let TyKind::Ref(return_region, returned_slice, return_mutability) =
            *signature.output().kind()
        else {
            panic!("native returned slice reference")
        };
        assert!(source_mutability.is_mut() && return_mutability.is_mut());
        assert!(matches!(source_slice.kind(), TyKind::Slice(element) if *element == tcx.types.i32));
        assert_eq!(source_slice, returned_slice);
        assert_eq!(source_region, return_region);
    })
    .expect("actual native reslice signature inspection; no model entry");
    let typed_consumer = format!(
        "{emitted}\nunsafe fn __crat_reslice_compile_only_consumer() -> i32 {{ let mut owned = [3, 5, 7]; let q: &mut [i32] = target(&mut owned); q[0] + q[1] }}"
    );
    assert!(
        super::verify::type_checks_str(&typed_consumer),
        "known length-3 borrowed input and both suffix elements are a compile-only consumer; no fixture execution"
    );
    println!(
        "RETURN-SHAPE constant-reslice structural remaining length=3-1=2; raw call-site extent is not reinterpreted\nemitted={emitted}"
    );
}
