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
            super::OverlapMode::PreciseReplay,
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
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_copy_plans)
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
            | Decision::Slice { .. } | Decision::Opt { .. } | Decision::Box(_) | Decision::NestedSlice { .. } | Decision::Cursor { .. }
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
        let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
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
