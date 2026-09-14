//! Equal-form local slice interface carriers (wave-5c).
//!
//! The seam deliberately emits no adapter for equal Slice forms. Its existing
//! input-form twin remains authoritative; this hook
//! completes only the slice-use receipt which looked exclusively for edits.

use rustc_hir::{ExprKind, HirId, ItemLocalId, Node, def::Res};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{DecisionTable, SubjectKind, seam::Form};
use crate::bo_rewriter::{
    bridge_receipt::SignatureClassId,
    mechanical_receipt::{
        CanonicalCallee, CanonicalLocation, MechanicalState, MechanicalSubjectKey,
        MechanicalTerminalReason, SliceUseReceiptPlan,
    },
};

const UNMAPPED: &str = "slice-use-existing-c-interface-carrier-unmapped:candidates=0";
const ADAPTER: &str = "owned-existing-c-same-slice";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Hold {
    Identity,
    Source,
    Form,
    MissingCarrier,
    AmbiguousCarrier,
    CarrierForm,
    Dependency,
}

fn prove(tcx: TyCtxt<'_>, table: &DecisionTable, plan: &SliceUseReceiptPlan) -> Result<Form, Hold> {
    let event = &plan.obligation.planned;
    let MechanicalSubjectKey::Local {
        owner,
        mir_local,
        slot_depth: 0,
    } = event.key.subject
    else {
        return Err(Hold::Source);
    };
    let CanonicalLocation::Hir {
        owner: hir_owner,
        item_local_id,
    } = plan.use_site.location
    else {
        return Err(Hold::Identity);
    };
    let Some(CanonicalCallee::Local(callee)) = plan.use_site.callee else {
        return Err(Hold::Identity);
    };
    let callee = callee.as_local().ok_or(Hold::Identity)?;
    let index = plan.use_site.argument_index.ok_or(Hold::Identity)? as usize;
    if owner != hir_owner
        || plan.use_site.owner != owner
        || plan.use_site != event.key.site
        || plan.owner_class != SignatureClassId::of(owner)
        || event.key.owner_class != plan.owner_class
        || event.source_shape != "bare-local"
        || event.argument_kind != "call-argument"
    {
        return Err(Hold::Identity);
    }
    let hir = HirId {
        owner: rustc_hir::OwnerId { def_id: owner },
        local_id: ItemLocalId::from_u32(item_local_id),
    };
    let Node::Expr(argument) = tcx.hir_node(hir) else { return Err(Hold::Identity) };
    let ExprKind::Path(path) = &argument.kind else { return Err(Hold::Source) };
    let Res::Local(binding) = tcx.typeck(owner).qpath_res(path, hir) else {
        return Err(Hold::Source);
    };
    let Node::Expr(call) = tcx.parent_hir_node(hir) else { return Err(Hold::Identity) };
    let ExprKind::Call(function, args) = call.kind else { return Err(Hold::Identity) };
    if args.get(index).is_none_or(|arg| arg.hir_id != hir)
        || argument.span.from_expansion()
        || !matches!(tcx.typeck(owner).expr_ty(function).kind(), TyKind::FnDef(did, _) if did.as_local() == Some(callee))
    {
        return Err(Hold::Identity);
    }
    let sources = table
        .entries
        .iter()
        .filter(|(s, _)| {
            s.fn_did == owner
                && s.local.as_u32() == mir_local
                && s.ptr_depth == 1
                && s.hir_id == binding
        })
        .collect::<Vec<_>>();
    let [(_, source)] = sources.as_slice() else { return Err(Hold::Source) };
    let form = super::seam::form_of(source);
    let mutable = match form {
        Form::Slice { mutable } => mutable,
        Form::Raw | Form::Ref { .. } | Form::Opt { .. } => return Err(Hold::Source),
    };
    let parameters = table
        .entries
        .iter()
        .filter(|(s, _)| {
            s.fn_did == callee
                && s.ptr_depth == 1
                && matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == index)
        })
        .collect::<Vec<_>>();
    let [(_, parameter)] = parameters.as_slice() else { return Err(Hold::Form) };
    let required = super::seam::form_of(parameter);
    if required != form || plan.source_form != form.key() || plan.candidate_form != form.key() {
        return Err(Hold::Form);
    }
    let carriers = table
        .seams
        .revert_found_form_edits
        .iter()
        .filter(|carrier| {
            carrier.owner_class == SignatureClassId::of(callee)
                && carrier.source_node == (owner, binding)
                && carrier.span.source_callsite() == argument.span.source_callsite()
                && carrier.arg_span.source_callsite() == argument.span.source_callsite()
        })
        .collect::<Vec<_>>();
    let [carrier] = carriers.as_slice() else {
        return Err(if carriers.is_empty() {
            Hold::MissingCarrier
        } else {
            Hold::AmbiguousCarrier
        });
    };
    let super::seam::SeamInputRendering::Adapter {
        spec,
        found: Form::Raw,
        ..
    } = &carrier.input
    else {
        return Err(Hold::CarrierForm);
    };
    if spec.core != super::seam::GlueCore::FromRawParts
        || spec.optional
        || spec.mutable != mutable
        || spec.len.is_none()
    {
        return Err(Hold::CarrierForm);
    }
    // The existing twin is created only after the seam accepts Ok(None), and
    // supplies the original input adapter if this source is later reverted.
    // Its length (possibly waived) never supplies a new width proof here.
    // Callee retraction is covered by this receipt's existing dependency.
    if !event
        .dependency_classes
        .contains(&SignatureClassId::of(callee))
    {
        return Err(Hold::Dependency);
    }
    Ok(form)
}

pub(crate) fn complete(tcx: TyCtxt<'_>, table: &mut DecisionTable) {
    let completions = table
        .slice_use_receipts
        .iter()
        .enumerate()
        .filter_map(|(index, plan)| {
            if plan.obligation.intended_terminal_state != MechanicalState::HeldNonmechanical
                || plan.obligation.intended_terminal_reason
                    != Some(MechanicalTerminalReason::EvidenceMissing(
                        UNMAPPED.to_owned(),
                    ))
            {
                return None;
            }
            // Failed proofs keep the existing typed missing-carrier hold intact.
            prove(tcx, table, plan).ok().map(|form| (index, form))
        })
        .collect::<Vec<_>>();
    for (index, form) in completions {
        let plan = &mut table.slice_use_receipts[index];
        plan.target_form = form.key().to_owned();
        plan.obligation.planned.expected_form = plan.target_form.clone();
        plan.adapter = ADAPTER.to_owned();
        plan.boundary_evidence = format!(
            "existing-c-input-twin:expected={};found={};same-form;original-argument",
            form.key(),
            form.key()
        );
        plan.obligation.intended_terminal_state = MechanicalState::Applied;
        plan.obligation.intended_terminal_reason = None;
    }
}

#[cfg(test)]
mod tests {
    use super::{super::Decision, *};
    const INPUT: &str = r###"#![allow(dead_code, unused_unsafe, unused_mut, non_snake_case)]
    pub mod adosc {
        extern "C" {
            #[no_mangle]
            fn __assert_rtn(_: *const std::os::raw::c_char,
            _: *const std::os::raw::c_char, _: std::os::raw::c_int,
            _: *const std::os::raw::c_char)
            -> !;
        }
        #[no_mangle]
        pub unsafe extern "C" fn ti_adosc_start(mut options:
                *const std::os::raw::c_double) -> std::os::raw::c_int {
            return *options.offset(1 as std::os::raw::c_int as isize) as
                        std::os::raw::c_int - 1 as std::os::raw::c_int;
        }
        #[no_mangle]
        pub unsafe extern "C" fn ti_adosc(mut size: std::os::raw::c_int,
            mut inputs: *const *const std::os::raw::c_double,
            mut options: *const std::os::raw::c_double,
            mut outputs: *const *mut std::os::raw::c_double)
            -> std::os::raw::c_int {
            let mut high: *const std::os::raw::c_double =
                *inputs.offset(0 as std::os::raw::c_int as isize);
            let mut low: *const std::os::raw::c_double =
                *inputs.offset(1 as std::os::raw::c_int as isize);
            let mut close: *const std::os::raw::c_double =
                *inputs.offset(2 as std::os::raw::c_int as isize);
            let mut volume: *const std::os::raw::c_double =
                *inputs.offset(3 as std::os::raw::c_int as isize);
            let short_period: std::os::raw::c_int =
                *options.offset(0 as std::os::raw::c_int as isize) as
                    std::os::raw::c_int;
            let long_period: std::os::raw::c_int =
                *options.offset(1 as std::os::raw::c_int as isize) as
                    std::os::raw::c_int;
            let start: std::os::raw::c_int =
                long_period - 1 as std::os::raw::c_int;
            if short_period < 1 as std::os::raw::c_int {
                return 1 as std::os::raw::c_int
            }
            if long_period < short_period { return 1 as std::os::raw::c_int }
            if size <= ti_adosc_start(options) {
                return 0 as std::os::raw::c_int
            }
            let short_per: std::os::raw::c_double =
                2 as std::os::raw::c_int as std::os::raw::c_double /
                    (short_period as std::os::raw::c_double +
                            1 as std::os::raw::c_int as std::os::raw::c_double);
            let long_per: std::os::raw::c_double =
                2 as std::os::raw::c_int as std::os::raw::c_double /
                    (long_period as std::os::raw::c_double +
                            1 as std::os::raw::c_int as std::os::raw::c_double);
            let mut output: *mut std::os::raw::c_double =
                *outputs.offset(0 as std::os::raw::c_int as isize);
            let mut sum: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            let mut short_ema: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            let mut long_ema: std::os::raw::c_double =
                0 as std::os::raw::c_int as std::os::raw::c_double;
            let mut i: std::os::raw::c_int = 0;
            i = 0 as std::os::raw::c_int;
            while i < size {
                let hl: std::os::raw::c_double =
                    *high.offset(i as isize) - *low.offset(i as isize);
                if hl != 0.0f64 {
                    sum +=
                        (*close.offset(i as isize) - *low.offset(i as isize) -
                                            *high.offset(i as isize) + *close.offset(i as isize)) / hl *
                            *volume.offset(i as isize)
                }
                if i == 0 as std::os::raw::c_int {
                    short_ema = sum;
                    long_ema = sum
                } else {
                    short_ema = (sum - short_ema) * short_per + short_ema;
                    long_ema = (sum - long_ema) * long_per + long_ema
                }
                if i >= start {
                    let fresh0 = output;
                    output = output.offset(1);
                    *fresh0 = short_ema - long_ema
                }
                i += 1
            }
            if !(output.offset_from(*outputs.offset(0 as std::os::raw::c_int
                                                            as isize)) as std::os::raw::c_long ==
                                        (size - ti_adosc_start(options)) as std::os::raw::c_long) as
                            std::os::raw::c_int as std::os::raw::c_long != 0 {
                __assert_rtn(([b't' as i8, b'i' as i8, b'_' as i8, b'a' as i8,
                                    b'd' as i8, b'o' as i8, b's' as i8, b'c' as i8,
                                    b'\0' as i8]).as_ptr(),
                    b"indicators/adosc.c\x00" as *const u8 as
                        *const std::os::raw::c_char, 73 as std::os::raw::c_int,
                    b"output - outputs[0] == size - ti_adosc_start(options)\x00"
                            as *const u8 as *const std::os::raw::c_char);
            } else {};
            return 0 as std::os::raw::c_int;
        }
    }
"###;

    #[test]
    fn w5c_wc1_adosc_two_equal_slice_calls() {
        let table = ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
            crate::bo_rewriter::decide_table(tcx).expect("W-C1 decisions")
        })
        .expect("W-C1 input compiles");
        for (subject, decision) in &table.entries {
            eprintln!(
                "W-C1 {:?} {:?} {:?}",
                subject.fn_did, subject.param_name, decision
            );
        }
        let rows = table
            .slice_use_receipts
            .iter()
            .flat_map(|p| p.materialize(true, false).1)
            .collect::<Vec<_>>();
        let receipt = crate::bo_rewriter::mechanical_receipt::render_slice_use_rows(&rows);
        eprintln!("W-C1 receipts\n{receipt}");
        let emitted =
            crate::bo_rewriter::emit_tests::ast_emitted_source_of(INPUT).expect("W-C1 emission");
        eprintln!("W-C1 emitted\n{emitted}");
        let completed = table
            .slice_use_receipts
            .iter()
            .filter(|p| p.adapter == ADAPTER)
            .collect::<Vec<_>>();
        assert_eq!(
            completed.len(),
            2,
            "both exact call sites must complete: {receipt}"
        );
        assert!(
            completed
                .iter()
                .all(|p| p.obligation.intended_terminal_state == MechanicalState::Applied)
        );
        let options = table
            .entries
            .iter()
            .filter(|(s, _)| s.param_name.as_deref() == Some("options"))
            .collect::<Vec<_>>();
        assert_eq!(options.len(), 2);
        assert!(
            options
                .iter()
                .all(|(_, d)| matches!(d, Decision::Slice { mutable: false, .. }))
        );
        let compact = emitted.split_whitespace().collect::<String>();
        assert_eq!(
            compact.matches("options:&[std::os::raw::c_double]").count(),
            2,
            "both signatures: {emitted}"
        );
        ::utils::compilation::run_compiler_on_str(&emitted, |tcx| {
            use rustc_hir::intravisit::{self, Visitor};
            struct Calls(usize);
            impl<'v> Visitor<'v> for Calls {
                fn visit_expr(&mut self, e: &'v rustc_hir::Expr<'v>) {
                    if let ExprKind::Call(f, args) = e.kind
                        && let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = f.kind
                        && path
                            .segments
                            .last()
                            .is_some_and(|s| s.ident.name.as_str() == "ti_adosc_start")
                    {
                        let [arg] = args else { panic!("one slice argument") };
                        let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = arg.kind else {
                            panic!("original slice binding")
                        };
                        assert_eq!(path.segments.last().unwrap().ident.name.as_str(), "options");
                        self.0 += 1;
                    }
                    intravisit::walk_expr(self, e);
                }
            }
            let mut calls = Calls(0);
            for owner in tcx.hir_body_owners() {
                calls.visit_body(tcx.hir_body_owned_by(owner));
            }
            assert_eq!(
                calls.0, 2,
                "both actual calls, excluding the assertion's string literal"
            );
        })
        .expect("emitted declarations and calls type/borrow-check");
        if let Some(dir) = std::env::var_os("CRAT_W5C_ARTIFACT_DIR") {
            let dir = std::path::PathBuf::from(dir);
            std::fs::write(dir.join("wc1-input.rs"), INPUT).unwrap();
            std::fs::write(dir.join("wc1-emitted.rs"), emitted).unwrap();
            std::fs::write(dir.join("wc1-receipts.tsv"), receipt).unwrap();
        }
    }

    fn fixture(check: impl FnOnce(TyCtxt<'_>, DecisionTable) + Send) {
        ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
            let table = crate::bo_rewriter::decide_table(tcx).unwrap();
            assert_eq!(
                table
                    .slice_use_receipts
                    .iter()
                    .filter(|p| p.adapter == ADAPTER)
                    .count(),
                2
            );
            check(tcx, table);
        })
        .unwrap();
    }

    fn reset(table: &mut DecisionTable) -> Vec<usize> {
        let ids = table
            .slice_use_receipts
            .iter()
            .enumerate()
            .filter_map(|(i, p)| (p.adapter == ADAPTER).then_some(i))
            .collect::<Vec<_>>();
        assert_eq!(ids.len(), 2);
        for &i in &ids {
            let p = &mut table.slice_use_receipts[i];
            p.adapter = "-".to_owned();
            p.obligation.intended_terminal_state = MechanicalState::HeldNonmechanical;
            p.obligation.intended_terminal_reason = Some(
                MechanicalTerminalReason::EvidenceMissing(UNMAPPED.to_owned()),
            );
        }
        ids
    }

    #[test]
    fn w5c_wc1_second_uncovered_call_stays_held() {
        fixture(|tcx, mut table| {
            let ids = reset(&mut table);
            assert_eq!(table.seams.revert_found_form_edits.len(), 2);
            table.seams.revert_found_form_edits.pop();
            complete(tcx, &mut table);
            assert_eq!(table.slice_use_receipts[ids[0]].adapter, ADAPTER);
            assert_eq!(
                table.slice_use_receipts[ids[1]]
                    .obligation
                    .intended_terminal_state,
                MechanicalState::HeldNonmechanical
            );
            let emission =
                crate::bo_rewriter::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &[])
                    .unwrap();
            assert!(
                emission
                    .plan
                    .held_classes()
                    .contains(&table.slice_use_receipts[ids[1]].owner_class)
            );
        });
    }

    #[test]
    fn w5c_wc1_duplicate_carrier_stays_held() {
        fixture(|tcx, mut table| {
            let ids = reset(&mut table);
            table
                .seams
                .revert_found_form_edits
                .push(table.seams.revert_found_form_edits[0].clone());
            assert_eq!(
                prove(tcx, &table, &table.slice_use_receipts[ids[0]]),
                Err(Hold::AmbiguousCarrier)
            );
            complete(tcx, &mut table);
            assert_eq!(
                table.slice_use_receipts[ids[0]]
                    .obligation
                    .intended_terminal_state,
                MechanicalState::HeldNonmechanical
            );
        });
    }

    #[test]
    fn w5c_wc1_unplaced_callee_and_form_mismatch_stay_held() {
        fixture(|tcx, table| {
            let plan = table
                .slice_use_receipts
                .iter()
                .find(|p| p.adapter == ADAPTER)
                .unwrap();
            let Some(CanonicalCallee::Local(callee)) = plan.use_site.callee else { unreachable!() };
            for decision in [
                Decision::Degraded(super::super::Degradation {
                    subject: "options".into(),
                    site: "unplaced-callee".into(),
                    reason: super::super::DegradeReason::SliceUseUnsupported,
                }),
                Decision::Ref { mutable: false },
                Decision::Opt {
                    mutable: false,
                    slice: true,
                    uses: vec![],
                },
                Decision::Slice {
                    mutable: true,
                    uses: vec![],
                },
            ] {
                let mut changed = table.clone();
                let ids = reset(&mut changed);
                changed
                    .entries
                    .iter_mut()
                    .find(|(s, _)| s.fn_did.to_def_id() == callee)
                    .unwrap()
                    .1 = decision;
                assert_eq!(
                    prove(tcx, &changed, &changed.slice_use_receipts[ids[0]]),
                    Err(Hold::Form)
                );
                complete(tcx, &mut changed);
                assert!(ids.iter().all(|i| {
                    changed.slice_use_receipts[*i]
                        .obligation
                        .intended_terminal_state
                        == MechanicalState::HeldNonmechanical
                }));
            }
        });
    }

    #[test]
    fn w5c_wc1_missing_dependency_stays_held() {
        fixture(|tcx, mut table| {
            let ids = reset(&mut table);
            table.slice_use_receipts[ids[0]]
                .obligation
                .planned
                .dependency_classes
                .clear();
            assert_eq!(
                prove(tcx, &table, &table.slice_use_receipts[ids[0]]),
                Err(Hold::Dependency)
            );
            complete(tcx, &mut table);
            assert_eq!(
                table.slice_use_receipts[ids[0]]
                    .obligation
                    .intended_terminal_state,
                MechanicalState::HeldNonmechanical
            );
        });
    }

    #[test]
    fn w5c_wc1_completion_preserves_seam_ownership_and_retraction() {
        fixture(|tcx, mut table| {
            let ids = reset(&mut table);
            let seams = table.seams.clone();
            complete(tcx, &mut table);
            assert_eq!(table.seams.edits, seams.edits);
            assert_eq!(table.seams.zero_bridges, seams.zero_bridges);
            assert_eq!(
                table.seams.revert_found_form_edits,
                seams.revert_found_form_edits
            );
            assert_eq!(
                table.seams.interface_dependencies,
                seams.interface_dependencies
            );
            for i in ids {
                let p = &table.slice_use_receipts[i];
                assert_eq!(
                    p.obligation.events(true, false)[1].state,
                    MechanicalState::Applied
                );
                assert_eq!(
                    p.obligation.events(false, false)[1].state,
                    MechanicalState::Dropped
                );
                assert_eq!(
                    p.obligation.events(true, true)[1].state,
                    MechanicalState::Dropped
                );
            }
        });
    }

    #[test]
    fn w5c_wc1_stale_identity_and_twin_form_stay_held() {
        fixture(|tcx, table| {
            let plan = table
                .slice_use_receipts
                .iter()
                .find(|p| p.adapter == ADAPTER)
                .unwrap();
            let mut changed = plan.clone();
            changed.use_site.argument_index = Some(1);
            changed.obligation.planned.key.site = changed.use_site.clone();
            assert_eq!(prove(tcx, &table, &changed), Err(Hold::Identity));
            let mut changed = plan.clone();
            if let MechanicalSubjectKey::Local { mir_local, .. } =
                &mut changed.obligation.planned.key.subject
            {
                *mir_local += 1;
            }
            assert_eq!(prove(tcx, &table, &changed), Err(Hold::Source));
            let mut changed = table.clone();
            let super::super::seam::SeamInputRendering::Adapter { spec, .. } =
                &mut changed.seams.revert_found_form_edits[0].input
            else {
                unreachable!()
            };
            spec.optional = true;
            assert_eq!(prove(tcx, &changed, plan), Err(Hold::CarrierForm));
        });
    }

    #[test]
    fn w5c_wc1_source_retraction_uses_the_original_input_twin() {
        ::utils::compilation::run_compiler_on_input(
            ::utils::compilation::str_to_input(INPUT),
            |tcx| {
                let capture = crate::bo_rewriter::ast_transform::capture_ast(tcx).unwrap();
                let table = crate::bo_rewriter::decide_table(tcx).unwrap();
                let emission = crate::bo_rewriter::emit_files(
                    tcx,
                    &table,
                    &rustc_hash::FxHashSet::default(),
                    &[],
                )
                .unwrap();
                let caller = table
                    .slice_use_receipts
                    .iter()
                    .find(|p| p.adapter == ADAPTER)
                    .unwrap()
                    .owner_class;
                let reverted = std::collections::BTreeSet::from([caller]);
                let reverts = crate::bo_rewriter::ast_transform::revert_set_from_classes_and_atoms(
                    &reverted,
                    &std::collections::BTreeSet::new(),
                    &table,
                )
                .unwrap();
                let (files, _, _, _) = crate::bo_rewriter::ast_transform::ast_emitted_files_from(
                    tcx,
                    &capture,
                    &reverts,
                    emission.plan.root_file.as_ref(),
                    &table,
                    Some(&emission.plan.terminal_call_plans),
                )
                .unwrap();
                let emitted = files.into_values().next().unwrap();
                let compact = emitted.split_whitespace().collect::<String>();
                assert_eq!(
                    compact
                        .matches("from_raw_parts(options,crate::FALLBACK_SLICE_EXTENT)")
                        .count(),
                    2,
                    "both original twins: {emitted}"
                );
                assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
            },
        )
        .unwrap();
    }
}
