//! R365: the terminal Rust formal controls lending; the model kind is recorded.
//! A seam Form::Raw alone is insufficient because that vocabulary also folds Box.
use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Local, ty::TyCtxt};

use super::{
    Decision, DecisionTable, SubjectKind,
    ownership_fields_effects::{EffectsHold, NativeEffects},
    ownership_fields_hook::Hold,
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::{
        bridge_receipt::SignatureClassId,
        ownership_fields::{
            emission::Kind,
            export::{EvidenceOwner, Missing, MissingReason},
            lend::{FormalForm, LendHold},
        },
        plan::ClassFinalization,
    },
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeFormal {
    callee: LocalDefId,
    argument: usize,
    model_kind: Kind,
    emitted: FormalForm,
    terminal: super::seam::Form,
}

impl NativeFormal {
    pub(crate) fn identity(&self) -> (LocalDefId, usize) {
        (self.callee, self.argument)
    }

    pub(crate) fn model_kind(&self) -> Kind {
        self.model_kind
    }

    pub(crate) fn emitted(&self) -> FormalForm {
        self.emitted
    }

    pub(crate) fn terminal(&self) -> super::seam::Form {
        self.terminal
    }

    pub(crate) fn matches(&self, callee: LocalDefId, argument: usize) -> bool {
        self.callee == callee && self.argument == argument
    }

    pub(crate) fn require_lend(&self) -> Result<(), Hold> {
        if self.emitted == FormalForm::Box {
            Err(Hold::Lend(LendHold::OwningCallee))
        } else {
            Ok(())
        }
    }
}

fn missing(field: &'static str) -> Hold {
    Hold::Missing(Missing {
        owner: EvidenceOwner::NativeIdentity,
        reason: MissingReason::Field(field),
    })
}

/// Read an actual completed class snapshot, including restoration to the input
/// interface. Callers must derive/check this again after any class recovery.
#[allow(clippy::too_many_arguments)]
pub(crate) fn resolve(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    table: &DecisionTable,
    classes: &ClassFinalization,
    callee: LocalDefId,
    argument: usize,
) -> Result<NativeFormal, Hold> {
    if argument
        >= tcx
            .fn_sig(callee.to_def_id())
            .skip_binder()
            .skip_binder()
            .inputs()
            .len()
    {
        return Err(Hold::Identity);
    }
    let formal = slots
        .fn_local_slots
        .get(&callee)
        .and_then(|u| u.slot_for_local_depth(Local::from_usize(argument + 1), 0))
        .map(|slot| SlotRef::Local(callee, slot))
        .ok_or_else(|| missing("native-formal-slot"))?;
    let model_kind = match model.get(&formal) {
        Some(SlotKind::Owning) => Kind::Owning,
        Some(SlotKind::Raw) => Kind::Raw,
        Some(SlotKind::Ref) => Kind::Ref,
        None => return Err(missing("native-formal-kind")),
    };
    let rows: Vec<_> = table
        .entries
        .iter()
        .filter(|(subject, _)| {
            subject.fn_did == callee
                && matches!(subject.kind,
            SubjectKind::Param { hir_index } if hir_index == argument)
        })
        .collect();
    let [(_, decision)] = rows.as_slice() else {
        return Err(missing("terminal-formal-subject"));
    };
    let live = classes
        .classes
        .get(&SignatureClassId::of(callee))
        .is_some_and(|c| c.is_ready());
    let is_box = match decision {
        Decision::Box(_) => true,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Cursor { .. }
        | Decision::Opt { .. }
        | Decision::Degraded(_) => false,
    };
    let terminal = crate::bo_rewriter::terminal_parameter_form(table, classes, callee, argument);
    let emitted = if live && is_box {
        FormalForm::Box
    } else {
        // For every other representation, the common terminal interface
        // resolver supplies the placed form or the actual restored input.
        match terminal {
            super::seam::Form::Raw => FormalForm::MutableRaw,
            super::seam::Form::Ref { mutable: true }
            | super::seam::Form::Slice { mutable: true } => FormalForm::MutableReference,
            super::seam::Form::Ref { mutable: false }
            | super::seam::Form::Slice { mutable: false } => FormalForm::SharedReference,
            _ => return Err(Hold::Lend(LendHold::Formal)),
        }
    };
    Ok(NativeFormal {
        callee,
        argument,
        model_kind,
        emitted,
        terminal,
    })
}

pub(crate) fn require_nonconsuming(
    effects: &NativeEffects<'_>,
    formal: &NativeFormal,
) -> Result<&'static str, Hold> {
    formal.require_lend()?;
    match effects.certify(formal.callee, formal.argument) {
        Ok(proof) if proof.matches(effects, formal.callee, formal.argument) => Ok(proof.scope()),
        Ok(_) => Err(Hold::Identity),
        Err(EffectsHold::Retirement(_)) => Err(Hold::Lend(LendHold::ConsumingCallee)),
        Err(other) => Err(Hold::NativeEffects(other)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bo_rewriter as bo;

    #[test]
    fn r365_native_owning_raw_formal_with_free_is_consuming() {
        let source =
            bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);")
                .replace(
                    "*output=*input+1.0;",
                    "free(output as *mut core::ffi::c_void);",
                )
                .replace("let result=*pl1+*pl2;", "let result=*pl1;")
                .replace("free(pl2 as *mut core::ffi::c_void);", "");
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let (table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let program = bo::collect_program(tcx);
            let callee = *program
                .functions
                .iter()
                .find(|id| tcx.def_path_str(id.to_def_id()) == "edt")
                .unwrap();
            let prepared = bo::prepare_plan_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )
            .unwrap();
            let formal = resolve(
                tcx,
                &ctx.slots,
                &ctx.model,
                &table,
                &prepared.plan.class_finalization,
                callee,
                1,
            )
            .unwrap();
            assert_eq!(formal.model_kind(), Kind::Owning);
            let Some(super::super::raw_boundary::RetentionVerdict::NoRetain { certificate }) =
                ctx.retention.get(callee, 1)
            else {
                panic!("free remains independently NoRetain")
            };
            ctx.retention
                .verify_certificate(callee, 1, certificate)
                .unwrap();
            // The invariant: the owner is NEVER lent into a callee that frees
            // it. Two admissible readings of this chain (R407-9 / R217-2(a)
            // golden migration): without wave-6a's W6A-C1 the formal stays
            // raw and the lend arm refuses it as consuming; with W6A-C1 the
            // formal is a Box parameter (`edt(input, output) { free(output) }`
            // with `pl2` never used after) and the lend arm refuses it as
            // owning — the move rule takes over.
            let verdict = require_nonconsuming(&NativeEffects::derive(&program), &formal);
            assert!(
                matches!(
                    (formal.emitted(), &verdict),
                    (
                        FormalForm::MutableRaw,
                        Err(Hold::Lend(LendHold::ConsumingCallee))
                    ) | (FormalForm::Box, Err(Hold::Lend(LendHold::OwningCallee)))
                ),
                "{:?} / {verdict:?}",
                formal.emitted()
            );
        })
        .unwrap();
    }

    #[test]
    fn r365_formal_control_distinguishes_live_box_and_recovered_raw() {
        let source =
            bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);");
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let (mut table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let program = bo::collect_program(tcx);
            let callee = *program
                .functions
                .iter()
                .find(|id| tcx.def_path_str(id.to_def_id()) == "edt")
                .unwrap();
            let mut prepared = bo::prepare_plan_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )
            .unwrap();
            let plan = table
                .entries
                .iter()
                .find_map(|(s, d)| match d {
                    Decision::Box(plan) if s.param_name.as_deref() == Some("pl1") => {
                        Some(plan.clone())
                    }
                    _ => None,
                })
                .expect("actual caller Box plan");
            // Deliberate finalized-interface perturbation: compiler identities
            // and model kinds are real, but this Box parameter/class snapshot
            // is constructed to test the second-rule boundary, not admission.
            let row = table
                .entries
                .iter_mut()
                .find(|(s, _)| {
                    s.fn_did == callee && matches!(s.kind, SubjectKind::Param { hir_index: 0 })
                })
                .unwrap();
            row.1 = Decision::Box(plan);
            let id = SignatureClassId::of(callee);
            prepared.plan.class_finalization.classes.insert(
                id,
                bo::plan::SignatureClassPlan {
                    id,
                    required_arms: Default::default(),
                    site_keys: Vec::new(),
                    edit_keys: Vec::new(),
                    depends_on: Vec::new(),
                    disposition: bo::plan::SignatureClassDisposition::Ready,
                    sites: Vec::new(),
                },
            );
            let live = resolve(
                tcx,
                &ctx.slots,
                &ctx.model,
                &table,
                &prepared.plan.class_finalization,
                callee,
                0,
            )
            .unwrap();
            assert_eq!(live.emitted(), FormalForm::Box);
            assert!(matches!(
                live.require_lend(),
                Err(Hold::Lend(LendHold::OwningCallee))
            ));
            prepared
                .plan
                .class_finalization
                .classes
                .get_mut(&id)
                .unwrap()
                .disposition =
                bo::plan::SignatureClassDisposition::Held(vec!["deliberate-recovery".into()]);
            let recovered = resolve(
                tcx,
                &ctx.slots,
                &ctx.model,
                &table,
                &prepared.plan.class_finalization,
                callee,
                0,
            )
            .unwrap();
            assert_eq!(recovered.emitted(), FormalForm::MutableRaw);
            assert!(recovered.require_lend().is_ok());
        })
        .unwrap();
    }
}
