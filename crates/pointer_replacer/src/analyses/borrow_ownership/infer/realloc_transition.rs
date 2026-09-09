//! Outcome-specific ownership at a source-derived realloc branch.

use rustc_middle::mir::{BasicBlock, Body, Local, Location, Place};

use super::{CallArgs, InferCtxt, LocalSig};
use crate::analyses::borrow_ownership::{
    AnalysisKind,
    export::{self, CallSite, PlaceKey, ReallocVersionSite},
    l2::MirLocationKey,
    realloc::{
        self, OldInput, OldResponsibility, ReallocOutcome, ReallocResult, ResultResponsibility,
    },
    realloc_ssa::{ReallocEdgeOperation, ReallocSsaPlan},
    solver::{OwnAssumeSite, with_own_assume_site},
    ssa::{
        constraint::{Database, infer::InferMode},
        consume::Consume,
        state::SSAIdx,
    },
};

#[derive(Clone)]
pub(super) struct ReallocInput {
    call: CallSite,
    old: Option<LocalSig>,
}

impl<'infercx, 'db, 'tcx, Analysis> InferCtxt<'infercx, 'db, 'tcx, Analysis>
where
    'tcx: 'infercx,
    Analysis: AnalysisKind<'infercx, 'db, 'tcx>,
{
    pub(crate) fn with_realloc_plans(mut self, plans: Vec<ReallocSsaPlan>) -> Self {
        self.realloc_plans = plans;
        self
    }

    pub(super) fn realloc_boundary(
        &mut self,
        destination: Option<Consume<LocalSig>>,
        args: &CallArgs,
    ) {
        let call = export::current_call_site().expect("realloc source call cursor");
        let plan = self
            .realloc_plans
            .iter()
            .find(|plan| {
                plan.site.key.block == call.location.block
                    && plan.site.key.statement == call.location.statement_index
            })
            .cloned()
            .expect("realloc requires a validated source outcome plan");
        if plan.coverage_hold.is_some() {
            assert!(
                plan.operations.is_empty(),
                "held realloc must not install outcome operations"
            );
            // The raw site carries no inferred allocation responsibility. Keep
            // source behavior, but do not invent conditional ownership claims.
            if let Some(destination) = destination {
                <Analysis as InferMode>::borrow(self, destination);
            }
            for (argument, _) in args.iter().flatten() {
                <Analysis as InferMode>::borrow(self, argument.clone());
            }
            return;
        }
        if let Some(continuation) = plan.site.result.continuation() {
            let cases = realloc::classify(&plan.site).expect("validated R219 cases");
            let old_argument = args.first().cloned().flatten();
            let old_before = old_argument
                .as_ref()
                .and_then(|(argument, _)| argument.r#use.clone().next());
            let old_after = old_argument
                .as_ref()
                .and_then(|(argument, _)| argument.def.clone().next());
            let result_claim = destination
                .as_ref()
                .and_then(|destination| destination.def.clone().next());
            if let Some(destination) = destination {
                export::with_realloc_endpoint(
                    ReallocOutcome::Success,
                    continuation.result_place.clone(),
                    || {
                        <Analysis as InferMode>::source(self, destination);
                    },
                );
            }
            if let Some((argument, is_ref)) = old_argument {
                assert!(!is_ref);
                if plan.site.old_input == OldInput::KnownNull {
                    <Analysis as InferMode>::assume(self, argument.r#use, false);
                    <Analysis as InferMode>::assume(self, argument.def, false);
                } else {
                    export::with_realloc_endpoint(
                        ReallocOutcome::Success,
                        continuation
                            .old_place
                            .clone()
                            .expect("old operand identity"),
                        || {
                            // Both source alternatives close the old claim: a
                            // success retirement, or R219's failure loss law. This
                            // is never a declaration that failure frees the block.
                            <Analysis as InferMode>::sink(self, argument);
                        },
                    );
                }
            }
            export::record(|capture| {
                capture.realloc_cases.extend(cases.into_iter().map(|case| {
                    export::ReallocCaseReceipt {
                        event: plan.site.key.clone(),
                        result_claim: (case.outcome == ReallocOutcome::Success)
                            .then_some(result_claim)
                            .flatten(),
                        case,
                        old_before,
                        old_after,
                    }
                }));
            });
            return;
        }
        let ReallocResult::DirectBranch(branch) = &plan.site.result else { unreachable!() };
        let destination = destination.expect("validated realloc result ownership definition");
        // The unqualified call→test window is only a placeholder. No access in
        // that window may depend on old/result responsibility. Real versions
        // are installed on BOTH source outcome edges and exported separately.
        <Analysis as InferMode>::assume(self, destination.r#use, false);
        <Analysis as InferMode>::assume(self, destination.def.clone(), false);
        self.realloc_ghosts.extend(destination.def);
        let old = if plan.site.old_input == OldInput::KnownNull {
            if let Some((argument, _)) = args[0].clone() {
                <Analysis as InferMode>::assume(self, argument.r#use, false);
                // This old value is unconditionally None, not an unresolved
                // outcome value. Later assignments must remain real exports.
                <Analysis as InferMode>::assume(self, argument.def, false);
            }
            None
        } else {
            let (argument, is_ref) = args[0].clone().expect("validated old ownership operand");
            assert!(!is_ref);
            let before = argument.r#use.clone();
            self.realloc_ghosts.extend(argument.def.clone());
            export::with_realloc_endpoint(
                ReallocOutcome::Success,
                PlaceKey::from_place(Place::from(branch.old.expect("source old operand"))),
                || <Analysis as InferMode>::sink(self, argument),
            );
            Some(before)
        };
        assert!(
            self.realloc_inputs
                .insert(call.location, ReallocInput { call, old })
                .is_none(),
            "one ownership transition per source realloc site"
        );
    }

    pub(super) fn apply_realloc_edge(
        &mut self,
        plan: &ReallocSsaPlan,
        outcome: ReallocOutcome,
        edge: BasicBlock,
        operation: &ReallocEdgeOperation,
        versions: &[(Local, Consume<SSAIdx>)],
        body: &Body<'tcx>,
    ) {
        let source = MirLocationKey::new(plan.site.key.block, plan.site.key.statement);
        let input = self
            .realloc_inputs
            .get(&source)
            .cloned()
            .expect("realloc boundary dominates its outcome edges");
        let case = realloc::classify(&plan.site)
            .expect("validated lifecycle cases")
            .into_iter()
            .find(|case| case.outcome == outcome)
            .expect("every feasible source outcome is represented");
        let resolved: Vec<_> = versions
            .iter()
            .map(|(local, consume)| {
                (
                    *local,
                    Consume {
                        r#use: self.fn_body_sig[*local][consume.r#use].clone(),
                        def: self.fn_body_sig[*local][consume.def].clone(),
                    },
                )
            })
            .collect();
        let value = |local: Local| {
            resolved
                .iter()
                .find(|(owner, _)| *owner == local)
                .expect("edge local definition")
                .1
                .clone()
        };
        with_own_assume_site(OwnAssumeSite::LibcRule, || match operation {
            ReallocEdgeOperation::Old { local } => {
                let destination = value(*local);
                match case.old {
                    OldResponsibility::RetireIfPresent => {
                        <Analysis as InferMode>::assume(self, destination.def, false)
                    }
                    OldResponsibility::PreserveIfPresent => {
                        for (before, after) in input
                            .old
                            .clone()
                            .expect("old generation input")
                            .zip(destination.def)
                        {
                            self.database.push_equal::<crate::analyses::borrow_ownership::ssa::constraint::Debug>((), before, after);
                        }
                    }
                    OldResponsibility::Absent => {
                        unreachable!("null old input has no old edge definition")
                    }
                    OldResponsibility::LoseClaimIfPresent => {
                        unreachable!("R219 unobserved outcomes do not use a direct branch edge")
                    }
                }
            }
            ReallocEdgeOperation::Result { local } => {
                let destination = value(*local);
                match case.result {
                    ResultResponsibility::None => {
                        <Analysis as InferMode>::borrow(self, destination)
                    }
                    ResultResponsibility::FreshGeneration => {
                        export::with_terminator_site(
                            input.call.fn_did,
                            input.call.function_path.clone(),
                            Location {
                                block: BasicBlock::from_u32(source.block),
                                statement_index: source.statement_index,
                            },
                            || {
                                export::with_callee("realloc", || {
                                    export::with_realloc_endpoint(
                                        outcome,
                                        PlaceKey::from_place(Place::from(*local)),
                                        || <Analysis as InferMode>::source(self, destination),
                                    )
                                })
                            },
                        );
                    }
                }
            }
            ReallocEdgeOperation::Transfer {
                source,
                destination,
                location,
                by_move,
            } => {
                if *by_move {
                    <Analysis as InferMode>::transfer::<true>(
                        self,
                        body.local_decls[*destination].ty,
                        value(*destination),
                        value(*source),
                        Some(*location),
                    );
                } else {
                    <Analysis as InferMode>::transfer::<false>(
                        self,
                        body.local_decls[*destination].ty,
                        value(*destination),
                        value(*source),
                        Some(*location),
                    );
                }
            }
        });
        let location = match operation {
            ReallocEdgeOperation::Transfer { location, .. } => {
                MirLocationKey::new(location.block.as_u32(), location.statement_index)
            }
            _ => source,
        };
        for (local, consume) in resolved {
            let before = consume.r#use.start;
            self.realloc_versions.push(ReallocVersionSite {
                fn_did: input.call.fn_did,
                event: plan.site.key.clone(),
                outcome,
                edge: edge.as_u32(),
                location,
                local,
                use_var: (!self.realloc_ghosts.contains(&before)).then_some(before),
                def_var: consume.def.start,
            });
        }
    }
}
