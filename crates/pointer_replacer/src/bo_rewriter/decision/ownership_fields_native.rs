//! R365 source-bound owning-local candidates. No allocation epoch is fabricated.
//! Candidates enter a final additive stage; terminal interfaces are checked again
//! against its completed class plan before the stage can survive.
use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Decision, DecisionTable, SubjectKind,
    a5_site_proof::{A5SeamProofIndex, A5SiteProofVerdict},
    box_facts::{BoxExprEdit, BoxPlan, BoxPlanFailure, BoxShape},
    construction::ConstructionFacts,
    ownership_fields_effects::NativeEffects,
    ownership_fields_formal::{self as formal, NativeFormal},
    ownership_fields_hook::Hold,
    ownership_fields_source::{self as source, SourceCallKey, SourceHold, SourcePlan},
    raw_boundary::{RawBoundarySiteFacts, RetentionSummaries, RetentionVerdict},
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::{
        ownership_fields::{
            free_sites::plan_frees,
            lend::{FormalForm, LendHold},
        },
        plan::ClassFinalization,
    },
    utils::rustc::RustProgram,
};

type Node = (LocalDefId, HirId);

#[derive(Clone, Debug)]
pub(crate) enum NativeHold {
    Source(SourceHold),
    Call(Hold),
    Missing(&'static str),
    Identity,
    Peer(&'static str),
    FinalInterface,
}

#[derive(Clone, Debug)]
struct Bundle {
    plan: BoxPlan,
    formals: Vec<NativeFormal>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Candidates {
    bundles: FxHashMap<Node, Bundle>,
    pub(crate) holds: FxHashMap<Node, NativeHold>,
}

pub(crate) struct Inputs<'a, 'tcx> {
    pub(crate) program: &'a RustProgram<'tcx>,
    pub(crate) slots: &'a CrateSlots,
    pub(crate) model: &'a FxHashMap<SlotRef, SlotKind>,
    pub(crate) constructions: &'a ConstructionFacts,
    pub(crate) sites: &'a RawBoundarySiteFacts,
    pub(crate) retention: &'a RetentionSummaries,
    pub(crate) a5: &'a A5SeamProofIndex,
}

impl Candidates {
    pub(crate) fn is_empty(&self) -> bool {
        self.bundles.is_empty()
    }

    pub(crate) fn derive(
        inputs: &Inputs<'_, '_>,
        table: &DecisionTable,
        classes: &ClassFinalization,
    ) -> Self {
        let effects = NativeEffects::derive(inputs.program);
        let mut result = Self::default();
        for (subject, decision) in &table.entries {
            if subject.kind != SubjectKind::Local {
                continue;
            }
            let degraded = match decision {
                Decision::Degraded(degraded) => degraded,
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_) => continue,
            };
            let super::DegradeReason::BoxFailure {
                failure: BoxPlanFailure::NativeEvidenceHeld { prior_key, .. },
            } = &degraded.reason
            else {
                continue;
            };
            if *prior_key != "box-param-caller-unknown" {
                continue;
            }
            let Some(slot) = inputs
                .slots
                .fn_local_slots
                .get(&subject.fn_did)
                .and_then(|u| u.slot_for_local_depth(subject.local, 0))
            else {
                continue;
            };
            if inputs.model.get(&SlotRef::Local(subject.fn_did, slot)) != Some(&SlotKind::Owning) {
                continue;
            }
            let node = (subject.fn_did, subject.hir_id);
            let bundle = source::derive(inputs.program, subject, inputs.constructions)
                .map_err(NativeHold::Source)
                .and_then(|source| {
                    derive_bundle(inputs, table, classes, &effects, subject, &source)
                });
            match bundle {
                Ok(bundle) => {
                    result.bundles.insert(node, bundle);
                }
                Err(hold) => {
                    result.holds.insert(node, hold);
                }
            }
        }
        result
    }

    /// This supplies only candidate rendering to the replayed suffix. The
    /// unchanged model owns the kind, and the final stage checks interfaces.
    pub(crate) fn plan(&self, node: Node) -> Option<&BoxPlan> {
        self.bundles.get(&node).map(|bundle| &bundle.plan)
    }

    pub(crate) fn invalid_owners(
        &self,
        inputs: &Inputs<'_, '_>,
        table: &DecisionTable,
        classes: &ClassFinalization,
    ) -> FxHashSet<LocalDefId> {
        let mut invalid = FxHashSet::default();
        for (&node, bundle) in &self.bundles {
            if !table.entries.iter().any(|(s, d)| {
                let selected = match d {
                    Decision::Box(plan) => plan == &bundle.plan,
                    Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::Opt { .. }
                    | Decision::Degraded(_) => false,
                };
                (s.fn_did, s.hir_id) == node && selected
            }) {
                continue;
            }
            for proof in &bundle.formals {
                let (callee, argument) = proof.identity();
                if formal::resolve(
                    inputs.program.tcx,
                    inputs.slots,
                    inputs.model,
                    table,
                    classes,
                    callee,
                    argument,
                )
                .map_or(true, |current| current != *proof)
                    || !stable_raw_formal(table, callee, argument)
                {
                    invalid.insert(node.0);
                }
            }
        }
        invalid
    }
}

/// This tranche does not convert formals. Its raw interface survives both a
/// ready class and restoration of that class, so later verification recovery
/// cannot change the argument expansion into a Box transfer or reference.
fn stable_raw_formal(table: &DecisionTable, callee: LocalDefId, argument: usize) -> bool {
    table.entries.iter().any(|(subject, decision)| {
        let degraded = match decision {
            Decision::Degraded(_) => true,
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => false,
        };
        subject.fn_did == callee
            && matches!(subject.kind, SubjectKind::Param{hir_index} if hir_index==argument)
            && degraded
    }) && table
        .input_interfaces
        .parameter_forms
        .get(&(callee, argument))
        == Some(&super::seam::Form::Raw)
}

fn derive_bundle(
    inputs: &Inputs<'_, '_>,
    table: &DecisionTable,
    classes: &ClassFinalization,
    effects: &NativeEffects<'_>,
    subject: &super::Subject,
    source: &SourcePlan,
) -> Result<Bundle, NativeHold> {
    if source.calls().is_empty() {
        return Err(NativeHold::Missing("native-lend-call-inventory"));
    }
    let tcx = inputs.program.tcx;
    let name = subject.param_name.as_ref().ok_or(NativeHold::Identity)?;
    let mut edits = vec![source.constructor().clone()];
    edits.extend_from_slice(source.scalar_edits());
    let mut receipts = vec![format!(
        "native-owning-source owner={} local={} generation=Missing source-root={:?}",
        subject.fn_did.local_def_index.as_u32(),
        subject.local.as_u32(),
        subject.hir_id
    )];
    receipts.push(format!("native-box-index-zero-nonempty count={} length-unchanged=closed-root-uses source-aliases={:?}",source.count(),source.mir_aliases()));
    let mut formals = Vec::new();
    let mut checked_calls = BTreeSet::<SourceCallKey>::new();
    for obligation in source.calls() {
        let callee = obligation
            .callee()
            .as_local()
            .ok_or(NativeHold::Missing("native-local-callee"))?;
        let argument = obligation.argument();
        let key = obligation.key();
        let matching: Vec<_> = inputs
            .sites
            .sites
            .iter()
            .filter(|site| {
                site.node == Some((subject.fn_did, subject.hir_id))
                    && site.callee_local == Some(callee)
                    && site.key.block == key.block
                    && site.key.statement_index as usize == key.statement
                    && site.key.argument_index == argument
                    && site.source_span.source_callsite()
                        == obligation.argument_span().source_callsite()
            })
            .collect();
        let [site] = matching.as_slice() else {
            return Err(NativeHold::Missing("native-lend-source-join"));
        };
        if site.callee_may_yield_pointer {
            return Err(NativeHold::Missing("native-pointer-yield"));
        }
        let emitted = formal::resolve(
            tcx,
            inputs.slots,
            inputs.model,
            table,
            classes,
            callee,
            argument,
        )
        .map_err(NativeHold::Call)?;
        if emitted.emitted() != FormalForm::MutableRaw
            || !stable_raw_formal(table, callee, argument)
        {
            return Err(NativeHold::FinalInterface);
        }
        formal::require_nonconsuming(effects, &emitted).map_err(NativeHold::Call)?;
        let Some(RetentionVerdict::NoRetain { certificate }) =
            inputs.retention.get(callee, argument)
        else {
            return Err(NativeHold::Call(Hold::Lend(LendHold::Retention)));
        };
        inputs
            .retention
            .verify_certificate(callee, argument, certificate)
            .map_err(|_| NativeHold::Call(Hold::Lend(LendHold::Retention)))?;
        let sig = tcx.fn_sig(callee.to_def_id()).skip_binder().skip_binder();
        // No hidden scalar effects, callee operand evaluation, indirect target,
        // aggregate argument or pointer-return path is admitted by this slice.
        if !sig.output().is_unit()
            || sig
                .inputs()
                .iter()
                .any(|ty| !matches!(ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)))
        {
            return Err(NativeHold::Missing("native-complete-pointer-call-shape"));
        }
        let peers: Vec<_> = inputs
            .sites
            .sites
            .iter()
            .filter(|peer| {
                peer.callee_local == Some(callee)
                    && peer.key.caller == site.key.caller
                    && peer.key.block == site.key.block
                    && peer.key.statement_index == site.key.statement_index
            })
            .collect();
        let indices: BTreeSet<_> = peers.iter().map(|p| p.key.argument_index).collect();
        if indices != (0..sig.inputs().len()).collect()
            || peers.len() != indices.len()
            || peers
                .iter()
                .any(|p| p.call_span != site.call_span || p.node.is_none())
        {
            return Err(NativeHold::Missing("native-peer-inventory"));
        }
        for peer in peers.iter().filter(|p| p.key.argument_index != argument) {
            let proof = inputs.a5.lookup(
                subject.fn_did.local_def_index.as_u32(),
                callee.local_def_index.as_u32(),
                argument,
                peer.key.argument_index,
                site.source_span,
                peer.source_span,
            );
            if proof.verdict != A5SiteProofVerdict::Clear {
                return Err(NativeHold::Peer(proof.reason));
            }
            for a in [argument, peer.key.argument_index] {
                let Some(proof_key) = proof.site_key(a) else {
                    return Err(NativeHold::Peer("missing-exact-site"));
                };
                if proof_key.caller != subject.fn_did
                    || proof_key.callee != callee.to_def_id()
                    || proof_key.location.block != key.block
                    || proof_key.location.statement_index != key.statement
                    || proof_key.slot_depth != 0
                {
                    return Err(NativeHold::Peer("mismatched-exact-site"));
                }
            }
            receipts.push(format!(
                "native-box-pair {:?} {}",
                key,
                proof.receipt(argument, peer.key.argument_index)
            ));
        }
        edits.push(BoxExprEdit {
            span: obligation.argument_span(),
            // Select the inherent slice operation directly; a source trait
            // method on Box must not capture the generated view operation.
            replacement: format!("<[_]>::as_mut_ptr(&mut *({name}))"),
            receipt: "native-box-lend-t1",
        });
        receipts.push(format!("native-box-lend {:?} arg={argument} formal_model={:?} emitted=raw T1=verified nonconsuming=verified interval=argument-list-through-return protector=call source-reference-inventory=complete",key,emitted.model_kind()));
        checked_calls.insert(key);
        formals.push(emitted);
    }
    // SourcePlan proves one fresh f32 root, no source aliases/escaping storage,
    // no reference-taking or rebinding, and all normal paths through its exact
    // C free. Each owner-using call above is separately proved nonretaining and
    // nonconsuming. That completes the all-roots account for extra unwinding
    // closes of this scalar root; it is not inferred from an empty loan set.
    for at in source.unwind_obligations() {
        receipts.push(format!("native-unwind-close-permit source-call={at:?} all-roots=fresh-local-closed-uses-and-verified-T1 payload=f32/nonrecursive; actual-waiver-sites=emitted-MIR-ledger"));
    }
    let required: BTreeSet<_> = source.frees().iter().map(|site| site.key()).collect();
    let frees = plan_frees(&required, source.frees()).map_err(NativeHold::Source)?;
    if frees.len() != source.frees().len() {
        return Err(NativeHold::Identity);
    }
    for (key, edit) in frees {
        let source_free = source
            .frees()
            .iter()
            .find(|site| site.key() == key)
            .ok_or(NativeHold::Identity)?;
        receipts.push(format!(
            "box-free-source-identity {key:?} callee={} span={:?} generation=Missing",
            tcx.def_path_str(source_free.callee()),
            source_free.span(),
        ));
        edits.push(edit);
    }
    let mut spans = BTreeSet::new();
    if edits
        .iter()
        .any(|e| !spans.insert((e.span.lo().0, e.span.hi().0)))
    {
        return Err(NativeHold::Identity);
    }
    receipts.push(format!("native-box-continuations calls={checked_calls:?} free_keys={required:?} scope-exit=exact-C-free"));
    Ok(Bundle {
        plan: BoxPlan {
            shape: BoxShape::Slice,
            optional: false,
            expr_edits: edits,
            delete_statements: Vec::new(),
            receipts,
            fabricated_extent: false,
            pointee_override: None,
            inferred_binding: subject.ty_span.is_none(),
            overwrite_spans: Vec::new(),
            retained_sink: true,
            implicit_scope_close: false,
        },
        formals,
    })
}
