//! R351 integration intake. A candidate is not a delivered Box.
//! Native producers must install a complete bundle before final admission.
//! The default catalog deliberately carries typed Missing; it never fabricates
//! T1/nonconsuming/A5/lifetime, construction, free, or extra-close evidence.
use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_span::Span;

use super::{
    super::ownership_fields::{
        self as owned, EvidenceKey, SiteId,
        export::{Evidence, EvidenceOwner, Missing, MissingReason},
        free_sites, lend, lifecycle, model_adapter,
    },
    Ctx, Subject,
    box_facts::{BoxPlan, BoxPlanFailure},
};
use crate::analyses::borrow_ownership::{SlotKind, solver::SlotRef};

type Node = (LocalDefId, HirId);

#[cfg(test)]
#[path = "ownership_fields_hook_tests.rs"]
mod tests;

/// Exact native occurrence projection supplied against the source snapshot.
/// `BoxPlan` expr_edits are still applied by the existing AST/class pipeline.
#[derive(Clone, Debug)]
pub(crate) struct LendBatch {
    pub(crate) inventory: lend::CallInventory,
    pub(crate) sites: Vec<lend::LendSite>,
    pub(crate) argument_spans: BTreeMap<u32, Span>,
}
#[derive(Clone, Debug)]
pub(crate) struct FreeBatch {
    pub(crate) required: BTreeSet<EvidenceKey>,
    pub(crate) sites: Vec<free_sites::FreeSite>,
    pub(crate) spans: BTreeMap<EvidenceKey, Span>,
}
#[derive(Clone, Debug)]
pub(crate) struct CloseSite {
    pub(crate) key: EvidenceKey,
    pub(crate) kind: lifecycle::CloseKind,
    pub(crate) payload: owned::OwnerId,
    pub(crate) graph: BTreeMap<owned::OwnerId, lifecycle::DropShape>,
    pub(crate) graph_revision: [u8; 32],
    pub(crate) depth: Option<lifecycle::DepthWitness>,
    pub(crate) proofs: lifecycle::CloseProofs,
}
#[derive(Clone, Debug)]
pub(crate) struct Bundle {
    pub(crate) slot: SlotRef,
    pub(crate) model_subject: model_adapter::ModelSlot,
    pub(crate) model_site: SiteId,
    pub(crate) expected_frame: model_adapter::ModelFrame,
    pub(crate) model_inputs: model_adapter::AcceptedInputs,
    pub(crate) consumption_pins: Evidence<model_adapter::ConsumptionPins>,
    /// Native constructor/parameter ingress plan already validated for its
    /// exact layout, all fields, type/depth, nullability and allocator. This
    /// must not be copied from a failed legacy Box plan after dropping gates.
    pub(crate) construction: Evidence<BoxPlan>,
    pub(crate) construction_proof: Evidence<EvidenceKey>,
    /// Includes EVERY boundary occurrence, raw returns and consuming calls as
    /// well as lends. Those other roles need their own contracts or Missing.
    pub(crate) boundary_inventory: Evidence<EvidenceKey>,
    pub(crate) lends: Evidence<Vec<LendBatch>>,
    pub(crate) frees: Evidence<FreeBatch>,
    /// Exact complete extra-close inventory; empty must be proved empty.
    pub(crate) closes: Evidence<Vec<CloseSite>>,
    pub(crate) close_inventory: Evidence<EvidenceKey>,
    /// Native source/occurrence projection and whole-class interface closure.
    /// Pending candidate facts cannot supply either final permit.
    pub(crate) source_projection: Evidence<EvidenceKey>,
    pub(crate) final_interface: Evidence<EvidenceKey>,
}
#[derive(Clone, Debug, Default)]
pub(crate) struct Inputs {
    rows: FxHashMap<Node, Evidence<Bundle>>,
    terminal_formals: BTreeMap<(u32, usize), super::ownership_fields_formal::NativeFormal>,
    native_candidates: super::ownership_fields_native::Candidates,
}
impl Inputs {
    /// **wave-5d2 hook (R436-3(a))** — the candidate plan, read-only, exactly
    /// as the ownership stage reads it (`plan`); ownership-fields 031 claim 5.
    pub(crate) fn candidate_plan(&self, node: Node) -> Option<&BoxPlan> {
        self.native_candidates.plan(node)
    }

    pub(crate) fn selected_slice_elements(
        &self,
        node: Node,
        selected: &super::box_facts::BoxPlan,
    ) -> Option<u64> {
        self.native_candidates
            .selected_slice_elements(node, selected)
    }

    /// Called before hypothetical decisions. This records scope only; no
    /// syntax/custody/Box decision is manufactured to bootstrap raw-boundary.
    pub(crate) fn discover(
        ctx_model: &FxHashMap<SlotRef, SlotKind>,
        slots: &crate::analyses::borrow_ownership::crate_slots::CrateSlots,
        subjects: &[Subject],
    ) -> Self {
        let mut rows = FxHashMap::default();
        for subject in subjects {
            let slot = slots
                .fn_local_slots
                .get(&subject.fn_did)
                .and_then(|u| u.slot_for_local_depth(subject.local, 0))
                .map(|slot| SlotRef::Local(subject.fn_did, slot));
            if slot.is_some_and(|slot| ctx_model.get(&slot) == Some(&SlotKind::Owning)) {
                rows.insert(
                    (subject.fn_did, subject.hir_id),
                    Err(missing("native-subject-bundle")),
                );
            }
        }
        Self {
            rows,
            terminal_formals: BTreeMap::new(),
            native_candidates: Default::default(),
        }
    }

    pub(crate) fn with_native_candidates(
        mut self,
        candidates: super::ownership_fields_native::Candidates,
    ) -> Self {
        self.native_candidates = candidates;
        self
    }

    /// The native producer must derive authenticated facts independently of
    /// the hypothetical Box rendering. No positive insertion is enabled until
    /// all native producer and final-interface obligations are discharged.
    pub(crate) fn install(&mut self, node: Node, bundle: Evidence<Bundle>) -> Result<(), Hold> {
        let Some(row) = self.rows.get_mut(&node) else {
            return Err(Hold::Identity);
        };
        *row = bundle;
        Ok(())
    }
}
#[derive(Clone, Debug)]
pub(crate) enum Hold {
    Missing(Missing),
    Identity,
    Construction,
    Projection,
    RecursiveSuppression,
    Lend(lend::LendHold),
    Free(free_sites::FreeHold),
    Close(lifecycle::CloseHold),
    NativeEffects(super::ownership_fields_effects::EffectsHold),
}
fn missing(field: &'static str) -> Missing {
    Missing {
        owner: EvidenceOwner::NativeIdentity,
        reason: MissingReason::Field(field),
    }
}
fn need<T>(value: &Evidence<T>) -> Result<&T, Hold> {
    value.as_ref().map_err(|m| Hold::Missing(m.clone()))
}
fn exact(proof: &Evidence<EvidenceKey>, key: EvidenceKey) -> Result<(), Hold> {
    if need(proof)? != &key {
        return Err(Hold::Identity);
    }
    Ok(())
}
fn expression(code: &str) -> &str {
    code.strip_suffix(';').unwrap_or(code)
}
fn expect_edit(plan: &BoxPlan, span: Span, replacement: &str) -> Result<(), Hold> {
    let edits = plan
        .expr_edits
        .iter()
        .filter(|e| e.span == span)
        .collect::<Vec<_>>();
    let [edit] = edits.as_slice() else {
        return Err(Hold::Projection);
    };
    if edit.replacement != replacement {
        return Err(Hold::Projection);
    }
    Ok(())
}

/// Validates prepared final data; it does not look up native facts from names,
/// syntax spans, kind bits or debug strings. Model input is checked against
/// the exact accepted native SlotRef once again at the decision hook.
fn validate(bundle: &Bundle) -> Result<BoxPlan, Hold> {
    let prepared = model_adapter::prepare(
        &bundle.expected_frame,
        &bundle.model_inputs,
        &bundle.consumption_pins,
    )
    .map_err(Hold::Missing)?;
    let grant = prepared
        .owning_grant(bundle.model_subject, bundle.model_site)
        .map_err(Hold::Missing)?;
    let key = grant.grant.key;
    for permit in [
        &bundle.construction_proof,
        &bundle.boundary_inventory,
        &bundle.close_inventory,
        &bundle.source_projection,
        &bundle.final_interface,
    ] {
        exact(permit, key)?;
    }
    let mut plan = need(&bundle.construction)?.clone();
    // This positive extension is limited to non-recursive ordinary Box
    // construction/ingress with all representation consequences supplied.
    // It may not inherit fabricated waiver strings from a candidate plan.
    if plan
        .receipts
        .iter()
        .any(|r| r.contains("waiver-drop") || r.contains("waiver-leak"))
    {
        return Err(Hold::Construction);
    }
    let same_frame =
        |other: EvidenceKey| other.model == key.model && other.configuration == key.configuration;
    let mut claimed_spans = Vec::new();
    let mut claimed_calls = BTreeSet::new();
    for call in need(&bundle.lends)? {
        if !claimed_calls.insert(call.inventory.call)
            || call
                .sites
                .iter()
                .any(|site| !same_frame(site.edge.actual) || !same_frame(site.edge.formal))
        {
            return Err(Hold::Identity);
        }
        let lend = lend::plan_call(&call.inventory, &call.sites).map_err(Hold::Lend)?;
        if lend.arguments.keys().copied().collect::<BTreeSet<_>>()
            != call.argument_spans.keys().copied().collect()
        {
            return Err(Hold::Projection);
        }
        for (argument, code) in lend.arguments {
            let span = call.argument_spans[&argument];
            if claimed_spans.contains(&span) {
                return Err(Hold::Projection);
            }
            claimed_spans.push(span);
            expect_edit(&plan, span, &code)?;
        }
        for receipt in lend.receipts {
            plan.receipts.push(format!("box-lend-t1 {:?}", receipt));
        }
    }
    let free = need(&bundle.frees)?;
    if free.required.iter().any(|sink| !same_frame(*sink))
        || free.sites.iter().any(|site| {
            !same_frame(site.sink)
                || !same_frame(site.owner)
                || site.owner.generation != key.generation
        })
    {
        return Err(Hold::Identity);
    }
    let drops = free_sites::plan_frees(&free.required, &free.sites).map_err(Hold::Free)?;
    if drops.keys().copied().collect::<BTreeSet<_>>() != free.spans.keys().copied().collect() {
        return Err(Hold::Projection);
    }
    for (sink, emitted) in drops {
        // Key join, never endpoint traversal zipped with source-order calls.
        let span = free.spans[&sink];
        if claimed_spans.contains(&span) {
            return Err(Hold::Projection);
        }
        claimed_spans.push(span);
        expect_edit(&plan, span, expression(&emitted.code))?;
        plan.receipts.push(format!("box-free-identity {:?}", sink));
    }
    let mut close_events = BTreeSet::new();
    for close in need(&bundle.closes)? {
        if !close_events.insert((close.key, close.kind.receipt())) {
            return Err(Hold::Projection);
        }
        if close.key.model != key.model || close.key.configuration != key.configuration {
            return Err(Hold::Identity);
        }
        let disposition = lifecycle::implicit_close(
            close.key,
            close.kind,
            close.payload,
            &close.graph,
            close.graph_revision,
            close.depth.as_ref(),
            &close.proofs,
        )
        .map_err(Hold::Close)?;
        match disposition {
            lifecycle::ClosePlan::Drop { key, receipt } => {
                plan.receipts.push(format!("{receipt} site={:?}", key.site));
            }
            lifecycle::ClosePlan::LeakRecursive { .. } => return Err(Hold::RecursiveSuppression),
        }
    }
    plan.receipts
        .push(format!("model-owning-grant {:?}", grant.receipt));
    Ok(plan)
}

/// R365 checks an owning-aware terminal formal while recording its model kind.
/// Effects neither manufacture the terminal interface nor override model bits.
pub(crate) fn native_lend_formal(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    slots: &crate::analyses::borrow_ownership::crate_slots::CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    callee: LocalDefId,
    argument: usize,
    emitted: &super::ownership_fields_formal::NativeFormal,
) -> Result<owned::emission::Kind, Hold> {
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
    let local = rustc_middle::mir::Local::from_usize(argument + 1);
    let formal = slots
        .fn_local_slots
        .get(&callee)
        .and_then(|slots| slots.slot_for_local_depth(local, 0))
        .map(|slot| SlotRef::Local(callee, slot))
        .ok_or_else(|| Hold::Missing(missing("native-formal-slot")))?;
    let kind = match model.get(&formal) {
        Some(SlotKind::Ref) => owned::emission::Kind::Ref,
        Some(SlotKind::Raw) => owned::emission::Kind::Raw,
        Some(SlotKind::Owning) => owned::emission::Kind::Owning,
        None => return Err(Hold::Missing(missing("native-formal-kind"))),
    };
    if !emitted.matches(callee, argument) || emitted.model_kind() != kind {
        return Err(Hold::Identity);
    }
    emitted.require_lend()?;
    Ok(kind)
}

pub(crate) fn plan(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    slot: SlotRef,
    prior: Result<BoxPlan, BoxPlanFailure>,
) -> Result<BoxPlan, BoxPlanFailure> {
    // R216-1: an additive intake must never replace a prior working plan.
    let prior_failure = match prior {
        Ok(plan) => return Ok(plan),
        Err(failure) => failure,
    };
    if ctx.family_policy.enabled_for(
        (subject.fn_did, subject.hir_id),
        super::super::additive::FamilyStage::Ownership,
    ) && let Some(plan) = ctx
        .ownership_fields
        .native_candidates
        .plan((subject.fn_did, subject.hir_id))
    {
        // The final ownership stage rebuilds boundary/class machinery from
        // these proof-backed candidates and rechecks its terminal formals.
        // Hypothetical rendering is not a delivered-interface receipt.
        return Ok(plan.clone());
    }
    if !matches!(
        prior_failure,
        BoxPlanFailure::BoundaryHeld
            | BoxPlanFailure::ParameterHeld
            | BoxPlanFailure::InitializerUnsupported
    ) || ctx.raw_boundary.is_none()
    {
        return Err(prior_failure);
    }
    let result = (|| {
        if ctx.model.get(&slot) != Some(&SlotKind::Owning) {
            return Err(Hold::Identity);
        }
        let row = ctx
            .ownership_fields
            .rows
            .get(&(subject.fn_did, subject.hir_id))
            .ok_or_else(|| Hold::Missing(missing("native-subject-catalog")))?;
        let bundle = need(row)?;
        if bundle.slot != slot
            || bundle.model_subject.owner.0 != subject.fn_did.local_def_index.as_u32()
            || bundle.model_subject.local != subject.local.as_u32()
            || bundle.model_subject.depth != 1
        {
            return Err(Hold::Identity);
        }
        let plan = validate(bundle)?;
        // A supplied key is not native no-consume evidence. Re-derive the
        // whole local dependency closure and bind each admitted target/arg.
        // The empty catalog path never runs this work; no cache/solver call.
        let program = crate::utils::rustc::RustProgram {
            tcx: ctx.tcx,
            functions: ctx.slots.fn_local_slots.keys().copied().collect(),
            structs: Vec::new(),
        };
        let effects = super::ownership_fields_effects::NativeEffects::derive(&program);
        for call in need(&bundle.lends)? {
            for site in &call.sites {
                let callee = program
                    .functions
                    .iter()
                    .copied()
                    .find(|owner| owner.local_def_index.as_u32() == site.edge.target.0)
                    .ok_or_else(|| Hold::Missing(missing("native-lend-callee")))?;
                let argument = site.edge.argument as usize;
                let emitted = ctx
                    .ownership_fields
                    .terminal_formals
                    .get(&(callee.local_def_index.as_u32(), argument))
                    .ok_or_else(|| Hold::Missing(missing("terminal-formal-frame")))?;
                let kind =
                    native_lend_formal(ctx.tcx, ctx.slots, ctx.model, callee, argument, emitted)?;
                if need(&site.formal)?.kind != kind || need(&site.formal)?.form != emitted.emitted()
                {
                    return Err(Hold::Identity);
                }
                super::ownership_fields_formal::require_nonconsuming(&effects, emitted)?;
            }
        }
        Ok(plan)
    })();
    result.map_err(|hold| BoxPlanFailure::NativeEvidenceHeld {
        prior_key: prior_failure.key(),
        detail: format!("prior={}; {hold:?}", prior_failure.key()),
    })
}
