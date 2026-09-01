//! E2-FN lifetime planning.
//!
//! This module is the sole rewriter-side consumer of the intact NB5-O
//! [`OriginSummaries`] carrier for lifetime semantics.  It starts with the
//! carrier-shape witness; eligibility, SCC planning, and emission receipts are
//! filled by the subsequent RED-first steps.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    ExprKind, QPath,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{Visitor, walk_expr},
};
use rustc_middle::{
    mir::{RETURN_PLACE, TerminatorKind},
    ty::TyKind,
};
use sha2::{Digest, Sha256};

use super::{
    Decision, DecisionTable, DegradeReason, Subject,
    co_conversion::{Escape, EscapeKind, NodeKey},
    construction::{CallResultTarget, Construction, ConstructionFacts},
};
use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        a5_overlap::WholeProgramAttestation,
        a5_producer::resolve_closed_world_call_world,
        crate_slots::CrateSlots,
        origin_summary::{
            OriginSlot, OriginSummaries, OriginSummary, SignatureRoot, SignatureSlot,
        },
        solver::SlotRef,
    },
    utils::rustc::RustProgram,
};

/// The minimal E2-X1 observation used to prove that the carrier reaches this
/// module without an A5-specific projection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CarrierReceipt {
    pub(crate) summary_count: usize,
    pub(crate) native_flows: bool,
}

pub(crate) fn carrier_receipt(origins: Option<&OriginSummaries>) -> CarrierReceipt {
    CarrierReceipt {
        summary_count: origins.map_or(0, |origins| origins.len()),
        native_flows: origins.is_some_and(|origins| origins.try_native_flows().is_some()),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum FnSignatureRoot {
    Arg(u32),
    Return,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct FnSignatureSlot {
    pub(crate) root: FnSignatureRoot,
    pub(crate) deref_depth: u8,
    pub(crate) depth: u8,
}

impl FnSignatureSlot {
    pub(crate) const RETURN: Self = Self {
        root: FnSignatureRoot::Return,
        deref_depth: 0,
        depth: 0,
    };

    pub(crate) fn arg(index: usize, deref_depth: u8, depth: u8) -> Self {
        Self {
            root: FnSignatureRoot::Arg(u32::try_from(index).expect("argument index fits u32")),
            deref_depth,
            depth,
        }
    }

    fn from_summary(slot: SignatureSlot) -> Result<Self, LifetimeFailure> {
        if slot.place.field.is_some() {
            return Err(LifetimeFailure::FieldHeld);
        }
        Ok(Self {
            root: match slot.place.root {
                SignatureRoot::Arg(local) => FnSignatureRoot::Arg(local.as_u32()),
                SignatureRoot::Return => FnSignatureRoot::Return,
            },
            deref_depth: slot.place.deref_depth,
            depth: slot.depth,
        })
    }

    fn needs_modeled_source(self) -> bool {
        matches!(self.root, FnSignatureRoot::Return)
            || matches!(self.root, FnSignatureRoot::Arg(_))
                && self.deref_depth.saturating_add(self.depth) > 0
    }

    fn receipt_key(self) -> String {
        match self.root {
            FnSignatureRoot::Arg(index) => {
                format!("arg{index}/deref{}/depth{}", self.deref_depth, self.depth)
            }
            FnSignatureRoot::Return => {
                format!("return/deref{}/depth{}", self.deref_depth, self.depth)
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LifetimeFailure {
    OriginUnknown,
    OriginAbsent,
    OriginConflict,
    FieldHeld,
    ExternalContractAbsent,
    FnPtrWebHeld,
    AstUnplaceable,
    SeamIncompatible,
}

/// The only token that may discharge one `escapes-via-return` row. Its
/// constructor is private to this module so co-conversion cannot manufacture a
/// bypass from a boolean or an arbitrary subject set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnLifetimePermit {
    subject: NodeKey,
    function: LocalDefId,
    sources: Vec<FnSignatureSlot>,
    target: FnSignatureSlot,
    origin_sources: Vec<OriginSlot>,
    origin_target: OriginSlot,
}

/// Evidence that an unannotated local receives a borrowed form from one
/// lifetime-bearing direct local callee.  Construction is private for the same
/// reason as [`ReturnLifetimePermit`]: the no-declaration-splice exception is
/// unavailable without the complete typed proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct InferredLifetimePermit {
    subject: NodeKey,
    callee: LocalDefId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OutputStorageLifetimePermit {
    function: LocalDefId,
    sources: Vec<FnSignatureSlot>,
    target: FnSignatureSlot,
    origin_sources: Vec<OriginSlot>,
    origin_target: OriginSlot,
}

impl OutputStorageLifetimePermit {
    fn new(
        function: LocalDefId,
        sources: Vec<(FnSignatureSlot, OriginSlot)>,
        target: (FnSignatureSlot, OriginSlot),
    ) -> Self {
        let (sources, origin_sources) = sources.into_iter().unzip();
        let (target, origin_target) = target;
        Self {
            function,
            sources,
            target,
            origin_sources,
            origin_target,
        }
    }
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OutputStorageReceipt {
    pub(crate) source: String,
    pub(crate) target: String,
}

impl InferredLifetimePermit {
    fn new(subject: NodeKey, callee: LocalDefId) -> Self {
        Self { subject, callee }
    }

    pub(crate) fn callee(self) -> LocalDefId {
        self.callee
    }
}

impl ReturnLifetimePermit {
    fn new(
        subject: NodeKey,
        function: LocalDefId,
        sources: Vec<(FnSignatureSlot, OriginSlot)>,
        target: (FnSignatureSlot, OriginSlot),
    ) -> Self {
        let (sources, origin_sources) = sources.into_iter().unzip();
        let (target, origin_target) = target;
        Self {
            subject,
            function,
            sources,
            target,
            origin_sources,
            origin_target,
        }
    }

    fn for_test(subject: NodeKey, source: FnSignatureSlot, target: FnSignatureSlot) -> Self {
        Self::new(
            subject,
            subject.0,
            vec![(source, OriginSlot::from_usize(0))],
            (target, OriginSlot::from_usize(1)),
        )
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LifetimeEligibility {
    return_permits: FxHashMap<NodeKey, ReturnLifetimePermit>,
    inferred_permits: FxHashMap<NodeKey, InferredLifetimePermit>,
    output_storage_permits: FxHashMap<(LocalDefId, FnSignatureSlot), OutputStorageLifetimePermit>,
    output_storage_escapes: FxHashSet<(NodeKey, NodeKey)>,
    failures: FxHashMap<NodeKey, LifetimeFailure>,
}

impl LifetimeEligibility {
    pub(crate) fn return_permit(&self, subject: NodeKey) -> Option<&ReturnLifetimePermit> {
        self.return_permits.get(&subject)
    }

    pub(crate) fn return_permit_count(&self) -> usize {
        self.return_permits.len()
    }

    pub(crate) fn inferred_permit(&self, subject: NodeKey) -> Option<InferredLifetimePermit> {
        self.inferred_permits.get(&subject).copied()
    }

    #[cfg(test)]
    pub(crate) fn inferred_permit_count(&self) -> usize {
        self.inferred_permits.len()
    }

    pub(crate) fn failure(&self, subject: NodeKey) -> Option<LifetimeFailure> {
        self.failures.get(&subject).copied()
    }

    pub(crate) fn permits_output_storage(&self, source: NodeKey, target: NodeKey) -> bool {
        self.output_storage_escapes.contains(&(source, target))
    }

    pub(crate) fn is_output_source(&self, source: NodeKey) -> bool {
        self.output_storage_escapes
            .iter()
            .any(|(candidate, _)| *candidate == source)
    }

    pub(crate) fn failures(&self) -> impl Iterator<Item = (NodeKey, LifetimeFailure)> + '_ {
        self.failures.iter().map(|(&key, &failure)| (key, failure))
    }

    #[cfg(test)]
    pub(crate) fn output_storage_receipts(&self) -> Vec<OutputStorageReceipt> {
        let mut permits = self.output_storage_permits.values().collect::<Vec<_>>();
        permits.sort_by_key(|permit| {
            (
                permit.function.local_def_index.as_u32(),
                permit.target,
                permit.sources.clone(),
            )
        });
        permits
            .into_iter()
            .flat_map(|permit| {
                permit.sources.iter().map(|source| OutputStorageReceipt {
                    source: source.receipt_key(),
                    target: permit.target.receipt_key(),
                })
            })
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn with_return_permit_for_test(subject: NodeKey) -> Self {
        let permit = ReturnLifetimePermit::for_test(
            subject,
            FnSignatureSlot::arg(1, 0, 0),
            FnSignatureSlot::RETURN,
        );
        Self {
            return_permits: [(subject, permit)].into_iter().collect(),
            inferred_permits: FxHashMap::default(),
            output_storage_permits: FxHashMap::default(),
            output_storage_escapes: FxHashSet::default(),
            failures: FxHashMap::default(),
        }
    }
}

fn model_is_ref(
    model: &FxHashMap<SlotRef, SlotKind>,
    slots: &CrateSlots,
    function: LocalDefId,
    signature: SignatureSlot,
) -> bool {
    let local = match signature.place.root {
        SignatureRoot::Arg(local) => local,
        SignatureRoot::Return => RETURN_PLACE,
    };
    let Some(depth) = signature.place.deref_depth.checked_add(signature.depth) else {
        return false;
    };
    slots
        .fn_local_slots
        .get(&function)
        .and_then(|universe| universe.slot_for_local_depth(local, depth))
        .and_then(|slot| model.get(&SlotRef::Local(function, slot)))
        == Some(&SlotKind::Ref)
}

pub(crate) fn derive_return_eligibility(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    origins: Option<&OriginSummaries>,
    hypothetical: &DecisionTable,
    subjects: &[Subject],
    constructions: &ConstructionFacts,
    escapes: &[Escape],
    attestation: Option<WholeProgramAttestation>,
) -> LifetimeEligibility {
    let mut result = LifetimeEligibility::default();
    let decisions = hypothetical
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect::<FxHashMap<_, _>>();
    let web = derive_fn_ptr_web(program, attestation);

    let mut return_subjects = escapes
        .iter()
        .filter(|escape| escape.kind == EscapeKind::Return)
        .map(|escape| escape.subject)
        .collect::<Vec<_>>();
    return_subjects
        .sort_unstable_by_key(|(did, hir)| (did.local_def_index.as_u32(), hir.local_id.as_u32()));
    return_subjects.dedup();

    for subject in return_subjects {
        if !matches!(decisions.get(&subject), Some(Decision::Ref { .. })) {
            continue;
        }
        let function = subject.0;
        let Ok(web) = &web else {
            result
                .failures
                .insert(subject, LifetimeFailure::FnPtrWebHeld);
            continue;
        };
        if web.contains(function) {
            result
                .failures
                .insert(subject, LifetimeFailure::FnPtrWebHeld);
            continue;
        }
        let Some(summary) = origins.and_then(|origins| origins.get(&function)) else {
            result
                .failures
                .insert(subject, LifetimeFailure::OriginAbsent);
            continue;
        };

        let targets = summary
            .slots
            .iter_enumerated()
            .filter(|(_, slot)| {
                slot.place.root == SignatureRoot::Return
                    && slot.place.field.is_none()
                    && slot.place.deref_depth == 0
                    && slot.depth == 0
            })
            .collect::<Vec<_>>();
        let [(target_origin, target_signature)] = targets.as_slice() else {
            result
                .failures
                .insert(subject, LifetimeFailure::OriginConflict);
            continue;
        };
        if !model_is_ref(model, slots, function, **target_signature) {
            result
                .failures
                .insert(subject, LifetimeFailure::OriginConflict);
            continue;
        }

        let sources = summary
            .slots
            .iter_enumerated()
            .filter(|(origin, slot)| {
                matches!(slot.place.root, SignatureRoot::Arg(_))
                    && slot.place.field.is_none()
                    && slot.place.deref_depth == 0
                    && summary.subset.contains(*origin, *target_origin)
                    && model_is_ref(model, slots, function, **slot)
            })
            .collect::<Vec<_>>();
        let mut required = sources
            .iter()
            .map(|(origin, _)| *origin)
            .collect::<Vec<_>>();
        required.push(*target_origin);
        if let Err(failure) = plan_function(summary, &required, &BTreeSet::new()) {
            result.failures.insert(subject, failure);
            continue;
        }

        let sources = sources
            .into_iter()
            .map(|(origin, slot)| FnSignatureSlot::from_summary(*slot).map(|slot| (slot, origin)))
            .collect::<Result<Vec<_>, _>>();
        let target =
            FnSignatureSlot::from_summary(**target_signature).map(|slot| (slot, *target_origin));
        match (sources, target) {
            (Ok(sources), Ok(target)) => {
                result.return_permits.insert(
                    subject,
                    ReturnLifetimePermit::new(subject, function, sources, target),
                );
            }
            (Err(failure), _) | (_, Err(failure)) => {
                result.failures.insert(subject, failure);
            }
        }
    }

    if let (Ok(web), Some(origins)) = (&web, origins) {
        for (&function, summary) in origins.iter() {
            if web.contains(function) {
                continue;
            }
            for (target_origin, target_signature) in summary.slots.iter_enumerated() {
                if !matches!(target_signature.place.root, SignatureRoot::Arg(_))
                    || target_signature.place.field.is_some()
                    || target_signature
                        .place
                        .deref_depth
                        .saturating_add(target_signature.depth)
                        == 0
                    || !model_is_ref(model, slots, function, *target_signature)
                {
                    continue;
                }
                let sources = summary
                    .slots
                    .iter_enumerated()
                    .filter(|(source_origin, source_signature)| {
                        *source_origin != target_origin
                            && matches!(source_signature.place.root, SignatureRoot::Arg(_))
                            && source_signature.place.field.is_none()
                            && summary.subset.contains(*source_origin, target_origin)
                            && model_is_ref(model, slots, function, **source_signature)
                    })
                    .collect::<Vec<_>>();
                if sources.is_empty() {
                    continue;
                }
                let mut required = sources
                    .iter()
                    .map(|(origin, _)| *origin)
                    .collect::<Vec<_>>();
                required.push(target_origin);
                if plan_function(summary, &required, &BTreeSet::new()).is_err() {
                    continue;
                }
                let Ok(sources) = sources
                    .into_iter()
                    .map(|(origin, slot)| {
                        FnSignatureSlot::from_summary(*slot).map(|slot| (slot, origin))
                    })
                    .collect::<Result<Vec<_>, _>>()
                else {
                    continue;
                };
                let Ok(target) = FnSignatureSlot::from_summary(*target_signature) else {
                    continue;
                };
                result.output_storage_permits.insert(
                    (function, target),
                    OutputStorageLifetimePermit::new(function, sources, (target, target_origin)),
                );
            }
        }
    }

    let signature_of = |key: NodeKey| {
        subjects
            .iter()
            .find(|subject| (subject.fn_did, subject.hir_id) == key)
            .and_then(|subject| match subject.kind {
                super::SubjectKind::Param { hir_index } => {
                    Some(FnSignatureSlot::arg(hir_index + 1, 0, 0))
                }
                super::SubjectKind::Local => None,
            })
    };
    for escape in escapes
        .iter()
        .filter(|escape| escape.kind == EscapeKind::FieldStore)
    {
        let Some(target) = escape.target else { continue };
        let (Some(source_slot), Some(target_root)) =
            (signature_of(escape.subject), signature_of(target))
        else {
            continue;
        };
        let target_slot = FnSignatureSlot {
            root: target_root.root,
            deref_depth: 0,
            depth: 1,
        };
        if result
            .output_storage_permits
            .get(&(escape.subject.0, target_slot))
            .is_some_and(|permit| permit.sources.contains(&source_slot))
        {
            result
                .output_storage_escapes
                .insert((escape.subject, target));
        }
    }
    for escape in escapes {
        let failure = match escape.kind {
            EscapeKind::ForeignArg => Some(LifetimeFailure::ExternalContractAbsent),
            EscapeKind::FieldStore if escape.target.is_none() => Some(LifetimeFailure::FieldHeld),
            _ => None,
        };
        if let Some(failure) = failure {
            result.failures.entry(escape.subject).or_insert(failure);
        }
    }

    let return_plan_functions = result
        .return_permits
        .values()
        .map(|permit| permit.function)
        .collect::<FxHashSet<_>>();
    for subject in subjects {
        let key = (subject.fn_did, subject.hir_id);
        let is_return_residual = decisions.get(&key).is_some_and(|decision| {
            matches!(
                decision,
                Decision::Degraded(record)
                    if record.reason == DegradeReason::ReturnNotAdapted
            )
        });
        if !is_return_residual {
            continue;
        }
        if matches!(subject.ctor, Some(Construction::Alloc { .. })) {
            result.failures.insert(key, LifetimeFailure::OriginAbsent);
            continue;
        }
        if !matches!(subject.ctor, Some(Construction::CallResult)) {
            continue;
        }
        let Some(target) = constructions.call_result_targets.get(&key).copied() else {
            result
                .failures
                .insert(key, LifetimeFailure::ExternalContractAbsent);
            continue;
        };
        let callee = match target {
            CallResultTarget::DirectLocal(callee) => callee,
            CallResultTarget::Indirect => {
                result.failures.insert(key, LifetimeFailure::FnPtrWebHeld);
                continue;
            }
            CallResultTarget::Foreign | CallResultTarget::Unresolved => {
                result
                    .failures
                    .insert(key, LifetimeFailure::ExternalContractAbsent);
                continue;
            }
        };
        let Ok(web) = &web else {
            result.failures.insert(key, LifetimeFailure::FnPtrWebHeld);
            continue;
        };
        if web.contains(subject.fn_did) || web.contains(callee) {
            result.failures.insert(key, LifetimeFailure::FnPtrWebHeld);
            continue;
        }
        let Some(slot) = slots
            .fn_local_slots
            .get(&subject.fn_did)
            .and_then(|universe| universe.slot_for_local_depth(subject.local, 0))
        else {
            result.failures.insert(key, LifetimeFailure::OriginConflict);
            continue;
        };
        if model.get(&SlotRef::Local(subject.fn_did, slot)) != Some(&SlotKind::Ref) {
            result.failures.insert(key, LifetimeFailure::OriginConflict);
            continue;
        }
        if !return_plan_functions.contains(&callee) {
            result.failures.insert(key, LifetimeFailure::OriginAbsent);
            continue;
        }
        result
            .inferred_permits
            .insert(key, InferredLifetimePermit::new(key, callee));
    }

    result
}

impl LifetimeFailure {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::OriginUnknown => "lifetime-origin-unknown",
            Self::OriginAbsent => "lifetime-origin-absent",
            Self::OriginConflict => "lifetime-origin-conflict",
            Self::FieldHeld => "lifetime-field-held",
            Self::ExternalContractAbsent => "lifetime-external-contract-absent",
            Self::FnPtrWebHeld => "lifetime-fnptr-web-held",
            Self::AstUnplaceable => "lifetime-ast-unplaceable",
            Self::SeamIncompatible => "lifetime-seam-incompatible",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FunctionPlan {
    lifetimes: BTreeMap<FnSignatureSlot, String>,
    pub(crate) sccs: Vec<Vec<FnSignatureSlot>>,
    pub(crate) outlives: Vec<(String, String)>,
}

/// Final, analysis-blind carrier handed to seam planning and structural AST
/// emission. Eligibility retains origin identities; this value retains only
/// the settled signature plan.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct LifetimePlan {
    functions: FxHashMap<LocalDefId, FunctionPlan>,
}

impl LifetimePlan {
    pub(crate) fn function(&self, did: LocalDefId) -> Option<&FunctionPlan> {
        self.functions.get(&did)
    }

    pub(crate) fn function_count(&self) -> usize {
        self.functions.len()
    }

    pub(crate) fn functions(&self) -> impl Iterator<Item = (LocalDefId, &FunctionPlan)> + '_ {
        self.functions.iter().map(|(&did, plan)| (did, plan))
    }

    pub(crate) fn canonical_receipt(&self, tcx: rustc_middle::ty::TyCtxt<'_>) -> String {
        let mut rows = self
            .functions
            .iter()
            .map(|(&did, plan)| {
                (
                    tcx.def_path_str(did.to_def_id()),
                    plan.receipt().replace('\n', " | "),
                )
            })
            .collect::<Vec<_>>();
        rows.sort_by(|left, right| left.0.cmp(&right.0));
        rows.into_iter()
            .map(|(function, receipt)| format!("{function}\t{receipt}"))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl FunctionPlan {
    pub(crate) fn lifetime_for(&self, slot: FnSignatureSlot) -> Option<&str> {
        self.lifetimes.get(&slot).map(String::as_str)
    }

    pub(crate) fn receipt(&self) -> String {
        let mut rows = Vec::new();
        for (slot, lifetime) in &self.lifetimes {
            rows.push(format!("slot\t{}\t{lifetime}", slot.receipt_key()));
        }
        for (longer, shorter) in &self.outlives {
            rows.push(format!("outlives\t{longer}\t{shorter}"));
        }
        rows.join("\n")
    }

    pub(crate) fn digest(&self) -> String {
        format!("{:x}", Sha256::digest(self.receipt().as_bytes()))
    }

    pub(crate) fn lifetimes(&self) -> impl Iterator<Item = (&FnSignatureSlot, &str)> {
        self.lifetimes
            .iter()
            .map(|(slot, lifetime)| (slot, lifetime.as_str()))
    }

    pub(crate) fn generated_names(&self) -> Vec<&str> {
        let mut names = self
            .lifetimes
            .values()
            .map(String::as_str)
            .collect::<Vec<_>>();
        names.sort_unstable();
        names.dedup();
        names
    }
}

fn existing_lifetime_names(program: &RustProgram<'_>, did: LocalDefId) -> BTreeSet<String> {
    let rustc_hir::Node::Item(item) = program.tcx.hir_node_by_def_id(did) else {
        return BTreeSet::new();
    };
    let Some(generics) = item.kind.generics() else {
        return BTreeSet::new();
    };
    generics
        .params
        .iter()
        .filter(|param| matches!(param.kind, rustc_hir::GenericParamKind::Lifetime { .. }))
        .map(|param| {
            param
                .name
                .ident()
                .name
                .as_str()
                .trim_start_matches('\'')
                .to_owned()
        })
        .collect()
}

pub(crate) fn finalize(
    program: &RustProgram<'_>,
    origins: Option<&OriginSummaries>,
    eligibility: &LifetimeEligibility,
    table: &DecisionTable,
) -> Result<LifetimePlan, String> {
    let Some(origins) = origins else {
        return Ok(LifetimePlan::default());
    };
    let final_decisions = table
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect::<FxHashMap<_, _>>();
    let mut required = FxHashMap::<LocalDefId, BTreeSet<OriginSlot>>::default();
    for (subject, permit) in &eligibility.return_permits {
        if !matches!(
            final_decisions.get(subject),
            Some(Decision::Ref { .. } | Decision::Slice { .. } | Decision::Opt { .. })
        ) {
            continue;
        }
        let slots = required.entry(permit.function).or_default();
        slots.extend(permit.origin_sources.iter().copied());
        slots.insert(permit.origin_target);
    }
    for permit in eligibility.output_storage_permits.values() {
        let slots = required.entry(permit.function).or_default();
        slots.extend(permit.origin_sources.iter().copied());
        slots.insert(permit.origin_target);
    }

    let mut functions = FxHashMap::default();
    let mut owners = required.into_iter().collect::<Vec<_>>();
    owners.sort_by_key(|(did, _)| did.local_def_index.as_u32());
    for (did, slots) in owners {
        let summary = origins.get(&did).ok_or_else(|| {
            format!(
                "lifetime-origin-absent: no summary for {}",
                program.tcx.def_path_str(did.to_def_id())
            )
        })?;
        let required = slots.into_iter().collect::<Vec<_>>();
        let plan = plan_function(summary, &required, &existing_lifetime_names(program, did))
            .map_err(|failure| {
                format!(
                    "{}: {}",
                    failure.key(),
                    program.tcx.def_path_str(did.to_def_id())
                )
            })?;
        functions.insert(did, plan);
    }
    Ok(LifetimePlan { functions })
}

fn next_lifetime_name(used: &mut BTreeSet<String>) -> String {
    for byte in b'a'..=b'z' {
        let name = char::from(byte).to_string();
        if used.insert(name.clone()) {
            return name;
        }
    }
    let mut index = 0usize;
    loop {
        let name = format!("lt{index}");
        if used.insert(name.clone()) {
            return name;
        }
        index += 1;
    }
}

pub(crate) fn plan_function(
    summary: &OriginSummary,
    required: &[OriginSlot],
    existing_names: &BTreeSet<String>,
) -> Result<FunctionPlan, LifetimeFailure> {
    if required.is_empty() {
        return Err(LifetimeFailure::OriginAbsent);
    }

    let mut by_key = BTreeMap::<FnSignatureSlot, OriginSlot>::new();
    for &origin_slot in required {
        let Some(&signature_slot) = summary.slots.get(origin_slot) else {
            return Err(LifetimeFailure::OriginConflict);
        };
        let key = FnSignatureSlot::from_summary(signature_slot)?;
        if by_key.insert(key, origin_slot).is_some() {
            return Err(LifetimeFailure::OriginConflict);
        }
        if summary.unknown.contains(origin_slot) {
            return Err(LifetimeFailure::OriginUnknown);
        }
    }

    for (&target_key, &target) in &by_key {
        if target_key.needs_modeled_source()
            && !by_key
                .values()
                .copied()
                .any(|source| source != target && summary.subset.contains(source, target))
        {
            return Err(LifetimeFailure::OriginAbsent);
        }
    }

    let mut unassigned = by_key.clone();
    let mut groups = Vec::<Vec<(FnSignatureSlot, OriginSlot)>>::new();
    while let Some((&seed_key, &seed)) = unassigned.first_key_value() {
        let mut group = vec![(seed_key, seed)];
        unassigned.remove(&seed_key);
        let peers = unassigned
            .iter()
            .filter_map(|(&key, &slot)| {
                (summary.subset.contains(seed, slot) && summary.subset.contains(slot, seed))
                    .then_some((key, slot))
            })
            .collect::<Vec<_>>();
        for (key, slot) in peers {
            unassigned.remove(&key);
            group.push((key, slot));
        }
        group.sort_by_key(|(key, _)| *key);
        groups.push(group);
    }
    groups.sort_by_key(|group| group[0].0);

    let mut used = existing_names
        .iter()
        .map(|name| name.trim_start_matches('\'').to_owned())
        .collect::<BTreeSet<_>>();
    let mut lifetimes = BTreeMap::new();
    let mut group_names = Vec::new();
    for group in &groups {
        let name = next_lifetime_name(&mut used);
        for &(key, _) in group {
            lifetimes.insert(key, name.clone());
        }
        group_names.push(name);
    }

    let mut outlives = BTreeSet::new();
    for (source_index, source_group) in groups.iter().enumerate() {
        for (target_index, target_group) in groups.iter().enumerate() {
            if source_index == target_index {
                continue;
            }
            let flows = source_group.iter().any(|(_, source)| {
                target_group
                    .iter()
                    .any(|(_, target)| summary.subset.contains(*source, *target))
            });
            if flows {
                outlives.insert((
                    group_names[source_index].clone(),
                    group_names[target_index].clone(),
                ));
            }
        }
    }

    Ok(FunctionPlan {
        lifetimes,
        sccs: groups
            .into_iter()
            .map(|group| group.into_iter().map(|(key, _)| key).collect())
            .collect(),
        outlives: outlives.into_iter().collect(),
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum WebDerivation {
    AdjustedFnPtr,
    Direct { caller: LocalDefId, block: u32 },
    Andersen { caller: LocalDefId, block: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FnPtrWeb {
    roots: FxHashSet<LocalDefId>,
    members: FxHashSet<LocalDefId>,
    reasons: FxHashMap<LocalDefId, WebDerivation>,
}

impl FnPtrWeb {
    pub(crate) fn contains(&self, function: LocalDefId) -> bool {
        self.members.contains(&function)
    }

    pub(crate) fn root_count(&self) -> usize {
        self.roots.len()
    }

    pub(crate) fn member_count(&self) -> usize {
        self.members.len()
    }

    #[cfg(test)]
    fn root_paths(&self, tcx: rustc_middle::ty::TyCtxt<'_>) -> Vec<String> {
        let mut paths = self
            .roots
            .iter()
            .map(|did| tcx.item_name(did.to_def_id()).to_string())
            .collect::<Vec<_>>();
        paths.sort();
        paths
    }

    #[cfg(test)]
    fn member_paths(&self, tcx: rustc_middle::ty::TyCtxt<'_>) -> Vec<String> {
        let mut paths = self
            .members
            .iter()
            .map(|did| tcx.item_name(did.to_def_id()).to_string())
            .collect::<Vec<_>>();
        paths.sort();
        paths
    }

    #[cfg(test)]
    fn reason_rows(&self, tcx: rustc_middle::ty::TyCtxt<'_>) -> Vec<String> {
        let mut rows = self
            .reasons
            .iter()
            .map(|(did, reason)| {
                let name = tcx.item_name(did.to_def_id());
                match reason {
                    WebDerivation::AdjustedFnPtr => format!("root\t{name}\tadjusted-fnptr"),
                    WebDerivation::Direct { caller, block } => format!(
                        "closure\t{name}\tdirect:{}:bb{block}",
                        tcx.item_name(caller.to_def_id())
                    ),
                    WebDerivation::Andersen { caller, block } => format!(
                        "closure\t{name}\tandersen:{}:bb{block}",
                        tcx.item_name(caller.to_def_id())
                    ),
                }
            })
            .collect::<Vec<_>>();
        rows.sort();
        rows
    }
}

fn collect_fn_ptr_roots(program: &RustProgram<'_>) -> FxHashSet<LocalDefId> {
    struct RootCollector<'tcx> {
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        roots: FxHashSet<LocalDefId>,
    }

    impl<'tcx> Visitor<'tcx> for RootCollector<'tcx> {
        fn visit_expr(&mut self, expression: &'tcx rustc_hir::Expr<'tcx>) {
            let mut function = None;
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expression.kind
                && let Res::Def(DefKind::Fn | DefKind::AssocFn, did) = path.res
            {
                function = did.as_local();
            } else if let ExprKind::Cast(inner, ty) = &expression.kind
                && matches!(ty.kind, rustc_hir::TyKind::BareFn(_))
                && let ExprKind::Path(QPath::Resolved(_, path)) = &inner.kind
                && let Res::Def(DefKind::Fn | DefKind::AssocFn, did) = path.res
            {
                function = did.as_local();
            }

            if let Some(function) = function
                && matches!(
                    self.tcx
                        .typeck(expression.hir_id.owner)
                        .expr_ty_adjusted(expression)
                        .kind(),
                    TyKind::FnPtr(..)
                )
            {
                self.roots.insert(function);
            }
            walk_expr(self, expression);
        }
    }

    let local_functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let mut collector = RootCollector {
        tcx: program.tcx,
        roots: FxHashSet::default(),
    };
    for &function in &program.functions {
        collector.visit_body(program.tcx.hir_body_owned_by(function));
    }
    collector
        .roots
        .retain(|function| local_functions.contains(function));
    collector.roots
}

fn web_reason_order(reason: &WebDerivation) -> (u8, u32, u32) {
    match *reason {
        WebDerivation::AdjustedFnPtr => (0, 0, 0),
        WebDerivation::Direct { caller, block } => (1, caller.local_def_index.as_u32(), block),
        WebDerivation::Andersen { caller, block } => (2, caller.local_def_index.as_u32(), block),
    }
}

fn edge_derivation(
    program: &RustProgram<'_>,
    caller: LocalDefId,
    block: rustc_middle::mir::BasicBlock,
) -> WebDerivation {
    let body_ref = program
        .tcx
        .mir_drops_elaborated_and_const_checked(caller)
        .borrow();
    let body = &*body_ref;
    let call = match &body.basic_blocks[block].terminator().kind {
        TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
        _ => unreachable!("closed call-world key must name a call"),
    };
    if matches!(call.ty(body, program.tcx).kind(), TyKind::FnDef(..)) {
        WebDerivation::Direct {
            caller,
            block: block.as_u32(),
        }
    } else {
        WebDerivation::Andersen {
            caller,
            block: block.as_u32(),
        }
    }
}

pub(crate) fn derive_fn_ptr_web(
    program: &RustProgram<'_>,
    attestation: Option<WholeProgramAttestation>,
) -> Result<FnPtrWeb, LifetimeFailure> {
    if attestation != Some(WholeProgramAttestation::FrozenBenchmarkGraph) {
        return Err(LifetimeFailure::FnPtrWebHeld);
    }

    let roots = collect_fn_ptr_roots(program);
    let call_world = resolve_closed_world_call_world(program, attestation);
    let mut members = FxHashSet::default();
    let mut reasons = roots
        .iter()
        .copied()
        .map(|root| (root, WebDerivation::AdjustedFnPtr))
        .collect::<FxHashMap<_, _>>();
    let mut pending = roots.iter().copied().collect::<Vec<_>>();
    pending.sort_unstable_by_key(|did| std::cmp::Reverse(did.local_def_index.as_u32()));

    while let Some(function) = pending.pop() {
        if !members.insert(function) {
            continue;
        }

        let mut edges = Vec::new();
        for (&(caller, block), targets) in &call_world.resolved {
            if caller != function {
                continue;
            }
            for &target in targets {
                edges.push((target, edge_derivation(program, caller, block)));
            }
        }
        edges.sort_by_key(|(target, reason)| {
            (target.local_def_index.as_u32(), web_reason_order(reason))
        });
        edges.dedup_by_key(|(target, _)| *target);
        for (target, reason) in edges.into_iter().rev() {
            if !members.contains(&target) {
                reasons.entry(target).or_insert(reason);
                pending.push(target);
            }
        }
    }

    Ok(FnPtrWeb {
        roots,
        members,
        reasons,
    })
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FnPtrWebDivergence {
    side: &'static str,
    unit: &'static str,
    function: String,
    reason: String,
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FnPtrWebDifferential {
    pub(crate) production_roots: usize,
    pub(crate) oracle_roots: usize,
    pub(crate) production_members: usize,
    pub(crate) oracle_members: usize,
    pub(crate) divergences: Vec<FnPtrWebDivergence>,
}

#[cfg(test)]
impl FnPtrWebDifferential {
    pub(crate) fn tsv(&self) -> String {
        let mut output = String::from("side\tunit\tfunction\treason\n");
        for row in &self.divergences {
            output.push_str(&format!(
                "{}\t{}\t{}\t{}\n",
                row.side, row.unit, row.function, row.reason
            ));
        }
        output
    }
}

#[cfg(test)]
fn derivation_text(tcx: rustc_middle::ty::TyCtxt<'_>, reason: &WebDerivation) -> String {
    match *reason {
        WebDerivation::AdjustedFnPtr => "adjusted-fnptr".to_owned(),
        WebDerivation::Direct { caller, block } => {
            format!("direct:{}:bb{block}", tcx.def_path_str(caller))
        }
        WebDerivation::Andersen { caller, block } => {
            format!("andersen:{}:bb{block}", tcx.def_path_str(caller))
        }
    }
}

#[cfg(test)]
fn oracle_web(
    program: &RustProgram<'_>,
    roots: &FxHashSet<LocalDefId>,
    resolved: &FxHashMap<(LocalDefId, rustc_middle::mir::BasicBlock), Vec<LocalDefId>>,
) -> (FxHashSet<LocalDefId>, FxHashMap<LocalDefId, WebDerivation>) {
    let mut members = FxHashSet::default();
    let mut reasons = roots
        .iter()
        .copied()
        .map(|root| (root, WebDerivation::AdjustedFnPtr))
        .collect::<FxHashMap<_, _>>();
    let mut pending = roots.iter().copied().collect::<Vec<_>>();
    while let Some(function) = pending.pop() {
        if !members.insert(function) {
            continue;
        }
        let mut outgoing = resolved
            .iter()
            .filter(|((caller, _), _)| *caller == function)
            .flat_map(|(&(caller, block), targets)| {
                targets
                    .iter()
                    .copied()
                    .map(move |target| (target, edge_derivation(program, caller, block)))
            })
            .collect::<Vec<_>>();
        outgoing.sort_by_key(|(target, reason)| {
            (target.local_def_index.as_u32(), web_reason_order(reason))
        });
        for (target, reason) in outgoing.into_iter().rev() {
            if !members.contains(&target) {
                reasons.entry(target).or_insert(reason);
                pending.push(target);
            }
        }
    }
    (members, reasons)
}

#[cfg(test)]
pub(crate) fn fn_ptr_web_differential(
    program: &RustProgram<'_>,
    attestation: Option<WholeProgramAttestation>,
) -> Result<FnPtrWebDifferential, LifetimeFailure> {
    let production = derive_fn_ptr_web(program, attestation)?;
    let local = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let mut oracle_roots = crate::rewriter::collector::collect_fn_ptrs(program);
    oracle_roots.retain(|function| local.contains(function));
    let call_world = resolve_closed_world_call_world(program, attestation);
    let (oracle_members, oracle_reasons) = oracle_web(program, &oracle_roots, &call_world.resolved);

    let mut divergences = Vec::new();
    for (unit, production_set, oracle_set) in [
        ("root", &production.roots, &oracle_roots),
        ("closure", &production.members, &oracle_members),
    ] {
        for function in production_set.difference(oracle_set) {
            divergences.push(FnPtrWebDivergence {
                side: "production-only",
                unit,
                function: program.tcx.def_path_str(*function),
                reason: derivation_text(program.tcx, &production.reasons[function]),
            });
        }
        for function in oracle_set.difference(production_set) {
            divergences.push(FnPtrWebDivergence {
                side: "p-b-only",
                unit,
                function: program.tcx.def_path_str(*function),
                reason: derivation_text(program.tcx, &oracle_reasons[function]),
            });
        }
    }
    divergences.sort_by(|left, right| {
        (left.unit, left.function.as_str(), left.side).cmp(&(
            right.unit,
            right.function.as_str(),
            right.side,
        ))
    });

    Ok(FnPtrWebDifferential {
        production_roots: production.roots.len(),
        oracle_roots: oracle_roots.len(),
        production_members: production.members.len(),
        oracle_members: oracle_members.len(),
        divergences,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use rustc_index::{
        IndexVec,
        bit_set::{DenseBitSet, SparseBitMatrix},
    };
    use rustc_middle::mir::Local;

    use super::*;
    use crate::analyses::borrow_ownership::origin_summary::{
        OriginSlot, OriginSummary, SignaturePlace, SignatureRoot, SignatureSlot,
    };

    fn arg(index: usize) -> SignatureSlot {
        SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Arg(Local::from_usize(index)),
                deref_depth: 0,
                field: None,
            },
            depth: 0,
        }
    }

    fn ret() -> SignatureSlot {
        SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Return,
                deref_depth: 0,
                field: None,
            },
            depth: 0,
        }
    }

    fn summary(
        slots: Vec<SignatureSlot>,
        edges: &[(usize, usize)],
        unknowns: &[usize],
    ) -> OriginSummary {
        let mut subset = SparseBitMatrix::new(slots.len());
        for &(source, target) in edges {
            subset.insert(
                OriginSlot::from_usize(source),
                OriginSlot::from_usize(target),
            );
        }
        let mut unknown = DenseBitSet::new_empty(slots.len());
        for &slot in unknowns {
            unknown.insert(OriginSlot::from_usize(slot));
        }
        OriginSummary {
            slots: IndexVec::from_raw(slots),
            subset,
            unknown,
        }
    }

    #[test]
    fn e2_w1_arg_return_shares_one_lifetime_relation() {
        let summary = summary(vec![arg(1), ret()], &[(0, 1)], &[]);
        let plan = plan_function(
            &summary,
            &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
            &BTreeSet::new(),
        )
        .expect("modeled input-to-return plan");

        assert_eq!(plan.lifetime_for(FnSignatureSlot::arg(1, 0, 0)), Some("a"));
        assert_eq!(plan.lifetime_for(FnSignatureSlot::RETURN), Some("b"));
        assert_eq!(plan.outlives, vec![("a".to_owned(), "b".to_owned())]);
    }

    #[test]
    fn e2_w2_multi_source_return_emits_ordered_outlives() {
        let summary = summary(vec![arg(1), arg(2), ret()], &[(0, 2), (1, 2)], &[]);
        let required = [
            OriginSlot::from_usize(2),
            OriginSlot::from_usize(0),
            OriginSlot::from_usize(1),
        ];
        let plan =
            plan_function(&summary, &required, &BTreeSet::new()).expect("multi-source return plan");

        assert_eq!(
            plan.outlives,
            vec![
                ("a".to_owned(), "c".to_owned()),
                ("b".to_owned(), "c".to_owned()),
            ]
        );
        assert_eq!(plan.sccs.len(), 3);
    }

    /// E2-W2b — compilation cannot distinguish an SCC collapse from two
    /// lifetimes carrying reflexive bounds, so the plan shape is the oracle.
    #[test]
    fn e2_w2b_mutual_arguments_collapse_to_one_lifetime_without_reflexive_bound() {
        let summary = summary(
            vec![arg(1), arg(2), ret()],
            &[(0, 1), (1, 0), (0, 2), (1, 2)],
            &[],
        );
        let plan = plan_function(
            &summary,
            &[
                OriginSlot::from_usize(0),
                OriginSlot::from_usize(1),
                OriginSlot::from_usize(2),
            ],
            &BTreeSet::new(),
        )
        .expect("mutually reachable argument plan");
        let arg1 = FnSignatureSlot::arg(1, 0, 0);
        let arg2 = FnSignatureSlot::arg(2, 0, 0);
        let mutual = plan
            .sccs
            .iter()
            .filter(|scc| scc.contains(&arg1) || scc.contains(&arg2))
            .collect::<Vec<_>>();
        assert_eq!(mutual.len(), 1, "plan={}", plan.receipt());
        assert_eq!(mutual[0], &vec![arg1, arg2], "plan={}", plan.receipt());
        assert_eq!(plan.lifetime_for(arg1), plan.lifetime_for(arg2));
        assert!(
            plan.outlives
                .iter()
                .all(|(longer, shorter)| longer != shorter),
            "reflexive outlives relation survived SCC collapse: {}",
            plan.receipt(),
        );
    }

    #[test]
    fn e2_w5_existing_names_and_input_order_do_not_change_plan_bytes() {
        let summary = summary(vec![arg(1), ret()], &[(0, 1)], &[]);
        let existing = BTreeSet::from(["a".to_owned(), "b".to_owned()]);
        let forward = plan_function(
            &summary,
            &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
            &existing,
        )
        .expect("forward plan");
        let reverse = plan_function(
            &summary,
            &[OriginSlot::from_usize(1), OriginSlot::from_usize(0)],
            &existing,
        )
        .expect("reverse plan");

        assert_eq!(forward.receipt(), reverse.receipt());
        assert_eq!(
            forward.lifetime_for(FnSignatureSlot::arg(1, 0, 0)),
            Some("c")
        );
        assert_eq!(forward.lifetime_for(FnSignatureSlot::RETURN), Some("d"));
    }

    #[test]
    fn e2_n1_unknown_origin_is_a_mandatory_veto() {
        let summary = summary(vec![arg(1), ret()], &[(0, 1)], &[1]);
        assert_eq!(
            plan_function(
                &summary,
                &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
                &BTreeSet::new(),
            ),
            Err(LifetimeFailure::OriginUnknown)
        );
    }

    #[test]
    fn e2_n2_return_without_a_modeled_source_is_absent() {
        let summary = summary(vec![arg(1), ret()], &[], &[]);
        assert_eq!(
            plan_function(
                &summary,
                &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
                &BTreeSet::new(),
            ),
            Err(LifetimeFailure::OriginAbsent)
        );
    }

    #[test]
    fn e2_n7_fnptr_root_and_forward_callee_are_both_held() {
        let code = r#"
            pub unsafe fn leaf(p: *mut i32) -> *mut i32 { p }
            pub unsafe fn root(p: *mut i32) -> *mut i32 { leaf(p) }
            pub unsafe fn install() {
                let _callback: unsafe fn(*mut i32) -> *mut i32 = root;
            }
            pub unsafe fn direct_only(p: *mut i32) -> *mut i32 { p }
        "#;
        let (roots, members, reasons) = ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let web = derive_fn_ptr_web(
                &program,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
            .expect("attested fixture web");
            (
                web.root_paths(tcx),
                web.member_paths(tcx),
                web.reason_rows(tcx),
            )
        })
        .expect("N7 fixture compiles");

        assert_eq!(roots, vec!["root"]);
        assert_eq!(members, vec!["leaf", "root"]);
        assert!(
            reasons
                .iter()
                .any(|row| row == "root\troot\tadjusted-fnptr")
        );
        assert!(
            reasons
                .iter()
                .any(|row| row.starts_with("closure\tleaf\tdirect:"))
        );
        assert!(!members.iter().any(|name| name == "install"));
        assert!(!members.iter().any(|name| name == "direct_only"));
    }

    #[test]
    fn e2_n7_unattested_web_fails_closed() {
        let code = "pub unsafe fn f(p: *mut i32) -> *mut i32 { p }";
        let result = ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            derive_fn_ptr_web(&program, None)
        })
        .expect("N7 unattested fixture compiles");
        assert_eq!(result, Err(LifetimeFailure::FnPtrWebHeld));
    }

    #[test]
    fn e2_p_b_differential_is_identity_exact_and_typed() {
        let code = r#"
            pub unsafe fn leaf(p: *mut i32) -> *mut i32 { p }
            pub unsafe fn root(p: *mut i32) -> *mut i32 { leaf(p) }
            pub unsafe fn install() {
                let _callback: unsafe fn(*mut i32) -> *mut i32 = root;
            }
        "#;
        let differential = ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            fn_ptr_web_differential(
                &program,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
            .expect("attested P-b differential")
        })
        .expect("P-b differential fixture compiles");

        assert_eq!(differential.production_roots, 1);
        assert_eq!(differential.oracle_roots, 1);
        assert_eq!(differential.production_members, 2);
        assert_eq!(differential.oracle_members, 2);
        assert!(differential.divergences.is_empty(), "{differential:#?}");
        assert_eq!(
            differential.tsv().lines().next(),
            Some("side\tunit\tfunction\treason")
        );
    }
}
