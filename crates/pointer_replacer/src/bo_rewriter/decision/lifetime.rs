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
    mir::{self, Location, RETURN_PLACE, StatementKind, TerminatorKind},
    ty::TyKind,
};
use rustc_span::Span;
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
        a5_producer::{ClosedWorldCallWorld, resolve_closed_world_call_world},
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
    web_roots: BTreeSet<String>,
    web_members: BTreeMap<String, String>,
    fnptr_web: Option<FnPtrWeb>,
    web_wall_s: f64,
    derive_wall_s: f64,
}

impl LifetimeEligibility {
    pub(crate) fn return_permit(&self, subject: NodeKey) -> Option<&ReturnLifetimePermit> {
        self.return_permits.get(&subject)
    }

    pub(crate) fn return_permit_count(&self) -> usize {
        self.return_permits.len()
    }

    #[cfg(test)]
    pub(crate) fn remove_return_permit_for_test(&mut self, subject: NodeKey) -> bool {
        self.return_permits.remove(&subject).is_some()
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

    pub(crate) fn web_roots(&self) -> &BTreeSet<String> {
        &self.web_roots
    }

    pub(crate) fn web_members(&self) -> &BTreeMap<String, String> {
        &self.web_members
    }

    pub(crate) fn fnptr_web(&self) -> Option<&FnPtrWeb> {
        self.fnptr_web.as_ref()
    }

    pub(crate) fn web_wall_s(&self) -> f64 {
        self.web_wall_s
    }

    pub(crate) fn derive_wall_s(&self) -> f64 {
        self.derive_wall_s
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
            web_roots: BTreeSet::new(),
            web_members: BTreeMap::new(),
            fnptr_web: None,
            web_wall_s: 0.0,
            derive_wall_s: 0.0,
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
    web: Result<FnPtrWeb, LifetimeFailure>,
    web_wall_s: f64,
    exposure: &super::exposure::ExposurePolicy,
) -> LifetimeEligibility {
    let derive_started = std::time::Instant::now();
    let mut result = LifetimeEligibility::default();
    let decisions = hypothetical
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect::<FxHashMap<_, _>>();
    result.web_wall_s = web_wall_s;
    if let Ok(web) = &web {
        result.web_roots = web
            .roots
            .iter()
            .map(|did| program.tcx.def_path_str(*did))
            .collect();
        result.web_members = web
            .members
            .iter()
            .map(|did| {
                (
                    program.tcx.def_path_str(*did),
                    derivation_text(program.tcx, &web.reasons[did]),
                )
            })
            .collect();
        result.fnptr_web = Some(web.clone());
    }

    let mut return_subjects = escapes
        .iter()
        .filter(|escape| escape.kind == EscapeKind::Return)
        .map(|escape| escape.subject)
        .collect::<Vec<_>>();
    return_subjects
        .sort_unstable_by_key(|(did, hir)| (did.local_def_index.as_u32(), hir.local_id.as_u32()));
    return_subjects.dedup();

    for subject in return_subjects {
        let candidate = match decisions.get(&subject) {
            Some(Decision::Ref { .. }) => true,
            Some(Decision::InferredRef { .. }) => false,
            Some(Decision::Slice { .. }) => false,
            Some(Decision::Opt { .. }) => false,
            Some(Decision::Box(_)) => false,
            Some(Decision::Degraded(_)) => false,
            None => false,
        };
        if !candidate {
            continue;
        }
        let function = subject.0;
        let Ok(web) = &web else {
            result
                .failures
                .insert(subject, LifetimeFailure::FnPtrWebHeld);
            continue;
        };
        if web.contains(function)
            && matches!(
                exposure.plan(function),
                super::exposure::ExposureSurfacePlan::NotApplicable
            )
        {
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

    result.derive_wall_s = derive_started.elapsed().as_secs_f64();
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
    return_reuses: Vec<ReturnLifetimeReuse>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ReturnTie {
    sources: Vec<FnSignatureSlot>,
    target: FnSignatureSlot,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReturnLifetimeReuse {
    sources: Vec<FnSignatureSlot>,
    target: FnSignatureSlot,
    common_name: String,
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
        for reuse in &self.return_reuses {
            rows.push(format!(
                "return_tie\tsources={}\ttarget={}\tcommon_name={}\treturn_lifetime_reused=true",
                reuse
                    .sources
                    .iter()
                    .map(|slot| slot.receipt_key())
                    .collect::<Vec<_>>()
                    .join(","),
                reuse.target.receipt_key(),
                reuse.common_name,
            ));
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
    let mut return_ties = FxHashMap::<LocalDefId, BTreeSet<ReturnTie>>::default();
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
        let mut sources = permit.sources.clone();
        sources.sort();
        sources.dedup();
        return_ties
            .entry(permit.function)
            .or_default()
            .insert(ReturnTie {
                sources,
                target: permit.target,
            });
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
        let ties = return_ties
            .remove(&did)
            .unwrap_or_default()
            .into_iter()
            .collect::<Vec<_>>();
        let plan = plan_function_with_return_ties(
            summary,
            &required,
            &existing_lifetime_names(program, did),
            &ties,
        )
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
    plan_function_with_return_ties(summary, required, existing_names, &[])
}

fn plan_function_with_return_ties(
    summary: &OriginSummary,
    required: &[OriginSlot],
    existing_names: &BTreeSet<String>,
    return_ties: &[ReturnTie],
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

    for tie in return_ties {
        let mut merged = Vec::new();
        let mut untouched = Vec::new();
        for group in groups.drain(..) {
            if group
                .iter()
                .any(|(key, _)| *key == tie.target || tie.sources.contains(key))
            {
                merged.extend(group);
            } else {
                untouched.push(group);
            }
        }
        let complete = std::iter::once(tie.target)
            .chain(tie.sources.iter().copied())
            .all(|required| merged.iter().any(|(key, _)| *key == required));
        if !complete {
            return Err(LifetimeFailure::OriginConflict);
        }
        merged.sort_by_key(|(key, _)| *key);
        merged.dedup_by_key(|(key, _)| *key);
        untouched.push(merged);
        groups = untouched;
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

    let mut return_reuses = Vec::new();
    for tie in return_ties {
        let Some(common_name) = lifetimes.get(&tie.target).cloned() else {
            return Err(LifetimeFailure::OriginConflict);
        };
        if !tie
            .sources
            .iter()
            .all(|source| lifetimes.get(source) == Some(&common_name))
        {
            return Err(LifetimeFailure::OriginConflict);
        }
        return_reuses.push(ReturnLifetimeReuse {
            sources: tie.sources.clone(),
            target: tie.target,
            common_name,
        });
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
        return_reuses,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum WebDerivation {
    AdjustedFnPtr,
    ConstMir {
        owner: LocalDefId,
        block: u32,
        statement: usize,
    },
    Direct {
        caller: LocalDefId,
        block: u32,
    },
    Andersen {
        caller: LocalDefId,
        block: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FnPtrWeb {
    roots: FxHashSet<LocalDefId>,
    members: FxHashSet<LocalDefId>,
    reasons: FxHashMap<LocalDefId, WebDerivation>,
    static_seeds: Vec<StaticFnPtrSeed>,
    mir_call_sites: Vec<MirCallTargetSite>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StaticFnPtrSeed {
    pub(crate) owner: LocalDefId,
    pub(crate) function: LocalDefId,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) span: Span,
}

/// One resolved target of one function-body MIR call terminator.  Unlike the
/// older HIR argument carrier, this inventory is independent of whether an
/// argument expression maps to a pointer-ledger subject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MirCallTargetSite {
    pub(crate) caller: LocalDefId,
    pub(crate) callee: LocalDefId,
    pub(crate) block: u32,
    pub(crate) argument_count: usize,
    pub(crate) span: Span,
}

impl StaticFnPtrSeed {
    pub(crate) fn location_key(&self) -> String {
        format!("bb{}:s{}", self.block, self.statement)
    }
}

impl FnPtrWeb {
    pub(crate) fn roots(&self) -> impl Iterator<Item = LocalDefId> + '_ {
        self.roots.iter().copied()
    }

    pub(crate) fn members(&self) -> impl Iterator<Item = LocalDefId> + '_ {
        self.members.iter().copied()
    }

    pub(crate) fn contains(&self, function: LocalDefId) -> bool {
        self.members.contains(&function)
    }

    pub(crate) fn static_seeds(&self) -> &[StaticFnPtrSeed] {
        &self.static_seeds
    }

    pub(crate) fn mir_call_sites(&self) -> &[MirCallTargetSite] {
        &self.mir_call_sites
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
                    WebDerivation::ConstMir {
                        owner,
                        block,
                        statement,
                    } => format!(
                        "root\t{name}\tconst-mir:{}:bb{block}:s{statement}",
                        tcx.item_name(owner.to_def_id())
                    ),
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

fn collect_const_mir_fn_ptr_seeds(program: &RustProgram<'_>) -> Vec<StaticFnPtrSeed> {
    struct OperandCollector<'a, 'tcx> {
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        body: &'a mir::Body<'tcx>,
        owner: LocalDefId,
        local_functions: &'a FxHashSet<LocalDefId>,
        hits: &'a mut Vec<StaticFnPtrSeed>,
    }

    impl<'tcx> mir::visit::Visitor<'tcx> for OperandCollector<'_, 'tcx> {
        fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, location: Location) {
            if let TyKind::FnDef(def_id, _) = operand.ty(self.body, self.tcx).kind()
                && let Some(function) = def_id.as_local()
                && self.local_functions.contains(&function)
            {
                self.hits.push(StaticFnPtrSeed {
                    owner: self.owner,
                    function,
                    block: location.block.as_u32(),
                    statement: location.statement_index,
                    span: self.body.source_info(location).span,
                });
            }
            self.super_operand(operand, location);
        }
    }

    let local_functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let mut hits = Vec::new();
    for owner in program.tcx.hir_body_owners().filter(|owner| {
        matches!(
            program.tcx.def_kind(*owner),
            DefKind::Static { .. }
                | DefKind::Const
                | DefKind::AssocConst
                | DefKind::AnonConst
                | DefKind::InlineConst
        )
    }) {
        // Const/static CTFE consumes the `Steal<Body>` behind
        // `mir_drops_elaborated_and_const_checked`.  `mir_for_ctfe` is the
        // cached, never-stolen body for these const-context owners.
        let body = program.tcx.mir_for_ctfe(owner);
        let mut collector = OperandCollector {
            tcx: program.tcx,
            body,
            owner,
            local_functions: &local_functions,
            hits: &mut hits,
        };
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(assignment) = &statement.kind else {
                    continue;
                };
                mir::visit::Visitor::visit_rvalue(
                    &mut collector,
                    &assignment.1,
                    Location {
                        block,
                        statement_index,
                    },
                );
            }
        }
    }
    hits.sort_by_key(|seed| {
        (
            seed.owner.local_def_index.as_u32(),
            seed.span.lo().0,
            seed.span.hi().0,
            seed.function.local_def_index.as_u32(),
        )
    });
    hits.dedup_by_key(|seed| {
        (
            seed.owner.local_def_index.as_u32(),
            seed.span.lo().0,
            seed.span.hi().0,
            seed.function.local_def_index.as_u32(),
        )
    });
    hits
}

fn collect_mir_call_target_sites(
    program: &RustProgram<'_>,
    call_world: &ClosedWorldCallWorld,
) -> Vec<MirCallTargetSite> {
    let functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let mut sites = Vec::new();
    for (&(caller, block), targets) in &call_world.resolved {
        if !functions.contains(&caller) {
            continue;
        }
        // `caller` is drawn only from `RustProgram::functions`, so this query
        // is a function-body read; unlike const/static owners, rustc does not
        // steal it for CTFE.
        let body_ref = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
        let terminator = body_ref.basic_blocks[block].terminator();
        let argument_count = match &terminator.kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => args.len(),
            _ => continue,
        };
        for &callee in targets {
            if functions.contains(&callee) {
                sites.push(MirCallTargetSite {
                    caller,
                    callee,
                    block: block.as_u32(),
                    argument_count,
                    span: terminator.source_info.span,
                });
            }
        }
    }
    sites.sort_by_key(|site| {
        (
            site.caller.local_def_index.as_u32(),
            site.block,
            site.callee.local_def_index.as_u32(),
            site.span.lo().0,
            site.span.hi().0,
        )
    });
    sites.dedup_by_key(|site| {
        (
            site.caller.local_def_index.as_u32(),
            site.block,
            site.callee.local_def_index.as_u32(),
        )
    });
    sites
}

fn web_reason_order(reason: &WebDerivation) -> (u8, u32, u32) {
    match *reason {
        WebDerivation::AdjustedFnPtr => (0, 0, 0),
        WebDerivation::ConstMir {
            owner,
            block,
            statement,
        } => (
            1,
            owner.local_def_index.as_u32(),
            block.saturating_add(u32::try_from(statement).unwrap_or(u32::MAX)),
        ),
        WebDerivation::Direct { caller, block } => (2, caller.local_def_index.as_u32(), block),
        WebDerivation::Andersen { caller, block } => (3, caller.local_def_index.as_u32(), block),
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

    // The frozen call-world builder still reads the drops-elaborated static
    // body through its legacy consumer.  Complete that read before the CTFE
    // query below consumes the `Steal`; the const-root collector is the
    // terminal reader and itself uses only `mir_for_ctfe`.
    let call_world = resolve_closed_world_call_world(program, attestation);
    let mir_call_sites = collect_mir_call_target_sites(program, &call_world);
    let mut roots = collect_fn_ptr_roots(program);
    let static_seeds = collect_const_mir_fn_ptr_seeds(program);
    roots.extend(static_seeds.iter().map(|seed| seed.function));
    let mut members = FxHashSet::default();
    let mut reasons = roots
        .iter()
        .copied()
        .map(|root| (root, WebDerivation::AdjustedFnPtr))
        .collect::<FxHashMap<_, _>>();
    for seed in &static_seeds {
        reasons.insert(
            seed.function,
            WebDerivation::ConstMir {
                owner: seed.owner,
                block: seed.block,
                statement: seed.statement,
            },
        );
    }
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
        static_seeds,
        mir_call_sites,
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

fn derivation_text(tcx: rustc_middle::ty::TyCtxt<'_>, reason: &WebDerivation) -> String {
    match *reason {
        WebDerivation::AdjustedFnPtr => "adjusted-fnptr".to_owned(),
        WebDerivation::ConstMir {
            owner,
            block,
            statement,
        } => format!(
            "const-mir:{}:bb{block}:s{statement}",
            tcx.def_path_str(owner)
        ),
        WebDerivation::Direct { caller, block } => {
            format!("direct:{}:bb{block}", tcx.def_path_str(caller))
        }
        WebDerivation::Andersen { caller, block } => {
            format!("andersen:{}:bb{block}", tcx.def_path_str(caller))
        }
    }
}

#[cfg(test)]
pub(crate) fn fn_ptr_web_differential(
    program: &RustProgram<'_>,
    attestation: Option<WholeProgramAttestation>,
    oracle_roots: &BTreeSet<String>,
    oracle_members: &BTreeSet<String>,
) -> Result<FnPtrWebDifferential, LifetimeFailure> {
    let production = derive_fn_ptr_web(program, attestation)?;
    let production_roots = production
        .roots
        .iter()
        .map(|did| program.tcx.def_path_str(*did))
        .collect::<BTreeSet<_>>();
    let production_members = production
        .members
        .iter()
        .map(|did| program.tcx.def_path_str(*did))
        .collect::<BTreeSet<_>>();
    let production_by_path = production
        .members
        .iter()
        .map(|did| (program.tcx.def_path_str(*did), *did))
        .collect::<BTreeMap<_, _>>();

    let mut divergences = Vec::new();
    for (unit, production_set, oracle_set) in [
        ("root", &production_roots, oracle_roots),
        ("closure", &production_members, oracle_members),
    ] {
        for function in production_set.difference(oracle_set) {
            let did = production_by_path[function];
            divergences.push(FnPtrWebDivergence {
                side: "production-only",
                unit,
                function: function.clone(),
                reason: derivation_text(program.tcx, &production.reasons[&did]),
            });
        }
        for function in oracle_set.difference(production_set) {
            divergences.push(FnPtrWebDivergence {
                side: "p-b-only",
                unit,
                function: function.clone(),
                reason: "frozen-control".to_owned(),
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
        production_roots: production_roots.len(),
        oracle_roots: oracle_roots.len(),
        production_members: production_members.len(),
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
    fn life_w2_return_tie_cannot_override_an_unknown_origin() {
        let summary = summary(vec![arg(1), ret()], &[(0, 1)], &[1]);
        let tie = ReturnTie {
            sources: vec![FnSignatureSlot::arg(1, 0, 0)],
            target: FnSignatureSlot::RETURN,
        };
        assert_eq!(
            plan_function_with_return_ties(
                &summary,
                &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
                &BTreeSet::new(),
                &[tie],
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
    fn e2_n4_field_signature_slot_is_held_before_planning() {
        let field = SignatureSlot {
            place: SignaturePlace {
                root: SignatureRoot::Arg(Local::from_usize(1)),
                deref_depth: 0,
                field: Some(crate::analyses::borrow_ownership::slots::StructFieldSlot {
                    struct_did: rustc_hir::def_id::CRATE_DEF_ID,
                    field_index: 0,
                }),
            },
            depth: 0,
        };
        let summary = summary(vec![arg(1), field], &[(0, 1)], &[]);
        assert_eq!(
            plan_function(
                &summary,
                &[OriginSlot::from_usize(0), OriginSlot::from_usize(1)],
                &BTreeSet::new(),
            ),
            Err(LifetimeFailure::FieldHeld),
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
                &BTreeSet::from(["root".to_owned()]),
                &BTreeSet::from(["leaf".to_owned(), "root".to_owned()]),
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

    /// CTFE-BODY-W1 — forcing the CTFE query for a static consumes the
    /// `Steal<Body>` behind `mir_drops_elaborated_and_const_checked`.  The
    /// const-initializer function-pointer collector must therefore read the
    /// cached CTFE body rather than borrowing the consumed wrapper.
    #[test]
    fn ctfe_body_w1_static_root_collection_survives_prior_ctfe_query() {
        let code = r#"
            pub type Callback = unsafe extern "C" fn(*mut i32) -> i32;
            pub unsafe extern "C" fn target(p: *mut i32) -> i32 { *p }
            pub static TABLE: [Option<Callback>; 1] = [Some(target as Callback)];
        "#;
        let seeds = ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let table = tcx
                .hir_body_owners()
                .find(|owner| matches!(tcx.def_kind(*owner), DefKind::Static { .. }))
                .expect("fixture static owner");
            let _ = tcx.mir_for_ctfe(table);
            collect_const_mir_fn_ptr_seeds(&program)
                .into_iter()
                .map(|seed| tcx.item_name(seed.function.to_def_id()).to_string())
                .collect::<Vec<_>>()
        })
        .expect("CTFE-before-collector fixture compiles");

        assert_eq!(seeds, vec!["target"]);
    }
}
