//! Raw-boundary facts and decisions.
//!
//! This module is rewriter-side by design. It consumes the frozen model/MIR and
//! never contributes a solver constraint or cache field.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::{
    mir::{
        Body, Local, Location, Operand, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::{Span, def_id::DefId};

use crate::{
    analyses::borrow_ownership::{
        a5_overlap::WholeProgramAttestation, origin_summary::OriginSummaries,
    },
    utils::rustc::RustProgram,
};

/// A lifetime-free, artifact-stable call-site identity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RawBoundarySiteKey {
    pub caller: String,
    pub block: u32,
    pub statement_index: u32,
    pub callee: ForeignSymbolKey,
    pub argument_index: usize,
    pub subject: String,
}

/// One exact raw-boundary edit identity.  The subject half supplies the
/// dependency group; the site half keeps two uses of the same subject
/// independently attributable until the closure is applied.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SubjectAtomKey {
    pub id: String,
    pub node: (LocalDefId, HirId),
    pub owner: String,
}

fn site_atom_id(key: &RawBoundarySiteKey) -> String {
    format!(
        "raw-boundary-site:{}:{}:{}:{}:{}:{}",
        key.caller,
        key.block,
        key.statement_index,
        key.callee.path,
        key.argument_index,
        key.subject
    )
}

fn address_atom_id(site: &AddressViewSite) -> String {
    format!(
        "raw-boundary-address:{}:{}:{}:{}:{}",
        site.owner,
        site.node.0.local_def_index.as_u32(),
        site.node.1.local_id.as_u32(),
        site.span.lo().0,
        site.op
    )
}

/// Resolved callee identity. `foreign` is load-bearing: a same-spelled local
/// function is not a libc contract match.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ForeignSymbolKey {
    pub symbol: String,
    pub path: String,
    pub abi: String,
    pub signature: String,
    pub foreign: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RawMutability {
    Const,
    Mut,
}

impl RawMutability {
    fn key(self) -> &'static str {
        match self {
            Self::Const => "const",
            Self::Mut => "mut",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawTargetType {
    pub rendered: String,
    pub pointee: String,
    pub mutability: RawMutability,
}

pub(crate) fn raw_target_type(ty: Ty<'_>) -> Option<RawTargetType> {
    let TyKind::RawPtr(pointee, mutability) = ty.kind() else {
        return None;
    };
    Some(RawTargetType {
        rendered: format!("{ty:?}"),
        pointee: format!("{pointee:?}"),
        mutability: if mutability.is_mut() {
            RawMutability::Mut
        } else {
            RawMutability::Const
        },
    })
}

/// One resolved argument to a non-body callee. This is the fact the old
/// `EscapeKind::ForeignArg` could not express: callee, position and target type
/// are captured at the HIR visitor boundary rather than reconstructed later.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ForeignCallArgFact {
    pub caller: LocalDefId,
    pub callee: ForeignSymbolKey,
    pub call_span: Span,
    pub argument_index: usize,
    pub argument_span: Span,
    pub root: Option<HirId>,
    pub shape: &'static str,
    pub source_type: String,
    pub target: RawTargetType,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BoundaryDirection {
    OutgoingArgument,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFact {
    pub key: RawBoundarySiteKey,
    pub node: Option<(LocalDefId, HirId)>,
    pub callee_local: Option<LocalDefId>,
    pub direction: BoundaryDirection,
    pub source_span: Span,
    pub source_shape: &'static str,
    pub source_type: String,
    pub target: RawTargetType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFailure {
    pub caller: String,
    pub node: Option<(LocalDefId, HirId)>,
    pub callee: ForeignSymbolKey,
    pub argument_index: usize,
    pub source_span: Span,
    pub reason: SiteMatchFailure,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFacts {
    pub sites: Vec<RawBoundarySiteFact>,
    pub failures: Vec<RawBoundarySiteFailure>,
}

pub(crate) fn symbol_key(
    tcx: TyCtxt<'_>,
    callee: DefId,
    body_functions: &[LocalDefId],
) -> ForeignSymbolKey {
    let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
    let foreign = !callee
        .as_local()
        .is_some_and(|local| body_functions.contains(&local));
    ForeignSymbolKey {
        symbol: tcx.item_name(callee).to_string(),
        path: tcx.def_path_str(callee),
        abi: format!("{:?}", sig.abi),
        signature: format!("{sig:?}"),
        foreign,
    }
}

fn operand_callee(func: &Operand<'_>) -> Option<DefId> {
    let constant = func.constant()?;
    let TyKind::FnDef(callee, _) = *constant.ty().kind() else {
        return None;
    };
    Some(callee)
}

fn mir_candidates(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    caller: LocalDefId,
    expected: &ForeignSymbolKey,
    argument_span: Span,
) -> Vec<MirCallCandidate> {
    let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
    let argument_span = argument_span.source_callsite();
    body.basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            let terminator = data.terminator();
            let func = match &terminator.kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
                _ => return None,
            };
            let callee = operand_callee(func)?;
            let key = symbol_key(tcx, callee, functions);
            let call_span = terminator.source_info.span.source_callsite();
            (key == *expected && call_span.contains(argument_span)).then_some(MirCallCandidate {
                block: block.as_u32(),
                statement_index: data.statements.len() as u32,
                callee: key,
            })
        })
        .collect()
}

impl RawBoundarySiteFacts {
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        emitability: &super::emitability::EmitabilityFacts,
    ) -> Self {
        let tcx = program.tcx;
        let mut out = Self::default();
        for fact in &emitability.foreign_call_args {
            let candidates = mir_candidates(
                tcx,
                &program.functions,
                fact.caller,
                &fact.callee,
                fact.argument_span,
            );
            match select_unique_site(&fact.callee, &candidates) {
                Ok((block, statement_index)) => out.sites.push(RawBoundarySiteFact {
                    key: RawBoundarySiteKey {
                        caller: tcx.def_path_str(fact.caller.to_def_id()),
                        block,
                        statement_index,
                        callee: fact.callee.clone(),
                        argument_index: fact.argument_index,
                        subject: fact
                            .root
                            .map_or_else(|| "<unrooted>".to_owned(), |root| format!("{root:?}")),
                    },
                    node: fact.root.map(|root| (fact.caller, root)),
                    callee_local: None,
                    direction: BoundaryDirection::OutgoingArgument,
                    source_span: fact.argument_span,
                    source_shape: fact.shape,
                    source_type: fact.source_type.clone(),
                    target: fact.target.clone(),
                }),
                Err(reason) => out.failures.push(RawBoundarySiteFailure {
                    caller: tcx.def_path_str(fact.caller.to_def_id()),
                    node: fact.root.map(|root| (fact.caller, root)),
                    callee: fact.callee.clone(),
                    argument_index: fact.argument_index,
                    source_span: fact.argument_span,
                    reason,
                }),
            }
        }
        for (&callee, calls) in &emitability.call_args {
            let callee_key = symbol_key(tcx, callee.to_def_id(), &program.functions);
            for call in calls {
                for argument in &call.args {
                    let Some(target) = argument.target.clone() else {
                        continue;
                    };
                    let candidates = mir_candidates(
                        tcx,
                        &program.functions,
                        call.caller,
                        &callee_key,
                        argument.span,
                    );
                    match select_unique_site(&callee_key, &candidates) {
                        Ok((block, statement_index)) => out.sites.push(RawBoundarySiteFact {
                            key: RawBoundarySiteKey {
                                caller: tcx.def_path_str(call.caller.to_def_id()),
                                block,
                                statement_index,
                                callee: callee_key.clone(),
                                argument_index: argument.index,
                                subject: argument.shape.place_root().map_or_else(
                                    || "<unrooted>".to_owned(),
                                    |root| format!("{root:?}"),
                                ),
                            },
                            node: argument.shape.place_root().map(|root| (call.caller, root)),
                            callee_local: Some(callee),
                            direction: BoundaryDirection::OutgoingArgument,
                            source_span: argument.span,
                            source_shape: argument.shape.key(),
                            source_type: argument.source_type.clone(),
                            target,
                        }),
                        Err(reason) => out.failures.push(RawBoundarySiteFailure {
                            caller: tcx.def_path_str(call.caller.to_def_id()),
                            node: argument.shape.place_root().map(|root| (call.caller, root)),
                            callee: callee_key.clone(),
                            argument_index: argument.index,
                            source_span: argument.span,
                            reason,
                        }),
                    }
                }
            }
        }
        out.sites.sort_by(|left, right| left.key.cmp(&right.key));
        out.failures.sort_by(|left, right| {
            (&left.caller, &left.callee, left.argument_index).cmp(&(
                &right.caller,
                &right.callee,
                right.argument_index,
            ))
        });
        out
    }

    pub(crate) fn to_tsv(&self) -> String {
        let mut out = String::from(
            "status\tcaller\tblock\tstatement_index\tcallee_path\tcallee_symbol\tforeign\tabi\tsignature\targument_index\tsubject\tsource_lo\tsource_hi\tsource_shape\tsource_type\ttarget_type\ttarget_pointee\ttarget_mutability\treason\n",
        );
        for site in &self.sites {
            out.push_str(&format!(
                "site\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t-\n",
                site.key.caller,
                site.key.block,
                site.key.statement_index,
                site.key.callee.path,
                site.key.callee.symbol,
                u8::from(site.key.callee.foreign),
                site.key.callee.abi,
                site.key.callee.signature,
                site.key.argument_index,
                site.key.subject,
                site.source_span.lo().0,
                site.source_span.hi().0,
                site.source_shape,
                site.source_type,
                site.target.rendered,
                site.target.pointee,
                site.target.mutability.key(),
            ));
        }
        for failure in &self.failures {
            out.push_str(&format!(
                "failure\t{}\t-\t-\t{}\t{}\t{}\t{}\t{}\t{}\t-\t{}\t{}\t-\t-\t-\t-\t-\t{}\n",
                failure.caller,
                failure.callee.path,
                failure.callee.symbol,
                u8::from(failure.callee.foreign),
                failure.callee.abi,
                failure.callee.signature,
                failure.argument_index,
                failure.source_span.lo().0,
                failure.source_span.hi().0,
                failure.reason.key(),
            ));
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MirCallCandidate {
    pub block: u32,
    pub statement_index: u32,
    pub callee: ForeignSymbolKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SiteMatchFailure {
    Missing,
    Ambiguous,
    CalleeMismatch,
}

impl SiteMatchFailure {
    fn key(self) -> &'static str {
        match self {
            Self::Missing => "site-missing",
            Self::Ambiguous => "site-ambiguous",
            Self::CalleeMismatch => "callee-mismatch",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RetentionUnknownReason {
    CalleeUnresolved,
    FnPtrWeb,
    OpenBoundary,
    MultiDef,
    NontransparentDef,
    ProjectionAmbiguous,
    OutputStorage,
    FieldOrGlobalStore,
    Return,
    LocalSummaryUnknown,
    AttestationAbsent,
    AnalysisIncomplete,
}

impl RetentionUnknownReason {
    pub(crate) const ALL: [Self; 12] = [
        Self::CalleeUnresolved,
        Self::FnPtrWeb,
        Self::OpenBoundary,
        Self::MultiDef,
        Self::NontransparentDef,
        Self::ProjectionAmbiguous,
        Self::OutputStorage,
        Self::FieldOrGlobalStore,
        Self::Return,
        Self::LocalSummaryUnknown,
        Self::AttestationAbsent,
        Self::AnalysisIncomplete,
    ];

    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::CalleeUnresolved => "retention-callee-unresolved",
            Self::FnPtrWeb => "retention-fnptr-web",
            Self::OpenBoundary => "retention-open-boundary",
            Self::MultiDef => "retention-multi-def",
            Self::NontransparentDef => "retention-nontransparent-def",
            Self::ProjectionAmbiguous => "retention-projection-ambiguous",
            Self::OutputStorage => "retention-output-storage",
            Self::FieldOrGlobalStore => "retention-field-or-global-store",
            Self::Return => "retention-return",
            Self::LocalSummaryUnknown => "retention-local-summary-unknown",
            Self::AttestationAbsent => "retention-attestation-absent",
            Self::AnalysisIncomplete => "retention-analysis-incomplete",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RetentionEventKind {
    Transparent,
    Return,
    OutputStorage,
    FieldOrGlobalStore,
    UnknownCall,
    KnownNoRetainCall,
    LocalCall,
    DereferenceOnly,
    Free,
    MultiDef,
    Nontransparent,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RetentionStep {
    pub location: String,
    pub kind: RetentionEventKind,
    pub detail: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RetentionCertificate {
    pub function: String,
    pub argument_index: usize,
    pub steps: Vec<RetentionStep>,
    pub attestation: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RetentionVerdict {
    NoRetain {
        certificate: RetentionCertificate,
    },
    Retains {
        sink: RetentionStep,
        path: Vec<RetentionStep>,
    },
    Unknown {
        reason: RetentionUnknownReason,
        frontier: Vec<RetentionStep>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RetentionDependency {
    callee: LocalDefId,
    argument_index: usize,
    step: RetentionStep,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RetentionBodyFacts {
    function: LocalDefId,
    function_path: String,
    argument_index: usize,
    steps: Vec<RetentionStep>,
    retains: Vec<RetentionStep>,
    unknowns: BTreeMap<RetentionUnknownReason, Vec<RetentionStep>>,
    dependencies: Vec<RetentionDependency>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RetentionSummaries {
    rows: FxHashMap<(LocalDefId, usize), RetentionVerdict>,
    facts: FxHashMap<(LocalDefId, usize), RetentionBodyFacts>,
    attested: bool,
}

fn location_label(location: Location) -> String {
    format!(
        "bb{}:s{}",
        location.block.as_u32(),
        location.statement_index
    )
}

fn retention_step(
    location: Location,
    kind: RetentionEventKind,
    detail: impl Into<String>,
) -> RetentionStep {
    RetentionStep {
        location: location_label(location),
        kind,
        detail: detail.into(),
    }
}

fn transparent_operand<'a, 'tcx>(rhs: &'a Rvalue<'tcx>) -> Option<&'a Operand<'tcx>> {
    match rhs {
        Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => Some(operand),
        _ => None,
    }
}

fn plain_operand_local(operand: &Operand<'_>) -> Option<Local> {
    operand.place().and_then(|place| place.as_local())
}

fn collect_retention_facts<'tcx>(
    program: &RustProgram<'tcx>,
    function: LocalDefId,
    argument_index: usize,
    body: &Body<'tcx>,
) -> RetentionBodyFacts {
    let tcx = program.tcx;
    let function_path = tcx.def_path_str(function.to_def_id());
    let root = Local::from_usize(argument_index + 1);
    let mut definitions = vec![0usize; body.local_decls.len()];
    let mut aliases = Vec::<(Local, Local, RetentionStep)>::new();

    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else {
                continue;
            };
            if let Some(destination) = lhs.as_local() {
                definitions[destination.index()] += 1;
                if let Some(source) = transparent_operand(rhs).and_then(plain_operand_local)
                    && matches!(body.local_decls[source].ty.kind(), TyKind::RawPtr(..))
                    && matches!(body.local_decls[destination].ty.kind(), TyKind::RawPtr(..))
                {
                    aliases.push((
                        source,
                        destination,
                        retention_step(
                            location,
                            RetentionEventKind::Transparent,
                            format!("_{}->_{}", source.as_u32(), destination.as_u32()),
                        ),
                    ));
                }
            }
        }
    }

    let mut reachable = BTreeSet::from([root.as_u32()]);
    loop {
        let before = reachable.len();
        for (source, destination, _) in &aliases {
            if reachable.contains(&source.as_u32()) {
                reachable.insert(destination.as_u32());
            }
        }
        if reachable.len() == before {
            break;
        }
    }
    let is_reachable = |local: Local| reachable.contains(&local.as_u32());

    let mut facts = RetentionBodyFacts {
        function,
        function_path,
        argument_index,
        steps: aliases
            .iter()
            .filter(|(source, _, _)| is_reachable(*source))
            .map(|(_, _, step)| step.clone())
            .collect(),
        retains: Vec::new(),
        unknowns: BTreeMap::new(),
        dependencies: Vec::new(),
    };

    for local in body.local_decls.indices() {
        if local != root && is_reachable(local) && definitions[local.index()] > 1 {
            facts
                .unknowns
                .entry(RetentionUnknownReason::MultiDef)
                .or_default()
                .push(RetentionStep {
                    location: "body".to_owned(),
                    kind: RetentionEventKind::MultiDef,
                    detail: format!(
                        "_{} has {} definitions",
                        local.as_u32(),
                        definitions[local.index()]
                    ),
                });
        }
    }

    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else {
                continue;
            };
            if is_reachable(lhs.local) && !lhs.projection.is_empty() {
                facts.steps.push(retention_step(
                    location,
                    RetentionEventKind::DereferenceOnly,
                    format!("access through _{}", lhs.local.as_u32()),
                ));
            }
            let Some(source_place) = transparent_operand(rhs).and_then(Operand::place) else {
                continue;
            };
            if is_reachable(source_place.local) && !source_place.projection.is_empty() {
                facts.steps.push(retention_step(
                    location,
                    RetentionEventKind::DereferenceOnly,
                    format!("read through _{}", source_place.local.as_u32()),
                ));
                continue;
            }
            let Some(source) = source_place.as_local().filter(|local| is_reachable(*local)) else {
                continue;
            };
            if lhs.local == RETURN_PLACE && lhs.projection.is_empty() {
                facts.retains.push(retention_step(
                    location,
                    RetentionEventKind::Return,
                    format!("return _{}", source.as_u32()),
                ));
            } else if !lhs.projection.is_empty() {
                let output_storage = lhs.local.as_usize() > 0
                    && lhs.local.as_usize() <= body.arg_count
                    && matches!(lhs.projection.first(), Some(ProjectionElem::Deref));
                let (reason, kind) = if output_storage {
                    (
                        RetentionUnknownReason::OutputStorage,
                        RetentionEventKind::OutputStorage,
                    )
                } else {
                    (
                        RetentionUnknownReason::FieldOrGlobalStore,
                        RetentionEventKind::FieldOrGlobalStore,
                    )
                };
                let step = retention_step(
                    location,
                    kind,
                    format!("store _{} through _{}", source.as_u32(), lhs.local.as_u32()),
                );
                facts.retains.push(step.clone());
                facts.unknowns.entry(reason).or_default().push(step);
            }
        }

        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        let terminator = data.terminator();
        let (func, args) = match &terminator.kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => (func, args),
            _ => continue,
        };
        for (index, argument) in args.iter().enumerate() {
            let Some(local) = argument.node.place().and_then(|place| place.as_local()) else {
                continue;
            };
            if !is_reachable(local) {
                continue;
            }
            let Some(callee) = operand_callee(func) else {
                let step = retention_step(
                    location,
                    RetentionEventKind::UnknownCall,
                    format!("fn-pointer argument {index}"),
                );
                facts
                    .unknowns
                    .entry(RetentionUnknownReason::FnPtrWeb)
                    .or_default()
                    .push(step.clone());
                facts.steps.push(step);
                continue;
            };
            if let Some(local_callee) = callee
                .as_local()
                .filter(|callee| program.functions.contains(callee))
            {
                let step = retention_step(
                    location,
                    RetentionEventKind::LocalCall,
                    format!("{} arg{index}", tcx.def_path_str(callee)),
                );
                facts.dependencies.push(RetentionDependency {
                    callee: local_callee,
                    argument_index: index,
                    step: step.clone(),
                });
                facts.steps.push(step);
                continue;
            }
            let key = symbol_key(tcx, callee, &program.functions);
            let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
            let source_ty = argument.node.ty(body, tcx);
            let target = sig
                .inputs()
                .get(index)
                .copied()
                .and_then(raw_target_type)
                .or_else(|| sig.c_variadic.then(|| raw_target_type(source_ty)).flatten());
            let Some(target) = target else {
                let step = retention_step(
                    location,
                    RetentionEventKind::UnknownCall,
                    format!("{} arg{index} target-unresolved", key.symbol),
                );
                facts
                    .unknowns
                    .entry(RetentionUnknownReason::CalleeUnresolved)
                    .or_default()
                    .push(step.clone());
                facts.steps.push(step);
                continue;
            };
            match super::raw_boundary_contracts::classify_contract(&key, index, &target) {
                Ok(contract) => {
                    let (kind, detail) = match contract.ownership {
                        super::raw_boundary_contracts::OwnershipContract::Consume => {
                            (RetentionEventKind::Free, "consume")
                        }
                        _ => (RetentionEventKind::KnownNoRetainCall, "no-retain"),
                    };
                    facts.steps.push(retention_step(
                        location,
                        kind,
                        format!("{} arg{index} {detail}", key.symbol),
                    ));
                }
                Err(error) => {
                    let step = retention_step(
                        location,
                        RetentionEventKind::UnknownCall,
                        format!("{} arg{index} {error:?}", key.symbol),
                    );
                    facts
                        .unknowns
                        .entry(RetentionUnknownReason::OpenBoundary)
                        .or_default()
                        .push(step.clone());
                    facts.steps.push(step);
                }
            }
        }
    }

    facts.steps.sort();
    facts.steps.dedup();
    facts.retains.sort();
    facts.retains.dedup();
    for steps in facts.unknowns.values_mut() {
        steps.sort();
        steps.dedup();
    }
    facts.dependencies.sort_by_key(|dependency| {
        (
            dependency.callee.local_def_index.as_u32(),
            dependency.argument_index,
            dependency.step.clone(),
        )
    });
    facts.dependencies.dedup();
    facts
}

fn direct_verdict(facts: &RetentionBodyFacts, attested: bool) -> RetentionVerdict {
    if !attested {
        return RetentionVerdict::Unknown {
            reason: RetentionUnknownReason::AttestationAbsent,
            frontier: facts.steps.clone(),
        };
    }
    if let Some(sink) = facts.retains.first().cloned() {
        return RetentionVerdict::Retains {
            sink: sink.clone(),
            path: vec![sink],
        };
    }
    if let Some((&reason, frontier)) = facts.unknowns.first_key_value() {
        return RetentionVerdict::Unknown {
            reason,
            frontier: frontier.clone(),
        };
    }
    RetentionVerdict::NoRetain {
        certificate: RetentionCertificate {
            function: facts.function_path.clone(),
            argument_index: facts.argument_index,
            steps: facts.steps.clone(),
            attestation: "closed_world_frozen_graph",
        },
    }
}

fn evaluate_retention(
    facts: &FxHashMap<(LocalDefId, usize), RetentionBodyFacts>,
    attested: bool,
) -> FxHashMap<(LocalDefId, usize), RetentionVerdict> {
    let mut rows = facts
        .iter()
        .map(|(&key, facts)| (key, direct_verdict(facts, attested)))
        .collect::<FxHashMap<_, _>>();
    let mut keys = facts.keys().copied().collect::<Vec<_>>();
    keys.sort_by_key(|(function, argument)| (function.local_def_index.as_u32(), *argument));
    for _ in 0..=keys.len() {
        let previous = rows.clone();
        for key in &keys {
            let fact = &facts[key];
            let direct = direct_verdict(fact, attested);
            let next = if matches!(direct, RetentionVerdict::Retains { .. }) {
                direct
            } else if let Some((dependency, sink)) =
                fact.dependencies.iter().find_map(|dependency| {
                    match previous.get(&(dependency.callee, dependency.argument_index)) {
                        Some(RetentionVerdict::Retains { sink, .. }) => {
                            Some((dependency, sink.clone()))
                        }
                        _ => None,
                    }
                })
            {
                RetentionVerdict::Retains {
                    sink: sink.clone(),
                    path: vec![dependency.step.clone(), sink],
                }
            } else if matches!(direct, RetentionVerdict::Unknown { .. }) {
                direct
            } else if let Some(dependency) = fact.dependencies.iter().find(|dependency| {
                !matches!(
                    previous.get(&(dependency.callee, dependency.argument_index)),
                    Some(RetentionVerdict::NoRetain { .. })
                )
            }) {
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::LocalSummaryUnknown,
                    frontier: vec![dependency.step.clone()],
                }
            } else {
                direct
            };
            rows.insert(*key, next);
        }
        if rows == previous {
            break;
        }
    }
    rows
}

impl RetentionSummaries {
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        origins: Option<&OriginSummaries>,
        attestation: Option<WholeProgramAttestation>,
    ) -> Self {
        let attested = attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph);
        let mut facts = FxHashMap::default();
        for &function in &program.functions {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            for argument_index in 0..body.arg_count {
                let local = Local::from_usize(argument_index + 1);
                if !matches!(body.local_decls[local].ty.kind(), TyKind::RawPtr(..)) {
                    continue;
                }
                facts.insert(
                    (function, argument_index),
                    collect_retention_facts(program, function, argument_index, &body),
                );
            }
        }
        let rows = if origins.is_none() {
            facts
                .keys()
                .copied()
                .map(|key| {
                    (
                        key,
                        RetentionVerdict::Unknown {
                            reason: RetentionUnknownReason::AnalysisIncomplete,
                            frontier: Vec::new(),
                        },
                    )
                })
                .collect()
        } else {
            evaluate_retention(&facts, attested)
        };
        Self {
            rows,
            facts,
            attested,
        }
    }

    pub(crate) fn get(
        &self,
        function: LocalDefId,
        argument_index: usize,
    ) -> Option<&RetentionVerdict> {
        self.rows.get(&(function, argument_index))
    }

    pub(crate) fn verify_certificate(
        &self,
        function: LocalDefId,
        argument_index: usize,
        certificate: &RetentionCertificate,
    ) -> Result<(), &'static str> {
        let replay = evaluate_retention(&self.facts, self.attested);
        let sorted_unique = certificate.steps.windows(2).all(|pair| pair[0] < pair[1]);
        match replay.get(&(function, argument_index)) {
            Some(RetentionVerdict::NoRetain {
                certificate: expected,
            }) if expected == certificate && sorted_unique => Ok(()),
            _ => Err("retention-certificate-invalid"),
        }
    }
}

pub(crate) const RAW_BOUNDARY_WAIVER_ID: &str =
    "c-aliasing-semantics-at-unsafe-bridges/v1@2026-09-01";
pub(crate) const RAW_BOUNDARY_WAIVER_TEXT: &str = "C-aliasing semantics at unsafe bridges. At a receipted T2 site, crat may expose a raw pointer derived from a safe reference to a boundary whose retention behavior is unknown, in order to preserve the source program's C calling convention. Current Rust aliasing models can invalidate a retained raw alias when the originating mutable reference remains live or is later reused. The conditional soundness claim therefore excludes an execution that retains and later uses that raw alias unless no-retention is independently established. This waiver licenses only the recorded safe-to-raw view at that call. It licenses no integer-to-pointer round trip, ownership transfer, unchecked null dereference, positive-retention site, or unreceipted reuse.";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BridgeTemplate {
    RefMutToRawMut,
    RefMutToRawConst,
    RefSharedToRawConst,
    SliceMutToRawMut,
    SliceToRawConst,
    OptRefMutToRawMut,
    OptRefToRawConst,
    OptSliceToRaw,
    BoxBorrowViewToRaw,
    KnownFreeDrop,
}

impl BridgeTemplate {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::RefMutToRawMut => "ref-mut-to-raw-mut",
            Self::RefMutToRawConst => "ref-mut-to-raw-const",
            Self::RefSharedToRawConst => "ref-shared-to-raw-const",
            Self::SliceMutToRawMut => "slice-mut-to-raw-mut",
            Self::SliceToRawConst => "slice-to-raw-const",
            Self::OptRefMutToRawMut => "opt-ref-mut-to-raw-mut",
            Self::OptRefToRawConst => "opt-ref-to-raw-const",
            Self::OptSliceToRaw => "opt-slice-to-raw",
            Self::BoxBorrowViewToRaw => "box-borrow-view-to-raw",
            Self::KnownFreeDrop => "known-free-drop",
        }
    }

    pub(crate) fn render(
        self,
        argument: &str,
        target_mutability: RawMutability,
        box_slice: bool,
    ) -> Result<BridgeRender, RawBoundaryBlockReason> {
        self.render_mode(argument, target_mutability, box_slice, false)
    }

    pub(crate) fn render_explicit(
        self,
        argument: &str,
        target_mutability: RawMutability,
        box_slice: bool,
    ) -> Result<BridgeRender, RawBoundaryBlockReason> {
        self.render_mode(argument, target_mutability, box_slice, true)
    }

    fn render_mode(
        self,
        argument: &str,
        target_mutability: RawMutability,
        box_slice: bool,
        force_explicit: bool,
    ) -> Result<BridgeRender, RawBoundaryBlockReason> {
        match self {
            Self::RefMutToRawMut if force_explicit => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_mut(&mut *{argument})"
            ))),
            Self::RefMutToRawConst if force_explicit => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_ref(&*{argument})"
            ))),
            Self::RefSharedToRawConst if force_explicit => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_ref({argument})"
            ))),
            Self::RefMutToRawMut | Self::RefMutToRawConst | Self::RefSharedToRawConst => {
                Ok(BridgeRender::ZeroSyntax)
            }
            Self::SliceMutToRawMut => Ok(BridgeRender::Edit(format!("{argument}.as_mut_ptr()"))),
            Self::SliceToRawConst => Ok(BridgeRender::Edit(format!("{argument}.as_ptr()"))),
            Self::OptRefMutToRawMut => Ok(BridgeRender::Edit(format!(
                "{argument}.as_deref_mut().map_or(core::ptr::null_mut(), core::ptr::from_mut)"
            ))),
            Self::OptRefToRawConst => Ok(BridgeRender::Edit(format!(
                "{argument}.as_deref().map_or(core::ptr::null(), core::ptr::from_ref)"
            ))),
            Self::OptSliceToRaw => Ok(BridgeRender::Edit(match target_mutability {
                RawMutability::Mut => format!(
                    "{argument}.as_deref_mut().map_or(core::ptr::null_mut(), |slice| slice.as_mut_ptr())"
                ),
                RawMutability::Const => format!(
                    "{argument}.as_deref().map_or(core::ptr::null(), |slice| slice.as_ptr())"
                ),
            })),
            Self::BoxBorrowViewToRaw if box_slice => {
                Ok(BridgeRender::Edit(match target_mutability {
                    RawMutability::Mut => format!("{argument}.as_mut_ptr()"),
                    RawMutability::Const => format!("{argument}.as_ptr()"),
                }))
            }
            Self::BoxBorrowViewToRaw => Ok(BridgeRender::Edit(match target_mutability {
                RawMutability::Mut => format!("core::ptr::from_mut({argument}.as_mut())"),
                RawMutability::Const => format!("core::ptr::from_ref({argument}.as_ref())"),
            })),
            Self::KnownFreeDrop => Ok(BridgeRender::Lifecycle),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BridgeRender {
    ZeroSyntax,
    Edit(String),
    Lifecycle,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RawBoundaryBlockReason {
    SiteUnresolved,
    SubjectUnrooted,
    SubjectNotSafe,
    SharedToMut,
    OwnershipTransfer,
    PositiveRetention,
    ContractInvalid,
    TemplateUnavailable,
    WaiverUnconfirmed,
}

impl RawBoundaryBlockReason {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::SiteUnresolved => "raw-boundary-site-unresolved",
            Self::SubjectUnrooted => "raw-boundary-subject-unrooted",
            Self::SubjectNotSafe => "raw-boundary-subject-not-safe",
            Self::SharedToMut => "raw-boundary-shared-to-mut",
            Self::OwnershipTransfer => "raw-boundary-ownership-transfer",
            Self::PositiveRetention => "raw-boundary-positive-retention",
            Self::ContractInvalid => "raw-boundary-contract-invalid",
            Self::TemplateUnavailable => "raw-boundary-template-unavailable",
            Self::WaiverUnconfirmed => "raw-boundary-waiver-unconfirmed",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RawBoundaryDisposition {
    T1 {
        template: BridgeTemplate,
        evidence: String,
    },
    T2 {
        template: BridgeTemplate,
        reason: RetentionUnknownReason,
        waiver_id: &'static str,
    },
    Blocked {
        reason: RawBoundaryBlockReason,
        detail: String,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct RawBoundaryRenderSite {
    pub span: Span,
    pub target: RawTargetType,
    pub box_slice: bool,
    pub source_shape: &'static str,
    pub node: Option<(LocalDefId, HirId)>,
    pub target_stays_raw: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct AddressViewSite {
    pub owner: String,
    pub span: Span,
    pub node: (LocalDefId, HirId),
    pub template: BridgeTemplate,
    pub target: RawTargetType,
    pub op: &'static str,
}

impl RawBoundaryDisposition {
    pub(crate) fn is_open(&self) -> bool {
        matches!(self, Self::T1 { .. } | Self::T2 { .. })
    }

    pub(crate) fn tier(&self) -> &'static str {
        match self {
            Self::T1 { .. } => "t1",
            Self::T2 { .. } => "t2",
            Self::Blocked { .. } => "blocked",
        }
    }

    pub(crate) fn template(&self) -> Option<BridgeTemplate> {
        match self {
            Self::T1 { template, .. } | Self::T2 { template, .. } => Some(*template),
            Self::Blocked { .. } => None,
        }
    }
}

fn template_for(
    decision: &super::Decision,
    target: &RawTargetType,
    ownership: Option<super::raw_boundary_contracts::OwnershipContract>,
) -> Result<BridgeTemplate, RawBoundaryBlockReason> {
    use super::{Decision, box_facts::BoxShape, raw_boundary_contracts::OwnershipContract};

    if matches!(
        ownership,
        Some(OwnershipContract::AtomicSourceSink | OwnershipContract::Produce)
    ) {
        return Err(RawBoundaryBlockReason::OwnershipTransfer);
    }
    match decision {
        Decision::Ref { mutable } | Decision::InferredRef { mutable, .. } => {
            match (*mutable, target.mutability) {
                (true, RawMutability::Mut) => Ok(BridgeTemplate::RefMutToRawMut),
                (true, RawMutability::Const) => Ok(BridgeTemplate::RefMutToRawConst),
                (false, RawMutability::Const) => Ok(BridgeTemplate::RefSharedToRawConst),
                (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
            }
        }
        Decision::Slice { mutable, .. } => match (*mutable, target.mutability) {
            (true, RawMutability::Mut) => Ok(BridgeTemplate::SliceMutToRawMut),
            (_, RawMutability::Const) => Ok(BridgeTemplate::SliceToRawConst),
            (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
        },
        Decision::Opt { mutable, slice, .. } => {
            if *slice {
                match (*mutable, target.mutability) {
                    (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
                    _ => Ok(BridgeTemplate::OptSliceToRaw),
                }
            } else {
                match (*mutable, target.mutability) {
                    (true, RawMutability::Mut) => Ok(BridgeTemplate::OptRefMutToRawMut),
                    (_, RawMutability::Const) => Ok(BridgeTemplate::OptRefToRawConst),
                    (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
                }
            }
        }
        Decision::Box(plan) => {
            if ownership == Some(OwnershipContract::Consume) {
                Ok(BridgeTemplate::KnownFreeDrop)
            } else if plan.shape == BoxShape::Sized || plan.shape == BoxShape::Slice {
                Ok(BridgeTemplate::BoxBorrowViewToRaw)
            } else {
                Err(RawBoundaryBlockReason::TemplateUnavailable)
            }
        }
        Decision::Degraded(_) => Err(RawBoundaryBlockReason::SubjectNotSafe),
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RawBoundaryDispositionIndex {
    by_site: BTreeMap<RawBoundarySiteKey, RawBoundaryDisposition>,
    render_sites: BTreeMap<RawBoundarySiteKey, RawBoundaryRenderSite>,
    site_lookup: Vec<((LocalDefId, HirId), Span, usize, RawBoundarySiteKey)>,
    open_nodes: FxHashSet<(LocalDefId, HirId)>,
    blocked_nodes: FxHashMap<(LocalDefId, HirId), RawBoundaryBlockReason>,
    address_sites: Vec<AddressViewSite>,
}

impl RawBoundaryDispositionIndex {
    pub(crate) fn derive(
        site_facts: &RawBoundarySiteFacts,
        retention: &RetentionSummaries,
        hypothetical: &super::DecisionTable,
        emitability: &super::emitability::EmitabilityFacts,
    ) -> Self {
        let decisions = hypothetical
            .entries
            .iter()
            .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
            .collect::<FxHashMap<_, _>>();
        let mut out = Self::default();
        let mut nodes = FxHashMap::<(LocalDefId, HirId), Vec<bool>>::default();
        for site in &site_facts.sites {
            let disposition: Result<RawBoundaryDisposition, (RawBoundaryBlockReason, String)> =
                (|| {
                    let node = site.node.ok_or_else(|| {
                        (
                            RawBoundaryBlockReason::SubjectUnrooted,
                            "site has no subject root".to_owned(),
                        )
                    })?;
                    let decision = decisions.get(&node).copied().ok_or_else(|| {
                        (
                            RawBoundaryBlockReason::SubjectNotSafe,
                            "hypothetical has no safe subject decision".to_owned(),
                        )
                    })?;
                    let contract = super::raw_boundary_contracts::classify_contract(
                        &site.key.callee,
                        site.key.argument_index,
                        &site.target,
                    );
                    let (retention_verdict, ownership, evidence) =
                        match contract {
                            Ok(contract) => (
                                RetentionVerdict::NoRetain {
                                    certificate: RetentionCertificate {
                                        function: site.key.callee.path.clone(),
                                        argument_index: site.key.argument_index,
                                        steps: Vec::new(),
                                        attestation: "boundary-contract",
                                    },
                                },
                                Some(contract.ownership),
                                format!("contract:{}", contract.provenance),
                            ),
                            Err(
                                super::raw_boundary_contracts::ContractFailure::PositionUnmodeled,
                            ) if site.callee_local.is_none() => (
                                RetentionVerdict::Unknown {
                                    reason: RetentionUnknownReason::OpenBoundary,
                                    frontier: Vec::new(),
                                },
                                None,
                                "foreign-retention-unknown".to_owned(),
                            ),
                            Err(super::raw_boundary_contracts::ContractFailure::NotForeign)
                                if site.callee_local.is_some() =>
                            {
                                let callee = site.callee_local.expect("guarded local callee");
                                (
                                    retention
                                        .get(callee, site.key.argument_index)
                                        .cloned()
                                        .unwrap_or(RetentionVerdict::Unknown {
                                            reason: RetentionUnknownReason::LocalSummaryUnknown,
                                            frontier: Vec::new(),
                                        }),
                                    None,
                                    "local-retention-summary".to_owned(),
                                )
                            }
                            Err(error) => {
                                return Err((
                                    RawBoundaryBlockReason::ContractInvalid,
                                    format!("{error:?}"),
                                ));
                            }
                        };
                    let template = template_for(decision, &site.target, ownership)
                        .map_err(|reason| (reason, "template-preflight".to_owned()))?;
                    match retention_verdict {
                        RetentionVerdict::NoRetain { certificate } => {
                            if site.callee_local.is_some()
                                && retention
                                    .verify_certificate(
                                        site.callee_local.expect("local"),
                                        site.key.argument_index,
                                        &certificate,
                                    )
                                    .is_err()
                            {
                                return Err((
                                    RawBoundaryBlockReason::ContractInvalid,
                                    "retention-certificate-invalid".to_owned(),
                                ));
                            }
                            Ok(RawBoundaryDisposition::T1 { template, evidence })
                        }
                        RetentionVerdict::Retains { sink, .. } => Err((
                            RawBoundaryBlockReason::PositiveRetention,
                            format!("{sink:?}"),
                        )),
                        RetentionVerdict::Unknown { reason, .. } => {
                            Ok(RawBoundaryDisposition::T2 {
                                template,
                                reason,
                                waiver_id: RAW_BOUNDARY_WAIVER_ID,
                            })
                        }
                    }
                })();
            let disposition = disposition.unwrap_or_else(|(reason, detail)| {
                RawBoundaryDisposition::Blocked { reason, detail }
            });
            let box_slice = site
                .node
                .and_then(|node| decisions.get(&node).copied())
                .is_some_and(|decision| {
                    matches!(
                        decision,
                        super::Decision::Box(plan)
                            if plan.shape == super::box_facts::BoxShape::Slice
                    )
                });
            let target_stays_raw = site.callee_local.is_none_or(|callee| {
                hypothetical
                    .entries
                    .iter()
                    .find_map(|(subject, decision)| {
                        let super::SubjectKind::Param { hir_index } = subject.kind else {
                            return None;
                        };
                        (subject.fn_did == callee && hir_index == site.key.argument_index)
                            .then_some(matches!(decision, super::Decision::Degraded(_)))
                    })
                    .unwrap_or(true)
            });
            out.render_sites.insert(
                site.key.clone(),
                RawBoundaryRenderSite {
                    span: site.source_span,
                    target: site.target.clone(),
                    box_slice,
                    source_shape: site.source_shape,
                    node: site.node,
                    target_stays_raw,
                },
            );
            if let Some(node) = site.node {
                nodes.entry(node).or_default().push(disposition.is_open());
                out.site_lookup.push((
                    node,
                    site.source_span.source_callsite(),
                    site.key.argument_index,
                    site.key.clone(),
                ));
                if let RawBoundaryDisposition::Blocked { reason, .. } = &disposition {
                    out.blocked_nodes.entry(node).or_insert(*reason);
                }
            }
            out.by_site.insert(site.key.clone(), disposition);
        }
        for failure in &site_facts.failures {
            if let Some(node) = failure.node {
                nodes.entry(node).or_default().push(false);
                out.blocked_nodes
                    .entry(node)
                    .or_insert(RawBoundaryBlockReason::SiteUnresolved);
            }
        }
        for (node, verdicts) in nodes {
            if !verdicts.is_empty() && verdicts.into_iter().all(|open| open) {
                out.open_nodes.insert(node);
            }
        }
        for observation in &emitability.address_observations {
            if observation.operands.len() != 2
                || !observation
                    .operands
                    .iter()
                    .all(|operand| out.open_nodes.contains(&operand.node))
            {
                continue;
            }
            for operand in &observation.operands {
                let Some(decision) = decisions.get(&operand.node).copied() else {
                    continue;
                };
                let target = RawTargetType {
                    rendered: "*const _".to_owned(),
                    pointee: "_".to_owned(),
                    mutability: RawMutability::Const,
                };
                let Ok(template) = template_for(decision, &target, None) else {
                    continue;
                };
                out.address_sites.push(AddressViewSite {
                    owner: site_facts
                        .sites
                        .iter()
                        .find(|site| site.node == Some(operand.node))
                        .map_or_else(
                            || observation.owner.local_def_index.as_u32().to_string(),
                            |site| site.key.caller.clone(),
                        ),
                    span: operand.span,
                    node: operand.node,
                    template,
                    target,
                    op: observation.op,
                });
            }
        }
        out.address_sites.sort_by_key(|site| {
            (
                site.node.0.local_def_index.as_u32(),
                site.node.1.local_id.as_u32(),
                site.span.lo(),
                site.span.hi(),
            )
        });
        out.site_lookup.sort_by(|left, right| {
            (
                left.0.0.local_def_index.as_u32(),
                left.0.1.local_id.as_u32(),
                left.1.lo(),
                left.1.hi(),
                left.2,
                &left.3,
            )
                .cmp(&(
                    right.0.0.local_def_index.as_u32(),
                    right.0.1.local_id.as_u32(),
                    right.1.lo(),
                    right.1.hi(),
                    right.2,
                    &right.3,
                ))
        });
        out
    }

    pub(crate) fn disposition(&self, key: &RawBoundarySiteKey) -> Option<&RawBoundaryDisposition> {
        self.by_site.get(key)
    }

    pub(crate) fn emission_sites(
        &self,
    ) -> impl Iterator<
        Item = (
            &RawBoundarySiteKey,
            &RawBoundaryDisposition,
            &RawBoundaryRenderSite,
        ),
    > {
        self.by_site.iter().filter_map(|(key, disposition)| {
            self.render_sites
                .get(key)
                .filter(|site| site.target_stays_raw)
                .map(|site| (key, disposition, site))
        })
    }

    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from(
            "caller\tblock\tstatement_index\tcallee\targument_index\tsubject\ttier\ttemplate\twaiver_id\tevidence\treason\tdetail\n",
        );
        for (key, disposition) in &self.by_site {
            let (template, waiver, evidence, reason, detail) = match disposition {
                RawBoundaryDisposition::T1 { template, evidence } => {
                    (template.key(), "-", evidence.as_str(), "-", "-")
                }
                RawBoundaryDisposition::T2 {
                    template,
                    reason,
                    waiver_id,
                } => (
                    template.key(),
                    *waiver_id,
                    "retention-unknown",
                    reason.key(),
                    "-",
                ),
                RawBoundaryDisposition::Blocked { reason, detail } => {
                    ("-", "-", "-", reason.key(), detail.as_str())
                }
            };
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                key.caller,
                key.block,
                key.statement_index,
                key.callee.path,
                key.argument_index,
                key.subject,
                disposition.tier(),
                template,
                waiver,
                evidence,
                reason,
                detail,
            ));
        }
        out
    }

    pub(crate) fn address_sites(&self) -> &[AddressViewSite] {
        &self.address_sites
    }

    /// Exact site atoms grouped by the subject whose safe declaration and use
    /// edits they jointly justify. Every consumer receives the already-sorted
    /// group; none reconstructs dependency closure from rendered text.
    pub(crate) fn subject_atom_groups(
        &self,
    ) -> FxHashMap<(LocalDefId, HirId), Vec<SubjectAtomKey>> {
        let mut groups = FxHashMap::<(LocalDefId, HirId), Vec<SubjectAtomKey>>::default();
        for (key, disposition) in &self.by_site {
            if !disposition.is_open() {
                continue;
            }
            let Some(site) = self
                .render_sites
                .get(key)
                .filter(|site| site.target_stays_raw)
            else {
                continue;
            };
            let Some(node) = site.node else {
                continue;
            };
            groups.entry(node).or_default().push(SubjectAtomKey {
                id: site_atom_id(key),
                node,
                owner: key.caller.clone(),
            });
        }
        for site in &self.address_sites {
            groups.entry(site.node).or_default().push(SubjectAtomKey {
                id: address_atom_id(site),
                node: site.node,
                owner: site.owner.clone(),
            });
        }
        for atoms in groups.values_mut() {
            atoms.sort_by(|left, right| left.id.cmp(&right.id));
            atoms.dedup_by(|left, right| left.id == right.id);
        }
        groups
    }

    pub(crate) fn opens_node(&self, node: (LocalDefId, HirId)) -> bool {
        self.open_nodes.contains(&node)
    }

    pub(crate) fn opens_span(&self, node: (LocalDefId, HirId), span: Span) -> bool {
        let span = span.source_callsite();
        self.opens_node(node)
            && self
                .site_lookup
                .iter()
                .any(|(candidate, site_span, _, key)| {
                    *candidate == node
                        && (site_span.contains(span) || span.contains(*site_span))
                        && self
                            .by_site
                            .get(key)
                            .is_some_and(RawBoundaryDisposition::is_open)
                })
    }

    pub(crate) fn opens_argument(
        &self,
        node: (LocalDefId, HirId),
        span: Span,
        argument_index: usize,
    ) -> bool {
        let span = span.source_callsite();
        self.opens_node(node)
            && self
                .site_lookup
                .iter()
                .any(|(candidate, site_span, index, key)| {
                    *candidate == node
                        && *index == argument_index
                        && (site_span.contains(span) || span.contains(*site_span))
                        && self
                            .by_site
                            .get(key)
                            .is_some_and(RawBoundaryDisposition::is_open)
                })
    }

    pub(crate) fn block_reason(&self, node: (LocalDefId, HirId)) -> Option<RawBoundaryBlockReason> {
        self.blocked_nodes.get(&node).copied()
    }
}

/// Select the one MIR call which represents an already-resolved HIR call site.
/// Zero and multiple matches stay typed rather than choosing by traversal
/// order.
pub(crate) fn select_unique_site(
    expected: &ForeignSymbolKey,
    candidates: &[MirCallCandidate],
) -> Result<(u32, u32), SiteMatchFailure> {
    let mut matching = candidates.iter().filter(|site| site.callee == *expected);
    let Some(site) = matching.next() else {
        return Err(if candidates.is_empty() {
            SiteMatchFailure::Missing
        } else {
            SiteMatchFailure::CalleeMismatch
        });
    };
    if matching.next().is_some() {
        return Err(SiteMatchFailure::Ambiguous);
    }
    Ok((site.block, site.statement_index))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn retention_of(
        src: &str,
        function_suffix: &str,
        attestation: Option<WholeProgramAttestation>,
    ) -> (RetentionVerdict, Result<(), &'static str>) {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|function| {
                    tcx.def_path_str(function.to_def_id())
                        .ends_with(function_suffix)
                })
                .expect("fixture function");
            let summaries = RetentionSummaries::derive(&program, Some(&origins), attestation);
            let verdict = summaries
                .get(function, 0)
                .expect("argument summary")
                .clone();
            let verification = match &verdict {
                RetentionVerdict::NoRetain { certificate } => {
                    summaries.verify_certificate(function, 0, certificate)
                }
                _ => Err("not-a-certificate"),
            };
            (verdict, verification)
        })
        .expect("fixture compiles")
    }

    fn symbol(name: &str, foreign: bool) -> ForeignSymbolKey {
        ForeignSymbolKey {
            symbol: name.to_owned(),
            path: format!("fixture::{name}"),
            abi: "C".to_owned(),
            signature: "(*mut i32)->()".to_owned(),
            foreign,
        }
    }

    #[test]
    fn rb_x1_exact_single_call_candidate_builds_owned_key() {
        let expected = symbol("consume", true);
        let site = select_unique_site(
            &expected,
            &[MirCallCandidate {
                block: 7,
                statement_index: 3,
                callee: expected.clone(),
            }],
        );
        assert_eq!(site, Ok((7, 3)));
    }

    #[test]
    fn rb_x1_zero_or_multiple_candidates_fail_closed() {
        let expected = symbol("consume", true);
        assert_eq!(
            select_unique_site(&expected, &[]),
            Err(SiteMatchFailure::Missing)
        );
        let one = MirCallCandidate {
            block: 1,
            statement_index: 0,
            callee: expected.clone(),
        };
        assert_eq!(
            select_unique_site(&expected, &[one.clone(), one]),
            Err(SiteMatchFailure::Ambiguous)
        );
    }

    #[test]
    fn rb_x1_same_spelled_local_is_not_the_foreign_site() {
        let expected = symbol("consume", true);
        let local = symbol("consume", false);
        assert_eq!(
            select_unique_site(
                &expected,
                &[MirCallCandidate {
                    block: 2,
                    statement_index: 1,
                    callee: local,
                }],
            ),
            Err(SiteMatchFailure::CalleeMismatch)
        );
    }

    #[test]
    fn rb_x1_target_mutability_is_not_collapsed() {
        assert_ne!(RawMutability::Const, RawMutability::Mut);
    }

    #[test]
    fn rb_x1_foreign_argument_fact_carries_callee_position_and_target_type() {
        let src = r#"
            extern "C" { fn consume(p: *mut i32); }
            unsafe fn caller(p: *mut i32) { consume(p); }
        "#;
        let fact = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::super::emitability::collect(tcx, &program.functions);
            assert_eq!(
                facts.foreign_call_args.len(),
                1,
                "{:#?}",
                facts.foreign_call_args
            );
            facts.foreign_call_args[0].clone()
        })
        .expect("fixture compiles");
        assert_eq!(fact.callee.symbol, "consume");
        assert!(fact.callee.foreign);
        assert_eq!(fact.argument_index, 0);
        assert_eq!(fact.shape, "bare-local");
        assert_eq!(fact.target.mutability, RawMutability::Mut);
        assert!(fact.target.pointee.contains("i32"), "{fact:#?}");
    }

    #[test]
    fn rb_x1_derived_foreign_site_has_the_exact_mir_location() {
        let src = r#"
            extern "C" { fn consume(p: *mut i32); }
            unsafe fn caller(p: *mut i32) { consume(p); }
        "#;
        let sites = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::super::emitability::collect(tcx, &program.functions);
            RawBoundarySiteFacts::derive(&program, &facts)
        })
        .expect("fixture compiles");
        assert!(sites.failures.is_empty(), "{sites:#?}");
        assert_eq!(sites.sites.len(), 1, "{sites:#?}");
        let site = &sites.sites[0];
        assert_eq!(site.key.argument_index, 0);
        assert_eq!(site.key.callee.symbol, "consume");
        assert_eq!(site.target.mutability, RawMutability::Mut);
        assert_eq!(sites.to_tsv(), sites.clone().to_tsv());
    }

    #[test]
    fn rb_x1_direct_local_call_uses_the_same_owned_site_domain() {
        let src = r#"
            unsafe fn consume(p: *mut i32) { *p = 1; }
            unsafe fn caller(p: *mut i32) { consume(p); }
        "#;
        let sites = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::super::emitability::collect(tcx, &program.functions);
            RawBoundarySiteFacts::derive(&program, &facts)
        })
        .expect("fixture compiles");
        assert!(sites.failures.is_empty(), "{sites:#?}");
        assert_eq!(sites.sites.len(), 1, "{sites:#?}");
        assert!(!sites.sites[0].key.callee.foreign);
        assert_eq!(sites.sites[0].key.argument_index, 0);
    }

    #[test]
    fn rb_x1_variadic_raw_argument_keeps_its_position_and_contract() {
        let src = r#"
            extern "C" { fn printf(fmt: *const i8, ...) -> i32; }
            unsafe fn caller(fmt: *const i8, p: *const i8) { printf(fmt, p); }
        "#;
        let facts = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            super::super::emitability::collect(tcx, &program.functions).foreign_call_args
        })
        .expect("fixture compiles");
        assert_eq!(facts.len(), 2, "{facts:#?}");
        assert_eq!(facts[1].argument_index, 1);
        assert_eq!(
            super::super::raw_boundary_contracts::classify_contract(
                &facts[1].callee,
                facts[1].argument_index,
                &facts[1].target,
            )
            .expect("printf vararg contract")
            .retention,
            super::super::raw_boundary_contracts::RetentionContract::NoRetain
        );
    }

    #[test]
    fn rb_w2_local_pointee_access_without_escape_has_a_verified_certificate() {
        let (verdict, verification) = retention_of(
            "unsafe fn no_retain(p: *mut i32) { let _ = *p; *p = 1; }",
            "no_retain",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(verdict, RetentionVerdict::NoRetain { .. }),
            "{verdict:#?}"
        );
        assert_eq!(verification, Ok(()));
    }

    #[test]
    fn rb_w3_returned_pointer_is_positive_retention() {
        let (verdict, _) = retention_of(
            "unsafe fn returns(p: *mut i32) -> *mut i32 { p }",
            "returns",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Retains {
                    sink: RetentionStep {
                        kind: RetentionEventKind::Return,
                        ..
                    },
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_w10_missing_attestation_is_typed_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn no_retain(p: *mut i32) { let _ = *p; }",
            "no_retain",
            None,
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::AttestationAbsent,
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_n1_multi_definition_alias_is_typed_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn branch(p: *mut i32, q: *mut i32, flag: bool) { let mut x = p; if flag { x = q; } let _ = *x; }",
            "branch",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::MultiDef,
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_n2_function_pointer_call_is_typed_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn indirect(p: *mut i32, cb: unsafe fn(*mut i32)) { cb(p); }",
            "indirect",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::FnPtrWeb,
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_n3_positive_retention_never_collapses_to_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn returns(p: *mut i32) -> *mut i32 { p }",
            "returns",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(verdict, RetentionVerdict::Retains { .. }),
            "{verdict:#?}"
        );
    }

    #[test]
    fn retention_unknown_reason_vocabulary_is_exact_and_exhaustive() {
        assert_eq!(
            RetentionUnknownReason::ALL.map(RetentionUnknownReason::key),
            [
                "retention-callee-unresolved",
                "retention-fnptr-web",
                "retention-open-boundary",
                "retention-multi-def",
                "retention-nontransparent-def",
                "retention-projection-ambiguous",
                "retention-output-storage",
                "retention-field-or-global-store",
                "retention-return",
                "retention-local-summary-unknown",
                "retention-attestation-absent",
                "retention-analysis-incomplete",
            ]
        );
    }

    #[test]
    fn local_no_retain_summary_propagates_to_its_caller() {
        let (verdict, verification) = retention_of(
            "unsafe fn leaf(p: *mut i32) { *p = 1; } unsafe fn wrapper(p: *mut i32) { leaf(p); }",
            "wrapper",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(verdict, RetentionVerdict::NoRetain { .. }),
            "{verdict:#?}"
        );
        assert_eq!(verification, Ok(()));
    }

    #[test]
    fn rb_w5_optional_mutable_ref_bridge_is_one_evaluation_without_unwrap() {
        let rendered = BridgeTemplate::OptRefMutToRawMut
            .render("p", RawMutability::Mut, false)
            .expect("optional bridge");
        let BridgeRender::Edit(text) = rendered else {
            panic!("expected edit, got {rendered:?}");
        };
        assert_eq!(text.matches("p.").count(), 1, "{text}");
        assert!(text.contains("as_deref_mut"), "{text}");
        assert!(!text.contains("unwrap"), "{text}");
    }

    #[test]
    fn rb_w6_shared_source_to_mutable_target_is_typed_block() {
        let target = RawTargetType {
            rendered: "*mut i32".to_owned(),
            pointee: "i32".to_owned(),
            mutability: RawMutability::Mut,
        };
        assert_eq!(
            template_for(
                &super::super::Decision::Ref { mutable: false },
                &target,
                None,
            ),
            Err(RawBoundaryBlockReason::SharedToMut)
        );
        assert_eq!(
            RawBoundaryBlockReason::SharedToMut.key(),
            "raw-boundary-shared-to-mut"
        );
    }

    #[test]
    fn rb_w7_box_borrow_view_does_not_consume_the_owner() {
        let rendered = BridgeTemplate::BoxBorrowViewToRaw
            .render("owner", RawMutability::Mut, false)
            .expect("Box view");
        let BridgeRender::Edit(text) = rendered else {
            panic!("expected edit, got {rendered:?}");
        };
        assert_eq!(text, "core::ptr::from_mut(owner.as_mut())");
        assert!(!text.contains("into_raw"), "{text}");
    }

    #[test]
    fn rb_w8_known_free_uses_the_existing_lifecycle_path() {
        assert_eq!(
            BridgeTemplate::KnownFreeDrop
                .render("owner", RawMutability::Mut, false)
                .expect("lifecycle"),
            BridgeRender::Lifecycle
        );
    }

    #[test]
    fn zero_syntax_ref_bridge_is_receipted_without_an_edit() {
        assert_eq!(
            BridgeTemplate::RefMutToRawMut
                .render("p", RawMutability::Mut, false)
                .expect("zero syntax"),
            BridgeRender::ZeroSyntax
        );
    }
}
