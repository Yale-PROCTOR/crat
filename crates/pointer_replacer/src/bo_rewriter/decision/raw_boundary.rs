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

pub(crate) fn site_atom_id(key: &RawBoundarySiteKey) -> String {
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
    pub depth2: Option<Depth2Target>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Depth2Target {
    pub inner_pointee: String,
    pub inner_mutability: RawMutability,
    pub thin: bool,
}

impl RawTargetType {
    pub(crate) fn is_void_pointee(&self) -> bool {
        self.pointee.rsplit("::").next() == Some("c_void")
    }
}

pub(crate) fn raw_target_type(ty: Ty<'_>) -> Option<RawTargetType> {
    let TyKind::RawPtr(pointee, mutability) = ty.kind() else {
        return None;
    };
    let depth2 = match pointee.kind() {
        TyKind::RawPtr(inner_pointee, inner_mutability) => Some(Depth2Target {
            inner_pointee: format!("{inner_pointee:?}"),
            inner_mutability: if inner_mutability.is_mut() {
                RawMutability::Mut
            } else {
                RawMutability::Const
            },
            thin: !matches!(
                inner_pointee.kind(),
                TyKind::Slice(_)
                    | TyKind::Str
                    | TyKind::Dynamic(..)
                    | TyKind::Foreign(..)
                    | TyKind::Param(_)
                    | TyKind::Alias(..)
                    | TyKind::Bound(..)
                    | TyKind::Placeholder(_)
                    | TyKind::Infer(_)
                    | TyKind::Error(_)
            ),
        }),
        _ => None,
    };
    Some(RawTargetType {
        rendered: format!("{ty:?}"),
        pointee: format!("{pointee:?}"),
        mutability: if mutability.is_mut() {
            RawMutability::Mut
        } else {
            RawMutability::Const
        },
        depth2,
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
    pub direct_storage: Option<(HirId, Span)>,
    pub adapter_operand_span: Span,
    pub adapter_operand_mutability: Option<RawMutability>,
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
    pub call_span: Span,
    pub source_site: String,
    pub source_shape: &'static str,
    pub source_type: String,
    pub target: RawTargetType,
    pub direct_storage_span: Option<Span>,
    pub adapter_operand_span: Span,
    pub adapter_operand_mutability: Option<RawMutability>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFailure {
    pub caller: String,
    pub node: Option<(LocalDefId, HirId)>,
    pub callee: ForeignSymbolKey,
    pub argument_index: usize,
    pub source_span: Span,
    pub source_site: String,
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
                            .direct_storage
                            .map(|(storage, _)| storage)
                            .or(fact.root)
                            .map_or_else(|| "<unrooted>".to_owned(), |root| format!("{root:?}")),
                    },
                    node: fact
                        .direct_storage
                        .map(|(storage, _)| (fact.caller, storage))
                        .or_else(|| fact.root.map(|root| (fact.caller, root))),
                    callee_local: None,
                    direction: BoundaryDirection::OutgoingArgument,
                    source_span: fact.argument_span,
                    call_span: fact.call_span,
                    source_site: tcx
                        .sess
                        .source_map()
                        .span_to_diagnostic_string(fact.argument_span),
                    source_shape: fact.shape,
                    source_type: fact.source_type.clone(),
                    target: fact.target.clone(),
                    direct_storage_span: fact.direct_storage.map(|(_, span)| span),
                    adapter_operand_span: fact.adapter_operand_span,
                    adapter_operand_mutability: fact.adapter_operand_mutability,
                }),
                Err(reason) => out.failures.push(RawBoundarySiteFailure {
                    caller: tcx.def_path_str(fact.caller.to_def_id()),
                    node: fact
                        .direct_storage
                        .map(|(storage, _)| (fact.caller, storage))
                        .or_else(|| fact.root.map(|root| (fact.caller, root))),
                    callee: fact.callee.clone(),
                    argument_index: fact.argument_index,
                    source_span: fact.argument_span,
                    source_site: tcx
                        .sess
                        .source_map()
                        .span_to_diagnostic_string(fact.argument_span),
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
                                subject: argument
                                    .direct_storage
                                    .map(|(storage, _)| storage)
                                    .or_else(|| argument.shape.place_root())
                                    .map_or_else(
                                        || "<unrooted>".to_owned(),
                                        |root| format!("{root:?}"),
                                    ),
                            },
                            node: argument
                                .direct_storage
                                .map(|(storage, _)| (call.caller, storage))
                                .or_else(|| {
                                    argument.shape.place_root().map(|root| (call.caller, root))
                                }),
                            callee_local: Some(callee),
                            direction: BoundaryDirection::OutgoingArgument,
                            source_span: argument.span,
                            call_span: call.span,
                            source_site: tcx
                                .sess
                                .source_map()
                                .span_to_diagnostic_string(argument.span),
                            source_shape: argument.shape.key(),
                            source_type: argument.source_type.clone(),
                            target,
                            direct_storage_span: argument.direct_storage.map(|(_, span)| span),
                            adapter_operand_span: argument.adapter_operand_span,
                            adapter_operand_mutability: argument.adapter_operand_mutability,
                        }),
                        Err(reason) => out.failures.push(RawBoundarySiteFailure {
                            caller: tcx.def_path_str(call.caller.to_def_id()),
                            node: argument
                                .direct_storage
                                .map(|(storage, _)| (call.caller, storage))
                                .or_else(|| {
                                    argument.shape.place_root().map(|root| (call.caller, root))
                                }),
                            callee: callee_key.clone(),
                            argument_index: argument.index,
                            source_span: argument.span,
                            source_site: tcx
                                .sess
                                .source_map()
                                .span_to_diagnostic_string(argument.span),
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
            "status\tcaller\tblock\tstatement_index\tcallee_path\tcallee_symbol\tforeign\tabi\tsignature\targument_index\tsubject\tsource_site\tsource_lo\tsource_hi\tsource_shape\tsource_type\ttarget_type\ttarget_pointee\ttarget_mutability\treason\n",
        );
        for site in &self.sites {
            out.push_str(&format!(
                "site\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t-\n",
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
                site.source_site,
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
                "failure\t{}\t-\t-\t{}\t{}\t{}\t{}\t{}\t{}\t-\t{}\t{}\t{}\t-\t-\t-\t-\t-\t{}\n",
                failure.caller,
                failure.callee.path,
                failure.callee.symbol,
                u8::from(failure.callee.foreign),
                failure.callee.abi,
                failure.callee.signature,
                failure.argument_index,
                failure.source_site,
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

    pub(crate) fn to_tsv(&self) -> String {
        let mut keys = self.rows.keys().copied().collect::<Vec<_>>();
        keys.sort_by_key(|(function, argument)| (function.local_def_index.as_u32(), *argument));
        let mut out = String::from(
            "function\tlocal_def_index\targument_index\tverdict\treason\tpath_or_frontier\tattested\n",
        );
        for key in keys {
            let facts = self.facts.get(&key);
            let function = facts.map_or("<missing>", |facts| facts.function_path.as_str());
            let (verdict, reason, steps) = match &self.rows[&key] {
                RetentionVerdict::NoRetain { certificate } => (
                    "no-retain",
                    "-",
                    certificate
                        .steps
                        .iter()
                        .map(|step| format!("{}:{:?}:{}", step.location, step.kind, step.detail))
                        .collect::<Vec<_>>()
                        .join(";"),
                ),
                RetentionVerdict::Retains { sink, path } => (
                    "retains",
                    "positive-retention",
                    path.iter()
                        .chain(std::iter::once(sink))
                        .map(|step| format!("{}:{:?}:{}", step.location, step.kind, step.detail))
                        .collect::<Vec<_>>()
                        .join(";"),
                ),
                RetentionVerdict::Unknown { reason, frontier } => (
                    "unknown",
                    reason.key(),
                    frontier
                        .iter()
                        .map(|step| format!("{}:{:?}:{}", step.location, step.kind, step.detail))
                        .collect::<Vec<_>>()
                        .join(";"),
                ),
            };
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                function,
                key.0.local_def_index.as_u32(),
                key.1,
                verdict,
                reason,
                if steps.is_empty() { "-" } else { &steps },
                u8::from(self.attested),
            ));
        }
        out
    }
}

pub(crate) const RAW_BOUNDARY_WAIVER_ID: &str =
    "c-aliasing-semantics-at-unsafe-bridges/v1@2026-09-01";
pub(crate) const RAW_BOUNDARY_WAIVER_TEXT: &str = "C-aliasing semantics at unsafe bridges. At a receipted T2 site, crat may expose a raw pointer derived from a safe reference to a boundary whose retention behavior is unknown, in order to preserve the source program's C calling convention. Current Rust aliasing models can invalidate a retained raw alias when the originating mutable reference remains live or is later reused. The conditional soundness claim therefore excludes an execution that retains and later uses that raw alias unless no-retention is independently established. This waiver licenses only the recorded safe-to-raw view at that call. It licenses no integer-to-pointer round trip, ownership transfer, unchecked null dereference, positive-retention site, or unreceipted reuse.";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BridgeTemplate {
    Depth2NpoConst,
    Depth2NpoMut,
    VoidFromMut,
    VoidFromRef,
    VoidFromMutAsConst,
    RawCastMut,
    RawCastConst,
    RefMutToRawMut,
    RefMutToRawConst,
    RefSharedToRawConst,
    RefSharedToRawMut,
    SliceMutToRawMut,
    SliceToRawConst,
    SliceToRawMut,
    OptRefMutToRawMut,
    OptRefToRawConst,
    OptRefToRawMut,
    OptSliceToRaw,
    OptSliceToRawMut,
    BoxBorrowViewToRaw,
    KnownFreeDrop,
}

impl BridgeTemplate {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::Depth2NpoConst | Self::Depth2NpoMut => "depth2-npo-bridge",
            Self::VoidFromMut | Self::VoidFromRef | Self::VoidFromMutAsConst => "void-generic-raw",
            Self::RawCastMut => "raw-cast-mut",
            Self::RawCastConst => "raw-cast-const",
            Self::RefMutToRawMut => "ref-mut-to-raw-mut",
            Self::RefMutToRawConst => "ref-mut-to-raw-const",
            Self::RefSharedToRawConst => "ref-shared-to-raw-const",
            Self::RefSharedToRawMut => "ref-shared-to-raw-mut",
            Self::SliceMutToRawMut => "slice-mut-to-raw-mut",
            Self::SliceToRawConst => "slice-to-raw-const",
            Self::SliceToRawMut => "slice-to-raw-mut",
            Self::OptRefMutToRawMut
            | Self::OptRefToRawConst
            | Self::OptRefToRawMut
            | Self::OptSliceToRaw
            | Self::OptSliceToRawMut => "option-to-raw-null-map",
            Self::BoxBorrowViewToRaw => "box-borrow-view-to-raw",
            Self::KnownFreeDrop => "known-free-drop",
        }
    }

    pub(crate) fn render(
        self,
        argument: &str,
        target_mutability: RawMutability,
        box_slice: bool,
        cast_pointee: Option<&str>,
    ) -> Result<BridgeRender, RawBoundaryBlockReason> {
        self.render_mode(argument, target_mutability, box_slice, cast_pointee, false)
    }

    pub(crate) fn render_explicit(
        self,
        argument: &str,
        target_mutability: RawMutability,
        box_slice: bool,
        cast_pointee: Option<&str>,
    ) -> Result<BridgeRender, RawBoundaryBlockReason> {
        self.render_mode(argument, target_mutability, box_slice, cast_pointee, true)
    }

    fn render_mode(
        self,
        argument: &str,
        target_mutability: RawMutability,
        box_slice: bool,
        cast_pointee: Option<&str>,
        force_explicit: bool,
    ) -> Result<BridgeRender, RawBoundaryBlockReason> {
        match self {
            Self::Depth2NpoConst | Self::Depth2NpoMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                let inner = if self == Self::Depth2NpoMut {
                    "mut"
                } else {
                    "const"
                };
                Ok(BridgeRender::Edit(format!(
                    "core::ptr::from_mut(&mut {argument}).cast::<*{inner} {pointee}>()"
                )))
            }
            Self::VoidFromMut | Self::VoidFromRef | Self::VoidFromMutAsConst => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                let source = match self {
                    Self::VoidFromMut => format!("core::ptr::from_mut({argument})"),
                    Self::VoidFromRef => format!("core::ptr::from_ref({argument})"),
                    Self::VoidFromMutAsConst => {
                        format!("core::ptr::from_ref(&*{argument})")
                    }
                    _ => unreachable!(),
                };
                Ok(BridgeRender::Edit(format!("{source}.cast::<{pointee}>()")))
            }
            Self::RawCastMut => Ok(BridgeRender::Edit(format!("{argument}.cast_mut()"))),
            Self::RawCastConst => Ok(BridgeRender::Edit(format!("{argument}.cast_const()"))),
            Self::RefMutToRawMut if force_explicit => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_mut(&mut *{argument})"
            ))),
            Self::RefMutToRawConst if force_explicit => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_ref(&*{argument})"
            ))),
            Self::RefSharedToRawConst if force_explicit => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_ref({argument})"
            ))),
            Self::RefSharedToRawMut => Ok(BridgeRender::Edit(format!(
                "core::ptr::from_ref({argument}).cast_mut()"
            ))),
            Self::RefMutToRawMut | Self::RefMutToRawConst | Self::RefSharedToRawConst => {
                Ok(BridgeRender::ZeroSyntax)
            }
            Self::SliceMutToRawMut => Ok(BridgeRender::Edit(format!("{argument}.as_mut_ptr()"))),
            Self::SliceToRawConst => Ok(BridgeRender::Edit(format!("{argument}.as_ptr()"))),
            Self::SliceToRawMut => Ok(BridgeRender::Edit(format!(
                "{argument}.as_ptr().cast_mut()"
            ))),
            Self::OptRefMutToRawMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), core::ptr::from_mut)"
                )))
            }
            Self::OptRefToRawConst => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null::<{pointee}>(), core::ptr::from_ref)"
                )))
            }
            Self::OptRefToRawMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null_mut::<{pointee}>(), |value| core::ptr::from_ref(value).cast_mut())"
                )))
            }
            Self::OptSliceToRaw => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(match target_mutability {
                    RawMutability::Mut => format!(
                        "{argument}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_mut_ptr())"
                    ),
                    RawMutability::Const => format!(
                        "{argument}.as_deref().map_or(core::ptr::null::<{pointee}>(), |slice| slice.as_ptr())"
                    ),
                }))
            }
            Self::OptSliceToRawMut => {
                let pointee = cast_pointee.ok_or(RawBoundaryBlockReason::TemplateUnavailable)?;
                Ok(BridgeRender::Edit(format!(
                    "{argument}.as_deref().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_ptr().cast_mut())"
                )))
            }
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
    Depth2FatLayout,
    Depth2StorageShape,
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
            Self::Depth2FatLayout => "depth2-fat-layout-incompatible",
            Self::Depth2StorageShape => "depth2-storage-shape-held",
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
    /// Another accepted emitter owns this exact site. It discharges the
    /// boundary obligation without creating an Arm-A edit or atom.
    OwnedByOtherArm {
        owner: &'static str,
        reason: &'static str,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct RawBoundaryRenderSite {
    pub span: Span,
    pub direct_storage_span: Option<Span>,
    pub adapter_operand_span: Span,
    pub call_span: Span,
    pub target: RawTargetType,
    pub box_slice: bool,
    pub source_shape: &'static str,
    pub source_site: String,
    pub node: Option<(LocalDefId, HirId)>,
    pub callee_local: Option<LocalDefId>,
    pub target_stays_raw: bool,
    pub subject_identity: String,
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
        match self {
            Self::T1 { .. } | Self::T2 { .. } => true,
            Self::Blocked { .. } | Self::OwnedByOtherArm { .. } => false,
        }
    }

    fn is_handled(&self) -> bool {
        match self {
            Self::T1 { .. } | Self::T2 { .. } | Self::OwnedByOtherArm { .. } => true,
            Self::Blocked { .. } => false,
        }
    }

    pub(crate) fn tier(&self) -> &'static str {
        match self {
            Self::T1 { .. } => "T1",
            Self::T2 { .. } => "T2",
            Self::Blocked { .. } => "blocked",
            Self::OwnedByOtherArm { owner: "box", .. } => "owned-by-box",
            Self::OwnedByOtherArm { .. } => "owned-by-other-arm",
        }
    }

    pub(crate) fn template(&self) -> Option<BridgeTemplate> {
        match self {
            Self::T1 { template, .. } | Self::T2 { template, .. } => Some(*template),
            Self::Blocked { .. } | Self::OwnedByOtherArm { .. } => None,
        }
    }
}

fn box_site_owner(
    decision: &super::Decision,
    site: &RawBoundarySiteFact,
) -> Option<(&'static str, &'static str)> {
    let plan = match decision {
        super::Decision::Box(plan) => plan,
        super::Decision::Ref { .. }
        | super::Decision::InferredRef { .. }
        | super::Decision::Slice { .. }
        | super::Decision::Opt { .. }
        | super::Decision::Degraded(_) => return None,
    };
    let site_span = site.source_span.source_callsite();
    if plan
        .delete_statements
        .iter()
        .any(|span| span.source_callsite().contains(site_span))
    {
        return Some(("box", "box-initializer-consumed"));
    }
    plan.expr_edits.iter().find_map(|edit| {
        edit.span.source_callsite().contains(site_span).then_some((
            "box",
            match edit.receipt {
                "c-free-site-drop" => "box-lifecycle-owned",
                "realloc-atomic" => "box-realloc-owned",
                _ => "box-construction-owned",
            },
        ))
    })
}

pub(crate) fn template_for(
    decision: &super::Decision,
    target: &RawTargetType,
    ownership: Option<super::raw_boundary_contracts::OwnershipContract>,
    permits_shared_to_mut: bool,
) -> Result<BridgeTemplate, RawBoundaryBlockReason> {
    use super::{Decision, box_facts::BoxShape, raw_boundary_contracts::OwnershipContract};

    if matches!(
        ownership,
        Some(OwnershipContract::AtomicSourceSink | OwnershipContract::Produce)
    ) {
        return Err(RawBoundaryBlockReason::OwnershipTransfer);
    }
    if let Some(depth2) = target.depth2.as_ref() {
        if !depth2.thin {
            return Err(RawBoundaryBlockReason::Depth2FatLayout);
        }
        return match decision {
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Opt { slice: false, .. } => {
                Ok(if depth2.inner_mutability == RawMutability::Mut {
                    BridgeTemplate::Depth2NpoMut
                } else {
                    BridgeTemplate::Depth2NpoConst
                })
            }
            Decision::Opt { slice: true, .. }
            | Decision::Slice { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => Err(RawBoundaryBlockReason::TemplateUnavailable),
        };
    }
    if target.is_void_pointee() {
        return match decision {
            Decision::Ref { mutable: true } | Decision::InferredRef { mutable: true, .. }
                if target.mutability == RawMutability::Mut =>
            {
                Ok(BridgeTemplate::VoidFromMut)
            }
            Decision::Ref { mutable: true } | Decision::InferredRef { mutable: true, .. } => {
                Ok(BridgeTemplate::VoidFromMutAsConst)
            }
            Decision::Ref { mutable: false } | Decision::InferredRef { mutable: false, .. }
                if target.mutability == RawMutability::Const =>
            {
                Ok(BridgeTemplate::VoidFromRef)
            }
            Decision::Ref { mutable: false } | Decision::InferredRef { mutable: false, .. } => {
                Err(RawBoundaryBlockReason::SharedToMut)
            }
            Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => Err(RawBoundaryBlockReason::TemplateUnavailable),
        };
    }
    match decision {
        Decision::Ref { mutable } | Decision::InferredRef { mutable, .. } => {
            match (*mutable, target.mutability) {
                (true, RawMutability::Mut) => Ok(BridgeTemplate::RefMutToRawMut),
                (true, RawMutability::Const) => Ok(BridgeTemplate::RefMutToRawConst),
                (false, RawMutability::Const) => Ok(BridgeTemplate::RefSharedToRawConst),
                (false, RawMutability::Mut) if permits_shared_to_mut => {
                    Ok(BridgeTemplate::RefSharedToRawMut)
                }
                (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
            }
        }
        Decision::Slice { mutable, .. } => match (*mutable, target.mutability) {
            (true, RawMutability::Mut) => Ok(BridgeTemplate::SliceMutToRawMut),
            (_, RawMutability::Const) => Ok(BridgeTemplate::SliceToRawConst),
            (false, RawMutability::Mut) if permits_shared_to_mut => {
                Ok(BridgeTemplate::SliceToRawMut)
            }
            (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
        },
        Decision::Opt { mutable, slice, .. } => {
            if *slice {
                match (*mutable, target.mutability) {
                    (false, RawMutability::Mut) if permits_shared_to_mut => {
                        Ok(BridgeTemplate::OptSliceToRawMut)
                    }
                    (false, RawMutability::Mut) => Err(RawBoundaryBlockReason::SharedToMut),
                    _ => Ok(BridgeTemplate::OptSliceToRaw),
                }
            } else {
                match (*mutable, target.mutability) {
                    (true, RawMutability::Mut) => Ok(BridgeTemplate::OptRefMutToRawMut),
                    (_, RawMutability::Const) => Ok(BridgeTemplate::OptRefToRawConst),
                    (false, RawMutability::Mut) if permits_shared_to_mut => {
                        Ok(BridgeTemplate::OptRefToRawMut)
                    }
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
    handled_nodes: FxHashSet<(LocalDefId, HirId)>,
    blocked_nodes: FxHashMap<(LocalDefId, HirId), RawBoundaryBlockReason>,
    address_open_nodes: FxHashSet<(LocalDefId, HirId)>,
    address_sites: Vec<AddressViewSite>,
    address_classes: FxHashMap<(LocalDefId, HirId), super::emitability::AddressUseClass>,
    certificate_replay_wall_s: f64,
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
            .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), (subject, decision)))
            .collect::<FxHashMap<_, _>>();
        let mut out = Self::default();
        let mut certificate_replay_wall_s = 0.0f64;
        let mut open_nodes = FxHashMap::<(LocalDefId, HirId), Vec<bool>>::default();
        let mut handled_nodes = FxHashMap::<(LocalDefId, HirId), Vec<bool>>::default();
        for site in &site_facts.sites {
            let disposition: Result<RawBoundaryDisposition, (RawBoundaryBlockReason, String)> =
                (|| {
                    let node = site.node.ok_or_else(|| {
                        (
                            RawBoundaryBlockReason::SubjectUnrooted,
                            "site has no subject root".to_owned(),
                        )
                    })?;
                    if site.target.depth2.is_some() && site.direct_storage_span.is_none() {
                        return Err((
                            RawBoundaryBlockReason::Depth2StorageShape,
                            "depth-2 out-param storage is not a direct variable local".to_owned(),
                        ));
                    }
                    let (_, decision) = decisions.get(&node).copied().ok_or_else(|| {
                        (
                            RawBoundaryBlockReason::SubjectNotSafe,
                            "hypothetical has no safe subject decision".to_owned(),
                        )
                    })?;
                    let source_stays_raw = match decision {
                        super::Decision::Degraded(_) => true,
                        super::Decision::Ref { .. }
                        | super::Decision::InferredRef { .. }
                        | super::Decision::Slice { .. }
                        | super::Decision::Opt { .. }
                        | super::Decision::Box(_) => false,
                    };
                    if source_stays_raw
                        && let Some(source_mutability) = site.adapter_operand_mutability
                        && source_mutability != site.target.mutability
                    {
                        let template = if site.target.mutability == RawMutability::Mut {
                            BridgeTemplate::RawCastMut
                        } else {
                            BridgeTemplate::RawCastConst
                        };
                        return Ok(RawBoundaryDisposition::T1 {
                            template,
                            evidence: "raw-pointer-mutability-cast".to_owned(),
                        });
                    }
                    if let Some((owner, reason)) = box_site_owner(decision, site) {
                        return Ok(RawBoundaryDisposition::OwnedByOtherArm { owner, reason });
                    }
                    let contract = super::raw_boundary_contracts::classify_contract(
                        &site.key.callee,
                        site.key.argument_index,
                        &site.target,
                    );
                    let (retention_verdict, ownership, permits_shared_to_mut, evidence) =
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
                                contract.permits_shared_to_mut,
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
                                false,
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
                                    false,
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
                    let template =
                        template_for(decision, &site.target, ownership, permits_shared_to_mut)
                            .map_err(|reason| (reason, "template-preflight".to_owned()))?;
                    match retention_verdict {
                        RetentionVerdict::NoRetain { certificate } => {
                            let certificate_started = std::time::Instant::now();
                            let certificate_invalid = site.callee_local.is_some()
                                && retention
                                    .verify_certificate(
                                        site.callee_local.expect("local"),
                                        site.key.argument_index,
                                        &certificate,
                                    )
                                    .is_err();
                            certificate_replay_wall_s +=
                                certificate_started.elapsed().as_secs_f64();
                            if certificate_invalid {
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
                .and_then(|node| decisions.get(&node).map(|(_, decision)| *decision))
                .is_some_and(|decision| match decision {
                    super::Decision::Box(plan) => plan.shape == super::box_facts::BoxShape::Slice,
                    super::Decision::Ref { .. }
                    | super::Decision::InferredRef { .. }
                    | super::Decision::Slice { .. }
                    | super::Decision::Opt { .. }
                    | super::Decision::Degraded(_) => false,
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
                            .then_some(match decision {
                                super::Decision::Degraded(_) => true,
                                super::Decision::Ref { .. }
                                | super::Decision::InferredRef { .. }
                                | super::Decision::Slice { .. }
                                | super::Decision::Opt { .. }
                                | super::Decision::Box(_) => false,
                            })
                    })
                    .unwrap_or(true)
            });
            out.render_sites.insert(
                site.key.clone(),
                RawBoundaryRenderSite {
                    span: site.source_span,
                    direct_storage_span: site.direct_storage_span,
                    adapter_operand_span: site.adapter_operand_span,
                    call_span: site.call_span,
                    target: site.target.clone(),
                    box_slice,
                    source_shape: site.source_shape,
                    source_site: site.source_site.clone(),
                    node: site.node,
                    callee_local: site.callee_local,
                    target_stays_raw,
                    subject_identity: site
                        .node
                        .and_then(|node| decisions.get(&node).map(|(subject, _)| *subject))
                        .map_or_else(
                            || format!("{}::{}", site.key.caller, site.key.subject),
                            |subject| subject.identity_key(&site.key.caller),
                        ),
                },
            );
            if let Some(node) = site.node {
                let opens_arm_a = disposition.is_open() && target_stays_raw;
                let handled = match &disposition {
                    RawBoundaryDisposition::OwnedByOtherArm { .. } => true,
                    _ => disposition.is_handled() && target_stays_raw,
                };
                open_nodes.entry(node).or_default().push(opens_arm_a);
                handled_nodes.entry(node).or_default().push(handled);
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
                open_nodes.entry(node).or_default().push(false);
                handled_nodes.entry(node).or_default().push(false);
                out.blocked_nodes
                    .entry(node)
                    .or_insert(RawBoundaryBlockReason::SiteUnresolved);
            }
        }
        for (node, verdicts) in open_nodes {
            if !verdicts.is_empty() && verdicts.into_iter().all(|open| open) {
                out.open_nodes.insert(node);
            }
        }
        for (node, verdicts) in handled_nodes {
            if !verdicts.is_empty() && verdicts.into_iter().all(|handled| handled) {
                out.handled_nodes.insert(node);
            }
        }
        for observation in &emitability.address_observations {
            if observation.operands.is_empty()
                || !observation.operands.iter().all(|operand| {
                    emitability.address_use_class(operand.node)
                        == super::emitability::AddressUseClass::ValueOnly
                })
            {
                continue;
            }
            for operand in &observation.operands {
                let Some((_, decision)) = decisions.get(&operand.node).copied() else {
                    continue;
                };
                let target = RawTargetType {
                    rendered: "*const _".to_owned(),
                    pointee: "_".to_owned(),
                    mutability: RawMutability::Const,
                    depth2: None,
                };
                let Ok(template) = template_for(decision, &target, None, false) else {
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
                out.address_open_nodes.insert(operand.node);
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
        let mut address_nodes = emitability
            .raw_only_uses
            .keys()
            .copied()
            .collect::<FxHashSet<_>>();
        address_nodes.extend(
            emitability
                .address_observations
                .iter()
                .flat_map(|observation| observation.operands.iter().map(|operand| operand.node)),
        );
        out.address_classes = address_nodes
            .into_iter()
            .map(|node| (node, emitability.address_use_class(node)))
            .collect();
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
        out.certificate_replay_wall_s = certificate_replay_wall_s;
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
            "caller\tblock\tstatement_index\tcallee\targument_index\tsubject\tsubject_identity\tsource_site\ttarget_stays_raw\tsite_owner\ttier\ttemplate\twaiver_id\tevidence\treason\tdetail\tatom_group\n",
        );
        let atom_groups = self.subject_atom_groups();
        for (key, disposition) in &self.by_site {
            let (template, waiver, evidence, reason, detail, site_owner) = match disposition {
                RawBoundaryDisposition::T1 { template, evidence } => {
                    (template.key(), "-", evidence.as_str(), "-", "-", "arm-a")
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
                    "arm-a",
                ),
                RawBoundaryDisposition::Blocked { reason, detail } => {
                    ("-", "-", "-", reason.key(), detail.as_str(), "blocked")
                }
                RawBoundaryDisposition::OwnedByOtherArm { owner, reason } => {
                    ("-", "-", "-", *reason, "-", *owner)
                }
            };
            let render = self.render_sites.get(key);
            let subject_identity = render.map_or("-", |site| site.subject_identity.as_str());
            let atom_group = render
                .and_then(|site| site.node)
                .map(|node| {
                    atom_groups
                        .get(&node)
                        .into_iter()
                        .flatten()
                        .map(|atom| atom.id.as_str())
                        .collect::<Vec<_>>()
                        .join(";")
                })
                .filter(|group| !group.is_empty())
                .unwrap_or_else(|| "-".to_owned());
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                key.caller,
                key.block,
                key.statement_index,
                key.callee.path,
                key.argument_index,
                key.subject,
                subject_identity,
                render.map_or("-", |site| site.source_site.as_str()),
                render.map_or("-", |site| if site.target_stays_raw { "1" } else { "0" }),
                site_owner,
                disposition.tier(),
                template,
                waiver,
                evidence,
                reason,
                detail,
                atom_group,
            ));
        }
        out
    }

    pub(crate) fn address_sites(&self) -> &[AddressViewSite] {
        &self.address_sites
    }

    pub(crate) fn opens_address(&self, node: (LocalDefId, HirId)) -> bool {
        self.address_open_nodes.contains(&node)
    }

    pub(crate) fn addresses_tsv(&self, tcx: TyCtxt<'_>) -> String {
        let mut out = String::from(
            "owner\tlocal_def_index\thir_local_id\tuse_class\trealized_edit_count\tops\n",
        );
        let mut classes = self.address_classes.iter().collect::<Vec<_>>();
        classes
            .sort_by_key(|(node, _)| (node.0.local_def_index.as_u32(), node.1.local_id.as_u32()));
        for (&node, &class) in classes {
            let sites = self
                .address_sites
                .iter()
                .filter(|site| site.node == node)
                .collect::<Vec<_>>();
            let ops = sites
                .iter()
                .map(|site| site.op)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
                .join(";");
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\n",
                tcx.def_path_str(node.0.to_def_id()),
                node.0.local_def_index.as_u32(),
                node.1.local_id.as_u32(),
                class.key(),
                sites.len(),
                if ops.is_empty() { "-" } else { &ops },
            ));
        }
        out
    }

    pub(crate) fn certificate_replay_wall_s(&self) -> f64 {
        self.certificate_replay_wall_s
    }

    pub(crate) fn atoms_tsv(&self) -> String {
        let groups = self.subject_atom_groups();
        let mut rows = groups
            .values()
            .flatten()
            .map(|atom| {
                (
                    atom.id.clone(),
                    format!(
                        "{}\t{}\t{}\t{}\n",
                        atom.id,
                        atom.owner,
                        atom.node.0.local_def_index.as_u32(),
                        atom.node.1.local_id.as_u32()
                    ),
                )
            })
            .collect::<Vec<_>>();
        rows.sort_by(|left, right| left.0.cmp(&right.0));
        let mut out = String::from("atom_id\towner\tlocal_def_index\thir_local_id\n");
        for (_, row) in rows {
            out.push_str(&row);
        }
        out
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

    fn handles_site(&self, key: &RawBoundarySiteKey) -> bool {
        match self.by_site.get(key) {
            Some(RawBoundaryDisposition::OwnedByOtherArm { .. }) => true,
            Some(RawBoundaryDisposition::T1 { .. } | RawBoundaryDisposition::T2 { .. }) => self
                .render_sites
                .get(key)
                .is_some_and(|site| site.target_stays_raw),
            Some(RawBoundaryDisposition::Blocked { .. }) | None => false,
        }
    }

    pub(crate) fn node_dispositions(
        &self,
        node: (LocalDefId, HirId),
    ) -> Vec<(&RawBoundarySiteKey, &RawBoundaryDisposition)> {
        let mut rows = self
            .render_sites
            .iter()
            .filter_map(|(key, site)| {
                (site.node == Some(node))
                    .then(|| self.by_site.get(key).map(|disposition| (key, disposition)))
                    .flatten()
            })
            .collect::<Vec<_>>();
        rows.sort_by(|left, right| left.0.cmp(right.0));
        rows
    }

    pub(crate) fn opens_span(&self, node: (LocalDefId, HirId), span: Span) -> bool {
        let span = span.source_callsite();
        self.handled_nodes.contains(&node)
            && self
                .site_lookup
                .iter()
                .any(|(candidate, site_span, _, key)| {
                    *candidate == node
                        && (site_span.contains(span) || span.contains(*site_span))
                        && self.handles_site(key)
                })
    }

    pub(crate) fn opens_argument(
        &self,
        node: (LocalDefId, HirId),
        span: Span,
        argument_index: usize,
    ) -> bool {
        let span = span.source_callsite();
        self.handled_nodes.contains(&node)
            && self
                .site_lookup
                .iter()
                .any(|(candidate, site_span, index, key)| {
                    *candidate == node
                        && *index == argument_index
                        && (site_span.contains(span) || span.contains(*site_span))
                        && self.handles_site(key)
                })
    }

    /// Whether this exact argument is in the T1/T2 boundary market, including
    /// a site whose final surface makes the raw bridge syntax a no-op. PAIR
    /// still owes an A5 proof receipt for that identity; unlike
    /// [`Self::opens_argument`], this observation does not claim the site is an
    /// active Arm-A edit.
    pub(crate) fn tracks_call_argument(
        &self,
        caller: LocalDefId,
        callee_path: &str,
        span: Span,
        argument_index: usize,
    ) -> bool {
        let span = span.source_callsite();
        self.site_lookup
            .iter()
            .any(|(candidate, site_span, index, key)| {
                candidate.0 == caller
                    && key.callee.path == callee_path
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
            .render("p", RawMutability::Mut, false, Some("i32"))
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
            depth2: None,
        };
        assert_eq!(
            template_for(
                &super::super::Decision::Ref { mutable: false },
                &target,
                None,
                false,
            ),
            Err(RawBoundaryBlockReason::SharedToMut)
        );
        assert_eq!(
            RawBoundaryBlockReason::SharedToMut.key(),
            "raw-boundary-shared-to-mut"
        );
    }

    #[test]
    fn rb_x3_read_only_family_permission_has_an_explicit_shared_to_mut_bridge() {
        let target = RawTargetType {
            rendered: "*mut i8".to_owned(),
            pointee: "i8".to_owned(),
            mutability: RawMutability::Mut,
            depth2: None,
        };
        let template = template_for(
            &super::super::Decision::Ref { mutable: false },
            &target,
            Some(super::super::raw_boundary_contracts::OwnershipContract::BorrowView),
            true,
        )
        .expect("ruled family bridge");
        assert_eq!(template, BridgeTemplate::RefSharedToRawMut);
        let BridgeRender::Edit(text) = template
            .render("p", RawMutability::Mut, false, None)
            .expect("explicit bridge")
        else {
            panic!("shared-to-mut family bridge must emit syntax");
        };
        assert!(text.contains("core::ptr::from_ref(p)"), "{text}");
        assert!(text.contains(".cast_mut()"), "{text}");
    }

    #[test]
    fn rb_w7_box_borrow_view_does_not_consume_the_owner() {
        let rendered = BridgeTemplate::BoxBorrowViewToRaw
            .render("owner", RawMutability::Mut, false, None)
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
                .render("owner", RawMutability::Mut, false, None)
                .expect("lifecycle"),
            BridgeRender::Lifecycle
        );
    }

    #[test]
    fn zero_syntax_ref_bridge_is_receipted_without_an_edit() {
        assert_eq!(
            BridgeTemplate::RefMutToRawMut
                .render("p", RawMutability::Mut, false, None)
                .expect("zero syntax"),
            BridgeRender::ZeroSyntax
        );
    }
}
