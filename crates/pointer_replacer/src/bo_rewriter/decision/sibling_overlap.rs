//! R233 caller-side sibling-overlap evidence, carried to terminal receipts.
//!
//! This consumer never changes the model, a declaration, an adapter, or a hold.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::Res,
    def_id::{DefId, LocalDefId},
    intravisit,
};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Location, Operand, ProjectionElem, RETURN_PLACE, Rvalue,
        StatementKind, TerminatorKind, visit::Visitor,
    },
    ty::{TyCtxt, TyKind},
};
use rustc_mir_dataflow::Analysis;
use rustc_span::Span;

use super::{
    Subject, SubjectKind,
    a5_site_proof::{A5PeerProof, A5SiteProofVerdict},
    outbound_expression::OutboundExpressionPlans,
    raw_boundary::{RawBoundarySiteKey, RetentionVerdict, raw_target_type, site_atom_id},
    raw_boundary_contracts::{PointeeAccess, RetentionContract, classify_contract},
    return_interface::ReturnInterface,
    seam::Form,
};
use crate::analyses::{
    borrow_ownership::{l2::MirLocationKey, slots::SlotOwner},
    liveness::MaybeLiveLocals,
};

pub(crate) const PENDING_REASON: &str = "t1-sibling-overlap:pending";
pub(crate) const PENDING_TIER: &str = "T2-pending";
pub(crate) const PENDING_WAIVER: &str = "c-aliasing-semantics-at-unsafe-bridges/v2-pending";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SiblingAccess {
    Foster {
        local: Local,
        mutable: bool,
        defaulted: bool,
    },
    Contract {
        access: PointeeAccess,
        provenance: &'static str,
    },
    Unknown(&'static str),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SiblingEvidence {
    pub argument_index: usize,
    /// Exact existing HIR argument classification; absence is missing capture,
    /// never an inferred shape from a binding name or the A5 verdict.
    pub argument_shape: Option<&'static str>,
    /// **R287-1(c).** Where this sibling's argument actually is, so the pending
    /// ledger row can state a disposition for it rather than leave a gap. The
    /// same absence rule as `argument_shape`: `None` is missing capture, and a
    /// disposition is never guessed from it.
    pub argument_span: Option<Span>,
    pub proof: A5PeerProof,
    pub access: SiblingAccess,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LocalPostCallEvidence {
    ParameterProtected,
    ParameterOrigin {
        parameters: Vec<usize>,
    },
    Live {
        locals: Vec<Local>,
    },
    /// Only complete frozen provenance and MIR exit-liveness can mint this.
    DeadUnprotected {
        checked_locals: Vec<Local>,
    },
    Unknown(&'static str),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SiblingSource {
    Declared(Subject),
    NativeReturnExpression {
        argument_hir: HirId,
        source_callee: LocalDefId,
        source_interface: ReturnInterface,
        /// The original outer call's actual MIR operand, including an
        /// original coercion temporary. This is not a declaration identity.
        mir_argument_local: Option<Local>,
        temporary: String,
    },
}

impl SiblingSource {
    pub(crate) fn declared(&self) -> Option<&Subject> {
        match self {
            Self::Declared(subject) => Some(subject),
            Self::NativeReturnExpression { .. } => None,
        }
    }

    pub(crate) fn hir_id(&self) -> HirId {
        match self {
            Self::Declared(subject) => subject.hir_id,
            Self::NativeReturnExpression { argument_hir, .. } => *argument_hir,
        }
    }

    pub(crate) fn caller(&self) -> LocalDefId {
        match self {
            Self::Declared(subject) => subject.fn_did,
            Self::NativeReturnExpression { argument_hir, .. } => argument_hir.owner.def_id,
        }
    }

    pub(crate) fn mir_local(&self) -> Option<Local> {
        match self {
            Self::Declared(subject) => Some(subject.local),
            Self::NativeReturnExpression {
                mir_argument_local, ..
            } => *mir_argument_local,
        }
    }

    pub(crate) fn owner_class(&self) -> crate::bo_rewriter::bridge_receipt::SignatureClassId {
        let owner = match self {
            Self::Declared(subject) => subject.fn_did,
            Self::NativeReturnExpression { source_callee, .. } => *source_callee,
        };
        crate::bo_rewriter::bridge_receipt::SignatureClassId::of(owner)
    }

    pub(crate) fn identity_key(&self, caller_path: &str) -> String {
        match self {
            Self::Declared(subject) => subject.identity_key(caller_path),
            Self::NativeReturnExpression { argument_hir, .. } => format!(
                "{caller_path}::<outbound-expression:{}>",
                argument_hir.local_id.as_u32()
            ),
        }
    }

    pub(crate) fn label(&self) -> String {
        match self {
            Self::Declared(subject) => subject.label.clone(),
            Self::NativeReturnExpression { argument_hir, .. } => {
                format!("outbound-expression:{}", argument_hir.local_id.as_u32())
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SiblingPotential {
    pub site: RawBoundarySiteKey,
    pub caller: LocalDefId,
    pub callee: DefId,
    pub source: SiblingSource,
    pub argument_span: Span,
    pub call_span: Span,
    pub source_shape: &'static str,
    pub siblings: Vec<SiblingEvidence>,
    pub local_post_call: LocalPostCallEvidence,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SourceBridgeEvidence {
    WholeSubject,
    ProjectedReferent { use_hir_id: HirId },
    TypedView { use_hir_id: HirId, method: DefId },
    NativeReturnExpression { use_hir_id: HirId },
    RawFieldValue,
    BindingStorage,
    UnknownShape(&'static str),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SourceBridgeCoverage {
    pub potential: SiblingPotential,
    pub evidence: SourceBridgeEvidence,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct SiblingInventory {
    pub potentials: Vec<SiblingPotential>,
    pub coverage: Vec<SourceBridgeCoverage>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CoverageGapReceipt {
    pub potential: SiblingPotential,
    pub source_form: Form,
    pub target_form: Form,
    pub reason: &'static str,
    /// R291-1: the unsealed source shape, carried rather than discarded.
    pub shape: &'static str,
}

pub(crate) fn select_coverage_gaps(
    coverage: &[SourceBridgeCoverage],
    mut terminal: impl FnMut(&SiblingPotential) -> TerminalSiteState,
) -> Vec<CoverageGapReceipt> {
    coverage
        .iter()
        .filter_map(|record| {
            if !matches!(record.evidence, SourceBridgeEvidence::UnknownShape(_)) {
                return None;
            }
            let state = terminal(&record.potential);
            if !pending_site_eligible(&record.potential, state) {
                return None;
            }
            let SourceBridgeEvidence::UnknownShape(shape) = record.evidence else {
                // Guarded by the filter above; restated so a new evidence
                // variant cannot silently acquire the empty shape.
                return None;
            };
            Some(CoverageGapReceipt {
                potential: record.potential.clone(),
                source_form: state.source_form,
                target_form: state.target_form,
                reason: "sibling-source-bridge-custody-unresolved",
                // **R291-1** — the gap carries the shape it could not seal.
                // The receipt discarded it, so 276 corpus sites arrived under
                // one name with no partition to design a row contract on.
                shape,
            })
        })
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TerminalSiteState {
    pub source_form: Form,
    pub target_form: Form,
    /// Actual declaration custody, not the hypothetical decision alone.
    pub source_delivered: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PendingSiblingReceipt {
    pub potential: SiblingPotential,
    pub source_form: Form,
    pub target_form: Form,
    pub risky_siblings: Vec<SiblingEvidence>,
    pub reason: &'static str,
    pub tier: &'static str,
    pub waiver: &'static str,
}

impl PendingSiblingReceipt {
    pub(crate) fn site_id(&self) -> String {
        site_atom_id(&self.potential.site)
    }
}

pub(crate) fn collect(tcx: TyCtxt<'_>, ctx: &super::super::DecideCtx) -> Vec<SiblingPotential> {
    collect_inventory(tcx, ctx).potentials
}

pub(crate) fn collect_inventory(
    tcx: TyCtxt<'_>,
    ctx: &super::super::DecideCtx,
) -> SiblingInventory {
    collect_inventory_with_expressions(tcx, ctx, &OutboundExpressionPlans::default())
}

pub(crate) fn collect_inventory_with_expressions(
    tcx: TyCtxt<'_>,
    ctx: &super::super::DecideCtx,
    outbound_expressions: &OutboundExpressionPlans,
) -> SiblingInventory {
    let mut potentials = Vec::new();
    let mut coverage = Vec::new();
    let mut exit_liveness = FxHashMap::default();
    let mut expressions = FxHashMap::default();
    for site in &ctx.raw_boundary_sites.sites {
        let (caller, mut source, source_evidence) =
            if let Some(expression) = outbound_expressions.plans.get(&site.key) {
                let exact = expression.key == site.key
                    && expression.argument_span == site.source_span
                    && expression.call_span == site.call_span
                    && expression.caller == expression.argument_hir.owner.def_id
                    && tcx.def_path_str(expression.caller.to_def_id()) == site.key.caller;
                (
                    expression.caller,
                    SiblingSource::NativeReturnExpression {
                        argument_hir: expression.argument_hir,
                        source_callee: expression.source_callee,
                        source_interface: expression.source_interface.clone(),
                        mir_argument_local: None,
                        temporary: expression.temporary.clone(),
                    },
                    if exact {
                        SourceBridgeEvidence::NativeReturnExpression {
                            use_hir_id: expression.argument_hir,
                        }
                    } else {
                        SourceBridgeEvidence::UnknownShape("native-expression-plan-site-mismatch")
                    },
                )
            } else {
                let Some((caller, binding)) = site.node else { continue };
                let Some(source) = ctx
                    .subjects
                    .iter()
                    .find(|subject| subject.fn_did == caller && subject.hir_id == binding)
                else {
                    continue;
                };
                let model_kind = ctx
                    .slots
                    .fn_local_slots
                    .get(&caller)
                    .and_then(|slots| slots.slot_for_local_depth(source.local, 0))
                    .and_then(|slot| ctx.model.get(&super::super::SlotRef::Local(caller, slot)));
                if model_kind != Some(&super::super::SlotKind::Ref) {
                    continue;
                }
                let expressions = expressions
                    .entry(caller)
                    .or_insert_with(|| expression_index(tcx, caller));
                let evidence = source_bridge_evidence(
                    tcx,
                    source,
                    site.source_span,
                    site.direct_storage_span.is_some(),
                    expressions,
                );
                (caller, SiblingSource::Declared(source.clone()), evidence)
            };
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let block = BasicBlock::from_u32(site.key.block);
        let Some(data) = body.basic_blocks.get(block) else { continue };
        if site.key.statement_index as usize != data.statements.len() {
            continue;
        }
        let (func, args) = match &data.terminator().kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => (func, args),
            _ => continue,
        };
        let Some(constant) = func.constant() else { continue };
        let TyKind::FnDef(callee, _) = *constant.ty().kind() else { continue };
        if tcx.def_path_str(callee) != site.key.callee.path {
            continue;
        }
        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        if let SiblingSource::NativeReturnExpression {
            mir_argument_local, ..
        } = &mut source
        {
            *mir_argument_local = args
                .get(site.key.argument_index)
                .and_then(|argument| argument.node.place())
                .and_then(|place| place.as_local());
        }
        let mut siblings = Vec::new();
        for (argument_index, argument) in args.iter().enumerate() {
            if argument_index == site.key.argument_index {
                continue;
            }
            let argument_type = argument.node.ty(&*body, tcx);
            let target = raw_target_type(tcx, argument_type);
            if target.is_none() && !matches!(argument_type.kind(), TyKind::Ref(..)) {
                continue;
            }
            let sibling_sites = ctx
                .raw_boundary_sites
                .sites
                .iter()
                .filter(|sibling| {
                    sibling.key.caller == site.key.caller
                        && sibling.key.callee == site.key.callee
                        && sibling.key.block == site.key.block
                        && sibling.key.statement_index == site.key.statement_index
                        && sibling.key.argument_index == argument_index
                })
                .collect::<Vec<_>>();
            let argument_shape = match sibling_sites.as_slice() {
                [sibling] => Some(sibling.source_shape),
                [] => {
                    let shapes = callee
                        .as_local()
                        .and_then(|callee| ctx.facts.call_args.get(&callee))
                        .into_iter()
                        .flatten()
                        .filter(|call| {
                            call.caller == caller
                                && call.span.source_callsite() == site.call_span.source_callsite()
                        })
                        .flat_map(|call| {
                            call.args
                                .iter()
                                .filter(|argument| argument.index == argument_index)
                        })
                        .map(|argument| argument.shape.key())
                        .collect::<Vec<_>>();
                    match shapes.as_slice() {
                        [shape] => Some(*shape),
                        _ => None,
                    }
                }
                _ => None,
            };
            let proof = if let ([sibling], Some(local_callee)) =
                (sibling_sites.as_slice(), callee.as_local())
            {
                let proof = ctx.a5_site_proofs.lookup(
                    caller.local_def_index.as_u32(),
                    local_callee.local_def_index.as_u32(),
                    site.key.argument_index,
                    argument_index,
                    site.source_span,
                    sibling.source_span,
                );
                if proof.location.is_some_and(|found| {
                    found
                        != MirLocationKey {
                            block: site.key.block,
                            statement_index: site.key.statement_index as usize,
                        }
                }) {
                    unknown_proof("sibling-a5-location-mismatch")
                } else {
                    proof
                }
            } else {
                unknown_proof("sibling-a5-operand-inventory-unresolved")
            };
            let access = if let Some(local_callee) = site.callee_local {
                let callee_body = tcx
                    .mir_drops_elaborated_and_const_checked(local_callee)
                    .borrow();
                let parameters = ctx
                    .subjects
                    .iter()
                    .filter(|subject| {
                        subject.fn_did == local_callee
                            && matches!(subject.kind, SubjectKind::Param { hir_index }
                            if hir_index == argument_index)
                    })
                    .collect::<Vec<_>>();
                match (
                    callee_body.args_iter().nth(argument_index),
                    parameters.as_slice(),
                ) {
                    (Some(local), [] | [_])
                        if parameters
                            .first()
                            .is_none_or(|parameter| parameter.local == local)
                            && matches!(
                                callee_body.local_decls[local].ty.kind(),
                                TyKind::RawPtr(..) | TyKind::Ref(..)
                            ) =>
                    {
                        SiblingAccess::Foster {
                            local,
                            mutable: ctx.mut_facts.is_mutable(local_callee, local),
                            defaulted: ctx.mut_facts.is_defaulted(local_callee, local),
                        }
                    }
                    _ => SiblingAccess::Unknown("sibling-parameter-identity-unresolved"),
                }
            } else if let Some(target) = target.as_ref() {
                match classify_contract(&site.key.callee, argument_index, target) {
                    Ok(contract) => SiblingAccess::Contract {
                        access: contract.access,
                        provenance: contract.provenance,
                    },
                    Err(_) => SiblingAccess::Unknown("sibling-library-access-unresolved"),
                }
            } else {
                SiblingAccess::Unknown("sibling-library-native-reference-access-unresolved")
            };
            let argument_span = match sibling_sites.as_slice() {
                [sibling] => Some(sibling.source_span),
                _ => None,
            };
            siblings.push(SiblingEvidence {
                argument_index,
                argument_shape,
                argument_span,
                proof,
                access,
            });
        }
        if siblings.is_empty() && matches!(source, SiblingSource::Declared(_)) {
            continue;
        }
        let local_post_call = match &source {
            SiblingSource::Declared(source) if matches!(source.kind, SubjectKind::Param { .. }) => {
                LocalPostCallEvidence::ParameterProtected
            }
            SiblingSource::Declared(source) => {
                let live = exit_liveness
                    .entry(caller)
                    .or_insert_with(|| call_exit_liveness(tcx, &body));
                local_evidence(
                    tcx,
                    ctx,
                    source.fn_did,
                    source.local,
                    source.ptr_depth,
                    &body,
                    location,
                    live.get(&location),
                )
            }
            SiblingSource::NativeReturnExpression {
                mir_argument_local: Some(local),
                ..
            } => {
                let live = exit_liveness
                    .entry(caller)
                    .or_insert_with(|| call_exit_liveness(tcx, &body));
                let depth = raw_target_type(tcx, body.local_decls[*local].ty)
                    .map_or(0, |target| if target.depth2.is_some() { 2 } else { 1 });
                local_evidence(
                    tcx,
                    ctx,
                    caller,
                    *local,
                    depth,
                    &body,
                    location,
                    live.get(&location),
                )
            }
            SiblingSource::NativeReturnExpression {
                mir_argument_local: None,
                ..
            } => LocalPostCallEvidence::Unknown("native-expression-mir-argument-local-unavailable"),
        };
        let potential = SiblingPotential {
            site: site.key.clone(),
            caller,
            callee,
            source,
            argument_span: site.source_span,
            call_span: site.call_span,
            source_shape: site.source_shape,
            siblings,
            local_post_call,
        };
        match source_evidence {
            SourceBridgeEvidence::WholeSubject
            | SourceBridgeEvidence::ProjectedReferent { .. }
            | SourceBridgeEvidence::TypedView { .. }
            | SourceBridgeEvidence::NativeReturnExpression { .. } => {
                potentials.push(potential.clone())
            }
            SourceBridgeEvidence::RawFieldValue
            | SourceBridgeEvidence::BindingStorage
            | SourceBridgeEvidence::UnknownShape(_) => {}
        }
        coverage.push(SourceBridgeCoverage {
            potential,
            evidence: source_evidence,
        });
    }
    potentials.sort_by(|left, right| left.site.cmp(&right.site));
    coverage.sort_by(|left, right| left.potential.site.cmp(&right.potential.site));
    SiblingInventory {
        potentials,
        coverage,
    }
}

type ExpressionIndex<'tcx> = BTreeMap<(u32, u32), Vec<&'tcx Expr<'tcx>>>;

fn expression_index<'tcx>(tcx: TyCtxt<'tcx>, caller: LocalDefId) -> ExpressionIndex<'tcx> {
    struct Expressions<'tcx> {
        by_span: ExpressionIndex<'tcx>,
    }
    impl<'tcx> intravisit::Visitor<'tcx> for Expressions<'tcx> {
        fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
            let span = expression.span.source_callsite();
            self.by_span
                .entry((span.lo().0, span.hi().0))
                .or_default()
                .push(expression);
            intravisit::walk_expr(self, expression);
        }
    }
    let mut expressions = Expressions {
        by_span: BTreeMap::new(),
    };
    intravisit::Visitor::visit_body(&mut expressions, tcx.hir_body_owned_by(caller));
    expressions.by_span
}

fn source_bridge_evidence(
    tcx: TyCtxt<'_>,
    source: &Subject,
    span: Span,
    direct_storage: bool,
    expressions: &ExpressionIndex<'_>,
) -> SourceBridgeEvidence {
    if direct_storage {
        return SourceBridgeEvidence::BindingStorage;
    }
    let span = span.source_callsite();
    let Some(candidates) = expressions.get(&(span.lo().0, span.hi().0)) else {
        return SourceBridgeEvidence::UnknownShape("source-expression-span-missing");
    };
    let typeck = tcx.typeck(source.fn_did);
    let mut normalized = Vec::new();
    for &candidate in candidates {
        let mut expression = candidate;
        loop {
            match expression.kind {
                ExprKind::DropTemps(inner) => expression = inner,
                ExprKind::Cast(inner, _)
                    if matches!(typeck.expr_ty(expression).kind(), TyKind::RawPtr(..))
                        && matches!(
                            typeck.expr_ty(inner).kind(),
                            TyKind::RawPtr(..) | TyKind::Ref(..)
                        ) =>
                {
                    expression = inner
                }
                _ => break,
            }
        }
        if !normalized
            .iter()
            .any(|old: &&Expr<'_>| old.hir_id == expression.hir_id)
        {
            normalized.push(expression);
        }
    }
    let [expression] = normalized.as_slice() else {
        return SourceBridgeEvidence::UnknownShape("source-expression-span-ambiguous");
    };
    fn root(expression: &Expr<'_>, binding: HirId) -> bool {
        matches!(expression.kind, ExprKind::Path(QPath::Resolved(_, path))
            if path.res == Res::Local(binding))
    }
    if root(expression, source.hir_id) {
        return SourceBridgeEvidence::WholeSubject;
    }
    if matches!(expression.kind, ExprKind::Field(..))
        && matches!(typeck.expr_ty(expression).kind(), TyKind::RawPtr(..))
    {
        return SourceBridgeEvidence::RawFieldValue;
    }
    if let ExprKind::AddrOf(_, _, mut place) = expression.kind {
        let mut dereferences = 0;
        loop {
            match place.kind {
                ExprKind::Field(base, _) | ExprKind::DropTemps(base) => place = base,
                ExprKind::Index(base, _, _)
                    if typeck.type_dependent_def_id(place.hir_id).is_none() =>
                {
                    place = base
                }
                ExprKind::Unary(rustc_hir::UnOp::Deref, base) => {
                    dereferences += 1;
                    place = base;
                }
                _ => break,
            }
        }
        if root(place, source.hir_id) {
            return match dereferences {
                0 => SourceBridgeEvidence::BindingStorage,
                1 => SourceBridgeEvidence::ProjectedReferent {
                    use_hir_id: expression.hir_id,
                },
                _ => SourceBridgeEvidence::UnknownShape("source-projection-depth-unlicensed"),
            };
        }
    }
    if let ExprKind::MethodCall(_, receiver, _, _) = expression.kind
        && root(receiver, source.hir_id)
        && matches!(typeck.expr_ty(receiver).kind(), TyKind::RawPtr(..))
        && let Some(method) = typeck.type_dependent_def_id(expression.hir_id)
        && !method.is_local()
        && tcx.crate_name(method.krate).as_str() == "core"
        && tcx.def_kind(method) == rustc_hir::def::DefKind::AssocFn
        && matches!(
            tcx.item_name(method).as_str(),
            "offset"
                | "add"
                | "sub"
                | "wrapping_offset"
                | "wrapping_add"
                | "wrapping_sub"
                | "byte_offset"
                | "wrapping_byte_offset"
                | "cast"
                | "cast_const"
                | "cast_mut"
        )
    {
        return SourceBridgeEvidence::TypedView {
            use_hir_id: expression.hir_id,
            method,
        };
    }
    SourceBridgeEvidence::UnknownShape(unsealed_shape(tcx, typeck, expression, source))
}

/// **R291-1 — what the source expression IS, when it is none of the sealed
/// shapes.**
///
/// The fallback said only `source-expression-not-a-sealed-reference-view`, and
/// every one of the corpus's 276 gap sites reported it — one bucket, no
/// partition, and no way to tell a shape worth sealing from one that never
/// could be. It names the shape instead, which is what the source-bridge row
/// contract has to state.
///
/// This changes no verdict: the site is a gap either way. It changes only what
/// the receipt says about it.
fn unsealed_shape(
    tcx: TyCtxt<'_>,
    typeck: &rustc_middle::ty::TypeckResults<'_>,
    expression: &Expr<'_>,
    source: &Subject,
) -> &'static str {
    fn rooted_elsewhere(expression: &Expr<'_>) -> bool {
        matches!(expression.kind, ExprKind::Path(QPath::Resolved(_, path))
            if matches!(path.res, Res::Local(_)))
    }
    match expression.kind {
        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
            Res::Local(_) => "unsealed:local-other-than-the-subject",
            Res::Def(rustc_hir::def::DefKind::Static { .. }, _) => "unsealed:static",
            Res::Def(rustc_hir::def::DefKind::Const, _)
            | Res::Def(rustc_hir::def::DefKind::AssocConst, _) => "unsealed:const",
            Res::Def(rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn, _) => {
                "unsealed:function-item"
            }
            _ => "unsealed:path-other",
        },
        ExprKind::Path(_) => "unsealed:path-unresolved",
        ExprKind::Field(..) => "unsealed:field-not-raw",
        ExprKind::Index(..) => "unsealed:index",
        ExprKind::Unary(rustc_hir::UnOp::Deref, _) => "unsealed:deref",
        ExprKind::Unary(..) => "unsealed:unary",
        ExprKind::Binary(..) => "unsealed:binary",
        ExprKind::AddrOf(..) => {
            if rooted_elsewhere(expression) {
                "unsealed:addr-of-other-root"
            } else {
                "unsealed:addr-of-non-place"
            }
        }
        ExprKind::MethodCall(_, receiver, _, _) => {
            let Some(method) = typeck.type_dependent_def_id(expression.hir_id) else {
                return "unsealed:method-unresolved";
            };
            let receiver_is_subject = matches!(receiver.kind, ExprKind::Path(QPath::Resolved(_, path))
                if path.res == Res::Local(source.hir_id));
            match (method.is_local(), receiver_is_subject) {
                (true, _) => "unsealed:method-local",
                (false, true) if tcx.crate_name(method.krate).as_str() == "core" => {
                    // On the subject, from core, but outside the sealed method
                    // list — the one bucket a widened seal would come from.
                    "unsealed:core-method-outside-the-seal"
                }
                (false, true) => "unsealed:foreign-method-on-the-subject",
                (false, false) => "unsealed:method-on-another-receiver",
            }
        }
        ExprKind::Call(..) => "unsealed:call",
        ExprKind::Lit(..) => "unsealed:literal",
        ExprKind::Cast(..) => "unsealed:cast-not-pointer-to-pointer",
        ExprKind::If(..) | ExprKind::Match(..) => "unsealed:branch",
        ExprKind::Block(..) => "unsealed:block",
        ExprKind::Struct(..) | ExprKind::Array(..) | ExprKind::Tup(..) => "unsealed:aggregate",
        _ => "unsealed:other",
    }
}

pub(crate) fn select_pending(
    potentials: &[SiblingPotential],
    mut terminal: impl FnMut(&SiblingPotential) -> TerminalSiteState,
) -> Vec<PendingSiblingReceipt> {
    potentials
        .iter()
        .filter_map(|potential| {
            let state = terminal(potential);
            if !pending_site_eligible(potential, state) {
                return None;
            }
            let risky_siblings = potential
                .siblings
                .iter()
                .filter(|sibling| risky_sibling(sibling))
                .cloned()
                .collect();
            Some(PendingSiblingReceipt {
                potential: potential.clone(),
                source_form: state.source_form,
                target_form: state.target_form,
                risky_siblings,
                reason: PENDING_REASON,
                tier: PENDING_TIER,
                waiver: PENDING_WAIVER,
            })
        })
        .collect()
}

fn pending_site_eligible(potential: &SiblingPotential, state: TerminalSiteState) -> bool {
    let borrowed_source = match state.source_form {
        Form::Raw => false,
        Form::Ref { .. } | Form::Slice { .. } | Form::Opt { .. } => true,
    };
    state.source_delivered
        && borrowed_source
        && state.target_form == Form::Raw
        && !matches!(
            potential.local_post_call,
            LocalPostCallEvidence::DeadUnprotected { .. }
        )
        && potential.siblings.iter().any(risky_sibling)
}

pub(crate) fn risky_sibling(sibling: &SiblingEvidence) -> bool {
    if sibling.proof.verdict == A5SiteProofVerdict::Clear {
        return false;
    }
    match sibling.access {
        SiblingAccess::Foster {
            mutable: writes,
            defaulted,
            ..
        } => writes || defaulted,
        // This pending waiver covers sibling writes. A read-only sibling
        // receives no new soundness certificate here. Stream state remains
        // with the existing io-domain interception.
        SiblingAccess::Contract {
            access: PointeeAccess::None | PointeeAccess::Read | PointeeAccess::Stream,
            ..
        } => false,
        SiblingAccess::Contract {
            access: PointeeAccess::Write | PointeeAccess::Lifecycle,
            ..
        }
        | SiblingAccess::Unknown(_) => true,
    }
}

fn unknown_proof(reason: &'static str) -> A5PeerProof {
    A5PeerProof {
        verdict: A5SiteProofVerdict::Undeterminable,
        reason,
        family: "sibling-unresolved",
        location: None,
        left_site: None,
        right_site: None,
    }
}

fn call_exit_liveness<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> FxHashMap<Location, DenseBitSet<Local>> {
    let mut cursor = MaybeLiveLocals
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);
    let mut live = FxHashMap::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        // Backward analysis: before the effect in analysis order is exit in
        // program order, including the union of normal and unwind successors.
        cursor.seek_before_primary_effect(location);
        live.insert(location, cursor.get().clone());
    }
    live
}

/// The same frozen caller-origin, alias and exit-liveness proof applies to a
/// declared local and to an actual MIR argument temporary. A native producer's
/// remote parameter is never substituted for this caller-side starting local.
fn local_evidence<'tcx>(
    tcx: TyCtxt<'tcx>,
    ctx: &super::super::DecideCtx,
    caller: LocalDefId,
    source_local: Local,
    ptr_depth: u8,
    body: &Body<'tcx>,
    call: Location,
    live: Option<&DenseBitSet<Local>>,
) -> LocalPostCallEvidence {
    if ptr_depth != 1 {
        return LocalPostCallEvidence::Unknown("local-proof-depth-not-one");
    }
    let Some(flow) = ctx
        .analysis
        .origins
        .as_ref()
        .and_then(|origins| origins.try_native_flows())
        .and_then(|flows| flows.get(&caller))
        .map(|flow| &flow.body)
    else {
        return LocalPostCallEvidence::Unknown("local-proof-origins-unavailable");
    };
    let Some((parameters, complete)) = flow.depth0_argument_origins(body, source_local) else {
        return LocalPostCallEvidence::Unknown("local-proof-origin-slot-unavailable");
    };
    if !parameters.is_empty() {
        return LocalPostCallEvidence::ParameterOrigin {
            parameters: parameters.into_iter().collect(),
        };
    }
    if !complete {
        return LocalPostCallEvidence::Unknown("local-proof-origin-incomplete");
    }
    // This existing closed relation includes storage aliases. Follow both
    // directions: a live ancestor or another descendant of that ancestor can
    // retain the same reference capability after this source local dies.
    // The component is a may set; over-inclusion keeps uncertain locals pending.
    let flows = flow.depth0_value_flows();
    let mut closure = FxHashSet::from_iter([SlotOwner::Local(source_local)]);
    let mut frontier = vec![SlotOwner::Local(source_local)];
    while let Some(owner) = frontier.pop() {
        for &(from, to) in &flows {
            let related = if from == owner {
                Some(to)
            } else if to == owner {
                Some(from)
            } else {
                None
            };
            if let Some(related) = related
                && closure.insert(related)
            {
                frontier.push(related);
            }
        }
    }
    if closure
        .iter()
        .any(|owner| matches!(owner, SlotOwner::Field(_)))
    {
        return LocalPostCallEvidence::Unknown("local-proof-field-alias");
    }
    if flow
        .unknown_owner_depths()
        .iter()
        .any(|(owner, depth)| *depth == 0 && closure.contains(owner))
    {
        return LocalPostCallEvidence::Unknown("local-proof-descendant-origin-incomplete");
    }
    let locals = closure
        .iter()
        .filter_map(|owner| match owner {
            SlotOwner::Local(local) => Some(*local),
            SlotOwner::Field(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let parameters = body
        .args_iter()
        .filter(|local| locals.contains(local))
        .map(|local| local.as_u32() as usize)
        .collect::<Vec<_>>();
    if !parameters.is_empty() {
        return LocalPostCallEvidence::ParameterOrigin { parameters };
    }
    if locals.contains(&RETURN_PLACE) {
        return LocalPostCallEvidence::Unknown("local-proof-returned-alias");
    }
    let Some(live) = live else {
        return LocalPostCallEvidence::Unknown("local-proof-liveness-unavailable");
    };
    let live_locals = locals
        .iter()
        .copied()
        .filter(|local| live.contains(*local))
        .collect::<Vec<_>>();
    if !live_locals.is_empty() {
        return LocalPostCallEvidence::Live {
            locals: live_locals,
        };
    }
    // Local liveness cannot see a stored pointer or an outstanding borrow of
    // the pointer slot. Retain only the transparent depth-zero subset here.
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (destination, rvalue) = &**assignment;
            if let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rvalue
                && locals.contains(&place.local)
            {
                // The observed constructor `_dst = &raw const (*_ref)`
                // transfers the pointer value, rather than borrowing the
                // pointer slot. Its complete tracked component was already
                // proved dead above. Keep every other address/reborrow shape
                // conservative, including bare slots and field projections.
                let pointer_value_transfer = matches!(rvalue, Rvalue::RawPtr(..))
                    && matches!(&place.projection[..], [ProjectionElem::Deref])
                    && destination.as_local().is_some_and(|local| {
                        locals.contains(&local)
                            && flows
                                .contains(&(SlotOwner::Local(place.local), SlotOwner::Local(local)))
                    })
                    && match (
                        body.local_decls[place.local].ty.kind(),
                        destination.ty(body, tcx).ty.kind(),
                    ) {
                        (
                            TyKind::Ref(_, source_pointee, _),
                            TyKind::RawPtr(target_pointee, mutability),
                        ) => source_pointee == target_pointee && !mutability.is_mut(),
                        _ => false,
                    };
                if !pointer_value_transfer {
                    return LocalPostCallEvidence::Unknown(
                        "local-proof-outstanding-address-or-reborrow",
                    );
                }
            }
            let mut mentions = PointerOperands {
                locals: &locals,
                found: false,
            };
            mentions.visit_rvalue(rvalue, call);
            if !mentions.found {
                continue;
            }
            let transparent = matches!(rvalue, Rvalue::Use(_) | Rvalue::Cast(_, _, _))
                && destination
                    .as_local()
                    .is_some_and(|local| locals.contains(&local))
                && matches!(
                    destination.ty(body, tcx).ty.kind(),
                    TyKind::RawPtr(..) | TyKind::Ref(..)
                );
            if !transparent {
                return LocalPostCallEvidence::Unknown("local-proof-nontransparent-pointer-use");
            }
        }
    }
    // Every call receiving a descendant must retain the existing positive
    // no-retention certificate. This does not infer no-retention from a
    // missing export, and return-alias children need their own use evidence.
    let functions = ctx.slots.fn_local_slots.keys().copied().collect::<Vec<_>>();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let (func, arguments) = match &data.terminator().kind {
            TerminatorKind::Call { func, args, .. } => (func, args),
            TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } => {
                return LocalPostCallEvidence::Unknown("local-proof-opaque-control");
            }
            TerminatorKind::TailCall { args, .. }
                if args.iter().any(|arg| operand_in(&arg.node, &locals)) =>
            {
                return LocalPostCallEvidence::Unknown("local-proof-tail-call");
            }
            _ => continue,
        };
        for (index, argument) in arguments
            .iter()
            .enumerate()
            .filter(|(_, arg)| operand_in(&arg.node, &locals))
        {
            let Some(constant) = func.constant() else {
                return LocalPostCallEvidence::Unknown("local-proof-indirect-call");
            };
            let TyKind::FnDef(callee, _) = *constant.ty().kind() else {
                return LocalPostCallEvidence::Unknown("local-proof-indirect-call");
            };
            if let Some(callee) = callee
                .as_local()
                .filter(|callee| functions.contains(callee))
            {
                if !matches!(
                    ctx.retention.get(callee, index),
                    Some(RetentionVerdict::NoRetain { .. })
                ) {
                    return LocalPostCallEvidence::Unknown("local-proof-callee-retention");
                }
            } else {
                let key = super::raw_boundary::symbol_key(tcx, callee, &functions);
                let Some(target) = raw_target_type(tcx, argument.node.ty(body, tcx)) else {
                    return LocalPostCallEvidence::Unknown("local-proof-library-target");
                };
                let Ok(contract) = classify_contract(&key, index, &target) else {
                    return LocalPostCallEvidence::Unknown("local-proof-library-contract");
                };
                if contract.retention != RetentionContract::NoRetain {
                    return LocalPostCallEvidence::Unknown("local-proof-library-retention");
                }
                if contract.returns_alias_of == Some(index) {
                    let observation = super::return_alias::observe(
                        body,
                        Location {
                            block,
                            statement_index: data.statements.len(),
                        },
                    );
                    if observation.state != super::return_alias::ReturnUseState::Unused {
                        return LocalPostCallEvidence::Unknown("local-proof-return-alias-child");
                    }
                }
            }
        }
    }
    LocalPostCallEvidence::DeadUnprotected {
        checked_locals: locals.into_iter().collect(),
    }
}

fn operand_in(operand: &Operand<'_>, locals: &BTreeSet<Local>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place
            .as_local()
            .is_some_and(|local| locals.contains(&local)),
        Operand::Constant(_) => false,
    }
}

struct PointerOperands<'a> {
    locals: &'a BTreeSet<Local>,
    found: bool,
}

impl<'tcx> Visitor<'tcx> for PointerOperands<'_> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, _location: Location) {
        self.found |= operand_in(operand, self.locals);
    }
}
