//! Owned MIR evidence for the descendants of a sealed returned-alias call.
//!
//! This layer classifies access and outward sinks. It grants no retention
//! certificate, model kind, bridge tier, or source transformation.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, Local, Location, Operand, Place, ProjectionElem, RETURN_PLACE,
        Rvalue, Statement, StatementKind, TerminatorKind,
        visit::{NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};

use super::{
    raw_boundary::{raw_target_type, symbol_key},
    raw_boundary_contracts::{
        ArgumentContract, ArgumentExtent, OwnershipContract, PointeeAccess, RetentionContract,
        classify_contract,
    },
    return_alias::{self, ReturnUseObservation},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ReturnedChildKey {
    pub caller: LocalDefId,
    pub call: Location,
    pub callee: DefId,
    pub parent_argument_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ChildRoot {
    Local(Local),
    Unknown {
        local: Option<Local>,
        reason: ChildUnknownReason,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ChildEdgeKind {
    Copy,
    PointerCast,
    ReturnedAlias {
        callee: DefId,
        parent_argument_index: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ChildEdge {
    pub location: Location,
    pub from: Local,
    pub to: Local,
    pub kind: ChildEdgeKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ChildUseKind {
    PointerCopy,
    PointerCast,
    PointerComparison,
    PointeeRead,
    ReturnedAliasArgument {
        callee: DefId,
        argument_index: usize,
    },
    KnownReadCall {
        callee: DefId,
        argument_index: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CheckedChildUse {
    pub location: Location,
    pub local: Local,
    pub kind: ChildUseKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ChildWriteKind {
    PointeeStore,
    KnownWriteCall {
        callee: DefId,
        argument_index: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ChildWriteSite {
    pub location: Location,
    pub local: Local,
    pub kind: ChildWriteKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ChildUnknownReason {
    ParentNotPlainLocal,
    DestinationNotPlainLocal,
    RedefinedLocal,
    OpaquePointerUse,
    OpaqueCall,
    UnmodeledCast,
    ProjectedPointerValue,
    ControlFlowCycle,
    MissingUseCoverage,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ChildFrontier {
    pub location: Location,
    pub local: Option<Local>,
    pub reason: ChildUnknownReason,
    pub callee: Option<DefId>,
    pub argument_index: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ChildAccess {
    Unused,
    /// Every pointer-value use in the reachable descendant graph is checked;
    /// absence of a write row alone can never construct this verdict.
    ReadOnly {
        checked_uses: Vec<CheckedChildUse>,
    },
    /// Positive write evidence survives an additional unknown frontier.
    Writes {
        sites: Vec<ChildWriteSite>,
        unknown_frontiers: Vec<ChildFrontier>,
    },
    Unknown {
        frontiers: Vec<ChildFrontier>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ChildSinkKind {
    FieldStore,
    GlobalStore,
    Return,
    ProjectedStore,
    RetainingCall {
        callee: DefId,
        argument_index: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ChildOutwardSink {
    pub location: Location,
    pub local: Local,
    pub kind: ChildSinkKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReturnedChildEvidence {
    pub key: ReturnedChildKey,
    pub contract_provenance: &'static str,
    pub initial: ReturnUseObservation,
    pub parent: ChildRoot,
    pub destination: ChildRoot,
    pub edges: Vec<ChildEdge>,
    pub access: ChildAccess,
    /// Positive sinks are independent of access completeness and never erased
    /// by an opaque use, redefinition, or other unknown frontier.
    pub outward_sinks: Vec<ChildOutwardSink>,
}

/// Inspect the original MIR once for each exact sealed returned-parent call.
/// This does not derive or query a model, and never changes retention.
pub(crate) fn derive(
    tcx: TyCtxt<'_>,
    caller: LocalDefId,
    call: Location,
) -> Vec<ReturnedChildEvidence> {
    let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
    let Some(data) = body.basic_blocks.get(call.block) else { return Vec::new() };
    if call.statement_index != data.statements.len() {
        return Vec::new();
    }
    let (func, arguments, destination, target) = match &data.terminator().kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => (func, &args[..], Some(*destination), *target),
        TerminatorKind::TailCall { func, args, .. } => (func, &args[..], None, None),
        _ => return Vec::new(),
    };
    let Some(callee) = resolved(func) else { return Vec::new() };
    let functions = tcx.hir_body_owners().collect::<Vec<_>>();
    arguments
        .iter()
        .enumerate()
        .filter_map(|(index, argument)| {
            let contract = contract_at(tcx, &body, &functions, callee, index, &argument.node)?;
            // returns_alias_of is function-level metadata: a non-parent argument
            // must not inherit the returned child's access or retention.
            if contract.returns_alias_of != Some(index) {
                return None;
            }
            Some(walk(
                tcx,
                &body,
                &functions,
                ReturnedChildKey {
                    caller,
                    call,
                    callee,
                    parent_argument_index: index,
                },
                contract,
                &argument.node,
                destination,
                target,
            ))
        })
        .collect()
}

/// **K18'/OAP-CHILD-ACCESS.** The same descendant walk, for a callee with no
/// pinned contract row.
///
/// Without a row we cannot know whether the callee's return derives from this
/// argument, so we assume it MAY -- that is the conservative direction -- and
/// let the walk report what the caller then does with the result. The point is
/// the difference between "no evidence" and "evidence of no write": passing
/// `None` for a child's access makes every shared subject hold, while a walk
/// that finds the child unused or only read keeps it admitted.
///
/// Only argument positions whose own type is a pointer are considered, and only
/// when `may_yield` says the callee can hand a pointer back at all. The
/// synthesized contract is neutral: unknown retention, no pointee access of its
/// own, and `returns_alias_of` set to this argument precisely because that is
/// the assumption being made.
pub(crate) fn derive_type_backed<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    call: Location,
    may_yield: &dyn Fn(DefId) -> bool,
) -> Vec<ReturnedChildEvidence> {
    let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
    let Some(data) = body.basic_blocks.get(call.block) else { return Vec::new() };
    if call.statement_index != data.statements.len() {
        return Vec::new();
    }
    let (func, arguments, destination, target) = match &data.terminator().kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } => (func, &args[..], Some(*destination), *target),
        TerminatorKind::TailCall { func, args, .. } => (func, &args[..], None, None),
        _ => return Vec::new(),
    };
    let Some(callee) = resolved(func) else { return Vec::new() };
    if !may_yield(callee) {
        return Vec::new();
    }
    let functions = tcx.hir_body_owners().collect::<Vec<_>>();
    arguments
        .iter()
        .enumerate()
        .filter_map(|(index, argument)| {
            if contract_at(tcx, &body, &functions, callee, index, &argument.node).is_some() {
                // The pinned row is the authority wherever it exists.
                return None;
            }
            if !pointer(argument.node.ty(&*body, tcx)) {
                return None;
            }
            Some(walk(
                tcx,
                &body,
                &functions,
                ReturnedChildKey {
                    caller,
                    call,
                    callee,
                    parent_argument_index: index,
                },
                ArgumentContract {
                    retention: RetentionContract::Unknown,
                    access: PointeeAccess::None,
                    ownership: OwnershipContract::BorrowView,
                    // K18' synthesizes a contract for a callee that HAS no
                    // pinned row, so nothing is known about how many elements
                    // the position consumes. `Unclassified` says exactly that;
                    // it is not `OneElement`, which would be a claim.
                    extent: ArgumentExtent::Unclassified,
                    returns_alias_of: Some(index),
                    provenance: "type-derived-return-carrier",
                },
                &argument.node,
                destination,
                target,
            ))
        })
        .collect()
}

fn resolved(operand: &Operand<'_>) -> Option<DefId> {
    let constant = operand.constant()?;
    let TyKind::FnDef(callee, _) = *constant.ty().kind() else { return None };
    Some(callee)
}

fn pointer(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(..) | TyKind::Ref(..))
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        Operand::Constant(_) => None,
    }
}

fn contract_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    functions: &[LocalDefId],
    callee: DefId,
    index: usize,
    operand: &Operand<'tcx>,
) -> Option<ArgumentContract> {
    let target = raw_target_type(tcx, operand.ty(body, tcx))?;
    classify_contract(&symbol_key(tcx, callee, functions), index, &target).ok()
}

fn location(block: BasicBlock, index: usize) -> Location {
    Location {
        block,
        statement_index: index,
    }
}

fn root(operand: Option<Local>, reason: ChildUnknownReason, known: Option<Local>) -> ChildRoot {
    operand.map_or(
        ChildRoot::Unknown {
            local: known,
            reason,
        },
        ChildRoot::Local,
    )
}

fn frontier(at: Location, local: Option<Local>, reason: ChildUnknownReason) -> ChildFrontier {
    ChildFrontier {
        location: at,
        local,
        reason,
        callee: None,
        argument_index: None,
    }
}

fn definitions(body: &Body<'_>) -> FxHashMap<Local, Vec<Location>> {
    let mut definitions = FxHashMap::<Local, Vec<Location>>::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (index, statement) in data.statements.iter().enumerate() {
            if let StatementKind::Assign(assignment) = &statement.kind
                && let Some(local) = assignment.0.as_local()
            {
                definitions
                    .entry(local)
                    .or_default()
                    .push(location(block, index));
            }
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && let Some(local) = destination.as_local()
        {
            definitions
                .entry(local)
                .or_default()
                .push(location(block, data.statements.len()));
        }
    }
    definitions
}

fn transfer(rvalue: &Rvalue<'_>) -> Option<(Local, ChildEdgeKind)> {
    match rvalue {
        Rvalue::Use(operand) => Some((operand_local(operand)?, ChildEdgeKind::Copy)),
        Rvalue::Cast(_, operand, ty) if pointer(*ty) => {
            Some((operand_local(operand)?, ChildEdgeKind::PointerCast))
        }
        _ => None,
    }
}

fn global_roots<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    definitions: &FxHashMap<Local, Vec<Location>>,
) -> FxHashSet<Local> {
    let mut globals = FxHashSet::default();
    let mut copies = Vec::new();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let Some(destination) = assignment.0.as_local() else { continue };
            if definitions
                .get(&destination)
                .is_none_or(|definitions| definitions.len() != 1)
            {
                continue;
            }
            match &assignment.1 {
                Rvalue::Use(Operand::Constant(constant))
                    if constant.check_static_ptr(tcx).is_some() =>
                {
                    globals.insert(destination);
                }
                Rvalue::ThreadLocalRef(_) => {
                    globals.insert(destination);
                }
                rvalue => {
                    if let Some((source, _)) = transfer(rvalue) {
                        copies.push((source, destination));
                    }
                }
            }
        }
    }
    let mut frontier = globals.iter().copied().collect::<Vec<_>>();
    while let Some(source) = frontier.pop() {
        for &(from, to) in &copies {
            if from == source && globals.insert(to) {
                frontier.push(to);
            }
        }
    }
    globals
}

fn sink_kind(place: Place<'_>, globals: &FxHashSet<Local>) -> ChildSinkKind {
    if place.as_local() == Some(RETURN_PLACE) {
        ChildSinkKind::Return
    } else if globals.contains(&place.local)
        && matches!(place.projection.first(), Some(ProjectionElem::Deref))
    {
        ChildSinkKind::GlobalStore
    } else if place
        .projection
        .iter()
        .any(|element| matches!(element, ProjectionElem::Field(..)))
    {
        ChildSinkKind::FieldStore
    } else {
        ChildSinkKind::ProjectedStore
    }
}

struct MirUse<'tcx> {
    place: Place<'tcx>,
    context: PlaceContext,
    at: Location,
}

struct Uses<'a, 'tcx> {
    tracked: &'a FxHashSet<Local>,
    uses: Vec<MirUse<'tcx>>,
}

impl<'tcx> Visitor<'tcx> for Uses<'_, 'tcx> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, at: Location) {
        if !matches!(statement.kind, StatementKind::FakeRead(..)) {
            self.super_statement(statement, at);
        }
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, at: Location) {
        let bookkeeping = !context.is_use()
            || matches!(
                context,
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::FakeBorrow | NonMutatingUseContext::PlaceMention
                )
            );
        let definition = place.projection.is_empty() && context.is_place_assignment();
        if self.tracked.contains(&place.local) && !bookkeeping && !definition {
            self.uses.push(MirUse {
                place: *place,
                context,
                at,
            });
        }
        self.super_place(place, context, at);
    }
}

fn core_null_test(tcx: TyCtxt<'_>, callee: DefId, index: usize, ty: Ty<'_>) -> bool {
    index == 0
        && pointer(ty)
        && !callee.is_local()
        && tcx.crate_name(callee.krate).as_str() == "core"
        && tcx.def_kind(callee) == rustc_hir::def::DefKind::AssocFn
        && tcx.item_name(callee).as_str() == "is_null"
}

fn walk<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    functions: &[LocalDefId],
    key: ReturnedChildKey,
    contract: ArgumentContract,
    parent_operand: &Operand<'tcx>,
    destination: Option<Place<'tcx>>,
    target: Option<BasicBlock>,
) -> ReturnedChildEvidence {
    let initial = return_alias::observe(body, key.call);
    let parent = root(
        operand_local(parent_operand),
        ChildUnknownReason::ParentNotPlainLocal,
        parent_operand.place().map(|place| place.local),
    );
    let destination_root = root(
        destination
            .and_then(|place| place.as_local())
            .filter(|local| pointer(body.local_decls[*local].ty)),
        ChildUnknownReason::DestinationNotPlainLocal,
        destination.map(|place| place.local),
    );
    let mut unknowns = Vec::new();
    for root in [&parent, &destination_root] {
        if let ChildRoot::Unknown { local, reason } = root {
            unknowns.push(frontier(key.call, *local, *reason));
        }
    }
    let definitions = definitions(body);
    let globals = global_roots(tcx, body, &definitions);
    let mut outward_sinks = Vec::new();
    if destination.is_none()
        && matches!(
            body.basic_blocks[key.call.block].terminator().kind,
            TerminatorKind::TailCall { .. }
        )
    {
        outward_sinks.push(ChildOutwardSink {
            location: key.call,
            local: operand_local(parent_operand).unwrap_or(RETURN_PLACE),
            kind: ChildSinkKind::Return,
        });
    }
    if let Some(destination) = destination
        && (destination.as_local().is_none() || destination.local == RETURN_PLACE)
    {
        outward_sinks.push(ChildOutwardSink {
            location: key.call,
            local: destination.local,
            kind: sink_kind(destination, &globals),
        });
        unknowns.push(frontier(
            key.call,
            Some(destination.local),
            ChildUnknownReason::OpaquePointerUse,
        ));
    }
    let mut reachable = BTreeSet::new();
    let mut pending = target.into_iter().collect::<Vec<_>>();
    while let Some(block) = pending.pop() {
        if reachable.insert(block) {
            if let Some(data) = body.basic_blocks.get(block) {
                pending.extend(data.terminator().successors());
            } else {
                unknowns.push(frontier(
                    key.call,
                    None,
                    ChildUnknownReason::MissingUseCoverage,
                ));
            }
        }
    }
    if target.is_none() {
        unknowns.push(frontier(
            key.call,
            None,
            ChildUnknownReason::MissingUseCoverage,
        ));
    }
    if reachable.contains(&key.call.block) {
        unknowns.push(frontier(
            key.call,
            destination.map(|place| place.local),
            ChildUnknownReason::ControlFlowCycle,
        ));
    }

    // All possible transparent edges are collected before the reachable
    // descendant closure. Multiple definitions stay explicit uncertainty.
    let mut candidates = Vec::new();
    for &block in &reachable {
        let Some(data) = body.basic_blocks.get(block) else { continue };
        for (index, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            if let Some(to) = assignment.0.as_local()
                && pointer(body.local_decls[to].ty)
                && let Some((from, kind)) = transfer(&assignment.1)
                && pointer(body.local_decls[from].ty)
            {
                candidates.push(ChildEdge {
                    location: location(block, index),
                    from,
                    to,
                    kind,
                });
            }
        }
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
            && let Some(callee) = resolved(func)
            && let Some(to) = destination.as_local()
            && pointer(body.local_decls[to].ty)
        {
            for (index, argument) in args.iter().enumerate() {
                if let Some(from) = operand_local(&argument.node)
                    && contract_at(tcx, body, functions, callee, index, &argument.node)
                        .is_some_and(|contract| contract.returns_alias_of == Some(index))
                {
                    candidates.push(ChildEdge {
                        location: location(block, data.statements.len()),
                        from,
                        to,
                        kind: ChildEdgeKind::ReturnedAlias {
                            callee,
                            parent_argument_index: index,
                        },
                    });
                }
            }
        }
    }
    let mut tracked = FxHashSet::default();
    let mut pending = destination
        .and_then(|place| place.as_local())
        .into_iter()
        .collect::<Vec<_>>();
    while let Some(local) = pending.pop() {
        if tracked.insert(local) {
            pending.extend(
                candidates
                    .iter()
                    .filter(|edge| edge.from == local)
                    .map(|edge| edge.to),
            );
        }
    }
    let mut edges = candidates
        .into_iter()
        .filter(|edge| tracked.contains(&edge.from))
        .collect::<Vec<_>>();
    for &local in &tracked {
        if let Some(definitions) = definitions.get(&local)
            && definitions.len() != 1
        {
            for &at in definitions {
                unknowns.push(frontier(
                    at,
                    Some(local),
                    ChildUnknownReason::RedefinedLocal,
                ));
            }
        }
    }
    let mut uses = Uses {
        tracked: &tracked,
        uses: Vec::new(),
    };
    for &block in &reachable {
        let Some(data) = body.basic_blocks.get(block) else { continue };
        for (index, statement) in data.statements.iter().enumerate() {
            uses.visit_statement(statement, location(block, index));
        }
        uses.visit_terminator(data.terminator(), location(block, data.statements.len()));
    }
    let observed_use_count = uses.uses.len();
    let mut checked_uses = Vec::new();
    let mut writes = Vec::new();
    for observed in uses.uses {
        let local = observed.place.local;
        let data = &body.basic_blocks[observed.at.block];
        let assignment = data
            .statements
            .get(observed.at.statement_index)
            .and_then(|statement| {
                if let StatementKind::Assign(assignment) = &statement.kind {
                    Some(&**assignment)
                } else {
                    None
                }
            });
        if !observed.place.projection.is_empty() {
            if matches!(
                observed.place.projection.first(),
                Some(ProjectionElem::Deref)
            ) && observed.context.is_place_assignment()
            {
                writes.push(ChildWriteSite {
                    location: observed.at,
                    local,
                    kind: ChildWriteKind::PointeeStore,
                });
            } else if matches!(observed.context, PlaceContext::NonMutatingUse(
                NonMutatingUseContext::Copy | NonMutatingUseContext::Move))
                // A whole aggregate copy can hide pointer fields whose later
                // uses are outside this depth-zero graph. Only scalar loads
                // establish complete read coverage here; no deep lineage is
                // inferred from the aggregate's top-level type.
                && matches!(observed.place.ty(body, tcx).ty.kind(),
                    TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_))
            {
                checked_uses.push(CheckedChildUse {
                    location: observed.at,
                    local,
                    kind: ChildUseKind::PointeeRead,
                });
            } else {
                unknowns.push(frontier(
                    observed.at,
                    Some(local),
                    ChildUnknownReason::ProjectedPointerValue,
                ));
            }
            continue;
        }
        if let Some((destination, rvalue)) = assignment {
            if destination.as_local() == Some(RETURN_PLACE)
                || !destination.projection.is_empty()
                || matches!(rvalue, Rvalue::Aggregate(..))
            {
                outward_sinks.push(ChildOutwardSink {
                    location: observed.at,
                    local,
                    kind: if matches!(rvalue, Rvalue::Aggregate(..)) {
                        ChildSinkKind::FieldStore
                    } else {
                        sink_kind(*destination, &globals)
                    },
                });
                unknowns.push(frontier(
                    observed.at,
                    Some(local),
                    ChildUnknownReason::ProjectedPointerValue,
                ));
            } else if let Some(edge) = edges
                .iter()
                .find(|edge| edge.location == observed.at && edge.from == local)
            {
                let kind = match edge.kind {
                    ChildEdgeKind::Copy => ChildUseKind::PointerCopy,
                    ChildEdgeKind::PointerCast => ChildUseKind::PointerCast,
                    ChildEdgeKind::ReturnedAlias {
                        callee,
                        parent_argument_index,
                    } => ChildUseKind::ReturnedAliasArgument {
                        callee,
                        argument_index: parent_argument_index,
                    },
                };
                checked_uses.push(CheckedChildUse {
                    location: observed.at,
                    local,
                    kind,
                });
            } else if matches!(
                rvalue,
                Rvalue::BinaryOp(
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge,
                    _
                )
            ) {
                checked_uses.push(CheckedChildUse {
                    location: observed.at,
                    local,
                    kind: ChildUseKind::PointerComparison,
                });
            } else {
                unknowns.push(frontier(
                    observed.at,
                    Some(local),
                    if matches!(rvalue, Rvalue::Cast(..)) {
                        ChildUnknownReason::UnmodeledCast
                    } else {
                        ChildUnknownReason::OpaquePointerUse
                    },
                ));
            }
            continue;
        }
        let (func, arguments, call_destination) = match &data.terminator().kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } if observed.at.statement_index == data.statements.len() => {
                (func, &args[..], Some(*destination))
            }
            TerminatorKind::TailCall { func, args, .. }
                if observed.at.statement_index == data.statements.len() =>
            {
                (func, &args[..], None)
            }
            _ => {
                unknowns.push(frontier(
                    observed.at,
                    Some(local),
                    ChildUnknownReason::OpaquePointerUse,
                ));
                continue;
            }
        };
        let callee = resolved(func);
        let positions = arguments
            .iter()
            .enumerate()
            .filter(|(_, argument)| operand_local(&argument.node) == Some(local))
            .collect::<Vec<_>>();
        if positions.is_empty() {
            unknowns.push(frontier(
                observed.at,
                Some(local),
                ChildUnknownReason::OpaquePointerUse,
            ));
        }
        for (index, argument) in positions {
            let Some(callee) = callee else {
                let mut gap = frontier(observed.at, Some(local), ChildUnknownReason::OpaqueCall);
                gap.argument_index = Some(index);
                unknowns.push(gap);
                continue;
            };
            if core_null_test(tcx, callee, index, argument.node.ty(body, tcx)) {
                checked_uses.push(CheckedChildUse {
                    location: observed.at,
                    local,
                    kind: ChildUseKind::PointerComparison,
                });
                continue;
            }
            let Some(contract) = contract_at(tcx, body, functions, callee, index, &argument.node)
            else {
                unknowns.push(ChildFrontier {
                    location: observed.at,
                    local: Some(local),
                    reason: ChildUnknownReason::OpaqueCall,
                    callee: Some(callee),
                    argument_index: Some(index),
                });
                continue;
            };
            if contract.retention != RetentionContract::NoRetain {
                if contract.retention == RetentionContract::Retains {
                    outward_sinks.push(ChildOutwardSink {
                        location: observed.at,
                        local,
                        kind: ChildSinkKind::RetainingCall {
                            callee,
                            argument_index: index,
                        },
                    });
                }
                unknowns.push(ChildFrontier {
                    location: observed.at,
                    local: Some(local),
                    reason: ChildUnknownReason::OpaqueCall,
                    callee: Some(callee),
                    argument_index: Some(index),
                });
            }
            match contract.access {
                PointeeAccess::Write | PointeeAccess::Stream | PointeeAccess::Lifecycle => writes
                    .push(ChildWriteSite {
                        location: observed.at,
                        local,
                        kind: ChildWriteKind::KnownWriteCall {
                            callee,
                            argument_index: index,
                        },
                    }),
                PointeeAccess::None | PointeeAccess::Read => {
                    checked_uses.push(CheckedChildUse {
                        location: observed.at,
                        local,
                        kind: if contract.returns_alias_of == Some(index) {
                            ChildUseKind::ReturnedAliasArgument {
                                callee,
                                argument_index: index,
                            }
                        } else {
                            ChildUseKind::KnownReadCall {
                                callee,
                                argument_index: index,
                            }
                        },
                    });
                }
            }
            if contract.returns_alias_of == Some(index) {
                if let Some(destination) = call_destination {
                    if destination.as_local().is_none() || destination.local == RETURN_PLACE {
                        outward_sinks.push(ChildOutwardSink {
                            location: observed.at,
                            local,
                            kind: sink_kind(destination, &globals),
                        });
                        unknowns.push(frontier(
                            observed.at,
                            Some(local),
                            ChildUnknownReason::DestinationNotPlainLocal,
                        ));
                    } else if !edges.iter().any(|edge| {
                        edge.location == observed.at
                            && edge.from == local
                            && matches!(edge.kind, ChildEdgeKind::ReturnedAlias { .. })
                    }) {
                        unknowns.push(frontier(
                            observed.at,
                            Some(local),
                            ChildUnknownReason::MissingUseCoverage,
                        ));
                    }
                } else {
                    outward_sinks.push(ChildOutwardSink {
                        location: observed.at,
                        local,
                        kind: ChildSinkKind::Return,
                    });
                    unknowns.push(frontier(
                        observed.at,
                        Some(local),
                        ChildUnknownReason::DestinationNotPlainLocal,
                    ));
                }
            }
        }
    }
    // A pointer-valued return is a positive outward use even though Return
    // has no explicit Operand for the ordinary MIR place visitor to visit.
    if tracked.contains(&RETURN_PLACE)
        && outward_sinks
            .iter()
            .all(|sink| sink.kind != ChildSinkKind::Return)
    {
        outward_sinks.push(ChildOutwardSink {
            location: key.call,
            local: RETURN_PLACE,
            kind: ChildSinkKind::Return,
        });
        unknowns.push(frontier(
            key.call,
            Some(RETURN_PLACE),
            ChildUnknownReason::OpaquePointerUse,
        ));
    }
    edges.sort_by_key(|edge| {
        (
            edge.location.block.as_u32(),
            edge.location.statement_index,
            edge.from.as_u32(),
            edge.to.as_u32(),
        )
    });
    edges.dedup();
    checked_uses.sort_by_key(|site| {
        (
            site.location.block.as_u32(),
            site.location.statement_index,
            site.local.as_u32(),
        )
    });
    checked_uses.dedup();
    writes.sort_by_key(|site| {
        (
            site.location.block.as_u32(),
            site.location.statement_index,
            site.local.as_u32(),
        )
    });
    writes.dedup();
    unknowns.sort_by_key(|site| {
        (
            site.location.block.as_u32(),
            site.location.statement_index,
            site.local.map(Local::as_u32),
        )
    });
    unknowns.dedup();
    outward_sinks.sort_by_key(|site| {
        (
            site.location.block.as_u32(),
            site.location.statement_index,
            site.local.as_u32(),
        )
    });
    outward_sinks.dedup();
    let access = if !writes.is_empty() {
        ChildAccess::Writes {
            sites: writes,
            unknown_frontiers: unknowns,
        }
    } else if !unknowns.is_empty() {
        ChildAccess::Unknown {
            frontiers: unknowns,
        }
    } else if observed_use_count == 0 && outward_sinks.is_empty() {
        ChildAccess::Unused
    } else if !checked_uses.is_empty() {
        ChildAccess::ReadOnly { checked_uses }
    } else {
        ChildAccess::Unknown {
            frontiers: vec![frontier(
                key.call,
                None,
                ChildUnknownReason::MissingUseCoverage,
            )],
        }
    };
    ReturnedChildEvidence {
        key,
        contract_provenance: contract.provenance,
        initial,
        parent,
        destination: destination_root,
        edges,
        access,
        outward_sinks,
    }
}
