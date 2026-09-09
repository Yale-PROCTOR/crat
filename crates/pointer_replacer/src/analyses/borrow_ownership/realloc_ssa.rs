//! Ownership edge plans for a validated source realloc result branch.
//!
//! MIR stays immutable. The normal SSA join placement sees the additional
//! branch-entry definitions; inference supplies their outcome-specific values.

use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::mir::{
    BasicBlock, Body, CastKind, Local, Location, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_mir_dataflow::Analysis;

use super::{
    CrateCtxt,
    ptr::Measurable,
    realloc::{self, OldInput, ReallocResult, ReallocSite, ReallocSiteKey, ReallocUnsupported},
    source_events::{SourcePhase, addressed_locals},
    ssa::consume::Definitions,
};
use crate::analyses::{
    liveness::MaybeLiveLocals,
    mir::{CallKind, TerminatorExt},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReallocEdgeOperation {
    Old {
        local: Local,
    },
    Result {
        local: Local,
    },
    Transfer {
        source: Local,
        destination: Local,
        location: Location,
        by_move: bool,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReallocSsaPlan {
    pub(crate) site: ReallocSite,
    /// Normalized SSA owner; `site` retains the original source-call operand.
    pub(crate) old: Option<Local>,
    pub(crate) operations: Vec<ReallocEdgeOperation>,
    pub(crate) coverage_hold: Option<coverage_hold::Reason>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReallocSsaUnsupported {
    Lifecycle(ReallocUnsupported),
    MultipleSites,
    StaleSite,
    UnsupportedControlFlow(BasicBlock),
    UnsupportedTransport(Location),
    UnsupportedOwnershipCarrier(Local),
    AmbiguousOldOwner(Local),
    ProjectedOldOwner(Local),
    CrossBlockOldProxy(Local),
    OldOwnerOverwritten(Local),
    MissingOwnershipDefinition(Local),
    OwnershipMeasure { local: Local, measure: u32 },
    ExtraPredecessor(BasicBlock),
    OutcomeReentry(BasicBlock),
    InvalidTransport(Location),
    LiveOutcomeJoin { block: BasicBlock, local: Local },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReallocSsaError {
    pub(crate) site: ReallocSiteKey,
    pub(crate) reason: ReallocSsaUnsupported,
}

fn pointer_transfer(value: &Rvalue<'_>) -> Option<(Local, bool)> {
    let operand = match value {
        Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => operand,
        _ => return None,
    };
    operand
        .place()
        .and_then(|place| place.as_local())
        .map(|local| (local, matches!(operand, Operand::Move(_))))
}

/// Compiler call-argument proxies are not ownership variables. Normalize only
/// unique bare copies/casts in the call block, without crossing a source write.
fn old_owner(
    body: &Body<'_>,
    definitions: &Definitions,
    mut local: Local,
    call: Location,
) -> Result<Local, ReallocSsaUnsupported> {
    let mut seen = BTreeSet::new();
    let mut before = call.statement_index;
    while definitions.call_arg_temps.contains(&local) {
        if !seen.insert(local) {
            return Err(ReallocSsaUnsupported::AmbiguousOldOwner(local));
        }
        let mut definition = None;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(box (destination, value)) = &statement.kind else {
                    continue;
                };
                if destination.local != local {
                    continue;
                }
                if !destination.projection.is_empty() {
                    return Err(ReallocSsaUnsupported::ProjectedOldOwner(local));
                }
                let source = pointer_transfer(value)
                    .ok_or(ReallocSsaUnsupported::ProjectedOldOwner(local))?
                    .0;
                if definition
                    .replace((block, statement_index, source))
                    .is_some()
                {
                    return Err(ReallocSsaUnsupported::AmbiguousOldOwner(local));
                }
            }
            if matches!(&data.terminator().kind,
                TerminatorKind::Call { destination, .. } if destination.local == local)
            {
                return Err(ReallocSsaUnsupported::AmbiguousOldOwner(local));
            }
        }
        let (block, statement_index, source) =
            definition.ok_or(ReallocSsaUnsupported::AmbiguousOldOwner(local))?;
        if block != call.block || statement_index >= before {
            return Err(ReallocSsaUnsupported::CrossBlockOldProxy(local));
        }
        if !body.local_decls[local].ty.is_raw_ptr() || !body.local_decls[source].ty.is_raw_ptr() {
            return Err(ReallocSsaUnsupported::AmbiguousOldOwner(local));
        }
        for statement in
            &body.basic_blocks[block].statements[statement_index + 1..call.statement_index]
        {
            if matches!(&statement.kind,
                StatementKind::Assign(box (destination, _))
                    if destination.as_local() == Some(source))
                || matches!(&statement.kind, StatementKind::StorageDead(dead) if *dead == source)
            {
                return Err(ReallocSsaUnsupported::OldOwnerOverwritten(source));
            }
        }
        before = statement_index;
        local = source;
    }
    Ok(local)
}

/// Accept only the supplied body's single supported site. An error leaves the
/// definition sets untouched, so a typed decline cannot partially install SSA.
fn plan_body_exact<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    body: &Body<'tcx>,
    definitions: &mut Definitions,
    sites: &[ReallocSite],
) -> Result<Vec<ReallocSsaPlan>, ReallocSsaError> {
    let function = crate_ctxt.tcx.def_path_str(body.source.def_id());
    let continuations: Vec<_> = sites
        .iter()
        .filter(|site| site.key.function == function)
        .collect();
    let mut continuation_plans = continuations
        .into_iter()
        .filter(|site| !matches!(site.result, ReallocResult::DirectBranch(_)))
        .map(|site| {
            let error = |reason| ReallocSsaError {
                site: site.key.clone(),
                reason,
            };
            realloc::classify(site)
                .map_err(|reason| error(ReallocSsaUnsupported::Lifecycle(reason)))?;
            let continuation = site
                .result
                .continuation()
                .ok_or_else(|| error(ReallocSsaUnsupported::StaleSite))?;
            let block = BasicBlock::from_u32(site.key.block);
            let Some(data) = body.basic_blocks.get(block) else {
                return Err(error(ReallocSsaUnsupported::StaleSite));
            };
            let Some(call) = data.terminator().as_call(crate_ctxt.tcx) else {
                return Err(error(ReallocSsaUnsupported::StaleSite));
            };
            if site.key.statement != data.statements.len()
                || !matches!(call.func, CallKind::LibC(name) if name.as_str() == "realloc")
                || super::export::PlaceKey::from_place(call.destination)
                    != continuation.result_place
                || call
                    .args
                    .first()
                    .and_then(|arg| arg.node.place())
                    .map(super::export::PlaceKey::from_place)
                    != continuation.old_place
            {
                return Err(error(ReallocSsaUnsupported::StaleSite));
            }
            // R219 continuations have no conditional CFG edge to rename. The
            // ordinary ownership boundary carries a success qualifier plus
            // explicit source-case/loss receipts, including projected places.
            Ok(ReallocSsaPlan {
                site: site.clone(),
                old: continuation.old,
                operations: Vec::new(),
                coverage_hold: None,
            })
        })
        .collect::<Result<Vec<_>, ReallocSsaError>>()?;
    let mut sites = sites.iter().filter(|site| {
        site.key.function == function && matches!(site.result, ReallocResult::DirectBranch(_))
    });
    let Some(site) = sites.next() else { return Ok(continuation_plans) };
    let error = |reason| ReallocSsaError {
        site: site.key.clone(),
        reason,
    };
    if sites.next().is_some() {
        return Err(error(ReallocSsaUnsupported::MultipleSites));
    }
    realloc::classify(site).map_err(|reason| error(ReallocSsaUnsupported::Lifecycle(reason)))?;
    let ReallocResult::DirectBranch(branch) = &site.result else {
        return Err(error(ReallocSsaUnsupported::StaleSite));
    };
    let call_block = BasicBlock::from_u32(site.key.block);
    if call_block.as_usize() >= body.basic_blocks.len()
        || branch.test.block.as_usize() >= body.basic_blocks.len()
        || branch.success.as_usize() >= body.basic_blocks.len()
        || branch.failure.as_usize() >= body.basic_blocks.len()
        || site.key.phase != SourcePhase::Call
        || site.key.statement != body.basic_blocks[call_block].statements.len()
        || branch.test.statement_index != body.basic_blocks[branch.test.block].statements.len()
    {
        return Err(error(ReallocSsaUnsupported::StaleSite));
    }
    let terminator = body.basic_blocks[call_block].terminator();
    let Some(call) = terminator.as_call(crate_ctxt.tcx) else {
        return Err(error(ReallocSsaUnsupported::StaleSite));
    };
    let TerminatorKind::Call {
        target: Some(first),
        ..
    } = &terminator.kind
    else {
        return Err(error(ReallocSsaUnsupported::StaleSite));
    };
    if !matches!(call.func, CallKind::LibC(name) if name.as_str() == "realloc")
        || call.destination.as_local() != Some(branch.result)
        || call
            .args
            .first()
            .and_then(|argument| argument.node.place())
            .and_then(|place| place.as_local())
            != branch.old
    {
        return Err(error(ReallocSsaUnsupported::StaleSite));
    }
    let old = if site.old_input == OldInput::KnownNull {
        None
    } else {
        Some(
            old_owner(
                body,
                definitions,
                branch
                    .old
                    .ok_or_else(|| error(ReallocSsaUnsupported::StaleSite))?,
                Location {
                    block: call_block,
                    statement_index: site.key.statement,
                },
            )
            .map_err(&error)?,
        )
    };
    if old == Some(branch.result) {
        return Err(error(ReallocSsaUnsupported::OldOwnerOverwritten(
            branch.result,
        )));
    }
    if let Some(old) = old
        && addressed_locals(body).contains(&old)
    {
        return Err(error(ReallocSsaUnsupported::AmbiguousOldOwner(old)));
    }

    let predecessors = body.basic_blocks.predecessors();
    let mut window = BTreeSet::from([call_block]);
    let mut previous = call_block;
    let mut block = *first;
    loop {
        if !window.insert(block) {
            return Err(error(ReallocSsaUnsupported::OutcomeReentry(block)));
        }
        if predecessors[block].iter().copied().collect::<BTreeSet<_>>()
            != BTreeSet::from([previous])
        {
            return Err(error(ReallocSsaUnsupported::ExtraPredecessor(block)));
        }
        let data = &body.basic_blocks[block];
        if let Some(old) = old {
            for statement in &data.statements {
                if matches!(&statement.kind,
                    StatementKind::Assign(box (destination, _))
                        if destination.as_local() == Some(old))
                    || matches!(&statement.kind, StatementKind::StorageDead(dead) if *dead == old)
                {
                    return Err(error(ReallocSsaUnsupported::OldOwnerOverwritten(old)));
                }
            }
            if matches!(&data.terminator().kind,
                TerminatorKind::Call { destination, .. } if destination.as_local() == Some(old))
            {
                return Err(error(ReallocSsaUnsupported::OldOwnerOverwritten(old)));
            }
        }
        if block == branch.test.block {
            break;
        }
        let next = match &data.terminator().kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Call {
                target: Some(target),
                ..
            } => *target,
            _ => return Err(error(ReallocSsaUnsupported::UnsupportedControlFlow(block))),
        };
        previous = block;
        block = next;
    }
    if !matches!(
        body.basic_blocks[branch.test.block].terminator().kind,
        TerminatorKind::SwitchInt { .. }
    ) {
        return Err(error(ReallocSsaUnsupported::StaleSite));
    }
    for entry in [branch.success, branch.failure] {
        if predecessors[entry].iter().copied().collect::<BTreeSet<_>>()
            != BTreeSet::from([branch.test.block])
        {
            return Err(error(ReallocSsaUnsupported::ExtraPredecessor(entry)));
        }
    }
    let mut pending = vec![branch.success, branch.failure];
    let mut visited = BTreeSet::new();
    while let Some(block) = pending.pop() {
        if window.contains(&block) {
            return Err(error(ReallocSsaUnsupported::OutcomeReentry(block)));
        }
        if visited.insert(block) {
            pending.extend(body.basic_blocks[block].terminator().successors());
        }
    }

    let mut operations = Vec::new();
    let mut affected = BTreeSet::from([branch.result]);
    if let Some(local) = old {
        operations.push(ReallocEdgeOperation::Old { local });
        affected.insert(local);
    }
    operations.push(ReallocEdgeOperation::Result {
        local: branch.result,
    });
    let mut aliases = BTreeMap::from([(branch.result, branch.result)]);
    for transport in &branch.transports {
        let location = transport.location;
        if !window.contains(&location.block) || location.block == call_block {
            return Err(error(ReallocSsaUnsupported::InvalidTransport(location)));
        }
        let statement = body.basic_blocks[location.block]
            .statements
            .get(location.statement_index)
            .ok_or_else(|| error(ReallocSsaUnsupported::InvalidTransport(location)))?;
        let StatementKind::Assign(box (destination, value)) = &statement.kind else {
            return Err(error(ReallocSsaUnsupported::InvalidTransport(location)));
        };
        let (source, by_move) = pointer_transfer(value)
            .ok_or_else(|| error(ReallocSsaUnsupported::InvalidTransport(location)))?;
        if destination.as_local() != Some(transport.destination) || source != transport.source {
            return Err(error(ReallocSsaUnsupported::InvalidTransport(location)));
        }
        if aliases.contains_key(&transport.destination) {
            return Err(error(ReallocSsaUnsupported::UnsupportedTransport(location)));
        }
        let source = *aliases
            .get(&source)
            .ok_or_else(|| error(ReallocSsaUnsupported::InvalidTransport(location)))?;
        if definitions.call_arg_temps.contains(&transport.destination) {
            aliases.insert(transport.destination, source);
        } else {
            operations.push(ReallocEdgeOperation::Transfer {
                source,
                destination: transport.destination,
                location,
                by_move,
            });
            aliases.insert(transport.destination, transport.destination);
            affected.insert(source);
            affected.insert(transport.destination);
        }
    }
    let measure = crate_ctxt
        .struct_ctxt
        .with_max_precision(super::BO_PRECISION);
    for &local in &affected {
        if definitions.call_arg_temps.contains(&local) {
            return Err(error(ReallocSsaUnsupported::UnsupportedOwnershipCarrier(
                local,
            )));
        }
        if !definitions.locals_with_defs.contains(local) || definitions.def_sites[local].is_empty()
        {
            return Err(error(ReallocSsaUnsupported::MissingOwnershipDefinition(
                local,
            )));
        }
        let count = measure.measure(body.local_decls[local].ty, 0);
        if count != 1 {
            return Err(error(ReallocSsaUnsupported::OwnershipMeasure {
                local,
                measure: count,
            }));
        }
    }
    // The bounded edge representation does not propagate conditional ownership
    // through a merged region that still uses these pointers. Refuse that
    // correlation explicitly; scope-finalization alone is not a source use.
    let reachable = |entry: BasicBlock| {
        let mut pending = vec![entry];
        let mut seen = BTreeSet::new();
        while let Some(block) = pending.pop() {
            if seen.insert(block) {
                pending.extend(body.basic_blocks[block].terminator().successors());
            }
        }
        seen
    };
    let success = reachable(branch.success);
    let failure = reachable(branch.failure);
    let common: BTreeSet<_> = success.intersection(&failure).copied().collect();
    let mut live = MaybeLiveLocals
        .iterate_to_fixpoint(crate_ctxt.tcx, body, None)
        .into_results_cursor(body);
    for &block in &common {
        if predecessors[block].iter().all(|pred| common.contains(pred)) {
            continue;
        }
        live.seek_before_primary_effect(Location {
            block,
            statement_index: 0,
        });
        if let Some(&local) = affected.iter().find(|local| live.get().contains(**local)) {
            return Err(error(ReallocSsaUnsupported::LiveOutcomeJoin {
                block,
                local,
            }));
        }
    }
    for local in affected {
        definitions.def_sites[local].insert(branch.success);
        definitions.def_sites[local].insert(branch.failure);
    }
    continuation_plans.push(ReallocSsaPlan {
        site: site.clone(),
        old,
        operations,
        coverage_hold: None,
    });
    Ok(continuation_plans)
}

/// R245/R246 recovery validates source identity before converting a coverage limit.
pub(crate) fn plan_body<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    body: &Body<'tcx>,
    definitions: &mut Definitions,
    sites: &[ReallocSite],
) -> Result<Vec<ReallocSsaPlan>, ReallocSsaError> {
    let function = crate_ctxt.tcx.def_path_str(body.source.def_id());
    let relevant = sites
        .iter()
        .filter(|site| site.key.function == function)
        .collect::<Vec<_>>();
    // A realloc-free body needs no fresh inventory materialization. An empty
    // supplied inventory for an actual realloc body must reach completeness.
    if relevant.is_empty()
        && !body.basic_blocks.iter().any(|data| {
            data.terminator().as_call(crate_ctxt.tcx).is_some_and(
                |call| matches!(call.func, CallKind::LibC(name) if name.as_str() == "realloc"),
            )
        })
    {
        return plan_body_exact(crate_ctxt, body, definitions, sites);
    }
    let program = crate::utils::rustc::RustProgram {
        tcx: crate_ctxt.tcx,
        functions: crate_ctxt.fns().iter().map(|f| f.expect_local()).collect(),
        structs: Vec::new(),
    };
    let actual = realloc::collect_sites(&program);
    for site in &relevant {
        if actual.iter().find(|row| row.key == site.key) != Some(*site)
            || relevant.iter().filter(|row| row.key == site.key).count() != 1
        {
            return Err(ReallocSsaError {
                site: site.key.clone(),
                reason: ReallocSsaUnsupported::StaleSite,
            });
        }
    }
    let actual_count = actual
        .iter()
        .filter(|site| site.key.function == function)
        .count();
    if actual_count != relevant.len() {
        return Err(ReallocSsaError {
            site: actual
                .iter()
                .find(|site| site.key.function == function)
                .or_else(|| relevant.first().copied())
                .expect("inventory count mismatch has a source or supplied site")
                .key
                .clone(),
            reason: ReallocSsaUnsupported::StaleSite,
        });
    }
    if let Some(site) = relevant
        .iter()
        .find(|site| site.size == realloc::ReallocSize::Unknown)
    {
        return Err(ReallocSsaError {
            site: site.key.clone(),
            reason: ReallocSsaUnsupported::Lifecycle(ReallocUnsupported::UnknownSize),
        });
    }
    #[cfg(test)]
    let planned = super::wrapper_fault_tests::recovery_error(relevant.first().copied())
        .map(Err)
        .unwrap_or_else(|| plan_body_exact(crate_ctxt, body, definitions, sites));
    #[cfg(not(test))]
    let planned = plan_body_exact(crate_ctxt, body, definitions, sites);
    match planned {
        Ok(plans) => Ok(plans),
        Err(error) => {
            let Some(reason) = coverage_hold::Reason::from_error(&error.reason) else {
                return Err(error);
            };
            // No definition set is mutated before the exact planner succeeds.
            // Hold every affected call in this function, keeping its original
            // source site/size/outcome evidence and source timing untouched.
            Ok(relevant
                .into_iter()
                .map(|site| ReallocSsaPlan {
                    site: site.clone(),
                    old: None,
                    operations: Vec::new(),
                    coverage_hold: Some(reason),
                })
                .collect())
        }
    }
}

pub(crate) mod coverage_hold {
    use super::*;
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) enum Reason {
        MultipleSites,
        AmbiguousOldOwner,
        ProjectedOldOwner,
        CrossBlockOldProxy,
        OldOwnerOverwritten,
        OwnershipMeasure,
        ExtraPredecessor,
        OutcomeReentry,
        LiveOutcomeJoin,
        ControlFlow,
        Transport,
        OwnershipCarrier,
        ZeroSize,
        ResultTest,
    }
    impl Reason {
        pub(crate) fn label(self) -> &'static str {
            match self {
                Self::MultipleSites => "multiple-sites",
                Self::AmbiguousOldOwner => "ambiguous-old-owner",
                Self::ProjectedOldOwner => "projected-old-owner",
                Self::CrossBlockOldProxy => "cross-block-old-proxy",
                Self::OldOwnerOverwritten => "old-owner-overwritten",
                Self::OwnershipMeasure => "ownership-measure",
                Self::ExtraPredecessor => "extra-predecessor",
                Self::OutcomeReentry => "outcome-reentry",
                Self::LiveOutcomeJoin => "live-outcome-join",
                Self::ControlFlow => "control-flow",
                Self::Transport => "transport-representation",
                Self::OwnershipCarrier => "ownership-carrier",
                Self::ZeroSize => "zero-size-lifecycle",
                Self::ResultTest => "result-test",
            }
        }

        pub(crate) fn from_error(error: &ReallocSsaUnsupported) -> Option<Self> {
            Some(match error {
                ReallocSsaUnsupported::MultipleSites => Self::MultipleSites,
                ReallocSsaUnsupported::AmbiguousOldOwner(_) => Self::AmbiguousOldOwner,
                ReallocSsaUnsupported::ProjectedOldOwner(_) => Self::ProjectedOldOwner,
                ReallocSsaUnsupported::CrossBlockOldProxy(_) => Self::CrossBlockOldProxy,
                ReallocSsaUnsupported::OldOwnerOverwritten(_) => Self::OldOwnerOverwritten,
                ReallocSsaUnsupported::OwnershipMeasure { .. } => Self::OwnershipMeasure,
                ReallocSsaUnsupported::ExtraPredecessor(_) => Self::ExtraPredecessor,
                ReallocSsaUnsupported::OutcomeReentry(_) => Self::OutcomeReentry,
                ReallocSsaUnsupported::LiveOutcomeJoin { .. } => Self::LiveOutcomeJoin,
                ReallocSsaUnsupported::UnsupportedControlFlow(_) => Self::ControlFlow,
                ReallocSsaUnsupported::UnsupportedTransport(_) => Self::Transport,
                ReallocSsaUnsupported::UnsupportedOwnershipCarrier(_) => Self::OwnershipCarrier,
                ReallocSsaUnsupported::Lifecycle(ReallocUnsupported::ZeroSize) => Self::ZeroSize,
                ReallocSsaUnsupported::Lifecycle(
                    ReallocUnsupported::DiscardedResult | ReallocUnsupported::UnresolvedResultTest,
                ) => Self::ResultTest,
                _ => return None,
            })
        }
    }
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub(crate) struct Receipt {
        pub(crate) site: ReallocSiteKey,
        pub(crate) reason: Reason,
        pub(crate) slots: Vec<super::super::solver::SlotRef>,
    }
}

/// Apply only site-local ownership holds before linking SSA values to kinds.
pub(crate) fn constrain_coverage_holds<'tcx>(
    crate_ctxt: &CrateCtxt<'tcx>,
    body: &Body<'tcx>,
    slots: &super::crate_slots::CrateSlots,
    solver: &super::solver::KindSolver,
    plans: &[ReallocSsaPlan],
) {
    use super::{
        resolve::{ResolvedSlot, resolve_place},
        solver::SlotRef,
    };
    if !plans.iter().any(|plan| plan.coverage_hold.is_some()) {
        return;
    }
    let function = body.source.def_id().expect_local();
    let program = crate::utils::rustc::RustProgram {
        tcx: crate_ctxt.tcx,
        functions: crate_ctxt.fns().iter().map(|f| f.expect_local()).collect(),
        structs: Vec::new(),
    };
    let graph = super::retirement::local_outcome::copy_graph(&program, slots);
    for plan in plans {
        let Some(reason) = plan.coverage_hold else { continue };
        assert!(plan.operations.is_empty());
        let block = BasicBlock::from_u32(plan.site.key.block);
        let call = body.basic_blocks[block]
            .terminator()
            .as_call(crate_ctxt.tcx)
            .expect("validated held call");
        let mut pending = Vec::new();
        for place in std::iter::once(call.destination)
            .chain(call.args.first().and_then(|argument| argument.node.place()))
        {
            for depth in 0..super::crate_slots::MAX_SLOT_DEPTH {
                if let Some(resolved) = resolve_place(slots, function, body, place, depth, None) {
                    pending.push(match resolved {
                        ResolvedSlot::Local(id) => SlotRef::Local(function, id),
                        ResolvedSlot::Field(id) => SlotRef::Field(id),
                    });
                }
            }
        }
        let mut seen = rustc_hash::FxHashSet::default();
        while let Some(slot) = pending.pop() {
            if seen.insert(slot) {
                pending.extend(graph.get(&slot).into_iter().flatten().copied());
            }
        }
        let targets = seen
            .into_iter()
            .map(|slot| (super::l2::SlotKey::of(slot), slot))
            .collect::<BTreeMap<_, _>>()
            .into_values()
            .collect::<Vec<_>>();
        assert!(
            !targets.is_empty(),
            "held realloc has no represented operand/result: missing required slot mapping"
        );
        for &target in &targets {
            solver.assume(target, super::SlotKind::Raw);
        }
        super::export::record(|capture| {
            capture.realloc_coverage_holds.push(coverage_hold::Receipt {
                site: plan.site.key.clone(),
                reason,
                slots: targets,
            })
        });
    }
}
