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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReallocSsaUnsupported {
    Lifecycle(ReallocUnsupported),
    MultipleSites,
    StaleSite,
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
pub(crate) fn plan_body<'tcx>(
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
            _ => return Err(error(ReallocSsaUnsupported::StaleSite)),
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
        if destination.as_local() != Some(transport.destination)
            || source != transport.source
            || aliases.contains_key(&transport.destination)
        {
            return Err(error(ReallocSsaUnsupported::InvalidTransport(location)));
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
        if definitions.call_arg_temps.contains(&local)
            || !definitions.locals_with_defs.contains(local)
            || definitions.def_sites[local].is_empty()
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
    });
    Ok(continuation_plans)
}
