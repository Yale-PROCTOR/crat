//! K18′, callee side: a descendant-free callee position.
//!
//! The type-backed child walk assumes a contract-less callee MAY hand back a
//! descendant of the argument and classifies what the caller then does with
//! the call's result; a callee returning no pointer local leaves it `Unknown`,
//! and one returning a FRESH pointer the caller later frees reads as `Writes`.
//! Both fire the shared-source hold `write-through-shared-view`. This module
//! answers the premise on the callee's own body: the argument's alias set has
//! a `NoRetain` certificate (the accepted retention instrument, transitive
//! through local callees) AND the body forms no non-transparent derivation of
//! that alias set (no address-of / raw address of a place under it, no
//! `Offset`, no aggregate capture, no cast to a non-pointer), returns none of
//! it, stores none of it through a projection, and every local callee that
//! receives an alias is descendant-free at that position in turn; a libc call
//! whose contract row says it returns an alias of the argument extends the
//! alias set with its result. No descendant then exists to hand back, and the
//! child access is `Unused` — the caller's use of a fresh result is its own
//! business.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{BinOp, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};

use super::decision::{
    raw_boundary::{RetentionVerdict, raw_target_type, symbol_key},
    raw_boundary_contracts::classify_contract,
    returned_child::{ChildAccess, ReturnedChildEvidence},
};
use crate::utils::rustc::RustProgram;

pub(crate) const PROVENANCE: &str = "k18-callee-descendant-free";

/// How a `core` raw-pointer method treats the pointer it receives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CorePointerCall {
    /// Takes the pointer by value and hands nothing back (`is_null`).
    NoRetain,
    /// Hands back the SAME allocation at another offset or spelling
    /// (`offset`, `add`, `sub`, `cast`, `cast_mut`, `cast_const`): the
    /// result is a transparent alias of the receiver, so the ordinary sinks
    /// decide what becomes of it. `wrapping_*` is deliberately left unknown:
    /// wave-5c's W-C2 control (`counted_extent_tests`) pins it as an open
    /// boundary, and moving that expectation is that lane's call.
    AliasResult,
}

/// Classify a `Rust`-ABI callee; `None` for anything the table does not
/// know, which stays an unknown call for the retention collector and refuses
/// the descendant-free scan.
pub(crate) fn core_pointer_call(tcx: TyCtxt<'_>, callee: DefId) -> Option<CorePointerCall> {
    if tcx.crate_name(callee.krate).as_str() != "core" {
        return None;
    }
    match tcx.item_name(callee).as_str() {
        "is_null" => Some(CorePointerCall::NoRetain),
        "offset" | "add" | "sub" | "cast" | "cast_mut" | "cast_const" => {
            Some(CorePointerCall::AliasResult)
        }
        _ => None,
    }
}

/// Whether `local` reaches the function's return place through transparent
/// copies and pointer casts. A subject's own rebind that is RETURNED
/// (`let q = p.offset(1); q`, wave-6s's re-ratified g18 form) keeps the
/// pre-hook reading — an open call, retention unknown — rather than a
/// positive retention of the parameter (main 036 / relay wave-6r/010).
pub(crate) fn result_returned(body: &Body<'_>, local: Local) -> bool {
    let mut aliases = vec![local];
    let mut changed = true;
    while changed {
        changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let (lhs, rhs) = (&assignment.0, &assignment.1);
                let source = match rhs {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand_local(operand),
                    _ => None,
                };
                let Some(source) = source.filter(|source| aliases.contains(source)) else {
                    continue;
                };
                if lhs.as_local() == Some(rustc_middle::mir::RETURN_PLACE) {
                    return true;
                }
                if let Some(destination) = lhs.as_local()
                    && !aliases.contains(&destination)
                {
                    aliases.push(destination);
                    changed = true;
                }
            }
        }
    }
    false
}

/// The collector's arm for a `Rust`-ABI callee: a known no-retain step when
/// the call is a classified core pointer method whose alias result (if any)
/// is not the function's own returned rebind.
pub(crate) fn core_pointer_known_no_retain<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    data: &rustc_middle::mir::BasicBlockData<'tcx>,
    callee: DefId,
) -> bool {
    match core_pointer_call(tcx, callee) {
        None => false,
        Some(CorePointerCall::NoRetain) => true,
        Some(CorePointerCall::AliasResult) => {
            let TerminatorKind::Call { destination, .. } = &data.terminator().kind else {
                return false;
            };
            destination
                .as_local()
                .is_some_and(|result| !result_returned(body, result))
        }
    }
}

/// The retention collector's alias edge for a block whose terminator is an
/// alias-result core call on a raw-pointer local: `receiver -> result`.
pub(crate) fn core_pointer_alias_edge<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    block: rustc_middle::mir::BasicBlock,
    data: &rustc_middle::mir::BasicBlockData<'tcx>,
) -> Option<(Local, Local, super::decision::raw_boundary::RetentionStep)> {
    let TerminatorKind::Call {
        func,
        args,
        destination,
        ..
    } = &data.terminator().kind
    else {
        return None;
    };
    let callee = resolved(func)?;
    if core_pointer_call(tcx, callee) != Some(CorePointerCall::AliasResult) {
        return None;
    }
    let receiver = operand_local(&args.first()?.node)?;
    let result = destination.as_local()?;
    if !matches!(body.local_decls[receiver].ty.kind(), TyKind::RawPtr(..))
        || !matches!(body.local_decls[result].ty.kind(), TyKind::RawPtr(..))
        || result_returned(body, result)
    {
        return None;
    }
    Some((
        receiver,
        result,
        super::decision::raw_boundary::RetentionStep {
            location: format!("bb{}:s{}", block.as_u32(), data.statements.len()),
            kind: super::decision::raw_boundary::RetentionEventKind::Transparent,
            detail: format!(
                "_{}->_{} core-{}",
                receiver.as_u32(),
                result.as_u32(),
                tcx.item_name(callee).as_str()
            ),
        },
    ))
}

fn pointer(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(..) | TyKind::Ref(..))
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    operand.place().and_then(|place| place.as_local())
}

fn resolved(operand: &Operand<'_>) -> Option<DefId> {
    let constant = operand.constant()?;
    let TyKind::FnDef(callee, _) = *constant.ty().kind() else { return None };
    Some(callee)
}

/// Whether `parameter` of `function` is descendant-free. `visited` breaks
/// recursion through local callees; a cycle is refused (conservative).
fn descendant_free(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    function: LocalDefId,
    parameter: Local,
    visited: &mut FxHashSet<(LocalDefId, Local)>,
) -> bool {
    if !visited.insert((function, parameter)) {
        return false;
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let body: &Body<'_> = &body;
    // Transparent alias closure: copies, pointer casts, and the results of
    // libc calls whose contract row returns an alias of an alias.
    let mut aliases = vec![parameter];
    let mut changed = true;
    while changed {
        changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let (lhs, rhs) = (&assignment.0, &assignment.1);
                let source = match rhs {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand_local(operand),
                    _ => None,
                };
                if let Some(source) = source
                    && aliases.contains(&source)
                    && let Some(destination) = lhs.as_local()
                    && pointer(body.local_decls[destination].ty)
                    && !aliases.contains(&destination)
                {
                    aliases.push(destination);
                    changed = true;
                }
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &data.terminator().kind
                && let Some(callee) = resolved(func)
                && callee
                    .as_local()
                    .is_none_or(|local| !functions.contains(&local))
                && let Some(result) = destination.as_local()
                && pointer(body.local_decls[result].ty)
                && !aliases.contains(&result)
            {
                if core_pointer_call(tcx, callee) == Some(CorePointerCall::AliasResult)
                    && args
                        .first()
                        .and_then(|argument| operand_local(&argument.node))
                        .is_some_and(|receiver| aliases.contains(&receiver))
                {
                    aliases.push(result);
                    changed = true;
                    continue;
                }
                let key = symbol_key(tcx, callee, functions);
                let returns_alias = args.iter().enumerate().any(|(index, argument)| {
                    operand_local(&argument.node).is_some_and(|local| aliases.contains(&local))
                        && raw_target_type(tcx, argument.node.ty(body, tcx)).is_some_and(|target| {
                            classify_contract(&key, index, &target)
                                .is_ok_and(|contract| contract.returns_alias_of == Some(index))
                        })
                });
                if returns_alias {
                    aliases.push(result);
                    changed = true;
                }
            }
        }
    }
    let is_alias =
        |operand: &Operand<'_>| operand_local(operand).is_some_and(|l| aliases.contains(&l));
    let hands_out = |place: &rustc_middle::mir::Place<'_>| {
        place
            .as_local()
            .is_none_or(|local| local == rustc_middle::mir::RETURN_PLACE)
    };
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (lhs, rhs) = (&assignment.0, &assignment.1);
            let derived = match rhs {
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    aliases.contains(&place.local)
                }
                Rvalue::BinaryOp(BinOp::Offset, operands) => is_alias(&operands.0),
                Rvalue::Aggregate(_, operands) => operands.iter().any(is_alias),
                // A copy or pointer cast of an alias stored through any
                // projection, or into the return place, hands it out; a cast
                // to a non-pointer is an image the scan cannot follow.
                Rvalue::Cast(_, operand, ty) => {
                    is_alias(operand) && (!pointer(*ty) || hands_out(lhs))
                }
                Rvalue::Use(operand) => is_alias(operand) && hands_out(lhs),
                _ => false,
            };
            if derived {
                return false;
            }
        }
        match &data.terminator().kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                let Some(callee) = resolved(func) else {
                    if args.iter().any(|argument| is_alias(&argument.node)) {
                        return false;
                    }
                    continue;
                };
                if matches!(data.terminator().kind, TerminatorKind::TailCall { .. })
                    && args.iter().any(|argument| is_alias(&argument.node))
                {
                    return false;
                }
                if let Some(local) = callee.as_local().filter(|local| functions.contains(local)) {
                    for (index, argument) in args.iter().enumerate() {
                        if is_alias(&argument.node)
                            && !descendant_free(
                                tcx,
                                functions,
                                local,
                                Local::from_usize(index + 1),
                                visited,
                            )
                        {
                            return false;
                        }
                    }
                }
                // Foreign callees: the retention certificate already refuses
                // an unknown or retaining contract; a known no-retain row that
                // returns an alias was folded into the alias set above — unless
                // its result lands somewhere other than a plain local, which
                // hands the alias out directly. A `Rust`-ABI method on an
                // alias is outside the contract table: only `is_null` is known.
                if callee
                    .as_local()
                    .is_none_or(|local| !functions.contains(&local))
                    && !symbol_key(tcx, callee, functions).abi.starts_with('C')
                    && args.iter().any(|argument| is_alias(&argument.node))
                    && core_pointer_call(tcx, callee).is_none()
                {
                    return false;
                }
                // An alias-result core call whose result lands outside a plain
                // local (a static, a field, the return place) hands the alias
                // out directly.
                if core_pointer_call(tcx, callee) == Some(CorePointerCall::AliasResult)
                    && args
                        .first()
                        .is_some_and(|argument| is_alias(&argument.node))
                    && let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                    && hands_out(destination)
                {
                    return false;
                }
                if callee
                    .as_local()
                    .is_none_or(|local| !functions.contains(&local))
                    && let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                    && destination
                        .as_local()
                        .is_none_or(|l| l == rustc_middle::mir::RETURN_PLACE)
                {
                    let key = symbol_key(tcx, callee, functions);
                    let returns_alias = args.iter().enumerate().any(|(index, argument)| {
                        is_alias(&argument.node)
                            && raw_target_type(tcx, argument.node.ty(body, tcx)).is_some_and(
                                |target| {
                                    classify_contract(&key, index, &target).is_ok_and(|contract| {
                                        contract.returns_alias_of == Some(index)
                                    })
                                },
                            )
                    });
                    if returns_alias {
                        return false;
                    }
                }
            }
            _ => {}
        }
    }
    true
}

/// The body scan alone (no retention row), for the witnesses.
#[cfg(test)]
pub(crate) fn position_is_descendant_free(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    function: LocalDefId,
    index: usize,
) -> bool {
    descendant_free(
        tcx,
        functions,
        function,
        Local::from_usize(index + 1),
        &mut FxHashSet::default(),
    )
}

/// The returned-alias continuation at ONE call site: a callee position whose
/// only retention is returning the parameter retains nothing beyond a call
/// whose result the caller discards. The retention row itself is untouched
/// (a caller that keeps the result keeps the sink); the site's effective
/// verdict becomes a no-retain certificate that names the discarded return.
pub(crate) fn site_retention(
    retention: &super::decision::raw_boundary::RetentionSummaries,
    caller: LocalDefId,
    key: &super::decision::raw_boundary::RawBoundarySiteKey,
    callee: LocalDefId,
) -> Option<RetentionVerdict> {
    use super::decision::raw_boundary::{RetentionCertificate, RetentionEventKind, RetentionStep};
    let base = retention.get(callee, key.argument_index)?;
    let RetentionVerdict::Retains { sink, path } = base else {
        return Some(base.clone());
    };
    let return_only = sink.kind == RetentionEventKind::Return
        && path
            .iter()
            .all(|step| step.kind == RetentionEventKind::Return);
    if !return_only {
        return Some(base.clone());
    }
    match retention.type_backed_child_access(caller, key) {
        Some(ChildAccess::Unused) => Some(RetentionVerdict::NoRetain {
            certificate: RetentionCertificate {
                function: key.callee.path.clone(),
                argument_index: key.argument_index,
                steps: vec![
                    sink.clone(),
                    RetentionStep {
                        location: format!("bb{}:s{}", key.block, key.statement_index),
                        kind: RetentionEventKind::KnownNoRetainCall,
                        detail: RETURNED_ALIAS_DISCARDED.to_owned(),
                    },
                ],
                attestation: "closed_world_frozen_graph",
            },
        }),
        _ => Some(base.clone()),
    }
}

pub(crate) const RETURNED_ALIAS_DISCARDED: &str = "returned-alias-discarded";

/// Certificate replay for a site: a site certificate (its last step is the
/// discarded-return marker) is re-derived from the callee's row and the
/// caller's child record and must be equal; every other certificate is the
/// callee row's and replays through the collector's own check.
pub(crate) fn verify_certificate(
    retention: &super::decision::raw_boundary::RetentionSummaries,
    caller: LocalDefId,
    key: &super::decision::raw_boundary::RawBoundarySiteKey,
    callee: LocalDefId,
    certificate: &super::decision::raw_boundary::RetentionCertificate,
) -> Result<(), &'static str> {
    if certificate
        .steps
        .last()
        .is_some_and(|step| step.detail == RETURNED_ALIAS_DISCARDED)
    {
        return match site_retention(retention, caller, key, callee) {
            Some(RetentionVerdict::NoRetain {
                certificate: expected,
            }) if &expected == certificate => Ok(()),
            _ => Err("retention-certificate-invalid"),
        };
    }
    retention.verify_certificate(callee, key.argument_index, certificate)
}

/// Rewrite the type-backed records whose callee position is descendant-free.
/// The retention rows are the same summaries the raw-boundary disposition
/// consumes; nothing is re-derived.
pub(crate) fn discharge<'a>(
    program: &RustProgram<'_>,
    rows: &FxHashMap<(LocalDefId, usize), RetentionVerdict>,
    records: impl Iterator<Item = &'a mut ReturnedChildEvidence>,
) {
    let tcx: TyCtxt<'_> = program.tcx;
    let mut memo = FxHashMap::<(LocalDefId, usize), bool>::default();
    for record in records {
        if matches!(record.access, ChildAccess::Unused) {
            continue;
        }
        let Some(callee) = record.key.callee.as_local() else { continue };
        if !program.functions.contains(&callee) {
            continue;
        }
        let index = record.key.parent_argument_index;
        if !matches!(
            rows.get(&(callee, index)),
            Some(RetentionVerdict::NoRetain { .. })
        ) {
            continue;
        }
        let free = *memo.entry((callee, index)).or_insert_with(|| {
            let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
            index < body.arg_count
                && descendant_free(
                    tcx,
                    &program.functions,
                    callee,
                    Local::from_usize(index + 1),
                    &mut FxHashSet::default(),
                )
        });
        if !free {
            continue;
        }
        record.access = ChildAccess::Unused;
        record.contract_provenance = PROVENANCE;
    }
}
