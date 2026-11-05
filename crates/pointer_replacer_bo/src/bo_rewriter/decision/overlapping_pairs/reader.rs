//! Object-wide no-write evidence for one exact local call interval.
//!
//! This certificate is a prerequisite, not a presentation or delivery grant.
//! In particular it supplies neither an extent nor permission to construct a
//! reference, and it never changes an A5 disjointness verdict.

use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{AssertMessage, BasicBlock, CastKind, Location, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};

use super::super::a5_site_proof::{A5ProofSiteKey, ATTESTED_GUARD, ATTESTED_WORLD};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Request {
    pub left: A5ProofSiteKey,
    pub right: A5ProofSiteKey,
    pub world: &'static str,
    pub guard: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Hold {
    MissingEvidence,
    StaleEvidence,
    UnattestedWorld,
    InvalidSite,
    NonScalarReturn,
    MemoryWrite {
        function: LocalDefId,
        location: Location,
    },
    OpaqueEffect {
        function: LocalDefId,
        location: Location,
    },
    LocalAddress {
        function: LocalDefId,
        location: Location,
    },
    OpaqueCall {
        function: LocalDefId,
        location: Location,
    },
    RecursiveCall,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Certificate {
    request: Request,
    functions: Vec<LocalDefId>,
}

impl Certificate {
    pub(crate) fn matches(&self, request: &Request) -> bool {
        &self.request == request
    }
}

pub(crate) fn prove(tcx: TyCtxt<'_>, request: &Request) -> Result<Certificate, Hold> {
    if request.world != ATTESTED_WORLD || request.guard != ATTESTED_GUARD {
        return Err(Hold::UnattestedWorld);
    }
    let (left, right) = (request.left, request.right);
    if left.caller != right.caller
        || left.callee != right.callee
        || left.location != right.location
        || left.slot_depth != 0
        || right.slot_depth != 0
        || left.argument_index >= right.argument_index
        || !tcx.is_mir_available(left.caller.to_def_id())
    {
        return Err(Hold::InvalidSite);
    }
    let caller = tcx
        .mir_drops_elaborated_and_const_checked(left.caller)
        .borrow();
    if left.location.block as usize >= caller.basic_blocks.len() {
        return Err(Hold::InvalidSite);
    }
    let block = caller
        .basic_blocks
        .get(BasicBlock::from_u32(left.location.block))
        .ok_or(Hold::InvalidSite)?;
    if block.statements.len() != left.location.statement_index {
        return Err(Hold::InvalidSite);
    }
    let TerminatorKind::Call { func, args, .. } = &block.terminator().kind else {
        return Err(Hold::InvalidSite);
    };
    let TyKind::FnDef(callee, _) = *func.ty(&caller.local_decls, tcx).kind() else {
        return Err(Hold::InvalidSite);
    };
    if callee != left.callee
        || [left.argument_index, right.argument_index]
            .iter()
            .any(|index| {
                !args.get(*index).is_some_and(|arg| {
                    matches!(
                        arg.node.ty(&caller.local_decls, tcx).kind(),
                        TyKind::RawPtr(..) | TyKind::Ref(..)
                    )
                })
            })
    {
        return Err(Hold::InvalidSite);
    }
    let callee = callee
        .as_local()
        .filter(|did| tcx.is_mir_available(did.to_def_id()))
        .ok_or(Hold::InvalidSite)?;
    let mut active = FxHashSet::default();
    let mut checked = FxHashSet::default();
    check_function(tcx, callee, &mut active, &mut checked)?;
    let mut functions = checked.into_iter().collect::<Vec<_>>();
    functions.sort_by_key(|did| did.local_def_index.as_u32());
    Ok(Certificate {
        request: request.clone(),
        functions,
    })
}

fn check_function(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    active: &mut FxHashSet<LocalDefId>,
    checked: &mut FxHashSet<LocalDefId>,
) -> Result<(), Hold> {
    if checked.contains(&function) {
        return Ok(());
    }
    if !active.insert(function) {
        return Err(Hold::RecursiveCall);
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    // Restrict result representation; this is not a retention certificate.
    // Aggregate and pointer returns need a separate lifetime producer. The
    // expression whitelist below also excludes encoded pointer provenance.
    match body.return_ty().kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {}
        TyKind::Tuple(fields) if fields.is_empty() => {}
        _ => return Err(Hold::NonScalarReturn),
    }
    // Check every block, including cleanup and syntactically unreachable
    // blocks. This deliberately proves a stronger property than per-pointer
    // immutability: no memory reachable through ANY alias is written.
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            match &statement.kind {
                StatementKind::Assign(assignment) => {
                    let (place, value) = &**assignment;
                    if place.is_indirect() {
                        return Err(Hold::MemoryWrite { function, location });
                    }
                    match value {
                        Rvalue::Ref(..) | Rvalue::RawPtr(..) => {
                            return Err(Hold::LocalAddress { function, location });
                        }
                        Rvalue::Cast(kind, ..) => match kind {
                            CastKind::IntToInt
                            | CastKind::IntToFloat
                            | CastKind::FloatToInt
                            | CastKind::FloatToFloat
                            | CastKind::PtrToPtr => {}
                            _ => return Err(Hold::OpaqueEffect { function, location }),
                        },
                        Rvalue::Use(_)
                        | Rvalue::BinaryOp(..)
                        | Rvalue::UnaryOp(..)
                        | Rvalue::Len(_)
                        | Rvalue::Discriminant(_)
                        | Rvalue::Repeat(..) => {}
                        _ => return Err(Hold::OpaqueEffect { function, location }),
                    }
                }
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop => {}
                _ => return Err(Hold::OpaqueEffect { function, location }),
            }
        }
        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        match &data.terminator().kind {
            TerminatorKind::Call {
                func, destination, ..
            } => {
                if destination.is_indirect() {
                    return Err(Hold::MemoryWrite { function, location });
                }
                let TyKind::FnDef(callee, _) = *func.ty(&body.local_decls, tcx).kind() else {
                    return Err(Hold::OpaqueCall { function, location });
                };
                let callee = callee
                    .as_local()
                    .filter(|did| tcx.is_mir_available(did.to_def_id()))
                    .ok_or(Hold::OpaqueCall { function, location })?;
                check_function(tcx, callee, active, checked)?;
            }
            // Only guards whose failure implies an invalid input access are
            // unreachable under the UB-free-input contract. Other assertions
            // may invoke user runtime hooks while the shared interval lives.
            TerminatorKind::Assert { msg, .. }
                if matches!(
                    **msg,
                    AssertMessage::MisalignedPointerDereference { .. }
                        | AssertMessage::NullPointerDereference
                ) => {}
            TerminatorKind::Return
            | TerminatorKind::Goto { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_) => {}
            _ => return Err(Hold::OpaqueEffect { function, location }),
        }
    }
    active.remove(&function);
    checked.insert(function);
    Ok(())
}

pub(crate) fn replay(
    tcx: TyCtxt<'_>,
    request: &Request,
    evidence: Option<&Certificate>,
) -> Result<(), Hold> {
    let evidence = evidence.ok_or(Hold::MissingEvidence)?;
    if &evidence.request != request {
        return Err(Hold::StaleEvidence);
    }
    if prove(tcx, request)? != *evidence {
        return Err(Hold::StaleEvidence);
    }
    Ok(())
}

#[cfg(test)]
mod tests;
