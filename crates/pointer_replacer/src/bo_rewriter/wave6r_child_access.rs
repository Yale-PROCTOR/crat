//! K18′, callee side: a descendant-free callee position.
//!
//! The type-backed child walk follows the call's RETURN local; a callee whose
//! return carries no pointer leaves it `Unknown`, and the shared-source hold
//! `write-through-shared-view` fires on the possibility that the callee hands
//! a descendant of the argument back through output storage. This module
//! answers that possibility on the callee's own body: the argument's alias
//! set has a `NoRetain` certificate (nothing transparently derived from it is
//! returned, stored, or passed to a retaining or unknown call — transitively
//! through local callees) AND the body forms no non-transparent derivation of
//! that alias set at all (no address-of / raw-address of a place under it, no
//! `Offset`, no aggregate capture, no cast to a non-pointer), so no descendant
//! exists to hand back. Only then is the child access `Unused`.

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{BinOp, Body, Local, Operand, Rvalue, StatementKind},
    ty::{Ty, TyCtxt, TyKind},
};

use super::decision::{
    raw_boundary::{CARRIER_WALK_DEPTH, RetentionVerdict, may_carry_pointer},
    returned_child::{ChildAccess, ReturnedChildEvidence},
};
use crate::utils::rustc::RustProgram;

pub(crate) const PROVENANCE: &str = "k18-callee-descendant-free";

fn pointer(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(..) | TyKind::Ref(..))
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    operand.place().and_then(|place| place.as_local())
}

/// The transparent alias closure of the parameter, then the refusal scan.
fn descendant_free(body: &Body<'_>, parameter: Local) -> bool {
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
        }
    }
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (lhs, rhs) = (&assignment.0, &assignment.1);
            let derived = match rhs {
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    aliases.contains(&place.local)
                }
                Rvalue::BinaryOp(BinOp::Offset, operands) => {
                    operand_local(&operands.0).is_some_and(|local| aliases.contains(&local))
                }
                Rvalue::Aggregate(_, operands) => operands
                    .iter()
                    .any(|operand| operand_local(operand).is_some_and(|l| aliases.contains(&l))),
                Rvalue::Cast(_, operand, ty) => {
                    operand_local(operand).is_some_and(|local| aliases.contains(&local))
                        && !pointer(*ty)
                }
                Rvalue::Use(operand) => {
                    operand_local(operand).is_some_and(|local| aliases.contains(&local))
                        && lhs.as_local().is_none()
                }
                _ => false,
            };
            if derived {
                return false;
            }
        }
    }
    true
}

/// Rewrite the `Unknown` type-backed records whose callee position is
/// descendant-free. The retention rows are the same summaries the raw-boundary
/// disposition consumes; nothing is re-derived.
pub(crate) fn discharge<'a>(
    program: &RustProgram<'_>,
    rows: &FxHashMap<(LocalDefId, usize), RetentionVerdict>,
    records: impl Iterator<Item = &'a mut ReturnedChildEvidence>,
) {
    let tcx: TyCtxt<'_> = program.tcx;
    for record in records {
        if !matches!(record.access, ChildAccess::Unknown { .. }) {
            continue;
        }
        let Some(callee) = record.key.callee.as_local() else { continue };
        if !program.functions.contains(&callee) {
            continue;
        }
        let index = record.key.parent_argument_index;
        let output = tcx
            .fn_sig(callee.to_def_id())
            .skip_binder()
            .skip_binder()
            .output();
        if may_carry_pointer(tcx, output, CARRIER_WALK_DEPTH) {
            continue;
        }
        if !matches!(
            rows.get(&(callee, index)),
            Some(RetentionVerdict::NoRetain { .. })
        ) {
            continue;
        }
        let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
        if index >= body.arg_count || !descendant_free(&body, Local::from_usize(index + 1)) {
            continue;
        }
        record.access = ChildAccess::Unused;
        record.contract_provenance = PROVENANCE;
    }
}
