//! R243: exact source result transport through a finite straight-line field chain.
//! This recognizes a null test; it does not manufacture conditional field SSA.
use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::{
    mir::{
        BasicBlock, Body, CastKind, Local, Location, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind, UnOp,
    },
    ty::{self, TyCtxt},
};

use super::{
    FieldResultTransport, ReallocBranch, is_pointer_null_test, null_comparison, operand_local,
};
use crate::analyses::{
    borrow_ownership::{export::PlaceKey, source_events::transfer_statement},
    mir::TerminatorExt,
};

fn field_base<'tcx>(place: Place<'tcx>, body: &Body<'tcx>) -> Option<Local> {
    let mut ty = body.local_decls[place.local].ty;
    let mut field = false;
    for (index, projection) in place.projection.iter().enumerate() {
        match projection {
            ProjectionElem::Deref if index == 0 => {
                ty = match ty.kind() {
                    ty::RawPtr(target, _) | ty::Ref(_, target, _) => *target,
                    _ => return None,
                };
            }
            ProjectionElem::Field(_, field_ty) if matches!(ty.kind(), ty::Adt(def, _) if def.is_struct()) =>
            {
                field = true;
                ty = field_ty;
            }
            _ => return None,
        }
    }
    (field && ty.is_raw_ptr()).then_some(place.local)
}

pub(super) fn branch<'tcx>(
    body: &Body<'tcx>,
    call_block: BasicBlock,
    old: Option<Local>,
    result: Local,
    first: BasicBlock,
    entries: &[Option<Vec<bool>>],
    addressed: &BTreeSet<Local>,
    tcx: TyCtxt<'tcx>,
) -> Option<(ReallocBranch, Vec<FieldResultTransport>)> {
    let predecessors = body.basic_blocks.predecessors();
    let mut visited = BTreeSet::from([call_block]);
    let mut previous = call_block;
    let mut block = first;
    let mut aliases = BTreeSet::from([PlaceKey::from_place(Place::from(result))]);
    let mut predicates = BTreeMap::new();
    let mut base = None;
    let mut transports = Vec::new();
    loop {
        if !visited.insert(block)
            || predecessors[block].iter().copied().collect::<BTreeSet<_>>()
                != BTreeSet::from([previous])
        {
            return None;
        }
        let data = &body.basic_blocks[block];
        let mut nulls = entries[block.as_usize()]
            .clone()
            .unwrap_or_else(|| vec![false; body.local_decls.len()]);
        for (index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index: index,
            };
            match &statement.kind {
                StatementKind::Assign(box (destination, value)) => {
                    let destination_key = PlaceKey::from_place(*destination);
                    if aliases.contains(&destination_key)
                        || destination.as_local().is_some_and(|local| {
                            Some(local) == base || Some(local) == old || addressed.contains(&local)
                        })
                    {
                        return None;
                    }
                    let source = match value {
                        Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
                            operand.place()
                        }
                        Rvalue::CopyForDeref(place) => Some(*place),
                        _ => None,
                    }
                    .map(PlaceKey::from_place)
                    .filter(|place| aliases.contains(place));
                    if let Some(source) = source {
                        if !destination.ty(body, tcx).ty.is_raw_ptr() {
                            return None;
                        }
                        if destination.as_local().is_none() {
                            let owner = field_base(*destination, body)?;
                            if base.is_some_and(|base| base != owner) {
                                return None;
                            }
                            base = Some(owner);
                        }
                        aliases.insert(destination_key.clone());
                        transports.push(FieldResultTransport {
                            location,
                            source,
                            destination: destination_key,
                        });
                    } else {
                        let destination = destination.as_local()?;
                        let locals = aliases
                            .iter()
                            .filter(|place| place.proj.is_empty())
                            .map(|place| place.local)
                            .collect();
                        if let Some(null_when_true) = null_comparison(value, &locals, &nulls, tcx) {
                            predicates.insert(destination, null_when_true);
                        } else if let Some(value) = match value {
                            Rvalue::Use(operand) => operand_local(operand)
                                .and_then(|local| predicates.get(&local).copied()),
                            Rvalue::UnaryOp(UnOp::Not, operand) => operand_local(operand)
                                .and_then(|local| predicates.get(&local).map(|value| !*value)),
                            _ => None,
                        } {
                            predicates.insert(destination, value);
                        } else {
                            // An unrelated overwrite cannot retain an earlier
                            // Boolean result-test correlation (even scalar false).
                            if predicates.contains_key(&destination) {
                                return None;
                            }
                            transfer_statement(&statement.kind, &mut nulls, addressed, tcx);
                            if !nulls[destination.as_usize()] {
                                return None;
                            }
                        }
                    }
                }
                StatementKind::StorageDead(local) => {
                    if Some(*local) == base {
                        return None;
                    }
                    aliases.retain(|place| place.local != *local);
                    predicates.remove(local);
                }
                StatementKind::StorageLive(_)
                | StatementKind::Nop
                | StatementKind::ConstEvalCounter
                | StatementKind::Coverage(_) => {}
                _ => return None,
            }
            transfer_statement(&statement.kind, &mut nulls, addressed, tcx);
        }
        let next = match &data.terminator().kind {
            TerminatorKind::Goto { target } => *target,
            TerminatorKind::Call {
                target: Some(target),
                ..
            } => {
                let call = data.terminator().as_call(tcx)?;
                let destination = call.destination.as_local()?;
                if Some(destination) == base
                    || Some(destination) == old
                    || predicates.contains_key(&destination)
                    || addressed.contains(&destination)
                    || aliases.contains(&PlaceKey::from_place(call.destination))
                {
                    return None;
                }
                if !is_pointer_null_test(&call.func, tcx)
                    || call.args.len() != 1
                    || !call.args[0]
                        .node
                        .place()
                        .map(PlaceKey::from_place)
                        .is_some_and(|place| aliases.contains(&place))
                {
                    return None;
                }
                predicates.insert(destination, true);
                *target
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                base?;
                let null_when_true = *predicates.get(&operand_local(discr)?)?;
                let target_for = |value| {
                    targets
                        .iter()
                        .find_map(|(candidate, target)| (candidate == value).then_some(target))
                        .unwrap_or_else(|| targets.otherwise())
                };
                let failure = target_for(u128::from(null_when_true));
                let success = target_for(u128::from(!null_when_true));
                if success == failure || visited.contains(&success) || visited.contains(&failure) {
                    return None;
                }
                return Some((
                    ReallocBranch {
                        old,
                        result,
                        test: Location {
                            block,
                            statement_index: data.statements.len(),
                        },
                        success,
                        failure,
                        transports: Vec::new(),
                    },
                    transports,
                ));
            }
            _ => return None,
        };
        previous = block;
        block = next;
    }
}
