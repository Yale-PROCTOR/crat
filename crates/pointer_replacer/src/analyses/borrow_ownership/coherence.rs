use rustc_middle::mir::{AggregateKind, Body, Operand, Rvalue, StatementKind};
use rustc_span::def_id::LocalDefId;

use super::{
    crate_slots::{CrateSlots, MAX_SLOT_DEPTH},
    resolve::{ResolvedSlot, resolve_place},
    solver::{KindSolver, SlotRef},
    slots::StructFieldSlot,
};

fn to_slot_ref(r: ResolvedSlot, fn_did: LocalDefId) -> SlotRef {
    match r {
        ResolvedSlot::Local(id) => SlotRef::Local(fn_did, id),
        ResolvedSlot::Field(id) => SlotRef::Field(id),
    }
}

pub fn add_coherence<'tcx>(
    solver: &KindSolver,
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
) {
    for bbdata in body.basic_blocks.iter() {
        for stmt in &bbdata.statements {
            let StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind else {
                continue;
            };

            match rvalue {
                Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))
                | Rvalue::CopyForDeref(rhs) => {
                    for d in 0..MAX_SLOT_DEPTH {
                        if let (Some(la), Some(ra)) = (
                            resolve_place(slots, fn_did, body, *lhs, d),
                            resolve_place(slots, fn_did, body, *rhs, d),
                        ) {
                            solver.equate(to_slot_ref(la, fn_did), to_slot_ref(ra, fn_did));
                        }
                    }
                }
                Rvalue::Ref(_, _, rhs) | Rvalue::RawPtr(_, rhs) => {
                    for d in 0..MAX_SLOT_DEPTH {
                        if let (Some(la), Some(ra)) = (
                            resolve_place(slots, fn_did, body, *lhs, d + 1),
                            resolve_place(slots, fn_did, body, *rhs, d),
                        ) {
                            solver.equate(to_slot_ref(la, fn_did), to_slot_ref(ra, fn_did));
                        }
                    }
                }
                Rvalue::Aggregate(kind, operands) => {
                    let AggregateKind::Adt(def_id, _variant, _args, _, _) = kind.as_ref() else {
                        continue;
                    };
                    let Some(struct_did) = def_id.as_local() else {
                        continue;
                    };

                    for (field_idx, operand) in operands.iter_enumerated() {
                        let operand_place = match operand {
                            Operand::Copy(place) | Operand::Move(place) => *place,
                            Operand::Constant(_) => continue,
                        };
                        let field = StructFieldSlot {
                            struct_did,
                            field_index: field_idx.index(),
                        };

                        for d in 0..MAX_SLOT_DEPTH {
                            if let (Some(field_slot_id), Some(operand_slot)) = (
                                slots.field_slots.slot_for_field_depth(field, d),
                                resolve_place(slots, fn_did, body, operand_place, d),
                            ) {
                                solver.equate(
                                    SlotRef::Field(field_slot_id),
                                    to_slot_ref(operand_slot, fn_did),
                                );
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
}
