use rustc_hash::FxHashMap;
use rustc_middle::mir::{AggregateKind, Body, Operand, Rvalue, StatementKind};
use rustc_span::def_id::LocalDefId;

use super::{
    crate_slots::{CrateSlots, MAX_SLOT_DEPTH},
    resolve::{ResolvedSlot, resolve_place},
    solver::{KindSolver, SlotRef},
    slots::StructFieldSlot,
};
use crate::utils::rustc::RustProgram;

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
                            // §9.10.2: a field STORE's depth-0 ownership is set crate-wide by
                            // `constrain_field_ownership` (`field.own <=> AND stored owns`), so
                            // skip the per-store equate here — equating multiple stores to one
                            // global field slot is what transitively dragged a borrowed value
                            // to `Owning`. (Field LOADS have a Local lhs and still equate.)
                            if d == 0 && matches!(la, ResolvedSlot::Field(_)) {
                                continue;
                            }
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
                            // §9.10.2: an aggregate is a field INITIALIZER; its depth-0
                            // ownership is set crate-wide by `constrain_field_ownership`.
                            if d == 0 {
                                continue;
                            }
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

/// §9.10.2 crate-wide field-ownership constraint. A struct field slot is ONE crate-wide slot
/// that (flow-insensitively) holds EVERY value stored into that field across the crate. The
/// per-store depth-0 `equate` is SKIPPED in `add_coherence` for field stores/aggregates (it is
/// what transitively dragged a borrowed value to `Owning` when an owned source was stored into
/// the same global field elsewhere). Instead, this collects, per depth-0 field slot, the
/// depth-0 slots of ALL its stored values crate-wide and asserts `field.own <=> AND(rhs.own)`
/// (`KindSolver::constrain_field_own`): the field may be `Owning` only if every value ever
/// stored into it is owned. This uses BO's OWN ownership verdict for each stored value, so
/// interprocedural / wrapper-returned allocations, borrowed returns, and projected loads are
/// all handled with NO syntactic detection — a field mixing an owned source and a borrowed
/// value settles non-Owning; a field populated only by owned transfers stays `Owning`.
pub(crate) fn constrain_field_ownership(
    solver: &KindSolver,
    slots: &CrateSlots,
    program: &RustProgram<'_>,
) {
    let mut stores: FxHashMap<SlotRef, Vec<SlotRef>> = FxHashMap::default();

    for &fn_did in &program.functions {
        let body_ref = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        let body = &*body_ref;

        for bbdata in body.basic_blocks.iter() {
            for stmt in &bbdata.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind else {
                    continue;
                };
                match rvalue {
                    Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs))
                    | Rvalue::CopyForDeref(rhs) => {
                        if let Some(ResolvedSlot::Field(fid)) =
                            resolve_place(slots, fn_did, body, *lhs, 0)
                            && let Some(rs) = resolve_place(slots, fn_did, body, *rhs, 0)
                        {
                            stores
                                .entry(SlotRef::Field(fid))
                                .or_default()
                                .push(to_slot_ref(rs, fn_did));
                        }
                    }
                    Rvalue::Aggregate(kind, operands) => {
                        let AggregateKind::Adt(def_id, _, _, _, _) = kind.as_ref() else {
                            continue;
                        };
                        let Some(struct_did) = def_id.as_local() else {
                            continue;
                        };
                        for (field_idx, operand) in operands.iter_enumerated() {
                            let op_place = match operand {
                                Operand::Copy(p) | Operand::Move(p) => *p,
                                Operand::Constant(_) => continue,
                            };
                            let field = StructFieldSlot {
                                struct_did,
                                field_index: field_idx.index(),
                            };
                            if let Some(fid) = slots.field_slots.slot_for_field_depth(field, 0)
                                && let Some(rs) = resolve_place(slots, fn_did, body, op_place, 0)
                            {
                                stores
                                    .entry(SlotRef::Field(fid))
                                    .or_default()
                                    .push(to_slot_ref(rs, fn_did));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    for (field, rhs) in &stores {
        solver.constrain_field_own(*field, rhs);
    }
}
