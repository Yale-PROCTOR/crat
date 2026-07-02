use rustc_hash::FxHashSet;
use rustc_middle::mir::{AggregateKind, Body, Local, Operand, Rvalue, StatementKind};
use rustc_span::def_id::LocalDefId;

use super::{
    crate_slots::{CrateSlots, MAX_SLOT_DEPTH},
    resolve::{ResolvedSlot, resolve_place},
    solver::{KindSolver, SlotRef},
    slots::StructFieldSlot,
    sources::collect_malloc_source_slots,
};
use crate::utils::rustc::RustProgram;

fn to_slot_ref(r: ResolvedSlot, fn_did: LocalDefId) -> SlotRef {
    match r {
        ResolvedSlot::Local(id) => SlotRef::Local(fn_did, id),
        ResolvedSlot::Field(id) => SlotRef::Field(id),
    }
}

/// Locals whose pointer VALUE originates from a borrowed input — a function parameter
/// (index `1..=arg_count`; local 0 is the return place) or a copy/cast/reborrow chain from
/// one. Storing such a value into a struct field means that crate-wide field slot can hold
/// non-owned memory, so its ownership must be vetoed (§9.10.2). Conservative: a parameter
/// that is actually an owned transfer is also treated as borrowed here (a safe leak, not an
/// over-claim). Value-preserving edges only (Use copy/move, ptr Cast, CopyForDeref); a
/// `Deref`/`Field`/`malloc` result is a fresh value and is NOT propagated.
fn compute_borrowed_origin(body: &Body<'_>) -> FxHashSet<Local> {
    let mut set: FxHashSet<Local> = (1..=body.arg_count).map(Local::from_usize).collect();
    let mut changed = true;
    while changed {
        changed = false;
        for bbdata in body.basic_blocks.iter() {
            for stmt in &bbdata.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind else {
                    continue;
                };
                let Some(dst) = lhs.as_local() else { continue };
                if set.contains(&dst) {
                    continue;
                }
                let src = match rvalue {
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::CopyForDeref(p)
                    | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => p.as_local(),
                    _ => None,
                };
                if let Some(srcl) = src
                    && set.contains(&srcl)
                {
                    set.insert(dst);
                    changed = true;
                }
            }
        }
    }
    set
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

/// §9.10.2 crate-wide field-ownership veto. A struct field slot is ONE crate-wide slot and
/// `coherence` is flow-insensitive, so a field assigned an owned allocation in one function
/// and a borrowed (parameter-origin) value in another would be forced `Owning` by the
/// allocation source yet actually hold borrowed memory in that other context — an unsound
/// over-claim (the rewriter would `Box`/free borrowed memory -> UAF). This vetoes the `own`
/// bit of any field slot that is assigned an alloc-origin value in one place AND a
/// borrowed-origin value in another (crate-wide), backing it off to non-Owning (the
/// retractable source leaks — a safe leak). A field consistently populated by owned
/// transfers (only alloc-origin) or consistently borrowed (only borrowed-origin) is NOT
/// vetoed, so legitimate ownership-transfer-into-a-field stays `Owning`.
pub(crate) fn apply_field_ownership_vetoes(
    solver: &KindSolver,
    slots: &CrateSlots,
    program: &RustProgram<'_>,
) {
    let alloc_sources = collect_malloc_source_slots(program, slots);
    let mut has_alloc: FxHashSet<SlotRef> = FxHashSet::default();
    let mut has_borrowed: FxHashSet<SlotRef> = FxHashSet::default();

    for &fn_did in &program.functions {
        let body_ref = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        let body = &*body_ref;
        let borrowed_origin = compute_borrowed_origin(body);

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
                        {
                            let f = SlotRef::Field(fid);
                            if let Some(rs) = resolve_place(slots, fn_did, body, *rhs, 0)
                                && alloc_sources.contains(&to_slot_ref(rs, fn_did))
                            {
                                has_alloc.insert(f);
                            }
                            if borrowed_origin.contains(&rhs.local) {
                                has_borrowed.insert(f);
                            }
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
                            let Some(fid) = slots.field_slots.slot_for_field_depth(field, 0) else {
                                continue;
                            };
                            let f = SlotRef::Field(fid);
                            if let Some(rs) = resolve_place(slots, fn_did, body, op_place, 0)
                                && alloc_sources.contains(&to_slot_ref(rs, fn_did))
                            {
                                has_alloc.insert(f);
                            }
                            if borrowed_origin.contains(&op_place.local) {
                                has_borrowed.insert(f);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    for field in has_alloc.intersection(&has_borrowed) {
        solver.veto_owning(*field);
    }
}
