use rustc_hash::FxHashSet;
use rustc_middle::mir::{AggregateKind, Body, Local, Operand, Rvalue, StatementKind};
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

/// Locals whose pointer VALUE originates from a borrowed input — a function parameter
/// (index `1..=arg_count`; local 0 is the return place) or a copy/cast/reborrow/load chain
/// ROOTED at one. The chain follows the ROOT local of the source place, so a load THROUGH a
/// borrowed pointer (`t = (*param).field`, `t = *param`) is also borrowed — a value pulled
/// out of borrowed/caller memory is itself borrowed w.r.t. this function. Conservative: a
/// parameter that is actually an owned transfer is also treated as borrowed here (its field
/// use only matters when the field is ALSO assigned a non-borrowed value — see
/// `apply_field_ownership_vetoes` — so a pure transfer is not vetoed).
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
                // Root local of a value-preserving/loaded source; `p.local` (not
                // `as_local`) so projected loads through a borrowed root propagate.
                let src = match rvalue {
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    | Rvalue::CopyForDeref(p)
                    | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => Some(p.local),
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
/// `coherence` is flow-insensitive, so it equates that slot to EVERY value assigned to the
/// field across the crate. If a field is assigned a borrowed value in one place, it can hold
/// non-owned memory, so it must never be `Owning` (else the rewriter would `Box`/free
/// borrowed memory -> UAF). This vetoes the `own` bit of any field slot that is assigned
/// BOTH a borrowed-origin value AND a non-borrowed-origin value across the crate — i.e. a
/// field that MIGHT be forced `Owning` by the non-borrowed side yet holds borrowed memory in
/// the borrowed context. Backing it off to non-Owning is a safe leak (the retractable source
/// leaks, or a hard `free` sink makes it UNSAT and BO declines — both sound).
///
/// Using "non-borrowed" (rather than specifically an allocation source) makes the alloc side
/// robust to interprocedural / wrapper-returned allocations (`let p = make(); (*d).p = p`) —
/// no allocator-source detection is needed. Crucially it does NOT over-veto: a field
/// populated ONLY by owned transfers (every assignment borrowed-origin — e.g. a setter
/// `(*list).head = node` for a param `node`) has no non-borrowed assignment, so it is NOT
/// vetoed and stays `Owning`; a field assigned ONLY allocations (no borrowed assignment) is
/// likewise not vetoed. Borrowed-origin follows `compute_borrowed_origin` (params + copy /
/// cast / load chains rooted at one), so a projected borrowed load (`t = (*src).p`) counts.
/// RESIDUAL (deferred, rarer): a field assigned an owned param in one fn and a borrowed param
/// in another (both borrowed-origin) is not vetoed — distinguishing needs interprocedural
/// param ownership.
pub(crate) fn apply_field_ownership_vetoes(
    solver: &KindSolver,
    slots: &CrateSlots,
    program: &RustProgram<'_>,
) {
    let mut has_borrowed: FxHashSet<SlotRef> = FxHashSet::default();
    let mut has_non_borrowed: FxHashSet<SlotRef> = FxHashSet::default();

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
                            if borrowed_origin.contains(&rhs.local) {
                                has_borrowed.insert(f);
                            } else {
                                has_non_borrowed.insert(f);
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
                            if borrowed_origin.contains(&op_place.local) {
                                has_borrowed.insert(f);
                            } else {
                                has_non_borrowed.insert(f);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    for field in has_borrowed.intersection(&has_non_borrowed) {
        solver.veto_owning(*field);
    }
}
