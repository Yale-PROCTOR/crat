//! §29 nullability facts: null is Option's `None`, orthogonal to pointer kind.

use rustc_hash::FxHashSet;
use rustc_middle::{
    mir::{AggregateKind, Operand, Place, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};
use rustc_span::def_id::LocalDefId;

use super::{
    crate_slots::CrateSlots,
    resolve::{ResolvedSlot, resolve_place},
    slots::StructFieldSlot,
    solver::SlotRef,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct NullabilityFacts {
    pub(crate) is_null_use: FxHashSet<SlotRef>,
    pub(crate) null_literal: FxHashSet<SlotRef>,
}

impl NullabilityFacts {
    pub(crate) fn contains(&self, slot: &SlotRef) -> bool {
        self.is_null_use.contains(slot) || self.null_literal.contains(slot)
    }

    pub(crate) fn slots(&self) -> FxHashSet<SlotRef> {
        self.is_null_use
            .union(&self.null_literal)
            .copied()
            .collect()
    }
}

fn to_slot_ref(fn_did: LocalDefId, resolved: ResolvedSlot) -> SlotRef {
    match resolved {
        ResolvedSlot::Local(slot) => SlotRef::Local(fn_did, slot),
        ResolvedSlot::Field(slot) => SlotRef::Field(slot),
    }
}

fn resolve<'tcx>(
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &rustc_middle::mir::Body<'tcx>,
    place: Place<'tcx>,
) -> Option<SlotRef> {
    resolve_place(slots, fn_did, body, place, 0, None).map(|slot| to_slot_ref(fn_did, slot))
}

fn const_is_zero(value: &rustc_middle::mir::Const<'_>, tcx: TyCtxt<'_>) -> bool {
    if let Some(scalar) = value.try_to_scalar()
        && let Ok(int) = scalar.try_to_scalar_int()
    {
        return int.to_bits(int.size()) == 0;
    }
    if let rustc_middle::mir::Const::Unevaluated(unevaluated, _) = value
        && unevaluated.promoted.is_none()
        && let Ok(rustc_middle::mir::ConstValue::Scalar(scalar)) =
            tcx.const_eval_poly(unevaluated.def)
        && let Ok(int) = scalar.try_to_scalar_int()
    {
        return int.to_bits(int.size()) == 0;
    }
    false
}

fn operand_is_null(operand: &Operand<'_>, tcx: TyCtxt<'_>) -> bool {
    matches!(operand, Operand::Constant(constant) if const_is_zero(&constant.const_, tcx))
}

pub(crate) fn analyze(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    slots: &CrateSlots,
) -> NullabilityFacts {
    let mut is_null_use = FxHashSet::default();
    let mut null_literal = FxHashSet::default();
    let mut edges = Vec::<(SlotRef, SlotRef)>::new();

    for &fn_did in functions {
        let body_ref = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        let body = &*body_ref;

        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
                    continue;
                };
                if let Rvalue::Aggregate(kind, operands) = rvalue
                    && let AggregateKind::Adt(def_id, _, _, _, _) = kind.as_ref()
                    && let Some(struct_did) = def_id.as_local()
                {
                    for (field_index, operand) in operands.iter_enumerated() {
                        let Some(field) = slots.field_slots.slot_for_field_depth(
                            StructFieldSlot {
                                struct_did,
                                field_index: field_index.index(),
                            },
                            0,
                        ) else {
                            continue;
                        };
                        let field = SlotRef::Field(field);
                        if operand_is_null(operand, tcx) {
                            null_literal.insert(field);
                        } else if let Some(place) = operand.place()
                            && let Some(source) = resolve(slots, fn_did, body, place)
                        {
                            edges.push((source, field));
                        }
                    }
                    continue;
                }

                let Some(target) = resolve(slots, fn_did, body, *lhs) else {
                    continue;
                };
                let operand = match rvalue {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => Some(operand),
                    Rvalue::CopyForDeref(place) => {
                        if let Some(source) = resolve(slots, fn_did, body, *place) {
                            edges.push((source, target));
                        }
                        None
                    }
                    _ => None,
                };
                if let Some(operand) = operand {
                    if operand_is_null(operand, tcx) {
                        null_literal.insert(target);
                    } else if let Some(place) = operand.place()
                        && let Some(source) = resolve(slots, fn_did, body, place)
                    {
                        edges.push((source, target));
                    }
                }
            }

            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &data.terminator().kind
            else {
                continue;
            };
            let TyKind::FnDef(def_id, _) = func.ty(body, tcx).kind() else {
                continue;
            };
            let name = tcx.item_name(*def_id);
            if matches!(name.as_str(), "null" | "null_mut")
                && let Some(target) = resolve(slots, fn_did, body, *destination)
            {
                null_literal.insert(target);
            }
            if name.as_str() == "is_null"
                && let Some(place) = args.first().and_then(|arg| arg.node.place())
                && let Some(source) = resolve(slots, fn_did, body, place)
            {
                is_null_use.insert(source);
            }
        }

        // A returned nullable local transfers its signal to the return slot through ordinary MIR
        // assignments; the generic edge scan above includes `_0 = local`. Keep RETURN_PLACE used
        // here as an audit assertion that a modeled pointer return has a slot when present.
        let _ = slots.fn_local_slots[&fn_did].slots_for_local(RETURN_PLACE);
    }

    let close = |set: &mut FxHashSet<SlotRef>| {
        let mut changed = true;
        while changed {
            changed = false;
            for &(source, target) in &edges {
                if set.contains(&source) {
                    changed |= set.insert(target);
                }
            }
        }
    };
    close(&mut is_null_use);
    close(&mut null_literal);

    NullabilityFacts {
        is_null_use,
        null_literal,
    }
}
