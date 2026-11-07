use pointer_replacer_bo::{
    AcceptedPointerAnalysis, SignatureRoot,
    analyses::borrow_ownership::{
        SlotKind,
        crate_slots::MAX_SLOT_DEPTH,
        resolve::{ResolvedSlot, resolve_place},
        slots::{SlotOwner, StructFieldSlot},
        solver::SlotRef,
    },
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{AggregateKind, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};
use rustc_span::def_id::LocalDefId;

use super::{InitialPointerDecisions, PointerTarget, PtrKind};

type Node = (LocalDefId, SlotRef);

pub(super) fn propagate(
    analysis: &mut AcceptedPointerAnalysis,
    decisions: &InitialPointerDecisions,
    tcx: TyCtxt<'_>,
) -> bool {
    let mut pending = Vec::new();
    for (&function, signature) in &decisions.signatures.data {
        let mut source = tcx
            .fn_sig(function)
            .instantiate_identity()
            .skip_binder()
            .output();
        for depth in 0..MAX_SLOT_DEPTH {
            let (TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _)) = *source.kind() else {
                break;
            };
            let layer = if depth == 0 {
                signature.output_dec
            } else {
                decisions
                    .nested(PointerTarget::Output(function))
                    .get(usize::from(depth) - 1)
                    .map(|layer| layer.kind)
            };
            if source.is_raw_ptr()
                && !inner.is_c_void(tcx)
                && matches!(layer, Some(PtrKind::Raw(_)))
                && let Some(slot) = analysis.slots.fn_local_slots[&function]
                    .slot_for_local_depth(RETURN_PLACE, depth)
                && analysis.kinds[&SlotRef::Local(function, slot)] == SlotKind::Ref
                && analysis.origins.get(&function).is_none_or(|summary| {
                    !summary.slots.iter_enumerated().any(|(returned, slot)| {
                        slot.place.root == SignatureRoot::Return
                            && slot.place.field.is_none()
                            && slot.place.deref_depth + slot.depth == depth
                            && summary.slots.iter_enumerated().any(|(source, slot)| {
                                matches!(slot.place.root, SignatureRoot::Arg(_))
                                    && summary.subset.contains(source, returned)
                            })
                    })
                })
            {
                pending.push((function, SlotRef::Local(function, slot)));
            }
            source = inner;
        }
    }
    let raw_fields = analysis
        .kinds
        .keys()
        .filter_map(|slot| {
            let SlotRef::Field(slot) = *slot else { return None };
            let field = analysis.slots.field_slots.slot(slot);
            let SlotOwner::Field(owner) = field.owner else { return None };
            decisions
                .fields
                .get(&owner)
                .and_then(|layers| layers.get(usize::from(field.depth)))
                .is_none_or(|layer| matches!(layer.kind, PtrKind::Raw(_)))
                .then_some(slot)
        })
        .collect::<Vec<_>>();
    if pending.is_empty() && raw_fields.is_empty() {
        return false;
    }
    let mut edges = FxHashMap::<Node, Vec<Node>>::default();
    for &function in analysis.slots.fn_local_slots.keys() {
        pending.extend(
            raw_fields
                .iter()
                .map(|&slot| (function, SlotRef::Field(slot))),
        );
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let resolve = |place, depth| {
            resolve_place(&analysis.slots, function, &body, place, depth, None).map(|slot| {
                (
                    function,
                    match slot {
                        ResolvedSlot::Local(slot) => SlotRef::Local(function, slot),
                        ResolvedSlot::Field(slot) => SlotRef::Field(slot),
                    },
                )
            })
        };
        let returned = |callee, depth| {
            analysis
                .slots
                .fn_local_slots
                .get(&callee)?
                .slot_for_local_depth(RETURN_PLACE, depth)
                .map(|slot| (callee, SlotRef::Local(callee, slot)))
        };
        let mut connect = |source, target| {
            if let (Some(source), Some(target)) = (source, target) {
                edges.entry(source).or_default().push(target);
            }
        };
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign(box (target, value)) = &statement.kind else { continue };
                let (source, shift) = match value {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                        let Some(source) = operand.place() else { continue };
                        (source, 0)
                    }
                    Rvalue::CopyForDeref(source) => (*source, 0),
                    Rvalue::Ref(_, _, source) | Rvalue::RawPtr(_, source) => {
                        // A reborrow of a pointee also depends on the pointer used to reach it.
                        let mut traversed = Vec::new();
                        resolve_place(
                            &analysis.slots,
                            function,
                            &body,
                            *source,
                            0,
                            Some(&mut traversed),
                        );
                        for slot in traversed {
                            let slot = match slot {
                                ResolvedSlot::Local(slot) => SlotRef::Local(function, slot),
                                ResolvedSlot::Field(slot) => SlotRef::Field(slot),
                            };
                            connect(Some((function, slot)), resolve(*target, 0));
                        }
                        (*source, 1)
                    }
                    Rvalue::Aggregate(kind, operands) => {
                        if let AggregateKind::Adt(owner, ..) = **kind
                            && let Some(owner) = owner.as_local()
                            && tcx.adt_def(owner).is_struct()
                        {
                            for (index, operand) in operands.iter_enumerated() {
                                let Some(source) = operand.place() else { continue };
                                for depth in 0..MAX_SLOT_DEPTH {
                                    let field = StructFieldSlot {
                                        struct_did: owner,
                                        field_index: index.as_usize(),
                                    };
                                    let target = analysis
                                        .slots
                                        .field_slots
                                        .slot_for_field_depth(field, depth)
                                        .map(|slot| (function, SlotRef::Field(slot)));
                                    connect(resolve(source, depth), target);
                                }
                            }
                        }
                        continue;
                    }
                    _ => continue,
                };
                for depth in 0..MAX_SLOT_DEPTH {
                    connect(resolve(source, depth), resolve(*target, depth + shift));
                }
            }
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &block.terminator().kind
            else {
                continue;
            };
            let TyKind::FnDef(callee, _) = *func.ty(&*body, tcx).kind() else { continue };
            if let Some(callee) = callee
                .as_local()
                .filter(|callee| analysis.origins.contains_key(callee))
            {
                for depth in 0..MAX_SLOT_DEPTH {
                    connect(returned(callee, depth), resolve(*destination, depth));
                }
                let summary = &analysis.origins[&callee];
                let instantiate = |slot: &pointer_replacer_bo::SignatureSlot| {
                    let place = match slot.place.root {
                        SignatureRoot::Return => *destination,
                        SignatureRoot::Arg(local) => args.get(local.index() - 1)?.node.place()?,
                    };
                    if let Some(field) = slot.place.field {
                        analysis
                            .slots
                            .field_slots
                            .slot_for_field_depth(field, slot.depth)
                            .map(|slot| (function, SlotRef::Field(slot)))
                    } else {
                        resolve(place, slot.place.deref_depth + slot.depth)
                    }
                };
                for (source, source_slot) in summary.slots.iter_enumerated() {
                    for (target, target_slot) in summary.slots.iter_enumerated() {
                        if summary.subset.contains(source, target) {
                            connect(instantiate(source_slot), instantiate(target_slot));
                        }
                    }
                }
            } else {
                for argument in args {
                    let Some(source) = argument.node.place() else { continue };
                    for depth in 0..MAX_SLOT_DEPTH {
                        connect(resolve(source, depth), resolve(*destination, depth));
                    }
                }
            }
        }
    }
    let mut visited = FxHashSet::default();
    while let Some(node) = pending.pop() {
        if visited.insert(node)
            && let Some(targets) = edges.get(&node)
        {
            pending.extend(targets);
        }
    }
    let mut changed = false;
    for (&function, summary) in &mut analysis.origins {
        for (index, slot) in summary.slots.iter_enumerated() {
            if slot.place.root == SignatureRoot::Return
                && slot.place.field.is_none()
                && let Some(returned) = analysis.slots.fn_local_slots[&function]
                    .slot_for_local_depth(RETURN_PLACE, slot.place.deref_depth + slot.depth)
                && visited.contains(&(function, SlotRef::Local(function, returned)))
            {
                changed |= summary.unknown.insert(index);
            }
        }
    }
    changed
}
