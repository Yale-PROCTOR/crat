use std::ops::Range;

use rustc_middle::{
    mir::{Body, Place, ProjectionElem},
    ty::TyKind,
};
use rustc_span::def_id::LocalDefId;

use super::{
    crate_slots::CrateSlots,
    slots::{SlotId, StructFieldSlot},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolvedSlot {
    Local(SlotId),
    Field(SlotId),
}

/// Push the pointer slot at `(range, depth)` — the pointer being dereferenced
/// at this step — into `layers`, if it is a modeled slot and a caller asked for
/// the traversed path (`§NB1` SAFE-MONO walk). A no-op when `layers` is `None`.
fn push_layer(
    layers: &mut Option<&mut Vec<ResolvedSlot>>,
    is_field: bool,
    range: &Option<Range<SlotId>>,
    depth: u8,
) {
    let (Some(layers), Some(r)) = (layers.as_mut(), range.as_ref()) else {
        return;
    };
    let idx = r.start.index() + depth as usize;
    if idx < r.end.index() {
        let slot = SlotId::from_usize(idx);
        layers.push(if is_field {
            ResolvedSlot::Field(slot)
        } else {
            ResolvedSlot::Local(slot)
        });
    }
}

/// Resolve a MIR place to the slot denoting that pointer value.
///
/// `None` means the place is not a fully modeled pointer slot and callers must
/// conservatively treat it as raw.
///
/// §NB1: when `layers` is `Some`, every pointer slot *dereferenced* on the way
/// to the target is appended to it (shallowest first, across struct-field
/// boundaries) — the SAFE-MONO walk's traversed layers. The target slot itself
/// is NOT a layer. Layers are only meaningful when the call returns `Some`
/// (a `None` return may leave a partially populated `layers`, which the caller
/// discards). Callers that do not need the path pass `None`.
pub fn resolve_place<'tcx>(
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    extra_deref: u8,
    mut layers: Option<&mut Vec<ResolvedSlot>>,
) -> Option<ResolvedSlot> {
    let fn_locals = slots.fn_local_slots.get(&fn_did)?;
    let mut is_field = false;
    let mut range: Option<Range<SlotId>> = fn_locals.slots_for_local(place.local);
    let mut base_ty = body.local_decls[place.local].ty;
    let mut depth = 0u8;

    for elem in place.projection {
        match elem {
            ProjectionElem::Deref => {
                push_layer(&mut layers, is_field, &range, depth);
                depth = depth.checked_add(1)?;
                base_ty = base_ty.builtin_deref(true)?;
            }
            ProjectionElem::Field(field_index, field_ty) => {
                let owner_len = match &range {
                    Some(r) => r.end.index() - r.start.index(),
                    None => 0,
                };
                // Enforce the boundary contract: the whole traversal must be
                // fully modeled before resolving a field.
                if depth as usize != owner_len {
                    return None;
                }

                let TyKind::Adt(adt, _) = base_ty.kind() else {
                    return None;
                };
                if !adt.did().is_local() || !adt.is_struct() || adt.is_union() {
                    return None;
                }

                let field = StructFieldSlot {
                    struct_did: adt.did().expect_local(),
                    field_index: field_index.index(),
                };
                let field_range = slots.field_slots.slots_for_field(field)?;
                is_field = true;
                range = Some(field_range);
                depth = 0;
                base_ty = field_ty;
            }
            ProjectionElem::OpaqueCast(ty) | ProjectionElem::Subtype(ty) => {
                base_ty = ty;
            }
            _ => return None,
        }
    }

    // Trailing `extra_deref`: the intermediate positions are traversed layers
    // too (used only with `extra_deref > 0`; the SAFE-MONO walk passes 0).
    for _ in 0..extra_deref {
        push_layer(&mut layers, is_field, &range, depth);
        depth = depth.checked_add(1)?;
    }
    let range = range?;
    let idx = range.start.index() + depth as usize;
    if idx < range.end.index() {
        let slot = SlotId::from_usize(idx);
        Some(if is_field {
            ResolvedSlot::Field(slot)
        } else {
            ResolvedSlot::Local(slot)
        })
    } else {
        None
    }
}
