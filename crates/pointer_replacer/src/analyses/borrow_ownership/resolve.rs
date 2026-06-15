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

/// Resolve a MIR place to the slot denoting that pointer value.
///
/// `None` means the place is not a fully modeled pointer slot and callers must
/// conservatively treat it as raw.
pub fn resolve_place<'tcx>(
    slots: &CrateSlots,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    extra_deref: u8,
) -> Option<ResolvedSlot> {
    let fn_locals = slots.fn_local_slots.get(&fn_did)?;
    let mut is_field = false;
    let mut range: Option<Range<SlotId>> = fn_locals.slots_for_local(place.local);
    let mut base_ty = body.local_decls[place.local].ty;
    let mut depth = 0u8;

    for elem in place.projection {
        match elem {
            ProjectionElem::Deref => {
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

    depth = depth.checked_add(extra_deref)?;
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
