use rustc_hash::FxHashSet;
use rustc_hir::LangItem;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{Body, Local, Operand, Place, PlaceElem, Rvalue, StatementKind},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::sym;

use super::{
    SlotKind,
    crate_slots::{CrateSlots, MAX_SLOT_DEPTH},
    resolve::{ResolvedSlot, resolve_place},
    solver::{KindSolver, SlotRef},
};
use crate::{analyses::mir::TerminatorExt, utils::rustc::RustProgram};

#[derive(Clone, Copy)]
enum Source<'tcx> {
    Value(Place<'tcx>),
    Address(Place<'tcx>),
}

/// Smart-pointer carriers have no kind-solver slot. Retain their possible source
/// loans instead of treating a move through an aggregate or a call as fresh memory.
pub(super) struct PointerLoanSources<'tcx> {
    transfers: IndexVec<Local, Vec<Source<'tcx>>>,
    destinations: Vec<Place<'tcx>>,
}

impl<'tcx> PointerLoanSources<'tcx> {
    pub(super) fn new(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let mut transfers = IndexVec::from_elem_n(Vec::new(), body.local_decls.len());
        let mut destinations = Vec::new();
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign(box (destination, rvalue)) = &statement.kind else {
                    continue;
                };
                if !carries_pointer(destination.ty(body, tcx).ty, tcx, &mut FxHashSet::default()) {
                    continue;
                }
                let sources = &mut transfers[destination.local];
                destinations.push(*destination);
                match rvalue {
                    Rvalue::Use(operand)
                    | Rvalue::Cast(_, operand, _)
                    | Rvalue::ShallowInitBox(operand, _) => {
                        if let Some(place) = operand.place() {
                            sources.push(Source::Value(place));
                        }
                    }
                    Rvalue::CopyForDeref(place) => sources.push(Source::Value(*place)),
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        sources.push(Source::Address(*place));
                    }
                    Rvalue::Aggregate(_, operands) => {
                        sources.extend(
                            operands
                                .iter()
                                .filter_map(Operand::place)
                                .filter(|place| {
                                    carries_pointer(
                                        place.ty(body, tcx).ty,
                                        tcx,
                                        &mut FxHashSet::default(),
                                    )
                                })
                                .map(Source::Value),
                        );
                    }
                    _ => {}
                }
            }
            if let Some(call) = block.terminator().as_call(tcx) {
                let arguments: Vec<_> = call
                    .args
                    .iter()
                    .filter_map(|arg| arg.node.place())
                    .filter(|place| {
                        carries_pointer(place.ty(body, tcx).ty, tcx, &mut FxHashSet::default())
                    })
                    .collect();
                // A call can store a pointer through any other actual argument.
                // Keep those possible transfers even when its result is scalar.
                for receiver in &arguments {
                    transfers[receiver.local].extend(
                        arguments
                            .iter()
                            .copied()
                            .filter(|source| source.local != receiver.local)
                            .map(Source::Value),
                    );
                }
                // A returned carrier may retain any actual pointer argument.
                // This is a may-alias relation, never evidence of unique ownership.
                if carries_pointer(
                    call.destination.ty(body, tcx).ty,
                    tcx,
                    &mut FxHashSet::default(),
                ) {
                    destinations.push(call.destination);
                    transfers[call.destination.local]
                        .extend(arguments.into_iter().map(Source::Value));
                }
            }
        }
        Self {
            transfers,
            destinations,
        }
    }

    pub(super) fn borrowed_places(
        &self,
        place: Place<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<Vec<Place<'tcx>>> {
        let (borrowed, smart, _) = pointer_target(place, body, tcx)?;
        let borrowed = self.box_origin(place, body, tcx).unwrap_or(borrowed);
        let mut places = vec![borrowed];
        if !smart {
            return Some(places);
        }
        let mut pending = vec![place.local];
        let mut visited = FxHashSet::default();
        while let Some(local) = pending.pop() {
            if !visited.insert(local) {
                continue;
            }
            for source in &self.transfers[local] {
                let place = match *source {
                    Source::Value(place) => {
                        if let Some((target, _, _)) = pointer_target(place, body, tcx)
                            && !places.contains(&target)
                        {
                            places.push(target);
                        }
                        place
                    }
                    Source::Address(place) => {
                        if !places.contains(&place) {
                            places.push(place);
                        }
                        place
                    }
                };
                pending.push(place.local);
            }
        }
        Some(places)
    }

    fn box_origin(
        &self,
        mut place: Place<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<Place<'tcx>> {
        let mut visited = FxHashSet::default();
        loop {
            let (target, _, boundary) = pointer_target(place, body, tcx)?;
            if !boundary && target.ty(body, tcx).ty.is_box() {
                return Some(target);
            }
            if !visited.insert(place.local) {
                return None;
            }
            let [Source::Value(source)] = self.transfers[place.local].as_slice() else {
                return None;
            };
            if source.ty(body, tcx).ty != body.local_decls[place.local].ty {
                return None;
            }
            place = source.project_deeper(place.projection, tcx);
        }
    }

    fn raw_boundary_locals(&self, body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> FxHashSet<Local> {
        let mut connected = FxHashSet::default();
        for (destination, sources) in self.transfers.iter_enumerated() {
            for source in sources {
                if let Source::Value(place) = *source
                    && pointer_target(place, body, tcx).is_some_and(|(_, _, boundary)| boundary)
                    && self.box_origin(place, body, tcx).is_none()
                {
                    connected.insert(place.local);
                    connected.insert(destination);
                }
            }
        }
        loop {
            let mut changed = false;
            for (destination, sources) in self.transfers.iter_enumerated() {
                for source in sources {
                    let (Source::Value(place) | Source::Address(place)) = source;
                    if connected.contains(&destination) || connected.contains(&place.local) {
                        changed |= connected.insert(destination);
                        changed |= connected.insert(place.local);
                    }
                }
            }
            if !changed {
                return connected;
            }
        }
    }
}

fn carries_pointer<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    visited: &mut FxHashSet<Ty<'tcx>>,
) -> bool {
    if ty.is_any_ptr() || ty.is_box() {
        return true;
    }
    if !visited.insert(ty) {
        return false;
    }
    match ty.kind() {
        TyKind::Adt(adt, arguments) => {
            Some(adt.did()) == tcx.get_diagnostic_item(sym::NonNull)
                || adt
                    .all_fields()
                    .any(|field| carries_pointer(field.ty(tcx, arguments), tcx, visited))
        }
        TyKind::Tuple(types) => types.iter().any(|ty| carries_pointer(ty, tcx, visited)),
        TyKind::Array(element, _) | TyKind::Slice(element) => {
            carries_pointer(*element, tcx, visited)
        }
        TyKind::Closure(..) | TyKind::Param(_) | TyKind::Alias(..) => true,
        _ => false,
    }
}

pub(super) fn constrain_carrier_boundaries(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    solver: &KindSolver,
) {
    // NonNull proves neither a borrow lifetime nor unique ownership. Until those
    // carrier origins have modeled slots, keep connected raw values raw, including
    // aliases copied into or extracted from aggregate fields.
    for &function in &program.functions {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let sources = PointerLoanSources::new(&body, program.tcx);
        let connected = sources.raw_boundary_locals(&body, program.tcx);
        let mut places = sources.destinations.clone();
        for (local, transfers) in sources.transfers.iter_enumerated() {
            places.push(Place::from(local));
            places.extend(transfers.iter().map(|source| {
                let (Source::Value(place) | Source::Address(place)) = *source;
                place
            }));
        }
        let mut pinned = FxHashSet::default();
        for place in places {
            if !connected.contains(&place.local) || !place.ty(&*body, program.tcx).ty.is_raw_ptr() {
                continue;
            }
            for depth in 0..MAX_SLOT_DEPTH {
                if let Some(slot) = resolve_place(slots, function, &body, place, depth, None) {
                    let slot = match slot {
                        ResolvedSlot::Local(slot) => SlotRef::Local(function, slot),
                        ResolvedSlot::Field(slot) => SlotRef::Field(slot),
                    };
                    if pinned.insert(slot) {
                        solver.assume(slot, SlotKind::Raw);
                    }
                }
            }
        }
    }
}

fn pointer_target<'tcx>(
    place: Place<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(Place<'tcx>, bool, bool)> {
    let unique = tcx.lang_items().get(LangItem::PtrUnique);
    let non_null = tcx.get_diagnostic_item(sym::NonNull);
    let is_unique =
        |ty: Ty<'tcx>| matches!(ty.kind(), TyKind::Adt(adt, _) if Some(adt.did()) == unique);
    let is_non_null =
        |ty: Ty<'tcx>| matches!(ty.kind(), TyKind::Adt(adt, _) if Some(adt.did()) == non_null);
    let pointee = |ty: Ty<'tcx>| match ty.kind() {
        TyKind::Adt(_, arguments) if is_unique(ty) || is_non_null(ty) => Some(arguments.type_at(0)),
        _ => ty.builtin_deref(true),
    };
    let mut prefix = Place::from(place.local);
    let mut box_owner = None;
    let mut carrier_payload = false;
    for element in place.projection {
        let parent = prefix.ty(body, tcx).ty;
        let child = prefix.project_deeper(&[element], tcx);
        let child_ty = child.ty(body, tcx).ty;
        let payload_field = (parent.is_box() && is_unique(child_ty)
            || is_unique(parent) && is_non_null(child_ty)
            || is_non_null(parent) && child_ty.is_raw_ptr())
            && pointee(parent) == pointee(child_ty);
        carrier_payload = matches!(element, PlaceElem::Field(..)) && payload_field;
        if !carrier_payload {
            box_owner = None;
        } else if parent.is_box() {
            box_owner = Some(prefix);
        }
        prefix = child;
    }
    let ty = place.ty(body, tcx).ty;
    if let Some(owner) = box_owner.or_else(|| ty.is_box().then_some(place)) {
        // Use the whole owner consistently for both abstract Box dereferences
        // and rustc's lowered representation-field projections.
        return Some((owner, true, false));
    }
    if let Some(pointee) = ty.builtin_deref(true) {
        return Some((
            place.project_deeper(&[PlaceElem::Deref], tcx),
            pointee.is_box() || carrier_payload,
            carrier_payload,
        ));
    }
    if is_non_null(ty) || is_unique(ty) {
        let TyKind::Adt(adt, arguments) = ty.kind() else { unreachable!() };
        let (field, field_ty) =
            adt.non_enum_variant()
                .fields
                .iter_enumerated()
                .find_map(|(index, field)| {
                    let ty = field.ty(tcx, arguments);
                    (pointee(ty) == pointee(place.ty(body, tcx).ty)).then_some((index, ty))
                })?;
        let payload = place.project_deeper(&[PlaceElem::Field(field, field_ty)], tcx);
        let (target, _, _) = pointer_target(payload, body, tcx)?;
        return Some((target, true, true));
    }
    None
}
