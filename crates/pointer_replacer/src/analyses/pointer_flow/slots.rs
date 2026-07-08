use std::ops::Range;

use rustc_abi::FieldIdx;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Body, Local, Place, ProjectionElem},
    ty::{self, Ty, TyCtxt},
};
use rustc_span::def_id::DefId;

pub type SlotIdx = usize;

#[derive(Clone, Debug, Default)]
pub struct SlotTable {
    local_slots: Vec<Range<SlotIdx>>,
    pub slot_infos: Vec<SlotInfo>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotInfo {
    pub root: Local,
    pub path: Vec<SlotPathElem>,
    pub depth: usize,
    pub qualifier_key: Option<QualifierKey>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QualifierKey {
    Local {
        offset: usize,
    },
    StructField {
        def_id: LocalDefId,
        field: FieldIdx,
        offset: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SlotPathElem {
    Pointee,
    Field(FieldIdx),
    Element,
}

pub(crate) fn slot_ty<'tcx>(
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    info: &SlotInfo,
) -> Option<Ty<'tcx>> {
    let mut ty = body.local_decls[info.root].ty;

    for elem in &info.path {
        match elem {
            SlotPathElem::Pointee => {
                ty = ty.builtin_deref(true)?;
            }
            SlotPathElem::Field(field) => {
                ty = match ty.kind() {
                    ty::TyKind::Adt(adt_def, args) => {
                        if !adt_def.is_struct() || adt_def.is_union() {
                            return None;
                        }
                        adt_def.all_fields().nth(field.index())?.ty(tcx, args)
                    }
                    ty::TyKind::Tuple(tys) => tys.iter().nth(field.index())?,
                    _ => return None,
                };
            }
            SlotPathElem::Element => {
                ty = ty.builtin_index()?;
            }
        }
    }

    Some(ty)
}

pub(crate) fn slot_path_from_place<'tcx>(place: Place<'tcx>) -> Option<Vec<SlotPathElem>> {
    slot_path_from_projection(place.projection.as_ref())
}

impl SlotTable {
    pub(crate) fn new<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let mut local_slots = Vec::with_capacity(body.local_decls.len());
        let mut slot_infos = vec![];

        for (local, decl) in body.local_decls.iter_enumerated() {
            let start = slot_infos.len();
            collect_slot_infos(
                local,
                decl.ty,
                tcx,
                &mut vec![],
                0,
                &mut QualifierContext::Local { next_offset: 0 },
                &mut FxHashSet::default(),
                &mut slot_infos,
            );
            let end = slot_infos.len();
            local_slots.push(start..end);
        }

        Self {
            local_slots,
            slot_infos,
        }
    }

    pub(crate) fn local_slots(&self, local: Local) -> Range<SlotIdx> {
        self.local_slots[local.index()].clone()
    }

    pub(crate) fn local_head_slot(&self, local: Local) -> Option<SlotIdx> {
        self.local_slots(local).next()
    }

    pub(crate) fn place_slots<'tcx>(
        &self,
        place: Place<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<Range<SlotIdx>> {
        let mut offset = 0;
        let mut base_ty = body.local_decls[place.local].ty;

        for elem in place.projection {
            match elem {
                ProjectionElem::Deref => {
                    base_ty = base_ty.builtin_deref(true)?;
                    offset += 1;
                }
                ProjectionElem::Field(field, ty) => {
                    offset += field_slot_offset(base_ty, field, tcx)?;
                    base_ty = ty;
                }
                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                    base_ty = base_ty.builtin_index()?;
                }
                _ => return None,
            }
        }

        let local_slots = self.local_slots(place.local);
        let width = count_slots(base_ty, tcx, &mut FxHashSet::default());
        let start = local_slots.start + offset;
        let end = start + width;
        if end <= local_slots.end {
            Some(start..end)
        } else {
            None
        }
    }

    pub(crate) fn place_head_slot<'tcx>(
        &self,
        place: Place<'tcx>,
        body: &Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Option<SlotIdx> {
        if !place.ty(body, tcx).ty.is_raw_ptr() {
            return None;
        }

        self.place_slots(place, body, tcx)?.next()
    }
}

#[allow(clippy::too_many_arguments)]
fn collect_slot_infos<'tcx>(
    root: Local,
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    path: &mut Vec<SlotPathElem>,
    depth: usize,
    qualifier_context: &mut QualifierContext,
    seen_adts: &mut FxHashSet<DefId>,
    out: &mut Vec<SlotInfo>,
) {
    if let Some(inner_ty) = ty.builtin_deref(true) {
        let qualifier_key = qualifier_context.next_key();
        out.push(SlotInfo {
            root,
            path: path.clone(),
            depth,
            qualifier_key,
        });
        path.push(SlotPathElem::Pointee);
        collect_slot_infos(
            root,
            inner_ty,
            tcx,
            path,
            depth + 1,
            qualifier_context,
            seen_adts,
            out,
        );
        path.pop();
        return;
    }

    if let Some(inner_ty) = ty.builtin_index() {
        path.push(SlotPathElem::Element);
        collect_slot_infos(
            root,
            inner_ty,
            tcx,
            path,
            depth,
            qualifier_context,
            seen_adts,
            out,
        );
        path.pop();
        return;
    }

    match ty.kind() {
        ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() && !adt_def.is_union() => {
            let def_id = adt_def.did();
            if !seen_adts.insert(def_id) {
                return;
            }
            for (idx, field) in adt_def.all_fields().enumerate() {
                let mut field_qualifier_context =
                    match def_id
                        .as_local()
                        .map(|local_def_id| QualifierContext::StructField {
                            def_id: local_def_id,
                            field: FieldIdx::from_usize(idx),
                            next_offset: 0,
                        }) {
                        Some(context) => context,
                        None => QualifierContext::None,
                    };
                path.push(SlotPathElem::Field(FieldIdx::from_usize(idx)));
                collect_slot_infos(
                    root,
                    field.ty(tcx, substs),
                    tcx,
                    path,
                    depth,
                    &mut field_qualifier_context,
                    seen_adts,
                    out,
                );
                path.pop();
            }
            seen_adts.remove(&def_id);
        }
        ty::TyKind::Tuple(tys) => {
            for (idx, field_ty) in tys.iter().enumerate() {
                path.push(SlotPathElem::Field(FieldIdx::from_usize(idx)));
                collect_slot_infos(
                    root,
                    field_ty,
                    tcx,
                    path,
                    depth,
                    qualifier_context,
                    seen_adts,
                    out,
                );
                path.pop();
            }
        }
        _ => {}
    }
}

#[derive(Clone, Debug)]
enum QualifierContext {
    Local {
        next_offset: usize,
    },
    StructField {
        def_id: LocalDefId,
        field: FieldIdx,
        next_offset: usize,
    },
    None,
}

impl QualifierContext {
    fn next_key(&mut self) -> Option<QualifierKey> {
        match self {
            QualifierContext::Local { next_offset } => {
                let offset = *next_offset;
                *next_offset += 1;
                Some(QualifierKey::Local { offset })
            }
            QualifierContext::StructField {
                def_id,
                field,
                next_offset,
            } => {
                let offset = *next_offset;
                *next_offset += 1;
                Some(QualifierKey::StructField {
                    def_id: *def_id,
                    field: *field,
                    offset,
                })
            }
            QualifierContext::None => None,
        }
    }
}

pub(crate) fn count_slots<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    seen_adts: &mut FxHashSet<DefId>,
) -> usize {
    if let Some(inner_ty) = ty.builtin_deref(true) {
        return 1 + count_slots(inner_ty, tcx, seen_adts);
    }

    if let Some(inner_ty) = ty.builtin_index() {
        return count_slots(inner_ty, tcx, seen_adts);
    }

    match ty.kind() {
        ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() && !adt_def.is_union() => {
            let def_id = adt_def.did();
            if !seen_adts.insert(def_id) {
                return 0;
            }
            let count = adt_def
                .all_fields()
                .map(|field| count_slots(field.ty(tcx, substs), tcx, seen_adts))
                .sum();
            seen_adts.remove(&def_id);
            count
        }
        ty::TyKind::Tuple(tys) => tys
            .iter()
            .map(|field_ty| count_slots(field_ty, tcx, seen_adts))
            .sum(),
        _ => 0,
    }
}

fn field_slot_offset<'tcx>(base_ty: Ty<'tcx>, field: FieldIdx, tcx: TyCtxt<'tcx>) -> Option<usize> {
    match base_ty.kind() {
        ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() && !adt_def.is_union() => {
            let mut offset = 0;
            let mut seen = FxHashSet::default();
            for field_def in adt_def.all_fields().take(field.index()) {
                seen.clear();
                offset += count_slots(field_def.ty(tcx, substs), tcx, &mut seen);
            }
            Some(offset)
        }
        ty::TyKind::Tuple(tys) => {
            let mut seen = FxHashSet::default();
            Some(
                tys.iter()
                    .take(field.index())
                    .map(|field_ty| {
                        seen.clear();
                        count_slots(field_ty, tcx, &mut seen)
                    })
                    .sum(),
            )
        }
        _ => None,
    }
}

pub(crate) fn slot_path_from_projection<V, T>(
    projection: &[ProjectionElem<V, T>],
) -> Option<Vec<SlotPathElem>> {
    projection
        .iter()
        .map(|elem| match elem {
            ProjectionElem::Deref => Some(SlotPathElem::Pointee),
            ProjectionElem::Field(field, _) => Some(SlotPathElem::Field(*field)),
            ProjectionElem::Index(_)
            | ProjectionElem::ConstantIndex { .. }
            | ProjectionElem::Subslice { .. } => Some(SlotPathElem::Element),
            _ => None,
        })
        .collect()
}
