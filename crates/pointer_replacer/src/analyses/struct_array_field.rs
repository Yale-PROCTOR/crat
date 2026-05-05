use points_to::andersen::{self, LocEdges, LocNode};
use rustc_abi::Size;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{BinOp, Body, Operand, Place, PlaceElem, Rvalue, StatementKind, TerminatorKind},
    ty::{self, TyCtxt},
};
use rustc_span::{Symbol, def_id::LocalDefId};

use crate::utils::rustc::RustProgram;

/// a group of consecutive same-typed fields in a struct to merge into a single array field
#[derive(Clone)]
pub struct FieldGroup {
    /// index of the first field in the group within the struct's field list
    pub start_idx: usize,
    /// number of consecutive same-typed fields (>= 2)
    pub count: usize,
    /// original names of the fields, in field definition order
    pub field_names: Vec<Symbol>,
}

impl FieldGroup {
    /// the name to use for the new array field (first field's name)
    pub fn array_name(&self) -> Symbol {
        self.field_names[0]
    }

    /// index within this group for a given original field name, if it belongs here
    pub fn group_index(&self, name: Symbol) -> Option<usize> {
        self.field_names.iter().position(|n| *n == name)
    }
}

/// maps struct LocalDefId to the list of field groups to merge into arrays
pub type StructRewriteCandidates = FxHashMap<LocalDefId, Vec<FieldGroup>>;

pub fn find_candidates(
    input: &RustProgram<'_>,
    points_to: &andersen::AnalysisResult,
) -> StructRewriteCandidates {
    let tcx = input.tcx;
    let candidates = select_candidates(input);
    let mut field_to_group = FxHashMap::default();
    let mut group_to_field_ty = FxHashMap::default();
    for (&struct_did, groups) in &candidates {
        let struct_ty = tcx.type_of(struct_did).skip_binder();
        let ty::TyKind::Adt(adt_def, args) = struct_ty.kind() else {
            continue;
        };
        for group in groups {
            let field_ty = adt_def
                .all_fields()
                .nth(group.start_idx)
                .expect("candidate field index must be valid")
                .ty(tcx, args);
            group_to_field_ty.insert((struct_did, group.start_idx), field_ty);
            for field_idx in group.start_idx..group.start_idx + group.count {
                field_to_group.insert((struct_did, field_idx), group.start_idx);
            }
        }
    }

    let mut field_ranges: FxHashMap<(LocalDefId, usize), Vec<LocRange>> = FxHashMap::default();
    let mut offset_ranges = Vec::new();

    for &fn_did in &input.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        collect_field_ranges(
            tcx,
            fn_did,
            &body,
            points_to,
            &field_to_group,
            &mut field_ranges,
        );
        collect_offset_ranges(tcx, fn_did, &body, points_to, &mut offset_ranges);
    }

    let mut rewrite_groups = FxHashSet::default();
    for (group_key, ranges) in &field_ranges {
        let Some(&field_ty) = group_to_field_ty.get(group_key) else {
            continue;
        };
        if ranges.iter().any(|field_range| {
            offset_ranges.iter().any(|offset_range| {
                ranges_overlap(*field_range, offset_range.range)
                    && types_are_compatible(field_ty, offset_range.pointee_ty)
            })
        }) {
            rewrite_groups.insert(*group_key);
        }
    }

    let mut rewrite_targets = FxHashMap::default();
    for (struct_did, groups) in candidates {
        let groups: Vec<_> = groups
            .into_iter()
            .filter(|group| rewrite_groups.contains(&(struct_did, group.start_idx)))
            .collect();
        if !groups.is_empty() {
            rewrite_targets.insert(struct_did, groups);
        }
    }

    rewrite_targets
}

#[derive(Clone, Copy)]
struct LocRange {
    start: andersen::Loc,
    end: andersen::Loc,
}

#[derive(Clone, Copy)]
struct OffsetRange<'tcx> {
    range: LocRange,
    pointee_ty: ty::Ty<'tcx>,
}

fn select_candidates(input: &RustProgram<'_>) -> StructRewriteCandidates {
    let tcx = input.tcx;
    let mut candidates = FxHashMap::default();

    for &struct_did in &input.structs {
        let struct_ty = tcx.type_of(struct_did).skip_binder();
        let ty::TyKind::Adt(adt_def, args) = struct_ty.kind() else {
            continue;
        };
        let repr = adt_def.repr();
        if !adt_def.is_struct()
            || adt_def.is_union()
            || !adt_def.did().is_local()
            || !repr.c()
            || repr.pack.is_some()
        {
            continue;
        }

        let fields: Vec<_> = adt_def.all_fields().collect();
        let mut groups = Vec::new();
        let mut start = 0;
        while start < fields.len() {
            let field_ty = fields[start].ty(tcx, args);
            let mut end = start + 1;
            while end < fields.len() && fields[end].ty(tcx, args) == field_ty {
                end += 1;
            }

            if end - start >= 2
                && candidate_element_ty_is_safe(tcx, struct_did, field_ty)
                && layout_is_contiguous(tcx, struct_did, struct_ty, &fields, start, end)
            {
                groups.push(FieldGroup {
                    start_idx: start,
                    count: end - start,
                    field_names: fields[start..end].iter().map(|f| f.name).collect(),
                });
            }
            start = end;
        }

        if !groups.is_empty() {
            candidates.insert(struct_did, groups);
        }
    }

    candidates
}

fn types_are_compatible<'tcx>(field_ty: ty::Ty<'tcx>, pointee_ty: ty::Ty<'tcx>) -> bool {
    field_ty == pointee_ty
}

fn candidate_element_ty_is_safe<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    ty: ty::Ty<'tcx>,
) -> bool {
    let typing_env = ty::TypingEnv::post_analysis(tcx, owner);
    let Ok(layout) = tcx.layout_of(typing_env.as_query_input(ty)) else {
        return false;
    };
    if layout.size == Size::ZERO {
        return false;
    }

    match ty.kind() {
        ty::TyKind::Array(..)
        | ty::TyKind::Slice(_)
        | ty::TyKind::Str
        | ty::TyKind::Dynamic(..)
        | ty::TyKind::Tuple(_)
        | ty::TyKind::Closure(..)
        | ty::TyKind::CoroutineClosure(..)
        | ty::TyKind::Coroutine(..)
        | ty::TyKind::CoroutineWitness(..)
        | ty::TyKind::Foreign(_) => false,
        ty::TyKind::Adt(adt_def, _) => {
            let repr = adt_def.repr();
            adt_def.is_struct()
                && !adt_def.is_union()
                && adt_def.did().is_local()
                && repr.c()
                && repr.pack.is_none()
                && tcx.type_is_copy_modulo_regions(typing_env, ty)
        }
        _ => true,
    }
}

fn layout_is_contiguous<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    struct_ty: ty::Ty<'tcx>,
    fields: &[&rustc_middle::ty::FieldDef],
    start: usize,
    end: usize,
) -> bool {
    let typing_env = ty::TypingEnv::post_analysis(tcx, owner);
    let Ok(struct_layout) = tcx.layout_of(typing_env.as_query_input(struct_ty)) else {
        return false;
    };
    let ty::TyKind::Adt(_, args) = struct_ty.kind() else {
        return false;
    };
    let elem_ty = fields[start].ty(tcx, args);
    let Ok(elem_layout) = tcx.layout_of(typing_env.as_query_input(elem_ty)) else {
        return false;
    };
    let elem_size = elem_layout.size;
    if elem_size == Size::ZERO {
        return false;
    }

    let first_offset = struct_layout.fields.offset(start);
    for (pos, field_idx) in (start..end).enumerate() {
        let field_ty = fields[field_idx].ty(tcx, args);
        let Ok(field_layout) = tcx.layout_of(typing_env.as_query_input(field_ty)) else {
            return false;
        };
        if field_layout.size != elem_size {
            return false;
        }
        if struct_layout.fields.offset(field_idx) != first_offset + elem_size * pos as u64 {
            return false;
        }
    }
    true
}

fn collect_field_ranges<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    points_to: &andersen::AnalysisResult,
    field_to_group: &FxHashMap<(LocalDefId, usize), usize>,
    field_ranges: &mut FxHashMap<(LocalDefId, usize), Vec<LocRange>>,
) {
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(box (_, Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place))) =
                &statement.kind
            else {
                continue;
            };
            let Some((struct_did, field_idx)) = candidate_field_from_place(body, place) else {
                continue;
            };
            let Some(&group_start) = field_to_group.get(&(struct_did, field_idx)) else {
                continue;
            };

            for loc in alias_target_locs_with_tys(points_to, body, tcx, fn_did, *place, 0) {
                if let Some(end) = points_to.ends.get(loc).copied() {
                    field_ranges
                        .entry((struct_did, group_start))
                        .or_default()
                        .push(LocRange { start: loc, end });
                }
            }
        }
    }
}

fn collect_offset_ranges<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    points_to: &andersen::AnalysisResult,
    offset_ranges: &mut Vec<OffsetRange<'tcx>>,
) {
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(box (_, Rvalue::BinaryOp(BinOp::Offset, box (ptr, _)))) =
                &statement.kind
            else {
                continue;
            };
            collect_operand_pointees(tcx, fn_did, body, points_to, ptr, offset_ranges);
        }

        let TerminatorKind::Call { func, args, .. } = &block.terminator().kind else {
            continue;
        };
        if !is_element_offset_call(tcx, func) {
            continue;
        }
        if let Some(arg) = args.first() {
            collect_operand_pointees(tcx, fn_did, body, points_to, &arg.node, offset_ranges);
        }
    }
}

fn collect_operand_pointees<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    body: &Body<'tcx>,
    points_to: &andersen::AnalysisResult,
    operand: &Operand<'tcx>,
    out: &mut Vec<OffsetRange<'tcx>>,
) {
    let Some(place) = operand.place() else {
        return;
    };
    let Some(pointee_ty) = operand.ty(&body.local_decls, tcx).builtin_deref(true) else {
        return;
    };
    for loc in alias_target_locs_with_tys(points_to, body, tcx, fn_did, place, 1) {
        if let Some(end) = points_to.ends.get(loc).copied() {
            out.push(OffsetRange {
                range: LocRange { start: loc, end },
                pointee_ty,
            });
        }
    }
}

fn is_element_offset_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Some(func) = func.constant() else {
        return false;
    };
    let ty::TyKind::FnDef(def_id, _) = func.ty().kind() else {
        return false;
    };
    matches!(
        tcx.item_name(*def_id).as_str(),
        "offset" | "wrapping_offset"
    ) && tcx.def_path_str(*def_id).contains("ptr::")
}

fn candidate_field_from_place<'tcx>(
    body: &Body<'tcx>,
    place: &Place<'tcx>,
) -> Option<(LocalDefId, usize)> {
    let mut base_ty = body.local_decls[place.local].ty;
    let mut candidate = None;

    for elem in place.projection {
        match elem {
            PlaceElem::Deref => {
                base_ty = base_ty.builtin_deref(true)?;
            }
            PlaceElem::Field(field, field_ty) => {
                if let ty::TyKind::Adt(adt_def, _) = base_ty.kind()
                    && adt_def.is_struct()
                    && !adt_def.is_union()
                    && let Some(struct_did) = adt_def.did().as_local()
                {
                    candidate = Some((struct_did, field.index()));
                }
                base_ty = field_ty;
            }
            PlaceElem::Index(_) | PlaceElem::ConstantIndex { .. } | PlaceElem::Subslice { .. } => {
                base_ty = base_ty.builtin_index()?;
            }
            PlaceElem::Downcast(_, _)
            | PlaceElem::OpaqueCast(_)
            | PlaceElem::UnwrapUnsafeBinder(_)
            | PlaceElem::Subtype(_) => {}
        }
    }

    candidate
}

fn project_nodes(
    points_to: &andersen::AnalysisResult,
    nodes: Vec<LocNode>,
    elem: PlaceElem<'_>,
) -> Vec<LocNode> {
    let mut next = Vec::new();
    match elem {
        PlaceElem::Deref => {
            for node in nodes {
                if let Some(LocEdges::Deref(succs)) = points_to.graph.get(&node) {
                    next.extend(succs.iter().copied());
                    continue;
                }
                let p0 = LocNode {
                    prefix: 0,
                    index: node.index,
                };
                if let Some(LocEdges::Deref(succs)) = points_to.graph.get(&p0) {
                    next.extend(succs.iter().copied());
                }
            }
        }
        PlaceElem::Field(field, _) => {
            for node in nodes {
                if let Some(LocEdges::Fields(succs)) = points_to.graph.get(&node)
                    && field.index() < succs.len()
                {
                    next.push(succs[field]);
                }
            }
        }
        PlaceElem::Index(_) => {
            for node in nodes {
                if let Some(LocEdges::Index(succ)) = points_to.graph.get(&node) {
                    next.push(*succ);
                }
            }
        }
        _ => {
            next = nodes;
        }
    }

    let mut seen = FxHashSet::default();
    next.retain(|node| seen.insert(*node));
    next
}

fn project_nodes_with_tys<'tcx>(
    points_to: &andersen::AnalysisResult,
    nodes: Vec<LocNode>,
    elem: PlaceElem<'tcx>,
    base_ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Vec<LocNode> {
    let mut next = project_nodes(points_to, nodes.clone(), elem);
    if matches!(elem, PlaceElem::Field(_, _)) && next.is_empty() {
        let PlaceElem::Field(field, _) = elem else { unreachable!() };
        if let Some(offset) = field_offset_for_ty(tcx, base_ty, field.index()) {
            next = nodes
                .into_iter()
                .filter_map(|node| {
                    let index = node.index + offset;
                    if index > points_to.ends[node.index] {
                        return None;
                    }
                    Some(LocNode {
                        prefix: node.prefix,
                        index,
                    })
                })
                .collect();
        }
    }
    let mut seen = FxHashSet::default();
    next.retain(|node| seen.insert(*node));
    next
}

fn projected_ty<'tcx>(ty: ty::Ty<'tcx>, elem: PlaceElem<'tcx>) -> Option<ty::Ty<'tcx>> {
    match elem {
        PlaceElem::Deref => match ty.kind() {
            ty::TyKind::Ref(_, inner, _) => Some(*inner),
            ty::TyKind::RawPtr(inner, _) => Some(*inner),
            _ => None,
        },
        PlaceElem::Field(_, field_ty) => Some(field_ty),
        PlaceElem::Index(_) => match ty.kind() {
            ty::TyKind::Array(inner, _) | ty::TyKind::Slice(inner) => Some(*inner),
            _ => None,
        },
        _ => None,
    }
}

fn alias_target_locs_with_tys<'tcx>(
    points_to: &andersen::AnalysisResult,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    place: Place<'tcx>,
    implicit_deref_count: usize,
) -> Vec<andersen::Loc> {
    let Some(start) = points_to.var_nodes.get(&(def_id, place.local)) else {
        return vec![];
    };
    let mut frontier = vec![*start];
    let mut current_ty = body.local_decls[place.local].ty;

    for elem in place.projection.iter() {
        frontier = project_nodes_with_tys(points_to, frontier, elem, current_ty, tcx);
        if frontier.is_empty() {
            return vec![];
        }
        let Some(next_ty) = projected_ty(current_ty, elem) else {
            return vec![];
        };
        current_ty = next_ty;
    }

    for _ in 0..implicit_deref_count {
        let elem = PlaceElem::Deref;
        frontier = project_nodes(points_to, frontier, elem);
        if frontier.is_empty() {
            return vec![];
        }
        let Some(next_ty) = projected_ty(current_ty, elem) else {
            return vec![];
        };
        current_ty = next_ty;
    }

    let mut out = Vec::new();
    let mut seen = FxHashSet::default();
    for loc in frontier.into_iter().map(|node| node.index) {
        if seen.insert(loc) {
            out.push(loc);
        }
    }
    out
}

fn field_offset_for_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    field_index: usize,
) -> Option<usize> {
    let ty::TyKind::Adt(adt, args) = ty.kind() else {
        return None;
    };
    if !adt.is_struct() && !adt.is_union() {
        return None;
    }
    let mut offset = 0;
    for (i, field) in adt.all_fields().enumerate() {
        if i == field_index {
            return Some(offset);
        }
        offset += ty_len(field.ty(tcx, args), tcx);
    }
    None
}

fn ty_len<'tcx>(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> usize {
    match ty.kind() {
        ty::TyKind::Ref(_, _, _) | ty::TyKind::RawPtr(_, _) => 1,
        ty::TyKind::Array(inner, len) => {
            ty_len(*inner, tcx) * len.try_to_target_usize(tcx).unwrap_or(0) as usize
        }
        ty::TyKind::Adt(adt, args) => {
            let mut len = 0;
            for field in adt.all_fields() {
                len += ty_len(field.ty(tcx, args), tcx);
            }
            len.max(1)
        }
        _ => 1,
    }
}

fn ranges_overlap(a: LocRange, b: LocRange) -> bool {
    a.start <= b.end && b.start <= a.end
}
