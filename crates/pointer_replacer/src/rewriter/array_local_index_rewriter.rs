use points_to::andersen;
use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor as AstVisitor},
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId, def::Res, def_id::LocalDefId, intravisit::Visitor as HirVisitor,
};
use rustc_middle::{
    mir::{
        Local, Location, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
        visit::{PlaceContext, Visitor as MirVisitor},
    },
    ty::{self, TyCtxt},
};
use rustc_span::Symbol;
use utils::{
    ast::{unwrap_cast_and_paren, unwrap_paren},
    ir::AstToHir,
};

use crate::{
    analyses::{
        self,
        array_local_provenance::{
            ArrayLocalProvenance, PfgNode, RewriteGroup, RewriteSelectionContext, SlotInfo,
            SlotPathElem, named_struct_field,
        },
        type_qualifier::foster::mutability::MutabilityResult,
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug)]
struct BindingRewrite {
    source_hir_id: HirId,
    index_name: String,
    base_hir_id: HirId,
    base_name: String,
    base_index_name: Option<String>,
    base_is_raw_ptr: bool,
    nullable: bool,
    ptr_ty: String,
    ptr_mut: bool,
    field_base: bool,
    base_proxy_hir_ids: FxHashSet<HirId>,
    group_member_hir_ids: FxHashSet<HirId>,
}

#[derive(Clone, Debug)]
struct BaseCursorRewrite {
    fn_def_id: LocalDefId,
    base_hir_id: HirId,
    base_name: String,
    index_name: String,
    base_is_raw_ptr: bool,
    ptr_ty: String,
    field_base: bool,
}

type BaseCursorKey = (HirId, String);

#[derive(Default)]
struct RewritePlan {
    by_hir_id: FxHashMap<HirId, BindingRewrite>,
    base_by_key: FxHashMap<BaseCursorKey, BaseCursorRewrite>,
    index_names_by_fn: FxHashMap<LocalDefId, FxHashSet<String>>,
}

pub(crate) fn apply_array_local_index_rewrite<'tcx>(
    krate: &mut Crate,
    input: &RustProgram<'tcx>,
    provenances: &FxHashMap<LocalDefId, ArrayLocalProvenance>,
    mutability_result: &MutabilityResult,
    nullity_result: &analyses::nullity::NullityResult,
    points_to: &andersen::AnalysisResult,
    ast_to_hir: &AstToHir,
) -> bool {
    let mut plan = build_rewrite_plan(
        input,
        provenances,
        mutability_result,
        nullity_result,
        points_to,
    );
    refine_base_pointer_kinds_from_ast(krate, ast_to_hir, input.tcx, &mut plan);
    prune_unsupported_direct_place_uses(krate, ast_to_hir, input.tcx, &mut plan);
    if plan.by_hir_id.is_empty() {
        return false;
    }

    let mut visitor = ArrayLocalIndexRewriteVisitor {
        tcx: input.tcx,
        ast_to_hir,
        plan,
        introduced_hir_ids: FxHashSet::default(),
        changed: false,
    };
    visitor.visit_crate(krate);
    visitor.changed
}

#[allow(dead_code)]
pub(crate) fn group_has_rewritable_binding<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &rustc_middle::mir::Body<'tcx>,
    provenance: &ArrayLocalProvenance,
    group: &RewriteGroup,
) -> bool {
    // index_tracked with a field base is unsupported.
    if group.base_slot_offset != 0 && group.index_tracked {
        return false;
    }
    let hir_to_mir = utils::ir::map_thir_to_mir(def_id, false, tcx);
    let local_to_hir: FxHashMap<Local, HirId> = hir_to_mir
        .binding_to_local
        .iter()
        .map(|(hir_id, local)| (*local, *hir_id))
        .collect();
    if !local_to_hir.contains_key(&group.base_local) {
        return false;
    }
    if group.index_tracked
        && !matches!(
            body.local_decls[group.base_local].ty.kind(),
            ty::TyKind::RawPtr(..)
        )
    {
        return false;
    }

    group.members.iter().any(|&slot_idx| {
        let Some(info) = provenance.slot_table.slot_infos.get(slot_idx) else {
            return false;
        };
        if info.root == group.base_local || !info.path.is_empty() {
            return false;
        }
        if !local_to_hir.contains_key(&info.root) {
            return false;
        }
        if !matches!(
            body.local_decls[info.root].ty.kind(),
            ty::TyKind::RawPtr(..)
        ) {
            return false;
        }
        // for field-base groups, a member is rewritable only if it is NOT a proxy
        // (proxies hold the base at offset 0 and are left unchanged).
        if group.base_slot_offset > 0 {
            return !local_is_pure_field_base_proxy(body, info.root);
        }
        true
    })
}

fn build_rewrite_plan<'tcx>(
    input: &RustProgram<'tcx>,
    provenances: &FxHashMap<LocalDefId, ArrayLocalProvenance>,
    mutability_result: &MutabilityResult,
    nullity_result: &analyses::nullity::NullityResult,
    points_to: &andersen::AnalysisResult,
) -> RewritePlan {
    let mut plan = RewritePlan::default();
    for &def_id in &input.functions {
        let Some(provenance) = provenances.get(&def_id) else {
            continue;
        };
        let body = input
            .tcx
            .mir_drops_elaborated_and_const_checked(def_id)
            .borrow();
        let groups = analyses::array_local_provenance::select_rewrite_groups(
            provenance,
            &body,
            mutability_result,
            def_id,
            RewriteSelectionContext {
                tcx: input.tcx,
                points_to,
            },
        );
        if groups.is_empty() {
            continue;
        }

        let hir_to_mir = utils::ir::map_thir_to_mir(def_id, false, input.tcx);
        let local_to_hir: FxHashMap<Local, HirId> = hir_to_mir
            .binding_to_local
            .iter()
            .map(|(hir_id, local)| (*local, *hir_id))
            .collect();
        let mut existing_names = binding_names_in_body(input.tcx, def_id);

        for group in groups {
            let mut context = GroupPlanContext {
                tcx: input.tcx,
                def_id,
                body: &body,
                provenance,
                nullity_result,
                local_to_hir: &local_to_hir,
                existing_names: &mut existing_names,
                plan: &mut plan,
            };
            add_group_to_plan(&mut context, &group);
        }
    }
    plan
}

fn refine_base_pointer_kinds_from_ast(
    krate: &Crate,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    plan: &mut RewritePlan,
) {
    if plan.by_hir_id.is_empty() {
        return;
    }
    let base_hir_ids = plan
        .by_hir_id
        .values()
        .map(|rewrite| rewrite.base_hir_id)
        .chain(plan.base_by_key.values().map(|rewrite| rewrite.base_hir_id))
        .collect();
    let base_names = plan
        .by_hir_id
        .values()
        .map(|rewrite| rewrite.base_name.clone())
        .chain(
            plan.base_by_key
                .values()
                .map(|rewrite| rewrite.base_name.clone()),
        )
        .collect();
    let mut visitor = BaseBindingTypeVisitor {
        ast_to_hir,
        tcx,
        base_hir_ids,
        base_names,
        base_is_raw_ptr_by_hir_id: FxHashMap::default(),
        base_is_raw_ptr_by_name: FxHashMap::default(),
    };
    visitor.visit_crate(krate);
    for rewrite in plan.by_hir_id.values_mut() {
        if let Some(&base_is_raw_ptr) = visitor.base_is_raw_ptr_by_hir_id.get(&rewrite.base_hir_id)
        {
            rewrite.base_is_raw_ptr = base_is_raw_ptr;
        } else if let Some(Some(base_is_raw_ptr)) =
            visitor.base_is_raw_ptr_by_name.get(&rewrite.base_name)
        {
            rewrite.base_is_raw_ptr = *base_is_raw_ptr;
        }
    }
    for rewrite in plan.base_by_key.values_mut() {
        if let Some(&base_is_raw_ptr) = visitor.base_is_raw_ptr_by_hir_id.get(&rewrite.base_hir_id)
        {
            rewrite.base_is_raw_ptr = base_is_raw_ptr;
        } else if let Some(Some(base_is_raw_ptr)) =
            visitor.base_is_raw_ptr_by_name.get(&rewrite.base_name)
        {
            rewrite.base_is_raw_ptr = *base_is_raw_ptr;
        }
    }
}

struct BaseBindingTypeVisitor<'a, 'tcx> {
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    base_hir_ids: FxHashSet<HirId>,
    base_names: FxHashSet<String>,
    base_is_raw_ptr_by_hir_id: FxHashMap<HirId, bool>,
    base_is_raw_ptr_by_name: FxHashMap<String, Option<bool>>,
}

impl AstVisitor<'_> for BaseBindingTypeVisitor<'_, '_> {
    fn visit_param(&mut self, param: &Param) {
        self.record_ast_pat_type_by_name(&param.pat, &param.ty);
        if let Some(hir_id) = self.param_binding_hir_id(param)
            && self.base_hir_ids.contains(&hir_id)
        {
            self.base_is_raw_ptr_by_hir_id
                .insert(hir_id, ast_ty_is_raw_ptr(&param.ty));
        }
        visit::walk_param(self, param);
    }

    fn visit_local(&mut self, local: &rustc_ast::Local) {
        if let Some(ty) = &local.ty {
            self.record_ast_pat_type_by_name(&local.pat, ty);
        }
        if let Some(hir_id) = self.local_binding_hir_id(local)
            && self.base_hir_ids.contains(&hir_id)
            && let Some(ty) = &local.ty
        {
            self.base_is_raw_ptr_by_hir_id
                .insert(hir_id, ast_ty_is_raw_ptr(ty));
        }
        visit::walk_local(self, local);
    }
}

impl BaseBindingTypeVisitor<'_, '_> {
    fn record_ast_pat_type_by_name(&mut self, pat: &Pat, ty: &Ty) {
        let PatKind::Ident(_, ident, _) = &pat.kind else {
            return;
        };
        let name = ident.name.to_string();
        if !self.base_names.contains(&name) {
            return;
        }
        let is_raw_ptr = ast_ty_is_raw_ptr(ty);
        self.base_is_raw_ptr_by_name
            .entry(name)
            .and_modify(|existing| {
                if *existing != Some(is_raw_ptr) {
                    *existing = None;
                }
            })
            .or_insert(Some(is_raw_ptr));
    }

    fn param_binding_hir_id(&self, param: &Param) -> Option<HirId> {
        let hir_param = self.ast_to_hir.get_param(param.id, self.tcx)?;
        let hir::PatKind::Binding(_, hir_id, _, _) = hir_param.pat.kind else {
            return None;
        };
        Some(hir_id)
    }

    fn local_binding_hir_id(&self, local: &rustc_ast::Local) -> Option<HirId> {
        let let_stmt = self.ast_to_hir.get_let_stmt(local.id, self.tcx)?;
        let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind else {
            return None;
        };
        Some(hir_id)
    }
}

fn ast_ty_is_raw_ptr(ty: &Ty) -> bool {
    match &ty.kind {
        TyKind::Ptr(_) => true,
        TyKind::Paren(inner) => ast_ty_is_raw_ptr(inner),
        _ => false,
    }
}

fn binding_names_in_body(tcx: TyCtxt<'_>, def_id: LocalDefId) -> FxHashSet<String> {
    struct NameVisitor {
        names: FxHashSet<String>,
    }
    impl<'tcx> hir::intravisit::Visitor<'tcx> for NameVisitor {
        fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
            if let hir::PatKind::Binding(_, _, ident, _) = pat.kind {
                self.names.insert(ident.name.to_string());
            }
            hir::intravisit::walk_pat(self, pat);
        }
    }

    let mut visitor = NameVisitor {
        names: FxHashSet::default(),
    };
    visitor.visit_body(tcx.hir_body_owned_by(def_id));
    visitor.names
}

struct GroupPlanContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &'a rustc_middle::mir::Body<'tcx>,
    provenance: &'a ArrayLocalProvenance,
    nullity_result: &'a analyses::nullity::NullityResult,
    local_to_hir: &'a FxHashMap<Local, HirId>,
    existing_names: &'a mut FxHashSet<String>,
    plan: &'a mut RewritePlan,
}

fn add_group_to_plan(context: &mut GroupPlanContext<'_, '_>, group: &RewriteGroup) {
    let Some(&base_hir_id) = context.local_to_hir.get(&group.base_local) else {
        return;
    };

    // Compute (base_name, proxy_hir_ids) depending on whether the base is a
    // direct local (offset 0) or a field path (offset > 0).
    let (base_name, proxy_hir_ids): (String, FxHashSet<HirId>) = if group.base_slot_offset == 0 {
        (
            context.tcx.hir_name(base_hir_id).to_string(),
            FxHashSet::default(),
        )
    } else {
        let Some(base_slot_info) =
            analyses::array_local_provenance::base_slot_info(context.provenance, group)
        else {
            return;
        };
        let local_name = context.tcx.hir_name(base_hir_id).to_string();
        let base_ty = context.body.local_decls[group.base_local].ty;
        let Some(name) =
            slot_path_to_expr_string(&local_name, &base_slot_info.path, base_ty, context.tcx)
        else {
            return;
        };
        // proxies: direct-local RawPtr members never assigned via a Call
        let proxies = group
            .members
            .iter()
            .filter_map(|&slot_idx| {
                let info = context.provenance.slot_table.slot_infos.get(slot_idx)?;
                if !info.path.is_empty() || info.root == group.base_local {
                    return None;
                }
                if !matches!(
                    context.body.local_decls[info.root].ty.kind(),
                    ty::TyKind::RawPtr(..)
                ) {
                    return None;
                }
                let &hir_id = context.local_to_hir.get(&info.root)?;
                (!group.index_tracked && local_is_pure_field_base_proxy(context.body, info.root))
                    .then_some(hir_id)
            })
            .collect();
        (name, proxies)
    };

    let base_is_raw_ptr = matches!(
        context.body.local_decls[group.base_local].ty.kind(),
        ty::TyKind::RawPtr(..)
    );
    let base_cursor_key = base_cursor_key(base_hir_id, &base_name);
    let group_member_hir_ids = group
        .members
        .iter()
        .filter_map(|&slot_idx| {
            let info = context.provenance.slot_table.slot_infos.get(slot_idx)?;
            if !info.path.is_empty() || info.root == group.base_local {
                return None;
            }
            if !matches!(
                context.body.local_decls[info.root].ty.kind(),
                ty::TyKind::RawPtr(..)
            ) {
                return None;
            }
            context.local_to_hir.get(&info.root).copied()
        })
        .collect::<FxHashSet<_>>();
    let base_index_name = if group.index_tracked {
        if let Some(rewrite) = context.plan.base_by_key.get(&base_cursor_key) {
            Some(rewrite.index_name.clone())
        } else {
            let Some(base_info) =
                analyses::array_local_provenance::base_slot_info(context.provenance, group)
            else {
                return;
            };
            let Some(base_ptr_ty) = slot_ty(context.body, context.tcx, base_info) else {
                return;
            };
            let ty::TyKind::RawPtr(pointee, mutability) = base_ptr_ty.kind() else {
                return;
            };
            let index_stem = if group.base_slot_offset == 0 {
                base_name.clone()
            } else {
                slot_path_to_index_stem(
                    &context.tcx.hir_name(base_hir_id).to_string(),
                    &base_info.path,
                    context.body.local_decls[group.base_local].ty,
                    context.tcx,
                )
                .unwrap_or_else(|| context.tcx.hir_name(base_hir_id).to_string())
            };
            let index_name = fresh_index_name(&index_stem, context.existing_names);
            let pointee = utils::ir::mir_ty_to_string(*pointee, context.tcx);
            let ptr_ty = format!(
                "*{} {}",
                if mutability.is_mut() { "mut" } else { "const" },
                pointee
            );
            context
                .plan
                .index_names_by_fn
                .entry(context.def_id)
                .or_default()
                .insert(index_name.clone());
            context.plan.base_by_key.insert(
                base_cursor_key,
                BaseCursorRewrite {
                    fn_def_id: context.def_id,
                    base_hir_id,
                    base_name: base_name.clone(),
                    index_name: index_name.clone(),
                    base_is_raw_ptr,
                    ptr_ty,
                    field_base: group.base_slot_offset != 0,
                },
            );
            Some(index_name)
        }
    } else {
        None
    };
    let non_null = context.nullity_result.non_null_locals.get(&context.def_id);

    for &slot_idx in &group.members {
        let Some(info) = context.provenance.slot_table.slot_infos.get(slot_idx) else {
            continue;
        };
        if info.root == group.base_local || !info.path.is_empty() {
            continue;
        }
        let Some(&source_hir_id) = context.local_to_hir.get(&info.root) else {
            continue;
        };
        // skip proxy locals — they hold the base at offset 0 and stay as-is.
        if proxy_hir_ids.contains(&source_hir_id) {
            continue;
        }
        if context.plan.by_hir_id.contains_key(&source_hir_id) {
            continue;
        }
        let source_name = context.tcx.hir_name(source_hir_id).to_string();
        let ptr_ty = context.body.local_decls[info.root].ty;
        let ty::TyKind::RawPtr(pointee, mutability) = ptr_ty.kind() else {
            continue;
        };
        let index_name = fresh_index_name(&source_name, context.existing_names);
        let pointee = utils::ir::mir_ty_to_string(*pointee, context.tcx);
        let ptr_ty = format!(
            "*{} {}",
            if mutability.is_mut() { "mut" } else { "const" },
            pointee
        );
        let nullable = context
            .provenance
            .provenance
            .unique_base(&PfgNode::Slot(slot_idx))
            .is_none()
            && !non_null.is_some_and(|set| set.contains(info.root));
        context
            .plan
            .index_names_by_fn
            .entry(context.def_id)
            .or_default()
            .insert(index_name.clone());
        context.plan.by_hir_id.insert(
            source_hir_id,
            BindingRewrite {
                source_hir_id,
                index_name,
                base_hir_id,
                base_name: base_name.clone(),
                base_index_name: base_index_name.clone(),
                base_is_raw_ptr,
                nullable,
                ptr_ty,
                ptr_mut: mutability.is_mut(),
                field_base: group.base_slot_offset != 0,
                base_proxy_hir_ids: proxy_hir_ids.clone(),
                group_member_hir_ids: group_member_hir_ids.clone(),
            },
        );
    }
}

fn slot_ty<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    info: &SlotInfo,
) -> Option<ty::Ty<'tcx>> {
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

fn fresh_index_name(source_name: &str, existing_names: &mut FxHashSet<String>) -> String {
    let mut candidate = format!("{source_name}_idx");
    let mut suffix = 1usize;
    while existing_names.contains(&candidate) {
        candidate = format!("{source_name}_idx_{suffix}");
        suffix += 1;
    }
    existing_names.insert(candidate.clone());
    candidate
}

fn slot_path_to_index_stem<'tcx>(
    local_name: &str,
    path: &[SlotPathElem],
    mut ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<String> {
    let mut parts = Vec::new();
    for elem in path {
        match elem {
            SlotPathElem::Pointee => {
                ty = ty.builtin_deref(true)?;
            }
            SlotPathElem::Field(field) => {
                let (field_name, field_ty) = named_struct_field(tcx, ty, *field)?;
                parts.push(field_name);
                ty = field_ty;
            }
            SlotPathElem::Element => return None,
        }
    }
    if parts.is_empty() {
        Some(local_name.to_string())
    } else {
        Some(parts.join("_"))
    }
}

fn slot_path_to_expr_string<'tcx>(
    local_name: &str,
    path: &[SlotPathElem],
    mut ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<String> {
    let mut expr = local_name.to_string();
    for elem in path {
        match elem {
            SlotPathElem::Pointee => {
                ty = ty.builtin_deref(true)?;
                expr = format!("(*{expr})");
            }
            SlotPathElem::Field(field) => {
                let (field_name, field_ty) = named_struct_field(tcx, ty, *field)?;
                expr = format!("{expr}.{field_name}");
                ty = field_ty;
            }
            SlotPathElem::Element => return None,
        }
    }
    Some(expr)
}

fn local_is_pure_field_base_proxy(body: &rustc_middle::mir::Body<'_>, local: Local) -> bool {
    let mut has_call_destination = false;
    let mut has_non_assignment_use = false;

    for (block, block_data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in block_data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            if let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind {
                if lhs.local == local && lhs.projection.is_empty() {
                    if rvalue_mentions_local(rvalue, local, location) {
                        has_non_assignment_use = true;
                    }
                    continue;
                }
            }
            if statement_mentions_local(statement, local, location) {
                has_non_assignment_use = true;
            }
        }
        if let Some(terminator) = &block_data.terminator
            && let TerminatorKind::Call { destination, .. } = &terminator.kind
        {
            if destination.local == local {
                has_call_destination = true;
            }
        }
        if let Some(terminator) = &block_data.terminator {
            let location = Location {
                block,
                statement_index: block_data.statements.len(),
            };
            if terminator_mentions_local(terminator, local, location) {
                has_non_assignment_use = true;
            }
        }
    }

    !has_call_destination && !has_non_assignment_use
}

struct LocalMentionVisitor {
    local: Local,
    found: bool,
}

impl<'tcx> MirVisitor<'tcx> for LocalMentionVisitor {
    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        if local == self.local && !matches!(context, PlaceContext::NonUse(_)) {
            self.found = true;
        }
    }
}

fn rvalue_mentions_local(rvalue: &Rvalue<'_>, local: Local, location: Location) -> bool {
    let mut visitor = LocalMentionVisitor {
        local,
        found: false,
    };
    visitor.visit_rvalue(rvalue, location);
    visitor.found
}

fn statement_mentions_local(statement: &Statement<'_>, local: Local, location: Location) -> bool {
    let mut visitor = LocalMentionVisitor {
        local,
        found: false,
    };
    visitor.visit_statement(statement, location);
    visitor.found
}

fn terminator_mentions_local(
    terminator: &Terminator<'_>,
    local: Local,
    location: Location,
) -> bool {
    let mut visitor = LocalMentionVisitor {
        local,
        found: false,
    };
    visitor.visit_terminator(terminator, location);
    visitor.found
}

fn prune_unsupported_direct_place_uses(
    krate: &Crate,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    plan: &mut RewritePlan,
) {
    if plan.by_hir_id.is_empty() {
        return;
    }

    let mut visitor = UnsupportedDirectPlaceUseVisitor {
        ast_to_hir,
        tcx,
        planned_rewrites: plan.by_hir_id.clone(),
        base_rewrites: plan.base_by_key.clone(),
        unsupported_hir_ids: FxHashSet::default(),
    };
    visitor.visit_crate(krate);
    if !visitor.unsupported_hir_ids.is_empty() {
        plan.by_hir_id
            .retain(|hir_id, _| !visitor.unsupported_hir_ids.contains(hir_id));
    }
    prune_orphan_base_cursors(plan);
}

fn prune_orphan_base_cursors(plan: &mut RewritePlan) {
    let live_base_keys = plan
        .by_hir_id
        .values()
        .filter(|rewrite| rewrite.base_index_name.is_some())
        .map(|rewrite| base_cursor_key(rewrite.base_hir_id, &rewrite.base_name))
        .collect::<FxHashSet<_>>();
    plan.base_by_key
        .retain(|base_key, _| live_base_keys.contains(base_key));
}

struct UnsupportedDirectPlaceUseVisitor<'a, 'tcx> {
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    planned_rewrites: FxHashMap<HirId, BindingRewrite>,
    base_rewrites: FxHashMap<BaseCursorKey, BaseCursorRewrite>,
    unsupported_hir_ids: FxHashSet<HirId>,
}

impl AstVisitor<'_> for UnsupportedDirectPlaceUseVisitor<'_, '_> {
    fn visit_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Assign(lhs, rhs, _) => {
                self.check_assignment(lhs, rhs);
                self.visit_expr(rhs);
            }
            ExprKind::AssignOp(_, lhs, rhs) => {
                if self.mark_direct_base_cursor(lhs).is_none()
                    && self.mark_direct_planned_local(lhs).is_none()
                {
                    self.visit_expr(lhs);
                }
                self.visit_expr(rhs);
            }
            ExprKind::AddrOf(_, _, inner) => {
                if self.mark_direct_base_cursor(inner).is_none()
                    && self.mark_direct_planned_local(inner).is_none()
                {
                    self.visit_expr(inner);
                }
            }
            _ => visit::walk_expr(self, expr),
        }
    }
}

impl UnsupportedDirectPlaceUseVisitor<'_, '_> {
    fn check_assignment(&mut self, lhs: &Expr, rhs: &Expr) {
        if let Some(base_key) =
            direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.base_rewrites, lhs)
        {
            if let Some(base_rewrite) = self.base_rewrites.get(&base_key) {
                let index = base_assignment_index_expr(
                    rhs,
                    self.ast_to_hir,
                    self.tcx,
                    &self.planned_rewrites,
                    base_rewrite,
                );
                let unsupported = matches!(index, IndexExpr::Null | IndexExpr::Unsupported)
                    || base_assignment_index_arg_contains_planned_local(
                        rhs,
                        self.ast_to_hir,
                        self.tcx,
                        &self.planned_rewrites,
                        base_rewrite,
                    );
                if unsupported {
                    self.mark_rewrites_for_base_unsupported(&base_key);
                }
                return;
            } else {
                self.mark_rewrites_for_base_unsupported(&base_key);
            }
        }

        let Some(hir_id) =
            direct_planned_local_hir_id(self.ast_to_hir, self.tcx, &self.planned_rewrites, lhs)
        else {
            self.visit_expr(lhs);
            return;
        };
        let Some(rewrite) = self.planned_rewrites.get(&hir_id) else {
            return;
        };
        let index = assignment_index_expr(
            rhs,
            self.ast_to_hir,
            self.tcx,
            &self.planned_rewrites,
            None,
            rewrite,
        );
        if index_init_expr(index, rewrite.nullable).is_none()
            || assignment_index_arg_contains_planned_local(
                rhs,
                self.ast_to_hir,
                self.tcx,
                &self.planned_rewrites,
                rewrite,
            )
        {
            self.unsupported_hir_ids.insert(hir_id);
        }
    }

    fn mark_rewrites_for_base_unsupported(&mut self, base_key: &BaseCursorKey) {
        for rewrite in self.planned_rewrites.values() {
            if base_cursor_key(rewrite.base_hir_id, &rewrite.base_name) == *base_key {
                self.unsupported_hir_ids.insert(rewrite.source_hir_id);
            }
        }
    }

    fn mark_direct_base_cursor(&mut self, expr: &Expr) -> Option<HirId> {
        let base_key =
            direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.base_rewrites, expr)?;
        if self.base_rewrites.contains_key(&base_key) {
            self.mark_rewrites_for_base_unsupported(&base_key);
            Some(base_key.0)
        } else {
            None
        }
    }

    fn mark_direct_planned_local(&mut self, expr: &Expr) -> Option<HirId> {
        let hir_id =
            direct_planned_local_hir_id(self.ast_to_hir, self.tcx, &self.planned_rewrites, expr)?;
        if self.planned_rewrites.contains_key(&hir_id) {
            self.unsupported_hir_ids.insert(hir_id);
            Some(hir_id)
        } else {
            None
        }
    }
}

struct PlannedLocalUseVisitor<'a, 'tcx> {
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
    planned_rewrites: &'a FxHashMap<HirId, BindingRewrite>,
    found: bool,
}

impl AstVisitor<'_> for PlannedLocalUseVisitor<'_, '_> {
    fn visit_expr(&mut self, expr: &Expr) {
        if self.found {
            return;
        }
        if direct_planned_local_hir_id(self.ast_to_hir, self.tcx, self.planned_rewrites, expr)
            .is_some()
        {
            self.found = true;
            return;
        }
        visit::walk_expr(self, expr);
    }
}

fn contains_planned_local_use(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
) -> bool {
    let mut visitor = PlannedLocalUseVisitor {
        ast_to_hir,
        tcx,
        planned_rewrites,
        found: false,
    };
    visitor.visit_expr(expr);
    visitor.found
}

fn assignment_index_arg_contains_planned_local(
    rhs: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    rewrite: &BindingRewrite,
) -> bool {
    let rhs = unwrap_paren(rhs);
    let ExprKind::MethodCall(call) = &rhs.kind else {
        return false;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return false;
    }
    let receiver = unwrap_cast_and_paren(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id);
    let receiver_is_base = receiver_hir_id == Some(rewrite.base_hir_id)
        || receiver_is_base_as_ptr(receiver, ast_to_hir, tcx, rewrite)
        || receiver_hir_id.is_some_and(|id| {
            rewrite.base_proxy_hir_ids.contains(&id)
                || (rewrite.field_base && rewrite.group_member_hir_ids.contains(&id))
        });
    if !receiver_is_base && receiver_hir_id != Some(rewrite.source_hir_id) {
        return false;
    }
    contains_planned_local_use(&call.args[0], ast_to_hir, tcx, planned_rewrites)
}

fn base_assignment_index_arg_contains_planned_local(
    rhs: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    base_rewrite: &BaseCursorRewrite,
) -> bool {
    let rhs = unwrap_paren(rhs);
    let ExprKind::MethodCall(call) = &rhs.kind else {
        return false;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return false;
    }
    let receiver = unwrap_cast_and_paren(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id);
    let receiver_is_base = (!base_rewrite.field_base
        && receiver_hir_id == Some(base_rewrite.base_hir_id))
        || receiver_is_base_as_ptr_for_context(
            receiver,
            ast_to_hir,
            tcx,
            base_rewrite.base_hir_id,
            &base_rewrite.base_name,
            base_rewrite.field_base,
        )
        || (base_rewrite.field_base && expr_matches_base_name(receiver, &base_rewrite.base_name));
    if !receiver_is_base
        && !receiver_hir_id.is_some_and(|hir_id| {
            planned_rewrites
                .get(&hir_id)
                .is_some_and(|rewrite| same_rewrite_base(rewrite, base_rewrite))
        })
    {
        return false;
    }
    contains_planned_local_use(&call.args[0], ast_to_hir, tcx, planned_rewrites)
}

fn direct_planned_local_hir_id(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    expr: &Expr,
) -> Option<HirId> {
    let hir_id = direct_local_hir_id(ast_to_hir, tcx, expr)?;
    planned_rewrites.contains_key(&hir_id).then_some(hir_id)
}

fn same_rewrite_base(rewrite: &BindingRewrite, base_rewrite: &BaseCursorRewrite) -> bool {
    rewrite.base_hir_id == base_rewrite.base_hir_id && rewrite.base_name == base_rewrite.base_name
}

fn base_cursor_key(base_hir_id: HirId, base_name: &str) -> BaseCursorKey {
    (base_hir_id, base_name.to_string())
}

fn direct_base_cursor_hir_id(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_rewrites: &FxHashMap<BaseCursorKey, BaseCursorRewrite>,
    expr: &Expr,
) -> Option<BaseCursorKey> {
    let hir_id = direct_local_hir_id(ast_to_hir, tcx, expr)?;
    base_rewrites.iter().find_map(|(key, rewrite)| {
        (!rewrite.field_base && rewrite.base_hir_id == hir_id).then_some(key.clone())
    })
}

fn direct_base_cursor_key(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_rewrites: &FxHashMap<BaseCursorKey, BaseCursorRewrite>,
    expr: &Expr,
) -> Option<BaseCursorKey> {
    if let Some(base_key) = direct_base_cursor_hir_id(ast_to_hir, tcx, base_rewrites, expr) {
        return Some(base_key);
    }
    base_rewrites.iter().find_map(|(key, rewrite)| {
        (rewrite.field_base
            && expr_matches_base_name(expr, &rewrite.base_name)
            && expr_is_projection_from_base_hir(expr, ast_to_hir, tcx, rewrite.base_hir_id))
        .then_some(key.clone())
    })
}

fn direct_local_hir_id(ast_to_hir: &AstToHir, tcx: TyCtxt<'_>, expr: &Expr) -> Option<HirId> {
    hir_id_of_ast_expr(ast_to_hir, tcx, unwrap_paren(expr).id)
}

#[derive(Clone)]
enum IndexExpr {
    Plain(Expr),
    Null,
    Unsupported,
}

fn hir_id_of_ast_expr(ast_to_hir: &AstToHir, tcx: TyCtxt<'_>, node_id: NodeId) -> Option<HirId> {
    let hir_expr = ast_to_hir.get_expr(node_id, tcx)?;
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_expr.kind else {
        return None;
    };
    let Res::Local(hir_id) = path.res else {
        return None;
    };
    Some(hir_id)
}

fn rewrite_binding_pat(pat: &mut Pat, index_name: &str) -> bool {
    let PatKind::Ident(_, ident, _) = &mut pat.kind else {
        return false;
    };
    ident.name = Symbol::intern(index_name);
    true
}

fn index_ty(nullable: bool) -> P<Ty> {
    if nullable {
        P(utils::ty!("Option<isize>"))
    } else {
        P(utils::ty!("isize"))
    }
}

fn is_null_expr(expr: &Expr) -> bool {
    let expr = unwrap_cast_and_paren(expr);
    match &expr.kind {
        ExprKind::Call(callee, _) => {
            let ExprKind::Path(_, path) = &unwrap_cast_and_paren(callee).kind else {
                return false;
            };
            let segments = path
                .segments
                .iter()
                .map(|seg| seg.ident.name.as_str())
                .collect::<Vec<_>>();
            matches!(
                segments.as_slice(),
                ["std", "ptr", "null" | "null_mut"] | ["core", "ptr", "null" | "null_mut"]
            )
        }
        ExprKind::Lit(lit) => lit.kind == token::LitKind::Integer && lit.symbol.as_str() == "0",
        _ => false,
    }
}

fn unwrap_pointer_producing_expr(expr: &Expr) -> &Expr {
    let expr = unwrap_cast_and_paren(expr);
    match &expr.kind {
        ExprKind::AddrOf(_, _, inner) => {
            let inner = unwrap_cast_and_paren(inner);
            if let ExprKind::Unary(UnOp::Deref, deref_inner) = &inner.kind {
                return unwrap_pointer_producing_expr(deref_inner);
            }
            expr
        }
        _ => expr,
    }
}

fn expr_matches_base_name(expr: &Expr, base_name: &str) -> bool {
    pprust::expr_to_string(unwrap_cast_and_paren(expr)).replace(' ', "")
        == base_name.replace(' ', "")
}

fn offset_index_arg_expr(name: &str, arg: &Expr) -> Expr {
    if name == "add" || matches!(unwrap_cast_and_paren(arg).kind, ExprKind::Lit(_)) {
        utils::expr!("({}) as isize", pprust::expr_to_string(arg))
    } else {
        utils::expr!("{}", pprust::expr_to_string(arg))
    }
}

fn add_index_expr(current: &str, offset: &Expr) -> Expr {
    utils::expr!("({}) + ({})", current, pprust::expr_to_string(offset))
}

fn relative_index_expr(current: &str, method_name: &str, arg: &Expr) -> Expr {
    let offset = offset_index_arg_expr(method_name, arg);
    add_index_expr(current, &offset)
}

fn base_current_index_expr(rewrite: &BindingRewrite) -> Option<&str> {
    rewrite.base_index_name.as_deref()
}

fn expr_is_projection_from_base_hir(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_hir_id: HirId,
) -> bool {
    let expr = unwrap_cast_and_paren(expr);
    if hir_id_of_ast_expr(ast_to_hir, tcx, expr.id) == Some(base_hir_id) {
        return true;
    }
    match &expr.kind {
        ExprKind::AddrOf(_, _, inner)
        | ExprKind::Field(inner, _)
        | ExprKind::Unary(UnOp::Deref, inner) => {
            expr_is_projection_from_base_hir(inner, ast_to_hir, tcx, base_hir_id)
        }
        _ => false,
    }
}

fn receiver_is_base_as_ptr_hir(
    receiver: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_hir_id: HirId,
) -> bool {
    let ExprKind::MethodCall(call) = &receiver.kind else {
        return false;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "as_ptr" | "as_mut_ptr") || !call.args.is_empty() {
        return false;
    }
    expr_is_projection_from_base_hir(&call.receiver, ast_to_hir, tcx, base_hir_id)
}

fn receiver_is_field_base_as_ptr(receiver: &Expr, base_name: &str) -> bool {
    let ExprKind::MethodCall(call) = &receiver.kind else {
        return false;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "as_ptr" | "as_mut_ptr") || !call.args.is_empty() {
        return false;
    }
    expr_matches_base_name(&call.receiver, base_name)
}

fn receiver_is_base_as_ptr_for_context(
    receiver: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_hir_id: HirId,
    base_name: &str,
    field_base: bool,
) -> bool {
    if field_base {
        receiver_is_field_base_as_ptr(receiver, base_name)
    } else {
        receiver_is_base_as_ptr_hir(receiver, ast_to_hir, tcx, base_hir_id)
    }
}

fn receiver_is_base_as_ptr(
    receiver: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    rewrite: &BindingRewrite,
) -> bool {
    receiver_is_base_as_ptr_for_context(
        receiver,
        ast_to_hir,
        tcx,
        rewrite.base_hir_id,
        &rewrite.base_name,
        rewrite.field_base,
    )
}

fn slice_base_expr_from_as_ptr_receiver(receiver: &Expr) -> &Expr {
    let receiver = unwrap_cast_and_paren(receiver);
    if let ExprKind::AddrOf(_, _, inner) = &receiver.kind {
        unwrap_cast_and_paren(inner)
    } else {
        receiver
    }
}

fn projected_as_ptr_receiver_base_name(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    rewrite: &BindingRewrite,
) -> Option<String> {
    if rewrite.field_base {
        return None;
    }
    let expr = unwrap_pointer_producing_expr(expr);
    let ExprKind::MethodCall(offset_call) = &expr.kind else {
        return None;
    };
    let name = offset_call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || offset_call.args.len() != 1 {
        return None;
    }
    let receiver = unwrap_cast_and_paren(&offset_call.receiver);
    let ExprKind::MethodCall(as_ptr_call) = &receiver.kind else {
        return None;
    };
    let as_ptr_name = as_ptr_call.seg.ident.name.as_str();
    if !matches!(as_ptr_name, "as_ptr" | "as_mut_ptr") || !as_ptr_call.args.is_empty() {
        return None;
    }
    let base_expr = slice_base_expr_from_as_ptr_receiver(&as_ptr_call.receiver);
    if hir_id_of_ast_expr(ast_to_hir, tcx, base_expr.id) == Some(rewrite.base_hir_id) {
        return None;
    }
    expr_is_projection_from_base_hir(base_expr, ast_to_hir, tcx, rewrite.base_hir_id)
        .then(|| pprust::expr_to_string(base_expr))
}

fn offset_from_base_expr(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    rewrite: &BindingRewrite,
) -> IndexExpr {
    pointer_index_from_base_expr(
        expr,
        ast_to_hir,
        tcx,
        rewrite.base_hir_id,
        &rewrite.base_name,
        rewrite.field_base,
        &rewrite.base_proxy_hir_ids,
        base_current_index_expr(rewrite),
    )
}

fn pointer_index_from_base_expr(
    expr: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    base_hir_id: HirId,
    base_name: &str,
    field_base: bool,
    base_proxy_hir_ids: &FxHashSet<HirId>,
    base_index_name: Option<&str>,
) -> IndexExpr {
    if is_null_expr(expr) {
        return IndexExpr::Null;
    }

    let expr = unwrap_pointer_producing_expr(expr);
    let expr_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, expr.id);
    if (!field_base && expr_hir_id == Some(base_hir_id))
        || expr_hir_id.is_some_and(|id| base_proxy_hir_ids.contains(&id))
        || (field_base && expr_matches_base_name(expr, base_name))
    {
        return IndexExpr::Plain(match base_index_name {
            Some(index_name) => utils::expr!("{}", index_name),
            None => utils::expr!("0isize"),
        });
    }

    let ExprKind::MethodCall(call) = &expr.kind else {
        return IndexExpr::Unsupported;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return IndexExpr::Unsupported;
    }
    let receiver = unwrap_cast_and_paren(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id);
    let receiver_is_base = (!field_base && receiver_hir_id == Some(base_hir_id))
        || receiver_is_base_as_ptr_for_context(
            receiver,
            ast_to_hir,
            tcx,
            base_hir_id,
            base_name,
            field_base,
        )
        || (field_base && expr_matches_base_name(receiver, base_name))
        || receiver_hir_id.is_some_and(|id| base_proxy_hir_ids.contains(&id));
    if !receiver_is_base {
        return IndexExpr::Unsupported;
    }
    let offset = offset_index_arg_expr(name, &call.args[0]);
    match base_index_name {
        Some(index_name) => IndexExpr::Plain(add_index_expr(index_name, &offset)),
        None => IndexExpr::Plain(offset),
    }
}

fn group_member_pointer_assignment_index_expr(
    rhs: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    rewrite: &BindingRewrite,
) -> IndexExpr {
    let rhs = unwrap_pointer_producing_expr(rhs);
    let ExprKind::MethodCall(call) = &rhs.kind else {
        return IndexExpr::Unsupported;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return IndexExpr::Unsupported;
    }
    let receiver = unwrap_pointer_producing_expr(&call.receiver);
    let Some(receiver_hir_id) = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id) else {
        return IndexExpr::Unsupported;
    };
    if !rewrite.group_member_hir_ids.contains(&receiver_hir_id) {
        return IndexExpr::Unsupported;
    }

    let rhs_ptr = pprust::expr_to_string(rhs);
    let base_index = base_current_index_expr(rewrite).unwrap_or("0isize");
    let base_ptr = base_offset_expr_for_index(rewrite, base_index);
    let relative = utils::expr!("({}).offset_from({})", rhs_ptr, base_ptr);
    match base_current_index_expr(rewrite) {
        Some(index_name) => IndexExpr::Plain(add_index_expr(index_name, &relative)),
        None => IndexExpr::Plain(relative),
    }
}

fn introduced_group_member_assignment_index_expr(
    rhs: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    introduced_hir_ids: &FxHashSet<HirId>,
    rewrite: &BindingRewrite,
) -> IndexExpr {
    let rhs = unwrap_pointer_producing_expr(rhs);
    let ExprKind::MethodCall(call) = &rhs.kind else {
        return IndexExpr::Unsupported;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return IndexExpr::Unsupported;
    }
    let receiver = unwrap_pointer_producing_expr(&call.receiver);
    let Some(receiver_hir_id) = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id) else {
        return IndexExpr::Unsupported;
    };
    if !rewrite.group_member_hir_ids.contains(&receiver_hir_id)
        || !introduced_hir_ids.contains(&receiver_hir_id)
    {
        return IndexExpr::Unsupported;
    }
    let Some(receiver_rewrite) = planned_rewrites.get(&receiver_hir_id) else {
        return IndexExpr::Unsupported;
    };
    if receiver_rewrite.base_hir_id != rewrite.base_hir_id
        || receiver_rewrite.base_name != rewrite.base_name
    {
        return IndexExpr::Unsupported;
    }
    IndexExpr::Plain(relative_index_expr(
        &idx_read_expr(receiver_rewrite),
        name,
        &call.args[0],
    ))
}

fn assignment_index_expr(
    rhs: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    introduced_hir_ids: Option<&FxHashSet<HirId>>,
    rewrite: &BindingRewrite,
) -> IndexExpr {
    match offset_from_base_expr(rhs, ast_to_hir, tcx, rewrite) {
        IndexExpr::Unsupported => {}
        index => return index,
    }

    let rhs = unwrap_pointer_producing_expr(rhs);
    let ExprKind::MethodCall(call) = &rhs.kind else {
        return IndexExpr::Unsupported;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return IndexExpr::Unsupported;
    }
    let receiver = unwrap_pointer_producing_expr(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id);
    if receiver_hir_id != Some(rewrite.source_hir_id) {
        if receiver_hir_id.is_some_and(|hir_id| {
            planned_rewrites.contains_key(&hir_id)
                && introduced_hir_ids.is_some_and(|introduced| introduced.contains(&hir_id))
        }) {
            return IndexExpr::Unsupported;
        }
        return group_member_pointer_assignment_index_expr(rhs, ast_to_hir, tcx, rewrite);
    }
    IndexExpr::Plain(relative_index_expr(
        &idx_read_expr(rewrite),
        name,
        &call.args[0],
    ))
}

fn base_assignment_index_expr(
    rhs: &Expr,
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    planned_rewrites: &FxHashMap<HirId, BindingRewrite>,
    base_rewrite: &BaseCursorRewrite,
) -> IndexExpr {
    if is_null_expr(rhs) {
        return IndexExpr::Null;
    }
    let rhs = unwrap_cast_and_paren(rhs);
    if !base_rewrite.field_base
        && hir_id_of_ast_expr(ast_to_hir, tcx, rhs.id) == Some(base_rewrite.base_hir_id)
    {
        return IndexExpr::Plain(utils::expr!("{}", base_rewrite.index_name));
    }
    if base_rewrite.field_base && expr_matches_base_name(rhs, &base_rewrite.base_name) {
        return IndexExpr::Plain(utils::expr!("{}", base_rewrite.index_name));
    }
    if let Some(rewrite) = direct_planned_local_hir_id(ast_to_hir, tcx, planned_rewrites, rhs)
        .and_then(|hir_id| planned_rewrites.get(&hir_id))
        && same_rewrite_base(rewrite, base_rewrite)
    {
        return IndexExpr::Plain(utils::expr!("{}", idx_read_expr(rewrite)));
    }

    let ExprKind::MethodCall(call) = &rhs.kind else {
        return IndexExpr::Unsupported;
    };
    let name = call.seg.ident.name.as_str();
    if !matches!(name, "offset" | "add") || call.args.len() != 1 {
        return IndexExpr::Unsupported;
    }
    let receiver = unwrap_cast_and_paren(&call.receiver);
    let receiver_hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, receiver.id);
    let receiver_is_base = (!base_rewrite.field_base
        && receiver_hir_id == Some(base_rewrite.base_hir_id))
        || receiver_is_base_as_ptr_for_context(
            receiver,
            ast_to_hir,
            tcx,
            base_rewrite.base_hir_id,
            &base_rewrite.base_name,
            base_rewrite.field_base,
        )
        || (base_rewrite.field_base && expr_matches_base_name(receiver, &base_rewrite.base_name));
    if receiver_is_base {
        let offset = offset_index_arg_expr(name, &call.args[0]);
        return IndexExpr::Plain(add_index_expr(&base_rewrite.index_name, &offset));
    }
    if let Some(rewrite) = receiver_hir_id.and_then(|hir_id| planned_rewrites.get(&hir_id))
        && same_rewrite_base(rewrite, base_rewrite)
    {
        return IndexExpr::Plain(relative_index_expr(
            &idx_read_expr(rewrite),
            name,
            &call.args[0],
        ));
    }
    IndexExpr::Unsupported
}

fn index_init_expr(index: IndexExpr, nullable: bool) -> Option<Expr> {
    match (index, nullable) {
        (IndexExpr::Plain(expr), false) => Some(expr),
        (IndexExpr::Plain(expr), true) => {
            Some(utils::expr!("Some({})", pprust::expr_to_string(&expr)))
        }
        (IndexExpr::Null, true) => Some(utils::expr!("None")),
        (IndexExpr::Null, false) | (IndexExpr::Unsupported, _) => None,
    }
}

fn index_assignment_rhs_expr(index: IndexExpr, nullable: bool) -> Option<Expr> {
    index_init_expr(index, nullable)
}

fn idx_read_expr(rewrite: &BindingRewrite) -> String {
    if rewrite.nullable {
        format!("{}.unwrap()", rewrite.index_name)
    } else {
        rewrite.index_name.clone()
    }
}

fn base_offset_expr_for_parts(base_name: &str, base_is_raw_ptr: bool, index_expr: &str) -> String {
    if base_is_raw_ptr {
        format!("({base_name}).offset({index_expr})")
    } else {
        format!("({base_name}).as_ptr().offset({index_expr})")
    }
}

fn base_offset_expr_for_index(rewrite: &BindingRewrite, index_expr: &str) -> String {
    base_offset_expr_for_parts(&rewrite.base_name, rewrite.base_is_raw_ptr, index_expr)
}

fn pointer_expr_for_index(rewrite: &BindingRewrite) -> Expr {
    let base_offset = base_offset_expr_for_index(rewrite, &idx_read_expr(rewrite));
    utils::expr!("{} as {}", base_offset, rewrite.ptr_ty)
}

fn pointer_value_expr(rewrite: &BindingRewrite) -> Expr {
    if rewrite.nullable {
        let null_fn = if rewrite.ptr_mut {
            "std::ptr::null_mut()"
        } else {
            "std::ptr::null()"
        };
        utils::expr!(
            "{}.map_or({} as {}, |idx| ({}) as {})",
            rewrite.index_name,
            null_fn,
            rewrite.ptr_ty,
            base_offset_expr_for_index(rewrite, "idx"),
            rewrite.ptr_ty
        )
    } else {
        pointer_expr_for_index(rewrite)
    }
}

fn base_cursor_pointer_expr(rewrite: &BaseCursorRewrite) -> Expr {
    let base_offset = base_offset_expr_for_parts(
        &rewrite.base_name,
        rewrite.base_is_raw_ptr,
        &rewrite.index_name,
    );
    utils::expr!("{} as {}", base_offset, rewrite.ptr_ty)
}

fn introduced_planned_local_hir_id(
    ast_to_hir: &AstToHir,
    tcx: TyCtxt<'_>,
    introduced_hir_ids: &FxHashSet<HirId>,
    expr: &Expr,
) -> Option<HirId> {
    let hir_id = hir_id_of_ast_expr(ast_to_hir, tcx, unwrap_cast_and_paren(expr).id)?;
    introduced_hir_ids.contains(&hir_id).then_some(hir_id)
}

struct ArrayLocalIndexRewriteVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a AstToHir,
    plan: RewritePlan,
    introduced_hir_ids: FxHashSet<HirId>,
    changed: bool,
}

impl MutVisitor for ArrayLocalIndexRewriteVisitor<'_, '_> {
    fn visit_item(&mut self, item: &mut Item) {
        if let ItemKind::Fn(box fn_item) = &mut item.kind
            && let Some(def_id) = self.ast_to_hir.global_map.get(&item.id).copied()
        {
            let mut cursors = self
                .plan
                .base_by_key
                .values()
                .filter(|rewrite| rewrite.fn_def_id == def_id)
                .cloned()
                .collect::<Vec<_>>();
            cursors.sort_by(|a, b| a.index_name.cmp(&b.index_name));
            if !cursors.is_empty() {
                let stmts = &mut fn_item.body.as_mut().unwrap().stmts;
                for rewrite in cursors.into_iter().rev() {
                    stmts.insert(
                        0,
                        utils::stmt!("let mut {}: isize = 0isize;", rewrite.index_name),
                    );
                }
                self.changed = true;
            }
        }
        mut_visit::walk_item(self, item);
    }

    fn visit_local(&mut self, local: &mut rustc_ast::Local) {
        let Some(let_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx) else {
            mut_visit::walk_local(self, local);
            return;
        };
        let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind else {
            mut_visit::walk_local(self, local);
            return;
        };
        let Some(mut rewrite) = self.plan.by_hir_id.get(&hir_id).cloned() else {
            mut_visit::walk_local(self, local);
            return;
        };
        let Some(init) = local.kind.init_mut() else {
            mut_visit::walk_local(self, local);
            return;
        };
        if let Some(base_name) =
            projected_as_ptr_receiver_base_name(init, self.ast_to_hir, self.tcx, &rewrite)
        {
            rewrite.base_name = base_name;
            rewrite.base_is_raw_ptr = false;
            self.plan.by_hir_id.insert(hir_id, rewrite.clone());
        }
        let mut index = offset_from_base_expr(init, self.ast_to_hir, self.tcx, &rewrite);
        if let IndexExpr::Unsupported = index {
            index = introduced_group_member_assignment_index_expr(
                init,
                self.ast_to_hir,
                self.tcx,
                &self.plan.by_hir_id,
                &self.introduced_hir_ids,
                &rewrite,
            );
        }
        let Some(new_init) = index_init_expr(index, rewrite.nullable) else {
            mut_visit::walk_local(self, local);
            return;
        };
        if !rewrite_binding_pat(&mut local.pat, &rewrite.index_name) {
            mut_visit::walk_local(self, local);
            return;
        }
        local.ty = Some(index_ty(rewrite.nullable));
        *init = P(new_init);
        self.introduced_hir_ids.insert(hir_id);
        self.changed = true;
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Assign(lhs, rhs, _) => {
                if let Some(base_key) =
                    direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, lhs)
                    && let Some(rewrite) = self.plan.base_by_key.get(&base_key)
                {
                    let index = base_assignment_index_expr(
                        rhs,
                        self.ast_to_hir,
                        self.tcx,
                        &self.plan.by_hir_id,
                        rewrite,
                    );
                    if let IndexExpr::Plain(new_rhs) = index {
                        *lhs = P(utils::expr!("{}", rewrite.index_name));
                        *rhs = P(new_rhs);
                        self.changed = true;
                    } else {
                        self.visit_expr(rhs);
                    }
                    return;
                }
                if let Some(hir_id) = introduced_planned_local_hir_id(
                    self.ast_to_hir,
                    self.tcx,
                    &self.introduced_hir_ids,
                    lhs,
                ) && let Some(rewrite) = self.plan.by_hir_id.get(&hir_id)
                {
                    let mut index = introduced_group_member_assignment_index_expr(
                        rhs,
                        self.ast_to_hir,
                        self.tcx,
                        &self.plan.by_hir_id,
                        &self.introduced_hir_ids,
                        rewrite,
                    );
                    if let IndexExpr::Unsupported = index {
                        index = assignment_index_expr(
                            rhs,
                            self.ast_to_hir,
                            self.tcx,
                            &self.plan.by_hir_id,
                            Some(&self.introduced_hir_ids),
                            rewrite,
                        );
                    }
                    if let Some(new_rhs) = index_assignment_rhs_expr(index, rewrite.nullable) {
                        *lhs = P(utils::expr!("{}", rewrite.index_name));
                        *rhs = P(new_rhs);
                        self.changed = true;
                    } else {
                        self.visit_expr(rhs);
                    }
                } else {
                    self.visit_expr(lhs);
                    self.visit_expr(rhs);
                }
                return;
            }
            ExprKind::AssignOp(_, lhs, rhs) => {
                if direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, lhs)
                    .is_none()
                    && introduced_planned_local_hir_id(
                        self.ast_to_hir,
                        self.tcx,
                        &self.introduced_hir_ids,
                        lhs,
                    )
                    .is_none()
                {
                    self.visit_expr(lhs);
                }
                self.visit_expr(rhs);
                return;
            }
            ExprKind::AddrOf(_, _, inner) => {
                if direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, inner)
                    .is_none()
                    && introduced_planned_local_hir_id(
                        self.ast_to_hir,
                        self.tcx,
                        &self.introduced_hir_ids,
                        inner,
                    )
                    .is_none()
                {
                    self.visit_expr(inner);
                }
                return;
            }
            _ => {}
        }

        if let ExprKind::MethodCall(call) = &expr.kind {
            let receiver = unwrap_paren(&call.receiver);
            if call.seg.ident.name.as_str() == "is_null"
                && call.args.is_empty()
                && let Some(hir_id) = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, receiver.id)
                && self.introduced_hir_ids.contains(&hir_id)
                && let Some(rewrite) = self.plan.by_hir_id.get(&hir_id)
            {
                *expr = if rewrite.nullable {
                    utils::expr!("{}.is_none()", rewrite.index_name)
                } else {
                    utils::expr!("false")
                };
                self.changed = true;
                return;
            }
        }

        if let ExprKind::Binary(op, lhs, rhs) = &expr.kind
            && matches!(
                op.node,
                BinOpKind::Eq
                    | BinOpKind::Ne
                    | BinOpKind::Lt
                    | BinOpKind::Le
                    | BinOpKind::Gt
                    | BinOpKind::Ge
            )
        {
            let lhs_hir =
                hir_id_of_ast_expr(self.ast_to_hir, self.tcx, unwrap_cast_and_paren(lhs).id);
            let rhs_hir =
                hir_id_of_ast_expr(self.ast_to_hir, self.tcx, unwrap_cast_and_paren(rhs).id);
            let lhs_rewrite = lhs_hir.and_then(|hir_id| self.plan.by_hir_id.get(&hir_id));
            let rhs_rewrite = rhs_hir.and_then(|hir_id| self.plan.by_hir_id.get(&hir_id));
            let lhs_introduced =
                lhs_hir.is_some_and(|hir_id| self.introduced_hir_ids.contains(&hir_id));
            let rhs_introduced =
                rhs_hir.is_some_and(|hir_id| self.introduced_hir_ids.contains(&hir_id));
            if let (Some(lhs_rewrite), Some(rhs_rewrite)) = (lhs_rewrite, rhs_rewrite)
                && lhs_introduced
                && rhs_introduced
                && !lhs_rewrite.nullable
                && !rhs_rewrite.nullable
                && lhs_rewrite.base_hir_id == rhs_rewrite.base_hir_id
                && lhs_rewrite.base_name == rhs_rewrite.base_name
                && lhs_rewrite.ptr_ty == rhs_rewrite.ptr_ty
            {
                let lhs_idx = idx_read_expr(lhs_rewrite);
                let rhs_idx = idx_read_expr(rhs_rewrite);
                *expr = match op.node {
                    BinOpKind::Eq => utils::expr!("{lhs_idx} == {rhs_idx}"),
                    BinOpKind::Ne => utils::expr!("{lhs_idx} != {rhs_idx}"),
                    BinOpKind::Lt => utils::expr!("{lhs_idx} < {rhs_idx}"),
                    BinOpKind::Le => utils::expr!("{lhs_idx} <= {rhs_idx}"),
                    BinOpKind::Gt => utils::expr!("{lhs_idx} > {rhs_idx}"),
                    BinOpKind::Ge => utils::expr!("{lhs_idx} >= {rhs_idx}"),
                    _ => unreachable!(),
                };
                self.changed = true;
                return;
            }
        }

        if let ExprKind::Unary(UnOp::Deref, inner) = &mut expr.kind
            && let Some(base_key) =
                direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, inner)
            && let Some(rewrite) = self.plan.base_by_key.get(&base_key)
        {
            let ptr = base_cursor_pointer_expr(rewrite);
            *expr = utils::expr!("*({})", pprust::expr_to_string(&ptr));
            self.changed = true;
            return;
        }

        if let ExprKind::Unary(UnOp::Deref, inner) = &mut expr.kind
            && let Some(hir_id) = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, inner.id)
            && self.introduced_hir_ids.contains(&hir_id)
            && let Some(rewrite) = self.plan.by_hir_id.get(&hir_id)
        {
            let ptr = pointer_expr_for_index(rewrite);
            *expr = utils::expr!("*({})", pprust::expr_to_string(&ptr));
            self.changed = true;
            return;
        }

        if let ExprKind::MethodCall(call) = &expr.kind
            && call.seg.ident.name.as_str() == "offset_from"
            && call.args.len() == 1
        {
            let receiver = unwrap_cast_and_paren(&call.receiver);
            let arg = unwrap_cast_and_paren(&call.args[0]);
            let receiver_hir = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, receiver.id);
            let arg_hir = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, arg.id);
            let receiver_rewrite = receiver_hir.and_then(|hir_id| self.plan.by_hir_id.get(&hir_id));
            let arg_rewrite = arg_hir.and_then(|hir_id| self.plan.by_hir_id.get(&hir_id));
            let receiver_introduced =
                receiver_hir.is_some_and(|hir_id| self.introduced_hir_ids.contains(&hir_id));
            let arg_introduced =
                arg_hir.is_some_and(|hir_id| self.introduced_hir_ids.contains(&hir_id));
            let replacement = if let (Some(lhs), Some(rhs)) = (receiver_rewrite, arg_rewrite)
                && lhs.base_hir_id == rhs.base_hir_id
                && lhs.base_name == rhs.base_name
            {
                if receiver_introduced && arg_introduced {
                    Some(utils::expr!(
                        "({}) - ({})",
                        idx_read_expr(lhs),
                        idx_read_expr(rhs)
                    ))
                } else if arg_introduced {
                    let base_ptr = base_offset_expr_for_index(rhs, &idx_read_expr(rhs));
                    Some(utils::expr!(
                        "({}).offset_from({})",
                        pprust::expr_to_string(receiver),
                        base_ptr
                    ))
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(replacement) = replacement {
                *expr = replacement;
                self.changed = true;
                return;
            }
        }

        mut_visit::walk_expr(self, expr);

        if let Some(base_key) =
            direct_base_cursor_key(self.ast_to_hir, self.tcx, &self.plan.base_by_key, expr)
            && let Some(rewrite) = self.plan.base_by_key.get(&base_key)
        {
            *expr = base_cursor_pointer_expr(rewrite);
            self.changed = true;
            return;
        }

        if let Some(hir_id) = hir_id_of_ast_expr(self.ast_to_hir, self.tcx, expr.id)
            && self.introduced_hir_ids.contains(&hir_id)
            && let Some(rewrite) = self.plan.by_hir_id.get(&hir_id)
        {
            *expr = pointer_value_expr(rewrite);
            self.changed = true;
        }
    }
}

trait LocalKindInitMut {
    fn init_mut(&mut self) -> Option<&mut P<Expr>>;
}

impl LocalKindInitMut for LocalKind {
    fn init_mut(&mut self) -> Option<&mut P<Expr>> {
        match self {
            LocalKind::Init(init) | LocalKind::InitElse(init, _) => Some(init),
            LocalKind::Decl => None,
        }
    }
}
