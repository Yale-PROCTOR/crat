use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    *,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir, def::Res};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{DUMMY_SP, Ident, Symbol, def_id::LocalDefId};
use thin_vec::{ThinVec, thin_vec};
use utils::ir::AstToHir;

use crate::analyses::struct_array_field::{FieldGroup, StructRewriteCandidates};

#[derive(Clone, Copy)]
struct StructArrayCtx<'a, 'tcx> {
    candidates: &'a StructRewriteCandidates,
    ast_to_hir: &'a AstToHir,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> StructArrayCtx<'a, 'tcx> {
    fn new(
        candidates: &'a StructRewriteCandidates,
        ast_to_hir: &'a AstToHir,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self {
            candidates,
            ast_to_hir,
            tcx,
        }
    }

    fn candidate_groups(&self, struct_did: LocalDefId) -> Option<&'a [FieldGroup]> {
        self.candidates.get(&struct_did).map(Vec::as_slice)
    }

    /// resolve the type of an expression from its AST NodeId via HIR
    fn expr_struct_did(&self, node_id: NodeId) -> Option<LocalDefId> {
        let hir_expr = self.ast_to_hir.get_expr(node_id, self.tcx)?;
        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
        let ty = typeck.expr_ty(hir_expr);
        let ty::TyKind::Adt(adt_def, _) = ty.kind() else {
            return None;
        };
        adt_def.did().as_local()
    }

    fn struct_field_order(&self, node_id: NodeId) -> Option<Vec<Symbol>> {
        let hir_expr = self.ast_to_hir.get_expr(node_id, self.tcx)?;
        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
        let struct_ty = typeck.expr_ty(hir_expr);
        let ty::TyKind::Adt(adt_def, _) = struct_ty.kind() else {
            return None;
        };
        Some(adt_def.all_fields().map(|f| f.name).collect())
    }

    fn offset_of_struct_did(&self, expr: &Expr, ast_ty: &Ty) -> Option<LocalDefId> {
        if let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx)
            && let hir::ExprKind::OffsetOf(hir_ty, _) = hir_expr.kind
            && let Some(struct_did) = self.hir_ty_struct_did(hir_ty)
        {
            return Some(struct_did);
        }

        let hir_ty = self.ast_to_hir.get_ty(ast_ty.id, self.tcx)?;
        self.hir_ty_struct_did(hir_ty)
    }

    fn hir_ty_struct_did(&self, hir_ty: &hir::Ty<'_>) -> Option<LocalDefId> {
        let hir::TyKind::Path(hir::QPath::Resolved(_, path)) = hir_ty.kind else {
            return None;
        };
        let Res::Def(_, def_id) = path.res else {
            return None;
        };
        let ty = self.tcx.type_of(def_id).skip_binder();
        let ty::TyKind::Adt(adt_def, _) = ty.kind() else {
            return None;
        };
        if adt_def.is_struct() && !adt_def.is_union() {
            adt_def.did().as_local()
        } else {
            None
        }
    }
}

fn group_for_field(groups: &[FieldGroup], field_name: Symbol) -> Option<(&FieldGroup, usize)> {
    groups
        .iter()
        .find_map(|group| group.group_index(field_name).map(|idx| (group, idx)))
}

struct StructArrayTransformVisitor<'a, 'tcx> {
    ctx: StructArrayCtx<'a, 'tcx>,
}

impl<'a, 'tcx> StructArrayTransformVisitor<'a, 'tcx> {
    fn new(
        candidates: &'a StructRewriteCandidates,
        ast_to_hir: &'a AstToHir,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self {
            ctx: StructArrayCtx::new(candidates, ast_to_hir, tcx),
        }
    }
}

impl MutVisitor for StructArrayTransformVisitor<'_, '_> {
    fn visit_item(&mut self, item: &mut Item) {
        if let ItemKind::Struct(_, _, VariantData::Struct { ref mut fields, .. }) = item.kind {
            let struct_did = self.ctx.ast_to_hir.global_map.get(&item.id).copied();
            if let Some(groups) = struct_did.and_then(|did| self.ctx.candidate_groups(did)) {
                rewrite_struct_definition_fields(fields, groups);
            }
        }
        mut_visit::walk_item(self, item);
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        // recurse into sub-expressions first
        mut_visit::walk_expr(self, expr);

        match expr.kind {
            ExprKind::Field(_, _) => {
                self.rewrite_field_expr(expr);
            }
            ExprKind::Struct(_) => {
                self.rewrite_struct_expr(expr);
            }
            _ => {}
        }
    }
}

impl StructArrayTransformVisitor<'_, '_> {
    fn rewrite_field_expr(&self, expr: &mut Expr) {
        let ExprKind::Field(ref base_expr, field_ident) = expr.kind else {
            return;
        };
        let field_name = field_ident.name;

        let Some(struct_did) = self.ctx.expr_struct_did(base_expr.id) else {
            return;
        };
        let Some(groups) = self.ctx.candidate_groups(struct_did) else {
            return;
        };
        let Some((group, field_idx)) = group_for_field(groups, field_name) else {
            return;
        };
        let array_name = group.array_name();

        // rewrite: expr.field_name to (expr.array_name)[group_idx]
        let span = expr.span;
        let old_expr = utils::ast::take_expr(expr);
        let ExprKind::Field(base, _) = old_expr.kind else { unreachable!() };

        let field_expr = Expr {
            id: DUMMY_NODE_ID,
            kind: ExprKind::Field(base, Ident::new(array_name, span)),
            span,
            attrs: thin_vec![],
            tokens: None,
        };
        let idx_expr = utils::expr!("{}", field_idx);
        expr.kind = ExprKind::Index(P(field_expr), P(idx_expr), span);
    }

    fn rewrite_struct_expr(&self, expr: &mut Expr) {
        let expr_id = expr.id;
        let Some(struct_did) = self.ctx.expr_struct_did(expr_id) else {
            return;
        };
        let Some(groups) = self.ctx.candidate_groups(struct_did) else {
            return;
        };

        let ExprKind::Struct(ref se) = expr.kind else { unreachable!() };
        if !struct_literal_has_group_field(se, groups) {
            return;
        }

        let Some(def_order) = self.ctx.struct_field_order(expr_id) else {
            return;
        };
        let ExprKind::Struct(ref mut se) = expr.kind else {
            return;
        };
        let old_fields = std::mem::take(&mut se.fields);
        se.fields = build_rewritten_struct_fields(old_fields, groups, &def_order);
    }
}

fn rewrite_struct_definition_fields(fields: &mut ThinVec<FieldDef>, groups: &[FieldGroup]) {
    let mut sorted_groups: Vec<&FieldGroup> = groups.iter().collect();
    sorted_groups.sort_by(|a, b| b.start_idx.cmp(&a.start_idx));

    for group in sorted_groups {
        let elem_ty = fields[group.start_idx].ty.clone();
        let span = fields[group.start_idx].span;
        fields[group.start_idx].ty = P(Ty {
            id: DUMMY_NODE_ID,
            kind: TyKind::Array(
                elem_ty,
                AnonConst {
                    id: DUMMY_NODE_ID,
                    value: P(utils::expr!("{}", group.count)),
                },
            ),
            span,
            tokens: None,
        });
        fields.drain(group.start_idx + 1..group.start_idx + group.count);
    }
}

fn struct_literal_has_group_field(se: &StructExpr, groups: &[FieldGroup]) -> bool {
    se.fields
        .iter()
        .any(|ef| group_for_field(groups, ef.ident.name).is_some())
}

fn build_rewritten_struct_fields(
    old_fields: ThinVec<ExprField>,
    groups: &[FieldGroup],
    def_order: &[Symbol],
) -> ThinVec<ExprField> {
    let mut field_map: FxHashMap<Symbol, ExprField> = old_fields
        .into_iter()
        .map(|ef| (ef.ident.name, ef))
        .collect();
    let skipped: FxHashSet<Symbol> = groups
        .iter()
        .flat_map(|g| g.field_names[1..].iter().copied())
        .collect();

    let mut new_fields = ThinVec::new();
    for field_name in def_order {
        if let Some(group) = groups
            .iter()
            .find(|group| group.field_names.first() == Some(field_name))
        {
            new_fields.push(build_group_expr_field(group, &mut field_map));
        } else if !skipped.contains(field_name)
            && let Some(ef) = field_map.remove(field_name)
        {
            new_fields.push(ef);
        }
    }

    new_fields
}

fn build_group_expr_field(
    group: &FieldGroup,
    field_map: &mut FxHashMap<Symbol, ExprField>,
) -> ExprField {
    let array_exprs: ThinVec<P<Expr>> = group
        .field_names
        .iter()
        .map(|name| {
            field_map
                .remove(name)
                .map(|field| field.expr)
                .expect("partial struct-array literal should be filtered before transform")
        })
        .collect();
    let array_expr = Expr {
        id: DUMMY_NODE_ID,
        kind: ExprKind::Array(array_exprs),
        span: DUMMY_SP,
        attrs: thin_vec![],
        tokens: None,
    };
    ExprField {
        attrs: thin_vec![],
        id: DUMMY_NODE_ID,
        span: DUMMY_SP,
        ident: Ident::new(group.array_name(), DUMMY_SP),
        expr: P(array_expr),
        is_shorthand: false,
        is_placeholder: false,
    }
}

struct StructArraySafetyVisitor<'a, 'tcx> {
    ctx: StructArrayCtx<'a, 'tcx>,
    rejected: FxHashSet<(LocalDefId, usize)>,
}

impl<'a, 'tcx> StructArraySafetyVisitor<'a, 'tcx> {
    fn new(
        candidates: &'a StructRewriteCandidates,
        ast_to_hir: &'a AstToHir,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self {
            ctx: StructArrayCtx::new(candidates, ast_to_hir, tcx),
            rejected: FxHashSet::default(),
        }
    }

    fn reject_offset_of_escape(&mut self, expr: &Expr) {
        let ExprKind::OffsetOf(ref ast_ty, ref fields) = expr.kind else {
            return;
        };
        let Some(struct_did) = self.ctx.offset_of_struct_did(expr, ast_ty) else {
            return;
        };
        let Some(groups) = self.ctx.candidate_groups(struct_did) else {
            return;
        };

        for group in groups {
            if fields
                .iter()
                .any(|field| group.group_index(field.name).is_some())
            {
                self.rejected.insert((struct_did, group.start_idx));
            }
        }
    }

    fn reject_partial_struct_literal(&mut self, expr: &Expr) {
        let ExprKind::Struct(ref se) = expr.kind else {
            return;
        };
        let Some(struct_did) = self.ctx.expr_struct_did(expr.id) else {
            return;
        };
        let Some(groups) = self.ctx.candidate_groups(struct_did) else {
            return;
        };

        let present: FxHashSet<Symbol> = se.fields.iter().map(|field| field.ident.name).collect();
        for group in groups {
            let present_count = group
                .field_names
                .iter()
                .filter(|name| present.contains(name))
                .count();
            if present_count > 0 && present_count < group.count {
                self.rejected.insert((struct_did, group.start_idx));
            }
        }
    }
}

impl MutVisitor for StructArraySafetyVisitor<'_, '_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        self.reject_offset_of_escape(expr);
        self.reject_partial_struct_literal(expr);
        mut_visit::walk_expr(self, expr);
    }
}

fn filter_safe_candidates(
    krate: &mut rustc_ast::ast::Crate,
    candidates: &StructRewriteCandidates,
    tcx: TyCtxt<'_>,
    ast_to_hir: &AstToHir,
) -> StructRewriteCandidates {
    let mut visitor = StructArraySafetyVisitor::new(candidates, ast_to_hir, tcx);
    visitor.visit_crate(krate);

    let mut filtered = FxHashMap::default();
    for (&struct_did, groups) in candidates {
        let groups: Vec<_> = groups
            .iter()
            .filter(|group| !visitor.rejected.contains(&(struct_did, group.start_idx)))
            .cloned()
            .collect();
        if !groups.is_empty() {
            filtered.insert(struct_did, groups);
        }
    }
    filtered
}

pub fn apply_struct_array_transform<'tcx>(
    krate: &mut rustc_ast::ast::Crate,
    candidates: &StructRewriteCandidates,
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &AstToHir,
) -> bool {
    let candidates = filter_safe_candidates(krate, candidates, tcx, ast_to_hir);
    if candidates.is_empty() {
        return false;
    }
    let mut visitor = StructArrayTransformVisitor::new(&candidates, ast_to_hir, tcx);
    visitor.visit_crate(krate);
    true
}
