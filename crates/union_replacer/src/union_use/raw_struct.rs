use rustc_ast::{Expr, ExprKind, Item, ItemKind, mut_visit, mut_visit::MutVisitor};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::{Ty, TyCtxt, TypingMode};
use rustc_span::{
    Symbol,
    def_id::{DefId, LocalDefId},
};
use rustc_trait_selection::infer::{InferCtxtExt as _, TyCtxtInferExt as _};
use smallvec::{SmallVec, smallvec};
use utils::ir::AstToHir;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldTypeClass {
    AnyBitPattern,
    NoUninit,
    Pod,
    Other,
}

#[derive(Debug, Clone)]
pub struct UnionFieldClassification<'tcx> {
    pub field_name: String,
    pub field_ty: Ty<'tcx>,
    pub class: FieldTypeClass,
}

#[derive(Debug, Clone, Copy, Default)]
struct BytemuckTraitIds {
    any_bit_pattern: Option<DefId>,
    no_uninit: Option<DefId>,
    pod: Option<DefId>,
}

pub fn has_bytemuck_traits(tcx: TyCtxt<'_>) -> bool {
    let trait_ids = resolve_bytemuck_trait_ids(tcx);
    trait_ids.pod.is_some() || trait_ids.any_bit_pattern.is_some() || trait_ids.no_uninit.is_some()
}

/// Classify each local union field type into one of:
/// `AnyBitPattern` / `NoUninit` / `Pod` / `Other`.
pub fn classify_union_field_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_tys: &[LocalDefId],
    verbose: bool,
) -> FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>> {
    let trait_ids = resolve_bytemuck_trait_ids(tcx);
    if verbose {
        println!(
            "\nBytemuck trait ids: Pod={:?}, AnyBitPattern={:?}, NoUninit={:?}",
            trait_ids.pod, trait_ids.any_bit_pattern, trait_ids.no_uninit
        );
    }
    let mut class_cache: FxHashMap<Ty<'tcx>, FieldTypeClass> = FxHashMap::default();
    let mut results: FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>> =
        FxHashMap::default();

    for &union_ty in union_tys {
        let union_adt = tcx.adt_def(union_ty.to_def_id());
        if !union_adt.is_union() {
            continue;
        }

        let union_ty_value = tcx.type_of(union_ty).instantiate_identity();
        let mut fields = Vec::new();
        if let rustc_middle::ty::TyKind::Adt(_, args) = union_ty_value.kind() {
            for field in union_adt.all_fields() {
                let field_ty = field.ty(tcx, args);
                let class = *class_cache
                    .entry(field_ty)
                    .or_insert_with(|| classify_field_type(tcx, union_ty, field_ty, trait_ids));
                fields.push(UnionFieldClassification {
                    field_name: field.ident(tcx).name.to_ident_string(),
                    field_ty,
                    class,
                });
            }
        }
        results.insert(union_ty, fields);
    }

    if verbose {
        println!("\nUnion Field Type Classification:");
        let mut unions = results.keys().copied().collect::<Vec<_>>();
        unions.sort_by_key(|def_id| tcx.def_path_str(*def_id));
        for union_ty in unions {
            println!("\t{}:", tcx.def_path_str(union_ty));
            for field in &results[&union_ty] {
                println!(
                    "\t\t{}: {:?} -> {:?}",
                    field.field_name, field.field_ty, field.class
                );
            }
        }
    }

    results
}

fn classify_field_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    ty: Ty<'tcx>,
    trait_ids: BytemuckTraitIds,
) -> FieldTypeClass {
    if trait_ids
        .pod
        .is_some_and(|did| ty_implements_trait(tcx, owner, ty, did))
    {
        return FieldTypeClass::Pod;
    }
    if trait_ids
        .any_bit_pattern
        .is_some_and(|did| ty_implements_trait(tcx, owner, ty, did))
    {
        return FieldTypeClass::AnyBitPattern;
    }
    if trait_ids
        .no_uninit
        .is_some_and(|did| ty_implements_trait(tcx, owner, ty, did))
    {
        return FieldTypeClass::NoUninit;
    }
    FieldTypeClass::Other
}

fn ty_implements_trait<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    ty: Ty<'tcx>,
    trait_def_id: DefId,
) -> bool {
    let param_env = tcx.param_env(owner);
    let infcx = tcx.infer_ctxt().build(TypingMode::non_body_analysis());
    infcx
        .type_implements_trait(trait_def_id, [ty], param_env)
        .must_apply_modulo_regions()
}

fn resolve_bytemuck_trait_ids(tcx: TyCtxt<'_>) -> BytemuckTraitIds {
    let mut trait_ids = BytemuckTraitIds::default();
    for did in tcx.all_traits() {
        if tcx.crate_name(did.krate).as_str() != "bytemuck" {
            continue;
        }
        match tcx.item_name(did).as_str() {
            "Pod" if trait_ids.pod.is_none() => trait_ids.pod = Some(did),
            "AnyBitPattern" if trait_ids.any_bit_pattern.is_none() => {
                trait_ids.any_bit_pattern = Some(did);
            }
            "NoUninit" if trait_ids.no_uninit.is_none() => {
                trait_ids.no_uninit = Some(did);
            }
            _ => {}
        }
    }
    trait_ids
}

pub struct RawStructVisitor<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    union_infos: FxHashMap<String, UnionTransformInfo<'tcx>>,
}

pub struct UnionUseRewriteVisitor<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    target_unions: FxHashSet<LocalDefId>,
    assign_lhs_depth: usize,
}

#[derive(Debug, Clone)]
struct UnionTransformInfo<'tcx> {
    raw_name: String,
    size: u64,
    fields: Vec<UnionFieldClassification<'tcx>>,
}

impl<'tcx> RawStructVisitor<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        union_tys: &[LocalDefId],
        field_classes: FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>>,
    ) -> Self {
        let mut union_infos = FxHashMap::default();
        for &union_ty in union_tys {
            let name = tcx.item_name(union_ty.to_def_id()).as_str().to_string();
            let raw_name = format!("{name}Raw");
            let ty = tcx.type_of(union_ty).instantiate_identity();
            let size = utils::ir::ty_size(ty, union_ty.to_def_id(), tcx);
            let fields = field_classes.get(&union_ty).cloned().unwrap_or_default();
            union_infos.insert(
                name,
                UnionTransformInfo {
                    raw_name,
                    size,
                    fields,
                },
            );
        }
        Self { tcx, union_infos }
    }

    fn make_access_impl_item(
        &self,
        union_name: &str,
        info: &UnionTransformInfo<'tcx>,
    ) -> rustc_ast::ptr::P<Item> {
        let mut methods = String::new();

        for field in &info.fields {
            let ty_s = utils::ir::mir_ty_to_string(field.field_ty, self.tcx);
            let get = format!("get_{}", field.field_name);
            let get_ref = format!("get_{}_ref", field.field_name);
            let get_mut = format!("get_{}_mut", field.field_name);
            let set = format!("set_{}", field.field_name);
            let size_expr = format!("core::mem::size_of::<{ty_s}>()");

            let (get_body, get_ref_body, get_mut_body, set_body) = match field.class {
                FieldTypeClass::Pod => (
                    format!(
                        "{{ let n = {size_expr}; *bytemuck::from_bytes::<{ty_s}>(&self.raw[..n]) }}"
                    ),
                    format!(
                        "{{ let n = {size_expr}; bytemuck::from_bytes::<{ty_s}>(&self.raw[..n]) }}"
                    ),
                    format!(
                        "{{ let n = {size_expr}; bytemuck::from_bytes_mut::<{ty_s}>(&mut self.raw[..n]) }}"
                    ),
                    "{ let bytes = bytemuck::bytes_of(&value); self.raw[..bytes.len()].copy_from_slice(bytes); }".to_string()
                ),
                FieldTypeClass::AnyBitPattern => (
                    format!(
                        "{{ let n = {size_expr}; *bytemuck::from_bytes::<{ty_s}>(&self.raw[..n]) }}"
                    ),
                    format!("{{ unsafe {{ &*(self.raw.as_ptr() as *const {ty_s}) }} }}"),
                    format!("{{ unsafe {{ &mut *(self.raw.as_mut_ptr() as *mut {ty_s}) }} }}"),
                    format!(
                        "{{ unsafe {{ core::ptr::write(self.raw.as_mut_ptr() as *mut {ty_s}, value); }} }}"
                    ),
                ),
                FieldTypeClass::NoUninit => (
                    format!(
                        "{{ unsafe {{ core::ptr::read(self.raw.as_ptr() as *const {ty_s}) }} }}"
                    ),
                    format!("{{ unsafe {{ &*(self.raw.as_ptr() as *const {ty_s}) }} }}"),
                    format!("{{ unsafe {{ &mut *(self.raw.as_mut_ptr() as *mut {ty_s}) }} }}"),
                    "{ let bytes = bytemuck::bytes_of(&value); self.raw[..bytes.len()].copy_from_slice(bytes); }".to_string()
                ),
                FieldTypeClass::Other => (
                    format!(
                        "{{ unsafe {{ core::ptr::read(self.raw.as_ptr() as *const {ty_s}) }} }}"
                    ),
                    format!("{{ unsafe {{ &*(self.raw.as_ptr() as *const {ty_s}) }} }}"),
                    format!("{{ unsafe {{ &mut *(self.raw.as_mut_ptr() as *mut {ty_s}) }} }}"),
                    format!(
                        "{{ unsafe {{ core::ptr::write(self.raw.as_mut_ptr() as *mut {ty_s}, value); }} }}"
                    ),
                ),
            };

            methods.push_str(&format!(
                " fn {get}(&self) -> {ty_s} {get_body} \
                  fn {get_ref}(&self) -> &{ty_s} {get_ref_body} \
                  fn {get_mut}(&mut self) -> &mut {ty_s} {get_mut_body} \
                  fn {set}(&mut self, value: {ty_s}) {set_body} "
            ));
        }

        rustc_ast::ptr::P(utils::item!("impl {} {{ {} }}", union_name, methods))
    }

    fn make_ctor_impl_item(
        &self,
        union_name: &str,
        info: &UnionTransformInfo<'tcx>,
    ) -> rustc_ast::ptr::P<Item> {
        let mut methods = String::new();
        methods.push_str(&format!(
            "fn new() -> Self {{ Self {{ raw: [0u8; {}], _align: [] }} }}",
            info.size
        ));

        for field in &info.fields {
            let ty_s = utils::ir::mir_ty_to_string(field.field_ty, self.tcx);
            let new_field = format!("new_{}", field.field_name);
            let set_field = format!("set_{}", field.field_name);
            methods.push_str(&format!(
                " fn {new_field}(value: {ty_s}) -> Self {{ let mut u = Self::new(); u.{set_field}(value); u }} "
            ));
        }

        rustc_ast::ptr::P(utils::item!("impl {} {{ {} }}", union_name, methods))
    }
}

impl<'tcx> UnionUseRewriteVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, ast_to_hir: AstToHir, target_unions: &[LocalDefId]) -> Self {
        let target_unions = target_unions.iter().copied().collect();
        Self {
            tcx,
            ast_to_hir,
            target_unions,
            assign_lhs_depth: 0,
        }
    }

    fn is_target_union_expr(&self, expr: &Expr) -> bool {
        self.target_union_ty_string(expr).is_some()
    }

    fn target_union_ty_string(&self, expr: &Expr) -> Option<String> {
        let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx)?;
        let owner = hir_expr.hir_id.owner.def_id;
        let typeck = self.tcx.typeck(owner);
        let ty = typeck.expr_ty_adjusted(hir_expr);
        let rustc_middle::ty::TyKind::Adt(adt, _) = ty.kind() else {
            return None;
        };
        let local = adt.did().as_local()?;
        if !adt.is_union() || !self.target_unions.contains(&local) {
            return None;
        }
        Some(utils::ir::mir_ty_to_string(ty, self.tcx))
    }
}

impl MutVisitor for RawStructVisitor<'_> {
    fn flat_map_item(
        &mut self,
        mut item: rustc_ast::ptr::P<Item>,
    ) -> SmallVec<[rustc_ast::ptr::P<Item>; 1]> {
        let union_name = match &item.kind {
            ItemKind::Union(ident, _, _) => ident.name.as_str().to_string(),
            _ => return mut_visit::walk_flat_map_item(self, item),
        };
        let Some(info) = self.union_infos.get(&union_name) else {
            return mut_visit::walk_flat_map_item(self, item);
        };

        if let ItemKind::Union(ident, _, _) = &mut item.kind {
            ident.name = Symbol::intern(&info.raw_name);
        }

        let mut struct_item = rustc_ast::ptr::P(utils::item!(
            "#[repr(C)] struct {} {{ raw: [u8; {}], _align: [{}; 0] }}",
            union_name,
            info.size,
            info.raw_name
        ));
        struct_item.vis = item.vis.clone();
        let access_impl_item = self.make_access_impl_item(&union_name, info);
        let ctor_impl_item = self.make_ctor_impl_item(&union_name, info);

        smallvec![item, struct_item, access_impl_item, ctor_impl_item]
    }
}

impl MutVisitor for UnionUseRewriteVisitor<'_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        if matches!(expr.kind, ExprKind::Struct(_)) {
            let target_union_ty_s = self.target_union_ty_string(expr);
            let ExprKind::Struct(se) = &mut expr.kind else {
                unreachable!();
            };
            for field in &mut se.fields {
                self.visit_expr(&mut field.expr);
            }
            if let rustc_ast::StructRest::Base(base) = &mut se.rest {
                self.visit_expr(base);
            }

            if let Some(union_ty_s) = target_union_ty_s
                && se.fields.len() == 1
                && matches!(se.rest, rustc_ast::StructRest::None)
            {
                let field = &se.fields[0];
                let field_name = field.ident.name;
                let value_s = pprust::expr_to_string(&field.expr);
                *expr = utils::expr!("{}::new_{}({})", union_ty_s, field_name, value_s);
            }
            return;
        }

        if let ExprKind::AddrOf(_, mutability, inner) = &mut expr.kind
            && matches!(mutability, rustc_ast::Mutability::Mut)
            && let ExprKind::Field(base, field_ident) = &inner.kind
            && self.is_target_union_expr(base)
        {
            let base_s = pprust::expr_to_string(base);
            *expr = utils::expr!("{}.get_{}_mut()", base_s, field_ident.name);
            return;
        }

        if let ExprKind::AddrOf(_, mutability, inner) = &mut expr.kind
            && matches!(mutability, rustc_ast::Mutability::Not)
            && let ExprKind::Field(base, field_ident) = &inner.kind
            && self.is_target_union_expr(base)
        {
            let base_s = pprust::expr_to_string(base);
            *expr = utils::expr!("{}.get_{}_ref()", base_s, field_ident.name);
            return;
        }

        if let ExprKind::MethodCall(call) = &mut expr.kind
            && call.seg.ident.name.as_str() == "as_mut_ptr"
            && let ExprKind::Field(base, field_ident) = &call.receiver.kind
            && self.is_target_union_expr(base)
        {
            let base_s = pprust::expr_to_string(base);
            *expr = utils::expr!("{}.get_{}_mut().as_mut_ptr()", base_s, field_ident.name);
            return;
        }

        if let ExprKind::MethodCall(call) = &mut expr.kind
            && call.seg.ident.name.as_str() == "as_ptr"
            && let ExprKind::Field(base, field_ident) = &call.receiver.kind
            && self.is_target_union_expr(base)
        {
            let base_s = pprust::expr_to_string(base);
            *expr = utils::expr!("{}.get_{}_ref().as_ptr()", base_s, field_ident.name);
            return;
        }

        if let ExprKind::Assign(lhs, rhs, _) = &mut expr.kind {
            self.visit_expr(rhs);
            self.assign_lhs_depth += 1;
            self.visit_expr(lhs);
            self.assign_lhs_depth -= 1;

            if let ExprKind::Field(base, field_ident) = &lhs.kind
                && self.is_target_union_expr(base)
            {
                let base_s = pprust::expr_to_string(base);
                let rhs_s = pprust::expr_to_string(rhs);
                *expr = utils::expr!("{}.set_{}({})", base_s, field_ident.name, rhs_s);
                return;
            }

            if let ExprKind::Index(lhs_base, index, _) = &lhs.kind
                && let ExprKind::Field(base, field_ident) = &lhs_base.kind
                && self.is_target_union_expr(base)
            {
                let base_s = pprust::expr_to_string(base);
                let idx_s = pprust::expr_to_string(index);
                let rhs_s = pprust::expr_to_string(rhs);
                *expr = utils::expr!(
                    "{}.get_{}_mut()[{}] = {}",
                    base_s,
                    field_ident.name,
                    idx_s,
                    rhs_s
                );
            }
            return;
        }

        mut_visit::walk_expr(self, expr);

        if self.assign_lhs_depth > 0 {
            return;
        }

        if let ExprKind::Field(base, field_ident) = &expr.kind
            && self.is_target_union_expr(base)
        {
            let base_s = pprust::expr_to_string(base);
            *expr = utils::expr!("{}.get_{}()", base_s, field_ident.name);
        }
    }
}
