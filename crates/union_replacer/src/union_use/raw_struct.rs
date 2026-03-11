use rustc_ast::{Expr, ExprKind, Item, ItemKind, mut_visit, mut_visit::MutVisitor};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::{
    Ty, TyCtxt, TyKind,
    adjustment::{Adjust, AutoBorrow, AutoBorrowMutability},
};
use rustc_span::def_id::LocalDefId;
use smallvec::{SmallVec, smallvec};
use utils::ir::AstToHir;

use super::check::{BytemuckTypeClassifier, FieldTypeClass};

#[derive(Debug, Clone)]
pub struct UnionFieldClassification<'tcx> {
    pub field_name: String,
    pub field_ty: Ty<'tcx>,
    pub class: FieldTypeClass,
}

/// Classify each local union field type into one of:
/// `AnyBitPattern` / `NoUninit` / `Pod` / `Other`.
pub fn classify_union_field_types<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_tys: &[LocalDefId],
    verbose: bool,
) -> FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>> {
    let mut classifier = BytemuckTypeClassifier::new(tcx);
    if verbose {
        println!("\nUnion field classification uses the local bytemuck rule reimplementation.");
    }
    let mut results: FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>> =
        FxHashMap::default();

    for &union_ty in union_tys {
        let union_adt = tcx.adt_def(union_ty.to_def_id());
        // if !union_adt.is_union() {
        //     unreachable!();
        // }

        let union_ty_value = tcx.type_of(union_ty).instantiate_identity();
        let mut fields = Vec::new();
        if let TyKind::Adt(_, args) = union_ty_value.kind() {
            for field in union_adt.all_fields() {
                let field_ty = field.ty(tcx, args);
                let class = classifier.classify_type(union_ty, field_ty);
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
        for &union_ty in results.keys() {
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

pub fn all_union_fields_are_pod<'tcx>(
    field_classes: &FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>>,
    union_ty: LocalDefId,
) -> bool {
    field_classes.get(&union_ty).is_some_and(|fields| {
        !fields.is_empty()
            && fields
                .iter()
                .all(|field| field.class == FieldTypeClass::Pod)
    })
}

#[derive(Debug, Clone)]
struct UnionTransformInfo<'tcx> {
    size: u64,
    align: u64,
    fields: Vec<UnionFieldClassification<'tcx>>,
}

pub struct RawStructVisitor<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    union_infos: FxHashMap<String, UnionTransformInfo<'tcx>>,
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
            let ty = tcx.type_of(union_ty).instantiate_identity();
            let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, union_ty);
            let layout = tcx.layout_of(typing_env.as_query_input(ty)).unwrap();
            let size = layout.size.bytes();
            let align = layout.align.abi.bytes();
            let fields = field_classes.get(&union_ty).cloned().unwrap_or_default();
            union_infos.insert(
                name,
                UnionTransformInfo {
                    size,
                    align,
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

    fn make_init_impl_item(
        &self,
        union_name: &str,
        info: &UnionTransformInfo<'tcx>,
    ) -> rustc_ast::ptr::P<Item> {
        let mut methods = String::new();
        methods.push_str(&format!(
            "fn new() -> Self {{ Self {{ raw: [0u8; {}] }} }}",
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

impl MutVisitor for RawStructVisitor<'_> {
    fn flat_map_item(
        &mut self,
        item: rustc_ast::ptr::P<Item>,
    ) -> SmallVec<[rustc_ast::ptr::P<Item>; 1]> {
        let union_name = match &item.kind {
            ItemKind::Union(ident, _, _) => ident.name.as_str().to_string(),
            _ => return mut_visit::walk_flat_map_item(self, item),
        };
        let Some(info) = self.union_infos.get(&union_name) else {
            return mut_visit::walk_flat_map_item(self, item);
        };

        let mut struct_item = rustc_ast::ptr::P(utils::item!(
            "#[repr(C, align({}))] struct {} {{ raw: [u8; {}] }}",
            info.align,
            union_name,
            info.size
        ));
        struct_item.vis = item.vis.clone();
        let access_impl_item = self.make_access_impl_item(&union_name, info);
        let init_impl_item = self.make_init_impl_item(&union_name, info);

        smallvec![struct_item, access_impl_item, init_impl_item]
    }
}

pub struct UnionUseRewriteVisitor<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    target_unions: FxHashSet<LocalDefId>,
    assign_lhs_depth: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FieldAccessKind {
    Value,
    Ref,
    MutRef,
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

    fn infer_field_access_kind(&self, expr: &Expr) -> FieldAccessKind {
        let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx) else {
            return FieldAccessKind::Value;
        };
        let owner = hir_expr.hir_id.owner.def_id;
        let typeck = self.tcx.typeck(owner);
        for adjustment in typeck.expr_adjustments(hir_expr).iter().rev() {
            if let Adjust::Borrow(auto_borrow) = &adjustment.kind {
                match auto_borrow {
                    AutoBorrow::Ref(AutoBorrowMutability::Mut { .. }) => {
                        return FieldAccessKind::MutRef;
                    }
                    AutoBorrow::Ref(AutoBorrowMutability::Not) => return FieldAccessKind::Ref,
                    AutoBorrow::RawPtr(_) => {
                        todo!("RawPtr auto borrow does not appear in the benchmarks")
                    }
                }
            }
        }
        FieldAccessKind::Value
    }
}

impl MutVisitor for UnionUseRewriteVisitor<'_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        let struct_target_union_ty_s = if matches!(expr.kind, ExprKind::Struct(_)) {
            self.target_union_ty_string(expr)
        } else {
            None
        };

        match &mut expr.kind {
            ExprKind::Struct(se) => {
                for field in &mut se.fields {
                    self.visit_expr(&mut field.expr);
                }
                if let rustc_ast::StructRest::Base(base) = &mut se.rest {
                    self.visit_expr(base);
                }

                // U { f: v } -> U::new_f(v)
                if let Some(union_ty_s) = struct_target_union_ty_s
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
            ExprKind::AddrOf(borrow_kind, mutability, inner) => {
                if matches!(borrow_kind, rustc_ast::BorrowKind::Ref)
                    && matches!(mutability, rustc_ast::Mutability::Mut)
                    && let ExprKind::Field(base, field_ident) = &mut inner.kind
                {
                    self.visit_expr(base);
                    if self.is_target_union_expr(base) {
                        let base_s = pprust::expr_to_string(base);
                        *expr = utils::expr!("{}.get_{}_mut()", base_s, field_ident.name);
                        return;
                    }
                }

                if matches!(borrow_kind, rustc_ast::BorrowKind::Ref)
                    && matches!(mutability, rustc_ast::Mutability::Not)
                    && let ExprKind::Field(base, field_ident) = &mut inner.kind
                {
                    self.visit_expr(base);
                    if self.is_target_union_expr(base) {
                        let base_s = pprust::expr_to_string(base);
                        *expr = utils::expr!("{}.get_{}_ref()", base_s, field_ident.name);
                        return;
                    }
                }

                mut_visit::walk_expr(self, expr);
                return;
            }
            ExprKind::Assign(lhs, rhs, _) => {
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
            ExprKind::AssignOp(op, lhs, rhs) => {
                self.visit_expr(rhs);
                self.assign_lhs_depth += 1;
                self.visit_expr(lhs);
                self.assign_lhs_depth -= 1;

                if let ExprKind::Field(base, field_ident) = &lhs.kind
                    && self.is_target_union_expr(base)
                {
                    let base_s = pprust::expr_to_string(base);
                    let rhs_s = pprust::expr_to_string(rhs);
                    *expr = utils::expr!(
                        "*{}.get_{}_mut() {} {}",
                        base_s,
                        field_ident.name,
                        op.node.as_str(),
                        rhs_s
                    );
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
                        "{}.get_{}_mut()[{}] {} {}",
                        base_s,
                        field_ident.name,
                        idx_s,
                        op.node.as_str(),
                        rhs_s
                    );
                    return;
                }

                return;
            }
            _ => mut_visit::walk_expr(self, expr),
        }

        if self.assign_lhs_depth > 0 {
            return;
        }

        if let ExprKind::Field(base, field_ident) = &expr.kind
            && self.is_target_union_expr(base)
        {
            let base_s = pprust::expr_to_string(base);
            match self.infer_field_access_kind(expr) {
                FieldAccessKind::Value => {
                    *expr = utils::expr!("{}.get_{}()", base_s, field_ident.name);
                }
                FieldAccessKind::Ref => {
                    *expr = utils::expr!("{}.get_{}_ref()", base_s, field_ident.name);
                }
                FieldAccessKind::MutRef => {
                    *expr = utils::expr!("{}.get_{}_mut()", base_s, field_ident.name);
                }
            }
        }
    }
}
