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

use super::bytemuck::{BytemuckTypeClassifier, FieldTypeClass};

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
    field_classes
        .get(&union_ty)
        .is_some_and(|fields| !fields.is_empty() && fields.iter().all(|field| field.class.is_pod()))
}

#[derive(Debug, Clone)]
struct UnionTransformInfo<'tcx> {
    size: u64,
    align: u64,
    fields: Vec<UnionFieldClassification<'tcx>>,
}

pub struct RawStructVisitor<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a AstToHir,
    union_infos: FxHashMap<LocalDefId, UnionTransformInfo<'tcx>>,
}

impl<'a, 'tcx> RawStructVisitor<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        ast_to_hir: &'a AstToHir,
        union_tys: &[LocalDefId],
        field_classes: FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>>,
    ) -> Self {
        let mut union_infos = FxHashMap::default();
        for &union_ty in union_tys {
            let ty = tcx.type_of(union_ty).instantiate_identity();
            let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, union_ty);
            let layout = tcx.layout_of(typing_env.as_query_input(ty)).unwrap();
            let size = layout.size.bytes();
            let align = layout.align.abi.bytes();
            let fields = field_classes.get(&union_ty).cloned().unwrap_or_default();
            union_infos.insert(
                union_ty,
                UnionTransformInfo {
                    size,
                    align,
                    fields,
                },
            );
        }
        Self {
            tcx,
            ast_to_hir,
            union_infos,
        }
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
            let field_size = self
                .tcx
                .layout_of(
                    rustc_middle::ty::TypingEnv::fully_monomorphized()
                        .as_query_input(field.field_ty),
                )
                .unwrap()
                .size
                .bytes();

            match field.class {
                FieldTypeClass::Pod => methods.push_str(&format!(
                    " pub fn {get}(&self) -> {ty_s} {{ let n = {size_expr}; *bytemuck::from_bytes::<{ty_s}>(&self.raw[..n]) }} \
                      pub fn {get_ref}(&self) -> &{ty_s} {{ let n = {size_expr}; bytemuck::from_bytes::<{ty_s}>(&self.raw[..n]) }} \
                      pub fn {get_mut}(&mut self) -> &mut {ty_s} {{ let n = {size_expr}; bytemuck::from_bytes_mut::<{ty_s}>(&mut self.raw[..n]) }} \
                      pub const fn {set}(&mut self, value: {ty_s}) {{ let bytes: [u8; {field_size}] = bytemuck::must_cast(value); self.raw.split_at_mut({field_size}).0.copy_from_slice(&bytes); }} "
                )),
                FieldTypeClass::AnyBitPattern => methods.push_str(&format!(
                    " pub fn {get}(&self) -> {ty_s} {{ let n = {size_expr}; *bytemuck::from_bytes::<{ty_s}>(&self.raw[..n]) }} \
                      pub fn {get_ref}(&self) -> &{ty_s} {{ let n = {size_expr}; bytemuck::from_bytes::<{ty_s}>(&self.raw[..n]) }} \
                      pub unsafe fn {get_mut}(&mut self) -> &mut {ty_s} {{ &mut *(self.raw.as_mut_ptr() as *mut {ty_s}) }} "
                )),
                FieldTypeClass::NoUninit(is_raw_ptr) => {
                    if is_raw_ptr {
                        let set_body = "let addr = value as usize; let bytes = bytemuck::bytes_of(&addr); self.raw[..bytes.len()].copy_from_slice(bytes);".to_string();
                        methods.push_str(&format!(
                            "pub unsafe fn {get_mut}(&mut self) -> &mut {ty_s} {{ &mut *(self.raw.as_mut_ptr() as *mut {ty_s}) }} \
                            pub fn {set}(&mut self, value: {ty_s}) {{ {set_body} }} "
                        ));

                    } else {
                        let set_body = format!(
                            "let bytes: [u8; {field_size}] = bytemuck::must_cast(value); self.raw.split_at_mut({field_size}).0.copy_from_slice(&bytes);",
                        );
                        methods.push_str(&format!(
                            "pub unsafe fn {get_mut}(&mut self) -> &mut {ty_s} {{ &mut *(self.raw.as_mut_ptr() as *mut {ty_s}) }} \
                            pub const fn {set}(&mut self, value: {ty_s}) {{ {set_body} }} "
                        ));
                    }
                }
                FieldTypeClass::Other => {}
            }
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
            "const fn new() -> Self {{ Self {{ raw: [0u8; {}] }} }}",
            info.size
        ));

        for field in &info.fields {
            if !field.class.is_writable() {
                continue;
            }
            let ty_s = utils::ir::mir_ty_to_string(field.field_ty, self.tcx);
            let new_field = format!("new_{}", field.field_name);
            let set_field = format!("set_{}", field.field_name);

            if let FieldTypeClass::NoUninit(true) = field.class {
                methods.push_str(&format!(
                    " pub fn {new_field}(value: {ty_s}) -> Self {{ let mut u = Self::new(); u.{set_field}(value); u }} "
                ));
            } else {
                methods.push_str(&format!(
                    " pub const fn {new_field}(value: {ty_s}) -> Self {{ let mut u = Self::new(); u.{set_field}(value); u }} "
                ));
            }
        }

        rustc_ast::ptr::P(utils::item!("impl {} {{ {} }}", union_name, methods))
    }
}

impl MutVisitor for RawStructVisitor<'_, '_> {
    fn flat_map_item(
        &mut self,
        item: rustc_ast::ptr::P<Item>,
    ) -> SmallVec<[rustc_ast::ptr::P<Item>; 1]> {
        let union_name = match &item.kind {
            ItemKind::Union(ident, _, _) => ident.name.as_str().to_string(),
            _ => return mut_visit::walk_flat_map_item(self, item),
        };
        let Some(hir_item) = self.ast_to_hir.get_item(item.id, self.tcx) else {
            return mut_visit::walk_flat_map_item(self, item);
        };
        let local_def_id = hir_item.owner_id.def_id;
        let Some(info) = self.union_infos.get(&local_def_id) else {
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

#[derive(Debug, Clone)]
enum Step {
    Field(String),
    Index(String),
    Method(String, Vec<String>, bool),
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

    fn infer_field_access_kind(&self, expr: &Expr, mut_required: bool) -> FieldAccessKind {
        if mut_required {
            return FieldAccessKind::MutRef;
        }
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

    fn tail_needs_mut(&self, tail: &[Step]) -> bool {
        tail.iter()
            .any(|step| matches!(step, Step::Method(_, _, true)))
    }

    fn method_needs_mut(&self, expr: &Expr) -> bool {
        let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx) else {
            return false;
        };
        let owner = hir_expr.hir_id.owner.def_id;
        let typeck = self.tcx.typeck(owner);
        let Some(def_id) = typeck.type_dependent_def_id(hir_expr.hir_id) else {
            return false;
        };

        let sig = self.tcx.fn_sig(def_id).instantiate_identity().skip_binder();
        let Some(receiver_ty) = sig.inputs().first().copied() else {
            return false;
        };

        matches!(receiver_ty.kind(), TyKind::Ref(_, _, mutbl) if mutbl.is_mut())
    }

    /// Return: (base, field, tail)
    /// - base: union struct expression
    /// - field: field projection
    /// - tail: rest of the projections
    fn chain(&self, expr: &Expr) -> Option<(String, String, Vec<Step>)> {
        match &expr.kind {
            ExprKind::Field(base, field_ident) => {
                if self.is_target_union_expr(base) {
                    Some((
                        pprust::expr_to_string(base),
                        field_ident.name.as_str().to_string(),
                        Vec::new(),
                    ))
                } else {
                    let (base_s, field_name, mut tail) = self.chain(base)?;
                    tail.push(Step::Field(field_ident.name.as_str().to_string()));
                    Some((base_s, field_name, tail))
                }
            }
            ExprKind::Index(base, index, _) => {
                let (base_s, field_name, mut tail) = self.chain(base)?;
                tail.push(Step::Index(pprust::expr_to_string(index)));
                Some((base_s, field_name, tail))
            }
            ExprKind::MethodCall(call) => {
                let (base_s, field_name, mut tail) = self.chain(&call.receiver)?;
                let args = call
                    .args
                    .iter()
                    .map(|arg| pprust::expr_to_string(arg))
                    .collect();
                let receiver_mut =
                    self.infer_field_access_kind(&call.receiver, false) == FieldAccessKind::MutRef;
                tail.push(Step::Method(
                    call.seg.ident.name.as_str().to_string(),
                    args,
                    receiver_mut,
                ));
                Some((base_s, field_name, tail))
            }
            ExprKind::Paren(inner) => self.chain(inner),
            _ => None,
        }
    }

    /// Tail to string
    fn tail(&self, tail: &[Step]) -> String {
        let mut s = String::new();
        for step in tail {
            match step {
                Step::Field(name) => {
                    s.push('.');
                    s.push_str(name);
                }
                Step::Index(index) => {
                    s.push('[');
                    s.push_str(index);
                    s.push(']');
                }
                Step::Method(name, args, _) => {
                    s.push('.');
                    s.push_str(name);
                    s.push('(');
                    s.push_str(&args.join(", "));
                    s.push(')');
                }
            }
        }
        s
    }

    fn access(&self, base: &str, field: &str, kind: FieldAccessKind, tail: &[Step]) -> String {
        let head = match kind {
            FieldAccessKind::Value => format!("{base}.get_{field}()"),
            FieldAccessKind::Ref => format!("{base}.get_{field}_ref()"),
            FieldAccessKind::MutRef => format!("{base}.get_{field}_mut()"),
        };
        format!("{}{}", head, self.tail(tail))
    }
}

impl MutVisitor for UnionUseRewriteVisitor<'_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        let target_union = if matches!(expr.kind, ExprKind::Struct(_)) {
            self.target_union_ty_string(expr)
        } else {
            None
        };
        let field_access_kind = if matches!(expr.kind, ExprKind::Field(_, _)) {
            Some(self.infer_field_access_kind(expr, false))
        } else {
            None
        };
        let method_needs_mut = if matches!(expr.kind, ExprKind::MethodCall(_)) {
            self.method_needs_mut(expr)
        } else {
            false
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
                if let Some(union_ty_s) = target_union
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
            ExprKind::Field(base, field_ident) => {
                let target_union = if matches!(base.kind, ExprKind::Struct(_)) {
                    self.target_union_ty_string(base)
                } else {
                    None
                };

                if let Some(union_ty_s) = target_union
                    && let ExprKind::Struct(se) = &mut base.kind
                {
                    for field in &mut se.fields {
                        self.visit_expr(&mut field.expr);
                    }
                    if let rustc_ast::StructRest::Base(rest) = &mut se.rest {
                        self.visit_expr(rest);
                    }

                    if se.fields.len() == 1 && matches!(se.rest, rustc_ast::StructRest::None) {
                        let init = &se.fields[0];
                        let init_name = init.ident.name;
                        let value_s = pprust::expr_to_string(&init.expr);
                        let new_s = format!("{union_ty_s}::new_{init_name}({value_s})");
                        let access_s = match field_access_kind.unwrap() {
                            FieldAccessKind::Value => {
                                format!("{new_s}.get_{}()", field_ident.name)
                            }
                            FieldAccessKind::Ref => {
                                format!("{new_s}.get_{}_ref()", field_ident.name)
                            }
                            FieldAccessKind::MutRef => {
                                format!("{new_s}.get_{}_mut()", field_ident.name)
                            }
                        };
                        *expr = utils::expr!("{}", access_s);
                        return;
                    }
                }

                mut_visit::walk_expr(self, expr);
            }
            ExprKind::AddrOf(borrow_kind, mutability, inner) => {
                // &u.f or &mut u.f -> u.get_f_ref() or u.get_f_mut()
                if matches!(borrow_kind, rustc_ast::BorrowKind::Ref)
                    && let Some((base_s, field_name, tail)) = self.chain(inner)
                {
                    let access_s = if matches!(mutability, rustc_ast::Mutability::Mut) {
                        self.access(&base_s, &field_name, FieldAccessKind::MutRef, &tail)
                    } else {
                        self.access(&base_s, &field_name, FieldAccessKind::Ref, &tail)
                    };
                    if tail.is_empty() {
                        *expr = utils::expr!("{}", access_s);
                    } else if matches!(mutability, rustc_ast::Mutability::Mut) {
                        *expr = utils::expr!("&mut {}", access_s);
                    } else {
                        *expr = utils::expr!("&{}", access_s);
                    }
                    return;
                }

                self.visit_expr(inner);
                return;
            }
            ExprKind::MethodCall(call) => {
                for arg in &mut call.args {
                    self.visit_expr(arg);
                }
                if let Some((base_s, field_name, tail)) = self.chain(&call.receiver) {
                    let kind = self.infer_field_access_kind(
                        &call.receiver,
                        method_needs_mut || self.tail_needs_mut(&tail),
                    );
                    let access_s = self.access(&base_s, &field_name, kind, &tail);
                    call.receiver = Box::new(utils::expr!("{}", access_s));
                } else {
                    self.visit_expr(&mut call.receiver);
                }
                return;
            }
            ExprKind::Assign(lhs, rhs, _) => {
                self.visit_expr(rhs);
                self.assign_lhs_depth += 1;
                self.visit_expr(lhs);
                self.assign_lhs_depth -= 1;

                if let Some((base_s, field_name, tail)) = self.chain(lhs) {
                    let rhs_s = pprust::expr_to_string(rhs);
                    // u.f = v -> u.set_f(v)
                    if tail.is_empty() {
                        *expr = utils::expr!("{}.set_{}({})", base_s, field_name, rhs_s);
                    } else {
                        // u.f.g = v or u.f[i] = v -> u.get_f_mut().g = v or u.get_f_mut()[i] = v
                        let lhs_s =
                            self.access(&base_s, &field_name, FieldAccessKind::MutRef, &tail);
                        *expr = utils::expr!("{} = {}", lhs_s, rhs_s);
                    }
                    return;
                }
                return;
            }
            ExprKind::AssignOp(op, lhs, rhs) => {
                self.visit_expr(rhs);
                self.assign_lhs_depth += 1;
                self.visit_expr(lhs);
                self.assign_lhs_depth -= 1;

                if let Some((base_s, field_name, tail)) = self.chain(lhs) {
                    let rhs_s = pprust::expr_to_string(rhs);
                    let lhs_s = self.access(&base_s, &field_name, FieldAccessKind::MutRef, &tail);
                    if tail.is_empty() {
                        *expr = utils::expr!("*{} {} {}", lhs_s, op.node.as_str(), rhs_s);
                    } else {
                        *expr = utils::expr!("{} {} {}", lhs_s, op.node.as_str(), rhs_s);
                    }
                    return;
                }
                return;
            }
            _ => mut_visit::walk_expr(self, expr),
        }

        if self.assign_lhs_depth > 0 {
            return;
        }

        if let Some((base_s, field_name, tail)) = self.chain(expr) {
            let access_s = self.access(
                &base_s,
                &field_name,
                self.infer_field_access_kind(expr, method_needs_mut || self.tail_needs_mut(&tail)),
                &tail,
            );
            *expr = utils::expr!("{}", access_s);
        }
    }
}
