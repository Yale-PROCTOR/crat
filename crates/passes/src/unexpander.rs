use std::ops::ControlFlow;

use etrace::some_or;
use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor},
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, QPath,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit,
    intravisit::Visitor as _,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, TyCtxt},
};
use rustc_span::{DUMMY_SP, Symbol, kw, sym};
use serde::Deserialize;
use smallvec::{SmallVec, smallvec};
use thin_vec::{ThinVec, thin_vec};
use utils::{
    ast::{unwrap_paren, unwrap_paren_mut},
    attr, expr, item,
};

#[derive(Debug, Default, Clone, Copy, Deserialize)]
pub struct Config {
    pub use_print: bool,
}

pub fn unexpand(config: Config, tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let mut pre_visitor = Previsitor {
        tcx,
        ast_to_hir,
        ctx: Ctx::default(),
    };
    pre_visitor.visit_crate(&krate);

    let mut visitor = AstVisitor {
        tcx,
        ast_to_hir: pre_visitor.ast_to_hir,
        ctx: pre_visitor.ctx,
        config,
    };
    visitor.visit_crate(&mut krate);
    FeatureUses {
        tcx,
        ast_to_hir: &visitor.ast_to_hir,
        required: &mut visitor.ctx.required_features,
    }
    .visit_crate(&krate);

    let mut unnecessary_attributes: FxHashSet<_> = [
        "derive_clone_copy",
        "hint_must_use",
        "panic_internals",
        "coverage_attribute",
        "builtin_syntax",
        "rt",
        "libstd_sys_internals",
        "structural_match",
    ]
    .into_iter()
    .collect();
    for feature in [
        "never_type",
        "thread_local_internals",
        "fmt_helpers_for_derive",
        "derive_eq",
    ] {
        if !visitor
            .ctx
            .required_features
            .contains(&Symbol::intern(feature))
        {
            unnecessary_attributes.insert(feature);
        }
    }
    if !visitor.ctx.use_intrinsics {
        unnecessary_attributes.insert("core_intrinsics");
    }
    unnecessary_attributes.insert("rt");
    unnecessary_attributes.insert("libstd_sys_internals");

    let mut attributes = thin_vec![];
    for attribute in std::mem::take(&mut krate.attrs) {
        if attribute.has_name(sym::feature) {
            for feature in attribute.meta_item_list().unwrap() {
                let feature = feature.ident().unwrap().name;
                if !unnecessary_attributes.contains(feature.as_str()) {
                    attributes.push(utils::ast::make_inner_attribute(sym::feature, feature, tcx));
                }
            }
            continue;
        }
        if !visitor.ctx.use_transmute
            && let AttrKind::Normal(attr) = &attribute.kind
            && attr.item.path.segments.last().unwrap().ident.name == sym::warn
            && let Some(arg) = utils::ast::get_attr_arg(&attr.item.args)
            && arg.as_str() == "mutable_transmutes"
        {
            continue;
        }
        attributes.push(attribute);
    }
    krate.attrs = attributes;

    pprust::crate_to_string_for_macros(&krate)
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: utils::ir::AstToHir,
    ctx: Ctx,
    config: Config,
}

impl MutVisitor for AstVisitor<'_> {
    fn flat_map_item(&mut self, item: P<Item>) -> SmallVec<[P<Item>; 1]> {
        if utils::ast::is_automatically_derived(&item.attrs) {
            return smallvec![];
        }
        if let ItemKind::Impl(imp) = &item.kind
            && let Some(of_trait) = &imp.of_trait
            && of_trait
                .path
                .segments
                .iter()
                .any(|s| s.ident.name.as_str() == "bytemuck")
        {
            return smallvec![];
        }
        if let ItemKind::Const(const_item) = &item.kind
            && const_item.ident.name == kw::Underscore
            && !self.ctx.bytemuck_traits.is_empty()
        {
            return smallvec![];
        }
        mut_visit::walk_flat_map_item(self, item)
    }

    fn visit_item(&mut self, item: &mut Item) {
        if let Some(replacement) = self.unexpanded_thread_local(item) {
            *item = replacement;
            return;
        }
        if matches!(
            item.kind,
            ItemKind::Struct(..) | ItemKind::Union(..) | ItemKind::Enum(..)
        ) {
            let local_def_id = self.ast_to_hir.global_map.get(&item.id).unwrap();
            if let Some(traits) = self.ctx.derived_traits.get(local_def_id) {
                for t in traits {
                    if *t == sym::StructuralPartialEq {
                        continue;
                    }
                    let attr = utils::ast::make_outer_attribute(sym::derive, *t, self.tcx);
                    item.attrs.push(attr);
                }
            }
            if let Some(bytemuck_traits) = self.ctx.bytemuck_traits.get(local_def_id) {
                let has_any_bit_pattern = bytemuck_traits
                    .iter()
                    .any(|t| t == "bytemuck::AnyBitPattern");
                let mut seen = FxHashSet::default();
                let mut parts: Vec<&str> = Vec::new();
                for t in bytemuck_traits {
                    // AnyBitPattern derive internally generates a Zeroable impl
                    if has_any_bit_pattern && t == "bytemuck::Zeroable" {
                        continue;
                    }
                    if seen.insert(t.as_str()) {
                        parts.push(t.as_str());
                    }
                }
                if !parts.is_empty() {
                    let derive_list = parts.join(", ");
                    item.attrs.extend(utils::attr!("#[derive({derive_list})]"));
                }
            }
        }
        match &mut item.kind {
            ItemKind::Struct(_, _, vd) => {
                let local_def_id = self.ast_to_hir.global_map.get(&item.id).unwrap();
                if let Some(bitfields) = self.ctx.bitfields.get(local_def_id) {
                    let VariantData::Struct { fields, .. } = vd else { panic!() };
                    for field in fields {
                        let bitfields =
                            some_or!(bitfields.get(&field.ident.unwrap().name), continue);
                        for bitfield in bitfields {
                            let BitField { name, ty, l, r } = bitfield;
                            let attrs = attr!(
                                "#[bitfield(name = \"{name}\", ty = \"{ty}\", bits = \"{l}..={r}\")]"
                            );
                            field.attrs.extend(attrs);
                        }
                    }
                }
            }
            ItemKind::Mod(_, _, ModKind::Loaded(items, ..)) => {
                unexpand_cursor_macros(items);
            }
            _ => {}
        }
        mut_visit::walk_item(self, item);
    }

    fn flat_map_stmt(&mut self, stmt: Stmt) -> SmallVec<[Stmt; 1]> {
        if let Some(mut condition) = expanded_assert_condition(&stmt) {
            self.visit_expr(&mut condition);
            let condition = pprust::expr_to_string(&condition);
            return smallvec![utils::stmt!("assert!({condition});")];
        }

        let mut stmts = mut_visit::walk_flat_map_stmt(self, stmt);
        for stmt in &mut stmts {
            // { use std::io::Write; print!(..) }; => print!(..);
            if let StmtKind::Semi(e) = &mut stmt.kind
                && let ExprKind::Block(block, _) = &mut e.kind
                && let [stmt1, stmt2] = &mut block.stmts[..]
                && let StmtKind::Item(item) = &stmt1.kind
                && matches!(item.kind, ItemKind::Use(_))
                && let StmtKind::Expr(expr) = &mut stmt2.kind
                && let expr = unwrap_paren_mut(expr)
                && let ExprKind::MacCall(mac) = &expr.kind
                && let name = mac.path.segments.last().unwrap().ident.name.as_str()
                && (name == "print" || name == "eprint")
            {
                let dummy = Expr {
                    id: DUMMY_NODE_ID,
                    kind: ExprKind::Dummy,
                    span: DUMMY_SP,
                    attrs: thin_vec![],
                    tokens: None,
                };
                let expr: Expr = std::mem::replace(expr, dummy);
                **e = expr;
            }
        }
        stmts
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if let Some(mut unexpanded) = self
            .unexpanded_comparison_assert(expr)
            .or_else(|| self.unexpanded_panic(expr))
            .or_else(|| self.unexpanded_print(expr))
        {
            unexpanded.attrs = expr.attrs.clone();
            unexpanded.span = expr.span;
            *expr = unexpanded;
            return;
        }
        if let ExprKind::Call(callee, args) = &expr.kind
            && let ExprKind::Path(None, callee) = &callee.kind
            && let [.., md, func] = &callee.segments[..]
        {
            let md = md.ident.name;
            let func = func.ident.name;
            if md == sym::panicking && self.core_panicking_call(expr).is_some() {
                if func == sym::panic
                    && let [arg] = &args[..]
                {
                    if let ExprKind::Lit(lit) = &arg.kind
                        && lit.symbol.as_str() == "internal error: entered unreachable code"
                    {
                        *expr = expr!("unreachable!()");
                    } else {
                        panic!("{}", pprust::expr_to_string(arg))
                    }
                } else {
                    panic!("{func}");
                }
            } else if md == sym::hint {
                if func == sym::must_use {
                    let [arg] = &args[..] else { panic!() };
                    *expr = (**arg).clone();
                } else {
                    panic!("{func}");
                }
            } else if md == sym::fmt {
                if func == sym::format {
                    let [arg] = &args[..] else { panic!() };
                    let arg = pprust::expr_to_string(arg);
                    let arg = arg
                        .strip_prefix("format_args!(")
                        .unwrap()
                        .strip_suffix(')')
                        .unwrap();
                    *expr = expr!("format!({arg})");
                } else {
                    panic!("{func}");
                }
            }
        } else if let ExprKind::Match(scrutinee, arms, _) = &mut expr.kind
            && let scrutinee = unwrap_paren_mut(scrutinee)
            && let ExprKind::MethodCall(call) = &scrutinee.kind
            && call.seg.ident.name == rustc_span::sym::write_fmt
            && let [arg] = &call.args[..]
            && let arg = unwrap_paren(arg)
            && matches!(arg.kind, ExprKind::FormatArgs(_))
        {
            let is_empty = arms.iter().all(|arm| {
                if let ExprKind::Block(block, _) = &arm.body.as_ref().unwrap().kind {
                    block.stmts.is_empty()
                } else {
                    false
                }
            });
            let receiver = unwrap_addr_of(&call.receiver);
            let name = if let ExprKind::Call(callee, args) = &receiver.kind
                && args.is_empty()
                && let ExprKind::Path(_, path) = &unwrap_paren(callee).kind
            {
                Some(path.segments.last().unwrap().ident.name)
            } else {
                None
            };
            let format = pprust::expr_to_string(arg);
            let format = format.strip_prefix("format_args!(").unwrap();
            if self.config.use_print
                && is_empty
                && let Some(name) = name
                && name.as_str() == "stdout"
            {
                *expr = utils::expr!("print!({format}");
            } else if self.config.use_print
                && is_empty
                && let Some(name) = name
                && name.as_str() == "stderr"
            {
                *expr = utils::expr!("eprint!({format}");
            } else {
                let receiver = pprust::expr_to_string(&call.receiver);
                *scrutinee = utils::expr!("write!({receiver}, {format}");
            }
        }
        if let ExprKind::OffsetOf(ty, fields) = &expr.kind {
            let ty_str = pprust::ty_to_string(ty);
            let fields_str = fields
                .iter()
                .map(|f| f.name.to_string())
                .collect::<Vec<_>>()
                .join(".");
            *expr = utils::expr!("core::mem::offset_of!({ty_str}, {fields_str})");
        }
        mut_visit::walk_expr(self, expr);
    }
}

impl AstVisitor<'_> {
    fn unexpanded_thread_local(&mut self, item: &Item) -> Option<Item> {
        let ItemKind::Const(value) = &item.kind else { return None };
        if !value.generics.params.is_empty() {
            return None;
        }
        let definition = self.ast_to_hir.global_map.get(&item.id)?;
        let value_type = self.tcx.type_of(*definition).instantiate_identity();
        let ty::Adt(adt, arguments) = value_type.kind() else { return None };
        if !self.tcx.is_diagnostic_item(sym::LocalKey, adt.did()) {
            return None;
        }
        let header_type = self.ast_to_hir.get_ty(value.ty.id, self.tcx)?;
        if !matches!(header_type.kind, hir::TyKind::Path(QPath::Resolved(_, path)) if path.res.opt_def_id() == Some(adt.did()))
        {
            return None;
        }
        let TyKind::Path(_, path) = &value.ty.kind else { return None };
        let GenericArgs::AngleBracketed(type_arguments) = path.segments.last()?.args.as_deref()?
        else {
            return None;
        };
        let [AngleBracketedArg::Arg(GenericArg::Type(ty))] = type_arguments.args.as_slice() else {
            return None;
        };
        let ExprKind::Block(body, None) = &value.expr.as_ref()?.kind else { return None };
        let [initialization, accessor] = body.stmts.as_slice() else { return None };
        let StmtKind::Item(initialization) = &initialization.kind else { return None };
        if !initialization
            .attrs
            .iter()
            .all(|attribute| attribute.has_name(sym::inline))
        {
            return None;
        }
        let helper = self
            .ast_to_hir
            .global_map
            .get(&initialization.id)?
            .to_def_id();
        let (mut initializer, constant) = match &initialization.kind {
            ItemKind::Const(initialization) if initialization.ident.name.as_str() == "__INIT" => {
                if !initialization.generics.params.is_empty()
                    || !initialization.generics.where_clause.predicates.is_empty()
                {
                    return None;
                }
                (initialization.expr.as_ref()?.clone(), true)
            }
            ItemKind::Fn(initialization) if initialization.ident.name.as_str() == "__init" => {
                if !initialization.generics.params.is_empty()
                    || !initialization.sig.decl.inputs.is_empty()
                    || !initialization.generics.where_clause.predicates.is_empty()
                    || initialization.sig.header.coroutine_kind.is_some()
                {
                    return None;
                }
                let body = initialization.body.as_ref()?;
                let initializer = if let [statement] = body.stmts.as_slice()
                    && let StmtKind::Expr(initializer) = &statement.kind
                {
                    initializer.clone()
                } else {
                    let mut initializer = expr!("{{}}");
                    initializer.kind = ExprKind::Block(body.clone(), None);
                    P(initializer)
                };
                (initializer, false)
            }
            _ => return None,
        };
        let StmtKind::Expr(accessor) = &accessor.kind else { return None };
        let ExprKind::Block(accessor, None) = &accessor.kind else { return None };
        let [statement] = accessor.stmts.as_slice() else { return None };
        let StmtKind::Expr(accessor) = &statement.kind else { return None };
        let (constructor, values) = self.resolved_call(accessor)?;
        let constructor_type = self.associated_adt(constructor)?;
        if constructor.is_local()
            || self.tcx.item_name(constructor).as_str() != "new"
            || !self
                .tcx
                .is_diagnostic_item(sym::LocalKey, constructor_type.did())
        {
            return None;
        }
        let [accessor] = values else { return None };
        let ExprKind::ConstBlock(accessor) = &accessor.kind else { return None };
        let ExprKind::Block(accessor, None) = &accessor.value.kind else { return None };
        let [statement] = accessor.stmts.as_slice() else { return None };
        let StmtKind::Expr(accessor) = &statement.kind else { return None };
        let ExprKind::If(condition, dropping, Some(non_dropping)) = &accessor.kind else {
            return None;
        };
        let (needs_drop, values) = self.resolved_call(condition)?;
        if !values.is_empty()
            || !self
                .tcx
                .is_diagnostic_item(Symbol::intern("needs_drop"), needs_drop)
        {
            return None;
        }
        let ExprKind::Call(callee, _) = &condition.kind else { return None };
        let callee = self.ast_to_hir.get_expr(callee.id, self.tcx)?;
        if self
            .tcx
            .typeck(callee.hir_id.owner)
            .node_args(callee.hir_id)
            .type_at(0)
            != arguments.type_at(0)
        {
            return None;
        }
        let ExprKind::Block(non_dropping, None) = &non_dropping.kind else { return None };
        if !self.native_thread_local_branch(dropping, helper, constant, true)
            || !self.native_thread_local_branch(non_dropping, helper, constant, false)
        {
            return None;
        }

        let mut uses = FeatureUses {
            tcx: self.tcx,
            ast_to_hir: &self.ast_to_hir,
            required: &mut self.ctx.required_features,
        };
        uses.visit_ty(ty);
        uses.visit_expr(&initializer);
        self.visit_expr(&mut initializer);
        let attributes = item
            .attrs
            .iter()
            .map(pprust::attribute_to_string)
            .collect::<Vec<_>>()
            .join("\n");
        let visibility = pprust::vis_to_string(&item.vis);
        let name = value.ident;
        let ty = pprust::ty_to_string(ty);
        let expression = pprust::expr_to_string(&initializer);
        let initializer = if constant {
            if matches!(initializer.kind, ExprKind::Block(_, None)) {
                format!("const {expression}")
            } else {
                format!("const {{ {expression} }}")
            }
        } else {
            expression
        };
        Some(item!(
            "::std::thread_local! {{ {attributes} {visibility} static {name}: {ty} = {initializer}; }}"
        ))
    }

    fn native_thread_local_branch(
        &self,
        block: &Block,
        helper: DefId,
        constant: bool,
        dropping: bool,
    ) -> bool {
        let [statement] = block.stmts.as_slice() else { return false };
        let StmtKind::Expr(expression) = &statement.kind else { return false };
        let ExprKind::Closure(closure) = &expression.kind else { return false };
        let [parameter] = closure.fn_decl.inputs.as_slice() else { return false };
        let ExprKind::Block(body, None) = &closure.body.kind else { return false };
        let [storage, access] = body.stmts.as_slice() else { return false };
        let StmtKind::Item(storage) = &storage.kind else { return false };
        let ItemKind::Static(value) = &storage.kind else { return false };
        if value.mutability.is_mut()
            || storage.attrs.len() != 1
            || !storage.attrs[0].has_name(sym::thread_local)
        {
            return false;
        }
        let Some(storage_id) = self.ast_to_hir.global_map.get(&storage.id).copied() else {
            return false;
        };
        let StmtKind::Expr(access) = &access.kind else { return false };
        let Some(initializer) = &value.expr else { return false };
        let is_storage = |expression: &Expr| {
            self.path_resolution(expression)
                .is_some_and(|resolution| resolution.opt_def_id() == Some(storage_id.to_def_id()))
        };
        let is_helper = |expression: &Expr| {
            self.path_resolution(expression)
                .is_some_and(|resolution| resolution.opt_def_id() == Some(helper))
        };
        if constant && !dropping {
            return is_helper(initializer)
                && matches!(&access.kind, ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, value) if is_storage(value));
        }
        let Some((constructor, arguments)) = self.resolved_call(initializer) else { return false };
        if constructor.is_local()
            || self.tcx.item_name(constructor).as_str() != "new"
            || if constant {
                !matches!(arguments, [value] if is_helper(value))
            } else {
                !arguments.is_empty()
            }
        {
            return false;
        }
        let storage_type = self.tcx.type_of(storage_id).instantiate_identity();
        let ty::Adt(storage_adt, storage_arguments) = storage_type.kind() else { return false };
        if storage_adt.did().krate != self.tcx.get_diagnostic_item(sym::LocalKey).unwrap().krate {
            return false;
        }
        let storage_path = self.tcx.def_path_str(storage_adt.did());
        if constant {
            if storage_path != "std::thread::local_impl::EagerStorage" {
                return false;
            }
        } else if storage_path != "std::thread::local_impl::LazyStorage"
            || if dropping {
                !storage_arguments.type_at(1).is_unit()
            } else {
                !storage_arguments.type_at(1).is_never()
            }
        {
            return false;
        }
        if !self
            .associated_adt(constructor)
            .is_some_and(|adt| adt.did() == storage_adt.did())
        {
            return false;
        }
        let ExprKind::MethodCall(method) = &access.kind else { return false };
        if !is_storage(&method.receiver) {
            return false;
        }
        if constant {
            if method.seg.ident.name.as_str() != "get" || !method.args.is_empty() {
                return false;
            }
        } else {
            let [input, initializer] = method.args.as_slice() else { return false };
            let Some(binding) = self.binding(&parameter.pat) else { return false };
            if method.seg.ident.name.as_str() != "get_or_init"
                || !self.is_binding(input, binding)
                || !is_helper(initializer)
            {
                return false;
            }
        }
        let Some(access) = self.ast_to_hir.get_expr(access.id, self.tcx) else { return false };
        self.tcx
            .typeck(access.hir_id.owner)
            .type_dependent_def_id(access.hir_id)
            .is_some_and(|method| {
                self.associated_adt(method)
                    .is_some_and(|adt| adt.did() == storage_adt.did())
            })
    }

    fn associated_adt(&self, definition: DefId) -> Option<ty::AdtDef<'_>> {
        if self.tcx.def_kind(definition) != DefKind::AssocFn {
            return None;
        }
        let implementation = self
            .tcx
            .associated_item(definition)
            .impl_container(self.tcx)?;
        let ty::Adt(adt, _) = self
            .tcx
            .type_of(implementation)
            .instantiate_identity()
            .kind()
        else {
            return None;
        };
        Some(*adt)
    }

    fn path_resolution(&self, expression: &Expr) -> Option<Res> {
        let expression = unwrap_paren(expression);
        let ExprKind::Path(_, path) = &expression.kind else { return None };
        if let Some(resolution) = self.ast_to_hir.path_span_to_res.get(&path.span) {
            return Some(*resolution);
        }
        let expression = self.ast_to_hir.get_expr(expression.id, self.tcx)?;
        let hir::ExprKind::Path(path) = &expression.kind else { return None };
        Some(
            self.tcx
                .typeck(expression.hir_id.owner)
                .qpath_res(path, expression.hir_id),
        )
    }

    fn binding(&self, pattern: &Pat) -> Option<hir::HirId> {
        if !matches!(
            pattern.kind,
            PatKind::Ident(BindingMode(ByRef::No, Mutability::Not), _, None)
        ) {
            return None;
        }
        let pattern = self.ast_to_hir.get_pat(pattern.id, self.tcx)?;
        let hir::PatKind::Binding(_, id, _, None) = pattern.kind else { return None };
        Some(id)
    }

    fn is_binding(&self, expression: &Expr, binding: hir::HirId) -> bool {
        expression.attrs.is_empty() && self.path_resolution(expression) == Some(Res::Local(binding))
    }

    fn is_dereferenced_binding(&self, expression: &Expr, binding: hir::HirId) -> bool {
        expression.attrs.is_empty()
            && matches!(&unwrap_paren(expression).kind, ExprKind::Unary(UnOp::Deref, value) if self.is_binding(value, binding))
    }

    fn variant(&self, expression: &Expr) -> Option<DefId> {
        let Res::Def(_, mut definition) = self.path_resolution(expression)? else { return None };
        if matches!(self.tcx.def_kind(definition), DefKind::Ctor(..)) {
            definition = self.tcx.parent(definition);
        }
        matches!(self.tcx.def_kind(definition), DefKind::Variant).then_some(definition)
    }

    fn unexpanded_comparison_assert(&mut self, expression: &Expr) -> Option<Expr> {
        let ExprKind::Match(scrutinee, arms, _) = &unwrap_paren(expression).kind else {
            return None;
        };
        let [arm] = arms.as_slice() else { return None };
        if arm.guard.is_some() || !arm.attrs.is_empty() {
            return None;
        }
        let PatKind::Tuple(bindings) = &arm.pat.kind else { return None };
        let [left_pattern, right_pattern] = bindings.as_slice() else { return None };
        let left_binding = self.binding(left_pattern)?;
        let right_binding = self.binding(right_pattern)?;
        let ExprKind::Tup(operands) = &unwrap_paren(scrutinee).kind else { return None };
        let [left, right] = operands.as_slice() else { return None };
        let ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, left) = &unwrap_paren(left).kind
        else {
            return None;
        };
        let ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, right) = &unwrap_paren(right).kind
        else {
            return None;
        };
        let ExprKind::Block(body, None) = &arm.body.as_ref()?.kind else { return None };
        if !matches!(body.rules, BlockCheckMode::Default) {
            return None;
        }
        let [statement] = body.stmts.as_slice() else { return None };
        let StmtKind::Expr(condition) = &statement.kind else { return None };
        let ExprKind::If(comparison, failure, None) = &condition.kind else { return None };
        if !condition.attrs.is_empty() || !matches!(failure.rules, BlockCheckMode::Default) {
            return None;
        }
        let (comparison, equality) = match &unwrap_paren(comparison).kind {
            ExprKind::Unary(UnOp::Not, inner) => (unwrap_paren(inner), true),
            _ => (unwrap_paren(comparison), false),
        };
        let ExprKind::Binary(operator, compared_left, compared_right) = &comparison.kind else {
            return None;
        };
        if operator.node != BinOpKind::Eq
            || !self.is_dereferenced_binding(compared_left, left_binding)
            || !self.is_dereferenced_binding(compared_right, right_binding)
        {
            return None;
        }
        let [kind, invocation] = failure.stmts.as_slice() else { return None };
        let StmtKind::Let(kind) = &kind.kind else { return None };
        let LocalKind::Init(kind_value) = &kind.kind else { return None };
        if !kind.attrs.is_empty() || kind.ty.is_some() {
            return None;
        }
        let kind_binding = self.binding(&kind.pat)?;
        let variant = self.variant(kind_value)?;
        if variant.is_local()
            || self.tcx.def_path_str(self.tcx.parent(variant)) != "core::panicking::AssertKind"
            || self.tcx.item_name(variant).as_str() != if equality { "Eq" } else { "Ne" }
        {
            return None;
        }
        let StmtKind::Semi(invocation) = &invocation.kind else { return None };
        let (name, arguments) = self.core_panicking_call(invocation)?;
        let [kind_argument, left_argument, right_argument, message] = arguments else {
            return None;
        };
        if name.as_str() != "assert_failed"
            || !invocation.attrs.is_empty()
            || !self.is_binding(kind_argument, kind_binding)
        {
            return None;
        }
        for (argument, binding) in [
            (left_argument, left_binding),
            (right_argument, right_binding),
        ] {
            let ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, value) = &argument.kind else {
                return None;
            };
            if !argument.attrs.is_empty() || !self.is_dereferenced_binding(value, binding) {
                return None;
            }
        }
        let message = if self
            .variant(message)
            .is_some_and(|definition| self.tcx.is_lang_item(definition, hir::LangItem::OptionNone))
        {
            String::new()
        } else {
            let ExprKind::Call(constructor, arguments) = &message.kind else { return None };
            let [format] = arguments.as_slice() else { return None };
            if !self.variant(constructor).is_some_and(|definition| {
                self.tcx.is_lang_item(definition, hir::LangItem::OptionSome)
            }) || !matches!(format.kind, ExprKind::FormatArgs(_))
            {
                return None;
            }
            let mut format = format.clone();
            self.visit_expr(&mut format);
            let format = pprust::expr_to_string(&format);
            format!(
                ", {}",
                format.strip_prefix("format_args!(")?.strip_suffix(')')?
            )
        };
        let (mut left, mut right) = (unwrap_paren(left).clone(), unwrap_paren(right).clone());
        self.visit_expr(&mut left);
        self.visit_expr(&mut right);
        let left = pprust::expr_to_string(&left);
        let right = pprust::expr_to_string(&right);
        let name = if equality { "assert_eq" } else { "assert_ne" };
        Some(expr!("::core::{name}!({left}, {right}{message})"))
    }

    fn resolved_call<'a>(&self, expression: &'a Expr) -> Option<(DefId, &'a [P<Expr>])> {
        let ExprKind::Call(callee, arguments) = &unwrap_paren(expression).kind else {
            return None;
        };
        let Res::Def(_, def_id) = self.path_resolution(callee)? else {
            return None;
        };
        Some((def_id, arguments))
    }

    fn core_panicking_call<'a>(&self, expression: &'a Expr) -> Option<(Symbol, &'a [P<Expr>])> {
        let (def_id, arguments) = self.resolved_call(expression)?;
        if def_id.is_local() || self.tcx.def_path_str(self.tcx.parent(def_id)) != "core::panicking"
        {
            return None;
        }
        Some((self.tcx.item_name(def_id), arguments))
    }

    fn unexpanded_print(&mut self, expression: &Expr) -> Option<Expr> {
        let expression = if let ExprKind::Block(block, None) = &expression.kind
            && matches!(block.rules, BlockCheckMode::Default)
            && let [statement] = block.stmts.as_slice()
            && let StmtKind::Semi(inner) = &statement.kind
            && inner.attrs.is_empty()
        {
            inner
        } else {
            expression
        };
        let (def_id, arguments) = self.resolved_call(expression)?;
        if def_id.is_local() || self.tcx.def_path_str(self.tcx.parent(def_id)) != "std::io::stdio" {
            return None;
        }
        let name = match self.tcx.item_name(def_id).as_str() {
            "_print" => "print",
            "_eprint" => "eprint",
            _ => return None,
        };
        let [format] = arguments else { return None };
        let mut format = unwrap_paren(format).clone();
        if !matches!(format.kind, ExprKind::FormatArgs(_)) {
            return None;
        }
        self.visit_expr(&mut format);
        let format = pprust::expr_to_string(&format);
        let arguments = format.strip_prefix("format_args!(")?.strip_suffix(')')?;
        Some(expr!("{name}!({arguments})"))
    }

    fn unexpanded_panic(&mut self, expression: &Expr) -> Option<Expr> {
        if let ExprKind::Block(block, None) = &expression.kind
            && matches!(block.rules, BlockCheckMode::Default)
        {
            match block.stmts.as_slice() {
                [statement] => {
                    if let StmtKind::Expr(inner) | StmtKind::Semi(inner) = &statement.kind
                        && inner.attrs.is_empty()
                        && self.core_panicking_call(inner).is_some()
                    {
                        return self.unexpanded_panic(inner);
                    }
                }
                [declaration, invocation] => {
                    let StmtKind::Item(item) = &declaration.kind else { return None };
                    let ItemKind::Fn(function) = &item.kind else { return None };
                    let StmtKind::Semi(call) = &invocation.kind else { return None };
                    let (callee, arguments) = self.resolved_call(call)?;
                    if Some(callee.as_local()?) != self.ast_to_hir.global_map.get(&item.id).copied()
                        || !call.attrs.is_empty()
                    {
                        return None;
                    }
                    let body = function.body.as_ref()?;
                    if !matches!(body.rules, BlockCheckMode::Default) {
                        return None;
                    }
                    let [body] = body.stmts.as_slice() else { return None };
                    let StmtKind::Expr(body) = &body.kind else { return None };
                    if !body.attrs.is_empty() {
                        return None;
                    }
                    let (name, body_arguments) = self.core_panicking_call(body)?;
                    if name.as_str() == "panic_explicit"
                        && panic_helper_has_signature(
                            item,
                            item!(
                                "#[cold] #[track_caller] #[inline(never)] const fn panic_cold_explicit() -> ! {{}}"
                            ),
                        )
                        && arguments.is_empty()
                        && body_arguments.is_empty()
                    {
                        return Some(expr!("::core::panic!(\"explicit panic\")"));
                    }
                    if name.as_str() == "panic_display"
                        && panic_helper_has_signature(
                            item,
                            item!(
                                "#[cold] #[track_caller] #[inline(never)] #[rustc_const_panic_str] #[rustc_do_not_const_check] const fn panic_cold_display<T: ::core::fmt::Display>(arg: &T) -> ! {{}}"
                            ),
                        )
                        && let [parameter] = function.sig.decl.inputs.as_slice()
                        && let [body_argument] = body_arguments
                        && let ExprKind::Path(None, path) = &body_argument.kind
                        && let Some(pattern) = self.ast_to_hir.get_pat(parameter.pat.id, self.tcx)
                        && let hir::PatKind::Binding(_, binding, _, _) = pattern.kind
                        && self.ast_to_hir.path_span_to_res.get(&path.span)
                            == Some(&Res::Local(binding))
                        && let [argument] = arguments
                        && let ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, argument) =
                            &argument.kind
                    {
                        let mut argument = argument.clone();
                        self.visit_expr(&mut argument);
                        let argument = pprust::expr_to_string(&argument);
                        return Some(expr!("::core::panic!(\"{{}}\", {argument})"));
                    }
                }
                _ => {}
            }
        }
        let (name, arguments) = self.core_panicking_call(expression)?;
        if name == sym::panic
            && let [argument] = arguments
            && let ExprKind::Lit(literal) = &argument.kind
            && let Ok(LitKind::Str(message, _)) = LitKind::from_token_lit(*literal)
            && message.as_str() != "internal error: entered unreachable code"
        {
            let message = message.as_str().replace('{', "{{").replace('}', "}}");
            return Some(expr!("::core::panic!({message:?})"));
        }
        if name.as_str() == "panic_explicit" && arguments.is_empty() {
            return Some(expr!("::core::panic!(\"explicit panic\")"));
        }
        if name.as_str() == "panic_display"
            && let [argument] = arguments
        {
            let mut argument = argument.clone();
            self.visit_expr(&mut argument);
            let argument = pprust::expr_to_string(&argument);
            return Some(expr!("::core::panic!(\"{{}}\", *({argument}))"));
        }
        if name == sym::panic_fmt
            && let [format] = arguments
            && matches!(format.kind, ExprKind::FormatArgs(_))
        {
            let mut format = format.clone();
            self.visit_expr(&mut format);
            let format = pprust::expr_to_string(&format);
            let arguments = format.strip_prefix("format_args!(")?.strip_suffix(')')?;
            return Some(expr!("::core::panic!({arguments})"));
        }
        None
    }
}

fn panic_helper_has_signature(item: &Item, expected: Item) -> bool {
    let mut header = item.clone();
    let ItemKind::Fn(function) = &mut header.kind else { unreachable!() };
    let ItemKind::Fn(expected_function) = &expected.kind else { unreachable!() };
    function.body = expected_function.body.clone();
    pprust::item_to_string(&header) == pprust::item_to_string(&expected)
}

fn expanded_assert_condition(stmt: &Stmt) -> Option<Expr> {
    let StmtKind::Semi(expr) = &stmt.kind else {
        return None;
    };
    let ExprKind::If(condition, then_block, else_expr) = &expr.kind else {
        return None;
    };
    if else_expr.is_some() {
        return None;
    }
    let ExprKind::Unary(UnOp::Not, condition) = &unwrap_paren(condition).kind else {
        return None;
    };
    let [panic_stmt] = then_block.stmts.as_slice() else {
        return None;
    };
    let StmtKind::Expr(panic_expr) = &panic_stmt.kind else {
        return None;
    };
    let ExprKind::Call(callee, args) = &panic_expr.kind else {
        return None;
    };
    let ExprKind::Path(None, path) = &callee.kind else {
        return None;
    };
    let [.., module, func] = path.segments.as_slice() else {
        return None;
    };
    if module.ident.name != sym::panicking || func.ident.name != sym::panic {
        return None;
    }
    let [arg] = args.as_slice() else {
        return None;
    };
    let ExprKind::Lit(lit) = &arg.kind else {
        return None;
    };
    if !lit.symbol.as_str().starts_with("assertion failed:") {
        return None;
    }
    Some(unwrap_paren(condition).clone())
}

fn unwrap_addr_of(expr: &Expr) -> &Expr {
    if let ExprKind::AddrOf(_, _, e) | ExprKind::Paren(e) = &expr.kind {
        unwrap_addr_of(e)
    } else {
        expr
    }
}

fn unexpand_cursor_macros(items: &mut ThinVec<P<Item>>) {
    let mut cursor_mut_read_types = vec![];
    let mut cursor_read_types = vec![];
    let mut cursor_mut_write_types = vec![];

    let mut new_items: ThinVec<_> = items
        .drain(..)
        .filter_map(|item| {
            if let ItemKind::Impl(imp) = &item.kind
                && let Some(of_trait) = &imp.of_trait
                && let Some(trait_seg) = of_trait.path.segments.last()
                && let TyKind::Path(_, self_ty) = &imp.self_ty.kind
                && let Some(self_seg) = self_ty.segments.last()
            {
                let self_name = self_seg.ident.name.as_str();
                let trait_name = trait_seg.ident.name.as_str();
                if self_name.starts_with("SliceCursor")
                    && let Some(box GenericArgs::AngleBracketed(args)) = &trait_seg.args
                    && let [AngleBracketedArg::Arg(GenericArg::Type(idx_ty))] = &args.args[..]
                    && let TyKind::Path(_, idx_path) = &idx_ty.kind
                    && let Some(idx_seg) = idx_path.segments.last()
                {
                    let ty = idx_seg.ident.name.to_string();

                    // Impls to be removed return false
                    // each cursor marco contains only one impl without Range
                    match (self_name, trait_name) {
                        (_, _) if ty.contains("Range") => {
                            return None;
                        }
                        ("SliceCursorMut", "Index") => {
                            cursor_mut_read_types.push(ty);
                            return None;
                        }
                        ("SliceCursor", "Index") => {
                            cursor_read_types.push(ty);
                            return None;
                        }
                        ("SliceCursorMut", "IndexMut") => {
                            cursor_mut_write_types.push(ty);
                            return None;
                        }
                        _ => {}
                    }
                }
            }
            Some(item)
        })
        .collect();

    if !cursor_mut_read_types.is_empty() {
        let args = cursor_mut_read_types.join(", ");
        new_items.push(P::new(item!(
            "impl_readable_index!(SliceCursorMut, {args});"
        )));
    }
    if !cursor_read_types.is_empty() {
        let args = cursor_read_types.join(", ");
        new_items.push(P::new(item!("impl_readable_index!(SliceCursor, {args});")));
    }
    if !cursor_mut_write_types.is_empty() {
        let args = cursor_mut_write_types.join(", ");
        new_items.push(P::new(item!("impl_mutable_index!({args});")));
    }
    *items = new_items;
}

#[derive(Default)]
struct Ctx {
    derived_traits: FxHashMap<LocalDefId, Vec<Symbol>>,
    bytemuck_traits: FxHashMap<LocalDefId, Vec<String>>,
    bitfields: FxHashMap<LocalDefId, FxHashMap<Symbol, Vec<BitField>>>,
    use_intrinsics: bool,
    use_transmute: bool,
    required_features: FxHashSet<Symbol>,
}

struct FeatureUses<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a utils::ir::AstToHir,
    required: &'a mut FxHashSet<Symbol>,
}

impl FeatureUses<'_, '_> {
    fn definition(&mut self, definition: DefId) {
        if !definition.is_local()
            && let Some(stability) = self.tcx.lookup_stability(definition)
            && matches!(
                stability.feature.as_str(),
                "thread_local_internals" | "fmt_helpers_for_derive" | "derive_eq"
            )
        {
            self.required.insert(stability.feature);
        }
    }
}

impl<'ast> Visitor<'ast> for FeatureUses<'_, '_> {
    fn visit_ty(&mut self, ty: &'ast Ty) {
        if matches!(ty.kind, TyKind::Never) {
            self.required.insert(Symbol::intern("never_type"));
        }
        visit::walk_ty(self, ty);
    }

    fn visit_fn_ret_ty(&mut self, return_type: &'ast FnRetTy) {
        if !matches!(return_type, FnRetTy::Ty(ty) if matches!(ty.kind, TyKind::Never)) {
            visit::walk_fn_ret_ty(self, return_type);
        }
    }

    fn visit_path(&mut self, path: &'ast Path) {
        if let Some(resolution) = self.ast_to_hir.path_span_to_res.get(&path.span)
            && let Some(definition) = resolution.opt_def_id()
        {
            self.definition(definition);
        }
        visit::walk_path(self, path);
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if matches!(expression.kind, ExprKind::Path(..))
            && let Some(expression) = self.ast_to_hir.get_expr(expression.id, self.tcx)
            && let hir::ExprKind::Path(path) = &expression.kind
            && let Some(definition) = self
                .tcx
                .typeck(expression.hir_id.owner)
                .qpath_res(path, expression.hir_id)
                .opt_def_id()
        {
            self.definition(definition);
        }
        if matches!(expression.kind, ExprKind::MethodCall(..))
            && let Some(expression) = self.ast_to_hir.get_expr(expression.id, self.tcx)
            && let Some(definition) = self
                .tcx
                .typeck(expression.hir_id.owner)
                .type_dependent_def_id(expression.hir_id)
        {
            self.definition(definition);
        }
        visit::walk_expr(self, expression);
    }
}

struct BitField {
    name: Symbol,
    ty: String,
    l: u128,
    r: u128,
}

struct Previsitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: utils::ir::AstToHir,
    ctx: Ctx,
}

impl<'ast> Visitor<'ast> for Previsitor<'_> {
    fn visit_item(&mut self, item: &'ast Item) {
        if utils::ast::is_automatically_derived(&item.attrs)
            && matches!(item.kind, ItemKind::Impl(_))
        {
            let hir_item = self.ast_to_hir.get_item(item.id, self.tcx).unwrap();
            let hir::ItemKind::Impl(imp) = hir_item.kind else { panic!() };
            let hir::TyKind::Path(QPath::Resolved(_, self_ty)) = imp.self_ty.kind else { panic!() };
            let Res::Def(_, def_id) = self_ty.res else { panic!() };
            let def_id = def_id.expect_local();
            if let Some(of_trait) = imp.of_trait {
                let of_trait = of_trait.path.segments.last().unwrap().ident.name;
                self.ctx
                    .derived_traits
                    .entry(def_id)
                    .or_default()
                    .push(of_trait);
            } else {
                let mut recovered_bitfields = false;
                let source_map = self.tcx.sess.source_map();
                for item in imp.items {
                    let impl_item = self.tcx.hir_impl_item(item.id);
                    let hir::ImplItemKind::Fn(sig, body_id) = &impl_item.kind else { continue };
                    let name = impl_item.ident.name;
                    if name.as_str().starts_with("set_") {
                        continue;
                    }
                    let hir::FnRetTy::Return(ty) = sig.decl.output else { panic!() };
                    let ty = source_map.span_to_snippet(ty.span).unwrap();
                    let body = self.tcx.hir_body(*body_id);
                    let mut visitor = HirBodyVisitor {
                        tcx: self.tcx,
                        field: None,
                    };
                    let (l, r) = visitor.visit_expr(body.value).break_value().unwrap();
                    let field = visitor.field.unwrap();
                    let bit_field = BitField { name, ty, l, r };
                    self.ctx
                        .bitfields
                        .entry(def_id)
                        .or_default()
                        .entry(field)
                        .or_default()
                        .push(bit_field);
                    recovered_bitfields = true;
                }
                if recovered_bitfields {
                    self.ctx
                        .derived_traits
                        .entry(def_id)
                        .or_default()
                        .push(Symbol::intern("BitfieldStruct"));
                }
            }
        }
        if !utils::ast::is_automatically_derived(&item.attrs)
            && let ItemKind::Impl(imp) = &item.kind
            && let Some(of_trait) = &imp.of_trait
            && of_trait
                .path
                .segments
                .iter()
                .any(|s| s.ident.name.as_str() == "bytemuck")
            && let Some(hir_item) = self.ast_to_hir.get_item(item.id, self.tcx)
            && let hir::ItemKind::Impl(hir_imp) = hir_item.kind
            && let hir::TyKind::Path(QPath::Resolved(_, self_ty)) = hir_imp.self_ty.kind
            && let Res::Def(_, def_id) = self_ty.res
            && let Some(local_def_id) = def_id.as_local()
        {
            let trait_name = of_trait.path.segments.last().unwrap().ident.name;
            self.ctx
                .bytemuck_traits
                .entry(local_def_id)
                .or_default()
                .push(format!("bytemuck::{trait_name}"));
        }

        visit::walk_item(self, item);
    }

    fn visit_path(&mut self, path: &'ast ast::Path) {
        if let [pre @ .., _] = &path.segments[..]
            && pre.iter().any(|s| s.ident.name == sym::intrinsics)
        {
            self.ctx.use_intrinsics = true;
        }
        if path.segments.last().unwrap().ident.name == sym::transmute {
            self.ctx.use_transmute = true;
        }
        visit::walk_path(self, path);
    }
}

struct HirBodyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    field: Option<Symbol>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirBodyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type Result = ControlFlow<(u128, u128)>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_local(&mut self, local: &'tcx hir::LetStmt<'tcx>) -> Self::Result {
        if let Some(init) = local.init {
            if let hir::ExprKind::AddrOf(hir::BorrowKind::Ref, ast::Mutability::Not, e) = init.kind
                && let hir::ExprKind::Field(e, f) = e.kind
                && let hir::ExprKind::Path(QPath::Resolved(_, p)) = e.kind
                && p.segments.last().unwrap().ident.name == kw::SelfLower
            {
                assert!(self.field.is_none());
                self.field = Some(f.name);
            } else if let hir::ExprKind::Tup([l, r]) = init.kind
                && let hir::ExprKind::Lit(l) = l.kind
                && let ast::LitKind::Int(l, _) = l.node
                && let hir::ExprKind::Lit(r) = r.kind
                && let ast::LitKind::Int(r, _) = r.node
            {
                assert!(self.field.is_some());
                return ControlFlow::Break((l.get(), r.get()));
            }
        }
        intravisit::walk_local(self, local)
    }
}

#[cfg(test)]
mod tests {
    fn normalize_source(code: &str) -> String {
        let expanded = utils::compilation::run_compiler_on_str(code, |tcx| {
            crate::expander::expand(crate::expander::Config::default(), tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&expanded, utils::type_check).expect(&expanded);
        let normalized = utils::compilation::run_compiler_on_str(&expanded, |tcx| {
            super::unexpand(super::Config::default(), tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&normalized, utils::type_check).expect(&normalized);
        normalized
    }

    #[test]
    fn thread_local_reconstruction_uses_resolved_identity_and_keeps_raw_accessors() {
        let source = normalize_source(
            r#"
#![feature(thread_local_internals)]
struct LocalKey<T>(T);
const LOOKALIKE: LocalKey<i32> = { const __INIT: i32 = { 3 }; LocalKey(__INIT) };
const RAW: std::thread::LocalKey<i32> = {
    const __INIT: i32 = 4;
    unsafe { std::thread::LocalKey::new(|_| &__INIT) }
};
macro_rules! thread_local { ($($tokens:tt)*) => { compile_error!("shadowed macro") }; }
use std::thread_local as scoped;
scoped! { #[allow(dead_code)] pub(crate) static r#type: std::cell::Cell<u32> = std::cell::Cell::new(5); }
fn read() -> i32 { RAW.with(|value| *value) + LOOKALIKE.0 }
"#,
        );
        assert_eq!(
            source.matches("::std::thread_local!").count(),
            1,
            "{source}"
        );
        assert!(source.contains("#[allow(dead_code)]"), "{source}");
        assert!(source.contains("pub(crate) static r#type"), "{source}");
        assert!(
            source.contains("const LOOKALIKE: LocalKey<i32>"),
            "{source}"
        );
        assert!(
            source.contains("const RAW: std::thread::LocalKey<i32>"),
            "{source}"
        );
        assert!(
            source.contains("#![feature(thread_local_internals)]"),
            "{source}"
        );
    }

    #[test]
    fn cleanup_preserves_never_types_inside_reconstructed_thread_local_tokens() {
        let source = normalize_source(
            r#"
#![feature(never_type)]
std::thread_local! {
    static VALUE: std::cell::Cell<Option<!>> = const { std::cell::Cell::new(None) };
}
fn read() -> bool { VALUE.with(|value| value.get().is_none()) }
"#,
        );
        assert!(source.contains("::std::thread_local!"), "{source}");
        assert!(source.contains("Option<!>"), "{source}");
        assert!(source.contains("#![feature(never_type)]"), "{source}");
        assert!(
            !source.contains("#![feature(thread_local_internals)]"),
            "{source}"
        );
        assert_eq!(normalize_source(&source), source);
    }

    #[test]
    fn const_thread_local_reconstruction_wraps_a_simplified_initializer() {
        let expanded = utils::compilation::run_compiler_on_str(
            "std::thread_local! { static VALUE: u32 = const { 7 }; }",
            |tcx| crate::expander::expand(crate::expander::Config::default(), tcx),
        )
        .unwrap();
        assert!(
            expanded.contains("const __INIT: u32 = { 7 };"),
            "{expanded}"
        );
        let expanded = expanded.replace("const __INIT: u32 = { 7 };", "const __INIT: u32 = 7;");
        let normalized = utils::compilation::run_compiler_on_str(&expanded, |tcx| {
            super::unexpand(super::Config::default(), tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&normalized, utils::type_check).expect(&normalized);
        assert!(
            normalized.contains("static VALUE: u32 = const { 7 }"),
            "{normalized}"
        );
        assert!(!normalized.contains("LocalKey::new"), "{normalized}");
        assert_eq!(normalize_source(&normalized), normalized);
    }

    #[test]
    fn thread_local_reconstruction_declines_transformed_aliases_and_generic_helpers() {
        let source = r#"
type Key<T> = std::thread::LocalKey<(T, T)>;
std::thread_local! { static ALIASED: (i32, i32) = (1, 2); static GENERIC: i32 = 3; }
"#;
        let expanded = utils::compilation::run_compiler_on_str(source, |tcx| {
            crate::expander::expand(crate::expander::Config::default(), tcx)
        })
        .unwrap();
        assert!(
            expanded.contains("::std::thread::LocalKey<(i32, i32)>"),
            "{expanded}"
        );
        let expanded = expanded
            .replace("::std::thread::LocalKey<(i32, i32)>", "Key<i32>")
            .replace("fn __init() -> i32", "fn __init<T: Default>() -> i32")
            .replace(
                "get_or_init(init, __init)",
                "get_or_init(init, __init::<()>)",
            );
        // The tuple helper is not generic, so only specialize calls in GENERIC's item.
        let start = expanded.find("const GENERIC:").unwrap();
        let expanded = format!(
            "{}{}",
            expanded[..start].replace("__init::<()>", "__init"),
            &expanded[start..]
        );
        let normalized = utils::compilation::run_compiler_on_str(&expanded, |tcx| {
            super::unexpand(super::Config::default(), tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&normalized, utils::type_check).expect(&normalized);
        assert!(!normalized.contains("::std::thread_local!"), "{normalized}");
        assert!(
            normalized.contains("const ALIASED: Key<i32>"),
            "{normalized}"
        );
        assert!(normalized.contains("fn __init<T: Default>"), "{normalized}");
        assert!(
            normalized.contains("#![feature(thread_local_internals)]"),
            "{normalized}"
        );
    }

    #[test]
    fn thread_local_reconstruction_preserves_generic_outer_constants() {
        let expanded = utils::compilation::run_compiler_on_str(
            "std::thread_local! { static VALUE: u32 = const { 7 }; }",
            |tcx| crate::expander::expand(crate::expander::Config::default(), tcx),
        )
        .unwrap();
        assert!(expanded.contains("const VALUE:"), "{expanded}");
        let expanded = format!(
            "#![feature(generic_const_items)]\n{}",
            expanded.replace("const VALUE:", "const VALUE<const N: usize>:")
        );
        let normalized = utils::compilation::run_compiler_on_str(&expanded, |tcx| {
            super::unexpand(super::Config::default(), tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&normalized, utils::type_check).expect(&normalized);
        assert!(
            normalized.contains("const VALUE<const N : usize>"),
            "{normalized}"
        );
        assert!(!normalized.contains("::std::thread_local!"), "{normalized}");
        assert!(
            normalized.contains("#![feature(thread_local_internals)]"),
            "{normalized}"
        );
    }

    #[test]
    fn cleanup_filters_combined_features_and_retains_exposed_library_helpers() {
        let source = r#"
#![feature(panic_internals, thread_local_internals, never_type, fmt_helpers_for_derive, derive_eq, allocator_api)]
type Empty = Option<!>;
use std::thread::LocalKey as Key;
const RAW: Key<i32> = unsafe { Key::new(|_| &1) };
fn format(f: &mut std::fmt::Formatter<'_>, value: &bool) -> std::fmt::Result {
    f.debug_struct_field1_finish("Entry", "value", value)
}
fn eq() { let _: core::cmp::AssertParamIsEq<bool>; }
fn allocate(value: u32) -> Result<Box<u32>, std::alloc::AllocError> { Box::try_new(value) }
"#;
        let normalized = utils::compilation::run_compiler_on_str(source, |tcx| {
            super::unexpand(super::Config::default(), tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&normalized, utils::type_check).expect(&normalized);
        for feature in [
            "thread_local_internals",
            "never_type",
            "fmt_helpers_for_derive",
            "derive_eq",
            "allocator_api",
        ] {
            assert!(
                normalized.contains(&format!("#![feature({feature})]")),
                "{normalized}"
            );
        }
        assert!(
            !normalized.contains("#![feature(panic_internals)]"),
            "{normalized}"
        );
    }

    fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
        let config = super::Config { use_print: true };
        let s = utils::compilation::run_compiler_on_str(code, |tcx| super::unexpand(config, tcx))
            .unwrap();
        utils::compilation::run_compiler_on_str(&s, utils::type_check).expect(&s);
        for include in includes {
            assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
        }
        for exclude in excludes {
            assert!(
                !s.contains(exclude),
                "Expected not to find `{exclude}` in:\n{s}"
            );
        }
    }

    #[test]
    fn cleanup_recompiles_expanded_eq_derive_and_restores_attributes() {
        let code = r#"
#[repr(u32)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind { Circle, Aabb }
#[no_mangle]
pub unsafe extern "C" fn compare(left: Kind, right: Kind) -> bool { left == right }
"#;
        let expanded = utils::compilation::run_compiler_on_str(code, |tcx| {
            crate::expander::expand(crate::expander::Config::default(), tcx)
        })
        .unwrap();
        assert!(expanded.contains("#[coverage(off)]"), "{expanded}");
        assert!(
            expanded.contains("#![feature(coverage_attribute)]"),
            "{expanded}"
        );

        let c_exposed_fns = rustc_hash::FxHashSet::from_iter(["compare".to_owned()]);
        let interfaces = utils::compilation::run_compiler_on_str(&expanded, |tcx| {
            crate::interface_fixer::fix_interfaces(
                &crate::interface_fixer::Config {
                    c_exposed_fns: c_exposed_fns.clone(),
                    ..Default::default()
                },
                tcx,
            )
        })
        .unwrap();
        let resolved = utils::compilation::run_compiler_on_str(&interfaces, |tcx| {
            crate::unsafe_resolver::resolve_unsafe(
                &crate::unsafe_resolver::Config {
                    remove_unused: true,
                    remove_no_mangle: true,
                    remove_extern_c: true,
                    replace_pub: true,
                    c_exposed_fns,
                },
                tcx,
            )
        })
        .unwrap();
        run_test(
            &resolved,
            &["#[derive(Eq)]", "#[derive(PartialEq)]", "fn compare("],
            &[
                "#[coverage(off)]",
                "coverage_attribute",
                "assert_receiver_is_total_eq",
            ],
        );
    }

    fn normalize_panic_source(code: &str) -> String {
        let expanded = utils::compilation::run_compiler_on_str(code, |tcx| {
            crate::expander::expand(crate::expander::Config { keep_allows: true }, tcx)
        })
        .unwrap();
        let normalized = utils::compilation::run_compiler_on_str(&expanded, |tcx| {
            super::unexpand(super::Config::default(), tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&normalized, utils::type_check).expect(&normalized);
        normalized
    }

    fn assert_stable_panic_source(code: &str) -> String {
        let first = normalize_panic_source(code);
        let second = normalize_panic_source(&first);
        assert_eq!(first, second);
        assert!(!second.contains("panic_cold_"), "{second}");
        assert!(!second.contains("panicking::"), "{second}");
        second
    }

    #[test]
    fn panic_messages_and_arguments_survive_repeated_normalization() {
        let source = assert_stable_panic_source(
            r#"
fn literal() -> ! { panic!("Reached end of non-void function without returning") }
fn explicit() -> ! { panic!() }
fn next_value() -> i32 { 7 }
fn formatted() -> ! { panic!("Invalid value: {}", next_value()) }
fn named(value: i32) -> ! { panic!("{captured} {named}", named = value, captured = next_value()) }
fn captured(value: i32) -> ! { panic!("Invalid value: {value}") }
"#,
        );
        assert!(source.contains("Reached end of non-void function without returning"));
        assert!(source.contains("::core::panic!(\"explicit panic\")"));
        assert!(source.contains("Invalid value: {0}"));
        assert_eq!(source.matches("next_value()").count(), 3);
        assert!(
            source.contains("\"{1} {0}\", value, next_value()"),
            "{source}"
        );
    }

    #[test]
    fn comparison_assertions_preserve_operands_messages_and_expression_roles() {
        let source = assert_stable_panic_source(
            r#"
fn left() -> String { String::new() }
fn right() -> String { String::new() }
fn message() -> usize { 7 }
fn f() {
    assert_eq!(left(), right());
    assert_ne!(left(), right(), "detail: {}", message());
}
fn tail(left: &[i32], right: &[i32]) { assert_eq!(left, right) }
fn returned(left: &str, right: &str) { return assert_ne!(left, right); }
"#,
        );
        assert!(source.contains("::core::assert_eq!("), "{source}");
        assert!(source.contains("::core::assert_ne!("), "{source}");
        assert_eq!(source.matches("left()").count(), 3, "{source}");
        assert_eq!(source.matches("right()").count(), 3, "{source}");
        assert_eq!(source.matches("message()").count(), 2, "{source}");
        assert!(source.contains("detail:"), "{source}");
    }

    #[test]
    fn comparison_assertion_reconstruction_uses_resolved_identity() {
        let source = normalize_panic_source(
            r#"
mod panicking { pub fn assert_failed(value: i32) -> i32 { value + 1 } }
macro_rules! assert_eq { ($($arg:tt)*) => { 7 }; }
macro_rules! assert_ne { ($($arg:tt)*) => { 9 }; }
fn f(left: &str, right: &str) {
    ::core::assert_eq!(left, right);
    ::core::assert_ne!(left, right);
}
fn lookalike() -> i32 { panicking::assert_failed(3) }
"#,
        );
        assert!(source.contains("::core::assert_eq!("), "{source}");
        assert!(source.contains("::core::assert_ne!("), "{source}");
        assert!(source.contains("panicking::assert_failed(3)"), "{source}");
    }

    #[test]
    fn literal_core_panics_preserve_escaping_constness_and_never_coercions() {
        let source = assert_stable_panic_source(
            r#"
#![feature(panic_internals)]
const fn pending() -> ! { todo!() }
const fn absent() -> ! { unimplemented!() }
fn initializer() -> i32 { let value: i32 = todo!(); value }
const fn literal() -> ! {
    ::core::panicking::panic("literal {braces}, \"quotes\", \\slash\nnewline")
}
"#,
        );
        assert!(source.contains("not yet implemented"), "{source}");
        assert!(source.contains("not implemented"), "{source}");
        assert!(source.contains("{{braces}}"), "{source}");
        assert!(source.contains("const fn literal"), "{source}");
    }

    #[test]
    fn assertions_and_literal_panics_survive_preparation_and_postprocessing() {
        let code = r#"
pub fn compare(left: &str, right: &str) {
    assert_eq!(left, right, "detail {}", left.len());
    assert_ne!(left, right);
}
pub const fn pending() -> ! { todo!() }
"#;
        let expanded = utils::compilation::run_compiler_on_str(code, |tcx| {
            crate::expander::expand(crate::expander::Config::default(), tcx)
        })
        .unwrap();
        let prepared = utils::compilation::run_compiler_on_str(&expanded, crate::preparer::prepare)
            .unwrap()
            .unwrap()
            .code;
        let interfaces = utils::compilation::run_compiler_on_str(&expanded, |tcx| {
            crate::interface_fixer::fix_interfaces(&crate::interface_fixer::Config::default(), tcx)
        })
        .unwrap();
        let resolved = utils::compilation::run_compiler_on_str(&interfaces, |tcx| {
            crate::unsafe_resolver::resolve_unsafe(&crate::unsafe_resolver::Config::default(), tcx)
        })
        .unwrap();
        for input in [prepared, resolved] {
            let output = utils::compilation::run_compiler_on_str(&input, |tcx| {
                super::unexpand(super::Config::default(), tcx)
            })
            .unwrap();
            utils::compilation::run_compiler_on_str(&output, utils::type_check).expect(&output);
            assert!(!output.contains("panicking::"), "{output}");
            assert!(output.contains("::core::assert_eq!("), "{output}");
            assert!(output.contains("not yet implemented"), "{output}");
        }
    }

    #[test]
    fn panic_format_arguments_are_normalized_before_reconstruction() {
        let source = normalize_panic_source(
            r#"
#[repr(C)] struct Pair { left: i32, right: i32 }
fn f(flag: bool) -> ! {
    panic!("offset: {}", if flag {
        core::mem::offset_of!(Pair, right)
    } else {
        panic!("inner panic")
    })
}
"#,
        );
        assert!(source.contains("offset_of!"));
        assert!(source.contains("inner panic"));
        assert!(!source.contains("builtin # offset_of"));
    }

    #[test]
    fn panic_reconstruction_uses_resolved_core_identity() {
        let source = normalize_panic_source(
            r#"
mod panicking { pub fn panic_fmt(value: i32) -> i32 { value + 1 } }
macro_rules! panic { ($($argument:tt)*) => { 7 }; }
fn f() -> ! { ::core::panic!("real panic") }
fn lookalike() -> i32 { panicking::panic_fmt(3) }
fn helper() -> ! {
    #[cold]
    #[track_caller]
    #[inline(never)]
    const fn panic_cold_explicit() -> ! { ::core::panic!("custom helper") }
    panic_cold_explicit();
}
fn attributed_helper() -> ! {
    #[cold]
    #[track_caller]
    #[inline(never)]
    #[export_name = "user_panic_helper"]
    const fn panic_cold_explicit() -> ! { ::core::panic!() }
    panic_cold_explicit();
}
"#,
        );
        assert!(source.contains("::core::panic!(\"real panic\")"));
        assert!(source.contains("panicking::panic_fmt(3)"));
        assert!(source.contains("const fn panic_cold_explicit()"));
        assert!(source.contains("custom helper"));
        assert!(source.contains("#[export_name = \"user_panic_helper\"]"));
    }

    #[test]
    fn display_panic_helpers_are_reconstructed_without_changing_const_support() {
        let code = r#"
const fn f() -> ! { panic!("{}", "message") }
fn g(value: i32) -> ! { panic!("{}", value) }
"#;
        let normalize = |code: &str| {
            utils::compilation::run_compiler_on_str(code, |tcx| {
                super::unexpand(super::Config::default(), tcx)
            })
            .unwrap()
        };
        let first = normalize(code);
        let second = normalize(&first);
        assert_eq!(first, second);
        assert!(!second.contains("panic_cold_"));
        utils::compilation::run_compiler_on_str(&second, utils::type_check).expect(&second);
    }

    #[test]
    fn handwritten_display_helper_keeps_its_argument_type() {
        let code = r#"
#![feature(panic_internals)]
fn f(value: &str) -> ! {
    #[cold]
    #[track_caller]
    #[inline(never)]
    const fn panic_cold_display(arg: &&str) -> ! {
        ::core::panicking::panic_display(arg)
    }
    panic_cold_display(&value);
}
"#;
        let source = normalize_panic_source(code);
        assert!(source.contains("const fn panic_cold_display(arg: &&str)"));
        assert!(source.contains("panic_cold_display(&value)"));
        assert!(source.contains("::core::panic!(\"{}\", *(arg))"));
    }

    #[test]
    fn test_offset_of() {
        run_test(
            r#"
#[repr(C)]
struct S { a: i32, b: i64 }
fn f() -> usize { core::mem::offset_of!(S, b) }
            "#,
            &["offset_of!"],
            &["builtin"],
        )
    }

    #[test]
    fn test_print() {
        run_test(
            r#"
fn f() {
    use std::io::Write;
    match (&mut std::io::stdout()).write_fmt(format_args!("")) {
        Ok(_) => {}
        Err(_) => {}
    };
}
            "#,
            &["print!"],
            &["stdout", "write_fmt", "format_args"],
        )
    }

    #[test]
    fn test_eprint() {
        run_test(
            r#"
fn f() {
    use std::io::Write;
    match (&mut std::io::stderr()).write_fmt(format_args!("")) {
        Ok(_) => {}
        Err(_) => {}
    };
}
            "#,
            &["eprint!"],
            &["stdout", "write_fmt", "format_args"],
        )
    }

    fn normalize_print_source(code: &str, use_print: bool) -> String {
        let expanded = utils::compilation::run_compiler_on_str(code, |tcx| {
            crate::expander::expand(crate::expander::Config { keep_allows: true }, tcx)
        })
        .unwrap();
        let normalized = utils::compilation::run_compiler_on_str(&expanded, |tcx| {
            super::unexpand(super::Config { use_print }, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&normalized, utils::type_check).expect(&normalized);
        normalized
    }

    #[test]
    fn print_macros_survive_repeated_normalization() {
        let code = r#"
fn next_value() -> i32 { 7 }
pub fn f(value: i32) {
    ::std::print!("Hello World!\n");
    ::std::println!();
    ::std::println!("stdout: {value}");
    ::std::eprint!("stderr: {}", next_value());
    ::std::eprintln!();
    ::std::eprintln!("{captured} {named}", named = value, captured = next_value());
}
"#;
        for use_print in [false, true] {
            let first = normalize_print_source(code, use_print);
            let second = normalize_print_source(&first, use_print);
            assert_eq!(first, second);
            for expected in [
                "print!(\"Hello World!\\n\")",
                "print!(\"\\n\")",
                "print!(\"stdout: {0}\\n\", value)",
                "eprint!(\"stderr: {0}\", next_value())",
                "eprint!(\"\\n\")",
                "eprint!(\"{1} {0}\\n\", value, next_value())",
            ] {
                let statement = format!("{expected};");
                assert!(
                    second.lines().any(|line| line.trim() == statement),
                    "{second}"
                );
            }
            assert_eq!(second.matches("next_value()").count(), 3);
            for unexpected in [
                "_print",
                "_eprint",
                "format_args!",
                "print_internals",
                "std::print!",
                "std::eprint!",
            ] {
                assert!(!second.contains(unexpected), "{second}");
            }
        }
    }

    #[test]
    fn print_format_arguments_are_normalized_before_reconstruction() {
        let source = normalize_print_source(
            r#"
#[repr(C)] struct Pair { left: i32, right: i32 }
pub fn f(flag: bool) {
    ::std::print!("offset: {}", if flag {
        core::mem::offset_of!(Pair, right)
    } else {
        ::std::eprint!("nested print");
        0
    });
}
"#,
            false,
        );
        assert!(
            source.contains("core::mem::offset_of!(Pair, right)"),
            "{source}"
        );
        assert!(source.contains("eprint!(\"nested print\")"), "{source}");
        assert!(!source.contains("builtin # offset_of"), "{source}");
        assert!(!source.contains("::_print"), "{source}");
        assert!(!source.contains("::_eprint"), "{source}");
    }

    #[test]
    fn print_reconstruction_uses_resolved_std_identity() {
        run_test(
            r#"
mod io {
    pub fn _print(_: std::fmt::Arguments<'_>) {}
    pub fn _eprint(_: std::fmt::Arguments<'_>) {}
}
pub fn f() {
    io::_print(format_args!("user stdout"));
    io::_eprint(format_args!("user stderr"));
    ::std::io::_print(format_args!("real stdout"));
    ::std::io::_eprint(format_args!("real stderr"));
}
"#,
            &[
                "io::_print(format_args!(\"user stdout\"))",
                "io::_eprint(format_args!(\"user stderr\"))",
                "print!(\"real stdout\")",
                "eprint!(\"real stderr\")",
            ],
            &["::std::io::_print", "::std::io::_eprint"],
        );
    }

    #[test]
    fn print_reconstruction_preserves_blocks_and_attributes() {
        run_test(
            r#"
pub fn f() {
    'kept: { ::std::io::_print(format_args!("labeled")); }
    unsafe { ::std::io::_eprint(format_args!("unsafe")); }
    {
        #[allow(unused_must_use)]
        ::std::io::_print(format_args!("attributed"));
    }
}
"#,
            &[
                "'kept:",
                "unsafe { eprint!(\"unsafe\"); }",
                "#[allow(unused_must_use)]",
                "print!(\"attributed\")",
            ],
            &["::_print", "::_eprint"],
        );
    }

    #[test]
    fn cleanup_restores_print_macros() {
        let code = r#"
unsafe fn main_0() -> i32 {
    ::std::print!("Hello World!\n");
    ::std::eprintln!("status: {}", 0);
    0
}
pub fn main() { unsafe { ::std::process::exit(main_0()) } }
"#;
        let expanded = utils::compilation::run_compiler_on_str(code, |tcx| {
            crate::expander::expand(crate::expander::Config::default(), tcx)
        })
        .unwrap();
        let interfaces = utils::compilation::run_compiler_on_str(&expanded, |tcx| {
            crate::interface_fixer::fix_interfaces(&crate::interface_fixer::Config::default(), tcx)
        })
        .unwrap();
        let resolved = utils::compilation::run_compiler_on_str(&interfaces, |tcx| {
            crate::unsafe_resolver::resolve_unsafe(
                &crate::unsafe_resolver::Config {
                    remove_unused: true,
                    remove_no_mangle: true,
                    remove_extern_c: true,
                    replace_pub: true,
                    ..Default::default()
                },
                tcx,
            )
        })
        .unwrap();
        run_test(
            &resolved,
            &[
                "print!(\"Hello World!\\n\")",
                "eprint!(\"status: {0}\\n\", 0)",
            ],
            &["::_print", "::_eprint", "print_internals"],
        );
    }

    #[test]
    fn test_assert() {
        run_test(
            r#"
fn f(x: i32) {
    assert!(x != 0);
}
            "#,
            &["assert!(x != 0);"],
            &["panicking", "assertion failed"],
        )
    }

    #[test]
    fn test_write() {
        run_test(
            r#"
fn f() {
    use std::io::Write;
    let x: i32 = match (&mut std::io::stdout()).write_fmt(format_args!("")) {
        Ok(_) => (0, 0),
        Err(_) => (-1, 1),
    }.0;
}
            "#,
            &["write!"],
            &["write_fmt", "format_args"],
        )
    }

    #[test]
    fn empty_generated_impl_does_not_restore_bitfield_derive() {
        run_test(
            r#"
#[repr(C)]
#[derive(Clone, Copy)]
pub struct Flags {
    pub ready_busy: [u8; 1],
    pub c2rust_padding: [u8; 7],
}
#[automatically_derived]
impl Flags {}
pub fn keep(value: Flags) -> Flags { value }
"#,
            &[
                "pub struct Flags",
                "ready_busy: [u8; 1]",
                "c2rust_padding: [u8; 7]",
                "#[derive(Clone)]",
                "#[derive(Copy)]",
            ],
            &["BitfieldStruct", "bitfield(", "impl Flags"],
        );
    }

    #[test]
    fn populated_bitfields_restore_derive_and_field_metadata() {
        let source = r#"
use c2rust_bitfields::BitfieldStruct;
#[repr(C)]
#[derive(BitfieldStruct)]
pub struct Flags {
    #[bitfield(name = "ready", ty = "u8", bits = "0..=0")]
    #[bitfield(name = "busy", ty = "u8", bits = "1..=1")]
    pub ready_busy: [u8; 1],
    pub c2rust_padding: [u8; 7],
}
pub fn read(value: Flags) -> u8 { value.ready() }
"#;
        let expanded = utils::compilation::run_compiler_on_str(source, |tcx| {
            crate::expander::expand(crate::expander::Config::default(), tcx)
        })
        .unwrap();
        run_test(
            &expanded,
            &[
                "#[derive(BitfieldStruct)]",
                "name = \"ready\"",
                "name = \"busy\"",
                "bits = \"0..=0\"",
                "bits = \"1..=1\"",
                "ready_busy: [u8; 1]",
                "c2rust_padding: [u8; 7]",
            ],
            &["impl Flags", "automatically_derived"],
        );
    }

    // bytemuck tests skip type checking
    // #[derive(bytemuck::...)] requires the proc macro crate
    fn run_bytemuck_test(code: &str, includes: &[&str], excludes: &[&str]) {
        let config = super::Config { use_print: true };
        let s = utils::compilation::run_compiler_on_str(code, |tcx| super::unexpand(config, tcx))
            .unwrap();
        for include in includes {
            assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
        }
        for exclude in excludes {
            assert!(
                !s.contains(exclude),
                "Expected not to find `{exclude}` in:\n{s}"
            );
        }
    }

    #[test]
    fn test_bytemuck_pod() {
        run_bytemuck_test(
            r#"
mod bytemuck {
    pub unsafe trait Zeroable {}
    pub unsafe trait Pod: Zeroable {}
}
#[repr(C)]
struct S { x: f32, y: f32 }
unsafe impl bytemuck::Zeroable for S {}
unsafe impl bytemuck::Pod for S {}
            "#,
            &["#[derive(bytemuck::Zeroable, bytemuck::Pod)]"],
            &["unsafe impl bytemuck"],
        )
    }

    #[test]
    fn test_bytemuck_anybitpattern() {
        run_bytemuck_test(
            r#"
mod bytemuck {
    pub unsafe trait Zeroable {}
    pub unsafe trait AnyBitPattern: Zeroable {}
}
struct T { x: f32 }
unsafe impl bytemuck::Zeroable for T {}
unsafe impl bytemuck::AnyBitPattern for T {}
            "#,
            &["#[derive(bytemuck::AnyBitPattern)]"],
            &["unsafe impl bytemuck", "derive(bytemuck::Zeroable"],
        )
    }
}
