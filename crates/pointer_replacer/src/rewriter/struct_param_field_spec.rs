//! applies the struct-param field specialization plan: narrows selected
//! struct-pointer parameters to field pointers, rewrites their body field
//! accesses, and updates every call site. edits are resolved per function
//! before any mutation; an unresolvable function drops out together with the
//! targets that forward into it (group-atomic, no partial rewrites).

use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    token,
    visit::{self as ast_visit, Visitor as AstVisitor},
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{Ident, Symbol, def_id::LocalDefId};
use thin_vec::thin_vec;
use utils::ir::AstToHir;

use crate::analyses::struct_param_field_spec::{SpecPlan, SpecTarget};

// per-function rewrite instructions resolved during validation
struct FnPlan {
    param_idx: usize,
    param_name: Symbol,
    field_name: Symbol,
    field_ty: P<Ty>,
}

pub(crate) fn apply_struct_param_field_spec(
    krate: &mut Crate,
    plan: &SpecPlan,
    tcx: TyCtxt<'_>,
    ast_to_hir: &AstToHir,
) -> bool {
    let field_tys = collect_field_tys(krate, plan, ast_to_hir);
    let fn_plans = resolve_and_validate(krate, plan, &field_tys, tcx, ast_to_hir);
    if fn_plans.is_empty() {
        return false;
    }
    let mut visitor = SpecTransformVisitor {
        fn_plans: &fn_plans,
        tcx,
        ast_to_hir,
        current_fn: None,
        changed: false,
    };
    visitor.visit_crate(krate);
    visitor.changed
}

// recurses into `ItemKind::Mod` so callers see every item regardless of how
// deeply c2rust nested it (it wraps translation units in `pub mod src { pub
// mod lib { ... } }`); read-only, does not allocate a flattened copy
fn walk_items<'a>(items: &'a [P<Item>], f: &mut impl FnMut(&'a Item)) {
    for item in items {
        f(item);
        if let ItemKind::Mod(_, _, ModKind::Loaded(nested, ..)) = &item.kind {
            walk_items(nested, f);
        }
    }
}

// phase 0: clone the declared AST type of each target field from its struct item
fn collect_field_tys(
    krate: &Crate,
    plan: &SpecPlan,
    ast_to_hir: &AstToHir,
) -> FxHashMap<(LocalDefId, usize), P<Ty>> {
    let needed: FxHashSet<(LocalDefId, usize)> = plan
        .targets
        .values()
        .map(|t| (t.struct_def, t.field.as_usize()))
        .collect();
    let mut out = FxHashMap::default();
    walk_items(&krate.items, &mut |item| {
        let ItemKind::Struct(_, _, VariantData::Struct { fields, .. }) = &item.kind else {
            return;
        };
        let Some(&did) = ast_to_hir.global_map.get(&item.id) else {
            return;
        };
        for (idx, field) in fields.iter().enumerate() {
            if needed.contains(&(did, idx)) {
                out.insert((did, idx), field.ty.clone());
            }
        }
    });
    out
}

// phase 1: resolve edits per target fn; reject functions whose param is used
// outside the rewritable shapes; cascade drops through forwarding edges
fn resolve_and_validate(
    krate: &Crate,
    plan: &SpecPlan,
    field_tys: &FxHashMap<(LocalDefId, usize), P<Ty>>,
    tcx: TyCtxt<'_>,
    ast_to_hir: &AstToHir,
) -> FxHashMap<(LocalDefId, usize), FnPlan> {
    let mut fn_plans: FxHashMap<(LocalDefId, usize), FnPlan> = FxHashMap::default();
    let mut dropped: FxHashSet<(LocalDefId, usize)> = FxHashSet::default();

    walk_items(&krate.items, &mut |item| {
        let ItemKind::Fn(func) = &item.kind else {
            return;
        };
        let Some(&did) = ast_to_hir.global_map.get(&item.id) else {
            return;
        };
        for (&(target_did, param_idx), target) in &plan.targets {
            if target_did != did {
                continue;
            }
            let key = (did, param_idx);
            let ok = resolve_fn_plan(func, param_idx, target, field_tys, tcx, ast_to_hir, plan)
                .map(|fn_plan| fn_plans.insert(key, fn_plan));
            if ok.is_none() {
                dropped.insert(key);
            }
        }
    });
    // targets whose fn item was never found are dropped too
    for key in plan.targets.keys() {
        if !fn_plans.contains_key(key) {
            dropped.insert(*key);
        }
    }

    // cascade: a forwarder into a dropped target cannot be rewritten either
    loop {
        let before = dropped.len();
        for (from, to) in &plan.forwards {
            if dropped.contains(to) {
                dropped.insert(*from);
            }
        }
        if dropped.len() == before {
            break;
        }
    }
    fn_plans.retain(|key, _| !dropped.contains(key));
    fn_plans
}

fn resolve_fn_plan(
    func: &Fn,
    param_idx: usize,
    target: &SpecTarget,
    field_tys: &FxHashMap<(LocalDefId, usize), P<Ty>>,
    tcx: TyCtxt<'_>,
    ast_to_hir: &AstToHir,
    plan: &SpecPlan,
) -> Option<FnPlan> {
    let field_ty = field_tys
        .get(&(target.struct_def, target.field.as_usize()))?
        .clone();
    let input = func.sig.decl.inputs.get(param_idx)?;
    let PatKind::Ident(_, param_ident, _) = input.pat.kind else {
        return None;
    };
    let body = func.body.as_deref()?;

    let mut checker = ParamUseChecker {
        param_name: param_ident.name,
        field_name: target.field_name,
        plan,
        tcx,
        ast_to_hir,
        ok: true,
    };
    checker.visit_block(body);
    checker.ok.then_some(FnPlan {
        param_idx,
        param_name: param_ident.name,
        field_name: target.field_name,
        field_ty,
    })
}

struct ParamUseChecker<'a, 'tcx> {
    param_name: Symbol,
    field_name: Symbol,
    plan: &'a SpecPlan,
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a AstToHir,
    ok: bool,
}

fn as_param_path(expr: &Expr, param_name: Symbol) -> bool {
    let expr = utils::ast::unwrap_paren(expr);
    matches!(&expr.kind, ExprKind::Path(None, path)
        if path.segments.len() == 1 && path.segments[0].ident.name == param_name)
}

// `(*s).field` with `s` being the param
fn as_param_deref_field(expr: &Expr, param_name: Symbol) -> Option<Ident> {
    let expr = utils::ast::unwrap_paren(expr);
    let ExprKind::Field(base, field_ident) = &expr.kind else {
        return None;
    };
    let base = utils::ast::unwrap_paren(base);
    let ExprKind::Unary(UnOp::Deref, inner) = &base.kind else {
        return None;
    };
    as_param_path(inner, param_name).then_some(*field_ident)
}

impl<'a> AstVisitor<'a> for ParamUseChecker<'_, '_> {
    fn visit_expr(&mut self, expr: &'a Expr) {
        // allowed context 1: `(*s).field` for the target field only
        if let Some(field_ident) = as_param_deref_field(expr, self.param_name) {
            if field_ident.name != self.field_name {
                self.ok = false;
            }
            return; // consumed; do not descend into the param path
        }
        // allowed context 2: `s.is_null()`
        if let ExprKind::MethodCall(call) = &expr.kind
            && call.seg.ident.name.as_str() == "is_null"
            && as_param_path(&call.receiver, self.param_name)
        {
            for arg in &call.args {
                self.visit_expr(arg);
            }
            return;
        }
        // allowed context 3: bare `s` forwarded to another selected target
        if let ExprKind::Call(callee, args) = &expr.kind {
            let callee_did = resolve_callee(self.tcx, self.ast_to_hir, callee);
            self.visit_expr(callee);
            for (i, arg) in args.iter().enumerate() {
                if as_param_path(arg, self.param_name) {
                    let forwarded =
                        callee_did.is_some_and(|did| self.plan.targets.contains_key(&(did, i)));
                    if !forwarded {
                        self.ok = false;
                    }
                    continue;
                }
                self.visit_expr(arg);
            }
            return;
        }
        // any other appearance of the bare param is unrewritable
        if as_param_path(expr, self.param_name) {
            self.ok = false;
            return;
        }
        ast_visit::walk_expr(self, expr);
    }
}

fn resolve_callee(tcx: TyCtxt<'_>, ast_to_hir: &AstToHir, callee: &Expr) -> Option<LocalDefId> {
    let hir_expr = ast_to_hir.get_expr(callee.id, tcx)?;
    let typeck = tcx.typeck(hir_expr.hir_id.owner);
    let ty::TyKind::FnDef(def_id, _) = typeck.expr_ty(hir_expr).kind() else {
        return None;
    };
    def_id.as_local()
}

struct SpecTransformVisitor<'a, 'tcx> {
    fn_plans: &'a FxHashMap<(LocalDefId, usize), FnPlan>,
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a AstToHir,
    // targets of the function currently being visited, keyed by param name
    current_fn: Option<FxHashMap<Symbol, &'a FnPlan>>,
    changed: bool,
}

impl MutVisitor for SpecTransformVisitor<'_, '_> {
    fn visit_item(&mut self, item: &mut Item) {
        let mut entered = false;
        if let ItemKind::Fn(func) = &mut item.kind
            && let Some(&did) = self.ast_to_hir.global_map.get(&item.id)
        {
            let mut by_name = FxHashMap::default();
            for (&(target_did, _), fn_plan) in self.fn_plans {
                if target_did != did {
                    continue;
                }
                // narrow the parameter type to a mut pointer to the field type
                let input = &mut func.sig.decl.inputs[fn_plan.param_idx];
                input.ty = P(Ty {
                    id: DUMMY_NODE_ID,
                    kind: TyKind::Ptr(MutTy {
                        ty: fn_plan.field_ty.clone(),
                        mutbl: Mutability::Mut,
                    }),
                    span: input.ty.span,
                    tokens: None,
                });
                by_name.insert(fn_plan.param_name, fn_plan);
                self.changed = true;
            }
            if !by_name.is_empty() {
                self.current_fn = Some(by_name);
                entered = true;
            }
        }
        mut_visit::walk_item(self, item);
        if entered {
            self.current_fn = None;
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        // children first: composed rewrites like `(*s).next` inside a call
        // argument settle before the argument itself is wrapped
        mut_visit::walk_expr(self, expr);
        self.rewrite_body_field_access(expr);
        self.rewrite_call_args(expr);
    }
}

impl SpecTransformVisitor<'_, '_> {
    // `(*s).field` -> `(*s)` inside a specialized function
    fn rewrite_body_field_access(&mut self, expr: &mut Expr) {
        let Some(params) = &self.current_fn else {
            return;
        };
        let ExprKind::Field(base, field_ident) = &expr.kind else {
            return;
        };
        let deref_base = utils::ast::unwrap_paren(base);
        let ExprKind::Unary(UnOp::Deref, inner) = &deref_base.kind else {
            return;
        };
        let inner = utils::ast::unwrap_paren(inner);
        let ExprKind::Path(None, path) = &inner.kind else {
            return;
        };
        if path.segments.len() != 1 {
            return;
        }
        let Some(fn_plan) = params.get(&path.segments[0].ident.name) else {
            return;
        };
        if field_ident.name != fn_plan.field_name {
            return;
        }
        let ExprKind::Field(base, _) = utils::ast::take_expr(expr).kind else { unreachable!() };
        *expr = *base;
        self.changed = true;
    }

    // rewrite arguments at specialized positions of calls to selected targets
    fn rewrite_call_args(&mut self, expr: &mut Expr) {
        let ExprKind::Call(callee, args) = &mut expr.kind else {
            return;
        };
        let Some(callee_did) = resolve_callee(self.tcx, self.ast_to_hir, callee) else {
            return;
        };
        for (i, arg) in args.iter_mut().enumerate() {
            let Some(fn_plan) = self.fn_plans.get(&(callee_did, i)) else {
                continue;
            };
            self.rewrite_arg(arg, fn_plan);
        }
    }

    fn rewrite_arg(&mut self, arg: &mut Expr, target: &FnPlan) {
        // forwarding: the caller's own specialized param passes through
        if let Some(params) = &self.current_fn
            && let ExprKind::Path(None, path) = &utils::ast::unwrap_paren(arg).kind
            && path.segments.len() == 1
            && params.contains_key(&path.segments[0].ident.name)
        {
            return;
        }
        // null literal keeps its shape with the new pointee type
        if is_null_literal(arg) {
            let ty_str = pprust::ty_to_string(&target.field_ty);
            *arg = utils::expr!("0 as *mut {}", ty_str);
            self.changed = true;
            return;
        }
        // general case: take the field address on the original argument
        let span = arg.span;
        let old = utils::ast::take_expr(arg);
        let deref = Expr {
            id: DUMMY_NODE_ID,
            kind: ExprKind::Unary(UnOp::Deref, P(old)),
            span,
            attrs: thin_vec![],
            tokens: None,
        };
        let field = Expr {
            id: DUMMY_NODE_ID,
            kind: ExprKind::Field(P(deref), Ident::new(target.field_name, span)),
            span,
            attrs: thin_vec![],
            tokens: None,
        };
        arg.kind = ExprKind::AddrOf(BorrowKind::Raw, Mutability::Mut, P(field));
        self.changed = true;
    }
}

// `0 as *mut T`, possibly through nested casts
fn is_null_literal(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Cast(inner, _) => is_null_literal(inner),
        ExprKind::Paren(inner) => is_null_literal(inner),
        ExprKind::Lit(lit) => lit.kind == token::LitKind::Integer && lit.symbol.as_str() == "0",
        _ => false,
    }
}
