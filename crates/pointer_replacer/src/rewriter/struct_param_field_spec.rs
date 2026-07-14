//! applies the struct-param field specialization plan: narrows selected
//! struct-pointer parameters to field pointers, rewrites their body field
//! accesses, and updates every call site. edits are resolved per function
//! before any mutation; an unresolvable function drops out together with the
//! targets that forward into it (group-atomic, no partial rewrites).

use std::fmt::Write as _;

use rustc_ast::{
    mut_visit::{self, MutVisitor},
    ptr::P,
    token,
    visit::{self as ast_visit, Visitor as AstVisitor},
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::def::{DefKind, Res};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{Ident, Symbol, def_id::LocalDefId, sym};
use thin_vec::{ThinVec, thin_vec};
use utils::ir::AstToHir;

use crate::analyses::struct_param_field_spec::{SiteEmission, SpecPlan, SpecTarget};

// per-function rewrite instructions resolved during validation
#[derive(Clone)]
struct FnPlan {
    param_idx: usize,
    param_name: Symbol,
    field_name: Symbol,
    field_ty: P<Ty>,
    // the field's type spelled from its MIR type (`utils::ir::mir_ty_to_string`),
    // not the cloned AST type: alias-free (e.g. `[u64; 8]`, never a c2rust
    // typedef like `uint64_t`), so it type-checks in every module, including
    // ones that never import the struct's own module's aliases. used only for
    // guard-statement casts (wrapper lets, hoisted call-site guards); wrapper
    // and signature emission keep using `field_ty` (same-module, unaffected)
    field_mir_ty_str: String,
    mutbl: Mutability,
    // Some(new name) when the fn is c-exposed: rename to `{name}_field`, strip
    // abi attrs, emit an original-signature wrapper
    exposed_rename: Option<Symbol>,
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
    let exposed_renames: FxHashMap<LocalDefId, Symbol> = fn_plans
        .iter()
        .filter_map(|(&(did, _), fp)| fp.exposed_rename.map(|n| (did, n)))
        .collect();
    let mut visitor = SpecTransformVisitor {
        fn_plans: &fn_plans,
        exposed_renames: &exposed_renames,
        plan,
        tcx,
        ast_to_hir,
        current_fn: None,
        current_fn_did: None,
        pending_renames: FxHashMap::default(),
        guard_counter: 0,
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

// all function item names in the crate, for `_field` collision checks
//
// intentionally name-only and module-blind: a same-named fn in another
// module registers as a collision and skips the target (fails closed).
// call-site retargeting resolves callees by defid, never by name, so a
// false collision can only suppress a rewrite, not misdirect one.
fn crate_fn_names(krate: &Crate) -> FxHashSet<Symbol> {
    let mut names = FxHashSet::default();
    walk_items(&krate.items, &mut |item| {
        if let ItemKind::Fn(func) = &item.kind {
            names.insert(func.ident.name);
        }
    });
    names
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
    let fn_names = crate_fn_names(krate);

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
            let exposed_rename = if target.exposed {
                let new_name = Symbol::intern(&format!("{}_field", func.ident.name));
                if fn_names.contains(&new_name) {
                    dropped.insert(key);
                    continue;
                }
                Some(new_name)
            } else {
                None
            };
            let ok = resolve_fn_plan(
                func,
                param_idx,
                target,
                field_tys,
                tcx,
                ast_to_hir,
                plan,
                exposed_rename,
            )
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

    // audit every call site into a still-live target: a specialized-position
    // argument must have a known, hoistable emission (forwarding shape,
    // null literal, or a site_emissions entry that is not Guarded-in-a-
    // while-head); violations drop the callee target before the cascade.
    // own_param_names mirrors the transform phase's `current_fn` map: a bare
    // path only counts as forwarding when it names the enclosing fn's own
    // already-specialized parameter, not any arbitrary local variable
    let mut own_param_names: FxHashMap<LocalDefId, FxHashSet<Symbol>> = FxHashMap::default();
    for (&(fn_did, _), fn_plan) in &fn_plans {
        own_param_names
            .entry(fn_did)
            .or_default()
            .insert(fn_plan.param_name);
    }
    let mut auditor = CallSiteAuditor {
        tcx,
        ast_to_hir,
        plan,
        own_param_names: &own_param_names,
        current_fn: None,
        in_while_head: false,
        violations: FxHashSet::default(),
    };
    walk_items(&krate.items, &mut |item| {
        auditor.visit_item(item);
    });
    dropped.extend(auditor.violations);

    // cascade both directions over forwarding edges (from, to):
    // - a forwarder into a dropped callee cannot be rewritten either, since
    //   its own call site into `to` is now meaningless
    // - a callee whose only justification for a call site was Forward(from)
    //   loses that justification when `from` drops; conservatively drop `to`
    //   too rather than re-deriving whether another class still covers the
    //   site (group-atomicity: no partial rewrites)
    loop {
        let before = dropped.len();
        for (from, to) in &plan.forwards {
            if dropped.contains(to) {
                dropped.insert(*from);
            }
            if dropped.contains(from) {
                dropped.insert(*to);
            }
        }
        if dropped.len() == before {
            break;
        }
    }
    fn_plans.retain(|key, _| !dropped.contains(key));
    fn_plans
}

// the field's type spelled from its MIR type, not the AST: alias-free (e.g.
// `[u64; 8]`, never a c2rust typedef like `uint64_t`), so it type-checks in
// any module. the struct is guaranteed non-generic by the detector (see
// `struct_pointee` in analyses/struct_param_field_spec.rs, which only admits
// candidates with empty generic args), so `args` is always empty
fn field_mir_ty_string(
    tcx: TyCtxt<'_>,
    struct_def: LocalDefId,
    field: rustc_abi::FieldIdx,
) -> String {
    let struct_ty = tcx.type_of(struct_def).skip_binder();
    let ty::TyKind::Adt(adt_def, args) = struct_ty.kind() else {
        unreachable!("struct_def target must resolve to an Adt")
    };
    let field_ty = adt_def.non_enum_variant().fields[field].ty(tcx, args);
    utils::ir::mir_ty_to_string(field_ty, tcx)
}

#[allow(clippy::too_many_arguments)]
fn resolve_fn_plan(
    func: &Fn,
    param_idx: usize,
    target: &SpecTarget,
    field_tys: &FxHashMap<(LocalDefId, usize), P<Ty>>,
    tcx: TyCtxt<'_>,
    ast_to_hir: &AstToHir,
    plan: &SpecPlan,
    exposed_rename: Option<Symbol>,
) -> Option<FnPlan> {
    let field_ty = field_tys
        .get(&(target.struct_def, target.field.as_usize()))?
        .clone();
    let field_mir_ty_str = field_mir_ty_string(tcx, target.struct_def, target.field);
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
        field_mir_ty_str,
        mutbl: target.mutbl,
        exposed_rename,
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

// read-only, resolution-phase visitor: audits every call into a selected
// target. each specialized-position argument must have a known, hoistable
// emission (forwarding shape, null literal, or a site_emissions entry that
// is Direct, or Guarded outside a while-loop condition); anything else
// drops the callee target. the bidirectional cascade (run by the caller,
// after this visitor) then propagates the drop
struct CallSiteAuditor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a AstToHir,
    plan: &'a SpecPlan,
    // fn did -> names of that fn's own already-specialized parameters, used
    // to recognize genuine forwarding shapes (mirrors the transform phase's
    // `current_fn` map)
    own_param_names: &'a FxHashMap<LocalDefId, FxHashSet<Symbol>>,
    // the enclosing fn's did, set by visit_item
    current_fn: Option<LocalDefId>,
    // true while visiting a `while` condition subtree
    in_while_head: bool,
    violations: FxHashSet<(LocalDefId, usize)>,
}

impl<'a> AstVisitor<'a> for CallSiteAuditor<'_, '_> {
    fn visit_item(&mut self, item: &'a Item) {
        if matches!(item.kind, ItemKind::Fn(_)) {
            let outer = self.current_fn;
            self.current_fn = self.ast_to_hir.global_map.get(&item.id).copied();
            ast_visit::walk_item(self, item);
            self.current_fn = outer;
            return;
        }
        ast_visit::walk_item(self, item);
    }

    fn visit_expr(&mut self, expr: &'a Expr) {
        if let ExprKind::While(cond, body, _) = &expr.kind {
            let outer = self.in_while_head;
            self.in_while_head = true;
            self.visit_expr(cond);
            self.in_while_head = outer;
            self.visit_block(body);
            return;
        }
        if let ExprKind::Call(callee, args) = &expr.kind {
            self.audit_call(expr, callee, args);
        }
        ast_visit::walk_expr(self, expr);
    }
}

impl CallSiteAuditor<'_, '_> {
    fn audit_call(&mut self, call_expr: &Expr, callee: &Expr, args: &[P<Expr>]) {
        let Some(callee_did) = resolve_callee(self.tcx, self.ast_to_hir, callee) else {
            return;
        };
        let Some(current_fn) = self.current_fn else {
            return;
        };
        for (i, arg) in args.iter().enumerate() {
            let key = (callee_did, i);
            if !self.plan.targets.contains_key(&key) {
                continue;
            }
            if self.arg_is_hoistable(current_fn, call_expr, arg, i) {
                continue;
            }
            self.violations.insert(key);
        }
    }

    // forwarding shape or null literal need no site_emissions entry; else
    // look up the entry recorded by the detector for this call site
    fn arg_is_hoistable(
        &self,
        current_fn: LocalDefId,
        call_expr: &Expr,
        arg: &Expr,
        arg_idx: usize,
    ) -> bool {
        if is_null_literal(arg) {
            return true;
        }
        if let ExprKind::Path(None, path) = &utils::ast::unwrap_paren(arg).kind
            && path.segments.len() == 1
            && self
                .own_param_names
                .get(&current_fn)
                .is_some_and(|names| names.contains(&path.segments[0].ident.name))
        {
            // bare path naming the enclosing fn's own already-specialized
            // parameter: forwarding shape (matches the rewriter's
            // `rewrite_arg` forwarding check, which is name-based)
            return true;
        }
        match self.lookup_emission(current_fn, call_expr, arg_idx) {
            Some(SiteEmission::Direct) => true,
            Some(SiteEmission::Guarded) => !self.in_while_head,
            None => false,
        }
    }

    // span matching: the detector recorded the MIR call terminator's span;
    // match the AST call expression's span by equality first (established
    // crat idiom, same compilation session, real output confirms exact
    // equality holds), falling back to containment, then to a scan over all
    // entries for this (fn, arg_idx) as a last resort; no match is missing
    // (fail closed)
    fn lookup_emission(
        &self,
        current_fn: LocalDefId,
        call_expr: &Expr,
        arg_idx: usize,
    ) -> Option<SiteEmission> {
        let span = call_expr.span;
        if let Some(&em) = self.plan.site_emissions.get(&(current_fn, span, arg_idx)) {
            return Some(em);
        }
        self.plan
            .site_emissions
            .iter()
            .find(|((fn_did, recorded, idx), _)| {
                *fn_did == current_fn
                    && *idx == arg_idx
                    && (span.contains(*recorded) || recorded.contains(span))
            })
            .map(|(_, em)| *em)
    }
}

struct SpecTransformVisitor<'a, 'tcx> {
    fn_plans: &'a FxHashMap<(LocalDefId, usize), FnPlan>,
    exposed_renames: &'a FxHashMap<LocalDefId, Symbol>,
    plan: &'a SpecPlan,
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a AstToHir,
    // targets of the function currently being visited, keyed by param name
    current_fn: Option<FxHashMap<Symbol, &'a FnPlan>>,
    // did of the function currently being visited, tracked for every fn
    // (not just target fns), used to key site_emissions lookups
    current_fn_did: Option<LocalDefId>,
    // arg NodeId -> hoisted field-pointer local name, consulted by
    // rewrite_arg before the inline Direct fallback
    pending_renames: FxHashMap<NodeId, Symbol>,
    // per-function counter for unique `__crat_g{n}` names
    guard_counter: u32,
    changed: bool,
}

// a hoisted null-checked guard for one guarded-emission call argument
struct Hoist {
    arg_node_id: NodeId,
    name: Symbol,
    stmts: [Stmt; 2],
}

impl MutVisitor for SpecTransformVisitor<'_, '_> {
    fn flat_map_item(&mut self, mut item: P<Item>) -> smallvec::SmallVec<[P<Item>; 1]> {
        // a `use` item resolving to a renamed (exposed) fn: the wrapper still
        // exists under the original name (build_wrapper preserves it), so the
        // original import keeps working, but call sites in this module that
        // got retargeted to the `_field` name (rewrite_call_args) also need
        // that name in scope. emit an additional sibling import for it rather
        // than renaming in place
        if let Some(sibling) = self.sibling_field_use(&item) {
            let mut items = smallvec::SmallVec::new();
            items.push(item);
            items.push(sibling);
            return items;
        }

        let mut entered = false;
        // (orig-signature snapshot, new name) for wrapper emission
        let mut wrapper_info: Option<(P<Item>, Symbol)> = None;
        // current_fn_did is tracked for every fn item, not just target fns:
        // the hoist scan needs it to key site_emissions lookups regardless
        // of whether the enclosing fn itself specializes a param
        let outer_fn_did = self.current_fn_did;
        let mut entered_fn_did = false;

        if matches!(item.kind, ItemKind::Fn(_))
            && let Some(&did) = self.ast_to_hir.global_map.get(&item.id)
        {
            self.current_fn_did = Some(did);
            self.guard_counter = 0;
            entered_fn_did = true;
            let mut by_name = FxHashMap::default();
            let mut rename: Option<Symbol> = None;
            for (&(target_did, _), fn_plan) in self.fn_plans {
                if target_did != did {
                    continue;
                }
                rename = rename.or(fn_plan.exposed_rename);
                by_name.insert(fn_plan.param_name, fn_plan);
            }
            if let Some(new_name) = rename {
                // snapshot the original item (name, attrs, signature) before mutation
                wrapper_info = Some((item.clone(), new_name));
            }
            let ItemKind::Fn(func) = &mut item.kind else { unreachable!() };
            for fn_plan in by_name.values() {
                // narrow the parameter type to a pointer to the field type
                let input = &mut func.sig.decl.inputs[fn_plan.param_idx];
                input.ty = P(Ty {
                    id: DUMMY_NODE_ID,
                    kind: TyKind::Ptr(MutTy {
                        ty: fn_plan.field_ty.clone(),
                        mutbl: fn_plan.mutbl,
                    }),
                    span: input.ty.span,
                    tokens: None,
                });
                self.changed = true;
            }
            if let Some((_, new_name)) = &wrapper_info {
                func.ident.name = *new_name;
                item.attrs.retain(|attr| {
                    !attr.has_name(sym::export_name) && !attr.has_name(sym::no_mangle)
                });
            }
            if !by_name.is_empty() {
                self.current_fn = Some(by_name);
                entered = true;
            }
        }

        let mut items = mut_visit::walk_flat_map_item(self, item);
        if entered {
            self.current_fn = None;
        }
        if entered_fn_did {
            self.current_fn_did = outer_fn_did;
        }
        if let Some((orig_item, new_name)) = wrapper_info {
            items.push(self.build_wrapper(orig_item, new_name));
        }
        items
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        // children first: composed rewrites like `(*s).next` inside a call
        // argument settle before the argument itself is wrapped
        mut_visit::walk_expr(self, expr);
        self.rewrite_body_field_access(expr);
        self.rewrite_call_args(expr);
    }

    fn visit_block(&mut self, block: &mut Block) {
        let mut new_stmts: ThinVec<Stmt> = ThinVec::with_capacity(block.stmts.len());
        for stmt in block.stmts.drain(..) {
            // pass 1: read-only scan for guarded-emission call arguments in
            // this statement, allocating hoisted names and building the
            // two-let capture/guard pair for each
            let hoists = self.collect_hoists(&stmt);
            for hoist in &hoists {
                self.pending_renames.insert(hoist.arg_node_id, hoist.name);
            }
            for hoist in hoists {
                let [capture, guard] = hoist.stmts;
                new_stmts.push(capture);
                new_stmts.push(guard);
            }
            // pass 2: mutate the statement normally; rewrite_arg consults
            // pending_renames first, replacing hoisted args with the
            // captured field-pointer name
            new_stmts.extend(self.flat_map_stmt(stmt));
        }
        block.stmts = new_stmts;
        self.visit_id(&mut block.id);
        self.visit_span(&mut block.span);
    }
}

impl SpecTransformVisitor<'_, '_> {
    // if `item` is a `use` item resolving (via HIR) to a fn that got renamed
    // to `{name}_field`, build an additional sibling `use` item importing
    // that new name, so cross-module call sites retargeted by
    // rewrite_call_args (which rewrites the call-expr path segment, not the
    // module's imports) resolve. the original `use` item is left untouched:
    // the wrapper still exists under the original name (build_wrapper), so
    // the pre-existing import keeps working for callers of the ABI-preserving
    // wrapper
    fn sibling_field_use(&self, item: &Item) -> Option<P<Item>> {
        let ItemKind::Use(tree) = &item.kind else {
            return None;
        };
        let hir_item = self.ast_to_hir.get_item(item.id, self.tcx)?;
        let hir::ItemKind::Use(path, _) = &hir_item.kind else {
            return None;
        };
        let Res::Def(DefKind::Fn, def_id) = path.res.value_ns? else {
            return None;
        };
        let def_id = def_id.as_local()?;
        let new_name = *self.exposed_renames.get(&def_id)?;
        let mut prefix = pprust::path_to_string(&tree.prefix);
        // drop the original (last) segment, replaced with `new_name` below
        if let Some(idx) = prefix.rfind("::") {
            prefix.truncate(idx);
        } else {
            return None;
        }
        let mut sibling = P(utils::item!("use {prefix}::{new_name};"));
        sibling.vis = item.vis.clone();
        Some(sibling)
    }

    // original name/attrs/signature; body forwards to the renamed function,
    // converting each specialized param to a null-guarded field address
    fn build_wrapper(&mut self, mut wrapper: P<Item>, new_name: Symbol) -> P<Item> {
        let ItemKind::Fn(func) = &mut wrapper.kind else { unreachable!() };
        let did = self.ast_to_hir.global_map[&wrapper.id];
        // each specialized param's null-guarded conversion is hoisted into its own
        // `let` statement ahead of the call, instead of being embedded inline in the
        // call argument. this lets the downstream borrow-promotion pass transform the
        // guard and the field-address branch together, under one context, instead of
        // two independent call-argument-scoped rewrite rules colliding on the same
        // source variable (see wrapper-io-diagnosis.md)
        let mut lets = Vec::new();
        let mut call = format!("{new_name}(");
        for (i, param) in func.sig.decl.inputs.iter().enumerate() {
            let PatKind::Ident(_, ident, _) = param.pat.kind else { unreachable!() };
            let x = ident.name;
            if let Some(fn_plan) = self.fn_plans.get(&(did, i)) {
                let m = match fn_plan.mutbl {
                    Mutability::Mut => "mut",
                    Mutability::Not => "const",
                };
                let mm = match fn_plan.mutbl {
                    Mutability::Mut => "mut ",
                    Mutability::Not => "",
                };
                // module-independent spelling: this guard may be printed into
                // a module that never imports the field's declaring module's
                // c2rust type aliases (see field_mir_ty_string)
                let ty = &fn_plan.field_mir_ty_str;
                let fld = fn_plan.field_name;
                let local = format!("__crat_{x}_field");
                lets.push(utils::stmt!(
                    "let {local} = if {x}.is_null() {{ 0 as *{m} {ty} }} else {{ &{mm}(*{x}).{fld} as *{m} {ty} }};",
                ));
                write!(call, "{local}, ").unwrap();
            } else {
                write!(call, "{x}, ").unwrap();
            }
        }
        call.push(')');
        let body = func.body.as_mut().unwrap();
        body.stmts.clear();
        body.stmts.extend(lets);
        body.stmts.push(utils::stmt!("{call}"));
        self.changed = true;
        wrapper
    }

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
        if let Some(new_name) = self.exposed_renames.get(&callee_did)
            && let ExprKind::Path(None, path) = &mut callee.kind
            && let Some(seg) = path.segments.last_mut()
        {
            seg.ident.name = *new_name;
            self.changed = true;
        }
        for (i, arg) in args.iter_mut().enumerate() {
            let Some(fn_plan) = self.fn_plans.get(&(callee_did, i)) else {
                continue;
            };
            self.rewrite_arg(arg, fn_plan);
        }
    }

    fn rewrite_arg(&mut self, arg: &mut Expr, target: &FnPlan) {
        // a hoisted guard was emitted for this exact argument node ahead of
        // the enclosing statement: swap in the captured field-pointer name
        if let Some(name) = self.pending_renames.remove(&arg.id) {
            *arg = utils::expr!("{}", name);
            self.changed = true;
            return;
        }
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
            let m = match target.mutbl {
                Mutability::Mut => "mut",
                Mutability::Not => "const",
            };
            let ty_str = pprust::ty_to_string(&target.field_ty);
            *arg = utils::expr!("0 as *{} {}", m, ty_str);
            self.changed = true;
            return;
        }
        // by this point the auditor has guaranteed every remaining
        // specialized-position argument reached a Direct emission; a
        // Guarded or missing entry here would mean a hoist should have
        // fired above (unreachable if the auditor is sound)
        debug_assert!(
            self.direct_emission_at(arg),
            "rewrite_arg reached the inline fallback for a non-Direct site"
        );
        // general case (Direct emission): take the field address inline on
        // the original argument
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
        let reference = Expr {
            id: DUMMY_NODE_ID,
            kind: ExprKind::AddrOf(BorrowKind::Ref, target.mutbl, P(field)),
            span,
            attrs: thin_vec![],
            tokens: None,
        };
        let ptr_ty = P(Ty {
            id: DUMMY_NODE_ID,
            kind: TyKind::Ptr(MutTy {
                ty: target.field_ty.clone(),
                mutbl: target.mutbl,
            }),
            span,
            tokens: None,
        });
        arg.kind = ExprKind::Cast(P(reference), ptr_ty);
        self.changed = true;
    }

    // read-only scan of one (not-yet-mutated) statement: finds call exprs
    // into selected targets whose specialized-position arguments need a
    // hoisted guard (not a forwarding shape, not a null literal, and the
    // site_emissions lookup says Guarded); returns (arg node id, arg
    // pretty-printed, target) triples in source order, deferring name
    // allocation and stmt-building to the caller (which owns &mut self)
    fn find_guarded_args(&self, stmt: &Stmt) -> Vec<(NodeId, String, FnPlan)> {
        let mut found = Vec::new();
        let mut finder = HoistFinder {
            visitor: self,
            found: &mut found,
        };
        finder.visit_stmt(stmt);
        found
    }

    // allocates unique names and builds the two-let capture/guard pair for
    // every guarded argument found in `stmt`
    fn collect_hoists(&mut self, stmt: &Stmt) -> Vec<Hoist> {
        self.find_guarded_args(stmt)
            .into_iter()
            .map(|(arg_node_id, e, target)| {
                let n = self.guard_counter;
                self.guard_counter += 1;
                let g = format!("__crat_g{n}");
                let gf = format!("__crat_g{n}_field");
                let m = match target.mutbl {
                    Mutability::Mut => "mut",
                    Mutability::Not => "const",
                };
                let mm = match target.mutbl {
                    Mutability::Mut => "mut ",
                    Mutability::Not => "",
                };
                // module-independent spelling: this guard is hoisted at the
                // call site, which may live in a module that never imports
                // the callee field's declaring module's c2rust type aliases
                let ty = &target.field_mir_ty_str;
                let fld = target.field_name;
                let capture = utils::stmt!("let {g} = {e};");
                let guard = utils::stmt!(
                    "let {gf} = if {g}.is_null() {{ 0 as *{m} {ty} }} else {{ &{mm}(*{g}).{fld} as *{m} {ty} }};",
                );
                Hoist {
                    arg_node_id,
                    name: Symbol::intern(&gf),
                    stmts: [capture, guard],
                }
            })
            .collect()
    }

    // true, purely for the debug_assert, when `arg` (post pending_renames
    // check, post forwarding check, post null-literal check) is confirmed
    // Direct by the site_emissions lookup at the enclosing call
    fn direct_emission_at(&self, arg: &Expr) -> bool {
        let Some(current_fn) = self.current_fn_did else {
            return false;
        };
        // the enclosing call expr's span is arg's own span's superset in
        // practice, but we don't have the call expr here; fall back to a
        // scan over site_emissions for any Direct entry whose span contains
        // this argument's span (mirrors the auditor's containment fallback)
        self.plan
            .site_emissions
            .iter()
            .any(|((fn_did, span, _), em)| {
                *fn_did == current_fn && span.contains(arg.span) && *em == SiteEmission::Direct
            })
    }

    // span matching identical to the auditor's: equality against the AST
    // call expression's span first, then containment either direction
    fn lookup_emission(
        &self,
        current_fn: LocalDefId,
        call_expr: &Expr,
        arg_idx: usize,
    ) -> Option<SiteEmission> {
        let span = call_expr.span;
        if let Some(&em) = self.plan.site_emissions.get(&(current_fn, span, arg_idx)) {
            return Some(em);
        }
        self.plan
            .site_emissions
            .iter()
            .find(|((fn_did, recorded, idx), _)| {
                *fn_did == current_fn
                    && *idx == arg_idx
                    && (span.contains(*recorded) || recorded.contains(span))
            })
            .map(|(_, em)| *em)
    }
}

// read-only visitor run once per (not-yet-mutated) statement by
// find_guarded_args; descends into every expression at this statement's own
// level, including nested calls (e.g. a guarded call as another call's
// argument), so those are still found. crucially does NOT descend into
// nested blocks (if/while/loop bodies, etc.): the outer visit_block will
// separately scan each nested block's own statements when it recurses
// there, so descending here would double-hoist the same call. purely
// read-only: name allocation and stmt-building happen afterward in
// collect_hoists, which owns &mut self
struct HoistFinder<'a, 'b, 'tcx> {
    visitor: &'a SpecTransformVisitor<'b, 'tcx>,
    found: &'a mut Vec<(NodeId, String, FnPlan)>,
}

impl<'a> AstVisitor<'a> for HoistFinder<'_, '_, '_> {
    fn visit_expr(&mut self, expr: &'a Expr) {
        if let ExprKind::Call(callee, args) = &expr.kind {
            self.visit_call(expr, callee, args);
        }
        ast_visit::walk_expr(self, expr);
    }

    // stop at nested block boundaries: visit_block (the outer
    // SpecTransformVisitor's) handles each nested block independently
    fn visit_block(&mut self, _block: &'a Block) {}
}

impl HoistFinder<'_, '_, '_> {
    fn visit_call(&mut self, call_expr: &Expr, callee: &Expr, args: &[P<Expr>]) {
        let v = self.visitor;
        let Some(callee_did) = resolve_callee(v.tcx, v.ast_to_hir, callee) else {
            return;
        };
        let Some(current_fn) = v.current_fn_did else {
            return;
        };
        for (i, arg) in args.iter().enumerate() {
            let Some(fn_plan) = v.fn_plans.get(&(callee_did, i)) else {
                continue;
            };
            if self.is_forwarding_or_null(arg) {
                continue;
            }
            if v.lookup_emission(current_fn, call_expr, i) != Some(SiteEmission::Guarded) {
                continue;
            }
            self.found
                .push((arg.id, pprust::expr_to_string(arg), fn_plan.clone()));
        }
    }

    fn is_forwarding_or_null(&self, arg: &Expr) -> bool {
        if is_null_literal(arg) {
            return true;
        }
        if let Some(params) = &self.visitor.current_fn
            && let ExprKind::Path(None, path) = &utils::ast::unwrap_paren(arg).kind
            && path.segments.len() == 1
            && params.contains_key(&path.segments[0].ident.name)
        {
            return true;
        }
        false
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
