use rustc_ast::{
    self as ast,
    mut_visit::{self, MutVisitor},
    visit::{self, Visitor},
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;
use rustc_session::lint::{Level, builtin::UNSAFE_OP_IN_UNSAFE_FN};
use rustc_span::{
    Span,
    def_id::{DefId, LocalDefId},
    sym,
};

use super::PrepareError;

fn called_function(
    expr: &ast::Expr,
    mapping: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<DefId> {
    let expr = mapping.get_expr(expr.id, tcx)?;
    let typeck = tcx.typeck(expr.hir_id.owner);
    match expr.kind {
        rustc_hir::ExprKind::Call(callee, _) => {
            if let rustc_middle::ty::FnDef(def_id, _) = typeck.expr_ty(callee).kind() {
                Some(*def_id)
            } else {
                None
            }
        }
        rustc_hir::ExprKind::MethodCall(..) => typeck.type_dependent_def_id(expr.hir_id),
        _ => None,
    }
}

struct Facts<'a, 'tcx> {
    mapping: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    function: Option<LocalDefId>,
    calls: FxHashMap<LocalDefId, FxHashSet<LocalDefId>>,
    unsafe_functions: FxHashSet<LocalDefId>,
    unsafe_operations: FxHashSet<LocalDefId>,
    functions_with_blocks: FxHashSet<LocalDefId>,
    error: Option<PrepareError>,
}

impl<'ast> Visitor<'ast> for Facts<'_, '_> {
    fn visit_anon_const(&mut self, constant: &'ast ast::AnonConst) {
        let previous = self.function.take();
        visit::walk_anon_const(self, constant);
        self.function = previous;
    }

    fn visit_ty(&mut self, ty: &'ast ast::Ty) {
        let previous = self.function.take();
        visit::walk_ty(self, ty);
        self.function = previous;
    }

    fn visit_item(&mut self, item: &'ast ast::Item) {
        let previous = self.function.take();
        visit::walk_item(self, item);
        self.function = previous;
    }

    fn visit_fn(&mut self, kind: visit::FnKind<'ast>, _: Span, id: ast::NodeId) {
        let visit::FnKind::Fn(context, _, function) = kind else {
            visit::walk_fn(self, kind);
            return;
        };
        let previous = self.function.take();
        if matches!(context, visit::FnCtxt::Free)
            && function.ident.name != sym::main
            && matches!(function.sig.header.constness, ast::Const::No)
            && function.body.is_some()
        {
            if let Some(def_id) = self.mapping.global_map.get(&id).copied() {
                self.function = Some(def_id);
                self.calls.entry(def_id).or_default();
                if matches!(function.sig.header.safety, ast::Safety::Unsafe(_)) {
                    self.unsafe_functions.insert(def_id);
                }
            } else {
                self.error = Some(PrepareError::MissingMapping {
                    construct: format!("function `{}`", function.ident),
                });
            }
        }
        if let Some(body) = &function.body {
            self.visit_block(body);
        }
        self.function = previous;
    }

    fn visit_expr(&mut self, expr: &'ast ast::Expr) {
        if let ast::ExprKind::ConstBlock(constant) = &expr.kind {
            self.visit_expr(&constant.value);
            return;
        }
        if let Some(caller) = self.function
            && matches!(
                expr.kind,
                ast::ExprKind::Call(..) | ast::ExprKind::MethodCall(..)
            )
            && let Some(callee) = called_function(expr, self.mapping, self.tcx)
        {
            if let Some(callee) = callee.as_local() {
                self.calls.entry(caller).or_default().insert(callee);
            }
            if self.tcx.fn_sig(callee).skip_binder().safety().is_unsafe() {
                self.unsafe_operations.insert(caller);
            }
        }
        visit::walk_expr(self, expr);
    }

    fn visit_block(&mut self, block: &'ast ast::Block) {
        if let Some(function) = self.function
            && matches!(block.rules, ast::BlockCheckMode::Unsafe(..))
        {
            self.functions_with_blocks.insert(function);
        }
        visit::walk_block(self, block);
    }
}

#[derive(Default)]
struct UnsafeOperations(bool);

impl utils::unsafety::UnsafetyHandler for UnsafeOperations {
    fn handle_unsafety(&mut self, _: utils::unsafety::UnsafeOpKind, _: Span, _: TyCtxt<'_>) {
        self.0 = true;
    }
}

pub(super) fn normalize(
    krate: &mut ast::Crate,
    mapping: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Result<(), PrepareError> {
    let mut facts = Facts {
        mapping,
        tcx,
        function: None,
        calls: FxHashMap::default(),
        unsafe_functions: FxHashSet::default(),
        unsafe_operations: FxHashSet::default(),
        functions_with_blocks: FxHashSet::default(),
        error: None,
    };
    facts.visit_crate(krate);
    if let Some(error) = facts.error {
        return Err(error);
    }
    let eligible = facts.calls.keys().copied().collect::<FxHashSet<_>>();
    for callees in facts.calls.values_mut() {
        callees.retain(|callee| eligible.contains(callee));
    }
    // Collect compiler facts first: unsafety checking consumes THIR, including nested bodies.
    let mut functions = eligible.iter().copied().collect::<Vec<_>>();
    functions.sort_by_key(|def_id| def_id.local_def_index.as_u32());
    for function in &functions {
        if !facts.functions_with_blocks.contains(function) {
            continue;
        }
        if tcx.thir_body(*function).is_err() {
            tcx.dcx().abort_if_errors();
        }
        let mut operations = UnsafeOperations::default();
        utils::unsafety::check_unsafety(*function, &mut operations, tcx);
        if operations.0 {
            facts.unsafe_operations.insert(*function);
        }
    }
    facts.unsafe_functions.extend(&facts.unsafe_operations);
    let callers = utils::graph::inverse(&facts.calls);
    let mut pending = facts.unsafe_functions.iter().copied().collect::<Vec<_>>();
    while let Some(callee) = pending.pop() {
        for caller in &callers[&callee] {
            if facts.unsafe_functions.insert(*caller) {
                pending.push(*caller);
            }
        }
    }
    for function in functions {
        let needs_context = facts.unsafe_operations.contains(&function)
            || facts.calls[&function]
                .iter()
                .any(|callee| facts.unsafe_functions.contains(callee));
        if needs_context
            && matches!(
                tcx.lint_level_at_node(
                    UNSAFE_OP_IN_UNSAFE_FN,
                    tcx.local_def_id_to_hir_id(function)
                )
                .level,
                Level::Deny | Level::Forbid
            )
        {
            return Err(PrepareError::UnsafeFunctionLint {
                function_name: tcx.def_path_str(function),
            });
        }
    }
    Normalizer {
        mapping,
        tcx,
        eligible: &eligible,
        unsafe_functions: &facts.unsafe_functions,
        normalize_blocks: false,
        unsafe_context: false,
    }
    .visit_crate(krate);
    Ok(())
}

struct Normalizer<'a, 'tcx> {
    mapping: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    eligible: &'a FxHashSet<LocalDefId>,
    unsafe_functions: &'a FxHashSet<LocalDefId>,
    normalize_blocks: bool,
    unsafe_context: bool,
}

impl MutVisitor for Normalizer<'_, '_> {
    fn visit_anon_const(&mut self, constant: &mut ast::AnonConst) {
        let previous = (self.normalize_blocks, self.unsafe_context);
        self.normalize_blocks = false;
        self.unsafe_context = false;
        mut_visit::walk_anon_const(self, constant);
        (self.normalize_blocks, self.unsafe_context) = previous;
    }

    fn visit_item(&mut self, item: &mut ast::Item) {
        let previous = (self.normalize_blocks, self.unsafe_context);
        self.normalize_blocks = false;
        self.unsafe_context = false;
        mut_visit::walk_item(self, item);
        (self.normalize_blocks, self.unsafe_context) = previous;
    }

    fn visit_fn(&mut self, kind: mut_visit::FnKind<'_>, span: Span, id: ast::NodeId) {
        let mut_visit::FnKind::Fn(context, visibility, function) = kind else {
            mut_visit::walk_fn(self, kind);
            return;
        };
        let previous = (self.normalize_blocks, self.unsafe_context);
        self.normalize_blocks = false;
        self.unsafe_context = false;
        let def_id = self.mapping.global_map.get(&id);
        let normalize = def_id.is_some_and(|def_id| self.eligible.contains(def_id));
        if def_id.is_some_and(|def_id| self.unsafe_functions.contains(def_id)) {
            function.sig.header.safety = ast::Safety::Unsafe(span);
        }
        let body = function.body.take();
        mut_visit::walk_fn(
            self,
            mut_visit::FnKind::Fn(context, visibility, &mut *function),
        );
        self.normalize_blocks = normalize;
        self.unsafe_context = matches!(function.sig.header.safety, ast::Safety::Unsafe(_));
        if let Some(mut body) = body {
            self.visit_block(&mut body);
            function.body = Some(body);
        }
        (self.normalize_blocks, self.unsafe_context) = previous;
    }

    fn visit_ty(&mut self, ty: &mut ast::Ty) {
        let previous = (self.normalize_blocks, self.unsafe_context);
        self.normalize_blocks = false;
        self.unsafe_context = false;
        mut_visit::walk_ty(self, ty);
        (self.normalize_blocks, self.unsafe_context) = previous;
    }

    fn visit_block(&mut self, block: &mut ast::Block) {
        let previous = self.unsafe_context;
        if matches!(block.rules, ast::BlockCheckMode::Unsafe(..)) {
            if self.normalize_blocks {
                block.rules = ast::BlockCheckMode::Default;
            } else {
                self.unsafe_context = true;
            }
        }
        mut_visit::walk_block(self, block);
        self.unsafe_context = previous;
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        if let ast::ExprKind::ConstBlock(constant) = &mut expr.kind {
            self.visit_expr(&mut constant.value);
            return;
        }
        let needs_wrapper = !self.unsafe_context
            && matches!(
                expr.kind,
                ast::ExprKind::Call(..) | ast::ExprKind::MethodCall(..)
            )
            && called_function(expr, self.mapping, self.tcx)
                .and_then(|def_id| def_id.as_local())
                .is_some_and(|def_id| self.unsafe_functions.contains(&def_id));
        mut_visit::walk_expr(self, expr);
        if needs_wrapper {
            let mut wrapped = utils::expr!("unsafe {{ () }}");
            let ast::ExprKind::Block(block, _) = &mut wrapped.kind else { unreachable!() };
            block.stmts[0].kind =
                ast::StmtKind::Expr(rustc_ast::ptr::P(utils::ast::take_expr(expr)));
            *expr = wrapped;
        }
    }
}
