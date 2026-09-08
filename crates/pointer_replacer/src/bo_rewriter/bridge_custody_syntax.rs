//! R231 test-instrument syntax custody; no model or production analysis facts.
//! Calls are direct AST call expressions. A callee path is syntax, never an
//! invented FnDef identity; method dispatch is outside this inventory.

use std::collections::{BTreeMap, BTreeSet};

use rustc_ast::{
    self as ast,
    visit::{self, Visitor},
};
use rustc_session::parse::ParseSess;
use rustc_span::{Span, edition::Edition};
use serde::{Deserialize, Serialize};

pub(crate) use super::delivery_custody::ByteSpan;

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Inventory {
    pub(crate) functions: Vec<Function>,
    pub(crate) calls: Vec<Call>,
    pub(crate) bindings: Vec<Binding>,
    pub(crate) scopes: Vec<Scope>,
    pub(crate) uses: Vec<BindingUse>,
    pub(crate) issues: Vec<String>,
}

/// An exact lexical occurrence, not a semantic liveness or execution claim.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BindingUse {
    pub(crate) binding_id: usize,
    pub(crate) span: ByteSpan,
    pub(crate) scope: usize,
    pub(crate) owner: String,
    pub(crate) context: UseContext,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum UseContext {
    PathRead,
    AddressOf,
    AssignmentTarget,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Function {
    pub(crate) owner: String,
    pub(crate) span: ByteSpan,
    pub(crate) parameters: Vec<Parameter>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Parameter {
    pub(crate) binding: String,
    pub(crate) index: usize,
    pub(crate) span: ByteSpan,
    pub(crate) type_text: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Scope {
    pub(crate) id: usize,
    pub(crate) owner: String,
    pub(crate) parent: Option<usize>,
    pub(crate) span: ByteSpan,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Binding {
    pub(crate) id: usize,
    pub(crate) owner: String,
    pub(crate) scope: usize,
    pub(crate) name: String,
    pub(crate) declaration_span: ByteSpan,
    pub(crate) binding_span: ByteSpan,
    pub(crate) init_span: Option<ByteSpan>,
    pub(crate) type_text: Option<String>,
    pub(crate) init_text: Option<String>,
    pub(crate) generated: Option<GeneratedKind>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum GeneratedKind {
    RawTemporary,
    C9Temporary,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Call {
    pub(crate) owner: String,
    pub(crate) scope: usize,
    pub(crate) ordinal: usize,
    pub(crate) span: ByteSpan,
    pub(crate) callee_text: String,
    pub(crate) callee_path: Option<String>,
    pub(crate) arguments: Vec<Argument>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Argument {
    pub(crate) span: ByteSpan,
    pub(crate) text: String,
    pub(crate) form: ArgumentForm,
    pub(crate) address_kind: Option<String>,
    pub(crate) address_mutable: Option<bool>,
    pub(crate) local_name: Option<String>,
    pub(crate) binding: Option<Binding>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum ArgumentForm {
    Path,
    AddrOfPath,
    Other,
}

struct LexicalScope {
    id: usize,
    names: BTreeMap<String, Option<usize>>,
    uncertain: bool,
}

#[derive(Default)]
struct PatternNames {
    names: Vec<rustc_span::Ident>,
    opaque: bool,
}

impl<'ast> Visitor<'ast> for PatternNames {
    fn visit_pat(&mut self, pattern: &'ast ast::Pat) {
        if let ast::PatKind::Ident(_, name, _) = &pattern.kind {
            self.names.push(*name);
        }
        self.opaque |= matches!(pattern.kind, ast::PatKind::MacCall(_));
        visit::walk_pat(self, pattern);
    }
}

fn unparen(mut expression: &ast::Expr) -> &ast::Expr {
    while let ast::ExprKind::Paren(inner) = &expression.kind {
        expression = inner;
    }
    expression
}

fn local_name(expression: &ast::Expr) -> Option<String> {
    let ast::ExprKind::Path(None, path) = &unparen(expression).kind else { return None };
    let [segment] = path.segments.as_slice() else { return None };
    segment
        .args
        .is_none()
        .then(|| segment.ident.name.to_string())
}

fn raw_type(mut ty: &ast::Ty) -> bool {
    while let ast::TyKind::Paren(inner) = &ty.kind {
        ty = inner;
    }
    matches!(ty.kind, ast::TyKind::Ptr(_))
}

fn explicit_type(ty: &ast::Ty) -> bool {
    struct Explicit(bool);
    impl<'ast> Visitor<'ast> for Explicit {
        fn visit_ty(&mut self, ty: &'ast ast::Ty) {
            self.0 &= !matches!(ty.kind, ast::TyKind::Infer);
            visit::walk_ty(self, ty);
        }
    }
    let mut visitor = Explicit(true);
    visitor.visit_ty(ty);
    visitor.0
}

struct InventoryVisitor<'source> {
    source: &'source str,
    start: u32,
    offsets: Vec<u32>,
    path: Vec<String>,
    owner: Option<String>,
    scopes: Vec<LexicalScope>,
    invalidated: BTreeSet<usize>,
    ordinals: BTreeMap<String, usize>,
    inventory: Inventory,
    error: Option<String>,
}

impl InventoryVisitor<'_> {
    fn range(&mut self, span: Span) -> ByteSpan {
        let lo = span
            .lo()
            .0
            .checked_sub(self.start)
            .and_then(|offset| self.offsets.get(offset as usize).copied());
        let hi = span
            .hi()
            .0
            .checked_sub(self.start)
            .and_then(|offset| self.offsets.get(offset as usize).copied());
        if let (Some(lo), Some(hi)) = (lo, hi)
            && lo <= hi
            && self.source.get(lo as usize..hi as usize).is_some()
        {
            return ByteSpan { lo, hi };
        }
        self.error
            .get_or_insert_with(|| "bridge custody span outside original source".to_owned());
        ByteSpan { lo: 0, hi: 0 }
    }

    fn text(&mut self, span: Span) -> String {
        let span = self.range(span);
        self.source[span.lo as usize..span.hi as usize].to_owned()
    }

    fn push_scope(&mut self, span: Span) {
        let Some(owner) = self.owner.clone() else { return };
        let id = self.inventory.scopes.len();
        let span = self.range(span);
        self.inventory.scopes.push(Scope {
            id,
            owner,
            parent: self.scopes.last().map(|scope| scope.id),
            span,
        });
        self.scopes.push(LexicalScope {
            id,
            names: BTreeMap::new(),
            uncertain: false,
        });
    }

    fn resolve_lexical(&self, name: &str) -> Option<Binding> {
        for scope in self.scopes.iter().rev() {
            if let Some(id) = scope.names.get(name) {
                return id.map(|id| self.inventory.bindings[id].clone());
            }
            if scope.uncertain {
                return None;
            }
        }
        None
    }

    fn resolve(&self, name: &str) -> Option<Binding> {
        self.resolve_lexical(name)
            .filter(|binding| !self.invalidated.contains(&binding.id))
    }

    fn record_use(&mut self, expression: &ast::Expr, context: UseContext) {
        let Some(name) = local_name(expression) else { return };
        let Some(binding) = self.resolve_lexical(&name) else { return };
        let Some(scope) = self.scopes.last().map(|scope| scope.id) else { return };
        let span = self.range(unparen(expression).span);
        self.inventory.uses.push(BindingUse {
            binding_id: binding.id,
            span,
            scope,
            owner: binding.owner,
            context,
        });
    }

    fn uncertain(&mut self, span: Span, reason: &str) {
        let Some(owner) = self.owner.clone() else { return };
        let span = self.range(span);
        for scope in &self.scopes {
            self.invalidated
                .extend(scope.names.values().filter_map(|id| *id));
        }
        if let Some(scope) = self.scopes.last_mut() {
            // A macro may introduce a shadow. Later explicit declarations can
            // establish new identities, but earlier names cannot be guessed
            // through this barrier. The issue also prevents interpreting an
            // absent use as proof of non-use.
            scope.names.clear();
            scope.uncertain = true;
            self.inventory
                .issues
                .push(format!("{reason}:{owner}:{}:scope={}", span.lo, scope.id));
        }
    }

    fn bind(
        &mut self,
        pattern: &ast::Pat,
        ty: Option<&ast::Ty>,
        init: Option<&ast::Expr>,
        span: Span,
    ) {
        let Some(owner) = self.owner.clone() else { return };
        let Some(scope) = self.scopes.last().map(|scope| scope.id) else { return };
        let mut names = PatternNames::default();
        names.visit_pat(pattern);
        if names.opaque {
            self.uncertain(pattern.span, "scope-uncertain-pattern-macro");
        }
        let mut leaf = pattern;
        while let ast::PatKind::Paren(inner) = &leaf.kind {
            leaf = inner;
        }
        // A whole tuple/struct annotation is never the individual binding's type.
        let direct = matches!(
            leaf.kind,
            ast::PatKind::Ident(ast::BindingMode::NONE, _, None)
        ) || matches!(
            leaf.kind,
            ast::PatKind::Ident(ast::BindingMode::MUT, _, None)
        );
        let mut seen = BTreeSet::new();
        for name in names.names {
            let name_text = name.name.to_string();
            if !seen.insert(name_text.clone()) {
                self.scopes
                    .last_mut()
                    .unwrap()
                    .names
                    .insert(name_text, None);
                continue;
            }
            let ty = direct.then_some(ty).flatten();
            let init = direct.then_some(init).flatten();
            // Generated-family tags describe typed syntax with an initializer;
            // the consumer must still validate that initializer and its exact
            // use at the intended call. A prefix alone is never a carrier.
            let typed_initializer = init.is_some() && ty.is_some_and(explicit_type);
            let generated = if typed_initializer && name_text.starts_with("__crat_c9_") {
                Some(GeneratedKind::C9Temporary)
            } else if typed_initializer
                && (name_text.starts_with("__crat_pair_raw_")
                    || name_text.starts_with("__crat_a5_raw_"))
                && ty.is_some_and(raw_type)
            {
                Some(GeneratedKind::RawTemporary)
            } else {
                None
            };
            let id = self.inventory.bindings.len();
            let binding = Binding {
                id,
                owner: owner.clone(),
                scope,
                name: name_text.clone(),
                declaration_span: self.range(span),
                binding_span: self.range(name.span),
                init_span: init.map(|init| self.range(init.span)),
                type_text: ty.map(|ty| self.text(ty.span)),
                init_text: init.map(|init| self.text(init.span)),
                generated,
            };
            self.inventory.bindings.push(binding);
            self.scopes
                .last_mut()
                .unwrap()
                .names
                .insert(name_text, Some(id));
        }
    }

    fn parameters(&mut self, inputs: &[ast::Param]) -> Vec<Parameter> {
        let mut parameters = Vec::new();
        for (index, parameter) in inputs.iter().enumerate() {
            let binding = match &parameter.pat.kind {
                ast::PatKind::Ident(_, name, None) => name.name.to_string(),
                _ => self.text(parameter.pat.span),
            };
            // Unannotated closure parameters have no original type bytes.
            let ty = (!parameter.ty.span.is_dummy()).then_some(&*parameter.ty);
            parameters.push(Parameter {
                binding,
                index,
                span: self.range(parameter.span),
                type_text: ty.map(|ty| self.text(ty.span)).unwrap_or_default(),
            });
            self.bind(&parameter.pat, ty, None, parameter.span);
        }
        parameters
    }

    fn function(&mut self, function: &ast::Fn, span: Span) {
        let previous_owner = self.owner.replace(self.path.join("::"));
        let previous_scopes = std::mem::take(&mut self.scopes);
        self.push_scope(span);
        let parameters = self.parameters(&function.sig.decl.inputs);
        let row = Function {
            owner: self.path.join("::"),
            span: self.range(span),
            parameters,
        };
        self.inventory.functions.push(row);
        if let Some(body) = &function.body {
            self.visit_block(body);
        }
        self.scopes = previous_scopes;
        self.owner = previous_owner;
    }

    fn argument(&mut self, expression: &ast::Expr) -> Argument {
        let expression_shape = unparen(expression);
        let (address_kind, address_mutable) = match &expression_shape.kind {
            ast::ExprKind::AddrOf(kind, mutable, _) => (
                Some(
                    match kind {
                        ast::BorrowKind::Ref => "ref",
                        ast::BorrowKind::Raw => "raw",
                    }
                    .to_owned(),
                ),
                Some(mutable.is_mut()),
            ),
            _ => (None, None),
        };
        let (form, name) = match &expression_shape.kind {
            ast::ExprKind::Path(..) => (ArgumentForm::Path, local_name(expression_shape)),
            ast::ExprKind::AddrOf(_, _, operand) if local_name(operand).is_some() => {
                (ArgumentForm::AddrOfPath, local_name(operand))
            }
            _ => (ArgumentForm::Other, None),
        };
        Argument {
            span: self.range(expression.span),
            text: self.text(expression.span),
            form,
            address_kind,
            address_mutable,
            binding: name.as_deref().and_then(|name| self.resolve(name)),
            local_name: name,
        }
    }

    fn call(
        &mut self,
        expression: &ast::Expr,
        callee: &ast::Expr,
        arguments: &[ast::ptr::P<ast::Expr>],
    ) {
        let Some(owner) = self.owner.clone() else {
            visit::walk_expr(self, expression);
            return;
        };
        let Some(scope) = self.scopes.last().map(|scope| scope.id) else { return };
        let ordinal = self.ordinals.entry(owner.clone()).or_default();
        let current_ordinal = *ordinal;
        *ordinal += 1;
        let callee_path = match &unparen(callee).kind {
            ast::ExprKind::Path(None, path) => Some(
                path.segments
                    .iter()
                    .filter(|segment| segment.ident.name != rustc_span::kw::PathRoot)
                    .map(|segment| segment.ident.name.to_string())
                    .collect::<Vec<_>>()
                    .join("::"),
            ),
            _ => None,
        };
        let mut row = Call {
            owner,
            scope,
            ordinal: current_ordinal,
            span: self.range(expression.span),
            callee_text: self.text(callee.span),
            callee_path,
            arguments: Vec::new(),
        };
        self.visit_expr(callee);
        for argument in arguments {
            row.arguments.push(self.argument(argument));
            self.visit_expr(argument);
        }
        self.inventory.calls.push(row);
    }

    fn condition(&mut self, expression: &ast::Expr) {
        match &expression.kind {
            ast::ExprKind::Let(pattern, initializer, ..) => {
                self.visit_expr(initializer);
                self.bind(pattern, None, Some(initializer), expression.span);
            }
            ast::ExprKind::Binary(operator, left, right)
                if operator.node == ast::BinOpKind::And =>
            {
                self.condition(left);
                self.condition(right);
            }
            ast::ExprKind::Paren(inner) => self.condition(inner),
            _ => self.visit_expr(expression),
        }
    }

    fn isolated_expression(&mut self, expression: &ast::Expr, kind: &str) {
        let at = self.range(expression.span).lo;
        self.path.push(format!("{kind}@{at}"));
        let previous_owner = self.owner.replace(self.path.join("::"));
        let previous_scopes = std::mem::take(&mut self.scopes);
        self.push_scope(expression.span);
        if let ast::ExprKind::Closure(closure) = &expression.kind {
            let parameters = self.parameters(&closure.fn_decl.inputs);
            let row = Function {
                owner: self.path.join("::"),
                span: self.range(expression.span),
                parameters,
            };
            self.inventory.functions.push(row);
            self.visit_expr(&closure.body);
        } else {
            visit::walk_expr(self, expression);
        }
        self.scopes = previous_scopes;
        self.owner = previous_owner;
        self.path.pop();
    }
}

impl<'ast> Visitor<'ast> for InventoryVisitor<'_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        if matches!(item.kind, ast::ItemKind::ForeignMod(_)) {
            visit::walk_item(self, item);
            return;
        }
        let at = self.range(item.span).lo;
        self.path.push(
            item.kind
                .ident()
                .map(|name| name.name.to_string())
                .unwrap_or_else(|| format!("item@{at}")),
        );
        if let ast::ItemKind::Fn(function) = &item.kind {
            self.function(function, item.span);
        } else {
            let owner = self.owner.take();
            let scopes = std::mem::take(&mut self.scopes);
            visit::walk_item(self, item);
            self.scopes = scopes;
            self.owner = owner;
        }
        self.path.pop();
    }

    fn visit_assoc_item(&mut self, item: &'ast ast::AssocItem, context: visit::AssocCtxt) {
        let at = self.range(item.span).lo;
        self.path.push(
            item.kind
                .ident()
                .map(|name| name.name.to_string())
                .unwrap_or_else(|| format!("associated@{at}")),
        );
        if let ast::AssocItemKind::Fn(function) = &item.kind {
            self.function(function, item.span);
        } else {
            visit::walk_assoc_item(self, item, context);
        }
        self.path.pop();
    }

    fn visit_foreign_item(&mut self, item: &'ast ast::ForeignItem) {
        if let ast::ForeignItemKind::Fn(function) = &item.kind {
            self.path.push(function.ident.name.to_string());
            self.function(function, item.span);
            self.path.pop();
        }
    }

    fn visit_block(&mut self, block: &'ast ast::Block) {
        if self.owner.is_none() {
            visit::walk_block(self, block);
            return;
        }
        self.push_scope(block.span);
        // Items are visible throughout their block, including before their text.
        for statement in &block.stmts {
            if let ast::StmtKind::Item(item) = &statement.kind
                && let Some(name) = item.kind.ident()
            {
                self.scopes
                    .last_mut()
                    .unwrap()
                    .names
                    .insert(name.name.to_string(), None);
            }
        }
        visit::walk_block(self, block);
        self.scopes.pop();
    }

    fn visit_local(&mut self, local: &'ast ast::Local) {
        if let Some(initializer) = local.kind.init() {
            self.visit_expr(initializer);
        }
        if let ast::LocalKind::InitElse(_, block) = &local.kind {
            self.visit_block(block);
        }
        // A let binding starts after its initializer and the diverging else arm.
        self.bind(
            &local.pat,
            local.ty.as_deref(),
            local.kind.init(),
            local.span,
        );
    }

    fn visit_stmt(&mut self, statement: &'ast ast::Stmt) {
        if matches!(statement.kind, ast::StmtKind::MacCall(_)) {
            self.uncertain(statement.span, "scope-uncertain-statement-macro");
        } else {
            visit::walk_stmt(self, statement);
        }
    }

    fn visit_arm(&mut self, arm: &'ast ast::Arm) {
        if self.owner.is_none() {
            visit::walk_arm(self, arm);
            return;
        }
        self.push_scope(arm.span);
        self.bind(&arm.pat, None, None, arm.pat.span);
        if let Some(guard) = &arm.guard {
            self.condition(guard);
        }
        if let Some(body) = &arm.body {
            self.visit_expr(body);
        }
        self.scopes.pop();
    }

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        match &expression.kind {
            ast::ExprKind::Path(..) => self.record_use(expression, UseContext::PathRead),
            ast::ExprKind::AddrOf(_, _, operand) => {
                if local_name(operand).is_some() {
                    self.record_use(operand, UseContext::AddressOf);
                } else {
                    self.visit_expr(operand);
                }
            }
            ast::ExprKind::Call(callee, arguments) => self.call(expression, callee, arguments),
            ast::ExprKind::Closure(_) => self.isolated_expression(expression, "closure"),
            ast::ExprKind::ConstBlock(_) => self.isolated_expression(expression, "const"),
            ast::ExprKind::Gen(..) => self.isolated_expression(expression, "coroutine"),
            ast::ExprKind::If(condition, body, otherwise) => {
                self.push_scope(expression.span);
                self.condition(condition);
                self.visit_block(body);
                if self.owner.is_some() {
                    self.scopes.pop();
                }
                if let Some(otherwise) = otherwise {
                    self.visit_expr(otherwise);
                }
            }
            ast::ExprKind::While(condition, body, _) => {
                self.push_scope(expression.span);
                self.condition(condition);
                self.visit_block(body);
                if self.owner.is_some() {
                    self.scopes.pop();
                }
            }
            ast::ExprKind::ForLoop {
                pat, iter, body, ..
            } => {
                self.visit_expr(iter);
                self.push_scope(expression.span);
                self.bind(pat, None, None, pat.span);
                self.visit_block(body);
                if self.owner.is_some() {
                    self.scopes.pop();
                }
            }
            ast::ExprKind::Assign(destination, value, _)
            | ast::ExprKind::AssignOp(_, destination, value) => {
                self.visit_expr(value);
                if let Some(name) = local_name(destination) {
                    self.record_use(destination, UseContext::AssignmentTarget);
                    if let Some(binding) = self.resolve_lexical(&name) {
                        self.invalidated.insert(binding.id);
                        let span = self.range(expression.span);
                        self.inventory.issues.push(format!(
                            "binding-reassigned:{}:{}:span={}..{}:scope={}",
                            binding.owner,
                            binding.id,
                            span.lo,
                            span.hi,
                            self.scopes
                                .last()
                                .map(|scope| scope.id)
                                .unwrap_or(binding.scope),
                        ));
                    }
                } else {
                    self.visit_expr(destination);
                }
            }
            ast::ExprKind::MacCall(_) => {
                self.uncertain(expression.span, "scope-uncertain-expression-macro")
            }
            _ => visit::walk_expr(self, expression),
        }
    }
}

pub(crate) fn inventory_source(name: &str, source: &str) -> Result<Inventory, String> {
    rustc_span::create_session_globals_then(Edition::Edition2018, &[], None, || {
        let psess = ParseSess::new(rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec());
        let krate = super::slice_use_inventory_tests::parse_crate(&psess, name, source)?;
        let files = psess.source_map().files();
        let file = files.first().ok_or("bridge custody parser source absent")?;
        // Same original-byte normalization as delivery_custody: rustc removes
        // a leading BOM and one byte from each CRLF pair before assigning spans.
        let bytes = source.as_bytes();
        let mut offset = if source.starts_with('\u{feff}') { 3 } else { 0 };
        let mut offsets = vec![offset as u32];
        while offset < bytes.len() {
            offset += if bytes[offset] == b'\r' && bytes.get(offset + 1) == Some(&b'\n') {
                2
            } else {
                1
            };
            offsets.push(
                u32::try_from(offset)
                    .map_err(|_| "bridge custody source exceeds byte-span range")?,
            );
        }
        if file
            .src
            .as_ref()
            .is_none_or(|normalized| normalized.len() + 1 != offsets.len())
        {
            return Err("unsupported bridge custody parser normalization".to_owned());
        }
        let mut visitor = InventoryVisitor {
            source,
            start: file.start_pos.0,
            offsets,
            path: Vec::new(),
            owner: None,
            scopes: Vec::new(),
            invalidated: BTreeSet::new(),
            ordinals: BTreeMap::new(),
            inventory: Inventory::default(),
            error: None,
        };
        visit::walk_crate(&mut visitor, &krate);
        if let Some(error) = visitor.error {
            return Err(error);
        }
        visitor
            .inventory
            .calls
            .sort_by_key(|call| (call.span.lo, call.span.hi));
        visitor
            .inventory
            .uses
            .sort_by_key(|usage| (usage.span.lo, usage.span.hi));
        visitor
            .inventory
            .functions
            .sort_by_key(|function| (function.span.lo, function.span.hi));
        Ok(visitor.inventory)
    })
}
