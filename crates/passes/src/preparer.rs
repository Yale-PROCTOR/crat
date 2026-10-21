use std::{
    collections::HashMap,
    fmt, fs,
    path::{Path, PathBuf},
};

use rustc_ast::{
    self as ast,
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor as _},
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir,
    def::{DefKind, Namespace, Res},
    intravisit,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::{
    Span, Symbol,
    def_id::{DefId, LocalDefId},
    sym,
};
use thin_vec::thin_vec;

#[cfg(test)]
mod tests;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrepareError {
    UnsupportedAsyncFunction {
        function_name: String,
    },
    UnsupportedPrelude {
        construct: String,
    },
    ScopedDependency {
        static_def_id: LocalDefId,
        static_name: String,
        dependency_def_id: LocalDefId,
        dependency_name: String,
    },
    MissingMapping {
        construct: String,
    },
}

impl fmt::Display for PrepareError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedAsyncFunction { function_name } => write!(
                formatter,
                "direct async function `{function_name}` is unsupported"
            ),
            Self::UnsupportedPrelude { construct } => {
                write!(formatter, "unsupported prelude configuration: {construct}")
            }
            Self::ScopedDependency {
                static_name,
                dependency_name,
                ..
            } => write!(
                formatter,
                "local static `{static_name}` depends on scoped binding `{dependency_name}`"
            ),
            Self::MissingMapping { construct } => {
                write!(formatter, "missing compiler mapping for {construct}")
            }
        }
    }
}

impl std::error::Error for PrepareError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreparationResult {
    pub code: String,
    pub requires_proctor_libc: bool,
}

#[derive(Debug)]
pub enum PreparationPublishError {
    Dependency { manifest: PathBuf, cause: String },
    Source { source: PathBuf, cause: String },
}

impl fmt::Display for PreparationPublishError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Dependency { manifest, cause } => write!(
                formatter,
                "failed to ensure proctor-libc dependency in {}: {cause}",
                manifest.display()
            ),
            Self::Source { source, cause } => write!(
                formatter,
                "failed to write prepared source {}: {cause}",
                source.display()
            ),
        }
    }
}

impl std::error::Error for PreparationPublishError {}

impl PreparationResult {
    pub fn publish(self, source: &Path, manifest: &Path) -> Result<(), PreparationPublishError> {
        self.publish_with(
            source,
            manifest,
            utils::dependency::ensure_crates_io_dependency,
            |source, code| fs::write(source, code).map_err(|error| error.to_string()),
        )
    }

    fn publish_with(
        self,
        source: &Path,
        manifest: &Path,
        ensure_dependency: impl FnOnce(&Path, &str, &str) -> Result<(), String>,
        write: impl FnOnce(&Path, String) -> Result<(), String>,
    ) -> Result<(), PreparationPublishError> {
        if self.requires_proctor_libc {
            ensure_dependency(manifest, "proctor-libc", "0.3.0").map_err(|cause| {
                PreparationPublishError::Dependency {
                    manifest: manifest.to_owned(),
                    cause,
                }
            })?;
        }
        write(source, self.code).map_err(|cause| PreparationPublishError::Source {
            source: source.to_owned(),
            cause,
        })
    }
}

fn validate_supported_input(krate: &ast::Crate) -> Result<(), PrepareError> {
    struct SupportedInputVisitor {
        error: Option<PrepareError>,
    }

    impl<'ast> visit::Visitor<'ast> for SupportedInputVisitor {
        fn visit_attribute(&mut self, attribute: &'ast ast::Attribute) {
            if self.error.is_none() && attribute.has_name(sym::no_implicit_prelude) {
                self.error = Some(PrepareError::UnsupportedPrelude {
                    construct: "`#[no_implicit_prelude]`".to_owned(),
                });
            }
        }

        fn visit_item(&mut self, item: &'ast ast::Item) {
            if self.error.is_some() {
                return;
            }
            if !item.span.is_dummy()
                && item
                    .attrs
                    .iter()
                    .any(|attribute| attribute.has_name(sym::prelude_import))
            {
                self.error = Some(PrepareError::UnsupportedPrelude {
                    construct: "source-authored `#[prelude_import]`".to_owned(),
                });
                return;
            }
            visit::walk_item(self, item);
        }

        fn visit_fn(&mut self, kind: visit::FnKind<'ast>, span: Span, node_id: ast::NodeId) {
            if self.error.is_some() {
                return;
            }
            if let visit::FnKind::Fn(_, _, function) = kind
                && function.sig.header.coroutine_kind.is_some()
            {
                self.error = Some(PrepareError::UnsupportedAsyncFunction {
                    function_name: function.ident.name.as_str().to_owned(),
                });
                return;
            }
            visit::walk_fn(self, kind);
            let _ = (span, node_id);
        }
    }

    let mut visitor = SupportedInputVisitor { error: None };
    visitor.visit_crate(krate);
    visitor.error.map_or(Ok(()), Err)
}

#[derive(Clone, Debug)]
struct Lift {
    node_id: ast::NodeId,
    def_id: LocalDefId,
    original_name: Symbol,
    anchor: ast::NodeId,
    scopes: Vec<hir::HirId>,
}

#[derive(Clone, Debug)]
struct LocalImport {
    scope: hir::HirId,
    name: Symbol,
    target: DefId,
    import_def_id: LocalDefId,
}

fn imported_module(path: &hir::UsePath<'_>) -> Option<DefId> {
    path.segments.last().and_then(|segment| match segment.res {
        Res::Def(DefKind::Mod, definition) => Some(definition),
        _ => None,
    })
}

struct Discovery<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a utils::ir::AstToHir,
    anchor: ast::NodeId,
    function_depth: usize,
    blocks: Vec<hir::HirId>,
    lifts: Vec<Lift>,
    local_imports: Vec<LocalImport>,
    error: Option<PrepareError>,
}

impl<'a, 'tcx> Discovery<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, ast_to_hir: &'a utils::ir::AstToHir) -> Self {
        Self {
            tcx,
            ast_to_hir,
            anchor: ast::DUMMY_NODE_ID,
            function_depth: 0,
            blocks: vec![],
            lifts: vec![],
            local_imports: vec![],
            error: None,
        }
    }

    fn discover_crate(&mut self, krate: &ast::Crate) {
        self.discover_module(&krate.items);
    }

    fn discover_module(&mut self, items: &[P<ast::Item>]) {
        let old_anchor = self.anchor;
        let old_depth = self.function_depth;
        self.function_depth = 0;
        for item in items {
            self.anchor = item.id;
            self.visit_item(item);
            if self.error.is_some() {
                break;
            }
        }
        self.anchor = old_anchor;
        self.function_depth = old_depth;
    }

    fn mapped_item(
        &mut self,
        item: &ast::Item,
        description: String,
    ) -> Option<&'tcx hir::Item<'tcx>> {
        let Some(def_id) = self.ast_to_hir.global_map.get(&item.id).copied() else {
            self.error = Some(PrepareError::MissingMapping {
                construct: description,
            });
            return None;
        };
        Some(self.tcx.hir_expect_item(def_id))
    }

    fn collect_local_import(&mut self, item: &ast::Item) {
        let Some(scope) = self.blocks.last().copied() else {
            return;
        };
        let Some(hir_item) = self.mapped_item(item, "local import".to_owned()) else {
            return;
        };
        let import_def_id = hir_item.owner_id.def_id;
        let hir::ItemKind::Use(path, kind) = hir_item.kind else {
            return;
        };
        match kind {
            hir::UseKind::Single(name) => {
                for target in [path.res.value_ns, path.res.type_ns]
                    .into_iter()
                    .flatten()
                    .filter_map(|resolution| resolution.opt_def_id())
                {
                    if self.local_imports.iter().any(|import| {
                        import.import_def_id == import_def_id && import.target == target
                    }) {
                        continue;
                    }
                    self.local_imports.push(LocalImport {
                        scope,
                        name: name.name,
                        target,
                        import_def_id,
                    });
                }
            }
            hir::UseKind::Glob => {
                if let Some(module) = imported_module(path) {
                    let children = if let Some(local) = module.as_local() {
                        self.tcx
                            .module_children_local(local)
                            .iter()
                            .collect::<Vec<_>>()
                    } else {
                        self.tcx.module_children(module).iter().collect::<Vec<_>>()
                    };
                    self.local_imports
                        .extend(children.into_iter().filter_map(|child| {
                            child.res.opt_def_id().map(|target| LocalImport {
                                scope,
                                name: child.ident.name,
                                target,
                                import_def_id,
                            })
                        }));
                }
            }
            hir::UseKind::ListStem => {}
        }
    }
}

impl<'ast> visit::Visitor<'ast> for Discovery<'_, '_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        if self.error.is_some() {
            return;
        }
        match &item.kind {
            ast::ItemKind::Mod(_, _, ast::ModKind::Loaded(items, ..)) => {
                let Some(_) = self.mapped_item(item, "module".to_owned()) else {
                    return;
                };
                self.discover_module(items);
            }
            ast::ItemKind::Static(box ast::StaticItem { ident, .. }) => {
                if self.function_depth == 0 {
                    return;
                }
                let Some(hir_item) = self.mapped_item(item, format!("local static `{ident}`"))
                else {
                    return;
                };
                let hir::ItemKind::Static(_, hir_ident, ..) = hir_item.kind else {
                    self.error = Some(PrepareError::MissingMapping {
                        construct: format!("local static `{ident}`"),
                    });
                    return;
                };
                self.lifts.push(Lift {
                    node_id: item.id,
                    def_id: hir_item.owner_id.def_id,
                    original_name: hir_ident.name,
                    anchor: self.anchor,
                    scopes: self.blocks.clone(),
                });
            }
            ast::ItemKind::Use(_) if self.function_depth > 0 => {
                self.collect_local_import(item);
                visit::walk_item(self, item);
            }
            _ => visit::walk_item(self, item),
        }
    }

    fn visit_fn(&mut self, kind: visit::FnKind<'ast>, span: Span, node_id: ast::NodeId) {
        self.function_depth += 1;
        visit::walk_fn(self, kind);
        self.function_depth -= 1;
        let _ = (span, node_id);
    }

    fn visit_block(&mut self, block: &'ast ast::Block) {
        let Some(scope) = self.ast_to_hir.local_map.get(&block.id).copied() else {
            self.error = Some(PrepareError::MissingMapping {
                construct: "lexical block scope".to_owned(),
            });
            return;
        };
        self.blocks.push(scope);
        visit::walk_block(self, block);
        self.blocks.pop();
    }
}

#[derive(Default)]
struct BinderInventory {
    counts: FxHashMap<Symbol, usize>,
    occupied: FxHashSet<Symbol>,
}

impl BinderInventory {
    fn add(&mut self, name: Symbol) {
        *self.counts.entry(name).or_default() += 1;
        self.occupied.insert(name);
    }
}

struct BinderCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    inventory: BinderInventory,
    items: FxHashSet<LocalDefId>,
    foreign_items: FxHashSet<LocalDefId>,
    patterns: FxHashSet<hir::HirId>,
    generic_params: FxHashSet<LocalDefId>,
    glob_bindings: FxHashSet<(LocalDefId, Symbol)>,
}

impl<'tcx> BinderCollector<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            inventory: BinderInventory::default(),
            items: FxHashSet::default(),
            foreign_items: FxHashSet::default(),
            patterns: FxHashSet::default(),
            generic_params: FxHashSet::default(),
            glob_bindings: FxHashSet::default(),
        }
    }

    fn add_variant_constructor(&mut self, variant: &hir::Variant<'_>) {
        if variant.data.ctor().is_some() {
            self.inventory.add(variant.ident.name);
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for BinderCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        let first = self.items.insert(item.owner_id.def_id);
        if first {
            match item.kind {
                hir::ItemKind::Static(_, ident, ..)
                | hir::ItemKind::Const(ident, ..)
                | hir::ItemKind::Fn { ident, .. } => self.inventory.add(ident.name),
                hir::ItemKind::Struct(ident, _, data) => {
                    if data.ctor().is_some() {
                        self.inventory.add(ident.name);
                    }
                }
                hir::ItemKind::Enum(_, _, definition) => {
                    for variant in definition.variants {
                        self.add_variant_constructor(variant);
                    }
                }
                hir::ItemKind::Use(path, hir::UseKind::Single(ident)) => {
                    if !self
                        .tcx
                        .hir_attrs(item.hir_id())
                        .iter()
                        .any(|attribute| attribute.has_name(sym::prelude_import))
                        && path.res.value_ns.is_some()
                    {
                        self.inventory.add(ident.name);
                    }
                }
                hir::ItemKind::Use(path, hir::UseKind::Glob) => {
                    if !self
                        .tcx
                        .hir_attrs(item.hir_id())
                        .iter()
                        .any(|attribute| attribute.has_name(sym::prelude_import))
                        && let Some(module) = imported_module(path)
                    {
                        let children = if let Some(local) = module.as_local() {
                            self.tcx
                                .module_children_local(local)
                                .iter()
                                .collect::<Vec<_>>()
                        } else {
                            self.tcx.module_children(module).iter().collect::<Vec<_>>()
                        };
                        for child in children {
                            if child.res.ns() == Some(Namespace::ValueNS)
                                && self
                                    .glob_bindings
                                    .insert((item.owner_id.def_id, child.ident.name))
                            {
                                self.inventory.add(child.ident.name);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        intravisit::walk_item(self, item);
    }

    fn visit_foreign_item(&mut self, item: &'tcx hir::ForeignItem<'tcx>) {
        if self.foreign_items.insert(item.owner_id.def_id)
            && matches!(
                item.kind,
                hir::ForeignItemKind::Fn(..) | hir::ForeignItemKind::Static(..)
            )
        {
            self.inventory.add(item.ident.name);
        }
        intravisit::walk_foreign_item(self, item);
    }

    fn visit_pat(&mut self, pattern: &'tcx hir::Pat<'tcx>) {
        if let hir::PatKind::Binding(_, canonical_id, ident, _) = pattern.kind
            && self.patterns.insert(canonical_id)
        {
            self.inventory.add(ident.name);
        }
        intravisit::walk_pat(self, pattern);
    }

    fn visit_generic_param(&mut self, parameter: &'tcx hir::GenericParam<'tcx>) {
        if matches!(parameter.kind, hir::GenericParamKind::Const { .. })
            && self.generic_params.insert(parameter.def_id)
        {
            self.inventory.add(parameter.name.ident().name);
        }
        intravisit::walk_generic_param(self, parameter);
    }
}

fn binder_inventory(tcx: TyCtxt<'_>) -> BinderInventory {
    let mut collector = BinderCollector::new(tcx);
    tcx.hir_visit_all_item_likes_in_crate(&mut collector);
    collector.inventory
}

fn implicit_prelude_module(tcx: TyCtxt<'_>) -> Option<DefId> {
    tcx.hir_free_items().find_map(|item_id| {
        let item = tcx.hir_item(item_id);
        if !tcx
            .hir_attrs(item.hir_id())
            .iter()
            .any(|attribute| attribute.has_name(sym::prelude_import))
        {
            return None;
        }
        let hir::ItemKind::Use(path, hir::UseKind::Glob) = item.kind else {
            return None;
        };
        imported_module(path)
    })
}

fn prelude_names(tcx: TyCtxt<'_>) -> FxHashSet<Symbol> {
    let names: FxHashSet<Symbol> = implicit_prelude_module(tcx)
        .map(|module| {
            let children = if let Some(local) = module.as_local() {
                tcx.module_children_local(local).iter().collect::<Vec<_>>()
            } else {
                tcx.module_children(module).iter().collect::<Vec<_>>()
            };
            children
                .into_iter()
                .filter(|child| child.res.ns() == Some(Namespace::ValueNS))
                .map(|child| child.ident.name)
                .collect()
        })
        .unwrap_or_default();
    names
}

fn allocated_names(
    lifts: &[Lift],
    inventory: &BinderInventory,
    tcx: TyCtxt<'_>,
) -> FxHashMap<LocalDefId, Symbol> {
    let mut result = FxHashMap::default();
    let mut allocated = FxHashSet::default();
    let prelude = prelude_names(tcx);
    for lift in lifts {
        let collides = inventory
            .counts
            .get(&lift.original_name)
            .copied()
            .unwrap_or_default()
            > 1
            || prelude.contains(&lift.original_name);
        if !collides {
            continue;
        }
        for suffix in 0_usize..=usize::MAX {
            let candidate = Symbol::intern(&format!("{}_{suffix}", lift.original_name));
            if !inventory.occupied.contains(&candidate)
                && !allocated.contains(&candidate)
                && !prelude.contains(&candidate)
            {
                result.insert(lift.def_id, candidate);
                allocated.insert(candidate);
                break;
            }
        }
    }
    result
}

fn is_inside_definition(mut definition: LocalDefId, ancestor: LocalDefId, tcx: TyCtxt<'_>) -> bool {
    loop {
        if definition == ancestor {
            return true;
        }
        let Some(parent) = tcx.opt_local_parent(definition) else {
            return false;
        };
        definition = parent;
    }
}

fn is_module_owned(mut definition: LocalDefId, tcx: TyCtxt<'_>) -> bool {
    loop {
        let Some(parent) = tcx.opt_local_parent(definition) else {
            return true;
        };
        match tcx.def_kind(parent) {
            DefKind::Fn | DefKind::AssocFn | DefKind::Closure => return false,
            _ => definition = parent,
        }
    }
}

struct DependencyVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a utils::ir::AstToHir,
    lift: &'a Lift,
    lifted: &'a FxHashSet<LocalDefId>,
    local_imports: &'a [LocalImport],
    error: Option<PrepareError>,
}

impl DependencyVisitor<'_, '_> {
    fn reject(&mut self, dependency: LocalDefId, name: Symbol) {
        self.error = Some(PrepareError::ScopedDependency {
            static_def_id: self.lift.def_id,
            static_name: self.lift.original_name.as_str().to_owned(),
            dependency_def_id: dependency,
            dependency_name: name.as_str().to_owned(),
        });
    }
}

impl<'ast> visit::Visitor<'ast> for DependencyVisitor<'_, '_> {
    fn visit_path(&mut self, path: &'ast ast::Path) {
        if self.error.is_some() {
            return;
        }
        for segment in &path.segments {
            let Some(hir_segment) = self.ast_to_hir.get_path_segment(segment.id, self.tcx) else {
                self.error = Some(PrepareError::MissingMapping {
                    construct: format!(
                        "segment `{}` of path `{}` in local static `{}`",
                        segment.ident,
                        pprust::path_to_string(path),
                        self.lift.original_name
                    ),
                });
                return;
            };
            let Some(definition) = hir_segment.res.opt_def_id() else {
                continue;
            };
            let nearest_import = self
                .local_imports
                .iter()
                .filter(|import| import.name == segment.ident.name && import.target == definition)
                .filter_map(|import| {
                    self.lift
                        .scopes
                        .iter()
                        .position(|scope| *scope == import.scope)
                        .map(|depth| (depth, import))
                })
                .max_by_key(|(depth, _)| *depth)
                .map(|(_, import)| import);
            if let Some(import) = nearest_import {
                self.reject(import.import_def_id, import.name);
                return;
            }
            if let Some(local) = definition.as_local()
                && !self.lifted.contains(&local)
                && !is_inside_definition(local, self.lift.def_id, self.tcx)
                && !is_module_owned(local, self.tcx)
            {
                self.reject(local, segment.ident.name);
                return;
            }
        }
        visit::walk_path(self, path);
    }
}

fn validate_dependencies(
    krate: &ast::Crate,
    lifts: &[Lift],
    local_imports: &[LocalImport],
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Result<(), PrepareError> {
    let lifted = lifts
        .iter()
        .map(|lift| lift.def_id)
        .collect::<FxHashSet<_>>();
    let by_node = lifts
        .iter()
        .map(|lift| (lift.node_id, lift))
        .collect::<FxHashMap<_, _>>();
    struct StaticFinder<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ast_to_hir: &'a utils::ir::AstToHir,
        by_node: &'a FxHashMap<ast::NodeId, &'a Lift>,
        lifted: &'a FxHashSet<LocalDefId>,
        local_imports: &'a [LocalImport],
        error: Option<PrepareError>,
    }
    impl<'ast> visit::Visitor<'ast> for StaticFinder<'_, '_> {
        fn visit_item(&mut self, item: &'ast ast::Item) {
            if self.error.is_some() {
                return;
            }
            let Some(lift) = self.by_node.get(&item.id).copied() else {
                visit::walk_item(self, item);
                return;
            };
            let ast::ItemKind::Static(box ast::StaticItem { ty, expr, .. }) = &item.kind else {
                unreachable!()
            };
            let mut visitor = DependencyVisitor {
                tcx: self.tcx,
                ast_to_hir: self.ast_to_hir,
                lift,
                lifted: self.lifted,
                local_imports: self.local_imports,
                error: None,
            };
            visitor.visit_ty(ty);
            if visitor.error.is_none()
                && let Some(expr) = expr
            {
                visitor.visit_expr(expr);
            }
            self.error = visitor.error;
        }
    }
    let mut finder = StaticFinder {
        tcx,
        ast_to_hir,
        by_node: &by_node,
        lifted: &lifted,
        local_imports,
        error: None,
    };
    finder.visit_crate(krate);
    finder.error.map_or(Ok(()), Err)
}

fn validate_use_mappings(
    krate: &ast::Crate,
    lifts: &[Lift],
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Result<(), PrepareError> {
    let targets = lifts
        .iter()
        .map(|lift| lift.def_id)
        .collect::<FxHashSet<_>>();

    struct HirUses<'tcx> {
        tcx: TyCtxt<'tcx>,
        targets: FxHashSet<LocalDefId>,
        expressions: FxHashSet<(LocalDefId, hir::HirId)>,
        inline_asm: FxHashSet<(LocalDefId, Span)>,
    }
    impl<'tcx> intravisit::Visitor<'tcx> for HirUses<'tcx> {
        type NestedFilter = nested_filter::OnlyBodies;

        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.tcx
        }

        fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
            if let hir::ExprKind::Path(path) = expression.kind
                && let Res::Def(DefKind::Static { .. }, definition) = self
                    .tcx
                    .typeck(expression.hir_id.owner)
                    .qpath_res(&path, expression.hir_id)
                && let Some(local) = definition.as_local()
                && self.targets.contains(&local)
            {
                self.expressions.insert((local, expression.hir_id));
            }
            intravisit::walk_expr(self, expression);
        }

        fn visit_inline_asm(&mut self, asm: &'tcx hir::InlineAsm<'tcx>, id: hir::HirId) {
            for (operand, span) in asm.operands {
                if let hir::InlineAsmOperand::SymStatic { def_id, .. } = operand
                    && let Some(local) = def_id.as_local()
                    && self.targets.contains(&local)
                {
                    self.inline_asm.insert((local, *span));
                }
            }
            intravisit::walk_inline_asm(self, asm, id);
        }
    }
    let mut hir_uses = HirUses {
        tcx,
        targets: targets.clone(),
        expressions: FxHashSet::default(),
        inline_asm: FxHashSet::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut hir_uses);

    struct AstUses<'a> {
        ast_to_hir: &'a utils::ir::AstToHir,
        targets: &'a FxHashSet<LocalDefId>,
        counts: FxHashMap<LocalDefId, usize>,
    }
    impl<'ast> visit::Visitor<'ast> for AstUses<'_> {
        fn visit_path(&mut self, path: &'ast ast::Path) {
            if let Some(Res::Def(DefKind::Static { .. }, definition)) =
                self.ast_to_hir.path_span_to_res.get(&path.span)
                && let Some(local) = definition.as_local()
                && self.targets.contains(&local)
            {
                *self.counts.entry(local).or_default() += 1;
            }
            visit::walk_path(self, path);
        }
    }
    let mut ast_uses = AstUses {
        ast_to_hir,
        targets: &targets,
        counts: FxHashMap::default(),
    };
    ast_uses.visit_crate(krate);

    for lift in lifts {
        let hir_count = hir_uses
            .expressions
            .iter()
            .filter(|(definition, _)| *definition == lift.def_id)
            .count()
            + hir_uses
                .inline_asm
                .iter()
                .filter(|(definition, _)| *definition == lift.def_id)
                .count();
        let ast_count = ast_uses
            .counts
            .get(&lift.def_id)
            .copied()
            .unwrap_or_default();
        if hir_count != ast_count {
            return Err(PrepareError::MissingMapping {
                construct: format!("use of local static `{}`", lift.original_name),
            });
        }
    }
    Ok(())
}

struct RewriteVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a utils::ir::AstToHir,
    names: &'a FxHashMap<LocalDefId, Symbol>,
}

impl MutVisitor for RewriteVisitor<'_, '_> {
    fn visit_item(&mut self, item: &mut ast::Item) {
        if let Some(def_id) = self.ast_to_hir.global_map.get(&item.id)
            && let Some(name) = self.names.get(def_id)
            && let ast::ItemKind::Static(box ast::StaticItem { ident, .. }) = &mut item.kind
        {
            let original = ident.name;
            ident.name = *name;
            if let Some(position) = item
                .attrs
                .iter()
                .position(|attribute| attribute.has_name(sym::no_mangle))
            {
                let span = item.attrs[position].span;
                item.attrs[position] = ast::attr::mk_attr_name_value_str(
                    &self.tcx.sess.psess.attr_id_generator,
                    ast::AttrStyle::Outer,
                    ast::Safety::Default,
                    sym::export_name,
                    original,
                    span,
                );
            }
        }
        mut_visit::walk_item(self, item);
    }

    fn visit_path(&mut self, path: &mut ast::Path) {
        if let Some(Res::Def(DefKind::Static { .. }, definition)) =
            self.ast_to_hir.path_span_to_res.get(&path.span)
            && let Some(local) = definition.as_local()
            && let Some(name) = self.names.get(&local)
            && let Some(segment) = path.segments.last_mut()
        {
            segment.ident.name = *name;
        }
        mut_visit::walk_path(self, path);
    }

    fn visit_expr(&mut self, expression: &mut ast::Expr) {
        mut_visit::walk_expr(self, expression);
        if let ast::ExprKind::Match(_, arms, _) = &mut expression.kind {
            for arm in arms {
                let Some(body) = arm.body.as_mut() else {
                    continue;
                };
                if matches!(body.kind, ast::ExprKind::Block(..)) {
                    continue;
                }
                let span = body.span;
                let tail = body.clone();
                *body = P(ast::Expr {
                    id: ast::DUMMY_NODE_ID,
                    kind: ast::ExprKind::Block(
                        P(ast::Block {
                            stmts: thin_vec![ast::Stmt {
                                id: ast::DUMMY_NODE_ID,
                                kind: ast::StmtKind::Expr(tail),
                                span,
                            }],
                            id: ast::DUMMY_NODE_ID,
                            rules: ast::BlockCheckMode::Default,
                            span,
                            tokens: None,
                        }),
                        None,
                    ),
                    span,
                    attrs: ast::AttrVec::new(),
                    tokens: None,
                });
            }
        }
    }
}

struct ExtractVisitor<'a> {
    lift_ids: &'a FxHashSet<ast::NodeId>,
    extracted: HashMap<ast::NodeId, P<ast::Item>>,
}

impl MutVisitor for ExtractVisitor<'_> {
    fn flat_map_stmt(&mut self, statement: ast::Stmt) -> smallvec::SmallVec<[ast::Stmt; 1]> {
        if let ast::StmtKind::Item(item) = &statement.kind
            && self.lift_ids.contains(&item.id)
        {
            let ast::StmtKind::Item(item) = statement.kind else { unreachable!() };
            self.extracted.insert(item.id, item);
            return smallvec::smallvec![];
        }
        mut_visit::walk_flat_map_stmt(self, statement)
    }
}

struct InsertVisitor<'a> {
    by_anchor: &'a FxHashMap<ast::NodeId, Vec<ast::NodeId>>,
    extracted: HashMap<ast::NodeId, P<ast::Item>>,
}

fn peel_parentheses(mut expression: &ast::Expr) -> &ast::Expr {
    while let ast::ExprKind::Paren(inner) = &expression.kind {
        expression = inner;
    }
    expression
}

fn is_ignored_setlocale_statement(statement: &ast::Stmt) -> bool {
    let ast::StmtKind::Semi(expression) = &statement.kind else {
        return false;
    };
    let ast::ExprKind::Call(callee, _) = &peel_parentheses(expression).kind else {
        return false;
    };
    let ast::ExprKind::Path(_, path) = &peel_parentheses(callee).kind else {
        return false;
    };
    path.segments
        .last()
        .is_some_and(|segment| segment.ident.name.as_str() == "setlocale")
}

struct IgnoredSetlocaleRemover;

impl MutVisitor for IgnoredSetlocaleRemover {
    fn flat_map_stmt(&mut self, statement: ast::Stmt) -> smallvec::SmallVec<[ast::Stmt; 1]> {
        if is_ignored_setlocale_statement(&statement) {
            return smallvec::smallvec![];
        }
        mut_visit::walk_flat_map_stmt(self, statement)
    }
}

#[derive(Default)]
struct CtypeRewriteVisitor {
    rewrote: bool,
}

impl MutVisitor for CtypeRewriteVisitor {
    fn visit_expr(&mut self, expression: &mut ast::Expr) {
        if let Some((function, argument)) =
            ctype_mask_call(expression).or_else(|| ctype_table_call(expression))
        {
            let mut argument = argument.clone();
            self.visit_expr(&mut argument);
            *expression = ctype_call(function, &argument);
            self.rewrote = true;
            return;
        }

        mut_visit::walk_expr(self, expression);

        let ast::ExprKind::Call(callee, arguments) = &expression.kind else {
            return;
        };
        let ast::ExprKind::Path(None, path) = &callee.kind else {
            return;
        };
        let [segment] = path.segments.as_slice() else {
            return;
        };
        let [argument] = arguments.as_slice() else {
            return;
        };
        let name = segment.ident.as_str();
        if direct_ctype_name(name).is_none() {
            return;
        }
        *expression = ctype_call(name, argument);
        self.rewrote = true;
    }
}

fn direct_ctype_name(name: &str) -> Option<&str> {
    matches!(
        name,
        "isalnum"
            | "isalpha"
            | "isblank"
            | "iscntrl"
            | "isdigit"
            | "isgraph"
            | "islower"
            | "isprint"
            | "ispunct"
            | "isspace"
            | "isupper"
            | "isxdigit"
            | "tolower"
            | "toupper"
    )
    .then_some(name)
}

fn ctype_call(function: &str, argument: &ast::Expr) -> ast::Expr {
    let argument = pprust::expr_to_string(argument);
    utils::expr!("::proctor_libc::{function}({argument})")
}

fn peel_casts(mut expression: &ast::Expr) -> &ast::Expr {
    while let ast::ExprKind::Cast(inner, _) = &expression.kind {
        expression = inner;
    }
    expression
}

fn terminal_isize_cast(expression: &ast::Expr) -> Option<&ast::Expr> {
    let ast::ExprKind::Cast(inner, ty) = &expression.kind else {
        return None;
    };
    (pprust::ty_to_string(ty) == "isize").then_some(inner)
}

fn ctype_accessor_index<'a>(expression: &'a ast::Expr, accessor: &str) -> Option<&'a ast::Expr> {
    let ast::ExprKind::Unary(ast::UnOp::Deref, load) = &expression.kind else {
        return None;
    };
    let ast::ExprKind::MethodCall(box ast::MethodCall {
        seg,
        receiver,
        args,
        ..
    }) = &load.kind
    else {
        return None;
    };
    if seg.ident.as_str() != "offset" {
        return None;
    }
    let [index] = args.as_slice() else {
        return None;
    };
    let ast::ExprKind::Paren(receiver) = &receiver.kind else {
        return None;
    };
    let ast::ExprKind::Unary(ast::UnOp::Deref, receiver) = &receiver.kind else {
        return None;
    };
    let ast::ExprKind::Call(callee, call_arguments) = &receiver.kind else {
        return None;
    };
    if !call_arguments.is_empty() {
        return None;
    }
    let ast::ExprKind::Path(None, path) = &callee.kind else {
        return None;
    };
    let [segment] = path.segments.as_slice() else {
        return None;
    };
    if segment.ident.as_str() != accessor {
        return None;
    }
    terminal_isize_cast(index)
}

fn ctype_mask_call(expression: &ast::Expr) -> Option<(&'static str, &ast::Expr)> {
    let ast::ExprKind::Binary(operator, left, right) = &expression.kind else {
        return None;
    };
    if operator.node != ast::BinOpKind::BitAnd {
        return None;
    }
    let ast::ExprKind::Cast(load, _) = &left.kind else {
        return None;
    };
    let argument = ctype_accessor_index(load, "__ctype_b_loc")?;
    let ast::ExprKind::Path(None, path) = &peel_casts(right).kind else {
        return None;
    };
    let [segment] = path.segments.as_slice() else {
        return None;
    };
    let function = match segment.ident.as_str() {
        "_ISupper" => "isupper",
        "_ISlower" => "islower",
        "_ISalpha" => "isalpha",
        "_ISdigit" => "isdigit",
        "_ISxdigit" => "isxdigit",
        "_ISspace" => "isspace",
        "_ISprint" => "isprint",
        "_ISgraph" => "isgraph",
        "_ISblank" => "isblank",
        "_IScntrl" => "iscntrl",
        "_ISpunct" => "ispunct",
        "_ISalnum" => "isalnum",
        _ => return None,
    };
    Some((function, argument))
}

fn ctype_table_call(expression: &ast::Expr) -> Option<(&'static str, &ast::Expr)> {
    ctype_accessor_index(expression, "__ctype_tolower_loc")
        .map(|argument| ("tolower", argument))
        .or_else(|| {
            ctype_accessor_index(expression, "__ctype_toupper_loc")
                .map(|argument| ("toupper", argument))
        })
}

impl MutVisitor for InsertVisitor<'_> {
    fn flat_map_item(&mut self, item: P<ast::Item>) -> smallvec::SmallVec<[P<ast::Item>; 1]> {
        let anchor = item.id;
        let mut result = smallvec::SmallVec::new();
        if let Some(ids) = self.by_anchor.get(&anchor) {
            for node_id in ids {
                result.push(
                    self.extracted
                        .remove(node_id)
                        .expect("planned local static was not extracted"),
                );
            }
        }
        result.extend(mut_visit::walk_flat_map_item(self, item));
        result
    }
}

pub fn prepare(tcx: TyCtxt<'_>) -> Result<PreparationResult, PrepareError> {
    let mut krate = utils::ast::expanded_ast(tcx);
    validate_supported_input(&krate)?;
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);

    let mut discovery = Discovery::new(tcx, &ast_to_hir);
    discovery.discover_crate(&krate);
    if let Some(error) = discovery.error {
        return Err(error);
    }
    validate_dependencies(
        &krate,
        &discovery.lifts,
        &discovery.local_imports,
        &ast_to_hir,
        tcx,
    )?;
    validate_use_mappings(&krate, &discovery.lifts, &ast_to_hir, tcx)?;
    let names = allocated_names(&discovery.lifts, &binder_inventory(tcx), tcx);

    utils::ast::remove_unnecessary_items_from_ast(&mut krate);
    RewriteVisitor {
        tcx,
        ast_to_hir: &ast_to_hir,
        names: &names,
    }
    .visit_crate(&mut krate);

    let lift_ids = discovery
        .lifts
        .iter()
        .map(|lift| lift.node_id)
        .collect::<FxHashSet<_>>();
    let mut extractor = ExtractVisitor {
        lift_ids: &lift_ids,
        extracted: HashMap::new(),
    };
    extractor.visit_crate(&mut krate);
    let by_anchor = discovery.lifts.iter().fold(
        FxHashMap::<ast::NodeId, Vec<ast::NodeId>>::default(),
        |mut result, lift| {
            result.entry(lift.anchor).or_default().push(lift.node_id);
            result
        },
    );
    let mut inserter = InsertVisitor {
        by_anchor: &by_anchor,
        extracted: extractor.extracted,
    };
    inserter.visit_crate(&mut krate);
    debug_assert!(inserter.extracted.is_empty());

    IgnoredSetlocaleRemover.visit_crate(&mut krate);

    let mut ctype_rewriter = CtypeRewriteVisitor::default();
    ctype_rewriter.visit_crate(&mut krate);

    Ok(PreparationResult {
        code: pprust::crate_to_string_for_macros(&krate),
        requires_proctor_libc: ctype_rewriter.rewrote,
    })
}
