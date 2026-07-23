use std::collections::BTreeSet;

use pointer_replacer::{
    InitialPointerDecisions, PointerDecisionOptions, PtrKind, initial_pointer_decisions,
};
use rustc_ast::{
    AttrKind, BindingMode, ByRef, Crate, Expr, ExprKind, Extern, FnRetTy, Item, ItemKind,
    LocalKind, Mutability, Pat, PatKind, Safety, Stmt, StmtKind, Ty, TyKind, mut_visit,
    mut_visit::MutVisitor, ptr::P, visit, visit::Visitor as _,
};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_hir::{
    self as hir, HirId,
    def::{DefKind, Res},
    intravisit::{self, Visitor, VisitorExt},
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, TyCtxt},
};
use rustc_span::{DUMMY_SP, Symbol, def_id::LocalDefId, sym};
use serde::{Deserialize, Serialize};
use smallvec::{SmallVec, smallvec};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ItemKindName {
    Fn,
    Static,
    Const,
    TyAlias,
    Enum,
    Struct,
    Union,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionRecord {
    pub id: u64,
    pub path: String,
    pub kind: ItemKindName,
    pub name: String,
    pub annotated_source: String,
    pub annotated_skeleton: String,
    pub source_signature: String,
    pub target_signature: String,
    pub signature_dependencies: Vec<u64>,
    pub dependencies: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValueRecord {
    pub id: u64,
    pub path: String,
    pub kind: ItemKindName,
    pub declaration: String,
    pub signature_dependencies: Vec<u64>,
    pub dependencies: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeRecord {
    pub id: u64,
    pub path: String,
    pub kind: ItemKindName,
    pub definition: String,
    pub dependencies: Vec<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ItemRecord {
    Function(FunctionRecord),
    Value(ValueRecord),
    Type(TypeRecord),
}

impl ItemRecord {
    pub fn id(&self) -> u64 {
        match self {
            Self::Function(record) => record.id,
            Self::Value(record) => record.id,
            Self::Type(record) => record.id,
        }
    }

    pub fn path(&self) -> &str {
        match self {
            Self::Function(record) => &record.path,
            Self::Value(record) => &record.path,
            Self::Type(record) => &record.path,
        }
    }

    pub fn kind(&self) -> ItemKindName {
        match self {
            Self::Function(record) => record.kind,
            Self::Value(record) => record.kind,
            Self::Type(record) => record.kind,
        }
    }

    pub fn dependencies(&self) -> &[u64] {
        match self {
            Self::Function(record) => &record.dependencies,
            Self::Value(record) => &record.dependencies,
            Self::Type(record) => &record.dependencies,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum GenerationErrorKind {
    EmptyStatement,
    FunctionLocalItem,
    NonBlockMatchArm,
    NestedControlPayload,
    AstHirMismatch,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenerationError {
    pub kind: GenerationErrorKind,
    pub function_path: String,
    pub message: String,
}

#[derive(Clone)]
struct SurfaceItem {
    id: u64,
    path: String,
    item: P<Item>,
    def_id: LocalDefId,
    kind: ItemKindName,
}

pub fn make_skeletons(source: &str, tcx: TyCtxt<'_>) -> Result<Vec<ItemRecord>, GenerationError> {
    let mut surface = utils::ast::parse_crate(source.to_owned());
    let mut mapper = utils::ir::AstToHirMapper::new(tcx);
    if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
    }))
    .is_err()
    {
        return Err(GenerationError {
            kind: GenerationErrorKind::AstHirMismatch,
            function_path: String::new(),
            message: "surface AST does not structurally match lowered HIR".to_owned(),
        });
    }
    let ast_to_hir = mapper.ast_to_hir;

    let mut raw_items = vec![];
    collect_surface_items(
        &surface,
        &ast_to_hir.global_map,
        &mut vec![],
        &mut raw_items,
    )?;
    let item_ids: FxHashMap<_, _> = raw_items
        .iter()
        .map(|item| (item.def_id.to_def_id(), item.id))
        .collect();
    let decisions = initial_pointer_decisions(
        &pointer_replacer::Config::default(),
        PointerDecisionOptions {
            assume_nonnegative_offsets: true,
        },
        tcx,
    );

    raw_items
        .into_iter()
        .map(|item| make_record(item, &ast_to_hir, &item_ids, &decisions, tcx))
        .collect()
}

pub fn skeletons_to_json(records: &[ItemRecord]) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(records)
}

pub fn included_item_kind(item: &Item) -> Option<ItemKindName> {
    match item.kind {
        ItemKind::Fn(..) => Some(ItemKindName::Fn),
        ItemKind::Static(..) => Some(ItemKindName::Static),
        ItemKind::Const(..) => Some(ItemKindName::Const),
        ItemKind::TyAlias(..) => Some(ItemKindName::TyAlias),
        ItemKind::Enum(..) => Some(ItemKindName::Enum),
        ItemKind::Struct(..) => Some(ItemKindName::Struct),
        ItemKind::Union(..) => Some(ItemKindName::Union),
        _ => None,
    }
}

fn collect_surface_items(
    krate: &Crate,
    global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
    path: &mut Vec<String>,
    output: &mut Vec<SurfaceItem>,
) -> Result<(), GenerationError> {
    collect_items(&krate.items, global_map, path, output)
}

fn collect_items(
    items: &[P<Item>],
    global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
    path: &mut Vec<String>,
    output: &mut Vec<SurfaceItem>,
) -> Result<(), GenerationError> {
    for item in items {
        if let ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(items, ..)) = &item.kind {
            path.push(ident.to_string());
            collect_items(items, global_map, path, output)?;
            path.pop();
            continue;
        }
        let Some(kind) = included_item_kind(item) else {
            continue;
        };
        if kind == ItemKindName::Fn
            && item
                .kind
                .ident()
                .is_some_and(|ident| ident.name.as_str() == "main")
        {
            continue;
        }
        let def_id = global_map
            .get(&item.id)
            .copied()
            .ok_or_else(|| GenerationError {
                kind: GenerationErrorKind::AstHirMismatch,
                function_path: path.join("::"),
                message: "surface item has no structurally mapped HIR owner".to_owned(),
            })?;
        let name = item
            .kind
            .ident()
            .map(|ident| ident.to_string())
            .unwrap_or_default();
        let full_path = path
            .iter()
            .cloned()
            .chain(std::iter::once(name))
            .collect::<Vec<_>>()
            .join("::");
        output.push(SurfaceItem {
            id: output.len() as u64,
            path: full_path,
            item: item.clone(),
            def_id,
            kind,
        });
    }
    Ok(())
}

fn make_record(
    surface: SurfaceItem,
    ast_to_hir: &utils::ir::AstToHir,
    item_ids: &FxHashMap<rustc_span::def_id::DefId, u64>,
    decisions: &InitialPointerDecisions,
    tcx: TyCtxt<'_>,
) -> Result<ItemRecord, GenerationError> {
    let hitem = tcx.hir_node_by_def_id(surface.def_id).expect_item();
    let dependencies = collect_dependencies(hitem, item_ids, tcx);
    match surface.kind {
        ItemKindName::Fn => make_function_record(surface, ast_to_hir, item_ids, decisions, tcx),
        ItemKindName::Static | ItemKindName::Const => {
            let signature_dependencies = collect_signature_dependencies(hitem, item_ids, tcx);
            let mut item = surface.item.clone();
            sanitize_item(&mut item);
            remove_value_initializer(&mut item);
            Ok(ItemRecord::Value(ValueRecord {
                id: surface.id,
                path: surface.path,
                kind: surface.kind,
                declaration: pprust::item_to_string(&item),
                signature_dependencies,
                dependencies,
            }))
        }
        ItemKindName::TyAlias | ItemKindName::Enum | ItemKindName::Struct | ItemKindName::Union => {
            let mut item = surface.item.clone();
            sanitize_item(&mut item);
            Ok(ItemRecord::Type(TypeRecord {
                id: surface.id,
                path: surface.path,
                kind: surface.kind,
                definition: pprust::item_to_string(&item),
                dependencies,
            }))
        }
    }
}

fn make_function_record(
    surface: SurfaceItem,
    ast_to_hir: &utils::ir::AstToHir,
    item_ids: &FxHashMap<rustc_span::def_id::DefId, u64>,
    decisions: &InitialPointerDecisions,
    tcx: TyCtxt<'_>,
) -> Result<ItemRecord, GenerationError> {
    let hitem = tcx.hir_node_by_def_id(surface.def_id).expect_item();
    let signature_dependencies = collect_signature_dependencies(hitem, item_ids, tcx);
    let dependencies = collect_dependencies(hitem, item_ids, tcx);
    let mut source = surface.item.clone();
    sanitize_item(&mut source);
    annotate_function(&mut source, &surface.path)?;
    let mut skeleton = source.clone();
    apply_target_signature(&mut skeleton, surface.def_id, decisions, tcx);
    let mut skeletonizer = Skeletonizer {
        ast_to_hir,
        decisions,
        tcx,
        function_path: &surface.path,
        error: None,
    };
    skeletonizer.visit_item(&mut skeleton);
    if let Some(error) = skeletonizer.error {
        return Err(error);
    }
    TargetBindingMutator.visit_item(&mut skeleton);

    let source_signature = render_signature(&source);
    let target_signature = render_signature(&skeleton);
    let name = surface.item.kind.ident().unwrap().to_string();
    Ok(ItemRecord::Function(FunctionRecord {
        id: surface.id,
        path: surface.path,
        kind: ItemKindName::Fn,
        name,
        annotated_source: render_annotated_item(&source),
        annotated_skeleton: render_annotated_item(&skeleton),
        source_signature,
        target_signature,
        signature_dependencies,
        dependencies,
    }))
}

fn sanitize_item(item: &mut Item) {
    item.attrs.retain(|attr| {
        let AttrKind::Normal(normal) = &attr.kind else {
            return true;
        };
        normal.item.path.segments.last().unwrap().ident.name != sym::no_mangle
    });
    if let ItemKind::Fn(box function) = &mut item.kind {
        function.sig.header.ext = Extern::None;
    }
}

fn remove_value_initializer(item: &mut Item) {
    match &mut item.kind {
        ItemKind::Static(static_item) => static_item.expr = None,
        ItemKind::Const(const_item) => const_item.expr = None,
        _ => unreachable!(),
    }
}

fn render_signature(item: &Item) -> String {
    let mut item = item.clone();
    let ItemKind::Fn(box function) = &mut item.kind else { unreachable!() };
    function.body = None;
    pprust::item_to_string(&item)
        .trim_end_matches(';')
        .to_owned()
}

fn render_annotated_item(item: &Item) -> String {
    let rendered = pprust::item_to_string(item);
    let lines = rendered.lines().collect::<Vec<_>>();
    let mut output = Vec::with_capacity(lines.len());
    for (index, line) in lines.iter().enumerate() {
        if line.is_empty()
            && lines
                .get(index + 1)
                .is_some_and(|next| next.trim_start().starts_with("#[proctor("))
        {
            continue;
        }
        output.push(*line);
    }
    output.join("\n")
}

struct Labeler<'a> {
    next: u32,
    function_path: &'a str,
    error: Option<GenerationError>,
}

impl MutVisitor for Labeler<'_> {
    fn flat_map_stmt(&mut self, mut stmt: Stmt) -> SmallVec<[Stmt; 1]> {
        if let StmtKind::Item(item) = &stmt.kind {
            self.error.get_or_insert_with(|| GenerationError {
                kind: GenerationErrorKind::FunctionLocalItem,
                function_path: self.function_path.to_owned(),
                message: format!(
                    "function-local {} items are unsupported",
                    local_item_kind(item)
                ),
            });
            return smallvec![stmt];
        }
        if matches!(stmt.kind, StmtKind::Empty) {
            self.error.get_or_insert_with(|| GenerationError {
                kind: GenerationErrorKind::EmptyStatement,
                function_path: self.function_path.to_owned(),
                message: "empty statement cannot be annotated".to_owned(),
            });
            return smallvec![stmt];
        }
        stmt_attrs_mut(&mut stmt).extend(utils::attr!("#[proctor({})]", self.next));
        self.next += 1;
        mut_visit::walk_flat_map_stmt(self, stmt)
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if let ExprKind::Match(_, arms, _) = &expr.kind {
            for arm in arms {
                if !arm
                    .body
                    .as_ref()
                    .is_some_and(|body| matches!(body.kind, ExprKind::Block(..)))
                {
                    self.error.get_or_insert_with(|| GenerationError {
                        kind: GenerationErrorKind::NonBlockMatchArm,
                        function_path: self.function_path.to_owned(),
                        message: "match arm body must be a block expression".to_owned(),
                    });
                    return;
                }
            }
        }
        mut_visit::walk_expr(self, expr);
    }
}

fn stmt_attrs_mut(stmt: &mut Stmt) -> &mut rustc_ast::AttrVec {
    match &mut stmt.kind {
        StmtKind::Let(local) => &mut local.attrs,
        StmtKind::Item(item) => &mut item.attrs,
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => &mut expr.attrs,
        StmtKind::MacCall(mac) => &mut mac.attrs,
        StmtKind::Empty => unreachable!(),
    }
}

fn annotate_function(item: &mut Item, path: &str) -> Result<(), GenerationError> {
    let mut labeler = Labeler {
        next: 0,
        function_path: path,
        error: None,
    };
    let ItemKind::Fn(box function) = &mut item.kind else { unreachable!() };
    labeler.visit_block(function.body.as_mut().unwrap());
    labeler.error.map_or(Ok(()), Err)
}

fn apply_target_signature(
    item: &mut Item,
    def_id: LocalDefId,
    decisions: &InitialPointerDecisions,
    tcx: TyCtxt<'_>,
) {
    let ItemKind::Fn(box function) = &mut item.kind else { unreachable!() };
    let force_main_argv = is_supported_two_argument_main_0(function);
    function.sig.header.safety = Safety::Unsafe(DUMMY_SP);
    let Some(decision) = decisions.signatures.data.get(&def_id) else {
        if force_main_argv {
            function.sig.decl.inputs[1].ty = P(utils::ast::parse_ty("&mut [&mut [i8]]".to_owned()));
        }
        return;
    };
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
    let mut lifetimes = vec![];
    for lifetime in decision
        .input_lifetimes
        .iter()
        .copied()
        .flatten()
        .chain(decision.output_lifetime)
    {
        if !lifetimes.contains(&lifetime) {
            lifetimes.push(lifetime);
        }
    }
    add_lifetime_params(&mut function.generics, &lifetimes);
    for (index, param) in function.sig.decl.inputs.iter_mut().enumerate() {
        let Some(kind) = decision.input_decs.get(index).copied().flatten() else {
            continue;
        };
        if raw_decision_matches_ast_type(kind, &param.ty) {
            continue;
        }
        let original = body.local_decls[rustc_middle::mir::Local::from_usize(index + 1)].ty;
        let lifetime = decision.input_lifetimes.get(index).copied().flatten();
        *param.ty = target_type(original, kind, lifetime, tcx);
    }
    if let Some(kind) = decision.output_dec
        && let FnRetTy::Ty(output) = &mut function.sig.decl.output
        && !raw_decision_matches_ast_type(kind, output)
    {
        let original = body.local_decls[rustc_middle::mir::RETURN_PLACE].ty;
        **output = target_type(original, kind, decision.output_lifetime, tcx);
    }
    if force_main_argv {
        function.sig.decl.inputs[1].ty = P(utils::ast::parse_ty("&mut [&mut [i8]]".to_owned()));
    }
}

fn is_supported_two_argument_main_0(function: &rustc_ast::Fn) -> bool {
    function.ident.name.as_str() == "main_0" && function.sig.decl.inputs.len() == 2
}

fn local_item_kind(item: &Item) -> &'static str {
    match item.kind {
        ItemKind::Const(..) => "const",
        ItemKind::Static(..) => "static",
        ItemKind::Fn(..) => "function",
        ItemKind::TyAlias(..) => "type alias",
        ItemKind::Struct(..) => "struct",
        ItemKind::Enum(..) => "enum",
        ItemKind::Union(..) => "union",
        ItemKind::Mod(..) => "module",
        ItemKind::Use(..) => "use",
        ItemKind::ExternCrate(..) => "extern crate",
        ItemKind::ForeignMod(..) => "foreign",
        ItemKind::Trait(..) => "trait",
        ItemKind::Impl(..) => "impl",
        ItemKind::MacroDef(..) => "macro definition",
        ItemKind::MacCall(..) => "macro invocation",
        _ => "other",
    }
}

struct TargetBindingMutator;

impl MutVisitor for TargetBindingMutator {
    fn visit_pat(&mut self, pat: &mut Pat) {
        if let PatKind::Ident(BindingMode(by_ref, mutability), ..) = &mut pat.kind {
            match by_ref {
                ByRef::No => *mutability = Mutability::Mut,
                ByRef::Yes(reference_mutability) => {
                    *reference_mutability = Mutability::Mut;
                }
            }
        }
        mut_visit::walk_pat(self, pat);
    }
}

fn raw_decision_matches_ast_type(kind: PtrKind, ty: &Ty) -> bool {
    let PtrKind::Raw(target_mutability) = kind else {
        return false;
    };
    let TyKind::Ptr(mut_ty) = &ty.kind else {
        return false;
    };
    target_mutability == matches!(mut_ty.mutbl, rustc_ast::Mutability::Mut)
}

fn add_lifetime_params(generics: &mut rustc_ast::Generics, lifetimes: &[Symbol]) {
    for lifetime in lifetimes.iter().rev() {
        let parsed = utils::item!("fn f<'{}>() {{}}", lifetime.as_str());
        let ItemKind::Fn(box parsed) = parsed.kind else { unreachable!() };
        generics.params.insert(0, parsed.generics.params[0].clone());
    }
}

fn target_type<'tcx>(
    original: ty::Ty<'tcx>,
    kind: PtrKind,
    lifetime: Option<Symbol>,
    tcx: TyCtxt<'tcx>,
) -> Ty {
    let (ty::TyKind::RawPtr(inner, _) | ty::TyKind::Ref(_, inner, _)) = original.kind() else {
        return utils::ast::parse_ty(utils::ir::mir_ty_to_string(original, tcx));
    };
    let inner = utils::ir::mir_ty_to_string(*inner, tcx);
    let lifetime = lifetime
        .map(|lifetime| format!("'{} ", lifetime.as_str()))
        .unwrap_or_default();
    let mutable = if kind.is_mut() { "mut " } else { "" };
    let rendered = match kind {
        PtrKind::Ref(_) => format!("&{lifetime}{mutable}{inner}"),
        PtrKind::OptRef(_) => format!("Option<&{lifetime}{mutable}{inner}>"),
        PtrKind::Box => format!("Box<{inner}>"),
        PtrKind::OptBox => format!("Option<Box<{inner}>>"),
        PtrKind::Raw(mutable) => {
            format!("*{} {inner}", if mutable { "mut" } else { "const" })
        }
        PtrKind::BoxedSlice => format!("Box<[{inner}]>"),
        PtrKind::OptBoxedSlice => format!("Option<Box<[{inner}]>>"),
        PtrKind::Slice(_) => format!("&{lifetime}{mutable}[{inner}]"),
        PtrKind::SliceCursor(mutable) => {
            let cursor = if mutable {
                "SliceCursorMut"
            } else {
                "SliceCursor"
            };
            let lifetime = lifetime.trim_end();
            let lifetime = if lifetime.is_empty() { "'_" } else { lifetime };
            format!("crate::slice_cursor::{cursor}<{lifetime}, {inner}>")
        }
    };
    utils::ast::parse_ty(rendered)
}

struct Skeletonizer<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    decisions: &'a InitialPointerDecisions,
    tcx: TyCtxt<'tcx>,
    function_path: &'a str,
    error: Option<GenerationError>,
}

impl MutVisitor for Skeletonizer<'_, '_> {
    fn flat_map_stmt(&mut self, mut stmt: Stmt) -> SmallVec<[Stmt; 1]> {
        match &mut stmt.kind {
            StmtKind::Let(local) => {
                if let PatKind::Ident(_, _, None) = local.pat.kind
                    && let Some(hir_id) = self.ast_to_hir.local_map.get(&local.pat.id).copied()
                {
                    let inferred = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                    let decision = inferred
                        .is_raw_ptr()
                        .then(|| self.decisions.bindings.get(&hir_id).copied())
                        .flatten();
                    let ty = match (decision, local.ty.as_deref()) {
                        (Some(kind), Some(ty))
                            if raw_decision_matches_inferred_type(kind, inferred) =>
                        {
                            ty.clone()
                        }
                        (Some(kind), _) => target_type(inferred, kind, None, self.tcx),
                        (None, Some(ty)) => ty.clone(),
                        (None, None) => utils::ast::parse_ty(inferred.to_string()),
                    };
                    local.ty = Some(P(ty));
                }
                match &mut local.kind {
                    LocalKind::Decl => {}
                    LocalKind::Init(init) => skeletonize_payload(init, self),
                    LocalKind::InitElse(init, else_block) => {
                        skeletonize_payload(init, self);
                        self.visit_block(else_block);
                    }
                }
            }
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => skeletonize_statement_expr(expr, self),
            StmtKind::Item(_) | StmtKind::Empty => {}
            StmtKind::MacCall(mac) => {
                let mut expr = todo_expr();
                expr.attrs = std::mem::take(&mut mac.attrs);
                stmt.kind = StmtKind::Semi(P(expr));
            }
        }
        smallvec![stmt]
    }
}

fn todo_expr() -> Expr {
    utils::expr!("todo!()")
}

fn replace_with_todo(expr: &mut Expr) {
    let attrs = std::mem::take(&mut expr.attrs);
    *expr = todo_expr();
    expr.attrs = attrs;
}

fn is_preserved_expression(expr: &Expr) -> bool {
    matches!(
        expr.kind,
        ExprKind::If(..)
            | ExprKind::While(..)
            | ExprKind::ForLoop { .. }
            | ExprKind::Loop(..)
            | ExprKind::Match(..)
            | ExprKind::Block(..)
    )
}

fn raw_decision_matches_inferred_type(kind: PtrKind, ty: ty::Ty<'_>) -> bool {
    let PtrKind::Raw(target_mutability) = kind else {
        return false;
    };
    let ty::TyKind::RawPtr(_, source_mutability) = ty.kind() else {
        return false;
    };
    target_mutability == source_mutability.is_mut()
}

fn contains_control_expression(expr: &Expr) -> bool {
    struct Finder {
        found: bool,
    }

    impl<'ast> visit::Visitor<'ast> for Finder {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            if is_preserved_expression(expr) {
                self.found = true;
                return;
            }
            visit::walk_expr(self, expr);
        }
    }

    let mut finder = Finder { found: false };
    finder.visit_expr(expr);
    finder.found
}

fn reject_nested_control(expr: &Expr, visitor: &mut Skeletonizer<'_, '_>) -> bool {
    if !contains_control_expression(expr) {
        return false;
    }
    visitor.error.get_or_insert_with(|| GenerationError {
        kind: GenerationErrorKind::NestedControlPayload,
        function_path: visitor.function_path.to_owned(),
        message: "control expression nested beneath a non-control payload".to_owned(),
    });
    true
}

fn skeletonize_payload(expr: &mut Expr, visitor: &mut Skeletonizer<'_, '_>) {
    if is_preserved_expression(expr) {
        skeletonize_control(expr, visitor);
    } else if !reject_nested_control(expr, visitor) {
        replace_with_todo(expr);
    }
}

fn skeletonize_statement_expr(expr: &mut Expr, visitor: &mut Skeletonizer<'_, '_>) {
    if is_preserved_expression(expr) {
        skeletonize_control(expr, visitor);
        return;
    }
    match &mut expr.kind {
        ExprKind::Ret(value) | ExprKind::Break(_, value) => {
            if let Some(value) = value {
                skeletonize_payload(value, visitor);
            }
        }
        ExprKind::Continue(_) => {}
        _ => skeletonize_payload(expr, visitor),
    }
}

fn skeletonize_condition(expr: &mut Expr, visitor: &mut Skeletonizer<'_, '_>) {
    if reject_nested_control(expr, visitor) {
        return;
    }
    if let ExprKind::Let(_, value, _, _) = &mut expr.kind {
        **value = todo_expr();
    } else {
        replace_with_todo(expr);
    }
}

fn skeletonize_control(expr: &mut Expr, visitor: &mut Skeletonizer<'_, '_>) {
    match &mut expr.kind {
        ExprKind::If(condition, then_block, else_expr) => {
            skeletonize_condition(condition, visitor);
            visitor.visit_block(then_block);
            if let Some(else_expr) = else_expr {
                skeletonize_payload(else_expr, visitor);
            }
        }
        ExprKind::While(condition, body, _) => {
            skeletonize_condition(condition, visitor);
            visitor.visit_block(body);
        }
        ExprKind::ForLoop { iter, body, .. } => {
            if !reject_nested_control(iter, visitor) {
                **iter = todo_expr();
            }
            visitor.visit_block(body);
        }
        ExprKind::Loop(body, ..) | ExprKind::Block(body, ..) => visitor.visit_block(body),
        ExprKind::Match(scrutinee, arms, _) => {
            if !reject_nested_control(scrutinee, visitor) {
                **scrutinee = todo_expr();
            }
            for arm in arms {
                if let Some(guard) = &mut arm.guard
                    && !reject_nested_control(guard, visitor)
                {
                    **guard = todo_expr();
                }
                skeletonize_payload(arm.body.as_mut().unwrap(), visitor);
            }
        }
        _ => replace_with_todo(expr),
    }
}

struct DependencyVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    item_ids: &'a FxHashMap<rustc_span::def_id::DefId, u64>,
    dependencies: BTreeSet<u64>,
}

impl DependencyVisitor<'_, '_> {
    fn add_res(&mut self, res: Res) {
        let Res::Def(kind, mut def_id) = res else {
            return;
        };
        if let Some(id) = self.item_ids.get(&def_id) {
            self.dependencies.insert(*id);
            return;
        }
        if !matches!(kind, DefKind::Ctor(..) | DefKind::Variant | DefKind::Field) {
            return;
        }
        while def_id.is_local() {
            def_id = self.tcx.parent(def_id);
            if let Some(id) = self.item_ids.get(&def_id) {
                self.dependencies.insert(*id);
                return;
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for DependencyVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_path(&mut self, path: &hir::Path<'tcx>, _hir_id: HirId) {
        self.add_res(path.res);
        intravisit::walk_path(self, path);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Field(base, _) = expr.kind {
            let ty = self.tcx.typeck(expr.hir_id.owner).expr_ty_adjusted(base);
            if let ty::TyKind::Adt(def, _) = ty.peel_refs().kind() {
                self.add_res(Res::Def(self.tcx.def_kind(def.did()), def.did()));
            }
        }
        intravisit::walk_expr(self, expr);
    }
}

fn collect_dependencies<'tcx>(
    item: &'tcx hir::Item<'tcx>,
    item_ids: &FxHashMap<rustc_span::def_id::DefId, u64>,
    tcx: TyCtxt<'tcx>,
) -> Vec<u64> {
    let mut visitor = DependencyVisitor {
        tcx,
        item_ids,
        dependencies: BTreeSet::new(),
    };
    visitor.visit_item(item);
    visitor.dependencies.into_iter().collect()
}

fn collect_signature_dependencies<'tcx>(
    item: &'tcx hir::Item<'tcx>,
    item_ids: &FxHashMap<rustc_span::def_id::DefId, u64>,
    tcx: TyCtxt<'tcx>,
) -> Vec<u64> {
    let mut visitor = DependencyVisitor {
        tcx,
        item_ids,
        dependencies: BTreeSet::new(),
    };
    match item.kind {
        hir::ItemKind::Fn { sig, .. } => {
            visitor.visit_fn_decl(sig.decl);
        }
        hir::ItemKind::Static(_, _, ty, _) | hir::ItemKind::Const(_, _, ty, _) => {
            visitor.visit_ty_unambig(ty)
        }
        _ => {}
    }
    visitor.dependencies.into_iter().collect()
}

#[cfg(test)]
mod tests;
