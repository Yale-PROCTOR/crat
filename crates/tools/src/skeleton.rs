use std::collections::BTreeSet;

use pointer_replacer::{
    InitialPointerDecisions, PointerDecisionOptions, PtrKind, initial_pointer_decisions,
};
use rustc_ast::{
    AttrKind, BindingMode, ByRef, Crate, Expr, ExprKind, Extern, FnRetTy, Item, ItemKind,
    LocalKind, Mutability, NodeId, Pat, PatKind, Safety, Stmt, StmtKind, Ty, TyKind, mut_visit,
    mut_visit::MutVisitor, ptr::P, visit, visit::Visitor as _,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId,
    def::{DefKind, Res},
    intravisit::{self, Visitor, VisitorExt},
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, TyCtxt},
};
use rustc_span::{
    DUMMY_SP, Symbol,
    def_id::{DefId, LocalDefId},
    sym,
};
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
    pub needs_transformation: bool,
    pub statements_requiring_transformation: Vec<u32>,
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

#[derive(Default)]
struct PreservationDecisionOverrides {
    changed_fields: FxHashSet<DefId>,
    changed_local_signatures: FxHashSet<LocalDefId>,
}

pub fn make_skeletons(source: &str, tcx: TyCtxt<'_>) -> Result<Vec<ItemRecord>, GenerationError> {
    make_skeletons_with_preservation_overrides(
        source,
        tcx,
        &PreservationDecisionOverrides::default(),
    )
}

fn make_skeletons_with_preservation_overrides(
    source: &str,
    tcx: TyCtxt<'_>,
    preservation_overrides: &PreservationDecisionOverrides,
) -> Result<Vec<ItemRecord>, GenerationError> {
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
        .map(|item| {
            make_record(
                item,
                &ast_to_hir,
                &item_ids,
                &decisions,
                preservation_overrides,
                tcx,
            )
        })
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
    preservation_overrides: &PreservationDecisionOverrides,
    tcx: TyCtxt<'_>,
) -> Result<ItemRecord, GenerationError> {
    let hitem = tcx.hir_node_by_def_id(surface.def_id).expect_item();
    let dependencies = collect_dependencies(hitem, item_ids, tcx);
    match surface.kind {
        ItemKindName::Fn => make_function_record(
            surface,
            ast_to_hir,
            item_ids,
            decisions,
            preservation_overrides,
            tcx,
        ),
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
    preservation_overrides: &PreservationDecisionOverrides,
    tcx: TyCtxt<'_>,
) -> Result<ItemRecord, GenerationError> {
    let hitem = tcx.hir_node_by_def_id(surface.def_id).expect_item();
    let signature_dependencies = collect_signature_dependencies(hitem, item_ids, tcx);
    let dependencies = collect_dependencies(hitem, item_ids, tcx);
    let mut source = surface.item.clone();
    sanitize_item(&mut source);
    validate_function_body(&source, &surface.path)?;
    let opaque_nested_ifs = collect_opaque_nested_ifs(&source, &surface.path)?;
    annotate_function(&mut source, &opaque_nested_ifs);
    PresentationBindingNormalizer.visit_item(&mut source);
    let statements_requiring_transformation = classify_function_statements(
        &source,
        &opaque_nested_ifs,
        ast_to_hir,
        decisions,
        preservation_overrides,
        tcx,
    );
    let mut skeleton = source.clone();
    apply_target_signature(&mut skeleton, surface.def_id, decisions, tcx);
    let mut skeletonizer = Skeletonizer {
        ast_to_hir,
        decisions,
        statements_requiring_transformation: &statements_requiring_transformation,
        tcx,
    };
    skeletonizer.visit_item(&mut skeleton);
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
        needs_transformation: !statements_requiring_transformation.is_empty(),
        statements_requiring_transformation: statements_requiring_transformation
            .into_iter()
            .collect(),
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

struct BodyValidator<'a> {
    function_path: &'a str,
    error: Option<GenerationError>,
}

impl<'ast> visit::Visitor<'ast> for BodyValidator<'_> {
    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        if self.error.is_some() {
            return;
        }
        if let StmtKind::Item(item) = &stmt.kind {
            self.error.get_or_insert_with(|| GenerationError {
                kind: GenerationErrorKind::FunctionLocalItem,
                function_path: self.function_path.to_owned(),
                message: format!(
                    "function-local {} items are unsupported",
                    local_item_kind(item)
                ),
            });
            return;
        }
        if matches!(stmt.kind, StmtKind::Empty) {
            self.error.get_or_insert_with(|| GenerationError {
                kind: GenerationErrorKind::EmptyStatement,
                function_path: self.function_path.to_owned(),
                message: "empty statement cannot be annotated".to_owned(),
            });
            return;
        }
        visit::walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        if self.error.is_some() {
            return;
        }
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
        visit::walk_expr(self, expr);
    }
}

fn validate_function_body(item: &Item, path: &str) -> Result<(), GenerationError> {
    let mut validator = BodyValidator {
        function_path: path,
        error: None,
    };
    let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
    validator.visit_block(function.body.as_ref().unwrap());
    validator.error.map_or(Ok(()), Err)
}

struct Labeler<'a> {
    next: u32,
    opaque_nested_ifs: &'a FxHashSet<NodeId>,
}

impl MutVisitor for Labeler<'_> {
    fn flat_map_stmt(&mut self, mut stmt: Stmt) -> SmallVec<[Stmt; 1]> {
        if matches!(stmt.kind, StmtKind::Item(_) | StmtKind::Empty) {
            return smallvec![stmt];
        }
        stmt_attrs_mut(&mut stmt).extend(utils::attr!("#[proctor({})]", self.next));
        self.next += 1;
        mut_visit::walk_flat_map_stmt(self, stmt)
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if self.opaque_nested_ifs.contains(&expr.id) {
            return;
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

fn annotate_function(item: &mut Item, opaque_nested_ifs: &FxHashSet<NodeId>) {
    let mut labeler = Labeler {
        next: 0,
        opaque_nested_ifs,
    };
    let ItemKind::Fn(box function) = &mut item.kind else { unreachable!() };
    labeler.visit_block(function.body.as_mut().unwrap());
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

struct PresentationBindingNormalizer;

impl MutVisitor for PresentationBindingNormalizer {
    fn visit_pat(&mut self, pat: &mut Pat) {
        if let PatKind::Ident(BindingMode(by_ref, mutability), ..) = &mut pat.kind
            && *by_ref == ByRef::No
        {
            *mutability = Mutability::Mut;
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

fn classify_function_statements(
    item: &Item,
    opaque_nested_ifs: &FxHashSet<NodeId>,
    ast_to_hir: &utils::ir::AstToHir,
    decisions: &InitialPointerDecisions,
    preservation_overrides: &PreservationDecisionOverrides,
    tcx: TyCtxt<'_>,
) -> BTreeSet<u32> {
    let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
    let mut classifier = StatementClassifier {
        ast_to_hir,
        decisions,
        preservation_overrides,
        opaque_nested_ifs,
        tcx,
        transformed: BTreeSet::new(),
    };
    classifier.visit_block(
        function
            .body
            .as_ref()
            .expect("source-defined function has a body"),
    );
    classifier.transformed
}

struct StatementClassifier<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    decisions: &'a InitialPointerDecisions,
    preservation_overrides: &'a PreservationDecisionOverrides,
    opaque_nested_ifs: &'a FxHashSet<NodeId>,
    tcx: TyCtxt<'tcx>,
    transformed: BTreeSet<u32>,
}

impl<'ast> visit::Visitor<'ast> for StatementClassifier<'_, '_> {
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        let label = statement_numeric_label(statement)
            .expect("generation assigned every statement a label");
        if !statement_is_preservable(
            statement,
            self.ast_to_hir,
            self.decisions,
            self.preservation_overrides,
            self.tcx,
        ) {
            self.transformed.insert(label);
        }
        visit::walk_stmt(self, statement);
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if self.opaque_nested_ifs.contains(&expression.id) {
            return;
        }
        visit::walk_expr(self, expression);
    }
}

fn statement_is_preservable(
    statement: &Stmt,
    ast_to_hir: &utils::ir::AstToHir,
    decisions: &InitialPointerDecisions,
    preservation_overrides: &PreservationDecisionOverrides,
    tcx: TyCtxt<'_>,
) -> bool {
    let mut surface = SurfacePreservationCheck {
        ast_to_hir,
        tcx,
        preservable: true,
    };
    surface.visit_stmt(statement);
    if !surface.preservable {
        return false;
    }
    let Some(hir_node) = ast_to_hir.get_local_node(statement.id, tcx) else {
        return false;
    };
    let owner = match hir_node {
        hir::Node::Stmt(statement) => statement.hir_id.owner,
        hir::Node::Expr(expression) => expression.hir_id.owner,
        _ => return false,
    };
    let mut hir = HirPreservationCheck {
        tcx,
        decisions,
        preservation_overrides,
        owner,
        direct_callee: None,
        preservable: true,
        sensitive_types: FxHashMap::default(),
        visiting_types: FxHashSet::default(),
    };
    match hir_node {
        hir::Node::Stmt(statement) => hir.visit_stmt(statement),
        hir::Node::Expr(expression) => hir.visit_expr(expression),
        _ => unreachable!(),
    }
    hir.preservable
}

struct SurfacePreservationCheck<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    preservable: bool,
}

impl<'ast> visit::Visitor<'ast> for SurfacePreservationCheck<'_, '_> {
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        if !self.ast_to_hir.local_map.contains_key(&statement.id)
            || matches!(statement.kind, StmtKind::MacCall(..))
        {
            self.preservable = false;
        }
        visit::walk_stmt(self, statement);
    }

    fn visit_local(&mut self, local: &'ast rustc_ast::Local) {
        if self.ast_to_hir.get_let_stmt(local.id, self.tcx).is_none() {
            self.preservable = false;
        }
        visit::walk_local(self, local);
    }

    fn visit_pat(&mut self, pattern: &'ast Pat) {
        if self.ast_to_hir.get_pat(pattern.id, self.tcx).is_none() {
            self.preservable = false;
        }
        visit::walk_pat(self, pattern);
    }

    fn visit_ty(&mut self, ty: &'ast Ty) {
        if self.ast_to_hir.get_ty(ty.id, self.tcx).is_none() {
            self.preservable = false;
        }
        visit::walk_ty(self, ty);
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if self.ast_to_hir.get_expr(expression.id, self.tcx).is_none()
            || matches!(
                expression.kind,
                ExprKind::MacCall(..)
                    | ExprKind::Closure(..)
                    | ExprKind::InlineAsm(..)
                    | ExprKind::Try(..)
                    | ExprKind::Await(..)
            )
        {
            self.preservable = false;
        }
        visit::walk_expr(self, expression);
    }

    fn visit_mac_call(&mut self, _mac: &'ast rustc_ast::MacCall) {
        self.preservable = false;
    }
}

struct HirPreservationCheck<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    decisions: &'a InitialPointerDecisions,
    preservation_overrides: &'a PreservationDecisionOverrides,
    owner: hir::OwnerId,
    direct_callee: Option<HirId>,
    preservable: bool,
    sensitive_types: FxHashMap<ty::Ty<'tcx>, bool>,
    visiting_types: FxHashSet<ty::Ty<'tcx>>,
}

impl<'tcx> HirPreservationCheck<'tcx, '_> {
    fn reject(&mut self) {
        self.preservable = false;
    }

    fn check_type(&mut self, ty: ty::Ty<'tcx>) {
        if self.type_is_sensitive(ty) {
            self.reject();
        }
    }

    fn type_is_sensitive(&mut self, ty: ty::Ty<'tcx>) -> bool {
        if let Some(result) = self.sensitive_types.get(&ty) {
            return *result;
        }
        if !self.visiting_types.insert(ty) {
            return false;
        }
        let sensitive = match ty.kind() {
            ty::TyKind::Bool
            | ty::TyKind::Char
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Float(_)
            | ty::TyKind::Str
            | ty::TyKind::Never => false,
            ty::TyKind::RawPtr(..) => true,
            ty::TyKind::Ref(_, inner, _) | ty::TyKind::Slice(inner) => {
                self.type_is_sensitive(*inner)
            }
            ty::TyKind::Array(inner, _) => self.type_is_sensitive(*inner),
            ty::TyKind::Tuple(types) => types.iter().any(|ty| self.type_is_sensitive(ty)),
            ty::TyKind::Adt(definition, arguments) => {
                let arguments_sensitive = arguments
                    .types()
                    .any(|argument| self.type_is_sensitive(argument));
                arguments_sensitive
                    || (definition.did().is_local()
                        && definition.variants().iter().any(|variant| {
                            variant.fields.iter().any(|field| {
                                self.preservation_overrides
                                    .changed_fields
                                    .contains(&field.did)
                                    || self.type_is_sensitive(field.ty(self.tcx, arguments))
                            })
                        }))
            }
            ty::TyKind::FnDef(def_id, arguments) => {
                self.callable_signature_is_sensitive(*def_id, arguments)
            }
            ty::TyKind::FnPtr(signature, _) => signature
                .skip_binder()
                .inputs_and_output
                .iter()
                .any(|ty| self.type_is_sensitive(ty)),
            ty::TyKind::Alias(..)
            | ty::TyKind::Param(..)
            | ty::TyKind::Bound(..)
            | ty::TyKind::Placeholder(..)
            | ty::TyKind::Infer(..)
            | ty::TyKind::Error(..)
            | ty::TyKind::Dynamic(..)
            | ty::TyKind::Foreign(..)
            | ty::TyKind::Closure(..)
            | ty::TyKind::CoroutineClosure(..)
            | ty::TyKind::Coroutine(..)
            | ty::TyKind::CoroutineWitness(..)
            | ty::TyKind::UnsafeBinder(..)
            | ty::TyKind::Pat(..) => true,
        };
        self.visiting_types.remove(&ty);
        self.sensitive_types.insert(ty, sensitive);
        sensitive
    }

    fn callable_signature_is_sensitive(
        &mut self,
        def_id: DefId,
        arguments: ty::GenericArgsRef<'tcx>,
    ) -> bool {
        self.tcx
            .fn_sig(def_id)
            .instantiate(self.tcx, arguments)
            .skip_binder()
            .inputs_and_output
            .iter()
            .any(|ty| self.type_is_sensitive(ty))
    }

    fn binding_changes(&self, hir_id: HirId) -> bool {
        let Some(decision) = self.decisions.bindings.get(&hir_id).copied() else {
            return false;
        };
        let source = self.tcx.typeck(hir_id.owner).node_type(hir_id);
        decision_changes_type(decision, source)
    }

    fn local_signature_changes(&self, def_id: LocalDefId) -> bool {
        if self
            .preservation_overrides
            .changed_local_signatures
            .contains(&def_id)
        {
            return true;
        }
        let signature = self.tcx.fn_sig(def_id).instantiate_identity().skip_binder();
        if self.tcx.item_name(def_id.to_def_id()).as_str() == "main_0"
            && signature.inputs().len() == 2
        {
            return true;
        }
        let Some(decision) = self.decisions.signatures.data.get(&def_id) else {
            return false;
        };
        decision
            .input_decs
            .iter()
            .zip(signature.inputs())
            .any(|(decision, source)| {
                decision.is_some_and(|decision| decision_changes_type(decision, *source))
            })
            || decision
                .output_dec
                .is_some_and(|decision| decision_changes_type(decision, signature.output()))
    }

    fn check_callable(&mut self, def_id: DefId, arguments: ty::GenericArgsRef<'tcx>) {
        if self.tcx.is_foreign_item(def_id) {
            self.reject();
            return;
        }
        let signature = self
            .tcx
            .fn_sig(def_id)
            .instantiate(self.tcx, arguments)
            .skip_binder();
        if !def_id.is_local() && signature.safety.is_unsafe() {
            self.reject();
        }
        if let Some(local) = def_id.as_local()
            && self.local_signature_changes(local)
        {
            self.reject();
        }
        if signature
            .inputs_and_output
            .iter()
            .any(|ty| self.type_is_sensitive(ty))
        {
            self.reject();
        }
    }

    fn check_expression_types(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        let typeck = self.tcx.typeck(self.owner);
        self.check_type(typeck.expr_ty(expression));
        self.check_type(typeck.expr_ty_adjusted(expression));
        for adjustment in typeck.expr_adjustments(expression) {
            self.check_type(adjustment.target);
        }
    }

    fn check_overloaded_operation(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        let typeck = self.tcx.typeck(self.owner);
        if let Some(def_id) = typeck.type_dependent_def_id(expression.hir_id) {
            let arguments = typeck.node_args(expression.hir_id);
            self.check_callable(def_id, arguments);
        }
    }
}

impl<'tcx> Visitor<'tcx> for HirPreservationCheck<'tcx, '_> {
    fn visit_stmt(&mut self, statement: &'tcx hir::Stmt<'tcx>) {
        if !self.preservable {
            return;
        }
        intravisit::walk_stmt(self, statement);
    }

    fn visit_pat(&mut self, pattern: &'tcx hir::Pat<'tcx>) {
        let typeck = self.tcx.typeck(self.owner);
        self.check_type(typeck.node_type(pattern.hir_id));
        if self.binding_changes(pattern.hir_id) {
            self.reject();
        }
        intravisit::walk_pat(self, pattern);
    }

    fn visit_ty(&mut self, ty: &'tcx hir::Ty<'tcx, hir::AmbigArg>) {
        self.check_type(self.tcx.typeck(self.owner).node_type(ty.hir_id));
        intravisit::walk_ty(self, ty);
    }

    fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        if !self.preservable {
            return;
        }
        self.check_expression_types(expression);
        let typeck = self.tcx.typeck(self.owner);
        match expression.kind {
            hir::ExprKind::Call(callee, arguments) => {
                let callee_ty = typeck.expr_ty(callee);
                let ty::TyKind::FnDef(def_id, generic_arguments) = callee_ty.kind() else {
                    self.reject();
                    return;
                };
                self.check_callable(*def_id, generic_arguments);
                let previous = self.direct_callee.replace(callee.hir_id);
                self.visit_expr(callee);
                self.direct_callee = previous;
                for argument in arguments {
                    self.visit_expr(argument);
                }
                return;
            }
            hir::ExprKind::MethodCall(_, receiver, arguments, _) => {
                let Some(def_id) = typeck.type_dependent_def_id(expression.hir_id) else {
                    self.reject();
                    return;
                };
                self.check_callable(def_id, typeck.node_args(expression.hir_id));
                self.visit_expr(receiver);
                for argument in arguments {
                    self.visit_expr(argument);
                }
                return;
            }
            hir::ExprKind::Path(ref path) => {
                match typeck.qpath_res(path, expression.hir_id) {
                    Res::Local(hir_id) if self.binding_changes(hir_id) => self.reject(),
                    Res::Def(
                        DefKind::Static {
                            mutability: hir::Mutability::Mut,
                            ..
                        },
                        _,
                    ) => self.reject(),
                    _ => {}
                }
                if matches!(typeck.expr_ty(expression).kind(), ty::TyKind::FnDef(..))
                    && self.direct_callee != Some(expression.hir_id)
                {
                    self.reject();
                }
            }
            hir::ExprKind::Field(base, _) => {
                let base_ty = typeck.expr_ty_adjusted(base).peel_refs();
                if let ty::TyKind::Adt(definition, _) = base_ty.kind()
                    && definition.is_union()
                {
                    self.reject();
                }
            }
            hir::ExprKind::Closure(..) | hir::ExprKind::InlineAsm(..) => self.reject(),
            hir::ExprKind::Match(_, _, hir::MatchSource::TryDesugar(_)) => self.reject(),
            hir::ExprKind::Binary(..)
            | hir::ExprKind::Unary(..)
            | hir::ExprKind::Index(..)
            | hir::ExprKind::AssignOp(..) => self.check_overloaded_operation(expression),
            _ => {}
        }
        intravisit::walk_expr(self, expression);
    }
}

fn decision_changes_type(decision: PtrKind, source: ty::Ty<'_>) -> bool {
    let ty::TyKind::RawPtr(_, source_mutability) = source.kind() else {
        // Pointer replacement decisions are only materialized for source raw
        // pointers. The analysis map can also contain propagated decisions for
        // already-safe references, which do not change their source type.
        return false;
    };
    match decision {
        PtrKind::Raw(target_mutability) => target_mutability != source_mutability.is_mut(),
        _ => true,
    }
}

struct Skeletonizer<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    decisions: &'a InitialPointerDecisions,
    statements_requiring_transformation: &'a BTreeSet<u32>,
    tcx: TyCtxt<'tcx>,
}

impl MutVisitor for Skeletonizer<'_, '_> {
    fn flat_map_stmt(&mut self, mut stmt: Stmt) -> SmallVec<[Stmt; 1]> {
        let requires_transformation = statement_numeric_label(&stmt)
            .is_none_or(|label| self.statements_requiring_transformation.contains(&label));
        if let StmtKind::Let(local) = &mut stmt.kind
            && let PatKind::Ident(_, _, None) = local.pat.kind
            && let Some(hir_id) = self.ast_to_hir.local_map.get(&local.pat.id).copied()
        {
            let inferred = self.tcx.typeck(hir_id.owner).node_type(hir_id);
            let decision = inferred
                .is_raw_ptr()
                .then(|| self.decisions.bindings.get(&hir_id).copied())
                .flatten();
            let ty = match (decision, local.ty.as_deref()) {
                (Some(kind), Some(ty)) if raw_decision_matches_inferred_type(kind, inferred) => {
                    Some(ty.clone())
                }
                (Some(kind), _) => Some(target_type(inferred, kind, None, self.tcx)),
                (None, Some(ty)) => Some(ty.clone()),
                (None, None)
                    if !matches!(
                        inferred.kind(),
                        ty::TyKind::FnDef(..)
                            | ty::TyKind::FnPtr(..)
                            | ty::TyKind::Closure(..)
                            | ty::TyKind::CoroutineClosure(..)
                            | ty::TyKind::Coroutine(..)
                            | ty::TyKind::CoroutineWitness(..)
                    ) =>
                {
                    Some(utils::ast::parse_ty(inferred.to_string()))
                }
                (None, None) => None,
            };
            local.ty = ty.map(P);
        }
        if !requires_transformation {
            return smallvec![stmt];
        }
        match &mut stmt.kind {
            StmtKind::Let(local) => match &mut local.kind {
                LocalKind::Decl => {}
                LocalKind::Init(init) => skeletonize_payload(init, self),
                LocalKind::InitElse(init, else_block) => {
                    skeletonize_payload(init, self);
                    self.visit_block(else_block);
                }
            },
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                skeletonize_statement_expr(expr, self);
            }
            StmtKind::Item(_) | StmtKind::Empty => {}
            StmtKind::MacCall(mac) => {
                debug_assert!(requires_transformation);
                let mut expr = todo_expr();
                expr.attrs = std::mem::take(&mut mac.attrs);
                stmt.kind = StmtKind::Semi(P(expr));
            }
        }
        smallvec![stmt]
    }
}

fn statement_numeric_label(statement: &Stmt) -> Option<u32> {
    let attributes = match &statement.kind {
        StmtKind::Let(local) => &local.attrs,
        StmtKind::Item(item) => &item.attrs,
        StmtKind::Expr(expression) | StmtKind::Semi(expression) => &expression.attrs,
        StmtKind::MacCall(mac) => &mac.attrs,
        StmtKind::Empty => return None,
    };
    attributes.iter().find_map(|attribute| {
        let AttrKind::Normal(normal) = &attribute.kind else {
            return None;
        };
        let rendered = pprust::attribute_to_string(attribute);
        (normal.item.path.segments.len() == 1
            && normal.item.path.segments[0].ident.name.as_str() == "proctor")
            .then(|| {
                rendered
                    .strip_prefix("#[proctor(")?
                    .strip_suffix(")]")?
                    .parse::<u32>()
                    .ok()
            })
            .flatten()
    })
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

fn contains_let_expression(expr: &Expr) -> bool {
    struct Finder {
        found: bool,
    }

    impl<'ast> visit::Visitor<'ast> for Finder {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            if matches!(expr.kind, ExprKind::Let(..)) {
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

fn is_restricted_conditional(expr: &Expr) -> bool {
    let ExprKind::If(condition, then_block, Some(else_expr)) = &expr.kind else {
        return false;
    };
    if contains_let_expression(condition) || contains_control_expression(condition) {
        return false;
    }
    restricted_branch(then_block)
        && match &else_expr.kind {
            ExprKind::If(..) => is_restricted_conditional(else_expr),
            ExprKind::Block(block, _) => restricted_branch(block),
            _ => false,
        }
}

fn restricted_branch(block: &rustc_ast::Block) -> bool {
    let [statement] = &block.stmts[..] else {
        return false;
    };
    let StmtKind::Expr(tail) = &statement.kind else {
        return false;
    };
    if is_preserved_expression(tail) {
        is_restricted_conditional(tail)
    } else {
        !contains_control_expression(tail)
    }
}

fn inspect_nested_control(expr: &Expr, mut on_restricted: impl FnMut(NodeId)) -> bool {
    struct Finder<'a, F> {
        on_restricted: &'a mut F,
        invalid: bool,
    }

    impl<'ast, F: FnMut(NodeId)> visit::Visitor<'ast> for Finder<'_, F> {
        fn visit_expr(&mut self, expr: &'ast Expr) {
            if self.invalid {
                return;
            }
            if is_preserved_expression(expr) {
                if is_restricted_conditional(expr) {
                    (self.on_restricted)(expr.id);
                } else {
                    self.invalid = true;
                }
                return;
            }
            visit::walk_expr(self, expr);
        }
    }

    let mut finder = Finder {
        on_restricted: &mut on_restricted,
        invalid: false,
    };
    finder.visit_expr(expr);
    finder.invalid
}

struct OpaqueNestedIfCollector<'a> {
    function_path: &'a str,
    opaque_nested_ifs: FxHashSet<NodeId>,
    error: Option<GenerationError>,
}

impl OpaqueNestedIfCollector<'_> {
    fn inspect_block(&mut self, block: &rustc_ast::Block) {
        for statement in &block.stmts {
            self.inspect_statement(statement);
            if self.error.is_some() {
                return;
            }
        }
    }

    fn inspect_statement(&mut self, statement: &Stmt) {
        match &statement.kind {
            StmtKind::Let(local) => match &local.kind {
                LocalKind::Decl => {}
                LocalKind::Init(initializer) => self.inspect_payload(initializer),
                LocalKind::InitElse(initializer, else_block) => {
                    self.inspect_payload(initializer);
                    self.inspect_block(else_block);
                }
            },
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => self.inspect_statement_expression(expr),
            StmtKind::Item(_) | StmtKind::MacCall(_) | StmtKind::Empty => {}
        }
    }

    fn inspect_statement_expression(&mut self, expr: &Expr) {
        if is_preserved_expression(expr) {
            self.inspect_control(expr);
            return;
        }
        match &expr.kind {
            ExprKind::Ret(value) | ExprKind::Break(_, value) => {
                if let Some(value) = value {
                    self.inspect_payload(value);
                }
            }
            ExprKind::Continue(_) => {}
            _ => self.inspect_non_control(expr),
        }
    }

    fn inspect_payload(&mut self, expr: &Expr) {
        if is_preserved_expression(expr) {
            self.inspect_control(expr);
        } else {
            self.inspect_non_control(expr);
        }
    }

    fn inspect_non_control(&mut self, expr: &Expr) {
        if inspect_nested_control(expr, |id| {
            self.opaque_nested_ifs.insert(id);
        }) {
            self.error.get_or_insert_with(|| GenerationError {
                kind: GenerationErrorKind::NestedControlPayload,
                function_path: self.function_path.to_owned(),
                message: "control expression nested beneath a non-control payload".to_owned(),
            });
        }
    }

    fn inspect_control(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::If(condition, then_block, else_expr) => {
                self.inspect_non_control(condition);
                self.inspect_block(then_block);
                if let Some(else_expr) = else_expr {
                    self.inspect_payload(else_expr);
                }
            }
            ExprKind::While(condition, body, _) => {
                self.inspect_non_control(condition);
                self.inspect_block(body);
            }
            ExprKind::ForLoop { iter, body, .. } => {
                self.inspect_non_control(iter);
                self.inspect_block(body);
            }
            ExprKind::Loop(body, ..) | ExprKind::Block(body, ..) => self.inspect_block(body),
            ExprKind::Match(scrutinee, arms, _) => {
                self.inspect_non_control(scrutinee);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.inspect_non_control(guard);
                    }
                    self.inspect_payload(arm.body.as_ref().unwrap());
                }
            }
            _ => unreachable!(),
        }
    }
}

fn collect_opaque_nested_ifs(
    item: &Item,
    path: &str,
) -> Result<FxHashSet<NodeId>, GenerationError> {
    let mut collector = OpaqueNestedIfCollector {
        function_path: path,
        opaque_nested_ifs: FxHashSet::default(),
        error: None,
    };
    let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
    collector.inspect_block(function.body.as_ref().unwrap());
    match collector.error {
        Some(error) => Err(error),
        None => Ok(collector.opaque_nested_ifs),
    }
}

fn skeletonize_payload(expr: &mut Expr, visitor: &mut Skeletonizer<'_, '_>) {
    if is_preserved_expression(expr) {
        skeletonize_control(expr, visitor);
    } else {
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

fn skeletonize_condition(expr: &mut Expr) {
    if let ExprKind::Let(_, value, _, _) = &mut expr.kind {
        **value = todo_expr();
    } else {
        replace_with_todo(expr);
    }
}

fn skeletonize_control(expr: &mut Expr, visitor: &mut Skeletonizer<'_, '_>) {
    match &mut expr.kind {
        ExprKind::If(condition, then_block, else_expr) => {
            skeletonize_condition(condition);
            visitor.visit_block(then_block);
            if let Some(else_expr) = else_expr {
                skeletonize_payload(else_expr, visitor);
            }
        }
        ExprKind::While(condition, body, _) => {
            skeletonize_condition(condition);
            visitor.visit_block(body);
        }
        ExprKind::ForLoop { iter, body, .. } => {
            **iter = todo_expr();
            visitor.visit_block(body);
        }
        ExprKind::Loop(body, ..) | ExprKind::Block(body, ..) => visitor.visit_block(body),
        ExprKind::Match(scrutinee, arms, _) => {
            **scrutinee = todo_expr();
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
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
