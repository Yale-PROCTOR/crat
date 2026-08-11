use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
};

use pointer_replacer::{
    InitialPointerDecisions, PointerDecisionOptions, PtrKind, initial_pointer_decisions,
};
use rustc_ast::{
    AttrKind, BindingMode, ByRef, Crate, Expr, ExprKind, Extern, FnRetTy, GenericParamKind, Item,
    ItemKind, LocalKind, Mutability, NodeId, Pat, PatKind, Safety, Stmt, StmtKind, Ty, TyKind,
    mut_visit, mut_visit::MutVisitor, ptr::P, visit, visit::Visitor as _,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId,
    def::{DefKind, Namespace, Res},
    intravisit::{self, Visitor, VisitorExt},
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, TyCtxt},
};
use rustc_span::{
    DUMMY_SP, Ident, Symbol,
    def_id::{CRATE_DEF_ID, DefId, LocalDefId},
    sym,
};
use serde::{Deserialize, Serialize};
use smallvec::{SmallVec, smallvec};

use crate::{
    AdtIdentity, AdtKind, BinaryOperator, BindingMutability, BorrowKind, ByRefKind, Expression,
    FieldIdentity, Literal, LoadedRuleSet, Pattern, PointerVariableMetadata, PointerVariableOrigin,
    RangeLimits, RawMutability, RefMutability, RuleDocument, RuleMatchInput, SkeletonView,
    Statement, StatementPairMetadata, TypeTree, UnaryOperator, ValueIdentity, VariantIdentity,
    observation::{select_rule_regions, semantic_type_tree},
    preservation::{make_disposition_forest, validate_cross_view_topology},
    validator::validate_rule_application_shape,
};

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
    pub baseline: SkeletonView,
    pub applied: SkeletonView,
    pub source_signature: String,
    pub target_signature: String,
    pub foreign_function_names: Vec<String>,
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
    Function(Box<FunctionRecord>),
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
    TypeSpelling,
    UnsupportedGeneric,
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
    make_skeletons_with_rules(source, None, tcx)
}

pub fn make_skeletons_with_rules(
    source: &str,
    rules: Option<&RuleDocument>,
    tcx: TyCtxt<'_>,
) -> Result<Vec<ItemRecord>, GenerationError> {
    make_skeletons_with_preservation_overrides(
        source,
        rules,
        tcx,
        &PreservationDecisionOverrides::default(),
    )
}

fn make_skeletons_with_preservation_overrides(
    source: &str,
    rules: Option<&RuleDocument>,
    tcx: TyCtxt<'_>,
    preservation_overrides: &PreservationDecisionOverrides,
) -> Result<Vec<ItemRecord>, GenerationError> {
    let mut surface = utils::ast::parse_crate(source.to_owned());
    reject_unsupported_function_generics(&surface.items, &mut vec![])?;
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
                rules,
                tcx,
            )
        })
        .collect()
}

fn reject_unsupported_function_generics(
    items: &[P<Item>],
    path: &mut Vec<String>,
) -> Result<(), GenerationError> {
    for item in items {
        if let ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(children, ..)) = &item.kind {
            path.push(ident.to_string());
            reject_unsupported_function_generics(children, path)?;
            path.pop();
            continue;
        }
        let ItemKind::Fn(box function) = &item.kind else {
            continue;
        };
        let name = item.kind.ident().unwrap().to_string();
        if name == "main" {
            continue;
        }
        let Some(parameter) = function
            .generics
            .params
            .iter()
            .find(|parameter| !matches!(parameter.kind, GenericParamKind::Lifetime))
        else {
            continue;
        };
        let function_path = path
            .iter()
            .cloned()
            .chain(std::iter::once(name))
            .collect::<Vec<_>>()
            .join("::");
        let kind = match parameter.kind {
            GenericParamKind::Type { .. } => "type",
            GenericParamKind::Const { .. } => "const",
            GenericParamKind::Lifetime => unreachable!(),
        };
        return Err(GenerationError {
            kind: GenerationErrorKind::UnsupportedGeneric,
            function_path: function_path.clone(),
            message: format!(
                "source-defined transformable function `{function_path}` declares an unsupported {kind} generic parameter"
            ),
        });
    }
    Ok(())
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
    rules: Option<&RuleDocument>,
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
            rules,
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

fn make_function_record<'tcx>(
    surface: SurfaceItem,
    ast_to_hir: &utils::ir::AstToHir,
    item_ids: &FxHashMap<rustc_span::def_id::DefId, u64>,
    decisions: &InitialPointerDecisions,
    preservation_overrides: &PreservationDecisionOverrides,
    rules: Option<&RuleDocument>,
    tcx: TyCtxt<'tcx>,
) -> Result<ItemRecord, GenerationError> {
    let hitem = tcx.hir_node_by_def_id(surface.def_id).expect_item();
    let signature_dependencies = collect_signature_dependencies(hitem, item_ids, tcx);
    let dependencies = collect_dependencies(hitem, item_ids, tcx);
    let foreign_function_names = collect_foreign_function_names(hitem, tcx);
    let mut source = surface.item.clone();
    sanitize_item(&mut source);
    validate_function_body(&source, &surface.path)?;
    let opaque_nested_ifs = collect_opaque_nested_ifs(&source, &surface.path)?;
    annotate_function(&mut source, &opaque_nested_ifs);
    PresentationBindingNormalizer.visit_item(&mut source);
    let statement_classification = classify_function_statements(
        &source,
        &opaque_nested_ifs,
        ast_to_hir,
        decisions,
        preservation_overrides,
        tcx,
    );
    let statements_requiring_transformation = statement_classification.transformed;
    let preserved_shell_statements = statement_classification.preserved_shells;
    let mut target = source.clone();
    let type_speller = TypeSpeller::new(surface.def_id, ast_to_hir, tcx);
    apply_target_signature(
        &mut target,
        surface.def_id,
        decisions,
        &type_speller,
        &surface.path,
        tcx,
    )?;
    let mut applied_target = target.clone();
    let rule_applied_statements = match rules {
        Some(rules) => apply_rule_set(
            &source,
            &mut applied_target,
            &statements_requiring_transformation,
            rules,
            surface.def_id,
            decisions,
            ast_to_hir,
            &type_speller,
            tcx,
        )?,
        None => BTreeSet::new(),
    };
    let applied_transformations = statements_requiring_transformation
        .difference(&rule_applied_statements)
        .copied()
        .collect::<BTreeSet<_>>();
    let mut baseline_skeleton = target.clone();
    let no_rule_applications = BTreeSet::new();
    let mut skeletonizer = Skeletonizer {
        ast_to_hir,
        decisions,
        statements_requiring_transformation: &statements_requiring_transformation,
        preserved_shell_statements: &preserved_shell_statements,
        rule_applied_statements: &no_rule_applications,
        type_speller: &type_speller,
        function_path: &surface.path,
        error: None,
        tcx,
    };
    skeletonizer.visit_item(&mut baseline_skeleton);
    if let Some(error) = skeletonizer.error {
        return Err(error);
    }
    let mut applied_skeleton = applied_target;
    let mut applied_skeletonizer = Skeletonizer {
        ast_to_hir,
        decisions,
        statements_requiring_transformation: &applied_transformations,
        preserved_shell_statements: &preserved_shell_statements,
        rule_applied_statements: &rule_applied_statements,
        type_speller: &type_speller,
        function_path: &surface.path,
        error: None,
        tcx,
    };
    applied_skeletonizer.visit_item(&mut applied_skeleton);
    if let Some(error) = applied_skeletonizer.error {
        return Err(error);
    }
    if let Some(label) = statements_requiring_transformation.iter().find(|label| {
        !applied_transformations.contains(label) && !rule_applied_statements.contains(label)
    }) {
        return Err(GenerationError {
            kind: GenerationErrorKind::AstHirMismatch,
            function_path: surface.path.clone(),
            message: format!(
                "baseline transform label {label} became preserved in the applied view"
            ),
        });
    }
    validate_cross_view_topology(&baseline_skeleton, &applied_skeleton).map_err(|error| {
        GenerationError {
            kind: GenerationErrorKind::AstHirMismatch,
            function_path: surface.path.clone(),
            message: error.message,
        }
    })?;
    let source_signature = render_signature(&source);
    let target_signature = render_signature(&baseline_skeleton);
    let baseline_statement_pair_metadata = collect_statement_pair_metadata(
        &source,
        &baseline_skeleton,
        &statements_requiring_transformation,
        ast_to_hir,
        &type_speller,
        &surface.path,
        tcx,
    )?;
    let applied_statement_pair_metadata = collect_statement_pair_metadata(
        &source,
        &applied_skeleton,
        &applied_transformations,
        ast_to_hir,
        &type_speller,
        &surface.path,
        tcx,
    )?;
    let transformed = statements_requiring_transformation
        .iter()
        .copied()
        .collect::<std::collections::HashSet<_>>();
    let preserved_shells = preserved_shell_statements
        .iter()
        .copied()
        .collect::<HashSet<_>>();
    let dispositions = make_disposition_forest(
        &baseline_skeleton,
        &transformed,
        &preserved_shells,
        &HashSet::new(),
    )
    .map_err(|error| GenerationError {
        kind: GenerationErrorKind::AstHirMismatch,
        function_path: surface.path.clone(),
        message: error.message,
    })?;
    let baseline = SkeletonView {
        skeleton: render_annotated_item(&baseline_skeleton),
        needs_transformation: !transformed.is_empty(),
        statement_dispositions: dispositions,
        statement_pair_metadata: baseline_statement_pair_metadata,
    };
    let applied_transformed = applied_transformations
        .iter()
        .copied()
        .collect::<HashSet<_>>();
    let applied_rules = rule_applied_statements
        .iter()
        .copied()
        .collect::<HashSet<_>>();
    let applied_dispositions = make_disposition_forest(
        &applied_skeleton,
        &applied_transformed,
        &preserved_shells,
        &applied_rules,
    )
    .map_err(|error| GenerationError {
        kind: GenerationErrorKind::AstHirMismatch,
        function_path: surface.path.clone(),
        message: error.message,
    })?;
    let applied = SkeletonView {
        skeleton: render_annotated_item(&applied_skeleton),
        needs_transformation: !applied_transformations.is_empty(),
        statement_dispositions: applied_dispositions,
        statement_pair_metadata: applied_statement_pair_metadata,
    };
    let name = surface.item.kind.ident().unwrap().to_string();
    Ok(ItemRecord::Function(Box::new(FunctionRecord {
        id: surface.id,
        path: surface.path,
        kind: ItemKindName::Fn,
        name,
        annotated_source: render_annotated_item(&source),
        baseline: baseline.clone(),
        applied,
        source_signature,
        target_signature,
        foreign_function_names,
        signature_dependencies,
        dependencies,
    })))
}

fn collect_statement_pair_metadata<'tcx>(
    source: &Item,
    skeleton: &Item,
    transformed: &BTreeSet<u32>,
    ast_to_hir: &utils::ir::AstToHir,
    type_speller: &TypeSpeller<'_, 'tcx>,
    function_path: &str,
    tcx: TyCtxt<'tcx>,
) -> Result<Vec<StatementPairMetadata>, GenerationError> {
    let catalog = collect_pointer_binding_catalog(
        source,
        skeleton,
        ast_to_hir,
        type_speller,
        function_path,
        tcx,
    )?;
    let ItemKind::Fn(box function) = &source.kind else { unreachable!() };
    let mut statements = FxHashMap::default();
    StatementByLabelCollector {
        statements: &mut statements,
    }
    .visit_block(function.body.as_ref().unwrap());

    Ok(transformed
        .iter()
        .map(|label| {
            let statement = statements
                .get(label)
                .expect("classification labels originate in the annotated source");
            let mut collector = PointerOccurrenceCollector {
                ast_to_hir,
                catalog: &catalog,
                complete: true,
                seen: FxHashSet::default(),
                variables: vec![],
                tcx,
            };
            collector.visit_stmt(statement);
            collector.collect_hir_root(statement);
            StatementPairMetadata {
                label: *label,
                before_statement: render_statement_group(std::slice::from_ref(*statement)),
                pointer_variables_complete: collector.complete,
                pointer_variables: collector.variables,
            }
        })
        .collect())
}

struct PointerBindingCatalog {
    variables: FxHashMap<HirId, PointerVariableMetadata>,
    known_ineligible: FxHashSet<HirId>,
}

fn collect_pointer_binding_catalog<'tcx>(
    source: &Item,
    skeleton: &Item,
    ast_to_hir: &utils::ir::AstToHir,
    type_speller: &TypeSpeller<'_, 'tcx>,
    function_path: &str,
    tcx: TyCtxt<'tcx>,
) -> Result<PointerBindingCatalog, GenerationError> {
    let ItemKind::Fn(box source_function) = &source.kind else { unreachable!() };
    let ItemKind::Fn(box skeleton_function) = &skeleton.kind else { unreachable!() };
    let mut catalog = FxHashMap::default();
    for (index, (source_parameter, target_parameter)) in source_function
        .sig
        .decl
        .inputs
        .iter()
        .zip(&skeleton_function.sig.decl.inputs)
        .enumerate()
    {
        let PatKind::Ident(_, name, _) = source_parameter.pat.kind else {
            continue;
        };
        let Some(pattern_hir_id) = ast_to_hir.local_map.get(&source_parameter.pat.id).copied()
        else {
            continue;
        };
        let Some(pattern) = ast_to_hir.get_pat(source_parameter.pat.id, tcx) else {
            continue;
        };
        let hir::PatKind::Binding(_, hir_id, ..) = pattern.kind else {
            continue;
        };
        if !tcx
            .typeck(pattern_hir_id.owner)
            .node_type(pattern_hir_id)
            .is_raw_ptr()
        {
            continue;
        }
        catalog.insert(
            hir_id,
            PointerVariableMetadata {
                name: name.to_string(),
                origin: PointerVariableOrigin::Parameter {
                    index: index
                        .try_into()
                        .expect("Rust function parameter count fits in u32"),
                },
                before_type: pprust::ty_to_string(&source_parameter.ty),
                selected_target_type: pprust::ty_to_string(&target_parameter.ty),
                before_type_is_inferred: false,
            },
        );
    }

    let mut target_types = FxHashMap::default();
    TargetLocalTypeCollector {
        target_types: &mut target_types,
    }
    .visit_block(skeleton_function.body.as_ref().unwrap());
    let mut locals = SourceLocalCatalogCollector {
        ast_to_hir,
        catalog: &mut catalog,
        function_path,
        target_types: &target_types,
        type_speller,
        error: None,
        tcx,
    };
    locals.visit_block(source_function.body.as_ref().unwrap());
    if let Some(error) = locals.error {
        return Err(error);
    }
    let mut known_ineligible = FxHashSet::default();
    KnownIneligibleBindingCollector {
        ast_to_hir,
        catalog: &catalog,
        known_ineligible: &mut known_ineligible,
        tcx,
    }
    .visit_item(source);
    Ok(PointerBindingCatalog {
        variables: catalog,
        known_ineligible,
    })
}

struct KnownIneligibleBindingCollector<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    catalog: &'a FxHashMap<HirId, PointerVariableMetadata>,
    known_ineligible: &'a mut FxHashSet<HirId>,
    tcx: TyCtxt<'tcx>,
}

impl<'ast> visit::Visitor<'ast> for KnownIneligibleBindingCollector<'_, '_> {
    fn visit_pat(&mut self, pattern: &'ast Pat) {
        if let Some(pattern) = self.ast_to_hir.get_pat(pattern.id, self.tcx)
            && let hir::PatKind::Binding(_, hir_id, ..) = pattern.kind
            && !self.catalog.contains_key(&hir_id)
        {
            self.known_ineligible.insert(hir_id);
        }
        visit::walk_pat(self, pattern);
    }
}

struct TargetLocalTypeCollector<'a> {
    target_types: &'a mut FxHashMap<NodeId, String>,
}

impl<'ast> visit::Visitor<'ast> for TargetLocalTypeCollector<'_> {
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        if let StmtKind::Let(local) = &statement.kind
            && matches!(local.pat.kind, PatKind::Ident(_, _, None))
            && let Some(ty) = &local.ty
        {
            self.target_types
                .insert(local.pat.id, pprust::ty_to_string(ty));
        }
        visit::walk_stmt(self, statement);
    }
}

struct SourceLocalCatalogCollector<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    catalog: &'a mut FxHashMap<HirId, PointerVariableMetadata>,
    function_path: &'a str,
    target_types: &'a FxHashMap<NodeId, String>,
    type_speller: &'a TypeSpeller<'a, 'tcx>,
    error: Option<GenerationError>,
    tcx: TyCtxt<'tcx>,
}

impl<'ast> visit::Visitor<'ast> for SourceLocalCatalogCollector<'_, '_> {
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        if self.error.is_some() {
            return;
        }
        if let StmtKind::Let(local) = &statement.kind
            && let PatKind::Ident(_, name, None) = local.pat.kind
            && let Some(pattern_hir_id) = self.ast_to_hir.local_map.get(&local.pat.id).copied()
            && let Some(pattern) = self.ast_to_hir.get_pat(local.pat.id, self.tcx)
            && let hir::PatKind::Binding(_, hir_id, ..) = pattern.kind
        {
            let inferred = self
                .tcx
                .typeck(pattern_hir_id.owner)
                .node_type(pattern_hir_id);
            if inferred.is_raw_ptr() {
                let before_type = match &local.ty {
                    Some(ty) => pprust::ty_to_string(ty),
                    None => match self.type_speller.render_semantic_type(inferred) {
                        Ok(ty) => pprust::ty_to_string(&ty),
                        Err(reason) => {
                            self.error = Some(type_spelling_error(
                                self.function_path,
                                &format!("local `{name}`"),
                                inferred,
                                reason,
                                self.tcx,
                            ));
                            return;
                        }
                    },
                };
                let selected_target_type = self
                    .target_types
                    .get(&local.pat.id)
                    .expect("raw-pointer locals are materialized in the target skeleton")
                    .clone();
                self.catalog.insert(
                    hir_id,
                    PointerVariableMetadata {
                        name: name.to_string(),
                        origin: PointerVariableOrigin::Local {
                            declaration_label: statement_numeric_label(statement)
                                .expect("annotated source statements have labels"),
                        },
                        before_type,
                        selected_target_type,
                        before_type_is_inferred: local.ty.is_none(),
                    },
                );
            }
        }
        visit::walk_stmt(self, statement);
    }
}

struct StatementByLabelCollector<'a, 'ast> {
    statements: &'a mut FxHashMap<u32, &'ast Stmt>,
}

impl<'ast> visit::Visitor<'ast> for StatementByLabelCollector<'_, 'ast> {
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        if let Some(label) = statement_numeric_label(statement) {
            self.statements.insert(label, statement);
        }
        visit::walk_stmt(self, statement);
    }
}

struct PointerOccurrenceCollector<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    catalog: &'a PointerBindingCatalog,
    complete: bool,
    seen: FxHashSet<HirId>,
    variables: Vec<PointerVariableMetadata>,
    tcx: TyCtxt<'tcx>,
}

impl PointerOccurrenceCollector<'_, '_> {
    fn add(&mut self, hir_id: HirId) {
        if self.seen.insert(hir_id) {
            if let Some(metadata) = self.catalog.variables.get(&hir_id) {
                self.variables.push(metadata.clone());
            } else if !self.catalog.known_ineligible.contains(&hir_id)
                && self.tcx.typeck(hir_id.owner).node_type(hir_id).is_raw_ptr()
            {
                // A resolved raw-pointer identity that was absent from the
                // source catalog means its source declaration could not be
                // correlated with a stable report origin.
                self.complete = false;
            }
        }
    }

    fn collect_hir_root(&mut self, statement: &Stmt) {
        let Some(node) = self.ast_to_hir.get_local_node(statement.id, self.tcx) else {
            self.complete = false;
            return;
        };
        let mut collector = HirPointerOccurrenceCollector {
            catalog: self.catalog,
            complete: &mut self.complete,
            seen: &mut self.seen,
            variables: &mut self.variables,
            tcx: self.tcx,
        };
        match node {
            hir::Node::Stmt(statement) => collector.visit_stmt(statement),
            hir::Node::Expr(expression) => collector.visit_expr(expression),
            _ => self.complete = false,
        }
    }
}

impl<'ast> visit::Visitor<'ast> for PointerOccurrenceCollector<'_, '_> {
    fn visit_pat(&mut self, pattern: &'ast Pat) {
        if matches!(pattern.kind, PatKind::Ident(..)) {
            match self.ast_to_hir.get_pat(pattern.id, self.tcx) {
                Some(pattern) => {
                    if let hir::PatKind::Binding(_, hir_id, ..) = pattern.kind {
                        self.add(hir_id);
                    } else {
                        self.complete = false;
                    }
                }
                _ => self.complete = false,
            }
        }
        visit::walk_pat(self, pattern);
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if matches!(expression.kind, ExprKind::Path(..)) {
            let Some(hir_expression) = self.ast_to_hir.get_expr(expression.id, self.tcx) else {
                self.complete = false;
                visit::walk_expr(self, expression);
                return;
            };
            let hir::ExprKind::Path(path) = hir_expression.kind else {
                self.complete = false;
                visit::walk_expr(self, expression);
                return;
            };
            match self
                .tcx
                .typeck(hir_expression.hir_id.owner)
                .qpath_res(&path, hir_expression.hir_id)
            {
                Res::Local(hir_id) => self.add(hir_id),
                Res::Err => self.complete = false,
                _ => {}
            }
        }
        visit::walk_expr(self, expression);
    }

    fn visit_mac_call(&mut self, mac: &'ast rustc_ast::MacCall) {
        self.complete = false;
        visit::walk_mac(self, mac);
    }
}

struct HirPointerOccurrenceCollector<'a, 'tcx> {
    catalog: &'a PointerBindingCatalog,
    complete: &'a mut bool,
    seen: &'a mut FxHashSet<HirId>,
    variables: &'a mut Vec<PointerVariableMetadata>,
    tcx: TyCtxt<'tcx>,
}

impl HirPointerOccurrenceCollector<'_, '_> {
    fn add(&mut self, hir_id: HirId) {
        if self.seen.insert(hir_id) {
            if let Some(metadata) = self.catalog.variables.get(&hir_id) {
                self.variables.push(metadata.clone());
            } else if !self.catalog.known_ineligible.contains(&hir_id)
                && self.tcx.typeck(hir_id.owner).node_type(hir_id).is_raw_ptr()
            {
                *self.complete = false;
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for HirPointerOccurrenceCollector<'_, 'tcx> {
    fn visit_pat(&mut self, pattern: &'tcx hir::Pat<'tcx>) {
        if let hir::PatKind::Binding(_, hir_id, ..) = pattern.kind {
            self.add(hir_id);
        }
        intravisit::walk_pat(self, pattern);
    }

    fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Path(path) = expression.kind
            && let Res::Local(hir_id) = self
                .tcx
                .typeck(expression.hir_id.owner)
                .qpath_res(&path, expression.hir_id)
        {
            self.add(hir_id);
        }
        intravisit::walk_expr(self, expression);
    }
}

pub(crate) fn render_statement_group(statements: &[Stmt]) -> String {
    let mut item = utils::ast::parse_item("fn __proctor_statement_render() {}".to_owned());
    let ItemKind::Fn(box function) = &mut item.kind else { unreachable!() };
    function.body.as_mut().unwrap().stmts = statements.iter().cloned().collect();
    let rendered = pprust::item_to_string(&item);
    let start = rendered
        .find('{')
        .expect("synthetic function rendering has a body")
        + 1;
    let end = rendered
        .rfind('}')
        .expect("synthetic function rendering closes its body");
    let body = rendered[start..end].trim();
    body.lines()
        .map(|line| line.strip_prefix("    ").unwrap_or(line))
        .collect::<Vec<_>>()
        .join("\n")
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

pub(crate) fn annotate_function(item: &mut Item, opaque_nested_ifs: &FxHashSet<NodeId>) {
    let mut labeler = Labeler {
        next: 0,
        opaque_nested_ifs,
    };
    let ItemKind::Fn(box function) = &mut item.kind else { unreachable!() };
    labeler.visit_block(function.body.as_mut().unwrap());
}

fn apply_target_signature<'a, 'tcx>(
    item: &mut Item,
    def_id: LocalDefId,
    decisions: &InitialPointerDecisions,
    type_speller: &TypeSpeller<'a, 'tcx>,
    function_path: &str,
    tcx: TyCtxt<'tcx>,
) -> Result<(), GenerationError> {
    let ItemKind::Fn(box function) = &mut item.kind else { unreachable!() };
    let force_main_argv = is_supported_two_argument_main_0(function);
    function.sig.header.safety = Safety::Unsafe(DUMMY_SP);
    let Some(decision) = decisions.signatures.data.get(&def_id) else {
        if force_main_argv {
            function.sig.decl.inputs[1].ty = P(utils::ast::parse_ty("&mut [&mut [i8]]".to_owned()));
        }
        return Ok(());
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
        if force_main_argv && index == 1 {
            continue;
        }
        let Some(kind) = decision.input_decs.get(index).copied().flatten() else {
            continue;
        };
        if raw_decision_matches_ast_type(kind, &param.ty) {
            continue;
        }
        let original = body.local_decls[rustc_middle::mir::Local::from_usize(index + 1)].ty;
        let lifetime = decision.input_lifetimes.get(index).copied().flatten();
        let source_hint = param.ty.clone();
        *param.ty = target_type(
            original,
            kind,
            lifetime,
            Some(&source_hint),
            type_speller,
            function_path,
            &format!("parameter `{}`", parameter_name(param, index)),
        )?;
    }
    if let Some(kind) = decision.output_dec
        && let FnRetTy::Ty(output) = &mut function.sig.decl.output
        && !raw_decision_matches_ast_type(kind, output)
    {
        let original = body.local_decls[rustc_middle::mir::RETURN_PLACE].ty;
        let source_hint = output.clone();
        **output = target_type(
            original,
            kind,
            decision.output_lifetime,
            Some(&source_hint),
            type_speller,
            function_path,
            "return",
        )?;
    }
    if force_main_argv {
        function.sig.decl.inputs[1].ty = P(utils::ast::parse_ty("&mut [&mut [i8]]".to_owned()));
    }
    Ok(())
}

fn parameter_name(param: &rustc_ast::Param, index: usize) -> String {
    match &param.pat.kind {
        PatKind::Ident(_, ident, _) => ident.to_string(),
        _ => format!("#{index}"),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ConstructorRequirements {
    option: bool,
    boxed: bool,
}

fn constructor_requirements(kind: PtrKind) -> ConstructorRequirements {
    match kind {
        PtrKind::Ref(_) => ConstructorRequirements {
            option: false,
            boxed: false,
        },
        PtrKind::OptRef(_) => ConstructorRequirements {
            option: true,
            boxed: false,
        },
        PtrKind::Box => ConstructorRequirements {
            option: false,
            boxed: true,
        },
        PtrKind::OptBox => ConstructorRequirements {
            option: true,
            boxed: true,
        },
        PtrKind::Raw(_) => ConstructorRequirements {
            option: false,
            boxed: false,
        },
        PtrKind::BoxedSlice => ConstructorRequirements {
            option: false,
            boxed: true,
        },
        PtrKind::OptBoxedSlice => ConstructorRequirements {
            option: true,
            boxed: true,
        },
        PtrKind::Slice(_) => ConstructorRequirements {
            option: false,
            boxed: false,
        },
        PtrKind::SliceCursor(_) => ConstructorRequirements {
            option: false,
            boxed: false,
        },
    }
}

#[derive(Clone)]
struct ScopeCandidate {
    ident: Ident,
    def_id: DefId,
    namespace: Namespace,
    own_definition: bool,
}

struct TypeSpeller<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a utils::ir::AstToHir,
    containing_module: LocalDefId,
    candidates: Vec<ScopeCandidate>,
    external_roots: Vec<(String, DefId)>,
    implicit_prelude_enabled: bool,
    implicit_prelude_disabled_by: Option<LocalDefId>,
    prelude_module: Option<DefId>,
}

impl<'a, 'tcx> TypeSpeller<'a, 'tcx> {
    fn new(
        function_def_id: LocalDefId,
        ast_to_hir: &'a utils::ir::AstToHir,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        let containing_module: LocalDefId = tcx.parent_module_from_def_id(function_def_id).into();
        let mut candidates = tcx
            .module_children_local(containing_module)
            .iter()
            .filter_map(|child| {
                let def_id = child.res.opt_def_id()?;
                let namespace = child.res.ns()?;
                let own_definition = def_id.as_local().is_some_and(|local| {
                    LocalDefId::from(tcx.parent_module_from_def_id(local)) == containing_module
                }) && child.reexport_chain.is_empty();
                Some(ScopeCandidate {
                    ident: child.ident,
                    def_id,
                    namespace,
                    own_definition,
                })
            })
            .collect::<Vec<_>>();
        candidates.sort_by_key(|candidate| candidate.ident.to_string());

        let mut module = Some(containing_module);
        let mut implicit_prelude_enabled = true;
        let mut implicit_prelude_disabled_by = None;
        while let Some(def_id) = module {
            if tcx
                .get_attrs(def_id, sym::no_implicit_prelude)
                .next()
                .is_some()
            {
                implicit_prelude_enabled = false;
                implicit_prelude_disabled_by = Some(def_id);
                break;
            }
            module = tcx.opt_local_parent(def_id);
        }

        let mut external_roots = vec![];
        for item_id in tcx.hir_root_module().item_ids {
            let item = tcx.hir_item(*item_id);
            if let hir::ItemKind::ExternCrate(_, ident) = item.kind
                && let Some(crate_num) = tcx.extern_mod_stmt_cnum(item.owner_id.def_id)
            {
                external_roots.push((ident.to_string(), crate_num.as_def_id()));
            }
        }
        for (name, entry) in tcx.sess.opts.externs.iter() {
            if !entry.add_prelude {
                continue;
            }
            let exact_match = tcx.crates(()).iter().find(|crate_num| {
                entry.files().is_some_and(|mut files| {
                    files.any(|file| {
                        tcx.crate_extern_paths(**crate_num)
                            .iter()
                            .any(|path| path == file.canonicalized() || path == file.original())
                    })
                })
            });
            if let Some(crate_num) = exact_match {
                external_roots.push((name.clone(), crate_num.as_def_id()));
            } else if let Some(crate_num) = tcx
                .crates(())
                .iter()
                .find(|crate_num| tcx.crate_name(**crate_num).as_str() == name)
            {
                external_roots.push((name.clone(), crate_num.as_def_id()));
            }
        }
        let prelude_module = tcx.hir_free_items().find_map(|item_id| {
            let item = tcx.hir_item(item_id);
            if !matches!(item.kind, hir::ItemKind::Use(_, hir::UseKind::Glob))
                || !tcx
                    .hir_attrs(item.hir_id())
                    .iter()
                    .any(|attribute| attribute.has_name(sym::prelude_import))
            {
                return None;
            }
            let hir::ItemKind::Use(path, _) = item.kind else {
                return None;
            };
            path.segments
                .last()
                .and_then(|segment| segment.res.opt_def_id())
        });
        if let Some(prelude) = prelude_module {
            external_roots.push((
                tcx.crate_name(prelude.krate).to_string(),
                prelude.krate.as_def_id(),
            ));
        }
        if implicit_prelude_enabled
            && let Some(core_crate) = tcx
                .crates(())
                .iter()
                .find(|crate_num| tcx.crate_name(**crate_num).as_str() == "core")
        {
            external_roots.push(("core".to_owned(), core_crate.as_def_id()));
        }
        external_roots.sort_by(|left, right| left.0.cmp(&right.0));
        external_roots.dedup();

        Self {
            tcx,
            ast_to_hir,
            containing_module,
            candidates,
            external_roots,
            implicit_prelude_enabled,
            implicit_prelude_disabled_by,
            prelude_module,
        }
    }

    fn preferred_one_segment(&self, def_id: DefId, namespace: Namespace) -> Option<Ident> {
        self.candidates
            .iter()
            .find(|candidate| {
                candidate.def_id == def_id
                    && candidate.namespace == namespace
                    && candidate.own_definition
            })
            .or_else(|| {
                self.candidates.iter().find(|candidate| {
                    candidate.def_id == def_id && candidate.namespace == namespace
                })
            })
            .map(|candidate| candidate.ident)
    }

    fn shorten_source_type(&self, ty: &mut Ty) {
        SourceTypeShortener { speller: self }.visit_ty(ty);
    }

    fn render_semantic_type(&self, ty: ty::Ty<'tcx>) -> Result<Ty, String> {
        let mut rendered = String::new();
        let mut nominal_path = |def_id| {
            self.nominal_path(def_id)
                .map_err(utils::ir::MirTypeFormatError::Nominal)
        };
        utils::ir::format_mir_ty_with_policy(
            &mut rendered,
            ty,
            self.tcx,
            &mut nominal_path,
            utils::ir::MirTypeFormatPolicy::SourceValid,
        )
        .map_err(|error| format!("{error:?}"))?;
        let mut rendered_ty = utils::ast::try_parse_ty(rendered.clone())
            .map_err(|error| format!("rendered type `{rendered}` does not parse: {error}"))?;
        SemanticIdentRestorer { speller: self }.visit_ty(&mut rendered_ty);
        Ok(rendered_ty)
    }

    fn nominal_path(&self, def_id: DefId) -> Result<String, String> {
        if let Some(ident) = self.preferred_one_segment(def_id, Namespace::TypeNS) {
            return Ok(ident.to_string());
        }
        let candidates = if def_id.is_local() {
            self.local_visible_paths_in_namespace(def_id, Namespace::TypeNS)
        } else {
            self.external_visible_paths_in_namespace(def_id, Namespace::TypeNS)
        };
        candidates.into_iter().next().ok_or_else(|| {
            format!(
                "no accessible source path names `{}` from the containing module",
                self.tcx.def_path_str(def_id)
            )
        })
    }

    fn value_path(&self, def_id: DefId) -> Result<String, String> {
        if let Some(ident) = self.preferred_one_segment(def_id, Namespace::ValueNS) {
            return Ok(ident.to_string());
        }
        let candidates = if def_id.is_local() {
            self.local_visible_paths_in_namespace(def_id, Namespace::ValueNS)
        } else {
            self.external_visible_paths_in_namespace(def_id, Namespace::ValueNS)
        };
        candidates.into_iter().next().ok_or_else(|| {
            format!(
                "no accessible source value path names `{}` from the containing module",
                self.tcx.def_path_str(def_id)
            )
        })
    }

    fn resolve_external_identity(
        &self,
        crate_name: &str,
        path: &[String],
        namespace: Namespace,
    ) -> Option<DefId> {
        let crate_num = self
            .tcx
            .crates(())
            .iter()
            .copied()
            .find(|crate_num| self.tcx.crate_name(*crate_num).as_str() == crate_name)?;
        let mut module = crate_num.as_def_id();
        for (index, segment) in path.iter().enumerate() {
            let terminal = index + 1 == path.len();
            let child = self.tcx.module_children(module).iter().find(|child| {
                child.ident.name.as_str() == segment
                    && if terminal {
                        child.res.ns() == Some(namespace)
                    } else {
                        matches!(child.res, Res::Def(DefKind::Mod, _))
                    }
            })?;
            module = child.res.opt_def_id()?;
        }
        Some(module)
    }

    fn local_visible_paths_in_namespace(&self, target: DefId, namespace: Namespace) -> Vec<String> {
        let mut paths = vec![];
        let mut queue = VecDeque::from([(CRATE_DEF_ID.to_def_id(), Vec::<String>::new())]);
        let mut best_modules = FxHashMap::<DefId, (usize, String)>::default();
        while let Some((module, prefix)) = queue.pop_front() {
            let mut children = if module.is_local() {
                self.tcx
                    .module_children_local(module.expect_local())
                    .iter()
                    .collect::<Vec<_>>()
            } else {
                vec![]
            };
            children.sort_by_key(|child| child.ident.to_string());
            for child in children {
                if !child
                    .vis
                    .is_accessible_from(self.containing_module, self.tcx)
                {
                    continue;
                }
                let Some(def_id) = child.res.opt_def_id() else {
                    continue;
                };
                let mut child_path = prefix.clone();
                child_path.push(child.ident.to_string());
                if def_id == target && child.res.ns() == Some(namespace) {
                    paths.push(format!("crate::{}", child_path.join("::")));
                }
                if matches!(child.res, Res::Def(DefKind::Mod, _)) && def_id.is_local() {
                    let rendered = child_path.join("::");
                    let key = (child_path.len(), rendered.clone());
                    if best_modules.get(&def_id).is_none_or(|old| key < *old) {
                        best_modules.insert(def_id, key);
                        queue.push_back((def_id, child_path));
                    }
                }
            }
        }
        sort_paths(&mut paths);
        paths
    }

    #[cfg(test)]
    fn external_visible_paths(&self, target: DefId) -> Vec<String> {
        self.external_visible_paths_in_namespace(target, Namespace::TypeNS)
    }

    fn external_visible_paths_in_namespace(
        &self,
        target: DefId,
        namespace: Namespace,
    ) -> Vec<String> {
        let mut paths = vec![];
        for (root_name, root_def_id) in &self.external_roots {
            if root_def_id.krate != target.krate {
                continue;
            }
            let mut queue = VecDeque::from([(*root_def_id, Vec::<String>::new())]);
            let mut best_modules = FxHashMap::<DefId, (usize, String)>::default();
            while let Some((module, prefix)) = queue.pop_front() {
                let mut children = self.tcx.module_children(module).iter().collect::<Vec<_>>();
                children.sort_by_key(|child| child.ident.to_string());
                for child in children {
                    if !child.vis.is_public() {
                        continue;
                    }
                    let Some(def_id) = child.res.opt_def_id() else {
                        continue;
                    };
                    let mut child_path = prefix.clone();
                    child_path.push(child.ident.to_string());
                    if def_id == target && child.res.ns() == Some(namespace) {
                        paths.push(format!("::{root_name}::{}", child_path.join("::")));
                    }
                    if matches!(child.res, Res::Def(DefKind::Mod, _)) {
                        let rendered = child_path.join("::");
                        let key = (child_path.len(), rendered.clone());
                        if best_modules.get(&def_id).is_none_or(|old| key < *old) {
                            best_modules.insert(def_id, key);
                            queue.push_back((def_id, child_path));
                        }
                    }
                }
            }
        }
        sort_paths(&mut paths);
        paths
    }

    fn check_constructors(&self, kind: PtrKind) -> Result<(), String> {
        let requirements = constructor_requirements(kind);
        if !self.implicit_prelude_enabled && (requirements.option || requirements.boxed) {
            let constructor = if requirements.option { "Option" } else { "Box" };
            let containing_module = if self.containing_module == CRATE_DEF_ID {
                "crate root".to_owned()
            } else {
                format!(
                    "containing module `{}`",
                    self.tcx.def_path_str(self.containing_module)
                )
            };
            let disabled_by = self
                .implicit_prelude_disabled_by
                .filter(|def_id| *def_id != self.containing_module)
                .map(|def_id| {
                    if def_id == CRATE_DEF_ID {
                        " by the crate root".to_owned()
                    } else {
                        format!(" by ancestor module `{}`", self.tcx.def_path_str(def_id))
                    }
                })
                .unwrap_or_default();
            return Err(format!(
                "selected kind {kind:?} requires bare `{constructor}`, but the {containing_module} has its ordinary implicit prelude disabled{disabled_by}"
            ));
        }
        if requirements.option {
            self.check_constructor(sym::Option, hir::LangItem::Option, "Option", kind)?;
        }
        if requirements.boxed {
            self.check_constructor(Symbol::intern("Box"), hir::LangItem::OwnedBox, "Box", kind)?;
        }
        Ok(())
    }

    fn check_constructor(
        &self,
        symbol: Symbol,
        lang_item: hir::LangItem,
        display: &str,
        kind: PtrKind,
    ) -> Result<(), String> {
        if let Some(candidate) = self.candidates.iter().find(|candidate| {
            candidate.namespace == Namespace::TypeNS && candidate.ident.name == symbol
        }) {
            if self.tcx.is_lang_item(candidate.def_id, lang_item) {
                return Ok(());
            }
            return Err(format!(
                "selected kind {kind:?} requires bare `{display}`, but it resolves to `{}`, not the standard `{display}`",
                self.tcx.def_path_str(candidate.def_id)
            ));
        }
        if let Some((root, def_id)) = self.external_roots.iter().find(|(root, _)| root == display) {
            return Err(format!(
                "selected kind {kind:?} requires bare `{display}`, but the extern prelude binds it to crate `{root}` ({})",
                self.tcx.def_path_str(*def_id)
            ));
        }
        let prelude_binding = self.prelude_module.and_then(|module| {
            self.tcx
                .module_children(module)
                .iter()
                .find(|child| {
                    child.ident.name == symbol && child.res.ns() == Some(Namespace::TypeNS)
                })
                .and_then(|child| child.res.opt_def_id())
        });
        match prelude_binding {
            Some(def_id) if self.tcx.is_lang_item(def_id, lang_item) => Ok(()),
            Some(def_id) => Err(format!(
                "selected kind {kind:?} requires bare `{display}`, but the ordinary prelude resolves it to `{}`, not the standard `{display}`",
                self.tcx.def_path_str(def_id)
            )),
            None => Err(format!(
                "selected kind {kind:?} requires bare `{display}`, but it is unresolved in the enabled ordinary prelude"
            )),
        }
    }
}

fn sort_paths(paths: &mut Vec<String>) {
    paths.sort_by(|left, right| {
        left.split("::")
            .filter(|segment| !segment.is_empty())
            .count()
            .cmp(
                &right
                    .split("::")
                    .filter(|segment| !segment.is_empty())
                    .count(),
            )
            .then_with(|| left.cmp(right))
    });
    paths.dedup();
}

struct SourceTypeShortener<'a, 'map, 'tcx> {
    speller: &'a TypeSpeller<'map, 'tcx>,
}

impl MutVisitor for SourceTypeShortener<'_, '_, '_> {
    fn visit_ty(&mut self, ty: &mut Ty) {
        if let TyKind::Path(None, path) = &mut ty.kind
            && let Some(res) = self.speller.ast_to_hir.path_span_to_res.get(&path.span)
            && let Some(def_id) = res.opt_def_id()
            && path.segments.len() != 1
            && let Some(ident) = self
                .speller
                .preferred_one_segment(def_id, Namespace::TypeNS)
        {
            let args = path
                .segments
                .last()
                .and_then(|segment| segment.args.clone());
            *path = rustc_ast::Path::from_ident(ident);
            path.segments[0].args = args;
        }
        mut_visit::walk_ty(self, ty);
    }
}

struct SemanticIdentRestorer<'a, 'map, 'tcx> {
    speller: &'a TypeSpeller<'map, 'tcx>,
}

impl MutVisitor for SemanticIdentRestorer<'_, '_, '_> {
    fn visit_ty(&mut self, ty: &mut Ty) {
        if let TyKind::Path(None, path) = &mut ty.kind
            && let [segment] = &path.segments[..]
            && let Some(candidate) = self.speller.candidates.iter().find(|candidate| {
                candidate.namespace == Namespace::TypeNS
                    && candidate.ident.to_string() == segment.ident.to_string()
            })
            && self
                .speller
                .preferred_one_segment(candidate.def_id, Namespace::TypeNS)
                == Some(candidate.ident)
        {
            path.segments[0].ident = candidate.ident;
        }
        mut_visit::walk_ty(self, ty);
    }
}

fn target_type<'tcx>(
    original: ty::Ty<'tcx>,
    kind: PtrKind,
    lifetime: Option<Symbol>,
    source_hint: Option<&Ty>,
    type_speller: &TypeSpeller<'_, 'tcx>,
    function_path: &str,
    location: &str,
) -> Result<Ty, GenerationError> {
    type_speller.check_constructors(kind).map_err(|reason| {
        type_spelling_error(function_path, location, original, reason, type_speller.tcx)
    })?;
    let (ty::TyKind::RawPtr(inner, _) | ty::TyKind::Ref(_, inner, _)) = original.kind() else {
        return type_speller
            .render_semantic_type(original)
            .map_err(|reason| {
                type_spelling_error(function_path, location, original, reason, type_speller.tcx)
            });
    };
    let inner = source_hint
        .and_then(peel_source_pointer)
        .map(|mut ty| {
            type_speller.shorten_source_type(&mut ty);
            Ok(ty)
        })
        .unwrap_or_else(|| type_speller.render_semantic_type(*inner))
        .map_err(|reason| {
            type_spelling_error(function_path, location, original, reason, type_speller.tcx)
        })?;
    let inner = pprust::ty_to_string(&inner);
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
    utils::ast::try_parse_ty(rendered.clone()).map_err(|reason| {
        type_spelling_error(
            function_path,
            location,
            original,
            format!("rendered target type `{rendered}` does not parse: {reason}"),
            type_speller.tcx,
        )
    })
}

fn selected_target_type_tree<'tcx>(
    source: ty::Ty<'tcx>,
    decision: PtrKind,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
) -> Option<TypeTree> {
    let (ty::TyKind::RawPtr(inner, _) | ty::TyKind::Ref(_, inner, _)) = source.kind() else {
        return semantic_type_tree(source, ast_to_hir, tcx);
    };
    let inner = semantic_type_tree(*inner, ast_to_hir, tcx)?;
    let reference = |mutable, pointee| TypeTree::Reference {
        mutability: if mutable {
            RefMutability::Mutable
        } else {
            RefMutability::Shared
        },
        pointee: Box::new(pointee),
    };
    let raw = |mutable, pointee| TypeTree::RawPointer {
        mutability: if mutable {
            RawMutability::Mut
        } else {
            RawMutability::Const
        },
        pointee: Box::new(pointee),
    };
    let adt = |adt_kind, crate_name: &str, path: &[&str], arguments| TypeTree::Adt {
        adt_kind,
        identity: AdtIdentity::External {
            crate_name: crate_name.to_owned(),
            path: path.iter().map(|part| (*part).to_owned()).collect(),
        },
        arguments,
    };
    let global_allocator = || adt(AdtKind::Struct, "alloc", &["alloc", "Global"], vec![]);
    let boxed = |pointee| {
        adt(
            AdtKind::Struct,
            "alloc",
            &["boxed", "Box"],
            vec![pointee, global_allocator()],
        )
    };
    let option = |value| adt(AdtKind::Enum, "core", &["option", "Option"], vec![value]);
    Some(match decision {
        PtrKind::Ref(mutable) => reference(mutable, inner),
        PtrKind::OptRef(mutable) => option(reference(mutable, inner)),
        PtrKind::Box => boxed(inner),
        PtrKind::OptBox => option(boxed(inner)),
        PtrKind::Raw(mutable) => raw(mutable, inner),
        PtrKind::BoxedSlice => boxed(TypeTree::Slice {
            element: Box::new(inner),
        }),
        PtrKind::OptBoxedSlice => option(boxed(TypeTree::Slice {
            element: Box::new(inner),
        })),
        PtrKind::Slice(mutable) => reference(
            mutable,
            TypeTree::Slice {
                element: Box::new(inner),
            },
        ),
        PtrKind::SliceCursor(_) => return None,
    })
}

fn rule_binding_catalog(
    source: &Item,
    function: LocalDefId,
    decisions: &InitialPointerDecisions,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> HashMap<hir::HirId, TypeTree> {
    let mut result = HashMap::new();
    let ItemKind::Fn(box source_function) = &source.kind else {
        return result;
    };
    if let Some(signature) = decisions.signatures.data.get(&function) {
        for (index, parameter) in source_function.sig.decl.inputs.iter().enumerate() {
            let Some(decision) = signature.input_decs.get(index).copied().flatten() else {
                continue;
            };
            let Some(pattern) = ast_to_hir.get_pat(parameter.pat.id, tcx) else {
                continue;
            };
            let hir::PatKind::Binding(_, binding, _, None) = pattern.kind else {
                continue;
            };
            let source_type = tcx.typeck(pattern.hir_id.owner).node_type(pattern.hir_id);
            if source_type.is_raw_ptr()
                && let Some(target) =
                    selected_target_type_tree(source_type, decision, ast_to_hir, tcx)
            {
                result.insert(binding, target);
            }
        }
    }
    struct Locals<'a, 'tcx> {
        result: &'a mut HashMap<hir::HirId, TypeTree>,
        decisions: &'a InitialPointerDecisions,
        ast_to_hir: &'a utils::ir::AstToHir,
        tcx: TyCtxt<'tcx>,
    }
    impl<'ast> visit::Visitor<'ast> for Locals<'_, '_> {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if let StmtKind::Let(local) = &statement.kind
                && matches!(local.pat.kind, PatKind::Ident(_, _, None))
                && let Some(hir_pattern) = self.ast_to_hir.get_pat(local.pat.id, self.tcx)
                && let hir::PatKind::Binding(_, binding, _, None) = hir_pattern.kind
                && let Some(decision) = self.decisions.bindings.get(&binding).copied()
            {
                let source_type = self
                    .tcx
                    .typeck(hir_pattern.hir_id.owner)
                    .node_type(hir_pattern.hir_id);
                if source_type.is_raw_ptr()
                    && let Some(target) =
                        selected_target_type_tree(source_type, decision, self.ast_to_hir, self.tcx)
                {
                    self.result.insert(binding, target);
                }
            }
            visit::walk_stmt(self, statement);
        }
    }
    Locals {
        result: &mut result,
        decisions,
        ast_to_hir,
        tcx,
    }
    .visit_block(source_function.body.as_ref().unwrap());
    result
}

fn rule_target_binding_catalog(
    source: &Item,
    function: LocalDefId,
    decisions: &InitialPointerDecisions,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> HashMap<hir::HirId, TypeTree> {
    let mut result = rule_binding_catalog(source, function, decisions, ast_to_hir, tcx);
    let ItemKind::Fn(box source_function) = &source.kind else {
        return result;
    };
    let mut add_pattern = |pattern: &Pat| {
        let Some(pattern) = ast_to_hir.get_pat(pattern.id, tcx) else {
            return;
        };
        let hir::PatKind::Binding(_, binding, _, None) = pattern.kind else {
            return;
        };
        if result.contains_key(&binding) {
            return;
        }
        let source_type = tcx.typeck(pattern.hir_id.owner).node_type(pattern.hir_id);
        if let Some(target) = semantic_type_tree(source_type, ast_to_hir, tcx) {
            result.insert(binding, target);
        }
    };
    for parameter in &source_function.sig.decl.inputs {
        add_pattern(&parameter.pat);
    }
    struct Locals<'a> {
        add_pattern: &'a mut dyn FnMut(&Pat),
    }
    impl<'ast> visit::Visitor<'ast> for Locals<'_> {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if let StmtKind::Let(local) = &statement.kind
                && matches!(local.pat.kind, PatKind::Ident(_, _, None))
            {
                (self.add_pattern)(&local.pat);
            }
            visit::walk_stmt(self, statement);
        }
    }
    Locals {
        add_pattern: &mut add_pattern,
    }
    .visit_block(source_function.body.as_ref().unwrap());
    result
}

fn rule_type_syntax(
    source: &Item,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> HashMap<String, String> {
    struct Types<'a, 'tcx> {
        ast_to_hir: &'a utils::ir::AstToHir,
        result: HashMap<String, String>,
        tcx: TyCtxt<'tcx>,
    }
    impl<'ast> visit::Visitor<'ast> for Types<'_, '_> {
        fn visit_ty(&mut self, ty: &'ast Ty) {
            if let Some(hir) = self.ast_to_hir.get_ty(ty.id, self.tcx)
                && let Some(normalized) = semantic_type_tree(
                    self.tcx.typeck(hir.hir_id.owner).node_type(hir.hir_id),
                    self.ast_to_hir,
                    self.tcx,
                )
                && let Ok(key) = serde_json::to_string(&normalized)
            {
                self.result
                    .entry(key)
                    .or_insert_with(|| pprust::ty_to_string(ty));
            }
            visit::walk_ty(self, ty);
        }
    }
    let mut types = Types {
        ast_to_hir,
        result: HashMap::new(),
        tcx,
    };
    if let ItemKind::Fn(box function) = &source.kind
        && let Some(body) = &function.body
    {
        types.visit_block(body);
    }
    types.result
}

struct RuleRenderer<'a, 'map, 'tcx> {
    names: &'a HashMap<String, String>,
    syntax_overrides: &'a BTreeMap<usize, String>,
    identity_syntax: &'a BTreeMap<String, String>,
    syntax_cursor: Cell<usize>,
    type_syntax: &'a HashMap<String, String>,
    type_speller: &'a TypeSpeller<'map, 'tcx>,
}

fn member_spelling(identity: &FieldIdentity, names: &HashMap<String, String>) -> Option<String> {
    match identity {
        FieldIdentity::External { path, .. } => path.last().cloned(),
        FieldIdentity::Local { id, .. } => names.get(id).cloned(),
    }
}

fn variant_spelling(identity: &VariantIdentity, names: &HashMap<String, String>) -> Option<String> {
    match identity {
        VariantIdentity::External { path, .. } => path.last().cloned(),
        VariantIdentity::Local { id, .. } => names.get(id).cloned(),
    }
}

fn type_tree_spelling(value: &TypeTree, renderer: &RuleRenderer<'_, '_, '_>) -> Option<String> {
    if let Ok(key) = serde_json::to_string(value)
        && let Some(source) = renderer.type_syntax.get(&key)
    {
        return Some(source.clone());
    }
    Some(match value {
        TypeTree::Primitive { name } if name == "never" => "!".to_owned(),
        TypeTree::Primitive { name } => name.clone(),
        TypeTree::Slice { element } => format!("[{}]", type_tree_spelling(element, renderer)?),
        TypeTree::Array { element, length } => {
            format!("[{}; {length}]", type_tree_spelling(element, renderer)?)
        }
        TypeTree::RawPointer {
            mutability,
            pointee,
        } => format!(
            "*{} {}",
            if *mutability == RawMutability::Mut {
                "mut"
            } else {
                "const"
            },
            type_tree_spelling(pointee, renderer)?
        ),
        TypeTree::Reference {
            mutability,
            pointee,
        } => format!(
            "&{}{}",
            if *mutability == RefMutability::Mutable {
                "mut "
            } else {
                ""
            },
            type_tree_spelling(pointee, renderer)?
        ),
        TypeTree::Tuple { elements } => {
            let values = elements
                .iter()
                .map(|element| type_tree_spelling(element, renderer))
                .collect::<Option<Vec<_>>>()?;
            if values.len() == 1 {
                format!("({},)", values[0])
            } else {
                format!("({})", values.join(", "))
            }
        }
        TypeTree::Adt {
            identity,
            arguments,
            ..
        } => {
            let path = match identity {
                AdtIdentity::External { crate_name, path } => renderer
                    .type_speller
                    .resolve_external_identity(crate_name, path, Namespace::TypeNS)
                    .and_then(|definition| renderer.type_speller.nominal_path(definition).ok())?,
                AdtIdentity::Local { id } => renderer.names.get(id)?.clone(),
            };
            if arguments.is_empty() {
                path
            } else {
                format!(
                    "{path}<{}>",
                    arguments
                        .iter()
                        .map(|argument| type_tree_spelling(argument, renderer))
                        .collect::<Option<Vec<_>>>()?
                        .join(", ")
                )
            }
        }
    })
}

fn value_spelling(value: &ValueIdentity, renderer: &RuleRenderer<'_, '_, '_>) -> Option<String> {
    match value {
        ValueIdentity::Binding { id }
        | ValueIdentity::Function { id }
        | ValueIdentity::Constant { id }
        | ValueIdentity::Static { id } => renderer
            .identity_syntax
            .get(id)
            .cloned()
            .or_else(|| renderer.names.get(id).cloned()),
        ValueIdentity::Method { id } => renderer.names.get(id).cloned(),
        ValueIdentity::External { crate_name, path } => renderer
            .type_speller
            .resolve_external_identity(crate_name, path, Namespace::ValueNS)
            .and_then(|definition| renderer.type_speller.value_path(definition).ok()),
        ValueIdentity::ForeignFunction { symbol } | ValueIdentity::ForeignStatic { symbol } => {
            Some(symbol.clone())
        }
        ValueIdentity::Constructor { adt, variant } => {
            let adt = match adt {
                AdtIdentity::External { crate_name, path } => renderer
                    .type_speller
                    .resolve_external_identity(crate_name, path, Namespace::TypeNS)
                    .and_then(|definition| renderer.type_speller.nominal_path(definition).ok())?,
                AdtIdentity::Local { id } => renderer.names.get(id)?.clone(),
            };
            Some(match variant {
                Some(variant) => {
                    format!("{adt}::{}", variant_spelling(variant, renderer.names)?)
                }
                None => adt,
            })
        }
    }
}

fn binary_spelling(operator: BinaryOperator) -> &'static str {
    match operator {
        BinaryOperator::Add => "+",
        BinaryOperator::Subtract => "-",
        BinaryOperator::Multiply => "*",
        BinaryOperator::Divide => "/",
        BinaryOperator::Remainder => "%",
        BinaryOperator::And => "&&",
        BinaryOperator::Or => "||",
        BinaryOperator::BitXor => "^",
        BinaryOperator::BitAnd => "&",
        BinaryOperator::BitOr => "|",
        BinaryOperator::ShiftLeft => "<<",
        BinaryOperator::ShiftRight => ">>",
        BinaryOperator::Equal => "==",
        BinaryOperator::NotEqual => "!=",
        BinaryOperator::Less => "<",
        BinaryOperator::LessEqual => "<=",
        BinaryOperator::Greater => ">",
        BinaryOperator::GreaterEqual => ">=",
    }
}

fn byte_literal_contents(value: &[u8]) -> String {
    value
        .iter()
        .map(|byte| match *byte {
            b'\n' => "\\n".to_owned(),
            b'\r' => "\\r".to_owned(),
            b'\t' => "\\t".to_owned(),
            b'\\' => "\\\\".to_owned(),
            b'"' => "\\\"".to_owned(),
            0x20..=0x7e => char::from(*byte).to_string(),
            _ => format!("\\x{byte:02x}"),
        })
        .collect()
}

fn block_spelling(block: &crate::Block, renderer: &RuleRenderer<'_, '_, '_>) -> Option<String> {
    let statements = block
        .statements
        .iter()
        .map(|statement| statement_spelling(statement, renderer))
        .collect::<Option<Vec<_>>>()?;
    Some(format!("{{ {} }}", statements.join(" ")))
}

fn statement_spelling(
    statement: &Statement,
    renderer: &RuleRenderer<'_, '_, '_>,
) -> Option<String> {
    Some(match statement {
        Statement::Let {
            pattern,
            ty,
            initializer,
        } => {
            let pattern = match pattern {
                Pattern::Binding {
                    id,
                    mutability,
                    by_ref,
                } => {
                    let name = renderer.names.get(id)?;
                    let prefix = match by_ref {
                        ByRefKind::No => {
                            if *mutability == BindingMutability::Mutable {
                                "mut "
                            } else {
                                ""
                            }
                        }
                        ByRefKind::Shared => "ref ",
                        ByRefKind::Mutable => "ref mut ",
                    };
                    format!("{prefix}{name}")
                }
                Pattern::Wildcard => "_".to_owned(),
            };
            let ty = match ty {
                Some(ty) => format!(": {}", type_tree_spelling(ty, renderer)?),
                None => String::new(),
            };
            let initializer = match initializer {
                Some(value) => format!(" = {}", expression_spelling(value, renderer)?),
                None => String::new(),
            };
            format!("let {pattern}{ty}{initializer};")
        }
        Statement::Expression {
            expression,
            semicolon,
        } => format!(
            "{}{}",
            expression_spelling(expression, renderer)?,
            if *semicolon { ";" } else { "" }
        ),
    })
}

fn block_expression_count(block: &crate::Block) -> usize {
    block
        .statements
        .iter()
        .map(|statement| match statement {
            Statement::Let { initializer, .. } => {
                initializer.as_ref().map_or(0, expression_node_count)
            }
            Statement::Expression { expression, .. } => expression_node_count(expression),
        })
        .sum()
}

fn expression_node_count(expression: &Expression) -> usize {
    let children = match expression {
        Expression::Array { elements } | Expression::Tuple { elements } => {
            elements.iter().map(expression_node_count).sum()
        }
        Expression::Call { callee, arguments } => {
            expression_node_count(callee)
                + arguments.iter().map(expression_node_count).sum::<usize>()
        }
        Expression::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            expression_node_count(receiver)
                + arguments.iter().map(expression_node_count).sum::<usize>()
        }
        Expression::Binary { left, right, .. }
        | Expression::Assign { left, right }
        | Expression::AssignOp { left, right, .. }
        | Expression::Index {
            base: left,
            index: right,
        }
        | Expression::Repeat {
            value: left,
            count: right,
        } => expression_node_count(left) + expression_node_count(right),
        Expression::Unary { operand, .. }
        | Expression::Cast {
            expression: operand,
            ..
        }
        | Expression::Field { base: operand, .. }
        | Expression::AddressOf {
            expression: operand,
            ..
        } => expression_node_count(operand),
        Expression::If {
            condition,
            then,
            else_expression,
        } => {
            expression_node_count(condition)
                + block_expression_count(then)
                + else_expression.as_deref().map_or(0, expression_node_count)
        }
        Expression::While { condition, body } => {
            expression_node_count(condition) + block_expression_count(body)
        }
        Expression::Loop { body } | Expression::Block { block: body } => {
            block_expression_count(body)
        }
        Expression::Range { start, end, .. } => {
            start.as_deref().map_or(0, expression_node_count)
                + end.as_deref().map_or(0, expression_node_count)
        }
        Expression::Break { value } | Expression::Return { value } => {
            value.as_deref().map_or(0, expression_node_count)
        }
        Expression::Struct { fields, rest, .. } => {
            fields
                .iter()
                .map(|field| expression_node_count(&field.value))
                .sum::<usize>()
                + rest.as_deref().map_or(0, expression_node_count)
        }
        Expression::Literal { .. } | Expression::Path { .. } | Expression::Continue => 0,
    };
    1 + children
}

fn expression_spelling(
    expression: &Expression,
    renderer: &RuleRenderer<'_, '_, '_>,
) -> Option<String> {
    let ordinal = renderer.syntax_cursor.get();
    renderer.syntax_cursor.set(ordinal + 1);
    if let Some(source) = renderer.syntax_overrides.get(&ordinal) {
        renderer
            .syntax_cursor
            .set(ordinal + expression_node_count(expression));
        return Some(source.clone());
    }
    let recurse = |value: &Expression| expression_spelling(value, renderer);
    Some(match expression {
        Expression::Array { elements } => format!(
            "[{}]",
            elements
                .iter()
                .map(recurse)
                .collect::<Option<Vec<_>>>()?
                .join(", ")
        ),
        Expression::Call { callee, arguments } => format!(
            "{}({})",
            recurse(callee)?,
            arguments
                .iter()
                .map(recurse)
                .collect::<Option<Vec<_>>>()?
                .join(", ")
        ),
        Expression::MethodCall {
            receiver,
            method,
            arguments,
        } => {
            let method = match method {
                ValueIdentity::External { path, .. } => path.last()?.clone(),
                ValueIdentity::Method { id } => renderer.names.get(id)?.clone(),
                _ => value_spelling(method, renderer)?
                    .rsplit("::")
                    .next()?
                    .to_owned(),
            };
            format!(
                "({}).{}({})",
                recurse(receiver)?,
                method,
                arguments
                    .iter()
                    .map(recurse)
                    .collect::<Option<Vec<_>>>()?
                    .join(", ")
            )
        }
        Expression::Tuple { elements } => {
            let values = elements.iter().map(recurse).collect::<Option<Vec<_>>>()?;
            if values.len() == 1 {
                format!("({},)", values[0])
            } else {
                format!("({})", values.join(", "))
            }
        }
        Expression::Binary {
            operator,
            left,
            right,
        } => {
            format!(
                "({} {} {})",
                recurse(left)?,
                binary_spelling(*operator),
                recurse(right)?
            )
        }
        Expression::Unary { operator, operand } => format!(
            "({}{})",
            match operator {
                UnaryOperator::Deref => "*",
                UnaryOperator::Not => "!",
                UnaryOperator::Negate => "-",
            },
            recurse(operand)?
        ),
        Expression::Literal { value } => match value {
            Literal::Bool { value } => value.to_string(),
            Literal::Char { value } => {
                let mut values = value.chars();
                let value = values.next()?;
                if values.next().is_some() {
                    return None;
                }
                format!("'{}'", value.escape_default())
            }
            Literal::Byte { value } => format!("{value}u8"),
            Literal::String { value } => format!("{value:?}"),
            Literal::ByteString { value } => format!("b\"{}\"", byte_literal_contents(value)),
            Literal::CString { value } => format!("c\"{}\"", byte_literal_contents(value)),
            Literal::Integer { value, ty } => format!("{value}{ty}"),
            Literal::Float { bits, ty } => format!("{ty}::from_bits(0x{bits})"),
        },
        Expression::Cast { expression, ty } => {
            format!(
                "({} as {})",
                recurse(expression)?,
                type_tree_spelling(ty, renderer)?
            )
        }
        Expression::If {
            condition,
            then,
            else_expression,
        } => format!(
            "if {} {}{}",
            recurse(condition)?,
            block_spelling(then, renderer)?,
            match else_expression {
                Some(value) => format!(" else {}", recurse(value)?),
                None => String::new(),
            }
        ),
        Expression::While { condition, body } => format!(
            "while {} {}",
            recurse(condition)?,
            block_spelling(body, renderer)?
        ),
        Expression::Loop { body } => format!("loop {}", block_spelling(body, renderer)?),
        Expression::Assign { left, right } => format!("({} = {})", recurse(left)?, recurse(right)?),
        Expression::AssignOp {
            operator,
            left,
            right,
        } => format!(
            "({} {}= {})",
            recurse(left)?,
            binary_spelling(*operator),
            recurse(right)?
        ),
        Expression::Field { base, field } => {
            format!(
                "({}).{}",
                recurse(base)?,
                member_spelling(field, renderer.names)?
            )
        }
        Expression::Index { base, index } => format!("({})[{}]", recurse(base)?, recurse(index)?),
        Expression::Range { start, end, limits } => format!(
            "{}{}{}",
            match start {
                Some(value) => recurse(value)?,
                None => String::new(),
            },
            if *limits == RangeLimits::Closed {
                "..="
            } else {
                ".."
            },
            match end {
                Some(value) => recurse(value)?,
                None => String::new(),
            }
        ),
        Expression::Path { value } => value_spelling(value, renderer)?,
        Expression::AddressOf {
            borrow,
            mutability,
            expression,
        } => format!(
            "&{}{}{}",
            if *borrow == BorrowKind::Raw {
                "raw "
            } else {
                ""
            },
            match (borrow, mutability) {
                (BorrowKind::Raw, RawMutability::Const) => "const ",
                (_, RawMutability::Mut) => "mut ",
                _ => "",
            },
            recurse(expression)?
        ),
        Expression::Break { value } => format!(
            "break{}",
            match value {
                Some(value) => format!(" {}", recurse(value)?),
                None => String::new(),
            }
        ),
        Expression::Continue => "continue".to_owned(),
        Expression::Return { value } => format!(
            "return{}",
            match value {
                Some(value) => format!(" {}", recurse(value)?),
                None => String::new(),
            }
        ),
        Expression::Struct {
            adt,
            variant,
            fields,
            rest,
        } => {
            let mut path = match adt {
                AdtIdentity::External { crate_name, path } => renderer
                    .type_speller
                    .resolve_external_identity(crate_name, path, Namespace::TypeNS)
                    .and_then(|definition| renderer.type_speller.nominal_path(definition).ok())?,
                AdtIdentity::Local { id } => renderer.names.get(id)?.clone(),
            };
            if let Some(variant) = variant {
                path.push_str("::");
                path.push_str(&variant_spelling(variant, renderer.names)?);
            }
            let mut values = fields
                .iter()
                .map(|field| {
                    Some(format!(
                        "{}: {}",
                        member_spelling(&field.field, renderer.names)?,
                        recurse(&field.value)?
                    ))
                })
                .collect::<Option<Vec<_>>>()?;
            if let Some(rest) = rest {
                values.push(format!("..{}", recurse(rest)?));
            }
            format!("{path} {{ {} }}", values.join(", "))
        }
        Expression::Repeat { value, count } => {
            format!("[{}; {}]", recurse(value)?, recurse(count)?)
        }
        Expression::Block { block } => block_spelling(block, renderer)?,
    })
}

fn supported_assignment_place(expression: &Expr) -> bool {
    match &expression.kind {
        ExprKind::Path(..) => true,
        ExprKind::Unary(rustc_ast::UnOp::Deref, value)
        | ExprKind::Paren(value)
        | ExprKind::Field(value, _)
        | ExprKind::Index(value, _, _) => supported_assignment_place(value),
        _ => false,
    }
}

fn supported_normalized_assignment_place(expression: &Expression) -> bool {
    match expression {
        Expression::Path { value } => matches!(
            value,
            ValueIdentity::Binding { .. }
                | ValueIdentity::Static { .. }
                | ValueIdentity::ForeignStatic { .. }
                | ValueIdentity::External { .. }
        ),
        Expression::Unary {
            operator: UnaryOperator::Deref,
            operand,
        } => supported_normalized_assignment_place(operand),
        Expression::Field { base, .. } | Expression::Index { base, .. } => {
            supported_normalized_assignment_place(base)
        }
        _ => false,
    }
}

fn parse_rule_expression(source: String, lhs: bool) -> Option<Expr> {
    let expression = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        utils::ast::parse_expr(source)
    }))
    .ok()?;
    struct ErrorFinder(bool);
    impl<'ast> visit::Visitor<'ast> for ErrorFinder {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if matches!(expression.kind, ExprKind::Err(_)) {
                self.0 = true;
            } else {
                visit::walk_expr(self, expression);
            }
        }
    }
    let mut errors = ErrorFinder(false);
    errors.visit_expr(&expression);
    (!errors.0 && (!lhs || supported_assignment_place(&expression))).then_some(expression)
}

struct RuleExpressionInstaller<'a> {
    replacements: &'a mut HashMap<NodeId, Expr>,
}

fn same_rule_region(root: NodeId, expression: &Expr) -> bool {
    if expression.id == root {
        return true;
    }
    matches!(&expression.kind, ExprKind::Paren(inner) if same_rule_region(root, inner))
}

fn selected_signature_type<'tcx>(
    definition: rustc_span::def_id::DefId,
    arguments: ty::GenericArgsRef<'tcx>,
    index: Option<usize>,
    decisions: &InitialPointerDecisions,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
) -> Option<TypeTree> {
    let signature = tcx
        .fn_sig(definition)
        .instantiate(tcx, arguments)
        .skip_binder();
    let source = match index {
        Some(index) => *signature.inputs().get(index)?,
        None => signature.output(),
    };
    let decision = (!tcx.is_foreign_item(definition))
        .then(|| definition.as_local())
        .flatten()
        .and_then(|local| {
            let signature = decisions.signatures.data.get(&local)?;
            match index {
                Some(index) => signature.input_decs.get(index).copied().flatten(),
                None => signature.output_dec,
            }
        });
    match decision {
        Some(decision) => selected_target_type_tree(source, decision, ast_to_hir, tcx),
        None => semantic_type_tree(source, ast_to_hir, tcx),
    }
}

fn direct_call_type<'tcx>(
    callee: &Expr,
    index: Option<usize>,
    decisions: &InitialPointerDecisions,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
) -> Option<TypeTree> {
    let callee = ast_to_hir.get_expr(callee.id, tcx)?;
    let typeck = tcx.typeck(callee.hir_id.owner);
    let ty::TyKind::FnDef(definition, arguments) = typeck.expr_ty(callee).kind() else {
        return None;
    };
    selected_signature_type(*definition, arguments, index, decisions, ast_to_hir, tcx)
}

fn option_or_box_pointee(value: &TypeTree) -> Option<TypeTree> {
    match value {
        TypeTree::RawPointer { pointee, .. } | TypeTree::Reference { pointee, .. } => {
            Some((**pointee).clone())
        }
        TypeTree::Adt {
            identity: AdtIdentity::External { crate_name, path },
            arguments,
            ..
        } if crate_name == "alloc" && path == &["boxed", "Box"] => arguments.first().cloned(),
        TypeTree::Adt {
            identity: AdtIdentity::External { crate_name, path },
            arguments,
            ..
        } if crate_name == "core" && path == &["option", "Option"] && arguments.len() == 1 => {
            match &arguments[0] {
                TypeTree::Reference { pointee, .. } => Some((**pointee).clone()),
                TypeTree::Adt {
                    identity: AdtIdentity::External { crate_name, path },
                    arguments,
                    ..
                } if crate_name == "alloc"
                    && path == &["boxed", "Box"]
                    && !arguments.is_empty() =>
                {
                    arguments.first().cloned()
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn substitute_field_type_tree(
    template: ty::Ty<'_>,
    source: TypeTree,
    substitutions: &HashMap<u32, TypeTree>,
) -> Option<TypeTree> {
    if let ty::TyKind::Param(parameter) = template.kind() {
        return substitutions.get(&parameter.index).cloned();
    }
    Some(match (template.kind(), source) {
        (ty::TyKind::Bool, value @ TypeTree::Primitive { .. })
        | (ty::TyKind::Char, value @ TypeTree::Primitive { .. })
        | (ty::TyKind::Int(_), value @ TypeTree::Primitive { .. })
        | (ty::TyKind::Uint(_), value @ TypeTree::Primitive { .. })
        | (ty::TyKind::Float(_), value @ TypeTree::Primitive { .. })
        | (ty::TyKind::Str, value @ TypeTree::Primitive { .. }) => value,
        (
            ty::TyKind::RawPtr(element, _),
            TypeTree::RawPointer {
                mutability,
                pointee,
            },
        ) => TypeTree::RawPointer {
            mutability,
            pointee: Box::new(substitute_field_type_tree(
                *element,
                *pointee,
                substitutions,
            )?),
        },
        (
            ty::TyKind::Ref(_, element, _),
            TypeTree::Reference {
                mutability,
                pointee,
            },
        ) => TypeTree::Reference {
            mutability,
            pointee: Box::new(substitute_field_type_tree(
                *element,
                *pointee,
                substitutions,
            )?),
        },
        (ty::TyKind::Slice(element), TypeTree::Slice { element: source }) => TypeTree::Slice {
            element: Box::new(substitute_field_type_tree(
                *element,
                *source,
                substitutions,
            )?),
        },
        (
            ty::TyKind::Array(element, _),
            TypeTree::Array {
                element: source,
                length,
            },
        ) => TypeTree::Array {
            element: Box::new(substitute_field_type_tree(
                *element,
                *source,
                substitutions,
            )?),
            length,
        },
        (ty::TyKind::Tuple(elements), TypeTree::Tuple { elements: source })
            if elements.len() == source.len() =>
        {
            TypeTree::Tuple {
                elements: elements
                    .iter()
                    .zip(source)
                    .map(|(template, source)| {
                        substitute_field_type_tree(template, source, substitutions)
                    })
                    .collect::<Option<_>>()?,
            }
        }
        (
            ty::TyKind::Adt(_, arguments),
            TypeTree::Adt {
                adt_kind,
                identity,
                arguments: source,
            },
        ) => {
            let templates = arguments.types().collect::<Vec<_>>();
            if templates.len() != source.len() {
                return None;
            }
            TypeTree::Adt {
                adt_kind,
                identity,
                arguments: templates
                    .into_iter()
                    .zip(source)
                    .map(|(template, source)| {
                        substitute_field_type_tree(template, source, substitutions)
                    })
                    .collect::<Option<_>>()?,
            }
        }
        _ => return None,
    })
}

fn target_field_type<'tcx>(
    base: &Expr,
    field_name: rustc_span::Symbol,
    target_base: TypeTree,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
) -> Option<TypeTree> {
    let TypeTree::Adt {
        arguments: target_arguments,
        ..
    } = target_base
    else {
        return None;
    };
    let base = ast_to_hir.get_expr(base.id, tcx)?;
    let mut source_base = tcx.typeck(base.hir_id.owner).expr_ty_adjusted(base);
    while let ty::TyKind::Ref(_, pointee, _) = source_base.kind() {
        source_base = *pointee;
    }
    let ty::TyKind::Adt(definition, source_arguments) = source_base.kind() else {
        return None;
    };
    let field = definition
        .non_enum_variant()
        .fields
        .iter()
        .find(|field| field.name == field_name)?;
    let source_field = field.ty(tcx, source_arguments);
    let source_tree = semantic_type_tree(source_field, ast_to_hir, tcx)?;
    let identity_arguments = ty::GenericArgs::identity_for_item(tcx, definition.did());
    let type_parameters = identity_arguments
        .types()
        .filter_map(|argument| match argument.kind() {
            ty::TyKind::Param(parameter) => Some(parameter.index),
            _ => None,
        })
        .collect::<Vec<_>>();
    if type_parameters.len() != target_arguments.len() {
        return None;
    }
    let substitutions = type_parameters
        .into_iter()
        .zip(target_arguments)
        .collect::<HashMap<_, _>>();
    substitute_field_type_tree(
        field.ty(tcx, identity_arguments),
        source_tree,
        &substitutions,
    )
}

fn target_place_type<'tcx>(
    expression: &Expr,
    catalog: &HashMap<hir::HirId, TypeTree>,
    decisions: &InitialPointerDecisions,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
) -> Option<TypeTree> {
    match &expression.kind {
        ExprKind::Paren(inner) => target_place_type(inner, catalog, decisions, ast_to_hir, tcx),
        ExprKind::Path(..) => {
            let expression = ast_to_hir.get_expr(expression.id, tcx)?;
            let hir::ExprKind::Path(path) = expression.kind else { return None };
            let hir::def::Res::Local(binding) = tcx
                .typeck(expression.hir_id.owner)
                .qpath_res(&path, expression.hir_id)
            else {
                return None;
            };
            catalog.get(&binding).cloned()
        }
        ExprKind::Call(callee, _) => direct_call_type(callee, None, decisions, ast_to_hir, tcx),
        ExprKind::Unary(rustc_ast::UnOp::Deref, operand) => option_or_box_pointee(
            &target_place_type(operand, catalog, decisions, ast_to_hir, tcx)?,
        ),
        ExprKind::Field(base, field) => target_field_type(
            base,
            field.name,
            target_place_type(base, catalog, decisions, ast_to_hir, tcx)?,
            ast_to_hir,
            tcx,
        ),
        ExprKind::Index(base, _, _) => {
            let base = target_place_type(base, catalog, decisions, ast_to_hir, tcx)?;
            match base {
                TypeTree::Array { element, .. } | TypeTree::Slice { element } => Some(*element),
                TypeTree::Reference { pointee, .. } => match *pointee {
                    TypeTree::Array { element, .. } | TypeTree::Slice { element } => Some(*element),
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

fn simple_local_target(
    local: &rustc_ast::Local,
    catalog: &HashMap<hir::HirId, TypeTree>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<TypeTree> {
    let pattern = ast_to_hir.get_pat(local.pat.id, tcx)?;
    let hir::PatKind::Binding(_, binding, _, None) = pattern.kind else { return None };
    catalog.get(&binding).cloned()
}

#[allow(clippy::too_many_arguments)]
fn contextual_target_type<'tcx>(
    root: NodeId,
    lhs: bool,
    source: &Item,
    function: LocalDefId,
    catalog: &HashMap<hir::HirId, TypeTree>,
    decisions: &InitialPointerDecisions,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
) -> Option<TypeTree> {
    let ItemKind::Fn(box source_function) = &source.kind else { return None };
    let current_return = || {
        selected_signature_type(
            function.to_def_id(),
            ty::GenericArgs::identity_for_item(tcx, function.to_def_id()),
            None,
            decisions,
            ast_to_hir,
            tcx,
        )
    };
    if let Some(statement) = source_function.body.as_ref()?.stmts.last()
        && let StmtKind::Expr(expression) = &statement.kind
        && same_rule_region(root, expression)
    {
        return current_return();
    }

    struct Finder<'a, 'tcx> {
        root: NodeId,
        lhs: bool,
        result: Option<TypeTree>,
        catalog: &'a HashMap<hir::HirId, TypeTree>,
        decisions: &'a InitialPointerDecisions,
        ast_to_hir: &'a utils::ir::AstToHir,
        current_return: &'a dyn Fn() -> Option<TypeTree>,
        tcx: TyCtxt<'tcx>,
    }
    impl<'ast> visit::Visitor<'ast> for Finder<'_, '_> {
        fn visit_local(&mut self, local: &'ast rustc_ast::Local) {
            if self.result.is_none()
                && let rustc_ast::LocalKind::Init(initializer)
                | rustc_ast::LocalKind::InitElse(initializer, _) = &local.kind
                && same_rule_region(self.root, initializer)
            {
                self.result = simple_local_target(local, self.catalog, self.ast_to_hir, self.tcx);
                return;
            }
            visit::walk_local(self, local);
        }

        fn visit_expr(&mut self, expression: &'ast Expr) {
            if self.result.is_some() {
                return;
            }
            match &expression.kind {
                ExprKind::Assign(left, right, _) if same_rule_region(self.root, right) => {
                    self.result = target_place_type(
                        left,
                        self.catalog,
                        self.decisions,
                        self.ast_to_hir,
                        self.tcx,
                    );
                }
                ExprKind::Assign(left, _, _) if self.lhs && same_rule_region(self.root, left) => {
                    let mut bare = left.as_ref();
                    while let ExprKind::Paren(inner) = &bare.kind {
                        bare = inner;
                    }
                    if matches!(bare.kind, ExprKind::Path(..)) {
                        self.result = target_place_type(
                            bare,
                            self.catalog,
                            self.decisions,
                            self.ast_to_hir,
                            self.tcx,
                        );
                    }
                }
                ExprKind::Call(callee, arguments) => {
                    if let Some(index) = arguments
                        .iter()
                        .position(|argument| same_rule_region(self.root, argument))
                    {
                        self.result = direct_call_type(
                            callee,
                            Some(index),
                            self.decisions,
                            self.ast_to_hir,
                            self.tcx,
                        );
                    }
                }
                ExprKind::Ret(Some(value)) if same_rule_region(self.root, value) => {
                    self.result = (self.current_return)();
                }
                ExprKind::Struct(value) => {
                    if let Some(field) = value
                        .fields
                        .iter()
                        .find(|field| same_rule_region(self.root, &field.expr))
                    {
                        let field = self.ast_to_hir.get_expr(field.expr.id, self.tcx);
                        self.result = field.and_then(|field| {
                            semantic_type_tree(
                                self.tcx.typeck(field.hir_id.owner).expr_ty_adjusted(field),
                                self.ast_to_hir,
                                self.tcx,
                            )
                        });
                    }
                }
                _ => {}
            }
            if self.result.is_none() {
                visit::walk_expr(self, expression);
            }
        }
    }
    let mut finder = Finder {
        root,
        lhs,
        result: None,
        catalog,
        decisions,
        ast_to_hir,
        current_return: &current_return,
        tcx,
    };
    finder.visit_block(source_function.body.as_ref()?);
    finder.result
}

impl MutVisitor for RuleExpressionInstaller<'_> {
    fn visit_expr(&mut self, expression: &mut Expr) {
        if let Some(mut replacement) = self.replacements.remove(&expression.id) {
            replacement.attrs = expression.attrs.clone();
            *expression = replacement;
            return;
        }
        mut_visit::walk_expr(self, expression);
    }
}

#[allow(clippy::too_many_arguments)]
fn apply_rule_set(
    source: &Item,
    target: &mut Item,
    transformed: &BTreeSet<u32>,
    document: &RuleDocument,
    function: LocalDefId,
    decisions: &InitialPointerDecisions,
    ast_to_hir: &utils::ir::AstToHir,
    type_speller: &TypeSpeller<'_, '_>,
    tcx: TyCtxt<'_>,
) -> Result<BTreeSet<u32>, GenerationError> {
    let loaded = LoadedRuleSet::new(document).map_err(|error| GenerationError {
        kind: GenerationErrorKind::AstHirMismatch,
        function_path: tcx.def_path_str(function.to_def_id()),
        message: format!("invalid rule document: {error}"),
    })?;
    if loaded.rules().is_empty() {
        return Ok(BTreeSet::new());
    }
    let catalog = rule_binding_catalog(source, function, decisions, ast_to_hir, tcx);
    let target_catalog = rule_target_binding_catalog(source, function, decisions, ast_to_hir, tcx);
    let type_syntax = rule_type_syntax(source, ast_to_hir, tcx);
    let ItemKind::Fn(box source_function) = &source.kind else {
        return Ok(BTreeSet::new());
    };
    let mut statements = FxHashMap::default();
    StatementByLabelCollector {
        statements: &mut statements,
    }
    .visit_block(source_function.body.as_ref().unwrap());
    let mut applied = BTreeSet::new();
    for label in transformed {
        let Some(statement) = statements.get(label).copied() else {
            continue;
        };
        let Some(regions) = select_rule_regions(statement, &catalog, ast_to_hir, tcx) else {
            continue;
        };
        if regions.is_empty() {
            continue;
        }
        let mut replacements = HashMap::new();
        let mut complete = true;
        for region in regions {
            let target_adjusted_type = contextual_target_type(
                region.root,
                region.observation.lhs,
                source,
                function,
                &target_catalog,
                decisions,
                ast_to_hir,
                tcx,
            );
            let input = RuleMatchInput {
                source_expression: region.observation.source_expression,
                pointer_anchors: region.observation.pointer_anchors,
                lhs: region.observation.lhs,
                source_type: region.observation.source_type,
                source_adjusted_type: region.observation.source_adjusted_type,
                target_type: None,
                target_adjusted_type,
            };
            let mut excluded = BTreeSet::new();
            let expression = loop {
                let Some(selection) = loaded.select_with_exclusions_and_syntax(
                    &input,
                    &excluded,
                    &region.source_syntax,
                ) else {
                    complete = false;
                    break None;
                };
                if input.lhs && !supported_normalized_assignment_place(&selection.target_expression)
                {
                    excluded.insert(selection.rule_index);
                    continue;
                }
                let renderer = RuleRenderer {
                    names: &region.spellings,
                    syntax_overrides: &selection.syntax_overrides,
                    identity_syntax: &selection.identity_syntax,
                    syntax_cursor: Cell::new(0),
                    type_syntax: &type_syntax,
                    type_speller,
                };
                let rendered = expression_spelling(&selection.target_expression, &renderer);
                if let Some(expression) =
                    rendered.and_then(|rendered| parse_rule_expression(rendered, input.lhs))
                {
                    let mut trial_replacements = replacements.clone();
                    trial_replacements.insert(region.root, expression.clone());
                    let mut trial = target.clone();
                    RuleExpressionInstaller {
                        replacements: &mut trial_replacements,
                    }
                    .visit_item(&mut trial);
                    if trial_replacements.is_empty()
                        && validate_rule_application_shape(&trial).is_ok()
                    {
                        break Some(expression);
                    }
                }
                excluded.insert(selection.rule_index);
            };
            let Some(expression) = expression else { break };
            replacements.insert(region.root, expression);
        }
        if complete && !replacements.is_empty() {
            let mut tentative = target.clone();
            RuleExpressionInstaller {
                replacements: &mut replacements,
            }
            .visit_item(&mut tentative);
            if replacements.is_empty() {
                *target = tentative;
                applied.insert(*label);
            }
        }
    }
    validate_rule_application_shape(target).map_err(|message| GenerationError {
        kind: GenerationErrorKind::AstHirMismatch,
        function_path: tcx.def_path_str(function.to_def_id()),
        message: format!("applied function failed structural validation: {message}"),
    })?;
    Ok(applied)
}

fn peel_source_pointer(ty: &Ty) -> Option<Ty> {
    match &ty.kind {
        TyKind::Ptr(mut_ty) | TyKind::Ref(_, mut_ty) => Some((*mut_ty.ty).clone()),
        _ => None,
    }
}

fn type_spelling_error<'tcx>(
    function_path: &str,
    location: &str,
    semantic_type: ty::Ty<'tcx>,
    reason: String,
    tcx: TyCtxt<'tcx>,
) -> GenerationError {
    GenerationError {
        kind: GenerationErrorKind::TypeSpelling,
        function_path: function_path.to_owned(),
        message: format!(
            "cannot spell type for {location} (semantic type `{}`): {reason}",
            tcx.erase_regions(semantic_type)
        ),
    }
}

struct StatementClassification {
    transformed: BTreeSet<u32>,
    preserved_shells: BTreeSet<u32>,
}

fn classify_function_statements(
    item: &Item,
    opaque_nested_ifs: &FxHashSet<NodeId>,
    ast_to_hir: &utils::ir::AstToHir,
    decisions: &InitialPointerDecisions,
    preservation_overrides: &PreservationDecisionOverrides,
    tcx: TyCtxt<'_>,
) -> StatementClassification {
    let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
    let mut classifier = StatementClassifier {
        ast_to_hir,
        decisions,
        preservation_overrides,
        opaque_nested_ifs,
        tcx,
        transformed: BTreeSet::new(),
        preserved_shells: BTreeSet::new(),
    };
    classifier.visit_block(
        function
            .body
            .as_ref()
            .expect("source-defined function has a body"),
    );
    StatementClassification {
        transformed: classifier.transformed,
        preserved_shells: classifier.preserved_shells,
    }
}

struct StatementClassifier<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    decisions: &'a InitialPointerDecisions,
    preservation_overrides: &'a PreservationDecisionOverrides,
    opaque_nested_ifs: &'a FxHashSet<NodeId>,
    tcx: TyCtxt<'tcx>,
    transformed: BTreeSet<u32>,
    preserved_shells: BTreeSet<u32>,
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
            if statement_shell_is_preservable(
                statement,
                self.ast_to_hir,
                self.decisions,
                self.preservation_overrides,
                self.tcx,
            ) {
                self.preserved_shells.insert(label);
            } else {
                self.transformed.insert(label);
            }
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
    statement_is_preservable_excluding(
        statement,
        &FxHashSet::default(),
        &FxHashSet::default(),
        ast_to_hir,
        decisions,
        preservation_overrides,
        tcx,
    )
}

fn statement_shell_is_preservable(
    statement: &Stmt,
    ast_to_hir: &utils::ir::AstToHir,
    decisions: &InitialPointerDecisions,
    preservation_overrides: &PreservationDecisionOverrides,
    tcx: TyCtxt<'_>,
) -> bool {
    let mut collector = NestedLabeledStatementCollector {
        root: statement.id,
        statements: FxHashSet::default(),
    };
    collector.visit_stmt(statement);
    if collector.statements.is_empty() {
        return false;
    }
    let mut excluded_hir = FxHashSet::default();
    for node_id in &collector.statements {
        let Some(node) = ast_to_hir.get_local_node(*node_id, tcx) else {
            return false;
        };
        let hir_id = match node {
            hir::Node::Stmt(statement) => statement.hir_id,
            hir::Node::Expr(expression) => expression.hir_id,
            _ => return false,
        };
        excluded_hir.insert(hir_id);
    }
    statement_is_preservable_excluding(
        statement,
        &collector.statements,
        &excluded_hir,
        ast_to_hir,
        decisions,
        preservation_overrides,
        tcx,
    )
}

struct NestedLabeledStatementCollector {
    root: NodeId,
    statements: FxHashSet<NodeId>,
}

impl<'ast> visit::Visitor<'ast> for NestedLabeledStatementCollector {
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        if statement.id != self.root && statement_numeric_label(statement).is_some() {
            self.statements.insert(statement.id);
            return;
        }
        visit::walk_stmt(self, statement);
    }
}

fn statement_is_preservable_excluding(
    statement: &Stmt,
    excluded_ast: &FxHashSet<NodeId>,
    excluded_hir: &FxHashSet<HirId>,
    ast_to_hir: &utils::ir::AstToHir,
    decisions: &InitialPointerDecisions,
    preservation_overrides: &PreservationDecisionOverrides,
    tcx: TyCtxt<'_>,
) -> bool {
    let mut surface = SurfacePreservationCheck {
        ast_to_hir,
        tcx,
        excluded_statements: excluded_ast,
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
        excluded_roots: excluded_hir,
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
    excluded_statements: &'a FxHashSet<NodeId>,
    preservable: bool,
}

impl<'ast> visit::Visitor<'ast> for SurfacePreservationCheck<'_, '_> {
    fn visit_stmt(&mut self, statement: &'ast Stmt) {
        if self.excluded_statements.contains(&statement.id) {
            return;
        }
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
    excluded_roots: &'a FxHashSet<HirId>,
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
        if !self.preservable || self.excluded_roots.contains(&statement.hir_id) {
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
        if !self.preservable || self.excluded_roots.contains(&expression.hir_id) {
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
    preserved_shell_statements: &'a BTreeSet<u32>,
    rule_applied_statements: &'a BTreeSet<u32>,
    type_speller: &'a TypeSpeller<'a, 'tcx>,
    function_path: &'a str,
    error: Option<GenerationError>,
    tcx: TyCtxt<'tcx>,
}

impl MutVisitor for Skeletonizer<'_, '_> {
    fn flat_map_stmt(&mut self, mut stmt: Stmt) -> SmallVec<[Stmt; 1]> {
        if self.error.is_some() {
            return smallvec![stmt];
        }
        let requires_transformation = statement_numeric_label(&stmt)
            .is_none_or(|label| self.statements_requiring_transformation.contains(&label));
        let rule_applied = statement_numeric_label(&stmt)
            .is_some_and(|label| self.rule_applied_statements.contains(&label));
        let preserved_shell = statement_numeric_label(&stmt)
            .is_some_and(|label| self.preserved_shell_statements.contains(&label));
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
                    Ok(Some(ty.clone()))
                }
                (Some(kind), source_hint) => target_type(
                    inferred,
                    kind,
                    None,
                    source_hint,
                    self.type_speller,
                    self.function_path,
                    &format!("local `{}`", local_binding_name(&local.pat)),
                )
                .map(Some),
                (None, Some(ty)) => Ok(Some(ty.clone())),
                (None, None)
                    if matches!(
                        inferred.kind(),
                        ty::TyKind::FnDef(..)
                            | ty::TyKind::FnPtr(..)
                            | ty::TyKind::Closure(..)
                            | ty::TyKind::CoroutineClosure(..)
                            | ty::TyKind::Coroutine(..)
                            | ty::TyKind::CoroutineWitness(..)
                    ) =>
                {
                    Ok(None)
                }
                (None, None) => self
                    .type_speller
                    .render_semantic_type(inferred)
                    .map(Some)
                    .map_err(|reason| {
                        type_spelling_error(
                            self.function_path,
                            &format!("local `{}`", local_binding_name(&local.pat)),
                            inferred,
                            reason,
                            self.tcx,
                        )
                    }),
            };
            match ty {
                Ok(ty) => local.ty = ty.map(P),
                Err(error) => {
                    self.error = Some(error);
                    return smallvec![stmt];
                }
            }
        }
        if !requires_transformation {
            if rule_applied || preserved_shell {
                self.visit_labeled_descendants(&mut stmt);
            }
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

impl Skeletonizer<'_, '_> {
    fn visit_labeled_descendants(&mut self, statement: &mut Stmt) {
        if let StmtKind::Let(local) = &mut statement.kind
            && let LocalKind::InitElse(_, else_block) = &mut local.kind
        {
            self.visit_block(else_block);
        }
        let expression = match &mut statement.kind {
            StmtKind::Let(local) => match &mut local.kind {
                LocalKind::Init(expression) | LocalKind::InitElse(expression, _) => expression,
                LocalKind::Decl => return,
            },
            StmtKind::Expr(expression) | StmtKind::Semi(expression) => expression,
            _ => return,
        };
        let expression = match &mut expression.kind {
            ExprKind::Ret(Some(value)) | ExprKind::Break(_, Some(value)) => value,
            _ => expression,
        };
        match &mut expression.kind {
            ExprKind::If(_, then_block, else_expression) => {
                self.visit_block(then_block);
                if let Some(else_expression) = else_expression {
                    self.visit_control_descendants(else_expression);
                }
            }
            ExprKind::While(_, body, _) | ExprKind::Loop(body, ..) | ExprKind::Block(body, _) => {
                self.visit_block(body)
            }
            ExprKind::ForLoop { body, .. } => self.visit_block(body),
            ExprKind::Match(_, arms, _) => {
                for arm in arms {
                    if let Some(body) = &mut arm.body
                        && let ExprKind::Block(block, _) = &mut body.kind
                    {
                        self.visit_block(block);
                    }
                }
            }
            _ => {}
        }
    }

    fn visit_control_descendants(&mut self, expression: &mut Expr) {
        match &mut expression.kind {
            ExprKind::Block(block, _) => self.visit_block(block),
            ExprKind::If(_, then_block, else_expression) => {
                self.visit_block(then_block);
                if let Some(else_expression) = else_expression {
                    self.visit_control_descendants(else_expression);
                }
            }
            _ => {}
        }
    }
}

fn local_binding_name(pattern: &Pat) -> String {
    match &pattern.kind {
        PatKind::Ident(_, ident, _) => ident.to_string(),
        _ => "<pattern>".to_owned(),
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

pub(crate) fn is_restricted_conditional(expr: &Expr) -> bool {
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

pub(crate) fn collect_opaque_nested_ifs(
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

struct ForeignFunctionVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    names: BTreeSet<String>,
}

impl ForeignFunctionVisitor<'_> {
    fn add_res(&mut self, res: Res) {
        let Res::Def(DefKind::Fn, def_id) = res else {
            return;
        };
        if self.tcx.is_foreign_item(def_id) {
            self.names.insert(self.tcx.item_name(def_id).to_string());
        }
    }
}

impl<'tcx> Visitor<'tcx> for ForeignFunctionVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_path(&mut self, path: &hir::Path<'tcx>, _hir_id: HirId) {
        self.add_res(path.res);
        intravisit::walk_path(self, path);
    }
}

fn collect_foreign_function_names<'tcx>(
    item: &'tcx hir::Item<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Vec<String> {
    let hir::ItemKind::Fn { body, .. } = item.kind else { unreachable!() };
    let mut visitor = ForeignFunctionVisitor {
        tcx,
        names: BTreeSet::new(),
    };
    visitor.visit_body(tcx.hir_body(body));
    visitor.names.into_iter().collect()
}

#[cfg(test)]
mod emitted_view_tests;

#[cfg(test)]
mod tests;
