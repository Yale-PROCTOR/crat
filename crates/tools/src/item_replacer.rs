use std::{
    collections::{HashMap, HashSet},
    panic::{AssertUnwindSafe, catch_unwind},
};

use rustc_ast::{
    AttrKind, Attribute, BindingMode, BlockCheckMode, ByRef, Crate, Expr, ExprKind, Extern,
    FnRetTy, GenericParamKind, Item, ItemKind, LocalKind, NodeId, Pat, PatKind, Safety, Stmt,
    StmtKind, Ty, TyKind,
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
    intravisit::{self, Visitor as HirVisitor},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Ident, Symbol, def_id::LocalDefId, sym};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use thin_vec::ThinVec;

use crate::{
    SkeletonView,
    preservation::{
        canonical_statement_group, canonicalize_function_with_view, validate_skeleton_view,
    },
    printf::{parse_print_macro_statement, validate_print_macro_statement},
    skeleton::{
        annotate_function, collect_opaque_nested_ifs, is_supported_two_argument_main_0,
        render_statement_group,
    },
};

const REPLACEMENT_SCHEMA_VERSION: u64 = 1;
type PreparedTransformations = (HashMap<String, P<Item>>, Vec<ReplacementStatementPair>);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplacementRequest {
    pub schema_version: u64,
    pub items: Vec<ReplacementItem>,
    pub transformation: String,
    pub accepted_correspondence: Vec<CallableCorrespondence>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallableCorrespondence {
    pub item_id: u64,
    pub logical_path: String,
    pub implementation_path: String,
    pub wrapper_path: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplacementItem {
    pub id: u64,
    pub path: String,
    pub name: String,
    pub view: SkeletonView,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplacementOutput {
    pub source: String,
    pub statement_pairs: Vec<ReplacementStatementPair>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtendedReplacementOutput {
    pub replacement: ReplacementOutput,
    pub observation_source: String,
    pub accepted_correspondence: Vec<CallableCorrespondence>,
    pub new_correspondence: Vec<CallableCorrespondence>,
    pub current_items: Vec<CurrentObservationItem>,
    pub source_stubs: Vec<SourceStub>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceStub {
    pub item_id: u64,
    pub path: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FinalizedProject {
    pub source: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CurrentObservationItem {
    pub item_id: u64,
    pub logical_path: String,
    pub source_copy_path: String,
    pub implementation_path: String,
    pub wrapper_path: Option<String>,
    pub transform_labels: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ReplacementStatementPair {
    pub item_id: u64,
    pub path: String,
    pub label: u32,
    pub after_statement: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplacementErrorKind {
    InvalidRequest,
    InvalidTransformation,
    TargetResolution,
    UnsupportedCallRewrite,
    RewriteFailure,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReplacementError {
    pub kind: ReplacementErrorKind,
    pub item: Option<Box<ReplacementItem>>,
    pub message: String,
}

pub fn replacement_request_from_json(input: &str) -> Result<ReplacementRequest, ReplacementError> {
    let request = serde_json::from_str(input).map_err(|error| ReplacementError {
        kind: ReplacementErrorKind::InvalidRequest,
        item: None,
        message: format!("replacement request is not valid schema-version-1 JSON: {error}"),
    })?;
    with_parse_session(|| {
        validate_request(&request)?;
        Ok(request)
    })
}

pub fn normalize_target_safety(source: &str) -> Result<String, ReplacementError> {
    with_parse_session(|| {
        let mut krate = parse_crate(source, ReplacementErrorKind::RewriteFailure)?;
        SafetyNormalizer.visit_crate(&mut krate);
        Ok(pprust::crate_to_string_for_macros(&krate))
    })
}

pub fn make_initial_source(source: &str) -> Result<String, ReplacementError> {
    with_parse_session(|| {
        let mut krate = parse_crate(source, ReplacementErrorKind::RewriteFailure)?;
        retain_non_function_items(&mut krate.items);
        Ok(pprust::crate_to_string_for_macros(&krate))
    })
}

fn retain_non_function_items(items: &mut ThinVec<P<Item>>) {
    items.retain(|item| !matches!(&item.kind, ItemKind::Fn(function) if function.body.is_some()));
    for item in items {
        if let ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(children, ..)) = &mut item.kind {
            retain_non_function_items(children);
        }
    }
}

fn function_at_path<'a>(items: &'a [P<Item>], path: &[String]) -> Option<&'a P<Item>> {
    let (first, rest) = path.split_first()?;
    if rest.is_empty() {
        return items.iter().find(|item| matches!(&item.kind, ItemKind::Fn(function) if function.ident.to_string() == *first));
    }
    let item = items.iter().find(|item| matches!(&item.kind, ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(..)) if ident.to_string() == *first))?;
    let ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(children, ..)) = &item.kind else {
        return None;
    };
    function_at_path(children, rest)
}

fn insert_item_at_path(
    items: &mut ThinVec<P<Item>>,
    module_path: &[String],
    item: P<Item>,
) -> Result<(), ReplacementError> {
    if let Some((first, rest)) = module_path.split_first() {
        let module = items.iter_mut().find(|item| {
            matches!(&item.kind, ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(..)) if ident.to_string() == *first)
        }).ok_or_else(|| global_error(ReplacementErrorKind::TargetResolution, format!("partial target has no inline module `{first}`")))?;
        let ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(children, ..)) = &mut module.kind else {
            unreachable!()
        };
        insert_item_at_path(children, rest, item)
    } else {
        let name = item
            .kind
            .ident()
            .expect("inserted item has an identifier")
            .to_string();
        if items.iter().any(|existing| matches!(&existing.kind, ItemKind::Fn(function) if function.ident.to_string() == name)) {
            return Err(global_error(ReplacementErrorKind::TargetResolution, format!("partial target already contains `{name}`")));
        }
        items.push(item);
        Ok(())
    }
}

pub fn add_functions_with_observations(
    analysis_source: &str,
    partial_source: &str,
    request: &ReplacementRequest,
    tcx: TyCtxt<'_>,
) -> Result<ExtendedReplacementOutput, ReplacementError> {
    validate_request(request)?;
    let (transformations, statement_pairs) = prepare_transformations(request)?;
    let mut analysis = parse_crate(analysis_source, ReplacementErrorKind::RewriteFailure)?;
    let ast_to_hir = map_surface_to_hir(&mut analysis, tcx)?;
    let mut functions = vec![];
    let mut occupied = HashMap::new();
    collect_current_functions(
        &analysis.items,
        &ast_to_hir.global_map,
        &mut vec![],
        &mut functions,
        &mut occupied,
    )?;
    let mut partial = parse_crate(partial_source, ReplacementErrorKind::RewriteFailure)?;
    let mut analysis_context = analysis.clone();
    let mut partial_context = partial.clone();
    retain_non_function_items(&mut analysis_context.items);
    retain_non_function_items(&mut partial_context.items);
    if pprust::crate_to_string_for_macros(&analysis_context)
        != pprust::crate_to_string_for_macros(&partial_context)
    {
        return Err(global_error(
            ReplacementErrorKind::TargetResolution,
            "partial target has different non-function context from analysis source".to_owned(),
        ));
    }
    let accepted = request
        .accepted_correspondence
        .iter()
        .map(|entry| (entry.logical_path.as_str(), entry))
        .collect::<HashMap<_, _>>();
    let requested_paths = request
        .items
        .iter()
        .map(|item| item.path.as_str())
        .collect::<HashSet<_>>();
    let partial_functions = collect_function_paths(&partial.items, &[]);
    if partial_functions.len() != accepted.len()
        || partial_functions
            .iter()
            .any(|path| !accepted.contains_key(path.as_str()))
    {
        return Err(global_error(
            ReplacementErrorKind::TargetResolution,
            "partial target functions do not match accepted correspondence".to_owned(),
        ));
    }
    let mut accepted_sources = vec![];
    for record in &request.accepted_correspondence {
        if record.wrapper_path.is_some()
            || record.logical_path != record.implementation_path
            || requested_paths.contains(record.logical_path.as_str())
        {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                "accepted correspondence is not an additive implementation set".to_owned(),
            ));
        }
        let original = functions
            .iter()
            .find(|function| function.path == record.logical_path)
            .ok_or_else(|| {
                global_error(
                    ReplacementErrorKind::TargetResolution,
                    format!(
                        "accepted function `{}` is absent from analysis source",
                        record.logical_path
                    ),
                )
            })?;
        let path = record
            .logical_path
            .split("::")
            .map(str::to_owned)
            .collect::<Vec<_>>();
        let target = function_at_path(&partial.items, &path).ok_or_else(|| {
            global_error(
                ReplacementErrorKind::TargetResolution,
                format!(
                    "accepted function `{}` is absent from partial target",
                    record.logical_path
                ),
            )
        })?;
        let (ItemKind::Fn(box original_fn), ItemKind::Fn(box target_fn)) =
            (&original.item.kind, &target.kind)
        else {
            unreachable!()
        };
        accepted_sources.push((
            original.def_id,
            record.item_id,
            original,
            signature_types(original_fn) != signature_types(target_fn),
        ));
    }
    accepted_sources.sort_by_key(|(_, item_id, _, _)| *item_id);

    let mut plans = vec![];
    let mut reserved = occupied;
    for requested in &request.items {
        let current = functions
            .iter()
            .find(|function| function.path == requested.path)
            .ok_or_else(|| {
                item_error(
                    ReplacementErrorKind::TargetResolution,
                    requested,
                    format!(
                        "analysis source contains no free function at path `{}`",
                        requested.path
                    ),
                )
            })?;
        if function_at_path(
            &partial.items,
            &requested
                .path
                .split("::")
                .map(str::to_owned)
                .collect::<Vec<_>>(),
        )
        .is_some()
        {
            return Err(item_error(
                ReplacementErrorKind::TargetResolution,
                requested,
                "function is already installed in partial target".to_owned(),
            ));
        }
        validate_current_target(current, requested)?;
        let transformation = transformations
            .get(&requested.name)
            .expect("validated transformation set");
        let (ItemKind::Fn(box current_fn), ItemKind::Fn(box transformed_fn)) =
            (&current.item.kind, &transformation.kind)
        else {
            unreachable!()
        };
        validate_transformed_header(current_fn, transformed_fn, requested)?;
        let labeled = compose_implementation(&current.item, transformation, requested)?;
        let mut implementation = labeled.clone();
        let ItemKind::Fn(box implementation_fn) = &mut implementation.kind else { unreachable!() };
        ProctorLabelRemover.visit_block(implementation_fn.body.as_mut().unwrap());
        let source_copy_name = allocate_generated_name(current, &mut reserved, "__proctor_source");
        let source_copy_path = absolute_item_path(&current.module_path, &source_copy_name)
            .trim_start_matches("crate::")
            .to_owned();
        plans.push(ReplacementPlan {
            requested: requested.clone(),
            current_def_id: current.def_id,
            implementation,
            observation_implementation: labeled,
            source_copy_name,
            source_copy_path,
        });
    }

    let current_ids = plans
        .iter()
        .map(|plan| plan.current_def_id)
        .collect::<FxHashSet<_>>();
    let mut rewrite_paths = plans
        .iter()
        .map(|plan| {
            (
                plan.current_def_id,
                format!("crate::{}", plan.source_copy_path),
            )
        })
        .collect::<FxHashMap<_, _>>();
    let mut stubs = vec![];
    for (def_id, item_id, original, changed) in &accepted_sources {
        if *changed {
            let name = allocate_generated_name(original, &mut reserved, "__proctor_source_stub");
            let path = absolute_item_path(&original.module_path, &name)
                .trim_start_matches("crate::")
                .to_owned();
            rewrite_paths.insert(*def_id, format!("crate::{path}"));
            stubs.push((
                *def_id,
                SourceStub {
                    item_id: *item_id,
                    path,
                },
                name,
                *original,
            ));
        }
    }
    let targets = rewrite_paths.keys().copied().collect::<FxHashSet<_>>();
    validate_additive_macro_rewrites(
        &analysis,
        &ast_to_hir,
        &functions,
        &current_ids,
        &targets,
        tcx,
    )?;
    let mut collector = SourceCopyCallCollector {
        ast_to_hir: &ast_to_hir,
        tcx,
        source_paths: &rewrite_paths,
        current_scc: &current_ids,
        current_function: None,
        rewrites: FxHashMap::default(),
    };
    collector.visit_crate(&analysis);
    let used_paths = collector.rewrites.values().cloned().collect::<HashSet<_>>();
    CallRewriter {
        rewrites: collector.rewrites,
    }
    .visit_crate(&mut analysis);

    let mut observation = partial.clone();
    for plan in &plans {
        let module_path = plan
            .requested
            .path
            .split("::")
            .map(str::to_owned)
            .collect::<Vec<_>>();
        insert_item_at_path(
            &mut partial.items,
            &module_path[..module_path.len() - 1],
            plan.implementation.clone(),
        )?;
        let mut labeled = plan.observation_implementation.clone();
        labeled
            .attrs
            .retain(|attribute| !is_export_attribute(attribute));
        insert_item_at_path(
            &mut observation.items,
            &module_path[..module_path.len() - 1],
            labeled,
        )?;
        let original = function_at_path(&analysis.items, &module_path)
            .expect("resolved current function exists");
        let mut copy = original.clone();
        copy.attrs.clear();
        copy.vis = crate_visible();
        let opaque = collect_opaque_nested_ifs(&copy, &plan.requested.path).map_err(|error| {
            item_error(
                ReplacementErrorKind::RewriteFailure,
                &plan.requested,
                error.message,
            )
        })?;
        let ItemKind::Fn(box function) = &mut copy.kind else { unreachable!() };
        function.ident = parsed_ident(&plan.source_copy_name);
        function.sig.header.ext = Extern::None;
        ProctorLabelRemover.visit_block(function.body.as_mut().unwrap());
        annotate_function(&mut copy, &opaque);
        insert_item_at_path(
            &mut observation.items,
            &module_path[..module_path.len() - 1],
            copy,
        )?;
    }
    let mut source_stubs = vec![];
    for (_, stub, name, original) in stubs {
        if !used_paths.contains(&format!("crate::{}", stub.path)) {
            continue;
        }
        let mut item = original.item.clone();
        item.attrs.clear();
        item.vis = crate_visible();
        let ItemKind::Fn(box function) = &mut item.kind else { unreachable!() };
        function.ident = parsed_ident(&name);
        function.sig.header.ext = Extern::None;
        function.body = Some(parse_body("{ todo!() }")?);
        insert_item_at_path(&mut observation.items, &original.module_path, item)?;
        source_stubs.push(stub);
    }
    source_stubs.sort_by_key(|stub| stub.item_id);
    let new_correspondence = plans
        .iter()
        .map(|plan| CallableCorrespondence {
            item_id: plan.requested.id,
            logical_path: plan.requested.path.clone(),
            implementation_path: plan.requested.path.clone(),
            wrapper_path: None,
        })
        .collect::<Vec<_>>();
    let mut combined = request.accepted_correspondence.clone();
    combined.extend(new_correspondence.iter().cloned());
    validate_correspondence(&combined)?;
    let current_items = plans
        .iter()
        .map(|plan| CurrentObservationItem {
            item_id: plan.requested.id,
            logical_path: plan.requested.path.clone(),
            source_copy_path: plan.source_copy_path.clone(),
            implementation_path: plan.requested.path.clone(),
            wrapper_path: None,
            transform_labels: plan.requested.view.transform_labels(),
        })
        .collect();
    Ok(ExtendedReplacementOutput {
        replacement: ReplacementOutput {
            source: pprust::crate_to_string_for_macros(&partial),
            statement_pairs,
        },
        observation_source: pprust::crate_to_string_for_macros(&observation),
        accepted_correspondence: request.accepted_correspondence.clone(),
        new_correspondence,
        current_items,
        source_stubs,
    })
}

fn crate_visible() -> rustc_ast::Visibility {
    utils::ast::parse_item("pub(crate) fn __visibility() {}".to_owned()).vis
}

fn collect_function_paths(items: &[P<Item>], module: &[String]) -> Vec<String> {
    let mut paths = vec![];
    for item in items {
        match &item.kind {
            ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(children, ..)) => {
                let mut nested = module.to_vec();
                nested.push(ident.to_string());
                paths.extend(collect_function_paths(children, &nested));
            }
            ItemKind::Fn(function) if function.body.is_some() => {
                paths.push(
                    module
                        .iter()
                        .cloned()
                        .chain(std::iter::once(function.ident.to_string()))
                        .collect::<Vec<_>>()
                        .join("::"),
                );
            }
            _ => {}
        }
    }
    paths
}

fn validate_additive_macro_rewrites(
    analysis: &Crate,
    ast_to_hir: &utils::ir::AstToHir,
    functions: &[CurrentFunction],
    callers: &FxHashSet<LocalDefId>,
    targets: &FxHashSet<LocalDefId>,
    tcx: TyCtxt<'_>,
) -> Result<(), ReplacementError> {
    let mut ast_counts = FxHashMap::default();
    CurrentSurfaceCallCounter {
        ast_to_hir,
        tcx,
        targets,
        callers,
        current_function: None,
        ast_counts: &mut ast_counts,
    }
    .visit_crate(analysis);
    for function in functions
        .iter()
        .filter(|function| callers.contains(&function.def_id))
    {
        let hir::ItemKind::Fn { body, .. } =
            tcx.hir_node_by_def_id(function.def_id).expect_item().kind
        else {
            continue;
        };
        let mut counter = HirDirectCallCounter {
            wrapped: targets,
            include_expansions: true,
            counts: FxHashMap::default(),
        };
        counter.visit_body(tcx.hir_body(body));
        for target in targets {
            if counter.counts.get(target).copied().unwrap_or(0)
                > ast_counts
                    .get(&(function.def_id, *target))
                    .copied()
                    .unwrap_or(0)
            {
                return Err(global_error(
                    ReplacementErrorKind::UnsupportedCallRewrite,
                    format!(
                        "a required source-copy call redirect in `{}` occurs inside a macro token input",
                        function.path
                    ),
                ));
            }
        }
    }
    Ok(())
}

pub fn finalize_additive_source(
    analysis_source: &str,
    partial_source: &str,
    target_kind: &str,
    api_functions: &[String],
    tcx: TyCtxt<'_>,
) -> Result<FinalizedProject, ReplacementError> {
    if !matches!(target_kind, "library" | "executable")
        || (target_kind == "executable" && !api_functions.is_empty())
        || api_functions.iter().any(|entry| entry == "main")
    {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            "invalid target kind or API function list".to_owned(),
        ));
    }
    let mut analysis = parse_crate(analysis_source, ReplacementErrorKind::RewriteFailure)?;
    let ast_to_hir = map_surface_to_hir(&mut analysis, tcx)?;
    let mut functions = vec![];
    let mut occupied = HashMap::new();
    collect_current_functions(
        &analysis.items,
        &ast_to_hir.global_map,
        &mut vec![],
        &mut functions,
        &mut occupied,
    )?;
    let mut partial = parse_crate(partial_source, ReplacementErrorKind::RewriteFailure)?;
    let mut analysis_context = analysis.clone();
    let mut partial_context = partial.clone();
    retain_non_function_items(&mut analysis_context.items);
    retain_non_function_items(&mut partial_context.items);
    if pprust::crate_to_string_for_macros(&analysis_context)
        != pprust::crate_to_string_for_macros(&partial_context)
    {
        return Err(global_error(
            ReplacementErrorKind::TargetResolution,
            "partial target has different non-function context from analysis source".to_owned(),
        ));
    }
    let expected = functions
        .iter()
        .filter(|function| !function_named(function, "main"))
        .map(|function| function.path.as_str())
        .collect::<HashSet<_>>();
    let installed = collect_function_paths(&partial.items, &[]);
    if installed.len() != expected.len()
        || installed
            .iter()
            .any(|path| !expected.contains(path.as_str()))
    {
        return Err(global_error(
            ReplacementErrorKind::TargetResolution,
            "partial target does not contain exactly the accepted non-main functions".to_owned(),
        ));
    }
    for main_0 in functions.iter().filter(|function| {
        matches!(&function.item.kind, ItemKind::Fn(body) if is_supported_two_argument_main_0(body))
    }) {
        let siblings = functions
            .iter()
            .filter(|function| {
                function.module_path == main_0.module_path && function_named(function, "main")
            })
            .count();
        if siblings != 1 {
            return Err(global_error(
                ReplacementErrorKind::RewriteFailure,
                format!(
                    "two-argument `main_0` requires exactly one sibling `main`, found {siblings}"
                ),
            ));
        }
    }
    for api in api_functions {
        let matched = functions.iter().any(|function| {
            let ItemKind::Fn(box body) = &function.item.kind else { unreachable!() };
            body.ident.name.as_str() == api
                || function.item.attrs.iter().any(|attr| {
                    attr.has_name(sym::export_name)
                        && attr.value_str().is_some_and(|name| name.as_str() == api)
                })
        });
        if !matched {
            return Err(global_error(
                ReplacementErrorKind::TargetResolution,
                format!("API function `{api}` did not match any source function"),
            ));
        }
    }
    for current in functions
        .iter()
        .filter(|function| function_named(function, "main"))
    {
        let main_0 = functions.iter().find(|function| {
            function.module_path == current.module_path && function_named(function, "main_0")
        });
        let main = if main_0.is_some_and(|sibling| matches!(&sibling.item.kind, ItemKind::Fn(function) if is_supported_two_argument_main_0(function))) {
            fixed_main_item()?
        } else {
            current.item.clone()
        };
        insert_item_at_path(&mut partial.items, &current.module_path, main)?;
    }
    Ok(FinalizedProject {
        source: pprust::crate_to_string_for_macros(&partial),
    })
}

fn function_named(function: &CurrentFunction, name: &str) -> bool {
    matches!(&function.item.kind, ItemKind::Fn(body) if body.ident.name.as_str() == name)
}

fn prepare_transformations(
    request: &ReplacementRequest,
) -> Result<PreparedTransformations, ReplacementError> {
    let returned_transformations = parse_transformations(request)?;
    let mut transformations = HashMap::new();
    let mut statement_pairs = vec![];
    for requested in &request.items {
        let expected = parse_replacement_skeleton(requested)?;
        let returned = returned_transformations
            .get(&requested.name)
            .expect("request validation established the function set");
        let canonical = canonicalize_function_with_view(&expected, returned, &requested.view, true)
            .map_err(|problem| {
                item_error(
                    ReplacementErrorKind::InvalidTransformation,
                    requested,
                    format!("{}: {}", problem.code, problem.message),
                )
            })?;
        let existing_temporaries = existing_temporary_bindings(&expected);
        for label in requested.view.transform_labels() {
            let template_metadata = requested
                .view
                .statement_pair_metadata
                .iter()
                .find(|metadata| metadata.label == label)
                .and_then(|metadata| metadata.printf_template.as_ref());
            let expected_group = canonical_statement_group(&expected, label).ok_or_else(|| {
                item_error(
                    ReplacementErrorKind::InvalidTransformation,
                    requested,
                    format!("expected skeleton contains no expansion group for label {label}"),
                )
            })?;
            if expected_group.len() != 1 || !matches!(expected_group[0].kind, StmtKind::MacCall(..))
            {
                if template_metadata.is_some() {
                    return Err(item_error(
                        ReplacementErrorKind::InvalidRequest,
                        requested,
                        format!("invalid print template group at label {label}"),
                    ));
                }
                continue;
            }
            {
                match parse_print_macro_statement(&expected_group[0]) {
                    Ok(template) => template,
                    Err(problem) if template_metadata.is_some() => {
                        return Err(item_error(
                            ReplacementErrorKind::InvalidRequest,
                            requested,
                            format!("{}: {}", problem.code, problem.message),
                        ));
                    }
                    Err(_) => continue,
                };
                let Some(template_metadata) = template_metadata else {
                    return Err(item_error(
                        ReplacementErrorKind::InvalidRequest,
                        requested,
                        format!("print template label {label} has no trusted metadata"),
                    ));
                };
                let group = canonical_statement_group(&canonical, label).ok_or_else(|| {
                    item_error(
                        ReplacementErrorKind::InvalidTransformation,
                        requested,
                        format!(
                            "canonical replacement contains no expansion group for label {label}"
                        ),
                    )
                })?;
                if group.len() != 1 {
                    return Err(item_error(
                        ReplacementErrorKind::InvalidTransformation,
                        requested,
                        format!("print template label {label} must contain exactly one statement"),
                    ));
                }
                validate_print_macro_statement(
                    &group[0],
                    &template_metadata.rust_format,
                    template_metadata.argument_count as usize,
                )
                .map_err(|problem| {
                    item_error(
                        ReplacementErrorKind::InvalidTransformation,
                        requested,
                        format!("{}: {}", problem.code, problem.message),
                    )
                })?;
                let parsed = parse_print_macro_statement(&group[0]).map_err(|problem| {
                    item_error(
                        ReplacementErrorKind::InvalidTransformation,
                        requested,
                        format!("{}: {}", problem.code, problem.message),
                    )
                })?;
                validate_print_arguments_independently(&parsed.arguments, &existing_temporaries)
                    .map_err(|message| {
                        item_error(
                            ReplacementErrorKind::InvalidTransformation,
                            requested,
                            message,
                        )
                    })?;
            }
        }
        for label in requested.view.report_labels() {
            let group = canonical_statement_group(&canonical, label).ok_or_else(|| {
                item_error(
                    ReplacementErrorKind::InvalidTransformation,
                    requested,
                    format!("canonical replacement contains no expansion group for label {label}"),
                )
            })?;
            statement_pairs.push(ReplacementStatementPair {
                item_id: requested.id,
                path: requested.path.clone(),
                label,
                after_statement: render_statement_group(&group),
            });
        }
        transformations.insert(requested.name.clone(), canonical);
    }
    statement_pairs.sort_by_key(|pair| (pair.item_id, pair.label));
    Ok((transformations, statement_pairs))
}

struct SafetyNormalizer;

impl MutVisitor for SafetyNormalizer {
    fn visit_item(&mut self, item: &mut Item) {
        if let ItemKind::Fn(box function) = &mut item.kind
            && function.body.is_some()
            && function.ident.name.as_str() != "main"
        {
            function.sig.header.safety = Safety::Unsafe(function.sig.span);
        }
        mut_visit::walk_item(self, item);
    }
}

#[derive(Clone)]
struct CurrentFunction {
    path: String,
    module_path: Vec<String>,
    item: P<Item>,
    def_id: LocalDefId,
}

struct ReplacementPlan {
    requested: ReplacementItem,
    current_def_id: LocalDefId,
    implementation: P<Item>,
    observation_implementation: P<Item>,
    source_copy_name: String,
    source_copy_path: String,
}

fn validate_request(request: &ReplacementRequest) -> Result<(), ReplacementError> {
    if request.schema_version != REPLACEMENT_SCHEMA_VERSION {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            format!(
                "replacement request schema version {} is unsupported; use version 1",
                request.schema_version
            ),
        ));
    }
    if request.items.is_empty() {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            "replacement request must contain at least one item".to_owned(),
        ));
    }
    let mut ids = HashSet::new();
    let mut paths = HashSet::new();
    let mut names = HashSet::new();
    validate_correspondence(&request.accepted_correspondence)?;
    for item in &request.items {
        if !ids.insert(item.id) {
            return Err(item_error(
                ReplacementErrorKind::InvalidRequest,
                item,
                format!("replacement item ID {} is duplicated", item.id),
            ));
        }
        if !paths.insert(item.path.as_str()) {
            return Err(item_error(
                ReplacementErrorKind::InvalidRequest,
                item,
                format!("replacement path `{}` is duplicated", item.path),
            ));
        }
        if !names.insert(item.name.as_str()) {
            return Err(item_error(
                ReplacementErrorKind::InvalidRequest,
                item,
                format!("replacement name `{}` is duplicated", item.name),
            ));
        }
        let segments = valid_full_path(&item.path).ok_or_else(|| {
            item_error(
                ReplacementErrorKind::InvalidRequest,
                item,
                format!(
                    "`{}` is not a valid crate-relative Rust item path",
                    item.path
                ),
            )
        })?;
        if segments.last().is_none_or(|segment| segment != &item.name) {
            return Err(item_error(
                ReplacementErrorKind::InvalidRequest,
                item,
                format!(
                    "replacement path `{}` does not end with requested name `{}`",
                    item.path, item.name
                ),
            ));
        }
        parse_replacement_skeleton(item)?;
    }
    parse_transformations(request)?;
    Ok(())
}

fn validate_correspondence(records: &[CallableCorrespondence]) -> Result<(), ReplacementError> {
    let mut item_ids = HashSet::new();
    let mut logical = HashSet::new();
    let mut implementations = HashSet::new();
    let mut wrappers = HashSet::new();
    for record in records {
        if !item_ids.insert(record.item_id) {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                format!(
                    "accepted correspondence item ID {} is duplicated",
                    record.item_id
                ),
            ));
        }
        for (kind, path) in [
            ("logical", &record.logical_path),
            ("implementation", &record.implementation_path),
        ] {
            if valid_full_path(path).is_none() {
                return Err(global_error(
                    ReplacementErrorKind::InvalidRequest,
                    format!("accepted correspondence {kind} path `{path}` is invalid"),
                ));
            }
        }
        if !logical.insert(record.logical_path.as_str()) {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                format!(
                    "accepted correspondence logical path `{}` is duplicated",
                    record.logical_path
                ),
            ));
        }
        if !implementations.insert(record.implementation_path.as_str()) {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                format!(
                    "accepted correspondence implementation path `{}` is duplicated",
                    record.implementation_path
                ),
            ));
        }
        if let Some(wrapper) = &record.wrapper_path
            && (valid_full_path(wrapper).is_none() || !wrappers.insert(wrapper.as_str()))
        {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                format!(
                    "accepted correspondence wrapper path `{wrapper}` is invalid or duplicated"
                ),
            ));
        }
    }
    for (index, record) in records.iter().enumerate() {
        for (other_index, other) in records.iter().enumerate() {
            if index != other_index && record.logical_path == other.implementation_path {
                return Err(global_error(
                    ReplacementErrorKind::InvalidRequest,
                    format!(
                        "accepted correspondence path `{}` has contradictory roles",
                        record.logical_path
                    ),
                ));
            }
        }
        if let Some(wrapper) = &record.wrapper_path
            && (logical.contains(wrapper.as_str()) || implementations.contains(wrapper.as_str()))
        {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                format!(
                    "accepted correspondence wrapper path `{wrapper}` collides with a logical or implementation path"
                ),
            ));
        }
    }
    Ok(())
}

fn existing_temporary_bindings(item: &Item) -> HashSet<String> {
    #[derive(Default)]
    struct Collector(HashSet<String>);
    impl<'ast> Visitor<'ast> for Collector {
        fn visit_pat(&mut self, pattern: &'ast Pat) {
            if let PatKind::Ident(_, ident, _) = &pattern.kind {
                let name = ident.name.to_string();
                if name.starts_with("proctor_temp_var_") {
                    self.0.insert(name);
                }
            }
            visit::walk_pat(self, pattern);
        }
    }
    let mut collector = Collector::default();
    collector.visit_item(item);
    collector.0
}

fn validate_print_arguments_independently(
    arguments: &[P<Expr>],
    existing_temporaries: &HashSet<String>,
) -> Result<(), String> {
    const TEMP_PREFIX: &str = "proctor_temp_var_";

    #[derive(Default)]
    struct Defense {
        error: Option<String>,
        declared: HashMap<String, usize>,
        existing: HashSet<String>,
    }

    fn is_temp_name(name: &str) -> bool {
        name.strip_prefix(TEMP_PREFIX).is_some_and(|suffix| {
            !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
        })
    }

    fn macro_contains_temp(tokens: &rustc_ast::tokenstream::TokenStream) -> bool {
        use rustc_ast::{
            token::TokenKind,
            tokenstream::{TokenStream, TokenTree},
        };
        fn walk(tokens: &TokenStream) -> bool {
            tokens.iter().any(|tree| match tree {
                TokenTree::Token(token, _) => matches!(
                    token.kind,
                    TokenKind::Ident(symbol, _) if symbol.as_str().starts_with(TEMP_PREFIX)
                ),
                TokenTree::Delimited(_, _, _, inner) => walk(inner),
            })
        }
        walk(tokens)
    }

    impl<'ast> Visitor<'ast> for Defense {
        fn visit_item(&mut self, _item: &'ast Item) {
            self.error
                .get_or_insert_with(|| "print argument contains a function-local item".to_owned());
        }

        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            let has_attrs = match &statement.kind {
                StmtKind::Let(local) => !local.attrs.is_empty(),
                StmtKind::Item(item) => !item.attrs.is_empty(),
                StmtKind::Expr(expression) | StmtKind::Semi(expression) => {
                    !expression.attrs.is_empty()
                }
                StmtKind::MacCall(mac) => !mac.attrs.is_empty(),
                StmtKind::Empty => false,
            };
            if has_attrs {
                self.error.get_or_insert_with(|| {
                    "print argument contains an unsupported statement attribute".to_owned()
                });
            }
            visit::walk_stmt(self, statement);
        }

        fn visit_pat(&mut self, pattern: &'ast Pat) {
            if let PatKind::Ident(_, ident, _) = &pattern.kind {
                let name = ident.name.to_string();
                if !is_temp_name(&name) || self.existing.contains(&name) {
                    self.error.get_or_insert_with(|| {
                        format!("print argument declares unsupported local binding `{name}`")
                    });
                } else {
                    *self.declared.entry(name).or_default() += 1;
                }
            }
            visit::walk_pat(self, pattern);
        }

        fn visit_expr(&mut self, expression: &'ast Expr) {
            if !expression.attrs.is_empty() {
                self.error.get_or_insert_with(|| {
                    "print argument contains an unsupported expression attribute".to_owned()
                });
            }
            if matches!(
                expression.kind,
                ExprKind::Block(ref block, _) if matches!(block.rules, BlockCheckMode::Unsafe(..))
            ) {
                self.error.get_or_insert_with(|| {
                    "print argument contains an explicit unsafe block".to_owned()
                });
            }
            if let ExprKind::Path(_, path) = &expression.kind
                && let Some(segment) = path.segments.last()
            {
                let name = segment.ident.name.to_string();
                if name.starts_with(TEMP_PREFIX) && !is_temp_name(&name) {
                    self.error.get_or_insert_with(|| {
                        format!("print argument uses invalid generated temporary `{name}`")
                    });
                }
            }
            visit::walk_expr(self, expression);
        }

        fn visit_mac_call(&mut self, mac: &'ast rustc_ast::MacCall) {
            if macro_contains_temp(&mac.args.tokens) {
                self.error.get_or_insert_with(|| {
                    "print argument uses a generated temporary inside macro tokens".to_owned()
                });
            }
        }
    }

    struct LexicalDefense<'a> {
        declared: &'a HashMap<String, usize>,
        existing: &'a HashSet<String>,
        scopes: Vec<HashSet<String>>,
        error: Option<String>,
    }

    impl LexicalDefense<'_> {
        fn activate_pattern(&mut self, pattern: &Pat) {
            #[derive(Default)]
            struct Bindings(Vec<String>);
            impl<'ast> Visitor<'ast> for Bindings {
                fn visit_pat(&mut self, pattern: &'ast Pat) {
                    if let PatKind::Ident(_, ident, _) = &pattern.kind {
                        self.0.push(ident.name.to_string());
                    }
                    visit::walk_pat(self, pattern);
                }
            }
            let mut bindings = Bindings::default();
            bindings.visit_pat(pattern);
            for name in bindings.0 {
                if self.declared.contains_key(&name) || self.existing.contains(&name) {
                    self.scopes.last_mut().unwrap().insert(name);
                }
            }
        }

        fn visit_scoped_block(&mut self, block: &rustc_ast::Block, pattern: Option<&Pat>) {
            self.scopes.push(HashSet::new());
            if let Some(pattern) = pattern {
                self.activate_pattern(pattern);
            }
            for statement in &block.stmts {
                self.visit_stmt(statement);
            }
            self.scopes.pop();
        }

        fn active(&self, name: &str) -> bool {
            self.scopes.iter().rev().any(|scope| scope.contains(name))
        }
    }

    impl<'ast> Visitor<'ast> for LexicalDefense<'_> {
        fn visit_block(&mut self, block: &'ast rustc_ast::Block) {
            self.visit_scoped_block(block, None);
        }

        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            match &statement.kind {
                StmtKind::Let(local) => {
                    match &local.kind {
                        LocalKind::Decl => {}
                        LocalKind::Init(initializer) => self.visit_expr(initializer),
                        LocalKind::InitElse(initializer, else_block) => {
                            self.visit_expr(initializer);
                            self.visit_block(else_block);
                        }
                    }
                    self.activate_pattern(&local.pat);
                }
                StmtKind::Item(_) => {}
                StmtKind::Expr(expression) | StmtKind::Semi(expression) => {
                    self.visit_expr(expression)
                }
                StmtKind::MacCall(_) | StmtKind::Empty => {}
            }
        }

        fn visit_expr(&mut self, expression: &'ast Expr) {
            match &expression.kind {
                ExprKind::If(condition, then_block, else_expression) => {
                    if let ExprKind::Let(pattern, value, ..) = &condition.kind {
                        self.visit_expr(value);
                        self.visit_scoped_block(then_block, Some(pattern));
                    } else {
                        self.visit_expr(condition);
                        self.visit_block(then_block);
                    }
                    if let Some(else_expression) = else_expression {
                        self.visit_expr(else_expression);
                    }
                }
                ExprKind::While(condition, body, _) => {
                    if let ExprKind::Let(pattern, value, ..) = &condition.kind {
                        self.visit_expr(value);
                        self.visit_scoped_block(body, Some(pattern));
                    } else {
                        self.visit_expr(condition);
                        self.visit_block(body);
                    }
                }
                ExprKind::ForLoop {
                    pat, iter, body, ..
                } => {
                    self.visit_expr(iter);
                    self.visit_scoped_block(body, Some(pat));
                }
                ExprKind::Match(scrutinee, arms, _) => {
                    self.visit_expr(scrutinee);
                    for arm in arms {
                        self.scopes.push(HashSet::new());
                        self.activate_pattern(&arm.pat);
                        if let Some(guard) = &arm.guard {
                            self.visit_expr(guard);
                        }
                        if let Some(body) = &arm.body {
                            self.visit_expr(body);
                        }
                        self.scopes.pop();
                    }
                }
                ExprKind::Closure(closure) => {
                    self.scopes.push(HashSet::new());
                    for parameter in &closure.fn_decl.inputs {
                        self.activate_pattern(&parameter.pat);
                    }
                    self.visit_expr(&closure.body);
                    self.scopes.pop();
                }
                ExprKind::Path(None, path) if path.segments.len() == 1 => {
                    let name = path.segments[0].ident.to_string();
                    if is_temp_name(&name) && !self.active(&name) {
                        self.error.get_or_insert_with(|| {
                            format!(
                                "print argument references generated temporary `{name}` outside its lexical expansion scope"
                            )
                        });
                    }
                }
                ExprKind::MacCall(_) => {}
                _ => visit::walk_expr(self, expression),
            }
        }
    }

    let mut all_declarations = HashMap::<String, usize>::new();
    for argument in arguments {
        let mut defense = Defense {
            existing: existing_temporaries.clone(),
            ..Defense::default()
        };
        defense.visit_expr(argument);
        if let Some(error) = defense.error {
            return Err(error);
        }
        for (name, count) in &defense.declared {
            *all_declarations.entry(name.clone()).or_default() += count;
        }
        let mut lexical = LexicalDefense {
            declared: &defense.declared,
            existing: existing_temporaries,
            scopes: vec![existing_temporaries.clone()],
            error: None,
        };
        lexical.visit_expr(argument);
        if let Some(error) = lexical.error {
            return Err(error);
        }
    }
    if let Some((name, _)) = all_declarations.iter().find(|(_, count)| **count != 1) {
        return Err(format!(
            "print argument declares generated temporary `{name}` more than once"
        ));
    }
    Ok(())
}

fn parse_replacement_skeleton(item: &ReplacementItem) -> Result<P<Item>, ReplacementError> {
    let krate = parse_crate(&item.view.skeleton, ReplacementErrorKind::InvalidRequest)?;
    if krate.items.len() != 1 || !matches!(krate.items[0].kind, ItemKind::Fn(..)) {
        return Err(item_error(
            ReplacementErrorKind::InvalidRequest,
            item,
            "replacement skeleton must contain exactly one free function".to_owned(),
        ));
    }
    let skeleton = krate.items[0].clone();
    let observed_name = skeleton.kind.ident().unwrap().to_string();
    if observed_name != item.name {
        return Err(item_error(
            ReplacementErrorKind::InvalidRequest,
            item,
            format!(
                "replacement skeleton defines `{observed_name}` instead of `{}`",
                item.name
            ),
        ));
    }
    validate_skeleton_view(&skeleton, &item.view).map_err(|problem| {
        item_error(
            ReplacementErrorKind::InvalidRequest,
            item,
            format!("{}: {}", problem.code, problem.message),
        )
    })?;
    Ok(skeleton)
}

fn valid_full_path(path: &str) -> Option<Vec<String>> {
    if path.is_empty() || path.starts_with("::") || path.ends_with("::") {
        return None;
    }
    let segments = path.split("::").map(str::to_owned).collect::<Vec<_>>();
    if segments.iter().any(|segment| segment.is_empty()) {
        return None;
    }
    for segment in &segments {
        let parsed = catch_unwind(AssertUnwindSafe(|| {
            utils::ast::parse_item(format!("fn {segment}() {{}}"))
        }))
        .ok()?;
        let ItemKind::Fn(box function) = parsed.kind else {
            return None;
        };
        if function.ident.to_string() != *segment {
            return None;
        }
    }
    Some(segments)
}

fn parse_transformations(
    request: &ReplacementRequest,
) -> Result<HashMap<String, P<Item>>, ReplacementError> {
    let krate = parse_crate(
        &request.transformation,
        ReplacementErrorKind::InvalidTransformation,
    )?;
    let requested = request
        .items
        .iter()
        .map(|item| item.name.as_str())
        .collect::<HashSet<_>>();
    let mut functions = HashMap::new();
    let mut function_order = vec![];
    for item in krate.items {
        let ItemKind::Fn(box function) = &item.kind else {
            return Err(global_error(
                ReplacementErrorKind::InvalidTransformation,
                format!(
                    "transformation contains an unexpected top-level {} item",
                    item_kind_name(&item)
                ),
            ));
        };
        let name = function.ident.to_string();
        function_order.push(name.clone());
        if functions.insert(name.clone(), item).is_some() {
            return Err(global_error(
                ReplacementErrorKind::InvalidTransformation,
                format!("transformation defines function `{name}` more than once"),
            ));
        }
    }
    for item in &request.items {
        if !functions.contains_key(&item.name) {
            return Err(item_error(
                ReplacementErrorKind::InvalidTransformation,
                item,
                format!(
                    "transformation is missing requested function `{}`",
                    item.name
                ),
            ));
        }
    }
    for name in function_order {
        if !requested.contains(name.as_str()) {
            return Err(global_error(
                ReplacementErrorKind::InvalidTransformation,
                format!("transformation defines unexpected function `{name}`"),
            ));
        }
    }
    for item in &request.items {
        validate_supported_transformation(
            functions.get(&item.name).expect("function set was checked"),
            item,
        )?;
    }
    Ok(functions)
}

fn validate_supported_transformation(
    item: &Item,
    requested: &ReplacementItem,
) -> Result<(), ReplacementError> {
    let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
    if function.sig.header.coroutine_kind.is_some() {
        return Err(item_error(
            ReplacementErrorKind::InvalidTransformation,
            requested,
            "returned async functions are unsupported".to_owned(),
        ));
    }
    if function.sig.decl.c_variadic() {
        return Err(item_error(
            ReplacementErrorKind::InvalidTransformation,
            requested,
            "returned variadic functions are unsupported".to_owned(),
        ));
    }
    let allow_wildcards = is_supported_two_argument_main_0(function);
    if function
        .sig
        .decl
        .inputs
        .iter()
        .any(|parameter| simple_parameter_pattern(parameter, allow_wildcards).is_none())
    {
        return Err(item_error(
            ReplacementErrorKind::InvalidTransformation,
            requested,
            "every returned parameter must use a simple by-value identifier pattern (or `_` for two-argument `main_0`)"
                .to_owned(),
        ));
    }
    if function.generics.params.iter().any(|parameter| {
        !matches!(parameter.kind, GenericParamKind::Lifetime)
            || !parameter.attrs.is_empty()
            || !parameter.bounds.is_empty()
    }) || function.generics.where_clause.has_where_token
    {
        return Err(item_error(
            ReplacementErrorKind::InvalidTransformation,
            requested,
            "returned generics must contain only unbounded, unattributed named lifetimes and no where clause"
                .to_owned(),
        ));
    }
    Ok(())
}

fn parse_crate(source: &str, kind: ReplacementErrorKind) -> Result<Crate, ReplacementError> {
    catch_unwind(AssertUnwindSafe(|| {
        utils::ast::parse_crate(source.to_owned())
    }))
    .map_err(|_| global_error(kind, "Rust source did not parse".to_owned()))
}

fn with_parse_session<T>(
    f: impl FnOnce() -> Result<T, ReplacementError>,
) -> Result<T, ReplacementError> {
    rustc_span::create_session_if_not_set_then(rustc_span::edition::Edition::Edition2021, |_| f())
}

fn map_surface_to_hir(
    surface: &mut Crate,
    tcx: TyCtxt<'_>,
) -> Result<utils::ir::AstToHir, ReplacementError> {
    let mut mapper = utils::ir::AstToHirMapper::new(tcx);
    catch_unwind(AssertUnwindSafe(|| {
        mapper.map_crate_to_mod(surface, tcx.hir_root_module(), false);
    }))
    .map_err(|_| {
        global_error(
            ReplacementErrorKind::RewriteFailure,
            "surface AST does not structurally match the HIR for the supplied source".to_owned(),
        )
    })?;
    Ok(mapper.ast_to_hir)
}

fn collect_current_functions(
    items: &[P<Item>],
    global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
    module_path: &mut Vec<String>,
    functions: &mut Vec<CurrentFunction>,
    occupied: &mut HashMap<Vec<String>, HashSet<String>>,
) -> Result<(), ReplacementError> {
    let module_names = occupied.entry(module_path.clone()).or_default();
    for item in items {
        collect_occupied_item_names(item, module_names);
    }
    for item in items {
        match &item.kind {
            ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(children, ..)) => {
                module_path.push(ident.to_string());
                collect_current_functions(children, global_map, module_path, functions, occupied)?;
                module_path.pop();
            }
            ItemKind::Fn(box function) if function.body.is_some() => {
                let Some(def_id) = global_map.get(&item.id).copied() else {
                    return Err(global_error(
                        ReplacementErrorKind::RewriteFailure,
                        format!(
                            "source function `{}` has no mapped HIR identity",
                            function.ident
                        ),
                    ));
                };
                let name = function.ident.to_string();
                functions.push(CurrentFunction {
                    path: module_path
                        .iter()
                        .cloned()
                        .chain(std::iter::once(name))
                        .collect::<Vec<_>>()
                        .join("::"),
                    module_path: module_path.clone(),
                    item: item.clone(),
                    def_id,
                });
            }
            _ => {}
        }
    }
    Ok(())
}

fn collect_occupied_item_names(item: &Item, names: &mut HashSet<String>) {
    if let Some(ident) = item.kind.ident() {
        names.insert(ident.name.as_str().to_owned());
    }
    match &item.kind {
        ItemKind::Use(tree) => collect_occupied_use_names(tree, None, names),
        ItemKind::ForeignMod(foreign_mod) => {
            for foreign_item in &foreign_mod.items {
                if let Some(ident) = foreign_item.kind.ident() {
                    names.insert(ident.name.as_str().to_owned());
                }
            }
        }
        _ => {}
    }
}

fn collect_occupied_use_names(
    tree: &rustc_ast::UseTree,
    parent: Option<Ident>,
    names: &mut HashSet<String>,
) {
    match &tree.kind {
        rustc_ast::UseTreeKind::Simple(rename) => {
            let imported = tree.prefix.segments.last().map(|segment| segment.ident);
            let ident = rename.or_else(|| {
                imported.and_then(|ident| {
                    if ident.name.as_str() == "self" {
                        parent
                    } else {
                        Some(ident)
                    }
                })
            });
            if let Some(ident) = ident {
                names.insert(ident.name.as_str().to_owned());
            }
        }
        rustc_ast::UseTreeKind::Nested { items, .. } => {
            let parent = tree
                .prefix
                .segments
                .last()
                .map(|segment| segment.ident)
                .or(parent);
            for (tree, _) in items {
                collect_occupied_use_names(tree, parent, names);
            }
        }
        rustc_ast::UseTreeKind::Glob => {}
    }
}

fn validate_current_target(
    current: &CurrentFunction,
    requested: &ReplacementItem,
) -> Result<(), ReplacementError> {
    let ItemKind::Fn(box function) = &current.item.kind else { unreachable!() };
    if function.ident.to_string() != requested.name {
        return Err(item_error(
            ReplacementErrorKind::TargetResolution,
            requested,
            format!(
                "current target at `{}` is named `{}` rather than `{}`",
                requested.path, function.ident, requested.name
            ),
        ));
    }
    if !matches!(function.sig.header.safety, Safety::Unsafe(_)) {
        return Err(item_error(
            ReplacementErrorKind::TargetResolution,
            requested,
            "current target is not unsafe; run target-safety normalization first".to_owned(),
        ));
    }
    if matches!(function.sig.header.constness, rustc_ast::Const::Yes(_)) {
        return Err(item_error(
            ReplacementErrorKind::TargetResolution,
            requested,
            "current const functions are unsupported replacement targets".to_owned(),
        ));
    }
    if function.sig.header.coroutine_kind.is_some() {
        return Err(item_error(
            ReplacementErrorKind::TargetResolution,
            requested,
            "current async functions are unsupported replacement targets".to_owned(),
        ));
    }
    if function.sig.decl.c_variadic() {
        return Err(item_error(
            ReplacementErrorKind::TargetResolution,
            requested,
            "current variadic functions are unsupported replacement targets".to_owned(),
        ));
    }
    if has_attr(&current.item.attrs, sym::no_mangle)
        && has_attr(&current.item.attrs, sym::export_name)
    {
        return Err(item_error(
            ReplacementErrorKind::TargetResolution,
            requested,
            "a current target carrying both `no_mangle` and `export_name` is unsupported"
                .to_owned(),
        ));
    }
    Ok(())
}

fn validate_transformed_header(
    current: &rustc_ast::Fn,
    transformed: &rustc_ast::Fn,
    requested: &ReplacementItem,
) -> Result<(), ReplacementError> {
    if current.sig.decl.inputs.len() != transformed.sig.decl.inputs.len() {
        return Err(item_error(
            ReplacementErrorKind::InvalidTransformation,
            requested,
            format!(
                "returned function has {} parameters but current target has {}",
                transformed.sig.decl.inputs.len(),
                current.sig.decl.inputs.len()
            ),
        ));
    }
    let allow_wildcards = is_supported_two_argument_main_0(current);
    for (index, (source, target)) in current
        .sig
        .decl
        .inputs
        .iter()
        .zip(&transformed.sig.decl.inputs)
        .enumerate()
    {
        let source_pattern =
            simple_parameter_pattern(source, allow_wildcards).ok_or_else(|| {
                item_error(
                    ReplacementErrorKind::TargetResolution,
                    requested,
                    format!("current parameter {index} is not a supported parameter pattern"),
                )
            })?;
        let target_pattern =
            simple_parameter_pattern(target, allow_wildcards).expect("returned header was checked");
        if source_pattern != target_pattern {
            return Err(item_error(
                ReplacementErrorKind::InvalidTransformation,
                requested,
                format!(
                    "returned parameter {index} uses pattern `{}` rather than `{}`",
                    target_pattern.description(),
                    source_pattern.description()
                ),
            ));
        }
    }
    Ok(())
}

#[derive(PartialEq, Eq)]
enum SimpleParameterPattern {
    Identifier(String),
    Wildcard,
}

impl SimpleParameterPattern {
    fn description(&self) -> &str {
        match self {
            Self::Identifier(name) => name,
            Self::Wildcard => "_",
        }
    }
}

fn simple_parameter_pattern(
    parameter: &rustc_ast::Param,
    allow_wildcard: bool,
) -> Option<SimpleParameterPattern> {
    match &parameter.pat.kind {
        PatKind::Ident(BindingMode(ByRef::No, _), ident, None) => {
            Some(SimpleParameterPattern::Identifier(ident.to_string()))
        }
        PatKind::Wild if allow_wildcard => Some(SimpleParameterPattern::Wildcard),
        _ => None,
    }
}

fn signature_types(function: &rustc_ast::Fn) -> Vec<String> {
    function
        .sig
        .decl
        .inputs
        .iter()
        .map(|parameter| canonical_type(&parameter.ty))
        .chain(std::iter::once(canonical_return(&function.sig.decl.output)))
        .collect()
}

fn allocate_generated_name(
    current: &CurrentFunction,
    occupied: &mut HashMap<Vec<String>, HashSet<String>>,
    prefix: &str,
) -> String {
    let ItemKind::Fn(box function) = &current.item.kind else { unreachable!() };
    let base = format!("{prefix}_{}", function.ident.name.as_str());
    let names = occupied.entry(current.module_path.clone()).or_default();
    for suffix in 0usize.. {
        let candidate = if suffix == 0 {
            base.clone()
        } else {
            format!("{base}_{}", suffix - 1)
        };
        if names.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!("generated name space is infinite")
}

fn compose_implementation(
    current: &P<Item>,
    transformed: &P<Item>,
    requested: &ReplacementItem,
) -> Result<P<Item>, ReplacementError> {
    let mut output = current.clone();
    let ItemKind::Fn(box output_fn) = &mut output.kind else { unreachable!() };
    let ItemKind::Fn(box transformed_fn) = &transformed.kind else { unreachable!() };
    output_fn.generics = transformed_fn.generics.clone();
    output_fn.sig.decl = transformed_fn.sig.decl.clone();
    output_fn.body = transformed_fn.body.clone();
    if output_fn.body.is_none() {
        return Err(item_error(
            ReplacementErrorKind::InvalidTransformation,
            requested,
            "returned function has no body".to_owned(),
        ));
    }
    Ok(output)
}

fn parse_body(source: &str) -> Result<P<rustc_ast::Block>, ReplacementError> {
    let item = catch_unwind(AssertUnwindSafe(|| {
        utils::ast::parse_item(format!("unsafe fn __proctor_body() {source}"))
    }))
    .map_err(|_| {
        global_error(
            ReplacementErrorKind::RewriteFailure,
            format!("failed to construct generated wrapper body `{source}`"),
        )
    })?;
    let ItemKind::Fn(box function) = item.kind else { unreachable!() };
    Ok(function.body.unwrap())
}

fn canonical_return(return_ty: &FnRetTy) -> String {
    match return_ty {
        FnRetTy::Default(_) => "<omitted>".to_owned(),
        FnRetTy::Ty(ty) => canonical_type(ty),
    }
}

fn canonical_type(ty: &Ty) -> String {
    let mut ty = ty.clone();
    TypeParenRemover.visit_ty(&mut ty);
    pprust::ty_to_string(&ty)
}

struct TypeParenRemover;

impl MutVisitor for TypeParenRemover {
    fn visit_ty(&mut self, ty: &mut Ty) {
        while let TyKind::Paren(inner) = &ty.kind {
            *ty = (**inner).clone();
        }
        mut_visit::walk_ty(self, ty);
    }
}

struct ProctorLabelRemover;

impl MutVisitor for ProctorLabelRemover {
    fn flat_map_stmt(&mut self, mut statement: Stmt) -> SmallVec<[Stmt; 1]> {
        if !matches!(statement.kind, StmtKind::Empty) {
            statement_attrs_mut(&mut statement)
                .retain(|attribute| !is_proctor_attribute(attribute));
        }
        mut_visit::walk_flat_map_stmt(self, statement)
    }

    fn visit_expr(&mut self, expression: &mut Expr) {
        expression
            .attrs
            .retain(|attribute| !is_proctor_attribute(attribute));
        mut_visit::walk_expr(self, expression);
    }
}

fn statement_attrs_mut(statement: &mut Stmt) -> &mut rustc_ast::AttrVec {
    match &mut statement.kind {
        StmtKind::Let(local) => &mut local.attrs,
        StmtKind::Item(item) => &mut item.attrs,
        StmtKind::Expr(expression) | StmtKind::Semi(expression) => &mut expression.attrs,
        StmtKind::MacCall(mac) => &mut mac.attrs,
        StmtKind::Empty => unreachable!(),
    }
}

fn is_proctor_attribute(attribute: &Attribute) -> bool {
    let AttrKind::Normal(normal) = &attribute.kind else {
        return false;
    };
    normal.item.path.segments.len() == 1
        && normal.item.path.segments[0].ident.name.as_str() == "proctor"
}

fn is_export_attribute(attribute: &Attribute) -> bool {
    attribute.has_name(sym::no_mangle) || attribute.has_name(sym::export_name)
}

fn has_attr(attributes: &[Attribute], name: Symbol) -> bool {
    attributes.iter().any(|attribute| attribute.has_name(name))
}

fn parsed_ident(name: &str) -> Ident {
    let item = utils::ast::parse_item(format!("fn {name}() {{}}"));
    let ItemKind::Fn(box function) = item.kind else { unreachable!() };
    function.ident
}

fn absolute_item_path(module_path: &[String], name: &str) -> String {
    std::iter::once("crate".to_owned())
        .chain(module_path.iter().cloned())
        .chain(std::iter::once(name.to_owned()))
        .collect::<Vec<_>>()
        .join("::")
}

struct SourceCopyCallCollector<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    source_paths: &'a FxHashMap<LocalDefId, String>,
    current_scc: &'a FxHashSet<LocalDefId>,
    current_function: Option<LocalDefId>,
    rewrites: FxHashMap<NodeId, String>,
}

impl<'ast> Visitor<'ast> for SourceCopyCallCollector<'_, '_> {
    fn visit_item(&mut self, item: &'ast Item) {
        let previous = self.current_function;
        if matches!(item.kind, ItemKind::Fn(..)) {
            self.current_function = self.ast_to_hir.global_map.get(&item.id).copied();
        }
        visit::walk_item(self, item);
        self.current_function = previous;
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if self
            .current_function
            .is_some_and(|caller| self.current_scc.contains(&caller))
            && let ExprKind::Call(callee, _) = &expression.kind
            && let Some(target) = resolved_local_function(callee, self.ast_to_hir, self.tcx)
            && let Some(path) = self.source_paths.get(&target)
        {
            self.rewrites.insert(callee.id, path.clone());
        }
        visit::walk_expr(self, expression);
    }
}

struct CallRewriter {
    rewrites: FxHashMap<NodeId, String>,
}

impl MutVisitor for CallRewriter {
    fn visit_expr(&mut self, expression: &mut Expr) {
        if let Some(path) = self.rewrites.get(&expression.id) {
            *expression = utils::expr!("{path}");
            return;
        }
        mut_visit::walk_expr(self, expression);
    }
}

fn resolved_local_function(
    callee: &Expr,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<LocalDefId> {
    let hir_callee = ast_to_hir.get_expr(callee.id, tcx)?;
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_callee.kind else {
        return None;
    };
    let Res::Def(DefKind::Fn, def_id) = path.res else {
        return None;
    };
    def_id.as_local()
}

struct CurrentSurfaceCallCounter<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    targets: &'a FxHashSet<LocalDefId>,
    callers: &'a FxHashSet<LocalDefId>,
    current_function: Option<LocalDefId>,
    ast_counts: &'a mut FxHashMap<(LocalDefId, LocalDefId), usize>,
}

impl<'ast> Visitor<'ast> for CurrentSurfaceCallCounter<'_, '_> {
    fn visit_item(&mut self, item: &'ast Item) {
        let previous = self.current_function;
        if matches!(item.kind, ItemKind::Fn(..)) {
            self.current_function = self.ast_to_hir.global_map.get(&item.id).copied();
        }
        visit::walk_item(self, item);
        self.current_function = previous;
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if let Some(caller) = self.current_function
            && self.callers.contains(&caller)
            && let ExprKind::Call(callee, _) = &expression.kind
            && let Some(target) = resolved_local_function(callee, self.ast_to_hir, self.tcx)
            && self.targets.contains(&target)
        {
            *self.ast_counts.entry((caller, target)).or_default() += 1;
        }
        visit::walk_expr(self, expression);
    }
}

struct HirDirectCallCounter<'a> {
    wrapped: &'a FxHashSet<LocalDefId>,
    include_expansions: bool,
    counts: FxHashMap<LocalDefId, usize>,
}

impl<'tcx> HirVisitor<'tcx> for HirDirectCallCounter<'_> {
    fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Call(callee, _) = expression.kind
            && (self.include_expansions || !callee.span.from_expansion())
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = callee.kind
            && let Res::Def(DefKind::Fn, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
            && self.wrapped.contains(&def_id)
        {
            *self.counts.entry(def_id).or_default() += 1;
        }
        intravisit::walk_expr(self, expression);
    }
}

fn fixed_main_item() -> Result<P<Item>, ReplacementError> {
    let source = r#"
pub fn main() {
    let mut command_line_arg_storage: Vec<Vec<i8>> = ::std::env::args()
        .map(|arg| {
            ::std::ffi::CString::new(arg)
                .expect("Failed to convert argument into CString.")
                .into_bytes_with_nul()
                .into_iter()
                .map(|byte| byte as i8)
                .collect()
        })
        .collect();

    let argc = command_line_arg_storage.len() as core::ffi::c_int;
    let mut command_line_arg_slices: Vec<&mut [i8]> = command_line_arg_storage
        .iter_mut()
        .map(|arg| arg.as_mut_slice())
        .collect();

    let mut argv_terminator: [i8; 0] = [];
    command_line_arg_slices.push(&mut argv_terminator);

    unsafe {
        ::std::process::exit(
            main_0(argc, command_line_arg_slices.as_mut_slice()) as i32,
        )
    }
}
"#;
    catch_unwind(AssertUnwindSafe(|| {
        P(utils::ast::parse_item(source.to_owned()))
    }))
    .map_err(|_| {
        global_error(
            ReplacementErrorKind::RewriteFailure,
            "failed to parse the fixed executable `main` implementation".to_owned(),
        )
    })
}

fn item_kind_name(item: &Item) -> &'static str {
    match item.kind {
        ItemKind::ExternCrate(..) => "extern crate",
        ItemKind::Use(..) => "use",
        ItemKind::Static(..) => "static",
        ItemKind::Const(..) => "const",
        ItemKind::Fn(..) => "function",
        ItemKind::Mod(..) => "module",
        ItemKind::ForeignMod(..) => "foreign",
        ItemKind::TyAlias(..) => "type alias",
        ItemKind::Enum(..) => "enum",
        ItemKind::Struct(..) => "struct",
        ItemKind::Union(..) => "union",
        ItemKind::Trait(..) => "trait",
        ItemKind::Impl(..) => "impl",
        ItemKind::MacCall(..) => "macro invocation",
        ItemKind::MacroDef(..) => "macro definition",
        _ => "other",
    }
}

fn global_error(kind: ReplacementErrorKind, message: String) -> ReplacementError {
    ReplacementError {
        kind,
        item: None,
        message,
    }
}

fn item_error(
    kind: ReplacementErrorKind,
    item: &ReplacementItem,
    message: String,
) -> ReplacementError {
    ReplacementError {
        kind,
        item: Some(Box::new(item.clone())),
        message,
    }
}

#[cfg(test)]
mod tests;
