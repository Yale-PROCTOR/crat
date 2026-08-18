use std::{
    collections::{HashMap, HashSet},
    panic::{AssertUnwindSafe, catch_unwind},
};

use rustc_ast::{
    AngleBracketedArg, AttrKind, Attribute, BindingMode, BlockCheckMode, ByRef, Crate, Expr,
    ExprKind, Extern, FnRetTy, GenericArg, GenericArgs, GenericParamKind, Item, ItemKind,
    LocalKind, Mutability, NodeId, Pat, PatKind, Safety, Stmt, StmtKind, Ty, TyKind,
    VisibilityKind,
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
    skeleton::{annotate_function, collect_opaque_nested_ifs, render_statement_group},
};

const REPLACEMENT_SCHEMA_VERSION: u64 = 1;

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
    UnsupportedConversion,
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

pub fn replace_items(
    source: &str,
    request: &ReplacementRequest,
    tcx: TyCtxt<'_>,
) -> Result<ReplacementOutput, ReplacementError> {
    replace_items_with_observations(source, request, tcx).map(|output| output.replacement)
}

pub fn replace_items_with_observations(
    source: &str,
    request: &ReplacementRequest,
    tcx: TyCtxt<'_>,
) -> Result<ExtendedReplacementOutput, ReplacementError> {
    validate_request(request)?;
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
    let mut surface = parse_crate(source, ReplacementErrorKind::RewriteFailure)?;
    let ast_to_hir = map_surface_to_hir(&mut surface, tcx)?;

    let mut current_functions = vec![];
    let mut occupied = HashMap::new();
    collect_current_functions(
        &surface.items,
        &ast_to_hir.global_map,
        &mut vec![],
        &mut current_functions,
        &mut occupied,
    )?;

    let mut plans = vec![];
    let mut reserved = occupied;
    for requested in &request.items {
        let matches = current_functions
            .iter()
            .filter(|function| function.path == requested.path)
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(item_error(
                ReplacementErrorKind::TargetResolution,
                requested,
                if matches.is_empty() {
                    format!(
                        "current source contains no free function at path `{}`",
                        requested.path
                    )
                } else {
                    format!(
                        "current source contains multiple free functions at path `{}`",
                        requested.path
                    )
                },
            ));
        }
        let current = matches[0];
        validate_current_target(current, requested)?;
        let transformation = transformations
            .get(&requested.name)
            .expect("request validation established the function set");
        let ItemKind::Fn(box current_fn) = &current.item.kind else { unreachable!() };
        let ItemKind::Fn(box transformed_fn) = &transformation.kind else { unreachable!() };
        validate_transformed_header(current_fn, transformed_fn, requested)?;

        let executable_arity = (current_fn.ident.name.as_str() == "main_0")
            .then_some(current_fn.sig.decl.inputs.len());
        let source_types = signature_types(current_fn);
        let target_types = signature_types(transformed_fn);
        let needs_wrapper = source_types != target_types && executable_arity != Some(2);

        let wrapper_name = if needs_wrapper {
            Some(allocate_wrapper_name(current, &mut reserved, requested))
        } else {
            None
        };
        let wrapper = wrapper_name
            .as_ref()
            .map(|name| build_wrapper(current, transformed_fn, requested, name))
            .transpose()?;
        let observation_implementation =
            compose_implementation(&current.item, transformation, needs_wrapper, requested)?;
        let mut implementation = observation_implementation.clone();
        let ItemKind::Fn(box implementation_fn) = &mut implementation.kind else { unreachable!() };
        ProctorLabelRemover.visit_block(
            implementation_fn
                .body
                .as_mut()
                .expect("composed implementations always have a body"),
        );

        let main_node = if executable_arity == Some(2) {
            Some(find_sibling_main(
                &current_functions,
                &current.module_path,
                requested,
            )?)
        } else {
            None
        };
        plans.push(ReplacementPlan {
            requested: requested.clone(),
            current_node: current.item.id,
            current_def_id: current.def_id,
            implementation,
            observation_implementation,
            wrapper,
            wrapper_path: wrapper_name.map(|name| {
                absolute_item_path(&current.module_path, &name)
                    .strip_prefix("crate::")
                    .unwrap_or(&name)
                    .to_owned()
            }),
            source_copy_name: String::new(),
            source_copy_path: String::new(),
            main_node,
        });
    }

    // Candidate wrapper allocation is deliberately complete before observation-only
    // source-copy names reserve anything in the module namespace.
    for plan in &mut plans {
        let current = current_functions
            .iter()
            .find(|function| function.item.id == plan.current_node)
            .expect("replacement plans originate in current functions");
        let name = allocate_generated_name(current, &mut reserved, "__proctor_source");
        plan.source_copy_path = absolute_item_path(&current.module_path, &name)
            .strip_prefix("crate::")
            .unwrap_or(&name)
            .to_owned();
        plan.source_copy_name = name;
    }

    validate_macro_call_rewrites(&surface, &ast_to_hir, &plans, &current_functions, tcx)?;
    let rewrites = collect_call_rewrites(&surface, &ast_to_hir, &plans, tcx)?;

    let mut observation_surface = surface.clone();
    validate_source_copy_macro_rewrites(
        &observation_surface,
        &ast_to_hir,
        &plans,
        &current_functions,
        tcx,
    )?;
    let source_copy_rewrites =
        collect_source_copy_call_rewrites(&observation_surface, &ast_to_hir, &plans, tcx);
    CallRewriter {
        rewrites: source_copy_rewrites,
    }
    .visit_crate(&mut observation_surface);
    apply_observation_replacements(&mut observation_surface.items, &plans)?;

    let mut call_rewriter = CallRewriter { rewrites };
    call_rewriter.visit_crate(&mut surface);
    apply_replacements(&mut surface.items, &plans)?;
    let new_correspondence: Vec<CallableCorrespondence> = plans
        .iter()
        .map(|plan| CallableCorrespondence {
            item_id: plan.requested.id,
            logical_path: plan.requested.path.clone(),
            implementation_path: plan.requested.path.clone(),
            wrapper_path: plan.wrapper_path.clone(),
        })
        .collect();
    let mut combined_correspondence = request.accepted_correspondence.clone();
    combined_correspondence.extend(new_correspondence.iter().cloned());
    validate_correspondence(&combined_correspondence)?;
    let current_items = plans
        .iter()
        .map(|plan| CurrentObservationItem {
            item_id: plan.requested.id,
            logical_path: plan.requested.path.clone(),
            source_copy_path: plan.source_copy_path.clone(),
            implementation_path: plan.requested.path.clone(),
            wrapper_path: plan.wrapper_path.clone(),
            transform_labels: plan.requested.view.transform_labels(),
        })
        .collect();
    Ok(ExtendedReplacementOutput {
        replacement: ReplacementOutput {
            source: pprust::crate_to_string_for_macros(&surface),
            statement_pairs,
        },
        observation_source: pprust::crate_to_string_for_macros(&observation_surface),
        accepted_correspondence: request.accepted_correspondence.clone(),
        new_correspondence,
        current_items,
    })
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
    current_node: NodeId,
    current_def_id: LocalDefId,
    implementation: P<Item>,
    observation_implementation: P<Item>,
    wrapper: Option<P<Item>>,
    wrapper_path: Option<String>,
    source_copy_name: String,
    source_copy_path: String,
    main_node: Option<NodeId>,
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
    if function.sig.decl.inputs.iter().any(|parameter| {
        !matches!(
            parameter.pat.kind,
            PatKind::Ident(BindingMode(ByRef::No, _), _, None)
        )
    }) {
        return Err(item_error(
            ReplacementErrorKind::InvalidTransformation,
            requested,
            "every returned parameter must use a simple by-value identifier pattern".to_owned(),
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
    for (index, (source, target)) in current
        .sig
        .decl
        .inputs
        .iter()
        .zip(&transformed.sig.decl.inputs)
        .enumerate()
    {
        let source_name = simple_parameter_name(source).ok_or_else(|| {
            item_error(
                ReplacementErrorKind::TargetResolution,
                requested,
                format!("current parameter {index} is not a simple identifier"),
            )
        })?;
        let target_name = simple_parameter_name(target).expect("returned header was checked");
        if source_name != target_name {
            return Err(item_error(
                ReplacementErrorKind::InvalidTransformation,
                requested,
                format!(
                    "returned parameter {index} is named `{target_name}` rather than `{source_name}`"
                ),
            ));
        }
    }
    Ok(())
}

fn simple_parameter_name(parameter: &rustc_ast::Param) -> Option<String> {
    let PatKind::Ident(BindingMode(ByRef::No, _), ident, None) = &parameter.pat.kind else {
        return None;
    };
    Some(ident.to_string())
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

fn allocate_wrapper_name(
    current: &CurrentFunction,
    occupied: &mut HashMap<Vec<String>, HashSet<String>>,
    requested: &ReplacementItem,
) -> String {
    let ItemKind::Fn(box function) = &current.item.kind else { unreachable!() };
    let base = format!("__proctor_wrapper_{}", function.ident.name.as_str());
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
    unreachable!("wrapper name space is infinite for {}", requested.path)
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

fn find_sibling_main(
    functions: &[CurrentFunction],
    module_path: &[String],
    requested: &ReplacementItem,
) -> Result<NodeId, ReplacementError> {
    let matches = functions
        .iter()
        .filter(|function| {
            function.module_path == module_path
                && matches!(
                    &function.item.kind,
                    ItemKind::Fn(function) if function.ident.name.as_str() == "main"
                )
        })
        .collect::<Vec<_>>();
    if matches.len() != 1 {
        return Err(item_error(
            ReplacementErrorKind::RewriteFailure,
            requested,
            format!(
                "two-argument `main_0` requires exactly one sibling `main`, found {}",
                matches.len()
            ),
        ));
    }
    Ok(matches[0].item.id)
}

fn compose_implementation(
    current: &P<Item>,
    transformed: &P<Item>,
    needs_wrapper: bool,
    requested: &ReplacementItem,
) -> Result<P<Item>, ReplacementError> {
    let mut output = current.clone();
    let ItemKind::Fn(box output_fn) = &mut output.kind else { unreachable!() };
    let ItemKind::Fn(box transformed_fn) = &transformed.kind else { unreachable!() };
    output_fn.generics = transformed_fn.generics.clone();
    output_fn.sig.decl = transformed_fn.sig.decl.clone();
    output_fn.body = transformed_fn.body.clone();
    if needs_wrapper {
        output_fn.sig.header.ext = Extern::None;
        output
            .attrs
            .retain(|attribute| !is_export_attribute(attribute));
    }
    if output_fn.body.is_none() {
        return Err(item_error(
            ReplacementErrorKind::InvalidTransformation,
            requested,
            "returned function has no body".to_owned(),
        ));
    }
    Ok(output)
}

fn build_wrapper(
    current: &CurrentFunction,
    transformed: &rustc_ast::Fn,
    requested: &ReplacementItem,
    wrapper_name: &str,
) -> Result<P<Item>, ReplacementError> {
    let mut wrapper = current.item.clone();
    let ItemKind::Fn(box wrapper_fn) = &mut wrapper.kind else { unreachable!() };
    let source_fn = wrapper_fn.clone();
    wrapper_fn.ident = parsed_ident(wrapper_name);
    wrapper_fn.sig.header.safety = Safety::Unsafe(wrapper_fn.sig.span);

    let arguments = source_fn
        .sig
        .decl
        .inputs
        .iter()
        .zip(&transformed.sig.decl.inputs)
        .map(|(source, target)| {
            let name = simple_parameter_name(source).expect("current target header was checked");
            input_conversion(&name, &source.ty, &target.ty, requested)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let call = format!(
        "{}({})",
        absolute_item_path(&current.module_path, &requested.name),
        arguments.join(", ")
    );
    let body_source = match (&source_fn.sig.decl.output, &transformed.sig.decl.output) {
        (FnRetTy::Default(_), FnRetTy::Default(_)) => format!("{{ {call}; }}"),
        (source_return, target_return) => {
            let result_name = fresh_result_name(&source_fn);
            let conversion =
                output_conversion(&result_name, source_return, target_return, requested)?;
            format!("{{ let {result_name} = {call}; {conversion} }}")
        }
    };
    wrapper_fn.body = Some(parse_body(&body_source)?);

    let no_mangle = has_attr(&wrapper.attrs, sym::no_mangle);
    let explicit_export = wrapper
        .attrs
        .iter()
        .find(|attribute| attribute.has_name(sym::export_name))
        .cloned();
    wrapper.attrs.clear();
    if no_mangle {
        wrapper.attrs.extend(utils::attr!(
            "#[export_name = \"{}\"]",
            source_fn.ident.name.as_str()
        ));
    } else if let Some(attribute) = explicit_export {
        wrapper.attrs.push(attribute);
    }
    Ok(wrapper)
}

fn fresh_result_name(function: &rustc_ast::Fn) -> String {
    let occupied = function
        .sig
        .decl
        .inputs
        .iter()
        .filter_map(simple_parameter_name)
        .collect::<HashSet<_>>();
    for index in 0usize.. {
        let name = if index == 0 {
            "__proctor_result".to_owned()
        } else {
            format!("__proctor_result_{}", index - 1)
        };
        if !occupied.contains(&name) {
            return name;
        }
    }
    unreachable!()
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

#[derive(Clone)]
enum ConvertedType {
    Raw {
        mutable: bool,
        inner: String,
        exact: String,
    },
    Ref {
        mutable: bool,
        inner: String,
    },
    Slice {
        mutable: bool,
        inner: String,
    },
    Box {
        inner: String,
    },
    OptionalRef {
        mutable: bool,
        inner: String,
    },
    OptionalBox {
        inner: String,
    },
    BoxedSlice,
    OptionalBoxedSlice,
    Other(String),
}

fn converted_type(ty: &Ty) -> ConvertedType {
    let ty = without_parens(ty);
    match &ty.kind {
        TyKind::Ptr(mut_ty) => ConvertedType::Raw {
            mutable: mut_ty.mutbl == Mutability::Mut,
            inner: canonical_type(&mut_ty.ty),
            exact: canonical_type(ty),
        },
        TyKind::Ref(_, mut_ty) => {
            if let TyKind::Slice(inner) = &without_parens(&mut_ty.ty).kind {
                ConvertedType::Slice {
                    mutable: mut_ty.mutbl == Mutability::Mut,
                    inner: canonical_type(inner),
                }
            } else {
                ConvertedType::Ref {
                    mutable: mut_ty.mutbl == Mutability::Mut,
                    inner: canonical_type(&mut_ty.ty),
                }
            }
        }
        TyKind::Path(_, path) => {
            let Some(segment) = path.segments.last() else {
                return ConvertedType::Other(canonical_type(ty));
            };
            let Some(inner) = single_type_argument(segment.args.as_deref()) else {
                return ConvertedType::Other(canonical_type(ty));
            };
            match segment.ident.name.as_str() {
                "Box" => match &without_parens(inner).kind {
                    TyKind::Slice(_) => ConvertedType::BoxedSlice,
                    _ => ConvertedType::Box {
                        inner: canonical_type(inner),
                    },
                },
                "Option" => match converted_type(inner) {
                    ConvertedType::Ref { mutable, inner } => {
                        ConvertedType::OptionalRef { mutable, inner }
                    }
                    ConvertedType::Box { inner } => ConvertedType::OptionalBox { inner },
                    ConvertedType::BoxedSlice => ConvertedType::OptionalBoxedSlice,
                    _ => ConvertedType::Other(canonical_type(ty)),
                },
                _ => ConvertedType::Other(canonical_type(ty)),
            }
        }
        _ => ConvertedType::Other(canonical_type(ty)),
    }
}

fn single_type_argument(args: Option<&GenericArgs>) -> Option<&Ty> {
    let GenericArgs::AngleBracketed(args) = args? else {
        return None;
    };
    let [AngleBracketedArg::Arg(GenericArg::Type(ty))] = &args.args[..] else {
        return None;
    };
    Some(ty)
}

fn input_conversion(
    name: &str,
    source: &Ty,
    target: &Ty,
    requested: &ReplacementItem,
) -> Result<String, ReplacementError> {
    let source_kind = converted_type(source);
    let target_kind = converted_type(target);
    let ConvertedType::Raw { .. } = source_kind else {
        if canonical_type(source) == canonical_type(target) {
            return Ok(name.to_owned());
        }
        return Err(unsupported_conversion(requested, source, target, "input"));
    };
    let output = match target_kind {
        ConvertedType::Ref {
            mutable: false,
            inner,
        } => format!("&*({name} as *const {inner})"),
        ConvertedType::Ref {
            mutable: true,
            inner,
        } => format!("&mut *({name} as *mut {inner})"),
        ConvertedType::OptionalRef {
            mutable: false,
            inner,
        } => format!("({name} as *const {inner}).as_ref()"),
        ConvertedType::OptionalRef {
            mutable: true,
            inner,
        } => format!("({name} as *mut {inner}).as_mut()"),
        ConvertedType::Slice {
            mutable: false,
            inner,
        } => format!(
            "if {name}.is_null() {{ &[] }} else {{ std::slice::from_raw_parts({name} as *const {inner}, 1_000_000) }}"
        ),
        ConvertedType::Slice {
            mutable: true,
            inner,
        } => format!(
            "if {name}.is_null() {{ &mut [] }} else {{ std::slice::from_raw_parts_mut({name} as *mut {inner}, 1_000_000) }}"
        ),
        ConvertedType::Box { inner } => format!("Box::from_raw({name} as *mut {inner})"),
        ConvertedType::OptionalBox { inner } => format!(
            "if {name}.is_null() {{ None }} else {{ Some(Box::from_raw({name} as *mut {inner})) }}"
        ),
        ConvertedType::Raw { exact, .. } => {
            if canonical_type(source) == exact {
                name.to_owned()
            } else {
                format!("{name} as {exact}")
            }
        }
        ConvertedType::BoxedSlice | ConvertedType::OptionalBoxedSlice => {
            return Err(item_error(
                ReplacementErrorKind::UnsupportedConversion,
                requested,
                format!(
                    "boxed-slice input conversion from `{}` to `{}` is unsupported",
                    canonical_type(source),
                    canonical_type(target)
                ),
            ));
        }
        ConvertedType::Other(target) if canonical_type(source) == target => name.to_owned(),
        _ => {
            return Err(unsupported_conversion(requested, source, target, "input"));
        }
    };
    Ok(output)
}

fn output_conversion(
    value: &str,
    source: &FnRetTy,
    target: &FnRetTy,
    requested: &ReplacementItem,
) -> Result<String, ReplacementError> {
    let (FnRetTy::Ty(source), FnRetTy::Ty(target)) = (source, target) else {
        return Err(item_error(
            ReplacementErrorKind::UnsupportedConversion,
            requested,
            "unit and non-unit return types cannot be converted".to_owned(),
        ));
    };
    let source_kind = converted_type(source);
    let target_kind = converted_type(target);
    let ConvertedType::Raw {
        mutable: source_mutable,
        inner: source_inner,
        exact: source_exact,
    } = source_kind
    else {
        if canonical_type(source) == canonical_type(target) {
            return Ok(value.to_owned());
        }
        return Err(unsupported_conversion(requested, target, source, "output"));
    };
    let null = typed_null(source_mutable, &source_inner, &source_exact);
    let output = match target_kind {
        ConvertedType::Ref { mutable, inner } => {
            reference_to_raw(value, mutable, &inner, &source_exact)
        }
        ConvertedType::OptionalRef { mutable, inner } => format!(
            "match {value} {{ None => {null}, Some({value}) => {} }}",
            reference_to_raw(value, mutable, &inner, &source_exact)
        ),
        ConvertedType::Slice { mutable, .. } => {
            let pointer = if mutable {
                format!("{value}.as_mut_ptr() as {source_exact}")
            } else {
                format!("{value}.as_ptr() as {source_exact}")
            };
            format!("if {value}.is_empty() {{ {null} }} else {{ {pointer} }}")
        }
        ConvertedType::Box { .. } => {
            format!("Box::into_raw({value}) as {source_exact}")
        }
        ConvertedType::OptionalBox { .. } => format!(
            "match {value} {{ None => {null}, Some({value}) => Box::into_raw({value}) as {source_exact} }}"
        ),
        ConvertedType::BoxedSlice => format!(
            "if {value}.is_empty() {{ drop({value}); {null} }} else {{ Box::leak({value}).as_mut_ptr() as {source_exact} }}"
        ),
        ConvertedType::OptionalBoxedSlice => format!(
            "match {value} {{ None => {null}, Some({value}) if {value}.is_empty() => {{ drop({value}); {null} }}, Some({value}) => Box::leak({value}).as_mut_ptr() as {source_exact} }}"
        ),
        ConvertedType::Raw { exact, .. } => {
            if exact == source_exact {
                value.to_owned()
            } else {
                format!("{value} as {source_exact}")
            }
        }
        ConvertedType::Other(target) if target == canonical_type(source) => value.to_owned(),
        _ => {
            return Err(unsupported_conversion(requested, target, source, "output"));
        }
    };
    Ok(output)
}

fn reference_to_raw(value: &str, mutable: bool, inner: &str, source_exact: &str) -> String {
    format!(
        "{value} as *{} {inner} as {source_exact}",
        if mutable { "mut" } else { "const" }
    )
}

fn typed_null(mutable: bool, inner: &str, exact: &str) -> String {
    format!(
        "std::ptr::{}::<{inner}>() as {exact}",
        if mutable { "null_mut" } else { "null" }
    )
}

fn unsupported_conversion(
    requested: &ReplacementItem,
    source: &Ty,
    target: &Ty,
    direction: &str,
) -> ReplacementError {
    item_error(
        ReplacementErrorKind::UnsupportedConversion,
        requested,
        format!(
            "unsupported {direction} conversion from `{}` to `{}`",
            canonical_type(source),
            canonical_type(target)
        ),
    )
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

fn without_parens(mut ty: &Ty) -> &Ty {
    while let TyKind::Paren(inner) = &ty.kind {
        ty = inner;
    }
    ty
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

fn collect_call_rewrites(
    surface: &Crate,
    ast_to_hir: &utils::ir::AstToHir,
    plans: &[ReplacementPlan],
    tcx: TyCtxt<'_>,
) -> Result<FxHashMap<NodeId, String>, ReplacementError> {
    let targets = plans
        .iter()
        .filter_map(|plan| {
            plan.wrapper_path
                .as_ref()
                .map(|path| (plan.current_def_id, format!("crate::{path}")))
        })
        .collect::<FxHashMap<_, _>>();
    let current_scc = plans
        .iter()
        .map(|plan| plan.current_def_id)
        .collect::<FxHashSet<_>>();
    let mut collector = AstCallCollector {
        ast_to_hir,
        tcx,
        targets: &targets,
        current_scc: &current_scc,
        current_function: None,
        rewrites: FxHashMap::default(),
    };
    collector.visit_crate(surface);
    Ok(collector.rewrites)
}

fn collect_source_copy_call_rewrites(
    surface: &Crate,
    ast_to_hir: &utils::ir::AstToHir,
    plans: &[ReplacementPlan],
    tcx: TyCtxt<'_>,
) -> FxHashMap<NodeId, String> {
    let source_paths = plans
        .iter()
        .map(|plan| {
            (
                plan.current_def_id,
                format!("crate::{}", plan.source_copy_path),
            )
        })
        .collect::<FxHashMap<_, _>>();
    let current_scc = source_paths.keys().copied().collect::<FxHashSet<_>>();
    let mut collector = SourceCopyCallCollector {
        ast_to_hir,
        tcx,
        source_paths: &source_paths,
        current_scc: &current_scc,
        current_function: None,
        rewrites: FxHashMap::default(),
    };
    collector.visit_crate(surface);
    collector.rewrites
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

struct AstCallCollector<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    targets: &'a FxHashMap<LocalDefId, String>,
    current_scc: &'a FxHashSet<LocalDefId>,
    current_function: Option<LocalDefId>,
    rewrites: FxHashMap<NodeId, String>,
}

impl<'ast> Visitor<'ast> for AstCallCollector<'_, '_> {
    fn visit_item(&mut self, item: &'ast Item) {
        let previous = self.current_function;
        if matches!(item.kind, ItemKind::Fn(..)) {
            self.current_function = self.ast_to_hir.global_map.get(&item.id).copied();
        }
        visit::walk_item(self, item);
        self.current_function = previous;
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if let ExprKind::Call(callee, _) = &expression.kind
            && self
                .current_function
                .is_none_or(|caller| !self.current_scc.contains(&caller))
            && let Some(target) = resolved_local_function(callee, self.ast_to_hir, self.tcx)
            && let Some(path) = self.targets.get(&target)
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

fn validate_macro_call_rewrites(
    surface: &Crate,
    ast_to_hir: &utils::ir::AstToHir,
    plans: &[ReplacementPlan],
    functions: &[CurrentFunction],
    tcx: TyCtxt<'_>,
) -> Result<(), ReplacementError> {
    let wrapped = plans
        .iter()
        .filter(|plan| plan.wrapper_path.is_some())
        .map(|plan| plan.current_def_id)
        .collect::<FxHashSet<_>>();
    if wrapped.is_empty() {
        return Ok(());
    }
    let scc = plans
        .iter()
        .map(|plan| plan.current_def_id)
        .collect::<FxHashSet<_>>();

    let mut ast_counts = FxHashMap::default();
    let mut scanner = SurfaceCallCounter {
        ast_to_hir,
        tcx,
        wrapped: &wrapped,
        scc: &scc,
        current_function: None,
        ast_counts: &mut ast_counts,
    };
    scanner.visit_crate(surface);

    for function in functions {
        if scc.contains(&function.def_id) {
            continue;
        }
        let hir::ItemKind::Fn { body, .. } =
            tcx.hir_node_by_def_id(function.def_id).expect_item().kind
        else {
            continue;
        };
        let mut counter = HirDirectCallCounter {
            wrapped: &wrapped,
            include_expansions: false,
            counts: FxHashMap::default(),
        };
        counter.visit_body(tcx.hir_body(body));
        for plan in plans.iter().filter(|plan| plan.wrapper_path.is_some()) {
            let hir_count = counter
                .counts
                .get(&plan.current_def_id)
                .copied()
                .unwrap_or(0);
            let surface_count = ast_counts
                .get(&(function.def_id, plan.current_def_id))
                .copied()
                .unwrap_or(0);
            if hir_count > surface_count {
                return Err(item_error(
                    ReplacementErrorKind::UnsupportedCallRewrite,
                    &plan.requested,
                    format!(
                        "a required call redirect in `{}` occurs inside a macro token input",
                        function.path
                    ),
                ));
            }
        }
    }
    Ok(())
}

fn validate_source_copy_macro_rewrites(
    surface: &Crate,
    ast_to_hir: &utils::ir::AstToHir,
    plans: &[ReplacementPlan],
    functions: &[CurrentFunction],
    tcx: TyCtxt<'_>,
) -> Result<(), ReplacementError> {
    let targets = plans
        .iter()
        .map(|plan| plan.current_def_id)
        .collect::<FxHashSet<_>>();
    let mut ast_counts = FxHashMap::default();
    let mut scanner = CurrentSurfaceCallCounter {
        ast_to_hir,
        tcx,
        targets: &targets,
        current_function: None,
        ast_counts: &mut ast_counts,
    };
    scanner.visit_crate(surface);
    for function in functions
        .iter()
        .filter(|function| targets.contains(&function.def_id))
    {
        let hir::ItemKind::Fn { body, .. } =
            tcx.hir_node_by_def_id(function.def_id).expect_item().kind
        else {
            continue;
        };
        let mut counter = HirDirectCallCounter {
            wrapped: &targets,
            include_expansions: true,
            counts: FxHashMap::default(),
        };
        counter.visit_body(tcx.hir_body(body));
        for plan in plans {
            let hir_count = counter
                .counts
                .get(&plan.current_def_id)
                .copied()
                .unwrap_or(0);
            let ast_count = ast_counts
                .get(&(function.def_id, plan.current_def_id))
                .copied()
                .unwrap_or(0);
            if hir_count > ast_count {
                return Err(item_error(
                    ReplacementErrorKind::UnsupportedCallRewrite,
                    &plan.requested,
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

struct CurrentSurfaceCallCounter<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    targets: &'a FxHashSet<LocalDefId>,
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
            && self.targets.contains(&caller)
            && let ExprKind::Call(callee, _) = &expression.kind
            && let Some(target) = resolved_local_function(callee, self.ast_to_hir, self.tcx)
            && self.targets.contains(&target)
        {
            *self.ast_counts.entry((caller, target)).or_default() += 1;
        }
        visit::walk_expr(self, expression);
    }
}

struct SurfaceCallCounter<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    wrapped: &'a FxHashSet<LocalDefId>,
    scc: &'a FxHashSet<LocalDefId>,
    current_function: Option<LocalDefId>,
    ast_counts: &'a mut FxHashMap<(LocalDefId, LocalDefId), usize>,
}

impl<'ast> Visitor<'ast> for SurfaceCallCounter<'_, '_> {
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
            && !self.scc.contains(&caller)
            && let ExprKind::Call(callee, _) = &expression.kind
            && let Some(target) = resolved_local_function(callee, self.ast_to_hir, self.tcx)
            && self.wrapped.contains(&target)
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

fn apply_replacements(
    items: &mut ThinVec<P<Item>>,
    plans: &[ReplacementPlan],
) -> Result<(), ReplacementError> {
    let by_node = plans
        .iter()
        .map(|plan| (plan.current_node, plan))
        .collect::<FxHashMap<_, _>>();
    let mains = plans
        .iter()
        .filter_map(|plan| plan.main_node.map(|node| (node, &plan.requested)))
        .collect::<FxHashMap<_, _>>();
    rewrite_item_list(items, &by_node, &mains)
}

fn apply_observation_replacements(
    items: &mut ThinVec<P<Item>>,
    plans: &[ReplacementPlan],
) -> Result<(), ReplacementError> {
    let by_node = plans
        .iter()
        .map(|plan| (plan.current_node, plan))
        .collect::<FxHashMap<_, _>>();
    let mains = plans
        .iter()
        .filter_map(|plan| plan.main_node.map(|node| (node, &plan.requested)))
        .collect::<FxHashMap<_, _>>();
    rewrite_observation_item_list(items, &by_node, &mains)
}

fn rewrite_observation_item_list(
    items: &mut ThinVec<P<Item>>,
    plans: &FxHashMap<NodeId, &ReplacementPlan>,
    mains: &FxHashMap<NodeId, &ReplacementItem>,
) -> Result<(), ReplacementError> {
    let mut output = ThinVec::with_capacity(items.len() + plans.len() * 2);
    for mut item in std::mem::take(items) {
        if let ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(children, ..)) = &mut item.kind {
            rewrite_observation_item_list(children, plans, mains)?;
        }
        if let Some(requested) = mains.get(&item.id) {
            item = fixed_main_item().map_err(|mut error| {
                error.item = Some(Box::new((*requested).clone()));
                error
            })?;
            item.attrs.clear();
        }
        if let Some(plan) = plans.get(&item.id) {
            let mut implementation = plan.observation_implementation.clone();
            implementation.attrs.clear();
            output.push(implementation);
            if let Some(wrapper) = &plan.wrapper {
                let mut wrapper = wrapper.clone();
                wrapper.attrs.clear();
                output.push(wrapper);
            }
            let mut source_copy = item;
            source_copy.attrs.clear();
            source_copy.vis.kind = VisibilityKind::Inherited;
            let opaque =
                collect_opaque_nested_ifs(&source_copy, &plan.requested.path).map_err(|error| {
                    item_error(
                        ReplacementErrorKind::RewriteFailure,
                        &plan.requested,
                        error.message,
                    )
                })?;
            let ItemKind::Fn(box function) = &mut source_copy.kind else { unreachable!() };
            function.ident = parsed_ident(&plan.source_copy_name);
            function.sig.header.ext = Extern::None;
            ProctorLabelRemover.visit_block(function.body.as_mut().unwrap());
            annotate_function(&mut source_copy, &opaque);
            output.push(source_copy);
        } else {
            output.push(item);
        }
    }
    *items = output;
    Ok(())
}

fn rewrite_item_list(
    items: &mut ThinVec<P<Item>>,
    plans: &FxHashMap<NodeId, &ReplacementPlan>,
    mains: &FxHashMap<NodeId, &ReplacementItem>,
) -> Result<(), ReplacementError> {
    let mut output = ThinVec::with_capacity(items.len() + plans.len());
    for mut item in std::mem::take(items) {
        if let ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(children, ..)) = &mut item.kind {
            rewrite_item_list(children, plans, mains)?;
        }
        if let Some(requested) = mains.get(&item.id) {
            item = fixed_main_item().map_err(|mut error| {
                error.item = Some(Box::new((*requested).clone()));
                error
            })?;
        }
        if let Some(plan) = plans.get(&item.id) {
            output.push(plan.implementation.clone());
            if let Some(wrapper) = &plan.wrapper {
                output.push(wrapper.clone());
            }
        } else {
            output.push(item);
        }
    }
    *items = output;
    Ok(())
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
