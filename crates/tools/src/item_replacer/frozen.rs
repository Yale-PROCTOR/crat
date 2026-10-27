use super::*;

mod unstructured;
pub use unstructured::*;

#[cfg(test)]
mod tests;

/// Compiler-resolved input shared by independent SCC jobs. No worker recompiles
/// the analysis crate or recomputes pointer decisions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FrozenProject {
    pub analysis_source: String,
    pub target_source: String,
    pub functions: Vec<FrozenFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FrozenFunction {
    pub record: crate::FunctionRecord,
    pub original_item: String,
    pub source_copy: String,
    pub source_copy_path: String,
    pub source_stub: String,
    pub source_stub_path: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AcceptedScc {
    pub members: Vec<u64>,
    pub source: String,
}

pub fn frozen_project_from_json(input: &str) -> Result<FrozenProject, ReplacementError> {
    let frozen: FrozenProject = serde_json::from_str(input).map_err(|error| {
        global_error(
            ReplacementErrorKind::InvalidRequest,
            format!("invalid frozen project JSON: {error}"),
        )
    })?;
    with_parse_session(|| {
        validate_frozen_project(&frozen)?;
        Ok(frozen)
    })
}

fn frozen_function(item: &Item) -> Result<&rustc_ast::Fn, ReplacementError> {
    if let ItemKind::Fn(function) = &item.kind
        && function.body.is_some()
    {
        return Ok(function);
    }
    Err(global_error(
        ReplacementErrorKind::InvalidRequest,
        "frozen function item must be a free function with a body".to_owned(),
    ))
}

fn frozen_function_items(
    items: &[P<Item>],
    module: &mut Vec<String>,
    functions: &mut HashMap<String, P<Item>>,
) -> Result<(), ReplacementError> {
    for item in items {
        match &item.kind {
            ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(children, ..)) => {
                module.push(ident.to_string());
                frozen_function_items(children, module, functions)?;
                module.pop();
            }
            ItemKind::Fn(function) => {
                frozen_function(item)?;
                let path = module
                    .iter()
                    .cloned()
                    .chain(std::iter::once(function.ident.to_string()))
                    .collect::<Vec<_>>()
                    .join("::");
                if functions.insert(path, item.clone()).is_some() {
                    return Err(global_error(
                        ReplacementErrorKind::InvalidRequest,
                        "duplicate frozen source function path".to_owned(),
                    ));
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn validate_frozen_project(frozen: &FrozenProject) -> Result<(), ReplacementError> {
    let analysis = parse_crate(
        &frozen.analysis_source,
        ReplacementErrorKind::InvalidRequest,
    )?;
    let target = parse_crate(&frozen.target_source, ReplacementErrorKind::InvalidRequest)?;
    require_same_context(&analysis, &target)?;
    let mut originals = HashMap::new();
    let mut targets = HashMap::new();
    frozen_function_items(&analysis.items, &mut vec![], &mut originals)?;
    frozen_function_items(&target.items, &mut vec![], &mut targets)?;
    let expected = originals
        .iter()
        .filter_map(|(path, item)| {
            let ItemKind::Fn(function) = &item.kind else { unreachable!() };
            (function.ident.name != sym::main).then_some(path.clone())
        })
        .collect::<HashSet<_>>();
    let mut ids = HashSet::new();
    let mut paths = HashSet::new();
    for function in &frozen.functions {
        if !ids.insert(function.record.id) || !paths.insert(function.record.path.clone()) {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                "duplicate frozen function identity".to_owned(),
            ));
        }
    }
    if paths != expected || targets.keys().cloned().collect::<HashSet<_>>() != expected {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            "frozen interface does not cover exactly the analysis and target functions".to_owned(),
        ));
    }
    let mut helpers = originals.keys().cloned().collect::<HashSet<_>>();
    for function in &frozen.functions {
        let record = &function.record;
        let original = one_item(&function.original_item)?;
        let original_fn = frozen_function(&original)?;
        if record.kind != crate::ItemKindName::Fn
            || record.name != original_fn.ident.to_string()
            || pprust::item_to_string(&original) != pprust::item_to_string(&originals[&record.path])
            || !matches!(original_fn.sig.header.safety, Safety::Unsafe(_))
        {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                format!(
                    "frozen original item disagrees with analysis function `{}`",
                    record.path
                ),
            ));
        }
        for view in [&record.baseline, &record.applied] {
            let skeleton = one_item(&view.skeleton)?;
            let skeleton_fn = frozen_function(&skeleton)?;
            let requested = ReplacementItem {
                id: record.id,
                path: record.path.clone(),
                name: record.name.clone(),
                view: view.clone(),
            };
            if skeleton_fn.ident.to_string() != record.name {
                return Err(global_error(
                    ReplacementErrorKind::InvalidRequest,
                    "frozen skeleton function name differs from its record".to_owned(),
                ));
            }
            validate_supported_transformation(&skeleton, &requested)?;
            validate_transformed_header(original_fn, skeleton_fn, &requested)?;
            let mut stub = compose_implementation(&original, &skeleton, &requested)?;
            let ItemKind::Fn(body) = &mut stub.kind else { unreachable!() };
            body.body = Some(parse_body("{ todo!() }")?);
            if pprust::item_to_string(&stub) != pprust::item_to_string(&targets[&record.path]) {
                return Err(global_error(
                    ReplacementErrorKind::InvalidRequest,
                    format!(
                        "frozen target header differs from the selected signatures for `{}`",
                        record.path
                    ),
                ));
            }
        }
        for (path, source, copy) in [
            (&function.source_copy_path, &function.source_copy, true),
            (&function.source_stub_path, &function.source_stub, false),
        ] {
            let segments = valid_full_path(path).ok_or_else(|| {
                global_error(
                    ReplacementErrorKind::InvalidRequest,
                    "invalid frozen helper path".to_owned(),
                )
            })?;
            let original_path = path_segments(&record.path);
            if segments[..segments.len() - 1] != original_path[..original_path.len() - 1]
                || !helpers.insert(path.clone())
            {
                return Err(global_error(
                    ReplacementErrorKind::InvalidRequest,
                    "frozen helper path has a different module or collides with another function"
                        .to_owned(),
                ));
            }
            let mut actual = one_item(source)?;
            let helper_fn = frozen_function(&actual)?;
            if helper_fn.ident.to_string() != *segments.last().unwrap() {
                return Err(global_error(
                    ReplacementErrorKind::InvalidRequest,
                    "frozen helper name differs from its path".to_owned(),
                ));
            }
            let mut expected = original.clone();
            if copy {
                expected.attrs.clear();
            } else {
                expected
                    .attrs
                    .retain(|attribute| !is_export_attribute(attribute));
            }
            expected.vis = crate_visible();
            let ItemKind::Fn(body) = &mut expected.kind else { unreachable!() };
            body.ident = helper_fn.ident;
            body.body = Some(parse_body("{ todo!() }")?);
            if copy {
                let ItemKind::Fn(body) = &mut actual.kind else { unreachable!() };
                body.body = Some(parse_body("{ todo!() }")?);
            }
            if pprust::item_to_string(&actual) != pprust::item_to_string(&expected) {
                return Err(global_error(
                    ReplacementErrorKind::InvalidRequest,
                    "frozen helper header or stub body differs from its original signature"
                        .to_owned(),
                ));
            }
        }
    }
    Ok(())
}

pub fn check_frozen_project_sources(
    frozen: &FrozenProject,
    analysis: &str,
    current: Option<&str>,
    require_template: bool,
) -> Result<(), ReplacementError> {
    with_parse_session(|| {
        validate_frozen_project(frozen)?;
        if normalize_target_safety(analysis)? != frozen.analysis_source {
            return Err(global_error(
                ReplacementErrorKind::TargetResolution,
                "analysis source differs from frozen project".to_owned(),
            ));
        }
        if let Some(current) = current {
            let template =
                parse_crate(&frozen.target_source, ReplacementErrorKind::RewriteFailure)?;
            let current = parse_crate(current, ReplacementErrorKind::RewriteFailure)?;
            require_same_context(&template, &current)?;
            if require_template
                && pprust::crate_to_string_for_macros(&current) != frozen.target_source
            {
                return Err(global_error(
                    ReplacementErrorKind::TargetResolution,
                    "independent SCC target differs from frozen template".to_owned(),
                ));
            }
        }
        Ok(())
    })
}

pub fn freeze_project(
    source: &str,
    records: &[crate::ItemRecord],
    tcx: TyCtxt<'_>,
) -> Result<FrozenProject, ReplacementError> {
    let mut analysis = parse_crate(source, ReplacementErrorKind::RewriteFailure)?;
    let ast_to_hir = map_surface_to_hir(&mut analysis, tcx)?;
    SafetyNormalizer.visit_crate(&mut analysis);
    let mut functions = vec![];
    let mut occupied = HashMap::new();
    collect_current_functions(
        &analysis.items,
        &ast_to_hir.global_map,
        &mut vec![],
        &mut functions,
        &mut occupied,
    )?;
    let mut target = analysis.clone();
    replace_pending_functions(&mut target.items);
    let mut frozen = vec![];
    let mut source_paths = FxHashMap::default();
    let mut originals = vec![];
    for record in records {
        let crate::ItemRecord::Function(record) = record else { continue };
        let current = functions
            .iter()
            .find(|function| function.path == record.path)
            .ok_or_else(|| {
                global_error(
                    ReplacementErrorKind::TargetResolution,
                    format!("frozen function `{}` is absent", record.path),
                )
            })?;
        let requested = ReplacementItem {
            id: record.id,
            path: record.path.clone(),
            name: record.name.clone(),
            view: record.baseline.clone(),
        };
        validate_current_target(current, &requested)?;
        let skeleton = parse_replacement_skeleton(&requested)?;
        let mut stub = compose_implementation(&current.item, &skeleton, &requested)?;
        let ItemKind::Fn(box body) = &mut stub.kind else { unreachable!() };
        body.body = Some(parse_body("{ todo!() }")?);
        let path = path_segments(&record.path);
        replace_function_at_path(&mut target.items, &path, stub)?;

        let source_name = allocate_generated_name(current, &mut occupied, "__proctor_source");
        let stub_name = allocate_generated_name(current, &mut occupied, "__proctor_source_stub");
        let source_copy_path = absolute_item_path(&current.module_path, &source_name)
            .trim_start_matches("crate::")
            .to_owned();
        let source_stub_path = absolute_item_path(&current.module_path, &stub_name)
            .trim_start_matches("crate::")
            .to_owned();
        source_paths.insert(current.def_id, format!("crate::{source_stub_path}"));
        let opaque = collect_opaque_expressions(&current.item, &current.path, &ast_to_hir, tcx)
            .map_err(|error| global_error(ReplacementErrorKind::RewriteFailure, error.message))?;
        let mut copy = current.item.clone();
        copy.attrs.clear();
        copy.vis = crate_visible();
        annotate_function(&mut copy, &opaque);
        let mut source_stub = current.item.clone();
        source_stub.attrs.retain(|attr| !is_export_attribute(attr));
        source_stub.vis = crate_visible();
        let ItemKind::Fn(box body) = &mut source_stub.kind else { unreachable!() };
        body.ident = parsed_ident(&stub_name);
        body.body = Some(parse_body("{ todo!() }")?);
        originals.push((current.def_id, copy, source_name));
        frozen.push(FrozenFunction {
            record: (**record).clone(),
            original_item: pprust::item_to_string(&current.item),
            source_copy: String::new(),
            source_copy_path,
            source_stub: pprust::item_to_string(&source_stub),
            source_stub_path,
        });
    }
    let ids = source_paths.keys().copied().collect::<FxHashSet<_>>();
    validate_additive_macro_rewrites(&analysis, &ast_to_hir, &functions, &ids, &ids, tcx)?;
    // Rewrite before renaming so resolution is exclusively against the complete
    // original crate. Source stubs retain the original ABI and parameter types.
    let mut collector = FrozenReferenceCollector {
        ast_to_hir: &ast_to_hir,
        tcx,
        paths: &source_paths,
        rewrites: FxHashMap::default(),
    };
    collector.visit_crate(&analysis);
    let mut rewriter = CallRewriter {
        rewrites: collector.rewrites,
    };
    for (function, (_, mut copy, name)) in frozen.iter_mut().zip(originals) {
        rewriter.visit_item(&mut copy);
        let ItemKind::Fn(box body) = &mut copy.kind else { unreachable!() };
        body.ident = parsed_ident(&name);
        function.source_copy = pprust::item_to_string(&copy);
    }
    Ok(FrozenProject {
        analysis_source: pprust::crate_to_string_for_macros(&analysis),
        target_source: pprust::crate_to_string_for_macros(&target),
        functions: frozen,
    })
}

struct FrozenReferenceCollector<'a, 'tcx> {
    ast_to_hir: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    paths: &'a FxHashMap<LocalDefId, String>,
    rewrites: FxHashMap<NodeId, String>,
}

impl<'ast> Visitor<'ast> for FrozenReferenceCollector<'_, '_> {
    fn visit_expr(&mut self, expression: &'ast Expr) {
        if matches!(expression.kind, ExprKind::Path(..))
            && let Some(def_id) = resolved_local_function(expression, self.ast_to_hir, self.tcx)
            && let Some(path) = self.paths.get(&def_id)
        {
            self.rewrites.insert(expression.id, path.clone());
        }
        visit::walk_expr(self, expression);
    }
}

fn path_segments(path: &str) -> Vec<String> {
    path.split("::").map(str::to_owned).collect()
}

fn one_item(source: &str) -> Result<P<Item>, ReplacementError> {
    let mut krate = parse_crate(source, ReplacementErrorKind::RewriteFailure)?;
    if krate.items.len() != 1 {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            "frozen function must contain exactly one item".to_owned(),
        ));
    }
    Ok(krate.items.remove(0))
}

pub fn transform_frozen_scc(
    frozen: &FrozenProject,
    request: &ReplacementRequest,
) -> Result<(ExtendedReplacementOutput, Vec<CallableCorrespondence>), ReplacementError> {
    with_parse_session(|| {
        validate_frozen_project(frozen)?;
        validate_request(request)?;
        if !request.accepted_correspondence.is_empty() {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                "independent SCC requests cannot contain accepted dependencies".to_owned(),
            ));
        }
        let (transformations, statement_pairs) = prepare_transformations(request)?;
        let mut candidate =
            parse_crate(&frozen.target_source, ReplacementErrorKind::RewriteFailure)?;
        let mut observation = candidate.clone();
        let mut new_correspondence = vec![];
        let mut current_items = vec![];
        let mut unfilled_stub_items = vec![];
        for requested in &request.items {
            let function = frozen
                .functions
                .iter()
                .find(|function| {
                    function.record.id == requested.id && function.record.path == requested.path
                })
                .ok_or_else(|| {
                    item_error(
                        ReplacementErrorKind::TargetResolution,
                        requested,
                        "requested function is absent from frozen interface".to_owned(),
                    )
                })?;
            if requested.name != function.record.name
                || (requested.view != function.record.baseline
                    && requested.view != function.record.applied)
            {
                return Err(item_error(
                    ReplacementErrorKind::InvalidRequest,
                    requested,
                    "requested view differs from frozen skeletons".to_owned(),
                ));
            }
            let original = one_item(&function.original_item)?;
            let transformed = &transformations[&requested.name];
            let (ItemKind::Fn(box original_fn), ItemKind::Fn(box transformed_fn)) =
                (&original.kind, &transformed.kind)
            else {
                unreachable!()
            };
            validate_transformed_header(original_fn, transformed_fn, requested)?;
            let mut implementation = compose_implementation(&original, transformed, requested)?;
            let path = path_segments(&requested.path);
            let mut labeled = implementation.clone();
            labeled.attrs.retain(|attr| !is_export_attribute(attr));
            replace_function_at_path(&mut observation.items, &path, labeled)?;
            let ItemKind::Fn(box body) = &mut implementation.kind else { unreachable!() };
            ProctorLabelRemover.visit_block(body.body.as_mut().unwrap());
            let stub = function_at_path(&candidate.items, &path)
                .expect("frozen template contains the requested function");
            if pprust::item_to_string(&implementation) == pprust::item_to_string(stub) {
                unfilled_stub_items.push(requested.id);
            }
            replace_function_at_path(&mut candidate.items, &path, implementation)?;
            insert_item_at_path(
                &mut observation.items,
                &path[..path.len() - 1],
                one_item(&function.source_copy)?,
            )?;
            new_correspondence.push(correspondence(&function.record));
            current_items.push(CurrentObservationItem {
                item_id: requested.id,
                logical_path: requested.path.clone(),
                implementation_path: requested.path.clone(),
                wrapper_path: None,
                source_copy_path: function.source_copy_path.clone(),
                transform_labels: requested.view.transform_labels(),
            });
        }
        let current = new_correspondence
            .iter()
            .map(|record| record.item_id)
            .collect::<HashSet<_>>();
        let dependencies = frozen
            .functions
            .iter()
            .filter(|function| !current.contains(&function.record.id))
            .map(|function| correspondence(&function.record))
            .collect();
        let mut source_stubs = vec![];
        for function in &frozen.functions {
            let path = path_segments(&function.record.path);
            insert_item_at_path(
                &mut observation.items,
                &path[..path.len() - 1],
                one_item(&function.source_stub)?,
            )?;
            source_stubs.push(SourceStub {
                item_id: function.record.id,
                path: function.source_stub_path.clone(),
            });
        }
        source_stubs.sort_by_key(|stub| stub.item_id);
        unfilled_stub_items.sort_unstable();
        Ok((
            ExtendedReplacementOutput {
                replacement: ReplacementOutput {
                    source: pprust::crate_to_string_for_macros(&candidate),
                    statement_pairs,
                },
                observation_source: pprust::crate_to_string_for_macros(&observation),
                accepted_correspondence: vec![],
                new_correspondence,
                current_items,
                source_stubs,
                unfilled_stub_items,
            },
            dependencies,
        ))
    })
}

fn correspondence(record: &crate::FunctionRecord) -> CallableCorrespondence {
    CallableCorrespondence {
        item_id: record.id,
        logical_path: record.path.clone(),
        implementation_path: record.path.clone(),
        wrapper_path: None,
    }
}

/// Assemble only the explicitly accepted SCC members, in original item order.
pub fn assemble_frozen_project(
    frozen: &FrozenProject,
    accepted: &[AcceptedScc],
) -> Result<String, ReplacementError> {
    with_parse_session(|| {
        validate_frozen_project(frozen)?;
        let mut assembled =
            parse_crate(&frozen.target_source, ReplacementErrorKind::RewriteFailure)?;
        let mut selected = HashMap::new();
        for scc in accepted {
            let source = parse_crate(&scc.source, ReplacementErrorKind::RewriteFailure)?;
            require_same_context(&assembled, &source)?;
            for id in &scc.members {
                let function = frozen
                    .functions
                    .iter()
                    .find(|function| function.record.id == *id)
                    .ok_or_else(|| {
                        global_error(
                            ReplacementErrorKind::TargetResolution,
                            format!("unknown accepted item {id}"),
                        )
                    })?;
                let path = path_segments(&function.record.path);
                let item = function_at_path(&source.items, &path).ok_or_else(|| {
                    global_error(
                        ReplacementErrorKind::TargetResolution,
                        format!("missing accepted function `{}`", function.record.path),
                    )
                })?;
                let expected = function_at_path(&assembled.items, &path)
                    .expect("frozen template contains every function");
                if pprust::item_to_string(item) == pprust::item_to_string(expected) {
                    return Err(global_error(
                        ReplacementErrorKind::InvalidTransformation,
                        format!(
                            "accepted function `{}` still has its frozen stub body",
                            function.record.path
                        ),
                    ));
                }
                let mut header = item.clone();
                let ItemKind::Fn(box body) = &mut header.kind else { unreachable!() };
                body.body = Some(parse_body("{ todo!() }")?);
                if pprust::item_to_string(&header) != pprust::item_to_string(expected)
                    || selected.insert(*id, item.clone()).is_some()
                {
                    return Err(global_error(
                        ReplacementErrorKind::InvalidRequest,
                        format!(
                            "duplicate or inconsistent accepted function `{}`",
                            function.record.path
                        ),
                    ));
                }
            }
        }
        for function in &frozen.functions {
            let item = selected.remove(&function.record.id).ok_or_else(|| {
                global_error(
                    ReplacementErrorKind::TargetResolution,
                    format!("unaccepted function `{}`", function.record.path),
                )
            })?;
            replace_function_at_path(
                &mut assembled.items,
                &path_segments(&function.record.path),
                item,
            )?;
        }
        Ok(pprust::crate_to_string_for_macros(&assembled))
    })
}

fn require_same_context(left: &Crate, right: &Crate) -> Result<(), ReplacementError> {
    let (mut left, mut right) = (left.clone(), right.clone());
    retain_non_function_items(&mut left.items);
    retain_non_function_items(&mut right.items);
    if pprust::crate_to_string_for_macros(&left) != pprust::crate_to_string_for_macros(&right) {
        return Err(global_error(
            ReplacementErrorKind::TargetResolution,
            "target has different non-function context from frozen source".to_owned(),
        ));
    }
    Ok(())
}

pub fn finalize_frozen_project(
    frozen: &FrozenProject,
    assembled: &str,
    target_kind: &str,
    api: &[String],
) -> Result<FinalizedProject, ReplacementError> {
    with_parse_session(|| {
        validate_frozen_project(frozen)?;
        let analysis = parse_crate(
            &frozen.analysis_source,
            ReplacementErrorKind::RewriteFailure,
        )?;
        let mut partial = parse_crate(assembled, ReplacementErrorKind::RewriteFailure)?;
        require_same_context(&analysis, &partial)?;
        finalize_source_functions(&analysis, &mut partial, target_kind, api)?;
        Ok(FinalizedProject {
            source: pprust::crate_to_string_for_macros(&partial),
        })
    })
}

fn finalize_source_functions(
    analysis: &Crate,
    partial: &mut Crate,
    target_kind: &str,
    api: &[String],
) -> Result<(), ReplacementError> {
    fn collect(
        items: &[P<Item>],
        module: &mut Vec<String>,
        result: &mut Vec<(Vec<String>, P<Item>)>,
    ) {
        for item in items {
            match &item.kind {
                ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(children, ..)) => {
                    module.push(ident.to_string());
                    collect(children, module, result);
                    module.pop();
                }
                ItemKind::Fn(function) if function.body.is_some() => {
                    result.push((module.clone(), item.clone()))
                }
                _ => {}
            }
        }
    }
    if !matches!(target_kind, "library" | "executable")
        || (target_kind == "executable" && !api.is_empty())
        || api.iter().any(|name| name == "main")
    {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            "invalid target kind or API function list".to_owned(),
        ));
    }
    let mut functions = vec![];
    collect(&analysis.items, &mut vec![], &mut functions);
    for name in api {
        if !functions.iter().any(|(_, item)| {
            let ItemKind::Fn(function) = &item.kind else { unreachable!() };
            function.ident.name.as_str() == name
                || item.attrs.iter().any(|attr| {
                    attr.has_name(sym::export_name)
                        && attr.value_str().is_some_and(|value| value.as_str() == name)
                })
        }) {
            return Err(global_error(
                ReplacementErrorKind::TargetResolution,
                format!("API function `{name}` did not match any source function"),
            ));
        }
    }
    for (module, item) in &functions {
        let ItemKind::Fn(function) = &item.kind else { unreachable!() };
        if is_supported_two_argument_main_0(function) && functions.iter().filter(|(path, item)| path == module && matches!(&item.kind, ItemKind::Fn(function) if function.ident.name == sym::main)).count() != 1 {
            return Err(global_error(ReplacementErrorKind::RewriteFailure, "two-argument `main_0` requires exactly one sibling `main`".to_owned()));
        }
        if function.ident.name == sym::main {
            let supported = functions.iter().any(|(path, item)| path == module && matches!(&item.kind, ItemKind::Fn(function) if is_supported_two_argument_main_0(function)));
            insert_item_at_path(
                &mut partial.items,
                module,
                if supported {
                    fixed_main_item()?
                } else {
                    item.clone()
                },
            )?;
        }
    }
    Ok(())
}
