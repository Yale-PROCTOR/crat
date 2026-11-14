use super::*;

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UnstructuredPreparationRequest {
    pub members: Vec<u64>,
    pub transformations: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct UnstructuredTarget {
    pub id: u64,
    pub path: String,
    pub name: String,
    pub source: String,
    pub signature: String,
}

#[derive(Debug, Serialize)]
pub struct UnstructuredPreparation {
    pub targets: Vec<UnstructuredTarget>,
    pub candidate: Option<String>,
}

pub struct RetainedFunctions {
    pub source: String,
    pub stubbed_items: Vec<u64>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UnstructuredReplacementRequest {
    pub members: Vec<u64>,
    pub transformation: String,
}

pub struct UnstructuredReplacement {
    pub source: String,
    pub new_correspondence: Vec<CallableCorrespondence>,
}

pub fn strip_proctor_labels(source: &str) -> Result<String, ReplacementError> {
    with_parse_session(|| {
        let mut krate = parse_crate(source, ReplacementErrorKind::InvalidTransformation)?;
        ProctorLabelRemover.visit_crate(&mut krate);
        Ok(pprust::crate_to_string_for_macros(&krate))
    })
}

fn selected_functions<'a>(
    frozen: &'a FrozenProject,
    members: &[u64],
) -> Result<Vec<&'a FrozenFunction>, ReplacementError> {
    if members.is_empty() || members.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            "unstructured members must be nonempty, unique, and sorted".to_owned(),
        ));
    }
    let mut names = HashSet::new();
    members
        .iter()
        .map(|id| {
            let function = frozen
                .functions
                .iter()
                .find(|function| function.record.id == *id)
                .ok_or_else(|| {
                    global_error(
                        ReplacementErrorKind::InvalidRequest,
                        format!("unknown unstructured member {id}"),
                    )
                })?;
            if !names.insert(&function.record.name) {
                return Err(global_error(
                    ReplacementErrorKind::InvalidRequest,
                    "unstructured members have duplicate function names".to_owned(),
                ));
            }
            Ok(function)
        })
        .collect()
}

pub fn prepare_unstructured_repair(
    frozen: &FrozenProject,
    request: &UnstructuredPreparationRequest,
) -> Result<UnstructuredPreparation, ReplacementError> {
    with_parse_session(|| {
        validate_frozen_project(frozen)?;
        let functions = selected_functions(frozen, &request.members)?;
        let targets = functions
            .iter()
            .map(|function| {
                let mut original = one_item(&function.original_item)?;
                ProctorLabelRemover.visit_item(&mut original);
                Ok(UnstructuredTarget {
                    id: function.record.id,
                    path: function.record.path.clone(),
                    name: function.record.name.clone(),
                    source: pprust::item_to_string(&original),
                    signature: function.record.target_signature.clone(),
                })
            })
            .collect::<Result<Vec<_>, ReplacementError>>()?;
        let candidate = request
            .transformations
            .iter()
            .rev()
            .find_map(|source| strip_proctor_labels(source).ok());
        Ok(UnstructuredPreparation { targets, candidate })
    })
}

pub fn retain_frozen_functions(
    frozen: &FrozenProject,
    request: &UnstructuredPreparationRequest,
) -> Result<RetainedFunctions, ReplacementError> {
    with_parse_session(|| {
        validate_frozen_project(frozen)?;
        let functions = selected_functions(frozen, &request.members)?;
        let mut retained = HashMap::new();
        for source in request.transformations.iter().rev() {
            let Ok(mut parsed) = utils::ast::try_parse_crate(source.clone()) else {
                continue;
            };
            ProctorLabelRemover.visit_crate(&mut parsed);
            let mut candidates = HashMap::new();
            for item in &parsed.items {
                let ItemKind::Fn(function) = &item.kind else { continue };
                let name = function.ident.to_string();
                let implementation = function
                    .body
                    .as_ref()
                    .filter(|body| !whole_function_stub(body))
                    .map(|_| item);
                candidates
                    .entry(name)
                    .and_modify(|item| *item = None)
                    .or_insert(implementation);
            }
            for function in &functions {
                if let Some(Some(item)) = candidates.get(&function.record.name) {
                    retained
                        .entry(function.record.id)
                        .or_insert_with(|| (*item).clone());
                }
            }
        }
        let mut candidate =
            parse_crate(&frozen.target_source, ReplacementErrorKind::RewriteFailure)?;
        let mut stubbed_items = Vec::new();
        for function in functions {
            let Some(retained) = retained.remove(&function.record.id) else {
                stubbed_items.push(function.record.id);
                continue;
            };
            let path = path_segments(&function.record.path);
            let mut implementation = function_at_path(&candidate.items, &path)
                .expect("frozen template contains every selected member")
                .clone();
            copy_function_body(&mut implementation, &retained);
            replace_function_at_path(&mut candidate.items, &path, implementation)?;
        }
        Ok(RetainedFunctions {
            source: pprust::crate_to_string_for_macros(&candidate),
            stubbed_items,
        })
    })
}

fn copy_function_body(output: &mut Item, returned: &Item) {
    output
        .attrs
        .retain(|attribute| attribute.style != rustc_ast::AttrStyle::Inner);
    output.attrs.extend(
        returned
            .attrs
            .iter()
            .filter(|attribute| attribute.style == rustc_ast::AttrStyle::Inner)
            .cloned(),
    );
    let (ItemKind::Fn(output), ItemKind::Fn(returned)) = (&mut output.kind, &returned.kind) else {
        unreachable!()
    };
    output.body = returned.body.clone();
}

pub(super) fn whole_function_stub(body: &rustc_ast::Block) -> bool {
    let [statement] = body.stmts.as_slice() else { return false };
    let (StmtKind::Expr(expression) | StmtKind::Semi(expression)) = &statement.kind else {
        return false;
    };
    whole_expression_stub(expression)
}

pub(super) fn whole_expression_stub(expression: &Expr) -> bool {
    match &expression.kind {
        ExprKind::Ret(Some(expression)) | ExprKind::Paren(expression) => {
            whole_expression_stub(expression)
        }
        ExprKind::Block(body, _) => whole_function_stub(body),
        ExprKind::MacCall(mac) => {
            let names = mac
                .path
                .segments
                .iter()
                .map(|segment| segment.ident.name)
                .filter(|name| *name != rustc_span::kw::PathRoot)
                .collect::<Vec<_>>();
            matches!(names.as_slice(), [name] if name.as_str() == "todo")
                || matches!(names.as_slice(), [root, name] if matches!(root.as_str(), "core" | "std") && name.as_str() == "todo")
        }
        _ => false,
    }
}

pub fn replace_unstructured_scc(
    frozen: &FrozenProject,
    request: &UnstructuredReplacementRequest,
) -> Result<UnstructuredReplacement, ReplacementError> {
    with_parse_session(|| {
        validate_frozen_project(frozen)?;
        let functions = selected_functions(frozen, &request.members)?;
        let items = functions
            .iter()
            .map(|function| ReplacementItem {
                id: function.record.id,
                path: function.record.path.clone(),
                name: function.record.name.clone(),
                view: function.record.baseline.clone(),
            })
            .collect::<Vec<_>>();
        let returned = parse_transformations(
            &ReplacementRequest {
                items: items.clone(),
                transformation: request.transformation.clone(),
                accepted_correspondence: vec![],
            },
            true,
        )?;
        let mut candidate =
            parse_crate(&frozen.target_source, ReplacementErrorKind::RewriteFailure)?;
        for (function, requested) in functions.iter().zip(&items) {
            let transformed = &returned[&requested.name];
            let path = path_segments(&function.record.path);
            let stub = function_at_path(&candidate.items, &path)
                .expect("frozen template contains every selected member");
            let mut implementation = stub.clone();
            copy_function_body(&mut implementation, transformed);
            let ItemKind::Fn(box implementation_fn) = &mut implementation.kind else {
                unreachable!()
            };
            if implementation_fn
                .body
                .as_ref()
                .is_none_or(|body| whole_function_stub(body))
            {
                return Err(item_error(
                    ReplacementErrorKind::InvalidTransformation,
                    requested,
                    "replace the generated whole-function todo stub".to_owned(),
                ));
            }
            replace_function_at_path(&mut candidate.items, &path, implementation)?;
        }
        Ok(UnstructuredReplacement {
            source: pprust::crate_to_string_for_macros(&candidate),
            new_correspondence: functions
                .iter()
                .map(|function| correspondence(&function.record))
                .collect(),
        })
    })
}
