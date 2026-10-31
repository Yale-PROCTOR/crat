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
        let returned = parse_transformations(&ReplacementRequest {
            items: items.clone(),
            transformation: request.transformation.clone(),
            accepted_correspondence: vec![],
        })?;
        let mut candidate =
            parse_crate(&frozen.target_source, ReplacementErrorKind::RewriteFailure)?;
        for (function, requested) in functions.iter().zip(&items) {
            let transformed = &returned[&requested.name];
            let ItemKind::Fn(box body) = &transformed.kind else { unreachable!() };
            let mut check = BodyCheck { problem: None };
            if let Some(block) = &body.body {
                check.visit_block(block);
            }
            if !transformed.attrs.is_empty() {
                check.problem = Some("returned function attributes are not allowed");
            }
            if let Some(problem) = check.problem {
                return Err(item_error(
                    ReplacementErrorKind::InvalidTransformation,
                    requested,
                    problem.to_owned(),
                ));
            }
            let expected = one_item(&function.record.baseline.skeleton)?;
            let mut header = compose_implementation(&expected, transformed, requested)?;
            let (ItemKind::Fn(expected_fn), ItemKind::Fn(transformed_fn)) =
                (&expected.kind, &transformed.kind)
            else {
                unreachable!()
            };
            validate_transformed_header(expected_fn, transformed_fn, requested)?;
            let mut expected_header = expected.clone();
            for item in [&mut header, &mut expected_header] {
                let ItemKind::Fn(box body) = &mut item.kind else { unreachable!() };
                body.body = Some(parse_body("{ todo!() }")?);
                TypeParenRemover.visit_item(item);
            }
            if pprust::item_to_string(&header) != pprust::item_to_string(&expected_header)
                || !matches!(body.sig.header.safety, Safety::Unsafe(_))
                || matches!(body.sig.header.constness, rustc_ast::Const::Yes(_))
            {
                return Err(item_error(
                    ReplacementErrorKind::InvalidTransformation,
                    requested,
                    "copy the exact target signature, including parameter names, types, and lifetimes"
                        .to_owned(),
                ));
            }
            let path = path_segments(&function.record.path);
            let stub = function_at_path(&candidate.items, &path)
                .expect("frozen template contains every selected member");
            let mut implementation = stub.clone();
            let ItemKind::Fn(box implementation_fn) = &mut implementation.kind else {
                unreachable!()
            };
            implementation_fn.body = body.body.clone();
            if pprust::item_to_string(&implementation) == pprust::item_to_string(stub) {
                return Err(item_error(
                    ReplacementErrorKind::InvalidTransformation,
                    requested,
                    "complete the unfilled whole-function stub".to_owned(),
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

struct BodyCheck {
    problem: Option<&'static str>,
}

impl<'ast> Visitor<'ast> for BodyCheck {
    fn visit_item(&mut self, _item: &'ast Item) {
        self.problem = Some("do not define additional items inside a function body");
    }

    fn visit_attribute(&mut self, _attribute: &'ast Attribute) {
        self.problem = Some("do not introduce proctor labels or other body attributes");
    }

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if matches!(&expression.kind, ExprKind::Block(block, _) if matches!(block.rules, BlockCheckMode::Unsafe(_)))
        {
            self.problem = Some("do not introduce explicit unsafe blocks");
        }
        visit::walk_expr(self, expression);
    }
}
