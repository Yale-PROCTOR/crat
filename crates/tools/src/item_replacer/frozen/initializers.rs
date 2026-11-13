use super::*;
use crate::skeleton::{initializer_expression, initializer_function, set_initializer};

#[cfg(test)]
mod tests;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FrozenInitializer {
    pub record: crate::ValueRecord,
    pub original_item: String,
    pub target_item: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InitializerTransformationRequest {
    pub item_id: u64,
    pub transformation: String,
}

#[derive(Debug, Serialize)]
#[serde(tag = "status", rename_all = "lowercase")]
pub enum InitializerTransformationResponse {
    Valid { source: String },
    Invalid { diagnostics: String },
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InitializerInstallationRequest {
    pub items: Vec<InitializerHistory>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InitializerHistory {
    pub item_id: u64,
    pub transformations: Vec<String>,
}

fn value_at_path<'a>(items: &'a [P<Item>], path: &[String]) -> Option<&'a P<Item>> {
    let (name, remaining) = path.split_first()?;
    for item in items {
        if remaining.is_empty()
            && item
                .kind
                .ident()
                .is_some_and(|ident| ident.to_string() == *name)
            && matches!(item.kind, ItemKind::Static(..) | ItemKind::Const(..))
        {
            return Some(item);
        }
        if let ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(children, ..)) = &item.kind
            && ident.to_string() == *name
        {
            return value_at_path(children, remaining);
        }
    }
    None
}

fn replace_value_at_path(
    items: &mut [P<Item>],
    path: &[String],
    replacement: P<Item>,
) -> Result<(), ReplacementError> {
    let Some((name, remaining)) = path.split_first() else {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            "empty initializer path".into(),
        ));
    };
    for item in items {
        if remaining.is_empty()
            && item
                .kind
                .ident()
                .is_some_and(|ident| ident.to_string() == *name)
            && matches!(item.kind, ItemKind::Static(..) | ItemKind::Const(..))
        {
            *item = replacement;
            return Ok(());
        }
        if let ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(children, ..)) = &mut item.kind
            && ident.to_string() == *name
        {
            return replace_value_at_path(children, remaining, replacement);
        }
    }
    Err(global_error(
        ReplacementErrorKind::TargetResolution,
        format!("initializer `{}` is absent", path.join("::")),
    ))
}

fn header(item: &Item) -> String {
    let mut item = item.clone();
    match &mut item.kind {
        ItemKind::Static(value) => value.expr = None,
        ItemKind::Const(value) => value.expr = None,
        _ => unreachable!("initializer items have a declaration"),
    }
    pprust::item_to_string(&item)
}

pub(super) fn freeze_initializers(
    records: &[crate::ItemRecord],
    analysis: &Crate,
) -> Result<Vec<FrozenInitializer>, ReplacementError> {
    records
        .iter()
        .filter_map(|record| match record {
            crate::ItemRecord::Value(record) if record.initializer.is_some() => Some(record),
            _ => None,
        })
        .map(|record| {
            let item =
                value_at_path(&analysis.items, &path_segments(&record.path)).ok_or_else(|| {
                    global_error(
                        ReplacementErrorKind::TargetResolution,
                        format!("initializer `{}` is absent", record.path),
                    )
                })?;
            let original_item = pprust::item_to_string(item);
            Ok(FrozenInitializer {
                record: record.clone(),
                original_item: original_item.clone(),
                target_item: original_item,
            })
        })
        .collect()
}

pub(super) fn validate_frozen_initializers(
    frozen: &FrozenProject,
    analysis: &Crate,
    expected: &mut Crate,
) -> Result<(), ReplacementError> {
    let mut ids = frozen
        .functions
        .iter()
        .map(|function| function.record.id)
        .chain(frozen.types.iter().map(|record| record.id))
        .collect::<HashSet<_>>();
    let mut paths = HashSet::new();
    for initializer in &frozen.initializers {
        let record = &initializer.record;
        let path = valid_full_path(&record.path).ok_or_else(|| {
            global_error(
                ReplacementErrorKind::InvalidRequest,
                "invalid frozen initializer path".into(),
            )
        })?;
        if !ids.insert(record.id) || !paths.insert(&record.path) {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                "duplicate frozen initializer identity".into(),
            ));
        }
        let original = one_item(&initializer.original_item)?;
        let target = one_item(&initializer.target_item)?;
        let actual = value_at_path(&analysis.items, &path).ok_or_else(|| {
            global_error(
                ReplacementErrorKind::InvalidRequest,
                "frozen initializer is absent from analysis".into(),
            )
        })?;
        if initializer_expression(&original).is_none()
            || initializer_expression(&target).is_none()
            || pprust::item_to_string(&original) != pprust::item_to_string(actual)
            || header(&original) != header(&target)
            || !matches!(
                (&original.kind, record.kind),
                (ItemKind::Static(..), crate::ItemKindName::Static)
                    | (ItemKind::Const(..), crate::ItemKindName::Const)
            )
        {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                "frozen initializer declaration differs from analysis".into(),
            ));
        }
        let source = record.initializer.as_ref().ok_or_else(|| {
            global_error(
                ReplacementErrorKind::InvalidRequest,
                "frozen initializer has no transformation record".into(),
            )
        })?;
        let annotated = one_item(&source.annotated_source)?;
        let skeleton = one_item(&source.skeleton)?;
        if initializer_expression(&annotated).is_none()
            || initializer_expression(&skeleton).is_none()
            || header(&annotated) != header(&original)
            || header(&skeleton) != header(&original)
        {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                "frozen initializer skeleton changes its declaration".into(),
            ));
        }
        let mut stripped = annotated.clone();
        ProctorLabelRemover.visit_item(&mut stripped);
        if pprust::item_to_string(&stripped) != pprust::item_to_string(&original) {
            return Err(global_error(
                ReplacementErrorKind::InvalidRequest,
                "frozen initializer source differs from analysis".into(),
            ));
        }
        validate_initializer_skeleton(source, &skeleton)?;
        replace_value_at_path(&mut expected.items, &path, target)?;
    }
    Ok(())
}

fn initializer_view(record: &crate::InitializerRecord, function: &Item) -> SkeletonView {
    let mut view = SkeletonView {
        skeleton: pprust::item_to_string(function),
        needs_transformation: record.needs_transformation,
        statement_dispositions: record.statement_dispositions.clone(),
        statement_pair_metadata: vec![],
    };
    view.statement_pair_metadata = view
        .transform_labels()
        .into_iter()
        .map(|label| crate::StatementPairMetadata {
            label,
            before_statement: String::new(),
            printf_template: None,
            pointer_variables_complete: false,
            pointer_variables: vec![],
        })
        .collect();
    view
}

fn validate_initializer_skeleton(
    record: &crate::InitializerRecord,
    skeleton: &Item,
) -> Result<(), ReplacementError> {
    let expression = initializer_expression(skeleton).expect("skeleton expression was checked");
    if record.block != matches!(expression.kind, ExprKind::Block(..)) {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            "initializer block metadata differs from its expression".into(),
        ));
    }
    if record.block {
        let function = initializer_function(skeleton);
        let view = initializer_view(record, &function);
        validate_skeleton_view(&function, &view)
            .map_err(|error| global_error(ReplacementErrorKind::InvalidRequest, error.message))?;
    } else if !record.needs_transformation || !record.statement_dispositions.is_empty() {
        return Err(global_error(
            ReplacementErrorKind::InvalidRequest,
            "non-block initializer has invalid statement metadata".into(),
        ));
    }
    Ok(())
}

fn parse_transformation(source: &str) -> Result<P<Item>, String> {
    let mut krate = utils::ast::try_parse_crate(source.to_owned())?;
    if !krate.attrs.is_empty()
        || krate.items.len() != 1
        || initializer_expression(&krate.items[0]).is_none()
    {
        return Err(
            "return exactly the requested static or const item with a complete initializer".into(),
        );
    }
    Ok(krate.items.remove(0))
}

#[derive(Default)]
struct InitializerBodyCheck {
    labels_allowed: bool,
    problem: Option<String>,
}

impl<'ast> Visitor<'ast> for InitializerBodyCheck {
    fn visit_item(&mut self, _: &'ast Item) {
        self.problem = Some("do not introduce items inside an initializer".into());
    }

    fn visit_attribute(&mut self, attribute: &'ast Attribute) {
        if !self.labels_allowed || !is_proctor_attribute(attribute) {
            self.problem =
                Some("only the required statement labels are allowed in an initializer".into());
        }
    }
}

pub fn transform_frozen_initializer(
    frozen: &FrozenProject,
    request: &InitializerTransformationRequest,
) -> Result<InitializerTransformationResponse, ReplacementError> {
    with_parse_session(|| {
        validate_frozen_project(frozen)?;
        let initializer = frozen
            .initializers
            .iter()
            .find(|initializer| initializer.record.id == request.item_id)
            .ok_or_else(|| {
                global_error(
                    ReplacementErrorKind::InvalidRequest,
                    format!("unknown initializer item {}", request.item_id),
                )
            })?;
        let record = initializer.record.initializer.as_ref().unwrap();
        let result = (|| -> Result<String, String> {
            let mut returned = parse_transformation(&request.transformation)?;
            let expected = one_item(&record.skeleton).map_err(|error| error.message)?;
            if header(&returned) != header(&expected) {
                return Err("preserve the exact global declaration, including its name, kind, type, visibility, mutability, and attributes".into());
            }
            let mut check = InitializerBodyCheck {
                labels_allowed: record.block,
                problem: None,
            };
            check.visit_expr(initializer_expression(&returned).unwrap());
            if let Some(problem) = check.problem {
                return Err(problem);
            }
            if record.block {
                if !matches!(
                    initializer_expression(&returned).unwrap().kind,
                    ExprKind::Block(..)
                ) {
                    return Err("preserve the initializer's block expression".into());
                }
                let expected_fn = initializer_function(&expected);
                let returned_fn = initializer_function(&returned);
                let view = initializer_view(record, &expected_fn);
                let errors = crate::validator::validate_initializer_function_with_view(
                    &expected_fn,
                    &returned_fn,
                    crate::ExpectedFunction {
                        id: initializer.record.id,
                        name: "__proctor_initializer".into(),
                        view: view.clone(),
                    },
                );
                if !errors.is_empty() {
                    return Err(errors
                        .iter()
                        .map(|error| error.message.as_str())
                        .collect::<Vec<_>>()
                        .join("\n"));
                }
                let canonical =
                    canonicalize_function_with_view(&expected_fn, &returned_fn, &view, true)
                        .map_err(|error| error.message)?;
                let ItemKind::Fn(function) = &canonical.kind else { unreachable!() };
                let mut expression = P(initializer_expression(&returned).unwrap().clone());
                let ExprKind::Block(block, _) = &mut expression.kind else { unreachable!() };
                let rules = block.rules;
                *block = function.body.as_ref().unwrap().clone();
                block.rules = rules;
                set_initializer(&mut returned, expression);
            }
            if crate::preservation::has_unfilled_holes(&returned, None) {
                return Err("complete every initializer transformation hole".into());
            }
            Ok(pprust::item_to_string(&returned))
        })();
        Ok(match result {
            Ok(source) => InitializerTransformationResponse::Valid { source },
            Err(diagnostics) => InitializerTransformationResponse::Invalid { diagnostics },
        })
    })
}

pub fn install_frozen_initializers(
    frozen: &FrozenProject,
    request: &InitializerInstallationRequest,
) -> Result<FrozenProject, ReplacementError> {
    with_parse_session(|| {
        validate_frozen_project(frozen)?;
        let histories = request
            .items
            .iter()
            .map(|history| (history.item_id, history))
            .collect::<HashMap<_, _>>();
        let expected = frozen
            .initializers
            .iter()
            .map(|initializer| initializer.record.id)
            .collect::<HashSet<_>>();
        if histories.len() != request.items.len()
            || histories.keys().copied().collect::<HashSet<_>>() != expected
        {
            return Err(global_error(ReplacementErrorKind::InvalidRequest, "initializer histories must cover exactly the selected initializer items without duplicates".into()));
        }
        let mut updated = frozen.clone();
        let mut target = parse_crate(&updated.target_source, ReplacementErrorKind::InvalidRequest)?;
        for initializer in &mut updated.initializers {
            let mut original = one_item(&initializer.original_item)?;
            let name = original.kind.ident().unwrap().to_string();
            for transformation in histories[&initializer.record.id]
                .transformations
                .iter()
                .rev()
            {
                let Ok(krate) = utils::ast::try_parse_crate(transformation.clone()) else {
                    continue;
                };
                let matching = krate
                    .items
                    .iter()
                    .filter(|item| {
                        initializer_expression(item).is_some()
                            && item
                                .kind
                                .ident()
                                .is_some_and(|ident| ident.to_string() == name)
                    })
                    .collect::<Vec<_>>();
                let [candidate] = matching.as_slice() else { continue };
                let expression = initializer_expression(candidate).unwrap();
                if unstructured::whole_expression_stub(expression) {
                    continue;
                }
                let mut expression = P(expression.clone());
                ProctorLabelRemover.visit_expr(&mut expression);
                set_initializer(&mut original, expression);
                break;
            }
            initializer.target_item = pprust::item_to_string(&original);
            replace_value_at_path(
                &mut target.items,
                &path_segments(&initializer.record.path),
                original,
            )?;
        }
        updated.target_source = pprust::crate_to_string_for_macros(&target);
        validate_frozen_project(&updated)?;
        Ok(updated)
    })
}
