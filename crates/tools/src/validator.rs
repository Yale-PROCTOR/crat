use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    panic::{AssertUnwindSafe, catch_unwind},
};

use rustc_ast::{
    AttrKind, Attribute, BindingMode, BlockCheckMode, ByRef, Crate, Expr, ExprKind, FnRetTy,
    GenericParamKind, Item, ItemKind, Local, LocalKind, Pat, PatKind, Stmt, StmtKind, Ty, TyKind,
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use serde::{Deserialize, Serialize, ser::SerializeStruct};

use crate::{
    SkeletonView,
    preservation::{canonicalize_function_with_view, validate_skeleton_view},
};

const SCHEMA_VERSION: u64 = 1;
const TEMP_PREFIX: &str = "proctor_temp_var_";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ValidationRequest {
    pub schema_version: u64,
    pub expected_functions: Vec<ExpectedFunction>,
    pub transformation: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExpectedFunction {
    pub id: u64,
    pub name: String,
    pub view: SkeletonView,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ValidationError {
    pub code: String,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ValidationFailure {
    pub id: Option<u64>,
    pub name: Option<String>,
    pub failed_snippet: String,
    pub errors: Vec<ValidationError>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationResponse {
    Valid,
    Invalid { failures: Vec<ValidationFailure> },
    SetupError { error: ValidationError },
}

impl Serialize for ValidationResponse {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where S: serde::Serializer {
        match self {
            Self::Valid => {
                let mut state = serializer.serialize_struct("ValidationResponse", 2)?;
                state.serialize_field("schema_version", &SCHEMA_VERSION)?;
                state.serialize_field("status", "valid")?;
                state.end()
            }
            Self::Invalid { failures } => {
                let mut state = serializer.serialize_struct("ValidationResponse", 3)?;
                state.serialize_field("schema_version", &SCHEMA_VERSION)?;
                state.serialize_field("status", "invalid")?;
                state.serialize_field("failures", failures)?;
                state.end()
            }
            Self::SetupError { error } => {
                let mut state = serializer.serialize_struct("ValidationResponse", 3)?;
                state.serialize_field("schema_version", &SCHEMA_VERSION)?;
                state.serialize_field("status", "setup_error")?;
                state.serialize_field("error", error)?;
                state.end()
            }
        }
    }
}

impl ValidationResponse {
    pub fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }
}

pub fn validation_response_to_json(
    response: &ValidationResponse,
) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(response)
}

pub fn validate_json(input: &str) -> String {
    let response = match serde_json::from_str::<ValidationRequest>(input) {
        Ok(request) => validate(&request),
        Err(error) => setup_error(
            if error.to_string().contains("unknown field") {
                "unknown_request_field"
            } else {
                "invalid_request_json"
            },
            format!("The validation request is not valid schema-version-1 JSON: {error}"),
        ),
    };
    validation_response_to_json(&response).expect("validation response serialization cannot fail")
}

struct ParsedExpected {
    metadata: ExpectedFunction,
    item: P<Item>,
}

pub fn validate(request: &ValidationRequest) -> ValidationResponse {
    rustc_span::create_session_if_not_set_then(rustc_span::edition::Edition::Edition2021, |_| {
        validate_inner(request)
    })
}

fn validate_inner(request: &ValidationRequest) -> ValidationResponse {
    let expected = match parse_expected_functions(request) {
        Ok(expected) => expected,
        Err(response) => return response,
    };

    let result = match parse_crate(&request.transformation) {
        Ok(result) => result,
        Err(detail) => {
            return global_invalid(
                &request.transformation,
                vec![error(
                    "result_parse_error",
                    format!("The returned Rust transformation does not parse: {detail}"),
                )],
            );
        }
    };

    let mut by_name: BTreeMap<String, Vec<&P<Item>>> = BTreeMap::new();
    let expected_names = expected
        .iter()
        .map(|entry| entry.metadata.name.as_str())
        .collect::<HashSet<_>>();
    let mut nonfunctions = vec![];
    for item in &result.items {
        if matches!(item.kind, ItemKind::Fn(..)) {
            let name = item.kind.ident().unwrap().to_string();
            by_name.entry(name).or_default().push(item);
        } else {
            nonfunctions.push(item);
        }
    }

    let mut set_errors = vec![];
    for entry in &expected {
        if !by_name.contains_key(&entry.metadata.name) {
            set_errors.push(error(
                "missing_function",
                format!(
                    "Expected function `{}` (item {}) is missing. Return it exactly once.",
                    entry.metadata.name, entry.metadata.id
                ),
            ));
        }
    }
    let mut seen_result_functions = HashSet::new();
    for item in &result.items {
        let ItemKind::Fn(..) = item.kind else {
            continue;
        };
        let name = item.kind.ident().unwrap().to_string();
        if !seen_result_functions.insert(name.clone()) {
            set_errors.push(error(
                "duplicate_function",
                format!(
                    "Returned function `{name}` appears more than once. Return it exactly once."
                ),
            ));
        }
    }
    for item in &result.items {
        if let ItemKind::Fn(..) = item.kind {
            let name = item.kind.ident().unwrap().to_string();
            if !expected_names.contains(name.as_str()) {
                set_errors.push(error(
                    "unexpected_function",
                    format!("Returned function `{name}` was not requested. Remove it."),
                ));
            }
        } else {
            set_errors.push(error(
                "unexpected_item",
                format!(
                    "The transformation contains an unexpected top-level {} item. Return only the requested functions.",
                    item_kind_name(item)
                ),
            ));
        }
    }
    debug_assert_eq!(
        nonfunctions.len(),
        set_errors
            .iter()
            .filter(|e| e.code == "unexpected_item")
            .count()
    );
    if !set_errors.is_empty() {
        return global_invalid(&request.transformation, set_errors);
    }

    let mut failures = vec![];
    for entry in expected {
        let result_item = by_name[&entry.metadata.name][0];
        let errors = validate_function(&entry, result_item);
        if !errors.is_empty() {
            failures.push(ValidationFailure {
                id: Some(entry.metadata.id),
                name: Some(entry.metadata.name),
                failed_snippet: pprust::item_to_string(result_item),
                errors,
            });
        }
    }
    if failures.is_empty() {
        ValidationResponse::Valid
    } else {
        ValidationResponse::Invalid { failures }
    }
}

fn parse_expected_functions(
    request: &ValidationRequest,
) -> Result<Vec<ParsedExpected>, ValidationResponse> {
    if request.schema_version != SCHEMA_VERSION {
        return Err(setup_error(
            "unsupported_schema_version",
            format!(
                "Request schema version {} is unsupported; use schema version 1.",
                request.schema_version
            ),
        ));
    }
    if request.expected_functions.is_empty() {
        return Err(setup_error(
            "empty_expected_functions",
            "At least one expected function is required.".to_owned(),
        ));
    }
    let mut ids = HashSet::new();
    for entry in &request.expected_functions {
        if !ids.insert(entry.id) {
            return Err(setup_error(
                "duplicate_expected_id",
                format!(
                    "Expected function item ID {} appears twice. Item IDs must be unique within one validation request.",
                    entry.id
                ),
            ));
        }
    }
    let mut names = HashSet::new();
    for entry in &request.expected_functions {
        if !names.insert(entry.name.as_str()) {
            return Err(setup_error(
                "duplicate_expected_name",
                format!(
                    "Expected function name `{}` appears twice. Function names must be unique within one validation request.",
                    entry.name
                ),
            ));
        }
    }

    let mut parsed = vec![];
    for entry in &request.expected_functions {
        let krate = parse_crate(&entry.view.skeleton).map_err(|detail| {
            setup_error(
                "expected_skeleton_parse_error",
                format!(
                    "Expected skeleton for `{}` (item {}) does not parse: {detail}",
                    entry.name, entry.id
                ),
            )
        })?;
        if krate.items.len() != 1 || !matches!(krate.items[0].kind, ItemKind::Fn(..)) {
            return Err(setup_error(
                "expected_skeleton_item_count",
                format!(
                    "Expected skeleton for `{}` (item {}) must contain exactly one free function.",
                    entry.name, entry.id
                ),
            ));
        }
        let item = krate.items[0].clone();
        let observed_name = item.kind.ident().unwrap().to_string();
        if observed_name != entry.name {
            return Err(setup_error(
                "expected_skeleton_name_mismatch",
                format!(
                    "Expected metadata names `{}`, but its skeleton defines `{observed_name}`. Make the names match.",
                    entry.name
                ),
            ));
        }
        if let Err(message) = validate_expected_skeleton(&item, entry) {
            return Err(setup_error("invalid_expected_skeleton", message));
        }
        parsed.push(ParsedExpected {
            metadata: entry.clone(),
            item,
        });
    }
    Ok(parsed)
}

fn validate_expected_skeleton(item: &Item, entry: &ExpectedFunction) -> Result<(), String> {
    let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
    validate_supported_target_signature(function).map_err(|detail| {
        format!(
            "Expected skeleton for `{}` (item {}) has an unsupported target signature: {detail}",
            entry.name, entry.id
        )
    })?;
    let body = function.body.as_ref().unwrap();
    let transformed = entry
        .view
        .transform_labels()
        .into_iter()
        .collect::<HashSet<_>>();
    let preserved = statement_labels(body)
        .into_iter()
        .filter(|label| !transformed.contains(label))
        .collect();
    let mut scan = BodyScanner::new_with_preserved_labels(true, preserved);
    scan.visit_block(body);
    if let Some(problem) = scan.syntax_errors.first() {
        return Err(format!(
            "Expected skeleton for `{}` (item {}) is invalid: {}",
            entry.name, entry.id, problem.message
        ));
    }
    if let Some(path) = scan.unlabeled_statements.first() {
        return Err(format!(
            "Expected skeleton for `{}` (item {}) contains an unlabeled statement in {path}; every generated skeleton statement must have one canonical `#[proctor(N)]` label.",
            entry.name, entry.id
        ));
    }
    if let Some(item) = scan.items.first() {
        return Err(format!(
            "Expected skeleton for `{}` (item {}) contains a function-local {} item{}; every function-local item is unsupported.",
            entry.name,
            entry.id,
            item.kind,
            label_context(item.label)
        ));
    }
    if let Some(attribute) = scan.body_attributes.first() {
        return Err(format!(
            "Expected skeleton for `{}` (item {}) contains unsupported body attribute `{}`{}; only canonical statement labels are allowed.",
            entry.name,
            entry.id,
            attribute.attribute,
            label_context(attribute.label)
        ));
    }
    if let Some(block) = scan.unsafe_blocks.first() {
        return Err(format!(
            "Expected skeleton for `{}` (item {}) contains an explicit unsafe block{}; generated target skeletons must not contain explicit unsafe blocks.",
            entry.name,
            entry.id,
            label_context(block.label)
        ));
    }
    let mut seen = HashSet::new();
    for occurrence in &scan.labels {
        if !seen.insert(occurrence.label) {
            return Err(format!(
                "Expected skeleton for `{}` (item {}) repeats label {}. Expected labels must be unique.",
                entry.name, entry.id, occurrence.label
            ));
        }
    }
    validate_skeleton_view(item, &entry.view).map_err(|error| {
        format!(
            "Expected skeleton for `{}` (item {}) has invalid preservation metadata: {}",
            entry.name, entry.id, error.message
        )
    })?;
    validate_expected_block(body, &transformed).map_err(|detail| {
        format!(
            "Expected skeleton for `{}` (item {}) has an invalid control/statement tree: {detail}",
            entry.name, entry.id
        )
    })?;
    Ok(())
}

pub(crate) fn validate_rule_application_shape(item: &Item) -> Result<(), String> {
    let ItemKind::Fn(box function) = &item.kind else {
        return Err("an applied skeleton item is not a function".to_owned());
    };
    validate_supported_target_signature(function)
        .map_err(|detail| format!("unsupported target signature: {detail}"))?;
    let body = function
        .body
        .as_ref()
        .ok_or_else(|| "an applied function has no body".to_owned())?;
    let labels = statement_labels(body);
    // Rule application runs before transformed payloads are skeletonized, so
    // every source-shaped restricted conditional is still opaque here.
    let mut scan = BodyScanner::new_with_preserved_labels(true, labels.clone());
    scan.visit_block(body);
    if let Some(problem) = scan.syntax_errors.first() {
        return Err(problem.message.clone());
    }
    if let Some(path) = scan.unlabeled_statements.first() {
        return Err(format!(
            "an applied skeleton contains an unlabeled statement in {path}"
        ));
    }
    if let Some(item) = scan.items.first() {
        return Err(format!(
            "an applied skeleton contains a function-local {} item{}",
            item.kind,
            label_context(item.label)
        ));
    }
    if let Some(attribute) = scan.body_attributes.first() {
        return Err(format!(
            "an applied skeleton contains unsupported body attribute `{}`{}",
            attribute.attribute,
            label_context(attribute.label)
        ));
    }
    if let Some(block) = scan.unsafe_blocks.first() {
        return Err(format!(
            "an applied skeleton contains an explicit unsafe block{}",
            label_context(block.label)
        ));
    }
    let mut seen = HashSet::new();
    if let Some(label) = scan
        .labels
        .iter()
        .map(|occurrence| occurrence.label)
        .find(|label| !seen.insert(*label))
    {
        return Err(format!("an applied skeleton repeats label {label}"));
    }
    if seen != labels.into_iter().collect() {
        return Err("an applied skeleton label scan is inconsistent".to_owned());
    }
    validate_expected_block(body, &HashSet::new())
}

fn validate_supported_target_signature(function: &rustc_ast::Fn) -> Result<(), &'static str> {
    if matches!(function.sig.header.constness, rustc_ast::Const::Yes(_)) {
        return Err("const functions are unsupported");
    }
    if function.sig.header.coroutine_kind.is_some() {
        return Err("async functions are unsupported");
    }
    if function.sig.decl.c_variadic() {
        return Err("variadic functions are unsupported");
    }
    if function.sig.decl.inputs.iter().any(|parameter| {
        !matches!(
            parameter.pat.kind,
            PatKind::Ident(BindingMode(ByRef::No, _), _, None)
        )
    }) {
        return Err("every parameter must be a simple by-value identifier pattern");
    }
    if function
        .generics
        .params
        .iter()
        .any(|parameter| !matches!(parameter.kind, GenericParamKind::Lifetime))
    {
        return Err("type and const generics are unsupported");
    }
    if function
        .generics
        .params
        .iter()
        .any(|parameter| !parameter.attrs.is_empty() || !parameter.bounds.is_empty())
        || function.generics.where_clause.has_where_token
    {
        return Err(
            "lifetime parameter attributes, generic bounds, and where clauses are unsupported",
        );
    }
    Ok(())
}

fn validate_expected_block(
    block: &rustc_ast::Block,
    transformed: &HashSet<u32>,
) -> Result<(), String> {
    for statement in &block.stmts {
        validate_expected_statement(statement, transformed)?;
    }
    Ok(())
}

fn validate_expected_statement(statement: &Stmt, transformed: &HashSet<u32>) -> Result<(), String> {
    let allow_restricted = stmt_label(statement).is_some_and(|label| !transformed.contains(&label));
    match &statement.kind {
        StmtKind::Let(local) => {
            match &local.kind {
                LocalKind::Decl => {}
                LocalKind::Init(initializer) => {
                    validate_expected_payload(initializer, transformed, allow_restricted)?
                }
                LocalKind::InitElse(initializer, else_block) => {
                    validate_expected_payload(initializer, transformed, allow_restricted)?;
                    validate_expected_block(else_block, transformed)?;
                }
            }
            Ok(())
        }
        StmtKind::Item(item) => Err(format!(
            "function-local {} items are unsupported",
            local_item_kind(item)
        )),
        StmtKind::Expr(expression) | StmtKind::Semi(expression) => match &expression.kind {
            ExprKind::Ret(Some(value)) | ExprKind::Break(_, Some(value)) => {
                validate_expected_payload(value, transformed, allow_restricted)
            }
            _ => validate_expected_payload(expression, transformed, allow_restricted),
        },
        StmtKind::MacCall(_) => Ok(()),
        StmtKind::Empty => Err("empty statements are unsupported".to_owned()),
    }
}

fn validate_expected_payload(
    expression: &Expr,
    transformed: &HashSet<u32>,
    allow_restricted: bool,
) -> Result<(), String> {
    match &expression.kind {
        ExprKind::If(condition, then_block, else_expression) => {
            validate_no_nested_control(condition, "an if condition", allow_restricted)?;
            validate_expected_block(then_block, transformed)?;
            if let Some(else_expression) = else_expression {
                match &else_expression.kind {
                    ExprKind::If(..) => {
                        validate_expected_payload(else_expression, transformed, allow_restricted)?
                    }
                    ExprKind::Block(block, _) => validate_expected_block(block, transformed)?,
                    _ => {
                        return Err(
                            "an if else branch must be a block or recursive else-if".to_owned()
                        );
                    }
                }
            }
            Ok(())
        }
        ExprKind::While(condition, body, _) => {
            validate_no_nested_control(condition, "a while condition", allow_restricted)?;
            validate_expected_block(body, transformed)
        }
        ExprKind::ForLoop { iter, body, .. } => {
            validate_no_nested_control(iter, "a for iterator", allow_restricted)?;
            validate_expected_block(body, transformed)
        }
        ExprKind::Loop(body, ..) | ExprKind::Block(body, ..) => {
            validate_expected_block(body, transformed)
        }
        ExprKind::Match(scrutinee, arms, _) => {
            validate_no_nested_control(scrutinee, "a match scrutinee", allow_restricted)?;
            for (index, arm) in arms.iter().enumerate() {
                if let Some(guard) = &arm.guard {
                    validate_no_nested_control(guard, "a match guard", allow_restricted)?;
                }
                let Some(body) = &arm.body else {
                    return Err(format!("match arm {index} has no body"));
                };
                let ExprKind::Block(block, _) = &body.kind else {
                    return Err(format!("match arm {index} must have a block body"));
                };
                validate_expected_block(block, transformed)?;
            }
            Ok(())
        }
        _ => validate_no_nested_control(expression, "a non-control payload", allow_restricted),
    }
}

fn validate_no_nested_control(
    expression: &Expr,
    role: &str,
    allow_restricted: bool,
) -> Result<(), String> {
    struct ControlFinder {
        found: bool,
        allow_restricted: bool,
    }

    impl<'ast> Visitor<'ast> for ControlFinder {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if control_expr(expression, ControlRole::Statement).is_some() {
                if !self.allow_restricted || !crate::skeleton::is_restricted_conditional(expression)
                {
                    self.found = true;
                }
                return;
            }
            visit::walk_expr(self, expression);
        }
    }

    let mut finder = ControlFinder {
        found: false,
        allow_restricted,
    };
    finder.visit_expr(expression);
    if finder.found {
        Err(format!(
            "a control expression is nested beneath {role}; controls must remain roots of supported statement payloads"
        ))
    } else {
        Ok(())
    }
}

fn parse_crate(source: &str) -> Result<Crate, String> {
    rustc_span::create_session_if_not_set_then(rustc_span::edition::Edition::Edition2021, |_| {
        catch_unwind(AssertUnwindSafe(|| {
            utils::ast::parse_crate(source.to_owned())
        }))
        .map_err(|_| "the Rust parser rejected the snippet".to_owned())
    })
}

fn setup_error(code: &str, message: String) -> ValidationResponse {
    ValidationResponse::SetupError {
        error: error(code, message),
    }
}

fn global_invalid(source: &str, errors: Vec<ValidationError>) -> ValidationResponse {
    ValidationResponse::Invalid {
        failures: vec![ValidationFailure {
            id: None,
            name: None,
            failed_snippet: source.to_owned(),
            errors,
        }],
    }
}

fn error(code: &str, message: String) -> ValidationError {
    ValidationError {
        code: code.to_owned(),
        message,
    }
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

fn validate_function(expected: &ParsedExpected, result: &Item) -> Vec<ValidationError> {
    let signature_errors = validate_signature(expected, result);
    let ItemKind::Fn(box expected_fn) = &expected.item.kind else { unreachable!() };
    let ItemKind::Fn(box returned_fn) = &result.kind else { unreachable!() };
    let mut returned_scan = BodyScanner::new(false);
    returned_scan.visit_block(returned_fn.body.as_ref().unwrap());
    let canonical = match canonicalize_function_with_view(
        &expected.item,
        result,
        &expected.metadata.view,
        false,
    ) {
        Ok(canonical) => canonical,
        Err(problem) => {
            let mut errors = signature_errors;
            errors.push(error(
                problem.code,
                function_message(expected, problem.message),
            ));
            return errors;
        }
    };
    let ItemKind::Fn(box result_fn) = &canonical.kind else { unreachable!() };
    let expected_body = expected_fn.body.as_ref().unwrap();
    let result_body = result_fn.body.as_ref().unwrap();

    let transformed = expected
        .metadata
        .view
        .transform_labels()
        .into_iter()
        .collect::<HashSet<_>>();
    let preserved = statement_labels(expected_body)
        .into_iter()
        .filter(|label| !transformed.contains(label))
        .collect();
    let mut expected_scan = BodyScanner::new_with_preserved_labels(true, preserved);
    expected_scan.visit_block(expected_body);
    let mut result_scan = BodyScanner::new(false);
    result_scan.visit_block(result_body);

    let mut declaration_errors = vec![];
    let mut temporary_errors = vec![];
    validate_declarations(
        expected,
        &expected_scan,
        &result_scan,
        &mut declaration_errors,
        &mut temporary_errors,
    );

    let mut label_errors = vec![];
    for problem in &result_scan.syntax_errors {
        label_errors.push(error(
            &problem.code,
            function_message(
                expected,
                format!("{}. Correct the attribute and preserve only canonical `#[proctor(N)]` statement labels.", problem.message),
            ),
        ));
    }

    let mut control_errors = vec![];
    let mut role_suppressions = RoleSuppressions::default();
    validate_nested_label_repetition(expected, &result_scan, &mut label_errors);
    validate_statement_list(
        expected,
        &expected_body.stmts,
        &result_body.stmts,
        "function body",
        false,
        &expected_scan,
        &result_scan,
        &mut role_suppressions,
        &mut label_errors,
        &mut control_errors,
    );
    validate_fallback_labels(expected, &expected_scan, &result_scan, &mut label_errors);
    order_label_errors(&mut label_errors, &expected_scan, &result_scan);

    validate_temporaries(
        expected,
        &canonical,
        &expected_scan,
        &result_scan,
        &returned_scan,
        &mut temporary_errors,
    );

    let mut safety_errors = vec![];
    for occurrence in &result_scan.unsafe_blocks {
        safety_errors.push(error(
            "explicit_unsafe_block",
            function_message(
                expected,
                format!(
                    "an explicit unsafe block occurs{}; remove the block because the transformed function is already unsafe",
                    label_context(occurrence.label)
                ),
            ),
        ));
    }
    for occurrence in &result_scan.body_attributes {
        safety_errors.push(error(
            "unexpected_body_attribute",
            function_message(
                expected,
                format!(
                    "unexpected statement or expression attribute `{}` occurs{}; remove it",
                    occurrence.attribute,
                    label_context(occurrence.label)
                ),
            ),
        ));
    }

    let mut errors = signature_errors;
    errors.extend(declaration_errors);
    errors.extend(label_errors);
    errors.extend(control_errors);
    errors.extend(temporary_errors);
    errors.extend(safety_errors);
    suppress_dependent_cascades(&mut errors, &expected_scan, &role_suppressions);
    errors
}

fn suppress_dependent_cascades(
    errors: &mut Vec<ValidationError>,
    expected: &BodyScanner,
    role_suppressions: &RoleSuppressions,
) {
    let parent_codes = [
        "control_kind_mismatch",
        "control_role_mismatch",
        "match_arm_shape_mismatch",
        "missing_control_root",
        "multiple_control_roots",
        "let_else_shape_mismatch",
    ];
    let parent_failures = errors
        .iter()
        .filter(|error| parent_codes.contains(&error.code.as_str()))
        .filter(|error| {
            !(error.code == "control_kind_mismatch"
                && error.message.contains("recursive else-if chain"))
        })
        .filter_map(|error| {
            first_message_label(&error.message).map(|label| (label, error.code.clone()))
        })
        .collect::<Vec<_>>();
    let parent_labels = parent_failures
        .iter()
        .map(|(label, _)| *label)
        .collect::<HashSet<_>>();
    if parent_labels.is_empty()
        && role_suppressions.expected_labels.is_empty()
        && role_suppressions.result_labels.is_empty()
    {
        return;
    }
    let expected_labels = expected
        .labels
        .iter()
        .map(|occurrence| occurrence.label)
        .collect::<HashSet<_>>();
    let parents = expected
        .labels
        .iter()
        .filter_map(|occurrence| {
            occurrence
                .parent_label
                .map(|parent| (occurrence.label, parent))
        })
        .collect::<HashMap<_, _>>();
    let suppressed = expected
        .labels
        .iter()
        .filter_map(|occurrence| {
            let mut current = occurrence.parent_label;
            while let Some(parent) = current {
                if parent_labels.contains(&parent) {
                    return Some(occurrence.label);
                }
                current = parents.get(&parent).copied();
            }
            None
        })
        .collect::<HashSet<_>>();
    let dependent_codes = [
        "missing_label",
        "unexpected_label",
        "label_order_mismatch",
        "descendant_location_mismatch",
        "missing_existing_binding",
        "duplicate_existing_binding",
        "existing_binding_location_mismatch",
        "existing_binding_mode_mismatch",
        "local_type_mismatch",
        "local_type_presence_mismatch",
        "unexpected_nested_item",
        "temporary_outside_expansion_group",
    ];
    errors.retain(|error| {
        if !dependent_codes.contains(&error.code.as_str()) {
            return true;
        }
        if role_suppressions
            .expected_labels
            .iter()
            .any(|label| message_names_label(&error.message, *label))
            || role_suppressions
                .result_labels
                .iter()
                .filter(|label| !expected_labels.contains(label))
                .any(|label| message_names_label(&error.message, *label))
        {
            return false;
        }
        if suppressed
            .iter()
            .any(|label| message_names_label(&error.message, *label))
        {
            return false;
        }
        let unreliable_parent_binding = parent_failures.iter().any(|(label, code)| {
            expected.bindings.iter().any(|binding| {
                let role_is_unreliable = match code.as_str() {
                    "let_else_shape_mismatch" => binding.anchor.contains("let-else pattern"),
                    "match_arm_shape_mismatch" => binding.anchor.contains("match-arm-"),
                    "control_kind_mismatch" | "missing_control_root" | "multiple_control_roots" => {
                        binding.anchor.contains("if-let pattern")
                            || binding.anchor.contains("while-let pattern")
                            || binding.anchor.contains("for pattern")
                            || binding.anchor.contains("match-arm-")
                    }
                    "control_role_mismatch" | "branch_shape_mismatch" => false,
                    _ => false,
                };
                binding.label == Some(*label)
                    && role_is_unreliable
                    && message_names_label(&error.message, *label)
                    && error.message.contains(&format!("`{}`", binding.name))
            })
        });
        !unreliable_parent_binding
    });
}

fn first_message_label(message: &str) -> Option<u32> {
    let start = message.find("label ")? + "label ".len();
    let digits = message[start..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect::<String>();
    digits.parse().ok()
}

fn message_names_label(message: &str, label: u32) -> bool {
    let needle = format!("label {label}");
    message.match_indices(&needle).any(|(index, _)| {
        message[index + needle.len()..]
            .chars()
            .next()
            .is_none_or(|character| !character.is_ascii_digit())
    })
}

fn validate_signature(expected: &ParsedExpected, result: &Item) -> Vec<ValidationError> {
    let ItemKind::Fn(box expected_fn) = &expected.item.kind else { unreachable!() };
    let ItemKind::Fn(box result_fn) = &result.kind else { unreachable!() };
    let expected_params = &expected_fn.sig.decl.inputs;
    let result_params = &result_fn.sig.decl.inputs;
    let mut errors = vec![];
    let expected_generics = lifetime_generic_declaration(&expected_fn.generics);
    let result_generics = lifetime_generic_declaration(&result_fn.generics);
    if expected_generics != result_generics {
        errors.push(error(
            "generic_parameter_mismatch",
            function_message(
                expected,
                format!(
                    "expected lifetime-generic declaration `{expected_generics}` but observed `{result_generics}`; copy the target skeleton's complete lifetime-generic declaration"
                ),
            ),
        ));
    }
    if expected_params.len() != result_params.len() {
        errors.push(error(
            "parameter_count_mismatch",
            function_message(
                expected,
                format!(
                    "expected {} parameters but observed {}; restore the target parameter list",
                    expected_params.len(),
                    result_params.len()
                ),
            ),
        ));
    }
    for (index, (expected_param, result_param)) in
        expected_params.iter().zip(result_params).enumerate()
    {
        let expected_name = simple_pattern_name(&expected_param.pat);
        let result_name = simple_pattern_name(&result_param.pat);
        if expected_name != result_name {
            errors.push(error(
                "parameter_name_mismatch",
                function_message(
                    expected,
                    format!(
                        "parameter {index} must be named `{}` but was `{}`; restore the target parameter name",
                        expected_name.unwrap_or("<pattern>"),
                        result_name.unwrap_or("<pattern>")
                    ),
                ),
            ));
        }
    }
    for (expected_param, result_param) in expected_params.iter().zip(result_params) {
        let expected_name = simple_pattern_name(&expected_param.pat);
        let expected_ty = canonical_type(&expected_param.ty);
        let result_ty = canonical_type(&result_param.ty);
        if expected_ty != result_ty {
            errors.push(error(
                "parameter_type_mismatch",
                function_message(
                    expected,
                    format!(
                        "parameter {} expected type `{expected_ty}` but observed `{result_ty}`; use the exact structural target type",
                        expected_name.unwrap_or("<pattern>")
                    ),
                ),
            ));
        }
    }
    let expected_return = canonical_return(&expected_fn.sig.decl.output);
    let result_return = canonical_return(&result_fn.sig.decl.output);
    if expected_return != result_return {
        errors.push(error(
            "return_type_mismatch",
            function_message(
                expected,
                format!(
                    "expected return type `{expected_return}` but observed `{result_return}`; restore the exact target return type"
                ),
            ),
        ));
    }
    errors
}

fn lifetime_generic_declaration(generics: &rustc_ast::Generics) -> String {
    let mut item = utils::item!("fn __proctor_generic_probe() {{}}");
    let ItemKind::Fn(box function) = &mut item.kind else { unreachable!() };
    function.generics = generics.clone();
    pprust::item_to_string(&item)
}

fn simple_pattern_name(pat: &Pat) -> Option<&str> {
    let PatKind::Ident(_, ident, None) = &pat.kind else {
        return None;
    };
    Some(ident.name.as_str())
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

fn function_message(expected: &ParsedExpected, detail: String) -> String {
    format!(
        "Function `{}` (item {}): {detail}.",
        expected.metadata.name, expected.metadata.id
    )
}

fn label_context(label: Option<u32>) -> String {
    label
        .map(|label| format!(" in expansion group label {label}"))
        .unwrap_or_default()
}

#[derive(Debug, Clone)]
struct SyntaxProblem {
    code: String,
    message: String,
}

#[derive(Debug, Clone)]
struct LabelOccurrence {
    label: u32,
    list_path: String,
    parent_label: Option<u32>,
}

#[derive(Debug, Clone)]
struct BodyOccurrence {
    label: Option<u32>,
}

#[derive(Debug, Clone)]
struct AttributeOccurrence {
    label: Option<u32>,
    attribute: String,
}

#[derive(Debug, Clone)]
struct BindingDecl {
    name: String,
    anchor: String,
    pattern_paths: Vec<String>,
    by_ref: bool,
    explicit_type: Option<String>,
    label: Option<u32>,
    order: usize,
}

#[derive(Debug, Clone)]
struct NestedItemDecl {
    name: String,
    kind: String,
    label: Option<u32>,
}

#[derive(Debug, Clone)]
struct TempReference {
    name: String,
    label: Option<u32>,
}

#[derive(Default)]
struct RoleSuppressions {
    expected_labels: HashSet<u32>,
    result_labels: HashSet<u32>,
}

struct BodyScanner {
    expected: bool,
    list_path: Vec<String>,
    current_label: Option<u32>,
    labels: Vec<LabelOccurrence>,
    syntax_errors: Vec<SyntaxProblem>,
    body_attributes: Vec<AttributeOccurrence>,
    bindings: Vec<BindingDecl>,
    items: Vec<NestedItemDecl>,
    macro_temporaries: Vec<TempReference>,
    unsafe_blocks: Vec<BodyOccurrence>,
    unlabeled_statements: Vec<String>,
    skip_expr_attrs: bool,
    root_attribute_spans: HashSet<(u32, u32)>,
    next_declaration_order: usize,
    preserved_labels: HashSet<u32>,
    non_control_payload: bool,
    suppress_unlabeled: usize,
}

impl BodyScanner {
    fn new(expected: bool) -> Self {
        Self {
            expected,
            list_path: vec!["function body".to_owned()],
            current_label: None,
            labels: vec![],
            syntax_errors: vec![],
            body_attributes: vec![],
            bindings: vec![],
            items: vec![],
            macro_temporaries: vec![],
            unsafe_blocks: vec![],
            unlabeled_statements: vec![],
            skip_expr_attrs: false,
            root_attribute_spans: HashSet::new(),
            next_declaration_order: 0,
            preserved_labels: HashSet::new(),
            non_control_payload: false,
            suppress_unlabeled: 0,
        }
    }

    fn new_with_preserved_labels(expected: bool, preserved_labels: HashSet<u32>) -> Self {
        Self {
            preserved_labels,
            ..Self::new(expected)
        }
    }

    fn path(&self) -> String {
        self.list_path.join(" / ")
    }

    fn with_path(&mut self, segment: String, f: impl FnOnce(&mut Self)) {
        self.list_path.push(segment);
        f(self);
        self.list_path.pop();
    }

    fn collect_pattern(&mut self, pat: &Pat, role: &str, explicit_type: Option<&Ty>) {
        let mut raw = vec![];
        collect_pattern_bindings(pat, "root", &mut raw);
        let mut grouped: Vec<(String, Vec<RawBinding>)> = vec![];
        for binding in raw {
            if let Some((_, occurrences)) =
                grouped.iter_mut().find(|(name, _)| *name == binding.name)
            {
                occurrences.push(binding);
            } else {
                grouped.push((binding.name.clone(), vec![binding]));
            }
        }
        for (name, bindings) in grouped {
            if bindings.iter().all(|binding| binding.constructor_like)
                && !name.starts_with(TEMP_PREFIX)
            {
                continue;
            }
            let by_ref = bindings[0].by_ref;
            let mut pattern_paths = bindings
                .into_iter()
                .map(|binding| binding.path)
                .collect::<Vec<_>>();
            pattern_paths.sort();
            self.bindings.push(BindingDecl {
                name,
                anchor: format!("{} / {role}", self.path()),
                pattern_paths,
                by_ref,
                explicit_type: explicit_type.map(canonical_type),
                label: self.current_label,
                order: self.next_declaration_order,
            });
            self.next_declaration_order += 1;
        }
    }

    fn record_root_attributes(
        &mut self,
        attrs: &[Attribute],
        allow_non_proctor: bool,
    ) -> Option<u32> {
        let mut labels = vec![];
        for attr in attrs {
            match parse_label_attribute(attr) {
                LabelAttribute::NotProctor => {
                    if !allow_non_proctor {
                        self.body_attributes.push(AttributeOccurrence {
                            label: self.current_label,
                            attribute: pprust::attribute_to_string(attr),
                        });
                    }
                }
                LabelAttribute::Valid(label) => labels.push(label),
                LabelAttribute::Malformed(message) => {
                    self.syntax_errors.push(SyntaxProblem {
                        code: "malformed_label".to_owned(),
                        message,
                    });
                }
            }
        }
        if labels.len() > 1 {
            self.syntax_errors.push(SyntaxProblem {
                code: "malformed_label".to_owned(),
                message: "a statement has duplicate `proctor` attributes".to_owned(),
            });
            None
        } else {
            labels.first().copied()
        }
    }

    fn visit_payload(&mut self, expression: &Expr) {
        if control_expr(expression, ControlRole::Statement).is_some() {
            self.visit_expr(expression);
            return;
        }
        let previous = std::mem::replace(&mut self.non_control_payload, true);
        self.visit_expr(expression);
        self.non_control_payload = previous;
    }

    fn visit_statement_expression(&mut self, expression: &Expr) {
        if matches!(
            expression.kind,
            ExprKind::Ret(..) | ExprKind::Break(..) | ExprKind::Continue(..)
        ) {
            self.visit_expr(expression);
        } else {
            self.visit_payload(expression);
        }
    }
}

impl<'ast> Visitor<'ast> for BodyScanner {
    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        let previous_label = self.current_label;
        let root_attrs = effective_stmt_attrs(stmt);
        self.root_attribute_spans.extend(
            root_attrs
                .iter()
                .map(|attr| (attr.span.lo().0, attr.span.hi().0)),
        );
        let label =
            self.record_root_attributes(root_attrs, matches!(stmt.kind, StmtKind::Item(..)));
        if self.expected && label.is_none() && self.suppress_unlabeled == 0 {
            self.unlabeled_statements.push(self.path());
        }
        if let Some(label) = label {
            self.labels.push(LabelOccurrence {
                label,
                list_path: self.path(),
                parent_label: previous_label,
            });
            self.current_label = Some(label);
        }
        match &stmt.kind {
            StmtKind::Let(local) => self.visit_local(local),
            StmtKind::Item(item) => self.visit_item(item),
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                self.skip_expr_attrs = true;
                self.visit_statement_expression(expr);
            }
            StmtKind::MacCall(mac) => self.visit_mac_call(&mac.mac),
            StmtKind::Empty => {}
        }
        self.current_label = previous_label;
    }

    fn visit_local(&mut self, local: &'ast Local) {
        self.collect_pattern(
            &local.pat,
            if matches!(local.kind, LocalKind::InitElse(..)) {
                "let-else pattern"
            } else {
                "let pattern"
            },
            local.ty.as_deref(),
        );
        match &local.kind {
            LocalKind::Decl => {}
            LocalKind::Init(init) => self.visit_payload(init),
            LocalKind::InitElse(init, else_block) => {
                self.visit_payload(init);
                self.with_path("let-else body".to_owned(), |this| {
                    this.visit_block(else_block)
                });
            }
        }
    }

    fn visit_item(&mut self, item: &'ast Item) {
        let kind = local_item_kind(item);
        let name = item
            .kind
            .ident()
            .map(|ident| ident.to_string())
            .unwrap_or_else(|| "<anonymous>".to_owned());
        self.items.push(NestedItemDecl {
            name,
            kind: kind.to_owned(),
            label: self.current_label,
        });
        self.next_declaration_order += 1;
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        let skip_attrs = std::mem::take(&mut self.skip_expr_attrs);
        if !skip_attrs {
            for attr in &expr.attrs {
                if self
                    .root_attribute_spans
                    .contains(&(attr.span.lo().0, attr.span.hi().0))
                {
                    continue;
                }
                if matches!(
                    parse_label_attribute(attr),
                    LabelAttribute::Valid(_) | LabelAttribute::Malformed(_)
                ) {
                    self.syntax_errors.push(SyntaxProblem {
                        code: "misplaced_label".to_owned(),
                        message: format!(
                            "`{}` is attached to an expression instead of a statement root",
                            pprust::attribute_to_string(attr)
                        ),
                    });
                } else {
                    self.body_attributes.push(AttributeOccurrence {
                        label: self.current_label,
                        attribute: pprust::attribute_to_string(attr),
                    });
                }
            }
        }
        let opaque_restricted = self.non_control_payload
            && self
                .current_label
                .is_some_and(|label| self.preserved_labels.contains(&label))
            && crate::skeleton::is_restricted_conditional(expr);
        if opaque_restricted {
            self.suppress_unlabeled += 1;
        }
        match &expr.kind {
            ExprKind::If(condition, then_block, else_expr) => {
                if let ExprKind::Let(pat, value, ..) = &condition.kind {
                    self.collect_pattern(pat, "if-let pattern", None);
                    self.visit_payload(value);
                } else {
                    self.visit_payload(condition);
                }
                self.with_path("if then branch".to_owned(), |this| {
                    this.visit_block(then_block)
                });
                if let Some(else_expr) = else_expr {
                    match &else_expr.kind {
                        ExprKind::If(..) => {
                            self.with_path("else-if".to_owned(), |this| this.visit_expr(else_expr))
                        }
                        ExprKind::Block(block, _) => self
                            .with_path("if else branch".to_owned(), |this| this.visit_block(block)),
                        _ => self.visit_expr(else_expr),
                    }
                }
            }
            ExprKind::While(condition, body, _) => {
                if let ExprKind::Let(pat, value, ..) = &condition.kind {
                    self.collect_pattern(pat, "while-let pattern", None);
                    self.visit_payload(value);
                } else {
                    self.visit_payload(condition);
                }
                self.with_path("while body".to_owned(), |this| this.visit_block(body));
            }
            ExprKind::ForLoop {
                pat, iter, body, ..
            } => {
                self.collect_pattern(pat, "for pattern", None);
                self.visit_payload(iter);
                self.with_path("for body".to_owned(), |this| this.visit_block(body));
            }
            ExprKind::Loop(body, ..) => {
                self.with_path("loop body".to_owned(), |this| this.visit_block(body));
            }
            ExprKind::Block(block, _) => {
                if matches!(block.rules, BlockCheckMode::Unsafe(..)) {
                    self.unsafe_blocks.push(BodyOccurrence {
                        label: self.current_label,
                    });
                }
                self.with_path("plain block".to_owned(), |this| this.visit_block(block));
            }
            ExprKind::Match(scrutinee, arms, _) => {
                self.visit_payload(scrutinee);
                for (index, arm) in arms.iter().enumerate() {
                    self.with_path(format!("match arm {index}"), |this| {
                        this.collect_pattern(&arm.pat, &format!("match-arm-{index} pattern"), None);
                        if let Some(guard) = &arm.guard {
                            this.visit_payload(guard);
                        }
                        if let Some(body) = &arm.body {
                            this.visit_expr(body);
                        }
                    });
                }
            }
            ExprKind::Ret(value) | ExprKind::Break(_, value) => {
                if let Some(value) = value {
                    self.visit_payload(value);
                }
            }
            ExprKind::Closure(closure) => {
                for (index, param) in closure.fn_decl.inputs.iter().enumerate() {
                    self.collect_pattern(
                        &param.pat,
                        &format!("closure parameter {index}"),
                        Some(&param.ty),
                    );
                }
                self.visit_expr(&closure.body);
            }
            ExprKind::MacCall(mac) => self.visit_mac_call(mac),
            _ => visit::walk_expr(self, expr),
        }
        if opaque_restricted {
            self.suppress_unlabeled -= 1;
        }
    }

    fn visit_mac_call(&mut self, mac: &'ast rustc_ast::MacCall) {
        collect_temp_symbols(&mac.args.tokens, &mut |name| {
            self.macro_temporaries.push(TempReference {
                name,
                label: self.current_label,
            });
        });
    }
}

fn stmt_attrs(stmt: &Stmt) -> &[Attribute] {
    match &stmt.kind {
        StmtKind::Let(local) => &local.attrs,
        StmtKind::Item(item) => &item.attrs,
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => &expr.attrs,
        StmtKind::MacCall(mac) => &mac.attrs,
        StmtKind::Empty => &[],
    }
}

fn effective_stmt_attrs(stmt: &Stmt) -> &[Attribute] {
    match &stmt.kind {
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => leading_expr_attrs(expr),
        _ => stmt_attrs(stmt),
    }
}

fn leading_expr_attrs(expr: &Expr) -> &[Attribute] {
    if !expr.attrs.is_empty() {
        return &expr.attrs;
    }
    match &expr.kind {
        ExprKind::Binary(_, left, _)
        | ExprKind::Unary(_, left)
        | ExprKind::Assign(left, ..)
        | ExprKind::AssignOp(_, left, _)
        | ExprKind::Cast(left, _)
        | ExprKind::Type(left, _)
        | ExprKind::Field(left, _)
        | ExprKind::Index(left, _, _)
        | ExprKind::Paren(left)
        | ExprKind::Try(left)
        | ExprKind::Await(left, _)
        | ExprKind::Use(left, _) => leading_expr_attrs(left),
        ExprKind::Call(callee, _) => leading_expr_attrs(callee),
        _ => &expr.attrs,
    }
}

fn statement_labels(block: &rustc_ast::Block) -> HashSet<u32> {
    struct Collector(HashSet<u32>);

    impl<'ast> Visitor<'ast> for Collector {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if let Some(label) = stmt_label(statement) {
                self.0.insert(label);
            }
            visit::walk_stmt(self, statement);
        }
    }

    let mut collector = Collector(HashSet::new());
    collector.visit_block(block);
    collector.0
}

enum LabelAttribute {
    NotProctor,
    Valid(u32),
    Malformed(String),
}

fn parse_label_attribute(attr: &Attribute) -> LabelAttribute {
    let AttrKind::Normal(normal) = &attr.kind else {
        return LabelAttribute::NotProctor;
    };
    let segments = &normal.item.path.segments;
    let proctor_like = segments
        .last()
        .is_some_and(|segment| segment.ident.name.as_str() == "proctor");
    if !proctor_like {
        return LabelAttribute::NotProctor;
    }
    let rendered = pprust::attribute_to_string(attr);
    if segments.len() != 1 {
        return LabelAttribute::Malformed(format!(
            "label attribute `{rendered}` must use the exact path `proctor`"
        ));
    }
    let Some(argument) = rendered
        .strip_prefix("#[proctor(")
        .and_then(|value| value.strip_suffix(")]"))
    else {
        return LabelAttribute::Malformed(format!(
            "label attribute `{rendered}` must have exactly one integer argument"
        ));
    };
    if argument.is_empty()
        || (argument != "0"
            && (argument.starts_with('0') || !argument.bytes().all(|byte| byte.is_ascii_digit())))
    {
        return LabelAttribute::Malformed(format!(
            "label `{argument}` is malformed; use exactly `0|[1-9][0-9]*` in the u32 range"
        ));
    }
    match argument.parse::<u32>() {
        Ok(label) => LabelAttribute::Valid(label),
        Err(_) => LabelAttribute::Malformed(format!(
            "label `{argument}` is malformed; use exactly `0|[1-9][0-9]*` in the u32 range"
        )),
    }
}

#[derive(Clone)]
struct RawBinding {
    name: String,
    path: String,
    by_ref: bool,
    constructor_like: bool,
}

fn collect_pattern_bindings(pat: &Pat, path: &str, output: &mut Vec<RawBinding>) {
    match &pat.kind {
        PatKind::Ident(BindingMode(by_ref, _), ident, subpattern) => {
            let name = ident.to_string();
            output.push(RawBinding {
                constructor_like: name
                    .trim_start_matches("r#")
                    .chars()
                    .next()
                    .is_some_and(char::is_uppercase)
                    && subpattern.is_none(),
                name,
                path: format!("{path}/@binder"),
                by_ref: matches!(by_ref, ByRef::Yes(_)),
            });
            if let Some(subpattern) = subpattern {
                collect_pattern_bindings(subpattern, &format!("{path}/@subpattern"), output);
            }
        }
        PatKind::Struct(_, _, fields, _) => {
            for field in fields {
                collect_pattern_bindings(
                    &field.pat,
                    &format!("{path}/struct-field:{}", field.ident),
                    output,
                );
            }
        }
        PatKind::TupleStruct(_, _, patterns) => {
            for (index, pattern) in patterns.iter().enumerate() {
                collect_pattern_bindings(pattern, &format!("{path}/tuple-struct:{index}"), output);
            }
        }
        PatKind::Or(patterns) => {
            for (index, pattern) in patterns.iter().enumerate() {
                collect_pattern_bindings(pattern, &format!("{path}/or:{index}"), output);
            }
        }
        PatKind::Tuple(patterns) => {
            for (index, pattern) in patterns.iter().enumerate() {
                collect_pattern_bindings(pattern, &format!("{path}/tuple:{index}"), output);
            }
        }
        PatKind::Box(pattern) => {
            collect_pattern_bindings(pattern, &format!("{path}/box"), output);
        }
        PatKind::Deref(pattern) => {
            collect_pattern_bindings(pattern, &format!("{path}/deref"), output);
        }
        PatKind::Ref(pattern, mutability) => {
            collect_pattern_bindings(pattern, &format!("{path}/ref:{mutability:?}"), output);
        }
        PatKind::Slice(patterns) => {
            let rest = patterns
                .iter()
                .position(|pattern| matches!(pattern.kind, PatKind::Rest));
            for (index, pattern) in patterns.iter().enumerate() {
                let position = match rest {
                    Some(rest) if index < rest => format!("slice-prefix:{index}"),
                    Some(rest) if index > rest => {
                        format!("slice-suffix:{}", patterns.len() - index - 1)
                    }
                    Some(_) => "slice-rest".to_owned(),
                    None => format!("slice:{index}"),
                };
                collect_pattern_bindings(pattern, &format!("{path}/{position}"), output);
            }
        }
        PatKind::Guard(pattern, _) => {
            collect_pattern_bindings(pattern, &format!("{path}/guard"), output);
        }
        PatKind::Paren(pattern) => {
            collect_pattern_bindings(pattern, &format!("{path}/paren"), output);
        }
        _ => {}
    }
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

fn collect_temp_symbols(
    tokens: &rustc_ast::tokenstream::TokenStream,
    output: &mut impl FnMut(String),
) {
    use rustc_ast::{
        token::TokenKind,
        tokenstream::{TokenStream, TokenTree},
    };

    fn walk(tokens: &TokenStream, output: &mut impl FnMut(String)) {
        for tree in tokens.iter() {
            match tree {
                TokenTree::Token(token, _) => {
                    if let TokenKind::Ident(symbol, _) = token.kind {
                        let name = symbol.to_string();
                        if is_temp_name(&name) {
                            output(name);
                        }
                    }
                }
                TokenTree::Delimited(_, _, _, inner) => walk(inner, output),
            }
        }
    }
    walk(tokens, output);
}

fn is_temp_name(name: &str) -> bool {
    name.strip_prefix(TEMP_PREFIX).is_some_and(|suffix| {
        !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
    })
}

fn validate_declarations(
    expected: &ParsedExpected,
    expected_scan: &BodyScanner,
    result_scan: &BodyScanner,
    errors: &mut Vec<ValidationError>,
    temporary_errors: &mut Vec<ValidationError>,
) {
    let mut expected_errors = vec![];
    let mut matched_result_bindings = HashSet::new();
    let ItemKind::Fn(box expected_function) = &expected.item.kind else { unreachable!() };
    let mut expected_names = expected_scan
        .bindings
        .iter()
        .map(|binding| binding.name.as_str())
        .collect::<HashSet<_>>();
    expected_names.extend(
        expected_function
            .sig
            .decl
            .inputs
            .iter()
            .filter_map(|parameter| simple_pattern_name(&parameter.pat)),
    );

    for expected_binding in &expected_scan.bindings {
        let exact = result_scan
            .bindings
            .iter()
            .enumerate()
            .filter(|(index, result)| {
                !matched_result_bindings.contains(index)
                    && same_binding_position(expected_binding, result)
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if exact.len() > 1 {
            expected_errors.push((expected_binding.order, error(
                "duplicate_existing_binding",
                function_message(
                    expected,
                    format!(
                        "existing binding `{}` is declared more than once{}; preserve exactly one declaration in its original structural role",
                        expected_binding.name,
                        label_context(expected_binding.label)
                    ),
                ),
            )));
            matched_result_bindings.extend(exact);
            continue;
        }
        let matched = if let Some(index) = exact.first().copied() {
            Some((index, true))
        } else {
            let same_name = result_scan
                .bindings
                .iter()
                .enumerate()
                .filter(|(index, result)| {
                    !matched_result_bindings.contains(index)
                        && result.name == expected_binding.name
                        && !expected_scan
                            .bindings
                            .iter()
                            .any(|candidate| same_binding_position(candidate, result))
                })
                .map(|(index, _)| index)
                .collect::<Vec<_>>();
            if same_name.len() == 1 {
                let index = same_name[0];
                let observed = &result_scan.bindings[index];
                expected_errors.push((expected_binding.order, error(
                    "existing_binding_location_mismatch",
                    function_message(
                        expected,
                        format!(
                            "existing binding `{}` expected {} in `{}` but was observed {} in `{}`; restore its original label and pattern role",
                            expected_binding.name,
                            label_context(expected_binding.label),
                            expected_binding.anchor,
                            label_context(observed.label),
                            observed.anchor
                        ),
                    ),
                )));
                Some((index, false))
            } else if same_name.len() > 1 {
                expected_errors.push((expected_binding.order, error(
                    "duplicate_existing_binding",
                    function_message(
                        expected,
                        format!(
                            "existing binding `{}` has multiple declarations; restore exactly one declaration in its original structural role",
                            expected_binding.name
                        ),
                    ),
                )));
                matched_result_bindings.extend(same_name);
                None
            } else {
                expected_errors.push((expected_binding.order, error(
                    "missing_existing_binding",
                    function_message(
                        expected,
                        format!(
                            "existing binding `{}` is missing{} from `{}`; restore it exactly once",
                            expected_binding.name,
                            label_context(expected_binding.label),
                            expected_binding.anchor
                        ),
                    ),
                )));
                None
            }
        };
        let Some((index, exact_position)) = matched else {
            continue;
        };
        matched_result_bindings.insert(index);
        if !exact_position {
            continue;
        }
        let observed = &result_scan.bindings[index];
        if expected_binding.by_ref != observed.by_ref {
            expected_errors.push((expected_binding.order, error(
                "existing_binding_mode_mismatch",
                function_message(
                    expected,
                    format!(
                        "binding `{}`{} expected {} mode but observed {}; restore or remove `ref` as required (binding `mut` may differ)",
                        expected_binding.name,
                        label_context(expected_binding.label),
                        if expected_binding.by_ref { "`ref`" } else { "by-value" },
                        if observed.by_ref { "`ref`" } else { "by-value" }
                    ),
                ),
            )));
        }
        match (
            expected_binding.explicit_type.as_deref(),
            observed.explicit_type.as_deref(),
        ) {
            (Some(expected_ty), Some(observed_ty)) if expected_ty != observed_ty => {
                expected_errors.push((expected_binding.order, error(
                    "local_type_mismatch",
                    function_message(
                        expected,
                        format!(
                            "binding `{}`{} expected local type `{expected_ty}` but observed `{observed_ty}`; use the exact structural target type",
                            expected_binding.name,
                            label_context(expected_binding.label)
                        ),
                    ),
                )));
            }
            (Some(_), None) | (None, Some(_)) => {
                expected_errors.push((expected_binding.order, error(
                    "local_type_presence_mismatch",
                    function_message(
                        expected,
                        format!(
                            "binding `{}`{} must {} an explicit local type exactly as in the target skeleton",
                            expected_binding.name,
                            label_context(expected_binding.label),
                            if expected_binding.explicit_type.is_some() {
                                "retain"
                            } else {
                                "omit"
                            }
                        ),
                    ),
                )));
            }
            _ => {}
        }
    }

    for (index, result_binding) in result_scan.bindings.iter().enumerate() {
        if matched_result_bindings.contains(&index) {
            continue;
        }
        if expected_names.contains(result_binding.name.as_str()) {
            temporary_errors.push(error(
                "invalid_generated_binding_name",
                function_message(
                    expected,
                    format!(
                        "new binding `{}` reuses an existing target binding spelling; choose a fresh `proctor_temp_var_n` name",
                        result_binding.name
                    ),
                ),
            ));
        } else if !is_temp_name(&result_binding.name) {
            temporary_errors.push(error(
                "invalid_generated_binding_name",
                function_message(
                    expected,
                    format!(
                        "new binding `{}`{} is invalid; new bindings must match exactly `proctor_temp_var_n` with a nonnegative decimal integer suffix",
                        result_binding.name,
                        label_context(result_binding.label)
                    ),
                ),
            ));
        }
    }

    expected_errors.sort_by_key(|(order, _)| *order);
    errors.extend(expected_errors.into_iter().map(|(_, error)| error));
    for item in &result_scan.items {
        errors.push(error(
            "unexpected_nested_item",
            function_message(
                expected,
                format!(
                    "unexpected function-local {} item `{}`{} was introduced; every function-local item is unsupported",
                    item.kind,
                    item.name,
                    label_context(item.label)
                ),
            ),
        ));
    }
}

fn same_binding_position(expected: &BindingDecl, result: &BindingDecl) -> bool {
    expected.name == result.name
        && expected.anchor == result.anchor
        && expected.pattern_paths == result.pattern_paths
        && expected.label == result.label
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ControlKind {
    PlainBlock,
    If,
    IfLet,
    While,
    WhileLet,
    For,
    Loop,
    Match,
}

impl ControlKind {
    fn name(self) -> &'static str {
        match self {
            Self::PlainBlock => "plain block",
            Self::If => "if",
            Self::IfLet => "if let",
            Self::While => "while",
            Self::WhileLet => "while let",
            Self::For => "for",
            Self::Loop => "loop",
            Self::Match => "match",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ControlRole {
    Statement,
    LetInitializer,
    ReturnValue,
    BreakValue,
    MatchArmTail,
}

impl ControlRole {
    fn name(self) -> &'static str {
        match self {
            Self::Statement => "statement root",
            Self::LetInitializer => "direct let initializer",
            Self::ReturnValue => "direct return value",
            Self::BreakValue => "direct break value",
            Self::MatchArmTail => "match-arm block tail",
        }
    }
}

struct ControlRoot<'a> {
    kind: ControlKind,
    role: ControlRole,
    expr: &'a Expr,
}

fn control_root(stmt: &Stmt, arm_tail: bool) -> Option<ControlRoot<'_>> {
    match &stmt.kind {
        StmtKind::Let(local) => match &local.kind {
            LocalKind::Init(expr) | LocalKind::InitElse(expr, _) => {
                control_expr(expr, ControlRole::LetInitializer)
            }
            LocalKind::Decl => None,
        },
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => match &expr.kind {
            ExprKind::Ret(Some(value)) => control_expr(value, ControlRole::ReturnValue),
            ExprKind::Break(_, Some(value)) => control_expr(value, ControlRole::BreakValue),
            _ => control_expr(
                expr,
                if arm_tail && matches!(stmt.kind, StmtKind::Expr(..)) {
                    ControlRole::MatchArmTail
                } else {
                    ControlRole::Statement
                },
            ),
        },
        _ => None,
    }
}

fn control_expr(expr: &Expr, role: ControlRole) -> Option<ControlRoot<'_>> {
    let kind = match &expr.kind {
        ExprKind::Block(..) => ControlKind::PlainBlock,
        ExprKind::If(condition, ..) if matches!(condition.kind, ExprKind::Let(..)) => {
            ControlKind::IfLet
        }
        ExprKind::If(..) => ControlKind::If,
        ExprKind::While(condition, ..) if matches!(condition.kind, ExprKind::Let(..)) => {
            ControlKind::WhileLet
        }
        ExprKind::While(..) => ControlKind::While,
        ExprKind::ForLoop { .. } => ControlKind::For,
        ExprKind::Loop(..) => ControlKind::Loop,
        ExprKind::Match(..) => ControlKind::Match,
        _ => return None,
    };
    Some(ControlRoot { kind, role, expr })
}

struct StatementGroup<'a> {
    label: Option<u32>,
    statements: Vec<&'a Stmt>,
}

fn statement_groups(stmts: &[Stmt]) -> Vec<StatementGroup<'_>> {
    let mut groups: Vec<StatementGroup<'_>> = vec![];
    for stmt in stmts {
        let label = stmt_label(stmt);
        if label.is_some() && groups.last().is_some_and(|group| group.label == label) {
            groups.last_mut().unwrap().statements.push(stmt);
        } else {
            groups.push(StatementGroup {
                label,
                statements: vec![stmt],
            });
        }
    }
    groups
}

fn stmt_label(stmt: &Stmt) -> Option<u32> {
    effective_stmt_attrs(stmt).iter().find_map(|attr| {
        if let LabelAttribute::Valid(label) = parse_label_attribute(attr) {
            Some(label)
        } else {
            None
        }
    })
}

fn stmt_has_malformed_label(stmt: &Stmt) -> bool {
    effective_stmt_attrs(stmt)
        .iter()
        .any(|attr| matches!(parse_label_attribute(attr), LabelAttribute::Malformed(_)))
}

#[allow(clippy::too_many_arguments)]
fn validate_statement_list(
    expected: &ParsedExpected,
    expected_stmts: &[Stmt],
    result_stmts: &[Stmt],
    path: &str,
    arm_tail: bool,
    expected_scan: &BodyScanner,
    result_scan: &BodyScanner,
    role_suppressions: &mut RoleSuppressions,
    label_errors: &mut Vec<ValidationError>,
    control_errors: &mut Vec<ValidationError>,
) {
    let expected_groups = statement_groups(expected_stmts);
    let result_groups = statement_groups(result_stmts);
    let expected_labels = expected_groups
        .iter()
        .filter_map(|group| group.label)
        .collect::<Vec<_>>();
    let observed_labels = result_groups
        .iter()
        .filter_map(|group| group.label)
        .collect::<Vec<_>>();

    let mut seen = HashSet::new();
    let mut nonconsecutive = false;
    for label in &observed_labels {
        if !seen.insert(*label) {
            nonconsecutive = true;
            label_errors.push(error(
                "nonconsecutive_label",
                function_message(
                    expected,
                    format!(
                        "label {label} reappears after another expansion group begins in {path}; keep all same-label siblings consecutive"
                    ),
                ),
            ));
        }
    }
    if !nonconsecutive
        && observed_labels.len() == expected_labels.len()
        && observed_labels
            .iter()
            .all(|label| expected_labels.contains(label))
        && observed_labels != expected_labels
    {
        label_errors.push(error(
            "label_order_mismatch",
            function_message(
                expected,
                format!(
                    "labels in {path} expected sequence `{}` but observed group sequence `{}`; restore the original order",
                    render_labels(&expected_labels),
                    render_labels(&observed_labels)
                ),
            ),
        ));
    }

    let expected_all = expected_scan
        .labels
        .iter()
        .map(|occurrence| occurrence.label)
        .collect::<HashSet<_>>();
    let result_all = result_scan
        .labels
        .iter()
        .map(|occurrence| occurrence.label)
        .collect::<HashSet<_>>();

    for (expected_group_index, label) in expected_labels.iter().enumerate() {
        if !observed_labels.contains(label) {
            if result_all.contains(label) {
                let observed_path = result_scan
                    .labels
                    .iter()
                    .find(|occurrence| occurrence.label == *label)
                    .map(|occurrence| occurrence.list_path.as_str())
                    .unwrap_or("another structural role");
                control_errors.push(error(
                    "descendant_location_mismatch",
                    function_message(
                        expected,
                        format!(
                            "label {label} expected in {path} but was observed in {observed_path}; restore it to its original branch, arm, loop, block, or let-else role"
                        ),
                    ),
                ));
            } else {
                let malformed_occupies_position = result_groups
                    .get(expected_group_index)
                    .is_some_and(|group| {
                        group.label.is_none()
                            && group
                                .statements
                                .iter()
                                .any(|statement| stmt_has_malformed_label(statement))
                    });
                if malformed_occupies_position {
                    continue;
                }
                let predecessor = expected_labels
                    .iter()
                    .position(|candidate| candidate == label)
                    .and_then(|index| index.checked_sub(1))
                    .map(|index| format!(" after label {}", expected_labels[index]))
                    .unwrap_or_default();
                label_errors.push(error(
                    "missing_label",
                    function_message(
                        expected,
                        format!(
                            "label {label} is missing from {path}; restore label {label}{predecessor} in its original structural position"
                        ),
                    ),
                ));
            }
        }
    }
    for label in &observed_labels {
        if !expected_all.contains(label) {
            label_errors.push(error(
                "unexpected_label",
                function_message(
                    expected,
                    format!(
                        "label {label} is not present in the target skeleton; remove the new numeric label"
                    ),
                ),
            ));
        }
    }
    for group in &result_groups {
        if group.label.is_none()
            && !group
                .statements
                .iter()
                .any(|statement| stmt_has_malformed_label(statement))
        {
            label_errors.push(error(
                "unlabeled_group_statement",
                function_message(
                    expected,
                    format!(
                        "an unlabeled sibling statement occurs in {path}; attach it to an expansion group or nest it inside one group"
                    ),
                ),
            ));
        }
    }

    for expected_group in expected_groups {
        let Some(label) = expected_group.label else {
            continue;
        };
        let Some(result_group) = result_groups
            .iter()
            .find(|group| group.label == Some(label))
        else {
            continue;
        };
        let expected_stmt = expected_group.statements[0];
        if is_let_else(expected_stmt) {
            let candidates = result_group
                .statements
                .iter()
                .filter(|stmt| is_let_else(stmt))
                .copied()
                .collect::<Vec<_>>();
            if candidates.len() != 1 {
                control_errors.push(error(
                    "let_else_shape_mismatch",
                    function_message(
                        expected,
                        format!(
                            "label {label} must preserve exactly one let-else statement and its else body"
                        ),
                    ),
                ));
                continue;
            }
            let StmtKind::Let(expected_local) = &expected_stmt.kind else { unreachable!() };
            let StmtKind::Let(result_local) = &candidates[0].kind else { unreachable!() };
            let LocalKind::InitElse(_, expected_else) = &expected_local.kind else {
                unreachable!()
            };
            let LocalKind::InitElse(_, result_else) = &result_local.kind else { unreachable!() };
            validate_statement_list(
                expected,
                &expected_else.stmts,
                &result_else.stmts,
                &format!("{path} / label {label} let-else body"),
                false,
                expected_scan,
                result_scan,
                role_suppressions,
                label_errors,
                control_errors,
            );
            continue;
        }
        let Some(expected_control) = control_root(expected_stmt, arm_tail) else {
            continue;
        };
        let controls = result_group
            .statements
            .iter()
            .filter_map(|stmt| control_root(stmt, arm_tail))
            .collect::<Vec<_>>();
        if controls.is_empty() {
            control_errors.push(error(
                "missing_control_root",
                function_message(
                    expected,
                    format!(
                        "label {label} must contain exactly one preserved {} control root in the {} role",
                        expected_control.kind.name(),
                        expected_control.role.name()
                    ),
                ),
            ));
            continue;
        }
        if controls.len() > 1 {
            control_errors.push(error(
                "multiple_control_roots",
                function_message(
                    expected,
                    format!(
                        "label {label} contains multiple control-root statements; keep exactly one preserved {} root",
                        expected_control.kind.name()
                    ),
                ),
            ));
            continue;
        }
        let observed = &controls[0];
        if observed.role != expected_control.role {
            control_errors.push(error(
                "control_role_mismatch",
                function_message(
                    expected,
                    format!(
                        "label {label} expected the control as {} but observed {}; restore the original statement role",
                        expected_control.role.name(),
                        observed.role.name()
                    ),
                ),
            ));
            continue;
        }
        if observed.kind != expected_control.kind {
            control_errors.push(error(
                "control_kind_mismatch",
                function_message(
                    expected,
                    format!(
                        "label {label} expected {} but observed {}; restore the original control kind",
                        expected_control.kind.name(),
                        observed.kind.name()
                    ),
                ),
            ));
            continue;
        }
        validate_control_shape(
            expected,
            label,
            &expected_control,
            observed,
            path,
            expected_scan,
            result_scan,
            role_suppressions,
            label_errors,
            control_errors,
        );
    }
}

fn render_labels(labels: &[u32]) -> String {
    labels
        .iter()
        .map(u32::to_string)
        .collect::<Vec<_>>()
        .join(",")
}

fn is_let_else(stmt: &Stmt) -> bool {
    matches!(
        stmt.kind,
        StmtKind::Let(box Local {
            kind: LocalKind::InitElse(..),
            ..
        })
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_control_shape(
    expected: &ParsedExpected,
    label: u32,
    expected_control: &ControlRoot<'_>,
    result_control: &ControlRoot<'_>,
    path: &str,
    expected_scan: &BodyScanner,
    result_scan: &BodyScanner,
    role_suppressions: &mut RoleSuppressions,
    label_errors: &mut Vec<ValidationError>,
    control_errors: &mut Vec<ValidationError>,
) {
    match (&expected_control.expr.kind, &result_control.expr.kind) {
        (
            ExprKind::If(_, expected_then, expected_else),
            ExprKind::If(_, result_then, result_else),
        ) => {
            validate_statement_list(
                expected,
                &expected_then.stmts,
                &result_then.stmts,
                &format!("{path} / label {label} then branch"),
                false,
                expected_scan,
                result_scan,
                role_suppressions,
                label_errors,
                control_errors,
            );
            validate_else(
                expected,
                label,
                expected_else.as_deref(),
                result_else.as_deref(),
                path,
                expected_scan,
                result_scan,
                role_suppressions,
                label_errors,
                control_errors,
            );
        }
        (ExprKind::While(_, expected_body, _), ExprKind::While(_, result_body, _)) => {
            validate_statement_list(
                expected,
                &expected_body.stmts,
                &result_body.stmts,
                &format!("{path} / label {label} while body"),
                false,
                expected_scan,
                result_scan,
                role_suppressions,
                label_errors,
                control_errors,
            )
        }
        (
            ExprKind::ForLoop {
                body: expected_body,
                ..
            },
            ExprKind::ForLoop {
                body: result_body, ..
            },
        ) => validate_statement_list(
            expected,
            &expected_body.stmts,
            &result_body.stmts,
            &format!("{path} / label {label} for body"),
            false,
            expected_scan,
            result_scan,
            role_suppressions,
            label_errors,
            control_errors,
        ),
        (ExprKind::Loop(expected_body, ..), ExprKind::Loop(result_body, ..))
        | (ExprKind::Block(expected_body, ..), ExprKind::Block(result_body, ..)) => {
            validate_statement_list(
                expected,
                &expected_body.stmts,
                &result_body.stmts,
                &format!(
                    "{path} / label {label} {} body",
                    expected_control.kind.name()
                ),
                false,
                expected_scan,
                result_scan,
                role_suppressions,
                label_errors,
                control_errors,
            )
        }
        (ExprKind::Match(_, expected_arms, _), ExprKind::Match(_, result_arms, _)) => {
            if expected_arms.len() != result_arms.len() {
                control_errors.push(error(
                    "match_arm_shape_mismatch",
                    function_message(
                        expected,
                        format!(
                            "label {label} expected {} match arms but observed {}; restore arm count and order",
                            expected_arms.len(),
                            result_arms.len()
                        ),
                    ),
                ));
                return;
            }
            for (index, (expected_arm, result_arm)) in
                expected_arms.iter().zip(result_arms).enumerate()
            {
                if expected_arm.guard.is_some() != result_arm.guard.is_some() {
                    control_errors.push(error(
                        "match_guard_mismatch",
                        function_message(
                            expected,
                            format!(
                                "label {label} match arm {index} changed guard presence; restore the original guard shape"
                            ),
                        ),
                    ));
                    continue;
                }
                let (Some(expected_body), Some(result_body)) =
                    (&expected_arm.body, &result_arm.body)
                else {
                    continue;
                };
                let (ExprKind::Block(expected_block, _), ExprKind::Block(result_block, _)) =
                    (&expected_body.kind, &result_body.kind)
                else {
                    control_errors.push(error(
                        "match_arm_shape_mismatch",
                        function_message(
                            expected,
                            format!("label {label} match arm {index} must retain its block body"),
                        ),
                    ));
                    continue;
                };
                validate_statement_list(
                    expected,
                    &expected_block.stmts,
                    &result_block.stmts,
                    &format!("{path} / label {label} match arm {index}"),
                    true,
                    expected_scan,
                    result_scan,
                    role_suppressions,
                    label_errors,
                    control_errors,
                );
            }
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_else(
    expected: &ParsedExpected,
    label: u32,
    expected_else: Option<&Expr>,
    result_else: Option<&Expr>,
    path: &str,
    expected_scan: &BodyScanner,
    result_scan: &BodyScanner,
    role_suppressions: &mut RoleSuppressions,
    label_errors: &mut Vec<ValidationError>,
    control_errors: &mut Vec<ValidationError>,
) {
    let (expected_else, result_else) = match (expected_else, result_else) {
        (None, None) => return,
        (Some(expected_else), Some(result_else)) => (expected_else, result_else),
        _ => {
            control_errors.push(error(
                "branch_shape_mismatch",
                function_message(
                    expected,
                    format!(
                        "label {label} changed the existence or recursive else-if shape; restore the original branches"
                    ),
                ),
            ));
            record_unreliable_expr_labels(expected_else, &mut role_suppressions.expected_labels);
            record_unreliable_expr_labels(result_else, &mut role_suppressions.result_labels);
            return;
        }
    };
    match (&expected_else.kind, &result_else.kind) {
        (ExprKind::Block(expected_block, _), ExprKind::Block(result_block, _)) => {
            validate_statement_list(
                expected,
                &expected_block.stmts,
                &result_block.stmts,
                &format!("{path} / label {label} else branch"),
                false,
                expected_scan,
                result_scan,
                role_suppressions,
                label_errors,
                control_errors,
            );
        }
        (
            ExprKind::If(expected_condition, expected_then, expected_next),
            ExprKind::If(result_condition, result_then, result_next),
        ) => {
            let expected_kind = if matches!(expected_condition.kind, ExprKind::Let(..)) {
                ControlKind::IfLet
            } else {
                ControlKind::If
            };
            let result_kind = if matches!(result_condition.kind, ExprKind::Let(..)) {
                ControlKind::IfLet
            } else {
                ControlKind::If
            };
            if expected_kind != result_kind {
                control_errors.push(error(
                    "control_kind_mismatch",
                    function_message(
                        expected,
                        format!(
                            "label {label} expected {} in the recursive else-if chain but observed {}; restore the original control kind",
                            expected_kind.name(),
                            result_kind.name()
                        ),
                    ),
                ));
                record_unreliable_expr_labels(
                    Some(expected_else),
                    &mut role_suppressions.expected_labels,
                );
                record_unreliable_expr_labels(
                    Some(result_else),
                    &mut role_suppressions.result_labels,
                );
                return;
            }
            validate_statement_list(
                expected,
                &expected_then.stmts,
                &result_then.stmts,
                &format!("{path} / label {label} else-if then branch"),
                false,
                expected_scan,
                result_scan,
                role_suppressions,
                label_errors,
                control_errors,
            );
            validate_else(
                expected,
                label,
                expected_next.as_deref(),
                result_next.as_deref(),
                path,
                expected_scan,
                result_scan,
                role_suppressions,
                label_errors,
                control_errors,
            );
        }
        _ => {
            control_errors.push(error(
                "branch_shape_mismatch",
                function_message(
                    expected,
                    format!(
                        "label {label} changed the existence or recursive else-if shape; restore the original branches"
                    ),
                ),
            ));
            record_unreliable_expr_labels(
                Some(expected_else),
                &mut role_suppressions.expected_labels,
            );
            record_unreliable_expr_labels(Some(result_else), &mut role_suppressions.result_labels);
        }
    }
}

fn record_unreliable_expr_labels(expr: Option<&Expr>, labels: &mut HashSet<u32>) {
    struct LabelCollector<'a> {
        labels: &'a mut HashSet<u32>,
    }

    impl<'ast> Visitor<'ast> for LabelCollector<'_> {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if let Some(label) = stmt_label(statement) {
                self.labels.insert(label);
            }
            visit::walk_stmt(self, statement);
        }
    }

    if let Some(expr) = expr {
        LabelCollector { labels }.visit_expr(expr);
    }
}

fn validate_nested_label_repetition(
    expected: &ParsedExpected,
    result_scan: &BodyScanner,
    errors: &mut Vec<ValidationError>,
) {
    let mut label_paths = BTreeMap::<u32, BTreeSet<&str>>::new();
    for occurrence in &result_scan.labels {
        label_paths
            .entry(occurrence.label)
            .or_default()
            .insert(&occurrence.list_path);
    }
    for (label, paths) in label_paths {
        if paths.len() > 1
            && !errors.iter().any(|candidate| {
                candidate.code == "nested_label_repetition"
                    && message_names_label(&candidate.message, label)
            })
        {
            errors.push(error(
                "nested_label_repetition",
                function_message(
                    expected,
                    format!(
                        "label {label} appears at multiple nested statement-list levels; keep repeated occurrences as consecutive siblings in one expansion group"
                    ),
                ),
            ));
        }
    }
    for occurrence in &result_scan.labels {
        if occurrence.parent_label == Some(occurrence.label)
            && !errors.iter().any(|candidate| {
                candidate.code == "nested_label_repetition"
                    && message_names_label(&candidate.message, occurrence.label)
            })
        {
            errors.push(error(
                "nested_label_repetition",
                function_message(
                    expected,
                    format!(
                        "label {} is repeated in nested code; repeated occurrences must be consecutive siblings in one expansion group",
                        occurrence.label
                    ),
                ),
            ));
        }
    }
}

fn validate_fallback_labels(
    expected: &ParsedExpected,
    expected_scan: &BodyScanner,
    result_scan: &BodyScanner,
    errors: &mut Vec<ValidationError>,
) {
    let expected_labels = expected_scan
        .labels
        .iter()
        .map(|occurrence| occurrence.label)
        .collect::<HashSet<_>>();
    for occurrence in &result_scan.labels {
        if !expected_labels.contains(&occurrence.label)
            && !errors.iter().any(|candidate| {
                candidate.code == "unexpected_label"
                    && message_names_label(&candidate.message, occurrence.label)
            })
        {
            errors.push(error(
                "unexpected_label",
                function_message(
                    expected,
                    format!(
                        "label {} is not present in the target skeleton; remove it",
                        occurrence.label
                    ),
                ),
            ));
        }
    }
    for occurrence in &expected_scan.labels {
        if !result_scan.syntax_errors.is_empty() {
            break;
        }
        if !result_scan
            .labels
            .iter()
            .any(|result| result.label == occurrence.label)
            && !errors.iter().any(|candidate| {
                candidate.code == "missing_label"
                    && message_names_label(&candidate.message, occurrence.label)
            })
        {
            errors.push(error(
                "missing_label",
                function_message(
                    expected,
                    format!(
                        "label {} is missing; restore it in its original structural position",
                        occurrence.label
                    ),
                ),
            ));
        }
    }
}

fn order_label_errors(
    errors: &mut Vec<ValidationError>,
    expected_scan: &BodyScanner,
    result_scan: &BodyScanner,
) {
    let expected_position = |error: &ValidationError| {
        first_message_label(&error.message)
            .and_then(|label| {
                expected_scan
                    .labels
                    .iter()
                    .position(|occurrence| occurrence.label == label)
            })
            .or_else(|| {
                expected_scan
                    .labels
                    .iter()
                    .position(|occurrence| error.message.contains(&occurrence.list_path))
            })
            .unwrap_or(usize::MAX)
    };
    let result_position = |error: &ValidationError| {
        first_message_label(&error.message)
            .and_then(|label| {
                result_scan
                    .labels
                    .iter()
                    .position(|occurrence| occurrence.label == label)
            })
            .or_else(|| {
                result_scan
                    .unlabeled_statements
                    .iter()
                    .position(|path| error.message.contains(path))
            })
            .unwrap_or(usize::MAX)
    };
    let mut indexed = errors.drain(..).enumerate().collect::<Vec<_>>();
    indexed.sort_by_key(|(original_position, error)| {
        let (precedence, structural_position) = match error.code.as_str() {
            "malformed_label" | "misplaced_label" => (0, *original_position),
            "nested_label_repetition" => {
                let expected = expected_position(error);
                (
                    1,
                    if expected == usize::MAX {
                        expected_scan
                            .labels
                            .len()
                            .saturating_add(result_position(error))
                    } else {
                        expected
                    },
                )
            }
            "nonconsecutive_label" => {
                let expected = expected_position(error);
                (
                    2,
                    if expected == usize::MAX {
                        expected_scan
                            .labels
                            .len()
                            .saturating_add(result_position(error))
                    } else {
                        expected
                    },
                )
            }
            "label_order_mismatch" => (3, expected_position(error)),
            "missing_label" => (4, expected_position(error)),
            "unexpected_label" => (5, result_position(error)),
            "unlabeled_group_statement" => (6, result_position(error)),
            _ => (7, *original_position),
        };
        (precedence, structural_position, *original_position)
    });
    errors.extend(indexed.into_iter().map(|(_, error)| error));
}

enum ScopedTempProblem {
    Unresolved {
        name: String,
        reference_label: Option<u32>,
    },
    OutsideGroup {
        name: String,
        declaration_label: Option<u32>,
        reference_label: Option<u32>,
    },
}

struct LexicalTempScanner<'a> {
    existing_names: &'a HashSet<String>,
    reliable_declarations: &'a HashMap<&'a str, Option<u32>>,
    discarded_declarations: &'a HashSet<&'a str>,
    unreliable_names: &'a HashSet<&'a str>,
    scopes: Vec<HashSet<String>>,
    current_label: Option<u32>,
    unresolved: Vec<ScopedTempProblem>,
    outside_group: Vec<ScopedTempProblem>,
}

impl LexicalTempScanner<'_> {
    fn activate_pattern(&mut self, pat: &Pat) {
        let mut bindings = vec![];
        collect_pattern_bindings(pat, "root", &mut bindings);
        for binding in bindings {
            if !binding.constructor_like
                && (self
                    .reliable_declarations
                    .contains_key(binding.name.as_str())
                    || self.existing_names.contains(binding.name.as_str()))
            {
                self.scopes.last_mut().unwrap().insert(binding.name);
            }
        }
    }

    fn visit_scoped_block(&mut self, block: &rustc_ast::Block, pat: Option<&Pat>) {
        self.scopes.push(HashSet::new());
        if let Some(pat) = pat {
            self.activate_pattern(pat);
        }
        for statement in &block.stmts {
            self.visit_stmt(statement);
        }
        self.scopes.pop();
    }

    fn is_active(&self, name: &str) -> bool {
        self.scopes.iter().rev().any(|scope| scope.contains(name))
    }
}

impl<'ast> Visitor<'ast> for LexicalTempScanner<'_> {
    fn visit_block(&mut self, block: &'ast rustc_ast::Block) {
        self.visit_scoped_block(block, None);
    }

    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        let previous_label = self.current_label;
        if let Some(label) = stmt_label(stmt) {
            self.current_label = Some(label);
        }
        match &stmt.kind {
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
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => self.visit_expr(expr),
            StmtKind::MacCall(_) | StmtKind::Empty => {}
        }
        self.current_label = previous_label;
    }

    fn visit_expr(&mut self, expr: &'ast Expr) {
        match &expr.kind {
            ExprKind::If(condition, then_block, else_expr) => {
                if let ExprKind::Let(pat, value, ..) = &condition.kind {
                    self.visit_expr(value);
                    self.visit_scoped_block(then_block, Some(pat));
                } else {
                    self.visit_expr(condition);
                    self.visit_block(then_block);
                }
                if let Some(else_expr) = else_expr {
                    self.visit_expr(else_expr);
                }
            }
            ExprKind::While(condition, body, _) => {
                if let ExprKind::Let(pat, value, ..) = &condition.kind {
                    self.visit_expr(value);
                    self.visit_scoped_block(body, Some(pat));
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
                if !is_temp_name(&name) || self.unreliable_names.contains(name.as_str()) {
                    return;
                }
                let declaration_label = self.reliable_declarations.get(name.as_str()).copied();
                if declaration_label.is_none() && !self.existing_names.contains(name.as_str()) {
                    self.unresolved.push(ScopedTempProblem::Unresolved {
                        name,
                        reference_label: self.current_label,
                    });
                    return;
                }
                if self.discarded_declarations.contains(name.as_str()) {
                    self.outside_group.push(ScopedTempProblem::OutsideGroup {
                        name,
                        declaration_label: declaration_label.flatten(),
                        reference_label: self.current_label,
                    });
                    return;
                }
                if !self.is_active(&name) {
                    self.unresolved.push(ScopedTempProblem::Unresolved {
                        name,
                        reference_label: self.current_label,
                    });
                } else if declaration_label.is_some()
                    && declaration_label.flatten() != self.current_label
                {
                    self.outside_group.push(ScopedTempProblem::OutsideGroup {
                        name,
                        declaration_label: declaration_label.flatten(),
                        reference_label: self.current_label,
                    });
                }
            }
            ExprKind::MacCall(_) => {}
            _ => visit::walk_expr(self, expr),
        }
    }
}

fn validate_temporaries(
    expected: &ParsedExpected,
    result: &Item,
    expected_scan: &BodyScanner,
    result_scan: &BodyScanner,
    returned_scan: &BodyScanner,
    errors: &mut Vec<ValidationError>,
) {
    let ItemKind::Fn(box expected_function) = &expected.item.kind else { unreachable!() };
    let mut expected_names = expected_scan
        .bindings
        .iter()
        .map(|binding| binding.name.clone())
        .collect::<HashSet<_>>();
    expected_names.extend(
        expected_function
            .sig
            .decl
            .inputs
            .iter()
            .filter_map(|parameter| simple_pattern_name(&parameter.pat).map(str::to_owned)),
    );
    let generated = result_scan
        .bindings
        .iter()
        .filter(|binding| {
            is_temp_name(&binding.name) && !expected_names.contains(binding.name.as_str())
        })
        .collect::<Vec<_>>();
    let mut counts = HashMap::<&str, usize>::new();
    let mut declaration_order = vec![];
    for binding in &generated {
        if !counts.contains_key(binding.name.as_str()) {
            declaration_order.push(binding.name.as_str());
        }
        *counts.entry(&binding.name).or_default() += 1;
    }
    for name in &declaration_order {
        let count = counts[name];
        if count > 1 {
            errors.push(error(
                "duplicate_generated_temporary",
                function_message(
                    expected,
                    format!(
                        "generated temporary `{name}` is declared {count} times; generated names must be unique and may not be shadowed"
                    ),
                ),
            ));
        }
    }
    let unreliable_names = counts
        .iter()
        .filter_map(|(name, count)| (*count > 1).then_some(*name))
        .collect::<HashSet<_>>();
    let reliable_declarations = generated
        .iter()
        .filter(|binding| !unreliable_names.contains(binding.name.as_str()))
        .map(|binding| (binding.name.as_str(), binding.label))
        .collect::<HashMap<_, _>>();
    let discarded_declarations = returned_scan
        .bindings
        .iter()
        .filter(|binding| {
            is_temp_name(&binding.name)
                && !expected_names.contains(binding.name.as_str())
                && !reliable_declarations.contains_key(binding.name.as_str())
        })
        .map(|binding| binding.name.as_str())
        .collect::<HashSet<_>>();
    let returned_declarations = returned_scan
        .bindings
        .iter()
        .filter(|binding| discarded_declarations.contains(binding.name.as_str()))
        .map(|binding| (binding.name.as_str(), binding.label));
    let reliable_declarations = reliable_declarations
        .into_iter()
        .chain(returned_declarations)
        .collect::<HashMap<_, _>>();
    let ItemKind::Fn(box result_function) = &result.kind else { unreachable!() };
    let mut scanner = LexicalTempScanner {
        existing_names: &expected_names,
        reliable_declarations: &reliable_declarations,
        discarded_declarations: &discarded_declarations,
        unreliable_names: &unreliable_names,
        scopes: vec![],
        current_label: None,
        unresolved: vec![],
        outside_group: vec![],
    };
    scanner.scopes.push(HashSet::new());
    for parameter in &result_function.sig.decl.inputs {
        scanner.activate_pattern(&parameter.pat);
    }
    for statement in &result_function.body.as_ref().unwrap().stmts {
        scanner.visit_stmt(statement);
    }
    scanner.scopes.pop();
    for problem in scanner.unresolved {
        let ScopedTempProblem::Unresolved {
            name,
            reference_label,
        } = problem
        else {
            unreachable!()
        };
        errors.push(error(
            "unresolved_generated_temporary",
            function_message(
                expected,
                format!(
                    "generated-looking identifier `{name}`{} has no generated declaration in lexical scope; declare it before the reference in the same expansion group or remove the reference",
                    label_context(reference_label)
                ),
            ),
        ));
    }
    for problem in scanner.outside_group {
        let ScopedTempProblem::OutsideGroup {
            name,
            declaration_label,
            reference_label,
        } = problem
        else {
            unreachable!()
        };
        errors.push(error(
            "temporary_outside_expansion_group",
            function_message(
                expected,
                format!(
                    "temporary `{name}` is declared{} but referenced{}; keep every reference inside its declaration expansion group",
                    label_context(declaration_label),
                    label_context(reference_label)
                ),
            ),
        ));
    }
    for occurrence in &result_scan.macro_temporaries {
        if expected_names.contains(occurrence.name.as_str()) {
            continue;
        }
        errors.push(error(
            "temporary_in_macro",
            function_message(
                expected,
                format!(
                    "temporary identifier `{}` occurs inside macro tokens{}; move that use into ordinary Rust syntax",
                    occurrence.name,
                    label_context(occurrence.label)
                ),
            ),
        ));
    }
    let _ = result;
}

#[cfg(test)]
mod tests;
