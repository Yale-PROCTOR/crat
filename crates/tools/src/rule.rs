use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};

mod markdown;

pub use markdown::rule_document_to_markdown;

use crate::{
    AdtKind, BinaryOperator, BindingMutability, BorrowKind, ByRefKind, Expression,
    OBSERVATION_SCHEMA_VERSION, Observation, ObservationDocument, RangeLimits, RawMutability,
    RefMutability, TypeTree, UnaryOperator,
};

pub const RULE_SCHEMA_VERSION: u64 = 1;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocumentError {
    pub message: String,
}

impl std::fmt::Display for DocumentError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for DocumentError {}

fn invalid(message: impl Into<String>) -> DocumentError {
    DocumentError {
        message: message.into(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RuleDocument {
    pub schema_version: u64,
    pub rules: Vec<Rule>,
}

impl Default for RuleDocument {
    fn default() -> Self {
        Self {
            schema_version: RULE_SCHEMA_VERSION,
            rules: vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Rule {
    pub source_pattern: RuleExpression,
    pub target_pattern: RuleExpression,
    pub pointer_anchors: Vec<RulePointerAnchor>,
    pub lhs: bool,
    pub source_type: RuleTypeTree,
    pub source_adjusted_type: RuleTypeTree,
    pub target_type: RuleTypeTree,
    pub target_adjusted_type: RuleTypeTree,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RulePointerAnchor {
    pub id: RuleVariable,
    pub source_type: RuleTypeTree,
    pub target_type: RuleTypeTree,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum VariableSort {
    Anchor,
    Binding,
    Function,
    Struct,
    Enum,
    Union,
    Field,
    Variant,
    Constant,
    Static,
    Method,
    Expression,
    IntegerMagnitude,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum RuleVariable {
    Variable { sort: VariableSort, index: u64 },
}

impl RuleVariable {
    pub fn new(sort: VariableSort, index: u64) -> Self {
        Self::Variable { sort, index }
    }

    pub fn sort(&self) -> VariableSort {
        match self {
            Self::Variable { sort, .. } => *sort,
        }
    }

    pub fn index(&self) -> u64 {
        match self {
            Self::Variable { index, .. } => *index,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum RuleTypeTree {
    Primitive {
        name: String,
    },
    Slice {
        element: Box<RuleTypeTree>,
    },
    Array {
        element: Box<RuleTypeTree>,
        length: u64,
    },
    RawPointer {
        mutability: RawMutability,
        pointee: Box<RuleTypeTree>,
    },
    Reference {
        mutability: RefMutability,
        pointee: Box<RuleTypeTree>,
    },
    Tuple {
        elements: Vec<RuleTypeTree>,
    },
    Adt {
        adt_kind: AdtKind,
        identity: RuleAdtIdentity,
        arguments: Vec<RuleTypeTree>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum RuleAdtIdentity {
    Variable {
        sort: VariableSort,
        index: u64,
    },
    External {
        #[serde(rename = "crate")]
        crate_name: String,
        path: Vec<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum RuleMemberIdentity {
    External {
        #[serde(rename = "crate")]
        crate_name: String,
        path: Vec<String>,
    },
    Local {
        owner: RuleAdtIdentity,
        id: RuleVariable,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum RuleValueIdentity {
    Variable {
        sort: VariableSort,
        index: u64,
    },
    External {
        #[serde(rename = "crate")]
        crate_name: String,
        path: Vec<String>,
    },
    ForeignFunction {
        symbol: String,
    },
    ForeignStatic {
        symbol: String,
    },
    Constructor {
        adt: RuleAdtIdentity,
        variant: Option<RuleMemberIdentity>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum RuleIntegerMagnitude {
    Fixed(String),
    Variable(RuleVariable),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum RuleLiteral {
    Bool {
        value: bool,
    },
    Char {
        value: String,
    },
    Byte {
        value: u8,
    },
    String {
        value: String,
    },
    ByteString {
        value: Vec<u8>,
    },
    CString {
        value: Vec<u8>,
    },
    Integer {
        value: RuleIntegerMagnitude,
        #[serde(rename = "type")]
        ty: String,
    },
    Float {
        bits: String,
        #[serde(rename = "type")]
        ty: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum RuleExpression {
    Variable {
        sort: VariableSort,
        index: u64,
    },
    Array {
        elements: Vec<RuleExpression>,
    },
    Call {
        callee: Box<RuleExpression>,
        arguments: Vec<RuleExpression>,
    },
    MethodCall {
        receiver: Box<RuleExpression>,
        method: RuleValueIdentity,
        arguments: Vec<RuleExpression>,
    },
    Tuple {
        elements: Vec<RuleExpression>,
    },
    Binary {
        operator: BinaryOperator,
        left: Box<RuleExpression>,
        right: Box<RuleExpression>,
    },
    Unary {
        operator: UnaryOperator,
        operand: Box<RuleExpression>,
    },
    Literal {
        value: RuleLiteral,
    },
    Cast {
        expression: Box<RuleExpression>,
        #[serde(rename = "type")]
        ty: RuleTypeTree,
    },
    If {
        condition: Box<RuleExpression>,
        then: RuleBlock,
        #[serde(rename = "else")]
        else_expression: Option<Box<RuleExpression>>,
    },
    While {
        condition: Box<RuleExpression>,
        body: RuleBlock,
    },
    Loop {
        body: RuleBlock,
    },
    Assign {
        left: Box<RuleExpression>,
        right: Box<RuleExpression>,
    },
    AssignOp {
        operator: BinaryOperator,
        left: Box<RuleExpression>,
        right: Box<RuleExpression>,
    },
    Field {
        base: Box<RuleExpression>,
        field: RuleMemberIdentity,
    },
    Index {
        base: Box<RuleExpression>,
        index: Box<RuleExpression>,
    },
    Range {
        start: Option<Box<RuleExpression>>,
        end: Option<Box<RuleExpression>>,
        limits: RangeLimits,
    },
    Path {
        value: RuleValueIdentity,
    },
    AddressOf {
        borrow: BorrowKind,
        mutability: RawMutability,
        expression: Box<RuleExpression>,
    },
    Break {
        value: Option<Box<RuleExpression>>,
    },
    Continue,
    Return {
        value: Option<Box<RuleExpression>>,
    },
    Struct {
        adt: RuleAdtIdentity,
        variant: Option<RuleMemberIdentity>,
        fields: Vec<RuleStructField>,
        rest: Option<Box<RuleExpression>>,
    },
    Repeat {
        value: Box<RuleExpression>,
        count: Box<RuleExpression>,
    },
    Block {
        block: RuleBlock,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RuleBlock {
    pub statements: Vec<RuleStatement>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum RuleStatement {
    Let {
        pattern: RulePattern,
        #[serde(rename = "type")]
        ty: Option<RuleTypeTree>,
        initializer: Option<RuleExpression>,
    },
    Expression {
        expression: RuleExpression,
        semicolon: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum RulePattern {
    Binding {
        id: RuleVariable,
        mutability: BindingMutability,
        by_ref: ByRefKind,
    },
    Wildcard,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RuleStructField {
    pub field: RuleMemberIdentity,
    pub value: RuleExpression,
}

pub fn observation_document_from_json(text: &str) -> Result<ObservationDocument, DocumentError> {
    let document: ObservationDocument = serde_json::from_str(text)
        .map_err(|error| invalid(format!("observation JSON decode failure: {error}")))?;
    validate_observation_document(&document)?;
    Ok(document)
}

pub fn observation_document_to_json(
    document: &ObservationDocument,
) -> Result<String, DocumentError> {
    validate_observation_document(document)?;
    pretty_json(document)
}

pub fn rule_document_from_json(text: &str) -> Result<RuleDocument, DocumentError> {
    let document: RuleDocument = serde_json::from_str(text)
        .map_err(|error| invalid(format!("rule JSON decode failure: {error}")))?;
    validate_rule_document(&document)?;
    Ok(document)
}

pub fn rule_document_to_json(document: &RuleDocument) -> Result<String, DocumentError> {
    validate_rule_document(document)?;
    pretty_json(document)
}

fn pretty_json<T: Serialize>(value: &T) -> Result<String, DocumentError> {
    let mut result = serde_json::to_string_pretty(value)
        .map_err(|error| invalid(format!("JSON serialization failed: {error}")))?;
    result.push('\n');
    Ok(result)
}

pub fn merge_observation_documents(
    documents: &[ObservationDocument],
) -> Result<ObservationDocument, DocumentError> {
    let mut observations = vec![];
    for document in documents {
        validate_observation_document(document)?;
        observations.extend(document.observations.iter().cloned());
    }
    Ok(ObservationDocument {
        schema_version: OBSERVATION_SCHEMA_VERSION,
        observations,
    })
}

const PRIMITIVES: &[&str] = &[
    "bool", "char", "str", "never", "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32",
    "u64", "u128", "usize", "f16", "f32", "f64", "f128",
];

fn parse_local_id(value: &str) -> Option<(&str, u64)> {
    let body = value.strip_prefix('<')?.strip_suffix('>')?;
    let split = body.find(|character: char| character.is_ascii_digit())?;
    let (prefix, digits) = body.split_at(split);
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let index = digits.parse().ok()?;
    matches!(
        prefix,
        "id" | "fn"
            | "struct"
            | "enum"
            | "union"
            | "field"
            | "variant"
            | "const"
            | "static"
            | "method"
    )
    .then_some((prefix, index))
}

fn expect_local_id(value: &str, allowed: &[&str], where_: &str) -> Result<(), DocumentError> {
    match parse_local_id(value) {
        Some((prefix, _)) if allowed.contains(&prefix) => Ok(()),
        _ => Err(invalid(format!(
            "{where_} has an invalid anonymized identity"
        ))),
    }
}

fn validate_external(crate_name: &str, path: &[String], where_: &str) -> Result<(), DocumentError> {
    if crate_name.is_empty() || path.is_empty() || path.iter().any(String::is_empty) {
        return Err(invalid(format!(
            "{where_} must name a nonempty external path"
        )));
    }
    Ok(())
}

fn validate_observation_document(document: &ObservationDocument) -> Result<(), DocumentError> {
    if document.schema_version != OBSERVATION_SCHEMA_VERSION {
        return Err(invalid(format!(
            "unsupported observation schema_version {}",
            document.schema_version
        )));
    }
    for (index, observation) in document.observations.iter().enumerate() {
        validate_observation(observation, &format!("observations[{index}]"))?;
    }
    Ok(())
}

fn validate_observation(observation: &Observation, where_: &str) -> Result<(), DocumentError> {
    validate_expression(
        &observation.source_expression,
        &format!("{where_}.source_expression"),
    )?;
    validate_expression(
        &observation.target_expression,
        &format!("{where_}.target_expression"),
    )?;
    if observation.pointer_anchors.is_empty() {
        return Err(invalid(format!(
            "{where_}.pointer_anchors must be nonempty"
        )));
    }
    let mut anchors = HashSet::new();
    for (index, anchor) in observation.pointer_anchors.iter().enumerate() {
        let anchor_where = format!("{where_}.pointer_anchors[{index}]");
        expect_local_id(&anchor.id, &["id"], &format!("{anchor_where}.id"))?;
        if !anchors.insert(anchor.id.as_str()) {
            return Err(invalid(format!(
                "{where_}.pointer_anchors contains a duplicate ID"
            )));
        }
        if !matches!(anchor.source_type, TypeTree::RawPointer { .. }) {
            return Err(invalid(format!(
                "{anchor_where}.source_type must be a raw pointer"
            )));
        }
        validate_type(&anchor.source_type, &format!("{anchor_where}.source_type"))?;
        validate_type(&anchor.target_type, &format!("{anchor_where}.target_type"))?;
    }
    for (name, ty) in [
        ("source_type", &observation.source_type),
        ("source_adjusted_type", &observation.source_adjusted_type),
        ("target_type", &observation.target_type),
        ("target_adjusted_type", &observation.target_adjusted_type),
    ] {
        validate_type(ty, &format!("{where_}.{name}"))?;
    }

    let mut all_ids = serialized_local_ids(&observation.source_expression)?;
    all_ids.extend(serialized_local_ids(&observation.target_expression)?);
    for anchor in &observation.pointer_anchors {
        all_ids.extend(serialized_local_ids(anchor)?);
    }
    for ty in [
        &observation.source_type,
        &observation.source_adjusted_type,
        &observation.target_type,
        &observation.target_adjusted_type,
    ] {
        all_ids.extend(serialized_local_ids(ty)?);
    }
    for prefix in all_ids
        .iter()
        .map(|(prefix, _, _)| *prefix)
        .collect::<BTreeSet<_>>()
    {
        let mut first = vec![];
        for (candidate, index, _) in &all_ids {
            if *candidate == prefix && !first.contains(index) {
                first.push(*index);
            }
        }
        if first.iter().copied().ne(0..first.len() as u64) {
            return Err(invalid(format!(
                "{where_} anonymized {prefix} IDs are not canonical"
            )));
        }
    }
    let source_ids = serialized_local_ids(&observation.source_expression)?
        .into_iter()
        .map(|(_, _, text)| text)
        .collect::<HashSet<_>>();
    for (prefix, _, text) in serialized_local_ids(&observation.target_expression)? {
        if matches!(prefix, "id" | "fn") && !source_ids.contains(&text) {
            return Err(invalid(format!(
                "{where_}.target_expression contains a target-only identity"
            )));
        }
    }
    let source_bindings = serialized_local_ids(&observation.source_expression)?
        .into_iter()
        .filter(|(prefix, _, _)| *prefix == "id")
        .map(|(_, _, text)| text)
        .fold(Vec::new(), |mut values, value| {
            if !values.contains(&value) {
                values.push(value);
            }
            values
        });
    let mut previous = None;
    for anchor in &observation.pointer_anchors {
        let position = source_bindings
            .iter()
            .position(|id| id == &anchor.id)
            .ok_or_else(|| invalid(format!("{where_}.pointer_anchors contains an unused ID")))?;
        if previous.is_some_and(|previous| previous >= position) {
            return Err(invalid(format!(
                "{where_}.pointer_anchors are not in source occurrence order"
            )));
        }
        previous = Some(position);
    }
    Ok(())
}

fn serialized_local_ids<T: Serialize>(
    value: &T,
) -> Result<Vec<(&'static str, u64, String)>, DocumentError> {
    let value = serde_json::to_value(value).map_err(|error| invalid(error.to_string()))?;
    let mut result = vec![];
    fn collect(value: &Value, result: &mut Vec<(&'static str, u64, String)>) {
        match value {
            Value::String(candidate) => {
                let Some((prefix, index)) = parse_local_id(candidate) else { return };
                let prefix = match prefix {
                    "id" => "id",
                    "fn" => "fn",
                    "struct" => "struct",
                    "enum" => "enum",
                    "union" => "union",
                    "field" => "field",
                    "variant" => "variant",
                    "const" => "const",
                    "static" => "static",
                    "method" => "method",
                    _ => unreachable!(),
                };
                result.push((prefix, index, candidate.to_owned()));
            }
            Value::Array(values) => values.iter().for_each(|value| collect(value, result)),
            Value::Object(object) => canonical_object_keys(object)
                .into_iter()
                .for_each(|key| collect(&object[key], result)),
            _ => {}
        }
    }
    collect(&value, &mut result);
    Ok(result)
}

fn validate_type(ty: &TypeTree, where_: &str) -> Result<(), DocumentError> {
    match ty {
        TypeTree::Primitive { name } if !PRIMITIVES.contains(&name.as_str()) => {
            Err(invalid(format!("{where_} has an unknown primitive")))
        }
        TypeTree::Primitive { .. } => Ok(()),
        TypeTree::Slice { element } | TypeTree::Array { element, .. } => {
            validate_type(element, where_)
        }
        TypeTree::RawPointer { pointee, .. } | TypeTree::Reference { pointee, .. } => {
            validate_type(pointee, where_)
        }
        TypeTree::Tuple { elements } => elements
            .iter()
            .try_for_each(|element| validate_type(element, where_)),
        TypeTree::Adt {
            adt_kind,
            identity,
            arguments,
        } => {
            match identity {
                crate::AdtIdentity::External { crate_name, path } => {
                    validate_external(crate_name, path, where_)?
                }
                crate::AdtIdentity::Local { id } => {
                    let prefix = match adt_kind {
                        AdtKind::Struct => "struct",
                        AdtKind::Enum => "enum",
                        AdtKind::Union => "union",
                    };
                    expect_local_id(id, &[prefix], where_)?;
                }
            }
            arguments
                .iter()
                .try_for_each(|argument| validate_type(argument, where_))
        }
    }
}

fn validate_adt(identity: &crate::AdtIdentity, where_: &str) -> Result<(), DocumentError> {
    match identity {
        crate::AdtIdentity::External { crate_name, path } => {
            validate_external(crate_name, path, where_)
        }
        crate::AdtIdentity::Local { id } => {
            expect_local_id(id, &["struct", "enum", "union"], where_)
        }
    }
}

fn validate_member(identity: &crate::FieldIdentity, where_: &str) -> Result<(), DocumentError> {
    match identity {
        crate::FieldIdentity::External { crate_name, path } => {
            validate_external(crate_name, path, where_)
        }
        crate::FieldIdentity::Local { owner, id } => {
            validate_adt(owner, where_)?;
            expect_local_id(id, &["field"], where_)
        }
    }
}

fn validate_variant(identity: &crate::VariantIdentity, where_: &str) -> Result<(), DocumentError> {
    match identity {
        crate::VariantIdentity::External { crate_name, path } => {
            validate_external(crate_name, path, where_)
        }
        crate::VariantIdentity::Local { owner, id } => {
            validate_adt(owner, where_)?;
            expect_local_id(id, &["variant"], where_)
        }
    }
}

fn validate_value(identity: &crate::ValueIdentity, where_: &str) -> Result<(), DocumentError> {
    match identity {
        crate::ValueIdentity::Binding { id } => expect_local_id(id, &["id"], where_),
        crate::ValueIdentity::Function { id } => expect_local_id(id, &["fn"], where_),
        crate::ValueIdentity::Constant { id } => expect_local_id(id, &["const"], where_),
        crate::ValueIdentity::Static { id } => expect_local_id(id, &["static"], where_),
        crate::ValueIdentity::Method { id } => expect_local_id(id, &["method"], where_),
        crate::ValueIdentity::External { crate_name, path } => {
            validate_external(crate_name, path, where_)
        }
        crate::ValueIdentity::ForeignFunction { symbol }
        | crate::ValueIdentity::ForeignStatic { symbol } => {
            if symbol.is_empty() {
                Err(invalid(format!("{where_} has an empty foreign symbol")))
            } else {
                Ok(())
            }
        }
        crate::ValueIdentity::Constructor { adt, variant } => {
            validate_adt(adt, where_)?;
            if let Some(variant) = variant {
                validate_variant(variant, where_)?;
            }
            Ok(())
        }
    }
}

fn validate_literal(literal: &crate::Literal, where_: &str) -> Result<(), DocumentError> {
    match literal {
        crate::Literal::Integer { value, ty } => {
            if value.is_empty()
                || !value.bytes().all(|byte| byte.is_ascii_digit())
                || !PRIMITIVES.contains(&ty.as_str())
                || ty.starts_with('f')
                || matches!(ty.as_str(), "bool" | "char" | "str" | "never")
            {
                Err(invalid(format!("{where_} has an invalid integer literal")))
            } else {
                Ok(())
            }
        }
        crate::Literal::Float { bits, ty } => {
            let width = match ty.as_str() {
                "f16" => 4,
                "f32" => 8,
                "f64" => 16,
                "f128" => 32,
                _ => 0,
            };
            if bits.len() != width
                || !bits
                    .bytes()
                    .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
            {
                Err(invalid(format!("{where_} has invalid float bits")))
            } else {
                Ok(())
            }
        }
        _ => Ok(()),
    }
}

fn validate_expression(expression: &Expression, where_: &str) -> Result<(), DocumentError> {
    match expression {
        Expression::Array { elements } | Expression::Tuple { elements } => elements
            .iter()
            .try_for_each(|value| validate_expression(value, where_)),
        Expression::Call { callee, arguments } => {
            validate_expression(callee, where_)?;
            arguments
                .iter()
                .try_for_each(|value| validate_expression(value, where_))
        }
        Expression::MethodCall {
            receiver,
            method,
            arguments,
        } => {
            validate_expression(receiver, where_)?;
            validate_value(method, where_)?;
            arguments
                .iter()
                .try_for_each(|value| validate_expression(value, where_))
        }
        Expression::Binary { left, right, .. }
        | Expression::Assign { left, right }
        | Expression::AssignOp { left, right, .. } => {
            validate_expression(left, where_)?;
            validate_expression(right, where_)
        }
        Expression::Unary { operand, .. } => validate_expression(operand, where_),
        Expression::Literal { value } => validate_literal(value, where_),
        Expression::Cast { expression, ty } => {
            validate_expression(expression, where_)?;
            validate_type(ty, where_)
        }
        Expression::If {
            condition,
            then,
            else_expression,
        } => {
            validate_expression(condition, where_)?;
            validate_block(then, where_)?;
            if let Some(value) = else_expression {
                validate_expression(value, where_)?;
            }
            Ok(())
        }
        Expression::While { condition, body } => {
            validate_expression(condition, where_)?;
            validate_block(body, where_)
        }
        Expression::Loop { body } | Expression::Block { block: body } => {
            validate_block(body, where_)
        }
        Expression::Field { base, field } => {
            validate_expression(base, where_)?;
            validate_member(field, where_)
        }
        Expression::Index { base, index } => {
            validate_expression(base, where_)?;
            validate_expression(index, where_)
        }
        Expression::Range { start, end, .. } => {
            if let Some(value) = start {
                validate_expression(value, where_)?;
            }
            if let Some(value) = end {
                validate_expression(value, where_)?;
            }
            Ok(())
        }
        Expression::Path { value } => validate_value(value, where_),
        Expression::AddressOf { expression, .. } => validate_expression(expression, where_),
        Expression::Break { value } | Expression::Return { value } => {
            if let Some(value) = value {
                validate_expression(value, where_)?;
            }
            Ok(())
        }
        Expression::Continue => Ok(()),
        Expression::Struct {
            adt,
            variant,
            fields,
            rest,
        } => {
            validate_adt(adt, where_)?;
            if let Some(variant) = variant {
                validate_variant(variant, where_)?;
            }
            let mut seen = HashSet::new();
            for field in fields {
                validate_member(&field.field, where_)?;
                let key = serde_json::to_string(&field.field)
                    .map_err(|error| invalid(error.to_string()))?;
                if !seen.insert(key) {
                    return Err(invalid(format!(
                        "{where_} contains a duplicate struct field"
                    )));
                }
                validate_expression(&field.value, where_)?;
            }
            if let Some(value) = rest {
                validate_expression(value, where_)?;
            }
            Ok(())
        }
        Expression::Repeat { value, count } => {
            validate_expression(value, where_)?;
            validate_expression(count, where_)
        }
    }
}

fn validate_block(block: &crate::Block, where_: &str) -> Result<(), DocumentError> {
    for statement in &block.statements {
        match statement {
            crate::Statement::Let {
                pattern,
                ty,
                initializer,
            } => {
                if let crate::Pattern::Binding { id, .. } = pattern {
                    expect_local_id(id, &["id"], where_)?;
                }
                if let Some(ty) = ty {
                    validate_type(ty, where_)?;
                }
                if let Some(value) = initializer {
                    validate_expression(value, where_)?;
                }
            }
            crate::Statement::Expression { expression, .. } => {
                validate_expression(expression, where_)?
            }
        }
    }
    Ok(())
}

fn validate_rule_document(document: &RuleDocument) -> Result<(), DocumentError> {
    if document.schema_version != RULE_SCHEMA_VERSION {
        return Err(invalid(format!(
            "unsupported rule schema_version {}",
            document.schema_version
        )));
    }
    for (index, rule) in document.rules.iter().enumerate() {
        validate_rule(rule, &format!("rules[{index}]"))?;
    }
    Ok(())
}

fn expect_sort(
    variable: &RuleVariable,
    allowed: &[VariableSort],
    where_: &str,
) -> Result<(), DocumentError> {
    if allowed.contains(&variable.sort()) {
        Ok(())
    } else {
        Err(invalid(format!("{where_} has an invalid variable sort")))
    }
}

fn validate_rule(rule: &Rule, where_: &str) -> Result<(), DocumentError> {
    if rule.pointer_anchors.is_empty() {
        return Err(invalid(format!(
            "{where_}.pointer_anchors must be nonempty"
        )));
    }
    let mut anchors = HashSet::new();
    for anchor in &rule.pointer_anchors {
        expect_sort(&anchor.id, &[VariableSort::Anchor], where_)?;
        if !anchors.insert((anchor.id.sort(), anchor.id.index())) {
            return Err(invalid(format!(
                "{where_}.pointer_anchors contains a duplicate variable"
            )));
        }
        if !matches!(anchor.source_type, RuleTypeTree::RawPointer { .. }) {
            return Err(invalid(format!(
                "{where_}.pointer_anchors source type must be a raw pointer"
            )));
        }
        validate_rule_type(&anchor.source_type, where_)?;
        validate_rule_type(&anchor.target_type, where_)?;
    }
    for ty in [
        &rule.source_type,
        &rule.source_adjusted_type,
        &rule.target_type,
        &rule.target_adjusted_type,
    ] {
        validate_rule_type(ty, where_)?;
    }
    validate_rule_expression(&rule.source_pattern, where_)?;
    validate_rule_expression(&rule.target_pattern, where_)?;

    let mut seen = HashSet::new();
    let mut next = HashMap::<VariableSort, u64>::new();
    let mut visit = |value: &Value, target: bool| -> Result<(), DocumentError> {
        visit_variables(value, &mut |sort, index| {
            let key = (sort, index);
            if target && !seen.contains(&key) {
                return Err(invalid(format!(
                    "{where_}.target_pattern contains an unavailable variable"
                )));
            }
            if seen.insert(key) {
                let expected = next.entry(sort).or_default();
                if index != *expected {
                    return Err(invalid(format!(
                        "{where_} variable indices are not in canonical first-occurrence order"
                    )));
                }
                *expected += 1;
            }
            Ok(())
        })
    };
    for anchor in &rule.pointer_anchors {
        visit(
            &serde_json::to_value(&anchor.id).map_err(|error| invalid(error.to_string()))?,
            false,
        )?;
        visit(
            &serde_json::to_value(&anchor.source_type)
                .map_err(|error| invalid(error.to_string()))?,
            false,
        )?;
        visit(
            &serde_json::to_value(&anchor.target_type)
                .map_err(|error| invalid(error.to_string()))?,
            false,
        )?;
    }
    for ty in [
        &rule.source_type,
        &rule.source_adjusted_type,
        &rule.target_type,
        &rule.target_adjusted_type,
    ] {
        visit(
            &serde_json::to_value(ty).map_err(|error| invalid(error.to_string()))?,
            false,
        )?;
    }
    visit(
        &serde_json::to_value(&rule.source_pattern).map_err(|error| invalid(error.to_string()))?,
        false,
    )?;
    visit(
        &serde_json::to_value(&rule.target_pattern).map_err(|error| invalid(error.to_string()))?,
        true,
    )?;
    if seen
        .iter()
        .any(|(sort, index)| *sort == VariableSort::Anchor && !anchors.contains(&(*sort, *index)))
    {
        return Err(invalid(format!(
            "{where_} uses an undeclared anchor variable"
        )));
    }
    Ok(())
}

fn validate_rule_type(ty: &RuleTypeTree, where_: &str) -> Result<(), DocumentError> {
    match ty {
        RuleTypeTree::Primitive { name } => {
            if PRIMITIVES.contains(&name.as_str()) {
                Ok(())
            } else {
                Err(invalid(format!("{where_} has an unknown primitive")))
            }
        }
        RuleTypeTree::Slice { element } | RuleTypeTree::Array { element, .. } => {
            validate_rule_type(element, where_)
        }
        RuleTypeTree::RawPointer { pointee, .. } | RuleTypeTree::Reference { pointee, .. } => {
            validate_rule_type(pointee, where_)
        }
        RuleTypeTree::Tuple { elements } => elements
            .iter()
            .try_for_each(|element| validate_rule_type(element, where_)),
        RuleTypeTree::Adt {
            adt_kind,
            identity,
            arguments,
        } => {
            validate_rule_adt(identity, Some(*adt_kind), where_)?;
            arguments
                .iter()
                .try_for_each(|argument| validate_rule_type(argument, where_))
        }
    }
}

fn validate_rule_adt(
    identity: &RuleAdtIdentity,
    expected: Option<AdtKind>,
    where_: &str,
) -> Result<(), DocumentError> {
    match identity {
        RuleAdtIdentity::Variable { sort, .. } => {
            let allowed = match expected {
                Some(AdtKind::Struct) => vec![VariableSort::Struct],
                Some(AdtKind::Enum) => vec![VariableSort::Enum],
                Some(AdtKind::Union) => vec![VariableSort::Union],
                None => vec![
                    VariableSort::Struct,
                    VariableSort::Enum,
                    VariableSort::Union,
                ],
            };
            if allowed.contains(sort) {
                Ok(())
            } else {
                Err(invalid(format!(
                    "{where_} has an invalid ADT variable sort"
                )))
            }
        }
        RuleAdtIdentity::External { crate_name, path } => {
            validate_external(crate_name, path, where_)
        }
    }
}

fn validate_rule_member(
    identity: &RuleMemberIdentity,
    sort: VariableSort,
    where_: &str,
) -> Result<(), DocumentError> {
    match identity {
        RuleMemberIdentity::External { crate_name, path } => {
            validate_external(crate_name, path, where_)
        }
        RuleMemberIdentity::Local { owner, id } => {
            validate_rule_adt(owner, None, where_)?;
            expect_sort(id, &[sort], where_)
        }
    }
}

fn validate_rule_value(identity: &RuleValueIdentity, where_: &str) -> Result<(), DocumentError> {
    match identity {
        RuleValueIdentity::Variable {
            sort:
                VariableSort::Anchor
                | VariableSort::Binding
                | VariableSort::Function
                | VariableSort::Constant
                | VariableSort::Static
                | VariableSort::Method,
            ..
        } => Ok(()),
        RuleValueIdentity::Variable { .. } => Err(invalid(format!(
            "{where_} has an invalid value variable sort"
        ))),
        RuleValueIdentity::External { crate_name, path } => {
            validate_external(crate_name, path, where_)
        }
        RuleValueIdentity::ForeignFunction { symbol }
        | RuleValueIdentity::ForeignStatic { symbol } => {
            if symbol.is_empty() {
                Err(invalid(format!("{where_} has an empty foreign symbol")))
            } else {
                Ok(())
            }
        }
        RuleValueIdentity::Constructor { adt, variant } => {
            validate_rule_adt(adt, None, where_)?;
            if let Some(variant) = variant {
                validate_rule_member(variant, VariableSort::Variant, where_)?;
            }
            Ok(())
        }
    }
}

fn validate_rule_literal(literal: &RuleLiteral, where_: &str) -> Result<(), DocumentError> {
    match literal {
        RuleLiteral::Char { value } => {
            let mut characters = value.chars();
            if characters.next().is_some() && characters.next().is_none() {
                Ok(())
            } else {
                Err(invalid(format!(
                    "{where_} character literal must contain exactly one Unicode scalar"
                )))
            }
        }
        RuleLiteral::Integer { value, ty } => {
            match value {
                RuleIntegerMagnitude::Fixed(value)
                    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) =>
                {
                    return Err(invalid(format!(
                        "{where_} has an invalid integer magnitude"
                    )));
                }
                RuleIntegerMagnitude::Variable(variable) => {
                    expect_sort(variable, &[VariableSort::IntegerMagnitude], where_)?
                }
                _ => {}
            }
            if !PRIMITIVES.contains(&ty.as_str())
                || ty.starts_with('f')
                || matches!(ty.as_str(), "bool" | "char" | "str" | "never")
            {
                Err(invalid(format!("{where_} has an invalid integer type")))
            } else {
                Ok(())
            }
        }
        RuleLiteral::Float { bits, ty } => {
            let width = match ty.as_str() {
                "f16" => 4,
                "f32" => 8,
                "f64" => 16,
                "f128" => 32,
                _ => 0,
            };
            if bits.len() == width
                && bits
                    .bytes()
                    .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
            {
                Ok(())
            } else {
                Err(invalid(format!("{where_} has invalid float bits")))
            }
        }
        _ => Ok(()),
    }
}

fn validate_rule_expression(
    expression: &RuleExpression,
    where_: &str,
) -> Result<(), DocumentError> {
    match expression {
        RuleExpression::Variable {
            sort: VariableSort::Expression,
            ..
        } => Ok(()),
        RuleExpression::Variable { .. } => Err(invalid(format!(
            "{where_} has a non-expression variable in expression position"
        ))),
        RuleExpression::Array { elements } | RuleExpression::Tuple { elements } => elements
            .iter()
            .try_for_each(|value| validate_rule_expression(value, where_)),
        RuleExpression::Call { callee, arguments } => {
            validate_rule_expression(callee, where_)?;
            arguments
                .iter()
                .try_for_each(|value| validate_rule_expression(value, where_))
        }
        RuleExpression::MethodCall {
            receiver,
            method,
            arguments,
        } => {
            validate_rule_expression(receiver, where_)?;
            validate_rule_value(method, where_)?;
            arguments
                .iter()
                .try_for_each(|value| validate_rule_expression(value, where_))
        }
        RuleExpression::Binary { left, right, .. }
        | RuleExpression::Assign { left, right }
        | RuleExpression::AssignOp { left, right, .. } => {
            validate_rule_expression(left, where_)?;
            validate_rule_expression(right, where_)
        }
        RuleExpression::Unary { operand, .. } => validate_rule_expression(operand, where_),
        RuleExpression::Literal { value } => validate_rule_literal(value, where_),
        RuleExpression::Cast { expression, ty } => {
            validate_rule_expression(expression, where_)?;
            validate_rule_type(ty, where_)
        }
        RuleExpression::If {
            condition,
            then,
            else_expression,
        } => {
            validate_rule_expression(condition, where_)?;
            validate_rule_block(then, where_)?;
            if let Some(value) = else_expression {
                validate_rule_expression(value, where_)?;
            }
            Ok(())
        }
        RuleExpression::While { condition, body } => {
            validate_rule_expression(condition, where_)?;
            validate_rule_block(body, where_)
        }
        RuleExpression::Loop { body } | RuleExpression::Block { block: body } => {
            validate_rule_block(body, where_)
        }
        RuleExpression::Field { base, field } => {
            validate_rule_expression(base, where_)?;
            validate_rule_member(field, VariableSort::Field, where_)
        }
        RuleExpression::Index { base, index } => {
            validate_rule_expression(base, where_)?;
            validate_rule_expression(index, where_)
        }
        RuleExpression::Range { start, end, .. } => {
            if let Some(value) = start {
                validate_rule_expression(value, where_)?;
            }
            if let Some(value) = end {
                validate_rule_expression(value, where_)?;
            }
            Ok(())
        }
        RuleExpression::Path { value } => validate_rule_value(value, where_),
        RuleExpression::AddressOf { expression, .. } => {
            validate_rule_expression(expression, where_)
        }
        RuleExpression::Break { value } | RuleExpression::Return { value } => {
            if let Some(value) = value {
                validate_rule_expression(value, where_)?;
            }
            Ok(())
        }
        RuleExpression::Continue => Ok(()),
        RuleExpression::Struct {
            adt,
            variant,
            fields,
            rest,
        } => {
            validate_rule_adt(adt, None, where_)?;
            if let Some(variant) = variant {
                validate_rule_member(variant, VariableSort::Variant, where_)?;
            }
            let mut seen = HashSet::new();
            for field in fields {
                validate_rule_member(&field.field, VariableSort::Field, where_)?;
                let key = serde_json::to_string(&field.field)
                    .map_err(|error| invalid(error.to_string()))?;
                if !seen.insert(key) {
                    return Err(invalid(format!("{where_} contains a duplicate field")));
                }
                validate_rule_expression(&field.value, where_)?;
            }
            if let Some(value) = rest {
                validate_rule_expression(value, where_)?;
            }
            Ok(())
        }
        RuleExpression::Repeat { value, count } => {
            validate_rule_expression(value, where_)?;
            validate_rule_expression(count, where_)
        }
    }
}

fn validate_rule_block(block: &RuleBlock, where_: &str) -> Result<(), DocumentError> {
    for statement in &block.statements {
        match statement {
            RuleStatement::Let {
                pattern,
                ty,
                initializer,
            } => {
                if let RulePattern::Binding { id, .. } = pattern {
                    expect_sort(id, &[VariableSort::Anchor, VariableSort::Binding], where_)?;
                }
                if let Some(ty) = ty {
                    validate_rule_type(ty, where_)?;
                }
                if let Some(value) = initializer {
                    validate_rule_expression(value, where_)?;
                }
            }
            RuleStatement::Expression { expression, .. } => {
                validate_rule_expression(expression, where_)?
            }
        }
    }
    Ok(())
}

fn visit_variables(
    value: &Value,
    visit: &mut impl FnMut(VariableSort, u64) -> Result<(), DocumentError>,
) -> Result<(), DocumentError> {
    match value {
        Value::Object(object) if object.get("kind").and_then(Value::as_str) == Some("variable") => {
            let sort: VariableSort = serde_json::from_value(
                object
                    .get("sort")
                    .cloned()
                    .ok_or_else(|| invalid("variable has no sort"))?,
            )
            .map_err(|error| invalid(error.to_string()))?;
            let index = object
                .get("index")
                .and_then(Value::as_u64)
                .ok_or_else(|| invalid("variable has invalid index"))?;
            visit(sort, index)
        }
        Value::Object(object) => {
            for key in canonical_object_keys(object) {
                visit_variables(&object[key], visit)?;
            }
            Ok(())
        }
        Value::Array(values) => values
            .iter()
            .try_for_each(|value| visit_variables(value, visit)),
        _ => Ok(()),
    }
}

fn canonical_object_keys(object: &Map<String, Value>) -> Vec<&str> {
    let keys = object.keys().map(String::as_str).collect::<HashSet<_>>();
    let candidates: &[&[&str]] = &[
        &["kind", "sort", "index"],
        &["kind", "name"],
        &["kind", "element"],
        &["kind", "element", "length"],
        &["kind", "mutability", "pointee"],
        &["kind", "elements"],
        &["kind", "adt_kind", "identity", "arguments"],
        &["kind", "crate", "path"],
        &["kind", "symbol"],
        &["kind", "owner", "id"],
        &["kind", "adt", "variant"],
        &["kind", "callee", "arguments"],
        &["kind", "receiver", "method", "arguments"],
        &["kind", "operator", "left", "right"],
        &["kind", "operator", "operand"],
        &["kind", "value"],
        &["kind", "expression", "type"],
        &["kind", "left", "right"],
        &["kind", "base", "index"],
        &["kind", "base", "field"],
        &["kind", "start", "end", "limits"],
        &["kind", "condition", "then", "else"],
        &["kind", "condition", "body"],
        &["kind", "body"],
        &["kind", "adt", "variant", "fields", "rest"],
        &["field", "value"],
        &["kind", "borrow", "mutability", "expression"],
        &["kind"],
        &["kind", "value", "count"],
        &["kind", "block"],
        &["statements"],
        &["kind", "expression", "semicolon"],
        &["kind", "pattern", "type", "initializer"],
        &["kind", "id", "mutability", "by_ref"],
        &["kind", "value", "type"],
        &["kind", "bits", "type"],
        &["id", "source_type", "target_type"],
    ];
    if let Some(order) = candidates
        .iter()
        .find(|order| order.len() == keys.len() && order.iter().all(|key| keys.contains(key)))
    {
        return order.to_vec();
    }
    let mut result = object.keys().map(String::as_str).collect::<Vec<_>>();
    result.sort_unstable();
    result
}

fn variable_value(sort: VariableSort, index: u64) -> Value {
    serde_json::json!({"kind": "variable", "sort": sort, "index": index})
}

fn compact(value: &Value) -> String {
    serde_json::to_string(value).expect("JSON value serialization cannot fail")
}

fn value_object(entries: impl IntoIterator<Item = (&'static str, Value)>) -> Value {
    Value::Object(
        entries
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect(),
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PairRejection {
    Context,
    Source,
    DegenerateSource,
    TargetLookup,
    Carrier,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PairSynthesis {
    pub rule: Option<Rule>,
    pub rejection: Option<PairRejection>,
    pub substitutions: BTreeMap<(VariableSort, u64), (Value, Value)>,
}

#[derive(Clone)]
struct SynthesisState {
    counters: BTreeMap<VariableSort, u64>,
    disagreements: HashMap<(VariableSort, String, String), Value>,
    identities: HashMap<(VariableSort, String, String), Value>,
    substitutions: BTreeMap<(VariableSort, u64), (Value, Value)>,
    context_forward: HashMap<(VariableSort, String), String>,
    context_reverse: HashMap<(VariableSort, String), String>,
    anchor_pairs: HashMap<(String, String), Value>,
    left_anchors: HashSet<String>,
    right_anchors: HashSet<String>,
}

impl SynthesisState {
    fn new() -> Self {
        Self {
            counters: BTreeMap::new(),
            disagreements: HashMap::new(),
            identities: HashMap::new(),
            substitutions: BTreeMap::new(),
            context_forward: HashMap::new(),
            context_reverse: HashMap::new(),
            anchor_pairs: HashMap::new(),
            left_anchors: HashSet::new(),
            right_anchors: HashSet::new(),
        }
    }

    fn allocate(&mut self, sort: VariableSort, left: &Value, right: &Value) -> Value {
        let index = *self.counters.get(&sort).unwrap_or(&0);
        self.counters.insert(sort, index + 1);
        self.substitutions
            .insert((sort, index), (left.clone(), right.clone()));
        variable_value(sort, index)
    }

    fn disagreement(
        &mut self,
        sort: VariableSort,
        left: &Value,
        right: &Value,
        mode: Mode,
    ) -> Option<Value> {
        let key = (sort, compact(left), compact(right));
        if let Some(value) = self.disagreements.get(&key) {
            return Some(value.clone());
        }
        if mode == Mode::Target {
            return None;
        }
        let value = self.allocate(sort, left, right);
        self.disagreements.insert(key, value.clone());
        Some(value)
    }

    fn identity(
        &mut self,
        sort: VariableSort,
        left: &str,
        right: &str,
        mode: Mode,
    ) -> Option<Value> {
        if sort == VariableSort::Binding
            && (self.left_anchors.contains(left) || self.right_anchors.contains(right))
        {
            return self
                .anchor_pairs
                .get(&(left.to_owned(), right.to_owned()))
                .cloned();
        }
        let key = (sort, left.to_owned(), right.to_owned());
        if let Some(value) = self.identities.get(&key) {
            return Some(value.clone());
        }
        if mode == Mode::Target {
            return None;
        }
        let value = self.allocate(
            sort,
            &Value::String(left.to_owned()),
            &Value::String(right.to_owned()),
        );
        self.identities.insert(key, value.clone());
        Some(value)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Context,
    Source,
    Target,
}

enum Walk {
    Ok(Value),
    Generalize,
    IdentityConflict,
    Reject,
}

fn local_sort(value: &str) -> Option<VariableSort> {
    Some(match parse_local_id(value)?.0 {
        "id" => VariableSort::Binding,
        "fn" => VariableSort::Function,
        "struct" => VariableSort::Struct,
        "enum" => VariableSort::Enum,
        "union" => VariableSort::Union,
        "field" => VariableSort::Field,
        "variant" => VariableSort::Variant,
        "const" => VariableSort::Constant,
        "static" => VariableSort::Static,
        "method" => VariableSort::Method,
        _ => return None,
    })
}

fn local_identity(
    left: &Value,
    right: &Value,
    expected: VariableSort,
    state: &mut SynthesisState,
    mode: Mode,
) -> Walk {
    let (Some(left), Some(right)) = (left.as_str(), right.as_str()) else {
        return Walk::IdentityConflict;
    };
    if local_sort(left) != Some(expected) || local_sort(right) != Some(expected) {
        return Walk::IdentityConflict;
    }
    match state.identity(expected, left, right, mode) {
        Some(value) => Walk::Ok(value),
        None if mode == Mode::Target => Walk::Reject,
        None => Walk::IdentityConflict,
    }
}

fn adt_identity(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (Some(left_object), Some(right_object)) = (left.as_object(), right.as_object()) else {
        return Walk::IdentityConflict;
    };
    match (
        left_object.get("kind").and_then(Value::as_str),
        right_object.get("kind").and_then(Value::as_str),
    ) {
        (Some("local"), Some("local")) => {
            let (Some(left_id), Some(right_id)) = (left_object.get("id"), right_object.get("id"))
            else {
                return Walk::IdentityConflict;
            };
            let Some(sort) = left_id.as_str().and_then(local_sort) else {
                return Walk::IdentityConflict;
            };
            if !matches!(
                sort,
                VariableSort::Struct | VariableSort::Enum | VariableSort::Union
            ) || right_id.as_str().and_then(local_sort) != Some(sort)
            {
                return Walk::IdentityConflict;
            }
            local_identity(left_id, right_id, sort, state, mode)
        }
        (Some("external"), Some("external")) if left == right => Walk::Ok(left.clone()),
        _ => Walk::IdentityConflict,
    }
}

fn member_identity(
    left: &Value,
    right: &Value,
    sort: VariableSort,
    state: &mut SynthesisState,
    mode: Mode,
) -> Walk {
    let (Some(left_object), Some(right_object)) = (left.as_object(), right.as_object()) else {
        return Walk::IdentityConflict;
    };
    match (
        left_object.get("kind").and_then(Value::as_str),
        right_object.get("kind").and_then(Value::as_str),
    ) {
        (Some("local"), Some("local")) => {
            let owner = adt_identity(&left_object["owner"], &right_object["owner"], state, mode);
            let Walk::Ok(owner) = owner else { return owner };
            let member = local_identity(&left_object["id"], &right_object["id"], sort, state, mode);
            let Walk::Ok(member) = member else { return member };
            Walk::Ok(value_object([
                ("kind", Value::String("local".into())),
                ("owner", owner),
                ("id", member),
            ]))
        }
        (Some("external"), Some("external")) if left == right => Walk::Ok(left.clone()),
        _ => Walk::IdentityConflict,
    }
}

fn value_identity(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (Some(left_object), Some(right_object)) = (left.as_object(), right.as_object()) else {
        return Walk::IdentityConflict;
    };
    let kind = left_object.get("kind").and_then(Value::as_str);
    if kind != right_object.get("kind").and_then(Value::as_str) {
        return Walk::IdentityConflict;
    }
    if let Some(sort) = match kind {
        Some("binding") => Some(VariableSort::Binding),
        Some("function") => Some(VariableSort::Function),
        Some("constant") => Some(VariableSort::Constant),
        Some("static") => Some(VariableSort::Static),
        Some("method") => Some(VariableSort::Method),
        _ => None,
    } {
        return local_identity(&left_object["id"], &right_object["id"], sort, state, mode);
    }
    if kind == Some("constructor") {
        let adt = adt_identity(&left_object["adt"], &right_object["adt"], state, mode);
        let Walk::Ok(adt) = adt else { return adt };
        let variant = match (&left_object["variant"], &right_object["variant"]) {
            (Value::Null, Value::Null) => Value::Null,
            (left, right) if !left.is_null() && !right.is_null() => {
                match member_identity(left, right, VariableSort::Variant, state, mode) {
                    Walk::Ok(value) => value,
                    other => return other,
                }
            }
            _ => return Walk::IdentityConflict,
        };
        return Walk::Ok(value_object([
            ("kind", Value::String("constructor".into())),
            ("adt", adt),
            ("variant", variant),
        ]));
    }
    if matches!(
        kind,
        Some("external" | "foreign_function" | "foreign_static")
    ) && left == right
    {
        Walk::Ok(left.clone())
    } else {
        Walk::IdentityConflict
    }
}

fn type_tree(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (Some(left_object), Some(right_object)) = (left.as_object(), right.as_object()) else {
        return Walk::Generalize;
    };
    let kind = left_object.get("kind").and_then(Value::as_str);
    if kind != right_object.get("kind").and_then(Value::as_str) {
        return Walk::Generalize;
    }
    match kind {
        Some("primitive") => {
            if left_object["name"] == right_object["name"] {
                Walk::Ok(left.clone())
            } else {
                Walk::Generalize
            }
        }
        Some("slice") => match type_tree(
            &left_object["element"],
            &right_object["element"],
            state,
            mode,
        ) {
            Walk::Ok(element) => Walk::Ok(value_object([
                ("kind", Value::String("slice".into())),
                ("element", element),
            ])),
            other => other,
        },
        Some("array") => {
            if left_object["length"] != right_object["length"] {
                return Walk::Generalize;
            }
            match type_tree(
                &left_object["element"],
                &right_object["element"],
                state,
                mode,
            ) {
                Walk::Ok(element) => Walk::Ok(value_object([
                    ("kind", Value::String("array".into())),
                    ("element", element),
                    ("length", left_object["length"].clone()),
                ])),
                other => other,
            }
        }
        Some("raw_pointer" | "reference") => {
            if left_object["mutability"] != right_object["mutability"] {
                return Walk::Generalize;
            }
            match type_tree(
                &left_object["pointee"],
                &right_object["pointee"],
                state,
                mode,
            ) {
                Walk::Ok(pointee) => Walk::Ok(value_object([
                    ("kind", Value::String(kind.unwrap().into())),
                    ("mutability", left_object["mutability"].clone()),
                    ("pointee", pointee),
                ])),
                other => other,
            }
        }
        Some("tuple") => match type_list(
            &left_object["elements"],
            &right_object["elements"],
            state,
            mode,
        ) {
            Walk::Ok(elements) => Walk::Ok(value_object([
                ("kind", Value::String("tuple".into())),
                ("elements", elements),
            ])),
            other => other,
        },
        Some("adt") => {
            if left_object["adt_kind"] != right_object["adt_kind"] {
                return Walk::Generalize;
            }
            let identity = adt_identity(
                &left_object["identity"],
                &right_object["identity"],
                state,
                mode,
            );
            let Walk::Ok(identity) = identity else { return identity };
            let arguments = type_list(
                &left_object["arguments"],
                &right_object["arguments"],
                state,
                mode,
            );
            let Walk::Ok(arguments) = arguments else { return arguments };
            Walk::Ok(value_object([
                ("kind", Value::String("adt".into())),
                ("adt_kind", left_object["adt_kind"].clone()),
                ("identity", identity),
                ("arguments", arguments),
            ]))
        }
        _ => Walk::Generalize,
    }
}

fn type_list(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (Some(left), Some(right)) = (left.as_array(), right.as_array()) else {
        return Walk::Generalize;
    };
    if left.len() != right.len() {
        return Walk::Generalize;
    }
    let mut result = vec![];
    for (left, right) in left.iter().zip(right) {
        match type_tree(left, right, state, mode) {
            Walk::Ok(value) => result.push(value),
            other => return other,
        }
    }
    Walk::Ok(Value::Array(result))
}

fn context_type(left: &Value, right: &Value, state: &mut SynthesisState) -> Walk {
    let before = state.identities.keys().cloned().collect::<HashSet<_>>();
    let result = type_tree(left, right, state, Mode::Context);
    if !matches!(result, Walk::Ok(_)) {
        return result;
    }
    let created = state
        .identities
        .keys()
        .filter(|key| !before.contains(*key))
        .cloned()
        .collect::<Vec<_>>();
    for (sort, left, right) in created {
        if state
            .context_forward
            .get(&(sort, left.clone()))
            .is_some_and(|value| value != &right)
            || state
                .context_reverse
                .get(&(sort, right.clone()))
                .is_some_and(|value| value != &left)
        {
            return Walk::Reject;
        }
        state
            .context_forward
            .insert((sort, left.clone()), right.clone());
        state.context_reverse.insert((sort, right), left);
    }
    result
}

fn expression_variable(
    left: &Value,
    right: &Value,
    state: &mut SynthesisState,
    mode: Mode,
) -> Walk {
    match state.disagreement(VariableSort::Expression, left, right, mode) {
        Some(value) => Walk::Ok(value),
        None => Walk::Reject,
    }
}

fn expression_child(
    result: Walk,
    left: &Value,
    right: &Value,
    state: &mut SynthesisState,
    mode: Mode,
) -> Walk {
    match result {
        Walk::Ok(_) | Walk::Reject => result,
        Walk::Generalize | Walk::IdentityConflict => expression_variable(left, right, state, mode),
    }
}

fn expression(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    if mode != Mode::Source {
        return expression_inner(left, right, state, mode);
    }
    let snapshot = (
        state.counters.clone(),
        state.disagreements.clone(),
        state.identities.clone(),
        state.substitutions.clone(),
    );
    let result = expression_inner(left, right, state, mode);
    if !matches!(result, Walk::Ok(_)) {
        (
            state.counters,
            state.disagreements,
            state.identities,
            state.substitutions,
        ) = snapshot;
        return result;
    }
    let whole_expression_variable = if let Walk::Ok(value) = &result {
        value.get("kind").and_then(Value::as_str) == Some("variable")
            && value.get("sort").and_then(Value::as_str) == Some("expression")
            && value
                .get("index")
                .and_then(Value::as_u64)
                .and_then(|index| state.substitutions.get(&(VariableSort::Expression, index)))
                .is_some_and(|(stored_left, stored_right)| {
                    stored_left == left && stored_right == right
                })
    } else {
        false
    };
    if whole_expression_variable {
        (
            state.counters,
            state.disagreements,
            state.identities,
            state.substitutions,
        ) = snapshot;
        return expression_variable(left, right, state, mode);
    }
    result
}

fn expression_list(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (Some(left), Some(right)) = (left.as_array(), right.as_array()) else {
        return Walk::Generalize;
    };
    if left.len() != right.len() {
        return Walk::Generalize;
    }
    let mut values = vec![];
    for (left, right) in left.iter().zip(right) {
        match expression(left, right, state, mode) {
            Walk::Ok(value) => values.push(value),
            other => return other,
        }
    }
    Walk::Ok(Value::Array(values))
}

fn optional_expression(
    left: &Value,
    right: &Value,
    state: &mut SynthesisState,
    mode: Mode,
) -> Walk {
    match (left.is_null(), right.is_null()) {
        (true, true) => Walk::Ok(Value::Null),
        (true, false) | (false, true) => Walk::Generalize,
        _ => expression(left, right, state, mode),
    }
}

fn pattern(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (Some(left), Some(right)) = (left.as_object(), right.as_object()) else {
        return Walk::Generalize;
    };
    if left.get("kind") != right.get("kind") {
        return Walk::Generalize;
    }
    if left.get("kind").and_then(Value::as_str) == Some("wildcard") {
        return Walk::Ok(value_object([("kind", Value::String("wildcard".into()))]));
    }
    if left.get("mutability") != right.get("mutability")
        || left.get("by_ref") != right.get("by_ref")
    {
        return Walk::Generalize;
    }
    match local_identity(
        &left["id"],
        &right["id"],
        VariableSort::Binding,
        state,
        mode,
    ) {
        Walk::Ok(id) => Walk::Ok(value_object([
            ("kind", Value::String("binding".into())),
            ("id", id),
            ("mutability", left["mutability"].clone()),
            ("by_ref", left["by_ref"].clone()),
        ])),
        other => other,
    }
}

fn block(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (Some(left), Some(right)) = (
        left.get("statements").and_then(Value::as_array),
        right.get("statements").and_then(Value::as_array),
    ) else {
        return Walk::Generalize;
    };
    if left.len() != right.len() {
        return Walk::Generalize;
    }
    let mut statements = vec![];
    for (left, right) in left.iter().zip(right) {
        let (Some(left_object), Some(right_object)) = (left.as_object(), right.as_object()) else {
            return Walk::Generalize;
        };
        let kind = left_object.get("kind").and_then(Value::as_str);
        if kind != right_object.get("kind").and_then(Value::as_str) {
            return Walk::Generalize;
        }
        if kind == Some("expression") {
            if left_object["semicolon"] != right_object["semicolon"] {
                return Walk::Generalize;
            }
            let Walk::Ok(value) = expression(
                &left_object["expression"],
                &right_object["expression"],
                state,
                mode,
            ) else {
                return Walk::Generalize;
            };
            statements.push(value_object([
                ("kind", Value::String("expression".into())),
                ("expression", value),
                ("semicolon", left_object["semicolon"].clone()),
            ]));
        } else {
            let pattern_result = pattern(
                &left_object["pattern"],
                &right_object["pattern"],
                state,
                mode,
            );
            let Walk::Ok(pattern_value) = pattern_result else { return pattern_result };
            let ty = match (&left_object["type"], &right_object["type"]) {
                (Value::Null, Value::Null) => Value::Null,
                (left, right) if !left.is_null() && !right.is_null() => {
                    match type_tree(left, right, state, mode) {
                        Walk::Ok(value) => value,
                        other => return other,
                    }
                }
                _ => return Walk::Generalize,
            };
            let initializer = optional_expression(
                &left_object["initializer"],
                &right_object["initializer"],
                state,
                mode,
            );
            let Walk::Ok(initializer) = initializer else { return initializer };
            statements.push(value_object([
                ("kind", Value::String("let".into())),
                ("pattern", pattern_value),
                ("type", ty),
                ("initializer", initializer),
            ]));
        }
    }
    Walk::Ok(value_object([("statements", Value::Array(statements))]))
}

fn expression_inner(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (Some(left_object), Some(right_object)) = (left.as_object(), right.as_object()) else {
        return expression_variable(left, right, state, mode);
    };
    let kind = left_object.get("kind").and_then(Value::as_str);
    if kind != right_object.get("kind").and_then(Value::as_str) {
        return expression_variable(left, right, state, mode);
    }
    let child = |left: &Value, right: &Value, state: &mut SynthesisState| {
        expression(left, right, state, mode)
    };
    match kind {
        Some("array" | "tuple") => match expression_list(
            &left_object["elements"],
            &right_object["elements"],
            state,
            mode,
        ) {
            Walk::Ok(elements) => Walk::Ok(value_object([
                ("kind", Value::String(kind.unwrap().into())),
                ("elements", elements),
            ])),
            other => expression_child(other, left, right, state, mode),
        },
        Some("call") => {
            let callee = child(&left_object["callee"], &right_object["callee"], state);
            let Walk::Ok(callee) = callee else {
                return expression_child(callee, left, right, state, mode);
            };
            let arguments = expression_list(
                &left_object["arguments"],
                &right_object["arguments"],
                state,
                mode,
            );
            let Walk::Ok(arguments) = arguments else {
                return expression_child(arguments, left, right, state, mode);
            };
            Walk::Ok(value_object([
                ("kind", Value::String("call".into())),
                ("callee", callee),
                ("arguments", arguments),
            ]))
        }
        Some("method_call") => {
            let receiver = child(&left_object["receiver"], &right_object["receiver"], state);
            let Walk::Ok(receiver) = receiver else {
                return expression_child(receiver, left, right, state, mode);
            };
            let method =
                value_identity(&left_object["method"], &right_object["method"], state, mode);
            let Walk::Ok(method) = method else {
                return expression_child(method, left, right, state, mode);
            };
            let arguments = expression_list(
                &left_object["arguments"],
                &right_object["arguments"],
                state,
                mode,
            );
            let Walk::Ok(arguments) = arguments else {
                return expression_child(arguments, left, right, state, mode);
            };
            Walk::Ok(value_object([
                ("kind", Value::String("method_call".into())),
                ("receiver", receiver),
                ("method", method),
                ("arguments", arguments),
            ]))
        }
        Some("binary" | "assign_op") => {
            if left_object["operator"] != right_object["operator"] {
                return expression_variable(left, right, state, mode);
            }
            let first = child(&left_object["left"], &right_object["left"], state);
            let Walk::Ok(first) = first else {
                return expression_child(first, left, right, state, mode);
            };
            let second = child(&left_object["right"], &right_object["right"], state);
            let Walk::Ok(second) = second else {
                return expression_child(second, left, right, state, mode);
            };
            Walk::Ok(value_object([
                ("kind", Value::String(kind.unwrap().into())),
                ("operator", left_object["operator"].clone()),
                ("left", first),
                ("right", second),
            ]))
        }
        Some("unary") => {
            if left_object["operator"] != right_object["operator"] {
                return expression_variable(left, right, state, mode);
            }
            let operand = child(&left_object["operand"], &right_object["operand"], state);
            match operand {
                Walk::Ok(value) => Walk::Ok(value_object([
                    ("kind", Value::String("unary".into())),
                    ("operator", left_object["operator"].clone()),
                    ("operand", value),
                ])),
                other => expression_child(other, left, right, state, mode),
            }
        }
        Some("path") => {
            match value_identity(&left_object["value"], &right_object["value"], state, mode) {
                Walk::Ok(value) => Walk::Ok(value_object([
                    ("kind", Value::String("path".into())),
                    ("value", value),
                ])),
                other => other,
            }
        }
        Some("cast") => {
            let expression_result = child(
                &left_object["expression"],
                &right_object["expression"],
                state,
            );
            let Walk::Ok(expression_value) = expression_result else {
                return expression_child(expression_result, left, right, state, mode);
            };
            let ty = type_tree(&left_object["type"], &right_object["type"], state, mode);
            let Walk::Ok(ty) = ty else { return expression_child(ty, left, right, state, mode) };
            Walk::Ok(value_object([
                ("kind", Value::String("cast".into())),
                ("expression", expression_value),
                ("type", ty),
            ]))
        }
        Some("assign" | "index") => {
            let (first_key, second_key) = if kind == Some("assign") {
                ("left", "right")
            } else {
                ("base", "index")
            };
            let first = child(&left_object[first_key], &right_object[first_key], state);
            let Walk::Ok(first) = first else {
                return expression_child(first, left, right, state, mode);
            };
            let second = child(&left_object[second_key], &right_object[second_key], state);
            let Walk::Ok(second) = second else {
                return expression_child(second, left, right, state, mode);
            };
            Walk::Ok(value_object([
                ("kind", Value::String(kind.unwrap().into())),
                (first_key, first),
                (second_key, second),
            ]))
        }
        Some("field") => {
            let base = child(&left_object["base"], &right_object["base"], state);
            let Walk::Ok(base) = base else {
                return expression_child(base, left, right, state, mode);
            };
            let member = member_identity(
                &left_object["field"],
                &right_object["field"],
                VariableSort::Field,
                state,
                mode,
            );
            let Walk::Ok(member) = member else {
                return expression_child(member, left, right, state, mode);
            };
            Walk::Ok(value_object([
                ("kind", Value::String("field".into())),
                ("base", base),
                ("field", member),
            ]))
        }
        Some("range") => {
            if left_object["limits"] != right_object["limits"] {
                return expression_variable(left, right, state, mode);
            }
            let start =
                optional_expression(&left_object["start"], &right_object["start"], state, mode);
            let Walk::Ok(start) = start else {
                return expression_child(start, left, right, state, mode);
            };
            let end = optional_expression(&left_object["end"], &right_object["end"], state, mode);
            let Walk::Ok(end) = end else { return expression_child(end, left, right, state, mode) };
            Walk::Ok(value_object([
                ("kind", Value::String("range".into())),
                ("start", start),
                ("end", end),
                ("limits", left_object["limits"].clone()),
            ]))
        }
        Some("if") => {
            let condition = child(&left_object["condition"], &right_object["condition"], state);
            let Walk::Ok(condition) = condition else {
                return expression_child(condition, left, right, state, mode);
            };
            let then = block(&left_object["then"], &right_object["then"], state, mode);
            let Walk::Ok(then) = then else {
                return expression_child(then, left, right, state, mode);
            };
            let otherwise =
                optional_expression(&left_object["else"], &right_object["else"], state, mode);
            let Walk::Ok(otherwise) = otherwise else {
                return expression_child(otherwise, left, right, state, mode);
            };
            Walk::Ok(value_object([
                ("kind", Value::String("if".into())),
                ("condition", condition),
                ("then", then),
                ("else", otherwise),
            ]))
        }
        Some("while") => {
            let condition = child(&left_object["condition"], &right_object["condition"], state);
            let Walk::Ok(condition) = condition else {
                return expression_child(condition, left, right, state, mode);
            };
            let body = block(&left_object["body"], &right_object["body"], state, mode);
            let Walk::Ok(body) = body else {
                return expression_child(body, left, right, state, mode);
            };
            Walk::Ok(value_object([
                ("kind", Value::String("while".into())),
                ("condition", condition),
                ("body", body),
            ]))
        }
        Some("loop") => match block(&left_object["body"], &right_object["body"], state, mode) {
            Walk::Ok(body) => Walk::Ok(value_object([
                ("kind", Value::String("loop".into())),
                ("body", body),
            ])),
            other => expression_child(other, left, right, state, mode),
        },
        Some("struct") => struct_expression(left, right, state, mode),
        Some("literal") => literal_expression(left, right, state, mode),
        Some("address_of") => {
            if left_object["borrow"] != right_object["borrow"]
                || left_object["mutability"] != right_object["mutability"]
            {
                return expression_variable(left, right, state, mode);
            }
            let value = child(
                &left_object["expression"],
                &right_object["expression"],
                state,
            );
            match value {
                Walk::Ok(value) => Walk::Ok(value_object([
                    ("kind", Value::String("address_of".into())),
                    ("borrow", left_object["borrow"].clone()),
                    ("mutability", left_object["mutability"].clone()),
                    ("expression", value),
                ])),
                other => expression_child(other, left, right, state, mode),
            }
        }
        Some("return" | "break") => {
            match optional_expression(&left_object["value"], &right_object["value"], state, mode) {
                Walk::Ok(value) => Walk::Ok(value_object([
                    ("kind", Value::String(kind.unwrap().into())),
                    ("value", value),
                ])),
                other => expression_child(other, left, right, state, mode),
            }
        }
        Some("continue") => Walk::Ok(value_object([("kind", Value::String("continue".into()))])),
        Some("repeat") => {
            let value = child(&left_object["value"], &right_object["value"], state);
            let Walk::Ok(value) = value else {
                return expression_child(value, left, right, state, mode);
            };
            let count = child(&left_object["count"], &right_object["count"], state);
            let Walk::Ok(count) = count else {
                return expression_child(count, left, right, state, mode);
            };
            Walk::Ok(value_object([
                ("kind", Value::String("repeat".into())),
                ("value", value),
                ("count", count),
            ]))
        }
        Some("block") => match block(&left_object["block"], &right_object["block"], state, mode) {
            Walk::Ok(value) => Walk::Ok(value_object([
                ("kind", Value::String("block".into())),
                ("block", value),
            ])),
            other => expression_child(other, left, right, state, mode),
        },
        _ => expression_variable(left, right, state, mode),
    }
}

fn struct_expression(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (left, right) = (left.as_object().unwrap(), right.as_object().unwrap());
    let adt = adt_identity(&left["adt"], &right["adt"], state, mode);
    let Walk::Ok(adt) = adt else {
        return expression_child(
            adt,
            &Value::Object(left.clone()),
            &Value::Object(right.clone()),
            state,
            mode,
        );
    };
    let variant = match (&left["variant"], &right["variant"]) {
        (Value::Null, Value::Null) => Value::Null,
        (left_value, right_value) if !left_value.is_null() && !right_value.is_null() => {
            match member_identity(left_value, right_value, VariableSort::Variant, state, mode) {
                Walk::Ok(value) => value,
                other => {
                    return expression_child(
                        other,
                        &Value::Object(left.clone()),
                        &Value::Object(right.clone()),
                        state,
                        mode,
                    );
                }
            }
        }
        _ => {
            return expression_variable(
                &Value::Object(left.clone()),
                &Value::Object(right.clone()),
                state,
                mode,
            );
        }
    };
    let (Some(left_fields), Some(right_fields)) =
        (left["fields"].as_array(), right["fields"].as_array())
    else {
        return Walk::Generalize;
    };
    if left_fields.len() != right_fields.len() {
        return expression_variable(
            &Value::Object(left.clone()),
            &Value::Object(right.clone()),
            state,
            mode,
        );
    }
    let mut fields = vec![];
    for (left_field, right_field) in left_fields.iter().zip(right_fields) {
        let member = member_identity(
            &left_field["field"],
            &right_field["field"],
            VariableSort::Field,
            state,
            mode,
        );
        let Walk::Ok(member) = member else {
            return expression_child(
                member,
                &Value::Object(left.clone()),
                &Value::Object(right.clone()),
                state,
                mode,
            );
        };
        let value = expression(&left_field["value"], &right_field["value"], state, mode);
        let Walk::Ok(value) = value else {
            return expression_child(
                value,
                &Value::Object(left.clone()),
                &Value::Object(right.clone()),
                state,
                mode,
            );
        };
        fields.push(value_object([("field", member), ("value", value)]));
    }
    let rest = optional_expression(&left["rest"], &right["rest"], state, mode);
    let Walk::Ok(rest) = rest else {
        return expression_child(
            rest,
            &Value::Object(left.clone()),
            &Value::Object(right.clone()),
            state,
            mode,
        );
    };
    Walk::Ok(value_object([
        ("kind", Value::String("struct".into())),
        ("adt", adt),
        ("variant", variant),
        ("fields", Value::Array(fields)),
        ("rest", rest),
    ]))
}

fn literal_expression(left: &Value, right: &Value, state: &mut SynthesisState, mode: Mode) -> Walk {
    let (left_literal, right_literal) = (&left["value"], &right["value"]);
    if left_literal.get("kind").and_then(Value::as_str) == Some("integer")
        && right_literal.get("kind").and_then(Value::as_str) == Some("integer")
    {
        if left_literal["type"] != right_literal["type"] {
            return expression_variable(left, right, state, mode);
        }
        let magnitude = if left_literal["value"] == right_literal["value"] {
            left_literal["value"].clone()
        } else {
            let (Some(left_value), Some(right_value)) = (
                left_literal["value"].as_str(),
                right_literal["value"].as_str(),
            ) else {
                return expression_variable(left, right, state, mode);
            };
            let canonical = |value: &str| {
                value == "0"
                    || (!value.starts_with('0') && value.bytes().all(|byte| byte.is_ascii_digit()))
            };
            if !canonical(left_value) || !canonical(right_value) {
                return expression_variable(left, right, state, mode);
            }
            match state.disagreement(
                VariableSort::IntegerMagnitude,
                &Value::String(left_value.into()),
                &Value::String(right_value.into()),
                mode,
            ) {
                Some(value) => value,
                None => return Walk::Reject,
            }
        };
        return Walk::Ok(value_object([
            ("kind", Value::String("literal".into())),
            (
                "value",
                value_object([
                    ("kind", Value::String("integer".into())),
                    ("value", magnitude),
                    ("type", left_literal["type"].clone()),
                ]),
            ),
        ]));
    }
    if left_literal == right_literal {
        Walk::Ok(left.clone())
    } else {
        expression_variable(left, right, state, mode)
    }
}

fn synthesize_context(
    left: &Value,
    right: &Value,
    state: &mut SynthesisState,
) -> Option<Map<String, Value>> {
    if left["lhs"] != right["lhs"] {
        return None;
    }
    let (left_anchors, right_anchors) = (
        left["pointer_anchors"].as_array()?,
        right["pointer_anchors"].as_array()?,
    );
    if left_anchors.len() != right_anchors.len() {
        return None;
    }
    let mut anchors = vec![];
    for (left_anchor, right_anchor) in left_anchors.iter().zip(right_anchors) {
        let (left_id, right_id) = (left_anchor["id"].as_str()?, right_anchor["id"].as_str()?);
        if state.left_anchors.contains(left_id) || state.right_anchors.contains(right_id) {
            return None;
        }
        let variable = state.allocate(
            VariableSort::Anchor,
            &Value::String(left_id.into()),
            &Value::String(right_id.into()),
        );
        state
            .anchor_pairs
            .insert((left_id.into(), right_id.into()), variable.clone());
        state.left_anchors.insert(left_id.into());
        state.right_anchors.insert(right_id.into());
        let Walk::Ok(source_type) = context_type(
            &left_anchor["source_type"],
            &right_anchor["source_type"],
            state,
        ) else {
            return None;
        };
        let Walk::Ok(target_type) = context_type(
            &left_anchor["target_type"],
            &right_anchor["target_type"],
            state,
        ) else {
            return None;
        };
        anchors.push(value_object([
            ("id", variable),
            ("source_type", source_type),
            ("target_type", target_type),
        ]));
    }
    let mut result = Map::new();
    result.insert("pointer_anchors".into(), Value::Array(anchors));
    result.insert("lhs".into(), left["lhs"].clone());
    for key in [
        "source_type",
        "source_adjusted_type",
        "target_type",
        "target_adjusted_type",
    ] {
        let Walk::Ok(value) = context_type(&left[key], &right[key], state) else { return None };
        result.insert(key.into(), value);
    }
    Some(result)
}

fn collect_local_identities(value: &Value, result: &mut HashSet<(VariableSort, String)>) {
    match value {
        Value::Object(object) => {
            let kind = object.get("kind").and_then(Value::as_str);
            if matches!(
                kind,
                Some("literal" | "external" | "foreign_function" | "foreign_static" | "variable")
            ) {
                return;
            }
            if kind == Some("local") {
                if let Some(owner) = object.get("owner") {
                    collect_local_identities(owner, result);
                }
                if let Some(id) = object.get("id").and_then(Value::as_str)
                    && let Some(sort) = local_sort(id)
                {
                    result.insert((sort, id.into()));
                }
                return;
            }
            if matches!(
                kind,
                Some("binding" | "function" | "constant" | "static" | "method")
            ) {
                if let Some(id) = object.get("id").and_then(Value::as_str)
                    && let Some(sort) = local_sort(id)
                {
                    result.insert((sort, id.into()));
                }
                return;
            }
            for child in object.values() {
                collect_local_identities(child, result);
            }
        }
        Value::Array(values) => {
            for child in values {
                collect_local_identities(child, result);
            }
        }
        _ => {}
    }
}

fn carriers_valid(state: &SynthesisState) -> bool {
    for side in 0..2 {
        let anchor_set = if side == 0 {
            &state.left_anchors
        } else {
            &state.right_anchors
        };
        let anchors = anchor_set
            .iter()
            .map(|id| (VariableSort::Binding, id.clone()))
            .collect::<HashSet<_>>();
        let mut carriers = HashMap::<(VariableSort, String), HashSet<(VariableSort, u64)>>::new();
        for (&(sort, index), values) in &state.substitutions {
            let value = if side == 0 { &values.0 } else { &values.1 };
            if matches!(
                sort,
                VariableSort::Binding
                    | VariableSort::Function
                    | VariableSort::Struct
                    | VariableSort::Enum
                    | VariableSort::Union
                    | VariableSort::Field
                    | VariableSort::Variant
                    | VariableSort::Constant
                    | VariableSort::Static
                    | VariableSort::Method
            ) {
                if let Some(id) = value.as_str()
                    && let Some(identity_sort) = local_sort(id)
                {
                    carriers
                        .entry((identity_sort, id.into()))
                        .or_default()
                        .insert((sort, index));
                }
            } else if sort == VariableSort::Expression {
                let mut identities = HashSet::new();
                collect_local_identities(value, &mut identities);
                if !identities.is_disjoint(&anchors) {
                    return false;
                }
                for identity in identities {
                    carriers.entry(identity).or_default().insert((sort, index));
                }
            }
        }
        if carriers
            .into_iter()
            .any(|(identity, values)| !anchors.contains(&identity) && values.len() > 1)
        {
            return false;
        }
    }
    true
}

fn rewrite_variables(
    value: &Value,
    mappings: &mut BTreeMap<VariableSort, BTreeMap<u64, u64>>,
) -> Value {
    if let Value::Object(object) = value {
        if object.get("kind").and_then(Value::as_str) == Some("variable") {
            let sort: VariableSort = serde_json::from_value(object["sort"].clone()).unwrap();
            let old = object["index"].as_u64().unwrap();
            let map = mappings.entry(sort).or_default();
            let next = map.len() as u64;
            let new = *map.entry(old).or_insert(next);
            return variable_value(sort, new);
        }
        let mut result = Map::new();
        for key in canonical_object_keys(object) {
            result.insert(key.into(), rewrite_variables(&object[key], mappings));
        }
        Value::Object(result)
    } else if let Value::Array(values) = value {
        Value::Array(
            values
                .iter()
                .map(|value| rewrite_variables(value, mappings))
                .collect(),
        )
    } else {
        value.clone()
    }
}

pub fn canonicalize_rule(rule: &Rule) -> Result<Rule, DocumentError> {
    let value = serde_json::to_value(rule).map_err(|error| invalid(error.to_string()))?;
    let mut mappings = BTreeMap::new();
    let mut output = Map::new();
    let mut anchors = vec![];
    for anchor in value["pointer_anchors"].as_array().unwrap() {
        anchors.push(value_object([
            ("id", rewrite_variables(&anchor["id"], &mut mappings)),
            (
                "source_type",
                rewrite_variables(&anchor["source_type"], &mut mappings),
            ),
            (
                "target_type",
                rewrite_variables(&anchor["target_type"], &mut mappings),
            ),
        ]));
    }
    output.insert("pointer_anchors".into(), Value::Array(anchors));
    output.insert("lhs".into(), value["lhs"].clone());
    for key in [
        "source_type",
        "source_adjusted_type",
        "target_type",
        "target_adjusted_type",
    ] {
        output.insert(key.into(), rewrite_variables(&value[key], &mut mappings));
    }
    output.insert(
        "source_pattern".into(),
        rewrite_variables(&value["source_pattern"], &mut mappings),
    );
    output.insert(
        "target_pattern".into(),
        rewrite_variables(&value["target_pattern"], &mut mappings),
    );
    let canonical: Rule = serde_json::from_value(Value::Object(output))
        .map_err(|error| invalid(format!("canonical rule is invalid: {error}")))?;
    validate_rule(&canonical, "rule")?;
    Ok(canonical)
}

pub fn synthesize_observation_pair(left: &Observation, right: &Observation) -> PairSynthesis {
    let left_value = serde_json::to_value(left).unwrap();
    let right_value = serde_json::to_value(right).unwrap();
    let mut state = SynthesisState::new();
    let Some(context) = synthesize_context(&left_value, &right_value, &mut state) else {
        return PairSynthesis {
            rule: None,
            rejection: Some(PairRejection::Context),
            substitutions: BTreeMap::new(),
        };
    };
    let source = expression(
        &left_value["source_expression"],
        &right_value["source_expression"],
        &mut state,
        Mode::Source,
    );
    let Walk::Ok(source) = source else {
        return PairSynthesis {
            rule: None,
            rejection: Some(PairRejection::Source),
            substitutions: state.substitutions,
        };
    };
    if source.get("kind").and_then(Value::as_str) == Some("variable")
        && source.get("sort").and_then(Value::as_str) == Some("expression")
    {
        return PairSynthesis {
            rule: None,
            rejection: Some(PairRejection::DegenerateSource),
            substitutions: state.substitutions,
        };
    }
    let target = expression(
        &left_value["target_expression"],
        &right_value["target_expression"],
        &mut state,
        Mode::Target,
    );
    let Walk::Ok(target) = target else {
        return PairSynthesis {
            rule: None,
            rejection: Some(PairRejection::TargetLookup),
            substitutions: state.substitutions,
        };
    };
    if !carriers_valid(&state) {
        return PairSynthesis {
            rule: None,
            rejection: Some(PairRejection::Carrier),
            substitutions: state.substitutions,
        };
    }
    let mut value = context;
    value.insert("source_pattern".into(), source);
    value.insert("target_pattern".into(), target);
    let rule = serde_json::from_value::<Rule>(Value::Object(value))
        .ok()
        .and_then(|rule| canonicalize_rule(&rule).ok());
    PairSynthesis {
        rule,
        rejection: None,
        substitutions: state.substitutions,
    }
}

pub fn synthesize_rules(documents: &[ObservationDocument]) -> Result<RuleDocument, DocumentError> {
    let mut unique = BTreeMap::<String, (Observation, bool)>::new();
    for document in documents {
        validate_observation_document(document)?;
        for observation in &document.observations {
            let key = serde_json::to_string(&serde_json::to_value(observation).unwrap()).unwrap();
            unique
                .entry(key)
                .and_modify(|entry| entry.1 = true)
                .or_insert((observation.clone(), false));
        }
    }
    let values = unique.into_values().collect::<Vec<_>>();
    let mut rules = BTreeMap::<String, Rule>::new();
    for (index, (left, repeated)) in values.iter().enumerate() {
        for (right, _) in &values[index + 1..] {
            if let Some(rule) = synthesize_observation_pair(left, right).rule {
                rules.insert(semantic_sort_key(&rule), rule);
            }
        }
        if *repeated && let Some(rule) = synthesize_observation_pair(left, left).rule {
            rules.insert(semantic_sort_key(&rule), rule);
        }
    }
    let document = RuleDocument {
        schema_version: RULE_SCHEMA_VERSION,
        rules: rules.into_values().collect(),
    };
    validate_rule_document(&document)?;
    Ok(document)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleMatchInput {
    pub source_expression: Expression,
    pub pointer_anchors: Vec<crate::PointerAnchor>,
    pub lhs: bool,
    pub source_type: TypeTree,
    pub source_adjusted_type: TypeTree,
    /// Required only for a non-pointer-like source root. When omitted there,
    /// the unchanged source intrinsic type is used.
    pub target_type: Option<TypeTree>,
    /// A pointer-like source root is inapplicable when this requirement is absent.
    pub target_adjusted_type: Option<TypeTree>,
}

#[derive(Debug, Clone)]
pub struct LoadedRuleSet {
    rules: Vec<Rule>,
    alpha_groups: Vec<usize>,
    strictly_more_specific_groups: Vec<BTreeSet<usize>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuleSelection {
    pub rule_index: usize,
    pub alpha_group: usize,
    pub target_expression: Expression,
    pub substitution_cost: usize,
    pub target_size: usize,
    pub syntax_overrides: BTreeMap<usize, String>,
    pub identity_syntax: BTreeMap<String, String>,
}

#[derive(Debug, Clone, Default)]
struct MatchState {
    bindings: BTreeMap<(VariableSort, u64), Value>,
    identity_reverse: HashMap<(VariableSort, String), (VariableSort, u64)>,
}

impl MatchState {
    fn bind(&mut self, sort: VariableSort, index: u64, value: Value) -> bool {
        let key = (sort, index);
        let value = if identity_namespace(sort).is_some() {
            let Some(value) = abstract_identity_value(sort, &value) else {
                return false;
            };
            value
        } else {
            value
        };
        if let Some(existing) = self.bindings.get(&key) {
            return existing == &value;
        }
        if identity_namespace(sort).is_some() {
            let namespace = identity_namespace(sort).unwrap();
            let reverse_key = (namespace, compact(&value));
            if self.identity_reverse.contains_key(&reverse_key) {
                return false;
            }
            self.identity_reverse.insert(reverse_key, key);
            self.bindings.insert(key, value);
        } else {
            self.bindings.insert(key, value);
        }
        true
    }
}

fn identity_namespace(sort: VariableSort) -> Option<VariableSort> {
    Some(match sort {
        VariableSort::Anchor | VariableSort::Binding => VariableSort::Binding,
        VariableSort::Function => VariableSort::Function,
        VariableSort::Struct => VariableSort::Struct,
        VariableSort::Enum => VariableSort::Enum,
        VariableSort::Union => VariableSort::Union,
        VariableSort::Field => VariableSort::Field,
        VariableSort::Variant => VariableSort::Variant,
        VariableSort::Constant => VariableSort::Constant,
        VariableSort::Static => VariableSort::Static,
        VariableSort::Method => VariableSort::Method,
        VariableSort::Expression | VariableSort::IntegerMagnitude => return None,
    })
}

fn abstract_identity_value(sort: VariableSort, value: &Value) -> Option<Value> {
    if value.get("kind").and_then(Value::as_str) == Some("variable") {
        let concrete_sort: VariableSort =
            serde_json::from_value(value.get("sort")?.clone()).ok()?;
        return (sort == concrete_sort).then(|| value.clone());
    }
    let text = if let Some(text) = value.as_str() {
        text
    } else {
        let object = value.as_object()?;
        object.get("id")?.as_str()?
    };
    let concrete_sort = local_sort(text)?;
    (identity_namespace(sort) == identity_namespace(concrete_sort))
        .then(|| Value::String(text.into()))
}

fn variable_parts(value: &Value) -> Option<(VariableSort, u64)> {
    let object = value.as_object()?;
    if object.get("kind")?.as_str()? != "variable" {
        return None;
    }
    let sort = serde_json::from_value(object.get("sort")?.clone()).ok()?;
    Some((sort, object.get("index")?.as_u64()?))
}

fn match_normalized(pattern: &Value, concrete: &Value, state: &mut MatchState) -> bool {
    if let Some((sort, index)) = variable_parts(pattern) {
        return match sort {
            VariableSort::Expression => state.bind(sort, index, concrete.clone()),
            VariableSort::IntegerMagnitude => {
                concrete.as_str().is_some() && state.bind(sort, index, concrete.clone())
            }
            _ => state.bind(sort, index, concrete.clone()),
        };
    }
    match (pattern, concrete) {
        (Value::Object(pattern), Value::Object(concrete)) => {
            pattern.len() == concrete.len()
                && pattern.iter().all(|(key, child)| {
                    concrete
                        .get(key)
                        .is_some_and(|value| match_normalized(child, value, state))
                })
        }
        (Value::Array(pattern), Value::Array(concrete)) => {
            pattern.len() == concrete.len()
                && pattern
                    .iter()
                    .zip(concrete)
                    .all(|(left, right)| match_normalized(left, right, state))
        }
        _ => pattern == concrete,
    }
}

fn source_root_pointer_like(source: &TypeTree, adjusted: &TypeTree) -> bool {
    pointer_like_type(source) || pointer_like_type(adjusted)
}

fn pointer_like_type(ty: &TypeTree) -> bool {
    match ty {
        TypeTree::RawPointer { .. } | TypeTree::Reference { .. } => true,
        TypeTree::Adt {
            identity,
            arguments,
            ..
        } if standard_box_identity(identity) => !arguments.is_empty(),
        TypeTree::Adt {
            identity,
            arguments,
            ..
        } if standard_option_identity(identity) && arguments.len() == 1 => {
            matches!(&arguments[0], TypeTree::Reference { .. })
                || matches!(&arguments[0], TypeTree::Adt { identity, arguments, .. } if standard_box_identity(identity) && !arguments.is_empty())
        }
        _ => false,
    }
}

fn standard_box_identity(identity: &crate::AdtIdentity) -> bool {
    matches!(identity, crate::AdtIdentity::External { crate_name, path }
        if crate_name == "alloc" && path == &["boxed", "Box"])
}

fn standard_option_identity(identity: &crate::AdtIdentity) -> bool {
    matches!(identity, crate::AdtIdentity::External { crate_name, path }
        if crate_name == "core" && path == &["option", "Option"])
}

fn rule_matches(rule: &Rule, input: &RuleMatchInput) -> Option<MatchState> {
    if rule.lhs != input.lhs || rule.pointer_anchors.len() != input.pointer_anchors.len() {
        return None;
    }
    let mut state = MatchState::default();
    for (rule_anchor, region_anchor) in rule.pointer_anchors.iter().zip(&input.pointer_anchors) {
        if !state.bind(
            rule_anchor.id.sort(),
            rule_anchor.id.index(),
            Value::String(region_anchor.id.clone()),
        ) {
            return None;
        }
        if !match_normalized(
            &serde_json::to_value(&rule_anchor.source_type).ok()?,
            &serde_json::to_value(&region_anchor.source_type).ok()?,
            &mut state,
        ) || !match_normalized(
            &serde_json::to_value(&rule_anchor.target_type).ok()?,
            &serde_json::to_value(&region_anchor.target_type).ok()?,
            &mut state,
        ) {
            return None;
        }
    }
    for (pattern, concrete) in [
        (&rule.source_type, &input.source_type),
        (&rule.source_adjusted_type, &input.source_adjusted_type),
    ] {
        if !match_normalized(
            &serde_json::to_value(pattern).ok()?,
            &serde_json::to_value(concrete).ok()?,
            &mut state,
        ) {
            return None;
        }
    }
    if source_root_pointer_like(&input.source_type, &input.source_adjusted_type) {
        let target_adjusted = input.target_adjusted_type.as_ref()?;
        if !match_normalized(
            &serde_json::to_value(&rule.target_adjusted_type).ok()?,
            &serde_json::to_value(target_adjusted).ok()?,
            &mut state,
        ) {
            return None;
        }
    } else if !match_normalized(
        &serde_json::to_value(&rule.target_type).ok()?,
        &serde_json::to_value(&input.source_type).ok()?,
        &mut state,
    ) || !match_normalized(
        &serde_json::to_value(&rule.target_adjusted_type).ok()?,
        &serde_json::to_value(&input.source_adjusted_type).ok()?,
        &mut state,
    ) {
        return None;
    }
    if !match_normalized(
        &serde_json::to_value(&rule.source_pattern).ok()?,
        &serde_json::to_value(&input.source_expression).ok()?,
        &mut state,
    ) {
        return None;
    }
    match_carriers_valid(&state, input).then_some(state)
}

fn match_carriers_valid(state: &MatchState, input: &RuleMatchInput) -> bool {
    let anchors = input
        .pointer_anchors
        .iter()
        .map(|anchor| (VariableSort::Binding, anchor.id.clone()))
        .collect::<HashSet<_>>();
    let mut carriers = HashMap::<(VariableSort, String), HashSet<(VariableSort, u64)>>::new();
    for (&(sort, index), value) in &state.bindings {
        if identity_namespace(sort).is_some() {
            if let Some(text) = value.as_str()
                && let Some(identity_sort) = local_sort(text)
            {
                carriers
                    .entry((identity_sort, text.into()))
                    .or_default()
                    .insert((sort, index));
            }
        } else if sort == VariableSort::Expression {
            let mut identities = HashSet::new();
            collect_local_identities(value, &mut identities);
            if !identities.is_disjoint(&anchors) {
                return false;
            }
            for identity in identities {
                carriers.entry(identity).or_default().insert((sort, index));
            }
        }
    }
    !carriers
        .into_iter()
        .any(|(identity, values)| !anchors.contains(&identity) && values.len() > 1)
}

fn source_pattern_variables(rule: &Rule) -> BTreeSet<(VariableSort, u64)> {
    let mut result = BTreeSet::new();
    visit_variables(
        &serde_json::to_value(&rule.source_pattern).unwrap(),
        &mut |sort, index| {
            result.insert((sort, index));
            Ok(())
        },
    )
    .unwrap();
    result
}

pub fn normalized_term_size(value: &Value) -> usize {
    match value {
        Value::Object(object)
            if matches!(
                object.get("kind").and_then(Value::as_str),
                Some(
                    "variable"
                        | "external"
                        | "local"
                        | "binding"
                        | "function"
                        | "constant"
                        | "static"
                        | "method"
                        | "foreign_function"
                        | "foreign_static"
                )
            ) =>
        {
            1
        }
        Value::Object(object) => {
            usize::from(object.contains_key("kind"))
                + object
                    .iter()
                    .filter(|(key, _)| key.as_str() != "kind")
                    .map(|(_, value)| normalized_term_size(value))
                    .sum::<usize>()
        }
        Value::Array(values) => values.iter().map(normalized_term_size).sum(),
        Value::Null => 0,
        _ => 1,
    }
}

fn substitution_cost(rule: &Rule, state: &MatchState) -> usize {
    source_pattern_variables(rule)
        .into_iter()
        .map(|key| state.bindings.get(&key).map_or(0, normalized_term_size))
        .sum()
}

fn abstract_match(pattern: &Value, term: &Value, state: &mut MatchState) -> bool {
    if let Some((sort, index)) = variable_parts(pattern) {
        let admissible = match sort {
            VariableSort::Expression => true,
            VariableSort::IntegerMagnitude => {
                term.as_str().is_some()
                    || variable_parts(term)
                        .is_some_and(|(term_sort, _)| term_sort == VariableSort::IntegerMagnitude)
            }
            _ => variable_parts(term).is_some_and(|(term_sort, _)| {
                identity_namespace(term_sort) == identity_namespace(sort)
            }),
        };
        return admissible && state.bind(sort, index, term.clone());
    }
    match (pattern, term) {
        (Value::Object(pattern), Value::Object(term)) => {
            pattern.len() == term.len()
                && pattern.iter().all(|(key, child)| {
                    term.get(key)
                        .is_some_and(|value| abstract_match(child, value, state))
                })
        }
        (Value::Array(pattern), Value::Array(term)) => {
            pattern.len() == term.len()
                && pattern
                    .iter()
                    .zip(term)
                    .all(|(left, right)| abstract_match(left, right, state))
        }
        _ => pattern == term,
    }
}

/// Returns whether `pattern` is at least as specific as `other`, considering
/// only the typed source patterns and standardizing their variables apart.
pub fn source_pattern_at_least_as_specific(
    pattern: &RuleExpression,
    other: &RuleExpression,
) -> bool {
    let more_specific = serde_json::to_value(pattern).unwrap();
    let less_specific = serde_json::to_value(other).unwrap();
    abstract_match(&less_specific, &more_specific, &mut MatchState::default())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SubstitutionPosition {
    Expression,
    ValueIdentity,
    AdtIdentity,
    IdentityId,
    Magnitude,
    Other,
}

fn expression_node_count(value: &Value, position: SubstitutionPosition) -> usize {
    let own = usize::from(
        position == SubstitutionPosition::Expression && matches!(value, Value::Object(_)),
    );
    match value {
        Value::Object(object) => {
            own + object
                .iter()
                .map(|(key, value)| {
                    expression_node_count(value, child_substitution_position(object, key))
                })
                .sum::<usize>()
        }
        Value::Array(values) => {
            own + values
                .iter()
                .map(|value| expression_node_count(value, position))
                .sum::<usize>()
        }
        _ => own,
    }
}

fn collect_source_expression_syntax(
    pattern: &Value,
    concrete: &Value,
    position: SubstitutionPosition,
    syntax: &[String],
    cursor: &mut usize,
    bindings: &mut BTreeMap<(VariableSort, u64), String>,
    enclosing_syntax: Option<&str>,
) {
    let mut current_syntax = enclosing_syntax;
    if position == SubstitutionPosition::Expression && matches!(pattern, Value::Object(_)) {
        let ordinal = *cursor;
        current_syntax = syntax.get(ordinal).map(String::as_str).or(enclosing_syntax);
        if let Some((sort, index)) = variable_parts(pattern)
            && let Some(value) = current_syntax
        {
            bindings
                .entry((sort, index))
                .or_insert_with(|| value.to_owned());
        }
        if let Some((VariableSort::Expression, _)) = variable_parts(pattern) {
            *cursor += expression_node_count(concrete, position);
            return;
        }
        *cursor += 1;
    } else if let Some((sort, index)) = variable_parts(pattern)
        && let Some(value) = current_syntax
    {
        bindings
            .entry((sort, index))
            .or_insert_with(|| value.to_owned());
    }
    match (pattern, concrete) {
        (Value::Object(pattern), Value::Object(concrete)) => {
            for key in canonical_object_keys(pattern) {
                if let Some(value) = concrete.get(key) {
                    collect_source_expression_syntax(
                        &pattern[key],
                        value,
                        child_substitution_position(pattern, key),
                        syntax,
                        cursor,
                        bindings,
                        current_syntax,
                    );
                }
            }
        }
        (Value::Array(pattern), Value::Array(concrete)) => {
            for (pattern, concrete) in pattern.iter().zip(concrete) {
                collect_source_expression_syntax(
                    pattern,
                    concrete,
                    position,
                    syntax,
                    cursor,
                    bindings,
                    current_syntax,
                );
            }
        }
        _ => {}
    }
}

fn collect_target_syntax_overrides(
    pattern: &Value,
    concrete: &Value,
    position: SubstitutionPosition,
    bindings: &BTreeMap<(VariableSort, u64), String>,
    cursor: &mut usize,
    overrides: &mut BTreeMap<usize, String>,
) {
    if position == SubstitutionPosition::Expression && matches!(pattern, Value::Object(_)) {
        let ordinal = *cursor;
        if let Some((VariableSort::Expression, index)) = variable_parts(pattern) {
            if let Some(value) = bindings.get(&(VariableSort::Expression, index)) {
                overrides.insert(ordinal, value.clone());
            }
            *cursor += expression_node_count(concrete, position);
            return;
        }
        *cursor += 1;
    }
    match (pattern, concrete) {
        (Value::Object(pattern), Value::Object(concrete)) => {
            for key in canonical_object_keys(pattern) {
                if let Some(value) = concrete.get(key) {
                    collect_target_syntax_overrides(
                        &pattern[key],
                        value,
                        child_substitution_position(pattern, key),
                        bindings,
                        cursor,
                        overrides,
                    );
                }
            }
        }
        (Value::Array(pattern), Value::Array(concrete)) => {
            for (pattern, concrete) in pattern.iter().zip(concrete) {
                collect_target_syntax_overrides(
                    pattern, concrete, position, bindings, cursor, overrides,
                );
            }
        }
        _ => {}
    }
}

fn substituted_variable(
    sort: VariableSort,
    value: &Value,
    position: SubstitutionPosition,
) -> Option<Value> {
    match sort {
        VariableSort::Expression => {
            matches!(position, SubstitutionPosition::Expression).then(|| value.clone())
        }
        VariableSort::IntegerMagnitude => {
            matches!(position, SubstitutionPosition::Magnitude).then(|| value.clone())
        }
        _ => {
            let id = value.as_str()?.to_owned();
            match position {
                SubstitutionPosition::IdentityId | SubstitutionPosition::Other => {
                    Some(Value::String(id))
                }
                SubstitutionPosition::AdtIdentity => Some(value_object([
                    ("kind", Value::String("local".into())),
                    ("id", Value::String(id)),
                ])),
                SubstitutionPosition::ValueIdentity => {
                    let kind = match sort {
                        VariableSort::Anchor | VariableSort::Binding => "binding",
                        VariableSort::Function => "function",
                        VariableSort::Constant => "constant",
                        VariableSort::Static => "static",
                        VariableSort::Method => "method",
                        _ => return None,
                    };
                    Some(value_object([
                        ("kind", Value::String(kind.into())),
                        ("id", Value::String(id)),
                    ]))
                }
                _ => None,
            }
        }
    }
}

fn child_substitution_position(object: &Map<String, Value>, key: &str) -> SubstitutionPosition {
    let kind = object.get("kind").and_then(Value::as_str);
    use SubstitutionPosition::*;
    match (kind, key) {
        (Some("array" | "tuple"), "elements") => Expression,
        (Some("call"), "callee" | "arguments") => Expression,
        (Some("method_call"), "receiver" | "arguments") => Expression,
        (Some("method_call"), "method") => ValueIdentity,
        (Some("binary" | "assign" | "assign_op"), "left" | "right") => Expression,
        (Some("unary"), "operand") => Expression,
        (Some("cast"), "expression") => Expression,
        (Some("if"), "condition" | "else") => Expression,
        (Some("if"), "then") => Other,
        (Some("while"), "condition") => Expression,
        (Some("while" | "loop" | "block"), "body" | "block") => Other,
        (Some("match"), "scrutinee") => Expression,
        (Some("match"), "arms") => Other,
        (Some("match_arm"), "guard" | "body") => Expression,
        (Some("field"), "base") => Expression,
        (Some("index"), "base" | "index") => Expression,
        (Some("range"), "start" | "end") => Expression,
        (Some("path"), "value") => ValueIdentity,
        (Some("address_of"), "expression") => Expression,
        (Some("break" | "return"), "value") => Expression,
        (Some("struct"), "adt") | (Some("constructor"), "adt") => AdtIdentity,
        (Some("struct"), "rest") => Expression,
        (Some("repeat"), "value" | "count") => Expression,
        (Some("adt"), "identity") => AdtIdentity,
        (Some("local"), "owner") => AdtIdentity,
        (Some("local" | "binding"), "id") => IdentityId,
        (Some("integer"), "value") => Magnitude,
        (Some("expression"), "expression") => Expression,
        (Some("let"), "initializer") => Expression,
        (None, "statements") => Other,
        (None, "value") => Expression,
        _ => Other,
    }
}

fn substitute_value(
    pattern: &Value,
    state: &MatchState,
    position: SubstitutionPosition,
) -> Option<Value> {
    if let Some((sort, index)) = variable_parts(pattern) {
        return substituted_variable(sort, state.bindings.get(&(sort, index))?, position);
    }
    match pattern {
        Value::Object(object) => {
            let mut result = Map::new();
            for key in canonical_object_keys(object) {
                let position = child_substitution_position(object, key);
                result.insert(key.into(), substitute_value(&object[key], state, position)?);
            }
            Some(Value::Object(result))
        }
        Value::Array(values) => Some(Value::Array(
            values
                .iter()
                .map(|value| substitute_value(value, state, position))
                .collect::<Option<Vec<_>>>()?,
        )),
        _ => Some(pattern.clone()),
    }
}

fn substitute_normalized_target(rule: &Rule, state: &MatchState) -> Option<Expression> {
    let pattern = serde_json::to_value(&rule.target_pattern).ok()?;
    serde_json::from_value(substitute_value(
        &pattern,
        state,
        SubstitutionPosition::Expression,
    )?)
    .ok()
}

fn normalized_assignment_place(expression: &Expression) -> bool {
    match expression {
        Expression::Path { value } => matches!(
            value,
            crate::ValueIdentity::Binding { .. }
                | crate::ValueIdentity::Static { .. }
                | crate::ValueIdentity::ForeignStatic { .. }
                | crate::ValueIdentity::External { .. }
        ),
        Expression::Unary {
            operator: UnaryOperator::Deref,
            operand,
        } => normalized_assignment_place(operand),
        Expression::Field { base, .. } | Expression::Index { base, .. } => {
            normalized_assignment_place(base)
        }
        _ => false,
    }
}

fn semantic_sort_key<T: Serialize>(value: &T) -> String {
    compact(&serde_json::to_value(value).expect("serializing normalized terms cannot fail"))
}

impl LoadedRuleSet {
    pub fn new(document: &RuleDocument) -> Result<Self, DocumentError> {
        validate_rule_document(document)?;
        let rules = document.rules.clone();
        let mut alpha_groups = vec![usize::MAX; rules.len()];
        let mut representatives: Vec<usize> = vec![];
        for index in 0..rules.len() {
            let group = representatives
                .iter()
                .position(|&representative| {
                    source_pattern_at_least_as_specific(
                        &rules[index].source_pattern,
                        &rules[representative].source_pattern,
                    ) && source_pattern_at_least_as_specific(
                        &rules[representative].source_pattern,
                        &rules[index].source_pattern,
                    )
                })
                .unwrap_or_else(|| {
                    representatives.push(index);
                    representatives.len() - 1
                });
            alpha_groups[index] = group;
        }
        let mut strictly_more_specific_groups = vec![BTreeSet::new(); representatives.len()];
        for (left_group, &left) in representatives.iter().enumerate() {
            for (right_group, &right) in representatives.iter().enumerate().skip(left_group + 1) {
                let left_at_least = source_pattern_at_least_as_specific(
                    &rules[left].source_pattern,
                    &rules[right].source_pattern,
                );
                let right_at_least = source_pattern_at_least_as_specific(
                    &rules[right].source_pattern,
                    &rules[left].source_pattern,
                );
                if left_at_least && !right_at_least {
                    strictly_more_specific_groups[right_group].insert(left_group);
                }
                if right_at_least && !left_at_least {
                    strictly_more_specific_groups[left_group].insert(right_group);
                }
            }
        }
        Ok(Self {
            rules,
            alpha_groups,
            strictly_more_specific_groups,
        })
    }

    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }

    pub fn alpha_group(&self, rule_index: usize) -> Option<usize> {
        self.alpha_groups.get(rule_index).copied()
    }

    pub fn select(&self, input: &RuleMatchInput) -> Option<RuleSelection> {
        let mut excluded = BTreeSet::new();
        loop {
            let selection = self.select_with_exclusions(input, &excluded)?;
            if !input.lhs || normalized_assignment_place(&selection.target_expression) {
                return Some(selection);
            }
            excluded.insert(selection.rule_index);
        }
    }

    /// Selects the winning applicable rule after removing exactly the listed
    /// rules and rerunning the complete ranking pipeline. The returned target
    /// is normalized but has not passed syntax, scope, or assignment-place
    /// materialization checks.
    pub fn select_with_exclusions(
        &self,
        input: &RuleMatchInput,
        excluded: &BTreeSet<usize>,
    ) -> Option<RuleSelection> {
        self.select_with_exclusions_and_syntax(input, excluded, &[])
    }

    pub(crate) fn select_with_exclusions_and_syntax(
        &self,
        input: &RuleMatchInput,
        excluded: &BTreeSet<usize>,
        source_syntax: &[String],
    ) -> Option<RuleSelection> {
        let mut applicable = self
            .rules
            .iter()
            .enumerate()
            .filter_map(|(index, rule)| {
                if excluded.contains(&index) {
                    return None;
                }
                let state = rule_matches(rule, input)?;
                let target = substitute_normalized_target(rule, &state)?;
                Some((index, state, target))
            })
            .collect::<Vec<_>>();
        let applicable_groups = applicable
            .iter()
            .map(|(index, _, _)| self.alpha_groups[*index])
            .collect::<BTreeSet<_>>();
        applicable.retain(|(index, _, _)| {
            self.strictly_more_specific_groups[self.alpha_groups[*index]]
                .is_disjoint(&applicable_groups)
        });
        let minimum_cost = applicable
            .iter()
            .map(|(index, state, _)| substitution_cost(&self.rules[*index], state))
            .min()?;
        applicable.retain(|(index, state, _)| {
            substitution_cost(&self.rules[*index], state) == minimum_cost
        });
        let maximum_target = applicable
            .iter()
            .map(|(index, _, _)| {
                normalized_term_size(
                    &serde_json::to_value(&self.rules[*index].target_pattern).unwrap(),
                )
            })
            .max()?;
        applicable.retain(|(index, _, _)| {
            normalized_term_size(&serde_json::to_value(&self.rules[*index].target_pattern).unwrap())
                == maximum_target
        });
        applicable.sort_by_key(|(index, _, _)| {
            (
                semantic_sort_key(&self.rules[*index].target_pattern),
                semantic_sort_key(&self.rules[*index]),
            )
        });
        let (rule_index, state, target_expression) = applicable.into_iter().next()?;
        let mut syntax_bindings = BTreeMap::new();
        let mut cursor = 0;
        collect_source_expression_syntax(
            &serde_json::to_value(&self.rules[rule_index].source_pattern).ok()?,
            &serde_json::to_value(&input.source_expression).ok()?,
            SubstitutionPosition::Expression,
            source_syntax,
            &mut cursor,
            &mut syntax_bindings,
            None,
        );
        let mut syntax_overrides = BTreeMap::new();
        cursor = 0;
        collect_target_syntax_overrides(
            &serde_json::to_value(&self.rules[rule_index].target_pattern).ok()?,
            &serde_json::to_value(&target_expression).ok()?,
            SubstitutionPosition::Expression,
            &syntax_bindings,
            &mut cursor,
            &mut syntax_overrides,
        );
        let identity_syntax = syntax_bindings
            .iter()
            .filter_map(|(key, syntax)| {
                (key.0 != VariableSort::Expression).then(|| {
                    state
                        .bindings
                        .get(key)?
                        .as_str()
                        .map(|id| (id.to_owned(), syntax.clone()))
                })?
            })
            .collect();
        Some(RuleSelection {
            rule_index,
            alpha_group: self.alpha_groups[rule_index],
            target_expression,
            substitution_cost: minimum_cost,
            target_size: maximum_target,
            syntax_overrides,
            identity_syntax,
        })
    }
}

#[cfg(test)]
mod synthesis_parity_tests;

#[cfg(test)]
mod tests {
    use super::*;

    fn observation_json(lhs: bool) -> String {
        format!(
            r#"{{
  "schema_version": 1,
  "observations": [
    {{
      "source_expression": {{"kind":"path","value":{{"kind":"binding","id":"<id0>"}}}},
      "target_expression": {{"kind":"path","value":{{"kind":"binding","id":"<id0>"}}}},
      "pointer_anchors": [
        {{
          "id": "<id0>",
          "source_type": {{"kind":"raw_pointer","mutability":"const","pointee":{{"kind":"primitive","name":"i32"}}}},
          "target_type": {{"kind":"reference","mutability":"shared","pointee":{{"kind":"primitive","name":"i32"}}}}
        }}
      ],
      "lhs": {lhs},
      "source_type": {{"kind":"primitive","name":"i32"}},
      "source_adjusted_type": {{"kind":"primitive","name":"i32"}},
      "target_type": {{"kind":"primitive","name":"i32"}},
      "target_adjusted_type": {{"kind":"primitive","name":"i32"}}
    }}
  ]
}}"#
        )
    }

    fn observation(lhs: bool) -> ObservationDocument {
        observation_document_from_json(&observation_json(lhs)).unwrap()
    }

    fn primitive() -> TypeTree {
        TypeTree::Primitive { name: "i32".into() }
    }

    fn rule_primitive() -> RuleTypeTree {
        RuleTypeTree::Primitive { name: "i32".into() }
    }

    fn anchor_variable() -> RuleValueIdentity {
        RuleValueIdentity::Variable {
            sort: VariableSort::Anchor,
            index: 0,
        }
    }

    fn anchor_path() -> RuleExpression {
        RuleExpression::Path {
            value: anchor_variable(),
        }
    }

    fn expression_variable(index: u64) -> RuleExpression {
        RuleExpression::Variable {
            sort: VariableSort::Expression,
            index,
        }
    }

    fn concrete_binding(id: &str) -> Expression {
        Expression::Path {
            value: crate::ValueIdentity::Binding { id: id.into() },
        }
    }

    fn base_rule(source_pattern: RuleExpression, target_pattern: RuleExpression) -> Rule {
        Rule {
            source_pattern,
            target_pattern,
            pointer_anchors: vec![RulePointerAnchor {
                id: RuleVariable::new(VariableSort::Anchor, 0),
                source_type: RuleTypeTree::RawPointer {
                    mutability: RawMutability::Const,
                    pointee: Box::new(rule_primitive()),
                },
                target_type: RuleTypeTree::Reference {
                    mutability: RefMutability::Shared,
                    pointee: Box::new(rule_primitive()),
                },
            }],
            lhs: false,
            source_type: rule_primitive(),
            source_adjusted_type: rule_primitive(),
            target_type: rule_primitive(),
            target_adjusted_type: rule_primitive(),
        }
    }

    fn input(source_expression: Expression) -> RuleMatchInput {
        RuleMatchInput {
            source_expression,
            pointer_anchors: vec![crate::PointerAnchor {
                id: "<id0>".into(),
                source_type: TypeTree::RawPointer {
                    mutability: RawMutability::Const,
                    pointee: Box::new(primitive()),
                },
                target_type: TypeTree::Reference {
                    mutability: RefMutability::Shared,
                    pointee: Box::new(primitive()),
                },
            }],
            lhs: false,
            source_type: primitive(),
            source_adjusted_type: primitive(),
            target_type: Some(primitive()),
            target_adjusted_type: Some(primitive()),
        }
    }

    fn add_rule(left: RuleExpression, right: RuleExpression) -> RuleExpression {
        RuleExpression::Binary {
            operator: BinaryOperator::Add,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn add_expression(left: Expression, right: Expression) -> Expression {
        Expression::Binary {
            operator: BinaryOperator::Add,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn integer_rule(value: RuleIntegerMagnitude) -> RuleExpression {
        RuleExpression::Literal {
            value: RuleLiteral::Integer {
                value,
                ty: "i32".into(),
            },
        }
    }

    fn integer(value: &str) -> Expression {
        Expression::Literal {
            value: crate::Literal::Integer {
                value: value.into(),
                ty: "i32".into(),
            },
        }
    }

    fn binding_variable(index: u64) -> RuleExpression {
        RuleExpression::Path {
            value: RuleValueIdentity::Variable {
                sort: VariableSort::Binding,
                index,
            },
        }
    }

    fn function_variable(index: u64) -> RuleExpression {
        RuleExpression::Path {
            value: RuleValueIdentity::Variable {
                sort: VariableSort::Function,
                index,
            },
        }
    }

    fn external_value(crate_name: &str, path: &[&str]) -> RuleValueIdentity {
        RuleValueIdentity::External {
            crate_name: crate_name.into(),
            path: path.iter().map(|part| (*part).into()).collect(),
        }
    }

    fn concrete_external(crate_name: &str, path: &[&str]) -> crate::ValueIdentity {
        crate::ValueIdentity::External {
            crate_name: crate_name.into(),
            path: path.iter().map(|part| (*part).into()).collect(),
        }
    }

    fn rule_method(
        receiver: RuleExpression,
        method: RuleValueIdentity,
        arguments: Vec<RuleExpression>,
    ) -> RuleExpression {
        RuleExpression::MethodCall {
            receiver: Box::new(receiver),
            method,
            arguments,
        }
    }

    fn concrete_method(
        receiver: Expression,
        method: crate::ValueIdentity,
        arguments: Vec<Expression>,
    ) -> Expression {
        Expression::MethodCall {
            receiver: Box::new(receiver),
            method,
            arguments,
        }
    }

    fn offset(argument: RuleExpression) -> RuleExpression {
        rule_method(
            anchor_path(),
            external_value("core", &["ptr", "const_ptr", "offset"]),
            vec![argument],
        )
    }

    fn concrete_offset(argument: Expression) -> Expression {
        concrete_method(
            concrete_binding("<id0>"),
            concrete_external("core", &["ptr", "const_ptr", "offset"]),
            vec![argument],
        )
    }

    fn dereference_rule(expression: RuleExpression) -> RuleExpression {
        RuleExpression::Unary {
            operator: UnaryOperator::Deref,
            operand: Box::new(expression),
        }
    }

    fn dereference(expression: Expression) -> Expression {
        Expression::Unary {
            operator: UnaryOperator::Deref,
            operand: Box::new(expression),
        }
    }

    fn cast_rule(expression: RuleExpression) -> RuleExpression {
        RuleExpression::Cast {
            expression: Box::new(expression),
            ty: RuleTypeTree::Primitive {
                name: "isize".into(),
            },
        }
    }

    fn cast(expression: Expression) -> Expression {
        Expression::Cast {
            expression: Box::new(expression),
            ty: TypeTree::Primitive {
                name: "isize".into(),
            },
        }
    }

    #[test]
    fn lhs_is_required_and_canonically_ordered() {
        let document = observation(false);
        let serialized = observation_document_to_json(&document).unwrap();
        assert!(serialized.contains("      \"pointer_anchors\":"));
        let anchors = serialized.find("      \"pointer_anchors\":").unwrap();
        let lhs = serialized.find("      \"lhs\": false").unwrap();
        let source_type = lhs + serialized[lhs..].find("      \"source_type\":").unwrap();
        assert!(anchors < lhs && lhs < source_type);
        assert!(serialized.ends_with('\n'));

        for replacement in ["null", "0", "1", "\"false\"", "[]", "{}"] {
            assert!(
                observation_document_from_json(
                    &observation_json(false)
                        .replace("\"lhs\": false", &format!("\"lhs\": {replacement}"))
                )
                .is_err()
            );
        }
        assert!(
            observation_document_from_json(
                &observation_json(false).replace("      \"lhs\": false,\n", "")
            )
            .is_err()
        );
    }

    #[test]
    fn empty_documents_have_exact_bytes() {
        assert_eq!(
            observation_document_to_json(&ObservationDocument::default()).unwrap(),
            "{\n  \"schema_version\": 1,\n  \"observations\": []\n}\n"
        );
        assert_eq!(
            rule_document_to_json(&RuleDocument::default()).unwrap(),
            "{\n  \"schema_version\": 1,\n  \"rules\": []\n}\n"
        );
    }

    #[test]
    fn merge_preserves_document_and_producer_order_and_duplicates() {
        let false_document = observation(false);
        let true_document = observation(true);
        let merged = merge_observation_documents(&[
            ObservationDocument {
                schema_version: 1,
                observations: vec![
                    false_document.observations[0].clone(),
                    false_document.observations[0].clone(),
                ],
            },
            ObservationDocument::default(),
            true_document.clone(),
        ])
        .unwrap();
        assert_eq!(merged.observations.len(), 3);
        assert_eq!(
            merged
                .observations
                .iter()
                .map(|value| value.lhs)
                .collect::<Vec<_>>(),
            vec![false, false, true]
        );
        assert!(
            merge_observation_documents(&[])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn lhs_must_match_before_synthesis() {
        let left = observation(false);
        let right = observation(true);
        let result = synthesize_observation_pair(&left.observations[0], &right.observations[0]);
        assert_eq!(result.rejection, Some(PairRejection::Context));
        assert!(result.substitutions.is_empty());
    }

    #[test]
    fn synthesized_rule_preserves_lhs_and_separates_roles() {
        let false_document = observation(false);
        let true_document = observation(true);
        let rules = synthesize_rules(&[
            false_document.clone(),
            false_document,
            true_document.clone(),
            true_document,
        ])
        .unwrap();
        assert_eq!(rules.rules.len(), 2);
        assert_eq!(
            rules
                .rules
                .iter()
                .map(|rule| rule.lhs)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([false, true])
        );
        for rule in &rules.rules {
            assert_eq!(
                rule.pointer_anchors[0].id,
                RuleVariable::new(VariableSort::Anchor, 0)
            );
            assert!(matches!(rule.source_pattern, RuleExpression::Path { .. }));
        }
        let text = rule_document_to_json(&rules).unwrap();
        let anchors = text.find("      \"pointer_anchors\":").unwrap();
        let lhs = text.find("      \"lhs\":").unwrap();
        let source_type = lhs + text[lhs..].find("      \"source_type\":").unwrap();
        assert!(anchors < lhs && lhs < source_type);
        assert_eq!(rule_document_from_json(&text).unwrap(), rules);
    }

    #[test]
    fn missing_or_nonboolean_rule_lhs_rejects() {
        let document = observation(false);
        let rules = synthesize_rules(&[document.clone(), document]).unwrap();
        let text = rule_document_to_json(&rules).unwrap();
        assert!(rule_document_from_json(&text.replace("      \"lhs\": false,\n", "")).is_err());
        assert!(rule_document_from_json(&text.replace("\"lhs\": false", "\"lhs\": 0")).is_err());
    }

    #[test]
    fn source_matching_enforces_repetition_anchor_exclusion_and_identity_injectivity() {
        let repeated = base_rule(
            add_rule(expression_variable(0), expression_variable(0)),
            expression_variable(0),
        );
        assert!(
            rule_matches(
                &repeated,
                &input(add_expression(
                    concrete_binding("<id1>"),
                    concrete_binding("<id1>")
                ))
            )
            .is_some()
        );
        assert!(
            rule_matches(
                &repeated,
                &input(add_expression(
                    concrete_binding("<id1>"),
                    concrete_binding("<id2>")
                ))
            )
            .is_none()
        );

        let expression_carrier = base_rule(
            add_rule(anchor_path(), expression_variable(0)),
            expression_variable(0),
        );
        assert!(
            rule_matches(
                &expression_carrier,
                &input(add_expression(
                    concrete_binding("<id0>"),
                    concrete_binding("<id1>")
                ))
            )
            .is_some()
        );
        assert!(
            rule_matches(
                &expression_carrier,
                &input(add_expression(
                    concrete_binding("<id0>"),
                    concrete_binding("<id0>")
                ))
            )
            .is_none()
        );

        let binding = RuleExpression::Path {
            value: RuleValueIdentity::Variable {
                sort: VariableSort::Binding,
                index: 0,
            },
        };
        let joint_identity = base_rule(add_rule(anchor_path(), binding), anchor_path());
        assert!(
            rule_matches(
                &joint_identity,
                &input(add_expression(
                    concrete_binding("<id0>"),
                    concrete_binding("<id0>")
                ))
            )
            .is_none()
        );
    }

    #[test]
    fn expression_variables_match_simple_compound_and_repeated_subtrees() {
        let simple = base_rule(
            dereference_rule(offset(cast_rule(expression_variable(0)))),
            anchor_path(),
        );
        for candidate in [
            concrete_binding("<id1>"),
            add_expression(concrete_binding("<id1>"), integer("1")),
        ] {
            assert!(
                rule_matches(
                    &simple,
                    &input(dereference(concrete_offset(cast(candidate))))
                )
                .is_some()
            );
        }

        let repeated = base_rule(
            dereference_rule(offset(cast_rule(add_rule(
                expression_variable(0),
                expression_variable(0),
            )))),
            anchor_path(),
        );
        assert!(
            rule_matches(
                &repeated,
                &input(dereference(concrete_offset(cast(add_expression(
                    concrete_binding("<id1>"),
                    concrete_binding("<id1>"),
                )))))
            )
            .is_some()
        );
        assert!(
            rule_matches(
                &repeated,
                &input(dereference(concrete_offset(cast(add_expression(
                    concrete_binding("<id1>"),
                    concrete_binding("<id2>"),
                )))))
            )
            .is_none()
        );
    }

    #[test]
    fn expression_carriers_reject_anchor_containment_and_split_locals() {
        let one_carrier = base_rule(
            dereference_rule(offset(expression_variable(0))),
            anchor_path(),
        );
        assert!(
            rule_matches(
                &one_carrier,
                &input(dereference(concrete_offset(cast(concrete_binding(
                    "<id0>"
                )))))
            )
            .is_none()
        );
        assert!(
            rule_matches(
                &one_carrier,
                &input(dereference(concrete_offset(cast(add_expression(
                    concrete_binding("<id1>"),
                    integer("1"),
                )))))
            )
            .is_some()
        );

        let split_expressions = base_rule(
            dereference_rule(offset(add_rule(
                expression_variable(0),
                expression_variable(1),
            ))),
            anchor_path(),
        );
        assert!(
            rule_matches(
                &split_expressions,
                &input(dereference(concrete_offset(add_expression(
                    cast(concrete_binding("<id1>")),
                    cast(concrete_binding("<id1>")),
                ))))
            )
            .is_none()
        );
        assert!(
            rule_matches(
                &split_expressions,
                &input(dereference(concrete_offset(add_expression(
                    integer("1"),
                    integer("1"),
                ))))
            )
            .is_some()
        );
    }

    #[test]
    fn explicit_identity_carriers_are_jointly_injective_and_cannot_split() {
        let anchor_and_binding = base_rule(
            dereference_rule(offset(cast_rule(binding_variable(0)))),
            anchor_path(),
        );
        assert!(
            rule_matches(
                &anchor_and_binding,
                &input(dereference(concrete_offset(cast(concrete_binding(
                    "<id0>"
                )))))
            )
            .is_none()
        );

        let branch = |condition, tail| RuleExpression::If {
            condition: Box::new(condition),
            then: RuleBlock {
                statements: vec![RuleStatement::Expression {
                    expression: tail,
                    semicolon: false,
                }],
            },
            else_expression: Some(Box::new(integer_rule(RuleIntegerMagnitude::Fixed(
                "0".into(),
            )))),
        };
        let concrete_branch = |condition, tail| Expression::If {
            condition: Box::new(condition),
            then: crate::Block {
                statements: vec![crate::Statement::Expression {
                    expression: tail,
                    semicolon: false,
                }],
            },
            else_expression: Some(Box::new(integer("0"))),
        };
        let split = base_rule(
            dereference_rule(offset(branch(binding_variable(0), expression_variable(0)))),
            anchor_path(),
        );
        assert!(
            rule_matches(
                &split,
                &input(dereference(concrete_offset(concrete_branch(
                    concrete_binding("<id1>"),
                    cast(concrete_binding("<id1>")),
                ))))
            )
            .is_none()
        );

        let distinct = base_rule(
            dereference_rule(offset(cast_rule(RuleExpression::Binary {
                operator: BinaryOperator::Subtract,
                left: Box::new(binding_variable(0)),
                right: Box::new(binding_variable(1)),
            }))),
            anchor_path(),
        );
        assert!(
            rule_matches(
                &distinct,
                &input(dereference(concrete_offset(cast(Expression::Binary {
                    operator: BinaryOperator::Subtract,
                    left: Box::new(concrete_binding("<id1>")),
                    right: Box::new(concrete_binding("<id1>")),
                }))))
            )
            .is_none()
        );
    }

    #[test]
    fn integer_magnitudes_and_fixed_methods_match_rigidly() {
        let magnitude = base_rule(
            dereference_rule(offset(integer_rule(RuleIntegerMagnitude::Variable(
                RuleVariable::new(VariableSort::IntegerMagnitude, 0),
            )))),
            anchor_path(),
        );
        assert!(
            rule_matches(
                &magnitude,
                &input(dereference(concrete_offset(integer("4"))))
            )
            .is_some()
        );

        let fixed = base_rule(
            dereference_rule(offset(integer_rule(RuleIntegerMagnitude::Fixed(
                "1".into(),
            )))),
            anchor_path(),
        );
        assert!(rule_matches(&fixed, &input(dereference(concrete_offset(integer("2"))))).is_none());
        let add = concrete_method(
            concrete_binding("<id0>"),
            concrete_external("core", &["ptr", "const_ptr", "add"]),
            vec![integer("1")],
        );
        assert!(rule_matches(&fixed, &input(dereference(add))).is_none());
    }

    #[test]
    fn normalized_integer_magnitudes_accept_ascii_digits_only() {
        for invalid in ["", "١", "Ⅳ", "1²"] {
            let rule = base_rule(
                integer_rule(RuleIntegerMagnitude::Fixed(invalid.into())),
                anchor_path(),
            );
            assert!(
                LoadedRuleSet::new(&RuleDocument {
                    schema_version: 1,
                    rules: vec![rule],
                })
                .is_err(),
                "{invalid:?}"
            );
        }
        for valid in ["0", "1", "10", "1234567890"] {
            let rule = base_rule(
                integer_rule(RuleIntegerMagnitude::Fixed(valid.into())),
                anchor_path(),
            );
            assert!(
                LoadedRuleSet::new(&RuleDocument {
                    schema_version: 1,
                    rules: vec![rule],
                })
                .is_ok(),
                "{valid}"
            );
        }
    }

    #[test]
    fn repeated_anchors_agree_and_distinct_anchors_are_ordered() {
        let repeated = base_rule(
            RuleExpression::Binary {
                operator: BinaryOperator::Equal,
                left: Box::new(dereference_rule(anchor_path())),
                right: Box::new(dereference_rule(anchor_path())),
            },
            anchor_path(),
        );
        let equal = Expression::Binary {
            operator: BinaryOperator::Equal,
            left: Box::new(dereference(concrete_binding("<id0>"))),
            right: Box::new(dereference(concrete_binding("<id0>"))),
        };
        assert!(rule_matches(&repeated, &input(equal)).is_some());

        let mut unequal_input = input(Expression::Binary {
            operator: BinaryOperator::Equal,
            left: Box::new(dereference(concrete_binding("<id0>"))),
            right: Box::new(dereference(concrete_binding("<id1>"))),
        });
        unequal_input.pointer_anchors.push(crate::PointerAnchor {
            id: "<id1>".into(),
            source_type: unequal_input.pointer_anchors[0].source_type.clone(),
            target_type: unequal_input.pointer_anchors[0].target_type.clone(),
        });
        assert!(rule_matches(&repeated, &unequal_input).is_none());
    }

    #[test]
    fn local_function_variables_match_only_local_function_identities() {
        let rule = base_rule(
            RuleExpression::Call {
                callee: Box::new(function_variable(0)),
                arguments: vec![anchor_path()],
            },
            anchor_path(),
        );
        let call = |callee| Expression::Call {
            callee: Box::new(Expression::Path { value: callee }),
            arguments: vec![concrete_binding("<id0>")],
        };
        assert!(
            rule_matches(
                &rule,
                &input(call(crate::ValueIdentity::Function { id: "<fn0>".into() }))
            )
            .is_some()
        );
        for callee in [
            concrete_external("libc", &["free"]),
            crate::ValueIdentity::ForeignFunction {
                symbol: "free".into(),
            },
        ] {
            assert!(rule_matches(&rule, &input(call(callee))).is_none());
        }

        let rigid = base_rule(
            RuleExpression::Call {
                callee: Box::new(RuleExpression::Path {
                    value: external_value("libc", &["free"]),
                }),
                arguments: vec![anchor_path()],
            },
            anchor_path(),
        );
        assert!(rule_matches(&rigid, &input(call(concrete_external("libc", &["free"])))).is_some());
    }

    #[test]
    fn every_match_context_component_is_exact() {
        let raw = RuleTypeTree::RawPointer {
            mutability: RawMutability::Const,
            pointee: Box::new(rule_primitive()),
        };
        let reference = RuleTypeTree::Reference {
            mutability: RefMutability::Shared,
            pointee: Box::new(rule_primitive()),
        };
        let mut rule = base_rule(anchor_path(), anchor_path());
        rule.source_type = raw.clone();
        rule.source_adjusted_type = raw;
        rule.target_type = reference.clone();
        rule.target_adjusted_type = reference;
        let mut region = input(concrete_binding("<id0>"));
        region.source_type = region.pointer_anchors[0].source_type.clone();
        region.source_adjusted_type = region.source_type.clone();
        region.target_type = Some(region.pointer_anchors[0].target_type.clone());
        region.target_adjusted_type = region.target_type.clone();
        assert!(rule_matches(&rule, &region).is_some());

        let mut mismatches = vec![];
        let mut changed = region.clone();
        changed.lhs = true;
        mismatches.push(changed);
        let mut changed = region.clone();
        changed.pointer_anchors.clear();
        mismatches.push(changed);
        let mut changed = region.clone();
        changed.pointer_anchors[0].source_type = primitive();
        mismatches.push(changed);
        let mut changed = region.clone();
        changed.pointer_anchors[0].target_type = primitive();
        mismatches.push(changed);
        let mut changed = region.clone();
        changed.source_type = primitive();
        mismatches.push(changed);
        let mut changed = region.clone();
        changed.source_adjusted_type = primitive();
        mismatches.push(changed);
        let mut changed = region.clone();
        changed.target_adjusted_type = Some(primitive());
        mismatches.push(changed);
        for changed in mismatches {
            assert!(rule_matches(&rule, &changed).is_none());
        }

        let anchor_one = RuleExpression::Path {
            value: RuleValueIdentity::Variable {
                sort: VariableSort::Anchor,
                index: 1,
            },
        };
        let mut ordered_rule = base_rule(add_rule(anchor_path(), anchor_one), anchor_path());
        ordered_rule.pointer_anchors.push(RulePointerAnchor {
            id: RuleVariable::new(VariableSort::Anchor, 1),
            source_type: ordered_rule.pointer_anchors[0].source_type.clone(),
            target_type: ordered_rule.pointer_anchors[0].target_type.clone(),
        });
        let mut ordered_input = input(add_expression(
            concrete_binding("<id0>"),
            concrete_binding("<id1>"),
        ));
        ordered_input.pointer_anchors.push(crate::PointerAnchor {
            id: "<id1>".into(),
            source_type: ordered_input.pointer_anchors[0].source_type.clone(),
            target_type: ordered_input.pointer_anchors[0].target_type.clone(),
        });
        assert!(rule_matches(&ordered_rule, &ordered_input).is_some());
        ordered_input.pointer_anchors.swap(0, 1);
        assert!(rule_matches(&ordered_rule, &ordered_input).is_none());
    }

    #[test]
    fn local_function_variable_does_not_match_external_identity() {
        let function = RuleExpression::Path {
            value: RuleValueIdentity::Variable {
                sort: VariableSort::Function,
                index: 0,
            },
        };
        let rule = base_rule(
            RuleExpression::Call {
                callee: Box::new(function),
                arguments: vec![anchor_path()],
            },
            anchor_path(),
        );
        let external = Expression::Path {
            value: crate::ValueIdentity::External {
                crate_name: "libc".into(),
                path: vec!["free".into()],
            },
        };
        let concrete = Expression::Call {
            callee: Box::new(external),
            arguments: vec![concrete_binding("<id0>")],
        };
        assert!(rule_matches(&rule, &input(concrete)).is_none());
    }

    #[test]
    fn lhs_and_type_context_are_exact() {
        let rule = base_rule(anchor_path(), anchor_path());
        let mut region = input(concrete_binding("<id0>"));
        assert!(rule_matches(&rule, &region).is_some());
        region.lhs = true;
        assert!(rule_matches(&rule, &region).is_none());
        region.lhs = false;
        region.pointer_anchors[0].target_type = TypeTree::Reference {
            mutability: RefMutability::Mutable,
            pointee: Box::new(primitive()),
        };
        assert!(rule_matches(&rule, &region).is_none());
    }

    #[test]
    fn directional_specificity_respects_structure_repetition_and_rigid_externals() {
        let fixed = add_rule(
            anchor_path(),
            integer_rule(RuleIntegerMagnitude::Fixed("1".into())),
        );
        let magnitude = add_rule(
            anchor_path(),
            integer_rule(RuleIntegerMagnitude::Variable(RuleVariable::new(
                VariableSort::IntegerMagnitude,
                0,
            ))),
        );
        assert!(source_pattern_at_least_as_specific(&fixed, &magnitude));
        assert!(!source_pattern_at_least_as_specific(&magnitude, &fixed));

        let repeated = add_rule(expression_variable(0), expression_variable(0));
        let distinct = add_rule(expression_variable(0), expression_variable(1));
        assert!(source_pattern_at_least_as_specific(&repeated, &distinct));
        assert!(!source_pattern_at_least_as_specific(&distinct, &repeated));

        let external = RuleExpression::Path {
            value: RuleValueIdentity::External {
                crate_name: "libc".into(),
                path: vec!["free".into()],
            },
        };
        let variable = RuleExpression::Path {
            value: RuleValueIdentity::Variable {
                sort: VariableSort::Function,
                index: 0,
            },
        };
        assert!(!source_pattern_at_least_as_specific(&external, &variable));
        assert!(!source_pattern_at_least_as_specific(&variable, &external));
    }

    #[test]
    fn directional_specificity_covers_all_structural_relations() {
        #[derive(Clone, Copy, Debug)]
        enum Relation {
            LeftStrict,
            Equal,
            Incomparable,
        }
        let method_variable = || RuleValueIdentity::Variable {
            sort: VariableSort::Method,
            index: 0,
        };
        let local_method = |argument| rule_method(anchor_path(), method_variable(), vec![argument]);
        let pointer_offset = |argument| dereference_rule(offset(argument));
        let call = |argument| RuleExpression::Call {
            callee: Box::new(function_variable(0)),
            arguments: vec![anchor_path(), argument],
        };
        let fixed = |value: &str| integer_rule(RuleIntegerMagnitude::Fixed(value.to_owned()));
        let magnitude = || {
            integer_rule(RuleIntegerMagnitude::Variable(RuleVariable::new(
                VariableSort::IntegerMagnitude,
                0,
            )))
        };
        let binary = |operator, left, right| RuleExpression::Binary {
            operator,
            left: Box::new(left),
            right: Box::new(right),
        };
        let field = RuleExpression::Field {
            base: Box::new(dereference_rule(anchor_path())),
            field: RuleMemberIdentity::External {
                crate_name: "fixture".into(),
                path: vec!["Record".into(), "field".into()],
            },
        };
        let index = RuleExpression::Index {
            base: Box::new(dereference_rule(anchor_path())),
            index: Box::new(expression_variable(0)),
        };
        let rigid_is_null = rule_method(
            anchor_path(),
            external_value("core", &["ptr", "const_ptr", "is_null"]),
            vec![],
        );
        let local_is_null = rule_method(anchor_path(), method_variable(), vec![]);
        let external_call = RuleExpression::Call {
            callee: Box::new(RuleExpression::Path {
                value: external_value("libc", &["free"]),
            }),
            arguments: vec![anchor_path()],
        };
        let local_call = RuleExpression::Call {
            callee: Box::new(function_variable(0)),
            arguments: vec![anchor_path()],
        };
        let cases = vec![
            (
                "fixed magnitude versus magnitude variable",
                pointer_offset(fixed("1")),
                pointer_offset(magnitude()),
                Relation::LeftStrict,
            ),
            (
                "binding carrier versus expression carrier",
                pointer_offset(cast_rule(binding_variable(0))),
                pointer_offset(expression_variable(0)),
                Relation::LeftStrict,
            ),
            (
                "repeated versus distinct expression variables",
                pointer_offset(add_rule(expression_variable(0), expression_variable(0))),
                pointer_offset(add_rule(expression_variable(0), expression_variable(1))),
                Relation::LeftStrict,
            ),
            (
                "structured expression versus expression variable",
                pointer_offset(add_rule(expression_variable(0), fixed("1"))),
                pointer_offset(expression_variable(0)),
                Relation::LeftStrict,
            ),
            (
                "method binding argument versus expression argument",
                local_method(cast_rule(binding_variable(0))),
                local_method(expression_variable(0)),
                Relation::LeftStrict,
            ),
            (
                "call structured argument versus expression argument",
                call(add_rule(expression_variable(0), fixed("1"))),
                call(expression_variable(0)),
                Relation::LeftStrict,
            ),
            (
                "identical patterns",
                pointer_offset(expression_variable(0)),
                pointer_offset(expression_variable(0)),
                Relation::Equal,
            ),
            (
                "alpha-renamed operand variables",
                pointer_offset(binary(
                    BinaryOperator::Subtract,
                    expression_variable(0),
                    expression_variable(1),
                )),
                pointer_offset(binary(
                    BinaryOperator::Subtract,
                    expression_variable(1),
                    expression_variable(0),
                )),
                Relation::Equal,
            ),
            (
                "different fixed magnitudes",
                pointer_offset(fixed("1")),
                pointer_offset(fixed("2")),
                Relation::Incomparable,
            ),
            (
                "different operand order",
                pointer_offset(add_rule(expression_variable(0), fixed("1"))),
                pointer_offset(add_rule(fixed("1"), expression_variable(0))),
                Relation::Incomparable,
            ),
            (
                "different fixed methods",
                pointer_offset(expression_variable(0)),
                dereference_rule(rule_method(
                    anchor_path(),
                    external_value("core", &["ptr", "const_ptr", "add"]),
                    vec![expression_variable(0)],
                )),
                Relation::Incomparable,
            ),
            (
                "repetition versus fixed structure",
                pointer_offset(add_rule(expression_variable(0), expression_variable(0))),
                pointer_offset(add_rule(expression_variable(0), fixed("1"))),
                Relation::Incomparable,
            ),
            ("field versus index", field, index, Relation::Incomparable),
            (
                "external method versus local method variable",
                rigid_is_null,
                local_is_null,
                Relation::Incomparable,
            ),
            (
                "external callee versus local function variable",
                external_call,
                local_call,
                Relation::Incomparable,
            ),
        ];
        for (name, left, right, relation) in cases {
            let left_at_least = source_pattern_at_least_as_specific(&left, &right);
            let right_at_least = source_pattern_at_least_as_specific(&right, &left);
            let expected = match relation {
                Relation::LeftStrict => (true, false),
                Relation::Equal => (true, true),
                Relation::Incomparable => (false, false),
            };
            assert_eq!((left_at_least, right_at_least), expected, "{name}");
        }
    }

    #[test]
    fn context_does_not_change_source_alpha_equivalence() {
        let source = dereference_rule(offset(expression_variable(0)));
        let left = base_rule(source.clone(), anchor_path());
        let mut right = base_rule(source, anchor_path());
        right.lhs = true;
        right.pointer_anchors[0].target_type = RuleTypeTree::Reference {
            mutability: RefMutability::Mutable,
            pointee: Box::new(rule_primitive()),
        };
        right.target_type = RuleTypeTree::Primitive {
            name: "usize".into(),
        };
        let loaded = LoadedRuleSet::new(&RuleDocument {
            schema_version: 1,
            rules: vec![left, right],
        })
        .unwrap();
        assert_eq!(loaded.alpha_group(0), loaded.alpha_group(1));
    }

    #[test]
    fn selection_prefers_specific_then_larger_target_then_canonical_json() {
        let general_source = add_rule(
            anchor_path(),
            integer_rule(RuleIntegerMagnitude::Variable(RuleVariable::new(
                VariableSort::IntegerMagnitude,
                0,
            ))),
        );
        let fixed_source = add_rule(
            anchor_path(),
            integer_rule(RuleIntegerMagnitude::Fixed("1".into())),
        );
        let general = base_rule(general_source, anchor_path());
        let broad = base_rule(
            add_rule(anchor_path(), expression_variable(0)),
            integer_rule(RuleIntegerMagnitude::Fixed("8".into())),
        );
        let specific_target = RuleExpression::Unary {
            operator: UnaryOperator::Deref,
            operand: Box::new(anchor_path()),
        };
        let specific = base_rule(fixed_source.clone(), specific_target.clone());
        let loaded = LoadedRuleSet::new(&RuleDocument {
            schema_version: 1,
            rules: vec![broad, general, specific],
        })
        .unwrap();
        let selected = loaded
            .select(&input(add_expression(
                concrete_binding("<id0>"),
                integer("1"),
            )))
            .unwrap();
        assert_eq!(
            selected.target_expression,
            Expression::Unary {
                operator: UnaryOperator::Deref,
                operand: Box::new(concrete_binding("<id0>"))
            }
        );

        let one = base_rule(
            fixed_source.clone(),
            integer_rule(RuleIntegerMagnitude::Fixed("1".into())),
        );
        let two = base_rule(
            fixed_source,
            integer_rule(RuleIntegerMagnitude::Fixed("2".into())),
        );
        for rules in [vec![two.clone(), one.clone()], vec![one, two]] {
            let selected = LoadedRuleSet::new(&RuleDocument {
                schema_version: 1,
                rules,
            })
            .unwrap()
            .select(&input(add_expression(
                concrete_binding("<id0>"),
                integer("1"),
            )))
            .unwrap();
            assert_eq!(selected.target_expression, integer("1"));
        }
    }

    #[test]
    fn ranking_prefers_specificity_then_distinct_source_substitution_cost() {
        let concrete = Expression::Tuple {
            elements: vec![
                add_expression(concrete_binding("<id1>"), integer("1")),
                add_expression(concrete_binding("<id1>"), integer("1")),
                integer("0"),
            ],
        };
        let repeated = base_rule(
            RuleExpression::Tuple {
                elements: vec![
                    expression_variable(0),
                    expression_variable(0),
                    integer_rule(RuleIntegerMagnitude::Fixed("0".into())),
                ],
            },
            integer_rule(RuleIntegerMagnitude::Fixed("7".into())),
        );
        let decomposed = base_rule(
            RuleExpression::Tuple {
                elements: vec![
                    add_rule(expression_variable(0), expression_variable(1)),
                    add_rule(expression_variable(0), expression_variable(1)),
                    expression_variable(2),
                ],
            },
            integer_rule(RuleIntegerMagnitude::Fixed("9".into())),
        );
        assert!(!source_pattern_at_least_as_specific(
            &repeated.source_pattern,
            &decomposed.source_pattern
        ));
        assert!(!source_pattern_at_least_as_specific(
            &decomposed.source_pattern,
            &repeated.source_pattern
        ));
        let repeated_state = rule_matches(&repeated, &input(concrete.clone())).unwrap();
        let decomposed_state = rule_matches(&decomposed, &input(concrete.clone())).unwrap();
        assert_eq!(substitution_cost(&repeated, &repeated_state), 8);
        assert_eq!(substitution_cost(&decomposed, &decomposed_state), 10);
        assert_eq!(
            LoadedRuleSet::new(&RuleDocument {
                schema_version: 1,
                rules: vec![decomposed, repeated],
            })
            .unwrap()
            .select(&input(concrete))
            .unwrap()
            .target_expression,
            integer("7")
        );

        let expression_source = expression_variable(0);
        let mut context_only = base_rule(
            expression_source,
            integer_rule(RuleIntegerMagnitude::Fixed("3".into())),
        );
        context_only.source_type = RuleTypeTree::Adt {
            adt_kind: AdtKind::Struct,
            identity: RuleAdtIdentity::Variable {
                sort: VariableSort::Struct,
                index: 0,
            },
            arguments: vec![],
        };
        let mut state = MatchState::default();
        state.bindings.insert(
            (VariableSort::Expression, 0),
            serde_json::to_value(integer("1")).unwrap(),
        );
        state
            .bindings
            .insert((VariableSort::Struct, 0), serde_json::json!("<struct0>"));
        assert_eq!(substitution_cost(&context_only, &state), 4);
    }

    #[test]
    fn ranking_uses_target_size_and_canonical_order_independently_of_document_order() {
        let source = add_rule(
            anchor_path(),
            integer_rule(RuleIntegerMagnitude::Fixed("1".into())),
        );
        let small = base_rule(
            source.clone(),
            integer_rule(RuleIntegerMagnitude::Fixed("1".into())),
        );
        let large_target = add_rule(
            integer_rule(RuleIntegerMagnitude::Fixed("1".into())),
            integer_rule(RuleIntegerMagnitude::Fixed("2".into())),
        );
        let large = base_rule(source.clone(), large_target.clone());
        let concrete = input(add_expression(concrete_binding("<id0>"), integer("1")));
        for rules in [
            vec![small.clone(), large.clone()],
            vec![large.clone(), small],
        ] {
            let selected = LoadedRuleSet::new(&RuleDocument {
                schema_version: 1,
                rules,
            })
            .unwrap()
            .select(&concrete)
            .unwrap();
            assert_eq!(
                selected.target_expression,
                add_expression(integer("1"), integer("2"))
            );
            assert_eq!(
                selected.target_size,
                normalized_term_size(&serde_json::to_value(&large_target).unwrap())
            );
        }

        let first = base_rule(
            source.clone(),
            integer_rule(RuleIntegerMagnitude::Fixed("1".into())),
        );
        let second = base_rule(
            source,
            integer_rule(RuleIntegerMagnitude::Fixed("2".into())),
        );
        for rules in [vec![second.clone(), first.clone()], vec![first, second]] {
            assert_eq!(
                LoadedRuleSet::new(&RuleDocument {
                    schema_version: 1,
                    rules,
                })
                .unwrap()
                .select(&concrete)
                .unwrap()
                .target_expression,
                integer("1")
            );
        }
    }

    #[test]
    fn exclusions_rerun_the_complete_ranking_pipeline() {
        let general = base_rule(
            add_rule(
                anchor_path(),
                integer_rule(RuleIntegerMagnitude::Variable(RuleVariable::new(
                    VariableSort::IntegerMagnitude,
                    0,
                ))),
            ),
            integer_rule(RuleIntegerMagnitude::Fixed("7".into())),
        );
        let specific = base_rule(
            add_rule(
                anchor_path(),
                integer_rule(RuleIntegerMagnitude::Fixed("1".into())),
            ),
            integer_rule(RuleIntegerMagnitude::Fixed("9".into())),
        );
        let loaded = LoadedRuleSet::new(&RuleDocument {
            schema_version: 1,
            rules: vec![general, specific],
        })
        .unwrap();
        let input = input(add_expression(concrete_binding("<id0>"), integer("1")));
        let first = loaded
            .select_with_exclusions(&input, &BTreeSet::new())
            .unwrap();
        assert_eq!(first.target_expression, integer("9"));
        let second = loaded
            .select_with_exclusions(&input, &BTreeSet::from([first.rule_index]))
            .unwrap();
        assert_eq!(second.target_expression, integer("7"));
    }

    #[test]
    fn expression_syntax_provenance_distinguishes_equal_metavariables() {
        let rule = base_rule(
            add_rule(expression_variable(0), expression_variable(1)),
            expression_variable(1),
        );
        let loaded = LoadedRuleSet::new(&RuleDocument {
            schema_version: 1,
            rules: vec![rule],
        })
        .unwrap();
        let selected = loaded
            .select_with_exclusions_and_syntax(
                &input(add_expression(integer("1"), integer("1"))),
                &BTreeSet::new(),
                &["1 + (1)".into(), "1".into(), "(1)".into()],
            )
            .unwrap();
        assert_eq!(
            selected.syntax_overrides.get(&0).map(String::as_str),
            Some("(1)")
        );
    }

    #[test]
    fn dormant_target_context_variable_excludes_only_that_candidate() {
        let mut dormant = base_rule(anchor_path(), anchor_path());
        let raw_source = RuleTypeTree::RawPointer {
            mutability: RawMutability::Const,
            pointee: Box::new(rule_primitive()),
        };
        dormant.source_type = raw_source.clone();
        dormant.source_adjusted_type = raw_source.clone();
        dormant.target_type = RuleTypeTree::Adt {
            adt_kind: AdtKind::Struct,
            identity: RuleAdtIdentity::Variable {
                sort: VariableSort::Struct,
                index: 0,
            },
            arguments: vec![],
        };
        dormant.target_pattern = RuleExpression::Struct {
            adt: RuleAdtIdentity::Variable {
                sort: VariableSort::Struct,
                index: 0,
            },
            variant: None,
            fields: vec![],
            rest: None,
        };
        let mut fallback = base_rule(anchor_path(), anchor_path());
        fallback.source_type = raw_source.clone();
        fallback.source_adjusted_type = raw_source;
        let loaded = LoadedRuleSet::new(&RuleDocument {
            schema_version: 1,
            rules: vec![dormant.clone(), fallback],
        })
        .unwrap();
        let mut pointer_input = input(concrete_binding("<id0>"));
        pointer_input.source_type = pointer_input.pointer_anchors[0].source_type.clone();
        pointer_input.source_adjusted_type = pointer_input.source_type.clone();
        assert_eq!(
            loaded.select(&pointer_input).unwrap().target_expression,
            concrete_binding("<id0>")
        );
        assert!(
            LoadedRuleSet::new(&RuleDocument {
                schema_version: 1,
                rules: vec![dormant],
            })
            .unwrap()
            .select(&pointer_input)
            .is_none()
        );
    }

    #[test]
    fn synthesis_and_round_trip_retain_dormant_target_intrinsic_variables() {
        let local = |index| TypeTree::Adt {
            adt_kind: AdtKind::Struct,
            identity: crate::AdtIdentity::Local {
                id: format!("<struct{index}>"),
            },
            arguments: vec![],
        };
        let mut first = observation(false);
        first.observations[0].target_type = local(0);
        let mut second = observation(false);
        second.observations[0].target_type = local(0);
        let pair = synthesize_observation_pair(&first.observations[0], &second.observations[0]);
        let synthesized = RuleDocument {
            schema_version: 1,
            rules: vec![pair.rule.unwrap_or_else(|| panic!("{:?}", pair.rejection))],
        };
        let json = rule_document_to_json(&synthesized).unwrap();
        let reloaded = rule_document_from_json(&json).unwrap();
        assert_eq!(reloaded, synthesized);
        assert!(json.contains("\"sort\": \"struct\""), "{json}");
        assert!(matches!(
            synthesized.rules[0].target_type,
            RuleTypeTree::Adt {
                identity: RuleAdtIdentity::Variable { .. },
                ..
            }
        ));
    }

    #[test]
    fn normalized_size_counts_exact_grammar_terms_not_json_containers() {
        assert_eq!(
            normalized_term_size(&serde_json::to_value(expression_variable(0)).unwrap()),
            1
        );
        assert_eq!(
            normalized_term_size(&serde_json::to_value(anchor_path()).unwrap()),
            2
        );
        let unary = RuleExpression::Unary {
            operator: UnaryOperator::Deref,
            operand: Box::new(anchor_path()),
        };
        assert_eq!(
            normalized_term_size(&serde_json::to_value(unary).unwrap()),
            4
        );
        let path = anchor_path();
        assert_eq!(
            normalized_term_size(&serde_json::to_value(&path).unwrap()),
            2
        );
        assert_eq!(
            normalized_term_size(
                &serde_json::to_value(add_rule(path.clone(), path.clone())).unwrap()
            ),
            6
        );
        let call = RuleExpression::Call {
            callee: Box::new(path.clone()),
            arguments: vec![path.clone(), path],
        };
        assert_eq!(
            normalized_term_size(&serde_json::to_value(call).unwrap()),
            7
        );
        assert_eq!(
            normalized_term_size(
                &serde_json::to_value(integer_rule(RuleIntegerMagnitude::Fixed("1".into())))
                    .unwrap()
            ),
            4
        );
    }

    #[test]
    fn pointer_like_types_require_the_resolved_standard_constructors() {
        let reference = TypeTree::Reference {
            mutability: RefMutability::Shared,
            pointee: Box::new(primitive()),
        };
        let raw = TypeTree::RawPointer {
            mutability: RawMutability::Const,
            pointee: Box::new(primitive()),
        };
        let adt = |adt_kind, crate_name: &str, path: &[&str], arguments| TypeTree::Adt {
            adt_kind,
            identity: crate::AdtIdentity::External {
                crate_name: crate_name.into(),
                path: path.iter().map(|part| (*part).into()).collect(),
            },
            arguments,
        };
        let global = || adt(AdtKind::Struct, "alloc", &["alloc", "Global"], vec![]);
        let boxed = |value| {
            adt(
                AdtKind::Struct,
                "alloc",
                &["boxed", "Box"],
                vec![value, global()],
            )
        };
        let option = |value| adt(AdtKind::Enum, "core", &["option", "Option"], vec![value]);

        assert!(pointer_like_type(&raw));
        assert!(pointer_like_type(&reference));
        assert!(pointer_like_type(&boxed(primitive())));
        assert!(pointer_like_type(&option(reference.clone())));
        assert!(pointer_like_type(&option(boxed(primitive()))));
        assert!(!pointer_like_type(&TypeTree::Slice {
            element: Box::new(primitive()),
        }));
        assert!(!pointer_like_type(&option(raw)));
        assert!(!pointer_like_type(&option(option(reference))));
        assert!(!pointer_like_type(&adt(
            AdtKind::Struct,
            "other",
            &["boxed", "Box"],
            vec![primitive()],
        )));
        assert!(!pointer_like_type(&TypeTree::Adt {
            adt_kind: AdtKind::Struct,
            identity: crate::AdtIdentity::Local {
                id: "<adt0>".into()
            },
            arguments: vec![primitive()],
        }));
    }

    #[test]
    fn lhs_target_must_materialize_a_supported_place() {
        let source = anchor_path();
        let mut place = base_rule(source.clone(), anchor_path());
        place.lhs = true;
        let mut call = base_rule(
            source,
            RuleExpression::Call {
                callee: Box::new(anchor_path()),
                arguments: vec![],
            },
        );
        call.lhs = true;
        let mut region = input(concrete_binding("<id0>"));
        region.lhs = true;
        assert!(
            LoadedRuleSet::new(&RuleDocument {
                schema_version: 1,
                rules: vec![place],
            })
            .unwrap()
            .select(&region)
            .is_some()
        );
        assert!(
            LoadedRuleSet::new(&RuleDocument {
                schema_version: 1,
                rules: vec![call],
            })
            .unwrap()
            .select(&region)
            .is_none()
        );
    }

    #[test]
    fn lhs_place_gate_accepts_only_paths_dereferences_fields_and_indices() {
        let path = concrete_binding("<id0>");
        let integer = integer("1");
        let field = Expression::Field {
            base: Box::new(path.clone()),
            field: crate::FieldIdentity::External {
                crate_name: "fixture".into(),
                path: vec!["Record".into(), "field".into()],
            },
        };
        let index = Expression::Index {
            base: Box::new(path.clone()),
            index: Box::new(integer.clone()),
        };
        for place in [
            path.clone(),
            Expression::Unary {
                operator: UnaryOperator::Deref,
                operand: Box::new(path.clone()),
            },
            field,
            index,
        ] {
            assert!(normalized_assignment_place(&place));
        }
        for non_place in [
            Expression::Call {
                callee: Box::new(path.clone()),
                arguments: vec![],
            },
            add_expression(path.clone(), integer.clone()),
            Expression::Cast {
                expression: Box::new(path.clone()),
                ty: TypeTree::RawPointer {
                    mutability: RawMutability::Mut,
                    pointee: Box::new(primitive()),
                },
            },
            Expression::If {
                condition: Box::new(Expression::Literal {
                    value: crate::Literal::Bool { value: true },
                }),
                then: crate::Block {
                    statements: vec![crate::Statement::Expression {
                        expression: path.clone(),
                        semicolon: false,
                    }],
                },
                else_expression: Some(Box::new(concrete_binding("<id1>"))),
            },
        ] {
            assert!(!normalized_assignment_place(&non_place));
        }
    }

    #[test]
    fn ordinary_source_anchor_inference_carrier_and_place_misses_are_nonfatal() {
        let base = base_rule(anchor_path(), anchor_path());
        let concrete = input(concrete_binding("<id0>"));

        let source_miss = base_rule(
            integer_rule(RuleIntegerMagnitude::Fixed("1".into())),
            anchor_path(),
        );
        assert!(rule_matches(&source_miss, &concrete).is_none());

        let mut anchor_miss = concrete.clone();
        anchor_miss.pointer_anchors[0].target_type = primitive();
        assert!(rule_matches(&base, &anchor_miss).is_none());

        let raw = RuleTypeTree::RawPointer {
            mutability: RawMutability::Const,
            pointee: Box::new(rule_primitive()),
        };
        let mut inference_rule = base.clone();
        inference_rule.source_type = raw.clone();
        inference_rule.source_adjusted_type = raw;
        let mut inference_miss = concrete.clone();
        inference_miss.source_type = inference_miss.pointer_anchors[0].source_type.clone();
        inference_miss.source_adjusted_type = inference_miss.source_type.clone();
        inference_miss.target_adjusted_type = None;
        assert!(rule_matches(&inference_rule, &inference_miss).is_none());

        let carrier_miss = base_rule(expression_variable(0), anchor_path());
        assert!(rule_matches(&carrier_miss, &concrete).is_none());

        let mut place_miss = base_rule(
            anchor_path(),
            RuleExpression::Call {
                callee: Box::new(anchor_path()),
                arguments: vec![],
            },
        );
        place_miss.lhs = true;
        let mut lhs_input = concrete;
        lhs_input.lhs = true;
        assert!(
            LoadedRuleSet::new(&RuleDocument {
                schema_version: 1,
                rules: vec![place_miss],
            })
            .unwrap()
            .select(&lhs_input)
            .is_none()
        );
    }
}
