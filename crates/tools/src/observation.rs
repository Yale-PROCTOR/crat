use std::{
    collections::{HashMap, HashSet},
    panic::{AssertUnwindSafe, catch_unwind},
    path::Path,
};

use rustc_ast::{
    AttrKind, Attribute, Expr, ExprKind, Item, ItemKind, NodeId, PatKind, Stmt, StmtKind,
    mut_visit::{self, MutVisitor},
    ptr::P,
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use rustc_hir::{self as hir, def::Res};
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::config::Input;
use rustc_span::{
    Symbol,
    def_id::{DefId, LocalDefId},
};
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

use crate::{CallableCorrespondence, CurrentObservationItem, ExtendedReplacementOutput};

pub const OBSERVATION_SCHEMA_VERSION: u64 = 1;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplacementObservationMetadata {
    pub schema_version: u64,
    pub candidate_sha256: String,
    pub statement_pairs_sha256: String,
    pub observation_source_sha256: String,
    pub accepted_correspondence: Vec<CallableCorrespondence>,
    pub new_correspondence: Vec<CallableCorrespondence>,
    pub current_items: Vec<CurrentObservationItem>,
}

impl ReplacementObservationMetadata {
    pub fn from_output(
        output: &ExtendedReplacementOutput,
        candidate: &[u8],
        statement_pairs: &[u8],
        observation_source: &[u8],
    ) -> Self {
        Self {
            schema_version: OBSERVATION_SCHEMA_VERSION,
            candidate_sha256: sha256_hex(candidate),
            statement_pairs_sha256: sha256_hex(statement_pairs),
            observation_source_sha256: sha256_hex(observation_source),
            accepted_correspondence: output.accepted_correspondence.clone(),
            new_correspondence: output.new_correspondence.clone(),
            current_items: output.current_items.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObservationDocument {
    pub schema_version: u64,
    pub observations: Vec<Observation>,
}

impl Default for ObservationDocument {
    fn default() -> Self {
        Self {
            schema_version: OBSERVATION_SCHEMA_VERSION,
            observations: vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Observation {
    pub source_expression: Expression,
    pub target_expression: Expression,
    pub pointer_anchors: Vec<PointerAnchor>,
    pub source_type: TypeTree,
    pub source_adjusted_type: TypeTree,
    pub target_type: TypeTree,
    pub target_adjusted_type: TypeTree,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PointerAnchor {
    pub id: String,
    pub source_type: TypeTree,
    pub target_type: TypeTree,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum TypeTree {
    Primitive {
        name: String,
    },
    Slice {
        element: Box<TypeTree>,
    },
    Array {
        element: Box<TypeTree>,
        length: u64,
    },
    RawPointer {
        mutability: RawMutability,
        pointee: Box<TypeTree>,
    },
    Reference {
        mutability: RefMutability,
        pointee: Box<TypeTree>,
    },
    Tuple {
        elements: Vec<TypeTree>,
    },
    Adt {
        adt_kind: AdtKind,
        identity: AdtIdentity,
        arguments: Vec<TypeTree>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RawMutability {
    Const,
    Mut,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RefMutability {
    Shared,
    Mutable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AdtKind {
    Struct,
    Enum,
    Union,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum AdtIdentity {
    External {
        #[serde(rename = "crate")]
        crate_name: String,
        path: Vec<String>,
    },
    Local {
        id: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum FieldIdentity {
    External {
        #[serde(rename = "crate")]
        crate_name: String,
        path: Vec<String>,
    },
    Local {
        owner: AdtIdentity,
        id: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum VariantIdentity {
    External {
        #[serde(rename = "crate")]
        crate_name: String,
        path: Vec<String>,
    },
    Local {
        owner: AdtIdentity,
        id: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ValueIdentity {
    Binding {
        id: String,
    },
    Function {
        id: String,
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
        adt: AdtIdentity,
        variant: Option<VariantIdentity>,
    },
    Constant {
        id: String,
    },
    Static {
        id: String,
    },
    Method {
        id: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Expression {
    Array {
        elements: Vec<Expression>,
    },
    Call {
        callee: Box<Expression>,
        arguments: Vec<Expression>,
    },
    MethodCall {
        receiver: Box<Expression>,
        method: ValueIdentity,
        arguments: Vec<Expression>,
    },
    Tuple {
        elements: Vec<Expression>,
    },
    Binary {
        operator: BinaryOperator,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Unary {
        operator: UnaryOperator,
        operand: Box<Expression>,
    },
    Literal {
        value: Literal,
    },
    Cast {
        expression: Box<Expression>,
        #[serde(rename = "type")]
        ty: TypeTree,
    },
    If {
        condition: Box<Expression>,
        then: Block,
        #[serde(rename = "else")]
        else_expression: Option<Box<Expression>>,
    },
    While {
        condition: Box<Expression>,
        body: Block,
    },
    Loop {
        body: Block,
    },
    Assign {
        left: Box<Expression>,
        right: Box<Expression>,
    },
    AssignOp {
        operator: BinaryOperator,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    Field {
        base: Box<Expression>,
        field: FieldIdentity,
    },
    Index {
        base: Box<Expression>,
        index: Box<Expression>,
    },
    Range {
        start: Option<Box<Expression>>,
        end: Option<Box<Expression>>,
        limits: RangeLimits,
    },
    Path {
        value: ValueIdentity,
    },
    AddressOf {
        borrow: BorrowKind,
        mutability: RawMutability,
        expression: Box<Expression>,
    },
    Break {
        value: Option<Box<Expression>>,
    },
    Continue,
    Return {
        value: Option<Box<Expression>>,
    },
    Struct {
        adt: AdtIdentity,
        variant: Option<VariantIdentity>,
        fields: Vec<StructField>,
        rest: Option<Box<Expression>>,
    },
    Repeat {
        value: Box<Expression>,
        count: Box<Expression>,
    },
    Block {
        block: Block,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Statement {
    Let {
        pattern: Pattern,
        #[serde(rename = "type")]
        ty: Option<TypeTree>,
        initializer: Option<Expression>,
    },
    Expression {
        expression: Expression,
        semicolon: bool,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Pattern {
    Binding {
        id: String,
        mutability: BindingMutability,
        by_ref: ByRefKind,
    },
    Wildcard,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StructField {
    pub field: FieldIdentity,
    pub value: Expression,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BindingMutability {
    Immutable,
    Mutable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ByRefKind {
    No,
    Shared,
    Mutable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BorrowKind {
    Reference,
    Raw,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RangeLimits {
    HalfOpen,
    Closed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    And,
    Or,
    BitXor,
    BitAnd,
    BitOr,
    ShiftLeft,
    ShiftRight,
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UnaryOperator {
    Deref,
    Not,
    Negate,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Literal {
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
        value: String,
        #[serde(rename = "type")]
        ty: String,
    },
    Float {
        bits: String,
        #[serde(rename = "type")]
        ty: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObservationError {
    pub code: &'static str,
    pub message: String,
}

pub fn extract_observations_from_path(
    path: &Path,
    metadata: &ReplacementObservationMetadata,
) -> Result<ObservationDocument, ObservationError> {
    extract_observations(utils::compilation::path_to_input(path), metadata)
}

fn extract_observations(
    input: Input,
    metadata: &ReplacementObservationMetadata,
) -> Result<ObservationDocument, ObservationError> {
    if metadata.schema_version != OBSERVATION_SCHEMA_VERSION {
        return Err(ObservationError {
            code: "unsupported_schema_version",
            message: format!("unsupported schema_version {}", metadata.schema_version),
        });
    }
    validate_replacement_metadata(metadata)?;
    let source = match input {
        Input::File(path) => std::fs::read_to_string(path).map_err(|error| ObservationError {
            code: "observation_source_io",
            message: format!("failed to read observation source: {error}"),
        })?,
        Input::Str { input, .. } => input,
    };
    let prepared = rustc_span::create_session_if_not_set_then(
        rustc_span::edition::Edition::Edition2021,
        |_| prepare_observation_source(&source, metadata),
    )?;
    let compiler_source = prepared.compiler_source.clone();
    utils::compilation::run_compiler_on_input(
        utils::compilation::str_to_input(&compiler_source),
        move |tcx| extract_with_tcx(&prepared, metadata, tcx),
    )
    .map_err(|_| ObservationError {
        code: "compiler_failure",
        message: "observation source failed to compile".to_owned(),
    })?
}

#[cfg(test)]
pub(crate) fn extract_observations_from_source(
    source: &str,
    metadata: &ReplacementObservationMetadata,
) -> Result<ObservationDocument, ObservationError> {
    extract_observations(utils::compilation::str_to_input(source), metadata)
}

struct PreparedObservation {
    compiler_source: String,
    functions: Vec<PreparedFunction>,
}

struct PreparedFunction {
    item_id: u64,
    source_path: String,
    target_path: String,
    labels: Vec<PreparedLabel>,
    local_pairs: Vec<(usize, usize)>,
}

struct PreparedLabel {
    label: u32,
    source_ordinal: usize,
    target_ordinals: Vec<usize>,
    macro_skip: bool,
    source_opaque_ordinals: Vec<usize>,
    opaque_labels_match: bool,
}

fn prepare_observation_source(
    source: &str,
    metadata: &ReplacementObservationMetadata,
) -> Result<PreparedObservation, ObservationError> {
    let mut krate = catch_unwind(AssertUnwindSafe(|| {
        utils::ast::parse_crate(source.to_owned())
    }))
    .map_err(|_| ObservationError {
        code: "observation_source_parse",
        message: "observation source did not parse".to_owned(),
    })?;
    let mut items = HashMap::new();
    collect_functions(&krate.items, &mut vec![], &mut items);
    let mut functions = vec![];
    for current in &metadata.current_items {
        let source_item = items
            .get(&current.source_copy_path)
            .ok_or_else(|| ObservationError {
                code: "metadata_function_mismatch",
                message: format!(
                    "metadata source-copy path `{}` is absent",
                    current.source_copy_path
                ),
            })?;
        let target_item =
            items
                .get(&current.implementation_path)
                .ok_or_else(|| ObservationError {
                    code: "metadata_function_mismatch",
                    message: format!(
                        "metadata implementation path `{}` is absent",
                        current.implementation_path
                    ),
                })?;
        let source_statements = labeled_statements(source_item, &current.source_copy_path)?;
        let target_statements = labeled_statements(target_item, &current.implementation_path)?;
        let local_pairs = pair_local_statement_ordinals(
            &source_statements,
            &target_statements,
            &current.source_copy_path,
            &current.implementation_path,
        )?;
        let mut labels = vec![];
        for label in &current.transform_labels {
            let source_matches = source_statements
                .iter()
                .filter(|statement| statement.label == Some(*label))
                .collect::<Vec<_>>();
            if source_matches.len() != 1 {
                return Err(ObservationError {
                    code: "ambiguous_transform_label",
                    message: format!(
                        "source copy has {} occurrences of transform label {label}",
                        source_matches.len()
                    ),
                });
            }
            let target_matches = target_statements
                .iter()
                .filter(|statement| statement.label == Some(*label))
                .collect::<Vec<_>>();
            if target_matches.is_empty() {
                return Err(ObservationError {
                    code: "absent_transform_label",
                    message: format!("target implementation has no transform label {label}"),
                });
            }
            if target_matches
                .windows(2)
                .any(|pair| pair[1].ordinal != pair[0].ordinal + 1)
            {
                return Err(ObservationError {
                    code: "nonconsecutive_transform_group",
                    message: format!("target transform label {label} is nonconsecutive"),
                });
            }
            labels.push(PreparedLabel {
                label: *label,
                source_ordinal: source_matches[0].ordinal,
                target_ordinals: target_matches
                    .iter()
                    .map(|statement| statement.ordinal)
                    .collect(),
                macro_skip: statement_contains_macro(source_matches[0].statement)
                    || target_matches
                        .iter()
                        .any(|statement| statement_contains_macro(statement.statement)),
                source_opaque_ordinals: source_statements
                    .iter()
                    .filter(|statement| {
                        statement.ordinal != source_matches[0].ordinal
                            && statement.label.is_some_and(|nested| nested != *label)
                            && source_matches[0]
                                .statement
                                .span
                                .contains(statement.statement.span)
                    })
                    .map(|statement| statement.ordinal)
                    .collect(),
                opaque_labels_match: nested_labels(
                    source_matches.iter().copied(),
                    &source_statements,
                    *label,
                ) == nested_labels(
                    target_matches.iter().copied(),
                    &target_statements,
                    *label,
                ),
            });
        }
        functions.push(PreparedFunction {
            item_id: current.item_id,
            source_path: current.source_copy_path.clone(),
            target_path: current.implementation_path.clone(),
            labels,
            local_pairs,
        });
    }
    ProctorAttributeRemover.visit_crate(&mut krate);
    Ok(PreparedObservation {
        compiler_source: pprust::crate_to_string_for_macros(&krate),
        functions,
    })
}

fn nested_labels<'a>(
    roots: impl Iterator<Item = &'a LabeledStatement<'a>>,
    statements: &[LabeledStatement<'_>],
    outer_label: u32,
) -> Vec<u32> {
    let root_spans = roots.map(|root| root.statement.span).collect::<Vec<_>>();
    statements
        .iter()
        .filter_map(|statement| {
            let label = statement.label?;
            (label != outer_label
                && root_spans
                    .iter()
                    .any(|span| span.contains(statement.statement.span)))
            .then_some(label)
        })
        .collect()
}

fn pair_local_statement_ordinals(
    source: &[LabeledStatement<'_>],
    target: &[LabeledStatement<'_>],
    source_path: &str,
    target_path: &str,
) -> Result<Vec<(usize, usize)>, ObservationError> {
    let source_locals = labeled_simple_locals(source, source_path)?;
    let target_locals = labeled_simple_locals(target, target_path)?;
    let mut pairs = Vec::with_capacity(source_locals.len());
    for (label, (source_ordinal, source_name)) in &source_locals {
        let Some((target_ordinal, target_name)) = target_locals.get(label) else {
            return Err(correspondence_error(&format!(
                "target has no simple local declaration for label {label}"
            )));
        };
        if source_name != target_name {
            return Err(correspondence_error(&format!(
                "local declaration symbols differ at label {label}"
            )));
        }
        pairs.push((*source_ordinal, *target_ordinal));
    }
    Ok(pairs)
}

fn labeled_simple_locals(
    statements: &[LabeledStatement<'_>],
    path: &str,
) -> Result<HashMap<u32, (usize, Symbol)>, ObservationError> {
    let mut result = HashMap::new();
    for statement in statements {
        let StmtKind::Let(local) = &statement.statement.kind else { continue };
        let PatKind::Ident(_, ident, None) = local.pat.kind else { continue };
        let Some(label) = statement.label else { continue };
        if result
            .insert(label, (statement.ordinal, ident.name))
            .is_some()
        {
            return Err(ObservationError {
                code: "binding_correspondence",
                message: format!("{path} has duplicate simple-local label {label}"),
            });
        }
    }
    Ok(result)
}

fn collect_functions<'a>(
    items: &'a [P<Item>],
    module_path: &mut Vec<String>,
    output: &mut HashMap<String, &'a Item>,
) {
    for item in items {
        match &item.kind {
            ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(children, ..)) => {
                module_path.push(ident.to_string());
                collect_functions(children, module_path, output);
                module_path.pop();
            }
            ItemKind::Fn(box function) if function.body.is_some() => {
                let path = module_path
                    .iter()
                    .cloned()
                    .chain(std::iter::once(function.ident.to_string()))
                    .collect::<Vec<_>>()
                    .join("::");
                output.insert(path, item);
            }
            _ => {}
        }
    }
}

struct LabeledStatement<'a> {
    ordinal: usize,
    label: Option<u32>,
    statement: &'a Stmt,
}

fn labeled_statements<'a>(
    item: &'a Item,
    path: &'a str,
) -> Result<Vec<LabeledStatement<'a>>, ObservationError> {
    struct Collector<'a> {
        path: &'a str,
        result: Vec<LabeledStatement<'a>>,
        error: Option<ObservationError>,
    }
    impl<'ast> Visitor<'ast> for Collector<'ast> {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if self.error.is_some() || matches!(statement.kind, StmtKind::Empty | StmtKind::Item(_))
            {
                return;
            }
            let attributes = statement_attributes(statement);
            let mut labels = vec![];
            for attribute in attributes
                .iter()
                .filter(|attribute| is_proctor_attribute(attribute))
            {
                match numeric_proctor_label(attribute) {
                    Some(label) => labels.push(label),
                    None => {
                        self.error = Some(ObservationError {
                            code: "malformed_proctor_label",
                            message: format!(
                                "{} contains a malformed proctor statement label",
                                self.path
                            ),
                        });
                        return;
                    }
                }
            }
            if labels.len() > 1 {
                self.error = Some(ObservationError {
                    code: "malformed_proctor_label",
                    message: format!("{} contains multiple proctor statement labels", self.path),
                });
                return;
            }
            self.result.push(LabeledStatement {
                ordinal: self.result.len(),
                label: labels.first().copied(),
                statement,
            });
            visit::walk_stmt(self, statement);
        }
    }
    let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
    let mut collector = Collector {
        path,
        result: vec![],
        error: None,
    };
    collector.visit_block(function.body.as_ref().unwrap());
    collector.error.map_or(Ok(collector.result), Err)
}

struct SurfaceFunction<'a> {
    item: &'a Item,
    def_id: LocalDefId,
}

fn extract_with_tcx(
    prepared: &PreparedObservation,
    metadata: &ReplacementObservationMetadata,
    tcx: TyCtxt<'_>,
) -> Result<ObservationDocument, ObservationError> {
    let mut surface = catch_unwind(AssertUnwindSafe(|| {
        utils::ast::parse_crate(prepared.compiler_source.clone())
    }))
    .map_err(|_| ObservationError {
        code: "observation_source_parse",
        message: "label-free observation source did not parse".to_owned(),
    })?;
    let mut mapper = utils::ir::AstToHirMapper::new(tcx);
    catch_unwind(AssertUnwindSafe(|| {
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
    }))
    .map_err(|_| ObservationError {
        code: "ast_hir_mapping",
        message: "label-free observation AST does not structurally match HIR".to_owned(),
    })?;
    let ast_to_hir = mapper.ast_to_hir;
    let mut raw_items = HashMap::new();
    collect_functions(&surface.items, &mut vec![], &mut raw_items);
    let mut functions = HashMap::new();
    for (path, item) in raw_items {
        let Some(def_id) = ast_to_hir.global_map.get(&item.id).copied() else {
            return Err(ObservationError {
                code: "ast_hir_mapping",
                message: format!("function `{path}` has no HIR identity"),
            });
        };
        functions.insert(path, SurfaceFunction { item, def_id });
    }
    let callable_correspondence = callable_correspondence(metadata, &functions)?;
    let mut output = vec![];
    let mut ordered = prepared.functions.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|function| function.item_id);
    for prepared_function in ordered {
        let source = functions
            .get(&prepared_function.source_path)
            .ok_or_else(|| ObservationError {
                code: "metadata_function_mismatch",
                message: format!(
                    "source-copy path `{}` disappeared after label removal",
                    prepared_function.source_path
                ),
            })?;
        let target = functions
            .get(&prepared_function.target_path)
            .ok_or_else(|| ObservationError {
                code: "metadata_function_mismatch",
                message: format!(
                    "implementation path `{}` disappeared after label removal",
                    prepared_function.target_path
                ),
            })?;
        let source_statements = plain_statements(source.item);
        let target_statements = plain_statements(target.item);
        let bindings = pair_bindings(
            source,
            target,
            &source_statements,
            &target_statements,
            &prepared_function.local_pairs,
            &ast_to_hir,
            tcx,
        )?;
        for label in &prepared_function.labels {
            if label.macro_skip || label.target_ordinals.len() != 1 || !label.opaque_labels_match {
                continue;
            }
            let Some(source_statement) = source_statements.get(label.source_ordinal) else {
                return Err(ObservationError {
                    code: "ast_hir_mapping",
                    message: format!("source label {} ordinal disappeared", label.label),
                });
            };
            let Some(target_statement) = target_statements.get(label.target_ordinals[0]) else {
                return Err(ObservationError {
                    code: "ast_hir_mapping",
                    message: format!("target label {} ordinal disappeared", label.label),
                });
            };
            let (Some(source_expression), Some(target_expression)) = (
                statement_expression(source_statement),
                statement_expression(target_statement),
            ) else {
                continue;
            };
            for (side, expression) in [("source", source_expression), ("target", target_expression)]
            {
                if ast_to_hir.get_expr(expression.id, tcx).is_none() {
                    return Err(ObservationError {
                        code: "ast_hir_mapping",
                        message: format!(
                            "{side} expression for transform label {} has no HIR mapping",
                            label.label
                        ),
                    });
                }
            }
            let mut tree = ExpressionTree {
                opaque: label
                    .source_opaque_ordinals
                    .iter()
                    .filter_map(|ordinal| source_statements.get(*ordinal))
                    .filter_map(|statement| statement_expression(statement))
                    .map(|expression| expression.id)
                    .collect(),
                ..ExpressionTree::default()
            };
            tree.add(
                source_expression,
                None,
                ParentRole::Boundary,
                &ast_to_hir,
                tcx,
            );
            if let Some(expression) = tree
                .expressions
                .values()
                .find(|expression| ast_to_hir.get_expr(expression.id, tcx).is_none())
            {
                return Err(ObservationError {
                    code: "ast_hir_mapping",
                    message: format!(
                        "source expression node {:?} for transform label {} has no HIR mapping",
                        expression.id, label.label
                    ),
                });
            }
            let mut selected = vec![];
            for anchor in &tree.anchors {
                let Some(target_binding) = bindings.get(&anchor.binding) else { continue };
                let Some(root) = select_region(anchor.expression, &tree, &ast_to_hir, tcx) else {
                    continue;
                };
                selected.push(SelectedRegion {
                    root,
                    anchors: vec![AnchorPair {
                        source_binding: anchor.binding,
                        target_binding: *target_binding,
                    }],
                });
            }
            merge_regions(&mut selected);
            if regions_overlap(&selected, &tree) {
                continue;
            }
            let mut selected_ids = selected
                .iter()
                .map(|region| region.root)
                .collect::<HashSet<_>>();
            selected_ids.extend(tree.opaque.iter().copied());
            let mut mappings = HashMap::new();
            if !align_expression(
                source_expression,
                target_expression,
                &selected_ids,
                &bindings,
                &callable_correspondence,
                &ast_to_hir,
                tcx,
                &mut mappings,
            ) {
                continue;
            }
            for region in selected {
                let Some(target_root) = mappings.get(&region.root).copied() else {
                    return Err(ObservationError {
                        code: "ast_hir_mapping",
                        message: format!(
                            "selected source region for transform label {} has no target mapping",
                            label.label
                        ),
                    });
                };
                if let Some(observation) = dump_observation(
                    tree.expressions[&region.root],
                    target_root,
                    &region.anchors,
                    &bindings,
                    &callable_correspondence,
                    &ast_to_hir,
                    tcx,
                ) {
                    output.push(observation);
                }
            }
        }
    }
    Ok(ObservationDocument {
        schema_version: OBSERVATION_SCHEMA_VERSION,
        observations: output,
    })
}

fn callable_correspondence(
    metadata: &ReplacementObservationMetadata,
    functions: &HashMap<String, SurfaceFunction<'_>>,
) -> Result<HashMap<DefId, u64>, ObservationError> {
    fn insert(
        result: &mut HashMap<DefId, u64>,
        def_id: DefId,
        item_id: u64,
        path: &str,
    ) -> Result<(), ObservationError> {
        if let Some(previous) = result.insert(def_id, item_id) {
            return Err(ObservationError {
                code: "contradictory_correspondence",
                message: format!(
                    "callable `{path}` maps one compiler identity to item IDs {previous} and {item_id}"
                ),
            });
        }
        Ok(())
    }
    let mut result = HashMap::new();
    for record in metadata
        .accepted_correspondence
        .iter()
        .chain(&metadata.new_correspondence)
    {
        let implementation =
            functions
                .get(&record.implementation_path)
                .ok_or_else(|| ObservationError {
                    code: "dangling_correspondence",
                    message: format!(
                        "correspondence implementation `{}` is absent",
                        record.implementation_path
                    ),
                })?;
        insert(
            &mut result,
            implementation.def_id.to_def_id(),
            record.item_id,
            &record.implementation_path,
        )?;
        if let Some(wrapper_path) = &record.wrapper_path {
            let wrapper = functions
                .get(wrapper_path)
                .ok_or_else(|| ObservationError {
                    code: "dangling_correspondence",
                    message: format!("correspondence wrapper `{wrapper_path}` is absent"),
                })?;
            insert(
                &mut result,
                wrapper.def_id.to_def_id(),
                record.item_id,
                wrapper_path,
            )?;
        }
    }
    for current in &metadata.current_items {
        let source = functions
            .get(&current.source_copy_path)
            .ok_or_else(|| ObservationError {
                code: "dangling_correspondence",
                message: format!("source copy `{}` is absent", current.source_copy_path),
            })?;
        insert(
            &mut result,
            source.def_id.to_def_id(),
            current.item_id,
            &current.source_copy_path,
        )?;
    }
    Ok(result)
}

fn plain_statements(item: &Item) -> Vec<&Stmt> {
    struct Collector<'a>(Vec<&'a Stmt>);
    impl<'ast> Visitor<'ast> for Collector<'ast> {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if matches!(statement.kind, StmtKind::Empty | StmtKind::Item(_)) {
                return;
            }
            self.0.push(statement);
            visit::walk_stmt(self, statement);
        }
    }
    let ItemKind::Fn(box function) = &item.kind else { unreachable!() };
    let mut collector = Collector(vec![]);
    collector.visit_block(function.body.as_ref().unwrap());
    collector.0
}

fn statement_expression(statement: &Stmt) -> Option<&Expr> {
    match &statement.kind {
        StmtKind::Let(local) => match &local.kind {
            rustc_ast::LocalKind::Init(expression)
            | rustc_ast::LocalKind::InitElse(expression, _) => Some(expression),
            rustc_ast::LocalKind::Decl => None,
        },
        StmtKind::Expr(expression) | StmtKind::Semi(expression) => Some(expression),
        _ => None,
    }
}

fn pair_bindings(
    source: &SurfaceFunction<'_>,
    target: &SurfaceFunction<'_>,
    source_statements: &[&Stmt],
    target_statements: &[&Stmt],
    local_pairs: &[(usize, usize)],
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Result<HashMap<hir::HirId, hir::HirId>, ObservationError> {
    let ItemKind::Fn(box source_fn) = &source.item.kind else { unreachable!() };
    let ItemKind::Fn(box target_fn) = &target.item.kind else { unreachable!() };
    if source_fn.sig.decl.inputs.len() != target_fn.sig.decl.inputs.len() {
        return Err(correspondence_error("parameter count differs"));
    }
    let mut result = HashMap::new();
    for (index, (source_parameter, target_parameter)) in source_fn
        .sig
        .decl
        .inputs
        .iter()
        .zip(&target_fn.sig.decl.inputs)
        .enumerate()
    {
        let (source_name, source_id) = simple_binding(&source_parameter.pat, ast_to_hir, tcx)
            .ok_or_else(|| {
                correspondence_error(&format!("source parameter {index} is not a simple binding"))
            })?;
        let (target_name, target_id) = simple_binding(&target_parameter.pat, ast_to_hir, tcx)
            .ok_or_else(|| {
                correspondence_error(&format!("target parameter {index} is not a simple binding"))
            })?;
        if source_name != target_name {
            return Err(correspondence_error(&format!(
                "parameter {index} symbols differ"
            )));
        }
        result.insert(source_id, target_id);
    }
    for &(source_ordinal, target_ordinal) in local_pairs {
        let Some(source_statement) = source_statements.get(source_ordinal) else {
            return Err(correspondence_error("source local declaration disappeared"));
        };
        let Some(target_statement) = target_statements.get(target_ordinal) else {
            return Err(correspondence_error("target local declaration disappeared"));
        };
        let (StmtKind::Let(source_local), StmtKind::Let(target_local)) =
            (&source_statement.kind, &target_statement.kind)
        else {
            continue;
        };
        let Some((source_name, source_id)) = simple_binding(&source_local.pat, ast_to_hir, tcx)
        else {
            continue;
        };
        let Some((target_name, target_id)) = simple_binding(&target_local.pat, ast_to_hir, tcx)
        else {
            continue;
        };
        if source_name == target_name {
            validate_local_annotations(
                source_local,
                target_local,
                source_id,
                target_id,
                ast_to_hir,
                tcx,
            )?;
            result.insert(source_id, target_id);
        } else {
            return Err(correspondence_error("paired local symbols differ"));
        }
    }
    Ok(result)
}

fn validate_local_annotations(
    source: &rustc_ast::Local,
    target: &rustc_ast::Local,
    source_binding: hir::HirId,
    target_binding: hir::HirId,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Result<(), ObservationError> {
    let target_annotation = target
        .ty
        .as_deref()
        .ok_or_else(|| correspondence_error("paired target local has no type annotation"))?;
    if !annotation_matches_binding(target_annotation, target_binding, ast_to_hir, tcx) {
        return Err(correspondence_error(
            "target local annotation disagrees with its binding type",
        ));
    }
    if let Some(source_annotation) = source.ty.as_deref()
        && !annotation_matches_binding(source_annotation, source_binding, ast_to_hir, tcx)
    {
        return Err(correspondence_error(
            "source local annotation disagrees with its binding type",
        ));
    }
    Ok(())
}

fn annotation_matches_binding(
    annotation: &rustc_ast::Ty,
    binding: hir::HirId,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    let Some(annotation) = ast_to_hir.get_ty(annotation.id, tcx) else { return false };
    let annotation_type = tcx
        .typeck(annotation.hir_id.owner)
        .node_type(annotation.hir_id);
    binding_type(binding, tcx).is_some_and(|binding_type| {
        tcx.erase_regions(annotation_type) == tcx.erase_regions(binding_type)
    })
}

fn simple_binding(
    pattern: &rustc_ast::Pat,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<(Symbol, hir::HirId)> {
    let PatKind::Ident(_, ident, None) = pattern.kind else { return None };
    let pattern = ast_to_hir.get_pat(pattern.id, tcx)?;
    let hir::PatKind::Binding(_, id, _, None) = pattern.kind else { return None };
    Some((ident.name, id))
}

fn correspondence_error(detail: &str) -> ObservationError {
    ObservationError {
        code: "binding_correspondence",
        message: detail.to_owned(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum ParentRole {
    Boundary,
    ArrayElement,
    TupleElement,
    RepeatValue,
    RepeatCount,
    CallCallee,
    CallArgument,
    MethodReceiver,
    MethodArgument,
    BinaryOperand,
    UnaryOperand(rustc_ast::UnOp),
    CastOperand,
    Condition,
    MatchScrutinee,
    BranchTail,
    AssignOperand,
    AssignOpOperand,
    FieldBase,
    IndexBase,
    IndexIndex,
    AddressOperand,
    ReturnOperand,
    StructField,
    StructRest,
    BlockTail,
    Unsupported,
}

#[derive(Clone, Copy)]
struct ParentEdge {
    parent: NodeId,
    role: ParentRole,
}

struct AnchorOccurrence {
    expression: NodeId,
    binding: hir::HirId,
}

#[derive(Default)]
struct ExpressionTree<'a> {
    expressions: HashMap<NodeId, &'a Expr>,
    parents: HashMap<NodeId, ParentEdge>,
    anchors: Vec<AnchorOccurrence>,
    opaque: HashSet<NodeId>,
}

impl<'a> ExpressionTree<'a> {
    fn add(
        &mut self,
        expression: &'a Expr,
        parent: Option<NodeId>,
        role: ParentRole,
        ast_to_hir: &utils::ir::AstToHir,
        tcx: TyCtxt<'_>,
    ) {
        if !self.opaque.contains(&expression.id)
            && let ExprKind::Paren(inner) = &expression.kind
        {
            self.add(inner, parent, role, ast_to_hir, tcx);
            return;
        }
        self.expressions.insert(expression.id, expression);
        if let Some(parent) = parent {
            self.parents
                .insert(expression.id, ParentEdge { parent, role });
        }
        if self.opaque.contains(&expression.id) {
            return;
        }
        if let Some(hir_expression) = ast_to_hir.get_expr(expression.id, tcx)
            && let hir::ExprKind::Path(path) = hir_expression.kind
            && let Res::Local(binding) = tcx
                .typeck(hir_expression.hir_id.owner)
                .qpath_res(&path, hir_expression.hir_id)
            && tcx
                .typeck(hir_expression.hir_id.owner)
                .expr_ty(hir_expression)
                .is_raw_ptr()
        {
            self.anchors.push(AnchorOccurrence {
                expression: expression.id,
                binding,
            });
        }
        let id = expression.id;
        match &expression.kind {
            ExprKind::Array(values) => {
                for value in values {
                    self.add(value, Some(id), ParentRole::ArrayElement, ast_to_hir, tcx);
                }
            }
            ExprKind::Tup(values) => {
                for value in values {
                    self.add(value, Some(id), ParentRole::TupleElement, ast_to_hir, tcx);
                }
            }
            ExprKind::Repeat(value, count) => {
                self.add(value, Some(id), ParentRole::RepeatValue, ast_to_hir, tcx);
                self.add(
                    &count.value,
                    Some(id),
                    ParentRole::RepeatCount,
                    ast_to_hir,
                    tcx,
                );
            }
            ExprKind::Call(callee, arguments) => {
                self.add(callee, Some(id), ParentRole::CallCallee, ast_to_hir, tcx);
                for argument in arguments {
                    self.add(
                        argument,
                        Some(id),
                        ParentRole::CallArgument,
                        ast_to_hir,
                        tcx,
                    );
                }
            }
            ExprKind::MethodCall(call) => {
                self.add(
                    &call.receiver,
                    Some(id),
                    ParentRole::MethodReceiver,
                    ast_to_hir,
                    tcx,
                );
                for argument in &call.args {
                    self.add(
                        argument,
                        Some(id),
                        ParentRole::MethodArgument,
                        ast_to_hir,
                        tcx,
                    );
                }
            }
            ExprKind::Binary(_, left, right) => {
                self.add(left, Some(id), ParentRole::BinaryOperand, ast_to_hir, tcx);
                self.add(right, Some(id), ParentRole::BinaryOperand, ast_to_hir, tcx);
            }
            ExprKind::Unary(operator, operand) => self.add(
                operand,
                Some(id),
                ParentRole::UnaryOperand(*operator),
                ast_to_hir,
                tcx,
            ),
            ExprKind::Cast(operand, _) => {
                self.add(operand, Some(id), ParentRole::CastOperand, ast_to_hir, tcx)
            }
            ExprKind::If(condition, then_block, otherwise) => {
                self.add(condition, Some(id), ParentRole::Condition, ast_to_hir, tcx);
                self.add_block(then_block, id, ParentRole::BranchTail, ast_to_hir, tcx);
                if let Some(otherwise) = otherwise {
                    self.add(otherwise, Some(id), ParentRole::BranchTail, ast_to_hir, tcx);
                }
            }
            ExprKind::While(condition, block, _) => {
                self.add(condition, Some(id), ParentRole::Condition, ast_to_hir, tcx);
                self.add_block(block, id, ParentRole::BranchTail, ast_to_hir, tcx);
            }
            ExprKind::Match(scrutinee, arms, _) => {
                self.add(
                    scrutinee,
                    Some(id),
                    ParentRole::MatchScrutinee,
                    ast_to_hir,
                    tcx,
                );
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.add(guard, Some(id), ParentRole::Condition, ast_to_hir, tcx);
                    }
                    if let Some(body) = &arm.body {
                        self.add(body, Some(id), ParentRole::BranchTail, ast_to_hir, tcx);
                    }
                }
            }
            ExprKind::Assign(left, right, _) => {
                self.add(left, Some(id), ParentRole::AssignOperand, ast_to_hir, tcx);
                self.add(right, Some(id), ParentRole::AssignOperand, ast_to_hir, tcx);
            }
            ExprKind::AssignOp(_, left, right) => {
                self.add(left, Some(id), ParentRole::AssignOpOperand, ast_to_hir, tcx);
                self.add(
                    right,
                    Some(id),
                    ParentRole::AssignOpOperand,
                    ast_to_hir,
                    tcx,
                );
            }
            ExprKind::Field(base, _) => {
                self.add(base, Some(id), ParentRole::FieldBase, ast_to_hir, tcx)
            }
            ExprKind::Index(base, index, _) => {
                self.add(base, Some(id), ParentRole::IndexBase, ast_to_hir, tcx);
                self.add(index, Some(id), ParentRole::IndexIndex, ast_to_hir, tcx);
            }
            ExprKind::AddrOf(_, _, operand) => self.add(
                operand,
                Some(id),
                ParentRole::AddressOperand,
                ast_to_hir,
                tcx,
            ),
            ExprKind::Ret(Some(value)) => {
                self.add(value, Some(id), ParentRole::ReturnOperand, ast_to_hir, tcx)
            }
            ExprKind::Struct(value) => {
                for field in &value.fields {
                    self.add(
                        &field.expr,
                        Some(id),
                        ParentRole::StructField,
                        ast_to_hir,
                        tcx,
                    );
                }
                if let rustc_ast::StructRest::Base(rest) = &value.rest {
                    self.add(rest, Some(id), ParentRole::StructRest, ast_to_hir, tcx);
                }
            }
            ExprKind::Block(block, _) => self.add_block(
                block,
                id,
                if role == ParentRole::BranchTail {
                    ParentRole::BranchTail
                } else {
                    ParentRole::BlockTail
                },
                ast_to_hir,
                tcx,
            ),
            _ => {}
        }
    }

    fn add_block(
        &mut self,
        block: &'a rustc_ast::Block,
        parent: NodeId,
        tail_role: ParentRole,
        ast_to_hir: &utils::ir::AstToHir,
        tcx: TyCtxt<'_>,
    ) {
        let single_unlabeled_tail = tail_role != ParentRole::BlockTail
            || (block.stmts.len() == 1
                && matches!(block.stmts[0].kind, StmtKind::Expr(_))
                && statement_attributes(&block.stmts[0]).is_empty());
        for (index, statement) in block.stmts.iter().enumerate() {
            if let Some(expression) = statement_expression(statement) {
                let role = if index + 1 == block.stmts.len()
                    && matches!(statement.kind, StmtKind::Expr(_))
                    && single_unlabeled_tail
                {
                    tail_role
                } else {
                    ParentRole::Unsupported
                };
                self.add(expression, Some(parent), role, ast_to_hir, tcx);
            }
        }
    }
}

#[derive(Clone)]
struct AnchorPair {
    source_binding: hir::HirId,
    target_binding: hir::HirId,
}

struct SelectedRegion {
    root: NodeId,
    anchors: Vec<AnchorPair>,
}

fn select_region(
    start: NodeId,
    tree: &ExpressionTree<'_>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<NodeId> {
    let mut current = start;
    while let Some(edge) = tree.parents.get(&current).copied() {
        let expression = tree.expressions[&current];
        let parent = tree.expressions.get(&edge.parent).copied();
        let current_pointer_like =
            expression_type(expression, ast_to_hir, tcx).is_some_and(|ty| pointer_like(ty, tcx));
        let decision = match edge.role {
            ParentRole::UnaryOperand(rustc_ast::UnOp::Deref) | ParentRole::AddressOperand => 1,
            ParentRole::UnaryOperand(_) => {
                let parent = parent?;
                let hir_parent = ast_to_hir.get_expr(parent.id, tcx)?;
                if tcx
                    .typeck(hir_parent.hir_id.owner)
                    .type_dependent_def_id(hir_parent.hir_id)
                    .is_none()
                    && expression_type(expression, ast_to_hir, tcx)
                        .is_some_and(builtin_operator_operand)
                {
                    0
                } else {
                    return None;
                }
            }
            ParentRole::CastOperand if current_pointer_like => 1,
            ParentRole::MethodReceiver => {
                let parent = parent?;
                let ExprKind::MethodCall(call) = &parent.kind else { return None };
                if expression_type(expression, ast_to_hir, tcx).is_some_and(|ty| ty.is_raw_ptr()) {
                    if resolved_builtin_raw_pointer_method(parent, ast_to_hir, tcx)
                        .is_some_and(|name| name == call.seg.ident.name)
                    {
                        1
                    } else {
                        return None;
                    }
                } else if current_pointer_like {
                    return None;
                } else {
                    0
                }
            }
            ParentRole::ArrayElement | ParentRole::TupleElement | ParentRole::RepeatValue => {
                if current_pointer_like {
                    return None;
                } else {
                    0
                }
            }
            ParentRole::RepeatCount
            | ParentRole::CallCallee
            | ParentRole::IndexBase
            | ParentRole::StructRest
            | ParentRole::Unsupported => return None,
            ParentRole::CallArgument => {
                let parent = parent?;
                let ExprKind::Call(callee, _) = &parent.kind else { return None };
                if resolved_definition(callee, ast_to_hir, tcx).is_some() {
                    0
                } else {
                    return None;
                }
            }
            ParentRole::MethodArgument => {
                let parent = parent?;
                let hir_parent = ast_to_hir.get_expr(parent.id, tcx)?;
                if tcx
                    .typeck(hir_parent.hir_id.owner)
                    .type_dependent_def_id(hir_parent.hir_id)
                    .is_some()
                {
                    0
                } else {
                    return None;
                }
            }
            ParentRole::BinaryOperand => {
                let parent = parent?;
                let hir_parent = ast_to_hir.get_expr(parent.id, tcx)?;
                if tcx
                    .typeck(hir_parent.hir_id.owner)
                    .type_dependent_def_id(hir_parent.hir_id)
                    .is_none()
                    && expression_type(expression, ast_to_hir, tcx)
                        .is_some_and(builtin_operator_operand)
                {
                    0
                } else {
                    return None;
                }
            }
            ParentRole::AssignOpOperand => {
                let parent = parent?;
                let hir_parent = ast_to_hir.get_expr(parent.id, tcx)?;
                if !current_pointer_like
                    && tcx
                        .typeck(hir_parent.hir_id.owner)
                        .type_dependent_def_id(hir_parent.hir_id)
                        .is_none()
                    && expression_type(expression, ast_to_hir, tcx)
                        .is_some_and(builtin_operator_operand)
                {
                    0
                } else {
                    return None;
                }
            }
            ParentRole::Condition
            | ParentRole::AssignOperand
            | ParentRole::ReturnOperand
            | ParentRole::StructField
            | ParentRole::Boundary => 0,
            ParentRole::BranchTail | ParentRole::MatchScrutinee | ParentRole::FieldBase => {
                if current_pointer_like {
                    return None;
                } else {
                    0
                }
            }
            ParentRole::IndexIndex => {
                let parent = parent?;
                let hir_parent = ast_to_hir.get_expr(parent.id, tcx)?;
                if tcx
                    .typeck(hir_parent.hir_id.owner)
                    .type_dependent_def_id(hir_parent.hir_id)
                    .is_none()
                    && scalar_type(expression_type(expression, ast_to_hir, tcx)?)
                {
                    0
                } else {
                    return None;
                }
            }
            ParentRole::BlockTail => 0,
            ParentRole::CastOperand => 0,
        };
        if decision == 0 {
            break;
        }
        current = edge.parent;
    }
    Some(current)
}

fn resolved_builtin_raw_pointer_method(
    expression: &Expr,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<Symbol> {
    let expression = ast_to_hir.get_expr(expression.id, tcx)?;
    let definition = tcx
        .typeck(expression.hir_id.owner)
        .type_dependent_def_id(expression.hir_id)?;
    if definition.is_local() || tcx.crate_name(definition.krate).as_str() != "core" {
        return None;
    }
    let path = tcx.def_path(definition).data;
    let names = path
        .iter()
        .filter_map(|component| component.data.get_opt_name())
        .collect::<Vec<_>>();
    if names.len() < 3
        || names[names.len() - 3].as_str() != "ptr"
        || !matches!(names[names.len() - 2].as_str(), "const_ptr" | "mut_ptr")
    {
        return None;
    }
    let name = *names.last()?;
    matches!(
        name.as_str(),
        "offset"
            | "add"
            | "sub"
            | "wrapping_offset"
            | "wrapping_add"
            | "wrapping_sub"
            | "offset_from"
            | "is_null"
    )
    .then_some(name)
}

fn expression_type<'tcx>(
    expression: &Expr,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
) -> Option<ty::Ty<'tcx>> {
    let expression = ast_to_hir.get_expr(expression.id, tcx)?;
    Some(tcx.typeck(expression.hir_id.owner).expr_ty(expression))
}

fn pointer_like(ty: ty::Ty<'_>, tcx: TyCtxt<'_>) -> bool {
    match ty.kind() {
        ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..) => true,
        ty::TyKind::Adt(definition, arguments) if utils::ir::is_option(definition.did(), tcx) => {
            arguments.types().next().is_some_and(|inner| {
                matches!(inner.kind(), ty::TyKind::Ref(..)) || is_box(inner, tcx)
            })
        }
        ty::TyKind::Adt(..) => is_box(ty, tcx),
        _ => false,
    }
}

fn is_box(ty: ty::Ty<'_>, tcx: TyCtxt<'_>) -> bool {
    matches!(ty.kind(), ty::TyKind::Adt(definition, _) if tcx.is_lang_item(definition.did(), rustc_hir::LangItem::OwnedBox))
}

fn scalar_type(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Bool
            | ty::TyKind::Char
            | ty::TyKind::Int(..)
            | ty::TyKind::Uint(..)
            | ty::TyKind::Float(..)
    )
}

fn builtin_operator_operand(ty: ty::Ty<'_>) -> bool {
    scalar_type(ty) || matches!(ty.kind(), ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..))
}

fn resolved_definition(
    expression: &Expr,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<DefId> {
    let expression = ast_to_hir.get_expr(expression.id, tcx)?;
    let hir::ExprKind::Path(path) = expression.kind else { return None };
    match tcx
        .typeck(expression.hir_id.owner)
        .qpath_res(&path, expression.hir_id)
    {
        Res::Def(_, id) => Some(id),
        _ => None,
    }
}

fn merge_regions(regions: &mut Vec<SelectedRegion>) {
    let mut merged: Vec<SelectedRegion> = vec![];
    for region in regions.drain(..) {
        if let Some(existing) = merged
            .iter_mut()
            .find(|existing| existing.root == region.root)
        {
            for anchor in region.anchors {
                if !existing
                    .anchors
                    .iter()
                    .any(|value| value.source_binding == anchor.source_binding)
                {
                    existing.anchors.push(anchor);
                }
            }
        } else {
            merged.push(region);
        }
    }
    *regions = merged;
}

fn regions_overlap(regions: &[SelectedRegion], tree: &ExpressionTree<'_>) -> bool {
    for (index, region) in regions.iter().enumerate() {
        let mut current = region.root;
        while let Some(edge) = tree.parents.get(&current) {
            current = edge.parent;
            if regions
                .iter()
                .enumerate()
                .any(|(other, value)| other != index && value.root == current)
            {
                return true;
            }
        }
    }
    false
}

#[allow(clippy::too_many_arguments)]
fn align_expression<'a>(
    source: &Expr,
    target: &'a Expr,
    selected: &HashSet<NodeId>,
    bindings: &HashMap<hir::HirId, hir::HirId>,
    callables: &HashMap<DefId, u64>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
    mappings: &mut HashMap<NodeId, &'a Expr>,
) -> bool {
    if selected.contains(&source.id) {
        mappings.insert(source.id, target);
        return true;
    }
    if let ExprKind::Paren(inner) = &source.kind {
        return align_expression(
            inner, target, selected, bindings, callables, ast_to_hir, tcx, mappings,
        );
    }
    if let ExprKind::Paren(inner) = &target.kind {
        return align_expression(
            source, inner, selected, bindings, callables, ast_to_hir, tcx, mappings,
        );
    }
    macro_rules! pair {
        ($left:expr, $right:expr) => {
            align_expression(
                $left, $right, selected, bindings, callables, ast_to_hir, tcx, mappings,
            )
        };
    }
    macro_rules! list {
        ($left:expr, $right:expr) => {{
            $left.len() == $right.len()
                && $left
                    .iter()
                    .zip($right)
                    .all(|(left, right)| pair!(left, right))
        }};
    }
    match (&source.kind, &target.kind) {
        (ExprKind::Array(left), ExprKind::Array(right))
        | (ExprKind::Tup(left), ExprKind::Tup(right)) => list!(left, right),
        (ExprKind::Call(left_callee, left_args), ExprKind::Call(right_callee, right_args)) => {
            pair!(left_callee, right_callee) && list!(left_args, right_args)
        }
        (ExprKind::MethodCall(left), ExprKind::MethodCall(right)) => {
            method_calls_correspond(source, target, callables, ast_to_hir, tcx)
                && pair!(&left.receiver, &right.receiver)
                && list!(&left.args, &right.args)
        }
        (
            ExprKind::Binary(left_op, left_a, left_b),
            ExprKind::Binary(right_op, right_a, right_b),
        ) => {
            left_op.node == right_op.node
                && operators_correspond(source, target, ast_to_hir, tcx)
                && pair!(left_a, right_a)
                && pair!(left_b, right_b)
        }
        (ExprKind::Unary(left_op, left), ExprKind::Unary(right_op, right)) => {
            left_op == right_op
                && operators_correspond(source, target, ast_to_hir, tcx)
                && pair!(left, right)
        }
        (ExprKind::Cast(left, left_ty), ExprKind::Cast(right, right_ty)) => {
            semantic_types_equal(left_ty, right_ty, ast_to_hir, tcx) && pair!(left, right)
        }
        (ExprKind::If(left_c, left_t, left_f), ExprKind::If(right_c, right_t, right_f)) => {
            pair!(left_c, right_c)
                && align_block(
                    left_t, right_t, selected, bindings, callables, ast_to_hir, tcx, mappings,
                )
                && match (left_f, right_f) {
                    (None, None) => true,
                    (Some(left), Some(right)) => pair!(left, right),
                    _ => false,
                }
        }
        (
            ExprKind::While(left_c, left_b, left_label),
            ExprKind::While(right_c, right_b, right_label),
        ) => {
            left_label.is_none()
                && right_label.is_none()
                && pair!(left_c, right_c)
                && align_block(
                    left_b, right_b, selected, bindings, callables, ast_to_hir, tcx, mappings,
                )
        }
        (ExprKind::Loop(left_b, left_label, _), ExprKind::Loop(right_b, right_label, _)) => {
            left_label.is_none()
                && right_label.is_none()
                && align_block(
                    left_b, right_b, selected, bindings, callables, ast_to_hir, tcx, mappings,
                )
        }
        (
            ExprKind::Match(left_scrutinee, left_arms, left_kind),
            ExprKind::Match(right_scrutinee, right_arms, right_kind),
        ) => {
            left_kind == right_kind
                && pair!(left_scrutinee, right_scrutinee)
                && left_arms.len() == right_arms.len()
                && left_arms.iter().zip(right_arms).all(|(left, right)| {
                    patterns_correspond(&left.pat, &right.pat, bindings, ast_to_hir, tcx)
                        && align_optional_expression(
                            left.guard.as_deref(),
                            right.guard.as_deref(),
                            selected,
                            bindings,
                            callables,
                            ast_to_hir,
                            tcx,
                            mappings,
                        )
                        && align_optional_expression(
                            left.body.as_deref(),
                            right.body.as_deref(),
                            selected,
                            bindings,
                            callables,
                            ast_to_hir,
                            tcx,
                            mappings,
                        )
                })
        }
        (ExprKind::Assign(left_a, left_b, _), ExprKind::Assign(right_a, right_b, _)) => {
            pair!(left_a, right_a) && pair!(left_b, right_b)
        }
        (
            ExprKind::AssignOp(left_op, left_a, left_b),
            ExprKind::AssignOp(right_op, right_a, right_b),
        ) => {
            left_op.node == right_op.node
                && operators_correspond(source, target, ast_to_hir, tcx)
                && pair!(left_a, right_a)
                && pair!(left_b, right_b)
        }
        (ExprKind::Field(left, left_field), ExprKind::Field(right, right_field)) => {
            same_resolved(
                resolved_field(left, left_field.name, ast_to_hir, tcx),
                resolved_field(right, right_field.name, ast_to_hir, tcx),
            ) && pair!(left, right)
        }
        (ExprKind::Index(left_a, left_b, _), ExprKind::Index(right_a, right_b, _)) => {
            operators_correspond(source, target, ast_to_hir, tcx)
                && pair!(left_a, right_a)
                && pair!(left_b, right_b)
        }
        (
            ExprKind::Range(left_start, left_end, left_limits),
            ExprKind::Range(right_start, right_end, right_limits),
        ) => {
            left_limits == right_limits
                && align_optional_expression(
                    left_start.as_deref(),
                    right_start.as_deref(),
                    selected,
                    bindings,
                    callables,
                    ast_to_hir,
                    tcx,
                    mappings,
                )
                && align_optional_expression(
                    left_end.as_deref(),
                    right_end.as_deref(),
                    selected,
                    bindings,
                    callables,
                    ast_to_hir,
                    tcx,
                    mappings,
                )
        }
        (
            ExprKind::AddrOf(left_kind, left_mut, left),
            ExprKind::AddrOf(right_kind, right_mut, right),
        ) => left_kind == right_kind && left_mut == right_mut && pair!(left, right),
        (ExprKind::Ret(left), ExprKind::Ret(right)) => align_optional_expression(
            left.as_deref(),
            right.as_deref(),
            selected,
            bindings,
            callables,
            ast_to_hir,
            tcx,
            mappings,
        ),
        (ExprKind::Break(left_label, left), ExprKind::Break(right_label, right)) => {
            left_label.is_none()
                && right_label.is_none()
                && align_optional_expression(
                    left.as_deref(),
                    right.as_deref(),
                    selected,
                    bindings,
                    callables,
                    ast_to_hir,
                    tcx,
                    mappings,
                )
        }
        (ExprKind::Continue(left), ExprKind::Continue(right)) => left.is_none() && right.is_none(),
        (ExprKind::Repeat(left_value, left_count), ExprKind::Repeat(right_value, right_count)) => {
            pair!(left_value, right_value)
                && semantic_literal_expression(
                    &left_count.value,
                    &right_count.value,
                    Some("usize"),
                    ast_to_hir,
                    tcx,
                )
        }
        (ExprKind::Block(left, _), ExprKind::Block(right, _)) => align_block(
            left, right, selected, bindings, callables, ast_to_hir, tcx, mappings,
        ),
        (ExprKind::Path(..), ExprKind::Path(..)) => {
            paths_correspond(source, target, bindings, callables, ast_to_hir, tcx)
        }
        (ExprKind::Lit(..), ExprKind::Lit(..)) => {
            semantic_literal_expression(source, target, None, ast_to_hir, tcx)
        }
        (ExprKind::Struct(left), ExprKind::Struct(right)) => {
            same_resolved(
                resolved_struct(source, ast_to_hir, tcx),
                resolved_struct(target, ast_to_hir, tcx),
            ) && left.fields.len() == right.fields.len()
                && left.fields.iter().zip(&right.fields).all(|(left, right)| {
                    same_resolved(
                        resolved_struct_field(source, left.ident.name, ast_to_hir, tcx),
                        resolved_struct_field(target, right.ident.name, ast_to_hir, tcx),
                    ) && pair!(&left.expr, &right.expr)
                })
                && match (&left.rest, &right.rest) {
                    (rustc_ast::StructRest::None, rustc_ast::StructRest::None) => true,
                    (rustc_ast::StructRest::Base(left), rustc_ast::StructRest::Base(right)) => {
                        pair!(left, right)
                    }
                    _ => false,
                }
        }
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn align_optional_expression<'a>(
    source: Option<&Expr>,
    target: Option<&'a Expr>,
    selected: &HashSet<NodeId>,
    bindings: &HashMap<hir::HirId, hir::HirId>,
    callables: &HashMap<DefId, u64>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
    mappings: &mut HashMap<NodeId, &'a Expr>,
) -> bool {
    match (source, target) {
        (None, None) => true,
        (Some(source), Some(target)) => align_expression(
            source, target, selected, bindings, callables, ast_to_hir, tcx, mappings,
        ),
        _ => false,
    }
}

#[allow(clippy::too_many_arguments)]
fn align_block<'a>(
    source: &rustc_ast::Block,
    target: &'a rustc_ast::Block,
    selected: &HashSet<NodeId>,
    bindings: &HashMap<hir::HirId, hir::HirId>,
    callables: &HashMap<DefId, u64>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
    mappings: &mut HashMap<NodeId, &'a Expr>,
) -> bool {
    source.stmts.len() == target.stmts.len()
        && source
            .stmts
            .iter()
            .zip(&target.stmts)
            .all(|(source, target)| match (&source.kind, &target.kind) {
                (StmtKind::Expr(source), StmtKind::Expr(target))
                | (StmtKind::Semi(source), StmtKind::Semi(target)) => align_expression(
                    source, target, selected, bindings, callables, ast_to_hir, tcx, mappings,
                ),
                (StmtKind::Let(source), StmtKind::Let(target)) => {
                    patterns_correspond(&source.pat, &target.pat, bindings, ast_to_hir, tcx)
                        && local_annotations_correspond(source, target, bindings, ast_to_hir, tcx)
                        && match (&source.kind, &target.kind) {
                            (rustc_ast::LocalKind::Decl, rustc_ast::LocalKind::Decl) => true,
                            (
                                rustc_ast::LocalKind::Init(source),
                                rustc_ast::LocalKind::Init(target),
                            ) => align_expression(
                                source, target, selected, bindings, callables, ast_to_hir, tcx,
                                mappings,
                            ),
                            _ => false,
                        }
                }
                _ => false,
            })
}

fn operators_correspond(
    source: &Expr,
    target: &Expr,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    let (Some(source), Some(target)) = (
        ast_to_hir.get_expr(source.id, tcx),
        ast_to_hir.get_expr(target.id, tcx),
    ) else {
        return false;
    };
    let source = tcx
        .typeck(source.hir_id.owner)
        .type_dependent_def_id(source.hir_id);
    let target = tcx
        .typeck(target.hir_id.owner)
        .type_dependent_def_id(target.hir_id);
    matches!((source, target), (None, None))
        || matches!((source, target), (Some(source), Some(target)) if source == target)
}

fn local_annotations_correspond(
    source: &rustc_ast::Local,
    target: &rustc_ast::Local,
    bindings: &HashMap<hir::HirId, hir::HirId>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    let paired = match (
        simple_binding(&source.pat, ast_to_hir, tcx),
        simple_binding(&target.pat, ast_to_hir, tcx),
    ) {
        (Some((_, source)), Some((_, target))) => bindings.get(&source) == Some(&target),
        _ => false,
    };
    paired
        || match (&source.ty, &target.ty) {
            (None, None) => true,
            (Some(source), Some(target)) => semantic_types_equal(source, target, ast_to_hir, tcx),
            _ => false,
        }
}

fn patterns_correspond(
    source: &rustc_ast::Pat,
    target: &rustc_ast::Pat,
    bindings: &HashMap<hir::HirId, hir::HirId>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    match (&source.kind, &target.kind) {
        (PatKind::Wild, PatKind::Wild) => true,
        (PatKind::Ident(source_mode, _, None), PatKind::Ident(target_mode, _, None))
            if source_mode == target_mode =>
        {
            match (
                simple_binding(source, ast_to_hir, tcx),
                simple_binding(target, ast_to_hir, tcx),
            ) {
                (Some((_, source)), Some((_, target))) => bindings.get(&source) == Some(&target),
                (None, None) => {
                    resolved_pattern(source.id, ast_to_hir, tcx).is_some_and(|resolution| {
                        resolved_pattern(target.id, ast_to_hir, tcx) == Some(resolution)
                    })
                }
                _ => false,
            }
        }
        (PatKind::Expr(source), PatKind::Expr(target)) => match (&source.kind, &target.kind) {
            (ExprKind::Lit(..), ExprKind::Lit(..))
            | (
                ExprKind::Unary(rustc_ast::UnOp::Neg, _),
                ExprKind::Unary(rustc_ast::UnOp::Neg, _),
            ) => semantic_literal_expression(source, target, None, ast_to_hir, tcx),
            _ => resolved_pattern(source.id, ast_to_hir, tcx).is_some_and(|resolution| {
                resolved_pattern(target.id, ast_to_hir, tcx) == Some(resolution)
            }),
        },
        (PatKind::Path(..), PatKind::Path(..)) => resolved_pattern(source.id, ast_to_hir, tcx)
            .is_some_and(|resolution| {
                resolved_pattern(target.id, ast_to_hir, tcx) == Some(resolution)
            }),
        (PatKind::Tuple(source), PatKind::Tuple(target))
        | (PatKind::Or(source), PatKind::Or(target)) => {
            source.len() == target.len()
                && source.iter().zip(target).all(|(source, target)| {
                    patterns_correspond(source, target, bindings, ast_to_hir, tcx)
                })
        }
        (PatKind::Ref(source, source_mut), PatKind::Ref(target, target_mut)) => {
            source_mut == target_mut
                && patterns_correspond(source, target, bindings, ast_to_hir, tcx)
        }
        _ => false,
    }
}

fn resolved_pattern(id: NodeId, ast_to_hir: &utils::ir::AstToHir, tcx: TyCtxt<'_>) -> Option<Res> {
    let pattern = ast_to_hir.get_pat(id, tcx)?;
    let path = match pattern.kind {
        hir::PatKind::Expr(hir::PatExpr {
            kind: hir::PatExprKind::Path(path),
            ..
        }) => path,
        hir::PatKind::Struct(ref path, ..) | hir::PatKind::TupleStruct(ref path, ..) => path,
        _ => return None,
    };
    Some(
        tcx.typeck(pattern.hir_id.owner)
            .qpath_res(path, pattern.hir_id),
    )
}

fn semantic_literal_expression(
    source: &Expr,
    target: &Expr,
    forced_type: Option<&str>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    fn split_negation(expression: &Expr) -> (bool, &Expr) {
        if let ExprKind::Unary(rustc_ast::UnOp::Neg, inner) = &expression.kind {
            (true, inner)
        } else {
            (false, expression)
        }
    }
    let (source_negative, source) = split_negation(source);
    let (target_negative, target) = split_negation(target);
    if source_negative != target_negative {
        return false;
    }
    let (ExprKind::Lit(..), ExprKind::Lit(..)) = (&source.kind, &target.kind) else {
        return false;
    };
    let bindings = HashMap::new();
    let callables = HashMap::new();
    let mut context = DumpContext::new(&bindings, &callables, ast_to_hir, tcx);
    context.literal_with_type(source, forced_type) == context.literal_with_type(target, forced_type)
}

fn same_resolved<T: PartialEq>(source: Option<T>, target: Option<T>) -> bool {
    source.is_some() && source == target
}

fn resolved_field(
    base: &Expr,
    name: Symbol,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<(DefId, DefId)> {
    let base = ast_to_hir.get_expr(base.id, tcx)?;
    let mut ty = tcx.typeck(base.hir_id.owner).expr_ty_adjusted(base);
    while let ty::TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    let ty::TyKind::Adt(definition, _) = ty.kind() else { return None };
    if definition.is_enum() {
        return None;
    }
    let field = definition
        .non_enum_variant()
        .fields
        .iter()
        .find(|field| field.name == name)?;
    Some((definition.did(), field.did))
}

fn resolved_struct(
    expression: &Expr,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<(DefId, Option<DefId>)> {
    let expression = ast_to_hir.get_expr(expression.id, tcx)?;
    let hir::ExprKind::Struct(path, ..) = expression.kind else { return None };
    let Res::Def(kind, id) = tcx
        .typeck(expression.hir_id.owner)
        .qpath_res(path, expression.hir_id)
    else {
        return None;
    };
    match kind {
        hir::def::DefKind::Struct | hir::def::DefKind::Union => Some((id, None)),
        hir::def::DefKind::Variant => Some((tcx.parent(id), Some(id))),
        _ => None,
    }
}

fn resolved_struct_field(
    expression: &Expr,
    name: Symbol,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<(DefId, DefId)> {
    let (adt, variant) = resolved_struct(expression, ast_to_hir, tcx)?;
    let definition = tcx.adt_def(adt);
    let variant = variant.map_or_else(
        || definition.non_enum_variant(),
        |variant| {
            definition
                .variants()
                .iter()
                .find(|value| value.def_id == variant)
                .unwrap()
        },
    );
    let field = variant.fields.iter().find(|field| field.name == name)?;
    Some((adt, field.did))
}

fn method_calls_correspond(
    source: &Expr,
    target: &Expr,
    callables: &HashMap<DefId, u64>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    let (Some(source), Some(target)) = (
        ast_to_hir.get_expr(source.id, tcx),
        ast_to_hir.get_expr(target.id, tcx),
    ) else {
        return false;
    };
    let (Some(source), Some(target)) = (
        tcx.typeck(source.hir_id.owner)
            .type_dependent_def_id(source.hir_id),
        tcx.typeck(target.hir_id.owner)
            .type_dependent_def_id(target.hir_id),
    ) else {
        return false;
    };
    source == target
        || callables
            .get(&source)
            .is_some_and(|logical| callables.get(&target) == Some(logical))
}

fn semantic_types_equal(
    source: &rustc_ast::Ty,
    target: &rustc_ast::Ty,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    let Some(source) = ast_to_hir.get_ty(source.id, tcx) else { return false };
    let Some(target) = ast_to_hir.get_ty(target.id, tcx) else { return false };
    tcx.erase_regions(tcx.typeck(source.hir_id.owner).node_type(source.hir_id))
        == tcx.erase_regions(tcx.typeck(target.hir_id.owner).node_type(target.hir_id))
}

fn paths_correspond(
    source: &Expr,
    target: &Expr,
    bindings: &HashMap<hir::HirId, hir::HirId>,
    callables: &HashMap<DefId, u64>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> bool {
    let (Some(source), Some(target)) = (
        ast_to_hir.get_expr(source.id, tcx),
        ast_to_hir.get_expr(target.id, tcx),
    ) else {
        return false;
    };
    let (hir::ExprKind::Path(source_path), hir::ExprKind::Path(target_path)) =
        (&source.kind, &target.kind)
    else {
        return false;
    };
    let source_res = tcx
        .typeck(source.hir_id.owner)
        .qpath_res(source_path, source.hir_id);
    let target_res = tcx
        .typeck(target.hir_id.owner)
        .qpath_res(target_path, target.hir_id);
    match (source_res, target_res) {
        (Res::Local(source), Res::Local(target)) => bindings.get(&source) == Some(&target),
        (Res::Def(_, source), Res::Def(_, target)) => {
            source == target
                || callables
                    .get(&source)
                    .is_some_and(|logical| callables.get(&target) == Some(logical))
        }
        _ => source_res == target_res,
    }
}

#[allow(clippy::too_many_arguments)]
fn dump_observation(
    source: &Expr,
    target: &Expr,
    anchors: &[AnchorPair],
    bindings: &HashMap<hir::HirId, hir::HirId>,
    callables: &HashMap<DefId, u64>,
    ast_to_hir: &utils::ir::AstToHir,
    tcx: TyCtxt<'_>,
) -> Option<Observation> {
    let mut context = DumpContext::new(bindings, callables, ast_to_hir, tcx);
    context.source_side = true;
    let source_expression = context.expression(source)?;
    context.source_side = false;
    let target_expression = context.expression(target)?;
    let mut pointer_anchors = vec![];
    for anchor in anchors {
        let id = context.binding_id(anchor.source_binding, true)?;
        let source_type = binding_type(anchor.source_binding, tcx)?;
        let target_type = binding_type(anchor.target_binding, tcx)?;
        pointer_anchors.push(PointerAnchor {
            id,
            source_type: context.type_tree(source_type)?,
            target_type: context.type_tree(target_type)?,
        });
    }
    let source_hir = ast_to_hir.get_expr(source.id, tcx)?;
    let target_hir = ast_to_hir.get_expr(target.id, tcx)?;
    let source_typeck = tcx.typeck(source_hir.hir_id.owner);
    let target_typeck = tcx.typeck(target_hir.hir_id.owner);
    Some(Observation {
        source_expression,
        target_expression,
        pointer_anchors,
        source_type: context.type_tree(source_typeck.expr_ty(source_hir))?,
        source_adjusted_type: context.type_tree(source_typeck.expr_ty_adjusted(source_hir))?,
        target_type: context.type_tree(target_typeck.expr_ty(target_hir))?,
        target_adjusted_type: context.type_tree(target_typeck.expr_ty_adjusted(target_hir))?,
    })
}

fn binding_type<'tcx>(binding: hir::HirId, tcx: TyCtxt<'tcx>) -> Option<ty::Ty<'tcx>> {
    Some(tcx.typeck(binding.owner).node_type(binding))
}

struct DumpContext<'a, 'tcx> {
    reverse_bindings: HashMap<hir::HirId, hir::HirId>,
    callables: &'a HashMap<DefId, u64>,
    ast_to_hir: &'a utils::ir::AstToHir,
    tcx: TyCtxt<'tcx>,
    source_side: bool,
    binding_ids: HashMap<hir::HirId, String>,
    function_ids: HashMap<u64, String>,
    local_function_ids: HashMap<DefId, String>,
    adt_ids: HashMap<DefId, String>,
    field_ids: HashMap<DefId, String>,
    variant_ids: HashMap<DefId, String>,
    constant_ids: HashMap<DefId, String>,
    static_ids: HashMap<DefId, String>,
    method_ids: HashMap<DefId, String>,
}

impl<'a, 'tcx> DumpContext<'a, 'tcx> {
    fn new(
        bindings: &'a HashMap<hir::HirId, hir::HirId>,
        callables: &'a HashMap<DefId, u64>,
        ast_to_hir: &'a utils::ir::AstToHir,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self {
            reverse_bindings: bindings
                .iter()
                .map(|(source, target)| (*target, *source))
                .collect(),
            callables,
            ast_to_hir,
            tcx,
            source_side: true,
            binding_ids: HashMap::new(),
            function_ids: HashMap::new(),
            local_function_ids: HashMap::new(),
            adt_ids: HashMap::new(),
            field_ids: HashMap::new(),
            variant_ids: HashMap::new(),
            constant_ids: HashMap::new(),
            static_ids: HashMap::new(),
            method_ids: HashMap::new(),
        }
    }

    fn binding_id(&mut self, binding: hir::HirId, source_side: bool) -> Option<String> {
        if !source_side {
            let source = self.reverse_bindings.get(&binding)?;
            return self.binding_ids.get(source).cloned();
        }
        let source = binding;
        if let Some(id) = self.binding_ids.get(&source) {
            return Some(id.clone());
        }
        let id = format!("<id{}>", self.binding_ids.len());
        self.binding_ids.insert(source, id.clone());
        Some(id)
    }

    fn type_tree(&mut self, value: ty::Ty<'tcx>) -> Option<TypeTree> {
        let value = self
            .tcx
            .try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), value)
            .unwrap_or(value);
        match value.kind() {
            ty::TyKind::Bool => Some(TypeTree::Primitive {
                name: "bool".into(),
            }),
            ty::TyKind::Char => Some(TypeTree::Primitive {
                name: "char".into(),
            }),
            ty::TyKind::Str => Some(TypeTree::Primitive { name: "str".into() }),
            ty::TyKind::Never => Some(TypeTree::Primitive {
                name: "never".into(),
            }),
            ty::TyKind::Int(kind) => Some(TypeTree::Primitive {
                name: kind.name_str().into(),
            }),
            ty::TyKind::Uint(kind) => Some(TypeTree::Primitive {
                name: kind.name_str().into(),
            }),
            ty::TyKind::Float(kind) => Some(TypeTree::Primitive {
                name: kind.name_str().into(),
            }),
            ty::TyKind::Slice(element) => Some(TypeTree::Slice {
                element: Box::new(self.type_tree(*element)?),
            }),
            ty::TyKind::Array(element, length) => Some(TypeTree::Array {
                element: Box::new(self.type_tree(*element)?),
                length: length.try_to_target_usize(self.tcx)?,
            }),
            ty::TyKind::RawPtr(element, mutability) => Some(TypeTree::RawPointer {
                mutability: if mutability.is_mut() {
                    RawMutability::Mut
                } else {
                    RawMutability::Const
                },
                pointee: Box::new(self.type_tree(*element)?),
            }),
            ty::TyKind::Ref(_, element, mutability) => Some(TypeTree::Reference {
                mutability: if mutability.is_mut() {
                    RefMutability::Mutable
                } else {
                    RefMutability::Shared
                },
                pointee: Box::new(self.type_tree(*element)?),
            }),
            ty::TyKind::Tuple(elements) => Some(TypeTree::Tuple {
                elements: elements
                    .iter()
                    .map(|element| self.type_tree(element))
                    .collect::<Option<_>>()?,
            }),
            ty::TyKind::Adt(definition, arguments) => {
                let arguments = arguments
                    .iter()
                    .filter_map(|argument| match argument.kind() {
                        ty::GenericArgKind::Lifetime(_) => None,
                        other => Some(other),
                    })
                    .map(|argument| match argument {
                        ty::GenericArgKind::Type(value) => self.type_tree(value),
                        ty::GenericArgKind::Const(_) => None,
                        ty::GenericArgKind::Lifetime(_) => unreachable!(),
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(TypeTree::Adt {
                    adt_kind: if definition.is_struct() {
                        AdtKind::Struct
                    } else if definition.is_enum() {
                        AdtKind::Enum
                    } else {
                        AdtKind::Union
                    },
                    identity: self.adt_identity(definition.did()),
                    arguments,
                })
            }
            _ => None,
        }
    }

    fn adt_identity(&mut self, id: DefId) -> AdtIdentity {
        if id.is_local() {
            let prefix = match self.tcx.def_kind(id) {
                hir::def::DefKind::Struct => "struct",
                hir::def::DefKind::Enum => "enum",
                hir::def::DefKind::Union => "union",
                _ => "adt",
            };
            let identity_prefix = format!("<{prefix}");
            let next = self
                .adt_ids
                .values()
                .filter(|value| value.starts_with(&identity_prefix))
                .count();
            let value = self
                .adt_ids
                .entry(id)
                .or_insert_with(|| format!("<{prefix}{next}>"))
                .clone();
            AdtIdentity::Local { id: value }
        } else {
            let (crate_name, path) = external_identity(id, self.tcx);
            AdtIdentity::External { crate_name, path }
        }
    }

    fn field_identity(&mut self, id: DefId, owner: DefId) -> FieldIdentity {
        if id.is_local() {
            let next = self.field_ids.len();
            let value = self
                .field_ids
                .entry(id)
                .or_insert_with(|| format!("<field{next}>"))
                .clone();
            FieldIdentity::Local {
                owner: self.adt_identity(owner),
                id: value,
            }
        } else {
            let (crate_name, path) = external_identity(id, self.tcx);
            FieldIdentity::External { crate_name, path }
        }
    }

    fn variant_identity(&mut self, id: DefId, owner: DefId) -> VariantIdentity {
        if id.is_local() {
            let next = self.variant_ids.len();
            let value = self
                .variant_ids
                .entry(id)
                .or_insert_with(|| format!("<variant{next}>"))
                .clone();
            VariantIdentity::Local {
                owner: self.adt_identity(owner),
                id: value,
            }
        } else {
            let (crate_name, path) = external_identity(id, self.tcx);
            VariantIdentity::External { crate_name, path }
        }
    }

    fn field_for_base(&mut self, value: &Expr, name: rustc_span::Symbol) -> Option<FieldIdentity> {
        let hir = self.ast_to_hir.get_expr(value.id, self.tcx)?;
        let mut ty = self.tcx.typeck(hir.hir_id.owner).expr_ty_adjusted(hir);
        while let ty::TyKind::Ref(_, inner, _) = ty.kind() {
            ty = *inner;
        }
        let ty::TyKind::Adt(definition, _) = ty.kind() else { return None };
        if definition.is_enum() {
            return None;
        }
        let field = definition
            .non_enum_variant()
            .fields
            .iter()
            .find(|field| field.name == name)?;
        Some(self.field_identity(field.did, definition.did()))
    }

    fn struct_identity(
        &mut self,
        value: &Expr,
    ) -> Option<(AdtIdentity, Option<VariantIdentity>, DefId)> {
        let hir = self.ast_to_hir.get_expr(value.id, self.tcx)?;
        let hir::ExprKind::Struct(path, _, _) = hir.kind else { return None };
        let resolution = self
            .tcx
            .typeck(hir.hir_id.owner)
            .qpath_res(path, hir.hir_id);
        let Res::Def(kind, id) = resolution else { return None };
        match kind {
            hir::def::DefKind::Struct | hir::def::DefKind::Union => {
                Some((self.adt_identity(id), None, id))
            }
            hir::def::DefKind::Variant => {
                let owner = self.tcx.parent(id);
                Some((
                    self.adt_identity(owner),
                    Some(self.variant_identity(id, owner)),
                    id,
                ))
            }
            _ => None,
        }
    }

    fn expression(&mut self, value: &Expr) -> Option<Expression> {
        if !value.attrs.is_empty() {
            return None;
        }
        match &value.kind {
            ExprKind::Paren(inner) => self.expression(inner),
            ExprKind::Array(values) => Some(Expression::Array {
                elements: values
                    .iter()
                    .map(|value| self.expression(value))
                    .collect::<Option<_>>()?,
            }),
            ExprKind::Tup(values) => Some(Expression::Tuple {
                elements: values
                    .iter()
                    .map(|value| self.expression(value))
                    .collect::<Option<_>>()?,
            }),
            ExprKind::Call(callee, args) => Some(Expression::Call {
                callee: Box::new(self.expression(callee)?),
                arguments: args
                    .iter()
                    .map(|value| self.expression(value))
                    .collect::<Option<_>>()?,
            }),
            ExprKind::MethodCall(call) => {
                let hir = self.ast_to_hir.get_expr(value.id, self.tcx)?;
                let def = self
                    .tcx
                    .typeck(hir.hir_id.owner)
                    .type_dependent_def_id(hir.hir_id)?;
                Some(Expression::MethodCall {
                    receiver: Box::new(self.expression(&call.receiver)?),
                    method: self.method_identity(def)?,
                    arguments: call
                        .args
                        .iter()
                        .map(|value| self.expression(value))
                        .collect::<Option<_>>()?,
                })
            }
            ExprKind::Binary(operator, left, right) => Some(Expression::Binary {
                operator: binary_operator(operator.node)?,
                left: Box::new(self.expression(left)?),
                right: Box::new(self.expression(right)?),
            }),
            ExprKind::Unary(operator, operand) => Some(Expression::Unary {
                operator: match operator {
                    rustc_ast::UnOp::Deref => UnaryOperator::Deref,
                    rustc_ast::UnOp::Not => UnaryOperator::Not,
                    rustc_ast::UnOp::Neg => UnaryOperator::Negate,
                },
                operand: Box::new(self.expression(operand)?),
            }),
            ExprKind::Lit(_) => Some(Expression::Literal {
                value: self.literal(value)?,
            }),
            ExprKind::Cast(expression, ty) => {
                let hir_ty = self.ast_to_hir.get_ty(ty.id, self.tcx)?;
                let semantic = self
                    .tcx
                    .typeck(hir_ty.hir_id.owner)
                    .node_type(hir_ty.hir_id);
                Some(Expression::Cast {
                    expression: Box::new(self.expression(expression)?),
                    ty: self.type_tree(semantic)?,
                })
            }
            ExprKind::Path(..) => Some(Expression::Path {
                value: self.path_identity(value)?,
            }),
            ExprKind::Index(base, index, _) => Some(Expression::Index {
                base: Box::new(self.expression(base)?),
                index: Box::new(self.expression(index)?),
            }),
            ExprKind::Assign(left, right, _) => Some(Expression::Assign {
                left: Box::new(self.expression(left)?),
                right: Box::new(self.expression(right)?),
            }),
            ExprKind::AssignOp(operator, left, right) => Some(Expression::AssignOp {
                operator: binary_operator(operator.node.into())?,
                left: Box::new(self.expression(left)?),
                right: Box::new(self.expression(right)?),
            }),
            ExprKind::Field(base, field) => Some(Expression::Field {
                base: Box::new(self.expression(base)?),
                field: self.field_for_base(base, field.name)?,
            }),
            ExprKind::AddrOf(kind, mutability, expression) => Some(Expression::AddressOf {
                borrow: match kind {
                    rustc_ast::BorrowKind::Ref => BorrowKind::Reference,
                    rustc_ast::BorrowKind::Raw => BorrowKind::Raw,
                },
                mutability: if mutability.is_mut() {
                    RawMutability::Mut
                } else {
                    RawMutability::Const
                },
                expression: Box::new(self.expression(expression)?),
            }),
            ExprKind::Ret(value) => Some(Expression::Return {
                value: match value {
                    Some(value) => Some(Box::new(self.expression(value)?)),
                    None => None,
                },
            }),
            ExprKind::Break(label, value) if label.is_none() => Some(Expression::Break {
                value: match value {
                    Some(value) => Some(Box::new(self.expression(value)?)),
                    None => None,
                },
            }),
            ExprKind::Continue(label) if label.is_none() => Some(Expression::Continue),
            ExprKind::Repeat(value, count) => Some(Expression::Repeat {
                value: Box::new(self.expression(value)?),
                count: Box::new(Expression::Literal {
                    value: self.literal_with_type(&count.value, Some("usize"))?,
                }),
            }),
            ExprKind::Block(block, label) if label.is_none() => Some(Expression::Block {
                block: self.block(block)?,
            }),
            ExprKind::If(condition, then, otherwise) => Some(Expression::If {
                condition: Box::new(self.expression(condition)?),
                then: self.block(then)?,
                else_expression: match otherwise {
                    Some(value) => Some(Box::new(self.expression(value)?)),
                    None => None,
                },
            }),
            ExprKind::While(condition, body, label) if label.is_none() => Some(Expression::While {
                condition: Box::new(self.expression(condition)?),
                body: self.block(body)?,
            }),
            ExprKind::Loop(body, label, _) if label.is_none() => Some(Expression::Loop {
                body: self.block(body)?,
            }),
            ExprKind::Range(start, end, limits) => Some(Expression::Range {
                start: match start {
                    Some(value) => Some(Box::new(self.expression(value)?)),
                    None => None,
                },
                end: match end {
                    Some(value) => Some(Box::new(self.expression(value)?)),
                    None => None,
                },
                limits: match limits {
                    rustc_ast::RangeLimits::HalfOpen => RangeLimits::HalfOpen,
                    rustc_ast::RangeLimits::Closed => RangeLimits::Closed,
                },
            }),
            ExprKind::Struct(struct_value) => {
                let (adt, variant, definition) = self.struct_identity(value)?;
                let adt_definition = self.tcx.adt_def(match self.tcx.def_kind(definition) {
                    hir::def::DefKind::Variant => self.tcx.parent(definition),
                    _ => definition,
                });
                let variant_definition = if adt_definition.is_enum() {
                    adt_definition
                        .variants()
                        .iter()
                        .find(|variant| variant.def_id == definition)?
                } else {
                    adt_definition.non_enum_variant()
                };
                let mut seen = HashSet::new();
                let fields = struct_value
                    .fields
                    .iter()
                    .map(|value| {
                        let field = variant_definition
                            .fields
                            .iter()
                            .find(|field| field.name == value.ident.name)?;
                        if !seen.insert(field.did) {
                            return None;
                        }
                        Some(StructField {
                            field: self.field_identity(field.did, adt_definition.did()),
                            value: self.expression(&value.expr)?,
                        })
                    })
                    .collect::<Option<Vec<_>>>()?;
                let rest = match &struct_value.rest {
                    rustc_ast::StructRest::None => None,
                    rustc_ast::StructRest::Base(value) => Some(Box::new(self.expression(value)?)),
                    rustc_ast::StructRest::Rest(_) => return None,
                };
                Some(Expression::Struct {
                    adt,
                    variant,
                    fields,
                    rest,
                })
            }
            _ => None,
        }
    }

    fn block(&mut self, block: &rustc_ast::Block) -> Option<Block> {
        Some(Block {
            statements: block
                .stmts
                .iter()
                .map(|statement| self.statement(statement))
                .collect::<Option<_>>()?,
        })
    }

    fn statement(&mut self, statement: &Stmt) -> Option<Statement> {
        match &statement.kind {
            StmtKind::Expr(value) => Some(Statement::Expression {
                expression: self.expression(value)?,
                semicolon: false,
            }),
            StmtKind::Semi(value) => Some(Statement::Expression {
                expression: self.expression(value)?,
                semicolon: true,
            }),
            StmtKind::Let(local) => {
                let pattern = self.pattern(&local.pat)?;
                let ty =
                    match &local.ty {
                        Some(value) => {
                            let hir = self.ast_to_hir.get_ty(value.id, self.tcx)?;
                            Some(self.type_tree(
                                self.tcx.typeck(hir.hir_id.owner).node_type(hir.hir_id),
                            )?)
                        }
                        None => None,
                    };
                let initializer = match &local.kind {
                    rustc_ast::LocalKind::Decl => None,
                    rustc_ast::LocalKind::Init(value) => Some(self.expression(value)?),
                    rustc_ast::LocalKind::InitElse(..) => return None,
                };
                Some(Statement::Let {
                    pattern,
                    ty,
                    initializer,
                })
            }
            _ => None,
        }
    }

    fn pattern(&mut self, pattern: &rustc_ast::Pat) -> Option<Pattern> {
        match &pattern.kind {
            PatKind::Wild => Some(Pattern::Wildcard),
            PatKind::Ident(mode, _, None) => {
                let hir = self.ast_to_hir.get_pat(pattern.id, self.tcx)?;
                let hir::PatKind::Binding(_, id, _, None) = hir.kind else { return None };
                Some(Pattern::Binding {
                    id: self.binding_id(id, self.source_side)?,
                    mutability: if mode.1.is_mut() {
                        BindingMutability::Mutable
                    } else {
                        BindingMutability::Immutable
                    },
                    by_ref: match mode.0 {
                        rustc_ast::ByRef::No => ByRefKind::No,
                        rustc_ast::ByRef::Yes(rustc_ast::Mutability::Not) => ByRefKind::Shared,
                        rustc_ast::ByRef::Yes(rustc_ast::Mutability::Mut) => ByRefKind::Mutable,
                    },
                })
            }
            _ => None,
        }
    }

    fn path_identity(&mut self, value: &Expr) -> Option<ValueIdentity> {
        let hir = self.ast_to_hir.get_expr(value.id, self.tcx)?;
        let hir::ExprKind::Path(path) = hir.kind else { return None };
        let res = self
            .tcx
            .typeck(hir.hir_id.owner)
            .qpath_res(&path, hir.hir_id);
        match res {
            Res::Local(id) => Some(ValueIdentity::Binding {
                id: self.binding_id(id, self.source_side)?,
            }),
            Res::Def(kind, id) => self.definition_identity(kind, id),
            _ => None,
        }
    }

    fn definition_identity(&mut self, kind: hir::def::DefKind, id: DefId) -> Option<ValueIdentity> {
        if let Some(logical) = self.callables.get(&id) {
            if !self.source_side && !self.function_ids.contains_key(logical) {
                return None;
            }
            let next = self.function_ids.len();
            let value = self
                .function_ids
                .entry(*logical)
                .or_insert_with(|| format!("<fn{next}>"))
                .clone();
            return Some(ValueIdentity::Function { id: value });
        }
        if self.tcx.is_foreign_item(id) {
            if !self.foreign_item_has_c_abi(id) {
                return None;
            }
            let symbol = self
                .tcx
                .codegen_fn_attrs(id)
                .link_name
                .unwrap_or_else(|| self.tcx.item_name(id))
                .to_string();
            return match kind {
                hir::def::DefKind::Fn => Some(ValueIdentity::ForeignFunction { symbol }),
                hir::def::DefKind::Static { .. } => Some(ValueIdentity::ForeignStatic { symbol }),
                _ => None,
            };
        }
        if !id.is_local() {
            let (crate_name, path) = external_identity(id, self.tcx);
            return Some(ValueIdentity::External { crate_name, path });
        }
        match kind {
            hir::def::DefKind::Fn => {
                if !self.source_side && !self.local_function_ids.contains_key(&id) {
                    return None;
                }
                let next = self.local_function_ids.len();
                let value = self
                    .local_function_ids
                    .entry(id)
                    .or_insert_with(|| format!("<fn{next}>"))
                    .clone();
                Some(ValueIdentity::Function { id: value })
            }
            hir::def::DefKind::AssocFn => self.method_identity(id),
            hir::def::DefKind::Static { .. } => {
                let next = self.static_ids.len();
                let value = self
                    .static_ids
                    .entry(id)
                    .or_insert_with(|| format!("<static{next}>"))
                    .clone();
                Some(ValueIdentity::Static { id: value })
            }
            hir::def::DefKind::Const | hir::def::DefKind::AssocConst => {
                let next = self.constant_ids.len();
                let value = self
                    .constant_ids
                    .entry(id)
                    .or_insert_with(|| format!("<const{next}>"))
                    .clone();
                Some(ValueIdentity::Constant { id: value })
            }
            hir::def::DefKind::Ctor(_, _) => {
                let parent = self.tcx.parent(id);
                if self.tcx.def_kind(parent) == hir::def::DefKind::Variant {
                    let owner = self.tcx.parent(parent);
                    Some(ValueIdentity::Constructor {
                        adt: self.adt_identity(owner),
                        variant: Some(self.variant_identity(parent, owner)),
                    })
                } else {
                    Some(ValueIdentity::Constructor {
                        adt: self.adt_identity(parent),
                        variant: None,
                    })
                }
            }
            _ => None,
        }
    }

    fn method_identity(&mut self, id: DefId) -> Option<ValueIdentity> {
        if !id.is_local() {
            let (crate_name, path) = external_identity(id, self.tcx);
            return Some(ValueIdentity::External { crate_name, path });
        }
        if self.tcx.associated_item(id).container == ty::AssocItemContainer::Trait {
            return None;
        }
        let next = self.method_ids.len();
        let value = self
            .method_ids
            .entry(id)
            .or_insert_with(|| format!("<method{next}>"))
            .clone();
        Some(ValueIdentity::Method { id: value })
    }

    fn foreign_item_has_c_abi(&self, id: DefId) -> bool {
        let Some(parent) = self.tcx.parent(id).as_local() else { return false };
        let hir::Node::Item(item) = self.tcx.hir_node_by_def_id(parent) else { return false };
        let hir::ItemKind::ForeignMod { abi, .. } = item.kind else { return false };
        matches!(abi, rustc_abi::ExternAbi::C { unwind: false })
    }

    fn literal(&mut self, expression: &Expr) -> Option<Literal> {
        self.literal_with_type(expression, None)
    }

    fn literal_with_type(
        &mut self,
        expression: &Expr,
        forced_type: Option<&str>,
    ) -> Option<Literal> {
        let hir = self.ast_to_hir.get_expr(expression.id, self.tcx)?;
        let hir::ExprKind::Lit(literal) = hir.kind else { return None };
        use rustc_ast::LitKind;
        match &literal.node {
            LitKind::Bool(value) => Some(Literal::Bool { value: *value }),
            LitKind::Char(value) => Some(Literal::Char {
                value: value.to_string(),
            }),
            LitKind::Byte(value) => Some(Literal::Byte { value: *value }),
            LitKind::Str(value, _) => Some(Literal::String {
                value: value.to_string(),
            }),
            LitKind::ByteStr(value, _) => Some(Literal::ByteString {
                value: value.to_vec(),
            }),
            LitKind::CStr(value, _) => Some(Literal::CString {
                value: value[..value.len().saturating_sub(1)].to_vec(),
            }),
            LitKind::Int(value, _) => Some(Literal::Integer {
                value: value.get().to_string(),
                ty: match forced_type {
                    Some(value) => value.to_owned(),
                    None => {
                        primitive_name(expression_type(expression, self.ast_to_hir, self.tcx)?)?
                    }
                },
            }),
            LitKind::Float(value, _) => {
                let ty = primitive_name(expression_type(expression, self.ast_to_hir, self.tcx)?)?;
                let bits = match ty.as_str() {
                    "f32" => format!("{:08x}", value.as_str().parse::<f32>().ok()?.to_bits()),
                    "f64" => format!("{:016x}", value.as_str().parse::<f64>().ok()?.to_bits()),
                    _ => return None,
                };
                Some(Literal::Float { bits, ty })
            }
            LitKind::Err(_) => None,
        }
    }
}

fn primitive_name(value: ty::Ty<'_>) -> Option<String> {
    match value.kind() {
        ty::TyKind::Int(value) => Some(value.name_str().into()),
        ty::TyKind::Uint(value) => Some(value.name_str().into()),
        ty::TyKind::Float(value) => Some(value.name_str().into()),
        _ => None,
    }
}

fn external_identity(id: DefId, tcx: TyCtxt<'_>) -> (String, Vec<String>) {
    let crate_name = tcx.crate_name(id.krate).to_string();
    let path = tcx
        .def_path(id)
        .data
        .into_iter()
        .filter_map(|component| component.data.get_opt_name())
        .map(|name| name.to_string())
        .collect();
    (crate_name, path)
}

fn binary_operator(value: rustc_ast::BinOpKind) -> Option<BinaryOperator> {
    use rustc_ast::BinOpKind;
    Some(match value {
        BinOpKind::Add => BinaryOperator::Add,
        BinOpKind::Sub => BinaryOperator::Subtract,
        BinOpKind::Mul => BinaryOperator::Multiply,
        BinOpKind::Div => BinaryOperator::Divide,
        BinOpKind::Rem => BinaryOperator::Remainder,
        BinOpKind::And => BinaryOperator::And,
        BinOpKind::Or => BinaryOperator::Or,
        BinOpKind::BitXor => BinaryOperator::BitXor,
        BinOpKind::BitAnd => BinaryOperator::BitAnd,
        BinOpKind::BitOr => BinaryOperator::BitOr,
        BinOpKind::Shl => BinaryOperator::ShiftLeft,
        BinOpKind::Shr => BinaryOperator::ShiftRight,
        BinOpKind::Eq => BinaryOperator::Equal,
        BinOpKind::Ne => BinaryOperator::NotEqual,
        BinOpKind::Lt => BinaryOperator::Less,
        BinOpKind::Le => BinaryOperator::LessEqual,
        BinOpKind::Gt => BinaryOperator::Greater,
        BinOpKind::Ge => BinaryOperator::GreaterEqual,
    })
}

fn statement_attributes(statement: &Stmt) -> &[Attribute] {
    match &statement.kind {
        StmtKind::Let(local) => &local.attrs,
        StmtKind::Item(item) => &item.attrs,
        StmtKind::Expr(expression) | StmtKind::Semi(expression) => {
            leading_expression_attributes(expression)
        }
        StmtKind::MacCall(mac) => &mac.attrs,
        StmtKind::Empty => &[],
    }
}

fn leading_expression_attributes(expression: &Expr) -> &[Attribute] {
    if !expression.attrs.is_empty() {
        return &expression.attrs;
    }
    match &expression.kind {
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
        | ExprKind::Use(left, _) => leading_expression_attributes(left),
        ExprKind::Call(callee, _) => leading_expression_attributes(callee),
        _ => &expression.attrs,
    }
}

fn is_proctor_attribute(attribute: &Attribute) -> bool {
    let AttrKind::Normal(normal) = &attribute.kind else { return false };
    normal.item.path.segments.len() == 1
        && normal.item.path.segments[0].ident.name.as_str() == "proctor"
}

fn numeric_proctor_label(attribute: &Attribute) -> Option<u32> {
    pprust::attribute_to_string(attribute)
        .strip_prefix("#[proctor(")?
        .strip_suffix(")]")?
        .parse()
        .ok()
}

struct ProctorAttributeRemover;

impl MutVisitor for ProctorAttributeRemover {
    fn visit_expr(&mut self, expression: &mut Expr) {
        expression
            .attrs
            .retain(|attribute| !is_proctor_attribute(attribute));
        mut_visit::walk_expr(self, expression);
    }

    fn flat_map_stmt(&mut self, mut statement: Stmt) -> SmallVec<[Stmt; 1]> {
        if !matches!(statement.kind, StmtKind::Empty) {
            match &mut statement.kind {
                StmtKind::Let(local) => local
                    .attrs
                    .retain(|attribute| !is_proctor_attribute(attribute)),
                StmtKind::Item(item) => item
                    .attrs
                    .retain(|attribute| !is_proctor_attribute(attribute)),
                StmtKind::Expr(expression) | StmtKind::Semi(expression) => expression
                    .attrs
                    .retain(|attribute| !is_proctor_attribute(attribute)),
                StmtKind::MacCall(mac) => mac
                    .attrs
                    .retain(|attribute| !is_proctor_attribute(attribute)),
                StmtKind::Empty => {}
            }
        }
        mut_visit::walk_flat_map_stmt(self, statement)
    }
}

fn statement_contains_macro(statement: &Stmt) -> bool {
    struct Finder(bool);
    impl<'ast> Visitor<'ast> for Finder {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if matches!(expression.kind, ExprKind::MacCall(..)) {
                self.0 = true;
                return;
            }
            visit::walk_expr(self, expression);
        }

        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if matches!(statement.kind, StmtKind::MacCall(..)) {
                self.0 = true;
                return;
            }
            visit::walk_stmt(self, statement);
        }
    }
    let mut finder = Finder(false);
    finder.visit_stmt(statement);
    finder.0
}

pub fn replacement_metadata_from_json(
    input: &str,
) -> Result<ReplacementObservationMetadata, ObservationError> {
    let value: ReplacementObservationMetadata =
        serde_json::from_str(input).map_err(|error| ObservationError {
            code: "malformed_metadata",
            message: format!(
                "replacement observation metadata is not valid schema-version-1 JSON: {error}"
            ),
        })?;
    if value.schema_version != OBSERVATION_SCHEMA_VERSION {
        return Err(ObservationError {
            code: "unsupported_schema_version",
            message: format!("unsupported schema_version {}", value.schema_version),
        });
    }
    for digest in [
        &value.candidate_sha256,
        &value.statement_pairs_sha256,
        &value.observation_source_sha256,
    ] {
        if digest.len() != 64
            || !digest
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(ObservationError {
                code: "malformed_metadata",
                message: "metadata digest is not 64 lowercase hexadecimal digits".to_owned(),
            });
        }
    }
    validate_replacement_metadata(&value)?;
    Ok(value)
}

fn metadata_error(message: impl Into<String>) -> ObservationError {
    ObservationError {
        code: "malformed_metadata",
        message: message.into(),
    }
}

fn canonical_metadata_path(path: &str) -> bool {
    !path.is_empty()
        && !path.starts_with("::")
        && !path.ends_with("::")
        && path.split("::").all(canonical_path_segment)
}

fn canonical_path_segment(segment: &str) -> bool {
    let (identifier, raw) = segment
        .strip_prefix("r#")
        .map_or((segment, false), |identifier| (identifier, true));
    if identifier == "_" {
        return false;
    }
    let mut chars = identifier.chars();
    let Some(first) = chars.next() else { return false };
    if !(first == '_' || unicode_ident::is_xid_start(first))
        || !chars.all(unicode_ident::is_xid_continue)
    {
        return false;
    }
    const KEYWORDS: &[&str] = &[
        "Self", "abstract", "as", "async", "await", "become", "box", "break", "const", "continue",
        "crate", "do", "dyn", "else", "enum", "extern", "false", "final", "fn", "for", "gen", "if",
        "impl", "in", "let", "loop", "macro", "match", "mod", "move", "mut", "override", "priv",
        "pub", "ref", "return", "self", "static", "struct", "super", "trait", "true", "try",
        "type", "typeof", "union", "unsafe", "unsized", "use", "virtual", "where", "while",
        "yield",
    ];
    if raw {
        !matches!(identifier, "Self" | "crate" | "self" | "super")
    } else {
        !KEYWORDS.contains(&identifier)
    }
}

fn validate_replacement_metadata(
    value: &ReplacementObservationMetadata,
) -> Result<(), ObservationError> {
    let accepted_and_new = value
        .accepted_correspondence
        .iter()
        .chain(&value.new_correspondence)
        .collect::<Vec<_>>();
    let mut item_ids = HashSet::new();
    let mut categories: HashMap<&str, Vec<(&str, u64)>> = HashMap::new();
    for record in &accepted_and_new {
        if !item_ids.insert(record.item_id) {
            return Err(metadata_error(format!(
                "metadata has duplicate correspondence item_id {}",
                record.item_id
            )));
        }
        for (category, path) in [
            ("logical_path", record.logical_path.as_str()),
            ("implementation_path", record.implementation_path.as_str()),
        ] {
            if !canonical_metadata_path(path) {
                return Err(metadata_error(format!(
                    "metadata {category} `{path}` is not a canonical crate-relative path"
                )));
            }
            categories
                .entry(category)
                .or_default()
                .push((path, record.item_id));
        }
        if let Some(wrapper) = &record.wrapper_path {
            if !canonical_metadata_path(wrapper) {
                return Err(metadata_error(format!(
                    "metadata wrapper_path `{wrapper}` is not a canonical crate-relative path"
                )));
            }
            categories
                .entry("wrapper_path")
                .or_default()
                .push((wrapper, record.item_id));
        }
    }
    let mut current_ids = HashSet::new();
    for current in &value.current_items {
        if !current_ids.insert(current.item_id) {
            return Err(metadata_error(format!(
                "metadata has duplicate current item_id {}",
                current.item_id
            )));
        }
        if !canonical_metadata_path(&current.source_copy_path) {
            return Err(metadata_error(format!(
                "metadata source_copy_path `{}` is not a canonical crate-relative path",
                current.source_copy_path
            )));
        }
        for pair in current.transform_labels.windows(2) {
            if pair[0] >= pair[1] {
                return Err(metadata_error(format!(
                    "metadata transform_labels for item {} are not strictly ordered",
                    current.item_id
                )));
            }
        }
        categories
            .entry("source_copy_path")
            .or_default()
            .push((&current.source_copy_path, current.item_id));
    }
    if value.new_correspondence.len() != value.current_items.len() {
        return Err(metadata_error(
            "metadata current_items and new_correspondence lengths differ",
        ));
    }
    for (index, (new, current)) in value
        .new_correspondence
        .iter()
        .zip(&value.current_items)
        .enumerate()
    {
        if new.item_id != current.item_id
            || new.logical_path != current.logical_path
            || new.implementation_path != current.implementation_path
            || new.wrapper_path != current.wrapper_path
        {
            return Err(metadata_error(format!(
                "metadata current_items[{index}] disagrees with new_correspondence[{index}]"
            )));
        }
    }
    let mut path_roles: HashMap<&str, (&str, u64)> = HashMap::new();
    for category in [
        "logical_path",
        "implementation_path",
        "wrapper_path",
        "source_copy_path",
    ] {
        let mut seen = HashSet::new();
        for &(path, item_id) in categories.get(category).into_iter().flatten() {
            if !seen.insert(path) {
                return Err(metadata_error(format!(
                    "metadata has duplicate {category} `{path}`"
                )));
            }
            if let Some(&(previous_category, previous_item)) = path_roles.get(path)
                && !(previous_category == "logical_path"
                    && category == "implementation_path"
                    && previous_item == item_id)
            {
                return Err(metadata_error(format!(
                    "metadata path `{path}` is used as both {previous_category} and {category}"
                )));
            }
            path_roles.entry(path).or_insert((category, item_id));
        }
    }
    Ok(())
}

pub fn sha256_hex(input: &[u8]) -> String {
    const INITIAL: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let bit_len = (input.len() as u64).wrapping_mul(8);
    let mut data = input.to_vec();
    data.push(0x80);
    while data.len() % 64 != 56 {
        data.push(0);
    }
    data.extend_from_slice(&bit_len.to_be_bytes());
    let mut state = INITIAL;
    for chunk in data.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, bytes) in chunk.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes(bytes.try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (slot, value) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *slot = slot.wrapping_add(value);
        }
    }
    state.iter().map(|word| format!("{word:08x}")).collect()
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn extract(source: &str) -> Result<ObservationDocument, ObservationError> {
        extract_labels(source, vec![0])
    }

    fn exact_optional_pointer_observations() -> serde_json::Value {
        let primitive = json!({ "kind": "primitive", "name": "i32" });
        let binding = json!({ "kind": "path", "value": { "kind": "binding", "id": "<id0>" } });
        let source_binding_type = json!({
            "kind": "raw_pointer",
            "mutability": "const",
            "pointee": primitive.clone()
        });
        let target_binding_type = json!({
            "kind": "adt",
            "adt_kind": "enum",
            "identity": {
                "kind": "external",
                "crate": "core",
                "path": ["option", "Option"]
            },
            "arguments": [{
                "kind": "reference",
                "mutability": "shared",
                "pointee": primitive.clone()
            }]
        });
        let anchor = json!({
            "id": "<id0>",
            "source_type": source_binding_type,
            "target_type": target_binding_type
        });
        let bool_type = json!({ "kind": "primitive", "name": "bool" });
        json!([
            {
                "source_expression": {
                    "kind": "method_call",
                    "receiver": binding.clone(),
                    "method": {
                        "kind": "external",
                        "crate": "core",
                        "path": ["ptr", "const_ptr", "is_null"]
                    },
                    "arguments": []
                },
                "target_expression": {
                    "kind": "method_call",
                    "receiver": binding.clone(),
                    "method": {
                        "kind": "external",
                        "crate": "core",
                        "path": ["option", "is_none"]
                    },
                    "arguments": []
                },
                "pointer_anchors": [anchor.clone()],
                "source_type": bool_type.clone(),
                "source_adjusted_type": bool_type.clone(),
                "target_type": bool_type.clone(),
                "target_adjusted_type": bool_type
            },
            {
                "source_expression": {
                    "kind": "unary",
                    "operator": "deref",
                    "operand": binding.clone()
                },
                "target_expression": {
                    "kind": "unary",
                    "operator": "deref",
                    "operand": {
                        "kind": "method_call",
                        "receiver": binding,
                        "method": {
                            "kind": "external",
                            "crate": "core",
                            "path": ["option", "unwrap"]
                        },
                        "arguments": []
                    }
                },
                "pointer_anchors": [anchor],
                "source_type": primitive.clone(),
                "source_adjusted_type": primitive.clone(),
                "target_type": primitive.clone(),
                "target_adjusted_type": primitive
            }
        ])
    }

    fn extract_labels(
        source: &str,
        transform_labels: Vec<u32>,
    ) -> Result<ObservationDocument, ObservationError> {
        extract_case(source, "__proctor_source_read", "read", transform_labels)
    }

    fn extract_case(
        source: &str,
        source_copy_path: &str,
        implementation_path: &str,
        transform_labels: Vec<u32>,
    ) -> Result<ObservationDocument, ObservationError> {
        let metadata = ReplacementObservationMetadata {
            schema_version: 1,
            candidate_sha256: sha256_hex(b""),
            statement_pairs_sha256: sha256_hex(b""),
            observation_source_sha256: sha256_hex(source.as_bytes()),
            accepted_correspondence: vec![],
            new_correspondence: vec![CallableCorrespondence {
                item_id: 7,
                logical_path: implementation_path.to_owned(),
                implementation_path: implementation_path.to_owned(),
                wrapper_path: None,
            }],
            current_items: vec![CurrentObservationItem {
                item_id: 7,
                logical_path: implementation_path.to_owned(),
                source_copy_path: source_copy_path.to_owned(),
                implementation_path: implementation_path.to_owned(),
                wrapper_path: None,
                transform_labels,
            }],
        };
        extract_metadata(source, metadata)
    }

    fn extract_metadata(
        source: &str,
        mut metadata: ReplacementObservationMetadata,
    ) -> Result<ObservationDocument, ObservationError> {
        metadata.observation_source_sha256 = sha256_hex(source.as_bytes());
        extract_observations_from_source(source, &metadata)
    }

    fn dump_statement_expressions(source: &str, function: &str) -> Vec<Expression> {
        let source = source.to_owned();
        utils::compilation::run_compiler_on_str(&source.clone(), move |tcx| {
            let mut surface = utils::ast::parse_crate(source);
            let mut mapper = utils::ir::AstToHirMapper::new(tcx);
            mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
            let ast_to_hir = mapper.ast_to_hir;
            let mut functions = HashMap::new();
            collect_functions(&surface.items, &mut vec![], &mut functions);
            let item = functions[function];
            let bindings = HashMap::new();
            let callables = HashMap::new();
            let mut context = DumpContext::new(&bindings, &callables, &ast_to_hir, tcx);
            plain_statements(item)
                .iter()
                .filter_map(|statement| statement_expression(statement))
                .filter_map(|expression| context.expression(expression))
                .collect()
        })
        .unwrap()
    }

    fn dump_parameter_types(source: &str, function: &str) -> Vec<TypeTree> {
        let source = source.to_owned();
        utils::compilation::run_compiler_on_str(&source.clone(), move |tcx| {
            let mut surface = utils::ast::parse_crate(source);
            let mut mapper = utils::ir::AstToHirMapper::new(tcx);
            mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
            let ast_to_hir = mapper.ast_to_hir;
            let mut functions = HashMap::new();
            collect_functions(&surface.items, &mut vec![], &mut functions);
            let ItemKind::Fn(box value) = &functions[function].kind else { unreachable!() };
            let bindings = HashMap::new();
            let callables = HashMap::new();
            let mut context = DumpContext::new(&bindings, &callables, &ast_to_hir, tcx);
            value
                .sig
                .decl
                .inputs
                .iter()
                .map(|parameter| {
                    let (_, binding) = simple_binding(&parameter.pat, &ast_to_hir, tcx).unwrap();
                    context
                        .type_tree(binding_type(binding, tcx).unwrap())
                        .unwrap()
                })
                .collect()
        })
        .unwrap()
    }

    fn dump_function_block(source: &str, function: &str) -> Block {
        let source = source.to_owned();
        utils::compilation::run_compiler_on_str(&source.clone(), move |tcx| {
            let mut surface = utils::ast::parse_crate(source);
            let mut mapper = utils::ir::AstToHirMapper::new(tcx);
            mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
            let ast_to_hir = mapper.ast_to_hir;
            let mut functions = HashMap::new();
            collect_functions(&surface.items, &mut vec![], &mut functions);
            let ItemKind::Fn(box value) = &functions[function].kind else { unreachable!() };
            let bindings = HashMap::new();
            let callables = HashMap::new();
            let mut context = DumpContext::new(&bindings, &callables, &ast_to_hir, tcx);
            context.block(value.body.as_ref().unwrap()).unwrap()
        })
        .unwrap()
    }

    #[test]
    fn sha256_matches_standard_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn metadata_paths_use_canonical_rust_identifier_segments() {
        let mut metadata = ReplacementObservationMetadata {
            schema_version: 1,
            candidate_sha256: sha256_hex(b""),
            statement_pairs_sha256: sha256_hex(b""),
            observation_source_sha256: sha256_hex(b""),
            accepted_correspondence: vec![],
            new_correspondence: vec![CallableCorrespondence {
                item_id: 1,
                logical_path: "módulo::r#type".into(),
                implementation_path: "módulo::r#type".into(),
                wrapper_path: None,
            }],
            current_items: vec![CurrentObservationItem {
                item_id: 1,
                logical_path: "módulo::r#type".into(),
                source_copy_path: "módulo::__copy".into(),
                implementation_path: "módulo::r#type".into(),
                wrapper_path: None,
                transform_labels: vec![0],
            }],
        };
        validate_replacement_metadata(&metadata).unwrap();
        for invalid in [
            "fn", "_", "r#_", "r#self", "crate::f", "::f", "f::", "a::::b",
        ] {
            metadata.new_correspondence[0].logical_path = invalid.into();
            metadata.current_items[0].logical_path = invalid.into();
            assert_eq!(
                validate_replacement_metadata(&metadata).unwrap_err().code,
                "malformed_metadata"
            );
        }
    }

    #[test]
    fn metadata_cross_record_invariants_reject() {
        fn correspondence(item_id: u64, path: &str) -> CallableCorrespondence {
            CallableCorrespondence {
                item_id,
                logical_path: path.into(),
                implementation_path: path.into(),
                wrapper_path: Some(format!("wrapper_{path}")),
            }
        }
        fn current(item_id: u64, path: &str) -> CurrentObservationItem {
            CurrentObservationItem {
                item_id,
                logical_path: path.into(),
                source_copy_path: format!("source_{path}"),
                implementation_path: path.into(),
                wrapper_path: Some(format!("wrapper_{path}")),
                transform_labels: vec![0],
            }
        }
        let base = ReplacementObservationMetadata {
            schema_version: 1,
            candidate_sha256: sha256_hex(b""),
            statement_pairs_sha256: sha256_hex(b""),
            observation_source_sha256: sha256_hex(b""),
            accepted_correspondence: vec![correspondence(0, "accepted")],
            new_correspondence: vec![correspondence(1, "first"), correspondence(2, "second")],
            current_items: vec![current(1, "first"), current(2, "second")],
        };
        validate_replacement_metadata(&base).unwrap();

        let mut malformed = base.clone();
        malformed.new_correspondence[0].item_id = 0;
        assert!(
            validate_replacement_metadata(&malformed)
                .unwrap_err()
                .message
                .contains("duplicate correspondence item_id")
        );

        let mut malformed = base.clone();
        malformed.current_items[1].item_id = 1;
        assert!(
            validate_replacement_metadata(&malformed)
                .unwrap_err()
                .message
                .contains("duplicate current item_id")
        );

        for category in ["logical", "implementation", "wrapper", "source"] {
            let mut malformed = base.clone();
            match category {
                "logical" => {
                    malformed.new_correspondence[1].logical_path = "first".into();
                    malformed.current_items[1].logical_path = "first".into();
                }
                "implementation" => {
                    malformed.new_correspondence[1].implementation_path = "first".into();
                    malformed.current_items[1].implementation_path = "first".into();
                }
                "wrapper" => {
                    malformed.new_correspondence[1].wrapper_path = Some("wrapper_first".into());
                    malformed.current_items[1].wrapper_path = Some("wrapper_first".into());
                }
                "source" => malformed.current_items[1].source_copy_path = "source_first".into(),
                _ => unreachable!(),
            }
            assert!(
                validate_replacement_metadata(&malformed)
                    .unwrap_err()
                    .message
                    .contains("duplicate")
            );
        }

        let mut malformed = base.clone();
        malformed.current_items[0].logical_path = "different".into();
        assert!(
            validate_replacement_metadata(&malformed)
                .unwrap_err()
                .message
                .contains("disagrees")
        );

        let mut malformed = base.clone();
        malformed.current_items[0].transform_labels = vec![1, 1];
        assert!(
            validate_replacement_metadata(&malformed)
                .unwrap_err()
                .message
                .contains("not strictly ordered")
        );

        let mut malformed = base;
        malformed.current_items[1].source_copy_path = "first".into();
        assert!(
            validate_replacement_metadata(&malformed)
                .unwrap_err()
                .message
                .contains("used as both logical_path and source_copy_path")
        );
    }

    #[test]
    fn labels_are_recorded_removed_and_recovered_on_unexpanded_ast() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)]
    if pointer.is_null() {
        #[proctor(1)]
        0
    } else {
        #[proctor(2)]
        *pointer
    }
}
unsafe fn target(mut pointer: Option<&i32>) -> i32 {
    #[proctor(0)]
    if pointer.is_none() {
        #[proctor(1)]
        0
    } else {
        #[proctor(2)]
        *pointer.unwrap()
    }
}
"#;
        let metadata = ReplacementObservationMetadata {
            schema_version: 1,
            candidate_sha256: sha256_hex(b""),
            statement_pairs_sha256: sha256_hex(b""),
            observation_source_sha256: sha256_hex(source.as_bytes()),
            accepted_correspondence: vec![],
            new_correspondence: vec![CallableCorrespondence {
                item_id: 7,
                logical_path: "target".into(),
                implementation_path: "target".into(),
                wrapper_path: None,
            }],
            current_items: vec![CurrentObservationItem {
                item_id: 7,
                logical_path: "target".into(),
                source_copy_path: "source_copy".into(),
                implementation_path: "target".into(),
                wrapper_path: None,
                transform_labels: vec![0, 1, 2],
            }],
        };
        let prepared = rustc_span::create_session_if_not_set_then(
            rustc_span::edition::Edition::Edition2021,
            |_| prepare_observation_source(source, &metadata),
        )
        .unwrap();
        assert_eq!(prepared.functions[0].labels.len(), 3);
        assert_eq!(
            prepared.functions[0]
                .labels
                .iter()
                .map(|label| label.label)
                .collect::<Vec<_>>(),
            vec![0, 1, 2]
        );
        assert!(!prepared.compiler_source.contains("proctor"));
        let document = extract_metadata(source, metadata).unwrap();
        assert_eq!(
            serde_json::to_value(&document.observations).unwrap(),
            exact_optional_pointer_observations()
        );
    }

    #[test]
    fn macro_anywhere_in_selected_statement_skips_before_expansion() {
        let source = r#"
macro_rules! one { () => { 1_i32 }; }
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)]
    if true {
        #[proctor(1)] *pointer
    } else {
        #[proctor(2)] one!()
    }
}
unsafe fn target(mut pointer: &i32) -> i32 {
    #[proctor(0)]
    if true {
        #[proctor(1)] *pointer
    } else {
        #[proctor(2)] one!()
    }
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0, 1, 2]).unwrap();
        assert_eq!(document.observations.len(), 1, "{document:?}");
        assert_eq!(document.observations[0].pointer_anchors[0].id, "<id0>");
    }

    #[test]
    fn parameters_pair_by_index_and_symbol() {
        let valid = r#"
unsafe fn source_copy(mut left: *const i32, mut right: *const i32) -> i32 {
    #[proctor(0)] *left + *right
}
unsafe fn target(mut left: &i32, mut right: &i32) -> i32 {
    #[proctor(0)] *left + *right
}
"#;
        let document = extract_case(valid, "source_copy", "target", vec![0]).unwrap();
        assert_eq!(document.observations.len(), 2);
        for observation in &document.observations {
            assert_eq!(observation.pointer_anchors.len(), 1);
            assert_eq!(observation.pointer_anchors[0].id, "<id0>");
            assert_eq!(
                observation.source_type,
                TypeTree::Primitive { name: "i32".into() }
            );
            assert_eq!(observation.source_adjusted_type, observation.source_type);
            assert_eq!(observation.target_type, observation.source_type);
            assert_eq!(observation.target_adjusted_type, observation.source_type);
        }
        assert_eq!(document.observations[0], document.observations[1]);
        let invalid = valid.replace(
            "mut left: &i32, mut right: &i32",
            "mut right: &i32, mut left: &i32",
        );
        assert_eq!(
            extract_case(&invalid, "source_copy", "target", vec![0])
                .unwrap_err()
                .code,
            "binding_correspondence"
        );
    }

    #[test]
    fn simple_locals_pair_by_declaration_label_and_symbol() {
        let source = r#"
unsafe fn source_copy(mut pointer: *mut i32) -> i32 {
    #[proctor(0)] let mut alias: *mut i32 = pointer;
    #[proctor(1)] *alias
}
unsafe fn target(mut pointer: &mut i32) -> i32 {
    #[proctor(0)] let mut alias: &mut i32 = pointer;
    #[proctor(1)] *alias
}
"#;
        assert_eq!(
            extract_case(source, "source_copy", "target", vec![0, 1])
                .unwrap()
                .observations
                .len(),
            2
        );
        for invalid in [
            source.replace(
                "#[proctor(0)] let mut alias: &mut",
                "#[proctor(2)] let mut alias: &mut",
            ),
            source.replace(
                "let mut alias: &mut i32 = pointer;\n    #[proctor(1)] *alias",
                "let mut other: &mut i32 = pointer;\n    #[proctor(1)] *other",
            ),
        ] {
            assert_eq!(
                extract_case(&invalid, "source_copy", "target", vec![0, 1])
                    .unwrap_err()
                    .code,
                "binding_correspondence"
            );
        }
        let missing_target_annotation = source.replace(
            "let mut alias: &mut i32 = pointer",
            "let mut alias = pointer",
        );
        assert_eq!(
            extract_case(
                &missing_target_annotation,
                "source_copy",
                "target",
                vec![0, 1],
            )
            .unwrap_err()
            .code,
            "binding_correspondence"
        );
        for disagreement in [
            source.replace(
                "let mut alias: *mut i32 = pointer",
                "let mut alias: u32 = pointer",
            ),
            source.replace(
                "let mut alias: &mut i32 = pointer",
                "let mut alias: u32 = pointer",
            ),
        ] {
            assert!(extract_case(&disagreement, "source_copy", "target", vec![0, 1]).is_err());
        }
    }

    #[test]
    fn uninitialized_type_changing_local_declaration_is_skipped() {
        let source = r#"
unsafe fn source_copy(pointer: *mut f32) -> *mut f32 {
    #[proctor(0)] let mut k: *mut f32;
    #[proctor(1)] pointer
}
unsafe fn target(pointer: &mut [f32]) -> &mut [f32] {
    #[proctor(0)] let mut k: &mut [f32];
    #[proctor(1)] pointer
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0, 1]).unwrap();
        assert_eq!(document.observations.len(), 1, "{document:?}");
        assert!(matches!(
            document.observations[0].source_expression,
            Expression::Path { .. }
        ));
        assert!(matches!(
            document.observations[0].target_expression,
            Expression::Path { .. }
        ));
    }

    #[test]
    fn shadowed_locals_remain_distinct() {
        let source = r#"
unsafe fn read(pointer: &mut i32) -> i32 {
    #[proctor(0)] let mut alias: &mut i32 = pointer;
    #[proctor(1)] {
        #[proctor(2)] let mut alias: &mut i32 = alias;
        #[proctor(3)] *alias += 1;
    }
    #[proctor(4)] *alias
}
unsafe fn __proctor_source_read(pointer: *mut i32) -> i32 {
    #[proctor(0)] let mut alias: *mut i32 = pointer;
    #[proctor(1)] {
        #[proctor(2)] let mut alias: *mut i32 = pointer;
        #[proctor(3)] *alias += 1;
    }
    #[proctor(4)] *alias
}
"#;
        let document = extract_labels(source, vec![0, 2, 3, 4]).unwrap();
        assert_eq!(document.observations.len(), 3);
        let raw = TypeTree::RawPointer {
            mutability: RawMutability::Mut,
            pointee: Box::new(TypeTree::Primitive { name: "i32".into() }),
        };
        let reference = TypeTree::Reference {
            mutability: RefMutability::Mutable,
            pointee: Box::new(TypeTree::Primitive { name: "i32".into() }),
        };
        for observation in &document.observations {
            assert_eq!(observation.pointer_anchors.len(), 1);
            assert_eq!(observation.pointer_anchors[0].id, "<id0>");
            assert_eq!(observation.pointer_anchors[0].source_type, raw);
            assert_eq!(observation.pointer_anchors[0].target_type, reference);
        }
        assert_eq!(document.observations[1], document.observations[2]);
        assert!(matches!(
            document.observations[0].source_expression,
            Expression::Path { .. }
        ));
        assert!(matches!(
            document.observations[0].target_expression,
            Expression::Path { .. }
        ));
        assert!(matches!(
            document.observations[1].source_expression,
            Expression::Unary {
                operator: UnaryOperator::Deref,
                ..
            }
        ));
        assert!(
            extract_labels(source, vec![2])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn source_only_reference_is_allowed() {
        let source = r#"
unsafe fn read(pointer: &[i32], extra: usize, index: usize) -> i32 {
    #[proctor(0)] pointer[index]
}
unsafe fn __proctor_source_read(pointer: *const i32, extra: usize, index: usize) -> i32 {
    #[proctor(0)] *pointer.add(extra + index)
}
"#;
        let document = extract(source).unwrap();
        assert_eq!(document.observations.len(), 1);
        assert_eq!(
            document.observations[0].pointer_anchors[0].target_type,
            TypeTree::Reference {
                mutability: RefMutability::Shared,
                pointee: Box::new(TypeTree::Slice {
                    element: Box::new(TypeTree::Primitive { name: "i32".into() })
                })
            }
        );
    }

    #[test]
    fn target_only_user_function_discards_observation() {
        let source = r#"
unsafe fn helper(value: i32) -> i32 { value }
unsafe fn read(pointer: &i32) -> i32 { #[proctor(0)] helper(*pointer) }
unsafe fn __proctor_source_read(pointer: *const i32) -> i32 { #[proctor(0)] *pointer }
"#;
        assert!(extract(source).unwrap().observations.is_empty());
    }

    #[test]
    fn unpaired_raw_pointer_local_is_not_an_anchor() {
        let source = r#"
unsafe fn source_copy(pointer: *const i32) -> i32 {
    let extra = pointer;
    #[proctor(0)] *extra
}
unsafe fn target(pointer: &i32) -> i32 {
    #[proctor(0)] *pointer
}
"#;
        assert!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn wildcard_local_annotations_must_match() {
        let source = r#"
unsafe fn source_copy(pointer: *const i32) {
    #[proctor(0)] let _: i32 = *pointer as i32;
}
unsafe fn target(pointer: &i32) {
    #[proctor(0)] let _: u32 = *pointer as u32;
}
"#;
        assert!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn inferred_raw_local_pairs_with_materialized_target_type() {
        let source = r#"
unsafe fn read(pointer: &mut i32) -> i32 {
    #[proctor(0)] let mut alias: &mut i32 = pointer;
    #[proctor(1)] *alias
}
unsafe fn __proctor_source_read(pointer: *mut i32) -> i32 {
    #[proctor(0)] let mut alias = pointer;
    #[proctor(1)] *alias
}
"#;
        assert_eq!(
            extract_labels(source, vec![0, 1])
                .unwrap()
                .observations
                .len(),
            2
        );
    }

    #[test]
    fn preserved_labels_never_emit() {
        let source = r#"
unsafe fn read(pointer: &i32) -> i32 {
    #[proctor(0)] let value: i32 = 1;
    #[proctor(1)] value + *pointer
}
unsafe fn __proctor_source_read(pointer: *const i32) -> i32 {
    #[proctor(0)] let value = 1;
    #[proctor(1)] value + *pointer
}
"#;
        assert_eq!(
            extract_labels(source, vec![1]).unwrap().observations.len(),
            1
        );
    }

    #[test]
    fn multi_statement_target_group_skips() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)] *pointer
}
unsafe fn target(mut pointer: &i32) -> i32 {
    #[proctor(0)] let proctor_temp_var_0 = *pointer;
    #[proctor(0)] proctor_temp_var_0
}
"#;
        assert!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn outer_control_keeps_conditions_and_opaque_nested_labels() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)]
    if pointer.is_null() {
        #[proctor(1)] 0
    } else {
        #[proctor(2)] *pointer
    }
}
unsafe fn target(mut pointer: Option<&i32>) -> i32 {
    #[proctor(0)]
    if pointer.is_none() {
        #[proctor(1)] 0
    } else {
        #[proctor(2)] *pointer.unwrap()
    }
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0, 1, 2]).unwrap();
        assert_eq!(
            serde_json::to_value(&document.observations).unwrap(),
            exact_optional_pointer_observations()
        );
    }

    #[test]
    fn parenthesized_nested_assignment_stays_opaque_to_outer_control() {
        let source = r#"
struct Pair { first: i32, second: i32 }
unsafe fn source_copy(mut condition: *const Pair, mut output: *mut Pair) {
    #[proctor(0)]
    if (*condition).first < (*condition).second {
        #[proctor(1)] ((*output).first = 0);
    }
}
unsafe fn target(mut condition: &Pair, mut output: &mut Pair) {
    #[proctor(0)]
    if condition.first < condition.second {
        #[proctor(1)] output.first = 0;
    }
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0, 1]).unwrap();
        assert_eq!(document.observations.len(), 3);
        for observation in &document.observations[..2] {
            assert!(matches!(
                observation.pointer_anchors[0].target_type,
                TypeTree::Reference {
                    mutability: RefMutability::Shared,
                    ..
                }
            ));
        }
        assert!(matches!(
            document.observations[2].pointer_anchors[0].target_type,
            TypeTree::Reference {
                mutability: RefMutability::Mutable,
                ..
            }
        ));
    }

    #[test]
    fn match_arms_use_canonical_labeled_blocks() {
        let source = r#"
unsafe fn read(pointer: &[i32]) -> i32 {
    #[proctor(0)]
    match pointer[0] {
        0 => { #[proctor(1)] pointer[1] }
        _ => { #[proctor(2)] 2 }
    }
}
unsafe fn __proctor_source_read(pointer: *const i32) -> i32 {
    #[proctor(0)]
    match *pointer {
        0 => { #[proctor(1)] *pointer.add(1) }
        _ => { #[proctor(2)] 2 }
    }
}
"#;
        assert_eq!(
            extract_labels(source, vec![0, 1])
                .unwrap()
                .observations
                .len(),
            2
        );
    }

    #[test]
    fn outer_control_keeps_disjoint_condition_regions() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32, mut other: *const i32) -> i32 {
    #[proctor(0)]
    if pointer.is_null() || other.is_null() {
        #[proctor(1)] 0
    } else {
        #[proctor(2)] *pointer
    }
}
unsafe fn target(mut pointer: Option<&i32>, mut other: Option<&i32>) -> i32 {
    #[proctor(0)]
    if pointer.is_none() || other.is_none() {
        #[proctor(1)] 0
    } else {
        #[proctor(2)] *pointer.unwrap()
    }
}
"#;
        assert_eq!(
            extract_case(source, "source_copy", "target", vec![0, 2])
                .unwrap()
                .observations
                .len(),
            3
        );
    }

    #[test]
    fn builtin_binary_produces_two_disjoint_regions() {
        let source = r#"
unsafe fn source_copy(mut left: *const i32, mut right: *const i32) -> i32 {
    #[proctor(0)] *left + *right
}
unsafe fn target(mut left: &i32, mut right: &i32) -> i32 {
    #[proctor(0)] *left + *right
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0]).unwrap();
        assert_eq!(document.observations.len(), 2);
        assert_eq!(document.observations[0].pointer_anchors[0].id, "<id0>");
        assert_eq!(document.observations[1].pointer_anchors[0].id, "<id0>");
    }

    #[test]
    fn repeated_binding_occurrences_remain_distinct() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)] *pointer + *pointer
}
unsafe fn target(mut pointer: &i32) -> i32 {
    #[proctor(0)] *pointer + *pointer
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0]).unwrap();
        assert_eq!(document.observations.len(), 2);
        assert_eq!(document.observations[0], document.observations[1]);
    }

    #[test]
    fn call_method_and_path_variants_are_exact() {
        let source = r#"
unsafe extern "C" {
    #[link_name = "linked_read"]
    fn foreign_read(pointer: *const i32) -> i32;
    static FOREIGN_VALUE: i32;
}
unsafe fn values(pointer: *const i32) -> i32 {
    foreign_read(pointer);
    FOREIGN_VALUE
}
"#;
        let values = dump_statement_expressions(source, "values");
        let Expression::Call { callee, .. } = &values[0] else { panic!() };
        assert_eq!(
            **callee,
            Expression::Path {
                value: ValueIdentity::ForeignFunction {
                    symbol: "linked_read".to_owned()
                }
            }
        );
        assert_eq!(
            values[1],
            Expression::Path {
                value: ValueIdentity::ForeignStatic {
                    symbol: "FOREIGN_VALUE".to_owned()
                }
            }
        );
    }

    #[test]
    fn array_tuple_repeat_and_block_variants_are_exact() {
        let values = dump_statement_expressions(
            "fn values() { let _ = ([1_i32], (2_i32,), [3_i32; 2], { 4_i32 }); }",
            "values",
        );
        let Expression::Tuple { elements } = &values[0] else { panic!() };
        assert_eq!(
            serde_json::to_value(elements).unwrap(),
            json!([
                {"kind":"array","elements":[{"kind":"literal","value":{"kind":"integer","value":"1","type":"i32"}}]},
                {"kind":"tuple","elements":[{"kind":"literal","value":{"kind":"integer","value":"2","type":"i32"}}]},
                {"kind":"repeat","value":{"kind":"literal","value":{"kind":"integer","value":"3","type":"i32"}},"count":{"kind":"literal","value":{"kind":"integer","value":"2","type":"usize"}}},
                {"kind":"block","block":{"statements":[{"kind":"expression","expression":{"kind":"literal","value":{"kind":"integer","value":"4","type":"i32"}},"semicolon":false}]}}
            ])
        );
    }

    #[test]
    fn binary_unary_cast_and_operator_enums_are_exact() {
        let values = dump_statement_expressions(
            "fn ops(mut value: i32) -> i64 { (!(value == 0) as i32 + -value) as i64 }",
            "ops",
        );
        assert_eq!(
            serde_json::to_value(&values[0]).unwrap(),
            json!({
                "kind":"cast",
                "expression":{"kind":"binary","operator":"add",
                    "left":{"kind":"cast","expression":{"kind":"unary","operator":"not","operand":{"kind":"binary","operator":"equal","left":{"kind":"path","value":{"kind":"binding","id":"<id0>"}},"right":{"kind":"literal","value":{"kind":"integer","value":"0","type":"i32"}}}},"type":{"kind":"primitive","name":"i32"}},
                    "right":{"kind":"unary","operator":"negate","operand":{"kind":"path","value":{"kind":"binding","id":"<id0>"}}}},
                "type":{"kind":"primitive","name":"i64"}
            })
        );

        let all = dump_statement_expressions(
            r#"fn all_ops(mut a: i32, mut b: i32, mut x: bool, mut y: bool) {
                let _ = (a-b,a*b,a/b,a%b,x&&y,x||y,a^b,a&b,a|b,a<<b,a>>b);
                let _ = (a!=b,a<b,a<=b,a>b,a>=b);
            }"#,
            "all_ops",
        );
        let operators = all
            .iter()
            .flat_map(|value| match value {
                Expression::Tuple { elements } => elements,
                _ => panic!(),
            })
            .map(|value| match value {
                Expression::Binary { operator, .. } => serde_json::to_value(operator)
                    .unwrap()
                    .as_str()
                    .unwrap()
                    .to_owned(),
                _ => panic!(),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            operators,
            [
                "subtract",
                "multiply",
                "divide",
                "remainder",
                "and",
                "or",
                "bit_xor",
                "bit_and",
                "bit_or",
                "shift_left",
                "shift_right",
                "not_equal",
                "less",
                "less_equal",
                "greater",
                "greater_equal"
            ]
        );
    }

    #[test]
    fn unlabeled_if_while_loop_break_continue_are_exact() {
        let values = dump_statement_expressions(
            r#"fn controls(mut flag: bool) {
                loop { while flag { if flag { break; } else { continue; } } break; }
                let _value = loop { break 1_i32; };
            }"#,
            "controls",
        );
        let encoded = serde_json::to_value(&values).unwrap();
        assert_eq!(encoded[0]["kind"], "loop");
        assert_eq!(
            encoded[0]["body"]["statements"][0]["expression"]["kind"],
            "while"
        );
        assert_eq!(
            encoded[0]["body"]["statements"][0]["expression"]["body"]["statements"][0]["expression"]
                ["kind"],
            "if"
        );
        assert_eq!(
            encoded[0]["body"]["statements"][1]["expression"],
            json!({"kind":"break","value":null})
        );
        let value_loop = encoded
            .as_array()
            .unwrap()
            .iter()
            .filter(|value| value["kind"] == "loop")
            .nth(1)
            .unwrap();
        assert_eq!(
            value_loop,
            &json!({"kind":"loop","body":{"statements":[{"kind":"expression","expression":{"kind":"break","value":{"kind":"literal","value":{"kind":"integer","value":"1","type":"i32"}}},"semicolon":true}]}})
        );

        let rejected = dump_statement_expressions(
            "fn labeled() { 'outer: loop { break 'outer; } }",
            "labeled",
        );
        assert!(rejected.is_empty());
    }

    #[test]
    fn literal_variants_are_semantic_and_exact() {
        let values = dump_statement_expressions(
            r#"fn literals() { let _ = (true, 'x', b'x', "x", b"xy", c"xy", 12_u16, 1.5_f32); }"#,
            "literals",
        );
        assert_eq!(
            serde_json::to_value(&values[0]).unwrap(),
            json!({"kind":"tuple","elements":[
                {"kind":"literal","value":{"kind":"bool","value":true}},
                {"kind":"literal","value":{"kind":"char","value":"x"}},
                {"kind":"literal","value":{"kind":"byte","value":120}},
                {"kind":"literal","value":{"kind":"string","value":"x"}},
                {"kind":"literal","value":{"kind":"byte_string","value":[120,121]}},
                {"kind":"literal","value":{"kind":"c_string","value":[120,121]}},
                {"kind":"literal","value":{"kind":"integer","value":"12","type":"u16"}},
                {"kind":"literal","value":{"kind":"float","bits":"3fc00000","type":"f32"}}
            ]})
        );
        let alternate = dump_statement_expressions(
            r##"fn alternate() { let _ = (r#"x"#, 0x0c_u16, 1.50_f32, -12_i32); }"##,
            "alternate",
        );
        assert_eq!(
            serde_json::to_value(&alternate[0]).unwrap(),
            json!({"kind":"tuple","elements":[
                {"kind":"literal","value":{"kind":"string","value":"x"}},
                {"kind":"literal","value":{"kind":"integer","value":"12","type":"u16"}},
                {"kind":"literal","value":{"kind":"float","bits":"3fc00000","type":"f32"}},
                {"kind":"unary","operator":"negate","operand":{"kind":"literal","value":{"kind":"integer","value":"12","type":"i32"}}}
            ]})
        );
    }

    #[test]
    fn let_and_expression_statements_and_patterns_are_exact() {
        let block = dump_function_block(
            r#"fn statements(mut value: i32) -> i32 {
                let ref mut alias: i32 = value;
                let _ = *alias;
                *alias;
                *alias
            }"#,
            "statements",
        );
        assert_eq!(
            serde_json::to_value(block).unwrap(),
            json!({"statements":[
                {"kind":"let","pattern":{"kind":"binding","id":"<id0>","mutability":"immutable","by_ref":"mutable"},"type":{"kind":"primitive","name":"i32"},"initializer":{"kind":"path","value":{"kind":"binding","id":"<id1>"}}},
                {"kind":"let","pattern":{"kind":"wildcard"},"type":null,"initializer":{"kind":"unary","operator":"deref","operand":{"kind":"path","value":{"kind":"binding","id":"<id0>"}}}},
                {"kind":"expression","expression":{"kind":"unary","operator":"deref","operand":{"kind":"path","value":{"kind":"binding","id":"<id0>"}}},"semicolon":true},
                {"kind":"expression","expression":{"kind":"unary","operator":"deref","operand":{"kind":"path","value":{"kind":"binding","id":"<id0>"}}},"semicolon":false}
            ]})
        );
    }

    #[test]
    fn unsupported_dump_node_discards_only_mapped_observation() {
        let source = r#"
unsafe fn read(left: &i32, right: &i32) -> i32 { #[proctor(0)] (|| *left)() + *right }
unsafe fn __proctor_source_read(left: *const i32, right: *const i32) -> i32 {
    #[proctor(0)] *left + *right
}
"#;
        let document = extract(source).unwrap();
        assert_eq!(document.observations.len(), 1);
        assert_eq!(
            document.observations[0].source_expression,
            Expression::Unary {
                operator: UnaryOperator::Deref,
                operand: Box::new(Expression::Path {
                    value: ValueIdentity::Binding { id: "<id0>".into() }
                })
            }
        );
    }

    #[test]
    fn namespaces_follow_source_then_target_first_occurrence() {
        let source = r#"
struct Node { value: i32 }
struct Offset { index: usize }
unsafe fn helper(value: usize) -> usize { value }
unsafe fn read(left: &[Node], offset: Offset) -> i32 {
    #[proctor(0)] left[helper(offset.index)].value
}
unsafe fn __proctor_source_read(left: *const Node, offset: Offset) -> i32 {
    #[proctor(0)] (*left.add(helper(offset.index))).value
}
"#;
        let observation = extract(source).unwrap().observations.remove(0);
        let encoded = serde_json::to_string(&observation).unwrap();
        assert!(encoded.contains("<id0>"));
        assert!(encoded.contains("<id1>"));
        assert!(encoded.contains("<fn0>"));
        assert!(encoded.contains("<field0>"));
        assert!(encoded.contains("<struct0>"));
        assert!(encoded.contains("<struct1>"));
        for original in ["left", "offset", "helper", "Node", "Offset"] {
            assert!(
                !encoded.contains(original),
                "leaked `{original}` in {encoded}"
            );
        }
    }

    #[test]
    fn crate_local_constant_static_and_method_policy() {
        let source = r#"
static OFFSET: usize = 0;
const STEP: usize = 1;
struct Index;
impl Index {
    const BASE: usize = 2;
    fn get(&self) -> usize { 0 }
    fn base() -> usize { 0 }
}
unsafe fn read(pointer: &[i32], index: Index) -> i32 {
    #[proctor(0)] pointer[index.get() + Index::base() + OFFSET + STEP + Index::BASE]
}
unsafe fn __proctor_source_read(pointer: *const i32, index: Index) -> i32 {
    #[proctor(0)] *pointer.add(index.get() + Index::base() + OFFSET + STEP + Index::BASE)
}
"#;
        let observation = extract(source).unwrap().observations.remove(0);
        let encoded = serde_json::to_string(&observation.source_expression).unwrap();
        for id in [
            "<method0>",
            "<method1>",
            "<static0>",
            "<const0>",
            "<const1>",
        ] {
            assert!(encoded.contains(id), "missing `{id}` in {encoded}");
        }

        let trait_method = r#"
trait IndexValue { fn get(&self) -> usize; }
struct Index;
impl IndexValue for Index { fn get(&self) -> usize { 0 } }
unsafe fn read(pointer: &[i32], index: Index) -> i32 {
    #[proctor(0)] pointer[index.get()]
}
unsafe fn __proctor_source_read(pointer: *const i32, index: Index) -> i32 {
    #[proctor(0)] *pointer.add(index.get())
}
"#;
        assert!(extract(trait_method).unwrap().observations.is_empty());
    }

    #[test]
    fn aliases_and_cast_syntax_normalize_to_one_tree() {
        let values = dump_parameter_types(
            "type Pointer = *const i32; unsafe fn values(a: Pointer, b: *const i32) {}",
            "values",
        );
        let expected = serde_json::json!({
            "kind": "raw_pointer",
            "mutability": "const",
            "pointee": { "kind": "primitive", "name": "i32" }
        });
        assert_eq!(serde_json::to_value(&values[0]).unwrap(), expected);
        assert_eq!(values[0], values[1]);
        let mut malformed = expected;
        malformed["unexpected"] = serde_json::json!(true);
        assert!(serde_json::from_value::<TypeTree>(malformed).is_err());
    }

    #[test]
    fn slice_array_raw_ref_tuple_and_primitives_have_exact_variants() {
        let values = dump_parameter_types(
            "unsafe fn values(a: &[u8], b: [u16; 3], c: *mut i32, d: (char, f64, &str)) {}",
            "values",
        );
        let expected = serde_json::json!([
            {
                "kind": "reference",
                "mutability": "shared",
                "pointee": {
                    "kind": "slice",
                    "element": { "kind": "primitive", "name": "u8" }
                }
            },
            {
                "kind": "array",
                "element": { "kind": "primitive", "name": "u16" },
                "length": 3
            },
            {
                "kind": "raw_pointer",
                "mutability": "mut",
                "pointee": { "kind": "primitive", "name": "i32" }
            },
            {
                "kind": "tuple",
                "elements": [
                    { "kind": "primitive", "name": "char" },
                    { "kind": "primitive", "name": "f64" },
                    {
                        "kind": "reference",
                        "mutability": "shared",
                        "pointee": { "kind": "primitive", "name": "str" }
                    }
                ]
            }
        ]);
        assert_eq!(serde_json::to_value(&values).unwrap(), expected);
        let mut malformed = expected[0].clone();
        malformed["lifetime"] = serde_json::json!("erased");
        assert!(serde_json::from_value::<TypeTree>(malformed).is_err());
    }

    #[test]
    fn external_generic_adt_uses_defining_identity_and_type_arguments() {
        let values = dump_parameter_types("unsafe fn values(value: Option<Box<i32>>) {}", "values");
        let expected = serde_json::json!({
            "kind": "adt",
            "adt_kind": "enum",
            "identity": {
                "kind": "external",
                "crate": "core",
                "path": ["option", "Option"]
            },
            "arguments": [{
                "kind": "adt",
                "adt_kind": "struct",
                "identity": {
                    "kind": "external",
                    "crate": "alloc",
                    "path": ["boxed", "Box"]
                },
                "arguments": [
                    { "kind": "primitive", "name": "i32" },
                    {
                        "kind": "adt",
                        "adt_kind": "struct",
                        "identity": {
                            "kind": "external",
                            "crate": "alloc",
                            "path": ["alloc", "Global"]
                        },
                        "arguments": []
                    }
                ]
            }]
        });
        assert_eq!(serde_json::to_value(&values[0]).unwrap(), expected);
        let mut malformed = expected;
        malformed["kind"] = serde_json::json!("unknown");
        assert!(serde_json::from_value::<TypeTree>(malformed).is_err());
    }

    #[test]
    fn local_adts_fields_and_variants_are_anonymized_consistently() {
        let source = r#"
struct LocalStruct { value: i32 }
enum LocalEnum { Value { value: i32 } }
union LocalUnion { value: i32 }
unsafe fn values(a: LocalStruct, b: LocalEnum, c: LocalUnion) {}
"#;
        let values = dump_parameter_types(source, "values");
        assert_eq!(
            serde_json::to_value(values).unwrap(),
            serde_json::json!([
                {
                    "kind": "adt",
                    "adt_kind": "struct",
                    "identity": { "kind": "local", "id": "<struct0>" },
                    "arguments": []
                },
                {
                    "kind": "adt",
                    "adt_kind": "enum",
                    "identity": { "kind": "local", "id": "<enum0>" },
                    "arguments": []
                },
                {
                    "kind": "adt",
                    "adt_kind": "union",
                    "identity": { "kind": "local", "id": "<union0>" },
                    "arguments": []
                }
            ])
        );
    }

    #[test]
    fn unrepresentable_recorded_type_discards_one_observation() {
        let source = r#"
unsafe fn helper(value: i32) -> i32 { value }
unsafe fn read(pointer: &i32) -> unsafe fn(i32) -> i32 { #[proctor(0)] helper }
unsafe fn __proctor_source_read(pointer: *const i32) -> i32 { #[proctor(0)] *pointer }
"#;
        assert!(extract(source).unwrap().observations.is_empty());
    }

    #[test]
    fn four_expression_types_and_two_anchor_types_are_all_recorded() {
        let source = r#"
unsafe fn read(pointer: &i32) -> i32 { #[proctor(0)] *pointer }
unsafe fn __proctor_source_read(pointer: *const i32) -> i32 { #[proctor(0)] *pointer }
"#;
        let observation = extract(source).unwrap().observations.remove(0);
        assert_eq!(observation.pointer_anchors.len(), 1);
        let primitive = TypeTree::Primitive { name: "i32".into() };
        assert_eq!(observation.source_type, primitive);
        assert_eq!(observation.source_adjusted_type, primitive);
        assert_eq!(observation.target_type, primitive);
        assert_eq!(observation.target_adjusted_type, primitive);
    }

    #[test]
    fn raw_receiver_allowlist_grows_through_deref() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32, mut index: usize) -> i32 {
    #[proctor(0)] *pointer.add(index)
}
unsafe fn target(mut pointer: &[i32], mut index: usize) -> i32 {
    #[proctor(0)] pointer[index]
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0]).unwrap();
        let primitive = json!({ "kind": "primitive", "name": "i32" });
        let pointer = json!({ "kind": "path", "value": { "kind": "binding", "id": "<id0>" } });
        let index = json!({ "kind": "path", "value": { "kind": "binding", "id": "<id1>" } });
        assert_eq!(
            serde_json::to_value(&document.observations).unwrap(),
            json!([{
                "source_expression": {
                    "kind": "unary",
                    "operator": "deref",
                    "operand": {
                        "kind": "method_call",
                        "receiver": pointer.clone(),
                        "method": {
                            "kind": "external",
                            "crate": "core",
                            "path": ["ptr", "const_ptr", "add"]
                        },
                        "arguments": [index.clone()]
                    }
                },
                "target_expression": {
                    "kind": "index",
                    "base": pointer,
                    "index": index
                },
                "pointer_anchors": [{
                    "id": "<id0>",
                    "source_type": {
                        "kind": "raw_pointer",
                        "mutability": "const",
                        "pointee": primitive.clone()
                    },
                    "target_type": {
                        "kind": "reference",
                        "mutability": "shared",
                        "pointee": {
                            "kind": "slice",
                            "element": primitive.clone()
                        }
                    }
                }],
                "source_type": primitive.clone(),
                "source_adjusted_type": primitive.clone(),
                "target_type": primitive.clone(),
                "target_adjusted_type": primitive
            }])
        );
        let methods = r#"
unsafe fn methods(p: *const i32, q: *const i32, n: usize) {
    let _ = p.offset(n as isize);
    let _ = p.add(n);
    let _ = p.sub(n);
    let _ = p.wrapping_offset(n as isize);
    let _ = p.wrapping_add(n);
    let _ = p.wrapping_sub(n);
    let _ = p.offset_from(q);
    let _ = p.is_null();
    let _ = p.read();
}
"#;
        utils::compilation::run_compiler_on_str(methods, |tcx| {
            let mut surface = utils::ast::parse_crate(methods.to_owned());
            let mut mapper = utils::ir::AstToHirMapper::new(tcx);
            mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
            let ast_to_hir = mapper.ast_to_hir;
            let mut functions = HashMap::new();
            collect_functions(&surface.items, &mut vec![], &mut functions);
            let decisions = plain_statements(functions["methods"])
                .into_iter()
                .map(|statement| {
                    let expression = statement_expression(statement).unwrap();
                    let ExprKind::MethodCall(call) = &expression.kind else { unreachable!() };
                    (
                        call.seg.ident.name.as_str().to_owned(),
                        resolved_builtin_raw_pointer_method(expression, &ast_to_hir, tcx).is_some(),
                    )
                })
                .collect::<Vec<_>>();
            assert_eq!(
                decisions,
                [
                    ("offset".into(), true),
                    ("add".into(), true),
                    ("sub".into(), true),
                    ("wrapping_offset".into(), true),
                    ("wrapping_add".into(), true),
                    ("wrapping_sub".into(), true),
                    ("offset_from".into(), true),
                    ("is_null".into(), true),
                    ("read".into(), false),
                ]
            );
        })
        .unwrap();
    }

    #[test]
    fn array_tuple_repeat_values_finish_nonpointer_elements() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32) -> ([i32; 1], (i32,), [i32; 2]) {
    #[proctor(0)] ([*pointer], (*pointer,), [*pointer; 2])
}
unsafe fn target(mut pointer: &i32) -> ([i32; 1], (i32,), [i32; 2]) {
    #[proctor(0)] ([*pointer], (*pointer,), [*pointer; 2])
}
"#;
        assert_eq!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .len(),
            3
        );
    }

    #[test]
    fn all_resolved_direct_call_arguments_finish() {
        let source = r#"
unsafe fn local_read(mut pointer: *const i32) -> i32 { *pointer }
unsafe extern "C" { fn foreign_read(pointer: *const i32) -> i32; }
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)]
    local_read(pointer)
        + std::ptr::read(pointer)
        + foreign_read(pointer)
}
unsafe fn target(mut pointer: &i32) -> i32 {
    #[proctor(0)]
    local_read(pointer as *const i32)
        + std::ptr::read(pointer as *const i32)
        + foreign_read(pointer as *const i32)
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0]).unwrap();
        assert_eq!(document.observations.len(), 3);
        for observation in document.observations {
            assert!(matches!(
                observation.source_type,
                TypeTree::RawPointer { .. }
            ));
            assert!(matches!(
                observation.target_type,
                TypeTree::RawPointer { .. }
            ));
        }
    }

    #[test]
    fn indirect_calls_reject() {
        let source = r#"
unsafe fn source_copy(
    mut function: unsafe fn(*const i32) -> i32,
    mut pointer: *const i32,
) -> i32 {
    #[proctor(0)] function(pointer)
}
unsafe fn target(
    mut function: unsafe fn(*const i32) -> i32,
    mut pointer: &i32,
) -> i32 {
    #[proctor(0)] function(pointer as *const i32)
}
"#;
        assert!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn method_receiver_and_argument_roles_are_closed() {
        let source = r#"
struct Sink;
impl Sink { fn take(&self, value: u32) -> u32 { value } }
unsafe fn source_copy(mut pointer: *const u32, mut sink: Sink) -> u32 {
    #[proctor(0)] (*pointer).count_ones();
    #[proctor(1)] sink.take(*pointer)
}
unsafe fn target(mut pointer: &u32, mut sink: Sink) -> u32 {
    #[proctor(0)] pointer.count_ones();
    #[proctor(1)] sink.take(*pointer)
}
"#;
        let first = extract_case(source, "source_copy", "target", vec![0]).unwrap();
        let second = extract_case(source, "source_copy", "target", vec![1]).unwrap();
        assert_eq!(first.observations.len(), 1, "label 0: {first:?}");
        assert_eq!(second.observations.len(), 1, "label 1: {second:?}");
        let document = ObservationDocument {
            schema_version: OBSERVATION_SCHEMA_VERSION,
            observations: first
                .observations
                .into_iter()
                .chain(second.observations)
                .collect(),
        };
        assert!(matches!(
            document.observations[0].target_type,
            TypeTree::Reference { .. }
        ));
        assert_eq!(
            document.observations[0].target_adjusted_type,
            TypeTree::Primitive { name: "u32".into() }
        );
    }

    #[test]
    fn conditions_and_guards_finish_without_required_type_inference() {
        let match_source = r#"
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)]
    match 0 {
        _ if pointer.is_null() => { #[proctor(1)] 0 }
        _ => { #[proctor(2)] 1 }
    }
}
unsafe fn target(mut pointer: Option<&i32>) -> i32 {
    #[proctor(0)]
    match 0 {
        _ if pointer.is_none() => { #[proctor(1)] 0 }
        _ => { #[proctor(2)] 1 }
    }
}
"#;
        assert_eq!(
            extract_case(match_source, "source_copy", "target", vec![0, 1, 2])
                .unwrap()
                .observations
                .len(),
            1
        );
        let control_source = r#"
unsafe fn source_copy(mut pointer: *const i32) {
    #[proctor(0)] if pointer.is_null() { #[proctor(1)] return; }
    #[proctor(2)] while pointer.is_null() { #[proctor(3)] return; }
}
unsafe fn target(mut pointer: Option<&i32>) {
    #[proctor(0)] if pointer.is_none() { #[proctor(1)] return; }
    #[proctor(2)] while pointer.is_none() { #[proctor(3)] return; }
}
"#;
        assert_eq!(
            extract_case(control_source, "source_copy", "target", vec![0, 1, 2, 3])
                .unwrap()
                .observations
                .len(),
            2
        );
    }

    #[test]
    fn let_assignment_return_and_root_semicolon_finish() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)] let mut value: i32 = *pointer;
    #[proctor(1)] value = *pointer.add(1);
    #[proctor(2)] pointer.add(2);
    #[proctor(3)] return *pointer.add(3);
}
unsafe fn target(mut pointer: &[i32]) -> i32 {
    #[proctor(0)] let mut value: i32 = pointer[0];
    #[proctor(1)] value = pointer[1];
    #[proctor(2)] pointer.get(2);
    #[proctor(3)] return pointer[3];
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0, 1, 2, 3]).unwrap();
        assert_eq!(document.observations.len(), 4);
        assert!(matches!(
            document.observations[2].source_type,
            TypeTree::RawPointer { .. }
        ));
        assert!(matches!(
            document.observations[2].target_type,
            TypeTree::Adt { .. }
        ));
    }

    #[test]
    fn field_base_allows_deref_removal_and_anonymizes_field() {
        let source = r#"
struct Pair { value: i32 }
unsafe fn source_copy(mut pointer: *const Pair) -> i32 {
    #[proctor(0)] (*pointer).value
}
unsafe fn target(mut pointer: &Pair) -> i32 {
    #[proctor(0)] pointer.value
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0]).unwrap();
        assert_eq!(document.observations.len(), 1);
        assert!(matches!(
            document.observations[0].source_expression,
            Expression::Unary {
                operator: UnaryOperator::Deref,
                ..
            }
        ));
    }

    #[test]
    fn index_index_and_struct_field_value_finish() {
        let source = r#"
struct Pair { value: i32 }
unsafe fn source_copy(mut pointer: *const usize, mut values: &[i32]) -> Pair {
    #[proctor(0)] Pair { value: values[*pointer] }
}
unsafe fn target(mut pointer: &usize, mut values: &[i32]) -> Pair {
    #[proctor(0)] Pair { value: values[*pointer] }
}
"#;
        assert_eq!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .len(),
            1
        );
    }

    #[test]
    fn address_and_cast_grow_transparently_through_parentheses() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32) -> usize {
    #[proctor(0)] ((&*pointer) as *const i32) as usize
}
unsafe fn target(mut pointer: &i32) -> usize {
    #[proctor(0)] (pointer as *const i32) as usize
}
"#;
        let document = extract_case(source, "source_copy", "target", vec![0]).unwrap();
        assert_eq!(document.observations.len(), 1);
        assert_eq!(
            document.observations[0].source_type,
            TypeTree::Primitive {
                name: "usize".into()
            }
        );
    }

    #[test]
    fn pointerlike_aggregate_roles_reject() {
        let classifier = r#"
struct Contains(*const i32);
type Raw = *mut i32;
type Ref<'a> = &'a mut i32;
type Slice<'a> = &'a mut [i32];
type OptionalRef<'a> = Option<&'a mut i32>;
type Owned = Box<i32>;
type OptionalOwned = Option<Box<i32>>;
type OwnedSlice = Box<[i32]>;
type OptionalOwnedSlice = Option<Box<[i32]>>;
fn raw(value: Raw) {} fn reference(value: Ref<'_>) {} fn slice(value: Slice<'_>) {}
fn optional_ref(value: OptionalRef<'_>) {} fn owned(value: Owned) {}
fn optional_owned(value: OptionalOwned) {} fn owned_slice(value: OwnedSlice) {}
fn optional_owned_slice(value: OptionalOwnedSlice) {} fn contains(value: Contains) {}
"#;
        utils::compilation::run_compiler_on_str(classifier, |tcx| {
            let mut surface = utils::ast::parse_crate(classifier.to_owned());
            let mut mapper = utils::ir::AstToHirMapper::new(tcx);
            mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
            let ast_to_hir = mapper.ast_to_hir;
            let mut functions = HashMap::new();
            collect_functions(&surface.items, &mut vec![], &mut functions);
            for name in [
                "raw",
                "reference",
                "slice",
                "optional_ref",
                "owned",
                "optional_owned",
                "owned_slice",
                "optional_owned_slice",
            ] {
                let ItemKind::Fn(box function) = &functions[name].kind else { unreachable!() };
                let (_, binding) =
                    simple_binding(&function.sig.decl.inputs[0].pat, &ast_to_hir, tcx).unwrap();
                assert!(
                    pointer_like(binding_type(binding, tcx).unwrap(), tcx),
                    "{name}"
                );
            }
            let ItemKind::Fn(box function) = &functions["contains"].kind else { unreachable!() };
            let (_, binding) =
                simple_binding(&function.sig.decl.inputs[0].pat, &ast_to_hir, tcx).unwrap();
            assert!(!pointer_like(binding_type(binding, tcx).unwrap(), tcx));
        })
        .unwrap();
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32) -> ([*const i32; 1], (*const i32,)) {
    #[proctor(0)] ([pointer], (pointer,))
}
unsafe fn target<'a>(mut pointer: Option<&'a i32>)
    -> ([Option<&'a i32>; 1], (Option<&'a i32>,))
{
    #[proctor(0)] ([pointer], (pointer,))
}
"#;
        assert!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn overloaded_operations_reject() {
        let binary = r#"
use std::ops::Add;
struct Wrap(*const i32);
impl Add<*const i32> for Wrap {
    type Output = i32;
    fn add(self, _other: *const i32) -> i32 { 0 }
}
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)] Wrap(core::ptr::null()) + pointer
}
unsafe fn target(mut pointer: &i32) -> i32 {
    #[proctor(0)] Wrap(core::ptr::null()) + (pointer as *const i32)
}
"#;
        assert!(
            extract_case(binary, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
        let assign = r#"
use std::ops::AddAssign;
struct Wrap;
impl AddAssign<*const i32> for Wrap {
    fn add_assign(&mut self, _other: *const i32) {}
}
unsafe fn source_copy(mut pointer: *const i32, mut value: Wrap) {
    #[proctor(0)] value += pointer;
}
unsafe fn target(mut pointer: &i32, mut value: Wrap) {
    #[proctor(0)] value += pointer as *const i32;
}
"#;
        assert!(
            extract_case(assign, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );

        let target_binary = r#"
use std::ops::Add;
struct Wrap(i32);
impl Add<i32> for Wrap { type Output = i32; fn add(self, other: i32) -> i32 { self.0 + other } }
unsafe fn source_copy(pointer: *const i32) -> i32 { #[proctor(0)] *pointer + 1 }
unsafe fn target(pointer: Wrap) -> i32 { #[proctor(0)] pointer + 1 }
"#;
        let target_assign = r#"
use std::ops::AddAssign;
struct Wrap(i32);
impl AddAssign<i32> for Wrap { fn add_assign(&mut self, other: i32) { self.0 += other; } }
unsafe fn source_copy(pointer: *mut i32) { #[proctor(0)] *pointer += 1; }
unsafe fn target(mut pointer: Wrap) { #[proctor(0)] pointer += 1; }
"#;
        let target_unary = r#"
use std::ops::Neg;
struct Wrap(i32);
impl Neg for Wrap { type Output = i32; fn neg(self) -> i32 { -self.0 } }
unsafe fn source_copy(pointer: *const i32) -> i32 { #[proctor(0)] -*pointer }
unsafe fn target(pointer: Wrap) -> i32 { #[proctor(0)] -pointer }
"#;
        let target_index = r#"
use std::ops::Index;
struct Values([i32; 1]);
impl Index<usize> for Values { type Output = i32; fn index(&self, index: usize) -> &i32 { &self.0[index] } }
unsafe fn source_copy(pointer: *const usize, values: [i32; 1]) -> i32 { #[proctor(0)] values[*pointer] }
unsafe fn target(pointer: &usize, values: Values) -> i32 { #[proctor(0)] values[*pointer] }
"#;
        for source in [target_binary, target_assign, target_unary, target_index] {
            assert!(
                extract_case(source, "source_copy", "target", vec![0])
                    .unwrap()
                    .observations
                    .is_empty()
            );
        }
    }

    #[test]
    fn unsupported_control_and_expression_variants_reject_without_panics() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const Result<i32, i32>) -> Result<i32, i32> {
    #[proctor(0)] Ok((*pointer)?)
}
unsafe fn target(mut pointer: &Result<i32, i32>) -> Result<i32, i32> {
    #[proctor(0)] Ok((*pointer)?)
}
"#;
        assert!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn index_base_and_struct_rest_reject_independently() {
        let index = r#"
unsafe fn source_copy(mut pointer: *const [i32], mut index: usize) -> i32 {
    #[proctor(0)] (*pointer)[index]
}
unsafe fn target(mut pointer: &[i32], mut index: usize) -> i32 {
    #[proctor(0)] pointer[index]
}
"#;
        assert!(
            extract_case(index, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
        let rest = r#"
#[derive(Copy, Clone)] struct Pair { value: i32 }
unsafe fn source_copy(mut pointer: *const Pair) -> Pair {
    #[proctor(0)] Pair { value: 1, ..*pointer }
}
unsafe fn target(mut pointer: &Pair) -> Pair {
    #[proctor(0)] Pair { value: 1, ..*pointer }
}
"#;
        assert!(
            extract_case(rest, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn builtin_assignop_and_other_unary_finish() {
        let source = r#"
unsafe fn source_copy(mut pointer: *mut bool) {
    #[proctor(0)] *pointer &= true;
    #[proctor(1)] let value = !*pointer;
}
unsafe fn target(mut pointer: &mut bool) {
    #[proctor(0)] *pointer &= true;
    #[proctor(1)] let value: bool = !*pointer;
}
"#;
        assert_eq!(
            extract_case(source, "source_copy", "target", vec![0, 1])
                .unwrap()
                .observations
                .len(),
            2
        );
    }

    #[test]
    fn strict_ancestry_overlap_skips_complete_statement() {
        let source = r#"
unsafe fn source_copy(mut base: *const i32, mut other: *const i32) -> i32 {
    #[proctor(0)] *base.offset(other.offset_from(base))
}
unsafe fn target(mut base: &[i32], mut other: &[i32]) -> i32 {
    #[proctor(0)] base[other.as_ptr().offset_from(base.as_ptr()) as usize]
}
"#;
        assert!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn nonregion_operator_or_child_role_change_rejects_statement() {
        let source = r#"
unsafe fn source_copy(mut pointer: *const i32, mut scalar: i32) -> i32 {
    #[proctor(0)] ((*pointer)) + scalar
}
unsafe fn target(mut pointer: &i32, mut scalar: i32) -> i32 {
    #[proctor(0)] scalar - (((*pointer)))
}
"#;
        assert!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn rejected_anchor_does_not_block_disjoint_valid_anchor() {
        let source = r#"
unsafe fn source_copy(
    mut good: *const i32,
    mut rejected: *const [i32],
) -> i32 {
    #[proctor(0)] *good + (*rejected)[0]
}
unsafe fn target(mut good: &i32, mut rejected: *const [i32]) -> i32 {
    #[proctor(0)] *good + (*rejected)[0]
}
"#;
        assert_eq!(
            extract_case(source, "source_copy", "target", vec![0])
                .unwrap()
                .observations
                .len(),
            1
        );
    }

    #[test]
    fn logical_callee_identity_aligns_wrapper_and_implementation() {
        let source = r#"
unsafe fn index(mut value: i32) -> usize { value as usize }
unsafe fn __proctor_wrapper_index(mut value: i32) -> usize { index(value) }
unsafe fn source_copy(mut pointer: *const i32) -> i32 {
    #[proctor(0)] *pointer.add(__proctor_wrapper_index(1))
}
unsafe fn target(mut pointer: &[i32]) -> i32 {
    #[proctor(0)] pointer[index(1)]
}
"#;
        let metadata = ReplacementObservationMetadata {
            schema_version: 1,
            candidate_sha256: sha256_hex(b""),
            statement_pairs_sha256: sha256_hex(b""),
            observation_source_sha256: String::new(),
            accepted_correspondence: vec![CallableCorrespondence {
                item_id: 6,
                logical_path: "index".into(),
                implementation_path: "index".into(),
                wrapper_path: Some("__proctor_wrapper_index".into()),
            }],
            new_correspondence: vec![CallableCorrespondence {
                item_id: 7,
                logical_path: "target".into(),
                implementation_path: "target".into(),
                wrapper_path: None,
            }],
            current_items: vec![CurrentObservationItem {
                item_id: 7,
                logical_path: "target".into(),
                source_copy_path: "source_copy".into(),
                implementation_path: "target".into(),
                wrapper_path: None,
                transform_labels: vec![0],
            }],
        };
        assert_eq!(
            extract_metadata(source, metadata.clone())
                .unwrap()
                .observations
                .len(),
            1
        );
        let mut omitted = metadata;
        omitted.accepted_correspondence.clear();
        assert!(
            extract_metadata(source, omitted)
                .unwrap()
                .observations
                .is_empty()
        );
    }

    #[test]
    fn assign_assignop_field_index_and_struct_are_exact() {
        let source = r#"
struct Pair { value: i32 }
enum Choice { Pair { value: i32 } }
unsafe fn values(mut pair: Pair, array: [i32; 1]) {
    pair.value = array[0];
    pair.value += 1;
    let _ = Choice::Pair { value: pair.value };
    let _ = Pair { value: pair.value, ..pair };
}
"#;
        let values = dump_statement_expressions(source, "values");
        assert!(matches!(values[0], Expression::Assign { .. }));
        assert!(matches!(values[1], Expression::AssignOp { .. }));
        let Expression::Struct {
            adt,
            variant,
            fields,
            rest: None,
        } = &values[2]
        else {
            panic!()
        };
        assert_eq!(
            adt,
            &AdtIdentity::Local {
                id: "<enum0>".into()
            }
        );
        assert_eq!(
            variant,
            &Some(VariantIdentity::Local {
                owner: AdtIdentity::Local {
                    id: "<enum0>".into()
                },
                id: "<variant0>".into(),
            })
        );
        assert_eq!(fields.len(), 1);
        assert!(matches!(
            values[3],
            Expression::Struct { rest: Some(_), .. }
        ));
    }

    #[test]
    fn range_address_of_return_and_repeat_are_exact() {
        let source = r#"
unsafe fn values(value: i32) {
    let _ = 0..=value;
    let _ = ..;
    let _ = &raw const value;
    let _ = [value; 2];
}
"#;
        let values = dump_statement_expressions(source, "values");
        assert!(matches!(
            values[0],
            Expression::Range {
                limits: RangeLimits::Closed,
                ..
            }
        ));
        assert_eq!(
            values[1],
            Expression::Range {
                start: None,
                end: None,
                limits: RangeLimits::HalfOpen,
            }
        );
        assert!(matches!(
            values[2],
            Expression::AddressOf {
                borrow: BorrowKind::Raw,
                ..
            }
        ));
        assert!(matches!(values[3], Expression::Repeat { .. }));
    }
}
