use std::collections::{HashMap, HashSet};

use rustc_ast::{
    AttrKind, Attribute, Expr, ExprKind, Item, ItemKind, Local, LocalKind, Stmt, StmtKind,
    ptr::P,
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use thin_vec::ThinVec;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PreservationError {
    pub code: &'static str,
    pub message: String,
}

pub(crate) fn validate_preservation_metadata(
    item: &Item,
    needs_transformation: bool,
    statements_requiring_transformation: &[u32],
) -> Result<(), PreservationError> {
    if needs_transformation == statements_requiring_transformation.is_empty() {
        return Err(metadata_error(
            "inconsistent_preservation_metadata",
            "`needs_transformation` must equal whether `statements_requiring_transformation` is nonempty",
        ));
    }
    if statements_requiring_transformation
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(metadata_error(
            "invalid_transformation_labels",
            "`statements_requiring_transformation` must be strictly increasing and unique",
        ));
    }

    let parents = collect_label_parents(item)?;
    let all_labels = parents.keys().copied().collect::<HashSet<_>>();
    let transformed = statements_requiring_transformation
        .iter()
        .copied()
        .collect::<HashSet<_>>();
    if let Some(label) = statements_requiring_transformation
        .iter()
        .find(|label| !all_labels.contains(label))
    {
        return Err(metadata_error(
            "unknown_transformation_label",
            format!("transformation label {label} does not occur in the annotated target skeleton"),
        ));
    }
    for label in statements_requiring_transformation {
        let mut parent = parents[label];
        while let Some(ancestor) = parent {
            if !transformed.contains(&ancestor) {
                return Err(metadata_error(
                    "open_preserved_parent",
                    format!(
                        "preserved label {ancestor} contains transformed descendant label {label}"
                    ),
                ));
            }
            parent = parents[&ancestor];
        }
    }
    Ok(())
}

pub(crate) fn canonicalize_function(
    expected: &Item,
    result: &Item,
    needs_transformation: bool,
    statements_requiring_transformation: &[u32],
) -> Result<P<Item>, PreservationError> {
    canonicalize_function_impl(
        expected,
        result,
        needs_transformation,
        statements_requiring_transformation,
        false,
    )
}

pub(crate) fn canonicalize_function_for_replacement(
    expected: &Item,
    result: &Item,
    needs_transformation: bool,
    statements_requiring_transformation: &[u32],
) -> Result<P<Item>, PreservationError> {
    canonicalize_function_impl(
        expected,
        result,
        needs_transformation,
        statements_requiring_transformation,
        true,
    )
}

fn canonicalize_function_impl(
    expected: &Item,
    result: &Item,
    needs_transformation: bool,
    statements_requiring_transformation: &[u32],
    require_complete_alignment: bool,
) -> Result<P<Item>, PreservationError> {
    validate_preservation_metadata(
        expected,
        needs_transformation,
        statements_requiring_transformation,
    )?;
    let ItemKind::Fn(box expected_function) = &expected.kind else {
        return Err(metadata_error(
            "invalid_expected_skeleton",
            "preservation metadata requires one function skeleton",
        ));
    };
    if !require_complete_alignment
        && collect_label_parents(expected)?.len() == statements_requiring_transformation.len()
    {
        return Ok(P(result.clone()));
    }
    let ItemKind::Fn(box returned_function) = &result.kind else {
        return Err(structural_error(
            "unexpected_function",
            "the returned item is not a function",
        ));
    };
    let mut canonical = P(expected.clone());
    let ItemKind::Fn(box result_function) = &mut canonical.kind else {
        unreachable!("the expected item was checked above")
    };
    result_function.body = returned_function.body.clone();
    let transformed = statements_requiring_transformation
        .iter()
        .copied()
        .collect::<HashSet<_>>();
    canonicalize_statement_list(
        &expected_function
            .body
            .as_ref()
            .expect("validated function skeleton has a body")
            .stmts,
        &mut result_function
            .body
            .as_mut()
            .expect("returned function has a body")
            .stmts,
        false,
        &transformed,
    )?;
    Ok(canonical)
}

fn metadata_error(code: &'static str, message: impl Into<String>) -> PreservationError {
    PreservationError {
        code,
        message: message.into(),
    }
}

fn structural_error(code: &'static str, message: impl Into<String>) -> PreservationError {
    PreservationError {
        code,
        message: message.into(),
    }
}

fn collect_label_parents(item: &Item) -> Result<HashMap<u32, Option<u32>>, PreservationError> {
    let ItemKind::Fn(box function) = &item.kind else {
        return Err(metadata_error(
            "invalid_expected_skeleton",
            "preservation metadata requires one function skeleton",
        ));
    };
    crate::skeleton::collect_opaque_nested_ifs(item, "").map_err(|error| {
        metadata_error(
            "invalid_expected_skeleton",
            format!(
                "expected skeleton has unsupported nested control: {}",
                error.message
            ),
        )
    })?;
    let mut collector = LabelTreeCollector {
        parents: HashMap::new(),
        parent: None,
        error: None,
    };
    collector.collect_block(
        function
            .body
            .as_ref()
            .expect("validated function skeleton has a body"),
    );
    match collector.error {
        Some(error) => Err(error),
        None => Ok(collector.parents),
    }
}

struct LabelTreeCollector {
    parents: HashMap<u32, Option<u32>>,
    parent: Option<u32>,
    error: Option<PreservationError>,
}

impl LabelTreeCollector {
    fn collect_block(&mut self, block: &rustc_ast::Block) {
        for statement in &block.stmts {
            self.collect_statement(statement);
            if self.error.is_some() {
                return;
            }
        }
    }

    fn collect_statement(&mut self, statement: &Stmt) {
        let Some(label) = statement_label(statement) else {
            self.error = Some(metadata_error(
                "invalid_expected_skeleton",
                "every expected statement must have one canonical `#[proctor(N)]` label",
            ));
            return;
        };
        if self.parents.insert(label, self.parent).is_some() {
            self.error = Some(metadata_error(
                "invalid_expected_skeleton",
                format!("expected statement label {label} is duplicated"),
            ));
            return;
        }
        if non_control_payload(statement).is_some_and(contains_statement_label) {
            self.error = Some(metadata_error(
                "invalid_expected_skeleton",
                format!(
                    "opaque restricted conditional beneath label {label} must not contain statement labels"
                ),
            ));
            return;
        }
        let previous = self.parent.replace(label);
        if let StmtKind::Let(local) = &statement.kind
            && let LocalKind::InitElse(_, else_block) = &local.kind
        {
            self.collect_block(else_block);
        }
        if let Some(root) = control_root(statement, false) {
            self.collect_control(root.expression);
        }
        self.parent = previous;
    }

    fn collect_control(&mut self, expression: &Expr) {
        match &expression.kind {
            ExprKind::If(condition, then_block, else_expression) => {
                if self.reject_opaque_operand_labels(condition) {
                    return;
                }
                self.collect_block(then_block);
                if let Some(else_expression) = else_expression {
                    match &else_expression.kind {
                        ExprKind::If(..) => self.collect_control(else_expression),
                        ExprKind::Block(block, _) => self.collect_block(block),
                        _ => {}
                    }
                }
            }
            ExprKind::While(condition, body, _) => {
                if self.reject_opaque_operand_labels(condition) {
                    return;
                }
                self.collect_block(body);
            }
            ExprKind::ForLoop { iter, body, .. } => {
                if self.reject_opaque_operand_labels(iter) {
                    return;
                }
                self.collect_block(body);
            }
            ExprKind::Loop(body, ..) | ExprKind::Block(body, ..) => self.collect_block(body),
            ExprKind::Match(scrutinee, arms, _) => {
                if self.reject_opaque_operand_labels(scrutinee) {
                    return;
                }
                for arm in arms {
                    if let Some(guard) = &arm.guard
                        && self.reject_opaque_operand_labels(guard)
                    {
                        return;
                    }
                    if let Some(body) = &arm.body
                        && let ExprKind::Block(block, _) = &body.kind
                    {
                        self.collect_block(block);
                    }
                }
            }
            _ => {}
        }
    }

    fn reject_opaque_operand_labels(&mut self, expression: &Expr) -> bool {
        if self.error.is_none() && contains_statement_label(expression) {
            let label = self
                .parent
                .expect("control operand is visited beneath its statement label");
            self.error = Some(metadata_error(
                "invalid_expected_skeleton",
                format!(
                    "opaque restricted conditional beneath label {label} must not contain statement labels"
                ),
            ));
            true
        } else {
            false
        }
    }
}

fn non_control_payload(statement: &Stmt) -> Option<&Expr> {
    let (expression, role) = match &statement.kind {
        StmtKind::Let(local) => match &local.kind {
            LocalKind::Init(expression) | LocalKind::InitElse(expression, _) => {
                (expression.as_ref(), ControlRole::LetInitializer)
            }
            LocalKind::Decl => return None,
        },
        StmtKind::Expr(expression) | StmtKind::Semi(expression) => match &expression.kind {
            ExprKind::Ret(Some(value)) => (value.as_ref(), ControlRole::ReturnValue),
            ExprKind::Break(_, Some(value)) => (value.as_ref(), ControlRole::BreakValue),
            _ => (expression.as_ref(), ControlRole::Statement),
        },
        _ => return None,
    };
    control_expression(expression, role)
        .is_none()
        .then_some(expression)
}

fn contains_statement_label(expression: &Expr) -> bool {
    struct Finder(bool);

    impl<'ast> Visitor<'ast> for Finder {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if effective_statement_attributes(statement)
                .iter()
                .any(|attribute| !matches!(parse_label_attribute(attribute), Ok(None)))
            {
                self.0 = true;
                return;
            }
            visit::walk_stmt(self, statement);
        }
    }

    let mut finder = Finder(false);
    finder.visit_expr(expression);
    finder.0
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
    expression: &'a Expr,
}

struct ControlRootMut<'a> {
    expression: &'a mut Expr,
}

fn control_root(statement: &Stmt, arm_tail: bool) -> Option<ControlRoot<'_>> {
    match &statement.kind {
        StmtKind::Let(local) => match &local.kind {
            LocalKind::Init(expression) | LocalKind::InitElse(expression, _) => {
                control_expression(expression, ControlRole::LetInitializer)
            }
            LocalKind::Decl => None,
        },
        StmtKind::Expr(expression) | StmtKind::Semi(expression) => match &expression.kind {
            ExprKind::Ret(Some(value)) => control_expression(value, ControlRole::ReturnValue),
            ExprKind::Break(_, Some(value)) => control_expression(value, ControlRole::BreakValue),
            _ => control_expression(
                expression,
                if arm_tail && matches!(statement.kind, StmtKind::Expr(..)) {
                    ControlRole::MatchArmTail
                } else {
                    ControlRole::Statement
                },
            ),
        },
        _ => None,
    }
}

fn control_root_mut(statement: &mut Stmt, arm_tail: bool) -> Option<ControlRootMut<'_>> {
    match &mut statement.kind {
        StmtKind::Let(local) => match &mut local.kind {
            LocalKind::Init(expression) | LocalKind::InitElse(expression, _) => {
                control_expression_mut(expression, ControlRole::LetInitializer)
            }
            LocalKind::Decl => None,
        },
        StmtKind::Expr(expression) => control_statement_expression_mut(
            expression,
            if arm_tail {
                ControlRole::MatchArmTail
            } else {
                ControlRole::Statement
            },
        ),
        StmtKind::Semi(expression) => {
            control_statement_expression_mut(expression, ControlRole::Statement)
        }
        _ => None,
    }
}

fn control_statement_expression_mut(
    expression: &mut Expr,
    default_role: ControlRole,
) -> Option<ControlRootMut<'_>> {
    let special_role = match expression.kind {
        ExprKind::Ret(Some(..)) => Some(ControlRole::ReturnValue),
        ExprKind::Break(_, Some(..)) => Some(ControlRole::BreakValue),
        _ => None,
    };
    match special_role {
        Some(ControlRole::ReturnValue) => {
            let ExprKind::Ret(Some(value)) = &mut expression.kind else { unreachable!() };
            control_expression_mut(value, ControlRole::ReturnValue)
        }
        Some(ControlRole::BreakValue) => {
            let ExprKind::Break(_, Some(value)) = &mut expression.kind else { unreachable!() };
            control_expression_mut(value, ControlRole::BreakValue)
        }
        _ => control_expression_mut(expression, default_role),
    }
}

fn control_expression(expression: &Expr, role: ControlRole) -> Option<ControlRoot<'_>> {
    let kind = expression_control_kind(expression)?;
    Some(ControlRoot {
        kind,
        role,
        expression,
    })
}

fn control_expression_mut(expression: &mut Expr, _role: ControlRole) -> Option<ControlRootMut<'_>> {
    expression_control_kind(expression)?;
    Some(ControlRootMut { expression })
}

fn expression_control_kind(expression: &Expr) -> Option<ControlKind> {
    Some(match &expression.kind {
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
    })
}

fn canonicalize_statement_list(
    expected: &[Stmt],
    result: &mut ThinVec<Stmt>,
    arm_tail: bool,
    transformed: &HashSet<u32>,
) -> Result<(), PreservationError> {
    let expected_groups = groups(expected);
    let result_groups = groups(result);
    let expected_labels = expected_groups
        .iter()
        .map(|group| {
            group.label.ok_or_else(|| {
                metadata_error(
                    "invalid_expected_skeleton",
                    "every expected statement must have one canonical label",
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(group) = result_groups.iter().find(|group| group.malformed) {
        return Err(structural_error(
            "malformed_label",
            format!(
                "returned statement at sibling position {} has a malformed `proctor` label",
                group.start
            ),
        ));
    }
    let observed_labels = result_groups
        .iter()
        .filter_map(|group| group.label)
        .collect::<Vec<_>>();

    let mut seen = HashSet::new();
    for label in &observed_labels {
        if !seen.insert(*label) {
            return Err(structural_error(
                "nonconsecutive_label",
                format!(
                    "label {label} reappears after another expansion group begins; keep same-label siblings consecutive"
                ),
            ));
        }
    }
    if result_groups.len() == expected_groups.len()
        && result_groups.iter().all(|group| group.label.is_some())
        && observed_labels
            .iter()
            .all(|label| expected_labels.contains(label))
        && observed_labels != expected_labels
    {
        return Err(structural_error(
            "label_order_mismatch",
            "returned statement groups are not in target-skeleton order",
        ));
    }

    for (position, expected_group) in expected_groups.iter().enumerate() {
        let label = expected_labels[position];
        let Some(result_group) = result_groups.get(position) else {
            return Err(structural_error(
                "missing_label",
                format!("label {label} is not locatable in its expected structural role"),
            ));
        };
        match result_group.label {
            Some(observed) if observed == label => {}
            Some(observed) if expected_labels.contains(&observed) => {
                return Err(structural_error(
                    if result_groups.len() == expected_groups.len() {
                        "label_order_mismatch"
                    } else {
                        "missing_label"
                    },
                    format!(
                        "expected label {label} at sibling position {position}, observed label {observed}"
                    ),
                ));
            }
            Some(observed) => {
                return Err(structural_error(
                    "unexpected_label",
                    format!(
                        "unexpected label {observed} occupies sibling position {position} for expected label {label}"
                    ),
                ));
            }
            None => {
                return Err(structural_error(
                    "unlabeled_sibling",
                    format!(
                        "unlabeled statement occupies sibling position {position} for expected label {label}"
                    ),
                ));
            }
        }
        if transformed.contains(&label) {
            canonicalize_transformed_group(
                &expected_group.statements[0],
                &mut result[result_group.start..result_group.end],
                arm_tail,
                label,
                transformed,
            )?;
        }
    }
    if let Some(extra) = result_groups.get(expected_groups.len()) {
        return Err(structural_error(
            if extra.label.is_some() {
                "unexpected_label"
            } else {
                "unlabeled_sibling"
            },
            format!(
                "returned function has an extra statement group at sibling position {}",
                expected_groups.len()
            ),
        ));
    }

    for expected_group in expected_groups.iter().rev() {
        let label = expected_group.label.expect("expected labels were checked");
        if transformed.contains(&label) {
            continue;
        }
        let current_groups = groups(result);
        let Some(result_group) = current_groups
            .iter()
            .find(|group| group.label == Some(label))
        else {
            return Err(structural_error(
                "missing_label",
                format!("preserved label {label} is not locatable"),
            ));
        };
        result.splice(
            result_group.start..result_group.end,
            std::iter::once(expected_group.statements[0].clone()),
        );
    }
    Ok(())
}

fn canonicalize_transformed_group(
    expected: &Stmt,
    result_group: &mut [Stmt],
    arm_tail: bool,
    label: u32,
    transformed: &HashSet<u32>,
) -> Result<(), PreservationError> {
    if let StmtKind::Let(expected_local) = &expected.kind
        && let LocalKind::InitElse(_, expected_else) = &expected_local.kind
    {
        let candidates = result_group
            .iter()
            .enumerate()
            .filter(|(_, statement)| {
                matches!(
                    statement.kind,
                    StmtKind::Let(box Local {
                        kind: LocalKind::InitElse(..),
                        ..
                    })
                )
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if candidates.len() != 1 {
            return Err(structural_error(
                if candidates.is_empty() {
                    "missing_control_root"
                } else {
                    "multiple_control_roots"
                },
                format!("label {label} must contain exactly one let-else structural anchor"),
            ));
        }
        let scope = result_group
            .iter()
            .flat_map(statement_labels)
            .collect::<HashSet<_>>();
        let StmtKind::Let(result_local) = &mut result_group[candidates[0]].kind else {
            unreachable!()
        };
        let LocalKind::InitElse(_, result_else) = &mut result_local.kind else { unreachable!() };
        return canonicalize_nested_statement_list(
            &expected_else.stmts,
            &mut result_else.stmts,
            false,
            transformed,
            &scope,
        );
    }

    let Some(expected_control) = control_root(expected, arm_tail) else {
        return Ok(());
    };
    let candidates = result_group
        .iter()
        .enumerate()
        .filter_map(|(index, statement)| {
            control_root(statement, arm_tail).map(|root| (index, root))
        })
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return Err(structural_error(
            "missing_control_root",
            format!(
                "label {label} must contain exactly one {} structural anchor",
                expected_control.kind.name()
            ),
        ));
    }
    if candidates.len() > 1 {
        return Err(structural_error(
            "multiple_control_roots",
            format!("label {label} contains multiple control structural anchors"),
        ));
    }
    let (index, observed) = &candidates[0];
    if observed.role != expected_control.role {
        return Err(structural_error(
            "control_role_mismatch",
            format!(
                "label {label} expected {} but observed {}",
                expected_control.role.name(),
                observed.role.name()
            ),
        ));
    }
    if observed.kind != expected_control.kind {
        return Err(structural_error(
            "control_kind_mismatch",
            format!(
                "label {label} expected {} but observed {}",
                expected_control.kind.name(),
                observed.kind.name()
            ),
        ));
    }
    let result_control =
        control_root_mut(&mut result_group[*index], arm_tail).expect("candidate still exists");
    canonicalize_control(
        expected_control.expression,
        result_control.expression,
        label,
        transformed,
    )
}

fn canonicalize_control(
    expected: &Expr,
    result: &mut Expr,
    label: u32,
    transformed: &HashSet<u32>,
) -> Result<(), PreservationError> {
    let scope = expression_labels(result);
    match (&expected.kind, &mut result.kind) {
        (
            ExprKind::If(_, expected_then, expected_else),
            ExprKind::If(_, result_then, result_else),
        ) => {
            canonicalize_nested_statement_list(
                &expected_then.stmts,
                &mut result_then.stmts,
                false,
                transformed,
                &scope,
            )?;
            canonicalize_else(
                expected_else.as_deref(),
                result_else.as_deref_mut(),
                label,
                transformed,
                &scope,
            )
        }
        (ExprKind::While(_, expected_body, _), ExprKind::While(_, result_body, _))
        | (ExprKind::Loop(expected_body, ..), ExprKind::Loop(result_body, ..))
        | (ExprKind::Block(expected_body, ..), ExprKind::Block(result_body, ..)) => {
            canonicalize_nested_statement_list(
                &expected_body.stmts,
                &mut result_body.stmts,
                false,
                transformed,
                &scope,
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
        ) => canonicalize_nested_statement_list(
            &expected_body.stmts,
            &mut result_body.stmts,
            false,
            transformed,
            &scope,
        ),
        (ExprKind::Match(_, expected_arms, _), ExprKind::Match(_, result_arms, _)) => {
            if expected_arms.len() != result_arms.len() {
                return Err(structural_error(
                    "match_arm_shape_mismatch",
                    format!(
                        "label {label} expected {} match arms but observed {}",
                        expected_arms.len(),
                        result_arms.len()
                    ),
                ));
            }
            for (index, (expected_arm, result_arm)) in
                expected_arms.iter().zip(result_arms).enumerate()
            {
                if expected_arm.guard.is_some() != result_arm.guard.is_some() {
                    return Err(structural_error(
                        "match_guard_mismatch",
                        format!("label {label} match arm {index} changed guard presence"),
                    ));
                }
                let (Some(expected_body), Some(result_body)) =
                    (&expected_arm.body, &mut result_arm.body)
                else {
                    return Err(structural_error(
                        "match_arm_shape_mismatch",
                        format!("label {label} match arm {index} lost its block body"),
                    ));
                };
                let (ExprKind::Block(expected_block, _), ExprKind::Block(result_block, _)) =
                    (&expected_body.kind, &mut result_body.kind)
                else {
                    return Err(structural_error(
                        "match_arm_shape_mismatch",
                        format!("label {label} match arm {index} must retain its block body"),
                    ));
                };
                canonicalize_nested_statement_list(
                    &expected_block.stmts,
                    &mut result_block.stmts,
                    true,
                    transformed,
                    &scope,
                )?;
            }
            Ok(())
        }
        _ => Err(structural_error(
            "control_kind_mismatch",
            format!("label {label} changed its control shape"),
        )),
    }
}

fn canonicalize_else(
    expected: Option<&Expr>,
    result: Option<&mut Expr>,
    label: u32,
    transformed: &HashSet<u32>,
    scope: &HashSet<u32>,
) -> Result<(), PreservationError> {
    match (expected, result) {
        (None, None) => Ok(()),
        (Some(expected), Some(result)) => {
            let same_control_kind =
                expression_control_kind(expected) == expression_control_kind(result);
            match (&expected.kind, &mut result.kind) {
                (ExprKind::Block(expected, _), ExprKind::Block(result, _)) => {
                    canonicalize_nested_statement_list(
                        &expected.stmts,
                        &mut result.stmts,
                        false,
                        transformed,
                        scope,
                    )
                }
                (
                    ExprKind::If(_, expected_then, expected_else),
                    ExprKind::If(_, result_then, result_else),
                ) if same_control_kind => {
                    canonicalize_nested_statement_list(
                        &expected_then.stmts,
                        &mut result_then.stmts,
                        false,
                        transformed,
                        scope,
                    )?;
                    canonicalize_else(
                        expected_else.as_deref(),
                        result_else.as_deref_mut(),
                        label,
                        transformed,
                        scope,
                    )
                }
                _ => Err(structural_error(
                    "branch_shape_mismatch",
                    format!("label {label} changed its recursive else-if shape"),
                )),
            }
        }
        _ => Err(structural_error(
            "branch_shape_mismatch",
            format!("label {label} changed the existence of an else branch"),
        )),
    }
}

fn canonicalize_nested_statement_list(
    expected: &[Stmt],
    result: &mut ThinVec<Stmt>,
    arm_tail: bool,
    transformed: &HashSet<u32>,
    scope: &HashSet<u32>,
) -> Result<(), PreservationError> {
    let local_labels = groups(result)
        .into_iter()
        .filter_map(|group| group.label)
        .collect::<HashSet<_>>();
    match canonicalize_statement_list(expected, result, arm_tail, transformed) {
        Err(error) if matches!(error.code, "missing_label" | "label_order_mismatch") => {
            let misplaced = groups(expected).into_iter().find_map(|group| {
                let label = group.label?;
                (!local_labels.contains(&label) && scope.contains(&label)).then_some(label)
            });
            if let Some(label) = misplaced {
                Err(structural_error(
                    "descendant_location_mismatch",
                    format!("label {label} occurs outside its expected control branch or arm"),
                ))
            } else {
                Err(error)
            }
        }
        result => result,
    }
}

fn expression_labels(expression: &Expr) -> HashSet<u32> {
    struct Collector(HashSet<u32>);

    impl<'ast> Visitor<'ast> for Collector {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if let Some(label) = statement_label(statement) {
                self.0.insert(label);
            }
            visit::walk_stmt(self, statement);
        }
    }

    let mut collector = Collector(HashSet::new());
    collector.visit_expr(expression);
    collector.0
}

fn statement_labels(statement: &Stmt) -> HashSet<u32> {
    struct Collector(HashSet<u32>);

    impl<'ast> Visitor<'ast> for Collector {
        fn visit_stmt(&mut self, statement: &'ast Stmt) {
            if let Some(label) = statement_label(statement) {
                self.0.insert(label);
            }
            visit::walk_stmt(self, statement);
        }
    }

    let mut collector = Collector(HashSet::new());
    collector.visit_stmt(statement);
    collector.0
}

struct Group {
    label: Option<u32>,
    start: usize,
    end: usize,
    malformed: bool,
    statements: Vec<Stmt>,
}

fn groups(statements: &[Stmt]) -> Vec<Group> {
    let mut output: Vec<Group> = vec![];
    for (index, statement) in statements.iter().enumerate() {
        let label = statement_label(statement);
        if label.is_some() && output.last().is_some_and(|group| group.label == label) {
            let group = output.last_mut().unwrap();
            group.end = index + 1;
            group.statements.push(statement.clone());
        } else {
            output.push(Group {
                label,
                start: index,
                end: index + 1,
                malformed: statement_has_malformed_label(statement),
                statements: vec![statement.clone()],
            });
        }
    }
    output
}

pub(crate) fn canonical_statement_group(item: &Item, target: u32) -> Option<Vec<Stmt>> {
    struct Collector {
        target: u32,
        statements: Option<Vec<Stmt>>,
    }

    impl<'ast> Visitor<'ast> for Collector {
        fn visit_block(&mut self, block: &'ast rustc_ast::Block) {
            if self.statements.is_some() {
                return;
            }
            if let Some(group) = groups(&block.stmts)
                .into_iter()
                .find(|group| group.label == Some(self.target))
            {
                self.statements = Some(group.statements);
                return;
            }
            visit::walk_block(self, block);
        }
    }

    let ItemKind::Fn(box function) = &item.kind else {
        return None;
    };
    let mut collector = Collector {
        target,
        statements: None,
    };
    collector.visit_block(function.body.as_ref()?);
    collector.statements
}

fn statement_label(statement: &Stmt) -> Option<u32> {
    effective_statement_attributes(statement)
        .iter()
        .find_map(|attribute| parse_label_attribute(attribute).ok().flatten())
}

fn statement_has_malformed_label(statement: &Stmt) -> bool {
    effective_statement_attributes(statement)
        .iter()
        .any(|attribute| parse_label_attribute(attribute).is_err())
}

fn effective_statement_attributes(statement: &Stmt) -> &[Attribute] {
    match &statement.kind {
        StmtKind::Expr(expression) | StmtKind::Semi(expression) => {
            leading_expression_attributes(expression)
        }
        StmtKind::Let(local) => &local.attrs,
        StmtKind::Item(item) => &item.attrs,
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

fn parse_label_attribute(attribute: &Attribute) -> Result<Option<u32>, ()> {
    let AttrKind::Normal(normal) = &attribute.kind else {
        return Ok(None);
    };
    let segments = &normal.item.path.segments;
    if segments
        .last()
        .is_none_or(|segment| segment.ident.name.as_str() != "proctor")
    {
        return Ok(None);
    }
    if segments.len() != 1 {
        return Err(());
    }
    let rendered = pprust::attribute_to_string(attribute);
    let Some(argument) = rendered
        .strip_prefix("#[proctor(")
        .and_then(|value| value.strip_suffix(")]"))
    else {
        return Err(());
    };
    if argument.is_empty()
        || (argument != "0"
            && (argument.starts_with('0') || !argument.bytes().all(|byte| byte.is_ascii_digit())))
    {
        return Err(());
    }
    argument.parse::<u32>().map(Some).map_err(|_| ())
}
