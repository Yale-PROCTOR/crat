use super::{
    AdtKind, BinaryOperator, BindingMutability, BorrowKind, ByRefKind, DocumentError, RangeLimits,
    RawMutability, RefMutability, RuleAdtIdentity, RuleBlock, RuleDocument, RuleExpression,
    RuleIntegerMagnitude, RuleLiteral, RuleMemberIdentity, RulePattern, RuleStatement,
    RuleTypeTree, RuleValueIdentity, RuleVariable, UnaryOperator, VariableSort,
    validate_rule_document,
};

pub fn rule_document_to_markdown(document: &RuleDocument) -> Result<String, DocumentError> {
    validate_rule_document(document)?;

    let mut output = String::new();
    for rule in &document.rules {
        output.push_str("* ");
        output.push_str(&code_span(&expression_spelling(&rule.source_pattern)));
        output.push_str(" -> ");
        output.push_str(&code_span(&expression_spelling(&rule.target_pattern)));
        output.push('\n');

        for anchor in &rule.pointer_anchors {
            output.push_str("  * ");
            output.push_str(&escape_markdown_text(&variable_spelling(&anchor.id)));
            output.push_str(": ");
            output.push_str(&code_span(&type_spelling(&anchor.source_type)));
            output.push_str(" -> ");
            output.push_str(&code_span(&type_spelling(&anchor.target_type)));
            output.push('\n');
        }

        output.push_str("  * lhs: ");
        output.push_str(if rule.lhs { "true" } else { "false" });
        output.push('\n');
        output.push_str("  * ");
        output.push_str(&code_span(&type_spelling(&rule.source_type)));
        output.push_str(" (");
        output.push_str(&code_span(&type_spelling(&rule.source_adjusted_type)));
        output.push_str(") -> ");
        output.push_str(&code_span(&type_spelling(&rule.target_type)));
        output.push_str(" (");
        output.push_str(&code_span(&type_spelling(&rule.target_adjusted_type)));
        output.push_str(").\n");
    }
    Ok(output)
}

fn code_span(value: &str) -> String {
    let value = value
        .chars()
        .map(|character| {
            if character.is_control() {
                character.escape_debug().to_string()
            } else {
                character.to_string()
            }
        })
        .collect::<String>();
    let longest_run = value
        .split(|character| character != '`')
        .map(str::len)
        .max()
        .unwrap_or(0);
    let delimiter = "`".repeat(longest_run + 1);
    if value.starts_with(['`', ' ']) || value.ends_with(['`', ' ']) {
        format!("{delimiter} {value} {delimiter}")
    } else {
        format!("{delimiter}{value}{delimiter}")
    }
}

fn escape_markdown_text(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

fn sort_prefix(sort: VariableSort) -> &'static str {
    match sort {
        VariableSort::Anchor => "A",
        VariableSort::Binding => "B",
        VariableSort::Function => "Fn",
        VariableSort::Struct => "S",
        VariableSort::Enum => "En",
        VariableSort::Union => "U",
        VariableSort::Field => "F",
        VariableSort::Variant => "V",
        VariableSort::Constant => "C",
        VariableSort::Static => "St",
        VariableSort::Method => "M",
        VariableSort::Expression => "E",
        VariableSort::IntegerMagnitude => "I",
    }
}

fn variable_parts_spelling(sort: VariableSort, index: u64) -> String {
    format!("<{}{index}>", sort_prefix(sort))
}

fn variable_spelling(variable: &RuleVariable) -> String {
    variable_parts_spelling(variable.sort(), variable.index())
}

fn external_path_spelling(crate_name: &str, path: &[String]) -> String {
    format!("{crate_name}::{}", path.join("::"))
}

fn adt_spelling(identity: &RuleAdtIdentity) -> String {
    match identity {
        RuleAdtIdentity::Variable { sort, index } => variable_parts_spelling(*sort, *index),
        RuleAdtIdentity::External { crate_name, path } => external_path_spelling(crate_name, path),
    }
}

fn member_spelling(identity: &RuleMemberIdentity) -> String {
    match identity {
        RuleMemberIdentity::External { path, .. } => path.last().unwrap().clone(),
        RuleMemberIdentity::Local { id, .. } => variable_spelling(id),
    }
}

fn value_spelling(identity: &RuleValueIdentity) -> String {
    match identity {
        RuleValueIdentity::Variable { sort, index } => variable_parts_spelling(*sort, *index),
        RuleValueIdentity::External { crate_name, path } => {
            external_path_spelling(crate_name, path)
        }
        RuleValueIdentity::ForeignFunction { symbol }
        | RuleValueIdentity::ForeignStatic { symbol } => symbol.clone(),
        RuleValueIdentity::Constructor { adt, variant } => match variant {
            Some(variant) => format!("{}::{}", adt_spelling(adt), member_spelling(variant)),
            None => adt_spelling(adt),
        },
    }
}

fn method_spelling(identity: &RuleValueIdentity) -> String {
    match identity {
        RuleValueIdentity::External { path, .. } => path.last().unwrap().clone(),
        RuleValueIdentity::Constructor {
            variant: Some(variant),
            ..
        } => member_spelling(variant),
        RuleValueIdentity::Constructor { adt, variant: None } => {
            adt_spelling(adt).rsplit("::").next().unwrap().to_owned()
        }
        RuleValueIdentity::Variable { sort, index } => variable_parts_spelling(*sort, *index),
        RuleValueIdentity::ForeignFunction { symbol }
        | RuleValueIdentity::ForeignStatic { symbol } => symbol.clone(),
    }
}

fn type_spelling(ty: &RuleTypeTree) -> String {
    match ty {
        RuleTypeTree::Primitive { name } if name == "never" => "!".to_owned(),
        RuleTypeTree::Primitive { name } => name.clone(),
        RuleTypeTree::Slice { element } => format!("[{}]", type_spelling(element)),
        RuleTypeTree::Array { element, length } => {
            format!("[{}; {length}]", type_spelling(element))
        }
        RuleTypeTree::RawPointer {
            mutability,
            pointee,
        } => format!(
            "*{} {}",
            match mutability {
                RawMutability::Const => "const",
                RawMutability::Mut => "mut",
            },
            type_spelling(pointee)
        ),
        RuleTypeTree::Reference {
            mutability,
            pointee,
        } => format!(
            "&{}{}",
            match mutability {
                RefMutability::Shared => "",
                RefMutability::Mutable => "mut ",
            },
            type_spelling(pointee)
        ),
        RuleTypeTree::Tuple { elements } => {
            tuple_spelling(&elements.iter().map(type_spelling).collect::<Vec<_>>())
        }
        RuleTypeTree::Adt {
            adt_kind,
            identity,
            arguments,
        } => {
            let identity = match adt_kind {
                AdtKind::Struct | AdtKind::Enum | AdtKind::Union => adt_spelling(identity),
            };
            if arguments.is_empty() {
                identity
            } else {
                format!(
                    "{identity}<{}>",
                    arguments
                        .iter()
                        .map(type_spelling)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

fn tuple_spelling(elements: &[String]) -> String {
    match elements {
        [element] => format!("({element},)"),
        _ => format!("({})", elements.join(", ")),
    }
}

struct SpelledExpression {
    precedence: u8,
    text: String,
}

impl SpelledExpression {
    fn new(precedence: u8, text: String) -> Self {
        Self { precedence, text }
    }

    fn at_least(self, precedence: u8) -> String {
        if self.precedence < precedence {
            format!("({})", self.text)
        } else {
            self.text
        }
    }

    fn above(self, precedence: u8) -> String {
        if self.precedence <= precedence {
            format!("({})", self.text)
        } else {
            self.text
        }
    }
}

fn binary_spelling(operator: BinaryOperator) -> (&'static str, u8) {
    match operator {
        BinaryOperator::Or => ("||", 3),
        BinaryOperator::And => ("&&", 4),
        BinaryOperator::Equal => ("==", 5),
        BinaryOperator::NotEqual => ("!=", 5),
        BinaryOperator::Less => ("<", 5),
        BinaryOperator::LessEqual => ("<=", 5),
        BinaryOperator::Greater => (">", 5),
        BinaryOperator::GreaterEqual => (">=", 5),
        BinaryOperator::BitOr => ("|", 6),
        BinaryOperator::BitXor => ("^", 7),
        BinaryOperator::BitAnd => ("&", 8),
        BinaryOperator::ShiftLeft => ("<<", 9),
        BinaryOperator::ShiftRight => (">>", 9),
        BinaryOperator::Add => ("+", 10),
        BinaryOperator::Subtract => ("-", 10),
        BinaryOperator::Multiply => ("*", 11),
        BinaryOperator::Divide => ("/", 11),
        BinaryOperator::Remainder => ("%", 11),
    }
}

fn byte_literal_contents(value: &[u8]) -> String {
    value
        .iter()
        .map(|byte| match *byte {
            b'\n' => "\\n".to_owned(),
            b'\r' => "\\r".to_owned(),
            b'\t' => "\\t".to_owned(),
            b'\\' => "\\\\".to_owned(),
            b'"' => "\\\"".to_owned(),
            0x20..=0x7e => char::from(*byte).to_string(),
            _ => format!("\\x{byte:02x}"),
        })
        .collect()
}

fn literal_spelling(literal: &RuleLiteral) -> String {
    match literal {
        RuleLiteral::Bool { value } => value.to_string(),
        RuleLiteral::Char { value } => format!("'{}'", value.escape_default()),
        RuleLiteral::Byte { value } => format!("{value}u8"),
        RuleLiteral::String { value } => format!("{value:?}"),
        RuleLiteral::ByteString { value } => format!("b\"{}\"", byte_literal_contents(value)),
        RuleLiteral::CString { value } => format!("c\"{}\"", byte_literal_contents(value)),
        RuleLiteral::Integer { value, ty } => {
            let value = match value {
                RuleIntegerMagnitude::Fixed(value) => value.clone(),
                RuleIntegerMagnitude::Variable(variable) => variable_spelling(variable),
            };
            format!("{value}{ty}")
        }
        RuleLiteral::Float { bits, ty } => format!("{ty}::from_bits(0x{bits})"),
    }
}

fn block_spelling(block: &RuleBlock) -> String {
    if block.statements.is_empty() {
        "{}".to_owned()
    } else {
        format!(
            "{{ {} }}",
            block
                .statements
                .iter()
                .map(statement_spelling)
                .collect::<Vec<_>>()
                .join(" ")
        )
    }
}

fn pattern_spelling(pattern: &RulePattern) -> String {
    match pattern {
        RulePattern::Binding {
            id,
            mutability,
            by_ref,
        } => {
            let prefix = match by_ref {
                ByRefKind::No => match mutability {
                    BindingMutability::Immutable => "",
                    BindingMutability::Mutable => "mut ",
                },
                ByRefKind::Shared => "ref ",
                ByRefKind::Mutable => "ref mut ",
            };
            format!("{prefix}{}", variable_spelling(id))
        }
        RulePattern::Wildcard => "_".to_owned(),
    }
}

fn statement_spelling(statement: &RuleStatement) -> String {
    match statement {
        RuleStatement::Let {
            pattern,
            ty,
            initializer,
        } => format!(
            "let {}{}{};",
            pattern_spelling(pattern),
            ty.as_ref()
                .map(|ty| format!(": {}", type_spelling(ty)))
                .unwrap_or_default(),
            initializer
                .as_ref()
                .map(|value| format!(" = {}", expression_spelling(value)))
                .unwrap_or_default()
        ),
        RuleStatement::Expression {
            expression,
            semicolon,
        } => format!(
            "{}{}",
            expression_spelling(expression),
            if *semicolon { ";" } else { "" }
        ),
    }
}

fn expression_spelling(expression: &RuleExpression) -> String {
    spelled_expression(expression).text
}

fn condition_spelling(expression: &RuleExpression) -> String {
    let spelling = spelled_expression(expression).text;
    if matches!(expression, RuleExpression::Struct { .. }) {
        format!("({spelling})")
    } else {
        spelling
    }
}

fn spelled_expression(expression: &RuleExpression) -> SpelledExpression {
    let recurse = spelled_expression;
    match expression {
        RuleExpression::Variable { sort, index } => {
            SpelledExpression::new(15, variable_parts_spelling(*sort, *index))
        }
        RuleExpression::Array { elements } => SpelledExpression::new(
            15,
            format!(
                "[{}]",
                elements
                    .iter()
                    .map(expression_spelling)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ),
        RuleExpression::Call { callee, arguments } => SpelledExpression::new(
            14,
            format!(
                "{}({})",
                recurse(callee).at_least(14),
                arguments
                    .iter()
                    .map(expression_spelling)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ),
        RuleExpression::MethodCall {
            receiver,
            method,
            arguments,
        } => SpelledExpression::new(
            14,
            format!(
                "{}.{}({})",
                recurse(receiver).at_least(14),
                method_spelling(method),
                arguments
                    .iter()
                    .map(expression_spelling)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        ),
        RuleExpression::Tuple { elements } => SpelledExpression::new(
            15,
            tuple_spelling(&elements.iter().map(expression_spelling).collect::<Vec<_>>()),
        ),
        RuleExpression::Binary {
            operator,
            left,
            right,
        } => {
            let (operator, precedence) = binary_spelling(*operator);
            SpelledExpression::new(
                precedence,
                format!(
                    "{} {operator} {}",
                    recurse(left).above(precedence),
                    recurse(right).above(precedence)
                ),
            )
        }
        RuleExpression::Unary { operator, operand } => SpelledExpression::new(
            13,
            format!(
                "{}{}",
                match operator {
                    UnaryOperator::Deref => "*",
                    UnaryOperator::Not => "!",
                    UnaryOperator::Negate => "-",
                },
                recurse(operand).at_least(13)
            ),
        ),
        RuleExpression::Literal { value } => SpelledExpression::new(15, literal_spelling(value)),
        RuleExpression::Cast { expression, ty } => SpelledExpression::new(
            12,
            format!("{} as {}", recurse(expression).above(12), type_spelling(ty)),
        ),
        RuleExpression::If {
            condition,
            then,
            else_expression,
        } => SpelledExpression::new(
            0,
            format!(
                "if {} {}{}",
                condition_spelling(condition),
                block_spelling(then),
                else_expression
                    .as_ref()
                    .map(|value| format!(" else {}", expression_spelling(value)))
                    .unwrap_or_default()
            ),
        ),
        RuleExpression::While { condition, body } => SpelledExpression::new(
            0,
            format!(
                "while {} {}",
                condition_spelling(condition),
                block_spelling(body)
            ),
        ),
        RuleExpression::Loop { body } => {
            SpelledExpression::new(0, format!("loop {}", block_spelling(body)))
        }
        RuleExpression::Assign { left, right } => SpelledExpression::new(
            1,
            format!(
                "{} = {}",
                recurse(left).above(1),
                recurse(right).at_least(1)
            ),
        ),
        RuleExpression::AssignOp {
            operator,
            left,
            right,
        } => SpelledExpression::new(
            1,
            format!(
                "{} {}= {}",
                recurse(left).above(1),
                binary_spelling(*operator).0,
                recurse(right).at_least(1)
            ),
        ),
        RuleExpression::Field { base, field } => SpelledExpression::new(
            14,
            format!("{}.{}", recurse(base).at_least(14), member_spelling(field)),
        ),
        RuleExpression::Index { base, index } => SpelledExpression::new(
            14,
            format!(
                "{}[{}]",
                recurse(base).at_least(14),
                expression_spelling(index)
            ),
        ),
        RuleExpression::Range { start, end, limits } => SpelledExpression::new(
            2,
            format!(
                "{}{}{}",
                start
                    .as_ref()
                    .map(|value| recurse(value).above(2))
                    .unwrap_or_default(),
                match limits {
                    RangeLimits::HalfOpen => "..",
                    RangeLimits::Closed => "..=",
                },
                end.as_ref()
                    .map(|value| recurse(value).above(2))
                    .unwrap_or_default()
            ),
        ),
        RuleExpression::Path { value } => SpelledExpression::new(15, value_spelling(value)),
        RuleExpression::AddressOf {
            borrow,
            mutability,
            expression,
        } => SpelledExpression::new(
            13,
            format!(
                "&{}{}{}",
                match borrow {
                    BorrowKind::Reference => "",
                    BorrowKind::Raw => "raw ",
                },
                match (borrow, mutability) {
                    (BorrowKind::Raw, RawMutability::Const) => "const ",
                    (_, RawMutability::Mut) => "mut ",
                    _ => "",
                },
                recurse(expression).at_least(13)
            ),
        ),
        RuleExpression::Break { value } => SpelledExpression::new(
            0,
            format!(
                "break{}",
                value
                    .as_ref()
                    .map(|value| format!(" {}", expression_spelling(value)))
                    .unwrap_or_default()
            ),
        ),
        RuleExpression::Continue => SpelledExpression::new(0, "continue".to_owned()),
        RuleExpression::Return { value } => SpelledExpression::new(
            0,
            format!(
                "return{}",
                value
                    .as_ref()
                    .map(|value| format!(" {}", expression_spelling(value)))
                    .unwrap_or_default()
            ),
        ),
        RuleExpression::Struct {
            adt,
            variant,
            fields,
            rest,
        } => {
            let mut path = adt_spelling(adt);
            if let Some(variant) = variant {
                path.push_str("::");
                path.push_str(&member_spelling(variant));
            }
            let mut fields = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}: {}",
                        member_spelling(&field.field),
                        expression_spelling(&field.value)
                    )
                })
                .collect::<Vec<_>>();
            if let Some(rest) = rest {
                fields.push(format!("..{}", expression_spelling(rest)));
            }
            SpelledExpression::new(0, format!("{path} {{ {} }}", fields.join(", ")))
        }
        RuleExpression::Repeat { value, count } => SpelledExpression::new(
            15,
            format!(
                "[{}; {}]",
                expression_spelling(value),
                expression_spelling(count)
            ),
        ),
        RuleExpression::Block { block } => SpelledExpression::new(0, block_spelling(block)),
    }
}
