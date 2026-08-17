use super::*;
use crate::{
    AdtIdentity, BinaryOperator, BindingMutability, Block, BorrowKind, ByRefKind, Expression,
    FieldIdentity, Literal, Observation, Pattern, RangeLimits, RawMutability, Statement,
    StructField, TypeTree, UnaryOperator, ValueIdentity,
};

fn primitive() -> TypeTree {
    TypeTree::Primitive { name: "i32".into() }
}

fn observation(source_expression: Expression, target_expression: Expression) -> Observation {
    Observation {
        source_expression,
        target_expression,
        pointer_anchors: vec![],
        lhs: false,
        source_type: primitive(),
        source_adjusted_type: primitive(),
        target_type: primitive(),
        target_adjusted_type: primitive(),
    }
}

fn string(value: &str) -> Expression {
    Expression::Literal {
        value: Literal::String {
            value: value.into(),
        },
    }
}

fn byte_string(value: &[u8]) -> Expression {
    Expression::Literal {
        value: Literal::ByteString {
            value: value.to_vec(),
        },
    }
}

fn c_string(value: &[u8]) -> Expression {
    Expression::Literal {
        value: Literal::CString {
            value: value.to_vec(),
        },
    }
}

fn integer(value: &str) -> Expression {
    Expression::Literal {
        value: Literal::Integer {
            value: value.into(),
            ty: "i32".into(),
        },
    }
}

fn boolean(value: bool) -> Expression {
    Expression::Literal {
        value: Literal::Bool { value },
    }
}

fn binding(id: &str) -> Expression {
    Expression::Path {
        value: ValueIdentity::Binding { id: id.into() },
    }
}

fn external(name: &str) -> ValueIdentity {
    ValueIdentity::External {
        crate_name: "fixture".into(),
        path: vec![name.into()],
    }
}

fn call(callee: ValueIdentity, arguments: Vec<Expression>) -> Expression {
    Expression::Call {
        callee: Box::new(Expression::Path { value: callee }),
        arguments,
    }
}

fn source_scan(symbol: &str, arguments: Vec<Expression>) -> Expression {
    call(
        ValueIdentity::ForeignFunction {
            symbol: symbol.into(),
        },
        arguments,
    )
}

fn target_scan(name: &str, arguments: Vec<Expression>) -> Expression {
    call(
        ValueIdentity::External {
            crate_name: "xj_scanf".into(),
            path: vec!["legacy".into(), name.into()],
        },
        arguments,
    )
}

fn plain_source(format: &str) -> Expression {
    source_scan("scanf", vec![string(format), binding("<id0>")])
}

fn plain_target(format: &str) -> Expression {
    target_scan("scanf", vec![string(format), binding("<id0>")])
}

fn raw_pointer(name: &str, mutability: RawMutability) -> TypeTree {
    TypeTree::RawPointer {
        mutability,
        pointee: Box::new(TypeTree::Primitive { name: name.into() }),
    }
}

fn complete_source_scan(format: &[u8]) -> Expression {
    source_scan(
        "scanf",
        vec![
            Expression::Cast {
                expression: Box::new(Expression::Cast {
                    expression: Box::new(byte_string(format)),
                    ty: raw_pointer("u8", RawMutability::Const),
                }),
                ty: raw_pointer("i8", RawMutability::Const),
            },
            Expression::Cast {
                expression: Box::new(Expression::AddressOf {
                    borrow: BorrowKind::Reference,
                    mutability: RawMutability::Mut,
                    expression: Box::new(binding("<id0>")),
                }),
                ty: raw_pointer("i32", RawMutability::Mut),
            },
        ],
    )
}

fn complete_target_scan(format: &str) -> Expression {
    target_scan(
        "scanf",
        vec![
            string(format),
            Expression::AddressOf {
                borrow: BorrowKind::Reference,
                mutability: RawMutability::Mut,
                expression: Box::new(Expression::Array {
                    elements: vec![Expression::AddressOf {
                        borrow: BorrowKind::Reference,
                        mutability: RawMutability::Mut,
                        expression: Box::new(binding("<id0>")),
                    }],
                }),
            },
        ],
    )
}

fn assert_rejection(result: PairSynthesis, expected: PairRejection) {
    assert_eq!(result.rejection, Some(expected));
    assert!(result.rule.is_none());
    assert!(
        result
            .substitutions
            .keys()
            .all(|(sort, _)| *sort != VariableSort::Expression)
    );
}

#[test]
fn complete_scan_observations_synthesize_exact_anchorless_patterns() {
    let scan = observation(complete_source_scan(b"%d\0"), complete_target_scan("%d"));
    let result = synthesize_observation_pair(&scan, &scan);
    assert!(result.rejection.is_none());
    assert_eq!(
        result.substitutions.keys().copied().collect::<Vec<_>>(),
        [(VariableSort::Binding, 0)]
    );
    let rule = result.rule.unwrap();
    assert!(rule.pointer_anchors.is_empty());
    let value = serde_json::to_value(&rule).unwrap();
    assert_eq!(
        value["source_pattern"]["arguments"][0]["expression"]["expression"]["value"],
        serde_json::json!({"kind":"byte_string","value":[37,100,0]})
    );
    assert_eq!(
        value["target_pattern"]["arguments"][0]["value"],
        serde_json::json!({"kind":"string","value":"%d"})
    );
    assert_eq!(
        value["source_pattern"]["arguments"][1]["expression"]["expression"]["value"],
        serde_json::json!({"kind":"variable","sort":"binding","index":0})
    );
    assert_eq!(
        value["target_pattern"]["arguments"][1]["expression"]["elements"][0]["expression"]["value"],
        serde_json::json!({"kind":"variable","sort":"binding","index":0})
    );
    let serialized = value.to_string();
    assert!(!serialized.contains("\"sort\":\"anchor\""));
    assert!(!serialized.contains("\"sort\":\"expression\""));
    assert!(!serialized.contains("\"sort\":\"integer_magnitude\""));

    assert_rejection(
        synthesize_observation_pair(
            &scan,
            &observation(complete_source_scan(b"%u\0"), complete_target_scan("%d")),
        ),
        PairRejection::Source,
    );
    assert_rejection(
        synthesize_observation_pair(
            &scan,
            &observation(complete_source_scan(b"%d\0"), complete_target_scan("%u")),
        ),
        PairRejection::TargetLookup,
    );
}

#[test]
fn every_string_like_format_kind_is_rigid_but_cross_side_kinds_are_independent() {
    let formats = [string("%d"), byte_string(b"%d"), c_string(b"%d")];
    let changes = [string("%u"), byte_string(b"%u"), c_string(b"%u")];
    for (format, change) in formats.into_iter().zip(changes) {
        let base = observation(
            source_scan("scanf", vec![format.clone()]),
            target_scan("scanf", vec![format.clone()]),
        );
        assert!(synthesize_observation_pair(&base, &base).rule.is_some());
        assert_rejection(
            synthesize_observation_pair(
                &base,
                &observation(
                    source_scan("scanf", vec![change]),
                    target_scan("scanf", vec![format]),
                ),
            ),
            PairRejection::Source,
        );
    }

    let cross_side = observation(
        source_scan("scanf", vec![byte_string(b"%d\0")]),
        target_scan("scanf", vec![string("%d")]),
    );
    assert!(
        synthesize_observation_pair(&cross_side, &cross_side)
            .rule
            .is_some()
    );
}

#[test]
fn scan_input_stream_and_other_arguments_reuse_ordinary_disagreements() {
    let source = |input: &str, format: Expression| {
        source_scan("sscanf", vec![string(input), format, binding("<id0>")])
    };
    let target = |input: &str, format: Expression| {
        target_scan("bscanf", vec![string(input), format, binding("<id0>")])
    };
    for (left, right) in [
        (string("%d"), string("%d")),
        (byte_string(b"%d"), byte_string(b"%d")),
        (c_string(b"%d"), c_string(b"%d")),
    ] {
        let result = synthesize_observation_pair(
            &observation(source("left", left.clone()), target("left", left)),
            &observation(source("right", right.clone()), target("right", right)),
        );
        assert!(result.rejection.is_none());
        let rule = result.rule.unwrap();
        let value = serde_json::to_value(rule).unwrap();
        assert_eq!(
            value["source_pattern"]["arguments"][0],
            serde_json::json!({"kind":"variable","sort":"expression","index":0})
        );
        assert_eq!(
            value["target_pattern"]["arguments"][0],
            serde_json::json!({"kind":"variable","sort":"expression","index":0})
        );
    }

    assert!(
        synthesize_observation_pair(
            &observation(
                call(external("log"), vec![byte_string(b"left")]),
                call(external("consume"), vec![byte_string(b"left")]),
            ),
            &observation(
                call(external("log"), vec![byte_string(b"right")]),
                call(external("consume"), vec![byte_string(b"right")]),
            ),
        )
        .rule
        .is_some()
    );
    assert!(
        synthesize_observation_pair(
            &observation(
                call(external("log"), vec![c_string(b"left")]),
                call(external("consume"), vec![c_string(b"left")]),
            ),
            &observation(
                call(external("log"), vec![c_string(b"right")]),
                call(external("consume"), vec![c_string(b"right")]),
            ),
        )
        .rule
        .is_some()
    );
}

#[test]
fn scan_families_protect_only_their_resolved_format_positions() {
    for (symbol, format_index) in [("scanf", 0), ("fscanf", 1), ("sscanf", 1)] {
        let mut left = vec![string("input"), string("%d"), binding("<id0>")];
        if format_index == 0 {
            left = vec![string("%d"), string("input"), binding("<id0>")];
        }
        let mut format_change = left.clone();
        format_change[format_index] = string("%u");
        let target = plain_target("%d");
        assert_rejection(
            synthesize_observation_pair(
                &observation(source_scan(symbol, left.clone()), target.clone()),
                &observation(source_scan(symbol, format_change), target.clone()),
            ),
            PairRejection::Source,
        );

        let unprotected_index = if format_index == 0 { 1 } else { 0 };
        let mut unprotected_change = left.clone();
        unprotected_change[unprotected_index] = string("other");
        assert!(
            synthesize_observation_pair(
                &observation(
                    source_scan(symbol, left.clone()),
                    call(external("consume"), left),
                ),
                &observation(
                    source_scan(symbol, unprotected_change.clone()),
                    call(external("consume"), unprotected_change),
                ),
            )
            .rule
            .is_some()
        );
    }

    for (name, format_index) in [("scanf", 0), ("brscanf", 1), ("bscanf", 1)] {
        let mut left = vec![string("input"), string("%d"), binding("<id0>")];
        if format_index == 0 {
            left = vec![string("%d"), string("input"), binding("<id0>")];
        }
        let mut format_change = left.clone();
        format_change[format_index] = string("%u");
        let source = plain_source("%d");
        assert_rejection(
            synthesize_observation_pair(
                &observation(source.clone(), target_scan(name, left.clone())),
                &observation(source.clone(), target_scan(name, format_change)),
            ),
            PairRejection::TargetLookup,
        );

        let unprotected_index = if format_index == 0 { 1 } else { 0 };
        let mut unprotected_change = left.clone();
        unprotected_change[unprotected_index] = string("other");
        assert!(
            synthesize_observation_pair(
                &observation(
                    call(external("prepare"), left.clone()),
                    target_scan(name, left),
                ),
                &observation(
                    call(external("prepare"), unprotected_change.clone()),
                    target_scan(name, unprotected_change),
                ),
            )
            .rule
            .is_some()
        );
    }
}

#[test]
fn scan_recognition_is_exact_and_literal_kinds_remain_semantic() {
    let target = plain_target("%d");
    for symbol in ["vscanf", "__isoc99_scanf"] {
        assert!(
            synthesize_observation_pair(
                &observation(
                    source_scan(symbol, vec![string("%d")]),
                    call(external("consume"), vec![string("%d")]),
                ),
                &observation(
                    source_scan(symbol, vec![string("%u")]),
                    call(external("consume"), vec![string("%u")]),
                ),
            )
            .rule
            .is_some()
        );
    }

    let negative_targets = [
        ValueIdentity::External {
            crate_name: "other".into(),
            path: vec!["legacy".into(), "scanf".into()],
        },
        ValueIdentity::External {
            crate_name: "xj_scanf".into(),
            path: vec!["scanf".into()],
        },
        ValueIdentity::External {
            crate_name: "xj_scanf".into(),
            path: vec!["other".into(), "scanf".into()],
        },
        ValueIdentity::External {
            crate_name: "xj_scanf".into(),
            path: vec!["legacy".into(), "sscanf".into()],
        },
        ValueIdentity::Function { id: "<fn0>".into() },
    ];
    for callee in negative_targets {
        assert!(
            synthesize_observation_pair(
                &observation(
                    call(callee.clone(), vec![string("%d")]),
                    call(callee.clone(), vec![string("%d")]),
                ),
                &observation(
                    call(callee.clone(), vec![string("%u")]),
                    call(callee.clone(), vec![string("%u")]),
                ),
            )
            .rule
            .is_some()
        );
    }

    for (left, right) in [
        (string("%d"), byte_string(b"%d")),
        (string("%d"), c_string(b"%d")),
        (byte_string(b"%d"), c_string(b"%d")),
    ] {
        assert_rejection(
            synthesize_observation_pair(
                &observation(source_scan("scanf", vec![left]), target.clone()),
                &observation(source_scan("scanf", vec![right]), target.clone()),
            ),
            PairRejection::Source,
        );
    }

    let cross_side = observation(
        source_scan("scanf", vec![byte_string(b"%d\0")]),
        target_scan("scanf", vec![string("%d")]),
    );
    assert!(
        synthesize_observation_pair(&cross_side, &cross_side)
            .rule
            .is_some()
    );
}

#[test]
fn nested_scan_calls_protect_only_their_own_format_arguments() {
    let nested = |input: &str, format: &str| {
        source_scan(
            "sscanf",
            vec![string(input), string(format), binding("<id0>")],
        )
    };
    let outer = |format: &str, nested| source_scan("scanf", vec![string(format), nested]);
    let target = plain_target("%d");
    let base = observation(outer("%d", nested("input", "%u")), target.clone());
    assert_rejection(
        synthesize_observation_pair(
            &base,
            &observation(outer("%i", nested("input", "%u")), target.clone()),
        ),
        PairRejection::Source,
    );
    assert_rejection(
        synthesize_observation_pair(
            &base,
            &observation(outer("%d", nested("input", "%x")), target.clone()),
        ),
        PairRejection::Source,
    );
    assert!(
        synthesize_observation_pair(
            &base,
            &observation(outer("%d", nested("other", "%u")), target),
        )
        .rule
        .is_some()
    );
}

#[derive(Clone, Copy, Debug)]
enum Wrapper {
    Array,
    Tuple,
    CallCallee,
    CallArgument,
    MethodReceiver,
    MethodArgument,
    BinaryLeft,
    BinaryRight,
    AssignLeft,
    AssignRight,
    AssignOpLeft,
    AssignOpRight,
    Unary,
    Cast,
    Field,
    IndexBase,
    IndexIndex,
    RangeStart,
    RangeEnd,
    IfCondition,
    IfThen,
    IfElse,
    WhileCondition,
    WhileBody,
    LoopBody,
    StructField,
    StructRest,
    Address,
    Return,
    Break,
    RepeatValue,
    RepeatCount,
    ExplicitBlock,
    BlockExpression,
    LetInitializer,
}

fn block_tail(expression: Expression) -> Block {
    Block {
        statements: vec![Statement::Expression {
            expression,
            semicolon: false,
        }],
    }
}

fn block_statement(expression: Expression) -> Block {
    Block {
        statements: vec![Statement::Expression {
            expression,
            semicolon: true,
        }],
    }
}

fn wrap(wrapper: Wrapper, expression: Expression) -> Expression {
    match wrapper {
        Wrapper::Array => Expression::Array {
            elements: vec![expression],
        },
        Wrapper::Tuple => Expression::Tuple {
            elements: vec![integer("0"), expression],
        },
        Wrapper::CallCallee => Expression::Call {
            callee: Box::new(expression),
            arguments: vec![],
        },
        Wrapper::CallArgument => call(external("keep"), vec![expression]),
        Wrapper::MethodReceiver => Expression::MethodCall {
            receiver: Box::new(expression),
            method: external("keep"),
            arguments: vec![],
        },
        Wrapper::MethodArgument => Expression::MethodCall {
            receiver: Box::new(integer("0")),
            method: external("keep"),
            arguments: vec![expression],
        },
        Wrapper::BinaryLeft => Expression::Binary {
            operator: BinaryOperator::Add,
            left: Box::new(expression),
            right: Box::new(integer("0")),
        },
        Wrapper::BinaryRight => Expression::Binary {
            operator: BinaryOperator::Add,
            left: Box::new(integer("0")),
            right: Box::new(expression),
        },
        Wrapper::AssignLeft => Expression::Assign {
            left: Box::new(expression),
            right: Box::new(integer("0")),
        },
        Wrapper::AssignRight => Expression::Assign {
            left: Box::new(binding("<id0>")),
            right: Box::new(expression),
        },
        Wrapper::AssignOpLeft => Expression::AssignOp {
            operator: BinaryOperator::Add,
            left: Box::new(expression),
            right: Box::new(integer("0")),
        },
        Wrapper::AssignOpRight => Expression::AssignOp {
            operator: BinaryOperator::Add,
            left: Box::new(binding("<id0>")),
            right: Box::new(expression),
        },
        Wrapper::Unary => Expression::Unary {
            operator: UnaryOperator::Not,
            operand: Box::new(expression),
        },
        Wrapper::Cast => Expression::Cast {
            expression: Box::new(expression),
            ty: primitive(),
        },
        Wrapper::Field => Expression::Field {
            base: Box::new(expression),
            field: FieldIdentity::External {
                crate_name: "fixture".into(),
                path: vec!["Record".into(), "field".into()],
            },
        },
        Wrapper::IndexBase => Expression::Index {
            base: Box::new(expression),
            index: Box::new(integer("0")),
        },
        Wrapper::IndexIndex => Expression::Index {
            base: Box::new(binding("<id0>")),
            index: Box::new(expression),
        },
        Wrapper::RangeStart => Expression::Range {
            start: Some(Box::new(expression)),
            end: Some(Box::new(integer("1"))),
            limits: RangeLimits::HalfOpen,
        },
        Wrapper::RangeEnd => Expression::Range {
            start: Some(Box::new(integer("0"))),
            end: Some(Box::new(expression)),
            limits: RangeLimits::HalfOpen,
        },
        Wrapper::IfCondition => Expression::If {
            condition: Box::new(expression),
            then: block_tail(integer("0")),
            else_expression: Some(Box::new(integer("1"))),
        },
        Wrapper::IfThen => Expression::If {
            condition: Box::new(boolean(true)),
            then: block_tail(expression),
            else_expression: Some(Box::new(integer("1"))),
        },
        Wrapper::IfElse => Expression::If {
            condition: Box::new(boolean(true)),
            then: block_tail(integer("0")),
            else_expression: Some(Box::new(expression)),
        },
        Wrapper::WhileCondition => Expression::While {
            condition: Box::new(expression),
            body: Block { statements: vec![] },
        },
        Wrapper::WhileBody => Expression::While {
            condition: Box::new(boolean(true)),
            body: block_statement(expression),
        },
        Wrapper::LoopBody => Expression::Loop {
            body: block_statement(expression),
        },
        Wrapper::StructField => Expression::Struct {
            adt: AdtIdentity::External {
                crate_name: "fixture".into(),
                path: vec!["Record".into()],
            },
            variant: None,
            fields: vec![StructField {
                field: FieldIdentity::External {
                    crate_name: "fixture".into(),
                    path: vec!["Record".into(), "field".into()],
                },
                value: expression,
            }],
            rest: None,
        },
        Wrapper::StructRest => Expression::Struct {
            adt: AdtIdentity::External {
                crate_name: "fixture".into(),
                path: vec!["Record".into()],
            },
            variant: None,
            fields: vec![],
            rest: Some(Box::new(expression)),
        },
        Wrapper::Address => Expression::AddressOf {
            borrow: BorrowKind::Reference,
            mutability: RawMutability::Const,
            expression: Box::new(expression),
        },
        Wrapper::Return => Expression::Return {
            value: Some(Box::new(expression)),
        },
        Wrapper::Break => Expression::Break {
            value: Some(Box::new(expression)),
        },
        Wrapper::RepeatValue => Expression::Repeat {
            value: Box::new(expression),
            count: Box::new(integer("1")),
        },
        Wrapper::RepeatCount => Expression::Repeat {
            value: Box::new(integer("0")),
            count: Box::new(expression),
        },
        Wrapper::ExplicitBlock => Expression::Block {
            block: block_statement(expression),
        },
        Wrapper::BlockExpression => Expression::Block {
            block: block_statement(expression),
        },
        Wrapper::LetInitializer => Expression::Block {
            block: Block {
                statements: vec![Statement::Let {
                    pattern: Pattern::Binding {
                        id: "<id0>".into(),
                        mutability: BindingMutability::Immutable,
                        by_ref: ByRefKind::No,
                    },
                    ty: None,
                    initializer: Some(expression),
                }],
            },
        },
    }
}

#[test]
fn rigid_rejection_reaches_every_composite_expression_route() {
    let wrappers = [
        Wrapper::Array,
        Wrapper::Tuple,
        Wrapper::CallCallee,
        Wrapper::CallArgument,
        Wrapper::MethodReceiver,
        Wrapper::MethodArgument,
        Wrapper::BinaryLeft,
        Wrapper::BinaryRight,
        Wrapper::AssignLeft,
        Wrapper::AssignRight,
        Wrapper::AssignOpLeft,
        Wrapper::AssignOpRight,
        Wrapper::Unary,
        Wrapper::Cast,
        Wrapper::Field,
        Wrapper::IndexBase,
        Wrapper::IndexIndex,
        Wrapper::RangeStart,
        Wrapper::RangeEnd,
        Wrapper::IfCondition,
        Wrapper::IfThen,
        Wrapper::IfElse,
        Wrapper::WhileCondition,
        Wrapper::WhileBody,
        Wrapper::LoopBody,
        Wrapper::StructField,
        Wrapper::StructRest,
        Wrapper::Address,
        Wrapper::Return,
        Wrapper::Break,
        Wrapper::RepeatValue,
        Wrapper::RepeatCount,
        Wrapper::ExplicitBlock,
        Wrapper::BlockExpression,
        Wrapper::LetInitializer,
    ];
    for wrapper in wrappers {
        let source_left = wrap(wrapper, plain_source("%d"));
        let target_left = wrap(wrapper, plain_target("%d"));
        assert_rejection(
            synthesize_observation_pair(
                &observation(source_left.clone(), target_left.clone()),
                &observation(wrap(wrapper, plain_source("%u")), target_left.clone()),
            ),
            PairRejection::Source,
        );
        assert_rejection(
            synthesize_observation_pair(
                &observation(source_left.clone(), target_left.clone()),
                &observation(source_left, wrap(wrapper, plain_target("%u"))),
            ),
            PairRejection::TargetLookup,
        );
    }
}

#[test]
fn one_sided_protected_topology_rejects_before_generalization() {
    let source = plain_source("%d");
    let target = plain_target("%d");
    let source_pairs = [
        (
            Expression::Array {
                elements: vec![source.clone()],
            },
            Expression::Array { elements: vec![] },
        ),
        (
            Expression::Return {
                value: Some(Box::new(source.clone())),
            },
            Expression::Return { value: None },
        ),
        (
            Expression::Break {
                value: Some(Box::new(source.clone())),
            },
            Expression::Break { value: None },
        ),
        (
            Expression::Range {
                start: Some(Box::new(source.clone())),
                end: None,
                limits: RangeLimits::HalfOpen,
            },
            Expression::Range {
                start: None,
                end: None,
                limits: RangeLimits::HalfOpen,
            },
        ),
        (
            Expression::If {
                condition: Box::new(boolean(true)),
                then: block_tail(integer("0")),
                else_expression: Some(Box::new(source.clone())),
            },
            Expression::If {
                condition: Box::new(boolean(true)),
                then: block_tail(integer("0")),
                else_expression: None,
            },
        ),
        (
            Expression::Struct {
                adt: AdtIdentity::External {
                    crate_name: "fixture".into(),
                    path: vec!["Record".into()],
                },
                variant: None,
                fields: vec![],
                rest: Some(Box::new(source.clone())),
            },
            Expression::Struct {
                adt: AdtIdentity::External {
                    crate_name: "fixture".into(),
                    path: vec!["Record".into()],
                },
                variant: None,
                fields: vec![],
                rest: None,
            },
        ),
    ];
    for (left, right) in source_pairs {
        assert_rejection(
            synthesize_observation_pair(
                &observation(left, target.clone()),
                &observation(right, target.clone()),
            ),
            PairRejection::Source,
        );
    }
}

#[test]
fn ordinary_block_generalization_and_scan_family_boundaries_remain_exact() {
    let ordinary = |callee: &str, value: Expression| Expression::Block {
        block: block_statement(call(external(callee), vec![value])),
    };
    let ordinary_result = synthesize_observation_pair(
        &observation(
            ordinary("source", integer("1")),
            ordinary("target", integer("1")),
        ),
        &observation(
            ordinary("source", boolean(true)),
            ordinary("target", boolean(true)),
        ),
    );
    assert!(ordinary_result.rejection.is_none());
    assert!(ordinary_result.rule.is_some());
    assert!(
        ordinary_result
            .substitutions
            .contains_key(&(VariableSort::Expression, 0))
    );

    for (left, right) in [
        (
            plain_source("%d"),
            source_scan("vscanf", vec![string("%d"), binding("<id0>")]),
        ),
        (
            Expression::Block {
                block: block_statement(plain_source("%d")),
            },
            Expression::Block {
                block: block_statement(source_scan("vscanf", vec![string("%d"), binding("<id0>")])),
            },
        ),
    ] {
        assert_rejection(
            synthesize_observation_pair(
                &observation(left, plain_target("%d")),
                &observation(right, plain_target("%d")),
            ),
            PairRejection::Source,
        );
    }

    let legacy_sscanf = target_scan("sscanf", vec![string("%d"), binding("<id0>")]);
    for (left, right) in [
        (plain_target("%d"), legacy_sscanf.clone()),
        (
            Expression::Block {
                block: block_statement(plain_target("%d")),
            },
            Expression::Block {
                block: block_statement(legacy_sscanf),
            },
        ),
    ] {
        assert_rejection(
            synthesize_observation_pair(
                &observation(plain_source("%d"), left),
                &observation(plain_source("%d"), right),
            ),
            PairRejection::TargetLookup,
        );
    }

    assert_rejection(
        synthesize_observation_pair(
            &observation(plain_source("%d"), plain_target("%d")),
            &observation(
                source_scan(
                    "sscanf",
                    vec![string("input"), string("%d"), binding("<id0>")],
                ),
                plain_target("%d"),
            ),
        ),
        PairRejection::Source,
    );
}

#[test]
fn protected_target_block_cannot_reuse_an_unrelated_source_disagreement() {
    let source = |ordinary: &str| Expression::Tuple {
        elements: vec![integer(ordinary), plain_source("%d")],
    };
    let target = |format: &str| Expression::Block {
        block: block_statement(plain_target(format)),
    };
    let result = synthesize_observation_pair(
        &observation(source("1"), target("%d")),
        &observation(source("2"), target("%u")),
    );
    assert_eq!(result.rejection, Some(PairRejection::TargetLookup));
    assert!(result.rule.is_none());
    let protected = [
        serde_json::to_value(string("%d")).unwrap(),
        serde_json::to_value(string("%u")).unwrap(),
        serde_json::to_value(plain_target("%d")).unwrap(),
        serde_json::to_value(plain_target("%u")).unwrap(),
        serde_json::to_value(target("%d")).unwrap(),
        serde_json::to_value(target("%u")).unwrap(),
    ];
    assert!(
        result
            .substitutions
            .values()
            .all(|(left, right)| !protected.contains(left) && !protected.contains(right))
    );
}
