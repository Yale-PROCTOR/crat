use std::collections::BTreeMap;

use serde_json::{Value, json};

use super::*;

fn primitive(name: &str) -> Value {
    json!({"kind": "primitive", "name": name})
}

fn raw_i32() -> Value {
    json!({"kind": "raw_pointer", "mutability": "const", "pointee": primitive("i32")})
}

fn ref_i32() -> Value {
    json!({"kind": "reference", "mutability": "shared", "pointee": primitive("i32")})
}

fn mut_slice_i32() -> Value {
    json!({
        "kind": "reference",
        "mutability": "mutable",
        "pointee": {"kind": "slice", "element": primitive("i32")}
    })
}

fn binding(index: usize) -> Value {
    json!({"kind": "path", "value": {"kind": "binding", "id": format!("<id{index}>")}})
}

fn external(name: &str) -> Value {
    json!({"kind": "path", "value": {"kind": "external", "crate": "fixture", "path": [name]}})
}

fn call(name: &str, arguments: Vec<Value>) -> Value {
    json!({"kind": "call", "callee": external(name), "arguments": arguments})
}

fn method(receiver: Value, crate_name: &str, path: &[&str], arguments: Vec<Value>) -> Value {
    json!({
        "kind": "method_call",
        "receiver": receiver,
        "method": {"kind": "external", "crate": crate_name, "path": path},
        "arguments": arguments
    })
}

fn offset(base: Value, amount: Value) -> Value {
    method(base, "core", &["ptr", "const_ptr", "offset"], vec![amount])
}

fn unary(operator: &str, operand: Value) -> Value {
    json!({"kind": "unary", "operator": operator, "operand": operand})
}

fn binary(operator: &str, left: Value, right: Value) -> Value {
    json!({"kind": "binary", "operator": operator, "left": left, "right": right})
}

fn integer(value: &str, ty: &str) -> Value {
    json!({"kind": "literal", "value": {"kind": "integer", "value": value, "type": ty}})
}

fn index(base: Value, index: Value) -> Value {
    json!({"kind": "index", "base": base, "index": index})
}

fn mutable_slice_from(base: Value, start: Value) -> Value {
    json!({
        "kind": "address_of",
        "borrow": "reference",
        "mutability": "mut",
        "expression": {
            "kind": "index",
            "base": base,
            "index": {"kind": "range", "start": start, "end": null, "limits": "half_open"}
        }
    })
}

fn local_adt(kind: &str, index: usize) -> Value {
    json!({"kind": "local", "id": format!("<{kind}{index}>")})
}

fn local_adt_type(kind: &str, index: usize) -> Value {
    json!({
        "kind": "adt",
        "adt_kind": kind,
        "identity": local_adt(kind, index),
        "arguments": []
    })
}

fn member(kind: &str, owner_kind: &str, owner_index: usize, index: usize) -> Value {
    json!({
        "kind": "local",
        "owner": local_adt(owner_kind, owner_index),
        "id": format!("<{kind}{index}>")
    })
}

fn field(base: Value, owner_kind: &str, owner_index: usize, field_index: usize) -> Value {
    json!({
        "kind": "field",
        "base": base,
        "field": member("field", owner_kind, owner_index, field_index)
    })
}

fn anchor(index: usize, target_type: Value) -> Value {
    json!({"id": format!("<id{index}>"), "source_type": raw_i32(), "target_type": target_type})
}

fn observation_value(
    source: Value,
    target: Value,
    anchors: Option<Vec<Value>>,
    root_types: Option<[Value; 4]>,
) -> Value {
    let [
        source_type,
        source_adjusted_type,
        target_type,
        target_adjusted_type,
    ] = root_types.unwrap_or_else(|| std::array::from_fn(|_| primitive("i32")));
    json!({
        "source_expression": source,
        "target_expression": target,
        "pointer_anchors": anchors.unwrap_or_else(|| vec![anchor(0, mut_slice_i32())]),
        "lhs": false,
        "source_type": source_type,
        "source_adjusted_type": source_adjusted_type,
        "target_type": target_type,
        "target_adjusted_type": target_adjusted_type
    })
}

fn observation(source: Value, target: Value) -> Observation {
    serde_json::from_value(observation_value(source, target, None, None)).unwrap()
}

fn with_anchor(source: Value, target: Value, anchors: Vec<Value>) -> Observation {
    serde_json::from_value(observation_value(source, target, Some(anchors), None)).unwrap()
}

fn with_context(
    source: Value,
    target: Value,
    anchors: Vec<Value>,
    root_types: [Value; 4],
) -> Observation {
    serde_json::from_value(observation_value(
        source,
        target,
        Some(anchors),
        Some(root_types),
    ))
    .unwrap()
}

fn document(observations: Vec<Observation>) -> ObservationDocument {
    ObservationDocument {
        schema_version: OBSERVATION_SCHEMA_VERSION,
        observations,
    }
}

fn synthesize(observations: Vec<Observation>) -> RuleDocument {
    synthesize_rules(&[document(observations)]).unwrap()
}

fn pair(left: &Observation, right: &Observation) -> PairSynthesis {
    synthesize_observation_pair(left, right)
}

fn serialized(document: &RuleDocument) -> String {
    rule_document_to_json(document).unwrap()
}

#[derive(Clone, Copy)]
enum ReconstructionRole {
    Ordinary,
    ValueIdentity,
    AdtIdentity,
    MemberId,
}

fn reconstruct_value(
    value: &Value,
    substitutions: &BTreeMap<(VariableSort, u64), (Value, Value)>,
    seed: usize,
    role: ReconstructionRole,
) -> Value {
    if let Some(object) = value.as_object() {
        if object.get("kind").and_then(Value::as_str) == Some("variable") {
            let variable: RuleVariable = serde_json::from_value(value.clone()).unwrap();
            let substitution = &substitutions[&(variable.sort(), variable.index())];
            let concrete = match seed {
                0 => substitution.0.clone(),
                1 => substitution.1.clone(),
                _ => panic!("reconstruction seed must be zero or one"),
            };
            return match variable.sort() {
                VariableSort::Expression | VariableSort::IntegerMagnitude => concrete,
                VariableSort::Field | VariableSort::Variant => concrete,
                VariableSort::Struct | VariableSort::Enum | VariableSort::Union
                    if matches!(role, ReconstructionRole::AdtIdentity) =>
                {
                    json!({"kind": "local", "id": concrete})
                }
                sort if matches!(role, ReconstructionRole::ValueIdentity) => {
                    let kind = if sort == VariableSort::Anchor {
                        "binding".to_owned()
                    } else {
                        serde_json::to_value(sort)
                            .unwrap()
                            .as_str()
                            .unwrap()
                            .to_owned()
                    };
                    json!({"kind": kind, "id": concrete})
                }
                _ if matches!(role, ReconstructionRole::MemberId) => concrete,
                _ => panic!("variable {variable:?} appeared in an invalid reconstruction role"),
            };
        }

        let kind = object.get("kind").and_then(Value::as_str);
        if kind == Some("path") {
            return json!({
                "kind": "path",
                "value": reconstruct_value(
                    &object["value"],
                    substitutions,
                    seed,
                    ReconstructionRole::ValueIdentity,
                )
            });
        }
        if kind == Some("constructor") {
            return json!({
                "kind": "constructor",
                "adt": reconstruct_value(
                    &object["adt"],
                    substitutions,
                    seed,
                    ReconstructionRole::AdtIdentity,
                ),
                "variant": if object["variant"].is_null() {
                    Value::Null
                } else {
                    reconstruct_value(
                        &object["variant"],
                        substitutions,
                        seed,
                        ReconstructionRole::Ordinary,
                    )
                }
            });
        }
        if kind == Some("local") && object.contains_key("owner") {
            return json!({
                "kind": "local",
                "owner": reconstruct_value(
                    &object["owner"],
                    substitutions,
                    seed,
                    ReconstructionRole::AdtIdentity,
                ),
                "id": reconstruct_value(
                    &object["id"],
                    substitutions,
                    seed,
                    ReconstructionRole::MemberId,
                )
            });
        }

        let mut result = serde_json::Map::new();
        for (key, child) in object {
            let child_role = match (kind, key.as_str()) {
                (Some("adt"), "identity") | (Some("struct"), "adt") => {
                    ReconstructionRole::AdtIdentity
                }
                (Some("method_call"), "method") => ReconstructionRole::ValueIdentity,
                (Some("binding"), "id") => ReconstructionRole::MemberId,
                _ => ReconstructionRole::Ordinary,
            };
            result.insert(
                key.clone(),
                reconstruct_value(child, substitutions, seed, child_role),
            );
        }
        Value::Object(result)
    } else if let Some(array) = value.as_array() {
        Value::Array(
            array
                .iter()
                .map(|child| {
                    reconstruct_value(child, substitutions, seed, ReconstructionRole::Ordinary)
                })
                .collect(),
        )
    } else {
        value.clone()
    }
}

fn assert_reconstructs(result: &PairSynthesis, left: &Observation, right: &Observation) {
    let rule = result
        .rule
        .as_ref()
        .unwrap_or_else(|| panic!("expected accepted pair, got {:?}", result.rejection));
    let rule = serde_json::to_value(rule).unwrap();
    for (seed, expected) in [left, right].into_iter().enumerate() {
        let anchors = rule["pointer_anchors"]
            .as_array()
            .unwrap()
            .iter()
            .map(|anchor| {
                json!({
                    "id": reconstruct_value(
                        &anchor["id"],
                        &result.substitutions,
                        seed,
                        ReconstructionRole::MemberId,
                    ),
                    "source_type": reconstruct_value(
                        &anchor["source_type"],
                        &result.substitutions,
                        seed,
                        ReconstructionRole::Ordinary,
                    ),
                    "target_type": reconstruct_value(
                        &anchor["target_type"],
                        &result.substitutions,
                        seed,
                        ReconstructionRole::Ordinary,
                    )
                })
            })
            .collect::<Vec<_>>();
        let reconstructed: Observation = serde_json::from_value(json!({
            "source_expression": reconstruct_value(
                &rule["source_pattern"],
                &result.substitutions,
                seed,
                ReconstructionRole::Ordinary,
            ),
            "target_expression": reconstruct_value(
                &rule["target_pattern"],
                &result.substitutions,
                seed,
                ReconstructionRole::Ordinary,
            ),
            "pointer_anchors": anchors,
            "lhs": rule["lhs"],
            "source_type": reconstruct_value(
                &rule["source_type"],
                &result.substitutions,
                seed,
                ReconstructionRole::Ordinary,
            ),
            "source_adjusted_type": reconstruct_value(
                &rule["source_adjusted_type"],
                &result.substitutions,
                seed,
                ReconstructionRole::Ordinary,
            ),
            "target_type": reconstruct_value(
                &rule["target_type"],
                &result.substitutions,
                seed,
                ReconstructionRole::Ordinary,
            ),
            "target_adjusted_type": reconstruct_value(
                &rule["target_adjusted_type"],
                &result.substitutions,
                seed,
                ReconstructionRole::Ordinary,
            )
        }))
        .unwrap();
        assert_eq!(&reconstructed, expected);
    }
}

fn count_sort(document: &RuleDocument, sort: &str) -> usize {
    serialized(document)
        .matches(&format!("\"sort\": \"{sort}\""))
        .count()
}

#[test]
fn magnitude_disagreement_reuses_one_variable_across_source_and_target() {
    let left = observation(
        offset(binding(0), integer("1", "isize")),
        mutable_slice_from(binding(0), integer("1", "usize")),
    );
    let right = observation(
        offset(binding(0), integer("2", "isize")),
        mutable_slice_from(binding(0), integer("2", "usize")),
    );
    let result = pair(&left, &right);
    assert_reconstructs(&result, &left, &right);
    let rules = synthesize(vec![left, right]);
    assert_eq!(rules.rules.len(), 1);
    assert_eq!(count_sort(&rules, "integer_magnitude"), 2);
}

#[test]
fn complete_expression_disagreement_reuses_one_variable_across_patterns() {
    let left_amount = binary("add", binding(1), integer("1", "isize"));
    let right_amount = binary("multiply", binding(1), integer("2", "isize"));
    let left = observation(
        offset(binding(0), left_amount.clone()),
        mutable_slice_from(binding(0), left_amount),
    );
    let right = observation(
        offset(binding(0), right_amount.clone()),
        mutable_slice_from(binding(0), right_amount),
    );
    let result = pair(&left, &right);
    assert_reconstructs(&result, &left, &right);
    assert_eq!(count_sort(&synthesize(vec![left, right]), "expression"), 2);
}

#[test]
fn repeated_expression_disagreement_keeps_one_variable_identity() {
    let left_amount = binary("add", binding(1), integer("1", "isize"));
    let right_amount = binary("multiply", binding(1), integer("2", "isize"));
    let make = |amount: Value| {
        observation(
            call(
                "pair",
                vec![
                    offset(binding(0), amount.clone()),
                    offset(binding(0), amount.clone()),
                ],
            ),
            call(
                "pair",
                vec![
                    mutable_slice_from(binding(0), amount.clone()),
                    mutable_slice_from(binding(0), amount),
                ],
            ),
        )
    };
    let left = make(left_amount);
    let right = make(right_amount);
    let result = pair(&left, &right);
    assert_reconstructs(&result, &left, &right);
    let rule = serde_json::to_value(result.rule.unwrap()).unwrap();
    let indices = rule["source_pattern"]["arguments"]
        .as_array()
        .unwrap()
        .iter()
        .map(|argument| argument["arguments"][0]["kind"].clone())
        .collect::<Vec<_>>();
    assert_eq!(indices, vec![json!("variable"), json!("variable")]);
    assert!(!serialized(&synthesize(vec![left, right])).contains("\"index\": 1"));
}

#[test]
fn reversed_magnitude_disagreements_allocate_distinct_variables() {
    let make = |first: &str, second: &str| {
        with_anchor(
            call(
                "triple",
                vec![
                    unary("deref", binding(0)),
                    integer(first, "usize"),
                    integer(second, "usize"),
                ],
            ),
            call(
                "triple",
                vec![
                    binding(0),
                    integer(first, "usize"),
                    integer(second, "usize"),
                ],
            ),
            vec![anchor(0, ref_i32())],
        )
    };
    let rules = synthesize(vec![make("1", "2"), make("2", "1")]);
    assert_eq!(rules.rules.len(), 1);
    assert!(serialized(&rules).contains("\"index\": 1"));
}

#[test]
fn magnitude_and_expression_disagreements_remain_separate_sorts() {
    let magnitude_left = offset(binding(0), integer("1", "isize"));
    let magnitude_right = offset(binding(0), integer("2", "isize"));
    let expression_left = call("left", vec![integer("0", "i32")]);
    let expression_right = call("right", vec![integer("1", "i32")]);
    let left = observation(
        call("pair", vec![magnitude_left, expression_left]),
        binding(0),
    );
    let right = observation(
        call("pair", vec![magnitude_right, expression_right]),
        binding(0),
    );
    let rules = synthesize(vec![left, right]);
    assert_eq!(rules.rules.len(), 1);
    assert!(count_sort(&rules, "integer_magnitude") >= 1);
    assert!(count_sort(&rules, "expression") >= 1);
}

#[test]
fn noncanonical_or_differently_typed_integer_disagreements_generalize_expression() {
    for (left_value, right_value, left_type, right_type, expected) in [
        ("01", "02", "isize", "isize", "expression"),
        ("1", "02", "isize", "isize", "expression"),
        ("1", "2", "isize", "usize", "expression"),
        ("0", "1", "isize", "isize", "integer_magnitude"),
    ] {
        let left = observation(
            offset(binding(0), integer(left_value, left_type)),
            binding(0),
        );
        let right = observation(
            offset(binding(0), integer(right_value, right_type)),
            binding(0),
        );
        let rules = synthesize(vec![left, right]);
        assert_eq!(rules.rules.len(), 1, "{left_value:?}, {right_value:?}");
        assert!(count_sort(&rules, expected) >= 1);
        if expected == "expression" {
            assert_eq!(count_sort(&rules, "integer_magnitude"), 0);
        }
    }
}

#[test]
fn equal_noncanonical_integer_magnitudes_remain_concrete() {
    let observation = observation(offset(binding(0), integer("01", "isize")), binding(0));
    let rules = synthesize(vec![observation.clone(), observation]);
    assert_eq!(rules.rules.len(), 1);
    assert_eq!(count_sort(&rules, "expression"), 0);
    assert_eq!(count_sort(&rules, "integer_magnitude"), 0);
}

#[test]
fn non_ascii_integer_magnitudes_are_rejected_by_the_closed_rust_format() {
    // Crat emits ASCII magnitude strings, so the Rust-owned format intentionally
    // closes the former Python loader's broader Unicode-digit acceptance.
    for value in ["١", "²"] {
        let invalid = observation(offset(binding(0), integer(value, "isize")), binding(0));
        let error = synthesize_rules(&[document(vec![invalid])]).unwrap_err();
        assert!(error.message.contains("invalid integer literal"));
    }
}

#[test]
fn exact_duplicate_self_pair_and_equal_source_target_are_retained() {
    let transformation = with_anchor(
        unary("deref", binding(0)),
        binding(0),
        vec![anchor(0, ref_i32())],
    );
    assert!(synthesize(vec![transformation.clone()]).rules.is_empty());
    assert_eq!(
        synthesize(vec![transformation.clone(), transformation])
            .rules
            .len(),
        1
    );

    let unchanged = with_anchor(
        unary("deref", binding(0)),
        unary("deref", binding(0)),
        vec![anchor(0, ref_i32())],
    );
    assert_eq!(
        synthesize(vec![unchanged.clone(), unchanged]).rules.len(),
        1
    );
}

#[test]
fn reordered_binding_identities_preserve_the_equality_relation() {
    let value = with_anchor(
        call(
            "mix",
            vec![unary("deref", binding(0)), binding(1), binding(2)],
        ),
        call("mix", vec![binding(0), binding(2), binding(1)]),
        vec![anchor(0, ref_i32())],
    );
    let result = pair(&value, &value);
    assert_reconstructs(&result, &value, &value);
    let text = serialized(&synthesize(vec![value.clone(), value]));
    assert_eq!(text.matches("\"sort\": \"binding\"").count(), 4);
    assert!(!text.contains("<id"));
}

#[test]
fn source_variables_may_be_discarded_by_the_target() {
    let make = |magnitude: &str| {
        with_anchor(
            call(
                "select",
                vec![unary("deref", binding(0)), integer(magnitude, "i32")],
            ),
            binding(0),
            vec![anchor(0, ref_i32())],
        )
    };
    assert_eq!(synthesize(vec![make("1"), make("2")]).rules.len(), 1);
}

#[test]
fn expression_and_magnitude_variables_are_not_injective() {
    let left = with_anchor(
        call(
            "triple",
            vec![
                call("left", vec![integer("0", "i32")]),
                call("left", vec![integer("0", "i32")]),
                unary("deref", binding(0)),
            ],
        ),
        binding(0),
        vec![anchor(0, ref_i32())],
    );
    let right = with_anchor(
        call(
            "triple",
            vec![
                call("right", vec![integer("1", "i32")]),
                call("other", vec![integer("2", "i32")]),
                unary("deref", binding(0)),
            ],
        ),
        binding(0),
        vec![anchor(0, ref_i32())],
    );
    let result = pair(&left, &right);
    assert_reconstructs(&result, &left, &right);
    assert!(serialized(&synthesize(vec![left, right])).contains("\"index\": 1"));
}

#[test]
fn every_local_identity_namespace_is_emitted_in_its_valid_position() {
    let constructor = json!({
        "kind": "path",
        "value": {
            "kind": "constructor",
            "adt": local_adt("enum", 0),
            "variant": member("variant", "enum", 0, 0)
        }
    });
    let struct_expression = json!({
        "kind": "struct",
        "adt": local_adt("enum", 0),
        "variant": member("variant", "enum", 0, 0),
        "fields": [{
            "field": member("field", "enum", 0, 0),
            "value": call("identities", vec![
                json!({"kind": "path", "value": {"kind": "function", "id": "<fn0>"}}),
                json!({"kind": "path", "value": {"kind": "constant", "id": "<const0>"}}),
                json!({"kind": "path", "value": {"kind": "static", "id": "<static0>"}}),
                json!({
                    "kind": "method_call",
                    "receiver": binding(1),
                    "method": {"kind": "method", "id": "<method0>"},
                    "arguments": []
                }),
                constructor,
            ])
        }],
        "rest": null
    });
    let source = call(
        "all",
        vec![
            unary("deref", binding(0)),
            binding(1),
            struct_expression,
            json!({
                "kind": "struct",
                "adt": local_adt("union", 0),
                "variant": null,
                "fields": [{
                    "field": member("field", "union", 0, 1),
                    "value": integer("0", "i32")
                }],
                "rest": null
            }),
            json!({
                "kind": "struct",
                "adt": local_adt("struct", 0),
                "variant": null,
                "fields": [{
                    "field": member("field", "struct", 0, 2),
                    "value": integer("0", "i32")
                }],
                "rest": null
            }),
        ],
    );
    let mut target = source.clone();
    target["arguments"][0] = binding(0);
    let value = with_anchor(source, target, vec![anchor(0, ref_i32())]);
    let rules = synthesize(vec![value.clone(), value]);
    assert_eq!(rules.rules.len(), 1);
    for sort in [
        "anchor", "binding", "function", "struct", "enum", "union", "field", "variant", "constant",
        "static", "method",
    ] {
        assert!(count_sort(&rules, sort) > 0, "missing variable sort {sort}");
    }
    assert!(!serialized(&rules).contains("<struct"));
    assert!(!serialized(&rules).contains("<field"));
}

#[test]
fn constructor_variant_and_field_keep_their_structural_owner() {
    let named = |value: Value| {
        json!({
            "kind": "struct",
            "adt": local_adt("enum", 0),
            "variant": member("variant", "enum", 0, 0),
            "fields": [{"field": member("field", "enum", 0, 0), "value": value}],
            "rest": null
        })
    };
    let value = with_anchor(
        named(unary("deref", binding(0))),
        named(binding(0)),
        vec![anchor(0, ref_i32())],
    );
    let result = pair(&value, &value);
    assert_reconstructs(&result, &value, &value);
    let rule = serde_json::to_value(result.rule.unwrap()).unwrap();
    assert_eq!(
        rule["source_pattern"]["adt"],
        rule["source_pattern"]["fields"][0]["field"]["owner"]
    );
    assert_eq!(
        rule["source_pattern"]["adt"],
        rule["source_pattern"]["variant"]["owner"]
    );
}

#[test]
fn field_owner_and_member_id_have_independent_identity_carriers() {
    let value = with_anchor(
        call(
            "pair",
            vec![
                field(unary("deref", binding(0)), "struct", 0, 0),
                field(unary("deref", binding(0)), "struct", 0, 1),
            ],
        ),
        call(
            "pair",
            vec![
                field(binding(0), "struct", 0, 0),
                field(binding(0), "struct", 0, 1),
            ],
        ),
        vec![anchor(0, ref_i32())],
    );
    let rules = synthesize(vec![value.clone(), value]);
    assert_eq!(rules.rules.len(), 1);
    assert_eq!(count_sort(&rules, "struct"), 4);
    assert_eq!(count_sort(&rules, "field"), 4);
    let rule = serde_json::to_value(&rules.rules[0]).unwrap();
    assert_eq!(
        rule["source_pattern"]["arguments"][0]["field"]["id"]["index"],
        0
    );
    assert_eq!(
        rule["source_pattern"]["arguments"][1]["field"]["id"]["index"],
        1
    );
}

#[test]
fn target_context_may_introduce_a_dormant_intrinsic_identity() {
    let root = local_adt_type("struct", 0);
    let value = with_context(
        unary("deref", binding(0)),
        binding(0),
        vec![anchor(0, ref_i32())],
        [primitive("i32"), primitive("i32"), root.clone(), root],
    );
    let result = pair(&value, &value);
    assert_reconstructs(&result, &value, &value);
    let rule = result.rule.unwrap();
    assert!(matches!(
        rule.target_type,
        RuleTypeTree::Adt {
            identity: RuleAdtIdentity::Variable {
                sort: VariableSort::Struct,
                ..
            },
            ..
        }
    ));
    let document = RuleDocument {
        schema_version: RULE_SCHEMA_VERSION,
        rules: vec![rule],
    };
    assert_eq!(
        rule_document_from_json(&serialized(&document)).unwrap(),
        document
    );
}

#[test]
fn rigid_external_and_foreign_identities_and_literals_remain_concrete() {
    let foreign_call = |symbol: &str| {
        json!({
            "kind": "call",
            "callee": {"kind": "path", "value": {"kind": "foreign_function", "symbol": symbol}},
            "arguments": [
                {"kind": "literal", "value": {"kind": "char", "value": "x"}},
                unary("deref", binding(0)),
            ]
        })
    };
    let source = call("outer", vec![foreign_call("ffi_read")]);
    let target = call(
        "outer",
        vec![json!({
            "kind": "call",
            "callee": {"kind": "path", "value": {"kind": "foreign_function", "symbol": "ffi_read"}},
            "arguments": [
                {"kind": "literal", "value": {"kind": "char", "value": "x"}},
                binding(0),
            ]
        })],
    );
    let value = with_anchor(source, target, vec![anchor(0, ref_i32())]);
    let text = serialized(&synthesize(vec![value.clone(), value]));
    assert!(text.contains("ffi_read"));
    assert!(text.contains("\"value\": \"x\""));
    assert!(text.contains("\"fixture\""));
}

#[test]
fn target_only_and_mismatched_disagreements_reject_without_widening() {
    let unchanged_source = method(binding(0), "core", &["ptr", "const_ptr", "read"], vec![]);
    let target_only = pair(
        &observation(unchanged_source.clone(), integer("0", "i32")),
        &observation(unchanged_source, integer("1", "i32")),
    );
    assert_eq!(target_only.rejection, Some(PairRejection::TargetLookup));

    let mismatched = pair(
        &observation(
            offset(binding(0), integer("1", "isize")),
            mutable_slice_from(binding(0), integer("0", "usize")),
        ),
        &observation(
            offset(binding(0), integer("2", "isize")),
            mutable_slice_from(binding(0), integer("1", "usize")),
        ),
    );
    assert_eq!(mismatched.rejection, Some(PairRejection::TargetLookup));

    let left_amount = binary("add", binding(1), integer("1", "isize"));
    let right_amount = binary("multiply", binding(1), integer("2", "isize"));
    let no_narrow_fallback = pair(
        &observation(
            offset(binding(0), left_amount),
            mutable_slice_from(binding(0), integer("1", "isize")),
        ),
        &observation(
            offset(binding(0), right_amount),
            mutable_slice_from(binding(0), integer("2", "isize")),
        ),
    );
    assert_eq!(
        no_narrow_fallback.rejection,
        Some(PairRejection::TargetLookup)
    );
}

#[test]
fn target_only_local_identity_namespaces_reject_lookup() {
    let targets = vec![
        field(binding(0), "struct", 0, 0),
        json!({"kind": "cast", "expression": binding(0), "type": local_adt_type("struct", 0)}),
        json!({"kind": "cast", "expression": binding(0), "type": local_adt_type("union", 0)}),
        json!({
            "kind": "call",
            "callee": {
                "kind": "path",
                "value": {
                    "kind": "constructor",
                    "adt": local_adt("enum", 0),
                    "variant": member("variant", "enum", 0, 0)
                }
            },
            "arguments": [binding(0)]
        }),
        call(
            "pair",
            vec![
                binding(0),
                json!({"kind": "path", "value": {"kind": "constant", "id": "<const0>"}}),
            ],
        ),
        call(
            "pair",
            vec![
                binding(0),
                json!({"kind": "path", "value": {"kind": "static", "id": "<static0>"}}),
            ],
        ),
        call(
            "pair",
            vec![
                binding(0),
                json!({
                    "kind": "method_call",
                    "receiver": binding(0),
                    "method": {"kind": "method", "id": "<method0>"},
                    "arguments": []
                }),
            ],
        ),
    ];
    for target in targets {
        let value = with_anchor(
            unary("deref", binding(0)),
            target,
            vec![anchor(0, ref_i32())],
        );
        assert_eq!(
            pair(&value, &value).rejection,
            Some(PairRejection::TargetLookup)
        );
    }
}

#[test]
fn differing_rigid_callees_generalize_only_at_a_strict_parent() {
    let root_left = with_anchor(
        call("load", vec![unary("deref", binding(0))]),
        call("load", vec![binding(0)]),
        vec![anchor(0, ref_i32())],
    );
    let root_right = with_anchor(
        call("peek", vec![unary("deref", binding(0))]),
        call("peek", vec![binding(0)]),
        vec![anchor(0, ref_i32())],
    );
    assert_eq!(
        pair(&root_left, &root_right).rejection,
        Some(PairRejection::DegenerateSource)
    );

    let nested_left = with_anchor(
        call(
            "outer",
            vec![
                call("load", vec![integer("0", "i32")]),
                unary("deref", binding(0)),
            ],
        ),
        call(
            "outer",
            vec![call("load", vec![integer("0", "i32")]), binding(0)],
        ),
        vec![anchor(0, ref_i32())],
    );
    let nested_right = with_anchor(
        call(
            "outer",
            vec![
                call("peek", vec![integer("1", "i32")]),
                unary("deref", binding(0)),
            ],
        ),
        call(
            "outer",
            vec![call("peek", vec![integer("1", "i32")]), binding(0)],
        ),
        vec![anchor(0, ref_i32())],
    );
    let accepted = pair(&nested_left, &nested_right);
    assert_reconstructs(&accepted, &nested_left, &nested_right);
}

#[test]
fn a_wholly_generalized_source_is_degenerate() {
    let left = observation(
        call("left", vec![unary("deref", binding(0))]),
        call("left", vec![unary("deref", binding(0))]),
    );
    let right = observation(
        call("right", vec![offset(binding(0), integer("1", "isize"))]),
        call("right", vec![offset(binding(0), integer("1", "isize"))]),
    );
    assert_eq!(
        pair(&left, &right).rejection,
        Some(PairRejection::DegenerateSource)
    );
}

#[test]
fn anchors_may_not_be_hidden_inside_expression_variables() {
    let left = observation(
        call("consume", vec![unary("deref", binding(0))]),
        call("consume", vec![unary("deref", binding(0))]),
    );
    let right = observation(
        call("consume", vec![offset(binding(0), integer("1", "isize"))]),
        call("consume", vec![offset(binding(0), integer("1", "isize"))]),
    );
    assert_eq!(pair(&left, &right).rejection, Some(PairRejection::Carrier));

    let explicit_left = with_anchor(
        call(
            "combine",
            vec![unary("deref", binding(0)), call("read", vec![binding(0)])],
        ),
        call("combine", vec![binding(0), call("read", vec![binding(0)])]),
        vec![anchor(0, ref_i32())],
    );
    let explicit_right = with_anchor(
        call(
            "combine",
            vec![
                unary("deref", binding(0)),
                offset(binding(0), integer("1", "isize")),
            ],
        ),
        call(
            "combine",
            vec![binding(0), offset(binding(0), integer("1", "isize"))],
        ),
        vec![anchor(0, ref_i32())],
    );
    assert_eq!(
        pair(&explicit_left, &explicit_right).rejection,
        Some(PairRejection::Carrier)
    );
}

#[test]
fn identities_may_not_split_across_explicit_and_expression_carriers() {
    let left = with_anchor(
        binary(
            "add",
            binding(0),
            unary("deref", offset(binding(1), binding(0))),
        ),
        binary("add", binding(0), index(binding(1), binding(0))),
        vec![anchor(1, mut_slice_i32())],
    );
    let right = with_anchor(
        binary(
            "add",
            binding(0),
            unary("deref", offset(binding(1), integer("1", "usize"))),
        ),
        binary("add", binding(0), index(binding(1), integer("1", "usize"))),
        vec![anchor(1, mut_slice_i32())],
    );
    assert_eq!(pair(&left, &right).rejection, Some(PairRejection::Carrier));
}

#[test]
fn unequal_binding_equality_partitions_reject() {
    let left = with_anchor(
        call(
            "combine",
            vec![unary("deref", binding(0)), binding(1), binding(1)],
        ),
        call("combine", vec![binding(0), binding(1), binding(1)]),
        vec![anchor(0, ref_i32())],
    );
    let right = with_anchor(
        call(
            "combine",
            vec![unary("deref", binding(0)), binding(1), binding(2)],
        ),
        call("combine", vec![binding(0), binding(1), binding(2)]),
        vec![anchor(0, ref_i32())],
    );
    assert_eq!(pair(&left, &right).rejection, Some(PairRejection::Carrier));
}

#[test]
fn context_requires_anchor_shape_types_and_namespace_bijections() {
    let one = observation(binding(0), binding(0));
    let two = with_anchor(
        call("f", vec![binding(0), binding(1)]),
        call("f", vec![binding(0), binding(1)]),
        vec![anchor(0, mut_slice_i32()), anchor(1, mut_slice_i32())],
    );
    assert_eq!(pair(&one, &two).rejection, Some(PairRejection::Context));

    let left_type = json!({
        "kind": "tuple",
        "elements": [local_adt_type("struct", 0), local_adt_type("struct", 0)]
    });
    let right_type = json!({
        "kind": "tuple",
        "elements": [local_adt_type("struct", 0), local_adt_type("struct", 1)]
    });
    let left = with_context(
        unary("deref", binding(0)),
        binding(0),
        vec![anchor(0, ref_i32())],
        std::array::from_fn(|_| left_type.clone()),
    );
    let right = with_context(
        unary("deref", binding(0)),
        binding(0),
        vec![anchor(0, ref_i32())],
        std::array::from_fn(|_| right_type.clone()),
    );
    assert_eq!(pair(&left, &right).rejection, Some(PairRejection::Context));
}

#[test]
fn every_expression_constructor_preserves_and_traverses_its_children() {
    let dereference = || unary("deref", binding(0));
    let direct = || binding(0);
    let expression_statement = |expression: Value| json!({"kind": "expression", "expression": expression, "semicolon": false});
    let cases = vec![
        (
            "array",
            json!({"kind": "array", "elements": [dereference()]}),
            json!({"kind": "array", "elements": [direct()]}),
        ),
        (
            "call",
            call("f", vec![dereference()]),
            call("f", vec![direct()]),
        ),
        (
            "method_call",
            method(dereference(), "fixture", &["Trait", "method"], vec![]),
            method(direct(), "fixture", &["Trait", "method"], vec![]),
        ),
        (
            "tuple",
            json!({"kind": "tuple", "elements": [integer("0", "i32"), dereference()]}),
            json!({"kind": "tuple", "elements": [integer("0", "i32"), direct()]}),
        ),
        (
            "binary",
            binary("add", integer("0", "i32"), dereference()),
            binary("add", integer("0", "i32"), direct()),
        ),
        ("unary", unary("not", dereference()), unary("not", direct())),
        (
            "cast",
            json!({"kind": "cast", "expression": dereference(), "type": primitive("i32")}),
            json!({"kind": "cast", "expression": direct(), "type": primitive("i32")}),
        ),
        (
            "if",
            json!({
                "kind": "if",
                "condition": {"kind": "literal", "value": {"kind": "bool", "value": true}},
                "then": {"statements": [expression_statement(dereference())]},
                "else": dereference()
            }),
            json!({
                "kind": "if",
                "condition": {"kind": "literal", "value": {"kind": "bool", "value": true}},
                "then": {"statements": [expression_statement(direct())]},
                "else": direct()
            }),
        ),
        (
            "while",
            json!({
                "kind": "while",
                "condition": {"kind": "literal", "value": {"kind": "bool", "value": true}},
                "body": {"statements": [expression_statement(dereference())]}
            }),
            json!({
                "kind": "while",
                "condition": {"kind": "literal", "value": {"kind": "bool", "value": true}},
                "body": {"statements": [expression_statement(direct())]}
            }),
        ),
        (
            "loop",
            json!({"kind": "loop", "body": {"statements": [expression_statement(dereference())]}}),
            json!({"kind": "loop", "body": {"statements": [expression_statement(direct())]}}),
        ),
        (
            "assign",
            json!({"kind": "assign", "left": integer("0", "i32"), "right": dereference()}),
            json!({"kind": "assign", "left": integer("0", "i32"), "right": direct()}),
        ),
        (
            "assign_op",
            json!({
                "kind": "assign_op",
                "operator": "add",
                "left": integer("0", "i32"),
                "right": dereference()
            }),
            json!({
                "kind": "assign_op",
                "operator": "add",
                "left": integer("0", "i32"),
                "right": direct()
            }),
        ),
        (
            "field",
            field(dereference(), "struct", 0, 0),
            field(direct(), "struct", 0, 0),
        ),
        (
            "index",
            index(integer("0", "i32"), dereference()),
            index(integer("0", "i32"), direct()),
        ),
        (
            "range",
            json!({"kind": "range", "start": integer("0", "usize"), "end": dereference(), "limits": "closed"}),
            json!({"kind": "range", "start": integer("0", "usize"), "end": direct(), "limits": "closed"}),
        ),
        (
            "address_of",
            json!({"kind": "address_of", "borrow": "raw", "mutability": "const", "expression": dereference()}),
            json!({"kind": "address_of", "borrow": "raw", "mutability": "const", "expression": direct()}),
        ),
        (
            "break",
            json!({"kind": "break", "value": dereference()}),
            json!({"kind": "break", "value": direct()}),
        ),
        (
            "continue",
            json!({"kind": "array", "elements": [{"kind": "continue"}, dereference()]}),
            json!({"kind": "array", "elements": [{"kind": "continue"}, direct()]}),
        ),
        (
            "return",
            json!({"kind": "return", "value": dereference()}),
            json!({"kind": "return", "value": direct()}),
        ),
        (
            "struct",
            json!({
                "kind": "struct",
                "adt": local_adt("struct", 0),
                "variant": null,
                "fields": [{"field": member("field", "struct", 0, 0), "value": dereference()}],
                "rest": null
            }),
            json!({
                "kind": "struct",
                "adt": local_adt("struct", 0),
                "variant": null,
                "fields": [{"field": member("field", "struct", 0, 0), "value": direct()}],
                "rest": null
            }),
        ),
        (
            "repeat",
            json!({"kind": "repeat", "value": dereference(), "count": integer("2", "usize")}),
            json!({"kind": "repeat", "value": direct(), "count": integer("2", "usize")}),
        ),
        (
            "block",
            json!({"kind": "block", "block": {"statements": [expression_statement(dereference())]}}),
            json!({"kind": "block", "block": {"statements": [expression_statement(direct())]}}),
        ),
    ];

    for (name, source, target) in cases {
        let value = with_anchor(source, target, vec![anchor(0, ref_i32())]);
        let result = pair(&value, &value);
        assert!(
            result.rule.is_some(),
            "constructor {name}: {:?}",
            result.rejection
        );
        assert_reconstructs(&result, &value, &value);
    }
}

#[test]
fn binding_and_wildcard_patterns_and_optional_block_fields_traverse_exactly() {
    let source = json!({
        "kind": "block",
        "block": {
            "statements": [
                {
                    "kind": "let",
                    "pattern": {"kind": "binding", "id": "<id1>", "mutability": "mutable", "by_ref": "no"},
                    "type": primitive("i32"),
                    "initializer": unary("deref", binding(0))
                },
                {
                    "kind": "let",
                    "pattern": {"kind": "wildcard"},
                    "type": null,
                    "initializer": null
                },
                {"kind": "expression", "expression": binding(1), "semicolon": false}
            ]
        }
    });
    let mut target = source.clone();
    target["block"]["statements"][0]["initializer"] = binding(0);
    let value = with_anchor(source, target, vec![anchor(0, ref_i32())]);
    let result = pair(&value, &value);
    assert_reconstructs(&result, &value, &value);
    let rule = serde_json::to_value(result.rule.unwrap()).unwrap();
    assert_eq!(
        rule["source_pattern"]["block"]["statements"][0]["pattern"]["id"],
        rule["source_pattern"]["block"]["statements"][2]["expression"]["value"]
    );
}

#[test]
fn every_type_constructor_is_retained_and_local_adt_identity_is_abstracted() {
    let types = vec![
        primitive("i32"),
        json!({"kind": "slice", "element": primitive("i32")}),
        json!({"kind": "array", "element": primitive("i32"), "length": 4}),
        raw_i32(),
        ref_i32(),
        json!({"kind": "tuple", "elements": [primitive("i32"), ref_i32()]}),
        local_adt_type("struct", 0),
        json!({
            "kind": "adt",
            "adt_kind": "enum",
            "identity": {"kind": "external", "crate": "core", "path": ["option", "Option"]},
            "arguments": [ref_i32()]
        }),
    ];
    for root in types {
        let value = with_context(
            unary("deref", binding(0)),
            binding(0),
            vec![anchor(0, ref_i32())],
            std::array::from_fn(|_| root.clone()),
        );
        let result = pair(&value, &value);
        assert_reconstructs(&result, &value, &value);
    }
}

#[test]
fn every_literal_constructor_and_foreign_static_are_rigid() {
    let literals = vec![
        json!({"kind": "bool", "value": true}),
        json!({"kind": "char", "value": "λ"}),
        json!({"kind": "byte", "value": 255}),
        json!({"kind": "string", "value": "text"}),
        json!({"kind": "byte_string", "value": [0, 255]}),
        json!({"kind": "c_string", "value": [65, 0]}),
        json!({"kind": "integer", "value": "42", "type": "u64"}),
        json!({"kind": "float", "bits": "3ff0000000000000", "type": "f64"}),
    ];
    let mut arguments = literals
        .into_iter()
        .map(|value| json!({"kind": "literal", "value": value}))
        .collect::<Vec<_>>();
    arguments.push(json!({
        "kind": "path",
        "value": {"kind": "foreign_static", "symbol": "FOREIGN_VALUE"}
    }));
    arguments.push(unary("deref", binding(0)));
    let source = call("literals", arguments);
    let mut target = source.clone();
    let last = target["arguments"].as_array().unwrap().len() - 1;
    target["arguments"][last] = binding(0);
    let value = with_anchor(source, target, vec![anchor(0, ref_i32())]);
    let result = pair(&value, &value);
    assert_reconstructs(&result, &value, &value);
    let text = serialized(&synthesize(vec![value.clone(), value]));
    for literal_kind in [
        "bool",
        "char",
        "byte",
        "string",
        "byte_string",
        "c_string",
        "integer",
        "float",
    ] {
        assert!(text.contains(&format!("\"kind\": \"{literal_kind}\"")));
    }
    assert!(text.contains("FOREIGN_VALUE"));
}

#[test]
fn one_identity_may_be_carried_by_one_expression_variable() {
    let left = observation(
        binary(
            "add",
            integer("1", "i32"),
            unary(
                "deref",
                offset(binding(0), binary("add", binding(1), binding(2))),
            ),
        ),
        binary(
            "add",
            integer("1", "i32"),
            index(binding(0), binary("add", binding(1), binding(2))),
        ),
    );
    let right = with_anchor(
        binary(
            "add",
            binding(0),
            unary(
                "deref",
                offset(binding(1), binary("add", binding(2), binding(3))),
            ),
        ),
        binary(
            "add",
            binding(0),
            index(binding(1), binary("add", binding(2), binding(3))),
        ),
        vec![anchor(1, mut_slice_i32())],
    );
    let result = pair(&left, &right);
    assert_reconstructs(&result, &left, &right);
}

#[test]
fn one_identity_may_not_split_across_two_expression_variables() {
    let left = with_anchor(
        call(
            "three",
            vec![
                unary("deref", binding(0)),
                call("left", vec![binding(1)]),
                call("left", vec![binding(1)]),
            ],
        ),
        binding(0),
        vec![anchor(0, ref_i32())],
    );
    let right = with_anchor(
        call(
            "three",
            vec![
                unary("deref", binding(0)),
                call("right", vec![binding(1)]),
                call("other", vec![binding(1)]),
            ],
        ),
        binding(0),
        vec![anchor(0, ref_i32())],
    );
    assert_eq!(pair(&left, &right).rejection, Some(PairRejection::Carrier));
}

#[test]
fn lhs_is_part_of_pair_compatibility_and_exact_reconstruction() {
    let mut left = observation(
        offset(binding(0), integer("1", "isize")),
        mutable_slice_from(binding(0), integer("1", "usize")),
    );
    let mut right = observation(
        offset(binding(0), integer("2", "isize")),
        mutable_slice_from(binding(0), integer("2", "usize")),
    );
    right.lhs = true;
    assert_eq!(pair(&left, &right).rejection, Some(PairRejection::Context));
    left.lhs = true;
    let result = pair(&left, &right);
    assert_reconstructs(&result, &left, &right);
    assert!(result.rule.unwrap().lhs);
}

#[test]
fn duplicate_compression_crosses_documents_and_singletons_do_not_self_pair() {
    let value = with_anchor(
        unary("deref", binding(0)),
        binding(0),
        vec![anchor(0, ref_i32())],
    );
    let singleton = synthesize_rules(&[document(vec![value.clone()])]).unwrap();
    assert!(singleton.rules.is_empty());
    let duplicates = synthesize_rules(&[
        document(vec![value.clone()]),
        document(vec![value.clone()]),
        document(vec![value]),
    ])
    .unwrap();
    assert_eq!(duplicates.rules.len(), 1);
    assert!(
        synthesize_rules(&[document(vec![])])
            .unwrap()
            .rules
            .is_empty()
    );
}

fn permutation_fixtures() -> [Observation; 4] {
    let a = observation(
        offset(binding(0), integer("1", "isize")),
        mutable_slice_from(binding(0), integer("1", "usize")),
    );
    let b = observation(
        offset(binding(0), integer("2", "isize")),
        mutable_slice_from(binding(0), integer("2", "usize")),
    );
    let c = observation(
        offset(binding(0), integer("1", "isize")),
        call("alternate", vec![binding(0), integer("1", "usize")]),
    );
    let d = observation(
        offset(binding(0), integer("2", "isize")),
        call("alternate", vec![binding(0), integer("2", "usize")]),
    );
    [a, b, c, d]
}

#[test]
fn document_and_observation_permutations_have_identical_canonical_bytes() {
    let [a, b, c, d] = permutation_fixtures();
    let variants = [
        vec![
            document(vec![a.clone(), b.clone()]),
            document(vec![c.clone(), d.clone(), a.clone()]),
        ],
        vec![
            document(vec![a.clone(), c.clone()]),
            document(vec![d.clone(), b.clone(), a.clone()]),
        ],
        vec![
            document(vec![a.clone()]),
            document(vec![a]),
            document(vec![c, b, d]),
        ],
    ];
    let outputs = variants
        .iter()
        .map(|documents| serialized(&synthesize_rules(documents).unwrap()))
        .collect::<Vec<_>>();
    assert!(outputs.windows(2).all(|pair| pair[0] == pair[1]));
}

#[test]
fn synthesis_does_not_mutate_nested_inputs_and_is_repeatable() {
    let [a, b, _, _] = permutation_fixtures();
    let documents = vec![document(vec![a, b])];
    let before = documents.clone();
    let first = synthesize_rules(&documents).unwrap();
    assert_eq!(documents, before);
    let second = synthesize_rules(&documents).unwrap();
    assert_eq!(documents, before);
    assert_eq!(serialized(&first), serialized(&second));
}

#[test]
fn conflicting_and_specific_candidates_are_retained_without_subsumption() {
    let [a, b, c, d] = permutation_fixtures();
    let rules = synthesize(vec![a.clone(), b, a, c, d]);
    assert_eq!(rules.rules.len(), 3);
}

#[test]
fn canonical_ids_follow_anchor_types_root_types_then_source_and_target_patterns() {
    let struct_expression = |value: Value| {
        json!({
            "kind": "struct",
            "adt": local_adt("struct", 0),
            "variant": null,
            "fields": [{"field": member("field", "struct", 0, 0), "value": value}],
            "rest": null
        })
    };
    let source = call(
        "ordered",
        vec![
            unary("deref", binding(0)),
            struct_expression(integer("0", "i32")),
        ],
    );
    let target = call(
        "ordered",
        vec![binding(0), struct_expression(integer("0", "i32"))],
    );
    let anchor_source = json!({
        "kind": "raw_pointer",
        "mutability": "const",
        "pointee": local_adt_type("struct", 1)
    });
    let anchor_target = json!({
        "kind": "reference",
        "mutability": "shared",
        "pointee": local_adt_type("struct", 1)
    });
    let root = local_adt_type("struct", 2);
    let value: Observation = serde_json::from_value(json!({
        "source_expression": source,
        "target_expression": target,
        "pointer_anchors": [{"id": "<id0>", "source_type": anchor_source, "target_type": anchor_target}],
        "lhs": false,
        "source_type": root,
        "source_adjusted_type": local_adt_type("struct", 2),
        "target_type": local_adt_type("struct", 2),
        "target_adjusted_type": local_adt_type("struct", 2)
    }))
    .unwrap();
    let rules = synthesize(vec![value.clone(), value]);
    let rule = serde_json::to_value(&rules.rules[0]).unwrap();
    assert_eq!(
        rule["pointer_anchors"][0]["source_type"]["pointee"]["identity"]["index"],
        0
    );
    assert_eq!(rule["source_type"]["identity"]["index"], 1);
    assert_eq!(rule["source_pattern"]["arguments"][1]["adt"]["index"], 2);
    assert_eq!(rule["target_pattern"]["arguments"][1]["adt"]["index"], 2);
    assert_eq!(rule["pointer_anchors"][0]["id"]["index"], 0);
    assert_eq!(
        rule["source_pattern"]["arguments"][0]["operand"]["value"]["index"],
        0
    );
}

#[test]
fn child_arity_and_operator_disagreements_hide_at_the_enclosing_expression() {
    let left_child = call("f", vec![binding(1)]);
    let right_child = call("f", vec![binding(1), binding(2)]);
    let left = observation(
        offset(binding(0), left_child.clone()),
        mutable_slice_from(binding(0), left_child),
    );
    let right = observation(
        offset(binding(0), right_child.clone()),
        mutable_slice_from(binding(0), right_child),
    );
    let arity = pair(&left, &right);
    assert_reconstructs(&arity, &left, &right);

    let left_child = binary("add", binding(1), integer("1", "isize"));
    let right_child = binary("subtract", binding(1), integer("1", "isize"));
    let left = observation(
        offset(binding(0), left_child.clone()),
        mutable_slice_from(binding(0), left_child),
    );
    let right = observation(
        offset(binding(0), right_child.clone()),
        mutable_slice_from(binding(0), right_child),
    );
    let operator = pair(&left, &right);
    assert_reconstructs(&operator, &left, &right);
}

#[test]
fn root_type_structure_and_external_identity_are_rigid_context() {
    let base = with_context(
        unary("deref", binding(0)),
        binding(0),
        vec![anchor(0, ref_i32())],
        std::array::from_fn(|_| {
            json!({
                "kind": "array",
                "element": local_adt_type("struct", 0),
                "length": 4
            })
        }),
    );
    let mut length = base.clone();
    length.source_type = serde_json::from_value(json!({
        "kind": "array",
        "element": local_adt_type("struct", 0),
        "length": 5
    }))
    .unwrap();
    assert_eq!(pair(&base, &length).rejection, Some(PairRejection::Context));

    let mut arity = base.clone();
    arity.source_type = serde_json::from_value(json!({
        "kind": "array",
        "element": {
            "kind": "adt",
            "adt_kind": "struct",
            "identity": local_adt("struct", 0),
            "arguments": [primitive("i32")]
        },
        "length": 4
    }))
    .unwrap();
    assert_eq!(pair(&base, &arity).rejection, Some(PairRejection::Context));

    let mut external = base.clone();
    external.source_type = serde_json::from_value(json!({
        "kind": "array",
        "element": {
            "kind": "adt",
            "adt_kind": "struct",
            "identity": {"kind": "external", "crate": "fixture", "path": ["External"]},
            "arguments": []
        },
        "length": 4
    }))
    .unwrap();
    assert_eq!(
        pair(&base, &external).rejection,
        Some(PairRejection::Context)
    );
}

fn reverse_json_object_members(value: &Value) -> Value {
    match value {
        Value::Object(object) => Value::Object(
            object
                .iter()
                .rev()
                .map(|(key, child)| (key.clone(), reverse_json_object_members(child)))
                .collect(),
        ),
        Value::Array(array) => {
            Value::Array(array.iter().map(reverse_json_object_members).collect())
        }
        _ => value.clone(),
    }
}

#[test]
fn recursive_input_json_member_order_does_not_change_canonical_output() {
    let left = observation_value(
        offset(binding(0), integer("1", "isize")),
        mutable_slice_from(binding(0), integer("1", "usize")),
        None,
        None,
    );
    let right = observation_value(
        offset(binding(0), integer("2", "isize")),
        mutable_slice_from(binding(0), integer("2", "usize")),
        None,
        None,
    );
    let ordinary = json!({"schema_version": 1, "observations": [left, right]});
    let reversed = reverse_json_object_members(&ordinary);
    let ordinary = observation_document_from_json(&ordinary.to_string()).unwrap();
    let reversed = observation_document_from_json(&reversed.to_string()).unwrap();
    assert_eq!(
        serialized(&synthesize_rules(&[ordinary]).unwrap()),
        serialized(&synthesize_rules(&[reversed]).unwrap())
    );
}

fn shift_variable_indices(value: &mut Value, amount: u64) {
    match value {
        Value::Object(object) => {
            if object.get("kind").and_then(Value::as_str) == Some("variable") {
                let index = object["index"].as_u64().unwrap();
                object.insert("index".into(), Value::from(index + amount));
            }
            for child in object.values_mut() {
                shift_variable_indices(child, amount);
            }
        }
        Value::Array(array) => {
            for child in array {
                shift_variable_indices(child, amount);
            }
        }
        _ => {}
    }
}

#[test]
fn canonicalization_ignores_precanonical_variable_indices() {
    let value = with_anchor(
        call("ordered", vec![unary("deref", binding(0)), binding(1)]),
        call("ordered", vec![binding(0), binding(1)]),
        vec![anchor(0, ref_i32())],
    );
    let original = pair(&value, &value).rule.unwrap();
    let mut shifted = serde_json::to_value(&original).unwrap();
    shift_variable_indices(&mut shifted, 9);
    let shifted: Rule = serde_json::from_value(shifted).unwrap();
    assert_eq!(
        canonicalize_rule(&original).unwrap(),
        canonicalize_rule(&shifted).unwrap()
    );
}

#[test]
fn rule_lhs_rejects_missing_and_every_nonboolean_wire_value() {
    let value = with_anchor(
        unary("deref", binding(0)),
        binding(0),
        vec![anchor(0, ref_i32())],
    );
    let valid = synthesize(vec![value.clone(), value]);
    let valid = serde_json::to_value(valid).unwrap();
    for replacement in [
        Value::Null,
        json!(0),
        json!(1),
        json!("false"),
        json!([]),
        json!({}),
    ] {
        let mut invalid = valid.clone();
        invalid["rules"][0]["lhs"] = replacement;
        assert!(rule_document_from_json(&invalid.to_string()).is_err());
    }
    let mut missing = valid;
    missing["rules"][0].as_object_mut().unwrap().remove("lhs");
    assert!(rule_document_from_json(&missing.to_string()).is_err());
}
