use super::*;
use crate::{StatementDisposition, StatementDispositionKind, StatementPairMetadata};

fn skeleton_view(skeleton: &str, transformed: Vec<u32>, needs: bool) -> SkeletonView {
    rustc_span::create_session_if_not_set_then(rustc_span::edition::Edition::Edition2021, |_| {
        let transformed_set = transformed.iter().copied().collect();
        let statement_dispositions = std::panic::catch_unwind(|| parse_crate(skeleton))
            .ok()
            .and_then(Result::ok)
            .and_then(|krate| {
                krate.items.first().and_then(|item| {
                    crate::preservation::make_disposition_forest(
                        item,
                        &transformed_set,
                        &HashSet::new(),
                    )
                    .ok()
                })
            })
            .unwrap_or_else(|| {
                transformed
                    .iter()
                    .copied()
                    .map(|label| StatementDisposition {
                        label,
                        disposition: StatementDispositionKind::Transform,
                        children: vec![],
                    })
                    .collect()
            });
        SkeletonView {
            skeleton: skeleton.to_owned(),
            needs_transformation: needs,
            statement_dispositions,
            statement_pair_metadata: transformed
                .into_iter()
                .map(|label| StatementPairMetadata {
                    label,
                    before_statement: "test".to_owned(),
                    pointer_variables_complete: true,
                    pointer_variables: vec![],
                })
                .collect(),
        }
    })
}

fn expected_function(id: u64, name: &str, skeleton: &str) -> ExpectedFunction {
    let mut labels = skeleton
        .match_indices("#[proctor(")
        .filter_map(|(start, _)| {
            let value = &skeleton[start + "#[proctor(".len()..];
            value[..value.find(')')?].parse::<u32>().ok()
        })
        .collect::<Vec<_>>();
    labels.sort_unstable();
    ExpectedFunction {
        id,
        name: name.to_owned(),
        view: skeleton_view(skeleton, labels.clone(), !labels.is_empty()),
    }
}

fn preservation_request(
    skeleton: &str,
    transformed: Vec<u32>,
    transformation: &str,
) -> ValidationRequest {
    ValidationRequest {
        schema_version: 1,
        expected_functions: vec![ExpectedFunction {
            id: 7,
            name: "f".to_owned(),
            view: skeleton_view(skeleton, transformed.clone(), !transformed.is_empty()),
        }],
        transformation: transformation.to_owned(),
    }
}

fn mixed_preservation_request(
    skeleton: &str,
    transformed: &[u32],
    rule_applied: &[u32],
    transformation: &str,
) -> ValidationRequest {
    let view = rustc_span::create_session_if_not_set_then(
        rustc_span::edition::Edition::Edition2021,
        |_| {
            let krate = parse_crate(skeleton).unwrap();
            SkeletonView {
                skeleton: skeleton.to_owned(),
                needs_transformation: !transformed.is_empty(),
                statement_dispositions: crate::preservation::make_disposition_forest(
                    &krate.items[0],
                    &transformed.iter().copied().collect(),
                    &rule_applied.iter().copied().collect(),
                )
                .unwrap(),
                statement_pair_metadata: transformed
                    .iter()
                    .copied()
                    .map(|label| StatementPairMetadata {
                        label,
                        before_statement: "test".to_owned(),
                        pointer_variables_complete: true,
                        pointer_variables: vec![],
                    })
                    .collect(),
            }
        },
    );
    ValidationRequest {
        schema_version: 1,
        expected_functions: vec![ExpectedFunction {
            id: 7,
            name: "f".to_owned(),
            view,
        }],
        transformation: transformation.to_owned(),
    }
}

fn request(skeleton: &str, transformation: &str) -> ValidationRequest {
    ValidationRequest {
        schema_version: 1,
        expected_functions: vec![expected_function(7, "f", skeleton)],
        transformation: transformation.to_owned(),
    }
}

fn codes(response: &ValidationResponse) -> Vec<&str> {
    match response {
        ValidationResponse::Invalid { failures } => failures
            .iter()
            .flat_map(|failure| failure.errors.iter())
            .map(|error| error.code.as_str())
            .collect(),
        ValidationResponse::SetupError { error } => vec![error.code.as_str()],
        ValidationResponse::Valid => vec![],
    }
}

fn assert_valid(skeleton: &str, transformation: &str) {
    let response = validate(&request(skeleton, transformation));
    assert_eq!(response, ValidationResponse::Valid, "{response:?}");
}

fn assert_code(skeleton: &str, transformation: &str, code: &str) {
    let response = validate(&request(skeleton, transformation));
    assert!(
        codes(&response).contains(&code),
        "missing `{code}` in {response:?}"
    );
}

fn assert_codes(skeleton: &str, transformation: &str, expected: &[&str]) {
    let response = validate(&request(skeleton, transformation));
    assert_eq!(codes(&response), expected, "{response:?}");
}

const UNIT_SKELETON: &str = "unsafe fn f() { #[proctor(0)] todo!(); }";

#[test]
fn preservation_forest_must_follow_depth_first_lexical_order() {
    let skeleton = r#"unsafe fn f() {
#[proctor(7)] if true {
    #[proctor(3)] return;
    #[proctor(9)] return;
}
#[proctor(1)] return;
}"#;
    for mutation in ["roots", "siblings"] {
        let mut expected = expected_function(7, "f", skeleton);
        match mutation {
            "roots" => expected.view.statement_dispositions.swap(0, 1),
            "siblings" => expected.view.statement_dispositions[0].children.swap(0, 1),
            _ => unreachable!(),
        }
        let response = validate(&ValidationRequest {
            schema_version: 1,
            expected_functions: vec![expected],
            transformation: skeleton.to_owned(),
        });
        assert_eq!(codes(&response), ["invalid_expected_skeleton"]);
    }
}

#[test]
fn mixed_rule_applied_slots_validate_in_both_topologies() {
    let outer_rule = r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag {
    #[proctor(1)] consume(1);
    #[proctor(2)] consume(2);
}
}"#;
    let valid_outer_rule = r#"unsafe fn f(flag: bool) {
#[proctor(0)] if !flag {
    #[proctor(1)] let proctor_temp_var_0 = 4;
    #[proctor(1)] consume(proctor_temp_var_0);
    #[proctor(2)] consume(5);
}
}"#;
    assert!(
        validate(&mixed_preservation_request(
            outer_rule,
            &[1, 2],
            &[0],
            valid_outer_rule,
        ))
        .is_valid()
    );

    let inner_rule = r#"unsafe fn f(flag: bool) {
#[proctor(0)] if true {
    #[proctor(1)] consume(1);
    #[proctor(2)] consume(2);
}
}"#;
    let valid_inner_rule = r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag {
    #[proctor(1)] consume(999);
    #[proctor(2)] consume(3);
}
}"#;
    assert!(
        validate(&mixed_preservation_request(
            inner_rule,
            &[0, 2],
            &[1],
            valid_inner_rule,
        ))
        .is_valid()
    );

    let invalid_outer = [
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(1)] consume(1); } }"#,
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(1)] consume(1); #[proctor(2)] consume(2); #[proctor(1)] consume(3); } }"#,
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(2)] consume(2); #[proctor(1)] consume(1); } }"#,
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(1)] consume(1); } #[proctor(2)] consume(2); }"#,
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { if true { #[proctor(1)] consume(1); } #[proctor(2)] consume(2); } }"#,
    ];
    for transformation in invalid_outer {
        assert!(
            !validate(&mixed_preservation_request(
                outer_rule,
                &[1, 2],
                &[0],
                transformation,
            ))
            .is_valid()
        );
    }

    let invalid_inner = [
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(2)] consume(2); } }"#,
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(1)] consume(1); #[proctor(1)] consume(3); #[proctor(2)] consume(2); } }"#,
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(2)] consume(2); #[proctor(1)] consume(1); } }"#,
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(2)] consume(2); } #[proctor(1)] consume(1); }"#,
        r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { if true { #[proctor(1)] consume(1); } #[proctor(2)] consume(2); } }"#,
    ];
    for transformation in invalid_inner {
        assert!(
            !validate(&mixed_preservation_request(
                inner_rule,
                &[0, 2],
                &[1],
                transformation,
            ))
            .is_valid()
        );
    }
}

#[test]
fn preserved_leaf_and_expansion_group_are_canonicalized() {
    let skeleton = "unsafe fn f(value: i32) -> i32 { #[proctor(0)] value + 1 }";
    for transformation in [
        "unsafe fn f(value: i32) -> i32 { #[proctor(0)] 999 }",
        "unsafe fn f(value: i32) -> i32 { #[proctor(0)] let proctor_temp_var_0 = value * 100; #[proctor(0)] proctor_temp_var_0 }",
    ] {
        assert_eq!(
            validate(&preservation_request(skeleton, vec![], transformation)),
            ValidationResponse::Valid
        );
    }
}

#[test]
fn preserved_parent_is_opaque_after_outer_alignment() {
    let skeleton = "unsafe fn f(flag: bool) -> i32 { #[proctor(0)] if flag { #[proctor(1)] let value: i32 = 1; #[proctor(2)] value } else { #[proctor(3)] 2 } }";
    let transformation = "unsafe fn f(flag: bool) -> i32 { #[proctor(0)] return 999; }";
    assert_eq!(
        validate(&preservation_request(skeleton, vec![], transformation)),
        ValidationResponse::Valid
    );
}

#[test]
fn preserved_restricted_conditional_coexists_with_transformed_control() {
    let skeleton = r#"
unsafe fn f(flag: bool, pointer: *mut i32, value: i32) -> i32 {
    #[proctor(0)]
    let conditional: i32 = value + (if flag { -1 } else { 1 });
    #[proctor(1)]
    if flag {
        #[proctor(2)]
        (*pointer = value);
    } else {
        #[proctor(3)]
        return conditional;
    }
    #[proctor(4)]
    conditional
}
"#;
    let transformation = r#"
unsafe fn f(flag: bool, pointer: *mut i32, value: i32) -> i32 {
    #[proctor(0)]
    let conditional: i32 = value + (if flag { 99 } else { 100 });
    #[proctor(1)]
    if flag {
        #[proctor(2)]
        (*pointer = value + 1);
    } else {
        #[proctor(3)]
        return -200;
    }
    #[proctor(4)]
    300
}
"#;
    assert_eq!(
        validate(&preservation_request(skeleton, vec![1, 2], transformation)),
        ValidationResponse::Valid
    );
}

#[test]
fn transformed_label_does_not_relax_nested_control_validation() {
    let skeleton = "unsafe fn f(flag: bool, value: i32) -> i32 { #[proctor(0)] value + (if flag { -1 } else { 1 }) }";
    assert_eq!(
        codes(&validate(&preservation_request(
            skeleton,
            vec![0],
            skeleton
        ))),
        ["invalid_expected_skeleton"]
    );
}

#[test]
fn opaque_restricted_conditional_rejects_inner_labels() {
    let skeleton = "unsafe fn f(flag: bool, value: i32) -> i32 { #[proctor(0)] value + (if flag { #[proctor(1)] -1 } else { 1 }) }";
    assert_eq!(
        codes(&validate(&preservation_request(skeleton, vec![], skeleton))),
        ["invalid_expected_skeleton"]
    );
}

#[test]
fn opaque_control_operand_rejects_inner_labels() {
    let skeleton = "unsafe fn f(a: bool) -> i32 { #[proctor(0)] if 1 + (if a { #[proctor(99)] 2 } else { 3 }) > 0 { #[proctor(1)] 1 } else { #[proctor(2)] 2 } }";
    assert_eq!(
        codes(&validate(&preservation_request(skeleton, vec![], skeleton))),
        ["invalid_expected_skeleton"]
    );
}

#[test]
fn unlabeled_restricted_conditionals_are_valid_control_operands() {
    for skeleton in [
        "unsafe fn f(a: bool) -> i32 { #[proctor(0)] if 1 + (if a { 2 } else { 3 }) > 0 { #[proctor(1)] 1 } else { #[proctor(2)] 2 } }",
        "unsafe fn f(a: bool) { #[proctor(0)] while 1 + (if a { 2 } else { 3 }) > 0 { #[proctor(1)] break; } }",
        "unsafe fn f(a: bool) { #[proctor(0)] for _value in 0..(if a { 1 } else { 2 }) { #[proctor(1)] continue; } }",
        "unsafe fn f(a: bool) -> i32 { #[proctor(0)] match (if a { 1 } else { 2 }) { value if (if a { true } else { false }) => { #[proctor(1)] value }, _ => { #[proctor(2)] 0 } } }",
    ] {
        assert_eq!(
            validate(&preservation_request(skeleton, vec![], skeleton)),
            ValidationResponse::Valid,
            "{skeleton}"
        );
    }
}

#[test]
fn bare_assignment_labels_are_statement_roots() {
    let skeleton = "unsafe fn f(mut values: (i32, i32), value: i32) { #[proctor(0)] values.0 = value; #[proctor(1)] values.1 += 1; }";
    assert_eq!(
        validate(&preservation_request(skeleton, vec![0, 1], skeleton)),
        ValidationResponse::Valid
    );
}

#[test]
fn preserved_child_requires_unique_control_anchor() {
    let skeleton = "unsafe fn f(flag: bool, pointer: *mut i32) { #[proctor(0)] if flag { #[proctor(1)] let nested: i32 = 1; #[proctor(2)] (*pointer = nested); } else { #[proctor(3)] return; } }";
    let valid = "unsafe fn f(flag: bool, pointer: *mut i32) { #[proctor(0)] let proctor_temp_var_0 = flag; #[proctor(0)] if proctor_temp_var_0 { #[proctor(1)] let nested: i32 = 99; #[proctor(2)] (*pointer = nested); } else { #[proctor(3)] return; } }";
    assert_eq!(
        validate(&preservation_request(skeleton, vec![0, 2], valid)),
        ValidationResponse::Valid
    );
    let misplaced = "unsafe fn f(flag: bool, pointer: *mut i32) { #[proctor(0)] if flag { #[proctor(2)] (*pointer = 7); } else { #[proctor(1)] let nested: i32 = 99; #[proctor(3)] return; } }";
    assert_eq!(
        codes(&validate(&preservation_request(
            skeleton,
            vec![0, 2],
            misplaced
        ))),
        ["descendant_location_mismatch"]
    );
    let missing = "unsafe fn f(flag: bool, pointer: *mut i32) { #[proctor(0)] let proctor_temp_var_0 = flag; }";
    assert_eq!(
        codes(&validate(&preservation_request(
            skeleton,
            vec![0, 2],
            missing
        ))),
        ["missing_control_root"]
    );
    let multiple = "unsafe fn f(flag: bool, pointer: *mut i32) { #[proctor(0)] if flag { #[proctor(1)] let nested: i32 = 1; #[proctor(2)] (*pointer = nested); } else { #[proctor(3)] return; } #[proctor(0)] if flag { #[proctor(1)] let nested: i32 = 2; #[proctor(2)] (*pointer = nested); } else { #[proctor(3)] return; } }";
    assert_eq!(
        codes(&validate(&preservation_request(
            skeleton,
            vec![0, 2],
            multiple
        ))),
        ["multiple_control_roots"]
    );
}

#[test]
fn invalid_preservation_metadata_is_setup_error() {
    let skeleton = "unsafe fn f() { #[proctor(0)] if true { #[proctor(1)] return; } }";
    for (needs, labels, code) in [
        (false, vec![0], "invalid_expected_skeleton"),
        (true, vec![0, 0], "invalid_expected_skeleton"),
        (true, vec![2], "invalid_expected_skeleton"),
        (true, vec![1], "invalid_expected_skeleton"),
    ] {
        let response = validate(&ValidationRequest {
            schema_version: 1,
            expected_functions: vec![ExpectedFunction {
                id: 7,
                name: "f".to_owned(),
                view: skeleton_view(skeleton, labels, needs),
            }],
            transformation: "unsafe fn f() { #[proctor(0)] if true { #[proctor(1)] return; } }"
                .to_owned(),
        });
        assert_eq!(codes(&response), [code], "{response:?}");
    }
}

#[test]
fn discarded_errors_do_not_leak_but_external_temporary_use_does() {
    let skeleton = "unsafe fn f(value: i32, pointer: *mut i32) -> i32 { #[proctor(0)] let scalar: i32 = value + 1; #[proctor(1)] (*pointer = scalar); #[proctor(2)] scalar }";
    let discarded = "unsafe fn f(value: i32, pointer: *mut i32) -> i32 { #[proctor(0)] #[allow(unused_variables)] unsafe { const LOCAL: i32 = 100; let wrong_name = value + LOCAL; wrong_name }; #[proctor(1)] (*pointer = value + 1); #[proctor(2)] 999 }";
    assert_eq!(
        validate(&preservation_request(skeleton, vec![1], discarded)),
        ValidationResponse::Valid
    );
    let escaping = "unsafe fn f(value: i32, pointer: *mut i32) -> i32 { #[proctor(0)] let proctor_temp_var_0 = value + 1; #[proctor(1)] (*pointer = proctor_temp_var_0); #[proctor(2)] 999 }";
    let response = validate(&preservation_request(skeleton, vec![1], escaping));
    assert!(
        codes(&response).contains(&"temporary_outside_expansion_group"),
        "{response:?}"
    );
}

#[test]
fn preserved_outer_alignment_keeps_stable_label_errors() {
    let skeleton = "unsafe fn f(value: i32) -> i32 { #[proctor(0)] let first: i32 = value + 1; #[proctor(1)] first + 2 }";
    for (transformation, code) in [
        (
            "unsafe fn f(value: i32) -> i32 { #[proctor(1)] value + 2 }",
            "missing_label",
        ),
        (
            "unsafe fn f(value: i32) -> i32 { #[proctor(00)] let first: i32 = value + 1; #[proctor(1)] first + 2 }",
            "malformed_label",
        ),
        (
            "unsafe fn f(value: i32) -> i32 { #[proctor(1)] value + 2; #[proctor(0)] let first: i32 = value + 1; }",
            "label_order_mismatch",
        ),
        (
            "unsafe fn f(value: i32) -> i32 { #[proctor(0)] let first: i32 = value + 1; #[proctor(1)] first + 2; #[proctor(0)] let second: i32 = value + 3; }",
            "nonconsecutive_label",
        ),
    ] {
        assert_eq!(
            codes(&validate(&preservation_request(
                skeleton,
                vec![],
                transformation
            ))),
            [code]
        );
    }
}

#[test]
fn valid_response_has_explicit_status() {
    let response = validate_json(
        r#"{"schema_version":1,"expected_functions":[{"id":7,"name":"f","view":{"skeleton":"unsafe fn f() { #[proctor(0)] todo!(); }","needs_transformation":true,"statement_dispositions":[{"label":0,"disposition":"transform","children":[]}],"statement_pair_metadata":[{"label":0,"before_statement":"test","pointer_variables_complete":true,"pointer_variables":[]}]}}],"transformation":"unsafe fn f() { #[proctor(0)] return; }"}"#,
    );
    assert_eq!(
        response,
        "{\n  \"schema_version\": 1,\n  \"status\": \"valid\"\n}"
    );
}

#[test]
fn invalid_response_matches_schema_and_key_order() {
    let response =
        validation_response_to_json(&validate(&request(UNIT_SKELETON, "unsafe fn f() {}")))
            .unwrap();
    assert!(
        response.starts_with(
            "{\n  \"schema_version\": 1,\n  \"status\": \"invalid\",\n  \"failures\": ["
        )
    );
    assert!(!response.ends_with('\n'));
    assert!(response.contains("\"code\": \"missing_label\""));
}

#[test]
fn setup_error_matches_schema_and_key_order() {
    let response =
        validate_json(r#"{"schema_version":2,"expected_functions":[],"transformation":""}"#);
    assert!(response.starts_with(
        "{\n  \"schema_version\": 1,\n  \"status\": \"setup_error\",\n  \"error\": {"
    ));
    assert!(response.contains("\"code\": \"unsupported_schema_version\""));
}

#[test]
fn json_round_trip_preserves_embedded_rust() {
    let input = r#"{
  "schema_version": 1,
  "expected_functions": [{"id":7,"name":"f","view":{"skeleton":"unsafe fn f() -> &'static str {\n #[proctor(0)]\n todo!()\n}","needs_transformation":true,"statement_dispositions":[{"label":0,"disposition":"transform","children":[]}],"statement_pair_metadata":[{"label":0,"before_statement":"test","pointer_variables_complete":true,"pointer_variables":[]}]}}],
  "transformation":"unsafe fn f() -> &'static str {\n #[proctor(0)]\n \"quote:\\\" slash:\\\\ line:\\n\"\n}"
}"#;
    assert!(validate_json(input).contains("\"status\": \"valid\""));
    let typed: ValidationRequest = serde_json::from_str(input).unwrap();
    assert!(
        typed
            .transformation
            .contains("quote:\\\" slash:\\\\ line:\\n")
    );
}

#[test]
fn response_serialization_is_byte_deterministic() {
    let request = request(
        "unsafe fn f() { #[proctor(0)] todo!(); #[proctor(1)] todo!(); }",
        "unsafe fn f() { #[proctor(2)] return; }",
    );
    assert_eq!(
        validation_response_to_json(&validate(&request)).unwrap(),
        validation_response_to_json(&validate(&request)).unwrap()
    );
}

#[test]
fn malformed_request_json_is_setup_error() {
    for input in [
        r#"{"schema_version":1,"expected_functions":["#,
        r#"{"schema_version":1.0,"expected_functions":[],"transformation":""}"#,
        r#"{"schema_version":1,"expected_functions":[{"id":-1,"name":"f","skeleton":"unsafe fn f() {}"}],"transformation":""}"#,
        r#"{"schema_version":1,"expected_functions":[{"id":1.0,"name":"f","skeleton":"unsafe fn f() {}"}],"transformation":""}"#,
        r#"{"schema_version":1,"expected_functions":[{"id":18446744073709551616,"name":"f","skeleton":"unsafe fn f() {}"}],"transformation":""}"#,
    ] {
        let response = validate_json(input);
        assert!(
            response.contains("\"code\": \"invalid_request_json\""),
            "{response}"
        );
        assert!(response.contains("\"schema_version\": 1"));
    }
}

#[test]
fn unknown_request_field_is_setup_error() {
    let response = validate_json(
        r#"{"schema_version":1,"expected_functions":[{"id":7,"name":"f","skeleton":"unsafe fn f() { #[proctor(0)] todo!(); }","needs_transformation":true,"statements_requiring_transformation":[0]}],"transformation":"unsafe fn f() { #[proctor(0)] return; }","extra":true}"#,
    );
    assert!(response.contains("\"code\": \"unknown_request_field\""));
}

#[test]
fn empty_expected_function_list_is_setup_error() {
    let response = validate(&ValidationRequest {
        schema_version: 1,
        expected_functions: vec![],
        transformation: String::new(),
    });
    assert_eq!(codes(&response), ["empty_expected_functions"]);
}

#[test]
fn duplicate_expected_ids_are_setup_error() {
    let mut request = request(UNIT_SKELETON, "unsafe fn f() {}");
    request.expected_functions.push(expected_function(
        7,
        "g",
        "unsafe fn g() { #[proctor(0)] todo!(); }",
    ));
    assert_eq!(codes(&validate(&request)), ["duplicate_expected_id"]);
}

#[test]
fn duplicate_expected_names_are_setup_error() {
    let mut request = request(UNIT_SKELETON, "unsafe fn f() {}");
    request
        .expected_functions
        .push(expected_function(8, "f", UNIT_SKELETON));
    assert_eq!(codes(&validate(&request)), ["duplicate_expected_name"]);
}

#[test]
fn expected_skeleton_must_parse_as_one_function() {
    assert_eq!(
        codes(&validate(&request("unsafe fn f( {", "unsafe fn f() {}"))),
        ["expected_skeleton_parse_error"]
    );
    assert_eq!(
        codes(&validate(&request(
            "unsafe fn f() {} unsafe fn g() {}",
            "unsafe fn f() {}"
        ))),
        ["expected_skeleton_item_count"]
    );
}

#[test]
fn expected_skeleton_name_must_match_metadata() {
    assert_eq!(
        codes(&validate(&request(
            "unsafe fn g() { #[proctor(0)] todo!(); }",
            "unsafe fn f() {}"
        ))),
        ["expected_skeleton_name_mismatch"]
    );
}

#[test]
fn invalid_expected_skeleton_is_setup_error() {
    for skeleton in [
        "unsafe fn f() { #[proctor(0)] return; #[proctor(0)] return; }",
        "unsafe fn f() { #[proctor(00)] return; }",
        "unsafe fn f() { #[proctor(0)] fn local() {} }",
        "unsafe fn f() { #[proctor(0)] const LOCAL: () = { #[proctor(1)] fn nested() {} }; }",
        "unsafe fn f() { #[proctor(0)] type Local = i32; }",
        "unsafe fn f() { #[proctor(0)] struct Local(i32); }",
        "unsafe fn f() { #[proctor(0)] use core::mem; }",
        "unsafe fn f() { #[proctor(0)] macro_rules! local { () => {}; } }",
        "unsafe fn f((x, y): (i32, i32)) { #[proctor(0)] return; }",
        "unsafe fn f<T>(x: T) { #[proctor(0)] return; }",
        "unsafe fn f<'a: 'static>(x: &'a i32) { #[proctor(0)] return; }",
        "unsafe fn f<'a>(x: &'a i32) where 'a: 'static { #[proctor(0)] return; }",
        "unsafe fn f<#[allow(unused)] 'a>(x: &'a i32) { #[proctor(0)] return; }",
        "unsafe fn f<'a>(x: &'a i32) where { #[proctor(0)] return; }",
        "async unsafe fn f() { #[proctor(0)] return; }",
        "const unsafe fn f() { #[proctor(0)] return; }",
        "unsafe extern \"C\" fn f(x: i32, mut args: ...) { #[proctor(0)] return; }",
        "unsafe fn f() { return; }",
        "unsafe fn f() { #[proctor(0)] #[allow(unused_variables)] let x = 1; }",
        "unsafe fn f() { #[proctor(0)] consume(if true { 1 } else { 0 }); }",
        "unsafe fn f(x: i32) { #[proctor(0)] match x { _ => return } }",
    ] {
        assert_eq!(
            codes(&validate(&request(skeleton, "unsafe fn f() {}"))),
            ["invalid_expected_skeleton"],
            "{skeleton}"
        );
    }
}

#[test]
fn result_parse_error_is_global() {
    assert_eq!(
        codes(&validate(&request(UNIT_SKELETON, "unsafe fn f( {"))),
        ["result_parse_error"]
    );
}

#[test]
fn missing_expected_function_is_global() {
    let mut request = request(UNIT_SKELETON, "unsafe fn f() { #[proctor(0)] return; }");
    request.expected_functions.push(expected_function(
        8,
        "g",
        "unsafe fn g() { #[proctor(0)] todo!(); }",
    ));
    assert_eq!(codes(&validate(&request)), ["missing_function"]);
}

#[test]
fn unexpected_and_duplicate_functions_are_global() {
    let response = validate(&request(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(0)] return; } unsafe fn f() { #[proctor(0)] return; } unsafe fn extra() {}",
    ));
    assert_eq!(
        codes(&response),
        ["duplicate_function", "unexpected_function"]
    );
}

#[test]
fn every_nonfunction_top_level_item_is_unexpected() {
    for item in [
        "use core::ptr;",
        "extern crate core;",
        "const X: i32 = 1;",
        "mod m {}",
        "macro_rules! m { () => {} }",
        "static X: i32 = 1;",
        "type X = i32;",
        "struct X(i32);",
        "enum X { A }",
        "union X { value: i32 }",
        "trait X {}",
        "impl X for i32 {}",
        "unsafe extern \"C\" { fn foreign(); }",
        "m!();",
    ] {
        let transformation = format!("{item} unsafe fn f() {{ #[proctor(0)] return; }}");
        assert_code(UNIT_SKELETON, &transformation, "unexpected_item");
    }
}

#[test]
fn result_function_order_is_irrelevant() {
    let request = ValidationRequest {
        schema_version: 1,
        expected_functions: vec![
            expected_function(7, "f", UNIT_SKELETON),
            expected_function(
                8,
                "r#match",
                "unsafe fn r#match() { #[proctor(0)] todo!(); }",
            ),
        ],
        transformation:
            "unsafe fn r#match() { #[proctor(0)] return; } unsafe fn f() { #[proctor(0)] return; }"
                .to_owned(),
    };
    assert_eq!(validate(&request), ValidationResponse::Valid);
}

#[test]
fn function_header_attributes_do_not_add_items() {
    assert_valid(
        UNIT_SKELETON,
        "#[inline(always)] pub const fn f() { #[proctor(0)] return; }",
    );
}

#[test]
fn binding_mutability_and_ignored_header_properties_may_differ() {
    assert_valid(
        "pub unsafe extern \"C\" fn f(mut p: &mut [i32], mut n: usize) -> i32 { #[proctor(0)] todo!() }",
        "const fn f(p: &mut [i32], mut n: usize) -> i32 { #[proctor(0)] p[n] }",
    );
}

#[test]
fn parameter_count_and_names_are_exact() {
    let skeleton = "unsafe fn f(mut left: i32, mut right: i32) -> i32 { #[proctor(0)] todo!() }";
    assert_code(
        skeleton,
        "unsafe fn f(left: i32) -> i32 { #[proctor(0)] left }",
        "parameter_count_mismatch",
    );
    assert_code(
        skeleton,
        "unsafe fn f(a: i32, right: i32) -> i32 { #[proctor(0)] a + right }",
        "parameter_name_mismatch",
    );
}

#[test]
fn formatting_and_redundant_type_parentheses_are_ignored() {
    assert_valid(
        "unsafe fn f(mut p: Option<&'static mut [i32; 4]>) -> (i32, usize) { #[proctor(0)] todo!() }",
        "unsafe fn f(p: Option < & 'static mut ([i32; 4]) >) -> ((i32), usize) { #[proctor(0)] (0, p.unwrap().len()) }",
    );
}

#[test]
fn path_qualification_is_structural() {
    assert_code(
        "unsafe fn f(mut p: Option<&i32>) { #[proctor(0)] todo!(); }",
        "unsafe fn f(p: core::option::Option<&i32>) { #[proctor(0)] return; }",
        "parameter_type_mismatch",
    );
}

#[test]
fn pointer_and_reference_mutability_are_enforced() {
    let response = validate(&request(
        "unsafe fn f(mut p: &mut i32, mut q: *const i32) { #[proctor(0)] todo!(); }",
        "unsafe fn f(p: &i32, q: *mut i32) { #[proctor(0)] return; }",
    ));
    assert_eq!(
        codes(&response),
        ["parameter_type_mismatch", "parameter_type_mismatch"]
    );
}

#[test]
fn array_lengths_and_generic_arguments_are_enforced() {
    let response = validate(&request(
        "unsafe fn f(mut a: [u8; 4], mut p: Option<Box<[i32]>>) { #[proctor(0)] todo!(); }",
        "unsafe fn f(a: [u8; 5], p: Option<Box<i32>>) { #[proctor(0)] return; }",
    ));
    assert_eq!(
        codes(&response),
        ["parameter_type_mismatch", "parameter_type_mismatch"]
    );
}

#[test]
fn explicit_lifetime_names_in_types_are_enforced() {
    let response = validate(&request(
        "unsafe fn f<'a>(mut x: &'a i32, mut y: &'a i32) -> &'a i32 { #[proctor(0)] todo!() }",
        "unsafe fn f<'b>(x: &'b i32, y: &'b i32) -> &'b i32 { #[proctor(0)] x }",
    ));
    assert_eq!(
        codes(&response),
        [
            "generic_parameter_mismatch",
            "parameter_type_mismatch",
            "parameter_type_mismatch",
            "return_type_mismatch"
        ]
    );
}

#[test]
fn matching_lifetime_generic_declaration_is_valid() {
    assert_valid(
        r#"unsafe fn f<'input, 'output>(
            mut input: &'input i32,
            mut fallback: &'output i32,
        ) -> &'input i32 {
            #[proctor(0)] todo!()
        }"#,
        r#"pub extern "C" fn f<'input, 'output>(
            input: &'input i32,
            fallback: &'output i32,
        ) -> &'input i32 {
            #[proctor(0)] let _ = fallback;
            #[proctor(0)] input
        }"#,
    );
}

#[test]
fn omitted_lifetime_declaration_is_rejected_even_when_types_match() {
    assert_codes(
        r#"unsafe fn f<'a>(mut input: &'a i32) -> &'a i32 {
            #[proctor(0)] todo!()
        }"#,
        r#"unsafe fn f(input: &'a i32) -> &'a i32 {
            #[proctor(0)] input
        }"#,
        &["generic_parameter_mismatch"],
    );
}

#[test]
fn added_or_renamed_lifetime_is_rejected() {
    let skeleton = r#"unsafe fn f<'a>(mut input: &'a i32) -> &'a i32 {
        #[proctor(0)] todo!()
    }"#;
    for transformation in [
        r#"unsafe fn f<'a, 'unused>(input: &'a i32) -> &'a i32 {
            #[proctor(0)] input
        }"#,
        r#"unsafe fn f<'b>(input: &'a i32) -> &'a i32 {
            #[proctor(0)] input
        }"#,
    ] {
        assert_codes(skeleton, transformation, &["generic_parameter_mismatch"]);
    }
}

#[test]
fn lifetime_parameter_order_is_exact() {
    assert_codes(
        "unsafe fn f<'a, 'b>() { #[proctor(0)] return; }",
        "unsafe fn f<'b, 'a>() { #[proctor(0)] return; }",
        &["generic_parameter_mismatch"],
    );
}

#[test]
fn attributes_bounds_type_const_and_where_generics_are_rejected() {
    let skeleton = r#"unsafe fn f<'a>(mut input: &'a i32) -> &'a i32 {
        #[proctor(0)] todo!()
    }"#;
    for transformation in [
        "unsafe fn f<'a: 'static>(input: &'a i32) -> &'a i32 { #[proctor(0)] input }",
        "unsafe fn f<#[allow(unused)] 'a>(input: &'a i32) -> &'a i32 { #[proctor(0)] input }",
        "unsafe fn f<'a, T>(input: &'a i32) -> &'a i32 { #[proctor(0)] input }",
        "unsafe fn f<'a, const N: usize>(input: &'a i32) -> &'a i32 { #[proctor(0)] input }",
        "unsafe fn f<'a>(input: &'a i32) -> &'a i32 where 'a: 'static { #[proctor(0)] input }",
        "unsafe fn f<'a>(input: &'a i32) -> &'a i32 where { #[proctor(0)] input }",
    ] {
        assert_codes(skeleton, transformation, &["generic_parameter_mismatch"]);
    }
}

#[test]
fn generic_mismatch_aggregates_in_request_order() {
    let request = ValidationRequest {
        schema_version: 1,
        expected_functions: vec![
            expected_function(
                7,
                "first",
                "unsafe fn first<'a>(mut input: &'a i32) -> &'a i32 { #[proctor(0)] todo!() }",
            ),
            expected_function(
                8,
                "second",
                "unsafe fn second<'x, 'y>(mut input: &'x i32, mut fallback: &'y i32) -> &'x i32 { #[proctor(0)] todo!() }",
            ),
        ],
        transformation: r#"
unsafe fn second<'y, 'x>(input: &'x i32, fallback: &'y i32) -> &'x i32 {
    #[proctor(0)] let _ = fallback;
    #[proctor(0)] input
}
unsafe fn first(input: &'a i32) -> &'a i32 {
    #[proctor(0)] input
}"#
        .to_owned(),
    };
    let ValidationResponse::Invalid { failures } = validate(&request) else {
        panic!("expected generic mismatches");
    };
    assert_eq!(
        failures
            .iter()
            .map(|failure| failure.name.as_deref().unwrap())
            .collect::<Vec<_>>(),
        ["first", "second"]
    );
    assert!(
        failures
            .iter()
            .all(|failure| failure.errors[0].code == "generic_parameter_mismatch")
    );
    assert_eq!(
        validation_response_to_json(&validate(&request)).unwrap(),
        validation_response_to_json(&validate(&request)).unwrap()
    );
}

#[test]
fn rejects_every_local_item() {
    for skeleton in [
        "unsafe fn f() { #[proctor(0)] const LOCAL: i32 = 1; }",
        "unsafe fn f() { #[proctor(0)] { #[proctor(1)] static mut STATE: i32 = 1; } }",
    ] {
        assert_codes(skeleton, "unsafe fn f() {}", &["invalid_expected_skeleton"]);
    }
    let skeleton = "unsafe fn f() { #[proctor(0)] return; }";
    for transformation in [
        r#"unsafe fn f() {
            #[proctor(0)] const LOCAL: i32 = {
                let ordinary_name = 1;
                ordinary_name
            };
        }"#,
        "unsafe fn f() { #[proctor(0)] static mut STATE: i32 = 1; }",
    ] {
        assert_codes(skeleton, transformation, &["unexpected_nested_item"]);
    }
}

#[test]
fn omitted_return_and_explicit_unit_are_distinct() {
    assert_code(
        UNIT_SKELETON,
        "unsafe fn f() -> () { #[proctor(0)] return; }",
        "return_type_mismatch",
    );
}

#[test]
fn one_to_one_and_one_to_many_groups_are_valid() {
    assert_valid(
        "unsafe fn f(mut p: Option<&i32>) -> i32 { #[proctor(0)] let mut x: i32 = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f(p: Option<&i32>) -> i32 { #[proctor(0)] let proctor_temp_var_0 = p.unwrap(); #[proctor(0)] let x: i32 = *proctor_temp_var_0; #[proctor(1)] x }",
    );
}

#[test]
fn every_expected_label_must_appear() {
    assert_code(
        "unsafe fn f() { #[proctor(0)] todo!(); #[proctor(1)] todo!(); }",
        "unsafe fn f() { #[proctor(0)] return; }",
        "missing_label",
    );
}

#[test]
fn new_numeric_label_is_rejected() {
    assert_code(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(0)] return; #[proctor(9)] return; }",
        "unexpected_label",
    );
}

#[test]
fn groups_must_follow_expected_order() {
    assert_code(
        "unsafe fn f() { #[proctor(0)] todo!(); #[proctor(1)] todo!(); #[proctor(2)] todo!(); }",
        "unsafe fn f() { #[proctor(1)] return; #[proctor(0)] return; #[proctor(2)] return; }",
        "label_order_mismatch",
    );
}

#[test]
fn one_group_must_be_consecutive() {
    assert_code(
        "unsafe fn f() { #[proctor(0)] todo!(); #[proctor(1)] todo!(); }",
        "unsafe fn f() { #[proctor(0)] return; #[proctor(1)] return; #[proctor(0)] return; }",
        "nonconsecutive_label",
    );
}

#[test]
fn unlabeled_sibling_at_expected_statement_level_is_rejected() {
    assert_code(
        "unsafe fn f() { #[proctor(0)] todo!(); #[proctor(1)] todo!(); }",
        "unsafe fn f() { #[proctor(0)] return; consume(); #[proctor(1)] return; }",
        "unlabeled_group_statement",
    );
}

#[test]
fn new_unlabeled_nested_code_inside_leaf_group_is_valid() {
    assert_valid(
        "unsafe fn f(mut flag: bool) -> i32 { #[proctor(0)] todo!() }",
        "unsafe fn f(flag: bool) -> i32 { #[proctor(0)] if flag { let proctor_temp_var_0 = 1; proctor_temp_var_0 } else { 0 } }",
    );
}

#[test]
fn existing_label_may_not_repeat_in_nested_code() {
    assert_codes(
        "unsafe fn f(mut flag: bool) -> i32 { #[proctor(0)] todo!() }",
        "unsafe fn f(flag: bool) -> i32 { #[proctor(0)] if flag { #[proctor(0)] 1 } else { 0 } }",
        &["nested_label_repetition"],
    );
}

#[test]
fn malformed_duplicate_and_misplaced_proctor_attributes_are_rejected() {
    for transformation in [
        "unsafe fn f() { #[proctor(x)] return; }",
        "unsafe fn f() { #[proctor(0, 1)] return; }",
        "unsafe fn f() { #[proctor()] return; }",
        "unsafe fn f() { #[proctor(4294967296)] return; }",
        "unsafe fn f() { #[other::proctor(0)] return; }",
        "unsafe fn f() { #[proctor(0)] #[proctor(0)] return; }",
        "unsafe fn f() { #[proctor(00)] return; }",
        "unsafe fn f() { #[proctor(1_0)] return; }",
        "unsafe fn f() { #[proctor(0u32)] return; }",
        "unsafe fn f() { #[proctor(0x0)] return; }",
        "unsafe fn f() { #[proctor(-1)] return; }",
    ] {
        assert_codes(UNIT_SKELETON, transformation, &["malformed_label"]);
    }
    assert_codes(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(0)] return; #[proctor(4294967295)] return; }",
        &["unexpected_label"],
    );
    assert_codes(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(0)] consume(#[proctor(0)] 1); }",
        &["misplaced_label"],
    );
    assert_codes(
        r#"unsafe fn f(mut flag: bool) {
#[proctor(0)] return;
#[proctor(1)] if todo!() {
#[proctor(2)] return;
}
}"#,
        r#"unsafe fn f(flag: bool) {
#[proctor(x)] return;
#[proctor(1)] while flag {
#[proctor(2)] return;
}
}"#,
        &["malformed_label", "control_kind_mismatch"],
    );
}

#[test]
fn all_supported_control_kinds_are_preserved() {
    let skeleton = r#"unsafe fn f(mut flag: bool, mut value: Option<i32>, mut xs: [i32; 1]) {
#[proctor(0)] if todo!() { #[proctor(1)] todo!(); } else { #[proctor(2)] todo!(); }
#[proctor(3)] if let Some(mut x) = todo!() { #[proctor(4)] todo!(); }
#[proctor(5)] while todo!() { #[proctor(6)] todo!(); }
#[proctor(7)] while let Some(mut x) = todo!() { #[proctor(8)] todo!(); }
#[proctor(9)] for mut x in todo!() { #[proctor(10)] todo!(); }
#[proctor(11)] loop { #[proctor(12)] break; }
#[proctor(13)] match todo!() { Some(mut x) => { #[proctor(14)] todo!(); } None => { #[proctor(15)] todo!(); } }
#[proctor(16)] { #[proctor(17)] todo!(); }
}"#;
    let result = r#"unsafe fn f(flag: bool, value: Option<i32>, xs: [i32; 1]) {
#[proctor(0)] if flag { #[proctor(1)] consume(1); } else { #[proctor(2)] consume(2); }
#[proctor(3)] if let Some(x) = value { #[proctor(4)] consume(x); }
#[proctor(5)] while flag { #[proctor(6)] break; }
#[proctor(7)] while let Some(x) = value { #[proctor(8)] consume(x); }
#[proctor(9)] for x in xs { #[proctor(10)] consume(x); }
#[proctor(11)] loop { #[proctor(12)] break; }
#[proctor(13)] match value { Some(x) => { #[proctor(14)] consume(x); } None => { #[proctor(15)] return; } }
#[proctor(16)] { #[proctor(17)] return; }
}"#;
    assert_valid(skeleton, result);
}

#[test]
fn control_kinds_are_distinct() {
    assert_code(
        "unsafe fn f(mut flag: bool) { #[proctor(0)] if todo!() { #[proctor(1)] todo!(); } }",
        "unsafe fn f(flag: bool) { #[proctor(0)] while flag { #[proctor(1)] return; } }",
        "control_kind_mismatch",
    );
}

#[test]
fn if_and_if_let_are_distinct() {
    assert_code(
        "unsafe fn f(mut value: Option<i32>) { #[proctor(0)] if let Some(mut x) = todo!() { #[proctor(1)] todo!(); } }",
        "unsafe fn f(value: Option<i32>) { #[proctor(0)] if value.is_some() { #[proctor(1)] return; } }",
        "control_kind_mismatch",
    );
}

#[test]
fn control_statement_role_is_preserved() {
    let skeleton = r#"unsafe fn f(mut flag: bool) -> i32 {
#[proctor(0)] let mut x: i32 = if todo!() { #[proctor(1)] todo!() } else { #[proctor(2)] todo!() };
#[proctor(3)] return if todo!() { #[proctor(4)] todo!() } else { #[proctor(5)] todo!() };
}"#;
    assert_code(
        skeleton,
        r#"unsafe fn f(flag: bool) -> i32 {
#[proctor(0)] if flag { #[proctor(1)] 1 } else { #[proctor(2)] 2 }
#[proctor(3)] return if flag { #[proctor(4)] 3 } else { #[proctor(5)] 4 };
}"#,
        "control_role_mismatch",
    );
    assert_code(
        skeleton,
        r#"unsafe fn f(flag: bool) -> i32 {
#[proctor(0)] let x: i32 = if flag { #[proctor(1)] 1 } else { #[proctor(2)] 2 };
#[proctor(3)] if flag { #[proctor(4)] return 3; } else { #[proctor(5)] return 4; }
}"#,
        "control_role_mismatch",
    );

    assert_codes(
        r#"unsafe fn f(mut flag: bool) -> i32 {
#[proctor(0)] let mut result: i32 = loop {
#[proctor(1)] break if todo!() {
#[proctor(2)] todo!()
} else {
#[proctor(3)] todo!()
};
};
#[proctor(4)] todo!()
}"#,
        r#"unsafe fn f(flag: bool) -> i32 {
#[proctor(0)] let result: i32 = loop {
#[proctor(1)] if flag {
#[proctor(2)] break 1;
} else {
#[proctor(3)] break 2;
}
};
#[proctor(4)] result
}"#,
        &["control_role_mismatch"],
    );

    assert_codes(
        r#"unsafe fn f(mut value: i32) -> i32 {
#[proctor(0)] match todo!() {
0 => {
#[proctor(1)] if todo!() {
#[proctor(2)] todo!()
} else {
#[proctor(3)] todo!()
}
}
_ => {
#[proctor(4)] todo!()
}
}
}"#,
        r#"unsafe fn f(value: i32) -> i32 {
#[proctor(0)] match value {
0 => {
#[proctor(1)] return if value > 0 {
#[proctor(2)] 1
} else {
#[proctor(3)] 2
};
}
_ => {
#[proctor(4)] 0
}
}
}"#,
        &["control_role_mismatch"],
    );
}

#[test]
fn if_else_existence_and_recursive_else_if_shape_are_preserved() {
    assert_code(
        r#"unsafe fn f(mut a: bool, mut b: bool) {
#[proctor(0)] if todo!() { #[proctor(1)] todo!(); } else if todo!() { #[proctor(2)] todo!(); } else { #[proctor(3)] todo!(); }
}"#,
        r#"unsafe fn f(a: bool, b: bool) {
#[proctor(0)] if a { #[proctor(1)] return; } else { #[proctor(2)] return; #[proctor(3)] return; }
}"#,
        "branch_shape_mismatch",
    );
    assert_codes(
        r#"unsafe fn f(mut value: Option<i32>) {
#[proctor(0)] if todo!() {
#[proctor(1)] return;
} else if let Some(_) = todo!() {
#[proctor(2)] return;
}
}"#,
        r#"unsafe fn f(value: Option<i32>) {
#[proctor(0)] if value.is_none() {
#[proctor(1)] return;
} else if value.is_some() {
#[proctor(2)] return;
}
}"#,
        &["control_kind_mismatch"],
    );
}

#[test]
fn match_arm_count_order_and_guard_presence_are_preserved() {
    let skeleton = r#"unsafe fn f(mut value: i32) {
#[proctor(0)] match todo!() {
0 => { #[proctor(1)] todo!(); }
x if todo!() => { #[proctor(2)] todo!(); }
_ => { #[proctor(3)] todo!(); }
} }"#;
    assert_code(
        skeleton,
        "unsafe fn f(value: i32) { #[proctor(0)] match value { 0 => { #[proctor(1)] return; } _ => { #[proctor(3)] return; } } }",
        "match_arm_shape_mismatch",
    );
    assert_code(
        skeleton,
        "unsafe fn f(value: i32) { #[proctor(0)] match value { 0 => { #[proctor(1)] return; } x => { #[proctor(2)] consume(x); } _ => { #[proctor(3)] return; } } }",
        "match_guard_mismatch",
    );
}

#[test]
fn labeled_descendant_cannot_move_between_branches() {
    let response = validate(&request(
        "unsafe fn f(mut flag: bool) { #[proctor(0)] if todo!() { #[proctor(1)] todo!(); } else { #[proctor(2)] todo!(); } }",
        "unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(2)] return; } else { #[proctor(1)] return; } }",
    ));
    assert_eq!(
        codes(&response),
        [
            "descendant_location_mismatch",
            "descendant_location_mismatch"
        ]
    );
}

#[test]
fn control_group_has_exactly_one_preserved_control_root() {
    let skeleton =
        "unsafe fn f(mut flag: bool) { #[proctor(0)] if todo!() { #[proctor(1)] todo!(); } }";
    assert_valid(
        skeleton,
        "unsafe fn f(flag: bool) { #[proctor(0)] let proctor_temp_var_0 = flag; #[proctor(0)] if proctor_temp_var_0 { #[proctor(1)] return; } #[proctor(0)] consume(flag); }",
    );
    assert_code(
        skeleton,
        "unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(1)] return; } #[proctor(0)] while flag {} }",
        "multiple_control_roots",
    );
    assert_code(
        skeleton,
        "unsafe fn f(flag: bool) { #[proctor(0)] consume(flag); #[proctor(0)] consume(!flag); }",
        "missing_control_root",
    );
}

#[test]
fn plain_blocks_are_distinct_and_recursive() {
    assert_code(
        "unsafe fn f() { #[proctor(0)] { #[proctor(1)] { #[proctor(2)] todo!(); } } }",
        "unsafe fn f() { #[proctor(0)] { #[proctor(1)] loop { #[proctor(2)] break; } } }",
        "control_kind_mismatch",
    );
}

#[test]
fn let_else_form_and_else_body_are_preserved() {
    assert_code(
        "unsafe fn f(mut value: Option<i32>) -> i32 { #[proctor(0)] let Some(mut x): Option<i32> = todo!() else { #[proctor(1)] return todo!(); }; #[proctor(2)] todo!() }",
        "unsafe fn f(value: Option<i32>) -> i32 { #[proctor(0)] let x: i32 = value.unwrap(); #[proctor(1)] if value.is_none() { return 0; } #[proctor(2)] x }",
        "let_else_shape_mismatch",
    );
}

#[test]
fn binding_mutability_is_ignored_everywhere() {
    assert_valid(
        r#"unsafe fn f(mut pair: (i32, i32), mut value: Option<i32>) -> i32 {
#[proctor(0)] let (mut a, mut b) = todo!();
#[proctor(1)] if let Some(mut x) = todo!() { #[proctor(2)] return todo!(); }
#[proctor(3)] todo!()
}"#,
        r#"unsafe fn f(mut pair: (i32, i32), value: Option<i32>) -> i32 {
#[proctor(0)] let (a, mut b) = pair;
#[proctor(1)] if let Some(x) = value { #[proctor(2)] return x + b; }
#[proctor(3)] a
}"#,
    );
}

#[test]
fn existing_binding_must_exist_exactly_once_in_its_group() {
    let skeleton =
        "unsafe fn f() -> i32 { #[proctor(0)] let mut x: i32 = todo!(); #[proctor(1)] todo!() }";
    assert_code(
        skeleton,
        "unsafe fn f() -> i32 { #[proctor(0)] consume(1); #[proctor(1)] 0 }",
        "missing_existing_binding",
    );
    assert_code(
        skeleton,
        "unsafe fn f() -> i32 { #[proctor(0)] let x: i32 = 1; #[proctor(0)] let x: i32 = 2; #[proctor(1)] x }",
        "duplicate_existing_binding",
    );
}

#[test]
fn existing_binding_cannot_move_to_another_label() {
    assert_code(
        "unsafe fn f() -> i32 { #[proctor(0)] let mut x: i32 = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f() -> i32 { #[proctor(0)] consume(1); #[proctor(1)] let x: i32 = 1; #[proctor(1)] x }",
        "existing_binding_location_mismatch",
    );
}

#[test]
fn pattern_binding_names_stay_in_their_structural_roles() {
    let response = validate(&request(
        r#"unsafe fn f(mut value: Option<(i32, i32)>) -> i32 {
#[proctor(0)] match todo!() {
Some((mut left, mut right)) => { #[proctor(1)] todo!() }
None => { #[proctor(2)] todo!() }
} }"#,
        r#"unsafe fn f(value: Option<(i32, i32)>) -> i32 {
#[proctor(0)] match value {
Some((right, left)) => { #[proctor(1)] left + right }
None => { #[proctor(2)] 0 }
} }"#,
    ));
    assert_eq!(
        codes(&response)
            .iter()
            .filter(|code| **code == "existing_binding_location_mismatch")
            .count(),
        2
    );

    assert_valid(
        "unsafe fn f(mut values: [i32; 3]) -> i32 { #[proctor(0)] let [mut head, .., mut tail] = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f(values: [i32; 3]) -> i32 { #[proctor(0)] let [head, .., tail] = values; #[proctor(1)] head + tail }",
    );
    assert_code(
        "unsafe fn f(mut values: [i32; 3]) -> i32 { #[proctor(0)] let [mut head, .., mut tail] = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f(values: [i32; 3]) -> i32 { #[proctor(0)] let [tail, .., head] = values; #[proctor(1)] head + tail }",
        "existing_binding_location_mismatch",
    );

    assert_valid(
        "unsafe fn f(mut value: (i32, i32)) -> i32 { #[proctor(0)] let mut whole @ (mut inner, _) = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f(value: (i32, i32)) -> i32 { #[proctor(0)] let whole @ (inner, _) = value; #[proctor(1)] whole.0 + inner }",
    );
    assert_code(
        "unsafe fn f(mut value: (i32, i32)) -> i32 { #[proctor(0)] let mut whole @ (mut inner, _) = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f(value: (i32, i32)) -> i32 { #[proctor(0)] let (whole @ inner, _) = value; #[proctor(1)] whole + inner }",
        "existing_binding_location_mismatch",
    );

    let or_skeleton = r#"unsafe fn f(mut value: E) {
#[proctor(0)] match todo!() {
E::A { left: mut x, right: mut y } | E::B { left: mut x, right: mut y } => { #[proctor(1)] todo!(); }
} }"#;
    assert_valid(
        or_skeleton,
        r#"unsafe fn f(value: E) {
#[proctor(0)] match value {
E::A { left: x, right: y } | E::B { left: x, right: y } => { #[proctor(1)] consume(x + y); }
} }"#,
    );
    assert_code(
        or_skeleton,
        r#"unsafe fn f(value: E) {
#[proctor(0)] match value {
E::A { left: y, right: x } | E::B { left: y, right: x } => { #[proctor(1)] consume(x + y); }
} }"#,
        "existing_binding_location_mismatch",
    );

    assert_valid(
        "unsafe fn f(mut pair: &(i32, i32)) -> i32 { #[proctor(0)] let &(mut left, (mut right)) = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f(pair: &(i32, i32)) -> i32 { #[proctor(0)] let &(left, (right)) = pair; #[proctor(1)] left + right }",
    );
    assert_code(
        "unsafe fn f(mut pair: &(i32, i32)) -> i32 { #[proctor(0)] let &(mut left, (mut right)) = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f(pair: &(i32, i32)) -> i32 { #[proctor(0)] let (left, right) = *pair; #[proctor(1)] left + right }",
        "existing_binding_location_mismatch",
    );

    let mode_skeleton = "unsafe fn f(mut pair: (i32, i32)) -> i32 { #[proctor(0)] let (ref mut left, mut right) = todo!(); #[proctor(1)] todo!() }";
    assert_valid(
        mode_skeleton,
        "unsafe fn f(pair: (i32, i32)) -> i32 { #[proctor(0)] let (ref left, right) = pair; #[proctor(1)] *left + right }",
    );
    assert_code(
        mode_skeleton,
        "unsafe fn f(pair: (i32, i32)) -> i32 { #[proctor(0)] let (left, right) = pair; #[proctor(1)] left + right }",
        "existing_binding_mode_mismatch",
    );
    assert_codes(
        mode_skeleton,
        "unsafe fn f(pair: (i32, i32)) -> i32 { #[proctor(0)] let (ref left, ref right) = pair; #[proctor(1)] *left + *right }",
        &["existing_binding_mode_mismatch"],
    );

    assert_codes(
        r#"unsafe fn f(mut value: Option<i32>) -> i32 {
#[proctor(0)] let Some(mut x): Option<i32> = todo!() else {
#[proctor(1)] return todo!();
};
#[proctor(2)] todo!()
}"#,
        r#"unsafe fn f(value: Option<i32>) -> i32 {
#[proctor(0)] let Some(proctor_temp_var_0): Option<i32> = value else {
#[proctor(1)] return 0;
};
#[proctor(0)] let x: Option<i32> = Some(proctor_temp_var_0);
#[proctor(2)] x.unwrap()
}"#,
        &["existing_binding_location_mismatch"],
    );
}

#[test]
fn target_local_type_is_structural_and_required() {
    let skeleton = "unsafe fn f() { #[proctor(0)] let mut p: Option<&mut [i32]> = todo!(); }";
    assert_code(
        skeleton,
        "unsafe fn f() { #[proctor(0)] let p: Option<&[i32]> = None; }",
        "local_type_mismatch",
    );
    assert_code(
        skeleton,
        "unsafe fn f() { #[proctor(0)] let p = None::<&mut [i32]>; }",
        "local_type_presence_mismatch",
    );
}

#[test]
fn target_absence_of_local_type_is_preserved() {
    assert_code(
        "unsafe fn f(mut pair: (i32, i32)) { #[proctor(0)] let (mut x, mut y) = todo!(); }",
        "unsafe fn f(pair: (i32, i32)) { #[proctor(0)] let (x, y): (i32, i32) = pair; }",
        "local_type_presence_mismatch",
    );
}

#[test]
fn same_spelling_bindings_in_distinct_scopes_keep_identity() {
    let skeleton = r#"unsafe fn f(mut a: bool, mut b: bool) {
#[proctor(0)] if todo!() { #[proctor(1)] let mut x: i32 = todo!(); }
#[proctor(2)] if todo!() { #[proctor(3)] let mut x: i32 = todo!(); }
}"#;
    let response = validate(&request(
        skeleton,
        r#"unsafe fn f(a: bool, b: bool) {
#[proctor(0)] if a { #[proctor(1)] let x: i32 = 1; }
#[proctor(2)] if b { #[proctor(3)] consume(2); }
}"#,
    ));
    assert_eq!(
        codes(&response)
            .iter()
            .filter(|code| **code == "missing_existing_binding")
            .count(),
        1
    );
    let response = validate(&request(
        skeleton,
        r#"unsafe fn f(a: bool, b: bool) {
#[proctor(0)] if a { #[proctor(1)] consume(1); }
#[proctor(2)] if b { #[proctor(3)] let x: i32 = 2; }
}"#,
    ));
    let ValidationResponse::Invalid { failures } = response else {
        panic!("expected one missing declaration")
    };
    assert_eq!(
        failures[0]
            .errors
            .iter()
            .map(|error| error.code.as_str())
            .collect::<Vec<_>>(),
        ["missing_existing_binding"]
    );
    assert!(failures[0].errors[0].message.contains("label 1"));
}

#[test]
fn temporaries_are_local_to_one_expansion_group() {
    assert_valid(
        "unsafe fn f(mut p: Option<&i32>) -> i32 { #[proctor(0)] let mut x: i32 = todo!(); #[proctor(1)] todo!() }",
        r#"unsafe fn f(p: Option<&i32>) -> i32 {
#[proctor(0)] let proctor_temp_var_2 = p.unwrap();
#[proctor(0)] let proctor_temp_var_9 = if *proctor_temp_var_2 > 0 { *proctor_temp_var_2 } else { 0 };
#[proctor(0)] let x: i32 = proctor_temp_var_9;
#[proctor(1)] x
}"#,
    );
}

#[test]
fn new_binding_names_and_temporary_declarations_are_strict() {
    for transformation in [
        "unsafe fn f() { #[proctor(0)] let helper = 1; }",
        "unsafe fn f() { #[proctor(0)] let proctor_temp_var_x = 1; }",
        "unsafe fn f() { #[proctor(0)] if let Some(helper) = Some(1) { consume(helper); } }",
        "unsafe fn f() { #[proctor(0)] let (helper, proctor_temp_var_0) = (1, 2); }",
        "unsafe fn f() { #[proctor(0)] while let Some(helper) = None::<i32> { consume(helper); } }",
        "unsafe fn f() { #[proctor(0)] for helper in [1] { consume(helper); } }",
        "unsafe fn f() { #[proctor(0)] match Some(1) { Some(helper) => { consume(helper); } None => {} } }",
        "unsafe fn f() { #[proctor(0)] let proctor_temp_var_0 = |helper| helper; }",
    ] {
        assert_code(
            UNIT_SKELETON,
            transformation,
            "invalid_generated_binding_name",
        );
    }
    assert_code(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(0)] let proctor_temp_var_0 = 1; { let proctor_temp_var_0 = 2; consume(proctor_temp_var_0); } }",
        "duplicate_generated_temporary",
    );
    assert_code(
        "unsafe fn f() -> i32 { #[proctor(0)] let mut proctor_temp_var_0: i32 = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f() -> i32 { #[proctor(0)] let proctor_temp_var_0: i32 = 1; #[proctor(1)] let proctor_temp_var_0 = 2; #[proctor(1)] proctor_temp_var_0 }",
        "invalid_generated_binding_name",
    );
}

#[test]
fn temporary_reference_cannot_cross_group_boundary() {
    let skeleton = "unsafe fn f() { #[proctor(0)] todo!(); #[proctor(1)] todo!(); }";
    assert_code(
        skeleton,
        "unsafe fn f() { #[proctor(0)] let proctor_temp_var_0 = 1; #[proctor(1)] consume(proctor_temp_var_0); }",
        "temporary_outside_expansion_group",
    );
    assert_code(
        skeleton,
        "unsafe fn f() { #[proctor(0)] consume(proctor_temp_var_7); #[proctor(1)] return; }",
        "unresolved_generated_temporary",
    );
    for transformation in [
        r#"unsafe fn f() {
#[proctor(0)] consume(proctor_temp_var_0);
#[proctor(0)] let proctor_temp_var_0 = 1;
#[proctor(1)] return;
}"#,
        r#"unsafe fn f() {
#[proctor(0)] {
let proctor_temp_var_0 = 1;
}
#[proctor(0)] consume(proctor_temp_var_0);
#[proctor(1)] return;
}"#,
        r#"unsafe fn f() {
#[proctor(0)] if true {
let proctor_temp_var_0 = 1;
} else {
consume(proctor_temp_var_0);
}
#[proctor(1)] return;
}"#,
    ] {
        assert_codes(
            skeleton,
            transformation,
            &["unresolved_generated_temporary"],
        );
    }
}

#[test]
fn existing_temporary_shaped_bindings_retain_lexical_identity() {
    let parameter_skeleton = "unsafe fn f(mut proctor_temp_var_0: i32) { #[proctor(0)] todo!(); }";
    assert_valid(
        parameter_skeleton,
        "unsafe fn f(proctor_temp_var_0: i32) { #[proctor(0)] consume(proctor_temp_var_0); }",
    );
    assert_valid(
        parameter_skeleton,
        "unsafe fn f(proctor_temp_var_0: i32) { #[proctor(0)] consume!(proctor_temp_var_0); }",
    );
    assert_code(
        parameter_skeleton,
        "unsafe fn f(proctor_temp_var_0: i32) { #[proctor(0)] let proctor_temp_var_0 = 1; }",
        "invalid_generated_binding_name",
    );

    assert_codes(
        r#"unsafe fn f(mut flag: bool) {
#[proctor(0)] if todo!() {
#[proctor(1)] let mut proctor_temp_var_0: i32 = todo!();
}
#[proctor(2)] todo!();
}"#,
        r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag {
#[proctor(1)] let proctor_temp_var_0: i32 = 1;
}
#[proctor(2)] consume(proctor_temp_var_0);
}"#,
        &["unresolved_generated_temporary"],
    );
}

#[test]
fn temporary_identifier_in_macro_tokens_is_rejected() {
    assert_code(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(0)] let proctor_temp_var_0 = 1; #[proctor(0)] println!(\"{}\", proctor_temp_var_0); }",
        "temporary_in_macro",
    );
    assert_valid(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(0)] println!(\"ok\"); }",
    );
}

#[test]
fn explicit_unsafe_block_is_rejected_at_any_depth() {
    assert_code(
        "unsafe fn f(mut p: *const i32) -> i32 { #[proctor(0)] todo!() }",
        "unsafe fn f(p: *const i32) -> i32 { #[proctor(0)] if p.is_null() { 0 } else { unsafe { *p } } }",
        "explicit_unsafe_block",
    );
}

#[test]
fn new_statement_or_expression_attributes_are_rejected() {
    assert_code(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(0)] #[allow(unused_variables)] let proctor_temp_var_0 = 1; }",
        "unexpected_body_attribute",
    );
    assert_code(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(0)] { #[allow(unused_variables)] let proctor_temp_var_0 = 1; } }",
        "unexpected_body_attribute",
    );
}

#[test]
fn parent_failure_suppresses_dependent_cascade() {
    let response = validate(&request(
        r#"unsafe fn f(mut flag: bool) {
#[proctor(0)] if todo!() {
#[proctor(1)] let mut x: i32 = todo!();
} else {
#[proctor(2)] let mut y: i32 = todo!();
} }"#,
        r#"unsafe fn f(flag: bool) {
#[proctor(0)] loop {
#[proctor(2)] let y: u32 = 1;
} }"#,
    ));
    assert_eq!(codes(&response), ["control_kind_mismatch"]);

    assert_codes(
        r#"unsafe fn f(mut value: Option<i32>) {
#[proctor(0)] if let Some(mut x) = todo!() {
#[proctor(1)] consume(todo!());
}
}"#,
        r#"unsafe fn f(value: Option<i32>) {
#[proctor(0)] if value.is_some() {
#[proctor(1)] consume(1);
}
}"#,
        &["control_kind_mismatch"],
    );
    assert_codes(
        r#"unsafe fn f(mut value: Option<i32>) -> i32 {
#[proctor(0)] let Some(mut x): Option<i32> = todo!() else {
#[proctor(1)] return todo!();
};
#[proctor(2)] todo!()
}"#,
        r#"unsafe fn f(value: Option<i32>) -> i32 {
#[proctor(0)] let x: Option<i32> = value;
#[proctor(1)] return 0;
#[proctor(2)] x.unwrap()
}"#,
        &["let_else_shape_mismatch"],
    );

    assert_codes(
        r#"unsafe fn f(mut value: Option<i32>) {
#[proctor(0)] if let Some(mut x) = todo!() {
#[proctor(1)] consume(todo!());
} else {
#[proctor(2)] return;
}
}"#,
        r#"unsafe fn f(value: Option<i32>) {
#[proctor(0)] if let Some(_) = value {
#[proctor(1)] consume(1);
}
}"#,
        &["missing_existing_binding", "branch_shape_mismatch"],
    );

    assert_codes(
        r#"unsafe fn f(mut flag: bool) {
#[proctor(0)] if todo!() {
#[proctor(1)] return;
} else {
#[proctor(2)] return;
}
}"#,
        r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag {}
}"#,
        &["missing_label", "branch_shape_mismatch"],
    );

    assert_codes(
        r#"unsafe fn f(mut flag: bool) {
#[proctor(0)] if todo!() {
#[proctor(1)] let mut x: i32 = todo!();
} else {
#[proctor(2)] return;
}
}"#,
        r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag {
#[proctor(1)] let x: u32 = 1;
} else if flag {
#[proctor(1)] return;
}
}"#,
        &[
            "local_type_mismatch",
            "nested_label_repetition",
            "branch_shape_mismatch",
        ],
    );
}

#[test]
fn independent_errors_are_aggregated_in_stable_order() {
    let validation_request = request(
        "unsafe fn f(mut p: &i32) -> i32 { #[proctor(0)] let mut x: i32 = todo!(); #[proctor(1)] todo!() }",
        "unsafe fn f(p: *const i32) -> i32 { #[proctor(0)] let x: u32 = 1; #[proctor(2)] 0 }",
    );
    assert_eq!(
        codes(&validate(&validation_request)),
        [
            "parameter_type_mismatch",
            "local_type_mismatch",
            "missing_label",
            "unexpected_label"
        ]
    );
    assert_eq!(
        validation_response_to_json(&validate(&validation_request)).unwrap(),
        validation_response_to_json(&validate(&validation_request)).unwrap()
    );

    assert_codes(
        "unsafe fn f(mut a: i32, mut b: u32) { #[proctor(0)] return; }",
        "unsafe fn f(x: i64, y: u64) { #[proctor(0)] return; }",
        &[
            "parameter_name_mismatch",
            "parameter_name_mismatch",
            "parameter_type_mismatch",
            "parameter_type_mismatch",
        ],
    );
    assert_codes(
        UNIT_SKELETON,
        "unsafe fn f() { #[proctor(1)] let helper = 1; }",
        &[
            "missing_label",
            "unexpected_label",
            "invalid_generated_binding_name",
        ],
    );
    assert_codes(
        r#"unsafe fn f(mut flag: bool) {
#[proctor(0)] if todo!() {
#[proctor(1)] return;
}
}"#,
        r#"unsafe fn f(flag: bool) {
#[proctor(0)] while flag {
#[proctor(1)] let helper = 1;
}
}"#,
        &["control_kind_mismatch", "invalid_generated_binding_name"],
    );

    let response = validate(&request(
        r#"unsafe fn f() {
#[proctor(0)] let (mut z, mut a): (i32, i32) = todo!();
}"#,
        "unsafe fn f() { #[proctor(0)] consume((1, 2)); }",
    ));
    let ValidationResponse::Invalid { failures } = response else {
        panic!("expected declaration failures")
    };
    assert!(failures[0].errors[0].message.contains("`z`"));
    assert!(failures[0].errors[1].message.contains("`a`"));

    let response = validate(&request(
        r#"unsafe fn f(mut flag: bool) {
#[proctor(0)] if todo!() {
#[proctor(1)] return;
}
#[proctor(2)] return;
}"#,
        r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag {}
}"#,
    ));
    assert_eq!(codes(&response), ["missing_label", "missing_label"]);
    let ValidationResponse::Invalid { failures } = response else {
        panic!("expected label failures")
    };
    assert!(failures[0].errors[0].message.contains("label 1"));
    assert!(failures[0].errors[1].message.contains("label 2"));

    for transformation in [
        r#"unsafe fn f() {
#[proctor(1)] { #[proctor(1)] return; }
#[proctor(0)] { #[proctor(0)] return; }
}"#,
        r#"unsafe fn f() {
#[proctor(1)] return;
#[proctor(0)] return;
#[proctor(1)] return;
#[proctor(0)] return;
}"#,
    ] {
        let response = validate(&request(
            "unsafe fn f() { #[proctor(0)] return; #[proctor(1)] return; }",
            transformation,
        ));
        let ValidationResponse::Invalid { failures } = response else {
            panic!("expected label-order failures")
        };
        let ordered = failures[0]
            .errors
            .iter()
            .filter(|error| {
                matches!(
                    error.code.as_str(),
                    "nested_label_repetition" | "nonconsecutive_label"
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(ordered.len(), 2);
        assert!(ordered[0].message.contains("label 0"));
        assert!(ordered[1].message.contains("label 1"));
    }
}

#[test]
fn deep_multi_function_request_reports_only_failing_items() {
    let request = ValidationRequest {
        schema_version: 1,
        expected_functions: vec![
            expected_function(
                7,
                "leaf",
                "unsafe fn leaf(mut p: Option<&i32>) -> i32 { #[proctor(0)] let mut x: i32 = todo!(); #[proctor(1)] todo!() }",
            ),
            expected_function(
                8,
                "driver",
                r#"unsafe fn driver(mut flag: bool, mut p: Option<&i32>) -> i32 {
#[proctor(0)] let mut result: i32 = if todo!() { #[proctor(1)] todo!() } else { #[proctor(2)] todo!() };
#[proctor(3)] match todo!() { 0 => { #[proctor(4)] todo!() } _ => { #[proctor(5)] todo!() } }
}"#,
            ),
        ],
        transformation: r#"unsafe fn driver(flag: bool, p: Option<&i32>) -> i32 {
#[proctor(0)] let result: i32 = if flag { #[proctor(2)] 0 } else { #[proctor(1)] leaf(p) };
#[proctor(3)] match result { 0 => { #[proctor(4)] 0 } _ => { #[proctor(5)] result } }
}
unsafe fn leaf(p: Option<&i32>) -> i32 {
#[proctor(0)] let x: i32 = *p.unwrap();
#[proctor(1)] x
}"#
        .to_owned(),
    };
    let ValidationResponse::Invalid { failures } = validate(&request) else {
        panic!("expected invalid response");
    };
    assert_eq!(failures.len(), 1);
    assert_eq!(failures[0].id, Some(8));
    assert_eq!(
        failures[0]
            .errors
            .iter()
            .map(|error| error.code.as_str())
            .collect::<Vec<_>>(),
        [
            "descendant_location_mismatch",
            "descendant_location_mismatch"
        ]
    );
}
