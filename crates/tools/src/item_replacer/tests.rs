use utils::compilation::run_compiler_on_str;

use super::*;

fn request(path: &str, name: &str, transformation: &str) -> ReplacementRequest {
    ReplacementRequest {
        schema_version: 1,
        items: vec![ReplacementItem {
            id: 7,
            path: path.to_owned(),
            name: name.to_owned(),
        }],
        transformation: transformation.to_owned(),
    }
}

fn replace(source: &str, request: &ReplacementRequest) -> Result<String, ReplacementError> {
    run_compiler_on_str(source, |tcx| replace_items(source, request, tcx)).unwrap()
}

fn compile(source: &str) {
    run_compiler_on_str(source, |_| ()).unwrap();
}

fn compact(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn count(source: &str, needle: &str) -> usize {
    source.match_indices(needle).count()
}

#[test]
fn normalizes_every_non_main_free_function_and_is_idempotent() {
    let source = r#"
#![allow(dead_code)]
#[inline]
pub extern "C" fn root(value: i32) -> i32 { value }
pub unsafe fn already(value: i32) -> i32 { value + 1 }
#[no_mangle]
pub extern "C" fn exported(value: i32) -> i32 { value + 2 }
#[export_name = "renamed_alias"]
pub fn alias(value: i32) -> i32 { value + 3 }
pub fn r#type() -> i32 { 4 }
pub fn main() {}
mod outer {
    pub(crate) fn nested(value: i32) -> i32 { value + 5 }
    pub unsafe extern "C" fn already_unsafe(value: i32) -> i32 { value + 6 }
    pub fn r#main() {}
}
extern "C" { fn foreign(value: *const i32) -> i32; }
"#;
    let normalized = normalize_target_safety(source).unwrap();
    let text = compact(&normalized);
    for name in ["root", "exported", "alias", "r#type", "nested"] {
        assert!(
            text.contains(&format!("unsafe fn {name}"))
                || text.contains(&format!("unsafe extern \"C\" fn {name}"))
        );
    }
    assert!(text.contains("pub fn main()"));
    assert!(count(&text, "pub fn main()") >= 2);
    assert!(text.contains("fn foreign(value: *const i32)"));
    let twice = normalize_target_safety(&normalized).unwrap();
    assert_eq!(compact(&normalized), compact(&twice));
}

#[test]
fn whole_program_normalization_preserves_safe_main_and_compiles() {
    let source = r#"
pub fn callee(value: i32) -> i32 { value + 1 }
pub fn caller(value: i32) -> i32 { callee(value) }
unsafe fn main_0() -> core::ffi::c_int { caller(1) }
pub fn main() { unsafe { ::std::process::exit(main_0() as i32) } }
"#;
    let normalized = normalize_target_safety(source).unwrap();
    assert!(compact(&normalized).contains("pub fn main()"));
    compile(&normalized);
}

#[test]
fn versioned_request_json_round_trip_preserves_rust() {
    let json = r#"{
  "schema_version": 1,
  "items": [{"id":7,"path":"f","name":"f"}],
  "transformation": "unsafe fn f(value: i32) -> i32 {\n #[proctor(0)]\n value + 1\n}"
}"#;
    let request = replacement_request_from_json(json).unwrap();
    assert_eq!(request.schema_version, 1);
    assert!(request.transformation.contains("#[proctor(0)]"));
    let output = replace("pub unsafe fn f(value: i32) -> i32 { value }", &request).unwrap();
    assert!(compact(&output).contains("value + 1"));
}

#[test]
fn replaces_body_and_recursively_removes_only_proctor_labels() {
    let source = r#"
#![allow(dead_code)]
pub unsafe fn f(mut value: i32) -> i32 { value += 1; value }
pub unsafe fn untouched() -> i32 { 9 }
"#;
    let transformation = r#"
unsafe fn f(value: i32) -> i32 {
    #[proctor(0)]
    let result: i32 = if value > 0 {
        #[proctor(1)]
        value * 2
    } else {
        #[proctor(2)]
        { #[proctor(3)] 0 }
    };
    #[proctor(4)]
    result
}
"#;
    let output = replace(source, &request("f", "f", transformation)).unwrap();
    assert!(!output.contains("proctor"));
    assert!(compact(&output).contains("pub unsafe fn f(value: i32) -> i32"));
    assert!(compact(&output).contains("unsafe fn untouched() -> i32 { 9 }"));
    assert!(!output.contains("__proctor_wrapper_f"));
    compile(&output);
}

#[test]
fn private_wrapper_is_a_same_module_sibling() {
    let source = r#"
mod m {
    unsafe fn f(f: *const i32) -> i32 { *f }
    pub unsafe fn caller(value: *const i32) -> i32 { f(value) }
}
"#;
    let output = replace(
        source,
        &request(
            "m::f",
            "f",
            "unsafe fn f(f: &i32) -> i32 { #[proctor(0)] *f }",
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("unsafe fn __proctor_wrapper_f(f: *const i32) -> i32"));
    assert!(text.contains("crate::m::f(&*(f as *const i32))"));
    assert!(text.contains("crate::m::__proctor_wrapper_f(value)"));
    compile(&output);
}

#[test]
fn request_json_rejects_unknown_fields_and_non_u64_numbers() {
    for input in [
        r#"{"schema_version":1,"items":[{"id":7,"path":"f","name":"f"}],"transformation":"unsafe fn f() {}","extra":true}"#,
        r#"{"schema_version":1.0,"items":[{"id":7,"path":"f","name":"f"}],"transformation":"unsafe fn f() {}"}"#,
        r#"{"schema_version":1,"items":[{"id":-1,"path":"f","name":"f"}],"transformation":"unsafe fn f() {}"}"#,
        r#"{"schema_version":1,"items":[{"id":18446744073709551616,"path":"f","name":"f"}],"transformation":"unsafe fn f() {}"}"#,
    ] {
        assert_eq!(
            replacement_request_from_json(input).unwrap_err().kind,
            ReplacementErrorKind::InvalidRequest
        );
    }
}

#[test]
fn unsupported_version_and_empty_items_are_rejected() {
    for request in [
        ReplacementRequest {
            schema_version: 2,
            items: vec![ReplacementItem {
                id: 7,
                path: "f".to_owned(),
                name: "f".to_owned(),
            }],
            transformation: "unsafe fn f() {}".to_owned(),
        },
        ReplacementRequest {
            schema_version: 1,
            items: vec![],
            transformation: String::new(),
        },
    ] {
        assert_eq!(
            replace("pub unsafe fn f() {}", &request).unwrap_err().kind,
            ReplacementErrorKind::InvalidRequest
        );
    }
}

#[test]
fn duplicate_ids_paths_and_names_are_rejected_deterministically() {
    let source = "pub unsafe fn f() {} pub unsafe fn g() {}";
    for items in [
        vec![(7, "f", "f"), (7, "g", "g")],
        vec![(7, "f", "f"), (8, "f", "g")],
        vec![(7, "f", "f"), (8, "g", "f")],
    ] {
        let request = ReplacementRequest {
            schema_version: 1,
            items: items
                .into_iter()
                .map(|(id, path, name)| ReplacementItem {
                    id,
                    path: path.to_owned(),
                    name: name.to_owned(),
                })
                .collect(),
            transformation: "unsafe fn f() {} unsafe fn g() {}".to_owned(),
        };
        let first = replace(source, &request).unwrap_err();
        let second = replace(source, &request).unwrap_err();
        assert_eq!(first.kind, ReplacementErrorKind::InvalidRequest);
        assert_eq!(first, second);
    }
}

#[test]
fn path_name_disagreement_and_invalid_paths_are_rejected() {
    let source = "mod m { pub unsafe fn f() {} }";
    for (path, name) in [("m::f", "g"), ("", "f"), ("m::::f", "f")] {
        let error = replace(source, &request(path, name, "unsafe fn f() {}")).unwrap_err();
        assert_eq!(error.kind, ReplacementErrorKind::InvalidRequest);
    }
}

#[test]
fn transformation_must_be_exact_supported_requested_function_set() {
    let source = "pub unsafe fn f() {} pub unsafe fn g() {}";
    let items = vec![
        ReplacementItem {
            id: 7,
            path: "f".to_owned(),
            name: "f".to_owned(),
        },
        ReplacementItem {
            id: 8,
            path: "g".to_owned(),
            name: "g".to_owned(),
        },
    ];
    for transformation in [
        "unsafe fn f( {",
        "unsafe fn f() {}",
        "unsafe fn f() {} unsafe fn f() {} unsafe fn g() {}",
        "unsafe fn f() {} unsafe fn g() {} unsafe fn h() {}",
        "unsafe fn f() {} unsafe fn g() {} const EXTRA: i32 = 1;",
        "unsafe fn f(value: i32) { let _ = value; } unsafe fn g() {}",
        "async unsafe fn f() {} unsafe fn g() {}",
        "unsafe extern \"C\" fn f(mut count: i32, mut args: ...) { let _ = count; } unsafe fn g() {}",
    ] {
        let request = ReplacementRequest {
            schema_version: 1,
            items: items.clone(),
            transformation: transformation.to_owned(),
        };
        assert_eq!(
            replace(source, &request).unwrap_err().kind,
            ReplacementErrorKind::InvalidTransformation,
            "{transformation}"
        );
    }

    let unexpected = ReplacementRequest {
        schema_version: 1,
        items: vec![items[0].clone()],
        transformation: "unsafe fn f() {} unsafe fn z() {} unsafe fn a() {}".to_owned(),
    };
    for _ in 0..4 {
        assert!(
            replace(source, &unexpected)
                .unwrap_err()
                .message
                .contains("unexpected function `z`")
        );
    }

    let error = replace(
        "pub unsafe fn f(value: (i32, i32)) -> i32 { value.0 + value.1 }",
        &request(
            "f",
            "f",
            "unsafe fn f((left, right): (i32, i32)) -> i32 { #[proctor(0)] left + right }",
        ),
    )
    .unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::InvalidTransformation);
}

#[test]
fn preserves_current_header_properties_and_ignores_llm_header() {
    let source = r#"
#![allow(dead_code)]
#[inline(never)]
pub(crate) unsafe extern "C" fn f(mut value: i32) -> i32 { value }
"#;
    let output = replace(
        source,
        &request(
            "f",
            "f",
            r#"#[cold] pub const extern "system" fn f(value: i32) -> i32 {
                #[proctor(0)] value + 1
            }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("#[inline(never)] pub(crate) unsafe extern \"C\" fn f(value: i32)"));
    assert!(!text.contains("#[cold]"));
    assert!(!text.contains("const fn f"));
    assert!(!text.contains("system"));
}

#[test]
fn redundant_nested_type_parentheses_do_not_create_wrapper() {
    let source = r#"
pub unsafe fn f(value: Option<(*const i32)>) -> Option<(*const i32)> {
    value
}
"#;
    let output = replace(
        source,
        &request(
            "f",
            "f",
            r#"
unsafe fn f(value: Option<*const i32>) -> Option<*const i32> {
    #[proctor(0)]
    value
}
"#,
        ),
    )
    .unwrap();
    assert!(!output.contains("__proctor_wrapper_f"));
    compile(&output);
}

#[test]
fn replaces_exact_nested_full_path_without_touching_same_name() {
    let source = r#"
pub mod left { pub unsafe fn f(value: i32) -> i32 { value + 1 } }
pub mod right { pub unsafe fn f(value: i32) -> i32 { value + 2 } }
"#;
    let output = replace(
        source,
        &request(
            "right::f",
            "f",
            "unsafe fn f(value: i32) -> i32 { #[proctor(0)] value + 20 }",
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("value + 1"));
    assert!(text.contains("value + 20"));

    let raw_source = r#"
pub mod r#type {
    pub unsafe fn r#match(value: *const i32) -> i32 { *value }
    pub unsafe fn caller(value: *const i32) -> i32 { r#match(value) }
}"#;
    let raw_output = replace(
        raw_source,
        &request(
            "r#type::r#match",
            "r#match",
            "unsafe fn r#match(value: &i32) -> i32 { #[proctor(0)] *value + 1 }",
        ),
    )
    .unwrap();
    assert!(compact(&raw_output).contains("crate::r#type::__proctor_wrapper_match(value)"));
    compile(&raw_output);
}

#[test]
fn multiple_functions_match_by_name_and_replace_in_request_order() {
    let source = r#"
pub unsafe fn first(value: i32) -> i32 { value }
pub unsafe fn second(value: i32) -> i32 { value }
"#;
    let multi_request = ReplacementRequest {
        schema_version: 1,
        items: vec![
            ReplacementItem {
                id: 7,
                path: "first".to_owned(),
                name: "first".to_owned(),
            },
            ReplacementItem {
                id: 8,
                path: "second".to_owned(),
                name: "second".to_owned(),
            },
        ],
        transformation: r#"
unsafe fn second(value: i32) -> i32 { #[proctor(0)] value + 2 }
unsafe fn first(value: i32) -> i32 { #[proctor(0)] value + 1 }
"#
        .to_owned(),
    };
    let output = replace(source, &multi_request).unwrap();
    let text = compact(&output);
    assert!(text.find("value + 1").unwrap() < text.find("value + 2").unwrap());
}

#[test]
fn copies_validated_lifetime_generics_parameters_and_return() {
    let source = r#"
pub unsafe fn choose(first: *const i32, second: *const i32, take_first: bool) -> *const i32 {
    if take_first { first } else { second }
}
pub unsafe fn caller(first: *const i32, second: *const i32) -> *const i32 {
    choose(first, second, true)
}
"#;
    let transformation = r#"
unsafe fn choose<'a, 'b>(first: &'a i32, second: &'b i32, take_first: bool) -> &'a i32 {
    #[proctor(0)]
    if take_first { first } else { let _ = second; first }
}
"#;
    let output = replace(source, &request("choose", "choose", transformation)).unwrap();
    let text = compact(&output);
    assert!(text.contains("unsafe fn choose<'a, 'b>(first: &'a i32, second: &'b i32"));
    assert!(text.contains("crate::__proctor_wrapper_choose(first, second, true)"));
    compile(&output);
}

#[test]
fn source_target_resolution_and_normalized_safety_fail_atomically() {
    let missing = replace(
        "pub unsafe fn f() {}",
        &request("missing", "missing", "unsafe fn missing() {}"),
    )
    .unwrap_err();
    assert_eq!(missing.kind, ReplacementErrorKind::TargetResolution);
    assert_eq!(missing.item.unwrap().id, 7);

    let safe = replace("pub fn f() {}", &request("f", "f", "unsafe fn f() {}")).unwrap_err();
    assert_eq!(safe.kind, ReplacementErrorKind::TargetResolution);
}

#[test]
fn wrapper_preserves_restricted_visibility_in_nested_module() {
    let source = r#"
mod outer { pub(super) unsafe fn f(value: *mut i32) -> i32 { *value } }
pub unsafe fn caller(value: *mut i32) -> i32 { outer::f(value) }
"#;
    let output = replace(
        source,
        &request(
            "outer::f",
            "f",
            r#"unsafe fn f(value: &mut i32) -> i32 {
                #[proctor(0)] *value += 1;
                #[proctor(1)] *value
            }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("pub(super) unsafe fn f(value: &mut i32)"));
    assert!(text.contains("pub(super) unsafe fn __proctor_wrapper_f(value: *mut i32)"));
    assert!(text.contains("crate::outer::__proctor_wrapper_f(value)"));
    compile(&output);
}

#[test]
fn wrapper_name_collision_is_resolved_deterministically() {
    let source = r#"
mod m {
    pub unsafe fn __proctor_wrapper_f(value: *const i32) -> i32 { *value + 10 }
    pub unsafe fn __proctor_wrapper_f_0(value: *const i32) -> i32 { *value + 20 }
    pub unsafe fn f(value: *const i32) -> i32 { *value }
    pub unsafe fn caller(value: *const i32) -> i32 { f(value) }
}"#;
    let single_request = request(
        "m::f",
        "f",
        "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value }",
    );
    let first = replace(source, &single_request).unwrap();
    let second = replace(source, &single_request).unwrap();
    assert_eq!(first, second);
    assert!(compact(&first).contains("crate::m::__proctor_wrapper_f_1(value)"));

    let source = r#"
mod m {
    pub unsafe fn __proctor_wrapper_f(value: *const i32) -> i32 { *value + 10 }
    pub unsafe fn f(value: *const i32) -> i32 { *value }
    pub unsafe fn f_0(value: *const i32) -> i32 { *value }
    pub unsafe fn caller(value: *const i32) -> i32 { f(value) + f_0(value) }
}"#;
    let collision_request = ReplacementRequest {
        schema_version: 1,
        items: vec![
            ReplacementItem {
                id: 7,
                path: "m::f".to_owned(),
                name: "f".to_owned(),
            },
            ReplacementItem {
                id: 8,
                path: "m::f_0".to_owned(),
                name: "f_0".to_owned(),
            },
        ],
        transformation: r#"
unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value }
unsafe fn f_0(value: &i32) -> i32 { #[proctor(0)] *value }
"#
        .to_owned(),
    };
    let output = replace(source, &collision_request).unwrap();
    let text = compact(&output);
    assert!(text.contains("crate::m::__proctor_wrapper_f_0(value)"));
    assert!(text.contains("crate::m::__proctor_wrapper_f_0_0(value)"));

    let source = r#"
mod m {
    pub type __proctor_wrapper_g = i32;
    pub unsafe fn g(value: *const i32) -> i32 { *value }
    pub unsafe fn caller(value: *const i32) -> i32 { g(value) }
}"#;
    let output = replace(
        source,
        &request(
            "m::g",
            "g",
            "unsafe fn g(value: &i32) -> i32 { #[proctor(0)] *value }",
        ),
    )
    .unwrap();
    assert!(compact(&output).contains("crate::m::__proctor_wrapper_g_0(value)"));

    let source = r#"
pub unsafe fn helper(value: *const i32) -> i32 { *value }
mod imported {
    use crate::helper as __proctor_wrapper_f;
    pub unsafe fn f(value: *const i32) -> i32 { *value }
    pub unsafe fn caller(value: *const i32) -> i32 { f(value) }
}
"#;
    let output = replace(
        source,
        &request(
            "imported::f",
            "f",
            "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value }",
        ),
    )
    .unwrap();
    assert!(compact(&output).contains("crate::imported::__proctor_wrapper_f_0(value)"));
    compile(&output);

    let nested_use_names = with_parse_session(|| {
        let item =
            utils::ast::parse_item("use crate::{helper as __proctor_wrapper_nested};".to_owned());
        let mut names = HashSet::new();
        collect_occupied_item_names(&item, &mut names);
        Ok(names)
    })
    .unwrap();
    assert!(nested_use_names.contains("__proctor_wrapper_nested"));
    let nested_self_names = with_parse_session(|| {
        let item =
            utils::ast::parse_item("use crate::__proctor_wrapper_nested_self::{self};".to_owned());
        let mut names = HashSet::new();
        collect_occupied_item_names(&item, &mut names);
        Ok(names)
    })
    .unwrap();
    assert!(nested_self_names.contains("__proctor_wrapper_nested_self"));

    let source = r#"
mod foreign {
    unsafe extern "C" { fn __proctor_wrapper_g(value: *const i32) -> i32; }
    pub unsafe fn g(value: *const i32) -> i32 { *value }
    pub unsafe fn caller(value: *const i32) -> i32 { g(value) }
}
"#;
    let output = replace(
        source,
        &request(
            "foreign::g",
            "g",
            "unsafe fn g(value: &i32) -> i32 { #[proctor(0)] *value }",
        ),
    )
    .unwrap();
    assert!(compact(&output).contains("crate::foreign::__proctor_wrapper_g_0(value)"));
    compile(&output);
}

#[test]
fn no_mangle_moves_to_wrapper_as_original_export_name() {
    let source = r#"
#[no_mangle]
pub unsafe extern "C" fn exported(value: *const i32) -> i32 { *value }
"#;
    let output = replace(
        source,
        &request(
            "exported",
            "exported",
            "unsafe fn exported(value: &i32) -> i32 { #[proctor(0)] *value }",
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("pub unsafe fn exported(value: &i32)"));
    assert!(text.contains(
        "#[export_name = \"exported\"] pub unsafe extern \"C\" fn __proctor_wrapper_exported"
    ));
    assert!(!text.contains("#[no_mangle]"));

    let unchanged = replace(
        source,
        &request(
            "exported",
            "exported",
            "unsafe fn exported(value: *const i32) -> i32 { #[proctor(0)] *value + 1 }",
        ),
    )
    .unwrap();
    let unchanged = compact(&unchanged);
    assert!(unchanged.contains("#[no_mangle] pub unsafe extern \"C\" fn exported"));
    assert!(!unchanged.contains("__proctor_wrapper_exported"));
}

#[test]
fn explicit_export_name_moves_exactly_to_wrapper() {
    let source = r#"
#[export_name = "c_api_entry_v1"]
pub unsafe extern "C" fn internal_name(value: *mut i32) -> i32 { *value }
"#;
    let output = replace(
        source,
        &request(
            "internal_name",
            "internal_name",
            r#"unsafe fn internal_name(value: &mut i32) -> i32 {
                #[proctor(0)] *value += 1;
                #[proctor(1)] *value
            }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert_eq!(count(&text, "export_name = \"c_api_entry_v1\""), 1);
    assert!(text.contains("#[export_name = \"c_api_entry_v1\"] pub unsafe extern \"C\" fn __proctor_wrapper_internal_name"));
    assert!(text.contains("pub unsafe fn internal_name(value: &mut i32)"));

    let unchanged = replace(
        source,
        &request(
            "internal_name",
            "internal_name",
            "unsafe fn internal_name(value: *mut i32) -> i32 { #[proctor(0)] *value + 1 }",
        ),
    )
    .unwrap();
    assert!(!unchanged.contains("__proctor_wrapper_internal_name"));
    assert!(
        compact(&unchanged).contains(
            "#[export_name = \"c_api_entry_v1\"] pub unsafe extern \"C\" fn internal_name"
        )
    );
}

#[test]
fn explicit_abi_moves_even_without_export_attribute() {
    let source = r#"pub(crate) unsafe extern "C" fn f(value: *const i32) -> i32 { *value }"#;
    let output = replace(
        source,
        &request(
            "f",
            "f",
            "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value }",
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("pub(crate) unsafe fn f(value: &i32)"));
    assert!(text.contains("pub(crate) unsafe extern \"C\" fn __proctor_wrapper_f"));
    assert!(!text.contains("export_name"));
}

#[test]
fn nonexport_attributes_stay_only_on_implementation() {
    let source = r#"
#![allow(dead_code)]
#[inline(never)]
#[cold]
pub unsafe fn f(value: *const i32) -> i32 { *value }
"#;
    let output = replace(
        source,
        &request(
            "f",
            "f",
            r#"#[allow(unused_variables)]
            unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert_eq!(count(&text, "#[inline(never)]"), 1);
    assert_eq!(count(&text, "#[cold]"), 1);
    assert!(!text.contains("unused_variables"));

    let error = replace(
        r#"#[no_mangle] #[export_name = "x"] pub unsafe extern "C" fn f(value: *const i32) -> i32 { *value }"#,
        &request(
            "f",
            "f",
            "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value }",
        ),
    )
    .unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::TargetResolution);
}

#[test]
fn raw_inputs_convert_to_shared_and_mutable_references_unchecked() {
    let source = r#"
pub unsafe fn combine(left: *const i32, right: *mut i32) -> i32 {
    *right += *left; *right
}
pub unsafe fn caller(left: *const i32, right: *mut i32) -> i32 {
    combine(left, right)
}"#;
    let output = replace(
        source,
        &request(
            "combine",
            "combine",
            r#"unsafe fn combine(left: &i32, right: &mut i32) -> i32 {
                #[proctor(0)] *right += *left;
                #[proctor(1)] *right
            }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("&*(left as *const i32)"));
    assert!(text.contains("&mut *(right as *mut i32)"));
    assert!(!text.contains("left.is_null()"));
    compile(&output);
}

#[test]
fn raw_inputs_convert_to_optional_references_by_nullity() {
    let source = r#"
pub unsafe fn choose(left: *const i32, right: *mut i32) -> i32 {
    if left.is_null() { 0 } else if right.is_null() { *left } else { *left + *right }
}
pub unsafe fn caller(left: *const i32, right: *mut i32) -> i32 { choose(left, right) }
"#;
    let output = replace(
        source,
        &request(
            "choose",
            "choose",
            r#"unsafe fn choose(left: Option<&i32>, right: Option<&mut i32>) -> i32 {
                #[proctor(0)] left.copied().unwrap_or(0) + right.map(|value| *value).unwrap_or(0)
            }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("(left as *const i32).as_ref()"));
    assert!(text.contains("(right as *mut i32).as_mut()"));
    compile(&output);
}

#[test]
fn raw_inputs_convert_to_slices_with_null_empty_and_fixed_bound() {
    let source = r#"
pub unsafe fn sum(first: *const i32, second: *mut i32) -> i32 {
    let left = if first.is_null() { 0 } else { *first };
    let right = if second.is_null() { 0 } else { *second };
    left + right
}
pub unsafe fn caller(first: *const i32, second: *mut i32) -> i32 { sum(first, second) }
"#;
    let output = replace(
        source,
        &request(
            "sum",
            "sum",
            r#"unsafe fn sum(first: &[i32], second: &mut [i32]) -> i32 {
                #[proctor(0)] first.first().copied().unwrap_or(0) + second.first().copied().unwrap_or(0)
            }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("if first.is_null() { &[] } else { std::slice::from_raw_parts(first as *const i32, 1_000_000) }"));
    assert!(text.contains("if second.is_null() { &mut [] } else { std::slice::from_raw_parts_mut(second as *mut i32, 1_000_000) }"));
    compile(&output);
}

#[test]
fn raw_inputs_convert_to_box_and_optional_box() {
    let source = r#"
pub unsafe fn consume(owned: *mut i32, optional: *mut i32) -> i32 {
    let first = *owned;
    let second = if optional.is_null() { 0 } else { *optional };
    first + second
}
pub unsafe fn caller(owned: *mut i32, optional: *mut i32) -> i32 { consume(owned, optional) }
"#;
    let output = replace(
        source,
        &request(
            "consume",
            "consume",
            r#"unsafe fn consume(owned: Box<i32>, optional: Option<Box<i32>>) -> i32 {
                #[proctor(0)] *owned + optional.map(|value| *value).unwrap_or(0)
            }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("Box::from_raw(owned as *mut i32)"));
    assert!(text.contains(
        "if optional.is_null() { None } else { Some(Box::from_raw(optional as *mut i32)) }"
    ));
    compile(&output);
}

#[test]
fn raw_cast_passthrough_and_unsupported_input_pairs() {
    let source = r#"
pub unsafe fn f(pointer: *mut i32, count: usize) -> usize {
    if pointer.is_null() { 0 } else { count }
}
pub unsafe fn caller(pointer: *mut i32, count: usize) -> usize { f(pointer, count) }
"#;
    let output = replace(
        source,
        &request(
            "f",
            "f",
            r#"unsafe fn f(pointer: *const i32, count: usize) -> usize {
                #[proctor(0)] if pointer.is_null() { 0 } else { count }
            }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("pointer as *const i32, count"));
    compile(&output);

    for transformation in [
        "unsafe fn f(pointer: Box<[i32]>) { #[proctor(0)] drop(pointer); }",
        "unsafe fn f(pointer: Option<Box<[i32]>>) { #[proctor(0)] drop(pointer); }",
        "unsafe fn f(pointer: usize) { #[proctor(0)] let _ = pointer; }",
    ] {
        let error = replace(
            "pub unsafe fn f(pointer: *mut i32) {}",
            &request("f", "f", transformation),
        )
        .unwrap_err();
        assert_eq!(error.kind, ReplacementErrorKind::UnsupportedConversion);
    }
}

#[test]
fn reference_outputs_cast_to_exact_raw_pointer_type() {
    for (source, transformation, expected) in [
        (
            "pub unsafe fn identity(value: *mut i32) -> *mut i32 { value } pub unsafe fn caller(value: *mut i32) -> *mut i32 { identity(value) }",
            "unsafe fn identity<'a>(value: &'a mut i32) -> &'a mut i32 { #[proctor(0)] value }",
            "__proctor_result as *mut i32 as *mut i32",
        ),
        (
            "pub unsafe fn identity(value: *mut i32) -> *mut i32 { value }",
            "unsafe fn identity<'a>(value: &'a i32) -> &'a i32 { #[proctor(0)] value }",
            "__proctor_result as *const i32 as *mut i32",
        ),
        (
            "pub unsafe fn identity(value: *const i32) -> *const i32 { value }",
            "unsafe fn identity<'a>(value: &'a mut i32) -> &'a mut i32 { #[proctor(0)] value }",
            "__proctor_result as *mut i32 as *const i32",
        ),
    ] {
        let output = replace(source, &request("identity", "identity", transformation)).unwrap();
        assert!(compact(&output).contains(expected));
        assert_eq!(count(&output, "crate::identity("), 1);
        compile(&output);
    }
}

#[test]
fn optional_reference_outputs_map_none_to_typed_null() {
    for (source, transformation, null, cast) in [
        (
            "pub unsafe fn maybe(value: *const i32, present: bool) -> *const i32 { if present { value } else { core::ptr::null() } }",
            "unsafe fn maybe<'a>(value: &'a i32, present: bool) -> Option<&'a i32> { #[proctor(0)] if present { Some(value) } else { None } }",
            "std::ptr::null::<i32>() as *const i32",
            "as *const i32 as *const i32",
        ),
        (
            "pub unsafe fn maybe(value: *mut i32, present: bool) -> *mut i32 { if present { value } else { core::ptr::null_mut() } }",
            "unsafe fn maybe<'a>(value: &'a mut i32, present: bool) -> Option<&'a mut i32> { #[proctor(0)] if present { Some(value) } else { None } }",
            "std::ptr::null_mut::<i32>() as *mut i32",
            "as *mut i32 as *mut i32",
        ),
        (
            "pub unsafe fn maybe(value: *mut i32, present: bool) -> *mut i32 { if present { value } else { core::ptr::null_mut() } }",
            "unsafe fn maybe<'a>(value: &'a i32, present: bool) -> Option<&'a i32> { #[proctor(0)] if present { Some(value) } else { None } }",
            "std::ptr::null_mut::<i32>() as *mut i32",
            "as *const i32 as *mut i32",
        ),
        (
            "pub unsafe fn maybe(value: *const i32, present: bool) -> *const i32 { if present { value } else { core::ptr::null() } }",
            "unsafe fn maybe<'a>(value: &'a mut i32, present: bool) -> Option<&'a mut i32> { #[proctor(0)] if present { Some(value) } else { None } }",
            "std::ptr::null::<i32>() as *const i32",
            "as *mut i32 as *const i32",
        ),
    ] {
        let output = replace(source, &request("maybe", "maybe", transformation)).unwrap();
        let text = compact(&output);
        assert!(text.contains(null));
        assert!(text.contains(cast));
        compile(&output);
    }
}

#[test]
fn slice_outputs_map_empty_to_null_and_nonempty_to_data_pointer() {
    for (source_pointer, transformation, null, pointer) in [
        (
            "*const i32",
            "unsafe fn prefix<'a>(value: &'a [i32]) -> &'a [i32] { #[proctor(0)] if value.is_empty() { &value[..0] } else { value } }",
            "null::<i32>() as *const i32",
            "as_ptr() as *const i32",
        ),
        (
            "*mut i32",
            "unsafe fn prefix<'a>(value: &'a mut [i32]) -> &'a mut [i32] { #[proctor(0)] value }",
            "null_mut::<i32>() as *mut i32",
            "as_mut_ptr() as *mut i32",
        ),
        (
            "*mut i32",
            "unsafe fn prefix<'a>(value: &'a [i32]) -> &'a [i32] { #[proctor(0)] value }",
            "null_mut::<i32>() as *mut i32",
            "as_ptr() as *mut i32",
        ),
        (
            "*const i32",
            "unsafe fn prefix<'a>(value: &'a mut [i32]) -> &'a mut [i32] { #[proctor(0)] value }",
            "null::<i32>() as *const i32",
            "as_mut_ptr() as *const i32",
        ),
    ] {
        let source = format!(
            "pub unsafe fn prefix(value: {source_pointer}) -> {source_pointer} {{ value }}"
        );
        let output = replace(&source, &request("prefix", "prefix", transformation)).unwrap();
        let text = compact(&output);
        assert!(text.contains(null));
        assert!(text.contains(pointer));
        assert!(text.contains("1_000_000"));
        compile(&output);
    }
}

#[test]
fn box_and_optional_box_outputs_use_into_raw() {
    for (source_pointer, transformation, null) in [
        (
            "*mut i32",
            "unsafe fn make() -> Box<i32> { #[proctor(0)] Box::new(2) }",
            None,
        ),
        (
            "*mut i32",
            "unsafe fn make(present: bool) -> Option<Box<i32>> { #[proctor(0)] if present { Some(Box::new(2)) } else { None } }",
            Some("null_mut::<i32>() as *mut i32"),
        ),
        (
            "*const i32",
            "unsafe fn make() -> Box<i32> { #[proctor(0)] Box::new(2) }",
            None,
        ),
        (
            "*const i32",
            "unsafe fn make(present: bool) -> Option<Box<i32>> { #[proctor(0)] if present { Some(Box::new(2)) } else { None } }",
            Some("null::<i32>() as *const i32"),
        ),
    ] {
        let has_param = transformation.contains("present:");
        let source = if has_param {
            format!(
                "pub unsafe fn make(present: bool) -> {source_pointer} {{ if present {{ Box::into_raw(Box::new(1)) as {source_pointer} }} else {{ core::ptr::null_mut() as {source_pointer} }} }}"
            )
        } else {
            format!(
                "pub unsafe fn make() -> {source_pointer} {{ Box::into_raw(Box::new(1)) as {source_pointer} }}"
            )
        };
        let output = replace(&source, &request("make", "make", transformation)).unwrap();
        let text = compact(&output);
        assert!(
            text.contains(&format!(
                "Box::into_raw(__proctor_result) as {source_pointer}"
            )) || text.contains(&format!(
                "Box::into_raw(__proctor_result) as {source_pointer}"
            ))
        );
        if let Some(null) = null {
            assert!(text.contains(null));
        }
        compile(&output);
    }
}

#[test]
fn boxed_slice_outputs_drop_empty_and_leak_nonempty() {
    for (source_pointer, optional) in [
        ("*mut i32", false),
        ("*mut i32", true),
        ("*const i32", false),
        ("*const i32", true),
    ] {
        let (source, transformation) = if optional {
            (
                format!(
                    "pub unsafe fn make(kind: i32) -> {source_pointer} {{ let _ = kind; core::ptr::null_mut() as {source_pointer} }}"
                ),
                r#"unsafe fn make(kind: i32) -> Option<Box<[i32]>> {
                    #[proctor(0)] match kind {
                        0 => None,
                        1 => Some(Vec::<i32>::new().into_boxed_slice()),
                        _ => Some(vec![1, 2].into_boxed_slice()),
                    }
                }"#,
            )
        } else {
            (
                format!(
                    "pub unsafe fn make(empty: bool) -> {source_pointer} {{ let _ = empty; core::ptr::null_mut() as {source_pointer} }}"
                ),
                r#"unsafe fn make(empty: bool) -> Box<[i32]> {
                    #[proctor(0)] if empty {
                        Vec::<i32>::new().into_boxed_slice()
                    } else {
                        vec![1, 2].into_boxed_slice()
                    }
                }"#,
            )
        };
        let output = replace(&source, &request("make", "make", transformation)).unwrap();
        let text = compact(&output);
        assert!(text.contains("drop(__proctor_result)"));
        assert!(text.contains("Box::leak(__proctor_result).as_mut_ptr()"));
        if source_pointer.starts_with("*const") {
            assert!(text.contains("null::<i32>() as *const i32"));
        } else {
            assert!(text.contains("null_mut::<i32>() as *mut i32"));
        }
        compile(&output);
    }
}

#[test]
fn raw_nonpointer_unit_and_single_evaluation_outputs() {
    let raw = replace(
        "pub unsafe fn raw(value: *mut i32) -> *mut i32 { value }",
        &request(
            "raw",
            "raw",
            "unsafe fn raw(value: *const i32) -> *const i32 { #[proctor(0)] value }",
        ),
    )
    .unwrap();
    assert!(compact(&raw).contains("__proctor_result as *mut i32"));
    compile(&raw);

    let count_output = replace(
        "pub unsafe fn count(value: i32) -> i32 { value }",
        &request(
            "count",
            "count",
            "unsafe fn count(value: i32) -> i32 { #[proctor(0)] value + 1 }",
        ),
    )
    .unwrap();
    assert!(!count_output.contains("__proctor_wrapper_count"));

    let touch = replace(
        "pub unsafe fn touch(value: *const i32) { let _ = *value; }",
        &request(
            "touch",
            "touch",
            "unsafe fn touch(value: &i32) { #[proctor(0)] let _ = *value; }",
        ),
    )
    .unwrap();
    assert!(touch.contains("__proctor_wrapper_touch"));
    assert!(!touch.contains("__proctor_result"));
    assert_eq!(count(&touch, "crate::touch("), 1);
    compile(&touch);
}

#[test]
fn aliases_multiple_calls_and_nested_expressions_rewrite_by_resolution() {
    let source = r#"
mod m { pub(crate) unsafe fn f(value: *const i32) -> i32 { *value } }
use m::f as alias;
pub unsafe fn caller(value: *const i32, flag: bool) -> i32 {
    let first = alias(value);
    if flag { first + m::f(value) } else { core::cmp::max(alias(value), 0) }
}"#;
    let output = replace(
        source,
        &request(
            "m::f",
            "f",
            "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value }",
        ),
    )
    .unwrap();
    assert_eq!(count(&output, "crate::m::__proctor_wrapper_f(value)"), 3);
    assert!(compact(&output).contains("use m::f as alias;"));
    compile(&output);
}

#[test]
fn self_super_crate_and_fully_qualified_calls_rewrite() {
    let source = r#"
pub(crate) mod outer {
    pub(crate) mod inner {
        pub(crate) unsafe fn f(value: *const i32) -> i32 { *value }
        pub(crate) unsafe fn via_self(value: *const i32) -> i32 { self::f(value) }
    }
    pub(crate) unsafe fn via_child(value: *const i32) -> i32 { inner::f(value) }
    pub(crate) mod sibling {
        pub(crate) unsafe fn via_super(value: *const i32) -> i32 { super::inner::f(value) }
    }
}
pub unsafe fn via_crate(value: *const i32) -> i32 { crate::outer::inner::f(value) }
"#;
    let output = replace(
        source,
        &request(
            "outer::inner::f",
            "f",
            "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value }",
        ),
    )
    .unwrap();
    assert_eq!(
        count(&output, "crate::outer::inner::__proctor_wrapper_f(value)"),
        4
    );
    compile(&output);
}

#[test]
fn mutually_recursive_scc_calls_stay_direct_while_external_calls_redirect() {
    let source = r#"
pub unsafe fn even(value: *const i32, n: i32) -> i32 {
    if n == 0 { *value } else { odd(value, n - 1) }
}
pub unsafe fn odd(value: *const i32, n: i32) -> i32 {
    if n == 0 { *value } else { even(value, n - 1) }
}
pub unsafe fn caller(value: *const i32) -> i32 { even(value, 4) + odd(value, 3) }
"#;
    let scc_request = ReplacementRequest {
        schema_version: 1,
        items: vec![
            ReplacementItem {
                id: 7,
                path: "even".to_owned(),
                name: "even".to_owned(),
            },
            ReplacementItem {
                id: 8,
                path: "odd".to_owned(),
                name: "odd".to_owned(),
            },
        ],
        transformation: r#"
unsafe fn odd(value: &i32, n: i32) -> i32 {
    #[proctor(0)] if n == 0 { *value } else { even(value, n - 1) }
}
unsafe fn even(value: &i32, n: i32) -> i32 {
    #[proctor(0)] if n == 0 { *value } else { odd(value, n - 1) }
}"#
        .to_owned(),
    };
    let output = replace(source, &scc_request).unwrap();
    let text = compact(&output);
    assert!(text.contains("odd(value, n - 1)"));
    assert!(text.contains("even(value, n - 1)"));
    assert!(text.contains("crate::__proctor_wrapper_even(value, 4)"));
    assert!(text.contains("crate::__proctor_wrapper_odd(value, 3)"));
    compile(&output);

    let initial = r#"
pub unsafe fn callee(value: *const i32) -> i32 { *value }
pub unsafe fn caller(value: *const i32) -> i32 { callee(value) }
pub unsafe fn top(value: *const i32) -> i32 { caller(value) }
"#;
    let first = replace(
        initial,
        &request(
            "callee",
            "callee",
            "unsafe fn callee(value: &i32) -> i32 { #[proctor(0)] *value }",
        ),
    )
    .unwrap();
    compile(&first);
    let second = replace(
        &first,
        &request(
            "caller",
            "caller",
            "unsafe fn caller(value: &i32) -> i32 { #[proctor(0)] callee(value) }",
        ),
    )
    .unwrap();
    let text = compact(&second);
    assert!(text.contains("unsafe fn caller(value: &i32) -> i32 { callee(value) }"));
    assert!(text.contains("crate::__proctor_wrapper_caller(value)"));
    assert_eq!(count(&text, "crate::__proctor_wrapper_callee(value)"), 0);
    assert!(second.contains("__proctor_wrapper_callee"));
    compile(&second);
}

#[test]
fn direct_recursion_stays_direct_and_wrapper_call_is_not_rewritten() {
    let source = r#"
pub unsafe fn recurse(value: *const i32, n: i32) -> i32 {
    if n == 0 { *value } else { recurse(value, n - 1) }
}
pub unsafe fn caller(value: *const i32) -> i32 { recurse(value, 2) }
"#;
    let output = replace(
        source,
        &request(
            "recurse",
            "recurse",
            r#"unsafe fn recurse(value: &i32, n: i32) -> i32 {
                #[proctor(0)] if n == 0 { *value } else { recurse(value, n - 1) }
            }"#,
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("recurse(value, n - 1)"));
    assert!(text.contains("crate::__proctor_wrapper_recurse(value, 2)"));
    assert_eq!(count(&output, "crate::recurse("), 1);
    compile(&output);
}

#[test]
fn unchanged_signature_needs_no_rewrite_and_macro_input_call_errors() {
    let source = r#"
pub unsafe fn f(value: *const i32) -> i32 { *value }
pub unsafe fn caller(value: *const i32) -> i32 { dbg!(f(value)) }
"#;
    let unchanged = replace(
        source,
        &request(
            "f",
            "f",
            "unsafe fn f(value: *const i32) -> i32 { #[proctor(0)] *value + 1 }",
        ),
    )
    .unwrap();
    assert!(compact(&unchanged).contains("dbg!(f(value))"));
    assert!(!unchanged.contains("__proctor_wrapper_f"));

    let error = replace(
        source,
        &request(
            "f",
            "f",
            "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value + 1 }",
        ),
    )
    .unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::UnsupportedCallRewrite);

    let aliased_source = r#"
pub unsafe fn f(value: *const i32) -> i32 { *value }
use f as renamed;
pub unsafe fn caller(value: *const i32) -> i32 { dbg!(renamed(value)) }
"#;
    let error = replace(
        aliased_source,
        &request(
            "f",
            "f",
            "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value + 1 }",
        ),
    )
    .unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::UnsupportedCallRewrite);
    assert_eq!(error.item.unwrap().path, "f");

    let expansion_only_source = r#"
macro_rules! call {
    ($callee:path, $value:expr) => { $callee($value) };
}
pub unsafe fn f(value: *const i32) -> i32 { *value }
pub unsafe fn caller(value: *const i32) -> i32 { call!(f, value) }
"#;
    let output = replace(
        expansion_only_source,
        &request(
            "f",
            "f",
            "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value + 1 }",
        ),
    )
    .unwrap();
    assert!(output.contains("call!(f, value)"));

    let mixed_expansion_source = r#"
macro_rules! call_f {
    ($unused:expr, $value:expr) => { f($value) };
}
pub unsafe fn f(value: *const i32) -> i32 { *value }
pub unsafe fn caller(value: *const i32) -> i32 { call_f!(Some(value), value) }
"#;
    let output = replace(
        mixed_expansion_source,
        &request(
            "f",
            "f",
            "unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value + 1 }",
        ),
    )
    .unwrap();
    assert!(output.contains("call_f!(Some(value), value)"));
}

#[test]
fn zero_argument_main_0_leaves_excluded_main_unchanged() {
    let source = r#"
unsafe fn main_0() -> core::ffi::c_int { 0 }
pub fn main() { unsafe { ::std::process::exit(main_0() as i32) } }
"#;
    let output = replace(
        source,
        &request(
            "main_0",
            "main_0",
            "unsafe fn main_0() -> core::ffi::c_int { #[proctor(0)] 1 }",
        ),
    )
    .unwrap();
    let text = compact(&output);
    assert!(text.contains("unsafe fn main_0() -> core::ffi::c_int { 1 }"));
    assert!(text.contains("pub fn main() { unsafe { ::std::process::exit(main_0() as i32) } }"));
    assert!(!text.contains("__proctor_wrapper_main_0"));
    compile(&output);
}

#[test]
fn two_argument_main_0_uses_fixed_main_and_never_wraps() {
    let source = r#"
unsafe fn main_0(
    argc: core::ffi::c_int,
    argv: *mut *mut core::ffi::c_char,
) -> core::ffi::c_int {
    let _ = argv; argc
}
pub fn main() {
    let mut command_line_args: Vec<*mut core::ffi::c_char> = Vec::new();
    for arg in ::std::env::args() {
        command_line_args.push(::std::ffi::CString::new(arg).unwrap().into_raw());
    }
    command_line_args.push(::core::ptr::null_mut());
    unsafe {
        ::std::process::exit(main_0(
            (command_line_args.len() - 1) as core::ffi::c_int,
            command_line_args.as_mut_ptr() as *mut *mut core::ffi::c_char,
        ) as i32)
    }
}"#;
    let transformation = r#"
unsafe fn main_0(argc: core::ffi::c_int, argv: &mut [&mut [i8]]) -> core::ffi::c_int {
    #[proctor(0)] let _ = argv;
    #[proctor(1)] argc
}"#;
    let output = replace(source, &request("main_0", "main_0", transformation)).unwrap();
    let text = compact(&output);
    assert!(!text.contains("__proctor_wrapper_main_0"));
    assert!(text.contains("into_bytes_with_nul()"));
    assert!(text.contains("let argc = command_line_arg_storage.len() as core::ffi::c_int;"));
    assert!(text.contains("command_line_arg_slices.push(&mut argv_terminator);"));
    assert!(text.contains("main_0(argc, command_line_arg_slices.as_mut_slice())"));
    compile(&output);

    let nested = r#"
pub mod app {
    pub(crate) unsafe fn main_0(mut argc: core::ffi::c_int, mut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int {
        let _ = argv; argc
    }
    pub fn main() { unsafe { ::std::process::exit(main_0(0, core::ptr::null_mut()) as i32) } }
}
pub mod distractor {
    pub unsafe fn main_0() -> core::ffi::c_int { 9 }
    pub fn main() { unsafe { ::std::process::exit(main_0() as i32) } }
}"#;
    let nested_output = replace(
        nested,
        &request(
            "app::main_0",
            "main_0",
            r#"unsafe fn main_0(mut argc: core::ffi::c_int, mut argv: &mut [&mut [i8]]) -> core::ffi::c_int {
                #[proctor(0)] let _ = argv;
                #[proctor(1)] argc
            }"#,
        ),
    )
    .unwrap();
    let nested_text = compact(&nested_output);
    assert_eq!(count(&nested_text, "into_bytes_with_nul()"), 1);
    assert!(nested_text.contains("pub unsafe fn main_0() -> core::ffi::c_int { 9 }"));
    compile(&nested_output);
}

#[test]
fn one_unsupported_item_aborts_multi_item_transaction() {
    let source = r#"
pub unsafe fn good(value: *const i32) -> i32 { *value }
pub unsafe fn bad(value: *mut i32) { let _ = value; }
pub unsafe fn caller(value: *mut i32) -> i32 { good(value) + { bad(value); 0 } }
"#;
    let request = ReplacementRequest {
        schema_version: 1,
        items: vec![
            ReplacementItem {
                id: 7,
                path: "good".to_owned(),
                name: "good".to_owned(),
            },
            ReplacementItem {
                id: 8,
                path: "bad".to_owned(),
                name: "bad".to_owned(),
            },
        ],
        transformation: r#"
unsafe fn good(value: &i32) -> i32 { #[proctor(0)] *value }
unsafe fn bad(value: Box<[i32]>) { #[proctor(0)] drop(value); }
"#
        .to_owned(),
    };
    let error = replace(source, &request).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::UnsupportedConversion);
    assert_eq!(error.item.unwrap().id, 8);
}
