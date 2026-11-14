use utils::compilation::run_compiler_on_str;

use super::*;

fn freeze(source: &str) -> FrozenProject {
    run_compiler_on_str(source, |tcx| {
        let records = crate::make_skeletons(source, tcx).unwrap();
        freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap()
}

#[test]
fn local_declarations_preserve_headers_and_keep_initializers_opaque() {
    let source = r#"
pub unsafe fn run(p: *mut i32) -> i32 {
    #[allow(dead_code)] const VALUE: i32 = { let original = 1; original };
    static mut STATE: i32 = { let original = 2; original };
    use core::{mem::size_of, hint::black_box};
    unsafe extern "C" { fn abs(value: i32) -> i32; }
    *p + VALUE + STATE
}
"#;
    let frozen = freeze(source);
    let function = &frozen.functions[0];
    assert_eq!(function.record.baseline.transform_labels(), vec![0, 1, 4]);
    assert_eq!(
        function
            .record
            .annotated_source
            .matches("#[proctor(")
            .count(),
        5
    );
    assert!(!function.record.baseline.skeleton.contains("original"));
    let returned = format!(
        r#"{} {{
        #[proctor(0)] #[allow(dead_code)] const VALUE: i32 = {{
            const fn helper() -> i32 {{ 1 }}
            let freely_named = helper();
            unsafe {{ freely_named }}
        }};
        #[proctor(1)] static mut STATE: i32 = {{ let freely_named: i32 = 2; freely_named }};
        #[proctor(2)] use nonexistent::ignored;
        #[proctor(3)] unsafe extern "C" {{ fn changed(); }}
        #[proctor(4)] *p + VALUE + STATE
    }}"#,
        function.record.target_signature
    );
    let replacement_request = request(function, Some(&returned));
    assert_eq!(
        crate::validate(&crate::ValidationRequest {
            expected_functions: vec![crate::ExpectedFunction {
                id: function.record.id,
                name: function.record.name.clone(),
                view: function.record.baseline.clone()
            }],
            transformation: returned.clone(),
        }),
        crate::ValidationResponse::Valid
    );
    let (output, metadata) = metadata(&frozen, &replacement_request);
    assert!(!output.replacement.source.contains("nonexistent"));
    assert!(!output.replacement.source.contains("fn changed"));
    run_compiler_on_str(&output.replacement.source, utils::type_check).unwrap();
    let observations =
        crate::observation::extract_observations_from_source(&output.observation_source, &metadata)
            .unwrap();
    assert!(!observations.observations.is_empty());
    for changed in [
        returned.replace("const VALUE", "const OTHER"),
        returned.replace("VALUE: i32", "VALUE: i64"),
        returned.replace("static mut STATE", "static STATE"),
        returned.replace("const VALUE", "static VALUE"),
        returned.replace("#[allow(dead_code)]", "#[allow(unused)]"),
        returned.replace(
            "let freely_named = helper();",
            "#[proctor(99)] let freely_named = helper();",
        ),
        returned.replace(
            "#[proctor(1)] static",
            "#[proctor(0)] let proctor_temp_var_0 = 1; #[proctor(1)] static",
        ),
    ] {
        assert!(
            transform_frozen_scc(&frozen, &request(function, Some(&changed))).is_err(),
            "{changed}"
        );
    }
}

#[test]
fn local_value_headers_protect_named_types_in_candidates_and_observations() {
    let source = r#"
pub struct Holder { p: *mut i32 }
pub unsafe fn run(p: *mut i32) -> i32 {
    const VALUE: ([u8; { const ZERO: usize = 0; ZERO }], Holder) = ([], Holder { p: core::ptr::null_mut() });
    static mut STATE: i32 = 2;
    *p
}
pub unsafe fn read(value: Holder) -> i32 { *value.p }
"#;
    let frozen = freeze(source);
    let holder = &frozen.types[0];
    assert_eq!(holder.source_definition, holder.target_definition);
    let function = frozen
        .functions
        .iter()
        .find(|function| function.record.name == "run")
        .unwrap();
    let returned = function
        .record
        .baseline
        .skeleton
        .replacen("todo!()", "([], Holder { p: core::ptr::null_mut() })", 1)
        .replacen("todo!()", "2", 1)
        .replace("todo!()", "*p");
    let (output, metadata) = metadata(&frozen, &request(function, Some(&returned)));
    run_compiler_on_str(&output.replacement.source, utils::type_check).unwrap();
    crate::observation::extract_observations_from_source(&output.observation_source, &metadata)
        .unwrap();
}

#[test]
fn unstructured_bodies_allow_local_items_attributes_unsafe_and_nested_todo() {
    let frozen = freeze(
        "#[inline] pub unsafe fn run(value: i32) -> i32 { #![allow(dead_code)] const UNUSED: i32 = 0; value }",
    );
    let function = &frozen.functions[0];
    let returned = format!(
        r#"{} {{
        #![allow(unused_variables)]
        #[allow(dead_code)] fn helper(value: i32) -> i32 {{ value }}
        struct Local(i32);
        const NUMBER: i32 = 1;
        static mut STATE: i32 = 0;
        use core::mem::size_of;
        unsafe extern "C" {{ fn abs(value: i32) -> i32; }}
        if value < 0 {{ todo!() }}
        #[allow(unused_unsafe)] unsafe {{ STATE = NUMBER; }}
        helper(Local(value).0) + size_of::<i32>() as i32
    }}"#,
        function.record.target_signature
    );
    let output = replace_unstructured_scc(
        &frozen,
        &UnstructuredReplacementRequest {
            members: vec![function.record.id],
            transformation: returned.clone(),
        },
    )
    .unwrap();
    assert!(output.source.contains("#[inline]"));
    assert!(output.source.contains("#![allow(unused_variables)]"));
    assert!(!output.source.contains("#![allow(dead_code)]"));
    assert!(!output.source.contains("UNUSED"));
    run_compiler_on_str(&output.source, utils::type_check).unwrap();
    let assembled = assemble_frozen_project(
        &frozen,
        &[AcceptedScc {
            members: vec![function.record.id],
            source: output.source.clone(),
            stubbed_items: vec![],
        }],
    )
    .unwrap();
    assert!(assembled.contains("#![allow(unused_variables)]"));
    run_compiler_on_str(&assembled, utils::type_check).unwrap();
    assert!(
        assemble_frozen_project(
            &frozen,
            &[AcceptedScc {
                members: vec![function.record.id],
                source: frozen
                    .target_source
                    .replace("todo!()", "#![allow(unused_variables)] todo!()"),
                stubbed_items: vec![],
            }]
        )
        .is_err()
    );
    let retained = retain_frozen_functions(
        &frozen,
        &UnstructuredPreparationRequest {
            members: vec![function.record.id],
            transformations: vec![returned],
        },
    )
    .unwrap();
    assert!(retained.source.contains("#![allow(unused_variables)]"));
    assert!(!retained.source.contains("#![allow(dead_code)]"));
    run_compiler_on_str(&retained.source, utils::type_check).unwrap();
    assert!(
        replace_unstructured_scc(
            &frozen,
            &UnstructuredReplacementRequest {
                members: vec![function.record.id],
                transformation: function
                    .record
                    .baseline
                    .skeleton
                    .replace("value", "renamed"),
            }
        )
        .is_err()
    );
    assert!(
        replace_unstructured_scc(
            &frozen,
            &UnstructuredReplacementRequest {
                members: vec![function.record.id],
                transformation: format!("{} {{ todo!() }}", function.record.target_signature),
            }
        )
        .is_err()
    );
}

#[test]
fn generic_functions_keep_signatures_and_rewrite_bodies_without_skeletons() {
    let source = r#"
pub unsafe fn read(p: *mut i32) -> i32 { *p }
#[inline]
pub unsafe fn generic<T: Copy>(p: *mut i32, value: T) -> T where T: PartialEq {
    let values = [value].into_iter().map(|x| x);
    if read(p) > 0 { values.into_iter().next().unwrap() } else { value }
}
pub fn callback(mut emit: impl FnMut(i32), p: *mut i32) {
    emit(unsafe { read(p) });
}
"#;
    let frozen = freeze(source);
    frozen_project_from_json(&serde_json::to_string(&frozen).unwrap()).unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).unwrap();
    let generic = frozen
        .functions
        .iter()
        .find(|f| f.record.name == "generic")
        .unwrap();
    let callback = frozen
        .functions
        .iter()
        .find(|f| f.record.name == "callback")
        .unwrap();
    let read = frozen
        .functions
        .iter()
        .find(|f| f.record.name == "read")
        .unwrap();
    assert!(
        read.record.target_signature.contains("&i32"),
        "{}",
        read.record.target_signature
    );
    for function in [generic, callback] {
        assert!(function.record.unstructured);
        assert_eq!(
            function.record.source_signature,
            function.record.target_signature
        );
        assert!(function.record.target_signature.contains("p: *mut i32"));
        assert!(!function.record.annotated_source.contains("#[proctor("));
        assert!(!function.record.annotated_source.contains("todo!"));
        assert!(function.record.baseline.statement_dispositions.is_empty());
        assert!(function.record.baseline.statement_pair_metadata.is_empty());
        assert!(function.source_copy.contains("todo!"));
        assert!(!function.source_copy.contains("#[proctor("));
        assert!(transform_frozen_scc(&frozen, &request(function, None)).is_err());
    }
    let prepared = prepare_unstructured_repair(
        &frozen,
        &UnstructuredPreparationRequest {
            members: vec![generic.record.id],
            transformations: vec![],
        },
    )
    .unwrap();
    assert!(prepared.targets[0].source.contains(".map("));
    let returned = format!(
        "{} {{ let copied = value; if read(&mut *p) > 0 {{ copied }} else {{ value }} }}",
        generic.record.target_signature
    );
    let result = replace_unstructured_scc(
        &frozen,
        &UnstructuredReplacementRequest {
            members: vec![generic.record.id],
            transformation: returned.clone(),
        },
    )
    .unwrap();
    run_compiler_on_str(&result.source, utils::type_check).unwrap();
    for changed in [
        returned.replace("T: Copy", "T: Clone"),
        returned.replace("PartialEq", "Eq"),
        returned.replace("*mut i32", "&mut i32"),
        returned.replace("-> T", "-> i32"),
        returned.replace("value: T", "other: T"),
    ] {
        assert!(
            replace_unstructured_scc(
                &frozen,
                &UnstructuredReplacementRequest {
                    members: vec![generic.record.id],
                    transformation: changed,
                }
            )
            .is_err()
        );
    }
    let changed_attributes = replace_unstructured_scc(
        &frozen,
        &UnstructuredReplacementRequest {
            members: vec![generic.record.id],
            transformation: returned.replace("#[inline]", "#[inline(always)]"),
        },
    )
    .unwrap();
    assert!(changed_attributes.source.contains("#[inline]"));
    assert!(!changed_attributes.source.contains("#[inline(always)]"));
    let callback_result = replace_unstructured_scc(
        &frozen,
        &UnstructuredReplacementRequest {
            members: vec![callback.record.id],
            transformation: format!(
                "{} {{ emit(read(&mut *p)); }}",
                callback.record.target_signature
            ),
        },
    )
    .unwrap();
    run_compiler_on_str(&callback_result.source, utils::type_check).unwrap();
    let read_body = read.record.baseline.skeleton.replace("todo!()", "*p");
    let read_result = transform_frozen_scc(&frozen, &request(read, Some(&read_body)))
        .unwrap()
        .0;
    let assembled = assemble_frozen_project(
        &frozen,
        &[
            AcceptedScc {
                members: vec![read.record.id],
                source: read_result.replacement.source,
                stubbed_items: vec![],
            },
            AcceptedScc {
                members: vec![generic.record.id],
                source: result.source,
                stubbed_items: vec![],
            },
            AcceptedScc {
                members: vec![callback.record.id],
                source: callback_result.source,
                stubbed_items: vec![],
            },
        ],
    )
    .unwrap();
    run_compiler_on_str(&assembled, utils::type_check).unwrap();
    assert!(
        replace_unstructured_scc(
            &frozen,
            &UnstructuredReplacementRequest {
                members: vec![callback.record.id],
                transformation: format!(
                    "#[inline] {} {{ emit(read(&mut *p)); }}",
                    callback.record.target_signature
                ),
            }
        )
        .is_ok()
    );
    let mut changed = frozen.clone();
    changed
        .functions
        .iter_mut()
        .find(|f| f.record.id == generic.record.id)
        .unwrap()
        .record
        .unstructured = false;
    assert!(frozen_project_from_json(&serde_json::to_string(&changed).unwrap()).is_err());
}

#[test]
fn generic_dependency_source_stubs_preserve_explicit_type_arguments() {
    let source = r#"
pub fn size<T>() -> usize { core::mem::size_of::<T>() }
pub fn identity<T: Copy>(value: T) -> T { value }
pub unsafe fn read(p: *mut i32) -> i32 { identity(*p) + size::<u32>() as i32 }
"#;
    let frozen = freeze(source);
    let index = frozen
        .functions
        .iter()
        .position(|f| f.record.name == "read")
        .unwrap();
    assert!(frozen.functions[index].source_copy.contains("::<u32>"));
    let read = &frozen.functions[index];
    let body = read
        .record
        .baseline
        .skeleton
        .replace("todo!()", "identity(*p) + size::<u32>() as i32");
    let (output, metadata) = metadata(&frozen, &request(read, Some(&body)));
    crate::observation::extract_observations_from_source(&output.observation_source, &metadata)
        .unwrap();
    let dependency = frozen
        .functions
        .iter()
        .find(|f| f.record.name == "size")
        .unwrap();
    assert!(output.observation_source.contains(&dependency.source_stub));
}

#[test]
fn generic_functions_preserve_type_const_and_lifetime_parameters_together() {
    let source = "pub fn identity<'a, T, const N: usize>(values: &'a [T; N]) -> &'a [T; N] where T: Copy { values }";
    let frozen = freeze(source);
    let function = &frozen.functions[0];
    assert!(function.record.unstructured);
    let result = replace_unstructured_scc(
        &frozen,
        &UnstructuredReplacementRequest {
            members: vec![function.record.id],
            transformation: format!("{} {{ values }}", function.record.target_signature),
        },
    )
    .unwrap();
    run_compiler_on_str(&result.source, utils::type_check).unwrap();
}

#[test]
fn generic_headers_protect_named_types_but_generic_bodies_do_not() {
    let source = r#"
pub struct Fixed { p: *mut i32 }
pub struct Changed { p: *mut i32 }
pub unsafe fn generic<T>(value: Fixed, extra: T) -> Fixed { let _ = extra; value }
pub unsafe fn body_only<T>(p: *mut i32, extra: T) -> i32 {
    let local: Changed = Changed { p };
    let _ = extra;
    *local.p
}
pub unsafe fn fixed_read(value: Fixed) -> i32 { *value.p }
pub unsafe fn changed_read(value: Changed) -> i32 { *value.p }
"#;
    let frozen = freeze(source);
    let fixed = frozen.types.iter().find(|t| t.path == "Fixed").unwrap();
    let changed = frozen.types.iter().find(|t| t.path == "Changed").unwrap();
    assert_eq!(fixed.source_definition, fixed.target_definition);
    assert_ne!(changed.source_definition, changed.target_definition);
    let generic = frozen
        .functions
        .iter()
        .find(|f| f.record.name == "generic")
        .unwrap();
    assert_eq!(
        generic.record.source_signature,
        generic.record.target_signature
    );
    run_compiler_on_str(&frozen.target_source, utils::type_check).unwrap();
}

fn request(function: &FrozenFunction, transformation: Option<&str>) -> ReplacementRequest {
    ReplacementRequest {
        items: vec![ReplacementItem {
            id: function.record.id,
            path: function.record.path.clone(),
            name: function.record.name.clone(),
            view: function.record.baseline.clone(),
        }],
        transformation: transformation
            .unwrap_or(&function.record.baseline.skeleton)
            .to_owned(),
        accepted_correspondence: vec![],
    }
}

fn transform(frozen: &FrozenProject, index: usize) -> ExtendedReplacementOutput {
    transform_frozen_scc(frozen, &request(&frozen.functions[index], None))
        .unwrap()
        .0
}

fn metadata(
    frozen: &FrozenProject,
    request: &ReplacementRequest,
) -> (
    ExtendedReplacementOutput,
    crate::ReplacementObservationMetadata,
) {
    let (output, dependencies) = transform_frozen_scc(frozen, request).unwrap();
    let metadata = crate::ReplacementObservationMetadata::from_frozen_output(
        &output,
        dependencies,
        frozen,
        output.replacement.source.as_bytes(),
        b"[]",
        output.observation_source.as_bytes(),
    );
    (output, metadata)
}

#[test]
fn variadic_signatures_remain_fixed_while_bodies_and_va_list_forwarding_transform() {
    let source = r#"
#![feature(c_variadic)]
extern "C" { fn vsink(fmt: *const i8, args: ::core::ffi::VaList) -> i32; }
pub unsafe extern "C" fn emit(fmt: *const i8, mut args: ...) -> i32 {
    let mut ap = args.clone();
    return vsink(fmt, ap.as_va_list());
}

pub unsafe fn caller(fmt: *const i8) -> i32 { emit(fmt, 7i32, 8i32) }
"#;
    let frozen = freeze(source);
    let emit = frozen
        .functions
        .iter()
        .find(|function| function.record.name == "emit")
        .unwrap();
    assert_eq!(emit.record.source_signature, emit.record.target_signature);
    assert!(emit.record.target_signature.contains("extern \"C\""));
    assert!(emit.record.target_signature.contains("fmt: *const i8"));
    assert!(emit.record.target_signature.contains("mut args: ..."));
    assert!(emit.record.baseline.needs_transformation);
    run_compiler_on_str(&frozen.target_source, |_| ()).unwrap();
    let returned = emit
        .record
        .baseline
        .skeleton
        .replace("= todo!();", "= args.clone();")
        .replace("return todo!();", "return vsink(fmt, ap.as_va_list()) + 1;");
    assert!(!returned.contains("todo!"), "{returned}");
    let request = request(emit, Some(&returned));
    assert_eq!(
        crate::validate(&crate::ValidationRequest {
            expected_functions: vec![crate::ExpectedFunction {
                id: emit.record.id,
                name: emit.record.name.clone(),
                view: emit.record.baseline.clone(),
            }],
            transformation: returned.clone(),
        }),
        crate::ValidationResponse::Valid
    );
    let output = transform_frozen_scc(&frozen, &request).unwrap().0;
    run_compiler_on_str(&output.replacement.source, |_| ()).unwrap();
    run_compiler_on_str(&output.observation_source, |_| ()).unwrap();
    for (old, new) in [
        ("*const i8", "*mut i8"),
        ("-> i32", "-> i64"),
        ("extern \"C\" ", ""),
        (", mut args: ...", ""),
        ("mut args", "mut other"),
    ] {
        let changed = ReplacementRequest {
            transformation: returned.replace(old, new),
            ..request.clone()
        };
        assert!(
            transform_frozen_scc(&frozen, &changed).is_err(),
            "{old} -> {new}"
        );
    }
}

#[test]
fn unstructured_variadic_replacement_checks_the_returned_header_before_restoration() {
    let frozen = freeze(
        r#"#![feature(c_variadic)] pub unsafe extern "C" fn f(fmt: *const i8, mut args: ...) -> i32 { 0 }"#,
    );
    let function = &frozen.functions[0];
    let returned = format!("{} {{ 7 }}", function.record.target_signature);
    let request = UnstructuredReplacementRequest {
        members: vec![function.record.id],
        transformation: returned.clone(),
    };
    let output = replace_unstructured_scc(&frozen, &request).unwrap();
    run_compiler_on_str(&output.source, |_| ()).unwrap();
    for (old, new) in [
        ("extern \"C\" ", ""),
        ("\"C\"", "\"C-unwind\""),
        (", mut args: ...", ""),
        ("*const i8", "*mut i8"),
    ] {
        let changed = UnstructuredReplacementRequest {
            members: request.members.clone(),
            transformation: returned.replace(old, new),
        };
        assert!(
            replace_unstructured_scc(&frozen, &changed).is_err(),
            "{old} -> {new}"
        );
    }
}

#[test]
fn template_retains_full_context_typed_headers_lifetimes_and_abi() {
    let source = r#"
pub struct Context { pub value: i32 }
pub const LIMIT: i32 = 4;
extern "C" { fn foreign(value: i32) -> i32; }
pub static CALLBACK: unsafe extern "C" fn(i32) -> i32 = value;
pub unsafe extern "C" fn value(n: i32) -> i32 { n + 1 }
pub mod nested {
    use crate::Context;
    pub(crate) unsafe fn echo<'a>(p: &'a Context) -> &'a Context { p }
}

fn main() {}
"#;
    let frozen = freeze(source);
    assert!(frozen.target_source.contains("pub static CALLBACK:"));
    assert!(frozen.target_source.contains("extern \"C\""));
    assert!(
        frozen
            .target_source
            .contains("pub(crate) unsafe fn echo<'a>")
    );
    assert!(frozen.target_source.contains("-> &'a Context"));
    assert!(!frozen.target_source.contains("fn main"));
    assert!(!frozen.target_source.contains("__proctor_source"));
    run_compiler_on_str(&frozen.target_source, |_| ()).unwrap();
    let round_trip = frozen_project_from_json(&serde_json::to_string(&frozen).unwrap()).unwrap();
    assert_eq!(round_trip, frozen);
    let value = serde_json::to_value(&frozen).unwrap();
    assert_eq!(
        value
            .as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        [
            "analysis_source",
            "functions",
            "initializers",
            "target_source",
            "types"
        ]
    );
    for field in [
        "analysis_source",
        "functions",
        "initializers",
        "target_source",
        "types",
    ] {
        let mut missing = value.clone();
        missing.as_object_mut().unwrap().remove(field);
        assert!(frozen_project_from_json(&missing.to_string()).is_err());
        let mut mistyped = value.clone();
        mistyped[field] = serde_json::Value::Null;
        assert!(frozen_project_from_json(&mistyped.to_string()).is_err());
    }
    let mut unknown = value;
    unknown["extra"] = serde_json::json!(true);
    assert!(frozen_project_from_json(&unknown.to_string()).is_err());
    check_frozen_project_sources(&frozen, source, Some(&frozen.target_source), true).unwrap();
    assert!(
        check_frozen_project_sources(
            &frozen,
            &source.replace("LIMIT: i32 = 4", "LIMIT: i32 = 5"),
            None,
            true
        )
        .is_err()
    );
    assert!(
        check_frozen_project_sources(&frozen, source, Some(&frozen.analysis_source), true).is_err()
    );
}

#[test]
fn independent_duplicate_names_assemble_in_original_order_without_stubs() {
    let frozen = freeze(
        "pub mod a { pub unsafe fn same() -> i32 { 11 } } pub const GAP: i32 = 0; pub mod b { pub unsafe fn same() -> i32 { 22 } }",
    );
    assert_eq!(
        frozen
            .functions
            .iter()
            .map(|function| function.record.id)
            .collect::<Vec<_>>(),
        vec![0, 2]
    );
    let first = transform(&frozen, 0);
    let second = transform(&frozen, 1);
    assert!(first.replacement.source.contains("todo!()"));
    assert!(second.replacement.source.contains("todo!()"));
    run_compiler_on_str(&first.replacement.source, |_| ()).unwrap();
    run_compiler_on_str(&second.replacement.source, |_| ()).unwrap();
    let accepted = [
        AcceptedScc {
            stubbed_items: vec![],
            members: vec![2],
            source: second.replacement.source,
        },
        AcceptedScc {
            stubbed_items: vec![],
            members: vec![0],
            source: first.replacement.source,
        },
    ];
    let assembled = assemble_frozen_project(&frozen, &accepted).unwrap();
    assert!(assembled.contains("11") && assembled.contains("22"));
    assert!(!assembled.contains("todo!") && !assembled.contains("__proctor_"));
    let mut reversed = accepted.clone();
    reversed.reverse();
    assert_eq!(
        assembled,
        assemble_frozen_project(&frozen, &reversed).unwrap()
    );
    assert!(assemble_frozen_project(&frozen, &accepted[..1]).is_err());
    let mut stub = accepted.clone();
    stub[0].source = frozen.target_source.clone();
    assert!(assemble_frozen_project(&frozen, &stub).is_err());
    assert!(assemble_frozen_project(&frozen, &[accepted[0].clone(), accepted[0].clone()]).is_err());
    let mut changed = accepted.clone();
    changed[0].source = changed[0].source.replace("GAP: i32 = 0", "GAP: i32 = 1");
    assert!(assemble_frozen_project(&frozen, &changed).is_err());
    let mut changed = accepted.clone();
    changed[0].source = changed[0].source.replace("-> i32", "-> u32");
    assert!(assemble_frozen_project(&frozen, &changed).is_err());
    run_compiler_on_str(&assembled, |_| ()).unwrap();
}

fn pointer_view(name: &str, source: &str) -> SkeletonView {
    SkeletonView {
        skeleton: format!(
            "unsafe fn {name}<'a>(mut p: &'a [i32]) -> i32 {{ #[proctor(0)] todo!() }}"
        ),
        needs_transformation: true,
        statement_dispositions: vec![crate::StatementDisposition {
            label: 0,
            disposition: crate::StatementDispositionKind::Transform,
            children: vec![],
        }],
        statement_pair_metadata: vec![crate::StatementPairMetadata {
            label: 0,
            before_statement: source.to_owned(),
            printf_template: None,
            pointer_variables_complete: true,
            pointer_variables: vec![],
        }],
    }
}

#[test]
fn cross_module_observations_use_original_and_target_signature_stubs_with_one_identity() {
    let source = "pub mod left { pub unsafe extern \"C\" fn leaf(p: *const i32) -> usize { 0 } } pub mod right { pub unsafe fn root(p: *const i32) -> i32 { *p.add(crate::left::leaf(p)) } }";
    let frozen = run_compiler_on_str(source, |tcx| {
        let mut records = crate::make_skeletons(source, tcx).unwrap();
        for item in &mut records {
            let crate::ItemRecord::Function(record) = item else { continue };
            record.baseline = pointer_view(
                &record.name,
                if record.name == "leaf" {
                    "*p"
                } else {
                    "crate::left::leaf(p)"
                },
            );
            if record.name == "leaf" {
                record.baseline.skeleton = record.baseline.skeleton.replace("-> i32", "-> usize");
            }
            record.applied = record.baseline.clone();
        }
        freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    let root = &frozen.functions[1];
    let request = request(
        root,
        Some(
            "unsafe fn root<'a>(mut p: &'a [i32]) -> i32 { #[proctor(0)] p[crate::left::leaf(p)] }",
        ),
    );
    let (output, metadata) = metadata(&frozen, &request);
    assert!(
        output
            .observation_source
            .contains("__proctor_source_stub_leaf(p: *const i32)")
    );
    assert!(
        output
            .observation_source
            .contains("extern \"C\" fn leaf<'a>")
    );
    assert!(
        output
            .observation_source
            .contains("crate::left::__proctor_source_stub_leaf(p)")
    );
    assert!(metadata.accepted_correspondence.is_empty());
    assert_eq!(metadata.dependency_correspondence.len(), 1);
    assert_eq!(metadata.new_correspondence.len(), 1);
    assert_eq!(metadata.source_stubs.len(), 2);
    let value = serde_json::to_value(&metadata).unwrap();
    assert_eq!(
        value
            .as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        [
            "accepted_correspondence",
            "candidate_sha256",
            "current_items",
            "dependency_correspondence",
            "frozen_project_sha256",
            "new_correspondence",
            "observation_source_sha256",
            "source_stubs",
            "statement_pairs_sha256",
            "unfilled_stub_items",
        ]
    );
    for field in value.as_object().unwrap().keys() {
        let mut missing = value.clone();
        missing.as_object_mut().unwrap().remove(field);
        assert!(crate::replacement_metadata_from_json(&missing.to_string()).is_err());
        let mut mistyped = value.clone();
        mistyped[field] = serde_json::Value::Null;
        assert!(crate::replacement_metadata_from_json(&mistyped.to_string()).is_err());
    }
    let decoded =
        crate::replacement_metadata_from_json(&serde_json::to_string(&metadata).unwrap()).unwrap();
    let observations =
        crate::observation::extract_observations_from_source(&output.observation_source, &decoded)
            .unwrap();
    let json = serde_json::to_string(&observations).unwrap();
    assert!(
        json.contains("\"kind\":\"function\",\"id\":\"<fn0>\""),
        "{json}"
    );
    assert!(!json.contains("__proctor_source"));
    run_compiler_on_str(&output.replacement.source, |_| ()).unwrap();
}

#[test]
fn opaque_value_locals_survive_frozen_replacement_and_preservation() {
    let frozen = freeze(
        r#"
pub unsafe fn value(p: *const i32) -> i32 {
    let preserved = Some({ let init: i32 = 7; init }).unwrap();
    let changed = Some({ let original = p; *original }).unwrap();
    preserved + changed
}
"#,
    );
    let function = &frozen.functions[0];
    assert_eq!(function.record.baseline.transform_labels(), [1]);
    let transformation = format!(
        r#"{} {{
    #[proctor(0)]
    let preserved: i32 = Some({{ let renamed_preserved: i64 = 99; renamed_preserved as i32 }}).unwrap();
    #[proctor(1)]
    let changed: i32 = Some({{ let renamed: &i32 = p; *renamed }}).unwrap();
    #[proctor(2)]
    preserved + changed
}}"#,
        function.record.target_signature,
    );
    let request = request(function, Some(&transformation));
    let (output, metadata) = metadata(&frozen, &request);
    let candidate = &output.replacement.source;
    assert!(candidate.contains("init: i32 = 7"), "{candidate}");
    assert!(!candidate.contains("renamed_preserved") && !candidate.contains("99"));
    assert!(candidate.contains("renamed: &i32"), "{candidate}");
    assert_eq!(output.replacement.statement_pairs.len(), 1);
    assert_eq!(output.replacement.statement_pairs[0].label, 1);
    assert!(metadata.unfilled_stub_items.is_empty());
    run_compiler_on_str(candidate, |_| ()).unwrap();
    crate::observation::extract_observations_from_source(&output.observation_source, &metadata)
        .unwrap();
    let assembled = assemble_frozen_project(
        &frozen,
        &[AcceptedScc {
            stubbed_items: vec![],
            members: vec![function.record.id],
            source: candidate.clone(),
        }],
    )
    .unwrap();
    assert!(assembled.contains("init: i32 = 7"));
    assert!(assembled.contains("renamed: &i32"));
    assert!(!assembled.contains("todo!()") && !assembled.contains("#[proctor"));
    run_compiler_on_str(&assembled, |_| ()).unwrap();
}

#[test]
fn recursive_source_copies_use_original_stubs_and_preserve_callable_identity() {
    let source = "pub unsafe fn recurse(p: *const i32) -> usize { *p.add(recurse(p)) as usize }";
    let frozen = run_compiler_on_str(source, |tcx| {
        let mut records = crate::make_skeletons(source, tcx).unwrap();
        let crate::ItemRecord::Function(record) = &mut records[0] else { unreachable!() };
        record.baseline = pointer_view("recurse", "*p.add(recurse(p)) as usize");
        record.baseline.skeleton = record.baseline.skeleton.replace("-> i32", "-> usize");
        record.applied = record.baseline.clone();
        freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    let request = request(
        &frozen.functions[0],
        Some(
            "unsafe fn recurse<'a>(mut p: &'a [i32]) -> usize { #[proctor(0)] p[recurse(p)] as usize }",
        ),
    );
    let (output, metadata) = metadata(&frozen, &request);
    assert!(
        output
            .observation_source
            .contains("crate::__proctor_source_stub_recurse(p)")
    );
    assert!(metadata.dependency_correspondence.is_empty());
    let document =
        crate::observation::extract_observations_from_source(&output.observation_source, &metadata)
            .unwrap();
    assert!(!document.observations.is_empty());
    let text = serde_json::to_string(&document).unwrap();
    assert!(
        text.contains("\"kind\":\"function\",\"id\":\"<fn0>\""),
        "{text}"
    );
}

#[test]
fn frozen_views_are_checked_before_canonical_replacement() {
    let frozen = freeze("pub unsafe fn f(value: i32) -> i32 { value }");
    let mut changed = request(&frozen.functions[0], None);
    changed.items[0].view.skeleton = changed.items[0].view.skeleton.replace("value", "other");
    assert!(transform_frozen_scc(&frozen, &changed).is_err());
    let mut changed = request(&frozen.functions[0], None);
    changed
        .accepted_correspondence
        .push(correspondence(&frozen.functions[0].record));
    assert!(transform_frozen_scc(&frozen, &changed).is_err());
}

#[test]
fn frozen_finalization_restores_main_and_preserves_original_api_exports() {
    let frozen = freeze(
        "#[export_name = \"public_entry\"] pub unsafe extern \"C\" fn entry() -> i32 { 7 } fn main() { unsafe { entry(); } }",
    );
    let output = transform(&frozen, 0);
    let accepted = [AcceptedScc {
        stubbed_items: vec![],
        members: vec![frozen.functions[0].record.id],
        source: output.replacement.source,
    }];
    let assembled = assemble_frozen_project(&frozen, &accepted).unwrap();
    assert!(!assembled.contains("fn main"));
    let final_project = finalize_frozen_project(&frozen, &assembled, "executable", &[]).unwrap();
    assert!(final_project.source.contains("fn main()"));
    assert!(
        !final_project.source.contains("todo!") && !final_project.source.contains("__proctor_")
    );
    run_compiler_on_str(&final_project.source, |_| ()).unwrap();
    let library =
        finalize_frozen_project(&frozen, &assembled, "library", &["public_entry".to_owned()])
            .unwrap();
    let declaration_only = finalize_frozen_project(
        &frozen,
        &assembled,
        "library",
        &["public_entry".to_owned(), "declared_only".to_owned()],
    )
    .unwrap();
    assert_eq!(declaration_only.source, library.source);
    assert!(library.source.contains("export_name = \"public_entry\""));
    for (kind, api) in [
        ("unknown", vec![]),
        ("executable", vec!["public_entry".to_owned()]),
        ("library", vec!["main".to_owned()]),
    ] {
        let error = finalize_frozen_project(&frozen, &assembled, kind, &api).unwrap_err();
        assert_eq!(error.kind, ReplacementErrorKind::InvalidRequest);
    }
}

#[test]
fn frozen_views_reject_a_child_moved_between_branches() {
    let frozen = freeze(
        "pub unsafe fn choose(flag: bool) { if flag { consume(); } else {} } unsafe fn consume() {}",
    );
    let mut changed = frozen.clone();
    let choose = changed
        .functions
        .iter_mut()
        .find(|function| function.record.name == "choose")
        .unwrap();
    choose.record.applied.skeleton = "pub unsafe fn choose(mut flag: bool) { #[proctor(0)] if flag {} else { #[proctor(1)] consume(); } }".to_owned();
    let error = frozen_project_from_json(&serde_json::to_string(&changed).unwrap()).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::InvalidRequest);
    assert!(error.message.contains("topology"), "{error:?}");
}

#[test]
fn malformed_frozen_bundles_return_errors_without_compiler_analysis_or_panics() {
    let frozen = freeze("pub mod nested { pub unsafe fn read(p: *const i32) -> i32 { *p } }");
    for mutation in [
        "missing",
        "original_kind",
        "kind",
        "target_missing",
        "path",
        "target_header",
        "original_header",
        "target_pattern",
        "copy_kind",
        "stub_header",
    ] {
        let mut changed = frozen.clone();
        match mutation {
            "missing" => changed.functions.clear(),
            "original_kind" => changed.functions[0].original_item = "pub struct Broken;".to_owned(),
            "kind" => changed.functions[0].record.kind = crate::ItemKindName::Static,
            "target_missing" => changed.target_source = "pub mod nested {}".to_owned(),
            "path" => changed.functions[0].record.path = "nested::missing".to_owned(),
            "target_header" => {
                changed.target_source = changed.target_source.replace("-> i32", "-> u32")
            }
            "original_header" => {
                changed.functions[0].original_item = changed.functions[0]
                    .original_item
                    .replace("-> i32", "-> u32")
            }
            "target_pattern" => {
                changed.functions[0].record.baseline.skeleton = changed.functions[0]
                    .record
                    .baseline
                    .skeleton
                    .replace("mut p", "(left, right)");
            }
            "copy_kind" => changed.functions[0].source_copy = "pub struct Broken;".to_owned(),
            "stub_header" => {
                changed.functions[0].source_stub =
                    changed.functions[0].source_stub.replace("-> i32", "-> u32")
            }
            _ => unreachable!(),
        }
        assert!(
            frozen_project_from_json(&serde_json::to_string(&changed).unwrap()).is_err(),
            "{mutation}"
        );
        assert!(
            check_frozen_project_sources(
                &changed,
                &frozen.analysis_source,
                Some(&frozen.target_source),
                true
            )
            .is_err(),
            "{mutation}"
        );
        assert!(
            transform_frozen_scc(&changed, &request(&frozen.functions[0], None)).is_err(),
            "{mutation}"
        );
        assert!(
            assemble_frozen_project(&changed, &[]).is_err(),
            "{mutation}"
        );
        assert!(
            finalize_frozen_project(&changed, &frozen.target_source, "library", &[]).is_err(),
            "{mutation}"
        );
    }
}

#[test]
fn unfilled_stub_metadata_identifies_only_requested_functions() {
    let frozen = freeze(
        "pub unsafe fn read(p: *const i32) -> i32 { *p } pub unsafe fn other(p: *const i32) -> i32 { *p }",
    );
    let singleton = request(&frozen.functions[0], None);
    assert_eq!(
        crate::validate(&crate::ValidationRequest {
            expected_functions: vec![crate::ExpectedFunction {
                id: 0,
                name: "read".to_owned(),
                view: frozen.functions[0].record.baseline.clone()
            }],
            transformation: singleton.transformation.clone(),
        }),
        crate::ValidationResponse::Valid
    );
    let (output, singleton_metadata) = metadata(&frozen, &singleton);
    assert_eq!(singleton_metadata.unfilled_stub_items, vec![0]);
    assert_eq!(output.replacement.source, frozen.target_source);
    run_compiler_on_str(&output.replacement.source, |_| ()).unwrap();

    let mut mixed = singleton.clone();
    mixed
        .items
        .extend(request(&frozen.functions[1], None).items);
    mixed.transformation = frozen.functions[0]
        .record
        .baseline
        .skeleton
        .replace("todo!()", "0")
        + "\n"
        + &frozen.functions[1].record.baseline.skeleton;
    let (output, mixed_metadata) = metadata(&frozen, &mixed);
    assert_eq!(mixed_metadata.unfilled_stub_items, vec![1]);
    run_compiler_on_str(&output.replacement.source, |_| ()).unwrap();
    let parsed =
        crate::replacement_metadata_from_json(&serde_json::to_string(&mixed_metadata).unwrap())
            .unwrap();
    assert_eq!(parsed.unfilled_stub_items, vec![1]);
    mixed.transformation = mixed.transformation.replace("todo!()", "0");
    let (_, repaired) = metadata(&frozen, &mixed);
    assert!(repaired.unfilled_stub_items.is_empty());
}

#[test]
fn nested_holes_in_requested_functions_are_repairable_without_rejecting_other_stubs() {
    let frozen = freeze(
        "pub unsafe fn read(p: *const i32) -> i32 { *p } pub unsafe fn other(p: *const i32) -> i32 { *p }",
    );
    for expression in [
        "{ let value: i32 = todo!(); value }",
        "(|| ::core::todo!())()",
    ] {
        let mut requested = request(&frozen.functions[0], None);
        requested.transformation = requested.transformation.replace("todo!()", expression);
        let (output, unfilled) = metadata(&frozen, &requested);
        assert_eq!(unfilled.unfilled_stub_items, vec![0], "{expression}");
        run_compiler_on_str(&output.replacement.source, utils::type_check).unwrap();
        requested.transformation = requested.transformation.replace(expression, "0");
        let (output, repaired) = metadata(&frozen, &requested);
        assert!(repaired.unfilled_stub_items.is_empty());
        assert!(output.replacement.source.contains("todo!()"));
    }
}

#[test]
fn unstructured_preparation_strips_labels_and_selects_latest_parseable_candidate() {
    let frozen = freeze("pub unsafe fn target(x: i32) -> i32 { x + 1 }");
    let request = UnstructuredPreparationRequest {
        members: vec![frozen.functions[0].record.id],
        transformations: vec![
            "unsafe fn target(mut x: i32) -> i32 { #[proctor(0)] x }".to_owned(),
            "unsafe fn target(mut x: i32) -> i32 { #[proctor(0)] let text = \"#[proctor(99)]\"; #[proctor(1)] x + 1 }".to_owned(),
            "unsafe fn target(".to_owned(),
        ],
    };
    let prepared = prepare_unstructured_repair(&frozen, &request).unwrap();
    let candidate = prepared.candidate.unwrap();
    assert!(!candidate.contains("#[proctor(0)]") && !candidate.contains("#[proctor(1)]"));
    assert!(candidate.contains("\"#[proctor(99)]\""));
    assert!(candidate.contains("x + 1"));
    assert!(!prepared.targets[0].source.contains("#[proctor("));
    assert_eq!(
        prepared.targets[0].signature,
        frozen.functions[0].record.target_signature
    );
    for transformations in [vec![], vec!["unsafe fn target(".to_owned()]] {
        let prepared = prepare_unstructured_repair(
            &frozen,
            &UnstructuredPreparationRequest {
                members: request.members.clone(),
                transformations,
            },
        )
        .unwrap();
        assert!(prepared.candidate.is_none());
    }
}

#[test]
fn retention_preserves_latest_usable_body_per_function_without_type_checking() {
    let frozen = freeze(
        "pub unsafe fn first(x: i32) -> i32 { x } pub unsafe fn second(x: i32) -> i32 { x }",
    );
    let members = frozen
        .functions
        .iter()
        .map(|function| function.record.id)
        .collect::<Vec<_>>();
    let retained = retain_frozen_functions(&frozen, &UnstructuredPreparationRequest {
        members: members.clone(),
        transformations: vec![
            "unsafe fn first(mut x: i32) -> i32 { 1 } unsafe fn second(mut x: i32) -> i32 { 2 }".to_owned(),
            "fn first(renamed: u8) -> bool { #[proctor(0)] let text = \"#[proctor(99)]\"; #[proctor(1)] missing_value } struct Unrelated;".to_owned(),
            "unsafe fn first(mut x: i32) -> i32 { 7 } unsafe fn first(mut x: i32) -> i32 { 8 }".to_owned(),
            "unsafe fn second(mut x: i32) -> i32 { ::core::todo!() }".to_owned(),
            "unsafe fn first(mut x: i32) -> i32 { return todo!(); } unsafe fn second(mut x: i32) -> i32 { { std::todo!() } }".to_owned(),
            "unsafe fn first(mut x: i32) -> i32 { let value = 1 x }".to_owned(),
            "unsafe fn second(mut x: i32) -> i32 { let value = ; 3 }".to_owned(),
            "unsafe fn second(".to_owned(),
        ],
    }).unwrap();
    assert!(retained.stubbed_items.is_empty());
    assert!(retained.source.contains("missing_value"));
    assert!(retained.source.contains("\"#[proctor(99)]\""));
    assert!(!retained.source.contains("#[proctor(0)]"));
    assert!(!retained.source.contains("#[proctor(1)]"));
    assert!(!retained.source.contains("Unrelated"));
    assert!(!retained.source.contains("renamed") && !retained.source.contains("u8"));
    let assembled = assemble_frozen_project(
        &frozen,
        &[AcceptedScc {
            members,
            source: retained.source.clone(),
            stubbed_items: retained.stubbed_items,
        }],
    )
    .unwrap();
    assert_eq!(assembled, retained.source);
    with_parse_session(|| {
        let parsed = parse_crate(&assembled, ReplacementErrorKind::InvalidTransformation)?;
        let second = function_at_path(&parsed.items, &["second".to_owned()]).unwrap();
        let expected = one_item(&format!(
            "{} {{ 2 }}",
            frozen.functions[1].record.target_signature
        ))?;
        assert_eq!(
            pprust::item_to_string(second),
            pprust::item_to_string(&expected)
        );
        Ok(())
    })
    .unwrap();
}

#[test]
fn retention_keeps_frozen_stubs_only_for_members_without_usable_bodies() {
    let frozen = freeze(
        "pub unsafe extern \"C\" fn first(x: i32) -> i32 { x } pub unsafe fn second(x: i32) -> i32 { x } pub unsafe fn third() {}",
    );
    let first = &frozen.functions[0];
    let second = &frozen.functions[1];
    let third = &frozen.functions[2];
    let retained = retain_frozen_functions(
        &frozen,
        &UnstructuredPreparationRequest {
            members: vec![first.record.id, second.record.id],
            transformations: vec!["fn first() { let value: i32 = todo!(); value }".to_owned()],
        },
    )
    .unwrap();
    assert_eq!(retained.stubbed_items, vec![second.record.id]);
    assert!(retained.source.contains("extern \"C\""));
    let assembled = assemble_frozen_project(
        &frozen,
        &[
            AcceptedScc {
                members: vec![first.record.id, second.record.id],
                source: retained.source,
                stubbed_items: retained.stubbed_items,
            },
            AcceptedScc {
                members: vec![third.record.id],
                source: frozen.target_source.clone(),
                stubbed_items: vec![third.record.id],
            },
        ],
    )
    .unwrap();
    assert!(assembled.contains("let value: i32 = todo!()"));
    assert_eq!(assembled.matches("todo!()").count(), 3);
    for members in [
        vec![],
        vec![u64::MAX],
        vec![first.record.id, first.record.id],
    ] {
        assert!(
            retain_frozen_functions(
                &frozen,
                &UnstructuredPreparationRequest {
                    members,
                    transformations: vec![],
                }
            )
            .is_err()
        );
    }
}

#[test]
fn assembly_requires_exact_stub_allowlists_and_complete_member_coverage() {
    let frozen = freeze("pub unsafe fn first() {} pub unsafe fn second() {}");
    let members = frozen
        .functions
        .iter()
        .map(|function| function.record.id)
        .collect::<Vec<_>>();
    for stubbed_items in [
        vec![],
        vec![members[0]],
        vec![members[0], members[0]],
        vec![u64::MAX],
    ] {
        assert!(
            assemble_frozen_project(
                &frozen,
                &[AcceptedScc {
                    members: members.clone(),
                    source: frozen.target_source.clone(),
                    stubbed_items,
                }]
            )
            .is_err()
        );
    }
    let retained = retain_frozen_functions(
        &frozen,
        &UnstructuredPreparationRequest {
            members: members.clone(),
            transformations: vec!["unsafe fn first() { let value = 1; }".to_owned()],
        },
    )
    .unwrap();
    assert!(
        assemble_frozen_project(
            &frozen,
            &[AcceptedScc {
                members: members.clone(),
                source: retained.source,
                stubbed_items: members.clone(),
            }]
        )
        .is_err()
    );
    assert!(
        assemble_frozen_project(
            &frozen,
            &[AcceptedScc {
                members: vec![members[0]],
                source: frozen.target_source.clone(),
                stubbed_items: vec![members[0]],
            }]
        )
        .is_err()
    );
    let assembled = assemble_frozen_project(
        &frozen,
        &[AcceptedScc {
            members: members.clone(),
            source: frozen.target_source.clone(),
            stubbed_items: members,
        }],
    )
    .unwrap();
    assert_eq!(assembled, frozen.target_source);
}

#[test]
fn unstructured_stripping_handles_misplaced_labels_in_failed_function_output() {
    let stripped = strip_proctor_labels("#![proctor(0)] #[allow(dead_code)] #[proctor(1)] unsafe fn target<#[proctor(2)] 'a>(#[proctor(3)] x: &'a i32) -> i32 { match *x { #[proctor(4)] _ => 1 } }").unwrap();
    assert!(!stripped.contains("proctor"));
    assert!(stripped.contains("allow(dead_code)"));
    assert!(stripped.contains("match *x"));
    for source in [
        "unsafe fn target() { let S { #[proctor(7)] x } = S { #[proctor(8)] x: 1 }; }",
        "struct S { #[proctor(1)] x: i32 } enum E { #[proctor(2)] A } extern \"C\" { #[proctor(3)] fn external(); } impl S { #[proctor(4)] fn helper() {} }",
        "unsafe fn target<T>() where #[proctor(5)] T: Copy {}",
    ] {
        let stripped = strip_proctor_labels(source).unwrap();
        assert!(!stripped.contains("proctor"), "{stripped}");
    }
}

#[test]
fn unstructured_rewrites_use_frozen_headers_and_assemble_after_free_body_changes() {
    let frozen = freeze("#[no_mangle] pub unsafe extern \"C\" fn target(x: i32) -> i32 { x + 1 }");
    let signature = &frozen.functions[0].record.target_signature;
    let replacement = replace_unstructured_scc(&frozen, &UnstructuredReplacementRequest {
        members: vec![frozen.functions[0].record.id],
        transformation: format!("{signature} {{ let new_name = x + 1; for value in 0..0 {{ let _ = value; }} new_name }}"),
    }).unwrap();
    assert!(!replacement.source.contains("#[proctor("));
    assert!(replacement.source.contains("extern \"C\""));
    assert!(replacement.source.contains("no_mangle"));
    assert_eq!(
        replacement.new_correspondence,
        vec![correspondence(&frozen.functions[0].record)]
    );
    let assembled = assemble_frozen_project(
        &frozen,
        &[AcceptedScc {
            stubbed_items: vec![],
            members: vec![frozen.functions[0].record.id],
            source: replacement.source,
        }],
    )
    .unwrap();
    assert!(assembled.contains("new_name"));
    run_compiler_on_str(&assembled, |_| ()).unwrap();
}

#[test]
fn unstructured_rejects_wrong_signatures_function_sets_and_whole_function_stubs() {
    let frozen = freeze("pub unsafe fn target(x: i32) -> i32 { x + 1 }");
    for transformation in [
        "unsafe fn target(mut x: i64) -> i32 { 0 }",
        "unsafe fn target(mut x: i32) -> i64 { 0 }",
        "unsafe fn target<'a>(mut x: i32) -> i32 { 0 }",
        "unsafe fn target(mut y: i32) -> i32 { 0 }",
        "fn target(mut x: i32) -> i32 { 0 }",
        "const unsafe fn target(mut x: i32) -> i32 { 0 }",
        "unsafe fn target(mut x: i32) -> i32 { todo!() }",
        "unsafe fn target(mut x: i32) -> i32;",
        "unsafe fn target(mut x: i32) -> i32 { x } fn extra() {}",
        "unsafe fn other(mut x: i32) -> i32 { x }",
        "unsafe fn target(",
    ] {
        let error = replace_unstructured_scc(
            &frozen,
            &UnstructuredReplacementRequest {
                members: vec![frozen.functions[0].record.id],
                transformation: transformation.to_owned(),
            },
        )
        .err()
        .unwrap_or_else(|| panic!("admitted {transformation}"));
        assert!(
            matches!(error.kind, ReplacementErrorKind::InvalidTransformation),
            "{transformation}: {}",
            error.message
        );
    }
}

#[test]
fn unstructured_preserves_destructured_parameter_signatures() {
    let frozen = freeze("pub unsafe fn target<T: Copy>((value,): (T,)) -> T { value }");
    let function = &frozen.functions[0];
    let output = replace_unstructured_scc(
        &frozen,
        &UnstructuredReplacementRequest {
            members: vec![function.record.id],
            transformation: format!(
                "{} {{ let copied = value; copied }}",
                function.record.target_signature
            ),
        },
    )
    .unwrap();
    run_compiler_on_str(&output.source, utils::type_check).unwrap();
}

#[test]
fn unstructured_preserves_other_scc_stubs_and_rejects_invalid_members() {
    let frozen = freeze(
        "pub unsafe fn first(x: i32) -> i32 { x } pub unsafe fn second(x: i32) -> i32 { x }",
    );
    let mut accepted = vec![];
    for function in &frozen.functions {
        let replacement = replace_unstructured_scc(
            &frozen,
            &UnstructuredReplacementRequest {
                members: vec![function.record.id],
                transformation: format!("{} {{ x }}", function.record.target_signature),
            },
        )
        .unwrap();
        assert_eq!(replacement.source.matches("todo!()").count(), 1);
        accepted.push(AcceptedScc {
            stubbed_items: vec![],
            members: vec![function.record.id],
            source: replacement.source,
        });
    }
    let assembled = assemble_frozen_project(&frozen, &accepted).unwrap();
    assert!(!assembled.contains("todo!()"));
    run_compiler_on_str(&assembled, |_| ()).unwrap();
    for members in [vec![], vec![u64::MAX], vec![0, 0], vec![1, 0]] {
        let error = replace_unstructured_scc(
            &frozen,
            &UnstructuredReplacementRequest {
                members,
                transformation: String::new(),
            },
        )
        .err()
        .unwrap();
        assert!(matches!(error.kind, ReplacementErrorKind::InvalidRequest));
    }
}

#[test]
fn unstructured_preserves_frozen_lifetimes_and_pointer_target_types() {
    let source = "pub unsafe fn read(p: *const i32) -> i32 { *p.add(1) }";
    let frozen = run_compiler_on_str(source, |tcx| {
        let mut records = crate::make_skeletons(source, tcx).unwrap();
        for item in &mut records {
            let crate::ItemRecord::Function(record) = item else { continue };
            record.baseline = pointer_view("read", "*p.add(1)");
            record.applied = record.baseline.clone();
            record.target_signature = "unsafe fn read<'a>(mut p: &'a [i32]) -> i32".to_owned();
        }
        freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    let signature = &frozen.functions[0].record.target_signature;
    assert!(signature.contains("<'") && signature.contains("[i32]"));
    let replacement = replace_unstructured_scc(
        &frozen,
        &UnstructuredReplacementRequest {
            members: vec![frozen.functions[0].record.id],
            transformation: format!("{signature} {{ p[1] }}"),
        },
    )
    .unwrap();
    let assembled = assemble_frozen_project(
        &frozen,
        &[AcceptedScc {
            stubbed_items: vec![],
            members: vec![frozen.functions[0].record.id],
            source: replacement.source,
        }],
    )
    .unwrap();
    run_compiler_on_str(&assembled, |_| ()).unwrap();
    let changed = signature.replacen('<', "<'unused, ", 1);
    assert!(
        replace_unstructured_scc(
            &frozen,
            &UnstructuredReplacementRequest {
                members: vec![frozen.functions[0].record.id],
                transformation: format!("{changed} {{ p[1] }}"),
            }
        )
        .is_err()
    );
}

#[test]
fn unstructured_rewrites_every_member_of_a_recursive_scc_together() {
    let frozen = freeze(
        "pub unsafe fn even(x: u32) -> bool { if x == 0 { true } else { odd(x - 1) } } pub unsafe fn odd(x: u32) -> bool { if x == 0 { false } else { even(x - 1) } }",
    );
    let members = frozen
        .functions
        .iter()
        .map(|function| function.record.id)
        .collect::<Vec<_>>();
    let transformation = frozen
        .functions
        .iter()
        .map(|function| {
            format!(
                "{} {{ x % 2 == {} }}",
                function.record.target_signature,
                if function.record.name == "even" { 0 } else { 1 }
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    let replacement = replace_unstructured_scc(
        &frozen,
        &UnstructuredReplacementRequest {
            members: members.clone(),
            transformation,
        },
    )
    .unwrap();
    assert_eq!(replacement.new_correspondence.len(), 2);
    let assembled = assemble_frozen_project(
        &frozen,
        &[AcceptedScc {
            stubbed_items: vec![],
            members,
            source: replacement.source,
        }],
    )
    .unwrap();
    run_compiler_on_str(&assembled, |_| ()).unwrap();
}

#[test]
fn transformed_types_remain_fixed_through_replacement_assembly_and_finalization() {
    let source = r#"
pub const LIMIT: i32 = 4;
pub struct Holder { pub pointer: *const i32 }
pub unsafe fn get(holder: *const Holder) -> *const i32 { (*holder).pointer }
"#;
    let frozen = freeze(source);
    assert_ne!(
        frozen.types[0].source_definition,
        frozen.types[0].target_definition
    );
    let function = &frozen.functions[0];
    let returned = function
        .record
        .baseline
        .skeleton
        .replace("todo!()", "holder.pointer");
    let output = transform_frozen_scc(&frozen, &request(function, Some(&returned)))
        .unwrap()
        .0;
    run_compiler_on_str(&output.replacement.source, utils::type_check)
        .expect(&output.replacement.source);
    let assembled = assemble_frozen_project(
        &frozen,
        &[AcceptedScc {
            stubbed_items: vec![],
            members: vec![function.record.id],
            source: output.replacement.source.clone(),
        }],
    )
    .unwrap();
    let finalized = finalize_frozen_project(&frozen, &assembled, "library", &[]).unwrap();
    run_compiler_on_str(&finalized.source, utils::type_check).expect(&finalized.source);
    assert!(
        finalized
            .source
            .contains(&frozen.types[0].target_definition)
    );
    for source in [
        assembled.replace("LIMIT: i32 = 4", "LIMIT: i32 = 5"),
        assembled.replace(
            &frozen.types[0].target_definition,
            &frozen.types[0].source_definition,
        ),
    ] {
        assert!(
            check_frozen_project_sources(&frozen, &frozen.analysis_source, Some(&source), false)
                .is_err()
        );
        assert!(finalize_frozen_project(&frozen, &source, "library", &[]).is_err());
    }
    let mut tampered = frozen.clone();
    tampered.target_source = tampered
        .target_source
        .replace("LIMIT: i32 = 4", "LIMIT: i32 = 5");
    assert!(frozen_project_from_json(&serde_json::to_string(&tampered).unwrap()).is_err());
}

#[test]
fn generated_nested_reference_bounds_survive_frozen_loading_validation_and_replacement() {
    let source = r#"
pub unsafe fn identity(head: *const *const i32) -> *const *const i32 { head }
"#;
    let frozen = freeze(source);
    let frozen = frozen_project_from_json(&serde_json::to_string(&frozen).unwrap()).unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
    let function = &frozen.functions[0];
    assert!(
        function.record.target_signature.contains("'b: 'a"),
        "{}",
        function.record.target_signature
    );
    let returned = format!(
        r#"{} {{
        #[proctor(0)] head
    }}"#,
        function.record.target_signature
    );
    let validation = |transformation| {
        crate::validate(&crate::ValidationRequest {
            expected_functions: vec![crate::ExpectedFunction {
                id: function.record.id,
                name: function.record.name.clone(),
                view: function.record.baseline.clone(),
            }],
            transformation,
        })
    };
    assert_eq!(
        validation(returned.clone()),
        crate::ValidationResponse::Valid
    );
    let output = transform_frozen_scc(&frozen, &request(function, Some(&returned)))
        .unwrap()
        .0;
    run_compiler_on_str(&output.replacement.source, utils::type_check)
        .expect(&output.replacement.source);
    let unlabeled = (0..1).fold(returned.clone(), |source, label| {
        source.replace(&format!("#[proctor({label})]"), "")
    });
    let unstructured = replace_unstructured_scc(
        &frozen,
        &UnstructuredReplacementRequest {
            members: vec![function.record.id],
            transformation: unlabeled.clone(),
        },
    )
    .unwrap();
    run_compiler_on_str(&unstructured.source, utils::type_check).expect(&unstructured.source);
    for bound in ["'b", "'b: 'static", "'b: 'a + 'static"] {
        let changed = returned.replace("'b: 'a", bound);
        assert!(matches!(
            validation(changed.clone()),
            crate::ValidationResponse::Invalid { .. }
        ));
        assert!(transform_frozen_scc(&frozen, &request(function, Some(&changed))).is_err());
        assert!(
            replace_unstructured_scc(
                &frozen,
                &UnstructuredReplacementRequest {
                    members: vec![function.record.id],
                    transformation: unlabeled.replace("'b: 'a", bound),
                }
            )
            .is_err()
        );
    }
    let assembled = assemble_frozen_project(
        &frozen,
        &[AcceptedScc {
            stubbed_items: vec![],
            members: vec![function.record.id],
            source: output.replacement.source,
        }],
    )
    .unwrap();
    let finalized =
        finalize_frozen_project(&frozen, &assembled, "library", &["identity".to_owned()]).unwrap();
    run_compiler_on_str(&finalized.source, utils::type_check).expect(&finalized.source);
    assert!(finalized.source.contains("'b: 'a"));
}
