use utils::compilation::run_compiler_on_str;

use super::*;
use crate::{
    PrintfTemplateMetadata, StatementDisposition, StatementDispositionKind, StatementPairMetadata,
};

fn skeleton_view(skeleton: &str, transformed: Vec<u32>, needs: bool) -> SkeletonView {
    with_parse_session(|| {
        let krate = parse_crate(skeleton, ReplacementErrorKind::InvalidRequest)?;
        let transformed_set = transformed.iter().copied().collect();
        let statement_dispositions = crate::preservation::make_disposition_forest(
            &krate.items[0],
            &transformed_set,
            &HashSet::new(),
            &HashSet::new(),
            &HashSet::new(),
        )
        .map_err(|problem| global_error(ReplacementErrorKind::InvalidRequest, problem.message))?;
        Ok(SkeletonView {
            skeleton: skeleton.to_owned(),
            needs_transformation: needs,
            statement_dispositions,
            statement_pair_metadata: transformed
                .into_iter()
                .map(|label| StatementPairMetadata {
                    label,
                    before_statement: "test".to_owned(),
                    printf_template: canonical_statement_group(&krate.items[0], label)
                        .and_then(|group| (group.len() == 1).then_some(group))
                        .and_then(|group| parse_print_macro_statement(&group[0]).ok())
                        .map(|parsed| PrintfTemplateMetadata {
                            rust_format: parsed.format,
                            argument_count: parsed.arguments.len() as u32,
                        }),
                    pointer_variables_complete: true,
                    pointer_variables: vec![],
                })
                .collect(),
        })
    })
    .unwrap()
}

fn replacement_item(id: u64, path: impl Into<String>, name: impl Into<String>) -> ReplacementItem {
    let name = name.into();
    ReplacementItem {
        id,
        path: path.into(),
        view: skeleton_view(&format!("unsafe fn {name}() {{}}"), vec![], false),
        name,
    }
}

fn preservation_item(
    id: u64,
    path: &str,
    name: &str,
    skeleton: &str,
    transformed: Vec<u32>,
) -> ReplacementItem {
    ReplacementItem {
        id,
        path: path.to_owned(),
        name: name.to_owned(),
        view: skeleton_view(skeleton, transformed.clone(), !transformed.is_empty()),
    }
}

fn mixed_preservation_item(
    skeleton: &str,
    transformed: &[u32],
    rule_applied: &[u32],
) -> ReplacementItem {
    let view = with_parse_session(|| {
        let krate = parse_crate(skeleton, ReplacementErrorKind::InvalidRequest)?;
        let statement_dispositions = crate::preservation::make_disposition_forest(
            &krate.items[0],
            &transformed.iter().copied().collect(),
            &HashSet::new(),
            &rule_applied.iter().copied().collect(),
            &HashSet::new(),
        )
        .map_err(|problem| global_error(ReplacementErrorKind::InvalidRequest, problem.message))?;
        Ok(SkeletonView {
            skeleton: skeleton.to_owned(),
            needs_transformation: !transformed.is_empty(),
            statement_dispositions,
            statement_pair_metadata: transformed
                .iter()
                .copied()
                .map(|label| StatementPairMetadata {
                    label,
                    before_statement: "test".to_owned(),
                    printf_template: canonical_statement_group(&krate.items[0], label)
                        .and_then(|group| (group.len() == 1).then_some(group))
                        .and_then(|group| parse_print_macro_statement(&group[0]).ok())
                        .map(|parsed| PrintfTemplateMetadata {
                            rust_format: parsed.format,
                            argument_count: parsed.arguments.len() as u32,
                        }),
                    pointer_variables_complete: true,
                    pointer_variables: vec![],
                })
                .collect(),
        })
    })
    .unwrap();
    ReplacementItem {
        id: 7,
        path: "f".to_owned(),
        name: "f".to_owned(),
        view,
    }
}

fn request(path: &str, name: &str, transformation: &str) -> ReplacementRequest {
    let mut item = replacement_item(7, path, name);
    let transformation =
        fully_annotated(transformation).unwrap_or_else(|| transformation.to_owned());
    if transformation.contains("#[proctor(") {
        item.view = skeleton_view(
            &transformation,
            item.view.transform_labels(),
            item.view.needs_transformation,
        );
    }
    ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![item],
        transformation,
    }
}

fn fully_annotated(source: &str) -> Option<String> {
    struct TestLabeler {
        next: u32,
    }

    impl MutVisitor for TestLabeler {
        fn flat_map_stmt(&mut self, mut statement: Stmt) -> SmallVec<[Stmt; 1]> {
            let attributes = match &mut statement.kind {
                StmtKind::Let(local) => &mut local.attrs,
                StmtKind::Item(item) => &mut item.attrs,
                StmtKind::Expr(expression) | StmtKind::Semi(expression) => &mut expression.attrs,
                StmtKind::MacCall(mac) => &mut mac.attrs,
                StmtKind::Empty => return smallvec::smallvec![statement],
            };
            attributes.extend(utils::attr!("#[proctor({})]", self.next));
            self.next += 1;
            mut_visit::walk_flat_map_stmt(self, statement)
        }
    }

    with_parse_session(|| {
        let mut krate = parse_crate(source, ReplacementErrorKind::InvalidTransformation)?;
        ProctorLabelRemover.visit_crate(&mut krate);
        for item in &mut krate.items {
            if let ItemKind::Fn(box function) = &mut item.kind {
                TestLabeler { next: 0 }.visit_block(function.body.as_mut().unwrap());
            }
        }
        Ok(pprust::crate_to_string_for_macros(&krate))
    })
    .ok()
}

fn request_with_items(mut items: Vec<ReplacementItem>, transformation: &str) -> ReplacementRequest {
    let transformation = fully_annotated(transformation).unwrap();
    with_parse_session(|| {
        let krate = parse_crate(&transformation, ReplacementErrorKind::InvalidTransformation)?;
        for requested in &mut items {
            let item = krate
                .items
                .iter()
                .find(|item| {
                    item.kind
                        .ident()
                        .is_some_and(|ident| ident.to_string() == requested.name)
                })
                .unwrap();
            let skeleton = pprust::item_to_string(item);
            requested.view = skeleton_view(
                &skeleton,
                requested.view.transform_labels(),
                requested.view.needs_transformation,
            );
        }
        Ok(())
    })
    .unwrap();
    ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items,
        transformation,
    }
}

fn replace(source: &str, request: &ReplacementRequest) -> Result<String, ReplacementError> {
    run_compiler_on_str(source, |tcx| {
        replace_items(source, request, tcx).map(|output| output.source)
    })
    .unwrap()
}

fn replace_output(
    source: &str,
    request: &ReplacementRequest,
) -> Result<ReplacementOutput, ReplacementError> {
    run_compiler_on_str(source, |tcx| replace_items(source, request, tcx)).unwrap()
}

fn replace_extended(
    source: &str,
    request: &ReplacementRequest,
) -> Result<ExtendedReplacementOutput, ReplacementError> {
    run_compiler_on_str(source, |tcx| {
        replace_items_with_observations(source, request, tcx)
    })
    .unwrap()
}

#[test]
fn print_arguments_are_defended_without_validator() {
    let source = "unsafe fn f() {}";
    let skeleton = r#"unsafe fn f() { #[proctor(0)] ::std::print!("{}", todo!()); }"#;
    for argument in [
        "{ fn hidden() {} 1 }",
        "unsafe { 1 }",
        "{ #[allow(unused_variables)] let proctor_temp_var_0 = 1; proctor_temp_var_0 }",
        "{ let invented = 1; invented }",
        "{ let proctor_temp_var_0 = 1; helper!(proctor_temp_var_0); proctor_temp_var_0 }",
    ] {
        let request = ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, "f", "f", skeleton, vec![0])],
            transformation: format!(
                r#"unsafe fn f() {{ #[proctor(0)] ::std::print!("{{}}", {argument}); }}"#
            ),
            accepted_correspondence: vec![],
        };
        let error = replace(source, &request).unwrap_err();
        assert_eq!(error.kind, ReplacementErrorKind::InvalidTransformation);
        assert!(error.message.contains("print argument"), "{error:?}");
    }

    let valid = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(7, "f", "f", skeleton, vec![0])],
        transformation:
            r#"unsafe fn f() { #[proctor(0)] ::std::print!("{}", value::<A, B>((a, b))); }"#
                .to_owned(),
        accepted_correspondence: vec![],
    };
    assert!(replace(source, &valid).is_ok());

    let local_temporary = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(7, "f", "f", skeleton, vec![0])],
        transformation: r#"unsafe fn f() { #[proctor(0)] ::std::print!("{}", { let proctor_temp_var_0 = 1; proctor_temp_var_0 }); }"#.to_owned(),
        accepted_correspondence: vec![],
    };
    assert!(replace(source, &local_temporary).is_ok());

    for argument in [
        "{ proctor_temp_var_0 + { let proctor_temp_var_0 = 1; proctor_temp_var_0 } }",
        "{ { let proctor_temp_var_0 = 1; } proctor_temp_var_0 }",
        "{ if true { let proctor_temp_var_0 = 1; } proctor_temp_var_0 }",
    ] {
        let request = ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, "f", "f", skeleton, vec![0])],
            transformation: format!(
                r#"unsafe fn f() {{ #[proctor(0)] ::std::print!("{{}}", {argument}); }}"#
            ),
            accepted_correspondence: vec![],
        };
        let error = replace(source, &request).unwrap_err();
        assert_eq!(error.kind, ReplacementErrorKind::InvalidTransformation);
        assert!(error.message.contains("lexical expansion scope"));
    }

    let two = r#"unsafe fn f() { #[proctor(0)] ::std::print!("{} {}", todo!(), todo!()); }"#;
    let cross_argument = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(7, "f", "f", two, vec![0])],
        transformation: r#"unsafe fn f() { #[proctor(0)] ::std::print!("{} {}", { let proctor_temp_var_0 = 1; proctor_temp_var_0 }, proctor_temp_var_0); }"#.to_owned(),
        accepted_correspondence: vec![],
    };
    let error = replace(source, &cross_argument).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::InvalidTransformation);
    assert!(error.message.contains("lexical expansion scope"));

    let existing = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "f",
            "f",
            r#"unsafe fn f(proctor_temp_var_0: i32) { #[proctor(0)] ::std::print!("{}", todo!()); }"#,
            vec![0],
        )],
        transformation: r#"unsafe fn f(proctor_temp_var_0: i32) { #[proctor(0)] ::std::print!("{}", proctor_temp_var_0); }"#.to_owned(),
        accepted_correspondence: vec![],
    };
    assert!(replace("unsafe fn f(proctor_temp_var_0: i32) {}", &existing).is_ok());
}

#[test]
fn print_template_invariants_are_defended_without_validator() {
    let source = "unsafe fn f() {}";
    let skeleton = r#"unsafe fn f() { #[proctor(0)] ::std::print!("{}/{:08x}/{}", todo!(), todo!(), todo!()); }"#;
    for statement in [
        r#"print!("{}/{:08x}/{}", a, b, c);"#,
        r#"std::print!("{}/{:08x}/{}", a, b, c);"#,
        r#"::std::println!("{}/{:08x}/{}", a, b, c);"#,
        r#"::core::print!("{}/{:08x}/{}", a, b, c);"#,
        r#"print("{}/{:08x}/{}", a, b, c);"#,
        r#"::std::print!["{}/{:08x}/{}", a, b, c];"#,
        r#"::std::print!{"{}/{:08x}/{}", a, b, c};"#,
        r#"{ ::std::print!("{}/{:08x}/{}", a, b, c); }"#,
        r#"::std::print!("changed", a, b, c);"#,
        r#"::std::print!("{1}/{0}/{}", a, b, c);"#,
        r#"::std::print!("{}/{:08x}/{}", a, b);"#,
        r#"::std::print!("{}/{:08x}/{}", a, b, c, d);"#,
        r#"::std::print!("{}/{:08x}/{}", name = a, b, c);"#,
    ] {
        let request = ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, "f", "f", skeleton, vec![0])],
            transformation: format!("unsafe fn f() {{ #[proctor(0)] {statement} }}"),
            accepted_correspondence: vec![],
        };
        let error = replace(source, &request).unwrap_err();
        assert_eq!(error.kind, ReplacementErrorKind::InvalidTransformation);
    }

    for statement in [
        r#"::std::print!("\x7b}/{:08x}/{}", a, b, c,);"#,
        r#"::std::print!("{}/{:08x}/{}", (a, b), { helper(a, b) }, value::<A, B>((a, b)));"#,
        r#"::std::print!("{}/{:08x}/{}", helper!(a), b, c);"#,
    ] {
        let request = ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, "f", "f", skeleton, vec![0])],
            transformation: format!("unsafe fn f() {{ #[proctor(0)] {statement} }}"),
            accepted_correspondence: vec![],
        };
        assert!(replace(source, &request).is_ok(), "{statement}");
    }

    for transformation in [
        r#"unsafe fn f() { #[proctor(0)] ::std::print!("{}/{:08x}/{}", a, b, c); #[proctor(0)] ::std::print!("{}/{:08x}/{}", a, b, c); }"#,
        r#"unsafe fn f() { #[proctor(0)] ::std::print!("{}/{:08x}/{}", a, b, c); consume(); }"#,
    ] {
        let request = ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, "f", "f", skeleton, vec![0])],
            transformation: transformation.to_owned(),
            accepted_correspondence: vec![],
        };
        assert_eq!(
            replace(source, &request).unwrap_err().kind,
            ReplacementErrorKind::InvalidTransformation
        );
    }
}

#[test]
fn aliased_printf_metadata_makes_corrupt_replacement_template_invalid_request() {
    let skeleton = r#"unsafe fn f() { #[proctor(0)] ::std::println!("{}"); }"#;
    let mut item = preservation_item(7, "f", "f", skeleton, vec![0]);
    item.view.statement_pair_metadata[0].printf_template = Some(PrintfTemplateMetadata {
        rust_format: "{}".to_owned(),
        argument_count: 1,
    });
    let request = ReplacementRequest {
        schema_version: 1,
        items: vec![item],
        transformation: skeleton.to_owned(),
        accepted_correspondence: vec![],
    };
    let error = replace("unsafe fn f() {}", &request).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::InvalidRequest);
}

#[test]
fn ordinary_candidate_and_statement_pairs_remain_exact() {
    let source = "pub unsafe fn read(mut pointer: *const i32) -> i32 { *pointer }";
    let request = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "read",
            "read",
            "pub unsafe fn read<'a>(mut pointer: &'a i32) -> i32 { #[proctor(0)] *pointer }",
            vec![0],
        )],
        transformation:
            "pub unsafe fn read<'a>(mut pointer: &'a i32) -> i32 { #[proctor(0)] *pointer }".into(),
        accepted_correspondence: vec![],
    };
    let ordinary = replace_output(source, &request).unwrap();
    let extended = replace_extended(source, &request).unwrap();
    assert_eq!(extended.replacement, ordinary);
    assert_eq!(
        extended.replacement.source.as_bytes(),
        concat!(
            "pub unsafe fn read<'a>(mut pointer: &'a i32) -> i32 { *pointer }\n",
            "pub unsafe fn __proctor_wrapper_read(mut pointer: *const i32) -> i32 {\n",
            "    let __proctor_result = crate::read(&*(pointer as *const i32));\n",
            "    __proctor_result\n",
            "}",
        )
        .as_bytes()
    );
    assert_eq!(
        extended.replacement.statement_pairs,
        vec![ReplacementStatementPair {
            item_id: 7,
            path: "read".to_owned(),
            label: 0,
            after_statement: "#[proctor(0)]\n*pointer".to_owned(),
        }]
    );
    assert_eq!(
        extended.new_correspondence[0].wrapper_path.as_deref(),
        Some("__proctor_wrapper_read")
    );
    assert_eq!(
        extended.current_items[0].source_copy_path,
        "__proctor_source_read"
    );
    assert_eq!(extended.current_items[0].transform_labels, vec![0]);
    let sidecar = concat!(
        "{\n  \"schema_version\": 1,\n  \"statements\": [\n    {\n",
        "      \"item_id\": 7,\n      \"path\": \"read\",\n      \"label\": 0,\n",
        "      \"after_statement\": \"#[proctor(0)]\\n*pointer\"\n    }\n  ]\n}",
    );
    let metadata = crate::ReplacementObservationMetadata::from_output(
        &extended,
        extended.replacement.source.as_bytes(),
        sidecar.as_bytes(),
        extended.observation_source.as_bytes(),
    );
    assert_eq!(
        metadata.candidate_sha256,
        crate::sha256_hex(extended.replacement.source.as_bytes())
    );
    assert_eq!(
        metadata.statement_pairs_sha256,
        crate::sha256_hex(sidecar.as_bytes())
    );
    assert_eq!(
        metadata.observation_source_sha256,
        crate::sha256_hex(extended.observation_source.as_bytes())
    );
}

#[test]
fn ordinary_call_shaped_metadata_never_confers_replacement_printf_provenance() {
    let source = "unsafe fn f() {}";
    let mut item = preservation_item(
        7,
        "f",
        "f",
        "unsafe fn f() { #[proctor(0)] todo!(); }",
        vec![0],
    );
    item.view.statement_pair_metadata[0].before_statement =
        r#"foo(b"%d\0" as *const u8 as *const i8, value);"#.to_owned();
    let request = ReplacementRequest {
        schema_version: 1,
        items: vec![item],
        transformation:
            r#"unsafe fn f() { #[proctor(0)] foo(b"%d\0" as *const u8 as *const i8, value); }"#
                .to_owned(),
        accepted_correspondence: vec![],
    };
    assert!(replace(source, &request).is_ok());
}

#[test]
fn source_copy_names_avoid_module_collisions_without_moving_wrappers() {
    let source = r#"
mod a {
    fn __proctor_source_read() {}
    fn __proctor_source_read_0() {}
    fn __proctor_wrapper_read() {}
    pub unsafe fn read(mut pointer: *const i32) -> i32 { *pointer }
}
mod b { pub unsafe fn read(mut pointer: *const i32) -> i32 { *pointer } }
"#;
    let target = "unsafe fn read(mut pointer: &i32) -> i32 { #[proctor(0)] *pointer }";
    let request_for = |id, path| ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(id, path, "read", target, vec![0])],
        transformation: target.into(),
        accepted_correspondence: vec![],
    };
    let a = replace_extended(source, &request_for(7, "a::read")).unwrap();
    assert_eq!(
        a.current_items[0].source_copy_path,
        "a::__proctor_source_read_1"
    );
    assert_eq!(
        a.new_correspondence[0].wrapper_path.as_deref(),
        Some("a::__proctor_wrapper_read_0")
    );
    let mut b_request = request_for(8, "b::read");
    b_request.accepted_correspondence = a.new_correspondence.clone();
    let b = replace_extended(&a.replacement.source, &b_request).unwrap();
    assert_eq!(
        b.current_items[0].source_copy_path,
        "b::__proctor_source_read"
    );
    assert_eq!(
        b.new_correspondence[0].wrapper_path.as_deref(),
        Some("b::__proctor_wrapper_read")
    );

    let raw = replace_extended(
        "pub unsafe fn r#type(pointer: *const i32) -> i32 { *pointer }",
        &ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(
                9,
                "r#type",
                "r#type",
                "unsafe fn r#type(pointer: &i32) -> i32 { #[proctor(0)] *pointer }",
                vec![0],
            )],
            transformation: "unsafe fn r#type(pointer: &i32) -> i32 { #[proctor(0)] *pointer }"
                .into(),
            accepted_correspondence: vec![],
        },
    )
    .unwrap();
    assert_eq!(
        raw.current_items[0].source_copy_path,
        "__proctor_source_type"
    );
}

#[test]
fn observation_functions_strip_outer_attributes_but_keep_statement_labels() {
    let source = "#[inline(never)] #[no_mangle] pub unsafe extern \"C\" fn read(mut pointer: *const i32) -> i32 { *pointer }";
    let request = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "read",
            "read",
            "pub unsafe fn read(mut pointer: &i32) -> i32 { #[proctor(0)] *pointer }",
            vec![0],
        )],
        transformation: "pub unsafe fn read(mut pointer: &i32) -> i32 { #[proctor(0)] *pointer }"
            .into(),
        accepted_correspondence: vec![],
    };
    let ordinary = replace_output(source, &request).unwrap();
    let extended = replace_extended(source, &request).unwrap();
    assert_eq!(extended.replacement, ordinary);
    let output = extended.observation_source;
    assert!(!output.contains("no_mangle"));
    assert!(!output.contains("inline"));
    assert_eq!(output.matches("#[proctor(0)]").count(), 2);
    assert!(output.contains("unsafe fn __proctor_source_read"));
    assert!(output.contains("fn __proctor_wrapper_read"));
    compile(&output.replace("#[proctor(0)]", ""));
}

#[test]
fn deterministic_relabeler_labels_real_source_after_earlier_call_redirect() {
    let source = r#"
unsafe fn callee(pointer: &i32) -> i32 { *pointer }
unsafe fn __proctor_wrapper_callee(pointer: *const i32) -> i32 { callee(&*pointer) }
pub unsafe fn caller(pointer: *const i32) -> i32 { __proctor_wrapper_callee(pointer) }
"#;
    let target = "pub unsafe fn caller(pointer: &i32) -> i32 { #[proctor(0)] callee(pointer) }";
    let output = replace_extended(
        source,
        &ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, "caller", "caller", target, vec![0])],
            transformation: target.into(),
            accepted_correspondence: vec![CallableCorrespondence {
                item_id: 3,
                logical_path: "callee".into(),
                implementation_path: "callee".into(),
                wrapper_path: Some("__proctor_wrapper_callee".into()),
            }],
        },
    )
    .unwrap();
    let observation = compact(&output.observation_source);
    assert!(observation.contains(
        "unsafe fn __proctor_source_caller(pointer: *const i32) -> i32 { #[proctor(0)] __proctor_wrapper_callee(pointer) }"
    ));
    assert!(observation.contains("#[proctor(0)] callee(pointer)"));
}

#[test]
fn source_clone_relabeling_needs_no_expected_label_sidecar() {
    let source = r#"pub unsafe fn read(pointer: *const i32) -> i32 {
        let value = 1;
        *pointer + value
    }"#;
    let target = r#"pub unsafe fn read(pointer: &i32) -> i32 {
        #[proctor(0)] let value: i32 = 1;
        #[proctor(1)] *pointer + value
    }"#;
    let output = replace_extended(
        source,
        &ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, "read", "read", target, vec![1])],
            transformation: target.into(),
            accepted_correspondence: vec![],
        },
    )
    .unwrap();
    assert_eq!(output.current_items[0].transform_labels, vec![1]);
    assert_eq!(
        output.observation_source.matches("#[proctor(0)]").count(),
        2
    );
    assert_eq!(
        output.observation_source.matches("#[proctor(1)]").count(),
        2
    );
    let metadata = crate::ReplacementObservationMetadata::from_output(
        &output,
        output.replacement.source.as_bytes(),
        b"",
        output.observation_source.as_bytes(),
    );
    let document =
        crate::observation::extract_observations_from_source(&output.observation_source, &metadata)
            .unwrap();
    assert_eq!(document.observations.len(), 1);
    let observation = &document.observations[0];
    assert_eq!(observation.pointer_anchors[0].id, "<id0>");
    assert!(matches!(
        observation.pointer_anchors[0].source_type,
        crate::TypeTree::RawPointer { .. }
    ));
    assert!(matches!(
        observation.pointer_anchors[0].target_type,
        crate::TypeTree::Reference { .. }
    ));
    for ty in [
        &observation.source_type,
        &observation.source_adjusted_type,
        &observation.target_type,
        &observation.target_adjusted_type,
    ] {
        assert_eq!(ty, &crate::TypeTree::Primitive { name: "i32".into() });
    }
}

#[test]
fn source_copy_recursion_uses_absolute_copy_path() {
    let source = r#"
mod nested {
    pub unsafe fn sum(mut pointer: *const i32, mut count: usize) -> i32 {
        if count == 0 { 0 } else { *pointer + sum(pointer.add(1), count - 1) }
    }
}
"#;
    let target = r#"
unsafe fn sum(mut pointer: &[i32], mut count: usize) -> i32 {
    #[proctor(0)]
    if count == 0 {
        #[proctor(1)]
        0
    } else {
        #[proctor(2)]
        pointer[0] + sum(&pointer[1..], count - 1)
    }
}
"#;
    let request = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "nested::sum",
            "sum",
            target,
            vec![0, 1, 2],
        )],
        transformation: target.into(),
        accepted_correspondence: vec![],
    };
    let output = replace_extended(source, &request).unwrap();
    assert_eq!(output.current_items[0].logical_path, "nested::sum");
    assert_eq!(
        output.current_items[0].source_copy_path,
        "nested::__proctor_source_sum"
    );
    let observation = compact(&output.observation_source);
    assert!(observation.contains("crate::nested::__proctor_source_sum(pointer.add(1), count - 1)"));
    assert!(observation.contains("pointer[0] + sum(&pointer[1..], count - 1)"));
    assert!(!observation.contains("pointer[0] + crate::nested::sum("));
    let label_free = output
        .observation_source
        .replace("#[proctor(0)]", "")
        .replace("#[proctor(1)]", "")
        .replace("#[proctor(2)]", "");
    compile(&label_free);
}

#[test]
fn mutual_scc_copies_call_each_other_in_item_order() {
    let source = r#"
pub unsafe fn even(pointer: *const i32, n: usize) -> i32 {
    if n == 0 { *pointer } else { odd(pointer, n - 1) }
}
pub unsafe fn odd(pointer: *const i32, n: usize) -> i32 {
    if n == 0 { *pointer } else { even(pointer, n - 1) }
}
"#;
    let target = r#"
unsafe fn even(pointer: &i32, n: usize) -> i32 {
    #[proctor(0)] if n == 0 { #[proctor(1)] *pointer } else { #[proctor(2)] odd(pointer, n - 1) }
}
unsafe fn odd(pointer: &i32, n: usize) -> i32 {
    #[proctor(0)] if n == 0 { #[proctor(1)] *pointer } else { #[proctor(2)] even(pointer, n - 1) }
}
"#;
    let even_view = "unsafe fn even(pointer: &i32, n: usize) -> i32 { #[proctor(0)] if n == 0 { #[proctor(1)] *pointer } else { #[proctor(2)] odd(pointer, n - 1) } }";
    let odd_view = "unsafe fn odd(pointer: &i32, n: usize) -> i32 { #[proctor(0)] if n == 0 { #[proctor(1)] *pointer } else { #[proctor(2)] even(pointer, n - 1) } }";
    let output = replace_extended(
        source,
        &request_with_items(
            vec![
                preservation_item(7, "odd", "odd", odd_view, vec![0, 1, 2]),
                preservation_item(3, "even", "even", even_view, vec![0, 1, 2]),
            ],
            target,
        ),
    )
    .unwrap();
    assert_eq!(
        output.new_correspondence,
        vec![
            CallableCorrespondence {
                item_id: 7,
                logical_path: "odd".into(),
                implementation_path: "odd".into(),
                wrapper_path: Some("__proctor_wrapper_odd".into()),
            },
            CallableCorrespondence {
                item_id: 3,
                logical_path: "even".into(),
                implementation_path: "even".into(),
                wrapper_path: Some("__proctor_wrapper_even".into()),
            },
        ]
    );
    assert_eq!(
        output
            .current_items
            .iter()
            .map(|item| (
                item.item_id,
                item.logical_path.as_str(),
                item.source_copy_path.as_str(),
                item.implementation_path.as_str(),
                item.wrapper_path.as_deref(),
                item.transform_labels.as_slice(),
            ))
            .collect::<Vec<_>>(),
        vec![
            (
                7,
                "odd",
                "__proctor_source_odd",
                "odd",
                Some("__proctor_wrapper_odd"),
                &[0, 1, 2][..]
            ),
            (
                3,
                "even",
                "__proctor_source_even",
                "even",
                Some("__proctor_wrapper_even"),
                &[0, 1, 2][..]
            ),
        ]
    );
    let observation = compact(&output.observation_source);
    assert!(observation.contains("crate::__proctor_source_even(pointer, n - 1)"));
    assert!(observation.contains("crate::__proctor_source_odd(pointer, n - 1)"));
    assert!(observation.contains("odd(pointer, n - 1)"));
    assert!(observation.contains("even(pointer, n - 1)"));
}

#[test]
fn two_argument_main_boundary_has_no_logical_copy() {
    let source = r#"
pub unsafe fn main_0(argc: i32, argv: *mut *mut i8) -> i32 { argc + (**argv != 0) as i32 }
pub fn main() {
    unsafe { std::process::exit(main_0(0, std::ptr::null_mut())) }
}
"#;
    let target = r#"pub unsafe fn main_0(argc: i32, argv: &mut [&mut [i8]]) -> i32 {
        #[proctor(0)] argc + (argv[0][0] != 0) as i32
    }"#;
    let output = replace_extended(
        source,
        &ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, "main_0", "main_0", target, vec![0])],
            transformation: target.into(),
            accepted_correspondence: vec![],
        },
    )
    .unwrap();
    assert_eq!(output.current_items.len(), 1);
    assert_eq!(output.current_items[0].logical_path, "main_0");
    assert_eq!(output.new_correspondence.len(), 1);
    assert!(!output.observation_source.contains("__proctor_source_main("));
    assert!(
        compact(&output.observation_source)
            .contains("main_0(argc, command_line_arg_slices.as_mut_slice())")
    );
}

#[test]
fn macro_hidden_copy_call_rewrite_is_fatal() {
    let source = r#"
macro_rules! recurse { ($p:expr) => { read($p) }; }
pub unsafe fn read(pointer: *const i32) -> i32 {
    if pointer.is_null() { 0 } else { recurse!(pointer) }
}
"#;
    let target = r#"pub unsafe fn read(pointer: Option<&i32>) -> i32 {
        #[proctor(0)] if pointer.is_none() {
            #[proctor(1)] 0
        } else {
            #[proctor(2)] read(pointer)
        }
    }"#;
    let error = replace_extended(
        source,
        &ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, "read", "read", target, vec![0, 1, 2])],
            transformation: target.into(),
            accepted_correspondence: vec![],
        },
    )
    .unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::UnsupportedCallRewrite);
}

#[test]
fn accepted_wrapper_correspondence_is_echoed_and_used() {
    let source = r#"
unsafe fn callee(mut pointer: &i32) -> i32 { *pointer }
unsafe fn __proctor_wrapper_callee(mut pointer: *const i32) -> i32 {
    callee(&*pointer)
}
pub unsafe fn caller(mut pointer: *const i32) -> i32 {
    __proctor_wrapper_callee(pointer)
}
"#;
    let target = r#"
pub unsafe fn caller(mut pointer: &i32) -> i32 {
    #[proctor(0)]
    callee(pointer)
}
"#;
    let accepted = CallableCorrespondence {
        item_id: 3,
        logical_path: "callee".into(),
        implementation_path: "callee".into(),
        wrapper_path: Some("__proctor_wrapper_callee".into()),
    };
    let request = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(7, "caller", "caller", target, vec![0])],
        transformation: target.into(),
        accepted_correspondence: vec![accepted.clone()],
    };
    let output = replace_extended(source, &request).unwrap();
    assert_eq!(output.accepted_correspondence, vec![accepted]);
    assert_eq!(
        output.new_correspondence,
        vec![CallableCorrespondence {
            item_id: 7,
            logical_path: "caller".into(),
            implementation_path: "caller".into(),
            wrapper_path: Some("__proctor_wrapper_caller".into()),
        }]
    );
    assert_eq!(
        output.current_items[0].source_copy_path,
        "__proctor_source_caller"
    );
    assert_eq!(output.current_items[0].transform_labels, vec![0]);

    let metadata = crate::ReplacementObservationMetadata::from_output(
        &output,
        output.replacement.source.as_bytes(),
        b"",
        output.observation_source.as_bytes(),
    );
    let document =
        crate::observation::extract_observations_from_source(&output.observation_source, &metadata)
            .unwrap();
    assert_eq!(document.observations.len(), 1);
    let observation = &document.observations[0];
    assert_eq!(observation.pointer_anchors.len(), 1);
    assert_eq!(observation.pointer_anchors[0].id, "<id0>");
    assert_eq!(
        observation.source_type,
        crate::TypeTree::RawPointer {
            mutability: crate::RawMutability::Const,
            pointee: Box::new(crate::TypeTree::Primitive { name: "i32".into() }),
        }
    );
    assert_eq!(
        observation.target_type,
        crate::TypeTree::Reference {
            mutability: crate::RefMutability::Shared,
            pointee: Box::new(crate::TypeTree::Primitive { name: "i32".into() }),
        }
    );
    let mut omitted = metadata;
    omitted.accepted_correspondence.clear();
    assert!(
        crate::observation::extract_observations_from_source(&output.observation_source, &omitted)
            .unwrap()
            .observations
            .is_empty()
    );
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
  "items": [{"id":7,"path":"f","name":"f","view":{"skeleton":"unsafe fn f(value: i32) -> i32 { #[proctor(0)] todo!() }","needs_transformation":true,"statement_dispositions":[{"label":0,"disposition":"transform","children":[]}],"statement_pair_metadata":[{"label":0,"before_statement":"test","printf_template":null,"pointer_variables_complete":true,"pointer_variables":[]}]}}],
  "transformation": "unsafe fn f(value: i32) -> i32 {\n #[proctor(0)]\n value + 1\n}",
  "accepted_correspondence": []
}"#;
    let request = replacement_request_from_json(json).unwrap();
    assert_eq!(request.schema_version, 1);
    assert!(request.transformation.contains("#[proctor(0)]"));
    let output = replace("pub unsafe fn f(value: i32) -> i32 { value }", &request).unwrap();
    assert!(compact(&output).contains("value + 1"));
}

#[test]
fn replacement_discards_preserved_groups_without_validator() {
    let source = "pub unsafe fn f(value: i32) -> i32 { value + 1 }";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "f",
            "f",
            "unsafe fn f(value: i32) -> i32 { #[proctor(0)] value + 1 }",
            vec![],
        )],
        transformation: "unsafe fn f(value: i32) -> i32 { #[proctor(0)] let proctor_temp_var_0 = value * 100; #[proctor(0)] proctor_temp_var_0 }".to_owned(),
    };
    let output = replace(source, &request).unwrap();
    assert!(compact(&output).contains("value + 1"));
    assert!(!output.contains("proctor_temp_var_0"));
    compile(&output);
}

#[test]
fn preserved_restricted_conditional_has_only_its_outer_label() {
    let source =
        "pub unsafe fn f(value: i32) -> i32 { return value + (if value > 0 { -1 } else { 1 }); }";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "f",
            "f",
            "unsafe fn f(value: i32) -> i32 { #[proctor(0)] return value + (if value > 0 { -1 } else { 1 }); }",
            vec![],
        )],
        transformation:
            "unsafe fn f(value: i32) -> i32 { #[proctor(0)] return value + (if value > 0 { 99 } else { 100 }); }"
                .to_owned(),
    };
    let output = replace(source, &request).unwrap();
    let text = compact(&output);
    assert!(text.contains("return value + (if value > 0 { -1 } else { 1 })"));
    assert!(!text.contains("99"));
    assert!(!text.contains("100"));
    compile(&output);
}

#[test]
fn restricted_conditional_does_not_hide_other_label_subtrees() {
    let source = r#"
pub unsafe fn f(mut pointer: *mut i32, value: i32, flag: bool) -> i32 {
    let conditional = value + (if flag { -1 } else { 1 });
    if flag {
        *pointer = value;
    }
    conditional
}
"#;
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "f",
            "f",
            r#"
unsafe fn f(mut pointer: *mut i32, value: i32, flag: bool) -> i32 {
    #[proctor(0)]
    let mut conditional: i32 = value + (if flag { -1 } else { 1 });
    #[proctor(1)]
    if flag {
        #[proctor(2)]
        *pointer = value;
    }
    #[proctor(3)]
    conditional
}
"#,
            vec![1, 2],
        )],
        transformation: r#"
unsafe fn f(mut pointer: *mut i32, value: i32, flag: bool) -> i32 {
    #[proctor(0)]
    let mut conditional: i32 = value + (if flag { 99 } else { 100 });
    #[proctor(1)]
    if flag {
        #[proctor(2)]
        *pointer = value + 1;
    }
    #[proctor(3)]
    300
}
"#
        .to_owned(),
    };
    let output = replace(source, &request).unwrap();
    let text = compact(&output);
    assert!(text.contains("value + (if flag { -1 } else { 1 })"));
    assert!(text.contains("*pointer = value + 1"));
    assert!(text.ends_with("conditional }"));
    assert!(!text.contains("99"));
    assert!(!text.contains("100"));
    assert!(!text.contains("300"));
    compile(&output);
}

#[test]
fn replacement_accepts_bare_assignment_labels() {
    let source = r#"
pub struct State {
    pub first: i32,
    pub second: i32,
}
pub unsafe fn f(mut state: State, value: i32) -> State {
    state.first = value;
    state.second += 1;
    state
}
"#;
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "f",
            "f",
            "unsafe fn f(mut state: State, value: i32) -> State { #[proctor(0)] state.first = value; #[proctor(1)] state.second += 2; #[proctor(2)] state }",
            vec![0, 1],
        )],
        transformation: "unsafe fn f(mut state: State, value: i32) -> State { #[proctor(0)] state.first = value + 1; #[proctor(1)] state.second += 2; #[proctor(2)] state }".to_owned(),
    };
    let output = replace(source, &request).unwrap();
    let text = compact(&output);
    assert!(text.contains("state.first = value + 1"));
    assert!(text.contains("state.second += 2"));
    assert!(!text.contains("proctor"));
    compile(&output);
}

#[test]
fn replacement_restores_every_preserved_validator_group() {
    let source = r#"
pub unsafe fn validate_me(flag: bool, mut pointer: *mut i32) -> i32 {
    let scalar = 1 + 2;
    if flag {
        let nested = 3 + 4;
        *pointer = nested;
    } else {
        return scalar;
    }
    scalar
}
"#;
    let skeleton = r#"
unsafe fn validate_me(flag: bool, pointer: *mut i32) -> i32 {
    #[proctor(0)]
    let scalar: i32 = 1 + 2;
    #[proctor(1)]
    if todo!() {
        #[proctor(2)]
        let nested: i32 = 3 + 4;
        #[proctor(3)]
        (*pointer = todo!());
    } else {
        #[proctor(4)]
        return scalar;
    }
    #[proctor(5)]
    scalar
}
"#;
    let transformation = r#"
unsafe fn validate_me(flag: bool, pointer: *mut i32) -> i32 {
    #[proctor(0)]
    let scalar: i32 = 999;
    #[proctor(1)]
    if flag {
        #[proctor(2)]
        let nested: i32 = -100;
        #[proctor(3)]
        (*pointer = nested);
    } else {
        #[proctor(4)]
        return -200;
    }
    #[proctor(5)]
    300
}
"#;
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "validate_me",
            "validate_me",
            skeleton,
            vec![1, 3],
        )],
        transformation: transformation.to_owned(),
    };
    let output = replace(source, &request).unwrap();
    let text = compact(&output);
    for canonical in ["1 + 2", "3 + 4", "return scalar", "} scalar }"] {
        assert!(text.contains(canonical), "{text}");
    }
    for discarded in ["999", "-100", "-200", "300"] {
        assert!(!text.contains(discarded), "{text}");
    }
    assert!(text.contains("*pointer = nested"));
    assert!(!text.contains("proctor"));
    compile(&output);
}

#[test]
fn replacement_independently_restores_mixed_rule_applied_topologies() {
    let source =
        "unsafe fn consume(_: i32) {} pub unsafe fn f(flag: bool) { if flag { consume(1); } }";
    let cases = [
        (
            r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag { #[proctor(1)] consume(1); }
}"#,
            vec![1],
            vec![0],
            r#"unsafe fn f(flag: bool) {
#[proctor(0)] if !flag { #[proctor(1)] consume(5); }
}"#,
            "if flag { consume(5); }",
        ),
        (
            r#"unsafe fn f(flag: bool) {
#[proctor(0)] if true { #[proctor(1)] consume(2); }
}"#,
            vec![0],
            vec![1],
            r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag { #[proctor(1)] consume(999); }
}"#,
            "if flag { consume(2); }",
        ),
    ];
    for (skeleton, transformed, applied, transformation, expected) in cases {
        let request = ReplacementRequest {
            accepted_correspondence: vec![],
            schema_version: 1,
            items: vec![mixed_preservation_item(skeleton, &transformed, &applied)],
            transformation: transformation.to_owned(),
        };
        let output = replace(source, &request).unwrap();
        assert!(compact(&output).contains(expected), "{output}");
    }
}

#[test]
fn replacement_restores_preserved_shell_and_keeps_transformed_child() {
    let source =
        "unsafe fn consume(_: i32) {} pub unsafe fn f(flag: bool) { if flag { consume(1); } }";
    let skeleton = r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag { #[proctor(1)] consume(1); }
}"#;
    let mut item = mixed_preservation_item(skeleton, &[1], &[]);
    item.view.statement_dispositions[0].disposition = StatementDispositionKind::PreserveShell;
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![item],
        transformation: r#"unsafe fn f(flag: bool) {
#[proctor(0)] if !flag { #[proctor(1)] consume(2); }
}"#
        .to_owned(),
    };

    let output = replace(source, &request).unwrap();
    assert!(
        compact(&output).contains("if flag { consume(2); }"),
        "{output}"
    );
}

#[test]
fn replacement_atomically_rejects_invalid_mixed_rule_applied_descendants() {
    let source = "unsafe fn consume(_: i32) {} pub unsafe fn f(flag: bool) { if flag { consume(1); consume(2); } }";
    let outer_rule = r#"unsafe fn f(flag: bool) {
#[proctor(0)] if flag { #[proctor(1)] consume(1); #[proctor(2)] consume(2); }
}"#;
    let inner_rule = r#"unsafe fn f(flag: bool) {
#[proctor(0)] if true { #[proctor(1)] consume(1); #[proctor(2)] consume(2); }
}"#;
    let cases = [
        (
            outer_rule,
            vec![1, 2],
            vec![0],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(1)] consume(1); } }"#,
        ),
        (
            outer_rule,
            vec![1, 2],
            vec![0],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(1)] consume(1); #[proctor(2)] consume(2); #[proctor(1)] consume(3); } }"#,
        ),
        (
            outer_rule,
            vec![1, 2],
            vec![0],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(2)] consume(2); #[proctor(1)] consume(1); } }"#,
        ),
        (
            outer_rule,
            vec![1, 2],
            vec![0],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(1)] consume(1); } #[proctor(2)] consume(2); }"#,
        ),
        (
            outer_rule,
            vec![1, 2],
            vec![0],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { if true { #[proctor(1)] consume(1); } #[proctor(2)] consume(2); } }"#,
        ),
        (
            inner_rule,
            vec![0, 2],
            vec![1],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(2)] consume(2); } }"#,
        ),
        (
            inner_rule,
            vec![0, 2],
            vec![1],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(1)] consume(1); #[proctor(1)] consume(3); #[proctor(2)] consume(2); } }"#,
        ),
        (
            inner_rule,
            vec![0, 2],
            vec![1],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(2)] consume(2); #[proctor(1)] consume(1); } }"#,
        ),
        (
            inner_rule,
            vec![0, 2],
            vec![1],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { #[proctor(2)] consume(2); } #[proctor(1)] consume(1); }"#,
        ),
        (
            inner_rule,
            vec![0, 2],
            vec![1],
            r#"unsafe fn f(flag: bool) { #[proctor(0)] if flag { if true { #[proctor(1)] consume(1); } #[proctor(2)] consume(2); } }"#,
        ),
    ];
    for (skeleton, transformed, applied, transformation) in cases {
        let request = ReplacementRequest {
            accepted_correspondence: vec![],
            schema_version: 1,
            items: vec![mixed_preservation_item(skeleton, &transformed, &applied)],
            transformation: transformation.to_owned(),
        };
        assert!(replace(source, &request).is_err(), "{transformation}");
    }
}

#[test]
fn replacement_rejects_extra_outer_groups_without_validator() {
    let source = "pub unsafe fn f(value: i32) -> i32 { value + 1 }";
    for transformation in [
        "unsafe fn f(value: i32) -> i32 { attacker(); #[proctor(0)] 999 }",
        "unsafe fn f(value: i32) -> i32 { #[proctor(99)] attacker(); #[proctor(0)] 999 }",
    ] {
        let request = ReplacementRequest {
            accepted_correspondence: vec![],
            schema_version: 1,
            items: vec![preservation_item(
                7,
                "f",
                "f",
                "unsafe fn f(value: i32) -> i32 { #[proctor(0)] value + 1 }",
                vec![],
            )],
            transformation: transformation.to_owned(),
        };
        let error = replace(source, &request).unwrap_err();
        assert_eq!(error.kind, ReplacementErrorKind::InvalidTransformation);
    }
}

#[test]
fn replacement_uses_immutable_skeleton_header() {
    let source = "pub unsafe fn f(value: i32) -> i32 { value + 1 }";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "f",
            "f",
            "unsafe fn f(value: i32) -> i32 { #[proctor(0)] value + 1 }",
            vec![],
        )],
        transformation: "unsafe fn f(value: String) -> usize { #[proctor(0)] value.len() }"
            .to_owned(),
    };
    let output = replace(source, &request).unwrap();
    let text = compact(&output);
    assert!(text.contains("unsafe fn f(value: i32) -> i32 { value + 1 }"));
    assert!(!text.contains("String"));
    compile(&output);
}

#[test]
fn fully_preserved_body_can_change_signature_and_create_wrapper() {
    let source = "pub unsafe fn f(pointer: *mut i32) -> bool { pointer.is_null() }";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "f",
            "f",
            "unsafe fn f(pointer: Option<&i32>) -> bool { #[proctor(0)] pointer.is_none() }",
            vec![],
        )],
        transformation: "unsafe fn f(pointer: Option<&i32>) -> bool { #[proctor(0)] false }"
            .to_owned(),
    };
    let output = replace(source, &request).unwrap();
    let text = compact(&output);
    assert!(text.contains("unsafe fn __proctor_wrapper_f"), "{text}");
    assert!(text.contains("pointer.is_none()"));
    compile(&output);
}

#[test]
fn metadata_failure_is_atomic() {
    let source = "pub unsafe fn f(value: i32) -> i32 { value + 1 }";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![ReplacementItem {
            id: 7,
            path: "f".to_owned(),
            name: "f".to_owned(),
            view: skeleton_view(
                "unsafe fn f(value: i32) -> i32 { #[proctor(0)] value + 1 }",
                vec![0],
                false,
            ),
        }],
        transformation: "unsafe fn f(value: i32) -> i32 { #[proctor(0)] 999 }".to_owned(),
    };
    let error = replace(source, &request).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::InvalidRequest);
    assert!(error.message.contains("inconsistent_preservation_metadata"));
    assert_eq!(source, "pub unsafe fn f(value: i32) -> i32 { value + 1 }");
}

#[test]
fn metadata_and_canonicalization_failures_are_atomic() {
    let source = r#"
pub unsafe fn f(flag: bool, pointer: *mut i32) {
    if flag {
        let nested: i32 = 1;
        *pointer = nested;
    } else {
        return;
    }
}
"#;
    let skeleton = "unsafe fn f(flag: bool, pointer: *mut i32) { #[proctor(0)] if flag { #[proctor(1)] let nested: i32 = 1; #[proctor(2)] (*pointer = nested); } else { #[proctor(3)] return; } }";
    let valid = "unsafe fn f(flag: bool, pointer: *mut i32) { #[proctor(0)] if flag { #[proctor(1)] let nested: i32 = 99; #[proctor(2)] (*pointer = 7); } else { #[proctor(3)] return; } }";
    let misplaced = "unsafe fn f(flag: bool, pointer: *mut i32) { #[proctor(0)] if flag { #[proctor(2)] (*pointer = 7); } else { #[proctor(1)] let nested: i32 = 99; #[proctor(3)] return; } }";
    for (labels, transformation, expected_code) in [
        (vec![0, 2, 99], valid, "invalid_disposition_tree"),
        (vec![2], valid, "open_preserved_parent"),
        (vec![0, 2], misplaced, "descendant_location_mismatch"),
    ] {
        let known_labels = labels
            .iter()
            .copied()
            .filter(|label| *label != 99)
            .collect();
        let mut item = preservation_item(7, "f", "f", skeleton, known_labels);
        if labels.contains(&99) {
            item.view.statement_dispositions.push(StatementDisposition {
                label: 99,
                disposition: StatementDispositionKind::Transform,
                children: vec![],
            });
            item.view
                .statement_pair_metadata
                .push(StatementPairMetadata {
                    label: 99,
                    before_statement: "test".to_owned(),
                    printf_template: None,
                    pointer_variables_complete: true,
                    pointer_variables: vec![],
                });
        }
        let request = ReplacementRequest {
            accepted_correspondence: vec![],
            schema_version: 1,
            items: vec![item],
            transformation: transformation.to_owned(),
        };
        let error = replace(source, &request).unwrap_err();
        assert!(error.message.contains(expected_code), "{}", error.message);
    }
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
            accepted_correspondence: vec![],
            schema_version: 2,
            items: vec![replacement_item(7, "f".to_owned(), "f".to_owned())],
            transformation: "unsafe fn f() {}".to_owned(),
        },
        ReplacementRequest {
            accepted_correspondence: vec![],
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
            accepted_correspondence: vec![],
            schema_version: 1,
            items: items
                .into_iter()
                .map(|(id, path, name)| replacement_item(id, path, name))
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
        replacement_item(7, "f".to_owned(), "f".to_owned()),
        replacement_item(8, "g".to_owned(), "g".to_owned()),
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
            accepted_correspondence: vec![],
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
        accepted_correspondence: vec![],
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
    let multi_request = request_with_items(
        vec![
            replacement_item(7, "first".to_owned(), "first".to_owned()),
            replacement_item(8, "second".to_owned(), "second".to_owned()),
        ],
        r#"
unsafe fn second(value: i32) -> i32 { #[proctor(0)] value + 2 }
unsafe fn first(value: i32) -> i32 { #[proctor(0)] value + 1 }
"#,
    );
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
    let collision_request = request_with_items(
        vec![
            replacement_item(7, "m::f".to_owned(), "f".to_owned()),
            replacement_item(8, "m::f_0".to_owned(), "f_0".to_owned()),
        ],
        r#"
unsafe fn f(value: &i32) -> i32 { #[proctor(0)] *value }
unsafe fn f_0(value: &i32) -> i32 { #[proctor(0)] *value }
"#,
    );
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
    let scc_request = request_with_items(
        vec![
            replacement_item(7, "even".to_owned(), "even".to_owned()),
            replacement_item(8, "odd".to_owned(), "odd".to_owned()),
        ],
        r#"
unsafe fn odd(value: &i32, n: i32) -> i32 {
    #[proctor(0)] if n == 0 { *value } else { even(value, n - 1) }
}
unsafe fn even(value: &i32, n: i32) -> i32 {
    #[proctor(0)] if n == 0 { *value } else { odd(value, n - 1) }
}"#,
    );
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
fn transformed_calls_cannot_restore_obsolete_wrapper_calls() {
    let source = r#"
pub unsafe fn callee(_pointer: *mut i32, value: i32) -> i32 {
    value + 1
}
pub unsafe fn caller(pointer: *mut i32, value: i32) -> i32 {
    callee(pointer, value)
}
"#;
    let callee_request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "callee",
            "callee",
            "unsafe fn callee(mut _pointer: &mut i32, mut value: i32) -> i32 { #[proctor(0)] value + 1 }",
            vec![],
        )],
        transformation:
            "unsafe fn callee(mut _pointer: &mut i32, mut value: i32) -> i32 { #[proctor(0)] 999 }"
                .to_owned(),
    };
    let after_callee = replace(source, &callee_request).unwrap();
    assert!(compact(&after_callee).contains("crate::__proctor_wrapper_callee(pointer, value)"));

    let caller_request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            8,
            "caller",
            "caller",
            "unsafe fn caller(mut pointer: &mut i32, mut value: i32) -> i32 { #[proctor(0)] todo!() }",
            vec![0],
        )],
        transformation: "unsafe fn caller(mut pointer: &mut i32, mut value: i32) -> i32 { #[proctor(0)] callee(pointer, value) }".to_owned(),
    };
    let output = replace(&after_callee, &caller_request).unwrap();
    let text = compact(&output);
    assert!(text.contains("unsafe fn caller(mut pointer: &mut i32, mut value: i32) -> i32"));
    assert!(text.contains("callee(pointer, value)"));
    assert!(!text.contains(
        "unsafe fn caller(mut pointer: &mut i32, mut value: i32) -> i32 { crate::__proctor_wrapper_callee"
    ));
    compile(&output);

    let scalar = r#"
pub unsafe fn scalar_callee(value: i32) -> i32 { value + 1 }
pub unsafe fn scalar_caller(value: i32) -> i32 { scalar_callee(value) }
"#;
    let unchanged = replace(
        scalar,
        &request(
            "scalar_caller",
            "scalar_caller",
            "unsafe fn scalar_caller(value: i32) -> i32 { #[proctor(0)] scalar_callee(value) }",
        ),
    )
    .unwrap();
    assert!(!unchanged.contains("__proctor_wrapper"));
    compile(&unchanged);
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
    let request = request_with_items(
        vec![
            replacement_item(7, "good".to_owned(), "good".to_owned()),
            replacement_item(8, "bad".to_owned(), "bad".to_owned()),
        ],
        r#"
unsafe fn good(value: &i32) -> i32 { #[proctor(0)] *value }
unsafe fn bad(value: Box<[i32]>) { #[proctor(0)] drop(value); }
"#,
    );
    let error = replace(source, &request).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::UnsupportedConversion);
    assert_eq!(error.item.unwrap().id, 8);
}

#[test]
fn replacement_output_has_exact_source_and_sorted_sidecar_shape() {
    let source = "pub unsafe fn first() {} pub unsafe fn second() {}";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![
            preservation_item(
                9,
                "second",
                "second",
                "unsafe fn second() { #[proctor(0)] todo!(); }",
                vec![0],
            ),
            preservation_item(
                2,
                "first",
                "first",
                "unsafe fn first() { #[proctor(0)] todo!(); }",
                vec![0],
            ),
        ],
        transformation: r#"
            unsafe fn second() { #[proctor(0)] return; }
            unsafe fn first() { #[proctor(0)] return; }
        "#
        .to_owned(),
    };
    let output = replace_output(source, &request).unwrap();
    assert_eq!(
        compact(&output.source),
        "pub unsafe fn first() { return; } pub unsafe fn second() { return; }"
    );
    assert_eq!(
        output.statement_pairs,
        [
            ReplacementStatementPair {
                item_id: 2,
                path: "first".to_owned(),
                label: 0,
                after_statement: "#[proctor(0)]\nreturn;".to_owned(),
            },
            ReplacementStatementPair {
                item_id: 9,
                path: "second".to_owned(),
                label: 0,
                after_statement: "#[proctor(0)]\nreturn;".to_owned(),
            },
        ]
    );

    let preserved = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            1,
            "first",
            "first",
            "unsafe fn first() { #[proctor(0)] () }",
            vec![],
        )],
        transformation: "unsafe fn first() { #[proctor(0)] return; }".to_owned(),
    };
    assert!(
        replace_output(source, &preserved)
            .unwrap()
            .statement_pairs
            .is_empty()
    );
}

#[test]
fn one_source_statement_reports_the_complete_canonical_expansion_group() {
    let source = "pub unsafe fn expansion(mut pointer: *mut i32) -> i32 { *pointer }";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "expansion",
            "expansion",
            "unsafe fn expansion(mut pointer: *mut i32) -> i32 { #[proctor(0)] todo!() }",
            vec![0],
        )],
        transformation: r#"unsafe fn expansion(mut pointer: *mut i32) -> i32 {
            #[proctor(0)] let proctor_temp_var_0 = *pointer;
            #[proctor(0)] proctor_temp_var_0
        }"#
        .to_owned(),
    };
    let output = replace_output(source, &request).unwrap();
    assert_eq!(output.statement_pairs.len(), 1);
    let after = &output.statement_pairs[0].after_statement;
    assert_eq!(
        after,
        "#[proctor(0)]\nlet proctor_temp_var_0 = *pointer;\n\n#[proctor(0)]\n\
         proctor_temp_var_0"
    );
    assert!(!output.source.contains("#[proctor("));
}

#[test]
fn canonical_after_restores_preserved_descendants_before_capture() {
    let source = "pub unsafe fn choose(mut pointer: *mut i32) -> i32 { if pointer.is_null() { 0 } else { *pointer } }";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "choose",
            "choose",
            r#"unsafe fn choose(mut pointer: *mut i32) -> i32 {
                #[proctor(0)] if pointer.is_null() {
                    #[proctor(1)] 0
                } else {
                    #[proctor(2)] todo!()
                }
            }"#,
            vec![0, 2],
        )],
        transformation: r#"unsafe fn choose(mut pointer: *mut i32) -> i32 {
            #[proctor(0)] if pointer.is_null() {
                #[proctor(1)] 99
            } else {
                #[proctor(2)] *pointer
            }
        }"#
        .to_owned(),
    };
    let output = replace_output(source, &request).unwrap();
    let parent = output
        .statement_pairs
        .iter()
        .find(|pair| pair.label == 0)
        .unwrap();
    assert!(parent.after_statement.contains("#[proctor(1)]"));
    assert!(parent.after_statement.contains('0'));
    assert!(!parent.after_statement.contains("99"));
}

#[test]
fn overlapping_parent_and_descendant_labels_each_get_one_entry() {
    let source = "pub unsafe fn choose(mut pointer: *mut i32) -> i32 { if pointer.is_null() { 0 } else { *pointer } }";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "choose",
            "choose",
            r#"unsafe fn choose(mut pointer: *mut i32) -> i32 {
                #[proctor(0)] if pointer.is_null() {
                    #[proctor(1)] 0
                } else {
                    #[proctor(2)] todo!()
                }
            }"#,
            vec![0, 2],
        )],
        transformation: r#"unsafe fn choose(mut pointer: *mut i32) -> i32 {
            #[proctor(0)] if pointer.is_null() {
                #[proctor(1)] 0
            } else {
                #[proctor(2)] *pointer
            }
        }"#
        .to_owned(),
    };
    let output = replace_output(source, &request).unwrap();
    assert_eq!(
        output
            .statement_pairs
            .iter()
            .map(|pair| pair.label)
            .collect::<Vec<_>>(),
        [0, 2]
    );
    assert!(
        output.statement_pairs[0]
            .after_statement
            .contains("#[proctor(2)]")
    );
    assert!(
        !output.statement_pairs[1]
            .after_statement
            .contains("#[proctor(0)]")
    );
}

#[test]
fn sidecar_excludes_preserved_labels_and_generated_variable_type_rows() {
    let source =
        "pub unsafe fn f(mut pointer: *mut i32) -> i32 { let value = 1; *pointer + value }";
    let request = ReplacementRequest {
        accepted_correspondence: vec![],
        schema_version: 1,
        items: vec![preservation_item(
            7,
            "f",
            "f",
            r#"unsafe fn f(mut pointer: *mut i32) -> i32 {
                #[proctor(0)] let value = 1;
                #[proctor(1)] todo!()
            }"#,
            vec![1],
        )],
        transformation: r#"unsafe fn f(mut pointer: *mut i32) -> i32 {
            #[proctor(0)] let value = 100;
            #[proctor(1)] let proctor_temp_var_0 = *pointer;
            #[proctor(1)] proctor_temp_var_0 + value
        }"#
        .to_owned(),
    };
    let output = replace_output(source, &request).unwrap();
    assert_eq!(output.statement_pairs.len(), 1);
    assert_eq!(output.statement_pairs[0].label, 1);
    assert!(
        output.statement_pairs[0]
            .after_statement
            .contains("proctor_temp_var_0")
    );
}

#[test]
fn replacement_library_failures_return_no_typed_output() {
    let cases = [
        (
            "malformed label",
            "pub unsafe fn f() {}",
            ReplacementRequest {
                accepted_correspondence: vec![],
                schema_version: 1,
                items: vec![preservation_item(
                    7,
                    "f",
                    "f",
                    "unsafe fn f() { #[proctor(0)] todo!(); }",
                    vec![0],
                )],
                transformation: "unsafe fn f() { #[proctor(0)] return; #[proctor(1)] return; }"
                    .to_owned(),
            },
            ReplacementErrorKind::InvalidTransformation,
        ),
        (
            "target resolution",
            "pub unsafe fn f() {}",
            ReplacementRequest {
                accepted_correspondence: vec![],
                schema_version: 1,
                items: vec![preservation_item(
                    7,
                    "missing",
                    "missing",
                    "unsafe fn missing() {}",
                    vec![],
                )],
                transformation: "unsafe fn missing() {}".to_owned(),
            },
            ReplacementErrorKind::TargetResolution,
        ),
        (
            "unsupported conversion",
            "pub unsafe fn f(pointer: *mut i32) {}",
            request(
                "f",
                "f",
                "unsafe fn f(pointer: Box<[i32]>) { drop(pointer); }",
            ),
            ReplacementErrorKind::UnsupportedConversion,
        ),
        (
            "call rewrite",
            r#"
                pub unsafe fn f(value: *const i32) -> i32 { *value }
                pub unsafe fn caller(value: *const i32) -> i32 { dbg!(f(value)) }
            "#,
            request("f", "f", "unsafe fn f(value: &i32) -> i32 { *value + 1 }"),
            ReplacementErrorKind::UnsupportedCallRewrite,
        ),
        (
            "source rewrite",
            r#"
                pub unsafe fn main_0(argc: i32, argv: *mut *mut i8) -> i32 {
                    let _ = argv;
                    argc
                }
            "#,
            request(
                "main_0",
                "main_0",
                r#"unsafe fn main_0(argc: i32, argv: &mut [&mut [i8]]) -> i32 {
                    let _ = argv;
                    argc
                }"#,
            ),
            ReplacementErrorKind::RewriteFailure,
        ),
    ];
    for (name, source, request, expected_kind) in cases {
        let error = replace_output(source, &request)
            .expect_err("a failed replacement cannot return partial typed output");
        assert_eq!(error.kind, expected_kind, "{name}");
    }
}
