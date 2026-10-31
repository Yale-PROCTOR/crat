use utils::compilation::run_compiler_on_str;

use super::*;

fn freeze(source: &str) -> FrozenProject {
    run_compiler_on_str(source, |tcx| {
        let records = crate::make_skeletons(source, tcx).unwrap();
        freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap()
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
        ["analysis_source", "functions", "target_source"]
    );
    for field in ["analysis_source", "functions", "target_source"] {
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
            members: vec![2],
            source: second.replacement.source,
        },
        AcceptedScc {
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
fn unfilled_stub_metadata_identifies_only_exact_current_whole_function_stubs() {
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
    let signature = frozen.functions[0]
        .record
        .target_signature
        .replace(": i32", ": (i32)");
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
            members: vec![frozen.functions[0].record.id],
            source: replacement.source,
        }],
    )
    .unwrap();
    assert!(assembled.contains("new_name"));
    run_compiler_on_str(&assembled, |_| ()).unwrap();
}

#[test]
fn unstructured_rejects_wrong_signatures_labels_unsafe_items_and_whole_function_stubs() {
    let frozen = freeze("pub unsafe fn target(x: i32) -> i32 { x + 1 }");
    for transformation in [
        "unsafe fn target(mut x: i64) -> i32 { 0 }",
        "unsafe fn target(mut x: i32) -> i64 { 0 }",
        "unsafe fn target<'a>(mut x: i32) -> i32 { 0 }",
        "unsafe fn target(mut y: i32) -> i32 { 0 }",
        "fn target(mut x: i32) -> i32 { 0 }",
        "const unsafe fn target(mut x: i32) -> i32 { 0 }",
        "unsafe fn target(mut x: i32) -> i32 { #[proctor(0)] x }",
        "unsafe fn target(mut x: i32) -> i32 { #[allow(unused)] let z = x; z }",
        "unsafe fn target(mut x: i32) -> i32 { unsafe { x } }",
        "unsafe fn target(mut x: i32) -> i32 { (|| unsafe { x })() }",
        "unsafe fn target(mut x: i32) -> i32 { fn extra() {} x }",
        "unsafe fn target(mut x: i32) -> i32 { (|| { use std::mem; x })() }",
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
            members,
            source: replacement.source,
        }],
    )
    .unwrap();
    run_compiler_on_str(&assembled, |_| ()).unwrap();
}
