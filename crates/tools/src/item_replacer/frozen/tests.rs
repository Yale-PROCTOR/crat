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
fn frozen_finalization_restores_main_and_validates_original_api_exports() {
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
    finalize_frozen_project(&frozen, &assembled, "library", &["public_entry".to_owned()]).unwrap();
    assert!(
        finalize_frozen_project(&frozen, &assembled, "library", &["missing".to_owned()]).is_err()
    );
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
