use utils::compilation::run_compiler_on_str;

use super::*;

fn freeze(source: &str) -> FrozenProject {
    run_compiler_on_str(source, |tcx| {
        let records = crate::make_skeletons(source, tcx).unwrap();
        freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap()
}

fn fixture(initializer: &str) -> FrozenProject {
    freeze(&format!(
        r#"
pub struct Holder {{ pub pointer: *const i32 }}
static VALUE: i32 = 7;
static mut GLOBAL: Holder = {initializer};
pub unsafe fn read(holder: *const Holder) -> i32 {{ *(*holder).pointer }}
"#
    ))
}

fn transform(frozen: &FrozenProject, transformation: &str) -> InitializerTransformationResponse {
    transform_frozen_initializer(
        frozen,
        &InitializerTransformationRequest {
            item_id: frozen.initializers[0].record.id,
            transformation: transformation.into(),
        },
    )
    .unwrap()
}

fn install(frozen: &FrozenProject, transformations: &[&str]) -> FrozenProject {
    install_frozen_initializers(
        frozen,
        &InitializerInstallationRequest {
            items: vec![InitializerHistory {
                item_id: frozen.initializers[0].record.id,
                transformations: transformations
                    .iter()
                    .map(|source| (*source).into())
                    .collect(),
            }],
        },
    )
    .unwrap()
}

#[test]
fn selects_changed_struct_initializers_and_keeps_unaffected_pointer_globals() {
    let source = r#"
pub struct Holder { pub pointer: *const i32 }
static VALUE: i32 = 7;
static mut GLOBAL: Holder = Holder { pointer: &VALUE };
static mut RAW: *const i32 = &VALUE;
static COUNT: i32 = 3;
pub unsafe fn read(holder: *const Holder) -> i32 { *(*holder).pointer }
"#;
    let frozen = freeze(source);
    assert_eq!(
        frozen
            .initializers
            .iter()
            .map(|initializer| initializer.record.path.as_str())
            .collect::<Vec<_>>(),
        ["GLOBAL"]
    );
    assert!(
        frozen.initializers[0]
            .record
            .initializer
            .as_ref()
            .unwrap()
            .needs_transformation
    );
    assert!(frozen.target_source.contains("RAW: *const i32"));
}

#[test]
fn selects_scalar_initializers_using_changed_fields_and_transitive_constants() {
    let source = r#"
pub struct Holder { pub pointer: *const i32 }
const TEST: bool = Holder { pointer: core::ptr::null() }.pointer.is_null();
const AGAIN: bool = TEST;
pub unsafe fn read(holder: *const Holder) -> i32 { *(*holder).pointer }
"#;
    let frozen = freeze(source);
    assert_eq!(
        frozen
            .initializers
            .iter()
            .map(|initializer| initializer.record.path.as_str())
            .collect::<Vec<_>>(),
        ["TEST", "AGAIN"]
    );
}

#[test]
fn array_initializers_remain_wholly_unlabeled_and_follow_aliases() {
    let source = r#"
pub struct Holder { pub pointer: *const i32 }
pub struct Container { pub item: Holder }
type Alias = [Container; 1];
static VALUE: i32 = 7;
static mut GLOBAL: Alias = [Container { item: { let h = Holder { pointer: &VALUE }; h } }];
pub unsafe fn read(holder: *const Holder) -> i32 { *(*holder).pointer }
"#;
    let frozen = freeze(source);
    let record = frozen.initializers[0].record.initializer.as_ref().unwrap();
    assert!(!record.block);
    assert!(!record.annotated_source.contains("#[proctor("));
    assert!(record.statement_dispositions.is_empty());
    assert!(record.skeleton.contains("= todo!()"));
}

#[test]
fn array_of_struct_slice_initializers_compiles_after_whole_expression_rewrite() {
    let frozen = freeze(
        r#"
pub struct Holder { pub pointer: *const i32 }
static VALUES: [i32; 2] = [7, 8];
static mut GLOBAL: [Holder; 1] = [Holder { pointer: VALUES.as_ptr() }];
pub unsafe fn read(holder: *const Holder) -> i32 { *(*holder).pointer.offset(1) }
"#,
    );
    assert!(frozen.types[0].target_definition.contains("[i32]"));
    let result = transform(
        &frozen,
        "static mut GLOBAL: [Holder; 1] = [Holder { pointer: &VALUES }];",
    );
    let InitializerTransformationResponse::Valid { source } = result else { panic!("{result:?}") };
    let installed = install(&frozen, &[&source]);
    assert!(installed.target_source.contains("GLOBAL: [Holder; 1]"));
    run_compiler_on_str(&installed.target_source, utils::type_check).unwrap();
}

#[test]
fn block_skeleton_preserves_scalar_statements_and_raw_local_pointer_types() {
    let frozen =
        fixture("{ let number: i32 = 7; let pointer: *const i32 = &VALUE; Holder { pointer } }");
    let record = frozen.initializers[0].record.initializer.as_ref().unwrap();
    assert!(record.block);
    assert!(record.annotated_source.contains("#[proctor(0)]"));
    assert!(record.skeleton.contains("number: i32 = 7"));
    assert!(
        record.skeleton.contains("pointer: *const i32 = todo!()"),
        "{}",
        record.skeleton
    );
    assert_eq!(
        record.statement_dispositions[0].disposition,
        crate::StatementDispositionKind::Preserve
    );
}

#[test]
fn inferred_struct_locals_gain_required_type_lifetimes_without_promoting_raw_locals() {
    let frozen = fixture("{ let mut init = Holder { pointer: &VALUE }; init }");
    let record = frozen.initializers[0].record.initializer.as_ref().unwrap();
    assert!(
        record.skeleton.contains("let mut init: Holder"),
        "{}",
        record.skeleton
    );
    let source = record
        .skeleton
        .replacen("todo!()", "Holder { pointer: &VALUE }", 1)
        .replacen("todo!()", "init", 1);
    let result = transform(&frozen, &source);
    let InitializerTransformationResponse::Valid { source } = result else { panic!("{result:?}") };
    let installed = install(&frozen, &[&source]);
    run_compiler_on_str(&installed.target_source, utils::type_check).unwrap();
}

#[test]
fn root_unsafe_initializer_keeps_its_boundary_through_generation_and_installation() {
    let frozen = fixture("unsafe { Holder { pointer: &*(&VALUE as *const i32) } }");
    let record = frozen.initializers[0].record.initializer.as_ref().unwrap();
    assert!(record.block);
    assert!(
        record.annotated_source.contains("unsafe {"),
        "{}",
        record.annotated_source
    );
    let source = "static mut GLOBAL: Holder = unsafe { #[proctor(0)] Holder { pointer: &*(&VALUE as *const i32) } };";
    let result = transform(&frozen, source);
    let InitializerTransformationResponse::Valid { source } = result else { panic!("{result:?}") };
    let installed = install(&frozen, &[&source]);
    assert!(installed.initializers[0].target_item.contains("unsafe {"));
    run_compiler_on_str(&installed.target_source, utils::type_check).unwrap();
}

#[test]
fn nested_unsafe_blocks_keep_function_style_nested_labels() {
    let frozen = fixture(
        "{ let pointer: *const i32 = unsafe { &*(&VALUE as *const i32) }; Holder { pointer } }",
    );
    let record = frozen.initializers[0].record.initializer.as_ref().unwrap();
    assert!(
        record.annotated_source.contains("#[proctor(2)]"),
        "{}",
        record.annotated_source
    );
    let source = "static mut GLOBAL: Holder = { #[proctor(0)] let pointer: *const i32 = unsafe { #[proctor(1)] &*(&VALUE as *const i32) }; #[proctor(2)] Holder { pointer: unsafe { &*pointer } } };";
    let result = transform(&frozen, source);
    let InitializerTransformationResponse::Valid { source } = result else { panic!("{result:?}") };
    let installed = install(&frozen, &[&source]);
    run_compiler_on_str(&installed.target_source, utils::type_check).unwrap();
}

#[test]
fn transforms_nonblock_initializer_without_changing_its_declaration() {
    let frozen = fixture("Holder { pointer: &VALUE }");
    let result = transform(
        &frozen,
        "static mut GLOBAL: Holder = Holder { pointer: &VALUE };",
    );
    let InitializerTransformationResponse::Valid { source } = result else { panic!("{result:?}") };
    assert!(source.contains("static mut GLOBAL: Holder"));
    let installed = install(&frozen, &[&source]);
    run_compiler_on_str(&installed.target_source, utils::type_check).unwrap();
    frozen_project_from_json(&serde_json::to_string(&installed).unwrap()).unwrap();
}

#[test]
fn strict_transformation_rejects_changed_global_headers_labels_and_extra_items() {
    let frozen = fixture("Holder { pointer: &VALUE }");
    for source in [
        "const GLOBAL: Holder = Holder { pointer: &VALUE };",
        "static mut GLOBAL: i32 = 0;",
        "#[allow(dead_code)] static mut GLOBAL: Holder = Holder { pointer: &VALUE };",
        "static mut OTHER: Holder = Holder { pointer: &VALUE };",
        "static mut GLOBAL: Holder = { #[proctor(0)] Holder { pointer: &VALUE } };",
        "static mut GLOBAL: Holder = Holder { pointer: &VALUE }; fn extra() {}",
        "static mut GLOBAL: Holder = todo!();",
        "static mut GLOBAL: Holder = { const EXTRA: i32 = 7; Holder { pointer: &VALUE } };",
    ] {
        assert!(
            matches!(
                transform(&frozen, source),
                InitializerTransformationResponse::Invalid { .. }
            ),
            "{source}"
        );
    }
}

#[test]
fn block_validation_reuses_labels_and_permits_required_unsafe_blocks() {
    let frozen = fixture("{ let number: i32 = 7; Holder { pointer: &VALUE } }");
    let source = "static mut GLOBAL: Holder = { #[proctor(0)] let number: i32 = 99; #[proctor(1)] Holder { pointer: unsafe { &*(&VALUE as *const i32) } } };";
    let result = transform(&frozen, source);
    let InitializerTransformationResponse::Valid { source } = result else { panic!("{result:?}") };
    assert!(source.contains("number: i32 = 7"));
    assert!(source.contains("unsafe"));
    let installed = install(&frozen, &[&source]);
    assert!(!installed.target_source.contains("#[proctor("));
    run_compiler_on_str(&installed.target_source, utils::type_check).unwrap();
}

#[test]
fn block_validation_rejects_missing_labels_and_altered_local_types() {
    let frozen = fixture("{ let number: i32 = 7; Holder { pointer: &VALUE } }");
    for source in [
        "static mut GLOBAL: Holder = { let number: i32 = 7; Holder { pointer: &VALUE } };",
        "static mut GLOBAL: Holder = { #[proctor(0)] let number: i32 = 7; #[proctor(1)] todo!() };",
        "static mut GLOBAL: Holder = Holder { pointer: &VALUE };",
    ] {
        assert!(
            matches!(
                transform(&frozen, source),
                InitializerTransformationResponse::Invalid { .. }
            ),
            "{source}"
        );
    }
}

#[test]
fn retention_uses_latest_parseable_initializer_and_preserves_original_header() {
    let frozen = fixture("Holder { pointer: &VALUE }");
    let original_header = "static mut GLOBAL: Holder";
    let installed = install(
        &frozen,
        &[
            "static mut GLOBAL: Holder = Holder { pointer: &VALUE };",
            "#[no_mangle] const GLOBAL: usize = { #[proctor(0)] Holder { pointer: core::ptr::null() } };",
            "static mut GLOBAL: Holder = Holder { pointer: ; };",
        ],
    );
    assert!(installed.target_source.contains(original_header));
    assert!(
        installed
            .target_source
            .contains("pointer: core::ptr::null()")
    );
    assert!(!installed.target_source.contains("#[no_mangle]"));
    assert!(!installed.target_source.contains("#[proctor("));
    frozen_project_from_json(&serde_json::to_string(&installed).unwrap()).unwrap();
}

#[test]
fn retention_falls_back_to_original_and_skips_whole_todo_stubs() {
    let frozen = fixture("Holder { pointer: &VALUE }");
    for sources in [
        vec![],
        vec!["static mut GLOBAL: Holder = (core::todo!());"],
        vec!["static mut GLOBAL: Holder = { todo!() };"],
        vec!["static mut GLOBAL: Holder = Holder { pointer: ; };"],
    ] {
        let installed = install(&frozen, &sources);
        assert_eq!(installed.target_source, frozen.target_source);
        assert_eq!(
            installed.initializers[0].target_item,
            frozen.initializers[0].original_item
        );
    }
}

#[test]
fn installation_requires_exact_selected_coverage_and_frozen_context_stays_immutable() {
    let frozen = fixture("Holder { pointer: &VALUE }");
    for items in [
        vec![],
        vec![InitializerHistory {
            item_id: u64::MAX,
            transformations: vec![],
        }],
        vec![
            InitializerHistory {
                item_id: frozen.initializers[0].record.id,
                transformations: vec![],
            },
            InitializerHistory {
                item_id: frozen.initializers[0].record.id,
                transformations: vec![],
            },
        ],
    ] {
        assert!(
            install_frozen_initializers(&frozen, &InitializerInstallationRequest { items })
                .is_err()
        );
    }
    let installed = install(
        &frozen,
        &["static mut GLOBAL: Holder = Holder { pointer: &VALUE };"],
    );
    let mut changed = installed.clone();
    changed.target_source = changed
        .target_source
        .replace("static VALUE: i32 = 7", "static VALUE: i32 = 8");
    assert!(frozen_project_from_json(&serde_json::to_string(&changed).unwrap()).is_err());
    let mut changed = installed.clone();
    changed.initializers[0].target_item =
        "const GLOBAL: Holder = Holder { pointer: &VALUE };".into();
    assert!(frozen_project_from_json(&serde_json::to_string(&changed).unwrap()).is_err());
}
