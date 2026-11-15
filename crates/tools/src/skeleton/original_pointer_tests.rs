use super::*;

fn compile_bodies(records: &[ItemRecord], bodies: &[(&str, &str)]) {
    let definitions = records
        .iter()
        .filter_map(|record| match record {
            ItemRecord::Type(record) => Some(record.target_definition.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    let functions = bodies
        .iter()
        .map(|(name, body)| format!("{} {{ {body} }}", function(records, name).target_signature))
        .collect::<Vec<_>>()
        .join("\n");
    let source = format!("{definitions}\n{functions}");
    run_compiler_on_str(&source, utils::type_check).expect(&source);
}

#[test]
fn original_analysis_is_default_and_bo_is_explicit() {
    let source = "pub unsafe fn read(pointer: *const *const i32) -> i32 { **pointer }";
    let (default, original, bo) = run_compiler_on_str(source, |tcx| {
        (
            make_skeletons(source, tcx).unwrap(),
            make_skeletons_with_analysis(source, None, &FxHashSet::default(), false, tcx).unwrap(),
            make_skeletons_with_analysis(source, None, &FxHashSet::default(), true, tcx).unwrap(),
        )
    })
    .unwrap();
    assert_eq!(default, original);
    assert!(
        function(&default, "read")
            .target_signature
            .contains("*const i32")
    );
    assert!(
        !function(&bo, "read")
            .target_signature
            .contains("*const i32")
    );
    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        let frozen = crate::freeze_project(source, &records, tcx).unwrap();
        run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
    })
    .unwrap();
}

#[test]
fn original_slices_use_nullity_for_parameters_and_local_bindings() {
    let source = r#"
pub unsafe fn nullable(pointer: *const i32, absent: bool) -> i32 {
    let local = if absent { core::ptr::null() } else { pointer };
    if local.is_null() { 0 } else { *local.offset(1) }
}
pub unsafe fn nonnull(pointer: *const i32) -> i32 { let first = *pointer; first + *pointer.offset(1) }
pub unsafe fn local_nonnull() -> i32 {
    let values = [1, 2];
    let local = &raw const values[0];
    *local.offset(1)
}
pub unsafe fn mutable(pointer: *mut i32) {
    if !pointer.is_null() { *pointer.offset(1) = 7; }
}
"#;
    let records = generate(source);
    assert!(
        function(&records, "nullable")
            .target_signature
            .contains("Option<&[i32]>")
    );
    assert!(
        function(&records, "nullable")
            .baseline
            .skeleton
            .contains("local: Option<&[i32]>")
    );
    assert!(
        function(&records, "nonnull")
            .target_signature
            .contains("pointer: &[i32]"),
        "{}",
        function(&records, "nonnull").target_signature
    );
    assert!(
        function(&records, "local_nonnull")
            .baseline
            .skeleton
            .contains("local: &[i32]"),
        "{}",
        function(&records, "local_nonnull").baseline.skeleton
    );
    assert!(
        function(&records, "mutable")
            .target_signature
            .contains("Option<&mut [i32]>")
    );
    compile_bodies(
        &records,
        &[
            (
                "nullable",
                "if absent { 0 } else { pointer.map_or(0, |pointer| pointer[1]) }",
            ),
            ("nonnull", "pointer[0] + pointer[1]"),
            (
                "local_nonnull",
                "let values = [1, 2]; let local: &[i32] = &values; local[1]",
            ),
            (
                "mutable",
                "if let Some(pointer) = pointer { pointer[1] = 7; }",
            ),
        ],
    );
}

#[test]
fn original_fields_support_optional_slices_and_propagated_lifetimes() {
    let source = r#"
#[derive(Clone, Copy, Debug)] pub struct Holder { pub scalar: *const i32, pub data: *const i32 }
pub type Alias = Holder;
pub struct Container { pub holder: Alias }
pub unsafe fn make(scalar: *const i32, data: *const i32) -> Container {
    let _ = data.offset(1);
    Container { holder: Holder { scalar, data } }
}
pub unsafe fn read(holder: *const Holder) -> i32 {
    *(*holder).scalar + *(*holder).data.offset(1)
}
"#;
    let records = generate(source);
    let ItemRecord::Type(holder) = records
        .iter()
        .find(|record| record.path() == "Holder")
        .unwrap()
    else {
        panic!()
    };
    assert!(
        holder.target_definition.contains("scalar: Option<&'"),
        "{}",
        holder.target_definition
    );
    assert!(
        holder.target_definition.contains("[i32]>"),
        "{}",
        holder.target_definition
    );
    assert!(
        holder.target_definition.contains("data: Option<&'"),
        "{}",
        holder.target_definition
    );
    for name in ["Alias", "Container"] {
        let ItemRecord::Type(record) = records.iter().find(|record| record.path() == name).unwrap()
        else {
            panic!()
        };
        assert_ne!(record.source_definition, record.target_definition);
    }
    compile_bodies(
        &records,
        &[
            ("make", "Container { holder: Holder { scalar, data } }"),
            (
                "read",
                "holder.scalar.map_or(0, |pointer| *pointer) + holder.data.map_or(0, |pointer| pointer[1])",
            ),
        ],
    );
}

#[test]
fn original_owning_fields_use_optional_boxes_and_remove_incompatible_derives() {
    let source = r#"
extern "C" { fn malloc(size: usize) -> *mut i32; fn free(pointer: *mut i32); }
#[derive(Clone, Copy, Debug)] pub struct Holder { pub pointer: *mut i32 }
pub unsafe fn stash(holder: *mut Holder) {
    let pointer = malloc(core::mem::size_of::<i32>());
    *pointer = 7;
    (*holder).pointer = pointer;
}
"#;
    let records = generate(source);
    let ItemRecord::Type(holder) = records
        .iter()
        .find(|record| record.path() == "Holder")
        .unwrap()
    else {
        panic!()
    };
    assert!(
        holder.target_definition.contains("Option<Box<i32>>"),
        "{}",
        holder.target_definition
    );
    assert!(!holder.target_definition.contains("Copy"));
    assert!(holder.target_definition.contains("Debug"));
    compile_bodies(
        &records,
        &[("stash", "holder.pointer = Some(Box::new(0));")],
    );
}

#[test]
fn original_field_decisions_respect_api_and_foreign_type_boundaries() {
    let source = r#"
#[repr(C)] pub struct Exposed { pub scalar: *const i32, pub data: *const i32 }
#[repr(C)] pub struct Foreign { pub scalar: *const i32 }
extern "C" { fn external(value: *const Foreign); }
pub unsafe fn api(value: *const Exposed) -> i32 { *(*value).scalar + *(*value).data.offset(1) }
pub unsafe fn read_foreign(value: *const Foreign) -> i32 { external(value); *(*value).scalar }
"#;
    let records = run_compiler_on_str(source, |tcx| {
        make_skeletons_with_api(source, None, &FxHashSet::from_iter(["api".to_owned()]), tcx)
            .unwrap()
    })
    .unwrap();
    let ItemRecord::Type(exposed) = records
        .iter()
        .find(|record| record.path() == "Exposed")
        .unwrap()
    else {
        panic!()
    };
    assert!(
        exposed.target_definition.contains("scalar: Option<&'"),
        "{}",
        exposed.target_definition
    );
    assert!(
        exposed.target_definition.contains("data: *const i32"),
        "{}",
        exposed.target_definition
    );
    let ItemRecord::Type(foreign) = records
        .iter()
        .find(|record| record.path() == "Foreign")
        .unwrap()
    else {
        panic!()
    };
    assert_eq!(foreign.source_definition, foreign.target_definition);
}

#[test]
fn original_owning_array_fields_keep_api_exposed_layouts_fixed() {
    let source = r#"
extern "C" { fn malloc(size: usize) -> *mut i32; }
#[repr(C)] pub struct Buffer { pub pointer: *mut i32 }
pub unsafe fn allocate(buffer: *mut Buffer) {
    (*buffer).pointer = malloc(2 * core::mem::size_of::<i32>());
    *(*buffer).pointer.offset(1) = 7;
}
"#;
    for exposed in [false, true] {
        let records = run_compiler_on_str(source, |tcx| {
            let api = if exposed {
                FxHashSet::from_iter(["allocate".to_owned()])
            } else {
                FxHashSet::default()
            };
            let records = make_skeletons_with_api(source, None, &api, tcx).unwrap();
            let frozen = crate::freeze_project(source, &records, tcx).unwrap();
            run_compiler_on_str(&frozen.target_source, utils::type_check)
                .expect(&frozen.target_source);
            records
        })
        .unwrap();
        let definition = &type_record(&records, "Buffer").target_definition;
        let expected = if exposed {
            "pointer: *mut i32"
        } else {
            "pointer: Option<Box<[i32]>>"
        };
        assert!(definition.contains(expected), "{definition}");
        if !exposed {
            compile_bodies(
                &records,
                &[(
                    "allocate",
                    "buffer.pointer = Some(vec![0, 7].into_boxed_slice());",
                )],
            );
        }
    }
}

#[test]
fn original_mutable_fields_propagate_derive_changes_and_keep_inner_pointers_raw() {
    let source = r#"
#[derive(Clone, Copy, Debug)] pub struct Holder { pub pointer: *mut i32, pub nested: *const *const i32 }
#[derive(Clone, Copy, Debug)] pub struct Container { pub holder: Holder }
pub unsafe fn write(holder: *mut Holder) { *(*holder).pointer = 7; }
pub unsafe fn read(holder: *const Holder) -> i32 { **(*holder).nested }
"#;
    let records = generate(source);
    for name in ["Holder", "Container"] {
        let definition = &type_record(&records, name).target_definition;
        assert!(!definition.contains("Copy"), "{definition}");
        assert!(!definition.contains("Clone"), "{definition}");
        assert!(definition.contains("Debug"), "{definition}");
    }
    let definition = &type_record(&records, "Holder").target_definition;
    assert!(definition.contains("mut i32>"), "{definition}");
    assert!(definition.contains("*const i32>"), "{definition}");
    compile_bodies(
        &records,
        &[
            (
                "write",
                "if let Some(pointer) = holder.pointer.as_deref_mut() { *pointer = 7; }",
            ),
            ("read", "holder.nested.map_or(0, |pointer| **pointer)"),
        ],
    );
}
