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

fn add_source(source: &str, request: &ReplacementRequest) -> Result<String, ReplacementError> {
    let initial = make_initial_source(source)?;
    add(source, &initial, request).map(|output| output.replacement.source)
}

fn add_output(
    source: &str,
    request: &ReplacementRequest,
) -> Result<ReplacementOutput, ReplacementError> {
    let initial = make_initial_source(source)?;
    add(source, &initial, request).map(|output| output.replacement)
}

fn add(
    analysis: &str,
    partial: &str,
    request: &ReplacementRequest,
) -> Result<ExtendedReplacementOutput, ReplacementError> {
    run_compiler_on_str(analysis, |tcx| {
        add_functions_with_observations(analysis, partial, request, tcx)
    })
    .unwrap()
}

fn finalize(
    analysis: &str,
    partial: &str,
    api: &[&str],
) -> Result<FinalizedProject, ReplacementError> {
    run_compiler_on_str(analysis, |tcx| {
        finalize_additive_source(
            analysis,
            partial,
            "library",
            &api.iter()
                .map(|name| (*name).to_owned())
                .collect::<Vec<_>>(),
            tcx,
        )
    })
    .unwrap()
}

fn compile(source: &str) {
    run_compiler_on_str(source, |_| ()).unwrap();
}

fn compile_checked(source: &str) {
    run_compiler_on_str(source, utils::type_check).unwrap();
}

fn compact(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn count(source: &str, needle: &str) -> usize {
    source.match_indices(needle).count()
}

fn assert_function_at_path(source: &str, path: &str, expected: &str) {
    with_parse_session(|| {
        let krate = parse_crate(source, ReplacementErrorKind::RewriteFailure)?;
        let segments = path.split("::").collect::<Vec<_>>();
        let mut items = &krate.items[..];
        for module_name in &segments[..segments.len() - 1] {
            let modules = items
                .iter()
                .filter(|item| {
                    matches!(&item.kind, ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(..)) if ident.to_string() == *module_name)
                })
                .collect::<Vec<_>>();
            assert_eq!(modules.len(), 1, "expected one module at `{path}`");
            let ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(children, ..)) = &modules[0].kind
            else {
                unreachable!()
            };
            items = children;
        }
        let name = segments.last().unwrap();
        let functions = items
            .iter()
            .filter(|item| {
                matches!(&item.kind, ItemKind::Fn(function) if function.ident.to_string() == *name)
            })
            .collect::<Vec<_>>();
        assert_eq!(functions.len(), 1, "expected one function at `{path}`");
        let expected = utils::ast::parse_item(expected.to_owned());
        assert_eq!(
            compact(&pprust::item_to_string(functions[0])),
            compact(&pprust::item_to_string(&expected)),
            "function at `{path}` differs"
        );
        Ok(())
    })
    .unwrap();
}

fn assert_only_item_of_kind_in_module(source: &str, module_path: &str, expected: &str) {
    with_parse_session(|| {
        let krate = parse_crate(source, ReplacementErrorKind::RewriteFailure)?;
        let expected = utils::ast::parse_item(expected.to_owned());
        let mut items = &krate.items[..];
        for module_name in module_path.split("::").filter(|segment| !segment.is_empty()) {
            let modules = items
                .iter()
                .filter(|item| {
                    matches!(&item.kind, ItemKind::Mod(_, ident, rustc_ast::ModKind::Loaded(..)) if ident.to_string() == module_name)
                })
                .collect::<Vec<_>>();
            assert_eq!(modules.len(), 1, "expected one module at `{module_path}`");
            let ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(children, ..)) = &modules[0].kind
            else {
                unreachable!()
            };
            items = children;
        }
        let matching = items
            .iter()
            .filter(|item| std::mem::discriminant(&item.kind) == std::mem::discriminant(&expected.kind))
            .collect::<Vec<_>>();
        assert_eq!(matching.len(), 1, "expected one matching item in `{module_path}`");
        assert_eq!(
            compact(&pprust::item_to_string(matching[0])),
            compact(&pprust::item_to_string(&expected)),
            "item in `{module_path}` differs"
        );
        Ok(())
    })
    .unwrap();
}

#[test]
fn initial_projection_keeps_context_and_pending_functions() {
    let source = r#"#![allow(dead_code)]
use core::ffi::c_int;
const BASE: c_int = 3;
mod inner { use super::c_int; pub struct Cell { pub value: c_int } pub unsafe fn leaf() {} mod deep { pub fn main() {} } }
mod consumer { use crate::inner::leaf; }
pub fn main() {}
"#;
    let initial = make_initial_source(source).unwrap();
    let compact = compact(&initial);
    assert!(compact.contains("#![allow(dead_code)]"));
    assert!(compact.contains("use core::ffi::c_int"));
    assert!(compact.contains("const BASE: c_int = 3"));
    assert!(compact.contains("mod inner"));
    assert!(compact.contains("pub struct Cell"));
    assert!(compact.contains("mod deep"));
    assert!(compact.contains("pub fn leaf() {}"));
    assert_eq!(count(&initial, "fn leaf"), 1);
    assert!(!compact.contains("unsafe fn leaf"));
    assert!(compact.contains("use crate::inner::leaf"));
    assert!(!compact.contains("fn main"));
    assert_function_at_path(&initial, "inner::leaf", "pub fn leaf() {}");
    compile_checked(&initial);
}

#[test]
fn pending_function_resolves_cross_module_import() {
    let analysis =
        "mod defs { pub unsafe fn foo(p: i32) -> i32 { p } } mod imports { use crate::defs::foo; }";
    let initial = make_initial_source(analysis).unwrap();
    assert_function_at_path(&initial, "defs::foo", "pub fn foo() {}");
    assert!(compact(&initial).contains("mod defs { pub fn foo() {} }"));
    assert!(compact(&initial).contains("use crate::defs::foo"));
    compile_checked(&initial);
    let accepted = add(
        analysis,
        &initial,
        &request(
            "defs::foo",
            "foo",
            "unsafe fn foo(p: i32) -> i32 { #[proctor(0)] p }",
        ),
    )
    .unwrap();
    assert_eq!(count(&accepted.replacement.source, "fn foo"), 1);
    assert_function_at_path(
        &accepted.replacement.source,
        "defs::foo",
        "pub unsafe fn foo(p: i32) -> i32 { p }",
    );
    assert!(accepted.replacement.source.contains("use crate::defs::foo"));
    compile_checked(&accepted.replacement.source);
}

#[test]
fn pending_functions_resolve_grouped_imports_and_reexports() {
    let analysis = "mod defs { pub unsafe fn f(p: i32) -> i32 { p } pub unsafe fn g() {} } mod imported { use crate::defs::{f as renamed, g}; } mod api { pub use crate::defs::{f as public_f, g}; }";
    let initial = make_initial_source(analysis).unwrap();
    assert_function_at_path(&initial, "defs::f", "pub fn f() {}");
    assert_function_at_path(&initial, "defs::g", "pub fn g() {}");
    assert!(compact(&initial).contains("pub fn f() {} pub fn g() {}"));
    assert!(initial.contains("f as renamed"));
    assert!(initial.contains("f as public_f"));
    compile_checked(&initial);
    let first = add(
        analysis,
        &initial,
        &request(
            "defs::f",
            "f",
            "unsafe fn f(p: i32) -> i32 { #[proctor(0)] p }",
        ),
    )
    .unwrap();
    assert!(compact(&first.replacement.source).contains("pub fn g() {}"));
    assert_function_at_path(
        &first.replacement.source,
        "defs::f",
        "pub unsafe fn f(p: i32) -> i32 { p }",
    );
    assert_function_at_path(&first.replacement.source, "defs::g", "pub fn g() {}");
    compile_checked(&first.replacement.source);
    let mut next = request("defs::g", "g", "unsafe fn g() {}");
    next.items[0].id = 8;
    next.accepted_correspondence = first.new_correspondence;
    let second = add(analysis, &first.replacement.source, &next).unwrap();
    assert_eq!(count(&second.replacement.source, "fn f"), 1);
    assert_eq!(count(&second.replacement.source, "fn g"), 1);
    assert_function_at_path(
        &second.replacement.source,
        "defs::f",
        "pub unsafe fn f(p: i32) -> i32 { p }",
    );
    assert_function_at_path(
        &second.replacement.source,
        "defs::g",
        "pub unsafe fn g() {}",
    );
    assert!(second.replacement.source.contains("f as renamed"));
    assert!(second.replacement.source.contains("f as public_f"));
    for source in [
        &initial,
        &first.replacement.source,
        &second.replacement.source,
    ] {
        assert_only_item_of_kind_in_module(
            source,
            "imported",
            "use crate::defs::{f as renamed, g};",
        );
        assert_only_item_of_kind_in_module(
            source,
            "api",
            "pub use crate::defs::{f as public_f, g};",
        );
    }
    compile_checked(&second.replacement.source);
}

#[test]
fn pending_functions_keep_visibility_and_nested_paths() {
    let analysis = "mod a { pub unsafe fn chosen() {} } mod b { unsafe fn chosen() {} pub(crate) mod deep { pub(crate) unsafe fn nested() {} pub(super) unsafe fn restricted() {} } } mod consumer { use crate::a::*; use crate::b::*; use crate::b::deep::nested; }";
    let initial = make_initial_source(analysis).unwrap();
    assert_function_at_path(&initial, "a::chosen", "pub fn chosen() {}");
    assert_function_at_path(&initial, "b::chosen", "fn chosen() {}");
    assert_function_at_path(&initial, "b::deep::nested", "pub(crate) fn nested() {}");
    assert_function_at_path(
        &initial,
        "b::deep::restricted",
        "pub(super) fn restricted() {}",
    );
    let text = compact(&initial);
    assert!(text.contains("mod a { pub fn chosen() {} }"));
    assert!(text.contains("mod b { fn chosen() {} pub(crate) mod deep { pub(crate) fn nested() {} pub(super) fn restricted() {} } }"));
    assert!(text.contains("use crate::a::*"));
    assert!(text.contains("use crate::b::*"));
    assert!(text.contains("use crate::b::deep::nested"));
    compile_checked(&initial);
    let accepted = add(
        analysis,
        &initial,
        &request("b::chosen", "chosen", "unsafe fn chosen() {}"),
    )
    .unwrap();
    assert!(compact(&accepted.replacement.source).contains("mod a { pub fn chosen() {} }"));
    assert!(compact(&accepted.replacement.source).contains("mod b { unsafe fn chosen() {}"));
    assert_function_at_path(
        &accepted.replacement.source,
        "b::chosen",
        "unsafe fn chosen() {}",
    );
    assert_function_at_path(
        &accepted.replacement.source,
        "a::chosen",
        "pub fn chosen() {}",
    );
    assert_function_at_path(
        &accepted.replacement.source,
        "b::deep::nested",
        "pub(crate) fn nested() {}",
    );
    assert_function_at_path(
        &accepted.replacement.source,
        "b::deep::restricted",
        "pub(super) fn restricted() {}",
    );
    compile_checked(&accepted.replacement.source);
}

#[test]
fn pending_function_drops_metadata_but_keeps_foreign_declarations() {
    let analysis = "#[no_mangle] pub unsafe extern \"C\" fn exported(p: *const i32) -> i32 { *p } extern \"C\" { fn foreign(p: *const i8) -> i32; }";
    let initial = make_initial_source(analysis).unwrap();
    assert_function_at_path(&initial, "exported", "pub fn exported() {}");
    assert!(compact(&initial).contains("pub fn exported() {}"));
    assert!(!initial.contains("no_mangle"));
    assert!(!initial.contains("unsafe fn exported"));
    assert!(compact(&initial).contains("fn foreign(p: *const i8) -> i32;"));
    assert_only_item_of_kind_in_module(
        &initial,
        "",
        "extern \"C\" { fn foreign(p: *const i8) -> i32; }",
    );
    compile_checked(&initial);
    let accepted = add(
        analysis,
        &initial,
        &request(
            "exported",
            "exported",
            "unsafe fn exported(p: &i32) -> i32 { #[proctor(0)] *p }",
        ),
    )
    .unwrap();
    assert!(accepted.replacement.source.contains("#[no_mangle]"));
    assert!(
        accepted
            .replacement
            .source
            .contains("pub unsafe extern \"C\" fn exported(p: &i32)")
    );
    assert!(compact(&accepted.replacement.source).contains("fn foreign(p: *const i8) -> i32;"));
    assert_only_item_of_kind_in_module(
        &accepted.replacement.source,
        "",
        "extern \"C\" { fn foreign(p: *const i8) -> i32; }",
    );
    assert_function_at_path(
        &accepted.replacement.source,
        "exported",
        "#[no_mangle] pub unsafe extern \"C\" fn exported(p: &i32) -> i32 { *p }",
    );
    compile_checked(&accepted.replacement.source);
}

#[test]
fn pending_raw_identifier_keeps_import_and_original_spelling() {
    let analysis = "mod api { pub unsafe fn r#type(x: i32) -> i32 { x } } mod imported { use crate::api::r#type as chosen; }";
    let initial = make_initial_source(analysis).unwrap();
    assert_function_at_path(&initial, "api::r#type", "pub fn r#type() {}");
    assert!(compact(&initial).contains("pub fn r#type() {}"));
    assert!(initial.contains("use crate::api::r#type as chosen"));
    compile_checked(&initial);
    let accepted = add(
        analysis,
        &initial,
        &request(
            "api::r#type",
            "r#type",
            "unsafe fn r#type(x: i32) -> i32 { #[proctor(0)] x }",
        ),
    )
    .unwrap();
    assert_eq!(count(&accepted.replacement.source, "fn r#type"), 1);
    assert_function_at_path(
        &accepted.replacement.source,
        "api::r#type",
        "pub unsafe fn r#type(x: i32) -> i32 { x }",
    );
    assert!(
        accepted
            .replacement
            .source
            .contains("use crate::api::r#type as chosen")
    );
    compile_checked(&accepted.replacement.source);
}

#[test]
fn excluded_main_import_remains_unresolved() {
    let source = "pub fn main() {} mod inner { pub fn main() {} }";
    let initial = make_initial_source(source).unwrap();
    assert!(!initial.contains("fn main"));
    let finalized = finalize(source, &initial, &[]).unwrap();
    assert_eq!(count(&finalized.source, "fn main"), 2);
    assert_function_at_path(&finalized.source, "main", "pub fn main() {}");
    assert_function_at_path(&finalized.source, "inner::main", "pub fn main() {}");
    let unresolved =
        make_initial_source("pub fn main() {} mod consumer { use crate::main; }").unwrap();
    assert!(!unresolved.contains("fn main"));
    assert!(unresolved.contains("use crate::main"));
    assert!(run_compiler_on_str(&unresolved, utils::type_check).is_err());
}

#[test]
fn additive_internal_signature_change_has_no_wrapper_and_uses_old_call_stub() {
    let analysis = r#"mod inner {
    pub unsafe fn leaf(p: *mut i32) -> i32 { *p }
    pub unsafe fn caller(p: *mut i32) -> i32 { leaf(p) }
}"#;
    let initial = make_initial_source(analysis).unwrap();
    assert_function_at_path(&initial, "inner::leaf", "pub fn leaf() {}");
    assert_function_at_path(&initial, "inner::caller", "pub fn caller() {}");
    compile_checked(&initial);
    let first = add(
        analysis,
        &initial,
        &request(
            "inner::leaf",
            "leaf",
            "unsafe fn leaf(p: Box<[i32]>) -> i32 { #[proctor(0)] p[0] }",
        ),
    )
    .unwrap();
    assert!(first.replacement.source.contains("Box<[i32]>"));
    assert!(!first.replacement.source.contains("__proctor_wrapper"));
    assert!(compact(&first.replacement.source).contains("pub fn caller() {}"));
    assert_eq!(count(&first.replacement.source, "fn leaf"), 1);
    assert_function_at_path(
        &first.replacement.source,
        "inner::leaf",
        "pub unsafe fn leaf(p: Box<[i32]>) -> i32 { p[0] }",
    );
    assert_function_at_path(
        &first.replacement.source,
        "inner::caller",
        "pub fn caller() {}",
    );
    assert!(first.source_stubs.is_empty());
    compile_checked(&first.replacement.source);
    let mut second_request = request(
        "inner::caller",
        "caller",
        "unsafe fn caller(p: Box<[i32]>) -> i32 { #[proctor(0)] leaf(p) }",
    );
    second_request.items[0].id = 8;
    second_request.accepted_correspondence = first.new_correspondence.clone();
    let second = add(analysis, &first.replacement.source, &second_request).unwrap();
    assert_eq!(second.accepted_correspondence, first.new_correspondence);
    assert_eq!(second.new_correspondence[0].logical_path, "inner::caller");
    assert_eq!(
        second.new_correspondence[0].implementation_path,
        "inner::caller"
    );
    assert_eq!(
        second.source_stubs,
        vec![SourceStub {
            item_id: 7,
            path: "inner::__proctor_source_stub_leaf".to_owned()
        }]
    );
    assert!(
        second
            .observation_source
            .contains("pub(crate) unsafe fn __proctor_source_stub_leaf")
    );
    assert!(!second.replacement.source.contains("source_stub"));
    assert!(!second.replacement.source.contains("__proctor_wrapper"));
    assert_eq!(count(&second.replacement.source, "fn caller"), 1);
    assert!(compact(&second.replacement.source).contains("fn caller(p: Box<[i32]>)"));
    assert_function_at_path(
        &second.replacement.source,
        "inner::leaf",
        "pub unsafe fn leaf(p: Box<[i32]>) -> i32 { p[0] }",
    );
    assert_function_at_path(
        &second.replacement.source,
        "inner::caller",
        "pub unsafe fn caller(p: Box<[i32]>) -> i32 { leaf(p) }",
    );
    assert_function_at_path(
        &second.observation_source,
        "inner::caller",
        "pub unsafe fn caller(p: Box<[i32]>) -> i32 { #[proctor(0)] leaf(p) }",
    );
    assert_eq!(
        second.current_items[0].source_copy_path,
        "inner::__proctor_source_caller"
    );
    assert_function_at_path(
        &second.observation_source,
        "inner::__proctor_source_caller",
        "pub(crate) unsafe fn __proctor_source_caller(p: *mut i32) -> i32 { #[proctor(0)] crate::inner::__proctor_source_stub_leaf(p) }",
    );
    assert_function_at_path(
        &second.observation_source,
        "inner::__proctor_source_stub_leaf",
        "pub(crate) unsafe fn __proctor_source_stub_leaf(p: *mut i32) -> i32 { todo!() }",
    );
    compile_checked(&second.replacement.source);
    compile(&second.observation_source);
    let metadata = crate::ReplacementObservationMetadata::from_additive_output(
        &second,
        second.replacement.source.as_bytes(),
        b"pairs",
        second.observation_source.as_bytes(),
    );
    let parsed =
        crate::replacement_metadata_from_json(&serde_json::to_string(&metadata).unwrap()).unwrap();
    assert_eq!(parsed.source_stubs.unwrap(), second.source_stubs);
    let mut future = metadata.clone();
    future.schema_version = 3;
    assert_eq!(
        crate::replacement_metadata_from_json(&serde_json::to_string(&future).unwrap())
            .unwrap_err()
            .code,
        "unsupported_schema_version"
    );
    let duplicate_version = format!(
        "{{\"schema_version\":999,{}",
        &serde_json::to_string(&metadata).unwrap()[1..]
    );
    let duplicate_error = crate::replacement_metadata_from_json(&duplicate_version).unwrap_err();
    assert_eq!(duplicate_error.code, "malformed_metadata");
    assert!(duplicate_error.message.contains("duplicate field"));
    crate::observation::extract_observations_from_source(&second.observation_source, &metadata)
        .unwrap();
    let mut missing = metadata.clone();
    missing.source_stubs = Some(vec![]);
    assert_eq!(
        crate::observation::extract_observations_from_source(&second.observation_source, &missing)
            .unwrap_err()
            .code,
        "dangling_correspondence"
    );
    let mut wrong = metadata.clone();
    wrong.source_stubs.as_mut().unwrap()[0].path =
        "elsewhere::__proctor_source_stub_leaf".to_owned();
    assert_eq!(
        crate::replacement_metadata_from_json(&serde_json::to_string(&wrong).unwrap())
            .unwrap_err()
            .code,
        "malformed_metadata"
    );
    let mut unknown = metadata.clone();
    unknown.source_stubs.as_mut().unwrap()[0].item_id = 8;
    assert_eq!(
        crate::replacement_metadata_from_json(&serde_json::to_string(&unknown).unwrap())
            .unwrap_err()
            .code,
        "malformed_metadata"
    );
    let finalized = finalize(analysis, &second.replacement.source, &["leaf"]).unwrap();
    assert_eq!(count(&finalized.source, "fn leaf"), 1);
    assert!(compact(&finalized.source).contains("fn leaf(p: Box<[i32]>)"));
    assert!(!finalized.source.contains("__proctor_wrapper"));
    assert!(!finalized.source.contains("__proctor_source"));
    assert_function_at_path(
        &finalized.source,
        "inner::caller",
        "pub unsafe fn caller(p: Box<[i32]>) -> i32 { leaf(p) }",
    );
}

#[test]
fn finalization_keeps_changed_apis_at_original_paths() {
    let analysis = r#"#[no_mangle] pub unsafe extern "C" fn first(p: *const i32) -> i32 { *p }
unsafe fn middle(p: *const i32) -> i32 { *p }
#[export_name = "public_last"] pub unsafe extern "C" fn last(p: *const i32) -> i32 { *p }
pub fn main() {}"#;
    let initial = make_initial_source(analysis).unwrap();
    assert_function_at_path(&initial, "middle", "fn middle() {}");
    let mut partial = initial;
    for (id, name) in [(1, "first"), (2, "middle"), (3, "last")] {
        let transformation = if name == "last" {
            "unsafe fn last(p: &[i32]) -> i32 { #[proctor(0)] p[0] }".to_owned()
        } else {
            format!("unsafe fn {name}(p: &i32) -> i32 {{ #[proctor(0)] *p }}")
        };
        let mut item = request(name, name, &transformation);
        item.items[0].id = id;
        item.accepted_correspondence = (1..id)
            .map(|previous| {
                let path = ["first", "middle", "last"][(previous - 1) as usize].to_owned();
                CallableCorrespondence {
                    item_id: previous,
                    logical_path: path.clone(),
                    implementation_path: path,
                    wrapper_path: None,
                }
            })
            .collect();
        partial = add(analysis, &partial, &item).unwrap().replacement.source;
        compile(&partial);
    }
    let final_result = finalize(analysis, &partial, &["public_last", "first"]).unwrap();
    let source = compact(&final_result.source);
    assert!(source.contains("fn main"));
    assert!(source.contains("pub unsafe extern \"C\" fn first(p: &i32)"));
    assert!(source.contains("fn middle(p: &i32)"));
    assert_function_at_path(
        &final_result.source,
        "middle",
        "unsafe fn middle(p: &i32) -> i32 { *p }",
    );
    assert_function_at_path(
        &final_result.source,
        "first",
        "#[no_mangle] pub unsafe extern \"C\" fn first(p: &i32) -> i32 { *p }",
    );
    assert_function_at_path(
        &final_result.source,
        "last",
        "#[export_name = \"public_last\"] pub unsafe extern \"C\" fn last(p: &[i32]) -> i32 { p[0] }",
    );
    assert!(source.contains("pub unsafe extern \"C\" fn last(p: &[i32])"));
    assert!(source.contains("fn last(p: &[i32]) -> i32 { p[0] }"));
    assert_eq!(count(&final_result.source, "#[no_mangle]"), 1);
    assert_eq!(
        count(&final_result.source, "export_name = \"public_last\""),
        1
    );
    assert_eq!(count(&final_result.source, "extern \"C\""), 2);
    assert!(!source.contains("__proctor_wrapper"));
    assert!(!source.contains("from_raw_parts"));
    compile(&final_result.source);
}

#[test]
fn additive_cross_module_recursive_group_uses_visible_source_copies() {
    let analysis = r#"mod a { pub unsafe fn even(n: u32) -> bool { if n == 0 { true } else { crate::b::odd(n - 1) } } }
mod b { pub unsafe fn odd(n: u32) -> bool { if n == 0 { false } else { crate::a::even(n - 1) } } }"#;
    let initial = make_initial_source(analysis).unwrap();
    assert_function_at_path(&initial, "a::even", "pub fn even() {}");
    assert_function_at_path(&initial, "b::odd", "pub fn odd() {}");
    let request = request_with_items(
        vec![
            replacement_item(1, "a::even", "even"),
            replacement_item(2, "b::odd", "odd"),
        ],
        r#"unsafe fn even(n: u32) -> bool { #[proctor(0)] if n == 0 { true } else { crate::b::odd(n - 1) } }
unsafe fn odd(n: u32) -> bool { #[proctor(0)] if n == 0 { false } else { crate::a::even(n - 1) } }"#,
    );
    let output = add(analysis, &initial, &request).unwrap();
    assert_function_at_path(
        &output.replacement.source,
        "a::even",
        "pub unsafe fn even(n: u32) -> bool { if n == 0 { true } else { crate::b::odd(n - 1) } }",
    );
    assert_function_at_path(
        &output.replacement.source,
        "b::odd",
        "pub unsafe fn odd(n: u32) -> bool { if n == 0 { false } else { crate::a::even(n - 1) } }",
    );
    assert_function_at_path(
        &output.observation_source,
        "a::even",
        "pub unsafe fn even(n: u32) -> bool { #[proctor(0)] if n == 0 { #[proctor(1)] true } else { #[proctor(2)] crate::b::odd(n - 1) } }",
    );
    assert_function_at_path(
        &output.observation_source,
        "b::odd",
        "pub unsafe fn odd(n: u32) -> bool { #[proctor(0)] if n == 0 { #[proctor(1)] false } else { #[proctor(2)] crate::a::even(n - 1) } }",
    );
    assert_function_at_path(
        &output.observation_source,
        "a::__proctor_source_even",
        "pub(crate) unsafe fn __proctor_source_even(n: u32) -> bool { #[proctor(0)] if n == 0 { #[proctor(1)] true } else { #[proctor(2)] crate::b::__proctor_source_odd(n - 1) } }",
    );
    assert_function_at_path(
        &output.observation_source,
        "b::__proctor_source_odd",
        "pub(crate) unsafe fn __proctor_source_odd(n: u32) -> bool { #[proctor(0)] if n == 0 { #[proctor(1)] false } else { #[proctor(2)] crate::a::__proctor_source_even(n - 1) } }",
    );
    assert!(output.source_stubs.is_empty());
    assert!(
        output
            .observation_source
            .contains("pub(crate) unsafe fn __proctor_source_even")
    );
    assert!(
        output
            .observation_source
            .contains("pub(crate) unsafe fn __proctor_source_odd")
    );
    assert!(
        output
            .observation_source
            .contains("crate::b::__proctor_source_odd"),
        "{}",
        output.observation_source
    );
    assert!(
        output
            .observation_source
            .contains("crate::a::__proctor_source_even")
    );
    compile(&output.replacement.source);
    compile(&output.observation_source);
}

#[test]
fn additive_rejects_wrong_path_and_repeated_installation() {
    let analysis = "mod a { pub unsafe fn f() {} } mod b { pub unsafe fn f() {} }";
    let initial = make_initial_source(analysis).unwrap();
    let error = add(
        analysis,
        &initial,
        &request("c::f", "f", "unsafe fn f() {}"),
    )
    .unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::TargetResolution);
    let first = add(
        analysis,
        &initial,
        &request("a::f", "f", "unsafe fn f() {}"),
    )
    .unwrap();
    let mut repeated = request("a::f", "f", "unsafe fn f() {}");
    repeated.accepted_correspondence = first.new_correspondence.clone();
    let error = add(analysis, &first.replacement.source, &repeated).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::InvalidRequest);
    assert!(compact(&first.replacement.source).contains("mod b { pub fn f() {} }"));
}

#[test]
fn additive_macro_hidden_old_call_is_rejected() {
    let analysis = r#"pub unsafe fn leaf(p: *mut i32) -> i32 { *p }
macro_rules! old_call { ($p:expr) => { leaf($p) }; }
pub unsafe fn caller(p: *mut i32) -> i32 { old_call!(p) }"#;
    let initial = make_initial_source(analysis).unwrap();
    let first = add(
        analysis,
        &initial,
        &request(
            "leaf",
            "leaf",
            "unsafe fn leaf(p: &mut i32) -> i32 { #[proctor(0)] *p }",
        ),
    )
    .unwrap();
    let mut next = request(
        "caller",
        "caller",
        "unsafe fn caller(p: &mut i32) -> i32 { #[proctor(0)] *p }",
    );
    next.items[0].id = 8;
    next.accepted_correspondence = first.new_correspondence;
    let error = add(analysis, &first.replacement.source, &next).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::UnsupportedCallRewrite);
    assert!(error.message.contains("macro token input"));
}

#[test]
fn observation_accepts_real_functions_with_stub_like_names() {
    let analysis = r#"pub unsafe fn __proctor_source_stub_leaf(p: i32) -> i32 { p }
pub unsafe fn __proctor_source_stub_caller(p: i32) -> i32 { __proctor_source_stub_leaf(p) }"#;
    let initial = make_initial_source(analysis).unwrap();
    let first = add(
        analysis,
        &initial,
        &request(
            "__proctor_source_stub_leaf",
            "__proctor_source_stub_leaf",
            "unsafe fn __proctor_source_stub_leaf(p: i32) -> i32 { #[proctor(0)] p }",
        ),
    )
    .unwrap();
    let mut next = request(
        "__proctor_source_stub_caller",
        "__proctor_source_stub_caller",
        "unsafe fn __proctor_source_stub_caller(p: i32) -> i32 { #[proctor(0)] __proctor_source_stub_leaf(p) }",
    );
    next.items[0].id = 8;
    next.accepted_correspondence = first.new_correspondence;
    let second = add(analysis, &first.replacement.source, &next).unwrap();
    assert!(second.source_stubs.is_empty());
    let metadata = crate::ReplacementObservationMetadata::from_additive_output(
        &second,
        second.replacement.source.as_bytes(),
        b"pairs",
        second.observation_source.as_bytes(),
    );
    crate::observation::extract_observations_from_source(&second.observation_source, &metadata)
        .unwrap();
}

#[test]
fn stub_allocation_does_not_depend_on_correspondence_order() {
    let analysis = r#"pub unsafe fn first(p: *mut i32) -> i32 { *p }
pub unsafe fn second(p: *mut i32) -> i32 { *p }
pub unsafe fn caller(p: *mut i32, q: *mut i32) -> i32 { first(p) + second(q) }"#;
    let initial = make_initial_source(analysis).unwrap();
    let mut first_request = request(
        "first",
        "first",
        "unsafe fn first(p: &mut i32) -> i32 { #[proctor(0)] *p }",
    );
    first_request.items[0].id = 2;
    let first = add(analysis, &initial, &first_request).unwrap();
    let mut second_request = request(
        "second",
        "second",
        "unsafe fn second(p: &mut i32) -> i32 { #[proctor(0)] *p }",
    );
    second_request.items[0].id = 1;
    second_request.accepted_correspondence = first.new_correspondence.clone();
    let second = add(analysis, &first.replacement.source, &second_request).unwrap();
    let mut caller = request(
        "caller",
        "caller",
        "unsafe fn caller(p: &mut i32, q: &mut i32) -> i32 { #[proctor(0)] first(p) + second(q) }",
    );
    caller.items[0].id = 3;
    caller.accepted_correspondence = second_request.accepted_correspondence;
    caller
        .accepted_correspondence
        .extend(second.new_correspondence);
    let forward = add(analysis, &second.replacement.source, &caller).unwrap();
    caller.accepted_correspondence.reverse();
    let reverse = add(analysis, &second.replacement.source, &caller).unwrap();
    assert_eq!(forward.observation_source, reverse.observation_source);
    assert_eq!(forward.source_stubs, reverse.source_stubs);
    assert_eq!(
        forward
            .source_stubs
            .iter()
            .map(|stub| stub.item_id)
            .collect::<Vec<_>>(),
        [1, 2]
    );
}

#[test]
fn finalization_restores_original_main_and_fixed_two_argument_main() {
    let raw = "pub fn r#main() {}";
    let raw_initial = make_initial_source(raw).unwrap();
    assert!(!raw_initial.contains("fn r#main"));
    let raw_final = finalize(raw, &raw_initial, &[]).unwrap();
    assert!(raw_final.source.contains("fn main"));

    let zero = "pub unsafe fn main_0() -> i32 { 0 } pub fn main() { unsafe { std::process::exit(main_0()) } }";
    let zero_initial = make_initial_source(zero).unwrap();
    let zero_added = add(
        zero,
        &zero_initial,
        &request(
            "main_0",
            "main_0",
            "unsafe fn main_0() -> i32 { #[proctor(0)] 0 }",
        ),
    )
    .unwrap();
    let zero_final = finalize(zero, &zero_added.replacement.source, &[]).unwrap();
    assert!(compact(&zero_final.source).contains("std::process::exit(main_0())"));
    compile(&zero_final.source);

    let two = "pub unsafe fn main_0(argc: i32, argv: *mut *mut i8) -> i32 { 0 } pub fn main() {}";
    let two_initial = make_initial_source(two).unwrap();
    let two_added = add(
        two,
        &two_initial,
        &request(
            "main_0",
            "main_0",
            "unsafe fn main_0(argc: i32, argv: &mut [&mut [i8]]) -> i32 { #[proctor(0)] 0 }",
        ),
    )
    .unwrap();
    let two_final = finalize(two, &two_added.replacement.source, &[]).unwrap();
    assert!(
        two_final
            .source
            .contains("command_line_arg_slices.as_mut_slice()")
    );
    compile(&two_final.source);
}

#[test]
fn finalization_requires_sibling_main_only_for_two_argument_main_0() {
    let source = "pub unsafe fn main_0(argc: i32, argv: *mut *mut i8) -> i32 { 0 }";
    let transformed = request(
        "main_0",
        "main_0",
        "unsafe fn main_0(argc: i32, argv: &mut [&mut [i8]]) -> i32 { #[proctor(0)] 0 }",
    );
    let initial = make_initial_source(source).unwrap();
    let added = add(source, &initial, &transformed).unwrap();
    let error = finalize(source, &added.replacement.source, &[]).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::RewriteFailure);
    assert_eq!(
        error.message,
        "two-argument `main_0` requires exactly one sibling `main`, found 0"
    );

    let zero = "pub unsafe fn main_0() -> i32 { 0 }";
    let zero_initial = make_initial_source(zero).unwrap();
    let zero_added = add(
        zero,
        &zero_initial,
        &request(
            "main_0",
            "main_0",
            "unsafe fn main_0() -> i32 { #[proctor(0)] 0 }",
        ),
    )
    .unwrap();
    let zero_final = finalize(zero, &zero_added.replacement.source, &[]).unwrap();
    assert!(!zero_final.source.contains("fn main()"));
    compile(&zero_final.source);
}

#[test]
fn finalization_selects_all_same_named_functions_and_deduplicates_api_entries() {
    let analysis = r#"mod a { pub unsafe fn work(p: *const i32) -> i32 { *p } }
mod b { pub unsafe fn work(p: *const i32) -> i32 { *p } }"#;
    let initial = make_initial_source(analysis).unwrap();
    assert_function_at_path(&initial, "a::work", "pub fn work() {}");
    assert_function_at_path(&initial, "b::work", "pub fn work() {}");
    let first = add(
        analysis,
        &initial,
        &request(
            "a::work",
            "work",
            "unsafe fn work(p: &i32) -> i32 { #[proctor(0)] *p }",
        ),
    )
    .unwrap();
    let mut second_request = request(
        "b::work",
        "work",
        "unsafe fn work(p: &i32) -> i32 { #[proctor(0)] *p }",
    );
    second_request.items[0].id = 8;
    second_request.accepted_correspondence = first.new_correspondence;
    let second = add(analysis, &first.replacement.source, &second_request).unwrap();
    let final_result = finalize(analysis, &second.replacement.source, &["work", "work"]).unwrap();
    assert_function_at_path(
        &second.replacement.source,
        "a::work",
        "pub unsafe fn work(p: &i32) -> i32 { *p }",
    );
    assert_function_at_path(
        &second.replacement.source,
        "b::work",
        "pub unsafe fn work(p: &i32) -> i32 { *p }",
    );
    assert_function_at_path(
        &final_result.source,
        "a::work",
        "pub unsafe fn work(p: &i32) -> i32 { *p }",
    );
    assert_function_at_path(
        &final_result.source,
        "b::work",
        "pub unsafe fn work(p: &i32) -> i32 { *p }",
    );
    assert_eq!(count(&final_result.source, "fn work"), 2);
    assert_eq!(count(&final_result.source, "p: &i32"), 2);
    assert!(!final_result.source.contains("__proctor_wrapper"));
    compile(&final_result.source);
    let error = finalize(analysis, &second.replacement.source, &["missing"]).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::TargetResolution);
    assert!(error.message.contains("missing"));
}

#[test]
fn finalization_deduplicates_rust_and_export_names_for_one_function() {
    let analysis = r#"#[export_name = "public_work"] pub unsafe extern "C" fn work(p: *const i32) -> i32 { *p }"#;
    let initial = make_initial_source(analysis).unwrap();
    let added = add(
        analysis,
        &initial,
        &request(
            "work",
            "work",
            "unsafe fn work(p: &i32) -> i32 { #[proctor(0)] *p }",
        ),
    )
    .unwrap();
    let final_result = finalize(
        analysis,
        &added.replacement.source,
        &["work", "public_work", "work"],
    )
    .unwrap();
    assert_eq!(count(&final_result.source, "fn work"), 1);
    assert!(compact(&final_result.source).contains("fn work(p: &i32)"));
    assert!(compact(&final_result.source).contains("extern \"C\" fn work"));
    assert!(!final_result.source.contains("__proctor_wrapper"));
    assert_eq!(
        count(&final_result.source, "export_name = \"public_work\""),
        1
    );
    compile(&final_result.source);
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
        let error = add_source(source, &request).unwrap_err();
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
    assert!(add_source(source, &valid).is_ok());

    let local_temporary = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(7, "f", "f", skeleton, vec![0])],
        transformation: r#"unsafe fn f() { #[proctor(0)] ::std::print!("{}", { let proctor_temp_var_0 = 1; proctor_temp_var_0 }); }"#.to_owned(),
        accepted_correspondence: vec![],
    };
    assert!(add_source(source, &local_temporary).is_ok());

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
        let error = add_source(source, &request).unwrap_err();
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
    let error = add_source(source, &cross_argument).unwrap_err();
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
    assert!(add_source("unsafe fn f(proctor_temp_var_0: i32) {}", &existing).is_ok());
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
        let error = add_source(source, &request).unwrap_err();
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
        assert!(add_source(source, &request).is_ok(), "{statement}");
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
            add_source(source, &request).unwrap_err().kind,
            ReplacementErrorKind::InvalidTransformation
        );
    }
}

#[test]
fn expanded_printf_templates_restore_exact_literals() {
    let cases = [
        (
            "precision_zero",
            "value: i32",
            "{:.0}",
            "::proctor_libc::printf::signed(value)",
        ),
        (
            "lower_hex",
            "value: u32",
            "{:#08.4x}",
            "::proctor_libc::printf::unsigned(value)",
        ),
        (
            "lower_exp",
            "value: f64",
            "{:12.2e}",
            "::proctor_libc::printf::scientific(value)",
        ),
        (
            "upper_exp",
            "value: f64",
            "{:.6E}",
            "::proctor_libc::printf::scientific(value)",
        ),
        (
            "alternate_general",
            "value: f64",
            "{:#.6}",
            "::proctor_libc::printf::general(value)",
        ),
        (
            "lower_hex_float",
            "value: f64",
            "{:.3x}",
            "::proctor_libc::printf::hex_float(value)",
        ),
        (
            "upper_hex_float",
            "value: f64",
            "{:#.0X}",
            "::proctor_libc::printf::hex_float(value)",
        ),
        (
            "bounded_bytes",
            "value: &[i8]",
            "{:10.3}",
            "::proctor_libc::printf::byte_string(value)",
        ),
        (
            "literal_mix",
            "value: i32",
            "{{}} % {:.0}",
            "::proctor_libc::printf::signed(value)",
        ),
    ];
    for (name, parameter, format, argument) in cases {
        let source = format!("unsafe fn {name}({parameter}) {{}}");
        let skeleton = format!(
            r#"unsafe fn {name}({parameter}) {{ #[proctor(0)] ::std::print!("{format}", todo!()); }}"#
        );
        let transformation = format!(
            r#"unsafe fn {name}({parameter}) {{ #[proctor(0)] ::std::print!("{format}", {argument}); }}"#
        );
        let request = ReplacementRequest {
            schema_version: 1,
            items: vec![preservation_item(7, name, name, &skeleton, vec![0])],
            transformation,
            accepted_correspondence: vec![],
        };
        let output = add_source(&source, &request).unwrap();
        assert!(output.contains(&format!(r#"::std::print!("{format}", {argument})"#)));
        assert!(!output.contains("printf_template"));
        assert!(!output.contains("printf_format_specifiers"));
    }
}

#[test]
fn replacer_rechecks_expanded_printf_literal_without_validator() {
    let skeleton =
        r#"unsafe fn lower_hex(value: u32) { #[proctor(0)] ::std::print!("{:#08.4x}", todo!()); }"#;
    let request = ReplacementRequest {
        schema_version: 1,
        items: vec![preservation_item(7, "lower_hex", "lower_hex", skeleton, vec![0])],
        transformation: r#"unsafe fn lower_hex(value: u32) { #[proctor(0)] ::std::print!("{:#08.4X}", ::proctor_libc::printf::unsigned(value)); }"#.to_owned(),
        accepted_correspondence: vec![],
    };
    let error = add_source("unsafe fn lower_hex(value: u32) {}", &request).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::InvalidTransformation);
    assert_eq!(
        error.message,
        "printf_format_literal: print format literal differs from the expected converted format"
    );
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
    let error = add_source("unsafe fn f() {}", &request).unwrap_err();
    assert_eq!(error.kind, ReplacementErrorKind::InvalidRequest);
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
    let output = add_source(source, &request).unwrap();
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
    let output = add_source(source, &request).unwrap();
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
    let output = add_source(source, &request).unwrap();
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
    let output = add_source(source, &request).unwrap();
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
    let output = add_source(source, &request).unwrap();
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
        let output = add_source(source, &request).unwrap();
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

    let output = add_source(source, &request).unwrap();
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
        assert!(add_source(source, &request).is_err(), "{transformation}");
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
        let error = add_source(source, &request).unwrap_err();
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
    let output = add_source(source, &request).unwrap();
    let text = compact(&output);
    assert!(text.contains("unsafe fn f(value: i32) -> i32 { value + 1 }"));
    assert!(!text.contains("String"));
    compile(&output);
}

#[test]
fn fully_preserved_body_can_change_signature_directly() {
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
    let output = add_source(source, &request).unwrap();
    let text = compact(&output);
    assert!(
        text.contains("unsafe fn f(pointer: Option<&i32>)"),
        "{text}"
    );
    assert!(!text.contains("__proctor_wrapper"));
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
    let error = add_source(source, &request).unwrap_err();
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
        let error = add_source(source, &request).unwrap_err();
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
    let output = add_source(source, &request("f", "f", transformation)).unwrap();
    assert!(!output.contains("proctor"));
    assert!(compact(&output).contains("pub unsafe fn f(value: i32) -> i32"));
    assert!(!compact(&output).contains("unsafe fn untouched() -> i32 { 9 }"));
    assert!(!output.contains("__proctor_wrapper_f"));
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
            add_source("pub unsafe fn f() {}", &request)
                .unwrap_err()
                .kind,
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
        let first = add_source(source, &request).unwrap_err();
        let second = add_source(source, &request).unwrap_err();
        assert_eq!(first.kind, ReplacementErrorKind::InvalidRequest);
        assert_eq!(first, second);
    }
}

#[test]
fn path_name_disagreement_and_invalid_paths_are_rejected() {
    let source = "mod m { pub unsafe fn f() {} }";
    for (path, name) in [("m::f", "g"), ("", "f"), ("m::::f", "f")] {
        let error = add_source(source, &request(path, name, "unsafe fn f() {}")).unwrap_err();
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
            add_source(source, &request).unwrap_err().kind,
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
            add_source(source, &unexpected)
                .unwrap_err()
                .message
                .contains("unexpected function `z`")
        );
    }

    let error = add_source(
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
    let output = add_source(
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
fn redundant_nested_type_parentheses_keep_direct_function() {
    let source = r#"
pub unsafe fn f(value: Option<(*const i32)>) -> Option<(*const i32)> {
    value
}
"#;
    let output = add_source(
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
fn multiple_functions_add_in_request_order() {
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
    let output = add_source(source, &multi_request).unwrap();
    let text = compact(&output);
    assert!(text.find("value + 1").unwrap() < text.find("value + 2").unwrap());
}

#[test]
fn adds_validated_lifetime_generics_parameters_and_return() {
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
    let output = add_source(source, &request("choose", "choose", transformation)).unwrap();
    let text = compact(&output);
    assert!(text.contains("unsafe fn choose<'a, 'b>(first: &'a i32, second: &'b i32"));
    assert!(!text.contains("__proctor_wrapper"));
    assert!(text.contains("pub fn caller() {}"));
    compile(&output);
}

#[test]
fn source_target_resolution_and_normalized_safety_fail_atomically() {
    let missing = add_source(
        "pub unsafe fn f() {}",
        &request("missing", "missing", "unsafe fn missing() {}"),
    )
    .unwrap_err();
    assert_eq!(missing.kind, ReplacementErrorKind::TargetResolution);
    assert_eq!(missing.item.unwrap().id, 7);

    let safe = add_source("pub fn f() {}", &request("f", "f", "unsafe fn f() {}")).unwrap_err();
    assert_eq!(safe.kind, ReplacementErrorKind::TargetResolution);
}

#[test]
fn wildcard_and_destructuring_parameters_remain_unsupported_elsewhere() {
    for (source, path, name, transformation) in [
        (
            "unsafe fn f(value: i32) { let _ = value; }",
            "f",
            "f",
            "unsafe fn f(_: i32) { #[proctor(0)] return; }",
        ),
        (
            r#"unsafe fn main_0(first: (i32, i32), second: i32) { let _ = (first, second); }
pub fn main() { unsafe { main_0((0, 0), 0) } }"#,
            "main_0",
            "main_0",
            "unsafe fn main_0((_, _): (i32, i32), _: i32) { #[proctor(0)] return; }",
        ),
    ] {
        let error = add_source(source, &request(path, name, transformation)).unwrap_err();
        assert_eq!(error.kind, ReplacementErrorKind::InvalidTransformation);
        assert!(error.message.contains("simple by-value identifier"));
    }
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
    let output = add_output(source, &request).unwrap();
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
        add_output(source, &preserved)
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
    let output = add_output(source, &request).unwrap();
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
    let output = add_output(source, &request).unwrap();
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
    let output = add_output(source, &request).unwrap();
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
    let output = add_output(source, &request).unwrap();
    assert_eq!(output.statement_pairs.len(), 1);
    assert_eq!(output.statement_pairs[0].label, 1);
    assert!(
        output.statement_pairs[0]
            .after_statement
            .contains("proctor_temp_var_0")
    );
}
