use rustc_ast::visit::Visitor as _;
use utils::compilation::run_compiler_on_str;

use super::*;

fn generate(source: &str) -> Vec<ItemRecord> {
    run_compiler_on_str(source, |tcx| make_skeletons(source, tcx).unwrap()).unwrap()
}

fn local_def(name: &str, tcx: TyCtxt<'_>) -> LocalDefId {
    tcx.hir_free_items()
        .find_map(|item_id| {
            let item = tcx.hir_item(item_id);
            item.kind
                .ident()
                .is_some_and(|ident| ident.name.as_str() == name)
                .then_some(item_id.owner_id.def_id)
        })
        .unwrap()
}

fn function<'a>(records: &'a [ItemRecord], path: &str) -> &'a FunctionRecord {
    records
        .iter()
        .find_map(|record| match record {
            ItemRecord::Function(function) if function.path == path => Some(function),
            _ => None,
        })
        .unwrap()
}

fn record<'a>(records: &'a [ItemRecord], path: &str) -> &'a ItemRecord {
    records.iter().find(|record| record.path() == path).unwrap()
}

fn value<'a>(records: &'a [ItemRecord], path: &str) -> &'a ValueRecord {
    match record(records, path) {
        ItemRecord::Value(value) => value,
        _ => panic!("{path} is not a value record"),
    }
}

fn type_record<'a>(records: &'a [ItemRecord], path: &str) -> &'a TypeRecord {
    match record(records, path) {
        ItemRecord::Type(value) => value,
        _ => panic!("{path} is not a type record"),
    }
}

fn generate_error(source: &str) -> GenerationError {
    run_compiler_on_str(source, |tcx| make_skeletons(source, tcx).unwrap_err()).unwrap()
}

fn compact(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn assert_skeleton(source: &str, path: &str, expected: &str) {
    struct ParenNormalizer;

    impl MutVisitor for ParenNormalizer {
        fn visit_expr(&mut self, expression: &mut Expr) {
            while let ExprKind::Paren(inner) = &expression.kind {
                *expression = (**inner).clone();
            }
            mut_visit::walk_expr(self, expression);
        }
    }

    fn canonical_item(text: &str) -> String {
        let without_labels = text
            .lines()
            .filter(|line| !line.trim_start().starts_with("#[proctor("))
            .collect::<Vec<_>>()
            .join("\n");
        let mut krate = utils::ast::parse_crate(without_labels);
        ParenNormalizer.visit_crate(&mut krate);
        let [item] = &krate.items[..] else { panic!("expected exactly one item in {text}") };
        pprust::item_to_string(item)
    }

    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        assert_eq!(
            canonical_item(&function(&records, path).annotated_skeleton),
            {
                let mut expected = utils::ast::parse_crate(expected.to_owned());
                PresentationBindingNormalizer.visit_crate(&mut expected);
                ParenNormalizer.visit_crate(&mut expected);
                pprust::item_to_string(&expected.items[0])
            }
        );
    })
    .unwrap();
}

fn simple_local_types(source: &str) -> Vec<(String, String, String)> {
    struct Finder {
        function_path: String,
        locals: Vec<(String, String, String)>,
    }

    impl<'ast> rustc_ast::visit::Visitor<'ast> for Finder {
        fn visit_local(&mut self, local: &'ast rustc_ast::Local) {
            if let PatKind::Ident(_, ident, None) = local.pat.kind
                && let Some(ty) = &local.ty
            {
                self.locals.push((
                    self.function_path.clone(),
                    ident.to_string(),
                    pprust::ty_to_string(ty),
                ));
            }
            rustc_ast::visit::walk_local(self, local);
        }
    }

    run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        let mut locals = vec![];
        for record in records {
            let ItemRecord::Function(function) = record else {
                continue;
            };
            let krate = utils::ast::parse_crate(function.annotated_skeleton);
            let mut finder = Finder {
                function_path: function.path,
                locals: vec![],
            };
            finder.visit_crate(&krate);
            locals.extend(finder.locals);
        }
        locals
    })
    .unwrap()
}

fn assert_paths(records: &[ItemRecord], expected: &[(&str, ItemKindName)]) {
    assert_eq!(
        records
            .iter()
            .map(|record| (record.path(), record.kind()))
            .collect::<Vec<_>>(),
        expected
    );
    assert_eq!(
        records.iter().map(ItemRecord::id).collect::<Vec<_>>(),
        (0..records.len() as u64).collect::<Vec<_>>()
    );
}

fn comprehensive_fixture() -> &'static str {
    r#"const N: usize = 4;
mod model {
    pub struct Point { pub x: i32 }
    pub union Bits { pub i: i32, pub u: u32 }
    pub enum Mode { Off = 0, On = crate::N as isize }
    pub type PointPtr = *mut Point;
    pub static ORIGIN: Point = Point { x: 0 };
    pub unsafe fn read(p: *const Point) -> i32 {
        let x = (*p).x;
        if x > 0 { x } else { crate::helper(x) }
    }
}
pub unsafe fn helper(x: i32) -> i32 {
    let mut total = 0;
    for i in 0..x { total += i; }
    if x <= 0 { total } else { helper(x - 1) }
}"#
}

#[test]
fn skeleton_json_is_a_top_level_array_with_pascal_case_kinds() {
    let records = generate(
        "pub unsafe fn f() {}\npub static S: i32 = 0;\npub const C: i32 = 0;\npub type A = i32;\npub enum E { V }\npub struct T { pub x: i32 }\npub union U { pub x: i32, pub y: u32 }",
    );
    assert_paths(
        &records,
        &[
            ("f", ItemKindName::Fn),
            ("S", ItemKindName::Static),
            ("C", ItemKindName::Const),
            ("A", ItemKindName::TyAlias),
            ("E", ItemKindName::Enum),
            ("T", ItemKindName::Struct),
            ("U", ItemKindName::Union),
        ],
    );
    assert!(
        serde_json::from_str::<serde_json::Value>(&skeletons_to_json(&records).unwrap())
            .unwrap()
            .is_array()
    );
}

#[test]
fn record_variants_serialize_only_their_defined_fields() {
    let records =
        generate("pub unsafe fn f() {}\npub static S: i32 = 0;\npub struct T { pub x: i32 }");
    let json: serde_json::Value =
        serde_json::from_str(&skeletons_to_json(&records).unwrap()).unwrap();
    let objects = json.as_array().unwrap();
    let keys = |index: usize| {
        objects[index]
            .as_object()
            .unwrap()
            .keys()
            .map(String::as_str)
            .collect::<std::collections::BTreeSet<_>>()
    };
    assert_eq!(
        keys(0),
        [
            "id",
            "path",
            "kind",
            "name",
            "annotated_source",
            "annotated_skeleton",
            "source_signature",
            "target_signature",
            "needs_transformation",
            "statements_requiring_transformation",
            "foreign_function_names",
            "signature_dependencies",
            "dependencies"
        ]
        .into_iter()
        .collect()
    );
    assert_eq!(
        keys(1),
        [
            "id",
            "path",
            "kind",
            "declaration",
            "signature_dependencies",
            "dependencies"
        ]
        .into_iter()
        .collect()
    );
    assert_eq!(
        keys(2),
        ["id", "path", "kind", "definition", "dependencies"]
            .into_iter()
            .collect()
    );
    assert!(!objects.iter().any(|value| {
        value
            .as_object()
            .unwrap()
            .values()
            .any(serde_json::Value::is_null)
    }));
}

#[test]
fn json_round_trip_preserves_embedded_rust_text() {
    let records = generate(
        r#"pub unsafe fn text() -> usize {
    let s = "quote:\" slash:\\ tab:\t line:\n";
    s.len()
}"#,
    );
    let before = function(&records, "text").clone();
    let round_trip: Vec<ItemRecord> =
        serde_json::from_str(&skeletons_to_json(&records).unwrap()).unwrap();
    assert_eq!(&before, function(&round_trip, "text"));
    assert_eq!(before.source_signature, "pub unsafe fn text() -> usize");
    assert!(
        before
            .annotated_skeleton
            .contains("let mut s: &str = \"quote:"),
        "{}",
        before.annotated_skeleton
    );
}

#[test]
fn json_serialization_is_byte_deterministic() {
    let source = comprehensive_fixture();
    assert_eq!(
        skeletons_to_json(&generate(source)).unwrap(),
        skeletons_to_json(&generate(source)).unwrap()
    );
}

#[test]
fn empty_crate_serializes_as_empty_array() {
    let records = generate("");
    assert!(records.is_empty());
    assert_eq!(skeletons_to_json(&records).unwrap(), "[]");
}

#[test]
fn includes_exactly_the_supported_item_kinds() {
    let records = generate(
        "pub unsafe fn f() {}\npub static S: i32 = 0;\npub static mut M: i32 = 0;\npub const C: i32 = 0;\npub type A = i32;\npub enum E { V }\npub struct Braced { pub x: i32 }\npub struct Tuple(pub i32);\npub struct Unit;\npub union U { pub x: i32, pub y: u32 }",
    );
    assert_paths(
        &records,
        &[
            ("f", ItemKindName::Fn),
            ("S", ItemKindName::Static),
            ("M", ItemKindName::Static),
            ("C", ItemKindName::Const),
            ("A", ItemKindName::TyAlias),
            ("E", ItemKindName::Enum),
            ("Braced", ItemKindName::Struct),
            ("Tuple", ItemKindName::Struct),
            ("Unit", ItemKindName::Struct),
            ("U", ItemKindName::Union),
        ],
    );
    assert_eq!(value(&records, "M").declaration, "pub static mut M: i32;");
}

#[test]
fn flattens_inline_modules_in_recursive_source_order() {
    let records = generate(
        "const A: usize = 1; mod outer { #[derive(Clone, Copy)] pub struct S { pub x: i32 } mod inner { pub unsafe fn f() {} } pub const B: usize = 2; } static Z: i32 = 0;",
    );
    assert_paths(
        &records,
        &[
            ("A", ItemKindName::Const),
            ("outer::S", ItemKindName::Struct),
            ("outer::inner::f", ItemKindName::Fn),
            ("outer::B", ItemKindName::Const),
            ("Z", ItemKindName::Static),
        ],
    );
    assert!(
        type_record(&records, "outer::S")
            .definition
            .contains("#[derive(Clone, Copy)]")
    );
}

#[test]
fn distinguishes_same_final_name_in_different_modules() {
    let records = generate(
        "mod a { pub struct T; pub unsafe fn f() {} } mod b { pub struct T; pub unsafe fn f() {} }",
    );
    assert_paths(
        &records,
        &[
            ("a::T", ItemKindName::Struct),
            ("a::f", ItemKindName::Fn),
            ("b::T", ItemKindName::Struct),
            ("b::f", ItemKindName::Fn),
        ],
    );
}

#[test]
fn preserves_raw_identifiers_in_paths_and_names() {
    let records = generate("mod r#type { pub unsafe fn r#match() {} }");
    assert_eq!(records[0].path(), "r#type::r#match");
    assert_eq!(function(&records, "r#type::r#match").name, "r#match");
}

#[test]
fn omits_modules_uses_and_extern_crates_as_records() {
    let records = generate(
        "extern crate core as rust_core; mod m { pub struct T; pub const C: i32 = 3; } use m::T as Alias; use m::*; pub unsafe fn f(_alias: Alias) -> i32 { let _ = rust_core::mem::size_of::<Alias>(); C }",
    );
    assert_paths(
        &records,
        &[
            ("m::T", ItemKindName::Struct),
            ("m::C", ItemKindName::Const),
            ("f", ItemKindName::Fn),
        ],
    );
    assert_eq!(function(&records, "f").signature_dependencies, [0]);
    assert_eq!(function(&records, "f").dependencies, [0, 1]);
}

#[test]
fn omits_foreign_modules_and_foreign_items() {
    let records = generate(
        "#![feature(extern_types)] unsafe extern \"C\" { static FOREIGN: i32; fn foreign_fn(x: i32) -> i32; type ForeignTy; } pub unsafe fn caller() -> i32 { foreign_fn(FOREIGN) }",
    );
    assert_paths(&records, &[("caller", ItemKindName::Fn)]);
    assert!(function(&records, "caller").dependencies.is_empty());
}

#[test]
fn filters_nonrecord_item_kinds_in_supported_input() {
    run_compiler_on_str("core::arch::global_asm!(\"\");", |tcx| {
        for source in [
            "extern crate core;",
            "use core::mem;",
            "mod m {}",
            "extern \"C\" {}",
        ] {
            let item = &utils::ast::parse_crate(source.to_owned()).items[0];
            assert_eq!(included_item_kind(item), None, "{source}");
        }
        let krate = utils::ast::expanded_ast(tcx);
        let global_asm = krate
            .items
            .iter()
            .find(|item| matches!(item.kind, rustc_ast::ItemKind::GlobalAsm(_)))
            .unwrap();
        assert_eq!(included_item_kind(global_asm), None);
    })
    .unwrap();
}

#[test]
fn does_not_emit_variant_field_or_constructor_records() {
    let records = generate(
        "pub struct S { pub x: i32, pub y: i32 } pub enum E { Unit, Tuple(i32), Struct { value: i32 } }",
    );
    assert_paths(
        &records,
        &[("S", ItemKindName::Struct), ("E", ItemKindName::Enum)],
    );
}

#[test]
fn type_records_preserve_complete_definitions() {
    let records = generate(
        "#[repr(C)] #[derive(Clone, Copy)] pub struct S { pub x: i32, y: u8 } #[repr(transparent)] pub struct W(pub i32); #[repr(i32)] pub enum E { A = -1, B = 4 } pub type Alias = (S, [W; 2]);",
    );
    assert!(
        type_record(&records, "S")
            .definition
            .contains("#[derive(Clone, Copy)]")
    );
    assert!(type_record(&records, "S").definition.contains("#[repr(C)]"));
    assert_eq!(type_record(&records, "Alias").dependencies, [0, 1]);
}

#[test]
fn value_records_render_declarations_without_initializers() {
    let records = generate(
        "#[no_mangle] pub static X: i32 = 1; pub static mut BUFFER: *mut u8 = core::ptr::null_mut(); pub const SIZE: usize = 4;",
    );
    assert_eq!(value(&records, "X").declaration, "pub static X: i32;");
    assert_eq!(
        value(&records, "BUFFER").declaration,
        "pub static mut BUFFER: *mut u8;"
    );
    assert_eq!(
        value(&records, "SIZE").declaration,
        "pub const SIZE: usize;"
    );
}

#[test]
fn function_records_sanitize_prompt_only_header_tokens_and_split_signatures() {
    let records = generate(
        "#[no_mangle] pub unsafe extern \"system\" fn add(x: i32, y: i32) -> i32 { x + y }",
    );
    let function = function(&records, "add");
    assert_eq!(
        function.source_signature,
        "pub unsafe fn add(mut x: i32, mut y: i32) -> i32"
    );
    assert_eq!(
        function.target_signature,
        "pub unsafe fn add(mut x: i32, mut y: i32) -> i32"
    );
    assert!(!function.annotated_source.contains("no_mangle"));
    assert!(!function.annotated_source.contains("extern"));
}

fn assert_fn_deps(source: &str, path: &str, signature: &[u64], all: &[u64]) {
    let records = generate(source);
    assert_eq!(function(&records, path).signature_dependencies, signature);
    assert_eq!(function(&records, path).dependencies, all);
}

#[test]
fn collects_direct_function_signature_type_dependencies() {
    assert_fn_deps(
        "struct In; struct Out; pub unsafe fn f(_input: In, _out: *const Out) -> Out { loop {} }",
        "f",
        &[0, 1],
        &[0, 1],
    );
}

#[test]
fn finds_types_nested_inside_signature_types() {
    assert_fn_deps(
        "struct A; struct B; struct C; struct D; struct E; struct F; pub unsafe fn nested(_a: &A, _b: *mut B, _c: [C; 2], _d: &[D], _e: (E, Option<F>)) {}",
        "nested",
        &[0, 1, 2, 3, 4, 5],
        &[0, 1, 2, 3, 4, 5],
    );
}

#[test]
fn collects_const_dependencies_from_array_lengths() {
    assert_fn_deps(
        "const N: usize = 4; struct T; pub unsafe fn f(x: [T; N]) -> [u8; N] { let _x = x; loop {} }",
        "f",
        &[0, 1],
        &[0, 1],
    );
}

#[test]
fn collects_static_and_const_signature_dependencies() {
    let records = generate(
        "#[derive(Clone, Copy)] struct T; const N: usize = 2; static mut X: *const T = core::ptr::null(); const VALUES: [T; N] = [T; N];",
    );
    assert_eq!(value(&records, "X").signature_dependencies, [0]);
    assert_eq!(value(&records, "VALUES").signature_dependencies, [0, 1]);
}

#[test]
fn collects_direct_function_calls_from_bodies() {
    assert_fn_deps(
        "pub unsafe fn callee(_x: i32) {} pub unsafe fn caller() { callee(1); callee(2); }",
        "caller",
        &[],
        &[0],
    );
}

#[test]
fn includes_direct_self_recursion() {
    assert_fn_deps(
        "pub unsafe fn recur(n: u32) -> u32 { if n == 0 { 0 } else { recur(n - 1) } }",
        "recur",
        &[],
        &[0],
    );
}

#[test]
fn collects_body_local_type_annotations_and_cast_types() {
    assert_fn_deps(
        "struct A; struct B; pub unsafe fn f() { let x: A = A; let p: *const A = &x; let _ = p as *const B; }",
        "f",
        &[],
        &[0, 1],
    );
}

#[test]
fn collects_static_and_const_uses_from_function_bodies() {
    assert_fn_deps(
        "static mut S: i32 = 1; const C: i32 = 2; pub unsafe fn f() -> i32 { S + C }",
        "f",
        &[],
        &[0, 1],
    );
}

#[test]
fn resolves_use_aliases_and_globs_to_item_ids() {
    assert_fn_deps(
        "mod m { pub struct T; pub const C: i32 = 3; } use m::T as Alias; use m::*; pub unsafe fn f(_alias: Alias) -> i32 { C }",
        "f",
        &[0],
        &[0, 1],
    );
}

#[test]
fn does_not_confuse_shadowing_locals_with_items() {
    assert_fn_deps(
        "unsafe fn value() -> i32 { 5 } pub unsafe fn f() -> i32 { let value = 1; value + crate::value() }",
        "f",
        &[],
        &[0],
    );
}

#[test]
fn ignores_foreign_and_external_dependencies() {
    assert_fn_deps(
        "unsafe extern \"C\" { fn foreign(x: i32) -> i32; static FOREIGN: i32; } pub unsafe fn f() -> usize { let x: Option<i32> = Some(foreign(FOREIGN)); core::mem::size_of_val(&x) }",
        "f",
        &[],
        &[],
    );
}

#[test]
fn dependency_lists_are_direct_not_transitive() {
    let records = generate(
        "struct A; struct B(A); pub unsafe fn callee(_b: B) {} pub unsafe fn caller(b: B) { callee(b); }",
    );
    assert_eq!(type_record(&records, "B").dependencies, [0]);
    assert_eq!(function(&records, "callee").dependencies, [1]);
    assert_eq!(function(&records, "caller").dependencies, [1, 2]);
}

#[test]
fn canonicalizes_struct_constructors_to_struct_records() {
    assert_fn_deps(
        "struct A { x: i32 } struct B(i32); struct C; pub unsafe fn f() { let _ = A { x: 1 }; let _ = B(2); let _ = C; let _ = A { x: 3 }; }",
        "f",
        &[],
        &[0, 1, 2],
    );
}

#[test]
fn canonicalizes_enum_variants_in_expressions_and_patterns() {
    assert_fn_deps(
        "enum E { Unit, Tuple(i32), Struct { x: i32 } } pub unsafe fn f(tag: i32) -> i32 { let e = if tag == 0 { E::Unit } else { E::Tuple(tag) }; let _ = E::Struct { x: tag }; match e { E::Unit => { 0 } E::Tuple(x) => { x } E::Struct { x } => { x } } }",
        "f",
        &[],
        &[0],
    );
}

#[test]
fn canonicalizes_field_accesses_to_containing_types() {
    assert_fn_deps(
        "struct S { x: i32, y: i32 } struct T(i32); unsafe fn make_s() -> S { S { x: 1, y: 2 } } unsafe fn make_t() -> T { T(3) } pub unsafe fn f() -> i32 { let mut s = make_s(); let t = make_t(); s.x = s.y; s.x + t.0 }",
        "f",
        &[],
        &[0, 1, 2, 3],
    );
}

#[test]
fn collects_initializer_dependencies_for_statics_and_consts() {
    let records = generate(
        "struct Marker; const BASE: i32 = 1; static X: i32 = BASE; const Y: Marker = Marker;",
    );
    assert!(value(&records, "X").signature_dependencies.is_empty());
    assert_eq!(value(&records, "X").dependencies, [1]);
    assert_eq!(value(&records, "Y").signature_dependencies, [0]);
    assert_eq!(value(&records, "Y").dependencies, [0]);
}

#[test]
fn collects_type_alias_dependencies() {
    let records =
        generate("const N: usize = 4; struct S; type A = S; type B = Option<(*mut A, [S; N])>;");
    assert_eq!(type_record(&records, "A").dependencies, [1]);
    assert_eq!(type_record(&records, "B").dependencies, [0, 1, 2]);
}

#[test]
fn collects_struct_and_union_field_dependencies() {
    let records = generate(
        "struct A; type I = i32; struct Braced { a: *const A, i: I } struct Tuple(*mut A, I); union U { a: *const A, i: I }",
    );
    for path in ["Braced", "Tuple", "U"] {
        assert_eq!(type_record(&records, path).dependencies, [0, 1]);
    }
}

#[test]
fn collects_enum_payload_and_discriminant_dependencies() {
    let records = generate(
        "const D: isize = 1; struct A; struct B; #[repr(isize)] enum E { One(A) = D, Two { b: B } = 2 }",
    );
    assert_eq!(type_record(&records, "E").dependencies, [0, 1, 2]);
}

#[test]
fn handles_self_recursive_and_mutually_recursive_types() {
    let records =
        generate("struct Node { next: *mut Node } struct A { b: *mut B } struct B { a: *mut A }");
    assert_eq!(type_record(&records, "Node").dependencies, [0]);
    assert_eq!(type_record(&records, "A").dependencies, [2]);
    assert_eq!(type_record(&records, "B").dependencies, [1]);
}

#[test]
fn resolves_same_spelling_in_value_and_type_namespaces() {
    let records =
        generate("type X = i32; const X: i32 = 7; pub unsafe fn f(x: X) -> i32 { X + x }");
    assert_eq!(function(&records, "f").signature_dependencies, [0]);
    assert_eq!(function(&records, "f").dependencies, [0, 1]);
}

#[test]
fn dependency_lists_are_deduplicated_sorted_and_subset_consistent() {
    assert_fn_deps(
        "struct A; struct B; struct C; pub unsafe fn f(_c: C, _a: *const A) -> A { let _: B = B; let _: B = B; loop {} }",
        "f",
        &[0, 2],
        &[0, 1, 2],
    );
}

fn labels(text: &str) -> Vec<u32> {
    let mut rest = text;
    let mut labels = vec![];
    while let Some(start) = rest.find("#[proctor(") {
        rest = &rest[start + "#[proctor(".len()..];
        let end = rest.find(')').unwrap();
        labels.push(rest[..end].parse().unwrap());
        rest = &rest[end + 1..];
    }
    labels
}

#[test]
fn labels_let_semi_and_tail_statements() {
    let records = generate(
        "unsafe extern \"C\" { fn consume(x: i32); } pub unsafe fn f() -> i32 { let x = 1; consume(x); x }",
    );
    let f = function(&records, "f");
    assert_eq!(labels(&f.annotated_source), [0, 1, 2]);
    assert_eq!(labels(&f.annotated_skeleton), [0, 1, 2]);
}

#[test]
fn labels_reset_for_each_function() {
    let records = generate(
        "pub unsafe fn a() -> i32 { let x = 1; x } pub unsafe fn b() -> i32 { let y = 2; y + 1 }",
    );
    for path in ["a", "b"] {
        assert_eq!(labels(&function(&records, path).annotated_source), [0, 1]);
        assert_eq!(labels(&function(&records, path).annotated_skeleton), [0, 1]);
    }
}

#[test]
fn nested_labels_follow_depth_first_preorder() {
    let records = generate(
        "unsafe fn hit(_x: i32) {} pub unsafe fn f(flag: bool) { if flag { hit(1); loop { hit(2); break; } } else { hit(3); } hit(4); }",
    );
    assert_eq!(
        labels(&function(&records, "f").annotated_source),
        [0, 1, 2, 3, 4, 5, 6]
    );
}

#[test]
fn source_and_skeleton_have_identical_label_trees() {
    let records = generate(comprehensive_control_fixture());
    let f = function(&records, "comprehensive");
    assert_eq!(labels(&f.annotated_source), (0..=11).collect::<Vec<_>>());
    assert_eq!(labels(&f.annotated_source), labels(&f.annotated_skeleton));
}

#[test]
fn rejects_top_level_empty_statement_in_function() {
    let error = generate_error("pub unsafe fn f() { ; }");
    assert_eq!(error.kind, GenerationErrorKind::EmptyStatement);
    assert_eq!(error.function_path, "f");
    assert!(
        error
            .message
            .contains("empty statement cannot be annotated")
    );
}

#[test]
fn rejects_nested_empty_statement() {
    let error = generate_error("pub unsafe fn f(flag: bool) { if flag { loop { ; } } }");
    assert_eq!(error.kind, GenerationErrorKind::EmptyStatement);
    assert_eq!(error.function_path, "f");
}

#[test]
fn phase_1_rejects_local_const_and_static_recursively() {
    for (source, kind) in [
        (
            r#"pub unsafe fn f() -> i32 {
                const LOCAL: i32 = { let inner = 1; inner };
                LOCAL
            }"#,
            "const",
        ),
        (
            r#"pub unsafe fn f(flag: bool) -> i32 {
                if flag {
                    static mut STATE: i32 = { let inner = 1; inner };
                    STATE
                } else {
                    0
                }
            }"#,
            "static",
        ),
    ] {
        let error = generate_error(source);
        assert_eq!(error.kind, GenerationErrorKind::FunctionLocalItem);
        assert_eq!(error.function_path, "f");
        assert!(error.message.contains(kind));
    }
}

#[test]
fn phase_1_rejects_representative_other_local_items() {
    for (source, kind) in [
        ("pub unsafe fn f() { fn local() {} }", "function"),
        ("pub unsafe fn f() { type Local = i32; }", "type alias"),
        ("pub unsafe fn f() { struct Local; }", "struct"),
        ("pub unsafe fn f() { enum Local { Variant } }", "enum"),
        ("pub unsafe fn f() { union Local { field: i32 } }", "union"),
        ("pub unsafe fn f() { mod local {} }", "module"),
        ("pub unsafe fn f() { use core::mem; }", "use"),
        (
            "pub unsafe fn f() { unsafe extern \"C\" { fn local(); } }",
            "foreign",
        ),
        ("pub unsafe fn f() { trait Local {} }", "trait"),
        ("struct Local; pub unsafe fn f() { impl Local {} }", "impl"),
        (
            "pub unsafe fn f() { macro_rules! local { () => {} } }",
            "macro definition",
        ),
    ] {
        let error = generate_error(source);
        assert_eq!(error.kind, GenerationErrorKind::FunctionLocalItem);
        assert_eq!(error.function_path, "f");
        assert!(error.message.contains(kind), "{source}: {}", error.message);
    }
}

#[test]
fn replaces_leaf_expression_payloads_with_todo() {
    let source = "unsafe fn callee(_x: i32) {} pub unsafe fn f() -> i32 { let x = 1; callee(x); println!(\"{x}\"); -x + 2 }";
    let records = generate(source);
    let skeleton = &function(&records, "f").annotated_skeleton;
    assert!(skeleton.contains("let mut x: i32 = 1;"));
    assert_eq!(skeleton.matches("todo!()").count(), 1);
    assert_eq!(labels(skeleton), [0, 1, 2, 3]);
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f() -> i32 { let x: i32 = 1; callee(x); todo!(); -x + 2 }",
    );
}

#[test]
fn materializes_inferred_types_for_simple_bindings() {
    let source = "struct Local; pub unsafe fn f() { let b = true; let i = -1i32; let u = 1u64; let n = 1.5f32; let c = 'x'; let t = (1i32, 2u8); let a = [1u16; 3]; let r = &i; let l = Local; }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    for declaration in [
        "let mut b: bool = true;",
        "let mut i: i32 = -1i32;",
        "let mut u: u64 = 1u64;",
        "let mut n: f32 = 1.5f32;",
        "let mut c: char = 'x';",
        "let mut t: (i32, u8) = (1i32, 2u8);",
        "let mut a: [u16; 3] = [1u16; 3];",
        "let mut r: &i32 = &i;",
        "let mut l: Local = Local;",
    ] {
        assert!(
            skeleton.contains(declaration),
            "missing {declaration} in {skeleton}"
        );
    }
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f() { let b: bool = true; let i: i32 = -1i32; let u: u64 = 1u64; let n: f32 = 1.5f32; let c: char = 'x'; let t: (i32, u8) = (1i32, 2u8); let a: [u16; 3] = [1u16; 3]; let r: &i32 = &i; let l: Local = Local; }",
    );
}

#[test]
fn preserves_mutability_declarations_and_existing_types() {
    let source = "struct T; type Count = i32; pub unsafe fn f() { let mut a = 1; let x: T; let y: Count = 2; x = T; let _ = (a, x, y); }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("let mut a: i32 = 1;"));
    assert!(skeleton.contains("let mut x: T;"));
    assert!(skeleton.contains("let mut y: Count = 2;"));
    assert_eq!(skeleton.matches("todo!()").count(), 0);
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f() { let mut a: i32 = 1; let x: T; let y: Count = 2; x = T; let _ = (a, x, y); }",
    );
}

#[test]
fn holes_assignments_and_preserves_return_and_break_roles() {
    let source = "pub unsafe fn f(mut x: i32) -> i32 { x = 1; x += 2; let y = loop { break x; }; return y; }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("let mut y: i32 = loop"));
    assert!(skeleton.contains("break x;"));
    assert!(skeleton.contains("return y;"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(mut x: i32) -> i32 { x = 1; x += 2; let y: i32 = loop { break x; }; return y; }",
    );
}

#[test]
fn preserves_if_and_else_structure() {
    let source = "unsafe fn sink(_x: i32) {} pub unsafe fn f(flag: bool) { if flag { sink(1); } else { sink(2); } }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("if flag"));
    assert!(skeleton.contains("} else {"));
    assert_eq!(
        labels(&function(&records, "f").annotated_skeleton),
        [0, 1, 2]
    );
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(flag: bool) { if flag { sink(1); } else { sink(2); } }",
    );
}

#[test]
fn preserves_nested_if_and_else_if_structure() {
    let source = "pub unsafe fn f(a: bool, b: bool, c: bool) -> i32 { let x = if a { 1 } else { 2 }; if b { if c { x } else { 3 } } else if a { 4 } else { 5 } }";
    let records = generate(source);
    let f = function(&records, "f");
    assert_eq!(labels(&f.annotated_skeleton), (0..=8).collect::<Vec<_>>());
    assert_eq!(f.annotated_skeleton.matches("if ").count(), 4);
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(a: bool, b: bool, c: bool) -> i32 { let x: i32 = if a { 1 } else { 2 }; if b { if c { x } else { 3 } } else if a { 4 } else { 5 } }",
    );
}

#[test]
fn preserves_if_let_and_while_let_patterns() {
    let source = "unsafe fn sink(_x: i32) {} pub unsafe fn f(mut value: Option<i32>) { if let Some(x) = value { sink(x); } while let Some(x) = value { sink(x); value = None; } }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("if let Some(mut x) = value"));
    assert!(skeleton.contains("while let Some(mut x) = value"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(mut value: Option<i32>) { if let Some(x) = value { sink(x); } while let Some(x) = value { sink(x); value = None; } }",
    );
}

#[test]
fn preserves_while_for_and_loop_constructs() {
    let source = "unsafe fn sink(_x: i32) {} pub unsafe fn f(mut n: i32, pairs: [(i32, i32); 2]) { 'w: while n > 0 { n -= 1; } for (x, y) in pairs { sink(x + y); } 'l: loop { break 'l; } }";
    let records = generate(source);
    let skeleton = compact(&function(&records, "f").annotated_skeleton);
    assert!(skeleton.contains("'w: while n > 0"));
    assert!(skeleton.contains("for (mut x, mut y) in todo!()"));
    assert!(skeleton.contains("'l: loop"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(mut n: i32, pairs: [(i32, i32); 2]) { 'w: while n > 0 { n -= 1; } for (x, y) in todo!() { sink(x + y); } 'l: loop { break 'l; } }",
    );
}

#[test]
fn preserves_match_arms_patterns_guards_and_order() {
    let source = "enum E { Unit, Tuple(i32), Struct { x: i32 } } unsafe fn sink(_x: i32) {} pub unsafe fn f(e: E, n: i32, pair: (i32, i32)) -> i32 { let a = match e { E::Unit => { 0 } E::Tuple(x) if x > 0 => { x } E::Tuple(_) => { -1 } E::Struct { x } => { sink(x); x }, }; let b = match n { 0 => { 0 } 1..=3 => { 1 } _ => { 2 } }; match pair { (x, y) => { a + b + x + y } } }";
    let records = generate(source);
    let f = function(&records, "f");
    assert_eq!(labels(&f.annotated_skeleton), (0..=11).collect::<Vec<_>>());
    let skeleton = compact(&f.annotated_skeleton);
    assert!(skeleton.contains("E::Tuple(mut x) if x > 0"));
    assert!(skeleton.contains("1..=3 =>"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(e: E, n: i32, pair: (i32, i32)) -> i32 { let a: i32 = match e { E::Unit => { 0 } E::Tuple(x) if x > 0 => { x } E::Tuple(_) => { -1 } E::Struct { x } => { sink(x); x }, }; let b: i32 = match todo!() { 0 => { 0 } 1..=3 => { 1 } _ => { 2 } }; match pair { (x, y) => { a + b + x + y } } }",
    );
}

#[test]
fn preserves_let_else_and_plain_nested_blocks() {
    let source = "unsafe fn sink(_x: i32) {} pub unsafe fn f(value: Option<i32>) -> i32 { let Some(x): Option<i32> = value else { return 0; }; let y = { sink(x); x + 1 }; y }";
    let records = generate(source);
    let f = function(&records, "f");
    assert_eq!(labels(&f.annotated_skeleton), [0, 1, 2, 3, 4, 5]);
    let skeleton = compact(&f.annotated_skeleton);
    assert!(skeleton.contains("let Some(mut x): Option<i32> = value else"));
    assert!(skeleton.contains("return 0;"));
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(value: Option<i32>) -> i32 { let Some(x): Option<i32> = value else { return 0; }; let y: i32 = { sink(x); x + 1 }; y }",
    );
}

#[test]
fn preserves_existing_identifiers_paths_and_patterns() {
    let source = "mod m { pub struct Pair { pub left: i32, pub right: i32 } } pub unsafe fn keep_names(mut input_value: m::Pair) -> i32 { let mut local_total = input_value.left; 'outer: loop { let m::Pair { left: bound_left, right: bound_right } = input_value; local_total += bound_left + bound_right; break 'outer; } local_total }";
    let records = generate(source);
    let skeleton = &function(&records, "keep_names").annotated_skeleton;
    for name in ["input_value", "local_total", "bound_left", "bound_right"] {
        assert!(skeleton.contains(name));
    }
    for forbidden in ["__crat", "proctor_tmp"] {
        assert!(!skeleton.contains(forbidden));
    }
    assert_skeleton(
        source,
        "keep_names",
        "pub unsafe fn keep_names(mut input_value: m::Pair) -> i32 { let mut local_total: i32 = input_value.left; 'outer: loop { let m::Pair { left: bound_left, right: bound_right } = input_value; local_total += bound_left + bound_right; break 'outer; } local_total }",
    );
}

fn comprehensive_control_fixture() -> &'static str {
    "unsafe fn sink(_x: i32) {} pub unsafe fn comprehensive(mut n: i32) -> i32 { if n > 0 { sink(n); } while n > 1 { n -= 1; } for i in 0..n { sink(i); } loop { break; } match n { 0 => { sink(0); } _ => { sink(n); } } n }"
}

#[test]
fn annotated_source_and_skeleton_snippets_parse_independently() {
    let records = generate(comprehensive_control_fixture());
    let f = function(&records, "comprehensive");
    assert_eq!(labels(&f.annotated_source), (0..=11).collect::<Vec<_>>());
    run_compiler_on_str(&f.annotated_source, |_| ()).unwrap();
    run_compiler_on_str(&f.annotated_skeleton, |_| ()).unwrap();
}

#[test]
fn preserves_payloadless_control_expressions_without_holes() {
    let source =
        "pub unsafe fn f(flag: bool) { if flag { return; } loop { if flag { continue; } break; } }";
    let records = generate(source);
    let skeleton = &function(&records, "f").annotated_skeleton;
    for expression in ["return;", "continue;", "break;"] {
        assert_eq!(skeleton.matches(expression).count(), 1);
    }
    assert_eq!(labels(skeleton), [0, 1, 2, 3, 4, 5]);
    assert_skeleton(
        source,
        "f",
        "pub unsafe fn f(flag: bool) { if flag { return; } loop { if flag { continue; } break; } }",
    );
}

#[test]
fn rejects_non_block_match_arm() {
    let error = generate_error("pub unsafe fn f(n: i32) -> i32 { match n { 0 => 1, _ => { 2 } } }");
    assert_eq!(error.kind, GenerationErrorKind::NonBlockMatchArm);
    assert_eq!(error.function_path, "f");
    assert!(
        error
            .message
            .contains("match arm body must be a block expression")
    );
}

#[test]
fn allows_restricted_conditionals_beneath_non_control_payloads() {
    let source = "
        pub unsafe fn assign(mut value: i32, flag: bool) {
            value = 1 + if flag { 2 } else { 3 };
        }
        pub unsafe fn wrapped_return(flag: bool) -> Option<i32> {
            return Some(if flag { 1 } else { 2 });
        }
        pub unsafe fn wrapped_let(flag: bool) -> i32 {
            let value = Some(if flag { 1 } else { 2 });
            value.unwrap()
        }
    ";
    let records = generate(source);
    for path in ["assign", "wrapped_return"] {
        let function = function(&records, path);
        assert_eq!(labels(&function.annotated_source), [0]);
        assert_eq!(labels(&function.annotated_skeleton), [0]);
        assert!(function.annotated_skeleton.contains("if "));
    }
    let wrapped_let = function(&records, "wrapped_let");
    assert_eq!(labels(&wrapped_let.annotated_source), [0, 1]);
    assert_eq!(labels(&wrapped_let.annotated_skeleton), [0, 1]);
    assert_skeleton(
        source,
        "assign",
        "pub unsafe fn assign(mut value: i32, flag: bool) { value = 1 + if flag { 2 } else { 3 }; }",
    );
    assert_skeleton(
        source,
        "wrapped_return",
        "pub unsafe fn wrapped_return(flag: bool) -> Option<i32> { return Some(if flag { 1 } else { 2 }); }",
    );
    assert_skeleton(
        source,
        "wrapped_let",
        "pub unsafe fn wrapped_let(flag: bool) -> i32 { let value: std::option::Option<i32> = Some(if flag { 1 } else { 2 }); value.unwrap() }",
    );
}

#[test]
fn allows_else_if_chains_and_recursive_branch_tail_conditionals() {
    let source = "
        pub unsafe fn chained(c1: bool, c2: bool) -> i32 {
            let value = Some(if c1 { 1 } else if c2 { 2 } else { 3 });
            value.unwrap()
        }
        pub unsafe fn nested(c1: bool, c2: bool) -> i32 {
            let value = Some(if c1 {
                1
            } else {
                if c2 { 2 } else { 3 }
            });
            value.unwrap()
        }
    ";
    let records = generate(source);
    for path in ["chained", "nested"] {
        let function = function(&records, path);
        assert_eq!(labels(&function.annotated_source), [0, 1]);
        assert_eq!(labels(&function.annotated_skeleton), [0, 1]);
        assert_eq!(function.annotated_source.matches("if ").count(), 2);
        assert!(function.annotated_skeleton.contains("if "));
        assert_skeleton(
            source,
            path,
            &format!(
                "pub unsafe fn {path}(c1: bool, c2: bool) -> i32 {{ let value: std::option::Option<i32> = {}; value.unwrap() }}",
                if path == "chained" {
                    "Some(if c1 { 1 } else if c2 { 2 } else { 3 })"
                } else {
                    "Some(if c1 { 1 } else { if c2 { 2 } else { 3 } })"
                }
            ),
        );
    }
}

#[test]
fn opaque_restricted_conditionals_keep_original_dependencies() {
    let source = "
        unsafe fn branch_value() -> i32 { 1 }
        pub unsafe fn f(flag: bool) -> i32 {
            let value = Some(if flag { branch_value() } else { 0 });
            value.unwrap()
        }
    ";
    let records = generate(source);
    let branch_id = record(&records, "branch_value").id();
    assert!(function(&records, "f").dependencies.contains(&branch_id));
}

#[test]
fn opaque_conditional_label_suppression_does_not_skip_body_validation() {
    let local_item = generate_error(
        "pub unsafe fn f(flag: bool) { let value = Some(if flag { { const LOCAL: i32 = 1; LOCAL } } else { 0 }); let _ = value; }",
    );
    assert_eq!(local_item.kind, GenerationErrorKind::FunctionLocalItem);
    assert!(local_item.message.contains("const"));

    let non_block_arm = generate_error(
        "pub unsafe fn f(flag: bool) { let value = Some(if flag { match 0 { 0 => 1, _ => { 2 } } } else { 3 }); let _ = value; }",
    );
    assert_eq!(non_block_arm.kind, GenerationErrorKind::NonBlockMatchArm);
}

#[test]
fn rejects_non_restricted_control_beneath_non_control_payloads() {
    for source in [
        "pub unsafe fn f(mut value: i32, flag: bool) { value = 1 + if flag { value += 1; 2 } else { 3 }; }",
        "pub unsafe fn f(mut value: i32, c1: bool, c2: bool) { value = 1 + if c1 { if c2 { value += 1; 2 } else { 3 } } else { 4 }; }",
        "pub unsafe fn f(flag: bool) { let value = Some(if flag { () }); let _ = value; }",
        "pub unsafe fn f(value: Option<i32>) { let result = Some(if let Some(value) = value { value } else { 0 }); let _ = result; }",
        "#![feature(let_chains)] pub unsafe fn f(value: Option<i32>) { let result = Some(if let Some(value) = value && value > 0 { value } else { 0 }); let _ = result; }",
        "pub unsafe fn f() { let value = Some(loop { break 1; }); let _ = value; }",
        "pub unsafe fn f(c1: bool, c2: bool) { let value = Some(if c1 { 1 + if c2 { 2 } else { 3 } } else { 4 }); let _ = value; }",
        "pub unsafe fn f(flag: bool) { let value = Some(if flag { 1; } else { 2; }); let _ = value; }",
    ] {
        let error = generate_error(source);
        assert_eq!(error.kind, GenerationErrorKind::NestedControlPayload);
        assert_eq!(error.function_path, "f");
        assert!(
            error
                .message
                .contains("control expression nested beneath a non-control payload")
        );
    }
}

#[test]
fn keeps_non_pointer_signature_types_unchanged() {
    let records = generate(
        "struct S { x: i32 } pub unsafe fn f(a: i32, b: (u8, bool), c: [i16; 2], s: S) -> (S, usize) { (s, a as usize + b.0 as usize + c[0] as usize) }",
    );
    let f = function(&records, "f");
    assert_eq!(
        f.source_signature,
        "pub unsafe fn f(mut a: i32, mut b: (u8, bool), mut c: [i16; 2], mut s: S)\n-> (S, usize)"
    );
    assert_eq!(
        f.target_signature,
        "pub unsafe fn f(mut a: i32, mut b: (u8, bool), mut c: [i16; 2], mut s: S)\n-> (S, usize)"
    );
}

fn scalar_reference_fixture() -> &'static str {
    "pub unsafe fn read_param(p: *const i32) -> i32 { *p } pub unsafe fn write_local() -> i32 { let mut x = 0i32; let p: *mut i32 = &mut x; *p = 7; x } pub unsafe fn read_local() -> i32 { let x = 7i32; let p: *const i32 = &x; *p }"
}

#[test]
fn selects_shared_and_mutable_scalar_references() {
    let records = generate(scalar_reference_fixture());
    assert!(
        function(&records, "read_param")
            .target_signature
            .contains("mut p: &i32")
    );
    assert!(
        function(&records, "write_local")
            .annotated_skeleton
            .contains("let mut p: &mut i32")
    );
    assert!(
        function(&records, "read_local")
            .annotated_skeleton
            .contains("let mut p: &i32")
    );
}

fn optional_reference_fixture() -> &'static str {
    "pub unsafe fn read(p: *const i32) -> i32 { if p.is_null() { 0 } else { *p } } pub unsafe fn write(p: *mut i32) { if !p.is_null() { *p = 1; } }"
}

#[test]
fn selects_optional_references_when_null_is_observable() {
    let records = generate(optional_reference_fixture());
    assert_eq!(
        function(&records, "read").target_signature,
        "pub unsafe fn read(mut p: Option<&i32>) -> i32"
    );
    assert_eq!(
        function(&records, "write").target_signature,
        "pub unsafe fn write(mut p: Option<&mut i32>)"
    );
}

fn array_pointer_fixture() -> &'static str {
    "pub unsafe fn read_array(a: [i32; 4]) -> i32 { let p: *const i32 = a.as_ptr(); *p.offset(1) } pub unsafe fn write_array(mut a: [i32; 4]) -> i32 { let p: *mut i32 = a.as_mut_ptr(); *p.offset(1) = 9; a[1] }"
}

#[test]
fn selects_shared_and_mutable_slices_for_array_borrows() {
    let records = generate(array_pointer_fixture());
    assert!(
        function(&records, "read_array")
            .annotated_skeleton
            .contains("let mut p: &[i32]")
    );
    assert!(
        function(&records, "write_array")
            .annotated_skeleton
            .contains("let mut p: &mut [i32]")
    );
    assert!(!skeletons_to_json(&records).unwrap().contains("SliceCursor"));
}

#[test]
fn promotes_array_derived_locals_to_explicit_slices() {
    let records = generate(array_pointer_fixture());
    assert!(
        function(&records, "read_array")
            .annotated_skeleton
            .contains("let mut p: &[i32] = todo!();")
    );
    assert!(
        function(&records, "write_array")
            .annotated_skeleton
            .contains("let mut p: &mut [i32] = todo!();")
    );
}

fn scalar_box_fixture() -> &'static str {
    "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; } pub unsafe fn alloc() -> *mut i32 { let p: *mut i32 = malloc(core::mem::size_of::<i32>()); *p = 7; p }"
}

#[test]
fn selects_scalar_box_types_from_ownership_analysis() {
    let records = generate(scalar_box_fixture());
    let alloc = function(&records, "alloc");
    assert_eq!(alloc.target_signature, "pub unsafe fn alloc() -> Box<i32>");
    assert!(
        alloc
            .annotated_skeleton
            .contains("let mut p: Box<i32> = todo!();")
    );
}

fn boxed_slice_fixture() -> &'static str {
    "unsafe extern \"C\" { fn calloc(count: usize, size: usize) -> *mut i32; } pub unsafe fn alloc_array() -> *mut i32 { let p: *mut i32 = calloc(4, core::mem::size_of::<i32>()); *p.offset(1) = 7; p }"
}

#[test]
fn selects_boxed_slice_types_from_ownership_and_fatness() {
    let records = generate(boxed_slice_fixture());
    let alloc = function(&records, "alloc_array");
    assert_eq!(
        alloc.target_signature,
        "pub unsafe fn alloc_array() -> Box<[i32]>"
    );
    assert!(
        alloc
            .annotated_skeleton
            .contains("let mut p: Box<[i32]> = todo!();")
    );
}

#[test]
fn adds_named_lifetimes_for_returned_borrows() {
    let records = generate(
        "pub unsafe fn id(x: *mut i32) -> *mut i32 { x } pub unsafe fn wrap(y: *mut i32) -> *mut i32 { id(y) }",
    );
    assert_eq!(
        function(&records, "id").target_signature,
        "pub unsafe fn id<'a>(mut x: &'a mut i32) -> &'a mut i32"
    );
    assert_eq!(
        function(&records, "wrap").target_signature,
        "pub unsafe fn wrap<'a>(mut y: &'a mut i32) -> &'a mut i32"
    );
}

#[test]
fn preserves_nullable_returned_borrow_relationships() {
    let records = generate(
        "pub unsafe fn maybe(flag: bool, x: *mut i32) -> *mut i32 { if flag { x } else { core::ptr::null_mut() } } pub unsafe fn maybe_local(flag: bool, x: *mut i32) -> *mut i32 { let r = if flag { x } else { core::ptr::null_mut() }; r }",
    );
    for path in ["maybe", "maybe_local"] {
        let signature = &function(&records, path).target_signature;
        assert!(
            signature.contains("mut x: Option<&'a mut i32>"),
            "{signature}"
        );
        assert!(signature.contains("-> Option<&'a mut i32>"), "{signature}");
    }
    assert!(
        function(&records, "maybe_local")
            .annotated_skeleton
            .contains("let mut r: Option<&mut i32>")
    );
}

fn raw_pointer_fixture() -> &'static str {
    "unsafe extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; } static mut SLOT: *mut *mut i32 = core::ptr::null_mut(); pub unsafe fn void_address(out: *mut core::ffi::c_void) -> usize { out as usize } pub unsafe fn keep_alias_raw(a: *mut i32, b: *mut i32) -> *mut i32 { *a = 1; *b = 2; a } pub unsafe fn drive_alias(p: *mut i32) -> *mut i32 { keep_alias_raw(p, p) } pub unsafe fn main_0() { let _ = drive_alias(malloc(core::mem::size_of::<i32>()) as *mut i32); } pub unsafe fn alias_caller() -> i32 { let mut x = 7i32; let p: *mut i32 = &mut x; *p = 8; *p } pub unsafe fn global_escape() { let p: *mut *mut i32 = malloc(core::mem::size_of::<*mut i32>()) as *mut *mut i32; *p = core::ptr::null_mut(); SLOT = p; }"
}

#[test]
fn keeps_required_raw_pointers_raw() {
    let records = generate(raw_pointer_fixture());
    assert!(
        function(&records, "void_address")
            .target_signature
            .contains("*mut core::ffi::c_void"),
        "{}",
        function(&records, "void_address").target_signature
    );
    assert!(
        function(&records, "keep_alias_raw")
            .target_signature
            .contains("mut a: *mut i32, mut b: *mut i32"),
        "{}",
        function(&records, "keep_alias_raw").target_signature
    );
    assert!(
        function(&records, "global_escape")
            .annotated_skeleton
            .contains("let mut p: *mut *mut i32")
    );
}

fn named_types_fixture() -> &'static str {
    "pub struct S { pub p: *mut i32 } pub union U { pub p: *const i32, pub bits: usize } pub enum E { Ptr(*mut i32), Empty } pub type Alias = *const i32; pub static mut GLOBAL: *mut i32 = core::ptr::null_mut(); pub const NIL: *const i32 = core::ptr::null(); pub unsafe fn use_all(s: S, u: U, e: E, a: Alias) -> usize { let _ = (s, u, e, a, GLOBAL, NIL); 0 }"
}

#[test]
fn does_not_change_named_type_or_global_declarations() {
    let records = generate(named_types_fixture());
    assert!(type_record(&records, "S").definition.contains("*mut i32"));
    assert!(
        type_record(&records, "Alias")
            .definition
            .contains("*const i32")
    );
    assert_eq!(
        function(&records, "use_all").signature_dependencies,
        [0, 1, 2, 3]
    );
    assert_eq!(
        function(&records, "use_all").dependencies,
        [0, 1, 2, 3, 4, 5]
    );
}

fn local_struct_demotion_fixture() -> &'static str {
    "#[repr(C)] pub struct Tree { root_id: i32 } pub unsafe fn tree_print_helper(tree: *mut Tree, root_id: i32) { (*tree).root_id = root_id; } pub unsafe fn caller(tree: *mut Tree) { tree_print_helper(tree, (*tree).root_id); }"
}

#[test]
fn uses_initial_decisions_before_rewriter_fallback_demotion() {
    let source = local_struct_demotion_fixture();
    let records = generate(source);
    assert_eq!(
        function(&records, "tree_print_helper").target_signature,
        "pub unsafe fn tree_print_helper(mut tree: &mut crate::Tree, mut root_id: i32)"
    );
    let rewritten = run_compiler_on_str(source, |tcx| {
        pointer_replacer::replace_local_borrows(&pointer_replacer::Config::default(), tcx).0
    })
    .unwrap();
    assert!(rewritten.contains("fn tree_print_helper(mut tree: *mut crate::Tree, root_id: i32)"));
}

#[test]
fn all_simple_locals_receive_final_explicit_target_types() {
    type ExpectedLocal<'a> = (&'a str, &'a str, &'a str);
    type Fixture<'a> = (&'a str, &'a [ExpectedLocal<'a>]);

    let fixtures: [Fixture<'_>; 7] = [
        (
            scalar_reference_fixture(),
            &[
                ("write_local", "x", "i32"),
                ("write_local", "p", "&mut i32"),
                ("read_local", "x", "i32"),
                ("read_local", "p", "&i32"),
            ],
        ),
        (optional_reference_fixture(), &[]),
        (
            array_pointer_fixture(),
            &[
                ("read_array", "p", "&[i32]"),
                ("write_array", "p", "&mut [i32]"),
            ],
        ),
        (scalar_box_fixture(), &[("alloc", "p", "Box<i32>")]),
        (boxed_slice_fixture(), &[("alloc_array", "p", "Box<[i32]>")]),
        (
            raw_pointer_fixture(),
            &[
                ("alias_caller", "x", "i32"),
                ("alias_caller", "p", "&mut i32"),
                ("global_escape", "p", "*mut *mut i32"),
            ],
        ),
        (
            optional_box_fixture(),
            &[("foo", "p", "Box<i32>"), ("foo", "q", "Option<Box<i32>>")],
        ),
    ];
    for (source, expected) in fixtures {
        let actual = simple_local_types(source);
        let expected = expected
            .iter()
            .map(|(path, name, ty)| ((*path).to_owned(), (*name).to_owned(), (*ty).to_owned()))
            .collect::<Vec<_>>();
        assert_eq!(actual, expected, "source: {source}");
    }
}

#[test]
fn skeleton_pointer_result_contains_no_cursor_variant() {
    for source in [
        scalar_reference_fixture(),
        array_pointer_fixture(),
        raw_pointer_fixture(),
        named_types_fixture(),
        tools_cursor_fixture(),
    ] {
        run_compiler_on_str(source, |tcx| {
            let decisions = initial_pointer_decisions(
                &pointer_replacer::Config::default(),
                PointerDecisionOptions {
                    assume_nonnegative_offsets: true,
                },
                tcx,
            );
            assert!(
                decisions
                    .signatures
                    .data
                    .values()
                    .flat_map(|decision| {
                        decision
                            .input_decs
                            .iter()
                            .copied()
                            .chain(std::iter::once(decision.output_dec))
                    })
                    .flatten()
                    .all(|kind| !matches!(kind, PtrKind::SliceCursor(_)))
            );
            assert!(
                decisions
                    .bindings
                    .values()
                    .all(|kind| !matches!(kind, PtrKind::SliceCursor(_)))
            );
        })
        .unwrap();
        let json = skeletons_to_json(&generate(source)).unwrap();
        assert!(!json.contains("SliceCursor"));
        assert!(!json.contains("slice_cursor"));
    }
}

fn optional_box_fixture() -> &'static str {
    "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; } pub unsafe fn owned_id(mut p: *mut i32) -> *mut i32 { p } pub unsafe fn foo() -> *mut i32 { let p: *mut i32 = malloc(core::mem::size_of::<i32>()); *p = 7; let q: *mut i32 = owned_id(p); q }"
}

#[test]
fn selects_optional_boxes_at_local_call_boundaries() {
    let records = generate(optional_box_fixture());
    assert_eq!(
        function(&records, "owned_id").target_signature,
        "pub unsafe fn owned_id(mut p: Option<Box<i32>>) -> Option<Box<i32>>"
    );
    assert!(
        function(&records, "foo")
            .target_signature
            .ends_with("-> Option<Box<i32>>")
    );
    let skeleton = &function(&records, "foo").annotated_skeleton;
    assert!(skeleton.contains("let mut p: Box<i32>"));
    assert!(skeleton.contains("let mut q: Option<Box<i32>>"));
}

fn tools_cursor_fixture() -> &'static str {
    "pub unsafe fn read_at(p: *const i32, offset: isize) -> i32 { let nonnegative = offset.max(0); *p.offset(nonnegative) } pub unsafe fn caller(offset: isize) -> i32 { let values = [10i32, 20, 30, 40]; read_at(values.as_ptr(), offset) }"
}

#[test]
fn tools_mode_disables_conservative_slice_cursors_without_changing_crat_default() {
    let source = tools_cursor_fixture();
    let default_kind = run_compiler_on_str(source, |tcx| {
        let result = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions::default(),
            tcx,
        );
        let did = result
            .signatures
            .data
            .keys()
            .copied()
            .find(|did| tcx.item_name(did.to_def_id()) == Symbol::intern("read_at"))
            .unwrap();
        result.signatures.data[&did].input_decs[0].unwrap()
    })
    .unwrap();
    assert_eq!(default_kind, PtrKind::SliceCursor(false));
    let tools_kind = run_compiler_on_str(source, |tcx| {
        let result = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        assert!(
            result
                .bindings
                .values()
                .all(|kind| !matches!(kind, PtrKind::SliceCursor(_)))
        );
        let did = result
            .signatures
            .data
            .keys()
            .copied()
            .find(|did| tcx.item_name(did.to_def_id()) == Symbol::intern("read_at"))
            .unwrap();
        result.signatures.data[&did].input_decs[0].unwrap()
    })
    .unwrap();
    assert_eq!(tools_kind, PtrKind::Slice(false));
    let records = generate(source);
    assert_eq!(
        function(&records, "read_at").target_signature,
        "pub unsafe fn read_at(mut p: &[i32], mut offset: isize) -> i32"
    );
    assert!(
        function(&records, "read_at")
            .annotated_skeleton
            .contains("let mut nonnegative: isize")
    );
    assert!(
        function(&records, "caller")
            .annotated_skeleton
            .contains("let mut values: [i32; 4]")
    );
}

#[test]
fn comprehensive_fixture_emits_consistent_records() {
    let records = generate(comprehensive_fixture());
    assert_paths(
        &records,
        &[
            ("N", ItemKindName::Const),
            ("model::Point", ItemKindName::Struct),
            ("model::Bits", ItemKindName::Union),
            ("model::Mode", ItemKindName::Enum),
            ("model::PointPtr", ItemKindName::TyAlias),
            ("model::ORIGIN", ItemKindName::Static),
            ("model::read", ItemKindName::Fn),
            ("helper", ItemKindName::Fn),
        ],
    );
    assert_eq!(type_record(&records, "model::Mode").dependencies, [0]);
    assert_eq!(function(&records, "model::read").dependencies, [1, 7]);
    assert_eq!(function(&records, "helper").dependencies, [7]);
    assert!(
        function(&records, "model::read")
            .target_signature
            .contains("p: &crate::model::Point")
    );
    assert_eq!(
        labels(&function(&records, "model::read").annotated_skeleton),
        [0, 1, 2, 3]
    );
    assert_eq!(
        labels(&function(&records, "helper").annotated_skeleton),
        [0, 1, 2, 3, 4, 5]
    );
}

#[test]
fn source_and_target_parameters_and_simple_locals_are_mutable() {
    let source = r#"pub unsafe fn f(input: i32, mut existing: i32) -> i32 {
    let value = input;
    let mut total: i32 = existing;
    total += value;
    total
}"#;
    let record = function(&generate(source), "f").clone();
    assert_skeleton(
        source,
        "f",
        r#"pub unsafe fn f(mut input: i32, mut existing: i32) -> i32 {
    let mut value: i32 = input;
    let mut total: i32 = existing;
    total += value;
    total
}"#,
    );
    assert_eq!(
        record.source_signature,
        "pub unsafe fn f(mut input: i32, mut existing: i32) -> i32"
    );
    assert_eq!(record.source_signature, record.target_signature);
    assert!(record.annotated_source.contains("let mut value = input;"));
    assert!(
        record
            .annotated_source
            .contains("let mut total: i32 = existing;")
    );
}

#[test]
fn wildcards_remain_wildcards() {
    let source = r#"pub unsafe fn f(pair: (i32, i32)) {
    let (_, value) = pair;
    let _ = value;
}"#;
    let record = function(&generate(source), "f").clone();
    assert_skeleton(
        source,
        "f",
        r#"pub unsafe fn f(mut pair: (i32, i32)) {
    let (_, mut value) = pair;
    let _ = value;
}"#,
    );
    assert_eq!(
        record.source_signature,
        "pub unsafe fn f(mut pair: (i32, i32))"
    );
    assert_eq!(record.source_signature, record.target_signature);
    assert!(
        record
            .annotated_source
            .contains("let (_, mut value) = pair;")
    );
    assert!(record.annotated_source.contains("let _ = value;"));
}

#[test]
fn non_ref_bindings_are_normalized_and_reference_modes_are_preserved() {
    let source = r#"enum E { Pair(i32, i32), Struct { x: i32 }, Unit }
enum Choice { Left(i32), Right(i32) }
pub unsafe fn f(
    pair: (i32, i32),
    mut opt: Option<(i32, i32)>,
    values: [(i32, i32); 1],
    value: E,
    choice: Choice,
) {
    let ref borrowed = pair;
    let _ = borrowed;
    let whole @ (a, b) = pair;
    let Some((c, d)): Option<(i32, i32)> = opt else { return; };
    if let Some((e, f)) = opt { let _ = e + f; }
    while let Some((g, h)) = opt { opt = None; let _ = g + h; }
    for (i, j) in values { let _ = i + j; }
    match value {
        E::Pair(k, l) => { let _ = k + l; }
        E::Struct { x: m } => { let _ = m; }
        E::Unit => {}
    }
    match choice {
        Choice::Left(n) | Choice::Right(n) => { let _ = n; }
    }
    let _ = (whole, a, b, c, d);
}"#;
    let records = generate(source);
    let record = function(&records, "f");
    for rendering in [&record.annotated_source, &record.annotated_skeleton] {
        for fragment in [
            "mut pair: (i32, i32)",
            "mut opt: Option<(i32, i32)>",
            "mut values: [(i32, i32); 1]",
            "mut value: E",
            "mut choice: Choice",
            "let ref borrowed",
            "let mut whole @ (mut a, mut b)",
            "Some((mut c, mut d))",
            "Some((mut e, mut f))",
            "Some((mut g, mut h))",
            "for (mut i, mut j)",
            "E::Pair(mut k, mut l)",
            "x: mut m",
            "Choice::Left(mut n) | Choice::Right(mut n)",
        ] {
            assert!(
                rendering.contains(fragment),
                "missing `{fragment}` in {rendering}"
            );
        }
        assert!(!rendering.contains("let ref mut borrowed"));
    }

    let ref_mut = generate(
        "pub unsafe fn ref_mut_source(mut value: i32) { let ref mut borrowed = value; let _ = borrowed; }",
    );
    let ref_mut = function(&ref_mut, "ref_mut_source");
    assert!(ref_mut.annotated_source.contains("let ref mut borrowed"));
    assert!(ref_mut.annotated_skeleton.contains("let ref mut borrowed"));
}

#[test]
fn safe_source_functions_get_unsafe_target_headers() {
    let records = generate(
        "pub fn safe(input: i32) -> i32 { let value = input; value } pub unsafe fn already_unsafe(input: i32) -> i32 { input }",
    );
    let safe = function(&records, "safe");
    assert_eq!(safe.source_signature, "pub fn safe(mut input: i32) -> i32");
    assert_eq!(
        safe.target_signature,
        "pub unsafe fn safe(mut input: i32) -> i32"
    );
    assert!(safe.annotated_source.starts_with("pub fn safe"));
    assert!(safe.annotated_source.contains("let mut value = input;"));
    assert!(safe.annotated_skeleton.starts_with("pub unsafe fn safe"));
    assert!(
        safe.annotated_skeleton
            .contains("let mut value: i32 = input;")
    );
    assert_eq!(
        function(&records, "already_unsafe").source_signature,
        "pub unsafe fn already_unsafe(mut input: i32) -> i32"
    );
    assert_eq!(
        function(&records, "already_unsafe").target_signature,
        "pub unsafe fn already_unsafe(mut input: i32) -> i32"
    );
}

#[test]
fn every_free_function_named_main_is_omitted_without_body_inspection() {
    let records = generate(
        r#"pub fn main() { let ignored = 1; core::mem::drop(ignored); }
unsafe fn main_0() -> core::ffi::c_int { 0 }
mod nested {
    pub fn main() { panic!("also omitted"); }
    pub unsafe fn helper() -> i32 { 1 }
}
mod raw {
    pub fn r#main() {}
    pub unsafe fn helper() -> i32 { 2 }
}"#,
    );
    assert_paths(
        &records,
        &[
            ("main_0", ItemKindName::Fn),
            ("nested::helper", ItemKindName::Fn),
            ("raw::helper", ItemKindName::Fn),
        ],
    );
}

#[test]
fn supported_main_0_forms_are_generated_with_the_fixed_argv_override() {
    let zero = generate(
        "unsafe fn main_0() -> core::ffi::c_int { 0 } pub fn main() { unsafe { ::std::process::exit(main_0() as i32) } }",
    );
    assert_eq!(zero.len(), 1);
    assert_eq!(
        function(&zero, "main_0").target_signature,
        "unsafe fn main_0() -> core::ffi::c_int"
    );

    let source = r#"unsafe fn main_0(
    mut argc: core::ffi::c_int,
    mut argv: *mut *mut core::ffi::c_char,
) -> core::ffi::c_int {
    if argc > 0 { **argv as core::ffi::c_int } else { 0 }
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
    let records = generate(source);
    assert_eq!(records.len(), 1);
    let main_0 = function(&records, "main_0");
    assert_eq!(
        main_0.source_signature,
        "unsafe fn main_0(mut argc: core::ffi::c_int,\nmut argv: *mut *mut core::ffi::c_char) -> core::ffi::c_int"
    );
    assert_eq!(
        main_0.target_signature,
        "unsafe fn main_0(mut argc: core::ffi::c_int, mut argv: &mut [&mut [i8]])\n-> core::ffi::c_int"
    );

    let parenthesized = generate(
        r#"unsafe fn main_0(
    argc: (core::ffi::c_int),
    argv: (*mut *mut core::ffi::c_char),
) -> (core::ffi::c_int) {
    0
}"#,
    );
    assert!(
        function(&parenthesized, "main_0")
            .target_signature
            .contains("mut argv: &mut [&mut [i8]]")
    );

    let arity_only = generate(
        r#"unsafe fn main_0(first: usize, second: *const u8) -> bool {
            let _ = (first, second);
            false
        }"#,
    );
    let target = &function(&arity_only, "main_0").target_signature;
    assert!(target.contains("mut first: usize"));
    assert!(target.contains("mut second: &mut [&mut [i8]]"));
    assert!(target.contains("-> bool"));
}

#[test]
fn generation_is_deterministic_across_compiler_runs() {
    let first = generate(comprehensive_fixture());
    let second = generate(comprehensive_fixture());
    assert_eq!(first, second);
    assert_eq!(
        skeletons_to_json(&first).unwrap(),
        skeletons_to_json(&second).unwrap()
    );
}

#[test]
fn record_paths_and_dependency_ids_are_self_consistent() {
    let records = generate(
        "mod a { pub struct T; pub const C: i32 = 1; pub unsafe fn make(_value: T) -> i32 { C } } mod b { pub struct T; pub unsafe fn call(x: crate::a::T) -> i32 { crate::a::make(x) } } pub unsafe fn root(x: a::T, _other: b::T) -> i32 { b::call(x) }",
    );
    assert_paths(
        &records,
        &[
            ("a::T", ItemKindName::Struct),
            ("a::C", ItemKindName::Const),
            ("a::make", ItemKindName::Fn),
            ("b::T", ItemKindName::Struct),
            ("b::call", ItemKindName::Fn),
            ("root", ItemKindName::Fn),
        ],
    );
    assert_eq!(function(&records, "a::make").dependencies, [0, 1]);
    assert_eq!(function(&records, "b::call").dependencies, [0, 2]);
    assert_eq!(function(&records, "root").dependencies, [0, 3, 4]);
    assert!(
        records
            .iter()
            .flat_map(ItemRecord::dependencies)
            .all(|id| *id < records.len() as u64)
    );
}

#[test]
fn empty_statement_error_prevents_partial_output() {
    let error = generate_error(
        "pub unsafe fn valid() -> i32 { 1 } pub unsafe fn invalid(flag: bool) { if flag { ; } }",
    );
    assert_eq!(error.kind, GenerationErrorKind::EmptyStatement);
    assert_eq!(error.function_path, "invalid");
}

#[test]
fn existing_function_records_and_helpers_adopt_the_final_shape() {
    let source = r#"pub unsafe fn scalar(value: i32) -> i32 {
    value + 1
}"#;
    let records = generate(source);
    assert_eq!(
        skeletons_to_json(&records).unwrap(),
        r#"[
  {
    "id": 0,
    "path": "scalar",
    "kind": "Fn",
    "name": "scalar",
    "annotated_source": "pub unsafe fn scalar(mut value: i32) -> i32 {\n    #[proctor(0)]\n    (value + 1)\n}",
    "annotated_skeleton": "pub unsafe fn scalar(mut value: i32) -> i32 {\n    #[proctor(0)]\n    (value + 1)\n}",
    "source_signature": "pub unsafe fn scalar(mut value: i32) -> i32",
    "target_signature": "pub unsafe fn scalar(mut value: i32) -> i32",
    "needs_transformation": false,
    "statements_requiring_transformation": [],
    "foreign_function_names": [],
    "signature_dependencies": [],
    "dependencies": []
  }
]"#
    );
}

#[test]
fn collects_per_function_names_sorted_deduplicated_and_resolved() {
    let records = generate(
        r#"#![feature(extern_types)]

unsafe extern "C" {
    fn strlen(text: *const core::ffi::c_char) -> usize;
    fn free(pointer: *mut core::ffi::c_void);
    fn transitive_foreign(value: i32) -> i32;
    fn unused_foreign(value: i32) -> i32;
    static FOREIGN_COUNTER: i32;
    type ForeignOpaque;
}

use strlen as c_strlen;

pub unsafe extern "C" fn local_abi(value: i32) -> i32 {
    transitive_foreign(value)
}

pub mod parser {
    pub unsafe fn scan(
        pointer: *mut core::ffi::c_void,
        text: *const core::ffi::c_char,
    ) -> usize {
        crate::free(pointer);
        let first = crate::c_strlen(text);
        let second = crate::strlen(text);
        let _ = crate::FOREIGN_COUNTER;
        let _: Option<*mut crate::ForeignOpaque> = None;
        let _ = crate::local_abi(first as i32);
        first + second + core::mem::size_of::<usize>()
    }

    pub unsafe fn release(pointer: *mut core::ffi::c_void) {
        crate::free(pointer);
        crate::free(pointer);
    }

    pub unsafe fn scalar(value: i32) -> i32 {
        crate::local_abi(value)
    }
}"#,
    );

    assert_eq!(
        function(&records, "local_abi").foreign_function_names,
        ["transitive_foreign"]
    );
    assert_eq!(
        function(&records, "parser::scan").foreign_function_names,
        ["free", "strlen"]
    );
    assert_eq!(
        function(&records, "parser::release").foreign_function_names,
        ["free"]
    );
    assert!(
        function(&records, "parser::scalar")
            .foreign_function_names
            .is_empty()
    );

    assert!(function(&records, "local_abi").dependencies.is_empty());
    assert_eq!(function(&records, "parser::scan").dependencies, [0]);
    assert!(
        function(&records, "parser::release")
            .dependencies
            .is_empty()
    );
    assert_eq!(function(&records, "parser::scalar").dependencies, [0]);
}

#[test]
fn handles_link_name_callable_reference_and_dependency_metadata() {
    let records = generate(
        r#"unsafe extern "C" {
    #[link_name = "strlen"]
    fn c_strlen(text: *const core::ffi::c_char) -> usize;
}

pub unsafe fn length(text: *const core::ffi::c_char) -> usize {
    c_strlen(text)
}

pub unsafe fn hold_callable() {
    let callable = c_strlen;
    let _ = callable;
}"#,
    );
    assert_eq!(
        function(&records, "length").foreign_function_names,
        ["c_strlen"]
    );
    assert_eq!(
        function(&records, "hold_callable").foreign_function_names,
        ["c_strlen"]
    );

    let dependency_records = generate(
        r#"extern crate libc;

pub unsafe fn dependency_free(pointer: *mut libc::c_void) {
    libc::free(pointer);
}"#,
    );
    assert_eq!(
        function(&dependency_records, "dependency_free").foreign_function_names,
        ["free"]
    );
}

#[test]
fn amendment_2_preserves_scalar_statements_and_metadata() {
    let source = r#"
pub unsafe fn scalar(mut x: i32, y: i32, z: i32) -> i32 {
    let sum = y + z;
    x = sum * 2;
    return x;
}
"#;
    let records = generate(source);
    let function = function(&records, "scalar");
    assert!(!function.needs_transformation);
    assert!(function.statements_requiring_transformation.is_empty());
    let skeleton = compact(&function.annotated_skeleton);
    assert!(skeleton.contains("y + z"));
    assert!(skeleton.contains("sum * 2"));
    assert!(skeleton.contains("return x"));
    assert!(!skeleton.contains("todo!"));
}

#[test]
fn amendment_2_mixed_control_has_recursive_parent_disposition() {
    let source = r#"
pub unsafe fn mixed(mut p: *mut i32, flag: bool, y: i32, z: i32) -> i32 {
    if flag {
        let sum = y + z;
        *p = sum;
    } else {
        let difference = y - z;
        return difference;
    }
    return y + z;
}
"#;
    let records = generate(source);
    let function = function(&records, "mixed");
    assert!(function.needs_transformation);
    assert_eq!(function.statements_requiring_transformation, [0, 2]);
    let skeleton = compact(&function.annotated_skeleton);
    assert!(skeleton.contains("if todo!()"));
    assert!(skeleton.contains("y + z"));
    assert!(skeleton.contains("y - z"));
    assert!(skeleton.contains("return difference"));
}

#[test]
fn amendment_2_callable_policy_is_conservative() {
    let source = r#"
pub fn local(value: i32) -> i32 { value + 1 }
pub unsafe fn caller(values: &[i32], left: i32, right: i32) -> i32 {
    let a = local(left);
    let b = std::cmp::max(a, right);
    let d = values.len() as i32;
    let e = values[0];
    b + d + e
}
"#;
    let records = generate(source);
    let caller = function(&records, "caller");
    assert_eq!(
        caller.statements_requiring_transformation,
        Vec::<u32>::new()
    );
}

#[test]
fn amendment_2_unsafe_nonlocal_calls_macros_and_raw_pointers_transform() {
    let source = r#"
pub unsafe fn cases(values: &[i32], pointer: *mut i32, value: i32) -> i32 {
    let unchecked = *values.get_unchecked(0);
    println!("{value}");
    let is_null = pointer.is_null();
    let scalar = value + 1;
    scalar + unchecked + is_null as i32
}
"#;
    let records = generate(source);
    let function = function(&records, "cases");
    assert_eq!(function.statements_requiring_transformation, [0, 1, 2]);
}

#[test]
fn amendment_2_opens_local_adts_but_not_external_representation() {
    let source = r#"
pub struct Leaf { pub pointer: *mut i32 }
pub struct Middle { pub leaf: Leaf }
pub unsafe fn values(
    mut local: Middle,
    other_local: Middle,
    mut integers: Vec<i32>,
    other_integers: Vec<i32>,
    mut pointers: Vec<*mut i32>,
    other_pointers: Vec<*mut i32>,
) {
    local = other_local;
    integers = other_integers;
    pointers = other_pointers;
}
"#;
    let records = generate(source);
    let function = function(&records, "values");
    assert_eq!(function.statements_requiring_transformation, [0, 2]);
    assert!(compact(&function.annotated_skeleton).contains("other_integers"));
}

#[test]
fn amendment_2_restricted_conditionals_preserve_or_stay_opaque() {
    let source = r#"
pub unsafe fn conditional(mut x: i32, flag: bool, pointer: *mut i32) -> i32 {
    x = 1 + if flag { 2 } else { 3 };
    x = 1 + if flag { *pointer } else { 3 };
    x
}
"#;
    let records = generate(source);
    let function = function(&records, "conditional");
    assert_eq!(function.statements_requiring_transformation, [1]);
    let skeleton = compact(&function.annotated_skeleton);
    assert!(skeleton.contains("1 + if flag"));
    assert_eq!(skeleton.matches("todo!()").count(), 1);
}

#[test]
fn amendment_2_future_field_change_marks_containing_values_sensitive() {
    let source = r#"
#[derive(Clone, Copy)]
pub struct FutureField { pub value: i32 }
pub unsafe fn move_future(mut left: FutureField, right: FutureField) -> i32 {
    left = right;
    left.value + right.value
}
"#;
    let ordinary = generate(source);
    assert!(
        function(&ordinary, "move_future")
            .statements_requiring_transformation
            .is_empty()
    );
    let changed = run_compiler_on_str(source, |tcx| {
        let item = tcx
            .hir_node_by_def_id(local_def("FutureField", tcx))
            .expect_item();
        let hir::ItemKind::Struct(_, _, variant) = item.kind else { unreachable!() };
        let mut overrides = PreservationDecisionOverrides::default();
        overrides
            .changed_fields
            .insert(variant.fields()[0].def_id.to_def_id());
        make_skeletons_with_preservation_overrides(source, tcx, &overrides).unwrap()
    })
    .unwrap();
    assert_eq!(
        function(&changed, "move_future").statements_requiring_transformation,
        [0, 1]
    );
}

#[test]
fn amendment_2_changed_local_signature_forces_call_transformation() {
    let source = r#"
pub unsafe fn scalar_callee(value: i32) -> i32 { value + 1 }
pub unsafe fn scalar_caller(value: i32) -> i32 { scalar_callee(value) }
"#;
    assert!(
        function(&generate(source), "scalar_caller")
            .statements_requiring_transformation
            .is_empty()
    );
    let changed = run_compiler_on_str(source, |tcx| {
        let mut overrides = PreservationDecisionOverrides::default();
        overrides
            .changed_local_signatures
            .insert(local_def("scalar_callee", tcx));
        make_skeletons_with_preservation_overrides(source, tcx, &overrides).unwrap()
    })
    .unwrap();
    assert_eq!(
        function(&changed, "scalar_caller").statements_requiring_transformation,
        [0]
    );
}

#[test]
fn amendment_2_missing_ast_mapping_and_changed_binding_decision_are_conservative() {
    let scalar_source = r#"
pub unsafe fn scalar(y: i32, z: i32) -> i32 {
    let sum = y + z;
    sum
}
"#;
    run_compiler_on_str(scalar_source, |tcx| {
        struct YExpression {
            id: Option<NodeId>,
        }

        impl<'ast> rustc_ast::visit::Visitor<'ast> for YExpression {
            fn visit_expr(&mut self, expression: &'ast Expr) {
                if let ExprKind::Path(None, path) = &expression.kind
                    && path
                        .segments
                        .last()
                        .is_some_and(|segment| segment.ident.name.as_str() == "y")
                {
                    self.id = Some(expression.id);
                }
                rustc_ast::visit::walk_expr(self, expression);
            }
        }

        let mut surface = utils::ast::parse_crate(scalar_source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let mut ast_to_hir = mapper.ast_to_hir;
        let mut finder = YExpression { id: None };
        finder.visit_crate(&surface);
        ast_to_hir.local_map.remove(&finder.id.unwrap());
        let ItemKind::Fn(box function) = &surface.items[0].kind else { unreachable!() };
        let decisions = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        assert!(!statement_is_preservable(
            &function.body.as_ref().unwrap().stmts[0],
            &ast_to_hir,
            &decisions,
            &PreservationDecisionOverrides::default(),
            tcx,
        ));
    })
    .unwrap();

    let pointer_source = r#"
pub unsafe fn observe(pointer: *mut i32) -> bool {
    let is_null = pointer.is_null();
    is_null
}
"#;
    run_compiler_on_str(pointer_source, |tcx| {
        let mut surface = utils::ast::parse_crate(pointer_source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let ast_to_hir = mapper.ast_to_hir;
        let ItemKind::Fn(box function) = &surface.items[0].kind else { unreachable!() };
        let parameter_hir = ast_to_hir.local_map[&function.sig.decl.inputs[0].pat.id];
        let mut decisions = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        decisions.bindings.insert(parameter_hir, PtrKind::Ref(true));
        let overrides = PreservationDecisionOverrides::default();
        let checker = HirPreservationCheck {
            tcx,
            decisions: &decisions,
            preservation_overrides: &overrides,
            owner: parameter_hir.owner,
            direct_callee: None,
            preservable: true,
            sensitive_types: FxHashMap::default(),
            visiting_types: FxHashSet::default(),
        };
        assert!(checker.binding_changes(parameter_hir));
        assert!(!statement_is_preservable(
            &function.body.as_ref().unwrap().stmts[0],
            &ast_to_hir,
            &decisions,
            &overrides,
            tcx,
        ));
    })
    .unwrap();
}

#[test]
fn amendment_2_type_sensitivity_substitutes_generic_local_adts_and_terminates() {
    let source = r#"
pub struct Wrap<T> { pub value: T }
pub struct Recursive<T> {
    pub next: Option<Box<Recursive<T>>>,
    pub value: T,
}
pub unsafe fn generic_values(
    scalar: Wrap<i32>,
    pointer: Wrap<*mut i32>,
    recursive_scalar: Recursive<i32>,
    recursive_pointer: Recursive<*mut i32>,
) {}
"#;
    run_compiler_on_str(source, |tcx| {
        let owner = local_def("generic_values", tcx);
        let decisions = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        let overrides = PreservationDecisionOverrides::default();
        let mut checker = HirPreservationCheck {
            tcx,
            decisions: &decisions,
            preservation_overrides: &overrides,
            owner: hir::OwnerId { def_id: owner },
            direct_callee: None,
            preservable: true,
            sensitive_types: FxHashMap::default(),
            visiting_types: FxHashSet::default(),
        };
        let signature = tcx.fn_sig(owner).instantiate_identity().skip_binder();
        assert_eq!(
            signature
                .inputs()
                .iter()
                .map(|ty| checker.type_is_sensitive(*ty))
                .collect::<Vec<_>>(),
            [false, true, false, true]
        );
    })
    .unwrap();
}

#[test]
fn amendment_2_unresolved_projection_is_transformation_sensitive() {
    let source = r#"
pub trait HasItem { type Item; }
pub unsafe fn projection<T: HasItem>(value: T::Item) { let _ = value; }
"#;
    run_compiler_on_str(source, |tcx| {
        let owner = local_def("projection", tcx);
        let decisions = initial_pointer_decisions(
            &pointer_replacer::Config::default(),
            PointerDecisionOptions {
                assume_nonnegative_offsets: true,
            },
            tcx,
        );
        let overrides = PreservationDecisionOverrides::default();
        let mut checker = HirPreservationCheck {
            tcx,
            decisions: &decisions,
            preservation_overrides: &overrides,
            owner: hir::OwnerId { def_id: owner },
            direct_callee: None,
            preservable: true,
            sensitive_types: FxHashMap::default(),
            visiting_types: FxHashSet::default(),
        };
        let signature = tcx.fn_sig(owner).instantiate_identity().skip_binder();
        assert!(checker.type_is_sensitive(signature.inputs()[0]));
    })
    .unwrap();
}

#[test]
fn amendment_2_exact_scalar_call_and_pointer_matrix() {
    let scalar = generate(
        r#"pub unsafe fn arithmetic(mut x: i32, y: i32, z: i32) -> (i64, [i32; 2]) {
            x = y + z;
            x += 1;
            let wide = x as i64;
            let pair = (wide, [y, z]);
            return pair;
        }"#,
    );
    assert!(
        function(&scalar, "arithmetic")
            .statements_requiring_transformation
            .is_empty()
    );

    let calls = generate(
        r#"unsafe extern "C" { fn foreign_abs(value: i32) -> i32; }
        pub fn local(value: i32) -> i32 { value + 1 }
        pub unsafe fn local_unsafe(value: i32) -> i32 { value + 1 }
        pub unsafe fn safe_calls(values: &[i32], left: i32, right: i32) -> i32 {
            let a = local(left);
            let b = std::cmp::max(a, right);
            let c = values.len() as i32;
            let d = values[0];
            b + c + d
        }
        pub unsafe fn local_call(value: i32) -> i32 { local_unsafe(value) }
        pub unsafe fn foreign_call(value: i32) -> i32 { foreign_abs(value) }
        pub unsafe fn unsafe_calls(values: &[i32]) -> (i32, char) {
            let value = *values.get_unchecked(0);
            let character = char::from_u32_unchecked(65);
            (value, character)
        }"#,
    );
    for path in ["safe_calls", "local_call"] {
        assert!(
            function(&calls, path)
                .statements_requiring_transformation
                .is_empty(),
            "{path}"
        );
    }
    assert_eq!(
        function(&calls, "foreign_call").statements_requiring_transformation,
        [0]
    );
    assert_eq!(
        function(&calls, "unsafe_calls").statements_requiring_transformation,
        [0, 1]
    );

    let pointers = generate(
        r#"pub unsafe fn pointer_uses(mut left: *mut i32, right: *const i32) -> i32 {
            *left = *right;
            let alias: *const i32 = left;
            let value = *alias;
            value
        }"#,
    );
    assert_eq!(
        function(&pointers, "pointer_uses").statements_requiring_transformation,
        [0, 1, 2]
    );
}

#[test]
fn amendment_2_exact_declaration_generic_and_macro_matrix() {
    let declarations = generate(
        r#"pub unsafe fn declarations() {
            let scalar: i32;
            let pointer: *mut i32;
            scalar = 1;
            pointer = core::ptr::null_mut();
            let _ = scalar;
            let _ = pointer;
        }"#,
    );
    assert_eq!(
        function(&declarations, "declarations").statements_requiring_transformation,
        [1, 3, 5]
    );
    let nested = generate(
        r#"pub unsafe fn nested(
            mut a: Option<Box<(*mut i32, [usize; 2])>>,
            b: Option<Box<(*mut i32, [usize; 2])>>,
        ) { a = b; }
        pub unsafe fn type_arguments() -> usize {
            let marker = core::marker::PhantomData::<*mut i32>;
            let size = core::mem::size_of::<*mut i32>();
            let _ = marker;
            size
        }"#,
    );
    assert_eq!(
        function(&nested, "nested").statements_requiring_transformation,
        [0]
    );
    assert_eq!(
        function(&nested, "type_arguments").statements_requiring_transformation,
        [0, 1, 2]
    );
    let macros = generate(
        r#"pub unsafe fn macros(value: i32) {
            println!("{value}");
            assert!(value > 0);
            let nested = 1 + dbg!(value);
            let _ = nested;
        }"#,
    );
    assert_eq!(
        function(&macros, "macros").statements_requiring_transformation,
        [0, 1, 2]
    );
}

#[test]
fn amendment_2_exact_local_adt_matrix_opens_alias_union_and_recursive_fields() {
    let records = generate(
        r#"pub struct Leaf { pub pointer: *mut i32 }
        pub struct Middle { pub leaf: Leaf }
        pub enum Choice { Empty, Value(Middle) }
        pub union Storage {
            pub leaf: core::mem::ManuallyDrop<Leaf>,
            pub integer: i64,
        }
        pub struct Link {
            pub next: Option<Box<Link>>,
            pub leaf: Leaf,
        }
        pub type Alias = Choice;
        pub unsafe fn move_values(
            mut a: Middle,
            b: Middle,
            mut c: Alias,
            d: Alias,
            mut s: Storage,
            t: Storage,
            mut link: Link,
            other: Link,
        ) {
            a = b;
            c = d;
            s = t;
            link = other;
        }"#,
    );
    assert_eq!(
        function(&records, "move_values").statements_requiring_transformation,
        [0, 1, 2, 3]
    );
}

#[test]
fn amendment_2_exact_patterns_control_and_unsafe_storage_matrix() {
    let patterns = generate(
        r#"pub unsafe fn patterns(
            pair: (i32, i32),
            pointer_pair: Option<(*mut i32, i32)>,
        ) -> i32 {
            let (left, right) = pair;
            let Some((pointer, value)) = pointer_pair else {
                return left + right;
            };
            match value {
                n if n > 0 => { let copy = n; copy }
                _ => { let _ = pointer; 0 }
            }
        }"#,
    );
    assert_eq!(
        function(&patterns, "patterns").statements_requiring_transformation,
        [1, 3, 6]
    );

    let safe_control = generate(
        r#"pub unsafe fn control(flag: bool, left: i32, right: i32) -> i32 {
            if flag {
                let value = left + right;
                return value;
            } else {
                return left - right;
            }
        }"#,
    );
    assert!(
        function(&safe_control, "control")
            .statements_requiring_transformation
            .is_empty()
    );

    let storage = generate(
        r#"pub static mut GLOBAL: i32 = 0;
        pub union Scalar { pub signed: i32, pub unsigned: u32 }
        pub unsafe fn storage(value: Scalar) -> i32 {
            GLOBAL = 1;
            let local = value.signed;
            local + GLOBAL
        }"#,
    );
    assert_eq!(
        function(&storage, "storage").statements_requiring_transformation,
        [0, 1, 2]
    );

    let control_patterns = generate(
        r#"pub unsafe fn control_patterns(
            mut current: Option<*mut i32>,
            values: [*mut i32; 1],
        ) {
            if let Some(pointer) = current {
                let _ = pointer;
            }
            while let Some(pointer) = current.take() {
                let _ = pointer;
            }
            for pointer in values {
                let _ = pointer;
            }
        }"#,
    );
    assert_eq!(
        function(&control_patterns, "control_patterns").statements_requiring_transformation,
        [0, 1, 2, 3, 4, 5]
    );

    let mixed_storage = generate(
        r#"pub union Mixed {
            pub pointer: *mut i32,
            pub integer: i32,
        }
        pub unsafe fn mixed_storage(value: Mixed) -> i32 {
            value.integer
        }"#,
    );
    assert_eq!(
        function(&mixed_storage, "mixed_storage").statements_requiring_transformation,
        [0]
    );
}

#[test]
fn amendment_2_exact_validator_fixture_has_recursive_parent_disposition() {
    let records = generate(
        r#"pub unsafe fn validate_me(flag: bool, mut pointer: *mut i32) -> i32 {
            let scalar = 1 + 2;
            if flag {
                let nested = 3 + 4;
                *pointer = nested;
            } else {
                return scalar;
            }
            scalar
        }"#,
    );
    assert_eq!(
        function(&records, "validate_me").statements_requiring_transformation,
        [1, 3]
    );
}

#[test]
fn amendment_2_exact_unsupported_callable_and_desugar_matrix() {
    let functions = generate(
        r#"pub unsafe fn local(value: i32) -> i32 { value + 1 }
        pub unsafe fn invoke(callback: unsafe fn(i32) -> i32, value: i32) -> i32 {
            callback(value)
        }
        pub unsafe fn hold_callable() {
            let callable = local;
            let _ = callable;
        }
        pub unsafe fn closure(value: i32) -> i32 {
            let add = |other: i32| value + other;
            add(1)
        }
        pub unsafe fn question(value: Option<i32>) -> Option<i32> {
            let inner = value?;
            Some(inner + 1)
        }"#,
    );
    assert_eq!(
        function(&functions, "invoke").statements_requiring_transformation,
        [0]
    );
    assert_eq!(
        function(&functions, "hold_callable").statements_requiring_transformation,
        [0, 1]
    );
    assert_eq!(
        function(&functions, "closure").statements_requiring_transformation,
        [0, 1]
    );
    assert_eq!(
        function(&functions, "question").statements_requiring_transformation,
        [0]
    );

    let assembly = generate(
        r#"pub unsafe fn assembly(mut value: u64) -> u64 {
            core::arch::asm!("/* {0} */", inout(reg) value);
            value
        }"#,
    );
    assert_eq!(
        function(&assembly, "assembly").statements_requiring_transformation,
        [0]
    );
}
