use super::*;

fn source(code: &str) -> String {
    format!(
        r#"
#![allow(dead_code, non_snake_case, non_upper_case_globals, unused_imports)]
{code}
"#
    )
}

fn transform(code: &str) -> Result<String, PrepareError> {
    let code = source(code);
    utils::compilation::run_compiler_on_str(&code, prepare)
        .unwrap()
        .map(|result| result.code)
}

fn transform_result(code: &str) -> Result<PreparationResult, PrepareError> {
    let code = source(code);
    utils::compilation::run_compiler_on_str(&code, prepare).unwrap()
}

fn transform_and_compile(code: &str) -> String {
    let result = transform(code).unwrap();
    utils::compilation::run_compiler_on_str(&result, utils::type_check).unwrap();
    result
}

fn canonical(code: &str) -> String {
    let code = source(code);
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let mut krate = utils::ast::expanded_ast(tcx);
        utils::ast::remove_unnecessary_items_from_ast(&mut krate);
        pprust::crate_to_string_for_macros(&krate)
    })
    .unwrap()
}

fn assert_prepares_to(input: &str, expected: &str) {
    let actual = transform_and_compile(input);
    assert_eq!(compact(&actual), compact(&canonical(expected)));
}

fn compact(code: &str) -> String {
    code.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[test]
fn preparation_result_publishes_in_dependency_order() {
    let events = std::cell::RefCell::new(vec![]);
    let source = std::path::Path::new("/work/project/lib.rs");
    let manifest = std::path::Path::new("/work/project/Cargo.toml");
    PreparationResult {
        code: "prepared".to_owned(),
        requires_proctor_libc: false,
    }
    .publish_with(
        source,
        manifest,
        |_, _, _| {
            events.borrow_mut().push("dependency");
            Ok(())
        },
        |path, code| {
            events.borrow_mut().push("write");
            assert_eq!(path, source);
            assert_eq!(code, "prepared");
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(*events.borrow(), ["write"]);

    events.borrow_mut().clear();
    PreparationResult {
        code: "prepared".to_owned(),
        requires_proctor_libc: true,
    }
    .publish_with(
        source,
        manifest,
        |path, name, minimum| {
            events.borrow_mut().push("dependency");
            assert_eq!(path, manifest);
            assert_eq!(name, "proctor-libc");
            assert_eq!(minimum, "0.3.0");
            Ok(())
        },
        |path, code| {
            events.borrow_mut().push("write");
            assert_eq!(path, source);
            assert_eq!(code, "prepared");
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(*events.borrow(), ["dependency", "write"]);
}

#[test]
fn preparation_result_stops_before_or_after_write_at_the_failing_boundary() {
    let events = std::cell::RefCell::new(vec![]);
    let source = std::path::Path::new("/work/project/lib.rs");
    let manifest = std::path::Path::new("/work/project/Cargo.toml");
    let error = PreparationResult {
        code: "prepared".to_owned(),
        requires_proctor_libc: true,
    }
    .publish_with(
        source,
        manifest,
        |path, name, minimum| {
            events.borrow_mut().push("dependency");
            assert_eq!(path, manifest);
            assert_eq!(name, "proctor-libc");
            assert_eq!(minimum, "0.3.0");
            Err("dependency failed".to_owned())
        },
        |_, _| {
            events.borrow_mut().push("write");
            Ok(())
        },
    )
    .unwrap_err();
    assert!(matches!(
        error,
        PreparationPublishError::Dependency {
            manifest: path,
            cause,
        } if path == manifest && cause == "dependency failed"
    ));
    assert_eq!(*events.borrow(), ["dependency"]);

    events.borrow_mut().clear();
    let error = PreparationResult {
        code: "prepared".to_owned(),
        requires_proctor_libc: true,
    }
    .publish_with(
        source,
        manifest,
        |path, name, minimum| {
            events.borrow_mut().push("dependency");
            assert_eq!(path, manifest);
            assert_eq!(name, "proctor-libc");
            assert_eq!(minimum, "0.3.0");
            Ok(())
        },
        |path, code| {
            events.borrow_mut().push("write");
            assert_eq!(path, source);
            assert_eq!(code, "prepared");
            Err("write failed".to_owned())
        },
    )
    .unwrap_err();
    assert!(matches!(
        error,
        PreparationPublishError::Source {
            source: path,
            cause,
        } if path == source && cause == "write failed"
    ));
    assert_eq!(*events.borrow(), ["dependency", "write"]);
}

#[test]
fn preparation_publication_errors_include_the_affected_path() {
    assert_eq!(
        PreparationPublishError::Dependency {
            manifest: "/work/project/Cargo.toml".into(),
            cause: "Cargo [dependencies] must be a table".to_owned(),
        }
        .to_string(),
        "failed to ensure proctor-libc dependency in /work/project/Cargo.toml: Cargo [dependencies] must be a table"
    );
    assert_eq!(
        PreparationPublishError::Source {
            source: "/work/project/lib.rs".into(),
            cause: "denied".to_owned(),
        }
        .to_string(),
        "failed to write prepared source /work/project/lib.rs: denied"
    );
}

fn count(code: &str, needle: &str) -> usize {
    code.match_indices(needle).count()
}

#[test]
fn wraps_non_block_match_arms_recursively_and_preserves_blocks() {
    assert_prepares_to(
        r#"
fn choose(x: i32, y: i32) -> i32 {
    match x {
        0 => match y { 0 => 1, _ => 2 },
        1 => { let z = y + 1; z },
        _ => unsafe { core::ptr::read(&y) },
    }
}
"#,
        r#"
fn choose(x: i32, y: i32) -> i32 {
    match x {
        0 => { match y { 0 => { 1 }, _ => { 2 } } },
        1 => { let z = y + 1; z },
        _ => unsafe { core::ptr::read(&y) },
    }
}
"#,
    );
}

#[test]
fn preserves_match_arm_metadata_and_wraps_special_expressions() {
    assert_prepares_to(
        r#"
fn choose(x: i32) -> i32 {
    loop {
        match x {
            #[allow(unreachable_code)]
            0 | 1 if x > 0 => break 4,
            _ => break 2,
        }
    }
}
fn constant() -> i32 { match () { _ => const { 2 } } }
fn closure() -> impl Fn() -> i32 { match () { _ => || 3 } }
"#,
        r#"
fn choose(x: i32) -> i32 {
    loop {
        match x {
            #[allow(unreachable_code)]
            0 | 1 if x > 0 => { break 4 },
            _ => { break 2 },
        }
    }
}
fn constant() -> i32 { match () { _ => { const { 2 } } } }
fn closure() -> impl Fn() -> i32 { match () { _ => { || 3 } } }
"#,
    );
}

#[test]
fn wraps_control_parenthesized_and_unit_match_bodies() {
    assert_prepares_to(
        r#"
fn forms(x: i32) -> i32 {
    match x {
        0 => if x == 0 { 1 } else { 2 },
        1 => loop { break 3 },
        2 => (4),
        _ => 5,
    };
    0
}
fn unit(x: i32) { match x { 0 => (), _ => () } }
"#,
        r#"
fn forms(x: i32) -> i32 {
    match x {
        0 => { if x == 0 { 1 } else { 2 } },
        1 => { loop { break 3 } },
        2 => { (4) },
        _ => { 5 },
    };
    0
}
fn unit(x: i32) { match x { 0 => { () }, _ => { () } } }
"#,
    );
}

#[test]
fn normalizes_matches_in_static_const_closure_and_async_owners() {
    assert_prepares_to(
        r#"
static TOP: i32 = match 0 { 0 => 1, _ => 2 };
const C: i32 = match 1 { 1 => 3, _ => 4 };
fn owners() {
    let closure = || match 2 { 2 => 5, _ => 6 };
    let _future = async { match 3 { 3 => 7, _ => 8 } };
    let _ = (closure, C, TOP);
}
"#,
        r#"
static TOP: i32 = match 0 { 0 => { 1 }, _ => { 2 } };
const C: i32 = match 1 { 1 => { 3 }, _ => { 4 } };
fn owners() {
    let closure = || match 2 { 2 => { 5 }, _ => { 6 } };
    let _future = async { match 3 { 3 => { 7 }, _ => { 8 } } };
    let _ = (closure, C, TOP);
}
"#,
    );
}

#[test]
fn maps_await_operands_while_normalizing_async_bodies() {
    assert_prepares_to(
        r#"
fn value(x: i32) {
    let _future = async {
        core::future::ready(match x { 0 => 1, _ => 2 }).await
    };
}
"#,
        r#"
fn value(x: i32) {
    let _future = async {
        core::future::ready(match x { 0 => { 1 }, _ => { 2 } }).await
    };
}
"#,
    );
}

#[test]
fn lifts_nested_statics_in_source_order() {
    assert_prepares_to(
        r#"
fn nested(flag: bool) -> i32 {
    if flag {
        static FIRST: i32 = 1;
        loop { static SECOND: i32 = 2; break FIRST + SECOND; }
    } else {
        static THIRD: i32 = 3;
        THIRD
    }
}
"#,
        r#"
static FIRST: i32 = 1;
static SECOND: i32 = 2;
static THIRD: i32 = 3;
fn nested(flag: bool) -> i32 {
    if flag {
        loop { break FIRST + SECOND; }
    } else {
        THIRD
    }
}
"#,
    );
}

#[test]
fn lifts_closure_async_local_function_and_method_statics_before_owner() {
    assert_prepares_to(
        r#"
struct S;
impl S { fn method() -> i32 { static METHOD: i32 = 4; METHOD } }
fn outer() {
    let closure = || { static CLOSURE: i32 = 1; CLOSURE };
    let future = async { static FUTURE: i32 = 2; FUTURE };
    fn inner() -> i32 { static INNER: i32 = 3; INNER }
    let _ = (closure, future, inner(), S::method());
}
"#,
        r#"
struct S;
static METHOD: i32 = 4;
impl S { fn method() -> i32 { METHOD } }
static CLOSURE: i32 = 1;
static FUTURE: i32 = 2;
static INNER: i32 = 3;
fn outer() {
    let closure = || { CLOSURE };
    let future = async { FUTURE };
    fn inner() -> i32 { INNER }
    let _ = (closure, future, inner(), S::method());
}
"#,
    );
}

#[test]
fn lifts_provided_trait_method_static_before_trait() {
    assert_prepares_to(
        r#"
trait T { fn value() -> i32 { static CELL: i32 = 3; CELL } }
"#,
        r#"
static CELL: i32 = 3;
trait T { fn value() -> i32 { CELL } }
"#,
    );
}

#[test]
fn uses_nearest_module_and_leaves_module_owned_statics() {
    assert_prepares_to(
        r#"
mod left { pub static OWNED: i32 = 0; pub fn f() -> i32 { static CELL: i32 = 1; CELL } }
mod right { pub fn g() -> i32 { static CELL: i32 = 2; CELL } }
fn outer() {
    mod local_module {
        pub static OWNED: i32 = 3;
        pub fn inner() -> i32 { static NESTED: i32 = 4; OWNED + NESTED }
    }
    let _ = local_module::inner();
}
"#,
        r#"
mod left {
    pub static OWNED: i32 = 0;
    static CELL_0: i32 = 1;
    pub fn f() -> i32 { CELL_0 }
}
mod right {
    static CELL_1: i32 = 2;
    pub fn g() -> i32 { CELL_1 }
}
fn outer() {
    mod local_module {
        pub static OWNED: i32 = 3;
        static NESTED: i32 = 4;
        pub fn inner() -> i32 { OWNED + NESTED }
    }
    let _ = local_module::inner();
}
"#,
    );
}

#[test]
fn preserves_mutability_type_initializer_and_non_export_attributes() {
    assert_prepares_to(
        r#"
fn f() -> u32 {
    #[used]
    #[link_section = ".data.demo"]
    static mut CELL: u32 = 7;
    unsafe { CELL += 1; CELL }
}
"#,
        r#"
#[used]
#[link_section = ".data.demo"]
static mut CELL: u32 = 7;
fn f() -> u32 { unsafe { CELL += 1; CELL } }
"#,
    );
}

#[test]
fn value_items_patterns_and_constructors_reserve_names() {
    assert_prepares_to(
        r#"
mod other {
    pub fn FUNCTION() {}
    pub const CONSTANT: i32 = 0;
    pub struct TUPLE(pub i32);
    pub struct UNIT;
    pub enum E { VARIANT, PAYLOAD(i32), RECORD { value: i32 } }
}
fn binders(PARAM: i32) { let LOCAL = PARAM; let _ = LOCAL; }
mod target {
    pub fn f() {
        static FUNCTION: i32 = 1;
        static CONSTANT: i32 = 2;
        static TUPLE: i32 = 3;
        static UNIT: i32 = 4;
        static VARIANT: i32 = 5;
        static PAYLOAD: i32 = 6;
        static RECORD: i32 = 7;
        static PARAM: i32 = 8;
        static LOCAL: i32 = 9;
        let _ = (FUNCTION, CONSTANT, TUPLE, UNIT, VARIANT, PAYLOAD, RECORD, PARAM, LOCAL);
    }
}
"#,
        r#"
mod other {
    pub fn FUNCTION() {}
    pub const CONSTANT: i32 = 0;
    pub struct TUPLE(pub i32);
    pub struct UNIT;
    pub enum E { VARIANT, PAYLOAD(i32), RECORD { value: i32 } }
}
fn binders(PARAM: i32) { let LOCAL = PARAM; let _ = LOCAL; }
mod target {
    static FUNCTION_0: i32 = 1;
    static CONSTANT_0: i32 = 2;
    static TUPLE_0: i32 = 3;
    static UNIT_0: i32 = 4;
    static VARIANT_0: i32 = 5;
    static PAYLOAD_0: i32 = 6;
    static RECORD: i32 = 7;
    static PARAM_0: i32 = 8;
    static LOCAL_0: i32 = 9;
    pub fn f() {
        let _ = (FUNCTION_0, CONSTANT_0, TUPLE_0, UNIT_0, VARIANT_0, PAYLOAD_0, RECORD, PARAM_0, LOCAL_0);
    }
}
"#,
    );
}

#[test]
fn imports_foreign_values_and_const_generics_reserve_names() {
    assert_prepares_to(
        r#"
mod source { pub static ORIGINAL: i32 = 0; }
mod imported { use crate::source::ORIGINAL as ALIAS; }
unsafe extern "C" { static FOREIGN: i32; }
fn generic<const N: usize>() { let _ = N; }
mod target {
    pub fn f() {
        static ALIAS: i32 = 1;
        static FOREIGN: i32 = 2;
        static N: i32 = 3;
        let _ = (ALIAS, FOREIGN, N);
    }
}
"#,
        r#"
mod source { pub static ORIGINAL: i32 = 0; }
mod imported { use crate::source::ORIGINAL as ALIAS; }
unsafe extern "C" { static FOREIGN: i32; }
fn generic<const N: usize>() { let _ = N; }
mod target {
    static ALIAS_0: i32 = 1;
    static FOREIGN_0: i32 = 2;
    static N_0: i32 = 3;
    pub fn f() { let _ = (ALIAS_0, FOREIGN_0, N_0); }
}
"#,
    );
}

#[test]
fn ordinary_glob_imports_reserve_value_names() {
    assert_prepares_to(
        r#"
mod source { pub static GLOB: i32 = 0; }
mod target {
    use crate::source::*;
    pub fn f() -> i32 { static GLOB: i32 = 1; GLOB }
}
"#,
        r#"
mod source { pub static GLOB: i32 = 0; }
mod target {
    use crate::source::*;
    static GLOB_0: i32 = 1;
    pub fn f() -> i32 { GLOB_0 }
}
"#,
    );
}

#[test]
fn local_const_function_and_static_binders_force_exact_renames() {
    assert_prepares_to(
        r#"
fn binders() -> i32 {
    const LOCAL_CONST: i32 = 1;
    fn LOCAL_FN() -> i32 { 2 }
    static LOCAL_STATIC: i32 = 3;
    LOCAL_CONST + LOCAL_FN() + LOCAL_STATIC
}
fn target() -> i32 {
    static LOCAL_CONST: i32 = 4;
    static LOCAL_FN: i32 = 5;
    static LOCAL_STATIC: i32 = 6;
    LOCAL_CONST + LOCAL_FN + LOCAL_STATIC
}
"#,
        r#"
static LOCAL_STATIC_0: i32 = 3;
fn binders() -> i32 {
    const LOCAL_CONST: i32 = 1;
    fn LOCAL_FN() -> i32 { 2 }
    LOCAL_CONST + LOCAL_FN() + LOCAL_STATIC_0
}
static LOCAL_CONST_0: i32 = 4;
static LOCAL_FN_0: i32 = 5;
static LOCAL_STATIC_1: i32 = 6;
fn target() -> i32 { LOCAL_CONST_0 + LOCAL_FN_0 + LOCAL_STATIC_1 }
"#,
    );
}

#[test]
fn every_pattern_binding_form_reserves_its_value_name() {
    assert_prepares_to(
        r#"
struct S { field: i32, rest: i32 }
fn binders(PARAM: i32, (TUPLE, _): (i32, i32), S { field: STRUCT, .. }: S) {
    let LET = 0;
    let [ARRAY, _] = [0, 1];
    if let Some(IF_LET) = Some(1) { let _ = IF_LET; }
    while let Some(WHILE_LET) = None::<i32> { let _ = WHILE_LET; }
    for FOR in 0..1 { let _ = FOR; }
    match Some(1) { Some(MATCH) => { let _ = MATCH; }, None => {} }
    let closure = |CLOSURE: i32| CLOSURE;
    let _ = (PARAM, TUPLE, STRUCT, LET, ARRAY, closure);
}
mod target {
    pub fn f() {
        static PARAM: i32 = 0; static TUPLE: i32 = 1; static STRUCT: i32 = 2;
        static LET: i32 = 3; static ARRAY: i32 = 4; static IF_LET: i32 = 5;
        static WHILE_LET: i32 = 6; static FOR: i32 = 7; static MATCH: i32 = 8;
        static CLOSURE: i32 = 9;
        let _ = (PARAM, TUPLE, STRUCT, LET, ARRAY, IF_LET, WHILE_LET, FOR, MATCH, CLOSURE);
    }
}
"#,
        r#"
struct S { field: i32, rest: i32 }
fn binders(PARAM: i32, (TUPLE, _): (i32, i32), S { field: STRUCT, .. }: S) {
    let LET = 0;
    let [ARRAY, _] = [0, 1];
    if let Some(IF_LET) = Some(1) { let _ = IF_LET; }
    while let Some(WHILE_LET) = None::<i32> { let _ = WHILE_LET; }
    for FOR in 0..1 { let _ = FOR; }
    match Some(1) { Some(MATCH) => { let _ = MATCH; }, None => {} }
    let closure = |CLOSURE: i32| CLOSURE;
    let _ = (PARAM, TUPLE, STRUCT, LET, ARRAY, closure);
}
mod target {
    static PARAM_0: i32 = 0;
    static TUPLE_0: i32 = 1;
    static STRUCT_0: i32 = 2;
    static LET_0: i32 = 3;
    static ARRAY_0: i32 = 4;
    static IF_LET_0: i32 = 5;
    static WHILE_LET_0: i32 = 6;
    static FOR_0: i32 = 7;
    static MATCH_0: i32 = 8;
    static CLOSURE_0: i32 = 9;
    pub fn f() {
        let _ = (PARAM_0, TUPLE_0, STRUCT_0, LET_0, ARRAY_0, IF_LET_0, WHILE_LET_0, FOR_0, MATCH_0, CLOSURE_0);
    }
}
"#,
    );
}

#[test]
fn type_field_associated_and_label_names_do_not_reserve_values() {
    assert_prepares_to(
        r#"
struct BRACED { FIELD: i32 }
type ALIAS = i32;
trait TRAIT { fn METHOD(&self); const ASSOCIATED: i32; }
fn labels() { 'LABEL: loop { break 'LABEL; } }
mod target {
    pub fn f() {
        static BRACED: i32 = 1;
        static FIELD: i32 = 2;
        static ALIAS: i32 = 3;
        static TRAIT: i32 = 4;
        static METHOD: i32 = 5;
        static ASSOCIATED: i32 = 6;
        static LABEL: i32 = 7;
        let _ = (BRACED, FIELD, ALIAS, TRAIT, METHOD, ASSOCIATED, LABEL);
    }
}
"#,
        r#"
struct BRACED { FIELD: i32 }
type ALIAS = i32;
trait TRAIT { fn METHOD(&self); const ASSOCIATED: i32; }
fn labels() { 'LABEL: loop { break 'LABEL; } }
mod target {
    static BRACED: i32 = 1;
    static FIELD: i32 = 2;
    static ALIAS: i32 = 3;
    static TRAIT: i32 = 4;
    static METHOD: i32 = 5;
    static ASSOCIATED: i32 = 6;
    static LABEL: i32 = 7;
    pub fn f() { let _ = (BRACED, FIELD, ALIAS, TRAIT, METHOD, ASSOCIATED, LABEL); }
}
"#,
    );
}

#[test]
fn macro_and_lifetime_names_do_not_force_a_rename() {
    assert_prepares_to(
        r#"
macro_rules! VALUE { () => { 1_i32 } }
fn f<'VALUE>() -> i32 { static VALUE: i32 = VALUE!(); VALUE }
"#,
        r#"
macro_rules! VALUE { () => { 1_i32 } }
static VALUE: i32 = 1_i32;
fn f<'VALUE>() -> i32 { VALUE }
"#,
    );
}

#[test]
fn suffix_allocation_uses_complete_original_set_and_discovery_order() {
    assert_prepares_to(
        r#"
fn reserves(NAME: i32, NAME_0: i32, NAME_2: i32) { let _ = (NAME, NAME_0, NAME_2); }
fn first() -> i32 { static NAME: i32 = 10; NAME }
fn second() -> i32 { static NAME: i32 = 20; NAME }
"#,
        r#"
fn reserves(NAME: i32, NAME_0: i32, NAME_2: i32) { let _ = (NAME, NAME_0, NAME_2); }
static NAME_1: i32 = 10;
fn first() -> i32 { NAME_1 }
static NAME_3: i32 = 20;
fn second() -> i32 { NAME_3 }
"#,
    );
}

#[test]
fn suffix_allocation_is_deterministic_across_compilations() {
    let code = r#"
fn reserve(NAME: i32, NAME_0: i32) { let _ = (NAME, NAME_0); }
fn first() -> i32 { static NAME: i32 = 1; NAME }
fn second() -> i32 { static NAME: i32 = 2; NAME }
"#;
    assert_eq!(
        compact(&transform(code).unwrap()),
        compact(&transform(code).unwrap())
    );
}

#[test]
fn suffixes_complete_raw_and_unicode_names() {
    assert_prepares_to(
        r#"
fn reserve(NAME_0: i32, r#type: i32, π: i32) { let _ = (NAME_0, r#type, π); }
fn first() -> i32 { static NAME_0: i32 = 1; NAME_0 }
fn second() -> i32 { static r#type: i32 = 2; r#type }
fn third() -> i32 { static π: i32 = 3; π }
"#,
        r#"
fn reserve(NAME_0: i32, r#type: i32, π: i32) { let _ = (NAME_0, r#type, π); }
static NAME_0_0: i32 = 1;
fn first() -> i32 { NAME_0_0 }
static type_0: i32 = 2;
fn second() -> i32 { type_0 }
static π_0: i32 = 3;
fn third() -> i32 { π_0 }
"#,
    );
}

#[test]
fn prelude_names_reserve_originals_without_rewriting_prelude_paths() {
    assert_prepares_to(
        r#"
fn probe() -> Option<i32> { let value = None; drop(0_i32); value }
fn f() -> i32 { static None: i32 = 1; static drop: i32 = 2; None + drop }
"#,
        r#"
fn probe() -> Option<i32> { let value = None; drop(0_i32); value }
static None_0: i32 = 1;
static drop_0: i32 = 2;
fn f() -> i32 { None_0 + drop_0 }
"#,
    );
}

#[test]
fn rejects_disabled_implicit_prelude_before_mapping() {
    let cases = [
        r#"
#![no_implicit_prelude]
#![allow(dead_code, non_snake_case, non_upper_case_globals)]
fn f() -> i32 { static None: i32 = 1; static drop: i32 = 2; None + drop }
"#,
        r#"
#![allow(dead_code, non_snake_case, non_upper_case_globals)]
#[no_implicit_prelude]
mod isolated { pub fn f() -> i32 { static CELL: i32 = 1; CELL } }
"#,
    ];
    for code in cases {
        let error = utils::compilation::run_compiler_on_str(code, prepare)
            .unwrap()
            .unwrap_err();
        assert_eq!(
            error,
            PrepareError::UnsupportedPrelude {
                construct: "`#[no_implicit_prelude]`".to_owned(),
            }
        );
        assert_eq!(
            error.to_string(),
            "unsupported prelude configuration: `#[no_implicit_prelude]`"
        );
    }
}

#[test]
fn no_std_uses_compiler_selected_prelude_names() {
    assert_prepares_to(
        r#"
#![no_std]
fn probe() -> Option<i32> { let value = None; drop(0_i32); value }
fn f() -> i32 { static None: i32 = 1; static drop: i32 = 2; None + drop }
"#,
        r#"
#![no_std]
fn probe() -> Option<i32> { let value = None; drop(0_i32); value }
static None_0: i32 = 1;
static drop_0: i32 = 2;
fn f() -> i32 { None_0 + drop_0 }
"#,
    );
}

#[test]
fn rejects_source_authored_prelude_before_mapping() {
    let code = r#"
#![feature(prelude_import)]
#![allow(dead_code, non_snake_case, non_upper_case_globals)]
mod custom_prelude { pub static NAME_0: i32 = 0; }
#[prelude_import]
use crate::custom_prelude::*;
fn reserve(NAME: i32) { let _ = NAME; }
fn f() -> i32 { static NAME: i32 = 1; NAME }
"#;
    let error = utils::compilation::run_compiler_on_str(code, prepare)
        .unwrap()
        .unwrap_err();
    assert_eq!(
        error,
        PrepareError::UnsupportedPrelude {
            construct: "source-authored `#[prelude_import]`".to_owned(),
        }
    );
    assert_eq!(
        error.to_string(),
        "unsupported prelude configuration: source-authored `#[prelude_import]`"
    );
}

#[test]
fn rejects_direct_async_functions_before_ast_to_hir_mapping() {
    let cases = [
        ("async fn free() {}", "free"),
        ("struct S; impl S { async fn method() {} }", "method"),
        ("trait T { async fn provided() {} }", "provided"),
        ("trait T { async fn required(); }", "required"),
        ("fn outer() { async fn local() {} }", "local"),
    ];
    for (code, expected_name) in cases {
        let error = transform(code).unwrap_err();
        assert_eq!(
            error,
            PrepareError::UnsupportedAsyncFunction {
                function_name: expected_name.to_owned(),
            }
        );
        assert_eq!(
            error.to_string(),
            format!("direct async function `{expected_name}` is unsupported")
        );
    }
}

#[test]
fn rewrites_only_uses_resolved_to_the_moved_static() {
    let result = compact(&transform_and_compile(
        r#"
mod a { pub fn f() -> i32 { static X: i32 = 1; X } }
mod b { pub static X: i32 = 2; pub fn g() -> i32 { X } }
fn h(X: i32) -> i32 { X }
"#,
    ));
    assert!(result.contains("mod a { static X_0: i32 = 1; pub fn f() -> i32 { X_0 } }"));
    assert!(result.contains("mod b { pub static X: i32 = 2; pub fn g() -> i32 { X } }"));
    assert!(result.contains("fn h(X: i32) -> i32 { X }"));
}

#[test]
fn rewrites_references_between_renamed_lifted_statics() {
    let result = compact(&transform_and_compile(
        r#"
fn reserve(CELL: i32, REFERENCE: i32) { let _ = (CELL, REFERENCE); }
fn f() -> &'static i32 {
    static CELL: i32 = 1;
    static REFERENCE: &i32 = &CELL;
    REFERENCE
}
"#,
    ));
    assert!(result.contains(
        "static CELL_0: i32 = 1; static REFERENCE_0: &i32 = &CELL_0; fn f() -> &'static i32 { REFERENCE_0 }"
    ));
}

#[test]
fn rewrites_reads_writes_raw_references_and_expanded_address_macros() {
    assert_prepares_to(
        r#"
fn reserve(CELL: i32) { let _ = CELL; }
fn f() {
    static mut CELL: i32 = 0;
    unsafe {
        let read = CELL;
        CELL = read + 1;
        let raw_const = &raw const CELL;
        let raw_mut = &raw mut CELL;
        let expanded = core::ptr::addr_of!(CELL);
        let _ = (raw_const, raw_mut, expanded);
    }
}
"#,
        r#"
fn reserve(CELL: i32) { let _ = CELL; }
static mut CELL_0: i32 = 0;
fn f() {
    unsafe {
        let read = CELL_0;
        CELL_0 = read + 1;
        let raw_const = &raw const CELL_0;
        let raw_mut = &raw mut CELL_0;
        let expanded = &raw const CELL_0;
        let _ = (raw_const, raw_mut, expanded);
    }
}
"#,
    );
}

#[cfg(target_arch = "x86_64")]
#[test]
fn rewrites_inline_asm_static_symbol_by_identity() {
    let result = compact(&transform_and_compile(
        r#"
use core::arch::asm;
fn reserve(CELL: i32) { let _ = CELL; }
fn f() {
    static CELL: i32 = 1;
    unsafe { asm!("/* {0} */", sym CELL); }
}
"#,
    ));
    assert!(result.contains("static CELL_0: i32 = 1"));
    assert!(result.contains("sym CELL_0"));
}

#[test]
fn allows_module_and_lifted_static_dependencies() {
    let result = compact(&transform_and_compile(
        r#"
type Word = usize;
const START: Word = 3;
const fn make() -> Word { START }
fn f() -> &'static Word {
    static VALUE: Word = make();
    static REFERENCE: &Word = &VALUE;
    REFERENCE
}
"#,
    ));
    assert!(
        result.contains("static VALUE: Word = make(); static REFERENCE: &Word = &VALUE; fn f()")
    );
}

#[test]
fn allows_definitions_nested_inside_the_moved_initializer() {
    assert_prepares_to(
        r#"
fn f() -> i32 {
    static CELL: i32 = {
        const N: i32 = 1;
        struct Local;
        impl Local { const VALUE: i32 = 2; }
        const fn make() -> i32 { 3 }
        N + Local::VALUE + make()
    };
    CELL
}
"#,
        r#"
static CELL: i32 = {
    const N: i32 = 1;
    struct Local;
    impl Local { const VALUE: i32 = 2; }
    const fn make() -> i32 { 3 }
    N + Local::VALUE + make()
};
fn f() -> i32 { CELL }
"#,
    );
}

#[test]
fn rejects_function_scoped_const_dependency() {
    let error = transform(
        r#"
fn f() -> usize {
    const N: usize = 4;
    static DATA: [u8; N] = [0; N];
    DATA.len()
}
"#,
    )
    .unwrap_err();
    let PrepareError::ScopedDependency {
        static_name,
        dependency_name,
        ..
    } = error
    else {
        panic!("unexpected error: {error}")
    };
    assert_eq!(static_name, "DATA");
    assert_eq!(dependency_name, "N");
}

#[test]
fn rejects_scoped_type_constructor_function_and_module_dependencies() {
    let cases = [
        (
            r#"fn f() { struct Local { value: i32 } static DATA: Local = Local { value: 1 }; let _ = DATA.value; }"#,
            "Local",
        ),
        (
            r#"fn f() { type Local = i32; static DATA: Local = 1; let _ = DATA; }"#,
            "Local",
        ),
        (
            r#"fn f() -> i32 { const fn local() -> i32 { 1 } static DATA: i32 = local(); DATA }"#,
            "local",
        ),
        (
            r#"fn f() -> i32 { mod local { pub const N: i32 = 1; } static DATA: i32 = local::N; DATA }"#,
            "local",
        ),
    ];
    for (code, expected_dependency) in cases {
        let error = transform(code).unwrap_err();
        let PrepareError::ScopedDependency {
            static_name,
            dependency_name,
            ..
        } = error
        else {
            panic!("unexpected error: {error}")
        };
        assert_eq!(static_name, "DATA");
        assert_eq!(dependency_name, expected_dependency);
    }
}

#[test]
fn rejects_function_scoped_explicit_and_glob_import_dependencies() {
    for import in ["use crate::source::N as LOCAL_N;", "use crate::source::*;"] {
        let name = if import.contains("LOCAL_N") {
            "LOCAL_N"
        } else {
            "N"
        };
        let code = format!(
            r#"
mod source {{ pub const N: usize = 2; }}
fn f() -> usize {{
    {import}
    static DATA: [u8; {name}] = [0; {name}];
    DATA.len()
}}
"#
        );
        let error = transform(&code).unwrap_err();
        assert!(matches!(error, PrepareError::ScopedDependency { .. }));
        assert!(error.to_string().contains(name), "{error}");
    }
}

#[test]
fn rejects_qualified_scoped_aliases_and_reports_the_binding_segment() {
    enum ExpectedBinding {
        Import,
        TypeAlias,
    }
    let cases = [
        (
            r#"
mod source { pub mod namespace { pub const N: usize = 2; } }
fn f() -> usize {
    use crate::source::namespace as local;
    static DATA: [u8; local::N] = [0; local::N];
    DATA.len()
}
"#,
            "local",
            ExpectedBinding::Import,
        ),
        (
            r#"
struct Holder;
impl Holder { const N: usize = 2; }
fn f() -> usize {
    use crate::Holder as Local;
    static DATA: [u8; Local::N] = [0; Local::N];
    DATA.len()
}
"#,
            "Local",
            ExpectedBinding::Import,
        ),
        (
            r#"
mod source { pub mod namespace { pub const N: usize = 2; } }
mod exports { pub use crate::source::namespace as local; }
fn f() -> usize {
    use crate::exports::*;
    static DATA: [u8; local::N] = [0; local::N];
    DATA.len()
}
"#,
            "local",
            ExpectedBinding::Import,
        ),
        (
            r#"
struct Holder;
impl Holder { const N: usize = 2; }
fn f() -> usize {
    type Local = Holder;
    static DATA: [u8; Local::N] = [0; Local::N];
    DATA.len()
}
"#,
            "Local",
            ExpectedBinding::TypeAlias,
        ),
    ];
    for (code, expected_dependency, expected_binding) in cases {
        let code = source(code);
        utils::compilation::run_compiler_on_str(&code, |tcx| {
            let mut krate = utils::ast::expanded_ast(tcx);
            let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
            let mut discovery = Discovery::new(tcx, &ast_to_hir);
            discovery.discover_crate(&krate);
            assert!(discovery.error.is_none());

            let expected_id = match expected_binding {
                ExpectedBinding::Import => {
                    discovery
                        .local_imports
                        .iter()
                        .find(|import| import.name.as_str() == expected_dependency)
                        .unwrap()
                        .import_def_id
                }
                ExpectedBinding::TypeAlias => {
                    struct AliasFinder {
                        node_id: Option<ast::NodeId>,
                    }
                    impl<'ast> visit::Visitor<'ast> for AliasFinder {
                        fn visit_item(&mut self, item: &'ast ast::Item) {
                            if let ast::ItemKind::TyAlias(box ast::TyAlias { ident, .. }) =
                                &item.kind
                                && ident.name.as_str() == "Local"
                            {
                                self.node_id = Some(item.id);
                                return;
                            }
                            visit::walk_item(self, item);
                        }
                    }
                    let mut finder = AliasFinder { node_id: None };
                    finder.visit_crate(&krate);
                    ast_to_hir.global_map[&finder.node_id.unwrap()]
                }
            };
            let error = validate_dependencies(
                &krate,
                &discovery.lifts,
                &discovery.local_imports,
                &ast_to_hir,
                tcx,
            )
            .unwrap_err();
            let display = error.to_string();
            let PrepareError::ScopedDependency {
                static_name,
                dependency_def_id,
                dependency_name,
                ..
            } = error
            else {
                panic!("unexpected error: {error}")
            };
            assert_eq!(static_name, "DATA");
            assert_eq!(dependency_name, expected_dependency);
            assert_eq!(dependency_def_id, expected_id);
            assert_eq!(
                display,
                format!("local static `DATA` depends on scoped binding `{expected_dependency}`")
            );
        })
        .unwrap();
    }
}

#[test]
fn identical_nested_import_reports_the_nearest_binding_definition() {
    let code = source(
        r#"
mod source { pub mod namespace { pub const N: usize = 2; } }
fn f() -> usize {
    use crate::source::namespace as local;
    {
        use crate::source::namespace as local;
        static DATA: [u8; local::N] = [0; local::N];
        DATA.len()
    }
}
"#,
    );
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let mut krate = utils::ast::expanded_ast(tcx);
        let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
        let mut discovery = Discovery::new(tcx, &ast_to_hir);
        discovery.discover_crate(&krate);
        assert!(discovery.error.is_none());
        let lift = &discovery.lifts[0];
        let matching = discovery
            .local_imports
            .iter()
            .filter(|import| import.name.as_str() == "local")
            .collect::<Vec<_>>();
        assert_eq!(matching.len(), 2);
        let inner = matching
            .iter()
            .find(|import| Some(import.scope) == lift.scopes.last().copied())
            .unwrap();
        let outer = matching
            .iter()
            .find(|import| import.import_def_id != inner.import_def_id)
            .unwrap();
        let error = validate_dependencies(
            &krate,
            &discovery.lifts,
            &discovery.local_imports,
            &ast_to_hir,
            tcx,
        )
        .unwrap_err();
        let PrepareError::ScopedDependency {
            dependency_def_id,
            dependency_name,
            ..
        } = error
        else {
            panic!("unexpected error: {error}")
        };
        assert_eq!(dependency_name, "local");
        assert_eq!(dependency_def_id, inner.import_def_id);
        assert_ne!(dependency_def_id, outer.import_def_id);
    })
    .unwrap();
}

#[test]
fn scoped_import_error_identifies_the_import_definition() {
    let code = source(
        r#"
mod source { pub mod namespace { pub const N: usize = 2; } }
fn f() -> usize {
    use crate::source::namespace as local;
    static DATA: [u8; local::N] = [0; local::N];
    DATA.len()
}
"#,
    );
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let mut krate = utils::ast::expanded_ast(tcx);
        validate_supported_input(&krate).unwrap();
        let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
        let mut discovery = Discovery::new(tcx, &ast_to_hir);
        discovery.discover_crate(&krate);
        assert!(discovery.error.is_none());
        let import = discovery
            .local_imports
            .iter()
            .find(|import| import.name.as_str() == "local")
            .unwrap();
        let error = validate_dependencies(
            &krate,
            &discovery.lifts,
            &discovery.local_imports,
            &ast_to_hir,
            tcx,
        )
        .unwrap_err();
        let PrepareError::ScopedDependency {
            dependency_def_id,
            dependency_name,
            ..
        } = error
        else {
            panic!("unexpected error: {error}")
        };
        assert_eq!(dependency_def_id, import.import_def_id);
        assert_eq!(dependency_name, "local");
    })
    .unwrap();
}

#[test]
fn fully_qualified_dependency_ignores_unrelated_local_import() {
    transform_and_compile(
        r#"
mod source { pub const N: usize = 2; }
fn f() -> usize {
    use crate::source::N as UNUSED;
    static DATA: [u8; crate::source::N] = [0; crate::source::N];
    DATA.len()
}
"#,
    );
}

#[test]
fn same_target_import_in_a_sibling_scope_is_not_a_dependency() {
    assert_prepares_to(
        r#"
mod local { pub const N: usize = 2; }
fn f() -> usize {
    { use crate::local as local; let _ = local::N; }
    { static DATA: [u8; local::N] = [0; local::N]; DATA.len() }
}
"#,
        r#"
mod local { pub const N: usize = 2; }
static DATA: [u8; local::N] = [0; local::N];
fn f() -> usize {
    { use crate::local as local; let _ = local::N; }
    { DATA.len() }
}
"#,
    );
}

#[test]
fn one_invalid_static_rejects_the_complete_unchanged_ast() {
    let code = source(
        r#"
fn good(x: i32) -> i32 {
    static GOOD: i32 = 1;
    match x { 0 => GOOD, _ => 2 }
}
fn bad() -> usize {
    const N: usize = 2;
    static BAD: [u8; N] = [0; N];
    BAD.len()
}
"#,
    );
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let mut krate = utils::ast::expanded_ast(tcx);
        validate_supported_input(&krate).unwrap();
        let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
        let before = pprust::crate_to_string_for_macros(&krate);
        let mut discovery = Discovery::new(tcx, &ast_to_hir);
        discovery.discover_crate(&krate);
        assert!(discovery.error.is_none());
        let error = validate_dependencies(
            &krate,
            &discovery.lifts,
            &discovery.local_imports,
            &ast_to_hir,
            tcx,
        )
        .unwrap_err();
        let PrepareError::ScopedDependency {
            static_name,
            dependency_name,
            ..
        } = error
        else {
            panic!("unexpected error: {error}")
        };
        assert_eq!(static_name, "BAD");
        assert_eq!(dependency_name, "N");
        assert_eq!(before, pprust::crate_to_string_for_macros(&krate));
    })
    .unwrap();
    let error = utils::compilation::run_compiler_on_str(&code, prepare)
        .unwrap()
        .unwrap_err();
    assert!(matches!(
        error,
        PrepareError::ScopedDependency {
            static_name,
            dependency_name,
            ..
        } if static_name == "BAD" && dependency_name == "N"
    ));
}

#[test]
fn compiler_rejection_remains_distinct_from_prepare_rejection() {
    for code in [
        "fn f(value: i32) -> i32 { static DATA: i32 = value; DATA }",
        "fn f<const N: usize>() -> usize { static DATA: [u8; N] = [0; N]; DATA.len() }",
    ] {
        assert!(utils::compilation::run_compiler_on_str(code, prepare).is_err());
    }
    assert!(matches!(
        utils::compilation::run_compiler_on_str("#![no_implicit_prelude]", prepare).unwrap(),
        Err(PrepareError::UnsupportedPrelude { .. })
    ));
}

#[test]
fn missing_definition_and_use_mappings_are_structured_errors() {
    let code = source(
        r#"
fn isalpha(c: i32) -> i32 { c }
fn reserve(CELL: i32) { let _ = CELL; }
fn f(c: i32) -> i32 { static CELL: i32 = 1; match c { 0 => isalpha(c) + CELL, _ => c } }
"#,
    );
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let mut krate = utils::ast::expanded_ast(tcx);
        let mut ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
        let mut discovery = Discovery::new(tcx, &ast_to_hir);
        discovery.discover_crate(&krate);
        assert!(discovery.error.is_none());
        let lift = discovery.lifts[0].clone();
        let lifts = discovery.lifts.clone();
        drop(discovery);
        let before = pprust::crate_to_string_for_macros(&krate);

        let use_span = ast_to_hir
            .path_span_to_res
            .iter()
            .find_map(|(span, resolution)| {
                matches!(
                    resolution,
                    Res::Def(DefKind::Static { .. }, definition)
                        if definition.as_local() == Some(lift.def_id)
                )
                .then_some(*span)
            })
            .unwrap();
        ast_to_hir.path_span_to_res.remove(&use_span);
        let error = validate_use_mappings(&krate, &lifts, &ast_to_hir, tcx).unwrap_err();
        assert_eq!(
            error,
            PrepareError::MissingMapping {
                construct: "use of local static `CELL`".to_owned(),
            }
        );
        assert_eq!(
            error.to_string(),
            "missing compiler mapping for use of local static `CELL`"
        );
        assert_eq!(before, pprust::crate_to_string_for_macros(&krate));
    })
    .unwrap();

    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let mut krate = utils::ast::expanded_ast(tcx);
        let mut ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
        let mut initial_discovery = Discovery::new(tcx, &ast_to_hir);
        initial_discovery.discover_crate(&krate);
        let static_node = initial_discovery.lifts[0].node_id;
        drop(initial_discovery);
        let before = pprust::crate_to_string_for_macros(&krate);
        ast_to_hir.global_map.remove(&static_node);
        let mut discovery = Discovery::new(tcx, &ast_to_hir);
        discovery.discover_crate(&krate);
        let error = discovery.error.unwrap();
        assert_eq!(
            error,
            PrepareError::MissingMapping {
                construct: "local static `CELL`".to_owned(),
            }
        );
        assert_eq!(
            error.to_string(),
            "missing compiler mapping for local static `CELL`"
        );
        assert_eq!(before, pprust::crate_to_string_for_macros(&krate));
    })
    .unwrap();
}

#[test]
fn preparation_errors_return_no_partially_rewritten_result() {
    let scoped = r#"
fn isalpha(c: i32) -> i32 { c }
fn combined(c: i32) -> usize {
    const N: usize = 2;
    static DATA: [u8; N] = [0; N];
    match c { 0 => (isalpha(c) as usize) + DATA.len(), _ => DATA.len() }
}
"#;
    assert!(matches!(
        transform_result(scoped),
        Err(PrepareError::ScopedDependency { .. })
    ));

    let direct_async = r#"
fn isalpha(c: i32) -> i32 { c }
fn combined(c: i32) -> i32 {
    static CELL: i32 = 1;
    match c { 0 => isalpha(c) + CELL, _ => c }
}
async fn unsupported() {}
"#;
    assert!(matches!(
        transform_result(direct_async),
        Err(PrepareError::UnsupportedAsyncFunction { .. })
    ));

    let unsupported_prelude = r#"
#![no_implicit_prelude]
fn isalpha(c: i32) -> i32 { c }
fn combined(c: i32) -> i32 {
    static CELL: i32 = 1;
    match c { 0 => isalpha(c) + CELL, _ => c }
}
"#;
    let result = utils::compilation::run_compiler_on_str(unsupported_prelude, prepare).unwrap();
    assert!(matches!(
        result,
        Err(PrepareError::UnsupportedPrelude { .. })
    ));
}

#[test]
fn missing_mapping_precedes_all_combined_preparation_rewrites() {
    let code = source(
        r#"
fn isalpha(c: i32) -> i32 { c }
fn reserve(CELL: i32) { let _ = CELL; }
fn combined(c: i32) -> i32 {
    static CELL: i32 = 1;
    match c { 0 => isalpha(c) + CELL, _ => c }
}
"#,
    );
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let mut krate = utils::ast::expanded_ast(tcx);
        let mut ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
        let mut discovery = Discovery::new(tcx, &ast_to_hir);
        discovery.discover_crate(&krate);
        assert!(discovery.error.is_none());
        let lifts = discovery.lifts.clone();
        let static_id = lifts[0].def_id;
        drop(discovery);

        let before = pprust::crate_to_string_for_macros(&krate);
        let use_span = ast_to_hir
            .path_span_to_res
            .iter()
            .find_map(|(span, resolution)| {
                matches!(
                    resolution,
                    Res::Def(DefKind::Static { .. }, definition)
                        if definition.as_local() == Some(static_id)
                )
                .then_some(*span)
            })
            .unwrap();
        ast_to_hir.path_span_to_res.remove(&use_span);

        assert_eq!(
            validate_use_mappings(&krate, &lifts, &ast_to_hir, tcx),
            Err(PrepareError::MissingMapping {
                construct: "use of local static `CELL`".to_owned(),
            })
        );
        let after = pprust::crate_to_string_for_macros(&krate);
        assert_eq!(after, before);
        assert!(after.contains("static CELL"));
        assert!(after.contains("isalpha(c)"));
        assert!(!after.contains("::proctor_libc::isalpha"));
        assert!(!after.contains("0 => {"));
    })
    .unwrap();
}

#[test]
fn preserves_export_attributes_across_renaming() {
    assert_prepares_to(
        r#"
fn reserve(EXPORTED: i32, INTERNAL: i32, PRIVATE: i32) { let _ = (EXPORTED, INTERNAL, PRIVATE); }
fn first() -> i32 { #[used] #[no_mangle] static EXPORTED: i32 = 1; EXPORTED }
fn second() -> i32 { #[export_name = "wire_symbol"] static INTERNAL: i32 = 2; INTERNAL }
fn third() -> i32 { static PRIVATE: i32 = 3; PRIVATE }
"#,
        r#"
fn reserve(EXPORTED: i32, INTERNAL: i32, PRIVATE: i32) { let _ = (EXPORTED, INTERNAL, PRIVATE); }
#[used]
#[export_name = "EXPORTED"]
static EXPORTED_0: i32 = 1;
fn first() -> i32 { EXPORTED_0 }
#[export_name = "wire_symbol"]
static INTERNAL_0: i32 = 2;
fn second() -> i32 { INTERNAL_0 }
static PRIVATE_0: i32 = 3;
fn third() -> i32 { PRIVATE_0 }
"#,
    );
}

#[test]
fn unrenamed_no_mangle_static_keeps_no_mangle() {
    assert_prepares_to(
        r#"fn f() -> i32 { #[no_mangle] static EXPORTED: i32 = 1; EXPORTED }"#,
        r#"#[no_mangle] static EXPORTED: i32 = 1; fn f() -> i32 { EXPORTED }"#,
    );
}

#[test]
fn prepare_is_idempotent() {
    let first = transform_and_compile(
        r#"
fn reserve(NAME: i32) { let _ = NAME; }
fn f(x: i32) -> i32 {
    #[no_mangle]
    static NAME: i32 = 1;
    match x { 0 => NAME, _ => 2 }
}
"#,
    );
    let second = utils::compilation::run_compiler_on_str(&first, prepare)
        .unwrap()
        .unwrap();
    assert!(!second.requires_proctor_libc);
    utils::compilation::run_compiler_on_str(&second.code, utils::type_check).unwrap();
    assert_eq!(compact(&first), compact(&second.code));
}

#[test]
fn leaves_module_statics_and_already_prepared_input_structurally_unchanged() {
    let code = r#"
static CELL: i32 = 1;
mod a { pub static DUP: i32 = 2; }
mod b { pub static DUP: i32 = 3; }
fn f() -> i32 { CELL }
"#;
    assert_prepares_to(code, code);
    let first = transform_and_compile(code);
    let second = utils::compilation::run_compiler_on_str(&first, prepare)
        .unwrap()
        .unwrap();
    assert!(!second.requires_proctor_libc);
    utils::compilation::run_compiler_on_str(&second.code, utils::type_check).unwrap();
    assert_eq!(compact(&first), compact(&second.code));
}

#[test]
fn enum_prepare_simpl_sequence_compiles() {
    let code = source(
        r#"
#![feature(core_intrinsics, structural_match)]
type Kind = core::ffi::c_uint;
const ZERO: Kind = 0;
const ONE: Kind = 1;
unsafe fn classify(x: Kind) -> i32 {
    static CALLS: i32 = 1;
    match x { ZERO => CALLS, ONE => CALLS + 1, _ => 0 }
}
"#,
    );
    let enum_output =
        utils::compilation::run_compiler_on_str(&code, crate::enum_replacer::replace_enums)
            .unwrap();
    let prepared = utils::compilation::run_compiler_on_str(&enum_output, prepare)
        .unwrap()
        .unwrap();
    let simplified =
        utils::compilation::run_compiler_on_str(&prepared.code, crate::simplifier::simplify)
            .unwrap();
    utils::compilation::run_compiler_on_str(&simplified, utils::type_check).unwrap();
    let simplified = compact(&simplified);
    assert_eq!(count(&simplified, "static CALLS"), 1);
    assert!(simplified.find("static CALLS").unwrap() < simplified.find("fn classify").unwrap());
    assert!(simplified.contains("=> { CALLS }"));
}

#[test]
fn prepare_then_unexpand_preserves_the_structural_postconditions() {
    let prepared = transform_and_compile(
        r#"
fn f(x: i32) -> i32 {
    static CELL: i32 = 1;
    match x { 0 => CELL, _ => x }
}
"#,
    );
    let unexpanded = utils::compilation::run_compiler_on_str(&prepared, |tcx| {
        crate::unexpander::unexpand(crate::unexpander::Config { use_print: true }, tcx)
    })
    .unwrap();
    utils::compilation::run_compiler_on_str(&unexpanded, utils::type_check).unwrap();
    let unexpanded = compact(&unexpanded);
    assert!(unexpanded.find("static CELL").unwrap() < unexpanded.find("fn f").unwrap());
    assert!(unexpanded.contains("match x { 0 => { CELL } _ => { x } }"));
}

#[test]
fn combined_modules_methods_dependencies_and_collisions_are_deterministic() {
    let code = r#"
fn reserve(CELL: i32, LINK: i32) { let _ = (CELL, LINK); }
mod nested {
    pub const BASE: i32 = 1;
    pub struct S;
    impl S {
        pub fn method(x: i32) -> i32 {
            static CELL: i32 = BASE;
            match x { 0 => CELL, _ => x }
        }
    }
    pub fn linked() -> &'static i32 {
        static CELL: i32 = BASE + 1;
        static LINK: &i32 = &CELL;
        LINK
    }
}
fn root(x: i32) -> i32 {
    static CELL: i32 = nested::BASE + 2;
    match x { 0 => CELL, _ => nested::S::method(x) }
}
"#;
    let first = transform_and_compile(code);
    let second = transform_and_compile(code);
    assert_eq!(first, second);
    let normalized = compact(&first);
    assert!(normalized.contains("pub struct S; static CELL_0: i32 = BASE; impl S"));
    assert!(normalized.contains("static CELL_1: i32 = BASE + 1; static LINK_0: &i32 = &CELL_1;"));
    assert!(normalized.contains("static CELL_2: i32 = nested::BASE + 2; fn root"));
}

#[test]
fn unsafe_cleanup_preserves_explicit_exports_created_by_prepare() {
    let prepared = transform_and_compile(
        r#"
fn reserve_renamed(RENAMED: i32) { let _ = RENAMED; }
fn reserve_internal(INTERNAL: i32) { let _ = INTERNAL; }
pub fn f() -> i32 { #[no_mangle] static UNCHANGED: i32 = 1; UNCHANGED }
pub fn g() -> i32 { #[no_mangle] static RENAMED: i32 = 2; RENAMED }
pub fn h() -> i32 { #[export_name = "wire_symbol"] static INTERNAL: i32 = 3; INTERNAL }
"#,
    );
    let config = crate::unsafe_resolver::Config {
        remove_unused: true,
        remove_no_mangle: true,
        remove_extern_c: true,
        replace_pub: true,
        c_exposed_fns: ["f", "g", "h"].into_iter().map(str::to_owned).collect(),
    };
    let output = utils::compilation::run_compiler_on_str(&prepared, |tcx| {
        crate::unsafe_resolver::resolve_unsafe(&config, tcx)
    })
    .unwrap();
    utils::compilation::run_compiler_on_str(&output, utils::type_check).unwrap();
    let output = compact(&output);
    assert!(!output.contains("no_mangle"));
    assert!(!output.contains("export_name = \"UNCHANGED\""));
    assert_eq!(count(&output, "export_name = \"RENAMED\""), 1);
    assert_eq!(count(&output, "export_name = \"wire_symbol\""), 1);
}

#[test]
fn rewrites_each_direct_ctype_call_by_textual_name() {
    for name in [
        "isalnum", "isalpha", "isblank", "iscntrl", "isdigit", "isgraph", "islower", "isprint",
        "ispunct", "isspace", "isupper", "isxdigit", "tolower", "toupper",
    ] {
        let input = format!(
            "fn {name}(c: i32) -> i32 {{ c + 100 }}\nfn use_it(c: i32) -> i32 {{ {name}(c) }}"
        );
        let result = transform_result(&input).unwrap();
        assert!(result.requires_proctor_libc, "{name}");
        assert!(
            compact(&result.code).contains(&format!("::proctor_libc::{name}(c)")),
            "{name}: {}",
            result.code
        );
        utils::compilation::run_compiler_on_str(&result.code, utils::type_check).unwrap();
    }
}

#[test]
fn direct_ctype_calls_preserve_arguments_and_reject_near_misses() {
    let result = transform_result(
        r#"
fn isalpha(c: i32) -> i32 { c }
fn isdigit(c: i32) -> i32 { c }
fn iscntrl(c: i32) -> i32 { c }
fn isspace(c: i32) -> i32 { c }
fn tolower(c: i32) -> i32 { c }
fn toupper(c: i32) -> i32 { c }
fn nested(mut n: i32) -> i32 { isalpha({ n += 1; isdigit(n) }) }
mod helpers { pub fn isalpha(c: i32) -> i32 { c } }
fn unchanged(c: i32) -> i32 { helpers::isalpha(c) }
"#,
    )
    .unwrap();
    assert!(result.requires_proctor_libc);
    let code = compact(&result.code);
    assert!(code.contains("::proctor_libc::isalpha({ n += 1; ::proctor_libc::isdigit(n) })"));
    assert!(code.contains("helpers::isalpha(c)"));
    utils::compilation::run_compiler_on_str(&result.code, utils::type_check).unwrap();

    for input in [
        "fn isalpha() -> i32 { 7 } fn f() -> i32 { isalpha() }",
        "fn isalpha(a: i32, b: i32) -> i32 { a + b } fn f(c: i32) -> i32 { isalpha(c, c) }",
        "fn c_isalpha(c: i32) -> i32 { c } fn f(c: i32) -> i32 { c_isalpha(c) }",
        "fn isalpha_extra(c: i32) -> i32 { c } fn f(c: i32) -> i32 { isalpha_extra(c) }",
        "struct Helper; impl Helper { fn isalpha(&self, c: i32) -> i32 { c } } fn f(helper: Helper, c: i32) -> i32 { helper.isalpha(c) }",
        "fn isalpha_fn(c: i32) -> i32 { c } fn f(c: i32) -> i32 { let classify: fn(i32) -> i32 = isalpha_fn; classify(c) }",
        "macro_rules! isalpha { ($c:expr) => { $c } } fn f(c: i32) -> i32 { isalpha!(c) }",
    ] {
        let result = transform_result(input).unwrap();
        assert!(!result.requires_proctor_libc);
    }
}

#[test]
fn direct_ctype_calls_cover_effects_nesting_and_defined_inputs() {
    for name in [
        "isalnum", "isalpha", "isblank", "iscntrl", "isdigit", "isgraph", "islower", "isprint",
        "ispunct", "isspace", "isupper", "isxdigit", "tolower", "toupper",
    ] {
        let input = format!(
            "unsafe extern \"C\" {{ fn {name}(c: i32) -> i32; }}\npub unsafe fn classify(mut n: i32) -> i32 {{ {name}({{ n += 1; n }}) }}"
        );
        let result = transform_result(&input).unwrap();
        assert!(result.requires_proctor_libc, "{name}");
        let code = compact(&result.code);
        assert!(
            code.contains(&format!("::proctor_libc::{name}({{ n += 1; n }} )"))
                || code.contains(&format!("::proctor_libc::{name}({{ n += 1; n }})")),
            "{name}: {code}"
        );
        assert_eq!(count(&code, "n += 1"), 1, "{name}: {code}");
        utils::compilation::run_compiler_on_str(&result.code, utils::type_check).unwrap();
    }

    let result = transform_result(
        r#"
fn isalpha(c: i32) -> i32 { c }
fn isdigit(c: i32) -> i32 { c }
fn iscntrl(c: i32) -> i32 { c }
fn isspace(c: i32) -> i32 { c }
fn tolower(c: i32) -> i32 { c }
fn toupper(c: i32) -> i32 { c }
fn nested(n: i32) -> i32 { isalpha(isdigit(n)) }
fn compared(n: i32) -> i32 { if isalpha(n) != 0 { 1 } else { 0 } }
fn returned(n: i32) -> i32 { return isalpha(n); }
fn matched(n: i32) -> i32 { match n { 0 => isalpha(n), _ => 0 } }
fn defined_inputs() -> i32 {
    isalpha(-1) + isalpha(65) + iscntrl(31) + isspace(9) + isdigit(48)
        + tolower(-1) + tolower(65) + toupper(-1) + toupper(97)
}
"#,
    )
    .unwrap();
    assert!(result.requires_proctor_libc);
    let code = compact(&result.code);
    assert!(code.contains("::proctor_libc::isalpha(::proctor_libc::isdigit(n))"));
    assert_eq!(count(&code, "::proctor_libc::isalpha"), 6);
    utils::compilation::run_compiler_on_str(&result.code, utils::type_check).unwrap();
}

fn ctype_table_prelude() -> &'static str {
    r#"
unsafe extern "C" {
    fn __ctype_b_loc() -> *mut *const u16;
    fn __ctype_tolower_loc() -> *mut *const i32;
    fn __ctype_toupper_loc() -> *mut *const i32;
}
const _ISupper: u32 = 256; const _ISlower: u32 = 512;
const _ISalpha: u32 = 1024; const _ISdigit: u32 = 2048;
const _ISxdigit: u32 = 4096; const _ISspace: u32 = 8192;
const _ISprint: u32 = 16384; const _ISgraph: u32 = 32768;
const _ISblank: u32 = 1; const _IScntrl: u32 = 2;
const _ISpunct: u32 = 4; const _ISalnum: u32 = 8;
"#
}

#[test]
fn rewrites_each_supported_ctype_mask_and_preserves_the_index() {
    for (mask, function) in [
        ("_ISupper", "isupper"),
        ("_ISlower", "islower"),
        ("_ISalpha", "isalpha"),
        ("_ISdigit", "isdigit"),
        ("_ISxdigit", "isxdigit"),
        ("_ISspace", "isspace"),
        ("_ISprint", "isprint"),
        ("_ISgraph", "isgraph"),
        ("_ISblank", "isblank"),
        ("_IScntrl", "iscntrl"),
        ("_ISpunct", "ispunct"),
        ("_ISalnum", "isalnum"),
    ] {
        let input = format!(
            "{}\npub unsafe fn classify(c: i32) -> i32 {{ *(*__ctype_b_loc()).offset(c as i32 as isize) as i32 & {mask} as i32 as u16 as i32 }}",
            ctype_table_prelude()
        );
        let result = transform_result(&input).unwrap();
        assert!(result.requires_proctor_libc, "{mask}");
        assert!(
            compact(&result.code).contains(&format!("::proctor_libc::{function}(c as i32)")),
            "{mask}: {}",
            result.code
        );
        utils::compilation::run_compiler_on_str(&result.code, utils::type_check).unwrap();
    }
}

#[test]
fn rewrites_case_tables_and_requires_the_terminal_isize_cast() {
    let input = format!(
        "{}\npub unsafe fn classify(mut c: i32) -> i32 {{ *(*__ctype_tolower_loc()).offset(({{ c += 1; c }}) as isize) + *(*__ctype_toupper_loc()).offset(c as i32 as isize) }}",
        ctype_table_prelude()
    );
    let first = transform_result(&input).unwrap();
    assert!(first.requires_proctor_libc);
    let code = compact(&first.code);
    assert!(code.contains("::proctor_libc::tolower("));
    assert!(code.contains("c += 1; c"));
    assert!(code.contains("::proctor_libc::toupper(c as i32)"));
    utils::compilation::run_compiler_on_str(&first.code, utils::type_check).unwrap();
    let second = utils::compilation::run_compiler_on_str(&first.code, prepare)
        .unwrap()
        .unwrap();
    assert!(!second.requires_proctor_libc);
    assert_eq!(compact(&first.code), compact(&second.code));

    let near_miss = format!(
        "{}\npub unsafe fn classify(c: isize) -> i32 {{ *(*__ctype_tolower_loc()).offset(c) }}",
        ctype_table_prelude()
    );
    let result = transform_result(&near_miss).unwrap();
    assert!(!result.requires_proctor_libc);
}

#[test]
fn ctype_table_rewrites_preserve_outer_contexts_and_inner_casts() {
    let input = format!(
        "{}\npub unsafe fn classify(c: i32) -> (i32, bool, bool, bool, bool, i32) {{\nlet bare = *(*__ctype_b_loc()).offset(c as i32 as isize) as i32 & _ISalpha as i32 as u16 as i32;\nlet a = (*(*__ctype_b_loc()).offset(c as i32 as isize) as i32 & _ISalpha as i32) != 0;\nlet b = 0 != (*(*__ctype_b_loc()).offset(c as i32 as isize) as i32 & _ISalpha as i32);\nlet d = (*(*__ctype_b_loc()).offset(c as i32 as isize) as i32 & _ISalpha as i32) == 0;\nlet e = 0 == (*(*__ctype_b_loc()).offset(c as i32 as isize) as i32 & _ISalpha as i32);\nlet casted = *(*__ctype_b_loc()).offset(c as u8 as i32 as isize) as i32 & _ISalpha as i32;\n(bare, a, b, d, e, casted)\n}}",
        ctype_table_prelude()
    );
    let result = transform_result(&input).unwrap();
    assert!(result.requires_proctor_libc);
    let code = compact(&result.code);
    assert_eq!(count(&code, "::proctor_libc::isalpha(c as i32)"), 5);
    assert_eq!(count(&code, "::proctor_libc::isalpha(c as u8 as i32)"), 1);
    assert_eq!(count(&code, " != "), 2, "{code}");
    assert_eq!(count(&code, " == "), 2, "{code}");
    utils::compilation::run_compiler_on_str(&result.code, utils::type_check).unwrap();
}

#[test]
fn ctype_table_rewrites_nested_ctype_in_retained_indices() {
    let input = format!(
        "{}\nfn isalpha(c: i32) -> i32 {{ c }}\nfn tolower(c: i32) -> i32 {{ c }}\npub unsafe fn classify(c: i32) -> i32 {{\n(*(*__ctype_b_loc()).offset(isalpha(c) as isize) as i32 & _ISspace as i32)\n+ *(*__ctype_toupper_loc()).offset(tolower(c) as isize)\n}}",
        ctype_table_prelude()
    );
    let first = transform_result(&input).unwrap();
    assert!(first.requires_proctor_libc);
    let code = compact(&first.code);
    assert_eq!(
        count(&code, "::proctor_libc::isspace(::proctor_libc::isalpha(c))"),
        1,
        "{code}"
    );
    assert_eq!(
        count(&code, "::proctor_libc::toupper(::proctor_libc::tolower(c))"),
        1,
        "{code}"
    );
    utils::compilation::run_compiler_on_str(&first.code, utils::type_check).unwrap();

    let second = utils::compilation::run_compiler_on_str(&first.code, prepare)
        .unwrap()
        .unwrap();
    assert!(!second.requires_proctor_libc);
    assert_eq!(compact(&first.code), compact(&second.code));
}

#[test]
fn ctype_table_recognition_is_syntax_only_and_rejects_near_misses() {
    let local = r#"
fn __ctype_b_loc() -> *mut *const u16 { ::std::ptr::null_mut() }
const _ISalpha: u32 = 7;
unsafe fn classify(c: i32) -> i32 {
    *(*__ctype_b_loc()).offset(c as isize) as i32 & _ISalpha as i32
}
"#;
    let result = transform_result(local).unwrap();
    assert!(result.requires_proctor_libc);
    assert!(compact(&result.code).contains("::proctor_libc::isalpha(c)"));
    utils::compilation::run_compiler_on_str(&result.code, utils::type_check).unwrap();

    let misses = [
        format!("{}\npub unsafe fn f() -> *const u16 {{ *__ctype_b_loc() }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ _ISalpha as i32 & (*(*__ctype_b_loc()).offset(c as isize) as i32) }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ (*(*__ctype_b_loc()).offset(c as isize) as i32) & (_ISalpha | _ISdigit) as i32 }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize, mask: i32) -> i32 {{ (*(*__ctype_b_loc()).offset(c as isize) as i32) & mask }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ (*(*crate::__ctype_b_loc()).offset(c as isize) as i32) & _ISalpha as i32 }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ (*(*__ctype_b_loc()).offset(c as isize) as i32) & crate::_ISalpha as i32 }}", ctype_table_prelude()),
        "unsafe extern \"C\" { fn __ctype_b_loc(_: i32) -> *mut *const u16; } const _ISalpha: u32 = 1; pub unsafe fn f(c: isize) -> i32 { (*(*__ctype_b_loc(0)).offset(c as isize) as i32) & _ISalpha as i32 }".to_owned(),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ (*(*__ctype_b_loc()).offset(c) as i32) & _ISalpha as i32 }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: usize) -> u16 {{ *(*__ctype_b_loc()).add(c) }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ *(*__ctype_tolower_loc()).offset(c) }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ *(*__ctype_toupper_loc()).offset(c) }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: usize) -> i32 {{ *(*__ctype_tolower_loc()).add(c) }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ *(*crate::__ctype_toupper_loc()).offset(c as isize) }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ (*(*__ctype_b_loc()).offset(c as isize) & _ISalpha as u16) as i32 }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ (**__ctype_b_loc().offset(c as isize) as i32) & _ISalpha as i32 }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ (*(__ctype_b_loc()).offset(c as isize) as i32) & _ISalpha as i32 }}", ctype_table_prelude()),
        format!("{}\npub unsafe fn f(c: isize) -> i32 {{ ((*__ctype_b_loc()).offset(c as isize) as i32) & _ISalpha as i32 }}", ctype_table_prelude()),
    ];
    for input in misses {
        let result = transform_result(&input).unwrap();
        assert!(!result.requires_proctor_libc, "{}", compact(&result.code));
        utils::compilation::run_compiler_on_str(&result.code, utils::type_check).unwrap();
    }
}

#[test]
fn ctype_prepare_is_structurally_idempotent() {
    let input = format!(
        "{}\nfn isalpha(c: i32) -> i32 {{ c }}\npub unsafe fn combined(c: i32) -> i32 {{\nstatic CALLS: i32 = 1;\nmatch c {{\n0 => isalpha(c) + CALLS,\n_ => (*(*__ctype_b_loc()).offset(c as isize) as i32 & _ISspace as i32) + *(*__ctype_tolower_loc()).offset(c as isize),\n}}\n}}",
        ctype_table_prelude()
    );
    let first = transform_result(&input).unwrap();
    assert!(first.requires_proctor_libc);
    let code = compact(&first.code);
    assert_eq!(count(&code, "::proctor_libc::isalpha(c)"), 1);
    assert_eq!(count(&code, "::proctor_libc::isspace(c)"), 1);
    assert_eq!(count(&code, "::proctor_libc::tolower(c)"), 1);
    utils::compilation::run_compiler_on_str(&first.code, utils::type_check).unwrap();
    let second = utils::compilation::run_compiler_on_str(&first.code, prepare)
        .unwrap()
        .unwrap();
    assert!(!second.requires_proctor_libc);
    assert_eq!(compact(&first.code), compact(&second.code));
}

#[test]
fn neighboring_passes_preserve_prepared_ctype_calls() {
    let prepared = source(
        r#"
pub unsafe fn direct(c: i32) -> i32 {
    if ::proctor_libc::isalpha(c) != 0 { 1 } else { 0 }
}
pub unsafe fn table(c: i32) -> i32 {
    ::proctor_libc::isspace(c)
}
"#,
    );
    let unsafe_config = crate::unsafe_resolver::Config {
        remove_unused: true,
        remove_no_mangle: true,
        remove_extern_c: true,
        replace_pub: true,
        c_exposed_fns: ["direct", "table"].into_iter().map(str::to_owned).collect(),
    };
    let outputs = [
        utils::compilation::run_compiler_on_str(&prepared, crate::simplifier::simplify).unwrap(),
        utils::compilation::run_compiler_on_str(&prepared, |tcx| {
            crate::unsafe_resolver::resolve_unsafe(&unsafe_config, tcx)
        })
        .unwrap(),
        utils::compilation::run_compiler_on_str(&prepared, |tcx| {
            crate::unexpander::unexpand(crate::unexpander::Config { use_print: true }, tcx)
        })
        .unwrap(),
    ];
    for output in outputs {
        utils::compilation::run_compiler_on_str(&output, utils::type_check).unwrap();
        let output = compact(&output);
        assert_eq!(count(&output, "::proctor_libc::isalpha(c)"), 1, "{output}");
        assert_eq!(count(&output, "::proctor_libc::isspace(c)"), 1, "{output}");
        assert!(!output.contains("__ctype_b_loc"));
    }

    let with_unused_declarations = source(
        r#"
unsafe extern "C" {
    fn isalpha(c: i32) -> i32;
    fn __ctype_b_loc() -> *mut *const u16;
}
pub unsafe fn direct(c: i32) -> i32 { ::proctor_libc::isalpha(c) }
pub unsafe fn table(c: i32) -> i32 { ::proctor_libc::isspace(c) }
"#,
    );
    let cleaned = utils::compilation::run_compiler_on_str(&with_unused_declarations, |tcx| {
        crate::unsafe_resolver::resolve_unsafe(&unsafe_config, tcx)
    })
    .unwrap();
    utils::compilation::run_compiler_on_str(&cleaned, utils::type_check).unwrap();
    let cleaned = compact(&cleaned);
    assert!(!cleaned.contains("extern \"C\""));
    assert!(cleaned.contains("fn direct"));
    assert!(cleaned.contains("fn table"));
}
