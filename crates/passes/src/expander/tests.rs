use utils::compilation::run_compiler_on_str;

const VECTORS: &str = r#"
pub struct Buffer { pub bytes: Vec<u8> }
pub struct Owned(pub i32);
pub fn empty() -> Vec<i32> { vec![] }
pub fn repeated(size: usize) -> Buffer { Buffer { bytes: vec![0; size] } }
pub fn listed(value: i32) -> Vec<i32> { vec![value, 2, 3, 4] }
pub fn owned(left: Owned, right: Owned) -> Vec<Owned> { vec![left, right] }
pub fn cloned(value: String, size: usize) -> Vec<String> { vec![value; size] }
pub fn boxed(size: usize) -> Box<[i8]> { vec![0i8; size].into_boxed_slice() }
pub fn pointers(size: usize) -> Box<[*const i8]> {
    vec![std::ptr::null::<i8>(); size].into_boxed_slice()
}
pub fn coerced() -> Vec<Box<dyn std::fmt::Display>> {
    vec![Box::new(1i32), Box::new(false)]
}
pub fn nested() -> Vec<Vec<i32>> { vec![vec![1, 2], vec![3; 4]] }
use std::vec as make_vec;
pub fn renamed() -> Vec<i32> { make_vec![1; 2] }
macro_rules! wrapped_vec { () => { std::vec![1, 2] }; }
pub fn wrapped() -> Vec<i32> { wrapped_vec!() }
"#;

fn expand(source: &str) -> String {
    run_compiler_on_str(source, |tcx| super::expand(super::Config::default(), tcx)).unwrap()
}

fn check(source: &str) {
    run_compiler_on_str(source, utils::type_check).expect(source);
}

const FALLIBLE_ALLOCATION: &str = r#"
pub fn allocate(value: u32) -> Result<Box<u32>, std::alloc::AllocError> {
    Box::try_new(value)
}
"#;

#[test]
fn existing_features_are_merged_deduplicated_and_emitted_individually() {
    for attributes in [
        "#![feature(c_variadic, allocator_api)]\n#![feature(extern_types, linkage)]",
        "#![feature(allocator_api)]\n#![feature(allocator_api, c_variadic)]",
    ] {
        let expanded = expand(&format!("{attributes}\n{FALLIBLE_ALLOCATION}"));
        check(&expanded);
        for feature in ["allocator_api", "c_variadic", "extern_types", "linkage"] {
            assert_eq!(
                expanded.matches(&format!("#![feature({feature})]")).count(),
                1,
                "{expanded}"
            );
        }
        let mut features = expanded
            .lines()
            .filter(|line| line.starts_with("#![feature("))
            .collect::<Vec<_>>();
        assert!(
            features.iter().all(|attribute| !attribute.contains(',')),
            "{expanded}"
        );
        let count = features.len();
        features.sort_unstable();
        features.dedup();
        assert_eq!(features.len(), count, "{expanded}");
        assert_eq!(expand(&expanded), expanded);
    }
}

#[test]
fn conditionally_enabled_features_survive_expansion() {
    let source = format!(
        r#"
#![cfg_attr(all(), feature(allocator_api))]
#![cfg_attr(any(), feature(try_blocks))]
{FALLIBLE_ALLOCATION}
"#
    );
    let expanded = expand(&source);
    check(&expanded);
    assert!(
        expanded.contains("#![feature(allocator_api)]"),
        "{expanded}"
    );
    assert!(!expanded.contains("try_blocks"), "{expanded}");
}

const THREAD_LOCALS: &str = r#"
use std::cell::{Cell, RefCell};
std::thread_local! {
    #[allow(dead_code)]
    pub static LAZY: RefCell<Vec<u8>> = RefCell::new(Vec::new());
    static LAZY_CELL: Cell<u32> = Cell::new(1);
    static LAZY_UNSAFE: Cell<u32> = Cell::new(unsafe { std::ptr::read(&5u32) });
    pub(crate) static EAGER: RefCell<String> = const { RefCell::new(String::new()) };
    static EAGER_CELL: Cell<u32> = const { Cell::new(2) };
}
pub fn update() -> u32 {
    LAZY.with(|value| value.borrow_mut().push(3));
    EAGER.with(|value| value.borrow_mut().push('x'));
    LAZY_CELL.with(|left| EAGER_CELL.with(|right| LAZY_UNSAFE.with(|extra| left.get() + right.get() + extra.get())))
}
mod nested {
    std::thread_local! { pub static VALUE: std::cell::Cell<usize> = std::cell::Cell::new(4); }
    pub fn get() -> usize { VALUE.with(std::cell::Cell::get) }
}
"#;

#[test]
fn standard_thread_locals_recompile_after_expansion() {
    let expanded = expand(THREAD_LOCALS);
    check(&expanded);
    assert_eq!(expand(&expanded), expanded);
}

#[test]
fn standard_thread_locals_recompile_through_preparation_and_unexpansion() {
    let expanded = expand(THREAD_LOCALS);
    let prepared = run_compiler_on_str(&expanded, crate::preparer::prepare)
        .unwrap()
        .unwrap();
    check(&prepared.code);
    let unexpanded = run_compiler_on_str(&prepared.code, |tcx| {
        crate::unexpander::unexpand(crate::unexpander::Config::default(), tcx)
    })
    .unwrap();
    check(&unexpanded);
    assert_eq!(
        unexpanded.matches("::std::thread_local!").count(),
        6,
        "{unexpanded}"
    );
    for internal in [
        "LazyStorage",
        "EagerStorage",
        "LocalKey::new",
        "#![feature(thread_local_internals)]",
    ] {
        assert!(!unexpanded.contains(internal), "{unexpanded}");
    }
}

#[test]
fn derived_debug_helpers_recompile_through_preparation_and_unexpansion() {
    let source = r#"
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Arithmetic { Integer { unsigned: bool }, Float }
        #[derive(Debug)]
        pub struct Location { pub line: usize, pub column: usize }
    "#;
    let expanded = expand(source);
    check(&expanded);
    let prepared = run_compiler_on_str(&expanded, crate::preparer::prepare)
        .unwrap()
        .unwrap();
    check(&prepared.code);
    let unexpanded = run_compiler_on_str(&prepared.code, |tcx| {
        crate::unexpander::unexpand(crate::unexpander::Config::default(), tcx)
    })
    .unwrap();
    check(&unexpanded);
    assert!(unexpanded.contains("#[derive(Debug)]"), "{unexpanded}");
    assert!(!unexpanded.contains("debug_struct_field"), "{unexpanded}");
    assert!(
        !unexpanded.contains("#![feature(fmt_helpers_for_derive)]"),
        "{unexpanded}"
    );
    assert!(
        !unexpanded.contains("#![feature(derive_eq)]"),
        "{unexpanded}"
    );
}

#[test]
fn standard_thread_locals_recompile_through_postprocessing() {
    let expanded = expand(THREAD_LOCALS);
    let interfaces = run_compiler_on_str(&expanded, |tcx| {
        crate::interface_fixer::fix_interfaces(&crate::interface_fixer::Config::default(), tcx)
    })
    .unwrap();
    check(&interfaces);
    let resolved = run_compiler_on_str(&interfaces, |tcx| {
        crate::unsafe_resolver::resolve_unsafe(&crate::unsafe_resolver::Config::default(), tcx)
    })
    .unwrap();
    check(&resolved);
    let unexpanded = run_compiler_on_str(&resolved, |tcx| {
        crate::unexpander::unexpand(crate::unexpander::Config::default(), tcx)
    })
    .unwrap();
    check(&unexpanded);
    assert_eq!(
        unexpanded.matches("::std::thread_local!").count(),
        6,
        "{unexpanded}"
    );
    assert!(!unexpanded.contains("LazyStorage"), "{unexpanded}");
    assert!(!unexpanded.contains("EagerStorage"), "{unexpanded}");
}

#[test]
fn preserved_features_do_not_change_other_crate_attribute_handling() {
    let source = r#"
#![feature(register_tool)]
#![register_tool(c2rust)]
#![allow(dead_code, unused_assignments, unused_mut, improper_ctypes)]
#![warn(unused_imports)]
#![doc = "source crate documentation"]
pub fn value() -> i32 { 1 }
"#;
    for keep_allows in [false, true] {
        let expanded = run_compiler_on_str(source, |tcx| {
            super::expand(super::Config { keep_allows }, tcx)
        })
        .unwrap();
        check(&expanded);
        assert!(
            expanded.contains("#![feature(register_tool)]"),
            "{expanded}"
        );
        assert!(
            !expanded.contains("#![register_tool(c2rust)]"),
            "{expanded}"
        );
        for attribute in [
            "improper_ctypes",
            "unused_imports",
            "source crate documentation",
        ] {
            assert!(!expanded.contains(attribute), "{expanded}");
        }
        for lint in [
            "non_camel_case_types",
            "non_snake_case",
            "non_upper_case_globals",
        ] {
            assert!(
                expanded.contains(&format!("#![allow({lint})]")),
                "{expanded}"
            );
        }
        assert!(
            expanded.contains("#![warn(mutable_transmutes)]"),
            "{expanded}"
        );
        for lint in ["dead_code", "unused_assignments", "unused_mut"] {
            assert_eq!(
                expanded.contains(&format!("#![allow({lint})]")),
                keep_allows,
                "{expanded}"
            );
        }
    }
}

#[test]
fn fallible_allocation_recompiles_through_preparation_and_unexpansion() {
    let expanded = expand(&format!(
        "#![feature(panic_internals, allocator_api)]\n{FALLIBLE_ALLOCATION}"
    ));
    check(&expanded);
    let prepared = run_compiler_on_str(&expanded, crate::preparer::prepare)
        .unwrap()
        .unwrap();
    check(&prepared.code);
    let unexpanded = run_compiler_on_str(&prepared.code, |tcx| {
        crate::unexpander::unexpand(crate::unexpander::Config::default(), tcx)
    })
    .unwrap();
    check(&unexpanded);
    assert!(
        unexpanded.contains("#![feature(allocator_api)]"),
        "{unexpanded}"
    );
    assert!(
        !unexpanded.contains("#![feature(panic_internals)]"),
        "{unexpanded}"
    );
    assert!(unexpanded.contains("Box::try_new"), "{unexpanded}");
}

#[test]
fn standard_vectors_recompile_after_expansion() {
    let expanded = expand(VECTORS);
    check(&expanded);
    assert!(!expanded.contains("::alloc::"), "{expanded}");
    assert!(!expanded.contains("liballoc_internals"), "{expanded}");
    assert_eq!(expand(&expanded), expanded);
}

#[test]
fn standard_vectors_recompile_through_preparation() {
    let expanded = expand(VECTORS);
    let prepared = run_compiler_on_str(&expanded, crate::preparer::prepare)
        .unwrap()
        .unwrap();
    check(&prepared.code);
    let unexpanded = run_compiler_on_str(&prepared.code, |tcx| {
        crate::unexpander::unexpand(crate::unexpander::Config::default(), tcx)
    })
    .unwrap();
    check(&unexpanded);
}

#[test]
fn standard_vectors_recompile_through_postprocessing() {
    let expanded = expand(VECTORS);
    let interfaces = run_compiler_on_str(&expanded, |tcx| {
        crate::interface_fixer::fix_interfaces(&crate::interface_fixer::Config::default(), tcx)
    })
    .unwrap();
    check(&interfaces);
    let resolved = run_compiler_on_str(&interfaces, |tcx| {
        crate::unsafe_resolver::resolve_unsafe(&crate::unsafe_resolver::Config::default(), tcx)
    })
    .unwrap();
    check(&resolved);
    let unexpanded = run_compiler_on_str(&resolved, |tcx| {
        crate::unexpander::unexpand(crate::unexpander::Config::default(), tcx)
    })
    .unwrap();
    check(&unexpanded);
}

#[test]
fn user_allocation_paths_and_custom_vec_macros_are_preserved() {
    let source = r#"
pub mod vec { pub fn from_elem(value: i32, count: usize) -> i32 { value + count as i32 } }
pub mod alloc {
    pub mod vec { pub fn from_elem(value: i32, count: usize) -> i32 { value - count as i32 } }
    pub mod boxed { pub fn box_new(value: i32) -> i32 { value + 1 } }
}
macro_rules! vec { ($value:expr; $count:expr) => { $crate::vec::from_elem($value, $count) }; }
pub fn custom() -> i32 { vec![4; 2] }
pub fn local() -> i32 { alloc::vec::from_elem(4, 2) + alloc::boxed::box_new(4) }
pub fn standard() -> std::vec::Vec<i32> { std::vec![4; 2] }
pub fn literal() -> &'static str { "::alloc::vec::from_elem" }
"#;
    let expanded = expand(source);
    check(&expanded);
    assert!(
        expanded.contains("\"::alloc::vec::from_elem\""),
        "{expanded}"
    );
}
