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
