use rustc_hash::FxHashSet;

use crate::ir_utils;

fn run_test(code: &str, unsafe_fns: &[&str]) {
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let res: Vec<_> = super::find_unsafe_fns(tcx)
            .into_iter()
            .map(|def_id| ir_utils::def_id_to_symbol(def_id, tcx).unwrap())
            .collect();
        let res: FxHashSet<_> = res.iter().map(|s| s.as_str()).collect();
        let expected: FxHashSet<_> = unsafe_fns.iter().cloned().collect();
        assert_eq!(res, expected);
    })
    .unwrap();
}

#[test]
fn test_mutable_static() {
    let code = r#"
static mut X: i32 = 0;
unsafe fn f() -> i32 {
    X += 1;
    X
}
unsafe fn g() -> i32 {
    let mut x = 0;
    x += 1;
    x
}
"#;
    run_test(code, &["f"]);
}

#[test]
fn test_extern_static() {
    let code = r#"
extern "C" {
    static mut X: i32;
}
unsafe fn f() -> i32 {
    X += 1;
    X
}
unsafe fn g() -> i32 {
    let mut x = 0;
    x += 1;
    x
}
"#;
    run_test(code, &["f"]);
}

#[test]
fn test_raw_pointer() {
    let code = r#"
unsafe fn f(x: *mut i32) -> i32 {
    *x += 1;
    *x
}
unsafe fn g(x: *mut i32) -> i32 {
    0
}
"#;
    run_test(code, &["f"]);
}

#[test]
fn test_union_field() {
    let code = r#"
union U {
    x: i32,
    y: f32,
}
unsafe fn f(x: &mut U) -> i32 {
    x.x
}
unsafe fn g(x: &mut U) -> i32 {
    x.x = 0;
    0
}
"#;
    run_test(code, &["f"]);
}

#[test]
fn test_extern_fn() {
    let code = r#"
extern "C" {
    fn h() -> i32;
}
unsafe fn f() -> i32 {
    h()
}
unsafe fn g() -> i32 {
    0
}
"#;
    run_test(code, &["f"]);
}

#[test]
fn test_call() {
    let code = r#"
static mut X: i32 = 0;
unsafe fn f0() -> i32 {
    X
}
unsafe fn f1() -> i32 {
    f0()
}
unsafe fn g0() -> i32 {
    0
}
unsafe fn g1() -> i32 {
    g0()
}
"#;
    run_test(code, &["f0", "f1"]);
}

#[test]
fn test_call_chain() {
    let code = r#"
static mut X: i32 = 0;
unsafe fn f0() -> i32 {
    X
}
unsafe fn f1() -> i32 {
    f0()
}
unsafe fn f2() -> i32 {
    f1()
}
unsafe fn f3() -> i32 {
    f2()
}
unsafe fn g() -> i32 {
    0
}
"#;
    run_test(code, &["f0", "f1", "f2", "f3"]);
}

#[test]
fn test_mutual_recursion() {
    let code = r#"
static mut X: i32 = 0;
unsafe fn f0() -> i32 {
    X
}
unsafe fn f1() -> i32 {
    f0();
    f3()
}
unsafe fn f2() -> i32 {
    f1()
}
unsafe fn f3() -> i32 {
    f2()
}
unsafe fn g() -> i32 {
    0
}
"#;
    run_test(code, &["f0", "f1", "f2", "f3"]);
}

#[test]
fn test_mutual_recursion_safe() {
    let code = r#"
static mut X: i32 = 0;
unsafe fn f() -> i32 {
    X
}
unsafe fn g0() -> i32 {
    g2()
}
unsafe fn g1() -> i32 {
    g0()
}
unsafe fn g2() -> i32 {
    g1()
}
"#;
    run_test(code, &["f"]);
}

#[test]
fn test_call_safe() {
    let code = r#"
static mut X: i32 = 0;
unsafe fn f() -> i32 {
    g();
    X
}
unsafe fn g() -> i32 {
    0
}
"#;
    run_test(code, &["f"]);
}
#[test]
fn test_vararg() {
    let code = r#"
#![feature(c_variadic)]
unsafe extern "C" fn f(mut x: i32, ...) -> i32 {
    x
}
unsafe fn g(mut x: i32) -> i32 {
    x
}
"#;
    run_test(code, &["f"]);
}
