use rustc_hash::FxHashSet;

fn run_transformation_test(code: &str, remove_unused: bool, includes: &[&str], excludes: &[&str]) {
    let transformed = utils::compilation::run_compiler_on_str(&code, |tcx| {
        let config = super::Config {
            remove_unused,
            remove_no_mangle: false,
            replace_pub: false,
        };
        super::resolve_unsafe(&config, tcx)
    })
    .unwrap();
    utils::compilation::run_compiler_on_str(&transformed, |tcx| {
        utils::type_check(tcx);
    })
    .expect(&transformed);
    for include in includes {
        assert!(
            transformed.contains(include),
            "{transformed}\ndoes not contain \"{include}\"",
        );
    }
    for exclude in excludes {
        assert!(
            !transformed.contains(exclude),
            "{transformed}\ncontains \"{exclude}\"",
        );
    }
}

#[test]
fn test_transformation_unsafe() {
    let code = r#"
unsafe fn f() -> i32 {
    0
}
unsafe fn g() -> i32 {
    h()
}
unsafe fn h() -> i32 {
    let x = 0;
    let p: *const i32 = &x;
    *p
}
"#;
    run_transformation_test(
        code,
        false,
        &["fn f()", "unsafe fn g()", "unsafe fn h()"],
        &["unsafe fn f()"],
    );
}

#[test]
fn test_transformation_unused() {
    let code = r#"
mod a {
    fn main() {}
    pub fn g() {}
}
mod b {
    use crate::a::g;
    pub fn f() {
        g();
    }
}
"#;
    run_transformation_test(
        code,
        true,
        &["fn main()"],
        &["fn f()", "fn g()", "use crate::a::g;"],
    );
}

#[test]
fn test_transformation_unused_uses() {
    let code = r#"
mod a {
    fn main() {
        g();
    }
    pub fn g() {}
}
mod b {
    use crate::a::g;
    pub fn f() {
        g();
    }
}
"#;
    run_transformation_test(
        code,
        true,
        &["fn main()", "fn g()"],
        &["fn f()", "use crate::a::g;"],
    );
}

#[test]
fn test_transformation_unused_method() {
    let code = r#"
trait A {
    fn f();
    fn g();
}
struct S {}
impl A for S {
    fn f() {}
    fn g() {}
}
fn main() {
    S::g();
}
"#;
    run_transformation_test(
        code,
        true,
        &["fn main()", "fn g()", "trait A", "struct S", "impl A for S"],
        &["fn f()"],
    );
}

fn run_test(code: &str, unsafe_fns: &[&str]) {
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let res: Vec<_> = super::find_unsafe_fns(tcx)
            .into_iter()
            .map(|def_id| utils::ir::def_id_to_symbol(def_id, tcx).unwrap())
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
