use rustc_hash::FxHashSet;

fn run_transformation_test(code: &str, remove_unused: bool, includes: &[&str], excludes: &[&str]) {
    let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
        let config = super::Config {
            remove_unused,
            remove_no_mangle: false,
            remove_extern_c: false,
            replace_pub: false,
            c_exposed_fns: FxHashSet::default(),
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
fn grouped_imports_keep_used_types_and_constants_and_prune_unused_leaves() {
    let code = r#"
mod data {
    pub struct Value;
    pub type Id = usize;
    pub const CAPACITY: Id = 4;
    pub fn obsolete() {}
}
mod app {
    use crate::data::{Value, Id, CAPACITY, obsolete};
    pub fn run() -> (Value, Id) { (Value, CAPACITY) }
}
mod unused {
    use crate::data::{obsolete};
    fn unused() { obsolete(); }
}
fn main() { app::run(); }
"#;
    run_transformation_test(
        code,
        true,
        &["use crate::data::{Value, Id, CAPACITY};"],
        &["obsolete", "mod unused"],
    );
}

#[test]
fn enum_prefix_imports_survive_construction_and_pattern_matching() {
    let code = r#"
mod data {
    pub enum JobStatus { Waiting, Finished(i32) }
    pub struct Job { pub status: JobStatus }
    pub struct Unused;
}
mod app {
    use crate::data::{Job, JobStatus, Unused};
    pub fn reset(job: &mut Job) { job.status = JobStatus::Waiting; }
    pub fn finish(job: &mut Job) { job.status = JobStatus::Finished(7); }
}
mod reports {
    use crate::data::{Job, JobStatus, Unused};
    pub fn result(job: &Job) -> i32 {
        match job.status {
            JobStatus::Waiting => 0,
            JobStatus::Finished(value) => value,
        }
    }
}
fn main() {
    let mut job = data::Job { status: data::JobStatus::Waiting };
    app::reset(&mut job);
    app::finish(&mut job);
    reports::result(&job);
}
"#;
    run_transformation_test(
        code,
        true,
        &["use crate::data::{Job, JobStatus};"],
        &["Unused"],
    );
}

#[test]
fn renamed_enum_and_type_alias_prefix_imports_are_retained() {
    let code = r#"
mod data {
    pub enum State { Ready, Done(i32) }
    pub type Alias = State;
    pub struct Unused;
}
mod app {
    use crate::data::{State as Mode, Alias as StateAlias, Unused};
    pub fn run() -> i32 {
        let ready = Mode::Ready;
        let done = StateAlias::Done(3);
        match (ready, done) {
            (Mode::Ready, StateAlias::Done(value)) => value,
            _ => 0,
        }
    }
}
fn main() { app::run(); }
"#;
    run_transformation_test(
        code,
        true,
        &[
            "State as Mode",
            "Alias as StateAlias",
            "pub type Alias = State;",
        ],
        &["Unused"],
    );
}

#[test]
fn direct_variant_imports_retain_the_enclosing_enum() {
    for (variant, expression, pattern) in [
        ("Ready", "Ready", "Ready"),
        ("Done", "Done(1)", "Done(_)"),
        ("Named", "Named { value: 1 }", "Named { value: _ }"),
    ] {
        let code = format!(
            r#"
mod data {{
    pub enum State {{ Ready, Done(i32), Named {{ value: i32 }} }}
}}
use crate::data::State::{variant};
fn main() {{
    let value = {expression};
    match value {{ {pattern} => {{}}, _ => {{}} }}
}}
"#
        );
        run_transformation_test(
            &code,
            true,
            &[
                "pub enum State",
                &format!("use crate::data::State::{variant};"),
            ],
            &[],
        );
    }
}

#[test]
fn function_local_grouped_io_imports_keep_types_and_traits() {
    let code = r#"
fn main() {
    use std::io::{Read, Seek, SeekFrom, Write};
    let mut stream = std::io::Cursor::new([0u8]);
    stream.write_all(b"a").unwrap();
    stream.seek(SeekFrom::Start(0)).unwrap();
    let mut buffer = [0u8];
    stream.read_exact(&mut buffer).unwrap();
}
"#;
    run_transformation_test(
        code,
        true,
        &["use std::io::{Read, Seek, SeekFrom, Write};"],
        &[],
    );
}

#[test]
fn grouped_imports_used_by_methods_and_closures_remain_in_scope() {
    let code = r#"
mod data {
    pub const VALUE: i32 = 7;
    pub type ResultValue = i32;
}
mod app {
    use crate::data::{VALUE, ResultValue};
    pub struct Receiver;
    impl Receiver {
        pub fn run() -> ResultValue { VALUE + (|| VALUE)() }
    }
}
fn main() { app::Receiver::run(); }
"#;
    run_transformation_test(code, true, &["use crate::data::{VALUE, ResultValue};"], &[]);
}

#[test]
fn nested_import_groups_preserve_self_and_renamed_leaves() {
    let code = r#"
mod data {
    pub const CAPACITY: usize = 4;
    pub mod nested {
        pub struct Value;
        pub fn run() -> usize { 1 }
        pub fn obsolete() {}
    }
}
mod app {
    use crate::data::{self as imported, nested::{Value as Renamed, obsolete}, CAPACITY};
    pub fn run() -> (Renamed, usize) { (Renamed, imported::nested::run() + CAPACITY) }
}
fn main() { app::run(); }
"#;
    run_transformation_test(
        code,
        true,
        &["self as imported", "Value as Renamed", "CAPACITY"],
        &["obsolete"],
    );
}

#[test]
fn grouped_trait_imports_follow_reachable_method_calls() {
    let code = r#"
mod traits {
    pub trait Required { fn value(&self) -> i32 { 7 } }
    pub trait Unused { fn unused(&self) {} }
    pub struct Receiver;
    pub struct UnusedReceiver;
    impl Required for Receiver {}
    impl Unused for UnusedReceiver {}
}
mod app {
    use crate::traits::{Receiver, Required as _, Unused};
    pub fn run() -> i32 { Receiver.value() }
}
fn removed() {
    use crate::traits::{Unused, UnusedReceiver};
    UnusedReceiver.unused();
}
fn main() { app::run(); }
"#;
    run_transformation_test(
        code,
        true,
        &["Required as _", "trait Required", "fn value("],
        &["Unused", "fn removed("],
    );
}

#[test]
fn grouped_reexports_keep_live_types_across_modules() {
    for visibility in ["pub", "pub(crate)"] {
        let code = format!(
            r#"
mod data {{
    pub struct Value {{ pub number: i32 }}
    pub type Alias = Value;
    pub fn obsolete() {{}}
}}
mod facade {{
    {visibility} use crate::data::{{Alias, Value, obsolete}};
}}
fn main() {{
    let value: facade::Value = facade::Alias {{ number: 7 }};
    let _number = value.number;
}}
"#
        );
        run_transformation_test(
            &code,
            true,
            &["use crate::data::{Alias, Value};"],
            &["obsolete"],
        );
    }
}

#[test]
fn private_grouped_imports_remain_visible_to_descendant_modules() {
    for code in [
        r#"
mod data { pub struct Value { pub number: i32 } }
mod facade {
    use crate::data::{Value as Alias};
    mod child {
        pub fn make() -> super::Alias { super::Alias { number: 1 } }
    }
    pub fn run() -> i32 { child::make().number }
}
fn main() { facade::run(); }
"#,
        r#"
mod data { pub struct Value { pub number: i32 } }
use crate::data::{Value as Alias};
mod child {
    pub fn make() -> crate::Alias { crate::Alias { number: 1 } }
}
fn main() { let value = child::make(); let _number = value.number; }
"#,
    ] {
        run_transformation_test(code, true, &["Value as Alias"], &[]);
    }
}

#[test]
fn grouped_globs_keep_live_reexports_and_remove_dead_import_scopes() {
    let code = r#"
mod data { pub fn entry() -> i32 { 1 } }
mod facade { pub use crate::data::*; }
mod app {
    use crate::facade::{self as alias, *};
    pub fn run() -> i32 { entry() + alias::entry() }
}
mod dead { pub fn obsolete() {} }
mod unused { use crate::dead::{*}; }
fn main() { app::run(); }
"#;
    run_transformation_test(
        code,
        true,
        &["self as alias", "pub use crate::data::*;", "fn entry()"],
        &["mod dead", "mod unused", "obsolete"],
    );
}

#[test]
fn nested_enum_globs_preserve_used_variants() {
    let code = r#"
mod data { pub enum Mode { First, Second } }
mod app {
    use crate::data::{Mode::{*}};
    pub fn run() -> crate::data::Mode { First }
}
fn main() { app::run(); }
"#;
    run_transformation_test(code, true, &["use crate::data::Mode::*;"], &[]);
}

#[test]
fn empty_glob_scopes_do_not_leave_dangling_imports() {
    let code = r#"
mod empty {}
use crate::empty::{*};
fn main() {}
"#;
    run_transformation_test(code, true, &["fn main()"], &["empty", "use crate"]);
}

#[test]
fn test_transformation_variant_reexport_used_from_other_module() {
    let code = r#"
mod a {
    pub enum E {
        A,
        B,
    }
    pub use E::A;
    pub use E::B;
}
mod b {
    use crate::a::A;
    pub fn f() -> crate::a::E {
        A
    }
}
fn main() {
    b::f();
}
"#;
    run_transformation_test(
        code,
        true,
        &["pub use E::A;", "fn f() -> crate::a::E"],
        &["pub use E::B;"],
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

#[test]
fn test_transformation_unused_auto_derived() {
    let code = r#"
struct S {
    _x: u32,
}
#[automatically_derived]
impl S {
    fn get_x(&self) -> u32 {
        self._x
    }
    fn set_x(&mut self, val: u32) {
        self._x = val;
    }
}
fn main() {
    let mut s = S { _x: 0 };
    s.set_x(1);
}
"#;
    run_transformation_test(
        code,
        true,
        &["fn main()", "fn get_x(", "fn set_x(", "struct S"],
        &[],
    );
}

fn run_test(code: &str, unsafe_fns: &[&str]) {
    utils::compilation::run_compiler_on_str(code, |tcx| {
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

#[test]
fn test_transformation_unused_used_attr() {
    let code = r#"
#[used]
static INIT: i32 = 42;
fn main() {}
"#;
    run_transformation_test(code, true, &["fn main()", "#[used]", "static INIT"], &[]);
}

fn run_exposed_test(code: &str, c_exposed_fns: &[&str], includes: &[&str], excludes: &[&str]) {
    let c_exposed_fns: FxHashSet<String> = c_exposed_fns.iter().map(|s| s.to_string()).collect();
    let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
        let config = super::Config {
            remove_unused: true,
            remove_no_mangle: false,
            remove_extern_c: false,
            replace_pub: false,
            c_exposed_fns,
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
fn test_transformation_export_name_exposed() {
    let code = r#"
#[export_name = "exposed"]
fn exposed_0() {}
fn other() {}
fn main() {
    exposed_0();
}
"#;
    run_exposed_test(
        code,
        &["exposed"],
        &["fn exposed_0()", "fn main()"],
        &["fn other()"],
    );
}

fn run_extern_c_test(code: &str, includes: &[&str], excludes: &[&str]) {
    let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
        let config = super::Config {
            remove_unused: false,
            remove_no_mangle: false,
            remove_extern_c: true,
            replace_pub: false,
            c_exposed_fns: FxHashSet::default(),
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
fn test_extern_c_fn_ptr_preserved() {
    let code = r#"
extern "C" fn f(x: i32) -> i32 {
    x
}
extern "C" fn g(x: i32) -> i32 {
    x + 1
}
fn main() {
    let p = f as extern "C" fn(i32) -> i32;
    g(0);
}
"#;
    run_extern_c_test(code, &["extern \"C\" fn f"], &["extern \"C\" fn g"]);
}

#[test]
fn test_extern_c_fn_in_static_array_preserved() {
    let code = r#"
extern "C" fn f() {}
extern "C" fn g() {}
#[used]
static INIT_ARRAY: [extern "C" fn(); 1] = [f];
fn main() {
    g();
}
"#;
    run_extern_c_test(code, &["extern \"C\" fn f"], &["extern \"C\" fn g"]);
}

#[test]
fn test_extern_c_variadic_preserved() {
    let code = r#"
#![feature(c_variadic)]
unsafe extern "C" fn f(_: i32, ...) {}
"#;
    run_extern_c_test(code, &["extern \"C\" fn f"], &[]);
}
