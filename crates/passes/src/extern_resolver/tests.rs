fn run_test(code1: &str, code2: &str, same: bool) {
    let code = format!("#![feature(extern_types)] mod a {{ {code1} }} mod b {{ {code2} }}");
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let res = super::resolve(false, false, tcx);
        for classes in res.equiv_adts.values() {
            if same {
                assert_eq!(classes.0.len(), 1);
            } else {
                for class in &classes.0 {
                    assert_eq!(class.len(), 1);
                }
            }
        }
    })
    .unwrap();
}

#[test]
fn test_simple() {
    let code1 = "
    pub struct s {
        x: i32,
    }
";
    let code2 = "
    pub struct s {
        x: i32,
    }
";
    run_test(code1, code2, true);
}

#[test]
fn test_simple_diff() {
    let code1 = "
    pub struct s {
        x: i32,
    }
";
    let code2 = "
    pub struct s {
        x: u32,
    }
";
    run_test(code1, code2, false);
}

#[test]
fn test_unnamed() {
    let code1 = "
    pub struct C2RustUnnamed {
        x: i32,
    }
    pub struct s {
        x: C2RustUnnamed,
        y: i32,
    }
";
    let code2 = "
    pub struct C2RustUnnamed_0 {
        x: i32,
    }
    pub struct s {
        x: C2RustUnnamed_0,
        y: i32,
    }
";
    run_test(code1, code2, true);
}

#[test]
fn test_unnamed_diff() {
    let code1 = "
    pub struct C2RustUnnamed {
        x: i32,
    }
    pub struct s {
        x: C2RustUnnamed,
        y: i32,
    }
";
    let code2 = "
    pub struct C2RustUnnamed_0 {
        x: i32,
    }
    pub struct s {
        x: C2RustUnnamed_0,
        y: u32,
    }
";
    run_test(code1, code2, false);
}

#[test]
fn test_recursion() {
    let code1 = "
    pub struct s {
        x: *mut s,
        y: i32,
    }
";
    let code2 = "
    pub struct s {
        x: *mut s,
        y: i32,
    }
";
    run_test(code1, code2, true);
}

#[test]
fn test_recursion_diff() {
    let code1 = "
    pub struct s {
        x: *mut s,
        y: i32,
    }
";
    let code2 = "
    pub struct s {
        x: *mut s,
        y: u32,
    }
";
    run_test(code1, code2, false);
}

#[test]
fn test_mutual_recursion() {
    let code1 = "
    pub struct s {
        x: *mut t,
        y: i32,
    }
    pub struct t {
        x: *mut s,
        y: i32,
    }
";
    let code2 = "
    pub struct s {
        x: *mut t,
        y: i32,
    }
    pub struct t {
        x: *mut s,
        y: i32,
    }
";
    run_test(code1, code2, true);
}

#[test]
fn test_mutual_recursion_diff() {
    let code1 = "
    pub struct s {
        x: *mut t,
        y: i32,
    }
    pub struct t {
        x: *mut s,
        y: i32,
    }
";
    let code2 = "
    pub struct s {
        x: *mut t,
        y: i32,
    }
    pub struct t {
        x: *mut s,
        y: u32,
    }
";
    run_test(code1, code2, false);
}

#[test]
fn test_unnamed_recursion() {
    let code1 = "
    pub struct C2RustUnnamed {
        x: *mut s,
    }
    pub struct s {
        x: C2RustUnnamed,
        y: i32,
    }
";
    let code2 = "
    pub struct C2RustUnnamed_0 {
        x: *mut s,
    }
    pub struct s {
        x: C2RustUnnamed_0,
        y: i32,
    }
";
    run_test(code1, code2, true);
}

#[test]
fn test_unnamed_recursion_diff() {
    let code1 = "
    pub struct C2RustUnnamed {
        x: *mut s,
        y: i32,
    }
    pub struct s {
        x: C2RustUnnamed,
        y: i32,
    }
";
    let code2 = "
    pub struct C2RustUnnamed_0 {
        x: *mut s,
        y: u32,
    }
    pub struct s {
        x: C2RustUnnamed_0,
        y: i32,
    }
";
    run_test(code1, code2, false);
}

#[test]
fn test_extern() {
    let code1 = r#"
    extern "C" {
        pub type s;
    }
    pub struct t {
        x: *mut s,
        y: i32,
    }
"#;
    let code2 = "
    pub struct s {
        y: i32,
    }
    pub struct t {
        x: *mut s,
        y: i32,
    }
";
    run_test(code1, code2, true);
}

#[test]
fn test_extern_diff() {
    let code1 = r#"
    extern "C" {
        pub type s;
    }
    pub struct t {
        x: *mut s,
        y: i32,
    }
"#;
    let code2 = "
    pub struct s {
        y: i32,
    }
    pub struct t {
        x: *mut s,
        y: u32,
    }
";
    run_test(code1, code2, false);
}

#[test]
fn test_extern_recursion() {
    let code1 = r#"
    extern "C" {
        pub type s;
    }
    pub struct t {
        x: *mut s,
        y: i32,
    }
"#;
    let code2 = "
    pub struct s {
        x: *mut t,
        y: i32,
    }
    pub struct t {
        x: *mut s,
        y: i32,
    }
";
    run_test(code1, code2, true);
}

#[test]
fn test_extern_recursion_diff() {
    let code1 = r#"
    extern "C" {
        pub type s;
    }
    pub struct t {
        x: *mut s,
        y: i32,
    }
"#;
    let code2 = "
    pub struct s {
        x: *mut t,
        y: i32,
    }
    pub struct t {
        x: *mut s,
        y: u32,
    }
";
    run_test(code1, code2, false);
}

fn run_extern_test(code: &str, config: super::Config, includes: &[&str], excludes: &[&str]) {
    let s =
        utils::compilation::run_compiler_on_str(code, |tcx| super::resolve_extern(&config, tcx))
            .unwrap();
    utils::compilation::run_compiler_on_str(&s, utils::type_check).expect(&s);
    for include in includes {
        assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
    }
    for exclude in excludes {
        assert!(
            !s.contains(exclude),
            "Expected not to find `{exclude}` in:\n{s}"
        );
    }
}

fn run_const_test(code1: &str, code2: &str, same: bool) {
    let code = format!("mod a {{ {code1} }} mod b {{ {code2} }}");
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let res = super::resolve(false, false, tcx);
        assert!(!res.equiv_consts.is_empty());
        for classes in res.equiv_consts.values() {
            if same {
                assert_eq!(classes.0.len(), 1);
            } else {
                for class in &classes.0 {
                    assert_eq!(class.len(), 1);
                }
            }
        }
    })
    .unwrap();
}

#[test]
fn test_const() {
    let code1 = "
    pub const B: core::ffi::c_uint = 1;
";
    let code2 = "
    pub const B: core::ffi::c_uint = 1;
";
    run_const_test(code1, code2, true);
}

#[test]
fn test_const_diff_body() {
    let code1 = "
    pub const B: core::ffi::c_uint = 1;
";
    let code2 = "
    pub const B: core::ffi::c_uint = 2;
";
    run_const_test(code1, code2, false);
}

#[test]
fn test_const_resolved_use() {
    run_extern_test(
        "
    mod a {
        pub const B: core::ffi::c_uint = 1;
    }
    mod b {
        pub const B: core::ffi::c_uint = 1;
        pub unsafe extern \"C\" fn bar() -> core::ffi::c_uint {
            return B;
        }
    }
",
        super::Config::default(),
        &["use crate::a::B;"],
        &["mod b {\n        pub const B"],
    );
}

#[test]
fn test_ignore_param_type() {
    run_extern_test(
        "
    #![feature(extern_types)]
    mod a {
        extern \"C\" {
            pub fn bar(_: *mut core::ffi::c_float) -> core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern \"C\" fn foo() -> core::ffi::c_int {
            let mut x: [core::ffi::c_float; 10] = [0.; 10];
            return bar(x.as_mut_ptr());
        }
    }
    mod b {
        #[no_mangle]
        pub unsafe extern \"C\" fn bar(mut x: *mut core::ffi::c_double)
            -> core::ffi::c_int {
            return *x.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int;
        }
    }
",
        super::Config {
            ignore_param_type: true,
            ..Default::default()
        },
        &["as *mut f64", "use crate::b::bar"],
        &["extern \"C\" {", "as *mut f32 as *mut f64"],
    );
}

#[test]
fn test_ignore_param_type_ref_arg_casts_via_resolved_extern_type() {
    run_extern_test(
        "
    #![feature(extern_types)]
    mod b {
        #[repr(C)]
        pub struct s {
            pub a: core::ffi::c_int,
        }
        #[no_mangle]
        pub unsafe extern \"C\" fn bar(mut x: *mut s) -> core::ffi::c_int {
            return (*x).a;
        }
        #[no_mangle]
        pub unsafe extern \"C\" fn baz(mut x: *const s) -> core::ffi::c_int {
            return (*x).a;
        }
    }
    mod y {
        #[repr(C)]
        pub struct s {
            pub a: core::ffi::c_int,
            pub b: core::ffi::c_int,
        }
    }
    mod z {
        #[repr(C)]
        pub struct s {
            pub a: core::ffi::c_int,
            pub b: core::ffi::c_int,
        }
        extern \"C\" {
            pub fn bar(_: *mut s) -> core::ffi::c_int;
            pub fn baz(_: *const s) -> core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern \"C\" fn foo() -> core::ffi::c_int {
            let mut x: s = s { a: 1, b: 2 };
            return bar(&mut x) + baz(&mut x);
        }
    }
",
        super::Config {
            ignore_param_type: true,
            ..Default::default()
        },
        &[
            "as *mut crate::y::s as *mut crate::b::s",
            "as *const crate::y::s as *const crate::b::s",
            "use crate::b::bar",
            "use crate::b::baz",
            "use crate::y::s",
        ],
        &["extern \"C\" {"],
    );
}

#[test]
fn test_ignore_param_type_resolved_adt() {
    run_extern_test(
        "
    #![feature(extern_types)]
    mod a {
        #[repr(C)]
        pub struct s {
            pub a: core::ffi::c_int,
        }
        extern \"C\" {
            pub fn bar(_: *mut s) -> core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern \"C\" fn foo() -> core::ffi::c_int {
            let mut x: s = s { a: 0 };
            return bar(&mut x);
        }
    }
    mod b {
        #[repr(C)]
        pub struct s {
            pub a: core::ffi::c_int,
        }
        #[no_mangle]
        pub unsafe extern \"C\" fn bar(mut x: *mut s) -> core::ffi::c_int {
            return (*x).a;
        }
    }
",
        super::Config {
            ignore_param_type: true,
            ..Default::default()
        },
        &["use crate::b::bar"],
        &["extern \"C\" {", " as "],
    );
}
