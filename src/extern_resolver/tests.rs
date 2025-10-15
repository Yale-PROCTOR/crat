fn run_test(code1: &str, code2: &str, same: bool) {
    let code = format!("#![feature(extern_types)] mod a {{ {code1} }} mod b {{ {code2} }}");
    utils::compilation::run_compiler_on_str(&code, |tcx| {
        let res = super::resolve(tcx);
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
