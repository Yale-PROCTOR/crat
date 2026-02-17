fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
    let res = utils::compilation::run_compiler_on_str(code, super::replace_libc).unwrap();
    utils::compilation::run_compiler_on_str(&res.code, utils::type_check).expect(&res.code);
    for include in includes {
        assert!(
            res.code.contains(include),
            "Expected to find `{include}` in:\n{}",
            res.code
        );
    }
    for exclude in excludes {
        assert!(
            !res.code.contains(exclude),
            "Expected not to find `{exclude}` in:\n{}",
            res.code
        );
    }
}

#[test]
fn test_memcpy_autoref() {
    run_test(
        r#"
extern "C" {
    fn memcpy(__dest: *mut core::ffi::c_void, __src: *const core::ffi::c_void, __n: usize) -> *mut core::ffi::c_void;
}
#[repr(C)]
pub struct s {
    pub buf: [core::ffi::c_uchar; 10],
}
pub unsafe extern "C" fn foo(mut p: *mut s, mut q: *mut s) {
    memcpy(
        ((*p).buf).as_mut_ptr() as *mut core::ffi::c_void,
        ((*q).buf).as_mut_ptr() as *const core::ffi::c_void,
        10,
    );
}
        "#,
        &["&mut", "&(", "copy_from_slice"],
        &[],
    );
}
