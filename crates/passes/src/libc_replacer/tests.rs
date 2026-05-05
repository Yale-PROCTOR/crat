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

#[test]
fn test_strncpy_from_short_slice_caps_copy_len() {
    run_test(
        r#"
extern "C" {
    fn strncpy(__dest: *mut i8, __src: *const i8, __n: usize) -> *mut i8;
}

pub unsafe fn copy_name(mut src: &[i8]) {
    let mut dst = [1i8; 64];
    strncpy(dst.as_mut_ptr(), src.as_ptr(), 63);
}
        "#,
        &[
            "std::ptr::write_bytes(___dst, 0, ___n)",
            "std::ptr::copy_nonoverlapping(___src.as_ptr(), ___dst, ___len)",
            "position(|&___c|",
            "___c == 0",
            ".min(___n)",
        ],
        &["copy_from_slice(&src[..63])"],
    );
}
