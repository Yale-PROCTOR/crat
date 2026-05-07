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

#[test]
fn test_ctype_masks_use_ascii_classification() {
    run_test(
        r#"
pub const _ISalnum: core::ffi::c_uint = 8;
pub const _ISalpha: core::ffi::c_uint = 1024;
pub const _ISspace: core::ffi::c_uint = 8192;

extern "C" {
    fn __ctype_b_loc() -> *mut *const core::ffi::c_ushort;
}

pub unsafe fn foo(mut c: core::ffi::c_char) -> core::ffi::c_int {
    let mut n = 0;
    if *(*__ctype_b_loc()).offset(c as core::ffi::c_int as isize) as core::ffi::c_int
        & _ISalnum as core::ffi::c_int as core::ffi::c_ushort as core::ffi::c_int
        != 0
    {
        n += 1;
    }
    if *(*__ctype_b_loc()).offset(c as core::ffi::c_int as isize) as core::ffi::c_int
        & _ISalpha as core::ffi::c_int as core::ffi::c_ushort as core::ffi::c_int
        != 0
    {
        n += 1;
    }
    if *(*__ctype_b_loc()).offset(c as core::ffi::c_int as isize) as core::ffi::c_int
        & _ISspace as core::ffi::c_int as core::ffi::c_ushort as core::ffi::c_int
        != 0
    {
        n += 1;
    }
    n
}
        "#,
        &[
            ".is_ascii_alphanumeric()",
            ".is_ascii_alphabetic()",
            "matches!",
            "0x0b",
        ],
        &[
            ".is_alphanumeric()",
            ".is_alphabetic()",
            ".is_whitespace()",
            ".is_ascii_whitespace()",
        ],
    );
}

#[test]
fn test_trig_abs_and_difftime_calls_use_safe_replacements() {
    run_test(
        r#"
extern "C" {
    fn abs(__x: core::ffi::c_int) -> core::ffi::c_int;
    fn sin(__x: core::ffi::c_double) -> core::ffi::c_double;
    fn cos(__x: core::ffi::c_double) -> core::ffi::c_double;
    fn atan2(__y: core::ffi::c_double, __x: core::ffi::c_double) -> core::ffi::c_double;
    fn difftime(__time1: core::ffi::c_long, __time0: core::ffi::c_long) -> core::ffi::c_double;
}

pub unsafe fn foo(mut i: core::ffi::c_int, mut x: f64, mut y: f64) -> f64 {
    abs(i) as f64 + sin(x) + cos(y) + atan2(y, x) + difftime(i as core::ffi::c_long, 0)
}
        "#,
        &[
            "i.abs()",
            "x.sin()",
            "y.cos()",
            "y.atan2(x)",
            "(i as core::ffi::c_long) as f64 - 0 as f64",
        ],
        &["abs(i)", "sin(x)", "cos(y)", "atan2(y, x)", "difftime(i"],
    );
}
