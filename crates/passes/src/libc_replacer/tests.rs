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
fn test_offset_memory_calls_use_slice_replacements() {
    run_test(
        r#"
extern "C" {
    fn memcpy(__dest: *mut core::ffi::c_void, __src: *const core::ffi::c_void, __n: usize) -> *mut core::ffi::c_void;
    fn memmove(__dest: *mut core::ffi::c_void, __src: *const core::ffi::c_void, __n: usize) -> *mut core::ffi::c_void;
    fn memset(__s: *mut core::ffi::c_void, __c: core::ffi::c_int, __n: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn foo(mut src: &[u8], mut dst: &mut [u8]) {
    memcpy(dst.as_mut_ptr().offset(2) as *mut _, src.as_ptr().offset(1) as *const _, 4);
    memmove(dst.as_mut_ptr().offset(1) as *mut _, dst.as_ptr() as *const _, 4);
    memset(dst.as_mut_ptr().offset(6) as *mut _, 0, 2);
}
        "#,
        &[
            "copy_from_slice",
            "let ___tmp",
            ".to_vec()",
            ".fill",
            "(2) as",
            "(6) as usize..",
        ],
        &[
            "memcpy(dst.as_mut_ptr",
            "memmove(dst.as_mut_ptr",
            "memset(dst.as_mut_ptr",
        ],
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
fn test_string_compare_copy_and_concat_use_c_lib_helpers() {
    run_test(
        r#"
extern "C" {
    fn strcmp(__s1: *const i8, __s2: *const i8) -> i32;
    fn strncmp(__s1: *const i8, __s2: *const i8, __n: usize) -> i32;
    fn strcpy(__dest: *mut i8, __src: *const i8) -> *mut i8;
    fn strcat(__dest: *mut i8, __src: *const i8) -> *mut i8;
    fn strncat(__dest: *mut i8, __src: *const i8, __n: usize) -> *mut i8;
}

pub unsafe fn foo(mut src: &[i8]) -> i32 {
    let mut dst = [0i8; 32];
    strcpy(dst.as_mut_ptr(), src.as_ptr());
    strcat(dst.as_mut_ptr(), b"-\0" as *const u8 as *const i8);
    strncat(dst.as_mut_ptr(), b"xxy\0" as *const u8 as *const i8, 2);
    strcmp(dst.as_ptr(), b"abc-xx\0" as *const u8 as *const i8)
        + strncmp(dst.as_ptr(), src.as_ptr(), 3)
}
        "#,
        &[
            "crate::c_lib::strcpy",
            "crate::c_lib::strcat",
            "crate::c_lib::strncat",
            "crate::c_lib::strcmp",
            "crate::c_lib::strncmp",
        ],
        &[
            "strcmp(dst.as_ptr",
            "strncmp(dst.as_ptr",
            "strcpy(dst.as_mut_ptr",
            "strcat(dst.as_mut_ptr",
            "strncat(dst.as_mut_ptr",
        ],
    );
}

#[test]
fn test_string_stdio_rewrites_safe_slice_calls() {
    run_test(
        r#"
extern "C" {
    fn sprintf(__s: *mut i8, __format: *const i8, ...) -> i32;
    fn snprintf(__s: *mut i8, __maxlen: usize, __format: *const i8, ...) -> i32;
    fn sscanf(__s: *const i8, __format: *const i8, ...) -> i32;
}

pub unsafe fn foo(mut input: &[i8], mut n: i32) -> i32 {
    let mut buf = [0i8; 64];
    let a = sprintf(buf.as_mut_ptr(), b"x%d\0" as *const u8 as *const i8, n);
    let b = snprintf(buf.as_mut_ptr(), 64, b"%04x\0" as *const u8 as *const i8, n);
    let c = sscanf(input.as_ptr(), b"%d\0" as *const u8 as *const i8, &raw mut n);
    a + b + c
}
        "#,
        &[
            "std::fmt::format(format_args!",
            "std::io::Cursor::new",
            "crate::c_lib::sscanf_scan_d",
            "crate::c_lib::Xu32",
        ],
        &[
            "sprintf(buf.as_mut_ptr",
            "snprintf(buf.as_mut_ptr",
            "sscanf(input.as_ptr",
        ],
    );
}

#[test]
fn test_string_stdio_skips_raw_and_unsupported_calls() {
    run_test(
        r#"
extern "C" {
    fn sprintf(__s: *mut i8, __format: *const i8, ...) -> i32;
    fn sscanf(__s: *const i8, __format: *const i8, ...) -> i32;
}

pub unsafe fn foo(mut out: *mut i8, mut input: &[i8], mut n: i32, mut consumed: usize) {
    sprintf(out, b"%d\0" as *const u8 as *const i8, n);
    sscanf(input.as_ptr(), b"%d%zn\0" as *const u8 as *const i8, &raw mut n, &raw mut consumed);
}
        "#,
        &["sprintf(out", "sscanf(input.as_ptr"],
        &["std::io::Cursor::new"],
    );
}

#[test]
fn test_string_and_memory_searches_use_safe_replacements() {
    run_test(
        r#"
extern "C" {
    fn strchr(__s: *const i8, __c: i32) -> *mut i8;
    fn strrchr(__s: *const i8, __c: i32) -> *mut i8;
    fn strstr(__haystack: *const i8, __needle: *const i8) -> *mut i8;
    fn memchr(__s: *const core::ffi::c_void, __c: i32, __n: usize) -> *mut core::ffi::c_void;
    fn memcmp(__s1: *const core::ffi::c_void, __s2: *const core::ffi::c_void, __n: usize) -> i32;
}

pub unsafe fn foo(mut s: &[i8], mut bytes: &[u8]) -> i32 {
    (!strchr(s.as_ptr(), 'x' as i32).is_null()) as i32
        + (!strrchr(s.as_ptr(), 'y' as i32).is_null()) as i32
        + (!strstr(s.as_ptr(), b"zz\0" as *const u8 as *const i8).is_null()) as i32
        + (!memchr(bytes.as_ptr() as *const _, 7, bytes.len()).is_null()) as i32
        + memcmp(bytes.as_ptr() as *const _, b"abc\0" as *const u8 as *const _, 3)
}
        "#,
        &[
            "from_bytes_until_nul",
            "crate::c_lib::strstr",
            "crate::c_lib::memchr",
            "crate::c_lib::memcmp",
        ],
        &[
            "strchr(s.as_ptr",
            "strrchr(s.as_ptr",
            "strstr(s.as_ptr",
            "memchr(bytes.as_ptr",
            "memcmp(bytes.as_ptr",
        ],
    );
}

#[test]
fn test_strcspn_accepts_byte_string_reject_set() {
    run_test(
        r#"
extern "C" {
    fn strcspn(__s: *const i8, __reject: *const i8) -> usize;
}

pub unsafe fn foo() -> usize {
    let mut input = [0i8; 16];
    input[0] = b'a' as i8;
    input[1] = b'\n' as i8;
    strcspn(input.as_ptr(), b"\n\0" as *const u8 as *const i8)
}
        "#,
        &["from_bytes_until_nul", "b\"\\n\\0\"", "take_while"],
        &["strcspn(input.as_ptr"],
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
fn test_exit_and_time_calls_use_safe_replacements() {
    run_test(
        r#"
type time_t = i64;

extern "C" {
    fn exit(__status: i32);
    fn time(__timer: *mut time_t) -> time_t;
}

pub unsafe fn foo() -> time_t {
    let mut current_time: time_t = 0;
    time(&raw mut current_time);
    let now: time_t = time(std::ptr::null_mut());
    if now < current_time {
        exit(1);
    }
    now
}
        "#,
        &[
            "std::process::exit",
            "std::time::SystemTime::now()",
            "std::time::UNIX_EPOCH",
            "current_time = ___time",
        ],
        &["time(&raw", "time(std::ptr::null_mut", "exit(1);"],
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
