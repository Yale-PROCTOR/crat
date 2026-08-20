use super::*;

fn rewrite_with_config(code: &str, config: &Config) -> (String, BytemuckDependency) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| replace_local_borrows(config, tcx))
        .unwrap()
}

fn rewrite_struct_arrays_with_config(code: &str, config: &Config) -> (String, bool) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| rewrite_struct_arrays(config, tcx))
        .unwrap()
}

fn rewrite_array_local_provenance_with_config(code: &str, config: &Config) -> (String, bool) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        rewrite_array_local_provenance(config, tcx)
    })
    .unwrap()
}

fn array_local_trace_events(code: &str) -> Vec<crate::rewriter::array_local_trace::TraceEvent> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        crate::rewriter::rewrite_array_local_provenance_trace(&Config::default(), tcx, true).1
    })
    .unwrap()
}

fn rewrite_struct_arrays_then_pointer(code: &str, config: &Config) -> (String, BytemuckDependency) {
    let (pre, changed) = rewrite_struct_arrays_with_config(code, config);
    let input = if changed { pre.as_str() } else { code };
    rewrite_with_config(input, config)
}

fn rewrite_struct_arrays_then_array_local_then_pointer(
    code: &str,
    config: &Config,
) -> (String, BytemuckDependency) {
    let (pre, struct_changed) = rewrite_struct_arrays_with_config(code, config);
    let input = if struct_changed { pre.as_str() } else { code };
    let (pre, array_changed) = rewrite_array_local_provenance_with_config(input, config);
    let input = if array_changed { pre.as_str() } else { input };
    rewrite_with_config(input, config)
}

fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
    let config = Config::default();
    let (s, _) = rewrite_with_config(code, &config);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    for include in includes {
        assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
    }
    for exclude in excludes {
        assert!(
            !s.contains(exclude),
            "Expected not to find `{exclude}` in:\n{s}",
        );
    }
}

fn run_test_with_config(code: &str, config: &Config, includes: &[&str], excludes: &[&str]) {
    let (s, _) = rewrite_with_config(code, config);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    for include in includes {
        assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
    }
    for exclude in excludes {
        assert!(
            !s.contains(exclude),
            "Expected not to find `{exclude}` in:\n{s}",
        );
    }
}

#[test]
fn test_local_ptr_to_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    return *q;
}
"#,
        &["&mut"],
        &["*mut"],
    );
}

#[test]
fn test_non_null_param_to_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(p: *const libc::c_int) -> libc::c_int {
    return *p;
}
"#,
        &["fn foo(p: &i32)", "return *p;"],
        &["Option<&i32>", "*const libc::c_int"],
    );
}

#[test]
fn test_param_null_check_before_deref_stays_optional() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(p: *const libc::c_int) -> libc::c_int {
    if p.is_null() {
        return 0 as libc::c_int;
    }
    return *p;
}
"#,
        &["p: Option<&i32>", "p.is_none()"],
        &["fn foo(p: &i32)"],
    );
}

#[test]
fn test_non_null_param_late_null_check_rewrites_false() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(p: *const libc::c_int) -> libc::c_int {
    let x = *p;
    if p.is_null() {
        return 0 as libc::c_int;
    }
    return x;
}
"#,
        &["fn foo(p: &i32)", "if false"],
        &["p.is_none()", "Option<&i32>"],
    );
}

#[test]
fn test_blocked_raw_state_param_gets_local_borrow_alias() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    pub buflen: i32,
    pub t: [u32; 2],
}

extern "C" {
    fn touch_state(state: *mut State);
    fn touch_words(words: *mut u32);
}

pub unsafe extern "C" fn update(mut S: *mut State) -> i32 {
    let mut left: i32 = (*S).buflen;
    (*S).t[0usize] = ((*S).t[0usize]).wrapping_add(1);
    let words: *mut u32 = ((*S).t).as_mut_ptr();
    touch_words(words);
    touch_state(S);
    return left + (*S).t[0usize] as i32;
}
"#,
        &[
            "pub unsafe extern \"C\" fn update(mut S: *mut crate::State)",
            "let __crat_borrowed_S = S.as_mut().unwrap();",
            "let mut left: i32 = __crat_borrowed_S.buflen;",
            "__crat_borrowed_S.t[0usize] =",
            "let mut words: *mut u32 = (__crat_borrowed_S.t).as_mut_ptr();",
            "return left + __crat_borrowed_S.t[0usize] as i32;",
        ],
        &[
            "pub unsafe extern \"C\" fn update(mut S: &mut State)",
            "let __crat_borrowed_S = unsafe",
            "let mut left: i32 = (*S).buflen;",
            "(*S).t[0usize]",
            "((*S).t).as_mut_ptr()",
        ],
    );
}

#[test]
fn test_reassigned_non_null_param_stays_optional() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(mut p: *const libc::c_int) -> libc::c_int {
    let x = *p;
    p = std::ptr::null();
    if p.is_null() {
        return x;
    }
    return *p;
}
"#,
        &["mut p: Option<&i32>", "p = None", "p.is_none()"],
        &["fn foo(mut p: &i32)"],
    );
}

#[test]
fn test_rewriter_output_unchanged_when_ownership_analysis_fails() {
    let code = r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    return *q;
}
"#;
    let baseline = rewrite_with_config(code, &Config::default());
    let fallback = rewrite_with_config(
        code,
        &Config {
            force_ownership_analysis_failure: true,
            ..Config::default()
        },
    );

    assert_eq!(fallback, baseline);
    ::utils::compilation::run_compiler_on_str(&fallback.0, ::utils::type_check).expect(&fallback.0);
}

#[test]
fn test_rewriter_rewrites_malloc_scalar_to_opt_box() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn foo() -> *mut i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 7;
    return p;
}
"#,
        &[
            "-> Box<i32>",
            "let mut p: Box<i32>",
            "Some(Box::new(<i32 as Default>::default()))",
            "return (Some(p)).unwrap();",
        ],
        &["Box::<i32>::new(", "Box::into_raw(", "Box::leak("],
    );
}

#[test]
fn test_rewriter_rewrites_owned_scalar_struct_field_to_opt_box() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

pub unsafe fn stash(owner: *mut Holder) {
    let data: *mut i32 = malloc(std::mem::size_of::<i32>());
    *data = 7;
    (*owner).data = data;
}
"#,
        &[
            "pub data: Option<Box<i32>>",
            "Box::from_raw((data) as *mut i32)",
        ],
        &["pub data: *mut i32", "(*owner).data = data;", "unsafe {"],
    );
}

#[test]
fn test_rewriter_drops_selected_owned_scalar_struct_field_free() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

pub unsafe fn stash(owner: *mut Holder) {
    let data: *mut i32 = malloc(std::mem::size_of::<i32>());
    (*owner).data = data;
}

pub unsafe fn release(owner: *mut Holder) {
    free((*owner).data as *mut core::ffi::c_void);
}
"#,
        &["pub data: Option<Box<i32>>", "drop(((*owner).data).take())"],
        &["free((*owner).data as *mut core::ffi::c_void);"],
    );
}

#[test]
fn test_rewriter_drops_nested_owned_scalar_struct_field_free() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

#[repr(C)]
pub struct Outer {
    pub inner: Holder,
}

pub unsafe fn stash(owner: *mut Outer) {
    (*owner).inner.data = malloc(std::mem::size_of::<i32>());
}

pub unsafe fn release(owner: *mut Outer) {
    free((*owner).inner.data as *mut core::ffi::c_void);
}
"#,
        &[
            "pub data: Option<Box<i32>>",
            "drop(((*owner).inner.data).take())",
        ],
        &["drop(((*owner).data).take())"],
    );
}

#[test]
fn test_rewriter_marks_local_owned_scalar_struct_field_free_mutable() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

pub unsafe fn stash(owner: *mut Holder) {
    (*owner).data = malloc(std::mem::size_of::<i32>());
}

pub unsafe fn release_local() {
    let h = Holder { data: malloc(std::mem::size_of::<i32>()) };
    free(h.data as *mut core::ffi::c_void);
}
"#,
        &["let mut h = Holder", "drop((h.data).take())"],
        &[
            "let h = crate::Holder",
            "free(h.data as *mut core::ffi::c_void);",
        ],
    );
}

#[test]
fn test_rewriter_keeps_unsupported_owned_scalar_struct_field_raw() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

pub unsafe fn stash(owner: *mut Holder) {
    (*owner).data = malloc(2 * std::mem::size_of::<i32>());
}
"#,
        &[
            "pub data: *mut i32",
            "malloc(2 * std::mem::size_of::<i32>())",
        ],
        &["pub data: Option<&", "pub data: Option<Box<i32>>"],
    );
}

#[test]
fn test_rewriter_removes_generated_copy_clone_for_owned_scalar_struct_field() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

pub unsafe fn stash(owner: *mut Holder) {
    (*owner).data = malloc(std::mem::size_of::<i32>());
}
"#,
        &["pub data: Option<Box<i32>>"],
        &["impl Copy for", "impl Clone for"],
    );
}

#[test]
fn test_rewriter_visits_impl_for_owned_scalar_struct_field() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

pub unsafe fn stash(owner: *mut Holder) {
    let data: *mut i32 = malloc(std::mem::size_of::<i32>());
    (*owner).data = data;
}

impl Holder {
    pub unsafe fn init(&mut self) {
        self.data = malloc(std::mem::size_of::<i32>());
    }
}
"#,
        &[
            "pub data: Option<Box<i32>>",
            "Box::from_raw((data) as *mut i32)",
            "self.data = Some(Box::new(<i32 as Default>::default()));",
        ],
        &["pub data: *mut i32", "self.data = malloc"],
    );
}

#[test]
fn test_rewriter_rewrites_malloc_casted_sizeof_local_struct_to_opt_box() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

pub unsafe fn make_state() -> *mut State {
    let mut state: *mut State = malloc(::core::mem::size_of::<State>() as usize) as *mut State;
    (*state).value = 7;
    state
}
"#,
        &[
            "pub unsafe fn make_state() -> Box<crate::State>",
            "let mut state: Box<crate::State>",
            "Some(Box::new(crate::State {",
        ],
        &[
            "malloc(::core::mem::size_of::<State>() as usize)",
            "Box::into_raw(",
            "Box::leak(",
        ],
    );
}

#[test]
fn test_rewriter_rewrites_calloc_casted_sizeof_local_struct_to_opt_box() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

pub unsafe fn make_state() -> *mut State {
    let mut state: *mut State =
        calloc(1 as usize, ::core::mem::size_of::<State>() as usize) as *mut State;
    (*state).value = 7;
    state
}
"#,
        &[
            "pub unsafe fn make_state() -> Box<crate::State>",
            "let mut state: Box<crate::State>",
            "Some(Box::new(crate::State {",
        ],
        &[
            "calloc(1 as usize, ::core::mem::size_of::<State>() as usize)",
            "Box::into_raw(",
            "Box::leak(",
        ],
    );
}

#[test]
fn test_rewriter_materializes_struct_box_with_raw_pointer_default() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct StructDefaultProbe {
    pub next: *mut i32,
    pub value: i32,
}

pub unsafe fn alloc_struct() -> *mut StructDefaultProbe {
    let mut state: *mut StructDefaultProbe =
        malloc(std::mem::size_of::<crate::StructDefaultProbe>()) as *mut crate::StructDefaultProbe;
    (*state).value = 7;
    state
}
"#,
        &[
            "pub unsafe fn alloc_struct() -> Box<crate::StructDefaultProbe>",
            "let mut state: Box<crate::StructDefaultProbe>",
            "Some(Box::new(crate::StructDefaultProbe {",
            "next: std::ptr::null_mut::<i32>()",
            "value: <i32 as Default>::default()",
        ],
        &[
            "malloc(std::mem::size_of::<crate::StructDefaultProbe>())",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_materializes_struct_box_with_large_array_defaults() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct StructArrayDefaultProbe {
    pub name: [i8; 64],
    pub nodes: [*mut i32; 100],
}

pub unsafe fn alloc_struct() -> *mut StructArrayDefaultProbe {
    let mut state: *mut StructArrayDefaultProbe =
        malloc(std::mem::size_of::<crate::StructArrayDefaultProbe>()) as *mut crate::StructArrayDefaultProbe;
    (*state).name[0] = 1;
    state
}
"#,
        &[
            "pub unsafe fn alloc_struct() -> Box<crate::StructArrayDefaultProbe>",
            "name: std::array::from_fn",
            "nodes: std::array::from_fn",
            "std::ptr::null_mut::<i32>()",
        ],
        &[
            "malloc(std::mem::size_of::<crate::StructArrayDefaultProbe>())",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_materializes_struct_box_with_union_default() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub union TypeConfusion {
    pub int_val: i32,
    pub float_val: f32,
}

#[repr(C)]
pub struct UnionHolderProbe {
    pub data: TypeConfusion,
    pub value: i32,
}

pub unsafe fn alloc_struct() -> *mut UnionHolderProbe {
    let mut state: *mut UnionHolderProbe =
        malloc(std::mem::size_of::<crate::UnionHolderProbe>()) as *mut crate::UnionHolderProbe;
    (*state).value = 7;
    state
}
"#,
        &[
            "pub unsafe fn alloc_struct() -> Box<crate::UnionHolderProbe>",
            "MaybeUninit::<crate::TypeConfusion>::zeroed().assume_init()",
            "value: <i32 as Default>::default()",
        ],
        &[
            "malloc(std::mem::size_of::<crate::UnionHolderProbe>())",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_rewrites_calloc_array_to_opt_boxed_slice() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut i32;
}

pub unsafe fn foo() -> *mut i32 {
    let mut p: *mut i32 = calloc(4, std::mem::size_of::<i32>());
    *p.offset(1) = 7;
    p
}
"#,
        &[
            "pub unsafe fn foo() -> Box<[i32]>",
            "let mut p: Box<[i32]>",
            "collect::<Vec<i32>>().into_boxed_slice()",
            "(&mut ((&mut (p)[..])[(1) as usize..]))[0] = 7;",
        ],
        &[
            "Box::leak(",
            "Box::into_raw(",
            "calloc(4, std::mem::size_of::<i32>())",
        ],
    );
}

#[test]
fn test_rewriter_materializes_calloc_array_as_direct_boxed_slice_value() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_arr() {
    let mut data: *mut i32 = calloc(4, std::mem::size_of::<i32>());
    *data.offset(1) = 7;
    free(data as *mut core::ffi::c_void);
}
"#,
        &[
            "pub unsafe fn alloc_arr()",
            "let mut data: Box<[i32]>",
            "collect::<Vec<i32>>().into_boxed_slice()",
            "drop(data);",
        ],
        &[
            "calloc(4, std::mem::size_of::<i32>())",
            "free(data as *mut core::ffi::c_void);",
            "Box::leak(",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_calloc_array_binding_as_boxed_slice_without_raw_downgrade() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut i32;
}

pub unsafe fn alloc_arr() -> *mut i32 {
    let mut data: *mut i32 = calloc(4, std::mem::size_of::<i32>());
    *data.offset(1) = 7;
    data
}
"#,
        &[
            "pub unsafe fn alloc_arr() -> Box<[i32]>",
            "let mut data: Box<[i32]>",
            "collect::<Vec<i32>>().into_boxed_slice()",
            "(&mut ((&mut (data)[..])[(1) as usize..]))[0] = 7;",
        ],
        &[
            "let mut data: *mut i32",
            "calloc(4, std::mem::size_of::<i32>())",
            "Box::leak(",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_rewrites_byte_calloc_size_to_opt_boxed_slice_len() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn make_buf(len: usize) -> *mut core::ffi::c_char {
    let p: *mut core::ffi::c_char = calloc(1, len) as *mut core::ffi::c_char;
    *p.offset(len.wrapping_sub(1) as isize) = 0;
    p
}
"#,
        &[
            "pub unsafe fn make_buf(len: usize) -> Box<[i8]>",
            ".take(((1) * (len) /",
            "std::mem::size_of::<i8>()) as",
        ],
        &["Box::leak(", "Box::into_raw(", "calloc(1, len)"],
    );
}

#[test]
fn test_rewriter_rewrites_malloc_array_to_opt_boxed_slice() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn foo() -> *mut i32 {
    let mut p: *mut i32 = malloc(4 * std::mem::size_of::<i32>());
    *p.offset(1) = 7;
    p
}
"#,
        &[
            "pub unsafe fn foo() -> Box<[i32]>",
            "let mut p: Box<[i32]>",
            "collect::<Vec<i32>>().into_boxed_slice()",
            "(&mut ((&mut (p)[..])[(1) as usize..]))[0] = 7;",
        ],
        &[
            "Box::leak(",
            "Box::into_raw(",
            "malloc(4 * std::mem::size_of::<i32>())",
        ],
    );
}

#[test]
fn test_rewriter_keeps_explicit_fn_pointer_return_signature_raw() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 5;
    return p;
}

pub unsafe fn call_it(f: unsafe fn() -> *mut i32) -> *mut i32 {
    return f();
}

pub unsafe fn foo() -> i32 {
    let p = call_it(alloc_one as unsafe fn() -> *mut i32);
    return *p;
}
"#,
        &[
            "pub unsafe fn alloc_one() -> *mut i32",
            "let mut p: Box<i32>",
            "Box::into_raw(p) as *mut i32",
        ],
        &[],
    );
}

#[test]
fn test_rewriter_converts_opt_box_call_result_into_opt_ref_param() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 5;
    return p;
}

pub unsafe fn take_raw(p: *mut i32) -> i32 {
    return *p;
}

pub unsafe fn foo() -> i32 {
    return take_raw(alloc_one());
}
"#,
        &["-> Box<i32>", ".as_ref()", "take_raw"],
        &[],
    );
}

#[test]
fn test_rewriter_converts_opt_boxed_slice_call_result_into_slice_param() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_many() -> *mut i32 {
    let mut p: *mut i32 = malloc(4 * std::mem::size_of::<i32>());
    *p.offset(1) = 5;
    p
}

pub unsafe fn take_raw(p: *mut i32) -> i32 {
    return *p.offset(1);
}

pub unsafe fn foo() -> i32 {
    return take_raw(alloc_many());
}
"#,
        &[
            "pub unsafe fn alloc_many() -> Box<[i32]>",
            "pub unsafe fn take_raw(p: &[i32])",
            "return take_raw(&(alloc_many())[..]);",
        ],
        &["std::slice::from_raw_parts(", "Box::leak("],
    );
}

#[test]
fn test_rewriter_rewrites_local_call_boundary_for_opt_box() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn id(mut p: *mut i32) -> *mut i32 {
    return p;
}

pub unsafe fn foo() -> *mut i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 7;
    let q: *mut i32 = id(p);
    return q;
}
"#,
        &[
            "pub unsafe fn id(mut p: Option<Box<i32>>) -> Option<Box<i32>>",
            "pub unsafe fn foo() -> Option<Box<i32>>",
            "let mut q: Option<Box<i32>> = id(Some(p));",
        ],
        &[],
    );
}

#[test]
fn test_rewriter_keeps_fn_pointer_scalar_return_raw_while_local_is_box() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn keep_raw() -> *mut i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 1;
    return p;
}

pub unsafe fn foo() {
    let fp: unsafe fn() -> *mut i32 = keep_raw;
    let _ = fp();
}
"#,
        &[
            "pub unsafe fn keep_raw() -> *mut i32",
            "let mut p: Box<i32>",
            "Box::into_raw(p) as *mut i32",
            "let fp: unsafe fn() -> *mut i32 = keep_raw;",
        ],
        &[],
    );
}

#[test]
fn test_rewriter_keeps_fn_pointer_array_return_raw_while_local_is_boxed_slice() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut i32;
}

pub unsafe fn keep_raw_arr() -> *mut i32 {
    let mut p: *mut i32 = calloc(4, std::mem::size_of::<i32>());
    *p.offset(1) = 7;
    p
}

pub unsafe fn foo() {
    let fp: unsafe fn() -> *mut i32 = keep_raw_arr;
    let _ = fp();
}
"#,
        &[
            "pub unsafe fn keep_raw_arr() -> *mut i32",
            "let mut p: Box<[i32]>",
            "Box::leak(p).as_mut_ptr()",
            "let fp: unsafe fn() -> *mut i32 = keep_raw_arr;",
        ],
        &["-> Option<Box<[i32]>>", "Box::into_raw("],
    );
}

#[test]
fn test_rewriter_rewrites_local_call_result_from_opt_box() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 5;
    return p;
}

pub unsafe fn caller() -> *mut i32 {
    let mut q: *mut i32 = alloc_one();
    *q = 9;
    return q;
}
"#,
        &[
            "fn alloc_one() -> Box<i32>",
            "fn caller() -> Box<i32>",
            "let mut q: Box<i32> = (Some(alloc_one())).unwrap();",
        ],
        &[],
    );
}

#[test]
fn test_rewriter_moves_opt_box_locals_with_take() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn move_owner() -> *mut i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 7;
    let q: *mut i32 = p;
    return q;
}
"#,
        &["let mut q: Box<i32> = (Some(p)).unwrap();"],
        &[],
    );
}

#[test]
fn test_rewriter_keeps_composite_realloc_struct_raw_across_return_and_call_result() {
    run_test(
        r#"
extern "C" {
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct Header {
    tag: i32,
}

pub unsafe fn make_header() -> *mut Header {
    let mut h: *mut Header = std::ptr::null_mut();
    h = realloc(
        std::ptr::null_mut(),
        std::mem::size_of::<Header>() + 16usize,
    ) as *mut Header;
    (*h).tag = 1;
    h
}

pub unsafe fn use_header() -> i32 {
    let mut h: *mut Header = make_header();
    let mut alias: *mut Header = std::ptr::null_mut();
    alias = h;
    return (*alias).tag;
}
"#,
        &[
            "pub unsafe fn make_header() -> *mut crate::Header",
            "let mut h: *mut crate::Header = make_header();",
            "let mut alias: *mut crate::Header = std::ptr::null_mut();",
            "alias = h;",
            "let mut h: *mut crate::Header = std::ptr::null_mut();",
        ],
        &["Option<Box<Header>>"],
    );
}

#[test]
fn test_rewriter_promotes_non_conflicting_local_struct_params() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    value: i32,
}

pub unsafe fn touch_state(s: *mut State) {
    (*s).value += 1;
}

pub unsafe fn caller(s: *mut State) {
    touch_state(s);
}
        "#,
        &["pub unsafe fn touch_state(mut s: &mut crate::State)"],
        &["pub unsafe fn touch_state(mut s: *mut crate::State)"],
    );
}

#[test]
fn test_rewriter_downgrades_local_struct_call_conflict_with_scalar_read() {
    run_test(
        r#"
#[repr(C)]
pub struct Tree {
    root_id: i32,
}

pub unsafe fn tree_print_helper(tree: *mut Tree, root_id: i32) {
    (*tree).root_id = root_id;
}

pub unsafe fn caller(tree: *mut Tree) {
    tree_print_helper(tree, (*tree).root_id);
}
        "#,
        &["pub unsafe fn tree_print_helper(mut tree: *mut crate::Tree, root_id: i32)"],
        &["pub unsafe fn tree_print_helper(mut tree: &mut crate::Tree"],
    );
}

#[test]
fn test_rewriter_downgrades_local_struct_call_conflict_with_field_borrow() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut State;
}

#[repr(C)]
pub struct State {
    value: i32,
    buf: [i32; 4],
}

pub unsafe fn touch_state(s: *mut State, buf: *mut i32) -> i32 {
    *buf = (*s).value;
    return (*s).value;
}

pub unsafe fn caller() -> i32 {
    let mut s: *mut State = malloc(std::mem::size_of::<State>());
    (*s).value = 3;
    return touch_state(s, ((*s).buf).as_mut_ptr());
        }
	"#,
        &["pub unsafe fn touch_state(mut s: *mut crate::State, mut buf: &mut i32)"],
        &["pub unsafe fn touch_state(mut s: &crate::State"],
    );
}

#[test]
fn test_rewriter_downgrades_repeated_local_struct_field_call_conflict() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    flags: i32,
    fp: *mut i32,
}

pub unsafe fn get_data(flags: i32, fp: *mut i32) -> i32 {
    if !fp.is_null() {
        *fp = flags;
    }
    flags
}

pub unsafe fn caller(state: *mut State) -> i32 {
    get_data((*state).flags, (*state).fp)
}
        "#,
        &["pub unsafe fn caller(mut state: *mut crate::State) -> i32"],
        &["pub unsafe fn caller(mut state: &mut crate::State) -> i32"],
    );
}

#[test]
fn test_rewriter_allows_disjoint_mutable_local_struct_field_call_args() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    a: [i32; 4],
    b: [i32; 4],
    c: [i32; 4],
}

pub unsafe fn fill(a: *mut i32, b: *mut i32, c: *mut i32) {
    *a = 1;
    *b = 2;
    *c = 3;
}

pub unsafe fn caller(s: *mut State) {
    fill((*s).a.as_mut_ptr(), (*s).b.as_mut_ptr(), (*s).c.as_mut_ptr());
}
        "#,
        &[
            "pub unsafe fn fill(mut a: &mut i32, mut b: &mut i32, mut c: &mut i32)",
            "pub unsafe fn caller(mut s: &mut crate::State)",
        ],
        &["pub unsafe fn caller(mut s: *mut crate::State)"],
    );
}

#[test]
fn test_rewriter_keeps_local_struct_callee_promoted_for_raw_field_pointer_bridge() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    value: i32,
    buf: [i32; 4],
}

pub unsafe fn touch_state(s: *mut State, buf: *const i32) -> i32 {
    (*s).value += *buf;
    return (*s).value;
}

pub unsafe fn caller(s: *mut State) -> i32 {
    touch_state(s, (*s).buf.as_ptr())
}
        "#,
        &[
            "pub unsafe fn touch_state(mut s: &mut crate::State, buf: &i32) -> i32",
            "pub unsafe fn caller(mut s: *mut crate::State) -> i32",
        ],
        &["pub unsafe fn touch_state(mut s: *mut crate::State"],
    );
}

#[test]
fn test_rewriter_keeps_shared_local_struct_array_field_as_mut_ptr_views_safe() {
    run_test(
        r#"
#[repr(C)]
pub struct s {
    pub buffer: [core::ffi::c_int; 3],
}

#[no_mangle]
pub unsafe extern "C" fn foo(mut p: *mut core::ffi::c_int) -> core::ffi::c_int {
    return *p.offset(0 as core::ffi::c_int as isize)
        + *p.offset(1 as core::ffi::c_int as isize);
}

#[no_mangle]
pub unsafe extern "C" fn qux(mut p: *mut core::ffi::c_int) -> core::ffi::c_int {
    *p.offset(0 as core::ffi::c_int as isize) = 1 as core::ffi::c_int;
    *p.offset(1 as core::ffi::c_int as isize) = 1 as core::ffi::c_int;
    return 1 as core::ffi::c_int;
}

#[no_mangle]
pub unsafe extern "C" fn bar(mut sp: *mut s) -> core::ffi::c_int {
    let mut x: core::ffi::c_int = 0 as core::ffi::c_int;
    x += foo(((*sp).buffer).as_mut_ptr());
    x += qux(((*sp).buffer).as_mut_ptr());
    return x;
}

#[no_mangle]
pub unsafe extern "C" fn baz(mut sp: *mut s) -> core::ffi::c_int {
    let mut x: core::ffi::c_int = 0 as core::ffi::c_int;
    let mut q: *mut core::ffi::c_int = ((*sp).buffer).as_mut_ptr();
    x += *q.offset(0 as core::ffi::c_int as isize)
        + *q.offset(1 as core::ffi::c_int as isize);
    let mut r: *mut core::ffi::c_int = &mut *((*sp).buffer)
        .as_mut_ptr()
        .offset(1 as core::ffi::c_int as isize) as *mut core::ffi::c_int;
    x += *r.offset(0 as core::ffi::c_int as isize)
        + *r.offset(1 as core::ffi::c_int as isize);
    x += foo(((*sp).buffer).as_mut_ptr());
    x += foo(&mut *((*sp).buffer).as_mut_ptr().offset(1 as core::ffi::c_int as isize));
    x += foo(((*sp).buffer).as_mut_ptr().offset(1 as core::ffi::c_int as isize));
    return x;
}
        "#,
        &[
            "pub unsafe extern \"C\" fn bar(mut sp: &mut crate::s)",
            "pub unsafe extern \"C\" fn baz(mut sp: &crate::s)",
            "let mut q: &[i32]",
            "let mut r: &[i32]",
            "foo(&",
        ],
        &[
            "pub unsafe extern \"C\" fn baz(mut sp: *mut crate::s)",
            "std::slice::from_raw_parts",
        ],
    );
}

#[test]
fn test_rewriter_downgrades_long_lived_array_field_alias_with_local_offset_index() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    bitdepth: u32,
    cur_blocksize: u32,
    subframe_bitdepth: u32,
    residuals: [i32; 5],
}

pub unsafe fn decorrelate(t: *mut State) {
    let residuals_0: *mut i32 = ((*t).residuals).as_mut_ptr();
    let mut i: u32 = 0;
    (*t).subframe_bitdepth = (*t).bitdepth;
    while i < (*t).cur_blocksize && i <= 5 {
        *residuals_0.offset(i as isize) = i as i32;
        i += 1;
    }
}
        "#,
        &[
            "pub unsafe fn decorrelate(mut t: &mut crate::State)",
            "let mut residuals_0: &mut [i32]",
        ],
        &[
            "pub unsafe fn decorrelate(mut t: *mut crate::State)",
            "let mut residuals_0: *mut i32",
        ],
    );
}

#[test]
fn test_rewriter_allows_long_lived_raw_pointer_field_borrow() {
    run_test(
        r#"
#[repr(C)]
pub struct Image {
    w: i32,
    h: i32,
    pix: *mut u8,
}

pub unsafe fn premultiply(img: *mut Image) {
    let data: *mut u8 = (*img).pix;
    let w = (*img).w;
    let h = (*img).h;
    *data.offset((w * h - 1) as isize) = 0;
}
        "#,
        &["pub unsafe fn premultiply(mut img: &mut crate::Image)"],
        &["pub unsafe fn premultiply(mut img: *mut crate::Image)"],
    );
}

#[test]
fn test_rewriter_downgrades_local_struct_reborrow_assignment_conflict() {
    run_test(
        r#"
extern "C" {
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Node {
    next: *mut Node,
}

pub unsafe fn clear_list(head: *mut Node) {
    let mut x: *mut Node = head;
    let mut y: *mut Node = std::ptr::null_mut();
    while !x.is_null() {
        y = (*x).next;
        free(x as *mut core::ffi::c_void);
        x = y;
    }
}
        "#,
        &[
            "let mut x: *mut crate::Node<'a> =",
            "let mut y: *mut crate::Node<'a> = std::ptr::null_mut();",
        ],
        &["Option<&crate::Node>"],
    );
}

#[test]
fn test_rewriter_keeps_local_struct_field_mut_ptr_offset_root_shared() {
    run_test(
        r#"
#[repr(C)]
pub struct ResultItem {
    value: i32,
}

impl Copy for ResultItem {}

impl Clone for ResultItem {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
pub struct ResultArray {
    count: i32,
    data: [ResultItem; 4],
}

pub unsafe fn compare(arr: *mut ResultArray, idx: i32) -> i32 {
    let ptr: *mut ResultItem = (*arr).data.as_mut_ptr().offset(idx as isize);
    return (*ptr).value;
}
        "#,
        &[
            "pub unsafe fn compare(arr: &crate::ResultArray",
            "let ptr: Option<&crate::ResultItem>",
        ],
        &[
            "pub unsafe fn compare(mut arr: *mut crate::ResultArray",
            "let ptr: *mut crate::ResultItem",
            "std::slice::from_raw_parts",
        ],
    );
}

#[test]
fn test_rewriter_allows_local_struct_field_mut_ptr_on_mut_root() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    pos: usize,
    buffer: [u8; 8],
}

pub unsafe fn write_byte(d: *mut u8, value: u8) {
    *d = value;
}

pub unsafe fn add_sample(m: *mut State, value: u8) {
    write_byte((*m).buffer.as_mut_ptr().offset((*m).pos as isize), value);
    (*m).pos += 1;
}
        "#,
        &["pub unsafe fn add_sample(mut m: &mut crate::State"],
        &["pub unsafe fn add_sample(mut m: *mut crate::State"],
    );
}

#[test]
fn test_rewriter_rewrites_array_field_mut_ptr_alias_offset_to_slice_suffix() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    pos: usize,
    buffer: [u8; 8],
}

pub unsafe fn write_byte(d: *mut u8, value: u8) {
    *d = value;
    *d.offset(1) = value;
}

pub unsafe fn add_sample(m: *mut State, value: u8) {
    let p: *mut u8 = (*m).buffer.as_mut_ptr();
    write_byte(p.offset((*m).pos as isize), value);
    (*m).pos += 1;
}
        "#,
        &[
            "let mut p: &mut [u8]",
            "write_byte(&mut ((p)[(m.pos as isize) as usize..]), value)",
        ],
        &[
            "let p: *mut u8",
            ".buffer.as_mut_ptr()",
            "p.offset((*m).pos as isize)",
        ],
    );
}

#[test]
fn test_rewriter_keeps_array_field_mut_ptr_alias_raw_when_root_reuses_same_field() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    pos: usize,
    buffer: [u8; 8],
}

pub unsafe fn write_byte(d: *mut u8, value: u8) {
    *d = value;
    *d.offset(1) = value;
}

pub unsafe fn add_sample(m: *mut State, value: u8) {
    let p: *mut u8 = (*m).buffer.as_mut_ptr();
    (*m).buffer[0] = value;
    write_byte(p.offset((*m).pos as isize), value);
}
        "#,
        &["let mut p: *mut u8"],
        &["let mut p: &mut [u8]"],
    );
}

#[test]
fn test_rewriter_downgrades_static_local_struct_array_projection() {
    run_test(
        r#"
#[repr(C)]
pub struct Node {
    id: i32,
}

impl Copy for Node {}

impl Clone for Node {
    fn clone(&self) -> Self {
        *self
    }
}

static mut NODE_STORAGE: [Node; 4] = [Node { id: 0 }; 4];

pub unsafe fn last_node(count: i32) -> i32 {
    let mut end_ptr: *mut Node = NODE_STORAGE.as_mut_ptr().offset(count as isize);
    let mut iter: *mut Node = end_ptr;
    if iter > NODE_STORAGE.as_mut_ptr() {
        iter = iter.offset(-1);
    }
    return (*iter).id;
}
        "#,
        &["let mut end_ptr: *mut crate::Node"],
        &[
            "let mut end_ptr: crate::slice_cursor::SliceCursor",
            "let mut end_ptr: &mut crate::Node",
        ],
    );
}

#[test]
fn test_rewriter_downgrades_foreign_mutable_local_struct_call_arg() {
    run_test(
        r#"
#[repr(C)]
pub struct Match {
    start: i32,
    end: i32,
}

extern "C" {
    fn fill_match(matches: *mut Match) -> i32;
}

pub unsafe fn wrapper(matches: *mut Match) -> i32 {
    return fill_match(matches);
}

pub unsafe fn caller(matches: *mut Match) -> i32 {
    return wrapper(matches);
}
        "#,
        &[
            "pub unsafe fn wrapper(mut matches: *mut crate::Match) -> i32",
            "fill_match(matches)",
        ],
        &["pub unsafe fn wrapper(matches: Option<&crate::Match>"],
    );
}

#[test]
fn test_rewriter_rewrites_add_on_slice_like_receivers() {
    run_test(
        r#"
extern "C" {
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut i32;
}

pub unsafe fn fill() -> *mut i32 {
    let mut p: *mut i32 = realloc(std::ptr::null_mut(), 4 * std::mem::size_of::<i32>());
    *p.add(1usize) = 5;
    p
}
"#,
        &[
            "pub unsafe fn fill() -> Option<Box<[i32]>>",
            "Option<Box<[i32]>>",
            ".as_mut_ptr().add(1usize)",
        ],
        &["Box::leak(", "Box::into_raw("],
    );
}

#[test]
fn test_rewriter_rewrites_realloc_null_char_ptr_to_boxed_slice() {
    run_test(
        r#"
extern "C" {
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_char;
}

pub unsafe fn dup_like(len: usize) -> *mut core::ffi::c_char {
    let p: *mut core::ffi::c_char = realloc(std::ptr::null_mut(), len);
    p
}
"#,
        &[
            "pub unsafe fn dup_like(len: usize) -> Option<Box<[i8]>>",
            "Option<Box<[i8]>>",
            "collect::<Vec<i8>>().into_boxed_slice()",
        ],
        &[
            "Box::leak(",
            "Box::into_raw(",
            "realloc(std::ptr::null_mut(), len)",
        ],
    );
}

#[test]
fn test_rewriter_keeps_foreign_strdup_tail_raw() {
    run_test(
        r#"
extern "C" {
    fn strdup(s: *const core::ffi::c_char) -> *mut core::ffi::c_char;
}

pub unsafe fn dup_tail(s: *const core::ffi::c_char) -> *mut core::ffi::c_char {
    return strdup(s);
}
"#,
        &["-> *mut i8", "return strdup((s).as_ptr());"],
        &["Option<Box", "Option<Box<["],
    );
}

#[test]
fn test_rewriter_promotes_struct_field_pointer_tail_param() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct Map {
    entries: *mut i32,
}

pub unsafe fn create_map() -> *mut Map {
    let map: *mut Map = malloc(std::mem::size_of::<Map>()) as *mut Map;
    (*map).entries = std::ptr::null_mut();
    return map;
}

pub unsafe fn get_entries(map: *mut Map) -> *mut i32 {
    return (*map).entries;
}
"#,
        &[
            "pub unsafe fn create_map<'a>() -> Box<crate::Map<'a>>",
            "Box::new(crate::Map { entries: None })",
            "pub unsafe fn get_entries<'a>(map: &crate::Map<'a>) -> *const i32",
        ],
        &[
            "Option<Box<i32>>",
            "Option<Box<[i32]>>",
            "Box<crate::Map>",
            "&crate::Map)",
            "entries: std::ptr::null_mut",
        ],
    );
}

#[test]
fn test_rewriter_promotes_struct_field_through_borrowed_struct_return() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *const i32,
}

pub unsafe fn id_holder(h: *mut Holder) -> *mut Holder {
    h
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let mut h = Holder { p: &raw const x };
    let r = id_holder(&raw mut h);
    *(*r).p
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a i32>",
            "pub unsafe fn id_holder<'a>(h: &'a mut crate::Holder<'a>)",
            "-> &'a mut crate::Holder<'a>",
            "Holder { p: Some(&x) }",
        ],
        &["pub p: *const i32", "*(*r).p"],
    );
}

#[test]
fn test_rewriter_promotes_generic_struct_field_synthetic_default_path() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct Holder<T> {
    pub p: *mut T,
}

pub unsafe fn create<T>() -> *mut Holder<T> {
    let holder: *mut Holder<T> = malloc(std::mem::size_of::<Holder<T>>()) as *mut Holder<T>;
    (*holder).p = std::ptr::null_mut();
    return holder;
}
"#,
        &[
            "pub struct Holder<'a, T>",
            "pub p: Option<&'a mut T>",
            "pub unsafe fn create<'a, T>() -> Box<crate::Holder<'a, T>>",
            "Box::new(crate::Holder { p: None })",
        ],
        &[
            "crate::Holder<T> {",
            "Box<crate::Holder<T>>",
            "p: std::ptr::null_mut",
        ],
    );
}

#[test]
fn test_rewriter_promotes_mutable_struct_field_to_option_ref() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let mut h = Holder { p: &raw mut x };
    *h.p = 7;
    h.p = core::ptr::null_mut();
    if h.p.is_null() {
        return x;
    }
    *h.p
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a mut i32>",
            "Holder { p: Some(&mut x) }",
            "h.p = None;",
            "h.p.is_none()",
        ],
        &["pub p: *mut i32", "*h.p"],
    );
}

#[test]
fn test_rewriter_promotes_mutable_struct_field_assigned_from_raw_pointer() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut x: i32, mut buf: [i32; 1]) -> i32 {
    let mut h = Holder { p: &raw mut x };
    *h.p = 7;
    h.p = buf.as_mut_ptr();
    if !h.p.is_null() {
        *h.p = 9;
    }
    x
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a mut i32>",
            "Holder { p: Some(&mut x) }",
            "h.p = (buf.as_mut_ptr()).as_mut();",
        ],
        &[
            "pub p: *mut i32",
            "h.p = buf.as_mut_ptr();",
            "unsafe { (buf.as_mut_ptr()).as_mut()",
        ],
    );
}

#[test]
fn test_rewriter_promotes_mutable_struct_field_zero_initializer_to_none() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut buf: [i32; 1]) -> i32 {
    let mut h = Holder { p: 0 as *mut i32 };
    h.p = buf.as_mut_ptr();
    if !h.p.is_null() {
        *h.p = 9;
    }
    buf[0]
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a mut i32>",
            "Holder { p: None }",
            "h.p = (buf.as_mut_ptr()).as_mut();",
        ],
        &["(0).as_mut()", "0 as *mut i32"],
    );
}

#[test]
fn test_rewriter_casts_raw_rhs_assigned_to_promoted_field() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i8,
}

pub unsafe fn touch(out: *mut core::ffi::c_void) -> i8 {
    let mut h = Holder { p: std::ptr::null_mut() };
    let _addr = out as usize;
    h.p = out as *mut i8;
    if !h.p.is_null() {
        *h.p = 9;
    }
    0
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a mut i8>",
            "h.p = (out as *mut i8).as_mut();",
        ],
        &[
            "h.p = out as *mut i8;",
            "unsafe { (out as *mut i8).as_mut()",
        ],
    );
}

#[test]
fn test_rewriter_promotes_field_with_offset_deref_receiver() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut buf: [i32; 2]) -> i32 {
    let mut h = Holder { p: buf.as_mut_ptr() };
    *h.p.offset(1) = 9;
    buf[1]
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: &'a mut [i32]",
            "as usize..",
        ],
        &[
            "pub p: Option<&'a mut i32>",
            "pub p: *mut i32",
            "*h.p.offset(1) = 9;",
        ],
    );
}

#[test]
fn test_rewriter_field_base_match_is_paren_insensitive() {
    // the field-base access is written with a redundant paren (`(h).p`), which a
    // pretty-printed string match rejects (`(h).p` != `h.p`); structural matching
    // resolves it and still promotes the field.
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut buf: [i32; 2]) -> i32 {
    let mut h = Holder { p: buf.as_mut_ptr() };
    *(h).p.offset(1) = 9;
    buf[1]
}
"#,
        &["pub p: &'a mut [i32]", "as usize.."],
        &[
            "pub p: Option<&'a mut i32>",
            "pub p: *mut i32",
            ".offset(1)",
        ],
    );
}

#[test]
fn test_rewriter_field_base_distinct_fields_do_not_cross_match() {
    // two pointer fields each form their own base; matching one must never match
    // the other (the `Field` step name differs), so both promote to their own
    // slice independently with no cross-contamination.
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
    pub q: *mut i32,
}

pub unsafe fn touch(mut a: [i32; 2], mut b: [i32; 2]) -> i32 {
    let mut h = Holder { p: a.as_mut_ptr(), q: b.as_mut_ptr() };
    *h.p.offset(1) = 9;
    *h.q.offset(1) = 7;
    a[1] + b[1]
}
"#,
        &["pub p: &'a mut [i32]", "pub q: &'b mut [i32]"],
        &["pub p: *mut i32", "pub q: *mut i32", ".offset(1)"],
    );
}

#[test]
fn test_rewriter_promotes_array_like_struct_field_to_slice() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut buf: [i32; 2]) -> i32 {
    let h = Holder { p: buf.as_mut_ptr() };
    *h.p.offset(1) = 9;
    buf[1]
}
"#,
        &["pub p: &'a mut [i32]", "as usize.."],
        &[
            "pub p: Option<&'a mut i32>",
            "pub p: *mut i32",
            "*h.p.offset",
        ],
    );
}

#[test]
fn test_rewriter_promotes_negative_offset_struct_field_to_slice_cursor() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *const i32,
}

pub unsafe fn touch(buf: [i32; 4]) -> i32 {
    let h = Holder { p: buf.as_ptr().offset(3) };
    *h.p.offset(-1)
}
"#,
        &[
            "pub p: crate::slice_cursor::SliceCursor<'a, i32>",
            "crate::slice_cursor::SliceCursor::",
            "(h.p)[",
            "-1",
        ],
        &[
            "pub p: Option<&'a i32>",
            "pub p: *const i32",
            "*h.p.offset",
            ".offset_by((-1) as isize)",
        ],
    );
}

#[test]
fn test_rewriter_reads_mutable_cursor_field_through_shared_struct_ref() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    pub words: *mut u32,
    pub word_index: i32,
}

pub unsafe fn load_word(s: *const State) -> u32 {
    *(*s).words.offset((*s).word_index as isize)
}
"#,
        &[
            "pub words: crate::slice_cursor::SliceCursorMut<'a, u32>",
            "(s.words)[",
            "s.word_index",
        ],
        &[
            "SliceCursor::new((s.words).as_slice())",
            "(s.words).as_slice()",
            "let mut _c = ((*s).words);",
            "*(*s).words.offset",
        ],
    );
}

#[test]
fn test_rewriter_promotes_borrowed_struct_field_offset_deref_to_slice_index() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    pub words: *const u32,
    pub word_index: i32,
}

pub unsafe fn load_word(s: *const State) -> u32 {
    return *(*s).words.offset((*s).word_index as isize);
}
"#,
        &[
            "pub struct State<'a>",
            "pub words: crate::slice_cursor::SliceCursor<'a, u32>",
            "(s.words)[",
            "s.word_index",
        ],
        &[
            "pub words: Option<&'a u32>",
            "*(*s).words.offset",
            ".offset_by((s.word_index",
        ],
    );
}

#[test]
fn test_rewriter_promotes_field_copied_to_safe_local_alias() {
    run_test(
        r#"
use ::libc;

#[repr(C)]
pub struct Buffer {
    pub content: *const libc::c_uchar,
    pub offset: usize,
}

pub unsafe extern "C" fn first(buffer: *const Buffer) -> libc::c_int {
    let input = (*buffer).content.offset((*buffer).offset as isize);
    *input as libc::c_int
}
"#,
        &[
            "pub struct Buffer<'a>",
            "pub content: &'a [libc::c_uchar]",
            "[(buffer.offset as isize) as usize..]).first()",
        ],
        &[
            "pub content: *const u8",
            "let input = (*buffer).content.offset",
            "*input as",
        ],
    );
}

#[test]
fn test_rewriter_promotes_cursor_field_copied_to_local_offset_alias_with_disjoint_root_update() {
    run_test(
        r#"
#[repr(C)]
pub struct Bs {
    pub buf: *const u8,
    pub pos: i32,
    pub limit: i32,
}

pub unsafe fn get_bits(bs: *mut Bs, n: i32) -> u32 {
    let mut p: *const u8 = ((*bs).buf).offset(((*bs).pos >> 3) as isize);
    (*bs).pos += n;
    if (*bs).pos > (*bs).limit {
        return 0;
    }
    let fresh = *p;
    p = p.offset(1);
    fresh as u32
}
"#,
        &[
            "pub struct Bs<'a>",
            "pub buf: crate::slice_cursor::SliceCursor<'a, u8>",
            "let mut p: crate::slice_cursor::SliceCursor<'_, u8>",
            "p.seek((1) as isize)",
        ],
        &[
            "pub buf: *const u8",
            "std::slice::from_raw_parts(((bs.buf).offset",
            "*p.offset",
        ],
    );
}

#[test]
fn test_rewriter_promotes_cursor_field_copied_to_local_offset_alias_without_root_mutation() {
    run_test(
        r#"
#[repr(C)]
pub struct Bs {
    pub buf: *const u8,
    pub pos: i32,
    pub limit: i32,
}

pub unsafe fn read_two(bs: *const Bs) -> u32 {
    let mut p: *const u8 = ((*bs).buf).offset(((*bs).pos >> 3) as isize);
    if (*bs).pos > (*bs).limit {
        return 0;
    }
    let first = *p as u32;
    p = p.offset(1);
    first + (*p as u32)
}
"#,
        &[
            "pub struct Bs<'a>",
            "pub buf: crate::slice_cursor::SliceCursor<'a, u8>",
            "let mut p: crate::slice_cursor::SliceCursor<'_, u8>",
            "p.seek((1) as isize)",
        ],
        &[
            "pub buf: *const u8",
            "std::slice::from_raw_parts(((bs.buf).offset",
            "*p as u32",
        ],
    );
}

#[test]
fn test_rewriter_rewrites_casted_promoted_field_offset_return() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    pub words: *const u32,
    pub word_index: i32,
    pub count: i32,
}

pub unsafe fn cp_ptr(s: *const State) -> *const i8 {
    return (((*s).words.offset((*s).word_index as isize)) as *const i8)
        .offset(-(((*s).count / 8) as isize));
}
"#,
        &[
            "pub struct State<'a>",
            "pub words: crate::slice_cursor::SliceCursor<'a, u32>",
            "crate::slice_cursor::SliceCursor::from_raw_parts",
            ".offset_by((-((s.count / 8) as isize))",
        ],
        &[
            "pub words: Option<&'a u32>",
            "std::ptr::null::<i8>(), |_x| _x",
        ],
    );
}

#[test]
fn test_rewriter_rewrites_casted_mutable_cursor_field_from_shared_struct_ref() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    pub words: *mut u32,
    pub word_index: i32,
    pub count: i32,
}

pub unsafe fn cp_ptr(s: *const State) -> *const i8 {
    return (((*s).words.offset((*s).word_index as isize)) as *mut i8)
        .offset(-(((*s).count / 8) as isize)) as *const i8;
}
"#,
        &[
            "pub words: crate::slice_cursor::SliceCursorMut<'a, u32>",
            ".as_slice()",
            ".offset_by((-((s.count / 8) as isize))",
        ],
        &["}).as_mut_ptr()", "*(*s).words.offset"],
    );
}

#[test]
fn test_rewriter_cursor_numeric_cast_uses_bytemuck_not_raw_parts() {
    run_test(
        r#"
#[repr(C)]
pub struct Pair {
    pub a: i32,
    pub b: i32,
}

pub unsafe fn container_from_b(i: *const i32) -> *const Pair {
    ((i as *const i8).offset(-(4 as isize))) as *const Pair
}
"#,
        &[
            "pub unsafe fn container_from_b(i: crate::slice_cursor::SliceCursor<'_, i32>)",
            "bytemuck::cast_slice::<_,",
            "i8>((i).as_slice())",
            ".offset_by((-(4 as isize))",
        ],
        &["crate::slice_cursor::SliceCursor::from_raw_parts((i).as_ptr()"],
    );
}

#[test]
fn test_rewriter_promotes_field_passed_to_unknown_raw_call() {
    run_test(
        r#"
extern "C" {
    fn foreign(p: *mut i32);
}

#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch() -> i32 {
    let mut x = 0;
    let mut h = Holder { p: &raw mut x };
    foreign(h.p);
    *h.p = 7;
    x
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a mut i32>",
            "foreign((h.p).as_deref_mut().map_or",
        ],
        &["pub p: *mut i32"],
    );
}

#[test]
fn test_rewriter_promotes_field_passed_to_local_raw_call() {
    run_test(
        r#"
pub unsafe fn local_raw(p: *mut i32) {
    extern "C" {
        fn foreign(p: *mut i32);
    }
    foreign(p);
}

#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch() -> i32 {
    let mut x = 0;
    let mut h = Holder { p: &raw mut x };
    local_raw(h.p);
    *h.p = 7;
    x
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a mut i32>",
            "local_raw((h.p).as_deref_mut())",
        ],
        &["pub p: *mut i32"],
    );
}

#[test]
fn test_rewriter_promotes_field_passed_to_local_slice_call() {
    run_test(
        r#"
pub unsafe fn read_second(p: *const i8) -> i32 {
    *p.offset(1) as i32
}

#[repr(C)]
pub struct Holder {
    pub p: *const i8,
}

pub unsafe fn touch(buf: [i8; 2]) -> i32 {
    let h = Holder { p: buf.as_ptr() };
    read_second(h.p)
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub unsafe fn read_second(p: &[i8])",
            "pub p: &'a [i8]",
            "read_second(h.p)",
        ],
        &["pub p: Option<&'a i8>", "pub p: *const i8"],
    );
}

#[test]
fn test_rewriter_stores_slice_param_into_promoted_field_via_raw_bridge() {
    run_test(
        r#"
#[repr(C)]
pub struct Program {
    pub code: *const i32,
    pub n: usize,
}

pub unsafe fn prog_init(p: *mut Program, code: *const i32, n: usize, out: *mut i32) {
    (*p).code = code;
    *out = *code.offset(0);
    (*p).n = n;
}

pub unsafe fn prog_fetch(p: *mut Program, out: *mut i32) {
    *out = *(*p).code.offset(0);
}
"#,
        &[
            "pub struct Program<'a>",
            "pub code: &'a [i32]",
            "code: &'a [i32]",
            "p.code = (code);",
        ],
        &[
            "pub code: Option<&'a i32>",
            "(*p).code = (code).as_ptr().as_ref();",
        ],
    );
}

#[test]
fn test_rewriter_removes_unneeded_generated_copy_for_mutable_struct_field() {
    run_test(
        r#"
#![feature(derive_clone_copy)]

#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
    pub tag: i32,
}

#[automatically_derived]
impl ::core::marker::Copy for Holder {}

#[automatically_derived]
impl ::core::clone::Clone for Holder {
    #[inline]
    fn clone(&self) -> Holder {
        let _: ::core::clone::AssertParamIsClone<*mut i32>;
        let _: ::core::clone::AssertParamIsClone<i32>;
        *self
    }
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let mut h = Holder { p: &raw mut x, tag: 3 };
    *h.p = 7;
    h.p = core::ptr::null_mut();
    h.tag
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a mut i32>",
            "Holder { p: Some(&mut x), tag: 3 }",
            "h.p = None;",
        ],
        &[
            "pub p: *mut i32",
            "impl ::core::marker::Copy for Holder",
            "impl ::core::clone::Clone for Holder",
            "*h.p = 7",
        ],
    );
}

#[test]
fn test_rewriter_reborrows_mutable_promoted_field_for_shared_pointer_assignment() {
    run_test(
        r#"
#![feature(derive_clone_copy)]

#[repr(C)]
pub struct Node {
    pub value: i32,
    pub next: *mut Node,
}

#[automatically_derived]
impl ::core::marker::Copy for Node {}

#[automatically_derived]
impl ::core::clone::Clone for Node {
    #[inline]
    fn clone(&self) -> Node {
        let _: ::core::clone::AssertParamIsClone<i32>;
        let _: ::core::clone::AssertParamIsClone<*mut Node>;
        *self
    }
}

pub unsafe fn last_value(mut head: *mut Node) -> i32 {
    if head.is_null() {
        return 0;
    }
    while !(*head).next.is_null() {
        head = (*head).next;
    }
    (*head).value
}
"#,
        &[
            "pub struct Node<'a>",
            "pub next: Option<&'a mut Node<'a>>",
            "head = ((*head.unwrap()).next).as_deref();",
        ],
        &[
            "impl ::core::marker::Copy for Node",
            "impl ::core::clone::Clone for Node",
            "head = unsafe { ((*(head).as_deref().unwrap()).next).as_ref() };",
        ],
    );
}

#[test]
fn test_rewriter_promotes_noop_cast_of_recursive_field_alias() {
    run_test(
        r#"
#[repr(C)]
pub struct Node {
    pub value: i32,
    pub next: *mut Node,
}


pub unsafe fn second_value(current: *const Node) -> i32 {
    if current.is_null() {
        return 0;
    }
    let next: *const Node = (*current).next as *const Node;
    if next.is_null() {
        return (*current).value;
    }
    (*next).value
}
"#,
        &[
            "pub struct Node<'a>",
            "pub next: Option<&'a mut Node<'a>>",
            "((*current.unwrap()).next).as_deref()",
        ],
        &["pub next: *mut Node", "as_ref()"],
    );
}

#[test]
fn test_rewriter_preserves_generated_copy_when_struct_is_reused_after_raw_storage_move() {
    run_test(
        r#"
#![feature(derive_clone_copy)]

#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
    pub tag: i32,
}

#[automatically_derived]
impl ::core::marker::Copy for Holder {}

#[automatically_derived]
impl ::core::clone::Clone for Holder {
    #[inline]
    fn clone(&self) -> Holder {
        let _: ::core::clone::AssertParamIsClone<*mut i32>;
        let _: ::core::clone::AssertParamIsClone<i32>;
        *self
    }
}

pub unsafe fn touch(mut x: i32, slot: *mut Holder) -> i32 {
    let h = Holder { p: &raw mut x, tag: 3 };
    *slot = h;
    *h.p = 7;
    h.tag
}
"#,
        &[
            "pub struct Holder {",
            "pub p: *mut i32",
            "impl ::core::marker::Copy for Holder",
            "impl ::core::clone::Clone for Holder",
            "*slot = h;",
            "*h.p = 7",
        ],
        &["pub p: Option<&'a mut i32>", "Holder<'a>"],
    );
}

#[test]
fn test_rewriter_preserves_generated_copy_when_copy_container_depends_on_struct() {
    run_test(
        r#"
#![feature(derive_clone_copy)]

#[repr(C)]
pub struct Inner {
    pub p: *mut i32,
}

#[automatically_derived]
impl ::core::marker::Copy for Inner {}

#[automatically_derived]
impl ::core::clone::Clone for Inner {
    #[inline]
    fn clone(&self) -> Inner {
        let _: ::core::clone::AssertParamIsClone<*mut i32>;
        *self
    }
}

#[repr(C)]
pub struct Outer {
    pub inner: Inner,
}

#[automatically_derived]
impl ::core::marker::Copy for Outer {}

#[automatically_derived]
impl ::core::clone::Clone for Outer {
    #[inline]
    fn clone(&self) -> Outer {
        let _: ::core::clone::AssertParamIsClone<Inner>;
        *self
    }
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let inner = Inner { p: &raw mut x };
    *inner.p = 7;
    0
}
"#,
        &[
            "pub struct Inner {",
            "pub p: *mut i32",
            "impl ::core::marker::Copy for Inner",
            "impl ::core::marker::Copy for Outer",
        ],
        &["pub p: Option<&'a mut i32>", "Inner<'a>"],
    );
}

#[test]
fn test_rewriter_demotes_promoted_field_struct_return_type() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *const i32,
}

pub unsafe fn make(x: *const i32) -> Holder {
    Holder { p: x }
}
"#,
        &["pub struct Holder {", "pub p: *const i32", "-> Holder"],
        &["Holder<'_", "Option<&'a i32>"],
    );
}

#[test]
fn test_rewriter_keeps_tuple_struct_field_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder(pub *mut i32);

pub unsafe fn touch(mut x: i32) -> i32 {
    let h = Holder(&raw mut x);
    *h.0 = 7;
    x
}
"#,
        &[
            "pub struct Holder(pub *mut i32)",
            "Holder(&raw mut (x))",
            "*h.0 = 7",
        ],
        &["Holder<'_", "Option<&'a mut i32>"],
    );
}

#[test]
fn test_rewriter_keeps_direct_freed_returned_pointer_raw() {
    run_test(
        r#"
extern "C" {
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn id(p: *mut i32) -> *mut i32 {
    p
}

pub unsafe fn caller(mut x: i32) {
    free(id(&raw mut x) as *mut core::ffi::c_void);
}
"#,
        &[
            "pub unsafe fn id(mut p: *mut i32) -> *mut i32",
            "free(id(&raw mut (x)) as *mut core::ffi::c_void)",
        ],
        &["pub unsafe fn id<'a>", "-> &'a mut i32"],
    );
}

#[test]
fn test_rewriter_updates_impl_headers_for_promoted_struct_lifetimes() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *const i32,
}

impl Copy for Holder {}

impl Clone for Holder {
    fn clone(&self) -> Self {
        *self
    }
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let h = Holder { p: &raw const x };
    let _ = *h.p;
    x
}
"#,
        &[
            "pub struct Holder<'a>",
            "impl<'a> Copy for Holder<'a>",
            "impl<'a> Clone for Holder<'a>",
            "pub p: Option<&'a i32>",
        ],
        &["impl Copy for Holder {", "impl Clone for Holder {"],
    );
}

#[test]
fn test_rewriter_rewrites_promoted_field_access_inside_impl_methods() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *const i32,
}

impl Holder {
    pub unsafe fn read(&self) -> i32 {
        if self.p.is_null() {
            return 0;
        }
        *self.p
    }
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let h = Holder { p: &raw const x };
    let _ = *h.p;
    h.read()
}
"#,
        &[
            "pub struct Holder<'a>",
            "impl<'a> Holder<'a>",
            "self.p.is_none()",
            "*(self.p.unwrap())",
        ],
        &["impl Holder {", "self.p.is_null()", "*self.p"],
    );
}

#[test]
fn test_rewriter_demotes_promoted_field_nested_in_generic_return_type() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let mut h = Holder { p: &raw mut x };
    *h.p = 7;
    x
}

pub unsafe fn maybe_holder() -> Option<Holder> {
    None
}
"#,
        &[
            "pub struct Holder {",
            "pub p: *mut i32",
            "pub unsafe fn maybe_holder() -> Option<Holder>",
        ],
        &["Holder<'_", "Option<&'a mut i32>"],
    );
}

#[test]
fn test_rewriter_demotes_promoted_field_raw_pointer_return_type() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

extern "C" {
    fn make_holder() -> *mut Holder;
}

pub unsafe fn touch() {
    let h = make_holder();
    if !(*h).p.is_null() {
        *(*h).p = 7;
    }
}
"#,
        &["pub struct Holder {", "pub p: *mut i32", "-> *mut Holder"],
        &["Holder<'_", "Option<&'a mut i32>"],
    );
}

#[test]
fn test_rewriter_promotes_c_string_field_from_offset_struct_array_call() {
    run_test(
        r#"
#![feature(derive_clone_copy)]

#[derive(Copy, Clone)]
#[repr(C)]
pub struct Record {
    pub name: *const i8,
}

pub unsafe fn consume_c_string(s: *const i8) -> i32 {
    if s.is_null() {
        return 0;
    }
    *s.offset(1) as i32
}

pub unsafe fn force_field_promotion(mut x: i8) -> i32 {
    let r = Record { name: &raw const x };
    *r.name as i32
}

pub unsafe fn show(fields: *mut Record, i: isize) -> i32 {
    consume_c_string((*fields.offset(i)).name)
}
"#,
        &[
            "pub struct Record<'a>",
            "pub name: &'a [i8]",
            "pub unsafe fn consume_c_string(s: &[i8])",
            "consume_c_string(((fields)[(i) as isize]).name)",
        ],
        &["pub name: Option<&'a i8>", "pub name: *const i8"],
    );
}

#[test]
fn test_rewriter_promotes_c_string_field_from_impl_method_call() {
    run_test(
        r#"
#![feature(derive_clone_copy)]

#[derive(Copy, Clone)]
#[repr(C)]
pub struct Record {
    pub name: *const i8,
}

pub unsafe fn consume_c_string(s: *const i8) -> i32 {
    if s.is_null() {
        return 0;
    }
    *s.offset(1) as i32
}

impl Record {
    pub unsafe fn show(fields: *mut Record, i: isize) -> i32 {
        consume_c_string((*fields.offset(i)).name)
    }
}

pub unsafe fn force_field_promotion(mut x: i8) -> i32 {
    let r = Record { name: &raw const x };
    *r.name as i32
}
"#,
        &[
            "pub struct Record<'a>",
            "impl<'a> Record<'a>",
            "pub name: Option<&'a i8>",
            "consume_c_string(&(std::slice::from_raw_parts",
        ],
        &["pub name: *const i8"],
    );
}

#[test]
fn test_rewriter_keeps_direct_raw_field_call_result_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn id(p: *mut i32) -> *mut i32 {
    p
}

pub unsafe fn make(mut x: i32) -> Holder {
    Holder { p: id(&raw mut x) }
}
"#,
        &[
            "pub struct Holder {",
            "pub p: *mut i32",
            "pub unsafe fn id<'a>(p: &'a mut i32) -> *mut i32",
            "Holder { p: id((Some(&mut x)).unwrap()) }",
        ],
        &["Holder<'_", "-> &'a mut i32", "Option<&'a mut i32>"],
    );
}

#[test]
fn test_rewriter_borrows_repeated_optional_mut_arg_without_move() {
    run_test(
        r#"
pub unsafe fn write(p: *mut i32) {
    *p = 1;
}

pub unsafe fn caller(p: *mut i32) {
    if !p.is_null() {
        write(p);
        write(p);
    }
}
"#,
        &[
            "pub unsafe fn caller(mut p: Option<&mut i32>)",
            "let p_borrowed = p.as_deref_mut().unwrap();",
            "write(p_borrowed)",
        ],
        &["write((p).unwrap())"],
    );
}

#[test]
fn test_rewriter_reborrows_repeated_optional_mut_arg_for_optional_callee() {
    run_test(
        r#"
pub unsafe fn maybe_write(p: *mut i32) {
    if !p.is_null() {
        *p = 1;
    }
}

pub unsafe fn caller(p: *mut i32) {
    if !p.is_null() {
        maybe_write(p);
        maybe_write(p);
    }
}
"#,
        &[
            "pub unsafe fn maybe_write(mut p: Option<&mut i32>)",
            "pub unsafe fn caller(mut p: Option<&mut i32>)",
            "maybe_write((p).as_deref_mut())",
        ],
        &["maybe_write(p);"],
    );
}

#[test]
fn test_rewriter_rewrites_noop_cast_local_binding_to_ref() {
    run_test(
        r#"
#[repr(C)]
pub struct Info {
    pub x: i32,
}

pub unsafe fn touch(info: *mut Info) {
    let q: *mut Info = info as *mut Info;
    (*q).x = 1;
}
"#,
        &[
            "pub unsafe fn touch(mut info: &mut crate::Info)",
            "let mut q: &mut crate::Info = (Some(&mut *(info))).unwrap();",
        ],
        &["let mut q: *mut crate::Info"],
    );
}

#[test]
fn test_rewriter_rewrites_noop_cast_local_call_arg_to_ref() {
    run_test(
        r#"
#[repr(C)]
pub struct Info {
    pub x: i32,
}

pub unsafe fn init(info: *mut Info) {
    (*info).x = 1;
}

pub unsafe fn touch(info: *mut Info) {
    init(info as *mut Info);
}
"#,
        &[
            "pub unsafe fn init(mut info: &mut crate::Info)",
            "init((Some(&mut *(info))).unwrap());",
        ],
        &["pub unsafe fn init(mut info: *mut crate::Info)"],
    );
}

#[test]
fn test_rewriter_does_not_demote_ref_callee_for_noop_cast_call() {
    run_test(
        r#"
#[repr(C)]
pub struct State {
    pub h: [u32; 8],
    pub flag: i32,
}

pub unsafe fn init(state: *mut State) {
    (*state).h[0] = 1;
    (*state).flag = 0;
}

pub unsafe fn caller(ctx: *mut State) {
    init(ctx as *mut State);
}
"#,
        &[
            "pub unsafe fn init(mut state: &mut crate::State)",
            "init((Some(&mut *(ctx))).unwrap());",
        ],
        &["pub unsafe fn init(mut state: *mut crate::State)"],
    );
}

#[test]
fn test_rewriter_keeps_raw_casted_foreign_call_input_raw() {
    run_test(
        r#"
extern "C" {
    fn strtol(s: *const core::ffi::c_char, endp: *mut *mut core::ffi::c_char, base: core::ffi::c_int) -> core::ffi::c_long;
}

pub unsafe fn parse(str: *const core::ffi::c_char) -> core::ffi::c_long {
    let mut endp: *mut i8 = str as *mut core::ffi::c_char as *mut i8;
    strtol(str, &raw mut endp, 10)
}
"#,
        &[
            "pub unsafe fn parse(str: *const i8)",
            "let mut endp: *mut i8",
            "str as *mut core::ffi::c_char as *mut i8",
            "strtol(str, &raw mut (endp), 10)",
        ],
        &["str: Option<&i8>", "strtol((str)"],
    );
}

#[test]
fn test_rewriter_rewrites_casted_optional_ref_local_binding() {
    run_test(
        r#"
pub unsafe fn read(bytes: *mut u8) -> i32 {
    let int_ptr: *mut core::ffi::c_int = bytes as *mut core::ffi::c_int;
    if int_ptr.is_null() {
        return 0;
    }
    *int_ptr
}
"#,
        &[
            "let int_ptr: Option<&i32>",
            "as *const i32",
            "int_ptr.is_none()",
        ],
        &["bytes as *mut core::ffi::c_int"],
    );
}

#[test]
fn test_rewriter_promotes_generic_struct_field_preserves_type_args() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder<T> {
    pub p: *mut T,
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let mut h: Holder<i32> = Holder { p: &raw mut x };
    *h.p = 7;
    x
}
"#,
        &[
            "pub struct Holder<'a, T>",
            "pub p: Option<&'a mut T>",
            "let mut h: Holder<'_, i32> = Holder { p: Some(&mut x) };",
        ],
        &["Holder<i32>", "pub p: *mut T", "*h.p"],
    );
}

#[test]
fn test_rewriter_promotes_struct_field_after_existing_lifetime_args() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder<'ctx, T> {
    pub ctx: &'ctx T,
    pub p: *mut T,
}

pub unsafe fn touch<'ctx>(ctx: &'ctx i32, mut x: i32) -> i32 {
    let mut h: Holder<'ctx, i32> = Holder { ctx, p: &raw mut x };
    *h.p = 7;
    *h.ctx
}
"#,
        &[
            "pub struct Holder<'ctx, 'a, T>",
            "pub p: Option<&'a mut T>",
            "let mut h: Holder<'ctx, '_, i32> = Holder { ctx, p: Some(&mut x) };",
        ],
        &[
            "Holder<'a, 'ctx",
            "Holder<'_, 'ctx",
            "Holder<'ctx, i32>",
            "*h.p",
        ],
    );
}

#[test]
fn test_rewriter_promotes_self_referential_struct_field_pointee_lifetime() {
    run_test(
        r#"
#[repr(C)]
pub struct Node {
    pub next: *mut Node,
    pub value: i32,
}

pub unsafe fn touch() -> i32 {
    let mut other = Node { next: std::ptr::null_mut(), value: 1 };
    let mut node = Node { next: &raw mut other, value: 0 };
    (*node.next).value = 2;
    node.value
}
"#,
        &[
            "pub struct Node<'a>",
            "pub next: Option<&'a mut Node<'a>>",
            "Node { next: None, value: 1 }",
            "Node { next: Some(&mut other), value: 0 }",
        ],
        &["Option<&'a mut Node>", "*node.next"],
    );
}

#[test]
fn test_rewriter_promotes_mutable_field_write_from_immutable_holder() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let h = Holder { p: &raw mut x };
    *h.p = 7;
    x
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a mut i32>",
            "let mut h = Holder { p: Some(&mut x) };",
        ],
        &["let h = Holder", "pub p: *mut i32", "*h.p"],
    );
}

#[test]
fn test_rewriter_promotes_mutable_field_write_from_by_value_param() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn write(h: Holder) {
    *h.p = 7;
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let h = Holder { p: &raw mut x };
    write(h);
    x
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a mut i32>",
            "pub unsafe fn write(mut h: Holder<'_>)",
        ],
        &["pub unsafe fn write(h: Holder<'_>)", "*h.p"],
    );
}

#[test]
fn test_rewriter_demotes_struct_field_on_active_raw_mut_reborrow() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let h = Holder { p: &raw mut x };
    let q = &raw mut x;
    *q = 1;
    *h.p = 7;
    x
}
"#,
        &["pub p: *mut i32", "Holder { p: &raw mut x }", "*h.p = 7"],
        &["Option<&'a mut i32>", "h.p.as_deref_mut"],
    );
}

#[test]
fn test_rewriter_demotes_mutable_struct_field_to_field_assignment_with_rhs_reuse() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut x: i32, mut y: i32) -> i32 {
    let mut h1 = Holder { p: &raw mut x };
    let h2 = Holder { p: &raw mut y };
    h1.p = h2.p;
    *h1.p = 7;
    *h2.p = 9;
    x
}
"#,
        &["pub p: *mut i32", "h1.p = h2.p;", "*h2.p = 9"],
        &[
            "Option<&'a mut i32>",
            "h1.p.as_deref_mut",
            "h2.p.as_deref_mut",
        ],
    );
}

#[test]
fn test_rewriter_demotes_mutable_struct_field_literal_copy_with_rhs_reuse() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn touch(mut y: i32) -> i32 {
    let h2 = Holder { p: &raw mut y };
    let h1 = Holder { p: h2.p };
    *h1.p = 7;
    *h2.p = 9;
    y
}
"#,
        &["pub p: *mut i32", "Holder { p: h2.p }", "*h2.p = 9"],
        &[
            "Option<&'a mut i32>",
            "h1.p.as_deref_mut",
            "h2.p.as_deref_mut",
        ],
    );
}

#[test]
fn test_rewriter_demotes_mutable_rhs_field_copied_to_shared_field() {
    run_test(
        r#"
#[repr(C)]
pub struct Source {
    pub p: *mut i32,
}

#[repr(C)]
pub struct View {
    pub q: *const i32,
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let src = Source { p: &raw mut x };
    let view = View { q: src.p };
    *src.p = 7;
    *view.q
}
"#,
        &["pub p: *mut i32", "View { q: src.p }", "*src.p = 7"],
        &["pub p: Option<&'a mut i32>", "src.p.as_deref_mut"],
    );
}

#[test]
fn test_rewriter_promotes_nested_struct_path_in_field_pointee_type() {
    run_test(
        r#"
#[repr(C)]
pub struct Node {
    pub value: *mut i32,
}

#[repr(C)]
pub struct Holder {
    pub nodes: *const Vec<Node>,
}

pub unsafe fn set_node(mut x: i32) -> i32 {
    let mut node = Node { value: &raw mut x };
    *node.value = 7;
    x
}

pub unsafe fn hold(nodes: &Vec<Node>) -> usize {
    let holder = Holder { nodes: std::ptr::null() };
    if holder.nodes.is_null() {
        return nodes.len();
    }
    (*holder.nodes).len()
}
"#,
        &[
            "pub struct Node<'a>",
            "pub value: Option<&'a mut i32>",
            "pub struct Holder<'a>",
            "pub nodes: Option<&'a Vec<Node<'a>>>",
        ],
        &["Vec<Node>>", "Vec<Node>"],
    );
}

#[test]
fn test_rewriter_demotes_multiple_mutable_struct_fields_from_same_local() {
    run_test(
        r#"
#[repr(C)]
pub struct Pair {
    pub a: *mut i32,
    pub b: *mut i32,
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let pair = Pair { a: &raw mut x, b: &raw mut x };
    *pair.a = 3;
    *pair.b = 4;
    x
}
"#,
        &[
            "pub a: *mut i32",
            "pub b: *mut i32",
            "Pair { a: &raw mut x, b: &raw mut x }",
        ],
        &["Option<&'a mut i32>", "Some(&mut x)", "as_deref_mut"],
    );
}

#[test]
fn test_rewriter_demotes_mixed_mutable_shared_struct_fields_from_same_local() {
    run_test(
        r#"
#[repr(C)]
pub struct Pair {
    pub a: *mut i32,
    pub b: *const i32,
}

pub unsafe fn touch(mut x: i32) -> i32 {
    let pair = Pair { a: &raw mut x, b: &raw const x };
    *pair.a = 3;
    *pair.b
}
"#,
        &[
            "pub a: *mut i32",
            "pub b: *const i32",
            "Pair { a: &raw mut x, b: &raw const x }",
        ],
        &[
            "Option<&'a mut i32>",
            "Option<&'b i32>",
            "Some(&mut x)",
            "Some(&x)",
        ],
    );
}

#[test]
fn test_rewriter_promotes_shared_struct_field_to_option_ref() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *const i32,
}

pub unsafe fn read(x: i32) -> i32 {
    let h = Holder { p: &raw const x };
    *h.p
}
"#,
        &[
            "pub struct Holder<'a>",
            "pub p: Option<&'a i32>",
            "Holder { p: Some(&x) }",
            "h.p.unwrap()",
        ],
        &["pub p: *const i32", "*h.p"],
    );
}

#[test]
fn test_rewriter_promotes_raw_struct_param_for_direct_pointer_field_access() {
    run_test(
        r#"
#[repr(C)]
pub struct Node {
    pub next: *mut Node,
    pub value: i32,
}

pub unsafe fn mark_if_linked(node: *mut Node) -> i32 {
    if ((*node).next).is_null() {
        (*node).value = 0;
    } else {
        (*node).value = 1;
    }
    (*node).value
}
"#,
        &[
            "pub struct Node<'a>",
            "pub next: Option<&'a mut Node<'a>>",
            "pub unsafe fn mark_if_linked<'a>(mut node: &mut crate::Node<'a>)",
            "(node.next).is_none()",
        ],
        &["pub next: *mut Node", "(*node).next", "(*&*(node)).next"],
    );
}

#[test]
fn test_rewriter_preserves_address_taken_field_base_for_promoted_struct_param() {
    run_test(
        r#"
#[repr(C)]
pub struct IntVec {
    pub data: *mut i32,
    pub len: usize,
    pub cap: usize,
}

#[repr(C)]
pub struct VM {
    pub stack: IntVec,
    pub steps: i32,
}

unsafe extern "C" {
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn init_vec(v: *mut IntVec) {
    free((*v).data as *mut core::ffi::c_void);
    (*v).data = std::ptr::null_mut();
    (*v).len = 0;
    (*v).cap = 0;
}

pub unsafe fn vm_init(vm: *mut VM) {
    init_vec(&mut (*vm).stack);
    (*vm).steps = 0;
}
"#,
        &[
            "pub unsafe fn vm_init(mut vm: &mut crate::VM)",
            "init_vec((Some(&mut (*vm).stack)).unwrap())",
            "vm.steps = 0",
        ],
        &["&raw mut (vm.stack)", "&mut *(&raw mut"],
    );
}

#[test]
fn test_rewriter_promotes_multiple_struct_fields_with_distinct_lifetimes() {
    run_test(
        r#"
#[repr(C)]
pub struct Pair {
    pub a: *mut i32,
    pub b: *const i32,
}

pub unsafe fn sum(mut x: i32, y: i32) -> i32 {
    let mut pair = Pair { a: &raw mut x, b: &raw const y };
    *pair.a = 3;
    *pair.a + *pair.b
}
"#,
        &[
            "pub struct Pair<'a, 'b>",
            "pub a: Option<&'a mut i32>",
            "pub b: Option<&'b i32>",
            "Pair { a: Some(&mut x), b: Some(&y) }",
        ],
        &["pub a: *mut i32", "pub b: *const i32"],
    );
}

#[test]
fn test_rewriter_keeps_demoted_struct_field_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn conflict() -> i32 {
    let mut x = 0;
    let mut h = Holder { p: &raw mut x };
    x = 1;
    *h.p = 2;
    x
}
"#,
        &["pub p: *mut i32", "*h.p = 2"],
        &["pub struct Holder<'a>", "Option<&'a mut i32>"],
    );
}

#[test]
fn test_rewriter_promotes_identity_return_with_named_lifetime() {
    run_test(
        r#"
pub unsafe fn id(x: *mut i32) -> *mut i32 {
    return x;
}
"#,
        &[
            "pub unsafe fn id<'a>(x: &'a mut i32) -> &'a mut i32",
            "return x;",
        ],
        &["-> *mut i32", "Option<&'a mut i32>"],
    );
}

#[test]
fn test_rewriter_promotes_extern_c_identity_return_with_named_lifetime() {
    run_test(
        r#"
pub unsafe extern "C" fn id(x: *mut i32) -> *mut i32 {
    return x;
}
"#,
        &[
            "pub unsafe extern \"C\" fn id<'a>(x: &'a mut i32) -> &'a mut i32",
            "return x;",
        ],
        &["-> *mut i32", "Option<&'a mut i32>"],
    );
}

#[test]
fn test_rewriter_promotes_interprocedural_return_lifetime() {
    run_test(
        r#"
pub unsafe fn id(x: *mut i32) -> *mut i32 {
    x
}

pub unsafe fn wrap(y: *mut i32) -> *mut i32 {
    id(y)
}
"#,
        &[
            "pub unsafe fn id<'a>(x: &'a mut i32) -> &'a mut i32",
            "pub unsafe fn wrap<'a>(y: &'a mut i32) -> &'a mut i32",
            "id(y)",
        ],
        &["-> *mut i32", "id((y) as *mut"],
    );
}

#[test]
fn test_rewriter_preserves_nullable_returned_borrow_lifetime() {
    run_test(
        r#"
pub unsafe fn maybe(flag: bool, x: *mut i32) -> *mut i32 {
    if flag { x } else { core::ptr::null_mut() }
}
"#,
        &[
            "pub unsafe fn maybe<'a>(flag: bool, mut x: Option<&'a mut i32>)",
            "-> Option<&'a mut i32>",
            "if flag { x } else { None }",
            "None",
        ],
        &["-> &'a mut i32", "panic!()"],
    );
}

#[test]
fn test_rewriter_preserves_nullable_returned_borrow_through_local() {
    run_test(
        r#"
pub unsafe fn maybe_local(flag: bool, x: *mut i32) -> *mut i32 {
    let r = if flag { x } else { core::ptr::null_mut() };
    r
}
"#,
        &[
            "pub unsafe fn maybe_local<'a>(flag: bool, mut x: Option<&'a mut i32>)",
            "-> Option<&'a mut i32>",
            "let mut r: Option<&mut i32> = if flag { x } else { None }",
            "r",
        ],
        &["-> &'a mut i32", "panic!()"],
    );
}

#[test]
fn test_rewriter_preserves_nullable_returned_borrow_null_literal() {
    run_test(
        r#"
pub unsafe fn maybe_zero(flag: bool, x: *mut i32) -> *mut i32 {
    if flag { x } else { 0 as *mut i32 }
}
"#,
        &[
            "pub unsafe fn maybe_zero<'a>(flag: bool, mut x: Option<&'a mut i32>)",
            "-> Option<&'a mut i32>",
            "if flag { x } else { None }",
        ],
        &["-> &'a mut i32", "panic!()"],
    );
}

#[test]
fn test_rewriter_preserves_nullable_returned_input_without_null_return() {
    run_test(
        r#"
pub unsafe fn pick(x: *mut i32, y: *mut i32) -> *mut i32 {
    *y = 1;
    if x.is_null() { y } else { x }
}
"#,
        &[
            "mut x: Option<&'a mut i32>",
            "y: &'a mut i32",
            "-> &'a mut i32",
            "if x.is_none()",
        ],
        &["x: &'a mut i32", "if false"],
    );
}

#[test]
fn test_rewriter_generated_lifetime_names_skip_existing_params() {
    run_test(
        r#"
pub unsafe fn pick_existing<'a>(x: &'a i32, y: *const i32) -> *const i32 {
    y
}
"#,
        &["pub unsafe fn pick_existing<'a, 'b>(x: &'a i32, y: &'b i32) -> &'b i32"],
        &["-> *const i32"],
    );
}

#[test]
fn test_rewriter_rewrites_fn_pointer_input_with_raw_return_relation() {
    run_test(
        r#"
pub unsafe fn id(x: *mut i32) -> *mut i32 {
    x
}

pub unsafe fn caller(mut x: i32) -> i32 {
    let f: unsafe fn(*mut i32) -> *mut i32 = id;
    let p = f(&mut x);
    *p
}
"#,
        &[
            "let f: unsafe fn(Option<&i32>) -> *mut i32 = id",
            "pub unsafe fn id(x: Option<&i32>) -> *mut i32",
        ],
        &["pub unsafe fn id<'a>"],
    );
}

#[test]
fn test_rewriter_bridges_raw_scalar_allocator_root_and_free() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_nested() {
    let mut p: *mut *mut i32 =
        malloc(std::mem::size_of::<*mut i32>()) as *mut *mut i32;
    free(p as *mut core::ffi::c_void);
}
"#,
        &["Box::leak(Box::new(", "Box::from_raw("],
        &[
            "let mut p: *mut *mut i32 = malloc(",
            "free(p as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_scalar_raw_malloc_when_only_alias_is_freed() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_nested_alias() {
    let p: *mut *mut i32 =
        malloc(std::mem::size_of::<*mut i32>()) as *mut *mut i32;
    let q = p;
    free(q as *mut core::ffi::c_void);
}
"#,
        &[
            "malloc(std::mem::size_of::<*mut i32>())",
            "free(q as *mut core::ffi::c_void",
        ],
        &["Box::into_raw(", "Box::from_raw("],
    );
}

#[test]
fn test_rewriter_bridges_raw_scalar_calloc_root_and_free() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_one() {
    let p: *mut *mut i32 =
        calloc(1, std::mem::size_of::<*mut i32>()) as *mut *mut i32;
    free(p as *mut core::ffi::c_void);
}
"#,
        &["Box::leak(Box::new(", "Box::from_raw("],
        &[
            "calloc(1, std::mem::size_of::<*mut i32>())",
            "free(p as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_bridges_raw_scalar_typedef_sizeof_allocator_root_and_free() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Node {
    pub next: *mut NodeAlias,
    pub value: i32,
}

pub type NodeAlias = Node;

#[repr(C)]
pub struct List {
    pub head: *mut NodeAlias,
}

pub unsafe fn push_alias_sized(list: *mut List) {
    let node: *mut NodeAlias =
        malloc(std::mem::size_of::<NodeAlias>()) as *mut NodeAlias;
    if node.is_null() {
        return;
    }
    (*node).next = (*list).head;
    (*list).head = node;
}

pub unsafe fn clear_alias_sized(list: *mut List) {
    free((*list).head as *mut core::ffi::c_void);
}
"#,
        &["Box::leak(Box::new(", "Box::from_raw("],
        &[
            "malloc(std::mem::size_of::<NodeAlias>())",
            "free(p as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_bridges_raw_scalar_field_allocator_root_and_free() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Node {
    pub value: i32,
}

#[repr(C)]
pub struct Holder {
    pub node: *mut Node,
}

pub unsafe fn init_and_clear(holder: *mut Holder) {
    (*holder).node = malloc(std::mem::size_of::<Node>()) as *mut Node;
    if ((*holder).node).is_null() {
        return;
    }
    (*(*holder).node).value = 7;
    free((*holder).node as *mut core::ffi::c_void);
}
"#,
        &["Box::leak(Box::new(", "Box::from_raw("],
        &[
            "malloc(std::mem::size_of::<Node>())",
            "free((*holder).node as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_raw_bridge_default_uses_fieldless_enum_zero_variant() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(i32)]
pub enum StatusCode {
    STATUS_ERROR = -1,
    STATUS_SUCCESS = 0,
    STATUS_WARNING = 1,
}

#[repr(C)]
pub struct ComputationResult {
    pub value: i32,
    pub status: StatusCode,
}

pub unsafe fn alloc_results(count: usize) {
    let results: *mut ComputationResult =
        malloc(count * std::mem::size_of::<crate::ComputationResult>()) as *mut crate::ComputationResult;
    free(results as *mut core::ffi::c_void);
}
"#,
        &[
            "Box::leak(std::iter::repeat_with(||",
            "status: crate::StatusCode::STATUS_SUCCESS",
            "Box::from_raw(std::ptr::slice_from_raw_parts_mut",
        ],
        &[
            "malloc(count * std::mem::size_of::<crate::ComputationResult>())",
            "free(results as *mut core::ffi::c_void);",
        ],
    );
}

#[test]
fn test_rewriter_keeps_dynamic_local_struct_field_free_raw() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Pixel {
    pub value: i32,
}

#[repr(C)]
pub struct Image {
    pub pix: *mut Pixel,
}

pub unsafe fn load(len: usize) {
    let mut img = Image { pix: core::ptr::null_mut() };
    img.pix = malloc(len * std::mem::size_of::<Pixel>()) as *mut Pixel;
    free(img.pix as *mut core::ffi::c_void);
}

pub unsafe fn load_via_local(len: usize) {
    let mut img = Image { pix: core::ptr::null_mut() };
    let pix = malloc(len * std::mem::size_of::<Pixel>()) as *mut Pixel;
    img.pix = pix;
    free(img.pix as *mut core::ffi::c_void);
}
"#,
        &[
            "img.pix = malloc(len * std::mem::size_of::<Pixel>()) as *mut Pixel;",
            "let mut pix: *mut crate::Pixel",
            "img.pix = pix;",
            "free(img.pix as *mut core::ffi::c_void);",
        ],
        &["Box::from_raw("],
    );
}

#[test]
fn test_rewriter_bridges_raw_array_realloc_null_root_and_free() {
    run_test(
        r#"
extern "C" {
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_chars(len: usize) {
    let buf: *mut core::ffi::c_char =
        realloc(std::ptr::null_mut::<core::ffi::c_void>(), len) as *mut core::ffi::c_char;
    free(buf as *mut core::ffi::c_void);
}
"#,
        &["Box::leak(", "slice_from_raw_parts_mut", "Box::from_raw("],
        &[
            "realloc(std::ptr::null_mut::<core::ffi::c_void>(), len)",
            "free(buf as *mut core::ffi::c_void);",
        ],
    );
}

#[test]
fn test_rewriter_box_from_raw_free_evaluates_argument_once() {
    run_test(
        r#"
extern "C" {
    fn free(ptr: *mut core::ffi::c_void);
    fn alloc_node() -> *mut Node;
}

#[repr(C)]
pub struct Node {
    pub value: i32,
}

pub unsafe fn cleanup() {
    free(alloc_node() as *mut core::ffi::c_void);
}
"#,
        &["let __crat_raw_free =", "Box::from_raw((__crat_raw_free)"],
        &["Box::from_raw((alloc_node()", "unsafe {"],
    );
}

#[test]
fn test_rewriter_keeps_owned_returners_boxed_when_one_result_is_freed() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn foo() -> *mut i32 {
    let p: *mut i32 = malloc(std::mem::size_of::<i32>()) as *mut i32;
    p
}

pub unsafe fn bar() -> *mut i32 {
    let p: *mut i32 = malloc(std::mem::size_of::<i32>()) as *mut i32;
    p
}

pub unsafe fn baz() {
    let p: *mut i32 = bar();
    free(p as *mut core::ffi::c_void);
}
"#,
        &[
            "pub unsafe fn foo() -> Box<i32>",
            "pub unsafe fn bar() -> Box<i32>",
            "let mut p: Box<i32>",
            "drop(p);",
        ],
        &[
            "pub unsafe fn bar() -> *mut i32",
            "free(p as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_nullable_owned_returner_boxed_when_result_is_freed() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn make_owned(flag: i32) -> *mut i32 {
    if flag == 0 {
        return std::ptr::null_mut();
    }
    let p: *mut i32 = malloc(std::mem::size_of::<i32>()) as *mut i32;
    p
}

pub unsafe fn cleanup(flag: i32) {
    let p: *mut i32 = make_owned(flag);
    if !p.is_null() {
        free(p as *mut core::ffi::c_void);
    }
}
"#,
        &[
            "pub unsafe fn make_owned(flag: i32) -> Option<Box<i32>>",
            "let mut p: Option<Box<i32>>",
            "if !p.is_none()",
            "drop((p).take());",
        ],
        &[
            "pub unsafe fn make_owned(flag: i32) -> *mut i32",
            "free(p as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_c_exposed_owned_returner_raw() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("make_owned".to_string());
    run_test_with_config(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[no_mangle]
pub unsafe extern "C" fn make_owned(flag: i32) -> *mut i32 {
    if flag == 0 {
        return std::ptr::null_mut();
    }
    let p: *mut i32 = malloc(std::mem::size_of::<i32>()) as *mut i32;
    p
}
"#,
        &config,
        &[
            "pub unsafe extern \"C\" fn make_owned(flag: i32) -> *mut i32",
            "Box::into_raw(",
        ],
        &["pub unsafe extern \"C\" fn make_owned(flag: i32) -> Option<Box<i32>>"],
    );
}

#[test]
fn test_rewriter_keeps_predeclared_nullable_owned_call_result_boxed() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn make_buffer(flag: i32) -> *mut i8 {
    if flag == 0 {
        return std::ptr::null_mut();
    }
    let p: *mut i8 = malloc(4) as *mut i8;
    p
}

pub unsafe fn first_byte(buffer: *const i8) -> *const i8 {
    if buffer.is_null() {
        return std::ptr::null();
    }
    buffer
}

pub unsafe fn cleanup(flag: i32) {
    let mut buffer: *mut i8 = std::ptr::null_mut();
    let mut found: *const i8 = std::ptr::null();
    buffer = make_buffer(flag);
    if !buffer.is_null() {
        found = first_byte(buffer);
        if !found.is_null() {
            let _offset = found.offset_from(buffer);
        }
        free(buffer as *mut core::ffi::c_void);
        buffer = std::ptr::null_mut();
    }
}
"#,
        &[
            "pub unsafe fn make_buffer(flag: i32) -> Option<Box<[i8]>>",
            "let mut buffer: Option<Box<[i8]>> = None;",
            "buffer = make_buffer(flag);",
            "if !buffer.is_none()",
            "drop((buffer).take());",
            "buffer = None;",
        ],
        &[
            "pub unsafe fn make_buffer(flag: i32) -> *mut i8",
            "let mut buffer: *mut i8",
            "free(buffer as *mut core::ffi::c_void);",
        ],
    );
}

#[test]
fn test_rewriter_does_not_move_box_into_later_freed_alias() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn compare_allocations(val: i32) -> i32 {
    let ptr1: *mut i32 = malloc(std::mem::size_of::<i32>()) as *mut i32;
    let mut alias: *mut i32 = std::ptr::null_mut();
    if ptr1.is_null() {
        free(ptr1 as *mut core::ffi::c_void);
        return -1;
    }
    *ptr1 = val;
    alias = ptr1;
    let result = *alias;
    free(ptr1 as *mut core::ffi::c_void);
    result
}
"#,
        &["drop(ptr1);"],
        &["alias = Some(ptr1);"],
    );
}

#[test]
fn test_rewriter_keeps_wrapper_freed_local_raw() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn cleanup_resources(ptr: *mut i8) {
    if !ptr.is_null() {
        free(ptr as *mut core::ffi::c_void);
    }
}

pub unsafe fn cleanup() {
    let mut dynamic_str: *mut i8 = std::ptr::null_mut();
    dynamic_str = malloc(50) as *mut i8;
    cleanup_resources(dynamic_str);
}
"#,
        &[
            "let mut dynamic_str: *mut i8 = std::ptr::null_mut();",
            "cleanup_resources((dynamic_str).as_ref());",
        ],
        &["let mut dynamic_str: Option<Box<[i8]>>"],
    );
}

#[test]
fn test_rewriter_keeps_raw_storage_call_result_raw() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn dup() -> *mut i8 {
    let p: *mut i8 = malloc(8) as *mut i8;
    p
}

pub unsafe fn store(slot: *mut *mut i8) {
    *slot = dup();
}
"#,
        &["pub unsafe fn dup() -> *mut i8", "*slot = dup();"],
        &["pub unsafe fn dup() -> Option<Box<[i8]>>"],
    );
}

#[test]
fn test_rewriter_consumes_direct_owned_call_result_free() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn make_owned() -> *mut i32 {
    let p: *mut i32 = malloc(std::mem::size_of::<i32>()) as *mut i32;
    p
}

pub unsafe fn cleanup() {
    free(make_owned() as *mut core::ffi::c_void);
}
"#,
        &[
            "pub unsafe fn make_owned() -> Box<i32>",
            "drop(make_owned());",
        ],
        &[
            "pub unsafe fn make_owned() -> *mut i32",
            "free(make_owned() as *mut core::ffi::c_void);",
            "Box::from_raw(",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_bridges_outermost_local_allocator_wrappers() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_zeroed(num: usize, size: usize) -> *mut core::ffi::c_void {
    let out: *mut core::ffi::c_void = calloc(num, size);
    if out.is_null() {
        std::process::abort();
    }
    out
}

pub unsafe fn dealloc_ptr(ptr: *mut core::ffi::c_void) {
    free(ptr);
}

pub unsafe fn foo() {
    let p: *mut i32 = alloc_zeroed(1, std::mem::size_of::<i32>()) as *mut i32;
    dealloc_ptr(p as *mut core::ffi::c_void);
}
"#,
        &["Box::leak(Box::new(", "Box::from_raw("],
        &[
            "alloc_zeroed(1, std::mem::size_of::<i32>())",
            "dealloc_ptr(p as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_generalizes_wrapper_returning_allocated_local() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
    fn snprintf(dst: *mut core::ffi::c_char, size: usize, fmt: *const core::ffi::c_char, ...);
}

pub unsafe fn create_msg(v: i32) -> *mut core::ffi::c_char {
    let msg: *mut core::ffi::c_char = malloc(64) as *mut core::ffi::c_char;
    if msg.is_null() {
        return std::ptr::null_mut();
    }
    snprintf(msg, 64, b"value=%d\0" as *const u8 as *const core::ffi::c_char, v);
    msg
}

pub unsafe fn free_msg(msg: *mut core::ffi::c_void) {
    free(msg);
}

pub unsafe fn caller() {
    let msg: *mut core::ffi::c_char = create_msg(7);
    free_msg(msg as *mut core::ffi::c_void);
}
"#,
        &["Box::leak(", "slice_from_raw_parts_mut", "Box::from_raw("],
        &["malloc(64)", "free_msg(msg as *mut core::ffi::c_void);"],
    );
}

#[test]
fn test_rewriter_keeps_initialized_allocator_wrapper_call_raw() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct BufferArray {
    pub buffers: *mut i32,
    pub count: i32,
}

pub unsafe fn alloc_array(count: i32) -> *mut BufferArray {
    let arr: *mut BufferArray =
        malloc(std::mem::size_of::<BufferArray>()) as *mut BufferArray;
    if arr.is_null() {
        return std::ptr::null_mut();
    }
    (*arr).buffers = malloc((count as usize) * std::mem::size_of::<i32>()) as *mut i32;
    (*arr).count = count;
    arr
}

pub unsafe fn free_array(arr: *mut BufferArray) {
    free((*arr).buffers as *mut core::ffi::c_void);
    free(arr as *mut core::ffi::c_void);
}

pub unsafe fn caller(count: i32) {
    let arr: *mut BufferArray = alloc_array(count);
    if arr.is_null() {
        return;
    }
    *(*arr).buffers = 1;
    free_array(arr);
}
"#,
        &[
            "alloc_array(count)",
            "let mut arr: Box<crate::BufferArray>",
            "(*arr).buffers =\n        malloc((count as usize) * std::mem::size_of::<i32>())",
        ],
        &["let mut arr: *mut crate::BufferArray = Box::into_raw(Box::new"],
    );
}

#[test]
fn test_rewriter_generalizes_wrapper_with_internal_free_after_foreign_use() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
    fn memcpy(dst: *mut core::ffi::c_void, src: *const core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn copy_and_sum(src: *mut i32, count: usize) -> i32 {
    let dest: *mut i32 =
        malloc(count * std::mem::size_of::<i32>()) as *mut i32;
    if dest.is_null() {
        return -1;
    }
    memcpy(
        dest as *mut core::ffi::c_void,
        src as *const core::ffi::c_void,
        count * std::mem::size_of::<i32>(),
    );
    let out = *dest;
    free(dest as *mut core::ffi::c_void);
    out
}
"#,
        &[
            "pub unsafe fn copy_and_sum(src: &[i32], count: usize) -> i32",
            "let mut dest: Box<[i32]>",
            "collect::<Vec<i32>>().into_boxed_slice()",
            "memcpy((&mut (dest)[..]).as_mut_ptr() as *mut _,",
            "drop(dest);",
        ],
        &[
            "malloc(count * std::mem::size_of::<i32>())",
            "free(dest as *mut core::ffi::c_void);",
            "Box::leak(",
            "slice_from_raw_parts_mut",
            "Box::from_raw(",
        ],
    );
}

#[test]
fn test_rewriter_preserves_boxed_slice_offset_projection() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn copy_and_sum(src: *mut i32, count: i32) -> i32 {
    let dest: *mut i32 =
        malloc(count as usize * std::mem::size_of::<i32>()) as *mut i32;
    if dest.is_null() {
        return -1;
    }
    let mut i = 0;
    while i < count {
        *dest.offset(i as isize) = *src.offset(i as isize);
        i += 1;
    }
    let mut sum = 0;
    let mut j = 0;
    while j < count {
        sum += *dest.offset(j as isize);
        j += 1;
    }
    free(dest as *mut core::ffi::c_void);
    sum
}
"#,
        &[
            "let mut dest: Box<[i32]>",
            "[(i as isize) as usize..]",
            "[(j as isize) as usize..]",
        ],
        &["(&mut (dest)[..])[0]", "sum += (&(dest)[..])[0]"],
    );
}

#[test]
fn test_rewriter_keeps_wrapper_escape_through_parameter_raw_in_m9() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn alloc_into(out: *mut *mut *mut i32) {
    let p: *mut *mut i32 =
        malloc(std::mem::size_of::<*mut i32>()) as *mut *mut i32;
    *out = p;
}
"#,
        &["malloc(std::mem::size_of::<*mut i32>())"],
        &["Box::into_raw(", "Box::leak("],
    );
}

#[test]
fn test_rewriter_keeps_wrapper_escape_through_global_raw_in_m9() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

static mut SLOT: *mut *mut i32 = std::ptr::null_mut();

pub unsafe fn save_global() {
    let p: *mut *mut i32 =
        malloc(std::mem::size_of::<*mut i32>()) as *mut *mut i32;
    SLOT = p;
}
"#,
        &["malloc(std::mem::size_of::<*mut i32>())"],
        &["Box::into_raw(", "Box::leak("],
    );
}

#[test]
fn test_rewriter_admits_local_scalar_temp_malloc_free_shape_in_m10() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
    fn strlen(s: *const core::ffi::c_char) -> usize;
    fn puts(s: *const core::ffi::c_char) -> core::ffi::c_int;
}

pub unsafe fn helper(out: *mut core::ffi::c_char) -> i32 {
    let len: usize = strlen(out).wrapping_add(5);
    let buf: *mut core::ffi::c_char = malloc(len) as *mut core::ffi::c_char;
    if buf.is_null() {
        return -1;
    }
    puts(buf);
    free(buf as *mut core::ffi::c_void);
    0
}

pub unsafe fn caller(out: *mut core::ffi::c_char) -> i32 {
    helper(out)
}
"#,
        &[
            "pub unsafe fn helper(out: &[i8]) -> i32",
            "let mut buf: Box<[i8]>",
            "collect::<Vec<i8>>().into_boxed_slice()",
            "puts((&mut (buf)[..]).as_mut_ptr());",
            "drop(buf);",
        ],
        &[
            "malloc(len)",
            "free(buf as *mut core::ffi::c_void);",
            "Box::leak(",
            "slice_from_raw_parts_mut",
            "Box::from_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_field_read_size_source_raw_in_m10() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct State {
    pub len: usize,
}

pub unsafe fn helper(state: State) -> i32 {
    let len: usize = state.len;
    let buf: *mut core::ffi::c_char = malloc(len) as *mut core::ffi::c_char;
    if buf.is_null() {
        return -1;
    }
    free(buf as *mut core::ffi::c_void);
    0
}

pub unsafe fn caller(state: State) -> i32 {
    helper(state)
}
"#,
        &["malloc(len)", "free(buf as *mut core::ffi::c_void);"],
        &["Box::leak(", "Box::from_raw(", "slice_from_raw_parts_mut"],
    );
}

#[test]
fn test_rewriter_keeps_deref_read_size_source_raw_in_m10() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn helper(n: *const usize) -> i32 {
    let len: usize = *n;
    let buf: *mut core::ffi::c_char = malloc(len) as *mut core::ffi::c_char;
    if buf.is_null() {
        return -1;
    }
    free(buf as *mut core::ffi::c_void);
    0
}

pub unsafe fn caller(n: *const usize) -> i32 {
    helper(n)
}
"#,
        &["malloc(len)", "free(buf as *mut core::ffi::c_void);"],
        &["Box::leak(", "Box::from_raw(", "slice_from_raw_parts_mut"],
    );
}

#[test]
fn test_rewriter_allows_borrow_only_local_callee_for_raw_bridge_in_m10() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

unsafe fn touch(state: *mut State) -> i32 {
    (*state).value = 7;
    (*state).value
}

pub unsafe fn helper() -> i32 {
    let s: *mut State = calloc(1, std::mem::size_of::<State>()) as *mut State;
    if s.is_null() {
        return -1;
    }
    let result = touch(s);
    free(s as *mut core::ffi::c_void);
    result
}
"#,
        &[
            "let mut s: Box<crate::State>",
            "Some(Box::new(crate::State {",
            "value: <i32 as Default>::default()",
            "unsafe fn touch(mut state: &mut crate::State) -> i32",
            "let result = touch((Some(&mut *((s).as_mut()))).unwrap());",
            "drop(s);",
        ],
        &[
            "calloc(1, std::mem::size_of::<State>())",
            "free(s as *mut core::ffi::c_void);",
            "Box::leak(",
            "slice_from_raw_parts_mut",
            "Box::from_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_local_callee_pointer_alias_raw_in_m10() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

unsafe fn touch_with_alias(state: *mut State) -> i32 {
    let alias = state;
    (*alias).value = 7;
    (*alias).value
}

pub unsafe fn helper() -> i32 {
    let s: *mut State = calloc(1, std::mem::size_of::<State>()) as *mut State;
    if s.is_null() {
        return -1;
    }
    let result = touch_with_alias(s);
    free(s as *mut core::ffi::c_void);
    result
}
"#,
        &[
            "let mut s: Box<crate::State>",
            "unsafe fn touch_with_alias(mut state: &mut crate::State) -> i32",
            "let result = touch_with_alias((Some(&mut *((s).as_mut()))).unwrap());",
            "drop(s);",
        ],
        &[
            "calloc(1, std::mem::size_of::<State>())",
            "free(s as *mut core::ffi::c_void);",
            "Box::into_raw(",
            "Box::leak(",
            "Box::from_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_local_callee_pointer_return_raw_in_m10() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

unsafe fn echo(state: *mut State) -> *mut State {
    state
}

pub unsafe fn helper() -> i32 {
    let s: *mut State = calloc(1, std::mem::size_of::<State>()) as *mut State;
    if s.is_null() {
        return -1;
    }
    let result = echo(s);
    free(result as *mut core::ffi::c_void);
    0
}
"#,
        &["Box::leak(Box::new(", "Box::from_raw("],
        &[
            "calloc(1, std::mem::size_of::<State>())",
            "free(result as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_local_callee_pointer_free_raw_in_m10() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

unsafe fn consume(state: *mut State) {
    free(state as *mut core::ffi::c_void);
}

pub unsafe fn helper() -> i32 {
    let s: *mut State = calloc(1, std::mem::size_of::<State>()) as *mut State;
    if s.is_null() {
        return -1;
    }
    consume(s);
    0
}
"#,
        &["Box::leak(Box::new(", "Box::from_raw("],
        &[
            "calloc(1, std::mem::size_of::<State>())",
            "free(state as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_local_callee_pointer_global_store_raw_in_m10() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

static mut SLOT: *mut State = std::ptr::null_mut();

unsafe fn stash(state: *mut State) {
    SLOT = state;
}

pub unsafe fn helper() -> i32 {
    let s: *mut State = calloc(1, std::mem::size_of::<State>()) as *mut State;
    if s.is_null() {
        return -1;
    }
    stash(s);
    free(s as *mut core::ffi::c_void);
    0
}
"#,
        &["Box::leak(Box::new(", "Box::from_raw("],
        &[
            "calloc(1, std::mem::size_of::<State>())",
            "free(s as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_cjson_style_local_field_storage_raw_in_m10() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

#[repr(C)]
pub struct PrintBuf {
    pub buffer: *mut State,
    pub length: usize,
}

unsafe fn print_preallocated_like(buffer: *mut State, length: usize) -> i32 {
    let mut p = PrintBuf {
        buffer: std::ptr::null_mut::<State>(),
        length: 0,
    };
    p.buffer = buffer;
    p.length = length;
    if p.buffer.is_null() {
        0
    } else {
        1
    }
}

pub unsafe fn helper() -> i32 {
    let s: *mut State = calloc(1, std::mem::size_of::<State>()) as *mut State;
    if s.is_null() {
        return -1;
    }
    let result = print_preallocated_like(s, 1);
    free(s as *mut core::ffi::c_void);
    result
}
"#,
        &[
            "let mut s: Box<crate::State>",
            "unsafe fn print_preallocated_like(mut buffer: *mut crate::State,",
            "print_preallocated_like(((s).as_mut()) as *mut crate::State, 1)",
            "drop(s);",
        ],
        &[
            "calloc(1, std::mem::size_of::<State>())",
            "free(s as *mut core::ffi::c_void);",
            "Box::into_raw(",
            "Box::leak(",
            "Box::from_raw(",
        ],
    );
}

#[test]
fn test_rewriter_allows_memcpy_style_local_helper_use_in_m12() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
    fn memcpy(
        dest: *mut core::ffi::c_void,
        src: *const core::ffi::c_void,
        n: usize,
    ) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

unsafe fn init_state(state: *mut State) {
    let template = State { value: 7 };
    memcpy(
        state as *mut core::ffi::c_void,
        &template as *const State as *const core::ffi::c_void,
        std::mem::size_of::<State>(),
    );
}

pub unsafe fn checkshift_like() -> i32 {
    let state: *mut State = malloc(std::mem::size_of::<State>()) as *mut State;
    if state.is_null() {
        return -1;
    }
    init_state(state);
    let result = (*state).value;
    free(state as *mut core::ffi::c_void);
    result
}
"#,
        &["Box::leak(Box::new(", "Box::from_raw("],
        &[
            "malloc(std::mem::size_of::<State>())",
            "free(state as *mut core::ffi::c_void);",
            "Box::into_raw(",
        ],
    );
}

#[test]
fn test_rewriter_consumes_direct_scalar_free_for_boxed_root() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct State {
    pub value: i32,
}

pub unsafe fn free_state() {
    let state: *mut State = malloc(std::mem::size_of::<State>()) as *mut State;
    if state.is_null() {
        return;
    }
    (*state).value = 7;
    free(state as *mut core::ffi::c_void);
}
"#,
        &[
            "let mut state: Box<crate::State>",
            "if false { return; }",
            "(*state).value = 7;",
            "drop(state);",
        ],
        &[
            "malloc(std::mem::size_of::<State>())",
            "free(state as *mut core::ffi::c_void);",
            "Box::from_raw(",
            "Box::into_raw(",
            "Box::leak(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_unknown_foreign_helper_use_raw_in_m12() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
    fn puts(s: *const core::ffi::c_char) -> i32;
}

unsafe fn show_task(task: *mut core::ffi::c_char) {
    puts(task);
}

pub unsafe fn driver_like(length: usize) -> i32 {
    let task: *mut core::ffi::c_char = malloc(length.wrapping_add(1)) as *mut core::ffi::c_char;
    if task.is_null() {
        return -1;
    }
    show_task(task);
    free(task as *mut core::ffi::c_void);
    0
}
"#,
        &[
            "malloc(length.wrapping_add(1))",
            "free(task as *mut core::ffi::c_void);",
        ],
        &["Box::into_raw(", "Box::leak(", "Box::from_raw("],
    );
}

#[test]
fn test_rewriter_keeps_raw_local_for_raw_return_call_result_assignment() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn snprintf(
        s: *mut core::ffi::c_char,
        maxlen: usize,
        format: *const core::ffi::c_char,
        ...
    ) -> i32;
}

pub unsafe fn create_result_string(
    op: *const core::ffi::c_char,
    val: i32,
) -> *mut core::ffi::c_char {
    let str: *mut core::ffi::c_char = malloc(64) as *mut core::ffi::c_char;
    if str.is_null() {
        return std::ptr::null_mut();
    }
    snprintf(
        str,
        64,
        b"Operation: %s, Value: %d\0" as *const u8 as *const core::ffi::c_char,
        op,
        val,
    );
    str
}

pub unsafe fn multiply_with_log(a: i32, b: i32) -> (i32, *mut i8) {
    let mut log_msg: *mut i8 = std::ptr::null_mut();
    log_msg = create_result_string(
        b"multiply\0" as *const u8 as *const core::ffi::c_char,
        a * b,
    ) as *mut i8;
    if log_msg.is_null() {
        return (0, log_msg);
    }
    (a * b, log_msg)
}
"#,
        &[
            "pub unsafe fn multiply_with_log(a: i32, b: i32) -> (i32, *mut i8)",
            "let mut log_msg: *mut i8 = std::ptr::null_mut();",
            "log_msg =",
            "create_result_string(bytemuck::cast_slice",
        ],
        &[
            "Option<&mut i8>",
            ".as_mut()",
            "return (0, (log_msg).as_deref_mut()",
        ],
    );
}

#[test]
fn test_rewriter_allows_returned_byte_calloc_buffer_in_m13() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn decode_like(len: usize, fail: bool) -> *mut core::ffi::c_char {
    let dest: *mut core::ffi::c_char =
        calloc(std::mem::size_of::<core::ffi::c_char>(), len) as *mut core::ffi::c_char;
    if dest.is_null() {
        return std::ptr::null_mut();
    }
    if fail {
        free(dest as *mut core::ffi::c_void);
        return std::ptr::null_mut();
    }
    dest
}
"#,
        &["Box::leak("],
        &["calloc(std::mem::size_of::<core::ffi::c_char>(), len)"],
    );
}

#[test]
fn test_rewriter_consumes_direct_boxed_slice_free() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_many() {
    let buf: *mut i32 = malloc(4 * std::mem::size_of::<i32>()) as *mut i32;
    if buf.is_null() {
        return;
    }
    *buf.offset(1) = 7;
    free(buf as *mut core::ffi::c_void);
}
"#,
        &[
            "let mut buf: Box<[i32]>",
            "if false { return; }",
            "drop(buf);",
        ],
        &[
            "malloc(4 * std::mem::size_of::<i32>())",
            "free(buf as *mut core::ffi::c_void);",
            "Box::leak(",
            "Box::from_raw(",
        ],
    );
}

#[test]
#[ignore = "requires branchy owning-return inference beyond direct free consumption"]
fn test_rewriter_consumes_branchy_free_or_return_boxed_slice() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_or_free(flag: bool) -> *mut i32 {
    let buf: *mut i32 = malloc(4 * std::mem::size_of::<i32>()) as *mut i32;
    if buf.is_null() {
        return std::ptr::null_mut();
    }
    if flag {
        free(buf as *mut core::ffi::c_void);
        return std::ptr::null_mut();
    }
    buf
}
"#,
        &[
            "pub unsafe fn alloc_or_free(flag: bool) -> Option<Box<[i32]>>",
            "let mut buf: Option<Box<[i32]>>",
            "if buf.is_none()",
            "drop((buf).take());",
            "return None;",
            "(buf).take()",
        ],
        &[
            "malloc(4 * std::mem::size_of::<i32>())",
            "free(buf as *mut core::ffi::c_void);",
            "Box::from_raw(",
            "Box::leak(",
        ],
    );
}

#[test]
fn test_rewriter_keeps_opaque_byte_calloc_wrapper_return_raw_in_m13() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn opaque_factory(len: usize) -> *mut core::ffi::c_void {
    let dest: *mut core::ffi::c_void =
        calloc(std::mem::size_of::<core::ffi::c_char>(), len);
    if dest.is_null() {
        return std::ptr::null_mut();
    }
    dest
}
"#,
        &["calloc(std::mem::size_of::<core::ffi::c_char>(), len)"],
        &["Box::leak(", "Box::into_raw("],
    );
}

#[test]
fn test_rewriter_keeps_helper_cleanup_byte_calloc_raw_in_m13() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

unsafe fn cleanup_resources(dynamic_buf: *mut core::ffi::c_void) {
    free(dynamic_buf);
}

pub unsafe fn decode_like(len: usize) -> i32 {
    let dest: *mut core::ffi::c_void =
        calloc(std::mem::size_of::<core::ffi::c_char>(), len);
    if dest.is_null() {
        return -1;
    }
    cleanup_resources(dest);
    0
}
"#,
        &[
            "calloc(std::mem::size_of::<core::ffi::c_char>(), len)",
            "cleanup_resources(dest);",
        ],
        &["Box::leak(", "Box::into_raw("],
    );
}

#[test]
fn test_rewriter_keeps_non_byte_reversed_calloc_raw_in_m13() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn alloc_words(len: usize) -> *mut i32 {
    let dest: *mut i32 = calloc(std::mem::size_of::<i32>(), len) as *mut i32;
    if dest.is_null() {
        return std::ptr::null_mut();
    }
    dest
}
"#,
        &["calloc(std::mem::size_of::<i32>(), len)"],
        &["Box::leak(", "Box::into_raw("],
    );
}

#[test]
fn test_rewriter_allows_byte_view_alias_of_returned_byte_buffer_in_m13() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn decode_like(len: usize) -> *mut core::ffi::c_char {
    let dest: *mut core::ffi::c_char =
        calloc(std::mem::size_of::<core::ffi::c_char>(), len) as *mut core::ffi::c_char;
    if dest.is_null() {
        return std::ptr::null_mut();
    }
    let mut p: *mut core::ffi::c_uchar = dest as *mut core::ffi::c_uchar;
    *p = b'A';
    p = p.offset(1);
    *p = 0;
    dest
}

pub unsafe fn caller(len: usize) {
    let dest = decode_like(len);
    if !dest.is_null() {
        free(dest as *mut core::ffi::c_void);
    }
}
"#,
        &["Box::leak("],
        &["calloc(std::mem::size_of::<core::ffi::c_char>(), len)"],
    );
}

#[test]
fn test_rewriter_keeps_returned_byte_buffer_alias_return_raw_in_m13() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn decode_like(len: usize) -> *mut core::ffi::c_char {
    let dest: *mut core::ffi::c_char =
        calloc(std::mem::size_of::<core::ffi::c_char>(), len) as *mut core::ffi::c_char;
    if dest.is_null() {
        return std::ptr::null_mut();
    }
    let p: *mut core::ffi::c_uchar = dest as *mut core::ffi::c_uchar;
    p as *mut core::ffi::c_char
}
"#,
        &["calloc(std::mem::size_of::<core::ffi::c_char>(), len)"],
        &["Box::leak(", "slice_from_raw_parts_mut", "Box::from_raw("],
    );
}

#[test]
fn test_rewriter_keeps_returned_byte_buffer_alias_free_raw_in_m13() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn decode_like(len: usize) -> *mut core::ffi::c_char {
    let dest: *mut core::ffi::c_char =
        calloc(std::mem::size_of::<core::ffi::c_char>(), len) as *mut core::ffi::c_char;
    if dest.is_null() {
        return std::ptr::null_mut();
    }
    let p: *mut core::ffi::c_uchar = dest as *mut core::ffi::c_uchar;
    free(p as *mut core::ffi::c_void);
    std::ptr::null_mut()
}
"#,
        &["calloc(std::mem::size_of::<core::ffi::c_char>(), len)"],
        &["Box::leak(", "slice_from_raw_parts_mut", "Box::from_raw("],
    );
}

#[test]
fn test_rewriter_keeps_returned_byte_buffer_alias_store_raw_in_m13() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
}

static mut SLOT: *mut core::ffi::c_uchar = std::ptr::null_mut();

pub unsafe fn decode_like(len: usize) -> *mut core::ffi::c_char {
    let dest: *mut core::ffi::c_char =
        calloc(std::mem::size_of::<core::ffi::c_char>(), len) as *mut core::ffi::c_char;
    if dest.is_null() {
        return std::ptr::null_mut();
    }
    let p: *mut core::ffi::c_uchar = dest as *mut core::ffi::c_uchar;
    SLOT = p;
    dest
}
"#,
        &["calloc(std::mem::size_of::<core::ffi::c_char>(), len)"],
        &["Box::leak(", "slice_from_raw_parts_mut", "Box::from_raw("],
    );
}

#[test]
fn test_rewriter_keeps_non_byte_view_alias_raw_in_m13() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn alloc_words(len: usize) -> *mut i32 {
    let dest: *mut i32 = calloc(std::mem::size_of::<i32>(), len) as *mut i32;
    if dest.is_null() {
        return std::ptr::null_mut();
    }
    let p: *mut u16 = dest as *mut u16;
    let _ = p;
    dest
}
"#,
        &["calloc(std::mem::size_of::<i32>(), len)"],
        &["Box::leak(", "slice_from_raw_parts_mut", "Box::from_raw("],
    );
}

#[test]
fn test_rewriter_keeps_owner_struct_field_frees_raw_in_m7() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

pub unsafe fn foo() {
    let owner: *mut Holder = malloc(std::mem::size_of::<Holder>()) as *mut Holder;
    (*owner).data = malloc(4 * std::mem::size_of::<i32>()) as *mut i32;
    free((*owner).data as *mut core::ffi::c_void);
    free(owner as *mut core::ffi::c_void);
}
"#,
        &[
            "malloc(4 * std::mem::size_of::<i32>())",
            "free((*owner).data as *mut core::ffi::c_void);",
        ],
        &[],
    );
}

#[test]
fn test_rewriter_preserves_fn_pointer_signature_with_opt_box_raw_fallback() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 5;
    return p;
}

pub unsafe fn caller() -> *mut i32 {
    let f: unsafe fn() -> *mut i32 = alloc_one;
    return f();
}
"#,
        &[
            "fn alloc_one() -> *mut i32",
            "let mut p: Box<i32>",
            "Box::into_raw(p) as *mut i32",
        ],
        &[],
    );
}

#[test]
fn test_rewriter_preserves_fn_pointer_signature_with_opt_boxed_slice_raw_fallback() {
    run_test(
        r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut i32;
}

pub unsafe fn alloc_arr() -> *mut i32 {
    let mut p: *mut i32 = calloc(4, std::mem::size_of::<i32>());
    *p.offset(1) = 7;
    p
}

pub unsafe fn caller() -> *mut i32 {
    let f: unsafe fn() -> *mut i32 = alloc_arr;
    return f();
}
"#,
        &[
            "fn alloc_arr() -> *mut i32",
            "let mut p: Box<[i32]>",
            "Box::leak(p).as_mut_ptr()",
            "let f: unsafe fn() -> *mut i32 = alloc_arr;",
        ],
        &["-> Option<Box<[i32]>>", "Box::into_raw("],
    );
}

#[test]
fn test_rewriter_mixed_return_shapes_do_not_infer_box_signature() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn maybe_alloc(flag: bool) -> *mut i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 7;
    if flag {
        return p;
    }
    return 0 as *mut i32;
}
"#,
        &[
            "fn maybe_alloc(flag: bool) -> *const i32",
            "std::ptr::null()",
            "Box::into_raw(p) as *const i32",
        ],
        &["-> Option<Box<i32>>"],
    );
}

// ===== Cross-PtrKind assignment tests (same type, no cast) =====

/// Raw q = OptRef p: p is promoted (OptRef), q copies p then p is used again,
/// invalidating q's copy-loan → q demoted to Raw. Conversion: raw_from_opt_ref.
#[test]
fn test_raw_eq_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    *p = 20 as libc::c_int;
    return *q;
}
"#,
        &[
            "let mut p: &mut i32",
            "let mut q: *const i32 = (p) as *mut i32",
        ],
        &[],
    );
}

/// OptRef q = Raw p: p has overlapping borrow conflict → demoted to Raw.
/// q = p after conflict, used simply → promoted to OptRef. Conversion: opt_ref_from_raw.
#[test]
fn test_ref_eq_raw() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    return *q;
}
"#,
        &[".as_ref()", "let mut q: &i32"],
        &[],
    );
}

/// Raw q = Slice p: p uses .offset() → Arr + promoted = Slice. q copies p,
/// then p used again → q's loan invalidated → q Raw. Conversion: raw_from_slice.
#[test]
fn test_raw_eq_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    *p.offset(2 as isize) = 30 as libc::c_int;
    return *q;
}
"#,
        &[".as_", "_ptr()", "&mut [i32]"],
        &[],
    );
}

/// OptRef q = Slice p: p uses .offset() → Slice. q = p (no array ops,
/// fatness doesn't propagate) → Ptr + promoted = OptRef. Conversion: opt_ref_from_slice.
#[test]
fn test_ref_eq_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    return *q;
}
"#,
        &[".first()", "Option<&i32>", "&mut [i32]"],
        &[],
    );
}

/// Slice q = Raw p: p has overlapping borrow conflict → demoted → Raw.
/// q = p, then q does array ops → Arr + promoted = Slice. Conversion: slice_from_raw.
#[test]
fn test_slice_eq_raw() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &["from_raw_parts_mut", "&mut [i32]"],
        &[],
    );
}

/// Slice q = Slice p: both p and q use .offset() → both Arr + promoted = Slice.
/// Conversion: slice_from_slice.
#[test]
fn test_slice_eq_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p;
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(1 as isize);
}
"#,
        &["&mut [i32]"],
        &["*mut"],
    );
}

// ===== Bytemuck type cast tests (same-size numerics) =====

/// OptRef q = OptRef p with type cast: both promoted (OptRef), but p is c_int
/// and q is c_uint. Same-size numerics → bytemuck::cast_ref.
/// Conversion: opt_ref_from_opt_ref (bytemuck branch).
#[test]
fn test_ref_eq_ref_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_uint = p as *mut libc::c_uint;
    return *q as libc::c_int;
}
"#,
        &[
            "bytemuck::cast_ref",
            "let mut q: &u32",
            "let mut p: &mut i32",
        ],
        &["*mut"],
    );
}

/// OptRef q = Slice p with type cast: p uses .offset() → Slice.
/// q = p (cast, no array ops) → OptRef. Same-size numerics → bytemuck::cast_ref.
/// Conversion: opt_ref_from_slice (bytemuck branch).
#[test]
fn test_ref_eq_slice_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_uint = p as *mut libc::c_uint;
    return *q as libc::c_int;
}
"#,
        &["bytemuck::cast_ref", "Option<&u32>", "&mut [i32]"],
        &["*mut"],
    );
}

/// Slice q = Slice p with type cast: both use .offset() → both Slice.
/// p is c_int, q is c_uint. Same-size numerics → bytemuck::cast_slice_mut.
/// Conversion: slice_from_slice (bytemuck branch).
#[test]
fn test_slice_eq_slice_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_uint = p as *mut libc::c_uint;
    *q.offset(0 as isize) = 30 as libc::c_uint;
    return *q.offset(1 as isize) as libc::c_int;
}
"#,
        &["bytemuck::cast_slice_mut", "&mut [u32]", "&mut [i32]"],
        &["*mut"],
    );
}

// ===== Non-bytemuck type cast tests =====
// For raw_from_*, opt_ref_from_raw, slice_from_raw: any different types trigger
// the cast branch (no bytemuck path exists). Uses c_int vs c_short.
// For opt_ref_from_opt_ref, opt_ref_from_slice: different-size numerics
// (c_int vs c_short) fail same_size → non-bytemuck else branch.
// For slice_from_slice: at least one non-numeric type needed (struct Pair)
// since all numerics go to bytemuck regardless of size.

/// Raw q = OptRef p, with type cast. q demoted via separate overlapping
/// borrow on y, then reassigned from OptRef p.
/// Conversion: raw_from_opt_ref (need_cast branch).
#[test]
fn test_raw_eq_ref_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut y: libc::c_short = 0 as libc::c_short;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_short = &mut y;
    let mut s: *mut libc::c_short = &mut y;
    *q = 1 as libc::c_short;
    *s = 2 as libc::c_short;
    q = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &["q = (p) as *mut i32 as *mut i16", "let mut p: &mut i32"],
        &["bytemuck"],
    );
}

/// Raw q = Slice p, with type cast. q demoted via separate overlapping
/// borrow on y, then reassigned from Slice p.
/// Conversion: raw_from_slice (need_cast branch).
#[test]
fn test_raw_eq_slice_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut y: libc::c_short = 0 as libc::c_short;
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_short = &mut y;
    let mut s: *mut libc::c_short = &mut y;
    *q = 1 as libc::c_short;
    *s = 2 as libc::c_short;
    q = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &["as_mut_ptr() as *mut _", "&mut [i32]"],
        &["bytemuck"],
    );
}

/// OptRef q = Raw p, with type cast. p has overlapping borrow conflict → Raw.
/// q = p with cast, used simply → OptRef.
/// Conversion: opt_ref_from_raw (need_cast branch).
#[test]
fn test_ref_eq_raw_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    let mut q: *mut libc::c_short = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &["as *const i16", ".as_ref()", "let mut q: &i16"],
        &["bytemuck"],
    );
}

#[test]
fn test_rewriter_wraps_raw_to_opt_ref_call_boundary_in_safe_context() {
    run_test(
        r#"
pub unsafe fn foo() -> i32 {
    let mut x: i32 = 42;
    let mut p: *mut i32 = &mut x;
    let mut r: *mut i32 = &mut x;
    *p = 10;
    *r = 20;
    let mut q: *mut i32 = p;
    *q
}
"#,
        &["let mut q: &i32", ".as_ref()"],
        &[],
    );
}

/// OptRef q = OptRef p, with type cast. Both promoted but p is c_int, q is c_short.
/// Different-size numerics → same_size fails → non-bytemuck cast.
/// Conversion: opt_ref_from_opt_ref (pointer-cast else branch).
#[test]
fn test_ref_eq_ref_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    let mut q: *mut libc::c_short = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &["as *const i16", "let mut q: &i16", "let mut p: &mut i32"],
        &["bytemuck"],
    );
}

/// OptRef q = Slice p, with type cast. p uses .offset() → Slice.
/// q = p (cast, no array ops) → OptRef. Different-size numerics → non-bytemuck cast.
/// Conversion: opt_ref_from_slice (pointer-cast else branch).
#[test]
fn test_ref_eq_slice_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_short = p as *mut libc::c_short;
    return *q as libc::c_int;
}
"#,
        &["as *const _ as *const _", ".first()", "&mut [i32]"],
        &["bytemuck"],
    );
}

/// Slice q = Raw p, with type cast. p has overlapping borrow conflict → Raw.
/// q = p with cast, uses .offset() → Slice.
/// Conversion: slice_from_raw (need_cast branch).
#[test]
fn test_slice_eq_raw_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    let mut q: *mut libc::c_short = p as *mut libc::c_short;
    *q.offset(0 as isize) = 30 as libc::c_short;
    return *q.offset(0 as isize) as libc::c_int;
}
"#,
        &["from_raw_parts_mut", "as *mut _", "&mut [i16]"],
        &["bytemuck"],
    );
}

/// Slice q = Slice p, with type cast. Both use .offset() → both Slice.
/// p is a bytemuck-derivable struct Pair, q is c_int, so the reinterpreted
/// slice view can use bytemuck instead of an open-ended raw-parts fallback.
/// Conversion: slice_from_slice (pointer-cast else branch).
#[test]
fn test_slice_eq_slice_cast() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Pair {
    pub a: libc::c_int,
    pub b: libc::c_int,
}
impl Copy for Pair {}
impl Clone for Pair {
    fn clone(&self) -> Self { *self }
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [Pair; 10] = [Pair { a: 0, b: 0 }; 10];
    let mut p: *mut Pair = arr.as_mut_ptr();
    (*p.offset(0 as isize)).a = 10 as libc::c_int;
    (*p.offset(1 as isize)).a = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p as *mut libc::c_int;
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(1 as isize);
}
"#,
        &[
            "#[derive(bytemuck::Zeroable, bytemuck::Pod)]",
            "bytemuck::cast_slice_mut::<_, i32>",
            "&mut [i32]",
        ],
        &["from_raw_parts_mut", "1_000_000"],
    );
}

// ===== projected_expr tests: offset and cast projections on Slice base =====
// When the RHS is `p.offset(n)` or `(p as *mut T).offset(n)` and p is Slice,
// projected_expr transforms the projections before passing to the conversion
// function. Offset becomes `[(n) as usize..]`; non-usize cast calls
// slice_from_slice internally.

// --- Single offset ---

/// OptRef q = Slice p.offset(2): projected_expr transforms offset to
/// slice range `(p)[(2) as usize..]`, then opt_ref_from_slice → .first().
#[test]
fn test_ref_eq_slice_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize);
    return *q;
}
"#,
        &["as usize..]", ".first()", "Option<&i32>"],
        &["*mut"],
    );
}

/// Slice q = Slice p.offset(2): projected_expr transforms offset to
/// slice range, then slice_from_slice → &mut(...).
#[test]
fn test_slice_eq_slice_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize);
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &["as usize..]", "&mut [i32]"],
        &["*mut"],
    );
}

// --- Multiple offsets ---

/// OptRef q = Slice p.offset(2).offset(1): projected_expr chains two
/// offset projections into nested slice ranges.
#[test]
fn test_ref_eq_slice_multi_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize).offset(1 as isize);
    return *q;
}
"#,
        &[
            "(2 as isize) as usize..]",
            "(1 as isize) as usize..]",
            ".first()",
        ],
        &["*mut"],
    );
}

/// Slice q = Slice p.offset(2).offset(1): projected_expr chains two
/// offset projections, then slice_from_slice → &mut(...).
#[test]
fn test_slice_eq_slice_multi_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize).offset(1 as isize);
    *q.offset(0 as isize) = 30 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &[
            "(2 as isize) as usize..]",
            "(1 as isize) as usize..]",
            "&mut [i32]",
        ],
        &["*mut"],
    );
}

// ===== addr_of tests: RHS is `&mut x` (taking address of a local variable) =====
// The `addr_of` branch handles RHS expressions of the form `&mut x`.
// 3 PtrKind contexts (Raw, OptRef, Slice) × 2-3 sub-cases (need_cast, ty_updated).

// --- Raw context ---

/// addr_of with Raw context, no cast: overlapping borrows on x demote both
/// pointers to Raw. Output: `&raw mut (x)`.
#[test]
fn test_addr_of_raw() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    return *p;
}
"#,
        &["&raw mut"],
        &["Some(", "slice::from"],
    );
}

/// addr_of with Raw context, with cast: overlapping borrows + type cast.
/// Output: `&raw mut (x) as *mut i16`.
#[test]
fn test_addr_of_raw_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_short = &mut x as *mut libc::c_int as *mut libc::c_short;
    let mut r: *mut libc::c_short = &mut x as *mut libc::c_int as *mut libc::c_short;
    *p = 10 as libc::c_short;
    *r = 20 as libc::c_short;
    return *p as libc::c_int;
}
"#,
        &["&raw mut", "as *mut i16"],
        &["Some("],
    );
}

// --- OptRef context ---

/// addr_of with OptRef context, no cast: simple `&mut x` usage, no conflicts.
/// Output: `Some(&mut (x))`.
#[test]
fn test_addr_of_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["let mut p: &mut i32", "Some(&mut"],
        &["*mut", "bytemuck"],
    );
}

/// addr_of with OptRef context, bytemuck cast: same-size numerics (c_int vs c_uint).
/// p is read-only so m=false → `Some(bytemuck::cast_ref::<_, u32>(&(x)))`.
#[test]
fn test_addr_of_ref_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_uint = &mut x as *mut libc::c_int as *mut libc::c_uint;
    return *p as libc::c_int;
}
"#,
        &["bytemuck::cast_ref", "let mut p: &u32"],
        &["*mut"],
    );
}

/// addr_of with OptRef context, non-bytemuck cast: different-size numerics
/// (c_int vs c_short). p is read-only so m=false → `Some(&*(&raw const (x) as *const i16))`.
#[test]
fn test_addr_of_ref_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_short = &mut x as *mut libc::c_int as *mut libc::c_short;
    return *p as libc::c_int;
}
"#,
        &["&raw const", "as *const i16", "Some("],
        &["bytemuck"],
    );
}

// --- Slice context ---

/// addr_of with Slice context, no cast: `&mut x` with .offset() usage gives
/// p array_pointer status → Slice. Output: `std::slice::from_mut(&mut (x))`.
#[test]
fn test_addr_of_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p.offset(0 as isize) = 10 as libc::c_int;
    return *p.offset(0 as isize);
}
"#,
        &["slice::from_mut", "&mut [i32]"],
        &["*mut", "bytemuck"],
    );
}

/// addr_of with Slice context, bytemuck cast: same-size numerics (c_int vs c_uint)
/// with .offset() usage. Output: `std::slice::from_mut(bytemuck::cast_mut(&mut (x)))`.
#[test]
fn test_addr_of_slice_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_uint = &mut x as *mut libc::c_int as *mut libc::c_uint;
    *p.offset(0 as isize) = 10 as libc::c_uint;
    return *p.offset(0 as isize) as libc::c_int;
}
"#,
        &["bytemuck::cast_mut", "slice::from_mut", "&mut [u32]"],
        &["*mut"],
    );
}

/// addr_of with Slice context, non-bytemuck cast: different-size numerics
/// (c_int vs c_short) with .offset() usage.
/// Output: `std::slice::from_raw_parts_mut(&raw mut (x) as *mut _, 1_000_000)`.
#[test]
fn test_addr_of_slice_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_short = &mut x as *mut libc::c_int as *mut libc::c_short;
    *p.offset(0 as isize) = 10 as libc::c_short;
    return *p.offset(0 as isize) as libc::c_int;
}
"#,
        &["from_raw_parts_mut", "&raw mut", "&mut [i16]"],
        &["bytemuck"],
    );
}

#[test]
fn test_addr_of_fixed_array_slice_cast_uses_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_short = &mut arr as *mut [libc::c_int; 10] as *mut libc::c_short;
    *p.offset(0 as isize) = 10 as libc::c_short;
    *p.offset(1 as isize) = 20 as libc::c_short;
    return *p.offset(0 as isize) as libc::c_int;
}
"#,
        &["bytemuck::cast_slice_mut::<_, i16>", "&mut [i16]"],
        &["from_raw_parts_mut", "1_000_000", "&raw mut"],
    );
}

// --- Non-usize cast + offset ---

/// OptRef q = Slice (p as *mut c_uint).offset(2): projected_expr first
/// applies cast via slice_from_slice (bytemuck for same-size numerics),
/// then offset → `(bytemuck::cast_slice(p))[(2) as usize..]`.
#[test]
fn test_ref_eq_slice_cast_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_uint = (p as *mut libc::c_uint).offset(2 as isize);
    return *q as libc::c_int;
}
"#,
        &[
            "bytemuck::cast_slice",
            "as usize..]",
            ".first()",
            "Option<&u32>",
        ],
        &["*mut"],
    );
}

/// Slice q = Slice (p as *mut c_uint).offset(2): projected_expr first
/// applies cast via slice_from_slice (bytemuck), then offset →
/// `(bytemuck::cast_slice_mut(p))[(2) as usize..]`.
#[test]
fn test_slice_eq_slice_cast_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    let mut q: *mut libc::c_uint = (p as *mut libc::c_uint).offset(2 as isize);
    *q.offset(0 as isize) = 30 as libc::c_uint;
    return *q.offset(0 as isize) as libc::c_int;
}
"#,
        &["bytemuck::cast_slice_mut", "as usize..]", "&mut [u32]"],
        &["*mut"],
    );
}

// ===== visit_expr code path tests =====

/// Binary pointer comparison (ExprKind::Binary with comparison ops on pointer-typed operands).
/// Both sides are transformed as PtrKind::Raw — OptRef pointers get converted via
/// `map_or(null_mut, ...)` for the comparison.
#[test]
fn test_ptr_comparison() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut y: libc::c_int = 43 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut q: *mut libc::c_int = &mut y;
    *p = 10 as libc::c_int;
    *q = 20 as libc::c_int;
    if p == q { return 1 as libc::c_int; }
    return 0 as libc::c_int;
}
"#,
        &["let mut p: &mut i32", "as *mut i32 =="],
        &[],
    );
}

/// Function call with pointer argument — local function, sig_decs lookup succeeds.
/// bar's parameter is proven non-null and the call site unwraps p accordingly.
#[test]
fn test_ptr_call_arg() {
    run_test(
        r#"
use ::libc;
unsafe fn bar(p: *mut libc::c_int) -> libc::c_int { return *p; }
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    return bar(p);
}
"#,
        &["fn bar(p: &i32)", "bar((Some(&*(p))).unwrap())"],
        &[],
    );
}

/// `.is_null()` on OptRef pointer → `.is_none()`.
#[test]
fn test_is_null_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    if p.is_null() { return 0 as libc::c_int; }
    return *p;
}
"#,
        &["if false", "let mut p: &mut i32"],
        &["is_null", "is_none"],
    );
}

/// `.is_null()` on Slice pointer → `.is_empty()`.
#[test]
fn test_is_null_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p.offset(0 as isize) = 10 as libc::c_int;
    if p.is_null() { return 0 as libc::c_int; }
    return *p.offset(0 as isize);
}
"#,
        &["is_empty", "&mut [i32]"],
        &["is_null"],
    );
}

/// Return statement with raw pointer return type — p is internally OptRef
/// but the function returns `*mut c_int`, so the return coerces p to Raw.
#[test]
fn test_return_raw_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> *mut libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    return p;
}
"#,
        &["&raw mut"],
        &["Option<", "&mut ["],
    );
}

/// Tuple return with a pointer element: p is promoted to Option<&mut>,
/// and the return expression must coerce the tuple element back to raw.
#[test]
fn test_return_tuple_with_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> (libc::c_int, *mut libc::c_int) {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    return (0 as libc::c_int, p);
}
"#,
        &["let mut p: &mut i32", "(p) as *mut i32"],
        &[],
    );
}

#[test]
fn test_outparam_tuple_result_keeps_forced_raw_call_result_mutability() {
    run_test(
        r#"
extern "C" {
    fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
    fn snprintf(
        __s: *mut core::ffi::c_char,
        __maxlen: usize,
        __format: *const core::ffi::c_char,
        ...
    ) -> core::ffi::c_int;
    fn malloc(__size: usize) -> *mut core::ffi::c_void;
    fn free(__ptr: *mut core::ffi::c_void);
    fn strcmp(__s1: *const core::ffi::c_char, __s2: *const core::ffi::c_char)
        -> core::ffi::c_int;
}

pub unsafe fn create_result_string(
    mut op: *const core::ffi::c_char,
    mut val: core::ffi::c_int,
) -> *mut core::ffi::c_char {
    let mut str: *mut core::ffi::c_char = malloc(64usize) as *mut core::ffi::c_char;
    if str.is_null() {
        return 0 as *mut core::ffi::c_char;
    }
    snprintf(
        str,
        64usize,
        b"Operation: %s, Value: %d\0" as *const u8 as *const core::ffi::c_char,
        op,
        val,
    );
    return str;
}

pub unsafe fn multiply_with_log(
    mut a: core::ffi::c_int,
    mut b: core::ffi::c_int,
) -> (core::ffi::c_int, *mut i8) {
    let mut log_msg___v: *mut i8 = 0 as *mut _;
    log_msg___v =
        create_result_string(b"multiply\0" as *const u8 as *const core::ffi::c_char, a * b);
    if (log_msg___v).is_null() {
        return (0 as core::ffi::c_int, log_msg___v);
    }
    return (a * b, log_msg___v);
}

pub unsafe fn complexmode(
    mut value1: core::ffi::c_int,
    mut value2: core::ffi::c_int,
) -> core::ffi::c_int {
    let mut result: core::ffi::c_int = 0;
    let mut log_message: *mut core::ffi::c_char = 0 as *mut core::ffi::c_char;
    result = {
        let rv___t = multiply_with_log(value1, value2);
        *(&mut log_message) = rv___t.1;
        rv___t.0
    };
    if log_message.is_null()
        || strcmp(log_message, b"\0" as *const u8 as *const core::ffi::c_char) == 0
    {
        printf(b"Log message creation failed\n\0" as *const u8 as *const core::ffi::c_char);
    } else {
        printf(
            b"Mode 2: %s\n\0" as *const u8 as *const core::ffi::c_char,
            log_message,
        );
        free(log_message as *mut core::ffi::c_void);
    }
    result
}
"#,
        &[
            "let mut log_msg___v: *mut i8",
            "let mut log_message: *mut i8",
            "Some(&mut log_message).unwrap() = rv___t.1",
        ],
        &["let mut log_msg___v: *const i8", "let mut log_message: &"],
    );
}

/// Slice deref fallback: `*p` on a Slice variable without offset → `(p)[0]`.
/// When p is Slice but deref doesn't match the `&arr[start..]` pattern,
/// the else branch at line 296 produces `(*p)[0]`.
#[test]
fn test_deref_slice_no_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(1 as isize) = 10 as libc::c_int;
    *p = 20 as libc::c_int;
    return *p;
}
"#,
        &["[0]", "&mut [i32]"],
        &["*mut"],
    );
}

// ===== transform_ptr code path tests: null literal, if-else, block, cast_int =====

/// Null literal (`0 as *mut T`) assigned to OptRef pointer → `None`.
/// Exercises the `is_zero() + PtrCtx::Rhs(OptRef)` branch.
#[test]
fn test_null_ptr_opt_ref() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    p = 0 as *mut libc::c_int;
    return if p.is_null() { 0 as libc::c_int } else { 1 as libc::c_int };
}
"#,
        &["None", "Option<&mut i32>"],
        &["null_mut"],
    );
}

/// Null literal (`0 as *mut T`) assigned to Slice pointer → `&mut []`.
/// Exercises the `is_zero() + PtrCtx::Rhs(Slice)` branch.
#[test]
fn test_null_ptr_slice() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p.offset(0 as isize) = 10 as libc::c_int;
    p = 0 as *mut libc::c_int;
    return 0 as libc::c_int;
}
"#,
        &["&mut []", "&mut [i32]"],
        &["null_mut"],
    );
}

/// Null constructors assigned to SliceCursor pointers should use the matching
/// empty cursor type, not raw/null or a nonexistent cursor reference type.
#[test]
fn test_null_ptr_constructor_slice_cursor() {
    let config = Config::default();
    let (s, _) = rewrite_with_config(
        r#"
use ::libc;
pub unsafe extern "C" fn mut_cursor() -> libc::c_int {
    let mut arr: [libc::c_int; 4] = [0; 4];
    let mut p: *mut libc::c_int = arr.as_mut_ptr().offset(2);
    *p.offset(-1) = 10 as libc::c_int;
    p = std::ptr::null_mut();
    return 0 as libc::c_int;
}

pub unsafe extern "C" fn shared_cursor() -> libc::c_int {
    let arr: [libc::c_int; 4] = [1; 4];
    let mut p: *const libc::c_int = arr.as_ptr().offset(2);
    let v = *p.offset(-1);
    p = std::ptr::null();
    return v;
}
"#,
        &config,
    );

    assert!(
        s.contains("crate::slice_cursor::SliceCursorMut::empty()"),
        "Expected mutable null constructor to use SliceCursorMut::empty():\n{s}"
    );
    assert!(
        s.contains("crate::slice_cursor::SliceCursor::empty()"),
        "Expected shared null constructor to use SliceCursor::empty():\n{s}"
    );
    assert!(
        !s.contains("SliceCursorRef::empty()"),
        "Expected no nonexistent SliceCursorRef constructor:\n{s}"
    );
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
}

/// Null literal (`0 as *mut T`) assigned to Raw pointer → `std::ptr::null_mut()`.
/// Exercises the `is_zero() + PtrCtx::Rhs(Raw)` branch.
#[test]
fn test_null_ptr_raw() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    *r = 20 as libc::c_int;
    p = 0 as *mut libc::c_int;
    return *r;
}
"#,
        &["null_mut"],
        &["None"],
    );
}

/// Dereference of null literal: `*(0 as *mut T)`.
/// Exercises the `is_zero() + PtrCtx::Deref` branch, which returns `PtrKind::Raw(m)`
/// and leaves the expression unchanged. The result is a raw deref that passes through.
#[test]
fn test_deref_null() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = *(0 as *mut libc::c_int);
    return x;
}
"#,
        &["*(0"],
        &["Option<", "&mut ["],
    );
}

/// If-else (ternary) pointer expression: `p = if cond { &mut x } else { &mut y }`.
/// Exercises the `ExprKind::If` branch in `transform_ptr` — both branches
/// are recursively transformed.
#[test]
fn test_if_else_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut y: libc::c_int = 43 as libc::c_int;
    let mut cond: libc::c_int = 1 as libc::c_int;
    let mut p: *mut libc::c_int = if cond != 0 { &mut x } else { &mut y };
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["let mut p: &mut i32", "Some(&mut"],
        &["*mut"],
    );
}

/// Block-wrapped pointer expression: `p = { &mut x }`.
/// Exercises the `ExprKind::Block` branch in `transform_ptr` — the inner
/// expression is recursively transformed.
#[test]
fn test_block_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = { &mut x };
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["let mut p: &mut i32", "Some(&mut"],
        &["*mut"],
    );
}

/// Integer-to-pointer cast via usize bitwise op: `q = (p as usize | 0) as *mut c_int`.
/// Exercises the `cast_int` branch in `transform_ptr` — the Binary expression
/// prevents `unwrap_cast_and_paren` from stripping the usize cast, so `ptr_expr`
/// sees a Cast to usize and sets `cast_int = true`. q must be Raw (overlapping
/// borrow) to match `PtrCtx::Rhs(Raw)`. Uses `|` (not `+`) since `projected_expr`
/// only handles `BitAnd`/`BitOr` for `IntegerBinOp`.
#[test]
fn test_cast_int_ptr() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut y: libc::c_int = 43 as libc::c_int;
    let mut q: *mut libc::c_int = &mut y;
    let mut s: *mut libc::c_int = &mut y;
    *q = 1 as libc::c_int;
    *s = 2 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    *p = 10 as libc::c_int;
    q = (p as usize | 0 as usize) as *mut libc::c_int;
    return *q;
}
"#,
        &["as usize"],
        &[],
    );
}

// ===== as_ptr + Raw context tests (lines 549-565) =====

/// as_ptr + Raw, no cast: overlapping borrows from `.as_mut_ptr()` demote both
/// to Raw. Same types → `!need_cast`. Output: `(arr).as_mut_ptr()`.
#[test]
fn test_as_ptr_raw_no_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    let mut q: *mut libc::c_int = arr.as_mut_ptr();
    *p = 10 as libc::c_int;
    *q = 20 as libc::c_int;
    return *p;
}
"#,
        &["as_mut_ptr()"],
        &["Some(", "Option<"],
    );
}

/// as_ptr + Raw, with cast: overlapping borrows + type cast (c_int vs c_short).
/// Output: `(arr).as_mut_ptr() as *mut _`.
#[test]
fn test_as_ptr_raw_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_short = arr.as_mut_ptr() as *mut libc::c_short;
    let mut q: *mut libc::c_short = arr.as_mut_ptr() as *mut libc::c_short;
    *p = 10 as libc::c_short;
    *q = 20 as libc::c_short;
    return *p as libc::c_int;
}
"#,
        &["as_mut_ptr()) as *mut _"],
        &["Some(", "Option<"],
    );
}

// ===== as_ptr + OptRef context tests (lines 567-599) =====

/// as_ptr + OptRef, no cast: single borrow from `.as_mut_ptr()`, no overlap,
/// no offset -> promoted to OptRef. Same types. Output uses `first_mut`.
#[test]
fn test_as_ptr_ref_no_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["Option<&mut i32>", ".first_mut()"],
        &["bytemuck"],
    );
}

/// as_ptr + OptRef, bytemuck cast: single borrow, c_int vs c_uint (same-size numerics).
/// Output casts the safe array view and then uses `first_mut`.
#[test]
fn test_as_ptr_ref_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_uint = arr.as_mut_ptr() as *mut libc::c_uint;
    *p = 10 as libc::c_uint;
    return *p as libc::c_int;
}
"#,
        &[
            "Option<&mut u32>",
            "bytemuck::cast_slice_mut",
            ".first_mut()",
        ],
        &["from_raw_parts_mut"],
    );
}

/// as_ptr + OptRef, non-bytemuck cast: single borrow, c_int (4B) vs c_short (2B)
/// → different size → else branch. Output: `Some(&mut *(arr).as_mut_ptr() as *mut i16)`.
#[test]
fn test_as_ptr_ref_ptr_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_short = arr.as_mut_ptr() as *mut libc::c_short;
    *p = 10 as libc::c_short;
    return *p as libc::c_int;
}
"#,
        &["Option<&mut i16>", ".as_mut()"],
        &["bytemuck"],
    );
}

// ===== as_ptr + Slice + need_cast tests (lines 616-637) =====

/// as_ptr + Slice, bytemuck cast: same-size numerics (c_int ↔ c_uint) with offset.
/// Output: `bytemuck::cast_slice_mut(&mut (arr))`.
#[test]
fn test_as_ptr_slice_bytemuck() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [libc::c_int; 10] = [0; 10];
    let mut p: *mut libc::c_uint = arr.as_mut_ptr() as *mut libc::c_uint;
    *p.offset(0 as isize) = 10 as libc::c_uint;
    *p.offset(1 as isize) = 20 as libc::c_uint;
    return *p.offset(0 as isize) as libc::c_int;
}
"#,
        &["bytemuck::cast_slice_mut", "&mut [u32]"],
        &["from_raw_parts_mut"],
    );
}

#[test]
fn test_as_ptr_call_arg_uses_safe_slice_view() {
    run_test(
        r#"
extern crate alloc;

pub unsafe fn consume(out: *mut i32, input: *const i32) {
    *out.offset(0) = *input.offset(0);
}

pub unsafe fn foo() -> i32 {
    let mut out = vec![0; 4];
    let input = [1, 2, 3, 4];
    consume(out.as_mut_ptr(), input.as_ptr());
    out[0]
}
"#,
        &["consume(&mut (out), &(input));"],
        &["from_raw_parts", "from_raw_parts_mut"],
    );
}

#[test]
fn test_as_ptr_from_vec_ref_uses_safe_slice_view() {
    run_test(
        r#"
pub unsafe fn foo() -> i32 {
    let mut alloca_allocations: Vec<Vec<u8>> = Vec::new();
    let mut data: *mut i32 = 0 as *mut i32;
    alloca_allocations.push(::std::vec::from_elem(
        0u8,
        10usize * ::core::mem::size_of::<i32>(),
    ));
    data = alloca_allocations.last_mut().unwrap().as_mut_ptr() as *mut i32;
    *data.offset(0) = 7;
    *data.offset(1) = 9;
    *data.offset(0)
}
"#,
        &[
            "let mut data: &mut [i32]",
            "bytemuck::cast_slice_mut",
            "alloca_allocations.last_mut().unwrap()",
        ],
        &["from_raw_parts_mut"],
    );
}

#[test]
fn test_as_ptr_deref_offset_uses_safe_slice_index() {
    run_test(
        r#"
extern crate alloc;

pub unsafe fn foo(idx: usize) -> i32 {
    let mut out = vec![0; 4];
    *out.as_mut_ptr().offset(idx as isize) = 7;
    out[idx]
}
"#,
        &["as usize..]))[0]"],
        &[".as_mut()", "from_raw_parts_mut"],
    );
}

#[test]
fn test_addr_of_scalar_byte_slice_uses_bytemuck_bytes_of() {
    run_test(
        r#"
pub type uint64_t = u64;

pub unsafe fn hash(mut key: uint64_t) -> u64 {
    let mut bytes: *const u8 = &mut key as *mut uint64_t as *mut u8;
    let mut hash = 0u64;
    let mut i = 0usize;
    while i < ::core::mem::size_of::<uint64_t>() {
        hash += *bytes.offset(i as isize) as u64;
        i += 1;
    }
    hash
}
"#,
        &["let mut bytes: &[u8] = bytemuck::bytes_of(&(key));"],
        &["from_raw_parts", "&raw const"],
    );
}

#[test]
fn test_addr_of_no_padding_struct_byte_slice_uses_bytemuck_bytes_of() {
    let code = r#"
#[repr(C)]
pub struct House {
    pub floors: i32,
    pub bedrooms: i32,
    pub bathrooms: f64,
}
impl Copy for House {}
impl Clone for House {
    fn clone(&self) -> Self { *self }
}

pub unsafe fn hash(mut house: House) -> u64 {
    let mut bytes: *const u8 = &mut house as *mut House as *mut u8;
    let mut hash = 0u64;
    let mut i = 0usize;
    while i < ::core::mem::size_of::<House>() {
        hash += *bytes.offset(i as isize) as u64;
        i += 1;
    }
    hash
}
"#;
    let (s, bytemuck) = rewrite_with_config(code, &Config::default());
    assert_eq!(bytemuck, BytemuckDependency::Derive);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    for include in [
        "#[derive(bytemuck::NoUninit)]",
        "let mut bytes: &[u8] = bytemuck::bytes_of(&(house));",
    ] {
        assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
    }
    for exclude in ["from_raw_parts", "&raw const"] {
        assert!(
            !s.contains(exclude),
            "Expected not to find `{exclude}` in:\n{s}",
        );
    }
}

#[test]
fn test_addr_of_padded_struct_byte_slice_stays_raw_parts() {
    let code = r#"
#[repr(C)]
pub struct Padded {
    pub tag: u8,
    pub value: u32,
}
impl Copy for Padded {}
impl Clone for Padded {
    fn clone(&self) -> Self { *self }
}

pub unsafe fn hash(mut value: Padded) -> u64 {
    let mut bytes: *const u8 = &mut value as *mut Padded as *mut u8;
    let mut hash = 0u64;
    let mut i = 0usize;
    while i < ::core::mem::size_of::<Padded>() {
        hash += *bytes.offset(i as isize) as u64;
        i += 1;
    }
    hash
}
"#;
    let (s, bytemuck) = rewrite_with_config(code, &Config::default());
    assert_eq!(bytemuck, BytemuckDependency::None);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(
        s.contains("from_raw_parts"),
        "Expected raw fallback in:\n{s}"
    );
    for exclude in ["bytemuck::bytes_of", "derive(bytemuck"] {
        assert!(
            !s.contains(exclude),
            "Expected not to find `{exclude}` in:\n{s}",
        );
    }
}

#[test]
fn test_array_field_ptr_arithmetic_uses_slice_suffix() {
    run_test(
        r#"
#[repr(C)]
pub struct Block {
    pub next: *mut Block,
    pub storage: [i8; 8],
}

#[repr(C)]
pub struct Arena {
    pub storage: *mut Block,
    pub remaining: usize,
}

pub unsafe fn alloc_from_block(a: *mut Arena, len: usize) -> i8 {
    let mut p: *mut i8 = (*(*a).storage).storage.as_mut_ptr().offset(
        ((*a).remaining as isize) - (len as isize),
    );
    *p = 1;
    *p.offset(1) = 2;
    *p.offset(1)
}
"#,
        &["let mut p: &mut [i8]", "&mut (&mut ((*a.storage).storage))"],
        &["from_raw_parts_mut", ".as_mut_ptr().offset"],
    );
}

#[test]
fn test_array_field_zero_offset_slice_arg_uses_slice_suffix() {
    run_test(
        r#"
#[repr(C)]
pub struct Info {
    pub addr: [u32; 8],
}

pub unsafe fn consume(addr: *mut u32) {
    *addr.offset(0) = 1;
    *addr.offset(1) = 2;
}

pub unsafe fn foo() {
    let mut info = Info { addr: [0; 8] };
    consume(info.addr.as_mut_ptr().offset(0));
}
"#,
        &["consume(&mut (info.addr)["],
        &["from_raw_parts_mut", ".addr.as_mut_ptr().offset"],
    );
}

#[test]
fn test_array_field_unsigned_offset_slice_arg_uses_slice_suffix() {
    run_test(
        r#"
#[repr(C)]
pub struct Info {
    pub addr: [u8; 16],
    pub pos: u32,
}

pub unsafe fn consume(addr: *mut u8) {
    *addr.offset(0) = 1;
    *addr.offset(1) = 2;
}

pub unsafe fn foo(info: *mut Info) {
    let pos = (*info).pos % 8;
    consume((*info).addr.as_mut_ptr().offset(pos as isize));
}
"#,
        &["consume(&mut ((*info).addr)[(pos as isize) as usize..]);"],
        &["from_raw_parts_mut", ".addr.as_mut_ptr().offset"],
    );
}

#[test]
fn test_array_field_c_int_arithmetic_offset_slice_arg_uses_slice_suffix() {
    run_test(
        r#"
#[repr(C)]
pub struct Md5 {
    pub buffer: [u8; 72],
}

pub unsafe fn unpack(d: *const u8) -> u32 {
    return *d.offset(0) as u32
        | ((*d.offset(1) as u32) << 8);
}

pub unsafe fn transform(m: *mut Md5) -> u32 {
    return unpack(
        &mut *(*m)
            .buffer
            .as_mut_ptr()
            .offset((10 as core::ffi::c_int * 4 as core::ffi::c_int) as isize),
    );
}
"#,
        &[
            "pub unsafe fn unpack(d: &[u8])",
            "unpack(&",
            "buffer)[",
            "10 as core::ffi::c_int",
            "* 4 as core::ffi::c_int",
            "as usize..])",
        ],
        &["from_raw_parts", ".buffer.as_mut_ptr().offset"],
    );
}

#[test]
fn test_raw_root_array_field_as_mut_ptr_slice_arg_uses_direct_borrow() {
    run_test(
        r#"
#[repr(C)]
pub struct Info {
    pub data: [i8; 4],
}

static mut SLOT: *mut Info = 0 as *mut Info;

pub unsafe fn consume(data: *const i8) -> i32 {
    *data.offset(0) as i32
}

pub unsafe fn foo() -> i32 {
    let info = SLOT;
    consume((*info).data.as_ptr())
}
"#,
        &["consume(&(&((*info).data))[..])"],
        &["from_raw_parts", ".data.as_ptr()"],
    );
}

#[test]
fn test_array_field_const_offset_raw_arg_uses_slice_suffix_ptr() {
    run_test(
        r#"
extern "C" {
    fn memset(dst: *mut core::ffi::c_void, c: i32, n: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct Ctx {
    pub ctr: [u8; 16],
}

pub unsafe fn foo() {
    let mut ctx = Ctx { ctr: [0; 16] };
    memset(ctx.ctr.as_mut_ptr().offset(12) as *mut _, 0, 4);
}
"#,
        &["&mut (ctx.ctr)[(12) as usize..]).as_mut_ptr()"],
        &[".ctr.as_mut_ptr().offset"],
    );
}

#[test]
fn test_array_field_unsigned_offset_raw_arg_uses_slice_suffix_ptr() {
    run_test(
        r#"
extern "C" {
    fn memcpy(dst: *mut core::ffi::c_void, src: *const core::ffi::c_void, n: usize)
        -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct Ctx {
    pub buffer: [u8; 16],
    pub buffer_pos: u64,
}

pub unsafe fn foo(n: usize) {
    let mut out = [0u8; 16];
    let mut ctx = Ctx {
        buffer: [0; 16],
        buffer_pos: 4,
    };
    memcpy(
        out.as_mut_ptr() as *mut _,
        ctx.buffer.as_mut_ptr().offset(ctx.buffer_pos as isize) as *const _,
        n,
    );
}
"#,
        &["&(ctx.buffer)[(ctx.buffer_pos as isize) as usize..]).as_ptr()"],
        &[".buffer.as_mut_ptr().offset"],
    );
}

/// as_ptr + Slice, bytemuck-derivable cast: struct array cast to c_int pointer.
#[test]
fn test_as_ptr_slice_reinterpretation_uses_bytemuck() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Pair {
    pub a: libc::c_int,
    pub b: libc::c_int,
}
impl Copy for Pair {}
impl Clone for Pair {
    fn clone(&self) -> Self { *self }
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut arr: [Pair; 10] = [Pair { a: 0, b: 0 }; 10];
    let mut p: *mut libc::c_int = arr.as_mut_ptr() as *mut libc::c_int;
    *p.offset(0 as isize) = 10 as libc::c_int;
    *p.offset(1 as isize) = 20 as libc::c_int;
    return *p.offset(0 as isize);
}
"#,
        &[
            "#[derive(bytemuck::Zeroable, bytemuck::Pod)]",
            "bytemuck::cast_slice_mut::<_, i32>",
            "&mut [i32]",
        ],
        &["from_raw_parts", "1_000_000"],
    );
}

#[test]
fn test_indexed_slice_reinterpretation_avoids_bytemuck_cast() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Header {
    pub a: libc::c_int,
    pub b: libc::c_int,
}
impl Copy for Header {}
impl Clone for Header {
    fn clone(&self) -> Self { *self }
}
#[repr(C)]
pub struct Chunk {
    pub a: libc::c_int,
    pub b: libc::c_int,
}
impl Copy for Chunk {}
impl Clone for Chunk {
    fn clone(&self) -> Self { *self }
}
pub unsafe extern "C" fn foo(data: *const Header) -> libc::c_int {
    let header: *const Header = data;
    let chunk: *const Chunk = header.offset(1 as isize) as *const Chunk;
    return (*chunk).a;
}
"#,
        &["first().map", "_x as *const _ as *const _"],
        &["bytemuck::cast_slice::<_, crate::Chunk>"],
    );
}

// ===== ByteStr tests (lines 700-732) =====

/// ByteStr + OptRef, u8: byte string literal used as `*const u8`, single deref
/// (no offset) → OptRef. `lhs_inner_ty == u8` → `.first()`.
#[test]
fn test_bytestr_opt_ref_u8() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut s: *const libc::c_uchar = b"hello\x00" as *const u8;
    return *s as libc::c_int;
}
"#,
        &[".first()"],
        &["*const", "bytemuck"],
    );
}

/// ByteStr + OptRef, numeric cast: byte string cast to `*const c_int`.
/// `lhs_inner_ty = i32` (numeric, not u8) → `bytemuck::cast_slice(...).first()`.
#[test]
fn test_bytestr_opt_ref_numeric() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut s: *const libc::c_int = b"hell" as *const u8 as *const libc::c_int;
    return *s;
}
"#,
        &["bytemuck::cast_slice", ".first()"],
        &["*const"],
    );
}

/// ByteStr + Slice, u8: byte string with offset → Slice. `lhs_inner_ty == u8`
/// → expression cloned.
#[test]
fn test_bytestr_slice_u8() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut s: *const libc::c_uchar = b"hello\x00" as *const u8;
    let a: libc::c_uchar = *s.offset(0 as isize);
    let b: libc::c_uchar = *s.offset(1 as isize);
    return (a as libc::c_int) + (b as libc::c_int);
}
"#,
        &["&[u8]"],
        &["*const", "bytemuck"],
    );
}

/// ByteStr + Slice, numeric cast: byte string cast to `*const c_int` with offset.
/// `lhs_inner_ty = i32` (not u8) → `bytemuck::cast_slice(...)`.
#[test]
fn test_bytestr_slice_numeric() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut s: *const libc::c_int = b"hellworl" as *const u8 as *const libc::c_int;
    let a: libc::c_int = *s.offset(0 as isize);
    let b: libc::c_int = *s.offset(1 as isize);
    return a + b;
}
"#,
        &["bytemuck::cast_slice"],
        &["*const"],
    );
}

// ===== Fallthrough tests (lines 734-755): struct field pointer access =====

/// Fallthrough + OptRef: struct field `s.data` is a `*mut c_int` → `PtrExprBaseKind::Other`.
/// Single borrow → promoted to OptRef.
#[test]
fn test_field_ptr_opt_ref() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Foo {
    pub data: *mut libc::c_int,
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut s: Foo = Foo { data: &mut x };
    let mut p: *mut libc::c_int = s.data;
    *p = 10 as libc::c_int;
    return *p;
}
"#,
        &["Option<&mut i32>"],
        &["*mut i32"],
    );
}

/// Fallthrough + Slice: struct field `s.data` with `.offset()` → Slice.
#[test]
fn test_field_ptr_slice() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Foo {
    pub data: *mut libc::c_int,
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut s: Foo = Foo { data: &mut x };
    let mut p: *mut libc::c_int = s.data;
    *p.offset(0 as isize) = 10 as libc::c_int;
    return *p.offset(0 as isize);
}
"#,
        &["&mut [i32]"],
        &["*mut i32"],
    );
}

// ===== slice_from_raw Branch A tests: method call (offset/as_mut_ptr/as_ptr) =====

/// slice_from_raw Branch A1 (no cast): `q = p.offset(2)` where p is Raw, q is Slice.
/// `method_call_name(p.offset(2))` → "offset" → skip null check, no cast needed.
#[test]
fn test_sfr_method_call_no_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 1 as libc::c_int;
    *r = 2 as libc::c_int;
    let mut q: *mut libc::c_int = p.offset(2 as isize);
    *q.offset(0 as isize) = 10 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &["from_raw_parts_mut", "p.offset"],
        &["is_null", "let _x"],
    );
}

/// slice_from_raw Branch A2 (with cast): `q = p.offset(2) as *mut c_short` where p is Raw.
/// `unwrap_cast_and_paren` strips cast → "offset" → Branch A, `need_cast=true` → `as *mut _`.
#[test]
fn test_sfr_method_call_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut r: *mut libc::c_int = &mut x;
    *p = 1 as libc::c_int;
    *r = 2 as libc::c_int;
    let mut q: *mut libc::c_short = p.offset(2 as isize) as *mut libc::c_short;
    *q.offset(0 as isize) = 10 as libc::c_short;
    return *q.offset(0 as isize) as libc::c_int;
}
"#,
        &["from_raw_parts_mut", "as *mut _"],
        &["is_null", "let _x"],
    );
}

// ===== slice_from_raw Branch C tests: side effects =====
// A function call returning a raw pointer has side effects (Call is not whitelisted)
// and reaches the fallthrough path (PtrExprBaseKind::Other at line 1153).
// transform_ptr does NOT recurse into Call expressions, so slice_from_raw sees the
// full call expression and hits Branch C.

/// slice_from_raw Branch C1 (side effects, no cast): `q = identity(p)` where
/// identity is an extern function returning a raw pointer. `has_side_effects(Call)` → true,
/// same types → C1. Uses extern to avoid parameter transformation.
#[test]
fn test_sfr_side_effects_no_cast() {
    run_test(
        r#"
use ::libc;
extern "C" { fn identity(p: *mut libc::c_int) -> *mut libc::c_int; }
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut q: *mut libc::c_int = identity(&mut x);
    *q.offset(0 as isize) = 10 as libc::c_int;
    return *q.offset(0 as isize);
}
"#,
        &["let _x", "from_raw_parts_mut"],
        &["as *mut _"],
    );
}

/// slice_from_raw Branch C2 (side effects, with cast): `q = identity(p) as *mut c_short`.
/// `has_side_effects(Call)` → true, different types → need_cast → C2. Uses extern to
/// avoid parameter transformation.
#[test]
fn test_sfr_side_effects_cast() {
    run_test(
        r#"
use ::libc;
extern "C" { fn identity(p: *mut libc::c_int) -> *mut libc::c_int; }
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut q: *mut libc::c_short = identity(&mut x) as *mut libc::c_short;
    *q.offset(0 as isize) = 10 as libc::c_short;
    return *q.offset(0 as isize) as libc::c_int;
}
"#,
        &["let _x", "from_raw_parts_mut", "as *mut _"],
        &[],
    );
}

// ===== addr_of + pointer arithmetic tests =====

/// addr_of with cast + offset: `*(&mut x as *mut c_int as *mut c_char).offset(1) = 0`.
/// The addr_of block builds a slice via `std::slice::from_mut`, applies Cast via
/// bytemuck::cast_slice_mut, then Offset as range indexing. visit_expr converts
/// `*&mut slice[n..]` → `slice[n]`.
#[test]
fn test_addr_of_cast_offset() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() {
    let mut x: libc::c_int = 0 as libc::c_int;
    *(&mut x as *mut libc::c_int as *mut libc::c_char)
        .offset(1 as libc::c_int as isize) = 0 as libc::c_char;
}

"#,
        &["bytemuck::cast_slice_mut", "slice::from_mut", "as usize..]"],
        &["*mut", "as *mut"],
    );
}

#[test]
fn test_param_byte_cast_offset_rewrites_to_slice_cursor() {
    run_test(
        r#"
#[repr(C)]
pub struct Info {
    pub leaf_addr: [u32; 8],
}

pub unsafe extern "C" fn set_type(addr: *mut u32, offset: i32, value: u32) {
    *(addr as *mut u8).offset(offset as isize) = value as u8;
}

pub unsafe extern "C" fn caller(info: *mut Info, offset: i32, value: u32) {
    let leaf_addr: *mut u32 = (*info).leaf_addr.as_mut_ptr();
    set_type(leaf_addr as *mut u32, offset, value);
}
"#,
        &[
            "crate::slice_cursor::SliceCursorMut<'_, u32>",
            "SliceCursorMut::from_raw_parts_mut((addr).as_ptr()",
            "as *mut u8, 1_000_000",
            "set_type((leaf_addr).as_deref_mut(), offset, value);",
        ],
        &[
            "pub unsafe extern \"C\" fn set_type(mut addr: *mut u32",
            "*(addr as *mut u8).offset",
            "bytemuck::cast_slice_mut",
        ],
    );
}

#[test]
fn test_raw_local_noop_cast_call_does_not_demote_cursor_callee() {
    run_test(
        r#"
#[repr(C)]
pub struct Info {
    pub leaf_addr: [u32; 8],
}

extern "C" {
    fn consume(ptr: *mut core::ffi::c_void);
}

pub unsafe extern "C" fn set_type(addr: *mut u32, offset: i32, value: u32) {
    *(addr as *mut u8).offset(offset as isize) = value as u8;
}

pub unsafe extern "C" fn caller(v_info: *mut core::ffi::c_void, offset: i32, value: u32) {
    let info: *mut Info = v_info as *mut Info;
    consume(info as *mut core::ffi::c_void);
    let leaf_addr: *mut u32 = (*info).leaf_addr.as_mut_ptr();
    set_type(leaf_addr as *mut u32, offset, value);
}
"#,
        &[
            "crate::slice_cursor::SliceCursorMut<'_, u32>",
            "SliceCursorMut::from_raw_parts_mut((addr).as_ptr()",
            "as *mut u8, 1_000_000",
            "set_type(if (leaf_addr).is_null()",
            "SliceCursorMut::from_raw_parts_mut((leaf_addr),",
        ],
        &[
            "pub unsafe extern \"C\" fn set_type(mut addr: *mut u32",
            "*(addr as *mut u8).offset",
            "bytemuck::cast_slice_mut",
        ],
    );
}

#[test]
fn test_c_exposed_abi_struct_without_interface_wrapper_stays_raw() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("parse_number".to_string());
    run_test_with_config(
        r#"
#[repr(C)]
pub struct parse_buffer {
    pub content: *const u8,
    pub length: usize,
    pub offset: usize,
    pub depth: usize,
}

#[repr(C)]
pub struct cJSON {
    pub valueint: i32,
}

#[no_mangle]
pub unsafe extern "C" fn parse_number(item: *mut cJSON, input_buffer: *mut parse_buffer) -> i32 {
    if input_buffer.is_null() || (*input_buffer).content.is_null() {
        return 0;
    }
    let b = *(*input_buffer).content.offset((*input_buffer).offset as isize);
    (*item).valueint = b as i32;
    (*input_buffer).offset += 1;
    return 1;
}
"#,
        &config,
        &["pub content: *const u8"],
        &["pub struct parse_buffer<", "pub content: &'"],
    );
}

#[test]
fn test_c_exposed_thin_struct_opt_ref_field_can_promote() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("smallestValue".to_string());
    run_test_with_config(
        r#"
#[repr(C)]
pub struct ListNode {
    pub value: i32,
    pub next: *mut ListNode,
}

#[no_mangle]
pub unsafe extern "C" fn smallestValue(mut head: *mut ListNode) -> i32 {
    if head.is_null() {
        return -1;
    }
    let mut smallest = (*head).value;
    while !(*head).next.is_null() {
        head = (*head).next;
        if (*head).value < smallest {
            smallest = (*head).value;
        }
    }
    smallest
}
"#,
        &config,
        &[
            "pub struct ListNode<'a>",
            "pub next: Option<&'a mut ListNode<'a>>",
            "head = ((*head.unwrap()).next).as_deref();",
        ],
        &[
            "pub next: *mut ListNode",
            "head = unsafe { ((*head.unwrap()).next).as_ref() };",
        ],
    );
}

#[test]
fn test_c_exposed_strduped_struct_field_stays_raw() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("parse".to_string());
    run_test_with_config(
        r#"
extern "C" {
    fn strdup(s: *const i8) -> *mut i8;
}

#[repr(C)]
pub struct OsData {
    pub arch: *mut i8,
}

#[no_mangle]
pub unsafe extern "C" fn parse(osd: *mut OsData, s: *const i8) -> i32 {
    (*osd).arch = strdup(s);
    if ((*osd).arch).is_null() {
        return 0;
    }
    *(*osd).arch as i32
}
"#,
        &config,
        &["pub arch: *mut i8", "osd.arch = strdup((s).as_ptr());"],
        &[
            "pub struct OsData<'",
            "pub arch: Option<&",
            "strdup(s)).as_mut()",
        ],
    );
}

#[test]
fn test_c_exposed_slice_element_abi_struct_fields_stay_raw() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("driver".to_string());
    run_test_with_config(
        r#"
#[repr(C)]
pub struct Record {
    pub name: *const i8,
    pub value: i32,
}

#[no_mangle]
pub unsafe extern "C" fn driver(records: *const Record) -> i32 {
    if records.is_null() {
        return 0;
    }
    let first = records.offset(0);
    if (*first).name.is_null() {
        return (*first).value;
    }
    return *(*first).name as i32 + (*first).value;
}
"#,
        &config,
        &["pub name: *const i8"],
        &["pub struct Record<", "pub name: Option<&", "pub name: &'"],
    );
}

#[test]
fn test_c_exposed_wrapped_function_does_not_freeze_non_slice_struct_param() {
    let mut config = Config::default();
    config
        .c_exposed_fns
        .insert("SPX_wots_gen_leafx1".to_string());
    run_test_with_config(
        r#"
#[repr(C)]
pub struct Info {
    pub steps: *const u32,
    pub leaf_addr: [u32; 8],
}

#[no_mangle]
pub unsafe extern "C" fn SPX_wots_gen_leafx1(dest: *mut u8, info: *mut Info, len: usize) {
    let mut i = 0usize;
    while i < len {
        *dest.offset(i as isize) = *(*info).steps.offset(i as isize) as u8;
        i += 1;
    }
    *dest.offset(0) = (*info).leaf_addr[0] as u8;
}
"#,
        &config,
        &["pub struct Info<", "pub steps: &'"],
        &["pub steps: *const u32"],
    );
}

#[test]
fn test_c_exposed_wrapped_function_keeps_cursor_struct_field_raw() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("read_bits".to_string());
    run_test_with_config(
        r#"
#[repr(C)]
pub struct Bs {
    pub buf: *const u8,
    pub pos: i32,
    pub limit: i32,
}

#[repr(C)]
pub struct Out {
    pub value: i32,
}

#[no_mangle]
pub unsafe extern "C" fn read_bits(bs: *mut Bs, out: *mut Out, hdr: *const u8) -> i32 {
    if bs.is_null() || out.is_null() || hdr.is_null() {
        return 0;
    }
    let mut p: *const u8 = ((*bs).buf).offset(((*bs).pos >> 3) as isize);
    (*bs).pos += 8;
    if (*bs).pos > (*bs).limit {
        return 0;
    }
    (*out).value = *hdr.offset(1) as i32;
    let first = *p as i32;
    p = p.offset(1);
    first + (*p as i32)
}
"#,
        &config,
        &["pub struct Bs {", "pub buf: *const u8"],
        &[
            "pub struct Bs<'",
            "pub buf: crate::slice_cursor::SliceCursor",
        ],
    );
}

#[test]
fn test_interproc_negative_offset_propagation() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(
    mut end: *mut libc::c_int,
    mut count: libc::c_int,
) -> libc::c_int {
    let mut sum: libc::c_int = 0 as libc::c_int;
    let mut ptr: *mut libc::c_int = end;
    let mut i: libc::c_int = 0 as libc::c_int;
    while i < count {
        sum += *ptr;
        ptr = ptr.offset(-1);
        i += 1;
    }
    return sum;
}
pub unsafe extern "C" fn bar() -> libc::c_int {
    let mut arr: [libc::c_int; 5] = [1, 2, 3, 4, 5];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    let mut last_element: *mut libc::c_int = p.offset(4 as isize);
    return foo(last_element, 5 as libc::c_int);
}
"#,
        &[
            "let mut last_element: crate::slice_cursor::SliceCursor",
            "foo(last_element, 5 as libc::c_int)",
        ],
        &["let mut last_element: &[i32]"],
    );
}

#[test]
fn test_raw_local_caller_keeps_negative_cursor_input_raw() {
    run_test(
        r#"
extern "C" {
    fn foreign() -> *const u8;
}

pub unsafe fn read_before(p: *const u8) -> u8 {
    *p.offset(-1)
}

pub unsafe fn drive() -> u8 {
    let p = foreign();
    read_before(p)
}
"#,
        &["pub unsafe fn read_before", "p: *const u8"],
        &[
            "fn read_before(p: crate::slice_cursor::SliceCursor",
            "fn read_before(mut p: crate::slice_cursor::SliceCursor",
        ],
    );
}

#[test]
fn test_array_pointer_caller_keeps_negative_cursor_input_cursor() {
    run_test(
        r#"
pub unsafe fn read_before(p: *const u8) -> u8 {
    *p.offset(-1)
}

pub unsafe fn drive() -> u8 {
    let buf = [1u8, 2, 3, 4];
    read_before(buf.as_ptr().offset(1))
}
"#,
        &[
            "pub unsafe fn read_before",
            "p: crate::slice_cursor::SliceCursor",
        ],
        &[
            "fn read_before(p: *const u8)",
            "fn read_before(mut p: *const u8)",
        ],
    );
}

#[test]
fn test_mut_cursor_multi_offset_deref_uses_combined_index() {
    run_test(
        r#"
pub unsafe fn write_offset(p: *mut i32, a: isize, b: isize) {
    *p.offset(a).offset(b) = 1;
}
"#,
        &["(p)[((a) as isize).wrapping_add((b) as isize)] = 1"],
        &["(p).as_deref_mut().offset_by"],
    );
}

#[test]
fn test_mut_cursor_multi_offset_call_reborrows_once() {
    run_test(
        r#"
pub unsafe fn recurse(items: *mut i32, a: isize, b: isize) {
    if b == 0 {
        return;
    }
    recurse(items.offset(a).offset(b), a, b - 1);
    *items = b as i32;
}
"#,
        &["as_deref_mut", ")).offset_by((b) as isize)"],
        &["as_deref_mut().offset_by((b) as isize)"],
    );
}

#[test]
fn test_opt_boxed_slice_offset_cursor_uses_slice_view_base() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn consume(mut end: *mut i32, mut count: i32) -> i32 {
    let mut sum: i32 = 0;
    while count > 0 {
        sum += *end;
        end = end.offset(-1);
        count -= 1;
    }
    sum
}

pub unsafe fn foo() -> i32 {
    let mut array_size: i32 = 5;
    let mut data_array: *mut i32 =
        malloc(array_size as usize * std::mem::size_of::<i32>()) as *mut i32;
    if data_array.is_null() {
        return -1;
    }
    let mut i: i32 = 0;
    while i < array_size {
        *data_array.offset(i as isize) = i + 1;
        i += 1;
    }
    let mut last_element: *mut i32 =
        data_array.offset((array_size as isize) + -(1 as isize));
    let sum = consume(last_element, array_size);
    free(data_array as *mut core::ffi::c_void);
    sum
}
"#,
        &[
            "let mut data_array: Box<[i32]>",
            "SliceCursor::with_pos(&(data_array)[..]",
            "if false { return -1; }",
        ],
        &["SliceCursor::with_pos(&data_array"],
    );
}

#[test]
fn test_owned_malloc_array_negative_offset_borrows_boxed_slice_as_cursor() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn foo() -> i32 {
    let mut data_array: *mut i32 = malloc(5 * std::mem::size_of::<i32>()) as *mut i32;
    if data_array.is_null() {
        return -1;
    }
    let mut i: i32 = 0;
    while i < 5 {
        *data_array.offset(i as isize) = i + 1;
        i += 1;
    }
    let mut tail: *mut i32 = data_array.offset(4 as isize);
    *tail.offset(-2 as isize)
}
"#,
        &[
            "let mut data_array: Box<[i32]>",
            "SliceCursor::with_pos(&(data_array)[..]",
            "if false { return -1; }",
        ],
        &[
            "let mut data_array: *mut i32",
            "let mut tail: *mut i32",
            "SliceCursor::with_pos(&data_array",
        ],
    );
}

#[test]
fn test_inline_offset_call_arg_borrows_boxed_slice_as_cursor() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn consume(mut end: *mut i32, mut count: i32) -> i32 {
    let mut sum: i32 = 0;
    while count > 0 {
        sum += *end;
        end = end.offset(-1);
        count -= 1;
    }
    sum
}

pub unsafe fn foo() -> i32 {
    let mut array_size: i32 = 5;
    let mut data_array: *mut i32 =
        malloc(array_size as usize * std::mem::size_of::<i32>()) as *mut i32;
    if data_array.is_null() {
        return -1;
    }
    let mut i: i32 = 0;
    while i < array_size {
        *data_array.offset(i as isize) = i + 1;
        i += 1;
    }
    let sum = consume(data_array.offset((array_size as isize) + -(1 as isize)), array_size);
    free(data_array as *mut core::ffi::c_void);
    sum
}
"#,
        &[
            "let mut data_array: Box<[i32]>",
            "consume(crate::slice_cursor::SliceCursor::with_pos(&(data_array)[..]",
            "if false { return -1; }",
        ],
        &[
            "let mut last_element:",
            "SliceCursor::with_pos(&data_array",
            "consume(data_array.offset(",
        ],
    );
}

#[test]
fn test_shared_array_field_offset_stays_shared() {
    run_test(
        r#"
extern "C" {
    fn memcpy(dst: *mut core::ffi::c_void, src: *const core::ffi::c_void, n: usize)
        -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct buffer_t {
    pub data: [u8; 256],
    pub length: usize,
}

pub unsafe fn copy_tail(
    mut src: *const buffer_t,
    mut split_pos: usize,
    mut dst: *mut buffer_t,
) {
    memcpy(
        ((*dst).data).as_mut_ptr() as *mut core::ffi::c_void,
        (*src).data.as_ptr().offset(split_pos as isize) as *const core::ffi::c_void,
        1,
    );
}
"#,
        &["&((*src).data)[("],
        &["&mut ((*src).data)"],
    );
}

#[test]
fn test_replace_local_borrows_does_not_run_struct_array_field_pre_stage() {
    let code = r#"
#[repr(C)]
pub struct Elem {
    pub x: i32,
}
impl Copy for Elem {}
impl Clone for Elem {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
pub struct Group {
    pub a: Elem,
    pub b: Elem,
    pub c: Elem,
    pub tag: i32,
}

pub unsafe fn foo() -> i32 {
    let mut s: Group = Group {
        a: Elem { x: 1 },
        b: Elem { x: 2 },
        c: Elem { x: 3 },
        tag: 4,
    };
    let mut p: *mut Elem = &raw mut s.a;
    let mut q: *mut Elem = p as *mut Elem;
    (*q.offset(1)).x = 7;
    s.b.x
}
"#;
    let (s, _) = rewrite_with_config(code, &Config::default());
    assert!(!s.contains("pub a: [Elem; 3]"), "{s}");
    assert!(s.contains("pub b: Elem"), "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
}

#[test]
fn test_array_local_rewriter_rewrites_simple_non_null_derived_local() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = p.offset(3);
    *p = 1;
    *q = 3;
    *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut q_idx: isize = (3) as isize"), "{s}");
    assert!(!s.contains("let mut q: *mut i32"), "{s}");
    assert!(s.contains("*((p).offset(q_idx) as *mut i32) = 3"), "{s}");
    assert!(s.contains("*((p).offset(q_idx) as *mut i32)"), "{s}");
}

#[test]
fn test_array_local_rewriter_uses_option_index_for_nullable_local() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32, mut k: isize) -> i32 {
    let mut q: *mut i32 = std::ptr::null_mut();
    if q.is_null() {
        q = p.offset(k);
    }
    *q = 7;
    q = q.offset(1);
    *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut q_idx: Option<isize> = None"), "{s}");
    assert!(s.contains("if q_idx.is_none()"), "{s}");
    assert!(s.contains("q_idx = Some(k)"), "{s}");
    assert!(
        s.contains("*((p).offset(q_idx.unwrap()) as *mut i32) = 7"),
        "{s}"
    );
    assert!(!s.contains("let mut q: *mut i32"), "{s}");
    assert!(!s.contains("q.is_null()"), "{s}");
}

#[test]
fn test_array_local_rewriter_preserves_nullable_pointer_value_use() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32, mut take: bool) -> *mut i32 {
    let mut q: *mut i32 = std::ptr::null_mut();
    if take {
        q = p.add(2);
    }
    q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut q_idx: Option<isize> = None"), "{s}");
    assert!(s.contains("q_idx = Some((2) as isize)"), "{s}");
    assert!(
        s.contains("q_idx.map_or(std::ptr::null_mut() as *mut i32"),
        "{s}"
    );
    assert!(s.contains("|idx| ((p).offset(idx)) as *mut i32"), "{s}");
    assert!(!s.contains("let mut q: *mut i32"), "{s}");
}

#[test]
fn test_array_local_rewriter_lowers_nullable_projected_deref_through_base() {
    // a nullable index-backed member that is projected-derefed (`*prev.offset(x)`)
    // lowers directly through the base pointer instead of the map_or bridge.
    let code = r#"
pub unsafe fn foo(mut raw: *mut u8, mut take: bool, mut x: isize) -> u8 {
    let mut prev: *mut u8 = std::ptr::null_mut();
    if take {
        prev = raw;
    }
    raw = raw.offset(1);
    *prev.offset(x)
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut prev_idx: Option<isize> = None"), "{s}");
    assert!(
        s.contains("*((raw).offset((prev_idx.unwrap()) + (x)) as *mut u8)"),
        "projected deref lowered through base: {s}"
    );
    assert!(
        !s.contains("prev_idx.map_or"),
        "no map_or bridge for the deref: {s}"
    );
}

#[test]
fn test_projected_nullable_deref_no_raw_bridge_after_promotion() {
    // reduced from B02_organic/unfilter_lib: `raw` is a moving base cursor that
    // borrow-promotes to a slice cursor; `prev` is a nullable member projected-
    // derefed. the promoted base must not leave a `map_or(...).as_mut_ptr().offset`
    // bridge.
    let code = r#"
pub unsafe extern "C" fn unfilter_like(mut h: i32, mut len: i32, mut raw: *mut u8) {
    let mut prev: *mut u8 = std::ptr::null_mut();
    let mut x: i32 = 0;
    let mut y: i32 = 1;
    while y < h {
        raw = raw.offset(1);
        if !prev.is_null() {
            x = 0;
            while x < len {
                *raw.offset(x as isize) = (*raw.offset(x as isize) as i32
                    + *prev.offset(x as isize) as i32) as u8;
                x += 1;
            }
        }
        prev = raw;
        raw = raw.offset(len as isize);
        y += 1;
    }
}
"#;
    let config = Config::default();
    let (s, _) = rewrite_struct_arrays_then_array_local_then_pointer(code, &config);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(
        !s.contains(".as_mut_ptr()).offset("),
        "no raw bridge for the projected nullable deref: {s}"
    );
    assert!(!s.contains("prev_idx.map_or"), "{s}");
}

#[test]
fn test_array_local_rewriter_leaves_cast_projected_deref_unchanged() {
    // a receiver cast in the projection keeps the bare member, which the existing
    // map_or pointer-value fallback lowers; the projected-deref branch bails.
    let code = r#"
pub unsafe fn foo(mut raw: *mut u8, mut take: bool, mut x: isize) -> u16 {
    let mut prev: *mut u8 = std::ptr::null_mut();
    if take {
        prev = raw;
    }
    raw = raw.offset(1);
    *(prev as *mut u16).offset(x)
}
"#;
    let (s, _) = rewrite_array_local_provenance_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(
        s.contains("prev_idx.map_or"),
        "cast receiver bails to map_or: {s}"
    );
}

#[test]
fn test_array_local_rewriter_leaves_non_nullable_projected_deref_to_existing_lowering() {
    // a non-nullable index-backed member keeps its existing lowering; the
    // nullable-gated projected-deref branch does not fire.
    let code = r#"
pub unsafe fn foo(mut raw: *mut i32, mut x: isize) -> i32 {
    let mut p: *mut i32 = raw.offset(1);
    raw = raw.offset(2);
    let v = *p.offset(x);
    let _ = raw;
    v
}
"#;
    let (s, _) = rewrite_array_local_provenance_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // `p` is index-backed but non-nullable, so it keeps the existing double-offset
    // lowering (deferred to item 10) rather than the nullable projected-base form.
    assert!(s.contains("let mut p_idx: isize"), "{s}");
    assert!(!s.contains("p_idx.unwrap()"), "{s}");
    assert!(
        s.contains("*((raw).offset(p_idx) as *mut i32).offset(x)"),
        "{s}"
    );
}

#[test]
fn test_array_local_rewriter_keeps_direct_base_write_cursor_index_only() {
    let code = r#"
pub unsafe fn wcscat_like(mut dst: *mut i32, mut num_elem: usize, mut src: *const i32) -> i32 {
    let mut ptr: *mut i32 = dst.offset(0);
    if dst.is_null() || num_elem == 0 {
        return 22;
    }
    while ptr < dst.offset(num_elem as isize) && *ptr != 0 {
        ptr = ptr.offset(1);
    }
    while ptr < dst.offset(num_elem as isize) {
        let fresh = *src;
        src = src.offset(1);
        *ptr = fresh;
        let seen = *ptr;
        ptr = ptr.offset(1);
        if seen == 0 {
            return 0;
        }
    }
    *dst = 0;
    34
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut ptr_idx: isize"), "{s}");
    assert!(!s.contains("let mut ptr: *mut i32"), "{s}");
    assert!(!s.contains("*ptr"), "{s}");
}

#[test]
fn test_array_local_rewriter_keeps_cast_cursor_index_only() {
    let code = r#"
fn parse_bool(c: i8) -> bool {
    c == 89 || c == 121
}

pub unsafe fn validate_sequence(mut sequence: *mut i8, mut len: usize) -> i32 {
    if len == 0 {
        return 0;
    }
    let mut bools: *mut bool = sequence as *mut bool;
    let mut i: usize = 0;
    while i < len {
        let val: bool = parse_bool(*sequence.offset(i as isize));
        *bools.offset(i as isize) = val;
        i = i.wrapping_add(1);
    }
    if !*bools.offset(0) {
        return -10;
    }
    if len > 1 && (*bools.offset(len.wrapping_sub(1) as isize)) as i32 != 0 {
        return -11;
    }
    0
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut bools_idx: isize"), "{s}");
    assert!(!s.contains("let mut bools: *mut bool"), "{s}");
    assert!(!s.contains("*bools.offset"), "{s}");
}

#[test]
fn test_array_local_map_or_closure_body_rewrites_slice_base_offset() {
    let code = r#"
pub unsafe fn foo(mut raw: *mut i32, mut take: bool, mut k: isize) -> *mut i32 {
    let mut prev: *mut i32 = std::ptr::null_mut();
    if take {
        prev = raw.offset(k);
    }
    *raw.offset(0) = 3;
    prev
}
"#;
    let (s, _) = rewrite_struct_arrays_then_array_local_then_pointer(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("mut raw: &mut [i32]"), "{s}");
    let compact = s.split_whitespace().collect::<String>();
    assert!(
        compact.contains(
            "prev_idx.map_or(std::ptr::null_mut()as*muti32,|idx|((raw)[(idx)asusize..]).as_mut_ptr())"
        ),
        "{s}"
    );
    assert!(!s.contains("(raw).offset(idx as isize)"), "{s}");
}

#[test]
fn test_raw_map_or_with_reference_closure_body_is_not_rewritten() {
    let code = r#"
pub unsafe fn foo(mut opt: Option<&mut i32>) -> *mut i32 {
    opt.as_deref_mut().map_or(std::ptr::null_mut::<i32>(), |_x| _x)
}
"#;
    let (s, _) = rewrite_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("map_or"), "{s}");
}

#[test]
fn test_non_option_map_or_with_raw_closure_body_is_not_rewritten() {
    let code = r#"
struct Wrapper;

impl Wrapper {
    unsafe fn map_or<F>(self, fallback: *mut i32, f: F) -> *mut i32
    where
        F: FnOnce(usize) -> *mut i32,
    {
        let result = f(0);
        if result.is_null() {
            fallback
        } else {
            result
        }
    }
}

pub unsafe fn foo(wrapper: Wrapper) -> *mut i32 {
    let addr = 0usize;
    wrapper.map_or(std::ptr::null_mut::<i32>(), |idx| (addr as *mut i32).offset(idx as isize))
}
"#;
    let (s, _) = rewrite_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("wrapper.map_or"), "{s}");
    assert!(s.contains("(addr as *mut i32).offset(idx as isize)"), "{s}");
}

#[test]
fn test_array_local_rewriter_skips_assignment_with_planned_local_in_rhs() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = std::ptr::null_mut();
    q = p.offset(if q.is_null() { 0 } else { 1 });
    *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut q: *mut i32"), "{s}");
    assert!(s.contains("q = p.offset(if q.is_null()"), "{s}");
}

#[test]
fn test_array_local_rewriter_does_not_treat_local_null_mut_as_null_literal() {
    let code = r#"
pub unsafe fn null_mut() -> *mut i32 {
    0 as *mut i32
}

pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = null_mut();
    q = p.add(1);
    *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut q: *mut i32 = null_mut()"), "{s}");
}

#[test]
fn test_array_local_rewriter_rewrites_self_relative_assignment() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = p.offset(1);
    *p = 1;
    q = q.offset(2);
    *q = 9;
    *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut q_idx: isize = (1) as isize"), "{s}");
    assert!(s.contains("q_idx ="), "{s}");
    assert!(s.contains("(q_idx) + ((2) as isize)"), "{s}");
    assert!(!s.contains("let mut q: *mut i32"), "{s}");
    assert!(s.contains("*((p).offset(q_idx) as *mut i32) = 9"), "{s}");
    assert!(!s.contains("q = q.offset"), "{s}");
}

#[test]
fn test_array_local_rewriter_parenthesizes_compound_relative_offset() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32, n: isize, mask: isize) -> i32 {
    let mut q: *mut i32 = p.offset(1);
    *p = 1;
    q = q.offset(n & mask);
    *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("q_idx = (q_idx) + (n & mask)"), "{s}");
    assert!(!s.contains("q_idx = q_idx + n & mask"), "{s}");
}

#[test]
fn test_array_local_rewriter_skips_address_taken_derived_local() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32, out: *mut *mut i32) {
    let mut q: *mut i32 = p.offset(3);
    let _addr: *mut *mut i32 = &raw mut q;
    *p = 0;
    *q = 1;
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    assert!(s.contains("let mut q: *mut i32 = p.offset(3)"), "{s}");
    assert!(s.contains("&raw mut q"), "{s}");
}

#[test]
fn test_array_local_rewriter_skips_unsupported_assignment_source() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32, r: *mut i32) {
    let mut q: *mut i32 = p.offset(3);
    *p = 0;
    q = r;
    *q = 1;
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    assert!(s.contains("let mut q: *mut i32 = p.offset(3)"), "{s}");
    assert!(s.contains("q = r"), "{s}");
}

#[test]
fn test_array_local_rewriter_tracks_index_when_base_is_reassigned() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = p.offset(1);
    p = p.offset(1);
    *q + *p
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut p_idx: isize = 0isize"), "{s}");
    assert!(s.contains("let mut q_idx: isize"), "{s}");
    assert!(s.contains("(p_idx) + ((1) as isize)"), "{s}");
    assert!(s.contains("p_idx = (p_idx) + ((1) as isize)"), "{s}");
    assert!(s.contains("let mut q: *mut i32"), "{s}");
    assert!(s.contains("*q + *((p).offset(p_idx) as *mut i32)"), "{s}");
    assert!(!s.contains("p = p.offset(1)"), "{s}");
}

#[test]
fn test_array_local_rewriter_preserves_member_before_base_cursor_move() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32, n: isize) -> i32 {
    let mut prev: *mut i32 = p;
    p = p.offset(n);
    *prev + *p
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut p_idx: isize = 0isize"), "{s}");
    assert!(s.contains("let mut prev_idx: isize = p_idx"), "{s}");
    assert!(s.contains("p_idx = (p_idx) + (n)"), "{s}");
    assert!(s.contains("let mut prev: *mut i32"), "{s}");
    assert!(
        s.contains("*prev + *((p).offset(p_idx) as *mut i32)"),
        "{s}"
    );
    assert!(!s.contains("p = p.offset(n)"), "{s}");
}

#[test]
fn test_pointer_pipeline_runs_array_local_rewriter_before_pointer_rewriter() {
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = p.offset(3);
    *p = 1;
    *q = 3;
    *q
}
"#;
    let (s, _) = rewrite_struct_arrays_then_array_local_then_pointer(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("q_idx"), "{s}");
    assert!(!s.contains("let mut q: *mut i32"), "{s}");
    assert!(s.contains("(&mut ((p)[(q_idx) as usize..]))[0] = 3"), "{s}");
}

#[test]
fn test_array_local_rewriter_uses_slice_base_pointer_after_struct_arrays() {
    let code = r#"
pub unsafe fn foo(p: &[i32], n: isize) -> i32 {
    let mut q: *mut i32 = p.as_ptr().offset(n) as *mut i32;
    if q > p.as_ptr() as *mut i32 {
        *q
    } else {
        0
    }
}
"#;
    let (s, array_changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(array_changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("q_idx"), "{s}");
    assert!(s.contains("(p).as_ptr().offset"), "{s}");
    assert!(!s.contains("p.offset"), "{s}");
}

#[test]
fn test_array_local_rewriter_rewrites_wrapped_array_field_pointer_initializers() {
    let code = r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct ResultArray {
    pub data: [Item; 8],
    pub count: i32,
}

pub unsafe fn weighted(mut arr: *mut ResultArray, mut i: isize) -> i32 {
    let mut current: *mut Item =
        &mut *((*arr).data).as_mut_ptr().offset(i) as *mut Item;
    let mut base: *mut Item =
        &mut *((*arr).data).as_mut_ptr().offset(0) as *mut Item;
    let cmp: i32 = if current > base { 1 } else { 0 };
    let weight: isize = current.offset_from(base);
    (*current).value + weight as i32 + cmp
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(
        changed,
        "expected wrapped pointer initializers to be rewritten:\n{s}"
    );
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut current_idx: isize = i"), "{s}");
    assert!(s.contains("let mut base_idx: isize = (0) as isize"), "{s}");
    assert!(s.contains("if current_idx > base_idx"), "{s}");
    assert!(s.contains(".data).as_ptr().offset(current_idx)"), "{s}");
    assert!(!s.contains("let mut current: *mut Item"), "{s}");
    assert!(!s.contains("let mut base: *mut Item"), "{s}");
}

#[test]
fn test_array_local_rewriter_materializes_read_only_field_base_local() {
    let code = r#"
#[repr(C)]
pub struct Bucket {
    pub hash: [usize; 8],
    pub index: [isize; 8],
}

#[repr(C)]
pub struct Table {
    pub storage: *mut Bucket,
    pub len: usize,
}

pub unsafe fn sum_hashes(mut table: *mut Table) -> usize {
    let mut total: usize = 0;
    let mut i: usize = 0;
    while i < (*table).len {
        let mut ob: *mut Bucket = (*table).storage.offset(i as isize);
        let mut j: usize = 0;
        while j < 8 {
            if (*ob).index[j] >= 0 {
                total = total.wrapping_add((*ob).hash[j]);
            }
            j += 1;
        }
        i += 1;
    }
    total
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "expected materialized read-only rewrite:\n{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("ob_idx"), "{s}");
    assert!(
        s.contains("let ob: *mut Bucket")
            || s.contains("let mut ob: *mut Bucket")
            || s.contains("let ob: *mut crate::Bucket")
            || s.contains("let mut ob: *mut crate::Bucket"),
        "expected ob to stay materialized as a raw pointer before pointer rewriting:\n{s}"
    );
    assert!(
        s.contains("(*ob).index[j as usize]") || s.contains("(*ob).index[j]"),
        "{s}"
    );
    assert!(
        s.contains("(*ob).hash[j as usize]") || s.contains("(*ob).hash[j]"),
        "{s}"
    );
    let storage_offset_uses = s.matches("storage).offset(ob_idx)").count();
    assert!(
        storage_offset_uses <= 1,
        "expected at most one storage offset to materialize ob, got {storage_offset_uses}:\n{s}"
    );
}

#[test]
fn test_struct_array_field_run_from_field_rooted_offset() {
    let code = r#"
#[repr(C)]
pub struct Elem {
    pub x: i32,
}
impl Copy for Elem {}
impl Clone for Elem {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
pub struct Group {
    pub a: Elem,
    pub b: Elem,
    pub c: Elem,
    pub tag: i32,
}

pub unsafe fn foo() -> i32 {
    let mut s: Group = Group {
        a: Elem { x: 1 },
        b: Elem { x: 2 },
        c: Elem { x: 3 },
        tag: 4,
    };
    let mut p: *mut Elem = &raw mut s.a;
    let mut q: *mut Elem = p as *mut Elem;
    (*q.offset(1)).x = 7;
    s.b.x
}
"#;
    let (s, bytemuck) = rewrite_struct_arrays_then_pointer(code, &Config::default());
    assert_eq!(bytemuck, BytemuckDependency::None);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    for include in [
        "pub a: [Elem; 3]",
        "a: [Elem { x: 1 }, Elem { x: 2 }, Elem { x: 3 }]",
        "s.a[1].x",
    ] {
        assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
    }
    for exclude in ["pub b: Elem", "s.b.x"] {
        assert!(
            !s.contains(exclude),
            "Expected not to find `{exclude}` in:\n{s}",
        );
    }
}

#[test]
fn test_struct_array_rejects_offset_with_different_pointee_type() {
    let code = r#"
#[repr(C)]
pub struct Group {
    pub a: i32,
    pub b: i32,
    pub c: i32,
}

pub unsafe fn foo(s: *mut Group) {
    let p: *mut i32 = &raw mut (*s).a;
    let q: *mut i64 = p as *mut i64;
    let _r = q.offset(1);
}
"#;
    let (s, changed) = rewrite_struct_arrays_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    assert!(s.contains("pub a: i32"), "{s}");
    assert!(s.contains("pub b: i32"), "{s}");
    assert!(s.contains("pub c: i32"), "{s}");
    assert!(!s.contains("pub a: [i32; 3]"), "{s}");
}

#[test]
fn test_struct_array_rejects_offset_with_same_size_different_pointee_type() {
    let code = r#"
#[repr(C)]
pub struct Pair {
    pub key: i32,
    pub value: i32,
}

#[repr(C)]
pub struct Header {
    pub length: usize,
    pub capacity: usize,
    pub payload: *mut core::ffi::c_void,
}

pub unsafe fn foo(items: *mut Pair) -> usize {
    let header = items.offset(-1) as *mut Header;
    (*header).length + (*header).capacity
}
"#;
    let (s, changed) = rewrite_struct_arrays_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    assert!(s.contains("pub length: usize"), "{s}");
    assert!(s.contains("pub capacity: usize"), "{s}");
    assert!(!s.contains("pub length: [usize; 2]"), "{s}");
}

#[test]
fn test_struct_array_rejects_nested_array_element_type() {
    let code = r#"
#[repr(C)]
#[derive(Copy, Clone)]
pub struct c2v {
    pub x: f32,
    pub y: f32,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct c2Poly {
    pub count: i32,
    pub verts: [c2v; 8],
    pub norms: [c2v; 8],
}

pub unsafe fn foo(poly: *mut c2Poly) {
    let p: *mut [c2v; 8] = &raw mut (*poly).verts;
    let _q = p.offset(1);
}
"#;
    let (s, changed) = rewrite_struct_arrays_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    assert!(s.contains("pub verts: [c2v; 8]"), "{s}");
    assert!(s.contains("pub norms: [c2v; 8]"), "{s}");
    assert!(!s.contains("pub verts: [[c2v; 8]; 2]"), "{s}");
}

#[test]
fn test_struct_array_rejects_whole_struct_byte_inspection() {
    let code = r#"
#[repr(C)]
#[derive(Copy, Clone)]
pub struct house_t {
    pub floors: i32,
    pub bedrooms: i32,
    pub bathrooms: f64,
}

extern "C" {
    fn print_hex(p: *mut core::ffi::c_uchar, n: core::ffi::c_int);
}

pub unsafe fn foo() {
    let mut house = house_t {
        floors: 2,
        bedrooms: 3,
        bathrooms: 1.5,
    };
    print_hex(
        &mut house as *mut house_t as *mut core::ffi::c_uchar,
        ::core::mem::size_of::<house_t>() as core::ffi::c_int,
    );
}
"#;
    let (s, changed) = rewrite_struct_arrays_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    assert!(s.contains("pub floors: i32"), "{s}");
    assert!(s.contains("pub bedrooms: i32"), "{s}");
    assert!(!s.contains("pub floors: [i32; 2]"), "{s}");
}

#[test]
fn test_struct_array_rejects_partial_literal_group() {
    let code = r#"
#[repr(C)]
pub struct Group {
    pub a: i32,
    pub b: i32,
    pub c: i32,
}

pub unsafe fn foo(s: *mut Group) {
    let _partial = Group { a: 1, ..*s };
    let p: *mut i32 = &raw mut (*s).a;
    let _q = p.offset(1);
}
"#;
    let (s, changed) = rewrite_struct_arrays_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    assert!(s.contains("pub a: i32"), "{s}");
    assert!(s.contains("pub b: i32"), "{s}");
    assert!(s.contains("pub c: i32"), "{s}");
}

#[test]
fn test_struct_array_rejects_offset_of_escape() {
    let code = r#"
#[repr(C)]
pub struct Group {
    pub a: i32,
    pub b: i32,
    pub c: i32,
}

pub unsafe fn foo(s: *mut Group) -> usize {
    let p: *mut i32 = &raw mut (*s).a;
    let _q = p.offset(1);
    ::core::mem::offset_of!(Group, b)
}
"#;
    let (s, changed) = rewrite_struct_arrays_with_config(code, &Config::default());
    assert!(!changed, "{s}");
    assert!(s.contains("pub a: i32"), "{s}");
    assert!(s.contains("pub b: i32"), "{s}");
    assert!(s.contains("pub c: i32"), "{s}");
    assert!(!s.contains("pub a: [i32; 3]"), "{s}");
}

#[test]
fn test_cursor_mut_to_ref_preserves_pos() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(
    mut end: *const libc::c_int,
    mut count: libc::c_int,
) -> libc::c_int {
    let mut sum: libc::c_int = 0 as libc::c_int;
    while count > 0 {
        sum += *end;
        end = end.offset(-1);
        count -= 1;
    }
    return sum;
}
pub unsafe extern "C" fn bar() -> libc::c_int {
    let mut arr: [libc::c_int; 6] = [1, 2, 3, 4, 5, 6];
    let mut p: *mut libc::c_int = arr.as_mut_ptr();
    *p = 9 as libc::c_int;
    p = p.offset(1 as isize);
    p = p.offset(-1 as isize);
    let mut q: *const libc::c_int = p.offset(4 as isize) as *const libc::c_int;
    return foo(q, 1 as libc::c_int);
}
"#,
        &["SliceCursor::new((p).as_slice())", ".offset_by((4 as"],
        &["}).as_deref()"],
    );
}

/// Fallthrough + Raw: overlapping borrows from struct field `s.data` → both demoted to Raw.
#[test]
fn test_field_ptr_raw() {
    run_test(
        r#"
use ::libc;
#[repr(C)]
pub struct Foo {
    pub data: *mut libc::c_int,
}
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 42 as libc::c_int;
    let mut s: Foo = Foo { data: &mut x };
    let mut p: *mut libc::c_int = s.data;
    let mut q: *mut libc::c_int = s.data;
    *p = 10 as libc::c_int;
    *q = 20 as libc::c_int;
    return *p;
}
"#,
        &["s.data"],
        &["Option<", "&mut ["],
    );
}

/// Raw pointer mutability cast: `p` is *mut (writes through it), `q` is *const
/// (only compared). The comparison `p == q` requires matching types, so a cast
/// is inserted.
#[test]
fn test_raw_ptr_mutability_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    let mut x: libc::c_int = 0 as libc::c_int;
    let mut p: *mut libc::c_int = &mut x;
    let mut q: *mut libc::c_int = &mut x;
    *p = 1 as libc::c_int;
    return (p == q) as libc::c_int;
}
"#,
        &["*mut", "*const"],
        &[],
    );
}

/// Return type mutability: function returns a pointer that is never written through,
/// so the return type should become *const.
#[test]
fn test_return_type_mutability() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(mut x: *mut libc::c_int) -> *mut libc::c_int {
    return x;
}
"#,
        &[
            "pub unsafe extern \"C\" fn foo<'a>(mut x: &'a mut i32)",
            "-> &'a mut i32",
        ],
        &["-> *mut libc::c_int", "*const"],
    );
}

/// Call-site cast: callee's return type mutability changes and the caller
/// needs a cast to match.
#[test]
fn test_call_site_return_type_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo(mut x: *mut libc::c_int) -> *mut libc::c_int {
    return x;
}
pub unsafe extern "C" fn bar() {
    let mut x: libc::c_int = 0 as libc::c_int;
    let mut p: *mut libc::c_int = 0 as *mut libc::c_int;
    let mut q: *mut *mut libc::c_int = &mut p;
    *q = foo(&mut x);
}
"#,
        &[
            "pub unsafe extern \"C\" fn foo<'a>(mut x: &'a mut i32)",
            "-> &'a mut i32",
            "*q = (foo((Some(&mut x)).unwrap())) as *mut i32;",
        ],
        &[
            "pub unsafe extern \"C\" fn foo(mut x: *mut libc::c_int)",
            "-> *mut libc::c_int",
        ],
    );
}

mod ownership_analysis {
    use std::{
        fs,
        path::{Path, PathBuf},
    };

    use points_to::andersen;
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_hir::{ItemKind, OwnerNode, def_id::DefId};
    use rustc_middle::{mir::Local, ty::TyCtxt};
    use rustc_span::def_id::LocalDefId;

    use crate::{
        analyses::{
            output_params::compute_output_params,
            ownership::{
                AnalysisKind, CrateCtxt, Ownership, Param,
                ssa::{AnalysisResults, consume::Consume},
                whole_program::WholeProgramAnalysis,
            },
            type_qualifier::foster::mutability::mutability_analysis,
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

    fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }

        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn compute_param_aliases(
        tcx: TyCtxt<'_>,
    ) -> FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>> {
        let arena = typed_arena::Arena::new();
        let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
        let config = andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: FxHashSet::default(),
        };
        let pre = andersen::pre_analyze(&config, &tss, tcx);
        let points_to = andersen::analyze(&config, &pre, &tss, tcx);

        let mut param_aliases = FxHashMap::default();
        for def_id in tcx.hir_body_owners() {
            let Some(calls) = pre.call_args.get(&def_id) else {
                continue;
            };
            let mut aliases: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
            let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
            for call_args in calls {
                for i in 0..body.arg_count {
                    for j in 0..i {
                        let Some(arg_i) = call_args[i] else { continue };
                        let Some(arg_j) = call_args[j] else { continue };
                        let mut sol_i = points_to[arg_i].clone();
                        sol_i.intersect(&points_to[arg_j]);
                        if !sol_i.is_empty() {
                            let i = Local::from_usize(i + 1);
                            let j = Local::from_usize(j + 1);
                            aliases.entry(i).or_default().insert(j);
                            aliases.entry(j).or_default().insert(i);
                        }
                    }
                }
            }
            if !aliases.is_empty() {
                param_aliases.insert(def_id, aliases);
            }
        }

        param_aliases
    }

    // `pub(super)` so the BB-parity-own harness (sibling `borrow_ownership_coherence`
    // module) can reuse the exact production-ownership pipeline as its baseline oracle.
    pub(super) fn analyze_program<'tcx>(
        program: &RustProgram<'tcx>,
    ) -> crate::analyses::ownership::whole_program::WholeProgramResults<'tcx> {
        let mutability_result = mutability_analysis(program);
        let aliases: FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>> =
            FxHashMap::default();
        let output_params = compute_output_params(program, &mutability_result, &aliases);
        let crate_ctxt = CrateCtxt::new(program);
        <WholeProgramAnalysis as AnalysisKind>::analyze(crate_ctxt, &output_params)
            .expect("ownership analysis should succeed")
    }

    fn find_function(program: &RustProgram<'_>, name: &str) -> DefId {
        program
            .functions
            .iter()
            .map(|did| did.to_def_id())
            .find(|&did| {
                let path = program.tcx.def_path_str(did);
                path.rsplit("::").next() == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    fn collect_guarded_rust_files(path: &Path, files: &mut Vec<PathBuf>) {
        if path.is_dir() {
            for entry in fs::read_dir(path).unwrap_or_else(|err| {
                panic!("failed to read guarded path `{}`: {err}", path.display())
            }) {
                let entry = entry.unwrap_or_else(|err| {
                    panic!("failed to iterate guarded path `{}`: {err}", path.display())
                });
                collect_guarded_rust_files(&entry.path(), files);
            }
            return;
        }

        if path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path.to_path_buf());
        }
    }

    fn forbidden_mir_source_bytes() -> Vec<u8> {
        [b"optimized".as_slice(), b"_mir".as_slice(), b"(".as_slice()].concat()
    }

    #[test]
    fn mir_source_regression_guard_rejects_legacy_callsites() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let guarded_paths = [
            root.join("analyses/output_params"),
            root.join("analyses/ownership"),
            root.join("tests.rs"),
        ];
        let needle = forbidden_mir_source_bytes();
        let mut files = Vec::new();
        for path in &guarded_paths {
            collect_guarded_rust_files(path, &mut files);
        }
        files.sort();

        let offenders = files
            .into_iter()
            .filter(|path| {
                let bytes = fs::read(path).unwrap_or_else(|err| {
                    panic!("failed to read guarded file `{}`: {err}", path.display())
                });
                bytes
                    .windows(needle.len())
                    .any(|window| window == needle.as_slice())
            })
            .map(|path| {
                path.strip_prefix(env!("CARGO_MANIFEST_DIR"))
                    .unwrap_or(path.as_path())
                    .display()
                    .to_string()
            })
            .collect::<Vec<_>>();

        assert!(
            offenders.is_empty(),
            "legacy MIR source token found in guarded files:\n{}",
            offenders.join("\n")
        );
    }

    #[test]
    fn overlapping_call_args_form_alias_cluster() {
        run_compiler(
            r#"
pub unsafe fn keep_alias_raw(a: *mut i32, b: *mut i32) -> *mut i32 {
    let _ = b;
    a
}

pub unsafe fn foo() -> *mut i32 {
    let mut x = 7i32;
    let p: *mut i32 = &mut x;
    keep_alias_raw(p, p)
}
"#,
            |tcx| {
                let aliases = compute_param_aliases(tcx);
                let keep_alias_raw = tcx
                    .hir_crate(())
                    .owners
                    .iter()
                    .filter_map(|maybe_owner| maybe_owner.as_owner())
                    .find_map(|owner| {
                        let OwnerNode::Item(item) = owner.node() else {
                            return None;
                        };
                        let ItemKind::Fn { .. } = item.kind else {
                            return None;
                        };
                        (tcx.item_name(item.owner_id.def_id.to_def_id()).as_str()
                            == "keep_alias_raw")
                            .then_some(item.owner_id.def_id)
                    })
                    .expect("keep_alias_raw should exist");

                let keep_alias_raw_aliases = aliases
                    .get(&keep_alias_raw)
                    .expect("expected alias cluster for keep_alias_raw");
                assert!(
                    keep_alias_raw_aliases
                        .get(&Local::from_u32(1))
                        .is_some_and(|locals| locals.contains(&Local::from_u32(2)))
                );
                assert!(
                    keep_alias_raw_aliases
                        .get(&Local::from_u32(2))
                        .is_some_and(|locals| locals.contains(&Local::from_u32(1)))
                );
            },
        );
    }

    #[test]
    fn ownership_from_option_and_display() {
        assert_eq!(Ownership::from(Some(true)), Ownership::Owning);
        assert_eq!(Ownership::from(Some(false)), Ownership::Transient);
        assert_eq!(Ownership::from(None), Ownership::Unknown);

        assert_eq!(Ownership::Owning.to_string(), "&move");
        assert_eq!(Ownership::Transient.to_string(), "&");
        assert_eq!(Ownership::Unknown.to_string(), "&any");
    }

    #[test]
    fn param_helpers_cover_normal_and_output_variants() {
        let normal = Param::Normal(7u8);
        assert!(!normal.is_output());
        assert_eq!(normal.clone().into_input(), 7);
        assert_eq!(normal.clone().into_output(), None);
        assert_eq!(normal.clone().expect_normal(), 7);

        let output = Param::Output(Consume {
            r#use: 11u8,
            def: 13u8,
        });
        assert!(output.is_output());
        assert_eq!(output.clone().into_input(), 11);
        assert_eq!(output.clone().into_output(), Some(13));
        let consume = output.clone().expect_output();
        assert_eq!(consume.r#use, 11);
        assert_eq!(consume.def, 13);

        let mapped = output.map(|x| x as u16 + 1);
        let mapped = mapped.expect_output();
        assert_eq!(mapped.r#use, 12);
        assert_eq!(mapped.def, 14);
    }

    #[test]
    fn malloc_source_marks_return_as_owning() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    malloc(4)
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let alloc_one = find_function(&program, "alloc_one");

                let ret = results
                    .fn_sig(alloc_one)
                    .next()
                    .unwrap()
                    .unwrap()
                    .expect_normal();
                assert_eq!(ret, [Ownership::Owning]);
            },
        );
    }

    #[test]
    fn free_sink_clears_ownership_before_return() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut i32);
}

pub unsafe fn alloc_then_free() -> *mut i32 {
    let p = malloc(4);
    free(p);
    p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "alloc_then_free");

                // `free` is modeled as a sink, so returning the same pointer should not
                // keep it in an owning state.
                let ret = results.fn_sig(did).next().unwrap().unwrap().expect_normal();
                assert_eq!(ret, [Ownership::Transient]);
            },
        );
    }

    #[test]
    fn ownership_propagates_through_local_function_calls() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc() -> *mut i32 {
    malloc(4)
}

pub unsafe fn wrapper() -> *mut i32 {
    alloc()
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);

                let alloc = find_function(&program, "alloc");
                let wrapper = find_function(&program, "wrapper");

                let alloc_ret = results
                    .fn_sig(alloc)
                    .next()
                    .unwrap()
                    .unwrap()
                    .expect_normal();
                let wrapper_ret = results
                    .fn_sig(wrapper)
                    .next()
                    .unwrap()
                    .unwrap()
                    .expect_normal();

                assert_eq!(alloc_ret, [Ownership::Owning]);
                assert_eq!(wrapper_ret, [Ownership::Owning]);
            },
        );
    }

    #[test]
    fn unknown_foreign_calls_are_treated_conservatively() {
        run_compiler(
            r#"
extern "C" {
    fn mystery(ptr: *mut i32) -> *mut i32;
}

pub unsafe fn passthrough_unknown(p: *mut i32) -> *mut i32 {
    mystery(p)
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "passthrough_unknown");

                let mut sig = results.fn_sig(did);
                let ret = sig.next().unwrap().unwrap().expect_normal();
                let arg = sig.next().unwrap().unwrap().expect_output();

                // For unknown calls, the analysis borrows the destination and only lends args.
                assert_eq!(ret, [Ownership::Transient]);
                assert_eq!(arg.r#use[0], Ownership::Owning);
                assert_eq!(arg.def[0], Ownership::Owning);
            },
        );
    }

    #[test]
    fn mutable_pointer_to_pointer_argument_becomes_output_param() {
        run_compiler(
            r#"
pub unsafe fn write_out(out: *mut *mut i32, value: *mut i32) {
    *out = value;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "write_out");

                let mut sig = results.fn_sig(did);
                assert!(sig.next().unwrap().is_none());

                let output_like = sig.next().unwrap().unwrap();
                let passthrough = sig.next().unwrap().unwrap();

                let output_like = output_like.expect_output();
                assert_eq!(output_like.r#use[0], Ownership::Owning);
                assert_eq!(output_like.def[0], Ownership::Owning);
                assert!(matches!(passthrough, Param::Normal(_)));
            },
        );
    }

    #[test]
    fn solidify_marks_return_local_as_owning_for_malloc() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    malloc(4)
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let solidified = results.solidify(&program);
                let did = find_function(&program, "alloc_one");

                let return_local = Local::from_u32(0);
                let ret_local = solidified.fn_results(&did).local_result(return_local);
                assert_eq!(ret_local, [Ownership::Owning]);
            },
        );
    }

    #[test]
    fn refinement_reaches_high_precision_for_nested_pointer_output() {
        run_compiler(
            r#"
pub unsafe fn write_out(out: *mut *mut i32, value: *mut i32) {
    *out = value;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "write_out");
                assert!(
                    results.precision(&did) >= 2,
                    "nested pointer flow should keep precision >= 2",
                );

                let solidified = results.solidify(&program);
                let output_param = solidified.fn_results(&did).local_result(Local::from_u32(1));
                assert_eq!(output_param.len(), 2);
                assert_eq!(output_param[0], Ownership::Owning);
            },
        );
    }

    #[test]
    fn refinement_drops_precision_for_conflicting_phi_merge() {
        run_compiler(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn phi_merge(flag: bool, p: *mut i32) -> *mut i32 {
    let mut x: *mut i32 = p;
    if flag {
        x = malloc(4);
    }
    x
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let did = find_function(&program, "phi_merge");
                assert_eq!(
                    results.precision(&did),
                    0,
                    "conflicting phi merge should force conservative precision fallback",
                );

                let solidified = results.solidify(&program);
                let body = &*tcx
                    .mir_drops_elaborated_and_const_checked(did.expect_local())
                    .borrow();
                let fn_results = solidified.fn_results(&did);

                let ptr_temporaries = body
                    .local_decls
                    .iter_enumerated()
                    .filter(|(local, decl)| {
                        decl.ty.is_raw_ptr() && local.index() > body.arg_count && local.index() != 0
                    })
                    .map(|(local, _)| local)
                    .collect::<Vec<_>>();

                assert!(
                    !ptr_temporaries.is_empty(),
                    "expected at least one pointer temporary around branch merge",
                );

                assert!(ptr_temporaries.iter().all(|&local| {
                    fn_results
                        .local_result(local)
                        .first()
                        .is_none_or(|ownership| !ownership.is_owning())
                }));
            },
        );
    }

    #[test]
    fn solidify_struct_field_results_are_exposed() {
        run_compiler(
            r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn make_holder() -> Holder {
    Holder { p: malloc(4) }
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let results = analyze_program(&program);
                let solidified = results.solidify(&program);

                let holder = program
                    .structs
                    .iter()
                    .map(|did| did.to_def_id())
                    .find(|&did| tcx.def_path_str(did).rsplit("::").next() == Some("Holder"))
                    .expect("struct `Holder` not found");

                let fields = solidified.struct_results(&holder).collect::<Vec<_>>();
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0].len(), 1);
            },
        );
    }
}

mod borrow_ownership_slots {
    use std::ops::Range;

    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{mir::Local, ty::TyCtxt};
    use rustc_span::def_id::LocalDefId;

    use crate::{
        analyses::borrow_ownership::{
            crate_slots::CrateSlots,
            slots::{SlotId, SlotOwner, StructFieldSlot},
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

    fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }

        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn struct_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .structs
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("struct `{name}` not found"))
    }

    fn function_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .functions
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    fn slot_range_len(range: Range<SlotId>) -> usize {
        range.end.index() - range.start.index()
    }

    #[test]
    fn crate_slots_registers_struct_pointer_fields() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub a: *mut i32,
    pub b: *mut *mut i32,
}

pub unsafe fn use_s(s: *mut S) {
    let _x = (*s).a;
    let _y = (*s).b;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let a = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };
                let b = StructFieldSlot {
                    struct_did: s,
                    field_index: 1,
                };

                assert_eq!(
                    slot_range_len(slots.field_slots.slots_for_field(a).expect("field S::a")),
                    1
                );
                assert_eq!(
                    slot_range_len(slots.field_slots.slots_for_field(b).expect("field S::b")),
                    2
                );

                let a_slot = slots
                    .field_slots
                    .slot_for_field_depth(a, 0)
                    .expect("slot for field S::a depth 0");
                assert_eq!(slots.field_slots.slot(a_slot).owner, SlotOwner::Field(a));
                assert_eq!(slots.field_slots.slot(a_slot).depth, 0);
            },
        );
    }

    #[test]
    fn crate_slots_local_chain_stops_at_struct() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub a: *mut i32,
}

pub unsafe fn f(s: *mut S) {
    let _x = (*s).a;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let f = function_by_name(&program, "f");
                let local_s = Local::from_u32(1);
                let field = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };

                let local_slots = slots.fn_local_slots.get(&f).expect("slots for f");
                assert_eq!(
                    slot_range_len(local_slots.slots_for_local(local_s).expect("local _1")),
                    1
                );
                assert!(slots.field_slots.slots_for_field(field).is_some());
            },
        );
    }

    // Arrays of pointers are a deferred shape per the §2 boundary contract in
    // docs/agents/plan/2026-06-13-borrow-ownership-unified-plan-concrete.md;
    // Phase 2's resolver must treat the absent slot as conservative Raw.
    // TODO: descend arrays or mark owners unsupported in a later phase.
    #[test]
    fn crate_slots_defers_array_of_pointer_shapes() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub arr: [*mut i32; 4],
    pub scalar: *mut i32,
}

pub unsafe fn takes_array(arr: [*mut i32; 4]) -> *mut i32 {
    arr[0]
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let arr = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };
                let scalar = StructFieldSlot {
                    struct_did: s,
                    field_index: 1,
                };

                assert!(slots.field_slots.slots_for_field(arr).is_none());
                assert_eq!(
                    slot_range_len(
                        slots
                            .field_slots
                            .slots_for_field(scalar)
                            .expect("field S::scalar"),
                    ),
                    1
                );

                let f = function_by_name(&program, "takes_array");
                assert!(
                    slots
                        .fn_local_slots
                        .get(&f)
                        .expect("slots for takes_array")
                        .slots_for_local(Local::from_u32(1))
                        .is_none()
                );
            },
        );
    }

    #[test]
    fn crate_slots_tracks_nested_local_pointers() {
        run_compiler(
            r#"
pub unsafe fn g(pp: *mut *mut i32) -> i32 {
    **pp
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let g = function_by_name(&program, "g");
                let pp = Local::from_u32(1);

                let local_slots = slots.fn_local_slots.get(&g).expect("slots for g");
                assert_eq!(
                    slot_range_len(local_slots.slots_for_local(pp).expect("local _1")),
                    2
                );

                let depth_0 = local_slots
                    .slot_for_local_depth(pp, 0)
                    .expect("slot for pp depth 0");
                let depth_1 = local_slots
                    .slot_for_local_depth(pp, 1)
                    .expect("slot for pp depth 1");

                assert_eq!(local_slots.slot(depth_0).depth, 0);
                assert_eq!(local_slots.slot(depth_1).depth, 1);
            },
        );
    }

    #[test]
    fn crate_slots_generic_struct_field_depth() {
        run_compiler(
            r#"
#[repr(C)]
pub struct Wrap<T> {
    pub p: *mut T,
}

pub unsafe fn h(w: *mut Wrap<i32>) {
    let _z = (*w).p;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let wrap = struct_by_name(&program, "Wrap");
                let field = StructFieldSlot {
                    struct_did: wrap,
                    field_index: 0,
                };

                assert_eq!(
                    slot_range_len(
                        slots
                            .field_slots
                            .slots_for_field(field)
                            .expect("field Wrap::p"),
                    ),
                    1
                );
            },
        );
    }
}

mod borrow_ownership_solver {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{mir::Local, ty::TyCtxt};
    use rustc_span::def_id::LocalDefId;
    use z3::SatResult;

    use crate::{
        analyses::borrow_ownership::{
            SlotKind,
            crate_slots::CrateSlots,
            slots::SlotId,
            solver::{KindSolver, SlotRef},
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

    fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }

        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn function_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .functions
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    fn with_g_slots<F>(f: F)
    where F: for<'tcx> FnOnce(&RustProgram<'tcx>, &CrateSlots, LocalDefId, SlotId, SlotId) + Send
    {
        run_compiler(
            r#"
pub unsafe fn g(pp: *mut *mut i32) -> i32 {
    **pp
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let g = function_by_name(&program, "g");
                let fn_slots = slots.fn_local_slots.get(&g).expect("slots for g");
                let pp = Local::from_u32(1);
                let d0 = fn_slots
                    .slot_for_local_depth(pp, 0)
                    .expect("pp depth 0 slot");
                let d1 = fn_slots
                    .slot_for_local_depth(pp, 1)
                    .expect("pp depth 1 slot");

                f(&program, &slots, g, d0, d1);
            },
        );
    }

    #[test]
    fn baseline_slot_encoding_is_satisfiable() {
        with_g_slots(|_, slots, _, _, _| {
            let ks = KindSolver::new(slots);

            assert_eq!(ks.check(), SatResult::Sat);
        });
    }

    #[test]
    fn max_ref_promotes_free_chain() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);
            let s0 = SlotRef::Local(g, d0);
            let s1 = SlotRef::Local(g, d1);

            assert_eq!(ks.check(), SatResult::Sat);
            let model = ks.model_kinds().expect("satisfiable model");
            assert_eq!(model.get(&s0), Some(&SlotKind::Ref));
            assert_eq!(model.get(&s1), Some(&SlotKind::Ref));
        });
    }

    #[test]
    fn max_ref_under_assumption() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);
            let s0 = SlotRef::Local(g, d0);
            let s1 = SlotRef::Local(g, d1);

            ks.assume(s0, SlotKind::Owning);

            assert_eq!(ks.check(), SatResult::Sat);
            let model = ks.model_kinds().expect("satisfiable model");
            assert_eq!(model.get(&s0), Some(&SlotKind::Owning));
            assert_eq!(model.get(&s1), Some(&SlotKind::Ref));
        });
    }

    #[test]
    fn optimal_model_is_repeatable() {
        with_g_slots(|_, slots, _, _, _| {
            let ks = KindSolver::new(slots);

            let first = ks.model_kinds().expect("first satisfiable model");
            let second = ks.model_kinds().expect("second satisfiable model");

            assert_eq!(first, second);
        });
    }

    #[test]
    fn monotonicity_rejects_raw_over_owning() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);

            ks.assume(SlotRef::Local(g, d0), SlotKind::Raw);
            ks.assume(SlotRef::Local(g, d1), SlotKind::Owning);

            assert_eq!(ks.check(), SatResult::Unsat);
        });
    }

    #[test]
    fn owning_chain_is_satisfiable() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);

            ks.assume(SlotRef::Local(g, d0), SlotKind::Owning);
            ks.assume(SlotRef::Local(g, d1), SlotKind::Owning);

            assert_eq!(ks.check(), SatResult::Sat);
        });
    }

    #[test]
    fn ref_separates_raw_from_deeper_owning() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);

            ks.assume(SlotRef::Local(g, d0), SlotKind::Ref);
            ks.assume(SlotRef::Local(g, d1), SlotKind::Owning);

            assert_eq!(ks.check(), SatResult::Sat);
        });
    }

    #[test]
    fn model_reports_assumed_raw_slots() {
        with_g_slots(|_, slots, g, d0, d1| {
            let ks = KindSolver::new(slots);
            let s0 = SlotRef::Local(g, d0);
            let s1 = SlotRef::Local(g, d1);

            ks.assume(s0, SlotKind::Raw);
            ks.assume(s1, SlotKind::Raw);

            assert_eq!(ks.check(), SatResult::Sat);
            let model = ks.model_kinds().expect("satisfiable model");
            assert_eq!(model.get(&s0), Some(&SlotKind::Raw));
            assert_eq!(model.get(&s1), Some(&SlotKind::Raw));
        });
    }
}

mod borrow_ownership_coherence {
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{
        mir::{Local, Location, Operand, Rvalue, StatementKind},
        ty::TyCtxt,
    };
    use rustc_span::def_id::LocalDefId;
    use z3::SatResult;

    use crate::{
        analyses::{
            borrow::{GBorrowInferCtxt, demote_pointers_iterative_with_fields},
            borrow_ownership::{
                CrateCtxt, SlotKind,
                borrow_engine::{
                    borrow_conflicts_replaying_with_flows_and_copy_lends,
                    borrow_conflicts_replaying_witnessed_with_copy_lends,
                },
                borrow_verify::{
                    SlotConflict, materialize_guards, model_accepts, revalidate,
                    revalidate_replaying, verify_to_fixpoint,
                },
                coherence::{
                    CopyLendPair, add_coherence, add_coherence_with_copy_lends,
                    constrain_field_ownership, selected_copy_lend_sites,
                },
                crate_slots::CrateSlots,
                emit_crate_ownership_constraints, emit_crate_ownership_constraints_with_copy_lends,
                export::{LoanClass, location_key, with_bo_export},
                mutability_facts::MutFacts,
                origins::{collect_no_borrow_origin_slots, compute_origins},
                slots::{SlotId, StructFieldSlot},
                solver::{BoOwnDatabase, KindSolver, SlotRef},
                sources::collect_malloc_source_slots,
                ssa::constraint::{Database, Gen, Var},
            },
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

    fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }

        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn function_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .functions
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    fn struct_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .structs
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("struct `{name}` not found"))
    }

    fn local_slot(slots: &CrateSlots, fn_did: LocalDefId, local: Local, depth: u8) -> SlotRef {
        let slot = slots
            .fn_local_slots
            .get(&fn_did)
            .unwrap_or_else(|| panic!("slots for function {fn_did:?}"))
            .slot_for_local_depth(local, depth)
            .unwrap_or_else(|| panic!("slot for local {local:?} depth {depth}"));

        SlotRef::Local(fn_did, slot)
    }

    /// The `Local` whose source-level variable name is `name`, via MIR debug info.
    fn local_by_var_name(tcx: TyCtxt<'_>, did: LocalDefId, name: &str) -> Local {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        for vdi in body.var_debug_info.iter() {
            if vdi.name.as_str() == name
                && let rustc_middle::mir::VarDebugInfoContents::Place(place) = &vdi.value
                && let Some(local) = place.as_local()
            {
                return local;
            }
        }
        panic!("no local named `{name}` in {did:?}");
    }

    /// Shared §8 BB3-b assertion for a mixed-role-local fixture (a local conflated to one
    /// flow-insensitive `Owning` slot that also carries a reference role). `verify_to_fixpoint`
    /// must accept a model with **no hidden `Ref`-vs-`Ref` aliasing**: the BB3-b under-report was
    /// an `Owning` slot being EXCLUDED from the replay, hiding its reference role's conflict. The
    /// complete-by-construction candidacy (every non-`Ref` slot a replay candidate) makes that
    /// impossible, so we assert it directly — the accepted model is clean under the COMPLETE
    /// replay (`is_raw = model != Ref`), and the mixed-role local does not survive as an aliasing
    /// `Ref`. Non-vacuous: the all-`Ref` round-0 shows the shape is genuinely hazardous. (The
    /// mixed-role local is output `Owning` — an ownership-precision residual deferred to
    /// flow-sensitivity, NOT a borrow under-report.) A regression that re-excludes `Owning` slots
    /// from the replay would surface the hidden conflict at the COMPLETE-replay assertion.
    fn assert_mixed_role_no_hidden_aliasing(tcx: TyCtxt<'_>, fn_name: &str, local: &str) {
        let program = collect_program(tcx);
        let f = function_by_name(&program, fn_name);
        let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_s, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("ownership emission");
        add_coherence(&solver, &slots, f, &body);

        // Non-vacuous: the shape is genuinely hazardous (a round-0 all-Ref aliasing conflict).
        let round0 = revalidate(&program, &slots, |_| true, true);
        assert!(
            round0.get(&f).is_some_and(|e| !e.is_empty()),
            "[{fn_name}] shape must be hazardous (a round-0 all-Ref conflict)"
        );

        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
            .expect("CEGAR converges");

        // The mixed-role local must not survive as an aliasing `Ref`.
        let local_ref = local_slot(&slots, f, local_by_var_name(tcx, f, local), 0);
        assert_ne!(
            model.get(&local_ref),
            Some(&SlotKind::Ref),
            "[{fn_name}] mixed-role local `{local}` must not survive as a Ref; got {:?}",
            model.get(&local_ref)
        );

        // Contract: no hidden Ref-vs-Ref aliasing — clean under the COMPLETE replay (every
        // non-Ref slot a candidate, matching verify_to_fixpoint's own candidacy).
        let complete = revalidate_replaying(
            &program,
            &slots,
            |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref),
            |s: SlotRef| model.get(&s) != Some(&SlotKind::Ref),
            true,
        );
        assert!(
            complete.get(&f).map_or(true, |e| e.is_empty()),
            "[{fn_name}] accepted model must have no hidden aliasing under the complete replay; \
             got {complete:?}"
        );
    }

    #[test]
    fn alloc_free_emits_ownership_into_kind_solver() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_free() {
    let p = unsafe { malloc(4) };
    unsafe { free(p) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B1 ownership emission should run");

                assert!(
                    stats.z3_ast_len > 1,
                    "expected per-version ownership Bool vars to be allocated"
                );
                // 1 source from malloc + 1 sink from free.
                assert_eq!(stats.source_sink_emissions, 2);
                // §NB-F: BOTH are retractable now — 1 source selector (malloc)
                // + 1 sink selector (free).
                assert_eq!(selectors.sources().len(), 1);
                assert_eq!(selectors.sinks().len(), 1);
                assert_eq!(selectors.all().len(), 2);
                assert!(kind_solver.model_kinds_relaxing(&selectors).is_some());
            },
        );
    }

    /// Locate the destination `Local` of the first call to `callee` (e.g. the
    /// `*mut c_void` local that `malloc`'s result is written into). Robust to
    /// MIR temp renumbering — we never hardcode the index.
    fn call_destination(
        tcx: TyCtxt<'_>,
        body: &rustc_middle::mir::Body<'_>,
        callee: &str,
    ) -> Local {
        call_nth_destination(tcx, body, callee, 0)
    }

    /// Destination `Local` of the `n`-th (0-indexed, in basic-block order) call to
    /// `callee` — for functions with several calls to the same callee.
    fn call_nth_destination(
        tcx: TyCtxt<'_>,
        body: &rustc_middle::mir::Body<'_>,
        callee: &str,
        n: usize,
    ) -> Local {
        let mut seen = 0;
        for bbdata in body.basic_blocks.iter() {
            let Some(term) = &bbdata.terminator else {
                continue;
            };
            if let rustc_middle::mir::TerminatorKind::Call {
                func, destination, ..
            } = &term.kind
            {
                if let Some((def_id, _)) = func.const_fn_def() {
                    if tcx.def_path_str(def_id).rsplit("::").next() == Some(callee) {
                        if seen == n {
                            return destination.local;
                        }
                        seen += 1;
                    }
                }
            }
        }
        panic!("no call #{n} to `{callee}` found");
    }

    /// B2: the per-version ownership forced by `malloc`'s `source` hook must be
    /// solidified onto the slot — `p`'s depth-0 slot becomes `Owning`. Without
    /// the version→slot linking, the unconstrained slot would be `Ref` (max-ref).
    #[test]
    fn alloc_free_links_owning_to_slot() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_free() {
    let p = unsafe { malloc(4) };
    unsafe { free(p) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let alloc_free = function_by_name(&program, "alloc_free");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(alloc_free)
                    .borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B2 ownership emission should run");

                let p_local = call_destination(tcx, &body, "malloc");
                let p = local_slot(&slots, alloc_free, p_local, 0);

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
            },
        );
    }

    /// B2 headline (Ref-over-Owning) via a store-through-pointer `*out = malloc`.
    /// The inner (`*out`) is `Owning` — malloc's ownership solidified onto the
    /// temp slot and carried to `out`'s inner depth by coherence; the outer `out`
    /// is caller storage forced non-owning by `exit`, so §4 (`¬(raw ∧ own)`) +
    /// max-ref make it `Ref`. Without the version→slot link, `*out` is not
    /// `Owning` and this fails. NOTE: `output_params` is empty here, so this
    /// exercises the store-through-deref shape, not output-param *classification*.
    #[test]
    fn store_through_ptr_is_ref_over_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn fill(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let fill = function_by_name(&program, "fill");
                let body = tcx.mir_drops_elaborated_and_const_checked(fill).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B2 ownership emission should run");
                add_coherence(&kind_solver, &slots, fill, &body);

                // `out` is param Local 1: out[0] = borrowed caller storage,
                // out[1] = the malloc-owned inner.
                let out_outer = local_slot(&slots, fill, Local::from_u32(1), 0);
                let out_inner = local_slot(&slots, fill, Local::from_u32(1), 1);

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(
                    model.get(&out_inner),
                    Some(&SlotKind::Owning),
                    "inner *out = Owning (the malloc'd value)"
                );
                assert_eq!(
                    model.get(&out_outer),
                    Some(&SlotKind::Ref),
                    "outer out = Ref (borrowed caller storage)"
                );
            },
        );
    }

    /// B3a: a leaked allocation (its `source` owning conflicts with return
    /// finalization) makes the single solve UNSAT — `source` hard-forces the
    /// malloc'd local owning while finalize-temporaries hard-forces the same SSA
    /// version false. The relax loop drops that source's selector (leaks the
    /// allocation) and returns a SAT model. Assertion is deliberately
    /// kind-agnostic (solvable ∧ not Owning); the exact non-owning variant
    /// (Ref vs Raw) is a 3f borrow-integration concern, not pinned here.
    #[test]
    fn leaked_alloc_return_relaxes_to_sat() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { malloc(8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let leak = function_by_name(&program, "leak");
                let body = tcx.mir_drops_elaborated_and_const_checked(leak).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B3a ownership emission should run");

                // Prove the relax path is genuinely exercised: exactly one source
                // selector, and the un-relaxed solve (assuming it) is UNSAT — so a
                // broken impl that ignored selectors could not pass.
                assert_eq!(selectors.all().len(), 1);
                assert_eq!(
                    kind_solver.optimize().check(selectors.all()),
                    SatResult::Unsat,
                    "the source-owning constraint must make the single solve UNSAT"
                );

                // The relax loop must leak the source and return a model.
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("relax loop should resolve the UNSAT by leaking the source");

                let p_local = call_destination(tcx, &body, "malloc");
                let p = local_slot(&slots, leak, p_local, 0);
                assert_ne!(
                    model.get(&p),
                    Some(&SlotKind::Owning),
                    "leaked allocation must not be Owning"
                );
            },
        );
    }

    /// B3a multi-source: relaxation must leak only the *conflicting* allocation.
    /// `a` is malloc'd and freed (no finalize conflict → stays `Owning`); `b` is
    /// malloc'd and leaked via `&raw mut b` (its owning conflicts with finalize).
    /// The relax loop must drop only `b`'s selector — a maximal-source-retention
    /// policy. A naive "drop any unsat-core member" loop could leak `a` too if
    /// z3's (non-minimal) core happened to include it.
    #[test]
    fn two_allocs_leaks_only_the_conflicting_one() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn two_allocs() -> *mut *mut core::ffi::c_void {
    let a = unsafe { malloc(8) };
    unsafe { free(a) };
    let mut b = unsafe { malloc(8) };
    &raw mut b
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let two = function_by_name(&program, "two_allocs");
                let body = tcx.mir_drops_elaborated_and_const_checked(two).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B3a ownership emission should run");

                // Two sources + (§NB-F) one free-sink selector; assuming all is
                // UNSAT (b conflicts with finalize — assuming more preserves it).
                assert_eq!(selectors.sources().len(), 2);
                assert_eq!(selectors.sinks().len(), 1);
                assert_eq!(
                    kind_solver.optimize().check(selectors.all()),
                    SatResult::Unsat
                );

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("relax loop should leak only b");

                // `a` (freed) must remain Owning; `b` (leaked) must not.
                let a_local = call_nth_destination(tcx, &body, "malloc", 0);
                let b_local = call_nth_destination(tcx, &body, "malloc", 1);
                let a = local_slot(&slots, two, a_local, 0);
                let b = local_slot(&slots, two, b_local, 0);
                assert_eq!(
                    model.get(&a),
                    Some(&SlotKind::Owning),
                    "the freed allocation must stay Owning (not over-leaked)"
                );
                assert_ne!(
                    model.get(&b),
                    Some(&SlotKind::Owning),
                    "the leaked allocation must not be Owning"
                );
            },
        );
    }

    /// §S2-1 (NB-F review F2) — a GENUINE mixed source/sink either/or tie
    /// whose UNSAT core is EXACTLY `{source-selector, sink-selector}`, so
    /// phase-2 restoration provably cannot undo it (F2's caveat) and the
    /// phase-1 drop choice alone decides which side leaks.
    ///
    /// The fabric that admits it is B4's Output protocol: every BO pointer
    /// arg is `Param::Output`, so a call pushes EQUALITIES (`sig.use =
    /// arg.use`, `sig.def = arg.def`) — a bidirectional broadcast shared by
    /// all call sites — and an Output param's final version is EXPORTED
    /// (`exit` equates it to `sig.def`), not finalize-pinned. The empty
    /// `pass(_x)` therefore fuses `sig.use = x_v0 = sig.def` into one
    /// equality class. `source_side` puts the source-forced `m_v1` into that
    /// class and escapes `m` through its (unconsumed) return — no sink on the
    /// source's branch. `sink_side`'s copy `let b = a` emits the fabric's
    /// only exclusivity, `push_linear(b_w1, a_v1, a_v0)` with `¬(b_w1 ∧
    /// a_v1)`; `pass(b)` puts fork child `b_w1` into the same class, `b`
    /// escapes through the return, and `free(a)` pins the sibling `a_v1`.
    /// So `¬(b_w1 ∧ a_v1)` fires iff `s ∧ k` — and with only these two
    /// selectors in the crate, `{s, k}` is the whole core.
    ///
    /// The tie is PROVED inside the fixture (it can never pass vacuously):
    /// `check(H∧s∧k) = Unsat ∧ check(H∧s) = Sat ∧ check(H∧k) = Sat`.
    ///
    /// RETENTION POLICY UNDER TEST (S2-1 decided-default: drop sinks first,
    /// retain sources — source retention drives Owning conversion, and a
    /// leaked sink only costs a leak while a leaked source costs precision):
    /// the relax loop must leak exactly `{k}` and retain the source,
    /// converting `m` to Owning. The pre-fix positional phase-1 pick drops
    /// the earliest-positioned core assumption; `Selectors::new` orders
    /// sources first, so it leaks the SOURCE and retains the sink — F2's
    /// backwards outcome, which phase 2 then cannot repair.
    #[test]
    fn nbs2_mixed_tie_drops_sink_retains_source() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn pass(_x: *mut core::ffi::c_void) {}

pub unsafe fn source_side() -> *mut core::ffi::c_void {
    let m = unsafe { malloc(4) };
    unsafe { pass(m) };
    m
}

pub unsafe fn sink_side(a: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let b = a;
    unsafe { pass(b) };
    unsafe { free(a) };
    b
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let source_side = function_by_name(&program, "source_side");
                let sink_side = function_by_name(&program, "sink_side");
                let source_body = tcx
                    .mir_drops_elaborated_and_const_checked(source_side)
                    .borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("S2-1 ownership emission should run");

                // Exactly ONE source (source_side's malloc) and ONE sink
                // (sink_side's free) exist in the crate: the mixed pair IS
                // the entire retractable-assumption set.
                assert_eq!(selectors.sources().len(), 1);
                assert_eq!(selectors.sinks().len(), 1);
                let s = selectors.sources()[0].clone();
                let k = selectors.sinks()[0].clone();

                // THE TIE PROOF (non-vacuity): jointly infeasible, each side
                // individually satisfiable — a true either/or tie that
                // phase-2 restoration cannot undo.
                assert_eq!(
                    kind_solver.optimize().check(&[s.clone(), k.clone()]),
                    SatResult::Unsat,
                    "mixed pair {{source, sink}} must be a genuine joint conflict"
                );
                assert_eq!(
                    kind_solver.optimize().check(&[s.clone()]),
                    SatResult::Sat,
                    "the source alone must be satisfiable (m escapes via the return)"
                );
                assert_eq!(
                    kind_solver.optimize().check(&[k.clone()]),
                    SatResult::Sat,
                    "the sink alone must be satisfiable (a's unit is voluntary)"
                );

                // RETENTION under the relax loop: leak exactly the sink,
                // retain the source.
                let (model, dropped) = kind_solver
                    .model_kinds_relaxing_reporting(&selectors)
                    .expect("relax loop must converge to SAT");
                assert_eq!(
                    dropped.len(),
                    1,
                    "a true 1-vs-1 tie leaks exactly one selector"
                );
                assert!(
                    selectors.is_sink(&dropped[0]),
                    "a mixed tie must drop the SINK and retain the SOURCE (S2-1 policy)"
                );

                // Source retention drives Owning conversion: m stays Owning.
                let m_local = call_destination(tcx, &source_body, "malloc");
                let m_slot = local_slot(&slots, source_side, m_local, 0);
                assert_eq!(
                    model.get(&m_slot),
                    Some(&SlotKind::Owning),
                    "the retained source must convert m to Owning"
                );

                // OBSERVED-VALUE PIN (semantic-change comment, NB-F practice):
                // the leaked free's pointer `a` settles OWNING here — the
                // retained source forces the shared `pass` equality class
                // true, the copy's fork child `b_w1` receives it, and
                // child⇒parent (`x → z` of the linear split) pulls `a`'s
                // entry version owning. A leaked free's value kind is
                // OBSERVED, not designed (NB-F decision 3): this is a
                // synthetic instance of a leaked free settling non-Raw.
                // Cross-ref S2-2 (2026-07-04-nb-stage2-backlog.md): the
                // freed-slot kind census must find this pin, not rediscover
                // it; a freed-`Ref` (not seen here) remains the
                // soundness-critical case that gates C2. This is a BREAKABLE
                // observation, not a semantic contract: if a later phase
                // (NB3/NB4 origins, call semantics) legitimately changes the
                // value, re-derive and re-pin the observation — do not
                // preserve Owning for its own sake.
                let a_local = local_by_var_name(tcx, sink_side, "a");
                let a_slot = local_slot(&slots, sink_side, a_local, 0);
                assert_eq!(
                    model.get(&a_slot),
                    Some(&SlotKind::Owning),
                    "observed: leaked-free a pulled Owning via the broadcast + fork parent"
                );
            },
        );
    }

    /// §S2-1 adversarial-review fold (Codex F1, HIGH) — the sinks-first
    /// policy's cardinality trade, pinned as DELIBERATE: with overlapping
    /// mixed cores `{s, k1}` and `{s, k2}` (one source's broadcast opposing
    /// TWO caller frees), retaining the source costs TWO leaked sinks where
    /// the pre-S2-1 positional pick would have leaked the one source. The
    /// leak set is subset-minimal (phase 2 proves neither sink individually
    /// restorable while the source is retained) but not minimum-cardinality
    /// — D7's rationale: the source's Owning conversion is precision;
    /// leaked frees stay raw-pointer frees. Zero corpus rows changed under
    /// this policy (Phase-0 baseline sweep), so today the trade is
    /// fixture-only; if corpus data ever shows material sink-leak
    /// inflation, a cardinality-aware refinement is a stage-2 decision,
    /// not a drive-by.
    #[test]
    fn nbs2_mixed_fanout_prefers_source_over_two_sinks() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn pass(_x: *mut core::ffi::c_void) {}

pub unsafe fn source_side() -> *mut core::ffi::c_void {
    let m = unsafe { malloc(4) };
    unsafe { pass(m) };
    m
}

pub unsafe fn sink_side1(a1: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let b = a1;
    unsafe { pass(b) };
    unsafe { free(a1) };
    b
}

pub unsafe fn sink_side2(a2: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let b = a2;
    unsafe { pass(b) };
    unsafe { free(a2) };
    b
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let source_side = function_by_name(&program, "source_side");
                let source_body = tcx
                    .mir_drops_elaborated_and_const_checked(source_side)
                    .borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("S2-1 fan-out emission should run");

                assert_eq!(selectors.sources().len(), 1);
                assert_eq!(selectors.sinks().len(), 2);
                let s = selectors.sources()[0].clone();
                let k1 = selectors.sinks()[0].clone();
                let k2 = selectors.sinks()[1].clone();
                let check = |set: &[&z3::ast::Bool]| {
                    kind_solver
                        .optimize()
                        .check(&set.iter().map(|&b| b.clone()).collect::<Vec<_>>())
                };

                // The overlapping-core structure: the source ties with EACH
                // sink separately; the two sinks do not tie with each other.
                assert_eq!(check(&[&s, &k1]), SatResult::Unsat);
                assert_eq!(check(&[&s, &k2]), SatResult::Unsat);
                assert_eq!(check(&[&k1, &k2]), SatResult::Sat);
                assert_eq!(check(&[&s]), SatResult::Sat);
                assert_eq!(check(&[&k1]), SatResult::Sat);
                assert_eq!(check(&[&k2]), SatResult::Sat);

                // POLICY PIN: both sinks leak, the source is retained — a
                // 2-leak outcome preferred over the 1-leak source drop.
                let (model, dropped) = kind_solver
                    .model_kinds_relaxing_reporting(&selectors)
                    .expect("relax loop must converge to SAT");
                assert_eq!(
                    dropped.len(),
                    2,
                    "the fan-out trade leaks both sinks (subset-minimal, not min-cardinality)"
                );
                assert!(
                    dropped.iter().all(|d| selectors.is_sink(d)),
                    "every leaked selector is a sink; the source is retained"
                );

                let m_local = call_destination(tcx, &source_body, "malloc");
                let m_slot = local_slot(&slots, source_side, m_local, 0);
                assert_eq!(
                    model.get(&m_slot),
                    Some(&SlotKind::Owning),
                    "the retained source must convert m to Owning"
                );
            },
        );
    }

    /// §S2-1 control — a PURE-SOURCE tie (the plan's control): two sources
    /// force OPPOSITE children of one copy-fork through two different callee
    /// broadcasts. `f_sink(m1)` forces `sigF.use`; `f_sink(b)` routes it into
    /// fork child `b_w1`. `g_sink(m2)` forces `sigG.use`; `g_sink(a)` routes
    /// it into the sibling `a_v1`. `¬(b_w1 ∧ a_v1)` makes `{s1, s2}` jointly
    /// infeasible while each alone is SAT — proved by the same check() triple.
    /// (Cross-side sink pairs tie too — the grave-sinks demand the same
    /// broadcasts — so the maximal retention is one whole SIDE: {s2, k_g}.)
    ///
    /// CONTROL PROPERTY: the relax outcome must be IDENTICAL before and after
    /// the mixed-tie fix — the F-side falls (earliest-positioned members drop
    /// first in both policies), G-side retained, m2 Owning, m1 Raw.
    #[test]
    fn nbs2_pure_source_tie_control_unchanged() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

unsafe fn f_sink(x: *mut core::ffi::c_void) {
    unsafe { free(x) };
}

unsafe fn g_sink(x: *mut core::ffi::c_void) {
    unsafe { free(x) };
}

pub unsafe fn ctrl2(a: *mut core::ffi::c_void) {
    let m1 = unsafe { malloc(4) };
    unsafe { f_sink(m1) };
    let m2 = unsafe { malloc(8) };
    unsafe { g_sink(m2) };
    let b = a;
    unsafe { f_sink(b) };
    unsafe { g_sink(a) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let ctrl = function_by_name(&program, "ctrl2");
                let body = tcx.mir_drops_elaborated_and_const_checked(ctrl).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("S2-1 control emission should run");

                assert_eq!(selectors.sources().len(), 2);
                assert_eq!(selectors.sinks().len(), 2);
                // Sources are emitted in statement order within `ctrl2`:
                // s1 = m1's malloc, s2 = m2's malloc. Verified structurally
                // below: the two sources must tie with EACH OTHER.
                let s1 = selectors.sources()[0].clone();
                let s2 = selectors.sources()[1].clone();
                let check = |set: &[&z3::ast::Bool]| {
                    kind_solver
                        .optimize()
                        .check(&set.iter().map(|&b| b.clone()).collect::<Vec<_>>())
                };

                // THE PURE-SOURCE TIE PROOF: jointly infeasible, each alone SAT.
                assert_eq!(
                    check(&[&s1, &s2]),
                    SatResult::Unsat,
                    "{{s1, s2}} must be a genuine pure-source joint conflict"
                );
                assert_eq!(check(&[&s1]), SatResult::Sat, "s1 alone must be SAT");
                assert_eq!(check(&[&s2]), SatResult::Sat, "s2 alone must be SAT");

                // CONTROL: the relax outcome is side-shaped and identical
                // under both retention policies — the F-side (s1 and f_sink's
                // grave) is dropped, the G-side retained.
                let (model, dropped) = kind_solver
                    .model_kinds_relaxing_reporting(&selectors)
                    .expect("relax loop must converge to SAT");
                assert_eq!(
                    dropped.len(),
                    2,
                    "one whole side (source + its grave-sink) must leak; got {:?}",
                    dropped.len()
                );
                assert_eq!(
                    dropped.iter().filter(|d| selectors.is_sink(d)).count(),
                    1,
                    "the dropped side is one source plus one sink"
                );
                assert!(
                    dropped.iter().any(|d| d == &s1) && !dropped.iter().any(|d| d == &s2),
                    "positional within-class order is preserved: s1 (earliest) leaks, s2 survives"
                );

                // Retained side converts: m2 Owning; leaked side does not: m1
                // non-Owning (Raw under NB0's eager ¬ref on source slots).
                let m1_local = call_nth_destination(tcx, &body, "malloc", 0);
                let m2_local = call_nth_destination(tcx, &body, "malloc", 1);
                let m1_slot = local_slot(&slots, ctrl, m1_local, 0);
                let m2_slot = local_slot(&slots, ctrl, m2_local, 0);
                assert_eq!(
                    model.get(&m2_slot),
                    Some(&SlotKind::Owning),
                    "the retained source must stay Owning"
                );
                assert_ne!(
                    model.get(&m1_slot),
                    Some(&SlotKind::Owning),
                    "the leaked source must not be Owning"
                );
            },
        );
    }

    /// §S2-1 control — a PURE-SINK tie (alias double-free): within-class
    /// retention must keep the pre-change positional behavior, byte-identical
    /// before/after the mixed-tie fix. `b = a` forks `a_v1 = b_w1 + a_v2`;
    /// the two frees pin the sibling children, so `{k1, k2}` is jointly
    /// infeasible while each free alone is satisfiable — and the source `s`
    /// allies with EITHER free (it feeds whichever consumes). The loop drops
    /// the earliest-positioned sink (k1), retains the source and k2, and
    /// phase-2 restores any spuriously dropped selector.
    ///
    /// (The plan asked for a pure-SOURCE tie control; that shape is
    /// structurally impossible in the current fabric — sources only GIVE, and
    /// two gives never clash; opposition needs a taker. Recorded as an S2-1
    /// finding in the task doc. The sink/sink tie is the constructible
    /// within-class control.)
    #[test]
    fn nbs2_pure_sink_tie_control_positional_unchanged() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn ctrl() {
    let a = unsafe { malloc(8) };
    let b = a;
    unsafe { free(a) };
    unsafe { free(b) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let ctrl = function_by_name(&program, "ctrl");
                let body = tcx.mir_drops_elaborated_and_const_checked(ctrl).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("S2-1 control emission should run");

                assert_eq!(selectors.sources().len(), 1);
                assert_eq!(selectors.sinks().len(), 2);
                let s = selectors.sources()[0].clone();
                let k1 = selectors.sinks()[0].clone();
                let k2 = selectors.sinks()[1].clone();

                // Tie proof, sink/sink: jointly infeasible, each side SAT,
                // and the source allies with either free.
                assert_eq!(
                    kind_solver.optimize().check(&[k1.clone(), k2.clone()]),
                    SatResult::Unsat
                );
                assert_eq!(kind_solver.optimize().check(&[k1.clone()]), SatResult::Sat);
                assert_eq!(kind_solver.optimize().check(&[k2.clone()]), SatResult::Sat);
                assert_eq!(
                    kind_solver.optimize().check(&[s.clone(), k1.clone()]),
                    SatResult::Sat
                );
                assert_eq!(
                    kind_solver.optimize().check(&[s.clone(), k2.clone()]),
                    SatResult::Sat
                );

                // Within-class positional retention: exactly one sink leaked
                // (the earliest-positioned, k1), source retained, a Owning.
                let (model, dropped) = kind_solver
                    .model_kinds_relaxing_reporting(&selectors)
                    .expect("relax loop must converge to SAT");
                assert_eq!(dropped.len(), 1, "minimal leak set is one free");
                assert!(
                    selectors.is_sink(&dropped[0]),
                    "a pure-sink tie must leak a sink, never the source"
                );
                assert!(
                    dropped[0] == k1,
                    "within-class tie-break stays positional: the earliest sink leaks"
                );

                let a_local = call_destination(tcx, &body, "malloc");
                let a_slot = local_slot(&slots, ctrl, a_local, 0);
                assert_eq!(
                    model.get(&a_slot),
                    Some(&SlotKind::Owning),
                    "the source must stay retained (Owning) on a pure-sink tie"
                );
            },
        );
    }

    /// §NB1 test (a) — the TRANSITIVE gap. `safe(x) ≡ ¬raw(x)`. Accessing the
    /// deepest slot of a pointer chain through its shallower layers asserts,
    /// per site, `safe(deep) ⇒ safe(each traversed layer)`; so no model may
    /// leave a SAFE deep slot over a RAW shallow one — including the
    /// `raw@0 / ref@1 / own@2` inversion that the structural `i1-adjacency`
    /// (`¬(raw ∧ own)` on adjacent pairs only) PERMITS for the `ref`-deep and
    /// non-adjacent cases. Probed directly on the emitted clause: with the
    /// per-site walk, assuming `raw(ppp@0) ∧ own(ppp@2)` is UNSAT (the deep
    /// safe slot forces the shallow layer safe); the all-raw chain stays SAT
    /// (non-vacuity — the clause only forbids safe-over-raw, never forces a
    /// kind). Under the pre-NB1 `chain`/`off` behavior no such clause exists,
    /// so the inversion is satisfiable — this fixture fails until the walk lands.
    #[test]
    fn nb1_transitive_gap_rejected() {
        run_compiler(
            r#"
pub unsafe fn chain(ppp: *mut *mut *mut i32) {
    let _y = **ppp;
}
"#,
            |tcx| {
                let build = |tcx| {
                    let program = collect_program(tcx);
                    let f = function_by_name(&program, "chain");
                    let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                    let slots = CrateSlots::build(&program);
                    let solver = KindSolver::new(&slots);
                    add_coherence(&solver, &slots, f, &body);
                    let ppp = local_by_var_name(tcx, f, "ppp");
                    let s0 = local_slot(&slots, f, ppp, 0);
                    let s2 = local_slot(&slots, f, ppp, 2);
                    (solver, s0, s2)
                };

                // safe deep (own@2) over raw shallow (raw@0) is forbidden.
                let (solver, s0, s2) = build(tcx);
                solver.assume(s0, SlotKind::Raw);
                solver.assume(s2, SlotKind::Owning);
                assert_eq!(
                    solver.check(),
                    SatResult::Unsat,
                    "per-site SAFE-MONO must forbid a safe deep slot over a raw shallow layer"
                );

                // Non-vacuity: an all-raw chain is fine (the clause forbids only
                // safe-over-raw, it never forces a kind).
                let (solver, s0, s2) = build(tcx);
                solver.assume(s0, SlotKind::Raw);
                solver.assume(s2, SlotKind::Raw);
                assert_eq!(
                    solver.check(),
                    SatResult::Sat,
                    "an all-raw chain must stay satisfiable"
                );
            },
        );
    }

    /// §NB1 test (b) — the FIELD boundary the structural `i1-adjacency` cannot
    /// reach. A struct field accessed through a raw parent pointer at a site
    /// (`(*s).f`) is a per-site layer traversal: `safe(field.f@0) ⇒ safe(s@0)`.
    /// So an `Owning`-eligible field cannot stay safe when read through a raw
    /// parent. Probed: assuming `raw(s@0) ∧ ref(field.f@0)` is UNSAT with the
    /// walk (a safe field over a raw parent is forbidden); `raw(s@0) ∧
    /// raw(field.f@0)` stays SAT. The structural adjacency relates only
    /// same-owner slots within one universe, so no `chain`/`off` clause spans
    /// the Local→Field boundary — this fixture fails until the walk lands.
    #[test]
    fn nb1_raw_parent_field_site_demotes() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub f: *mut i32,
}

pub unsafe fn g(s: *mut S) {
    let _y = (*s).f;
}
"#,
            |tcx| {
                let build = |tcx| {
                    let program = collect_program(tcx);
                    let f = function_by_name(&program, "g");
                    let s_did = struct_by_name(&program, "S");
                    let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                    let slots = CrateSlots::build(&program);
                    let solver = KindSolver::new(&slots);
                    add_coherence(&solver, &slots, f, &body);
                    let s = local_by_var_name(tcx, f, "s");
                    let parent = local_slot(&slots, f, s, 0);
                    let field_id = slots
                        .field_slots
                        .slot_for_field_depth(
                            StructFieldSlot {
                                struct_did: s_did,
                                field_index: 0,
                            },
                            0,
                        )
                        .expect("field f depth-0 slot");
                    (solver, parent, SlotRef::Field(field_id))
                };

                // safe field (ref) over raw parent is forbidden.
                let (solver, parent, field) = build(tcx);
                solver.assume(parent, SlotKind::Raw);
                solver.assume(field, SlotKind::Ref);
                assert_eq!(
                    solver.check(),
                    SatResult::Unsat,
                    "per-site SAFE-MONO must demote a field read through a raw parent pointer"
                );

                // Non-vacuity: a raw field over a raw parent is fine.
                let (solver, parent, field) = build(tcx);
                solver.assume(parent, SlotKind::Raw);
                solver.assume(field, SlotKind::Raw);
                assert_eq!(
                    solver.check(),
                    SatResult::Sat,
                    "a raw field over a raw parent must stay satisfiable"
                );
            },
        );
    }

    /// §NB1 adversarial-review fold (Codex, 2026-07-10) — a pure WRITE/overwrite
    /// destination is NOT a SAFE-MONO site. `(*s).f = malloc()` writes THROUGH
    /// the parent `s` but does not dereference the field's OLD value as a
    /// reference, so this site must not couple the (crate-wide) field kind to
    /// the parent pointer's kind. Contrast `nb1_raw_parent_field_site_demotes`,
    /// where the field is READ through the parent. The field may therefore be
    /// `Owning` even when the parent is `Raw`: `raw(s@0) ∧ own(field.f@0)` must
    /// stay SAT (the store LHS emits no clause). Pre-fold, the walk emitted the
    /// clause for the store LHS too, spuriously coupling the field to every
    /// parent pointer and over-demoting on the corpus. SAFE-MONO is heuristic
    /// pruning — soundness is carried by the acceptance replay, not this clause.
    #[test]
    fn nb1_write_dest_does_not_couple_field_to_parent() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct S {
    pub f: *mut core::ffi::c_void,
}

pub unsafe fn stash(s: *mut S) {
    (*s).f = malloc(4);
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "stash");
                let s_did = struct_by_name(&program, "S");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let solver = KindSolver::new(&slots);
                add_coherence(&solver, &slots, f, &body);
                let s = local_by_var_name(tcx, f, "s");
                let parent = local_slot(&slots, f, s, 0);
                let field_id = slots
                    .field_slots
                    .slot_for_field_depth(
                        StructFieldSlot {
                            struct_did: s_did,
                            field_index: 0,
                        },
                        0,
                    )
                    .expect("field f depth-0 slot");
                let field = SlotRef::Field(field_id);

                solver.assume(parent, SlotKind::Raw);
                solver.assume(field, SlotKind::Owning);
                assert_eq!(
                    solver.check(),
                    SatResult::Sat,
                    "a store destination must not couple the field kind to the parent pointer"
                );
            },
        );
    }

    /// §NB2 — mutability hard facts, the shared-read WIN (requirement #2, coexistence).
    /// Two aliasing reborrows of one base that are only READ settle Foster `Imm`. Under
    /// fact-driven mutability, `borrow::invalidates` skips their immutable loans
    /// (`invalidates.rs:73`), so the aliasing produces no conflict and every slot stays `Ref`.
    /// The control prong (forced-mut, pre-NB2) treats the same reads as mutable and demotes
    /// >=1 slot — the two-prong design proves the mutability facts are the *sole* cause of the
    /// win (identical program, only the oracle differs). Structurally this is the `bb0`
    /// conflict with reads in place of writes.
    ///
    /// Liveness note: `errors = loan_liveness ∩ invalidates` (`errors.rs:8`), and `is_mutable`
    /// is read ONLY in `invalidates` — so an immutable loan still fully participates in
    /// liveness; only its invalidation is suppressed. That participation is structural (no
    /// fixture can break it), which is why this pair pins invalidation, not liveness.
    #[test]
    fn nb2_two_shared_reads_both_ref() {
        run_compiler(
            r#"
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut r1 = p;
    let mut r2 = r1;
    let mut q = r1;
    let a = *q;
    let b = *r1;
    let c = *r2;
    let d = *p;
    a + b + c + d
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let slot_of =
                    |name: &str| local_slot(&slots, f, local_by_var_name(tcx, f, name), 0);
                let names = ["p", "r1", "r2", "q"];

                // Control: forced-mutable (pre-NB2) — the aliasing reads are treated as
                // mutable, so the CEGAR loop demotes >=1 slot off Ref.
                let model_ctrl = {
                    let solver = KindSolver::new(&slots);
                    let (_s, selectors) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("control emission");
                    add_coherence(&solver, &slots, f, &body);
                    verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                        .expect("control accepts")
                };
                let ctrl_ref = names
                    .iter()
                    .filter(|n| model_ctrl.get(&slot_of(n)) == Some(&SlotKind::Ref))
                    .count();
                assert!(
                    ctrl_ref < names.len(),
                    "forced-mut control: aliasing reads must demote >=1 slot; all stayed Ref"
                );

                // Treatment: fact-driven — all reads ⇒ Foster Imm ⇒ immutable loans skipped ⇒
                // no conflict ⇒ every slot stays Ref.
                let facts = MutFacts::from_program(&program);
                let model_fact = {
                    let solver = KindSolver::new(&slots);
                    let (_s, selectors) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("treatment emission");
                    add_coherence(&solver, &slots, f, &body);
                    verify_to_fixpoint(&program, &slots, &solver, &selectors, &facts)
                        .expect("treatment accepts")
                };
                for n in names {
                    assert_eq!(
                        model_fact.get(&slot_of(n)),
                        Some(&SlotKind::Ref),
                        "fact-driven: `{n}` stays Ref (shared read, immutable loan skipped)"
                    );
                }
            },
        );
    }

    /// §NB2 — the write direction (requirement #2, "killed by a write"). A pointer written
    /// through ITSELF is Foster `Mut` (Foster is precise for the same-pointer case), so its
    /// loan is NOT skipped: the aliasing conflict survives fact-driven mutability exactly as
    /// under forced-mut, and >=1 slot is still demoted. Companion to
    /// `nb2_two_shared_reads_both_ref` (reads relax, writes do not). The program is the `bb0`
    /// conflict verbatim. (The cross-alias case — a cell written through a *sibling* while a
    /// read-only view stays `Imm` — is the separate S2-6 gap; see
    /// `nb2_cross_alias_write_uncaught_witness`.)
    #[test]
    fn nb2_written_base_still_conflicts() {
        run_compiler(
            r#"
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut r1 = p;
    let mut r2 = r1;
    let mut q = r1;
    *q = 1;
    *r1 = 2;
    *r2 = 3;
    *p = 4;
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let slot_of =
                    |name: &str| local_slot(&slots, f, local_by_var_name(tcx, f, name), 0);
                let names = ["p", "r1", "r2", "q"];

                let facts = MutFacts::from_program(&program);
                let model = {
                    let solver = KindSolver::new(&slots);
                    let (_s, selectors) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("emission");
                    add_coherence(&solver, &slots, f, &body);
                    verify_to_fixpoint(&program, &slots, &solver, &selectors, &facts)
                        .expect("accepts")
                };
                let ref_count = names
                    .iter()
                    .filter(|n| model.get(&slot_of(n)) == Some(&SlotKind::Ref))
                    .count();
                assert!(
                    ref_count < names.len(),
                    "fact-driven: written bases stay Mut, so the conflict survives (>=1 demoted)"
                );
            },
        );
    }

    /// §NB2 S2-6 witness — the CONFIRMED cross-alias immutable-loan invalidation gap.
    ///
    /// Rebuilt 2026-07-10 after a Codex adversarial review DISPROVED the earlier "the coherence
    /// equate-closure is the acceptance-level guard" claim. The earlier program was a *direct*
    /// copy cluster (`let xp = p; let z = xp; let b = p; *b = 5;`): p/xp/z/b are one coherence
    /// cluster, a mutable p/b conflict demotes the whole cluster in BOTH modes, so it was
    /// non-causal (the skip changed nothing — even the round-0 conflict edges were byte-identical
    /// across modes) and proved no gap. The equate-closure only unifies DIRECT copy clusters; it
    /// does NOT model interprocedural aliases.
    ///
    /// Here `x = id(p)` aliases `p` through a CALL RETURN, which coherence does not connect, so
    /// x/z/q form their own cluster carrying ONLY immutable loans (Foster marks x/z/q `Imm` —
    /// verified below — they are never written THROUGH; the write is via the mutable sibling `b`,
    /// `b = p`). `*b = 5` demotes the p/b cluster but NOT x/z/q. Result — **mode-differential**
    /// (the causal proof the skip runs, which the old witness lacked):
    ///   - forced-mut (skip OFF): x/z/q = `Raw` (their loans participate; the write demotes them);
    ///   - fact-mut  (skip ON):  x/z/q = `Ref` in STATE-2 — a shared `&T` aliasing the written cell;
    ///     NB4-R (STATE-3, 2026-07-15) now routes the write to their loan, so this is `Raw` too (the
    ///     mode differential collapses).
    ///
    /// In STATE-2 the fact-mode `Ref` was an **acceptance-level unsoundness REAL TODAY** (not merely
    /// "if flow-sensitivity is relaxed"), production-PARITY (production's own
    /// `borrow::mutable_references_no_guarantee` promotes x and q to shared `&T` on this exact program
    /// — verified), guarded ONLY by the **§8 codegen guardrail** (BO output unconsumed by codegen).
    /// NB4-R (STATE-3) removes that unsoundness for this shape by demoting x/z/q to `Raw` at analysis
    /// time — §8 is no longer the sole guard here.
    ///
    /// **NB3-3b finding (2026-07-10): write-aware invalidation does NOT close THIS case.** 3b
    /// restores the read/write distinction so an immutable loan is skipped for reads only. But the
    /// cross-alias write here is `*b = 5` with `b = p` (a copy), and `local_map.row(b)` is EMPTY —
    /// the loan is on `(*x)`/`(*p)`, not on `b`, so the write invalidates nothing. Place-conflict is
    /// structurally blind to the call-return alias (`x = id(p)`); write-awareness cannot route the
    /// write's invalidation of p's loan to x's loan. The forced-mut demotion of x/z/q rides the
    /// READ pointer-copies `z = x`/`q = x` (verified: `INSERT rw=Read borrowed=(*x)` at those
    /// points), which the read-skip soundly preserves. Closing this needed **routing** (the router is
    /// NB4-R, place-based). **NB4-R HAS LANDED (2026-07-15): this now flips to `Raw` — see the in-test
    /// STATE-3 assertions.** (The SOUND-skip proof is `nb2_two_shared_reads_both_ref`; this was its
    /// UNSOUND-skip counterpart until NB4-R.)
    ///
    /// **Decision B (2026-07-11):** the 3b write-aware fix was measured **corpus-inert** — 0
    /// shared-ref demotions across all 19 accepts (same-base immutable-written cases don't arise
    /// from real Foster facts: a written-through pointer is Foster `Mut`, so its loan is never
    /// skip-eligible). Write-awareness is inert *without* a router that makes the cross-alias write
    /// reach the aliased loan.
    ///
    /// **STATE-3: S2-6 CLOSED by NB4-R (2026-07-15).** The write's non-reach was diagnosed by dump:
    /// `*b=5` invalidates only b's own loan (`row(b)` keyed under b, empty of the loan x/z/q require,
    /// which is keyed under p). Three routers were refuted BEFORE NB4-R, each by a dump — recorded so
    /// none is re-attempted:
    ///   • 3c origins (subset edges) — invalidation is place-based, subset never changes a write's reach;
    ///   • `tree_borrow_local` copy-groups — singleton at round 0 (only unioned during demotion replay);
    ///   • `Local`-based issues→borrowed re-basing (NB4-4b `ffd90100`) — fixture-level closure but on
    ///     the corpus it CRASHED 3 programs (re-basing a projection across incompatible types) and
    ///     over-demoted −17.7% (offset conflation). REVERTED.
    /// WA is also refuted for this witness: the loan x/z/q require has base `p` which is Foster `Mut`
    /// (never skip-eligible) — routing alone flips it. NB4-R is the router that landed: **place-based
    /// cross-alias routing (before NB5) — compose-onto-`borrowed` algebra with a type-check + whole-cell
    /// fallback (no re-basing crash), `offset` excluded (no −17.7%), PRE-order bounded walk.** x/z/q
    /// now settle `Raw` in both mut modes; §8 is no longer the sole guard for this shape. (Corpus
    /// impact is measured at the NB4-R sweep gate.)
    #[test]
    fn nb2_cross_alias_write_uncaught_witness() {
        run_compiler(
            r#"
#[inline(never)]
unsafe fn id(mut p: *mut i32) -> *mut i32 { p }
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut b = p;
    let mut x = id(p);
    let mut z = x;
    let mut q = x;
    let r0 = *z + *q;
    *b = 5;
    let r1 = *z;
    r0 + r1
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let slot_of =
                    |name: &str| local_slot(&slots, f, local_by_var_name(tcx, f, name), 0);
                let local_of = |name: &str| local_by_var_name(tcx, f, name);

                let facts = MutFacts::from_program(&program);
                // x/z/q are read-only views (never written THROUGH) ⇒ Foster `Imm` ⇒ their loans
                // are skip-eligible at `invalidates.rs:73`. These ARE the real loan bases — the
                // point the earlier witness got wrong (it asserted a copy, not the loan base).
                for name in ["x", "z", "q"] {
                    assert!(
                        !facts.is_mutable(f, local_of(name)),
                        "`{name}` is a read-only view ⇒ Foster Imm ⇒ its loan is skip-eligible"
                    );
                }
                // `b` (= p) writes the cell x/z/q alias via `id` ⇒ Foster `Mut` (the writer).
                assert!(
                    facts.is_mutable(f, local_of("b")),
                    "`b` writes the aliased cell ⇒ Foster Mut (the cross-alias writer)"
                );

                let kind_of = |name: &str, mf_true: bool| {
                    let solver = KindSolver::new(&slots);
                    let (_s, selectors) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("emission");
                    add_coherence(&solver, &slots, f, &body);
                    let sid = slot_of(name);
                    if mf_true {
                        verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                            .expect("accepts")
                            .get(&sid)
                            .copied()
                    } else {
                        verify_to_fixpoint(&program, &slots, &solver, &selectors, &facts)
                            .expect("accepts")
                            .get(&sid)
                            .copied()
                    }
                };

                // §NB4-R STATE-3 (S2-6 CLOSED): place-based cross-alias routing lands and flips this
                // witness. `*b = 5` now ROUTES through `b`'s issued loan (`b = p`, borrowed=(*p)) to
                // `row(p)`, where the loan x/z/q require (the id-arg copy's main loan, borrowed=(*p),
                // keyed under `p`) lives — and invalidates it. x/z/q were the CALL-RETURN alias the
                // pre-routing engine's `row(b)`-empty lookup was blind to (state-2). They now settle
                // `Raw` in BOTH mut modes — the routed demotion does not depend on the mut-fact skip
                // (`p` is a `Mut` base, never skip-eligible) — so the state-2 mode differential
                // collapses. This is the executable proof that NB4-R closed S2-6.
                for name in ["x", "z", "q"] {
                    assert_eq!(
                        kind_of(name, true),
                        Some(SlotKind::Raw),
                        "forced-mut: `{name}`'s loan participates ⇒ Raw (unchanged from state-2)"
                    );
                    assert_eq!(
                        kind_of(name, false),
                        Some(SlotKind::Raw),
                        "fact-mut: `{name}` is now `Raw` — NB4-R routing reaches the call-return alias's \
                         loan on `(*p)` via `b`'s issued loan. S2-6 CLOSED here (was `Ref` in state-2)."
                    );
                }

                // The edge set is no longer a lone self-edge: routing adds a genuine cross-slot
                // conflict that demotes the view `z` (the CEGAR representative of the x/z/q alias
                // group) via a NON-self issuer — the concrete S2-6 closure witness. (The `b` self-edge
                // from `*b=5` on b's own cell persists alongside it.)
                let edges = revalidate_replaying(&program, &slots, |_| true, |_| false, &facts);
                let z_slot = slot_of("z");
                let fn_edges = edges.get(&f).map(Vec::as_slice).unwrap_or(&[]);
                assert!(
                    fn_edges
                        .iter()
                        .any(|e| e.requirers == vec![z_slot] && e.issuer != Some(z_slot)),
                    "state-3: a routed cross-alias edge must demote the view `z` via a non-self issuer \
                     (the S2-6 closure). Edges: {fn_edges:?}"
                );
            },
        );
    }

    /// §NB4-4c SCOPE GUARD: the demotion set is the interprocedural SIGNATURE boundary only
    /// (args/returns/fields, via `to_summary`), NEVER internal locals. An internal `Copy`/`Move` of an
    /// addr-of-local / `.offset` / plain / opaque-result pointer is body-level unknown but is NOT a
    /// signature slot, so it is not demoted — no promotion coverage is lost on intermediates. (This
    /// refutes the "source-less copies get hard `¬ref`" concern: those are internal locals.)
    #[test]
    fn nb4_4c_demotion_is_signature_boundary_only() {
        let cases: &[(&str, &str, &str)] = &[
            (
                "addrof_copy",
                "q",
                "fn f() { let mut x = 0i32; let p = &raw mut x; let q = p; unsafe { *q = 1; } }",
            ),
            (
                "offset_copy",
                "q",
                "unsafe fn f(p: *mut i32) { let r = p.offset(1); let q = r; let _ = q; }",
            ),
            (
                "plain_copy",
                "q",
                "unsafe fn f(p: *mut i32) { let q = p; let _ = q; }",
            ),
            (
                "opaque_result_local",
                "q",
                "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
              unsafe fn f(p: *mut i32) { let q = op(p); let _ = q; }",
            ),
        ];
        for (label, var, code) in cases {
            run_compiler(code, |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let set = collect_no_borrow_origin_slots(&origins, &slots);
                let local = local_by_var_name(tcx, f, var);
                let s0 = slots
                    .fn_local_slots
                    .get(&f)
                    .and_then(|u| u.slot_for_local_depth(local, 0))
                    .map(|id| SlotRef::Local(f, id));
                assert!(
                    !s0.map(|s| set.contains(&s)).unwrap_or(false),
                    "{label}: an internal local `{var}` must NOT be demoted (signature-boundary only)"
                );
            });
        }
    }

    /// §NB4-4c MARKER (§8-guarded — the Codex-F1 re-review residue, 2026-07-17). `summary.unknown`
    /// is a MAY-set, not an exclusive no-origin partition: a signature RETURN can carry BOTH a
    /// modeled borrow origin (`q = p`) AND a stale opaque may-definition (`q = op(p)`) that a later
    /// overwrite kills. Because the opaque def still MAY-reaches, the return lands in
    /// `collect_no_borrow_origin_slots`; the monotone `¬ref` demotes it, and copy-coherence drags the
    /// modeled-origin param `p` and the copy `q` to `Raw` too — COLLATERAL over-demotion of slots that
    /// have a real borrow origin. This is the strong-form failure of the NB4-4c "F1 refutation": the
    /// demotion is signature-boundary for DIRECT membership (an internal-only local is never in the
    /// set — see `nb4_4c_demotion_is_signature_boundary_only`), but a modeled-origin SIGNATURE slot
    /// CAN be, and coherence then spreads it.
    ///
    /// SOUNDNESS: this is COMPLETENESS-CLASS (precision), NOT unsoundness — `Ref → Raw` is the
    /// conservative direction (Raw is always memory-safe), the model still ACCEPTS, and BO output is
    /// unconsumed by codegen (§8). It FLIPS (`p` back to `Ref`, return out of the set) when the
    /// deferred "definitely-overwritten vs may-reach unknown-def" distinction lands (one bucket, gate
    /// = effect-row + opaque-interaction detection). Tripwire, not a regression.
    #[test]
    fn nb4_4c_marker_coherence_collateral_demotes_modeled_origin() {
        use rustc_middle::mir::RETURN_PLACE;
        // Control: pure modeled copy — return has ONLY a modeled origin, stays Ref (baseline).
        run_compiler(
            "unsafe fn f(p: *mut i32) -> *mut i32 { let q = p; q }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                let p0 = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
                assert!(
                    !collect_no_borrow_origin_slots(&origins, &slots).contains(&ret),
                    "control: a pure modeled-copy return must NOT be no-borrow-origin"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&p0),
                    Some(&SlotKind::Ref),
                    "control: modeled-origin p stays Ref"
                );
            },
        );
        // Mixed: q first opaque, then overwritten with modeled p, then returned. TODAY: the return is
        // in the set (may-set over-inclusion) and coherence collaterally demotes p to Raw.
        run_compiler(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; q }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                let p0 = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
                assert!(
                    collect_no_borrow_origin_slots(&origins, &slots).contains(&ret),
                    "TODAY: a modeled-origin return with a stale opaque may-def IS over-included \
                     (may-set); this flips when the overwrite-kill distinction lands"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&p0),
                    Some(&SlotKind::Raw),
                    "TODAY: coherence collaterally demotes the modeled-origin param p to Raw \
                     (conservative, §8-guarded); flips to Ref when the deferred fix lands"
                );
            },
        );
    }

    /// §NB4-4c-Q (Codex confirming pass, 2026-07-17): PIN the restored-output-param OUTCOME directly on
    /// `compute_origins` — the collector-output test (`overincl` 0/0) alone does not prove it. Records
    /// only the OBSERVED signature-level fact: the restore-after-opaque shape yields exactly one unknown
    /// slot and ZERO summary subset edges, so neither over-inclusion predicate can see it. The MECHANISM
    /// is deliberately NOT claimed: the earlier "poisoning drops the value-restore edge" explanation was
    /// refuted (`mark_unknown` only sets a bit; the store IS recorded), and a body-level
    /// `arg1@1 → old → arg1@1` path exists whose signature projection threads the internal local `old`.
    /// The precise reason the SIGNATURE summary carries no self-loop is untraced and belongs to item-4
    /// (the flow-sensitive analysis that will size this component-2 residual). This test guards the
    /// outcome the gate relies on (both predicates miss ⇒ summary-invisible-at-signature-level).
    #[test]
    fn nb4_4c_q_restored_summary_invisible() {
        run_compiler(
            "unsafe extern \"C\" { fn op() -> *mut i32; } \
             unsafe fn f(out: *mut *mut i32) { let old = *out; *out = op(); *out = old; }",
            |tcx| {
                let program = collect_program(tcx);
                let origins = compute_origins(&program);
                let f = function_by_name(&program, "f");
                let sum = &origins[&f];
                assert_eq!(
                    sum.unknown.count(),
                    1,
                    "restored: exactly one unknown signature slot"
                );
                let edges: usize = sum
                    .subset
                    .rows()
                    .map(|r| sum.subset.row(r).map_or(0, |b| b.iter().count()))
                    .sum();
                assert_eq!(
                    edges, 0,
                    "restored: ZERO summary subset edges — both over-inclusion predicates miss it \
                     (the summary-invisible OUTCOME; mechanism untraced, item-4's to pin)"
                );
            },
        );
    }

    /// §NB5-Z (2026-07-17): z3 determinism regression-guard. Two independent in-process BO solves of
    /// the same fixture must produce byte-identical models. This holds INHERENTLY in-process: z3 0.19's
    /// default `Context` is a `thread_local!` built ONCE per thread (`Context::new(&Config::new())`) and
    /// cloned/reused for the thread's life, so both solves share one random seed. So this is a
    /// determinism REGRESSION-GUARD, not a "fixed nondeterminism" RED (NB5-Z rider, correction #3). The
    /// z3 seed pin's real value is the cross-VERSION contract — the sweep-worker `set_global_param` plus
    /// the `z3_full_version` stamp — which a single-version suite cannot exercise, so this test does not
    /// claim to. It locks in-process determinism so a future solver/z3 change cannot silently reintroduce
    /// run-to-run drift.
    #[test]
    fn nb5z_solve_run_to_run_deterministic() {
        run_compiler(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; q }",
            |tcx| {
                let solve = || {
                    let program = collect_program(tcx);
                    let f = function_by_name(&program, "f");
                    let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                    let slots = CrateSlots::build(&program);
                    let crate_ctxt = CrateCtxt::new(&program);
                    let facts = MutFacts::from_program(&program);
                    let solver = KindSolver::new(&slots);
                    let (_s, sel) = emit_crate_ownership_constraints(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                    )
                    .expect("emission");
                    add_coherence(&solver, &slots, f, &body);
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts")
                };
                let m1 = solve();
                let m2 = solve();
                assert_eq!(
                    m1, m2,
                    "NB5-Z: two independent in-process solves must be identical (determinism guard)"
                );
            },
        );
    }

    /// §NB4-4c-Q RED (item-4 sizing gate, 2026-07-17): the coherence-collateral measurement, validated
    /// against the INDEPENDENT multi-agent derivation (user ruling 2026-07-17). Exercises the EXACT
    /// harness code (`bo_c1::measure_collateral`) the corpus sweep runs.
    ///
    /// GRANULARITY (user-ruled MIR-slot-level 2026-07-17): the collateral is measured in the `n_ref` /
    /// `n_ref_d0` metric's own units — MIR SLOTS, not source variables. The agents' source-variable
    /// derivation (Sh1=3, Sh3=4) is right at its granularity; the metric adds the coherence-equated MIR
    /// COPY-TEMPS (`_3` the `op(p)` arg copy, `_4` the call-result temp → +2 on copy-chain shapes). The
    /// gate ratio's denominator (corpus `n_ref_d0`) counts these temps too, so the ratio is honest — but
    /// per-program outlier inspection must remember temps inflate the raw copy-chain counts. Sh4 has no
    /// +2 because the depth-0 field-store equate skip (`coherence.rs:45-47`) blocks the drag.
    #[test]
    fn nb4_4c_q_collateral_shapes() {
        fn measure(code: &str) -> crate::bo_c1::CollateralMeasurement {
            let mut out = None;
            run_compiler(code, |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let origins = compute_origins(&program);
                let mut_facts = MutFacts::from_program(&program);
                out = Some(crate::bo_c1::measure_collateral(
                    &program, &slots, &origins, &mut_facts,
                ));
            });
            out.expect("run_compiler ran the callback")
        }
        // Shape 1: definitely-overwritten copy. coherence chain p≡q≡return (2 equates, 3 slots).
        let s1 = measure(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; q }",
        );
        assert_eq!(s1.status, "ok", "Shape 1: solved");
        assert_eq!(
            s1.overincl_mit, 1,
            "Shape 1: over-inclusion (mitigated) = 1 (the return)"
        );
        // MIR-slot-level = source view (3: p,q,return) + arg/result copy-temps (2: _3,_4) = 5.
        assert_eq!(s1.collateral_mit, 5, "Shape 1: collateral = 5 (MIR slots)");
        assert_eq!(
            s1.collateral_upper, 5,
            "Shape 1: upper == mit (no restored/storage extra here)"
        );
        // Shape 3: 2-hop copy chain (+r=q). Drag SCALES with chain length: source view 4 + 2 temps = 6.
        let s3 = measure(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { let mut q = op(p); q = p; let r = q; r }",
        );
        assert_eq!(s3.overincl_mit, 1, "Shape 3: over-inclusion = 1");
        assert_eq!(s3.collateral_mit, 6, "Shape 3: collateral = 6 (MIR slots)");
        // Shape 4: field store. coherence.rs:45-47 skips the depth-0 field-store equate → NO drag onto
        // p; field collateral shows in n_ref (=1) but is INVISIBLE in n_ref_d0 (=0).
        let s4 = measure(
            "#[repr(C)] pub struct S { pub g: *mut i32 } \
             unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(s: *mut S, p: *mut i32) { (*s).g = op(p); (*s).g = p; }",
        );
        assert_eq!(
            s4.overincl_mit, 1,
            "Shape 4: over-inclusion = 1 (the field)"
        );
        assert_eq!(s4.collateral_mit, 1, "Shape 4: collateral = 1 (n_ref)");
        assert_eq!(
            s4.collateral_d0_mit, 0,
            "Shape 4: collateral_d0 = 0 (field slots are invisible at depth-0)"
        );
        // Shape 2: branch-join. Predicate FIRES identically to Shape 1 (flow-insensitive), but the
        // demotion is LEGITIMATE — MINUS un-demoting it reinstates an unsound Ref. THIS IS THE PROOF
        // that MINUS is MEASUREMENT-ONLY and must never ship; item-4's definitely-overwritten kill
        // would NOT fire here.
        let s2 = measure(
            "unsafe extern \"C\" { fn op(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32, c: bool) -> *mut i32 { let q = if c { op(p) } else { p }; q }",
        );
        assert_eq!(
            s2.overincl_mit, 1,
            "Shape 2: predicate FIRES (measurement-only; MINUS must not ship)"
        );
        assert_eq!(
            s2.collateral_mit, 4,
            "Shape 2: collateral = 4 (MIR slots). MINUS un-demoting this is UNSOUND — the `op(p)` branch \
             can return opaque memory at runtime; the shippable item-4 kill would NOT fire on a branch-join."
        );
        // SECOND measurement-only witness (the "_4 tell", user-noted 2026-07-17): in Shape 1 the flipping
        // set includes `_4`, the OPAQUE-RESULT temp — under MINUS it becomes `Ref`, which is itself
        // unsound. So even the direct copy shape carries an unsound-under-MINUS slot; MINUS is a sizing
        // measurement only, never a shippable demotion set (Shape 2 is the other witness).
        // Counterexample (amendment 1): the storage-alias false positive. `&raw mut p` makes the return
        // pointee alias `p`'s storage — a SYMMETRIC subset edge whose true (opaque) source is filtered
        // out of `unknown`, so RAW fires but MITIGATED (reverse-edge discard) does NOT. Guards the
        // predicate against storage-edge inflation.
        let cx = measure(
            "unsafe extern \"C\" { fn op() -> *mut i32; } \
             unsafe fn f(mut p: *mut i32) -> *mut *mut i32 { p = op(); &raw mut p }",
        );
        assert!(
            cx.overincl_raw >= 1,
            "counterexample: RAW predicate fires via the storage edge"
        );
        assert_eq!(
            cx.overincl_mit, 0,
            "counterexample: MITIGATED predicate must NOT fire (symmetric storage edge discarded)"
        );
        assert!(
            cx.overincl_upper >= 1,
            "counterexample: UPPER bound DOES catch it (any incoming edge, self/symmetric-inclusive)"
        );
        // RESTORED-OUTPUT-PARAM (Codex F1 + confirming pass, 2026-07-17 — component-2 residual): `*out`
        // is restored to its original value after an opaque overwrite. OBSERVED signature-level outcome
        // (pinned by `nb4_4c_q_restored_summary_invisible`): exactly one unknown slot and ZERO summary
        // subset edges, so NEITHER the mitigated NOR the upper predicate sees it (both 0). The MECHANISM
        // is NOT claimed — the earlier "poisoning drops the store" explanation was REFUTED (`mark_unknown`
        // only sets a bit; the store is recorded); the reason the `arg1@1→old→arg1@1` body path leaves no
        // SIGNATURE self-loop is untraced and belongs to item-4. (Contrast the storage counterexample
        // above: an ADDRESS alias survives to `to_summary`, so `upper` DOES catch that — value-restore
        // vs address-alias.) The gate's `collateral_upper` sizes only the summary-VISIBLE collateral;
        // this component-2 case is UNMEASURED at the summary level (COMPLETENESS — test-only, unconsumed,
        // conservative Ref→Raw; NOT asserted empirically rare) and carried to item-4's RED scope.
        let restored = measure(
            "unsafe extern \"C\" { fn op() -> *mut i32; } \
             unsafe fn f(out: *mut *mut i32) { let old = *out; *out = op(); *out = old; }",
        );
        assert_eq!(
            restored.overincl_mit, 0,
            "restored: mitigated misses it (no summary edge)"
        );
        assert_eq!(
            restored.overincl_upper, 0,
            "restored: UPPER also misses it — SUMMARY-INVISIBLE (poisoning drops the value restore); \
             this component-2 residual is item-4 territory, not sizable at the summary level"
        );
        assert_eq!(
            restored.status, "no-oi",
            "restored: no summary over-inclusion → no solve"
        );
    }

    // ---- §NB4-4c — MAY-SUPPLY DEMOTION over the NO-BORROW-ORIGIN set ----
    //
    // These were the §NB3-3c-ii NB4-boundary markers. NB4-4c lands the **may-supply demotion**: a
    // monotone `¬ref` on every NO-BORROW-ORIGIN slot (`collect_no_borrow_origin_slots`, base
    // signature slots + struct fields), wired into `emit_crate_ownership_constraints` (was:
    // marker-tests-only).
    //
    // KEY CONCEPT (dump-corrected 2026-07-16): `summary.unknown` is "NO-BORROW-ORIGIN", NOT
    // "opaque-poisoned". A slot lands there when its value has no trackable *borrow* origin — an
    // opaque-callee RESULT, OR a freshly-`malloc`'d OWNED pointer. The `malloc_only` vs `malloc_opaque`
    // ablation proves `opaque(out)` adds nothing to the set. So `¬ref`-ONLY (not `¬ref ∧ ¬own`, which
    // over-demoted owned transfers — 9 tests): it is SELF-DISCRIMINATING — an owned slot keeps
    // `Owning` (source selector), an opaque RESULT loses `Ref` → `Raw`.
    //
    // Two markers pin DEFERRED §8-guarded hazards (flip when opaque-INTERACTION detection lands, one
    // bucket): `nb4_4c_marker_may_overwrite_owning_today` (owned out@1 an opaque callee may overwrite)
    // and `nb4_4c_marker_depth0_arg_retention_open` (depth-0 arg an opaque callee may retain). The
    // GREEN tests below encode the may-supply FIX (opaque results → Raw); the controls stay `Ref`.

    /// §NB4-4c (MAY-SUPPLY): an opaque-callee-RESULT RETURN is a NO-BORROW-ORIGIN slot and is DEMOTED
    /// to **`Raw`** by the monotone `¬ref` — the FFI-edition S2-6 fix (a shared `&T` over unknown
    /// C-state the callee may retain + write is now forbidden). No owning source reaches it (opacity
    /// breaks the link), so `¬ref` settles it `Raw`.
    #[test]
    fn nb4_4c_no_origin_return_demoted_to_raw() {
        run_compiler(
            "unsafe extern \"C\" { fn opaque_dup(p: *mut i32) -> *mut i32; } \
             unsafe fn f(p: *mut i32) -> *mut i32 { opaque_dup(p) }",
            |tcx| {
                use rustc_middle::mir::RETURN_PLACE;
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                assert!(
                    collect_no_borrow_origin_slots(&origins, &slots).contains(&ret),
                    "opaque-return must be no-borrow-origin (the hazard the 4c demotion targets)"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&ret),
                    Some(&SlotKind::Raw),
                    "NB4-4c: no-borrow-origin may-supply return must be demoted to Raw (¬ref)"
                );
            },
        );
    }

    /// §NB4-4c (negative control + PURE-READ RESIDUAL): a KNOWN provenance-preserving callee
    /// (`.offset`) has a borrow origin, so its return legitimately stays `Ref` — the demotion must leave
    /// it alone. Green before AND after 4c (the boundary gates WHO gets demoted).
    #[test]
    fn nb4_4c_known_callee_not_demoted_stays_ref() {
        run_compiler(
            "unsafe fn f(p: *mut i32) -> *mut i32 { p.offset(1) }",
            |tcx| {
                use rustc_middle::mir::RETURN_PLACE;
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                assert!(
                    !collect_no_borrow_origin_slots(&origins, &slots).contains(&ret),
                    "known provenance-preserving `.offset` must NOT poison f's return (no 4c demotion)"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&ret),
                    Some(&SlotKind::Ref),
                    "NB4-4c: an origin-carrying `.offset` return must stay Ref (demotion must not over-reach)"
                );
            },
        );
    }

    /// §NB4-4c (PURE-READ RESIDUAL): a `*mut i32` param only READ through (`*p`) is NOT a
    /// no-borrow-origin slot and stays `Ref` — the demotion must never touch an ordinary read-only
    /// pointer. Green throughout.
    #[test]
    fn nb4_4c_pure_read_preserves_ref() {
        run_compiler("unsafe fn f(p: *mut i32) -> i32 { *p }", |tcx| {
            let program = collect_program(tcx);
            let f = function_by_name(&program, "f");
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            let slots = CrateSlots::build(&program);
            let crate_ctxt = CrateCtxt::new(&program);
            let origins = compute_origins(&program);
            let facts = MutFacts::from_program(&program);
            let p0 = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
            assert!(
                !collect_no_borrow_origin_slots(&origins, &slots).contains(&p0),
                "a read-only param must NOT be a no-borrow-origin slot"
            );
            let solver = KindSolver::new(&slots);
            let (_s, sel) = emit_crate_ownership_constraints(
                &crate_ctxt,
                &slots,
                &compute_origins(&program),
                &solver,
            )
            .expect("emission");
            add_coherence(&solver, &slots, f, &body);
            let m = verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
            assert_eq!(
                m.get(&p0),
                Some(&SlotKind::Ref),
                "NB4-4c: a purely-read param must stay Ref (pure-read residual)"
            );
        });
    }

    /// §NB4-4c MARKER (§8-guarded — the DEFERRED depth-0-arg retention gap, ruled 2026-07-16): a
    /// direct depth-0 `*mut T` arg to a genuinely-opaque callee stays UN-DEMOTED (`Ref`) today. base
    /// (lifetime_flow unknown-targets) does NOT poison it — pure-read externs are correctly left
    /// alone, which is why the seed-size dump showed a blanket depth-0 extension is a firehose (~21k
    /// args, ~all pure-read: __assert_fail/printf/fprintf/str/mem). The sound-AND-precise extension
    /// is deferred to a boundary-table effect-row expansion (fragment-F/§6.4 gap + backlog; sizing =
    /// tier-2 dump, harness `CRAT_BOC1_SEED_SIZE`). This pins the OPEN behavior: if `opaque_take`
    /// RETAINS `p` and later writes `*p`, a surviving `Ref` is unsound (§8-guarded, BO unconsumed).
    /// It FLIPS to `Raw` when the effect-row-paired extension lands — a tripwire, not a regression.
    #[test]
    fn nb4_4c_marker_depth0_arg_retention_open() {
        run_compiler(
            "unsafe extern \"C\" { fn opaque_take(p: *mut i32); } \
             unsafe fn f(p: *mut i32) { opaque_take(p); }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let p0 = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
                assert!(
                    !collect_no_borrow_origin_slots(&origins, &slots).contains(&p0),
                    "base must NOT poison a depth-0 arg to an opaque callee (the deferred gap)"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&p0),
                    Some(&SlotKind::Ref),
                    "§8-guarded OPEN gap: depth-0 arg retention un-demoted today; flips to Raw when \
                     the effect-row-paired depth-0 extension lands"
                );
            },
        );
    }

    /// §NB4-4c (FIELD coverage — the F2 field extension, LANDED this row per the seed-size ruling):
    /// a struct pointer field that receives opaque-callee provenance is a no-borrow-origin slot and
    /// DEMOTED to `Raw`. Drops the `field.is_some()` seed skip and maps the signature field slot to
    /// its kind `SlotRef::Field` via `slot_for_field_depth`. NB the field slot is crate-wide
    /// flow-insensitive, so this is a GLOBAL demotion (consistent with the existing field model).
    #[test]
    fn nb4_4c_no_origin_field_demoted_to_raw() {
        run_compiler(
            "struct S { p: *mut i32 } \
             unsafe extern \"C\" { fn opaque_dup(p: *mut i32) -> *mut i32; } \
             unsafe fn f(s: *mut S, q: *mut i32) { (*s).p = opaque_dup(q); }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let s_did = struct_by_name(&program, "S");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                // Fixture validity, independent of the seed's field-skip: a field slot IS no-borrow-origin.
                assert!(
                    origins.values().any(|su| su
                        .unknown
                        .iter()
                        .any(|sl| su.slots[sl].place.field.is_some())),
                    "fixture must poison a struct-field slot"
                );
                let field = StructFieldSlot {
                    struct_did: s_did,
                    field_index: 0,
                };
                let fslot = slots
                    .field_slots
                    .slot_for_field_depth(field, 0)
                    .expect("field S::p depth-0 kind slot");
                let fref = SlotRef::Field(fslot);
                let solver = KindSolver::new(&slots);
                let (_s, sel) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&fref),
                    Some(&SlotKind::Raw),
                    "NB4-4c: a no-borrow-origin struct-field slot must be demoted to Raw (field skip dropped)"
                );
            },
        );
    }

    /// §NB4-4c MARKER (§8-guarded — the DEFERRED may-OVERWRITE hazard, ruled 2026-07-16): `out@1`
    /// (`*out = malloc()` then `opaque(out)`) holds owned heap and is in the NO-BORROW-ORIGIN set, so
    /// it settles **`Owning` today** — unchanged by the may-supply `¬ref` (which leaves an owned slot
    /// `Owning`). If `opaque` overwrites `*out` with foreign memory, codegen dropping the "owned" slot
    /// is a UAF. This hazard is NOT targetable from `summary.unknown`: the `malloc_only` vs
    /// `malloc_opaque` ablation proves `opaque(out)` adds nothing to the set, so a `¬own` here cannot
    /// tell it apart from a SAFE `*out = malloc()` (which must stay `Owning` — `store_through_ptr_*`).
    /// It DEFERS to the effect-row/opaque-interaction bucket (with depth-0). Pins `Owning`; FLIPS to
    /// `Raw` when overwrite detection lands — a tripwire, not a regression.
    #[test]
    fn nb4_4c_marker_may_overwrite_owning_today() {
        run_compiler(
            "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; fn opaque(out: *mut *mut i32); } \
             unsafe fn f(out: *mut *mut i32) { *out = malloc(core::mem::size_of::<i32>()); opaque(out); }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let facts = MutFacts::from_program(&program);
                let out1 = local_slot(&slots, f, local_by_var_name(tcx, f, "out"), 1);
                assert!(
                    collect_no_borrow_origin_slots(&origins, &slots).contains(&out1),
                    "the out-param pointee is in the no-borrow-origin set (owned heap, no borrow origin)"
                );
                let solver = KindSolver::new(&slots);
                let (_s, sel) =
                    emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                        .expect("emission");
                add_coherence(&solver, &slots, f, &body);
                let m =
                    verify_to_fixpoint(&program, &slots, &solver, &sel, &facts).expect("accepts");
                assert_eq!(
                    m.get(&out1),
                    Some(&SlotKind::Owning),
                    "§8-guarded: owned out@1 stays Owning under may-supply ¬ref; the may-overwrite \
                     demotion is DEFERRED (opaque overwrite is not in the no-borrow-origin set)"
                );
            },
        );
    }

    /// §NB4-4c white-box: `KindSolver::add_owning_exclusion(slot)` forbids `Owning` — the CONTRACT of
    /// the deferred may-overwrite tool (rider 3, kept warm in place of `allow(dead_code)`). On a lone
    /// `malloc`-source return (which settles `Owning` under the may-supply `¬ref`), adding `¬own` makes
    /// the retractable source selector LEAK under relaxation → the slot settles `Raw`, never `Owning`,
    /// and never a hard decline.
    #[test]
    fn nb4_4c_add_owning_exclusion_forbids_owning() {
        run_compiler(
            "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; } \
             unsafe fn f() -> *mut i32 { malloc(4) }",
            |tcx| {
                use rustc_middle::mir::RETURN_PLACE;
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let ret = local_slot(&slots, f, RETURN_PLACE, 0);
                let solver = KindSolver::new(&slots);
                let (_s, sel) =
                    emit_crate_ownership_constraints(&crate_ctxt, &slots, &origins, &solver)
                        .expect("emission");
                // Baseline (may-supply `¬ref` already applied): the malloc'd return settles Owning.
                let base = solver.model_kinds_relaxing(&sel).expect("sat");
                assert_eq!(
                    base.get(&ret),
                    Some(&SlotKind::Owning),
                    "baseline: a malloc-source return is Owning under ¬ref-only"
                );
                // `¬own` forbids Owning → the source selector leaks → Raw (non-Owning), not a decline.
                solver.add_owning_exclusion(ret);
                let m = solver
                    .model_kinds_relaxing(&sel)
                    .expect("relaxed accept, NOT a decline");
                assert_eq!(
                    m.get(&ret),
                    Some(&SlotKind::Raw),
                    "¬own must force non-Owning; on a malloc source it leaks → Raw"
                );
            },
        );
    }

    // ================= §NB4-4a — call-site semantics: A′ (live-requirer discharge) =================
    //
    // RULED 2026-07-12 after a borrow-STRUCTURE DUMP refuted the "the destination has no loan"
    // premise (that claim was inferred from one code site and was FALSE; the dump standard exists
    // because of it). What the dump actually shows for every shape below:
    //
    //     LOAN L_(0) borrowed=(*p) assigned=Assign(<arg temp>)   ← the call's arg-temp copy
    //     REQUIRES   x → [L_(0)]                                  ← x ALREADY requires it
    //     ERROR      L_(0) live ∧ invalidated                     ← already an error
    //     EDGE       issuer=<arg temp> requirers=[x]
    //
    // So the loan, the requirement, and the error all already exist. The bug is the DISCHARGE MENU:
    // Mode-A's `representative` prefers the ISSUER, so the arg temp (≡ `p`) is demoted and the live
    // requirer `x` survives as a `Ref` aliasing a cell written through a now-`Raw` sibling.
    //
    // A′ PRINCIPLE: demoting a slot discharges an edge only if it removes the CONFLICT, not the
    // REQUIREMENT. An edge with live `Ref` requirers BEYOND the issuer is discharged by
    // `⋁¬ref(live requirers)`; the issuer stays in the menu only when no such requirer exists.
    // (This RESTRICTS the commit menu — it adds no new assertion kind, so §3 invariant 7 holds.)

    /// §NB4-4a helper — solve `f` to fixpoint under fact-driven mutability; return each named
    /// local's depth-0 accepted kind + its Foster mutability.
    fn nb4_accept<'tcx>(
        tcx: TyCtxt<'tcx>,
        program: &RustProgram<'tcx>,
        fn_name: &str,
        names: &[&str],
    ) -> Vec<(Option<SlotKind>, bool)> {
        let f = function_by_name(program, fn_name);
        let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        let slots = CrateSlots::build(program);
        let crate_ctxt = CrateCtxt::new(program);
        let facts = MutFacts::from_program(program);
        let solver = KindSolver::new(&slots);
        let (_s, sel) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("emission");
        add_coherence(&solver, &slots, f, &body);
        let model = verify_to_fixpoint(program, &slots, &solver, &sel, &facts).expect("accepts");
        names
            .iter()
            .map(|n| {
                let l = local_by_var_name(tcx, f, n);
                let slot = local_slot(&slots, f, l, 0);
                (model.get(&slot).copied(), facts.is_mutable(f, l))
            })
            .collect()
    }

    /// S1 helper: solve the ordinary Mode-A path and return its accepted model.
    /// The caller owns the semantic assertion so the premise control and
    /// coverage contrasts all exercise the same setup.
    fn s1_accept_model(
        program: &RustProgram<'_>,
        f: LocalDefId,
    ) -> (CrateSlots, FxHashMap<SlotRef, SlotKind>) {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(f)
            .borrow();
        let slots = CrateSlots::build(program);
        let crate_ctxt = CrateCtxt::new(program);
        let facts = MutFacts::from_program(program);
        let solver = KindSolver::new(&slots);
        let (_stats, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(program),
            &solver,
        )
        .expect("S1 ownership emission");
        add_coherence(&solver, &slots, f, &body);
        let model = verify_to_fixpoint(program, &slots, &solver, &selectors, &facts)
            .expect("S1 fixture must reach a Mode-A acceptance");
        assert!(
            model_accepts(program, &slots, &model, &facts),
            "the model returned by Mode-A must be accepted by the same oracle"
        );
        (slots, model)
    }

    fn s1_all_ref_model(slots: &CrateSlots) -> FxHashMap<SlotRef, SlotKind> {
        let mut model = FxHashMap::default();
        for index in 0..slots.field_slots.len() {
            model.insert(SlotRef::Field(SlotId::from_usize(index)), SlotKind::Ref);
        }
        for (&did, universe) in &slots.fn_local_slots {
            for index in 0..universe.len() {
                model.insert(
                    SlotRef::Local(did, SlotId::from_usize(index)),
                    SlotKind::Ref,
                );
            }
        }
        model
    }

    /// S1 premise control: `q = p` creates a loan on `*p`, then the bare
    /// assignment `p = other` kills it.  Rust accepts the same-lifetime
    /// reference lowering while `q` remains live: replacing the reference
    /// local does not access the old pointee, which remains borrowed through
    /// `q`.  The kill is therefore the correct boundary, not a missed error.
    #[test]
    #[ignore = "S1 premise control: run explicitly with the coverage investigation"]
    fn s1_loan_kill_plain_overwrite_is_valid_ref_replacement() {
        run_compiler(
            "#[allow(unused_assignments)] \
             fn lowered<'a>(mut p: &'a mut i32, other: &'a mut i32) -> i32 { \
                 let q = &mut *p; *q = 1; p = other; *q \
             } \
             unsafe fn f(mut p: *mut i32, other: *mut i32) -> i32 { \
                 let q = p; *q = 1; p = other; *q \
             }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let (slots, model) = s1_accept_model(&program, f);
                let p = local_slot(&slots, f, p, 0);
                let q = local_slot(&slots, f, q, 0);
                eprintln!(
                    "S1 plain accepted kinds: p={:?} q={:?}",
                    model.get(&p),
                    model.get(&q)
                );
                assert_eq!(
                    (model.get(&p), model.get(&q)),
                    (Some(&SlotKind::Ref), Some(&SlotKind::Ref)),
                    "Rust accepted the explicit same-lifetime reference lowering in this same \
                     crate; Mode A should preserve the valid Ref/Ref replacement shape"
                );
            },
        );
    }

    /// S1 C-idiomatic variant.  Unlike the plain overwrite, the right-hand side
    /// reads through `p`; the existing deep-access path may catch this before
    /// the destination assignment kills loans rooted at `p`.
    #[test]
    #[ignore = "S1 boundary fixture: run explicitly with the coverage investigation"]
    fn s1_loan_kill_c_next_overwrite_must_reject_all_ref_model() {
        run_compiler(
            "#[repr(C)] struct Node { next: *mut Node, value: i32 } \
             unsafe fn f(mut p: *mut Node) -> i32 { \
                 let q = p; (*q).value = 1; p = (*p).next; (*q).value \
             }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let (slots, model) = s1_accept_model(&program, f);
                let p = local_slot(&slots, f, p, 0);
                let q = local_slot(&slots, f, q, 0);
                eprintln!(
                    "S1 C-next accepted kinds: p={:?} q={:?}",
                    model.get(&p),
                    model.get(&q)
                );
                let all_ref = s1_all_ref_model(&slots);
                let facts = MutFacts::from_program(&program);
                assert!(
                    !model_accepts(&program, &slots, &all_ref, &facts),
                    "the C-style dereferenced RHS must invalidate q's required loan before kill"
                );
            },
        );
    }

    /// S1 negative control: without the reassignment of the borrowed source,
    /// the pointer copy and exclusive use through `q` are a valid reborrow.
    #[test]
    #[ignore = "S1 negative control: run explicitly with the coverage investigation"]
    fn s1_loan_kill_no_overwrite_control_stays_accepted() {
        run_compiler(
            "unsafe fn f(p: *mut i32) -> i32 { let q = p; *q = 1; *q }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let (slots, model) = s1_accept_model(&program, f);
                eprintln!(
                    "S1 control accepted kinds: p={:?} q={:?}",
                    model.get(&local_slot(&slots, f, p, 0)),
                    model.get(&local_slot(&slots, f, q, 0))
                );
                let all_ref = s1_all_ref_model(&slots);
                let facts = MutFacts::from_program(&program);
                assert!(
                    model_accepts(&program, &slots, &all_ref, &facts),
                    "control: without a source overwrite the all-Ref reborrow remains valid"
                );
                assert_eq!(
                    (
                        model.get(&local_slot(&slots, f, p, 0)),
                        model.get(&local_slot(&slots, f, q, 0)),
                    ),
                    (Some(&SlotKind::Ref), Some(&SlotKind::Ref)),
                    "control: the no-overwrite reborrow should remain accepted as Ref/Ref"
                );
            },
        );
    }

    /// S1 nearest-shape contrast: if the use after `p = other` writes through
    /// `q`, the current provenance/`requires` routing rejects the all-Ref
    /// model even though Rust accepts the same-lifetime reference lowering.
    /// This is a conservative compensation, not evidence that the bare kill
    /// should have been an error.
    #[test]
    #[ignore = "S1 routing contrast: run explicitly with the coverage investigation"]
    fn s1_post_overwrite_write_routing_is_conservative() {
        run_compiler(
            "#[allow(unused_assignments)] \
             fn lowered<'a>(mut p: &'a mut i32, other: &'a mut i32) -> i32 { \
                 let q = &mut *p; p = other; *q = 1; *q \
             } \
             unsafe fn f(mut p: *mut i32, other: *mut i32) -> i32 { \
                 let q = p; p = other; *q = 1; *q \
             }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let (slots, model) = s1_accept_model(&program, f);
                let p = local_slot(&slots, f, p, 0);
                let q = local_slot(&slots, f, q, 0);
                eprintln!(
                    "S1 post-write accepted kinds: p={:?} q={:?}",
                    model.get(&p),
                    model.get(&q)
                );
                let all_ref = s1_all_ref_model(&slots);
                let facts = MutFacts::from_program(&program);
                assert!(
                    !model_accepts(&program, &slots, &all_ref, &facts),
                    "current boundary: provenance/requirements reject all-Ref after q writes"
                );
            },
        );
    }

    /// S1 tree-grouping contrast: force `p` Raw in replay.  Its earlier invalid
    /// loan unions `p` with `r`; rebuilding `q = p` must then add the existing
    /// bare group-member loan on `r`, so `r = other` surfaces a conflict owned
    /// and required by `q` even though the copy arm still skips bare `p`.
    #[test]
    #[ignore = "S1 grouping contrast: run explicitly with the coverage investigation"]
    fn s1_tree_group_member_contrast_catches_sibling_overwrite() {
        run_compiler(
            "unsafe fn f(mut r: *mut i32, other: *mut i32) -> i32 { \
                 let p = r; *r = 1; let q = p; r = other; *q = 2; *q \
             }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let slots = CrateSlots::build(&program);
                let p_slot = local_slot(&slots, f, p, 0);
                let q_slot = local_slot(&slots, f, q, 0);
                let conflicts = revalidate_replaying(
                    &program,
                    &slots,
                    |slot| slot != p_slot,
                    |slot| slot == p_slot,
                    true,
                );
                assert!(
                    conflicts
                        .get(&f)
                        .is_some_and(|edges| edges.iter().any(|edge| {
                            edge.issuer == Some(q_slot) || edge.requirers.contains(&q_slot)
                        })),
                    "tree-group replay must catch the sibling overwrite through q's bare group \
                     member loan; got {conflicts:?}"
                );
            },
        );
    }

    const NB4_ID: &str = "#[inline(never)] unsafe fn id(q: *mut i32) -> *mut i32 { q } ";

    /// §NB4-4a-ii — pins the six-class pointee-effect SCHEMA and the ONE `Role → Effect` mapping
    /// (rider 5: stated once; 4c consumes it unmodified). The gate that would have consumed
    /// `no-access` at invalidation time was refuted (see `nb4_no_deref_callee_still_conflicts`);
    /// the SCHEMA survives because 4c's `unknown` demotion is defined over these classes. This
    /// test keeps the mapping honest until then — it is the schema's only consumer.
    #[test]
    fn nb4_effect_schema_role_mapping() {
        use crate::analyses::borrow_ownership::boundary_table::{Effect, Role, role_effects};
        // The bottom class is exactly the roles that never touch the pointee.
        for r in [Role::Ignore, Role::Lend, Role::NullConstructor] {
            assert_eq!(
                role_effects(r),
                [Effect::NoAccess],
                "{r:?} must be no-access"
            );
        }
        // Every other role touches the pointee (read/write/free/reborrow) — never no-access.
        for r in [
            Role::Source,
            Role::Sink,
            Role::FlowTransfer,
            Role::LoanCreating,
            Role::ProvenanceFlow,
            Role::FlowSuppression,
        ] {
            assert!(
                !role_effects(r).contains(&Effect::NoAccess),
                "{r:?} accesses the pointee and must NOT be no-access"
            );
        }
        // The two effect classes 4c gates on are represented where expected.
        assert!(
            role_effects(Role::Sink).contains(&Effect::MayOverwrite),
            "free ⇒ may-overwrite"
        );
        assert!(
            role_effects(Role::Source).contains(&Effect::MaySupply),
            "alloc ⇒ may-supply"
        );
    }

    // ===== §NB4-4a NAMED RESIDUAL — "unmodeled call-boundary materialization" =====
    // (raw caller arg → `Ref` callee param.)
    //
    // Surfaced by 4a-i's WIDENED §0.1 residual-model probe. **PRE-EXISTING**: both markers below
    // hold identically before A′, so A′ neither introduces nor regresses this class — the probe
    // only made it visible.
    //
    // STATUS: accepted for this pass, **§8-guarded** (BO output is unconsumed by codegen). It is
    // NOT proven safe and no safety is claimed here. A `Ref` callee param reached from a `Raw`
    // caller arg forces the rewriter to materialize `&mut *p` at the call. That materialized
    // reborrow is never modeled: its issuer (the arg temp) is `Raw`, and a `Raw` local issues no
    // loan in the replay, so no loan exists to check. This is a **LOAN-CREATION GAP** (plan
    // fragment-F / §6.4 list: OPEN).
    //
    // MECHANISM OWNERSHIP: the candidate fix ("retain the loan when the callee param is `Ref`
    // though the caller arg is `Raw`") is ENTANGLED with the F2 copy-group routing redesign — a
    // materialized loan is inert without routing, because the invalidating access is keyed under a
    // different `Local` (the same `local_map` blindness). Investigation is assigned to **4b's
    // micro-plan**, alongside routing; the homing decision is made there, with dumps.

    /// MARKER — raw caller arg → `Ref` callee param, unmodeled. `f`'s whole cluster is correctly
    /// `Raw` under A′, yet `id`'s PARAM settles `Ref`, so the call must materialize `&mut *p` from
    /// a raw pointer. §8-guarded; must flip when the materialized reborrow is modeled.
    #[test]
    fn nb4_marker_raw_arg_ref_param_unmodeled() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let x = id(p); *x = 1; let b = p; *b = 2; *x }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let caller = nb4_accept(tcx, &program, "f", &["x", "p", "b"]);
                let sig = nb4_accept(tcx, &program, "id", &["q"]);
                for (n, k) in [("x", caller[0].0), ("p", caller[1].0), ("b", caller[2].0)] {
                    assert_eq!(k, Some(SlotKind::Raw), "A′: caller-side `{n}` is Raw");
                }
                assert_eq!(
                    sig[0].0,
                    Some(SlotKind::Ref),
                    "TODAY `id.q` settles `Ref` while every caller-side slot is `Raw` — the call \
                     materializes `&mut *p` from a raw pointer and that reborrow is UNMODELED \
                     (§8-guarded). Must flip when the materialized loan is modeled."
                );
            },
        );
    }

    /// MARKER (the SHARPEST instance) — **two aliasing args, both `Ref`**. `id2(p, p)` passes the
    /// same raw pointer twice into a callee whose params BOTH settle `Ref`, so the call site
    /// materializes **two overlapping `&mut` to one cell**. That is UB at materialization — no
    /// during-call write is even required. Accepted today; §8-guarded.
    #[test]
    fn nb4_marker_two_aliasing_args_both_ref() {
        run_compiler(
            "#[inline(never)] unsafe fn id2(a: *mut i32, b: *mut i32) -> i32 \
             { *a = 1; *b = 2; *a } \
             unsafe fn f(p: *mut i32) -> i32 { id2(p, p) }",
            |tcx| {
                let program = collect_program(tcx);
                let callee = nb4_accept(tcx, &program, "id2", &["a", "b"]);
                let caller = nb4_accept(tcx, &program, "f", &["p"]);
                assert_eq!(caller[0].0, Some(SlotKind::Raw), "the caller's `p` is Raw");
                assert_eq!(
                    (callee[0].0, callee[1].0),
                    (Some(SlotKind::Ref), Some(SlotKind::Ref)),
                    "TODAY both params of `id2` settle `Ref` while the sole caller passes ONE raw \
                     pointer to both — the call materializes two overlapping `&mut` to the same \
                     cell (UB at materialization). §8-guarded; must flip when the materialized \
                     loans are modeled."
                );
            },
        );
    }

    /// §NB4-4a RED (c) — **returned borrow vs base mutation.** `x = id(p)` aliases `(*p)` through
    /// the call return; the base is then mutated through the sibling copy `b = p`. TODAY the edge
    /// `issuer=<arg temp> requirers=[x]` is discharged via the ISSUER, so `p`/`b` go `Raw` and
    /// **`x` survives `Ref`** — a shared reference into a cell written through a raw alias (the
    /// S2-6 family, production-parity, §8-guarded). A′ must demote the live requirer `x`.
    ///
    /// §0.1 residual-model probe (WIDENED, ruled 2026-07-12): the accepted model is inspected for
    /// the WHOLE aliasing cluster, not just `x` — no slot in it may remain `Ref`, or the "fix" has
    /// merely relocated the unsoundness. Any `Ref` here is a STOP requiring a soundness argument.
    #[test]
    fn nb4_returned_borrow_vs_base_mutation() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let x = id(p); *x = 1; let b = p; *b = 2; *x }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["x", "p", "b"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "A′: `x` is a LIVE requirer of the invalidated loan on `(*p)`; demoting the \
                     issuer (the arg temp ≡ `p`) removes the CONFLICT but not x's REQUIREMENT — \
                     x must not survive `Ref`"
                );
                // §0.1 WIDENED residual-model probe: pin the FULL accepted model, not just `x` —
                // a "fix" that merely relocates the unsoundness must not pass.
                for (label, (kind, _)) in [("p", m[1]), ("b", m[2])] {
                    assert_ne!(
                        kind,
                        Some(SlotKind::Ref),
                        "residual-model probe: `{label}` aliases the written cell and must not \
                         settle `Ref` — a `Ref` here means the unsoundness moved, not closed"
                    );
                }
                // The ONE slot that does settle `Ref`: the callee PARAM. Pinned, not excused — it
                // is the named residual "unmodeled call-boundary materialization" (§8-guarded,
                // pre-existing, assigned to 4b's micro-plan). See
                // `nb4_marker_raw_arg_ref_param_unmodeled` and `nb4_marker_two_aliasing_args_both_ref`.
                let sig = nb4_accept(tcx, &program, "id", &["q"]);
                assert_eq!(
                    sig[0].0,
                    Some(SlotKind::Ref),
                    "residual-model probe: `id.q` is the sole `Ref` in the accepted model — the \
                     named call-boundary-materialization residual, NOT closed by A′"
                );
            },
        );
    }

    /// §NB4-4a RED (a) — **callee write kills the caller's alias.** Same edge shape as (c), but the
    /// invalidating write comes from a CALLEE (`writer` writes `*q`) rather than an inline base
    /// mutation. This is the INTERACTION fixture: it must hold under A′ (4a-i) *and* survive
    /// 4a-ii's effect gating, because `writer` is classified **may-write** — gating must not
    /// silently switch off a real writer's access.
    #[test]
    fn nb4_callee_write_invalidates_caller_loan() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn writer(q: *mut i32) {{ *q = 7; }} \
                 unsafe fn f(p: *mut i32) -> i32 {{ let x = id(p); *x = 1; writer(p); *x }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["x", "p"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "A′: `writer(p)` invalidates the loan `x` requires; x is the live requirer and \
                     must be demoted (today the issuer is demoted and x survives `Ref`)"
                );
                assert_ne!(
                    m[1].0,
                    Some(SlotKind::Ref),
                    "residual probe: `p` must not stay `Ref`"
                );
            },
        );
    }

    /// §NB4-4a RED (c′) — the **minimal S2-6-family** shape: the returned borrow `x` is IMMUTABLE
    /// (never written through ⇒ Foster `Imm`), and the base is written through the sibling `b = p`.
    /// A′ closes this **a phase early** — its reach is a property of the EDGE MENU, not of loan
    /// mutability, so the "immutable ⇒ needs write-awareness" intuition does not apply.
    ///
    /// ⚠ TRIPWIRE (recorded 2026-07-12): this closure rests on the pointer-copy-as-`Deep`-access
    /// OVER-APPROXIMATION — `let b = p` is a copy of the pointer VALUE, not an access to the
    /// pointee, yet it invalidates the loan `x` requires. If any future precision work gates copy
    /// accesses, this fixture goes RED and the soundness must be re-carried by the copy-group
    /// routing mechanism (the redesigned 4b closure). This test is the tripwire for exactly that.
    #[test]
    fn nb4_returned_immutable_borrow_vs_base_write() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let x = id(p); let b = p; *b = 5; *x }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["x", "p", "b"]);
                assert!(
                    !m[0].1,
                    "precondition: `x` is never written THROUGH ⇒ Foster `Imm` (this is the \
                     immutable shape — the one the Imm-skip protects at 4b)"
                );
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "A′ demotes the live requirer `x` even though its provenance is IMMUTABLE — \
                     the menu restriction is orthogonal to the immutable-loan skip"
                );
                assert_ne!(m[1].0, Some(SlotKind::Ref), "residual probe: `p`");
                assert_ne!(m[2].0, Some(SlotKind::Ref), "residual probe: `b`");
            },
        );
    }

    /// §NB4-4a-ii **CONTROL — the fixture that KILLED the no-access gate.** (Was
    /// `nb4_no_deref_callee_loan_survives`, asserting `x` stays `Ref`. That assertion was
    /// **UNSOUND**; it now pins the opposite, and exists to stop the gate being re-attempted.)
    ///
    /// `ignores` takes the pointer BY VALUE and never dereferences it, so the "spurious
    /// over-invalidation" story was: the Call arm's effect-blind `Deep` access to `(*arg)`
    /// manufactures a conflict no callee could cause ⇒ gate it and `x` survives `Ref`.
    ///
    /// **The no-call CONTROL refutes that.** Replacing `ignores(p)` with a plain value use of `p`
    /// and **no call at all** (`let v = p as usize as i32;`) demotes `x` to `Raw` *identically*.
    /// So the conflict is not about the POINTEE and not about the call: it is a **use of `p`
    /// while `x` holds an outstanding reborrow of `(*p)`**, which under the reference reading the
    /// model is deciding is a GENUINE borrowck conflict (`let x = id(p); *x = 1; /* use p */; *x`
    /// — you cannot use a `&mut` while a live reborrow derives from it).
    ///
    /// Therefore `Deep`-access-on-copy is **not** an over-approximation of pointee access — it is
    /// the correct conservative treatment of a use of a BORROWED BASE, and there is no
    /// over-invalidation class to gate at the argument level. `call_effects`'s `no-access` facts
    /// are real, but gating invalidation on them is unsound. **Do not re-add the gate.**
    #[test]
    fn nb4_no_deref_callee_still_conflicts() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn ignores(_q: *mut i32) -> i32 {{ 0 }} \
                 unsafe fn f(p: *mut i32) -> i32 \
                 {{ let x = id(p); *x = 1; let v = ignores(p); *x + v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["x"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`x` MUST be demoted: passing `p` to `ignores` is a USE of `p` while `x` holds \
                     a live reborrow of `(*p)` — a genuine conflict, independent of what the callee \
                     does with the pointee. The no-call control (`let v = p as usize`) demotes `x` \
                     identically, which is what refuted the no-access gate. Do not gate this."
                );
            },
        );
    }

    /// §NB4-R MARKER — Codex adversarial review (2026-07-15) surfaced two code-level fragilities in
    /// the routing under MULTIPLY-ASSIGNED / branch-joined MIR locals:
    ///   (F1) offset exclusion keys by `(Local, Place)` without loan-location, so a local assigned
    ///        BOTH `b = p.offset(1)` and `b = p` (same source) has its copy loan wrongly excluded;
    ///   (F2) the routing walk dedups by base `Local`, so a writer branch-joined from `h.q`/`h.r`
    ///        (both base local `h`) has one field edge dropped by the visited set.
    /// Both are in the UNDER-invalidation direction (a missed demotion → §8-guarded UAF class).
    ///
    /// This marker WITNESSES that on both flagged shapes the views settle `Raw` REGARDLESS of routing
    /// (verified `Raw` with `CRAT_NB4R_ROUTING` on AND off, 2026-07-15): the tree-borrow GROUP
    /// machinery demotes the branch/collision copies independently, so the routing edge-drop /
    /// over-exclusion is MASKED — no observable under-invalidation. The findings are latent code
    /// fragility, not an active regression. If a future change removes the grouping safety net for
    /// these shapes, this marker flips (a view goes `Ref`) and surfaces the hole. See the NB4-R task
    /// doc for the fix options (F2: dedup the walk by loan/edge, not base local; F1: disambiguate
    /// offset vs copy via a copy-signature set).
    #[test]
    fn nb4r_marker_multiassign_grouping_masked() {
        let f2 = format!(
            "{NB4_ID} #[repr(C)] struct H {{ q: *mut i32, r: *mut i32 }} \
             unsafe fn f(mut h: H, c: bool) -> i32 \
             {{ let vq = id(h.q); let vr = id(h.r); let b = if c {{ h.q }} else {{ h.r }}; \
                let r0 = *vq + *vr; *b = 5; r0 + *vq + *vr }}"
        );
        let f1 = format!(
            "{NB4_ID} unsafe fn f(mut p: *mut i32, c: bool) -> i32 \
             {{ let v = id(p); let mut b = p; if c {{ b = p.offset(1); }} \
                let r0 = *v; *b = 5; r0 + *v }}"
        );
        for (label, src, views) in [
            ("F2 branch-joined field sources", f2, &["vq", "vr"][..]),
            ("F1 offset+copy collision", f1, &["v"][..]),
        ] {
            run_compiler(&src, |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", views);
                for (i, v) in views.iter().enumerate() {
                    assert_eq!(
                        m[i].0,
                        Some(SlotKind::Raw),
                        "{label}: view `{v}` is demoted by the grouping safety net (Raw), masking the \
                         Codex-flagged routing fragility — no observable under-invalidation here."
                    );
                }
            });
        }
    }

    /// §NB4-R MARKER — the READ-direction residue that WRITE-gating could open (user probe 2026-07-16).
    /// Shape: `x = id(p)` is a LIVE MUTABLE call-return `&mut` (it writes `*x=1` later); a foreign read
    /// `v = *b` (b=p, sibling) sits between x's borrow and x's write. Under Tree Borrows the foreign
    /// read freezes x's tag → `*x=1` is UB, so x must NOT stay a safe `&mut`. Routing is WRITE-gated,
    /// so `*b` (a read) does NOT route to x's loan (keyed under p) — the worry was that this leaves x
    /// at `Ref`.
    ///
    /// WITNESS: x settles `Raw` with `CRAT_NB4R_ROUTING` on AND off (verified 2026-07-16). MECHANISM —
    /// GROUPING masks it: unlike a shared read *view* (which survives grouping and is the S2-6 hole a
    /// WRITE must route to close, e.g. `nb4r_sibling_copies`), a `&mut` view aliasing the same cell is
    /// linked through `p` to the co-aliaser `b` and demoted by the tree-borrow group conflict. So
    /// write-gating did NOT open an observable residue in the read-vs-`&mut` direction. This joins
    /// F1/F2/3b behind the grouping safety net (see NB4-R task doc §13). If a future change stops
    /// grouping from demoting a `&mut` with a live foreign read, this marker flips (x → Ref) and the
    /// residue becomes real — at which point route read-derefs but check only MUTABLE loans
    /// (borrowck's read-vs-`&mut`; the immutable-loan skip already spares read-only cells).
    #[test]
    fn nb4r_marker_read_vs_mut_grouping_masked() {
        let src = format!(
            "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
             {{ let x = id(p); let b = p; let v = *b; *x = 1; v + *x }}"
        );
        run_compiler(&src, |tcx| {
            let program = collect_program(tcx);
            let m = nb4_accept(tcx, &program, "f", &["x"]);
            assert_eq!(
                m[0].0,
                Some(SlotKind::Raw),
                "x (a &mut call-return frozen by the foreign read `*b`) is demoted to Raw by the \
                 grouping safety net — so WRITE-gating opens no observable read-vs-&mut residue."
            );
        });
    }

    /// §NB4-R WHITE-BOX (Amendment 3b, grouping-independent) — the whole-cell fallback DECISION.
    /// The end-to-end `nb4r_type_pun_invalidates` is grouping-masked (the view is `Raw` regardless), so
    /// a fallback REGRESSION (composing the ill-typed place → `places_conflict` `unreachable!`/`Disjoint`)
    /// could hide behind grouping. This tests `route_compose` directly: an `(*p):i32` edge with a
    /// `Pair`-field `rest` and `deref_ty = Pair` MUST return `WholeCell` (the whole i32 cell, later
    /// forced Deep), never `Composed` (which would feed `places_conflict` an ill-typed place). The
    /// well-typed control (`(*q):Pair` edge, same rest) MUST `Composed`. Survives grouping changes.
    #[test]
    fn nb4r_route_compose_fallback_on_type_mismatch() {
        use rustc_abi::FieldIdx;
        use rustc_middle::mir::{Place, PlaceElem};

        use crate::analyses::borrow_ownership::borrow_engine::{RoutedCompose, route_compose};
        run_compiler(
            "#[repr(C)] struct Pair { a: i32, b: i32 } \
             unsafe fn f(p: *mut i32, q: *mut Pair) { let _ = (p, q); }",
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let p = local_by_var_name(tcx, f, "p");
                let q = local_by_var_name(tcx, f, "q");
                let bp = Place::from(p).project_deeper(&[PlaceElem::Deref], tcx); // (*p): i32
                let bq = Place::from(q).project_deeper(&[PlaceElem::Deref], tcx); // (*q): Pair
                let i32_ty = bp.ty(&*body, tcx).ty;
                let pair_ty = bq.ty(&*body, tcx).ty;
                let field0 = [PlaceElem::Field(FieldIdx::from_usize(0), i32_ty)]; // Pair.a : i32

                // MISMATCH: edge `(*p):i32`, access derefs to `Pair` with a Pair-field rest ⇒ fallback.
                match route_compose(tcx, &*body, bp, &field0, pair_ty) {
                    RoutedCompose::WholeCell(pl) => {
                        assert_eq!(pl, bp, "fallback must be the whole borrowed cell `(*p)`")
                    }
                    RoutedCompose::Composed(_) => {
                        panic!(
                            "type mismatch MUST fall back — composing feeds places_conflict a \
                                Field-of-Pair on an i32 place (unreachable!/Disjoint→UAF)"
                        )
                    }
                }
                // WELL-TYPED control: edge `(*q):Pair`, `deref_ty=Pair`, Pair-field rest ⇒ compose.
                match route_compose(tcx, &*body, bq, &field0, pair_ty) {
                    RoutedCompose::Composed(pl) => {
                        assert_eq!(
                            pl,
                            bq.project_deeper(&field0, tcx),
                            "well-typed composition"
                        )
                    }
                    RoutedCompose::WholeCell(_) => panic!("well-typed composition MUST compose"),
                }
            },
        );
    }

    // ===== §NB4-R — place-based cross-alias-write routing (RED-first, pre-implementation) =====
    //
    // Spec: docs/agents/tasks/2026-07-15-nb4r-place-based-routing-spec.md.
    //
    // WHAT THE ROUTING HOLE ACTUALLY IS (dump 2026-07-15, corrected from the spec's assumption): the
    // existing tree-borrow-GROUP machinery already produces cross-alias conflict edges for most
    // co-located views — a DIRECT copy view (`c=p`), a 2-hop writer (`c=b=p`), a field/cast writer —
    // are demoted TODAY without routing. The genuine hole is NARROW: a grouping-BROKEN view (a call
    // return `c=id(p)`, keyed under the base cell but NOT linked to the writer by a group loan) written
    // through a SIMPLE 1-hop / deref / reconverging sibling. There, `*b=…` looks up the EMPTY `row(b)`
    // and leaves `c` at `Ref`. Routing composes the write onto the loan's BORROWED place, sends it to
    // `row(base)`, and demotes `c` to `Raw`.
    //
    // So the fixtures split two ways:
    //   * RED FLIPS (view `Ref` today, `Raw` after routing) — the isolating tests: `sibling_copies`
    //     (1-hop), `deref_chain_no_crash` (multi-level), `reconverging_dag_bounded` (multi-writer).
    //   * CRASH-SAFETY / NO-REGRESSION CONTROLS (view already `Raw`, or `Ref` in both states) — routing
    //     must FIRE on these composition shapes without panicking or regressing: `copy_of_copy`
    //     (2-hop), `field_local_source` (leading-Field — the reverted crash), `type_pun_invalidates`
    //     (cast whole-cell fallback — the `places_conflict` `unreachable!` class), `offset_excluded`
    //     (offset shape), `reborrow_self_write_survives` (self-skip → `Ref`), `no_alias_ablation`
    //     (inert → `Ref`). These are NOT RED.

    /// §NB4-R RED (Amendment 3a) — **1-hop sibling, call-return view.** `b=p` (writer) and `c=id(p)`
    /// (a call-return alias of `(*p)`) address the same cell, but `c` is NOT tree-borrow-grouped with
    /// `b` (a call return is not a copy rvalue), so `*b=5` — which looks up the EMPTY `row(b)` — leaves
    /// `c` at `Ref` today (the S2-6 hole; direct `c=p` is grouped-demoted and would NOT isolate
    /// routing — confirmed by dump 2026-07-15). Routing walks `b`'s issued loan to `row(p)` and demotes
    /// `c`. One hop (`b→p`); contrast `nb4r_copy_of_copy`.
    #[test]
    fn nb4r_sibling_copies() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let b = p; let c = id(p); let r0 = *c; *b = 5; r0 + *c }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["c"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`c` (call-return view of (*p), live across `*b=5`) must be demoted: routing sends \
                     the write through `b`'s issued loan (borrowed=(*p)) to `row(p)` (S2-6 closure, 1-hop)."
                );
            },
        );
    }

    /// §NB4-R CONTROL (crash-safety, 2-hop composition) — writer `c = b = p`; `*c=5` makes routing
    /// walk `c→b→p` (PRE-order visited discipline). The call-return view `v=id(p)` is already demoted
    /// TODAY by the group machinery (a 2-hop writer links to the view's cell via group loans), so this
    /// is NOT a flip — it guards that the multi-hop walk does not crash or regress `v` off `Raw`.
    #[test]
    fn nb4r_copy_of_copy() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let v = id(p); let b = p; let c = b; let r0 = *v; *c = 5; r0 + *v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["v"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`v` stays `Raw`: the 2-hop routing walk c→b→p must terminate cleanly and not \
                     regress the (already group-demoted) view."
                );
            },
        );
    }

    /// §NB4-R CONTROL (crash-safety, leading-Field composition) — writer `b = h.q` builds
    /// `borrowed=(*(h.q)) = [Field(q), Deref]` — LAST element `Deref` (a copy of a field pointer), so
    /// it IS a chain edge (the reverted `first==Deref` filter wrongly dropped it, §11-B). Compose
    /// routes `*b=5` onto `(*(h.q))` (type-valid); the reverted `Local` re-base produced `(*h)` (a
    /// STRUCT deref → `places_conflict` crash). The view `v=id(h.q)` is already group-demoted, so this
    /// guards that leading-Field composition routes without the crash — not a flip.
    #[test]
    fn nb4r_field_local_source() {
        run_compiler(
            &format!(
                "{NB4_ID} #[repr(C)] struct H {{ q: *mut i32 }} \
                 unsafe fn f(mut h: H) -> i32 \
                 {{ let v = id(h.q); let b = h.q; let r0 = *v; *b = 5; r0 + *v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["v"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`v` stays `Raw`: leading-Field composition onto `(*(h.q))` must route without the \
                     struct-deref crash the `Local` re-base hit."
                );
            },
        );
    }

    /// §NB4-R RED — **multi-level deref, no crash.** writer `inner = *pp` builds `borrowed=(**pp) =
    /// [Deref, Deref]` — the exact shape the reverted re-base crashed on (`places_conflict`
    /// `unreachable!`). Compose routes `*inner=5` to `(**pp)` cleanly and demotes the call-return view
    /// `v=id(*pp)` (keyed under `pp`).
    #[test]
    fn nb4r_deref_chain_no_crash() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(pp: *mut *mut i32) -> i32 \
                 {{ let inner = *pp; let v = id(*pp); let r0 = *v; *inner = 5; r0 + *v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["v"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`v` (call-return view of *pp) is demoted by `*inner=5` via the multi-level chain \
                     to `(**pp)` — routes clean where the old rule panicked."
                );
            },
        );
    }

    /// §NB4-R CONTROL (Amendment 3b — type-pun whole-cell fallback; no-crash + invalidation) — writer
    /// `b = p as *mut Pair` casts the pointee type; `(*b).a = 5` would compose `(*p):i32 ++ [Field(a)]`
    /// which is ILL-TYPED. The type-check MUST catch this and fall back to whole-cell `(*p)` Deep — if
    /// it instead emitted the composed place, `places_conflict` would `unreachable!` (panic) or return
    /// `Disjoint` (silent miss → UAF). `w=id(p)` ends `Raw` (invalidated, not silently missed).
    ///
    /// ISOLATION CAVEAT (dump 2026-07-15): the cast operand is a compiler-inserted copy of `p`
    /// (`_5=copy _1; _4=_5 as Pair`), which the group machinery links to the view's cell, so `w` is
    /// already `Raw` today. The fallback's positive effect therefore CANNOT be isolated as a `Ref→Raw`
    /// flip in a minimal fixture; this test guards the two properties that ARE testable here — the
    /// type-check prevents the `places_conflict` crash (no panic) and the write does invalidate `w`
    /// (`Raw`, not silently dropped). Reported to the user as a deviation from Amendment 3b's "isolate
    /// the fallback" wording, with this structural reason.
    #[test]
    fn nb4r_type_pun_invalidates() {
        run_compiler(
            &format!(
                "{NB4_ID} #[repr(C)] struct Pair {{ a: i32, b: i32 }} \
                 unsafe fn f(p: *mut i32) -> i32 \
                 {{ let w = id(p); let b = p as *mut Pair; let r0 = *w; (*b).a = 5; r0 + *w }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["w"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`w` stays `Raw`: the ill-typed cast composition must fall back to whole-cell `(*p)` \
                     Deep — no `places_conflict` panic, and the write is NOT silently missed."
                );
            },
        );
    }

    /// §NB4-R RED (walk-bound smoke) — reconverging copy chains (`s→a→p`, `s2→b→p`) must terminate
    /// within the N cap and still demote the call-return view `v=id(p)`. PRE-order visited-marking
    /// keeps the reconvergence at `p` from re-expanding; the impl's per-site cap asserts it.
    #[test]
    fn nb4r_reconverging_dag_bounded() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let a = p; let b = p; let s = a; let s2 = b; let v = id(p); \
                    let r0 = *v; *s = 1; *s2 = 2; r0 + *v }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["v"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`v` demoted by the routed writes; the reconverging chains terminate (no hang/panic)."
                );
            },
        );
    }

    /// §NB4-R CONTROL (offset shape — no crash) — writer `r = p.offset(1)` builds the copy-identical
    /// `borrowed=(*p)` but addresses a DIFFERENT cell (`p+1`), so routing EXCLUDES it as a chain edge
    /// (§4.1 coupling guard). Here the view `c=id(p)` is already demoted by the existing engine's
    /// handling of the offset write (dump 2026-07-15: `c=Raw` today), so this shape cannot isolate the
    /// −17.7% over-demotion the exclusion prevents — that guard lives at the CORPUS gate (§8). This
    /// unit only pins that routing handles the offset shape without a crash/regression.
    #[test]
    fn nb4r_offset_excluded() {
        run_compiler(
            &format!(
                "{NB4_ID} unsafe fn f(p: *mut i32) -> i32 \
                 {{ let c = id(p); let r = p.offset(1); let v0 = *c; *r = 9; v0 + *c }}"
            ),
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["c"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Raw),
                    "`c` stays `Raw` (already demoted by the existing offset-write handling); routing \
                     with offset EXCLUDED must not crash or regress it. The over-demotion guard is the \
                     corpus gate, not this unit."
                );
            },
        );
    }

    /// §NB4-R CONTROL (self-loan skip — finding C) — `b = p; *b = 5; *b`. `b` is the SOLE alias and
    /// writes through itself; routing reaches `b`'s OWN loan in `row(p)` (keyed under p, not b), which
    /// must be SKIPPED (`assigned == Assign(b)`) or `b` self-demotes. `b` stays `Ref` (a valid `&mut`)
    /// in BOTH states. Without the skip, every `let b=&mut *p; *b=…` reborrow would regress.
    #[test]
    fn nb4r_reborrow_self_write_survives() {
        run_compiler(
            "unsafe fn f(p: *mut i32) -> i32 { let b = p; *b = 5; *b }",
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["b"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Ref),
                    "`b` writes through itself as the sole alias — a valid `&mut`. Routing must skip \
                     `b`'s own loan (self-loan skip) or it spuriously self-demotes."
                );
            },
        );
    }

    /// §NB4-R CONTROL (ablation — byte-identical) — a shared view with NO cross-alias write anywhere
    /// stays `Ref` in BOTH states. Routing must not perturb a program with nothing to route.
    #[test]
    fn nb4r_no_alias_ablation() {
        run_compiler(
            "unsafe fn f(p: *mut i32) -> i32 { let c = p; let r0 = *c; let r1 = *c; r0 + r1 }",
            |tcx| {
                let program = collect_program(tcx);
                let m = nb4_accept(tcx, &program, "f", &["c"]);
                assert_eq!(
                    m[0].0,
                    Some(SlotKind::Ref),
                    "no write ⇒ `c` stays a shared `&` view; routing is inert here."
                );
            },
        );
    }

    /// Multiset difference for the §NB3-3c divergence delta: `a` minus `b`, each `b` element removing
    /// exactly ONE `a` element (multiplicity-preserving, so a duplicated or dropped edge is not
    /// masked). Module-level so `nb3c_divergence_delta_multiplicity` can guard it directly.
    fn multiset_diff(a: &[String], b: &[String]) -> Vec<String> {
        let mut remaining: std::collections::BTreeMap<&String, usize> =
            std::collections::BTreeMap::new();
        for x in b {
            *remaining.entry(x).or_default() += 1;
        }
        let mut out = vec![];
        for x in a {
            match remaining.get_mut(x) {
                Some(c) if *c > 0 => *c -= 1,
                _ => out.push(x.clone()),
            }
        }
        out
    }

    /// Guards the §NB3-3c divergence DELTA (Codex F3): the multiplicity-preserving symmetric
    /// difference must (a) be empty for equal multisets, (b) CHANGE when an edge within a case
    /// changes, and (c) not mask a dropped duplicate. Without this, once 3c-ii allowlists a case,
    /// edges shifting inside it would leave the case-ID present and the gate green.
    #[test]
    fn nb3c_divergence_delta_multiplicity() {
        let s = |xs: &[&str]| xs.iter().map(|x| x.to_string()).collect::<Vec<_>>();
        // (a) equal ⇒ empty both ways.
        assert!(multiset_diff(&s(&["A", "B"]), &s(&["B", "A"])).is_empty());
        // (b) a within-case edge change (fork C→D) alters the fork-only side of the delta.
        let prod = s(&["A", "B"]);
        let before = multiset_diff(&s(&["A", "C"]), &prod); // fork_only when fork = {A,C}
        let after = multiset_diff(&s(&["A", "D"]), &prod); // fork_only when fork = {A,D}
        assert_eq!(before, s(&["C"]));
        assert_ne!(
            before, after,
            "changing an edge within a case must change the delta"
        );
        // (c) multiplicity: a dropped DUPLICATE is surfaced, not masked by the other copy.
        assert_eq!(multiset_diff(&s(&["A", "A"]), &s(&["A"])), s(&["A"]));
    }

    /// §NB3-3c EQUIVALENCE SUCCESSOR — replaces the two retired 3a byte/multiset-equivalence
    /// fixtures (`nb3a_fork_engine_edges_match_production`, `nb3a_fork_engine_multiset_matches_mixed_replay`).
    ///
    /// 3a's job was pre-divergence faithfulness: fork == production on every case. 3c is the first
    /// deliberate divergence (3c-ii injects origins), so the gate's shape changes from "fork ==
    /// production, always" to "**fork == production modulo an ENUMERATED divergence list**". This is
    /// that successor. It collects the case-ID of every (program, mode) where the fork's conflict-edge
    /// MULTISET differs from production's, and asserts that divergence set EQUALS
    /// `FORK_PRODUCTION_DIVERGENCE` — both directions, exactly as the §0.2 dependency ratchet does:
    ///   - fork≠prod on an un-enumerated case → fails (a divergence must be declared, with its cause);
    ///   - an enumerated case that no longer diverges → fails (the list must shrink to match reality).
    ///
    /// **At 3c-i the list is EMPTY:** origins are computed but NOT injected, so the fork is still
    /// byte/multiset-equal to production on every case — the successor proves itself against the (still
    /// present) 3a gate before any divergence exists, which is the correct retirement sequence. 3c-ii's
    /// injection commit adds one case-ID per program×mode its new interprocedural conflicts perturb.
    ///
    /// Covers BOTH 3a fixtures' inputs: the uniform program×mode differential (round-0 across
    /// mutability; replaying across raw-candidacy × mutability, all-Ref base) AND the mixed-Raw/Ref
    /// replay (r0/r1/r2 Raw, keep Ref). Comparison is order-INSENSITIVE (`multiset`): loan-ID / edge
    /// order is non-contractual (production's `UnionFind` walks a seed-randomized `std::HashSet`); the
    /// contractual chain is **same edge multiset per replay ⇒ same demotion set ⇒ same accepted model**.
    #[test]
    fn nb3c_fork_equals_production_modulo_divergence() {
        use std::collections::BTreeMap;

        use rustc_hash::FxHashMap;
        use rustc_span::def_id::LocalDefId;

        use crate::analyses::{
            borrow::{self, ConflictEdge},
            borrow_ownership::borrow_engine,
        };

        // 3c-i: EMPTY. 3c-ii enumerates deliberate divergences here as (case-ID, expected DELTA)
        // pairs — case-ID is "{program}/round0/mut=.." | "{program}/replay/raw=../mut=.." |
        // "mixed_replay"; the DELTA is the canonical per-case prod-vs-fork edge symmetric-difference
        // string (`case_delta`). Enumerating the DELTA (not just the ID) means edges CHANGING within
        // an already-allowed divergence still fails the gate (Codex F3).
        // §NB4-R cross-alias-WRITE routing divergence class (2026-07-15). Fork routes the write
        // `*b=5` through `b`'s issued loan to the aliased loan (the S2-6 closure); production is
        // structurally blind. SOUND DIRECTION — every entry is `prod_only=[]` (fork ⊇ production;
        // fork only ADDS conflict edges, never drops one), so the fork is strictly more conservative.
        // Surfaces only in forced-`mut=true` (the gate's all-mutable mode); the real fact-mut flip is
        // proven by `nb2_cross_alias_write_uncaught_witness` (state-3). Routing is gated to WRITE
        // accesses, so read-only cases (`raw_copies`) do NOT diverge.
        const FORK_PRODUCTION_DIVERGENCE: &[(&str, &str)] = &[
            (
                "call_return_write/round0/mut=true",
                "prod_only=[] fork_only=[\"DefId(0:4 ~ rust_out[96a3]::f) issuer=Some(Local(_4)) requirers=[\\\"Local(_5)\\\"]\"]",
            ),
            (
                "call_return_write/replay/raw=false/mut=true",
                "prod_only=[] fork_only=[\"DefId(0:4 ~ rust_out[96a3]::f) issuer=Some(Local(_4)) requirers=[\\\"Local(_5)\\\"]\"]",
            ),
        ];

        // Order-INSENSITIVE canonical edge multiset (per-fn key embedded), for prod-vs-fork equality.
        fn multiset(m: &FxHashMap<LocalDefId, Vec<ConflictEdge>>) -> Vec<String> {
            let mut out: Vec<String> = m
                .iter()
                .flat_map(|(k, edges)| {
                    edges.iter().map(move |e| {
                        let mut rs: Vec<String> =
                            e.requirers.iter().map(|o| format!("{o:?}")).collect();
                        rs.sort();
                        format!("{k:?} issuer={:?} requirers={rs:?}", e.issuer)
                    })
                })
                .collect();
            out.sort();
            out
        }

        // The per-case divergence DELTA (Codex F3): the multiplicity-preserving symmetric difference
        // of the prod vs fork edge multisets, as a canonical string. `None` ⇔ multisets equal (no
        // divergence). Comparing the DELTA (not just a case ID) makes a change to the edges WITHIN an
        // already-enumerated divergence fail the gate.
        fn case_delta(
            prod: &FxHashMap<LocalDefId, Vec<ConflictEdge>>,
            fork: &FxHashMap<LocalDefId, Vec<ConflictEdge>>,
        ) -> Option<String> {
            let (p, f) = (multiset(prod), multiset(fork));
            let prod_only = multiset_diff(&p, &f);
            let fork_only = multiset_diff(&f, &p);
            (!prod_only.is_empty() || !fork_only.is_empty())
                .then(|| format!("prod_only={prod_only:?} fork_only={fork_only:?}"))
        }

        // (stable case-ID root, source) — the 3a fixture-1 program family.
        let programs: [(&str, &str); 5] = [
            // aliasing &mut borrows of one local, both live → conflict (all-mut)
            (
                "mut_alias",
                "unsafe fn f() { let mut x = 0i32; let p = &mut x as *mut i32; \
                 let q = &mut x as *mut i32; *p = 1; *q = 2; }",
            ),
            // aliasing borrows with reads (exercises mutability-dependent conflict)
            (
                "mut_alias_reads",
                "unsafe fn f() { let mut x = 0i32; let a = &mut x as *mut i32; \
                 let b = &mut x as *mut i32; let u = *a; let v = *b; let _ = (u, v); }",
            ),
            // *mut *mut aliasing outer pointers + a call (the out-param shape)
            (
                "outparam_call",
                "unsafe fn g(o: *mut *mut i32) { let _ = o; } \
                 unsafe fn f() { let mut local: *mut i32 = core::ptr::null_mut(); \
                 let p = &mut local as *mut *mut i32; let q = &mut local as *mut *mut i32; \
                 g(p); *q = core::ptr::null_mut(); }",
            ),
            // raw-pointer copies (no borrows) → empty map (agreement on empty is still a real check)
            (
                "raw_copies",
                "unsafe fn f(mut p: *mut i32) -> i32 { let a = p; let b = p; *a + *b }",
            ),
            // call-return alias + write (the S2-6 shape — the case 3c-ii origins will diverge on)
            (
                "call_return_write",
                "#[inline(never)] unsafe fn id(mut p: *mut i32) -> *mut i32 { p } \
                 unsafe fn f(mut p: *mut i32) -> i32 { let b = p; let x = id(p); let z = x; let r0 = *z; *b = 5; r0 + *z }",
            ),
        ];

        let mut diverged: BTreeMap<String, String> = BTreeMap::new();

        // Non-vacuity guard (from 3a fixture-1): aliasing &mut borrows of one local, both live, MUST
        // produce a conflict edge — proves the differential is not comparing empty==empty.
        run_compiler(programs[0].1, |tcx| {
            let program = collect_program(tcx);
            let edges = borrow::borrow_conflicts(
                &program,
                |_: LocalDefId| |_: Local| true,
                |_: LocalDefId| |_: Local| true,
            );
            assert!(
                !edges.is_empty(),
                "non-vacuity: aliasing &mut borrows must produce a conflict edge"
            );
        });

        for (label, src) in programs {
            run_compiler(src, |tcx| {
                let program = collect_program(tcx);
                // round-0 (`borrow_conflicts`) across mutability:
                for mutb in [true, false] {
                    let prod = borrow::borrow_conflicts(
                        &program,
                        |_: LocalDefId| |_: Local| true,
                        move |_: LocalDefId| move |_: Local| mutb,
                    );
                    let fork = borrow_engine::borrow_conflicts(
                        &program,
                        |_: LocalDefId| |_: Local| true,
                        move |_: LocalDefId| move |_: Local| mutb,
                    );
                    if let Some(d) = case_delta(&prod, &fork) {
                        diverged.insert(format!("{label}/round0/mut={mutb}"), d);
                    }
                }
                // replaying across raw-candidacy × mutability, all-Ref base:
                for raw in [false, true] {
                    for mutb in [true, false] {
                        let prod = borrow::borrow_conflicts_replaying(
                            &program,
                            |_: LocalDefId| |_: Local| true,
                            move |_: LocalDefId| move |_: Local| raw,
                            move |_: LocalDefId| move |_: Local| mutb,
                        );
                        let fork = borrow_engine::borrow_conflicts_replaying(
                            &program,
                            |_: LocalDefId| |_: Local| true,
                            move |_: LocalDefId| move |_: Local| raw,
                            move |_: LocalDefId| move |_: Local| mutb,
                            &[], /* §NB5-F2: no field candidacy → fork matches production's field handling */
                        );
                        if let Some(d) = case_delta(&prod, &fork) {
                            diverged.insert(format!("{label}/replay/raw={raw}/mut={mutb}"), d);
                        }
                    }
                }
            });
        }

        // The 3a fixture-2 mixed-Raw/Ref replay (r0/r1/r2 Raw, keep Ref) — the loan-ID-order stressor.
        run_compiler(
            r#"
unsafe fn f() {
    let mut cell = 0i32;
    let r0 = &mut cell as *mut i32;
    let r1 = &mut cell as *mut i32;
    let r2 = &mut cell as *mut i32;
    let keep = &mut cell as *mut i32;
    let k0 = keep;
    *r0 = 1;
    let k1 = keep;
    *r1 = 2;
    let k2 = keep;
    *r2 = 3;
    let s = *keep;
    let _ = (k0, k1, k2, s);
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let rl: [Local; 3] = [
                    local_by_var_name(tcx, f, "r0"),
                    local_by_var_name(tcx, f, "r1"),
                    local_by_var_name(tcx, f, "r2"),
                ];
                let rl = &rl;
                let prod = borrow::borrow_conflicts_replaying(
                    &program,
                    |_: LocalDefId| |_: Local| true,
                    move |_fd: LocalDefId| move |local: Local| rl.contains(&local),
                    |_: LocalDefId| |_: Local| true,
                );
                let fork = borrow_engine::borrow_conflicts_replaying(
                    &program,
                    |_: LocalDefId| |_: Local| true,
                    move |_fd: LocalDefId| move |local: Local| rl.contains(&local),
                    |_: LocalDefId| |_: Local| true,
                    &[], // §NB5-F2: no field candidacy → fork matches production's field handling
                );
                assert!(
                    !prod.is_empty(),
                    "non-vacuity: the mixed replay must produce conflict edges"
                );
                if let Some(d) = case_delta(&prod, &fork) {
                    diverged.insert("mixed_replay".to_string(), d);
                }
            },
        );

        let expected: BTreeMap<String, String> = FORK_PRODUCTION_DIVERGENCE
            .iter()
            .map(|(id, delta)| (id.to_string(), delta.to_string()))
            .collect();
        assert_eq!(
            diverged, expected,
            "fork vs production per-case divergence DELTAs != enumerated FORK_PRODUCTION_DIVERGENCE.\n  \
             A case-ID on one side only is a new/removed divergence; a case-ID on both sides with a \
             DIFFERENT delta is a changed (possibly regressed) divergence — all fail.\n  \
             observed: {diverged:#?}\n  expected: {expected:#?}"
        );
    }

    /// B3b headline: interprocedural ownership flow across a *return* edge.
    /// `make` allocates and returns ownership; `forward` just returns `make()`'s
    /// result. `forward` contains no `malloc` and no sink, so the *only* path to
    /// ownership in `forward`'s return slot is `Boundary::call` linking
    /// `dest.def = make.ret` (and `make.ret` being owning, which requires `make`'s
    /// body to have been emitted). If that cross-function edge were absent,
    /// `forward`'s return would be soft-objective non-owning — so the assertion
    /// is non-vacuous (a local sink cannot satisfy it, unlike a `free(p)` shape).
    /// `selectors.all().len() == 1` independently proves `make`'s source was emitted by
    /// the crate driver; single-fn emission of `forward` alone would instead
    /// panic on the local call to `make` (absent from a self-entry `InterCtxt`).
    #[test]
    fn interproc_alloc_return_flows_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn make() -> *mut core::ffi::c_void {
    unsafe { malloc(4) }
}

pub unsafe fn forward() -> *mut core::ffi::c_void {
    unsafe { make() }
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let make = function_by_name(&program, "make");
                let forward = function_by_name(&program, "forward");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B3b crate emission should run");

                // The only malloc is in `make`; a selector here proves `make`'s
                // body was emitted by the crate driver (emitting `forward` alone
                // would see zero sources).
                assert_eq!(selectors.all().len(), 1);

                // Return locals (Local 0) at depth 0.
                let make_ret = local_slot(&slots, make, Local::from_u32(0), 0);
                let forward_ret = local_slot(&slots, forward, Local::from_u32(0), 0);

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                // Diagnostic: `make_ret` owning proves `make` was emitted owning;
                // `forward_ret` owning proves the cross-function return edge carried
                // it. A broken edge fails `forward_ret` while `make_ret` still holds.
                assert_eq!(
                    model.get(&make_ret),
                    Some(&SlotKind::Owning),
                    "`make` must return Owning (its malloc source emitted)"
                );
                assert_eq!(
                    model.get(&forward_ret),
                    Some(&SlotKind::Owning),
                    "ownership from `make` must flow across the call into `forward`'s return"
                );
            },
        );
    }

    /// B4 (escape-half retirement): with `output_params` retired, a pointer param
    /// the body only *reads* through must NOT be promoted to `Owning`. Escape is
    /// decided natively now — nothing forces `p` owning, so the soft objective
    /// (prefers Ref) settles its depth-0 slot to `Ref`. This is the anti-regression
    /// guard for the uniform two-slot change: it is RED if the input owning seeds
    /// are kept (they would hard-force `p` `Owning`), GREEN once they are dropped.
    #[test]
    fn read_only_input_arg_is_ref() {
        run_compiler(
            r#"
pub unsafe fn reader(p: *mut i32) -> i32 {
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let reader = function_by_name(&program, "reader");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B4 crate emission should run");

                // `p` is param Local 1; read-only, so its depth-0 slot must be Ref.
                let p = local_slot(&slots, reader, Local::from_u32(1), 0);
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Ref),
                    "a read-only input pointer param must stay Ref, not be promoted to Owning"
                );
            },
        );
    }

    /// B4b probe: a local call passing a (cast) pointer to a `*mut c_void` param.
    /// Post-B4a every arg is `Param::Output`, so the call flows through the `call`
    /// Output arm — which lacks the c_void range-narrowing the now-dead
    /// `Param::Normal` arm had. This checks the Output arm handles the c_void
    /// formal (a deeper actual cast down to c_void) without panicking, deciding
    /// whether B4b can drop the narrowing or must port it.
    #[test]
    fn c_void_local_call_arg_emits() {
        run_compiler(
            r#"
pub unsafe fn take_void(p: *mut core::ffi::c_void) {
    let _ = p;
}

pub unsafe fn caller(pp: *mut *mut i32) {
    unsafe { take_void(pp as *mut core::ffi::c_void) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let _take_void = function_by_name(&program, "take_void");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B4b: c_void local-call emission should run without panicking");

                assert!(
                    kind_solver.model_kinds_relaxing(&selectors).is_some(),
                    "the joint system stays satisfiable with a c_void local-call arg"
                );
            },
        );
    }

    /// B4b escape-half guard (Codex hardening): a pointer param passed *through*
    /// to a local callee. The `call` Output arm ties `p` to the callee's formal
    /// `q`; neither allocates nor frees, so both stay `Ref` (borrowed) — escape
    /// stays solved, not spuriously promoted to Owning across the interprocedural
    /// arg edge that B4a's uniform-Output change rewired.
    #[test]
    fn passed_through_param_stays_ref() {
        run_compiler(
            r#"
pub unsafe fn sink_it(q: *mut i32) {
    let _ = q;
}

pub unsafe fn passes_through(p: *mut i32) {
    unsafe { sink_it(p) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let sink_it = function_by_name(&program, "sink_it");
                let passes_through = function_by_name(&program, "passes_through");
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("B4b: pass-through emission should run");

                let p = local_slot(&slots, passes_through, Local::from_u32(1), 0);
                let q = local_slot(&slots, sink_it, Local::from_u32(1), 0);
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Ref),
                    "passed-through `p` stays Ref (no allocation escapes)"
                );
                assert_eq!(model.get(&q), Some(&SlotKind::Ref), "callee `q` stays Ref");
            },
        );
    }

    /// BB0 (§8 borrow seam): the verifier adapter. `revalidate` runs the production
    /// borrow pipeline with a BO-model-derived ref-candidacy (here all-Ref = Round-0)
    /// and maps the conflict edges back to BO `SlotRef`s. The fixture is the borrow
    /// analysis's own `proof_of_concept` conflict (production demotes `r2`), so the
    /// result must be NON-EMPTY (non-vacuous) and every involved slot must be a real
    /// depth-0 local slot of `f`. This proves candidacy-from-model + borrow_inference
    /// + error extraction + owner→SlotRef translation end-to-end.
    #[test]
    fn bb0_revalidate_maps_round0_borrow_conflict_to_slots() {
        run_compiler(
            r#"
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut r1 = p;
    let mut r2 = r1;
    let mut q = r1;
    *q = 1;
    *r1 = 2;
    *r2 = 3;
    *p = 4;
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let slots = CrateSlots::build(&program);

                // All-Ref Round-0 candidacy + all-mutable (so conflicts register —
                // `invalidates` skips immutable-base loans).
                let conflicts = revalidate(&program, &slots, |_| true, true);
                let f_conflicts = conflicts.get(&f).map(Vec::as_slice).unwrap_or(&[]);

                assert!(
                    !f_conflicts.is_empty(),
                    "all-Ref Round-0 borrow inference must surface the `r2` conflict"
                );

                // Every involved slot is a real depth-0 local of `f`.
                let involved: Vec<SlotRef> = f_conflicts
                    .iter()
                    .flat_map(|c| c.issuer.iter().chain(c.requirers.iter()).copied())
                    .collect();
                for s in &involved {
                    assert!(
                        matches!(s, SlotRef::Local(d, _) if *d == f),
                        "every involved slot is a depth-0 local of `f`, got {s:?}"
                    );
                }

                // The conflict is concretely attributed (not an empty edge): at least
                // one issuer, and `r2` — the local production ultimately demotes, so
                // necessarily a requirer of the round-0 invalid loan — is involved.
                assert!(
                    f_conflicts.iter().any(|c| c.issuer.is_some()),
                    "the conflict must carry a concrete issuer (the loan's assigned owner)"
                );
                let r2_slot = local_slot(&slots, f, local_by_var_name(tcx, f, "r2"), 0);
                assert!(
                    involved.contains(&r2_slot),
                    "`r2`'s depth-0 slot must be in the round-0 conflict; involved = {involved:?}"
                );
            },
        );
    }

    /// BB1 (§8 guard encoder): Round-0 borrow conflicts become `¬ref` exclusion
    /// clauses on the `KindSolver`. The `proof_of_concept` fixture (production demotes
    /// `r2`) has a genuine all-Ref reference-aliasing conflict but NO ownership source,
    /// so the bare BO solve (soft objective maxes Ref) makes every pointer slot `Ref`.
    /// Applying the guards must force >=1 conflict-involved slot OFF Ref. Two
    /// independent solvers prove the guard is the *sole* cause (non-vacuous): baseline
    /// = all Ref; guarded = >=1 non-Ref.
    #[test]
    fn bb1_guard_forces_conflict_slot_off_ref() {
        run_compiler(
            r#"
unsafe fn f(mut p: *mut i32) -> i32 {
    let mut r1 = p;
    let mut r2 = r1;
    let mut q = r1;
    *q = 1;
    *r1 = 2;
    *r2 = 3;
    *p = 4;
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);

                let involved = ["p", "r1", "r2", "q"];
                let slot_of =
                    |name: &str| local_slot(&slots, f, local_by_var_name(tcx, f, name), 0);

                // Solver A — baseline (no guards). `f` has no ownership source, so the
                // soft objective settles every pointer slot to Ref. We assert on the
                // solved *model* (never `KindSolver::assume`, which is a hard constraint
                // — hard-assuming Ref then adding the exclusion would be UNSAT by
                // construction); the guard in Solver B is thus the only added hard fact.
                let solver_a = KindSolver::new(&slots);
                let (_a, selectors_a) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver_a,
                )
                .expect("BB1 baseline emission");
                add_coherence(&solver_a, &slots, f, &body);
                let model_a = solver_a
                    .model_kinds_relaxing(&selectors_a)
                    .expect("baseline satisfiable");
                for name in involved {
                    assert_eq!(
                        model_a.get(&slot_of(name)),
                        Some(&SlotKind::Ref),
                        "baseline (no guards): `{name}` should be Ref (max-ref, no source)"
                    );
                }

                // Solver B — same, plus BB1 guards from the Round-0 (all-Ref,
                // all-mutable) conflict. The guard `¬ref(issuer) ∨ ⋁¬ref(requirers)`
                // must demote >=1 involved slot off Ref.
                let solver_b = KindSolver::new(&slots);
                let (_b, selectors_b) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver_b,
                )
                .expect("BB1 guarded emission");
                add_coherence(&solver_b, &slots, f, &body);
                let conflicts = revalidate(&program, &slots, |_| true, true);
                materialize_guards(&solver_b, &conflicts);

                let model_b = solver_b
                    .model_kinds_relaxing(&selectors_b)
                    .expect("guarded satisfiable");
                let non_ref = involved
                    .iter()
                    .filter(|name| model_b.get(&slot_of(name)) != Some(&SlotKind::Ref))
                    .count();
                assert!(
                    non_ref >= 1,
                    "BB1 guards must force >=1 conflict-involved slot off Ref (all stayed Ref)"
                );
            },
        );
    }

    /// Caller-side out-param escape: a caller passes `&raw mut local` to a callee that
    /// writes `*out = malloc`. The malloc'd ownership flows back so the caller's `local`
    /// (depth-0 slot) becomes `Owning` after the call — the before/after caller state
    /// the legacy ownership analysis modeled, now carried by the uniform two-version
    /// use/def encoding at **precision 2** (the depth-1 signature var the `*out = malloc`
    /// escape flows through via the already-wired `call_args → call-matcher → exit-zip`
    /// path), rather than an output-param flag.
    ///
    /// `local` must be USED (returned) for the assertion to be non-vacuous: an unused
    /// owning `local` is a leak, which the solver models as non-owning (`Ref`) — the
    /// `bo-interproc-test-soundness` fixture trap. Closed by the §9.11 landing
    /// (precision-2 + `field ⟹ parent` suppression for struct-pointer pointees, so the
    /// escape lands without over-claiming borrowed struct pointers); the callee-side
    /// (`store_through_ptr_is_ref_over_owning`) and return-edge
    /// (`interproc_alloc_return_flows_owning`) escapes were already sound.
    #[test]
    fn caller_side_outparam_escape_flows_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn make(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}

pub unsafe fn caller() -> *mut core::ffi::c_void {
    let mut local: *mut core::ffi::c_void = core::ptr::null_mut();
    unsafe { make(&raw mut local) };
    local
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let make = function_by_name(&program, "make");
                let caller = function_by_name(&program, "caller");
                let make_body = tcx.mir_drops_elaborated_and_const_checked(make).borrow();
                let caller_body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("escape emission should run");
                add_coherence(&kind_solver, &slots, make, &make_body);
                add_coherence(&kind_solver, &slots, caller, &caller_body);

                let local = local_slot(&slots, caller, local_by_var_name(tcx, caller, "local"), 0);
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_eq!(
                    model.get(&local),
                    Some(&SlotKind::Owning),
                    "caller's `local` must become Owning after the out-param call"
                );
            },
        );
    }

    /// NON-REGRESSION (output-param contract, §9.8/§9.9): a borrowed struct pointer
    /// whose FIELD is malloc'd (`(*owner).data = malloc`) is a **field-ownership
    /// transfer**, NOT evidence that `owner` owns. Under the precision-2 escape
    /// support this must NOT over-claim `owner` as `Owning` — the `field ⟹ parent`
    /// suppression in `GlobalAssumptionApplier::apply` guarantees it. Without that
    /// suppression, global precision-2 forces `owner` `Owning` (the reverted §9.8
    /// regression, which the green suite otherwise MISSED — no other test exercises a
    /// borrowed struct-pointer param). This is the guard that keeps the escape support
    /// from re-introducing that over-claim.
    #[test]
    fn outparam_field_malloc_leaves_parent_ref() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub struct Holder {
    pub data: *mut core::ffi::c_void,
}

pub unsafe fn stash(owner: *mut Holder) {
    (*owner).data = unsafe { malloc(4) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let stash = function_by_name(&program, "stash");
                let stash_body = tcx.mir_drops_elaborated_and_const_checked(stash).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("stash emission should run");
                add_coherence(&kind_solver, &slots, stash, &stash_body);

                let owner = local_slot(&slots, stash, local_by_var_name(tcx, stash, "owner"), 0);
                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("satisfiable model");
                assert_ne!(
                    model.get(&owner),
                    Some(&SlotKind::Owning),
                    "borrowed struct-pointer `owner` must NOT be Owning (field malloc is field-ownership transfer, not parent ownership)"
                );
            },
        );
    }

    /// NON-REGRESSION (precision-2 depth-chain over-claim, from a Codex adversarial
    /// review of the BB-escape landing): two aliasing `&mut local as *mut *mut T` outer
    /// pointers plus the caller-side out-param escape. The hypothesised hazard: the
    /// escape makes depth1 (`local`) Owning; a borrow conflict on `p`/`q` demotes depth0
    /// off `Ref`; the coherence invariant `¬(raw(d) ∧ own(d+1))` then forces the outer
    /// pointer (to STACK `local`) Owning — a UAF-class over-claim outside the fixed
    /// field⟹parent path.
    ///
    /// It does NOT manifest: the escape's Owning source is retractable, so the solver
    /// LEAKS the deeper allocation (`local` settles `Raw`, making `own(depth1)` false and
    /// releasing the coherence pressure) rather than over-claiming the stack pointer.
    /// Verified equal at precision 1 and 2 — precision-2 adds no new over-claim on this
    /// shape. (The non-retractable `free(local)` variant goes UNSAT and
    /// `verify_to_fixpoint` DECLINES — a sound conservative fallback, no wrong `Owning`
    /// — at BOTH precisions, i.e. pre-existing, so it is not encoded here.) This guards
    /// the outer slots against ever becoming `Owning`.
    #[test]
    fn outparam_escape_aliasing_outer_ptr_never_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn make(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}

pub unsafe fn caller() -> *mut core::ffi::c_void {
    let mut local: *mut core::ffi::c_void = core::ptr::null_mut();
    let p = &mut local as *mut *mut core::ffi::c_void;
    let q = &mut local as *mut *mut core::ffi::c_void;
    make(p);
    *q = local;
    local
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let make = function_by_name(&program, "make");
                let caller = function_by_name(&program, "caller");
                let make_body = tcx.mir_drops_elaborated_and_const_checked(make).borrow();
                let caller_body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, make, &make_body);
                add_coherence(&solver, &slots, caller, &caller_body);

                // The shape is genuinely hazardous (round-0 aliasing borrow conflicts).
                let round0 = revalidate(&program, &slots, |_| true, true);
                assert!(
                    round0.get(&caller).is_some_and(|e| !e.is_empty()),
                    "shape must be hazardous (aliasing outer-pointer borrow conflicts)"
                );

                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");

                let p = local_slot(&slots, caller, local_by_var_name(tcx, caller, "p"), 0);
                let q = local_slot(&slots, caller, local_by_var_name(tcx, caller, "q"), 0);
                assert_ne!(
                    model.get(&p),
                    Some(&SlotKind::Owning),
                    "outer pointer `p` (to stack `local`) must never be Owning"
                );
                assert_ne!(
                    model.get(&q),
                    Some(&SlotKind::Owning),
                    "outer pointer `q` (to stack `local`) must never be Owning"
                );
            },
        );
    }

    /// PROBE (headline-reframing rationale): storing a global address through `*out`
    /// does NOT produce a round-0 *borrow* conflict — `&raw mut G` is a 'static-region
    /// raw borrow of a static, not a reference-aliasing loan. This confirms the
    /// `*out = g` exclusivity hazard is an *ownership* concern (a global is a
    /// non-owning source), not a borrow one, which is why BB1's headline uses the
    /// `proof_of_concept` reference-aliasing conflict instead.
    #[test]
    fn store_global_through_outparam_no_borrow_conflict() {
        run_compiler(
            r#"
static mut G: i32 = 0;

pub unsafe fn store_global(out: *mut *mut i32) {
    *out = &raw mut G;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let store_global = function_by_name(&program, "store_global");
                let slots = CrateSlots::build(&program);

                let conflicts = revalidate(&program, &slots, |_| true, true);
                let edges = conflicts
                    .get(&store_global)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                assert!(
                    edges.is_empty(),
                    "storing a global address through `*out` is not a borrow conflict; got {edges:?}"
                );
            },
        );
    }

    /// BB2-i (§8 CEGAR validate seam, union replay) through the BO `SlotRef` API.
    /// Two `&mut local` borrows: marking `x`'s slot `Raw` (production's iteration-1
    /// demotion) must, under replay, surface `y`'s conflict via the `tree_borrow_local`
    /// union — which plain `revalidate` (round-0, no union) does not. Mirrors the
    /// borrow-side `bb2i_replay_surfaces_union_induced_conflict` through the slot space.
    #[test]
    fn bb2i_revalidate_replaying_surfaces_union_induced_slot_conflict() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut local = 0i32;
    let x = &mut local as *mut i32;
    let y = &mut local as *mut i32;
    *x = 1;
    *y = 2;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let slots = CrateSlots::build(&program);
                let x = local_slot(&slots, f, local_by_var_name(tcx, f, "x"), 0);
                let y = local_slot(&slots, f, local_by_var_name(tcx, f, "y"), 0);

                let involves_y = |conflicts: &FxHashMap<LocalDefId, Vec<_>>| {
                    conflicts.get(&f).is_some_and(|edges: &Vec<SlotConflict>| {
                        edges
                            .iter()
                            .any(|e| e.issuer == Some(y) || e.requirers.contains(&y))
                    })
                };

                // Candidacy: `x` Raw, everything else Ref.
                let is_ref = |s: SlotRef| s != x;
                let is_raw = |s: SlotRef| s == x;

                // Round-0 `revalidate` (no union): `y = &mut local` alone is sound — no
                // conflict at all for `f`. Emptiness pins the union as the sole cause.
                let bb0 = revalidate(&program, &slots, is_ref, true);
                assert!(
                    bb0.get(&f).map_or(true, |edges| edges.is_empty()),
                    "round-0 revalidate must find NO conflict for f; got {bb0:?}"
                );

                // Replay: demote `x` + union(x, local) ⇒ `y` conflicts.
                let replay = revalidate_replaying(&program, &slots, is_ref, is_raw, true);
                assert!(
                    involves_y(&replay),
                    "replay must surface the union-induced y conflict; got {replay:?}"
                );
            },
        );
    }

    /// BB2-ii (§8 CEGAR iteration loop, Mode A). On the two-`&mut local` fixture a single
    /// demotion is *insufficient*: demoting one involved slot's `Raw` union surfaces a
    /// further conflict under replay, so `verify_to_fixpoint` must iterate (commit `¬ref`
    /// on a representative → re-solve) until conflict-free. The necessity is the contrast
    /// asserted below: a single-step demotion (what a BB1 one-shot reaches) leaves a
    /// residual, while the loop's fixpoint is clean.
    ///
    /// Because both pointers share one base (`local`) and the conflict is asymmetric
    /// (creating the 2nd borrow invalidates the 1st's live loan), each monotone single-slot
    /// commit's `tree_borrow_local` union re-surfaces a fresh self-conflict, cascading until
    /// ALL of this fn's pointer slots are `Raw` — a sound but non-minimal "give up on every
    /// borrow" fixpoint. (`bb2ii_preserves_independent_borrow` shows the loop instead keeps
    /// an *independent* borrow `Ref`; that test carries the non-vacuous clean assertion.)
    #[test]
    fn bb2ii_cegar_loop_reaches_union_clean_fixpoint() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut local = 0i32;
    let x = &mut local as *mut i32;
    let y = &mut local as *mut i32;
    *x = 1;
    *y = 2;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "f");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);

                // --- Necessity (deterministic): a single round-0 guard is NOT a fixpoint. ---
                // The round-0 conflict admits a single-slot demotion — its requirer alone —
                // that a one-shot disjunctive guard could pick (a valid max-ref choice). Yet
                // demoting just that slot induces a `tree_borrow_local` union that surfaces a
                // *further* conflict under replay. Only BB2-ii's re-validation loop catches
                // that. Asserting this directly (not via the solver) is robust to z3's
                // tie-break between the equally-good issuer/requirer demotions.
                let round0 = revalidate(&program, &slots, |_| true, true);
                let requirer = *round0
                    .get(&f)
                    .and_then(|edges| edges.first())
                    .and_then(|edge| edge.requirers.first())
                    .expect("round-0 conflict with a requirer");
                let residual = revalidate_replaying(
                    &program,
                    &slots,
                    |s: SlotRef| s != requirer,
                    |s: SlotRef| s == requirer,
                    true,
                );
                assert!(
                    residual.get(&f).is_some_and(|e| !e.is_empty()),
                    "demoting the round-0 requirer alone must leave a union-induced residual \
                     (the re-validation loop is necessary); got {residual:?}"
                );

                // --- BB2-ii loop reaches the clean fixpoint. ---
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges to a SAT model");

                // Non-trivial: the conflict forced a real demotion — ≥1 pointer slot is
                // Raw. Checking `== Raw` (not `!= Ref`) attributes it to the borrow path:
                // f has no ownership source, so a borrow commit is the only Raw producer
                // (an unrelated Owning slot could satisfy `!= Ref` without any demotion).
                let demoted_to_raw = body.local_decls.indices().any(|local| {
                    slots
                        .fn_local_slots
                        .get(&f)
                        .and_then(|u| u.slot_for_local_depth(local, 0))
                        .and_then(|sid| model.get(&SlotRef::Local(f, sid)))
                        == Some(&SlotKind::Raw)
                });
                assert!(
                    demoted_to_raw,
                    "fixpoint must demote >=1 pointer slot to Raw; got {model:?}"
                );

                // The accepted model is genuinely conflict-free under replay.
                let clean = revalidate_replaying(
                    &program,
                    &slots,
                    |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref),
                    |s: SlotRef| model.get(&s) == Some(&SlotKind::Raw),
                    true,
                );
                assert!(
                    clean.get(&f).map_or(true, |e| e.is_empty()),
                    "fixpoint model must be conflict-free under replay; got {clean:?}"
                );
            },
        );
    }

    /// BB2-ii non-vacuous fixpoint: an INDEPENDENT borrow (distinct base) stays Ref while
    /// the conflicting borrows demote. `p`,`q` both borrow `a` (conflict); `s` borrows `b`
    /// (independent). The loop demotes the `a`-chain but never commits `s`, so the fixpoint
    /// keeps `s` Ref — making the conflict-free assertion load-bearing: `s` is a live Ref
    /// candidate, so an empty residual is a genuine reconciliation, not the degenerate
    /// no-Ref-candidates-left reading of the single-base `f` case.
    #[test]
    fn bb2ii_preserves_independent_borrow() {
        run_compiler(
            r#"
pub unsafe fn g() {
    let mut a = 0i32;
    let mut b = 0i32;
    let p = &mut a as *mut i32;
    let q = &mut a as *mut i32;
    let s = &mut b as *mut i32;
    *p = 1;
    *q = 2;
    *s = 3;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "g");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let s = local_slot(&slots, f, local_by_var_name(tcx, f, "s"), 0);

                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");

                // The independent borrow `s` (distinct base `b`) is never committed → Ref.
                assert_eq!(
                    model.get(&s),
                    Some(&SlotKind::Ref),
                    "independent borrow `s` must remain Ref at the fixpoint; got {:?}",
                    model.get(&s)
                );

                // Non-vacuous clean: `s` is a live Ref candidate, so an empty residual means
                // a genuine reconciliation, not the no-Ref-candidates-left degeneracy.
                let clean = revalidate_replaying(
                    &program,
                    &slots,
                    |x: SlotRef| model.get(&x) == Some(&SlotKind::Ref),
                    |x: SlotRef| model.get(&x) == Some(&SlotKind::Raw),
                    true,
                );
                assert!(
                    clean.get(&f).map_or(true, |e| e.is_empty()),
                    "fixpoint must be conflict-free under replay; got {clean:?}"
                );
            },
        );
    }

    /// BB2-ii regression: a DEAD copy of a borrowed pointer (`let _r = p;`) must NOT panic
    /// the loop. coherence's flow-insensitive `equate(_r, p)` drags `_r` to Raw when `p` is
    /// committed off Ref, but `_r` is dead at the conflict so it is never a borrow demotion
    /// witness. `borrow_conflicts_replaying`'s former hard "Raw ⟹ witness" assert tripped
    /// on it; the relaxed *inert-ness* invariant lets the loop converge (the stray Raw `_r`
    /// is provably in no residual edge). C2Rust output is full of such dead pointer copies.
    #[test]
    fn bb2ii_dead_copy_does_not_panic() {
        run_compiler(
            r#"
pub unsafe fn dcu() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let _r = p;
    let q = &mut a as *mut i32;
    *p = 1;
    *q = 2;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "dcu");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("dead copy must not panic; loop converges");

                let clean = revalidate_replaying(
                    &program,
                    &slots,
                    |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref),
                    |s: SlotRef| model.get(&s) == Some(&SlotKind::Raw),
                    true,
                );
                assert!(
                    clean.get(&f).map_or(true, |e| e.is_empty()),
                    "dead-copy fixpoint must be conflict-free under replay; got {clean:?}"
                );
            },
        );
    }

    /// BB3-a (`Ref ⇒ loan`, source-based): a malloc result owns heap — it is not a borrow,
    /// so it must never be classified `Ref` (a reference to owned memory is unsound). Here
    /// `leak` mallocs and returns `&raw mut p`; the source conflicts with return
    /// finalization so the relax loop leaks it (¬Owning), and with no enforcement the
    /// max-ref objective floats the malloc result to `Ref`. `verify_to_fixpoint` must
    /// demote the **malloc-destination** slot to `Raw` (¬Owning leaked ∧ ¬Ref source).
    #[test]
    fn bb3a_leaked_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { malloc(8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                // The malloc-destination slot (robust to whether MIR names it `p` or a temp).
                let src = local_slot(&slots, f, call_destination(tcx, &body, "malloc"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&src),
                    Some(&SlotKind::Raw),
                    "leaked malloc source must be Raw (¬Owning leaked ∧ ¬Ref source); got {:?}",
                    model.get(&src)
                );
            },
        );
    }

    /// BB3-a regression guard: a reference PARAMETER must STAY `Ref`. Its backing borrow is
    /// the caller's (no local loan), so the earlier "loanless" predicate wrongly demoted it
    /// to `Raw`. The source-based predicate must not — a param is never a malloc-call
    /// destination, so it is never a source slot.
    #[test]
    fn bb3a_param_ref_stays_ref() {
        run_compiler(
            r#"
pub unsafe fn foo(p: *mut i32) -> i32 {
    *p = 1;
    *p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "foo");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let p = local_slot(&slots, f, Local::from_u32(1), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Ref),
                    "reference param `p` must stay Ref (not a malloc source); got {:?}",
                    model.get(&p)
                );
            },
        );
    }

    /// BB3-a regression guard (projected-store / `destination.as_local`): in `*out = malloc()`
    /// the store's base local `out` is a PARAM — `destination.local` would wrongly flag it as
    /// a source. The scan uses `destination.as_local()` (bare-local only), so `out` is never
    /// flagged and stays `Ref` (the malloc'd pointee is `Owning`, carried through `*out`).
    #[test]
    fn bb3a_store_malloc_through_outparam_keeps_param_ref() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn fill(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "fill");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                // `out` is param Local 1; its depth-0 slot is borrowed caller storage = Ref.
                let out = local_slot(&slots, f, Local::from_u32(1), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&out),
                    Some(&SlotKind::Ref),
                    "out-param `out` must stay Ref (its base is not a bare-local malloc dest); got {:?}",
                    model.get(&out)
                );
            },
        );
    }

    /// BB3-a (cast-following): the canonical C2Rust shape `let p = malloc(n) as *mut T`
    /// routes the allocation through a CAST (`_tmp = malloc()`, `_p = _tmp as *mut T`). The
    /// source scan must flag BOTH `_tmp` and the cast target, else a leaked alloc lets the
    /// cast target `p` float to `Ref` (a reference to owned heap). `p` must be `Raw`.
    #[test]
    fn bb3a_leaked_cast_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak_cast() -> *mut *mut i32 {
    let mut p = unsafe { malloc(8) } as *mut i32;
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak_cast");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                // `p` is the CAST TARGET (`malloc(...) as *mut i32`), not the call dest.
                let p = local_slot(&slots, f, local_by_var_name(tcx, f, "p"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Raw),
                    "leaked malloc CAST target `p` must be Raw (cast-following); got {:?}",
                    model.get(&p)
                );
            },
        );
    }

    /// BB3-a (allocator coverage): a leaked `calloc` source — not just `malloc` — must be
    /// demoted to `Raw`. Guards the `ALLOCATOR_NAMES` list against silently dropping an entry.
    #[test]
    fn bb3a_leaked_calloc_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn calloc(nmemb: usize, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak_calloc() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { calloc(1, 8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak_calloc");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let src = local_slot(&slots, f, call_destination(tcx, &body, "calloc"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&src),
                    Some(&SlotKind::Raw),
                    "leaked calloc source must be Raw; got {:?}",
                    model.get(&src)
                );
            },
        );
    }

    /// BB3-a (precision, `¬ref` not `raw`): an UNLEAKED malloc source (allocated then freed,
    /// no escape) must settle `Owning`, NOT be force-demoted to `Raw`. BB3-a's `== Ref` gate
    /// only fires on `Ref`-classified sources, so an `Owning` source is left alone.
    #[test]
    fn bb3a_unleaked_malloc_stays_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_free() {
    let p = unsafe { malloc(8) };
    unsafe { free(p) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "alloc_free");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let p = local_slot(&slots, f, call_destination(tcx, &body, "malloc"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&p),
                    Some(&SlotKind::Owning),
                    "unleaked malloc source must stay Owning (¬ref not raw); got {:?}",
                    model.get(&p)
                );
            },
        );
    }

    /// BB3-a (allocator coverage): `realloc` — which also sinks arg0 — must still be a
    /// source on its RESULT. Guards `ALLOCATOR_NAMES` against dropping `realloc`.
    #[test]
    fn bb3a_leaked_realloc_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak_realloc() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { realloc(core::ptr::null_mut(), 8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak_realloc");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let src = local_slot(&slots, f, call_destination(tcx, &body, "realloc"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&src),
                    Some(&SlotKind::Raw),
                    "leaked realloc source must be Raw; got {:?}",
                    model.get(&src)
                );
            },
        );
    }

    /// BB3-a (allocator coverage): `strdup`. Guards `ALLOCATOR_NAMES` against dropping it.
    #[test]
    fn bb3a_leaked_strdup_source_forced_raw() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn strdup(s: *const i8) -> *mut i8;
}

pub unsafe fn leak_strdup(s: *const i8) -> *mut *mut i8 {
    let mut p = unsafe { strdup(s) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "leak_strdup");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("ownership emission");
                add_coherence(&solver, &slots, f, &body);

                let src = local_slot(&slots, f, call_destination(tcx, &body, "strdup"), 0);
                let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
                    .expect("CEGAR converges");
                assert_eq!(
                    model.get(&src),
                    Some(&SlotKind::Raw),
                    "leaked strdup source must be Raw; got {:?}",
                    model.get(&src)
                );
            },
        );
    }

    /// BB3-a (extern gate): a crate-LOCAL fn named `malloc` is NOT an ownership source (the
    /// boundary only sources extern `ForeignItem` callees), so its call destination must not
    /// be flagged a malloc source — else its result would be wrongly demoted off `Ref`.
    #[test]
    fn bb3a_local_fn_named_malloc_is_not_a_source() {
        run_compiler(
            r#"
unsafe fn malloc(p: *mut i32) -> *mut i32 {
    p
}

pub unsafe fn use_it(x: *mut i32) {
    let q = unsafe { malloc(x) };
    *q = 1;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let use_it = function_by_name(&program, "use_it");
                let body = tcx.mir_drops_elaborated_and_const_checked(use_it).borrow();
                let slots = CrateSlots::build(&program);

                let q = local_slot(&slots, use_it, call_destination(tcx, &body, "malloc"), 0);
                let sources = collect_malloc_source_slots(program.tcx, &program.functions, &slots);
                assert!(
                    !sources.contains(&q),
                    "a crate-local fn named `malloc` must not be flagged a source; got {sources:?}"
                );
            },
        );
    }

    /// §NB-F (flipped from NB0's `should_panic` tripwire pin, per that fixture's
    /// own flip-loudly note): the minimized uthash shape — `is_null` on
    /// `&mut local as *mut S` where S has pointer fields, c2rust's
    /// `assert(&els[i] != NULL)` — must EMIT CLEANLY and solve. `call_is_null`
    /// now peels the leading outer-reference slot of an `is_ref` arg (the
    /// established boundary/memset peel idiom) instead of asserting it
    /// impossible. History: minimized from uthash tests/test68.rs during NB-R's
    /// bisect; fix approved with option (a) at the NB-R gate.
    #[test]
    fn nbf_uthash_isnull_ref_arg_emits() {
        run_compiler(
            r#"
#[derive(Copy, Clone)]
#[repr(C)]
pub struct el {
    pub id: i32,
    pub next: *mut el,
}

pub unsafe fn f() {
    let mut e = el { id: 0, next: 0 as *mut el };
    if !(&mut e as *mut el).is_null() {}
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let solver = KindSolver::new(&slots);
                let (_s, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &solver,
                )
                .expect("the uthash is_ref shape must emit cleanly");
                assert!(
                    solver.model_kinds_relaxing(&selectors).is_some(),
                    "the shape must also solve (no hidden contradiction from the peel)"
                );
            },
        );
    }

    /// §NB0 (hoisted BB3-a): `¬ref(source)` is a candidacy-independent domain invariant
    /// emitted EAGERLY — no model, however early, may classify a malloc-source slot
    /// `Ref`. Uses the leaked-alloc shape whose source previously FLOATED to `Ref`
    /// under the max-ref objective on the raw relax-solve (the lazy loop only demoted
    /// it in a later round; post-hoist there is no such window).
    #[test]
    fn nb0_emission_source_never_ref() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn leak() -> *mut *mut core::ffi::c_void {
    let mut p = unsafe { malloc(8) };
    &raw mut p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let leak = function_by_name(&program, "leak");
                let body = tcx.mir_drops_elaborated_and_const_checked(leak).borrow();
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let kind_solver = KindSolver::new(&slots);
                let (_stats, selectors) = emit_crate_ownership_constraints(
                    &crate_ctxt,
                    &slots,
                    &compute_origins(&program),
                    &kind_solver,
                )
                .expect("NB0 emission");

                let model = kind_solver
                    .model_kinds_relaxing(&selectors)
                    .expect("relax loop resolves the leak");
                let p = local_slot(&slots, leak, call_destination(tcx, &body, "malloc"), 0);
                assert_ne!(
                    model.get(&p),
                    Some(&SlotKind::Ref),
                    "a malloc-source slot may never be Ref, even on the first relax-solve \
                     (eager ¬ref); got {:?}",
                    model.get(&p)
                );
            },
        );
    }

    /// BB3-b (Owning under-report — investigated → unreachable). An `Owning` slot is a
    /// **non-candidate** in the replay (`is_candidate = is_ref ∨ is_raw`), so it issues and
    /// requires NO loan — it can never be named in a conflict edge. The investigation's
    /// concern was whether a borrow hazard *caused by* an Owning pointer could thereby be
    /// MISSED (an under-report ⇒ an unsound accepted model). It cannot: every borrow conflict
    /// needs ≥1 loan, every loan is issued by a `Ref`/`Raw` candidate, and `invalidates` keys
    /// on the borrowed `Place`'s base — NOT on that base's candidacy (`invalidates.rs:65-88`:
    /// a loan is skipped only for *immutable provenance*, which an Owning base, having none,
    /// lacks) — so a hazard around an Owning base still fires, attributed to the borrowing
    /// `Ref`. The remaining no-loan cases (`Owning↔Owning` double-free, `Owning↔Raw`) are the
    /// ownership-linearity layer's concern / sound in real Rust, never a borrow loan.
    ///
    /// This pins the load-bearing half empirically with TWO candidacies over a malloc base
    /// aliased by two conflicting `&mut *p` borrows:
    ///   (A) base = `Owning` (its source slots non-candidate), aliases = `Ref`;
    ///   (B) base = `Ref` candidate too (every pointer slot `Ref`).
    /// In BOTH, the residual is non-empty (the hazard stays visible — the anti-under-report
    /// guard: were the Owning case blind, (A) would go empty) and NO conflict edge ever names
    /// the malloc base. The owners are the `&mut *p` loan-issuer temporaries, never the
    /// dereferenced base: a pointer that is *borrowed through* is a loan TARGET, not a loan
    /// OWNER (`issuer`/`requirer` come from the `&mut` LHS, `borrow/mod.rs:448-465`). So the
    /// base is absent from the edges *irrespective of its kind* — which is precisely why the
    /// under-report cannot occur: classifying a slot `Owning` removes nothing a `Ref` slot
    /// would have contributed as an owner, because the base was never an owner to begin with.
    #[test]
    fn bb3b_owning_base_hazard_surfaces_on_ref_not_owning_slot() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn ob() {
    let p = unsafe { malloc(4) } as *mut i32;
    let x = &mut *p as *mut i32;
    let y = &mut *p as *mut i32;
    *x = 1;
    *y = 2;
    unsafe { free(p as *mut core::ffi::c_void) };
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let f = function_by_name(&program, "ob");
                let slots = CrateSlots::build(&program);

                // The malloc base (call destination + its cast target) = the Owning source set.
                let sources = collect_malloc_source_slots(program.tcx, &program.functions, &slots);
                assert!(
                    !sources.is_empty(),
                    "the malloc base must be recognized as a source"
                );

                // Assert, for one replay candidacy, that the hazard is visible AND no edge
                // names the malloc base. Returns nothing; panics on violation.
                let assert_hazard_excludes_base = |label: &str, base_is_ref: bool| {
                    let residual = revalidate_replaying(
                        &program,
                        &slots,
                        // (A) base Owning ⇒ a source slot is NOT a Ref candidate; (B) base Ref.
                        |s: SlotRef| base_is_ref || !sources.contains(&s),
                        |_s: SlotRef| false,
                        true,
                    );
                    assert!(
                        residual.get(&f).is_some_and(|e| !e.is_empty()),
                        "[{label}] the alias hazard must remain visible under replay (an empty \
                         residual would BE the under-report); got {residual:?}"
                    );
                    for edge in residual.get(&f).into_iter().flatten() {
                        for owner in edge.issuer.iter().chain(edge.requirers.iter()) {
                            assert!(
                                !sources.contains(owner),
                                "[{label}] the malloc base must never be a conflict OWNER (it is \
                                 a loan target, not a loan owner); got {owner:?} in {edge:?}"
                            );
                        }
                    }
                };

                // (A) Base classified Owning: the hazard is still seen, attributed to the Refs.
                assert_hazard_excludes_base("base=Owning", false);
                // (B) Base classified Ref too: the base STILL never appears — its exclusion is
                // structural (borrow target ≠ loan owner), not an artifact of being Owning. This
                // is the conclusive reason the Owning under-report is unreachable.
                assert_hazard_excludes_base("base=Ref", true);
            },
        );
    }

    // §8 BB3-b — the mixed-role under-report and its complete-by-construction fix. The four
    // fixtures below are the four reachable shapes successive adversarial rounds produced; each
    // is a local conflated to one flow-insensitive `Owning` slot that ALSO carries a reference
    // role. With the old "exclude `Owning` from the replay" candidacy each hid a real `Ref`-vs-
    // `Ref` aliasing; under `is_raw = model != Ref` (never exclude a non-`Ref` slot) none can.
    // All assert the same contract via `assert_mixed_role_no_hidden_aliasing` — see its doc.

    /// round-1: a local reused as a borrow (`p = &mut a`, aliasing `q`) then an allocation
    /// (`p = malloc()`). The DIRECT mixed-role shape.
    #[test]
    fn bb3b_mixed_role_direct_no_hidden_aliasing() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn mixed() {
    let mut a = 0i32;
    let mut p = &mut a as *mut i32;
    let q = &mut a as *mut i32;
    *p = 1;
    *q = 2;
    p = unsafe { malloc(4) } as *mut i32;
    unsafe { free(p as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_mixed_role_no_hidden_aliasing(tcx, "mixed", "p"),
        );
    }

    /// round-2: a caller local made `Owning` by an allocator WRAPPER's owned return
    /// (`make() { malloc() }`) — `Owning` without being a direct malloc source.
    #[test]
    fn bb3b_mixed_role_owned_return_no_hidden_aliasing() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

unsafe fn make() -> *mut i32 {
    (unsafe { malloc(4) }) as *mut i32
}

pub unsafe fn mixed() {
    let mut a = 0i32;
    let mut p = &mut a as *mut i32;
    let q = &mut a as *mut i32;
    *p = 1;
    *q = 2;
    p = unsafe { make() };
    unsafe { free(p as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_mixed_role_no_hidden_aliasing(tcx, "mixed", "p"),
        );
    }

    /// round-3: a reborrow (`s = &mut *p`) whose aliasing of `a` is UNION-INDUCED — it only
    /// materializes after `p` is demoted and `p`~`a` unions, so `s` is not a round-0 conflict
    /// owner (round-0 all-`Ref` has no `tree_borrow_local` unions).
    #[test]
    fn bb3b_mixed_role_union_induced_no_hidden_aliasing() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn unioncase() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    a = 10;
    let mut s = &mut *p as *mut i32;
    let t = &mut a as *mut i32;
    *s = 1;
    *t = 2;
    s = (unsafe { malloc(4) }) as *mut i32;
    unsafe { free(s as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_mixed_role_no_hidden_aliasing(tcx, "unioncase", "s"),
        );
    }

    /// round-4: a derived pointer via `offset` (`s = p.offset(0)`) — a reference role the borrow
    /// replay propagates through a pointer-method call, which a syntactic Ref/RawPtr+cast/copy
    /// scan does not. The complete-by-construction candidacy needs no such scan.
    #[test]
    fn bb3b_mixed_role_offset_no_hidden_aliasing() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn offcase() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    a = 10;
    let mut s = unsafe { p.offset(0) };
    let t = &mut a as *mut i32;
    *s = 1;
    *t = 2;
    s = (unsafe { malloc(4) }) as *mut i32;
    unsafe { free(s as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_mixed_role_no_hidden_aliasing(tcx, "offcase", "s"),
        );
    }

    // ===================================================================================
    // §8 BB-parity-borrow — differential parity of BO's §8 borrow classification against
    // the production borrow analysis. Criterion (see task/plan docs):
    //   HA1 (hard, soundness): BO's accepted model is a replaying-borrow fixpoint
    //     (`revalidate_replaying` finds no residual) — catches BO UNDER-demotion. This is
    //     BO's own accept condition, so it is a stability/regression guard, NOT an
    //     independent oracle (the union replay is unavoidable for a partial candidacy).
    //     Blind to the RESIDUAL Owning-issuer no-loan case (an `Owning` slot issues no loan,
    //     so a conflict caused by its exclusivity is invisible to the replay AND to the
    //     production greedy driver) — inherited from BO, guardrail-tolerated. Distinct from
    //     the exclusion-based mixed-role under-report BB3-b closed by construction.
    //   Witness-specific non-vacuity (hard, production-only, INDEPENDENT): every local in
    //     `demoted` must be demoted by the production greedy driver
    //     (`demote_pointers_iterative_with_fields` from all-Ref, sharing only
    //     `borrow_inference`) — ties the gate to the fixture's INTENDED conflict witnesses
    //     (not a decoy demotion elsewhere) and proves HA1 is not vacuously clean.
    //   Control survivors (hard): every local in `kept_ref` must stay `Ref` in BO's model —
    //     enforces a control's stated claim (e.g. distinct-base borrows survive), so a
    //     wholesale all-`Raw` collapse cannot pass silently.
    //   Precision report (NON-failing): BO non-`Ref` vs production-demoted, attributed.
    //     Over-demotion (borrow-`Raw` ∉ production, e.g. coherence-drag / all-`Raw` collapse)
    //     is SAFE (precision, not soundness), so it is reported, never asserted.
    fn assert_borrow_parity(tcx: TyCtxt<'_>, fn_name: &str, demoted: &[&str], kept_ref: &[&str]) {
        let program = collect_program(tcx);
        let f = function_by_name(&program, fn_name);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_s, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("BB-parity: ownership emission");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
            .expect("BB-parity: BO CEGAR must converge (Some) on the corpus");

        // HA1 — soundness gate: no residual conflict under the COMPLETE replay (every
        // non-`Ref` slot a candidate, matching verify_to_fixpoint's own acceptance). A
        // residual would mean BO left a surviving `Ref` that still aliases (under-demotion).
        let residual = revalidate_replaying(
            &program,
            &slots,
            |s: SlotRef| model.get(&s) == Some(&SlotKind::Ref),
            |s: SlotRef| model.get(&s) != Some(&SlotKind::Ref),
            true,
        );
        assert!(
            residual.values().all(|edges| edges.is_empty()),
            "BB-parity HA1: BO's accepted model has a residual borrow conflict (under-demotion); \
             got {residual:?}"
        );

        // Independent production greedy driver from all-Ref; map its demoted locals to depth-0
        // slots. Shares only `borrow_inference`, never `borrow_conflicts_replaying`.
        let mut ctxt = GBorrowInferCtxt::new(&program, |_| |_| true, |_| |_| true);
        let d_prod = demote_pointers_iterative_with_fields(&program, &mut ctxt);
        let mut prod_slots: rustc_hash::FxHashSet<SlotRef> = rustc_hash::FxHashSet::default();
        for (g, dem) in &d_prod.locals {
            let Some(universe) = slots.fn_local_slots.get(g) else {
                continue;
            };
            for local in dem.iter() {
                if let Some(sid) = universe.slot_for_local_depth(local, 0) {
                    prod_slots.insert(SlotRef::Local(*g, sid));
                }
            }
        }

        // Witness-specific NON-VACUITY (Codex HIGH): each named local the INDEPENDENT
        // production driver MUST demote — ties the gate to the fixture's INTENDED conflict
        // witnesses, not a decoy demotion elsewhere in the program.
        for nm in demoted {
            let sref = local_slot(&slots, f, local_by_var_name(tcx, f, nm), 0);
            assert!(
                prod_slots.contains(&sref),
                "BB-parity: fixture `{fn_name}` expected the independent production driver to \
                 demote `{nm}` (its intended conflict witness), but it did not"
            );
        }

        // CONTROL survivors (Codex MEDIUM): each named local MUST stay `Ref` in BO's model,
        // enforcing the control's stated claim so a wholesale all-`Raw` collapse cannot pass.
        for nm in kept_ref {
            let sref = local_slot(&slots, f, local_by_var_name(tcx, f, nm), 0);
            assert_eq!(
                model.get(&sref),
                Some(&SlotKind::Ref),
                "BB-parity: fixture `{fn_name}` requires `{nm}` to stay `Ref` in BO's model; \
                 got {:?}",
                model.get(&sref)
            );
        }

        // Precision report (NON-failing). Over-demotion (borrow-`Raw` ∉ production) is SAFE.
        let sources = collect_malloc_source_slots(program.tcx, &program.functions, &slots);
        let (mut borrow_raw, mut owning, mut leaked_raw, mut over_demote) = (0usize, 0, 0, 0);
        for (s, kind) in &model {
            if !matches!(s, SlotRef::Local(..)) {
                continue;
            }
            match kind {
                SlotKind::Owning => owning += 1,
                SlotKind::Raw if sources.contains(s) => leaked_raw += 1,
                SlotKind::Raw => {
                    borrow_raw += 1;
                    if !prod_slots.contains(s) {
                        over_demote += 1;
                    }
                }
                SlotKind::Ref => {}
            }
        }
        let bo_precision_wins = prod_slots
            .iter()
            .filter(|s| model.get(*s) == Some(&SlotKind::Ref))
            .count();
        eprintln!(
            "[BB-parity] borrow_raw={borrow_raw} owning={owning} leaked_raw={leaked_raw} \
             prod_demoted={} over_demote(safe)={over_demote} bo_precision_wins={bo_precision_wins}",
            prod_slots.len()
        );
    }

    /// Two `&mut` of the SAME local base alias — the canonical demote. BO collapses to
    /// all-`Raw`; production demotes both. HA1 holds; non-vacuous.
    #[test]
    fn bbparity_alias_two_mut_same_base() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let x = &mut a as *mut i32;
    let y = &mut a as *mut i32;
    *x = 1;
    *y = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["x", "y"], &[]),
        );
    }

    /// Copy-alias chain: `q = p` copies a borrow of `a` that also has a second `&mut a`.
    /// Exercises the round-0 (non-replay) conflict path. Non-vacuous.
    #[test]
    fn bbparity_alias_copy_chain() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let q = p;
    let r = &mut a as *mut i32;
    *q = 1;
    *r = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["q", "r"], &[]),
        );
    }

    /// Conflicting a-chain (p,q) alongside a DISTINCT-base borrow s that must stay live —
    /// proves the clean residual reconciles with a surviving candidate, not an all-`Raw`
    /// cascade. Non-vacuous.
    #[test]
    fn bbparity_independent_borrow_amid_conflict() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let mut b = 0i32;
    let p = &mut a as *mut i32;
    let q = &mut a as *mut i32;
    let s = &mut b as *mut i32;
    *p = 1;
    *q = 2;
    *s = 3;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["p", "q"], &["s"]),
        );
    }

    /// Reborrow-through-`*p` aliasing: `s`,`t` are both `&mut *p`, so they alias directly.
    /// Production demotes `s`,`t`; the base `p` stays `Ref` (a loan target, not an owner) —
    /// a distinct SHAPE from two `&mut` of a local, exercising reborrow provenance.
    /// NON-vacuous. NOTE round-0 already sees this conflict, so it does NOT isolate the
    /// union-replay path; a genuine union-only parity fixture (round-0-empty vs
    /// replay-non-empty) is deferred to the follow-up — `bb2i_*` covers union replay
    /// differentially today.
    #[test]
    fn bbparity_reborrow_deref_aliasing() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let s = &mut *p as *mut i32;
    let t = &mut *p as *mut i32;
    *s = 1;
    *t = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["s", "t"], &["p"]),
        );
    }

    /// Pointer-arithmetic via the WHITELISTED `offset` (is_borrowing_method): `q = p.offset(0)`
    /// aliases p, so a loan + union form and the conflict surfaces. Non-vacuous. (The `add`
    /// whitelist-miss contrast needs a no-base-loan shape; deferred to the follow-up.)
    #[test]
    fn bbparity_offset_derived_conflict() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let q = unsafe { p.offset(0) };
    *p = 1;
    *q = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["q"], &[]),
        );
    }

    /// Mixed ownership + borrow: the malloc base `p` is `Owning` (a source) while its two
    /// reborrows x,y are borrow-`Raw`. The core reconciliation — production demotes {x,y}
    /// (blind to p's ownership), BO carries `Owning` on p (filtered from the borrow axis).
    /// Non-vacuous. Byte-identical to `bb3b_owning_base_hazard`'s `ob`.
    #[test]
    fn bbparity_malloc_base_aliased() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn f() {
    let p = unsafe { malloc(4) } as *mut i32;
    let x = &mut *p as *mut i32;
    let y = &mut *p as *mut i32;
    *x = 1;
    *y = 2;
    unsafe { free(p as *mut core::ffi::c_void) };
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["x", "y"], &[]),
        );
    }

    /// Dead copy `let _r = p`: coherence's flow-insensitive equate drags `_r` to `Raw` that
    /// production's witness-only collection leaves un-demoted (the confirmed HA2-⊆ breaker).
    /// HA1 still holds; the report's over-demote counter is non-zero (SAFE precision loss,
    /// not a soundness bug). Non-vacuous.
    #[test]
    fn bbparity_dead_copy() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let p = &mut a as *mut i32;
    let _r = p;
    let q = &mut a as *mut i32;
    *p = 1;
    *q = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &["p", "q"], &[]),
        );
    }

    /// CONTROL: two `&mut` of DISTINCT local bases must both stay `Ref` — production demotes
    /// nothing. The false-positive guard (multiplicity of `&mut` alone must not demote).
    #[test]
    fn bbparity_independent_distinct_bases() {
        run_compiler(
            r#"
pub unsafe fn f() {
    let mut a = 0i32;
    let mut b = 0i32;
    let x = &mut a as *mut i32;
    let y = &mut b as *mut i32;
    *x = 1;
    *y = 2;
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &[], &["x", "y"]),
        );
    }

    /// CONTROL: pure allocation, no borrow — production demotes {} while BO settles p
    /// `Owning`. Proves a naive set-equality gate is wrong and the ownership axis is
    /// separated from borrow. Vacuous on the borrow axis (report shows owning≥1).
    #[test]
    fn bbparity_unleaked_malloc() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn f() {
    let p = unsafe { malloc(4) };
    unsafe { free(p) };
}
"#,
            |tcx| assert_borrow_parity(tcx, "f", &[], &[]),
        );
    }

    /// CONTROL: a crate-local fn named `malloc` is NOT an allocator source (the extern gate),
    /// so `q` stays `Ref`; both drivers demote nothing. The source-detector correctness
    /// anchor. Vacuous.
    #[test]
    fn bbparity_local_fn_named_malloc() {
        run_compiler(
            r#"
unsafe fn malloc(p: *mut i32) -> *mut i32 {
    p
}

pub unsafe fn use_it(x: *mut i32) {
    let q = unsafe { malloc(x) };
    *q = 1;
}
"#,
            |tcx| assert_borrow_parity(tcx, "use_it", &[], &["q"]),
        );
    }

    /// A depth-zero local copy whose source is forced `Owning` has two sound readings:
    /// the current equal `Owning/Owning` arm, or the phase-1 shared-lend
    /// `Ref/Owning` arm. The max-Ref objective must choose the latter.
    #[test]
    fn copy_lend_owner_source_prefers_shared_destination() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let solver = KindSolver::new(&slots);

                let p = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "p"),
                    0,
                );
                let q = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "q"),
                    0,
                );
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                solver.assume(p, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
                assert_eq!(
                    model.get(&q),
                    Some(&SlotKind::Ref),
                    "an eligible owning-source local copy must select the shared lend arm"
                );
            },
        );
    }

    /// The new disjunction must not disturb the existing equal-kind reading when the source is
    /// pinned Raw: the owner-to-reference lend arm is unavailable without `rhs.own`. Pinning Raw
    /// makes this non-vacuous — without the equality arm, the max-Ref objective would choose q=Ref.
    #[test]
    fn copy_lend_nonowning_source_keeps_equal_raw() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let solver = KindSolver::new(&slots);

                let p = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "p"),
                    0,
                );
                let q = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "q"),
                    0,
                );
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                solver.assume(p, SlotKind::Raw);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&p), Some(&SlotKind::Raw));
                assert_eq!(model.get(&q), Some(&SlotKind::Raw));
            },
        );
    }

    /// Lend selection is a function of the one-hot kind model, not assertion order. Repeated
    /// solves and reversing the order in which function bodies add their copy constraints must
    /// therefore produce the same selected destination kinds.
    #[test]
    fn copy_lend_choice_is_stable_across_solves_and_function_registration_order() {
        run_compiler(
            r#"
pub unsafe fn copy_a(pa: *const i32) -> i32 {
    let qa = pa;
    let value = unsafe { *qa };
    value
}

pub unsafe fn copy_b(pb: *const i32) -> i32 {
    let qb = pb;
    let value = unsafe { *qb };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_a = function_by_name(&program, "copy_a");
                let copy_b = function_by_name(&program, "copy_b");
                let pairs = [
                    (
                        local_slot(&slots, copy_a, local_by_var_name(tcx, copy_a, "pa"), 0),
                        local_slot(&slots, copy_a, local_by_var_name(tcx, copy_a, "qa"), 0),
                    ),
                    (
                        local_slot(&slots, copy_b, local_by_var_name(tcx, copy_b, "pb"), 0),
                        local_slot(&slots, copy_b, local_by_var_name(tcx, copy_b, "qb"), 0),
                    ),
                ];

                let solve = |order: [LocalDefId; 2]| {
                    let solver = KindSolver::new(&slots);
                    let copy_lends = FxHashSet::from_iter(
                        pairs
                            .iter()
                            .map(|(source, destination)| CopyLendPair::new(*destination, *source)),
                    );
                    for did in order {
                        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                        add_coherence_with_copy_lends(&solver, &slots, did, &body, &copy_lends);
                    }
                    for (source, _) in pairs {
                        solver.assume(source, SlotKind::Owning);
                    }
                    assert_eq!(solver.check(), SatResult::Sat);
                    let first = solver.model_kinds().expect("first satisfiable model");
                    let second = solver.model_kinds().expect("repeated satisfiable model");
                    let read = |model: &FxHashMap<SlotRef, SlotKind>| {
                        pairs
                            .iter()
                            .map(|(source, destination)| {
                                (model.get(source).copied(), model.get(destination).copied())
                            })
                            .collect::<Vec<_>>()
                    };
                    assert_eq!(read(&first), read(&second), "repeated solve drifted");
                    read(&first)
                };

                let forward = solve([copy_a, copy_b]);
                let reverse = solve([copy_b, copy_a]);
                assert_eq!(
                    forward, reverse,
                    "function registration order changed the model"
                );
                assert_eq!(
                    forward,
                    vec![
                        (Some(SlotKind::Owning), Some(SlotKind::Ref)),
                        (Some(SlotKind::Owning), Some(SlotKind::Ref)),
                    ]
                );
            },
        );
    }

    /// R1 RED: once the derived lend guard is true, Copy and Move have the same ownership
    /// consequence. The destination is non-owning and the source owns both before and after the
    /// site; the current `push_linear`/move split must not remain active on this branch.
    #[test]
    fn copy_lend_guarded_ownership_keeps_source_and_forbids_destination_for_copy_and_move() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                for ensure_move in [false, true] {
                    let program = collect_program(tcx);
                    let slots = CrateSlots::build(&program);
                    let copy_local = function_by_name(&program, "copy_local");
                    let p = local_slot(
                        &slots,
                        copy_local,
                        local_by_var_name(tcx, copy_local, "p"),
                        0,
                    );
                    let q = local_slot(
                        &slots,
                        copy_local,
                        local_by_var_name(tcx, copy_local, "q"),
                        0,
                    );
                    let solver = KindSolver::new(&slots);
                    solver.lend_or_equate(q, p);
                    solver.assume(p, SlotKind::Owning);
                    let lend = solver.lend_guard(q, p);

                    let mut database = BoOwnDatabase::new(solver.optimize(), solver.tracker());
                    let mut var_gen = Gen::new();
                    let mut vars = database.new_vars(&mut var_gen, 3);
                    let destination_def = vars.next().expect("destination def");
                    let source_def = vars.next().expect("source def");
                    let source_use = vars.next().expect("source use");
                    database.push_guarded_copy(
                        &lend,
                        destination_def,
                        source_def,
                        source_use,
                        ensure_move,
                    );

                    let destination_ast = database.own_bool(destination_def).clone();
                    let source_def_ast = database.own_bool(source_def).clone();
                    let source_use_ast = database.own_bool(source_use).clone();
                    solver.link_own(q, &destination_ast);
                    solver.link_own(p, &z3::ast::Bool::or(&[&source_use_ast, &source_def_ast]));
                    drop(database);

                    assert_eq!(solver.check(), SatResult::Sat, "ensure_move={ensure_move}");
                    let model = solver.optimize().get_model().expect("ownership model");
                    let owned = |ast: &z3::ast::Bool| {
                        model
                            .eval(ast, true)
                            .and_then(|value| value.as_bool())
                            .unwrap_or(false)
                    };
                    assert!(!owned(&destination_ast), "ensure_move={ensure_move}");
                    assert!(owned(&source_use_ast), "ensure_move={ensure_move}");
                    assert!(owned(&source_def_ast), "ensure_move={ensure_move}");
                }
            },
        );
    }

    /// R1 MIR-plumbing RED: the ownership emitter and coherence must consume the same explicit
    /// pair plan. The accepted model's per-version readout at the copy site pins the lend branch,
    /// not merely the slot-global kind result.
    #[test]
    fn copy_lend_mir_transfer_exports_source_retention_and_nonowning_destination() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let p_local = local_by_var_name(tcx, copy_local, "p");
                let q_local = local_by_var_name(tcx, copy_local, "q");
                let p = local_slot(&slots, copy_local, p_local, 0);
                let q = local_slot(&slots, copy_local, q_local, 0);
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                let solver = KindSolver::new(&slots);

                let (model, export) = with_bo_export(|| {
                    let (_stats, selectors) = emit_crate_ownership_constraints_with_copy_lends(
                        &crate_ctxt,
                        &slots,
                        &compute_origins(&program),
                        &solver,
                        &copy_lends,
                    )
                    .expect("ownership emission");
                    add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                    solver.assume(p, SlotKind::Owning);
                    solver.model_kinds_relaxing(&selectors)
                });
                let model = model.expect("lend model must be satisfiable");
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
                assert_eq!(model.get(&q), Some(&SlotKind::Ref));

                let copy_location = body
                    .basic_blocks
                    .iter_enumerated()
                    .find_map(|(block, data)| {
                        data.statements.iter().enumerate().find_map(
                            |(statement_index, statement)| {
                                let StatementKind::Assign(box (lhs, Rvalue::Use(operand))) =
                                    &statement.kind
                                else {
                                    return None;
                                };
                                let (Operand::Copy(rhs) | Operand::Move(rhs)) = operand else {
                                    return None;
                                };
                                (lhs.as_local() == Some(q_local) && rhs.as_local() == Some(p_local))
                                    .then_some(Location {
                                        block,
                                        statement_index,
                                    })
                            },
                        )
                    })
                    .expect("q = p MIR copy location");
                let copy_key = location_key(copy_location);
                let site = |local| {
                    export
                        .version_sites
                        .iter()
                        .find(|site| {
                            site.fn_did == copy_local
                                && site.local == local
                                && site.location == copy_key
                        })
                        .unwrap_or_else(|| panic!("missing version site for {local:?}"))
                };
                let q_site = site(q_local);
                let p_site = site(p_local);
                let owns = export.version_owns.as_ref().expect("per-version model");
                let owned = |var: Option<Var>| var.is_some_and(|var| owns[var]);
                assert!(!owned(q_site.def_var), "lend destination must not own");
                assert!(owned(p_site.use_var), "lend source must own before copy");
                assert!(owned(p_site.def_var), "lend source must retain ownership");
            },
        );
    }

    /// R3/R1 CopyForDeref RED at the source-only semantic seam. A rustc deref temp has no
    /// ownership signature, so this arm must preserve the source without inventing a destination
    /// ownership variable.
    #[test]
    fn copy_lend_guarded_copy_for_deref_keeps_source_ownership() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let p = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "p"),
                    0,
                );
                let q = local_slot(
                    &slots,
                    copy_local,
                    local_by_var_name(tcx, copy_local, "q"),
                    0,
                );
                let solver = KindSolver::new(&slots);
                solver.lend_or_equate(q, p);
                solver.assume(p, SlotKind::Owning);
                let lend = solver.lend_guard(q, p);

                let mut database = BoOwnDatabase::new(solver.optimize(), solver.tracker());
                let mut var_gen = Gen::new();
                let mut vars = database.new_vars(&mut var_gen, 2);
                let source_def = vars.next().expect("source def");
                let source_use = vars.next().expect("source use");
                database.push_guarded_lend_source(&lend, source_def, source_use);

                let source_def_ast = database.own_bool(source_def).clone();
                let source_use_ast = database.own_bool(source_use).clone();
                solver.link_own(p, &z3::ast::Bool::or(&[&source_use_ast, &source_def_ast]));
                drop(database);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.optimize().get_model().expect("ownership model");
                let owned = |ast: &z3::ast::Bool| {
                    model
                        .eval(ast, true)
                        .and_then(|value| value.as_bool())
                        .unwrap_or(false)
                };
                assert!(owned(&source_use_ast));
                assert!(owned(&source_def_ast));
            },
        );
    }

    /// Required witness 1 RED: the selected lend must survive into the final replay as a typed
    /// loan at the exact copy location. A syntactic copy loan without the `CopyLend` class does not
    /// discharge R3 because later invalidation cannot apply the new semantics selectively.
    #[test]
    fn copy_lend_emits_replay_loan() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *const i32) -> i32 {
    let q = p;
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let p_local = local_by_var_name(tcx, copy_local, "p");
                let q_local = local_by_var_name(tcx, copy_local, "q");
                let p = local_slot(&slots, copy_local, p_local, 0);
                let q = local_slot(&slots, copy_local, q_local, 0);
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                let solver = KindSolver::new(&slots);

                let (model, export) = with_bo_export(|| {
                    let (_stats, selectors) = emit_crate_ownership_constraints_with_copy_lends(
                        &crate_ctxt,
                        &slots,
                        &origins,
                        &solver,
                        &copy_lends,
                    )
                    .expect("ownership emission");
                    add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                    solver.assume(p, SlotKind::Owning);
                    let model = solver
                        .model_kinds_relaxing(&selectors)
                        .expect("lend model must be satisfiable");
                    let selected = selected_copy_lend_sites(&program, &slots, &copy_lends, &model);
                    let conflicts = borrow_conflicts_replaying_with_flows_and_copy_lends(
                        &program,
                        origins.native_flows(),
                        |did| {
                            let model = &model;
                            let slots = &slots;
                            move |local| {
                                slots
                                    .fn_local_slots
                                    .get(&did)
                                    .and_then(|universe| universe.slot_for_local_depth(local, 0))
                                    .map(|slot| SlotRef::Local(did, slot))
                                    .is_some_and(|slot| model.get(&slot) == Some(&SlotKind::Ref))
                            }
                        },
                        |did| {
                            let model = &model;
                            let slots = &slots;
                            move |local| {
                                slots
                                    .fn_local_slots
                                    .get(&did)
                                    .and_then(|universe| universe.slot_for_local_depth(local, 0))
                                    .map(|slot| SlotRef::Local(did, slot))
                                    .is_some_and(|slot| model.get(&slot) != Some(&SlotKind::Ref))
                            }
                        },
                        |_| |_| false,
                        &[],
                        &selected,
                    );
                    assert!(
                        conflicts.values().all(Vec::is_empty),
                        "conflict-free copy fixture must remain clean: {conflicts:?}"
                    );
                    model
                });
                assert_eq!(model.get(&p), Some(&SlotKind::Owning));
                assert_eq!(model.get(&q), Some(&SlotKind::Ref));
                assert!(
                    export.loans.iter().any(|loan| {
                        loan.class == LoanClass::CopyLend
                            && loan.key.fn_did == copy_local
                            && loan.key.borrower
                                == crate::analyses::borrow_ownership::export::BorrowerKind::Assign {
                                    owner:
                                        crate::analyses::borrow_ownership::export::OwnerKey::Local(
                                            q_local.as_u32(),
                                        ),
                                }
                    }),
                    "selected lend emitted no typed replay loan: {:?}",
                    export.loans
                );
            },
        );
    }

    /// Required witness 2 RED: CopyLend is shared, so a write through the retained owner while
    /// the destination loan is live must invalidate it even though Foster marks the destination
    /// read-only. The witnessed edge must name the source local as the invalidator.
    #[test]
    fn copy_lend_source_write_conflicts() {
        run_compiler(
            r#"
pub unsafe fn copy_local(p: *mut i32) -> i32 {
    let q = p;
    unsafe { *p = 7 };
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let p_local = local_by_var_name(tcx, copy_local, "p");
                let q_local = local_by_var_name(tcx, copy_local, "q");
                let p = local_slot(&slots, copy_local, p_local, 0);
                let q = local_slot(&slots, copy_local, q_local, 0);
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                let solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints_with_copy_lends(
                    &crate_ctxt,
                    &slots,
                    &origins,
                    &solver,
                    &copy_lends,
                )
                .expect("ownership emission");
                add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                solver.assume(p, SlotKind::Owning);
                let model = solver
                    .model_kinds_relaxing(&selectors)
                    .expect("lend model must be satisfiable");
                let selected = selected_copy_lend_sites(&program, &slots, &copy_lends, &model);
                let is_ref = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) == Some(&SlotKind::Ref))
                    }
                };
                let is_raw = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) != Some(&SlotKind::Ref))
                    }
                };
                let witnessed = borrow_conflicts_replaying_witnessed_with_copy_lends(
                    &program,
                    origins.native_flows(),
                    is_ref,
                    is_raw,
                    |_| |_| false,
                    &[],
                    &selected,
                );
                let edges = witnessed
                    .get(&copy_local)
                    .expect("source write must produce a witnessed conflict");
                assert!(
                    edges
                        .iter()
                        .any(|edge| edge.invalidators.contains(&p_local)),
                    "source local was not recorded as invalidator: {edges:?}"
                );
            },
        );
    }

    /// Required witness 3 RED: the triptych's raw seam. A direct foreign-C `free(owner)` while
    /// the shared CopyLend remains live until a later alias use must be reported by the oracle.
    #[test]
    fn copy_lend_triptych_free_then_use_conflicts() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn free(p: *mut i32);
}

pub unsafe fn copy_local(p: *mut i32) -> i32 {
    let q = p;
    unsafe { free(p) };
    let value = unsafe { *q };
    value
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let crate_ctxt = CrateCtxt::new(&program);
                let origins = compute_origins(&program);
                let copy_local = function_by_name(&program, "copy_local");
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(copy_local)
                    .borrow();
                let p_local = local_by_var_name(tcx, copy_local, "p");
                let q_local = local_by_var_name(tcx, copy_local, "q");
                let p = local_slot(&slots, copy_local, p_local, 0);
                let q = local_slot(&slots, copy_local, q_local, 0);
                let copy_lends = FxHashSet::from_iter([CopyLendPair::new(q, p)]);
                let solver = KindSolver::new(&slots);

                let (_stats, selectors) = emit_crate_ownership_constraints_with_copy_lends(
                    &crate_ctxt,
                    &slots,
                    &origins,
                    &solver,
                    &copy_lends,
                )
                .expect("ownership emission");
                add_coherence_with_copy_lends(&solver, &slots, copy_local, &body, &copy_lends);
                solver.assume(p, SlotKind::Owning);
                let model = solver
                    .model_kinds_relaxing(&selectors)
                    .expect("lend model must be satisfiable");
                let selected = selected_copy_lend_sites(&program, &slots, &copy_lends, &model);
                let is_ref = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) == Some(&SlotKind::Ref))
                    }
                };
                let is_raw = |did| {
                    let model = &model;
                    let slots = &slots;
                    move |local| {
                        slots
                            .fn_local_slots
                            .get(&did)
                            .and_then(|universe| universe.slot_for_local_depth(local, 0))
                            .map(|slot| SlotRef::Local(did, slot))
                            .is_some_and(|slot| model.get(&slot) != Some(&SlotKind::Ref))
                    }
                };
                let witnessed = borrow_conflicts_replaying_witnessed_with_copy_lends(
                    &program,
                    origins.native_flows(),
                    is_ref,
                    is_raw,
                    |_| |_| false,
                    &[],
                    &selected,
                );
                let edges = witnessed
                    .get(&copy_local)
                    .expect("free-before-use must produce a witnessed conflict");
                assert!(
                    edges
                        .iter()
                        .any(|edge| edge.invalidators.contains(&p_local)),
                    "free argument was not recorded as invalidator: {edges:?}"
                );
            },
        );
    }

    #[test]
    fn copy_propagates_kind() {
        run_compiler(
            r#"
pub unsafe fn copy_fn(p: *mut i32) -> *mut i32 {
    p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_fn = function_by_name(&program, "copy_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(copy_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, copy_fn, &body);

                let ret = local_slot(&slots, copy_fn, Local::from_u32(0), 0);
                let p = local_slot(&slots, copy_fn, Local::from_u32(1), 0);
                solver.assume(p, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&ret), Some(&SlotKind::Owning));
            },
        );
    }

    #[test]
    fn address_of_depth_shift() {
        run_compiler(
            r#"
pub unsafe fn addr_fn(mut p: *mut i32) -> *mut *mut i32 {
    let q: *mut *mut i32 = &raw mut p;
    q
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let addr_fn = function_by_name(&program, "addr_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(addr_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, addr_fn, &body);

                let ret_depth_1 = local_slot(&slots, addr_fn, Local::from_u32(0), 1);
                let p = local_slot(&slots, addr_fn, Local::from_u32(1), 0);
                solver.assume(p, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&ret_depth_1), Some(&SlotKind::Owning));
            },
        );
    }

    #[test]
    fn all_raw_sat_with_coherence() {
        run_compiler(
            r#"
pub unsafe fn copy_fn(p: *mut i32) -> *mut i32 {
    p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let copy_fn = function_by_name(&program, "copy_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(copy_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, copy_fn, &body);

                solver.assume(
                    local_slot(&slots, copy_fn, Local::from_u32(0), 0),
                    SlotKind::Raw,
                );
                solver.assume(
                    local_slot(&slots, copy_fn, Local::from_u32(1), 0),
                    SlotKind::Raw,
                );

                assert_eq!(solver.check(), SatResult::Sat);
            },
        );
    }

    #[test]
    fn cast_does_not_propagate_kind() {
        run_compiler(
            r#"
pub unsafe fn cast_fn(p: *mut i32) -> *mut u8 {
    p as *mut u8
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let cast_fn = function_by_name(&program, "cast_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(cast_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, cast_fn, &body);

                let ret = local_slot(&slots, cast_fn, Local::from_u32(0), 0);
                let p = local_slot(&slots, cast_fn, Local::from_u32(1), 0);
                solver.assume(p, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(model.get(&ret), Some(&SlotKind::Ref));
            },
        );
    }

    #[test]
    fn aggregate_initializes_field_slot() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub p: *mut i32,
}

pub unsafe fn agg_fn(ptr: *mut i32) -> S {
    S { p: ptr }
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let agg_fn = function_by_name(&program, "agg_fn");
                let body = tcx.mir_drops_elaborated_and_const_checked(agg_fn).borrow();
                let solver = KindSolver::new(&slots);

                add_coherence(&solver, &slots, agg_fn, &body);
                // §9.10.2: aggregate field ownership is now linked by the crate-wide
                // `constrain_field_ownership` (`S::p.own <=> ptr.own`), not the per-store
                // equate; add it so assuming `ptr` Owning makes `S::p` Owning.
                constrain_field_ownership(&solver, &slots, &program);

                let ptr = local_slot(&slots, agg_fn, Local::from_u32(1), 0);
                solver.assume(ptr, SlotKind::Owning);

                assert_eq!(solver.check(), SatResult::Sat);
                let field_slot = slots
                    .field_slots
                    .slot_for_field_depth(
                        StructFieldSlot {
                            struct_did: s,
                            field_index: 0,
                        },
                        0,
                    )
                    .expect("slot for S::p");
                let model = solver.model_kinds().expect("satisfiable model");
                assert_eq!(
                    model.get(&SlotRef::Field(field_slot)),
                    Some(&SlotKind::Owning)
                );
            },
        );
    }

    // ===== BB-parity-own: ownership-slice semantic-verdict harness =====
    //
    // DEFERRED — relaxed-monotonicity IMPROVEMENT fixture (BO correctly `Owning` where
    // production is not): an empirical search over direct `free(p); return malloc` and the
    // interprocedural non-monotonic caller (`y = non_mono(x)`, non_mono frees its input and
    // returns a fresh malloc) found BO and production AGREE on every named local — BO does
    // not visibly exceed production on these simple shapes (production's monotonicity gating
    // is correctly scoped for them; some mixed alloc+out-param shapes go UNSAT and decline).
    // Per the project owner: do NOT fabricate an improvement case. A real divergence likely
    // needs a cyclic/recursive or deeper interprocedural shape and is deferred to a targeted
    // follow-up. When one is found, encode it as a gate-1 `owning` witness and confirm the
    // report shows PROD_MISSES for that witness.

    /// BB-parity-OWN: a SEMANTIC ownership-verdict harness for BO (borrow_ownership). The
    /// hard gates are pure SEMANTIC verdicts against the INTENDED ownership model (the §9.9
    /// output-param contract — a caller-visible ownership slot the callee REWRITES), NOT
    /// agreement with any implementation:
    ///   (1) each `owning` pointer BO MUST classify `Owning`;
    ///   (2) each `kept_non_owning` pointer BO must NOT over-claim `Owning` (over-claim =
    ///       `Box`/`free` on borrowed memory = double-free/UAF — the real soundness teeth).
    /// Production ownership (and, later, `output_params`) are REPORTED as DIAGNOSTICS ONLY,
    /// never gates: BO may legitimately claim MORE `Owning` than production (relaxed
    /// monotonicity is an intended improvement), so a witness production misses is REPORTED
    /// (PROD_MISSES / BO_EXTRA), not failed. Non-vacuity is intrinsic — gate 1 fails if BO
    /// does not genuinely compute `Owning`, and control slots are present in the model (so
    /// gate 2's `!= Owning` is a real verdict, not an absent-slot pass). Depth-0
    /// single-indirection only in this slice (BO syntactic depth vs production semantic depth
    /// can misalign at depth >= 1; deferred).
    /// A semantic ownership verdict target: a function `Local(name, depth)` or a struct
    /// `Field(struct_name, field_index, depth)`, at deref `depth` (0 = the slot's own
    /// value). Built via `loc` / `loc_at` / `fld`.
    #[derive(Clone, Copy, Debug)]
    enum Own<'a> {
        Local(&'a str, u8),
        Field(&'a str, usize, u8),
    }
    fn loc(name: &str) -> Own<'_> {
        Own::Local(name, 0)
    }
    fn loc_at(name: &str, depth: u8) -> Own<'_> {
        Own::Local(name, depth)
    }
    fn fld(struct_name: &str, field_index: usize) -> Own<'_> {
        Own::Field(struct_name, field_index, 0)
    }

    fn resolve_own(
        tcx: TyCtxt<'_>,
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        fn_did: LocalDefId,
        o: Own,
    ) -> SlotRef {
        match o {
            Own::Local(name, depth) => {
                local_slot(slots, fn_did, local_by_var_name(tcx, fn_did, name), depth)
            }
            Own::Field(struct_name, field_index, depth) => {
                let struct_did = struct_by_name(program, struct_name);
                let fsid = slots
                    .field_slots
                    .slot_for_field_depth(
                        StructFieldSlot {
                            struct_did,
                            field_index,
                        },
                        depth,
                    )
                    .unwrap_or_else(|| {
                        panic!("no field slot for `{struct_name}`.{field_index} depth {depth}")
                    });
                SlotRef::Field(fsid)
            }
        }
    }

    fn assert_ownership_parity(tcx: TyCtxt<'_>, fn_name: &str, owning: &[Own], non_owning: &[Own]) {
        // BO model (SUT) — identical construction to `assert_borrow_parity`.
        let program = collect_program(tcx);
        let f = function_by_name(&program, fn_name);
        let slots = CrateSlots::build(&program);
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let (_s, selectors) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        )
        .expect("BB-parity-own: ownership emission");
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        let model = verify_to_fixpoint(&program, &slots, &solver, &selectors, true)
            .expect("BB-parity-own: BO CEGAR must converge (Some) on the corpus");

        // Production ownership oracle — DIAGNOSTIC baseline only (NOT a gate/ceiling).
        let prod_owning = build_prod_owning(tcx, &program, &slots);

        // HARD gate 1 — positive Owning verdicts (Local OR Field, any depth): BO MUST classify
        // each `Owning`. Pure SEMANTIC verdict; production is NOT a gate. A verdict BO owns
        // that production MISSES is a relaxed-monotonicity IMPROVEMENT (reported), not a fail.
        let mut prod_agrees: Vec<Own> = Vec::new();
        let mut prod_misses: Vec<Own> = Vec::new();
        for &o in owning {
            let sref = resolve_own(tcx, &program, &slots, f, o);
            assert_eq!(
                model.get(&sref),
                Some(&SlotKind::Owning),
                "BB-parity-own: fixture `{fn_name}` requires BO to classify {o:?} Owning \
                 (semantic verdict); got {:?}",
                model.get(&sref)
            );
            // Production comparison applies to LOCAL verdicts only: `build_prod_owning` maps
            // production LOCAL ownership, not field ownership (deferred), so a `Field` verdict
            // is not a meaningful PROD_AGREES/MISSES signal.
            if matches!(o, Own::Local(..)) {
                if prod_owning.contains(&sref) {
                    prod_agrees.push(o);
                } else {
                    prod_misses.push(o);
                }
            }
        }

        // HARD gate 2 — semantic non-Owning verdicts: BO must NOT over-claim. Production is
        // not ground truth, so soundness lives HERE: over-claiming a read-only param, a
        // field-transfer parent, or a BORROWED field is a double-free/UAF.
        for &o in non_owning {
            let sref = resolve_own(tcx, &program, &slots, f, o);
            assert_ne!(
                model.get(&sref),
                Some(&SlotKind::Owning),
                "BB-parity-own: control {o:?} must NOT be Owning in BO's model \
                 (over-claim = double-free/UAF); got {:?}",
                model.get(&sref)
            );
        }

        // SOFT report (NEVER fails), over LOCAL slots (production field-granularity mapping is
        // deferred — field verdicts are hard-gated above, not compared to production here).
        // BO_EXTRA (BO-only Owning) is TRIAGED: expected relaxed-monotonicity improvement vs a
        // suspicious over-claim that should earn its own semantic control.
        let (mut covered, mut bo_extra, mut bo_owning_total) = (0usize, 0usize, 0usize);
        for (s, kind) in &model {
            if !matches!(s, SlotRef::Local(..)) || *kind != SlotKind::Owning {
                continue;
            }
            bo_owning_total += 1;
            if prod_owning.contains(s) {
                covered += 1;
            } else {
                bo_extra += 1;
            }
        }
        let bo_under = prod_owning
            .iter()
            .filter(|s| model.get(*s) != Some(&SlotKind::Owning))
            .count();
        eprintln!(
            "[BB-parity-own] {fn_name}: bo_owning(local)={bo_owning_total} prod_owning={} \
             COVERED={covered} BO_UNDER(safe)={bo_under} BO_EXTRA(triage)={bo_extra} \
             | witnesses PROD_AGREES={prod_agrees:?} PROD_MISSES(BO-improvement)={prod_misses:?}",
            prod_owning.len()
        );
    }

    /// Build the baseline ownership oracle's `Owning` set as depth-indexed BO slots, by
    /// running the ownership analysis via `analyze_program` -> `solidify` and mapping every
    /// `is_owning()` (local, depth) to a `SlotRef::Local`. BASELINE only — see
    /// `assert_ownership_parity`.
    ///
    /// PRECISION NOTE (Codex): `analyze_program` runs the ownership analysis with an EMPTY
    /// param-alias map — the same simplified reference the `ownership_analysis` tests use —
    /// NOT the Andersen points-to aliases (`find_param_aliases`) the real rewriter pipeline
    /// (`rewriter::replace_local_borrows`) feeds to `compute_output_params`. The two agree
    /// except where param aliasing changes output-param classification. The current
    /// focused-core fixtures are all non-aliasing (empty ≡ Andersen), so this is exact for
    /// them; an ALIAS-AWARE oracle (thread `find_param_aliases`) + an alias-sensitive
    /// fixture is DEFERRED with the other follow-ups (interproc / depth>=1 / field / coverage
    /// counters). Until then, do NOT add an alias-sensitive fixture expecting a faithful
    /// production comparison.
    fn build_prod_owning(
        tcx: TyCtxt<'_>,
        program: &RustProgram<'_>,
        slots: &CrateSlots,
    ) -> rustc_hash::FxHashSet<SlotRef> {
        let results = super::ownership_analysis::analyze_program(program);
        let solidified = results.solidify(program);
        let mut prod_owning = rustc_hash::FxHashSet::default();
        for &g in &program.functions {
            let Some(universe) = slots.fn_local_slots.get(&g) else {
                continue;
            };
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            let did = g.to_def_id();
            let fnr = solidified.fn_results(&did);
            for local in body.local_decls.indices() {
                for (depth, own) in fnr.local_result(local).iter().enumerate() {
                    if own.is_owning()
                        && let Some(sid) = universe.slot_for_local_depth(local, depth as u8)
                    {
                        prod_owning.insert(SlotRef::Local(g, sid));
                    }
                }
            }
        }
        prod_owning
    }

    /// BB-parity-own positive witness: a locally allocated-and-freed pointer is genuinely
    /// `Owning` in BOTH BO and the production oracle (no relaxed-monotonicity subtlety), so
    /// it seeds hard gate 1 (BO Owning) and hard gate 3 (production non-vacuity).
    #[test]
    fn boparity_alloc_free_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn f() {
    let p = malloc(4);
    free(p);
}
"#,
            |tcx| assert_ownership_parity(tcx, "f", &[loc("p")], &[]),
        );
    }

    /// BB-parity-own semantic non-Owning control: a read-only borrowed pointer param must
    /// NOT be `Owning` (over-claim = UAF on caller memory). Seeds hard gate 2.
    #[test]
    fn boparity_read_only_param_control() {
        run_compiler(
            r#"
pub unsafe fn reader(p: *mut i32) -> i32 {
    unsafe { *p }
}
"#,
            |tcx| assert_ownership_parity(tcx, "reader", &[], &[loc("p")]),
        );
    }

    /// BB-parity-own semantic non-Owning control (the §9.8 field-transfer): a borrowed
    /// struct pointer whose FIELD is malloc'd must NOT make the parent `owner` Owning —
    /// field-ownership transfer is not parent ownership (the output-param contract). This
    /// control has real teeth: at precision 2 WITHOUT the `field ⟹ parent` suppression BO
    /// over-claims `owner` (the reverted §9.8 regression), so a regression there fails here.
    #[test]
    fn boparity_field_transfer_parent_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub struct Holder {
    pub data: *mut core::ffi::c_void,
}

pub unsafe fn stash(owner: *mut Holder) {
    (*owner).data = unsafe { malloc(4) };
}
"#,
            |tcx| assert_ownership_parity(tcx, "stash", &[fld("Holder", 0)], &[loc("owner")]),
        );
    }

    /// BB-parity-own semantic non-Owning control: a pointer merely PASSED THROUGH to another
    /// function (no allocation, no free) must NOT be Owning — nothing owns it. Guards against
    /// BO's every-arg-is-Param::Output modeling over-claiming a pass-through.
    #[test]
    fn boparity_pass_through_param_control() {
        run_compiler(
            r#"
pub unsafe fn sink(q: *mut i32) -> i32 {
    unsafe { *q }
}

pub unsafe fn pass_through(p: *mut i32) -> i32 {
    unsafe { sink(p) }
}
"#,
            |tcx| assert_ownership_parity(tcx, "pass_through", &[], &[loc("p")]),
        );
    }

    /// BB-parity-own positive witness (the BB-escape win as a SEMANTIC verdict): a caller-side
    /// out-param `make(&raw mut local){ *out = malloc }` rewrites the caller-visible slot, so
    /// the caller's `local` MUST be Owning — the §9.9 output-param contract. RETURN-`local`
    /// shape so `local` is USED (an unused owning local leaks -> non-Owning, the fixture trap).
    #[test]
    fn boparity_caller_outparam_escape_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn make(out: *mut *mut core::ffi::c_void) {
    *out = unsafe { malloc(4) };
}

pub unsafe fn caller() -> *mut core::ffi::c_void {
    let mut local: *mut core::ffi::c_void = core::ptr::null_mut();
    unsafe { make(&raw mut local) };
    local
}
"#,
            |tcx| assert_ownership_parity(tcx, "caller", &[loc("local")], &[]),
        );
    }

    /// BB-parity-own positive witness (the deferred by-value depth-1 case, now working): a
    /// by-value double-pointer out-param `make_byval(pp){ *pp = malloc }` makes pp's depth-1
    /// pointee Owning while the outer pointer stays non-Owning — the depth>=1 ownership that
    /// coherence carries even though `link_versions_to_slots` is depth-0-only.
    #[test]
    fn boparity_byval_double_ptr_pointee_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub unsafe fn make_byval(pp: *mut *mut core::ffi::c_void) {
    *pp = unsafe { malloc(4) };
}
"#,
            |tcx| assert_ownership_parity(tcx, "make_byval", &[loc_at("pp", 1)], &[loc("pp")]),
        );
    }

    /// BB-parity-own positive witness (struct-field out-param transfer): a callee that mallocs
    /// into a struct field makes the FIELD slot Owning (routed to the StructFieldSlot), while
    /// the parent pointer stays non-Owning — the §9.10.2 goal, both sides.
    #[test]
    fn boparity_struct_field_outparam_owning() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct Node {
    pub next: *mut core::ffi::c_void,
}
pub unsafe fn set_next(n: *mut Node) {
    (*n).next = unsafe { malloc(4) };
}
"#,
            |tcx| assert_ownership_parity(tcx, "set_next", &[fld("Node", 0)], &[loc("n")]),
        );
    }

    /// BB-parity-own semantic non-Owning control (borrowed field): a struct field that only
    /// ever receives a BORROWED pointer (a param, never malloc) must NOT be Owning — freeing
    /// it would be a UAF on caller memory.
    #[test]
    fn boparity_borrowed_field_control() {
        run_compiler(
            r#"
pub struct Bag {
    pub p: *mut i32,
}
pub unsafe fn stash_borrow(b: *mut Bag, src: *mut i32) {
    (*b).p = src;
}
"#,
            |tcx| {
                assert_ownership_parity(
                    tcx,
                    "stash_borrow",
                    &[],
                    &[fld("Bag", 0), loc("b"), loc("src")],
                )
            },
        );
    }

    /// BB-parity-own regression control (flow-insensitive global-field over-claim — FIXED §9.10.2).
    ///
    /// A struct field slot is a SINGLE crate-wide slot; `coherence` is flow-insensitive, so it
    /// equates that one slot to EVERY value assigned to the field. Here `cell_own` mallocs into
    /// `Cell::p` (an Owning source) and `cell_borrow` assigns a borrowed `src` into the SAME
    /// field. BEFORE the fix the malloc source forced the shared slot Owning, so `cell_borrow`
    /// over-claimed `Cell::p` and the rewriter would `Box`/free the borrowed `src` -> UAF.
    /// FIXED by the conservative field-ownership veto (`coherence::compute_borrowed_origin` +
    /// `KindSolver::veto_owning`): storing a borrowed-origin (a parameter, or a copy/cast/reborrow
    /// chain from one) value into a struct field HARD-vetoes that field slot's `own`, so it backs
    /// off to non-Owning (the retractable malloc source leaks — a safe leak, not a UAF). Guards
    /// that `Cell::p` stays non-Owning. Conservative: a field that only ever receives OWNED param
    /// transfers is also vetoed (a safe precision loss, not an over-claim).
    ///
    /// The adversarial sweep (2026-07-02, 10-family workflow probe) confirmed this was the SOLE
    /// real over-claim root cause and characterized its scope — a raw-pointer struct field
    /// (scalar `*mut T` or a multi-level `*mut *mut T` at its depth-0 slot) owned by a source
    /// (malloc/strdup/calloc) or sink (free) in one fn AND assigned a borrowed value in another;
    /// the param-origin veto covers all of them. NON-gaps (unchanged): deeper (depth>=1) chain
    /// levels UNDER-claim (safe leak); Rust array `[*mut T; N]` fields are unmodeled (no slot);
    /// unions unmodeled; realloc's arg-sink is CORRECT (realloc consumes its arg, like free).
    #[test]
    fn boparity_mixed_owned_borrowed_field_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct Cell {
    pub p: *mut core::ffi::c_void,
}
pub unsafe fn cell_own(c: *mut Cell) {
    (*c).p = unsafe { malloc(4) };
}
pub unsafe fn cell_borrow(c: *mut Cell, src: *mut core::ffi::c_void) {
    (*c).p = src;
}
"#,
            |tcx| assert_ownership_parity(tcx, "cell_borrow", &[], &[fld("Cell", 0)]),
        );
    }

    /// BB-parity-own regression control (mixed field via a PROJECTED borrowed load — Codex).
    /// The borrowed value reaches the field through `t = (*src).p` (a load through a borrowed
    /// param), not a direct param copy. `compute_borrowed_origin` propagates through the
    /// borrowed root so `t` counts as borrowed-origin; combined with `c_own`'s malloc into the
    /// same field, `C::p` is a mixed field and is vetoed to non-Owning. Without the
    /// projected-load propagation the over-claim survived (Owning).
    #[test]
    fn boparity_mixed_field_projected_borrow_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct C {
    pub p: *mut core::ffi::c_void,
}
pub unsafe fn c_own(c: *mut C) {
    (*c).p = unsafe { malloc(4) };
}
pub unsafe fn c_borrow_proj(dst: *mut C, src: *mut C) {
    let t = (*src).p;
    (*dst).p = t;
}
"#,
            |tcx| assert_ownership_parity(tcx, "c_borrow_proj", &[], &[fld("C", 0)]),
        );
    }

    /// BB-parity-own regression control (mixed field via an INTERPROC-return allocation —
    /// Codex). The owned side reaches the field via a local wrapper call `let p = d_make();
    /// (*d).p = p` (d_make returns malloc), which allocator-SOURCE detection does NOT flag.
    /// The veto uses "non-borrowed" evidence rather than allocation evidence, so the interproc
    /// alloc still counts: `D::p` is assigned a non-borrowed (`p`) value AND a borrowed (`src`)
    /// value, so it is vetoed to non-Owning. Without this the over-claim survived (Owning).
    #[test]
    fn boparity_mixed_field_interproc_alloc_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct D {
    pub p: *mut core::ffi::c_void,
}
pub unsafe fn d_make() -> *mut core::ffi::c_void {
    unsafe { malloc(4) }
}
pub unsafe fn d_own(d: *mut D) {
    let p = d_make();
    (*d).p = p;
}
pub unsafe fn d_borrow(d: *mut D, src: *mut core::ffi::c_void) {
    (*d).p = src;
}
"#,
            |tcx| assert_ownership_parity(tcx, "d_borrow", &[], &[fld("D", 0)]),
        );
    }

    /// BB-parity-own regression control (address-of / non-owned field store — Codex). A field
    /// with a malloc store (`E::p = malloc as *mut i32`, a Cast the collector follows to the
    /// owned operand) AND a direct address-of store (`(*e).p = &raw mut x`, a `RawPtr` rvalue)
    /// must NOT be Owning: it can hold a stack address, so freeing it is a UAF. The address
    /// store is not resolvable to an owned value, so `constrain_field_ownership` BLOCKS the
    /// field (`forbid_field_own`) rather than dropping it from the `AND` (which would wrongly
    /// permit Owning).
    #[test]
    fn boparity_addr_of_field_store_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
pub struct E {
    pub p: *mut i32,
}
pub unsafe fn e_own(e: *mut E) {
    (*e).p = unsafe { malloc(4) } as *mut i32;
}
pub unsafe fn e_addr(e: *mut E) {
    let mut x: i32 = 0;
    (*e).p = &raw mut x;
}
"#,
            |tcx| assert_ownership_parity(tcx, "e_addr", &[], &[fld("E", 0)]),
        );
    }

    /// BB-parity-own regression control (free-through-a-field projection — Codex). A field
    /// assigned a borrowed `src` and freed elsewhere via `free((*b).p)` must NOT drag `src`
    /// (or the field) to Owning: BO's free SINK, like its allocator sources, skips a PROJECTED
    /// argument, so `free((*b).p)` does not force the field Owning, and the borrowed store
    /// keeps it non-Owning. Guards that the field-ownership biconditional cannot be
    /// back-propagated by a field sink.
    #[test]
    fn boparity_free_through_field_control() {
        run_compiler(
            r#"
unsafe extern "C" {
    fn free(ptr: *mut core::ffi::c_void);
}
pub struct F {
    pub p: *mut core::ffi::c_void,
}
pub unsafe fn f_stash(b: *mut F, src: *mut core::ffi::c_void) {
    (*b).p = src;
}
pub unsafe fn f_drop(b: *mut F) {
    free((*b).p);
}
"#,
            |tcx| assert_ownership_parity(tcx, "f_stash", &[], &[fld("F", 0), loc("src")]),
        );
    }
}

mod borrow_ownership_resolve {
    use rustc_abi::FieldIdx;
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::{
        mir::{Local, Place, ProjectionElem},
        ty::{Ty, TyCtxt, TyKind},
    };
    use rustc_span::def_id::LocalDefId;

    use crate::{
        analyses::borrow_ownership::{
            crate_slots::{CrateSlots, ptr_chain_depth},
            ptr::decompose_ty,
            resolve::{ResolvedSlot, resolve_place},
            slots::StructFieldSlot,
        },
        utils::rustc::RustProgram,
    };

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

    fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }

        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn struct_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .structs
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("struct `{name}` not found"))
    }

    fn function_by_name(program: &RustProgram<'_>, name: &str) -> LocalDefId {
        program
            .functions
            .iter()
            .copied()
            .find(|did| {
                program
                    .tcx
                    .def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    == Some(name)
            })
            .unwrap_or_else(|| panic!("function `{name}` not found"))
    }

    fn struct_field_ty<'tcx>(
        tcx: TyCtxt<'tcx>,
        struct_did: LocalDefId,
        field_index: usize,
    ) -> Ty<'tcx> {
        let ty = tcx.type_of(struct_did).skip_binder();
        let TyKind::Adt(adt, substs) = ty.kind() else {
            panic!("expected struct ADT type");
        };

        adt.all_fields()
            .nth(field_index)
            .unwrap_or_else(|| panic!("field index {field_index} not found"))
            .ty(tcx, substs)
    }

    #[test]
    fn resolve_local_chain_depths() {
        run_compiler(
            r#"
pub unsafe fn g(pp: *mut *mut i32) -> i32 {
    **pp
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let g = function_by_name(&program, "g");
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                let body = &*body;
                let pp = Local::from_u32(1);
                let base = Place::from(pp);
                let fn_locals = slots.fn_local_slots.get(&g).expect("slots for g");

                assert_eq!(
                    resolve_place(&slots, g, body, base, 0, None),
                    fn_locals
                        .slot_for_local_depth(pp, 0)
                        .map(ResolvedSlot::Local)
                );
                assert_eq!(
                    resolve_place(&slots, g, body, base, 1, None),
                    fn_locals
                        .slot_for_local_depth(pp, 1)
                        .map(ResolvedSlot::Local)
                );
                assert_eq!(resolve_place(&slots, g, body, base, 2, None), None);
            },
        );
    }

    /// §NB1: the `layers` out-param records every pointer slot *dereferenced*
    /// to reach the target (shallowest first), which the SAFE-MONO walk pairs
    /// with the target. The target itself is not a layer; a bare local
    /// traverses none.
    #[test]
    fn resolve_place_collects_traversed_layers() {
        run_compiler(
            r#"
pub unsafe fn g(ppp: *mut *mut *mut i32) -> i32 {
    ***ppp
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let g = function_by_name(&program, "g");
                let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
                let body = &*body;
                let ppp = Local::from_u32(1);
                let fn_locals = slots.fn_local_slots.get(&g).expect("slots for g");
                let d = |depth| {
                    fn_locals
                        .slot_for_local_depth(ppp, depth)
                        .map(ResolvedSlot::Local)
                        .unwrap()
                };

                // `**ppp` (two real Deref projections) targets depth 2, and
                // traverses layers depth 0 then depth 1.
                let two_derefs = Place::from(ppp)
                    .project_deeper(&[ProjectionElem::Deref, ProjectionElem::Deref], tcx);
                let mut layers = Vec::new();
                let target = resolve_place(&slots, g, body, two_derefs, 0, Some(&mut layers));
                assert_eq!(target, Some(d(2)));
                assert_eq!(layers, vec![d(0), d(1)]);

                // A bare local (no deref) traverses no layers.
                let mut none = Vec::new();
                let bare = resolve_place(&slots, g, body, Place::from(ppp), 0, Some(&mut none));
                assert_eq!(bare, Some(d(0)));
                assert!(none.is_empty(), "a bare local dereferences nothing");
            },
        );
    }

    #[test]
    fn resolve_struct_field() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub a: *mut i32,
    pub b: *mut i32,
}

pub unsafe fn f(s: *mut S) {
    let _x = (*s).a;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let f = function_by_name(&program, "f");
                let s = struct_by_name(&program, "S");
                let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
                let body = &*body;
                let s_local = Local::from_u32(1);
                let field_a_ty = struct_field_ty(tcx, s, 0);
                let field_a = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };
                let place = Place::from(s_local).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(0), field_a_ty),
                    ],
                    tcx,
                );

                assert_eq!(
                    resolve_place(&slots, f, body, place, 0, None),
                    slots
                        .field_slots
                        .slot_for_field_depth(field_a, 0)
                        .map(ResolvedSlot::Field)
                );
                assert_eq!(
                    resolve_place(&slots, f, body, Place::from(s_local), 0, None),
                    slots
                        .fn_local_slots
                        .get(&f)
                        .expect("slots for f")
                        .slot_for_local_depth(s_local, 0)
                        .map(ResolvedSlot::Local)
                );
            },
        );
    }

    #[test]
    fn resolve_capped_deref_then_field_is_conservative() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub a: *mut i32,
}

pub unsafe fn ok_field(q: *mut *mut *mut S) -> *mut i32 {
    (***q).a
}

pub unsafe fn deep_field(p: *mut *mut *mut *mut S) -> *mut i32 {
    (****p).a
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let s = struct_by_name(&program, "S");
                let ok_field = function_by_name(&program, "ok_field");
                let deep_field = function_by_name(&program, "deep_field");
                let field_a_ty = struct_field_ty(tcx, s, 0);
                let field_a = StructFieldSlot {
                    struct_did: s,
                    field_index: 0,
                };
                let expected_field = slots
                    .field_slots
                    .slot_for_field_depth(field_a, 0)
                    .map(ResolvedSlot::Field);

                let ok_body = tcx
                    .mir_drops_elaborated_and_const_checked(ok_field)
                    .borrow();
                let ok_body = &*ok_body;
                let q = Local::from_u32(1);
                let ok_place = Place::from(q).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(0), field_a_ty),
                    ],
                    tcx,
                );
                assert_eq!(
                    resolve_place(&slots, ok_field, ok_body, ok_place, 0, None),
                    expected_field
                );

                let deep_body = tcx
                    .mir_drops_elaborated_and_const_checked(deep_field)
                    .borrow();
                let deep_body = &*deep_body;
                let p = Local::from_u32(1);
                let deep_place = Place::from(p).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(0), field_a_ty),
                    ],
                    tcx,
                );
                assert_eq!(
                    resolve_place(&slots, deep_field, deep_body, deep_place, 0, None),
                    None
                );
            },
        );
    }

    #[test]
    fn resolve_depth_cap_conservative() {
        run_compiler(
            r#"
pub unsafe fn deep(p: *mut *mut *mut *mut i32) -> i32 {
    ****p
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let deep = function_by_name(&program, "deep");
                let body = tcx.mir_drops_elaborated_and_const_checked(deep).borrow();
                let body = &*body;
                let p = Local::from_u32(1);
                let base = Place::from(p);
                let fn_locals = slots.fn_local_slots.get(&deep).expect("slots for deep");

                for depth in 0..3 {
                    assert_eq!(
                        resolve_place(&slots, deep, body, base, depth, None),
                        fn_locals
                            .slot_for_local_depth(p, depth)
                            .map(ResolvedSlot::Local)
                    );
                }
                assert_eq!(resolve_place(&slots, deep, body, base, 3, None), None);
            },
        );
    }

    #[test]
    fn resolve_array_conservative() {
        run_compiler(
            r#"
#[repr(C)]
pub struct S {
    pub arr: [*mut i32; 4],
    pub scalar: *mut i32,
}

pub unsafe fn h(s: *mut S, a: [*mut i32; 4]) {
    let _x = (*s).arr;
    let _y = a;
    let _z = (*s).scalar;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let slots = CrateSlots::build(&program);
                let h = function_by_name(&program, "h");
                let s = struct_by_name(&program, "S");
                let body = tcx.mir_drops_elaborated_and_const_checked(h).borrow();
                let body = &*body;
                let s_local = Local::from_u32(1);
                let array_param = Local::from_u32(2);
                let arr_ty = struct_field_ty(tcx, s, 0);
                let scalar_ty = struct_field_ty(tcx, s, 1);
                let arr_place = Place::from(s_local).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(0), arr_ty),
                    ],
                    tcx,
                );
                let scalar_place = Place::from(s_local).project_deeper(
                    &[
                        ProjectionElem::Deref,
                        ProjectionElem::Field(FieldIdx::from_u32(1), scalar_ty),
                    ],
                    tcx,
                );
                let scalar_field = StructFieldSlot {
                    struct_did: s,
                    field_index: 1,
                };

                assert_eq!(resolve_place(&slots, h, body, arr_place, 0, None), None);
                assert_eq!(
                    resolve_place(&slots, h, body, Place::from(array_param), 0, None),
                    None
                );
                assert_eq!(
                    resolve_place(&slots, h, body, scalar_place, 0, None),
                    slots
                        .field_slots
                        .slot_for_field_depth(scalar_field, 0)
                        .map(ResolvedSlot::Field)
                );
            },
        );
    }

    #[test]
    fn reconciliation_depth_models() {
        run_compiler(
            r#"
pub unsafe fn recon(
    chain2: *mut *mut i32,
    arr: [*mut i32; 4],
    deep: *mut *mut *mut *mut i32,
) {
    let _ = chain2;
    let _ = arr;
    let _ = deep;
}
"#,
            |tcx| {
                let program = collect_program(tcx);
                let recon = function_by_name(&program, "recon");
                let body = tcx.mir_drops_elaborated_and_const_checked(recon).borrow();
                let body = &*body;
                let chain2_ty = body.local_decls[Local::from_u32(1)].ty;
                let arr_ty = body.local_decls[Local::from_u32(2)].ty;
                let deep_ty = body.local_decls[Local::from_u32(3)].ty;

                assert_eq!(ptr_chain_depth(chain2_ty), 2);
                assert_eq!(decompose_ty(chain2_ty).0, 2);

                assert_eq!(ptr_chain_depth(arr_ty), 0);
                assert_eq!(decompose_ty(arr_ty).0, 1);

                assert_eq!(ptr_chain_depth(deep_ty), 3);
                assert_eq!(decompose_ty(deep_ty).0, 4);
            },
        );
    }
}

#[test]
fn test_array_local_rewriter_field_base_group_rewrites_loop_pointers() {
    let code = r#"
#[repr(C)]
pub struct Image {
    pub pix: *mut u8,
    pub w: i32,
    pub h: i32,
}
pub unsafe fn flip(mut img: *mut Image) {
    let mut pix: *mut u8 = (*img).pix;
    let mut w: i32 = (*img).w;
    let mut h: i32 = (*img).h;
    let mut flips: i32 = h / 2;
    let mut i: i32 = 0;
    while i < flips {
        let mut a: *mut u8 = pix.offset((w * i) as isize);
        let mut b: *mut u8 = pix.offset((w * (h - i - 1)) as isize);
        let mut j: i32 = 0;
        while j < w {
            let t: u8 = *a;
            *a = *b;
            *b = t;
            a = a.offset(1);
            b = b.offset(1);
            j += 1;
        }
        i += 1;
    }
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    eprintln!("changed={changed}\n{s}");
    assert!(changed, "expected rewrite to change the code:\n{s}");
    assert!(s.contains("a_idx"), "expected a_idx in:\n{s}");
    assert!(s.contains("b_idx"), "expected b_idx in:\n{s}");
    // pix is never reassigned so it stays as a raw pointer — not rewritten to an index
    assert!(
        s.contains("let mut pix: *mut u8") || s.contains("let pix: *mut u8"),
        "expected pix to remain as a raw pointer in:\n{s}"
    );
    // a and b are only used through indices into pix — no materialized pointer locals
    assert!(
        !s.contains("let mut a: *mut u8") && !s.contains("let a: *mut u8"),
        "expected a NOT to be materialized in:\n{s}"
    );
    assert!(
        !s.contains("let mut b: *mut u8") && !s.contains("let b: *mut u8"),
        "expected b NOT to be materialized in:\n{s}"
    );
    assert!(
        s.contains("pix).offset(a_idx)"),
        "expected pix offset by a_idx in:\n{s}"
    );
    assert!(
        s.contains("pix).offset(b_idx)"),
        "expected pix offset by b_idx in:\n{s}"
    );
}

#[test]
fn test_array_local_rewriter_materializes_mutable_moving_cursors() {
    let code = r#"
#[repr(C)]
pub struct Image {
    pub pix: *mut u8,
    pub w: i32,
    pub h: i32,
}

pub unsafe fn flip(mut img: *mut Image) {
    let mut pix: *mut u8 = (*img).pix;
    let mut w: i32 = (*img).w;
    let mut h: i32 = (*img).h;
    let mut flips: i32 = h / 2;
    let mut i: i32 = 0;
    while i < flips {
        let mut a: *mut u8 = pix.offset((w * i) as isize);
        let mut b: *mut u8 = pix.offset((w * (h - i - 1)) as isize);
        let mut j: i32 = 0;
        while j < w {
            let t: u8 = *a;
            *a = *b;
            *b = t;
            a = a.offset(1);
            b = b.offset(1);
            j += 1;
        }
        i += 1;
    }
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "expected rewrite to change the code:\n{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("a_idx"), "{s}");
    assert!(s.contains("b_idx"), "{s}");
    // pix is never reassigned — stays as a raw pointer, not rewritten to an index
    assert!(
        s.contains("let mut pix: *mut u8") || s.contains("let pix: *mut u8"),
        "expected pix to remain as raw pointer:\n{s}"
    );
    // a and b become index-only — no separate pointer locals
    assert!(
        !s.contains("let mut a: *mut u8") && !s.contains("let a: *mut u8"),
        "expected a not to be materialized:\n{s}"
    );
    assert!(
        !s.contains("let mut b: *mut u8") && !s.contains("let b: *mut u8"),
        "expected b not to be materialized:\n{s}"
    );
    assert!(
        s.contains("pix).offset(a_idx)"),
        "expected reads/writes through pix offset by a_idx:\n{s}"
    );
    assert!(
        s.contains("pix).offset(b_idx)"),
        "expected reads/writes through pix offset by b_idx:\n{s}"
    );
    assert!(
        s.contains("a_idx = (a_idx) +") || s.contains("a_idx = a_idx +") || s.contains("a_idx +="),
        "expected a_idx to be advanced relative to itself:\n{s}"
    );
    assert!(
        s.contains("b_idx = (b_idx) +") || s.contains("b_idx = b_idx +") || s.contains("b_idx +="),
        "expected b_idx to be advanced relative to itself:\n{s}"
    );
}

#[test]
fn test_array_local_rewriter_skips_materialization_when_pointer_escapes() {
    let code = r#"
#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

unsafe extern "C" {
    fn store_pointer(p: *mut i32);
}

pub unsafe fn expose(mut h: *mut Holder, mut i: isize) {
    let mut p: *mut i32 = (*h).data.offset(i);
    store_pointer(p);
    *p = 3;
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    if changed {
        assert!(
            !s.contains("let p: &") && !s.contains("let mut p: &mut"),
            "escaping pointer must not be materialized as a reference:\n{s}"
        );
    }
}

#[test]
fn test_array_local_rewriter_rewrites_reassigned_pointee_field_base_live() {
    // (*s).out is caller-visible: the field write is KEPT live, a shadow
    // counter tracks the advance, and members materialize off the live field
    // with the counter subtracted (approach D).
    let code = r#"
#[repr(C)]
pub struct State {
    pub out: *mut i8,
    pub out_end: *mut i8,
}

pub unsafe fn copy_from_back(mut s: *mut State, mut length: isize, mut distance: isize) -> i32 {
    let mut src: *mut i8 = (*s).out.offset(-distance);
    let mut dst: *mut i8 = (*s).out;
    (*s).out = (*s).out.offset(length);
    *dst = *src;
    dst = dst.offset(1);
    src = src.offset(1);
    *dst as i32 + *src as i32
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // field write kept live
    assert!(s.contains("(*s).out = (*s).out.offset(length)"), "{s}");
    // shadow counter declared and advanced
    assert!(s.contains("let mut out_idx: isize = 0isize"), "{s}");
    assert!(s.contains("out_idx = (out_idx) + (length)"), "{s}");
    // members are indexes, materialized with - out_idx
    assert!(s.contains("src_idx"), "{s}");
    assert!(s.contains("dst_idx"), "{s}");
    assert!(s.contains("- (out_idx)"), "{s}");
}

#[test]
fn test_array_local_rewriter_rewrites_memory_copy_cursors_of_reassigned_pointee_field_base() {
    // (*s).out is caller-visible: the field write is KEPT live (approach D),
    // a shadow counter tracks the advance, and members are index-rewritten.
    let code = r#"
#[repr(C)]
pub struct State {
    pub out: *mut i8,
}

unsafe extern "C" {
    fn memset(ptr: *mut core::ffi::c_void, value: i32, n: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn copy_from_back(mut s: *mut State, mut length: i32, mut distance: i32) {
    let mut src: *mut i8 = (*s).out.offset(-(distance as isize));
    let mut dst: *mut i8 = (*s).out;
    (*s).out = (*s).out.offset(length as isize);
    if distance == 1 {
        memset(dst as *mut core::ffi::c_void, (*src) as i32, length as usize);
    } else {
        while length != 0 {
            length -= 1;
            let fresh = *src;
            src = src.offset(1);
            *dst = fresh;
            dst = dst.offset(1);
        }
    }
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // field write kept live
    assert!(s.contains("(*s).out ="), "{s}");
    // member index vars present
    assert!(s.contains("src_idx") || s.contains("dst_idx"), "{s}");
    // shadow counter for out declared
    assert!(s.contains("out_idx"), "{s}");
}

#[test]
fn test_array_local_rewriter_rewrites_two_reassigned_pointee_field_bases() {
    // both (*p).a and (*p).b are caller-visible field bases; both are rewritten
    // with the live-field / shadow-counter scheme (approach D).
    let code = r#"
#[repr(C)]
pub struct Pair {
    pub a: *mut i8,
    pub b: *mut i16,
}

pub unsafe fn dual(mut p: *mut Pair, mut da: isize, mut db: isize) -> i32 {
    let mut ax: *mut i8 = (*p).a.offset(1);
    let mut bx: *mut i16 = (*p).b.offset(1);
    (*p).a = (*p).a.offset(da);
    (*p).b = (*p).b.offset(db);
    ax = ax.offset(1);
    bx = bx.offset(1);
    *ax as i32 + *bx as i32
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // field writes kept live
    assert!(s.contains("(*p).a ="), "{s}");
    assert!(s.contains("(*p).b ="), "{s}");
    // member index vars present
    assert!(s.contains("ax_idx") || s.contains("a_idx"), "{s}");
    assert!(s.contains("bx_idx") || s.contains("b_idx"), "{s}");
}

#[test]
fn test_array_local_rewriter_skips_live_field_base_with_non_self_advance() {
    // the base field is reassigned from a member, not a self-advance,
    // cannot track the counter; the group is dropped and left unrewritten.
    let code = r#"
#[repr(C)]
pub struct State {
    pub out: *mut i8,
}

pub unsafe fn f(mut s: *mut State, mut n: isize) -> i32 {
    let mut cur: *mut i8 = (*s).out.offset(n);
    (*s).out = cur;
    cur = cur.offset(1);
    *cur as i32
}
"#;
    let (s, _changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("(*s).out = cur"), "{s}");
    assert!(!s.contains("out_idx"), "{s}");
}

#[test]
fn test_array_local_rewriter_rewrites_field_base_cursor_local_used_in_offset_from() {
    let code = r#"
#[repr(C)]
pub struct ProcessState {
    pub buffer: *mut i8,
}

unsafe extern "C" {
    fn memchr(ptr: *const core::ffi::c_void, ch: i32, n: usize) -> *mut core::ffi::c_void;
}

pub unsafe fn process_buffer(mut state: *mut ProcessState, mut target: i8, mut remaining: usize) -> i32 {
    let mut count: i32 = 0;
    let mut ptr: *mut i8 = (*state).buffer;
    while remaining > 0 {
        let mut found: *mut i8 = memchr(ptr as *const core::ffi::c_void, target as i32, remaining) as *mut i8;
        if found.is_null() {
            break;
        }
        count += 1;
        remaining = remaining.wrapping_sub((found.offset_from(ptr) + 1) as usize);
        ptr = found.offset(1);
    }
    count
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(
        changed,
        "expected field-base cursor local to be rewritten:\n{s}"
    );
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // cursor is now an Option<isize> because memchr may return null
    assert!(s.contains("ptr_idx: Option<isize>"), "{s}");
    assert!(!s.contains("let mut ptr: *mut i8"), "{s}");
    assert!(!s.contains("let ptr: *mut i8"), "{s}");
    // memchr arg inlines the nullable cursor via map_or: ...map_or(...null..., |idx| ...offset(idx)...)
    assert!(
        s.contains("ptr_idx.map_or(") && s.contains(".offset(idx)"),
        "expected memchr to inline nullable ptr_idx via map_or from the field base:\n{s}"
    );
    assert!(!s.contains("memchr(ptr as *const core::ffi::c_void"), "{s}");
    assert!(!s.contains("ptr = found.offset(1)"), "{s}");
    assert!(
        !s.contains("ptr = ((*state).buffer).offset(ptr_idx)"),
        "{s}"
    );
}

#[test]
fn borrow_ownership_slot_universe_tracks_local_pointer_depths() {
    use rustc_middle::mir::Local;
    use rustc_span::def_id::{DefIndex, LocalDefId};

    use crate::analyses::borrow_ownership::{
        SlotKind,
        slots::{SlotId, SlotOwner, SlotUniverse, StructFieldSlot},
    };

    assert_eq!(
        SlotKind::ALL,
        [SlotKind::Raw, SlotKind::Ref, SlotKind::Owning]
    );

    let pointer = Local::from_u32(1);
    let nested_pointer = Local::from_u32(2);
    let unregistered = Local::from_u32(3);
    let field = StructFieldSlot {
        struct_did: LocalDefId {
            local_def_index: DefIndex::from_u32(42),
        },
        field_index: 1,
    };
    let mut universe = SlotUniverse::from_local_depths([(pointer, 1), (nested_pointer, 2)]);
    universe.register_field(field, 2);

    assert_eq!(universe.len(), 5);
    assert_eq!(
        universe.slots_for_local(pointer),
        Some(SlotId::from_usize(0)..SlotId::from_usize(1))
    );
    assert_eq!(
        universe.slots_for_local(nested_pointer),
        Some(SlotId::from_usize(1)..SlotId::from_usize(3))
    );
    assert_eq!(
        universe.slots_for_field(field),
        Some(SlotId::from_usize(3)..SlotId::from_usize(5))
    );

    let pointer_slot = universe
        .slot_for_local_depth(pointer, 0)
        .expect("slot for local pointer");
    assert_eq!(pointer_slot, SlotId::from_usize(0));
    assert_eq!(universe.slot(pointer_slot).owner, SlotOwner::Local(pointer));
    assert_eq!(universe.slot(pointer_slot).depth, 0);

    assert!(universe.slot_for_local_depth(pointer, 1).is_none());
    assert!(universe.slots_for_local(unregistered).is_none());
    assert!(universe.slot_for_local_depth(unregistered, 0).is_none());

    let nested_outer = universe
        .slot_for_local_depth(nested_pointer, 0)
        .expect("outer slot for nested pointer");
    let nested_inner = universe
        .slot_for_local_depth(nested_pointer, 1)
        .expect("inner slot for nested pointer");

    assert_eq!(nested_outer, SlotId::from_usize(1));
    assert_eq!(nested_inner, SlotId::from_usize(2));
    assert_eq!(
        universe.slot(nested_outer).owner,
        SlotOwner::Local(nested_pointer)
    );
    assert_eq!(
        universe.slot(nested_inner).owner,
        SlotOwner::Local(nested_pointer)
    );
    assert_eq!(universe.slot(nested_outer).depth, 0);
    assert_eq!(universe.slot(nested_inner).depth, 1);
    assert!(universe.slot_for_local_depth(nested_pointer, 2).is_none());

    let field_outer = universe
        .slot_for_field_depth(field, 0)
        .expect("outer field slot");
    let field_inner = universe
        .slot_for_field_depth(field, 1)
        .expect("inner field slot");

    assert_eq!(field_outer, SlotId::from_usize(3));
    assert_eq!(field_inner, SlotId::from_usize(4));
    assert_eq!(universe.slot(field_outer).owner, SlotOwner::Field(field));
    assert_eq!(universe.slot(field_inner).owner, SlotOwner::Field(field));
    assert_eq!(universe.slot(field_outer).depth, 0);
    assert_eq!(universe.slot(field_inner).depth, 1);
    assert!(universe.slot_for_field_depth(field, 2).is_none());
}

#[test]
fn test_array_local_rewriter_rejects_size_changing_receiver_cast() {
    // `(p as *mut i8).offset(12)` advances 12 *bytes* past an *mut i32 base;
    // recording index 12 and re-materializing in i32 units would be 48 bytes.
    // the rewriter must leave q untouched.
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = (p as *mut i8).offset(12) as *mut i32;
    *p = 1;
    *q = 3;
    *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(
        !changed,
        "size-changing receiver cast must not be rewritten:\n{s}"
    );
    assert!(
        s.contains("let mut q: *mut i32"),
        "q must stay a raw pointer:\n{s}"
    );
    assert!(!s.contains("q_idx"), "no index must be derived for q:\n{s}");
}

#[test]
fn test_array_local_rewriter_keeps_offset_then_cast() {
    // offset-then-cast: the index is computed in base (i32) units, the cast is
    // applied to the result, so this stays rewritten (control).
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = p.offset(3) as *mut i32;
    *p = 1;
    *q = 3;
    *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut q_idx: isize = (3) as isize"), "{s}");
    assert!(!s.contains("let mut q: *mut i32"), "{s}");
}

#[test]
fn test_array_local_rewriter_keeps_equal_size_receiver_cast() {
    // `(p as *const u8).offset(3)` over an *mut i8 base: pointee size is
    // unchanged (1 == 1), so the index unit is correct and the rewrite stands.
    let code = r#"
pub unsafe fn foo(mut p: *mut i8) -> i8 {
    let mut q: *mut i8 = (p as *const u8).offset(3) as *mut i8;
    *p = 1;
    *q = 3;
    *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut q_idx: isize = (3) as isize"), "{s}");
    assert!(!s.contains("let mut q: *mut i8"), "{s}");
}

#[test]
fn test_array_local_rewriter_offset_from_not_folded_across_size_cast() {
    // q is a size-changing cast cursor; its offset_from(r) must NOT be folded
    // into an index subtraction, because q has no valid base-unit index.
    let code = r#"
pub unsafe fn foo(mut base: *mut i32) -> isize {
    let mut q: *mut i32 = (base as *mut i8).offset(12) as *mut i32;
    let mut r: *mut i32 = base.offset(1);
    *base = 0;
    *q = 0;
    *r = 0;
    q.offset_from(r)
}
"#;
    let (s, _changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // r may be independently rewritten to r_idx (no size-changing cast on r's
    // receiver), so we check only that q is the (unrewritten) receiver of
    // offset_from, not that r specifically appears as the argument.
    assert!(
        s.contains("q.offset_from("),
        "offset_from must be preserved:\n{s}"
    );
    assert!(
        !s.contains("q_idx"),
        "no index must be derived for the cast cursor q:\n{s}"
    );
}

#[test]
fn test_array_local_trace_records_selection_and_apply_for_rewritten_group() {
    use crate::rewriter::array_local_trace::{TraceStage, TraceSubject};
    // a simple selectable + rewritten group (mirrors
    // test_array_local_rewriter_rewrites_simple_non_null_derived_local).
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = p.offset(3);
    *p = 1;
    *q = 3;
    *q
}
"#;
    let events = array_local_trace_events(code);
    assert!(
        events.iter().any(|e| e.stage == TraceStage::Selection),
        "expected at least one Selection event: {events:#?}"
    );
    assert!(
        events.iter().any(|e| e.stage == TraceStage::Apply
            && matches!(&e.subject, TraceSubject::Member(name) if name == "q")),
        "expected an Apply event for member q: {events:#?}"
    );
}

#[test]
fn test_array_local_trace_disabled_is_neutral() {
    // enabling the trace must not change the rewritten output, and the disabled
    // trace must record nothing.
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = p.offset(3);
    *p = 1;
    *q = 3;
    *q
}
"#;
    let (src_enabled, _events) = ::utils::compilation::run_compiler_on_str(code, |tcx| {
        crate::rewriter::rewrite_array_local_provenance_trace(&Config::default(), tcx, true)
    })
    .unwrap();
    let (src_disabled, events_disabled) = ::utils::compilation::run_compiler_on_str(code, |tcx| {
        crate::rewriter::rewrite_array_local_provenance_trace(&Config::default(), tcx, false)
    })
    .unwrap();
    assert!(
        events_disabled.is_empty(),
        "disabled trace must record nothing: {events_disabled:#?}"
    );
    assert_eq!(
        src_enabled, src_disabled,
        "enabling the trace must not change pass output"
    );
}

#[test]
fn test_array_local_trace_records_prune_drop_with_assignment_text() {
    use crate::rewriter::array_local_trace::{TraceDecision, TraceStage};
    // q is reassigned via an expression the index rewrite cannot handle, so the
    // prune pass drops it; the trace records a Prune/Dropped event whose reason
    // includes the offending assignment text.
    let code = r#"
pub unsafe fn foo(mut p: *mut i32) -> i32 {
    let mut q: *mut i32 = std::ptr::null_mut();
    q = p.offset(if q.is_null() { 0 } else { 1 });
    *q
}
"#;
    let events = array_local_trace_events(code);
    assert!(
        events.iter().any(|e| e.stage == TraceStage::Prune
            && e.decision == TraceDecision::Dropped
            && e.reason.contains("q.is_null()")),
        "expected a Prune/Dropped event mentioning the offending assignment: {events:#?}"
    );
}

#[test]
fn test_array_local_partial_group_characterization() {
    // characterization of the spec's partial_group() shape. with conditional
    // cursor support (task 2), q's `if`-RHS is now derivable: both branches
    // express as index values relative to `p_idx`, so q is fully index-rewritten.
    let code = r#"
pub unsafe fn partial_group() -> i32 {
    let mut buf = [0i32; 4];
    let mut p = buf.as_mut_ptr();
    let mut q = p.offset(1);
    q = if *p == 0 { p.offset(2) } else { p };
    *p = 1;
    *q = 2;
    *p + *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    // the rewritten source must always compile (no undeclared *_idx).
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // both p and q are now index-rewritten.
    assert!(changed, "p and q should be rewritten: {s}");
    assert!(s.contains("p_idx"), "p rewritten to an index: {s}");
    assert!(
        s.contains("let mut p_idx: isize = 0isize"),
        "p_idx initialized: {s}"
    );
    assert!(s.contains("q_idx"), "q rewritten to an index: {s}");
    assert!(
        s.contains("(buf).as_ptr().offset(p_idx) as *mut i32"),
        "p accesses use buf base with p_idx: {s}"
    );
}

#[test]
fn test_array_local_rewriter_copies_group_member_in_init_and_assignment() {
    // q is initialized and re-assigned by directly copying p (another member of
    // the same {base, p, q} group). both must lower to an index copy q_idx = p_idx.
    let code = r#"
pub unsafe fn foo(mut base: *mut i32, n: isize) -> i32 {
    let mut p: *mut i32 = base.offset(n);
    let mut q: *mut i32 = p;
    *q = 1;
    q = p;
    *q = 2;
    *p + *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("p_idx"), "p rewritten: {s}");
    assert!(s.contains("q_idx"), "q rewritten: {s}");
    // both the init and the assignment copy the index.
    assert!(s.matches("q_idx").count() >= 2, "q copied from p_idx: {s}");
    assert!(
        !s.contains("let mut q: *mut i32 = p"),
        "raw copy removed: {s}"
    );
}

#[test]
fn test_array_local_rewriter_rejects_cross_group_copy() {
    // q is copied from `other`, a raw pointer that is NOT in q's group. q must
    // stay raw (item-6 model) and the output must still compile.
    let code = r#"
pub unsafe fn foo(mut base: *mut i32, other: *mut i32, n: isize) -> i32 {
    let mut p: *mut i32 = base.offset(n);
    let mut q: *mut i32 = other;
    *p = 1;
    *q = 2;
    *p + *q
}
"#;
    let (s, _changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(
        s.contains("let mut q: *mut i32 = other"),
        "cross-group copy stays raw: {s}"
    );
    assert!(!s.contains("q_idx"), "q not index-rewritten: {s}");
}

#[test]
fn test_array_local_rewriter_lowers_member_relative_conditional() {
    // p is updated by a conditional whose branches are q.offset(1) and q (a
    // sibling member). it must lower to an index-valued conditional.
    let code = r#"
pub unsafe fn foo(mut base: *mut i32, n: isize) -> i32 {
    let mut p: *mut i32 = base.offset(n);
    let mut q: *mut i32 = p;
    q = q.offset(1);
    p = if *q != 0 { q.offset(1) } else { q };
    *p + *q
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // the emitted form splits `p_idx =` and `if` across a line break, so check
    // both parts independently.
    assert!(
        s.contains("p_idx ="),
        "p updated via an index assignment: {s}"
    );
    assert!(
        s.contains("if *((base).offset(q_idx)"),
        "condition rewrites *q to base-indexed deref: {s}"
    );
    assert!(
        s.contains("(q_idx) + ((1) as isize)"),
        "then branch is q_idx+1: {s}"
    );
    assert!(s.contains("else { q_idx }"), "else branch is q_idx: {s}");
    assert!(
        !s.contains("p = if"),
        "no raw pointer conditional for p: {s}"
    );
}

#[test]
fn test_array_local_rewriter_lowers_base_relative_conditional() {
    // both branches derive from the base; indices 2 and 0. a second member `p`
    // ensures the planner forms a group (a lone `q = base` with no offset may
    // not trigger planning).
    let code = r#"
pub unsafe fn foo(mut base: *mut i32, c: bool) -> i32 {
    let mut p: *mut i32 = base.offset(1);
    let mut q: *mut i32 = base;
    q = if c { base.offset(2) } else { base };
    *q + *p
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("q_idx"), "q rewritten with index: {s}");
    assert!(!s.contains("q = if"), "no raw pointer conditional: {s}");
}

#[test]
fn test_array_local_rewriter_rejects_conditional_without_else() {
    // a conditional missing an else branch is unsupported; q stays raw.
    let code = r#"
pub unsafe fn foo(mut base: *mut i32, n: isize, c: bool) -> i32 {
    let mut q: *mut i32 = base.offset(n);
    if c { q = q.offset(1); }
    *q
}
"#;
    let (s, _changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // an `if` statement (no else, not an assignment RHS) is not a conditional
    // cursor update; q's self-advance inside it stays handled as today.
}

#[test]
fn test_array_local_rewriter_rewrites_tu_linkage_read_stdin_shape() {
    // mirrors B02_synthetic/tu_linkage::read_stdin: a local array base with two
    // cursors where q is copied from p (let mut q = p) and p is updated by a
    // conditional (p = if *q != 0 { q.offset(1) } else { q }).  both must rewrite
    // to indices.
    //
    // `total += *q + *p` keeps p live at the same MIR location as q so that the
    // simultaneous-liveness gate in classify_rewrite_groups admits the {buf,p,q}
    // group.  the real B02_synthetic/tu_linkage corpus case also passes the gate
    // (p is materialized and read in the body).
    let code = r#"
pub unsafe fn read_stdin(mut buf: [i32; 64]) -> i32 {
    let mut total: i32 = 0;
    let mut p: *mut i32 = buf.as_mut_ptr();
    while *p != 0 {
        let mut q: *mut i32 = p;
        while *q != 0 && *q != 32 {
            q = q.offset(1);
        }
        total += *q + *p;
        p = if *q != 0 { q.offset(1) } else { q };
    }
    total
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("p_idx"), "p rewritten to an index: {s}");
    assert!(s.contains("q_idx"), "q rewritten to an index: {s}");
    // q is initialized by copying p — let mut q_idx: isize = p_idx.
    assert!(
        s.contains("let mut q_idx: isize = p_idx"),
        "q copy lowered to index copy: {s}"
    );
    // the emitted form splits `p_idx =` and `if` across a line break — check parts.
    assert!(s.contains("p_idx ="), "p updated via index assignment: {s}");
    // no raw pointer offset operations remain for the two cursors.
    assert!(!s.contains("q = q.offset(1)"), "q advance lowered: {s}");
    assert!(!s.contains("p = if *q"), "p conditional lowered: {s}");
    // p is fully index-only: no kept raw pointer or reference binding.
    assert!(
        !s.contains("let mut p: *mut i32") && !s.contains("let mut p: &i32"),
        "p is index-only: {s}"
    );
}

#[test]
fn test_array_local_rewriter_copies_nullable_group_member() {
    // q starts null (Option<isize>) and is later copied from p; the copy must
    // preserve the Option value (q_idx = p_idx), not re-wrap it.
    let code = r#"
pub unsafe fn foo(mut base: *mut i32, n: isize, c: bool) -> i32 {
    let mut p: *mut i32 = std::ptr::null_mut();
    if c { p = base.offset(n); }
    let mut q: *mut i32 = std::ptr::null_mut();
    q = p;
    if !q.is_null() { *q = 7; }
    0
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // p and q are Option<isize>; the copy is a plain Option assignment.
    assert!(
        s.contains("q_idx = p_idx"),
        "nullable copy preserves the Option: {s}"
    );
    assert!(
        !s.contains("q_idx = Some(p_idx)"),
        "no re-wrap of the Option: {s}"
    );
}

#[test]
fn test_array_local_rewriter_keeps_moving_deref_cursor_index_only() {
    // two cursors that both move and deref (never passed to a call, never stored
    // as a pointer value) stay index-only instead of kept &T references.
    let code = r#"
pub unsafe fn foo(mut base: *mut i32, n: isize) -> i32 {
    let mut p: *mut i32 = base.offset(1);
    let mut q: *mut i32 = base.offset(2);
    let mut total: i32 = 0;
    let mut i: isize = 0;
    while i < n {
        total += *p + *q;
        p = p.offset(1);
        q = q.offset(1);
        i += 1;
    }
    total
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(
        s.contains("p_idx") && s.contains("q_idx"),
        "cursors index-rewritten: {s}"
    );
    assert!(
        !s.contains("let mut p: &i32") && !s.contains("let mut q: &i32"),
        "moving deref cursors are index-only, not kept references: {s}"
    );
}

#[test]
fn test_array_local_rewriter_inline_materializes_call_argument_cursor() {
    // a moving cursor passed to a foreign function stays index-only; the raw
    // pointer is reconstructed inline at the call, with no kept binding.
    let code = r#"
unsafe extern "C" { fn sink(p: *const i32) -> i32; }
pub unsafe fn foo(mut base: *mut i32, n: isize) -> i32 {
    let mut p: *mut i32 = base.offset(1);
    let mut q: *mut i32 = base.offset(2);
    let mut total: i32 = 0;
    let mut i: isize = 0;
    while i < n {
        total += sink(p) + *q;
        p = p.offset(1);
        q = q.offset(1);
        i += 1;
    }
    total
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("p_idx"), "p is index-only: {s}");
    assert!(
        !s.contains("let mut p: *mut i32"),
        "no kept raw pointer for p: {s}"
    );
    assert!(s.contains("sink("), "call preserved: {s}");
}

#[test]
fn test_array_local_rewriter_rewrites_single_base_strstr_cursor() {
    // a cursor initialised from strstr(base, needle) becomes a nullable
    // Option<isize> index initialised via offset_from against the base.
    // q is a second mutable cursor (base + n) that keeps base live in the loop
    // so the simultaneous-liveness gate in classify_rewrite_groups admits the
    // {base, p, q} group.
    let code = r#"
unsafe extern "C" { fn strstr(h: *const i8, n: *const i8) -> *mut i8; }
pub unsafe fn foo(base: *mut i8, needle: *const i8, n: isize) -> i32 {
    let mut p: *mut i8 = strstr(base, needle);
    let mut q: *mut i8 = base.offset(n);
    let mut total: i32 = 0;
    let mut i: isize = 0;
    while i < n {
        if !p.is_null() {
            total += *p as i32;
            p = p.offset(1);
        }
        total += *q as i32;
        q = q.offset(-1);
        i += 1;
    }
    total
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("p_idx"), "p index-rewritten: {s}");
    assert!(s.contains("Option<isize>"), "nullable index: {s}");
    assert!(s.contains("offset_from"), "offset_from init: {s}");
    assert!(
        !s.contains("let mut p: *mut i8"),
        "no kept raw pointer for p: {s}"
    );
}

// ── epoch split (pointer-pass stage before array-local provenance) ────────────

fn rewrite_epoch_split_with_config(code: &str, config: &Config) -> (String, bool) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| rewrite_epoch_split(config, tcx)).unwrap()
}

fn run_epoch_split_test(code: &str, includes: &[&str], excludes: &[&str]) {
    let (s, _) = rewrite_epoch_split_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
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

#[test]
fn test_epoch_split_skips_single_base() {
    // a single-base scratch local is NOT split: only genuine multi-base reuse is
    // split, so the original binding and its sole assignment are left untouched.
    run_epoch_split_test(
        r#"
pub unsafe extern "C" fn f(mut a: *mut i8) -> *mut i8 {
    let mut x: *mut i8 = 0 as *mut i8;
    x = a;
    return x;
}
        "#,
        &["let mut x: *mut i8 = 0 as *mut i8", "x = a", "return x"],
        &["x_0"],
    )
}

#[test]
fn test_epoch_split_sequential_bases() {
    // two unrelated bases through one scratch local -> two epoch lets.
    run_epoch_split_test(
        r#"
pub unsafe extern "C" fn f(mut a: *mut i8, mut b: *mut i8) -> *mut i8 {
    let mut x: *mut i8 = 0 as *mut i8;
    x = a;
    let _c: i8 = *x;
    x = b;
    return x;
}
        "#,
        &[
            "let mut x_0: *mut i8 = a",
            "let mut x_1: *mut i8 = b",
            "_c: i8 = *x_0",
            "return x_1",
        ],
        &["let mut x: *mut i8 = 0 as *mut i8"],
    )
}

#[test]
fn test_epoch_split_same_epoch_movement() {
    // `.offset` on the same local keeps the epoch and stays an assignment (not a
    // `let`); a later distinct base gives the local a second epoch so it splits.
    run_epoch_split_test(
        r#"
pub unsafe extern "C" fn f(mut a: *mut i8, mut b: *mut i8) -> *mut i8 {
    let mut x: *mut i8 = 0 as *mut i8;
    x = a;
    x = x.offset(1 as isize);
    let _c: i8 = *x;
    x = b;
    return x;
}
        "#,
        &[
            "let mut x_0: *mut i8 = a",
            "x_0 = x_0.offset",
            "let mut x_1: *mut i8 = b",
            "return x_1",
        ],
        &["let mut x: *mut i8 = 0 as *mut i8"],
    )
}

#[test]
fn test_epoch_split_rejects_addr_taken() {
    // the local is rejected because it is address-taken (`&mut x`), leaving the
    // scratch local unchanged.
    run_epoch_split_test(
        r#"
pub unsafe extern "C" fn f(mut a: *mut u8) -> *mut u8 {
    let mut x: *mut u8 = 0 as *mut u8;
    x = a;
    x = x.wrapping_add(1 as usize);
    let p: *mut *mut u8 = &mut x;
    return x;
}
        "#,
        &["let mut x: *mut u8 = 0 as *mut u8"],
        &["x_0"],
    )
}

#[test]
fn test_epoch_split_branch_contained() {
    // two branch-contained epochs (one per arm), each used only inside its arm and
    // not after the join -> the local has two epochs and splits within each branch.
    run_epoch_split_test(
        r#"
extern "C" {
    fn foo(_: *mut i8);
}
pub unsafe extern "C" fn f(mut a: *mut i8, mut b: *mut i8, cond: i32) {
    let mut x: *mut i8 = 0 as *mut i8;
    if cond != 0 {
        x = a;
        foo(x);
    } else {
        x = b;
        foo(x);
    }
}
        "#,
        &[
            "let mut x_0: *mut i8 = a",
            "foo(x_0)",
            "let mut x_1: *mut i8 = b",
            "foo(x_1)",
        ],
        &["let mut x: *mut i8 = 0 as *mut i8"],
    )
}

#[test]
fn test_epoch_split_rejects_cross_join_use() {
    // one branch assigns; the post-if use may see old-or-new -> reject, preserve write.
    run_epoch_split_test(
        r#"
pub unsafe extern "C" fn f(mut a: *mut i8, cond: i32) -> *mut i8 {
    let mut x: *mut i8 = 0 as *mut i8;
    if cond != 0 {
        x = a;
    }
    return x;
}
        "#,
        &["let mut x: *mut i8 = 0 as *mut i8", "x = a", "return x"],
        &["x_0"],
    )
}

#[test]
fn test_epoch_split_rejects_loop_base_change() {
    // a base change inside a loop cannot be promoted to a `let` -> reject.
    run_epoch_split_test(
        r#"
pub unsafe extern "C" fn f(mut a: *mut i8, n: i32) -> *mut i8 {
    let mut x: *mut i8 = 0 as *mut i8;
    let mut i: i32 = 0;
    while i < n {
        x = a;
        i += 1;
    }
    return x;
}
        "#,
        &["let mut x: *mut i8 = 0 as *mut i8", "x = a"],
        &["x_0"],
    )
}

#[test]
fn test_epoch_split_loop_same_epoch_movement() {
    // incoming epoch, loop only moves it (renamed, no `let` in loop); a later
    // distinct base gives the local a second epoch so it splits.
    run_epoch_split_test(
        r#"
pub unsafe extern "C" fn f(mut a: *mut i8, mut b: *mut i8, n: i32) -> *mut i8 {
    let mut x: *mut i8 = 0 as *mut i8;
    x = a;
    let mut i: i32 = 0;
    while i < n {
        x = x.offset(1 as isize);
        i += 1;
    }
    x = b;
    return x;
}
        "#,
        &[
            "let mut x_0: *mut i8 = a",
            "x_0 = x_0.offset",
            "let mut x_1: *mut i8 = b",
            "return x_1",
        ],
        &["let mut x: *mut i8 = 0 as *mut i8"],
    )
}

#[test]
fn test_epoch_split_use_kinds() {
    // deref, null check, call arg, cast, and pointer-method uses all rename to the
    // epoch local; a second distinct base gives the local two epochs so it splits.
    run_epoch_split_test(
        r#"
pub unsafe extern "C" fn use_ptr(p: *mut i8) {}
pub unsafe extern "C" fn f(mut a: *mut i8, mut b: *mut i8) -> i32 {
    let mut x: *mut i8 = 0 as *mut i8;
    x = a;
    let d: i8 = *x;                 // deref
    if !x.is_null() {               // null check + pointer method
        use_ptr(x);                 // call argument
        let c: *const i8 = x as *const i8; // cast
    }
    x = b;
    return d as i32;
}
        "#,
        &[
            "let mut x_0: *mut i8 = a",
            "*x_0",
            "x_0.is_null()",
            "use_ptr(x_0)",
            "x_0 as *const i8",
            "let mut x_1: *mut i8 = b",
        ],
        &["let mut x: *mut i8 = 0 as *mut i8"],
    )
}

#[test]
fn test_epoch_split_parse_uname_shape() {
    run_epoch_split_test(
        r#"
extern "C" {
    fn strstr(_: *const i8, _: *const i8) -> *mut i8;
    fn get_os_arch(_: *mut i8) -> *mut i8;
    fn use_c(_: *mut i8);
}
pub unsafe extern "C" fn f(mut uname: *mut i8, cond: i32) {
    let mut str_tmp: *mut i8 = 0 as *mut i8;
    str_tmp = strstr(uname, uname);
    if cond != 0 {
        str_tmp = str_tmp.offset(7 as isize);
        use_c(str_tmp);
    } else {
        str_tmp = get_os_arch(uname);
        if !str_tmp.is_null() {
            use_c(str_tmp);
        }
    }
}
        "#,
        &[
            "let mut str_tmp_0: *mut i8 = strstr",
            "str_tmp_0 = str_tmp_0.offset",
            "let mut str_tmp_1: *mut i8 = get_os_arch",
            "str_tmp_1.is_null()",
        ],
        &["let mut str_tmp: *mut i8 = 0 as *mut i8"],
    )
}

#[test]
fn test_epoch_split_rejects_epoch_escaping_block() {
    // two epochs where the second is created inside a nested block and then used
    // after the block: the block-scoped epoch `let` would be out of scope, so the
    // whole local is rejected (left unsplit) rather than dangling.
    run_epoch_split_test(
        r#"
pub unsafe extern "C" fn f(mut a: *mut i8, mut b: *mut i8) -> *mut i8 {
    let mut x: *mut i8 = 0 as *mut i8;
    x = a;
    'c_blk: {
        x = b;
    }
    return x;
}
        "#,
        &[
            "let mut x: *mut i8 = 0 as *mut i8",
            "x = a",
            "x = b",
            "return x",
        ],
        &["x_0", "x_1"],
    )
}

#[test]
fn test_epoch_split_then_array_local_index_backing() {
    // the integration the stage exists for: a multi-base scratch local splits into
    // per-epoch locals, and the array-local pass then index-rewrites each epoch
    // against its own base. without the split, `q` is multi-base and the
    // array-local pass cannot rewrite it at all.
    let code = r#"
pub unsafe fn foo(mut p: *mut i32, mut r: *mut i32) -> i32 {
    let mut q: *mut i32 = 0 as *mut i32;
    q = p.offset(3);
    *p = 1;
    *q = 3;
    let a: i32 = *q;
    q = r.offset(1);
    *r = 2;
    *q = 5;
    a
}
"#;
    let config = Config::default();
    let (split, changed) = rewrite_epoch_split_with_config(code, &config);
    assert!(changed, "{split}");
    let (s, changed) = rewrite_array_local_provenance_with_config(&split, &config);
    assert!(changed, "{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut q_0_idx: isize = (3) as isize"), "{s}");
    assert!(s.contains("let mut q_1_idx: isize = (1) as isize"), "{s}");
    assert!(s.contains("*((p).offset(q_0_idx) as *mut i32) = 3"), "{s}");
    assert!(s.contains("*((r).offset(q_1_idx) as *mut i32) = 5"), "{s}");
    assert!(!s.contains("let mut q: *mut i32"), "{s}");
}

#[test]
fn test_array_local_rewriter_folds_value_position_offset_chain() {
    // a projection chain used as a pointer VALUE (call argument) must fold its
    // offsets into the nullable index closure instead of stacking a raw
    // `.offset` on top of the materialized pointer.
    let code = r#"
unsafe extern "C" {
    fn strstr(a: *const i8, b: *const i8) -> *mut i8;
    fn strdup(a: *const i8) -> *mut i8;
    fn consume(p: *mut i8);
}

pub unsafe fn f(mut uname: *mut i8, k: isize) -> *mut i8 {
    let mut out: *mut i8 = std::ptr::null_mut();
    let mut p0: *mut i8 = strstr(uname, b"x\0" as *const u8 as *const i8);
    if !p0.is_null() {
        *p0 = 0;
        p0 = p0.offset(2);
        p0 = p0.offset(1);
        consume(p0.offset(k));
        out = strdup(p0);
    } else {
        let mut p1: *mut i8 = strstr(uname, b"y\0" as *const u8 as *const i8);
        if !p1.is_null() {
            *p1 = 0;
            p1 = p1.offset(1);
            out = strdup(p1);
        }
    }
    return out;
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "expected cursors to be index-rewritten:\n{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    // the call-derived index seeds from the bare base, not `base.offset(0isize)`.
    assert!(s.contains("offset_from((uname))"), "{s}");
    assert!(!s.contains("offset(0isize)"), "{s}");
    // the chained value use folds its offset into the closure index...
    assert!(s.contains(".offset((idx) + (k))"), "{s}");
    // ...instead of stacking a second raw offset on the materialized pointer.
    assert!(!s.contains(".offset(k)"), "{s}");
}

#[test]
fn test_array_local_rewriter_skips_unprofitable_nullable_raw_base_group() {
    // value-heavy nullable cursors of a raw base: every call argument, deref
    // write, and value use would keep one raw offset per site after an index
    // rewrite, while only one self-advance per cursor goes away. the cost
    // model keeps the raw locals instead of net-increasing unsafe operations.
    let code = r#"
unsafe extern "C" {
    fn strstr(a: *const i8, b: *const i8) -> *mut i8;
    fn strdup(a: *const i8) -> *mut i8;
    fn consume(p: *mut i8);
}

pub unsafe fn f(mut uname: *mut i8) -> *mut i8 {
    let mut out: *mut i8 = std::ptr::null_mut();
    let mut p0: *mut i8 = strstr(uname, b"x\0" as *const u8 as *const i8);
    if !p0.is_null() {
        *p0 = 0;
        p0 = p0.offset(2);
        consume(p0);
        consume(p0);
        out = strdup(p0);
    }
    return out;
}
"#;
    // the guard applies to raw parameter bases of c-exposed functions only:
    // any other base may still be upgraded to a slice by later stages.
    let mut config = Config::default();
    config.c_exposed_fns.insert("f".to_string());
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &config);
    let _ = changed;
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut p0: *mut i8"), "{s}");
    assert!(!s.contains("p0_idx"), "{s}");
}
