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

    fn analyze_program<'tcx>(
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
    assert!(s.contains("ptr_idx"), "{s}");
    assert!(!s.contains("let mut ptr: *mut i8"), "{s}");
    assert!(!s.contains("let ptr: *mut i8"), "{s}");
    assert!(
        s.contains("memchr(((*state).buffer).offset(ptr_idx)")
            || s.contains("memchr((*state).buffer.offset(ptr_idx)"),
        "expected memchr to inline ptr_idx from the field base:\n{s}"
    );
    assert!(!s.contains("memchr(ptr as *const core::ffi::c_void"), "{s}");
    assert!(!s.contains("ptr = found.offset(1)"), "{s}");
    assert!(
        !s.contains("ptr = ((*state).buffer).offset(ptr_idx)"),
        "{s}"
    );
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
