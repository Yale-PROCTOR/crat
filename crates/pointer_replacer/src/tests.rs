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

fn assert_slop_prone_slice_cast_trims_byte_prefix(
    s: &str,
    cast_fn: &str,
    target_ty: &str,
    direct_sources: &[&str],
) {
    let size_patterns = [
        format!("std::mem::size_of::<{target_ty}>()"),
        format!("::std::mem::size_of::<{target_ty}>()"),
        format!("core::mem::size_of::<{target_ty}>()"),
        format!("::core::mem::size_of::<{target_ty}>()"),
    ];
    assert!(
        size_patterns.iter().any(|pattern| s.contains(pattern)),
        "Expected slop-prone bytemuck cast to trim with target size {target_ty}:\n{s}"
    );

    assert!(
        s.contains("bytemuck::cast_slice::<_, u8>")
            || s.contains("bytemuck::cast_slice_mut::<_, u8>"),
        "Expected slop-prone bytemuck cast to build a byte-prefix view before target cast:\n{s}"
    );

    for source in direct_sources {
        let direct_cast = format!("bytemuck::{cast_fn}::<_, {target_ty}>({source})");
        assert!(
            !s.contains(&direct_cast),
            "Expected slop-prone bytemuck cast not to reinterpret the whole source slice `{source}` directly:\n{s}"
        );
    }
}

fn assert_direct_slice_cast_without_byte_prefix(s: &str, cast_fn: &str, target_ty: &str) {
    assert!(
        s.contains(&format!("bytemuck::{cast_fn}::<_, {target_ty}>")),
        "Expected direct bytemuck cast to {target_ty}:\n{s}"
    );
    assert!(
        !s.contains("__crat_bytes") && !s.contains("__crat_len"),
        "Expected divisible bytemuck cast not to use byte-prefix trimming:\n{s}"
    );
}

fn run_typecheck_test_after_shape_check(code: &str, includes: &[&str], excludes: &[&str]) {
    let (s, _) = rewrite_with_config(code, &Config::default());
    for include in includes {
        assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
    }
    for exclude in excludes {
        assert!(
            !s.contains(exclude),
            "Expected not to find `{exclude}` in:\n{s}",
        );
    }
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
}

fn run_raw_origin_cursor_rejection_test(code: &str, includes: &[&str], excludes: &[&str]) {
    let (s, _) = rewrite_with_config(code, &Config::default());
    for exclude in ["crate::slice_cursor::SliceCursor", "from_raw_parts"]
        .iter()
        .copied()
        .chain(excludes.iter().copied())
    {
        assert!(
            !s.contains(exclude),
            "Expected raw-origin rewrite not to find `{exclude}` in:\n{s}",
        );
    }
    for include in includes {
        assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
    }
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
}

fn run_adt_lifetime_family_test(
    code: &str,
    unified_lifetime_includes: &[&str],
    raw_pointer_includes: &[&str],
) {
    let config = Config::default();
    let (s, _) = rewrite_with_config(code, &config);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);

    let has_unified_lifetimes = unified_lifetime_includes
        .iter()
        .all(|include| s.contains(include));
    let has_raw_pointers = raw_pointer_includes
        .iter()
        .all(|include| s.contains(include));
    assert!(
        has_unified_lifetimes || has_raw_pointers,
        "Expected rewritten code to either use one ADT lifetime family or keep the affected pointers raw.\n\
Unified-lifetime fragments: {unified_lifetime_includes:?}\n\
Raw-pointer fragments: {raw_pointer_includes:?}\n\
Rewritten code:\n{s}",
    );
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
fn test_rewriter_e0499_callback_payload_promoted_field_reuse_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Repo {
    pub value: i32,
}

#[repr(C)]
pub struct ParentData {
    pub repo: *mut Repo,
    pub count: i32,
}

pub unsafe fn bump_repo(repo: *mut Repo) -> i32 {
    (*repo.offset(0)).value += 1;
    (*repo.offset(0)).value
}

pub unsafe fn visit(payload: *mut core::ffi::c_void) {
    let data = payload as *mut ParentData;
    (*data).count += 1;
}

pub unsafe fn create(repo: *mut Repo) -> i32 {
    let mut data = ParentData { repo: repo, count: 0 };
    let before = bump_repo(repo);
    visit(&raw mut data as *mut core::ffi::c_void);
    (*data.repo.offset(0)).value += data.count;
    before + (*data.repo.offset(0)).value
}
"#,
        &[
            "pub struct ParentData {",
            "pub repo: *mut Repo",
            "pub unsafe fn bump_repo(mut repo: &mut [crate::Repo]) -> i32",
            "pub unsafe fn create(mut repo: &mut [crate::Repo]) -> i32",
            ".as_mut_ptr()",
        ],
        &[
            "pub struct ParentData<'a>",
            "pub repo: &'a mut [crate::Repo]",
            "pub unsafe fn bump_repo(mut repo: *mut crate::Repo)",
        ],
    );
}

#[test]
fn test_rewriter_e0499_callback_payload_field_reuse_with_pointer_comparison_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Repo {
    pub value: i32,
}

#[repr(C)]
pub struct ParentData {
    pub repo: *mut Repo,
}

pub unsafe fn touch(repo: *mut Repo) {
    (*repo.offset(0)).value = (*repo.offset(0)).value.wrapping_add(1);
}

pub unsafe fn enqueue(payload: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    payload
}

pub unsafe fn create(repo: *mut Repo) -> i32 {
    let mut data = ParentData { repo: repo };
    let same = data.repo == repo;
    touch(repo);
    enqueue(&raw mut data as *mut core::ffi::c_void);
    if same { (*data.repo.offset(0)).value } else { 0 }
}
"#,
        &[
            "pub struct ParentData {",
            "pub repo: *mut Repo",
            "pub unsafe fn touch(mut repo: &mut [crate::Repo])",
            "pub unsafe fn create(mut repo: &mut [crate::Repo]) -> i32",
            ".as_mut_ptr()",
        ],
        &[
            "pub struct ParentData<'a>",
            "pub repo: &'a mut [crate::Repo]",
            "pub unsafe fn touch(mut repo: *mut crate::Repo)",
        ],
    );
}

#[test]
fn test_rewriter_e0499_callback_payload_scalar_ref_source_stays_promoted() {
    run_test(
        r#"
#[repr(C)]
pub struct Repo {
    pub value: i32,
}

#[repr(C)]
pub struct ParentData {
    pub repo: *mut Repo,
}

pub unsafe fn touch(repo: *mut Repo) {
    (*repo).value += 1;
}

pub unsafe fn visit(payload: *mut core::ffi::c_void) {
    let data = payload as *mut ParentData;
    (*(*data).repo).value += 1;
}

pub unsafe fn create(repo: *mut Repo) -> i32 {
    let mut data = ParentData { repo: repo };
    touch(repo);
    visit(&raw mut data as *mut core::ffi::c_void);
    (*data.repo).value
}
"#,
        &[
            "pub struct ParentData {",
            "pub repo: *mut Repo",
            "pub unsafe fn touch(mut repo: &mut crate::Repo)",
            "pub unsafe fn create(mut repo: Option<&mut crate::Repo>) -> i32",
        ],
        &[
            "pub struct ParentData<'a>",
            "pub repo: &'a mut crate::Repo",
            "pub unsafe fn touch(mut repo: *mut crate::Repo)",
        ],
    );
}

#[test]
fn test_rewriter_e0499_same_call_field_and_raw_parent_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct HashCtx {
    pub value: u8,
}

#[repr(C)]
pub struct Oid {
    pub id: [u8; 4],
}

impl Copy for Oid {}

impl Clone for Oid {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
pub struct PatchArgs {
    pub ctx: HashCtx,
    pub result: Oid,
    pub len: usize,
}

pub unsafe fn hash_final(out: *mut u8, ctx: *mut HashCtx) -> i32 {
    *out.offset(0) = (*ctx).value;
    0
}

pub unsafe fn hash_init(ctx: *mut HashCtx) -> i32 {
    (*ctx).value = 0;
    0
}

pub unsafe fn flush(result: *mut Oid, args: *mut PatchArgs) {
    let ctx: *mut HashCtx = &mut (*args).ctx;
    let mut hash = Oid { id: [0; 4] };
    hash_final(hash.id.as_mut_ptr(), ctx);
    hash_init(ctx);
    let mut i = 0usize;
    while i < (*args).len {
        (*result.offset(0)).id[i] = hash.id[i];
        i += 1;
    }
}

pub unsafe fn caller() -> u8 {
    let mut args = PatchArgs {
        ctx: HashCtx { value: 7 },
        result: Oid { id: [0; 4] },
        len: 1,
    };
    flush(&mut args.result, &mut args);
    args.result.id[0] + args.ctx.value
}
"#,
        &[
            "pub unsafe fn flush(mut result: &mut [crate::Oid],",
            "mut args: *mut crate::PatchArgs)",
            "std::slice::from_mut(&mut (args.result))",
            "&raw mut (args)",
        ],
        &["pub unsafe fn flush(mut result: *mut crate::Oid"],
    );
}

#[test]
fn test_rewriter_e0499_same_call_array_field_and_raw_parent_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct HashCtx {
    pub value: i32,
}

#[repr(C)]
pub struct Work {
    pub ctx: HashCtx,
    pub values: [i32; 4],
    pub len: usize,
}

pub unsafe fn reset(ctx: *mut HashCtx) {
    (*ctx).value += 1;
}

pub unsafe fn fill(values: *mut i32, work: *mut Work) {
    let ctx: *mut HashCtx = &mut (*work).ctx;
    reset(ctx);
    let mut i = 0usize;
    while i < (*work).len {
        *values.offset(i as isize) = (*work).ctx.value;
        i += 1;
    }
}

pub unsafe fn caller() -> i32 {
    let mut work = Work {
        ctx: HashCtx { value: 3 },
        values: [0; 4],
        len: 1,
    };
    fill(work.values.as_mut_ptr(), &mut work);
    work.values[0] + work.ctx.value
}
"#,
        &[
            "pub unsafe fn fill(mut values: &mut [i32], mut work: *mut crate::Work)",
            "&mut (work.values)",
            "&raw mut (work)",
        ],
        &["pub unsafe fn fill(mut values: *mut i32"],
    );
}

#[test]
fn test_rewriter_e0499_nested_same_local_mut_borrow_typechecks() {
    run_test(
        r#"
pub unsafe fn pop(stack: *mut *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let current = *stack.offset(0);
    *stack.offset(0) = core::ptr::null_mut();
    current
}

pub unsafe fn push(stack: *mut *mut core::ffi::c_void, item: *mut core::ffi::c_void) {
    *stack.offset(0) = item;
}

pub unsafe fn caller(item: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let mut list: *mut core::ffi::c_void = item;
    push(&mut list, pop(&mut list));
    list
}
"#,
        &[
            "pub unsafe fn pop(mut stack: &mut [*mut std::ffi::c_void])",
            "-> *mut std::ffi::c_void",
            "pub unsafe fn push(mut stack: &mut [*mut std::ffi::c_void],",
            "mut item: *mut std::ffi::c_void)",
            "std::slice::from_mut(&mut (list))",
        ],
        &[
            "pub unsafe fn pop(mut stack: *mut *mut core::ffi::c_void",
            "pub unsafe fn push(mut stack: *mut *mut core::ffi::c_void",
        ],
    );
}

#[test]
fn test_rewriter_e0499_nested_same_local_mut_borrow_in_later_argument_typechecks() {
    run_test(
        r#"
pub unsafe fn pop(stack: *mut *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let current = *stack.offset(0);
    *stack.offset(0) = core::ptr::null_mut();
    current
}

pub unsafe fn choose(
    item: *mut core::ffi::c_void,
    fallback: *mut core::ffi::c_void,
) -> *mut core::ffi::c_void {
    if item.is_null() { fallback } else { item }
}

pub unsafe fn store(
    stack: *mut *mut core::ffi::c_void,
    item: *mut core::ffi::c_void,
    flag: i32,
) -> i32 {
    *stack.offset(0) = item;
    flag
}

pub unsafe fn caller(
    item: *mut core::ffi::c_void,
    fallback: *mut core::ffi::c_void,
) -> i32 {
    let mut list: *mut core::ffi::c_void = item;
    store(&mut list, choose(pop(&mut list), fallback), 1)
}
"#,
        &[
            "pub unsafe fn pop(mut stack: &mut [*mut std::ffi::c_void])",
            "-> *mut std::ffi::c_void",
            "pub unsafe fn store(mut stack: &mut [*mut std::ffi::c_void],",
            "mut item: *mut std::ffi::c_void, flag: i32) -> i32",
            "std::slice::from_mut(&mut (list))",
        ],
        &[
            "pub unsafe fn pop(mut stack: *mut *mut core::ffi::c_void",
            "pub unsafe fn store(mut stack: *mut *mut core::ffi::c_void",
        ],
    );
}

#[test]
fn test_rewriter_same_call_scalar_output_and_copy_read_uses_temporary() {
    run_test(
        r#"
pub unsafe fn checked_add(mut out: *mut i32, old: i32, add: i32) -> i32 {
    *out.offset(0) = old + add;
    return 0;
}

pub unsafe fn caller() -> i32 {
    let mut len: i32 = 4;
    checked_add(&mut len, len, 1);
    return len;
}
"#,
        &[
            "pub unsafe fn checked_add(mut out: &mut [i32], old: i32, add: i32) -> i32",
            "let __crat_same_call_0_len = len;",
            "std::slice::from_mut(&mut (len))",
        ],
        &[
            "checked_add(std::slice::from_mut(&mut (len)), len, 1)",
            "pub unsafe fn checked_add(mut out: *mut i32",
        ],
    );
}

#[test]
fn test_rewriter_same_call_scalar_output_and_expression_read_uses_temporary() {
    run_test(
        r#"
pub unsafe fn checked_add(mut out: *mut i32, old: i32, add: i32) -> i32 {
    *out.offset(0) = old + add;
    return 0;
}

pub unsafe fn caller(delta: i32) -> i32 {
    let mut len: i32 = 4;
    checked_add(&mut len, len + delta, 1);
    return len;
}
"#,
        &[
            "pub unsafe fn checked_add(mut out: &mut [i32], old: i32, add: i32) -> i32",
            "let __crat_same_call_0_len = len;",
            "std::slice::from_mut(&mut (len))",
        ],
        &[
            "checked_add(std::slice::from_mut(&mut (len)), len + delta, 1)",
            "pub unsafe fn checked_add(mut out: *mut i32",
        ],
    );
}

#[test]
fn test_rewriter_same_call_pointer_output_and_copy_read_uses_temporary() {
    run_test(
        r#"
pub unsafe fn open_slot(
    mut out: *mut *mut core::ffi::c_void,
    current: *mut core::ffi::c_void,
    level: i32,
) -> i32 {
    *out.offset(0) = current;
    return level;
}

pub unsafe fn caller(mut config: *mut core::ffi::c_void, level: i32) -> i32 {
    open_slot(&mut config, config, level);
    return level;
}
"#,
        &[
            "pub unsafe fn open_slot(mut out: &mut [*mut std::ffi::c_void]",
            "let __crat_same_call_0_config = config;",
            "std::slice::from_mut(&mut (config))",
        ],
        &[
            "open_slot(std::slice::from_mut(&mut (config)), config, level)",
            "pub unsafe fn open_slot(mut out: *mut *mut core::ffi::c_void",
        ],
    );
}

#[test]
fn test_rewriter_same_call_pointer_output_and_slice_read_uses_temporary() {
    run_test(
        r#"
pub unsafe fn open_level(mut out: *mut *mut i32, values: *const i32, level: i32) -> i32 {
    *out.offset(0) = values as *mut i32;
    return *values.offset(level as isize);
}

pub unsafe fn caller(level: i32) -> i32 {
    let mut config: *mut i32 = core::ptr::null_mut();
    open_level(&mut config, config, level);
    return level;
}
"#,
        &[
            "pub unsafe fn open_level(mut out: &mut [*mut i32]",
            "values: *const i32",
            "let __crat_same_call_0_config = config;",
            "std::slice::from_mut(&mut (config))",
            "open_level(std::slice::from_mut(&mut (config)),\n            __crat_same_call_0_config, level)",
        ],
        &[
            "open_level(std::slice::from_mut(&mut (config)), config, level)",
            "std::slice::from_mut(&mut (config)),\n        if (config).is_null()",
            "values: crate::slice_cursor::SliceCursor<'_, i32>",
            "pub unsafe fn open_level(mut out: *mut *mut i32",
        ],
    );
}

#[test]
fn test_rewriter_same_call_multiple_outputs_and_later_copy_read_uses_temporary() {
    run_test(
        r#"
pub unsafe fn fill_offsets(
    mut base_out: *mut i64,
    mut aux_out: *mut i32,
    mut curpos_out: *mut i64,
    base: i64,
) -> i32 {
    *base_out.offset(0) = base + 1;
    *aux_out.offset(0) = 7;
    *curpos_out.offset(0) = base + 2;
    return 0;
}

pub unsafe fn caller() -> i64 {
    let mut base_offset: i64 = 10;
    let mut aux: i32 = 0;
    let mut curpos: i64 = 0;
    fill_offsets(&mut base_offset, &mut aux, &mut curpos, base_offset);
    return base_offset + curpos + aux as i64;
}
"#,
        &[
            "pub unsafe fn fill_offsets(mut base_out: &mut [i64]",
            "mut aux_out: &mut [i32]",
            "mut curpos_out: &mut [i64]",
            "let __crat_same_call_0_base_offset = base_offset;",
            "std::slice::from_mut(&mut (base_offset))",
            "std::slice::from_mut(&mut (curpos))",
        ],
        &[
            "std::slice::from_mut(&mut (curpos)),\n        base_offset)",
            "std::slice::from_mut(&mut (curpos)), base_offset)",
            "pub unsafe fn fill_offsets(mut base_out: *mut i64",
        ],
    );
}

#[test]
fn test_rewriter_same_call_signed_helper_output_and_copy_read_uses_temporary() {
    run_test(
        r#"
pub unsafe fn sub_int_overflow(mut out: *mut i32, old: i32, sub: i32) -> i32 {
    *out.offset(0) = old - sub;
    return 0;
}

pub unsafe fn caller(oldlines: i32) -> i32 {
    let mut old_lineno: i32 = 99;
    sub_int_overflow(&mut old_lineno, old_lineno, oldlines);
    return old_lineno;
}
"#,
        &[
            "pub unsafe fn sub_int_overflow(mut out: &mut [i32]",
            "let __crat_same_call_0_old_lineno = old_lineno;",
            "std::slice::from_mut(&mut (old_lineno))",
        ],
        &[
            "sub_int_overflow(std::slice::from_mut(&mut (old_lineno)), old_lineno",
            "pub unsafe fn sub_int_overflow(mut out: *mut i32",
        ],
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
            "let mut x: *mut crate::Node<'_> =",
            "let mut y: *mut crate::Node<'_> = std::ptr::null_mut();",
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
            "std::ptr::null_mut::<i32>()",
            "(_x).as_mut_ptr()",
            "} else { ((_x).as_mut_ptr()).add(1usize) }",
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
        &[
            "-> *mut i8",
            "return strdup(if (s).is_empty()",
            "std::ptr::null::<i8>()",
        ],
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
            "pub unsafe fn id_holder<'a, 'b>(h: &'a mut crate::Holder<'b>)",
            "-> &'a mut crate::Holder<'b>",
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
fn test_rewriter_keeps_array_like_owning_struct_field_raw_for_slice_call_arg() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe fn stash(owner: *mut Holder) {
    (*owner).p = malloc(std::mem::size_of::<i32>());
}

pub unsafe fn read(p: *mut i32) -> i32 {
    *p.offset(1)
}

pub unsafe fn drive(owner: *mut Holder) -> i32 {
    read((*owner).p)
}

pub unsafe fn release(owner: *mut Holder) {
    free((*owner).p as *mut core::ffi::c_void);
}
"#,
        &[
            "pub p: *mut i32",
            "pub unsafe fn read(p: &[i32]) -> i32",
            "std::slice::from_raw_parts",
            "free(owner.p as *mut core::ffi::c_void);",
        ],
        &["pub p: Option<Box<i32>>"],
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
fn test_rewriter_keeps_raw_field_copied_to_local_offset_alias_with_disjoint_root_update() {
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
            "pub struct Bs {",
            "pub buf: *const u8",
            "let mut p: *const u8 = (bs.buf).offset",
            "p = p.offset(1)",
        ],
        &[
            "crate::slice_cursor::SliceCursor",
            "std::slice::from_raw_parts(((bs.buf).offset",
        ],
    );
}

#[test]
fn test_rewriter_keeps_raw_field_copied_to_local_offset_alias_without_root_mutation() {
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
            "pub struct Bs {",
            "pub buf: *const u8",
            "let mut p: *const u8 = (bs.buf).offset",
            "p = p.offset(1)",
        ],
        &[
            "crate::slice_cursor::SliceCursor",
            "std::slice::from_raw_parts(((bs.buf).offset",
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
            ".into_deref().offset_by((-((s.count / 8) as",
        ],
        &[
            "}).as_mut_ptr()",
            "*(*s).words.offset",
            ".as_deref().offset_by",
        ],
    );
}

#[test]
fn test_rewriter_raw_pointer_numeric_cast_stays_raw() {
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
            "pub unsafe fn container_from_b(i: *const i32) -> *const crate::Pair",
            "((i as *const i8).offset(-(4 as isize))) as *const Pair",
        ],
        &[
            "crate::slice_cursor::SliceCursor",
            "bytemuck::cast_slice",
            "from_raw_parts((i).as_ptr()",
        ],
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
fn test_rewriter_preserves_generated_copy_after_mutable_slice_field_final_demotion() {
    run_typecheck_test_after_shape_check(
        r#"
#![feature(derive_clone_copy)]

#[repr(C)]
pub struct ConfigMap {
    pub value: i32,
}

#[repr(C)]
pub struct MapData {
    pub name: *const core::ffi::c_char,
    pub maps: *mut ConfigMap,
    pub map_count: usize,
    pub default_value: i32,
}

#[automatically_derived]
impl ::core::marker::Copy for MapData {}

#[automatically_derived]
impl ::core::clone::Clone for MapData {
    #[inline]
    fn clone(&self) -> MapData {
        let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_char>;
        let _: ::core::clone::AssertParamIsClone<*mut ConfigMap>;
        let _: ::core::clone::AssertParamIsClone<usize>;
        let _: ::core::clone::AssertParamIsClone<i32>;
        *self
    }
}

extern "C" {
    fn raw_touch(ptr: *mut core::ffi::c_void);
}

pub unsafe fn rewrite_maps(mut data: *mut MapData) -> i32 {
    raw_touch((*data).maps as *mut core::ffi::c_void);
    (*(*data).maps.offset(1)).value = 7;
    return (*(*data).maps.offset(1)).value + *(*data).name.offset(0) as i32;
}
"#,
        &[
            "pub struct MapData<'a>",
            "pub name: &'a [core::ffi::c_char]",
            "pub maps: *mut ConfigMap",
            "impl<'a> ::core::marker::Copy for MapData<'a>",
            "impl<'a> ::core::clone::Clone for MapData<'a>",
        ],
        &[
            "pub maps: &'a mut [ConfigMap]",
            "impl ::core::marker::Copy for MapData {}",
            "impl ::core::clone::Clone for MapData {",
        ],
    );
}

#[test]
fn test_rewriter_preserves_generated_copy_for_static_repeat_after_final_demotion() {
    run_test(
        r#"
#![feature(derive_clone_copy)]

#[repr(C)]
pub struct ConfigMap {
    pub value: i32,
}

#[repr(C)]
pub struct MapData {
    pub name: *const core::ffi::c_char,
    pub maps: *mut ConfigMap,
    pub map_count: usize,
    pub default_value: i32,
}

#[automatically_derived]
impl ::core::marker::Copy for MapData {}

#[automatically_derived]
impl ::core::clone::Clone for MapData {
    #[inline]
    fn clone(&self) -> MapData {
        let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_char>;
        let _: ::core::clone::AssertParamIsClone<*mut ConfigMap>;
        let _: ::core::clone::AssertParamIsClone<usize>;
        let _: ::core::clone::AssertParamIsClone<i32>;
        *self
    }
}

extern "C" {
    fn raw_touch(ptr: *mut core::ffi::c_void);
}

pub static mut DEFAULT_MAPS: [MapData; 15] = [MapData {
    name: b"default\0" as *const u8 as *const core::ffi::c_char,
    maps: 0 as *mut ConfigMap,
    map_count: 0,
    default_value: 0,
}; 15];

pub unsafe fn rewrite_maps(mut data: *mut MapData) -> i32 {
    raw_touch((*data).maps as *mut core::ffi::c_void);
    (*(*data).maps.offset(1)).value = 7;
    return (*(*data).maps.offset(1)).value
        + *(*data).name.offset(0) as i32
        + DEFAULT_MAPS[0].default_value;
}
"#,
        &[
            "pub struct MapData<'a>",
            "pub name: &'a [core::ffi::c_char]",
            "pub maps: *mut ConfigMap",
            "impl<'a> ::core::marker::Copy for MapData<'a>",
            "impl<'a> ::core::clone::Clone for MapData<'a>",
            "static mut DEFAULT_MAPS: [MapData<'_>; 15]",
        ],
        &[
            "pub maps: &'a mut [ConfigMap]",
            "impl ::core::marker::Copy for MapData {}",
            "impl ::core::clone::Clone for MapData {",
        ],
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
            "consume_c_string((*fields.offset(i)).name)",
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
            "pub struct Holder<'a, 'b>",
            "pub nodes: Option<&'a Vec<Node<'b>>>",
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
fn test_rewriter_local_slice_annotation_uses_in_scope_lifetime_for_promoted_adt() {
    run_test(
        r#"
#[repr(C)]
pub struct Node {
    pub value: *const i32,
}

pub unsafe fn promote_node(x: i32) -> i32 {
    let node = Node { value: &raw const x };
    *node.value
}

pub unsafe fn read_second(x: i32, y: i32) -> i32 {
    let nodes = [
        Node { value: &raw const x },
        Node { value: &raw const y },
    ];
    let mut p: *const Node = nodes.as_ptr();
    *(*p.offset(1)).value
}
"#,
        &["pub struct Node<'a>", "let mut p: &[crate::Node<'_>]"],
        &["let mut p: *const crate::Node"],
    );
}

#[test]
fn test_rewriter_local_raw_ptr_annotation_uses_in_scope_lifetime_for_promoted_adt() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Node {
    pub next: *mut Node,
    pub value: i32,
}

pub unsafe fn clear_local_list() {
    let mut x: *mut Node = malloc(std::mem::size_of::<Node>()) as *mut Node;
    (*x).next = std::ptr::null_mut();
    let mut y: *mut Node = std::ptr::null_mut();
    while !x.is_null() {
        y = (*x).next;
        free(x as *mut core::ffi::c_void);
        x = y;
    }
}
"#,
        &["pub struct Node<'a>", "let mut x: *mut crate::Node<'_>"],
        &["let mut x: &mut crate::Node"],
    );
}

#[test]
fn test_rewriter_local_raw_alloc_annotation_uses_in_scope_lifetime_for_nested_adt() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Node {
    pub value: *const i32,
}

#[repr(C)]
pub struct Wrapper {
    pub node: Node,
    pub tag: i32,
}

pub unsafe fn promote_node(x: i32) -> i32 {
    let node = Node {
        value: &raw const x,
    };
    *node.value
}

pub unsafe fn owned_nodes(x: i32) {
    let mut p: *mut Wrapper = malloc(2 * std::mem::size_of::<Wrapper>()) as *mut Wrapper;
    (*p.offset(1)).tag = x;
    free(p as *mut core::ffi::c_void);
}
"#,
        &["pub struct Node<'a>", "let mut p: *mut crate::Wrapper<'_>"],
        &["let mut p: &mut crate::Wrapper"],
    );
}

#[test]
fn test_rewriter_local_nullable_raw_alloc_annotation_uses_in_scope_lifetime_for_nested_adt() {
    run_test(
        r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Node {
    pub value: *const i32,
}

#[repr(C)]
pub struct Wrapper {
    pub node: Node,
    pub tag: i32,
}

pub unsafe fn promote_node(x: i32) -> i32 {
    let node = Node {
        value: &raw const x,
    };
    *node.value
}

pub unsafe fn maybe_owned_nodes(flag: bool, x: i32) {
    let mut p: *mut Wrapper = std::ptr::null_mut();
    if flag {
        p = malloc(2 * std::mem::size_of::<Wrapper>()) as *mut Wrapper;
        (*p.offset(1)).tag = x;
    }
    if !p.is_null() {
        free(p as *mut core::ffi::c_void);
    }
}
"#,
        &["pub struct Node<'a>", "let mut p: *mut crate::Wrapper<'_>"],
        &["let mut p: &mut crate::Wrapper"],
    );
}

#[test]
fn test_rewriter_local_cursor_annotation_uses_in_scope_lifetime_for_promoted_adt() {
    run_test(
        r#"
#[repr(C)]
pub struct Node {
    pub value: *const i32,
}

pub unsafe fn promote_node(x: i32) -> i32 {
    let node = Node { value: &raw const x };
    *node.value
}

pub unsafe fn read_around_cursor(x: i32, y: i32) -> i32 {
    let nodes = [
        Node { value: &raw const x },
        Node { value: &raw const y },
    ];
    let mut p: *const Node = nodes.as_ptr().offset(1);
    let first = *(*p.offset(-1)).value;
    p = p.offset(1);
    first + *(*p.offset(-1)).value
}
"#,
        &[
            "pub struct Node<'a>",
            "let mut p: crate::slice_cursor::SliceCursor<'_, crate::Node<'_>>",
        ],
        &["let mut p: *const crate::Node"],
    );
}

#[test]
fn test_rewriter_local_slice_annotation_uses_in_scope_lifetimes_for_multi_lifetime_adt() {
    run_test(
        r#"
#[repr(C)]
pub struct Pair {
    pub left: *const i32,
    pub right: *const i32,
}

pub unsafe fn promote_pair(x: i32, y: i32) -> i32 {
    let pair = Pair {
        left: &raw const x,
        right: &raw const y,
    };
    *pair.left + *pair.right
}

pub unsafe fn read_second_pair(a: i32, b: i32, c: i32, d: i32) -> i32 {
    let pairs = [
        Pair {
            left: &raw const a,
            right: &raw const b,
        },
        Pair {
            left: &raw const c,
            right: &raw const d,
        },
    ];
    let mut p: *const Pair = pairs.as_ptr();
    *(*p.offset(1)).left + *(*p.offset(1)).right
}
"#,
        &[
            "pub struct Pair<'a, 'b>",
            "let mut p: &[crate::Pair<'_, '_>]",
        ],
        &["let mut p: *const crate::Pair"],
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
            "std::ptr::null_mut::<std::ffi::c_void>()",
            "(_x).as_mut_ptr() as *mut std::ffi::c_void",
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
            "std::ptr::null_mut::<i8>()",
            "(_x).as_mut_ptr()",
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

#[test]
fn test_mut_c_char_21_slice_to_i32_bytemuck_cast_trims_slop() {
    let (s, bytemuck) = rewrite_with_config(
        r#"
pub unsafe extern "C" fn foo() -> i32 {
    let mut buf: [core::ffi::c_char; 21] = [0; 21];
    let mut p: *mut core::ffi::c_char = buf.as_mut_ptr();
    *p.offset(0 as isize) = 1 as core::ffi::c_char;
    *p.offset(20 as isize) = 2 as core::ffi::c_char;
    let mut q: *mut i32 = p as *mut i32;
    *q.offset(0 as isize) = 7;
    return *q.offset(4 as isize);
}
"#,
        &Config::default(),
    );
    assert_eq!(bytemuck, BytemuckDependency::Runtime);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("&mut [i8]"), "{s}");
    assert!(s.contains("&mut [i32]"), "{s}");
    assert_slop_prone_slice_cast_trims_byte_prefix(
        &s,
        "cast_slice_mut",
        "i32",
        &["(p)", "&mut (p)"],
    );
}

#[test]
fn test_shared_i8_slice_to_i32_bytemuck_cast_trims_slop() {
    let (s, bytemuck) = rewrite_with_config(
        r#"
pub unsafe extern "C" fn foo() -> i32 {
    let buf: [i8; 21] = [0; 21];
    let p: *const i8 = buf.as_ptr();
    let first = *p.offset(0 as isize) as i32;
    let q: *const i32 = p as *const i32;
    return first + *q.offset(4 as isize);
}
"#,
        &Config::default(),
    );
    assert_eq!(bytemuck, BytemuckDependency::Runtime);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("&[i8]"), "{s}");
    assert!(s.contains("&[i32]"), "{s}");
    assert_slop_prone_slice_cast_trims_byte_prefix(&s, "cast_slice", "i32", &["(p)", "&(p)"]);
}

#[test]
fn test_mut_i8_slice_to_i16_bytemuck_cast_trims_slop() {
    let (s, bytemuck) = rewrite_with_config(
        r#"
pub unsafe extern "C" fn foo() -> i16 {
    let mut buf: [i8; 5] = [0; 5];
    let mut p: *mut i8 = buf.as_mut_ptr();
    *p.offset(4 as isize) = 1;
    let mut q: *mut i16 = p as *mut i16;
    *q.offset(0 as isize) = 7;
    return *q.offset(1 as isize);
}
"#,
        &Config::default(),
    );
    assert_eq!(bytemuck, BytemuckDependency::Runtime);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("&mut [i8]"), "{s}");
    assert!(s.contains("&mut [i16]"), "{s}");
    assert_slop_prone_slice_cast_trims_byte_prefix(
        &s,
        "cast_slice_mut",
        "i16",
        &["(p)", "&mut (p)"],
    );
}

#[test]
fn test_mut_i16_slice_to_i32_bytemuck_cast_trims_slop() {
    let (s, bytemuck) = rewrite_with_config(
        r#"
pub unsafe extern "C" fn foo() -> i32 {
    let mut buf: [i16; 3] = [0; 3];
    let mut p: *mut i16 = buf.as_mut_ptr();
    *p.offset(2 as isize) = 1;
    let mut q: *mut i32 = p as *mut i32;
    *q.offset(0 as isize) = 7;
    return *q.offset(0 as isize);
}
"#,
        &Config::default(),
    );
    assert_eq!(bytemuck, BytemuckDependency::Runtime);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("&mut [i16]"), "{s}");
    assert!(s.contains("&mut [i32]"), "{s}");
    assert_slop_prone_slice_cast_trims_byte_prefix(
        &s,
        "cast_slice_mut",
        "i32",
        &["(p)", "&mut (p)"],
    );
}

#[test]
fn test_as_mut_ptr_i8_array_to_i32_slice_bytemuck_cast_trims_slop() {
    let (s, bytemuck) = rewrite_with_config(
        r#"
pub unsafe extern "C" fn foo() -> i32 {
    let mut buf: [i8; 21] = [0; 21];
    let mut q: *mut i32 = buf.as_mut_ptr() as *mut i32;
    *q.offset(0 as isize) = 7;
    return *q.offset(4 as isize);
}
"#,
        &Config::default(),
    );
    assert_eq!(bytemuck, BytemuckDependency::Runtime);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("&mut [i32]"), "{s}");
    assert_slop_prone_slice_cast_trims_byte_prefix(
        &s,
        "cast_slice_mut",
        "i32",
        &["&mut (buf)", "(&mut (buf))"],
    );
}

#[test]
fn test_raw_i8_pointer_to_i32_pointer_cast_stays_raw_without_bytemuck() {
    let (s, bytemuck) = rewrite_with_config(
        r#"
pub unsafe fn foo(p: *const i8) -> i32 {
    let q: *const i32 = (p as *const i32).offset(-(1 as isize));
    return *q.offset(1 as isize);
}
"#,
        &Config::default(),
    );
    assert_eq!(bytemuck, BytemuckDependency::None);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("pub unsafe fn foo(p: *const i8) -> i32"), "{s}");
    assert!(
        s.contains("let q: *const i32 = (p as *const i32).offset(-(1 as isize));"),
        "{s}"
    );
    assert!(!s.contains("crate::slice_cursor::SliceCursor"), "{s}");
    assert!(!s.contains("bytemuck::cast_slice"), "{s}");
    assert!(!s.contains("from_raw_parts"), "{s}");
}

#[test]
fn test_mut_i32_slice_to_i8_bytemuck_cast_stays_direct() {
    let (s, bytemuck) = rewrite_with_config(
        r#"
pub unsafe extern "C" fn foo() -> i8 {
    let mut buf: [i32; 5] = [0; 5];
    let mut p: *mut i32 = buf.as_mut_ptr();
    *p.offset(0 as isize) = 7;
    let mut q: *mut i8 = p as *mut i8;
    *q.offset(3 as isize) = 1;
    return *q.offset(7 as isize);
}
"#,
        &Config::default(),
    );
    assert_eq!(bytemuck, BytemuckDependency::Runtime);
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("&mut [i32]"), "{s}");
    assert!(s.contains("&mut [i8]"), "{s}");
    assert_direct_slice_cast_without_byte_prefix(&s, "cast_slice_mut", "i8");
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
        &[
            "std::ptr::null_mut::<i16>()",
            "(p).as_mut_ptr() as *mut i16",
            "&mut [i32]",
        ],
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
        &["from_raw_parts_mut", ::utils::FALLBACK_SLICE_LEN],
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
/// Output: `std::slice::from_raw_parts_mut(&raw mut (x) as *mut _, 1_000_000_000)`.
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
        &[
            "from_raw_parts_mut",
            ::utils::FALLBACK_SLICE_LEN,
            "&raw mut",
        ],
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

#[test]
fn test_unsized_projection_shared_slice_offset_to_raw_output_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Commit {
    pub header: u32,
    pub payload: u32,
}

pub unsafe fn shared_tail(mut commit: *const Commit, out: *mut *const core::ffi::c_char) {
    let _header = (*commit.offset(0)).header;
    *out.offset(0) =
        (commit as *const core::ffi::c_char).offset(core::mem::size_of::<Commit>() as isize);
}
"#,
        &[
            "mut commit: &[crate::Commit]",
            "mut out: &mut [*const i8]",
            "std::slice::from_raw_parts",
            "core::mem::size_of::<Commit>()",
            "as usize..",
            ".as_ptr()",
        ],
        &[],
    );
}

#[test]
fn test_unsized_projection_mut_slice_offset_returned_as_raw_pointer_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Commit {
    pub header: u32,
    pub payload: u32,
}

pub unsafe fn mut_tail(mut commit: *mut Commit) -> *mut core::ffi::c_char {
    (*commit.offset(0)).header = 1;
    (commit as *mut core::ffi::c_char).offset(core::mem::size_of::<Commit>() as isize)
}
"#,
        &[
            "mut commit: &mut [crate::Commit]",
            "std::slice::from_raw_parts_mut",
            "core::mem::size_of::<Commit>()",
            "as usize..",
            "_ptr()",
        ],
        &[],
    );
}

#[test]
fn test_unsized_projection_range_used_as_raw_function_argument_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Commit {
    pub header: u32,
    pub payload: u32,
}

extern "C" {
    fn consume_tail(ptr: *const core::ffi::c_char);
}

pub unsafe fn call_tail(mut commit: *const Commit) -> u32 {
    let header = (*commit.offset(0)).header;
    consume_tail((commit as *const core::ffi::c_char).offset(core::mem::size_of::<Commit>() as isize));
    header
}
"#,
        &[
            "mut commit: &[crate::Commit]",
            "std::slice::from_raw_parts",
            "core::mem::size_of::<Commit>()",
            "as usize..",
            ".as_ptr()",
        ],
        &[],
    );
}

#[test]
fn test_unsized_projection_range_returned_as_raw_pointer_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Commit {
    pub header: u32,
    pub payload: u32,
}

pub unsafe fn return_tail(mut commit: *const Commit) -> *const core::ffi::c_char {
    let _header = (*commit.offset(0)).header;
    (commit as *const core::ffi::c_char).offset(core::mem::size_of::<Commit>() as isize)
}
"#,
        &[
            "mut commit: &[crate::Commit]",
            "pub unsafe fn return_tail",
            "std::slice::from_raw_parts",
            "core::mem::size_of::<Commit>()",
            "as usize..",
            ".as_ptr()",
        ],
        &[],
    );
}

#[test]
fn test_unsized_projection_range_stored_in_raw_output_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Commit {
    pub header: u32,
    pub payload: u32,
}

pub unsafe fn store_tail(mut commit: *mut Commit, out: *mut *mut core::ffi::c_char) {
    (*commit.offset(0)).header = 1;
    *out.offset(0) =
        (commit as *mut core::ffi::c_char).offset(core::mem::size_of::<Commit>() as isize);
}
"#,
        &[
            "mut commit: &mut [crate::Commit]",
            "mut out: &mut [*mut i8]",
            "std::slice::from_raw_parts_mut",
            "core::mem::size_of::<Commit>()",
            "as usize..",
            ".as_mut_ptr()",
        ],
        &[],
    );
}

#[test]
fn test_unsized_projection_offset_from_projected_byte_slice_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Commit {
    pub header: u32,
    pub payload: u32,
}

pub unsafe fn projected_distance(mut commit: *const Commit) -> isize {
    let _header = (*commit.offset(0)).header;
    (commit as *const core::ffi::c_char)
        .offset(core::mem::size_of::<Commit>() as isize)
        .offset_from((commit as *const core::ffi::c_char).offset(core::mem::size_of::<u32>() as isize))
}
"#,
        &[
            "mut commit: &[crate::Commit]",
            "std::slice::from_raw_parts",
            "core::mem::size_of::<Commit>()",
            "core::mem::size_of::<u32>()",
            "as usize..",
            ".as_ptr()",
            ".offset_from",
        ],
        &[],
    );
}

#[test]
fn test_unsized_projection_cast_reslice_offset_to_raw_char_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Commit {
    pub header: u32,
    pub payload: u32,
}

extern "C" {
    fn consume_payload(ptr: *mut core::ffi::c_char);
}

pub unsafe fn commit_payload(mut commit: *mut Commit) {
    (*commit.offset(0)).header = 1;
    consume_payload((commit as *mut core::ffi::c_char).offset(core::mem::size_of::<Commit>() as isize));
}
"#,
        &[
            "mut commit: &mut [crate::Commit]",
            "std::slice::from_raw_parts_mut",
            "core::mem::size_of::<Commit>()",
            "as usize..",
            ".as_mut_ptr()",
        ],
        &[],
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

#[test]
fn test_empty_slice_raw_bridge_preserves_null() {
    run_test(
        r#"
pub unsafe extern "C" fn bar(mut p: *mut i32, mut q: *const i32) {
    if p.is_null() {
        return;
    }
    if q.is_null() {
        return;
    }
    *p.offset(1) = *q.offset(1);
}

pub unsafe extern "C" fn foo(mut p: *mut i32) {
    bar(p, p);
}

pub unsafe extern "C" fn main_0() -> i32 {
    let mut p: *mut i32 = 0 as *mut i32;
    foo(p);
    let mut arr: [i32; 10] = [0; 10];
    let mut q: *mut i32 = arr.as_mut_ptr();
    foo(q);
    return 0;
}
"#,
        &[
            "mut p: &mut [i32]",
            "bar(if (p).is_empty()",
            "std::ptr::null_mut::<i32>()",
            "std::ptr::null::<i32>()",
        ],
        &["bar((p).as_mut_ptr(), (p).as_ptr())"],
    );
}

#[test]
fn test_empty_slice_raw_bridge_wraps_chained_add_receiver() {
    run_test(
        r#"
extern "C" {
    fn sink(p: *const i8);
}

pub unsafe extern "C" fn publish(mut data: *const i8) -> i32 {
    if data.is_null() {
        return 0;
    }
    sink(data.add(1usize).add(2usize));
    return *data.offset(0) as i32;
}
"#,
        &[
            "mut data: &[i8]",
            "} else { (((data).as_ptr()).add(1usize)).add(2usize) }",
        ],
        &["}.add(2usize)"],
    );
}

#[test]
fn test_empty_slice_to_opt_ref_field_uses_first_mut() {
    run_test(
        r#"
#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
}

pub unsafe extern "C" fn store(mut p: *mut i32) -> i32 {
    let mut h = Holder { p: 0 as *mut i32 };
    *p.offset(0) = 1;
    h.p = p;
    if h.p.is_null() {
        return 0;
    }
    *h.p = 2;
    return *h.p;
}
"#,
        &["pub p: Option<&'a mut i32>", "h.p = (p).first_mut()"],
        &["as_mut_ptr().as_mut()", "as_ptr().as_ref()"],
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

#[test]
fn test_deref_if_slice_else_null() {
    run_test(
        r#"
use ::libc;

pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;

pub unsafe extern "C" fn foo(take_slot: bool) -> libc::c_int {
    let mut buf: [libc::c_int; 4] = [0; 4];
    let mut p: *mut libc::c_int = buf.as_mut_ptr();
    let mut size: usize = 0;
    *p.offset(1 as isize) = 11 as libc::c_int;
    *((if take_slot {
        let fresh = size;
        size = size.wrapping_add(1);
        &mut *p.offset(fresh as isize) as *mut libc::c_int as *mut core::ffi::c_void
    } else {
        NULL
    }) as *mut libc::c_int) = 7 as libc::c_int;
    return buf[0];
}
"#,
        &["panic!()", "[0]", "&mut [i32]"],
        &[],
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

#[test]
fn test_intptr_to_raw_c_void_arg_stays_raw() {
    run_test(
        r#"
pub type intptr_t = isize;

unsafe extern "C" fn compare_and_swap(
    ptr: *mut *mut core::ffi::c_void,
    oldval: *mut core::ffi::c_void,
    newval: *mut core::ffi::c_void,
) -> *mut core::ffi::c_void {
    let foundval: *mut core::ffi::c_void = *ptr;
    if foundval == oldval {
        *ptr = newval;
    }
    foundval
}

pub unsafe extern "C" fn foo(slot: *mut intptr_t, value: intptr_t) {
    let oldval: intptr_t = *slot;
    compare_and_swap(
        slot as *mut *mut core::ffi::c_void,
        oldval as *mut core::ffi::c_void,
        value as *mut core::ffi::c_void,
    );
}
"#,
        &["oldval as *mut", "value as *mut"],
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
        &["from_raw_parts", ::utils::FALLBACK_SLICE_LEN],
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

#[test]
fn test_bytestr_direct_deref_numeric_cast() {
    run_test(
        r#"
use ::libc;
pub unsafe extern "C" fn foo() -> libc::c_int {
    return *(b"alnum\x00" as *const u8 as *const libc::c_char) as libc::c_int;
}
"#,
        &["bytemuck::cast_slice::<_, i8>", ".first().unwrap()"],
        &["*const libc::c_char"],
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

// ===== Section 5: static byte-string initializers =====

#[test]
fn test_static_bytestr_slice_field_initializer_type_checks() {
    run_test(
        r#"
#[repr(C)]
pub struct InfoName {
    pub key: core::ffi::c_int,
    pub name: *const core::ffi::c_char,
}

static mut BUILDINFO_NAMES: [InfoName; 3] = [
    InfoName {
        key: 1 as core::ffi::c_int,
        name: b"cpu\x00" as *const u8 as *const core::ffi::c_char,
    },
    InfoName {
        key: 2 as core::ffi::c_int,
        name: b"built from commit\x00" as *const u8 as *const core::ffi::c_char,
    },
    InfoName {
        key: 0 as core::ffi::c_int,
        name: 0 as *const core::ffi::c_char,
    },
];

pub unsafe fn first_name_byte<'a>() -> core::ffi::c_int {
    let entry = BUILDINFO_NAMES.as_ptr();
    let name = (*entry).name;
    return *name.offset(0 as isize) as core::ffi::c_int;
}
"#,
        &[
            "name: bytemuck::must_cast_slice::<_, i8>(b\"cpu\\x00\")",
            "name: bytemuck::must_cast_slice::<_",
            "i8>(b\"built from commit\\x00\")",
        ],
        &[
            "name: bytemuck::cast_slice(b\"cpu\\x00\")",
            "name: bytemuck::cast_slice(b\"built from commit\\x00\")",
        ],
    );
}

#[test]
fn test_static_bytestr_multiple_slice_fields_type_check() {
    run_test(
        r#"
#[repr(C)]
pub struct DriverDefinition {
    pub name: *const core::ffi::c_char,
    pub fns: *const core::ffi::c_char,
    pub words: *const core::ffi::c_char,
    pub flags: core::ffi::c_int,
}

static mut BUILTIN_DEFS: [DriverDefinition; 2] = [
    DriverDefinition {
        name: b"ada\x00" as *const u8 as *const core::ffi::c_char,
        fns: b"!^(.*[ \t])?(is[ \t]+new|renames|is[ \t]+separate)([ \t].*)?$\x00"
            as *const u8 as *const core::ffi::c_char,
        words: b"[a-zA-Z][a-zA-Z0-9_]*|=>|\\.\\.|\\*\\*|:=|/=|>=|<=|[^[:space:]]\x00"
            as *const u8 as *const core::ffi::c_char,
        flags: 1 as core::ffi::c_int,
    },
    DriverDefinition {
        name: 0 as *const core::ffi::c_char,
        fns: 0 as *const core::ffi::c_char,
        words: 0 as *const core::ffi::c_char,
        flags: 0 as core::ffi::c_int,
    },
];

pub unsafe fn builtin_first_bytes<'a, 'b, 'c>() -> core::ffi::c_int {
    let def = BUILTIN_DEFS.as_ptr();
    let name = (*def).name;
    let fns = (*def).fns;
    let words = (*def).words;
    return *name.offset(0 as isize) as core::ffi::c_int
        + *fns.offset(0 as isize) as core::ffi::c_int
        + *words.offset(0 as isize) as core::ffi::c_int;
}
"#,
        &[
            "name: bytemuck::must_cast_slice::<_, i8>(b\"ada\\x00\")",
            "fns: bytemuck::must_cast_slice",
            "words: bytemuck::must_cast_slice",
        ],
        &[
            "name: bytemuck::cast_slice(b\"ada\\x00\")",
            "fns: bytemuck::cast_slice(",
            "words: bytemuck::cast_slice(",
        ],
    );
}

#[test]
fn test_dangerous_implicit_autoref_local_array_slice_field_null_check_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn raw_touch(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct SearchInfo {
    pub found: *const core::ffi::c_char,
    pub raw: *mut core::ffi::c_void,
    pub hits: i32,
}

pub unsafe fn scan_found(mut k: isize) -> i32 {
    let mut info_storage = [
        SearchInfo {
            found: b"hit\0" as *const u8 as *const core::ffi::c_char,
            raw: core::ptr::null_mut(),
            hits: 1,
        },
        SearchInfo {
            found: 0 as *const core::ffi::c_char,
            raw: core::ptr::null_mut(),
            hits: 0,
        },
    ];
    let mut info = info_storage.as_mut_ptr();
    let same = info == info_storage.as_mut_ptr();
    raw_touch((*info.offset(k)).raw);
    if (*info.offset(k)).found.is_null() {
        return 0;
    }
    return *(*info.offset(k)).found.offset(0) as i32 + same as i32;
}
"#,
        &[
            "pub struct SearchInfo<'a>",
            "pub found: &'a [core::ffi::c_char]",
        ],
        &["pub found: *const core::ffi::c_char"],
    );
}

#[test]
fn test_dangerous_implicit_autoref_local_array_nested_slice_field_null_check_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn raw_touch(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct InfoName {
    pub name: *const core::ffi::c_char,
}

impl Copy for InfoName {}

impl Clone for InfoName {
    fn clone(&self) -> InfoName {
        *self
    }
}

#[repr(C)]
pub struct SearchInfo {
    pub name: InfoName,
    pub raw: *mut core::ffi::c_void,
    pub hits: i32,
}

pub unsafe fn force_name_field(info: InfoName) -> i32 {
    if info.name.is_null() {
        return 0;
    }
    return *info.name.offset(0) as i32;
}

pub unsafe fn scan_name(mut k: isize) -> i32 {
    let mut info_storage = [
        SearchInfo {
            name: InfoName {
                name: b"entry\0" as *const u8 as *const core::ffi::c_char,
            },
            raw: core::ptr::null_mut(),
            hits: 1,
        },
        SearchInfo {
            name: InfoName {
                name: 0 as *const core::ffi::c_char,
            },
            raw: core::ptr::null_mut(),
            hits: 0,
        },
    ];
    let mut info = info_storage.as_mut_ptr();
    let same = info == info_storage.as_mut_ptr();
    raw_touch((*info.offset(k)).raw);
    if (*info.offset(k)).name.name.is_null() {
        return 0;
    }
    return force_name_field((*info.offset(k)).name) + same as i32;
}
"#,
        &[
            "pub struct InfoName<'a>",
            "pub name: &'a [core::ffi::c_char]",
            "pub unsafe fn force_name_field(info: InfoName<'_>) -> i32",
        ],
        &["pub name: *const core::ffi::c_char"],
    );
}

#[test]
fn test_dangerous_implicit_autoref_callback_slice_field_null_check_typechecks() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("write_callback".to_string());
    run_test_with_config(
        r#"
#[repr(C)]
pub struct WriteData {
    pub out: *mut u8,
    pub len: usize,
}

pub type WriteCallback = Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> i32>;

pub static mut WRITE_CALLBACK: WriteCallback = Some(
    write_callback as unsafe extern "C" fn(*mut core::ffi::c_void) -> i32,
);

pub unsafe extern "C" fn write_callback(payload: *mut core::ffi::c_void) -> i32 {
    let data = payload as *mut WriteData;
    let same = data == payload as *mut WriteData;
    if (*data).out.is_null() {
        return 0;
    }
    *(*data).out.offset(0) = 1;
    return (*data).len as i32 + same as i32;
}

pub unsafe fn drive_write(mut bytes: [u8; 4]) -> i32 {
    let mut data = WriteData {
        out: bytes.as_mut_ptr(),
        len: 4,
    };
    return WRITE_CALLBACK.unwrap()(&raw mut data as *mut core::ffi::c_void);
}
"#,
        &config,
        &["pub struct WriteData<'a>", "pub out: &'a mut [u8]"],
        &["pub out: *mut u8"],
    );
}

#[test]
fn test_dangerous_implicit_autoref_scalar_opt_ref_field_null_check_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct ScalarInfo {
    pub value: *const i32,
    pub tag: i32,
}

pub static VALUE: i32 = 7;

static mut SCALARS: [ScalarInfo; 2] = [
    ScalarInfo {
        value: &VALUE as *const i32,
        tag: 1,
    },
    ScalarInfo {
        value: 0 as *const i32,
        tag: 0,
    },
];

pub unsafe fn find_scalar() -> i32 {
    let mut entry = SCALARS.as_ptr();
    while !(*entry).value.is_null() {
        return *(*entry).value + (*entry).tag;
    }
    return 0;
}
"#,
        &["pub struct ScalarInfo<'a>", "pub value: Option<&'a i32>"],
        &["pub value: *const i32"],
    );
}

#[test]
fn test_dangerous_implicit_autoref_static_slice_field_raw_bridge_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn raw_take(ptr: *const core::ffi::c_char);
}

#[repr(C)]
pub struct BridgeEntry {
    pub name: *const core::ffi::c_char,
    pub value: i32,
}

static mut BRIDGES: [BridgeEntry; 2] = [
    BridgeEntry {
        name: b"one\0" as *const u8 as *const core::ffi::c_char,
        value: 1,
    },
    BridgeEntry {
        name: 0 as *const core::ffi::c_char,
        value: 0,
    },
];

pub unsafe fn pass_static_raw_bridge() -> i32 {
    let mut entry = BRIDGES.as_ptr();
    if (*entry).name.is_null() {
        return 0;
    }
    if *(*entry).name.offset(0) == b'o' as core::ffi::c_char {
        raw_take((*entry).name);
    }
    return (*entry).value;
}
"#,
        &[
            "pub struct BridgeEntry<'a>",
            "pub name: &'a [core::ffi::c_char]",
            "std::ptr::null::<i8>()",
            "(&((*entry).name)).as_ptr()",
        ],
        &["pub name: *const core::ffi::c_char"],
    );
}

#[test]
fn test_dangerous_implicit_autoref_static_mut_table_slice_field_null_check_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct TableEntry {
    pub name: *const core::ffi::c_char,
    pub value: i32,
}

static mut TABLE: [TableEntry; 2] = [
    TableEntry {
        name: b"one\0" as *const u8 as *const core::ffi::c_char,
        value: 1,
    },
    TableEntry {
        name: 0 as *const core::ffi::c_char,
        value: 0,
    },
];

pub unsafe fn find_mut_table() -> i32 {
    let mut entry = TABLE.as_mut_ptr();
    while !(*entry).name.is_null() {
        if *(*entry).name.offset(0) == b'o' as core::ffi::c_char {
            return (*entry).value;
        }
        entry = entry.offset(1);
    }
    return 0;
}
"#,
        &[
            "pub struct TableEntry<'a>",
            "pub name: &'a [core::ffi::c_char]",
        ],
        &["pub name: *const core::ffi::c_char"],
    );
}

#[test]
fn test_dangerous_implicit_autoref_static_const_table_slice_field_null_check_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct TableEntry {
    pub name: *const core::ffi::c_char,
    pub value: i32,
}

static mut TABLE: [TableEntry; 2] = [
    TableEntry {
        name: b"one\0" as *const u8 as *const core::ffi::c_char,
        value: 1,
    },
    TableEntry {
        name: 0 as *const core::ffi::c_char,
        value: 0,
    },
];

pub unsafe fn find_const_table() -> i32 {
    let mut entry = TABLE.as_ptr();
    while !(*entry).name.is_null() {
        if *(*entry).name.offset(0) == b'o' as core::ffi::c_char {
            return (*entry).value;
        }
        entry = entry.offset(1);
    }
    return 0;
}
"#,
        &[
            "pub struct TableEntry<'a>",
            "pub name: &'a [core::ffi::c_char]",
        ],
        &["pub name: *const core::ffi::c_char"],
    );
}

#[test]
fn test_dangerous_implicit_autoref_static_nested_slice_field_null_check_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct InfoName {
    pub name: *const core::ffi::c_char,
}

impl Copy for InfoName {}

impl Clone for InfoName {
    fn clone(&self) -> InfoName {
        *self
    }
}

#[repr(C)]
pub struct TableEntry {
    pub nested: InfoName,
    pub value: i32,
}

pub unsafe fn force_name_field(info: InfoName) -> i32 {
    if info.name.is_null() {
        return 0;
    }
    return *info.name.offset(0) as i32;
}

static mut TABLE: [TableEntry; 2] = [
    TableEntry {
        nested: InfoName {
            name: b"one\0" as *const u8 as *const core::ffi::c_char,
        },
        value: 1,
    },
    TableEntry {
        nested: InfoName {
            name: 0 as *const core::ffi::c_char,
        },
        value: 0,
    },
];

pub unsafe fn find_nested_table() -> i32 {
    let mut entry = TABLE.as_ptr();
    while !(*entry).nested.name.is_null() {
        if force_name_field((*entry).nested) == b'o' as core::ffi::c_char as i32 {
            return (*entry).value;
        }
        entry = entry.offset(1);
    }
    return 0;
}
"#,
        &[
            "pub struct InfoName<'a>",
            "pub name: &'a [core::ffi::c_char]",
        ],
        &["pub name: *const core::ffi::c_char"],
    );
}

#[test]
fn test_dangerous_implicit_autoref_static_cursor_field_null_check_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct CursorEntry {
    pub cursor: *const i32,
    pub value: i32,
}

pub static VALUES: [i32; 3] = [10, 20, 30];

static mut CURSORS: [CursorEntry; 2] = [
    CursorEntry {
        cursor: VALUES.as_ptr(),
        value: 1,
    },
    CursorEntry {
        cursor: 0 as *const i32,
        value: 0,
    },
];

pub unsafe fn find_cursor_table() -> i32 {
    let mut entry = CURSORS.as_ptr();
    while !(*entry).cursor.is_null() {
        return *(*entry).cursor.offset(-1) + (*entry).value;
    }
    return 0;
}
"#,
        &[
            "pub struct CursorEntry<'a>",
            "pub cursor: crate::slice_cursor::SliceCursor<'a, i32>",
        ],
        &["pub cursor: *const i32"],
    );
}

#[test]
fn test_root1_static_mut_shared_array_field_as_ptr_cursor_initializer_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct StaticCursorDesc {
    pub data: *const i32,
    pub index: isize,
}

pub static VALUES: [i32; 4] = [10, 20, 30, 40];

pub static mut SHARED_DESC: StaticCursorDesc = StaticCursorDesc {
    data: VALUES.as_ptr(),
    index: 2,
};

pub unsafe fn read_shared_desc() -> i32 {
    return *SHARED_DESC.data.offset(SHARED_DESC.index);
}
"#,
        &[
            "pub struct StaticCursorDesc<'a>",
            "pub data: crate::slice_cursor::SliceCursor<'a, i32>",
            "static mut SHARED_DESC: StaticCursorDesc",
        ],
        &["pub data: *const i32"],
    );
}

#[test]
fn test_root1_static_null_field_empty_cursor_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct CursorEntry {
    pub data: *const i32,
    pub index: isize,
}

pub static WORDS: [i32; 3] = [3, 5, 8];

pub static mut WORD_DESC: CursorEntry = CursorEntry {
    data: WORDS.as_ptr(),
    index: 1,
};

pub static mut EMPTY_DESC: CursorEntry = CursorEntry {
    data: core::ptr::null(),
    index: 0,
};

pub unsafe fn read_descriptor() -> i32 {
    return *WORD_DESC.data.offset(WORD_DESC.index) + EMPTY_DESC.index as i32;
}
"#,
        &[
            "pub struct CursorEntry<'a>",
            "pub data: crate::slice_cursor::SliceCursor<'a, i32>",
            "static mut WORD_DESC: CursorEntry",
            "static mut EMPTY_DESC: CursorEntry",
            "data: crate::slice_cursor::SliceCursor::empty()",
        ],
        &["pub data: *const i32"],
    );
}

#[test]
fn test_root1_static_multiple_cursor_fields_distinct_lifetimes_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct MultiCursorDesc {
    pub codes: *const i16,
    pub weights: *const i32,
    pub code_index: isize,
    pub weight_index: isize,
}

pub static CODES: [i16; 4] = [1, 1, 2, 3];
pub static WEIGHTS: [i32; 4] = [5, 8, 13, 21];

pub static mut MULTI_DESC: MultiCursorDesc = MultiCursorDesc {
    codes: CODES.as_ptr(),
    weights: WEIGHTS.as_ptr(),
    code_index: 2,
    weight_index: 3,
};

pub unsafe fn read_multi_desc() -> i32 {
    return *MULTI_DESC.codes.offset(MULTI_DESC.code_index) as i32
        + *MULTI_DESC.weights.offset(MULTI_DESC.weight_index);
}
"#,
        &[
            "pub struct MultiCursorDesc<'a, 'b>",
            "pub codes: crate::slice_cursor::SliceCursor<'a, i16>",
            "pub weights: crate::slice_cursor::SliceCursor<'b, i32>",
            "static mut MULTI_DESC: MultiCursorDesc",
        ],
        &["pub codes: *const i16", "pub weights: *const i32"],
    );
}

#[test]
fn test_root1_nested_alias_static_descriptor_cursor_initializers_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct StaticTreeDesc {
    pub static_tree: *const i32,
    pub extra_bits: *const i16,
}

pub type StaticTreeDescAlias = StaticTreeDesc;

#[repr(C)]
pub struct TreeDesc {
    pub stat_desc: *const StaticTreeDescAlias,
}

pub static TREE_VALUES: [i32; 4] = [4, 6, 8, 10];
pub static EXTRA_VALUES: [i16; 2] = [1, 2];

pub static mut STATIC_TREE_DESC: StaticTreeDescAlias = StaticTreeDesc {
    static_tree: TREE_VALUES.as_ptr(),
    extra_bits: EXTRA_VALUES.as_ptr(),
};

pub unsafe fn read_nested_tree(idx: isize) -> i32 {
    let desc = TreeDesc {
        stat_desc: &raw const STATIC_TREE_DESC as *const StaticTreeDescAlias,
    };
    let stat = desc.stat_desc;
    return *(*stat).static_tree.offset(idx)
        + *(*stat).extra_bits.offset(0) as i32;
}
"#,
        &[
            "pub struct StaticTreeDesc<'a, 'b>",
            "pub static_tree: crate::slice_cursor::SliceCursor<'a, i32>",
            "pub extra_bits: &'b [i16]",
            "pub type StaticTreeDescAlias<'a, 'b>",
            "static mut STATIC_TREE_DESC: StaticTreeDescAlias",
            "pub struct TreeDesc<'a, 'b, 'c>",
        ],
        &[
            "pub static_tree: *const i32",
            "pub extra_bits: *const i16",
            "pub type StaticTreeDescAlias = StaticTreeDesc",
        ],
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

// ===== slice_from_raw method-call tests =====

/// `q = p.offset(2)` where p is Raw, q is Slice uses the normal null-checked raw bridge.
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
        &["from_raw_parts_mut", "p.offset", "is_null"],
        &["let _x"],
    );
}

/// `q = p.offset(2) as *mut c_short` keeps the cast inside the normal null-checked raw bridge.
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
        &["from_raw_parts_mut", "as *mut _", "is_null"],
        &["let _x"],
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

#[test]
fn test_raw_constructor_type_anchor_mut_slice_if_c_void_null_const_branch() {
    run_test(
        r#"
pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;

pub unsafe extern "C" fn write_slot(use_data: bool, idx: usize) -> i64 {
    let mut data: [i64; 4] = [0; 4];
    let ptr: *mut i64 = (if use_data {
        data.as_mut_ptr() as *mut core::ffi::c_void
    } else {
        NULL
    }) as *mut i64;
    *ptr.offset(idx as isize) = 13;
    return data[idx];
}
"#,
        &["from_raw_parts_mut", "as *mut", "&mut [i64]"],
        &["from_raw_parts_mut((NULL),"],
    );
}

#[test]
fn test_raw_constructor_type_anchor_shared_slice_if_c_void_null_const_branch() {
    run_test(
        r#"
pub const NULL: *const core::ffi::c_void = 0 as *const core::ffi::c_void;

pub unsafe extern "C" fn read_slot(use_data: bool, idx: usize) -> i32 {
    let data: [i32; 4] = [1, 2, 3, 4];
    let ptr: *const i32 = (if use_data {
        data.as_ptr() as *const core::ffi::c_void
    } else {
        NULL
    }) as *const i32;
    return *ptr.offset(idx as isize);
}
"#,
        &["from_raw_parts", "as *const", "&[i32]"],
        &["from_raw_parts((NULL),"],
    );
}

#[test]
fn test_raw_constructor_type_anchor_mut_cursor_if_git_malloc_null_const_branch() {
    run_test(
        r#"
extern "C" {
    fn git__malloc(size: usize) -> *mut core::ffi::c_void;
}

pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;

pub unsafe extern "C" fn write_before(use_alloc: bool) -> i64 {
    let ptr: *mut i64 = (if use_alloc {
        git__malloc(64)
    } else {
        NULL
    }) as *mut i64;
    *ptr.offset(-1) = 7;
    *ptr.offset(0) = 11;
    return *ptr.offset(0);
}
"#,
        &["let mut ptr: *mut i64", "*ptr.offset(-1)", "*ptr.offset(0)"],
        &[
            "SliceCursorMut::from_raw_parts_mut",
            "crate::slice_cursor::SliceCursorMut<'_, i64>",
        ],
    );
}

#[test]
fn test_raw_constructor_type_anchor_shared_cursor_if_callback_null_const_branch() {
    run_test(
        r#"
extern "C" {
    fn object_data(id: i32) -> *const core::ffi::c_void;
}

pub const NULL: *const core::ffi::c_void = 0 as *const core::ffi::c_void;

pub unsafe extern "C" fn read_before(use_callback: bool) -> i64 {
    let ptr: *const i64 = (if use_callback {
        object_data(1)
    } else {
        NULL
    }) as *const i64;
    return *ptr.offset(-1) + *ptr.offset(0);
}
"#,
        &["let ptr: *const i64", "*ptr.offset(-1)", "*ptr.offset(0)"],
        &[
            "SliceCursor::from_raw_parts",
            "crate::slice_cursor::SliceCursor<'_, i64>",
        ],
    );
}

#[test]
fn test_raw_constructor_type_anchor_mut_slice_if_null_0_const_branch() {
    run_test(
        r#"
#[repr(C)]
pub struct GitDiffLine {
    pub origin: i32,
}

pub const NULL_0: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;

pub unsafe extern "C" fn line_origin(use_lines: bool, idx: usize) -> i32 {
    let mut lines: [GitDiffLine; 2] = [
        GitDiffLine { origin: 1 },
        GitDiffLine { origin: 2 },
    ];
    let ptr: *mut GitDiffLine = (if use_lines {
        lines.as_mut_ptr() as *mut core::ffi::c_void
    } else {
        NULL_0
    }) as *mut GitDiffLine;
    (*ptr.offset(idx as isize)).origin = 9;
    return lines[idx].origin;
}
"#,
        &["from_raw_parts_mut", "as *mut", "&mut [crate::GitDiffLine]"],
        &["from_raw_parts_mut((NULL_0),"],
    );
}

#[test]
fn test_raw_constructor_type_anchor_mut_slice_if_direct_null_mut_branch() {
    run_test(
        r#"
extern "C" {
    fn raw_words() -> *mut core::ffi::c_void;
}

pub unsafe extern "C" fn write_direct_null(use_data: bool, idx: usize) -> i16 {
    let ptr: *mut i16 = (if use_data {
        raw_words()
    } else {
        std::ptr::null_mut::<core::ffi::c_void>()
    }) as *mut i16;
    *ptr.offset(idx as isize) = 5;
    return *ptr.offset(0);
}
"#,
        &["let _x", "from_raw_parts_mut", "as *mut", "&mut [i16]"],
        &[
            "from_raw_parts_mut(_x,",
            "from_raw_parts_mut((std::ptr::null_mut",
        ],
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
            "as *mut u8",
            ::utils::FALLBACK_SLICE_LEN,
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
            "as *mut u8",
            ::utils::FALLBACK_SLICE_LEN,
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
        &[
            "pub arch: *mut i8",
            "std::ptr::null::<i8>()",
            "strdup(if (s).is_empty()",
        ],
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
fn test_raw_origin_param_assigned_to_cursor_like_local_stays_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
pub unsafe fn raw_param_assigned_to_cursor_like_local(p: *const core::ffi::c_void) -> i32 {
    let mut q: *const i32 = p as *const i32;
    let before = *q.offset(-1);
    q = q.offset(1);
    before + *q
}
"#,
        &[
            "pub unsafe fn raw_param_assigned_to_cursor_like_local",
            "*const std::ffi::c_void",
            "let mut q: *const i32 = p as *const i32;",
        ],
        &[],
    );
}

#[test]
fn test_raw_origin_param_offset_add_sub_chain_before_negative_index_stays_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
pub unsafe fn raw_param_offset_add_sub_chain_before_negative_index(
    p: *const core::ffi::c_void,
    n: usize,
    m: isize,
) -> u8 {
    let q: *const u8 = (p as *const u8).add(n).offset(m).sub(1);
    *q.offset(-1)
}
"#,
        &["*const std::ffi::c_void", "let q: *const u8"],
        &[],
    );
}

#[test]
fn test_raw_origin_returning_functions_assigned_to_cursor_like_locals_stay_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
extern "C" {
    fn foreign_raw() -> *const i32;
}

pub unsafe fn local_raw(p: *mut i32) -> *mut i32 {
    p
}

pub unsafe fn raw_returning_functions_assigned_to_cursor_like_locals(p: *mut i32) -> i32 {
    let q = foreign_raw().offset(1);
    let r = local_raw(p).offset(1);
    *r.offset(-1) = *q.offset(-1);
    *r
}
"#,
        &["foreign_raw", "-> *const i32", "local_raw", "-> *mut i32"],
        &[
            "from_raw_parts((foreign_raw())",
            "from_raw_parts_mut((local_raw(",
        ],
    );
}

#[test]
fn test_raw_origin_function_return_converted_to_cursor_output_stays_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
pub unsafe fn raw_function_return_converted_to_cursor_output(
    p: *mut core::ffi::c_void,
    n: isize,
) -> *mut u8 {
    let q: *mut u8 = (p as *mut u8).offset(n);
    q.offset(-1)
}

pub unsafe fn raw_function_return_converted_to_cursor_output_driver(
    p: *mut core::ffi::c_void,
    n: isize,
    value: u8,
) -> u8 {
    let q = raw_function_return_converted_to_cursor_output(p, n);
    *q = value;
    *q
}
"#,
        &[
            "pub unsafe fn raw_function_return_converted_to_cursor_output(",
            "-> *mut u8",
            "let mut q: *mut u8",
        ],
        &["from_raw_parts_mut((p) as"],
    );
}

#[test]
fn test_raw_origin_struct_field_direct_and_offset_sources_stay_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
#[repr(C)]
pub struct RawFieldHolder {
    pub data: *const i32,
}

pub unsafe fn raw_struct_field_direct_and_offset_sources(
    h: RawFieldHolder,
    n: isize,
) -> i32 {
    let direct = h.data;
    let shifted = h.data.offset(n);
    *direct.offset(-1) + *shifted.offset(-1)
}
"#,
        &[
            "pub struct RawFieldHolder {",
            "pub data: *const i32",
            "let direct: *const i32",
            "let shifted: *const i32",
        ],
        &[],
    );
}

#[test]
fn test_raw_origin_tuple_destructured_pointer_source_stays_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
pub unsafe fn raw_tuple_source(p: *const i32) -> (*const i32, i32) {
    (p, 7)
}

pub unsafe fn raw_tuple_destructured_pointer_source(p: *const i32) -> i32 {
    let (q, tag) = raw_tuple_source(p);
    *q.offset(-1) + tag
}
"#,
        &["-> (*const i32, i32)", "let (q, tag)"],
        &[],
    );
}

#[test]
fn test_raw_origin_call_argument_to_cursor_candidate_callee_stays_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
pub unsafe fn raw_cursor_candidate_callee(p: *const i32) -> i32 {
    *p.offset(-1)
}

pub unsafe fn raw_call_argument_to_cursor_candidate_callee(p: *const i32) -> i32 {
    let q = p.offset(1);
    raw_cursor_candidate_callee(q)
}
"#,
        &[
            "pub unsafe fn raw_cursor_candidate_callee(p: *const i32)",
            "let q: *const i32",
        ],
        &[],
    );
}

#[test]
fn test_array_and_slice_pointer_sources_can_still_form_cursors() {
    run_typecheck_test_after_shape_check(
        r#"
pub unsafe fn slice_as_ptr_source_can_form_cursor() -> u8 {
    let buf = [1u8, 2, 3, 4];
    let q = (&buf[..]).as_ptr().add(2);
    *q.offset(-1)
}

pub unsafe fn slice_as_mut_ptr_source_can_form_cursor() -> u8 {
    let mut buf = [1u8, 2, 3, 4];
    let r = (&mut buf[..]).as_mut_ptr().add(2);
    *r.offset(-1) = 9;
    *r.offset(-1)
}
"#,
        &[
            "let q: crate::slice_cursor::SliceCursor<'_, u8>",
            "let mut r: crate::slice_cursor::SliceCursorMut<'_, u8>",
        ],
        &["let q: *const u8", "let r: *mut u8"],
    );
}

#[test]
fn test_mixed_raw_and_anchored_assignments_converge_to_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
pub unsafe fn mixed_raw_and_anchored_assignments(use_raw: bool, raw: *const u8) -> u8 {
    let buf = [1u8, 2, 3, 4];
    let mut p: *const u8 = buf.as_ptr().add(1);
    if use_raw {
        p = raw;
    }
    *p.offset(-1)
}
"#,
        &[
            "pub unsafe fn mixed_raw_and_anchored_assignments",
            "let mut p: *const u8",
            "*p.offset(-1)",
        ],
        &[],
    );
}

#[test]
fn test_recursive_raw_param_source_stays_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
pub unsafe fn recursive_raw_param_source(p: *const i32, n: i32) -> i32 {
    if n == 0 {
        return *p.offset(-1);
    }
    recursive_raw_param_source(p.offset(1), n - 1)
}
"#,
        &[
            "pub unsafe fn recursive_raw_param_source(p: *const i32, n: i32) -> i32",
            "*p.offset(-1)",
            "recursive_raw_param_source(p.offset(1), n - 1)",
        ],
        &[],
    );
}

#[test]
fn test_reordered_struct_destructure_preserves_field_provenance() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct Pair {
    pub anchored: *const u8,
    pub raw: *const u8,
}

pub unsafe fn reordered_struct_destructure_preserves_field_provenance(raw: *const u8) -> u8 {
    let buf = [1u8, 2, 3, 4];
    let pair = Pair {
        anchored: buf.as_ptr().add(1),
        raw,
    };
    let Pair { raw: q, anchored: p } = pair;
    *q.offset(-1) + *p.offset(-1)
}
"#,
        &[
            "reordered_struct_destructure_preserves_field_provenance",
            "*q.offset(-1)",
            "crate::slice_cursor::SliceCursor",
        ],
        &["std::slice::from_raw_parts((q)"],
    );
}

#[test]
fn test_anchored_aggregate_return_sources_stay_raw_without_aggregate_output_rewrite() {
    run_typecheck_test_after_shape_check(
        r#"
pub unsafe fn anchored_tuple_sources(buf: &[u8]) -> (*const u8, *const u8) {
    (buf.as_ptr().add(1), buf.as_ptr().add(2))
}

pub unsafe fn anchored_aggregate_return_sources_can_still_form_cursors(buf: &[u8]) -> u8 {
    let (p, q) = anchored_tuple_sources(buf);
    *p.offset(-1) + *q.offset(-1)
}
"#,
        &[
            "anchored_aggregate_return_sources_can_still_form_cursors",
            "pub unsafe fn anchored_tuple_sources(buf: &[u8]) -> (*const u8, *const u8)",
            "let (p, q)",
            "*p.offset(-1) + *q.offset(-1)",
        ],
        &["crate::slice_cursor::SliceCursor", "from_raw_parts"],
    );
}

#[test]
fn test_raw_origin_param_type_changing_cast_chain_stays_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
#[repr(C)]
pub struct Header {
    pub value: u32,
}

pub unsafe fn read_header(
    s: *mut core::ffi::c_void,
    byte_off: isize,
    header_off: isize,
) -> u32 {
    let mut p: *mut Header =
        ((s as *mut u8).offset(byte_off) as *mut Header).offset(header_off);
    let before = (*p.offset(-1)).value;
    p = p.offset(1);
    before + (*p).value
}
"#,
        &[
            "pub unsafe fn read_header(",
            "*mut std::ffi::c_void",
            "let mut p: *mut crate::Header",
        ],
        &[],
    );
}

#[test]
fn test_raw_origin_function_return_type_preserving_mut_cast_stays_raw() {
    run_raw_origin_cursor_rejection_test(
        r#"
extern "C" {
    fn get() -> *const u8;
}

pub unsafe fn write_from_get(n: isize, value: u8) -> u8 {
    let mut p: *mut u8 = (get() as *mut u8).offset(n);
    *p.offset(-1) = value;
    *p
}
"#,
        &["fn get()", "-> *const u8", "let mut p: *mut u8"],
        &["from_raw_parts_mut(((get())"],
    );
}

#[test]
fn test_raw_param_multi_offset_deref_stays_raw() {
    run_test(
        r#"
pub unsafe fn write_offset(p: *mut i32, a: isize, b: isize) {
    *p.offset(a).offset(b) = 1;
}
"#,
        &[
            "pub unsafe fn write_offset(mut p: *mut i32, a: isize, b: isize)",
            "*p.offset(a).offset(b) = 1",
        ],
        &[
            "crate::slice_cursor::SliceCursor",
            "(p).as_deref_mut().offset_by",
        ],
    );
}

#[test]
fn test_raw_param_recursive_multi_offset_call_stays_raw() {
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
        &[
            "pub unsafe fn recurse(mut items: *mut i32, a: isize, b: isize)",
            "recurse(items.offset(a).offset(b), a, b - 1)",
            "*items = b as i32",
        ],
        &["crate::slice_cursor::SliceCursor", "from_raw_parts"],
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
fn test_libgit2_pointer_rewrite_shared_slice_field_offset_from_argument_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct Entry {
    pub ptr: *const u8,
}

pub unsafe fn read_entry(entry: *const Entry) -> u8 {
    *(*entry).ptr.offset(1)
}

pub unsafe fn distance_from_field_argument(entry: *const Entry, current: *const u8) -> isize {
    current.offset_from((*entry).ptr)
}
"#,
        &["pub struct Entry<'a>", "pub ptr: &'a [u8]"],
        &["pub ptr: *const u8"],
    );
}

#[test]
fn test_libgit2_pointer_rewrite_shared_slice_field_offset_from_receiver_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct Entry {
    pub ptr: *const u8,
}

pub unsafe fn read_second(ptr: *const u8) -> u8 {
    *ptr.offset(1)
}

pub unsafe fn distance_from_field_receiver(buf: [u8; 8], pos: usize) -> isize {
    let entry = Entry { ptr: buf.as_ptr() };
    read_second(entry.ptr) as isize + entry.ptr.add(pos).offset_from(buf.as_ptr())
}
"#,
        &["pub struct Entry<'a>", "pub ptr: &'a [u8]"],
        &["pub ptr: *const u8"],
    );
}

#[test]
fn test_libgit2_pointer_rewrite_shared_slice_field_mut_raw_bridge_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn raw_consume(ptr: *mut u8) -> i32;
}

#[repr(C)]
pub struct Entry {
    pub ptr: *const u8,
}

pub unsafe fn read_second(ptr: *const u8) -> u8 {
    *ptr.offset(1)
}

pub unsafe fn call_raw_bridge(buf: [u8; 8]) -> i32 {
    let entry = Entry { ptr: buf.as_ptr() };
    read_second(entry.ptr) as i32 + raw_consume(entry.ptr as *mut u8)
}
"#,
        &["pub struct Entry<'a>", "pub ptr: &'a [u8]"],
        &["pub ptr: *const u8"],
    );
}

#[test]
fn test_libgit2_pointer_rewrite_const_outer_field_address_cast_to_mut_raw_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct Field {
    pub value: i32,
}

#[repr(C)]
pub struct Outer {
    pub field: Field,
    pub tag: i32,
}

extern "C" {
    fn raw_field(field: *mut Field) -> i32;
}

pub unsafe fn call_raw_field(outer: *const Outer) -> i32 {
    raw_field(&raw const (*outer).field as *const Field as *mut Field)
}
"#,
        &["pub unsafe fn call_raw_field(outer: &crate::Outer)"],
        &["pub unsafe fn call_raw_field(outer: *const crate::Outer)"],
    );
}

#[test]
fn test_libgit2_pointer_rewrite_mutable_slice_field_raw_bridge_still_uses_mutable_reference() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn write_raw(ptr: *mut u8);
}

#[repr(C)]
pub struct Entry {
    pub ptr: *mut u8,
}

pub unsafe fn call_mut_raw_bridge(mut buf: [u8; 8]) -> u8 {
    let entry = Entry {
        ptr: buf.as_mut_ptr(),
    };
    write_raw(entry.ptr);
    *entry.ptr.offset(0)
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub ptr: &'a mut [u8]",
            ".as_mut_ptr()",
        ],
        &["pub ptr: *mut u8"],
    );
}

#[test]
fn test_field_raw_bridge_pointee_cast_shared_c_char_slice_to_const_c_void() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn raw_read(ptr: *const core::ffi::c_void) -> i32;
}

#[repr(C)]
pub struct Entry {
    pub name: *const core::ffi::c_char,
}

pub unsafe fn read_second(ptr: *const core::ffi::c_char) -> core::ffi::c_char {
    *ptr.offset(1)
}

pub unsafe fn call_raw_bridge(buf: [core::ffi::c_char; 8]) -> i32 {
    let entry = Entry { name: buf.as_ptr() };
    read_second(entry.name) as i32 + raw_read(entry.name as *const core::ffi::c_void)
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub name: &'a [core::ffi::c_char]",
            "raw_read(if (entry.name).is_empty()",
            "(entry.name).as_ptr()",
        ],
        &["pub name: *const core::ffi::c_char"],
    );
}

#[test]
fn test_field_raw_bridge_pointee_cast_mut_u8_slice_to_mut_c_void() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn raw_write(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Entry {
    pub data: *mut u8,
}

pub unsafe fn write_second(ptr: *mut u8) {
    *ptr.offset(1) = 9;
}

pub unsafe fn call_raw_bridge(mut buf: [u8; 8]) -> u8 {
    let entry = Entry {
        data: buf.as_mut_ptr(),
    };
    write_second(entry.data);
    raw_write(entry.data as *mut core::ffi::c_void);
    *entry.data.offset(0)
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub data: &'a mut [u8]",
            "raw_write(if (entry.data).is_empty()",
            "(entry.data).as_mut_ptr()",
        ],
        &["pub data: *mut u8"],
    );
}

#[test]
fn test_field_raw_bridge_pointee_cast_shared_u8_slice_to_const_u16() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn raw_word(ptr: *const u16) -> i32;
}

#[repr(C)]
pub struct Entry {
    pub bytes: *const u8,
}

pub unsafe fn read_second(ptr: *const u8) -> u8 {
    *ptr.offset(1)
}

pub unsafe fn call_raw_bridge(buf: [u8; 8]) -> i32 {
    let entry = Entry {
        bytes: buf.as_ptr(),
    };
    read_second(entry.bytes) as i32 + raw_word(entry.bytes as *const u16)
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub bytes: &'a [u8]",
            "raw_word(if (entry.bytes).is_empty()",
            "(entry.bytes).as_ptr()",
        ],
        &["pub bytes: *const u8"],
    );
}

#[test]
fn test_field_raw_bridge_pointee_cast_shared_cursor_to_const_u16() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn raw_word(ptr: *const u16) -> i32;
}

#[repr(C)]
pub struct Window {
    pub cursor: *const u8,
}

pub unsafe fn read_previous(ptr: *const u8) -> u8 {
    *ptr.offset(-1)
}

pub unsafe fn call_raw_bridge(buf: [u8; 8]) -> i32 {
    let window = Window {
        cursor: buf.as_ptr().offset(4),
    };
    read_previous(window.cursor) as i32 + raw_word(window.cursor as *const u16)
}
"#,
        &[
            "pub struct Window<'a>",
            "pub cursor: crate::slice_cursor::SliceCursor<'a, u8>",
            "raw_word(if (window.cursor).is_empty()",
            "(window.cursor).as_ptr()",
        ],
        &["pub cursor: *const u8"],
    );
}

#[test]
fn test_field_raw_bridge_pointee_cast_mut_cursor_to_mut_c_void() {
    run_typecheck_test_after_shape_check(
        r#"
extern "C" {
    fn raw_write(ptr: *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Window {
    pub cursor: *mut u8,
}

pub unsafe fn write_previous(ptr: *mut u8) {
    *ptr.offset(-1) = 7;
}

pub unsafe fn call_raw_bridge(mut buf: [u8; 8]) -> u8 {
    let window = Window {
        cursor: buf.as_mut_ptr().offset(4),
    };
    write_previous(window.cursor);
    raw_write(window.cursor as *mut core::ffi::c_void);
    *window.cursor.offset(-1)
}
"#,
        &[
            "pub struct Window<'a>",
            "pub cursor: crate::slice_cursor::SliceCursorMut<'a, u8>",
            "raw_write(if (window.cursor).is_empty()",
            "(window.cursor).as_mut_ptr()",
        ],
        &["pub cursor: *mut u8"],
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
    assert!(
        s.contains("|___idx| ((p).offset(___idx)) as *mut i32"),
        "{s}"
    );
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
            "prev_idx.map_or(std::ptr::null_mut()as*muti32,|___idx|if((raw)[(___idx)asusize..]).is_empty(){std::ptr::null_mut::<i32>()}else{((raw)[(___idx)asusize..]).as_mut_ptr()})"
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
fn test_map_or_raw_pointer_constness_mut_i8_offset_from_typechecks() {
    run_test(
        r#"
pub unsafe extern "C" fn distance_from_candidate(
    mut ptr: *mut i8,
    idx: Option<isize>,
    pos: usize,
) -> isize {
    if ptr.is_null() {
        return 0;
    }
    *ptr.offset(0) = 1;
    let current: *mut i8 = ptr.add(pos);
    return current.offset_from(idx.map_or(
        std::ptr::null_mut() as *mut i8,
        |___idx| ((ptr).offset(___idx)) as *mut i8,
    ));
}
"#,
        &[".as_mut_ptr()"],
        &[".as_ptr()"],
    );
}

#[test]
fn test_map_or_raw_pointer_constness_mut_u8_add_offset_from_typechecks() {
    run_test(
        r#"
pub unsafe extern "C" fn byte_delta(
    mut hdr: *mut u8,
    idx: Option<isize>,
    pos: usize,
) -> isize {
    if hdr.is_null() {
        return 0;
    }
    *hdr.add(0usize) = 1;
    *hdr.offset(pos as isize) = (*hdr.add(0usize)).wrapping_add(1);
    let current: *mut u8 = hdr.offset(pos as isize);
    return current.offset_from(idx.map_or(
        std::ptr::null_mut() as *mut u8,
        |___idx| ((hdr).add(___idx as usize)) as *mut u8,
    ));
}
"#,
        &[".as_mut_ptr()"],
        &[],
    );
}

#[test]
fn test_map_or_raw_pointer_constness_mut_u8_offset_from_typechecks() {
    run_test(
        r#"
pub unsafe extern "C" fn byte_distance(
    mut hdr: *mut u8,
    idx: Option<isize>,
    pos: usize,
) -> isize {
    if hdr.is_null() {
        return 0;
    }
    *hdr.offset(0) = 1;
    let current: *mut u8 = hdr.add(pos);
    return current.offset_from(idx.map_or(
        std::ptr::null_mut() as *mut u8,
        |___idx| ((hdr).offset(___idx)) as *mut u8,
    ));
}
"#,
        &[".as_mut_ptr()"],
        &[".as_ptr()"],
    );
}

#[test]
fn test_map_or_raw_pointer_constness_mut_struct_offset_from_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: i32,
}

pub unsafe extern "C" fn entry_delta(
    mut entries: *mut Entry,
    idx: Option<isize>,
    pos: usize,
) -> isize {
    if entries.is_null() {
        return 0;
    }
    (*entries.offset(0)).value = 1;
    let current: *mut Entry = entries.add(pos);
    return current.offset_from(idx.map_or(
        std::ptr::null_mut() as *mut Entry,
        |___idx| ((entries).offset(___idx)) as *mut Entry,
    ));
}
"#,
        &[".as_mut_ptr()"],
        &[".as_ptr()"],
    );
}

#[test]
fn test_map_or_raw_pointer_constness_mut_function_argument_typechecks() {
    run_test(
        r#"
extern "C" {
    fn consume_mut_byte(ptr: *mut u8) -> i32;
}

pub unsafe extern "C" fn call_consume(
    mut ptr: *mut u8,
    idx: Option<isize>,
) -> i32 {
    if ptr.is_null() {
        return 0;
    }
    *ptr.offset(0) = 1;
    return consume_mut_byte(idx.map_or(
        std::ptr::null_mut() as *mut u8,
        |___idx| ((ptr).offset(___idx)) as *mut u8,
    ));
}
"#,
        &[".as_mut_ptr()"],
        &[".as_ptr()"],
    );
}

#[test]
fn test_map_or_raw_pointer_constness_const_i8_offset_from_typechecks() {
    run_test(
        r#"
pub unsafe extern "C" fn const_distance_from_candidate(
    mut ptr: *const i8,
    idx: Option<isize>,
    pos: usize,
) -> isize {
    if ptr.is_null() {
        return 0;
    }
    let first = *ptr.offset(0) as isize;
    let current: *const i8 = ptr.add(pos);
    return first
        + current.offset_from(idx.map_or(
            std::ptr::null() as *const i8,
            |___idx| ((ptr).offset(___idx)) as *const i8,
        ));
}
"#,
        &[".as_ptr()"],
        &[".as_mut_ptr()"],
    );
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
fn test_array_local_rewriter_keeps_alias_typed_field_base_as_raw_pointer() {
    let code = r#"
#[repr(C)]
pub struct State {
    pub out: *mut u8,
}

pub type StatePtr = *mut State;

pub unsafe fn copy_from_back(mut s: StatePtr, mut length: isize, mut distance: isize) -> u8 {
    let mut src: *mut u8 = (*s).out.offset(-distance);
    let mut dst: *mut u8 = (*s).out;
    (*s).out = (*s).out.offset(length);
    *dst = *src;
    dst = dst.offset(1);
    src = src.offset(1);
    *dst
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(
        changed,
        "expected aliased field-base pointer to be rewritten:\n{s}"
    );
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(
        !s.contains("((*s).out).as_ptr()"),
        "raw pointer field base must not be reconstructed with as_ptr:\n{s}"
    );
}

#[test]
fn test_array_local_rewriter_casts_c_void_base_for_relative_offset_from() {
    let code = r#"
pub unsafe fn search(mut array_ptr: *mut core::ffi::c_void, mut item_size: usize, mut lim: usize) -> usize {
    let mut part: *mut u8 = 0 as *mut u8;
    let mut array: *mut u8 = array_ptr as *mut u8;
    let mut base: *mut u8 = array_ptr as *mut u8;
    while lim != 0 {
        part = base.offset((lim / 2).wrapping_mul(item_size) as isize);
        if *part == 0 {
            base = part;
            break;
        }
        base = part.offset(item_size as isize);
        lim >>= 1;
    }
    base.offset_from(array) as usize
}
"#;
    let (s, changed) = rewrite_array_local_provenance_with_config(code, &Config::default());
    assert!(changed, "expected c_void base cursor to be rewritten:\n{s}");
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(
        !s.contains(".offset_from((array_ptr).offset(0isize))"),
        "relative offset_from must not compare u8 and c_void pointers:\n{s}"
    );
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

#[test]
fn test_direct_union_field_pointer_stays_raw() {
    let code = r#"
#[repr(C)]
pub union U {
    pub p: *mut i32,
    pub n: usize,
}
pub unsafe fn foo(u: U) -> *mut i32 {
    u.p
}
"#;
    let (s, _) = rewrite_struct_arrays_then_array_local_then_pointer(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("pub union U"), "{s}");
    assert!(s.contains("-> *mut i32"), "{s}");
}

#[test]
fn test_nested_union_field_pointer_stays_raw() {
    let code = r#"
#[repr(C)]
pub struct S {
    pub x: i32,
    pub y: U,
}
#[repr(C)]
pub union U {
    pub x: i32,
    pub y: Inner,
}
#[repr(C)]
pub struct Inner {
    pub x: i32,
    pub y: *mut i32,
}
impl Copy for Inner {}
impl Clone for Inner {
    fn clone(&self) -> Self {
        *self
    }
}
pub unsafe extern "C" fn foo(mut sp: *mut S) -> *mut i32 {
    return (*sp).y.y.y;
}
"#;
    let (s, _) = rewrite_struct_arrays_then_array_local_then_pointer(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("pub union U"), "{s}");
    assert!(s.contains("-> *mut i32"), "{s}");
}

#[test]
fn test_union_field_mut_borrow_marks_outer_pointer_mut() {
    let code = r#"
#[repr(C)]
pub struct Ctx {
    pub u: U,
    pub tag: i32,
}
#[repr(C)]
pub union U {
    pub a: A,
    pub b: B,
}
#[repr(C)]
pub struct A {
    pub state: i32,
}
impl Copy for A {}
impl Clone for A {
    fn clone(&self) -> Self {
        *self
    }
}
#[repr(C)]
pub struct B {
    pub state: i32,
}
impl Copy for B {}
impl Clone for B {
    fn clone(&self) -> Self {
        *self
    }
}
pub unsafe extern "C" fn init_a(mut a: *mut A) {
    (*a).state = 1;
}
pub unsafe extern "C" fn init_ctx(mut ctx: *mut Ctx) {
    if (*ctx).tag == 1 {
        init_a(&mut (*ctx).u.a);
    }
}
"#;
    let (s, _) = rewrite_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(
        s.contains("pub unsafe extern \"C\" fn init_ctx(mut ctx: &mut crate::Ctx)"),
        "Expected mutable outer pointer after mutable borrow through union field:\n{s}",
    );
    assert!(
        !s.contains("pub unsafe extern \"C\" fn init_ctx(mut ctx: &crate::Ctx)"),
        "init_ctx::ctx must not be rewritten as shared:\n{s}",
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
fn test_array_local_rewriter_tracks_index_for_reassigned_field_base() {
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
    assert!(
        changed,
        "expected field-base index tracking to rewrite:\n{s}"
    );
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("out_idx") || s.contains("s_out_idx"), "{s}");
    assert!(s.contains("src_idx"), "{s}");
    assert!(s.contains("dst_idx"), "{s}");
    assert!(s.contains("let mut src: *mut i8"), "{s}");
    assert!(s.contains("let mut dst: *mut i8"), "{s}");
    assert!(!s.contains("(*s).out = (*s).out.offset(length)"), "{s}");
}

#[test]
fn test_array_local_rewriter_keeps_field_base_memory_copy_cursors_index_only() {
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
    assert!(
        changed,
        "expected field-base memory copy cursors to be rewritten:\n{s}"
    );
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("src_idx"), "{s}");
    assert!(s.contains("dst_idx"), "{s}");
    assert!(!s.contains("let mut src: *mut i8"), "{s}");
    assert!(!s.contains("let mut dst: *mut i8"), "{s}");
    assert!(
        s.contains("memset(((*s).out).offset(dst_idx)")
            || s.contains("memset((*s).out.offset(dst_idx)"),
        "expected memset destination to inline dst_idx from the field base:\n{s}"
    );
    assert!(
        s.contains("*(((*s).out).offset(src_idx)") || s.contains("*((*s).out.offset(src_idx)"),
        "expected src deref to inline src_idx from the field base:\n{s}"
    );
    assert!(
        s.contains("*(((*s).out).offset(dst_idx)") || s.contains("*((*s).out.offset(dst_idx)"),
        "expected dst deref to inline dst_idx from the field base:\n{s}"
    );
}

#[test]
fn test_array_local_rewriter_keeps_distinct_indexes_for_two_reassigned_field_bases() {
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
    assert!(
        changed,
        "expected both reassigned field bases to be rewritten:\n{s}"
    );
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
    assert!(s.contains("let mut a_idx: isize"), "{s}");
    assert!(s.contains("let mut b_idx: isize"), "{s}");
    assert!(s.contains("ax_idx"), "{s}");
    assert!(s.contains("bx_idx"), "{s}");
    assert!(s.contains("let mut ax: *mut i8"), "{s}");
    assert!(s.contains("let mut bx: *mut i16"), "{s}");
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
fn test_array_local_rewriter_handles_result_pointer_payload() {
    let code = r#"
pub static mut GLOBAL: i32 = 0;

pub unsafe fn foo(mut x: i32) -> Result<*mut i32, i32> {
    let mut p___s: bool = false;
    let mut p___v: *mut i32 = core::ptr::null_mut();
    let mut p: *mut *mut i32 = &mut p___v;
    if x != 0 {
        let mut q: *mut i32 = &raw mut GLOBAL;
        { p___s = true; *p = q };
        return if p___s { Ok(p___v) } else { Err(0) };
    } else {
        return if p___s { Ok(p___v) } else { Err(1) };
    };
}

pub unsafe fn bar() {
    let mut p: *mut i32 = core::ptr::null_mut();
    let mut x: i32 =
        match { let rv___ = foo(1); rv___ } {
            Ok(v___) => { *(&mut p) = v___; 0 }
            Err(v___) => v___,
        };
    let _ = x;
    let _ = p;
}
"#;
    let (s, _) = rewrite_array_local_provenance_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
}

#[test]
fn test_replace_local_borrows_handles_result_pointer_payload() {
    let code = r#"
pub static mut GLOBAL: i32 = 0;

pub unsafe fn foo(mut x: i32) -> Result<*mut i32, i32> {
    let mut p___s: bool = false;
    let mut p___v: *mut i32 = core::ptr::null_mut();
    let mut p: *mut *mut i32 = &mut p___v;
    if x != 0 {
        let mut q: *mut i32 = &raw mut GLOBAL;
        { p___s = true; *p = q };
        return if p___s { Ok(p___v) } else { Err(0) };
    } else {
        return if p___s { Ok(p___v) } else { Err(1) };
    };
}

pub unsafe fn bar() {
    let mut p: *mut i32 = core::ptr::null_mut();
    let mut x: i32 =
        match { let rv___ = foo(1); rv___ } {
            Ok(v___) => { *(&mut p) = v___; 0 }
            Err(v___) => v___,
        };
    let _ = x;
    let _ = p;
}
"#;
    let (s, _) = rewrite_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
}

#[test]
fn test_fn_ptr_static_struct_array_option_cast_rewrites_storage_and_call_site() {
    run_test(
        r#"
#[repr(C)]
pub struct Command {
    pub run: Option<unsafe extern "C" fn(i32, *mut *mut i8) -> i32>,
}

pub unsafe extern "C" fn add(mut argc: i32, mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return argc;
}

pub static COMMANDS: [Command; 1] = [Command {
    run: Some(add as unsafe extern "C" fn(i32, *mut *mut i8) -> i32),
}];

pub unsafe fn dispatch(mut argc: i32, mut argv: *mut *mut i8) -> i32 {
    let handler = COMMANDS[0].run.expect("command");
    return handler(argc, argv);
}
"#,
        &[
            "fn add(mut argc: i32, mut argv: &mut [*mut i8]) -> i32",
            "Option<unsafe extern \"C\" fn(i32, &mut [*mut i8]) -> i32>",
            "return handler(argc, (argv));",
        ],
        &[
            "Option<unsafe extern \"C\" fn(i32, *mut *mut i8) -> i32>",
            "add as unsafe extern \"C\" fn(i32, *mut *mut i8) -> i32",
            "return handler(argc, (argv).as_mut_ptr());",
        ],
    );
}

#[test]
fn test_fn_ptr_static_option_alias_cast_rewrites_alias_and_initializer() {
    run_test(
        r#"
pub type CommandFn = Option<unsafe extern "C" fn(i32, *mut *mut i8) -> i32>;

pub unsafe extern "C" fn add(mut argc: i32, mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return argc;
}

pub static COMMAND: CommandFn =
    Some(add as unsafe extern "C" fn(i32, *mut *mut i8) -> i32);
"#,
        &[
            "type CommandFn = Option<unsafe extern \"C\" fn(i32, &mut [*mut i8]) -> i32>",
            "Some(add as unsafe extern \"C\" fn(i32, &mut [*mut i8]) -> i32)",
        ],
        &[
            "type CommandFn = Option<unsafe extern \"C\" fn(i32, *mut *mut i8) -> i32>",
            "add as unsafe extern \"C\" fn(i32, *mut *mut i8) -> i32",
        ],
    );
}

#[test]
fn test_fn_ptr_const_aggregate_option_cast_rewrites_nested_field_type() {
    run_test(
        r#"
#[repr(C)]
pub struct Command {
    pub run: Option<unsafe extern "C" fn(i32, *mut *mut i8) -> i32>,
}

pub unsafe extern "C" fn add(mut argc: i32, mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return argc;
}

pub const COMMAND: Command = Command {
    run: Some(add as unsafe extern "C" fn(i32, *mut *mut i8) -> i32),
};
"#,
        &[
            "fn add(mut argc: i32, mut argv: &mut [*mut i8]) -> i32",
            "Option<unsafe extern \"C\" fn(i32, &mut [*mut i8]) -> i32>",
            "Some(add as unsafe extern \"C\" fn(i32, &mut [*mut i8]) -> i32)",
        ],
        &[
            "Option<unsafe extern \"C\" fn(i32, *mut *mut i8) -> i32>",
            "add as unsafe extern \"C\" fn(i32, *mut *mut i8) -> i32",
        ],
    );
}

#[test]
fn test_section7_address_cast_materializes_slice_pointer() {
    run_test(
        r#"
pub unsafe extern "C" fn crc32_align(mut buf: *const u8, mut len: usize) -> u64 {
    if buf.is_null() {
        return 0;
    }

    let mut sum: u64 = 0;
    while len != 0 && (buf as core::ffi::c_ulong & 7 as core::ffi::c_ulong) != 0 {
        sum = sum.wrapping_add(*buf as u64);
        buf = buf.offset(1);
        len = len.wrapping_sub(1);
    }
    return sum;
}
"#,
        &[
            "mut buf: &[u8]",
            "if (buf).is_empty()",
            "std::ptr::null::<u8>()",
            "(buf).as_ptr() } as core::ffi::c_ulong",
        ],
        &["buf as core::ffi::c_ulong"],
    );
}

#[test]
fn test_section7_typed_raw_cast_materializes_mut_slice_pointer() {
    run_test(
        r#"
#[repr(C)]
pub struct GitCommit {
    pub id: i32,
}

pub unsafe extern "C" fn collect_parent(
    mut parent: *mut GitCommit,
    mut n: usize,
) -> *const GitCommit {
    (*parent.offset(n as isize)).id = 1;
    let mut parents: [*const GitCommit; 1] = [parent as *const GitCommit];
    return parents[0];
}
"#,
        &[
            "mut parent: &mut [crate::GitCommit]",
            "std::ptr::null::<crate::GitCommit>()",
            "(parent).as_ptr() } as *const GitCommit",
        ],
        &[
            "parent as *const crate::GitCommit",
            "parent as *const GitCommit",
        ],
    );
}

#[test]
fn test_section7_c_void_cast_materializes_mut_slice_pointer() {
    run_test(
        r#"
#[repr(C)]
pub struct GitRepository {
    pub id: i32,
}

pub unsafe extern "C" fn checkout_repo(mut repo: *mut GitRepository, mut slot: usize) -> i32 {
    (*repo.offset(slot as isize)).id = 7;
    if (repo as *mut core::ffi::c_void).is_null() {
        return 0;
    }
    return 1;
}
"#,
        &[
            "mut repo: &mut [crate::GitRepository]",
            "std::ptr::null_mut::<crate::GitRepository>()",
            "(repo).as_mut_ptr() } as",
        ],
        &["repo as *mut core::ffi::c_void"],
    );
}

#[test]
fn test_section7_c_char_cast_materializes_shared_slice_pointer() {
    run_test(
        r#"
extern "C" {
    fn use_strings(count: usize, strings: *const *const core::ffi::c_char);
}

pub unsafe extern "C" fn check_ref(mut ref_0: *const core::ffi::c_char) -> i32 {
    if *ref_0.offset(0) != 0 {
        let strings: [*const core::ffi::c_char; 3] = [
            b"bad\0".as_ptr() as *const core::ffi::c_char,
            ref_0 as *const core::ffi::c_char,
            b"\0".as_ptr() as *const core::ffi::c_char,
        ];
        use_strings(3, strings.as_ptr());
    }
    return *ref_0.offset(0) as i32;
}
"#,
        &[
            "mut ref_0: &[i8]",
            "std::ptr::null::<i8>()",
            "(ref_0).as_ptr() } as *const core::ffi::c_char",
        ],
        &["ref_0 as *const core::ffi::c_char"],
    );
}

#[test]
fn test_raw_aggregate_context_rewrites_const_array_elements() {
    run_test(
        r#"
extern "C" {
    fn use_strings(count: usize, strings: *const *const core::ffi::c_char);
}

pub unsafe extern "C" fn collect(mut text: *const core::ffi::c_char) -> i32 {
    if *text.offset(0) != 0 {
        let table: [*const core::ffi::c_char; 2] = [text, text.add(1usize)];
        use_strings(2, table.as_ptr());
    }
    return *text.offset(0) as i32;
}
"#,
        &[
            "mut text: &[i8]",
            "let table: [*const core::ffi::c_char; 2]",
            "(text).as_ptr()",
            ".add(1usize)",
        ],
        &["[text, text.add(1usize)]", "text.add(1usize)"],
    );
}

#[test]
fn test_raw_aggregate_context_rewrites_mut_array_elements() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub id: i32,
}

extern "C" {
    fn use_items(ptrs: *const *mut Item);
}

pub unsafe extern "C" fn collect(mut items: *mut Item, slot: usize) -> i32 {
    (*items.offset(slot as isize)).id = 5;
    let table: [*mut Item; 2] = [items, items.add(1usize)];
    use_items(table.as_ptr());
    return (*items.offset(slot as isize)).id;
}
"#,
        &[
            "mut items: &mut [crate::Item]",
            "let table: [*mut Item; 2]",
            "(items).as_mut_ptr()",
            ".add(1usize)",
        ],
        &["[items, items.add(1usize)]", "items.add(1usize)"],
    );
}

#[test]
fn test_raw_aggregate_context_rewrites_nested_struct_tuple_fields() {
    run_test(
        r#"
#[repr(C)]
pub struct RawBundle {
    pub first: *const i8,
    pub nested: (*const i8, [*const i8; 2]),
}

extern "C" {
    fn accept_bundle(bundle: RawBundle);
}

pub unsafe extern "C" fn publish(mut data: *const i8) -> i32 {
    if data.is_null() {
        return 0;
    }
    accept_bundle(RawBundle {
        first: data.offset(0),
        nested: (data.add(1usize), [data, data.add(2usize)]),
    });
    return *data.add(2usize) as i32;
}
"#,
        &[
            "mut data: &[i8]",
            "pub struct RawBundle {",
            "std::ptr::null::<i8>()",
            "} else { ((data).as_ptr()).offset(0) }",
            "} else { ((data).as_ptr()).add(1usize) }",
            "} else { ((data).as_ptr()).add(2usize) }",
        ],
        &[
            "RawBundle<'",
            "first: data.offset(0)",
            "data.add(1usize)",
            "[data, data.add(2usize)]",
        ],
    );
}

#[test]
fn test_raw_aggregate_context_rewrites_tuple_local_elements() {
    run_test(
        r#"
extern "C" {
    fn use_pair(first: *const i8, second: *const i8);
}

pub unsafe extern "C" fn collect(mut data: *const i8) -> i32 {
    if *data.offset(0) == 0 {
        return 0;
    }
    let pair: (*const i8, *const i8) = (data, data.add(1usize));
    use_pair(pair.0, pair.1);
    return *data.offset(0) as i32;
}
"#,
        &[
            "mut data: &[i8]",
            "let pair: (*const i8, *const i8)",
            "(data).as_ptr()",
            "} else { ((data).as_ptr()).add(1usize) }",
        ],
        &["(data, data.add(1usize))", "data.add(1usize)"],
    );
}

#[test]
fn test_raw_aggregate_context_rewrites_call_argument_array() {
    run_test(
        r#"
pub unsafe fn take_table(table: [*const i8; 2]) -> i32 {
    return *table[1usize] as i32;
}

pub unsafe extern "C" fn call_table(mut data: *const i8) -> i32 {
    if *data.offset(0) == 0 {
        return 0;
    }
    return take_table([data, data.add(1usize)]);
}
"#,
        &[
            "mut data: &[i8]",
            "pub unsafe fn take_table(table: [*const i8; 2])",
            "(data).as_ptr()",
            "} else { ((data).as_ptr()).add(1usize) }",
        ],
        &["take_table([data, data.add(1usize)])", "data.add(1usize)"],
    );
}

#[test]
fn test_raw_aggregate_element_contract_direct_const_array_arg_typechecks() {
    run_test(
        r#"
pub unsafe fn read_table(mut table: *const *const i8) -> i32 {
    return *(*table.offset(0)) as i32 + *(*table.offset(1)) as i32;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    return first as i32 + read_table([data, data.add(1usize)].as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_direct_mut_array_arg_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

pub unsafe fn read_items(mut items: *const *mut Item) -> i32 {
    (*(*items.offset(0))).value += 1;
    return (*(*items.offset(1))).value;
}

pub unsafe extern "C" fn dispatch(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value = 1;
    (*item.offset(1)).value = 2;
    return read_items([item, item.add(1usize)].as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_direct_mut_outer_array_arg_typechecks() {
    run_test(
        r#"
pub unsafe fn advance_first(mut table: *mut *const i8) -> i32 {
    *table.offset(0) = (*table.offset(0)).add(1usize);
    return *(*table.offset(0)) as i32;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    return first as i32 + advance_first([data, data.add(1usize)].as_mut_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_direct_nested_const_array_arg_typechecks() {
    run_test(
        r#"
pub unsafe fn read_rows(mut rows: *const [*const i8; 2]) -> i32 {
    return *(*rows.offset(0))[0usize] as i32 + *(*rows.offset(0))[1usize] as i32;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    return first as i32 + read_rows([[data, data.add(1usize)]].as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_direct_mut_tuple_array_arg_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

pub unsafe fn read_pairs(mut pairs: *const (*mut Item, *mut Item)) -> i32 {
    let next = pairs.offset(1isize);
    return (next as usize != pairs as usize) as i32;
}

pub unsafe extern "C" fn dispatch(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value = 1;
    (*item.offset(1)).value = 2;
    return read_pairs([(item, item.add(1usize))].as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_local_tuple_array_arg_typechecks() {
    run_test(
        r#"
pub unsafe fn read_pairs(mut pairs: *const (*const i8, *const i8)) -> i32 {
    let next = pairs.offset(1isize);
    return (next as usize != pairs as usize) as i32;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    let pairs = &[(data, data.add(1usize))];
    return first as i32 + read_pairs(pairs.as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_local_struct_array_arg_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Bundle {
    pub tag: i32,
    pub first: *const i8,
    pub second: *const i8,
}

impl Copy for Bundle {}

impl Clone for Bundle {
    fn clone(&self) -> Bundle {
        *self
    }
}

extern "C" {
    fn accept_bundle(bundle: Bundle);
}

pub unsafe fn read_bundles(mut bundles: *const Bundle) -> i32 {
    let bundle = *bundles.offset(0);
    accept_bundle(bundle);
    return bundle.tag;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    let bundles = &[Bundle {
        tag: first as i32,
        first: data,
        second: data.add(1usize),
    }];
    return read_bundles(bundles.as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_direct_tuple_array_arg_typechecks() {
    run_test(
        r#"
pub unsafe fn read_pairs(mut pairs: *const (*const i8, *const i8)) -> i32 {
    let next = pairs.offset(1isize);
    return (next as usize != pairs as usize) as i32;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    return first as i32 + read_pairs([(data, data.add(1usize))].as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_direct_nested_tuple_array_arg_typechecks() {
    run_test(
        r#"
pub unsafe fn read_nested(mut pairs: *const ((*const i8, [*const i8; 2]), i32)) -> i32 {
    let next = pairs.offset(1isize);
    return (next as usize != pairs as usize) as i32;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    return first as i32 + read_nested([((data, [data, data.add(1usize)]), 4)].as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_direct_struct_array_arg_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Bundle {
    pub tag: i32,
    pub first: *const i8,
    pub second: *const i8,
}

impl Copy for Bundle {}

impl Clone for Bundle {
    fn clone(&self) -> Bundle {
        *self
    }
}

extern "C" {
    fn accept_bundle(bundle: Bundle);
}

pub unsafe fn read_bundles(mut bundles: *const Bundle) -> i32 {
    let bundle = *bundles.offset(0);
    accept_bundle(bundle);
    return bundle.tag;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    return first as i32
        + read_bundles((&[Bundle {
            tag: first as i32,
            first: data,
            second: data.add(1usize),
        }]).as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_direct_nested_struct_array_arg_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Inner {
    pub ptrs: [*const i8; 2],
}

impl Copy for Inner {}

impl Clone for Inner {
    fn clone(&self) -> Inner {
        *self
    }
}

#[repr(C)]
pub struct Outer {
    pub inner: Inner,
    pub tag: i32,
    pub tail: *const i8,
}

impl Copy for Outer {}

impl Clone for Outer {
    fn clone(&self) -> Outer {
        *self
    }
}

extern "C" {
    fn accept_outer(outer: Outer);
}

pub unsafe fn read_outers(mut outers: *const Outer) -> i32 {
    let outer = *outers.offset(0);
    accept_outer(outer);
    return outer.tag;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    return first as i32
        + read_outers([Outer {
            inner: Inner {
                ptrs: [data, data.add(1usize)],
            },
            tag: first as i32,
            tail: data.add(2usize),
        }].as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_local_nested_struct_array_then_passed_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Inner {
    pub ptrs: [*const i8; 2],
}

impl Copy for Inner {}

impl Clone for Inner {
    fn clone(&self) -> Inner {
        *self
    }
}

#[repr(C)]
pub struct Outer {
    pub inner: Inner,
    pub tag: i32,
    pub tail: *const i8,
}

impl Copy for Outer {}

impl Clone for Outer {
    fn clone(&self) -> Outer {
        *self
    }
}

extern "C" {
    fn accept_outer(outer: Outer);
}

pub unsafe fn read_outers(mut outers: *const Outer) -> i32 {
    let outer = *outers.offset(0);
    accept_outer(outer);
    return outer.tag;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    let outers = &[Outer {
        inner: Inner {
            ptrs: [data, data.add(1usize)],
        },
        tag: first as i32,
        tail: data.add(2usize),
    }];
    return first as i32 + read_outers(outers.as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_raw_aggregate_element_contract_local_nested_tuple_array_then_passed_typechecks() {
    run_test(
        r#"
pub unsafe fn read_nested(mut pairs: *const ((*const i8, [*const i8; 2]), i32)) -> i32 {
    let next = pairs.offset(1isize);
    return (next as usize != pairs as usize) as i32;
}

pub unsafe extern "C" fn dispatch(mut data: *const i8) -> i32 {
    let first = *data.offset(0);
    let pairs = &[((data, [data, data.add(1usize)]), 9)];
    return first as i32 + read_nested(pairs.as_ptr());
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_section7_raw_origin_offset_raw_cast_is_not_promoted_to_cursor() {
    run_test(
        r#"
pub unsafe extern "C" fn compact(mut str: *mut core::ffi::c_char) -> usize {
    let mut scan_idx: Option<isize> = None;
    let mut pos_idx: isize = 0isize;
    if str.is_null() {
        return 0;
    }

    scan_idx = Some(0isize);
    while *((str).offset(scan_idx.unwrap()) as *mut i8) != 0 {
        *((str).offset(pos_idx) as *mut i8) =
            *((str).offset(scan_idx.unwrap()) as *mut i8);
        pos_idx = (pos_idx) + ((1) as isize);
        scan_idx = Some((scan_idx.unwrap()) + ((1) as isize));
    }

    if (str).offset(pos_idx) as *mut i8 !=
        scan_idx.map_or(std::ptr::null_mut() as *mut i8,
            |___idx| ((str).offset(___idx)) as *mut i8)
    {
        *((str).offset(pos_idx) as *mut i8) = 0;
    }

    return pos_idx as usize;
}
"#,
        &[
            "mut str:",
            "(str).offset(pos_idx)",
            "return pos_idx as usize",
            "*mut i8",
        ],
        &["crate::slice_cursor::SliceCursorMut"],
    );
}

#[test]
fn test_section7_call_argument_c_void_cast_materializes_promoted_param() {
    run_test(
        r#"
#[repr(C)]
pub struct GitRepository {
    pub id: i32,
}

#[repr(C)]
pub struct GitIndex {
    pub owner: *mut core::ffi::c_void,
    pub id: i32,
}

unsafe extern "C" fn git_ptr__swap(
    mut ptr: *mut *mut core::ffi::c_void,
    mut newval: *mut core::ffi::c_void,
) -> *mut core::ffi::c_void {
    let mut old: *mut core::ffi::c_void = *ptr;
    *ptr = newval;
    return old;
}

pub unsafe extern "C" fn set_odb(
    mut repo: *mut GitRepository,
    mut index: *mut GitIndex,
    mut slot: usize,
) {
    (*repo.offset(slot as isize)).id = 1;
    (*index.offset(slot as isize)).id = 2;
    git_ptr__swap(
        &mut (*index).owner as *mut *mut core::ffi::c_void,
        repo as *mut core::ffi::c_void,
    );
}
"#,
        &[
            "mut repo: &mut [crate::GitRepository]",
            "(repo).as_mut_ptr() as *mut",
        ],
        &["repo as *mut core::ffi::c_void"],
    );
}

#[test]
fn test_section7_nested_c_void_address_cast_materializes_promoted_param() {
    run_test(
        r#"
extern "C" {
    fn read(fd: i32, buf: *mut core::ffi::c_void, count: usize) -> isize;
}

pub unsafe extern "C" fn getseed(mut seed: *mut u64) -> u64 {
    if seed.is_null() {
        return 0;
    }

    read(
        0,
        seed as *mut core::ffi::c_void,
        core::mem::size_of::<u64>(),
    );
    *seed.offset(0) = (*seed.offset(0) as u64) ^
        ((seed as *mut core::ffi::c_void as usize as u64) << 32);
    return *seed.offset(0);
}
"#,
        &[
            "mut seed: &mut [u64]",
            "std::ptr::null_mut::<u64>()",
            "(seed).as_mut_ptr() } as *mut core::ffi::c_void as",
        ],
        &["seed as *mut core::ffi::c_void as usize as u64"],
    );
}

#[test]
fn test_forced_raw_param_call_result_keeps_signature_and_body_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Repo {
    pub odb: *mut Odb,
}

#[repr(C)]
pub struct Odb {
    pub owner: *mut core::ffi::c_void,
    pub refcount: i32,
}

unsafe extern "C" fn git_ptr__swap(
    mut ptr: *mut *mut core::ffi::c_void,
    mut newval: *mut core::ffi::c_void,
) -> *mut core::ffi::c_void {
    let mut old: *mut core::ffi::c_void = *ptr;
    *ptr = newval;
    return old;
}

unsafe extern "C" fn git_odb_free(mut odb: *mut Odb) {
    if !odb.is_null() {
        (*odb).refcount = 0;
    }
}

pub unsafe extern "C" fn set_odb(mut repo: *mut Repo, mut odb: *mut Odb) {
    if !odb.is_null() {
        (*odb).refcount += 1;
    }
    odb = git_ptr__swap(
        &mut (*repo).odb as *mut *mut Odb as *mut *mut core::ffi::c_void,
        odb as *mut core::ffi::c_void,
    ) as *mut Odb;
    if !odb.is_null() {
        git_odb_free(odb);
    }
}
"#,
        &[
            "mut odb: *mut crate::Odb",
            "odb as *mut core::ffi::c_void",
            "if !odb.is_null()",
        ],
        &["mut odb: &mut [crate::Odb]", "mut odb: &mut crate::Odb"],
    );
}

#[test]
fn test_forced_raw_slice_param_call_result_keeps_signature_and_body_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: i32,
}

unsafe extern "C" fn raw_identity(mut ptr: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    return ptr;
}

pub unsafe extern "C" fn replace_entry(mut entry: *mut Entry, mut slot: usize) {
    if entry.is_null() {
        return;
    }
    (*entry.offset(slot as isize)).value += 1;
    entry = raw_identity(entry as *mut core::ffi::c_void) as *mut Entry;
    if !entry.is_null() {
        (*entry).value += 1;
    }
}
"#,
        &[
            "mut entry: *mut crate::Entry",
            "entry as *mut core::ffi::c_void",
            "if !entry.is_null()",
        ],
        &[
            "mut entry: &mut [crate::Entry]",
            "mut entry: &mut crate::Entry",
        ],
    );
}

#[test]
fn test_section12_keeps_hashmap_link_fields_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: i32,
}

#[repr(C)]
pub struct Map {
    pub entries: *mut Entry,
    pub last: *mut Entry,
}

pub unsafe extern "C" fn select_entry(mut map: *mut Map, mut index: usize) {
    (*map).last = ((*map).entries).offset(index as isize);
}
"#,
        &[
            "pub entries: &'a mut [Entry]",
            "pub last: *mut Entry",
            "if ((map.entries)[(index as isize) as usize..]).is_empty()",
            "std::ptr::null_mut::<crate::Entry>()",
            "} else { ((map.entries)[(index as isize) as usize..]).as_mut_ptr() };",
        ],
        &["pub last: &", "pub last: Option<&"],
    );
}

#[test]
fn test_struct_field_storage_lifetime_slice_param_indexed_result_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
pub unsafe fn read_second(p: *const i32) -> i32 {
    *p.offset(1)
}

#[repr(C)]
pub struct Hashmap {
    pub entries: *mut i32,
    pub xpp: *const i32,
}

pub unsafe extern "C" fn fill_hashmap(
    mut xpp: *const i32,
    mut result: *mut Hashmap,
) -> i32 {
    (*result.offset(0)).xpp = xpp;
    (*result.offset(0)).entries = (*result.offset(0)).entries;
    return read_second((*result.offset(0)).xpp) + read_second(xpp);
}
"#,
        &[
            "pub struct Hashmap<'a>",
            "pub xpp: &'a [i32]",
            "pub unsafe fn read_second(p: &[i32])",
            "mut xpp: &'",
            "[i32]",
            "mut result: &mut [crate::Hashmap<'",
        ],
        &["pub xpp: *const i32"],
    );
}

#[test]
fn test_struct_field_storage_lifetime_slice_param_deref_result_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
pub unsafe fn read_second(p: *const i32) -> i32 {
    *p.offset(1)
}

#[repr(C)]
pub struct Hashmap {
    pub entries: *mut i32,
    pub xpp: *const i32,
}

pub unsafe extern "C" fn fill_hashmap_one(
    mut xpp: *const i32,
    mut result: *mut Hashmap,
    mut idx: isize,
) -> i32 {
    (*result).xpp = xpp;
    (*result).entries = (*result).entries;
    return read_second((*result).xpp) + read_second(xpp) + idx as i32;
}
"#,
        &[
            "pub struct Hashmap<'a>",
            "pub xpp: &'a [i32]",
            "pub unsafe fn read_second(p: &[i32])",
            "mut xpp: &'",
            "[i32]",
            "mut result: &mut crate::Hashmap<'",
        ],
        &["pub xpp: *const i32"],
    );
}

#[test]
fn test_struct_field_storage_lifetime_cursor_param_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct Hashmap {
    pub entries: *mut i32,
    pub cursor: *const i32,
}

pub unsafe extern "C" fn install_cursor(
    mut cursor: *const i32,
    mut result: *mut Hashmap,
) -> i32 {
    (*result.offset(0)).cursor = cursor.offset(3);
    (*result.offset(0)).entries = (*result.offset(0)).entries;
    return *(*result.offset(0)).cursor.offset(-1);
}
"#,
        &[
            "pub struct Hashmap {",
            "pub cursor: *const i32",
            "mut cursor: &[i32]",
            "mut result: &mut [crate::Hashmap]",
            "((cursor)[(3) as usize..]).as_ptr()",
            ".cursor.offset(-1)",
        ],
        &[
            "pub cursor: crate::slice_cursor::SliceCursor",
            "SliceCursor::with_pos",
        ],
    );
}

#[test]
fn test_section15_option_fn_payload_cast_in_extern_call_keeps_raw_until_supported() {
    let code = r#"
#[repr(C)]
pub struct GitFilter {
    pub id: i32,
}

#[repr(C)]
pub struct GitStr {
    pub ptr: *mut i8,
}

#[repr(C)]
pub struct GitFilterSource {
    pub mode: i32,
}

#[repr(C)]
pub struct GitWritestream {
    pub id: i32,
}

unsafe extern "C" {
    pub fn git_filter_buffered_stream_new(
        out: *mut *mut GitWritestream,
        filter: *mut GitFilter,
        apply: Option<unsafe extern "C" fn(
            *mut GitFilter,
            *mut *mut core::ffi::c_void,
            *mut GitStr,
            *const GitStr,
            *const GitFilterSource,
        ) -> i32>,
        empty: *mut GitStr,
        payload: *mut *mut core::ffi::c_void,
        source: *const GitFilterSource,
        next: *mut GitWritestream,
    ) -> i32;
}

pub unsafe extern "C" fn crlf_apply(
    mut filter: *mut GitFilter,
    mut payload: *mut *mut core::ffi::c_void,
    mut out: *mut GitStr,
    mut src: *const GitStr,
    mut source: *const GitFilterSource,
) -> i32 {
    (*out).ptr = (*src).ptr;
    *payload = core::ptr::null_mut();
    return (*filter).id + (*source).mode;
}

pub unsafe extern "C" fn crlf_stream(
    mut out: *mut *mut GitWritestream,
    mut filter: *mut GitFilter,
    mut payload: *mut *mut core::ffi::c_void,
    mut source: *const GitFilterSource,
    mut next: *mut GitWritestream,
) -> i32 {
    return git_filter_buffered_stream_new(
        out,
        filter,
        (Some(crlf_apply as unsafe extern "C" fn(
            *mut GitFilter,
            *mut *mut core::ffi::c_void,
            *mut GitStr,
            *const GitStr,
            *const GitFilterSource,
        ) -> i32)) as Option<unsafe extern "C" fn(
            *mut GitFilter,
            *mut *mut core::ffi::c_void,
            *mut GitStr,
            *const GitStr,
            *const GitFilterSource,
        ) -> i32>,
        core::ptr::null_mut(),
        payload,
        source,
        next,
    );
}
"#;
    let (s, _) = rewrite_with_config(code, &Config::default());
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);
}

#[test]
fn test_deref_array_pointer_as_mut_ptr_offset_without_rewrite_decision() {
    run_test(
        r#"
#[repr(C)]
pub struct Hunk {
    pub header_len: usize,
    pub header: [i8; 128],
}

#[repr(C)]
pub struct Line {
    pub content: *const i8,
    pub content_len: usize,
}

unsafe extern "C" {
    pub fn install(
        cb: Option<unsafe extern "C" fn(*const Hunk, *mut Line) -> i32>,
    ) -> i32;
}

pub unsafe extern "C" fn print_hunk(mut h: *const Hunk, mut line: *mut Line) -> i32 {
    let mut content: *const i8 = ((*h).header).as_ptr();
    (*line).content = content;
    (*line).content_len = (*h).header_len;
    return *content as i32;
}

pub unsafe extern "C" fn register() -> i32 {
    return install(
        (Some(print_hunk as unsafe extern "C" fn(*const Hunk, *mut Line) -> i32))
            as Option<unsafe extern "C" fn(*const Hunk, *mut Line) -> i32>,
    );
}
"#,
        &["content: Option<&i8>", "(&((*h).header)).first()"],
        &["((*h).header).as_ptr()"],
    );
}

#[test]
fn test_section4_keeps_opaque_out_param_local_raw() {
    run_test(
        r#"
#![feature(extern_types)]

extern "C" {
    pub type git_branch_iterator;
    pub fn memset(dst: *mut core::ffi::c_void, value: i32, len: usize) -> *mut core::ffi::c_void;
    pub fn git_branch_iterator_new(out: *mut *mut git_branch_iterator) -> i32;
    pub fn git_branch_iterator_free(iter: *mut git_branch_iterator);
}

pub unsafe extern "C" fn list_branches() -> i32 {
    let mut iter: *mut git_branch_iterator = 0 as *mut git_branch_iterator;
    if git_branch_iterator_new(&mut iter) < 0 {
        return -1;
    }
    memset(iter as *mut core::ffi::c_void, 0, 1);
    git_branch_iterator_free(iter);
    return 0;
}
"#,
        &[
            "let mut iter: *mut crate::git_branch_iterator",
            "memset(iter as *mut core::ffi::c_void, 0, 1);",
            "git_branch_iterator_free(iter);",
        ],
        &[
            "&mut [crate::git_branch_iterator]",
            "&mut [git_branch_iterator]",
        ],
    );
}

#[test]
fn test_pointer_output_call_keeps_local_storage_raw_with_mut_address() {
    run_test(
        r#"
pub unsafe fn set_slot(mut out: *mut *mut i32, mut value: *mut i32) {
    *out.offset(0) = value;
}

pub unsafe fn caller(mut value: *mut i32, idx: usize) -> i32 {
    let mut p: *mut i32 = value;
    set_slot(&mut p, value);
    return *p.offset(idx as isize);
}
"#,
        &[
            "pub unsafe fn set_slot(mut out: &mut [*mut i32]",
            "let mut p: *mut i32",
            "set_slot(std::slice::from_mut(&mut (p))",
        ],
        &[
            "let mut p: &mut [i32]",
            "std::slice::from_raw_parts_mut(&raw mut (p) as *mut _",
            "&raw mut (p) as",
        ],
    );
}

#[test]
fn test_pointer_output_call_keeps_local_storage_raw_with_raw_mut_address() {
    run_test(
        r#"
pub unsafe fn set_slot(mut out: *mut *mut i32, mut value: *mut i32) {
    *out.offset(0) = value;
}

pub unsafe fn caller(mut value: *mut i32, idx: usize) -> i32 {
    let mut p: *mut i32 = value;
    set_slot(&raw mut p, value);
    return *p.offset(idx as isize);
}
"#,
        &[
            "pub unsafe fn set_slot(mut out: &mut [*mut i32]",
            "let mut p: *mut i32",
            "set_slot(std::slice::from_mut(&mut (p))",
        ],
        &[
            "let mut p: &mut [i32]",
            "std::slice::from_raw_parts_mut(&raw mut (p) as *mut _",
            "&raw mut (p) as",
        ],
    );
}

#[test]
fn test_pointer_output_wrapper_keeps_forwarded_local_storage_raw() {
    run_test(
        r#"
pub unsafe fn set_slot(mut out: *mut *mut i32, mut value: *mut i32) {
    *out.offset(0) = value;
}

pub unsafe fn forward(mut out: *mut *mut i32, mut value: *mut i32) {
    set_slot(out, value);
}

pub unsafe fn caller(mut value: *mut i32, idx: usize) -> i32 {
    let mut p: *mut i32 = value;
    forward(&mut p, value);
    return *p.offset(idx as isize);
}
"#,
        &[
            "pub unsafe fn set_slot(mut out: &mut [*mut i32]",
            "pub unsafe fn forward(mut out: &mut [*mut i32]",
            "let mut p: *mut i32",
            "forward(std::slice::from_mut(&mut (p))",
        ],
        &[
            "let mut p: &mut [i32]",
            "std::slice::from_raw_parts_mut(&raw mut (p) as *mut _",
            "&raw mut (p) as",
        ],
    );
}

#[test]
fn test_pointer_output_alias_call_keeps_local_storage_raw() {
    run_test(
        r#"
pub unsafe fn set_slot(mut out: *mut *mut i32, mut value: *mut i32) {
    *out.offset(0) = value;
}

pub unsafe fn caller(mut value: *mut i32, idx: usize) -> i32 {
    let mut p: *mut i32 = value;
    let out: *mut *mut i32 = &raw mut p;
    set_slot(out, value);
    return *p.offset(idx as isize);
}
"#,
        &[
            "pub unsafe fn set_slot(mut out: &mut [*mut i32]",
            "let mut p: *mut i32",
            "set_slot(",
        ],
        &[
            "let mut p: &mut [i32]",
            "std::slice::from_raw_parts_mut(&raw mut (p) as *mut _",
            "&raw mut (p) as",
        ],
    );
}

#[test]
fn test_pointer_output_call_keeps_caller_parameter_storage_raw() {
    run_test(
        r#"
pub unsafe fn set_slot(mut out: *mut *mut i32, mut value: *mut i32) {
    *out.offset(0) = value;
}

pub unsafe fn caller(mut p: *mut i32, mut value: *mut i32, idx: usize) -> i32 {
    set_slot(&mut p, value);
    return *p.offset(idx as isize);
}
"#,
        &[
            "pub unsafe fn set_slot(mut out: &mut [*mut i32]",
            "pub unsafe fn caller(mut p: *mut i32",
            "set_slot(std::slice::from_mut(&mut (p))",
        ],
        &[
            "pub unsafe fn caller(mut p: &mut [i32]",
            "std::slice::from_raw_parts_mut(&raw mut (p) as *mut _",
            "&raw mut (p) as",
        ],
    );
}

#[test]
fn test_pointer_output_fn_ptr_call_keeps_local_storage_raw() {
    run_test(
        r#"
pub unsafe fn set_slot(mut out: *mut *mut i32, mut value: *mut i32) {
    *out.offset(0) = value;
}

pub unsafe fn caller(mut value: *mut i32, idx: usize) -> i32 {
    let cb: unsafe fn(*mut *mut i32, *mut i32) = set_slot;
    let mut p: *mut i32 = value;
    cb(&mut p, value);
    return *p.offset(idx as isize);
}
"#,
        &[
            "pub unsafe fn set_slot(mut out: &mut [*mut i32]",
            "let mut p: *mut i32",
            "std::slice::from_mut(&mut (p))",
        ],
        &[
            "let mut p: &mut [i32]",
            "std::slice::from_raw_parts_mut(&raw mut (p) as *mut _",
            "&raw mut (p) as",
        ],
    );
}

#[test]
fn test_pointer_output_storage_c_void_raw_mut_address_keeps_slice_local_raw() {
    run_test(
        r#"
pub unsafe fn overwrite_slot(mut payload: *mut core::ffi::c_void, mut value: *mut i32) {
    let slot: *mut *mut i32 = payload as *mut *mut i32;
    *slot = value;
}

pub unsafe fn caller(mut value: *mut i32, idx: usize) -> i32 {
    let mut p: *mut i32 = value;
    overwrite_slot(&raw mut p as *mut core::ffi::c_void, value);
    return *p.offset(idx as isize);
}
"#,
        &["let mut p: *mut i32", "return *p.offset(idx as isize);"],
        &[
            "let mut p: &mut [i32]",
            "let mut p: &[i32]",
            "crate::slice_cursor::SliceCursor",
        ],
    );
}

#[test]
fn test_pointer_output_storage_c_void_mut_address_cast_keeps_slice_local_raw() {
    run_test(
        r#"
pub unsafe fn overwrite_slot(mut payload: *mut core::ffi::c_void, mut value: *mut i32) {
    let slot: *mut *mut i32 = payload as *mut *mut i32;
    *slot = value;
}

pub unsafe fn caller(mut value: *mut i32, idx: usize) -> i32 {
    let mut p: *mut i32 = value;
    overwrite_slot(&mut p as *mut *mut i32 as *mut core::ffi::c_void, value);
    return *p.offset(idx as isize);
}
"#,
        &["let mut p: *mut i32", "return *p.offset(idx as isize);"],
        &[
            "let mut p: &mut [i32]",
            "let mut p: &[i32]",
            "crate::slice_cursor::SliceCursor",
        ],
    );
}

#[test]
fn test_pointer_output_storage_c_void_raw_mut_address_keeps_cursor_local_raw() {
    run_test(
        r#"
pub unsafe fn overwrite_slot(mut payload: *mut core::ffi::c_void, mut value: *mut i32) {
    let slot: *mut *mut i32 = payload as *mut *mut i32;
    *slot = value;
}

pub unsafe fn caller(mut value: *mut i32) -> i32 {
    let mut data: [i32; 4] = [1, 2, 3, 4];
    let mut p: *mut i32 = data.as_mut_ptr().offset(3);
    overwrite_slot(&raw mut p as *mut core::ffi::c_void, value);
    return *p.offset(-1);
}
"#,
        &["let mut p: *mut i32", "return *p.offset(-1);"],
        &[
            "let mut p: &mut [i32]",
            "let mut p: &[i32]",
            "crate::slice_cursor::SliceCursor",
        ],
    );
}

#[test]
fn test_pointer_output_storage_c_void_alias_keeps_slice_local_raw() {
    run_test(
        r#"
pub unsafe fn overwrite_slot(mut payload: *mut core::ffi::c_void, mut value: *mut i32) {
    let slot: *mut *mut i32 = payload as *mut *mut i32;
    *slot = value;
}

pub unsafe fn caller(mut value: *mut i32, idx: usize) -> i32 {
    let mut p: *mut i32 = value;
    let payload: *mut core::ffi::c_void = &raw mut p as *mut core::ffi::c_void;
    overwrite_slot(payload, value);
    return *p.offset(idx as isize);
}
"#,
        &[
            "let mut p: *mut i32",
            "payload: *mut",
            "return *p.offset(idx as isize);",
        ],
        &[
            "let mut p: &mut [i32]",
            "let mut p: &[i32]",
            "crate::slice_cursor::SliceCursor",
        ],
    );
}

#[test]
fn test_pointer_output_storage_c_void_raw_mut_address_keeps_slice_param_raw() {
    run_test(
        r#"
pub unsafe fn overwrite_slot(mut payload: *mut core::ffi::c_void, mut value: *mut i32) {
    let slot: *mut *mut i32 = payload as *mut *mut i32;
    *slot = value;
}

pub unsafe fn caller(mut p: *mut i32, mut value: *mut i32, idx: usize) -> i32 {
    overwrite_slot(&raw mut p as *mut core::ffi::c_void, value);
    return *p.offset(idx as isize);
}
"#,
        &[
            "pub unsafe fn caller(mut p: *mut i32",
            "return *p.offset(idx as isize);",
        ],
        &[
            "pub unsafe fn caller(mut p: &mut [i32]",
            "pub unsafe fn caller(mut p: &[i32]",
            "crate::slice_cursor::SliceCursor",
        ],
    );
}

#[test]
fn test_pointer_output_storage_c_void_address_does_not_demote_scalar_ref_local() {
    run_test(
        r#"
pub unsafe fn read_slot(mut payload: *mut core::ffi::c_void) -> i32 {
    let slot: *mut *mut i32 = payload as *mut *mut i32;
    return **slot;
}

pub unsafe fn caller() -> i32 {
    let mut value: i32 = 1;
    let mut p: *mut i32 = &mut value;
    let seen = read_slot(&raw mut p as *mut core::ffi::c_void);
    *p = seen + 1;
    return *p;
}
"#,
        &["let mut p: &mut i32", "read_slot(&raw mut (p)"],
        &["let mut p: *mut i32", "let mut p: &mut [i32]"],
    );
}

#[test]
fn test_pointer_output_storage_c_void_address_does_not_demote_scalar_opt_ref_local() {
    run_test(
        r#"
pub unsafe fn read_slot(mut payload: *mut core::ffi::c_void) -> i32 {
    let slot: *mut *mut i32 = payload as *mut *mut i32;
    if (*slot).is_null() {
        return 0;
    }
    return **slot;
}

pub unsafe fn caller(mut value: *mut i32) -> i32 {
    let mut p: *mut i32 = value;
    let seen = read_slot(&raw mut p as *mut core::ffi::c_void);
    if p.is_null() {
        return seen;
    }
    *p += seen;
    return *p;
}
"#,
        &["let mut p: Option<&mut i32>", "read_slot(&raw mut (p)"],
        &["let mut p: *mut i32", "let mut p: &mut [i32]"],
    );
}

#[test]
fn test_wide_storage_address_taken_does_not_demote_pointee_address() {
    run_test(
        r#"
pub unsafe fn caller(idx: usize) -> i32 {
    let mut data: [i32; 4] = [1, 2, 3, 4];
    let mut p: *mut i32 = data.as_mut_ptr();
    let q: *mut i32 = &mut *p;
    *p.offset(idx as isize) = *q;
    return *p.offset(idx as isize);
}
"#,
        &["let mut p: &mut [i32]"],
        &["let mut p: *mut i32"],
    );
}

#[test]
fn test_wide_storage_address_taken_does_not_demote_raw_pointee_address() {
    run_test(
        r#"
pub unsafe fn caller(idx: usize) -> i32 {
    let mut data: [i32; 4] = [1, 2, 3, 4];
    let mut p: *mut i32 = data.as_mut_ptr();
    let q: *mut i32 = &raw mut *p;
    *p.offset(idx as isize) = *q;
    return *p.offset(idx as isize);
}
"#,
        &["let mut p: &mut [i32]"],
        &["let mut p: *mut i32"],
    );
}

#[test]
fn test_section4_keeps_opaque_foreign_api_handle_raw() {
    run_test(
        r#"
#![feature(extern_types)]

extern "C" {
    pub type __dirstream;
    pub fn memset(dst: *mut core::ffi::c_void, value: i32, len: usize) -> *mut core::ffi::c_void;
    pub fn open_dir() -> *mut DIR;
    pub fn read_dir(dir: *mut DIR) -> i32;
    pub fn close_dir(dir: *mut DIR) -> i32;
}

pub type DIR = __dirstream;

pub unsafe extern "C" fn scan_dir() -> i32 {
    let mut dir: *mut DIR = open_dir();
    if dir.is_null() {
        return -1;
    }
    memset(dir as *mut core::ffi::c_void, 0, 1);
    if read_dir(dir) < 0 {
        close_dir(dir);
        return -1;
    }
    return close_dir(dir);
}
"#,
        &[
            "let mut dir: *mut crate::__dirstream",
            "memset(dir as *mut core::ffi::c_void, 0, 1);",
            "read_dir(dir)",
            "close_dir(dir)",
        ],
        &["&mut [crate::__dirstream]", "&mut [__dirstream]"],
    );
}

#[test]
fn test_section4_keeps_opaque_pcre_match_data_raw() {
    run_test(
        r#"
#![feature(extern_types)]

extern "C" {
    pub type pcre2_real_match_data_8;
    pub fn memset(dst: *mut core::ffi::c_void, value: i32, len: usize) -> *mut core::ffi::c_void;
    pub fn pcre2_match_data_create_8(count: u32) -> *mut pcre2_match_data_8;
    pub fn pcre2_match_8(data: *mut pcre2_match_data_8) -> i32;
    pub fn pcre2_match_data_free_8(data: *mut pcre2_match_data_8);
}

pub type pcre2_match_data_8 = pcre2_real_match_data_8;

pub unsafe extern "C" fn git_regexp_match(mut count: u32) -> i32 {
    let mut data: *mut pcre2_match_data_8 = 0 as *mut pcre2_match_data_8;
    data = pcre2_match_data_create_8(count);
    if data.is_null() {
        return -1;
    }
    memset(data as *mut core::ffi::c_void, 0, 1);
    let mut error = pcre2_match_8(data);
    pcre2_match_data_free_8(data);
    return error;
}
"#,
        &[
            "let mut data: *mut crate::pcre2_real_match_data_8",
            "memset(data as *mut core::ffi::c_void, 0, 1);",
            "pcre2_match_8(data)",
            "pcre2_match_data_free_8(data)",
        ],
        &[
            "&mut [crate::pcre2_match_data_8]",
            "&mut [pcre2_match_data_8]",
            "&mut [crate::pcre2_real_match_data_8]",
            "&mut [pcre2_real_match_data_8]",
        ],
    );
}

#[test]
fn test_ordinary_call_in_anon_const_does_not_enter_fn_ptr_callee_fallback() {
    run_test(
        r#"
pub unsafe fn foo() -> i32 {
    let values: [i32; core::mem::size_of::<i32>()] = [1; core::mem::size_of::<i32>()];
    return values[0];
}
"#,
        &["core::mem::size_of::<i32>()"],
        &[],
    );
}

#[test]
fn test_root1_fn_ptr_raw_boundary_field_storage_forces_callback_raw() {
    run_test(
        r#"
pub type emit_func_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

#[repr(C)]
pub struct Callbacks {
    pub cb: emit_func_t,
}

unsafe extern "C" {
    pub fn install_callbacks(callbacks: *const Callbacks) -> i32;
}

pub unsafe extern "C" fn emit_one(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 1;
}

pub unsafe fn register_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let callbacks = Callbacks {
        cb: Some(emit_one as unsafe extern "C" fn(*mut *mut i8) -> i32),
    };
    return install_callbacks(&callbacks) + emit_one(argv);
}
"#,
        &[
            "type emit_func_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "fn emit_one(mut argv: *mut *mut i8) -> i32",
            "emit_one as unsafe extern \"C\" fn(*mut *mut i8) -> i32",
        ],
        &[
            "type emit_func_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "fn emit_one(mut argv: &mut [*mut i8]) -> i32",
            "emit_one as unsafe extern \"C\" fn(&mut [*mut i8]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_alias_option_associated_unwrap_uses_alias_contract() {
    run_test(
        r#"
pub type emit_func_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

pub unsafe extern "C" fn emit_one(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub static EMIT: emit_func_t =
    Some(emit_one as unsafe extern "C" fn(*mut *mut i8) -> i32);

pub unsafe fn dispatch_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return Option::unwrap(EMIT)(argv);
}
"#,
        &[
            "type emit_func_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "fn emit_one(mut argv: &mut [*mut i8]) -> i32",
        ],
        &[
            "type emit_func_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "emit_one as unsafe extern \"C\" fn(*mut *mut i8) -> i32",
            "Option::unwrap(EMIT)((argv).as_mut_ptr())",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_struct_fields_associated_expect_use_field_contract() {
    run_test(
        r#"
pub type emit_func_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

#[repr(C)]
pub struct Callbacks {
    pub emit: emit_func_t,
    pub fallback: Option<unsafe extern "C" fn(*mut *mut i8) -> i32>,
}

pub unsafe extern "C" fn emit_one(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub static CALLBACKS: Callbacks = Callbacks {
    emit: Some(emit_one as unsafe extern "C" fn(*mut *mut i8) -> i32),
    fallback: Some(emit_one as unsafe extern "C" fn(*mut *mut i8) -> i32),
};

pub unsafe fn dispatch_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return Option::expect(CALLBACKS.emit, "emit")(argv)
        + Option::unwrap(CALLBACKS.fallback)(argv);
}
"#,
        &[
            "type emit_func_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "pub emit: emit_func_t",
            "pub fallback: Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
        ],
        &[
            "Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "emit_one as unsafe extern \"C\" fn(*mut *mut i8) -> i32",
            "Option::expect(CALLBACKS.emit, \"emit\")((argv).as_mut_ptr())",
            "Option::unwrap(CALLBACKS.fallback)((argv).as_mut_ptr())",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_typedef_option_local_param_associated_expect_uses_contract() {
    run_test(
        r#"
pub type emit_func_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

pub unsafe extern "C" fn emit_one(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe fn invoke_emit(
    cb: emit_func_t,
    mut argv: *mut *mut i8,
) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return Option::expect(cb, "emit")(argv);
}

pub unsafe fn dispatch_emit(mut argv: *mut *mut i8) -> i32 {
    return invoke_emit(
        Some(emit_one as unsafe extern "C" fn(*mut *mut i8) -> i32),
        argv,
    );
}
"#,
        &[
            "type emit_func_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "cb: emit_func_t",
        ],
        &[
            "type emit_func_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "emit_one as unsafe extern \"C\" fn(*mut *mut i8) -> i32",
            "Option::expect(cb, \"emit\")((argv).as_mut_ptr())",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_typedef_option_local_copy_associated_unwrap_uses_contract() {
    run_test(
        r#"
pub type emit_func_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

#[repr(C)]
pub struct Callbacks {
    pub emit: emit_func_t,
}

pub unsafe extern "C" fn emit_one(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub static CALLBACKS: Callbacks = Callbacks {
    emit: Some(emit_one as unsafe extern "C" fn(*mut *mut i8) -> i32),
};

pub unsafe fn dispatch_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let cb: emit_func_t = CALLBACKS.emit;
    return Option::unwrap(cb)(argv);
}
"#,
        &[
            "type emit_func_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "pub emit: emit_func_t",
        ],
        &[
            "type emit_func_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "emit_one as unsafe extern \"C\" fn(*mut *mut i8) -> i32",
            "Option::unwrap(cb)((argv).as_mut_ptr())",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_if_initializer_condition_raw_field_does_not_pollute_branch_contract() {
    run_test(
        r#"
pub type raw_probe_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;
pub type local_emit_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

#[repr(C)]
pub struct RawCallbacks {
    pub probe: raw_probe_t,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub static RAW_CALLBACKS: RawCallbacks = RawCallbacks { probe: None };

pub unsafe extern "C" fn local_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe fn choose_and_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let emit: local_emit_t = if RAW_CALLBACKS.probe.is_some() {
        Some(local_emit as unsafe extern "C" fn(*mut *mut i8) -> i32)
    } else {
        Some(local_emit as unsafe extern "C" fn(*mut *mut i8) -> i32)
    };
    return install_raw_callbacks(&RAW_CALLBACKS) + emit.expect("emit")(argv);
}
"#,
        &[
            "type raw_probe_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "type local_emit_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "fn local_emit(mut argv: &mut [*mut i8]) -> i32",
        ],
        &[
            "type raw_probe_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "type local_emit_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "emit.expect(\"emit\")((argv).as_mut_ptr())",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_match_scrutinee_raw_field_does_not_pollute_arm_contract() {
    run_test(
        r#"
pub type raw_probe_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;
pub type local_emit_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

#[repr(C)]
pub struct RawCallbacks {
    pub probe: raw_probe_t,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub static RAW_CALLBACKS: RawCallbacks = RawCallbacks { probe: None };

pub unsafe extern "C" fn local_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe fn choose_and_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let emit: local_emit_t = match RAW_CALLBACKS.probe {
        Some(_) => Some(local_emit as unsafe extern "C" fn(*mut *mut i8) -> i32),
        None => Some(local_emit as unsafe extern "C" fn(*mut *mut i8) -> i32),
    };
    return install_raw_callbacks(&RAW_CALLBACKS) + emit.expect("emit")(argv);
}
"#,
        &[
            "type raw_probe_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "type local_emit_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "fn local_emit(mut argv: &mut [*mut i8]) -> i32",
        ],
        &[
            "type raw_probe_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "type local_emit_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "emit.expect(\"emit\")((argv).as_mut_ptr())",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_block_statement_raw_field_does_not_pollute_tail_contract() {
    run_test(
        r#"
pub type raw_probe_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;
pub type local_emit_t = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

#[repr(C)]
pub struct RawCallbacks {
    pub probe: raw_probe_t,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub static RAW_CALLBACKS: RawCallbacks = RawCallbacks { probe: None };

pub unsafe extern "C" fn local_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe fn choose_and_emit(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let emit: local_emit_t = {
        let _seen = RAW_CALLBACKS.probe.is_some();
        Some(local_emit as unsafe extern "C" fn(*mut *mut i8) -> i32)
    };
    return install_raw_callbacks(&RAW_CALLBACKS) + emit.expect("emit")(argv);
}
"#,
        &[
            "type raw_probe_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "type local_emit_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "fn local_emit(mut argv: &mut [*mut i8]) -> i32",
        ],
        &[
            "type raw_probe_t = Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
            "type local_emit_t = Option<unsafe extern \"C\" fn(*mut *mut i8) -> i32>",
            "emit.expect(\"emit\")((argv).as_mut_ptr())",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_nested_raw_outer_definition_forces_inner_callback_table_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Iterator {
    pub value: i32,
}

pub type each_cb = Option<unsafe extern "C" fn(*mut Iterator) -> i32>;

#[repr(C)]
pub struct InnerCallbacks {
    pub each: each_cb,
}

#[repr(C)]
pub struct OuterDefinition {
    pub callbacks: InnerCallbacks,
}

unsafe extern "C" {
    pub fn register_outer_definition(definition: *const OuterDefinition) -> i32;
}

pub unsafe extern "C" fn local_each(mut iter: *mut Iterator) -> i32 {
    (*iter.offset(0)).value += 1;
    return (*iter.offset(0)).value;
}

pub static mut OUTER_DEFINITION: OuterDefinition = OuterDefinition {
    callbacks: InnerCallbacks {
        each: Some(local_each as unsafe extern "C" fn(*mut Iterator) -> i32),
    },
};

pub unsafe fn register_outer() -> i32 {
    return register_outer_definition(&raw const OUTER_DEFINITION);
}
"#,
        &[
            "type each_cb = Option<unsafe extern \"C\" fn(*mut Iterator) -> i32>",
            "pub each: each_cb",
            "fn local_each(mut iter: *mut crate::Iterator) -> i32",
            "local_each as",
            "unsafe extern \"C\" fn(*mut Iterator) -> i32",
        ],
        &[
            "type each_cb = Option<unsafe extern \"C\" fn(&mut [crate::Iterator]) -> i32>",
            "fn local_each(mut iter: &mut [crate::Iterator]) -> i32",
            "local_each as unsafe extern \"C\" fn(&mut [crate::Iterator]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_shared_callback_field_raw_merge_forces_slice_entry_cast_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub id: i32,
}

#[repr(C)]
pub struct Iterator {
    pub current: *const Entry,
    pub position: i32,
}

#[repr(C)]
pub struct IteratorCallbacks {
    pub current: Option<unsafe extern "C" fn(*mut *const Entry, *mut Iterator) -> i32>,
}

unsafe extern "C" {
    pub fn keep_raw_iterator(iter: *mut Iterator) -> i32;
}

pub unsafe extern "C" fn slice_current(
    mut out: *mut *const Entry,
    mut iter: *mut Iterator,
) -> i32 {
    *out.offset(0) = (*iter.offset(0)).current;
    return (*iter.offset(0)).position;
}

pub unsafe extern "C" fn raw_current(
    mut out: *mut *const Entry,
    mut iter: *mut Iterator,
) -> i32 {
    *out.offset(0) = core::ptr::null();
    return keep_raw_iterator(iter);
}

pub static SLICE_CALLBACKS: IteratorCallbacks = IteratorCallbacks {
    current: Some(
        slice_current as unsafe extern "C" fn(*mut *const Entry, *mut Iterator) -> i32,
    ),
};

pub static RAW_CALLBACKS: IteratorCallbacks = IteratorCallbacks {
    current: Some(
        raw_current as unsafe extern "C" fn(*mut *const Entry, *mut Iterator) -> i32,
    ),
};

pub unsafe fn call_both(
    mut out: *mut *const Entry,
    mut iter: *mut Iterator,
) -> i32 {
    *out.offset(0) = core::ptr::null();
    let first = SLICE_CALLBACKS.current.expect("slice")(out, iter);
    let second = RAW_CALLBACKS.current.expect("raw")(out, iter);
    return first + second;
}
"#,
        &[
            "*mut Iterator<'a>) -> i32>",
            "mut iter: *mut crate::Iterator<'a>",
        ],
        &[
            "slice_current as unsafe extern \"C\" fn(&mut [*const Entry], &[Iterator]) -> i32",
            "slice_current as unsafe extern \"C\" fn(&mut [*const Entry], &mut [Iterator]) -> i32",
            "slice_current as\n                unsafe extern \"C\" fn(&mut [*const Entry], &[Iterator<'_>])",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_local_static_callback_field_raw_merge_forces_slice_entry_cast_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub id: i32,
}

#[repr(C)]
pub struct Iterator {
    pub current: *const Entry,
    pub position: i32,
}

#[repr(C)]
pub struct IteratorCallbacks {
    pub current: Option<unsafe extern "C" fn(*mut *const Entry, *mut Iterator) -> i32>,
}

unsafe extern "C" {
    pub fn keep_raw_iterator(iter: *mut Iterator) -> i32;
}

pub unsafe extern "C" fn slice_current(
    mut out: *mut *const Entry,
    mut iter: *mut Iterator,
) -> i32 {
    *out.offset(0) = (*iter.offset(0)).current;
    return (*iter.offset(0)).position;
}

pub unsafe extern "C" fn raw_current(
    mut out: *mut *const Entry,
    mut iter: *mut Iterator,
) -> i32 {
    *out.offset(0) = core::ptr::null();
    return keep_raw_iterator(iter);
}

pub unsafe fn call_local_tables(
    mut out: *mut *const Entry,
    mut iter: *mut Iterator,
) -> i32 {
    static mut SLICE_CALLBACKS: IteratorCallbacks = IteratorCallbacks {
        current: Some(
            slice_current as unsafe extern "C" fn(*mut *const Entry, *mut Iterator) -> i32,
        ),
    };
    static mut RAW_CALLBACKS: IteratorCallbacks = IteratorCallbacks {
        current: Some(
            raw_current as unsafe extern "C" fn(*mut *const Entry, *mut Iterator) -> i32,
        ),
    };
    *out.offset(0) = core::ptr::null();
    let first = SLICE_CALLBACKS.current.expect("slice")(out, iter);
    let second = RAW_CALLBACKS.current.expect("raw")(out, iter);
    return first + second;
}
"#,
        &[
            "*mut Iterator<'a>) -> i32>",
            "mut iter: *mut crate::Iterator<'a>",
        ],
        &[
            "slice_current as unsafe extern \"C\" fn(&mut [*const Entry], &[Iterator]) -> i32",
            "slice_current as unsafe extern \"C\" fn(&mut [*const Entry], &mut [Iterator]) -> i32",
            "slice_current as\n                    unsafe extern \"C\" fn(&mut [*const Entry], &[Iterator<'_>])",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_global_raw_item_callback_table_forces_callback_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct RawCallbacks {
    pub reset: Option<unsafe extern "C" fn(*mut Item) -> i32>,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub unsafe extern "C" fn reset_item(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value = 0;
    return (*item.offset(0)).value;
}

pub static RAW_CALLBACKS: RawCallbacks = RawCallbacks {
    reset: Some(reset_item as unsafe extern "C" fn(*mut Item) -> i32),
};

pub unsafe fn register_raw_callbacks() -> i32 {
    return install_raw_callbacks(&RAW_CALLBACKS);
}
"#,
        &[
            "pub reset: Option<unsafe extern \"C\" fn(*mut Item) -> i32>",
            "fn reset_item(mut item: *mut crate::Item) -> i32",
            "reset_item as unsafe extern \"C\" fn(*mut Item) -> i32",
        ],
        &[
            "pub reset: Option<unsafe extern \"C\" fn(&mut [Item]) -> i32>",
            "fn reset_item(mut item: &mut [crate::Item]) -> i32",
            "reset_item as unsafe extern \"C\" fn(&mut [Item]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_local_static_raw_item_callback_table_forces_callback_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct RawCallbacks {
    pub reset: Option<unsafe extern "C" fn(*mut Item) -> i32>,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub unsafe extern "C" fn reset_item(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value = 0;
    return (*item.offset(0)).value;
}

pub unsafe fn register_local_raw_callbacks() -> i32 {
    static mut RAW_CALLBACKS: RawCallbacks = RawCallbacks {
        reset: Some(reset_item as unsafe extern "C" fn(*mut Item) -> i32),
    };
    return install_raw_callbacks(&raw const RAW_CALLBACKS);
}
"#,
        &[
            "pub reset: Option<unsafe extern \"C\" fn(*mut Item) -> i32>",
            "fn reset_item(mut item: *mut crate::Item) -> i32",
            "reset_item as unsafe extern \"C\" fn(*mut Item) -> i32",
        ],
        &[
            "pub reset: Option<unsafe extern \"C\" fn(&mut [Item]) -> i32>",
            "fn reset_item(mut item: &mut [crate::Item]) -> i32",
            "reset_item as unsafe extern \"C\" fn(&mut [Item]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_multi_field_raw_reset_free_keeps_only_raw_default_callbacks_raw() {
    run_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub id: i32,
}

#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct IteratorCallbacks {
    pub current: Option<unsafe extern "C" fn(*mut *const Entry, *mut Item) -> i32>,
    pub reset: Option<unsafe extern "C" fn(*mut Item) -> i32>,
    pub free: Option<unsafe extern "C" fn(*mut Item)>,
}

unsafe extern "C" {
    pub fn install_raw_reset(reset: Option<unsafe extern "C" fn(*mut Item) -> i32>) -> i32;
    pub fn install_raw_free(free: Option<unsafe extern "C" fn(*mut Item)>);
}

pub unsafe extern "C" fn set_current(
    mut out: *mut *const Entry,
    mut item: *mut Item,
) -> i32 {
    *out.offset(0) = core::ptr::null();
    (*item.offset(0)).value += 1;
    return (*item.offset(0)).value;
}

pub unsafe extern "C" fn reset_item(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value = 0;
    return (*item.offset(0)).value;
}

pub unsafe extern "C" fn free_item(mut item: *mut Item) {
    (*item.offset(0)).value = -1;
}

pub static CALLBACKS: IteratorCallbacks = IteratorCallbacks {
    current: Some(
        set_current as unsafe extern "C" fn(*mut *const Entry, *mut Item) -> i32,
    ),
    reset: Some(reset_item as unsafe extern "C" fn(*mut Item) -> i32),
    free: Some(free_item as unsafe extern "C" fn(*mut Item)),
};

pub unsafe fn dispatch_callbacks(
    mut out: *mut *const Entry,
    mut item: *mut Item,
) -> i32 {
    *out.offset(0) = core::ptr::null();
    let result = CALLBACKS.current.expect("current")(out, item);
    install_raw_free(CALLBACKS.free);
    return result + install_raw_reset(CALLBACKS.reset);
}
"#,
        &[
            "fn set_current(mut out: &mut [*const crate::Entry]",
            "mut item: &mut [crate::Item]) -> i32",
            "pub reset: Option<unsafe extern \"C\" fn(*mut Item) -> i32>",
            "pub free: Option<unsafe extern \"C\" fn(*mut Item)>",
            "fn reset_item(mut item: *mut crate::Item) -> i32",
            "fn free_item(mut item: *mut crate::Item)",
            "reset_item as unsafe extern \"C\" fn(*mut Item) -> i32",
            "free_item as unsafe extern \"C\" fn(*mut Item)",
        ],
        &[
            "fn reset_item(mut item: &mut [crate::Item]) -> i32",
            "fn free_item(mut item: &mut [crate::Item])",
            "reset_item as unsafe extern \"C\" fn(&mut [Item]) -> i32",
            "free_item as unsafe extern \"C\" fn(&mut [Item])",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_raw_field_local_variable_initializer_pushes_back_to_callback() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct RawCallbacks {
    pub current: Option<unsafe extern "C" fn(*mut Item) -> i32>,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub unsafe extern "C" fn visit_item(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value += 1;
    return (*item.offset(0)).value;
}

pub unsafe fn register_from_local() -> i32 {
    let cb = Some(visit_item as unsafe extern "C" fn(*mut Item) -> i32);
    let callbacks = RawCallbacks { current: cb };
    return install_raw_callbacks(&callbacks);
}
"#,
        &[
            "pub current: Option<unsafe extern \"C\" fn(*mut Item) -> i32>",
            "fn visit_item(mut item: *mut crate::Item) -> i32",
            "visit_item as unsafe extern \"C\" fn(*mut Item) -> i32",
        ],
        &[
            "pub current: Option<unsafe extern \"C\" fn(&mut [Item]) -> i32>",
            "fn visit_item(mut item: &mut [crate::Item]) -> i32",
            "visit_item as unsafe extern \"C\" fn(&mut [Item]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_raw_field_assignment_from_local_variable_pushes_back_to_callback() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct RawCallbacks {
    pub current: Option<unsafe extern "C" fn(*mut Item) -> i32>,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub unsafe extern "C" fn visit_item(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value += 1;
    return (*item.offset(0)).value;
}

pub unsafe fn register_assigned_from_local() -> i32 {
    let cb = Some(visit_item as unsafe extern "C" fn(*mut Item) -> i32);
    let mut callbacks = RawCallbacks { current: None };
    callbacks.current = cb;
    return install_raw_callbacks(&callbacks);
}
"#,
        &[
            "pub current: Option<unsafe extern \"C\" fn(*mut Item) -> i32>",
            "fn visit_item(mut item: *mut crate::Item) -> i32",
            "visit_item as unsafe extern \"C\" fn(*mut Item) -> i32",
        ],
        &[
            "pub current: Option<unsafe extern \"C\" fn(&mut [Item]) -> i32>",
            "fn visit_item(mut item: &mut [crate::Item]) -> i32",
            "visit_item as unsafe extern \"C\" fn(&mut [Item]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_raw_field_direct_assignment_pushes_back_to_callback() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct RawCallbacks {
    pub current: Option<unsafe extern "C" fn(*mut Item) -> i32>,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub unsafe extern "C" fn visit_item(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value += 1;
    return (*item.offset(0)).value;
}

pub unsafe fn register_direct_assignment() -> i32 {
    let mut callbacks = RawCallbacks { current: None };
    callbacks.current = Some(visit_item as unsafe extern "C" fn(*mut Item) -> i32);
    return install_raw_callbacks(&callbacks);
}
"#,
        &[
            "pub current: Option<unsafe extern \"C\" fn(*mut Item) -> i32>",
            "fn visit_item(mut item: *mut crate::Item) -> i32",
            "visit_item as unsafe extern \"C\" fn(*mut Item) -> i32",
        ],
        &[
            "pub current: Option<unsafe extern \"C\" fn(&mut [Item]) -> i32>",
            "fn visit_item(mut item: &mut [crate::Item]) -> i32",
            "visit_item as unsafe extern \"C\" fn(&mut [Item]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_raw_field_rhs_block_does_not_force_unstored_callback() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct RawCallbacks {
    pub current: Option<unsafe extern "C" fn(*mut Item) -> i32>,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub unsafe extern "C" fn stored_item(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value += 1;
    return (*item.offset(0)).value;
}

pub unsafe extern "C" fn local_only(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value += 2;
    return (*item.offset(0)).value;
}

pub unsafe fn register_with_rhs_block(mut item: *mut Item) -> i32 {
    let callbacks = RawCallbacks {
        current: {
            let _seen = if Some(
                local_only as unsafe extern "C" fn(*mut Item) -> i32,
            )
            .is_some()
            {
                1
            } else {
                0
            };
            Some(stored_item as unsafe extern "C" fn(*mut Item) -> i32)
        },
    };
    return install_raw_callbacks(&callbacks) + local_only(item);
}
"#,
        &[
            "pub current: Option<unsafe extern \"C\" fn(*mut Item) -> i32>",
            "fn stored_item(mut item: *mut crate::Item) -> i32",
            "stored_item as unsafe extern \"C\" fn(*mut Item) -> i32",
            "fn local_only(mut item: &mut [crate::Item]) -> i32",
            "local_only as",
            "unsafe extern \"C\" fn(&mut [Item]) -> i32",
        ],
        &[
            "fn stored_item(mut item: &mut [crate::Item]) -> i32",
            "stored_item as unsafe extern \"C\" fn(&mut [Item]) -> i32",
            "fn local_only(mut item: *mut crate::Item) -> i32",
            "local_only as unsafe extern \"C\" fn(*mut Item) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_raw_field_type_alias_constructor_pushes_back_to_callback() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct RawCallbacks {
    pub current: Option<unsafe extern "C" fn(*mut Item) -> i32>,
}

pub type RawCallbacksAlias = RawCallbacks;

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: *const RawCallbacks) -> i32;
}

pub unsafe extern "C" fn visit_item(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value += 1;
    return (*item.offset(0)).value;
}

pub unsafe fn register_alias_constructor() -> i32 {
    let callbacks = RawCallbacksAlias {
        current: Some(visit_item as unsafe extern "C" fn(*mut Item) -> i32),
    };
    return install_raw_callbacks(&callbacks);
}
"#,
        &[
            "pub current: Option<unsafe extern \"C\" fn(*mut Item) -> i32>",
            "type RawCallbacksAlias = RawCallbacks",
            "fn visit_item(mut item: *mut crate::Item) -> i32",
            "visit_item as",
            "unsafe extern \"C\" fn(*mut Item) -> i32",
        ],
        &[
            "pub current: Option<unsafe extern \"C\" fn(&mut [Item]) -> i32>",
            "type RawCallbacksAlias = RawCallbacks<'",
            "fn visit_item(mut item: &mut [crate::Item]) -> i32",
            "visit_item as unsafe extern \"C\" fn(&mut [Item]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_raw_field_foreign_by_value_boundary_pushes_back_to_callback() {
    run_test(
        r#"
#[repr(C)]
pub struct Item {
    pub value: i32,
}

#[repr(C)]
pub struct RawCallbacks {
    pub current: Option<unsafe extern "C" fn(*mut Item) -> i32>,
}

unsafe extern "C" {
    pub fn install_raw_callbacks(callbacks: RawCallbacks) -> i32;
}

pub unsafe extern "C" fn visit_item(mut item: *mut Item) -> i32 {
    (*item.offset(0)).value += 1;
    return (*item.offset(0)).value;
}

pub unsafe fn register_by_value() -> i32 {
    let callbacks = RawCallbacks {
        current: Some(visit_item as unsafe extern "C" fn(*mut Item) -> i32),
    };
    return install_raw_callbacks(callbacks);
}
"#,
        &[
            "pub current: Option<unsafe extern \"C\" fn(*mut Item) -> i32>",
            "pub fn install_raw_callbacks(callbacks: RawCallbacks)",
            "fn visit_item(mut item: *mut crate::Item) -> i32",
            "visit_item as",
            "unsafe extern \"C\" fn(*mut Item) -> i32",
        ],
        &[
            "pub current: Option<unsafe extern \"C\" fn(&mut [Item]) -> i32>",
            "fn visit_item(mut item: &mut [crate::Item]) -> i32",
            "visit_item as unsafe extern \"C\" fn(&mut [Item]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_raw_field_helper_param_pushes_back_to_callback() {
    run_test(
        r#"
#[repr(C)]
pub struct DiffFile {
    pub flags: i32,
}

pub type git_diff_file_cb =
    Option<unsafe extern "C" fn(*mut DiffFile) -> i32>;

#[repr(C)]
pub struct DiffOutput {
    pub file_cb: git_diff_file_cb,
}

unsafe extern "C" {
    pub fn install_diff_output(out: *const DiffOutput) -> i32;
}

pub unsafe extern "C" fn patch_generated_file_cb(mut file: *mut DiffFile) -> i32 {
    (*file.offset(0)).flags += 1;
    return (*file.offset(0)).flags;
}

pub unsafe fn diff_output_init(
    mut out: *mut DiffOutput,
    file_cb: git_diff_file_cb,
) {
    (*out).file_cb = file_cb;
}

pub unsafe fn generate_patch_output() -> i32 {
    let mut out = DiffOutput { file_cb: None };
    diff_output_init(
        &raw mut out,
        Some(patch_generated_file_cb as unsafe extern "C" fn(*mut DiffFile) -> i32),
    );
    return install_diff_output(&raw const out);
}
"#,
        &[
            "type git_diff_file_cb =",
            "Option<unsafe extern \"C\" fn(*mut DiffFile) -> i32>",
            "pub file_cb: git_diff_file_cb",
            "file_cb: git_diff_file_cb",
            "fn patch_generated_file_cb",
            "mut file:",
            "*mut crate::DiffFile",
            "patch_generated_file_cb as",
            "unsafe extern \"C\" fn(*mut DiffFile) -> i32",
        ],
        &[
            "type git_diff_file_cb = Option<unsafe extern \"C\" fn(&mut [DiffFile]) -> i32>",
            "fn patch_generated_file_cb(mut file: &mut [crate::DiffFile]) -> i32",
            "unsafe extern \"C\" fn(&mut [DiffFile]) -> i32",
        ],
    );
}

#[test]
fn test_root1_fn_ptr_raw_field_result_return_pushes_back_to_callback_call() {
    run_test(
        r#"
#[repr(C)]
pub struct Transport {
    pub id: i32,
}

#[repr(C)]
pub struct Remote {
    pub hits: i32,
}

pub type git_transport_cb =
    Option<unsafe extern "C" fn(*mut *mut Transport, *mut Remote, *mut i32) -> i32>;

#[repr(C)]
pub struct TransportDefinition {
    pub callback: git_transport_cb,
}

unsafe extern "C" {
    pub fn register_transport_definition(definition: *const TransportDefinition) -> i32;
}

pub unsafe extern "C" fn local_transport_cb(
    mut out: *mut *mut Transport,
    mut owner: *mut Remote,
    mut param: *mut i32,
) -> i32 {
    *out.offset(0) = core::ptr::null_mut();
    (*owner.offset(0)).hits += *param.offset(0);
    return (*owner.offset(0)).hits;
}

pub static TRANSPORT_DEFINITION: TransportDefinition = TransportDefinition {
    callback: Some(
        local_transport_cb
            as unsafe extern "C" fn(*mut *mut Transport, *mut Remote, *mut i32) -> i32,
    ),
};

pub unsafe fn transport_find_fn() -> Result<git_transport_cb, i32> {
    register_transport_definition(&raw const TRANSPORT_DEFINITION);
    return Ok(TRANSPORT_DEFINITION.callback);
}

pub unsafe fn dispatch_transport(
    mut owner: *mut Remote,
    mut param: *mut i32,
) -> i32 {
    let mut out: *mut Transport = core::ptr::null_mut();
    let fn_0 = transport_find_fn().unwrap();
    return fn_0.expect("transport")(&mut out, owner, param);
}
"#,
        &[
            "type git_transport_cb =",
            "Option<unsafe extern \"C\" fn(*mut *mut Transport, *mut Remote,",
            "*mut i32)",
            "-> i32>",
            "pub callback: git_transport_cb",
            "Result<git_transport_cb, i32>",
            "fn local_transport_cb",
            "mut out:",
            "*mut *mut crate::Transport",
            "mut owner: *mut crate::Remote",
            "mut param: *mut i32",
            "local_transport_cb as",
            "unsafe extern \"C\" fn(*mut *mut Transport, *mut Remote,",
            "*mut i32) -> i32",
            "let mut out: *mut crate::Transport",
            "fn_0.expect(\"transport\")",
        ],
        &[
            "type git_transport_cb = Option<unsafe extern \"C\" fn(&mut [*mut Transport]",
            "fn local_transport_cb(mut out: &mut [*mut crate::Transport]",
            "mut owner: &mut [crate::Remote]",
            "mut param: &mut [i32]",
            "let mut out: &mut [crate::Transport]",
            "as_mut_ptr()",
            "&raw mut (out) as",
        ],
    );
}

#[test]
fn test_root2_cursor_cast_field_const_offset_reads_typecheck() {
    run_test(
        r#"
#[repr(C)]
pub struct Header {
    pub signature: u32,
    pub version: u32,
}

pub unsafe fn read_header_fields(mut data: *const u8, idx: isize) -> u32 {
    let signature = (*((data).offset(idx) as *const Header)).signature;
    let version = (*((data).offset(idx) as *const Header)).version;
    return signature.wrapping_add(version);
}
"#,
        &["fn read_header_fields", "signature", "version"],
        &[
            "[(idx) as isize].signature",
            "[(idx) as isize].version",
            "[(idx) as usize].signature",
            "[(idx) as usize].version",
        ],
    );
}

#[test]
fn test_root2_cursor_cast_field_option_unwrap_reads_typecheck() {
    run_test(
        r#"
#[repr(C)]
pub struct Header {
    pub signature: u32,
    pub flags: u32,
}

pub unsafe fn read_optional_header(mut data: *const u8, hdr_idx: Option<isize>) -> u32 {
    if hdr_idx.is_none() {
        return 0;
    }
    let signature = (*((data).offset(hdr_idx.unwrap()) as *const Header)).signature;
    let flags = (*((data).offset(hdr_idx.unwrap()) as *const Header)).flags;
    return signature ^ flags;
}
"#,
        &["fn read_optional_header", "signature", "flags"],
        &[
            "[(hdr_idx.unwrap()) as isize].signature",
            "[(hdr_idx.unwrap()) as isize].flags",
            "[(hdr_idx.unwrap()) as usize].signature",
            "[(hdr_idx.unwrap()) as usize].flags",
        ],
    );
}

#[test]
fn test_root2_cursor_cast_field_mut_offset_write_typecheck() {
    run_test(
        r#"
#[repr(C)]
pub struct Header {
    pub signature: u32,
    pub version: u32,
}

pub unsafe fn write_header_version(mut data: *mut u8, idx: isize) -> u32 {
    (*((data).offset(idx) as *mut Header)).version = 2;
    return (*((data).offset(idx) as *mut Header)).version;
}
"#,
        &["fn write_header_version", "version"],
        &[
            "[(idx) as isize].version = 2",
            "[(idx) as isize].version",
            "[(idx) as usize].version = 2",
            "[(idx) as usize].version",
        ],
    );
}

#[test]
fn test_root2_cursor_cast_field_nonzero_repeated_offset_reads_typecheck() {
    run_test(
        r#"
#[repr(C)]
pub struct Header {
    pub signature: u32,
    pub length: u32,
}

pub unsafe fn read_later_header_twice(mut data: *const u8, idx: isize) -> u32 {
    let hdr_off = idx + 8isize;
    let signature = (*((data).offset(hdr_off) as *const Header)).signature;
    let length = (*((data).offset(hdr_off) as *const Header)).length;
    return signature.wrapping_add(length);
}
"#,
        &["fn read_later_header_twice", "signature", "length"],
        &[
            "[(hdr_off) as isize].signature",
            "[(hdr_off) as isize].length",
            "[(hdr_off) as usize].signature",
            "[(hdr_off) as usize].length",
        ],
    );
}

#[test]
fn test_root2_cursor_cast_field_chained_offsets_before_cast_read_typecheck() {
    run_test(
        r#"
#[repr(C)]
pub struct Header {
    pub signature: u32,
    pub version: u32,
}

pub unsafe fn read_chained_header_signature(mut data: *const u8, a: isize, b: isize) -> u32 {
    let signature = (*((data.offset(a).offset(b)) as *const Header)).signature;
    return signature;
}
"#,
        &["fn read_chained_header_signature", "signature"],
        &[
            "[(a) as isize].signature",
            "[(a) as usize].signature",
            "[(b) as isize].signature",
            "[(b) as usize].signature",
        ],
    );
}

#[test]
fn test_root2_cursor_cast_field_cast_before_offset_read_typecheck() {
    run_test(
        r#"
#[repr(C)]
pub struct Header {
    pub signature: u32,
    pub version: u32,
}

pub unsafe fn read_cast_before_offset_header_signature(mut data: *const u8, idx: isize) -> u32 {
    let signature = (*((data as *const Header).offset(idx))).signature;
    return signature;
}
"#,
        &["fn read_cast_before_offset_header_signature", "signature"],
        &[
            "(data)[(idx) as isize].signature",
            "(data)[(idx) as usize].signature",
            "data[(idx) as isize].signature",
            "data[(idx) as usize].signature",
        ],
    );
}

#[test]
fn test_root2_cursor_cast_field_mut_cast_before_offset_write_typecheck() {
    run_test(
        r#"
#[repr(C)]
pub struct Header {
    pub signature: u32,
    pub version: u32,
}

pub unsafe fn write_cast_before_offset_header_version(mut data: *mut u8, idx: isize) {
    (*((data as *mut Header).offset(idx))).version = 7;
}
"#,
        &["fn write_cast_before_offset_header_version", "version"],
        &[
            "(data)[(idx) as isize].version",
            "(data)[(idx) as usize].version",
            "data[(idx) as isize].version",
            "data[(idx) as usize].version",
        ],
    );
}

#[test]
fn test_fn_ptr_contract_option_param_expect_callee_uses_rewritten_arg_contract() {
    run_test(
        r#"
pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn call_cb(
    cb: Option<unsafe extern "C" fn(*mut *mut i8) -> i32>,
    mut argv: *mut *mut i8,
) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return cb.expect("cb")(argv);
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    return call_cb(
        Some(add as unsafe extern "C" fn(*mut *mut i8) -> i32),
        argv,
    );
}
"#,
        &[
            "fn add(mut argv: &mut [*mut i8]) -> i32",
            "Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
        ],
        &["cb.expect(\"cb\")((argv).as_mut_ptr())"],
    );
}

#[test]
fn test_fn_ptr_contract_wrapped_option_expect_callee_uses_rewritten_arg_contract() {
    run_test(
        r#"
pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn call_cb(
    cb: Option<unsafe extern "C" fn(*mut *mut i8) -> i32>,
    mut argv: *mut *mut i8,
) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return Some(cb.expect("inner")).expect("outer")(argv);
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    return call_cb(
        Some(add as unsafe extern "C" fn(*mut *mut i8) -> i32),
        argv,
    );
}
"#,
        &[
            "fn add(mut argv: &mut [*mut i8]) -> i32",
            "Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
        ],
        &["expect(\"outer\")((argv).as_mut_ptr())"],
    );
}

#[test]
fn test_fn_ptr_contract_static_field_wrapped_expect_callee_uses_field_contract() {
    run_test(
        r#"
#[repr(C)]
pub struct Command {
    pub run: Option<unsafe extern "C" fn(*mut *mut i8) -> i32>,
}

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub static COMMANDS: [Command; 1] = [Command {
    run: Some(add as unsafe extern "C" fn(*mut *mut i8) -> i32),
}];

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return Some(COMMANDS[0].run.expect("inner")).expect("outer")(argv);
}
"#,
        &[
            "fn add(mut argv: &mut [*mut i8]) -> i32",
            "Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
        ],
        &["expect(\"outer\")((argv).as_mut_ptr())"],
    );
}

#[test]
fn test_fn_ptr_contract_alias_static_and_cast_share_signature_decisions() {
    run_test(
        r#"
pub type CommandFn = unsafe extern "C" fn(*mut *mut i8) -> i32;

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub static COMMAND: CommandFn = add as unsafe extern "C" fn(*mut *mut i8) -> i32;

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return COMMAND(argv);
}
"#,
        &[
            "type CommandFn = unsafe extern \"C\" fn(&mut [*mut i8]) -> i32",
            "add as unsafe extern \"C\" fn(&mut [*mut i8]) -> i32",
        ],
        &[
            "type CommandFn = unsafe extern \"C\" fn(*mut *mut i8) -> i32",
            "COMMAND((argv).as_mut_ptr())",
        ],
    );
}

#[test]
fn test_fn_ptr_contract_alias_local_call_uses_alias_decisions() {
    run_test(
        r#"
pub type CommandFn = unsafe extern "C" fn(*mut *mut i8) -> i32;

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let handler: CommandFn = add as unsafe extern "C" fn(*mut *mut i8) -> i32;
    return handler(argv);
}
"#,
        &[
            "type CommandFn = unsafe extern \"C\" fn(&mut [*mut i8]) -> i32",
            "let handler: CommandFn =",
            "add as unsafe extern \"C\" fn(&mut [*mut i8]) -> i32",
        ],
        &[
            "type CommandFn = unsafe extern \"C\" fn(*mut *mut i8) -> i32",
            "handler((argv).as_mut_ptr())",
        ],
    );
}

#[test]
fn test_fn_ptr_contract_field_option_local_temporary_uses_field_contract() {
    run_test(
        r#"
#[repr(C)]
pub struct Command {
    pub run: Option<unsafe extern "C" fn(*mut *mut i8) -> i32>,
}

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub static COMMANDS: [Command; 1] = [Command {
    run: Some(add as unsafe extern "C" fn(*mut *mut i8) -> i32),
}];

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let handler = COMMANDS[0].run;
    return handler.expect("command")(argv);
}
"#,
        &[
            "fn add(mut argv: &mut [*mut i8]) -> i32",
            "Option<unsafe extern \"C\" fn(&mut [*mut i8]) -> i32>",
        ],
        &["expect(\"command\")((argv).as_mut_ptr())"],
    );
}

#[test]
fn test_fn_pointer_contract_tuple_local_scalar_callback_typechecks() {
    run_test(
        r#"
pub unsafe extern "C" fn set_one(mut value: *mut i32) -> i32 {
    *value = 1;
    return *value;
}

pub unsafe extern "C" fn dispatch(mut value: *mut i32) -> i32 {
    *value = 0;
    let handlers: (unsafe extern "C" fn(*mut i32) -> i32, i32) =
        (set_one as unsafe extern "C" fn(*mut i32) -> i32, 5);
    return (handlers.0)(value) + handlers.1;
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_nested_alias_field_slice_callback_typechecks() {
    run_test(
        r#"
pub type CommandFn = unsafe extern "C" fn(*mut *mut i8) -> i32;
pub type MaybeCommandFn = Option<CommandFn>;

#[repr(C)]
pub struct Command {
    pub run: MaybeCommandFn,
}

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub static COMMANDS: [Command; 1] = [Command {
    run: Some(add as unsafe extern "C" fn(*mut *mut i8) -> i32),
}];

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let handler: MaybeCommandFn = COMMANDS[0].run;
    return handler.expect("command")(argv);
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_alias_param_callback_typechecks() {
    run_test(
        r#"
pub type CommandFn = unsafe extern "C" fn(*mut *mut i8) -> i32;

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn invoke(
    cb: CommandFn,
    mut argv: *mut *mut i8,
) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return cb(argv);
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    return invoke(
        add as unsafe extern "C" fn(*mut *mut i8) -> i32,
        argv,
    );
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_tuple_param_callback_typechecks() {
    run_test(
        r#"
pub type CommandFn = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn invoke(
    pair: (CommandFn, i32),
    mut argv: *mut *mut i8,
) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return pair.0.expect("command")(argv) + pair.1;
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    return invoke(
        (Some(add as unsafe extern "C" fn(*mut *mut i8) -> i32), 7),
        argv,
    );
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_tuple_local_callback_slot_typechecks() {
    run_test(
        r#"
pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let handlers: (unsafe extern "C" fn(*mut *mut i8) -> i32, i32) =
        (add as unsafe extern "C" fn(*mut *mut i8) -> i32, 9);
    return (handlers.0)(argv) + handlers.1;
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_array_local_callback_slot_typechecks() {
    run_test(
        r#"
pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let handlers: [unsafe extern "C" fn(*mut *mut i8) -> i32; 1] =
        [add as unsafe extern "C" fn(*mut *mut i8) -> i32];
    return handlers[0](argv);
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_struct_field_alias_local_typechecks() {
    run_test(
        r#"
pub type CommandFn = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

#[repr(C)]
pub struct Inner {
    pub run: (CommandFn, i32),
}

#[repr(C)]
pub struct Outer {
    pub inner: Inner,
}

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub static OUTER: Outer = Outer {
    inner: Inner {
        run: (Some(add as unsafe extern "C" fn(*mut *mut i8) -> i32), 3),
    },
};

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let handler = OUTER.inner.run.0;
    return handler.expect("command")(argv) + OUTER.inner.run.1;
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_lifetime_args_bare_alias_pointee_adt_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Payload {
    pub value: *mut i32,
}

pub type PayloadVisitor = unsafe extern "C" fn(*mut Payload) -> i32;

pub unsafe extern "C" fn visit_payload(mut payload: *mut Payload) -> i32 {
    *(*payload).value = 13;
    return *(*payload).value;
}

pub unsafe fn promote_and_visit(mut value: i32) -> i32 {
    let mut payload = Payload { value: &raw mut value };
    *payload.value = 5;
    let visitor: PayloadVisitor =
        visit_payload as unsafe extern "C" fn(*mut Payload) -> i32;
    return visitor(&raw mut payload);
}
"#,
        &[
            "pub struct Payload<'a>",
            "pub value: Option<&'a mut i32>",
            "type PayloadVisitor =",
            "for<'a> unsafe extern \"C\" fn(&mut Payload<'a>) -> i32",
        ],
        &["type PayloadVisitor<'a>", "fn(&mut Payload) -> i32"],
    );
}

#[test]
fn test_fn_pointer_lifetime_args_option_alias_pointee_adt_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Payload {
    pub value: *mut i32,
}

pub type MaybePayloadVisitor = Option<unsafe extern "C" fn(*mut Payload) -> i32>;

pub unsafe extern "C" fn visit_payload(mut payload: *mut Payload) -> i32 {
    *(*payload).value = 21;
    return *(*payload).value;
}

pub unsafe fn promote_and_visit(mut value: i32) -> i32 {
    let mut payload = Payload { value: &raw mut value };
    *payload.value = 8;
    let visitor: MaybePayloadVisitor =
        Some(visit_payload as unsafe extern "C" fn(*mut Payload) -> i32);
    return visitor.expect("payload visitor")(&raw mut payload);
}
"#,
        &[
            "pub struct Payload<'a>",
            "pub value: Option<&'a mut i32>",
            "type MaybePayloadVisitor =",
            "Option<for<'a> unsafe extern \"C\" fn(&mut Payload<'a>) -> i32>",
        ],
        &["type MaybePayloadVisitor<'a>", "fn(&mut Payload) -> i32"],
    );
}

#[test]
fn test_fn_pointer_lifetime_args_struct_field_callback_pointee_adt_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Payload {
    pub value: *mut i32,
}

#[repr(C)]
pub struct CallbackTable {
    pub visit: Option<unsafe extern "C" fn(*mut Payload) -> i32>,
}

pub unsafe extern "C" fn visit_payload(mut payload: *mut Payload) -> i32 {
    *(*payload).value = 34;
    return *(*payload).value;
}

pub unsafe fn promote_and_visit(mut value: i32) -> i32 {
    let mut payload = Payload { value: &raw mut value };
    *payload.value = 11;
    let table = CallbackTable {
        visit: Some(visit_payload as unsafe extern "C" fn(*mut Payload) -> i32),
    };
    return table.visit.expect("payload visitor")(&raw mut payload);
}
"#,
        &[
            "pub struct Payload<'a>",
            "pub value: Option<&'a mut i32>",
            "pub struct CallbackTable",
            "pub visit: Option<for<'a> unsafe extern \"C\" fn(&mut Payload<'a>) -> i32>",
        ],
        &["pub struct CallbackTable<'a>", "fn(&mut Payload) -> i32"],
    );
}

#[test]
fn test_fn_pointer_lifetime_args_nested_callback_table_chain_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Payload {
    pub value: *mut i32,
}

pub type PayloadVisitor = Option<unsafe extern "C" fn(*mut Payload) -> i32>;

#[repr(C)]
pub struct RemoteCallbacks {
    pub visit: PayloadVisitor,
}

#[repr(C)]
pub struct FetchOptions {
    pub callbacks: RemoteCallbacks,
}

#[repr(C)]
pub struct CloneOptions {
    pub fetch: FetchOptions,
    pub checkout: PayloadVisitor,
}

pub unsafe extern "C" fn visit_payload(mut payload: *mut Payload) -> i32 {
    *(*payload).value += 1;
    return *(*payload).value;
}

pub unsafe fn promote_and_visit(mut value: i32) -> i32 {
    let mut payload = Payload { value: &raw mut value };
    *payload.value = 55;
    let options = CloneOptions {
        fetch: FetchOptions {
            callbacks: RemoteCallbacks {
                visit: Some(visit_payload as unsafe extern "C" fn(*mut Payload) -> i32),
            },
        },
        checkout: Some(visit_payload as unsafe extern "C" fn(*mut Payload) -> i32),
    };
    let first = options
        .fetch
        .callbacks
        .visit
        .expect("remote callback")(&raw mut payload);
    return first + options.checkout.expect("checkout callback")(&raw mut payload);
}
"#,
        &[
            "pub struct Payload<'a>",
            "pub value: Option<&'a mut i32>",
            "type PayloadVisitor =",
            "Option<for<'a> unsafe extern \"C\" fn(&mut Payload<'a>) -> i32>",
            "pub struct RemoteCallbacks",
            "pub visit: PayloadVisitor",
            "pub struct FetchOptions",
            "pub callbacks: RemoteCallbacks",
            "pub struct CloneOptions",
            "pub fetch: FetchOptions",
            "pub checkout: PayloadVisitor",
        ],
        &[
            "fn(&mut Payload) -> i32",
            "type PayloadVisitor<'a>",
            "pub struct RemoteCallbacks<'a>",
            "pub struct FetchOptions<'a>",
            "pub struct CloneOptions<'",
        ],
    );
}

#[test]
fn test_fn_pointer_contract_options_callback_output_return_lifetime_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Inner {
    pub value: *const i32,
}

#[repr(C)]
pub struct Remote {
    pub inner: Inner,
    pub id: i32,
}

pub type RemoteCreateCb =
    Option<unsafe extern "C" fn(*mut *mut Remote) -> i32>;

#[repr(C)]
pub struct RemoteCreateOptions {
    pub create: RemoteCreateCb,
}

pub unsafe fn promote_inner(value: i32) -> i32 {
    let inner = Inner { value: &raw const value };
    return *inner.value;
}

pub unsafe fn read_remote(mut remote: *mut Remote) -> i32 {
    return *(*remote).inner.value + (*remote).id;
}

pub unsafe extern "C" fn create_remote(mut out: *mut *mut Remote) -> i32 {
    *out.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe fn create_and_configure_origin(
    mut opts: *mut RemoteCreateOptions,
    mut fallback: *mut Remote,
) -> Option<*mut Remote> {
    let mut remote: *mut Remote = fallback;
    (*opts).create.expect("create")(&mut remote);
    if remote.is_null() {
        return None;
    }
    return Some(remote);
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_options_callback_local_alias_output_return_lifetime_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Inner {
    pub value: *const i32,
}

#[repr(C)]
pub struct Remote {
    pub inner: Inner,
    pub id: i32,
}

pub type RemoteCreateCb =
    Option<unsafe extern "C" fn(*mut *mut Remote) -> i32>;

#[repr(C)]
pub struct RemoteCreateOptions {
    pub create: RemoteCreateCb,
}

pub unsafe fn promote_inner(value: i32) -> i32 {
    let inner = Inner { value: &raw const value };
    return *inner.value;
}

pub unsafe fn read_remote(mut remote: *mut Remote) -> i32 {
    return *(*remote).inner.value + (*remote).id;
}

pub unsafe extern "C" fn create_remote(mut out: *mut *mut Remote) -> i32 {
    *out.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe fn create_and_configure_alias(
    mut opts: *mut RemoteCreateOptions,
    mut fallback: *mut Remote,
) -> Option<*mut Remote> {
    let mut remote: *mut Remote = fallback;
    let mut create = (*opts).create;
    create.expect("create")(&mut remote);
    if remote.is_null() {
        return None;
    }
    return Some(remote);
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_transport_method_options_lifetime_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct ConnectOptions {
    pub payload: *mut i32,
}

pub type ConnectFn =
    Option<unsafe extern "C" fn(*mut Transport, *mut ConnectOptions) -> i32>;

#[repr(C)]
pub struct Transport {
    pub payload: *mut i32,
    pub connect: ConnectFn,
}

#[repr(C)]
pub struct Remote {
    pub transport: *mut Transport,
}

pub unsafe extern "C" fn connect_impl(
    mut transport: *mut Transport,
    mut opts: *mut ConnectOptions,
) -> i32 {
    *(*transport).payload += *(*opts).payload;
    return *(*transport).payload;
}

pub unsafe fn connect_or_reset_options(
    mut remote: *mut Remote,
    mut opts: *mut ConnectOptions,
) -> i32 {
    return (*(*remote).transport)
        .connect
        .expect("connect")((*remote).transport, opts);
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_root3_fn_pointer_static_definition_table_lookup_result_dispatch_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Transport {
    pub payload: *mut i32,
}

#[repr(C)]
pub struct Remote {
    pub transport: *mut Transport,
    pub payload: *mut i32,
}

pub type TransportCb =
    Option<unsafe extern "C" fn(*mut *mut Transport, *mut Remote) -> i32>;

#[repr(C)]
pub struct TransportDefinition {
    pub scheme: *const i8,
    pub callback: TransportCb,
}

pub unsafe extern "C" fn local_transport(
    mut out: *mut *mut Transport,
    mut remote: *mut Remote,
) -> i32 {
    *out.offset(0) = core::ptr::null_mut();
    *(*remote).payload += 1;
    return *(*remote).payload;
}

pub unsafe fn read_transport(mut transport: *mut Transport) -> i32 {
    return *(*transport).payload;
}

pub static mut TRANSPORTS: [TransportDefinition; 2] = [
    TransportDefinition {
        scheme: b"file\0".as_ptr() as *const i8,
        callback: Some(
            local_transport
                as unsafe extern "C" fn(*mut *mut Transport, *mut Remote) -> i32,
        ),
    },
    TransportDefinition {
        scheme: b"local\0".as_ptr() as *const i8,
        callback: Some(
            local_transport
                as unsafe extern "C" fn(*mut *mut Transport, *mut Remote) -> i32,
        ),
    },
];

pub unsafe fn transport_find_by_url(
    mut use_second: i32,
) -> *const TransportDefinition {
    if use_second != 0 {
        return &raw const TRANSPORTS[1usize];
    }
    return &raw const TRANSPORTS[0usize];
}

pub unsafe fn transport_find_fn(mut use_second: i32) -> Result<TransportCb, i32> {
    let definition = transport_find_by_url(use_second);
    if definition.is_null() {
        return Err(-1);
    }
    return Ok((*definition).callback);
}

pub unsafe fn dispatch_transport(mut remote: *mut Remote) -> i32 {
    let mut transport: *mut Transport = core::ptr::null_mut();
    let callback = transport_find_fn(1).unwrap();
    return callback.expect("transport")(&mut transport, remote);
}

pub unsafe fn call_with_non_static_transport(
    mut transport_payload: i32,
    mut remote_payload: i32,
) -> i32 {
    let mut transport = Transport {
        payload: &raw mut transport_payload,
    };
    let mut remote = Remote {
        transport: &raw mut transport,
        payload: &raw mut remote_payload,
    };
    return dispatch_transport(&raw mut remote) + read_transport(&raw mut transport);
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_root3_fn_pointer_static_mut_single_definition_fallback_tuple_dispatch_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Transport {
    pub payload: *mut i32,
}

#[repr(C)]
pub struct Remote {
    pub transport: *mut Transport,
    pub payload: *mut i32,
}

pub type TransportCb =
    Option<unsafe extern "C" fn(*mut *mut Transport, *mut Remote) -> i32>;

#[repr(C)]
pub struct TransportDefinition {
    pub callback: TransportCb,
}

pub unsafe extern "C" fn local_transport(
    mut out: *mut *mut Transport,
    mut remote: *mut Remote,
) -> i32 {
    *out.offset(0) = core::ptr::null_mut();
    *(*remote).payload += 1;
    return *(*remote).payload;
}

pub unsafe fn read_transport(mut transport: *mut Transport) -> i32 {
    return *(*transport).payload;
}

pub static mut LOCAL_TRANSPORT_DEFINITION: TransportDefinition =
    TransportDefinition {
        callback: Some(
            local_transport
                as unsafe extern "C" fn(*mut *mut Transport, *mut Remote) -> i32,
        ),
    };

pub unsafe fn transport_find_fallback() -> *const TransportDefinition {
    return &raw const LOCAL_TRANSPORT_DEFINITION;
}

pub unsafe fn transport_find_fallback_fn() -> (TransportCb, i32) {
    let definition = transport_find_fallback();
    if definition.is_null() {
        return (None, -1);
    }
    return ((*definition).callback, 0);
}

pub unsafe fn dispatch_fallback(mut remote: *mut Remote) -> i32 {
    let mut transport: *mut Transport = core::ptr::null_mut();
    let found = transport_find_fallback_fn();
    if found.1 != 0 {
        return found.1;
    }
    return found.0.expect("transport")(&mut transport, remote);
}

pub unsafe fn call_fallback_with_non_static_transport(
    mut transport_payload: i32,
    mut remote_payload: i32,
) -> i32 {
    let mut transport = Transport {
        payload: &raw mut transport_payload,
    };
    let mut remote = Remote {
        transport: &raw mut transport,
        payload: &raw mut remote_payload,
    };
    return dispatch_fallback(&raw mut remote) + read_transport(&raw mut transport);
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_root3_fn_pointer_mixed_data_and_callback_field_lifetimes_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Payload {
    pub value: *mut i32,
}

#[repr(C)]
pub struct CallbackTable {
    pub stored: *mut Payload,
    pub visit: Option<unsafe extern "C" fn(*mut Payload) -> i32>,
}

pub unsafe extern "C" fn visit_payload(mut payload: *mut Payload) -> i32 {
    *(*payload).value += 1;
    return *(*payload).value;
}

pub unsafe fn promote_and_visit(mut value: i32) -> i32 {
    let mut payload = Payload { value: &raw mut value };
    let table = CallbackTable {
        stored: &raw mut payload,
        visit: Some(visit_payload as unsafe extern "C" fn(*mut Payload) -> i32),
    };
    return table.visit.expect("payload visitor")(table.stored);
}
"#,
        &[
            "pub struct CallbackTable<'a, 'b>",
            "pub stored: &'a mut [Payload<'b>]",
            "pub visit: Option<for<'c> unsafe extern \"C\" fn(&mut Payload<'c>) -> i32>",
        ],
        &["pub visit: Option<for<'a> unsafe extern \"C\" fn(&mut Payload<'a>) -> i32>"],
    );
}

#[test]
fn test_fn_signature_declares_nested_adt_lifetimes_raw_nested_parameter_typechecks() {
    run_test(
        r#"
extern "C" {
    fn raw_touch(slot: *mut *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Payload {
    pub value: *mut i32,
}

pub unsafe fn promote_payload(mut value: i32) -> i32 {
    let mut payload = Payload { value: &raw mut value };
    *payload.value = 101;
    return *payload.value;
}

pub unsafe fn raw_nested_slot(mut slot: *mut *mut Payload) {
    raw_touch(slot as *mut *mut core::ffi::c_void);
}
"#,
        &[
            "pub struct Payload<'a>",
            "pub unsafe fn raw_nested_slot<'a>(mut slot:",
            "Option<&mut *mut crate::Payload<'a>>",
        ],
        &["pub unsafe fn raw_nested_slot(mut slot:"],
    );
}

#[test]
fn test_fn_signature_declares_nested_adt_lifetimes_out_slice_parameter_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Payload {
    pub value: *mut i32,
}

pub unsafe fn promote_payload(mut value: i32) -> i32 {
    let mut payload = Payload { value: &raw mut value };
    *payload.value = 202;
    return *payload.value;
}

pub unsafe fn clear_payload_slot(mut out: *mut *mut Payload) {
    *out.offset(0) = core::ptr::null_mut();
}
"#,
        &[
            "pub struct Payload<'a>",
            "pub unsafe fn clear_payload_slot<'a>(mut out:",
            "&mut [*mut crate::Payload<'a>])",
        ],
        &["pub unsafe fn clear_payload_slot(mut out: &mut [*mut crate::Payload<'a>])"],
    );
}

#[test]
fn test_fn_signature_declares_nested_adt_lifetimes_multi_lifetime_out_slice_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Pair {
    pub left: *mut i32,
    pub right: *const i32,
}

pub unsafe fn promote_pair(mut left: i32, right: i32) -> i32 {
    let mut pair = Pair {
        left: &raw mut left,
        right: &raw const right,
    };
    *pair.left = 303;
    return *pair.left + *pair.right;
}

pub unsafe fn clear_pair_slot(mut out: *mut *mut Pair) {
    *out.offset(0) = core::ptr::null_mut();
}
"#,
        &[
            "pub struct Pair<'a, 'b>",
            "pub unsafe fn clear_pair_slot<'a,",
            "'b>(mut out: &mut [*mut crate::Pair<'a, 'b>])",
        ],
        &["pub unsafe fn clear_pair_slot(mut out: &mut [*mut crate::Pair<'a, 'b>])"],
    );
}

#[test]
fn test_fn_signature_declares_nested_adt_lifetimes_multi_lifetime_raw_parameter_typechecks() {
    run_test(
        r#"
extern "C" {
    fn raw_touch(slot: *mut *mut core::ffi::c_void);
}

#[repr(C)]
pub struct Pair {
    pub left: *mut i32,
    pub right: *const i32,
}

pub unsafe fn promote_pair(mut left: i32, right: i32) -> i32 {
    let mut pair = Pair {
        left: &raw mut left,
        right: &raw const right,
    };
    *pair.left = 404;
    return *pair.left + *pair.right;
}

pub unsafe fn raw_pair_slot(mut slot: *mut *mut Pair) {
    raw_touch(slot as *mut *mut core::ffi::c_void);
}
"#,
        &[
            "pub struct Pair<'a, 'b>",
            "pub unsafe fn raw_pair_slot<'a,",
            "'b>(mut slot:",
            "Option<&mut *mut crate::Pair<'a, 'b>>",
        ],
        &["pub unsafe fn raw_pair_slot(mut slot:"],
    );
}

#[test]
fn test_fn_signature_declares_nested_adt_lifetimes_merges_existing_input_lifetime_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Pair {
    pub left: *mut i32,
    pub right: *const i32,
}

pub unsafe fn promote_pair(mut left: i32, right: i32) -> i32 {
    let mut pair = Pair {
        left: &raw mut left,
        right: &raw const right,
    };
    *pair.left = 505;
    return *pair.left + *pair.right;
}

pub unsafe fn pair_slot_and_identity(
    flag: bool,
    value: *mut i32,
    out: *mut *mut Pair,
) -> *mut i32 {
    *out.offset(0) = core::ptr::null_mut();
    if flag {
        return value;
    }
    return core::ptr::null_mut();
}
"#,
        &[
            "pub struct Pair<'a, 'b>",
            "pub unsafe fn pair_slot_and_identity<'a,",
            "'b,\n    'c>(flag: bool",
            "mut value: Option<&'a mut i32>",
            "mut out: &mut [*mut crate::Pair<'b, 'c>]",
            "-> Option<&'a mut i32>",
        ],
        &["pub unsafe fn pair_slot_and_identity<'a>("],
    );
}

#[test]
fn test_fn_signature_uses_nested_item_lifetime_slots_for_second_repeated_shared_field_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct static_tree_desc {
    pub static_tree: *const i32,
}

#[repr(C)]
pub struct tree_desc {
    pub stat_desc: *const static_tree_desc,
}

#[repr(C)]
pub struct internal_state {
    pub l_desc: tree_desc,
    pub bl_desc: tree_desc,
}

pub unsafe fn build_tree(
    mut s: *mut internal_state,
    mut desc: *mut tree_desc,
) -> i32 {
    return *(*(*desc.offset(0)).stat_desc.offset(0)).static_tree.offset(0);
}

pub unsafe fn build_bl_tree(mut s: *mut internal_state) -> i32 {
    return build_tree(s, &raw mut (*s.offset(0)).bl_desc);
}
"#,
        &[
            "pub struct tree_desc<'a, 'b>",
            "pub struct internal_state<'a, 'b, 'c, 'd>",
            "pub l_desc: tree_desc<'a, 'b>",
            "pub bl_desc: tree_desc<'c, 'd>",
            "pub unsafe fn build_tree<'a, 'b,",
        ],
        &["pub bl_desc: tree_desc,"],
    );
}

#[test]
fn test_fn_signature_uses_nested_item_lifetime_slots_for_second_repeated_mut_chain_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct static_tree_desc {
    pub static_tree: *mut i32,
}

#[repr(C)]
pub struct tree_desc {
    pub stat_desc: *mut static_tree_desc,
}

#[repr(C)]
pub struct internal_state {
    pub l_desc: tree_desc,
    pub bl_desc: tree_desc,
}

pub unsafe fn read_tree_value(
    mut s: *mut internal_state,
    mut desc: *mut tree_desc,
) -> i32 {
    return *(*(*desc.offset(0)).stat_desc.offset(0)).static_tree.offset(0);
}

pub unsafe fn read_bl_tree_value(mut s: *mut internal_state) -> i32 {
    return read_tree_value(s, &raw mut (*s.offset(0)).bl_desc);
}
"#,
        &[
            "pub struct tree_desc<'a, 'b>",
            "pub struct internal_state<'a, 'b, 'c, 'd>",
            "pub l_desc: tree_desc<'a, 'b>",
            "pub bl_desc: tree_desc<'c, 'd>",
            "pub unsafe fn read_tree_value<'a, 'b,",
        ],
        &["pub bl_desc: tree_desc,"],
    );
}

#[test]
fn test_fn_signature_uses_nested_item_lifetime_slots_for_reversed_second_field_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
#[repr(C)]
pub struct static_tree_desc {
    pub static_tree: *const i32,
}

#[repr(C)]
pub struct tree_desc {
    pub stat_desc: *const static_tree_desc,
}

#[repr(C)]
pub struct internal_state {
    pub bl_desc: tree_desc,
    pub l_desc: tree_desc,
}

pub unsafe fn build_tree(
    mut s: *mut internal_state,
    mut desc: *mut tree_desc,
) -> i32 {
    return *(*(*desc.offset(0)).stat_desc.offset(0)).static_tree.offset(0);
}

pub unsafe fn build_l_tree(mut s: *mut internal_state) -> i32 {
    return build_tree(s, &raw mut (*s.offset(0)).l_desc);
}
"#,
        &[
            "pub struct tree_desc<'a, 'b>",
            "pub struct internal_state<'a, 'b, 'c, 'd>",
            "pub bl_desc: tree_desc<'a, 'b>",
            "pub l_desc: tree_desc<'c, 'd>",
            "pub unsafe fn build_tree<'a, 'b,",
        ],
        &["pub l_desc: tree_desc,"],
    );
}

#[test]
fn test_fn_return_declares_nested_adt_lifetimes_option_raw_payload_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Inner {
    pub value: *const i32,
}

#[repr(C)]
pub struct Payload {
    pub inner: Inner,
    pub tag: i32,
}

pub unsafe fn promote_inner(value: i32) -> i32 {
    let inner = Inner { value: &raw const value };
    return *inner.value;
}

pub unsafe fn read_second_inner(first: i32, second: i32) -> i32 {
    let inners = [
        Inner { value: &raw const first },
        Inner { value: &raw const second },
    ];
    let mut p: *const Inner = inners.as_ptr();
    return *(*p.offset(1)).value;
}

pub unsafe fn maybe_payload(flag: bool) -> Option<*mut Payload> {
    if flag {
        return Some(core::ptr::null_mut());
    }
    return None;
}
"#,
        &[
            "pub struct Inner<'a>",
            "pub struct Payload<'a>",
            "pub inner: Inner<'a>",
            "pub unsafe fn maybe_payload<'a>(flag: bool) -> Option<*mut Payload<'a>>",
        ],
        &["Option<*mut Payload<'_>>"],
    );
}

#[test]
fn test_fn_return_declares_nested_adt_lifetimes_result_raw_payload_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Inner {
    pub value: *const i32,
}

#[repr(C)]
pub struct Payload {
    pub inner: Inner,
    pub tag: i32,
}

pub unsafe fn promote_inner(value: i32) -> i32 {
    let inner = Inner { value: &raw const value };
    return *inner.value;
}

pub unsafe fn read_second_inner(first: i32, second: i32) -> i32 {
    let inners = [
        Inner { value: &raw const first },
        Inner { value: &raw const second },
    ];
    let mut p: *const Inner = inners.as_ptr();
    return *(*p.offset(1)).value;
}

pub unsafe fn payload_result(flag: bool) -> Result<*mut Payload, i32> {
    if flag {
        return Ok(core::ptr::null_mut());
    }
    return Err(-1);
}
"#,
        &[
            "pub struct Inner<'a>",
            "pub struct Payload<'a>",
            "pub inner: Inner<'a>",
            "pub unsafe fn payload_result<'a>(flag: bool)",
            "-> Result<*mut Payload<'a>, i32>",
        ],
        &["Result<*mut Payload<'_>, i32>"],
    );
}

#[test]
fn test_fn_return_declares_nested_adt_lifetimes_tuple_raw_payload_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Inner {
    pub value: *const i32,
}

#[repr(C)]
pub struct Payload {
    pub inner: Inner,
    pub tag: i32,
}

pub unsafe fn promote_inner(value: i32) -> i32 {
    let inner = Inner { value: &raw const value };
    return *inner.value;
}

pub unsafe fn read_second_inner(first: i32, second: i32) -> i32 {
    let inners = [
        Inner { value: &raw const first },
        Inner { value: &raw const second },
    ];
    let mut p: *const Inner = inners.as_ptr();
    return *(*p.offset(1)).value;
}

pub unsafe fn payload_tuple() -> (*mut Payload, i32) {
    return (core::ptr::null_mut(), 8);
}
"#,
        &[
            "pub struct Inner<'a>",
            "pub struct Payload<'a>",
            "pub inner: Inner<'a>",
            "pub unsafe fn payload_tuple<'a>() -> (*mut Payload<'a>, i32)",
        ],
        &["(*mut Payload<'_>, i32)"],
    );
}

#[test]
fn test_fn_return_declares_nested_adt_lifetimes_direct_raw_payload_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Inner {
    pub value: *const i32,
}

#[repr(C)]
pub struct Payload {
    pub inner: Inner,
    pub tag: i32,
}

pub unsafe fn promote_inner(value: i32) -> i32 {
    let inner = Inner { value: &raw const value };
    return *inner.value;
}

pub unsafe fn read_second_inner(first: i32, second: i32) -> i32 {
    let inners = [
        Inner { value: &raw const first },
        Inner { value: &raw const second },
    ];
    let mut p: *const Inner = inners.as_ptr();
    return *(*p.offset(1)).value;
}

pub unsafe fn raw_payload() -> *mut Payload {
    return core::ptr::null_mut();
}

pub unsafe fn call_raw_payload() {
    let factory: unsafe fn() -> *mut Payload = raw_payload;
    let _ = factory();
}
"#,
        &[
            "pub struct Inner<'a>",
            "pub struct Payload<'a>",
            "pub inner: Inner<'a>",
            "pub unsafe fn raw_payload<'a>()",
            "Payload<'a>",
        ],
        &["-> *mut Payload<'_>"],
    );
}

#[test]
fn test_fn_return_declares_nested_adt_lifetimes_reuses_input_lifetime_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Inner {
    pub value: *const i32,
}

#[repr(C)]
pub struct Payload {
    pub inner: Inner,
    pub tag: i32,
}

pub unsafe fn promote_inner(value: i32) -> i32 {
    let inner = Inner { value: &raw const value };
    return *inner.value;
}

pub unsafe fn read_second_inner(first: i32, second: i32) -> i32 {
    let inners = [
        Inner { value: &raw const first },
        Inner { value: &raw const second },
    ];
    let mut p: *const Inner = inners.as_ptr();
    return *(*p.offset(1)).value;
}

pub unsafe fn maybe_payload_for_value<'a>(
    _value: &'a i32,
    flag: bool,
) -> Option<*mut Payload> {
    if flag {
        return Some(core::ptr::null_mut());
    }
    return None;
}
"#,
        &[
            "pub struct Inner<'a>",
            "pub struct Payload<'a>",
            "pub inner: Inner<'a>",
            "pub unsafe fn maybe_payload_for_value<'a>(",
            "_value: &'a i32",
            "-> Option<*mut Payload<'a>>",
        ],
        &["Option<*mut Payload<'_>>"],
    );
}

#[test]
fn test_fn_return_declares_nested_adt_lifetimes_option_multi_lifetime_payload_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Pair {
    pub left: *const i32,
    pub right: *const i32,
}

#[repr(C)]
pub struct PairPayload {
    pub pair: Pair,
    pub tag: i32,
}

pub unsafe fn promote_pair(left: i32, right: i32) -> i32 {
    let pair = Pair {
        left: &raw const left,
        right: &raw const right,
    };
    return *pair.left + *pair.right;
}

pub unsafe fn read_second_pair(a: i32, b: i32, c: i32, d: i32) -> i32 {
    let pairs = [
        Pair {
            left: &raw const a,
            right: &raw const b,
        },
        Pair {
            left: &raw const c,
            right: &raw const d,
        },
    ];
    let mut p: *const Pair = pairs.as_ptr();
    return *(*p.offset(1)).left + *(*p.offset(1)).right;
}

pub unsafe fn maybe_pair_payload(flag: bool) -> Option<*mut PairPayload> {
    if flag {
        return Some(core::ptr::null_mut());
    }
    return None;
}
"#,
        &[
            "pub struct Pair<'a, 'b>",
            "pub struct PairPayload<'a, 'b>",
            "pub pair: Pair<'a, 'b>",
            "pub unsafe fn maybe_pair_payload<'a, 'b>(flag: bool)",
            "-> Option<*mut PairPayload<'a, 'b>>",
        ],
        &["Option<*mut PairPayload<'_"],
    );
}

#[test]
fn test_adt_lifetime_family_direct_member_field_store_typechecks() {
    run_adt_lifetime_family_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: *mut i32,
}

#[repr(C)]
pub struct Head {
    pub entry: *mut Entry,
}

pub unsafe fn promote_entry(mut entry: *mut Entry) -> i32 {
    *(*entry).value += 1;
    return *(*entry).value;
}

pub unsafe fn install_entry(mut head: *mut Head, mut entry: *mut Entry) {
    (*head).entry = entry;
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub struct Head<'a>",
            "pub unsafe fn install_entry<'a",
            "crate::Head<'a",
            "crate::Entry<'a",
        ],
        &[
            "pub struct Head {",
            "pub entry: *mut Entry",
            "pub unsafe fn install_entry(mut head: *mut crate::Head",
        ],
    );
}

#[test]
fn test_adt_lifetime_family_indirect_slot_store_typechecks() {
    run_adt_lifetime_family_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: *mut i32,
}

#[repr(C)]
pub struct HeadMap {
    pub slot: *mut *mut Entry,
}

pub unsafe fn promote_entry(mut entry: *mut Entry) -> i32 {
    *(*entry).value = 3;
    return *(*entry).value;
}

pub unsafe fn install_slot(mut head: *mut HeadMap, mut entry: *mut Entry) {
    *(*head).slot = entry;
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub struct HeadMap<'a, 'b>",
            "pub unsafe fn install_slot<'a",
            "crate::HeadMap<'b, 'a",
            "crate::Entry<'a",
        ],
        &[
            "pub struct HeadMap {",
            "pub slot: *mut *mut Entry",
            "pub unsafe fn install_slot(mut head: *mut crate::HeadMap",
        ],
    );
}

#[test]
fn test_adt_lifetime_family_output_param_retrieval_typechecks() {
    run_adt_lifetime_family_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: *mut i32,
}

#[repr(C)]
pub struct Head {
    pub entry: *mut Entry,
}

pub unsafe fn promote_entry(mut entry: *mut Entry) -> i32 {
    *(*entry).value += 5;
    return *(*entry).value;
}

pub unsafe fn get_entry(mut out: *mut *mut Entry, mut head: *mut Head) {
    *out.offset(0) = (*head).entry;
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub struct Head<'a>",
            "pub unsafe fn get_entry<'a",
            "&mut [*mut crate::Entry<'a>]",
            "crate::Head<'a",
        ],
        &[
            "pub struct Head {",
            "pub entry: *mut Entry",
            "pub unsafe fn get_entry(mut out: *mut *mut crate::Entry",
        ],
    );
}

#[test]
fn test_adt_lifetime_family_cyclic_graph_out_param_typechecks() {
    run_adt_lifetime_family_test(
        r#"
#[repr(C)]
pub struct Remote {
    pub push: *mut Push,
    pub id: i32,
}

#[repr(C)]
pub struct Push {
    pub remote: *mut Remote,
    pub value: *mut i32,
}

pub unsafe fn promote_push(mut push: *mut Push) -> i32 {
    *(*push).value += 7;
    return *(*push).value;
}

pub unsafe fn link_push(
    mut out: *mut *mut Push,
    mut remote: *mut Remote,
    mut push: *mut Push,
) {
    (*push).remote = remote;
    (*remote).push = push;
    *out.offset(0) = push;
}
"#,
        &[
            "pub struct Remote<'a>",
            "pub struct Push<'a>",
            "pub unsafe fn link_push<'a",
            "crate::Push<'a",
            "crate::Remote<'a",
        ],
        &[
            "pub struct Remote {",
            "pub push: *mut Push",
            "pub struct Push {",
            "pub remote: *mut Remote",
        ],
    );
}

#[test]
fn test_adt_lifetime_family_type_alias_member_store_typechecks() {
    run_adt_lifetime_family_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: *mut i32,
}

pub type EntryAlias = Entry;
pub type EntryPtr = *mut EntryAlias;

#[repr(C)]
pub struct Bucket {
    pub current: EntryPtr,
}

pub unsafe fn promote_entry(mut entry: *mut Entry) -> i32 {
    *(*entry).value += 9;
    return *(*entry).value;
}

pub unsafe fn install_alias(mut bucket: *mut Bucket, mut entry: EntryPtr) {
    (*bucket).current = entry;
}
"#,
        &[
            "pub type EntryAlias<'a> = Entry<'a>",
            "pub type EntryPtr<'a> = *mut EntryAlias<'a>",
            "pub struct Bucket<'a>",
            "pub unsafe fn install_alias<'a",
            "crate::Bucket<'a",
            "crate::Entry<'a",
        ],
        &[
            "pub type EntryAlias = Entry",
            "pub type EntryPtr = *mut EntryAlias",
            "pub struct Bucket {",
            "pub current: EntryPtr",
        ],
    );
}

#[test]
fn test_adt_lifetime_family_nested_container_store_typechecks() {
    run_adt_lifetime_family_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: *mut i32,
}

#[repr(C)]
pub struct Head {
    pub entry: *mut Entry,
}

#[repr(C)]
pub struct Wrapper {
    pub head: Head,
}

pub unsafe fn promote_entry(mut entry: *mut Entry) -> i32 {
    *(*entry).value += 11;
    return *(*entry).value;
}

pub unsafe fn install_nested(mut wrapper: *mut Wrapper, mut entry: *mut Entry) {
    (*wrapper).head.entry = entry;
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub struct Head<'a>",
            "pub struct Wrapper<'a>",
            "pub unsafe fn install_nested<'a",
            "crate::Wrapper<'a",
            "crate::Entry<'a",
        ],
        &[
            "pub struct Head {",
            "pub entry: *mut Entry",
            "pub struct Wrapper {",
            "pub head: Head",
        ],
    );
}

#[test]
fn test_adt_lifetime_family_local_call_field_output_slot_typechecks() {
    run_test(
        r#"
#[repr(C)]
pub struct Leaf {
    pub value: *const i32,
}

impl Copy for Leaf {}

impl Clone for Leaf {
    fn clone(&self) -> Leaf {
        *self
    }
}

#[repr(C)]
pub struct Index {
    pub left: Leaf,
    pub right: Leaf,
}

#[repr(C)]
pub struct Holder {
    pub index: *mut Index,
    pub count: i32,
}

pub unsafe fn promote_leaf(value: i32) -> i32 {
    let leaf = Leaf { value: &raw const value };
    return *leaf.value;
}

pub unsafe fn promote_distinct(left: i32, right: i32) -> i32 {
    let index = Index {
        left: Leaf { value: &raw const left },
        right: Leaf { value: &raw const right },
    };
    return *index.left.value + *index.right.value;
}

pub unsafe fn init(mut out: *mut *mut Index, mut index: *mut Index) {
    (*index).left = (*index).right;
    *out.offset(0) = index;
}

pub unsafe fn install(mut src: *mut Holder, mut index: *mut Index) {
    init(&mut (*src).index, index);
    (*src).count = 1;
}
"#,
        &[
            "pub struct Leaf<'a>",
            "pub struct Index<'a, 'b>",
            "pub struct Holder<'a, 'b>",
            "pub unsafe fn init<'a>(mut out: &mut [*mut crate::Index<'a, 'a>]",
            "pub unsafe fn install<'a>(mut src: &mut crate::Holder<'a, 'a>",
            "std::slice::from_mut(&mut ((*src).index))",
        ],
        &["pub unsafe fn install<'a, 'b>(mut src: &mut crate::Holder<'a, 'b>"],
    );
}

#[test]
fn test_adt_lifetime_family_local_call_cross_argument_field_slot_typechecks() {
    run_adt_lifetime_family_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: *const i32,
}

#[repr(C)]
pub struct Head {
    pub entry: *const Entry,
}

#[repr(C)]
pub struct Holder {
    pub head: Head,
    pub pending: *const Entry,
}

pub unsafe fn promote_entry(value: i32) -> i32 {
    let entry = Entry { value: &raw const value };
    return *entry.value;
}

pub unsafe fn link(mut head: *mut Head, mut entry: *const Entry) {
    (*head).entry = entry;
}

pub unsafe fn install_pending(mut holder: *mut Holder) {
    link(&raw mut (*holder).head, (*holder).pending);
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub struct Head<'a>",
            "pub struct Holder<'a, 'b, 'c>",
            "pub unsafe fn link<'a>",
            "crate::Head<'a",
            "crate::Entry<'a",
            "pub unsafe fn install_pending<'a",
            "crate::Holder<'b, 'a, 'a>",
        ],
        &[
            "pub struct Holder {",
            "pub head: Head,",
            "pub pending: *const Entry",
            "pub unsafe fn install_pending(mut holder: *mut crate::Holder",
        ],
    );
}

#[test]
fn test_adt_lifetime_family_let_alias_member_field_store_typechecks() {
    run_adt_lifetime_family_test(
        r#"
#[repr(C)]
pub struct Entry {
    pub value: *mut i32,
}

#[repr(C)]
pub struct Head {
    pub entry: *mut Entry,
}

pub unsafe fn promote_entry(mut entry: *mut Entry) -> i32 {
    *(*entry).value += 13;
    return *(*entry).value;
}

pub unsafe fn install_entry_alias(mut head: *mut Head, mut entry: *mut Entry) {
    let mut tmp = entry;
    (*head).entry = tmp;
}
"#,
        &[
            "pub struct Entry<'a>",
            "pub struct Head<'a>",
            "pub unsafe fn install_entry_alias<'a",
            "crate::Head<'a",
            "crate::Entry<'a",
        ],
        &[
            "pub struct Head {",
            "pub entry: *mut Entry",
            "pub unsafe fn install_entry_alias(mut head: *mut crate::Head",
        ],
    );
}

#[test]
fn test_fn_pointer_contract_raw_c_exposed_param_slot_typechecks() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("invoke".to_string());
    run_test_with_config(
        r#"
pub type CommandFn = unsafe extern "C" fn(*mut *mut i8) -> i32;

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

#[no_mangle]
pub unsafe extern "C" fn invoke(
    cb: CommandFn,
    mut argv: *mut *mut i8,
) -> i32 {
    return cb(argv);
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return invoke(
        add as unsafe extern "C" fn(*mut *mut i8) -> i32,
        argv,
    );
}
"#,
        &config,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_raw_c_exposed_field_slot_typechecks() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("invoke".to_string());
    run_test_with_config(
        r#"
pub type CommandFn = unsafe extern "C" fn(*mut *mut i8) -> i32;

#[repr(C)]
pub struct Command {
    pub run: (CommandFn, i32),
}

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

#[no_mangle]
pub unsafe extern "C" fn invoke(command: *mut Command, mut argv: *mut *mut i8) -> i32 {
    return ((*command).run.0)(argv) + (*command).run.1;
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let mut command = Command {
        run: (add as unsafe extern "C" fn(*mut *mut i8) -> i32, 11),
    };
    return invoke(&mut command as *mut Command, argv);
}
"#,
        &config,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_mixed_local_and_foreign_callbacks_typechecks() {
    run_test(
        r#"
extern "C" {
    fn raw_add(argv: *mut *mut i8) -> i32;
}

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn dispatch(
    use_local: bool,
    mut argv: *mut *mut i8,
) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let handler: unsafe extern "C" fn(*mut *mut i8) -> i32 =
        if use_local {
            add as unsafe extern "C" fn(*mut *mut i8) -> i32
        } else {
            raw_add as unsafe extern "C" fn(*mut *mut i8) -> i32
        };
    return handler(argv);
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_rewritten_callback_with_raw_argument_typechecks() {
    run_test(
        r#"
extern "C" {
    fn raw_touch(argv: *mut *mut i8);
}

pub type CommandFn = Option<unsafe extern "C" fn(*mut *mut i8) -> i32>;

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn dispatch(
    cb: CommandFn,
    mut argv: *mut *mut i8,
) -> i32 {
    raw_touch(argv);
    return cb.expect("command")(argv);
}

pub unsafe extern "C" fn call(mut argv: *mut *mut i8) -> i32 {
    return dispatch(
        Some(add as unsafe extern "C" fn(*mut *mut i8) -> i32),
        argv,
    );
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_explicit_cast_destination_typechecks() {
    run_test(
        r#"
pub type CommandFn = unsafe extern "C" fn(*mut *mut i8) -> i32;

pub unsafe extern "C" fn add(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    return 0;
}

pub unsafe extern "C" fn choose(use_add: bool) -> CommandFn {
    if use_add {
        return add as unsafe extern "C" fn(*mut *mut i8) -> i32;
    }
    return add as unsafe extern "C" fn(*mut *mut i8) -> i32;
}

pub unsafe extern "C" fn dispatch(mut argv: *mut *mut i8) -> i32 {
    *argv.offset(0) = core::ptr::null_mut();
    let handler = choose(true);
    return handler(argv);
}
"#,
        &[],
        &[],
    );
}

#[test]
fn test_fn_pointer_contract_c_exposed_scalar_input_raw_output_field_typechecks() {
    let mut config = Config::default();
    config.c_exposed_fns.insert("init_allocator".to_string());
    run_test_with_config(
        r#"
pub type size_t = usize;

#[repr(C)]
pub struct Allocator {
    pub gmalloc: Option<unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void>,
    pub gfree: Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> ()>,
}

unsafe extern "C" fn fail_malloc(len: size_t) -> *mut core::ffi::c_void {
    if len == 0 {
        return core::ptr::null_mut();
    }
    return core::ptr::null_mut();
}

unsafe extern "C" fn fail_free(_ptr: *mut core::ffi::c_void) {}

pub static mut ALLOCATOR: Allocator = Allocator {
    gmalloc: Some(fail_malloc as unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void),
    gfree: Some(fail_free as unsafe extern "C" fn(*mut core::ffi::c_void) -> ()),
};

#[no_mangle]
pub unsafe extern "C" fn init_allocator(allocator: *mut Allocator) {
    (*allocator).gmalloc =
        Some(fail_malloc as unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void);
    (*allocator).gfree = Some(fail_free as unsafe extern "C" fn(*mut core::ffi::c_void) -> ());
}

pub unsafe extern "C" fn allocate(len: size_t) -> *mut core::ffi::c_void {
    let p: *mut core::ffi::c_void =
        (ALLOCATOR.gmalloc).expect("non-null function pointer")(len);
    if p.is_null() {
        return core::ptr::null_mut();
    }
    return p;
}
"#,
        &config,
        &["expect(\"non-null function pointer\")(len)"],
        &["len as *mut", "(len)."],
    );
}

#[test]
fn test_raw_offset_to_slice_local_checks_null() {
    let (s, _) = rewrite_with_config(
        r#"
#[repr(C)]
pub struct S {
    pub x: *mut i32,
}

pub unsafe fn foo(mut p: *mut S, x: i32, y: i32) -> i32 {
    let mut q: *mut i32 = ((*p).x).offset(x as isize);
    if y != 0 {
        return *q.offset(1);
    }
    return 0;
}

pub unsafe fn bar(mut p: *mut S) {
    let mut q: *mut i32 = (*p).x;
    *(*p).x = 1;
    *q = 1;
}

pub unsafe fn caller() -> i32 {
    let mut s = S { x: 0 as *mut i32 };
    return foo(&mut s, 0, 0);
}
"#,
        &Config::default(),
    );
    ::utils::compilation::run_compiler_on_str(&s, ::utils::type_check).expect(&s);

    assert!(s.contains("let mut q: &[i32]"), "{s}");
    assert!(
        s.contains("let mut q: &[i32] =\n        if ((p.x).offset(x as isize)).is_null()"),
        "{s}"
    );
    assert!(
        !s.contains("let mut q: &[i32] =\n        std::slice::from_raw_parts"),
        "{s}"
    );
}

#[test]
fn test_direct_call_mutability_contract_const_arg_to_mut_slice() {
    run_test(
        r#"
pub unsafe fn write_word(mut words: *mut i32, idx: usize) {
    *words.offset(idx as isize) = 99;
}

pub unsafe extern "C" fn dispatch(mut words: *const i32, idx: usize) -> i32 {
    let before = *words.offset(idx as isize);
    write_word((words as *mut i32), idx);
    return before;
}
"#,
        &[
            "fn write_word(mut words: &mut [i32], idx: usize)",
            "fn dispatch(mut words: &[i32], idx: usize) -> i32",
            "write_word(if (words).is_empty()",
            "std::slice::from_raw_parts_mut((words).as_ptr().cast_mut()",
        ],
        &["write_word((words), idx)"],
    );
}

#[test]
fn test_direct_call_mutability_contract_local_cast_arg_to_mut_slice() {
    run_test(
        r#"
pub unsafe fn write_slot(mut slots: *mut i16, idx: usize) {
    *slots.offset(idx as isize) = 7;
}

pub unsafe extern "C" fn dispatch(mut slots: *const i16, idx: usize) -> i16 {
    let local: *const i16 = slots;
    let before = *local.offset(idx as isize);
    write_slot(((local as *const i16) as *mut i16), idx);
    return before;
}
"#,
        &[
            "fn write_slot(mut slots: &mut [i16], idx: usize)",
            "let local: &[i16]",
            "write_slot(if (local).is_empty()",
            "std::slice::from_raw_parts_mut((local).as_ptr().cast_mut()",
        ],
        &["write_slot((local), idx)", "write_slot(((local"],
    );
}

#[test]
fn test_direct_call_mutability_contract_local_arg_to_mut_cursor() {
    run_test(
        r#"
pub unsafe fn write_previous(mut words: *mut i32) {
    *words.offset(-1) = 5;
}

pub unsafe extern "C" fn dispatch(mut words: *const i32) -> i32 {
    let cursor: *const i32 = words;
    let before = *cursor.offset(-1);
    write_previous((cursor as *mut i32));
    return before;
}
"#,
        &[
            "pub unsafe fn write_previous(mut words: *mut i32)",
            "let cursor: *const i32 = words;",
            "write_previous((cursor as *mut i32) as *mut i32);",
        ],
        &[
            "crate::slice_cursor::SliceCursorMut<'_, i32>",
            "let cursor: crate::slice_cursor::SliceCursor<'_, i32>",
        ],
    );
}

#[test]
fn test_struct_array_field_as_mut_ptr_to_cursor_uses_field_slice() {
    run_test(
        r#"
#![deny(dangerous_implicit_autorefs)]

#[repr(C)]
pub struct Holder {
    pub values: [i32; 4],
}

pub unsafe fn write_at(mut values: *mut i32, idx: isize) {
    *values.offset(idx) = 7;
}

pub unsafe extern "C" fn dispatch(mut holder: *mut Holder, idx: isize) {
    write_at((*holder).values.as_mut_ptr(), idx);
}
"#,
        &[
            "crate::slice_cursor::SliceCursorMut<'_, i32>",
            "write_at(crate::slice_cursor::SliceCursorMut::new(&mut (&mut ((*holder).values))[..])",
        ],
        &[
            "write_at((*holder).values.as_mut_ptr(), idx)",
            "SliceCursorMut::from_raw_parts_mut",
        ],
    );
}

#[test]
fn test_struct_array_field_as_ptr_to_cursor_uses_field_slice() {
    run_test(
        r#"
#![deny(dangerous_implicit_autorefs)]

#[repr(C)]
pub struct Holder {
    pub values: [i32; 4],
}

pub unsafe fn read_at(mut values: *const i32, idx: isize) -> i32 {
    *values.offset(idx)
}

pub unsafe extern "C" fn dispatch(holder: *const Holder, idx: isize) -> i32 {
    read_at((*holder).values.as_ptr(), idx)
}
"#,
        &[
            "mut values: crate::slice_cursor::SliceCursor<'_, i32>",
            "read_at(crate::slice_cursor::SliceCursor::new(&(&((*holder).values))[..])",
        ],
        &[
            "read_at((*holder).values.as_ptr(), idx)",
            "SliceCursor::from_raw_parts",
        ],
    );
}

#[test]
fn test_raw_parent_struct_array_field_as_mut_ptr_to_cursor_uses_field_slice() {
    run_test(
        r#"
#![deny(dangerous_implicit_autorefs)]

#[repr(C)]
pub struct Holder {
    pub values: [i32; 4],
}

pub static mut HOLDER_SLOT: *mut Holder = 0 as *mut Holder;

pub unsafe fn write_at(mut values: *mut i32, idx: isize) {
    *values.offset(idx) = 7;
}

pub unsafe fn dispatch(idx: isize) {
    let holder = HOLDER_SLOT;
    write_at((*holder).values.as_mut_ptr(), idx);
}
"#,
        &[
            "crate::slice_cursor::SliceCursorMut<'_, i32>",
            "write_at(crate::slice_cursor::SliceCursorMut::new(&mut (&mut ((*holder).values))[..])",
        ],
        &[
            "write_at((*holder).values.as_mut_ptr(), idx)",
            "SliceCursorMut::from_raw_parts_mut",
        ],
    );
}

#[test]
fn test_raw_parent_struct_array_field_as_ptr_to_cursor_uses_field_slice() {
    run_test(
        r#"
#![deny(dangerous_implicit_autorefs)]

#[repr(C)]
pub struct Holder {
    pub values: [i32; 4],
}

pub static mut HOLDER_SLOT: *const Holder = 0 as *const Holder;

pub unsafe fn read_at(mut values: *const i32, idx: isize) -> i32 {
    *values.offset(idx)
}

pub unsafe fn dispatch(idx: isize) -> i32 {
    let holder = HOLDER_SLOT;
    read_at((*holder).values.as_ptr(), idx)
}
"#,
        &[
            "mut values: crate::slice_cursor::SliceCursor<'_, i32>",
            "read_at(crate::slice_cursor::SliceCursor::new(&(&((*holder).values))[..])",
        ],
        &[
            "read_at((*holder).values.as_ptr(), idx)",
            "SliceCursor::from_raw_parts",
        ],
    );
}

#[test]
fn test_direct_call_mutability_contract_cursor_arg_to_mut_slice() {
    run_test(
        r#"
pub unsafe fn write_window(mut words: *mut i32, idx: usize) {
    *words.offset(idx as isize) = 11;
}

pub unsafe extern "C" fn dispatch(mut words: *const i32, idx: usize) -> i32 {
    let cursor: *const i32 = words;
    let before = *cursor.offset(-1);
    write_window((cursor as *mut i32), idx);
    return before;
}
"#,
        &[
            "fn write_window(mut words: &mut [i32], idx: usize)",
            "let cursor: *const i32 = words;",
            "write_window(if (cursor).is_null()",
            "std::slice::from_raw_parts_mut((cursor) as *mut _,",
            ::utils::FALLBACK_SLICE_LEN,
        ],
        &[
            "let cursor: crate::slice_cursor::SliceCursor<'_, i32>",
            "write_window((cursor).as_slice_mut(), idx)",
        ],
    );
}

#[test]
fn test_direct_call_mutability_contract_slice_arg_to_mut_cursor() {
    run_test(
        r#"
pub unsafe fn write_previous(mut words: *mut i32) {
    *words.offset(-1) = 5;
}

pub unsafe extern "C" fn anchor(mut words: *const i32) -> i32 {
    let cursor: *const i32 = words;
    let before = *cursor.offset(-1);
    write_previous((cursor as *mut i32));
    return before;
}

pub unsafe extern "C" fn dispatch(words: &[i32]) -> i32 {
    let before = words[0];
    write_previous(words.as_ptr() as *mut i32);
    return before;
}
"#,
        &[
            "pub unsafe fn write_previous(mut words: *mut i32)",
            "fn dispatch(words: &[i32]) -> i32",
            "write_previous(((words).as_ptr()).cast_mut())",
        ],
        &[
            "crate::slice_cursor::SliceCursorMut<'_, i32>",
            "write_previous(crate::slice_cursor::SliceCursorMut::from_raw_parts_mut",
            "write_previous((words).as_ptr() as",
        ],
    );
}

#[test]
fn test_root6_mut_cursor_shared_call_then_index_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
pub unsafe fn root6_peek_prev(mut cursor: *const i32) -> i32 {
    return *cursor.offset(-1);
}

pub unsafe fn root6_param_call_then_index(mut stack: *mut i32) -> i32 {
    let before = root6_peek_prev(stack as *const i32);
    *stack.offset(-1) = before + 1;
    return *stack.offset(-1);
}
"#,
        &[
            "root6_peek_prev",
            "pub unsafe fn root6_peek_prev(mut cursor: *const i32)",
            "root6_param_call_then_index",
            "pub unsafe fn root6_param_call_then_index(mut stack: *mut i32)",
        ],
        &["crate::slice_cursor::SliceCursor"],
    );
}

#[test]
fn test_root6_loop_shared_calls_then_mut_cursor_write_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
pub unsafe fn root6_peek_prev(mut cursor: *const i32) -> i32 {
    return *cursor.offset(-1);
}

pub unsafe fn root6_peek_two_back(mut cursor: *const i32) -> i32 {
    return *cursor.offset(-2);
}

pub unsafe fn root6_loop_calls_then_write(mut stack: *mut i32, mut count: i32) -> i32 {
    let mut total = 0;
    while count > 0 {
        total += root6_peek_prev(stack as *const i32);
        total += root6_peek_two_back(stack as *const i32);
        *stack.offset(-1) = total;
        count -= 1;
    }
    return total + *stack.offset(-1);
}
"#,
        &[
            "root6_peek_prev",
            "root6_peek_two_back",
            "pub unsafe fn root6_peek_prev(mut cursor: *const i32)",
            "pub unsafe fn root6_peek_two_back(mut cursor: *const i32)",
            "root6_loop_calls_then_write",
            "pub unsafe fn root6_loop_calls_then_write(mut stack: *mut i32",
        ],
        &["crate::slice_cursor::SliceCursor"],
    );
}

#[test]
fn test_root6_shared_local_from_mut_cursor_then_mut_use_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
pub unsafe fn root6_local_shared_then_mut_use(mut stack: *mut i32) -> i32 {
    let view: *const i32 = stack as *const i32;
    let before = *view.offset(-1);
    *stack.offset(-1) = before + 2;
    return *stack.offset(-1);
}
"#,
        &[
            "root6_local_shared_then_mut_use",
            "pub unsafe fn root6_local_shared_then_mut_use(mut stack: *mut i32)",
            "let view: *const i32 = stack as *const i32;",
        ],
        &["crate::slice_cursor::SliceCursor"],
    );
}

#[test]
fn test_root6_raw_origin_offset_call_then_write_stays_raw_typechecks() {
    run_typecheck_test_after_shape_check(
        r#"
pub unsafe fn root6_peek_prev_after_offset(mut cursor: *const i32) -> i32 {
    return *cursor.offset(-1);
}

pub unsafe fn root6_offset_call_then_write(mut stack: *mut i32) -> i32 {
    stack = stack.offset(1);
    let before = root6_peek_prev_after_offset(stack as *const i32);
    *stack.offset(-1) = before + 3;
    return *stack.offset(-1);
}
"#,
        &[
            "root6_peek_prev_after_offset",
            "pub unsafe fn root6_peek_prev_after_offset(mut cursor: *const i32) -> i32",
            "*cursor.offset(-1)",
            "root6_offset_call_then_write",
            "pub unsafe fn root6_offset_call_then_write(mut stack: *mut i32) -> i32",
            "*stack.offset(-1) = before + 3",
        ],
        &["crate::slice_cursor::SliceCursor"],
    );
}
