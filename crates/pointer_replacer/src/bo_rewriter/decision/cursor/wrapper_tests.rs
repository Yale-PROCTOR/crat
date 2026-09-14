use super::tests::{compile, emitted};

#[test]
fn slicecursor_strrwd_backward_walk() {
    let input = r#"
unsafe extern "C" { fn strdup(p: *const i8) -> *mut i8; }
pub unsafe fn strrwd(base: &[i8], n: usize) -> *mut i8 {
    let mut ptr: *const i8 = base.as_ptr().add(n);
    while *ptr != 47 { ptr = ptr.offset(-1); }
    strdup(ptr)
}
"#;
    let source = emitted(input);
    save_fixture("strrwd", input, &source);
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "wrapper absent: {source}"
    );
    assert!(source.contains(".seek("), "backward seek absent: {source}");
    assert!(
        source.contains(".as_ptr()"),
        "strdup raw boundary absent: {source}"
    );
    compile(
        &source,
        Some(
            r#"unsafe extern "C" { fn free(p: *mut core::ffi::c_void); } fn main() { let s = [47i8, 97, 98, 0]; let p = unsafe { strrwd(&s, 2) }; assert_eq!(unsafe { std::ffi::CStr::from_ptr(p) }.to_bytes(), b"/ab"); unsafe { free(p.cast()); } }"#,
        ),
    );
}

#[test]
fn slicecursor_tulip_previous_output_read() {
    let input = r#"
pub unsafe fn previous_output(output: &mut [f64], n: usize, k: isize) {
    let mut p: *mut f64 = output.as_mut_ptr();
    let mut i = 0usize;
    while i < n {
        if i >= k as usize { *p = *p.offset(-k) + 1.; }
        p = p.add(1);
        i += 1;
    }
}
"#;
    let source = emitted(input);
    save_fixture("previous-output", input, &source);
    assert!(
        source.contains("slice_cursor::SliceCursorMut"),
        "wrapper absent: {source}"
    );
    assert!(source.contains(".seek("), "advance absent: {source}");
    compile(
        &source,
        Some(
            "fn main() { let mut a = [1., 2., 0., 0., 0.]; unsafe { previous_output(&mut a, 5, 2); } assert_eq!(a, [1., 2., 2., 3., 3.]); }",
        ),
    );
}

#[test]
fn slicecursor_urlparser_native_parameter() {
    let input = r#"
unsafe extern "C" { fn strdup(p: *const i8) -> *mut i8; }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn strrwd(mut ptr: *mut i8, n: i32) -> *mut i8 {
    let mut i = 0;
    while i < n {
        let fresh = *ptr;
        ptr = ptr.offset(-1);
        let _y = fresh as i32;
        i += 1;
    }
    strdup(ptr)
}
"#;
    let source = emitted(input);
    save_fixture("native-strrwd", input, &source);
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "native wrapper absent: {source}"
    );
    assert!(
        source.contains(".seek("),
        "native parameter seek absent: {source}"
    );
}

#[test]
fn slicecursor_parameter_local_call() {
    let source = emitted(
        "unsafe fn walk(p: *const i32, k: isize) -> i32 { *p.offset(k) } pub unsafe fn caller(p: *const i32, k: isize) -> i32 { walk(p, k) }",
    );
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "parameter cursor absent: {source}"
    );
}

#[test]
fn slicecursor_nullable_parameter() {
    let source = emitted(
        "pub unsafe fn walk(p: *const i32, k: isize) -> i32 { if p.is_null() { 0 } else { *p.offset(k) } }",
    );
    assert!(
        source.contains(".map(crate::slice_cursor::SliceCursor::new)"),
        "nullable cursor absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { assert_eq!(unsafe { walk(None, -1) }, 0); assert_eq!(unsafe { walk(Some(&[3,4]), 1) }, 4); }",
        ),
    );
}

#[test]
fn slicecursor_undelivered_table_is_held() {
    let input = "pub unsafe fn previous(outputs: *mut *mut f64, k: isize) -> f64 { let output: *mut f64 = *outputs.offset(0); *output.offset(k) }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("output"))
            .unwrap();
        let super::Decision::Degraded(record) = decision else {
            panic!("raw table admitted: {decision:?}");
        };
        assert_eq!(record.reason.key(), "cursor-base-unavailable");
    })
    .unwrap();
}

#[test]
fn slicecursor_cast_table_is_held() {
    let input = "pub unsafe fn previous(outputs: *mut *mut f64, k: isize) -> f64 { let output: *mut f64 = (*outputs.offset(0)) as *mut f64; *output.offset(k) }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("output"))
            .unwrap();
        let super::Decision::Degraded(record) = decision else {
            panic!("raw table admitted: {decision:?}");
        };
        assert_eq!(record.reason.key(), "cursor-base-unavailable");
    })
    .unwrap();
}

fn save_fixture(name: &str, input: &str, output: &str) {
    if let Some(directory) = std::env::var_os("CRAT_SLICECURSOR_WITNESS_OUTPUT") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join(format!("{name}.before.rs")), input).unwrap();
        std::fs::write(directory.join(format!("{name}.after.rs")), output).unwrap();
    }
}

#[test]
fn slicecursor_nullable_local_none_then_delivered_base() {
    let input = "pub unsafe fn walk(a: &[i32], yes: bool) -> i32 { let mut p: *const i32 = core::ptr::null(); if yes { p = a.as_ptr().add(2); } if p.is_null() { 0 } else { *p.offset(-1) } }";
    let source = emitted(input);
    assert!(
        source.contains("Option<crate::slice_cursor::SliceCursor"),
        "optional local wrapper absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { assert_eq!(unsafe { walk(&[3,4,5],false) },0); assert_eq!(unsafe { walk(&[3,4,5],true) },4); }",
        ),
    );
}

#[test]
fn slicecursor_alias_of_raw_table_is_held() {
    let input = "pub unsafe fn previous(outputs: *mut *mut f64, k: isize) -> f64 { let loaded: *mut f64 = *outputs.offset(0); let output: *mut f64 = loaded; *output.offset(k) }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("output"))
            .unwrap();
        let super::Decision::Degraded(record) = decision else {
            panic!("raw table admitted: {decision:?}");
        };
        assert_eq!(record.reason.key(), "cursor-base-unavailable");
    })
    .unwrap();
}

#[test]
fn slicecursor_difference_and_comparison_use_raw_address_receipts() {
    let input = "pub unsafe fn inspect(a: &[i32], k: isize) -> (i32, bool, isize) { let p: *const i32 = a.as_ptr().add(2); let q: *const i32 = a.as_ptr(); (*p.offset(k), p < q, p.offset_from(q)) }";
    let source = emitted(input);
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "address cursor absent: {source}"
    );
    compile(
        &source,
        Some("fn main() { assert_eq!(unsafe { inspect(&[10,20,30,40], -1) }, (20,false,2)); }"),
    );
}

#[test]
fn slicecursor_shared_offset_copy() {
    let source = emitted(
        "pub unsafe fn inspect(a: &[i32]) -> i32 { let p: *const i32 = a.as_ptr().add(2); let q: *const i32 = p.offset(1); *q.offset(-1) + *p.offset(-1) }",
    );
    assert!(
        source.contains("q: crate::slice_cursor::SliceCursor"),
        "derived cursor absent: {source}"
    );
    compile(
        &source,
        Some("fn main() { assert_eq!(unsafe { inspect(&[10,20,30,40]) },50); }"),
    );
}

#[test]
fn slicecursor_mutable_offset_reborrow() {
    let source = emitted(
        "pub unsafe fn inspect(a: &mut [i32]) -> i32 { let p: *mut i32 = a.as_mut_ptr().add(2); { let q: *mut i32 = p.offset(1); *q.offset(-1) = 9; } *p.offset(-1) }",
    );
    assert!(
        source.contains(".as_deref_mut()"),
        "derived reborrow absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let mut a=[1,2,3,4]; assert_eq!(unsafe { inspect(&mut a) },2); assert_eq!(a,[1,2,9,4]); }",
        ),
    );
}
