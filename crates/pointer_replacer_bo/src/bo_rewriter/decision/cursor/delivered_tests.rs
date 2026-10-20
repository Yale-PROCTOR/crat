//! Relay 009 native witnesses: retain an already delivered slice and advance
//! only its administrative index. No synthetic model supplies Ref authority.

use super::tests::{compile, emitted};

fn assert_cursor(source: &str, element: &str) {
    assert!(
        source.contains("::core::primitive::usize")
            && source.contains("checked_add")
            && source.contains(&format!("&mut [{element}]")),
        "delivered slice plus checked cursor index missing: {source}"
    );
    assert!(
        !source.contains("p = p.add(1)"),
        "raw self-advance survived the cursor rewrite: {source}"
    );
}

const CHECK_WRITES: &str = r#"
fn main() {
    for n in [0usize, 1, 4] {
        let mut values = vec![0i32; n];
        unsafe { witness(&mut values); }
        assert_eq!(values, vec![7i32; n]);
    }
}
"#;

#[test]
fn delivered_slice_parameter_postincrement_loop_emits_cursor() {
    let source = emitted(
        r#"
pub unsafe fn witness(output: &mut [i32]) {
    let n = output.len();
    let mut p: *mut i32 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < n {
        *p = 7;
        p = p.add(1);
        i += 1;
    }
}
"#,
    );
    assert_cursor(&source, "i32");
    compile(&source, Some(CHECK_WRITES));
}

#[test]
fn delivered_local_slice_postincrement_loop_emits_cursor() {
    let source = emitted(
        r#"
pub unsafe fn witness(values: &mut [i32]) {
    let output: &mut [i32] = values;
    let n = output.len();
    let mut p: *mut i32 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < n {
        *p = 7;
        p = p.add(1);
        i += 1;
    }
}
"#,
    );
    assert_cursor(&source, "i32");
    compile(&source, Some(CHECK_WRITES));
}

#[test]
fn delivered_boxed_slice_view_keeps_the_owner_in_its_caller() {
    // The native frontend consumes C-like inputs; an already emitted Box is
    // exercised in the compiled caller, which lends its full slice to this
    // same delivered-parameter lowering rather than moving/reconstructing it.
    let source = emitted(
        r#"
pub unsafe fn witness(output: &mut [i32]) {
    let n = output.len();
    let mut p: *mut i32 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < n { *p = 7; p = p.add(1); i += 1; }
}
"#,
    );
    assert_cursor(&source, "i32");
    compile(
        &source,
        Some(
            r#"
fn main() {
    for n in [0usize, 1, 4] {
        let mut ff = vec![0i32; n].into_boxed_slice();
        unsafe { witness(&mut *ff); }
        assert_eq!(&*ff, vec![7i32; n].as_slice());
    }
}
"#,
        ),
    );
}

#[test]
fn delivered_fallback_inner_slice_reuses_its_existing_construction() {
    let source = emitted(
        r#"
const FALLBACK_SLICE_EXTENT: usize = 1024;
pub unsafe fn witness(raw: *mut f64) {
    let output: &mut [f64] =
        core::slice::from_raw_parts_mut(raw, FALLBACK_SLICE_EXTENT);
    walk(output);
}
unsafe fn walk(output: &mut [f64]) {
    let n = output.len();
    let mut p: *mut f64 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < n {
        *p = 7.0;
        p = p.add(1);
        i += 1;
    }
}
"#,
    );
    assert_cursor(&source, "f64");
    assert_eq!(
        source.matches("from_raw_parts_mut").count(),
        1,
        "cursor introduced another slice construction: {source}"
    );
    assert_eq!(
        source.matches("const FALLBACK_SLICE_EXTENT").count(),
        1,
        "cursor introduced another fabricated extent: {source}"
    );
    // Allocate the full declared extent: this finite runtime witness exercises
    // the existing constructor without relying on slice-length UB or a waiver.
    compile(
        &source,
        Some(
            "fn main() { let mut values = vec![0.0f64; 1024]; unsafe { witness(values.as_mut_ptr()); } assert!(values.iter().all(|v| *v == 7.0)); }",
        ),
    );
}

fn assert_no_cursor(input: &str) {
    utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.param_name.as_deref() == Some("p"))
            .expect("the raw cursor subject must be inventoried");
        assert!(
            !matches!(decision, super::Decision::Cursor { .. }),
            "unproved delivered-base cursor was admitted: {decision:?}"
        );
    })
    .unwrap();
}

#[test]
fn delivered_cursor_requires_an_actual_slice_base() {
    assert_no_cursor(
        r#"
pub unsafe fn witness(raw: *mut i32, n: usize) {
    let mut p: *mut i32 = raw;
    let mut i: usize = 0;
    while i < n { *p = 7; p = p.add(1); i += 1; }
}
"#,
    );
}

#[test]
fn delivered_cursor_trip_count_must_join_the_same_window() {
    // Both functions can be called on UB-free inputs; neither establishes the
    // relation to output.len() needed for unrestricted cursor admission.
    for bound in ["other.len()", "n"] {
        assert_no_cursor(&format!(
            r#"
pub unsafe fn witness(output: &mut [i32], other: &[i32], n: usize) {{
    let mut p: *mut i32 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < {bound} {{ *p = 7; p = p.add(1); i += 1; }}
}}
"#
        ));
    }
}

#[test]
fn delivered_cursor_checks_each_intermediate_step() {
    // Compile-only: leaving the carried window and returning must not be
    // admitted merely because the final dereference is at the starting index.
    assert_no_cursor(
        r#"
pub unsafe fn witness(output: &mut [i32]) {
    let mut p: *mut i32 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < output.len() {
        *p.sub(1).add(1) = 7;
        p = p.add(1);
        i += 1;
    }
}
"#,
    );
}

#[test]
fn delivered_cursor_closes_implicit_and_pattern_borrows_of_loop_state() {
    for mutation in ["n.clone_from(&0);", "let ref mut alias = n; *alias = 0;"] {
        assert_no_cursor(&format!(
            r#"
pub unsafe fn witness(output: &mut [i32]) {{
    let mut n = output.len();
    {mutation}
    let mut p: *mut i32 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < n {{ *p = 7; p = p.add(1); i += 1; }}
}}
"#
        ));
    }
    assert_no_cursor(
        r#"
pub unsafe fn witness(output: &mut [i32]) {
    let n = output.len();
    let mut p: *mut i32 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < n { let ref mut alias = i; *alias = 0; *p = 7; p = p.add(1); i += 1; }
}
"#,
    );
}

#[test]
fn delivered_postincrement_raw_temporary_keeps_one_access_and_order() {
    let source = emitted(
        r#"
pub unsafe fn witness(output: &mut [i32]) {
    let n = output.len();
    let mut p: *mut i32 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < n {
        let fresh = p;
        p = p.add(1);
        *fresh = 7;
        i += 1;
    }
}
"#,
    );
    assert_cursor(&source, "i32");
    assert!(
        source.contains("as_mut_ptr().add"),
        "current-index raw temporary missing: {source}"
    );
    compile(&source, Some(CHECK_WRITES));
}

#[test]
fn delivered_postincrement_temporary_cannot_escape_or_reborrow_the_base() {
    for rhs in ["output.len() as i32", "unsafe { *p }"] {
        assert_no_cursor(&format!(
            r#"
pub unsafe fn witness(output: &mut [i32]) {{
    let n = output.len(); let mut p:*mut i32=output.as_mut_ptr(); let mut i:usize=0;
    while i<n {{ let fresh=p; p=p.add(1); *fresh={rhs}; i+=1; }}
}}
"#
        ));
    }
    assert_no_cursor(
        r#"
pub unsafe fn witness(output: &mut [i32]) {
    let n=output.len(); let mut p:*mut i32=output.as_mut_ptr(); let mut i:usize=0;
    while i<n { let fresh=p; p=p.add(1); *fresh=7; let escaped=fresh; i+=1; }
}
"#,
    );
}

#[test]
fn raw_pointer_table_does_not_supply_an_inner_delivered_binding() {
    // Measured native model makes output and p Raw. This is a held source
    // premise, not permission to invent a from_raw_parts construction.
    assert_no_cursor(
        r#"
pub unsafe fn witness(outputs: *const *mut i32) {
    let output: *mut i32 = *outputs;
    *output.add(0) = 0;
    let mut p: *mut i32 = output;
    let mut i: usize = 0;
    while i < 4 { *p = 7; p = p.add(1); i += 1; }
}
"#,
    );
}

#[test]
fn pointer_table_inner_slice_keeps_its_existing_binding_and_constructor() {
    let source = emitted(
        r#"
const FALLBACK_SLICE_EXTENT:usize=1024;
pub unsafe fn witness(outputs: &[*mut i32]) {
    let output:&mut[i32]=core::slice::from_raw_parts_mut(outputs[0],FALLBACK_SLICE_EXTENT);
    let n=output.len(); let mut p:*mut i32=output.as_mut_ptr(); let mut i:usize=0;
    while i<n { let fresh=p; p=p.add(1); *fresh=7; i+=1; }
}
"#,
    );
    assert_cursor(&source, "i32");
    assert_eq!(
        source.matches("from_raw_parts_mut").count(),
        1,
        "duplicate constructor: {source}"
    );
    compile(
        &source,
        Some(
            "fn main(){let mut v=vec![0i32;1024];unsafe{witness(&[v.as_mut_ptr()]);}assert!(v.iter().all(|v|*v==7));}",
        ),
    );
}

#[test]
fn delivered_cursor_rejects_implicit_element_method_borrows() {
    // Even a harmless builtin receiver borrow must take the unbuilt-method
    // hold; arbitrary retaining methods cannot enter through this spelling.
    assert_no_cursor(
        r#"
pub unsafe fn witness(output:&mut[i32]) {
    let n=output.len(); let mut p:*mut i32=output.as_mut_ptr(); let mut i:usize=0;
    while i<n { (*p).clone_from(&7); p=p.add(1); i+=1; }
}
"#,
    );
}

#[test]
fn delivered_cursor_successor_must_stay_inside_the_same_window() {
    assert_no_cursor(
        r#"
pub unsafe fn witness(output:&mut[i32]) {
    let n=output.len(); let mut p:*mut i32=output.as_mut_ptr(); let mut i:usize=0;
    while i<n { *p=7; p=p.add(2); i+=1; }
}
"#,
    );
}

#[test]
fn delivered_cursor_t1_reader_observes_the_current_index() {
    let source = emitted(
        r#"
unsafe fn read(p:*const i32)->i32 {p.read()}
pub unsafe fn witness(output:&[i32])->i32 {
    let n=output.len(); let mut p:*const i32=output.as_ptr(); let mut i:usize=0; let mut sum=0;
    while i<n { sum+=read(p); p=p.add(1); i+=1; }
    sum
}
"#,
    );
    assert!(
        source.contains("checked_add") && source.contains(".as_ptr().add"),
        "current-index T1 missing: {source}"
    );
    compile(
        &source,
        Some(
            "fn main(){assert_eq!(unsafe{witness(&[2,3,5])},10);assert_eq!(unsafe{witness(&[])},0);}",
        ),
    );
}
