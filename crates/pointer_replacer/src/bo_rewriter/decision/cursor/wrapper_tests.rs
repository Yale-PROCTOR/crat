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
fn slicecursor_written_table_element_is_admitted_when_loaded_once() {
    // Expectation migrated (relay 003): a written element loaded once from the
    // table is the function's only view of its buffer and takes the exclusive
    // fallback base.
    let input = "pub unsafe fn previous(outputs: *mut *mut f64, k: isize) { let output: *mut f64 = *outputs.offset(0); *output.offset(k) = 1.; }";
    let source = emitted(input);
    assert!(
        source.contains("crate::slice_cursor::SliceCursorMut::from_raw_parts_mut(outputs["),
        "exclusive fallback base absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let mut a = [0., 0., 0.]; let mut t = [a.as_mut_ptr()]; unsafe { previous(&mut t, 2) }; assert_eq!(a, [0., 0., 1.]); }",
        ),
    );
}

#[test]
fn slicecursor_written_table_element_mutable_element_read_only_stays_shared() {
    // Hold pin kept from the pre-relay-003 form: a written element whose table is
    // loaded twice never takes a mutable view (see the second-view witness); a
    // read-only element still takes the shared form even when loaded twice.
    let input = "pub unsafe fn previous(outputs: *const *mut f64, k: isize) -> f64 { let output: *mut f64 = *outputs.offset(0); *output.offset(k) + *(*outputs.offset(0)).offset(1) }";
    let source = emitted(input);
    assert!(
        source.contains("crate::slice_cursor::SliceCursor::from_raw_parts(outputs["),
        "shared fallback base absent: {source}"
    );
    assert!(
        !source.contains("SliceCursorMut::from_raw_parts_mut(outputs["),
        "read-only element must not take a mutable view: {source}"
    );
}

#[test]
fn slicecursor_read_only_element_of_mutable_table_takes_fallback_base() {
    // Expectation migrated from `slicecursor_undelivered_table_is_held`: the
    // read-only element of a delivered outer table is a bare raw base and takes
    // the receipted fallback (charter §1(c)); the `*mut` element coerces to the
    // shared constructor's `*const`.
    let input = "pub unsafe fn previous(outputs: *mut *mut f64, k: isize) -> f64 { let output: *mut f64 = *outputs.offset(0); *output.offset(k) }";
    let source = emitted(input);
    assert!(
        source.contains("crate::slice_cursor::SliceCursor::from_raw_parts(outputs["),
        "fallback base absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let mut a = [1., 2., 3.]; let t = [a.as_mut_ptr()]; assert_eq!(unsafe { previous(&t, 2) }, 3.); }",
        ),
    );
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

#[test]
fn slicecursor_integer_address_escape_is_not_a_scalar_comparison() {
    let source = emitted(
        "pub unsafe fn inspect(a: &mut [i32]) { let p: *mut i32 = a.as_mut_ptr().add(1); let address = p as usize; let q = address as *mut i32; *p.offset(-1) = 3; *q = 4; }",
    );
    assert!(
        !source.contains("slice_cursor::SliceCursor"),
        "integer address escape is not licensed by scalar comparison evidence: {source}"
    );
}

#[test]
fn slicecursor_table_element_shared_fallback_two_inputs() {
    // tulipindicators `ti_adx`: input cursors loaded from the delivered outer
    // table `inputs: &[*const f64]`; the loaded element is a bare raw base.
    let input = r#"
pub unsafe fn adx(size: i32, inputs: *const *const f64) -> f64 {
    let high: *const f64 = *inputs.offset(0);
    let low: *const f64 = *inputs.offset(1);
    let mut acc = 0.;
    let mut i = 1isize;
    while i < size as isize {
        acc += *high.offset(i) - *low.offset(i - 1);
        i += 1;
    }
    acc
}
"#;
    let source = emitted(input);
    save_fixture("table-element-two-inputs", input, &source);
    assert!(
        source.contains("crate::slice_cursor::SliceCursor::from_raw_parts(inputs["),
        "table-element fallback base absent: {source}"
    );
    assert!(
        !source.contains("*inputs.offset"),
        "outer element rewrite lost under the composed constructor: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let h = [1., 2., 4.]; let l = [0.5, 1., 1.5]; let t = [h.as_ptr(), l.as_ptr()]; assert_eq!(unsafe { adx(3, &t) }, 4.5); }",
        ),
    );
}

#[test]
fn slicecursor_table_element_shared_fallback_with_raw_output_table() {
    // tulipindicators `ti_mom`: one shared input cursor beside a forward-only
    // output loaded from a second table; the input takes the receipted
    // fallback base composed over the outer's element rewrite.
    let input = r#"
pub unsafe fn mom(size: i32, inputs: *const *const f64, period: i32, outputs: *const *mut f64) -> i32 {
    let input: *const f64 = *inputs.offset(0);
    let mut output: *mut f64 = *outputs.offset(0);
    let mut i = period;
    while i < size {
        *output = *input.offset(i as isize) - *input.offset((i - period) as isize);
        output = output.offset(1);
        i += 1;
    }
    0
}
"#;
    let source = emitted(input);
    save_fixture("table-element-raw-output", input, &source);
    assert!(
        source.contains("crate::slice_cursor::SliceCursor::from_raw_parts(inputs["),
        "table-element fallback base absent: {source}"
    );
    // The forward-only output is the slice family's existing composed
    // fallback over the same outer-table shape; the cursor mirrors it.
    assert!(
        source.contains("core::slice::from_raw_parts_mut(outputs["),
        "forward-only output fallback absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let x = [1., 3., 6., 10.]; let mut o = [0.; 2]; let t = [x.as_ptr()]; let u = [o.as_mut_ptr()]; assert_eq!(unsafe { mom(4, &t, 2, &u) }, 0); assert_eq!(o, [5., 7.]); }",
        ),
    );
}

#[test]
fn slicecursor_table_element_composition_owns_the_initializer_key() {
    // The outer's element rewrite is composed into the constructor text; the
    // AST use map must carry exactly one edit at the initializer span, with no
    // overwritten key (the census gates `use_key_collisions` at 0).
    let input = r#"
pub unsafe fn adx(size: i32, inputs: *const *const f64) -> f64 {
    let low: *const f64 = *inputs.offset(1);
    let mut acc = 0.;
    let mut i = 1isize;
    while i < size as isize {
        acc += *low.offset(i - 1);
        i += 1;
    }
    acc
}
"#;
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("low"))
            .unwrap();
        let super::Decision::Cursor { plan, .. } = decision else {
            panic!("table element not admitted: {decision:?}");
        };
        assert_eq!(plan.composed_edit_spans.len(), 1, "{plan:?}");
        let init = *ctx
            .constructions
            .init_hirs
            .get(&(subject.fn_did, subject.hir_id))
            .unwrap();
        let init_span = tcx.hir_node(init).expect_expr().span;
        assert_eq!(plan.composed_edit_spans[0], init_span);
        let reverts = crate::bo_rewriter::ast_transform::revert_set_from_classes_and_atoms(
            &std::collections::BTreeSet::new(),
            &std::collections::BTreeSet::new(),
            &table,
        )
        .unwrap();
        let inputs = crate::bo_rewriter::ast_transform::filtered_inputs(&table, &reverts);
        assert_eq!(inputs.use_key_collisions, 0);
        let composed = inputs
            .uses
            .get(&(init_span.lo().0, init_span.hi().0))
            .expect("constructor at the initializer span");
        assert!(
            composed.contains("SliceCursor::from_raw_parts(inputs[1]"),
            "{composed}"
        );
    })
    .unwrap();
}

#[test]
fn slicecursor_written_table_element_takes_exclusive_fallback_base() {
    // tulipindicators `ti_decay`: the output cursor is loaded once from the
    // delivered table, written through `*output++`, and read back at `-1`.
    // The element is the function's only view of that buffer.
    let input = r#"
pub unsafe fn decay(size: i32, inputs: *const *const f64, outputs: *const *mut f64, scale: f64) -> i32 {
    let input: *const f64 = *inputs.offset(0);
    let mut output: *mut f64 = *outputs.offset(0);
    *output = *input.offset(0);
    output = output.offset(1);
    let mut i = 1;
    while i < size {
        let d = *output.offset(-1) - scale;
        *output = if *input.offset(i as isize) > d { *input.offset(i as isize) } else { d };
        output = output.offset(1);
        i += 1;
    }
    0
}
"#;
    let source = emitted(input);
    save_fixture("table-element-written-output", input, &source);
    assert!(
        source.contains("crate::slice_cursor::SliceCursorMut::from_raw_parts_mut(outputs["),
        "exclusive table-element base absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let x = [5., 1., 2., 9.]; let mut o = [0.; 4]; let t = [x.as_ptr()]; let u = [o.as_mut_ptr()]; assert_eq!(unsafe { decay(4, &t, &u, 1.) }, 0); assert_eq!(o, [5., 4., 3., 9.]); }",
        ),
    );
}

#[test]
fn slicecursor_written_table_element_with_second_view_is_held() {
    // A second load of the same table is a second view of a buffer the
    // mutable cursor would claim exclusively; the cursor stays held.
    // The outer stays a delivered slice here (two element loads, one written
    // through the cursor, one read inline), so the refusal is this rule's own.
    let input = "pub unsafe fn previous(outputs: *const *mut f64, k: isize) -> f64 { let output: *mut f64 = *outputs.offset(0); *output.offset(k) = 1.; *(*outputs.offset(0)).offset(1) }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        assert!(
            table
                .entries
                .iter()
                .any(|(s, d)| s.param_name.as_deref() == Some("outputs")
                    && matches!(d, super::Decision::Slice { .. })),
            "fixture premise: the outer table must be a delivered slice"
        );
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("output"))
            .unwrap();
        let super::Decision::Degraded(record) = decision else {
            panic!("second view admitted: {decision:?}");
        };
        assert_eq!(record.reason.key(), "cursor-base-unavailable");
    })
    .unwrap();
}

#[test]
fn slicecursor_written_table_element_with_escaping_table_is_held() {
    // The table itself escaping to a callee is another route to the buffer.
    let input = "unsafe extern \"C\" { fn sink(t: *mut *mut f64); } pub unsafe fn previous(outputs: *mut *mut f64, k: isize) { let output: *mut f64 = *outputs.offset(0); *output.offset(k) = 1.; sink(outputs); }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("output"))
            .unwrap();
        assert!(
            matches!(decision, super::Decision::Degraded(_)),
            "escaping table admitted: {decision:?}"
        );
    })
    .unwrap();
}

#[test]
fn slicecursor_element_as_index_operand_of_another_pointer() {
    // heman `edt`: the cursor's element `*w.offset(k)` is the index operand of
    // another pointer's offset, `*f.offset(*w.offset(k) as isize)`; `k` walks
    // both ways.
    let input = r#"
pub unsafe fn edt(f: *const f32, w: *mut u16, n: i32) -> f32 {
    let mut k = 0i32;
    let mut q = 1i32;
    let mut s = 0f32;
    *w.offset(0) = 0;
    while q < n {
        s = *f.offset(q as isize) - *f.offset(*w.offset(k as isize) as isize);
        if s < 0. { k -= 1; }
        k += 1;
        *w.offset(k as isize) = q as u16;
        q += 1;
    }
    s
}
"#;
    let source = emitted(input);
    save_fixture("element-as-index-operand", input, &source);
    assert!(
        source.contains("slice_cursor::SliceCursorMut"),
        "wrapper absent: {source}"
    );
    assert!(
        source.contains("f[(w[(0isize).wrapping_add((k as isize) as isize)]) as usize]"),
        "element-as-index composition absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let f = [4., 1., 5., 2.]; let mut w = [9u16; 4]; let s = unsafe { edt(&f, &mut w, 4) }; assert_eq!(s, -3.); assert_eq!(w, [1, 3, 9, 9]); }",
        ),
    );
}

#[test]
fn slicecursor_element_as_index_operand_backward_write() {
    // bzip2 `fallbackSimpleSort`: `*eclass.offset(*fmap.offset(j) as isize)`
    // beside `*fmap.offset(j - 4) = *fmap.offset(j)` writes.
    let input = r#"
pub unsafe fn sort(fmap: *mut u32, eclass: *const u32, lo: i32, hi: i32) {
    let mut i = hi - 4;
    while i >= lo {
        let mut j = i + 4;
        while j <= hi && *eclass.offset(*fmap.offset(j as isize) as isize) > 3 {
            *fmap.offset((j - 4) as isize) = *fmap.offset(j as isize);
            j += 4;
        }
        i -= 1;
    }
}
"#;
    let source = emitted(input);
    save_fixture("element-as-index-operand-write", input, &source);
    assert!(
        source.contains("slice_cursor::SliceCursorMut"),
        "wrapper absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let ec = [0u32, 9, 0, 9, 0]; let mut fm = [0u32, 1, 2, 3, 4, 3, 1]; unsafe { sort(&mut fm, &ec, 0, 6) }; assert_eq!(fm, [0, 3, 1, 3, 4, 3, 1]); }",
        ),
    );
}

#[test]
fn slicecursor_returned_derived_pointer_takes_raw_return_bridge() {
    // json.h `json_write_minified_value`: the function keeps its raw return and
    // returns `data.offset(k)` from a bidirectional cursor parameter.
    let input = r#"
pub unsafe fn write_value(kind: i32, data: *mut i8, k: isize) -> *mut i8 {
    if kind == 1 {
        *data.offset(0) = 110;
        *data.offset(1) = 117;
        return data.offset(2);
    }
    let peeked = *data.offset(k);
    *data.offset(0) = peeked;
    data.offset(1)
}
"#;
    let source = emitted(input);
    save_fixture("returned-derived-pointer", input, &source);
    assert!(
        source.contains("slice_cursor::SliceCursorMut"),
        "wrapper absent: {source}"
    );
    assert!(
        source.contains(".as_mut_ptr()"),
        "raw return bridge absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let mut b = [7i8, 7, 7, 7, 9, 7, 7, 7]; let base = b.as_mut_ptr(); let r = unsafe { write_value(1, &mut b[2..], 0) }; assert_eq!(r, unsafe { base.add(4) }); assert_eq!(&b[2..4], &[110, 117]); let r = unsafe { write_value(0, &mut b[2..], 2) }; assert_eq!(r, unsafe { base.add(3) }); assert_eq!(b[2], 9); }",
        ),
    );
}

#[test]
fn slicecursor_whole_cursor_to_local_cursor_parameter() {
    // A cursor passed whole to a local callee whose parameter is itself a
    // wrapper cursor takes the callee's slice form at the seam.
    let input = r#"
pub unsafe fn inner(p: *mut i8, k: isize) -> *mut i8 {
    let peeked = *p.offset(k);
    *p.offset(0) = peeked;
    p.offset(1)
}
pub unsafe fn outer(data: *mut i8, flag: i32, k: isize) -> *mut i8 {
    if flag != 0 {
        return inner(data, k);
    }
    *data.offset(0) = *data.offset(k) + 1;
    data.offset(1)
}
"#;
    let source = emitted(input);
    save_fixture("whole-cursor-to-local-cursor-parameter", input, &source);
    assert!(
        source.contains("data.as_slice_mut()"),
        "cursor-to-cursor seam absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let mut b = [1i8, 2, 3, 4]; let base = b.as_mut_ptr(); let r = unsafe { outer(&mut b[1..], 1, 2) }; assert_eq!(r, unsafe { base.add(2) }); assert_eq!(b, [1, 4, 3, 4]); let r = unsafe { outer(&mut b[2..], 0, 1) }; assert_eq!(r, unsafe { base.add(3) }); assert_eq!(b, [1, 4, 5, 4]); }",
        ),
    );
}

#[test]
fn slicecursor_whole_cursor_to_local_slice_parameter() {
    // A cursor handed whole to a local callee whose parameter is a plain slice
    // takes the tail view at the argument (charter §1(d)).
    let input = "pub unsafe fn sum2(p: *const i8) -> i8 { *p.offset(0) + *p.offset(1) } pub unsafe fn outer(data: *const i8, k: isize) -> i8 { let a = *data.offset(k); a + sum2(data) }";
    let source = emitted(input);
    save_fixture("whole-cursor-to-local-slice-parameter", input, &source);
    assert!(
        source.contains("sum2(data.as_slice())"),
        "cursor tail view at the slice argument absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let b = [1i8, 2, 3, 4]; assert_eq!(unsafe { outer(&b[1..], 2) }, 4 + 2 + 3); }",
        ),
    );
}
