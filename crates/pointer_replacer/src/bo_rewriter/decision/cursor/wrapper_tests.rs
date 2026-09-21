use super::tests::{compile, cursor_decisions, cursor_dispositions, emitted};
use crate::bo_rewriter::decision::Decision;

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
    // **The dichotomy** (R472-6 route 1, the same shape as the fragment pin).
    // This walker goes BELOW the pointer it was handed, and a cursor rooted at a
    // raw parameter has its window fabricated forward from that pointer, so the
    // rendered form panics where the input program was correct (report 033 §3
    // reproduces it). Which arm holds is read from the derivation's own
    // `RetainedBase`, the same fact the census column reports:
    //
    //  * `ca63e6f44` + the guard (this frame): `Missing(EntryWindow)` — the
    //    family refuses, the parameter keeps its raw form, and the receipt says
    //    `ScheduleMissing`. The corpus row (`src::test::strrwd::ptr#1`) was
    //    already `degraded / slice-cursor-use / placed = 0`, so no emitted
    //    program changes.
    //  * once a base origin below entry exists (a caller-supplied cursor, or a
    //    window with a backward extent): the base is proven and the cursor is
    //    rendered with a `.seek(` as this witness pinned before.
    if entry_window_held(input, "ptr") {
        assert!(
            !source.contains("slice_cursor::SliceCursor"),
            "the window cannot hold this walk, so no cursor may be rendered: {source}"
        );
        assert_eq!(
            cursor_dispositions(input),
            vec![("strrwd::ptr".to_owned(), "Err(ScheduleMissing)".to_owned())],
            "the refusal must be the typed one"
        );
    } else {
        assert!(
            source.contains("slice_cursor::SliceCursor"),
            "native wrapper absent: {source}"
        );
        assert!(
            source.contains(".seek("),
            "native parameter seek absent: {source}"
        );
    }
}

/// Whether the derivation says this parameter root needs a position below its
/// entry — the `RetainedBase` fact the census column reports and the guard
/// consults, asked here so the pin reads the frame instead of assuming it.
fn entry_window_held(input: &str, param: &str) -> bool {
    utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (subject, _) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.param_name.as_deref() == Some(param))
            .unwrap_or_else(|| panic!("{param} subject"));
        super::inspect_subject(tcx, &ctx.slots, &ctx.model, subject).findings[0].outcome
            == super::admission::Outcome::Missing(super::admission::Need::EntryWindow)
    })
    .expect("admission")
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
    // Expectation migrated (relay 009): a pointee-PRESERVING cast is the
    // c2rust idiom and peels; a reinterpreting cast stays a cast base and holds.
    let input = "pub unsafe fn previous(outputs: *mut *mut f64, k: isize) -> u8 { let output: *mut u8 = (*outputs.offset(0)) as *mut u8; *output.offset(k) }";
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

#[test]
fn slicecursor_struct_field_raw_base_shared() {
    // genann `genann_train`: a shared cursor over a raw pointer field of a
    // struct, offset at construction, read at `k - 1`.
    let input = r#"
pub struct Net { pub output: *const f64, pub hidden: i32 }
pub unsafe fn train(ann: *const Net, h: i32, n: i32) -> f64 {
    let base = if h != 0 { (*ann).hidden * (h - 1) } else { 0 };
    let i_0: *const f64 = ((*ann).output).offset(base as isize);
    let mut acc = 0.;
    let mut k = 1;
    while k <= n {
        acc += *i_0.offset((k - 1) as isize);
        k += 1;
    }
    acc
}
"#;
    let source = emitted(input);
    save_fixture("struct-field-raw-base", input, &source);
    assert!(
        source.contains("crate::slice_cursor::SliceCursor::from_raw_parts(((*ann).output)"),
        "struct-field fallback base absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let out = [1., 2., 3., 4., 5.]; let net = Net { output: out.as_ptr(), hidden: 2 }; assert_eq!(unsafe { train(&net, 2, 3) }, 3. + 4. + 5.); assert_eq!(unsafe { train(&net, 0, 2) }, 1. + 2.); }",
        ),
    );
}

#[test]
fn slicecursor_struct_field_raw_base_written_is_held() {
    // A written cursor over a struct's raw pointer field would be an exclusive
    // view over a field the struct may hand out again; it stays held.
    let input = "pub struct Net { pub output: *mut f64 } pub unsafe fn zero(ann: *mut Net, n: isize, k: isize) { let o: *mut f64 = ((*ann).output).offset(n); *o.offset(k) = 0.; }";
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let (_, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some("o"))
            .unwrap();
        let super::Decision::Degraded(record) = decision else {
            panic!("written field base admitted: {decision:?}");
        };
        assert_eq!(record.reason.key(), "cursor-base-unavailable");
    })
    .unwrap();
}

#[test]
fn slicecursor_table_element_with_direct_caller() {
    // tulipindicators `ti_sma` is called directly (the smoke tests), so its
    // `inputs` parameter carries a caller-side input plan; the table-element
    // base makes no window claim on the outer and must still admit.
    let input = r#"
pub unsafe fn sma(size: i32, inputs: *const *const f64, period: i32) -> f64 {
    let input: *const f64 = *inputs.offset(0);
    let mut sum = 0.;
    let mut i = 0;
    while i < period { sum += *input.offset(i as isize); i += 1; }
    i = period;
    while i < size {
        sum += *input.offset(i as isize);
        sum -= *input.offset((i - period) as isize);
        i += 1;
    }
    sum
}
pub unsafe fn caller(t: *const *const f64) -> f64 { sma(4, t, 2) }
"#;
    let source = emitted(input);
    save_fixture("table-element-with-direct-caller", input, &source);
    assert!(
        source.contains("crate::slice_cursor::SliceCursor::from_raw_parts(inputs["),
        "table-element base absent under a direct caller: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let x = [1., 2., 3., 4.]; let t = x.as_ptr(); assert_eq!(unsafe { caller(&t) }, 3. + 4.); }",
        ),
    );
}

#[test]
fn slicecursor_ordering_walk_to_derived_end() {
    // brotli `ShannonEntropy`: a forward walk of a parameter cursor compared
    // against a derived, untyped end (`population < population_end`).
    let input = r#"
pub unsafe fn entropy(mut population: *const u32, size: usize) -> u64 {
    let mut sum = 0u64;
    let mut population_end = population.offset(size as isize);
    while population < population_end {
        sum += *population as u64;
        population = population.offset(1);
    }
    sum
}
"#;
    let source = emitted(input);
    save_fixture("ordering-walk-to-derived-end", input, &source);
    assert!(
        source.contains("let mut population_end: crate::slice_cursor::SliceCursor<'_, u32> ="),
        "derived end declaration absent: {source}"
    );
    assert!(
        source.contains(".addr() < ") || source.contains(".addr()) < "),
        "ordering address view absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let p = [1u32, 2, 3, 4]; assert_eq!(unsafe { entropy(&p, 4) }, 10); assert_eq!(unsafe { entropy(&p[1..], 2) }, 5); }",
        ),
    );
}

#[test]
fn slicecursor_ordering_two_parameters_with_difference() {
    // lodepng `lodepng_chunk_next` / binn `AdvanceDataPos`: two parameter
    // cursors ordered against each other and their difference taken; neither
    // walks backward. (Its E2-permitted raw return is the seam's, not tested here.)
    let input = r#"
pub unsafe fn chunk_len(chunk: *mut u8, end: *mut u8) -> usize {
    let available = end.offset_from(chunk) as usize;
    if chunk >= end || available < 4 { return 0; }
    *chunk.offset(3) as usize + available
}
"#;
    let source = emitted(input);
    save_fixture("ordering-two-parameters", input, &source);
    assert!(
        source.contains("slice_cursor::SliceCursor::new(chunk)")
            && source.contains("slice_cursor::SliceCursor::new(end)"),
        "wrapper absent: {source}"
    );
    assert!(
        source.contains(".addr()") && source.contains("offset_from("),
        "address views absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let b = [0u8, 0, 0, 2, 9, 9, 9, 9]; assert_eq!(unsafe { chunk_len(&b[..], &b[8..]) }, 10); let c = [9u8, 9]; assert_eq!(unsafe { chunk_len(&c[..], &c[2..]) }, 0); }",
        ),
    );
}

#[test]
fn slicecursor_count_zeros_cursor_from_cursor() {
    // lodepng `countZeros`: a parameter cursor, two derived locals, a bound
    // taken against a derived temporary, and a cursor-from-cursor assignment.
    let input = r#"
pub unsafe fn count_zeros(mut data: *const u8, size: usize, pos: usize) -> u32 {
    let mut start = data.offset(pos as isize);
    let mut end = start.offset(6);
    if end > data.offset(size as isize) {
        end = data.offset(size as isize);
    }
    data = start;
    while data != end && *data == 0 {
        data = data.offset(1);
    }
    data.offset_from(start) as u32
}
"#;
    let source = emitted(input);
    save_fixture("count-zeros", input, &source);
    // Re-pinned 2026-09-16 (batch-8 dry3): on the composed tree the forward
    // slice family may take `start` / `end` and the pass-on into `data`; the
    // witness pins delivery and the runtime result, the form is the seat's
    // precedence ruling.
    assert!(
        source.contains("slice_cursor::SliceCursor::new(data)")
            || source.contains("core::slice::from_raw_parts(data"),
        "no delivery: {source}"
    );
    // The harness follows the emitted parameter form: a cursor parameter is
    // a slice at the safe body; the composed tree may keep `data` raw.
    let argument = if source.contains("fn count_zeros(mut data: *const u8") {
        "b.as_ptr()"
    } else {
        "&b"
    };
    compile(
        &source,
        Some(&format!(
            "fn main() {{ let b = [0u8, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0]; assert_eq!(unsafe {{ count_zeros({argument}, 12, 1) }}, 3); assert_eq!(unsafe {{ count_zeros({argument}, 12, 5) }}, 6); assert_eq!(unsafe {{ count_zeros({argument}, 12, 9) }}, 3); }}"
        )),
    );
}

#[test]
fn slicecursor_reborrow_idiom_from_slice_parameter() {
    // lodepng `encodeLZ77`: null-initialised cursors assigned the c2rust
    // reborrow idiom `&*in_0.offset(k) as *const u8` over a slice parameter,
    // compared for identity and differenced.
    let input = r#"
pub unsafe fn match_len(in_0: *const u8, insize: usize, pos: usize, back: usize) -> u32 {
    let mut lastptr = 0 as *const u8;
    let mut foreptr = 0 as *const u8;
    let mut backptr = 0 as *const u8;
    let limit = if insize < pos + 6 { insize } else { pos + 6 };
    lastptr = &*in_0.offset(limit as isize) as *const u8;
    foreptr = &*in_0.offset(pos as isize) as *const u8;
    backptr = &*in_0.offset((pos - back) as isize) as *const u8;
    while foreptr != lastptr && *backptr == *foreptr {
        backptr = backptr.offset(1);
        foreptr = foreptr.offset(1);
    }
    foreptr.offset_from(&*in_0.offset(pos as isize) as *const u8) as u32
}
"#;
    let source = emitted(input);
    save_fixture("reborrow-idiom-from-slice-parameter", input, &source);
    assert!(
        source.contains("Option<crate::slice_cursor::SliceCursor"),
        "optional cursors absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let b = [1u8, 2, 3, 1, 2, 3, 9]; assert_eq!(unsafe { match_len(&b, 7, 3, 3) }, 3); assert_eq!(unsafe { match_len(&b, 7, 1, 1) }, 0); }",
        ),
    );
}

#[test]
fn slicecursor_fragment_fast_core_loop() {
    // brotli `BrotliCompressFragmentFastImpl`, the hash-match core: optional
    // cursors over `input`, a derived end, a candidate looked up backward and
    // from a table, compared, differenced and matched. (The match through a
    // local callee whose parameters the slice family delivers is the R398-1
    // restoration wall on the composed batch-8 tree; that variant is kept as a
    // witness for wave-5d, not in the suite — re-pinned 2026-09-16.)
    let input = r#"
pub unsafe fn fragment(input: *const u8, block_size: usize, table: *mut i32, last_distance: i32) -> i32 {
    let mut ip_end = 0 as *const u8;
    let mut ip = 0 as *const u8;
    let mut candidate = 0 as *const u8;
    let base_ip = input;
    let mut matched = 0;
    ip = input;
    ip_end = input.offset(block_size as isize);
    ip = ip.offset(1);
    while ip < ip_end.offset(-2) {
        let hash = (*ip as usize) & 7;
        candidate = ip.offset(-(last_distance as isize));
        if candidate < base_ip || *ip.offset(0) != *candidate.offset(0) || *ip.offset(1) != *candidate.offset(1) {
            candidate = base_ip.offset(*table.offset(hash as isize) as isize);
        }
        *table.offset(hash as isize) = ip.offset_from(base_ip) as i32;
        if candidate < ip && *ip.offset(0) == *candidate.offset(0) && *ip.offset(1) == *candidate.offset(1) {
            matched += 1;
        }
        ip = ip.offset(1);
    }
    matched
}
"#;
    let source = emitted(input);
    save_fixture("fragment-fast-core-loop", input, &source);
    // **The dichotomy** (R471-4, test-only under R217-2(a)). Two frames are
    // admissible and this pin says which family rendered the row on each:
    //
    //  * `ca63e6f44` (batch 15, the landed frame): the cursor family takes
    //    `input`. The emitted text carries optional cursors, and the corpus
    //    twins — the 14 `compress_fragment{,_two_pass}::…::input#2` rows —
    //    sit at `candidate = true, admission = NeedsFact, emission = unchanged`:
    //    this family holds them as candidates and delivers none, which is the
    //    hand-off point this witness has always pinned.
    //  * with wave-5c's plain twin built (their 031): `input` settles
    //    `Slice { mutable: false }`, no cursor is rendered for it, and the
    //    hand-off reads in the other direction.
    //
    // Neither direction is conceded. If this family's `NeedsFact` fact later
    // lands, the row comes back through the cursor and the first arm holds
    // again — the pin reports the frame rather than fixing the outcome.
    match decision_of(input, "fragment::input") {
        Decision::Slice { mutable: false, .. } => {
            assert!(
                !source.contains("Option<crate::slice_cursor::SliceCursor"),
                "the plain twin took the row, so no cursor may be rendered for it: {source}"
            );
            assert!(
                !cursor_dispositions(input)
                    .iter()
                    .any(|(label, disposition)| label == "fragment::input"
                        && disposition == "Ok(())"),
                "the plain twin took the row, so this family may not admit it"
            );
        }
        other => {
            assert!(
                source.contains("Option<crate::slice_cursor::SliceCursor"),
                "optional cursors absent under {other:?}: {source}"
            );
        }
    }
    compile(
        &source,
        Some(
            "fn main() { let b = [1u8, 2, 1, 2, 1, 2, 9, 9]; let mut t = [0i32; 8]; assert_eq!(unsafe { fragment(&b, 8, &mut t, 2) }, 3); }",
        ),
    );
}

/// The decision one labelled subject settles on, for a pin that must say which
/// family rendered a row rather than assume it.
fn decision_of(input: &str, label: &str) -> Decision {
    utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        table
            .entries
            .iter()
            .find(|(subject, _)| subject.label == label)
            .map(|(_, decision)| decision.clone())
            .unwrap_or_else(|| panic!("{label} subject"))
    })
    .expect("decision")
}

#[test]
fn slicecursor_encode_lz77_body() {
    // lodepng `encodeLZ77`'s body around the match loop: the input parameter
    // is read at computed offsets and roots the three null-initialised
    // cursors through the reborrow idiom. (With `in_0` also handed whole to a
    // local callee the tree hits the R398-1 restoration wall — that reduction
    // is kept as a witness for wave-5d, not in the suite.)
    let input = r#"
pub unsafe fn lz77(in_0: *const u8, insize: usize, chain: *mut u16, maxsize: usize) -> u32 {
    let mut pos = 0usize;
    let mut total = 0u32;
    let mut lastptr = 0 as *const u8;
    let mut foreptr = 0 as *const u8;
    let mut backptr = 0 as *const u8;
    while pos < insize {
        let hashval = if pos + 2 < insize { (*in_0.offset(pos as isize) as u32) ^ (*in_0.offset((pos + 1) as isize) as u32) } else { 0 };
        let mut numzeros = 0u32;
        if hashval == 0 && pos + 1 < insize && *in_0.offset((pos + 1) as isize) == 0 { numzeros = 1; }
        let limit = if insize < pos + maxsize { insize } else { pos + maxsize };
        lastptr = &*in_0.offset(limit as isize) as *const u8;
        let cur = *chain.offset(pos as isize) as usize;
        if cur > 0 && cur <= pos {
            foreptr = &*in_0.offset(pos as isize) as *const u8;
            backptr = &*in_0.offset((pos - cur) as isize) as *const u8;
            if numzeros >= 1 {
                backptr = backptr.offset(numzeros as isize);
                foreptr = foreptr.offset(numzeros as isize);
            }
            while foreptr != lastptr && *backptr == *foreptr {
                backptr = backptr.offset(1);
                foreptr = foreptr.offset(1);
            }
            total += foreptr.offset_from(&*in_0.offset(pos as isize) as *const u8) as u32;
        }
        pos += 1;
    }
    total
}
"#;
    let source = emitted(input);
    save_fixture("encode-lz77-body", input, &source);
    assert!(
        source.contains("Option<crate::slice_cursor::SliceCursor"),
        "optional cursors absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let b = [0u8, 0, 5, 6, 0, 0, 5, 6, 7]; let mut c = [0u16, 0, 0, 0, 4, 4, 4, 4, 4]; assert_eq!(unsafe { lz77(&b, 9, &mut c, 8) }, 10); }",
        ),
    );
}

#[test]
fn slicecursor_fragment_fast_core_loop_with_local_callee() {
    // The R398-1 wall reduction (reports 011/012, relay 013 §1): the same
    // core loop with the candidates also handed whole to a local callee whose
    // parameters the slice family delivers. The callee's class was premised
    // on the raw source (arm C); the cursor's own view at the argument
    // (`.as_slice()`) is that C adaptation, receipted under the arm — so the
    // class is not lost and the program is not restored to raw.
    let input = r#"#![allow(unused_unsafe,unsafe_op_in_unsafe_fn,unused_mut,unused_assignments)]
pub unsafe fn is_match(p1: *const u8, p2: *const u8) -> i32 {
    (*p1.offset(0) == *p2.offset(0) && *p1.offset(1) == *p2.offset(1)) as i32
}
pub unsafe fn fragment(input: *const u8, block_size: usize, table: *mut i32, last_distance: i32) -> i32 {
    let mut ip_end = 0 as *const u8;
    let mut ip = 0 as *const u8;
    let mut candidate = 0 as *const u8;
    let base_ip = input;
    let mut matched = 0;
    ip = input;
    ip_end = input.offset(block_size as isize);
    ip = ip.offset(1);
    while ip < ip_end.offset(-2) {
        let hash = (*ip as usize) & 7;
        candidate = ip.offset(-(last_distance as isize));
        if candidate < base_ip || is_match(ip, candidate) == 0 {
            candidate = base_ip.offset(*table.offset(hash as isize) as isize);
        }
        *table.offset(hash as isize) = ip.offset_from(base_ip) as i32;
        if candidate < ip && is_match(ip, candidate) != 0 {
            matched += 1;
        }
        ip = ip.offset(1);
    }
    matched
}
"#;
    let source = emitted(input);
    save_fixture("fragment-fast-with-local-callee", input, &source);
    assert!(
        source.contains("fn fragment(input: &[u8], block_size: usize, table: &mut [i32]"),
        "cursor parameter absent: {source}"
    );
    assert!(
        source.contains("is_match(ip.as_ref().expect(\"non-null cursor\").as_slice(),")
            && source.contains("candidate.as_ref().expect(\"non-null cursor\").as_slice()) =="),
        "cursor view at the delivered slice formal absent: {source}"
    );
    assert!(
        !source.contains("restore-family")
            && source
                .contains("let mut ip: Option<crate::slice_cursor::SliceCursor<'_, u8>> = None;"),
        "optional cursors absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let b = [1u8, 2, 1, 2, 1, 2, 9, 9]; let mut t = [0i32; 8]; assert_eq!(unsafe { fragment(&b, 8, &mut t, 2) }, 3); }",
        ),
    );
}

#[test]
fn slicecursor_offset_chain_argument_at_a_raw_callee() {
    // brotli `hasSuffix` (report 008's typed hold, attempt 3): an offset chain
    // rooted at the cursor handed to a raw foreign formal. The chain is the
    // cursor's derived value at the argument; the boundary's own site renders
    // the cursor's raw view over it (`.as_ptr()`), the same span composed
    // use-then-seam, under the boundary's own retention receipt.
    let input = r#"
unsafe extern "C" { fn strcmp(a: *const i8, b: *const i8) -> i32; }
pub unsafe fn has_suffix(s: *const i8, suffix: *const i8, ns: isize, nx: isize) -> i32 {
    if ns < nx { return 0; }
    if strcmp(s.offset(ns + (-nx)), suffix) == 0 { 1 } else { 0 }
}
"#;
    let source = emitted(input);
    save_fixture("offset-chain-argument-at-raw-callee", input, &source);
    // `suffix` is another family's (raw here; a slice where a libc contract
    // extent delivers it on the composed tree): the harness follows its form.
    assert!(
        source.contains("fn has_suffix(s: &[i8], suffix: "),
        "cursor parameter absent: {source}"
    );
    assert!(
        source.contains("strcmp(s.offset_by((0isize).wrapping_add((ns + (-nx)) as")
            && source.contains("isize)).as_ptr(), suffix"),
        "raw view over the derived cursor absent: {source}"
    );
    let raw_suffix = source.contains("fn has_suffix(s: &[i8], suffix: *const i8");
    let (good, bad) = if raw_suffix {
        ("d.as_ptr()", "x.as_ptr()")
    } else {
        ("&d[..]", "&x[..]")
    };
    compile(
        &source,
        Some(&format!(
            "fn main() {{ let s = *b\"abcdef\\0\"; let s = s.map(|b| b as i8); let d = *b\"def\\0\"; let d = d.map(|b| b as i8); let x = *b\"xyz\\0\"; let x = x.map(|b| b as i8); assert_eq!(unsafe {{ has_suffix(&s[..6], {good}, 6, 3) }}, 1); assert_eq!(unsafe {{ has_suffix(&s[..6], {bad}, 6, 3) }}, 0); assert_eq!(unsafe {{ has_suffix(&s[..6], {good}, 2, 3) }}, 0); }}"
        )),
    );
}

#[test]
fn slicecursor_repointed_child_withdraws_with_its_parent() {
    // brotli `BrotliCompressFragmentFastImpl` (batch-8 census-1, 42 cursor
    // errors): `ip_end`, a null-initialised cursor re-pointed from the
    // parameter `input` (`ip_end = input.offset(n)`), was kept as a cursor
    // after `input` itself withdrew (its copies into raw locals are holds), so
    // the constructor called `offset_by` on a raw pointer. A re-pointed child
    // stands only on a base that admitted, like an initialised one.
    let input = r#"
pub unsafe fn walk(p: *const u8, q: *const u8) -> i32 { (*p.offset(0) as i32) + (*q.offset(1) as i32) }
pub unsafe fn fragment(input: *const u8, n: usize) -> i32 {
    let mut ip_end = 0 as *const u8;
    let mut copy = input;
    let mut acc = 0;
    ip_end = input.offset(n as isize);
    let mut ip = input.offset(1);
    while ip < ip_end {
        acc += *ip.offset(-1) as i32;
        ip = ip.offset(1);
    }
    acc + walk(copy, copy)
}
"#;
    let decisions = cursor_decisions(input);
    let cursor = |label: &str| decisions.iter().any(|(l, c)| l == label && *c);
    assert!(
        !cursor("fragment::ip_end") || cursor("fragment::input"),
        "child cursor over a raw parent: {decisions:?}"
    );
    let source = emitted(input);
    save_fixture("repointed-child-withdraws-with-parent", input, &source);
    // On the composed tree the forward slice family may deliver the freed
    // parameter as a slice: the harness follows the emitted form.
    let argument = if source.contains("fn fragment(input: *const u8") {
        "b.as_ptr()"
    } else {
        "&b[..]"
    };
    compile(
        &source,
        Some(&format!(
            "fn main() {{ let b = [1u8, 2, 3, 4, 5, 6]; assert_eq!(unsafe {{ fragment({argument}, 5) }}, 1 + 2 + 3 + 4 + 1 + 2); }}"
        )),
    );
}

#[test]
fn slicecursor_parent_withdraws_with_the_copies_it_lent() {
    // brotli `CreateCommands` (batch-8 census-1, 42 cursor errors): the
    // parameter `input` was admitted with its copies (`let mut ip = input;`,
    // `next_emit = input`) left to the copies' own cursor candidacy; the
    // copies then withdrew (raw callee positions), `input` stayed a cursor,
    // and every copy became a `SliceCursor` by inference with raw uses. A use
    // left to a peer cursor stands only while that peer is a cursor too.
    let input = r#"
pub unsafe fn is_match(p1: *const u8, p2: *const u8) -> i32 { (*p1.offset(0) == *p2.offset(0) && *p1.offset(4) == *p2.offset(4)) as i32 }
pub unsafe fn match_len(s1: *const u8, s2: *const u8, limit: usize) -> usize { let mut m = 0usize; while m < limit && *s1.offset(m as isize) == *s2.offset(m as isize) { m += 1; } m }
unsafe extern "C" { fn memcpy(d: *mut u8, s: *const u8, n: usize) -> *mut u8; }
pub unsafe fn create_commands(input: *const u8, block_size: usize, base_ip: *const u8, table: *mut i32, literals: *mut *mut u8) -> i32 {
    let mut ip = input;
    let mut ip_end = input.offset(block_size as isize);
    let mut next_emit = input;
    let mut last_distance = -1i32;
    let mut acc = 0;
    if block_size >= 16 {
        let mut ip_limit = input.offset((block_size - 16) as isize);
        ip = ip.offset(1);
        loop {
            let mut next_ip = ip;
            let mut candidate = 0 as *const u8;
            let mut skip = 32u32;
            let mut stop = false;
            loop {
                let hash = (*ip as usize) & 7;
                let fresh = skip; skip += 1;
                ip = next_ip;
                next_ip = ip.offset((fresh >> 5) as isize);
                if next_ip > ip_limit { stop = true; break; }
                candidate = ip.offset(-(last_distance as isize));
                if is_match(ip, candidate) != 0 && candidate < ip {
                    *table.offset(hash as isize) = ip.offset_from(base_ip) as i32;
                } else {
                    candidate = base_ip.offset(*table.offset(hash as isize) as isize);
                    *table.offset(hash as isize) = ip.offset_from(base_ip) as i32;
                    if is_match(ip, candidate) == 0 { continue; }
                }
                if !(ip.offset_from(candidate) > 1000) { break; }
            }
            if stop { break; }
            let base = ip;
            let matched = 5 + match_len(candidate.offset(5), ip.offset(5), (ip_end.offset_from(ip) as usize) - 5);
            let distance = base.offset_from(candidate) as i32;
            let insert = base.offset_from(next_emit) as usize;
            ip = ip.offset(matched as isize);
            memcpy(*literals, next_emit, insert);
            *literals = (*literals).offset(insert as isize);
            acc += distance;
            last_distance = distance;
            next_emit = ip;
            if ip >= ip_limit { break; }
        }
    }
    if next_emit < ip_end {
        let insert = ip_end.offset_from(next_emit) as usize;
        memcpy(*literals, next_emit, insert);
        *literals = (*literals).offset(insert as isize);
        acc += insert as i32;
    }
    acc
}
"#;
    let decisions = cursor_decisions(input);
    let cursor = |label: &str| decisions.iter().any(|(l, c)| l == label && *c);
    for (parent, copy) in [
        ("create_commands::input", "create_commands::ip"),
        ("create_commands::input", "create_commands::next_emit"),
        ("create_commands::base_ip", "create_commands::candidate"),
    ] {
        assert!(
            !cursor(parent) || cursor(copy),
            "{parent} is a cursor while its copy {copy} is raw: {decisions:?}"
        );
    }
    let source = emitted(input);
    save_fixture("parent-withdraws-with-copies", input, &source);
    // On the composed tree the forward slice family may deliver the freed
    // parameters as slices: the harness follows the emitted forms.
    let input_argument = if source.contains("fn create_commands(input: *const u8") {
        "b.as_ptr()"
    } else {
        "&b[..]"
    };
    let base_argument = if source.contains("base_ip: *const u8") {
        "b.as_ptr()"
    } else {
        "&b[..]"
    };
    let table_argument = if source.contains("table: *mut i32") {
        "t.as_mut_ptr()"
    } else {
        "&mut t[..]"
    };
    compile(
        &source,
        Some(&format!(
            "fn main() {{ let b = [1u8, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 9, 9, 9, 9, 9, 9, 9, 9]; let mut t = [0i32; 8]; let mut lit = [0u8; 64]; let mut lp = lit.as_mut_ptr(); let r = unsafe {{ create_commands({input_argument}, 32, {base_argument}, {table_argument}, &mut lp) }}; assert_eq!(r, 11); }}"
        )),
    );
}

#[test]
fn slicecursor_mutable_pointer_address_view_against_a_raw_mut_operand() {
    // binn `IsValidBinnHeader` (batch-8 census-1, 4 x E0308): `plimit`, a
    // null-initialised `*mut u8` cursor, is ordered against the raw `*mut u8`
    // `p` through an offset chain (`p.offset(3) > plimit`); the chain arm's
    // address view rendered `*const u8` (`null()` / `addr()`), which Rust will
    // not order against a `*mut`. The view keeps the binding's own pointer
    // mutability, as the observed-address arm already did.
    let input = r#"
static mut SAVED: *mut u8 = 0 as *mut u8;
pub unsafe fn keep(q: *mut u8) { SAVED = q; }
pub unsafe fn header(buf: &mut [u8], p: *mut u8, n: isize) -> i32 {
    let mut plimit = 0 as *mut u8;
    if n > 0 { plimit = buf.as_mut_ptr().offset(n + (-1)); }
    keep(p);
    if !plimit.is_null() && p > plimit { return 0; }
    if !plimit.is_null() && p.offset(3) > plimit { return 2; }
    1
}
"#;
    let source = emitted(input);
    save_fixture("mutable-pointer-address-view", input, &source);
    assert!(
        source.contains("let mut plimit: Option<crate::slice_cursor::SliceCursor<'_, u8>> = None;")
            && source.contains("fn header(buf: &mut [u8], p: *mut u8, n: isize)"),
        "optional cursor beside the raw operand absent: {source}"
    );
    assert!(
        source
            .matches("|cursor| cursor.addr())).cast_mut()")
            .count()
            == 2
            && !source.contains("cursor.addr()) {"),
        "the *mut address view absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let mut b = [0u8; 8]; let p = b.as_mut_ptr(); assert_eq!(unsafe { header(&mut b[..], p, 8) }, 1); let mut c = [0u8; 8]; let q = unsafe { c.as_mut_ptr().add(3) }; assert_eq!(unsafe { header(&mut c[..], q, 5) }, 2); let mut d = [0u8; 8]; let r = unsafe { d.as_mut_ptr().add(6) }; assert_eq!(unsafe { header(&mut d[..], r, 2) }, 0); }",
        ),
    );
}

#[test]
fn slicecursor_cursor_cast_to_a_void_formal_takes_its_raw_view() {
    // brotli `CreateCommands` / the fragment compressors (census #6's archive:
    // `ip` and `next_ip` hold `RawBoundaryUnbuilt`, and the 14 forwarders'
    // `DeclarationUnbuilt` sit behind them): a cursor CAST to an opaque pointer
    // at a FOREIGN formal (`memcpy(dst, next_emit as *const c_void, n)`).
    //
    // The cursor's own raw view belongs inside the cast, which keeps its text —
    // built here. What is NOT this family's to grant is the site's retention
    // receipt: the raw boundary does not open a cast-to-opaque argument for a
    // cursor subject, so the subject holds `RawBoundaryUnbuilt` (the use is
    // built, the receipt is missing) where it held the undiagnosed `UseUnbuilt`
    // before. A local callee's void parameter stays the region family's.
    let input = r#"
use std::os::raw::c_void;
unsafe extern "C" { fn sink(p: *const c_void) -> u64; }
pub unsafe fn emit(input: &[u8], n: usize) -> u64 {
    let mut ip = input.as_ptr().offset(1);
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < n {
        acc += *ip.offset(-1) as u64;
        acc = acc.wrapping_add(sink(ip.offset(-1) as *const c_void));
        ip = ip.offset(1);
        i += 1;
    }
    acc
}
"#;
    let dispositions = cursor_dispositions(input);
    let of = |label: &str| {
        dispositions
            .iter()
            .find(|(l, _)| l == label)
            .map(|(_, d)| d.as_str())
            .unwrap_or("<no receipt>")
    };
    assert_eq!(
        of("emit::ip"),
        "Ok(())",
        "the cast operand's view is not delivered: {dispositions:?}"
    );
    let source = emitted(input);
    save_fixture("cursor-cast-to-void-formal", input, &source);
    assert!(
        source.contains(".as_ptr() as *const c_void)"),
        "the cursor's raw view inside the cast is absent: {source}"
    );
}

#[test]
fn slicecursor_reborrow_idiom_at_a_slice_callee_takes_the_tail_view() {
    // brotli `BrotliTransformDictionaryWord` (census #6: `dst` is the archive's
    // single `BorrowedElementUnbuilt`; `uppercase` / `shift` withdraw with it).
    // The c2rust idiom handed DIRECTLY to a local callee whose parameter the
    // slice family delivers — `ToUpperCase(&mut *dst.offset(idx - len))`.
    //
    // The view itself is mechanical (`dst.offset_by(k).as_slice_mut()`, the same
    // view a whole-cursor argument takes) and was built and measured; emitting it
    // makes the ADDITIVE-FAMILY machinery withdraw the owner's family instead
    // (every receipt disappears), because a cursor argument at a delivered-slice
    // formal needs its interface dependency registered the way report 013's
    // arm-C receipt registers a whole-cursor argument. Held until that exists
    // (MAX-3 stop, report 026); this pins the wall so the day it moves is visible.
    let input = r#"
pub unsafe fn to_upper(p: *mut u8) -> i32 {
    if *p.offset(0) >= 97 && *p.offset(0) <= 122 { *p.offset(0) = *p.offset(0) - 32; }
    1
}
pub unsafe fn shift_all(p: *mut u8, len: i32, param: u8) {
    let mut i = 0;
    while i < len { *p.offset(i as isize) = (*p.offset(i as isize)).wrapping_add(param); i += 1; }
}
pub unsafe fn transform(dst: *mut u8, idx: i32, mut len: i32, t: i32, param: u8) {
    if t == 1 {
        to_upper(&mut *dst.offset((idx - len) as isize));
    } else if t == 2 {
        let mut uppercase: *mut u8 = &mut *dst.offset((idx - len) as isize) as *mut u8;
        while len > 0 {
            let step = to_upper(uppercase);
            uppercase = uppercase.offset(step as isize);
            len -= step;
        }
    } else if t == 3 {
        shift_all(&mut *dst.offset((idx - len) as isize), len, param);
    }
}
"#;
    let dispositions = cursor_dispositions(input);
    let of = |label: &str| {
        dispositions
            .iter()
            .find(|(l, _)| l == label)
            .map(|(_, d)| d.as_str())
            .unwrap_or("<no receipt>")
    };
    assert_eq!(
        (of("transform::dst"), of("transform::uppercase")),
        ("Ok(())", "Ok(())"),
        "the idiom at a slice callee is not the tail view: {dispositions:?}"
    );
    let source = emitted(input);
    save_fixture("reborrow-idiom-at-a-slice-callee", input, &source);
    assert!(
        source.contains("fn transform(dst: &mut [u8], idx: i32, mut len: i32, t: i32,")
            && source.matches(".as_slice_mut()").count() >= 3,
        "the tail views are absent: {source}"
    );
    compile(
        &source,
        Some(
            "fn main() { let mut b = *b\"abcd\"; unsafe { transform(&mut b[..], 4, 2, 1, 0) }; assert_eq!(&b, b\"abCd\"); let mut c = *b\"abcd\"; unsafe { transform(&mut c[..], 4, 2, 2, 0) }; assert_eq!(&c, b\"abCD\"); let mut d = *b\"abcd\"; unsafe { transform(&mut d[..], 4, 2, 3, 1) }; assert_eq!(&d, b\"abde\"); }",
        ),
    );
}

// ---------------------------------------------------------------------------
// **The N2 seam** (nested's relay 034 §2 / R453-6). Their fixture and their RED
// witness, transplanted into this family's files because the change is this
// family's: `table_element_base` builds `new(t[k])` over a table that delivers
// its inner level. Both are copied from
// `docs/agents/artifacts/2026-09-17-nested-n2-handover/`; the witness is
// unmodified except for the harness helpers below, which are this file's.
// ---------------------------------------------------------------------------

#[allow(dead_code, unused_assignments, unused_mut)]
#[path = "nested_seam_fixture.rs"]
mod nested_seam_original;

const NESTED_SEAM_SOURCE: &str = include_str!("nested_seam_fixture.rs");
const CURSOR: &str = "indicators::sma_cursor::ti_sma_cursor";

/// The emitted tree of the N2 seam fixture, through the corpus's own path
/// (A5 replay over the frozen benchmark graph) so the exposure plan is the
/// `PositiveSeedShim` the registration entry asks for.
fn nested_seam_emitted() -> &'static str {
    static SOURCE_AFTER: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    SOURCE_AFTER.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("crat-slicecursor-n2-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("lib.rs");
        std::fs::write(&root, NESTED_SEAM_SOURCE).unwrap();
        let outcome = crate::bo_rewriter::rewrite_m1_path_a5_injected(
            &root,
            crate::bo_rewriter::A5Mode::PreciseReplay,
            Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            &|_| {},
        );
        std::fs::remove_dir_all(&dir).unwrap();
        let crate::bo_rewriter::RewriteOutcome::Emitted { source, .. } = outcome else {
            panic!("N2 seam emission unavailable; compiler diagnostics precede this assertion");
        };
        println!("N2-SEAM-EMITTED\n{source}\nN2-SEAM-END");
        source
    })
}

fn region<'a>(source: &'a str, owner: &str) -> &'a str {
    source
        .split(&format!("pub unsafe extern \"C\" fn {owner}("))
        .nth(1)
        .unwrap_or_else(|| panic!("{owner} in the emitted tree"))
        .split("pub mod ")
        .next()
        .expect("owner region")
}

/// The decision of one named parameter of one owner, at the final table.
fn table_decision(name: &str, parameter: &str) -> Decision {
    utils::compilation::run_compiler_on_str(NESTED_SEAM_SOURCE, |tcx| {
        let (table, _) = crate::bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::bo_rewriter::A5Mode::PreciseReplay,
                Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        table
            .entries
            .iter()
            .find(|(s, _)| {
                tcx.def_path_str(s.fn_did.to_def_id()) == name
                    && s.param_name.as_deref() == Some(parameter)
            })
            .map(|(_, decision)| decision.clone())
            .unwrap_or_else(|| panic!("{name}::{parameter} subject"))
    })
    .expect("nested seam decisions")
}

/// **W-N2-CURSOR** — the seam (relay 002 §2). The input row is the cursor
/// family's subject; its table still delivers its inner level, and the cursor's
/// constructor becomes `SliceCursor::new(t[k])` — which takes NO length, so the
/// seam fabricates nothing and the row's one fabricated extent is the one this
/// arm relocated to the wrapper.
#[test]
#[ignore = "needs nested's N2 admission and main's ctx_of re-parameterisation (R452-6 (b))"]
fn n2_seams_a_cursor_row_onto_the_delivered_inner_slice() {
    // The decision frame is REPORTED, never gated (nested 013 STOP 3 / R478-5):
    // a first assertion on the frame masks everything downstream, so the
    // emitted text is what this witness fails on.
    println!("N2-FRAME inputs = {:?}", table_decision(CURSOR, "inputs"));
    let source = nested_seam_emitted();
    let body = region(source, "ti_sma_cursor");
    assert!(
        body.contains("inputs: &[&[std::os::raw::c_double]]"),
        "the nested input table:\n{body}"
    );
    assert!(
        body.contains("crate::slice_cursor::SliceCursor::new(inputs[0])"),
        "the cursor takes the delivered inner slice, with no length:\n{body}"
    );
    assert!(
        !body.contains("SliceCursor::from_raw_parts"),
        "no raw cursor construction survives on the seamed row:\n{body}"
    );
    assert!(
        !body.contains("from_raw_parts(inputs,"),
        "the delivered table's own fabricated outer extent is gone:\n{body}"
    );
}

/// **W-CUR-LOCAL** — the ephemeral copy of a cursor (urlparser `strrwd`'s
/// `let fresh = ptr; ptr = ptr.offset(-1); *fresh`). A copy whose single use is
/// a deref READ is not a second cursor: it is the cursor's raw view at the
/// current position, which is the `raw-op-cursor-local` vocabulary the
/// delivered-base arm already owns, receipted per site.
#[test]
fn slicecursor_read_only_copy_of_a_cursor_takes_its_raw_view() {
    let input = r#"
pub unsafe fn scan(mut p: *const i32, n: i32) -> i32 {
    let mut total = 0i32;
    p = p.offset(4);
    let mut i = 0i32;
    while i < n {
        let fresh = p;
        p = p.offset(-1);
        total += *fresh;
        i += 1;
    }
    total
}
pub unsafe fn caller(base: &[i32]) -> i32 { scan(base.as_ptr(), 3) }
"#;
    let source = emitted(input);
    save_fixture("cursor-local-copy", input, &source);
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "the parameter did not deliver: {source}"
    );
    assert!(
        source.contains("let fresh = p.as_ptr();"),
        "the copy is not the cursor's raw view: {source}"
    );
    compile(
        &source,
        Some(
            r#"fn main() { let mut b = [0i32; 2048]; b[2] = 2; b[3] = 3; b[4] = 4; assert_eq!(unsafe { caller(&b) }, 9); }"#,
        ),
    );
}

/// **F-CUR-LOCAL-EXCLUSIVE** — an exclusive cursor with a raw copy of its own
/// region alive beside it is a retained alias; the rule is shared-only, and on
/// this shape the MODEL refuses one step earlier (`RefMissing`, `kind-raw`)
/// than the rule would.
#[test]
fn slicecursor_a_copy_of_an_exclusive_cursor_is_not_a_raw_view() {
    let input = r#"
pub unsafe fn scan(mut p: *mut i32, n: i32) -> i32 {
    let mut total = 0i32;
    p = p.offset(4);
    let mut i = 0i32;
    while i < n {
        let fresh = p;
        p = p.offset(-1);
        total += *fresh;
        *p = total;
        i += 1;
    }
    total
}
pub unsafe fn caller(base: &mut [i32]) -> i32 { scan(base.as_mut_ptr(), 3) }
"#;
    assert_eq!(
        cursor_dispositions(input),
        vec![("scan::p".to_owned(), "Err(RefMissing)".to_owned())],
        "an exclusive copy must not admit"
    );
}

/// **F-CUR-LOCAL-WRITE** — a WRITE through the copy is a retained alias of the
/// cursor's region, not a read view: the family holds rather than bridging it.
#[test]
fn slicecursor_a_written_copy_of_a_cursor_is_not_a_raw_view() {
    let input = r#"
pub unsafe fn scan(mut p: *mut i32, n: i32) -> i32 {
    let mut i = 0i32;
    p = p.offset(4);
    while i < n {
        let fresh = p;
        p = p.offset(-1);
        *fresh = i;
        i += 1;
    }
    i
}
pub unsafe fn caller(base: &mut [i32]) -> i32 { scan(base.as_mut_ptr(), 3) }
"#;
    assert_eq!(
        cursor_dispositions(input),
        vec![("scan::p".to_owned(), "Err(RefMissing)".to_owned())],
        "a written copy must not admit — here the model refuses first"
    );
}

/// **F-CUR-LOCAL-TWICE** — a copy used twice is not ephemeral: the receipt
/// model is one access per bridge, so the family holds.
#[test]
fn slicecursor_a_twice_used_copy_of_a_cursor_is_not_a_raw_view() {
    let input = r#"
pub unsafe fn scan(mut p: *const i32, n: i32) -> i32 {
    let mut total = 0i32;
    let mut i = 0i32;
    p = p.offset(4);
    while i < n {
        let fresh = p;
        p = p.offset(-1);
        total += *fresh + *fresh;
        i += 1;
    }
    total
}
pub unsafe fn caller(base: &[i32]) -> i32 { scan(base.as_ptr(), 3) }
"#;
    assert_eq!(
        cursor_dispositions(input),
        vec![("scan::p".to_owned(), "Err(UseUnbuilt)".to_owned())],
        "a twice-used copy must not admit"
    );
}

/// **F-CUR-LOCAL-ANNOTATED** — an annotated declaration fixes the copy's type,
/// which the raw view may not match: the family holds.
#[test]
fn slicecursor_an_annotated_copy_of_a_cursor_is_not_a_raw_view() {
    let input = r#"
pub unsafe fn scan(mut p: *const i32, n: i32) -> i32 {
    let mut total = 0i32;
    let mut i = 0i32;
    p = p.offset(4);
    while i < n {
        let fresh: *const i32 = p;
        p = p.offset(-1);
        total += *fresh;
        i += 1;
    }
    total
}
pub unsafe fn caller(base: &[i32]) -> i32 { scan(base.as_ptr(), 3) }
"#;
    assert_eq!(
        cursor_dispositions(input),
        vec![("scan::p".to_owned(), "Err(UseUnbuilt)".to_owned())],
        "an annotated copy must not admit"
    );
}

/// **W-CUR-PEER-LET** — `let base_ip = ip;` binds a second cursor over the same
/// base (brotli's two-pass terminal, report 040). The destination is this
/// family's own candidate, so it owns its constructor — the shared wrapper is
/// `Copy` — and the copy itself needs no edit, exactly as the assignment form
/// `data = start` does one statement shape over.
#[test]
fn slicecursor_let_bound_peer_is_the_peers_own_constructor() {
    let input = r#"
pub unsafe fn walk(buf: &[u8], n: usize) -> u32 {
    let mut ip: *const u8 = buf.as_ptr().add(4);
    let base_ip = ip;
    let mut total = 0u32;
    let mut i = 0usize;
    while i < n {
        if ip >= base_ip { total += *ip as u32 + *base_ip.offset(-1) as u32; }
        ip = ip.offset(-1);
        i += 1;
    }
    total
}
"#;
    let source = emitted(input);
    save_fixture("peer-let", input, &source);
    assert!(
        source.contains("base_ip: crate::slice_cursor::SliceCursor<'_, u8> = ip;"),
        "the peer's initialiser is not the bare cursor it copies: {source}"
    );
    assert!(
        source.contains("slice_cursor::SliceCursor"),
        "the pair did not deliver: {source}"
    );
    compile(
        &source,
        Some("fn main() { let b = [0u8, 1, 2, 3, 4, 5]; assert_eq!(unsafe { walk(&b, 3) }, 7); }"),
    );
}

/// **W-CUR-ARG-NOT-RETURN** — the argument path does not consult the OWNER's
/// return type (relay 046 / main 062a §3, measured rather than read). Two
/// bodies identical but for the owner's signature — one returning `()`, one
/// returning a raw pointer it never hands the subject to — settle the SAME
/// receipt, so the hold on a bare cursor argument at a local callee is the raw
/// boundary's site permit and nothing about the owner's return.
///
/// `raw_return`'s preconditions (the three `RawBoundaryUnbuilt` sites inside it)
/// are reachable only from `Ret(..)` and the body's tail expression; a void
/// owner has neither. If someone ever routes the argument path through them,
/// the two receipts here stop agreeing.
#[test]
fn slicecursor_the_argument_path_does_not_ask_the_owners_return_type() {
    let void_owner = r#"
unsafe fn core_loop(input: *const u8, base_ip: *const u8, n: usize, out: *mut u32) {
    let mut ip = input;
    let mut i = 0usize;
    while i < n {
        let candidate = ip.offset(-1);
        if candidate >= base_ip { *out = *candidate as u32; }
        ip = ip.offset(1);
        i += 1;
    }
}
pub unsafe fn two_pass(mut input: *const u8, mut input_size: usize, out: *mut u32) {
    while input_size > 0 {
        let block_size = if input_size < 8 { input_size } else { 8 };
        core_loop(input, input, block_size, out);
        input = input.offset(block_size as isize);
        input_size -= block_size;
    }
}
pub unsafe fn caller(b: &[u8], out: *mut u32) { two_pass(b.as_ptr(), b.len(), out) }
"#;
    let raw_returning_owner = void_owner
        .replace(
            "pub unsafe fn two_pass(mut input: *const u8, mut input_size: usize, out: *mut u32) {",
            "pub unsafe fn two_pass(mut input: *const u8, mut input_size: usize, out: *mut u32) -> *const u8 {",
        )
        .replace(
            "        input_size -= block_size;\n    }\n}",
            "        input_size -= block_size;\n    }\n    core::ptr::null()\n}",
        )
        .replace(
            "pub unsafe fn caller(b: &[u8], out: *mut u32) { two_pass(b.as_ptr(), b.len(), out) }",
            "pub unsafe fn caller(b: &[u8], out: *mut u32) -> *const u8 { two_pass(b.as_ptr(), b.len(), out) }",
        );
    let void = cursor_dispositions(void_owner);
    let raw = cursor_dispositions(&raw_returning_owner);
    assert!(
        void.iter()
            .any(|(label, disposition)| label == "two_pass::input"
                && disposition == "Err(RawBoundaryUnbuilt)"),
        "the void owner's hold moved: {void:?}"
    );
    assert_eq!(
        void.iter()
            .find(|(label, _)| label == "two_pass::input")
            .map(|(_, disposition)| disposition.clone()),
        raw.iter()
            .find(|(label, _)| label == "two_pass::input")
            .map(|(_, disposition)| disposition.clone()),
        "the owner's return type changed the ARGUMENT path's receipt: {void:?} vs {raw:?}"
    );
}

/// The owner-level family-fallback causes a program records: the receipt whose
/// `slice-use-adapter` line withdraws a whole `Return` family.
fn family_fallback_causes(input: &str) -> Vec<String> {
    utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        ctx.raw_boundary_artifacts
            .additive_family_receipts
            .iter()
            .map(|receipt| receipt.cause.clone())
            .collect::<Vec<_>>()
    })
    .expect("family receipts")
}

/// lodepng `countZeros`, the census's `ptr-comparison` / `sole_blocker = 1`
/// pair (`data#1`, `end#9`), reproduced whole: `start = data.offset(pos)`,
/// `end = start.offset(258)` clamped, `data = start`, then
/// `while data != end && *data == 0 { data = data.offset(1) }`.
///
/// The slice family delivers the shared root `start`; the `slice-use-adapter`
/// it plants there is then dropped `slice-use-evidence-held`, because that
/// evidence is premised on the destinations staying raw and the cursor family
/// has taken them. Reading that drop as an unsatisfied family site withdraws
/// the owner's WHOLE `Return` family — which is the receipt this lane found on
/// the corpus at `batch25` (report 051) and reproduces here on a fixture, so it
/// is this shape and not the composed line.
///
/// A site a later family replaced is not a site that failed: R397-6(a)'s own
/// invariant, which `superseded_by_an_option_destination` already restores for
/// the Option family. This asserts it for a cursor destination.
///
/// **Necessary, not sufficient** (report 053): the pair still does not deliver,
/// because `end`'s delivered base — `start`'s slice, built on a fabricated
/// extent — fails `provider_delivered`, and because `data` is re-seeded
/// (`data = start`) so its base binding changes, which is wave-6o's re-seeded
/// walker, not this arm. The claim here is exactly that the slice adapter no
/// longer withdraws the owner.
#[test]
fn slicecursor_a_cursor_destination_supersedes_the_slice_adapter_it_replaces() {
    let input = r#"
unsafe extern "C" fn countZeros(mut data: *const u8, mut size: usize, mut pos: usize) -> u32 {
    let mut start = data.offset(pos as isize);
    let mut end = start.offset(258 as isize);
    if end > data.offset(size as isize) { end = data.offset(size as isize); }
    data = start;
    while data != end && *data as i32 == 0 as i32 { data = data.offset(1); }
    return data.offset_from(start) as i64 as u32;
}
pub unsafe fn caller(b: &[u8]) -> u32 { countZeros(b.as_ptr(), b.len(), 0) }
"#;
    let causes = family_fallback_causes(input);
    assert!(
        !causes
            .iter()
            .any(|cause| cause.contains("slice-use-adapter")),
        "the replaced slice adapter still withdraws the owner: {causes:?}"
    );
}

/// The control: the same root, delivered the same way, with NO cursor
/// destination — the walk is gone, so nothing of this family takes `data` or
/// `end`. Whatever the receipt layer does with the adapter here, the cursor
/// supersession cannot be what did it, and the arm stays an exception rather
/// than a loosening of the drop.
#[test]
fn slicecursor_a_slice_adapter_with_no_cursor_destination_is_untouched() {
    let input = r#"
unsafe extern "C" fn countBytes(mut data: *const u8, mut size: usize, mut pos: usize) -> u32 {
    let start = data.offset(pos as isize);
    let mut end = start.offset(258 as isize);
    if end > data.offset(size as isize) { end = data.offset(size as isize); }
    return end.offset_from(start) as i64 as u32;
}
pub unsafe fn caller(b: &[u8]) -> u32 { countBytes(b.as_ptr(), b.len(), 0) }
"#;
    let decisions = cursor_decisions(input);
    assert!(
        !decisions.iter().any(|(_, cursor)| *cursor),
        "the control grew a cursor destination: {decisions:?}"
    );
}
