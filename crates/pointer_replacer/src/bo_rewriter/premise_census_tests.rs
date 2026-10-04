//! R801-2 (USER), main 163: the witnesses of P7's census receipt. Each is an
//! input beside the final emitted tree the code generator made of it.

use super::premise_census::{
    BridgedCall, Reading, SiteKind, bridged_calls, census_lines, read_program,
};

fn read(input: &str, emitted: &str, bridged: &[BridgedCall]) -> Reading {
    read_program(
        &syn::parse_file(input).expect("input parses"),
        &syn::parse_file(emitted).expect("emitted parses"),
        bridged,
    )
}

fn kinds(reading: &Reading) -> Vec<(SiteKind, &str, &str)> {
    reading
        .rows
        .iter()
        .map(|row| (row.kind, row.function.as_str(), row.binding.as_str()))
        .collect()
}

/// A construction the input dereferences in the very next item: (b) holds, P1
/// covers it, no row.
#[test]
fn r801_2_a_construction_dereferenced_next_has_no_row() {
    let reading = read(
        "pub mod m { pub unsafe fn f(p: *const u8) -> u8 {
            let mut x: *const u8 = p;
            let v = *x.offset(1);
            v
        } }",
        "pub mod m { pub unsafe fn f(p: *const u8) -> u8 {
            let mut x: &[u8] = core::slice::from_raw_parts(p, crate::FALLBACK_SLICE_EXTENT);
            let v = x[1];
            v
        } }",
        &[],
    );
    assert!(reading.rows.is_empty(), "{reading:?}");
    assert_eq!(
        reading.held_b.get(&SiteKind::DeclarationConstruction),
        Some(&1)
    );
}

/// buffer `buffer_indexof::sub`'s shape: the null test returns, then the pointer
/// is only measured. (b) fails: a row, and the dominance reading fails too.
#[test]
fn r801_2_a_construction_measured_but_never_dereferenced_has_a_row() {
    let reading = read(
        "pub mod m { pub unsafe fn f(data: *mut i8, s: *const i8) -> i64 {
            let mut sub: *mut i8 = strstr(data, s);
            if sub.is_null() { return -1; }
            return sub.offset_from(data) as i64;
        } }",
        "pub mod m { pub unsafe fn f(data: *mut i8, s: *const i8) -> i64 {
            let mut sub: &mut [i8] = { let p = strstr(data, s); core::slice::from_raw_parts_mut(p, 1024) };
            if sub.is_empty() { return -1; }
            return sub.as_mut_ptr().offset_from(data) as i64;
        } }",
        &[],
    );
    assert_eq!(
        kinds(&reading),
        vec![(SiteKind::DeclarationConstruction, "m::f", "sub")]
    );
    assert_eq!(
        reading.rows[0].rule_b,
        "an early-exit null test, then no dereference"
    );
    assert!(!reading.rows[0].quiet_prefix);
}

/// An early-exiting null test, then a dereference: (b) holds.
#[test]
fn r801_2_an_early_exit_null_test_then_a_dereference_has_no_row() {
    let reading = read(
        "pub mod m { pub unsafe fn f(p: *mut i32) -> i32 {
            let mut x: *mut i32 = p;
            if x.is_null() { return 0; }
            *x = 1;
            0
        } }",
        "pub mod m { pub unsafe fn f(p: *mut i32) -> i32 {
            let mut x = p.as_mut();
            if x.is_none() { return 0; }
            *x.unwrap() = 1;
            0
        } }",
        &[],
    );
    assert!(reading.rows.is_empty(), "{reading:?}");
    assert_eq!(reading.held_b.get(&SiteKind::DeclarationView), Some(&1));
}

/// A view whose next item is an unrelated call: a row, of the view kind.
#[test]
fn r801_2_a_view_followed_by_an_unrelated_call_has_a_row() {
    let reading = read(
        "pub mod m { pub unsafe fn f(p: *mut i32) {
            let mut x: *mut i32 = p;
            log_it();
            *x = 1;
        } }",
        "pub mod m { pub unsafe fn f(p: *mut i32) {
            let mut x = p.as_mut().unwrap();
            log_it();
            *x = 1;
        } }",
        &[],
    );
    assert_eq!(
        kinds(&reading),
        vec![(SiteKind::DeclarationView, "m::f", "x")]
    );
    assert!(!reading.rows[0].quiet_prefix);
}

/// libtree `print_error::runpath`'s shape: the generator re-binds a raw FORMAL
/// as a reborrow; the input's first item is an unrelated call.
#[test]
fn r801_2_a_reborrow_of_a_formal_used_first_by_an_unrelated_call_has_a_row() {
    let reading = read(
        "pub mod m { pub unsafe fn f(runpath: *const i8) {
            fputs(b\"x\\0\".as_ptr() as *const i8, stderr);
            g(runpath);
        } }",
        "pub mod m { pub unsafe fn f(runpath: *const i8) {
            let runpath: &i8 = &*runpath;
            fputs(b\"x\\0\".as_ptr() as *const i8, stderr);
            g(runpath);
        } }",
        &[],
    );
    assert_eq!(
        kinds(&reading),
        vec![(SiteKind::DeclarationReborrow, "m::f", "runpath")]
    );
}

/// A quiet item (no call, no exit) before the dereference: (b) as built fails,
/// the dominance reading clears it. Both are on the row.
#[test]
fn r801_2_a_quiet_prefix_is_recorded_beside_rule_b() {
    let reading = read(
        "pub mod m { pub unsafe fn f(p: *const u32, k: usize) -> u32 {
            let mut x: *const u32 = p;
            let j = k.wrapping_add(1);
            *x.offset(j as isize)
        } }",
        "pub mod m { pub unsafe fn f(p: *const u32, k: usize) -> u32 {
            let mut x: &[u32] = core::slice::from_raw_parts(p, 1024);
            let j = k.wrapping_add(1);
            x[j]
        } }",
        &[],
    );
    assert_eq!(reading.rows.len(), 1, "{reading:?}");
    assert!(reading.rows[0].quiet_prefix);
}

/// tulip's exposure wrapper: the views are made after the size test and handed
/// whole to the safe twin. (b) holds by the family's shape: no row, counted apart.
#[test]
fn r801_2_an_exposure_wrapper_has_no_row() {
    let reading = read(
        "pub mod m { pub unsafe extern \"C\" fn ti_x(size: i32, inputs: *const f64) -> i32 {
            let mut i: i32 = 0;
            while i < size { i += 1; }
            0
        } }",
        "pub mod m {
            pub unsafe extern \"C\" fn ti_x(size: i32, inputs: *const f64) -> i32 {
                if size <= 0 { return 0; }
                let inputs_0 = core::slice::from_raw_parts(inputs, size as usize);
                __crat_safe_ti_x(size, inputs_0)
            }
            unsafe fn __crat_safe_ti_x(size: i32, inputs: &[f64]) -> i32 {
                let mut i: i32 = 0;
                while i < size { i += 1; }
                0
            }
        }",
        &[],
    );
    assert!(reading.rows.is_empty(), "{reading:?}");
    assert_eq!(reading.exempt_exposure, 1);
}

/// A site the verify rounds reverted keeps the input's raw declaration: nothing.
#[test]
fn r801_2_a_reverted_site_has_no_row() {
    let source = "pub mod m { pub unsafe fn f(p: *const u8) -> u8 {
        let mut x: *const u8 = p;
        log_it();
        *x
    } }";
    let reading = read(source, source, &[]);
    assert_eq!(reading, Reading::default());
}

/// R758-1 (β): a delivered thin formal its callers bridge from a raw pointer.
/// Not dereferenced first: a row per bridged call. Dereferenced first: no row.
/// A formal the tree keeps raw (its class reverted): nothing.
#[test]
fn r801_2_call_bridges_are_read_at_the_callee_entry() {
    let input = "pub mod m {
        pub unsafe fn g(q: *mut i32) { log_it(); *q = 1; }
        pub unsafe fn k(q: *mut i32) { *q = 1; log_it(); }
        pub unsafe fn r(q: *mut i32) { log_it(); *q = 1; }
    }";
    let emitted = "pub mod m {
        pub unsafe fn g(q: &mut i32) { log_it(); *q = 1; }
        pub unsafe fn k(q: &mut i32) { *q = 1; log_it(); }
        pub unsafe fn r(q: *mut i32) { log_it(); *q = 1; }
    }";
    let call = |callee: &str, site: &str| BridgedCall {
        callee: callee.to_owned(),
        formal: 0,
        caller: "m::main_0".to_owned(),
        site: site.to_owned(),
    };
    let reading = read(
        input,
        emitted,
        &[
            call("m::g", "1"),
            call("m::g", "2"),
            call("m::k", "3"),
            call("m::r", "4"),
        ],
    );
    assert_eq!(
        kinds(&reading),
        vec![
            (SiteKind::CallBridge, "m::g", "q"),
            (SiteKind::CallBridge, "m::g", "q")
        ]
    );
    assert_eq!(reading.call_bridge_formals, 1);
    assert_eq!(reading.held_b.get(&SiteKind::CallBridge), Some(&1));
    assert_eq!(reading.rows[1].site, "m::main_0@2");
}

/// The census's adapters table: only placed raw-to-reference bridges count.
#[test]
fn r801_2_bridged_calls_read_placed_reborrow_adapters_only() {
    let tsv = "program\tkind\towner_fn\tsite\tcaller\tparam_index\ttemplate\n\
        p\tplaced\tm::g\tlib.rs:1:1\tm::a\t0\tc-raw-reborrow-mut\n\
        p\tplaced\tm::h\tlib.rs:2:1\tm::a\t1\tc-raw-slice-mut\n\
        p\tblocked\tm::g\tlib.rs:3:1\tm::a\t0\tc-raw-reborrow-shared\n\
        p\tplaced\tm::k\tlib.rs:4:1\tm::b\t2\tc-raw-reborrow-shared\n";
    let calls = bridged_calls(tsv);
    assert_eq!(
        calls
            .iter()
            .map(|call| (call.callee.as_str(), call.formal))
            .collect::<Vec<_>>(),
        vec![("m::g", 0), ("m::k", 2)]
    );
}

/// The census receipt's lines: the total, by kind, by program, and the counts
/// the rows do not carry.
#[test]
fn r801_2_census_lines_count_by_kind_and_program() {
    let reading = read(
        "pub mod m { pub unsafe fn f(p: *mut i32) { let mut x: *mut i32 = p; log_it(); *x = 1; } }",
        "pub mod m { pub unsafe fn f(p: *mut i32) { let mut x = p.as_mut().unwrap(); log_it(); *x = 1; } }",
        &[],
    );
    let lines = census_lines(&[("p", Ok(reading)), ("q", Err("missing".to_owned()))]);
    assert!(
        lines.contains("premise_bridge_dereferenceable=1\n"),
        "{lines}"
    );
    assert!(lines.contains(
        "premise_bridge_dereferenceable_kinds=call-bridge:0,declaration-view:1,declaration-construction:0,declaration-reborrow:0\n"
    ));
    assert!(lines.contains("premise_bridge_dereferenceable_by_program=p:1\n"));
    assert!(lines.contains("premise_bridge_dereferenceable_unreadable=q:missing\n"));
}

/// brotli `FindLongestMatchH2::buckets` (162 §1): the input declares the binding
/// without a type (`let mut buckets = (*self_0).buckets_;`). The emitted
/// construction is still a reference made from that raw pointer.
#[test]
fn r801_2_an_unannotated_input_declaration_is_read() {
    let reading = read(
        "pub mod m { pub unsafe fn f(self_0: *mut H, out: *mut R, key: usize) {
            let mut buckets = (*self_0).buckets_;
            let best = (*out).len;
            *buckets.offset(key as isize) = best;
        } }",
        "pub mod m { pub unsafe fn f(self_0: &mut H, out: &mut R, key: usize) {
            let mut buckets: &mut [u32] = core::slice::from_raw_parts_mut((*self_0).buckets_, crate::FALLBACK_SLICE_EXTENT);
            let best = (*out).len;
            buckets[key] = best;
        } }",
        &[],
    );
    assert_eq!(
        kinds(&reading),
        vec![(SiteKind::DeclarationConstruction, "m::f", "buckets")]
    );
    assert!(reading.rows[0].quiet_prefix);
    assert_eq!(reading.unread, 0);
}

/// tulip's `__crat_safe_ti_*`: `&mut *outputs[0]` reborrows an element of an
/// already-safe slice; no reference is made from a raw pointer there (162 §0).
#[test]
fn r801_2_a_reborrow_of_an_already_safe_element_has_no_row() {
    let reading = read(
        "pub mod m { pub unsafe fn ti_x(outputs: *mut *mut f64) -> i32 {
            let mut output: *mut f64 = *outputs.offset(0);
            0
        } }",
        "pub mod m { pub unsafe fn ti_x(outputs: &mut [&mut [f64]]) -> i32 {
            let mut output: &mut [f64] = &mut *outputs[0];
            0
        } }",
        &[],
    );
    assert_eq!(reading, Reading::default());
}

/// brotli `FindLongestMatchH42::key`: `let key = HashBytesH42(from_raw_parts(..))`
/// makes the slice at the CALL, not at the declaration of `key`.
#[test]
fn r801_2_a_construction_inside_an_initializers_call_is_not_the_declarations() {
    let source = |init: &str| {
        format!(
            "pub mod m {{ pub unsafe fn f(data: *const u8, ix: usize) -> u32 {{
                let mut key = {init};
                log_it();
                key
            }} }}"
        )
    };
    let reading = read(
        &source("HashBytes(&*data.offset(ix as isize))"),
        &source(
            "HashBytes(core::slice::from_raw_parts(&*data.offset(ix as isize), crate::FALLBACK_SLICE_EXTENT))",
        ),
        &[],
    );
    assert_eq!(reading, Reading::default());
}

/// json.h `json_write_number::{inf, nan}`: a slice over a string literal points
/// at static storage nothing releases. Counted apart, no row.
#[test]
fn r801_2_a_construction_over_a_string_literal_has_no_row() {
    let reading = read(
        "pub mod m { pub unsafe fn f() -> u8 {
            let mut inf: *const i8 = b\"Infinity\\0\" as *const u8 as *const i8;
            let mut k: usize = 0;
            *inf.offset(k as isize) as u8
        } }",
        "pub mod m { pub unsafe fn f() -> u8 {
            let mut inf: &[i8] = core::slice::from_raw_parts(b\"Infinity\\0\" as *const u8 as *const i8, crate::FALLBACK_SLICE_EXTENT);
            let mut k: usize = 0;
            inf[k] as u8
        } }",
        &[],
    );
    assert!(reading.rows.is_empty(), "{reading:?}");
    assert_eq!(reading.exempt_literal, 1);
}

/// buffer `buffer_indexof::sub` / libtree `interpolate_variables::dollar` (162
/// §1): the Option family's fat view, `p.as_ref().map(|p| from_raw_parts(p, n))`.
#[test]
fn r801_2_a_construction_mapped_over_an_option_view_is_read() {
    let reading = read(
        "pub mod m { pub unsafe fn f(data: *mut i8, s: *const i8) -> i64 {
            let mut sub: *mut i8 = strstr(data, s);
            if sub.is_null() { return -1; }
            return sub.offset_from(data) as i64;
        } }",
        "pub mod m { pub unsafe fn f(data: *mut i8, s: *const i8) -> i64 {
            let mut sub: Option<&[i8]> = {
                let __crat_slice_ptr_4: *const _ = strstr(data, s);
                __crat_slice_ptr_4.as_ref().map(|p| core::slice::from_raw_parts(p, crate::FALLBACK_SLICE_EXTENT))
            };
            if sub.is_none() { return -1; }
            return sub.unwrap().as_ptr().offset_from(data) as i64;
        } }",
        &[],
    );
    assert_eq!(
        kinds(&reading),
        vec![(SiteKind::DeclarationConstruction, "m::f", "sub")]
    );
}
