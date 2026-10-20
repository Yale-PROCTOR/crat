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
        "premise_bridge_dereferenceable_kinds=call-bridge:0,declaration-view:1,declaration-construction:0,declaration-reborrow:0,assignment-view:0,assignment-construction:0,assignment-reborrow:0,assignment-option-construction:0\n"
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

/// wave-6o 106a (a): the view families' own table replaces this reader's view
/// kind (rows and held count); an empty or header-less table changes nothing.
#[test]
fn r801_2_the_view_families_table_is_the_view_kind() {
    let reading = || {
        read(
            "pub mod m { pub unsafe fn f(p: *mut i32) { let mut x: *mut i32 = p; log_it(); *x = 1; } }",
            "pub mod m { pub unsafe fn f(p: *mut i32) { let mut x = p.as_mut().unwrap(); log_it(); *x = 1; } }",
            &[],
        )
    };
    let mut merged = reading();
    let lane = "corpus\tprogram\tfunction\tbinding\tsite\trule_b\tquiet_prefix\n\
        rs-crown\tlil\tsrc::lil::fnc_reflect\ttarget\tlib.rs:140:9: 140:40\tthe next item: if\tfails\n\
        rs-crown\tlil\tsrc::lil::lil_get_var_or\tvar\tlib.rs:200:9: 200:30\tthe next item: x\tclears\n";
    assert!(super::premise_census::merge_lane_views(&mut merged, lane));
    assert!(merged.lane_views);
    assert_eq!(
        kinds(&merged),
        vec![
            (SiteKind::DeclarationView, "src::lil::fnc_reflect", "target"),
            (SiteKind::DeclarationView, "src::lil::lil_get_var_or", "var")
        ]
    );
    assert!(merged.rows[1].quiet_prefix);
    let mut untouched = reading();
    assert!(!super::premise_census::merge_lane_views(
        &mut untouched,
        "corpus\tprogram\t\n"
    ));
    assert_eq!(untouched, reading());
}

/// **R857-3 (075 §S7(b)).** bzip2 `addFlagsFromEnvVar::envbase`'s shape: a view
/// written at an ASSIGNMENT (the binding is declared `None`), whose next input
/// item is an unrelated call. (b) fails: a row of the assignment kind, with its
/// own site identity.
#[test]
fn r857_3_an_assignment_view_not_dereferenced_next_has_a_row() {
    let reading = read(
        "pub mod m { pub unsafe fn f(name: *const i8) {
            let mut envbase: *mut i8 = 0 as *mut i8;
            envbase = getenv(name);
            log_it();
            if !envbase.is_null() { *envbase = 0; }
        } }",
        "pub mod m { pub unsafe fn f(name: *const i8) {
            let mut envbase: Option<&mut i8> = None;
            envbase = (getenv(name) as *mut i8).as_mut();
            log_it();
            if let Some(e) = envbase { *e = 0; }
        } }",
        &[],
    );
    assert_eq!(
        kinds(&reading),
        vec![(SiteKind::AssignmentView, "m::f", "envbase")]
    );
    assert_eq!(SiteKind::AssignmentView.key(), "assignment-view");
    assert_eq!(reading.rows[0].site, "assign#1");
    assert!(!reading.rows[0].quiet_prefix);
}

/// An assignment view the input dereferences in the very next item: (b) holds,
/// no row, counted as held of the assignment kind.
#[test]
fn r857_3_an_assignment_view_dereferenced_next_has_no_row() {
    let reading = read(
        "pub mod m { pub unsafe fn f(p: *mut i32) {
            let mut x: *mut i32 = 0 as *mut i32;
            x = p;
            *x = 1;
        } }",
        "pub mod m { pub unsafe fn f(p: *mut i32) {
            let mut x: Option<&mut i32> = None;
            x = p.as_mut();
            *x.unwrap() = 1;
        } }",
        &[],
    );
    assert!(reading.rows.is_empty(), "{reading:?}");
    assert_eq!(reading.held_b.get(&SiteKind::AssignmentView), Some(&1));
}

/// An assignment to a binding the input declares as a non-pointer is not a
/// reference the generator made from a raw pointer: no row, nothing held.
#[test]
fn r857_3_an_assignment_to_a_non_pointer_binding_is_not_read() {
    let reading = read(
        "pub mod m { pub unsafe fn f(p: &mut i32) {
            let mut x: Option<&mut i32> = None;
            x = Some(p);
            log_it();
        } }",
        "pub mod m { pub unsafe fn f(p: &mut i32) {
            let mut x: Option<&mut i32> = None;
            x = (p as *mut i32).as_mut();
            log_it();
        } }",
        &[],
    );
    assert!(reading.rows.is_empty(), "{reading:?}");
    assert!(reading.held_b.is_empty(), "{reading:?}");
}

/// **The stand-in review of R857-3, MED-1.** The generator removed one of the
/// binding's assignments (a cursor's `p = p.offset(1)` became `p.seek(1)`), so
/// the emitted second assignment is the input's THIRD: pairing by ordinal would
/// read the wrong input site (a false `held`). A different count is not read.
#[test]
fn r857_3_an_assignment_the_generator_removed_makes_the_binding_unread() {
    let reading = read(
        "pub mod m { pub unsafe fn f(a: *mut i32, b: *mut i32) {
            let mut p: *mut i32 = 0 as *mut i32;
            p = a;
            p = p.offset(1);
            *p = 0;
            p = b;
            log_it();
            *p = 1;
        } }",
        "pub mod m { pub unsafe fn f(a: *mut i32, b: *mut i32) {
            let mut p: Option<&mut i32> = None;
            p = a.as_mut();
            *p.unwrap() = 0;
            p = b.as_mut();
            log_it();
            *p.unwrap() = 1;
        } }",
        &[],
    );
    assert!(reading.rows.is_empty(), "{reading:?}");
    assert!(reading.held_b.is_empty(), "{reading:?}");
    assert_eq!(reading.unread, 2, "{reading:?}");
}

/// json.h `json_write_pretty::indent`'s shape: a raw FORMAL re-assigned with a
/// slice construction, the next input item unrelated: a row of the
/// assignment-construction kind.
#[test]
fn r857_3_a_construction_assigned_to_a_raw_formal_has_a_row() {
    let reading = read(
        "pub mod m { pub unsafe fn f(mut s: *const u8) -> u8 {
            s = g();
            log_it();
            *s
        } }",
        "pub mod m { pub unsafe fn f(mut s: &[u8]) -> u8 {
            s = core::slice::from_raw_parts(g(), 1024);
            log_it();
            s[0]
        } }",
        &[],
    );
    assert_eq!(
        kinds(&reading),
        vec![(SiteKind::AssignmentConstruction, "m::f", "s")]
    );
    assert_eq!(reading.rows[0].site, "assign#1");
}

/// A non-empty lanes table carries the views and the Option family's nullable
/// constructions at assignments: the reader's rows of exactly those kinds give
/// way; a bare construction (the slice family's sized assignment) stays.
#[test]
fn r857_3_a_lanes_table_replaces_only_the_option_familys_assignment_rows() {
    let mut reading = read(
        "pub mod m { pub unsafe fn f(name: *const i8, mut s: *const u8, mut t: *const u8) {
            let mut envbase: *mut i8 = 0 as *mut i8;
            envbase = getenv(name);
            log_it();
            s = g();
            log_it();
            t = g();
            log_it();
        } }",
        "pub mod m { pub unsafe fn f(name: *const i8, mut s: &[u8], mut t: Option<&[u8]>) {
            let mut envbase: Option<&mut i8> = None;
            envbase = (getenv(name) as *mut i8).as_mut();
            log_it();
            s = core::slice::from_raw_parts(g(), 1024);
            log_it();
            t = if g().is_null() { None } else { Some(core::slice::from_raw_parts(g(), 1024)) };
            log_it();
        } }",
        &[],
    );
    assert_eq!(
        kinds(&reading),
        vec![
            (SiteKind::AssignmentView, "m::f", "envbase"),
            (SiteKind::AssignmentConstruction, "m::f", "s"),
            (SiteKind::AssignmentOptionConstruction, "m::f", "t"),
        ]
    );
    assert!(super::premise_census::merge_lane_views(
        &mut reading,
        "function\tbinding\tsite\trule_b\tquiet_prefix\nm::f\tenvbase\tlane-site\tthe next item: log_it ()\tfails\n",
    ));
    assert_eq!(
        kinds(&reading),
        vec![
            (SiteKind::AssignmentConstruction, "m::f", "s"),
            (SiteKind::DeclarationView, "m::f", "envbase"),
        ]
    );
}

/// The pairing at a later ordinal: the binding's SECOND assignment is read
/// against the input's second (lil `fnc_func::cmd` #2's shape), and an untyped
/// raw `let` (`let mut x = 0 as *mut T;`, C2Rust's usual spelling) is raw.
#[test]
fn r857_3_the_second_assignment_of_an_untyped_raw_let_is_read_against_the_second() {
    let reading = read(
        "pub mod m { pub unsafe fn f(a: *mut i32, b: *mut i32) {
            let mut x = 0 as *mut i32;
            x = a;
            *x = 0;
            x = b;
            log_it();
            *x = 1;
        } }",
        "pub mod m { pub unsafe fn f(a: *mut i32, b: *mut i32) {
            let mut x: Option<&mut i32> = None;
            x = a.as_mut();
            *x.unwrap() = 0;
            x = b.as_mut();
            log_it();
            *x.unwrap() = 1;
        } }",
        &[],
    );
    assert_eq!(
        kinds(&reading),
        vec![(SiteKind::AssignmentView, "m::f", "x")]
    );
    assert_eq!(reading.rows[0].site, "assign#2");
    assert_eq!(reading.held_b.get(&SiteKind::AssignmentView), Some(&1));
}
