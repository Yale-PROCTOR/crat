//! **Relay 107 — the adversarial review of `local/wave4-57` (Codex, 10-07).**
//! One fixture per finding, each the review's own counterexample. Each is RED
//! while the inference over-claims a length the input's accesses do not prove.
//! (The field count's fixtures left with the field count, report 085.)

const PRE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, unreachable_code)]\n\
extern \"C\" { fn malloc(size: usize) -> *mut core::ffi::c_void; fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void; \
fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: usize) -> *mut core::ffi::c_void; }\n";

fn emitted(src: &str) -> String {
    match super::rewrite_m1(src) {
        super::RewriteOutcome::Emitted { source, .. } => source,
        other => panic!("fixture must survive production verify: {other:?}"),
    }
}

/// The seam ledger (the production producer's own rows).
fn seams(src: &str) -> String {
    ::utils::compilation::run_compiler_on_str(&format!("{PRE}{src}"), |tcx| {
        super::seam_tsv(tcx).expect("seam receipt")
    })
    .expect("fixture compiles")
}

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The callee bound's receipt for parameter `index` of `function`.
fn bound(src: &str, function: &str, index: usize) -> Option<String> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(&format!("{PRE}{src}"), |tcx| {
        let def = tcx
            .hir_body_owners()
            .find(|d| {
                matches!(tcx.def_kind(d.to_def_id()), rustc_hir::def::DefKind::Fn)
                    && tcx.item_name(d.to_def_id()).as_str() == function
            })
            .unwrap_or_else(|| panic!("{function} in the fixture"));
        out = super::decision::callee_bound::of_parameter(tcx, def, index)
            .map(|b| b.receipt(&super::decision::callee_bound::parameter_names(tcx, def)));
    })
    .expect("fixture compiles");
    out
}

// ---- callee_bound.rs -------------------------------------------------------

/// Finding 1a: a loop that breaks after its first read reads one element; its
/// limit `n` proves nothing about the allocation.
#[test]
fn r107_cb1a_a_loop_that_breaks_bounds_nothing_by_its_limit() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 {\n\
        let mut s = 0; let mut i: usize = 0;\n\
        while i < n { s += *p.offset(i as isize); break; }\n\
        s }\n";
    let got = bound(src, "f", 0);
    assert_ne!(got.as_deref(), Some("len-callee-bound:may:n"), "{got:?}");
}

/// Finding 1b: `i < 1 && i < n` runs to `min(1, n)`; the looser conjunct is
/// not the loop's extent.
#[test]
fn r107_cb1b_a_conjunction_of_limits_is_not_the_looser_one() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 {\n\
        let mut s = 0; let mut i: usize = 0;\n\
        while i < 1 && i < n { s += *p.offset(i as isize); i += 1; }\n\
        s }\n";
    let got = bound(src, "f", 0);
    assert_ne!(got.as_deref(), Some("len-callee-bound:may:n"), "{got:?}");
}

/// Finding 2a: `i < n as u8` with `n: u16 = 257` runs once; the narrowing cast
/// is not the identity.
#[test]
fn r107_cb2a_a_narrowing_cast_on_the_limit_is_refused() {
    let src = "pub unsafe fn f(p: *const i32, n: u16) -> i32 {\n\
        let mut s = 0; let mut i: u8 = 0;\n\
        while i < n as u8 { s += *p.offset(i as isize); i += 1; }\n\
        s }\n";
    let got = bound(src, "f", 0);
    assert_ne!(got.as_deref(), Some("len-callee-bound:may:n"), "{got:?}");
}

/// Finding 2b: `i < n.wrapping_add(2)` with `n: u8 = 255` runs once; the
/// wrapped sum is not `n + 2`.
#[test]
fn r107_cb2b_wrapping_arithmetic_on_a_narrow_limit_is_refused() {
    let src = "pub unsafe fn f(p: *const i32, n: u8) -> i32 {\n\
        let mut s = 0; let mut i: u8 = 0;\n\
        while i < n.wrapping_add(2) { s += *p.offset(i as isize); i += 1; }\n\
        s }\n";
    let got = bound(src, "f", 0);
    assert!(
        got.as_deref()
            .is_none_or(|g| !g.contains("n+2") && !g.contains("n + 2")),
        "{got:?}"
    );
}

/// Finding 9: an access after a nested block's `return` never runs; it is not
/// a `must` access.
#[test]
fn r107_cb9_an_access_after_a_nested_return_is_not_must() {
    let src = "pub unsafe fn f(p: *const i32) -> i32 {\n\
        let x = *p; { return x; } *p.offset(99) }\n";
    let got = bound(src, "f", 0);
    assert_ne!(got.as_deref(), Some("len-callee-bound:must:100"), "{got:?}");
}

/// Finding 8b: an integer argument that calls a function is not effect-free;
/// the length must not evaluate it again.
#[test]
fn r107_cb8_a_calling_argument_is_not_duplicated_into_the_length() {
    let src = "static mut CALLS: usize = 0;\n\
        pub unsafe fn next() -> usize { CALLS += 1; CALLS }\n\
        pub unsafe fn g(p: *const i32, n: usize) -> i32 {\n\
        let mut s = 0; let mut i: usize = 0;\n\
        while i < n { s += *p.offset(i as isize); i += 1; }\n\
        s }\n\
        pub unsafe fn caller(base: *const i32, k: isize) -> i32 { g(base.offset(k), (next)()) }\n";
    let rows = seams(src);
    let row = rows
        .lines()
        .find(|l| l.starts_with("placed\tg\t"))
        .unwrap_or_else(|| panic!("{rows}"));
    // The callee bound refuses a calling argument (its own length is not
    // taken); what else answers here is printed for the record.
    assert!(!row.contains("len-callee-bound"), "{row}");
    println!("CB8 ROW {row}");
}

// ---- the callee bound's full-file round (Codex, 10-07) ---------------------

/// F1: `(n as u8)` with `n: i8 = -1` is index 255; `n + 1` would be 0.
#[test]
fn r107_cbf1_a_sign_changing_index_cast_is_refused() {
    let src = "pub unsafe fn f(p: *const u8, n: i8) -> u8 { *p.offset((n as u8) as isize) }\n";
    let got = bound(src, "f", 0);
    assert!(got.as_deref().is_none_or(|g| !g.contains('n')), "{got:?}");
}

/// F2: `n.wrapping_add(1)` with `n = usize::MAX` is index 0; `n + 2` would
/// wrap at the render and under-bound the other access.
#[test]
fn r107_cbf2_a_64_bit_wrapping_index_is_refused() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 { *p.offset(n.wrapping_add(1) as isize) + *p.offset(2) }\n";
    let got = bound(src, "f", 0);
    assert!(got.as_deref().is_none_or(|g| !g.contains('n')), "{got:?}");
}

/// F3: `max(2n, 5)` must render with the product parenthesized (the bound's
/// own rendering, read directly: the emission of a signed index is not this
/// test's subject).
#[test]
fn r107_cbf3_a_product_term_renders_parenthesized() {
    let src =
        "pub unsafe fn f(p: *const i32, n: isize) -> i32 { *p.offset(n + n - 1) + *p.offset(4) }\n";
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(&format!("{PRE}{src}"), |tcx| {
        let def = tcx
            .hir_body_owners()
            .find(|d| tcx.item_name(d.to_def_id()).as_str() == "f")
            .expect("f");
        out = super::decision::callee_bound::of_parameter(tcx, def, 0)
            .map(|b| b.render_count(&|_| "n".to_owned()));
    })
    .expect("fixture compiles");
    let text = out.expect("a bound");
    assert!(!text.starts_with("2 * ((n) as i128).max("), "{text}");
}

/// F4a: two increments per iteration skip the last index.
#[test]
fn r107_cbf4a_two_increments_per_iteration_give_no_bound() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 {\n\
        let mut s = 0; let mut i: usize = 0;\n\
        while i < n { s += *p.offset(i as isize); i += 1; i += 1; }\n\
        s }\n";
    let got = bound(src, "f", 0);
    assert_ne!(got.as_deref(), Some("len-callee-bound:may:n"), "{got:?}");
}

/// F4b: a read guarded inside the loop need not run at the last index.
#[test]
fn r107_cbf4b_a_guarded_read_in_a_loop_gives_no_loop_bound() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 {\n\
        let mut s = 0; let mut i: usize = 0;\n\
        while i < n { if i == 0 { s += *p.offset(i as isize); } i += 1; }\n\
        s }\n";
    let got = bound(src, "f", 0);
    assert_ne!(got.as_deref(), Some("len-callee-bound:may:n"), "{got:?}");
}

/// F5: a user function NAMED `wrapping_add` is a call with effects.
#[test]
fn r107_cbf5_a_function_named_like_a_primitive_is_a_call() {
    let src = "static mut COUNTER: usize = 0;\n\
        pub unsafe fn wrapping_add() -> usize { COUNTER += 1; COUNTER }\n\
        pub unsafe fn read_at(p: *const i32, n: usize) -> i32 { *p.offset(n as isize) }\n\
        pub unsafe fn caller(base: *const i32, k: isize) -> i32 { read_at(base.offset(k), wrapping_add()) }\n";
    let out = flat(&emitted(&format!("{PRE}{src}")));
    let call = out.split("fn caller").nth(1).unwrap_or("");
    assert!(call.matches("wrapping_add()").count() <= 1, "{out}");
}

/// F6: `!0` for a `u8` parameter is 255; the copied text must keep that type.
#[test]
fn r107_cbf6_an_instantiated_argument_keeps_its_parameter_type() {
    let src = "pub unsafe fn read_at(p: *const u8, n: u8) -> u8 { *p.offset(n as isize) }\n\
        pub unsafe fn caller(base: *const u8, k: isize) -> u8 { read_at(base.offset(k), !0) }\n";
    let out = flat(&emitted(&format!("{PRE}{src}")));
    assert!(!out.contains("((!0) as i128)"), "{out}");
}
