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
