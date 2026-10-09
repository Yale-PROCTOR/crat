//! **Relay 107 / relay 112 — the callee bound's adversarial reviews (Codex,
//! 10-07).** One fixture per high finding of the three full-file rounds (3 + 6
//! + 9), each the review's own counterexample. Under R923-1's narrowed rule
//! (relay 112) every one of them takes the fallback: the module gives NO bound
//! (or, at a call site, the seam row carries no `len-callee-bound`).
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

/// The seam rows of the callee `g`'s raw argument: one exists, and none of
/// them carries a callee bound (the narrowed rule refuses the argument).
fn no_callee_bound_at_the_call(src: &str) {
    let rows = seams(src);
    assert!(
        rows.lines().any(|l| l.starts_with("placed\tg\t")),
        "the call is a seam site:\n{rows}"
    );
    assert!(!rows.contains("len-callee-bound"), "{rows}");
}

/// The loop shape the narrowed rule keeps: `g`'s own bound is `n`, so a
/// refusal at the call is the argument's. `flag` keeps the length argument
/// away from the pointer, so no companion licence answers first.
const G_U8: &str = "pub unsafe fn g(n: u8, flag: i32, p: *const u8) -> u32 {\n\
    let mut s = 0u32; let mut i: u8 = 0;\n\
    while i < n { s += *p.offset(i as isize) as u32; i += 1; }\n\
    s }\n";
const G_ISIZE: &str = "pub unsafe fn g(n: isize, flag: i32, p: *const u8) -> u32 {\n\
    let mut s = 0u32; let mut i: isize = 0;\n\
    while i < n { s += *p.offset(i) as u32; i += 1; }\n\
    s }\n";

// ---- round 1 (Codex, 10-07) ------------------------------------------------

/// Finding 1a: a loop that breaks after its first read reads one element; its
/// limit `n` proves nothing about the allocation.
#[test]
fn r107_cb1a_a_loop_that_breaks_bounds_nothing_by_its_limit() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 {\n\
        let mut s = 0; let mut i: usize = 0;\n\
        while i < n { s += *p.offset(i as isize); break; }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// Finding 1b: `i < 1 && i < n` runs to `min(1, n)`; the looser conjunct is
/// not the loop's extent.
#[test]
fn r107_cb1b_a_conjunction_of_limits_is_not_the_looser_one() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 {\n\
        let mut s = 0; let mut i: usize = 0;\n\
        while i < 1 && i < n { s += *p.offset(i as isize); i += 1; }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// Finding 2a: `i < n as u8` with `n: u16 = 257` runs once; the narrowing cast
/// is not the identity.
#[test]
fn r107_cb2a_a_narrowing_cast_on_the_limit_is_refused() {
    let src = "pub unsafe fn f(p: *const i32, n: u16) -> i32 {\n\
        let mut s = 0; let mut i: u8 = 0;\n\
        while i < n as u8 { s += *p.offset(i as isize); i += 1; }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// Finding 2b: `i < n.wrapping_add(2)` with `n: u8 = 255` runs once; the
/// wrapped sum is not `n + 2`.
#[test]
fn r107_cb2b_wrapping_arithmetic_on_a_narrow_limit_is_refused() {
    let src = "pub unsafe fn f(p: *const i32, n: u8) -> i32 {\n\
        let mut s = 0; let mut i: u8 = 0;\n\
        while i < n.wrapping_add(2) { s += *p.offset(i as isize); i += 1; }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// Finding 9: an access after a nested block's `return` never runs.
#[test]
fn r107_cb9_an_access_after_a_nested_return_is_not_must() {
    let src = "pub unsafe fn f(p: *const i32) -> i32 {\n\
        let x = *p; { return x; } *p.offset(99) }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// Finding 8b: an integer argument that calls a function is not effect-free;
/// the length must not evaluate it again.
#[test]
fn r107_cb8_a_calling_argument_is_not_duplicated_into_the_length() {
    let src = "static mut CALLS: isize = 0;\n\
        pub unsafe fn next() -> isize { CALLS += 1; CALLS }\n\
        pub unsafe fn g(n: isize, flag: i32, p: *const i32) -> i32 {\n\
        let mut s = 0; let mut i: isize = 0;\n\
        while i < n { s += *p.offset(i as isize); i += 1; }\n\
        s }\n\
        pub unsafe fn caller(base: *const i32, k: isize) -> i32 { g((next)(), 1, base.offset(k)) }\n";
    assert_eq!(
        bound(src, "g", 2).as_deref(),
        Some("len-callee-bound:may:n")
    );
    no_callee_bound_at_the_call(src);
}

// ---- round 2, the full-file round (Codex, 10-07) --------------------------

/// F1: `(n as u8)` with `n: i8 = -1` is index 255; `n + 1` would be 0.
#[test]
fn r107_cbf1_a_sign_changing_index_cast_is_refused() {
    let src = "pub unsafe fn f(p: *const u8, n: i8) -> u8 { *p.offset((n as u8) as isize) }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// F2: `n.wrapping_add(1)` with `n = usize::MAX` is index 0; `n + 2` would
/// wrap at the render and under-bound the other access.
#[test]
fn r107_cbf2_a_64_bit_wrapping_index_is_refused() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 { *p.offset(n.wrapping_add(1) as isize) + *p.offset(2) }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// F3: `max(2n, 5)` rendered without parentheses reads `2 * max(n, 5)`.
#[test]
fn r107_cbf3_a_product_term_renders_parenthesized() {
    let src =
        "pub unsafe fn f(p: *const i32, n: isize) -> i32 { *p.offset(n + n - 1) + *p.offset(4) }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// F4a: two increments per iteration skip the last index.
#[test]
fn r107_cbf4a_two_increments_per_iteration_give_no_bound() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 {\n\
        let mut s = 0; let mut i: usize = 0;\n\
        while i < n { s += *p.offset(i as isize); i += 1; i += 1; }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// F4b: a read guarded inside the loop need not run at the last index.
#[test]
fn r107_cbf4b_a_guarded_read_in_a_loop_gives_no_loop_bound() {
    let src = "pub unsafe fn f(p: *const i32, n: usize) -> i32 {\n\
        let mut s = 0; let mut i: usize = 0;\n\
        while i < n { if i == 0 { s += *p.offset(i as isize); } i += 1; }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// F5: a user function NAMED `wrapping_add` is a call with effects.
#[test]
fn r107_cbf5_a_function_named_like_a_primitive_is_a_call() {
    let src = format!(
        "static mut COUNTER: isize = 0;\n\
         pub unsafe fn wrapping_add() -> isize {{ COUNTER += 1; COUNTER }}\n\
         {G_ISIZE}\
         pub unsafe fn caller(base: *const u8, k: isize) -> u32 {{ g(wrapping_add(), 1, base.offset(k)) }}\n"
    );
    no_callee_bound_at_the_call(&src);
}

/// F6: `!0` for a `u8` parameter is 255; copied alone it reads as `i32` -1.
#[test]
fn r107_cbf6_an_instantiated_argument_keeps_its_parameter_type() {
    let src = format!(
        "{G_U8}\
         pub unsafe fn caller(base: *const u8, k: isize) -> u32 {{ g(!0, 1, base.offset(k)) }}\n"
    );
    no_callee_bound_at_the_call(&src);
}

// ---- round 3, the second full-file round (Codex, 10-07) -------------------

/// R3-1: `!0 / 2` for a `u8` parameter is 127; re-typing the copied text as
/// `((!0 / 2) as u8)` evaluates the division in `i32` (0).
#[test]
fn r112_r3_1_an_argument_with_operators_is_not_copied() {
    let src = format!(
        "{G_U8}\
         pub unsafe fn caller(base: *const u8, k: isize) -> u32 {{ g(!0 / 2, 1, base.offset(k)) }}\n"
    );
    no_callee_bound_at_the_call(&src);
}

/// R3-2: `n: u8 = 255` reads index `(255u8 as i8) + 2 = 1`; `n + 3` is no
/// bound of it.
#[test]
fn r112_r3_2_an_intermediate_sign_changing_cast_is_refused() {
    let src =
        "pub unsafe fn f(p: *const u8, n: u8) -> u8 { *p.offset(((n as i8) + 2) as isize) }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// R3-3: a closure writes the limit before the loop; the entry value of `n`
/// under-bounds the read.
#[test]
fn r112_r3_3_a_closure_writing_the_limit_is_refused() {
    let src = "pub unsafe fn f(p: *const u8, mut n: usize) -> u32 {\n\
        (|| n += 10)();\n\
        let mut s = 0u32; let mut i: usize = 0;\n\
        while i < n { s += *p.add(i) as u32; i += 1; }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// R3-4: `&raw const *p` forms an address the callee reads at index 10; it is
/// no one-element access.
#[test]
fn r112_r3_4_a_raw_address_of_the_pointee_is_refused() {
    let src = "pub unsafe fn leaf(q: *const u8) -> u8 { *q.add(10) }\n\
        pub unsafe fn f(p: *const u8) -> u8 { leaf(&raw const *p) }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// R3-5: a labelled `continue` leaves the inner loop after index 0.
#[test]
fn r112_r3_5_a_labelled_continue_is_refused() {
    let src = "pub unsafe fn f(p: *const u8, n: usize) -> u32 {\n\
        let mut s = 0u32; let mut j = 0;\n\
        'outer: while j < 1 { j += 1; let mut i: usize = 0;\n\
        while i < n { if i == 1 { continue 'outer; } s += *p.add(i) as u32; i += 1; } }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// R3-6: the callee reads only when `yes`; composed with the loop's offset,
/// its bound need not run at the last index.
#[test]
fn r112_r3_6_a_composition_at_an_offset_is_refused() {
    let src = "pub unsafe fn leaf(q: *const u8, yes: bool) -> u8 { if yes { *q } else { 0 } }\n\
        pub unsafe fn f(p: *const u8, n: usize) -> u32 {\n\
        let mut s = 0u32; let mut i: usize = 0;\n\
        while i < n { s += leaf(p.add(i), i == 0) as u32; i += 1; }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// R3-7: `n - 2` on `n: i8 = -128` wraps to 126 with overflow checks off.
#[test]
fn r112_r3_7_ordinary_arithmetic_in_the_index_is_refused() {
    let src = "pub unsafe fn f(p: *const u8, n: i8) -> u8 { *p.offset((n - 2) as isize) }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// R3-8: a user METHOD named `wrapping_add` is a call with effects.
#[test]
fn r112_r3_8_a_user_method_named_like_a_primitive_is_refused() {
    let src = format!(
        "pub struct Counter {{ c: core::cell::Cell<isize> }}\n\
         impl Counter {{ pub fn wrapping_add(&self, _k: isize) -> isize {{ let v = self.c.get(); self.c.set(v + 1); v }} }}\n\
         {G_ISIZE}\
         pub unsafe fn caller(base: *const u8, k: isize, counter: &Counter) -> u32 {{ g(counter.wrapping_add(1), 1, base.offset(k)) }}\n"
    );
    no_callee_bound_at_the_call(&src);
}

/// R3-9: `gate(stop)` may exit before the read; `*p.add(9)` is no `must:10`.
#[test]
fn r112_r3_9_an_access_after_a_call_that_can_exit_is_refused() {
    let src = "pub unsafe fn gate(stop: bool) { if stop { std::process::exit(0); } }\n\
        pub unsafe fn f(p: *const u8, stop: bool) -> u8 { gate(stop); *p.add(9) }\n";
    assert_eq!(bound(src, "f", 0), None);
}

// ---- relay 112, the narrowed module's round 1 (Claude stand-in, 10-09) -----

/// The callee bound of pointer LOCAL `local` of `function`.
fn local_bound(src: &str, function: &str, local: &str) -> Option<String> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(&format!("{PRE}{src}"), |tcx| {
        let def = tcx
            .hir_body_owners()
            .find(|d| {
                matches!(tcx.def_kind(d.to_def_id()), rustc_hir::def::DefKind::Fn)
                    && tcx.item_name(d.to_def_id()).as_str() == function
            })
            .unwrap_or_else(|| panic!("{function} in the fixture"));
        struct Find(Option<rustc_hir::HirId>, String);
        impl<'v> rustc_hir::intravisit::Visitor<'v> for Find {
            fn visit_pat(&mut self, p: &'v rustc_hir::Pat<'v>) {
                if let rustc_hir::PatKind::Binding(_, id, ident, _) = p.kind
                    && ident.name.as_str() == self.1
                {
                    self.0 = Some(id);
                }
                rustc_hir::intravisit::walk_pat(self, p);
            }
        }
        let mut find = Find(None, local.to_owned());
        rustc_hir::intravisit::Visitor::visit_body(&mut find, tcx.hir_body_owned_by(def));
        let id = find.0.unwrap_or_else(|| panic!("{local} in {function}"));
        out = super::decision::callee_bound::of_local(tcx, def, id)
            .map(|b| b.receipt(&super::decision::callee_bound::parameter_names(tcx, def)));
    })
    .expect("fixture compiles");
    out
}

/// S1-M1a: `(n >>= 1, 0).1` halves the copied `n` between its evaluation and
/// the construction after it: length 5, the callee reads index 9.
#[test]
fn r112_s1_m1a_a_compound_shift_in_another_argument_is_refused() {
    let src = format!(
        "{G_ISIZE}\
         pub unsafe fn caller(base: *const u8, k: isize) -> u32 {{\n\
         let mut n: isize = 10; g(n, (n >>= 1, 0).1, base.offset(k)) }}\n"
    );
    assert_eq!(
        bound(&src, "g", 2).as_deref(),
        Some("len-callee-bound:may:n")
    );
    no_callee_bound_at_the_call(&src);
}

/// S1-M1b: a macro in another argument writes the copied `n`; its call text
/// shows no assignment.
#[test]
fn r112_s1_m1b_a_macro_in_another_argument_is_refused() {
    let src = format!(
        "macro_rules! halve {{ ($x:ident) => {{{{ $x >>= 1; 0 }}}} }}\n\
         {G_ISIZE}\
         pub unsafe fn caller(base: *const u8, k: isize) -> u32 {{\n\
         let mut n: isize = 10; g(n, halve!(n), base.offset(k)) }}\n"
    );
    no_callee_bound_at_the_call(&src);
}

/// S1-M1c: a user method named `add` in another argument writes the global
/// the length copies.
#[test]
fn r112_s1_m1c_a_user_method_named_add_writing_the_copied_global_is_refused() {
    let src = format!(
        "static mut N: isize = 10;\n\
         pub struct W;\n\
         impl W {{ pub fn add(&self, _k: isize) -> i32 {{ unsafe {{ N = 5; }} 1 }} }}\n\
         {G_ISIZE}\
         pub unsafe fn caller(base: *const u8, k: isize, w: &W) -> u32 {{ g(N, w.add(1), base.offset(k)) }}\n"
    );
    no_callee_bound_at_the_call(&src);
}

/// S1-M2a: `(*m.offset(i)).as_mut_ptr()` escapes row `i`'s address through an
/// autoref; it is no read of row `i`.
#[test]
fn r112_s1_m2a_an_autoref_of_the_pointee_is_refused() {
    let src = "extern \"C\" { fn memset(d: *mut core::ffi::c_void, c: i32, n: usize) -> *mut core::ffi::c_void; }\n\
        pub unsafe fn clear(m: *mut [i32; 4], n: i32) {\n\
        let mut i: i32 = 0;\n\
        while i < n { memset((*m.offset(i as isize)).as_mut_ptr() as *mut core::ffi::c_void, 0, 32); i += 1; } }\n";
    assert_eq!(bound(src, "clear", 0), None);
}

/// S1-M2b: the address of a field of the pointee escapes.
#[test]
fn r112_s1_m2b_an_address_through_a_projection_is_refused() {
    let src = "pub struct S { pub f: i32 }\n\
        extern \"C\" { fn keep(q: *mut i32); }\n\
        pub unsafe fn mark(p: *mut S, n: i32) {\n\
        let mut i: i32 = 0;\n\
        while i < n { keep(&mut (*p.offset(i as isize)).f); i += 1; } }\n";
    assert_eq!(bound(src, "mark", 0), None);
}

/// S1-M3: a row pointer bound anew on every iteration (row `i` of a
/// triangular table holds `i + 1` elements) is no allocation of `n`.
#[test]
fn r112_s1_m3_a_local_bound_inside_the_loop_is_refused() {
    let src = "pub unsafe fn tri(rows: *const *mut i32, n: i32) {\n\
        let mut i: i32 = 0;\n\
        while i < n { let mut row: *mut i32 = *rows.offset(i as isize); *row.offset(i as isize) = 1; i += 1; } }\n";
    assert_eq!(local_bound(src, "tri", "row"), None);
}

// ---- relay 112, the narrowed module's round 2 (Claude stand-in, 10-09) -----

/// S2-F1a: the limit written through a `&raw const` of it (defined under
/// Tree Borrows): the loop runs to 10 with an entry `n` of 1.
#[test]
fn r112_s2_f1a_a_limit_written_through_a_raw_const_address_is_refused() {
    let src = "static mut NP: *mut i32 = 0 as *mut i32;\n\
        pub unsafe fn grow() { if *NP < 10 { *NP = 10; } }\n\
        pub unsafe fn f(p: *mut i32, mut n: i32) {\n\
        NP = &raw const n as *mut i32;\n\
        let mut i: i32 = 0;\n\
        while i < n { grow(); *p.offset(i as isize) = 0; i += 1; } }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// S2-F1b: the counter written through a `&raw const` of it.
#[test]
fn r112_s2_f1b_a_counter_written_through_a_raw_const_address_is_refused() {
    let src = "static mut IP: *mut i32 = 0 as *mut i32;\n\
        pub unsafe fn jump() { *IP = 100; }\n\
        pub unsafe fn f(p: *mut i32, n: i32) {\n\
        let mut i: i32 = 0;\n\
        IP = &raw const i as *mut i32;\n\
        while i < n { jump(); *p.offset(i as isize) = 0; i += 1; } }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// S2-F1c: an overloaded auto-deref in another argument runs user code that
/// writes the copied `n` through a `&raw const` of it.
#[test]
fn r112_s2_f1c_an_overloaded_deref_in_another_argument_is_refused() {
    let src = format!(
        "static mut NP: *mut isize = 0 as *mut isize;\n\
         pub struct Inner {{ pub v: i32 }}\n\
         pub struct W(Inner);\n\
         impl core::ops::Deref for W {{ type Target = Inner; fn deref(&self) -> &Inner {{ unsafe {{ *NP = 5; }} &self.0 }} }}\n\
         {G_ISIZE}\
         pub unsafe fn caller(base: *const u8, k: isize, w: W) -> u32 {{\n\
         let n: isize = 10; NP = &raw const n as *mut isize; g(n, w.v, base.offset(k)) }}\n"
    );
    no_callee_bound_at_the_call(&src);
}

/// S2-F2: a `ref` binding of the pointee escapes its address; the program
/// later reads one element past the loop's last.
#[test]
fn r112_s2_f2_a_ref_binding_of_the_pointee_is_refused() {
    let src = "pub unsafe fn f(p: *const i32, n: i32) -> i32 {\n\
        let mut q: *const i32 = core::ptr::null();\n\
        let mut i: i32 = 0;\n\
        while i < n { let ref x = *p.offset(i as isize); q = x; i += 1; }\n\
        if q.is_null() { 0 } else { *q.offset(1) } }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// S2-F3: `let _ = *p.offset(i)` reads nothing; it is no access.
#[test]
fn r112_s2_f3_a_wildcard_let_is_no_access() {
    let src = "pub unsafe fn f(p: *const i32, n: i32) {\n\
        let mut i: i32 = 0;\n\
        while i < n { let _ = *p.offset(i as isize); i += 1; } }\n";
    assert_eq!(bound(src, "f", 0), None);
}

/// S2-F3b: `300` under `#[allow(overflowing_literals)]` is the `u8` 44.
#[test]
fn r112_s2_f3b_an_overflowing_literal_limit_is_refused() {
    let src = "#[allow(overflowing_literals)]\n\
        pub unsafe fn f(p: *const u8) -> u32 {\n\
        let mut s = 0u32; let mut i: u8 = 0;\n\
        while i < 300 { s += *p.offset(i as isize) as u32; i += 1; }\n\
        s }\n";
    assert_eq!(bound(src, "f", 0), None);
}
