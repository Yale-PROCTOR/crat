//! **Relay 107 — the adversarial review of `local/wave4-57` (Codex, 10-07).**
//! One fixture per finding, each the review's own counterexample. Each is RED
//! while the inference over-claims a length the input's accesses do not prove.

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

/// `<count>:<form>` the field count proves for `strukt.field`, or `None`.
fn proven(src: &str, strukt: &str, field: &str) -> Option<String> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(&format!("{PRE}{src}"), |tcx| {
        let adt = tcx
            .hir_crate_items(())
            .definitions()
            .find(|d| {
                matches!(tcx.def_kind(*d), rustc_hir::def::DefKind::Struct)
                    && tcx.item_name(d.to_def_id()).as_str() == strukt
            })
            .unwrap_or_else(|| panic!("{strukt} in the fixture"));
        out = super::decision::field_count::proven_count(
            tcx,
            adt.to_def_id(),
            rustc_span::Symbol::intern(field),
        )
        .map(|p| format!("{}:{}", p.count, p.form));
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

// ---- field_count.rs --------------------------------------------------------

const HT: &str = "pub struct Entry { pub key: *const i8, pub value: *mut core::ffi::c_void }\n\
pub struct Ht { pub entries: *mut Entry, pub capacity: usize, pub length: usize }\n";

/// Finding 3: the count rewritten after the allocation in the same block.
#[test]
fn r107_fc3_a_count_rewritten_after_its_allocation_refuses() {
    let src = format!(
        "{HT}pub unsafe fn create() -> *mut Ht {{\n\
        let t = malloc(core::mem::size_of::<Ht>()) as *mut Ht;\n\
        (*t).capacity = 1;\n\
        let ref mut f0 = (*t).entries;\n\
        *f0 = calloc((*t).capacity, core::mem::size_of::<Entry>()) as *mut Entry;\n\
        (*t).capacity = 8;\n\
        t }}\n"
    );
    assert_eq!(proven(&src, "Ht", "entries"), None);
}

/// Finding 4a: a `ref mut` alias of the field handed to a callee that writes it.
#[test]
fn r107_fc4a_an_escaped_field_alias_refuses() {
    let src = format!(
        "{HT}pub unsafe fn replace(out: &mut *mut Entry) {{ *out = malloc(core::mem::size_of::<Entry>()) as *mut Entry; }}\n\
        pub unsafe fn create() -> *mut Ht {{\n\
        let t = malloc(core::mem::size_of::<Ht>()) as *mut Ht;\n\
        (*t).capacity = 8;\n\
        let ref mut f0 = (*t).entries;\n\
        *f0 = calloc((*t).capacity, core::mem::size_of::<Entry>()) as *mut Entry;\n\
        t }}\n\
        pub unsafe fn shrink(t: *mut Ht) {{ let ref mut f1 = (*t).entries; replace(f1); }}\n"
    );
    assert_eq!(proven(&src, "Ht", "entries"), None);
}

/// Finding 4b: a partial `memcpy` over the struct's first field.
#[test]
fn r107_fc4b_a_partial_copy_over_the_field_refuses() {
    let src = format!(
        "{HT}pub unsafe fn create() -> *mut Ht {{\n\
        let t = malloc(core::mem::size_of::<Ht>()) as *mut Ht;\n\
        (*t).capacity = 8;\n\
        let ref mut f0 = (*t).entries;\n\
        *f0 = calloc((*t).capacity, core::mem::size_of::<Entry>()) as *mut Entry;\n\
        t }}\n\
        pub unsafe fn smash(t: *mut Ht, one: *mut Entry) {{\n\
        memcpy(t as *mut core::ffi::c_void, &one as *const *mut Entry as *const core::ffi::c_void, core::mem::size_of::<*mut Entry>()); }}\n"
    );
    assert_eq!(proven(&src, "Ht", "entries"), None);
}

const ANN: &str = "pub struct Ann { pub total: u32, pub weight: *mut f64, pub output: *mut f64 }\n";

/// Finding 5: an offset witness that runs only under a condition.
#[test]
fn r107_fc5_a_conditional_offset_witness_refuses() {
    let src = format!(
        "{ANN}pub unsafe fn init(n: u32, p: *mut f64, flag: i32) -> *mut Ann {{\n\
        let ret = malloc(core::mem::size_of::<Ann>()) as *mut Ann;\n\
        (*ret).total = n;\n\
        let ref mut f0 = (*ret).weight;\n\
        *f0 = p;\n\
        if flag != 0 {{ let ref mut f1 = (*ret).output; *f1 = ((*ret).weight).offset((*ret).total as isize); }}\n\
        ret }}\n"
    );
    assert_eq!(proven(&src, "Ann", "weight"), None);
}

/// Finding 6: a signed count proves no forward extent when negative; the
/// length must never wrap to a huge `usize`.
#[test]
fn r107_fc6_a_signed_count_never_renders_a_wrapped_length() {
    let src = "pub struct Sig { pub total: i32, pub weight: *mut f64, pub output: *mut f64 }\n\
        pub unsafe fn init(n: i32) -> *mut Sig {\n\
        let ret = malloc(core::mem::size_of::<Sig>() + 16) as *mut Sig;\n\
        (*ret).total = n;\n\
        let ref mut f0 = (*ret).weight;\n\
        *f0 = (ret as *mut u8).offset(core::mem::size_of::<Sig>() as isize) as *mut f64;\n\
        let ref mut f1 = (*ret).output;\n\
        *f1 = ((*ret).weight).offset((*ret).total as isize);\n\
        ret }\n\
        pub unsafe fn run(s: *const Sig) -> f64 {\n\
        let mut w: *const f64 = (*s).weight;\n\
        let mut a = 0.0; let mut i: i32 = 0;\n\
        while i < (*s).total { a += *w.offset(i as isize); i += 1; }\n\
        a }\n";
    let out = flat(&emitted(&format!("{PRE}{src}")));
    assert!(!out.contains("((*s).total) as usize)"), "{out}");
}

/// Finding 7: a field of bytes handed on through a cast to a wider pointee is
/// not `C` elements of that pointee.
#[test]
fn r107_fc7_a_cast_to_another_pointee_takes_no_field_count() {
    let src = "pub struct Buf { pub data: *mut u8, pub len: usize }\n\
        pub unsafe fn create(n: usize) -> *mut Buf {\n\
        let b = malloc(core::mem::size_of::<Buf>()) as *mut Buf;\n\
        (*b).len = n;\n\
        let ref mut f0 = (*b).data;\n\
        *f0 = calloc((*b).len, core::mem::size_of::<u8>()) as *mut u8;\n\
        b }\n\
        pub unsafe fn reader(w: *const u32, k: isize) -> u32 { if k > 0 { *w.offset(0) } else { *w.offset(1) } }\n\
        pub unsafe fn user(b: *mut Buf, k: isize) -> u32 { reader((*b).data as *const u32, k) }\n";
    let out = flat(&emitted(&format!("{PRE}{src}")));
    assert!(!out.contains("((*b).len) as usize"), "{out}");
}

/// Finding 8a: a base that calls a function is not read twice for its count.
#[test]
fn r107_fc8_a_calling_base_is_not_duplicated_into_the_length() {
    let src = format!(
        "{HT}pub static mut TABLE: *mut Ht = 0 as *mut Ht;\n\
        pub unsafe fn next_object() -> *mut Ht {{ TABLE }}\n\
        pub unsafe fn create() -> *mut Ht {{\n\
        let t = malloc(core::mem::size_of::<Ht>()) as *mut Ht;\n\
        (*t).capacity = 8;\n\
        let ref mut f0 = (*t).entries;\n\
        *f0 = calloc((*t).capacity, core::mem::size_of::<Entry>()) as *mut Entry;\n\
        t }}\n\
        unsafe fn walk(entries: *mut Entry, capacity: usize) -> usize {{\n\
        let mut i: usize = 0; let mut c = 0;\n\
        while i < capacity {{ if !(*entries.offset(i as isize)).key.is_null() {{ c += 1; }} i += 1; }}\n\
        c }}\n\
        pub unsafe fn user() -> usize {{ walk((*next_object()).entries, 8) }}\n"
    );
    let out = flat(&emitted(&format!("{PRE}{src}")));
    assert!(out.matches("next_object()").count() <= 2, "{out}");
    assert!(
        !out.contains("((*next_object()).capacity) as usize"),
        "{out}"
    );
}

// ---- round 2 (Codex, 10-07): three bypasses of the field-count fixes --------

const PAIR: &str = "#[repr(C)] pub struct S { pub p: *mut u8, pub n: usize }\n\
pub unsafe fn make(n: usize) -> *mut S {\n\
    let s = malloc(core::mem::size_of::<S>()) as *mut S;\n\
    (*s).n = n;\n\
    let ref mut f0 = (*s).p;\n\
    *f0 = calloc((*s).n, core::mem::size_of::<u8>()) as *mut u8;\n\
    s }\n";

/// Round 2, finding 1: a field address is not a whole object; a whole-size
/// copy from a field's address overwrites `n` without `p`.
#[test]
fn r107_r2a_a_copy_from_a_field_address_is_not_a_whole_copy() {
    let src = format!(
        "{PAIR}pub unsafe fn smash(dst: *mut S, src: *mut S) {{\n\
        memcpy(&(*dst).n as *const usize as *mut usize as *mut core::ffi::c_void, &(*src).n as *const usize as *const core::ffi::c_void, core::mem::size_of::<S>()); }}\n"
    );
    assert_eq!(proven(&src, "S", "p"), None);
}

/// Round 2, finding 2: zero is a literal, not a text prefix.
#[test]
fn r107_r2b_a_nonzero_memset_value_is_not_a_zeroing() {
    let src = format!(
        "{PAIR}extern \"C\" {{ fn memset(d: *mut core::ffi::c_void, c: i32, n: usize) -> *mut core::ffi::c_void; }}\n\
        pub unsafe fn fill(s: *mut S) {{ memset(s as *mut core::ffi::c_void, 0 as i32 + 1, core::mem::size_of::<S>()); }}\n"
    );
    assert_eq!(proven(&src, "S", "p"), None);
}

/// Round 2, finding 3: a witness in the right operand of `&&` runs only when
/// the left one holds.
#[test]
fn r107_r2c_a_short_circuit_witness_is_conditional() {
    let src = format!(
        "{ANN}pub unsafe fn init(n: u32, p: *mut f64, flag: bool) -> *mut Ann {{\n\
        let ret = malloc(core::mem::size_of::<Ann>()) as *mut Ann;\n\
        (*ret).total = n;\n\
        let ref mut f0 = (*ret).weight;\n\
        *f0 = p;\n\
        let _ = flag && {{ let ref mut f1 = (*ret).output; *f1 = ((*ret).weight).offset((*ret).total as isize); true }};\n\
        ret }}\n"
    );
    assert_eq!(proven(&src, "Ann", "weight"), None);
}

/// Round 3 (Codex, 10-07): a pointer to POINTERS to the struct is not a whole
/// object; a struct-sized copy out of an array of struct pointers installs any
/// `p` and `n`.
#[test]
fn r107_r3a_a_pointer_array_is_not_a_whole_object() {
    let src = format!(
        "{PAIR}pub unsafe fn smash(dst: *mut S, one: *mut S) {{\n\
        let slots = [one, 8usize as *mut S];\n\
        memcpy(dst as *mut core::ffi::c_void, slots.as_ptr() as *const core::ffi::c_void, core::mem::size_of::<S>()); }}\n"
    );
    assert_eq!(proven(&src, "S", "p"), None);
}
