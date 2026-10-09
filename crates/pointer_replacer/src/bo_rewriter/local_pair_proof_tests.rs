//! **R924-1 (USER; wave-5d 148) — the pending pair holds a local proof covers.**
//! A source handed to a raw formal beside a written raw sibling stays held
//! (R829-1 / R855-1) unless the pair is shown disjoint. Where the audit and the
//! certificates ran no proof, two local ones now answer: at a FOREIGN callee the
//! certificates' own root classes for the two arguments (a fresh allocation or a
//! stack object beside storage that existed at entry), and at a local callee
//! whose caller is an exported entry nothing calls, the scope's separate-object
//! certificate for two of its own formals. A parameter beside a parameter, and
//! an entry the program calls, stay held.

use super::decision::{Decision, DegradeReason};

/// Each subject's label, whether the settled table holds it beside a pair not
/// shown disjoint, and whether it is raw at all (the attested census world).
fn held(input: &str) -> Vec<(String, bool, bool)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decisions");
        table
            .entries
            .iter()
            .map(|(subject, decision)| {
                println!("DECISION {} {decision:?}", subject.label);
                (
                    subject.label.clone(),
                    matches!(decision, Decision::Degraded(d)
                        if matches!(d.reason, DegradeReason::PairNotShownDisjoint { .. })),
                    matches!(decision, Decision::Degraded(_)),
                )
            })
            .collect()
    })
    .expect("fixture compiles")
}

fn row<'a>(rows: &'a [(String, bool, bool)], label: &str) -> &'a (String, bool, bool) {
    rows.iter()
        .find(|(l, ..)| l == label)
        .unwrap_or_else(|| panic!("no subject {label}: {rows:?}"))
}

fn is_held(rows: &[(String, bool, bool)], label: &str) -> bool {
    row(rows, label).1
}

fn is_raw(rows: &[(String, bool, bool)], label: &str) -> bool {
    row(rows, label).2
}

const FRESH: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn malloc(n: usize) -> *mut i8;
    fn strncpy(dst: *mut i8, src: *const i8, n: usize) -> *mut i8;
}
pub unsafe fn caller(p: *const i8) -> i8 {
    let mut dst = malloc(2);
    strncpy(dst, p, 2);
    *p.offset(1)
}
pub unsafe fn control(p: *const i8, q: *mut i8) -> i8 {
    strncpy(q, p, 2);
    *p.offset(1)
}
"#;

/// (1) A fresh allocation beside a parameter at a libc call: the block did
/// not exist when `p` was passed in, so the two are disjoint (distinct roots).
#[test]
fn r924_1_a_fresh_allocation_beside_a_parameter_at_a_libc_call_is_not_held() {
    let rows = held(FRESH);
    assert!(!is_held(&rows, "caller::p"), "{rows:?}");
}

/// Control: a parameter beside a parameter stays held.
#[test]
fn r924_1_control_two_parameters_at_a_libc_call_stay_held() {
    let rows = held(FRESH);
    assert!(is_held(&rows, "control::p"), "{rows:?}");
}

const STACK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" { fn strncpy(dst: *mut i8, src: *const i8, n: usize) -> *mut i8; }
pub unsafe fn caller(p: *const i8) -> i8 {
    let mut dst = [0i8; 2];
    strncpy(dst.as_mut_ptr(), p, 2);
    *p.offset(1)
}
"#;

/// (1) A stack array beside a parameter at a libc call (stack object versus
/// storage that existed at entry).
#[test]
fn r924_1_a_stack_array_beside_a_parameter_at_a_libc_call_is_not_held() {
    let rows = held(STACK);
    assert!(!is_held(&rows, "caller::p"), "{rows:?}");
}

const ENTRY: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
unsafe fn write2(a: *mut i32, b: *const i32) -> i32 {
    *a = *b;
    (b as usize) as i32
}
#[no_mangle]
pub unsafe extern "C" fn entry(x: *mut i32, y: *const i32) -> i32 {
    write2(x, y);
    *y
}
pub unsafe fn other(z: *mut i32) -> i32 {
    write2(z, z)
}
"#;

/// (2) Two of its own formals handed on by an exported entry nothing in the
/// program calls: separate outside objects (R816 / R819).
#[test]
fn r924_1_two_formals_of_an_entry_nothing_calls_are_not_held() {
    let rows = held(ENTRY);
    assert!(!is_held(&rows, "entry::y"), "{rows:?}");
}

/// Control: the same entry called inside the program with one pointer twice
/// is not certified; `y` stays raw (the pair pass's raw view takes it first).
#[test]
fn r924_1_control_an_entry_the_program_calls_stays_raw() {
    let input = format!("{ENTRY}pub unsafe fn calls_entry(q: *mut i32) -> i32 {{ entry(q, q) }}\n");
    let rows = held(&input);
    assert!(is_raw(&rows, "entry::y"), "{rows:?}");
}

const STATIC_VALUE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
extern "C" { fn malloc(n: usize) -> *mut u8; }
static mut G: *mut u8 = 0 as *mut u8;
unsafe fn cp2(d: *mut u8, s: *const u8) { *d = *s; }
unsafe fn cp(d: *mut u8, s: *const u8) { *d.offset(-1) = *s.offset(1); }
pub unsafe fn both() -> u8 { let mut tmp = malloc(64); G = tmp; cp2(G, tmp); *tmp }
pub unsafe fn raw_side() -> u8 { let mut tmp = malloc(64); G = tmp; cp(G.offset(32), tmp); *tmp }
"#;

/// wave-5d 148b (the review's HIGH-1): a pointer static's VALUE is not the
/// static's storage. `G == tmp`, so `cp2(G, tmp)` must not deliver both sides.
#[test]
fn r148b_a_pointer_statics_value_is_not_its_storage() {
    let rows = held(STATIC_VALUE);
    // R930-1: both sides raw (R833-1's peer arm holds the primary beside the
    // pair's raw view; on the composed 57 head).
    assert!(
        is_raw(&rows, "cp2::d") && is_raw(&rows, "cp2::s"),
        "{rows:?}"
    );
    // The raw-side shape: `d` writes inside the view `s` would take.
    assert!(is_raw(&rows, "cp::s"), "{rows:?}");
}

const INTEGER_CAST: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
unsafe fn cp2(d: *mut u8, s: *const u8) { *d = *s; }
pub unsafe fn caller(buf: *mut u8, n: usize) -> u8 { cp2(n as *mut u8, buf); *buf }
"#;

/// wave-5d 148b (the review's HIGH-2): an integer cast to a pointer is not a
/// stack object (`n` may be `(uintptr_t)buf` in C).
#[test]
fn r148b_an_integer_cast_to_a_pointer_is_not_a_stack_object() {
    let rows = held(INTEGER_CAST);
    // R930-1: both sides raw (the stand-in review's LOW).
    assert!(
        is_raw(&rows, "cp2::s") && is_raw(&rows, "cp2::d"),
        "{rows:?}"
    );
}

/// R931-1 (USER; wave-5d 149): `f` hands two of its own formals to `write2`,
/// whose pair another caller refutes (`write2(z, z)`), so (e) on the callee
/// fails; every in-program call of `f` passes two distinct stack objects, so
/// the CALLER's pair is disjoint at `f`'s call.
const CALLER_PAIR: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
unsafe fn write2(a: *mut i32, b: *const i32) -> i32 {
    *a = *b;
    (b as usize) as i32
}
unsafe fn f(x: *mut i32, y: *const i32) -> i32 {
    let _k = x as usize;
    write2(x, y);
    *y
}
pub unsafe fn other(z: *mut i32) -> i32 {
    write2(z, z)
}
pub unsafe fn top() -> i32 {
    let mut a: i32 = 1;
    let mut b: i32 = 2;
    f(&mut a, &b)
}
"#;

#[test]
fn r931_1_a_callers_formal_pair_every_call_separates_is_not_held() {
    let rows = held(CALLER_PAIR);
    assert!(!is_held(&rows, "f::y"), "{rows:?}");
}

/// Control: one object at both of `f`'s positions refutes the pair.
#[test]
fn r931_1_control_a_call_passing_one_object_twice_refutes_the_pair() {
    let input = CALLER_PAIR.replace(
        "    f(&mut a, &b)\n",
        "    let p = &mut a as *mut i32;\n    f(p, p)\n",
    );
    let rows = held(&input);
    assert!(is_raw(&rows, "f::y"), "{rows:?}");
}

/// Control: `f`'s address is taken, so callers the records do not show may
/// reach it; nothing is certified from the direct calls.
#[test]
fn r931_1_control_an_address_taken_caller_is_not_certified() {
    let input = format!(
        "{CALLER_PAIR}pub static F: unsafe fn(*mut i32, *const i32) -> i32 = f;\n\
         pub unsafe fn through(q: *mut i32) -> i32 {{ F(q, q) }}\n"
    );
    let rows = held(&input);
    assert!(is_raw(&rows, "f::y"), "{rows:?}");
}

/// R931-1 at the certificate itself: the pair `f → write2(x, y)` of the
/// caller's own formals.
fn caller_pair_verdict(
    src: &str,
) -> Result<
    super::decision::pair_disjointness::CertificateKind,
    super::decision::pair_disjointness::Unproved,
> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = super::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        out = Some(index.certify_recorded(function("f"), function("write2"), 0, 1));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

#[test]
fn r931_1_the_certificate_proves_a_callers_formal_pair_every_call_separates() {
    assert_eq!(
        caller_pair_verdict(CALLER_PAIR),
        Ok(super::decision::pair_disjointness::CertificateKind::CallerParameterPair)
    );
}

#[test]
fn r931_1_control_the_certificate_refuses_one_object_twice() {
    let input = CALLER_PAIR.replace(
        "    f(&mut a, &b)\n",
        "    let p = &mut a as *mut i32;\n    f(p, p)\n",
    );
    assert!(caller_pair_verdict(&input).is_err());
}

#[test]
fn r931_1_control_the_certificate_refuses_an_address_taken_caller() {
    let input = format!("{CALLER_PAIR}pub static F: unsafe fn(*mut i32, *const i32) -> i32 = f;\n");
    assert!(caller_pair_verdict(&input).is_err());
}

/// wave-5d 149g (the stand-in review's HIGH-1): R930-1's "may point anywhere"
/// read only the argument's own text. A pointer static's value reaching the
/// call through a local, an integer cast held in a local, and a pointer field
/// of a static struct may address any object too.
fn anywhere_shape(body: &str) -> String {
    format!(
        r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
extern "C" {{ fn malloc(n: usize) -> *mut u8; }}
static mut G: *mut u8 = 0 as *mut u8;
#[repr(C)]
pub struct C {{ buf: *mut u8 }}
static mut S: C = C {{ buf: 0 as *mut u8 }};
unsafe fn cp(d: *mut u8, s: *const u8) {{ *d.offset(-1) = *s.offset(1); }}
unsafe fn cp2(d: *mut u8, s: *const u8) {{ *d = *s; }}
{body}
"#
    )
}

#[test]
fn r149g_a_statics_value_through_a_local_may_point_anywhere() {
    let rows = held(&anywhere_shape(
        "pub unsafe fn a() -> u8 { let mut tmp = malloc(64); G = tmp; let mut p = G; cp(p.offset(32), tmp); *tmp }",
    ));
    assert!(is_raw(&rows, "cp::s"), "{rows:?}");
}

#[test]
fn r149g_an_integer_cast_held_in_a_local_may_point_anywhere() {
    let rows = held(&anywhere_shape(
        "pub unsafe fn b(buf: *mut u8, n: usize) -> u8 { let q = n as *mut u8; cp2(q, buf); *buf }",
    ));
    assert!(is_raw(&rows, "cp2::s"), "{rows:?}");
}

#[test]
fn r149g_a_pointer_field_of_a_static_may_point_anywhere() {
    let rows = held(&anywhere_shape(
        "pub unsafe fn c() -> u8 { let mut tmp = malloc(64); S.buf = tmp; cp(S.buf.offset(32), tmp); *tmp }",
    ));
    assert!(is_raw(&rows, "cp::s"), "{rows:?}");
}

/// The certificate's verdict for `caller → callee(l, r)`.
fn verdict_at(
    src: &str,
    caller: &'static str,
    callee: &'static str,
    l: usize,
    r: usize,
) -> Result<
    super::decision::pair_disjointness::CertificateKind,
    super::decision::pair_disjointness::Unproved,
> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = super::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        out = Some(index.certify_recorded(function(caller), function(callee), l, r));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

const STATIC_VS_FORMAL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
static mut G: [u8; 4] = [0; 4];
unsafe fn cp2(d: *mut u8, s: *const u8) { *d = *s; }
unsafe fn f(p: *mut u8) -> u8 { cp2(p, G.as_ptr()); *p }
pub unsafe fn top() -> u8 { let mut x = 0u8; f(&mut x) }
"#;

/// Control: every call of `f` passes a stack object, never `G`.
#[test]
fn r149g_control_a_static_beside_a_formal_every_call_separates_is_certified() {
    assert!(verdict_at(STATIC_VS_FORMAL, "f", "cp2", 0, 1).is_ok());
}

/// wave-5d 149g (the stand-in review's HIGH-2): `f` reached through a fn
/// pointer may be handed `G` itself; the static-vs-formal chain (R483-3 (f))
/// certifies nothing about an address-taken function, as (e) does not.
#[test]
fn r149g_an_address_taken_function_is_not_certified_static_vs_formal() {
    let input = format!(
        "{STATIC_VS_FORMAL}pub static FP: unsafe fn(*mut u8) -> u8 = f;\n\
         pub unsafe fn through() -> u8 {{ FP(G.as_mut_ptr()) }}\n"
    );
    assert!(verdict_at(&input, "f", "cp2", 0, 1).is_err());
}

/// wave-5d 149g (the stand-in review's MED-2): a call inside a closure is a
/// caller the records do not show.
#[test]
fn r149g_a_call_inside_a_closure_refuses_the_certificate() {
    let input = format!(
        "{CALLER_PAIR}pub unsafe fn via_closure(q: *mut i32) -> i32 {{\n\
         let g = |r: *mut i32| unsafe {{ f(r, r) }};\n    g(q)\n}}\n"
    );
    assert!(caller_pair_verdict(&input).is_err());
}

/// wave-5d 149g (the stand-in review's MED-2): a call through an `extern "C"`
/// redeclaration of an exported local function is an in-program call the
/// records do not show; the waiver covers the embedder's calls only.
#[test]
fn r149g_a_call_through_an_extern_redeclaration_refuses_the_certificate() {
    let input = CALLER_PAIR.replace(
        "unsafe fn f(",
        "#[no_mangle]\npub unsafe extern \"C\" fn f(",
    ) + "pub mod other {\n    extern \"C\" { pub fn f(x: *mut i32, y: *const i32) -> i32; }\n\
         pub unsafe fn g(q: *mut i32) -> i32 { f(q, q) }\n}\n";
    assert!(caller_pair_verdict(&input).is_err());
}

/// wave-5d 149g (the stand-in review's MED-1): a reference binding is not the
/// object it borrows; `&mut *r` with `r = &mut *buf` is inside `buf`.
#[test]
fn r149g_a_reference_binding_is_not_a_stack_object() {
    let input = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
unsafe fn cp2(d: *mut u8, s: *const u8) { *d = *s; }
pub unsafe fn m(buf: *mut u8) -> u8 { let r: &mut u8 = &mut *buf; cp2(&mut *r, buf); *buf }
"#;
    assert!(verdict_at(input, "m", "cp2", 0, 1).is_err());
}

/// wave-5d 149h (the round-2 review's MED): a redeclaration under another
/// name (`#[link_name]`) is the same symbol, so the same hidden caller.
#[test]
fn r149h_a_renamed_extern_redeclaration_refuses_the_certificate() {
    let input = CALLER_PAIR.replace(
        "unsafe fn f(",
        "#[no_mangle]\npub unsafe extern \"C\" fn f(",
    ) + "pub mod other {\n    extern \"C\" { #[link_name = \"f\"] pub fn f_ext(x: *mut i32, y: *const i32) -> i32; }\n\
         pub unsafe fn g(q: *mut i32) -> i32 { f_ext(q, q) }\n}\n";
    assert!(caller_pair_verdict(&input).is_err());
}
