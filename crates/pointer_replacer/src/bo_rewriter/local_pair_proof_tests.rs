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
// R939-1: the store happens in another function, so the caller's text shows
// no relation and P11 is literal (the same-function store is r939_1's).
unsafe fn set_g(t: *mut u8) { G = t; }
pub unsafe fn both() -> u8 { let mut tmp = malloc(64); set_g(tmp); cp2(G, tmp); *tmp }
pub unsafe fn raw_side() -> u8 { let mut tmp = malloc(64); set_g(tmp); cp(G.offset(32), tmp); *tmp }
"#;

/// wave-5d 148b: a pointer static's VALUE is not the static's storage, so no
/// structural certificate reads `G` as a root. **R936-1 (P11, the USER with
/// the advisor)** puts aliasing through a global outside the claim: the pair is
/// cleared by the premise arm, receipted, and nothing is held for it (R930-1's
/// hold is withdrawn; `G = tmp` makes this fixture an input outside the claim).
#[test]
fn r148b_a_pointer_statics_value_is_not_its_storage() {
    let rows = held(STATIC_VALUE);
    assert!(
        !is_held(&rows, "cp2::d") && !is_held(&rows, "cp2::s") && !is_held(&rows, "cp::s"),
        "{rows:?}"
    );
    assert_eq!(
        verdict_at(STATIC_VALUE, "both", "cp2", 0, 1),
        Ok(
            super::decision::pair_disjointness::CertificateKind::GlobalOrIntegerPremise(
                super::decision::global_or_integer::ProvenanceKind::GlobalValue
            )
        )
    );
}

const INTEGER_CAST: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
unsafe fn cp2(d: *mut u8, s: *const u8) { *d = *s; }
pub unsafe fn caller(buf: *mut u8, n: usize) -> u8 { cp2(n as *mut u8, buf); *buf }
"#;

/// wave-5d 148b: an integer cast to a pointer is not a stack object, so no
/// structural certificate reads it as one. **R936-1 (P11)**: aliasing through
/// an integer is outside the claim; the premise arm clears the pair, receipted.
#[test]
fn r148b_an_integer_cast_to_a_pointer_is_not_a_stack_object() {
    let rows = held(INTEGER_CAST);
    assert!(
        !is_held(&rows, "cp2::s") && !is_held(&rows, "cp2::d"),
        "{rows:?}"
    );
    assert_eq!(
        verdict_at(INTEGER_CAST, "caller", "cp2", 0, 1),
        Ok(
            super::decision::pair_disjointness::CertificateKind::GlobalOrIntegerPremise(
                super::decision::global_or_integer::ProvenanceKind::Integer
            )
        )
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
// R939-1: stores in other functions, so a caller's text shows no relation.
unsafe fn set_g(t: *mut u8) {{ G = t; }}
unsafe fn set_s(t: *mut u8) {{ S.buf = t; }}
{body}
"#
    )
}

/// R936-1 (P11): the premise arm clears it, receipted; nothing is held.
#[test]
fn r149g_a_statics_value_through_a_local_may_point_anywhere() {
    let source = anywhere_shape(
        "pub unsafe fn a() -> u8 { let mut tmp = malloc(64); set_g(tmp); let mut p = G; cp(p.offset(32), tmp); *tmp }",
    );
    let rows = held(&source);
    assert!(!is_held(&rows, "cp::s"), "{rows:?}");
    assert_eq!(
        verdict_at(&source, "a", "cp", 0, 1),
        Ok(
            super::decision::pair_disjointness::CertificateKind::GlobalOrIntegerPremise(
                super::decision::global_or_integer::ProvenanceKind::GlobalValue
            )
        )
    );
}

/// R936-1 (P11): the premise arm clears it, receipted; nothing is held.
#[test]
fn r149g_an_integer_cast_held_in_a_local_may_point_anywhere() {
    let source = anywhere_shape(
        "pub unsafe fn b(buf: *mut u8, n: usize) -> u8 { let q = n as *mut u8; cp2(q, buf); *buf }",
    );
    let rows = held(&source);
    assert!(!is_held(&rows, "cp2::s"), "{rows:?}");
    assert_eq!(
        verdict_at(&source, "b", "cp2", 0, 1),
        Ok(
            super::decision::pair_disjointness::CertificateKind::GlobalOrIntegerPremise(
                super::decision::global_or_integer::ProvenanceKind::Integer
            )
        )
    );
}

/// R936-1 (P11): the premise arm clears it, receipted; nothing is held.
#[test]
fn r149g_a_pointer_field_of_a_static_may_point_anywhere() {
    let source = anywhere_shape(
        "pub unsafe fn c() -> u8 { let mut tmp = malloc(64); set_s(tmp); cp(S.buf.offset(32), tmp); *tmp }",
    );
    let rows = held(&source);
    assert!(!is_held(&rows, "cp::s"), "{rows:?}");
    assert_eq!(
        verdict_at(&source, "c", "cp", 0, 1),
        Ok(
            super::decision::pair_disjointness::CertificateKind::GlobalOrIntegerPremise(
                super::decision::global_or_integer::ProvenanceKind::GlobalValue
            )
        )
    );
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
    // R936-1 (P11): no structural certificate (the address-taken guard
    // holds); `G.as_ptr()` is a pointer to a static's storage, so the premise
    // arm clears the pair, receipted.
    assert_eq!(
        verdict_at(&input, "f", "cp2", 0, 1),
        Ok(
            super::decision::pair_disjointness::CertificateKind::GlobalOrIntegerPremise(
                super::decision::global_or_integer::ProvenanceKind::GlobalStorage
            )
        )
    );
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

/// wave-6a 157b's three functions, the write through `dst` itself.
const PLAIN_WRITE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
pub struct Holder { data: *mut i32 }
pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }
pub unsafe fn caller(holder: *const Holder, src: *const i32) { update((*holder).data, src); }
pub unsafe fn outer(holder: *const Holder, v: *const i32) -> i32 { let x = *v; caller(holder, v); x + *v }
#[no_mangle]
pub unsafe extern "C" fn entry() -> i32 {
    let mut value = 1;
    let p: *mut i32 = &mut value;
    let holder = Holder { data: p };
    outer(&holder, p)
}
"#;

/// wave-6a 157c §2: the very same write, through a pointer the callee rebuilt
/// from an integer. Foster's mutability does not follow the integer, so
/// `dst` reads as never written.
fn integer_round_trip() -> String {
    PLAIN_WRITE.replace(
        "*dst = *src + 1;",
        "let d = dst as usize as *mut i32; *d = *src + 1;",
    )
}

/// wave-6a 157c §2: the write through an integer round trip of the sibling
/// formal. **R936-1 (P11)**: aliasing through an integer is outside the claim,
/// so the round trip is not chased (relay 197 drops R934-1 (iii)); the pair is
/// not held and the three are delivered. The plain write (no integer) stays
/// held, as R833-1 asks.
#[test]
fn r157c_a_write_through_an_integer_round_trip_is_outside_the_claim() {
    let plain = held(PLAIN_WRITE);
    let round = held(&integer_round_trip());
    let watched = ["update::src", "caller::src", "outer::v"];
    for label in watched {
        assert!(is_raw(&plain, label), "{label}: {plain:?}");
        assert!(!is_raw(&round, label), "{label}: {round:?}");
    }
}

/// wave-5d 149f (soundness): the same pair with `dst` model-raw through a
/// retyping cast, the write Foster sees. One argument is a loaded pointer
/// (`(*holder).data`), so the pair relation is unknown; no PAIR row exists for
/// a formal raw from the outset. What the plain write keeps raw stays raw.
#[test]
fn r149f_a_reference_beside_a_model_raw_written_formal_is_held() {
    let plain = held(PLAIN_WRITE);
    let retyped = held(&PLAIN_WRITE.replace(
        "*dst = *src + 1;",
        "*(dst as *mut u32) = (*src + 1) as u32;",
    ));
    for label in ["update::src", "caller::src", "outer::v"] {
        assert!(
            !is_raw(&plain, label) || is_raw(&retyped, label),
            "{label}: raw beside the plain write, delivered beside the retyped one: {retyped:?}"
        );
    }
}

/// wave-5d 149h (the round-2 review's HIGH-1 residual): a list of shapes that
/// may point anywhere is never complete. Each of these reaches `cp` beside
/// `tmp` (the same block, `G = tmp`) through a shape the list does not name,
/// and the relation answers unknown.
fn residual_source(body: &str) -> String {
    anywhere_shape(&format!(
        "unsafe fn get_g() -> *mut u8 {{ G }}\nunsafe fn ld(o: *mut *mut u8) {{ *o = G; }}\n{body}"
    ))
}

fn residual(body: &str) -> Vec<(String, bool, bool)> {
    held(&residual_source(body))
}

/// R936-1 (P11, relay 197 item 2): a global's value reaches the call, so the
/// premise arm clears the pair, receipted; nothing is held.
#[test]
fn r149h_a_getter_of_a_statics_value_is_a_receipted_premise() {
    let source = residual_source(
        "pub unsafe fn a() -> u8 { let mut tmp = malloc(64); set_g(tmp); cp(get_g().offset(32), tmp); *tmp }",
    );
    let rows = held(&source);
    assert!(!is_held(&rows, "cp::s"), "{rows:?}");
    assert_eq!(
        verdict_at(&source, "a", "cp", 0, 1),
        Ok(
            super::decision::pair_disjointness::CertificateKind::GlobalOrIntegerPremise(
                super::decision::global_or_integer::ProvenanceKind::GlobalValue
            )
        )
    );
}

/// R936-1 (P11): a conditional is a premise only when EVERY branch's
/// provenance passes through a global or an integer; here the `else` branch
/// (`buf`, an entry formal) does not, so no premise and the pair stays held
/// (the conservative side; relay 197 item 2 asked for a receipt, named in 150).
#[test]
fn r149h_a_conditional_over_a_statics_value_is_held() {
    let rows = residual(
        "pub unsafe fn a(c: bool, buf: *mut u8) -> u8 { let mut tmp = malloc(64); G = tmp; cp((if c { G } else { buf }).offset(32), tmp); *tmp }",
    );
    assert!(is_raw(&rows, "cp::s"), "{rows:?}");
}

/// R936-1 (P11): what `ld` stores through `&mut p` is not in the caller's text
/// (an address-taken local is no premise), so the pair stays held (the
/// conservative side; named in 150).
#[test]
fn r149h_an_out_parameter_loaded_with_a_statics_value_is_held() {
    let rows = residual(
        "pub unsafe fn a() -> u8 { let mut tmp = malloc(64); G = tmp; let mut p = 0 as *mut u8; ld(&mut p); cp(p.offset(32), tmp); *tmp }",
    );
    assert!(is_raw(&rows, "cp::s"), "{rows:?}");
}

/// R936-1 (P11): a local aggregate's slot is not followed (its stores are not
/// read), so the pair stays held (the conservative side; named in 150).
#[test]
fn r149h_a_local_aggregate_slot_holding_a_statics_value_is_held() {
    let rows = residual(
        "pub unsafe fn a() -> u8 { let mut tmp = malloc(64); G = tmp; let mut c: C = core::mem::zeroed(); c.buf = G; cp(c.buf.offset(32), tmp); *tmp }",
    );
    assert!(is_raw(&rows, "cp::s"), "{rows:?}");
}

/// R936-1 (P11, relay 197 item 2): a global's value reaches the call, so the
/// premise arm clears the pair, receipted; nothing is held.
#[test]
fn r149h_a_pointer_to_a_static_struct_is_a_receipted_premise() {
    let source = residual_source(
        "pub unsafe fn a() -> u8 { let mut tmp = malloc(64); set_s(tmp); let s: *const C = &S; cp((*s).buf.offset(32), tmp); *tmp }",
    );
    let rows = held(&source);
    assert!(!is_held(&rows, "cp::s"), "{rows:?}");
    assert_eq!(
        verdict_at(&source, "a", "cp", 0, 1),
        Ok(
            super::decision::pair_disjointness::CertificateKind::GlobalOrIntegerPremise(
                super::decision::global_or_integer::ProvenanceKind::GlobalValue
            )
        )
    );
}

/// Control: a fresh block beside a stack array at the same call is certified
/// (distinct roots), so nothing is held.
#[test]
fn r149h_control_two_distinct_objects_are_not_held() {
    let rows = residual(
        "pub unsafe fn a() -> u8 { let mut tmp = malloc(64); let mut arr = [0u8; 64]; cp(arr.as_mut_ptr().offset(32), tmp); *tmp }",
    );
    assert!(!is_held(&rows, "cp::s"), "{rows:?}");
}

/// wave-5d 150 (the round-3 review's H1): `(*CTX).data` is a pointer loaded
/// from a heap or stack object that a global's VALUE designates; it was never
/// stored in or read from a static, so it is not P11 (R936-1) but 149f's core
/// (relay 197 item 3): the reference beside the written raw formal is held.
const LOADED_THROUGH_A_GLOBAL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
pub struct Holder { pub data: *mut i32 }
pub static mut CTX: *mut Holder = 0 as *mut Holder;
pub unsafe fn update(dst: *mut i32, src: *const i32) { *(dst as *mut u32) = (*src + 1) as u32; }
pub unsafe fn caller(src: *mut i32) { update((*CTX).data, src); }
#[no_mangle]
pub unsafe extern "C" fn entry() -> i32 {
    let mut v = 1;
    let p: *mut i32 = &mut v;
    let mut h = Holder { data: p };
    CTX = &mut h;
    caller(p);
    v
}
"#;

#[test]
fn r150_a_pointer_loaded_from_an_object_a_global_designates_is_not_p11() {
    let rows = held(LOADED_THROUGH_A_GLOBAL);
    assert!(is_raw(&rows, "update::src"), "{rows:?}");
    assert!(verdict_at(LOADED_THROUGH_A_GLOBAL, "caller", "update", 0, 1).is_err());
}

/// wave-5d 150 (the round-3 review's M2): one global's value beside its own
/// storage (`ST.pos` may point into `ST.buf`) is one global at both positions:
/// no premise.
#[test]
fn r150_a_globals_value_beside_its_own_storage_is_no_premise() {
    let input = r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
pub struct St { pub buf: [u8; 16], pub pos: *mut u8 }
pub static mut ST: St = St { buf: [0; 16], pos: 0 as *mut u8 };
unsafe fn cp2(d: *mut u8, s: *const u8) { *d = *s; }
pub unsafe fn shift() { cp2(ST.pos, ST.buf.as_ptr()); }
"#;
    assert!(verdict_at(input, "shift", "cp2", 0, 1).is_err());
}

/// wave-5d 150d (the round-4 review's MED-3): two premise clears at two calls
/// of one caller to one callee are two rows of the P11 table, each at its own
/// call.
#[test]
fn r150d_two_premise_calls_are_two_rows() {
    let input = r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
pub static mut G1: *mut u8 = 0 as *mut u8;
pub static mut G2: *mut u8 = 0 as *mut u8;
unsafe fn cp2(d: *mut u8, s: *const u8) { *d = *s; }
pub unsafe fn c(q: *mut u8) {
    cp2(G1, q);
    cp2(G2, q);
}
"#;
    let table = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decisions");
        let certificates = ctx
            .a5_site_proofs
            .pair_certificates()
            .expect("certificates");
        // What the rules themselves asked (the census's table), before the
        // helper asks at every recorded call (round-5 MED-A).
        let asked = certificates.premise_receipts_tsv(tcx);
        let _ = certificates.certify_recorded_all(tcx, "c", "cp2", 0, 1);
        (asked, certificates.premise_receipts_tsv(tcx))
    })
    .expect("fixture compiles");
    let (asked, table) = table;
    // The census's own table already has both rows: the rules ask at each call.
    assert_eq!(asked, table, "the rules asked at both calls");
    let rows: Vec<&str> = table.lines().skip(1).collect();
    assert_eq!(rows.len(), 2, "{table}");
    assert_ne!(
        rows[0].split('\t').nth(2),
        rows[1].split('\t').nth(2),
        "each row names its own call: {table}"
    );
}

/// wave-5d 150e (the round-5 review's MED-B): a containment the text shows
/// (`br` inside `*s`, through an integer round trip of `s`) is held though a
/// premise clears the pair: the premise answers an unresolved pair only.
#[test]
#[ignore = "the frozen analysis panics on this input (rustc_middle mir/statement.rs:185 via analyses::borrow_ownership::borrow_engine::invalidates::route_compose, on `&mut (*r).x` with `r` made from an integer); kept as the reproduction for the analysis lane; wave-5d report 150e"]
fn r150e_a_premise_never_answers_a_shown_containment() {
    let input = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
pub struct S { pub x: i32, pub y: i32 }
unsafe fn upd(a: *mut S, b: *mut i32) { (*a).y = 1; *b = 2; }
pub unsafe fn c(s: *mut S) {
    let t = s as usize;
    let r = t as *mut S;
    let br = &mut (*r).x as *mut i32;
    upd(s, br);
}
"#;
    let rows = held(input);
    assert!(
        is_raw(&rows, "upd::a") && is_raw(&rows, "upd::b"),
        "{rows:?}"
    );
}

/// R939-1 (the seat on 150d's MED-2): P11 covers unknown provenance only. Where
/// the caller's own text relates the two arguments (`G = p; upd(G, p)`), the
/// premise is not asked and the pair is held as any shown overlap is.
const SHOWN_THROUGH_A_GLOBAL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
pub static mut G: *mut i32 = 0 as *mut i32;
unsafe fn upd(a: *mut i32, b: *mut i32) { *a += *b; }
pub unsafe fn c(p: *mut i32) {
    G = p;
    upd(G, p);
}
"#;

#[test]
fn r939_1_a_relation_the_callers_text_shows_refuses_the_premise() {
    assert_eq!(
        verdict_at(SHOWN_THROUGH_A_GLOBAL, "c", "upd", 0, 1),
        Err(super::decision::pair_disjointness::Unproved::PremiseShownRelation)
    );
    let rows = held(SHOWN_THROUGH_A_GLOBAL);
    assert!(
        is_raw(&rows, "upd::a") && is_raw(&rows, "upd::b"),
        "{rows:?}"
    );
}

/// R939-1 at a foreign callee: `G = p; strncpy(G, p, 2)` (the pending hold's
/// local proof, `certify_call_arguments`).
#[test]
fn r939_1_a_shown_relation_at_a_foreign_callee_keeps_the_hold() {
    let input = r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
extern "C" {
    fn strncpy(dst: *mut i8, src: *const i8, n: usize) -> *mut i8;
}
pub static mut G: *mut i8 = 0 as *mut i8;
pub unsafe fn c(p: *mut i8) -> i8 {
    G = p;
    strncpy(G, p, 2);
    *p.offset(1)
}
"#;
    let rows = held(input);
    assert!(is_held(&rows, "c::p"), "{rows:?}");
}

/// Control (R939-1): with no relation in the caller's text the premise stays
/// literal.
#[test]
fn r939_1_control_an_unrelated_global_keeps_the_premise() {
    let input = SHOWN_THROUGH_A_GLOBAL.replace("    G = p;\n", "");
    assert!(verdict_at(&input, "c", "upd", 0, 1).is_ok());
}

/// The round-6 review's MED-1 / MED-2 / MED-3 (wave-5d 150h): relations the
/// caller's text shows that the first R939-1 walk did not reach.
fn refusal(src: &str, caller: &'static str, callee: &'static str) -> bool {
    verdict_at(src, caller, callee, 0, 1)
        == Err(super::decision::pair_disjointness::Unproved::PremiseShownRelation)
}

const R939_SHAPES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
pub static mut G: *mut i32 = 0 as *mut i32;
#[repr(C)]
pub struct C { pub buf: *mut i32, pub n: usize }
pub static mut S: C = C { buf: 0 as *mut i32, n: 0 };
unsafe fn upd(a: *mut i32, b: *mut i32) { *a += *b; }
unsafe fn get_g() -> *mut i32 { G }
pub unsafe fn getter(p: *mut i32) { G = p; upd(get_g(), p); }
pub unsafe fn through_a_pointer(p: *mut i32) { let s: *mut C = &mut S; (*s).buf = p; upd((*s).buf, p); }
pub unsafe fn aggregate(p: *mut i32) { let mut c = C { buf: 0 as *mut i32, n: 0 }; c.n = p as usize; upd(c.n as *mut i32, p); }
"#;

#[test]
fn r150h_the_getters_static_is_where_the_refusal_starts() {
    assert!(refusal(R939_SHAPES, "getter", "upd"));
}

#[test]
fn r150h_a_store_through_a_pointer_to_the_static_refuses() {
    assert!(refusal(R939_SHAPES, "through_a_pointer", "upd"));
}

#[test]
fn r150h_a_store_into_a_local_aggregate_refuses() {
    assert!(refusal(R939_SHAPES, "aggregate", "upd"));
}
