//! **R864-3 (relay 299; era-5c 154 / 154a) — the retained-access check of record as
//! the joint fixpoint's fourth predicate.** The positive control (a self-reference
//! the check names is held on the settled table) and one witness per filter (era-5c
//! 154's fixtures). The filters' faults are measured by disabling each in a build of
//! its own (main 194), not by markers in the production code.

use rustc_hash::FxHashMap;

use super::{A5Mode, WholeProgramAttestation};

const ALLOW: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, unused_variables, non_snake_case, non_camel_case_types)]\n";

/// Every subject's settled decision, `label => Debug`.
fn decisions(source: &str) -> FxHashMap<String, String> {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decision table");
        table
            .entries
            .iter()
            .map(|(subject, decision)| (subject.label.clone(), format!("{decision:?}")))
            .collect()
    })
    .expect("fixture compiles")
}

fn held(decisions: &FxHashMap<String, String>, subject: &str) -> bool {
    decisions
        .get(subject)
        .unwrap_or_else(|| panic!("no {subject}: {decisions:#?}"))
        .contains("RetainedAlias")
}

/// The positive control: libtree's shape, a self-reference stored by `init` and used
/// by `append` within one call from outside, is held on the settled table (155 §4:
/// the hook-free line left `append::v` `Ref { mutable: true }`). The field carries raw
/// evidence here (a byte write through it), as libtree's does; the shape without it is
/// pinned below.
const SELF_REFERENCE: &str = r#"
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
pub unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); (*v).n = 0; }
pub unsafe fn append(v: *mut small_vec, x: u64) {
    *(*v).p.offset((*v).n as isize) = x;
    *((*v).p as *mut u8) = 0;
    (*v).n += 1;
}
pub unsafe fn run(v: *mut small_vec) { init(v); append(v, 1); }
"#;

#[test]
fn r864_3_a_self_reference_is_held_on_the_settled_table() {
    let d = decisions(&format!("{ALLOW}{SELF_REFERENCE}"));
    assert!(held(&d, "append::v"), "{d:#?}");
    assert!(d["append::v"].contains("evident:self-reference"), "{d:#?}");
}

/// era-5c's own `W2_RUN` (main 194a §3; R878-1; era-5c 158 / 158a): with no raw evidence
/// on `small_vec.p` the model decides it `Ref`, and the check of record used to clear
/// `append::v` on that reading while the rewriter keeps the field raw. The check's guard
/// now reads the applied field transactions (`after_deliveries`, relay 305), and no
/// transaction delivers `small_vec.p`: held.
const SELF_REFERENCE_UNMARKED: &str = r#"
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
pub unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); (*v).n = 0; }
pub unsafe fn append(v: *mut small_vec, x: u64) {
    *(*v).p.offset((*v).n as isize) = x;
    (*v).n += 1;
}
pub unsafe fn run(v: *mut small_vec) { init(v); append(v, 1); }
"#;

#[test]
fn r864_3_libtrees_self_reference_is_held_whatever_the_model_decides_the_field() {
    let d = decisions(&format!("{ALLOW}{SELF_REFERENCE_UNMARKED}"));
    assert!(held(&d, "append::v"), "{d:#?}");
    assert!(d["append::v"].contains("evident:self-reference"), "{d:#?}");
}

/// Filter 1: a formal moved into the program's storage as an owner (wave-6a's C2
/// store sink) is a move, not an alias.
const STORE_CHAIN: &str = r#"
extern "C" { fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void; }
#[repr(C)]
pub struct slot { pub key: *mut i8, pub value: i32 }
unsafe extern "C" fn slot_set(mut slots: *mut slot, mut index: usize, mut key: *mut i8, mut value: i32) {
    *key.offset(0 as isize) = 0 as i8;
    (*slots.offset(index as isize)).value = value;
    (*slots.offset(index as isize)).key = key;
}
pub unsafe extern "C" fn table_put(mut slots: *mut slot, mut index: usize) {
    let mut key = calloc(8 as usize, ::std::mem::size_of::<i8>()) as *mut i8;
    *key.offset(1 as isize) = 65 as i8;
    slot_set(slots, index, key, 7 as i32);
}
"#;

#[test]
fn r864_3_filter1_an_owning_decision_is_not_held() {
    let d = decisions(&format!("{ALLOW}{STORE_CHAIN}"));
    assert!(!held(&d, "slot_set::key"), "{d:#?}");
}

/// Filter 3: a formal stored into a field the rewriter delivers as a reference (ht's
/// iterator).
const HT: &str = include_str!("wave6f_fixture_ht.rs");

#[test]
fn r864_3_filter3_a_store_into_a_delivered_field_is_not_held() {
    let d = decisions(HT);
    assert!(!held(&d, "ht_iterator::table"), "{d:#?}");
}

/// Filter 2: a subject the retention tier waives at its retaining site (binn's
/// `GetValue` shape).
const RETAINED: &str = r#"
#[repr(C)]
pub struct Blob { pub ptr: *mut u8, pub len: i32 }
unsafe fn GetValue(mut p: *mut u8, mut value: *mut Blob) -> i32 {
    if value.is_null() { return 0; }
    (*value).ptr = p;
    (*value).len = *p.offset(0 as isize) as i32;
    return 1;
}
pub unsafe fn caller(mut buf: *mut u8, mut value: *mut Blob) -> i32 {
    if buf.is_null() { return 0; }
    *buf.offset(0 as isize) = 1 as u8;
    return GetValue(buf, value);
}
"#;

#[test]
fn r864_3_filter2_the_tiers_disposition_stands() {
    let d = decisions(&format!("{ALLOW}{RETAINED}"));
    assert!(!held(&d, "caller::buf"), "{d:#?}");
}

/// The stand-in review's round 2, R2-1 (relay 304, R878-1: E2 / E3 are never exempt):
/// filter 2 is a reading of one site's retention, not of the subject. A foreign call at
/// the subject's own site that the tier waives (`trace`: retention unknown, the tier-2
/// waiver) must not exempt the self-reference the check names (the positive control
/// plus that one call).
const SELF_REFERENCE_TRACED: &str = r#"
extern "C" { fn trace(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
pub unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); (*v).n = 0; }
pub unsafe fn append(v: *mut small_vec, x: u64) {
    trace(v as *mut core::ffi::c_void);
    *(*v).p.offset((*v).n as isize) = x;
    *((*v).p as *mut u8) = 0;
    (*v).n += 1;
}
pub unsafe fn run(v: *mut small_vec) { init(v); append(v, 1); }
"#;

#[test]
fn r864_3_round2_a_waived_site_does_not_exempt_a_self_reference() {
    let d = decisions(&format!("{ALLOW}{SELF_REFERENCE_TRACED}"));
    assert!(held(&d, "append::v"), "{d:#?}");
    assert!(d["append::v"].contains("evident:self-reference"), "{d:#?}");
}

/// R2-1's second shape: the subject's own derived store into a field the rewriter keeps
/// raw (a place expression's address: wave-6f's `store-source-raw-expression`) is a
/// retained raw pointer whatever the tier read at another of the subject's calls.
const OWN_STORE_TRACED: &str = r#"
extern "C" { fn trace(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { pub x: i32, pub y: i32 }
#[repr(C)] pub struct H { pub f: *mut i32 }
pub unsafe fn bind(h: *mut H, s: *mut S) {
    trace(s as *mut core::ffi::c_void);
    (*h).f = &mut (*s).x;
}
pub unsafe fn bump(h: *mut H) { *(*h).f += 1; }
pub unsafe fn run(h: *mut H, s: *mut S) { bind(h, s); (*s).x = 0; bump(h); }
"#;

#[test]
fn r864_3_round2_a_waived_site_does_not_exempt_an_own_store() {
    let d = decisions(&format!("{ALLOW}{OWN_STORE_TRACED}"));
    assert!(
        !d["bind::s"].starts_with("Ref") && !d["bind::s"].starts_with("InferredRef"),
        "{d:#?}"
    );
}

/// The stand-in review's round 3, R3-1: the tier's reading at one of the subject's
/// calls (`note`, T2 with a bridge) is no reading of a callee store at another call that
/// has no tier site (`keep` takes the subject inside an aggregate). `H.f` keeps the
/// pointer and `run` writes through `o` before reading through it.
const CALLEE_STORE_UNSITED: &str = r#"
#[repr(C)] pub struct S { pub x: i32 }
#[repr(C)] #[derive(Copy, Clone)] pub struct Pair { pub a: *mut S, pub n: i32 }
#[repr(C)] pub struct H { pub f: *mut S }
static mut LAST: *mut S = 0 as *mut S;
unsafe fn note(p: *mut S) { LAST = p; }
unsafe fn keep(p: Pair, h: *mut H) { (*h).f = p.a; }
pub unsafe fn f(s: *mut S, h: *mut H) { note(s); keep(Pair { a: s, n: 0 }, h); }
pub unsafe fn run(o: *mut S, h: *mut H) { f(o, h); (*o).x = 2; let _y = (*(*h).f).x; }
"#;

#[test]
fn r864_3_round3_a_reading_at_one_call_is_none_at_an_unsited_one() {
    let d = decisions(&format!("{ALLOW}{CALLEE_STORE_UNSITED}"));
    assert!(
        !d["f::s"].starts_with("Ref") && !d["f::s"].starts_with("InferredRef"),
        "{d:#?}"
    );
}

/// The review's round 3, R3-2: a protected formal released on its callee's receipt. `g`
/// hands `p` to `keep` (stored into a static, the tier-2 waiver at `g`'s site), and `f`
/// then frees what the static holds while its own `s` would be a protected `&mut S`.
const RELEASED_THEN_FREED: &str = r#"
extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { pub x: i32 }
static mut LIST: [*mut S; 8] = [0 as *mut S; 8];
static mut N: usize = 0;
unsafe fn keep(q: *mut S) { LIST[N] = q; N += 1; }
unsafe fn g(p: *mut S) { (*p).x += 1; keep(p); }
unsafe fn free_all() { while N > 0 { N -= 1; free(LIST[N] as *mut core::ffi::c_void); } }
pub unsafe fn f(s: *mut S) { g(s); free_all(); }
"#;

#[test]
fn r864_3_round3_a_formal_is_not_released_on_its_callees_receipt() {
    let d = decisions(&format!("{ALLOW}{RELEASED_THEN_FREED}"));
    assert!(
        !d["f::s"].starts_with("Ref") && !d["f::s"].starts_with("InferredRef"),
        "{d:#?}"
    );
}
