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
/// the hook-free line left `append::v` `Ref { mutable: true }`). The check reads the
/// model's field kinds (a retaining field the model decides `Ref` / `Owning` is no raw
/// retaining place), so the field carries raw evidence here (a byte write through it),
/// as libtree's does.
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
