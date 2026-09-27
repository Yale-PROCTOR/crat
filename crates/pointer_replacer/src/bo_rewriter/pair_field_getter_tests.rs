//! wave-6p R601-4 (G4): a call result through a field-returning callee.
//!
//! R579-3 (ii) carries an admitted field's root into a local that reads it —
//! `data = (*s).buf` names the block `buf` holds, separated from `*s`. A local
//! that takes the SAME value from a getter, `out = GetStorage(s, n)` whose every
//! return is `(*s).storage`, stayed `Unknown` (`call-result`), and every chain
//! that met it stopped: brotli's `EncodeData` holds 8 subjects that way (report
//! 047). G4 carries the fact across the one call boundary: the result is the
//! field's block, keyed to the root of the ARGUMENT at the getter's formal.

use super::decision::pair_disjointness::{CertificateKind, PairDisjointnessIndex, Unproved};

fn verdict(
    src: &str,
    caller: &str,
    callee: &str,
    left: usize,
    right: usize,
) -> Result<CertificateKind, Unproved> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = PairDisjointnessIndex::derive(&program, &mut_facts, None);
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        out = Some(index.certify_recorded(function(caller), function(callee), left, right));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

/// `storage` and `scratch` are stored only by `malloc` (admitted, not
/// same-base-only); `cmds` through a fresh local (admitted, same-base-only);
/// `loose` points into the struct's own `hist` (never admitted). `Put` takes
/// two formals of one pointee type, so the type rule refuses `same-type` and
/// the root rules are the ones under test; `Relay` is (e)'s intermediate and
/// `Store` static-vs-entry's.
const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables, unused_assignments)]
extern "C" {
    fn malloc(n: libc::c_ulong) -> *mut libc::c_void;
    fn free(p: *mut libc::c_void);
}
#[repr(C)]
pub struct S {
    pub storage: *mut u8,
    pub scratch: *mut u8,
    pub cmds: *mut u8,
    pub loose: *mut u8,
    pub hist: [u8; 8],
}
pub static TABLE: [u8; 4] = [1, 2, 3, 4];
pub unsafe fn Init(mut s: *mut S) {
    (*s).storage = malloc(64) as *mut u8;
    (*s).scratch = malloc(8) as *mut u8;
    let mut c = malloc(32) as *mut u8;
    (*s).cmds = c;
    (*s).loose = (*s).hist.as_mut_ptr();
}
pub unsafe fn Put(mut a: *mut u8, mut b: *mut u8) {
    *a = 1;
    *b = 2;
}
pub unsafe fn Relay(mut a: *mut u8, mut b: *mut u8) {
    Put(a, b);
}
pub unsafe fn Peek(mut a: *const u8, mut b: *mut u8) {
    *b = *a;
}
pub unsafe fn Store(mut out: *mut u8) {
    Peek(TABLE.as_ptr(), out);
}
/// brotli's `GetBrotliStorage`: frees and re-allocates the field, then returns
/// it; a null return is the one other value it may give (R479-4b).
pub unsafe fn GetStorage(mut s: *mut S, mut n: libc::c_ulong) -> *mut u8 {
    if n == 0 {
        return 0 as *mut u8;
    }
    if n > 64 {
        free((*s).storage as *mut libc::c_void);
        (*s).storage = malloc(n) as *mut u8;
    }
    return (*s).storage;
}
"#;

/// W1: `EncodeData`'s shape — the getter's result beside a place in its base.
const GETTER_OF_AN_ADMITTED_FIELD: &str = r#"
pub unsafe fn Emit(mut s: *mut S) {
    let mut out = GetStorage(s, 128);
    Relay((*s).hist.as_mut_ptr(), out);
    Store(out);
}
"#;

/// W2: the getter reads its SECOND formal, so the base is that argument's.
const GETTER_OF_THE_SECOND_FORMAL_BESIDE_IT: &str = r#"
pub unsafe fn GetFrom(mut s: *mut S, mut t: *mut S) -> *mut u8 {
    return (*t).storage;
}
pub unsafe fn Emit(mut s: *mut S, mut t: *mut S) {
    let mut out = GetFrom(s, t);
    Relay((*t).hist.as_mut_ptr(), out);
}
"#;

/// C1: `loose` points into `hist`, so the getter can return `hist` itself.
const GETTER_OF_A_FIELD_NOT_ADMITTED: &str = r#"
pub unsafe fn GetLoose(mut s: *mut S) -> *mut u8 {
    return (*s).loose;
}
pub unsafe fn Emit(mut s: *mut S) {
    let mut out = GetLoose(s);
    Relay((*s).hist.as_mut_ptr(), out);
}
"#;

/// C2: brotli's `GetHashTable` — a view of the formal's own storage on one
/// path, an admitted field on the other. Here it returns `hist`.
const GETTER_OF_A_VIEW_OR_A_FIELD: &str = r#"
pub unsafe fn GetTable(mut s: *mut S, mut n: libc::c_ulong) -> *mut u8 {
    if n <= 8 {
        return (*s).hist.as_mut_ptr();
    }
    return (*s).storage;
}
pub unsafe fn Emit(mut s: *mut S) {
    let mut out = GetTable(s, 4);
    Relay((*s).hist.as_mut_ptr(), out);
}
"#;

/// C3: two admitted fields — here it returns `scratch`, passed beside itself.
const GETTER_OF_TWO_FIELDS: &str = r#"
pub unsafe fn GetEither(mut s: *mut S, mut n: libc::c_ulong) -> *mut u8 {
    if n > 8 {
        return (*s).storage;
    }
    return (*s).scratch;
}
pub unsafe fn Emit(mut s: *mut S) {
    let mut out = GetEither(s, 4);
    Relay((*s).scratch, out);
}
"#;

/// C4: `cmds` is same-base-only (R579-3); a getter does not launder that.
const GETTER_OF_A_SAME_BASE_ONLY_FIELD: &str = r#"
pub unsafe fn GetCmds(mut s: *mut S) -> *mut u8 {
    return (*s).cmds;
}
pub unsafe fn Emit(mut s: *mut S) {
    let mut c = GetCmds(s);
    let mut out = GetStorage(s, 128);
    Relay(c, out);
}
"#;

/// C5: the field of either formal. A caller may pass `s = (*t).storage`, and
/// then the result IS `*s`.
const GETTER_OF_TWO_FORMALS: &str = r#"
pub unsafe fn GetFromEither(mut s: *mut S, mut t: *mut S, mut n: libc::c_ulong) -> *mut u8 {
    if n > 8 {
        return (*s).storage;
    }
    return (*t).storage;
}
pub unsafe fn Emit(mut s: *mut S, mut t: *mut S) {
    let mut out = GetFromEither(s, t, 4);
    Relay((*s).hist.as_mut_ptr(), out);
}
"#;

/// C6: the base is the SECOND argument's root, so the result is not separated
/// from the first: a caller may pass `s = (*t).storage`.
const GETTER_OF_THE_SECOND_FORMAL_BESIDE_THE_FIRST: &str = r#"
pub unsafe fn GetFrom(mut s: *mut S, mut t: *mut S) -> *mut u8 {
    return (*t).storage;
}
pub unsafe fn Emit(mut s: *mut S, mut t: *mut S) {
    let mut out = GetFrom(s, t);
    Relay((*s).hist.as_mut_ptr(), out);
}
"#;

fn source(extra: &str) -> String {
    format!("{PRELUDE}{extra}")
}

#[test]
fn w6p_g4_a_getter_result_is_the_fields_block_beside_its_base() {
    assert_eq!(
        verdict(&source(GETTER_OF_AN_ADMITTED_FIELD), "Emit", "Relay", 0, 1),
        Ok(CertificateKind::DistinctRoots),
        "`out` is the block `(*s).storage` holds, so it is not `(*s).hist`"
    );
}

#[test]
fn w6p_g4_static_vs_entry_reads_a_getter_result_as_known() {
    assert_eq!(
        verdict(&source(GETTER_OF_AN_ADMITTED_FIELD), "Store", "Peek", 0, 1),
        Ok(CertificateKind::StaticVsEntry(1)),
        "`Store`'s one caller passes the getter's result, a block that is not `TABLE`"
    );
}

#[test]
fn w6p_g4_parameter_pair_reads_a_getter_result_as_known() {
    assert_eq!(
        verdict(&source(GETTER_OF_AN_ADMITTED_FIELD), "Relay", "Put", 0, 1),
        Ok(CertificateKind::ParameterPair),
        "`Relay`'s one caller separates its two arguments, so (e) proves the formals"
    );
}

#[test]
fn w6p_g4_the_base_is_the_argument_at_the_getters_formal() {
    assert_eq!(
        verdict(
            &source(GETTER_OF_THE_SECOND_FORMAL_BESIDE_IT),
            "Emit",
            "Relay",
            0,
            1
        ),
        Ok(CertificateKind::DistinctRoots),
        "`GetFrom` reads `(*t).storage`, so its result is separated from `*t`"
    );
}

#[test]
fn w6p_g4_a_getter_of_a_field_that_is_not_admitted_stays_unknown() {
    let verdict = verdict(
        &source(GETTER_OF_A_FIELD_NOT_ADMITTED),
        "Emit",
        "Relay",
        0,
        1,
    );
    assert!(
        verdict.is_err(),
        "`loose` holds `(*s).hist.as_mut_ptr()`: got {verdict:?}"
    );
}

#[test]
fn w6p_g4_a_getter_that_may_return_a_view_of_its_formal_stays_unknown() {
    let verdict = verdict(&source(GETTER_OF_A_VIEW_OR_A_FIELD), "Emit", "Relay", 0, 1);
    assert!(
        verdict.is_err(),
        "one return is `(*s).hist.as_mut_ptr()` itself: got {verdict:?}"
    );
}

#[test]
fn w6p_g4_a_getter_of_two_fields_stays_unknown() {
    let verdict = verdict(&source(GETTER_OF_TWO_FIELDS), "Emit", "Relay", 0, 1);
    assert!(
        verdict.is_err(),
        "the result may be `(*s).scratch`, passed beside it: got {verdict:?}"
    );
}

#[test]
fn w6p_g4_a_same_base_only_field_is_still_refused_beside_another_field() {
    let verdict = verdict(
        &source(GETTER_OF_A_SAME_BASE_ONLY_FIELD),
        "Emit",
        "Relay",
        0,
        1,
    );
    assert!(
        verdict.is_err(),
        "R579-3: `cmds` separates only from its own base: got {verdict:?}"
    );
}

#[test]
fn w6p_g4_a_getter_of_two_formals_stays_unknown() {
    let verdict = verdict(&source(GETTER_OF_TWO_FORMALS), "Emit", "Relay", 0, 1);
    assert!(
        verdict.is_err(),
        "the result may be `(*t).storage`, which a caller may pass as `s`: got {verdict:?}"
    );
}

#[test]
fn w6p_g4_a_getter_of_the_second_formal_is_not_separated_from_the_first() {
    let verdict = verdict(
        &source(GETTER_OF_THE_SECOND_FORMAL_BESIDE_THE_FIRST),
        "Emit",
        "Relay",
        0,
        1,
    );
    assert!(
        verdict.is_err(),
        "the result is keyed to `t`; `s` may be `(*t).storage` itself: got {verdict:?}"
    );
}
