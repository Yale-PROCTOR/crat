//! **R829-1 / R855-1 (USER; main 184) — the caller-side hold of the pending
//! sibling-overlap sites, decided on the settled table before anything is
//! planned.** A source delivered as a borrowed form and handed to a raw formal
//! beside a risky raw sibling is decided raw (`held:pair-not-shown-disjoint`),
//! its callers plan their bridges against that raw formal, and the pending table
//! reads 0. Run through the real round driver (`rewrite_m1_path`).

use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Outcome {
    source: String,
    reasons: Vec<(String, String)>,
    pending: usize,
}

fn outcome(text: &str) -> Outcome {
    let dir = std::env::temp_dir().join(format!(
        "crat-r855-hold-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("fixture dir");
    let root = dir.join("lib.rs");
    std::fs::write(&root, text).expect("fixture root");
    let result = super::rewrite_m1_path(&root);
    let _ = std::fs::remove_dir_all(&dir);
    match result {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            raw_boundary_artifacts,
            ..
        } => {
            println!("SOURCE\n{source}");
            for d in &degradations {
                println!("DEGRADED {} {}", d.subject, d.reason.key());
            }
            assert!(super::verify::type_checks_str(&source), "{source}");
            Outcome {
                source,
                reasons: degradations
                    .iter()
                    .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
                    .collect(),
                pending: raw_boundary_artifacts.pending_sibling_receipts.len(),
            }
        }
        other => panic!("the fixture must emit: {other:?}"),
    }
}

fn reason_of<'a>(outcome: &'a Outcome, subject: &str) -> Option<&'a str> {
    outcome
        .reasons
        .iter()
        .find(|(s, _)| s.starts_with(subject))
        .map(|(_, r)| r.as_str())
}

fn signature<'a>(source: &'a str, function: &str) -> &'a str {
    source
        .lines()
        .find(|line| line.contains(&format!("fn {function}(")))
        .unwrap_or_default()
}

/// **H-C7** (relay 293): wave-6l's `w6l_nul_c7` shape, where the round driver's
/// hold left `caller(p: &[i32]) { head(p) }` into `*mut i32` (`E0308`) and the
/// program degraded (main 182b §2). `head::dist_cache` is a formal handed to
/// `memcpy` beside the written raw `out`: it is decided raw, and the caller is
/// planned against the raw formal.
const C7: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_snake_case)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
unsafe fn head(mut dist_cache: *mut i32) {
    let mut out: [u8; 8] = [0; 8];
    memcpy(out.as_mut_ptr() as *mut core::ffi::c_void,
        dist_cache as *const core::ffi::c_void, 6 as u64);
}
pub unsafe fn caller(mut p: *mut i32) {
    head(p);
}
"#;

#[test]
fn r855_1_hc7_a_held_formal_emits_with_its_caller_planned_against_it() {
    let out = outcome(C7);
    assert_eq!(out.pending, 0, "the pending table reads 0");
    assert_eq!(
        reason_of(&out, "head::dist_cache"),
        Some("held:pair-not-shown-disjoint"),
        "{:?}",
        out.reasons
    );
    let head = signature(&out.source, "head");
    assert!(head.contains("dist_cache: *mut i32"), "held raw: {head}");
}

/// **H1** (re-pinned): `caller::src` (a formal) is handed to `update`'s raw `src`
/// beside `(*holder).data`, a raw sibling `update` writes through, and `entry`
/// passes one object to both. Decided raw under its own reason.
const PARAMETER_CASE: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub struct Holder { data: *mut i32 }\n\
    pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
    pub unsafe fn caller(holder: *const Holder, src: *const i32) {\n\
        update((*holder).data, src);\n\
    }\n\
    pub unsafe fn entry() {\n\
        let mut value = 1;\n\
        let holder = Holder { data: &mut value };\n\
        caller(&holder, &value);\n\
    }\n";

#[test]
fn r855_1_h1_a_pending_formal_is_decided_raw() {
    let out = outcome(PARAMETER_CASE);
    assert_eq!(out.pending, 0, "the pending table reads 0");
    assert_eq!(
        reason_of(&out, "caller::src"),
        Some("held:pair-not-shown-disjoint"),
        "{:?}",
        out.reasons
    );
    let caller = signature(&out.source, "caller");
    assert!(caller.contains("src: *const i32"), "held raw: {caller}");
    // Only the held source: the caller's other formal keeps its reference.
    assert!(caller.contains("holder: &Holder"), "untouched: {caller}");
}

/// The switch is strict: a value other than `on` / `off` is a mistake, never "on".
#[test]
fn r855_1_the_switch_rejects_an_unknown_value() {
    assert_eq!(super::decision::pending_hold::parse(None), Ok(true));
    assert_eq!(super::decision::pending_hold::parse(Some("on")), Ok(true));
    assert_eq!(super::decision::pending_hold::parse(Some("off")), Ok(false));
    assert!(super::decision::pending_hold::parse(Some("OFF")).is_err());
    assert!(super::decision::pending_hold::parse(Some("0")).is_err());
}

/// **H3** (R857-1, main 184a option (a)): the frame-binding premise is one
/// predicate in both places. `lstat(name, &mut statBuf)` hands a formal beside the
/// address of a binding of the caller's own frame, which did not exist when the
/// frame received `name`, so under the UB-free-input scope the two cannot alias:
/// the site is neither held at decision time nor pending at the terminal, and the
/// program emits with `name` delivered (bzip2's three `lstat` / `stat` rows,
/// R407-14).
const H3_FRAME_BINDING: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct stat {
    pub st_dev: u64,
    pub st_nlink: u64,
}
extern "C" {
    fn lstat(path: *const i8, buf: *mut stat) -> i32;
}
pub unsafe fn countHardLinks(mut name: *mut i8) -> i32 {
    let mut statBuf: stat = stat { st_dev: 0, st_nlink: 0 };
    let i = lstat(name, &mut statBuf);
    if i != 0 {
        return 0;
    }
    statBuf.st_nlink as i32 - 1
}
"#;

/// H3's control: the written sibling is borrowed THROUGH a dereference
/// (`&mut (*h).st`), storage the frame did not create, so the premise does not
/// apply and the formal is held.
const H3_THROUGH_DEREF: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct stat {
    pub st_dev: u64,
    pub st_nlink: u64,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct holder {
    pub st: stat,
}
extern "C" {
    fn lstat(path: *const i8, buf: *mut stat) -> i32;
}
pub unsafe fn countHardLinks(mut name: *mut i8, mut h: *mut holder) -> i32 {
    let i = lstat(name, &mut (*h).st);
    if i != 0 {
        return 0;
    }
    (*h).st.st_nlink as i32 - 1
}
"#;

#[test]
fn r857_1_h3_a_frame_binding_sibling_is_neither_held_nor_pending() {
    let out = outcome(H3_FRAME_BINDING);
    assert_eq!(out.pending, 0, "not a pending site");
    assert_eq!(
        reason_of(&out, "copyRec::s"),
        None,
        "not held: {:?}",
        out.reasons
    );
    let function = signature(&out.source, "countHardLinks");
    assert!(!function.contains("name: *mut i8"), "delivered: {function}");
}

#[test]
fn r857_1_h3_control_a_sibling_through_a_dereference_is_held() {
    let out = outcome(H3_THROUGH_DEREF);
    assert_eq!(out.pending, 0, "the pending table reads 0");
    assert_eq!(
        reason_of(&out, "copyRec::s"),
        Some("held:pair-not-shown-disjoint"),
        "{:?}",
        out.reasons
    );
    let function = signature(&out.source, "countHardLinks");
    assert!(function.contains("name: *mut i8"), "held raw: {function}");
}

/// **D1 (main 186): R857-1's premise at a LOCAL callee.** brotli `CopyStat`'s
/// shape: C2Rust's local `stat` wrapper stands between the formal and `__xstat`,
/// and the sibling addresses a binding of the caller's own frame. The premise is
/// about the caller's frame, not the callee's kind: neither held nor pending.
const H3_LOCAL_CALLEE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct stat_t {
    pub st_dev: u64,
    pub st_mode: u32,
}
extern "C" {
    fn __xstat(ver: i32, path: *const i8, buf: *mut stat_t) -> i32;
}
unsafe fn stat(mut path: *const i8, mut buf: *mut stat_t) -> i32 {
    return __xstat(1 as i32, path, buf);
}
pub unsafe fn CopyStat(mut name: *const i8) -> u32 {
    let mut statbuf: stat_t = stat_t { st_dev: 0, st_mode: 0 };
    if stat(name, &mut statbuf) != 0 {
        return 0;
    }
    statbuf.st_mode
}
"#;

#[test]
fn r857_1_d1_a_frame_binding_sibling_at_a_local_callee_is_neither_held_nor_pending() {
    let out = match super::rewrite_m1_census_world(H3_LOCAL_CALLEE) {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            raw_boundary_artifacts,
            ..
        } => {
            println!("SOURCE\n{source}");
            assert!(super::verify::type_checks_str(&source), "{source}");
            Outcome {
                source,
                reasons: degradations
                    .iter()
                    .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
                    .collect(),
                pending: raw_boundary_artifacts.pending_sibling_receipts.len(),
            }
        }
        other => panic!("the fixture must emit: {other:?}"),
    };
    assert_eq!(out.pending, 0, "not a pending site");
    assert_eq!(
        reason_of(&out, "CopyStat::name"),
        None,
        "not held: {:?}",
        out.reasons
    );
}

/// D1 in the open world (`rewrite_m1`, no attestation: no A5 proof is final), as
/// the suite's fixtures run: the premise alone keeps the site off the pending set
/// and the formal is not this hold's (in this world `stat::path` takes its own
/// `held:thin-extent`, and its class carries `CopyStat` with it).
#[test]
fn r857_1_d1_open_world_a_frame_binding_sibling_at_a_local_callee_is_not_held() {
    let out = outcome(H3_LOCAL_CALLEE);
    assert_eq!(out.pending, 0, "not a pending site");
    assert_ne!(
        reason_of(&out, "CopyStat::name"),
        Some("held:pair-not-shown-disjoint"),
        "not this hold's: {:?}",
        out.reasons
    );
}

/// **R861-1 (D3): a string-literal sibling is not risky.** On a UB-free input a
/// literal is never written, so a literal beside a formal cannot be the written
/// side of an overlap (as R608-1 treats a literal SOURCE). `strncmp` has no
/// contract row, so its literal argument reads `Unknown`; the formal is neither
/// held nor pending.
const D3_LITERAL_SIBLING: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
extern "C" {
    fn strncmp(a: *const i8, b: *const i8, n: u64) -> i32;
}
pub unsafe fn is_flag(mut name: *const i8) -> i32 {
    let mut first: i8 = *name;
    if first == 0 {
        return 0;
    }
    return (strncmp(name, b"--\0" as *const u8 as *const i8, 2 as u64) == 0) as i32;
}
"#;

#[test]
fn r861_1_d3_a_string_literal_sibling_is_not_risky() {
    let out = outcome(D3_LITERAL_SIBLING);
    assert_eq!(out.pending, 0, "not a pending site");
    assert_ne!(
        reason_of(&out, "is_flag::name"),
        Some("held:pair-not-shown-disjoint"),
        "not held: {:?}",
        out.reasons
    );
}

/// **The probe's json.h collateral (main 186 §5, relay 297).** The callee's
/// formal is held (`memcpy` writes its sibling), and the caller hands it its own
/// OPTIONAL formal (a null test makes it `Option<&T>`): the call is planned with
/// the ordinary bridge into the held raw formal, so no verify round reverts it.
const JSON_OPTION_INTO_HELD: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct json_value_s {
    pub payload: i32,
    pub type_0: i32,
}
unsafe extern "C" fn copy_value(mut state: *mut u8, mut value: *const json_value_s) {
    memcpy(state as *mut core::ffi::c_void, value as *const core::ffi::c_void, 8 as u64);
}
pub unsafe extern "C" fn extract(mut value: *const json_value_s) -> i32 {
    if value.is_null() {
        return 0;
    }
    let mut buf: [u8; 8] = [0; 8];
    copy_value(buf.as_mut_ptr(), value);
    return (*value).type_0;
}
"#;

#[test]
fn r857_1_an_optional_formal_into_a_held_raw_formal_is_bridged() {
    let (source, degradations) = match super::rewrite_m1_census_world(JSON_OPTION_INTO_HELD) {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            ..
        } => (source, degradations),
        other => panic!("the fixture must emit: {other:?}"),
    };
    println!("SOURCE\n{source}");
    let reverted = degradations
        .iter()
        .filter(|d| d.reason.key() == "reverted-after-verify-failure")
        .map(|d| d.subject.clone())
        .collect::<Vec<_>>();
    assert!(reverted.is_empty(), "verify reverts: {reverted:?}");
}

/// **Relay 297: one held map, one loop.** `Drop2::p` is both copied by `memcpy`
/// beside the written `out` (the pending hold) and released through
/// `free_func` (R857-2's backstop): it stays held, and the settled-hold table
/// carries BOTH predicates' receipts for it.
const TWO_HOLDS: &str = r#"
// r861-two-holds
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
extern "C" {
    fn free(p: *mut core::ffi::c_void);
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
pub type free_func_t =
    Option<unsafe extern "C" fn(*mut core::ffi::c_void, *mut core::ffi::c_void) -> ()>;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct MemoryManager {
    pub free_func: free_func_t,
    pub opaque: *mut core::ffi::c_void,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Obj {
    pub k: i32,
}
unsafe extern "C" fn DefaultFree(mut opaque: *mut core::ffi::c_void, mut address: *mut core::ffi::c_void) {
    free(address);
}
pub unsafe fn Init(mut m: *mut MemoryManager) {
    (*m).free_func = Some(DefaultFree as unsafe extern "C" fn(*mut core::ffi::c_void, *mut core::ffi::c_void) -> ());
}
pub unsafe fn Drop2(mut m: *mut MemoryManager, mut out: *mut Obj, mut p: *mut Obj) {
    memcpy(out as *mut core::ffi::c_void, p as *const core::ffi::c_void, 4 as u64);
    (*m).free_func.expect("non-null function pointer")((*m).opaque, p as *mut core::ffi::c_void);
}
"#;

#[test]
fn r861_a_subject_two_holds_name_stays_held_with_both_receipts() {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set(
        "r861-two-holds",
        Vec::new(),
        vec![("Drop2::p".to_owned(), SlotKind::Ref)],
    );
    let result = super::rewrite_m1_census_world(TWO_HOLDS);
    super::test_model_override::clear();
    let super::RewriteOutcome::Emitted {
        source,
        degradations,
        raw_boundary_artifacts,
        ..
    } = result
    else {
        panic!("the fixture must emit: {result:?}");
    };
    println!(
        "SOURCE\n{source}\nRECEIPTS\n{}",
        raw_boundary_artifacts.settled_hold_receipts
    );
    let reason = degradations
        .iter()
        .find(|d| d.subject.starts_with("Drop2::p"))
        .map(|d| d.reason.key());
    assert!(
        matches!(
            reason,
            Some("held:released-through-indirect-call" | "held:pair-not-shown-disjoint")
        ),
        "held: {reason:?}"
    );
    let predicates = raw_boundary_artifacts
        .settled_hold_receipts
        .lines()
        .filter(|row| {
            row.split('\t')
                .nth(1)
                .is_some_and(|s| s.contains("Drop2::p"))
        })
        .map(|row| row.split('\t').next().unwrap_or_default().to_owned())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        predicates,
        [
            "held:pair-not-shown-disjoint",
            "held:released-through-indirect-call"
        ]
        .into_iter()
        .map(str::to_owned)
        .collect(),
        "{}",
        raw_boundary_artifacts.settled_hold_receipts
    );
}

/// **The comparison view of a held formal** (relay 297; libzahl `zor` / `zxor` /
/// `zadd_unsigned` at the 57 head): the address views of a pointer comparison
/// are planned once, on the table before the holds, so a formal the hold later
/// makes raw kept its reference view, `core::ptr::from_ref(c).cast_mut()` over a
/// `*mut` (`E0308`). A held operand keeps its raw text, as any raw operand of a
/// comparison does.
const HELD_COMPARISON: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub struct Num { used: i32, sign: i32 }\n\
    pub static mut LAST: *mut Num = 0 as *mut Num;\n\
    pub unsafe fn set(a: *mut Num, b: *mut Num) { LAST = b; (*a).sign = (*b).sign; (*a).used = (*b).used; }\n\
    pub unsafe fn or(a: *mut Num, b: *mut Num, c: *mut Num) {\n\
        if (*b).used == 0 { if a != c { set(a, c); } return; }\n\
        (*a).used = (*b).used + (*c).used;\n\
    }\n\
    pub unsafe fn entry() {\n\
        let mut x = Num { used: 0, sign: 0 };\n\
        let mut y = Num { used: 0, sign: 1 };\n\
        let mut z = Num { used: 1, sign: 1 };\n\
        or(&mut x, &mut y, &mut z);\n\
    }\n";

#[test]
fn r861_1_a_held_operand_of_a_comparison_keeps_its_raw_text() {
    let out = outcome(HELD_COMPARISON);
    assert_eq!(
        reason_of(&out, "or::c"),
        Some("held:pair-not-shown-disjoint"),
        "{:?}",
        out.reasons
    );
    let or = signature(&out.source, "or");
    assert!(or.contains("c: *mut Num"), "held raw: {or}");
    assert!(
        !out.source.contains("from_ref(c)") && !out.source.contains("from_mut(&mut *c)"),
        "no reference view of a held formal: {}",
        out.source
    );
}

/// The census's A5 world (`rewrite_m1_census_world`), read as [`outcome`] reads
/// the open world.
fn census_outcome(text: &str) -> Outcome {
    match super::rewrite_m1_census_world(text) {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            raw_boundary_artifacts,
            ..
        } => {
            println!("SOURCE\n{source}");
            assert!(super::verify::type_checks_str(&source), "{source}");
            Outcome {
                source,
                reasons: degradations
                    .iter()
                    .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
                    .collect(),
                pending: raw_boundary_artifacts.pending_sibling_receipts.len(),
            }
        }
        other => panic!("the fixture must emit: {other:?}"),
    }
}

/// **D1 beneath casts** (relay 297; binn `binn_list_int32`'s
/// `&mut value as *mut i32 as *mut c_void`): the address of the caller's own
/// binding, cast, is still that binding's address, so the premise reads it as
/// it reads `&mut statbuf`.
const H3_LOCAL_CALLEE_CAST: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct stat_t {
    pub st_dev: u64,
    pub st_mode: u32,
}
extern "C" {
    fn __xstat(ver: i32, path: *const i8, buf: *mut stat_t) -> i32;
}
unsafe fn stat(mut path: *const i8, mut buf: *mut core::ffi::c_void) -> i32 {
    return __xstat(1 as i32, path, buf as *mut stat_t);
}
pub unsafe fn CopyStat(mut name: *const i8) -> u32 {
    let mut statbuf: stat_t = stat_t { st_dev: 0, st_mode: 0 };
    if stat(name, &mut statbuf as *mut stat_t as *mut core::ffi::c_void) != 0 {
        return 0;
    }
    statbuf.st_mode
}
"#;

#[test]
fn r861_1_d1_a_frame_binding_sibling_beneath_casts_is_neither_held_nor_pending() {
    let out = census_outcome(H3_LOCAL_CALLEE_CAST);
    assert_eq!(out.pending, 0, "not a pending site");
    assert_eq!(
        reason_of(&out, "CopyStat::name"),
        None,
        "not held: {:?}",
        out.reasons
    );
}

/// The same in the open world, where no A5 proof is final: the premise alone
/// keeps the site off the pending set.
#[test]
fn r861_1_d1_open_world_a_frame_binding_sibling_beneath_casts_is_not_held() {
    let out = outcome(H3_LOCAL_CALLEE_CAST);
    assert_eq!(out.pending, 0, "not a pending site");
    assert_ne!(
        reason_of(&out, "CopyStat::name"),
        Some("held:pair-not-shown-disjoint"),
        "not this hold's: {:?}",
        out.reasons
    );
}

/// **The premise's own condition (the stand-in review's M1).** A formal
/// reassigned before the call (`s = other`) may no longer hold a referent from
/// before the frame, so the frame-binding exemption reads only a formal holding
/// its entry value or a pointer stepped from it. (No reduced RED: on this shape
/// and on the `lstat` one the reassignment trips another hold first — a lifetime
/// degrade, `held:thin-extent` — so the fixture serves the control below.)
const H3_REASSIGNED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct rec {
    pub a: u64,
    pub b: u64,
}
extern "C" {
    fn fill(src: *const rec, dst: *mut rec) -> i32;
}
pub unsafe fn copyRec(mut s: *mut rec, mut other: *mut rec) -> u64 {
    let mut local: rec = rec { a: 0, b: 0 };
    if (*other).a != 0 {
        s = other;
    }
    let i = fill(s, &mut local);
    if i != 0 {
        return 0;
    }
    local.b + (*s).a
}
"#;

/// The control: a formal only stepped from itself (`s = s.offset(1)`) still
/// addresses its entry referent; the premise applies.
#[test]
fn r861_1_m1_a_formal_stepped_from_itself_keeps_the_premise() {
    let input = H3_REASSIGNED.replace("        s = other;\n", "        s = s.offset(1);\n");
    assert!(input.contains("s.offset(1)"));
    let out = outcome(&input);
    assert_ne!(
        reason_of(&out, "copyRec::s"),
        Some("held:pair-not-shown-disjoint"),
        "{:?}",
        out.reasons
    );
}

/// **The ladder's borrowed rule into a held formal (the stand-in review's M4).**
/// `caller::src` is held beside `(*holder).data` (H1); `outer` hands it
/// `&mut *r`, a reborrow of its delivered `r`: the raw pointer `update` may keep
/// would outlive the reborrow, so `r` is held too (`held:into-held-formal`), as
/// the ladder blocks `borrowed-into-raw-param`.
const BORROWED_INTO_HELD: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub struct Holder { data: *mut i32 }\n\
    pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
    pub unsafe fn caller(holder: *const Holder, src: *const i32) {\n\
        update((*holder).data, src);\n\
    }\n\
    pub unsafe fn outer(holder: *const Holder, r: *mut i32) {\n\
        *r = 3;\n\
        caller(holder, &mut *r);\n\
    }\n\
    pub unsafe fn entry() {\n\
        let mut value = 1;\n\
        let mut other = 2;\n\
        let holder = Holder { data: &mut value };\n\
        outer(&holder, &mut other);\n\
    }\n";

#[test]
fn r861_1_m4_a_binding_borrowed_into_a_held_formal_is_held() {
    let out = outcome(BORROWED_INTO_HELD);
    assert_eq!(
        reason_of(&out, "caller::src"),
        Some("held:pair-not-shown-disjoint"),
        "{:?}",
        out.reasons
    );
    assert_eq!(
        reason_of(&out, "outer::r"),
        Some("held:into-held-formal"),
        "{:?}",
        out.reasons
    );
}

/// **Within the function (the stand-in review's M4).** `caller::s2` is the held
/// source; `src` initializes it whole. The model keeps the two in one kind; with
/// `s2` held raw, a delivered `src` would coerce into it silently, so `src` is
/// held too (`into-held-binding`).
const FLOWS_INTO_HELD: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub struct Holder { data: *mut i32 }\n\
    pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }\n\
    pub unsafe fn caller(holder: *const Holder, src: *const i32) {\n\
        let s2: *const i32 = src;\n\
        update((*holder).data, s2);\n\
    }\n\
    pub unsafe fn entry() {\n\
        let mut value = 1;\n\
        let holder = Holder { data: &mut value };\n\
        caller(&holder, &value);\n\
    }\n";

#[test]
fn r861_1_m4_a_binding_flowing_into_a_held_binding_is_held() {
    let out = outcome(FLOWS_INTO_HELD);
    let held = |subject: &str| {
        matches!(
            reason_of(&out, subject),
            Some("held:pair-not-shown-disjoint" | "held:into-held-formal")
        )
    };
    assert!(
        held("caller::s2") && held("caller::src"),
        "both held: {:?}",
        out.reasons
    );
    let caller = signature(&out.source, "caller");
    assert!(caller.contains("src: *const i32"), "raw: {caller}");
}
