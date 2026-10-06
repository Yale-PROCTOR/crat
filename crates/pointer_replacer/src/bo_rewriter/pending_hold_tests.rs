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
        reason_of(&out, "countHardLinks::name"),
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
        reason_of(&out, "countHardLinks::name"),
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
