//! era-5c relay 213 (R988-1, USER): the MUTABLE copy-lend (`CRAT_ERA5C_COPY_LEND_MUT=on`). A copy
//! `q = p` whose destination is written through is lent `q = &mut *p` when no read, write or
//! reassignment of `p` (or of another copy of `p`) happens while `q` is live; the lend's loan is
//! unique, so the replay stays the judge. Each witness runs in a child under the frame of record's
//! env (`frames/l01p14u-s39-env.sh`) with the switch as named, and reads the classifier's row for
//! each copy pair and the settled kinds by name.

use std::collections::BTreeMap;

const FRAME_ENV: &str = include_str!("../../../frames/l01p14u-s39-env.sh");

const LIBC: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types)]
extern "C" {
    fn malloc(_: u64) -> *mut core::ffi::c_void;
    fn free(_: *mut core::ffi::c_void);
}
"#;

/// (i) `q = p; *q = 1;` then `p` used after `q`'s window and released: a mutable lend.
const MUT_LEND: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let q: *mut i32 = p;
    *q = 1;
    let r = *p;
    free(p as *mut core::ffi::c_void);
    r
}
"#;

/// (ii) `p` written while `q` is live: no lend.
const WRITE_IN_WINDOW: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let q: *mut i32 = p;
    *q = 1;
    *p = 2;
    *q = 3;
    let r = *p;
    free(p as *mut core::ffi::c_void);
    r
}
"#;

/// (ii″) `p` READ while `q` is live: no lend. A shared copy-lend's loan already conflicts with a
/// write to its owner; only a unique loan conflicts with this read.
const READ_IN_WINDOW: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let q: *mut i32 = p;
    *q = 1;
    let r = *p;
    *q = 3;
    free(p as *mut core::ffi::c_void);
    r
}
"#;

/// (ii′) another copy of `p` written while `q` is live: no lend.
const OTHER_COPY_IN_WINDOW: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let q: *mut i32 = p;
    let s: *mut i32 = p;
    *q = 1;
    *s = 2;
    *q = 3;
    let r = *p;
    free(p as *mut core::ffi::c_void);
    r
}
"#;

/// (iii) the destination released (S2-2): no lend, as today.
const FREE_DESTINATION: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let q: *mut i32 = p;
    *q = 1;
    free(q as *mut core::ffi::c_void);
    0
}
"#;

/// (iii′) `free(p)` on a path after `q`'s last use: outside the window (`q`'s liveness ends at
/// `*q = 1` on that path), so the lend is taken.
const FREE_AFTER_LAST_USE: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run(c: i32) -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let q: *mut i32 = p;
    *q = 1;
    if c != 0 {
        free(p as *mut core::ffi::c_void);
        return 0;
    }
    *q = 2;
    free(p as *mut core::ffi::c_void);
    1
}
"#;

/// (iii″) `free(p)` while `q` is live: `q` is used after the release, so the input itself is UB
/// (§28 owes it nothing); the window check still refuses the lend.
const FREE_IN_WINDOW: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    let q: *mut i32 = p;
    *q = 1;
    free(p as *mut core::ffi::c_void);
    *q = 2;
    0
}
"#;

/// (iv) a read-only copy (era-5c 133's `copy_read`): the shared lend, unchanged.
const READ_ONLY: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    *p = 7;
    let q: *mut i32 = p;
    let r = *q;
    free(p as *mut core::ffi::c_void);
    r
}
"#;

const SHAPES: [(&str, &str); 9] = [
    ("MUT_LEND", MUT_LEND),
    ("WRITE_IN_WINDOW", WRITE_IN_WINDOW),
    ("READ_IN_WINDOW", READ_IN_WINDOW),
    ("OTHER_COPY_IN_WINDOW", OTHER_COPY_IN_WINDOW),
    ("FREE_DESTINATION", FREE_DESTINATION),
    ("FREE_AFTER_LAST_USE", FREE_AFTER_LAST_USE),
    ("FREE_IN_WINDOW", FREE_IN_WINDOW),
    ("READ_ONLY", READ_ONLY),
    ("BOTH", ""),
];

fn shape(name: &str) -> String {
    let body = SHAPES
        .iter()
        .find(|(shape, _)| *shape == name)
        .unwrap_or_else(|| panic!("unknown shape {name}"))
        .1;
    format!("{LIBC}{body}")
}

/// The frame of record's arms: every `CRAT_` export but the raw-cause sidecar and the launch
/// identity (`CRAT_ERA5_*`), which a fixture solve does not take.
fn frame_arms() -> Vec<(String, String)> {
    FRAME_ENV
        .lines()
        .filter_map(|line| line.strip_prefix("export "))
        .filter_map(|assignment| {
            let assignment = assignment.split('#').next()?.trim();
            let (key, value) = assignment.split_once('=')?;
            (key.starts_with("CRAT_")
                && !key.starts_with("CRAT_ERA5_")
                && !key.starts_with("CRAT_ERA5C_RAW_CAUSE"))
            .then(|| (key.to_owned(), value.trim().to_owned()))
        })
        .collect()
}

/// The classifier's rows (`fn q p drop`, `drop` = `eligible` or `eligible-mut` when kept) for the
/// shape under the switch as the environment gives it.
fn classifier_rows(code: &str) -> Vec<String> {
    use rustc_hir::{ItemKind, OwnerNode};
    let mut rows = Vec::new();
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = super::crate_slots::CrateSlots::build(&program);
        let origins = super::origins::compute_origins(&program);
        let mutability = super::mutability_facts::MutFacts::from_program(&program);
        for candidate in super::construction::analyze_copy_lend_candidates(
            &program,
            &slots,
            &mutability,
            origins.native_flows(),
        ) {
            let site = &candidate.sites[0];
            let body = tcx
                .mir_drops_elaborated_and_const_checked(site.fn_did)
                .borrow();
            let name = |local: rustc_middle::mir::Local| {
                body.var_debug_info
                    .iter()
                    .find_map(|info| match info.value {
                        rustc_middle::mir::VarDebugInfoContents::Place(place)
                            if place.local == local && place.projection.is_empty() =>
                        {
                            Some(info.name.to_string())
                        }
                        _ => None,
                    })
                    .unwrap_or_else(|| format!("{local:?}"))
            };
            let kept = if candidate.pair.mutable {
                "eligible-mut"
            } else {
                "eligible"
            };
            rows.push(format!(
                "{} {} {} {}",
                tcx.item_name(site.fn_did.to_def_id()),
                name(site.lhs_local),
                name(site.rhs_local),
                candidate.drop.map_or(kept, |drop| drop.label())
            ));
        }
    })
    .expect("the fixture compiles");
    rows.sort();
    rows
}

#[test]
#[ignore = "runs under the frame's arms in a child of the e5c_cm witnesses"]
fn e5c_inner_copy_lend_mut() {
    let code = shape(&std::env::var("CRAT_E5C_CM_SHAPE").expect("CRAT_E5C_CM_SHAPE"));
    for row in classifier_rows(&code) {
        println!("E5C_CM_ROW {row}");
    }
    if std::env::var("CRAT_E5C_CM_KINDS").as_deref() != Ok("off") {
        for (key, kind) in super::copy_relax_tests::kinds(&code) {
            println!("E5C_CM_KIND {key} {kind}");
        }
    }
}

/// What a child saw: the classifier's rows and the settled kinds.
#[derive(Debug, PartialEq, Eq)]
struct Seen {
    rows: Vec<String>,
    kinds: BTreeMap<String, String>,
}

/// The shape under the frame's arms and the extra environment `extra` (faults).
fn seen_with(name: &str, extra: &[(&str, &str)]) -> Seen {
    let exe = std::env::current_exe().expect("current_exe");
    let mut command = std::process::Command::new(exe);
    command.args([
        "analyses::borrow_ownership::copy_lend_mut_tests::e5c_inner_copy_lend_mut",
        "--exact",
        "--ignored",
        "--nocapture",
        "--test-threads=1",
    ]);
    for (key, value) in frame_arms() {
        command.env(key, value);
    }
    command.env("CRAT_E5C_CM_SHAPE", name);
    for (key, value) in extra {
        command.env(key, value);
    }
    let output = command.output().expect("child test");
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "child {name} failed:\n{text}");
    let rows = text
        .lines()
        .filter_map(|l| {
            l.split_once("E5C_CM_ROW ")
                .map(|(_, rest)| rest.trim().to_owned())
        })
        .collect();
    let kinds = text
        .lines()
        .filter_map(|l| l.split_once("E5C_CM_KIND ").map(|(_, rest)| rest))
        .filter_map(|l| l.rsplit_once(' '))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect();
    let seen = Seen { rows, kinds };
    eprintln!("E5C_CM_SEEN {name} mutable={mutable:?} extra={extra:?} {seen:?}");
    seen
}

fn seen(name: &str) -> Seen {
    seen_with(name, &[])
}

fn row<'a>(seen: &'a Seen, q: &str, p: &str) -> &'a str {
    seen.rows
        .iter()
        .find_map(|row| {
            let cols: Vec<_> = row.split(' ').collect();
            (cols[1] == q && cols[2] == p).then_some(cols[3])
        })
        .unwrap_or_else(|| panic!("no pair {q} = {p}: {seen:#?}"))
}

fn kind<'a>(seen: &'a Seen, key: &str) -> &'a str {
    seen.kinds
        .get(key)
        .map(String::as_str)
        .unwrap_or_else(|| panic!("no {key}: {seen:#?}"))
}

/// (i) A copy written through, `p` used after `q`'s window and released: the pair is lent
/// mutably, `p` owns (`Box`) and `q` is a reference (`&mut`).
#[test]
fn e5c_cm_1_a_written_copy_is_lent_mutably() {
    let s = seen("MUT_LEND");
    assert_eq!(row(&s, "q", "p"), "eligible-mut", "{s:#?}");
    assert_eq!(kind(&s, "run::p"), "owning", "{s:#?}");
    assert_eq!(kind(&s, "run::q"), "ref", "{s:#?}");
}

/// (ii) `p`, or another copy of it, written while `q` is live: the window check refuses.
#[test]
fn e5c_cm_2_an_access_in_the_window_refuses_the_lend() {
    for name in ["WRITE_IN_WINDOW", "OTHER_COPY_IN_WINDOW"] {
        let on = seen(name);
        assert_eq!(
            row(&on, "q", "p"),
            "c2-mutable-window-access",
            "{name}: {on:#?}"
        );
    }
}

/// (ii″) `p` read while `q` is live: the window check refuses.
#[test]
fn e5c_cm_2_a_read_of_the_owner_in_the_window_refuses_the_lend() {
    let on = seen("READ_IN_WINDOW");
    assert_eq!(row(&on, "q", "p"), "c2-mutable-window-access", "{on:#?}");
}

/// Whether the shape's solve took the mutable lend (`p` owning beside `q` a reference).
fn lent(seen: &Seen) -> bool {
    kind(seen, "run::p") == "owning" && kind(seen, "run::q") == "ref"
}

/// Fault F1 (`no-window`): without the static window check the classifier keeps both window
/// shapes, and the replay's unique loan still refuses the lend: the replay is the judge.
#[test]
fn e5c_cm_f1_without_the_window_check_the_unique_loan_refuses() {
    for name in ["WRITE_IN_WINDOW", "READ_IN_WINDOW"] {
        let s = seen_with(name, &[("CRAT_E5C_CM_FAULT", "no-window")]);
        assert_eq!(row(&s, "q", "p"), "eligible-mut", "{name}: {s:#?}");
        assert!(!lent(&s), "{name}: {s:#?}");
    }
}

/// F2 (`no-window` + W52's `no-loan`), an observation of record: even without the window check and
/// without the lend's loan, the replay refuses the read of `p` in `q`'s window, because the copy
/// itself issues an ordinary loan and `p` is mutable (the facts give a copy one qualifier). The
/// read is caught three times: the window check, the unique loan, the copy's own loan. A fault that
/// lets it through would have to remove the base borrow inference; none is built.
#[test]
fn e5c_cm_f2_without_the_window_or_the_lends_loan_the_copys_own_loan_catches_the_read() {
    let s = seen_with(
        "READ_IN_WINDOW",
        &[
            ("CRAT_E5C_CM_FAULT", "no-window"),
            ("CRAT_E5C_W52_FAULT", "no-loan"),
        ],
    );
    assert_eq!(row(&s, "q", "p"), "eligible-mut", "{s:#?}");
    assert!(!lent(&s), "{s:#?}");
}

/// F2′ (`no-window,shared-loan`), an observation of record: a SHARED loan catches the read here
/// too. The mutability facts give a copy one qualifier, so the write through `q` makes `p` mutable,
/// and the replay conflicts a read of `p` with any loan on it. The unique loan is the defense that
/// does not rest on that propagation.
#[test]
fn e5c_cm_f2_a_shared_loan_is_caught_here_too() {
    let s = seen_with(
        "READ_IN_WINDOW",
        &[("CRAT_E5C_CM_FAULT", "no-window,shared-loan")],
    );
    assert_eq!(row(&s, "q", "p"), "eligible-mut", "{s:#?}");
    assert!(!lent(&s), "{s:#?}");
}

/// (iii) the destination released (S2-2), or `free(p)` inside `q`'s window: no lend.
#[test]
fn e5c_cm_3_a_release_refuses_the_lend() {
    let on = seen("FREE_DESTINATION");
    assert_eq!(row(&on, "q", "p"), "s2-2-free-destination", "{on:#?}");
    let on = seen("FREE_IN_WINDOW");
    assert_eq!(row(&on, "q", "p"), "c2-mutable-window-access", "{on:#?}");
}

/// (iii′) the window is `q`'s liveness, path by path: `free(p)` after `q`'s last use is outside it.
#[test]
fn e5c_cm_3_a_release_after_the_last_use_is_outside_the_window() {
    let s = seen("FREE_AFTER_LAST_USE");
    assert_eq!(row(&s, "q", "p"), "eligible-mut", "{s:#?}");
}

/// (iv) a read-only copy: the shared lend, never the mutable one.
#[test]
fn e5c_cm_4_a_read_only_copy_is_unchanged() {
    let on = seen("READ_ONLY");
    assert_eq!(row(&on, "q", "p"), "eligible", "{on:#?}");
    assert!(
        on.rows.iter().all(|r| !r.ends_with("eligible-mut")),
        "{on:#?}"
    );
}
