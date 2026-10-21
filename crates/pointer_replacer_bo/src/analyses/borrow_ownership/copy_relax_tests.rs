//! The depth-0 Copy relaxation and the merge liveness. Each witness runs the full solve of a
//! fixture (the joint pass, borrow verification, retirement, the relax loop) in a child under the
//! switches of the pinned env file and reads the settled kinds by name.

use std::collections::BTreeMap;

const FRAME_ENV: &str = include_str!("../../../frames/l01p14u-env.sh");

/// The pinned switches: every `CRAT_` export of the env file but the raw-cause sidecar and
/// the launch identity (`CRAT_ERA5_*`), which a fixture solve does not take.
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

/// (1) `q` is raw for a reason that does not involve `p`'s loans (it is a cast's source), its value
/// never leaves the function, and nothing invalidates a loan `p`'s origin carries while `q` lives:
/// the relaxation keeps `p` a reference.
const CASTCOPY: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let mut x: i32 = 0;
    let p: *mut i32 = &mut x;
    *p = 3;
    let q: *mut i32 = p;
    let r: *mut u8 = q as *mut u8;
    *r = 1;
    *p += 1;
    return x;
}
"#;

/// (2) The referent is written between two uses of the raw copy: under Tree Borrows `q` carries
/// `p`'s tag, which the write to `x` disables. The liveness rule must make `p` raw.
const WRITE_BETWEEN: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let mut x: i32 = 0;
    let p: *mut i32 = &mut x;
    *p = 3;
    let q: *mut i32 = p;
    let r: *mut u8 = q as *mut u8;
    *r = 1;
    x = 5;
    let s: *mut u8 = q as *mut u8;
    *s = 2;
    return x;
}
"#;

/// The raw copy escapes as a return.
const ESCAPE_RETURN: &str = r#"
unsafe fn get(p: *mut i32) -> *mut i32 {
    *p = 1;
    let q: *mut i32 = p;
    let r: *mut u8 = q as *mut u8;
    *r = 2;
    return q;
}
#[no_mangle] pub unsafe extern "C" fn run() -> i32 { let mut x: i32 = 0; let y = get(&mut x); *y = 3; return x; }
"#;

/// The copy is the return itself (`_0 = p`, as in a routine that returns its output parameter).
const RETURN_DIRECT: &str = r#"
unsafe fn out(p: *mut i32, q: *mut i32) -> *mut i32 {
    *p = *q + 1;
    return p;
}
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let mut x: i32 = 0; let mut z: i32 = 2;
    let y = out(&mut x, &mut z);
    let w = y as *mut u8; *w = 3;
    return x;
}
"#;

/// The raw copy escapes into a call.
const ESCAPE_CALL: &str = r#"
unsafe extern "C" { fn keep(p: *mut i32); }
unsafe fn give(p: *mut i32) {
    *p = 1;
    let q: *mut i32 = p;
    let r: *mut u8 = q as *mut u8;
    *r = 2;
    keep(q);
}
#[no_mangle] pub unsafe extern "C" fn run() -> i32 { let mut x: i32 = 0; give(&mut x); return x; }
"#;

/// The raw copy escapes into a field.
const ESCAPE_FIELD: &str = r#"
#[repr(C)] pub struct S { pub f: *mut i32, pub n: i32 }
unsafe fn put(s: *mut S, p: *mut i32) {
    *p = 1;
    let q: *mut i32 = p;
    let r: *mut u8 = q as *mut u8;
    *r = 2;
    (*s).f = q;
}
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let mut x: i32 = 0; let mut s = S { f: 0 as *mut i32, n: 0 }; put(&mut s, &mut x); return x;
}
"#;

/// (3) An Owning source stays equal: `p` is freed, so it cannot be a reference, and the raw copy
/// keeps it raw (no Owning source beside a Raw copy).
const OWNING: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); fn sink(p: *mut i32); }
#[no_mangle] pub unsafe extern "C" fn run() {
    let p: *mut i32 = malloc(4);
    *p = 1;
    let q: *mut i32 = p;
    sink(q);
    free(p);
}
"#;

/// (4) A cast (Copy's equality does not apply), the referent written
/// between the view's uses. The merge liveness alone must make `p` raw.
const CAST: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let mut x: i32 = 0;
    let p: *mut i32 = &mut x;
    *p = 3;
    let q: *mut u8 = p as *mut u8;
    *q = 1;
    x = 5;
    *q = 2;
    return x;
}
"#;

/// (4′) The control: the view is not used after the write, so `p` stays a reference.
const CAST_DEAD: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let mut x: i32 = 0;
    let p: *mut i32 = &mut x;
    *p = 3;
    let q: *mut u8 = p as *mut u8;
    *q = 1;
    x = 5;
    return x;
}
"#;

/// The settled kinds of a fixture's solve, by name: `fn::local` for a named local at depth 0.
pub(super) fn kinds(code: &str) -> BTreeMap<String, String> {
    use rustc_hir::{ItemKind, OwnerNode};
    let mut rows = BTreeMap::new();
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
        let verified = super::construction::solve_bo_overlap_config(
            &program,
            &slots,
            &origins,
            &mutability,
            super::param_overlap::OverlapMode::PreciseReplay,
            Some(super::param_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        )
        .expect("the fixture solves");
        for (slot, kind) in &verified.model {
            let super::SlotRef::Local(function, id) = slot else { continue };
            let s = slots.fn_local_slots[function].slot(*id);
            let super::slots::SlotOwner::Local(local) = s.owner else { unreachable!() };
            if s.depth != 0 {
                continue;
            }
            let body = tcx
                .mir_drops_elaborated_and_const_checked(*function)
                .borrow();
            let Some(name) = body
                .var_debug_info
                .iter()
                .find_map(|info| match info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place)
                        if place.local == local && place.projection.is_empty() =>
                    {
                        Some(info.name.to_string())
                    }
                    _ => None,
                })
            else {
                continue;
            };
            let key = format!("{}::{name}", tcx.item_name(function.to_def_id()));
            rows.insert(key, format!("{kind:?}").to_lowercase());
        }
    })
    .expect("the fixture compiles");
    rows
}

#[test]
#[ignore = "runs in a child of the e5c_cr witnesses"]
fn e5c_inner_copy_relax() {
    let code = match std::env::var("CRAT_E5C_CR_SHAPE").as_deref() {
        Ok("CASTCOPY") => CASTCOPY,
        Ok("WRITE_BETWEEN") => WRITE_BETWEEN,
        Ok("ESCAPE_RETURN") => ESCAPE_RETURN,
        Ok("ESCAPE_CALL") => ESCAPE_CALL,
        Ok("ESCAPE_FIELD") => ESCAPE_FIELD,
        Ok("RETURN_DIRECT") => RETURN_DIRECT,
        Ok("OWNING") => OWNING,
        Ok("CAST") => CAST,
        Ok("CAST_DEAD") => CAST_DEAD,
        other => panic!("unknown shape {other:?}"),
    };
    for (key, kind) in kinds(code) {
        println!("E5C_CR {key} {kind}");
    }
}

/// The shape's kinds under the pinned switches.
fn rows(shape: &str) -> BTreeMap<String, String> {
    let exe = std::env::current_exe().expect("current_exe");
    let mut command = std::process::Command::new(exe);
    command.args([
        "analyses::borrow_ownership::copy_relax_tests::e5c_inner_copy_relax",
        "--exact",
        "--ignored",
        "--nocapture",
        "--test-threads=1",
    ]);
    for (key, value) in frame_arms() {
        command.env(key, value);
    }
    command.env("CRAT_E5C_CR_SHAPE", shape);
    let output = command.output().expect("child test");
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "child {shape} failed:\n{text}");
    let rows: BTreeMap<String, String> = text
        .lines()
        .filter_map(|l| l.split_once("E5C_CR ").map(|(_, rest)| rest))
        .filter_map(|l| l.rsplit_once(' '))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect();
    eprintln!("E5C_CR_ROWS {shape} {rows:?}");
    rows
}

fn kind<'a>(rows: &'a BTreeMap<String, String>, key: &str) -> &'a str {
    rows.get(key)
        .map(String::as_str)
        .unwrap_or_else(|| panic!("no {key}: {rows:#?}"))
}

/// (1) With the relaxation, the liveness rule and the mutable copy-lend, `p` settles raw beside
/// its raw copy.
#[test]
fn e5c_cr_1_a_raw_copy_beside_the_mutable_lend_leaves_its_source_raw() {
    let r = rows("CASTCOPY");
    assert_eq!(kind(&r, "run::p"), "raw", "{r:#?}");
    assert_eq!(kind(&r, "run::q"), "raw", "{r:#?}");
}

/// (2) The referent written between the copy's uses: with the liveness rule `p` is not a
/// reference.
#[test]
fn e5c_cr_2_a_write_between_the_copys_uses_demotes_the_source() {
    let r = rows("WRITE_BETWEEN");
    assert_ne!(kind(&r, "run::p"), "ref", "{r:#?}");
}

/// A raw copy that escapes (a return, a call, a field) is not relaxed: its source stays
/// equal to it.
#[test]
fn e5c_cr_b_an_escaping_copy_is_not_relaxed() {
    for (shape, function) in [
        ("ESCAPE_RETURN", "get"),
        ("ESCAPE_CALL", "give"),
        ("ESCAPE_FIELD", "put"),
    ] {
        let r = rows(shape);
        assert_eq!(
            kind(&r, &format!("{function}::p")),
            kind(&r, &format!("{function}::q")),
            "{shape}: {r:#?}"
        );
    }
}

/// (3) An Owning source stays equal: never Owning beside a Raw copy, never a reference.
#[test]
fn e5c_cr_3_an_owning_source_stays_equal() {
    let r = rows("OWNING");
    assert_eq!(kind(&r, "run::q"), "raw", "{r:#?}");
    assert_eq!(kind(&r, "run::p"), "raw", "{r:#?}");
}

/// (4) The cast shape: without the liveness rule `p` is raw (the cast's source) and `q` a
/// reference over it, though `x` is written between `q`'s uses. The liveness rule alone makes `q`
/// raw.
#[test]
fn e5c_cr_4_the_cast_view_used_after_a_write_is_not_a_reference() {
    let r = rows("CAST");
    assert_ne!(kind(&r, "run::q"), "ref", "{r:#?}");
}

/// (4′) The control: the view not used after the write stays a reference under the rule.
#[test]
fn e5c_cr_4_control_a_dead_view_stays_a_reference() {
    let r = rows("CAST_DEAD");
    assert_eq!(kind(&r, "run::q"), "ref", "{r:#?}");
}
