//! era-5c relays 215/216 (R1022-1, R1024-1, USER): the objective's order Ref > Owning > Raw
//! (`CRAT_ERA5C_KIND_ORDER=ref-own-raw`: `own` at 1 in place of the raw term). Each witness runs the
//! full solve of a fixture in a child under the frame of record's env (`frames/l01p14u-s39-env.sh`
//! + `CRAT_ERA5C_COPY_LEND_MUT=on`, 59m) with the switch as named, and reads the settled kinds by name.

use std::collections::BTreeMap;

const FRAME_ENV: &str = include_str!("../../../frames/l01p14u-s39-env.sh");

const LIBC: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types)]
extern "C" {
    fn malloc(_: u64) -> *mut core::ffi::c_void;
    fn free(_: *mut core::ffi::c_void);
}
"#;

/// An allocation never released (a leak; R534's leak-parity waiver lets a Box drop it).
const LEAKED: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    *p = 1;
    *p
}
"#;

/// An allocation released by a local callee that frees its formal.
const RELEASED_BY_CALLEE: &str = r#"
unsafe fn release(q: *mut i32) {
    free(q as *mut core::ffi::c_void);
}
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    *p = 1;
    let r = *p;
    release(p);
    r
}
"#;

/// An allocation stored through an out-parameter.
const OUT_PARAM: &str = r#"
#[no_mangle] pub unsafe extern "C" fn make(out: *mut *mut i32) {
    let p: *mut i32 = malloc(4) as *mut i32;
    *p = 0;
    *out = p;
}
"#;

/// An allocation returned.
const RETURNED: &str = r#"
#[no_mangle] pub unsafe extern "C" fn make() -> *mut i32 {
    let p: *mut i32 = malloc(4) as *mut i32;
    *p = 0;
    p
}
"#;

/// An allocation stepped through with arithmetic, then released.
const CURSOR_FREED: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let p: *mut i32 = malloc(16) as *mut i32;
    let mut c: *mut i32 = p;
    *c = 1;
    c = c.offset(1);
    *c = 2;
    let r = *p;
    free(p as *mut core::ffi::c_void);
    r
}
"#;

/// (b) a reference the replay admits: a pointer to a local, written through.
const STACK_REF: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let mut x: i32 = 0;
    let p: *mut i32 = &mut x;
    *p = 3;
    x
}
"#;

/// (c) a raw pointer to a stack array, stepped with arithmetic: no allocation to own.
const STACK_CURSOR: &str = r#"
#[no_mangle] pub unsafe extern "C" fn run() -> i32 {
    let mut a: [i32; 4] = [0; 4];
    let mut c: *mut i32 = a.as_mut_ptr();
    c = c.offset(1);
    *c = 2;
    a[1]
}
"#;

/// An allocation bound to a named local, then stored into a field the program releases.
const FIELD_STORE_RELEASED: &str = r#"
#[repr(C)] pub struct T { pub e: *mut i32 }
#[no_mangle] pub unsafe extern "C" fn make() -> *mut T {
    let t: *mut T = malloc(8) as *mut T;
    let e: *mut i32 = malloc(16) as *mut i32;
    (*t).e = e;
    t
}
#[no_mangle] pub unsafe extern "C" fn destroy(t: *mut T) {
    free((*t).e as *mut core::ffi::c_void);
    free(t as *mut core::ffi::c_void);
}
"#;

/// The same, with nothing in the program releasing the field.
const FIELD_STORE_UNRELEASED: &str = r#"
#[repr(C)] pub struct T { pub e: *mut i32 }
#[no_mangle] pub unsafe extern "C" fn make() -> *mut T {
    let t: *mut T = malloc(8) as *mut T;
    let e: *mut i32 = malloc(16) as *mut i32;
    (*t).e = e;
    t
}
"#;

/// ht_create's shape: the field's allocation stored straight from the call (a temporary).
const FIELD_STORE_DIRECT: &str = r#"
#[repr(C)] pub struct T { pub e: *mut i32 }
#[no_mangle] pub unsafe extern "C" fn make() -> *mut T {
    let t: *mut T = malloc(8) as *mut T;
    (*t).e = malloc(16) as *mut i32;
    t
}
#[no_mangle] pub unsafe extern "C" fn destroy(t: *mut T) {
    free((*t).e as *mut core::ffi::c_void);
    free(t as *mut core::ffi::c_void);
}
"#;

/// (a) quadtree's test `main_0` reduced: a pointer formal of an internal function whose only caller
/// passes a `Vec`'s `as_mut_ptr()` (a raw origin: its reference is refused) and which nothing
/// releases or constrains further: its `own` is SAT, so it settles Raw under `ref-raw` and Owning
/// under `ref-own-raw`.
const MAIN_ARGV: &str = r#"
unsafe fn main_0(argc: i32, argv: *mut *const i8) -> i32 {
    argc
}
pub fn main() {
    let mut args: Vec<*mut i8> = Vec::new();
    for arg in ::std::env::args() {
        args.push(::std::ffi::CString::new(arg).unwrap().into_raw());
    }
    args.push(::core::ptr::null_mut());
    unsafe {
        ::std::process::exit(main_0((args.len() - 1) as i32, args.as_mut_ptr() as *mut *const i8) as i32)
    }
}
"#;

/// MAIN_ARGV with its temporaries named: the string `into_raw` gives up, and the vector's buffer.
const MAIN_ARGV_NAMED: &str = r#"
unsafe fn main_0(argc: i32, argv: *mut *const i8) -> i32 {
    argc
}
pub fn main() {
    let mut args: Vec<*mut i8> = Vec::new();
    for arg in ::std::env::args() {
        let raw: *mut i8 = ::std::ffi::CString::new(arg).unwrap().into_raw();
        args.push(raw);
    }
    args.push(::core::ptr::null_mut());
    let buffer: *mut *mut i8 = args.as_mut_ptr();
    unsafe { ::std::process::exit(main_0((args.len() - 1) as i32, buffer as *mut *const i8) as i32) }
}
"#;

const SHAPES: [(&str, &str); 12] = [
    ("MAIN_ARGV_NAMED", MAIN_ARGV_NAMED),
    ("MAIN_ARGV", MAIN_ARGV),
    ("FIELD_STORE_RELEASED", FIELD_STORE_RELEASED),
    ("FIELD_STORE_UNRELEASED", FIELD_STORE_UNRELEASED),
    ("FIELD_STORE_DIRECT", FIELD_STORE_DIRECT),
    ("LEAKED", LEAKED),
    ("RELEASED_BY_CALLEE", RELEASED_BY_CALLEE),
    ("OUT_PARAM", OUT_PARAM),
    ("RETURNED", RETURNED),
    ("CURSOR_FREED", CURSOR_FREED),
    ("STACK_REF", STACK_REF),
    ("STACK_CURSOR", STACK_CURSOR),
];

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

#[test]
#[ignore = "runs under the frame's arms in a child of the e5c_ko witnesses"]
fn e5c_inner_kind_order() {
    let name = std::env::var("CRAT_E5C_KO_SHAPE").expect("CRAT_E5C_KO_SHAPE");
    let body = SHAPES
        .iter()
        .find(|(shape, _)| *shape == name)
        .unwrap_or_else(|| panic!("unknown shape {name}"))
        .1;
    for (key, kind) in super::copy_relax_tests::kinds(&format!("{LIBC}{body}")) {
        println!("E5C_KO {key} {kind}");
    }
}

/// The shape's settled kinds with the switch as given (`None` = absent).
fn kinds(shape: &str, order: Option<&str>) -> BTreeMap<String, String> {
    let exe = std::env::current_exe().expect("current_exe");
    let mut command = std::process::Command::new(exe);
    command.args([
        "analyses::borrow_ownership::kind_order_tests::e5c_inner_kind_order",
        "--exact",
        "--ignored",
        "--nocapture",
        "--test-threads=1",
    ]);
    for (key, value) in frame_arms() {
        command.env(key, value);
    }
    command.env("CRAT_E5C_KO_SHAPE", shape);
    match order {
        Some(value) => command.env("CRAT_ERA5C_KIND_ORDER", value),
        None => command.env_remove("CRAT_ERA5C_KIND_ORDER"),
    };
    let output = command.output().expect("child test");
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "child {shape} failed:\n{text}");
    let rows: BTreeMap<String, String> = text
        .lines()
        .filter_map(|l| l.split_once("E5C_KO ").map(|(_, rest)| rest))
        .filter_map(|l| l.rsplit_once(' '))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect();
    eprintln!("E5C_KO_ROWS {shape} order={order:?} {rows:?}");
    rows
}

/// Every shape under both orders (an observation; run with --ignored --nocapture).
#[test]
#[ignore = "an observation: every shape's kinds under ref-raw and ref-own-raw"]
fn e5c_ko_observe_every_shape() {
    for (shape, _) in SHAPES {
        let before = kinds(shape, None);
        let after = kinds(shape, Some("ref-own-raw"));
        println!("E5C_KO_OBSERVE {shape}\n  ref-raw     {before:?}\n  ref-own-raw {after:?}");
    }
}

/// Every slot's settled kind for a corpus program (`CRAT_E5C_KO_PATH=<lib.rs>`), under the switch as
/// the environment gives it: `fn::_local@d<depth>` / `Struct::field@d<depth>` and the kind. An
/// observation for choosing fixtures (run with --ignored --nocapture).
#[test]
#[ignore = "an observation: one program's whole model"]
fn e5c_ko_observe_program() {
    use rustc_hir::{ItemKind, OwnerNode};
    let source = match std::env::var("CRAT_E5C_KO_SHAPE") {
        Ok(name) => format!(
            "{LIBC}{}",
            SHAPES
                .iter()
                .find(|(shape, _)| *shape == name)
                .unwrap_or_else(|| panic!("unknown shape {name}"))
                .1
        ),
        Err(_) => {
            std::fs::read_to_string(std::env::var("CRAT_E5C_KO_PATH").expect("CRAT_E5C_KO_PATH"))
                .expect("read")
        }
    };
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
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
        let verified = super::construction::solve_bo_a5_config(
            &program,
            &slots,
            &origins,
            &mutability,
            super::a5_overlap::A5Mode::PreciseReplay,
            Some(super::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        )
        .expect("the program solves");
        let mut rows: Vec<String> = verified
            .model
            .iter()
            .map(|(slot, kind)| {
                let name = match slot {
                    super::SlotRef::Local(function, id) => {
                        let s = slots.fn_local_slots[function].slot(*id);
                        let super::slots::SlotOwner::Local(local) = s.owner else { unreachable!() };
                        let body = tcx
                            .mir_drops_elaborated_and_const_checked(*function)
                            .borrow();
                        let named = body
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
                            .unwrap_or_else(|| format!("_{}", local.as_usize()));
                        format!(
                            "{}::{named}@d{}",
                            tcx.def_path_str(function.to_def_id()),
                            s.depth
                        )
                    }
                    other => format!("{other:?}"),
                };
                format!("E5C_KO_SLOT {name} {kind:?}")
            })
            .collect();
        rows.sort();
        for row in rows {
            println!("{row}");
        }
    })
    .expect("compiles");
}

/// The shape's whole model (`fn::local@d<depth>` -> kind) with the switch as given (`None` = absent),
/// from a child running `e5c_ko_observe_program`.
fn model(shape: &str, order: Option<&str>) -> BTreeMap<String, String> {
    let exe = std::env::current_exe().expect("current_exe");
    let mut command = std::process::Command::new(exe);
    command.args([
        "analyses::borrow_ownership::kind_order_tests::e5c_ko_observe_program",
        "--exact",
        "--ignored",
        "--nocapture",
        "--test-threads=1",
    ]);
    for (key, value) in frame_arms() {
        command.env(key, value);
    }
    command.env("CRAT_E5C_KO_SHAPE", shape);
    match order {
        Some(value) => command.env("CRAT_ERA5C_KIND_ORDER", value),
        None => command.env_remove("CRAT_ERA5C_KIND_ORDER"),
    };
    let output = command.output().expect("child test");
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "child {shape} failed:\n{text}");
    text.lines()
        .filter_map(|l| l.split_once("E5C_KO_SLOT ").map(|(_, rest)| rest))
        .filter_map(|l| l.rsplit_once(' '))
        .map(|(k, v)| (k.to_owned(), v.trim().to_owned()))
        .collect()
}

/// The slots whose kind differs between two models: `slot -> (before, after)`.
fn moved(
    before: &BTreeMap<String, String>,
    after: &BTreeMap<String, String>,
) -> BTreeMap<String, (String, String)> {
    before
        .iter()
        .filter_map(|(slot, kind)| {
            let other = after.get(slot).cloned().unwrap_or_default();
            (other != *kind).then(|| (slot.clone(), (kind.clone(), other)))
        })
        .collect()
}

/// (a) Slots whose reference is refused and whose `own` is SAT settle Raw under `ref-raw` and
/// Owning under `ref-own-raw` (quadtree's test `main`, reduced: the vector's and the strings'
/// temporaries), and nothing else moves.
#[test]
fn e5c_ko_a_a_refused_reference_whose_own_is_free_settles_owning() {
    let before = model("MAIN_ARGV", None);
    let after = model("MAIN_ARGV", Some("ref-own-raw"));
    let moves = moved(&before, &after);
    assert!(!moves.is_empty(), "nothing moved: {before:#?}");
    for (slot, (from, to)) in &moves {
        assert_eq!(
            (from.as_str(), to.as_str()),
            ("Raw", "Owning"),
            "{slot}: {moves:#?}"
        );
    }
}

/// (b) A reference is never displaced: every slot Ref under `ref-raw` is Ref under `ref-own-raw`,
/// on every shape.
#[test]
fn e5c_ko_b_a_reference_stays_a_reference() {
    for (shape, _) in SHAPES {
        let before = model(shape, None);
        let after = model(shape, Some("ref-own-raw"));
        for (slot, kind) in before.iter().filter(|(_, kind)| kind.as_str() == "Ref") {
            assert_eq!(after.get(slot), Some(kind), "{shape} {slot}");
        }
    }
    assert_eq!(
        model("STACK_REF", Some("ref-own-raw"))
            .get("run::p@d0")
            .map(String::as_str),
        Some("Ref")
    );
}

/// (c) A slot whose `own` is UNSAT stays Raw: a leaked local under Exit.
#[test]
fn e5c_ko_c_an_unsat_own_stays_raw() {
    let after = model("LEAKED", Some("ref-own-raw"));
    assert_eq!(
        after.get("run::p@d0").map(String::as_str),
        Some("Raw"),
        "{after:#?}"
    );
}

/// (d) The identity names the order (its three weights) only when set to `ref-own-raw`; `ref-raw`
/// and absence are the frame's identity; an unknown value fails loud.
#[test]
fn e5c_ko_d_the_identity_names_the_order() {
    let exe = std::env::current_exe().expect("current_exe");
    let identity = |value: Option<&str>| {
        let mut command = std::process::Command::new(&exe);
        command.args([
            "analyses::borrow_ownership::copy_relax_tests::e5c_inner_identity",
            "--exact",
            "--ignored",
            "--nocapture",
        ]);
        match value {
            Some(value) => command.env("CRAT_ERA5C_KIND_ORDER", value),
            None => command.env_remove("CRAT_ERA5C_KIND_ORDER"),
        };
        let output = command.output().expect("child");
        let text = format!(
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        (output.status.success(), text)
    };
    let line = "era5c_kind_order=ref-own-raw(ref=slots+1,own=1,raw=0)";
    let fields = |text: &str| -> Vec<String> {
        text.lines()
            .filter(|l| l.contains('=') && !l.starts_with("test ") && !l.starts_with("running"))
            .map(str::to_owned)
            .collect()
    };
    let (ok, absent) = identity(None);
    assert!(ok && !absent.contains("era5c_kind_order"), "{absent}");
    let (ok, frame) = identity(Some("ref-raw"));
    assert!(ok && fields(&frame) == fields(&absent), "{frame}");
    let (ok, set) = identity(Some("ref-own-raw"));
    assert!(ok && set.contains(line), "{set}");
    let (ok, bogus) = identity(Some("own-ref-raw"));
    assert!(!ok && bogus.contains("CRAT_ERA5C_KIND_ORDER"), "{bogus}");
}
