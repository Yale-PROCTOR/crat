//! R1500-2 / R1502-2: the three instruments' lines, read from a child process's stderr (the phase
//! log and the dump switch are read once per process, and the rewrite runs its compiler on its own
//! thread); the per-round file under `CRAT_BO_CONFLICT_DUMP_DIR` only; the model unchanged.

use std::{ffi::OsString, path::PathBuf};

use serde::{Deserialize, Serialize};

/// 322's cascade beside the source / sink tie: rounds with conflicts and re-solves in both verifies.
const CASCADE_TIE: &str = r#"
unsafe fn id(p: *mut i32) -> *mut i32 { p }
pub unsafe fn f(p: *mut i32) -> i32 { let x = id(p); *x = 1; let b = p; *b = 2; *x }
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
unsafe extern "C" { fn retain_for_policy_fixture(x: *mut core::ffi::c_void); }
pub unsafe fn pass(x: *mut core::ffi::c_void) { retain_for_policy_fixture(x); }
pub unsafe fn source_side() -> *mut core::ffi::c_void {
    let m = unsafe { malloc(4) };
    unsafe { pass(m) };
    m
}
pub unsafe fn sink_side(a: *mut core::ffi::c_void) -> *mut core::ffi::c_void {
    let b = a;
    unsafe { pass(b) };
    unsafe { free(a) };
    b
}
"#;

const CHILD_ROOT: &str = "CRAT_R1500_2_CHILD_ROOT";
const CHILD_OUT: &str = "CRAT_R1500_2_CHILD_OUT";

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ChildResult {
    source: String,
    files: Vec<String>,
    overlap_receipt: String,
    model_sha256: Option<String>,
}

/// In a child: the whole rewrite of `CHILD_ROOT`, its result to `CHILD_OUT`.
fn child() -> bool {
    let Some(root) = std::env::var_os(CHILD_ROOT) else {
        return false;
    };
    let outcome = crate::bo_rewriter::rewrite_m1_path_with_emission_config(
        &PathBuf::from(root),
        crate::analyses::borrow_ownership::param_overlap::OverlapMode::PreciseReplay,
        Some(crate::analyses::borrow_ownership::param_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        &crate::bo_rewriter::EmissionRunConfig::default(),
    );
    let crate::bo_rewriter::RewriteOutcome::Emitted {
        source,
        files,
        overlap_receipt,
        solve_receipt,
        ..
    } = outcome
    else {
        panic!("the fixture emits");
    };
    let result = ChildResult {
        source,
        files: files.into_values().collect(),
        overlap_receipt,
        model_sha256: solve_receipt.map(|receipt| receipt.model_sha256),
    };
    let out = std::env::var_os(CHILD_OUT).expect("child out");
    std::fs::write(out, serde_json::to_vec(&result).unwrap()).unwrap();
    true
}

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("crat-r1500-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Run `test` in a child on a fresh copy of the fixture, with `env`; its result and stderr.
fn spawn(test: &str, tag: &str, env: &[(&str, OsString)]) -> (ChildResult, String) {
    let dir = scratch(tag);
    std::fs::write(dir.join("lib.rs"), CASCADE_TIE).unwrap();
    let out = dir.join("result.json");
    let mut command = std::process::Command::new(std::env::current_exe().unwrap());
    command
        .args([
            test,
            "--exact",
            "--include-ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(CHILD_ROOT, dir.join("lib.rs"))
        .env(CHILD_OUT, &out)
        .env_remove("CRAT_BO_PHASE_LOG")
        .env_remove("CRAT_BO_CONFLICT_DUMP_DIR")
        .env_remove("CRAT_BO_ARTIFACT_DIR")
        .env_remove("CRAT_BO_CHECKPOINT_OUT")
        .env_remove("CRAT_BO_CHECKPOINT_IN")
        .env_remove("CRAT_BO_CACHE_DIR");
    for (name, value) in env {
        command.env(name, value);
    }
    let output = command.output().unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(output.status.success(), "child {tag} failed:\n{stderr}");
    let result = serde_json::from_slice(&std::fs::read(&out).unwrap()).unwrap();
    (result, stderr)
}

fn field<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    line.split(' ')
        .find_map(|token| token.strip_prefix(&format!("{key}=")))
}

fn lines<'a>(stderr: &'a str, phase: &str) -> Vec<&'a str> {
    stderr
        .lines()
        .filter(|line| line.starts_with(&format!("[bo-phase] {phase} end ")))
        .collect()
}

/// With the phase log on and the dump switch set: each replay end writes `verify:conflicts` (the
/// count, the paths when few, the file) and the per-round file holds every path; each commit writes
/// `verify:commit`; each re-solve writes `verify:drift`; both verifies (baseline, precise) write
/// them; and nothing lands in the artifact directory. RED at `88b63584c`: no such line, no file.
#[test]
fn r1500_2_the_three_instruments_write_their_lines_and_the_dump_file() {
    if child() {
        return;
    }
    let test = "analyses::borrow_ownership::round_log::tests::r1500_2_the_three_instruments_write_their_lines_and_the_dump_file";
    let dump = scratch("dump").join("dump");
    let art = scratch("art");
    let (_, stderr) = spawn(
        test,
        "instruments",
        &[
            ("CRAT_BO_PHASE_LOG", OsString::from("on")),
            ("CRAT_BO_CONFLICT_DUMP_DIR", dump.clone().into_os_string()),
            ("CRAT_BO_ARTIFACT_DIR", art.clone().into_os_string()),
        ],
    );
    let conflicts = lines(&stderr, "verify:conflicts");
    let commits = lines(&stderr, "verify:commit");
    let drifts = lines(&stderr, "verify:drift");
    let verifies = conflicts
        .iter()
        .filter_map(|line| field(line, "verify"))
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        verifies.len() >= 2,
        "both verifies: {conflicts:?}\n{stderr}"
    );
    let conflicted = conflicts
        .iter()
        .find(|line| field(line, "count").is_some_and(|count| count != "0"))
        .unwrap_or_else(|| panic!("no replay with a conflict:\n{stderr}"));
    let name = field(conflicted, "file").unwrap();
    assert!(
        name.starts_with(super::CONFLICTS_FILE_PREFIX) && name.ends_with(".tsv"),
        "{conflicted}"
    );
    assert!(
        field(conflicted, "fns")
            .unwrap()
            .split(',')
            .any(|path| path == "f"),
        "{conflicted}"
    );
    let guarded = commits
        .iter()
        .find(|line| field(line, "kind") == Some("guarded"))
        .unwrap_or_else(|| panic!("no guarded commit line:\n{stderr}"));
    assert!(
        field(guarded, "target").is_some_and(|target| target.starts_with("f::_")),
        "{guarded}"
    );
    assert!(
        field(guarded, "issuer").is_some_and(|issuer| issuer.starts_with("f::_")),
        "{guarded}"
    );
    assert!(
        field(guarded, "label")
            .is_some_and(|label| label.starts_with("event=l2_commit|kind=guarded|")),
        "{guarded}"
    );
    let drift = drifts
        .first()
        .unwrap_or_else(|| panic!("no drift line:\n{stderr}"));
    for key in [
        "slots",
        "changed",
        "gone",
        "in_conflict_fns",
        "conflict_fns",
        "top",
    ] {
        assert!(field(drift, key).is_some(), "{key}: {drift}");
    }
    assert!(field(drift, "top").unwrap().starts_with("f:"), "{drift}");
    let written = std::fs::read_dir(&dump)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(written, vec![name.to_owned()], "one file, the child's own");
    let file = std::fs::read_to_string(dump.join(name)).expect("the per-round file");
    let mut rows = file.lines();
    assert_eq!(rows.next(), Some("verify\tround\tfunction"));
    let rows = rows.collect::<Vec<_>>();
    assert!(rows.iter().any(|row| row.ends_with("\tf")), "{file}");
    let total: usize = conflicts
        .iter()
        .filter_map(|line| field(line, "count")?.parse::<usize>().ok())
        .sum();
    assert_eq!(
        rows.len(),
        total,
        "one row per conflict function per replay:\n{file}"
    );
    assert!(
        std::fs::read_dir(&art).unwrap().next().is_none(),
        "nothing in the artifact directory"
    );
}

/// With the phase log on and the dump switch unset: the lines say `file=none`, and no file is
/// written anywhere (the artifact directory set, as the identity runs set it, stays without one).
#[test]
fn r1500_2_without_the_dump_switch_no_file_is_written() {
    if child() {
        return;
    }
    let test = "analyses::borrow_ownership::round_log::tests::r1500_2_without_the_dump_switch_no_file_is_written";
    let art = scratch("art-only");
    let (_, stderr) = spawn(
        test,
        "nodump",
        &[
            ("CRAT_BO_PHASE_LOG", OsString::from("on")),
            ("CRAT_BO_ARTIFACT_DIR", art.clone().into_os_string()),
        ],
    );
    let conflicts = lines(&stderr, "verify:conflicts");
    assert!(!conflicts.is_empty(), "{stderr}");
    assert!(
        conflicts
            .iter()
            .all(|line| field(line, "file") == Some("none")),
        "{conflicts:?}"
    );
    assert!(std::fs::read_dir(&art).unwrap().next().is_none());
}

/// The phase log (and with it the instruments) changes nothing the rewrite decides: on the
/// cascade + tie fixture, the emitted source, files, overlap receipt and model sha are the same with
/// the log on (and the dump set) as with it off, where no instrument line is written.
#[test]
fn r1500_2_the_instruments_change_no_model() {
    if child() {
        return;
    }
    let test =
        "analyses::borrow_ownership::round_log::tests::r1500_2_the_instruments_change_no_model";
    // The dump switch set with the log off: nothing computed, so no file either.
    let quiet_dump = scratch("dump-off");
    let (off, quiet) = spawn(
        test,
        "log-off",
        &[(
            "CRAT_BO_CONFLICT_DUMP_DIR",
            quiet_dump.clone().into_os_string(),
        )],
    );
    assert!(std::fs::read_dir(&quiet_dump).unwrap().next().is_none());
    let (on, loud) = spawn(
        test,
        "log-on",
        &[
            ("CRAT_BO_PHASE_LOG", OsString::from("on")),
            (
                "CRAT_BO_CONFLICT_DUMP_DIR",
                scratch("dump-on").into_os_string(),
            ),
        ],
    );
    assert!(lines(&quiet, "verify:conflicts").is_empty(), "{quiet}");
    assert!(!lines(&loud, "verify:drift").is_empty(), "{loud}");
    assert!(on.model_sha256.is_some());
    assert_eq!(on, off);
}

/// The commit line's bound and the issuer's inverse mapping.
#[test]
fn r1500_2_the_label_is_bounded_and_the_slot_key_inverse_covers_both_variants() {
    use crate::analyses::borrow_ownership::{
        guarded_repair::SlotKey, slots::SlotId, solver::SlotRef,
    };
    let short = "x".repeat(super::LABEL_BYTES);
    assert_eq!(super::bounded(&short), short);
    let long = format!("{}é{}", "y".repeat(super::LABEL_BYTES - 1), "z".repeat(50));
    let cut = super::bounded(&long);
    assert!(
        cut.starts_with(&"y".repeat(super::LABEL_BYTES - 1)),
        "{cut}"
    );
    assert!(cut.ends_with("…(+52 bytes)"), "{cut}");
    let field = SlotRef::Field(SlotId::from_usize(3));
    assert_eq!(super::slot_of_key(SlotKey::of(field)), Some(field));
    let local = SlotRef::Local(
        rustc_span::def_id::LocalDefId {
            local_def_index: rustc_span::def_id::DefIndex::from_u32(7),
        },
        SlotId::from_usize(2),
    );
    assert_eq!(super::slot_of_key(SlotKey::of(local)), Some(local));
    assert_eq!(
        super::slot_of_key(SlotKey {
            variant: 9,
            owner: 0,
            slot: 0
        }),
        None
    );
}

/// The dump switch's reading, and, with the phase log off (the gate's process), nothing computed.
#[test]
fn r1500_2_the_dump_switch_reads_a_path_and_the_log_off_computes_nothing() {
    assert_eq!(super::dump_dir_from(None), None);
    assert_eq!(super::dump_dir_from(Some(OsString::new())), None);
    assert_eq!(
        super::dump_dir_from(Some(OsString::from("/d"))),
        Some(PathBuf::from("/d"))
    );
    if crate::phase_log::on() {
        return;
    }
    assert_eq!(super::begin_verify(), 0);
    let empty: rustc_hash::FxHashMap<rustc_span::def_id::LocalDefId, ()> = Default::default();
    ::utils::compilation::run_compiler_on_str("pub fn g() {}", |tcx| {
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions: Vec::new(),
            structs: Vec::new(),
        };
        assert!(super::conflicts(&program, 0, 1, &empty).is_none());
    })
    .unwrap_or_else(|error| error.raise());
}
