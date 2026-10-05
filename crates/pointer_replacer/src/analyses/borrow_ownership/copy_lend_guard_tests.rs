//! L01¹⁴ (R804-1, era-5c 133): the copy-lend arm lends only an owner the function
//! makes or releases itself, never its caller's value (R536-4).

use rustc_hir::{ItemKind, OwnerNode};

/// Every copy-lend candidate of `code`: `fn  source  copy  drop` (`eligible` when kept).
fn candidates(code: &str) -> Vec<String> {
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
            rows.push(format!(
                "{}\t{:?}\t{:?}\t{}",
                tcx.def_path_str(site.fn_did.to_def_id()),
                site.rhs_local,
                site.lhs_local,
                candidate.drop.map_or("eligible", |drop| drop.label())
            ));
        }
    })
    .expect("compiles");
    rows
}

fn drop_of(rows: &[String], function: &str, source: &str) -> String {
    rows.iter()
        .find(|row| {
            let cols: Vec<_> = row.split('\t').collect();
            cols[0].ends_with(function) && cols[1] == source
        })
        .unwrap_or_else(|| panic!("no candidate {function} {source}: {rows:#?}"))
        .split('\t')
        .nth(3)
        .unwrap()
        .to_string()
}

/// lodepng's sixteen (104a): an entry's formal copied into a local and only read.
/// bzip2's `copy_read` (104 §1): a local allocation copied and read, then released.
/// A formal the function releases itself.
const SHAPES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
extern "C" {
    fn malloc(_: u64) -> *mut core::ffi::c_void;
    fn free(_: *mut core::ffi::c_void);
}
#[no_mangle] pub unsafe extern "C" fn read_formal(mut buf: *const i32) -> i32 {
    let p = buf;
    *p
}
#[no_mangle] pub unsafe extern "C" fn copy_read() -> i32 {
    let buf = malloc(8) as *mut i32;
    let p = buf;
    let r = *p;
    free(buf as *mut core::ffi::c_void);
    r
}
#[no_mangle] pub unsafe extern "C" fn release_formal(mut buf: *mut i32) -> i32 {
    let p = buf;
    let r = *p;
    free(buf as *mut core::ffi::c_void);
    r
}
"#;

#[test]
fn e5c_l14_g1_a_formal_copied_into_a_local_is_not_lent() {
    let rows = candidates(SHAPES);
    assert_eq!(
        drop_of(&rows, "read_formal", "_1"),
        "guard-caller-derived-source",
        "{rows:#?}"
    );
}

#[test]
fn e5c_l14_g2_a_local_allocation_is_still_lent() {
    let rows = candidates(SHAPES);
    let lent: Vec<_> = rows
        .iter()
        .filter(|row| row.starts_with("copy_read") && row.ends_with("eligible"))
        .collect();
    assert!(!lent.is_empty(), "{rows:#?}");
}

#[test]
fn e5c_l14_g3_a_formal_the_function_releases_is_still_lent() {
    let rows = candidates(SHAPES);
    assert_eq!(
        drop_of(&rows, "release_formal", "_1"),
        "eligible",
        "{rows:#?}"
    );
}

#[test]
#[ignore = "child of e5c_l14_g4 (the guard's fault)"]
fn e5c_l14_inner_guard_fault() {
    let rows = candidates(SHAPES);
    println!("E5C_L14_G4 {}", drop_of(&rows, "read_formal", "_1"));
}

/// The fault: without the guard the formal's pair is eligible again.
#[test]
fn e5c_l14_g4_the_guards_fault_is_caught() {
    let exe = std::env::current_exe().expect("current_exe");
    let output = std::process::Command::new(exe)
        .args([
            "analyses::borrow_ownership::copy_lend_guard_tests::e5c_l14_inner_guard_fault",
            "--exact",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env("CRAT_E5C_L14_FAULT", "copy-lend-guard")
        .output()
        .expect("child test");
    let text = String::from_utf8_lossy(&output.stdout);
    assert!(output.status.success(), "{text}");
    assert!(text.contains("E5C_L14_G4 eligible"), "{text}");
}

/// The guarded funnel's S1 over a named program (era-5c 133): every copy-lend
/// candidate with its drop. `CRAT_E5C_SIDE_SOURCE` names the source, the rows go to
/// `CRAT_E5C_SIDE_ROWS`.
#[test]
#[ignore = "the guarded funnel's S1 driver (era-5c 133)"]
fn e5c_l14_guarded_funnel_named_source() {
    let path = std::env::var("CRAT_E5C_SIDE_SOURCE").expect("CRAT_E5C_SIDE_SOURCE");
    let out = std::env::var("CRAT_E5C_SIDE_ROWS").expect("CRAT_E5C_SIDE_ROWS");
    let source = std::fs::read_to_string(&path).expect("source");
    let rows = candidates(&source);
    std::fs::write(&out, rows.join("\n") + "\n").expect("write rows");
    eprintln!("E5C_L14_FUNNEL {path} pairs={}", rows.len());
}

/// era-5c 134: the digest of the system the solve starts from (hard and soft), after
/// the construction, under the copy-lend mode of the environment. Run once with the
/// arm off and once on, each in its own process: equal digests mean the arm leaves
/// the program's constraint system byte-identical.
#[test]
#[ignore = "the construction digest driver (era-5c 134)"]
fn e5c_l14_construction_digest_named_source() {
    use sha2::{Digest, Sha256};
    let path = std::env::var("CRAT_E5C_SIDE_SOURCE").expect("CRAT_E5C_SIDE_SOURCE");
    ::utils::compilation::run_compiler_on_path(std::path::Path::new(&path), |tcx| {
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
        let solver = super::solver::KindSolver::new(&slots);
        let (construction, links) = super::construction::construct_bo_into_a16_refined(
            &program,
            &slots,
            &origins,
            &mutability,
            &solver,
        )
        .expect("construction");
        let text = solver.system_text();
        let digest = Sha256::digest(text.as_bytes());
        let hex: String = digest.iter().map(|b| format!("{b:02x}")).collect();
        println!(
            "E5C_L14_DIGEST mode={} eligible={} links={links} bytes={} sha256={hex}",
            construction.mode.label(),
            construction.eligibility.pairs.len(),
            text.len()
        );
    })
    .expect("compiles");
}
