//! **R611-2 (relay 094): the census-side conformance checkers, one test per
//! condition.** Each test runs its checker (`docs/agents/tools/conformance/`)
//! over a small fixture laid out like a census directory, clean and then with
//! the one deliberate fault the checker exists to catch. The checkers read
//! census exports only; they never call into this crate.
//!
//! Where the worktree has no `docs/` (the checkers live in the docs
//! repository), each test is a typed skip, the rule R538-3(v) set for tests
//! that read docs paths.
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

fn tool(name: &str) -> Option<PathBuf> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../docs/agents/tools/conformance")
        .join(name);
    path.exists().then_some(path)
}

fn scratch(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("crat-conformance-{tag}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// Runs the checker and returns its receipt line for `program`.
fn receipt(script: &Path, args: &[&Path], program: &str) -> String {
    let output = Command::new("python3")
        .arg(script)
        .args(args)
        .output()
        .expect("python3 runs the checker");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    stdout
        .lines()
        .find(|line| line.contains(&format!(" program={program} ")))
        .unwrap_or_else(|| {
            panic!(
                "no receipt for {program}:\n{stdout}\n{}",
                String::from_utf8_lossy(&output.stderr)
            )
        })
        .to_owned()
}

fn field<'a>(line: &'a str, key: &str) -> &'a str {
    line.split(' ')
        .find_map(|kv| kv.strip_prefix(&format!("{key}=")))
        .unwrap_or_else(|| panic!("no {key} in {line}"))
}

const FRAME: &str = "analysis_frame";

/// **FactFidelity — consumed ≡ accepted.** The fault: one row of the consumed
/// table disagrees with the sealed model.
#[test]
fn conformance_fact_fidelity_catches_a_mutated_consumed_row() {
    let Some(script) = tool("c1_fact_fidelity.py") else {
        println!("SKIP conformance_fact_fidelity: docs/agents/tools/conformance absent");
        return;
    };
    let dir = scratch("c1");
    let (census, cache) = (dir.join("census"), dir.join("cache"));
    fs::create_dir_all(&census).unwrap();
    fs::create_dir_all(&cache).unwrap();
    fs::write(
        cache.join("fp0.json"),
        r#"{"schema":"era5b-model-cache-v1","universe":["m::f::_1@d0","m::f::_2@d0","m::f::_2@d1"],"model":{"m::f::_1@d0":"ref","m::f::_2@d0":"owning","m::f::_2@d1":"raw"},"exports":{}}"#,
    )
    .unwrap();
    let manifest = dir.join("manifest.tsv");
    fs::write(&manifest, "program\tfingerprint\tentry_sha256\np\tfp0\t-\n").unwrap();
    let subjects = |second: &str| {
        format!(
            "{FRAME}\tsubject_key\towner_fn\tmir_local\tptr_depth\tmodel_kind\n\
             L\tm::f::a#1\tm::f\t1\t1\tref\n\
             L\tm::f::b#2\tm::f\t2\t2\t{second}\n"
        )
    };
    let path = census.join("p.raw-boundary-subjects.tsv");
    fs::write(&path, subjects("owning")).unwrap();
    let clean = receipt(&script, &[&census, &cache, &manifest], "p");
    assert_eq!(field(&clean, "subjects"), "2", "{clean}");
    assert_eq!(field(&clean, "mismatches"), "0", "{clean}");
    fs::write(&path, subjects("ref")).unwrap();
    let faulted = receipt(&script, &[&census, &cache, &manifest], "p");
    assert_eq!(field(&faulted, "mismatches"), "1", "{faulted}");
    fs::remove_dir_all(dir).unwrap();
}

/// **RetainedLifecycle — free sites = release sites.** The fault: the emitted
/// tree drops the release the source makes.
#[test]
fn conformance_retained_lifecycle_catches_a_dropped_release() {
    let Some(script) = tool("c2_retained_lifecycle.py") else {
        println!("SKIP conformance_retained_lifecycle: docs/agents/tools/conformance absent");
        return;
    };
    let dir = scratch("c2");
    let (census, substrate) = (dir.join("census"), dir.join("substrate"));
    fs::create_dir_all(census.join("emitted-trees/p")).unwrap();
    fs::create_dir_all(substrate.join("p")).unwrap();
    fs::write(
        substrate.join("p/lib.rs"),
        "extern \"C\" { fn free(_: *mut u8); }\n\
         unsafe fn f(p: *mut u8) { let s = \"free(x)\"; free(p); }\n",
    )
    .unwrap();
    let emitted = census.join("emitted-trees/p/lib.rs");
    fs::write(
        &emitted,
        "extern \"C\" { fn free(_: *mut u8); }\n\
         unsafe fn f(p: *mut u8) { let s = \"free(x)\"; free(p); }\n",
    )
    .unwrap();
    let clean = receipt(&script, &[&census, &substrate], "p");
    assert_eq!(
        (
            field(&clean, "matched"),
            field(&clean, "unmatched_source"),
            field(&clean, "extra_emitted")
        ),
        ("1", "0", "0"),
        "the literal `free(x)` is not a site: {clean}"
    );
    fs::write(
        &emitted,
        "extern \"C\" { fn free(_: *mut u8); }\n\
         unsafe fn f(p: *mut u8) { let s = \"free(x)\"; }\n",
    )
    .unwrap();
    let faulted = receipt(&script, &[&census, &substrate], "p");
    assert_eq!(field(&faulted, "unmatched_source"), "1", "{faulted}");
    fs::remove_dir_all(dir).unwrap();
}

/// **FormConformance — the form classifier.** The fault: a delivered subject
/// whose form maps to no elaboration row.
#[test]
fn conformance_form_conformance_catches_an_unmapped_form() {
    let Some(script) = tool("c3_form_conformance.py") else {
        println!("SKIP conformance_form_conformance: docs/agents/tools/conformance absent");
        return;
    };
    let dir = scratch("c3");
    let path = dir.join("p.raw-boundary-subject-outcomes.tsv");
    let rows = |form: &str| {
        format!(
            "{FRAME}\tsubject_key\tfamily\tdelivery\temitted_form\n\
             L\ta\tref\trealized-as-predicted\tref\n\
             L\tb\toptional\trealized-as-predicted\t{form}\n\
             L\tc\traw\tdegraded\tunchanged\n"
        )
    };
    fs::write(&path, rows("optional")).unwrap();
    let clean = receipt(&script, &[&dir], "p");
    assert_eq!(
        (field(&clean, "delivered"), field(&clean, "unclassified")),
        ("2", "0"),
        "{clean}"
    );
    fs::write(&path, rows("mystery")).unwrap();
    let faulted = receipt(&script, &[&dir], "p");
    assert_eq!(
        (
            field(&faulted, "unclassified"),
            field(&faulted, "unmapped_forms")
        ),
        ("1", "mystery"),
        "{faulted}"
    );
    fs::remove_dir_all(dir).unwrap();
}

/// **CoreCoverage — the vocabulary closure.** The fault: a construct with no
/// core route.
#[test]
fn conformance_core_coverage_catches_a_foreign_construct() {
    let Some(script) = tool("c4_core_coverage.py") else {
        println!("SKIP conformance_core_coverage: docs/agents/tools/conformance absent");
        return;
    };
    let dir = scratch("c4");
    fs::create_dir_all(dir.join("emitted-trees/p")).unwrap();
    let emitted = dir.join("emitted-trees/p/lib.rs");
    let core = "unsafe fn f(p: *mut u8, q: Option<&u8>) -> u8 {\n\
                    if p.is_null() || q.is_none() { return 0; }\n\
                    let r: &u8 = &*p;\n\
                    *r + *q.unwrap()\n\
                }\n";
    fs::write(&emitted, core).unwrap();
    let clean = receipt(&script, &[&dir], "p");
    assert_eq!(field(&clean, "outside"), "0", "{clean}");
    fs::write(
        &emitted,
        format!("{core}unsafe fn g(p: *const u8, q: *const u8) -> isize {{ p.offset_from(q) }}\n"),
    )
    .unwrap();
    let faulted = receipt(&script, &[&dir], "p");
    assert_eq!(
        (field(&faulted, "outside"), field(&faulted, "outside_kinds")),
        ("1", "ptr-offset-from:1"),
        "{faulted}"
    );
    fs::remove_dir_all(dir).unwrap();
}

/// **RetainedLifecycle over MIR (C2b, R615-1) — implicit releases.** A Box
/// owner live at an early return is released by its scope-exit drop, which no
/// syntax shows. With the census's `waiver-drop(scope-exit)` receipt for the
/// function the release is receipted; the fault removes the receipt.
#[test]
fn conformance_retained_lifecycle_catches_an_unreceipted_implicit_release() {
    let Some(script) = tool("c2b_implicit_release.py") else {
        println!("SKIP conformance_retained_lifecycle (C2b): docs/agents/tools/conformance absent");
        return;
    };
    let deps = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../deps_crate/target/debug/deps");
    if !deps.exists() {
        println!("SKIP conformance_retained_lifecycle (C2b): deps_crate not built");
        return;
    }
    let dir = scratch("c2b");
    let (census, out) = (dir.join("census"), dir.join("mir"));
    fs::create_dir_all(census.join("emitted-trees/p")).unwrap();
    fs::write(
        census.join("emitted-trees/p/lib.rs"),
        "pub unsafe fn f(flag: i32) -> i32 {\n\
             let b: Option<Box<i32>> = Some(Box::new(1));\n\
             if flag != 0 {\n\
                 return 0;\n\
             }\n\
             drop(b);\n\
             1\n\
         }\n",
    )
    .unwrap();
    let receipts = census.join("p.return-certificate-receipts.tsv");
    fs::write(
        &receipts,
        "function\treceipt\ncrate::f\twaiver-drop(scope-exit) site=<program>/lib.rs:2:9: 2:10\n",
    )
    .unwrap();
    let args = [census.as_path(), out.as_path(), deps.as_path()];
    let clean = receipt(&script, &args, "p");
    assert_eq!(
        (field(&clean, "scope_exit"), field(&clean, "unreceipted")),
        ("1", "0"),
        "{clean}"
    );
    fs::write(&receipts, "function\treceipt\n").unwrap();
    let faulted = receipt(&script, &args, "p");
    assert_eq!(field(&faulted, "unreceipted"), "1", "{faulted}");
    fs::remove_dir_all(dir).unwrap();
}

/// The receipt line of `condition` for `program` (x_instruments prints three).
fn x_receipt(script: &Path, args: &[&Path], condition: &str) -> String {
    let output = Command::new("python3")
        .arg(script)
        .args(args)
        .output()
        .expect("python3 runs the checker");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    stdout
        .lines()
        .find(|line| line.starts_with(&format!("conformance {condition} program=p ")))
        .unwrap_or_else(|| {
            panic!(
                "no {condition} receipt:\n{stdout}\n{}",
                String::from_utf8_lossy(&output.stderr)
            )
        })
        .to_owned()
}

/// A census fixture for the X instruments: the tree, the census's frame
/// columns, and the tables they read.
fn x_fixture(tag: &str, tree: &str, receipts: &str, admissions: &str) -> (PathBuf, PathBuf) {
    let dir = scratch(tag);
    let census = dir.join("census");
    fs::create_dir_all(census.join("emitted-trees/p")).unwrap();
    fs::write(census.join("emitted-trees/p/lib.rs"), tree).unwrap();
    fs::write(census.join("p.return-certificate-receipts.tsv"), receipts).unwrap();
    let frame = "c\tL\tsha\tw\ttrue\trelease\t0\t0\tm\tw\ta\tx\ty";
    let header = "corpus\tanalysis_frame\tcode_frame\traw_boundary_wave\tdata\tbuild_profile\t\
                  resource_configured_mib\tresource_effective_mib\ta5_mode\ta5_world\ta5_attestation\t\
                  cache_manifest_sha256\tlaunch_env_sha256";
    let rows: String = admissions
        .lines()
        .map(|row| format!("{frame}\t{row}\n"))
        .collect();
    fs::write(
        census.join("p.raw-boundary-ownership-fields-native.tsv"),
        format!(
            "{header}\tprogram\tsubject_key\towner_fn\tmir_local\tis_param\tptr_depth\t\
             model_kind\tfinal_decision\tconsidered\tnative_status\n{rows}"
        ),
    )
    .unwrap();
    (dir, census)
}

/// **GeneratedRetirement (R625-3)** — every Drop of a Box-carrying place is a
/// row. A scope-exit release with its `waiver-drop(scope-exit)` receipt is
/// receipted; the fault removes the receipt.
#[test]
fn conformance_generated_retirement_catches_an_unreceipted_release() {
    let Some(script) = tool("x_instruments.py") else {
        println!("SKIP conformance_generated_retirement: docs/agents/tools/conformance absent");
        return;
    };
    let deps = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../deps_crate/target/debug/deps");
    if !deps.exists() {
        println!("SKIP conformance_generated_retirement: deps_crate not built");
        return;
    }
    let tree = "pub unsafe fn f(flag: i32) -> i32 {\n\
                    let b: Option<Box<i32>> = Some(Box::new(1));\n\
                    if flag != 0 {\n\
                        return 0;\n\
                    }\n\
                    drop(b);\n\
                    1\n\
                }\n";
    let admit = "p\tcrate::f::b#1\tcrate::f\t1\tfalse\t1\towning\tbox\ttrue\tselected";
    let receipt =
        "function\treceipt\ncrate::f\twaiver-drop(scope-exit) site=<program>/lib.rs:2:9: 2:10\n";
    let (dir, census) = x_fixture("x1", tree, receipt, admit);
    let out = dir.join("out");
    let args = [census.as_path(), out.as_path(), deps.as_path()];
    let clean = x_receipt(&script, &args, "GeneratedRetirement");
    assert_eq!(
        (
            field(&clean, "implicit_release_sites"),
            field(&clean, "unreceipted"),
            field(&clean, "unwind")
        ),
        ("1", "0", "0"),
        "{clean}"
    );
    fs::write(
        census.join("p.return-certificate-receipts.tsv"),
        "function\treceipt\n",
    )
    .unwrap();
    let faulted = x_receipt(&script, &args, "GeneratedRetirement");
    assert_eq!(field(&faulted, "unreceipted"), "1", "{faulted}");
    fs::remove_dir_all(dir).unwrap();
}

/// **RemainingRoots (R625-3)** — an implicit release is accounted when its
/// owner's admission receipt exists and no pointer derived from the owner is
/// live at the drop. Two faults: a raw alias read after the drop, and the
/// admission row removed.
#[test]
fn conformance_remaining_roots_catches_a_live_alias_and_a_missing_admission() {
    let Some(script) = tool("x_instruments.py") else {
        println!("SKIP conformance_remaining_roots: docs/agents/tools/conformance absent");
        return;
    };
    let deps = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../deps_crate/target/debug/deps");
    if !deps.exists() {
        println!("SKIP conformance_remaining_roots: deps_crate not built");
        return;
    }
    let tree = |use_after: &str| {
        format!(
            "pub unsafe fn g(flag: i32) -> i32 {{\n\
                 let p: *const i32;\n\
                 {{\n\
                     let b: Box<i32> = Box::new(7);\n\
                     p = &*b;\n\
                 }}\n\
                 {use_after}\n\
                 let _ = (flag, p);\n\
                 0\n\
             }}\n"
        )
    };
    let admit = "p\tcrate::g::b#3\tcrate::g\t3\tfalse\t1\towning\tbox\ttrue\tselected";
    let receipt =
        "function\treceipt\ncrate::g\twaiver-drop(scope-exit) site=<program>/lib.rs:4:13: 4:14\n";
    let (dir, census) = x_fixture("x2", &tree(""), receipt, admit);
    let out = dir.join("out");
    let args = [census.as_path(), out.as_path(), deps.as_path()];
    let clean = x_receipt(&script, &args, "RemainingRoots");
    assert_eq!(
        (field(&clean, "all_roots"), field(&clean, "unproved")),
        ("1", "0"),
        "{clean}"
    );
    fs::write(
        census.join("emitted-trees/p/lib.rs"),
        tree("if flag != 0 { return *p; }"),
    )
    .unwrap();
    let alias = x_receipt(&script, &args, "RemainingRoots");
    assert_eq!(
        field(&alias, "unproved"),
        "1",
        "a live alias at the drop: {alias}"
    );
    fs::write(census.join("emitted-trees/p/lib.rs"), tree("")).unwrap();
    let (_, census2) = (dir.clone(), census.clone());
    fs::write(
        census2.join("p.raw-boundary-ownership-fields-native.tsv"),
        "corpus\tanalysis_frame\n",
    )
    .unwrap();
    let unadmitted = x_receipt(&script, &args, "RemainingRoots");
    assert_eq!(
        field(&unadmitted, "unproved"),
        "1",
        "no admission: {unadmitted}"
    );
    fs::remove_dir_all(dir).unwrap();
}

/// **OwnershipRealization (R625-3)** — the owner ledger: a Box closed by its
/// explicit `drop` (the C free site's image) is `closed_explicit`; the fault
/// deletes the drop, and the close becomes implicit.
#[test]
fn conformance_ownership_realization_catches_a_deleted_drop() {
    let Some(script) = tool("x_instruments.py") else {
        println!("SKIP conformance_ownership_realization: docs/agents/tools/conformance absent");
        return;
    };
    let deps = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../deps_crate/target/debug/deps");
    if !deps.exists() {
        println!("SKIP conformance_ownership_realization: deps_crate not built");
        return;
    }
    let tree = |release: &str| {
        format!(
            "pub unsafe fn h() -> i32 {{\n\
                 let c: Box<i32> = Box::new(3);\n\
                 let v = *c;\n\
                 {release}\n\
                 v\n\
             }}\n"
        )
    };
    let (dir, census) = x_fixture("x3", &tree("drop(c);"), "function\treceipt\n", "");
    let out = dir.join("out");
    let args = [census.as_path(), out.as_path(), deps.as_path()];
    let clean = x_receipt(&script, &args, "OwnershipRealization");
    assert_eq!(
        (
            field(&clean, "closed_explicit"),
            field(&clean, "closed_implicit"),
            field(&clean, "open")
        ),
        ("1", "0", "0"),
        "{clean}"
    );
    fs::write(census.join("emitted-trees/p/lib.rs"), tree("")).unwrap();
    let faulted = x_receipt(&script, &args, "OwnershipRealization");
    assert_eq!(
        (
            field(&faulted, "closed_explicit"),
            field(&faulted, "closed_implicit")
        ),
        ("0", "1"),
        "{faulted}"
    );
    fs::remove_dir_all(dir).unwrap();
}
