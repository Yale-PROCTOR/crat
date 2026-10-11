//! **Relay 324 (R975-1; era-5c 167c §2): a formal its own raw copy walks.**
//! Under S39 (`CRAT_COPY_RELAX=depth0-borrow-to-raw`) a bare copy `inp = s` may
//! take a raw view of a reference source, so the model makes `s` Ref while its
//! copy `inp` walks past the first element with `offset`. The form rule read
//! the subject's OWN raw-only uses, gave `s` the thin form `&mut f64`, and a
//! caller holding a `Box<[f64]>` owner rendered `&mut [f64]` into it:
//! tulipindicators' `smoke::get_array` E0308, reverted with four custody rows
//! behind it. The formal takes the slice form its copy uses.
//!
//! Each witness runs the rewrite in a child under the frame of record's arms
//! (`frames/l01p14u-env.sh`) with the S39 switches named or not, as era-5c's
//! `copy_relax_tests` do: the switches are read from the environment.

const FRAME_ENV: &str = include_str!("../../frames/l01p14u-env.sh");

const ALLOW: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, unused_variables, non_snake_case, non_camel_case_types)]\n";

/// tulipindicators' `get_array`, reduced: the raw copy `inp` walks `s` and
/// measures the walk against it. One caller hands it a stack array's pointer
/// that it walks itself (a slice at the caller), the other a `malloc`ed
/// pointer it frees (an owner).
const GET_ARRAY: &str = r#"
extern "C" {
    fn malloc(_: u64) -> *mut core::ffi::c_void;
    fn free(_: *mut core::ffi::c_void);
    fn next(n: i32) -> i32;
}
#[no_mangle]
pub unsafe extern "C" fn get_array(mut n: i32, mut s: *mut f64) -> i32 {
    if n == 0 as i32 { return 0 as i32 }
    let mut inp: *mut f64 = s;
    loop {
        *inp = n as f64;
        inp = inp.offset(1);
        n = next(n);
        if n == 0 as i32 { break; }
    }
    return inp.offset_from(s) as i64 as i32;
}
#[no_mangle]
pub unsafe extern "C" fn run_stack(mut n: i32) -> i32 {
    let mut buf: [f64; 512] = [0.; 512];
    let mut p: *mut f64 = buf.as_mut_ptr();
    let mut k: i32 = get_array(n, p);
    return k + *p.offset(1) as i32;
}
#[no_mangle]
pub unsafe extern "C" fn run_heap(mut n: i32) -> i32 {
    let mut a: *mut f64 = malloc((::std::mem::size_of::<f64>() as u64).wrapping_mul(512 as i32 as u64)) as *mut f64;
    let mut k: i32 = get_array(n, a);
    let mut v: i32 = *a.offset(1) as i32;
    free(a as *mut core::ffi::c_void);
    return k + v;
}
"#;

/// The control: the copy reads through `s` and never steps — nothing walks
/// past the first element, and the formal keeps the thin form.
const READ_ONLY_COPY: &str = r#"
extern "C" {
    fn next(n: i32) -> i32;
}
#[no_mangle]
pub unsafe extern "C" fn get_one(mut n: i32, mut s: *mut f64) -> i32 {
    let mut inp: *mut f64 = s;
    *inp = n as f64;
    return next(n);
}
#[no_mangle]
pub unsafe extern "C" fn run(mut n: i32) -> i32 {
    let mut x: f64 = 0.;
    return get_one(n, &mut x);
}
"#;

/// The control: a narrower copy steps only within the formal's own element
/// (binn's `copy_be32` byte view, relay 065's element test) — no walk past the
/// first element, and the formal keeps the thin form.
const BYTE_VIEW_COPY: &str = r#"
#[no_mangle]
pub unsafe extern "C" fn put_be32(mut v: u32, mut s: *mut u32) {
    let mut d: *mut u8 = s as *mut u8;
    *d.offset(0 as isize) = (v >> 24) as u8;
    *d.offset(1 as isize) = (v >> 16) as u8;
    *d.offset(2 as isize) = (v >> 8) as u8;
    *d.offset(3 as isize) = v as u8;
}
#[no_mangle]
pub unsafe extern "C" fn run(mut v: u32) -> u32 {
    let mut x: u32 = 0;
    put_be32(v, &mut x);
    return x;
}
"#;

/// The stand-in review's MED-1: a caller hands the formal a pointer it has
/// itself null-tested, so the formal carries the caller's nullability (not
/// its own: no null literal reaches it). With the formal's Option stage
/// withdrawn (an exclusion re-derivation; here the test hook) it must fall
/// back to raw, never to a bare slice built on a possibly null base.
const NULLABLE_ACTUAL: &str = r#"
extern "C" {
    fn next(n: i32) -> i32;
}
#[no_mangle]
pub unsafe extern "C" fn get_array(mut n: i32, mut s: *mut f64) -> i32 {
    if n == 0 as i32 { return 0 as i32 }
    let mut inp: *mut f64 = s;
    loop {
        *inp = n as f64;
        inp = inp.offset(1);
        n = next(n);
        if n == 0 as i32 { break; }
    }
    return inp.offset_from(s) as i64 as i32;
}
#[no_mangle]
pub unsafe extern "C" fn run_maybe(mut n: i32, mut q: *mut f64) -> i32 {
    if q.is_null() { return get_array(0 as i32, q); }
    return get_array(n, q);
}
"#;

/// The frame's arms: every `CRAT_` export of the frame's env file but the
/// launch identity (`CRAT_ERA5_*`) and the raw-cause sidecar, which a fixture
/// rewrite does not take (era-5c's `copy_relax_tests::frame_arms`).
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
#[ignore = "runs under the frame's arms in a child of the r324 witnesses"]
fn r324_inner_rewrite() {
    let code = match std::env::var("CRAT_R324_SHAPE").as_deref() {
        Ok("GET_ARRAY") => GET_ARRAY,
        Ok("READ_ONLY_COPY") => READ_ONLY_COPY,
        Ok("BYTE_VIEW_COPY") => BYTE_VIEW_COPY,
        Ok("NULLABLE_ACTUAL") => NULLABLE_ACTUAL,
        other => panic!("unknown shape {other:?}"),
    };
    // The Option stage withdrawn for the labels named, as an exclusion
    // re-derivation would (the R824-2 hook; the child is one decision).
    if let Ok(labels) = std::env::var("CRAT_R324_WITHDRAW") {
        super::decision::FORCED_OPTION_WITHDRAWALS
            .lock()
            .expect("hook")
            .extend(labels.split(',').map(str::to_owned));
    }
    let (source, degradations, reverted_count) =
        match super::rewrite_m1_census_world(&format!("{ALLOW}{code}")) {
            super::RewriteOutcome::Emitted {
                source,
                degradations,
                reverted_count,
                ..
            } => (source, degradations, reverted_count),
            super::RewriteOutcome::Degraded { reason, .. } => {
                panic!("the fixture must emit, it degraded: {reason}")
            }
        };
    for line in source.lines() {
        println!("R324_SOURCE {line}");
    }
    for d in &degradations {
        println!("R324_DEGRADED {} {}", d.subject, d.reason.key());
    }
    println!("R324_REVERTED {reverted_count}");
    println!(
        "R324_TYPECHECKS {}",
        super::verify::type_checks_str(&source)
    );
}

struct Emitted {
    source: String,
    degraded: Vec<(String, String)>,
    reverted: usize,
    type_checks: bool,
}

impl Emitted {
    fn reason(&self, subject: &str) -> Option<&str> {
        self.degraded
            .iter()
            .find(|(s, _)| s == subject || s.starts_with(&format!("{subject}#")))
            .map(|(_, reason)| reason.as_str())
    }

    /// The function's signature, whitespace removed.
    fn signature(&self, function: &str) -> String {
        let at = self
            .source
            .find(&format!("fn {function}("))
            .unwrap_or_else(|| panic!("no fn {function}:\n{}", self.source));
        let rest = &self.source[at..];
        rest[..rest.find('{').unwrap_or(rest.len())]
            .split_whitespace()
            .collect()
    }
}

/// The shape rewritten in a child under the frame's arms, with S39's two
/// switches on (`relax`) or as the frame has them (off).
fn rewrite(shape: &str, relax: bool) -> Emitted {
    rewrite_withdrawn(shape, relax, None)
}

/// [`rewrite`], with the Option stage withdrawn for the labels named.
fn rewrite_withdrawn(shape: &str, relax: bool, withdrawn: Option<&str>) -> Emitted {
    let exe = std::env::current_exe().expect("current_exe");
    let mut command = std::process::Command::new(exe);
    command.args([
        "bo_rewriter::copy_walk_slice_tests::r324_inner_rewrite",
        "--exact",
        "--ignored",
        "--nocapture",
        "--test-threads=1",
    ]);
    for (key, value) in frame_arms() {
        command.env(key, value);
    }
    command.env("CRAT_R324_SHAPE", shape);
    if let Some(labels) = withdrawn {
        command.env("CRAT_R324_WITHDRAW", labels);
    }
    let (copy_relax, merge_liveness) = if relax {
        ("depth0-borrow-to-raw", "on")
    } else {
        ("off", "off")
    };
    command.env("CRAT_COPY_RELAX", copy_relax);
    command.env("CRAT_MERGE_LIVENESS", merge_liveness);
    let output = command.output().expect("child test");
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "child {shape} failed:\n{text}");
    let mut emitted = Emitted {
        source: String::new(),
        degraded: Vec::new(),
        reverted: usize::MAX,
        type_checks: false,
    };
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("R324_SOURCE ") {
            emitted.source.push_str(rest);
            emitted.source.push('\n');
        } else if let Some(rest) = line.strip_prefix("R324_DEGRADED ") {
            let (subject, reason) = rest.split_once(' ').expect("subject reason");
            emitted
                .degraded
                .push((subject.to_owned(), reason.to_owned()));
        } else if let Some(rest) = line.strip_prefix("R324_REVERTED ") {
            emitted.reverted = rest.trim().parse().expect("a count");
        } else if let Some(rest) = line.strip_prefix("R324_TYPECHECKS ") {
            emitted.type_checks = rest.trim() == "true";
        }
    }
    emitted.degraded.sort();
    eprintln!(
        "R324 {shape} relax={relax}\n{}\nDEGRADED {:#?}\nREVERTED {}",
        emitted.source, emitted.degraded, emitted.reverted
    );
    emitted
}

/// Under S39 the formal its raw copy walks is a slice, the copy is its raw
/// view, and both callers' arguments meet it with nothing reverted.
#[test]
fn r324_a_formal_its_raw_copy_walks_takes_the_slice_form() {
    let relaxed = rewrite("GET_ARRAY", true);
    assert!(relaxed.type_checks, "{}", relaxed.source);
    assert_eq!(relaxed.reverted, 0, "{:#?}", relaxed.degraded);
    assert_eq!(
        relaxed.reason("get_array::s"),
        None,
        "{:#?}",
        relaxed.degraded
    );
    assert!(
        relaxed.signature("get_array").contains("s:&mut[f64]"),
        "{}",
        relaxed.signature("get_array")
    );
}

/// The frame without the switches: the copy is equated with `s`, both raw, as
/// at 58.
#[test]
fn r324_control_without_the_switches_the_formal_stays_raw() {
    let frame = rewrite("GET_ARRAY", false);
    assert!(frame.type_checks, "{}", frame.source);
    assert!(
        frame.signature("get_array").contains("s:*mutf64"),
        "{}",
        frame.signature("get_array")
    );
}

/// A copy that never steps does not make its source a slice.
#[test]
fn r324_control_a_copy_that_does_not_walk_keeps_the_thin_form() {
    let relaxed = rewrite("READ_ONLY_COPY", true);
    assert!(relaxed.type_checks, "{}", relaxed.source);
    assert!(
        relaxed.signature("get_one").contains("s:&mutf64"),
        "{}",
        relaxed.signature("get_one")
    );
}

/// A narrower copy stepping inside the element does not make its source a
/// slice.
#[test]
fn r324_control_a_byte_view_within_the_element_keeps_the_thin_form() {
    let relaxed = rewrite("BYTE_VIEW_COPY", true);
    assert!(relaxed.type_checks, "{}", relaxed.source);
    assert!(
        relaxed.signature("put_be32").contains("s:&mutu32"),
        "{}",
        relaxed.signature("put_be32")
    );
}

/// MED-1: with its Option stage withdrawn, a walked formal that carries a
/// caller's nullability falls back to raw (R819-1's gate on the thin form),
/// never to a bare slice.
#[test]
fn r324_med1_a_nullable_walked_formal_with_its_option_stage_withdrawn_stays_raw() {
    let withdrawn = rewrite_withdrawn("NULLABLE_ACTUAL", true, Some("get_array::s"));
    assert!(withdrawn.type_checks, "{}", withdrawn.source);
    assert_eq!(withdrawn.reverted, 0, "{:#?}", withdrawn.degraded);
    assert_eq!(
        withdrawn.reason("get_array::s"),
        Some("null-init"),
        "{:#?}",
        withdrawn.degraded
    );
    assert!(
        withdrawn.signature("get_array").contains("s:*mutf64"),
        "{}",
        withdrawn.signature("get_array")
    );
}

/// MED-1 without the hook: in this fixture the exclusion re-derivation
/// withdraws the formal's Option stage itself, and the formal falls back to
/// raw by the same gate. (With the stage enabled such a formal takes the thin
/// optional form ahead of the walk — a residual of 58‴ this change does not
/// touch, stated in main 220a.)
#[test]
fn r324_med1_the_natural_withdrawal_falls_back_to_raw() {
    let natural = rewrite("NULLABLE_ACTUAL", true);
    assert!(natural.type_checks, "{}", natural.source);
    assert_eq!(natural.reverted, 0, "{:#?}", natural.degraded);
    assert_eq!(
        natural.reason("get_array::s"),
        Some("null-init"),
        "{:#?}",
        natural.degraded
    );
    assert!(
        natural.signature("get_array").contains("s:*mutf64"),
        "{}",
        natural.signature("get_array")
    );
}
