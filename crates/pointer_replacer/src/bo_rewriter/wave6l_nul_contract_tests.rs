//! wave-6l relay 057 (R608-1): C strings at NUL-contract positions take the
//! slice family, and a constant count equal to the pointee's size is one
//! element.
//!
//! Every fixture is the reduced corpus shape named on its constant. Their
//! decisions at the base (`8070b43cf`) were `held:thin-extent`,
//! `return-not-adapted` — the RED record is the
//! probe log filed with report 054 — and each rule has a fault that restores it.

fn emitted_from_file(source: &str) -> super::RewriteOutcome {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "crat-w6l-nul-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("fixture directory");
    let root = dir.join("lib.rs");
    std::fs::write(&root, source).expect("fixture file");
    let outcome = super::rewrite_m1_path(&root);
    let _ = std::fs::remove_dir_all(&dir);
    outcome
}

/// binn `strlen2::str`: null-tested, then read by `strlen`; its one caller
/// hands it a raw `void *` (held `void-pointee`).
const PROBE_STRLEN2: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn strlen(s: *const i8) -> usize;
}
unsafe fn strlen2(mut str: *mut i8) -> usize {
    if str.is_null() {
        return 0;
    }
    return strlen(str);
}
pub unsafe fn add_value(mut pvalue: *mut core::ffi::c_void) -> usize {
    strlen2(pvalue as *mut i8)
}
"#;

/// brotli `OpenInputFile::input_path` (and `OpenOutputFile`, `CopyStat`): null-tested,
/// read by `fopen`, handed to the local `PrintablePath` whose result `fprintf` reads,
/// and passed in from a raw struct field.
const PROBE_OPEN_INPUT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn fopen(path: *const i8, mode: *const i8) -> *mut core::ffi::c_void;
    fn fprintf(stream: *mut core::ffi::c_void, format: *const i8, ...) -> i32;
    static mut stderr: *mut core::ffi::c_void;
}
pub struct Context {
    pub current_input_path: *const i8,
}
unsafe fn printable_path(mut path: *const i8) -> *const i8 {
    return if !path.is_null() { path } else { b"con\0" as *const u8 as *const i8 };
}
unsafe fn open_input_file(mut input_path: *const i8) -> i32 {
    if input_path.is_null() {
        return 1;
    }
    let mut f = fopen(input_path, b"rb\0" as *const u8 as *const i8);
    if f.is_null() {
        fprintf(stderr, b"failed to open input file [%s]\n\0" as *const u8 as *const i8,
            printable_path(input_path));
        return 0;
    }
    1
}
pub unsafe fn next_file(mut context: *mut Context) -> i32 {
    open_input_file((*context).current_input_path)
}
"#;

/// libzahl `zrand::pathname`: declared null, assigned only string literals.
const PROBE_LITERAL_ASSIGNED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn open(path: *const i8, flags: i32, ...) -> i32;
    fn abort() -> !;
}
pub unsafe fn zrand(mut dev: u32) -> i32 {
    let mut pathname = 0 as *const i8;
    let mut fd: i32 = 0;
    match dev {
        0 => {
            pathname = b"/dev/urandom\0" as *const u8 as *const i8;
        }
        1 => {
            pathname = b"/dev/random\0" as *const u8 as *const i8;
        }
        _ => {
            abort();
        }
    }
    fd = open(pathname, 0);
    fd
}
"#;

/// urlparser `url_get_auth::protocol`: a local callee's RAW result, null-tested,
/// read by `strlen` — held (see the pin below).
const PROBE_CALL_RESULT_STRLEN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn strlen(s: *const i8) -> usize;
}
static mut PROTOCOL: [i8; 16] = [0; 16];
unsafe fn get_protocol(mut url: *mut i8) -> *mut i8 {
    if *url == 0 {
        return 0 as *mut i8;
    }
    return PROTOCOL.as_mut_ptr();
}
pub unsafe fn get_auth(mut url: *mut i8) -> i32 {
    let mut protocol = get_protocol(url);
    if protocol.is_null() {
        return 0;
    }
    let mut l = strlen(protocol) as i32 + 3;
    l
}
"#;

/// lil `fnc_catcher::catcher`: as `lil_to_boolean::s`, and ALSO an argument of
/// the local `strclone` — still held (report 054).
const PROBE_CATCHER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn strlen(s: *const i8) -> usize;
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn strcpy(d: *mut i8, s: *const i8) -> *mut i8;
}
pub struct Value {
    pub d: *mut i8,
}
pub struct Lil {
    pub catcher: *mut i8,
}
unsafe fn to_string(mut v: *mut Value) -> *const i8 {
    return if (*v).d.is_null() { b"\0" as *const u8 as *const i8 } else { (*v).d as *const i8 };
}
unsafe fn strclone(mut s: *const i8) -> *mut i8 {
    let mut len = strlen(s).wrapping_add(1);
    let mut ns = malloc(len) as *mut i8;
    if ns.is_null() {
        return 0 as *mut i8;
    }
    strcpy(ns, s);
    ns
}
pub unsafe fn fnc_catcher(mut lil: *mut Lil, mut argv: *mut *mut Value) {
    let mut catcher = to_string(*argv.offset(0 as isize));
    (*lil).catcher = if *catcher.offset(0 as isize) as i32 != 0 {
        strclone(catcher)
    } else {
        0 as *mut i8
    };
}
"#;

/// heman `kmVec4Assign::pIn`: `memcpy` of `size_of::<f32>() * 4` bytes of a
/// `kmVec4` — one element, spelled as another type.
const PROBE_KMVEC4: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
    fn abort() -> !;
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct kmVec4 {
    pub x: f32,
    pub y: f32,
    pub z: f32,
    pub w: f32,
}
pub unsafe fn kmVec4Assign(mut pOut: *mut kmVec4, mut pIn: *const kmVec4) -> *mut kmVec4 {
    if pOut != pIn as *mut kmVec4 {
    } else {
        abort();
    }
    memcpy(pOut as *mut core::ffi::c_void, pIn as *const core::ffi::c_void,
        (::std::mem::size_of::<f32>() as u64).wrapping_mul(4 as i32 as u64));
    return pOut;
}
"#;

/// lil `lil_to_boolean::s`: a local callee's RAW result, indexed to the NUL —
/// held (see the pin below).
const PROBE_CALL_RESULT_SCAN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
pub struct Value {
    pub d: *mut i8,
}
unsafe fn to_string(mut v: *mut Value) -> *const i8 {
    return if (*v).d.is_null() { b"\0" as *const u8 as *const i8 } else { (*v).d as *const i8 };
}
pub unsafe fn to_boolean(mut v: *mut Value) -> i32 {
    let mut s = to_string(v);
    let mut i: usize = 0;
    if *s.offset(0 as isize) == 0 {
        return 0;
    }
    while *s.offset(i as isize) != 0 {
        if *s.offset(i as isize) as i32 != '0' as i32 {
            return 1;
        }
        i = i.wrapping_add(1);
    }
    0
}
"#;

fn emitted_source(fixture: &str) -> (String, super::RawBoundaryArtifacts) {
    match emitted_from_file(fixture) {
        super::RewriteOutcome::Emitted {
            source,
            raw_boundary_artifacts,
            ..
        } => {
            assert!(super::verify::type_checks_str(&source), "{source}");
            (source, raw_boundary_artifacts)
        }
        other => panic!("fixture must emit: {other:?}"),
    }
}

fn reason(decisions: &[(String, bool, String)], name: &str, is_param: bool) -> String {
    decisions
        .iter()
        .find(|(subject, param, _)| subject == name && *param == is_param)
        .map(|(_, _, reason)| reason.clone())
        .unwrap_or_else(|| panic!("no subject {name}: {decisions:#?}"))
}

fn lift_row<'a>(lifts: &'a str, subject: &str) -> &'a str {
    lifts
        .lines()
        .skip(1)
        .find(|row| row.split('\t').nth(1) == Some(subject))
        .unwrap_or_else(|| panic!("no lift receipt for {subject}: {lifts}"))
}

/// W1 — the null-tested C string takes `Option<&[i8]>`, and the raw caller is
/// adapted with a null test and the receipted §77 fallback.
#[test]
fn w6l_nul_w1_a_null_tested_c_string_parameter_takes_the_optional_slice() {
    let decisions = super::emit_tests::decisions_of(PROBE_STRLEN2);
    assert_eq!(
        reason(&decisions, "str", true),
        "<emitted>",
        "{decisions:#?}"
    );
    assert_eq!(reason(&decisions, "pvalue", true), "held:void-pointee");
    let (source, artifacts) = emitted_source(PROBE_STRLEN2);
    assert!(
        source.contains("fn strlen2(mut str: Option<&[i8]>)"),
        "{source}"
    );
    assert!(source.contains("str.is_none()"), "{source}");
    assert!(
        source.contains("slice.as_ptr()"),
        "strlen reads through the slice's own pointer: {source}"
    );
    assert!(
        source.contains("__crat_call_adapter_ptr.is_null()")
            && source.contains("from_raw_parts(__crat_call_adapter_ptr,")
            && source.contains("crate::FALLBACK_SLICE_EXTENT"),
        "the raw caller keeps its null and takes the receipted fallback: {source}"
    );
    let row = lift_row(&artifacts.licensed_lifts, "strlen2::str");
    assert!(
        row.contains("\topt-slice\tfallback\t")
            && row.contains("fallback(extent-lift@addendum-77:"),
        "{row}"
    );
}

/// W2 — the brotli path shape: the optional slice is bridged into `fopen` and
/// into the local `printable_path`, whose returned child only `fprintf` reads,
/// and the raw struct-field caller is adapted.
#[test]
fn w6l_nul_w2_the_path_parameter_bridges_into_its_local_callee() {
    let decisions = super::emit_tests::decisions_of(PROBE_OPEN_INPUT);
    assert_eq!(
        reason(&decisions, "input_path", true),
        "<emitted>",
        "{decisions:#?}"
    );
    let (source, _) = emitted_source(PROBE_OPEN_INPUT);
    assert!(
        source.contains("fn open_input_file(mut input_path: Option<&[i8]>)"),
        "{source}"
    );
    assert!(
        source.contains("printable_path(input_path.as_deref().map_or(core::ptr::null::<i8>(),"),
        "{source}"
    );
    assert!(
        source.contains("(*context).current_input_path;")
            && source.contains("crate::FALLBACK_SLICE_EXTENT"),
        "{source}"
    );
}

/// W3 — every value the binding holds is a literal of its own length: the
/// declaration's null is `&[]`, each assignment builds its literal's slice, no
/// extent is fabricated and the lift is receipted as evidence.
#[test]
fn w6l_nul_w3_a_literal_only_binding_is_evidence_backed() {
    let decisions = super::emit_tests::decisions_of(PROBE_LITERAL_ASSIGNED);
    assert_eq!(
        reason(&decisions, "pathname", false),
        "<emitted>",
        "{decisions:#?}"
    );
    let (source, artifacts) = emitted_source(PROBE_LITERAL_ASSIGNED);
    assert!(
        source.contains("let mut pathname: &[i8] = &[];"),
        "{source}"
    );
    assert!(
        source.contains(
            "b\"/dev/urandom\\0\" as *const u8 as\n                        *const i8, 13usize)"
        ) || source.contains("*const i8, 13usize)"),
        "{source}"
    );
    assert!(source.contains("*const i8, 12usize)"), "{source}");
    assert!(source.contains("open(pathname.as_ptr(), 0)"), "{source}");
    let body = &source
        [source.find("fn zrand").unwrap()..source.find("const FALLBACK").unwrap_or(source.len())];
    assert!(
        !body.contains("FALLBACK_SLICE_EXTENT"),
        "no fabricated extent: {body}"
    );
    let row = lift_row(&artifacts.licensed_lifts, "zrand::pathname");
    assert!(
        row.contains("\tslice\tevidence\t")
            && row.contains("evidence(literal-bytes:thin-extent:-)"),
        "{row}"
    );
}

/// The two call-result receivers stay held (report 054): a sealed
/// constructor over `callee(arg)` would replace the initializer's text and
/// drop the argument's own boundary bridge (lil's `lil_to_string(val)` — `val`
/// delivered, the formal raw — would be E0308 and revert `val`'s class), so
/// clause (b) of the constructor refusal is left as it stands. Pinned so the
/// composition build that opens them sees them move.
#[test]
fn w6l_nul_the_call_result_receivers_stay_held() {
    for (fixture, name) in [
        (PROBE_CALL_RESULT_STRLEN, "protocol"),
        (PROBE_CALL_RESULT_SCAN, "s"),
    ] {
        let decisions = super::emit_tests::decisions_of(fixture);
        assert_eq!(
            reason(&decisions, name, false),
            "return-not-adapted",
            "{decisions:#?}"
        );
    }
}

/// The held one of the family, pinned so a later carrier build sees it move.
#[test]
fn w6l_nul_the_catcher_stays_held_at_its_local_callee_argument() {
    let decisions = super::emit_tests::decisions_of(PROBE_CATCHER);
    assert_eq!(
        reason(&decisions, "catcher", false),
        "return-not-adapted",
        "{decisions:#?}"
    );
    assert_eq!(reason(&decisions, "s", true), "<emitted>", "{decisions:#?}");
}

/// W7 — the count's value, not its spelling: one element, no thin-extent hold.
#[test]
fn w6l_nul_w7_a_constant_count_of_the_pointee_size_is_one_element() {
    let decisions = super::emit_tests::decisions_of(PROBE_KMVEC4);
    assert_eq!(
        reason(&decisions, "pIn", true),
        "<emitted>",
        "{decisions:#?}"
    );
}

const CONTROL_SIGN_CHANGING_COUNT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Big {
    pub bytes: [u8; 200],
}
pub unsafe fn big_assign(mut pOut: *mut Big, mut pIn: *const Big) {
    memcpy(pOut as *mut core::ffi::c_void, pIn as *const core::ffi::c_void,
        200 as i32 as i8 as u64);
}
"#;

/// The `one_pointee` fact at the fixture's `memcpy` source position.
fn memcpy_source_one_pointee(fixture: &str) -> bool {
    ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(fixture),
        |tcx| {
            let (_, ctx) = super::decide_table_with_ctx(tcx)?;
            ctx.facts
                .foreign_call_args
                .iter()
                .find(|fact| fact.callee.path == "memcpy" && fact.argument_index == 1)
                .and_then(|fact| fact.contract_count.as_ref())
                .map(|count| count.one_pointee)
                .ok_or_else(|| "no memcpy source count".to_owned())
        },
    )
    .expect("fixture compiles")
    .expect("memcpy source fact")
}

/// C4 (Codex review): a cast that CHANGES the value is not peeled. `200 as
/// i32 as i8 as u64` spells the pointee's size, 200, and is `2^64 - 56`: the
/// count is not one element. W7's count is, by value.
#[test]
fn w6l_nul_c4_a_value_changing_cast_is_not_one_element() {
    assert!(!memcpy_source_one_pointee(CONTROL_SIGN_CHANGING_COUNT));
    assert!(memcpy_source_one_pointee(PROBE_KMVEC4));
}

const CONTROL_ONE_ELEMENT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
#[repr(C)]
pub struct Stat {
    pub size: i64,
}
extern "C" {
    fn stat(path: *const i8, buf: *mut Stat) -> i32;
}
pub unsafe fn size_of_file(mut buf: *mut Stat) -> i64 {
    if buf.is_null() {
        return 0;
    }
    stat(b"x\0" as *const u8 as *const i8, buf);
    (*buf).size
}
"#;

/// C1 — a non-NUL (one-element) foreign use stays thin: `Option<&mut Stat>`,
/// never a slice, and no lift receipt.
#[test]
fn w6l_nul_c1_a_one_element_foreign_use_stays_thin() {
    let decisions = super::emit_tests::decisions_of(CONTROL_ONE_ELEMENT);
    assert_eq!(
        reason(&decisions, "buf", true),
        "<emitted>",
        "{decisions:#?}"
    );
    let (source, artifacts) = emitted_source(CONTROL_ONE_ELEMENT);
    assert!(source.contains("buf: Option<&mut Stat>"), "{source}");
    assert!(!source.contains("[Stat]"), "{source}");
    assert_eq!(
        artifacts.licensed_lifts.lines().count(),
        1,
        "{}",
        artifacts.licensed_lifts
    );
}

const CONTROL_COUNTED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8;
}
unsafe fn copy_n(mut dst: *mut u8, mut src: *const u8, mut n: usize) {
    if src.is_null() {
        return;
    }
    memcpy(dst, src, n);
}
"#;

/// C2 — a counted companion beats the fallback: the null-tested source with an
/// exact count takes its contract promotion (evidence `n`) in the ladder, so
/// the waiver's lift never sees it.
#[test]
fn w6l_nul_c2_a_counted_companion_beats_the_fallback() {
    let promotions = ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(CONTROL_COUNTED),
        |tcx| {
            let table = super::decide_table(tcx)?;
            Ok::<_, String>((
                table
                    .contract_extent_promotions
                    .into_values()
                    .collect::<Vec<_>>(),
                super::decision::licensed_lift::receipts_tsv(&table.licensed_lifts),
            ))
        },
    )
    .expect("fixture compiles")
    .expect("decision table");
    let source = promotions
        .0
        .iter()
        .find(|promotion| promotion.nullable)
        .unwrap_or_else(|| panic!("the nullable source is promoted: {:#?}", promotions.0));
    assert_eq!(
        source.length,
        super::decision::contract_extent::LengthPlan::Evidence {
            elements: "n".to_owned(),
            source: super::decision::contract_extent::LengthSource::ExactContract {
                site: source.sites[0].site.clone(),
                argument_index: 2,
            },
        },
        "{source:#?}"
    );
    assert!(
        !promotions.1.contains("copy_n::src"),
        "the waiver's lift never sees a counted source: {}",
        promotions.1
    );
}
