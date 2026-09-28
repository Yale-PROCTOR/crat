//! wave-6l relay 057 (R608-1): C strings at NUL-contract positions take the
//! slice family, a string-literal source is not a pending sibling-overlap
//! site, and a constant count equal to the pointee's size is one element.
//!
//! Every fixture is the reduced corpus shape named on its constant. Their
//! decisions at the base (`8070b43cf`) were `held:thin-extent`,
//! `return-not-adapted` and `pending-sibling-overlap` — the RED record is the
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
/// read by `strlen`.
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

/// urlparser `url_parse::fmt` / libtree `print_error::box_vertical`: a string
/// literal handed to a call whose sibling is WRITTEN (`sprintf`'s buffer, `strcpy`'s
/// destination).
const PROBE_LITERAL_SIBLING: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn sprintf(s: *mut i8, format: *const i8, ...) -> i32;
    fn strcpy(d: *mut i8, s: *const i8) -> *mut i8;
    fn malloc(n: usize) -> *mut core::ffi::c_void;
}
pub unsafe fn url_parse(mut is_ssh: bool, mut tmp_path: *mut i8) -> *mut i8 {
    let mut path = malloc(64) as *mut i8;
    if path.is_null() {
        return 0 as *mut i8;
    }
    let mut fmt = (if is_ssh as i32 != 0 {
        b"%s\0" as *const u8 as *const i8
    } else {
        b"/%s\0" as *const u8 as *const i8
    }) as *mut i8;
    sprintf(path, fmt, tmp_path);
    path
}
pub unsafe fn print_error(mut p: *mut i8) {
    let mut box_vertical = b"    |\0" as *const u8 as *const i8;
    strcpy(p, box_vertical);
}
"#;

/// lil `lil_to_boolean::s`: a local callee's RAW result, indexed to the NUL.
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

/// W4 (R615-7) — a local callee's RAW result, null-tested and read by
/// `strlen`: the receiver is the optional-slice constructor WRAPPED around the
/// untouched call (a bracket of two insertions).
#[test]
fn w6l_nul_w4_a_raw_call_result_takes_the_optional_slice_bracket() {
    let decisions = super::emit_tests::decisions_of(PROBE_CALL_RESULT_STRLEN);
    assert_eq!(
        reason(&decisions, "protocol", false),
        "<emitted>",
        "{decisions:#?}"
    );
    let (source, _) = emitted_source(PROBE_CALL_RESULT_STRLEN);
    assert!(
        source.contains("let mut protocol: Option<&[i8]> ="),
        "{source}"
    );
    assert!(source.contains("= get_protocol(url);"), "{source}");
    assert!(
        source.contains("core::slice::from_raw_parts(p,")
            && source.contains("crate::FALLBACK_SLICE_EXTENT"),
        "{source}"
    );
    assert!(
        source.contains("fn get_protocol(mut url: &i8) -> *mut i8"),
        "{source}"
    );
}

/// W5 (R615-7) — a local callee's RAW result, indexed to the NUL: a
/// fallback slice wrapped around the call, indexed.
#[test]
fn w6l_nul_w5_an_indexed_raw_call_result_is_a_fallback_slice_bracket() {
    let decisions = super::emit_tests::decisions_of(PROBE_CALL_RESULT_SCAN);
    assert_eq!(
        reason(&decisions, "s", false),
        "<emitted>",
        "{decisions:#?}"
    );
    let (source, _) = emitted_source(PROBE_CALL_RESULT_SCAN);
    assert!(
        source.contains("let mut s: &[i8] =")
            && source.contains("core::slice::from_raw_parts(to_string(v),"),
        "{source}"
    );
    assert!(source.contains("while s[i] != 0"), "{source}");
}

/// lil's `lil_to_boolean(val)`: `val` is delivered, `lil_to_string`'s formal
/// stays raw (here: its address is read as an integer), so the ARGUMENT
/// carries a bridge inside the receiver's initializer.
const CONTROL_BRIDGED_ARGUMENT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]
pub type text_t = *mut i8;
#[no_mangle]
pub unsafe extern "C" fn to_string(mut text: text_t) -> *const i8 {
    return text as *const i8;
}
pub unsafe fn to_boolean(mut buf: *mut i8, mut n: usize) -> i32 {
    *buf.offset(1 as isize) = 0;
    let mut s = to_string(buf);
    let mut i: usize = 0;
    while *s.offset(i as isize) != 0 {
        if *s.offset(i as isize) as i32 != '0' as i32 {
            return 1;
        }
        i = i.wrapping_add(1);
    }
    0
}
"#;

/// C5 (R615-7, the relay's control) — the receiver is wrapped and the
/// argument's own bridge (a seam: `buf.as_mut_ptr()` into the alias formal
/// the rewriter leaves raw) survives inside it, and the crate type-checks.
/// (Correction of wave-6l 054: a text replacement composes a SEAM planned in
/// the table as well — its E0308 fixture failed without any constructor. The
/// bracket additionally carries the edits the later AST passes place.)
#[test]
fn w6l_nul_c5_a_wrapped_receiver_keeps_the_argument_bridge() {
    let (source, _) = emitted_source(CONTROL_BRIDGED_ARGUMENT);
    assert!(
        source.contains("fn to_string(mut text: text_t)"),
        "{source}"
    );
    assert!(
        source.contains("fn to_boolean(mut buf: &mut [i8]"),
        "{source}"
    );
    assert!(source.contains("let mut s: &[i8] ="), "{source}");
    assert!(
        source.contains("to_string(buf.as_mut_ptr())"),
        "the argument keeps its raw bridge inside the wrapped call: {source}"
    );
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

/// W6 — both halves of the R419-3 hold exempt a literal-only source, and the
/// sibling audit states the premise at each site.
#[test]
fn w6l_nul_w6_a_literal_source_is_not_a_pending_sibling_site() {
    let decisions = super::emit_tests::decisions_of(PROBE_LITERAL_SIBLING);
    assert_eq!(
        reason(&decisions, "fmt", false),
        "<emitted>",
        "{decisions:#?}"
    );
    assert_eq!(
        reason(&decisions, "box_vertical", false),
        "<emitted>",
        "{decisions:#?}"
    );
    let (source, artifacts) = emitted_source(PROBE_LITERAL_SIBLING);
    assert!(source.contains("sprintf(path, fmt.as_ptr(),"), "{source}");
    assert!(
        source.contains("strcpy(p.as_mut_ptr(), box_vertical.as_ptr())"),
        "{source}"
    );
    // `tmp_path` (a parameter) is still a pending source at `sprintf`; the
    // literals are not.
    assert!(
        artifacts.pending_sibling_receipts.iter().all(|site| site
            .receipt
            .potential
            .site
            .argument_index
            == 2
            && site.receipt.potential.site.callee.path == "sprintf"),
        "the one pending site left is tmp_path's: {:#?}",
        artifacts.pending_sibling_receipts
    );
    let literal_rows = artifacts
        .sibling_audit_rows
        .iter()
        .filter(|row| row.outcome == super::sibling_audit::Outcome::LiteralSourceReadOnly)
        .collect::<Vec<_>>();
    assert_eq!(literal_rows.len(), 2, "{:#?}", artifacts.sibling_audit_rows);
    assert!(
        literal_rows
            .iter()
            .all(|row| row.data && row.issues.is_empty()),
        "{literal_rows:#?}"
    );
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

const CONTROL_CONVERTED_RETURN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
unsafe fn make() -> *mut i8 {
    let mut p = malloc(16) as *mut i8;
    p
}
pub unsafe fn first() -> i8 {
    let mut q = make();
    let mut c = *q.offset(1);
    free(q as *mut core::ffi::c_void);
    c
}
"#;

/// C3 — (b′) is exactly its premise: where a family DOES convert the callee's
/// return (here a Box certificate), no constructor is built over the call.
#[test]
fn w6l_nul_c3_a_converted_return_is_never_constructed_over() {
    let (source, _) = emitted_source(CONTROL_CONVERTED_RETURN);
    assert!(
        !source.contains("from_raw_parts(make()") && !source.contains("from_raw_parts_mut(make()"),
        "{source}"
    );
}

const PROBE_WIDE_LOCAL_CALLEE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn BrotliUnalignedRead32(p: *const core::ffi::c_void) -> u32 {
    *(p as *const u32)
}
unsafe fn Hash14(data: *const u8) -> u32 {
    if data.is_null() {
        return 0;
    }
    let h = BrotliUnalignedRead32(data as *const core::ffi::c_void);
    return h.wrapping_add(*data as u32);
}
pub struct Ctx {
    pub data: *const u8,
}
pub unsafe fn caller(mut ctx: *mut Ctx) -> u32 {
    Hash14((*ctx).data)
}
"#;

/// C11 (R631-3, wave-6l relay 061) — the wide access keeps its hold: the
/// callee reads four bytes (`*(p as *const u32)`) through a one-`u8` subject,
/// so the nullable twin may not release it (the R416-5 class). Formerly W8,
/// which asserted the lift; the ruling is the reverse.
#[test]
fn w6l_nul_c11_a_wider_local_callee_access_keeps_the_hold() {
    let decisions = super::emit_tests::decisions_of(PROBE_WIDE_LOCAL_CALLEE);
    assert_eq!(
        reason(&decisions, "data", true),
        "held:local-callee-access-extent",
        "{decisions:#?}"
    );
    let (_, artifacts) = emitted_source(PROBE_WIDE_LOCAL_CALLEE);
    assert!(
        !artifacts.licensed_lifts.contains("\topt-slice\t"),
        "{}",
        artifacts.licensed_lifts
    );
}

/// The same caller at a callee that reads the subject only at its element's
/// own width: both reads are `u8`, one element apart.
const PROBE_ELEMENT_WIDTH_LOCAL_CALLEE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn ReadPair(p: *const core::ffi::c_void) -> u32 {
    (*(p as *const u8) as u32).wrapping_add(*(p as *const u8).offset(1) as u32)
}
unsafe fn Hash2(data: *const u8) -> u32 {
    if data.is_null() {
        return 0;
    }
    let h = ReadPair(data as *const core::ffi::c_void);
    return h.wrapping_add(*data as u32);
}
pub struct Ctx {
    pub data: *const u8,
}
pub unsafe fn caller(mut ctx: *mut Ctx) -> u32 {
    Hash2((*ctx).data)
}
"#;

/// W8 (R615-7, STOP 4 of 054; re-cut under R631-3) — a null-tested subject
/// held at a LOCAL callee that accesses it at the element's own width takes
/// the optional slice under the same receipt (`opt-slice`, `fallback`), its
/// raw struct-field caller adapted with a null test.
#[test]
fn w6l_nul_w8_an_element_width_local_callee_row_takes_the_optional_slice() {
    let decisions = super::emit_tests::decisions_of(PROBE_ELEMENT_WIDTH_LOCAL_CALLEE);
    assert_eq!(
        reason(&decisions, "data", true),
        "<emitted>",
        "{decisions:#?}"
    );
    let (source, artifacts) = emitted_source(PROBE_ELEMENT_WIDTH_LOCAL_CALLEE);
    assert!(source.contains("fn Hash2(data: Option<&[u8]>)"), "{source}");
    assert!(
        source.contains("__crat_call_adapter_ptr.is_null()")
            && source.contains("crate::FALLBACK_SLICE_EXTENT"),
        "{source}"
    );
    let row = lift_row(&artifacts.licensed_lifts, "Hash2::data");
    assert!(row.contains("\topt-slice\tfallback\t"), "{row}");
}

/// C12 (R631-3) — a width the walk cannot state keeps the hold: the callee
/// binds `p as *const u32` to a local and reads four bytes through it, beside
/// an element-width `u8` read. The bound local is not followed, so the width
/// is unstated, not the one read that is.
const PROBE_BOUND_WIDER_LOCAL_CALLEE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn ReadBound(p: *const core::ffi::c_void) -> u32 {
    let q = p as *const u32;
    (*(p as *const u8) as u32).wrapping_add(*q)
}
unsafe fn Hash4(data: *const u8) -> u32 {
    if data.is_null() {
        return 0;
    }
    let h = ReadBound(data as *const core::ffi::c_void);
    return h.wrapping_add(*data as u32);
}
pub struct Ctx {
    pub data: *const u8,
}
pub unsafe fn caller(mut ctx: *mut Ctx) -> u32 {
    Hash4((*ctx).data)
}
"#;

#[test]
fn w6l_nul_c12_an_unstated_callee_width_keeps_the_hold() {
    let decisions = super::emit_tests::decisions_of(PROBE_BOUND_WIDER_LOCAL_CALLEE);
    assert_eq!(
        reason(&decisions, "data", true),
        "held:local-callee-access-extent",
        "{decisions:#?}"
    );
}

/// C13 (R631-3, Codex 059) — a dereference that only forms an address is not
/// an access: the callee takes `&raw const *(p as *const u8)` and reads a
/// `u32` through it, beside ordinary `u8` reads. The hold stays.
const PROBE_ADDRESS_THEN_WIDER: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn ReadVia(p: *const core::ffi::c_void) -> u32 {
    let q = &raw const *(p as *const u8);
    (*(p as *const u8) as u32).wrapping_add(q.cast::<u32>().read_unaligned())
}
unsafe fn Hash5(data: *const u8) -> u32 {
    if data.is_null() {
        return 0;
    }
    let h = ReadVia(data as *const core::ffi::c_void);
    return h.wrapping_add(*data as u32);
}
pub struct Ctx {
    pub data: *const u8,
}
pub unsafe fn caller(mut ctx: *mut Ctx) -> u32 {
    Hash5((*ctx).data)
}
"#;

#[test]
fn w6l_nul_c13_an_address_formed_by_a_dereference_keeps_the_hold() {
    let decisions = super::emit_tests::decisions_of(PROBE_ADDRESS_THEN_WIDER);
    assert_eq!(
        reason(&decisions, "data", true),
        "held:local-callee-access-extent",
        "{decisions:#?}"
    );
}

/// C14 (R631-3, Codex 059) — a wider read inside a closure the callee runs is
/// an access too.
const PROBE_CLOSURE_WIDER: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn ReadClosure(p: *const core::ffi::c_void) -> u32 {
    let wide = || unsafe { *(p as *const u32) };
    (*(p as *const u8) as u32).wrapping_add(wide())
}
unsafe fn Hash6(data: *const u8) -> u32 {
    if data.is_null() {
        return 0;
    }
    let h = ReadClosure(data as *const core::ffi::c_void);
    return h.wrapping_add(*data as u32);
}
pub struct Ctx {
    pub data: *const u8,
}
pub unsafe fn caller(mut ctx: *mut Ctx) -> u32 {
    Hash6((*ctx).data)
}
"#;

#[test]
fn w6l_nul_c14_a_wider_read_in_a_closure_keeps_the_hold() {
    let decisions = super::emit_tests::decisions_of(PROBE_CLOSURE_WIDER);
    assert_eq!(
        reason(&decisions, "data", true),
        "held:local-callee-access-extent",
        "{decisions:#?}"
    );
}

const CONTROL_ONE_ELEMENT_LOCAL: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn read_one(p: *const u32) -> u32 {
    *p
}
pub unsafe fn look(value: *const u32) -> u32 {
    if value.is_null() {
        return 0;
    }
    read_one(value)
}
"#;

/// C6 (R615-7) — the local-callee twin of C1: a null-tested subject handed to
/// a local callee that reads ONE element is no access-extent row and keeps the
/// thin optional; no lift receipt.
#[test]
fn w6l_nul_c6_a_one_element_local_callee_keeps_the_thin_optional() {
    let (source, artifacts) = emitted_source(CONTROL_ONE_ELEMENT_LOCAL);
    assert!(!source.contains("value: Option<&[u32]>"), "{source}");
    assert!(
        !artifacts.licensed_lifts.contains("look::value"),
        "{}",
        artifacts.licensed_lifts
    );
}

/// brotli `BrotliCreateHqZopfliBackwardReferences::dist_cache#9`: `memcpy`
/// both ways of `4 * size_of::<c_int>()` bytes — four elements spelled in
/// bytes, at two exact sites.
const PROBE_DIST_CACHE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_snake_case)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
unsafe fn ZopfliRefs(mut num_bytes: u64, mut dist_cache: *mut i32) {
    let mut orig_dist_cache: [i32; 4] = [0; 4];
    memcpy(orig_dist_cache.as_mut_ptr() as *mut core::ffi::c_void,
        dist_cache as *const core::ffi::c_void,
        (4 as i32 as u64).wrapping_mul(::std::mem::size_of::<i32>() as u64));
    if num_bytes > 1 {
        memcpy(dist_cache as *mut core::ffi::c_void,
            orig_dist_cache.as_mut_ptr() as *const core::ffi::c_void,
            (4 as i32 as u64).wrapping_mul(::std::mem::size_of::<i32>() as u64));
    }
}
pub struct State {
    pub dist_cache_: [i32; 16],
}
pub unsafe fn caller(mut s: *mut State, mut n: u64) {
    ZopfliRefs(n, ((*s).dist_cache_).as_mut_ptr());
}
"#;

/// The subject's contract-extent length plan, rendered.
fn contract_length(fixture: &str, subject: &str) -> String {
    ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(fixture),
        |tcx| {
            let (table, _) = super::decide_table_with_ctx(tcx)?;
            let (key, _) = table
                .entries
                .iter()
                .find(|(entry, _)| entry.param_name.as_deref() == Some(subject))
                .map(|(entry, decision)| ((entry.fn_did, entry.hir_id), decision))
                .ok_or_else(|| format!("no subject {subject}"))?;
            Ok::<_, String>(
                table
                    .contract_extent_promotions
                    .get(&key)
                    .map_or_else(|| "no-promotion".to_owned(), |p| format!("{:?}", p.length)),
            )
        },
    )
    .expect("fixture compiles")
    .expect("subject found")
}

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// W9 (R615-7, STOP 2) — the count's value divided by the pointee's size is
/// an exact element count, the two sites agree on it, and every caller
/// constructs over it instead of the §77 fallback.
#[test]
fn w6l_nul_w9_a_constant_byte_count_is_an_element_count_at_every_caller() {
    let length = contract_length(PROBE_DIST_CACHE, "dist_cache");
    assert!(length.starts_with("Evidence { elements: \"4\""), "{length}");
    let (source, _) = emitted_source(PROBE_DIST_CACHE);
    let source = flat(&source);
    assert!(
        source.contains("fn ZopfliRefs(mut num_bytes: u64, mut dist_cache: &mut [i32])"),
        "{source}"
    );
    assert!(
        source.contains(
            "core::slice::from_raw_parts_mut(((*s).dist_cache_).as_mut_ptr(), (4) as usize)"
        ),
        "{source}"
    );
    assert!(!source.contains("FALLBACK_SLICE_EXTENT"), "{source}");
}

/// C7 — a constant that is not a whole number of elements claims none.
const CONTROL_PARTIAL_ELEMENT: &str = r#"
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

/// C8 — two constant sites that disagree are two requirements. The caller
/// hands an initialized array, so the WRITE site is a site too (a write
/// position counts only over initialized elements).
const CONTROL_UNEQUAL_CONSTANTS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_snake_case)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
unsafe fn refs(mut num_bytes: u64, mut dist_cache: *mut i32) {
    let mut orig: [i32; 4] = [0; 4];
    memcpy(orig.as_mut_ptr() as *mut core::ffi::c_void,
        dist_cache as *const core::ffi::c_void,
        (4 as u64).wrapping_mul(::std::mem::size_of::<i32>() as u64));
    if num_bytes > 1 {
        memcpy(dist_cache as *mut core::ffi::c_void,
            orig.as_mut_ptr() as *const core::ffi::c_void,
            (2 as u64).wrapping_mul(::std::mem::size_of::<i32>() as u64));
    }
}
pub struct State {
    pub dist_cache_: [i32; 16],
}
pub unsafe fn caller(mut s: *mut State, mut n: u64) {
    refs(n, ((*s).dist_cache_).as_mut_ptr());
}
"#;

/// C9 — a runtime byte count over a sized pointee proves no units.
const CONTROL_RUNTIME_BYTES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_snake_case)]
extern "C" {
    fn memcpy(d: *mut core::ffi::c_void, s: *const core::ffi::c_void, n: u64) -> *mut core::ffi::c_void;
}
unsafe fn copy_in(mut dst: *mut u8, mut src: *const i32, mut n: u64) {
    memcpy(dst as *mut core::ffi::c_void, src as *const core::ffi::c_void,
        n.wrapping_mul(::std::mem::size_of::<i32>() as u64));
}
pub unsafe fn caller(mut d: *mut u8, mut s: *const i32, mut n: u64) {
    copy_in(d, s, n);
}
"#;

#[test]
fn w6l_nul_c7_a_partial_element_constant_stays_fallback() {
    let length = contract_length(CONTROL_PARTIAL_ELEMENT, "dist_cache");
    assert!(!length.starts_with("Evidence"), "{length}");
    let (source, _) = emitted_source(CONTROL_PARTIAL_ELEMENT);
    assert!(!flat(&source).contains("(1) as usize"), "{source}");
}

#[test]
fn w6l_nul_c8_unequal_constant_sites_stay_fallback() {
    let length = contract_length(CONTROL_UNEQUAL_CONSTANTS, "dist_cache");
    assert_eq!(length, "Fallback(MultipleRequirements)");
    let (source, _) = emitted_source(CONTROL_UNEQUAL_CONSTANTS);
    let source = flat(&source);
    assert!(!source.contains("(4) as usize"), "{source}");
    assert!(!source.contains("(2) as usize"), "{source}");
}

#[test]
fn w6l_nul_c9_a_runtime_byte_count_stays_unproved() {
    let length = contract_length(CONTROL_RUNTIME_BYTES, "src");
    assert!(!length.starts_with("Evidence"), "{length}");
}

/// C10 (Codex review, 055 round 2) — the wrapped call is an IMPORTED call of
/// a surfaced helper (`start` is a fn-pointer value, so it keeps a raw outer
/// and its callers call `__crat_safe_start`). The helper-path pass, which runs
/// after the bracket, qualifies the call by its callee's span: the bracket
/// must keep that span, or the call is E0425.
const CONTROL_BRACKETED_IMPORTED_HELPER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
extern "C" {
    fn getenv(name: *const i8) -> *mut i8;
}
pub mod provider {
    pub unsafe fn start(p: *const i32) -> *const i8 {
        if *p == 0 {
            return 0 as *const i8;
        }
        crate::getenv(b"HOME\0" as *const u8 as *const i8) as *const i8
    }
    pub fn install() {
        let _callback: unsafe fn(*const i32) -> *const i8 = start;
    }
}
pub mod consumer {
    use crate::provider::start;
    pub unsafe fn imported(p: *const i32) -> i32 {
        let mut s = start(p);
        let mut i: usize = 0;
        while *s.offset(i as isize) != 0 {
            i = i.wrapping_add(1);
        }
        i as i32
    }
}
"#;

fn emitted_with_exposure(input: &str) -> String {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = crate::bo_rewriter::ast_transform::capture_ast(tcx).unwrap();
        let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::bo_rewriter::A5Mode::PreciseReplay,
                Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let emission = crate::bo_rewriter::emit_files(
            tcx,
            &table,
            &Default::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        let reverts = crate::bo_rewriter::ast_transform::revert_set_from_classes_and_atoms(
            &emission.plan.held_classes(),
            &Default::default(),
            &table,
        )
        .unwrap();
        crate::bo_rewriter::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .unwrap()
        .0
        .into_values()
        .next()
        .unwrap()
    })
    .unwrap()
}

#[test]
fn w6l_nul_c10_a_bracketed_imported_helper_call_is_qualified() {
    let source = emitted_with_exposure(CONTROL_BRACKETED_IMPORTED_HELPER);
    let flat = flat(&source);
    assert!(flat.contains("fn __crat_safe_start"), "{source}");
    assert!(flat.contains("let mut s: &[i8] ="), "{source}");
    assert!(
        flat.contains("core::slice::from_raw_parts(crate::provider::__crat_safe_start(p),"),
        "{source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}
