//! Reduced from urlparser url_get_port → url_get_hostname: a shared `url`
//! reaches a raw `*mut c_char` formal of a callee that only reads it and
//! returns a FRESH string, which the caller later frees. The type-backed walk
//! assumed the result may descend from `url` and read the free as a write.
const INPUT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
use core::ffi::c_void;
pub struct Url { len: i32, tag: *mut u8 }
unsafe extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn free(p: *mut c_void);
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn url_get_hostname(url: *mut Url, cache: *mut i32) -> *mut Url {
    let ret = malloc(core::mem::size_of::<Url>()) as *mut Url;
    *cache = (*url).len;
    (*ret).len = (*url).len;
    ret
}
pub unsafe fn url_get_port(url: *mut Url, cache: *mut i32) -> i32 {
    let hostname = url_get_hostname(url, cache);
    if hostname.is_null() { return 0; }
    let port = (*hostname).len + 1;
    free(hostname as *mut c_void);
    port
}
"#;

fn hostname_arg0_disposition(input: &str) -> String {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        for (subject, decision) in &table.entries {
            println!("DECISION {} {decision:?}", subject.label);
        }
        let rows = ctx.raw_boundary.receipts_tsv();
        println!("DISPOSITIONS\n{rows}");
        rows.lines()
            .find(|line| {
                line.starts_with("url_get_port\t") && line.contains("\turl_get_hostname\t0\t")
            })
            .expect("the hostname arg0 site is inventoried")
            .to_owned()
    })
    .expect("input type-checks")
}

#[test]
fn wave6r_url_fresh_result_callee_discharges_write_through_shared_view() {
    let row = hostname_arg0_disposition(INPUT);
    assert!(row.contains("\tshared-ref-to-mut-raw\t"), "{row}");
    assert!(!row.contains("write-through-shared-view"), "{row}");
    let source = super::emitted(INPUT);
    assert!(
        source.contains("url_get_hostname(url: *mut Url"),
        "{source}"
    );
    assert!(
        source.contains("url_get_hostname(core::ptr::from_ref(url).cast_mut(), "),
        "{source}"
    );
}

fn held(input: &str) {
    let row = hostname_arg0_disposition(input);
    assert!(
        row.contains("\tblocked\t")
            && row.contains("ordinary-argument-permission:write-through-shared-view"),
        "the hold must stand: {row}"
    );
}

/// The body scan on its own, for the shapes the decision engine re-kinds
/// before they reach a disposition row.
fn scan(input: &str, function: &str, index: usize) -> bool {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let functions = tcx.hir_body_owners().collect::<Vec<_>>();
        let target = functions
            .iter()
            .copied()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == function)
            .expect("the scanned function exists");
        super::super::wave6r_child_access::position_is_descendant_free(
            tcx, &functions, target, index,
        )
    })
    .expect("input type-checks")
}

const SCAN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, static_mut_refs)]
use core::ffi::c_void;
pub struct Url { len: i32, tag: *mut u8 }
pub static mut KEEP: *mut c_void = core::ptr::null_mut();
unsafe extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn strchr(s: *const core::ffi::c_char, c: i32) -> *mut core::ffi::c_char;
}
pub unsafe fn fresh(url: *mut Url) -> *mut Url {
    let ret = malloc(core::mem::size_of::<Url>()) as *mut Url;
    (*ret).len = (*url).len;
    ret
}
pub unsafe fn returns_argument(url: *mut Url) -> *mut Url { url }
pub unsafe fn returns_copy(url: *mut Url) -> *mut Url { let copy = url; copy }
pub unsafe fn stores_libc_alias(url: *mut Url) -> i32 {
    KEEP = strchr(url as *const core::ffi::c_char, 0) as *mut c_void;
    (*url).len
}
pub unsafe fn returns_through_local(url: *mut Url) -> *mut Url { returns_copy(url) }
pub unsafe fn passes_to_fresh(url: *mut Url) -> *mut Url { fresh(url) }
"#;

#[test]
fn wave6r_scan_fresh_result_is_descendant_free() {
    assert!(scan(SCAN, "fresh", 0));
    assert!(
        scan(SCAN, "passes_to_fresh", 0),
        "a local callee that is descendant-free keeps the caller free"
    );
}

#[test]
fn wave6r_scan_returned_argument_is_not_descendant_free() {
    assert!(!scan(SCAN, "returns_argument", 0));
    assert!(
        !scan(SCAN, "returns_copy", 0),
        "a transparent copy reaching the return place"
    );
}

#[test]
fn wave6r_scan_libc_returned_alias_stored_is_not_descendant_free() {
    assert!(
        !scan(SCAN, "stores_libc_alias", 0),
        "strchr's row returns an alias of arg0"
    );
}

#[test]
fn wave6r_scan_local_callee_returning_alias_is_not_descendant_free() {
    assert!(!scan(SCAN, "returns_through_local", 0));
}

/// A `Rust`-ABI pointer method other than `is_null` (`offset`) derives a new
/// pointer the scan cannot follow through a contract row: refuse.
#[test]
fn wave6r_scan_core_offset_result_stored_is_not_descendant_free() {
    let input = SCAN.replace(
        "pub unsafe fn fresh(",
        "pub unsafe fn stores_offset(url: *mut Url) -> i32 { KEEP = url.offset(1) as *mut c_void; (*url).len }\npub unsafe fn null_tests(url: *mut Url) -> i32 { if url.is_null() { return 0; } (*url).len }\npub unsafe fn fresh(",
    );
    assert!(!scan(&input, "stores_offset", 0));
    assert!(
        scan(&input, "null_tests", 0),
        "is_null keeps the position free"
    );
}
