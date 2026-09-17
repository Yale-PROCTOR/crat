//! Reduced from brotli `StoreRangeH35 → StoreH35 → StoreH3 → HashBytesH3`
//! (report 018 claim 4): the callee reads the shared `data` through an ADDRESS
//! taken under an alias — `HashBytesH3(&*data.offset((ix & mask) as isize))` —
//! which the child walk refused outright. An address under an alias points
//! into the same pointee, so it joins the alias closure and the same scan
//! proves its uses; what leaves the closure (a store through a projection, a
//! return, an open callee) still refuses.
const STORE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, static_mut_refs)]
pub struct H3 { buckets: [u32; 8], num: u32 }
pub struct H35 { ha: H3, hb: H3 }
pub static mut KEEP: *const u8 = core::ptr::null();
unsafe extern "C" {
    fn sink(p: *const u8);
}
unsafe fn hash_bytes(data: *const u8) -> usize { (*data as usize) & 7 }
unsafe fn hash_and_keep(data: *const u8) -> usize { KEEP = data; (*data as usize) & 7 }
unsafe fn store_keeping(self_0: *mut H3, data: *const u8, ix: usize) {
    let key = hash_and_keep(&*data.offset(ix as isize));
    (*self_0).buckets[key] = ix as u32;
}
unsafe fn store_h3(self_0: *mut H3, data: *const u8, mask: usize, ix: usize) {
    let key = hash_bytes(&*data.offset((ix & mask) as isize));
    (*self_0).buckets[key] = ix as u32;
}
unsafe fn store_h35(self_0: *mut H35, data: *const u8, mask: usize, ix: usize) {
    store_h3(&mut (*self_0).ha, data, mask, ix);
    store_h3(&mut (*self_0).hb, data, mask, ix);
}
unsafe fn store_and_keep(self_0: *mut H3, data: *const u8, mask: usize, ix: usize) {
    let p = &*data.offset((ix & mask) as isize);
    KEEP = p;
    (*self_0).num = *p as u32;
}
unsafe fn store_and_return(self_0: *mut H3, data: *const u8, ix: usize) -> *const u8 {
    let p = &raw const *data.offset(ix as isize);
    (*self_0).num = *p as u32;
    p
}
unsafe fn store_and_sink(self_0: *mut H3, data: *const u8, ix: usize) {
    let p = &*data.offset(ix as isize);
    sink(p);
    (*self_0).num = *p as u32;
}
unsafe fn store_through_out(self_0: *mut H3, out: *mut *const u8, data: *const u8, ix: usize) {
    let p = &*data.offset(ix as isize);
    *out = p;
    (*self_0).num = *p as u32;
}
pub unsafe fn store_range(self_0: *mut H35, data: *const u8, mask: usize, ix_start: usize, ix_end: usize) {
    let mut ix = ix_start;
    while ix < ix_end {
        store_h35(self_0, data, mask, ix);
        ix += 1;
    }
}
"#;

fn scan_store(function: &str, index: usize) -> Option<String> {
    ::utils::compilation::run_compiler_on_str(STORE, |tcx| {
        let functions = tcx.hir_body_owners().collect::<Vec<_>>();
        let target = functions
            .iter()
            .copied()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == function)
            .expect("the scanned function exists");
        super::super::wave6r_child_access::position_refusal(tcx, &functions, target, index)
    })
    .expect("input type-checks")
}

#[test]
fn wave6r_address_under_an_alias_read_through_is_free() {
    assert_eq!(scan_store("store_h3", 1), None);
    assert_eq!(scan_store("store_h35", 1), None);
    assert_eq!(scan_store("store_range", 1), None);
}

#[test]
fn wave6r_address_under_an_alias_that_leaves_the_closure_refuses() {
    assert_eq!(
        scan_store("store_keeping", 1).as_deref(),
        Some("hash_and_keep@0:use-hands-out")
    );
    assert_eq!(
        scan_store("store_and_keep", 1).as_deref(),
        Some("use-hands-out")
    );
    assert_eq!(
        scan_store("store_and_return", 1).as_deref(),
        Some("use-hands-out")
    );
    assert_eq!(
        scan_store("store_through_out", 2).as_deref(),
        Some("use-hands-out")
    );
}

/// The derived address is the SCAN's business, because this frame's retention
/// walk does not track `&*p`: it reads `store_and_sink`'s parameter as
/// `no-retain` although the address reaches an unmodeled `extern "C"` sink
/// that may keep it. The scan refuses the position, so the discharge — which
/// needs BOTH — cannot fire. (wave-6v2's R412-1 edge closes the row side on
/// the batch-9 composition; this conjunct keeps the scan sound on its own.)
#[test]
fn wave6r_address_handed_to_an_unmodeled_foreign_callee_is_refused_by_the_scan() {
    assert_eq!(
        scan_store("store_and_sink", 1).as_deref(),
        Some("derived-address-into-open-callee:sink")
    );
    let row = ::utils::compilation::run_compiler_on_str(STORE, |tcx| {
        let (_, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let rows = ctx.retention.to_tsv();
        println!("RETENTION\n{rows}");
        rows.lines()
            .find(|line| line.starts_with("store_and_sink\t") && line.contains("\t1\t"))
            .expect("the sink position has a row")
            .to_owned()
    })
    .expect("input type-checks");
    // Two admissible readings (R217-2(a)): on this frame the row is BLIND to
    // the derived address (`no-retain`), on the batch-10 composition
    // wave-6v2's R412-1 edge sees it and the row is open (`unknown`). Either
    // way the scan refuses the position, so the discharge cannot fire.
    assert!(
        row.contains("\tno-retain\t") || row.contains("\tunknown\t"),
        "the row is blind or open, never a proof: {row}"
    );
}

/// The site the extension is for: the shared `data` at a raw formal of a
/// callee that only reads it through such an address.
#[test]
fn wave6r_address_under_an_alias_site_delivers() {
    let (rows, inner) = ::utils::compilation::run_compiler_on_str(STORE, |tcx| {
        let (_, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let rows = ctx.raw_boundary.receipts_tsv();
        println!("DISPOSITIONS\n{rows}");
        println!("RETENTION\n{}", ctx.retention.to_tsv());
        let pick = |caller: &str, callee: &str| {
            rows.lines()
                .filter(|line| {
                    line.starts_with(&format!("{caller}\t"))
                        && line.contains(&format!("\t{callee}\t"))
                })
                .map(str::to_owned)
                .collect::<Vec<_>>()
        };
        (
            pick("store_range", "store_h35\t1"),
            pick("store_h3", "hash_bytes\t0"),
        )
    })
    .expect("input type-checks");
    assert!(!rows.is_empty(), "the store_h35 site is inventoried");
    assert!(!inner.is_empty(), "the hash_bytes site is inventoried");
    // The invariant this build owns: NO position of the chain is held by the
    // child walk any more. Which of the two sites carries the delivery is
    // frame-dependent (R217-2(a)): on this frame the outer one does, on the
    // batch-10 composition the subject of the outer one is degraded by
    // `held:local-callee-access-extent` (another family) and the inner one
    // delivers instead.
    assert!(
        !rows
            .iter()
            .chain(inner.iter())
            .any(|row| row.contains("write-through-shared-view")
                || row.contains("raw-boundary-returned-child-permission")),
        "the child walk holds nothing here: {rows:?} {inner:?}"
    );
    assert!(
        rows.iter()
            .chain(inner.iter())
            .any(|row| row.contains("\tT1\t")),
        "the read-through address delivers somewhere in the chain: {rows:?} {inner:?}"
    );
}

/// The child-access receipt (relay wave-6r/017): one row per callee position
/// the discharge looked at, naming the outcome and — where it held — the
/// conjunct that refused. Instrument-only: no decision reads it.
#[test]
fn wave6r_child_access_receipt_names_the_outcome_and_the_reason() {
    let receipt = ::utils::compilation::run_compiler_on_str(STORE, |tcx| {
        let (_, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let receipt = ctx.retention.child_access.clone();
        println!("CHILD-ACCESS\n{receipt}");
        receipt
    })
    .expect("input type-checks");
    assert!(
        receipt.starts_with(super::super::wave6r_child_access::CHILD_ACCESS_HEADER),
        "{receipt}"
    );
    assert!(
        receipt
            .lines()
            .any(|row| row.starts_with("hash_bytes\t0\t") && row.contains("\tdischarged\t-")),
        "the read-through position is discharged: {receipt}"
    );
    assert!(
        receipt
            .lines()
            .any(|row| row.starts_with("hash_and_keep\t0\t")
                && row.contains("\theld\tcallee-row-retains")),
        "a position held at the ROW names that, before the scan runs: {receipt}"
    );
}

const URLP: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
use core::ffi::{c_char, c_int, c_void};
unsafe extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn free(p: *mut c_void);
    fn strlen(s: *const c_char) -> usize;
    fn strcpy(d: *mut c_char, s: *const c_char) -> *mut c_char;
    fn strcmp(a: *const c_char, b: *const c_char) -> c_int;
    fn sscanf(s: *const c_char, f: *const c_char, ...) -> c_int;
}
pub unsafe fn strdup_local(str: *const c_char) -> *mut c_char {
    let n = strlen(str) + 1;
    let dup = malloc(n) as *mut c_char;
    if !dup.is_null() { strcpy(dup, str); }
    dup
}
unsafe fn strff(mut ptr: *mut c_char, n: c_int) -> *mut c_char {
    let mut i = 0;
    while i < n { ptr = ptr.offset(1); i += 1; }
    strdup_local(ptr)
}
unsafe fn get_part(url: *mut c_char, format: *const c_char, l: c_int) -> *mut c_char {
    let mut has = false;
    let tmp = malloc(1) as *mut c_char;
    let tmp_url = strdup_local(url);
    let mut fmt_url = strdup_local(url);
    let mut ret = malloc(1) as *mut c_char;
    if tmp.is_null() || tmp_url.is_null() || fmt_url.is_null() || ret.is_null() {
        return core::ptr::null_mut();
    }
    fmt_url = strff(fmt_url, l);
    sscanf(fmt_url, format, tmp);
    if 0 != strcmp(tmp, tmp_url) { has = true; ret = strdup_local(tmp); }
    free(tmp as *mut c_void);
    free(tmp_url as *mut c_void);
    free(fmt_url as *mut c_void);
    if has { ret } else { core::ptr::null_mut() }
}
pub unsafe fn url_get_path(url: *mut c_char) -> *mut c_char {
    get_part(url, b"%*[^/]%s\0" as *const u8 as *const c_char, 0)
}
"#;

fn scan_url(function: &str, index: usize) -> Option<String> {
    ::utils::compilation::run_compiler_on_str(URLP, |tcx| {
        let functions = tcx.hir_body_owners().collect::<Vec<_>>();
        let target = functions
            .iter()
            .copied()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == function)
            .expect("the scanned function exists");
        super::super::wave6r_child_access::position_refusal(tcx, &functions, target, index)
    })
    .expect("input type-checks")
}

/// Report 018 claim 3 left urlparser's six `url#1` positions unattributed:
/// they are `no-retain` at every site and still held. On the reduction of
/// `url_get_path → get_part → strdup/strff` the SCAN frees every position, so
/// the corpus hold is not the child walk's — the receipt names it at the
/// batch-10 census (relay 017 granted the column).
#[test]
fn wave6r_urlparser_get_part_chain_is_descendant_free() {
    assert_eq!(scan_url("get_part", 0), None);
    assert_eq!(scan_url("strdup_local", 0), None);
    assert_eq!(scan_url("strff", 0), None);
    assert_eq!(scan_url("url_get_path", 0), None);
    let receipt = ::utils::compilation::run_compiler_on_str(URLP, |tcx| {
        let (_, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let receipt = ctx.retention.child_access.clone();
        println!("CHILD-ACCESS\n{receipt}");
        receipt
    })
    .expect("input type-checks");
    assert!(
        !receipt
            .lines()
            .any(|row| row.starts_with("get_part\t0\t") && row.contains("\theld\t")),
        "the reduction's chain is not held by the child walk: {receipt}"
    );
}

/// lodepng `alloc_string::in_0#1` (report 018 claim 3, relay 018): the only
/// open step on the position is `offset_from`, which yields a COUNT — it reads
/// the receiver and retains nothing, exactly like `is_null`.
const OFFSET_FROM: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
use core::ffi::c_void;
unsafe extern "C" {
    fn malloc(n: usize) -> *mut c_void;
    fn memcpy(d: *mut c_void, s: *const c_void, n: usize) -> *mut c_void;
}
unsafe fn span(begin: *const u8, end: *const u8) -> usize {
    end.offset_from(begin) as usize
}
pub unsafe fn alloc_string(in_0: *const u8, end: *const u8) -> *mut u8 {
    let size = span(in_0, end);
    let out = malloc(size + 1) as *mut u8;
    memcpy(out as *mut c_void, in_0 as *const c_void, size);
    out
}
"#;

#[test]
fn wave6r_offset_from_is_a_known_no_retain_read() {
    let row = ::utils::compilation::run_compiler_on_str(OFFSET_FROM, |tcx| {
        let (_, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let rows = ctx.retention.to_tsv();
        println!("RETENTION\n{rows}");
        rows.lines()
            .find(|line| line.starts_with("span\t") && line.contains("\t1\t"))
            .expect("the span position has a row")
            .to_owned()
    })
    .expect("input type-checks");
    assert!(row.contains("\tno-retain\t"), "{row}");
}
