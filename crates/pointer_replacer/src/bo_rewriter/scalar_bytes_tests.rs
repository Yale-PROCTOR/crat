//! **A scalar formal read only as bytes is a byte region (wave-6b, R609-4).**
//!
//! binn's `copy_be16/32/64` (rs-crown-derived/binn/lib.rs:190–223) take
//! `*mut uN_0` formals whose only use is `p as *mut c_uchar`, the source of a
//! byte view (W6B-6). Every one of their 17 callers passes a cast: a byte
//! cursor into the serialized buffer, the address of an integer local, the
//! void payload, or a union field. A typed `&mut u32_0` over a byte cursor is a
//! misaligned reference, so co-conversion blocks the typed form
//! (`arg-cast-form-unbuilt`) and the blocked formal withholds the byte views
//! too. The form that is sound at every call is the formal as a byte region of
//! exactly the scalar's size: `&mut [u8]` / `&[u8]` of `size_of::<T>()`, built
//! at each call from the caller's own pointer, which needs no alignment.
//!
//! Where the two byte-region formals of one call are not proven disjoint, the
//! READ side stays raw (`pair-raw-view`) and the WRITE side converts under the
//! T2 raw-view receipt — the practice at binn's `GetValue` sites (R609-4 (a)).

use super::decision::{Decision, DegradeReason};
use crate::analyses::borrow_ownership::a5_overlap::{A5Mode, WholeProgramAttestation};

fn compact(source: &str) -> String {
    source.chars().filter(|c| !c.is_whitespace()).collect()
}

/// The fixture's `libc` names, for a standalone build: appended, so the
/// fixture's inner attributes stay first.
const LIBC_SHIM: &str = "mod libc { pub type c_int = i32; pub type c_short = i16; pub type c_uchar = u8; pub type c_void = core::ffi::c_void; }";

fn run_binary(source: &str) -> Vec<u8> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("crat-w6b-bytes-{}-{id}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let input = dir.join("main.rs");
    let binary = dir.join("main");
    std::fs::write(&input, source).unwrap();
    let compiled = std::process::Command::new("rustc")
        .args(["--edition=2021", "-Awarnings"])
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "runtime build: {}\n{source}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let run = std::process::Command::new(&binary).output().unwrap();
    assert!(
        run.status.success(),
        "runtime: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(&dir).unwrap();
    run.stdout
}

fn precise() -> Option<(A5Mode, Option<WholeProgramAttestation>)> {
    Some((
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
    ))
}

/// The census's own configuration (precise replay over the frozen graph), so
/// the A5 site proofs and wave-6p's pair certificates are what they are at a
/// census.
fn decisions(input: &str) -> Vec<(String, String, Decision)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) =
            super::decide_table_with_ctx_config(tcx, precise()).expect("fixture decision");
        table
            .entries
            .iter()
            .map(|(subject, decision)| {
                (
                    tcx.item_name(subject.fn_did.to_def_id()).to_string(),
                    subject
                        .label
                        .rsplit("::")
                        .next()
                        .unwrap_or_default()
                        .to_owned(),
                    decision.clone(),
                )
            })
            .collect()
    })
    .expect("fixture compiles")
}

fn decision<'a>(
    rows: &'a [(String, String, Decision)],
    function: &str,
    name: &str,
) -> &'a Decision {
    rows.iter()
        .find(|(f, n, _)| f == function && n == name)
        .map(|(_, _, d)| d)
        .unwrap_or_else(|| panic!("no subject {function}::{name}"))
}

fn is_slice(decision: &Decision, mutable: bool) -> bool {
    matches!(decision, Decision::Slice { mutable: m, .. } if *m == mutable)
}

/// R934-1 (i): held beside a pair not shown disjoint.
fn is_pair_held(decision: &Decision) -> bool {
    matches!(decision, Decision::Degraded(d)
        if matches!(d.reason, DegradeReason::PairNotShownDisjoint { .. }))
}

fn is_pair_raw_view(decision: &Decision) -> bool {
    matches!(decision, Decision::Degraded(d) if d.reason == DegradeReason::PairRawView)
}

/// The emitted source and the region bridges' `(retention, waiver)`, under the
/// census configuration.
fn emitted(
    input: &str,
) -> (
    String,
    Vec<(
        String,
        super::bridge_receipt::BridgeRetentionTier,
        Option<String>,
    )>,
) {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("capture");
        let (table, ctx) =
            super::decide_table_with_ctx_config(tcx, precise()).expect("fixture decision");
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("emission");
        let held = emission.plan.held_classes();
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &held,
            &std::collections::BTreeSet::new(),
            &table,
        )
        .expect("reverts");
        let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("AST emission");
        let events = emission
            .plan
            .bridge_events(&std::collections::BTreeSet::new())
            .iter()
            .filter(|event| event.state != super::bridge_receipt::BridgeReceiptState::Dropped)
            .map(|event| {
                (
                    event.site.bridge_kind.to_string(),
                    event.retention,
                    event.waiver_id.clone(),
                )
            })
            .collect();
        (files.into_values().next().expect("one file"), events)
    })
    .expect("fixture compiles")
}

/// binn.rs:190–223 verbatim, and four callers with the corpus's four argument
/// shapes. Every cursor is read out of the object (`(*item).pbuf`), as binn's
/// are, so the caller's pointer stays raw.
pub(super) const COPY_BE: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type u16_0 = u16;
pub type u32_0 = u32;
pub type u64_0 = u64;
#[repr(C)]
#[derive(Copy, Clone)]
pub union C2RustUnnamed {
    pub vint16: libc::c_short,
    pub vint32: libc::c_int,
    pub vint64: i64,
}
#[repr(C)]
pub struct binn {
    pub pbuf: *mut libc::c_void,
    pub used_size: libc::c_int,
    pub c2rust_unnamed: C2RustUnnamed,
}
unsafe extern "C" fn copy_be16(mut pdest: *mut u16_0,
    mut psource: *mut u16_0) {
    let mut source = psource as *mut libc::c_uchar;
    let mut dest = pdest as *mut libc::c_uchar;
    *dest.offset(0 as libc::c_int as isize) =
        *source.offset(1 as libc::c_int as isize);
    *dest.offset(1 as libc::c_int as isize) =
        *source.offset(0 as libc::c_int as isize);
}
unsafe extern "C" fn copy_be32(mut pdest: *mut u32_0,
    mut psource: *mut u32_0) {
    let mut source = psource as *mut libc::c_uchar;
    let mut dest = pdest as *mut libc::c_uchar;
    *dest.offset(0 as libc::c_int as isize) =
        *source.offset(3 as libc::c_int as isize);
    *dest.offset(1 as libc::c_int as isize) =
        *source.offset(2 as libc::c_int as isize);
    *dest.offset(2 as libc::c_int as isize) =
        *source.offset(1 as libc::c_int as isize);
    *dest.offset(3 as libc::c_int as isize) =
        *source.offset(0 as libc::c_int as isize);
}
unsafe extern "C" fn copy_be64(mut pdest: *mut u64_0,
    mut psource: *mut u64_0) {
    let mut source = psource as *mut libc::c_uchar;
    let mut dest = pdest as *mut libc::c_uchar;
    let mut i: libc::c_int = 0;
    i = 0 as libc::c_int;
    while i < 8 as libc::c_int {
        *dest.offset(i as isize) =
            *source.offset((7 as libc::c_int - i) as isize);
        i += 1;
    }
}
/// binn_map_set_raw:854 — a byte cursor receives an integer local.
pub unsafe fn put_id(mut item: *mut binn, mut id: libc::c_int) {
    let mut p = ((*item).pbuf as *mut libc::c_uchar).offset((*item).used_size as isize);
    copy_be32(p as *mut u32_0, &mut id as *mut libc::c_int as *mut u32_0);
    (*item).used_size += 4 as libc::c_int;
}
/// read_map_id:650 — an integer local receives a byte cursor.
pub unsafe fn read_id(mut item: *mut binn, mut pos: libc::c_int) -> libc::c_int {
    let mut id: libc::c_int = 0;
    let mut p = ((*item).pbuf as *mut libc::c_uchar).offset(pos as isize);
    copy_be32(&mut id as *mut libc::c_int as *mut u32_0, p as *mut u32_0);
    return id;
}
/// AddValue:1029 — a byte cursor receives the void payload.
pub unsafe fn put_value16(mut item: *mut binn, mut pvalue: *mut libc::c_void) {
    let mut p = ((*item).pbuf as *mut libc::c_uchar).offset((*item).used_size as isize);
    copy_be16(p as *mut u16_0, pvalue as *mut u16_0);
    (*item).used_size += 2 as libc::c_int;
}
/// GetValue:1432 — a union field receives a byte cursor.
pub unsafe fn get_value64(mut item: *mut binn, mut pos: libc::c_int, mut value: *mut binn) {
    let mut p = ((*item).pbuf as *mut libc::c_uchar).offset(pos as isize);
    copy_be64(&mut (*value).c2rust_unnamed.vint64 as *mut i64 as *mut u64_0, p as *mut u64_0);
}
"#;

/// The formals are byte regions of the scalar's size and the byte views
/// deliver. On the base every formal is `arg-cast-form-unbuilt` and the views
/// are withheld with them. **R934-1 (i) (the seat on 149f; R833-1):**
/// `copy_be16` / `copy_be64` are called at a pair the proofs do not clear (a
/// cursor loaded from `item` beside the payload), so their written formal is
/// held raw with the read one; `copy_be32`'s calls are certified and are the
/// byte-region witness (wave-5d 150).
#[test]
fn w6b_a_scalar_formal_read_as_bytes_is_a_byte_region() {
    let rows = decisions(COPY_BE);
    for function in ["copy_be16", "copy_be64"] {
        assert!(
            is_pair_held(decision(&rows, function, "pdest")),
            "{function}::pdest beside an unproven pair is held: {:?}",
            decision(&rows, function, "pdest")
        );
    }
    for function in ["copy_be32"] {
        assert!(
            is_slice(decision(&rows, function, "pdest"), true),
            "{function}::pdest is a mutable byte region: {:?}",
            decision(&rows, function, "pdest")
        );
        let psource = decision(&rows, function, "psource");
        assert!(
            is_slice(psource, false) || is_pair_raw_view(psource),
            "{function}::psource is a shared byte region, or the raw view of an unproven pair: {psource:?}"
        );
    }
    // copy_be32's two sites pass a stack local's address beside a heap
    // cursor: certified disjoint, so both sides convert.
    assert!(
        is_slice(decision(&rows, "copy_be32", "psource"), false),
        "copy_be32::psource: {:?}",
        decision(&rows, "copy_be32", "psource")
    );
    let (source, _) = emitted(COPY_BE);
    let c = compact(&source);
    // The count names the RESOLVED scalar, as W6B-6's views always have.
    for (function, width) in [("copy_be32", "u32")] {
        assert!(
            c.contains(&format!("fn{function}(mutpdest:&mut[u8],")),
            "{function}: the written formal is a byte region: {source}"
        );
        assert!(
            c.contains(&format!("letmutdest:&mut[u8]=core::slice::from_raw_parts_mut(pdest.as_mut_ptr()as*mutlibc::c_uchar,core::mem::size_of::<{width}>())")),
            "{function}: the byte view is a child of the formal's region: {source}"
        );
    }
    // The read views deliver as exact byte slices where the region does
    // (R422-7: one scalar's storage, never a fallback extent).
    assert!(
        c.matches("letmutsource:&[u8]=core::slice::from_raw_parts(")
            .count()
            >= 1,
        "{source}"
    );
    assert!(!c.contains("FALLBACK_SLICE_EXTENT)"), "{source}");
    assert!(
        c.contains("copy_be32(core::slice::from_raw_parts_mut(((pas*mutu32_0)as*mutu8),4)"),
        "a byte cursor is bridged as exactly four bytes, no typed reference: {source}"
    );
    assert!(
        c.contains(
            "core::slice::from_raw_parts(((&mutidas*mutlibc::c_intas*mutu32_0)as*constu8),4)"
        ) || c.contains(
            "core::slice::from_raw_parts_mut(((&mutidas*mutlibc::c_intas*mutu32_0)as*mutu8),4)"
        ),
        "an integer local's address is bridged as its four bytes: {source}"
    );
    assert!(
        !source.contains("FALLBACK_SLICE_EXTENT"),
        "the extent is the scalar's size, never fabricated: {source}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// The emitted program behaves as the input does, including a cursor at an
/// ODD offset (where a typed `&mut u32` would be misaligned).
#[test]
fn w6b_byte_region_formals_run_identically() {
    let (source, _) = emitted(COPY_BE);
    let main = r#"fn main() { unsafe {
        let mut buf = [0u8; 32];
        let mut item = binn { pbuf: buf.as_mut_ptr() as *mut libc::c_void, used_size: 1,
            c2rust_unnamed: C2RustUnnamed { vint64: 0 } };
        put_id(&mut item, 0x01020304);
        let mut v16: u16 = 0xa1b2;
        put_value16(&mut item, &mut v16 as *mut u16 as *mut libc::c_void);
        let back = read_id(&mut item, 1);
        let mut value = binn { pbuf: core::ptr::null_mut(), used_size: 0,
            c2rust_unnamed: C2RustUnnamed { vint64: 0 } };
        get_value64(&mut item, 1, &mut value);
        println!("{:?} {} {} {:x}", &buf[..8], item.used_size, back, value.c2rust_unnamed.vint64);
    }}"#;
    let with_libc = |s: &str| format!("{s}\n{main}\n{LIBC_SHIM}");
    let original = run_binary(&with_libc(COPY_BE));
    assert_eq!(
        String::from_utf8_lossy(&original),
        "[0, 1, 2, 3, 4, 161, 178, 0] 7 16909060 1020304a1b20000\n"
    );
    assert_eq!(original, run_binary(&with_libc(&source)));
}

/// R609-4 (a) converted the WRITE side at a call the pair proofs do not clear,
/// beside the READ side's raw view (a T2 bridge under the named waiver).
/// **R934-1 (i) (the seat on 149f; R833-1):** a pair not shown disjoint keeps
/// both sides raw, so at `put_value16`'s cursor beside the void payload
/// (AddValue:1029) and `get_value64`'s union field beside a cursor
/// (GetValue:1432) the written formal is held with the read one; `copy_be32`'s
/// calls are certified, and its bridges stay T1 (wave-5d 150).
#[test]
fn w6b_an_unproven_byte_region_pair_keeps_the_read_side_raw() {
    let rows = decisions(COPY_BE);
    for function in ["copy_be16", "copy_be64"] {
        assert!(
            is_pair_held(decision(&rows, function, "pdest")),
            "{function}: the written side is held beside the unproven pair: {:?}",
            decision(&rows, function, "pdest")
        );
        assert!(
            matches!(decision(&rows, function, "psource"), Decision::Degraded(_)),
            "{function}: the read side of an unproven pair stays raw: {:?}",
            decision(&rows, function, "psource")
        );
    }
    let (source, events) = emitted(COPY_BE);
    let region_bridges = events
        .iter()
        .filter(|(kind, _, _)| kind.starts_with("c-raw-slice"))
        .collect::<Vec<_>>();
    assert!(
        region_bridges
            .iter()
            .any(|(_, tier, _)| *tier == super::bridge_receipt::BridgeRetentionTier::T1),
        "a certified call's bridges stay T1: {events:#?}"
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
}

/// A call passing ONE root at two positions (`copy_be32(p, p)`) is the
/// aliased-storage twin's; the callee keeps its hold rather than grafting a
/// view the twin would duplicate.
#[test]
fn w6b_a_same_root_call_keeps_the_hold() {
    let input = format!(
        "{COPY_BE}\npub unsafe fn swap_in_place(mut item: *mut binn) {{ let mut p = (*item).pbuf as *mut libc::c_uchar; copy_be32(p as *mut u32_0, p as *mut u32_0); }}\n"
    );
    let rows = decisions(&input);
    for name in ["pdest", "psource"] {
        assert!(
            !matches!(decision(&rows, "copy_be32", name), Decision::Slice { .. }),
            "copy_be32::{name} is not a byte region: {:?}",
            decision(&rows, "copy_be32", name)
        );
    }
    let base = decisions(COPY_BE);
    assert_eq!(
        format!("{:?}", decision(&rows, "copy_be16", "pdest")),
        format!("{:?}", decision(&base, "copy_be16", "pdest")),
        "the other callees are unaffected"
    );
}

/// An `&mut b` caller can take the typed reference, and does: the byte region
/// is for formals every caller reaches through a cast (W6B-6's own fixture).
#[test]
fn w6b_a_typed_caller_keeps_the_typed_reference() {
    let rows = decisions(super::void_region_tests::BE64);
    for name in ["pdest", "psource"] {
        assert!(
            matches!(decision(&rows, "copy_be64", name), Decision::Ref { .. }),
            "{name} stays a typed reference: {:?}",
            decision(&rows, "copy_be64", name)
        );
    }
}
