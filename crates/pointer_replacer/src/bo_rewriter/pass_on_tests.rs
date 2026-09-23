//! **W6S-13 (R526-4 / R528-4) — the pass-on rule.** A caller held at a local
//! callee whose only refused uses are arguments at local callee parameters that
//! deliver as slices in the same plan has a slice image at every use: it hands
//! the slice on. Fixtures reduced from brotli `StitchToPreviousBlockH2`.
//!
//! **Side of the reduction/real-crate divergence rule (relay 042).** These are
//! REDUCTIONS, and a reduction delivers `ringbuffer` outright (measured while
//! building this file: no hold, no decline). On the real crate the owner's
//! SliceUse family is WITHDRAWN (batch 28's
//! `brotli.raw-boundary-additive-family-fallbacks.json`: owner
//! `src::enc::encode::StitchToPreviousBlockH2`, `SliceUse` / `Option` /
//! `Declaration` / `Return`, cause `new-family-dependency:2337`), so the lift's
//! gate reads the before-family walk. The fixtures seed that recorded
//! withdrawal (`crat-test-withdraw`) rather than hunting a caller graph that
//! reproduces it; the corpus row is measured at the census.

const PREFIX: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
// crat-test-withdraw: SliceUse StitchToPreviousBlockH2
// crat-test-withdraw: Option StitchToPreviousBlockH2
// crat-test-withdraw: Declaration StitchToPreviousBlockH2
// crat-test-withdraw: Return StitchToPreviousBlockH2
pub type uint8_t = u8;
pub type uint32_t = u32;
pub type uint64_t = u64;
pub type size_t = usize;
pub type libc_int = i32;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct H2 {
    pub buckets_: *mut uint32_t,
}
static kHashMul64: uint64_t = 0x1e35a7bd1e35a7bd;
unsafe extern "C" fn BrotliUnalignedRead64(mut p: *const core::ffi::c_void) -> uint64_t {
    return *(p as *const uint64_t);
}
unsafe extern "C" fn HashBytesH2(mut data: *const uint8_t) -> uint32_t {
    let h = (BrotliUnalignedRead64(data as *const core::ffi::c_void) << 64 as libc_int - 8 as libc_int * 5 as libc_int).wrapping_mul(kHashMul64);
    return (h >> 64 as libc_int - 16 as libc_int) as uint32_t;
}
"#;

/// brotli's `StoreH2`: `data` delivers `&[uint8_t]`.
const STORE_DELIVERS: &str = r#"
unsafe extern "C" fn StoreH2(mut self_0: *mut H2, mut data: *const uint8_t, mask: size_t, ix: size_t) {
    let key = HashBytesH2(&*data.offset((ix & mask) as isize));
    {
        *((*self_0).buckets_).offset(key as isize) = ix as uint32_t;
    };
}
"#;

/// FAULT: a callee whose `data` parameter does not deliver a slice — it is
/// read through an address cast, which has no slice image of its own.
const STORE_RAW: &str = r#"
unsafe extern "C" fn StoreH2(mut self_0: *mut H2, mut data: *const uint8_t, mask: size_t, ix: size_t) {
    let key = (data as size_t).wrapping_add(*data.offset((ix & mask) as isize) as size_t) & 15;
    {
        *((*self_0).buckets_).offset(key as isize) = ix as uint32_t;
    };
}
"#;

/// brotli's `StitchToPreviousBlockH2`, verbatim in shape: `ringbuffer`'s ONLY
/// uses are three `StoreH2(self_0, ringbuffer, …)` arguments.
const STITCH: &str = r#"
unsafe extern "C" fn StitchToPreviousBlockH2(mut self_0: *mut H2, mut num_bytes: size_t,
        mut position: size_t, mut ringbuffer: *const uint8_t, mut ringbuffer_mask: size_t) {
    if num_bytes >= 3 && position >= 3 {
        StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(3));
        StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(2));
        StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(1));
    }
}
"#;

/// CONTROL: the same caller with a SECOND use that is not a pass-on.
const STITCH_SECOND_USE: &str = r#"
unsafe extern "C" fn StitchToPreviousBlockH2(mut self_0: *mut H2, mut num_bytes: size_t,
        mut position: size_t, mut ringbuffer: *const uint8_t, mut ringbuffer_mask: size_t) {
    if num_bytes >= 3 && position >= 3 {
        StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(3));
        StoreH2(self_0, ringbuffer, ringbuffer_mask, position.wrapping_sub(2));
        (*self_0).buckets_ = ringbuffer as size_t as *mut uint32_t;
    }
}
"#;

fn fixture(store: &str, stitch: &str) -> String {
    format!("{PREFIX}{store}{stitch}")
}

type Lift = (
    String,
    Option<super::decision::licensed_lift::Refusal>,
    String,
    Option<&'static str>,
);

fn table(
    input: &str,
) -> (
    Vec<Lift>,
    Vec<super::decision::pass_on::Receipt>,
    Vec<(String, String)>,
) {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )?;
        Ok::<_, String>((
            table
                .licensed_lifts
                .iter()
                .map(|l| (l.subject.clone(), l.declined, l.key(), l.use_shape))
                .collect(),
            table.pass_on_receipts.clone(),
            table
                .entries
                .iter()
                .map(|(s, d)| (s.label.clone(), format!("{d:?}")))
                .collect(),
        ))
    })
    .expect("fixture compiles")
    .expect("table")
}

fn declined_by_use(lifts: &[Lift]) -> bool {
    use super::decision::licensed_lift::Refusal;
    lifts.iter().any(|(subject, declined, ..)| {
        subject == "StitchToPreviousBlockH2::ringbuffer"
            && *declined == Some(Refusal::Declined("slice-use-unsupported"))
    })
}

/// The withdrawal is what makes the reduction a witness: with it, and
/// before W6S-13, `ringbuffer` is exactly the corpus row — held at `StoreH2`,
/// declined `slice-use-unsupported`. Pinned via the fault below (whose callee
/// does not deliver, so the rule must not admit), which reads the same hold.
///
/// **W6S-13 — the pass-on delivers.** Every refused use hands the slice to
/// `StoreH2::data`, which delivers `&[uint8_t]`; the lift is not declined, the
/// caller decides `Slice`, the pair is receipted, and the tree type-checks.
#[test]
fn w6s13_the_pass_on_lifts_stitch_ringbuffer() {
    let input = fixture(STORE_DELIVERS, STITCH);
    let (lifts, receipts, entries) = table(&input);
    assert!(!declined_by_use(&lifts), "{lifts:#?}");
    let ringbuffer = entries
        .iter()
        .find(|(label, _)| label == "StitchToPreviousBlockH2::ringbuffer")
        .unwrap_or_else(|| panic!("{entries:#?}"));
    assert!(ringbuffer.1.starts_with("Slice {"), "{entries:#?}");
    assert!(
        lifts.iter().any(|(subject, declined, _, shape)| subject
            == "StitchToPreviousBlockH2::ringbuffer"
            && declined.is_none()
            && *shape == Some("pass-on")),
        "the lift row says which door: {lifts:#?}"
    );
    assert_eq!(
        receipts,
        vec![super::decision::pass_on::Receipt {
            caller: "StitchToPreviousBlockH2::ringbuffer".to_owned(),
            callee: "StoreH2".to_owned(),
            parameter_index: 1,
        }],
        "one receipt per (callee, parameter) pair, not per call: {lifts:#?}"
    );
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(&input) else {
        panic!("the fixture must emit")
    };
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("ringbuffer: &[uint8_t]"), "{source}");
}

/// **FAULT — a callee parameter that does not deliver.** The use is still a
/// bare local-callee argument, but `StoreH2::data` is not `Slice`, so nothing
/// receives the caller's slice and the decline stands.
#[test]
fn w6s13_fault_a_callee_that_does_not_deliver_keeps_the_decline() {
    let (lifts, receipts, entries) = table(&fixture(STORE_RAW, STITCH));
    assert!(
        !entries
            .iter()
            .any(|(label, d)| label == "StoreH2::data" && d.starts_with("Slice {")),
        "the fault's callee must not deliver: {entries:#?}"
    );
    assert!(declined_by_use(&lifts), "{lifts:#?}");
    assert!(receipts.is_empty(), "{receipts:#?}");
}

/// **CONTROL — a second, non-pass-on use.** One refused use that is not an
/// argument (a cast into a field) keeps the whole subject without a slice
/// image, exactly as before the rule.
#[test]
fn w6s13_control_a_second_non_pass_on_use_keeps_the_decline() {
    let (lifts, receipts, _) = table(&fixture(STORE_DELIVERS, STITCH_SECOND_USE));
    assert!(declined_by_use(&lifts), "{lifts:#?}");
    assert!(receipts.is_empty(), "{receipts:#?}");
}

/// W6S-13b: brotli `backward_references::StoreRangeH35::data#2` — one use at a
/// `Slice` formal (`StoreRangeH3`), one at a thin formal
/// (`StoreRangeHROLLING_FAST`, whose body never reads it).
const RANGE: &str = r#"
// crat-test-withdraw: SliceUse StoreRangeH35
// crat-test-withdraw: Option StoreRangeH35
// crat-test-withdraw: Declaration StoreRangeH35
// crat-test-withdraw: Return StoreRangeH35
unsafe extern "C" fn StoreRangeH3(mut self_0: *mut H2, mut data: *const uint8_t, mask: size_t, ix_start: size_t, ix_end: size_t) {
    let mut i: size_t = ix_start;
    while i < ix_end {
        StoreH2(self_0, data, mask, i);
        i = i.wrapping_add(1);
    }
}
unsafe extern "C" fn StoreRangeHROLLING_FAST(mut self_0: *mut H2, mut data: *const uint8_t, mask: size_t, ix_start: size_t, ix_end: size_t) {}
unsafe extern "C" fn StoreRangeH35(mut self_0: *mut H2, mut data: *const uint8_t, mask: size_t, ix_start: size_t, ix_end: size_t) {
    StoreRangeH3(self_0, data, mask, ix_start, ix_end);
    StoreRangeHROLLING_FAST(self_0, data, mask, ix_start, ix_end);
}
"#;

/// The chain: `Top::storage` hands on to `Mid::storage`, which hands on to a
/// delivering `Leaf::storage`; both owners withdrawn, as brotli's
/// `BuildAndStoreCommandPrefixCode` → `BrotliStoreHuffmanTree` are.
const CHAIN: &str = r#"
// crat-test-withdraw: SliceUse InitOrStitch
// crat-test-withdraw: Option InitOrStitch
// crat-test-withdraw: Declaration InitOrStitch
// crat-test-withdraw: Return InitOrStitch
unsafe extern "C" fn InitOrStitch(mut self_0: *mut H2, mut data: *const uint8_t, mut mask: size_t,
        mut position: size_t, mut input_size: size_t) {
    StitchToPreviousBlockH2(self_0, input_size, position, data, mask);
}
"#;

/// Mutability (d): the STITCH shape with the callee's formal seeded MUTABLE
/// and the caller left shared — `&[T]` handed to `&mut [T]`.
const MUT_SEED: &str = "\n// crat-test-mutable: StoreH2::data\n";

fn emitted(input: &str) -> String {
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(input) else {
        panic!("the fixture must emit")
    };
    assert!(super::verify::type_checks_str(&source), "{source}");
    source
}

/// **W6S-13b — a thin formal takes the first element.** `StoreRangeH35::data`
/// hands on to `StoreRangeH3::data` (`Slice`) and `StoreRangeHROLLING_FAST::data`
/// (thin `Ref`): lifted by the pass-on, one receipt per pair, and the seam's
/// glue renders the thin argument as the slice's first element —
/// `data.first().unwrap()`, which panics on an empty slice exactly where
/// `&data[0]` would (the real `StoreRangeHROLLING_FAST` never reads it).
#[test]
fn w6s13b_a_thin_formal_takes_the_first_element() {
    let input = fixture(STORE_DELIVERS, RANGE);
    let (lifts, receipts, entries) = table(&input);
    assert!(
        entries
            .iter()
            .any(|(l, d)| l == "StoreRangeHROLLING_FAST::data" && d.starts_with("Ref {")),
        "the second formal is thin: {entries:#?}"
    );
    assert!(
        lifts
            .iter()
            .any(|(s, d, _, shape)| s == "StoreRangeH35::data"
                && d.is_none()
                && *shape == Some("pass-on")),
        "{lifts:#?}"
    );
    let pairs = receipts
        .iter()
        .filter(|r| r.caller == "StoreRangeH35::data")
        .map(|r| (r.callee.as_str(), r.parameter_index))
        .collect::<Vec<_>>();
    assert_eq!(
        pairs,
        vec![("StoreRangeH3", 1), ("StoreRangeHROLLING_FAST", 1)],
        "{receipts:#?}"
    );
    let source = emitted(&input);
    assert!(source.contains("data: &[uint8_t]"), "{source}");
    // Measured: the seam's `(Ref, Slice)` glue is `First`, rendered checked.
    assert!(
        source.contains("StoreRangeHROLLING_FAST(self_0, data.first().unwrap(), mask"),
        "the thin argument is the first element: {source}"
    );
}

/// **The chain round.** `InitOrStitch::data` hands on to
/// `StitchToPreviousBlockH2::ringbuffer`, which is itself held until the
/// first round lifts it; the second round lifts the caller.
#[test]
fn w6s13_the_chain_round_lifts_the_caller_of_a_lifted_caller() {
    let input = format!("{}{CHAIN}", fixture(STORE_DELIVERS, STITCH));
    let (lifts, receipts, _) = table(&input);
    for subject in ["StitchToPreviousBlockH2::ringbuffer", "InitOrStitch::data"] {
        assert!(
            lifts
                .iter()
                .any(|(s, d, _, shape)| s == subject && d.is_none() && *shape == Some("pass-on")),
            "{subject}: {lifts:#?}"
        );
        assert!(
            !lifts.iter().any(|(s, d, ..)| s == subject
                && d.is_some_and(|r| matches!(
                    r,
                    super::decision::licensed_lift::Refusal::Declined(_)
                ))),
            "a lifted row keeps no decline: {subject}: {lifts:#?}"
        );
    }
    assert!(
        receipts.iter().any(|r| r.caller == "InitOrStitch::data"
            && r.callee == "StitchToPreviousBlockH2"
            && r.parameter_index == 3),
        "{receipts:#?}"
    );
    emitted(&input);
}

/// **(d) — a shared caller is never handed to a mutable formal.** Refused, and
/// the decline row says why.
#[test]
fn w6s13_a_shared_caller_at_a_mutable_formal_is_refused_and_receipted() {
    let input = format!("{}{MUT_SEED}", fixture(STORE_DELIVERS, STITCH));
    let (lifts, receipts, entries) = table(&input);
    assert!(
        entries
            .iter()
            .any(|(l, d)| l == "StoreH2::data" && d.starts_with("Slice { mutable: true")),
        "the seed makes the formal mutable: {entries:#?}"
    );
    assert!(declined_by_use(&lifts), "{lifts:#?}");
    assert!(
        lifts.iter().any(
            |(s, d, _, shape)| s == "StitchToPreviousBlockH2::ringbuffer"
                && d.is_some()
                && *shape == Some("pass-on-refused:shared-into-mut")
        ),
        "{lifts:#?}"
    );
    assert!(receipts.is_empty(), "{receipts:#?}");
}

/// (c) B1's root walk: a caller that passes a sized array states the extent.
const SIZED_CALLER: &str = r#"
pub unsafe fn drive(mut h: *mut H2) {
    let mut buf: [uint8_t; 64] = [0; 64];
    let mut ringbuffer: *const uint8_t = buf.as_ptr();
    StitchToPreviousBlockH2(h, 64, 3, ringbuffer, 63);
}
"#;

/// **(c) The third gate.** A pass-on row whose every caller states an extent
/// lifts on B1's EVIDENCE, and the waiver never fabricates one for it.
#[test]
fn w6s13_a_pass_on_row_with_a_root_extent_lifts_on_evidence() {
    let input = format!("{}{SIZED_CALLER}", fixture(STORE_DELIVERS, STITCH));
    let rows = ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(&input),
        |tcx| {
            let (table, _ctx) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    super::A5Mode::PreciseReplay,
                    Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )?;
            Ok::<_, String>((
                table
                    .root_extents
                    .iter()
                    .map(|r| {
                        (
                            r.subject.clone(),
                            r.outcome,
                            r.extent.clone(),
                            r.evidence.clone(),
                        )
                    })
                    .collect::<Vec<_>>(),
                table
                    .licensed_lifts
                    .iter()
                    .map(|l| (l.subject.clone(), l.key()))
                    .collect::<Vec<_>>(),
            ))
        },
    )
    .expect("fixture compiles")
    .expect("table");
    let (roots, lifts) = rows;
    assert!(
        roots.iter().any(
            |(s, outcome, ..)| s == "StitchToPreviousBlockH2::ringbuffer" && *outcome == "lifted"
        ),
        "B1 lifts it on the callers' extent: {roots:#?}\n{lifts:#?}"
    );
    assert!(
        !lifts
            .iter()
            .any(|(s, key)| s == "StitchToPreviousBlockH2::ringbuffer"
                && key.starts_with("fallback(")),
        "never on the waiver: {lifts:#?}"
    );
}

/// **R533-4 (wave-4 061 C7) — wave-4's shape.** A mutable caller held at
/// `BrotliUnalignedRead32` (a width READ, whose region is `mutable: false`)
/// that also hands itself to a local callee writing through it.
///
/// Measured while building 071: at `247d3664e` this shape is lifted by the
/// EXACT arm's own path — the collector supports both uses, so
/// `pass_on::supported` is never asked (re-measured with the rule disabled:
/// identical) — to `&[u8]`, and the program comes back `Degraded`
/// (`class recovery found no strict compiling subset`). The fix is the exact
/// arm's lift mutability, not the pass-on's: `pass_on::supported` now asks
/// with the lift's mutability as R533-4 rules, and that alone does not reach
/// this shape.
const READ_THEN_WRITE: &str = r#"
#![allow(dead_code, unused_mut, unused_assignments, non_snake_case, non_camel_case_types, unused_unsafe)]
pub type uint8_t = u8;
pub type uint32_t = u32;
unsafe extern "C" fn BrotliUnalignedRead32(mut p: *const core::ffi::c_void) -> uint32_t {
    return *(p as *const uint32_t);
}
unsafe extern "C" fn Clear(mut dst: *mut uint8_t) {
    *dst = 0;
}
unsafe extern "C" fn HashAndClear(mut data: *mut uint8_t) -> uint32_t {
    let h = BrotliUnalignedRead32(data as *const core::ffi::c_void);
    Clear(data);
    return h;
}
"#;

#[test]
fn w6s13_wave4_shape_a_mutable_caller_is_never_lifted_shared() {
    let (lifts, _receipts, entries) = table(READ_THEN_WRITE);
    let decision = |label: &str| {
        entries
            .iter()
            .find(|(l, _)| l == label)
            .map(|(_, d)| d.clone())
            .unwrap_or_else(|| panic!("no {label}: {entries:#?}"))
    };
    assert!(
        decision("Clear::dst").starts_with("Ref { mutable: true"),
        "the second callee writes: {entries:#?}"
    );
    let data = decision("HashAndClear::data");
    assert!(
        !data.starts_with("Slice { mutable: false"),
        "a mutable caller is never lifted to a SHARED slice: {data}\n{lifts:#?}"
    );
    let source = emitted(READ_THEN_WRITE);
    assert!(source.contains("Clear("), "{source}");
}

/// **R536-6 R1 (wave-4 062) — per-module duplicates share a label.** Module `a`
/// is the chain (its `InitOrStitch::data` lifts in the second round); module
/// `b` is C2Rust's copy of the same functions, whose `InitOrStitch::data` has a
/// second, non-pass-on use and stays held. The chain round must not delete
/// `b`'s refusal because `a`'s twin — same LABEL — lifted.
fn twins() -> String {
    let body = |extra: &str| {
        format!("{STORE_DELIVERS}{STITCH}{CHAIN}").replace(
            "    StitchToPreviousBlockH2(self_0, input_size, position, data, mask);\n}",
            &format!(
                "    StitchToPreviousBlockH2(self_0, input_size, position, data, mask);\n{extra}}}"
            ),
        )
    };
    let a = body("");
    let b = body("    let _address = data as size_t;\n");
    let prelude = PREFIX.replace("pub type", "pub type");
    format!(
        "{prelude}\nmod a {{\n    use super::*;\n{a}\n}}\nmod b {{\n    use super::*;\n{b}\n}}\n"
    )
}

#[test]
fn w6s13_r1_a_twins_lift_does_not_delete_the_held_twins_refusal() {
    let (lifts, _receipts, entries) = table(&twins());
    let states = entries
        .iter()
        .filter(|(l, _)| l == "InitOrStitch::data")
        .map(|(_, d)| d.chars().take(12).collect::<String>())
        .collect::<Vec<_>>();
    assert_eq!(states.len(), 2, "two twins: {entries:#?}");
    assert!(
        states.iter().any(|d| d.starts_with("Slice"))
            && states.iter().any(|d| d.starts_with("Degraded")),
        "one twin lifts, one stays held: {states:?}"
    );
    use super::decision::licensed_lift::Refusal;
    assert!(
        lifts
            .iter()
            .any(|(s, d, ..)| s == "InitOrStitch::data" && matches!(d, Some(Refusal::Declined(_)))),
        "the held twin keeps its refusal row: {lifts:#?}"
    );
    assert!(
        lifts
            .iter()
            .any(|(s, d, _, shape)| s == "InitOrStitch::data"
                && d.is_none()
                && *shape == Some("pass-on")),
        "the lifted twin keeps its lift row: {lifts:#?}"
    );
}

/// **R536-6 R2 — a still-held row keeps the LAST round's reason.** `entry::p`
/// (its owner withdrawn, as brotli's are) hands itself to
/// `StitchToPreviousBlockH2::ringbuffer`, which is held until round 1 lifts
/// it. In round 1 `p` stops at the use gate; in round 2 it clears it and stops
/// at the one-place-root gate (`p = &x` is one element). The recorded refusal
/// is round 2's, not round 1's `slice-use-unsupported`.
const PLACE_ROOT: &str = r#"
// crat-test-withdraw: SliceUse entry
// crat-test-withdraw: Option entry
// crat-test-withdraw: Declaration entry
// crat-test-withdraw: Return entry
pub unsafe fn entry(mut h: *mut H2) {
    let mut x: uint8_t = 0;
    let mut p: *const uint8_t = &mut x;
    StitchToPreviousBlockH2(h, 3, 3, p, 63);
}
"#;

#[test]
fn w6s13_r2_a_still_held_row_keeps_the_last_rounds_reason() {
    let input = format!("{}{PLACE_ROOT}", fixture(STORE_DELIVERS, STITCH));
    let (lifts, _receipts, entries) = table(&input);
    assert!(
        entries
            .iter()
            .any(|(l, d)| l == "entry::p" && d.starts_with("Degraded")),
        "held at the fixpoint: {entries:#?}"
    );
    use super::decision::licensed_lift::Refusal;
    let declines = lifts
        .iter()
        .filter(|(s, d, ..)| s == "entry::p" && matches!(d, Some(Refusal::Declined(_))))
        .map(|(_, d, ..)| *d)
        .collect::<Vec<_>>();
    assert_eq!(
        declines,
        vec![Some(Refusal::Declined("one-place-root"))],
        "exactly one refusal, the one true at the fixpoint: {lifts:#?}"
    );
}
