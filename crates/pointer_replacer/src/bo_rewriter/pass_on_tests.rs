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
