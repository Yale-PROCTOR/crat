//! **R573-4 — the forced cover, end to end.** brotli's `EncodeData` →
//! `InitOrStitchToPreviousBlock(m, &mut (*s).hasher_, data, _, &mut (*s).params)` (class 2337):
//! the A5 proof site for the raw `data` (a `*const u8`, which may address any object) overlaps
//! `m`, `hasher` and `params`; `hasher` and `params` retain (the callee stores them through each
//! other). The single-primary rule found no primary and held the class `a5-primary-ambiguous`.

pub(super) const STAR: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
#[repr(C)]
pub struct Mm { pub n: usize }
#[repr(C)]
pub struct Params { pub quality: i32, pub back: *mut Hasher }
#[repr(C)]
pub struct Hasher { pub params: *mut Params, pub count: usize }
#[repr(C)]
pub struct State { pub mm: Mm, pub hasher: Hasher, pub params: Params, pub buf: *mut u8 }
pub unsafe extern "C" fn Setup(mut m: *mut Mm, mut hasher: *mut Hasher, mut params: *mut Params, mut data: *const u8) {
    (*m).n = (*m).n.wrapping_add(*data as usize);
    (*hasher).params = params;
    (*params).back = hasher;
}
pub unsafe extern "C" fn Stitch(mut m: *mut Mm, mut hasher: *mut Hasher, mut data: *const u8, mut params: *mut Params) {
    let _address = data as usize;
    Setup(m, hasher, params, data);
}
pub unsafe extern "C" fn Encode(mut s: *mut State) {
    let mut data: *const u8 = (*s).buf;
    Stitch(&mut (*s).mm, &mut (*s).hasher, data, &mut (*s).params);
}
"#;

/// The seam receipt (`seam_tsv_from_table`) in the precise-replay decision table.
fn seam_receipts(src: &str) -> String {
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("one decision pipeline");
        super::seam_tsv_from_table(tcx, &table)
    })
    .expect("fixture compiles")
}

/// The overlap-proof row for `callee`'s parameter `param`.
fn overlap_proof<'a>(tsv: &'a str, callee: &str, param: usize) -> &'a str {
    tsv.lines()
        .find(|row| {
            row.starts_with(&format!("overlap-proof\t{callee}\t"))
                && row.contains(&format!("\tparam:{param}\t"))
        })
        .unwrap_or_else(|| panic!("an overlap proof for {callee}#{param}:\n{tsv}"))
}

/// **R573-4 witness, end to end — the receipt names the rule.** At `Stitch → Setup` the
/// star is `data` (a non-retaining `*const u8`) against `m`, and against `hasher` / `params`,
/// which `Setup` stores through each other (both retain). The single-primary rule held the call
/// `a5-primary-ambiguous`; the forced cover makes `data` the raw view
/// (`a5-site-proof-t2-fallback`) and `m` the primary, each receipted `pair-forced-cover`.
/// (`hasher` / `params` are raw formals here, so the A5 path's own positive-retention gate
/// holds them; in brotli they are pair-owned and never reach it.)
#[test]
fn r573_4_the_star_receipt_names_the_forced_cover() {
    let tsv = seam_receipts(STAR);
    assert!(!tsv.contains("a5-primary-ambiguous"), "{tsv}");
    let data = overlap_proof(&tsv, "Setup", 3);
    assert!(data.contains("\ta5-site-proof-t2-fallback\t"), "{data}");
    assert!(data.contains("pair-forced-cover"), "{data}");
    let m = overlap_proof(&tsv, "Setup", 0);
    assert!(m.contains("\ta5-site-proof-pair-primary\t"), "{m}");
    assert!(m.contains("pair-forced-cover"), "{m}");
}
