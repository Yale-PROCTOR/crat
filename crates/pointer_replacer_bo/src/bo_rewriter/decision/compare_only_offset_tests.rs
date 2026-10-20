//! R464-3: the compare-only sign arm. wave-6v2's reduction (their report 026,
//! `2026-09-18-wave-6v2-sign-gate-read/reduction.rs`) verbatim: binn's header
//! reader with the two COMPARE-ONLY offsets the corpus function carries.
//!
//! The discriminating fact is the RESULT's use, not the operand's sign. Five
//! of the nine offset-like calls advance the cursor that is read, and their
//! operands are non-negative literals; the three non-literal ones
//! (`plimit = p.offset(*psize - 1)`, two `p.offset(size_of::<i32>() - 1)`)
//! produce values that are only compared or null-tested — never dereferenced,
//! stored, returned or passed — so they do not move the read window and the
//! plain-slice guard has nothing to refuse.

const REDUCTION: &str = r####"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn copy_be32(mut pdest: *mut u32, mut psource: *mut u32) {
    let mut source = psource as *mut u8;
    let mut dest = pdest as *mut u8;
    *dest.offset(0) = *source.offset(3);
    *dest.offset(1) = *source.offset(2);
    *dest.offset(2) = *source.offset(1);
    *dest.offset(3) = *source.offset(0);
}
pub unsafe fn IsValidBinnHeader(mut pbuf: *mut core::ffi::c_void, mut ptype: *mut i32,
    mut psize: *mut i32) -> i32 {
    let mut p = 0 as *mut u8;
    let mut plimit = 0 as *mut u8;
    let mut int32: u32 = 0;
    let mut byte: u8 = 0;
    if pbuf.is_null() { return 0; }
    p = pbuf as *mut u8;
    // SEED (a): a Top-valued operand. The result is null-tested and compared, never read.
    if !psize.is_null() && *psize > 0 { plimit = p.offset((*psize as isize) + (-(1 as isize))); }
    byte = *p;
    p = p.offset(1);
    if byte as i32 & 0xe0 != 0xe0 { return 0; }
    if !plimit.is_null() && p > plimit { return 0; }
    // SEED (b): `size_of` is not in `eval_integer_terminator_call`'s table, so the
    // operand is NonNeg + ConstI(-1) = Top. The result is compared, never read.
    if !plimit.is_null()
        && p.offset((::core::mem::size_of::<i32>() as u64 as isize) + (-(1 as isize))) > plimit {
        return 0;
    }
    copy_be32(&mut int32 as *mut u32, p as *mut u32);
    p = p.offset(4);
    if !ptype.is_null() { *ptype = byte as i32; }
    if !psize.is_null() { *psize = int32 as i32; }
    return p.offset_from(pbuf as *mut u8) as i32;
}
pub unsafe fn binn_buf_type(mut pbuf: *mut core::ffi::c_void) -> i32 {
    let mut type_0: i32 = 0;
    if IsValidBinnHeader(pbuf, &mut type_0, 0 as *mut i32) == 0 { return 0; }
    return type_0;
}
"####;

/// The fact, read directly off the owner's MIR: `Ok(())` where every offset
/// whose operand is not a non-negative literal produces a value the body only
/// compares.
fn verdict(input: &str, owner: &str, parameter: usize) -> Result<(), String> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let did = tcx
            .hir_body_owners()
            .find(|did| {
                tcx.def_path_str(did.to_def_id())
                    .rsplit("::")
                    .next()
                    .unwrap_or_default()
                    == owner
            })
            .unwrap_or_else(|| panic!("{owner}"));
        super::compare_only_offset::every_advancing_offset_is_a_non_negative_literal(
            tcx,
            did,
            rustc_middle::mir::Local::from_usize(parameter + 1),
        )
        .map_err(|refusal| format!("{refusal:?}"))
    })
    .unwrap()
}

/// **The shape.** wave-6v2's reduction, verbatim: `IsValidBinnHeader`'s nine
/// offset-like calls — five non-negative literals that advance the cursor that
/// is read, three non-literal ones whose results are only compared, and one
/// `offset_from` (not offset-like). The fact admits it.
#[test]
fn w5c_compare_only_offsets_admit_the_header_walk() {
    assert_eq!(verdict(REDUCTION, "IsValidBinnHeader", 0), Ok(()));
}

/// **Control (i)** — seed (b)'s result is made to ADVANCE: the same
/// `size_of - 1` offset, but the cursor is moved by it and then read. The fact
/// refuses: a non-literal operand that moves the read window is exactly what
/// the sign bit is for.
#[test]
fn w5c_compare_only_refuses_a_non_literal_that_advances() {
    let input = REDUCTION.replace(
        "    if !plimit.is_null()\n        && p.offset((::core::mem::size_of::<i32>() as u64 as isize) + (-(1 as isize))) > plimit {\n        return 0;\n    }",
        "    p = p.offset((::core::mem::size_of::<i32>() as u64 as isize) + (-(1 as isize)));\n    if !plimit.is_null() && p > plimit { return 0; }",
    );
    assert_ne!(input, REDUCTION, "the control must change the fixture");
    assert!(
        verdict(&input, "IsValidBinnHeader", 0).is_err(),
        "an advancing non-literal offset must keep the refusal"
    );
}

/// **Control (ii)** — the comparison is kept and the result is ALSO read. One
/// read through the value is enough: the window moved.
#[test]
fn w5c_compare_only_refuses_a_compared_value_that_is_also_read() {
    let input = REDUCTION.replace(
        "    byte = *p;",
        "    if !plimit.is_null() { byte = *p.offset((*psize as isize) + (-(1 as isize))); }\n    byte = *p;",
    );
    assert_ne!(input, REDUCTION, "the control must change the fixture");
    assert!(
        verdict(&input, "IsValidBinnHeader", 0).is_err(),
        "a compared value that is also dereferenced must keep the refusal"
    );
}

/// The corpus shape report 027 sized at 24 rows: a VARIABLE advancing offset
/// (`fmap.offset(lo as isize)`). It stays refused — this arm does not touch it.
#[test]
fn w5c_compare_only_refuses_a_variable_advancing_walk() {
    let input = r####"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_snake_case)]
pub unsafe fn walk(mut fmap: *mut u32, mut lo: isize, mut hi: isize) -> u32 {
    let mut acc = 0u32;
    let mut i = lo;
    while i < hi { acc = acc.wrapping_add(*fmap.offset(i)); i += 1; }
    acc
}
"####;
    assert!(verdict(input, "walk", 0).is_err());
}

/// **R470-6 — the corpus idiom, measured.** The reduction writes the advancing
/// step as `p.offset(4)`; binn itself writes it as
/// `p = p.offset(4 as libc::c_int as isize)` (lib.rs:1192), and c2rust writes
/// every sized step that way. In MIR the operand is then `move _91`, a local
/// holding `_92 = const 4_i32; _91 = move _92 as isize`, so
/// `non_negative_literal` — which reads the operand's own constant — sees no
/// literal and the walk is refused for a step whose sign is written down.
///
/// The probe of R470-5(b) measured this on the substrate: binn's
/// `IsValidBinnHeader::pbuf` refuses at THIS offset, not at `plimit`'s
/// (whose result is compare-only and already admitted).
#[test]
fn w5c_compare_only_admits_a_literal_step_behind_c2rusts_casts() {
    let input = REDUCTION.replace(
        "    p = p.offset(4);",
        "    p = p.offset(4 as core::ffi::c_int as isize);",
    );
    assert_ne!(input, REDUCTION, "the witness must change the fixture");
    assert_eq!(
        verdict(&input, "IsValidBinnHeader", 0),
        Ok(()),
        "a non-negative literal behind c2rust's casts is still a literal step"
    );
}

/// **Control** — the same casts around a NEGATED literal. `-(4)` is a MIR
/// `UnaryOp`, not a cast of a constant, so the operand stays non-literal and
/// the step (which moves the cursor that is then read) keeps the refusal.
#[test]
fn w5c_compare_only_refuses_a_negated_literal_behind_the_same_casts() {
    let input = REDUCTION.replace(
        "    p = p.offset(4);",
        "    p = p.offset(-(4 as core::ffi::c_int) as isize);",
    );
    assert_ne!(input, REDUCTION, "the control must change the fixture");
    assert!(
        verdict(&input, "IsValidBinnHeader", 0).is_err(),
        "a negated literal must not be read as a non-negative literal step"
    );
}

/// **Control** — a step local written TWICE is not one spelling of one
/// literal. The walk back stops at the second writer and the operand stays
/// non-literal, so the step (which moves the cursor that is read) is refused
/// even though one of the two writers is `4`.
#[test]
fn w5c_compare_only_refuses_a_step_local_written_twice() {
    let input = REDUCTION.replace(
        "    p = p.offset(4);",
        "    let mut step: isize = -4isize;\n    \
         if byte as i32 > 3 { step = 4 as core::ffi::c_int as isize; }\n    \
         p = p.offset(step);",
    );
    assert_ne!(input, REDUCTION, "the control must change the fixture");
    assert!(
        verdict(&input, "IsValidBinnHeader", 0).is_err(),
        "a step written twice must not be read as a literal step"
    );
}
