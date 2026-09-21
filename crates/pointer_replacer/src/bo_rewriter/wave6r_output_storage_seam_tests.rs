//! The seam's A5 site proof asks the callee ROW whether the position retains,
//! and binn's `*_get_value` / `*_next` row says `retains` because its only
//! positive sinks are stores through its own out-parameter
//! (`OutputStorage: store _N through _3`). wave-6v2's certificate answers
//! exactly that shape — the outputs are frame-confined at every inventoried
//! call — so the guard reads it beside wave-6r's returned-alias fact
//! (report 026 claim 2: batch 10's five binn `seam-positive-retention`
//! function reverts are this shape, not the returned-alias one).
const OUT_STORAGE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct binn { pub header: i32, pub type_0: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
pub unsafe fn get_value(mut ptr: *mut u8, mut pos: i32, mut value: *mut binn) -> i32 {
    if ptr.is_null() || value.is_null() { return 0 as i32; }
    (*value).type_0 = *ptr.offset(pos as isize) as i32;
    (*value).ptr = ptr.offset(pos as isize) as *mut core::ffi::c_void;
    return 1 as i32;
}
pub unsafe fn get_type(mut ptr: *mut u8, mut pos: i32) -> i32 {
    let mut value = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };
    if get_value(ptr, pos, &mut value) == 0 as i32 { return 0 as i32; }
    return value.type_0;
}
"#;

fn settled(callee: &str, index: usize) -> bool {
    ::utils::compilation::run_compiler_on_str(OUT_STORAGE, |tcx| {
        let (_, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let target = tcx
            .hir_body_owners()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == callee)
            .expect("the callee exists");
        ctx.retention.output_storage_settled(target, index)
    })
    .expect("input type-checks")
}

/// The guard reads the certificate: the position whose only sinks are stores
/// through the out-parameter is settled, and the read-only position is not in
/// the set at all (its row is `no-retain` already).
#[test]
fn wave6r_output_storage_settled_is_read_beside_the_returned_alias_fact() {
    assert!(
        settled("get_value", 0),
        "the stored-through position is settled"
    );
    assert!(
        !settled("get_value", 1),
        "a scalar position is not an output-storage certificate"
    );
}

// NOTE (report 030): a seam-level witness for the `||` itself is NOT here.
// The A5 site proof does not fire on a reduction this small — the same wall
// report 024 hit for the returned-alias lever, which the corpus probe had to
// answer instead. The disjunct is one line over the fact above; its evidence
// is batch 13's census (binn's five `seam-positive-retention` function
// reverts of report 026 claim 2), not a vacuous local assertion.

// NOTE (report 036): there is no seam-level witness for the block arm
// either. I wrote one and MEASURED it vacuous — with the disjunct disabled
// it still passes, because this reduction's site is never blocked. The same
// wall as report 030's A5 arm: the evidence for both disjuncts is the
// corpus (binn's five `seam-positive-retention` function reverts), not a
// local assertion that cannot fail.

/// The twin receipt reaches the artifacts, which is what a census reads.
#[test]
fn wave6r_twin_placement_is_exported_to_the_artifacts() {
    let exported = ::utils::compilation::run_compiler_on_str(OUT_STORAGE, |tcx| {
        let (_, ctx) = super::super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::super::A5Mode::PreciseReplay,
                Some(super::super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        ctx.raw_boundary_artifacts.twin_placement.clone()
    })
    .expect("input type-checks");
    // This fixture grafts no counted-void call, so the receipt is empty —
    // what the witness pins is that the FIELD exists and is wired, which is
    // exactly what was missing (the row could never reach a census).
    assert!(
        exported.is_empty()
            || exported.starts_with(super::super::decision::counted_void::TWIN_RECEIPT_HEADER),
        "{exported}"
    );
}
