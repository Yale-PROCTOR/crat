//! wave-6p R593-4: `read-read-peers` releases a pair whose two positions both
//! carry R492-3's shared-read fact — `*const` in the input, nothing written
//! through the formal, and no mutable reborrow of it anywhere in the callee.
//! Two shared borrows of one place are exactly what Rust permits, so such a
//! pair needs no disjointness at all.
//!
//! **Scope: calls the shared-read consumer never takes.** wave-6k's consumer
//! (`decision/shared_read_pairs.rs`, R396-2) owns every TWO-argument call: it
//! rewrites the addresses itself and pins that the A5 overlap verdict of such a
//! call stays `Overlapping`. So a two-argument read/read pair stays refused to
//! it (the pin `w6p_read_read_pair_is_left_to_the_shared_read_consumer`), and
//! this rule releases the pair only in a call with any other number of
//! arguments — the shape of report 044 §C's four sites.

use super::decision::pair_disjointness::{CertificateKind, PairDisjointnessIndex, Unproved};

fn verdict(
    src: &str,
    caller: &str,
    callee: &str,
    left: usize,
    right: usize,
) -> Result<CertificateKind, Unproved> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = PairDisjointnessIndex::derive(&program, &mut_facts, None);
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        out = Some(index.certify_recorded(function(caller), function(callee), left, right));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

/// brotli's `EvaluateNode → ComputeDistanceCache(pos, starting_dist_cache,
/// nodes, dist_cache)`: positions 1 and 2 are `*const`, only read, never
/// mutably reborrowed; position 3 is written.
const FOUR_ARGUMENTS: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct Node { pub v: i32, pub w: i32 }
pub unsafe fn ComputeDistanceCache(
    mut pos: usize,
    mut starting: *const i32,
    mut nodes: *const Node,
    mut out: *mut i32,
) {
    *out = *starting + (*nodes).v + pos as i32;
}
pub unsafe fn EvaluateNode(mut start: *const i32, mut nodes: *const Node, mut out: *mut i32) {
    ComputeDistanceCache(0, start, nodes, out);
}
"#;

/// The same shape, but `nodes` is `*mut` in the input though never written:
/// the formal is immutable, so the pair reaches the read/read branch, yet it
/// does not carry the shared-read fact — one side only.
const ONE_SIDE_ONLY: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct Node { pub v: i32, pub w: i32 }
pub unsafe fn ComputeDistanceCache(
    mut pos: usize,
    mut starting: *const i32,
    mut nodes: *mut Node,
    mut out: *mut i32,
) {
    *out = *starting + (*nodes).v + pos as i32;
}
pub unsafe fn EvaluateNode(mut start: *const i32, mut nodes: *mut Node, mut out: *mut i32) {
    ComputeDistanceCache(0, start, nodes, out);
}
"#;

/// wave-6k's territory: a TWO-argument read/read call stays refused to their
/// consumer, whatever the fact says.
const TWO_ARGUMENTS: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct Node { pub v: i32, pub w: i32 }
pub unsafe fn Pair(mut starting: *const i32, mut nodes: *const Node) -> i32 {
    *starting + (*nodes).v
}
pub unsafe fn Caller(mut start: *const i32, mut nodes: *const Node) -> i32 {
    Pair(start, nodes)
}
"#;

#[test]
fn w6p_a_shared_shared_pair_in_a_wider_call_is_released() {
    assert_eq!(
        verdict(FOUR_ARGUMENTS, "EvaluateNode", "ComputeDistanceCache", 1, 2),
        Ok(CertificateKind::ReadReadShared),
        "two shared borrows need no disjointness"
    );
}

#[test]
fn w6p_a_shared_mutable_pair_keeps_its_refusal() {
    let verdict = verdict(FOUR_ARGUMENTS, "EvaluateNode", "ComputeDistanceCache", 1, 3);
    assert!(
        verdict.is_err(),
        "`out` is written, so `starting` beside it needs a real proof: got {verdict:?}"
    );
}

#[test]
fn w6p_the_fact_on_one_side_only_keeps_the_refusal() {
    assert_eq!(
        verdict(ONE_SIDE_ONLY, "EvaluateNode", "ComputeDistanceCache", 1, 2),
        Err(Unproved::ReadReadPeers),
        "`nodes` is `*mut` in the input: not a shared-read position"
    );
}

#[test]
fn w6p_a_two_argument_read_read_call_stays_with_the_consumer() {
    assert_eq!(
        verdict(TWO_ARGUMENTS, "Caller", "Pair", 0, 1),
        Err(Unproved::ReadReadPeers),
        "wave-6k's consumer owns every two-argument read/read call (R396-2)"
    );
}
