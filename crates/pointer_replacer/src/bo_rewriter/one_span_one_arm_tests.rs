//! **The one-span-one-arm gate, half (b)** — a FALLBACK arm may not take a span that
//! strictly contains another class's edit.
//!
//! batch 20's brotli lost 69 subjects to six rows of exactly this shape
//! (`agents/artifacts/2026-09-21-batch-20/brotli-new-collisions.txt`):
//!
//! ```text
//! class=1835|arm=pair|interval=lib.rs:8180243:8180565|kind=a5-site-proof-t2-fallback
//!   vs class=1849|arm=surface|interval=lib.rs:8180398:…
//! ```
//!
//! `finalize_class_inputs` sees both sites, cannot compose them, and records a
//! `ClassIntervalCollision` — which blocks BOTH classes. `BrotliHistogramCombine*` and the
//! three `ClusterBlocks*` callers went down together, and 28 of the 97 lost subjects were the
//! whole of `delivered-box`'s regression.
//!
//! A fallback exists to materialize what another arm may already materialize. When its
//! interval strictly contains another class's edit, the right answer is for the FALLBACK to
//! yield its own site — one class stands down instead of two — which is the cross-class form
//! of the yield the A5 planner already makes to the PAIR rendering.
//!
//! These are unit witnesses over `finalize_class_inputs`, which is a pure function of its
//! inputs: no compiler run, no fixture, and the shape is built exactly rather than hoped for.

use super::{
    bridge_receipt::SignatureClassId,
    decision::Arm,
    plan::{ClassInput, ClassSite, finalize_class_inputs},
};

const FILE: &str = "<program>/lib.rs";

fn class(index: u32) -> SignatureClassId {
    use rustc_hir::def_id::{DefIndex, LocalDefId};
    SignatureClassId::of(LocalDefId {
        local_def_index: DefIndex::from_u32(index),
    })
}

fn input(id: SignatureClassId, arm: Arm, lo: u32, hi: u32, kind: &str) -> ClassInput {
    let mut input = ClassInput::new(id, Default::default());
    input
        .sites
        .push(ClassSite::edit(id, id, arm, FILE, lo, hi, kind));
    input
}

/// The brotli shape, to the interval: a pair-arm A5 T2 fallback over `8180243..8180565`
/// strictly containing a surface edit of another class at `8180398..8180420`.
#[test]
fn r499_1b_a_fallback_yields_the_span_it_strictly_contains() {
    let (fallback, surface) = (class(1835), class(1849));
    let finalization = finalize_class_inputs(vec![
        input(
            fallback,
            Arm::Pair,
            8_180_243,
            8_180_565,
            "a5-site-proof-t2-fallback",
        ),
        input(surface, Arm::Surface, 8_180_398, 8_180_420, "surface"),
    ]);
    assert!(
        finalization.collisions.is_empty(),
        "the fallback yields rather than colliding: {:#?}",
        finalization.collisions
    );
    assert!(
        finalization.classes[&surface].is_ready(),
        "the edit the fallback contained survives: {:#?}",
        finalization.classes[&surface]
    );
}

/// Control: two NON-fallback arms overlapping still collide. The rule is about a fallback
/// standing down, not about overlaps being tolerated.
#[test]
fn r499_1b_two_ordinary_arms_still_collide() {
    let (left, right) = (class(700), class(701));
    let finalization = finalize_class_inputs(vec![
        input(left, Arm::Surface, 100, 400, "surface"),
        input(right, Arm::C, 200, 300, "c-argument"),
    ]);
    assert_eq!(
        finalization.collisions.len(),
        1,
        "an ordinary cross-class overlap is still a collision: {:#?}",
        finalization.collisions
    );
}

/// Control: a fallback that merely OVERLAPS — without strictly containing — still collides.
/// Yielding there would drop an edit that covers bytes the other arm does not.
#[test]
fn r499_1b_a_fallback_that_only_overlaps_still_collides() {
    let (fallback, surface) = (class(800), class(801));
    let finalization = finalize_class_inputs(vec![
        input(fallback, Arm::Pair, 100, 300, "a5-site-proof-t2-fallback"),
        input(surface, Arm::Surface, 200, 400, "surface"),
    ]);
    assert_eq!(
        finalization.collisions.len(),
        1,
        "partial overlap is not containment: {:#?}",
        finalization.collisions
    );
}

/// Control: the same class's own overlapping sites are an INTRA-class hold, untouched.
#[test]
fn r499_1b_the_intra_class_hold_is_untouched() {
    let id = class(900);
    let mut only = ClassInput::new(id, Default::default());
    only.sites.push(ClassSite::edit(
        id,
        id,
        Arm::Pair,
        FILE,
        100,
        400,
        "a5-site-proof-t2-fallback",
    ));
    only.sites.push(ClassSite::edit(
        id,
        id,
        Arm::Surface,
        FILE,
        200,
        300,
        "surface",
    ));
    let finalization = finalize_class_inputs(vec![only]);
    assert!(
        finalization.collisions.is_empty(),
        "intra-class is not a collision"
    );
    assert!(
        finalization.classes[&id]
            .hold_reasons()
            .iter()
            .any(|reason| reason == "intra-class-interval-overlap"),
        "{:#?}",
        finalization.classes[&id]
    );
}

/// Control, and the boundary the standing set taught me: a fallback containing a `C`-arm
/// ARGUMENT bridge still collides. That edit is the very thing the fallback's raw view
/// substitutes for — the two are rival renderings of one argument, and
/// `a5_wrapper_composition` is what decides them (wave-5d's
/// `a5_wrapper_over_unselected_argument` pins all three of its cases). Only a contained
/// SURFACE edit, which no raw view can stand in for, is yielded.
#[test]
fn r499_1b_a_fallback_containing_an_argument_bridge_still_collides() {
    let (fallback, argument) = (class(1000), class(1001));
    let finalization = finalize_class_inputs(vec![
        input(fallback, Arm::Pair, 100, 400, "a5-site-proof-t2-fallback"),
        input(argument, Arm::C, 200, 300, "raw-cast-const"),
    ]);
    assert_eq!(
        finalization.collisions.len(),
        1,
        "an argument bridge is a rival rendering, not something to yield to: {:#?}",
        finalization.collisions
    );
}
