//! W-C4: a raw-boundary node is "handled" by the sites the raw boundary owns.
//!
//! `RawBoundaryFacts::derive` decides per site whether the T1 / T2 bridge (or
//! another arm) handles it, then folds those verdicts into a per-node
//! conjunction that `opens_argument` / `opens_span` consult before the seam's
//! silent-coercion gate. A site whose callee parameter CONVERTS is not a raw
//! boundary at all — it is the seam's own safe→safe edge, adapted by
//! `co_conversion` — so its raw-bridge verdict says nothing about the node.
//! Folding it in as "unhandled" refused every subject whose calls mix
//! converting targets with raw targets (`borrowed-into-raw-param` /
//! `flows-into-raw-param` at the seam), although each raw site had its
//! bridge. Only a BRIDGED site (T1 / T2) at a converting target is neutral.
//!
//! A blocked site always votes: `target_stays_raw` reads the hypothetical
//! table, and a parameter that converts there can still degrade in
//! production (`keep(&mut (*h).space)` with `p` stored to a `static mut`
//! degrades `escapes-via-static-store`) — then the site IS a raw target at the
//! terminal, its bridge is refused, and the borrow would coerce silently.
use super::raw_boundary::RawBoundaryDisposition;

pub(crate) fn site_votes(target_stays_raw: bool, disposition: &RawBoundaryDisposition) -> bool {
    target_stays_raw
        || matches!(
            disposition,
            RawBoundaryDisposition::OwnedByOtherArm { .. } | RawBoundaryDisposition::Blocked { .. }
        )
}
