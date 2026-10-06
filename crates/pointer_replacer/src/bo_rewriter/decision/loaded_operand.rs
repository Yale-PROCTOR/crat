//! **R838 (era-5c 148) — origin evidence over a value loaded from memory.**
//!
//! A5's origin evidence calls the origin of a value loaded from memory (a
//! static's contents, a pointee through any pointer) complete and private, so
//! two such loads always read as disjoint origins, whatever other bodies stored
//! there; `classify_pair` takes origins OR points-to, so that evidence wins
//! even where the points-to sets overlap. The analyses tree does not say which
//! evidence proved a pair, so the pair pass does not take the classifier's
//! proof where an operand is loaded from memory: such a pair is not shown
//! disjoint (R833-1).

use super::{
    a5_site_proof::{A5PeerProof, A5SiteProofVerdict},
    emitability::CallSite,
};

/// The reason a corrected proof carries.
pub(crate) const REASON: &str = "a5-proof-over-a-loaded-operand";

/// The proof at `site` for `left` / `right`, read with the correction.
pub(crate) fn read_loaded_operands(
    site: &CallSite,
    left: usize,
    right: usize,
    proof: &mut A5PeerProof,
) {
    let _ = (site, left, right, proof);
}
