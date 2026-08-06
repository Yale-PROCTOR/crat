//! **The canonical, session-independent name of a BO slot.**
//!
//! Every rustc handle a slot is made of — `LocalDefId`, `SlotId`, `HirId`,
//! `Span` — is **session-local**. Serializing one and reading it back in a
//! different compiler session is the key-divergence failure this project has
//! already paid for more than once, so anything that must survive a session
//! boundary is named here instead.
//!
//! The format is `def_path_str`-based, which is stable across sessions for
//! unchanged source:
//!
//! - locals: `{def_path}::_{local}@d{depth}`
//! - fields: `{def_path}::field{index}@d{depth}`
//!
//! # One definition
//!
//! **RELOCATED 2026-08-06 from `bo_c1`**, unchanged, so the analysis-model
//! cache's loader and the harness's snapshot writer share **one** canonicalizer
//! rather than a copy each. The round trip is witnessed by
//! `ownership_yield_model_kind_snapshot_is_byte_stable_and_round_trips`, which
//! passes unchanged across the move — that is the relocation's own check.

use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

pub(crate) fn local_key(
    tcx: TyCtxt<'_>,
    fn_did: LocalDefId,
    local: usize,
    depth: u8,
) -> String {
    format!(
        "{}::_{}@d{depth}",
        tcx.def_path_str(fn_did.to_def_id()),
        local
    )
}

pub(crate) fn field_key(
    tcx: TyCtxt<'_>,
    struct_did: LocalDefId,
    field_index: usize,
    depth: u8,
) -> String {
    format!(
        "{}::field{field_index}@d{depth}",
        tcx.def_path_str(struct_did.to_def_id())
    )
}
