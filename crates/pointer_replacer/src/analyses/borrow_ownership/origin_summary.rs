//! §NB3-3c — the BO-native **origin summary**: the ONLY interface the rest of BO sees for
//! interprocedural signature-origin relations (isolation requirement, ruled 2026-07-11).
//!
//! Derived at 3c-i by wrapping production `lifetime_flow` **read-only** behind a single call site in
//! `origins.rs`. The value-flow⇒subset bridge is the engine's own established semantics
//! (`borrow/mod.rs:760` converts `depth0_value_flows` into `SubsetConstraint`s); the provenance
//! universe is depth-0/Local-grained, so full-depth+field origin granularity exists only in
//! `lifetime_flow`'s `SignatureSlot` model — hence the shape is adopted from it, read-only.
//! At NB5-O the derivation is swapped for BO-native borrow facts (drop-in, gated on a corpus
//! differential); `OriginSummary`'s shape is the stable interface that survives that swap.

use rustc_hash::FxHashMap;
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_span::def_id::LocalDefId;

use crate::analyses::borrow::lifetime_flow::{LifetimeSlot, SignatureSlot};

/// Per-function signature-origin summary.
///
/// - `slots`: the signature slots (origin variables), keyed by `LifetimeSlot` (shape adopted
///   read-only from `lifetime_flow`).
/// - `subset`: the **transitively-closed** origin subset relation. An entry `subset.contains(sub,
///   sup)` means `sub`'s origin flows into (is contained in) `sup`'s — mirroring the engine's own
///   `subset_closure.contains(arg, return)` convention (`borrow/mod.rs:1205`). Built here with a
///   correct multi-hop closure (NOT the 1-hop production `subset_closure` — D3, diagnostic-only).
/// - `unknown`: slots poisoned to top by an opaque callee. Production's conflict path never consumes
///   the analogous `unknown_targets` (verified), so 3c-ii consuming this for candidacy demotion is a
///   fork-only soundness win.
#[derive(Clone, Debug)]
pub struct OriginSummary {
    pub slots: IndexVec<LifetimeSlot, SignatureSlot>,
    /// Note: interprocedural *storage-write* flows (e.g. an output-param `*dst = src`) land in
    /// `subset` at the pointee depth (`src → dst@depth+1`), the same seam `depth0_value_flows`
    /// feeds — so no separate storage relation is carried (lifetime_flow's `storage_aliases` is not
    /// part of the injected subset seam).
    pub subset: SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    pub unknown: DenseBitSet<LifetimeSlot>,
}

/// Per-function origin summaries, keyed like `LifetimeFlowResults`.
pub type OriginSummaries = FxHashMap<LocalDefId, OriginSummary>;
