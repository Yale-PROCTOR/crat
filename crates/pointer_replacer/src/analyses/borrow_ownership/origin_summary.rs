//! §NB3-3c — the BO-native **origin summary**: the ONLY interface the rest of BO sees for
//! interprocedural signature-origin relations (isolation requirement, ruled 2026-07-11).
//!
//! Derived at 3c-i by wrapping production `lifetime_flow` **read-only** behind a single call site in
//! `origins.rs`. The value-flow⇒subset bridge is the engine's own established semantics
//! (`borrow/mod.rs:760` converts `depth0_value_flows` into `SubsetConstraint`s); the provenance
//! universe is depth-0/Local-grained, so full-depth+field origin granularity exists only in
//! `lifetime_flow`'s `SignatureSlot` model — hence the shape is adopted from it, read-only.
//! At NB5-O the derivation is swapped for BO-native borrow facts, gated on a corpus differential.
//! **This is NOT a drop-in swap** (corrected after the 3c-i adversarial review): only the CONCEPTUAL
//! `slots`/`subset`/`unknown` boundary survives — NB5-O must also replace the production-owned types
//! this interface is built from (`LifetimeSlot`, `SignatureSlot`, and `derive_signature_flows`'s
//! `LifetimeFlowResults` return) with BO-owned index/place/slot types, keeping the production→BO
//! conversion behind the one adapter. The isolation holds (one call site + one type boundary); the
//! type replacement is the real NB5-O work.

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
/// - `unknown`: slots at least one of whose may-definitions has NO trackable borrow origin — an
///   opaque-callee RESULT **or** a freshly `malloc`'d OWNED pointer. **This is "no-borrow-origin", NOT
///   "opaque-poisoned"** (NB4-4c dump correction: the `malloc_only` vs `malloc_opaque` ablation proves
///   an opaque call adds nothing to this set). **It is a MAY-set, not an exclusive partition** (Codex
///   re-review 2026-07-17): a slot with a REAL modeled origin can also be here via a stale-but-may-reach
///   opaque def that a later assignment kills — so membership means "some may-def is origin-less", NOT
///   "this slot has no origin". Production's conflict path never consumes the analogous `unknown_targets`
///   (verified), so NB4-4c consuming this for the may-supply `¬ref` demotion is a fork-only win — sound
///   because `¬ref` is CONSERVATIVE (`Ref → Raw`), not because membership is exclusive. `¬ref` ONLY: an
///   owned member must keep `Owning` (a uniform `¬own` over-demotes it). The may-set over-inclusion
///   collaterally demotes modeled-origin slots via coherence — completeness-class, marker-pinned
///   (`nb4_4c_marker_coherence_collateral_demotes_modeled_origin`), fix deferred (definitely-overwritten
///   vs may-reach distinction).
#[derive(Clone, Debug)]
pub struct OriginSummary {
    pub slots: IndexVec<LifetimeSlot, SignatureSlot>,
    pub subset: SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    pub unknown: DenseBitSet<LifetimeSlot>,
}

// NOTE — storage aliases are NOT a separate field: `compute_origins` folds them INTO `subset` by
// unioning `summary.storage_aliases` into `summary.value_flows` before the transitive closure. This
// is deliberate and load-bearing (Codex 3c-i re-review): `value_flows` alone is NOT a superset of
// `storage_aliases` — `to_summary()` re-projects value-flow targets through an
// `observable_value_target` filter (lifetime_flow.rs:758) that drops some argument depth-0 targets,
// whereas `storage_aliases` is retained UNFILTERED (:774), so a symmetric storage direction to a
// non-observable arg slot survives only in `storage_aliases`. Folding it into `subset` keeps the
// complete (both-directions) relation in one matrix. Consequence for 3c-ii: storage reachability is
// in `subset` and injected whenever `subset` is — no independent storage lever at the thin-reuse
// wrap; value-only vs value+storage selectivity would require a BO-native derivation (NB5-O).

/// Per-function origin summaries, keyed like `LifetimeFlowResults`.
pub type OriginSummaries = FxHashMap<LocalDefId, OriginSummary>;
