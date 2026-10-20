//! BO-native origin-summary domain: the only interface the rest of BO sees for interprocedural
//! signature-origin relations.
//!
//! NB5-O replaced both the wrapped production derivation and its production-owned slot types. The
//! active path is derived by `origin_flow`; the wrapped route remains test-only as the frozen
//! differential oracle.

use std::ops::{Deref, DerefMut};

use rustc_hash::FxHashMap;
use rustc_index::{
    IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};
use rustc_middle::mir::Local;
use rustc_span::def_id::LocalDefId;

use super::{origin_flow::OriginFlowResults, slots::StructFieldSlot};

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "O_({})"]
    pub struct OriginSlot {}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SignatureRoot {
    Return,
    Arg(Local),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SignaturePlace {
    pub root: SignatureRoot,
    pub deref_depth: u8,
    pub field: Option<StructFieldSlot>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SignatureSlot {
    pub place: SignaturePlace,
    pub depth: u8,
}

/// Per-function signature-origin summary.
///
/// - `slots`: BO-owned signature slots (origin variables), keyed by `OriginSlot`.
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
    pub slots: IndexVec<OriginSlot, SignatureSlot>,
    pub subset: SparseBitMatrix<OriginSlot, OriginSlot>,
    pub unknown: DenseBitSet<OriginSlot>,
}

// NOTE — storage aliases are NOT a separate field: `compute_origins` folds them INTO `subset` by
// unioning `summary.storage_aliases` into `summary.value_flows` before the transitive closure. This
// is deliberate and load-bearing (Codex 3c-i re-review): `value_flows` alone is NOT a superset of
// `storage_aliases` — `to_summary()` re-projects value-flow targets through an
// `observable_value_target` filter (lifetime_flow.rs:758) that drops some argument depth-0 targets,
// whereas `storage_aliases` is retained UNFILTERED (:774), so a symmetric storage direction to a
// non-observable arg slot survives only in `storage_aliases`. Folding it into `subset` keeps the
// complete (both-directions) relation in one matrix.

/// Per-function BO-native origin summaries plus the body-level flows used by replay.
///
/// Keeping both products together ensures the whole-program flow fixpoint runs once and both
/// consumers observe the same derivation.
#[derive(Clone, Debug, Default)]
pub struct OriginSummaries {
    summaries: FxHashMap<LocalDefId, OriginSummary>,
    native_flows: Option<OriginFlowResults>,
}

impl OriginSummaries {
    pub(crate) fn native(
        summaries: FxHashMap<LocalDefId, OriginSummary>,
        native_flows: OriginFlowResults,
    ) -> Self {
        Self {
            summaries,
            native_flows: Some(native_flows),
        }
    }

    pub(crate) fn native_flows(&self) -> &OriginFlowResults {
        self.native_flows
            .as_ref()
            .expect("active BO origins must retain native body flows")
    }

    pub(crate) fn try_native_flows(&self) -> Option<&OriginFlowResults> {
        self.native_flows.as_ref()
    }
}

impl FromIterator<(LocalDefId, OriginSummary)> for OriginSummaries {
    fn from_iter<T: IntoIterator<Item = (LocalDefId, OriginSummary)>>(iter: T) -> Self {
        Self {
            summaries: iter.into_iter().collect(),
            native_flows: None,
        }
    }
}

impl Deref for OriginSummaries {
    type Target = FxHashMap<LocalDefId, OriginSummary>;

    fn deref(&self) -> &Self::Target {
        &self.summaries
    }
}

impl DerefMut for OriginSummaries {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.summaries
    }
}
