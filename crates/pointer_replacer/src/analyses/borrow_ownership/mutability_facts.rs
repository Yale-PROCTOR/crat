//! §NB2 — mutability hard facts for the BO borrow replay.
//!
//! Feeds the Foster mutability qualifier into the production borrow verifier's existing
//! per-local `is_mutable` closure (today forced `true` in every BO seam). When a pointer's
//! outermost provenance is immutable, `borrow::invalidates` skips its loan
//! (`invalidates.rs:73` — *loan of immutable provenance does not invalidate*), so two shared
//! reads of one base stop invalidating each other and both survive `Ref`. That is the entire
//! NB2 depth-0 Ref recovery mechanism.
//!
//! This adds NOTHING to the z3 kind solver — no new variable, no kind clause (theorems
//! invariant 7 untouched). Mutability is consumed entirely outside the solve, as a static
//! per-`(LocalDefId, Local)` boolean. The `&T`/`&mut T` distinction is a *readout* fact, not
//! a solver kind (the domain has only `Raw`/`Ref`/`Owning`).
//!
//! Soundness (corrected per adversarial review 2026-07-10 — this is NOT "Foster
//! over-approximates `Mut`"): Foster is *precise per-pointer* — it marks a pointer `Imm` iff
//! that pointer is never written THROUGH, which is NOT the same as its referent cell being
//! immutable. A read-only copy whose cell is written through a *sibling* pointer is therefore
//! `Imm`, and its loan IS skipped by `invalidates.rs:73` — the latent S2-6 cross-alias gap
//! (witnessed by `nb2_cross_alias_write_uncaught_witness`). Two legs keep this sound today:
//!   1. MISSING map data defaults to `Mut` (`is_mutable` below) — the sole unsound *data*
//!      direction (a wrongly-`&T`), so absent facts never wrongly relax a conflict.
//!   2. At the ACCEPTANCE level, the flow-insensitive **coherence equate-closure** unifies each
//!      copy cluster and demotes it to `Raw` when any member is written, so a skipped `Imm`
//!      view never survives as a shared `Ref` aliasing a written cell. This is what actually
//!      guards the cross-alias case (mode-independent — NOT the skip, NOT Foster's direction),
//!      matching production's own `_no_guarantee` posture
//!      (`borrow::classified_references_..._no_guarantee`).
//! If the equate-closure is relaxed for flow-sensitivity (`borrow_verify.rs` BB3-b), the gap
//! becomes an ACCEPTANCE-level unsoundness — hence **S2-6** gates codegen consumption; the §8
//! guardrail (BO unconsumed by codegen) is the further backstop, not the primary reason.

use rustc_hash::FxHashMap;
use rustc_index::IndexVec;
use rustc_middle::mir::Local;
use rustc_span::def_id::LocalDefId;

use crate::{
    analyses::{
        mir_variable_grouping::SourceVarGroups,
        type_qualifier::foster::mutability::mutability_analysis,
    },
    utils::rustc::RustProgram,
};

/// A per-local mutability oracle for the production borrow replay's
/// `is_mutable(LocalDefId, Local)` closure. Implemented by `bool` (uniform — the
/// forced-mutable control / mode `Off`, so pre-NB2 all-mutable callers pass `true`
/// unchanged) and by `&MutFacts` (fact-driven). The `borrow_verify` seams are generic over
/// this, so the seam signatures — not their 40+ existing call sites — carry the change.
pub(crate) trait MutProvider {
    fn is_mutable(&self, fn_did: LocalDefId, local: Local) -> bool;
}

impl MutProvider for bool {
    fn is_mutable(&self, _fn_did: LocalDefId, _local: Local) -> bool {
        *self
    }
}

impl MutProvider for &MutFacts {
    fn is_mutable(&self, fn_did: LocalDefId, local: Local) -> bool {
        MutFacts::is_mutable(self, fn_did, local)
    }
}

/// §NB2 switch. `On` (default) consults Foster; `Off` reproduces the pre-NB2 forced-mutable
/// behavior. Env `CRAT_BO_MUT_FACTS ∈ {off, on}` flips the corpus sweep with no recompile;
/// fixtures never set it and build `MutFacts` directly, so they are deterministic. Only the
/// `bo_c1` driver consults `current()` (to choose `all_mut()` vs `from_program`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MutFactsMode {
    Off,
    On,
}

impl MutFactsMode {
    const DEFAULT: MutFactsMode = MutFactsMode::On;

    pub(crate) fn current() -> MutFactsMode {
        match std::env::var("CRAT_BO_MUT_FACTS").as_deref() {
            Ok("off") => MutFactsMode::Off,
            Ok("on") => MutFactsMode::On,
            _ => MutFactsMode::DEFAULT,
        }
    }

    /// Stable label for reporting (bo_c1 row column).
    pub(crate) fn label(self) -> &'static str {
        match self {
            MutFactsMode::Off => "off",
            MutFactsMode::On => "on",
        }
    }
}

/// Per-`(LocalDefId, Local)` outermost-provenance mutability, built to be BYTE-IDENTICAL to
/// production's `mutables` input (`mutability_analysis` +
/// `SourceVarGroups::postprocess_mut_res`: per-local `any(is_mutable)` across pointer depths,
/// then source-var-group OR). BO thereby adopts production's exact mutability handling rather
/// than a novel scheme.
pub(crate) struct MutFacts {
    /// Empty when `all_mut` — the map is not consulted in that mode.
    mutables: FxHashMap<LocalDefId, IndexVec<Local, bool>>,
    /// `true` ⇒ every pointer is treated mutable (forced-mutable control / mode `Off`).
    all_mut: bool,
}

impl MutFacts {
    /// Forced-mutable: every pointer mutable. The mode-`Off` sweep control and the
    /// non-vacuity control prong of the NB2 fixtures (reproduces pre-NB2 behavior exactly).
    pub(crate) fn all_mut() -> MutFacts {
        MutFacts {
            mutables: FxHashMap::default(),
            all_mut: true,
        }
    }

    /// The production-parity fact map for the whole program. Env-free (deterministic) — mode
    /// gating is applied by the caller. Runs the same two analyses the production rewriter
    /// runs (`mutability_analysis`, `SourceVarGroups`), so the cost is already paid upstream.
    pub(crate) fn from_program(program: &RustProgram) -> MutFacts {
        let result = mutability_analysis(program);
        let mutables = SourceVarGroups::new(program).postprocess_mut_res(program, &result);
        MutFacts {
            mutables,
            all_mut: false,
        }
    }

    /// Per-local outermost-provenance mutability. Missing data (unseen `did` / out-of-range
    /// `Local`) ⇒ `Mut` (the sole sound default). Inherent so the bo_c1 readout can query it
    /// directly (the `&T`/`&mut` split); the `MutProvider` impl delegates here.
    pub(crate) fn is_mutable(&self, fn_did: LocalDefId, local: Local) -> bool {
        if self.all_mut {
            return true;
        }
        self.mutables
            .get(&fn_did)
            .and_then(|per_local| per_local.get(local))
            .copied()
            .unwrap_or(true)
    }

    /// Whether `(fn_did, local)` would fall back to the `Mut` default because the map has no
    /// fact for it (unseen `did` / out-of-range `Local`). Feeds the `mut_default_fires`
    /// reporting column (requirement #1: the missing-data default is the sole unsound
    /// direction, so it is counted). Always `false` under `all_mut` (nothing defaults there).
    pub(crate) fn is_defaulted(&self, fn_did: LocalDefId, local: Local) -> bool {
        !self.all_mut
            && self
                .mutables
                .get(&fn_did)
                .and_then(|per_local| per_local.get(local))
                .is_none()
    }
}
