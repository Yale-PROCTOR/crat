//! **S3.2′-1 — `FatFacts`.** The fatness qualifier, adapted for the rewriter.
//!
//! Built on the `MutFacts` precedent: the rewriter consumes an **adapter**, not
//! a raw analysis result. `apply` and `plan` never see either, and until
//! S3.2′-4 lifts the entry, neither does `decision` — the ban is mechanized in
//! [`super::import_denylist`] rather than left to inspection, because a
//! wired-but-dormant path would satisfy every corpus invariant while violating
//! the claim that this slice changes no decision.
//!
//! # The lattice orientation, and why it is the load-bearing fact
//!
//! `Fatness::Arr ⊑ Fatness::Ptr`, and `fatness_analysis` returns the
//! **greatest** model. So the solver maximizes toward `Ptr`, and:
//!
//! - **`Arr` is EVIDENCE.** A variable reads `Arr` only where constraints force
//!   it down from the top. Array-ness is concluded, not assumed.
//! - **`Ptr` is the DEFAULT.** An unconstrained variable reads `Ptr`. It means
//!   *no array evidence was found*, which is **not** the same as *this pointer
//!   is provably to a single object*.
//!
//! That asymmetry decides how the verdict may be used, and it runs opposite to
//! the naive reading of ruling A-1 ("unknown fatness degrades"). This analysis
//! never says *unknown*: it always answers `Arr` or `Ptr`, and the no-evidence
//! case is spelled `Ptr`. Therefore:
//!
//! - emitting a **slice** on `Arr` is licensed — the verdict carries evidence;
//! - treating `Ptr` as proof of single-object allocation is **not** licensed,
//!   and nothing in this crate may do so. Where thinness has to be *established*
//!   rather than defaulted — the `Box<T>` versus `Box<[T]>` discriminator — the
//!   allocation-size expression is the authority and fatness is corroboration
//!   only.
//!
//! [`FatFacts::is_array`] is deliberately the only predicate exposed. There is
//! no `is_thin`, because a caller that could ask that question would be asking
//! the one this analysis cannot answer.

use rustc_middle::mir::Local;
use rustc_hir::def_id::LocalDefId;

use crate::{
    analyses::type_qualifier::foster::fatness::{Fatness, FatnessResult, fatness_analysis},
    utils::rustc::RustProgram,
};

pub(crate) struct FatFacts {
    result: FatnessResult,
}

impl FatFacts {
    pub(crate) fn from_program(program: &RustProgram<'_>) -> Self {
        Self {
            result: fatness_analysis(program),
        }
    }

    /// The raw verdict for a local's **depth-0** pointer position.
    ///
    /// `None` when the local carries no pointer variable at all — a non-pointer
    /// local, or an index past the function's locals. Distinct from `Ptr`:
    /// absence of a variable is not a verdict.
    pub(crate) fn verdict(&self, fn_did: LocalDefId, local: Local) -> Option<Fatness> {
        self.result.function_body_fact(fn_did, local.index(), 0)
    }

    /// **Is there array evidence for this local?**
    ///
    /// Unused in production until S3.2′-4 wires fatness into the decision
    /// phase — which is the point of the S3.2′-1 split, not an oversight. The
    /// entry-validation controls exercise it now.
    ///
    /// The only predicate offered, for the reason in the module doc: `Arr` is a
    /// conclusion and `Ptr` is a default, so this direction is answerable and
    /// its negation is not.
    #[allow(
        dead_code,
        reason = "S3.2′-1 ships the adapter; S3.2′-4 wires it into `decide_one`. \
                  The split is a reviewer ruling, not a gap: with no fat form to \
                  select, consumption could only degrade. The entry-validation \
                  controls exercise this method today."
    )]
    pub(crate) fn is_array(&self, fn_did: LocalDefId, local: Local) -> bool {
        matches!(self.verdict(fn_did, local), Some(Fatness::Arr))
    }

    /// Rendering for the measurement column. `-` is *no pointer variable*,
    /// which the table keeps distinct from a `ptr` verdict.
    pub(crate) fn render(&self, fn_did: LocalDefId, local: Local) -> &'static str {
        match self.verdict(fn_did, local) {
            Some(Fatness::Arr) => "arr",
            Some(Fatness::Ptr) => "ptr",
            None => "-",
        }
    }
}
