//! **S3.2′-3 task 1 — `SignFacts`.** The offset-sign verdict, adapted.
//!
//! Built on the `MutFacts`/`FatFacts` precedent: the rewriter consumes an
//! **adapter**, never a raw analysis result, and `plan`/`apply` never see
//! either.
//!
//! # The exported result is TWO-way, and that is a property of the analysis
//!
//! `OffsetSignResult::access_signs` is a single bit per local: membership means
//! *this pointer is in a cursor-tainted SCC*. The seed is
//! `AbsValue::needs_cursor()`, which admits `Neg`, `NonPos`, `Top`, and negative
//! constants **through one door**. So `provably negative` and `unknown sign` are
//! indistinguishable at this surface.
//!
//! The three-way split the reslice decision would like — non-negative /
//! negative / unknown — is therefore **not derivable here**, and this adapter
//! does not pretend otherwise. Widening `OffsetSignResult` would change a frozen
//! analysis with four legacy consumers (`rewriter/decision.rs`,
//! `rewriter/collector.rs`, `rewriter/transform/mod.rs`,
//! `analyses/fn_ptr_rewrite_decision.rs`), which is a ruling, not a slice task.
//!
//! For **form selection** the narrowing costs nothing: `Neg` and `Top` both mean
//! *not reslice*. It costs only the internal split of the cursor market, which
//! is why every census column here reads `neg-or-unknown` and never `negative`.
//!
//! # What BO consumes, and how it differs from what the legacy rewriter consumes
//!
//! Every legacy call site postprocesses `access_signs` through
//! `MirVariableGrouping::postprocess_offset_signs` before use. BO's path has no
//! such grouping, so **this adapter consumes the raw capture** — stated here
//! because the two are not the same verdict, and a reader comparing BO's numbers
//! against the legacy rewriter's would otherwise assume they were.
//!
//! # The `None` policy
//!
//! `None` is a lookup miss — no entry for the function, or a local past the
//! body's domain. At the decision layer it reads as **may-be-negative**, the
//! conservative direction (it refuses a reslice rather than inventing one).
//! [`Self::render`] reports the raw capture, so measurement never sees the
//! policy: instruments measure the capture, the `FatFacts` rule.

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::Local;

use crate::{
    analyses::offset_sign::sign::{OffsetSignResult, offset_sign_analysis},
    utils::rustc::RustProgram,
};

pub(crate) struct SignFacts {
    result: OffsetSignResult,
}

impl SignFacts {
    pub(crate) fn from_program(program: &RustProgram<'_>) -> Self {
        Self {
            result: offset_sign_analysis(program),
        }
    }

    /// The raw capture. `Some(true)` = cursor-tainted; `Some(false)` = analyzed
    /// and not tainted; `None` = no verdict for this local.
    pub(crate) fn verdict(&self, fn_did: LocalDefId, local: Local) -> Option<bool> {
        let set = self.result.access_signs.get(&fn_did)?;
        // `DenseBitSet::contains` panics past its domain, and a subject's local
        // can outrun the body the analysis sized the set from.
        if local.index() >= set.domain_size() {
            return None;
        }
        Some(set.contains(local))
    }

    /// **May this pointer be offset negatively?** The one predicate offered.
    ///
    /// There is deliberately no `is_non_negative` with a different `None`
    /// policy: a caller that wanted the other default would be asking this
    /// analysis to assert non-negativity where it has no verdict.
    #[allow(
        dead_code,
        reason = "S3.2′-3 task 1 ships the adapter; the sign-keyed split (task 2) \
                  and the reslice decision consume it. The entry-validation \
                  controls exercise it today."
    )]
    pub(crate) fn may_be_negative(&self, fn_did: LocalDefId, local: Local) -> bool {
        self.verdict(fn_did, local).unwrap_or(true)
    }

    /// Rendering for the measurement column — the raw capture, never the policy.
    pub(crate) fn render(&self, fn_did: LocalDefId, local: Local) -> &'static str {
        match self.verdict(fn_did, local) {
            Some(true) => "neg-or-unknown",
            Some(false) => "nonneg",
            None => "-",
        }
    }
}

#[cfg(test)]
mod tests {
    /// **A-2 entry validation — the discriminating pair, in ONE function.**
    ///
    /// A positive control each way is not enough on its own: two controls in two
    /// bodies can both pass while the adapter is really reporting a per-function
    /// property. So both subjects live in the same body, offset in opposite
    /// directions, and the adapter must separate them.
    ///
    /// It asserts the **raw capture** (`render`), not `may_be_negative`, because
    /// the `None` policy would make a lookup miss pass for a verdict — which is
    /// exactly the confusion the `FatFacts` `None`-vs-`Ptr` rule exists to stop.
    #[test]
    fn the_adapter_separates_a_negative_offset_from_a_non_negative_one() {
        use std::fs;

        const SRC: &str = r#"#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]
pub unsafe fn s_pair(up: *mut i32, down: *mut i32) -> i32 {
    *up.offset(1) + *down.offset(-1)
}
"#;
        let dir = std::env::temp_dir().join(format!("crat-sign-facts-{}", std::process::id()));
        fs::create_dir_all(&dir).expect("fixture dir");
        let root = dir.join("lib.rs");
        fs::write(&root, SRC).expect("fixture written");

        let rendered = ::utils::compilation::run_compiler_on_path(&root, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::SignFacts::from_program(&program);
            let fn_did = *program
                .functions
                .iter()
                .find(|d| tcx.def_path_str(d.to_def_id()).ends_with("s_pair"))
                .expect("the fixture's function");
            // Parameters are `_1`, `_2` in declaration order.
            (
                facts.render(fn_did, rustc_middle::mir::Local::from_usize(1)),
                facts.render(fn_did, rustc_middle::mir::Local::from_usize(2)),
            )
        })
        .expect("fixture compiles");
        let _ = fs::remove_dir_all(&dir);

        assert_eq!(
            rendered,
            ("nonneg", "neg-or-unknown"),
            "the adapter must separate `up.offset(1)` from `down.offset(-1)` \
             within one body; got (up, down) = {rendered:?}"
        );
    }
}
