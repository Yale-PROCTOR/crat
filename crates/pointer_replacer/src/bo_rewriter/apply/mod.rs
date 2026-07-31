//! **Phase 3 — apply.** Plan in, rewritten source out. **Analysis-blind.**
//!
//! This phase imports plan structs and nothing else. It performs no lookup, no
//! inference, and no decision: if a question arises here that the plan does not
//! already answer, that is a plan defect, not a reason to import an analysis.
//!
//! The import-denylist test enforces exactly that — `apply/` may not name
//! `crate::analyses`, the export, or `super::decision`.
//!
//! # Rollbacks
//!
//! An edit this phase cannot apply is **rolled back and counted**, never
//! applied partially. The structural gate requires the count to be zero: a
//! nonzero count means the plan asked for something incoherent, and the right
//! response is to fix the plan, not to let a half-applied edit reach the
//! emitted crate.

use super::plan::Edit;

/// Outcome of applying a plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Applied {
    pub source: String,
    /// Edits rejected as incoherent. **Gate requires 0.**
    pub rollbacks: Vec<Rollback>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Rollback {
    pub edit: Edit,
    pub reason: &'static str,
}

/// Splice **one file's** edits into that file's source.
///
/// Edits address the ORIGINAL source, so they are applied back-to-front: a
/// later edit's offsets are then still valid when an earlier one has already
/// changed the string length. Overlapping edits are rejected rather than
/// resolved — a plan that wants two rewrites of one range has not decided.
///
/// Takes a slice rather than the whole [`super::plan::Plan`] because edit
/// offsets are **file-relative**: this function has no way to tell which file a
/// given `(lo, hi)` belongs to, so handing it the whole plan would let a
/// cross-file mix-up look like an ordinary splice. The caller groups; this
/// splices.
pub(crate) fn apply(source: &str, edits: &[Edit]) -> Applied {
    let mut ordered: Vec<&Edit> = edits.iter().collect();
    ordered.sort_by_key(|e| (e.lo, e.hi));

    let mut rollbacks = Vec::new();
    let mut accepted: Vec<&Edit> = Vec::new();
    let mut prev_hi: Option<usize> = None;
    for edit in ordered {
        if edit.lo > edit.hi || edit.hi > source.len() {
            rollbacks.push(Rollback {
                edit: edit.clone(),
                reason: "edit range is out of bounds or inverted",
            });
            continue;
        }
        if !source.is_char_boundary(edit.lo) || !source.is_char_boundary(edit.hi) {
            rollbacks.push(Rollback {
                edit: edit.clone(),
                reason: "edit range does not fall on UTF-8 char boundaries",
            });
            continue;
        }
        if prev_hi.is_some_and(|hi| edit.lo < hi) {
            rollbacks.push(Rollback {
                edit: edit.clone(),
                reason: "edit overlaps an earlier edit",
            });
            continue;
        }
        prev_hi = Some(edit.hi);
        accepted.push(edit);
    }

    let mut out = source.to_owned();
    for edit in accepted.iter().rev() {
        out.replace_range(edit.lo..edit.hi, &edit.replacement);
    }
    Applied {
        source: out,
        rollbacks,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bo_rewriter::plan::{Edit, Justification};

    fn edit(lo: usize, hi: usize, text: &str) -> Edit {
        Edit {
            lo,
            hi,
            replacement: text.to_owned(),
            justification: Justification::KindDecision { kind: "test" },
            owner_fn: "test::owner".to_owned(),
        }
    }

    /// The happy path: disjoint edits apply, no rollbacks.
    #[test]
    fn disjoint_edits_apply_with_no_rollbacks() {
        let src = "abcdef";
        let edits = vec![edit(0, 1, "X"), edit(4, 6, "YZ!")];
        let applied = apply(src, &edits);
        assert_eq!(applied.source, "XbcdYZ!");
        assert!(
            applied.rollbacks.is_empty(),
            "clean plan produced rollbacks: {:?}",
            applied.rollbacks
        );
    }

    /// **Structural gate input.** Overlapping edits are rejected and COUNTED,
    /// never partially applied.
    ///
    /// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the overlap
    /// check in `apply` and this fails — the second edit applies over the first
    /// and `rollbacks` is empty.
    #[test]
    fn overlapping_edits_roll_back_and_are_counted() {
        let src = "abcdef";
        let edits = vec![edit(0, 3, "X"), edit(2, 5, "Y")];
        let applied = apply(src, &edits);
        assert_eq!(
            applied.rollbacks.len(),
            1,
            "an overlapping edit must be rolled back and counted"
        );
        assert_eq!(
            applied.rollbacks[0].reason, "edit overlaps an earlier edit",
            "rollback must name its reason"
        );
        // The surviving edit applied; the rejected one did not.
        assert_eq!(applied.source, "Xdef");
    }

    /// Out-of-bounds and inverted ranges are rejected rather than panicking.
    ///
    /// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the bounds
    /// check and this fails.
    ///
    /// **The reason assertion is load-bearing, and was added after the deletion
    /// SURVIVED without it (S2b.0a.1).** With the bounds check gone, an
    /// out-of-range `hi` is caught one guard later by `is_char_boundary`, which
    /// returns false for any index past the end — so a witness that only counted
    /// rollbacks saw exactly one either way and could not tell which guard
    /// fired. Naming the reason is what makes the two distinguishable, exactly
    /// as the overlap witness above already did.
    #[test]
    fn out_of_bounds_edits_roll_back() {
        let src = "abc";
        let edits = vec![edit(2, 99, "X")];
        let applied = apply(src, &edits);
        assert_eq!(applied.rollbacks.len(), 1);
        assert_eq!(
            applied.rollbacks[0].reason, "edit range is out of bounds or inverted",
            "the rollback must come from the BOUNDS guard, not from a later one \
             that happens to reject the same edit for a different reason"
        );
        assert_eq!(applied.source, src, "a rolled-back edit must not apply");
    }

    /// Edits address the ORIGINAL source, so a length-changing earlier edit
    /// must not shift a later one. Back-to-front application is what buys this.
    ///
    /// *Mutation-tested:* applying front-to-back instead corrupts the second
    /// edit's target and this fails.
    #[test]
    fn length_changing_edits_do_not_shift_later_offsets() {
        let src = "aXbYc";
        let edits = vec![
                edit(1, 2, "LONGER"),
                // Addresses the ORIGINAL offsets of "Y".
                edit(3, 4, "Z"),
            ];
        let applied = apply(src, &edits);
        assert!(applied.rollbacks.is_empty());
        assert_eq!(applied.source, "aLONGERbZc");
    }
}
