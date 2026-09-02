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
    /// **ORIGINAL ← EMITTED line translation for THIS splice** (I-31). Built
    /// from the ACCEPTED edits, here, where they are known — never by scanning
    /// `source` afterwards, which would re-derive what the splicer just did.
    pub line_map: LineMap,
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
    let splices: Vec<(usize, usize, String)> = accepted
        .iter()
        .map(|e| (e.lo, e.hi, e.replacement.clone()))
        .collect();
    Applied {
        line_map: LineMap::from_splices(source, &splices),
        source: out,
        rollbacks,
    }
}

/// **ORIGINAL → EMITTED LINE TRANSLATION, from the emitter's own placement
/// data** (I-31, 2026-08-18).
///
/// # The defect this exists to close
///
/// `attribute()` decides which function owns a verify diagnostic by comparing
/// `diag.line` — a line in the **EMITTED** program — against edit line ranges
/// computed over the **ORIGINAL** source. That is sound only while the emitter
/// preserves line numbering. `render` very nearly does (it splices in place);
/// **`pprust` does not** — it reprints whole functions, so line numbers drift.
///
/// Measured on libtree round 0: span drift stays within 1 line across the whole
/// file, **AST drift accumulates to −36**. Past that, diagnostics are attributed
/// to whichever function *used to* occupy those lines, and the revert loop
/// reverts functions that did nothing wrong. libtree lost 4 subjects this way
/// and brotli gained 1 — **reverts manufactured by the instrument, not by the
/// analysis.**
///
/// # Built from placement data, never by scanning the output
///
/// The segments come from the SAME `(lo, hi, replacement)` triples the splice
/// applies. Re-deriving them by scanning the emitted text would be a second
/// derivation of what the splicer already knows — this module's founding defect
/// class — so the constructor takes the accepted splices and nothing else.
///
/// # Direction
///
/// Translation runs **emitted → original**, so `EditSite`/`EmittedSite` keep
/// their original-source coordinates and only the diagnostic moves. The
/// alternative (translating every site forward) would have rewritten two
/// producers instead of one consumer.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct LineMap {
    /// One per accepted splice, ascending, non-overlapping.
    segments: Vec<Segment>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Segment {
    /// 1-based inclusive line range in the ORIGINAL source.
    orig_lo: usize,
    orig_hi: usize,
    /// 1-based inclusive line range in the EMITTED document.
    emit_lo: usize,
    emit_hi: usize,
}

impl LineMap {
    /// `splices` are the ACCEPTED edits — the ones the splice actually applied.
    /// Order is irrelevant; they are sorted here.
    pub(crate) fn from_splices(source: &str, splices: &[(usize, usize, String)]) -> Self {
        let mut ordered: Vec<&(usize, usize, String)> = splices.iter().collect();
        ordered.sort_by_key(|(lo, hi, _)| (*lo, *hi));

        let line_of = |byte: usize| -> usize {
            // 1-based, matching rustc diagnostics.
            1 + source[..byte.min(source.len())]
                .bytes()
                .filter(|b| *b == b'\n')
                .count()
        };

        let mut segments = Vec::new();
        let mut delta: isize = 0;
        for (lo, hi, replacement) in ordered {
            let orig_lo = line_of(*lo);
            let orig_hi = line_of(*hi);
            let new_lines = replacement.bytes().filter(|b| *b == b'\n').count();
            let emit_lo = (orig_lo as isize + delta).max(1) as usize;
            let emit_hi = emit_lo + new_lines;
            delta += new_lines as isize - (orig_hi - orig_lo) as isize;
            segments.push(Segment {
                orig_lo,
                orig_hi,
                emit_lo,
                emit_hi,
            });
        }
        Self { segments }
    }

    /// Map a line in the emitted document back to a line in the original.
    ///
    /// A line INSIDE a replaced region maps to that region's original start:
    /// the region is one function's reprint, so every line of it belongs to
    /// that function, and the start is the coordinate its `EditSite` carries.
    pub(crate) fn to_original(&self, emit_line: usize) -> usize {
        let mut delta: isize = 0;
        for seg in &self.segments {
            if emit_line < seg.emit_lo {
                break;
            }
            if emit_line <= seg.emit_hi {
                return seg.orig_lo;
            }
            delta += (seg.emit_hi - seg.emit_lo) as isize - (seg.orig_hi - seg.orig_lo) as isize;
        }
        (emit_line as isize - delta).max(1) as usize
    }

    /// Exact offset-preserving map for a replacement whose original and
    /// emitted line spans have equal length. E1 uses this only when the normal
    /// owner-attribution map (which intentionally collapses a whole reprinted
    /// function to its start) names no function. Unequal spans return `None`
    /// rather than guessing an interior correspondence.
    pub(crate) fn to_original_if_bijective(&self, emit_line: usize) -> Option<usize> {
        let mut delta: isize = 0;
        for segment in &self.segments {
            if emit_line < segment.emit_lo {
                break;
            }
            if emit_line <= segment.emit_hi {
                if segment.orig_hi - segment.orig_lo != segment.emit_hi - segment.emit_lo {
                    return None;
                }
                return Some(segment.orig_lo + emit_line - segment.emit_lo);
            }
            delta += (segment.emit_hi - segment.emit_lo) as isize
                - (segment.orig_hi - segment.orig_lo) as isize;
        }
        Some((emit_line as isize - delta).max(1) as usize)
    }

    /// The exact original region corresponding to an emitted line. Inside a
    /// reprinted function this returns that function splice's complete original
    /// line span; outside a splice it returns the ordinary mapped singleton.
    pub(crate) fn original_region(&self, emit_line: usize) -> Option<(usize, usize)> {
        for segment in &self.segments {
            if emit_line < segment.emit_lo {
                break;
            }
            if emit_line <= segment.emit_hi {
                return Some((segment.orig_lo, segment.orig_hi));
            }
        }
        self.to_original_if_bijective(emit_line)
            .map(|line| (line, line))
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
            atom_ids: Vec::new(),
            subject_id: "test::subject".to_owned(),
            required_arms: "-".to_owned(),
            edit_kind: "fixture",
        }
    }

    #[test]
    fn e1_bijective_line_map_preserves_equal_span_offsets_and_refuses_unequal_spans() {
        let equal = LineMap {
            segments: vec![Segment {
                orig_lo: 57,
                orig_hi: 65,
                emit_lo: 57,
                emit_hi: 65,
            }],
        };
        assert_eq!(equal.to_original(60), 57, "ordinary gate map collapses");
        assert_eq!(equal.to_original_if_bijective(60), Some(60));
        assert_eq!(equal.original_region(60), Some((57, 65)));

        let unequal = LineMap {
            segments: vec![Segment {
                orig_lo: 57,
                orig_hi: 65,
                emit_lo: 57,
                emit_hi: 63,
            }],
        };
        assert_eq!(unequal.to_original_if_bijective(60), None);
        assert_eq!(unequal.original_region(60), Some((57, 65)));
    }

    /// **THE libtree SHAPE — accumulated drift, and it must discriminate.**
    ///
    /// A reprint that is SHORTER than what it replaces shifts everything after
    /// it upward, and the shift ACCUMULATES across reprints. That is exactly
    /// what `pprust` does to libtree: span drift stays within 1 line for the
    /// whole file, AST drift reaches −36 by `print_tree`. A one-splice fixture
    /// cannot witness this — the second splice is where accumulation begins.
    ///
    /// Original lines 1..=12; two functions reprinted, each 4 lines → 2.
    ///
    /// *Mutation-tested.* Restore the defect by making `to_original` the
    /// identity (`emit_line`) — i.e. compare emitted lines against original
    /// ranges, the pre-fix behaviour — and the post-drift assertions fail
    /// (9 vs 11, 12 vs 14).
    #[test]
    fn accumulated_drift_maps_emitted_lines_back_to_the_original() {
        let source = "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n11\n12\n";
        let off = |line: usize| -> usize {
            source
                .char_indices()
                .filter(|(_, c)| *c == '\n')
                .nth(line - 2)
                .map(|(i, _)| i + 1)
                .unwrap_or(0)
        };
        // Two replaced regions, each spanning 4 original lines, each emitting 2.
        let splices = vec![
            (off(2), off(6) - 1, "A\nA".to_owned()),
            (off(8), off(12) - 1, "B\nB".to_owned()),
        ];
        let map = LineMap::from_splices(source, &splices);

        // The emitted document is 8 lines:
        //   1 | 1          <- untouched
        //   2 | A          <- reprint of original 2..=5
        //   3 | A
        //   4 | 6          <- untouched, shifted by -2
        //   5 | 7
        //   6 | B          <- reprint of original 8..=11
        //   7 | B
        //   8 | 12         <- untouched, shifted by -4  (ACCUMULATED)
        assert_eq!(
            map.to_original(1),
            1,
            "a line before every splice cannot move"
        );
        assert_eq!(map.to_original(2), 2);
        assert_eq!(
            map.to_original(3),
            2,
            "every line of a reprint belongs to it"
        );
        assert_eq!(
            map.to_original(4),
            6,
            "a line between the reprints carries the FIRST splice's delta"
        );
        assert_eq!(map.to_original(5), 7);
        assert_eq!(map.to_original(6), 8, "inside the second reprint");
        assert_eq!(map.to_original(7), 8);
        // THE discriminating assertion: after BOTH reprints the deltas
        // ACCUMULATE (-4). The identity mapping answers 8 here, which is the
        // pre-fix behaviour and the reason a one-splice fixture is useless.
        assert_eq!(
            map.to_original(8),
            12,
            "drift must ACCUMULATE across reprints -- the libtree shape"
        );
    }

    /// **A line-preserving emitter is the IDENTITY** — the span layer's shape.
    ///
    /// Positive control, labelled as one: it passes under the defect too. Its
    /// job is to show the translation does not invent movement where the
    /// emitter produced none, which is why `render`'s near-zero drift never
    /// surfaced this.
    #[test]
    fn a_line_preserving_splice_translates_to_the_identity() {
        let source = "aaa\nbbb\nccc\nddd\n";
        let splices = vec![(4, 7, "BBB".to_owned())];
        let map = LineMap::from_splices(source, &splices);
        for line in 1..=4 {
            assert_eq!(
                map.to_original(line),
                line,
                "an in-place splice changes no line number"
            );
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
