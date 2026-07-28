//! **Phase 2 — plan.** Decision table in, edits-as-data out. No AST mutation.
//!
//! An edit is a value, and it carries **its own justification**: a re-route
//! carries the `LoanKey` that licenses it (§1.6 admissibility is a content
//! lookup, so the licensing loan is nameable), and a drop-form edit carries the
//! selector site that motivated it. That is what lets [`super::apply`] be
//! analysis-blind — it never has to ask *why*, because the edit says so.
//!
//! # Edits are byte-range splices
//!
//! An edit replaces a half-open byte range of the ORIGINAL source with new
//! text. Two properties follow, and both are why this representation was
//! chosen over pretty-printing a rewritten AST:
//!
//! 1. **Structure-preserving by construction.** Everything outside the edited
//!    ranges is the input, byte for byte — comments, spacing and macro shapes
//!    included. The frozen rewriter's whole-crate pretty-print is exactly the
//!    defect this avoids.
//! 2. **Insertions are the zero-width case** (`lo == hi`), so the statement
//!    insertions S3 needs for drops and moves are the same mechanism, not a
//!    second one.
//!
//! # E1 state visibility
//!
//! Reads the decision table by value. Does NOT read analyses, the export, or
//! decision internals beyond the table it was handed. Hands `apply` a plan by
//! value.
//!
//! # Status
//!
//! S1 lands the **G01 arm**: a pointer parameter's type becomes a reference
//! type. [`Justification`] is shaped against all ten goldens' expected text so
//! the breadth in S2–S3 fills arms rather than reshaping the type.

use super::decision::{Decision, DecisionTable};

/// Why an edit is licensed. **Shaped against all ten goldens; one arm live.**
///
/// The unbuilt arms are deliberate: designing the justification type against
/// every golden now means S3 adds construction sites, not a new type — and the
/// breadth hedge for the walking-skeleton cut rests on exactly that.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Justification {
    /// G01–G03: BO decided this slot is a reference. **Live at S1.**
    KindDecision { kind: &'static str },
    /// G06: a move re-route, licensed by a specific surviving loan. The
    /// `LoanKey` is rendered rather than held so `plan` carries no analysis
    /// type into `apply` — the import rule forbids it, and the string is the
    /// audit trail, not a lookup handle.
    ReRoute { licensing_loan: String },
    /// G04/G05/G08: a drop-form edit (§5.3 (D)), motivated by a selector site.
    DropForm { selector_site: String },
    /// G07/G09: a store form that must NOT drop — (N-raw)/(N-safe)/(R) — or a
    /// P-drop suppression, carrying which rule applied.
    StoreForm { form: &'static str },
}

/// One byte-range splice into the original source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Edit {
    /// Byte offset into the ORIGINAL source, inclusive.
    pub lo: usize,
    /// Byte offset into the ORIGINAL source, exclusive. `lo == hi` inserts.
    pub hi: usize,
    pub replacement: String,
    pub justification: Justification,
}

/// The finished plan handed to [`super::apply`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Plan {
    pub edits: Vec<Edit>,
}

/// Turn decisions into edits.
///
/// `source` is read only to copy the pointee's text verbatim: an emitted
/// `&mut i32` keeps the input's own `i32` rather than a re-rendered type, which
/// is what keeps generics, paths and whitespace inside the pointee intact.
pub(crate) fn plan(table: &DecisionTable, source: &str, span_to_range: impl Fn(rustc_span::Span) -> Option<(usize, usize)>) -> Plan {
    let mut edits = Vec::new();
    for (subject, decision) in &table.entries {
        let Decision::Ref { mutable } = decision else {
            // Degraded subjects produce no edit BY DESIGN — the decision phase
            // already recorded why, and re-deciding here would duplicate the
            // authority the architecture puts in one place.
            continue;
        };
        let (Some((ty_lo, ty_hi)), Some((p_lo, p_hi))) = (
            span_to_range(subject.ty_span),
            span_to_range(subject.pointee_span),
        ) else {
            continue;
        };
        let Some(pointee) = source.get(p_lo..p_hi) else {
            continue;
        };
        let replacement = if *mutable {
            format!("&mut {pointee}")
        } else {
            format!("&{pointee}")
        };
        edits.push(Edit {
            lo: ty_lo,
            hi: ty_hi,
            replacement,
            justification: Justification::KindDecision {
                kind: if *mutable { "Ref(mut)" } else { "Ref(shared)" },
            },
        });
    }
    Plan { edits }
}
