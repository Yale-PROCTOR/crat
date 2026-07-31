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

use std::{collections::BTreeMap, path::PathBuf};

use super::decision::{Decision, DecisionTable};

/// Which source file an edit belongs to.
///
/// # Why an enum rather than a `PathBuf`
///
/// The string entry point compiles through `FileName::Custom("main.rs")`, **not**
/// `FileName::Real` — so a key that could only hold a real path would reject
/// every golden. Both cases are first-class here; only [`FileKey::Real`] is
/// writable back to disk, which is the emit layer's concern, not the plan's.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FileKey {
    /// A file on disk.
    Real(PathBuf),
    /// A virtual root — the string entry point's `main.rs`.
    Virtual(String),
}

/// A decision that could not be turned into a placed edit.
///
/// **Counted and attributed, never silently dropped.** Its reason key is
/// aggregate-pinned expected-zero on the frozen corpus, so an occurrence is a
/// finding to rule on rather than a number that quietly moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Unplaceable {
    pub reason: &'static str,
    /// Attribution — which subject, in the artifact's own terms.
    pub detail: String,
}

/// Why an edit is licensed. **Shaped against all ten goldens; one arm live.**
///
/// The unbuilt arms are deliberate: designing the justification type against
/// every golden now means S3 adds construction sites, not a new type — and the
/// breadth hedge for the walking-skeleton cut rests on exactly that.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(
    dead_code,
    reason = "S1 builds only KindDecision; the other arms are shaped against \
              the remaining goldens on purpose, so S3 adds construction sites \
              rather than reshaping the type"
)]
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
    /// **The subject whose rewrite JUSTIFIES this edit** — not the file the edit
    /// lands in, and not necessarily the function containing it.
    ///
    /// In M1 the two coincide: a parameter's type is rewritten inside its own
    /// declaration. **They diverge at S3**, whose call-site adaptation emits
    /// edits into CALLER files while the edit is justified by the CALLEE's
    /// subject. The verify loop reverts by JUSTIFICATION, never by geography —
    /// reverting the file or the containing function would take back edits the
    /// culprit did not cause and leave the ones it did.
    ///
    /// Carried as a rendered path rather than a `LocalDefId` so no compiler type
    /// enters `plan`.
    pub owner_fn: String,
}

/// The finished plan handed to [`super::apply`], **grouped by file**.
///
/// # Why a map keyed by file
///
/// An edit's byte offsets are **file-relative**, so a flat list of edits across
/// a multi-file crate is ambiguous by construction: two edits in different files
/// can carry identical `(lo, hi)`. Keying by file makes *an edit with no file*
/// unrepresentable rather than merely tested, and `BTreeMap` keeps file
/// iteration deterministic (D19: a report whose order permutes between runs is
/// not comparable).
///
/// 10 of the 20 frozen-corpus programs carry subjects across 2–110 source files,
/// which is why the flat shape could not survive contact with the corpus.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Plan {
    pub by_file: BTreeMap<FileKey, Vec<Edit>>,
    /// Decisions that produced no placed edit, with attribution.
    pub unplaceable: Vec<Unplaceable>,
}

/// Turn decisions into edits.
///
/// `source` is read only to copy the pointee's text verbatim: an emitted
/// `&mut i32` keeps the input's own `i32` rather than a re-rendered type, which
/// is what keeps generics, paths and whitespace inside the pointee intact.
/// # Why `source_of` is a per-file lookup and not one `&str`
///
/// **S3-proofing — do not "simplify" this back.** It would be tempting to invoke
/// `plan` once per file with that file's text. That works today, because every
/// edit S1 emits lands in the same file as the subject's declaration. **It
/// breaks at S3:** call-site adaptation emits edits into files *other* than the
/// declaring one, so file identity belongs to the **edit**, not to the
/// invocation. A per-file invocation would have to be unwound the moment S3
/// lands, and the unwinding would be silent — the code would still compile and
/// simply place S3's edits in the wrong file.
///
/// `reverted` names subjects the verify loop has already taken back: they are
/// skipped here rather than removed from the table, so the decision phase stays
/// the single authority on what was decided and the loop only decides what is
/// *emitted*.
pub(crate) fn plan(
    table: &DecisionTable,
    source_of: impl Fn(&FileKey) -> Option<String>,
    span_to_loc: impl Fn(rustc_span::Span) -> Result<(FileKey, usize, usize), &'static str>,
    owner_of: impl Fn(&super::decision::Subject) -> String,
    reverted: &dyn Fn(&super::decision::Subject) -> bool,
) -> Plan {
    let mut by_file: BTreeMap<FileKey, Vec<Edit>> = BTreeMap::new();
    let mut unplaceable = Vec::new();
    for (subject, decision) in &table.entries {
        if reverted(subject) {
            continue;
        }
        let Decision::Ref { mutable } = decision else {
            // Degraded subjects produce no edit BY DESIGN — the decision phase
            // already recorded why, and re-deciding here would duplicate the
            // authority the architecture puts in one place.
            continue;
        };
        let attribution = || {
            format!(
                "{} (param #{})",
                subject.param_name.as_deref().unwrap_or("<unnamed>"),
                subject.hir_index
            )
        };
        // A `Ref` decision implies a syntactic raw-pointer declaration:
        // `decide_one` degrades every other shape with `NonPointerDecl`,
        // precisely because there is no pointee text to copy through an alias.
        let Some(pointee_span) = subject.pointee_span else {
            continue;
        };
        let (ty_file, ty_lo, ty_hi) = match span_to_loc(subject.ty_span) {
            Ok(located) => located,
            Err(reason) => {
                unplaceable.push(Unplaceable { reason, detail: attribution() });
                continue;
            }
        };
        let (pointee_file, p_lo, p_hi) = match span_to_loc(pointee_span) {
            Ok(located) => located,
            Err(reason) => {
                unplaceable.push(Unplaceable { reason, detail: attribution() });
                continue;
            }
        };
        // The pointee's text is copied through verbatim, so it must come from
        // the same file the type is spliced into. Different files here would
        // mean copying bytes across a file boundary by offset — exactly the
        // collapse this grouping exists to prevent.
        if pointee_file != ty_file {
            unplaceable.push(Unplaceable {
                reason: "pointee text is in a different file from the declaration",
                detail: attribution(),
            });
            continue;
        }
        let Some(source) = source_of(&ty_file) else {
            unplaceable.push(Unplaceable {
                reason: "no source text available for the declaring file",
                detail: attribution(),
            });
            continue;
        };
        let Some(pointee) = source.get(p_lo..p_hi) else {
            unplaceable.push(Unplaceable {
                reason: "pointee range is outside its own file's source",
                detail: attribution(),
            });
            continue;
        };
        let replacement = if *mutable {
            format!("&mut {pointee}")
        } else {
            format!("&{pointee}")
        };
        by_file.entry(ty_file).or_default().push(Edit {
            lo: ty_lo,
            hi: ty_hi,
            replacement,
            justification: Justification::KindDecision {
                kind: if *mutable { "Ref(mut)" } else { "Ref(shared)" },
            },
            owner_fn: owner_of(subject),
        });
    }
    Plan { by_file, unplaceable }
}
