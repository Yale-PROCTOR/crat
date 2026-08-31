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
/// **Counted and attributed, never silently dropped.**
///
/// # Expected zero — what is true today, stated exactly
///
/// **Measured** zero on all 20 frozen-corpus programs (S2b.1's emit run), and
/// **not asserted anywhere**: `m1_emit_corpus` reports the count into its row
/// under its measurement-only discipline, and nothing fails on a nonzero. The
/// pin is **scheduled for S2b.3**, alongside the placement-true counters that
/// give it something to be consistent with.
///
/// This doc previously read "aggregate-pinned expected-zero on the frozen
/// corpus". It was pinned nowhere. Prose asserting a check the code does not
/// have is this track's founding failure class, so the claim does not outlive
/// the slice that measured it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Unplaceable {
    pub reason: &'static str,
    /// Attribution — which subject, in the artifact's own terms.
    pub detail: String,
    /// **Identity**, in the `owner_fn::param` form the driver keys emitted
    /// subjects by — which [`Self::detail`] is not: `"p (param #0)"` compares
    /// equal for the `p` of every function in the crate.
    ///
    /// Its purpose is subtraction, not display. `emitted` counts PLACEMENTS as
    /// of S2b.3, and the only way to exclude a decision that produced no edit is
    /// to name it in the same terms the emitting side names its own.
    pub subject: String,
}

/// Why an edit is licensed. **Shaped against all ten goldens; one arm live.**
///
/// The unbuilt arms are deliberate: designing the justification type against
/// every golden now means S3 adds construction sites, not a new type — and the
/// breadth hedge for the walking-skeleton cut rests on exactly that.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(
    dead_code,
    reason = "KindDecision and SeamAdapter are BOTH live; ReRoute/DropForm/\
              StoreForm are shaped against goldens g04-g08 on purpose, so the \
              slice that builds drops and moves adds construction sites rather \
              than reshaping the type. Their emptiness is MEASURED, not \
              assumed: arm 4's census counts every variant per program and the \
              corpus gate holds those three at zero."
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
    /// **S3.6-1**: one expression of glue at a mismatched argument position.
    /// `family` is `"safe"` or `"reborrow"` — the latter carries the aliasing
    /// exposure §5a measured, so the two must stay countable apart.
    SeamAdapter {
        family: &'static str,
        /// **Whether this adapter's length was FABRICATED** (ruling
        /// 2026-08-12). Carried from `spec.len`, never re-derived by testing
        /// the replacement text for the const's name — the classifier
        /// anti-pattern this milestone retired once already.
        ///
        /// It is here rather than only in the seam census because the const
        /// item's insertion is conditioned on a fabricated adapter **surviving
        /// the revert set**, and the surviving set is a `plan` fact.
        fabricated: bool,
    },
    /// A5 C-9 snapshot temp at one retained marked call site.
    C9Mark,
    /// **The fabricated-extent const's declaration** (marker ruling,
    /// 2026-08-15). One per crate, in the crate root file, emitted only when at
    /// least one fabricated adapter survives.
    ///
    /// It has no owning subject, and that is deliberate: keying it to one
    /// adapter's `owner_fn` would delete the const when that function reverts
    /// while other sites still name it (`E0433`, cascading), and keying it to a
    /// never-reverted sentinel would leave a dead const behind when every
    /// fabricated site reverts. It is DERIVED from the surviving edits instead,
    /// which is why it is created after the revert filter rather than before.
    FabricatedLenConst,
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
    /// **The crate ROOT file** — where a crate-level item must go, and the only
    /// place `crate::FALLBACK_SLICE_EXTENT` resolves from.
    ///
    /// Filled by the caller, which is the only party holding a `TyCtxt`; `plan`
    /// itself takes no compiler type. `None` leaves the fabricated-const
    /// insertion **fail-closed** — no root, no insertion, and the fabricated
    /// adapters that need it fail `verify` loudly rather than emitting a crate
    /// with a dangling path.
    pub root_file: Option<FileKey>,
    /// **The fabricated-extent const's TEXT, produced once by the caller.**
    ///
    /// It is carried rather than built where it is spliced because building it
    /// **parses and pretty-prints**, and both need `rustc_span` session globals
    /// — which the verify/revert loop does not have: `rewrite_core`'s `TyCtxt`
    /// closure ends before the loop's `render` calls. Producing it inside
    /// `render` panicked four corpus programs, and only the four in which a
    /// fabricated adapter survived into a loop round.
    ///
    /// So the rule is: **anything needing a compiler session is produced while
    /// one provably exists, and travels as data.** `None` fail-closes — no
    /// text, no insertion, and the adapters that name it fail `verify` loudly
    /// rather than emitting a crate with a dangling path.
    pub len_const_item: Option<String>,
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
///
/// # The non-placing arms, and what each one owes (S2b.2 audit)
///
/// Every path out of the loop that produces no edit is listed here, so *"which
/// arms are silent"* is answerable by reading this file rather than by
/// re-deriving it. A bare `continue` is legitimate only when some **other**
/// component already holds the attribution.
///
/// | arm | disposition |
/// |---|---|
/// | `reverted(subject)` | bare `continue` — the verify loop owns the count |
/// | decision is not `Ref` | bare `continue` — the table holds the `Degradation`, with subject, site and reason |
/// | `pointee_span` is `None` | **`Unplaceable`** — unreachable through the pipeline, so nothing else would hold it |
/// | `span_to_loc(ty_span)` errs | `Unplaceable`, reason from the locator |
/// | `span_to_loc(pointee_span)` errs | `Unplaceable`, reason from the locator |
/// | pointee file ≠ declaration file | `Unplaceable` |
/// | no source text for the file | `Unplaceable` |
/// | pointee range outside its file | `Unplaceable` |
///
/// **Counting — SETTLED AT S2b.3.** The reported `emitted` counts *placements*:
/// every `Unplaceable` recorded here is subtracted from the emitted-subject set
/// by its [`Unplaceable::subject`] identity, so a decision that produced no edit
/// is not reported as a rewrite. It was a count of *decisions* through S2b.2,
/// over-reporting by exactly the unplaceable set.
///
/// Exposure was zero across all 20 frozen programs both before and after, which
/// is why this was a derivation fix rather than a number change — and why it was
/// worth making: a counter that is right by measurement is one corpus change
/// away from being wrong, and the wrongness would present as a yield figure
/// rather than as a failure.
///
/// The count is now also **pinned**: `m1_emit_corpus` fails on a nonzero
/// `unplaceable`, fail-closed on a missing or unparseable value. The pin is
/// meaningful on FAIL rows only because `RewriteOutcome::Degraded` carries the
/// count as of S2b.3; before that it reported a constant.
///
/// **Where alias-typed subjects land today:** a parameter whose *resolved* type
/// is a pointer but whose declaration is a type alias is collected (R-A) with
/// `DeclShape::Alias`, and `decide_one` degrades it as
/// `UnsupportedDeclShape { shape: "alias" }` — a reason named for the declaration
/// shape, which is true but says nothing about what BO concluded for it. The
/// alias-specific relabel is **registered**, to ride whichever slice first makes
/// alias emission live (S3 at the earliest).
pub(crate) fn plan(
    table: &DecisionTable,
    source_of: impl Fn(&FileKey) -> Option<String>,
    span_to_loc: impl Fn(rustc_span::Span) -> Result<(FileKey, usize, usize), &'static str>,
    owner_of: impl Fn(&super::decision::Subject) -> String,
    reverted: &dyn Fn(&super::decision::Subject) -> bool,
) -> Plan {
    let mut by_file: BTreeMap<FileKey, Vec<Edit>> = BTreeMap::new();
    let mut unplaceable = Vec::new();

    // **S3.6-1 seam adapters, placed FIRST.**
    //
    // A seam edit lands in the CALLER's file and is justified by the CALLEE's
    // subject, which is the divergence `Edit::owner_fn`'s doc was written for —
    // and the reason the same-file guard further down does not apply to it. That
    // guard exists because a subject's pointee text is copied by byte offset, so
    // only a *use* edit may cross a file; a seam copies no pointee text, it
    // wraps an expression already present in the caller.
    //
    // Reverting the callee reverts its seams with it, because `owner_fn` is the
    // revert key and every seam carries the callee's path. That is what keeps a
    // half-adapted call from surviving a revert.
    for seam in &table.seams.edits {
        match span_to_loc(seam.span) {
            Ok((file, lo, hi)) => by_file.entry(file).or_default().push(Edit {
                lo,
                hi,
                replacement: seam.replacement.clone(),
                justification: Justification::SeamAdapter {
                    family: match seam.family {
                        super::decision::seam::SeamFamily::Safe => "safe",
                        super::decision::seam::SeamFamily::Reborrow => "reborrow",
                    },
                    fabricated: seam.spec.len.as_ref().is_some_and(|l| l.is_fabricated()),
                },
                owner_fn: seam.owner_fn.clone(),
            }),
            // A span that cannot be located is RECORDED, never dropped: a seam
            // that silently vanishes leaves the callee converted and the call
            // site raw, which is the `E0308` this whole slice exists to remove.
            Err(reason) => unplaceable.push(Unplaceable {
                reason,
                detail: format!("seam adapter for {}", seam.owner_fn),
                subject: seam.owner_fn.clone(),
            }),
        }
    }
    for body in &table.seams.body_edits {
        match span_to_loc(body.span) {
            Ok((file, lo, hi)) => by_file.entry(file).or_default().push(Edit {
                lo,
                hi,
                replacement: body.replacement.clone(),
                justification: Justification::SeamAdapter {
                    family: match body.family {
                        super::decision::seam::SeamFamily::Safe => "safe",
                        super::decision::seam::SeamFamily::Reborrow => "reborrow",
                    },
                    fabricated: false,
                },
                owner_fn: body.owner_fn.clone(),
            }),
            Err(reason) => unplaceable.push(Unplaceable {
                reason,
                detail: format!("body adapter for {}", body.destination),
                subject: body.owner_fn.clone(),
            }),
        }
    }

    for (subject, decision) in &table.entries {
        if reverted(subject) {
            continue;
        }
        // EXHAUSTIVE (S3.0, ruling 5). A `let …else` here compiled clean against
        // a third `Decision` variant and silently produced no edit AND no
        // `Unplaceable` record — measured with a variant probe before the
        // repair: the build named only `artifact::rows` and `degradations()`.
        // A `match` makes the next disposition a compile error at this site.
        let (mutable, use_edits_in, optional, fat, box_plan) = match decision {
            Decision::Ref { mutable } => (mutable, None, false, false, None),
            // The direct callee supplies this local's type. There is no local
            // declaration span to edit; the signature owner is planned by E2.
            Decision::InferredRef { .. } => continue,
            // S3.2′-2: the first disposition that is not declaration-only.
            Decision::Slice { mutable, uses } => (mutable, Some(uses), false, true, None),
            // S3.2′-3: an optional form, thin or fat. Its uses travel the same
            // channel — declaration and uses move together or not at all, which
            // `use_failure` below enforces for every form that has uses.
            Decision::Opt {
                mutable,
                slice,
                uses,
            } => (mutable, Some(uses), true, *slice, None),
            Decision::Box(plan) => (
                &false,
                None,
                plan.optional,
                matches!(plan.shape, super::decision::box_facts::BoxShape::Slice),
                Some(plan),
            ),
            // Degraded subjects produce no edit BY DESIGN — the decision phase
            // already recorded why, and re-deciding here would duplicate the
            // authority the architecture puts in one place.
            Decision::Degraded(_) => continue,
        };
        // Attribution names the universe, so a locals record does not read as a
        // parameter at position 0 — `detail` is what a human reads in an
        // `Unplaceable`, and "p (param #0)" for a local would be a false
        // statement, not merely a vague one. Identity still lives in
        // `Unplaceable::subject`; this is display.
        let attribution = || match subject.kind {
            super::decision::SubjectKind::Param { hir_index } => format!(
                "{} (param #{hir_index})",
                subject.param_name.as_deref().unwrap_or("<unnamed>")
            ),
            super::decision::SubjectKind::Local => format!(
                "{} (local {:?})",
                subject.param_name.as_deref().unwrap_or("<unnamed>"),
                subject.local
            ),
        };
        // The SAME recipe the driver builds its emitted-subject labels with.
        // Two spellings of one identity would make the subtraction silently
        // empty — the failure mode would be `emitted` staying decision-shaped
        // while looking placement-shaped.
        // S3.0′: ONE definition, in `decision`. This site used to build the key
        // by hand and the driver built the same string by hand beside it — a
        // duplicated canonicalizer whose two copies had to be edited together.
        let identity = || subject.identity_key(&owner_of(subject));
        // A `Ref` decision implies a syntactic raw-pointer declaration:
        // `decide_one` degrades every other shape with `UnsupportedDeclShape`,
        // precisely because there is no pointee text to copy through an alias.
        //
        // So this arm is UNREACHABLE through the shipping pipeline — which is
        // exactly why it is ATTRIBUTED rather than skipped. An unreachable arm
        // that `continue`s silently is a subject that vanishes leaving no
        // counter behind the moment its premise stops holding, and the premise
        // lives in a different phase. Backstop against our own bugs, in the
        // shape design counter (c) requires; witnessed by a data-level
        // injection, since nothing in the pipeline can reach it.
        let Some(pointee_span) = subject.pointee_span else {
            unplaceable.push(Unplaceable {
                reason: "Ref decision on a declaration with no pointee span",
                detail: attribution(),
                subject: identity(),
            });
            continue;
        };
        // S3.1: a subject with no DECLARED TYPE has no splice target. Reachable
        // only for locals (an unannotated `let`, or a destructuring pattern
        // whose annotation belongs to the pattern rather than the component),
        // and such subjects degrade in the decision phase — so this arm is a
        // backstop over a population the decision phase has already removed,
        // not the place the case is handled. Recorded because S2b.2's audit
        // requires every non-placing arm to be listed with what it owes.
        let Some(subject_ty_span) = subject.ty_span else {
            unplaceable.push(Unplaceable {
                reason: "subject has no declared type to splice",
                detail: attribution(),
                subject: identity(),
            });
            continue;
        };
        let (ty_file, ty_lo, ty_hi) = match span_to_loc(subject_ty_span) {
            Ok(located) => located,
            Err(reason) => {
                unplaceable.push(Unplaceable {
                    reason,
                    detail: attribution(),
                    subject: identity(),
                });
                continue;
            }
        };
        let (pointee_file, p_lo, p_hi) = match span_to_loc(pointee_span) {
            Ok(located) => located,
            Err(reason) => {
                unplaceable.push(Unplaceable {
                    reason,
                    detail: attribution(),
                    subject: identity(),
                });
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
                subject: identity(),
            });
            continue;
        }
        let Some(source) = source_of(&ty_file) else {
            unplaceable.push(Unplaceable {
                reason: "no source text available for the declaring file",
                detail: attribution(),
                subject: identity(),
            });
            continue;
        };
        let Some(pointee) = source.get(p_lo..p_hi) else {
            unplaceable.push(Unplaceable {
                reason: "pointee range is outside its own file's source",
                detail: attribution(),
                subject: identity(),
            });
            continue;
        };
        let base = if box_plan.is_some() {
            if fat {
                format!("Box<[{pointee}]>")
            } else {
                format!("Box<{pointee}>")
            }
        } else {
            match (fat, *mutable) {
                (false, true) => format!("&mut {pointee}"),
                (false, false) => format!("&{pointee}"),
                (true, true) => format!("&mut [{pointee}]"),
                (true, false) => format!("&[{pointee}]"),
            }
        };
        let replacement = if optional {
            format!("Option<{base}>")
        } else {
            base
        };
        // The USE-SITE edits, placed before the declaration edit is pushed so a
        // use that cannot be located takes the whole subject with it. A subject
        // whose declaration is spliced while one use is left raw is an
        // ill-typed crate, not a partial rewrite.
        let mut use_edits = Vec::new();
        let mut use_failure = None;
        if let Some(box_plan) = box_plan {
            for edit in &box_plan.expr_edits {
                match span_to_loc(edit.span) {
                    Ok((file, lo, hi)) if file == ty_file => use_edits.push(Edit {
                        lo,
                        hi,
                        replacement: edit.replacement.clone(),
                        justification: if box_plan.fabricated_extent
                            && matches!(edit.receipt, "memset-zero-slice" | "realloc-atomic")
                        {
                            Justification::SeamAdapter {
                                family: "box",
                                fabricated: true,
                            }
                        } else if edit.receipt == "c-free-site-drop" {
                            Justification::DropForm {
                                selector_site: edit.receipt.to_owned(),
                            }
                        } else {
                            Justification::KindDecision { kind: "Box(expr)" }
                        },
                        owner_fn: owner_of(subject),
                    }),
                    Ok(_) => {
                        use_failure = Some("Box edit is in a different file from the declaration")
                    }
                    Err(reason) => use_failure = Some(reason),
                }
            }
            for &span in &box_plan.delete_statements {
                match span_to_loc(span) {
                    Ok((file, lo, hi)) if file == ty_file => use_edits.push(Edit {
                        lo,
                        hi,
                        replacement: String::new(),
                        justification: Justification::StoreForm {
                            form: "box-delete-initializer-store",
                        },
                        owner_fn: owner_of(subject),
                    }),
                    Ok(_) => {
                        use_failure = Some(
                            "Box deleted statement is in a different file from the declaration",
                        )
                    }
                    Err(reason) => use_failure = Some(reason),
                }
            }
        }
        for use_edit in use_edits_in.into_iter().flatten() {
            match span_to_loc(use_edit.span) {
                Ok((file, lo, hi)) if file == ty_file => use_edits.push(Edit {
                    lo,
                    hi,
                    replacement: use_edit.replacement.clone(),
                    justification: Justification::KindDecision {
                        kind: if optional { "Opt(use)" } else { "Slice(use)" },
                    },
                    owner_fn: owner_of(subject),
                }),
                Ok(_) => {
                    use_failure = Some("slice use is in a different file from the declaration")
                }
                Err(reason) => use_failure = Some(reason),
            }
        }
        if let Some(reason) = use_failure {
            unplaceable.push(Unplaceable {
                reason,
                detail: attribution(),
                subject: identity(),
            });
            continue;
        }
        let kind = if box_plan.is_some() {
            match (optional, fat) {
                (false, false) => "Box",
                (false, true) => "BoxSlice",
                (true, false) => "OptBox",
                (true, true) => "OptBoxSlice",
            }
        } else {
            match (optional, fat, *mutable) {
                (false, false, true) => "Ref(mut)",
                (false, false, false) => "Ref(shared)",
                (false, true, true) => "Slice(mut)",
                (false, true, false) => "Slice(shared)",
                (true, false, true) => "OptRef(mut)",
                (true, false, false) => "OptRef(shared)",
                (true, true, true) => "OptSlice(mut)",
                (true, true, false) => "OptSlice(shared)",
            }
        };
        by_file
            .entry(ty_file.clone())
            .or_default()
            .extend(use_edits);
        by_file.entry(ty_file).or_default().push(Edit {
            lo: ty_lo,
            hi: ty_hi,
            replacement,
            justification: Justification::KindDecision { kind },
            owner_fn: owner_of(subject),
        });
    }
    Plan {
        by_file,
        unplaceable,
        // Both filled by the caller; `plan` has no `TyCtxt`, so it can ask
        // neither which file is the crate root nor the parser for an item.
        root_file: None,
        len_const_item: None,
    }
}

#[cfg(test)]
mod tests {
    use rustc_middle::mir::Local;

    use super::*;
    use crate::bo_rewriter::decision::{DeclShape, Subject};

    /// A subject the collector really does build: an alias-typed declaration
    /// whose RESOLVED type is a pointer. It carries `pointee_span: None`,
    /// because an alias hides the `*mut` and there is no pointee text to copy.
    fn alias_subject() -> Subject {
        Subject {
            fn_did: rustc_hir::def_id::CRATE_DEF_ID,
            local: Local::from_u32(1),
            hir_id: rustc_hir::CRATE_HIR_ID,
            param_name: Some("p".to_owned()),
            kind: crate::bo_rewriter::decision::SubjectKind::Param { hir_index: 0 },
            ptr_depth: 1,
            label: "f::p".to_owned(),
            ty_span: Some(rustc_span::DUMMY_SP),
            binding_span: rustc_span::DUMMY_SP,
            pointee_span: None,
            decl_shape: DeclShape::Alias,
            mutable: false,
            freed_at: None,
            len_recovered: false,
            null_init: false,
            mut_binding: false,
            ctor: None,
        }
    }

    /// **The arm-3 witness.** A `Ref` decision on a declaration with no pointee
    /// span is recorded as `Unplaceable`, not skipped.
    ///
    /// # Why the injection is data-level
    ///
    /// `decide_one` degrades every non-`RawPtr` declaration shape, so no input
    /// program can reach this arm — it is a backstop, and a backstop that
    /// cannot be exercised is indistinguishable from one that is not there.
    /// The reachability Rider 5 asks for is supplied HERE, by handing `plan` a
    /// table it could not have produced itself: `plan` is a pure function over
    /// its input, so the constructed table is the whole seam. **No `cfg` or env
    /// hook exists in shipping code for this** — phase separation is what makes
    /// the cheap route also the clean one.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* delete the
    /// `unplaceable.push(..)` in that arm and this fails on the length.
    #[test]
    fn a_ref_decision_with_no_pointee_span_is_attributed_not_skipped() {
        let table = DecisionTable {
            seams: Default::default(),
            c9_marks: Vec::new(),
            entries: vec![(alias_subject(), Decision::Ref { mutable: false })],
        };

        let planned = plan(
            &table,
            |_| Some("fn f(p: PtrAlias) {}".to_owned()),
            // Doubles as an ORDERING assertion: the arm must short-circuit
            // before anything tries to locate a span, because the span it would
            // locate is the one that does not exist.
            |_: rustc_span::Span| -> Result<(FileKey, usize, usize), &'static str> {
                panic!("the missing-pointee arm must fire before any span is located")
            },
            |_| "f".to_owned(),
            &|_| false,
        );

        assert!(
            planned.by_file.is_empty(),
            "no edit can be placed without a pointee span, yet one was: {:?}",
            planned.by_file
        );
        assert_eq!(
            planned.unplaceable.len(),
            1,
            "the subject vanished with no attribution — this is the silent \
             `continue` the arm was replaced to prevent: {:?}",
            planned.unplaceable
        );
        assert_eq!(
            planned.unplaceable[0].reason,
            "Ref decision on a declaration with no pointee span"
        );
        assert!(
            planned.unplaceable[0].detail.contains("p (param #0)"),
            "the record must name WHICH subject, in the artifact's own terms: {:?}",
            planned.unplaceable[0].detail
        );
    }

    /// The same table with the same subject **decided as degraded** places
    /// nothing and records nothing — the decision table already holds that
    /// attribution, so a second record here would double-count it.
    ///
    /// Without this, the arm above could be "satisfied" by an implementation
    /// that reports every non-emitting subject as unplaceable, which would make
    /// the corpus's measured zero meaningless.
    #[test]
    fn a_degraded_subject_is_not_also_reported_unplaceable() {
        let table = DecisionTable {
            seams: Default::default(),
            c9_marks: Vec::new(),
            entries: vec![(
                alias_subject(),
                Decision::Degraded(crate::bo_rewriter::decision::Degradation {
                    subject: "f::p".to_owned(),
                    site: "f.rs:1".to_owned(),
                    reason: crate::bo_rewriter::decision::DegradeReason::UnsupportedDeclShape {
                        shape: "alias",
                    },
                }),
            )],
        };

        let planned = plan(
            &table,
            |_| Some("fn f(p: PtrAlias) {}".to_owned()),
            |_: rustc_span::Span| -> Result<(FileKey, usize, usize), &'static str> {
                panic!("a degraded subject must not reach span location")
            },
            |_| "f".to_owned(),
            &|_| false,
        );

        assert!(planned.by_file.is_empty(), "{:?}", planned.by_file);
        assert!(
            planned.unplaceable.is_empty(),
            "a degradation the TABLE already attributes was recorded a second \
             time here: {:?}",
            planned.unplaceable
        );
    }
}
