//! **The artifact contract.** One row per subject, JSONL, shared by both
//! producers.
//!
//! # Sharing this file is not sharing a derivation
//!
//! Producer A (`bo_rewriter::artifact`) and producer B
//! ([`super::producer_b`]) both encode through these types. That is
//! deliberate and is *not* a weakening of the independence this module exists
//! for: **independence lives in VALUE DERIVATION, not in serialization.** A
//! hand-rolled second encoder would buy only spurious mismatches — differences
//! in quoting or field order reported as coverage findings — while leaving the
//! derivations exactly as coupled or uncoupled as they already are.
//!
//! # Encoding, pinned
//!
//! - **Explicit `null`, never field omission**, on both sides. There is no
//!   `skip_serializing_if` anywhere in this file, which makes omission
//!   *impossible* rather than merely tested. `witnesses.rs` pins the bytes.
//! - **Fixed field order** — serde emits in declaration order, so the order
//!   below is the wire order.
//! - **Sorted by `(fn_path, mir_local)`** before writing, by
//!   [`sort_rows`]. D19's lesson: a report whose row order permutes between
//!   runs is not comparable, and content-keyed ordering is the fix that already
//!   worked for `LoanKey`.
//!
//! # Who fills what
//!
//! | field | producer A | producer B | reconciled? |
//! |---|---|---|---|
//! | `fn_path`, `mir_local` | ✓ | ✓ | alignment key |
//! | `param_name`, `arg_index` | ✓ | ✓ | **PAIRING** — fail-loud on mismatch |
//! | `ptr_depth` | ✓ | ✓ | classification — attributed finding |
//! | `pairing_confidence` | ✓ | ✓ | gates the severity of a pairing mismatch |
//! | `decl_span`, `decl_shape` | ✓ | `null` | attribution only, not compared |
//! | `decl_span_lo/hi` | ✓ | `null` | **SPAN axis** — A's half of the interleave |
//! | `binding_span_lo/hi` | `null` | ✓ | **SPAN axis** — B's half, and the activation signal |
//! | `outcome`, `degrade_reason` | ✓ | `null` | S2b consumes; not compared |
//! | `freed` | ✓ | `null` | co-attribution; not compared |
//! | `approx_len` | ✓ | `null` | U-2′ counter; not compared |
//!
//! `decl_span` (the rendered string) is not reconciled: A's span is the declared
//! *type*'s span, and the nearest MIR-side fact is the *binding*'s span, so an
//! EQUALITY comparison would report a guaranteed difference on every row. That
//! reasoning was correct but **incomplete** — equality is not the only relation
//! available. Track 2 adds the numeric fields and compares them by **order**:
//! `binding_i.hi ≤ ty_i.lo` and `ty_{i-1}.hi ≤ binding_i.lo`. Measured on 3173
//! corpus parameters with zero exceptions, and it breaks under a permutation,
//! which equality could never have detected without a shared derivation.

use serde::{Deserialize, Serialize};

/// How the parameter's declaration is written in source. **Producer A only** —
/// it is a HIR property, and producer B is MIR-derived by design.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum DeclShape {
    RawPtr,
    Alias,
    Reference,
    Other,
}

/// What M1 decided for a subject. **Total over dispositions, and closed.**
///
/// Totality is the ruling's requirement and it is about **row presence**: a
/// kept-`Raw` subject emits a row exactly as an emitted `Ref` does. Without
/// that, *covered-but-unchanged* and *dropped* are indistinguishable in the
/// diff — both would be an absent row — which is the same conflation A1 exists
/// to retire, reintroduced at the artifact layer.
///
/// "Dropped" is deliberately **not** a value here. A dropped subject is
/// row-*absence* in producer A, which is precisely what a B-only row detects.
///
/// The mechanization lives at the construction site: `bo_rewriter::artifact`
/// matches `Decision` **exhaustively, with no `_` arm**, so a new `Decision`
/// variant (S3's `Box` family) breaks the build instead of silently mapping to
/// a default.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Outcome {
    RefMut,
    RefShared,
    Degraded,
    /// **S3.2′-2** — a borrowed slice form, `&[T]` / `&mut [T]`.
    SliceShared,
    SliceMut,
    /// **S3.2′-3** — an optional form, `Option<&T>` / `Option<&mut T>` and their
    /// fat twins. Four values rather than two because the reference axis and the
    /// fatness axis are independently reported everywhere else, and collapsing
    /// them here would make the artifact the one place they are not.
    OptRefShared,
    OptRefMut,
    OptSliceShared,
    OptSliceMut,
}

/// Whether the pairing for this row can be trusted.
///
/// `Low` is set when a parameter's `var_debug_info` entry count is not exactly
/// one. **On the emittable universe the reachable case is count 0** (measured
/// 2026-07-31), and it covers both an unnamed `_` and a **pattern parameter**,
/// whose bindings become fresh non-parameter locals and so match nothing:
/// `fn s(&x: &*mut i32)` is depth 2, emits a row, and lands here with entry
/// count 0.
///
/// > **"and so match nothing" SUPERSEDED at S3.1** (ruling C, 2026-08-05) —
/// > annotated in place, not erased, because it is the correct reading of the
/// > **parameter-only** universe this row was written for. Once the LOCALS
/// > universe exists, a pattern parameter's component bindings are exactly the
/// > fresh non-parameter locals that universe enumerates, so they **do** match —
/// > as ordinary locals rows. Measured 2026-08-05:
/// > `fn patterned((a, b): (*mut i32, *mut i32))` gives `_2`/`_3`, one entry
/// > each, `argument_index: None`. Nothing about the *parameter* row changes:
/// > the tuple local is still depth 0 and still emits no row.
///
/// **Corrected 2026-07-31.** This comment previously said "more than one covers
/// a pattern parameter such as `fn f((a, b): (*mut i32, *mut i32))`". That was
/// false twice over: the tuple parameter's argument local is a **tuple at
/// pointer depth 0**, so it emits **no row at all** and cannot illustrate any
/// `PairingConfidence` value; and its matching entry count is **0**, not "more
/// than one". No probed shape produced a count above one — that branch is
/// phase-defensive, not an observed population, which is why its incidence is
/// aggregate-pinned rather than exercised by a fixture.
///
/// A `Low` row's pairing disagreement
/// is classified as an attributed finding rather than a violation, because the
/// instrument — not necessarily the collector — is the thing in doubt.
///
/// **That classification does not currently change the program outcome**
/// (ruling 2026-07-31, option A): every finding class is pinned to
/// expected-zero, so a low-confidence mismatch fails its program exactly as a
/// violation does. The downgrade buys triage today; its verdict-level effect is
/// registered as option (B) and triggers when a corpus with legitimate
/// low-confidence incidence enters scope. On frozen rs-crown that incidence is
/// zero — C2Rust emits no pattern or unnamed parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum PairingConfidence {
    High,
    Low,
}

/// One subject. Field order here **is** the wire order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Row {
    pub fn_path: String,
    /// MIR local of the **subject**. With `fn_path`, the alignment key.
    ///
    /// "Subject" rather than "parameter" since S3.1 (H-3, 2026-08-05): the row
    /// population is parameters **and** named pointer locals. Doc text only —
    /// the field, its type and its wire position are unchanged.
    pub mir_local: u32,
    /// Pairing term 1. `None` for an unnamed parameter, and for any subject
    /// whose `var_debug_info` entry count is not exactly one.
    pub param_name: Option<String>,
    /// Pairing term 2.
    ///
    /// # The basis is PINNED HERE: **1-BASED**
    ///
    /// This doc comment is normative for both producers; the design document is
    /// descriptive of it. Matching `VarDebugInfo::argument_index` and MIR's
    /// parameter locals means the **reference side stays transformation-free** —
    /// producer B emits `argument_index` verbatim, and producer A converts
    /// (`hir_index + 1`). The side that transforms is the one whose native basis
    /// differs, and that is the collector, not the reference.
    ///
    /// Two bases would not degrade gracefully: they would fail *every* row's
    /// pairing at first contact, a systematic off-by-one presenting as total
    /// disagreement.
    ///
    /// Producer A derives this from its recorded HIR position, **never from
    /// `mir_local`** — a pairing field that restates the alignment key can never
    /// disagree with it, which is what F1 was.
    ///
    /// **`None` means "not a parameter", never "unpaired"** (S3.1 pre-flight,
    /// 2026-08-05). A named pointer LOCAL has no argument position and carries
    /// `None` here legitimately. The only consumer, `compare::pairing_agrees`,
    /// compares this field by **equality** — `None == None` agrees — and no site
    /// anywhere presence-tests it. Stated at the field so the locals population
    /// is not later mistaken for a pairing failure.
    pub arg_index: Option<u32>,
    /// Pointer-chain depth of the resolved subject type.
    pub ptr_depth: u8,
    pub pairing_confidence: PairingConfidence,
    /// Producer A only. Rendered `file:line:col`, for **attribution**; not
    /// orderable, so it is never used to decide the span axis.
    pub decl_span: Option<String>,
    /// Producer A only — the declared type's extent, **numeric**.
    ///
    /// # Coordinate system, pinned
    ///
    /// **File-relative byte offsets**, obtained via
    /// `SourceMap::lookup_byte_offset(..).pos.0` — *not* raw `BytePos`, which is
    /// global across the source map and would be meaningless to compare between
    /// files. Both producers use the same call, and the plan splices with the
    /// same one, so the audited number **is** the edit target.
    pub decl_span_lo: Option<u32>,
    pub decl_span_hi: Option<u32>,
    /// Producer B only — the parameter BINDING's extent, same coordinate
    /// system. Sourced from `VarDebugInfo.source_info.span`.
    ///
    /// Its presence is also the **span-axis activation signal**: an artifact
    /// with zero `binding_span_lo` anywhere has an inactive axis (producer B
    /// does not emit the field yet); *any* present value makes the axis ACTIVE
    /// for that artifact, with absent bindings on High rows becoming real
    /// findings. There is deliberately no gray zone.
    pub binding_span_lo: Option<u32>,
    pub binding_span_hi: Option<u32>,
    /// Producer A only.
    pub decl_shape: Option<DeclShape>,
    /// Producer A only. Its presence is what distinguishes covered-but-unchanged
    /// from dropped.
    pub outcome: Option<Outcome>,
    /// Producer A only; `Some` exactly when `outcome` is `Degraded`.
    pub degrade_reason: Option<String>,
    /// **The freed-slot attribution.** Producer A only: `Some(true)` when this
    /// subject's binding is passed to a deallocator, `Some(false)` when it is
    /// not, `None` on a producer-B row.
    ///
    /// # A column, not a reason — and why both exist
    ///
    /// `degrade_reason` names the FIRST test that fired, because `decide_one`
    /// returns at it. The freed-slot gate fires last, so on today's corpus every
    /// freed subject is attributed to something else and the reason field alone
    /// reports the freed population as **empty**. That is the ordering blindness
    /// `facts_join_tsv` exists to defeat, one axis at a time; this is the same
    /// remedy for this fact.
    ///
    /// So the two are **co-attribution**, deliberately: a row may read
    /// `degrade_reason: "call-site-not-adapted"` and `freed: true` at once, and
    /// that pair is exactly the population S3 must not silently convert when it
    /// retires the first of them.
    ///
    /// `Option<bool>` rather than `bool`: producer B is MIR-derived and has no
    /// derivation for this, so a `false` from B would be a claim it cannot
    /// support — the silently-agreeing field that F1 was.
    pub freed: Option<bool>,
    /// **U-2′'s assumption-violation counter.** `Some(true)` when a slice
    /// subject's length was approximated rather than recovered at a construction
    /// site; `None` on any non-slice row, so the counter's denominator is the
    /// slice population.
    ///
    /// Producer A only. Under theorem option (ii) the exact-length assumption
    /// fails exactly on the flagged set, so this is a **measured number** the
    /// paper reports per program and corpus-wide, not a caveat.
    pub approx_len: Option<bool>,
}

impl Row {
    /// The alignment key. Rows from the two producers are matched on this.
    pub(crate) fn key(&self) -> (&str, u32) {
        (self.fn_path.as_str(), self.mir_local)
    }
}

/// Canonical order: `(fn_path, mir_local)`.
pub(crate) fn sort_rows(rows: &mut [Row]) {
    rows.sort_by(|a, b| a.key().cmp(&b.key()));
}

/// Encode rows as JSONL, canonically ordered.
#[allow(
    dead_code,
    reason = "no non-test consumer until the rewriter is wired into \
              the pipeline. EXPIRY-CORRECTED 2026-07-30: this reason used to \
              say 'consumers land at C.1/C.4'. Both landed and the allow is \
              still required, because both consumers are `cfg(test)` — a dated \
              promise that came due and did not settle. Targeted on the entry \
              point rather than module-wide: allowing an item makes it a live \
              root, so the lint stays active over everything reachable from it."
)]
pub(crate) fn encode(rows: &[Row]) -> String {
    let mut owned = rows.to_vec();
    sort_rows(&mut owned);
    let mut out = String::new();
    for row in &owned {
        out.push_str(&serde_json::to_string(row).expect("Row is always serializable"));
        out.push('\n');
    }
    out
}

/// Decode JSONL. Blank lines are skipped; a malformed line is an error naming
/// its line number, never a silently dropped row.
#[allow(
    dead_code,
    reason = "no non-test consumer until the rewriter is wired into \
              the pipeline. EXPIRY-CORRECTED 2026-07-30: this reason used to \
              say 'consumers land at C.1/C.4'. Both landed and the allow is \
              still required, because both consumers are `cfg(test)` — a dated \
              promise that came due and did not settle. Targeted on the entry \
              point rather than module-wide: allowing an item makes it a live \
              root, so the lint stays active over everything reachable from it."
)]
pub(crate) fn decode(text: &str) -> Result<Vec<Row>, String> {
    let mut rows = Vec::new();
    for (index, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let row =
            serde_json::from_str::<Row>(line).map_err(|e| format!("line {}: {e}", index + 1))?;
        rows.push(row);
    }
    Ok(rows)
}
