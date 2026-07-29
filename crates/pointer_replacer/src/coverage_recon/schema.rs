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
//! | `outcome`, `degrade_reason` | ✓ | `null` | S2b consumes; not compared |
//!
//! `decl_span` is deliberately **not** a reconciled field even though §1 first
//! grouped it under pairing. A's span is the declared *type*'s span (it is what
//! the plan splices); the nearest MIR-side equivalent is the local's
//! `source_info.span`, which denotes the *binding*. Comparing them would report
//! a guaranteed difference as a finding on every row. Amendment (a) settles the
//! question by naming the two pairing terms explicitly: `param_name` and
//! `arg_index`.

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
}

/// Whether the pairing for this row can be trusted.
///
/// `Low` is set when a parameter's `var_debug_info` entry count is not exactly
/// one — zero covers an unnamed `_`, and more than one covers a pattern
/// parameter such as `fn f((a, b): (*mut i32, *mut i32))`, whose entries name
/// the *bindings* rather than the parameter. A `Low` row's pairing disagreement
/// is an attributed finding rather than a fail-loud, because the instrument —
/// not necessarily the collector — is the thing in doubt.
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
    /// MIR local of the parameter. With `fn_path`, the alignment key.
    pub mir_local: u32,
    /// Pairing term 1. `None` for an unnamed parameter.
    pub param_name: Option<String>,
    /// Pairing term 2. **1-based**, matching `VarDebugInfo::argument_index` and
    /// MIR's parameter locals. Producer A records its own HIR position + 1 —
    /// derived independently of its `mir_local`, so the field is not a restatement
    /// of the alignment key.
    pub arg_index: Option<u32>,
    /// Pointer-chain depth of the resolved parameter type.
    pub ptr_depth: u8,
    pub pairing_confidence: PairingConfidence,
    /// Producer A only.
    pub decl_span: Option<String>,
    /// Producer A only.
    pub decl_shape: Option<DeclShape>,
    /// Producer A only. Its presence is what distinguishes covered-but-unchanged
    /// from dropped.
    pub outcome: Option<Outcome>,
    /// Producer A only; `Some` exactly when `outcome` is `Degraded`.
    pub degrade_reason: Option<String>,
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
    reason = "S2a-H lands its consumers in later slices: the fixture \
              reconciliation (C.1) and the corpus mode (C.4). Targeted on the \
              entry points rather than module-wide — allowing an item makes it \
              a live root, so the lint stays active over everything reachable \
              from it. A module-wide blanket is what hid two dead fields in the \
              round this design replaces."
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
    reason = "S2a-H lands its consumers in later slices: the fixture \
              reconciliation (C.1) and the corpus mode (C.4). Targeted on the \
              entry points rather than module-wide — allowing an item makes it \
              a live root, so the lint stays active over everything reachable \
              from it. A module-wide blanket is what hid two dead fields in the \
              round this design replaces."
)]
pub(crate) fn decode(text: &str) -> Result<Vec<Row>, String> {
    let mut rows = Vec::new();
    for (index, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let row = serde_json::from_str::<Row>(line)
            .map_err(|e| format!("line {}: {e}", index + 1))?;
        rows.push(row);
    }
    Ok(rows)
}
