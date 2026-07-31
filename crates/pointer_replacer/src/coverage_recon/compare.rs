//! **The reconciliation.** Two artifacts in, a verdict out.
//!
//! Rows are aligned on `(fn_path, mir_local)` and compared **field by field**.
//! Never bare counts — count-only agreement is how the first two coverage gates
//! passed while both sides were blind.
//!
//! # Severity, direction-asymmetric (R-B)
//!
//! | condition | class | program outcome |
//! |---|---|---|
//! | row in B only | `out-of-coverage` finding | **FAIL** |
//! | row in A only | violation | **FAIL** |
//! | pairing disagrees, confidence `high` | violation | **FAIL** |
//! | pairing disagrees, confidence `low` | finding | **FAIL** |
//! | classification disagrees (`ptr_depth`) | finding | **FAIL** |
//!
//! # R-B's verdict-level asymmetry is DEFERRED, not deleted (ruling 2026-07-31)
//!
//! R-B graded a coverage gap as *loud but not fatal* and a contract violation
//! as fatal. At the **verdict** level that distinction is currently inert:
//! every finding class is pinned to expected-zero, so any finding fails its
//! program whatever `passed()` says — the inertness follows from the
//! expected-zero generalization, not from `passed()`, and reverting `passed()`
//! alone would not restore it.
//!
//! Option (A) is in force: accept the inertness and say so. Option (B) — a
//! declared nonzero budget for `pairing-mismatch-low-confidence`, which
//! reactivates the downgrade — is **registered with a trigger**: on frozen
//! rs-crown the legitimate incidence of low-confidence pairing is genuinely
//! **zero** (C2Rust emits no pattern or unnamed parameters), so the only honest
//! budget today is 0 — and a budget of 0 *is* option (A). A nonzero budget now
//! would be speculative configurability for a class with no incidence: dead
//! machinery of the `excluded_other` kind.
//!
//! **Decision rule:** when a corpus with legitimate low-confidence incidence
//! enters scope (un-tamed robustness runs, M4-era), set the budget from
//! MEASURED incidence and the verdict-level downgrade activates.
//!
//! What the class still buys today: triage. The record says which instrument
//! is in doubt, and the sweep still continues past it to full incidence.
//!
//! A parameter the collector cannot see is an unhandled subject, and halting
//! the crate for it reproduces the whole-crate-verdict problem S2b is separately
//! fixing. A subject on *neither* reference was not missed, it was invented. A
//! mis-pairing silently applies BO's decision to the wrong source parameter, so
//! it corrupts output rather than merely omitting it — which is why it is graded
//! with invention rather than with coverage.
//!
//! # Aggregates are not optional
//!
//! Every attributed-finding class carries a count in [`Verdict::aggregates`],
//! **including when it is zero**, so a corpus gate can pin it. Recorded
//! rationale: *attribution without aggregation is how downgrades go silent* —
//! R-B's "loud in the counters" only holds if something reads the counters, and
//! a class that vanishes from the map when empty cannot be pinned to zero.

use std::collections::BTreeMap;

use super::schema::{PairingConfidence, Row};

/// Finding classes. Every one appears in [`Verdict::aggregates`], always.
pub(crate) const FINDING_CLASSES: &[&str] = &[
    "out-of-coverage",
    "pairing-mismatch-low-confidence",
    "classification-mismatch",
    // Track 2. Its OWN class rather than folded into the pairing class: they
    // answer different questions — is the PAIRING trustworthy vs is the SPLICE
    // TARGET trustworthy — and folding them would make a nonzero aggregate
    // ambiguous about which axis degraded.
    "span-check-not-evaluable",
];

/// Is the span axis ACTIVE for this artifact pair?
///
/// The predicate is exactly **"zero `binding_span_lo` in the entire producer-B
/// artifact"** ⇒ inactive. *Any* present value ⇒ ACTIVE, and absent bindings on
/// High rows are then real findings. **No gray zone** — a per-row fallback would
/// let a partly-filled artifact look healthy while most of the axis was dark.
///
/// Inactive is a bounded, declared state: producer B's `binding_span` arrives
/// via the gated follow-on, `span_axis_is_active_on_producer_b` is RED until it
/// does, and S2a-H cannot close while either holds.
pub(crate) fn span_axis_active(b_rows: &[Row]) -> bool {
    b_rows.iter().any(|r| r.binding_span_lo.is_some())
}

/// An attributed finding.
///
/// **Not "non-halting" at the verdict level** — see the module docs. It does
/// not halt the *sweep* (the driver continues to the next program), but it does
/// fail its own program while every finding class is pinned to expected-zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Finding {
    pub class: &'static str,
    pub fn_path: String,
    pub mir_local: u32,
    pub detail: String,
}

/// A contract violation. Fail-loud at **program** granularity: in a fixture
/// this is an assertion failure; on the corpus the program's verdict is FAIL,
/// its output is untrusted, and **the sweep continues** so one run yields the
/// full incidence rather than halting at the first program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Violation {
    pub class: &'static str,
    pub fn_path: String,
    pub mir_local: u32,
    pub detail: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Verdict {
    pub violations: Vec<Violation>,
    pub findings: Vec<Finding>,
    /// Every class in [`FINDING_CLASSES`], present even at zero.
    pub aggregates: BTreeMap<&'static str, usize>,
}

impl Verdict {
    /// The expected-zero enforcement verdict passes only when there is nothing
    /// to report. The driver still continues to the next program after a
    /// finding so one run yields full incidence.
    #[allow(
        dead_code,
        reason = "the per-program corpus verdict (C.5) is this method's \
                  shipping consumer; it is exercised by the witnesses today."
    )]
    pub(crate) fn passed(&self) -> bool {
        self.violations.is_empty()
            && self.findings.is_empty()
            && FINDING_CLASSES
                .iter()
                .all(|class| self.aggregates.contains_key(class))
    }
}

/// Render both pairing terms for a mismatch message, so the report names what
/// each side actually said rather than only that they differed.
fn pairing_detail(a: &Row, b: &Row) -> String {
    format!(
        "A(name={:?}, arg_index={:?}) vs B(name={:?}, arg_index={:?})",
        a.param_name, a.arg_index, b.param_name, b.arg_index
    )
}

/// Do the two rows agree on **both** pairing terms?
///
/// Both terms are compared. A permutation of two parameters flips `param_name`
/// and `arg_index` together, so a comparator checking only one term would still
/// pass the permutation witness — the single-term unit cases in `witnesses.rs`
/// exist to kill that mutant, which the headline witness cannot.
fn pairing_agrees(a: &Row, b: &Row) -> bool {
    a.param_name == b.param_name && a.arg_index == b.arg_index
}

/// Reconcile producer A's rows against producer B's.
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
pub(crate) fn compare(a_rows: &[Row], b_rows: &[Row]) -> Verdict {
    let mut verdict = Verdict::default();
    for class in FINDING_CLASSES {
        verdict.aggregates.insert(class, 0);
    }

    let a_by_key: BTreeMap<(&str, u32), &Row> = a_rows.iter().map(|r| (r.key(), r)).collect();
    let b_by_key: BTreeMap<(&str, u32), &Row> = b_rows.iter().map(|r| (r.key(), r)).collect();

    // B-only: a parameter the collector never produced a subject for.
    for (key, b) in &b_by_key {
        if a_by_key.contains_key(key) {
            continue;
        }
        verdict.findings.push(Finding {
            class: "out-of-coverage",
            fn_path: b.fn_path.clone(),
            mir_local: b.mir_local,
            detail: format!("no producer-A row; B says name={:?}", b.param_name),
        });
        *verdict.aggregates.entry("out-of-coverage").or_default() += 1;
    }

    // A-only: a subject no reference knows about.
    for (key, a) in &a_by_key {
        if b_by_key.contains_key(key) {
            continue;
        }
        verdict.violations.push(Violation {
            class: "collector-surplus",
            fn_path: a.fn_path.clone(),
            mir_local: a.mir_local,
            detail: format!(
                "subject present in producer A and absent from producer B \
                 (name={:?}); a subject on neither reference was not missed, it \
                 was invented",
                a.param_name
            ),
        });
    }

    // Present in both: pairing first, then classification.
    for (key, a) in &a_by_key {
        let Some(b) = b_by_key.get(key) else {
            continue;
        };
        if !pairing_agrees(a, b) {
            let low = a.pairing_confidence == PairingConfidence::Low
                || b.pairing_confidence == PairingConfidence::Low;
            if low {
                verdict.findings.push(Finding {
                    class: "pairing-mismatch-low-confidence",
                    fn_path: a.fn_path.clone(),
                    mir_local: a.mir_local,
                    detail: pairing_detail(a, b),
                });
                *verdict
                    .aggregates
                    .entry("pairing-mismatch-low-confidence")
                    .or_default() += 1;
            } else {
                verdict.violations.push(Violation {
                    class: "pairing-mismatch",
                    fn_path: a.fn_path.clone(),
                    mir_local: a.mir_local,
                    detail: pairing_detail(a, b),
                });
            }
        }
        if a.ptr_depth != b.ptr_depth {
            verdict.findings.push(Finding {
                class: "classification-mismatch",
                fn_path: a.fn_path.clone(),
                mir_local: a.mir_local,
                detail: format!("ptr_depth A={} B={}", a.ptr_depth, b.ptr_depth),
            });
            *verdict
                .aggregates
                .entry("classification-mismatch")
                .or_default() += 1;
        }
    }

    // ---- span axis (Track 2) -------------------------------------------
    if span_axis_active(b_rows) {
        let mut by_fn: BTreeMap<&str, Vec<(&Row, &Row)>> = BTreeMap::new();
        for (key, a) in &a_by_key {
            if let Some(b) = b_by_key.get(key) {
                by_fn.entry(key.0).or_default().push((a, b));
            }
        }
        for (fn_path, mut pairs) in by_fn {
            pairs.sort_by_key(|(a, _)| a.mir_local);
            let mut prev_ty_hi: u32 = 0;
            for (index, (a, b)) in pairs.iter().enumerate() {
                let evaluable = a.decl_span_lo.zip(a.decl_span_hi).zip(
                    b.binding_span_lo.zip(b.binding_span_hi),
                );
                match evaluable {
                    Some(((ty_lo, ty_hi), (b_lo, b_hi)))
                        if a.pairing_confidence == PairingConfidence::High
                            && b.pairing_confidence == PairingConfidence::High =>
                    {
                        if b_hi > ty_lo || prev_ty_hi > b_lo {
                            // NAMES THE FAILING INDEX: the conjunction fires at
                            // >= 1 index under a permutation, not at every one,
                            // so reporting the function alone would imply every
                            // row is detached.
                            verdict.violations.push(Violation {
                                class: "span-interleave-breach",
                                fn_path: fn_path.to_owned(),
                                mir_local: a.mir_local,
                                detail: format!(
                                    "index {index}: binding=({b_lo},{b_hi}) ty=({ty_lo},{ty_hi}) \
                                     prev_ty_hi={prev_ty_hi} — the declared type is not \
                                     positioned within its own parameter's extent, so the \
                                     splice target is mis-associated"
                                ),
                            });
                        }
                        prev_ty_hi = ty_hi;
                    }
                    _ => {
                        verdict.findings.push(Finding {
                            class: "span-check-not-evaluable",
                            fn_path: fn_path.to_owned(),
                            mir_local: a.mir_local,
                            detail: format!(
                                "index {index}: span axis active but this row lacks a \
                                 usable extent pair (A={:?}..{:?}, B={:?}..{:?}, \
                                 confidence A={:?} B={:?})",
                                a.decl_span_lo, a.decl_span_hi,
                                b.binding_span_lo, b.binding_span_hi,
                                a.pairing_confidence, b.pairing_confidence
                            ),
                        });
                        *verdict
                            .aggregates
                            .entry("span-check-not-evaluable")
                            .or_default() += 1;
                        if let Some(hi) = a.decl_span_hi {
                            prev_ty_hi = hi;
                        }
                    }
                }
            }
        }
    }

    verdict.violations.sort_by(|x, y| {
        (x.class, &x.fn_path, x.mir_local).cmp(&(y.class, &y.fn_path, y.mir_local))
    });
    verdict.findings.sort_by(|x, y| {
        (x.class, &x.fn_path, x.mir_local).cmp(&(y.class, &y.fn_path, y.mir_local))
    });
    verdict
}
