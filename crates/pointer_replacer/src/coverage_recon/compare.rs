//! **The reconciliation.** Two artifacts in, a verdict out.
//!
//! Rows are aligned on `(fn_path, mir_local)` and compared **field by field**.
//! Never bare counts — count-only agreement is how the first two coverage gates
//! passed while both sides were blind.
//!
//! # Severity, direction-asymmetric (R-B)
//!
//! | condition | severity |
//! |---|---|
//! | row in B only | attributed `OutOfCoverage` finding; the run continues |
//! | row in A only | **fail-loud** |
//! | pairing fields disagree, `pairing_confidence = high` | **fail-loud** |
//! | pairing fields disagree, `pairing_confidence = low` | attributed finding |
//! | classification fields disagree (`ptr_depth`) | attributed finding |
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
];

/// A non-halting finding, attributed.
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
    /// A program passes when nothing fails loudly. Findings are loud but not
    /// fatal — that is R-B's asymmetry, not an oversight.
    #[allow(
        dead_code,
        reason = "the per-program corpus verdict (C.5) is this method's \
                  shipping consumer; it is exercised by the witnesses today."
    )]
    pub(crate) fn passed(&self) -> bool {
        self.violations.is_empty()
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

    verdict.violations.sort_by(|x, y| {
        (x.class, &x.fn_path, x.mir_local).cmp(&(y.class, &y.fn_path, y.mir_local))
    });
    verdict.findings.sort_by(|x, y| {
        (x.class, &x.fn_path, x.mir_local).cmp(&(y.class, &y.fn_path, y.mir_local))
    });
    verdict
}
