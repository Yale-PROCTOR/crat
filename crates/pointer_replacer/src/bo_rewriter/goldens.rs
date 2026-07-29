//! M1 golden tests — the ten hand-written pairs, landed **verbatim**.
//!
//! Source: `docs/agents/plan/2026-07-28-m05-m1-goldens.md` and its
//! `testdata/m1-goldens/`. The `.rs` files here were copied byte-for-byte
//! (verified by SHA-256 at copy time); they are the spec, not a restatement of
//! it.
//!
//! # Formatting canonicalization (reviewer ruling, 2026-07-28)
//!
//! Comparison runs **after both sides pass through the same canonical
//! formatter** — `rustfmt`, identical invocation, applied to emitted and
//! expected alike.
//!
//! This is **not** editing expected text, and the distinction is the point:
//! whitespace normalization is applied symmetrically by a tool neither side
//! controls, whereas a *semantic* edit to a golden changes what the milestone
//! is required to produce. Semantic edits stay ruling-gated — if a golden turns
//! out to be unproducible by the pipeline, that is a **golden defect** to be
//! escalated, never a licence to rewrite the expectation.
//!
//! Without canonicalization S0's RED would conflate two different failures —
//! "no emitter yet" and "pretty-printer spaces differently" — and S1 would then
//! meet the second disguised as a contract mismatch.
//!
//! # What RED means here, and how it shifted
//!
//! At S0 every golden failed on the *outcome* assertion, because `rewrite_m1`
//! degraded unconditionally.
//!
//! From S1 that is no longer uniform, and the distinction is worth stating so a
//! red test is read correctly:
//!
//! - **g02/g06** degrade, now with **attributed** per-subject reasons (S2a).
//! - **g04/g05/g07/g08** have no pointer *parameters*, so S1–S2a produce no
//!   subjects for them and `rewrite_m1` returns the input unchanged. They fail
//!   on the **diff**, not on a missing-emitter message — their shapes (Box,
//!   drops, stores) arrive in S3. Their RED therefore signals "shape not yet
//!   implemented" only by virtue of the diff, which is weaker than the S0
//!   signal and is recorded rather than papered over.
//! - **g09** passes trivially — see its companion assertion below.

use std::{
    io::Write,
    process::{Command, Stdio},
};

use super::{RewriteOutcome, rewrite_m1};

/// One golden pair, embedded at compile time so the test binary is
/// self-contained.
struct Golden {
    name: &'static str,
    input: &'static str,
    expected: &'static str,
}

macro_rules! goldens {
    ($($name:literal),* $(,)?) => {
        &[$(Golden {
            name: $name,
            input: include_str!(concat!("testdata/m1-goldens/", $name, ".input.rs")),
            expected: include_str!(concat!("testdata/m1-goldens/", $name, ".expected.rs")),
        }),*]
    };
}

const GOLDENS: &[Golden] = goldens![
    "g01_ref_mut",
    "g02_opt_ref",
    "g03_ref_shared",
    "g04_box_drop",
    "g05_opt_box",
    "g06_move_reroute",
    "g07_nonDropping_store",
    "g08_drop_all_paths",
    "g09_pdrop_suppression",
    "g10_mixed_group",
];

/// Run `rustfmt` over a source string with pinned settings.
///
/// Pinned = the same edition and emit mode for both sides, with no config file
/// discovery that could differ between them. A formatter failure is surfaced,
/// never swallowed: silently returning the input on error would let a
/// malformed emission compare equal to a well-formed expectation.
fn canonicalize(label: &str, src: &str) -> String {
    let mut child = Command::new("rustfmt")
        .args(["--edition", "2021", "--emit", "stdout", "--quiet"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|e| panic!("rustfmt not runnable (needed to canonicalize {label}): {e}"));
    child
        .stdin
        .as_mut()
        .expect("rustfmt stdin")
        .write_all(src.as_bytes())
        .expect("write to rustfmt");
    let out = child.wait_with_output().expect("rustfmt output");
    assert!(
        out.status.success(),
        "rustfmt failed on {label}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8(out.stdout).expect("rustfmt emitted valid UTF-8")
}

/// The ten goldens. RED until the emitter exists.
///
/// Each is a separate `#[test]` rather than one loop, so a partially working
/// emitter reports *which* shapes pass — S1 turns exactly one of these green.
macro_rules! golden_test {
    ($fn_name:ident, $golden:literal) => {
        #[test]
        fn $fn_name() {
            let golden = GOLDENS
                .iter()
                .find(|g| g.name == $golden)
                .expect("golden is registered in GOLDENS");
            let emitted = match rewrite_m1(golden.input) {
                RewriteOutcome::Emitted { source, .. } => source,
                RewriteOutcome::Degraded {
                    reason,
                    degradations,
                    ..
                } => panic!(
                    "{}: no emission — {reason}. Attributed degradations: {:#?}",
                    golden.name, degradations
                ),
            };
            let emitted = canonicalize("emitted", &emitted);
            let expected = canonicalize("expected", golden.expected);
            assert_eq!(
                emitted, expected,
                "{}: emitted crate differs from the golden AFTER canonical \
                 formatting, so this is a semantic difference, not whitespace",
                golden.name
            );
        }
    };
}

golden_test!(g01_ref_mut, "g01_ref_mut");
golden_test!(g02_opt_ref, "g02_opt_ref");
golden_test!(g03_ref_shared, "g03_ref_shared");
golden_test!(g04_box_drop, "g04_box_drop");
golden_test!(g05_opt_box, "g05_opt_box");
golden_test!(g06_move_reroute, "g06_move_reroute");
golden_test!(g07_non_dropping_store, "g07_nonDropping_store");
golden_test!(g08_drop_all_paths, "g08_drop_all_paths");
golden_test!(g09_pdrop_suppression, "g09_pdrop_suppression");
golden_test!(g10_mixed_group, "g10_mixed_group");

/// The canonicalizer must be a real normalizer, not a pass-through.
///
/// Without this, a broken `canonicalize` (one that returned its input) would
/// leave every golden comparison whitespace-sensitive again, and the ruling
/// this module documents would be silently unimplemented.
#[test]
fn canonicalization_normalizes_whitespace() {
    let ugly = "pub  fn   f( x : i32 )->i32{x+1}\n";
    let tidy = "pub fn f(x: i32) -> i32 {\n    x + 1\n}\n";
    assert_eq!(canonicalize("ugly", ugly), canonicalize("tidy", tidy));
    assert_ne!(
        canonicalize("ugly", ugly),
        ugly,
        "canonicalize returned its input unchanged — it is a pass-through, so \
         golden comparison is still whitespace-sensitive"
    );
}

/// Every registered golden must have both halves present and non-empty.
///
/// Guards the copy step: a missing or truncated fixture would otherwise show up
/// as a confusing diff much later.
#[test]
fn every_golden_pair_is_present() {
    assert_eq!(GOLDENS.len(), 10, "the M0.5 package specifies ten pairs");
    for g in GOLDENS {
        assert!(!g.input.trim().is_empty(), "{}: empty .input.rs", g.name);
        assert!(
            !g.expected.trim().is_empty(),
            "{}: empty .expected.rs",
            g.name
        );
    }
}

/// **G09 companion assertion (approved remedy).**
///
/// `g09_pdrop_suppression`'s input and expected are byte-identical, so the text
/// comparison passes for any rewriter that emits its input — including a
/// completely broken one. The expected text is NOT edited; instead this asserts
/// the outcome is unchanged *for a stated reason* rather than by accident.
///
/// At S2a the reason available is that the fixture yields **no emitted
/// subject**: `emitted_count == 0`. When S3 lands P-drop, this tightens to
/// asserting the table recorded the suppression itself.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** make `rewrite_m1`
/// return a non-zero `emitted_count` for this fixture (e.g. by removing the
/// A1 raw-pointer-operation check so a subject is emitted) and this fails,
/// where the text comparison alone would not.
#[test]
fn g09_is_unchanged_for_a_stated_reason_not_by_accident() {
    let golden = GOLDENS
        .iter()
        .find(|g| g.name == "g09_pdrop_suppression")
        .expect("g09 is registered");
    assert_eq!(
        golden.input, golden.expected,
        "this companion exists BECAUSE the pair is byte-identical; if that \
         changed, the ordinary golden test is now doing real work and this \
         assertion should be revisited"
    );
    match rewrite_m1(golden.input) {
        RewriteOutcome::Emitted {
            source,
            emitted_count,
            ..
        } => {
            assert_eq!(source, golden.expected, "g09 emitted a changed crate");
            assert_eq!(
                emitted_count, 0,
                "g09 emitted {emitted_count} subject(s); its expected text is \
                 identical to its input, so any emission means the text \
                 comparison is passing for the wrong reason"
            );
        }
        RewriteOutcome::Degraded {
            reason,
            degradations,
            ..
        } => panic!("g09 degraded: {reason}; {degradations:#?}"),
    }
}

// ---------------------------------------------------------------------------
// S2a exit gate: attribution at DECISION time
// ---------------------------------------------------------------------------

/// Find the degradations `rewrite_m1` attributed for one golden's input.
fn degradations_for(name: &str) -> Vec<super::decision::Degradation> {
    let golden = GOLDENS
        .iter()
        .find(|g| g.name == name)
        .expect("golden is registered");
    match rewrite_m1(golden.input) {
        RewriteOutcome::Emitted { degradations, .. } => degradations,
        RewriteOutcome::Degraded { degradations, .. } => degradations,
    }
}

/// A1 facts for an inline source, **without running BO**.
///
/// §5.3: the A1 mechanism fixtures used to assert on `rewrite_m1`'s
/// degradations, so they passed only because the solver happened to return
/// `Ref` for the parameter in question — an unrelated precision change would
/// have turned a mechanism test into a false red. Asserting on the fact
/// collector directly tests the layer the test names.
#[derive(Debug, Default)]
struct FactSnapshot {
    /// `(fn path, raw-only operation)`.
    raw_only: Vec<(String, String)>,
    /// Functions referenced in-crate — called, address-taken, or cast.
    referenced: Vec<String>,
    /// Functions with a pointer parameter used in a comparison.
    compared: Vec<String>,
}

fn facts_for_source(src: &str) -> FactSnapshot {
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = super::collect_program(tcx);
        let facts = super::decision::emitability::collect(tcx, &program.functions);
        let mut snapshot = FactSnapshot {
            raw_only: facts
                .raw_only_uses
                .iter()
                .map(|((did, _), (op, _))| (tcx.def_path_str(did.to_def_id()), op.clone()))
                .collect(),
            referenced: facts
                .referenced
                .keys()
                .map(|did| tcx.def_path_str(did.to_def_id()))
                .collect(),
            compared: facts
                .ptr_comparisons
                .keys()
                .map(|(did, _)| tcx.def_path_str(did.to_def_id()))
                .collect(),
        };
        snapshot.raw_only.sort();
        snapshot.referenced.sort();
        snapshot.compared.sort();
        snapshot
    })
    .expect("fixture compiles")
}

/// **S2a exit gate (g02 class).** A parameter used in a raw-pointer-only
/// operation is degraded IN THE DECISION PHASE, with its own site and reason.
///
/// Before S2a this parameter was decided `Ref`, emitted, and killed by the
/// whole-crate type-check gate as the anonymous string "emitted crate failed
/// the type-check gate" — no site, no subject. That made the envelope counters
/// wrong by construction: the subject was recorded as a success.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the
/// `raw_only_uses` check from `decide_one` and this fails — the subject is
/// decided `Ref` again and no degradation is attributed.
#[test]
fn g02_class_is_attributed_at_decision_time() {
    use super::decision::DegradeReason;
    let records = degradations_for("g02_opt_ref");
    let hit = records
        .iter()
        .find(|d| matches!(d.reason, DegradeReason::RawPointerOperation { .. }))
        .unwrap_or_else(|| {
            panic!("no raw-pointer-operation degradation was attributed; got {records:#?}")
        });
    assert!(
        hit.subject.contains("g02_maybe"),
        "degradation names the wrong subject: {hit:?}"
    );
    assert!(
        !hit.site.is_empty() && hit.site.contains(':'),
        "degradation carries no usable site: {hit:?}"
    );
    let DegradeReason::RawPointerOperation { op } = &hit.reason else {
        unreachable!()
    };
    assert_eq!(op, "is_null", "the attributed operation should be the real one");
}

/// **S2a exit gate (g06 class).** A function with an in-crate caller is degraded
/// in the decision phase, naming the call site — not discovered later as a
/// crate-wide type error.
///
/// This reason is explicitly **temporary**: S3's call-site adaptation retires
/// `CallSiteNotAdapted`, and the typed variant is what makes that retirement
/// visible in the counters rather than silent.
///
/// *Mutation-tested, Rider 0 order.* **Deletion first:** remove the `callers`
/// check from `decide_one` and this fails.
#[test]
fn g06_class_is_attributed_at_decision_time() {
    use super::decision::DegradeReason;
    let records = degradations_for("g06_move_reroute");
    let hit = records
        .iter()
        .find(|d| d.reason == DegradeReason::CallSiteNotAdapted)
        .unwrap_or_else(|| {
            panic!("no call-site-not-adapted degradation was attributed; got {records:#?}")
        });
    assert!(
        !hit.site.is_empty() && hit.site.contains(':'),
        "degradation must name the CALL SITE: {hit:?}"
    );
}

/// **S2a-R / F2 — the headline witness, restructured so it always asserts.**
///
/// The previous form was `if let Degraded { .. } = …` inside a loop. Every
/// golden returns `Emitted` (a degraded subject produces no edit, so the source
/// is unchanged and type-checks), so the body never ran — `assert!(false)`
/// inside it passed. I reported that unexecuted check as this slice's central
/// evidence.
///
/// Now the match is **exhaustive over the outcome**, so every golden asserts on
/// whichever arm it takes:
/// - `Degraded` → the reason must be attributed, never the anonymous
///   whole-crate string;
/// - `Emitted` → every degradation carried alongside must itself be attributed.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing the `Emitted` arm's
/// body with `{}` fails, because the anonymous-string check then has nothing to
/// run on for any golden.
#[test]
fn every_golden_outcome_is_attributed() {
    let mut checked_emitted = 0usize;
    let mut degraded: std::collections::BTreeSet<&str> = std::collections::BTreeSet::new();
    let mut degradations_seen = 0usize;

    for golden in GOLDENS {
        match rewrite_m1(golden.input) {
            RewriteOutcome::Degraded {
                reason,
                degradations,
                ..
            } => {
                degraded.insert(golden.name);
                assert!(
                    !reason.contains("failed the type-check gate"),
                    "{}: died at the anonymous whole-crate gate ({reason}) — the \
                     cause must be attributed at decision time",
                    golden.name
                );
                assert!(
                    !degradations.is_empty(),
                    "{}: degraded with no per-subject attribution",
                    golden.name
                );
            }
            RewriteOutcome::Emitted { degradations, .. } => {
                checked_emitted += 1;
                for d in &degradations {
                    degradations_seen += 1;
                    assert!(
                        !d.subject.is_empty(),
                        "{}: degradation with no subject: {d:?}",
                        golden.name
                    );
                    assert!(
                        d.site.contains(':'),
                        "{}: degradation with no site: {d:?}",
                        golden.name
                    );
                }
            }
        }
    }

    // ADV-R4: the previous "non-vacuity" assert here summed two counters that
    // are each incremented exactly once per iteration and compared the total to
    // the loop bound — unfailable, and labelled non-vacuity inside a commit
    // whose purpose was deleting checks that cannot fail.
    //
    // §5.2: its replacement was `assert_eq!(checked_degraded, 0)`, which pins
    // the Degraded arm as permanently dead-while-green and inverts into an
    // obstacle the moment a golden correctly degrades — the maintainer's
    // response would be to bump the constant, which is the change-detector loop.
    //
    // The EXPECTED SET instead: a golden that starts degrading fails with
    // *which* golden, and the fix is to add it here with a reason — an
    // intentional edit that records a decision, not a number bumped to restore
    // green.
    //
    // Stated plainly so it is not over-read: with the set EMPTY and no golden
    // degrading today, this assertion is no more load-bearing right now than
    // the zero-pin it replaces. The change buys a better failure mode later,
    // not more coverage now. What is load-bearing today is the Emitted arm
    // below and the non-vacuity assertion after it — the former verified by
    // emptying its loop, which fails this test.
    const EXPECTED_DEGRADED: &[&str] = &[];
    assert_eq!(
        degraded.iter().copied().collect::<Vec<_>>(),
        EXPECTED_DEGRADED,
        "the set of goldens taking the Degraded arm changed. That is not itself \
         wrong — but this test's coverage has MOVED, so re-check that the \
         Degraded arm's assertions are the ones you want load-bearing, then add \
         the golden to EXPECTED_DEGRADED with a reason."
    );
    assert_eq!(
        checked_emitted,
        GOLDENS.len(),
        "not every golden was classified"
    );
    assert!(
        degradations_seen > 0,
        "no golden carried a single degradation, so the Emitted arm asserted \
         nothing — this witness would be vacuous exactly as its predecessor was"
    );
}

/// **S2a-R / F4 — per-subject attribution is WITNESSED, not asserted.**
///
/// g10 is the discriminating fixture: three pointer parameters with a mixed
/// outcome — `solo` emits, `a` and `b` degrade. Two properties no previous test
/// checked:
///
/// 1. **Per-subject, not per-function.** Two degradations from ONE function,
///    naming different parameters. A per-function attribution cannot produce
///    this.
/// 2. **The site is the USE site, not the declaration.** Mutating both site
///    expressions in `decide_one` to the already-in-scope `decl_site` passed the
///    entire suite before this test existed.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing
/// `EmitabilityFacts::site(tcx, *span)` with `decl_site` in `decide_one` fails
/// assertion 2 here.
#[test]
fn g10_witnesses_per_subject_site_attribution() {
    let golden = GOLDENS
        .iter()
        .find(|g| g.name == "g10_mixed_group")
        .expect("g10 is registered");
    let RewriteOutcome::Emitted {
        degradations,
        emitted_count,
        ..
    } = rewrite_m1(golden.input)
    else {
        panic!("g10 must emit");
    };

    assert_eq!(emitted_count, 1, "g10 emits exactly `solo`");
    assert!(
        degradations.len() >= 2,
        "g10 has three pointer params and emits one, so at least two must be \
         degraded; got {degradations:#?}"
    );

    // (1) distinct subjects from ONE function.
    let subjects: std::collections::BTreeSet<&str> =
        degradations.iter().map(|d| d.subject.as_str()).collect();
    assert!(
        subjects.len() >= 2,
        "all degradations name the same subject {subjects:?} — attribution is \
         per-FUNCTION, not per-subject"
    );

    // NOTE on scope, learned from the data rather than assumed: g10's
    // degradations are `KindRaw`, and for that reason the DECLARATION is the
    // correct site — BO decided the slot is raw, which is a property of the
    // parameter, not of any use. Site-vs-declaration discrimination therefore
    // belongs to a reason whose cause is elsewhere; see
    // `g02_site_is_the_use_not_the_declaration`.
}

/// Parse the line number out of a rendered site (`<main.rs>:7:28: 7:36`).
fn site_line(site: &str) -> Option<usize> {
    let after_file = site.rsplit_once(">:")?.1;
    after_file.split(':').next()?.parse().ok()
}

/// **S2a-R / F4 — the site is the USE site, not the declaration.**
///
/// g02's parameter is declared on one line and used (`p.is_null()`) on
/// another, so the two spans are distinguishable by line number. Mutating both
/// site expressions in `decide_one` to the already-in-scope `decl_site` passed
/// the entire suite before this existed — "per-subject attribution (site +
/// subject + reason)" had its site dimension unwitnessed.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing
/// `EmitabilityFacts::site(tcx, *span)` with `decl_site` in the
/// raw-pointer-operation arm fails this.
#[test]
fn g02_site_is_the_use_not_the_declaration() {
    use super::decision::DegradeReason;
    let golden = GOLDENS
        .iter()
        .find(|g| g.name == "g02_opt_ref")
        .expect("g02 is registered");
    let records = degradations_for("g02_opt_ref");
    let hit = records
        .iter()
        .find(|d| matches!(d.reason, DegradeReason::RawPointerOperation { .. }))
        .expect("g02 degrades on a raw-pointer operation");

    let decl_line = golden
        .input
        .lines()
        .position(|l| l.contains("fn g02_maybe"))
        .expect("g02 declares its function")
        + 1;
    let use_line = golden
        .input
        .lines()
        .position(|l| l.contains("is_null"))
        .expect("g02 uses is_null")
        + 1;
    assert_ne!(
        decl_line, use_line,
        "fixture no longer distinguishes the two spans, so this witness is inert"
    );

    let site_line = site_line(&hit.site)
        .unwrap_or_else(|| panic!("site did not parse as <file>:line:col: {hit:?}"));
    assert_eq!(
        site_line, use_line,
        "site is line {site_line} but the raw-pointer use is on line {use_line} \
         (declaration is line {decl_line}) — the site is not the use site"
    );
}

// ---------------------------------------------------------------------------
// S2a-R2: fixtures for A1 arms that had none, and for the universe gate
// ---------------------------------------------------------------------------

/// Degradation reasons `rewrite_m1` attributes for an inline source.
fn reasons_for_source(src: &str) -> Vec<super::decision::Degradation> {
    match rewrite_m1(src) {
        RewriteOutcome::Emitted { degradations, .. } => degradations,
        RewriteOutcome::Degraded { degradations, .. } => degradations,
    }
}

const PREAMBLE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]\n";

/// **F5 fixture — the bounds-check shape, which had NO fixture.**
///
/// Modelled on the corpus sites (`binn::AdvanceDataPos`,
/// `lodepng::lodepng_chunk_next`): two pointer parameters compared with `>`.
/// This is the case F5 exists for and the dangerous half of it — on raw
/// pointers the comparison is on ADDRESSES, on references it is on POINTEES,
/// so a rewrite that type-checks would silently invert the bound.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `ExprKind::Binary`
/// arm in `emitability::collect` fails the mechanism half; deleting the
/// `ptr_comparisons` arm in `decide_one` fails the attribution half.
///
/// §5.3: the mechanism half asserts on `EmitabilityFacts::collect` directly.
/// The attribution half still goes through `rewrite_m1` — that composition IS
/// the property it names — but it can no longer be the only evidence, so a
/// solver change that stops returning `Ref` here degrades one assertion instead
/// of erasing the fixture's whole meaning.
#[test]
fn ptr_comparison_shape_is_degraded_with_its_own_reason() {
    use super::decision::DegradeReason;
    let src = format!(
        "{PREAMBLE}pub unsafe fn advance(p: *mut u8, plimit: *mut u8) -> i32 {{\n    \
         if p > plimit {{ return 0; }}\n    1\n}}\n"
    );

    // (1) mechanism, solver-independent.
    let facts = facts_for_source(&src);
    assert!(
        facts.compared.iter().any(|f| f.contains("advance")),
        "the comparison fact was not collected at all; got {facts:#?}"
    );

    // (2) attribution, end to end.
    let records = reasons_for_source(&src);
    let hit = records
        .iter()
        .find(|d| d.reason == DegradeReason::PtrComparison)
        .unwrap_or_else(|| panic!("no PtrComparison degradation attributed; got {records:#?}"));
    assert!(
        hit.subject.contains("advance"),
        "degradation names the wrong subject: {hit:?}"
    );
    assert!(hit.site.contains(':'), "no site: {hit:?}");
}

/// **F1 fixture — the fn-table / address-taken shape, which had NO fixture.**
///
/// This is F1's own motivating case: the function is never *called*, so the
/// pre-repair `ExprKind::Call`-only detector missed it entirely, rewrote the
/// signature, and left the fn-item cast referring to the old type — dying at
/// the anonymous whole-crate gate. Reverting F1 left the suite green precisely
/// because this shape was untested.
///
/// *Mutation-tested (Rider 0, deletion first):* narrowing the `ExprKind::Path`
/// arm back to `ExprKind::Call` fails this.
///
/// §5.1/§5.3, two repairs folded in. The second assertion used to be
/// `if let RewriteOutcome::Degraded { .. }` with no `else`, in a fixture that
/// returns `Emitted` — so it never ran; it is now an exhaustive `match` where
/// **both** arms assert. The first assertion is sound and does discriminate the
/// F1 repair (the old `Call`-only detector would not have caught
/// `Some(descent as unsafe fn(..))`), so only the dead half changed — and it is
/// now taken at the fact layer, independent of the solver.
#[test]
fn address_taken_function_is_degraded_not_silently_rewritten() {
    use super::decision::DegradeReason;
    let src = format!(
        "{PREAMBLE}pub unsafe fn descent(node: *mut i32) -> i32 {{ *node }}\n\
         pub unsafe fn table() -> Option<unsafe fn(*mut i32) -> i32> {{\n    \
         Some(descent as unsafe fn(*mut i32) -> i32)\n}}\n"
    );

    // (1) F1's mechanism: the fn-item cast counts as a reference.
    let facts = facts_for_source(&src);
    assert!(
        facts.referenced.iter().any(|f| f.contains("descent")),
        "the address-taken reference was not collected; the detector is back to \
         `ExprKind::Call` only. Facts: {facts:#?}"
    );

    // (2) and it is attributed, per subject.
    let records = reasons_for_source(&src);
    assert!(
        records
            .iter()
            .any(|d| d.reason == DegradeReason::CallSiteNotAdapted
                && d.subject.contains("descent")),
        "an address-taken function's parameter was not degraded; got {records:#?}"
    );

    // (3) and the crate did not die anonymously. Exhaustive: the Emitted arm is
    // the one this fixture actually takes, and it asserted nothing before.
    match rewrite_m1(&src) {
        RewriteOutcome::Degraded { reason, .. } => panic!(
            "address-taken shape must not reach a whole-crate verdict at all; \
             degraded with: {reason}"
        ),
        RewriteOutcome::Emitted {
            source,
            emitted_count,
            ..
        } => {
            assert_eq!(
                emitted_count, 0,
                "`descent` is address-taken, so nothing in this fixture is \
                 emittable; emitting {emitted_count} means the degradation was \
                 recorded but not honoured"
            );
            assert_eq!(
                source, src,
                "no subject was emitted, so the source must come through byte \
                 for byte"
            );
        }
    }
}

/// **RAW_ONLY_METHODS mechanism fixture.**
///
/// Proportionality call, recorded rather than assumed: the list is **data, not
/// arms**. One `contains` check consumes every entry, so a per-entry fixture
/// would test `slice::contains` sixteen times and add bloat without adding
/// coverage. This proves the mechanism over a few representative entries
/// (`offset`, `wrapping_add`); a new entry is a data edit, and the risk it
/// carries is a wrong *name*, which no fixture of this shape would catch either.
///
/// *Mutation-tested (Rider 0, deletion first):* emptying `RAW_ONLY_METHODS`
/// fails this.
///
/// §5.3: asserted at the fact layer, which is the layer the test names. Going
/// through `rewrite_m1` made this pass only because BO returned `Ref` for `p`,
/// so a solver precision change could have turned a `RAW_ONLY_METHODS`
/// mechanism test into a false red.
#[test]
fn raw_only_method_mechanism_covers_representative_entries() {
    for method in ["offset", "wrapping_add"] {
        let src = format!(
            "{PREAMBLE}pub unsafe fn f(p: *mut u8) -> *mut u8 {{ p.{method}(1) }}\n"
        );
        let facts = facts_for_source(&src);
        assert!(
            facts
                .raw_only
                .iter()
                .any(|(f, op)| f.contains("f") && op == method),
            "`{method}` was not collected as a raw-only use; got {facts:#?}"
        );
    }
}

/// **ADV-R1 fixture — the impl-method case the old gate could not see.**
///
/// An inherent method with a pointer parameter is out of M1's subject universe
/// **by ruling** (not a C-source shape). The point of this test is that the
/// exclusion is a COUNTED, attributed quantity: the old "independent" count
/// re-walked `program.functions`, so it skipped this item exactly as the
/// collector did, agreed at zero, and the parameter vanished silently.
///
/// *Mutation-tested (Rider 0, deletion first):* removing the `ImplItem` arm
/// from `universe::classify` fails this — the exclusion goes back to zero and
/// becomes invisible.
#[test]
fn impl_method_pointer_params_are_counted_as_excluded_not_invisible() {
    let src = format!(
        "{PREAMBLE}pub struct S;\nimpl S {{\n    pub unsafe fn m(&self, p: *mut i32) -> i32 {{ *p }}\n}}\n\
         pub unsafe fn free_fn(q: *mut i32) -> i32 {{ *q }}\n"
    );
    let report = ::utils::compilation::run_compiler_on_str(&src, |tcx| {
        super::decision::universe::classify(tcx)
    })
    .expect("fixture compiles");

    // TWO, not one — and the second is `&self`.
    //
    // `ptr_chain_depth` (the predicate R-A made shared between the collector,
    // E-R1 and this walk) counts `TyKind::Ref` as depth-bearing, so a `&self`
    // receiver is a depth-1 parameter by its definition. That is a real
    // consequence of adopting one predicate everywhere rather than a defect:
    // sharing it is what makes the type-axis mapping check meaningful, so
    // "pointer parameter" in M1's vocabulary means `ptr_chain_depth > 0` and
    // the counts are read that way. Asserted at its true value with the reason
    // named, rather than weakened to `>= 1`.
    assert_eq!(
        report.excluded.impl_items, 2,
        "the impl method's parameters (`&self` and `p: *mut i32`) must be \
         COUNTED as excluded, not skipped silently; report was {report:?}"
    );
    assert_eq!(
        report.subjects, 1,
        "the free function is the only M1 subject; report was {report:?}"
    );
}

/// **The exclusion counts reach a CONSUMER** (§4).
///
/// The buckets used to be written and read by nothing outside one test, while
/// the ledger claimed they "flow into S2b's counters, visible as a number
/// rather than as an absence". They now ride out on `RewriteOutcome`, which is
/// what makes that claim true of a code path.
///
/// *Mutation-tested (Rider 0, deletion first):* delete `excluded` from the
/// `Emitted` variant's construction site (returning `Excluded::default()`
/// instead) and this fails.
#[test]
fn exclusion_counts_reach_the_outcome() {
    let src = format!(
        "{PREAMBLE}unsafe extern \"C\" {{\n    pub fn ext(p: *mut i32) -> i32;\n}}\n\
         pub unsafe fn free_fn(q: *mut i32) -> i32 {{ *q }}\n"
    );
    match rewrite_m1(&src) {
        RewriteOutcome::Emitted { excluded, .. } => assert_eq!(
            excluded.foreign_items, 1,
            "the extern declaration's pointer parameter must reach the outcome"
        ),
        RewriteOutcome::Degraded {
            reason, excluded, ..
        } => panic!("fixture degraded ({reason}); excluded was {excluded:?}"),
    }
}

/// **R-A witness — the C2Rust alias class is COLLECTED and ATTRIBUTED.**
///
/// `pub type lil_value_t = *mut _lil_value_t` lowers to `TyKind::Path`, so the
/// retired syntactic collector produced no subject for a parameter declared
/// `val: lil_value_t`: BO decided it, and the rewriter discarded that decision
/// with no `Decision`, no `Degradation`, no site and no reason. That is exactly
/// the "unrewritten and unattributed" class the A1 layer exists to retire, and
/// it is present in the evaluation corpus.
///
/// R-A rules these **collected, not excluded**. They are real C pointer
/// parameters; what they get is a decision and an attributed reason, because
/// emitting *through* an alias is a separate design question — the alias
/// already contains the `*mut`, so `&mut lil_value_t` would be wrong.
///
/// *Mutation-tested (Rider 0, deletion first):* revert `collect_subjects` to
/// the syntactic `let rustc_hir::TyKind::Ptr(..) = input.kind else { continue }`
/// predicate and this fails — no subject is produced, so no degradation is
/// attributed and the parameter is invisible again.
#[test]
fn alias_typed_pointer_params_are_collected_and_attributed() {
    use super::decision::DegradeReason;
    let src = format!(
        "{PREAMBLE}pub struct _lil_value_t {{ pub n: i32 }}\n\
         pub type lil_value_t = *mut _lil_value_t;\n\
         pub unsafe fn take(val: lil_value_t) -> i32 {{ (*val).n }}\n"
    );
    let records = reasons_for_source(&src);
    let hit = records
        .iter()
        .find(|d| d.reason == DegradeReason::NonPointerDecl { shape: "alias" })
        .unwrap_or_else(|| {
            panic!(
                "the alias-typed parameter produced no attributed degradation — \
                 it is invisible to the rewriter again; got {records:#?}"
            )
        });
    assert!(
        hit.subject.contains("take::val"),
        "degradation names the wrong subject: {hit:?}"
    );
    assert!(hit.site.contains(':'), "no site: {hit:?}");
}

/// **The other half of the shared-predicate consequence: reference params.**
///
/// `ptr_chain_depth` counts `TyKind::Ref` as depth-bearing, so adopting it as
/// the shared predicate (R-A) brings already-reference parameters into the
/// subject universe too. That is deliberate — the collector and E-R1 must apply
/// the SAME predicate or the type-axis comparison reports noise instead of
/// mapping failures — and it is why [`DeclShape`] distinguishes `Reference`
/// from `Alias`: they are one collection rule and two different reasons.
///
/// *Mutation-tested (Rider 0, deletion first):* delete the `TyKind::Ref` arm of
/// the `decl_shape` match in `collect_subjects` (so it falls through to
/// `Other`) and this fails on the shape string.
#[test]
fn reference_typed_params_are_collected_with_their_own_shape() {
    use super::decision::DegradeReason;
    let src = format!("{PREAMBLE}pub fn borrowed(v: &mut i32) -> i32 {{ *v }}\n");
    let records = reasons_for_source(&src);
    let hit = records
        .iter()
        .find(|d| d.reason == DegradeReason::NonPointerDecl { shape: "reference" })
        .unwrap_or_else(|| {
            panic!("the reference-typed parameter was not attributed; got {records:#?}")
        });
    assert!(
        hit.subject.contains("borrowed::v"),
        "degradation names the wrong subject: {hit:?}"
    );
}
