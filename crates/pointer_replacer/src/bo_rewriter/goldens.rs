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
    let mut checked_degraded = 0usize;
    let mut degradations_seen = 0usize;

    for golden in GOLDENS {
        match rewrite_m1(golden.input) {
            RewriteOutcome::Degraded {
                reason,
                degradations,
            } => {
                checked_degraded += 1;
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

    // Non-vacuity: the assertions above must actually have run on something.
    assert_eq!(
        checked_emitted + checked_degraded,
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
