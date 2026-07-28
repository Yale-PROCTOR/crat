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
//! # Why these are RED at S0
//!
//! [`super::rewrite_m1`] returns [`super::RewriteOutcome::Degraded`], so every
//! test below fails on the *outcome assertion* — a stated missing emitter —
//! rather than on a diff or a panic.

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
                RewriteOutcome::Emitted(src) => src,
                RewriteOutcome::Degraded { reason } => panic!(
                    "{}: no emission — degraded with reason {reason:?}. This is the \
                     expected S0 state; it turns GREEN when the emitter handles \
                     this shape.",
                    golden.name
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
