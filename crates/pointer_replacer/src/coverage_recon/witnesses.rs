//! Witnesses for the artifact contract and the reconciliation.
//!
//! Every test here is mutation-tested, deletion first (Rider 0), and every one
//! is enumerated in the slice report with its result (Rider 4).

use super::{
    compare::{FINDING_CLASSES, Finding, compare},
    schema::{DeclShape, Outcome, PairingConfidence, Row, decode, encode},
};

fn full_row() -> Row {
    Row {
        fn_path: "m::f".to_owned(),
        mir_local: 1,
        param_name: Some("p".to_owned()),
        arg_index: Some(1),
        ptr_depth: 1,
        pairing_confidence: PairingConfidence::High,
        decl_span: Some("<main.rs>:3:14: 3:22".to_owned()),
        decl_span_lo: Some(50),
        decl_span_hi: Some(58),
        binding_span_lo: None,
        binding_span_hi: None,
        decl_shape: Some(DeclShape::RawPtr),
        outcome: Some(Outcome::Degraded),
        degrade_reason: Some("kind-raw".to_owned()),
    }
}

/// A producer-B row: every producer-A-only field absent.
fn bare_row(fn_path: &str, local: u32, name: Option<&str>, arg: Option<u32>, depth: u8) -> Row {
    Row {
        fn_path: fn_path.to_owned(),
        mir_local: local,
        param_name: name.map(str::to_owned),
        arg_index: arg,
        ptr_depth: depth,
        pairing_confidence: PairingConfidence::High,
        decl_span: None,
        decl_span_lo: None,
        decl_span_hi: None,
        binding_span_lo: None,
        binding_span_hi: None,
        decl_shape: None,
        outcome: None,
        degrade_reason: None,
    }
}

/// A pair of rows carrying the span axis: A supplies the ty extent, B the
/// binding extent.
fn span_pair(
    local: u32, name: &str, bind: (u32, u32), ty: (u32, u32),
) -> (Row, Row) {
    let mut a = bare_row("f", local, Some(name), Some(local), 1);
    a.decl_span_lo = Some(ty.0);
    a.decl_span_hi = Some(ty.1);
    let mut b = bare_row("f", local, Some(name), Some(local), 1);
    b.binding_span_lo = Some(bind.0);
    b.binding_span_hi = Some(bind.1);
    (a, b)
}

// ---------------------------------------------------------------------------
// A.3 — byte-exact encoding
// ---------------------------------------------------------------------------

/// **The encoding is pinned to exact bytes**, not to a round-trip.
///
/// A round-trip is symmetric under a shared encoding bug: if `encode` and
/// `decode` both omitted a field, a round-trip test would still pass. Byte
/// equality is not symmetric that way.
///
/// The second assertion is the one that enforces the ruling's *explicit null,
/// never omission* pin structurally, so it survives a deliberate golden update:
/// every field name appears even when every optional is absent.
///
/// *Mutation-tested (Rider 0, deletion first):* adding
/// `#[serde(skip_serializing_if = "Option::is_none")]` to any optional field in
/// `schema.rs` fails this — which is why no such attribute exists there.
///
/// **Golden updated 2026-07-31, deliberately.** Track 2 added four numeric span
/// fields, so the wire form changed. This is a §5.2-discipline edit with a
/// stated reason — a schema extension whose new bytes are *specified* — not a
/// RED-weakening: the structural half below still enumerates **every** field
/// name, including the four new ones, so the explicit-null pin cannot be
/// satisfied by omission.
#[test]
fn encoding_is_byte_exact_and_never_omits_a_field() {
    let full = encode(&[full_row()]);
    assert_eq!(
        full,
        r#"{"fn_path":"m::f","mir_local":1,"param_name":"p","arg_index":1,"ptr_depth":1,"pairing_confidence":"high","decl_span":"<main.rs>:3:14: 3:22","decl_span_lo":50,"decl_span_hi":58,"binding_span_lo":null,"binding_span_hi":null,"decl_shape":"raw-ptr","outcome":"degraded","degrade_reason":"kind-raw"}
"#,
        "fully-populated row encoding drifted"
    );

    let bare = encode(&[bare_row("g", 2, None, None, 0)]);
    assert_eq!(
        bare,
        r#"{"fn_path":"g","mir_local":2,"param_name":null,"arg_index":null,"ptr_depth":0,"pairing_confidence":"high","decl_span":null,"decl_span_lo":null,"decl_span_hi":null,"binding_span_lo":null,"binding_span_hi":null,"decl_shape":null,"outcome":null,"degrade_reason":null}
"#,
        "all-optionals-absent row encoding drifted"
    );

    // Structural, and independent of the exact bytes above: every declared
    // field name is present on a row whose optionals are ALL absent.
    for field in [
        "fn_path",
        "mir_local",
        "param_name",
        "arg_index",
        "ptr_depth",
        "pairing_confidence",
        "decl_span",
        "decl_span_lo",
        "decl_span_hi",
        "binding_span_lo",
        "binding_span_hi",
        "decl_shape",
        "outcome",
        "degrade_reason",
    ] {
        assert!(
            bare.contains(&format!("\"{field}\":")),
            "field `{field}` was OMITTED rather than emitted as null: {bare}"
        );
    }
}

/// Decoding rejects a malformed line by number instead of dropping it.
///
/// *Mutation-tested (Rider 0, deletion first):* replacing the `map_err` line
/// with `.ok()` + `continue` (silently skipping bad lines) fails this.
#[test]
fn a_malformed_line_is_an_error_not_a_silent_drop() {
    let text = format!("{}{{not json}}\n", encode(&[full_row()]));
    let err = decode(&text).expect_err("a malformed line must not decode");
    assert!(err.starts_with("line 2:"), "error must name the line: {err}");
}

// ---------------------------------------------------------------------------
// A.4 — canonical order
// ---------------------------------------------------------------------------

/// Rows are emitted sorted by `(fn_path, mir_local)`.
///
/// D19's lesson: a report whose row order permutes between runs is not
/// comparable. The input here is deliberately in the wrong order on both keys.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `sort_rows` call
/// in `encode` fails this.
#[test]
fn rows_are_emitted_in_canonical_order() {
    let rows = vec![
        bare_row("zeta", 2, Some("b"), Some(2), 1),
        bare_row("alpha", 3, Some("c"), Some(3), 1),
        bare_row("alpha", 1, Some("a"), Some(1), 1),
    ];
    let order: Vec<String> = encode(&rows)
        .lines()
        .map(|l| {
            let row: Row = serde_json::from_str(l).expect("line decodes");
            format!("{}:{}", row.fn_path, row.mir_local)
        })
        .collect();
    assert_eq!(order, vec!["alpha:1", "alpha:3", "zeta:2"]);
}

// ---------------------------------------------------------------------------
// A.6 — the five severity classes
// ---------------------------------------------------------------------------

/// **Class 1 — a B-only row is an attributed `out-of-coverage` finding.**
///
/// The NAME is kept because it is still accurate: this is about CLASSIFICATION,
/// which is unchanged. What was corrected (ruling 2026-07-31) is the claim that
/// "the run continues" describes the verdict — it describes the SWEEP. The
/// program itself fails, because every finding class is pinned to
/// expected-zero.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `for (key, b) in
/// &b_by_key` loop fails this.
#[test]
fn a_row_only_producer_b_has_is_an_attributed_finding() {
    let a = vec![bare_row("f", 1, Some("p"), Some(1), 1)];
    let b = vec![
        bare_row("f", 1, Some("p"), Some(1), 1),
        bare_row("f", 2, Some("q"), Some(2), 1),
    ];
    let v = compare(&a, &b);
    assert!(
        !v.passed(),
        "the expected-zero corpus verdict must reject every finding: {v:#?}"
    );
    assert_eq!(v.findings.len(), 1, "{v:#?}");
    assert_eq!(v.findings[0].class, "out-of-coverage");
    assert_eq!(v.findings[0].mir_local, 2, "the finding must name the subject");
    assert_eq!(v.aggregates["out-of-coverage"], 1);
}

/// **Class 2 — A-only row is a fail-loud contract violation.**
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `for (key, a) in
/// &a_by_key` surplus loop fails this.
#[test]
fn a_row_only_producer_a_has_is_a_violation() {
    let a = vec![
        bare_row("f", 1, Some("p"), Some(1), 1),
        bare_row("f", 9, Some("ghost"), Some(9), 1),
    ];
    let b = vec![bare_row("f", 1, Some("p"), Some(1), 1)];
    let v = compare(&a, &b);
    assert!(!v.passed(), "an invented subject must fail loudly");
    assert_eq!(v.violations.len(), 1, "{v:#?}");
    assert_eq!(v.violations[0].class, "collector-surplus");
    assert_eq!(v.violations[0].mir_local, 9);
}

/// **Class 3 — a high-confidence pairing mismatch is fail-loud, and the message
/// carries BOTH sides' name and index.**
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `if
/// !pairing_agrees(a, b)` block fails this.
#[test]
fn a_high_confidence_pairing_mismatch_is_a_violation() {
    let a = vec![bare_row("f", 1, Some("r"), Some(2), 1)];
    let b = vec![bare_row("f", 1, Some("q"), Some(1), 1)];
    let v = compare(&a, &b);
    assert!(!v.passed(), "a mis-pairing must fail loudly");
    assert_eq!(v.violations[0].class, "pairing-mismatch");
    let d = &v.violations[0].detail;
    for expected in [r#"name=Some("r")"#, r#"name=Some("q")"#, "arg_index=Some(2)", "arg_index=Some(1)"] {
        assert!(d.contains(expected), "detail must carry both sides: {d}");
    }
}

/// **Class 4 — the low-confidence downgrade, which is a CLASS change, not an
/// outcome change.**
///
/// A `pairing_confidence = low` row with a pairing disagreement is recorded as
/// a finding rather than a violation, and increments the low-confidence
/// aggregate — the instrument, not necessarily the collector, is what is in
/// doubt when `var_debug_info` gave no usable entry.
///
/// **It does not currently change the program outcome** (ruling 2026-07-31,
/// option A). The name is kept because the downgrade is real at the
/// classification level; the verdict-level effect is registered as option (B)
/// with a measured-incidence trigger.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `let low = …`
/// branch (so every mismatch is a violation) fails this.
#[test]
fn a_low_confidence_pairing_mismatch_is_downgraded_to_a_finding() {
    let mut a_row = bare_row("f", 1, Some("r"), Some(2), 1);
    a_row.pairing_confidence = PairingConfidence::Low;
    let a = vec![a_row];
    let b = vec![bare_row("f", 1, None, None, 1)];
    let v = compare(&a, &b);
    assert!(
        !v.passed(),
        "the expected-zero corpus verdict must reject every finding: {v:#?}"
    );
    assert_eq!(v.findings[0].class, "pairing-mismatch-low-confidence");
    assert_eq!(v.aggregates["pairing-mismatch-low-confidence"], 1);
}

/// **Class 5 — a classification disagreement is an attributed finding.**
///
/// Attributed, and — like every finding class while the expected-zero pin
/// stands — failing for its program. The sweep still continues past it.
///
/// `ptr_depth` is the one field both producers derive with *different*
/// implementations of the depth predicate (§2.2), so a disagreement is
/// information about the two derivations rather than proof either is wrong.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `if a.ptr_depth !=
/// b.ptr_depth` block fails this.
#[test]
fn a_classification_mismatch_is_an_attributed_finding() {
    let a = vec![bare_row("f", 1, Some("p"), Some(1), 2)];
    let b = vec![bare_row("f", 1, Some("p"), Some(1), 1)];
    let v = compare(&a, &b);
    assert!(
        !v.passed(),
        "the expected-zero corpus verdict must reject every finding: {v:#?}"
    );
    assert_eq!(v.findings[0].class, "classification-mismatch");
    assert!(v.findings[0].detail.contains("A=2"), "{:#?}", v.findings[0]);
    assert_eq!(v.aggregates["classification-mismatch"], 1);
}

// ---------------------------------------------------------------------------
// A.6 (amendment a) — SINGLE-TERM pairing disagreements
// ---------------------------------------------------------------------------

/// **Name differs, index agrees.**
///
/// This case exists because the headline permutation witness cannot cover it: a
/// real permutation flips `param_name` and `arg_index` **together**, so a
/// comparator that checked only `arg_index` would still pass A.7. Without this
/// test, dropping `param_name` from `pairing_agrees` is a surviving mutant
/// hiding behind the headline witness.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting `a.param_name ==
/// b.param_name` from `pairing_agrees` fails this (and only this).
#[test]
fn pairing_compares_the_name_term() {
    let a = vec![bare_row("f", 1, Some("r"), Some(1), 1)];
    let b = vec![bare_row("f", 1, Some("q"), Some(1), 1)];
    assert!(
        !compare(&a, &b).passed(),
        "a name-only disagreement was not detected — `param_name` is not being \
         compared"
    );
}

/// **Index differs, name agrees.** The mirror of the above, for the other term.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting `a.arg_index ==
/// b.arg_index` from `pairing_agrees` fails this (and only this).
#[test]
fn pairing_compares_the_index_term() {
    let a = vec![bare_row("f", 1, Some("p"), Some(3), 1)];
    let b = vec![bare_row("f", 1, Some("p"), Some(1), 1)];
    assert!(
        !compare(&a, &b).passed(),
        "an index-only disagreement was not detected — `arg_index` is not being \
         compared"
    );
}

// ---------------------------------------------------------------------------
// A.7 — THE ROUND'S LOAD-BEARING WITNESS
// ---------------------------------------------------------------------------

/// **The in-domain permutation, at the artifact layer.**
///
/// This is the defect F1 named and the reason the apparatus moved. Two pointer
/// parameters of one function have their HIR associations swapped: the set of
/// `(fn_path, mir_local)` keys is **identical**, every membership check agrees,
/// and the in-process gate reported zero gaps. The pairing terms in the row are
/// what make it visible.
///
/// Note what is deliberately NOT perturbed: no key is added, none removed, and
/// the row count is unchanged. Any comparison that reduces to membership or to
/// counts passes this by construction.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the `if
/// !pairing_agrees(a, b)` block in `compare` fails this. Deleting **either**
/// term inside `pairing_agrees` does NOT fail it — see
/// `pairing_compares_the_name_term` / `…index_term`, which exist for exactly
/// that reason.
#[test]
fn an_in_domain_permutation_is_caught() {
    // Producer B: the ground truth from var_debug_info.
    let b = vec![
        bare_row("two", 1, Some("q"), Some(1), 1),
        bare_row("two", 2, Some("r"), Some(2), 1),
    ];
    // Producer A: same keys, associations swapped.
    let a = vec![
        bare_row("two", 1, Some("r"), Some(2), 1),
        bare_row("two", 2, Some("q"), Some(1), 1),
    ];

    let a_keys: Vec<(&str, u32)> = a.iter().map(|r| r.key()).collect();
    let b_keys: Vec<(&str, u32)> = b.iter().map(|r| r.key()).collect();
    assert_eq!(
        a_keys, b_keys,
        "the fixture must be membership-identical, or it is not testing the \
         permutation blind spot"
    );

    let v = compare(&a, &b);
    assert!(
        !v.passed(),
        "an in-domain permutation was ACCEPTED — this is F1, the defect the \
         whole apparatus move exists to close: {v:#?}"
    );
    assert_eq!(v.violations.len(), 2, "both rows are mis-paired: {v:#?}");
    assert!(v.violations.iter().all(|x| x.class == "pairing-mismatch"));
}

// ---------------------------------------------------------------------------
// A.8 — aggregates are always present
// ---------------------------------------------------------------------------

/// **Every finding class is present in the aggregates even at zero**, so a
/// corpus gate can pin it.
///
/// Attribution without aggregation is how downgrades go silent: a class that
/// vanishes from the map when empty cannot be pinned to zero, and R-B's "loud
/// in the counters" only holds if something reads the counters.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the
/// `for class in FINDING_CLASSES` pre-seed loop in `compare` fails this.
#[test]
fn every_finding_class_is_aggregated_even_at_zero() {
    let rows = vec![bare_row("f", 1, Some("p"), Some(1), 1)];
    let v = compare(&rows, &rows);
    assert!(v.passed() && v.findings.is_empty(), "{v:#?}");
    for class in FINDING_CLASSES {
        assert_eq!(
            v.aggregates.get(class),
            Some(&0),
            "class `{class}` is absent from the aggregates on a clean run, so it \
             cannot be pinned to zero at the corpus gate: {:#?}",
            v.aggregates
        );
    }
}

/// A future writer cannot introduce an unregistered finding class and have the
/// reader interpret its absent aggregate as zero.
///
/// *Mutation-tested:* restoring the old violations-only/default-to-zero verdict
/// makes this crafted writer/reader mismatch pass.
#[test]
fn an_unknown_finding_class_fails_the_verdict() {
    let rows = vec![bare_row("f", 1, Some("p"), Some(1), 1)];
    let mut verdict = compare(&rows, &rows);
    verdict.findings.push(Finding {
        class: "future-writer-class",
        fn_path: "f".to_owned(),
        mir_local: 1,
        detail: "crafted writer/reader mismatch".to_owned(),
    });

    assert!(
        !verdict.passed(),
        "an unregistered finding class was accepted because its missing \
         aggregate defaulted to zero: {verdict:#?}"
    );
}

/// A registered expected-zero class may not disappear from the map and be read
/// as zero.
///
/// *Mutation-tested:* restoring the old default-to-zero verdict makes this
/// crafted missing-key breach pass.
#[test]
fn a_missing_registered_aggregate_fails_the_verdict() {
    let rows = vec![bare_row("f", 1, Some("p"), Some(1), 1)];
    let mut verdict = compare(&rows, &rows);
    verdict.aggregates.remove("out-of-coverage");

    assert!(
        !verdict.passed(),
        "a missing registered aggregate was accepted as zero: {verdict:#?}"
    );
}

/// The clean case: identical artifacts reconcile with nothing to report.
///
/// **Positive control, and no deletion mutation fails it** — stated rather than
/// dressed up. A test asserting the comparator *accepts* agreement cannot be
/// broken by deleting one of its disagreement arms; its job is to prove the
/// seven negatives above are not passing because `compare` reports everything.
#[test]
fn identical_artifacts_reconcile_clean() {
    let rows = vec![
        bare_row("f", 1, Some("p"), Some(1), 1),
        bare_row("g", 1, Some("x"), Some(1), 2),
    ];
    let v = compare(&rows, &rows);
    assert!(v.passed(), "{v:#?}");
    assert!(v.findings.is_empty(), "{v:#?}");
}

// ---------------------------------------------------------------------------
// T1.4-iv (residue B) — equal cardinality, DISJOINT membership
// ---------------------------------------------------------------------------

/// **Equal counts with different members must still fail.**
///
/// Restored: `equal_counts_with_different_members_still_fail` was deleted with
/// `decision/coverage.rs` at C.2, and no surviving witness had its shape. The
/// A-only and B-only tests use *unequal* counts; the permutation test uses
/// equal counts with *equal keys*. Count-only agreement is exactly what the
/// sets-not-cardinalities rule was written against, so it may not be the one
/// property with no witness.
///
/// **Amendment 1 — why `!passed()` alone is not enough.** This fixture produces
/// findings in BOTH directions: the A-only row is a violation, the B-only row a
/// finding. Asserting only `!passed()` would survive deletion of the *B-only*
/// loop, because the A-only violation alone still fails the verdict. So each
/// direction is asserted non-empty separately, and both loop deletions are run
/// as separate mutations. This is amendment (a)'s single-term lesson in set
/// form.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the A-only loop fails
/// the violation assertion; deleting the B-only loop fails the finding
/// assertion. Neither hides behind the other.
#[test]
fn equal_counts_with_disjoint_members_fail_in_both_directions() {
    let a = vec![
        bare_row("f", 1, Some("p"), Some(1), 1),
        bare_row("f", 9, Some("ghost"), Some(9), 1),
    ];
    let b = vec![
        bare_row("f", 1, Some("p"), Some(1), 1),
        bare_row("f", 2, Some("q"), Some(2), 1),
    ];
    assert_eq!(a.len(), b.len(), "the fixture must have EQUAL cardinality");

    let v = compare(&a, &b);
    assert!(
        v.violations.iter().any(|x| x.class == "collector-surplus" && x.mir_local == 9),
        "the A-only member produced no violation — a count-only comparison \
         would accept this input: {v:#?}"
    );
    assert!(
        v.findings.iter().any(|x| x.class == "out-of-coverage" && x.mir_local == 2),
        "the B-only member produced no finding — a count-only comparison \
         would accept this input: {v:#?}"
    );
    assert_eq!(v.aggregates["out-of-coverage"], 1, "{v:#?}");
}

// ---------------------------------------------------------------------------
// T2.4a — the SPAN axis, comparator level
// ---------------------------------------------------------------------------

/// The interleave holds on real corpus geometry.
///
/// Numbers are the measured `two(p: *mut i32, q: *const u8)` spans from the
/// Track 2 dump, not invented ones.
#[test]
fn the_span_interleave_accepts_real_geometry() {
    let (a0, b0) = span_pair(1, "p", (47, 48), (50, 58));
    let (a1, b1) = span_pair(2, "q", (60, 61), (63, 72));
    let v = compare(&[a0, a1], &[b0, b1]);
    assert!(v.passed(), "real span geometry was rejected: {v:#?}");
}

/// **A span PERMUTATION is caught, and the finding names the failing index.**
///
/// This is the defect HIGH-1 named: identity intact, splice target detached.
/// `param_name`, `arg_index`, `mir_local` and `ptr_depth` are all unchanged —
/// only the ty extents are swapped — so every pre-Track-2 check passes.
///
/// The breach fires at index 1, not index 0 (verified against the real
/// numbers): at i=0 the swapped extent still follows its binding. A witness
/// asserting "every row is flagged" would be wrong.
///
/// *Mutation-tested (Rider 0):* deleting the `b_hi > ty_lo` conjunct fails this;
/// deleting `prev_ty_hi > b_lo` is covered separately below.
#[test]
fn a_span_permutation_is_caught_and_names_the_index() {
    let (mut a0, b0) = span_pair(1, "p", (47, 48), (50, 58));
    let (mut a1, b1) = span_pair(2, "q", (60, 61), (63, 72));
    // Swap ONLY the ty extents — identity untouched.
    std::mem::swap(&mut a0.decl_span_lo, &mut a1.decl_span_lo);
    std::mem::swap(&mut a0.decl_span_hi, &mut a1.decl_span_hi);

    let v = compare(&[a0, a1], &[b0, b1]);
    assert!(!v.passed(), "a detached splice target was accepted: {v:#?}");
    let breach: Vec<_> = v
        .violations
        .iter()
        .filter(|x| x.class == "span-interleave-breach")
        .collect();
    assert_eq!(breach.len(), 1, "expected exactly the one index: {v:#?}");
    assert_eq!(breach[0].mir_local, 2, "the breach is at the second parameter");
    assert!(breach[0].detail.contains("index 1"), "{:#?}", breach[0]);
}

/// The **follows** conjunct on its own: a type extent that starts before its
/// OWN binding ends, with nothing preceding it.
///
/// Added after `T2-conj-follows` **survived**: deleting `b_hi > ty_lo` left the
/// permutation witness green, because a permutation is caught by the ORDERING
/// conjunct at index 1. Rider 5 — the survivor was closed by supplying the
/// missing witness, not by an argument that the conjunct was covered.
///
/// The fixture is a single parameter, so `prev_ty_hi` is 0 and the ordering
/// conjunct cannot fire; only the follows conjunct can.
///
/// *Mutation-tested (Rider 0):* deleting `b_hi > ty_lo` fails this and nothing
/// else.
#[test]
fn the_span_follows_conjunct_is_compared() {
    // ty (47,49) starts BEFORE the binding (50,58) ends — a type detached from
    // the parameter it is supposed to belong to.
    let (a0, b0) = span_pair(1, "p", (50, 58), (47, 49));
    let v = compare(&[a0], &[b0]);
    assert!(
        v.violations.iter().any(|x| x.class == "span-interleave-breach"),
        "a type extent preceding its own binding was accepted — the \
         follows conjunct is not being compared: {v:#?}"
    );
}

/// The **ordering** conjunct on its own: a type that runs past the next
/// binding, with its own binding still ahead of it.
///
/// Single-term coverage, per the standing lesson: the permutation witness flips
/// geometry in a way that can satisfy one conjunct, so each is killed alone.
///
/// *Mutation-tested (Rider 0):* deleting `prev_ty_hi > b_lo` fails this and
/// not the permutation witness.
#[test]
fn the_span_ordering_conjunct_is_compared() {
    let (a0, b0) = span_pair(1, "p", (47, 48), (50, 90)); // ty overruns q's binding
    let (a1, b1) = span_pair(2, "q", (60, 61), (95, 99));
    let v = compare(&[a0, a1], &[b0, b1]);
    assert!(
        v.violations.iter().any(|x| x.class == "span-interleave-breach"),
        "an overrunning type extent was accepted: {v:#?}"
    );
}

/// A row without a usable extent pair is `span-check-not-evaluable` — its own
/// class, not folded into the pairing class.
///
/// *Mutation-tested (Rider 0):* changing the class string to
/// `"pairing-mismatch-low-confidence"` fails this.
#[test]
fn an_unevaluable_span_row_gets_its_own_class() {
    let (a0, b0) = span_pair(1, "p", (47, 48), (50, 58));
    let (mut a1, b1) = span_pair(2, "q", (60, 61), (63, 72));
    a1.decl_span_lo = None; // producer A could not supply an extent
    let v = compare(&[a0, a1], &[b0, b1]);
    assert_eq!(v.aggregates["span-check-not-evaluable"], 1, "{v:#?}");
    assert!(
        v.findings.iter().any(|f| f.class == "span-check-not-evaluable"),
        "{v:#?}"
    );
}

/// **The activation predicate is all-or-nothing.** Zero `binding_span_lo`
/// anywhere ⇒ inactive; ANY present ⇒ active, and absent bindings become real
/// findings. No gray zone.
///
/// *Mutation-tested (Rider 0):* changing `any` to `all` in `span_axis_active`
/// fails the second half.
#[test]
fn the_span_axis_activation_predicate_has_no_gray_zone() {
    let plain = vec![bare_row("f", 1, Some("p"), Some(1), 1)];
    assert!(
        !super::compare::span_axis_active(&plain),
        "an artifact with no binding spans must report INACTIVE"
    );

    let (a0, b0) = span_pair(1, "p", (47, 48), (50, 58));
    let mut b1 = bare_row("f", 2, Some("q"), Some(2), 1); // no binding span
    b1.pairing_confidence = PairingConfidence::High;
    let mut a1 = bare_row("f", 2, Some("q"), Some(2), 1);
    a1.decl_span_lo = Some(63);
    a1.decl_span_hi = Some(72);
    assert!(
        super::compare::span_axis_active(&[b0.clone(), b1.clone()]),
        "ONE present binding span must make the whole artifact ACTIVE"
    );
    let v = compare(&[a0, a1], &[b0, b1]);
    assert_eq!(
        v.aggregates["span-check-not-evaluable"], 1,
        "a mixed artifact must treat the absent binding as a real finding, not \
         as tolerated dormancy: {v:#?}"
    );
}

/// **Ruling F — an unannotated LOCAL is non-evaluable under its OWN class.**
///
/// The population split exists because the two halves have different expected
/// values: a parameter always has a declared type, so a non-evaluable parameter
/// is an instrument fault (expected zero); an unannotated local has no
/// declaration to point at, and 83.6% of corpus locals are exactly that.
///
/// The assertion is two-sided on purpose. Counting the local is half the
/// property; the other half is that it did **not** land in the parameter class,
/// because that class keeps a zero-pin and a mis-routed local would break the
/// Track 2 calibration rather than its own.
///
/// *Mutation-tested (Rider 0, deletion first):* deleting the
/// `span-check-not-evaluable-local` arm in `compare`'s population split — so the
/// local is counted under the parameter class — fails this on BOTH assertions.
#[test]
fn an_unannotated_local_counts_under_the_locals_class() {
    // A: a local (arg_index None) with NO decl_span — the unannotated shape.
    let mut a_local = bare_row("m::f", 2, Some("p"), None, 1);
    a_local.outcome = Some(Outcome::Degraded);
    a_local.degrade_reason = Some("no-declared-type".to_owned());
    // A parameter alongside it, fully evaluable, so the span axis has a
    // parameter to walk and the parameter class is exercised rather than empty.
    let a_param = full_row();

    // B: binding spans present, which is what makes the axis ACTIVE.
    let mut b_local = bare_row("m::f", 2, Some("p"), None, 1);
    b_local.binding_span_lo = Some(70);
    b_local.binding_span_hi = Some(71);
    let mut b_param = bare_row("m::f", 1, Some("p"), Some(1), 1);
    b_param.binding_span_lo = Some(44);
    b_param.binding_span_hi = Some(45);

    let verdict = compare(&[a_param, a_local], &[b_param, b_local]);

    assert_eq!(
        verdict.aggregates.get("span-check-not-evaluable-local"),
        Some(&1),
        "the unannotated local must be counted under the LOCALS class: {:?}",
        verdict.aggregates
    );
    assert_eq!(
        verdict.aggregates.get("span-check-not-evaluable"),
        Some(&0),
        "the parameter class keeps its zero — a mis-routed local would break \
         Track 2's calibration instead of its own: {:?}",
        verdict.aggregates
    );
}
