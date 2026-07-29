//! Witnesses for the artifact contract and the reconciliation.
//!
//! Every test here is mutation-tested, deletion first (Rider 0), and every one
//! is enumerated in the slice report with its result (Rider 4).

use super::{
    compare::{FINDING_CLASSES, compare},
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
        decl_shape: None,
        outcome: None,
        degrade_reason: None,
    }
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
#[test]
fn encoding_is_byte_exact_and_never_omits_a_field() {
    let full = encode(&[full_row()]);
    assert_eq!(
        full,
        r#"{"fn_path":"m::f","mir_local":1,"param_name":"p","arg_index":1,"ptr_depth":1,"pairing_confidence":"high","decl_span":"<main.rs>:3:14: 3:22","decl_shape":"raw-ptr","outcome":"degraded","degrade_reason":"kind-raw"}
"#,
        "fully-populated row encoding drifted"
    );

    let bare = encode(&[bare_row("g", 2, None, None, 0)]);
    assert_eq!(
        bare,
        r#"{"fn_path":"g","mir_local":2,"param_name":null,"arg_index":null,"ptr_depth":0,"pairing_confidence":"high","decl_span":null,"decl_shape":null,"outcome":null,"degrade_reason":null}
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

/// **Class 1 — B-only row is an attributed finding, and the run continues.**
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
    assert!(v.passed(), "a coverage gap must NOT halt the run: {v:#?}");
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

/// **Class 4 — the low-confidence downgrade.** A `pairing_confidence = low` row
/// with a pairing disagreement is an attributed finding, NOT fail-loud, and it
/// increments the low-confidence aggregate.
///
/// The instrument, not necessarily the collector, is what is in doubt when
/// `var_debug_info` gave no usable entry.
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
    assert!(v.passed(), "a low-confidence pairing must not halt: {v:#?}");
    assert_eq!(v.findings[0].class, "pairing-mismatch-low-confidence");
    assert_eq!(v.aggregates["pairing-mismatch-low-confidence"], 1);
}

/// **Class 5 — a classification disagreement is an attributed finding.**
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
    assert!(v.passed(), "a predicate divergence must not halt: {v:#?}");
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
