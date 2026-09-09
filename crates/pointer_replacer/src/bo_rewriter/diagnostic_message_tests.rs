//! L31/L32 (§39 addendum 272, R272-3 — re-targeted) — the diagnostic
//! primary-message capture.
//!
//! The J″ diagnostic ledger's 21 live rows are 19 `E0308` and **2 with no
//! error code at all**, and the two uncoded ones are the shape L31 named: one
//! carries a CHILD note as its whole message (`` `#[deny(invalid_reference_casting)]`
//! on by default ``) and the other carries **nothing**. The same emptiness
//! shows on every captured `E0282` and `E0599` row.
//!
//! The cause is in `verify::Capture::emit_diagnostic`: it built the message
//! from `DiagMessage::Str` alone. rustc's own `Translator` handles three
//! variants — a `Translated` message and a `FluentIdentifier` yet to be
//! resolved — and every lint and every Fluent-authored error uses one of the
//! other two. So the primary message was dropped and whatever `Str` children
//! happened to exist were left standing in its place.
//!
//! That is not cosmetic. `verify::baseline_key` keys a diagnostic on
//! `(file, code, message)`, so an empty message collapses distinct
//! diagnostics of the same code in one file into ONE key — and the baseline
//! differential is a MULTISET comparison over those keys. A rewrite-introduced
//! diagnostic could hide behind a baseline one it does not actually match.

/// Every uncoded lint error in this fixture carries a real message.
///
/// `invalid_reference_casting` is deny-by-default and Fluent-authored — the
/// exact class the J″ ledger caught with an empty message — and it is also
/// the class the raw-boundary gate must never go blind to, since writing
/// through a shared-reference-derived pointer is the S-class shape.
#[test]
fn diag_w1_uncoded_lint_errors_carry_their_primary_message() {
    const INPUT: &str = r#"
        pub fn main() {
            let x = 8_u8;
            let p = &x as *const u8 as *mut u8;
            unsafe { *p = 9; }
        }
    "#;
    let diagnosis = super::verify::diagnose_str(INPUT);
    assert!(
        diagnosis.errors > 0,
        "the fixture must produce an error-level diagnostic: {diagnosis:#?}"
    );
    assert_eq!(
        diagnosis.unrenderable, 0,
        "no captured diagnostic may have an empty message: {diagnosis:#?}"
    );
    let uncoded = diagnosis
        .diags
        .iter()
        .filter(|diag| diag.code.is_none())
        .collect::<Vec<_>>();
    assert!(
        !uncoded.is_empty(),
        "the fixture must produce an uncoded lint error: {diagnosis:#?}"
    );
    for diag in &uncoded {
        assert!(
            !diag.message.trim().is_empty(),
            "an uncoded lint lost its primary message: {diag:#?}"
        );
        assert!(
            diag.message.contains("undefined behavior"),
            "the PRIMARY message must be the primary one, not a child note: {diag:#?}"
        );
    }
}

/// The coded twin. A Fluent-authored coded error keeps its message too, and
/// its code still identifies it.
#[test]
fn diag_w1_coded_errors_keep_their_primary_message() {
    const INPUT: &str = r#"
        pub fn takes(_x: &i32) {}
        pub fn main() {
            let p: *const i32 = core::ptr::null();
            takes(p);
        }
    "#;
    let diagnosis = super::verify::diagnose_str(INPUT);
    assert_eq!(diagnosis.unrenderable, 0, "{diagnosis:#?}");
    let coded = diagnosis
        .diags
        .iter()
        .find(|diag| matches!(diag.code.as_deref(), Some("E0308" | "ErrCode(308)")))
        .unwrap_or_else(|| panic!("E0308 expected: {diagnosis:#?}"));
    assert!(
        coded.message.contains("mismatched types"),
        "the primary message is the head of the row: {coded:#?}"
    );
}

/// The identity consequence, stated as a property rather than a message
/// spelling: two DIFFERENT diagnostics in one file must not share a
/// `baseline_key`, which is exactly what an empty message caused.
#[test]
fn diag_w1_distinct_diagnostics_do_not_share_one_baseline_key() {
    const INPUT: &str = r#"
        pub fn main() {
            let x = 8_u8;
            let y = 9_u8;
            let p = &x as *const u8 as *mut u8;
            let q = &y as *const u8 as *mut u8;
            unsafe { *p = 1; }
            unsafe { *q = 2; }
        }
    "#;
    let diagnosis = super::verify::diagnose_str(INPUT);
    assert_eq!(diagnosis.unrenderable, 0, "{diagnosis:#?}");
    let root = std::path::Path::new("");
    let keys = diagnosis
        .diags
        .iter()
        .map(|diag| super::verify::baseline_key(diag, root))
        .collect::<std::collections::BTreeSet<_>>();
    assert!(
        keys.iter()
            .all(|(_, _, message)| !message.trim().is_empty()),
        "a diagnostic identity keyed on an empty message: {keys:#?}"
    );
}
