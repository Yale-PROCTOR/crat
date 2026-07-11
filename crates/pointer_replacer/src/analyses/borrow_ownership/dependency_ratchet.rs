//! §0.2 dependency ratchet (NB3-3c-i) — enforces the self-containment ledger as a test invariant.
//!
//! The BO end state (execution-plan §0.2, user-ratified 2026-07-11) is **zero dependencies on
//! `analyses/borrow/` and `analyses/ownership/`** except the NB6 validator seam and test-only
//! baselines. This test freezes an **allowlist** of every `analyses::borrow::<seg>` /
//! `analyses::ownership::<seg>` reference the NON-TEST `borrow_ownership/` code is currently
//! permitted to make, each tagged with its §0.2 retirement milestone. It asserts the actual
//! reference surface **equals** the allowlist:
//!   - a NEW reference (surface ⊋ allowlist) fails → a fresh production dependency needs an
//!     explicit, reviewed allowlist entry with its milestone;
//!   - a STALE entry (allowlist ⊋ surface) fails → a retired dependency must be removed from the
//!     allowlist in the same commit, so the allowlist **only ever shrinks**. Self-containment
//!     progress is measured by its length (same tripwire philosophy as the fork-sync tests).
//!
//! The scanner reads the crate source at test time (`CARGO_MANIFEST_DIR`) and defends against every
//! false-match class present in this tree: `borrow_ownership::` substring hits (word-boundary
//! guard), doc/line/block comments (stripped), `std::borrow` re-exports (`Borrow`/`BorrowMut`/`Cow`/
//! `ToOwned` excluded), multi-line `use borrow::{ … }` groups (whole-file scan), and `#[cfg(test)]`
//! modules (stripped — test-only baselines are a sanctioned §0.2 exception).

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::path::{Path, PathBuf};

    /// Every permitted `analyses::borrow::<seg>` reference in non-test BO code, with its §0.2
    /// ledger retirement milestone. MAY ONLY SHRINK.
    const BORROW_ALLOW: &[&str] = &[
        // → S2-4(b) BO-side reconstruction / NB5 lemma loop (the 3a replaying fact source +
        //   orchestration; the fork consumes production's pre-invalidation facts):
        "borrow_inference",
        "BorrowInferenceResults",
        "GBorrowInferCtxt",
        "collect_invalid_loan_demotions",
        // → with `borrow_inference` retirement (BO-native data model replaces the imported types):
        "BorrowSet",
        "Loan",
        "Borrower",
        "Provenance",
        "ProvenanceSet",
        "ProvenanceOwner",
        "ConflictEdge",
        // → NB5-O (BO-native origin derivation replaces the read-only `lifetime_flow` wrap):
        "lifetime_flow",
        // → VALIDATOR SEAM / NB6 (production replay as the independent judge — the one permanent
        //   §0.2 exception, retiring only at the post-C2 rustc validation net). `self` is the
        //   `use borrow::{self, …}` that lets `borrow::borrow_conflicts[_replaying]` resolve:
        "borrow_conflicts",
        "borrow_conflicts_replaying",
        "self",
    ];

    /// Every permitted `analyses::ownership::<seg>` reference in non-test BO code. **NONE** — BO has
    /// been self-contained from ownership since inception (§0.2 ledger: "ownership: NONE ✓ done").
    /// The two `ownership::` strings in the tree are doc-comment intra-links (`mod.rs:337`,
    /// `infer.rs:227`), stripped by the scanner. Any real reference here must fail.
    const OWNERSHIP_ALLOW: &[&str] = &[];

    /// `std::borrow` re-exports — never an `analyses::borrow` dependency.
    const STD_BORROW: &[&str] = &["Borrow", "BorrowMut", "Cow", "ToOwned"];

    /// The ratchet does not scan itself (its allowlist entries are string literals anyway).
    const SELF_FILE: &str = "dependency_ratchet.rs";

    fn bo_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("src/analyses/borrow_ownership")
    }

    fn collect_rs(dir: &Path, out: &mut Vec<PathBuf>) {
        for entry in std::fs::read_dir(dir).expect("read borrow_ownership dir") {
            let p = entry.expect("dir entry").path();
            if p.is_dir() {
                collect_rs(&p, out);
            } else if p.extension().is_some_and(|e| e == "rs")
                && p.file_name().is_none_or(|n| n != SELF_FILE)
            {
                out.push(p);
            }
        }
    }

    /// Replace comment and string-literal spans with spaces, yielding pure ASCII code text. `'` is
    /// deliberately NOT treated as a delimiter (Rust lifetimes `'a`/`'static` are not char literals).
    fn strip_comments_and_strings(src: &str) -> String {
        let b = src.as_bytes();
        let mut out = String::with_capacity(src.len());
        let mut i = 0;
        while i < b.len() {
            let c = b[i];
            if c == b'/' && b.get(i + 1) == Some(&b'/') {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            } else if c == b'/' && b.get(i + 1) == Some(&b'*') {
                i += 2;
                while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                    i += 1;
                }
                i = (i + 2).min(b.len());
                out.push(' ');
            } else if c == b'"' {
                i += 1;
                while i < b.len() {
                    if b[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if b[i] == b'"' {
                        i += 1;
                        break;
                    }
                    i += 1;
                }
                out.push(' ');
            } else {
                out.push(if c.is_ascii() { c as char } else { ' ' });
                i += 1;
            }
        }
        out
    }

    /// Remove every `#[cfg(test)]`-gated item span (mod / fn / use). Operates on already-ASCII text,
    /// so byte offsets are char boundaries.
    fn strip_cfg_test(mut s: String) -> String {
        const ATTR: &str = "#[cfg(test)]";
        while let Some(pos) = s.find(ATTR) {
            let b = s.as_bytes();
            let mut j = pos + ATTR.len();
            while j < b.len() && b[j] != b'{' && b[j] != b';' {
                j += 1;
            }
            let end = if j >= b.len() {
                b.len()
            } else if b[j] == b';' {
                j + 1
            } else {
                let mut depth = 0usize;
                let mut k = j;
                while k < b.len() {
                    match b[k] {
                        b'{' => depth += 1,
                        b'}' => {
                            depth -= 1;
                            if depth == 0 {
                                k += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    k += 1;
                }
                k
            };
            s.replace_range(pos..end, " ");
        }
        s
    }

    fn is_ident(c: u8) -> bool {
        c.is_ascii_alphanumeric() || c == b'_'
    }

    /// Extract the first path segment after each word-boundary `{kind}::` occurrence, expanding a
    /// top-level `{ … }` group into its depth-1 leading identifiers.
    fn extract(kind: &str, text: &str, found: &mut BTreeSet<String>) {
        let b = text.as_bytes();
        let needle = format!("{kind}::");
        let mut base = 0;
        while let Some(rel) = text[base..].find(&needle) {
            let start = base + rel;
            let after = start + needle.len();
            base = after;
            // word boundary: `borrow_ownership::` must not match `ownership::`.
            if start > 0 && is_ident(b[start - 1]) {
                continue;
            }
            let mut j = after;
            while j < b.len() && (b[j] as char).is_whitespace() {
                j += 1;
            }
            if j < b.len() && b[j] == b'{' {
                let mut depth = 0usize;
                let mut expect = false;
                let mut k = j;
                while k < b.len() {
                    match b[k] {
                        b'{' => {
                            depth += 1;
                            expect = true;
                            k += 1;
                        }
                        b'}' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                            k += 1;
                        }
                        b',' if depth == 1 => {
                            expect = true;
                            k += 1;
                        }
                        c if depth == 1 && expect && is_ident(c) => {
                            let s0 = k;
                            while k < b.len() && is_ident(b[k]) {
                                k += 1;
                            }
                            add_seg(kind, &text[s0..k], found);
                            expect = false;
                        }
                        _ => k += 1,
                    }
                }
            } else if j < b.len() && is_ident(b[j]) {
                let s0 = j;
                let mut k = j;
                while k < b.len() && is_ident(b[k]) {
                    k += 1;
                }
                add_seg(kind, &text[s0..k], found);
            }
        }
    }

    fn add_seg(kind: &str, seg: &str, found: &mut BTreeSet<String>) {
        if kind == "borrow" && STD_BORROW.contains(&seg) {
            return;
        }
        found.insert(seg.to_string());
    }

    fn scan() -> (BTreeSet<String>, BTreeSet<String>) {
        let mut files = vec![];
        collect_rs(&bo_dir(), &mut files);
        assert!(files.len() > 10, "expected the BO source tree; found {} files", files.len());
        let (mut borrow, mut ownership) = (BTreeSet::new(), BTreeSet::new());
        for f in &files {
            let src = std::fs::read_to_string(f).expect("read BO source file");
            let clean = strip_cfg_test(strip_comments_and_strings(&src));
            extract("borrow", &clean, &mut borrow);
            extract("ownership", &clean, &mut ownership);
        }
        (borrow, ownership)
    }

    fn diff(actual: &BTreeSet<String>, allow: &[&str]) -> (Vec<String>, Vec<String>) {
        let allow: BTreeSet<&str> = allow.iter().copied().collect();
        let unexpected: Vec<String> =
            actual.iter().filter(|s| !allow.contains(s.as_str())).cloned().collect();
        let stale: Vec<String> =
            allow.iter().filter(|s| !actual.contains(**s)).map(|s| s.to_string()).collect();
        (unexpected, stale)
    }

    /// The ratchet: the actual non-test BO reference surface must EQUAL the allowlist, both
    /// directions. See module docs for the enforcement semantics.
    #[test]
    fn dependency_ratchet_matches_allowlist() {
        let (borrow, ownership) = scan();
        let (b_new, b_stale) = diff(&borrow, BORROW_ALLOW);
        let (o_new, o_stale) = diff(&ownership, OWNERSHIP_ALLOW);
        assert!(
            b_new.is_empty() && b_stale.is_empty() && o_new.is_empty() && o_stale.is_empty(),
            "BO self-containment ratchet tripped (§0.2).\n  \
             borrow  NEW (un-allowlisted refs — remove the dep, or add with a milestone): {b_new:?}\n  \
             borrow  STALE (retired — delete from BORROW_ALLOW so the allowlist shrinks): {b_stale:?}\n  \
             ownership NEW (must stay empty — BO is self-contained from ownership): {o_new:?}\n  \
             ownership STALE: {o_stale:?}\n  \
             (allowlist length is the self-containment metric: {} borrow / {} ownership)",
            BORROW_ALLOW.len(),
            OWNERSHIP_ALLOW.len(),
        );
    }
}
