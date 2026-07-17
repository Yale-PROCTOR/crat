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
        // → NB5-F2 (field candidacy: the fork disables a Raw field's loan via the manifest-widened
        //   `disable_owner(ProvenanceOwner::Field(field))`; `StructFieldSlot` is the field key):
        "StructFieldSlot",
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
                // Rust block comments NEST — track depth to the matching outer `*/`, else a
                // `/* … /* … */ #[cfg(test)] */` leaves the inner `#[cfg(test)]` visible and
                // strip_cfg_test removes a real declaration after it.
                i += 2;
                let mut depth = 1usize;
                while i < b.len() && depth > 0 {
                    if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
                        depth += 1;
                        i += 2;
                    } else if b[i] == b'*' && b.get(i + 1) == Some(&b'/') {
                        depth -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                out.push(' ');
            } else if c == b'r'
                && {
                    // Raw string prefix `r` `#`×N `"` (also matches the `r` of a byte-raw `br"…"`,
                    // whose leading `b` is pushed harmlessly). NOT a raw identifier `r#ident` (no `"`).
                    let mut h = i + 1;
                    while h < b.len() && b[h] == b'#' {
                        h += 1;
                    }
                    h < b.len() && b[h] == b'"'
                }
            {
                // Raw string `r #×N " … " #×N` — content is uninterpreted; find the closing `"`
                // followed by exactly N `#` and blank the whole literal, so an interior `"` (or `/*`)
                // cannot desync the scanner and swallow the following code.
                let mut h = i + 1;
                while h < b.len() && b[h] == b'#' {
                    h += 1;
                }
                let hashes = h - (i + 1);
                let mut m = h + 1;
                while m < b.len() {
                    if b[m] == b'"'
                        && b[m + 1..].iter().take(hashes).filter(|&&x| x == b'#').count() == hashes
                    {
                        m += 1 + hashes;
                        break;
                    }
                    m += 1;
                }
                i = m;
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
            } else if c == b'\'' {
                // Char literal vs lifetime. A char literal (`'x'`, `'\n'`, `'{'`, `'\u{7f}'`) is
                // blanked so its contents — braces especially — cannot corrupt `strip_cfg_test`'s
                // brace count (a `'{'` inside a #[cfg(test)] block would otherwise over-consume and
                // swallow real code). A lifetime (`'a`, `'static`: ident chars, no closing quote) is
                // left untouched. Heuristic: it's a char literal iff the char after `'` is `\`
                // (escape) or is followed immediately by a closing `'`.
                let is_char_lit =
                    b.get(i + 1) == Some(&b'\\') || b.get(i + 2) == Some(&b'\'');
                if is_char_lit {
                    i += 1; // opening '
                    if b.get(i) == Some(&b'\\') {
                        i += 1; // backslash
                        match b.get(i) {
                            Some(&b'x') => i += 3,      // \xNN
                            Some(&b'u') => {
                                while i < b.len() && b[i] != b'}' {
                                    i += 1;
                                }
                                i += 1; // past '}'
                            }
                            _ => i += 1, // \n \\ \' \0 ...
                        }
                    } else {
                        i += 1; // the single char
                    }
                    if b.get(i) == Some(&b'\'') {
                        i += 1; // closing '
                    }
                    out.push(' ');
                } else {
                    out.push('\''); // lifetime tick
                    i += 1;
                }
            } else {
                out.push(if c.is_ascii() { c as char } else { ' ' });
                i += 1;
            }
        }
        out
    }

    /// Remove every `#[cfg(test)]`-gated item span (mod / fn / use / FIELD / variant). Operates on
    /// already-ASCII text, so byte offsets are char boundaries. The item terminator is found while
    /// tracking `()`/`[]`/`{}` nesting, so a comma or brace *inside* a parameter list, type, or
    /// initializer is not mistaken for the item boundary: the item ends at the first **depth-0** `;`
    /// or `,` (use / mod-decl / field / enum variant), or a depth-0 `{` (mod / fn / impl body) whose
    /// matching `}` closes it. (Residual: a generic field type with a *top-level* comma, e.g.
    /// `f: Map<K, V>,` — `<>` is not tracked (angle brackets are ambiguous with comparison) — would
    /// under-consume; that fails LOUD as a false positive, never a silent false-negative.)
    fn strip_cfg_test(mut s: String) -> String {
        const ATTR: &str = "#[cfg(test)]";
        while let Some(pos) = s.find(ATTR) {
            let b = s.as_bytes();
            let mut depth = 0i32;
            let mut k = pos + ATTR.len();
            let mut end = b.len();
            while k < b.len() {
                match b[k] {
                    b'(' | b'[' => depth += 1,
                    b')' | b']' => depth -= 1,
                    b'{' if depth == 0 => {
                        // Brace-match the item body.
                        let mut d = 0i32;
                        let mut m = k;
                        while m < b.len() {
                            match b[m] {
                                b'{' => d += 1,
                                b'}' => {
                                    d -= 1;
                                    if d == 0 {
                                        m += 1;
                                        break;
                                    }
                                }
                                _ => {}
                            }
                            m += 1;
                        }
                        end = m;
                        break;
                    }
                    b'{' => depth += 1,
                    b'}' => depth -= 1,
                    b';' | b',' if depth == 0 => {
                        end = k + 1;
                        break;
                    }
                    _ => {}
                }
                k += 1;
            }
            s.replace_range(pos..end, " ");
        }
        s
    }

    fn is_ident(c: u8) -> bool {
        c.is_ascii_alphanumeric() || c == b'_'
    }

    /// Extract the first path segment after each whole-word `{kind}` followed by (optionally spaced)
    /// `::`, expanding a top-level `{ … }` group into its depth-1 leading identifiers and recording a
    /// glob `*`. Matching the WORD (not the literal `{kind}::`) catches `borrow :: X` spaced
    /// separators; the whole-word guards keep `borrow_ownership` / `borrow_inference`'s inner
    /// substrings from matching.
    fn extract(kind: &str, text: &str, found: &mut BTreeSet<String>) {
        let b = text.as_bytes();
        let mut base = 0;
        while let Some(rel) = text[base..].find(kind) {
            let start = base + rel;
            let after_word = start + kind.len();
            base = after_word;
            // Whole word: non-ident on BOTH sides (so `borrow_ownership`, `borrow_inference`,
            // `xborrow` don't match on their embedded `borrow`/`ownership`).
            if start > 0 && is_ident(b[start - 1]) {
                continue;
            }
            if after_word < b.len() && is_ident(b[after_word]) {
                continue;
            }
            // Optional whitespace, then the `::` path separator.
            let mut p = after_word;
            while p < b.len() && (b[p] as char).is_whitespace() {
                p += 1;
            }
            if !(p + 1 < b.len() && b[p] == b':' && b[p + 1] == b':') {
                // Not `::`. A module ALIAS `borrow as X` imports the whole module under a new name —
                // a whole-surface dependency the alias would otherwise hide from segment tracking, so
                // record `*` (not in any allowlist ⇒ the ratchet trips).
                if b.get(p) == Some(&b'a')
                    && b.get(p + 1) == Some(&b's')
                    && b.get(p + 2).is_some_and(|&x| (x as char).is_whitespace())
                {
                    add_seg(kind, "*", found);
                }
                continue;
            }
            let mut j = p + 2;
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
                        b'*' if depth == 1 && expect => {
                            // A grouped glob `borrow::{self, *}` imports the whole surface — record `*`
                            // (else the group walker would capture only the sibling idents and miss it).
                            add_seg(kind, "*", found);
                            expect = false;
                            k += 1;
                        }
                        c if depth == 1 && expect && is_ident(c) => {
                            let s0 = k;
                            while k < b.len() && is_ident(b[k]) {
                                k += 1;
                            }
                            let seg = &text[s0..k];
                            // `self as X` inside a group aliases the WHOLE module → record `*` (a
                            // normal `Foo as Bar` keeps `Foo` as the captured segment; only a self-alias
                            // hides the module behind a new name).
                            let mut q = k;
                            while q < b.len() && (b[q] as char).is_whitespace() {
                                q += 1;
                            }
                            let self_aliased = seg == "self"
                                && b.get(q) == Some(&b'a')
                                && b.get(q + 1) == Some(&b's')
                                && b.get(q + 2).is_some_and(|&x| (x as char).is_whitespace());
                            add_seg(kind, if self_aliased { "*" } else { seg }, found);
                            expect = false;
                        }
                        _ => k += 1,
                    }
                }
            } else if j < b.len() && b[j] == b'*' {
                // Glob import `borrow::*` pulls in the ENTIRE module surface — record it as "*" so it
                // can never SILENTLY pass (not in any allowlist ⇒ the ratchet trips on it).
                add_seg(kind, "*", found);
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

    /// A glob import `borrow::*` pulls in the entire module surface. `extract` must record it as `*`
    /// (which is in no allowlist ⇒ the ratchet trips) rather than capturing nothing and silently
    /// passing — the whole-surface false-negative.
    #[test]
    fn scanner_catches_glob_import() {
        let cleaned = strip_cfg_test(strip_comments_and_strings("use crate::analyses::borrow::*;"));
        let mut set = BTreeSet::new();
        extract("borrow", &cleaned, &mut set);
        assert!(set.contains("*"), "glob `borrow::*` must be recorded, not silently missed; got {set:?}");
    }

    /// A `'{'` char literal inside a `#[cfg(test)]` block must not make `strip_cfg_test` over-consume
    /// and swallow a real `borrow::` ref AFTER the block (a silent false-negative). The ref INSIDE the
    /// (test) block must itself be stripped.
    #[test]
    fn scanner_char_literal_brace_is_stripped() {
        let src = "#[cfg(test)] mod t { let _c = '{'; let _ = borrow::TEST_ONLY; } \
                   fn real() { let _ = borrow::REAL_DEP; }";
        let cleaned = strip_cfg_test(strip_comments_and_strings(src));
        let mut set = BTreeSet::new();
        extract("borrow", &cleaned, &mut set);
        assert!(set.contains("REAL_DEP"), "real ref after the block must survive; got {set:?}");
        assert!(!set.contains("TEST_ONLY"), "test-only ref inside the block must be stripped; got {set:?}");
    }

    /// A comma-terminated `#[cfg(test)]` FIELD (the `call_graph.rs:109` shape) must be stripped at its
    /// comma, NOT brace-match the next block and swallow real code with its `borrow::` ref (a silent
    /// false-negative). The test-only field type must not be counted either.
    #[test]
    fn scanner_cfg_gated_field_does_not_over_consume() {
        let src = "struct S { #[cfg(test)] dbg: VecVec<DefId>, keep: T } \
                   impl S { fn m() { let _ = borrow::REAL_DEP; } }";
        let cleaned = strip_cfg_test(strip_comments_and_strings(src));
        let mut set = BTreeSet::new();
        extract("borrow", &cleaned, &mut set);
        assert!(set.contains("REAL_DEP"), "real ref after a cfg-gated field must survive; got {set:?}");
    }

    /// A spaced path separator `borrow :: X` (or `borrow:: X`) must not evade the scanner — a
    /// hand-written space around `::` would otherwise hide a real dependency.
    #[test]
    fn scanner_handles_spaced_path_separator() {
        let cleaned = strip_cfg_test(strip_comments_and_strings("fn f() { let _ = borrow :: SpacedDep; }"));
        let mut set = BTreeSet::new();
        extract("borrow", &cleaned, &mut set);
        assert!(set.contains("SpacedDep"), "space around `::` must not evade the scanner; got {set:?}");
    }

    /// A grouped glob `borrow::{self, *}` must record `*` — not silently capture only the sibling
    /// `self` (Codex re-review). The `*` imports the whole surface.
    #[test]
    fn scanner_catches_grouped_glob() {
        let cleaned =
            strip_cfg_test(strip_comments_and_strings("use crate::analyses::borrow::{self, *};"));
        let mut set = BTreeSet::new();
        extract("borrow", &cleaned, &mut set);
        assert!(set.contains("*"), "grouped glob `borrow::{{self, *}}` must record `*`; got {set:?}");
    }

    /// A module alias `use borrow as prod;` imports the whole surface under a new name — record `*`
    /// (the alias would otherwise hide every `prod::X` use from segment tracking) (Codex re-review).
    #[test]
    fn scanner_catches_module_alias() {
        let cleaned =
            strip_cfg_test(strip_comments_and_strings("use crate::analyses::borrow as prod;"));
        let mut set = BTreeSet::new();
        extract("borrow", &cleaned, &mut set);
        assert!(set.contains("*"), "module alias `borrow as prod` must record `*`; got {set:?}");
    }

    /// A raw string with an interior `"` must not desync the scanner and blank the following code —
    /// the dependency AFTER it must survive scanning (Codex re-review).
    #[test]
    fn scanner_raw_string_does_not_swallow_following_dep() {
        let src = "const S: &str = r#\"one quote: \"\"#; fn f() { let _ = borrow::REAL_DEP; }";
        let cleaned = strip_cfg_test(strip_comments_and_strings(src));
        let mut set = BTreeSet::new();
        extract("borrow", &cleaned, &mut set);
        assert!(set.contains("REAL_DEP"), "dep after a raw string must survive scanning; got {set:?}");
    }

    /// A self-aliased group `borrow::{self as prod}` aliases the WHOLE module — must record `*`, not
    /// just capture the sibling `self` (Codex 3rd review).
    #[test]
    fn scanner_catches_grouped_self_alias() {
        let cleaned =
            strip_cfg_test(strip_comments_and_strings("use crate::analyses::borrow::{self as prod};"));
        let mut set = BTreeSet::new();
        extract("borrow", &cleaned, &mut set);
        assert!(
            set.contains("*"),
            "grouped self-alias `borrow::{{self as prod}}` must record `*`; got {set:?}"
        );
    }

    /// Rust block comments NEST — `/* /* */ #[cfg(test)] */` must be fully stripped so the interior
    /// cfg token cannot make strip_cfg_test remove a real dependency after it (Codex 3rd review).
    #[test]
    fn scanner_nested_block_comment() {
        let src = "/* outer /* inner */ #[cfg(test)] */ type H = crate::analyses::borrow::REAL_DEP;";
        let cleaned = strip_cfg_test(strip_comments_and_strings(src));
        let mut set = BTreeSet::new();
        extract("borrow", &cleaned, &mut set);
        assert!(set.contains("REAL_DEP"), "dep after a nested block comment must survive; got {set:?}");
    }
}
