//! **The AST application layer's bridge** — phases 1 and 2 of the migration.
//!
//! Standing decision 3 requires structure-preserving AST rewriting. The M1
//! application layer departed from it into byte splicing (departure recorded
//! 2026-08-12); this module is where the return begins.
//!
//! # The ordering constraint, and why it is not negotiable
//!
//! [`::utils::ast::expanded_ast`] **panics once the HIR is built** — it clones
//! the resolver's crate, and the resolver is consumed by lowering. Every
//! consumer of this module must therefore capture the AST as the FIRST action
//! inside the compiler callback, before `decide_table` or any other query
//! touches HIR or MIR.
//!
//! That is a constraint on call order, not a limitation: the AST is an input to
//! the pipeline exactly as the MIR is, and nothing about the decision layer
//! needs to run before it.
//!
//! # What the map is, and which direction it runs
//!
//! [`::utils::ast::make_ast_to_hir`] yields `AstToHir`, whose `local_map` sends
//! **AST `NodeId` → HIR `HirId`** and whose `global_map` sends
//! **AST `NodeId` → `LocalDefId`**. That is the FORWARD direction, and it is the
//! one a tree walk wants: the transform visitor walks the AST, reads each
//! node's own `NodeId`, resolves it to a `HirId`, and asks the decision table —
//! which is keyed by `(LocalDefId, HirId)` — what to do. No inversion is
//! needed, and none is built.
//!
//! `map_pat_to_pat` maps an AST `PatKind::Ident` onto `hir::PatKind::Binding`,
//! which is exactly the key M1 uses for both universes: a subject's `hir_id` is
//! its binding pattern's.
//!
//! # The mapper's failure mode is a PANIC, not a miss
//!
//! `ast_to_hir.rs` carries 161 assertions and asserts its way through every
//! structural correspondence it expects. A shape it does not expect aborts the
//! mapping rather than returning `None` for one node. So a resolution failure
//! can present as a panic over a whole crate, and the census below runs the
//! mapping inside `catch_unwind` for that reason — a program whose mapping
//! aborts is a REPORTED finding, not a dead sweep.

use rustc_middle::ty::TyCtxt;

/// **The substituted range must COVER the outer attributes.**
///
/// `Item::span` starts at `pub`/`unsafe`/`fn`, NOT at the first attribute —
/// measured, not assumed: `subst_span_at_attr` came back **0 on all 20
/// programs**. `pprust::item_to_string` prints the attributes, so replacing
/// `item.span` alone leaves the substrate's `#[no_mangle]` in place and adds a
/// second one from the printed text. `bst.substituted.rs` had them on
/// consecutive lines 47 and 48.
///
/// This is the counter earning its place: the defect is invisible in the
/// idempotence gate — printing and reparsing a function is a fixed point
/// whether or not the SPAN used to splice it is right — and it would have
/// surfaced in phase 3 as an unexplained parity diff over every attributed
/// function in the corpus.
pub(crate) fn item_span_with_attrs(item: &rustc_ast::Item) -> rustc_span::Span {
    let lo = item
        .attrs
        .iter()
        .map(|a| a.span.lo())
        .min()
        .map_or(item.span.lo(), |a| a.min(item.span.lo()));
    item.span.with_lo(lo)
}

/// **PHASE 1's SECOND HALF — does function-granular substitution COMPILE?**
///
/// Not "does a whole-crate reprint compile". The frozen-substrate correction
/// made that question obsolete: the emitted crate is the substrate with each
/// transformed function's byte range replaced by that function's printed text,
/// and every other byte untouched. So the property to measure is the one the
/// emission model actually relies on.
///
/// **It also discharges the carried caveat** (reviewer note, 2026-08-12):
/// *"non-overlapping by construction" rests on decided functions being disjoint
/// top-level items — a nested item inside a decided function's range is a
/// FINDING, not a silent assumption.* This walk reports containment rather than
/// assuming its absence.
pub(crate) struct SubstStats {
    /// Function spans that CONTAIN another function's span. Must be 0, or
    /// function-granular substitution is not non-overlapping after all.
    pub nested: usize,
    /// Spans whose original text could not be recovered — substitution would be
    /// guessing, so it is refused and counted.
    pub unrenderable: usize,
    /// Does `item.span` include the outer attributes? Measured, not assumed:
    /// substituting a span that excludes them duplicates every `#[no_mangle]`.
    pub span_starts_at_attr: usize,
    /// **THE `files_touched` NUMERATOR — files with at least one SURVIVING
    /// EDIT** (ruling 2026-08-18).
    ///
    /// NOT the size of the emission map. The map is SEEDED with every file
    /// holding a function, because a crate with no surviving edits must still
    /// emit its original text rather than an empty file (the g09 fix). Counting
    /// map entries therefore reports a file as touched when nothing touched it —
    /// measured on `bst`, which converges with every subject reverted and so
    /// reported 1 against the span layer's 0.
    ///
    /// This counts distinct files among the reprints that SURVIVED the
    /// changed-set filter — the same single derivation that decides what gets
    /// spliced, so the counter cannot drift from the emission.
    pub files_with_edits: usize,
}

pub(crate) fn collect_fn_spans(
    items: &[rustc_ast::ptr::P<rustc_ast::Item>],
    out: &mut Vec<rustc_span::Span>,
) {
    for item in items {
        if let rustc_ast::ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(inner, _, _, _)) =
            &item.kind
        {
            collect_fn_spans(inner, out);
            continue;
        }
        if matches!(item.kind, rustc_ast::ItemKind::Fn(_)) {
            out.push(item_span_with_attrs(item));
        }
    }
}

/// **THE SWITCHOVER ARTIFACT'S PRINTER — one implementation, two krates.**
///
/// Extracted from [`substituted_source`] so the *transformed* krate can reach
/// the same splice. The alternative was a second copy of this loop, which is the
/// duplicate-implementation hazard phase 4 spent two rounds measuring.
///
/// Reprints every function through `pprust` and splices those reprints into the
/// ORIGINAL file text. Two consequences follow from that and are load-bearing
/// for the golden batch:
///
/// - text **outside** a function span survives **verbatim** (file-level
///   comments, `extern` blocks, inner attributes);
/// - text **inside** a function span is normalized, so comments in bodies are
///   dropped by `pprust`.
/// **Per-file emission (A1, revived by ruling 2026-08-18).**
///
/// Groups every reprint by the source file its span lives in and splices each
/// file's edits into that file's own text, with that file's own `start_pos` as
/// the offset base. The previous shape picked `spans.first()`'s file and
/// spliced EVERY reprint into it — correct on a single-file crate and a wrong
/// program on any other.
///
/// ⚠ **Why this exists when the corpus does not need it.** All 20 corpus
/// programs are single crate-source file (C-20), so this changes no corpus
/// byte. It exists because the verify loop's own end-to-end witnesses are
/// multi-file, and they are the only witnesses that the loop reverts a bad
/// rewrite while keeping a good one. C-20's retirement check scoped the corpus
/// and not the witness population — the correction is recorded there.
pub(crate) fn splice_fn_prints_per_file(
    tcx: TyCtxt<'_>,
    krate: &rustc_ast::Crate,
    edited: Option<&[rustc_span::Span]>,
) -> (
    std::collections::BTreeMap<super::plan::FileKey, String>,
    SubstStats,
    // **I-31**: per-file emitted→original line translation. `pprust` reprints
    // whole functions, so this layer's line numbers drift from the original's —
    // measured at −36 on libtree. Built from the SAME edit vector spliced below.
    std::collections::BTreeMap<super::plan::FileKey, super::apply::LineMap>,
) {
    let mut spans = Vec::new();
    collect_fn_spans(&krate.items, &mut spans);
    let mut printed: Vec<(rustc_span::Span, String)> = Vec::new();
    collect_fn_prints(&krate.items, &mut printed);
    // wave-6f: a struct or impl item is reprinted only when a field transaction
    // claimed an edit inside it; the parity instrument's reprint-all path never
    // sees one.
    if let Some(edited) = edited {
        collect_item_prints_containing(&krate.items, edited, &mut printed);
    }
    // A raw-boundary surface replacement deliberately represents one original
    // function span with TWO printed items: raw outer first, safe inner second.
    // Collapse that pair into one splice. No unrelated duplicate span is
    // absorbed: the safe-inner name is the type marker for this one sanctioned
    // shape.
    let mut surface_combined: Vec<(rustc_span::Span, String)> = Vec::new();
    for (span, text) in printed {
        if let Some((previous_span, previous_text)) = surface_combined.last_mut()
            && *previous_span == span
            && (text.contains("fn __crat_safe_") || text.contains("fn __crat_raw_"))
        {
            previous_text.push('\n');
            previous_text.push_str(&text);
        } else {
            surface_combined.push((span, text));
        }
    }
    let mut printed = surface_combined;
    // **SPLICE ONLY WHAT CHANGED** (fix ruling, 2026-08-18). Reprinting an
    // untouched function normalizes its spacing and DROPS its interior
    // comments — a defect against byte preservation for untransformed code,
    // measured at `reverting_every_function_reproduces_the_substrate`.
    //
    // The predicate is containment against the transform's OWN claim records.
    // Deriving "changed" by comparing reprint text to the original was
    // explicitly forbidden: it would call a function unchanged exactly when the
    // reprint happens to be canonical, which is the vacuity that nearly hid
    // this defect in the first place.
    // `None` means REPRINT ALL, and it has exactly one caller: the parity
    // instrument, whose whole purpose is canonicalizing every function before
    // a token comparison. Emission always passes `Some`.
    //
    // ⚠ **SEED BEFORE FILTERING.** The file map must carry every source file
    // that holds a function, whether or not that file has an edit — otherwise a
    // crate with no changes emits an EMPTY root file instead of the original.
    // That is not hypothetical: it broke `g09_pdrop_suppression`, whose input
    // and expected are byte-identical (I-12) and whose correct emission is
    // therefore the substrate unchanged.
    let seed: Vec<rustc_span::Span> = printed.iter().map(|(sp, _)| *sp).collect();
    if let Some(edited) = edited {
        printed.retain(|(sp, _)| edited.iter().any(|e| sp.contains(*e)));
    }

    let sm = tcx.sess.source_map();
    let mut s = SubstStats {
        nested: 0,
        unrenderable: 0,
        span_starts_at_attr: 0,
        files_with_edits: 0,
    };
    // Containment: a function span that strictly contains another's.
    for a in &spans {
        if spans
            .iter()
            .any(|b| b != a && a.contains(*b) && (a.lo() != b.lo() || a.hi() != b.hi()))
        {
            s.nested += 1;
        }
    }

    // Edits bucketed BY FILE. A span whose file has no source text, or whose
    // name does not map to a `FileKey`, is unrenderable — counted, never
    // silently spliced into a neighbouring file, which is precisely the defect
    // the single-file shape had.
    let mut per_file: std::collections::BTreeMap<
        super::plan::FileKey,
        (String, rustc_span::BytePos, Vec<(usize, usize, String)>),
    > = std::collections::BTreeMap::new();
    for sp in &seed {
        let file = sm.lookup_source_file(sp.lo());
        if let (Some(src), Some(key)) = (file.src.as_ref(), super::file_key(&file.name)) {
            per_file
                .entry(key)
                .or_insert_with(|| (src.to_string(), file.start_pos, Vec::new()));
        }
    }
    for (sp, text) in &printed {
        let file = sm.lookup_source_file(sp.lo());
        let (Some(_src), Some(key)) = (file.src.as_ref(), super::file_key(&file.name)) else {
            s.unrenderable += 1;
            continue;
        };
        let Some(slot) = per_file.get_mut(&key) else {
            s.unrenderable += 1;
            continue;
        };
        match sm.span_to_snippet(*sp) {
            Ok(orig) => {
                if orig.trim_start().starts_with('#') {
                    s.span_starts_at_attr += 1;
                }
                let lo = (sp.lo() - slot.1).0 as usize;
                let hi = (sp.hi() - slot.1).0 as usize;
                slot.2.push((lo, hi, text.clone()));
            }
            Err(_) => s.unrenderable += 1,
        }
    }

    s.files_with_edits = per_file.values().filter(|(_, _, e)| !e.is_empty()).count();

    let mut out = std::collections::BTreeMap::new();
    let mut maps = std::collections::BTreeMap::new();
    for (key, (src, _base, mut edits)) in per_file {
        // Back-to-front, exactly as `apply` does: offsets address the ORIGINAL.
        edits.sort_by_key(|(lo, _, _)| std::cmp::Reverse(*lo));
        // **The map is built from the edits that will be APPLIED**, before the
        // loop consumes them, and from the ORIGINAL text they address.
        let applied: Vec<(usize, usize, String)> = edits
            .iter()
            .filter(|(lo, hi, _)| lo <= hi && *hi <= src.len())
            .cloned()
            .collect();
        maps.insert(
            key.clone(),
            super::apply::LineMap::from_splices(&src, &applied),
        );
        let mut text = src;
        for (lo, hi, replacement) in edits {
            if lo <= hi && hi <= text.len() {
                text.replace_range(lo..hi, &replacement);
            } else {
                s.unrenderable += 1;
            }
        }
        out.insert(key, text);
    }
    (out, s, maps)
}

#[cfg(test)]
/// **The root file alone**, for callers that emit one text: the string entry,
/// the goldens, and the parity gates. Selects by `spans.first()`'s file — the
/// same rule the pre-A1 shape used — so single-file callers are byte-identical
/// to before.
pub(crate) fn splice_fn_prints(
    tcx: TyCtxt<'_>,
    krate: &rustc_ast::Crate,
    edited: Option<&[rustc_span::Span]>,
) -> (String, SubstStats) {
    let mut spans = Vec::new();
    collect_fn_spans(&krate.items, &mut spans);
    let root = spans
        .first()
        .map(|sp| tcx.sess.source_map().lookup_source_file(sp.lo()))
        .and_then(|f| super::file_key(&f.name));
    let (files, s, _) = splice_fn_prints_per_file(tcx, krate, edited);
    let text = root
        .and_then(|key| files.get(&key).cloned())
        .unwrap_or_default();
    (text, s)
}

/// wave-6f: struct and impl items that contain an edited span.
pub(crate) fn collect_item_prints_containing(
    items: &[rustc_ast::ptr::P<rustc_ast::Item>],
    edited: &[rustc_span::Span],
    out: &mut Vec<(rustc_span::Span, String)>,
) {
    use rustc_ast_pretty::pprust;
    for item in items {
        if let rustc_ast::ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(inner, _, _, _)) =
            &item.kind
        {
            collect_item_prints_containing(inner, edited, out);
            continue;
        }
        if !matches!(
            item.kind,
            rustc_ast::ItemKind::Struct(..) | rustc_ast::ItemKind::Impl(..)
        ) {
            continue;
        }
        let span = item_span_with_attrs(item);
        if span.from_expansion() || !edited.iter().any(|e| span.contains(*e)) {
            continue;
        }
        out.push((span, pprust::item_to_string(item)));
    }
}

pub(crate) fn collect_fn_prints(
    items: &[rustc_ast::ptr::P<rustc_ast::Item>],
    out: &mut Vec<(rustc_span::Span, String)>,
) {
    use rustc_ast_pretty::pprust;
    for item in items {
        if let rustc_ast::ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(inner, _, _, _)) =
            &item.kind
        {
            collect_fn_prints(inner, out);
            continue;
        }
        if matches!(item.kind, rustc_ast::ItemKind::Fn(_)) {
            out.push((item_span_with_attrs(item), pprust::item_to_string(item)));
        }
    }
}
