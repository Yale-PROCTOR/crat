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

use rustc_data_structures::unord::UnordSet;
use rustc_hir::HirId;
use rustc_middle::ty::TyCtxt;

/// **PHASE 1's GATE — idempotence on the print path**, per FUNCTION.
///
/// The frozen-substrate correction (user, 2026-08-12) narrowed this from a
/// whole-crate reprint to exactly what the emission model does: an emitted
/// function carries printer output, and every other byte in the file is the
/// substrate's. So the property that has to hold is
/// `print(parse(print(f))) == print(f)` for a function item — not for a crate.
///
/// **Why it gates.** If printing is not a fixed point, then two rounds of the
/// verify loop over the same unchanged function produce different bytes, and
/// every downstream comparison — parity differentials, golden anchors, the
/// revert/no-revert distinction — is measuring the printer instead of the
/// rewrite.
///
/// A function that fails to REPARSE counts as non-idempotent and is named. That
/// is the stronger reading and the right one: text this pipeline emits but
/// cannot itself read back is not a fixed point in any useful sense.
#[derive(Default)]
pub(crate) struct IdemStats {
    pub functions: usize,
    pub stable: usize,
    /// Function names whose print is not a fixed point — **capped**, for the
    /// artifact. Never the count: see [`Self::unstable_count`].
    pub unstable: Vec<String>,
    /// Functions whose printed text did not reparse at all — **capped**.
    pub unparseable: Vec<String>,
    /// The UNCAPPED counts. Split from the name lists because reporting a
    /// capped `Vec::len()` as a measurement makes every population read as the
    /// cap.
    pub unstable_count: usize,
    pub unparseable_count: usize,
}

#[cfg(test)]
fn idempotence_over(krate: &rustc_ast::Crate, tcx: TyCtxt<'_>) -> IdemStats {
    let mut s = IdemStats::default();
    walk_items(&krate.items, tcx, &mut s);
    s
}

/// **RECURSES INTO MODULES**, and that is not a detail.
///
/// The first version of this walk iterated `krate.items` alone and measured
/// **zero functions on all 20 programs**: every corpus function lives inside
/// nested modules — `src::avl::height` is `mod src { mod avl { fn height } }`,
/// which is what c2rust emits for a single-file crate. The gate reported
/// `0 functions / 0 stable`: **vacuous, not passing.**
///
/// It was caught only because the census reports the **denominator** beside the
/// rate. A rate alone would have read as a total failure or been waved off as a
/// glitch, and a uniformly-zero predicate would have shipped as a green gate.
/// Same shape as the corpus-empty `addr-taken` arm and the RED-weakening trap:
/// **a measurement whose population is zero has not passed anything.**
#[cfg(test)]
fn walk_items(items: &[rustc_ast::ptr::P<rustc_ast::Item>], tcx: TyCtxt<'_>, s: &mut IdemStats) {
    use rustc_ast_pretty::pprust;
    for item in items {
        if let rustc_ast::ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(inner, _, _, _)) =
            &item.kind
        {
            walk_items(inner, tcx, s);
            continue;
        }
        if !matches!(item.kind, rustc_ast::ItemKind::Fn(_)) {
            continue;
        }
        s.functions += 1;
        let name = item
            .kind
            .ident()
            .map_or_else(|| "<anon>".to_owned(), |i| i.to_string());
        let t1 = pprust::item_to_string(item);
        // **A UNIQUE FILE NAME PER PARSE, and it is load-bearing.**
        //
        // `utils::ast::new_parser_from_str` hardcodes `FileName::Custom(
        // "main.rs")`, and `SourceMap::new_source_file` dedupes on a stable id
        // derived from that name — so the second and every later parse in one
        // session get back the FIRST function's source file. The measurement
        // then compares every function against function #1 and reports
        // "1 stable per program", which is precisely what it did: 1 in avl
        // (9 fns) and 1 in brotli (867 fns), in all 20 programs.
        //
        // A shared helper cannot be fixed from here — `crates/utils` is outside
        // this crate's boundary — so the parser is built locally with a
        // per-item name.
        let fname = rustc_span::FileName::Custom(format!("idem-{}.rs", s.functions));
        let Ok(mut parser) =
            rustc_parse::new_parser_from_source_str(&tcx.sess.psess, fname, t1.clone())
        else {
            if s.unparseable.len() < 20 {
                s.unparseable.push(name);
            }
            continue;
        };
        match parser.parse_crate_mod() {
            Ok(k2) => {
                let t2 = k2
                    .items
                    .iter()
                    .map(|i| pprust::item_to_string(i))
                    .collect::<Vec<_>>()
                    .join("\n");
                if t2.trim() == t1.trim() {
                    s.stable += 1;
                } else {
                    // COUNT and NAMES are separate: the names list is capped
                    // for the artifact, the count is not. Reporting
                    // `unstable.len()` as the count made every program read
                    // exactly 20 — the cap, wearing a measurement's clothes.
                    s.unstable_count += 1;
                    if s.unstable.len() < 20 {
                        s.unstable.push(name);
                    }
                }
            }
            Err(diag) => {
                // Cancelled, not emitted: this is a MEASUREMENT, and a probe
                // that reports through the diagnostic stream would contaminate
                // the verify loop's own attribution.
                diag.cancel();
                s.unparseable_count += 1;
                if s.unparseable.len() < 20 {
                    s.unparseable.push(name);
                }
            }
        }
    }
}

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

/// One subject's bridge status.
pub(crate) struct BridgeRow {
    pub fn_path: String,
    pub mir_local: u32,
    pub is_param: bool,
    /// `true` when the subject carries an emitting decision — the population
    /// the phase-2 bar is stated over.
    pub decided: bool,
    /// Is the subject's binding `HirId` in the image of the AST→HIR map?
    pub hir_resolved: bool,
    /// Is the subject's owning function in the image of the global map?
    pub fn_resolved: bool,
}

/// **PHASE 2's BAR.** For every subject, can the AST walk reach the node the
/// decision is keyed to?
///
/// Pre-stated bar (user ruling, 2026-08-12): **100 % resolution on decision
/// keys of the DECIDED population.** A miss there is blocking — a decided
/// subject whose node cannot be found is a subject the new layer cannot emit,
/// which is a silent ledger movement. Misses outside the decided population are
/// priced findings: they cost nothing today and price a future capability.
///
/// **Must be called before any HIR/MIR query** — see the module doc.
///
/// Returns `Err` with the panic's message if the mapper aborts, so that a
/// program whose correspondence the mapper rejects is reported rather than
/// crashing the sweep.
#[cfg(test)]
pub(crate) fn census(tcx: TyCtxt<'_>) -> Result<(Vec<BridgeRow>, IdemStats), String> {
    // FIRST, before anything touches HIR. `catch_unwind` covers the mapping,
    // not the decision phase: a decision-phase panic is a real defect and must
    // not be swallowed here.
    // ONE `expanded_ast` call, shared. A second would panic: `make_ast_to_hir`
    // below builds the HIR, and `expanded_ast` clones a resolver that lowering
    // consumes. Phase 1's gate and phase 2's bar therefore ride the same
    // capture rather than each taking their own.
    let mapped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut krate = ::utils::ast::expanded_ast(tcx);
        let idem = idempotence_over(&krate, tcx);
        let map = ::utils::ast::make_ast_to_hir(&mut krate, tcx);
        // `NodeMap` is rustc's `UnordMap`, which hides `values()`/`iter()` on
        // purpose so nondeterministic iteration cannot leak into compiler
        // output. Membership is order-free, so `UnordSet` is the right
        // container and `From<UnordItems>` is the supported construction.
        let hir_image: UnordSet<HirId> = map.local_map.items().map(|(_, v)| *v).into();
        let fn_image: UnordSet<rustc_span::def_id::LocalDefId> =
            map.global_map.items().map(|(_, v)| *v).into();
        (hir_image, fn_image, idem)
    }));
    let (hir_image, fn_image, idem) = match mapped {
        Ok(pair) => pair,
        Err(payload) => {
            let msg = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_else(|| "<non-string panic payload>".to_owned());
            return Err(msg);
        }
    };

    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    let rows = table
        .entries
        .iter()
        .map(|(subject, decision)| BridgeRow {
            fn_path: tcx.def_path_str(subject.fn_did.to_def_id()),
            mir_local: subject.local.as_u32(),
            is_param: matches!(subject.kind, super::decision::SubjectKind::Param { .. }),
            // EXHAUSTIVE, not `matches!` — the import denylist rejects the
            // bypass shape, and it is right to: the bar is stated over the
            // DECIDED population, so a new emitting disposition that this
            // census silently counted as degraded would understate the very
            // number the phase gates on.
            decided: match decision {
                super::decision::Decision::Ref { .. }
                | super::decision::Decision::Slice { .. }
                | super::decision::Decision::Opt { .. } => true,
                super::decision::Decision::Degraded(_) => false,
            },
            hir_resolved: hir_image.contains(&subject.hir_id),
            fn_resolved: fn_image.contains(&subject.fn_did),
        })
        .collect();
    Ok((rows, idem))
}

/// The census as a TSV artifact, for the corpus sweep.
#[cfg(test)]
pub(crate) fn census_tsv(tcx: TyCtxt<'_>) -> String {
    let mut out =
        String::from("fn_path\tmir_local\tis_param\tdecided\thir_resolved\tfn_resolved\n");
    match census(tcx) {
        Ok((rows, idem)) => {
            // Phase 1's gate rides the same artifact as phase 2's bar, on one
            // header line, because they share one AST capture and separating
            // them into two files would let a consumer read one at a vintage
            // the other was not measured at.
            out.push_str(&format!(
                "<idempotence>\t{}\t{}\t{}\t{}\t{}\n",
                idem.functions,
                idem.stable,
                idem.unstable_count,
                idem.unparseable_count,
                idem.unstable
                    .iter()
                    .chain(idem.unparseable.iter())
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(","),
            ));
            for r in rows {
                out.push_str(&format!(
                    "{}\t{}\t{}\t{}\t{}\t{}\n",
                    r.fn_path,
                    r.mir_local,
                    u8::from(r.is_param),
                    u8::from(r.decided),
                    u8::from(r.hir_resolved),
                    u8::from(r.fn_resolved),
                ));
            }
        }
        // A declined census is REPORTED in the artifact, never an empty file:
        // an empty file and a total mapping failure are different facts, and
        // the bar must not read the second as the first.
        Err(why) => out.push_str(&format!(
            "<declined>\t0\t0\t0\t0\t0\t{}\n",
            why.replace(['\t', '\n', '\r'], " ")
        )),
    }
    out
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
    pub functions: usize,
    /// Function spans that CONTAIN another function's span. Must be 0, or
    /// function-granular substitution is not non-overlapping after all.
    pub nested: usize,
    /// Spans whose original text could not be recovered — substitution would be
    /// guessing, so it is refused and counted.
    pub unrenderable: usize,
    /// Does `item.span` include the outer attributes? Measured, not assumed:
    /// substituting a span that excludes them duplicates every `#[no_mangle]`.
    pub span_starts_at_attr: usize,
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

/// Build the substituted source for the crate's single root file, plus the
/// findings above. Returns `Err` when the AST capture itself is refused.
#[cfg(test)]
pub(crate) fn substituted_source(tcx: TyCtxt<'_>) -> Result<(String, SubstStats), String> {
    let mapped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let krate = ::utils::ast::expanded_ast(tcx);
        splice_fn_prints(tcx, &krate)
    }));
    mapped.map_err(|_| "AST capture panicked".to_owned())
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
) -> (
    std::collections::BTreeMap<super::plan::FileKey, String>,
    SubstStats,
) {
    let mut spans = Vec::new();
    collect_fn_spans(&krate.items, &mut spans);
    let mut printed: Vec<(rustc_span::Span, String)> = Vec::new();
    collect_fn_prints(&krate.items, &mut printed);

    let sm = tcx.sess.source_map();
    let mut s = SubstStats {
        functions: printed.len(),
        nested: 0,
        unrenderable: 0,
        span_starts_at_attr: 0,
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
    for (sp, text) in &printed {
        let file = sm.lookup_source_file(sp.lo());
        let (Some(src), Some(key)) = (file.src.as_ref(), super::file_key(&file.name)) else {
            s.unrenderable += 1;
            continue;
        };
        let slot = per_file
            .entry(key)
            .or_insert_with(|| (src.to_string(), file.start_pos, Vec::new()));
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

    let mut out = std::collections::BTreeMap::new();
    for (key, (src, _base, mut edits)) in per_file {
        // Back-to-front, exactly as `apply` does: offsets address the ORIGINAL.
        edits.sort_by_key(|(lo, _, _)| std::cmp::Reverse(*lo));
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
    (out, s)
}

/// **The root file alone**, for callers that emit one text: the string entry,
/// the goldens, and the parity gates. Selects by `spans.first()`'s file — the
/// same rule the pre-A1 shape used — so single-file callers are byte-identical
/// to before.
pub(crate) fn splice_fn_prints(tcx: TyCtxt<'_>, krate: &rustc_ast::Crate) -> (String, SubstStats) {
    let mut spans = Vec::new();
    collect_fn_spans(&krate.items, &mut spans);
    let root = spans
        .first()
        .map(|sp| tcx.sess.source_map().lookup_source_file(sp.lo()))
        .and_then(|f| super::file_key(&f.name));
    let (files, s) = splice_fn_prints_per_file(tcx, krate);
    let text = root
        .and_then(|key| files.get(&key).cloned())
        .unwrap_or_default();
    (text, s)
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
