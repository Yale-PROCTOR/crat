//! §NB3-3c-i — signature-origin inference (compute-only; NOT yet injected into the borrow replay).
//!
//! Thin-reuse architecture (ruled 2026-07-11): derive origin relations from production
//! `lifetime_flow`'s signature-granularity value-flow summaries, wrapped **read-only** behind the
//! single call site `derive_signature_flows` (isolation requirement). `OriginSummary` is the only
//! interface the rest of BO sees. **NB5-O is NOT a body-only swap** (corrected after the 3c-i
//! adversarial review): `OriginSummary` still uses production slot types (`LifetimeSlot` /
//! `SignatureSlot`) and `derive_signature_flows` returns `LifetimeFlowResults`, so retiring
//! `lifetime_flow` at NB5-O replaces the derivation body AND those interface/return types with
//! BO-owned index/place/slot types — with the production→BO conversion kept behind this one adapter.
//! Scoped (the isolation still holds — one call site + one type boundary), but not drop-in; gated on
//! a corpus differential.
//!
//! What this adds over the reused summaries: (1) a **transitively-correct** subset closure (the
//! production `subset_closure` is 1-hop — D3, diagnostic-only, never reused); (2) `unknown` carried
//! for 3c-ii candidacy demotion (production's conflict path never consumes the analogous
//! `unknown_targets` — a fork-only soundness win). Origin inference is kind-independent and runs
//! ONCE per program; `ORIGIN_WRAP_COUNT` (counting ORIGINS' wrap, not the underlying lifetime-flow
//! call) backs the runs-once invariant.

use std::cell::Cell;

use rustc_index::{
    Idx,
    bit_set::{DenseBitSet, SparseBitMatrix},
};

use crate::analyses::borrow::lifetime_flow::{self, LifetimeFlowResults, LifetimeSlot};
use crate::utils::rustc::RustProgram;

use super::origin_summary::{OriginSummaries, OriginSummary};

thread_local! {
    /// Per-thread count of `compute_origins` invocations (one increment per call), NOT the underlying
    /// lifetime-flow derivation. Backs the "origin inference runs once per program, kind-independent"
    /// invariant. **THREAD-LOCAL, not a global atomic:** compiler test sessions run on separate
    /// threads with thread-local rustc session globals, so compute_origins calls from concurrent tests
    /// race a global counter; the runs-once test measures this counter's delta around a single driver
    /// call, all on one callback thread, where a thread-local delta is exact.
    pub(crate) static ORIGIN_WRAP_COUNT: Cell<usize> = const { Cell::new(0) };
}

/// The ONE derivation call site (isolation requirement). NB5-O replaces this body's derivation AND
/// its `LifetimeFlowResults` return with a BO-native origin derivation over BO-owned types; downstream
/// keys off `OriginSummary`, whose field types (`LifetimeSlot`/`SignatureSlot`) are ALSO swapped to
/// BO-owned at that point (not a body-only change — 3c-i review). At 3c-ii injection this should
/// consume the ctxt's already
/// computed `lifetime_flows` (`GBorrowInferCtxt`, `pub`) rather than recompute — no double-compute.
fn derive_signature_flows(program: &RustProgram<'_>) -> LifetimeFlowResults {
    lifetime_flow::analyze_program_lifetime_flow(program)
}

/// Whole-program signature-origin summaries. Computed once, kind-independent.
pub(crate) fn compute_origins(program: &RustProgram<'_>) -> OriginSummaries {
    ORIGIN_WRAP_COUNT.with(|c| c.set(c.get() + 1));
    derive_signature_flows(program)
        .into_iter()
        .map(|(f, result)| {
            let summary = result.summary;
            let n = summary.slots.len();
            // `subset` = closure(value_flows ∪ storage_aliases). `closed()` fuses storage into
            // value_flows at BODY granularity, but `to_summary()` re-projects value_flow targets
            // through an `observable_value_target` filter (lifetime_flow.rs:758) that DROPS some
            // argument depth-0 targets, while `storage_aliases` is retained UNFILTERED (:774). So the
            // summary's `value_flows` is NOT a superset of `storage_aliases` — a symmetric storage
            // direction to a non-observable arg slot lives only in `storage_aliases` (Codex 3c-i
            // re-review; witness `&raw mut p`: value has arg1@0→return@1, storage the return@1→arg1@0).
            // Unioning `storage_aliases` back in BEFORE closing restores the complete relation in one
            // matrix (no separate storage field). The union is not pre-closed across value↔storage
            // chains, so `transitive_closure` below does real work (and is guarded directly).
            let mut combined = summary.value_flows;
            for src in summary.storage_aliases.rows() {
                if let Some(tgts) = summary.storage_aliases.row(src) {
                    for tgt in tgts.iter() {
                        combined.insert(src, tgt);
                    }
                }
            }
            let subset = transitive_closure(&combined, n);
            (
                f,
                OriginSummary {
                    slots: summary.slots,
                    subset,
                    unknown: summary.unknown_targets,
                },
            )
        })
        .collect()
}

/// Correct multi-hop transitive closure of `value_flows` (edge `source → target` means
/// `source`'s origin flows into `target`'s). `answer.contains(sub, sup)` ⇔ `sub` reaches `sup`.
/// This is the transitively-correct closure the production `subset_closure` (1-hop, D3) is not —
/// note line: successors are taken from the POPPED node, never the root.
fn transitive_closure(
    value_flows: &SparseBitMatrix<LifetimeSlot, LifetimeSlot>,
    n_slots: usize,
) -> SparseBitMatrix<LifetimeSlot, LifetimeSlot> {
    let mut answer = SparseBitMatrix::new(n_slots);
    let mut stack: Vec<LifetimeSlot> = vec![];
    let mut visited: DenseBitSet<LifetimeSlot> = DenseBitSet::new_empty(n_slots);
    for root in (0..n_slots).map(LifetimeSlot::new) {
        stack.clear();
        visited.clear();
        if let Some(succs) = value_flows.row(root) {
            stack.extend(succs.iter());
        }
        while let Some(node) = stack.pop() {
            if !visited.insert(node) {
                continue;
            }
            answer.insert(root, node);
            if let Some(succs) = value_flows.row(node) {
                stack.extend(succs.iter());
            }
        }
    }
    answer
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyses::borrow::lifetime_flow::{SignatureRoot, SignatureSlot};
    use rustc_hash::FxHashMap;
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::ty::TyCtxt;

    fn build_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = vec![];
        let mut structs = vec![];
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        RustProgram { tcx, functions, structs }
    }

    fn format_slot(slot: SignatureSlot) -> String {
        let root = match slot.place.root {
            SignatureRoot::Return => "return".to_string(),
            SignatureRoot::Arg(local) => format!("arg{}", local.index()),
        };
        let derefs = "*".repeat(slot.place.deref_depth as usize);
        let field = slot
            .place
            .field
            .map(|f| format!(".field{}", f.field_index))
            .unwrap_or_default();
        format!("{root}{derefs}{field}@{}", slot.depth)
    }

    struct Facts {
        subset: Vec<(String, String)>,
        unknown: Vec<String>,
    }

    fn origin_facts(code: &str) -> FxHashMap<String, Facts> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = build_program(tcx);
            let summaries = compute_origins(&program);
            let mut out = FxHashMap::default();
            for &f in &program.functions {
                let s = &summaries[&f];
                let edges = |m: &rustc_index::bit_set::SparseBitMatrix<LifetimeSlot, LifetimeSlot>| {
                    let mut v = vec![];
                    for sub in m.rows() {
                        if let Some(sups) = m.row(sub) {
                            for sup in sups.iter() {
                                v.push((format_slot(s.slots[sub]), format_slot(s.slots[sup])));
                            }
                        }
                    }
                    v.sort();
                    v
                };
                let mut unknown: Vec<String> =
                    s.unknown.iter().map(|slot| format_slot(s.slots[slot])).collect();
                unknown.sort();
                out.insert(
                    tcx.item_name(f.to_def_id()).to_string(),
                    Facts { subset: edges(&s.subset), unknown },
                );
            }
            out
        })
        .unwrap()
    }

    fn has(edges: &[(String, String)], sub: &str, sup: &str) -> bool {
        edges.iter().any(|(a, b)| a == sub && b == sup)
    }

    /// RED: a callee that returns its arg ⇒ the return origin ⊇ the arg origin.
    #[test]
    fn nb3_id_flow_through() {
        let facts = origin_facts("unsafe fn id(p: *mut i32) -> *mut i32 { p }");
        let f = &facts["id"];
        assert!(
            has(&f.subset, "arg1@0", "return@0"),
            "id: arg1@0 → return@0 expected in origin subset; got {:?}",
            f.subset
        );
    }

    /// RED: mutual recursion — the SCC fixpoint must converge with each fn's return ⊇ its arg.
    #[test]
    fn nb3_mutual_recursion_fixpoint() {
        // Terminating mutual recursion (base case) — a non-terminating a→b→a never returns, so its
        // return flow is (correctly) empty; the base case makes arg⇒return real and exercises the SCC.
        let facts = origin_facts(
            "unsafe fn a(p: *mut i32, n: i32) -> *mut i32 { if n == 0 { p } else { b(p, n - 1) } }\n\
             unsafe fn b(p: *mut i32, n: i32) -> *mut i32 { if n == 0 { p } else { a(p, n - 1) } }",
        );
        assert!(
            has(&facts["a"].subset, "arg1@0", "return@0"),
            "a: arg1@0 → return@0 expected; got {:?}",
            facts["a"].subset
        );
        assert!(
            has(&facts["b"].subset, "arg1@0", "return@0"),
            "b: arg1@0 → return@0 expected; got {:?}",
            facts["b"].subset
        );
    }

    /// RED: an opaque (extern) callee poisons the flowed-through origins.
    #[test]
    fn nb3_unknown_callee_poisons() {
        let facts = origin_facts(
            "unsafe extern \"C\" { fn ext(p: *mut i32) -> *mut i32; }\n\
             unsafe fn f(p: *mut i32) -> *mut i32 { ext(p) }",
        );
        assert!(
            !facts["f"].unknown.is_empty(),
            "f: opaque callee ext must poison at least one origin; unknown was empty"
        );
    }

    /// NEGATIVE CONTROL (req 4): a KNOWN callee (boundary-table pointer method) must NOT poison —
    /// poisoning that fires on everything passes the positive test and silently destroys precision.
    #[test]
    fn nb3_known_callee_no_poison() {
        let facts = origin_facts("unsafe fn f(p: *mut i32) -> *mut i32 { p.offset(1) }");
        assert!(
            facts["f"].unknown.is_empty(),
            "f: known provenance-preserving method `.offset` must NOT poison; got {:?}",
            facts["f"].unknown
        );
    }

    /// RED: `*dst = src` — src's origin flows into arg0's storage (output-param shape).
    #[test]
    fn nb3_arg_into_arg0_storage_flow() {
        let facts =
            origin_facts("unsafe fn f(dst: *mut *mut i32, src: *mut i32) { *dst = src; }");
        let f = &facts["f"];
        // src (arg2@0) flows into dst's pointee (arg1@1 — the store `*dst = src`); the deref is
        // captured in the slot depth, and this output-param flow lands in the same subset seam
        // `depth0_value_flows` feeds.
        assert!(
            has(&f.subset, "arg2@0", "arg1@1"),
            "f: arg2@0 (src) → arg1@1 (dst pointee) expected in subset; got {:?}",
            f.subset
        );
    }

    /// SYMMETRIC storage alias folds into `subset` (corrected 2026-07-11 after the 3c-i adversarial
    /// review). `lifetime_flow`'s `closed()` unions the symmetric `storage_aliases` into `value_flows`
    /// (lifetime_flow.rs:678-680) BEFORE the summary, so both directions of a `*mut *mut` forwarding
    /// alias (`arg1@1 ↔ return@1`) land in `subset` — there is no separate `storage` field and no
    /// lost direction (the earlier "carry storage separately" concern was moot). Asserting BOTH
    /// directions in `subset` is exactly what pins that the symmetric relation survives the fold.
    #[test]
    fn nb3_storage_alias_symmetric() {
        let facts =
            origin_facts("unsafe fn forward(out: *mut *mut i32) -> *mut *mut i32 { out }");
        let f = &facts["forward"];
        assert!(
            has(&f.subset, "arg1@1", "return@1"),
            "forward: arg1@1 → return@1 (folded storage alias) expected in subset; got {:?}",
            f.subset
        );
        assert!(
            has(&f.subset, "return@1", "arg1@1"),
            "forward: return@1 → arg1@1 (the symmetric direction, folded into subset) expected; got {:?}",
            f.subset
        );
    }

    /// 3-NODE-CHAIN closure (req 2026-07-11): a→b→c ⇒ a→c — the exact test whose absence let the
    /// D3 1-hop bug survive in production `subset_closure`. `*a=*b; *b=*c` gives value-flows
    /// arg3@1→arg2@1→arg1@1; a correct multi-hop closure MUST yield arg3@1→arg1@1 (a 1-hop closure
    /// would miss it). Pins the "successors from the POPPED node, not the seed" fix forever.
    #[test]
    fn nb3_transitive_closure_three_node_chain() {
        let facts = origin_facts(
            "unsafe fn chain(a: *mut *mut i32, b: *mut *mut i32, c: *mut *mut i32) { \
             *a = *b; *b = *c; }",
        );
        let f = &facts["chain"];
        assert!(
            has(&f.subset, "arg3@1", "arg1@1"),
            "chain: arg3@1 → arg1@1 must hold transitively (arg3@1→arg2@1→arg1@1); a 1-hop closure \
             misses it; got {:?}",
            f.subset
        );
    }

    /// DIRECT guard for the multi-hop `transitive_closure` (Codex 3c-i re-review). The end-to-end
    /// three-node fixture above is vacuous for THIS function: `lifetime_flow`'s summary is already
    /// transitively closed, so a 1-hop or no-op closure still passes it. This feeds a synthetic,
    /// NOT-pre-closed matrix (only A→B and B→C) and asserts the transitive A→C — which a 1-hop closure
    /// (successors taken from the seed, not the popped node) would miss. This is the real guard for the
    /// closure the NB5-O BO-native (un-closed) input will depend on.
    #[test]
    fn transitive_closure_multi_hop_from_synthetic() {
        let mut m: SparseBitMatrix<LifetimeSlot, LifetimeSlot> = SparseBitMatrix::new(3);
        let (a, b, c) = (LifetimeSlot::new(0), LifetimeSlot::new(1), LifetimeSlot::new(2));
        m.insert(a, b);
        m.insert(b, c);
        let closed = transitive_closure(&m, 3);
        let reaches = |x: LifetimeSlot, y: LifetimeSlot| closed.row(x).is_some_and(|r| r.iter().any(|z| z == y));
        assert!(reaches(a, c), "A→C must hold transitively (A→B→C); a 1-hop closure misses it");
        assert!(reaches(a, b) && reaches(b, c), "direct A→B and B→C must hold");
    }

    /// Argument depth-0 storage symmetry regression (Codex 3c-i re-review). A storage alias whose
    /// target is a NON-observable argument depth-0 slot survives ONLY in `storage_aliases` —
    /// `to_summary()` drops it from `value_flows` via the `observable_value_target` filter. `&raw mut
    /// p` aliases the returned `*mut *mut` pointee storage with `p`'s address, so `subset` must carry
    /// BOTH directions — proving `compute_origins` unions `storage_aliases` in (not lost with the
    /// removed separate field).
    #[test]
    fn nb3_arg_depth0_storage_symmetry() {
        let facts =
            origin_facts("unsafe fn addr(mut p: *mut i32) -> *mut *mut i32 { &raw mut p }");
        let f = &facts["addr"];
        assert!(
            has(&f.subset, "arg1@0", "return@1") && has(&f.subset, "return@1", "arg1@0"),
            "addr: BOTH storage directions (arg1@0 ↔ return@1) must be in subset after the storage \
             union; got {:?}",
            f.subset
        );
    }
}
