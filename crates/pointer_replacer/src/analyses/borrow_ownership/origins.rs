//! BO-native signature-origin inference.
//!
//! NB5-O replaced the wrapped production `lifetime_flow` route with BO-owned slot types and
//! `origin_flow`. `OriginSummary` remains the only interface the rest of BO sees. The wrapped
//! derivation and its production→BO conversion remain compiled only in tests as the differential
//! oracle; production `analyses/borrow/` stays frozen for the rewriter.
//!
//! What this adds over the reused summaries: (1) a **transitively-correct** subset closure (the
//! production `subset_closure` is 1-hop — D3, diagnostic-only, never reused); (2) `unknown` carried
//! for candidacy demotion. Origin inference is kind-independent and runs ONCE per program;
//! `origin_flow::ORIGIN_DERIVATION_COUNT` backs the runs-once invariant.
//!
//! §NB3-3c-ii OUTCOME (2026-07-12): compute-only is where origins STAY on the BO path.
//! - **Depth-0 subset is NOT injected — proven redundant.** `nb3c_origins_subset_redundant_vs_depth0`
//!   shows every depth-0 origins subset edge (minus `unknown`) is already consumed by the fork via
//!   production's `depth0_value_flows` seam (fixtures + corpus: all `already`; closure/storage/
//!   genuinely-new = 0). So there is nothing to inject at depth-0 (deeper origins are the NB5-O harvest).
//! - **`unknown` candidacy demotion moves to NB4.** A blunt emission-time `¬ref` clause on
//!   opaque-poisoned slots was prototyped and REJECTED by adversarial review: `¬ref` still permits an
//!   unsound `Owning` on may-overwrite slots, and it misses direct-arg/field retention. The sound
//!   treatment is effect-dependent (may-overwrite vs may-supply vs pure-read) = NB4. The clause impl +
//!   retain-shape/negative-control witnesses are saved as an NB4 seed patch.

use rustc_index::{
    Idx, IndexVec,
    bit_set::{DenseBitSet, SparseBitMatrix},
};

#[cfg(test)]
use super::origin_summary::SignaturePlace;
use super::{
    crate_slots::CrateSlots,
    origin_flow,
    origin_summary::{OriginSlot, OriginSummaries, OriginSummary, SignatureRoot, SignatureSlot},
    solver::SlotRef,
};
#[cfg(test)]
use crate::analyses::borrow::lifetime_flow::{self, LifetimeFlowResults};
use crate::utils::rustc::RustProgram;

/// Test-only wrapped oracle at the single production→BO type boundary.
#[cfg(test)]
fn derive_signature_flows_wrapped(program: &RustProgram<'_>) -> LifetimeFlowResults {
    lifetime_flow::analyze_program_lifetime_flow(program)
}

#[cfg(test)]
fn wrapped_slot(slot: crate::analyses::borrow::lifetime_flow::SignatureSlot) -> SignatureSlot {
    let root = match slot.place.root {
        crate::analyses::borrow::lifetime_flow::SignatureRoot::Return => SignatureRoot::Return,
        crate::analyses::borrow::lifetime_flow::SignatureRoot::Arg(local) => {
            SignatureRoot::Arg(local)
        }
    };
    let field = slot.place.field.map(|field| super::slots::StructFieldSlot {
        struct_did: field.struct_did,
        field_index: field.field_index,
    });
    SignatureSlot {
        place: SignaturePlace {
            root,
            deref_depth: slot.place.deref_depth,
            field,
        },
        depth: slot.depth,
    }
}

fn build_origin_summary(
    slots: IndexVec<OriginSlot, SignatureSlot>,
    value_flows: &SparseBitMatrix<OriginSlot, OriginSlot>,
    storage_aliases: &SparseBitMatrix<OriginSlot, OriginSlot>,
    unknown: DenseBitSet<OriginSlot>,
) -> OriginSummary {
    let n = slots.len();
    let mut combined = SparseBitMatrix::new(n);
    for relation in [value_flows, storage_aliases] {
        for source in relation.rows() {
            if let Some(targets) = relation.row(source) {
                for target in targets.iter() {
                    combined.insert(source, target);
                }
            }
        }
    }
    OriginSummary {
        slots,
        subset: transitive_closure(&combined, n),
        unknown,
    }
}

/// Wrapped validation oracle converted at the single production→BO type boundary.
#[cfg(test)]
pub(crate) fn compute_origins_wrapped(program: &RustProgram<'_>) -> OriginSummaries {
    derive_signature_flows_wrapped(program)
        .into_iter()
        .map(|(f, result)| {
            let summary = result.summary;
            let n = summary.slots.len();
            let slots =
                IndexVec::from_raw(summary.slots.iter().copied().map(wrapped_slot).collect());
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
            let mut value_flows = SparseBitMatrix::new(n);
            for src in summary.value_flows.rows() {
                if let Some(tgts) = summary.value_flows.row(src) {
                    for tgt in tgts.iter() {
                        value_flows
                            .insert(OriginSlot::new(src.index()), OriginSlot::new(tgt.index()));
                    }
                }
            }
            let mut storage_aliases = SparseBitMatrix::new(n);
            for src in summary.storage_aliases.rows() {
                if let Some(tgts) = summary.storage_aliases.row(src) {
                    for tgt in tgts.iter() {
                        storage_aliases
                            .insert(OriginSlot::new(src.index()), OriginSlot::new(tgt.index()));
                    }
                }
            }
            let mut unknown = DenseBitSet::new_empty(n);
            for slot in summary.unknown_targets.iter() {
                unknown.insert(OriginSlot::new(slot.index()));
            }
            (
                f,
                build_origin_summary(slots, &value_flows, &storage_aliases, unknown),
            )
        })
        .collect()
}

/// NB5-O native derivation over BO-owned MIR-flow and signature-slot types.
pub(crate) fn compute_origins_native(program: &RustProgram<'_>) -> OriginSummaries {
    let flows = origin_flow::analyze_program_origin_flow(program);
    origin_summaries_from_flows(flows)
}

fn origin_summaries_from_flows(flows: origin_flow::OriginFlowResults) -> OriginSummaries {
    let summaries = flows
        .iter()
        .map(|(&f, result)| {
            let summary = &result.summary;
            (
                f,
                build_origin_summary(
                    summary.slots.clone(),
                    &summary.value_flows,
                    &summary.storage_aliases,
                    summary.unknown_targets.clone(),
                ),
            )
        })
        .collect();
    OriginSummaries::native(summaries, flows)
}

pub(crate) fn compute_origins_a2(
    program: &RustProgram<'_>,
) -> (OriginSummaries, origin_flow::A2Plan) {
    let (flows, plan) = origin_flow::analyze_program_origin_flow_a2(program);
    (origin_summaries_from_flows(flows), plan)
}

/// Whole-program signature-origin summaries. NB5-O's zero-delta rs-crown differential retired the
/// wrapped production derivation from the BO path; it remains available only as a test oracle.
pub(crate) fn compute_origins(program: &RustProgram<'_>) -> OriginSummaries {
    compute_origins_native(program)
}

/// §NB4-4c NO-BORROW-ORIGIN DEMOTION SET: the origins' `unknown` SIGNATURE/FIELD slots, mapped to
/// their kind-solver `SlotRef`s. `emit_crate_ownership_constraints` applies a monotone `¬ref` to each
/// (the may-supply demotion).
///
/// **The set is "NO-BORROW-ORIGIN", NOT "opaque-poisoned"** (dump-corrected 2026-07-16). A slot lands
/// in `summary.unknown` when its value has no trackable *borrow* origin — either an opaque-callee
/// RESULT (opaque return / opaque-supplied field), OR a freshly-`malloc`'d OWNED pointer
/// (`*out = malloc()`, `return malloc()`). The `malloc_only` vs `malloc_opaque` ablation proves
/// `opaque(out)` adds NOTHING to this set, so a member cannot be read as "an opaque callee may
/// overwrite it."
///
/// `¬ref`-only is sound precisely because it is SELF-DISCRIMINATING and makes no may-overwrite claim:
/// - an OWNED slot keeps `Owning` — its malloc source selector still settles it, and `¬ref` forbids
///   only the *reference* reading; the slot is `Owning` before AND after (no over-demotion — this is
///   what a uniform `¬own` got wrong: it forced owned `*out=malloc()` transfers to `Raw`).
/// - an opaque RESULT (no owning origin, previously `Ref`) drops to `Raw` — the may-supply FFI-S2-6
///   fix (a shared `&T` over unknown callee memory the callee may retain + write).
///
/// Covers base signature slots (args/returns) AND struct fields (the field skip is dropped).
///
/// DEFERRED — one bucket, gate = effect-row + opaque-interaction detection (see task doc): (a) the
/// may-OVERWRITE demotion of an owned slot an opaque callee may overwrite — UN-targetable here (the
/// overwrite is not in `summary.unknown`); marker = the reverted `out@1`-Owning-today assertion.
/// (b) depth-0 arg retention — marker `nb4_4c_marker_depth0_arg_retention_open`; the tier-2 seed-size
/// dump (harness `CRAT_BOC1_SEED_SIZE`) sizes it. Both need opaque-callee-interaction detection that
/// this no-borrow-origin set does not provide.
pub(crate) fn collect_no_borrow_origin_slots(
    origins: &OriginSummaries,
    slots: &CrateSlots,
) -> Vec<SlotRef> {
    let mut out = vec![];
    for (&f, summary) in origins.iter() {
        for slot in summary.unknown.iter() {
            if let Some(r) = signature_slot_to_ref(summary.slots[slot], f, slots) {
                out.push(r);
            }
        }
    }
    out
}

/// Map a signature slot to its kind-solver `SlotRef` (shared by the demotion set and the NB4-4c-Q
/// over-inclusion measurement, so both agree on the mapping).
///
/// §NB4-4c: field slots are NOT skipped — a no-borrow-origin struct-field slot maps to its crate-wide
/// kind `SlotRef::Field`. The signature carries the `borrow`-side `StructFieldSlot`; the kind universe
/// keys on the `borrow_ownership::slots` one — identically shaped, SAME `(struct_did, all-fields
/// `field_index`)` semantics (`borrow/mod.rs:136` `field.index()` vs `crate_slots.rs:39-46`
/// `all_fields().enumerate()`), but distinct nominal types.
fn signature_slot_to_ref(
    sig: SignatureSlot,
    f: rustc_span::def_id::LocalDefId,
    slots: &CrateSlots,
) -> Option<SlotRef> {
    use rustc_middle::mir::RETURN_PLACE;
    if let Some(field) = sig.place.field {
        return slots
            .field_slots
            .slot_for_field_depth(field, sig.depth)
            .map(SlotRef::Field);
    }
    let universe = slots.fn_local_slots.get(&f)?;
    let local = match sig.place.root {
        SignatureRoot::Return => RETURN_PLACE,
        SignatureRoot::Arg(l) => l,
    };
    universe
        .slot_for_local_depth(local, sig.depth)
        .map(|id| SlotRef::Local(f, id))
}

/// §NB4-4c-Q (MEASUREMENT-ONLY — item-4 sizing, 2026-07-17): the OVER-INCLUSION subset of the
/// no-borrow-origin demotion set — `unknown` SIGNATURE/FIELD slots that ALSO carry a modeled borrow
/// origin. These are the slots the may-supply `¬ref` demotes despite them having a real origin; the
/// coherence-collateral Ref-loss they cause is what the `CRAT_BOC1_COLLATERAL` sweep measures (n_ref
/// with these slots removed from the demotion set MINUS n_ref with the full set).
///
/// **NEVER SHIP a demotion that excludes these.** A branch-join `q = if c { op(p) } else { p }` fires
/// this predicate identically to a definitely-overwritten `q = op(p); q = p` (flow-insensitivity), yet
/// the branch-join demotion is LEGITIMATE — un-demoting it reinstates an unsound `Ref`. The shippable
/// fix is item-4's definitely-overwritten-vs-may-reach distinction, not this set. This collector exists
/// solely to SIZE the collateral (an UPPER BOUND on what the precise fix would recover).
///
/// `mitigated`: discard incoming edges whose REVERSE is also in `subset`. `subset` folds the SYMMETRIC
/// `storage_aliases` (both directions), and `observable_value_target` filters `unknown` but NOT storage
/// — so an opaque-derived slot can pass "sub ∉ unknown" via a bidirectional storage edge whose true
/// source was filtered out of `unknown`. Genuine `q = p` value flows are unidirectional and survive the
/// mitigation; storage pairs are discarded. Both counts are reported so the storage inflation is visible.
pub(crate) fn collect_overincluded_modeled_origin_slots(
    origins: &OriginSummaries,
    slots: &CrateSlots,
    mitigated: bool,
) -> Vec<SlotRef> {
    let mut out = vec![];
    for (&f, summary) in origins.iter() {
        for s in summary.unknown.iter() {
            if carries_modeled_origin(summary, s, mitigated) {
                if let Some(r) = signature_slot_to_ref(summary.slots[s], f, slots) {
                    out.push(r);
                }
            }
        }
    }
    out
}

/// True iff `s` has an incoming subset edge `sub → s` from a non-self, non-`unknown` source (a modeled
/// borrow origin flows into it). `mitigated` additionally requires the edge be unidirectional (no
/// reverse `s → sub`), discarding the symmetric storage aliases folded into `subset`.
fn carries_modeled_origin(summary: &OriginSummary, s: OriginSlot, mitigated: bool) -> bool {
    for sub in summary.subset.rows() {
        if sub == s || summary.unknown.contains(sub) {
            continue;
        }
        if !summary.subset.contains(sub, s) {
            continue;
        }
        if mitigated && summary.subset.contains(s, sub) {
            continue;
        }
        return true;
    }
    false
}

/// §NB4-4c-Q UPPER BOUND (Codex F1, 2026-07-17): the MAXIMAL over-inclusion — `unknown` SIGNATURE slots
/// with ANY incoming subset edge, SELF-INCLUSIVE and UNMITIGATED. Unlike the mitigated set, this catches
/// (a) restored input-root self-origins — `*out = old` after `*out = op()`, whose recovered origin
/// survives projection only as a self-loop `s → s` (the intermediate `old` is dropped) — and (b)
/// symmetric storage aliases. Removing these from the demotion set yields collateral ≥ the TRUE
/// recoverable, so it is the SOUND upper bound the defer/gate decision needs. A pure opaque result has
/// NO incoming edge (the opaque call breaks the flow), so it stays demoted — correctly excluded.
fn has_any_incoming_origin(summary: &OriginSummary, s: OriginSlot) -> bool {
    summary
        .subset
        .rows()
        .any(|sub| summary.subset.contains(sub, s))
}

/// §NB4-4c-Q UPPER-BOUND over-inclusion collector (Codex F1). The self-inclusive maximal set; see
/// `has_any_incoming_origin`. Reported alongside the mitigated set so the gate can use a sound upper
/// bound (`mitigated ⊆ upper`).
pub(crate) fn collect_upperbound_overincluded_slots(
    origins: &OriginSummaries,
    slots: &CrateSlots,
) -> Vec<SlotRef> {
    let mut out = vec![];
    for (&f, summary) in origins.iter() {
        for s in summary.unknown.iter() {
            if has_any_incoming_origin(summary, s) {
                if let Some(r) = signature_slot_to_ref(summary.slots[s], f, slots) {
                    out.push(r);
                }
            }
        }
    }
    out
}

/// Correct multi-hop transitive closure of `value_flows` (edge `source → target` means
/// `source`'s origin flows into `target`'s). `answer.contains(sub, sup)` ⇔ `sub` reaches `sup`.
/// This is the transitively-correct closure the production `subset_closure` (1-hop, D3) is not —
/// note line: successors are taken from the POPPED node, never the root.
fn transitive_closure(
    value_flows: &SparseBitMatrix<OriginSlot, OriginSlot>,
    n_slots: usize,
) -> SparseBitMatrix<OriginSlot, OriginSlot> {
    let mut answer = SparseBitMatrix::new(n_slots);
    let mut stack: Vec<OriginSlot> = vec![];
    let mut visited: DenseBitSet<OriginSlot> = DenseBitSet::new_empty(n_slots);
    for root in (0..n_slots).map(OriginSlot::new) {
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
    use rustc_hash::FxHashMap;
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_middle::ty::TyCtxt;

    use super::*;
    use crate::analyses::borrow_ownership::origin_summary::{
        OriginSlot, SignatureRoot, SignatureSlot,
    };

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
        RustProgram {
            tcx,
            functions,
            structs,
        }
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
            let summaries = compute_origins_native(&program);
            let mut out = FxHashMap::default();
            for &f in &program.functions {
                let s = &summaries[&f];
                let edges = |m: &rustc_index::bit_set::SparseBitMatrix<OriginSlot, OriginSlot>| {
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
                let mut unknown: Vec<String> = s
                    .unknown
                    .iter()
                    .map(|slot| format_slot(s.slots[slot]))
                    .collect();
                unknown.sort();
                out.insert(
                    tcx.item_name(f.to_def_id()).to_string(),
                    Facts {
                        subset: edges(&s.subset),
                        unknown,
                    },
                );
            }
            out
        })
        .unwrap()
    }

    #[derive(Debug, PartialEq, Eq)]
    struct CanonicalSummary {
        slots: Vec<String>,
        subset: Vec<(String, String)>,
        unknown: Vec<String>,
    }

    fn canonical_summaries(
        code: &str,
        compute: for<'tcx> fn(&RustProgram<'tcx>) -> OriginSummaries,
    ) -> FxHashMap<String, CanonicalSummary> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = build_program(tcx);
            let summaries = compute(&program);
            let mut out = FxHashMap::default();
            for &f in &program.functions {
                let summary = &summaries[&f];
                let slots = summary.slots.iter().copied().map(format_slot).collect();
                let mut subset = Vec::new();
                for sub in summary.subset.rows() {
                    if let Some(sups) = summary.subset.row(sub) {
                        for sup in sups.iter() {
                            subset.push((
                                format_slot(summary.slots[sub]),
                                format_slot(summary.slots[sup]),
                            ));
                        }
                    }
                }
                subset.sort();
                let mut unknown = summary
                    .unknown
                    .iter()
                    .map(|slot| format_slot(summary.slots[slot]))
                    .collect::<Vec<_>>();
                unknown.sort();
                out.insert(
                    tcx.item_name(f.to_def_id()).to_string(),
                    CanonicalSummary {
                        slots,
                        subset,
                        unknown,
                    },
                );
            }
            out
        })
        .unwrap()
    }

    /// NB5-O RED: the BO-native derivation must reproduce the wrapped oracle at the finest
    /// summary granularity: every function, ordered slot, subset edge, and unknown membership.
    #[test]
    fn nb5o_native_matches_wrapped_fixture_summaries() {
        const FIXTURES: &[&str] = &[
            "unsafe fn id(p: *mut i32) -> *mut i32 { p }",
            "unsafe fn f(dst: *mut *mut i32, src: *mut i32) { *dst = src; }",
            "unsafe fn addr(mut p: *mut i32) -> *mut *mut i32 { &raw mut p }",
            "unsafe extern \"C\" { fn ext(p: *mut i32) -> *mut i32; }\n\
             unsafe fn f(p: *mut i32) -> *mut i32 { ext(p) }",
            "unsafe fn a(p: *mut i32, n: i32) -> *mut i32 { if n == 0 { p } else { b(p, n - 1) } }\n\
             unsafe fn b(p: *mut i32, n: i32) -> *mut i32 { if n == 0 { p } else { a(p, n - 1) } }",
            "struct A { p: *mut i32 }\nstruct B { p: *mut i32 }\n\
             unsafe fn f(a: *mut A, b: *mut B) { (*a).p = (*b).p; }",
        ];
        for fixture in FIXTURES {
            assert_eq!(
                canonical_summaries(fixture, compute_origins_native),
                canonical_summaries(fixture, compute_origins_wrapped),
                "native/wrapped summary delta for fixture:\n{fixture}"
            );
        }
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
        let facts = origin_facts("unsafe fn f(dst: *mut *mut i32, src: *mut i32) { *dst = src; }");
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
        let facts = origin_facts("unsafe fn forward(out: *mut *mut i32) -> *mut *mut i32 { out }");
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
        let mut m: SparseBitMatrix<OriginSlot, OriginSlot> = SparseBitMatrix::new(3);
        let (a, b, c) = (OriginSlot::new(0), OriginSlot::new(1), OriginSlot::new(2));
        m.insert(a, b);
        m.insert(b, c);
        let closed = transitive_closure(&m, 3);
        let reaches =
            |x: OriginSlot, y: OriginSlot| closed.row(x).is_some_and(|r| r.iter().any(|z| z == y));
        assert!(
            reaches(a, c),
            "A→C must hold transitively (A→B→C); a 1-hop closure misses it"
        );
        assert!(
            reaches(a, b) && reaches(b, c),
            "direct A→B and B→C must hold"
        );
    }

    /// Argument depth-0 storage symmetry regression (Codex 3c-i re-review). A storage alias whose
    /// target is a NON-observable argument depth-0 slot survives ONLY in `storage_aliases` —
    /// `to_summary()` drops it from `value_flows` via the `observable_value_target` filter. `&raw mut
    /// p` aliases the returned `*mut *mut` pointee storage with `p`'s address, so `subset` must carry
    /// BOTH directions — proving `compute_origins` unions `storage_aliases` in (not lost with the
    /// removed separate field).
    #[test]
    fn nb3_arg_depth0_storage_symmetry() {
        let facts = origin_facts("unsafe fn addr(mut p: *mut i32) -> *mut *mut i32 { &raw mut p }");
        let f = &facts["addr"];
        assert!(
            has(&f.subset, "arg1@0", "return@1") && has(&f.subset, "return@1", "arg1@0"),
            "addr: BOTH storage directions (arg1@0 ↔ return@1) must be in subset after the storage \
             union; got {:?}",
            f.subset
        );
    }

    // ---- §NB3-3c-ii REDUNDANCY WITNESS (guard-claim discipline) ----
    //
    // The rescope claim (2026-07-12): injecting origins' depth-0 subset into the fork adds nothing —
    // the fork ALREADY consumes `lifetime_flow`'s interprocedural flows through production's own
    // `depth0_value_flows` seam (fork replay → `borrow_inference` → `ProvenanceConstraintGraph::new`).
    // This witness proves it PER EDGE-CLASS: every depth-0 origins subset edge (minus `unknown`
    // endpoints) is one of — (already) already in `depth0_value_flows`; (closure) derivable by the
    // fork's own transitive closure of those edges (`compute_subset_closure`/`requires`); or a
    // genuinely-new (storage / composite) edge the fork CANNOT re-derive. The GATE asserts the last
    // two soundness-relevant buckets (`storage`, `genuinely_new`) are EMPTY. If either is non-empty,
    // injection would add a real constraint ⇒ the redundancy claim is false ⇒ STOP.
    //
    // Only DEPTH-0 endpoints are in scope: `depth0_value_flows` never carries deeper pointer levels,
    // and 3c-ii injection would be depth-0 (the depth-0/Local-grained provenance universe). Deeper
    // origins are the NB5-O harvest, out of scope here.

    use rustc_hash::FxHashSet;

    use crate::analyses::{borrow::ProvenanceOwner, borrow_ownership::slots::StructFieldSlot};

    // Owner key preserving FULL field identity (F4, Codex 2026-07-12): `StructFieldSlot` carries
    // `struct_did` + `field_index`, so keying fields by `field_index` alone collided field-0 across
    // DIFFERENT structs and could mask a genuinely-new cross-struct edge as already/reflexive. The
    // enum keeps the whole `StructFieldSlot` — exactly what `provenance_owner` (and thus
    // `depth0_value_flows`) compares.
    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
    enum OKey {
        Local(usize),
        Field(StructFieldSlot),
    }

    fn owner_key(o: ProvenanceOwner) -> OKey {
        match o {
            ProvenanceOwner::Local(l) => OKey::Local(l.index()),
            ProvenanceOwner::Field(sf) => OKey::Field(StructFieldSlot {
                struct_did: sf.struct_did,
                field_index: sf.field_index,
            }),
        }
    }

    // A depth-0 `SignatureSlot` → the SAME key `depth0_value_flows` uses via `provenance_owner`.
    // None for depth>0 (out of scope — deeper origins are the NB5-O harvest).
    fn slot_key(slot: SignatureSlot) -> Option<OKey> {
        if slot.depth != 0 {
            return None;
        }
        match slot.place.field {
            Some(sf) => Some(OKey::Field(sf)),
            None => match slot.place.root {
                SignatureRoot::Return => Some(OKey::Local(0)), // RETURN_PLACE = _0
                SignatureRoot::Arg(l) => Some(OKey::Local(l.index())),
            },
        }
    }

    #[derive(Default)]
    struct Buckets {
        already: usize,
        closure: usize,
        /// Reflexive `sub ⊆ sub` — trivially true, a vacuous no-op as a subset constraint. Arises
        /// e.g. from a symmetric storage alias round-tripping through a deeper slot (`addr`'s
        /// `arg1@0 ↔ return@1` yields `arg1@0 → arg1@0`). Excluded from the gate: it adds nothing.
        reflexive: usize,
        storage: Vec<(OKey, OKey)>,
        genuinely_new: Vec<(OKey, OKey)>,
    }

    // `v` reachable from `u` over the directed edge set `b` (multi-hop) — the fork's own subset
    // closure. BFS; successors taken from the POPPED node (the D3-correct closure).
    fn reachable(b: &FxHashSet<(OKey, OKey)>, u: OKey, v: OKey) -> bool {
        let mut seen: FxHashSet<OKey> = FxHashSet::default();
        let mut stack = vec![u];
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            for &(s, t) in b {
                if s == n {
                    if t == v {
                        return true;
                    }
                    stack.push(t);
                }
            }
        }
        false
    }

    fn redundancy_buckets(src: &str) -> Vec<(String, Buckets)> {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = build_program(tcx);
            let origins = compute_origins(&program);
            let flows = lifetime_flow::analyze_program_lifetime_flow(&program);
            let mut out = vec![];
            for &f in &program.functions {
                let o = &origins[&f];
                let body = &flows[&f].body;
                let storage = &flows[&f].summary.storage_aliases;

                // B = depth0_value_flows edges (owner-key space) — what the fork already consumes.
                let mut b: FxHashSet<(OKey, OKey)> = FxHashSet::default();
                for (s, t) in body.depth0_value_flows() {
                    b.insert((owner_key(s), owner_key(t)));
                }
                // Direct storage-alias edges at depth-0 (owner-key space) — the fork does NOT get
                // these (`depth0_value_flows` reads value_flows only), so they classify as `storage`.
                let mut store: FxHashSet<(OKey, OKey)> = FxHashSet::default();
                for sub in storage.rows() {
                    let Some(sk) = slot_key(o.slots[OriginSlot::new(sub.index())]) else {
                        continue;
                    };
                    if let Some(sups) = storage.row(sub) {
                        for sup in sups.iter() {
                            if let Some(tk) = slot_key(o.slots[OriginSlot::new(sup.index())]) {
                                store.insert((sk, tk));
                            }
                        }
                    }
                }

                let unknown: std::collections::BTreeSet<OriginSlot> = o.unknown.iter().collect();
                let mut buckets = Buckets::default();
                for sub in o.subset.rows() {
                    if unknown.contains(&sub) {
                        continue;
                    }
                    let Some(sk) = slot_key(o.slots[sub]) else { continue };
                    if let Some(sups) = o.subset.row(sub) {
                        for sup in sups.iter() {
                            if unknown.contains(&sup) {
                                continue;
                            }
                            let Some(tk) = slot_key(o.slots[sup]) else { continue };
                            let edge = (sk, tk);
                            if sk == tk {
                                buckets.reflexive += 1; // vacuous `sub ⊆ sub` — never a real constraint
                            } else if b.contains(&edge) {
                                buckets.already += 1;
                            } else if reachable(&b, sk, tk) {
                                buckets.closure += 1;
                            } else if store.contains(&edge) {
                                buckets.storage.push(edge);
                            } else {
                                buckets.genuinely_new.push(edge);
                            }
                        }
                    }
                }
                out.push((tcx.item_name(f.to_def_id()).to_string(), buckets));
            }
            out
        })
        .unwrap()
    }

    /// GATE: origins' depth-0 subset (minus `unknown`) carries only edges the fork already has or
    /// re-derives by closure — no `storage`/`genuinely_new`. STOP if either bucket is non-empty.
    #[test]
    fn nb3c_origins_subset_redundant_vs_depth0() {
        const FIXTURES: &[(&str, &str)] = &[
            ("id", "unsafe fn id(p: *mut i32) -> *mut i32 { p }"),
            (
                "copychain",
                "unsafe fn f(a: *mut i32, b: *mut i32, c: *mut i32) -> *mut i32 { \
                 let x = a; let y = x; let _ = (b, c); y }",
            ),
            (
                "addr",
                "unsafe fn addr(mut p: *mut i32) -> *mut *mut i32 { &raw mut p }",
            ),
            (
                "storechain",
                "unsafe fn f(a: *mut *mut i32, b: *mut *mut i32, c: *mut *mut i32) { \
                 *a = *b; *b = *c; }",
            ),
            (
                "witness",
                "#[inline(never)] unsafe fn id(mut p: *mut i32) -> *mut i32 { p } \
                 unsafe fn f(mut p: *mut i32) -> i32 { let b = p; let x = id(p); let z = x; \
                 let r0 = *z; *b = 5; r0 + *z }",
            ),
            // Two structs with a same-INDEX pointer field (F4 non-vacuity, Codex): exercises field
            // slots so the `OKey::Field(StructFieldSlot)` full-identity key is actually stressed — a
            // `field_index`-only key would conflate `A.f0` with `B.f0`.
            (
                "two_struct_same_index_fields",
                "#[repr(C)] pub struct A { pub f0: *mut i32 } #[repr(C)] pub struct B { pub f0: *mut i32 } \
                 pub unsafe fn f(a: *mut A, b: *mut B) { (*a).f0 = (*b).f0; }",
            ),
        ];
        for (label, src) in FIXTURES {
            for (fname, bk) in redundancy_buckets(src) {
                eprintln!(
                    "REDUNDANCY {label}/{fname}: already={} closure={} reflexive={} storage={} \
                     genuinely_new={}",
                    bk.already,
                    bk.closure,
                    bk.reflexive,
                    bk.storage.len(),
                    bk.genuinely_new.len()
                );
                assert!(
                    bk.storage.is_empty() && bk.genuinely_new.is_empty(),
                    "{label}/{fname}: origins carry depth-0 subset edges the fork cannot re-derive — \
                     injection is NOT redundant (STOP). storage={:?} genuinely_new={:?} \
                     (already={} closure={} reflexive={})",
                    bk.storage,
                    bk.genuinely_new,
                    bk.already,
                    bk.closure,
                    bk.reflexive
                );
            }
        }
    }
}
