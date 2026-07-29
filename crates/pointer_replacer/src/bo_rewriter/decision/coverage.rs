//! **The coverage gate.** Two axes, two references, compared as SETS.
//!
//! # Why two
//!
//! A coverage reference must come from a different *derivation layer*, not a
//! different function. Three rounds shipped one reference each and called the
//! gate closed; each was blind exactly where the collector was blind:
//!
//! | axis | collector | reference | independent of the collector? |
//! |---|---|---|---|
//! | **type** — is this parameter a pointer? | `ptr_chain_depth` on `fn_sig` inputs | `ptr_chain_depth` on MIR `local_decls` (E-R1) | *predicate shared* — see below |
//! | **item** — which functions exist? | `program.functions`, from `hir_crate(()).owners` | [`super::universe`], from `hir_crate_items(())` | **YES** |
//!
//! ## What the type axis does and does not check, post-R-A
//!
//! Stated plainly because it is a real narrowing. R-A moved subject collection
//! onto resolved types, which was the right fix — it is what makes the C2Rust
//! alias class visible at all — but it also made the collector's *type
//! predicate* the same function E-R1 uses. So the type axis no longer
//! cross-checks the predicate: the alias class is **fixed by R-A rather than
//! gated**, and residual type-axis correctness rests on `ptr_chain_depth`'s own
//! witnesses (one M0-hardened function, not a new gate's worth of risk). That
//! is recorded as a named joint-blindness spot in the evaluation's
//! threats-to-validity, not papered over here.
//!
//! What the type axis still checks — and it is the thing most likely to break —
//! is the **mapping**: HIR parameter index `i` ↔ MIR local `_{i+1}`. The two
//! sides reach the same predicate through genuinely different lowerings
//! (`fn_sig` from HIR, `local_decls` from MIR building), so a mapping that
//! slips shows up as a set difference even though the predicate agrees. The
//! fail-loud arm below guards *that*, and its message says so rather than
//! implying it guards invention in general.
//!
//! # Direction-asymmetric severity (R-B)
//!
//! - **Reference surplus** — a reference sees a pointer parameter the collector
//!   produced no subject for: an attributed [`DegradeReason::OutOfCoverage`],
//!   loud in the counters, **run continues**. This is the coverage gap the gate
//!   exists to surface, and halting the crate for it would reproduce the
//!   whole-crate-verdict problem S2b is separately fixing.
//! - **Collector surplus** — a subject no reference knows about: **fail-loud**.
//!   A subject that exists on neither reference was not missed, it was invented,
//!   and no counter should absorb that.
//!
//! # Sets, not cardinalities
//!
//! Every comparison here is over mapped sets. Equal counts with different
//! members must fail: count-only agreement is exactly how two blind sides agree,
//! and it is how round one and round two passed.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Local, ty::TyCtxt};

use super::{Degradation, DegradeReason, Subject, emitability::EmitabilityFacts, universe::UniverseReport};
use crate::analyses::borrow_ownership::crate_slots::CrateSlots;

/// What the reconciliation found.
pub(crate) struct Reconciliation {
    /// Reference-side surplus, as attributed degradations (R-B).
    pub gaps: Vec<Degradation>,
}

/// Reconcile the collector's subjects against both references.
///
/// `arg_counts` maps each function to its MIR `arg_count`, which is what bounds
/// the parameter locals `_1 ..= arg_count`. It is passed in rather than queried
/// here so this function does not need to borrow MIR bodies a second time.
///
/// # Panics
///
/// On **collector surplus** in either axis — a subject or a function the
/// references do not know. See the module docs: that direction is a contract
/// violation, not a coverage gap.
pub(crate) fn reconcile(
    tcx: TyCtxt<'_>,
    program_fns: &[LocalDefId],
    subjects: &[Subject],
    slots: &CrateSlots,
    arg_counts: &FxHashMap<LocalDefId, usize>,
    universe: &UniverseReport,
) -> Reconciliation {
    let mut gaps = Vec::new();

    // ---- item axis: hir_crate_items(()) vs program.functions ----------------
    let program_set: FxHashSet<LocalDefId> = program_fns.iter().copied().collect();

    let invented: Vec<LocalDefId> = program_set
        .iter()
        .filter(|did| !universe.free_fns.contains(did))
        .copied()
        .collect();
    assert!(
        invented.is_empty(),
        "collector surplus on the ITEM axis: {} function(s) are in the analysis \
         universe but absent from the independent `hir_crate_items` walk — {:?}. \
         A function on neither reference was not missed, it was invented, so this \
         is a contract violation rather than a coverage gap (R-B).",
        invented.len(),
        invented
            .iter()
            .map(|did| tcx.def_path_str(did.to_def_id()))
            .collect::<Vec<_>>()
    );

    for did in &universe.free_fns {
        if program_set.contains(did) {
            continue;
        }
        // Reference surplus on the item axis: a whole function the collector's
        // universe never saw. Its pointer parameters are the missing subjects.
        gaps.push(Degradation {
            subject: tcx.def_path_str(did.to_def_id()),
            site: EmitabilityFacts::site(tcx, tcx.def_span(did.to_def_id())),
            reason: DegradeReason::OutOfCoverage {
                reference: "hir-crate-items",
            },
        });
    }

    // ---- type axis: E-R1 depth-0 parameter slots vs collected subjects ------
    let collected: FxHashSet<(LocalDefId, Local)> =
        subjects.iter().map(|s| (s.fn_did, s.local)).collect();

    let mut reference: FxHashSet<(LocalDefId, Local)> = FxHashSet::default();
    for &f in program_fns {
        let (Some(slot_universe), Some(&arg_count)) =
            (slots.fn_local_slots.get(&f), arg_counts.get(&f))
        else {
            continue;
        };
        for index in 1..=arg_count {
            let local = Local::from_usize(index);
            if slot_universe.slot_for_local_depth(local, 0).is_some() {
                reference.insert((f, local));
            }
        }
    }

    let unmapped: Vec<&Subject> = subjects
        .iter()
        .filter(|s| !reference.contains(&(s.fn_did, s.local)))
        .collect();
    assert!(
        unmapped.is_empty(),
        "collector surplus on the TYPE axis: {} subject(s) have no depth-0 \
         parameter slot in E-R1 — {:?}. Both sides apply the same \
         `ptr_chain_depth` predicate (R-A), so a difference here is not a \
         predicate disagreement: it means the HIR parameter index → MIR local \
         `_{{i+1}}` MAPPING slipped, or a subject was built for a function with \
         no MIR body. That is a contract violation, not a coverage gap (R-B).",
        unmapped.len(),
        unmapped.iter().map(|s| &s.label).collect::<Vec<_>>()
    );

    for (fn_did, local) in &reference {
        if collected.contains(&(*fn_did, *local)) {
            continue;
        }
        gaps.push(Degradation {
            subject: format!("{}::_{}", tcx.def_path_str(fn_did.to_def_id()), local.as_usize()),
            site: EmitabilityFacts::site(tcx, tcx.def_span(fn_did.to_def_id())),
            reason: DegradeReason::OutOfCoverage {
                reference: "er1-depth0-param-slots",
            },
        });
    }

    // Deterministic order: `gaps` is built from hash-set iteration, and a
    // report whose row order permutes between runs is not comparable.
    gaps.sort_by(|a, b| (&a.subject, &a.site).cmp(&(&b.subject, &b.site)));
    Reconciliation { gaps }
}

#[cfg(test)]
mod tests {
    //! # Scope of these witnesses, stated rather than implied
    //!
    //! Each perturbs ONE reconciliation input and asserts the corresponding arm
    //! fires. They are unit tests of the gate, **not** end-to-end fixtures, and
    //! the reason is worth recording: no *source program* can currently make
    //! the two sides disagree. Post-R-A both apply `ptr_chain_depth`, and
    //! `hir_crate_items` agrees with the owner walk on every crate shape this
    //! milestone has seen. A test claiming an end-to-end divergence would be
    //! claiming a defect that does not exist.
    //!
    //! What that buys is real all the same: these are the arms that fire when a
    //! future filter, mapping change, or collector edit *does* introduce a
    //! divergence — and unlike the three gates this round replaced, each of them
    //! demonstrably fails when its branch is deleted.

    use super::*;
    use crate::analyses::borrow_ownership::mutability_facts::MutFacts;

    const SRC: &str = "#![allow(dead_code)]\n\
         pub unsafe fn one(p: *mut i32) -> i32 { *p }\n\
         pub unsafe fn two(q: *mut u8, r: *const u8) -> u8 { *q as u8 + *r }\n";

    /// Everything `reconcile` needs, all of it lifetime-free so it can be built
    /// inside the compiler callback and perturbed before the call.
    struct Inputs {
        program_fns: Vec<LocalDefId>,
        subjects: Vec<Subject>,
        slots: CrateSlots,
        arg_counts: FxHashMap<LocalDefId, usize>,
        universe: UniverseReport,
    }

    fn inputs(tcx: TyCtxt<'_>) -> Inputs {
        let program = crate::bo_rewriter::collect_program(tcx);
        let slots = CrateSlots::build(&program);
        let mut_facts = MutFacts::from_program(&program);
        let subjects = crate::bo_rewriter::collect_subjects(tcx, &program, &mut_facts);
        let mut arg_counts = FxHashMap::default();
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            arg_counts.insert(g, body.arg_count);
        }
        Inputs {
            program_fns: program.functions.clone(),
            subjects,
            slots,
            arg_counts,
            universe: super::super::universe::classify(tcx),
        }
    }

    fn run(tcx: TyCtxt<'_>, i: &Inputs) -> Reconciliation {
        reconcile(
            tcx,
            &i.program_fns,
            &i.subjects,
            &i.slots,
            &i.arg_counts,
            &i.universe,
        )
    }

    /// Baseline: the real pipeline agrees with both references.
    ///
    /// Also the non-vacuity anchor for every test below — if the fixture stopped
    /// producing subjects, the perturbations would be perturbing nothing and
    /// each of them would pass for the wrong reason.
    #[test]
    fn the_real_pipeline_agrees_with_both_references() {
        ::utils::compilation::run_compiler_on_str(SRC, |tcx| {
            let i = inputs(tcx);
            assert_eq!(
                i.subjects.len(),
                3,
                "fixture must produce the three pointer params it declares, or \
                 every perturbation below is inert; got {:?}",
                i.subjects.iter().map(|s| &s.label).collect::<Vec<_>>()
            );
            assert!(
                run(tcx, &i).gaps.is_empty(),
                "unperturbed inputs must reconcile clean"
            );
        })
        .expect("fixture compiles");
    }

    /// **Type axis, reference surplus.** A pointer parameter E-R1 sees and the
    /// collector produced no subject for is an attributed `OutOfCoverage`
    /// degradation — loud, and the run continues (R-B).
    ///
    /// *Mutation-tested (Rider 0, deletion first):* delete the
    /// `for (fn_did, local) in &reference` loop and this fails — the dropped
    /// parameter produces no gap and vanishes exactly as it did before this
    /// round.
    #[test]
    fn a_parameter_the_collector_missed_becomes_an_attributed_gap() {
        ::utils::compilation::run_compiler_on_str(SRC, |tcx| {
            let mut i = inputs(tcx);
            let dropped = i.subjects.pop().expect("fixture has subjects");
            let gaps = run(tcx, &i).gaps;
            assert_eq!(gaps.len(), 1, "expected exactly one gap, got {gaps:#?}");
            assert_eq!(
                gaps[0].reason,
                DegradeReason::OutOfCoverage {
                    reference: "er1-depth0-param-slots"
                },
                "wrong reason: {:#?}",
                gaps[0]
            );
            assert!(
                gaps[0].subject.contains(&format!("_{}", dropped.local.as_usize())),
                "the gap must NAME the missing parameter; dropped {} but gap says {}",
                dropped.label,
                gaps[0].subject
            );
            assert!(gaps[0].site.contains(':'), "gap carries no site: {:#?}", gaps[0]);
        })
        .expect("fixture compiles");
    }

    /// **Type axis, collector surplus.** A subject with no depth-0 parameter
    /// slot fails loudly (R-B).
    ///
    /// The message names what this arm actually guards, and the scope is
    /// narrower than "invention": post-R-A both sides apply the same
    /// `ptr_chain_depth` predicate, so a difference here cannot be a predicate
    /// disagreement — it is the HIR-index → MIR-local mapping having slipped.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* delete the `unmapped`
    /// assertion and this fails — no panic occurs.
    #[test]
    #[should_panic(expected = "collector surplus on the TYPE axis")]
    fn a_subject_with_no_slot_is_a_loud_mapping_failure() {
        ::utils::compilation::run_compiler_on_str(SRC, |tcx| {
            let mut i = inputs(tcx);
            // A parameter local no function has: the mapping produced a subject
            // the slot universe cannot account for.
            let mut invented = i.subjects[0].clone();
            invented.local = Local::from_usize(99);
            invented.label = "one::<invented>".to_owned();
            i.subjects.push(invented);
            run(tcx, &i);
        })
        .expect("fixture compiles");
    }

    /// **Item axis, reference surplus.** A whole function the analysis universe
    /// dropped is an attributed gap, not silence.
    ///
    /// This is the axis E-R1 cannot cover: `CrateSlots::build` iterates
    /// `program.functions`, so it is jointly blind with the collector here. Only
    /// the `hir_crate_items` walk can see it.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* delete the
    /// `for did in &universe.free_fns` loop and this fails.
    #[test]
    fn a_function_dropped_from_the_analysis_universe_becomes_an_attributed_gap() {
        ::utils::compilation::run_compiler_on_str(SRC, |tcx| {
            let mut i = inputs(tcx);
            let dropped = i.program_fns.pop().expect("fixture has functions");
            // Its subjects go with it — otherwise they would (correctly) trip
            // the TYPE axis's collector-surplus arm first and this test would
            // be measuring that instead.
            i.subjects.retain(|s| s.fn_did != dropped);
            let gaps = run(tcx, &i).gaps;
            assert_eq!(gaps.len(), 1, "expected exactly one gap, got {gaps:#?}");
            assert_eq!(
                gaps[0].reason,
                DegradeReason::OutOfCoverage {
                    reference: "hir-crate-items"
                },
                "wrong reason: {:#?}",
                gaps[0]
            );
            assert!(
                gaps[0].subject.contains(&tcx.def_path_str(dropped.to_def_id())),
                "the gap must NAME the dropped function; got {}",
                gaps[0].subject
            );
        })
        .expect("fixture compiles");
    }

    /// **Item axis, collector surplus.** A function on neither reference was
    /// not missed, it was invented — fail loudly (R-B).
    ///
    /// *Mutation-tested (Rider 0, deletion first):* delete the `invented`
    /// assertion and this fails — no panic occurs.
    #[test]
    #[should_panic(expected = "collector surplus on the ITEM axis")]
    fn a_function_no_item_walk_knows_is_a_loud_contract_failure() {
        ::utils::compilation::run_compiler_on_str(SRC, |tcx| {
            let mut i = inputs(tcx);
            // Same effect as a function reaching `program.functions` by a route
            // the independent item walk does not model.
            let hidden = *i.program_fns.first().expect("fixture has functions");
            i.universe.free_fns.remove(&hidden);
            run(tcx, &i);
        })
        .expect("fixture compiles");
    }

    /// **Sets, not cardinalities.** Equal counts with different members must
    /// still fail — count-only agreement is how two blind sides agree, and it
    /// is how the first two gates passed.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* replacing the set
    /// comparisons with `collected.len() == reference.len()` makes this pass,
    /// because the perturbation preserves the count exactly.
    #[test]
    fn equal_counts_with_different_members_still_fail() {
        ::utils::compilation::run_compiler_on_str(SRC, |tcx| {
            let mut i = inputs(tcx);
            // Swap one subject's local for another unmapped one: |subjects| is
            // unchanged, membership is not.
            let victim = i.subjects.last_mut().expect("fixture has subjects");
            victim.local = Local::from_usize(98);
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(tcx, &i)));
            assert!(
                result.is_err(),
                "a member-level difference with an identical count was accepted"
            );
        })
        .expect("fixture compiles");
    }
}
