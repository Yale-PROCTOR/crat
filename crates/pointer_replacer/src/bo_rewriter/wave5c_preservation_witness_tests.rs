//! Wave-5c preservation witness: a reduction of brotli's cluster / bit_cost
//! chain with the real callers, reproducing the shared family-restoration
//! withdrawal that the census of `dc601707` recorded (root 1831
//! `BrotliCompareAndPushToQueueLiteral`, path `[1831, 1834, …, 1348, 1347]`).
//! Handed to wave-5d (R397-6(a) / R398-1); this lane changes no restoration
//! logic.

use crate::bo_rewriter::decision::thin_counted_tests::ENTROPY;

/// The chain reduced to the four real callers on the recorded path
/// `[1831, 1834, …, 1369, 1348, 1347]`: `BrotliClusterHistogramsLiteral` →
/// `BrotliHistogramCombineLiteral` → `BrotliCompareAndPushToQueueLiteral` →
/// `BrotliPopulationCostLiteral` → `BitsEntropy` → `ShannonEntropy`.
const CHAIN: &str = r###"
#[derive(Copy, Clone)]
#[repr(C)]
pub struct HistogramLiteral { pub data_: [u32; 256], pub total_count_: usize, pub bit_cost_: f64 }
unsafe fn ClusterCostDiff(size_a: usize, size_b: usize) -> f64 {
    let size_c = size_a.wrapping_add(size_b);
    size_a as f64 * FastLog2(size_a) + size_b as f64 * FastLog2(size_b) - size_c as f64 * FastLog2(size_c)
}
unsafe fn HistogramAddHistogramLiteral(self_0: *mut HistogramLiteral, v: *const HistogramLiteral) {
    let mut i: usize = 0;
    (*self_0).total_count_ = (*self_0).total_count_.wrapping_add((*v).total_count_);
    while i < 256 {
        (*self_0).data_[i] = (*self_0).data_[i].wrapping_add((*v).data_[i]);
        i = i.wrapping_add(1);
    }
}
unsafe fn BrotliPopulationCostLiteral(histogram: *const HistogramLiteral) -> f64 {
    if (*histogram).total_count_ == 0 { return 12.0; }
    let mut depth_histo: [u32; 18] = [0; 18];
    let mut i: usize = 0;
    while i < 256 {
        if (*histogram).data_[i] > 0 {
            let depth = if i < 17 { i } else { 17 };
            depth_histo[depth] = depth_histo[depth].wrapping_add(1);
        }
        i = i.wrapping_add(1);
    }
    BitsEntropy(depth_histo.as_ptr(), 18usize)
}
unsafe fn BrotliCompareAndPushToQueueLiteral(out: *const HistogramLiteral, cluster_size: *const u32, idx1: u32, idx2: u32) -> f64 {
    if idx1 == idx2 { return 0.0; }
    let cost_diff = 0.5f64 * ClusterCostDiff(*cluster_size.offset(idx1 as isize) as usize,
                                             *cluster_size.offset(idx2 as isize) as usize);
    let mut combo = *out.offset(idx1 as isize);
    HistogramAddHistogramLiteral(&mut combo, &*out.offset(idx2 as isize));
    cost_diff + BrotliPopulationCostLiteral(&mut combo)
}
unsafe fn BrotliHistogramCombineLiteral(out: *const HistogramLiteral, cluster_size: *mut u32, num_clusters: usize) -> f64 {
    let mut acc = 0.0f64;
    let mut idx1: usize = 0;
    while idx1 < num_clusters {
        let mut idx2 = idx1.wrapping_add(1);
        while idx2 < num_clusters {
            acc += BrotliCompareAndPushToQueueLiteral(out, cluster_size, idx1 as u32, idx2 as u32);
            idx2 = idx2.wrapping_add(1);
        }
        *cluster_size.offset(idx1 as isize) = (*cluster_size.offset(idx1 as isize)).wrapping_add(1);
        idx1 = idx1.wrapping_add(1);
    }
    acc
}
pub unsafe fn BrotliClusterHistogramsLiteral(in_0: *const HistogramLiteral, in_size: usize) -> f64 {
    let cluster_size = if in_size > 0 { malloc(in_size.wrapping_mul(4)) as *mut u32 } else { 0 as *mut u32 };
    let mut i: usize = 0;
    while i < in_size {
        *cluster_size.offset(i as isize) = 1;
        i = i.wrapping_add(1);
    }
    let acc = BrotliHistogramCombineLiteral(in_0, cluster_size, in_size);
    free(cluster_size as *mut core::ffi::c_void);
    acc
}
"###;

fn chain_fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,non_snake_case,non_camel_case_types)]\nextern \"C\" {{ fn malloc(size: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }}\n{ENTROPY}\n{CHAIN}"
    )
}

use std::collections::BTreeSet;

use crate::bo_rewriter::{
    additive::{self, FamilyPolicy, FamilyStage, StageSnapshot},
    bridge_receipt::SignatureClassId,
    decision::{Decision, Degradation, DegradeReason},
};

/// What the census of `dc601707` recorded for brotli at every stage from
/// `SliceUse` on (`brotli-transaction-runs.json` in the witness packet):
///
/// * the predecessor stage delivered `BrotliCompareAndPushToQueueLiteral::
///   cluster_size#2` as `slice-shared`;
/// * the candidate stage converts its caller `BrotliHistogramCombineLiteral::
///   cluster_size#2` (`raw → slice-mut`) and, planning the call under the
///   T2-waived `SliceMutToWritableRawConst` bridge, decides the callee's
///   `cluster_size` raw — the delivered subject is lost;
/// * iteration 1 restores the callee — the victim — with
///   `restore-prior-family-disposition`; the caller is not touched, so the
///   loss persists;
/// * iteration 2 finds the victim disabled and withdraws EVERY changed owner in
///   the undirected interface component (105–120 per stage) with
///   `restore-family-interface-path:[1831, …]`, among them the four entropy
///   owners whose only change was this lane's independent `raw → slice-shared`
///   conversion (`…, 1369, 1348, 1347]`).
///
/// The reduction runs the four real callers, takes the terminal table and plan
/// as the stage predecessor, and edits exactly the three decisions the record
/// names: the loss, the culprit, and the innocent conversion.
struct Reduction {
    prior: StageSnapshot,
    candidate: StageSnapshot,
    push: SignatureClassId,
    combine: SignatureClassId,
    population_cost: SignatureClassId,
    bits: SignatureClassId,
    shannon: SignatureClassId,
}

fn with_reduction(test: impl FnOnce(Reduction) + Send) {
    let input = chain_fixture();
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                crate::bo_rewriter::A5Mode::PreciseReplay,
                Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let emission = crate::bo_rewriter::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        let terminal = StageSnapshot {
            table,
            plan: emission.plan,
        };
        let owner = |label: &str| {
            let (subject, _) = terminal
                .table
                .entries
                .iter()
                .find(|(s, _)| s.label == label)
                .unwrap_or_else(|| panic!("fixture subject {label}"));
            SignatureClassId::of(subject.fn_did)
        };
        let push = owner("BrotliCompareAndPushToQueueLiteral::cluster_size");
        let combine = owner("BrotliHistogramCombineLiteral::cluster_size");
        let population_cost = owner("BrotliPopulationCostLiteral::histogram");
        let bits = owner("BitsEntropy::population");
        let shannon = owner("ShannonEntropy::population");
        // The real shape at the landed frame: the callee's count-read parameter
        // is a delivered shared slice, the writing caller's is held.
        assert!(matches!(
            decision_of(
                &terminal,
                "BrotliCompareAndPushToQueueLiteral::cluster_size"
            ),
            Decision::Slice { mutable: false, .. }
        ));
        assert!(matches!(
            decision_of(&terminal, "BrotliHistogramCombineLiteral::cluster_size"),
            Decision::Degraded(Degradation {
                reason: DegradeReason::SliceUseUnsupported,
                ..
            })
        ));
        for class in [push, combine, population_cost, bits, shannon] {
            assert!(
                terminal
                    .plan
                    .class_finalization
                    .classes
                    .contains_key(&class),
                "every owner of the chain has a class"
            );
        }
        assert!(terminal.plan.class_finalization.classes[&push].is_ready());
        assert!(terminal.plan.class_finalization.classes[&bits].is_ready());
        assert!(terminal.plan.class_finalization.classes[&shannon].is_ready());

        // Predecessor: the entropy conversions have not arrived yet.
        let mut prior = terminal.clone();
        for label in ["BitsEntropy::population", "ShannonEntropy::population"] {
            degrade(&mut prior, label, DegradeReason::KindRaw);
        }
        // Candidate: the caller converts, the callee's delivered slice is lost,
        // the entropy conversions arrive.
        let mut candidate = terminal.clone();
        degrade(
            &mut candidate,
            "BrotliCompareAndPushToQueueLiteral::cluster_size",
            DegradeReason::SliceUseUnsupported,
        );
        *decision_mut(
            &mut candidate,
            "BrotliHistogramCombineLiteral::cluster_size",
        ) = Decision::Slice {
            mutable: true,
            uses: Vec::new(),
        };
        test(Reduction {
            prior,
            candidate,
            push,
            combine,
            population_cost,
            bits,
            shannon,
        });
    })
    .unwrap();
}

fn decision_of<'a>(snapshot: &'a StageSnapshot, label: &str) -> &'a Decision {
    &snapshot
        .table
        .entries
        .iter()
        .find(|(s, _)| s.label == label)
        .unwrap_or_else(|| panic!("fixture subject {label}"))
        .1
}

fn decision_mut<'a>(snapshot: &'a mut StageSnapshot, label: &str) -> &'a mut Decision {
    &mut snapshot
        .table
        .entries
        .iter_mut()
        .find(|(s, _)| s.label == label)
        .unwrap_or_else(|| panic!("fixture subject {label}"))
        .1
}

fn degrade(snapshot: &mut StageSnapshot, label: &str, reason: DegradeReason) {
    let (subject, decision) = snapshot
        .table
        .entries
        .iter_mut()
        .find(|(s, _)| s.label == label)
        .unwrap_or_else(|| panic!("fixture subject {label}"));
    *decision = Decision::Degraded(Degradation {
        subject: subject.identity_key(&label[..label.find("::").unwrap()]),
        site: "w5c preservation witness".to_owned(),
        reason,
    });
}

fn requested(reduction: &Reduction, policy: &FamilyPolicy) -> Vec<(SignatureClassId, String)> {
    additive::withdrawals(&reduction.prior, &reduction.candidate, policy, &[])
        .into_iter()
        .map(|w| (w.owner, w.cause))
        .collect()
}

fn owners(requests: &[(SignatureClassId, String)]) -> BTreeSet<SignatureClassId> {
    requests.iter().map(|(owner, _)| *owner).collect()
}

/// Iteration 2 of the record: the victim is already withdrawn, the loss
/// persists. RED for wave-5d (R397-6(a) / R398-1): an owner whose only change
/// is an independent conversion, connected to the loss by nothing but the
/// undirected interface graph, must keep it.
#[test]
#[ignore = "RED by design: wave-5d primitive (R398-1)"]
fn w5c_wall_interface_restoration_must_not_withdraw_an_unmoved_neighbour() {
    with_reduction(|reduction| {
        let mut policy = FamilyPolicy::at(FamilyStage::SliceUse);
        policy
            .withdrawn
            .insert((FamilyStage::SliceUse, reduction.push));
        let requests = requested(&reduction, &policy);
        println!("W5C-WALL iteration-2 requests: {requests:?}");
        let withdrawn = owners(&requests);
        assert!(
            !withdrawn.contains(&reduction.bits) && !withdrawn.contains(&reduction.shannon),
            "the entropy owners moved no lost subject; withdrawing them by interface reachability \
             is the wall: {requests:?}"
        );
        assert!(
            !withdrawn.contains(&reduction.population_cost),
            "an unchanged owner on the path is never a transaction: {requests:?}"
        );
    });
}

/// Iteration 1 of the record: nothing withdrawn yet. RED for wave-5d: the
/// transaction that owns the loss is the caller's new `slice-mut` candidate
/// (excluding it at the input restores the callee), never the callee whose
/// delivered slice it demoted.
#[test]
#[ignore = "RED by design: wave-5d primitive (R398-1)"]
fn w5c_wall_restoration_targets_the_candidate_that_caused_the_loss_not_the_victim() {
    with_reduction(|reduction| {
        let policy = FamilyPolicy::at(FamilyStage::SliceUse);
        let requests = requested(&reduction, &policy);
        println!("W5C-WALL iteration-1 requests: {requests:?}");
        let withdrawn = owners(&requests);
        assert_eq!(
            withdrawn,
            BTreeSet::from([reduction.combine]),
            "the withdrawal is the caller's candidate alone; the victim keeps its prior \
             delivery without a transaction of its own: {requests:?}"
        );
    });
}
