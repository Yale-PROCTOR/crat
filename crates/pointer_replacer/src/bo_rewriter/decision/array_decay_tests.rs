//! R864-1 (b) (fan-out 081): two decays of one array are never disjoint, and
//! the classifier's proof over a decay is not taken.

use super::{
    a5_site_proof::{A5PeerProof, A5SiteProofVerdict},
    array_decay::{OVER_A_DECAY, SAME_ARRAY},
};

const INPUT: &str = include_str!("../testdata/r864_array_decays.rs");

/// `caller`'s call into `add`, arguments 0 and 1, a clear proof of `reason`
/// read through the decay rules.
fn read(caller: &str, reason: &'static str) -> (A5SiteProofVerdict, &'static str) {
    ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let functions = tcx
            .hir_body_owners()
            .filter(|owner| matches!(tcx.def_kind(*owner), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let callee = functions
            .iter()
            .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "add")
            .expect("add");
        let site = facts.call_args[callee]
            .iter()
            .find(|site| tcx.item_name(site.caller.to_def_id()).as_str() == caller)
            .expect("the call");
        let mut proof = A5PeerProof {
            verdict: A5SiteProofVerdict::Clear,
            reason,
            family: "excluded-proven-disjoint",
            location: None,
            left_site: None,
            right_site: None,
        };
        super::array_decay::read_array_decays(site, 0, 1, &mut proof);
        (proof.verdict, proof.reason)
    })
    .expect("input type-checks")
}

const CLASSIFIER: &str = "a5-proven-disjoint";
const SAME: (A5SiteProofVerdict, &str) = (A5SiteProofVerdict::Overlapping, SAME_ARRAY);
const NOT_TAKEN: (A5SiteProofVerdict, &str) = (A5SiteProofVerdict::Overlapping, OVER_A_DECAY);
const PROVEN: (A5SiteProofVerdict, &str) = (A5SiteProofVerdict::Clear, CLASSIFIER);

#[test]
fn r864_1_b_two_decays_of_one_local_array_are_not_disjoint() {
    assert_eq!(read("same_local", CLASSIFIER), SAME);
}

#[test]
fn r864_1_b_two_decays_of_one_static_array_are_not_disjoint() {
    assert_eq!(read("same_static", CLASSIFIER), SAME);
}

/// fan-out 081's emitted form: `zadd(&mut *x.as_mut_ptr(), x.as_mut_ptr(), …)`.
#[test]
fn r864_1_b_a_reborrowed_decay_beside_the_same_decay_is_not_disjoint() {
    assert_eq!(read("same_local_reborrowed", CLASSIFIER), SAME);
}

/// (i) holds whatever proved the pair: a certificate's clear is overridden too.
#[test]
fn r864_1_b_the_same_array_overrides_any_clear_proof() {
    assert_eq!(read("same_local", "pair-disjoint:distinct-roots"), SAME);
}

#[test]
fn r864_1_b_a_classifier_proof_over_a_decay_beside_a_pointer_is_not_taken() {
    assert_eq!(read("decay_beside_a_pointer", CLASSIFIER), NOT_TAKEN);
}

#[test]
fn r864_1_b_decays_through_references_are_not_distinct_objects() {
    assert_eq!(read("decays_through_references", CLASSIFIER), NOT_TAKEN);
}

#[test]
fn r864_1_b_control_decays_of_two_distinct_local_arrays_keep_the_proof() {
    assert_eq!(read("distinct_locals", CLASSIFIER), PROVEN);
}

#[test]
fn r864_1_b_control_decays_of_two_distinct_static_arrays_keep_the_proof() {
    assert_eq!(read("distinct_statics", CLASSIFIER), PROVEN);
}

/// wave-5d 145a (the review's HIGH 2): C `add(&x[1], &x[1])`.
#[test]
fn r864_1_b_offsets_of_one_array_are_not_disjoint() {
    assert_eq!(read("offsets_of_one_local", CLASSIFIER), SAME);
}

/// A local whose every definition is a decay of `x`, or arithmetic on itself.
#[test]
fn r864_1_b_locals_copied_from_one_array_are_not_disjoint() {
    assert_eq!(read("copies_of_one_local", CLASSIFIER), SAME);
}

#[test]
fn r864_1_b_reborrowed_offsets_of_one_array_are_not_disjoint() {
    assert_eq!(read("reborrowed_offsets_of_one_local", CLASSIFIER), SAME);
}

#[test]
fn r864_1_b_control_offsets_of_two_distinct_arrays_keep_the_proof() {
    assert_eq!(read("offsets_of_two_locals", CLASSIFIER), PROVEN);
}

/// A copy with another definition is not read as the array; the decay beside
/// it still refuses the classifier's proof.
#[test]
fn r864_1_b_a_copy_with_another_definition_is_not_the_array() {
    assert_eq!(
        read("a_copy_also_assigned_elsewhere", CLASSIFIER),
        NOT_TAKEN
    );
}
