//! R838 (era-5c 148): a proof of disjointness A5 gave by its classifier
//! (origins OR points-to) is not taken where an operand is loaded from memory.

use super::a5_site_proof::{A5PeerProof, A5SiteProofVerdict};

const INPUT: &str = include_str!("../testdata/r838_loaded_operands.rs");

/// `caller`'s call into `add`, its arguments 0 and 1: a proven-disjoint proof
/// read through the correction.
fn read(caller: &str) -> (A5SiteProofVerdict, &'static str) {
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
            reason: "a5-proven-disjoint",
            family: "excluded-proven-disjoint",
            location: None,
            left_site: None,
            right_site: None,
        };
        // The retention the test supplies: only `keep` keeps its argument.
        let keep = functions
            .iter()
            .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "keep")
            .copied();
        super::loaded_operand::read_loaded_operands(site, 0, 1, &mut proof, |callee, _| {
            Some(callee) == keep
        });
        (proof.verdict, proof.reason)
    })
    .expect("input type-checks")
}

const NOT_SHOWN: (A5SiteProofVerdict, &str) = (
    A5SiteProofVerdict::Overlapping,
    super::loaded_operand::REASON,
);
const PROVEN: (A5SiteProofVerdict, &str) = (A5SiteProofVerdict::Clear, "a5-proven-disjoint");

#[test]
fn r838_two_statics_contents_are_not_shown_disjoint() {
    assert_eq!(read("statics"), NOT_SHOWN);
}

#[test]
fn r838_two_fields_read_through_a_pointer_are_not_shown_disjoint() {
    assert_eq!(read("fields"), NOT_SHOWN);
}

#[test]
fn r838_two_dereferences_one_through_a_local_are_not_shown_disjoint() {
    assert_eq!(read("derefs"), NOT_SHOWN);
}

#[test]
fn r838_two_locals_each_defined_by_a_load_are_not_shown_disjoint() {
    assert_eq!(read("locals_loaded"), NOT_SHOWN);
}

#[test]
fn r838_control_two_static_arrays_addresses_keep_the_proof() {
    assert_eq!(read("arrays"), PROVEN);
}

#[test]
fn r838_control_two_locals_addresses_keep_the_proof() {
    assert_eq!(read("locals"), PROVEN);
}

#[test]
fn r838_control_an_entrys_two_formals_keep_the_proof() {
    assert_eq!(read("entry"), PROVEN);
}

/// The narrowing: a loaded pointer beside `&mut l`, `l` a scalar local whose
/// address reaches no memory (its one borrow is this argument, and `add` keeps
/// nothing), keeps the proof.
#[test]
fn r838_narrowed_a_loaded_pointer_beside_an_unescaped_local_keeps_the_proof() {
    assert_eq!(read("unescaped"), PROVEN);
}

#[test]
fn r838_narrowed_control_the_local_stored_through_a_pointer_is_not_shown_disjoint() {
    assert_eq!(read("stored"), NOT_SHOWN);
}

#[test]
fn r838_narrowed_control_the_local_handed_to_a_callee_that_keeps_it_is_not_shown_disjoint() {
    assert_eq!(read("kept"), NOT_SHOWN);
}

#[test]
fn r838_narrowed_control_the_local_bound_by_ref_is_not_shown_disjoint() {
    assert_eq!(read("ref_bound"), NOT_SHOWN);
}
