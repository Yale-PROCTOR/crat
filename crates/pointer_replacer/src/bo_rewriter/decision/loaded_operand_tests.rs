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
        super::loaded_operand::read_loaded_operands(site, 0, 1, &mut proof);
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
