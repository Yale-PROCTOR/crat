//! R838 (era-5c 148): a proof of disjointness A5 gave by its classifier
//! (origins OR points-to) is not taken where an operand is loaded from memory.

use super::a5_site_proof::{A5PeerProof, A5SiteProofVerdict};

const INPUT: &str = include_str!("../testdata/r838_loaded_operands.rs");

/// `caller`'s call into `add`, its arguments 0 and 1: a proven-disjoint proof
/// read through the correction.
fn read(caller: &str) -> (A5SiteProofVerdict, &'static str) {
    read_call("add", caller)
}

/// The same, for a call into `callee`. The no-retention certificate the test
/// supplies: every callee but `keepadd` certifies it.
fn read_call(callee: &str, caller: &str) -> (A5SiteProofVerdict, &'static str) {
    let callee_name = callee;
    ::utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let functions = tcx
            .hir_body_owners()
            .filter(|owner| matches!(tcx.def_kind(*owner), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let callee = functions
            .iter()
            .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == callee_name)
            .expect("the callee");
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
        super::loaded_operand::read_loaded_operands(site, *callee, 0, 1, &mut proof, |c, _| {
            tcx.item_name(c.to_def_id()).as_str() != "keepadd"
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
/// address the body takes only here, at a call no loop repeats, keeps the
/// proof (no pointer held that address when the arguments were evaluated).
#[test]
fn r838_narrowed_a_loaded_pointer_beside_an_unescaped_local_keeps_the_proof() {
    assert_eq!(read("unescaped"), PROVEN);
}

#[test]
fn r838_narrowed_control_the_local_stored_through_a_pointer_is_not_shown_disjoint() {
    assert_eq!(read("stored"), NOT_SHOWN);
}

#[test]
fn r838_narrowed_control_the_local_handed_to_another_call_first_is_not_shown_disjoint() {
    assert_eq!(read("kept"), NOT_SHOWN);
}

#[test]
fn r838_narrowed_control_the_local_bound_by_ref_is_not_shown_disjoint() {
    assert_eq!(read("ref_bound"), NOT_SHOWN);
}

/// era-5c 148a, executed in the census world (each emitted `add(a: &mut i32,
/// b: &i32)` before the correction): `add(G1, G1)`.
#[test]
fn r838_era5c_148a_one_static_passed_twice_is_not_shown_disjoint() {
    assert_eq!(read("same_static"), NOT_SHOWN);
}

/// era-5c 148a: `G2 = G1; add(G1, G2)`.
#[test]
fn r838_era5c_148a_a_static_copied_into_another_is_not_shown_disjoint() {
    assert_eq!(read("copied_static"), NOT_SHOWN);
}

/// era-5c 148a: `add(*p, *q)` called with `p == q`.
#[test]
fn r838_era5c_148a_two_dereferences_a_caller_makes_equal_are_not_shown_disjoint() {
    assert_eq!(read("derefs_equal"), NOT_SHOWN);
}

#[test]
fn r838_narrowed_control_a_call_a_loop_repeats_is_not_shown_disjoint() {
    assert_eq!(read("in_loop"), NOT_SHOWN);
}

#[test]
fn r838_narrowed_control_an_if_let_ref_binding_is_not_shown_disjoint() {
    assert_eq!(read("if_let_ref"), NOT_SHOWN);
}

/// Relay 180 item 4: the callee that receives the address must also certify
/// no retention: `keepadd` stores its second argument, so a loaded pointer
/// beside `&mut l` taken once, outside a loop, is still not shown disjoint.
#[test]
fn r838_narrowed_control_a_callee_without_the_no_retention_certificate_is_not_shown_disjoint() {
    assert_eq!(read_call("keepadd", "kept_once"), NOT_SHOWN);
}
