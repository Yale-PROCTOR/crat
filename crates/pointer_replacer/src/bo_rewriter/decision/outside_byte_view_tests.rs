//! R815-6 / R819-1 item 2: the scope's separate-object certificate read at the
//! pair proof, on `binn_object_blob`'s call into `binn_object_get` (`key` at
//! argument 1, `psize` at argument 4) and its variants. Each case reads one
//! not-proven-disjoint proof through the certificate and names the instance.

use super::a5_site_proof::{A5PeerProof, A5SiteProofVerdict};

const RECEIPT: &str = "pair-disjoint:premise-outside-byte-view";
const SAME_POINTEE_MUT: &str = "exported-entry:same-pointee-mut-pair";
const SCOPE_CLOSED_PROGRAM: &str = "pair-disjoint:scope-closed-program";

const BLOB: &str = include_str!("../testdata/r815_entry_byte_view_beside_typed.rs");

/// The proof at `entry`'s call into `binn_object_get` for arguments 1 and 4,
/// after the certificate reads it.
fn read(input: &str, entry: &str) -> (A5SiteProofVerdict, &'static str) {
    read_at(input, "binn_object_get", entry, 1, 4)
}

/// The proof at `entry`'s call into `callee` for arguments `left` and `right`,
/// after the certificate reads it.
fn read_at(
    input: &str,
    callee: &str,
    entry: &str,
    left: usize,
    right: usize,
) -> (A5SiteProofVerdict, &'static str) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let functions = tcx
            .hir_body_owners()
            .filter(|owner| matches!(tcx.def_kind(*owner), rustc_hir::def::DefKind::Fn))
            .collect::<Vec<_>>();
        let facts = super::emitability::collect(tcx, &functions);
        let callee = functions
            .iter()
            .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == callee)
            .expect("the callee");
        let site = facts.call_args[callee]
            .iter()
            .find(|site| tcx.item_name(site.caller.to_def_id()).as_str() == entry)
            .expect("the entry's call");
        let mut proof = A5PeerProof {
            verdict: A5SiteProofVerdict::Overlapping,
            reason: "a5-not-proven-disjoint",
            family: "recorded-risky",
            location: None,
            left_site: None,
            right_site: None,
        };
        super::outside_byte_view::read_under_p8(&facts, site, left, right, &mut proof);
        (proof.verdict, proof.reason)
    })
    .expect("input type-checks")
}

fn certified(input: &str, entry: &str, receipt: &str) {
    assert_eq!(read(input, entry), (A5SiteProofVerdict::Clear, receipt));
}

fn not_certified(input: &str, entry: &str) {
    assert_eq!(
        read(input, entry),
        (A5SiteProofVerdict::Overlapping, "a5-not-proven-disjoint")
    );
}

/// P8: a byte formal beside a typed one.
#[test]
fn r819_2_a_byte_formal_beside_a_typed_formal_is_the_p8_instance() {
    certified(BLOB, "binn_object_blob", RECEIPT);
}

/// Two byte formals: the scope's remaining instance.
#[test]
fn r819_2_two_byte_formals_are_the_scope_instance() {
    let input = BLOB
        .replace("psize: *mut i32", "psize: *mut u8")
        .replace("*psize = value.size;", "*psize = value.size as u8;")
        .replace("0 as *mut i32", "0 as *mut u8");
    certified(&input, "binn_object_blob", SCOPE_CLOSED_PROGRAM);
}

/// A shared and a mutable formal of one pointee: the scope's remaining instance.
#[test]
fn r819_2_a_shared_and_a_mutable_formal_of_one_pointee_are_the_scope_instance() {
    let input = BLOB
        .replace("key: *const i8", "key: *const i32")
        .replace("*p.offset(i) as i8", "*p.offset(i) as i32");
    certified(&input, "binn_object_blob", SCOPE_CLOSED_PROGRAM);
}

/// Two mutable formals of one pointee: W4's instance.
#[test]
fn r819_2_two_mutable_formals_of_one_pointee_are_w4s_instance() {
    let input = BLOB
        .replace("key: *const i8", "key: *mut i32")
        .replace("*p.offset(i) as i8", "*p.offset(i) as i32");
    certified(&input, "binn_object_blob", SAME_POINTEE_MUT);
}

/// R767: a formal pair the provided test passes one object to (the fixture
/// table's `crat_w6o_zsub`, positions 0 and 2).
#[test]
fn r819_2_control_a_pair_the_provided_test_aliases_is_not_certified() {
    let input = BLOB.replace(
        "pub unsafe extern \"C\" fn binn_object_blob(\n    mut obj: *mut core::ffi::c_void,\n    mut key: *const i8,\n    mut psize: *mut i32,",
        "pub unsafe extern \"C\" fn crat_w6o_zsub(\n    mut key: *const i8,\n    mut obj: *mut core::ffi::c_void,\n    mut psize: *mut i32,",
    );
    assert!(input.contains("fn crat_w6o_zsub("));
    not_certified(&input, "crat_w6o_zsub");
}

/// An entry the program itself calls.
#[test]
fn r819_2_control_an_entry_the_program_calls_is_not_certified() {
    let input = format!(
        "{BLOB}\npub unsafe fn blob_user(o: *mut core::ffi::c_void, k: *const i8, s: *mut i32) -> *mut core::ffi::c_void {{ binn_object_blob(o, k, s) }}\n"
    );
    not_certified(&input, "binn_object_blob");
}

/// An unexported function.
#[test]
fn r819_2_control_an_unexported_function_is_not_certified() {
    let input = BLOB.replace(
        "#[no_mangle]\npub unsafe extern \"C\" fn binn_object_blob(",
        "pub unsafe extern \"C\" fn binn_object_blob(",
    );
    assert!(input.contains("\npub unsafe extern \"C\" fn binn_object_blob("));
    not_certified(&input, "binn_object_blob");
}

/// An argument that is not the entry's own formal (a local copied from it).
#[test]
fn r819_2_control_a_local_copy_of_a_formal_is_not_certified() {
    let input = BLOB.replace(
        "    binn_object_get(obj, key, 0xc0, &mut value as *mut *mut core::ffi::c_void as *mut core::ffi::c_void, psize);",
        "    let mut size = psize;\n    binn_object_get(obj, key, 0xc0, &mut value as *mut *mut core::ffi::c_void as *mut core::ffi::c_void, size);",
    );
    assert!(input.contains("let mut size = psize;"));
    not_certified(&input, "binn_object_blob");
}

/// A formal the entry's body assigns.
#[test]
fn r819_2_control_an_assigned_formal_is_not_certified() {
    let input = BLOB.replace(
        "    let mut value = 0 as *mut core::ffi::c_void;\n    binn_object_get(obj, key, 0xc0,",
        "    let mut value = 0 as *mut core::ffi::c_void;\n    psize = psize.offset(0);\n    binn_object_get(obj, key, 0xc0,",
    );
    assert!(input.contains("psize = psize.offset(0);"));
    not_certified(&input, "binn_object_blob");
}

const ROOTS: &str = include_str!("../testdata/r821_entry_formal_roots.rs");

/// R821-3 item 1: two different formals of one pointee, both mutable, are
/// certified (W4's instance) — the positive case beside the root controls.
#[test]
fn r821_3_two_different_formals_are_certified() {
    assert_eq!(
        read_at(ROOTS, "two", "distinct", 0, 1),
        (A5SiteProofVerdict::Clear, SAME_POINTEE_MUT)
    );
}

/// R821-3 item 1: one formal handed twice is one outside object.
#[test]
fn r821_3_control_one_formal_handed_twice_is_not_certified() {
    assert_eq!(
        read_at(ROOTS, "two", "twice", 0, 1),
        (A5SiteProofVerdict::Overlapping, "a5-not-proven-disjoint")
    );
}

/// R821-3 item 1: two places inside one formal are one outside object.
#[test]
fn r821_3_control_two_places_inside_one_formal_are_not_certified() {
    assert_eq!(
        read_at(ROOTS, "two", "fields", 0, 1),
        (A5SiteProofVerdict::Overlapping, "a5-not-proven-disjoint")
    );
}

/// R821-3 item 1 (wave-6o 123 note 1): a formal whose address is taken may be
/// reassigned through that address, so it is not the outside caller's pointer.
#[test]
fn r821_3_control_a_formal_whose_address_is_taken_is_not_certified() {
    assert_eq!(
        read_at(ROOTS, "two", "address_taken", 0, 1),
        (A5SiteProofVerdict::Overlapping, "a5-not-proven-disjoint")
    );
}

/// The review's finding 1: a place reached through a pointer loaded from the
/// formal (`&mut (*(*l).head).next`) is not a place inside `l`'s object.
#[test]
fn r821_review_control_a_place_through_a_loaded_pointer_is_not_certified() {
    assert_eq!(
        read_at(ROOTS, "two", "link", 0, 1),
        (A5SiteProofVerdict::Overlapping, "a5-not-proven-disjoint")
    );
}

/// The review's finding 5: a formal assigned inside a closure of the entry.
#[test]
fn r821_review_control_a_formal_assigned_in_a_closure_is_not_certified() {
    assert_eq!(
        read_at(ROOTS, "two", "in_closure", 0, 1),
        (A5SiteProofVerdict::Overlapping, "a5-not-proven-disjoint")
    );
}

/// The review's finding 5: an entry the program calls through an extern
/// declaration of its own symbol.
#[test]
fn r821_review_control_an_entry_called_by_its_symbol_is_not_certified() {
    assert_eq!(
        read_at(ROOTS, "two", "by_symbol", 0, 1),
        (A5SiteProofVerdict::Overlapping, "a5-not-proven-disjoint")
    );
}
