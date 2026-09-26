//! F01 role candidates: compiler inputs only; no accepted borrow proof is inferred
//! merely from a candidate. Replay must still validate the selected reader arm.

use super::graph_tests::with_facts;

#[test]
fn f01_readonly_traversal_records_exact_field_and_borrowed_return_roles() {
    with_facts(
        r#"
pub struct Node { left: *mut Node, right: *mut Node, value: i32 }
pub unsafe fn minimum(mut node: *mut Node) -> *mut Node {
    while !(*node).left.is_null() { node = (*node).left; }
    node
}
pub unsafe fn right_value(node: *mut Node) -> i32 {
    let child = (*node).right;
    (*child).value
}
"#,
        |facts| {
            let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            let document = serde_json::to_value(&snapshot).unwrap();
            let readers = document["reader_candidates"]
                .as_array()
                .expect("F01 reader occurrence family");
            for name in ["minimum", "right_value"] {
                let selected: Vec<_> = readers
                    .iter()
                    .filter(|row| row["function"] == name)
                    .collect();
                assert!(
                    !selected.is_empty(),
                    "{name} must retain its exact field reads"
                );
                for row in selected {
                    assert!(row["block"].is_number() && row["statement"].is_number());
                    assert!(
                        row["field_key"]
                            .as_str()
                            .is_some_and(|key| key.starts_with("Node::field"))
                    );
                    assert_eq!(row["origin_parameter"], 1);
                    assert_eq!(
                        row["replay_required"], true,
                        "static use roles do not imply a checked loan"
                    );
                }
            }
            let functions = document["reader_functions"]
                .as_array()
                .expect("exact borrowed function roles");
            let minimum = functions
                .iter()
                .find(|row| row["function"] == "minimum")
                .unwrap();
            assert_eq!(
                minimum["returned_parameters"],
                serde_json::json!([1]),
                "the traversal's returned descendant must keep its actual input origin"
            );
        },
    );
}

#[test]
fn f01_consuming_retaining_and_unknown_return_functions_are_not_readers() {
    with_facts(
        r#"
unsafe extern "C" { fn free(p: *mut i32); fn retain(p: *mut i32); fn opaque() -> *mut i32; }
pub struct H { ptr: *mut i32 }
pub unsafe fn release(h: &mut H) { free(h.ptr); }
pub unsafe fn retaining(h: &H) { retain(h.ptr); }
pub unsafe fn unknown(h: &H) -> *mut i32 { let _value = *h.ptr; opaque() }
"#,
        |facts| {
            let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            let document = serde_json::to_value(&snapshot).unwrap();
            assert!(
                document["reader_candidates"]
                    .as_array()
                    .expect("reader candidates")
                    .is_empty()
            );
            assert!(
                document["reader_functions"]
                    .as_array()
                    .expect("reader functions")
                    .is_empty()
            );
        },
    );
}

#[test]
fn f01_pointer_addresses_and_aggregate_returns_are_retaining_outputs() {
    with_facts(
        r#"
pub struct Saved { p: *mut i32 }
pub unsafe fn address(p: *mut i32) -> usize { p as usize }
pub unsafe fn nested(p: *mut i32) -> Saved { Saved { p } }
pub unsafe fn repeated(p: *mut i32) -> [*mut i32; 2] { [p; 2] }
"#,
        |facts| {
            assert!(
                facts.reader_plan.functions.is_empty(),
                "integer and non-scalar results must not hide a retained pointer: {:?}",
                facts.reader_plan.functions
            );
        },
    );
}

#[test]
fn f03_borrowed_struct_reader_keeps_the_field_owner_and_zero_view() {
    let fixture = super::tests::inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub struct H { ptr: *mut i32 }
pub unsafe fn make() -> H { let owner = malloc(4); H { ptr: owner } }
pub unsafe fn peek(h: &H) -> i32 { let view = h.ptr; *view }
"#,
    );
    let readers = fixture.origin_json["licensing"][0]["reader_candidates"]
        .as_array()
        .unwrap();
    assert!(
        readers.iter().any(|row| row["function"] == "peek"),
        "native-reference field read must have a static candidate"
    );
    fixture.assert_kind("H.ptr", super::super::SlotKind::Owning);
    fixture.assert_kind("make::owner", super::super::SlotKind::Owning);
    fixture.assert_kind("peek::view", super::super::SlotKind::Ref);
    fixture.assert_kind("peek::h", super::super::SlotKind::Ref);
    assert!(
        fixture
            .export
            .ownership_equations
            .as_ref()
            .unwrap()
            .iter()
            .any(|row| row.point.function.as_deref() == Some("peek")
                && row.operation.starts_with("guarded-reader")),
        "the selected role must refine its actual SSA transfer"
    );
}

#[test]
fn f04_reader_transfer_proof_is_exported_beside_the_static_candidate() {
    with_facts(
        r#"
pub struct H { ptr: *mut i32 }
pub unsafe fn peek(h: &H) -> i32 { let view = h.ptr; *view }
"#,
        |facts| {
            let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            let document = serde_json::to_value(&snapshot).unwrap();
            let proofs = document["reader_transfers"]
                .as_array()
                .expect("reader transfer coverage family");
            assert_eq!(proofs.len(), 1);
            assert_eq!(proofs[0]["coverage"]["state"], "present");
            assert!(
                !proofs[0]["coverage"]["value"]
                    .as_array()
                    .unwrap()
                    .is_empty()
            );
            snapshot.validate().unwrap();
        },
    );
}

#[test]
fn f04_selected_reader_has_an_exact_replay_loan_and_field_origin_receipt() {
    let fixture = super::tests::inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub struct H { ptr: *mut i32 }
pub unsafe fn make() -> H { let owner = malloc(4); H { ptr: owner } }
pub unsafe fn peek(h: &H) -> i32 { let view = h.ptr; *view }
"#,
    );
    fixture.assert_kind("H.ptr", super::super::SlotKind::Owning);
    let receipts = fixture.origin_json["reader_replay"]
        .as_array()
        .expect("accepted reader replay evidence");
    let peek: Vec<_> = receipts
        .iter()
        .filter(|row| row["candidate"]["function"] == "peek")
        .collect();
    assert_eq!(peek.len(), 1);
    assert_eq!(peek[0]["matched_loans"], 1);
    assert_eq!(peek[0]["origin_linked"], true);
    assert_eq!(peek[0]["candidate"]["field_key"], "H::field0@d0");
}

#[test]
fn f05_a_retained_partner_free_cannot_leave_an_owning_field_alias() {
    let fixture = super::tests::inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub struct H { ptr: *mut i32 }
pub unsafe fn make() -> H {
    let owner = malloc(4);
    let holder = H { ptr: owner };
    free(owner);
    holder
}
pub unsafe fn peek(h: &H) -> i32 { let view = h.ptr; *view }
"#,
    );
    // Returning an unobserved dangling raw value is not itself a dereference.
    // This assertion concerns the ownership output, not execution of peek.
    fixture.assert_kind("H.ptr", super::super::SlotKind::Raw);
}

#[test]
fn f05_a_shared_struct_reference_does_not_authorize_taking_its_field_owner() {
    let fixture = super::tests::inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub struct H { ptr: *mut i32 }
pub unsafe fn make() -> H { let owner = malloc(4); H { ptr: owner } }
pub unsafe fn peek(h: &H) -> i32 { let view = h.ptr; *view }
pub unsafe fn release(h: &H) { free(h.ptr); }
"#,
    );
    fixture.assert_kind("H.ptr", super::super::SlotKind::Raw);
}

#[test]
fn f05_omitting_an_unknown_store_cannot_create_field_support() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn opaque() -> *mut i32; }
pub struct H { ptr: *mut i32 }
pub unsafe fn make() -> H { let p = malloc(4); H { ptr: p } }
pub unsafe fn replace(h: &mut H) { h.ptr = opaque(); }
pub unsafe fn peek(h: &H) -> i32 { let view = h.ptr; *view }
"#,
        |facts| {
            let frozen = facts.licensing.as_ref().unwrap();
            assert!(
                !frozen
                    .field_support
                    .iter()
                    .find(|row| row.field_key == "H::field0@d0")
                    .unwrap()
                    .supported()
            );
            let mut omitted = facts.field_support_inputs.clone();
            let before = omitted.stores.len();
            omitted.stores.retain(|row| row.site.function != "replace");
            assert!(omitted.stores.len() < before);
            let audit = super::field_support::audit(
                facts,
                &omitted,
                &frozen.matched,
                &frozen.value_origins,
            );
            assert!(
                !audit
                    .iter()
                    .find(|row| row.field_key == "H::field0@d0")
                    .unwrap()
                    .supported(),
                "a recorded source-level field store cannot disappear from all-store coverage"
            );
        },
    );
}

#[test]
fn f04_reader_precision_tails_have_explicit_zero_view_obligations() {
    with_facts(
        r#"
pub struct Node { left: *mut Node, right: *mut Node, value: i32 }
pub unsafe fn peek(node: &Node) -> i32 { let view = node.left; (*view).value }
"#,
        |facts| {
            let rows: Vec<_> = facts
                .equations
                .iter()
                .filter(|row| {
                    row.point.function.as_deref() == Some("peek")
                        && row.operation == "guarded-reader-view-tail"
                })
                .collect();
            assert_eq!(
                rows.len(),
                2,
                "both unpaired destination descendants need guarded zero obligations"
            );
            let frozen = facts.licensing.as_ref().unwrap();
            assert!(frozen.reader_transfers.iter().all(|proof| matches!(
                proof.coverage,
                super::super::ownership_occurrence::Availability::Present(_)
            )));
            let mut omitted = facts.clone();
            omitted
                .equations
                .retain(|row| row.ordinal != rows[0].ordinal);
            assert!(
                super::readers::audit_transfers(&omitted, frozen.matched.guard_aliases())
                    .iter()
                    .all(|proof| matches!(
                        proof.coverage,
                        super::super::ownership_occurrence::Availability::Missing(_)
                    )),
                "an unrepresented precision tail is not a complete reader proof"
            );
        },
    );
}

#[test]
fn f04_pair_cardinality_cannot_hide_an_omitted_source_component() {
    use super::{
        super::ownership_occurrence::{Availability::Present, PathStep},
        facts::EquationId,
    };
    with_facts(
        r#"pub struct H { ptr: *mut i32 }
pub unsafe fn peek(h: &H) -> i32 { let view = h.ptr; *view }"#,
        |facts| {
            let mut corrupt = facts.clone();
            let template = facts
                .equations
                .iter()
                .find(|row| row.operation.starts_with("guarded-reader-"))
                .unwrap()
                .clone();
            let transfer = template.transfer.as_ref().unwrap();
            let (Present(source), Present(destination)) = (&transfer.source, &transfer.destination)
            else {
                panic!("actual transfer bindings")
            };
            for ordinal in [source.consume, destination.consume] {
                let consume = corrupt
                    .consumes
                    .iter_mut()
                    .find(|row| row.ordinal == ordinal)
                    .unwrap();
                let (Present(base), Present(projected), Present(paths)) = (
                    &mut consume.base,
                    &mut consume.projected,
                    &mut consume.pointer_paths,
                ) else {
                    panic!("actual consume windows")
                };
                base.use_end += 2;
                base.def_end += 2;
                projected.use_end += 2;
                projected.def_end += 2;
                let head = paths[(projected.use_start - base.use_start) as usize].clone();
                for index in 0..2 {
                    let mut path = head.clone();
                    path.extend([
                        PathStep::Deref,
                        PathStep::Field {
                            structure: "Payload".into(),
                            index,
                            name: format!("f{index}"),
                        },
                    ]);
                    paths.push(path);
                }
            }
            let mut aliases = facts
                .licensing
                .as_ref()
                .unwrap()
                .matched
                .guard_aliases()
                .clone();
            let alias = aliases[&EquationId {
                construction: template.point.construction,
                ordinal: template.ordinal,
            }];
            for destination_offset in 1..=2 {
                let mut row = template.clone();
                let transfer = row.transfer.as_mut().unwrap();
                let (Present(source), Present(destination)) =
                    (&mut transfer.source, &mut transfer.destination)
                else {
                    unreachable!()
                };
                // Both rows claim source component 1; source component 2 disappears.
                for (binding, offset) in [(source, 1), (destination, destination_offset)] {
                    binding.use_var += offset;
                    binding.def_var += offset;
                    let consume = corrupt
                        .consumes
                        .iter()
                        .find(|c| c.ordinal == binding.consume)
                        .unwrap();
                    let (Present(base), Present(paths)) = (&consume.base, &consume.pointer_paths)
                    else {
                        unreachable!()
                    };
                    binding.path = paths[(binding.use_var - base.use_start) as usize].clone();
                    binding.pointer_depth = binding
                        .path
                        .iter()
                        .filter(|p| matches!(p, PathStep::Deref))
                        .count();
                }
                let (Present(source), Present(destination)) =
                    (&transfer.source, &transfer.destination)
                else {
                    unreachable!()
                };
                transfer.source_use = source.use_var;
                transfer.source_def = source.def_var;
                transfer.destination_use = destination.use_var;
                transfer.destination_def = destination.def_var;
                row.variables = vec![destination.def_var, source.def_var, source.use_var];
                let destination_use = transfer.destination_use;
                row.ordinal = corrupt.equations.len();
                aliases.insert(
                    EquationId {
                        construction: row.point.construction,
                        ordinal: row.ordinal,
                    },
                    alias,
                );
                let mut old = row.clone();
                old.ordinal += 1;
                old.operation = "assume".into();
                old.value = Some(false);
                old.guard = None;
                old.assumption_class = Some("ssa-transfer".into());
                old.variables = vec![destination_use];
                corrupt.equations.extend([row, old]);
            }
            assert!(
                super::readers::audit_transfers(&corrupt, &aliases)
                    .iter()
                    .all(|proof| matches!(
                        proof.coverage,
                        super::super::ownership_occurrence::Availability::Missing(_)
                    )),
                "pair count plus head coverage cannot authenticate every component"
            );
        },
    );
}

#[test]
fn f06_bst_left_and_right_readers_preserve_both_owning_fields() {
    let fixture = super::tests::inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut Node; }
pub struct Node { left: *mut Node, right: *mut Node, value: i32 }
pub unsafe fn make() -> Node {
    let left = malloc(core::mem::size_of::<Node>());
    let right = malloc(core::mem::size_of::<Node>());
    Node { left, right, value: 0 }
}
pub unsafe fn left_value(node: &Node) -> i32 { let view = node.left; (*view).value }
pub unsafe fn right_value(node: &Node) -> i32 { let view = node.right; (*view).value }
"#,
    );
    for field in ["Node.left", "Node.right"] {
        fixture.assert_kind(field, super::super::SlotKind::Owning);
    }
    for function in ["left_value", "right_value"] {
        fixture.assert_kind(&format!("{function}::view"), super::super::SlotKind::Ref);
        fixture.assert_kind(&format!("{function}::node"), super::super::SlotKind::Ref);
        assert!(
            fixture.origin_json["reader_replay"]
                .as_array()
                .unwrap()
                .iter()
                .any(|row| row["candidate"]["function"] == function
                    && row["matched_loans"] == 1
                    && row["origin_linked"] == true)
        );
    }
}

#[test]
fn f07_quadtree_nw_and_se_readers_have_independent_field_support() {
    let fixture = super::tests::inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub struct Bounds { nw: *mut i32, se: *mut i32 }
pub unsafe fn make() -> Bounds {
    let nw = malloc(4); let se = malloc(4); Bounds { nw, se }
}
pub unsafe fn northwest(bounds: &Bounds) -> i32 { let view = bounds.nw; *view }
pub unsafe fn southeast(bounds: &Bounds) -> i32 { let view = bounds.se; *view }
"#,
    );
    for field in ["Bounds.nw", "Bounds.se"] {
        fixture.assert_kind(field, super::super::SlotKind::Owning);
    }
    for function in ["northwest", "southeast"] {
        fixture.assert_kind(&format!("{function}::view"), super::super::SlotKind::Ref);
        assert!(fixture.origin_json["reader_replay"].as_array().unwrap().iter().any(|row|
            row["candidate"]["function"] == function && row["origin_linked"] == true));
    }
}
