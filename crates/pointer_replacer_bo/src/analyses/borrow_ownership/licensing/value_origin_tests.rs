//! O02 alternatives from real zero-query compiler construction facts.

use super::{
    super::{
        ownership_boundary::{Role, Substitution, Variables},
        ownership_occurrence::Availability,
    },
    facts::{EquationId, Facts},
    graph_tests::with_facts,
    transport::Node,
    value_origins::{OriginAtom, ValueOrigins},
};

fn source(facts: &Facts, function: &str) -> (EquationId, Node) {
    let rows: Vec<_> = facts
        .equations
        .iter()
        .filter(|row| row.operation == "source" && row.point.function.as_deref() == Some(function))
        .collect();
    assert_eq!(rows.len(), 1, "one actual source endpoint in {function}");
    let row = rows[0];
    assert_eq!(
        row.endpoint.as_ref().expect("typed allocator").callee,
        "malloc"
    );
    (
        EquationId {
            construction: row.point.construction,
            ordinal: row.ordinal,
        },
        Node {
            construction: row.point.construction,
            var: row.variables[0],
        },
    )
}

fn boundary<'a>(
    facts: &'a Facts,
    function: &str,
    role: Role,
    callee: Option<&str>,
) -> &'a Substitution {
    let rows: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|row| {
            row.role == role
                && row.point.function.as_deref() == Some(function)
                && row.callee.as_deref() == callee
        })
        .collect();
    assert_eq!(rows.len(), 1, "one actual {role:?} boundary in {function}");
    assert!(!rows[0].matched.is_empty(), "represented pointer boundary");
    rows[0]
}

fn receiver(facts: &Facts, caller: &str, callee: &str) -> Node {
    let row = boundary(facts, caller, Role::ReturnReceiver, Some(callee));
    assert!(matches!(row.actual_occurrence, Availability::Present(_)));
    let Variables::UseDef { def_var, .. } = row.matched[0].actual else {
        panic!("actual receiver def")
    };
    Node {
        construction: row.point.construction,
        var: def_var,
    }
}

fn signature_node(row: &Substitution) -> Node {
    let Variables::Single { var } = row.matched[0].formal else {
        panic!("formal signature component")
    };
    Node {
        construction: row.point.construction,
        var,
    }
}

#[test]
fn o02_nullable_fresh_return_keeps_fresh_and_null_through_exact_wrapper_receivers() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn make(empty: bool) -> *mut i32 {
    if empty { 0 as *mut i32 } else { malloc(4) }
}
pub unsafe fn wrapper(empty: bool) -> *mut i32 { make(empty) }
pub unsafe fn run(empty: bool) -> *mut i32 { wrapper(empty) }
"#,
        |facts| {
            let (source_id, source_node) = source(facts, "make");
            let origins = ValueOrigins::build(facts);
            assert!(
                origins
                    .at(source_node)
                    .contains(&OriginAtom::Fresh(source_id))
            );
            for node in [
                receiver(facts, "wrapper", "make"),
                receiver(facts, "run", "wrapper"),
            ] {
                let alternatives = origins.at(node);
                assert!(
                    alternatives.contains(&OriginAtom::Fresh(source_id)),
                    "allocation origin must cross the exact return application"
                );
                assert!(
                    alternatives.contains(&OriginAtom::Null),
                    "the explicit null return is an alternative"
                );
                assert!(
                    alternatives
                        .iter()
                        .all(|atom| matches!(atom, OriginAtom::Fresh(_) | OriginAtom::Null)),
                    "complete fresh/null flow has no invented borrower or missing origin"
                );
                assert!(
                    origins.fresh_without_borrow(node),
                    "null does not erase positive non-borrow origin evidence"
                );
            }
        },
    );
}

#[test]
fn o02_borrowed_input_return_keeps_its_input_origin_and_cannot_become_fresh() {
    with_facts(
        r#"
pub unsafe fn borrowed(p: *mut i32) -> *mut i32 { let q = p; q }
"#,
        |facts| {
            let input = signature_node(boundary(facts, "borrowed", Role::Entry, None));
            let returned = signature_node(boundary(facts, "borrowed", Role::ExitReturn, None));
            let origins = ValueOrigins::build(facts);
            let alternatives = origins.at(returned);
            assert!(
                alternatives.contains(&OriginAtom::Input(input))
                    || alternatives.contains(&OriginAtom::Borrow(input)),
                "the real input-to-return route must survive"
            );
            assert!(
                alternatives
                    .iter()
                    .all(|atom| matches!(atom, OriginAtom::Input(_) | OriginAtom::Borrow(_)))
            );
            assert!(!origins.fresh_without_borrow(returned));
        },
    );
}

#[test]
fn o02_mixed_fresh_and_opaque_return_retains_unknown_and_refuses_complete_fresh_evidence() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn opaque() -> *mut i32; }
pub unsafe fn mixed(fresh: bool) -> *mut i32 { if fresh { malloc(4) } else { opaque() } }
pub unsafe fn run(fresh: bool) -> *mut i32 { mixed(fresh) }
"#,
        |facts| {
            let (source_id, _) = source(facts, "mixed");
            let node = receiver(facts, "run", "mixed");
            let origins = ValueOrigins::build(facts);
            let alternatives = origins.at(node);
            assert!(
                alternatives.contains(&OriginAtom::Fresh(source_id)),
                "retain the actual allocating arm"
            );
            assert!(
                alternatives
                    .iter()
                    .any(|atom| matches!(atom, OriginAtom::Unknown(_))),
                "opaque alternative cannot disappear behind a fresh path"
            );
            assert!(
                !origins.fresh_without_borrow(node),
                "a partial fresh route is not complete origin evidence"
            );
        },
    );
}

#[test]
fn o02_buffer_outer_origin_does_not_inherit_the_borrowed_character_field() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; }
pub struct Buffer { data: *mut u8, len: usize }
pub unsafe fn make(data: *mut u8) -> *mut Buffer {
    let buffer = malloc(core::mem::size_of::<Buffer>()) as *mut Buffer;
    (*buffer).data = data;
    (*buffer).len = 1;
    buffer
}
pub unsafe fn run(data: *mut u8) -> *mut Buffer { make(data) }
"#,
        |facts| {
            let (source_id, _) = source(facts, "make");
            let outer = receiver(facts, "run", "make");
            let origins = ValueOrigins::build(facts);
            let alternatives = origins.at(outer);
            assert!(alternatives.contains(&OriginAtom::Fresh(source_id)));
            assert!(
                alternatives
                    .iter()
                    .all(|atom| matches!(atom, OriginAtom::Fresh(_) | OriginAtom::Null)),
                "an input stored in Buffer.data does not supply the outer Buffer pointer"
            );
            assert!(origins.fresh_without_borrow(outer));
        },
    );
}

#[test]
fn o02_omitted_phi_alternative_cannot_create_complete_fresh_evidence() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn opaque() -> *mut i32; }
pub unsafe fn mixed(fresh: bool) -> *mut i32 { if fresh { malloc(4) } else { opaque() } }
pub unsafe fn run(fresh: bool) -> *mut i32 { mixed(fresh) }
"#,
        |facts| {
            let node = receiver(facts, "run", "mixed");
            assert!(!ValueOrigins::build(facts).fresh_without_borrow(node));
            let phi_ids: Vec<_> = facts
                .equations
                .iter()
                .filter(|row| {
                    row.point.function.as_deref() == Some("mixed")
                        && row.point.phase == "phi"
                        && row.operation == "equal"
                })
                .map(|row| row.ordinal)
                .collect();
            assert!(!phi_ids.is_empty());
            for id in phi_ids {
                let mut omitted = facts.clone();
                omitted.equations.retain(|row| {
                    !(row.point.function.as_deref() == Some("mixed") && row.ordinal == id)
                });
                assert!(
                    !ValueOrigins::build(&omitted).fresh_without_borrow(node),
                    "a missing return alternative must become Unknown, not a fresh-only proof"
                );
            }
        },
    );
}

#[test]
fn o02_missing_return_boundary_preserves_an_unknown_call_alternative() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn opaque() -> *mut i32; }
pub unsafe fn opaque_wrapper() -> *mut i32 { opaque() }
pub unsafe fn mixed(fresh: bool) -> *mut i32 {
    if fresh { malloc(4) } else { opaque_wrapper() }
}
pub unsafe fn run(fresh: bool) -> *mut i32 { mixed(fresh) }
"#,
        |facts| {
            let node = receiver(facts, "run", "mixed");
            assert!(!ValueOrigins::build(facts).fresh_without_borrow(node));
            let mut omitted = facts.clone();
            let before = omitted.boundary_substitutions.len();
            omitted.boundary_substitutions.retain(|row| {
                !(row.point.function.as_deref() == Some("opaque_wrapper")
                    && row.role == Role::ExitReturn)
            });
            assert_eq!(before - omitted.boundary_substitutions.len(), 1);
            assert!(
                !ValueOrigins::build(&omitted).fresh_without_borrow(node),
                "an unresolved call summary cannot vanish from the mixed return"
            );
        },
    );
}

#[test]
fn o02_missing_call_input_preserves_unknown_beside_fresh() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn mixed(fresh: bool, p: *mut i32) -> *mut i32 {
    if fresh { malloc(4) } else { p }
}
pub unsafe fn run(fresh: bool, p: *mut i32) -> *mut i32 { mixed(fresh, p) }
"#,
        |facts| {
            let node = receiver(facts, "run", "mixed");
            assert!(!ValueOrigins::build(facts).fresh_without_borrow(node));
            let mut omitted = facts.clone();
            let before = omitted.boundary_substitutions.len();
            omitted.boundary_substitutions.retain(|row| {
                !(row.point.function.as_deref() == Some("run") && row.role == Role::CallArgument)
            });
            assert!(omitted.boundary_substitutions.len() < before);
            let origins = ValueOrigins::build(&omitted);
            assert!(!origins.fresh_without_borrow(node));
            // R367-2: the atom the callee's unresolvable `Input` becomes is now
            // typed — `UnresolvedInput` keeps the formal port instead of losing
            // it. The claim this control makes is unchanged and is the first
            // assertion: the value is still not provably fresh. What the type
            // buys is checked here too — with the call's argument substitution
            // removed there is no consumed argument, so the only reader that
            // admits the atom refuses it.
            let unresolved: Vec<_> = origins
                .at(node)
                .into_iter()
                .filter(|atom| matches!(atom, OriginAtom::UnresolvedInput { .. }))
                .collect();
            assert!(!unresolved.is_empty(), "{:?}", origins.at(node));
            let call = super::matched::CallKey {
                construction: 0,
                caller: "run".to_owned(),
                block: 0,
                statement: 0,
                callee: "mixed".to_owned(),
            };
            for atom in &unresolved {
                assert!(
                    !super::fold_caller::returned_token(&omitted, &call, atom),
                    "no substitution, so no consumed argument to have returned"
                );
            }
        },
    );
}

#[test]
fn o02_unresolved_recursive_call_alternative_is_not_a_fresh_proof() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn cycle() -> *mut i32 { cycle() }
pub unsafe fn mixed(fresh: bool) -> *mut i32 {
    if fresh { malloc(4) } else { cycle() }
}
pub unsafe fn run(fresh: bool) -> *mut i32 { mixed(fresh) }
"#,
        |facts| {
            let node = receiver(facts, "run", "mixed");
            let origins = ValueOrigins::build(facts);
            assert!(
                !origins.fresh_without_borrow(node),
                "an unresolved recursion is a completeness hold, not a disappearing alternative"
            );
        },
    );
}

#[test]
fn o02_closed_value_origins_are_exported_and_metadata_revalidated() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn make() -> *mut i32 { malloc(4) }
pub unsafe fn run() -> *mut i32 { make() }
"#,
        |facts| {
            let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            let document = serde_json::to_value(&snapshot).unwrap();
            assert!(
                document.get("value_origins").is_some(),
                "immutable origin alternatives must survive the optional export"
            );
            assert!(
                document["no_ref_carriers"]
                    .as_array()
                    .is_some_and(|rows| !rows.is_empty()),
                "the non-Ref conclusion retains exact carrier/value keys"
            );
            snapshot.validate().unwrap();
        },
    );
}

#[test]
fn o03_native_reference_head_is_not_the_allocated_payload() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn fill(out: &mut *mut i32) { *out = malloc(4); }
"#,
        |facts| {
            assert!(
                facts.slot_refs.contains_key("fill::_1@d0"),
                "native reference has its own kind slot"
            );
            assert!(
                !facts
                    .raw_pointer_heads
                    .iter()
                    .any(|head| head.slot_key == "fill::_1@d0")
            );
            let frozen = facts.licensing.as_ref().unwrap();
            assert!(
                !frozen
                    .no_ref_carriers
                    .iter()
                    .any(|carrier| carrier.slot_key == "fill::_1@d0"),
                "the output payload cannot forbid the outer native reference"
            );
        },
    );
}

#[test]
fn o02_argument_derived_return_does_not_invent_a_consuming_input_contract() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn identity(p: *mut i32) -> *mut i32 { p }
pub unsafe fn run() -> i32 {
    let owner = malloc(4);
    let view = identity(owner);
    let value = *view;
    free(owner);
    value
}
"#,
        |facts| {
            let view = receiver(facts, "run", "identity");
            assert!(
                !ValueOrigins::build(facts).fresh_without_borrow(view),
                "a plain input-return relation can return a view of the caller's retained owner; it is not an OwnedInput contract"
            );
        },
    );
}
