//! Relay main/388 stage 2 (R1347-1), 270 row 6: a demoted holder pins the slots its VALUE can reach,
//! not the slots that merely copy from the same field elsewhere.

use super::{
    local_outcome::{copy_graph, directed_closure, directed_copies},
    tests_call_reach::named_local,
    tests_return_origin::{named_function, with_program},
};
use crate::analyses::borrow_ownership::{crate_slots::CrateSlots, solver::SlotRef};

/// One field, three frames: one stores a value into it, two load from it; and a frame whose loaded
/// value is handed to a call.
const FIELD: &str = r#"
pub struct Node {
    pub next: *mut Node,
}
pub struct Table {
    pub head: *mut Node,
}
unsafe fn keep(node: *mut Node) -> *mut Node {
    node
}
pub unsafe fn store_into(t: *mut Table, s: *mut Node) {
    let stored: *mut Node = s;
    (*t).head = stored;
}
pub unsafe fn load_from(t: *mut Table) {
    let loaded: *mut Node = (*t).head;
    let copied: *mut Node = loaded;
    let _ = copied;
}
pub unsafe fn other_load(t: *mut Table) {
    let elsewhere: *mut Node = (*t).head;
    let _ = elsewhere;
}
pub unsafe fn passes(t: *mut Table) {
    let handed: *mut Node = (*t).head;
    let _ = keep(handed);
}
"#;

/// Whether the closure of `function::holder` (depth 0) reaches `other_function::other` (depth 0).
fn reaches(holder: (&str, &str), other: (&str, &str)) -> bool {
    let mut answer = None;
    with_program(FIELD, |program| {
        let slots = CrateSlots::build(program);
        let slot = |(function, local): (&str, &str)| {
            let function = named_function(program, function);
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let id = slots.fn_local_slots[&function]
                .slot_for_local_depth(named_local(&body, local), 0)
                .expect("a registered depth-0 slot");
            SlotRef::Local(function, id)
        };
        let closure = directed_closure(
            slot(holder),
            &directed_copies(program, &slots),
            &copy_graph(program, &slots),
        );
        answer = Some(closure.contains(&slot(other)));
    });
    answer.expect("the fixture compiled")
}

/// (d): a value stored into a field reaches every load of that field, in every frame -- a dangling
/// value must not re-enter a Ref slot through the field.
#[test]
fn r388_d_a_field_store_reaches_every_load_of_the_field() {
    assert!(reaches(("store_into", "stored"), ("load_from", "copied")));
    assert!(reaches(
        ("store_into", "stored"),
        ("other_load", "elsewhere")
    ));
}

/// (d): a value LOADED from a field does not flow into it, so a slot copying from the same field in
/// another frame is not pinned (the `cc_hashtable_get::bucket` shape) -- the undirected closure
/// reached it through the field.
#[test]
fn r388_d_a_load_from_a_field_does_not_reach_another_frames_load() {
    assert!(reaches(("load_from", "loaded"), ("load_from", "copied")));
    assert!(!reaches(
        ("load_from", "loaded"),
        ("other_load", "elsewhere")
    ));
}

/// (d), fail closed: a value handed to a call leaves the graph, so its holder takes the undirected
/// closure and pins the other frame's load as before.
#[test]
fn r388_d_a_flow_through_a_call_argument_takes_the_undirected_closure() {
    assert!(reaches(("passes", "handed"), ("other_load", "elsewhere")));
}
