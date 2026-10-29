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
        let (closure, _) = directed_closure(
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

/// R1352-1 (a): one frame per class of `COPY_METHODS`, each handing its result on to a field another
/// frame loads; `is_null` / `addr` / `offset_from` return no pointer; `write` writes the pointee.
const METHODS: &str = r#"
pub struct Node {
    pub next: *mut Node,
}
pub struct Table {
    pub head: *mut Node,
}
pub unsafe fn offsets(t: *mut Table, s: *mut Node) {
    let a: *mut Node = s.offset(1);
    let b: *mut Node = a.add(1);
    let c: *mut Node = b.wrapping_sub(1);
    let d: *mut Node = c.byte_add(0);
    (*t).head = d;
}
pub unsafe fn casts(t: *mut Table, s: *mut Node) {
    let a: *mut u8 = s.cast::<u8>();
    let b: *const u8 = a.cast_const();
    let c: *mut u8 = b.cast_mut();
    (*t).head = c.cast::<Node>();
}
pub unsafe fn borrows(t: *mut Table, s: *mut Node) {
    if let Some(r) = s.as_mut() {
        (*t).head = r;
    }
}
pub unsafe fn probes(s: *mut Node, o: *mut Node) -> bool {
    s.is_null() || s.addr() == 0 || s.offset_from(o) == 0
}
pub unsafe fn writes(p: *mut *mut Node, q: *mut Node) {
    p.write(q);
    let r: *mut Node = *p;
    let _ = r;
}
pub unsafe fn other_load(t: *mut Table) {
    let elsewhere: *mut Node = (*t).head;
    let _ = elsewhere;
}
extern "C" {
    fn memcpy(dest: *mut u8, src: *const u8, n: usize) -> *mut u8;
}
pub unsafe fn copies(p: *mut *mut Node, q: *mut *mut Node) {
    memcpy(p.cast::<u8>(), q.cast::<u8>().cast_const(), 8);
    let r: *mut Node = *p;
    let _ = r;
}
"#;

/// The closure of `function::holder` (depth 0) in `METHODS`: whether it reaches `other_load::
/// elsewhere`, and the first leak's kind.
fn method_closure(function: &str, holder: &str) -> (bool, Option<&'static str>) {
    let mut answer = None;
    with_program(METHODS, |program| {
        let slots = CrateSlots::build(program);
        let slot = |function: &str, local: &str| {
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
        let (closure, leak) = directed_closure(
            slot(function, holder),
            &directed_copies(program, &slots),
            &copy_graph(program, &slots),
        );
        answer = Some((
            closure.contains(&slot("other_load", "elsewhere")),
            leak.map(|(_, kind)| kind.label()),
        ));
    });
    answer.expect("the fixture compiled")
}

/// (a) the offset family (`offset`, `add`, `wrapping_sub`, `byte_add`): copies, no leak -- the value
/// reaches the field's load in another frame.
#[test]
fn r388_d_the_offset_family_is_a_copy() {
    assert_eq!(method_closure("offsets", "s"), (true, None));
}

/// (a) the cast family (`cast`, `cast_const`, `cast_mut`): copies, no leak.
#[test]
fn r388_d_the_cast_family_is_a_copy() {
    assert_eq!(method_closure("casts", "s"), (true, None));
}

/// (a) `as_mut` (and `as_ref`) is NOT a copy: the walk cannot follow its `Option<&mut T>` into the
/// payload (`if let Some(r)`), so modeling it as a copy would lose the value; it is a leak, and the
/// holder takes the undirected closure.
#[test]
fn r388_d_as_mut_is_a_leak() {
    assert_eq!(method_closure("borrows", "s").1, Some("library-argument"));
}

/// (a) `is_null` / `addr` / `offset_from` return no pointer: no edge and no leak.
#[test]
fn r388_d_a_pointer_probe_adds_nothing_and_leaks_nothing() {
    assert_eq!(method_closure("probes", "s"), (false, None));
}

/// (a) `p.write(q); r = *p`: a method that writes the pointee is a leak -- the walk does not carry
/// the store's edge `q -> *p` -- so `q`'s holder takes the undirected closure.
#[test]
fn r388_d_a_pointee_write_is_a_leak() {
    assert_eq!(method_closure("writes", "q").1, Some("library-argument"));
}

/// (b) a foreign `memcpy` argument is a leak of its own kind (split from the other foreign calls).
#[test]
fn r388_d_a_memcpy_argument_is_a_memcpy_leak() {
    assert_eq!(method_closure("copies", "q").1, Some("memcpy-argument"));
}
