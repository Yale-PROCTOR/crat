//! The object facts' scope at a projected store and a `Drop` (N), and at
//! `core::ptr` pointer arithmetic (O). Relay era-5c/264, R1317-4.
//!
//! N: a store through memory, or drop glue, changes a MIR local's own value only
//! if that local's address was taken, so it clobbers what a callee could reach
//! (`clobber_callee_reachable`) and the local whose own storage it writes. A
//! formal's depth-0 cell survives it.
//!
//! O: an `offset` / `add` / `sub` of `core::ptr` that leaves its allocation (one
//! past the end allowed) is UB in Rust and in C, so under §28 the result points
//! into the receiver's objects. `wrapping_*` and `byte_*` stay Unknown.

use rustc_hash::FxHashSet;
use rustc_middle::mir::{Body, Local, Location, TerminatorKind};
use rustc_span::def_id::LocalDefId;

use super::{
    objects::{ObjectFacts, ObjectRoot, ObjectSet},
    tests_call_reach::{named_local, object_facts},
    tests_return_origin::{named_function, with_program},
};
use crate::{
    analyses::{
        borrow_ownership::{
            crate_slots::CrateSlots,
            export::{PlaceKey, ProjKey},
        },
        mir::TerminatorExt,
    },
    utils::rustc::RustProgram,
};

fn cell(
    facts: &ObjectFacts,
    function: LocalDefId,
    at: Location,
    local: Local,
    depth: u8,
) -> ObjectSet {
    facts.pointer_at(
        function,
        at,
        &PlaceKey {
            local,
            proj: Vec::new(),
        },
        depth,
    )
}

fn input(function: LocalDefId, parameter: Local, depth: u8) -> ObjectSet {
    ObjectSet {
        roots: FxHashSet::from_iter([ObjectRoot::Input {
            function,
            parameter,
            depth,
        }]),
        unknown: false,
    }
}

/// The location right after the one statement assigning to `(*local)`.
fn after_store_through(body: &Body<'_>, local: Local) -> Location {
    let found: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .flat_map(|(block, data)| {
            data.statements
                .iter()
                .enumerate()
                .filter_map(move |(index, statement)| {
                    let (place, _) = statement.kind.as_assign()?;
                    (place.local == local && PlaceKey::from_place(*place).proj == [ProjKey::Deref])
                        .then_some(Location {
                            block,
                            statement_index: index + 1,
                        })
                })
        })
        .collect();
    assert_eq!(found.len(), 1, "one store through {local:?}");
    found[0]
}

/// The location right after the one statement assigning to `local` itself.
fn after_assign(body: &Body<'_>, local: Local) -> Location {
    let found: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .flat_map(|(block, data)| {
            data.statements
                .iter()
                .enumerate()
                .filter_map(move |(index, statement)| {
                    let (place, _) = statement.kind.as_assign()?;
                    (place.as_local() == Some(local)).then_some(Location {
                        block,
                        statement_index: index + 1,
                    })
                })
        })
        .collect();
    assert_eq!(found.len(), 1, "one assignment to {local:?}");
    found[0]
}

/// The one `Drop` of `local`: its own location and its normal successor.
fn drop_of(body: &Body<'_>, local: Local) -> (Location, Location) {
    let found: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .filter(|(_, data)| !data.is_cleanup)
        .filter_map(|(block, data)| {
            let TerminatorKind::Drop { place, target, .. } = data.terminator().kind else {
                return None;
            };
            (place.as_local() == Some(local)).then_some((
                Location {
                    block,
                    statement_index: data.statements.len(),
                },
                Location {
                    block: target,
                    statement_index: 0,
                },
            ))
        })
        .collect();
    assert_eq!(found.len(), 1, "one drop of {local:?}: {found:?}");
    found[0]
}

/// The normal successor of the one call whose destination is `local`.
fn after_call_into(body: &Body<'_>, local: Local) -> Location {
    let found: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(_, data)| {
            let TerminatorKind::Call {
                destination,
                target: Some(target),
                ..
            } = data.terminator().kind
            else {
                return None;
            };
            (destination.as_local() == Some(local)).then_some(Location {
                block: target,
                statement_index: 0,
            })
        })
        .collect();
    assert_eq!(found.len(), 1, "one call into {local:?}");
    found[0]
}

/// The local `caller` hands `callee` as its first argument at their one call,
/// for an `accepts` selection.
fn first_argument_local(code: &str, caller: &str, callee: &str) -> u32 {
    let found = std::sync::Mutex::new(Vec::new());
    with_program(code, |program| {
        let function = named_function(program, caller);
        let callee = named_function(program, callee).to_def_id();
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        for data in body.basic_blocks.iter() {
            let Some(call) = data.terminator().as_call(program.tcx) else {
                continue;
            };
            if call.func.did() != Some(callee) {
                continue;
            }
            let place = call.args[0].node.place().expect("the argument is a local");
            found
                .lock()
                .unwrap()
                .push(place.as_local().expect("a bare local").as_u32());
        }
    });
    let found = found.into_inner().unwrap();
    assert_eq!(found.len(), 1, "one call {caller} -> {callee}");
    found[0]
}

fn local_index(code: &str, function: &str, name: &str) -> u32 {
    let found = std::sync::Mutex::new(None);
    with_program(code, |program| {
        let function = named_function(program, function);
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        *found.lock().unwrap() = Some(named_local(&body, name).as_u32());
    });
    found.into_inner().unwrap().expect("the local")
}

fn with_body(
    program: &RustProgram<'_>,
    function: &str,
    check: impl FnOnce(LocalDefId, &Body<'_>, &ObjectFacts),
) {
    let function = named_function(program, function);
    let facts = object_facts(program);
    let body = program
        .tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    check(function, &body, &facts);
}

/// N1's shape: a formal `sig`, and a store of a byte through another formal
/// `other`. A `**` formal `pp` carries the depth-1 cell such a store may write.
const STORE_THROUGH_ANOTHER: &str = r#"
pub unsafe fn sign(sig: *mut u8, other: *mut u8, pp: *mut *mut u8) -> u8 {
    *other = 1;
    let seen = sig;
    *seen
}
"#;

/// N1: the formal's cell survives a store through another pointer. The store
/// cannot name `sig`'s own storage (its address is never taken), so `sig` keeps
/// its exact `Input` root; memory behind a pointer -- `pp`'s depth-1 cell -- is
/// still clobbered.
#[test]
fn e5c_w264_n1_a_formal_survives_a_store_through_another_pointer() {
    with_program(STORE_THROUGH_ANOTHER, |program| {
        with_body(program, "sign", |function, body, facts| {
            let sig = named_local(body, "sig");
            let pp = named_local(body, "pp");
            let at = after_store_through(body, named_local(body, "other"));
            assert_eq!(
                cell(facts, function, at, sig, 0),
                input(function, sig, 0),
                "`sig`'s own cell is not reachable from a store through `other`"
            );
            let behind = cell(facts, function, at, pp, 1);
            assert!(
                behind.unknown,
                "memory behind a pointer may be the stored cell: {behind:?}"
            );
        });
    });
}

/// The P01 shape (relay 263's `SPX_fors_sign::sig`): a store through another
/// formal, then the formal handed to a callee whose own `Vec` drop is routed up
/// the call while the reborrow of `(*sig)` is live.
const ROUTED_DROP: &str = r#"
#![allow(dead_code, unused_mut, unused_variables)]
pub unsafe fn leaf(out: *mut u8, n: usize) {
    let mut buf: Vec<u8> = ::std::vec::from_elem(0, n);
    *buf.as_mut_ptr() = 1;
    *out = *buf.as_ptr();
}
pub unsafe fn sign(sig: *mut u8, other: *mut u8, n: usize) {
    *other = 1;
    leaf(sig, n);
}
pub unsafe fn sign_drop(sig: *mut u8, n: usize) {
    {
        let mut own: Vec<u8> = ::std::vec::from_elem(0, n);
        *own.as_mut_ptr() = 1;
    }
    leaf(sig, n);
}
pub unsafe fn sign_add(sig: *mut u8, n: usize) {
    let s = sig.add(4);
    leaf(s, n);
}
"#;

/// N1b: end to end, the survival clears the routed drop's conflict. The
/// reborrow of `(*sig)` handed to `leaf` resolves to `sig`'s `Input` object,
/// which `leaf`'s fresh buffer is not; with the clobber it resolved to Unknown.
#[test]
fn e5c_w264_n1b_the_formal_s_reborrow_clears_a_routed_drop() {
    let argument = first_argument_local(ROUTED_DROP, "sign", "leaf");
    assert!(
        super::tests::accepts(ROUTED_DROP, &[("sign", 1, 0), ("sign", argument, 0)]),
        "the store through `other` cannot change `sig`, so its reborrow is not `leaf`'s buffer"
    );
}

/// N2's shape: `escaped`'s address is taken, and a store through that address
/// writes `escaped` itself.
const STORE_INTO_ESCAPED: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; }
pub unsafe fn caller(v: *mut u8) -> *mut u8 {
    let mut escaped = malloc(8);
    let slot = &raw mut escaped;
    *slot = v;
    escaped
}
"#;

/// N2: the address-taken local is still clobbered. `*slot = v` writes
/// `escaped`'s own storage; its exact `Fresh` root must not survive.
#[test]
fn e5c_w264_n2_an_address_taken_local_is_still_clobbered_by_a_store() {
    with_program(STORE_INTO_ESCAPED, |program| {
        with_body(program, "caller", |function, body, facts| {
            let escaped = named_local(body, "escaped");
            let slot = named_local(body, "slot");
            let before = cell(facts, function, after_assign(body, slot), escaped, 0);
            assert!(
                !before.unknown
                    && before.roots.len() == 1
                    && before
                        .roots
                        .iter()
                        .all(|root| matches!(root, ObjectRoot::Fresh { .. })),
                "`escaped` is exactly Fresh before the store, or this witness is vacuous: {before:?}"
            );
            let after = cell(facts, function, after_store_through(body, slot), escaped, 0);
            assert!(
                after.unknown,
                "the store through `slot` wrote `escaped`: {after:?}"
            );
        });
    });
}

/// N3's shape: an array-of-pointer local stored by index, then read through;
/// and a struct local stored by field, then read through.
const AGGREGATE_LOCALS: &str = r#"
#[repr(C)] pub struct Holder { pub slot: *mut u8 }
pub unsafe fn table(keep: *mut u8, i: usize) -> u8 {
    let mut slots: [*mut u8; 4] = [core::ptr::null_mut(); 4];
    slots[i] = keep;
    let got = slots[i];
    let through = *slots[i];
    let mut holder = Holder { slot: core::ptr::null_mut() };
    holder.slot = keep;
    let held = holder.slot;
    *got + through + *held
}
"#;

/// N3: a store into a local's own storage leaves no stale object behind,
/// because (a) only raw-pointer and reference locals have cells, so the
/// array and the struct have none, and (b) a read of an element or a field
/// of a local is Unknown. The build also clobbers the written local's row.
#[test]
fn e5c_w264_n3_an_array_of_pointers_has_no_cell_and_reads_unknown() {
    with_program(AGGREGATE_LOCALS, |program| {
        let slots = CrateSlots::build(program);
        with_body(program, "table", |function, body, facts| {
            let universe = &slots.fn_local_slots[&function];
            for name in ["slots", "holder"] {
                let local = named_local(body, name);
                assert!(
                    universe.slot_for_local_depth(local, 0).is_none(),
                    "`{name}` is an aggregate local and has no depth cell"
                );
            }
            for name in ["got", "held"] {
                let local = named_local(body, name);
                let value = cell(facts, function, after_assign(body, local), local, 0);
                assert!(
                    value.unknown,
                    "`{name}` is read out of a local's element or field: {value:?}"
                );
            }
            // The read through `slots[i]` -- `(*slots[i])`, or a `CopyForDeref`
            // temporary of `slots[i]` dereferenced -- finds no object either.
            let through = named_local(body, "through");
            let reads: Vec<_> = body
                .basic_blocks
                .iter_enumerated()
                .flat_map(|(block, data)| {
                    data.statements
                        .iter()
                        .enumerate()
                        .filter_map(move |(index, statement)| {
                            let (place, value) = statement.kind.as_assign()?;
                            if place.as_local() != Some(through) {
                                return None;
                            }
                            let rustc_middle::mir::Rvalue::Use(operand) = value else {
                                return None;
                            };
                            Some((
                                Location {
                                    block,
                                    statement_index: index,
                                },
                                PlaceKey::from_place(operand.place()?),
                            ))
                        })
                })
                .collect();
            assert_eq!(reads.len(), 1, "one read through an element: {reads:?}");
            let (at, read) = &reads[0];
            let storage = facts.storage_at(function, *at, read);
            assert!(
                storage.unknown,
                "the object read through an element is Unknown: {read:?} {storage:?}"
            );
        });
    });
}

/// N4: the formal's cell survives a `Drop` (`ROUTED_DROP`'s `sign_drop`: the
/// body's own `Vec` dropped at the end of its block). Drop glue reaches what
/// the dropped value reaches and what a callee could; `sig`'s own storage is
/// neither.
#[test]
fn e5c_w264_n4_a_formal_survives_a_drop() {
    with_program(ROUTED_DROP, |program| {
        with_body(program, "sign_drop", |function, body, facts| {
            let sig = named_local(body, "sig");
            let (_, after) = drop_of(body, named_local(body, "own"));
            assert!(facts.has_location(function, after), "the drop returns");
            assert_eq!(
                cell(facts, function, after, sig, 0),
                input(function, sig, 0),
                "dropping `own` cannot change `sig`"
            );
        });
    });
    with_program(DROP_BEHIND, |program| {
        with_body(program, "drop_behind", |function, body, facts| {
            let pp = named_local(body, "pp");
            let (at, after) = drop_of(body, named_local(body, "noisy"));
            assert_eq!(
                cell(facts, function, at, pp, 1),
                input(function, pp, 1),
                "`pp`'s depth-1 cell is exact before the drop, or this half is vacuous"
            );
            assert_eq!(cell(facts, function, after, pp, 0), input(function, pp, 0));
            let behind = cell(facts, function, after, pp, 1);
            assert!(
                behind.unknown,
                "drop glue may write memory behind a pointer: {behind:?}"
            );
        });
    });
}

/// N4's second shape: a guard with a user `Drop` and no call before it, so a
/// `**` formal's depth-1 cell is exact up to the drop.
const DROP_BEHIND: &str = r#"
pub struct Noisy(u8);
impl Drop for Noisy {
    fn drop(&mut self) {}
}
pub unsafe fn drop_behind(pp: *mut *mut u8) -> *mut u8 {
    {
        let noisy = Noisy(0);
    }
    *pp
}
"#;

/// N4b: end to end, the same survival across the body's own `Vec` drop clears
/// the routed drop's conflict.
#[test]
fn e5c_w264_n4b_a_reborrow_after_a_drop_clears_a_routed_drop() {
    let argument = first_argument_local(ROUTED_DROP, "sign_drop", "leaf");
    assert!(
        super::tests::accepts(
            ROUTED_DROP,
            &[("sign_drop", 1, 0), ("sign_drop", argument, 0)]
        ),
        "the drop of `own` cannot change `sig`, so its reborrow is not `leaf`'s buffer"
    );
}

/// N5's shape: a guard whose user `Drop` writes through a pointer to
/// `escaped`, dropped at the end of its block.
const USER_DROP: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; }
pub struct Guard(*mut *mut u8);
impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { *self.0 = core::ptr::null_mut(); }
    }
}
pub unsafe fn caller(v: *mut u8) -> *mut u8 {
    let mut escaped = malloc(8);
    {
        let guard = Guard(&raw mut escaped);
    }
    escaped
}
"#;

/// N5: a `Drop` whose user impl reaches an escaped local clobbers that local,
/// as before: the guard's drop glue may write `escaped`.
#[test]
fn e5c_w264_n5_a_user_drop_reaching_an_escaped_local_still_clobbers_it() {
    with_program(USER_DROP, |program| {
        with_body(program, "caller", |function, body, facts| {
            let escaped = named_local(body, "escaped");
            let (at, after) = drop_of(body, named_local(body, "guard"));
            let before = cell(facts, function, at, escaped, 0);
            assert!(
                !before.unknown
                    && before.roots.len() == 1
                    && before
                        .roots
                        .iter()
                        .all(|root| matches!(root, ObjectRoot::Fresh { .. })),
                "`escaped` is exactly Fresh before the drop, or this witness is vacuous: {before:?}"
            );
            assert!(facts.has_location(function, after), "the drop returns");
            let after = cell(facts, function, after, escaped, 0);
            assert!(
                after.unknown,
                "the guard's drop wrote `escaped` through its address: {after:?}"
            );
        });
    });
}

/// O1's shape: `offset`, `add` and `sub` of `*mut`, and `add` of `*const`.
const ARITHMETIC: &str = r#"
pub unsafe fn walk(p: *mut u8, n: isize) -> u8 {
    let a = p.offset(n);
    let b = a.add(2);
    let c = b.sub(1);
    let d = (p as *const u8).add(1);
    *c + *d
}
pub unsafe fn walk_deep(pp: *mut *mut u8) -> *mut u8 {
    let q = pp.add(1);
    *q
}
"#;

/// O1: `offset` / `add` / `sub` of `core::ptr` keep the receiver's objects.
#[test]
fn e5c_w264_o1_offset_add_sub_keep_the_receiver_s_objects() {
    with_program(ARITHMETIC, |program| {
        with_body(program, "walk", |function, body, facts| {
            let p = named_local(body, "p");
            for name in ["a", "b", "c", "d"] {
                let local = named_local(body, name);
                assert_eq!(
                    cell(facts, function, after_call_into(body, local), local, 0),
                    input(function, p, 0),
                    "`{name}` points into `p`'s object"
                );
            }
        });
        // Only depth 0 is carried: `*q` is another element than `*pp`.
        with_body(program, "walk_deep", |function, body, facts| {
            let pp = named_local(body, "pp");
            let q = named_local(body, "q");
            let at = after_call_into(body, q);
            assert_eq!(cell(facts, function, at, q, 0), input(function, pp, 0));
            let behind = cell(facts, function, at, q, 1);
            assert!(behind.unknown, "`*q` is not `*pp`: {behind:?}");
        });
    });
}

/// O1b: end to end, the reborrow of an `add` result is the receiver's object,
/// not `leaf`'s buffer.
#[test]
fn e5c_w264_o1b_an_offset_s_reborrow_clears_a_routed_drop() {
    let s = local_index(ROUTED_DROP, "sign_add", "s");
    let argument = first_argument_local(ROUTED_DROP, "sign_add", "leaf");
    assert!(
        super::tests::accepts(
            ROUTED_DROP,
            &[("sign_add", s, 0), ("sign_add", argument, 0)]
        ),
        "`s` points into `sig`'s object, which `leaf`'s fresh buffer is not"
    );
}

/// O2's shape: `core::ops::Add::add` on a reference receiver (a name match on
/// `add` would carry `t`'s object to a fresh block), a local function named
/// `offset`, and `wrapping_add` / `byte_add`.
const NOT_ARITHMETIC: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; }
pub struct Thing(u8);
impl<'a> core::ops::Add<usize> for &'a Thing {
    type Output = *mut u8;
    fn add(self, k: usize) -> *mut u8 { unsafe { malloc(k) } }
}
unsafe fn offset(p: *mut u8, k: isize) -> *mut u8 { p.wrapping_offset(k) }
pub unsafe fn ctl(t: &Thing, p: *mut u8, k: usize) -> u8 {
    let x = t + k;
    let y = offset(p, 1);
    let z = p.wrapping_add(k);
    let w = p.byte_add(1);
    *x + *y + *z + *w
}
"#;

/// O2: only `core::ptr`'s three are arithmetic. `Add::add`'s, the local
/// `offset`'s, `wrapping_add`'s and `byte_add`'s results stay Unknown.
#[test]
fn e5c_w264_o2_a_name_match_is_not_pointer_arithmetic() {
    with_program(NOT_ARITHMETIC, |program| {
        with_body(program, "ctl", |function, body, facts| {
            let t = named_local(body, "t");
            let x = named_local(body, "x");
            let receiver = cell(facts, function, after_call_into(body, x), t, 0);
            assert_eq!(
                receiver,
                input(function, t, 0),
                "`t` is exactly its Input root at the call, or this control is vacuous"
            );
            for name in ["x", "y", "z", "w"] {
                let local = named_local(body, name);
                let value = cell(facts, function, after_call_into(body, local), local, 0);
                assert!(
                    value.unknown,
                    "`{name}` is not `core::ptr` arithmetic: {value:?}"
                );
            }
        });
    });
}

/// N6's shape (the adversarial review of `4a79ab406`): `x`'s address is copied
/// into `px`, `x` is then written directly, and its value is read back through
/// `px` and freed. The free releases `sig`'s object. `stale_store` adds a store
/// through another formal after the read, which before N clobbered `y`.
const STALE_THROUGH_ADDRESS: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); }
pub unsafe fn stale(sig: *mut u8) {
    let mut x = malloc(8);
    let px = &raw mut x;
    x = sig;
    let y = *px;
    free(y as *mut core::ffi::c_void);
}
pub unsafe fn stale_store(sig: *mut u8, other: *mut u8) {
    let mut x = malloc(8);
    let px = &raw mut x;
    x = sig;
    let y = *px;
    *other = 0;
    free(y as *mut core::ffi::c_void);
}
"#;

/// N6: a direct write to an address-taken local ends every depth >= 1 copy of
/// its old value. `px`'s depth-1 cell held `x`'s malloc root; after `x = sig` the
/// read `y = *px` is not that root, and the free of `y` conflicts with `sig`.
#[test]
fn e5c_w264_n6_a_direct_write_to_an_escaped_local_ends_its_copies() {
    with_program(STALE_THROUGH_ADDRESS, |program| {
        for function in ["stale", "stale_store"] {
            with_body(program, function, |function, body, facts| {
                let y = named_local(body, "y");
                let value = cell(facts, function, after_assign(body, y), y, 0);
                assert!(
                    value.unknown,
                    "`y` is read through `px` after `x = sig`: {value:?}"
                );
            });
        }
    });
    for function in ["stale", "stale_store"] {
        assert!(
            !super::tests::accepts(STALE_THROUGH_ADDRESS, &[(function, 1, 0)]),
            "{function} frees `sig`'s object through `px`"
        );
    }
}
