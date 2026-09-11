//! Row (a) CALL-CLOBBER-SCOPE: a callee can only write what it can reach.

use rustc_hash::FxHashSet;
use rustc_middle::mir::{
    Body, Local, Location, TerminatorKind, UnwindAction, VarDebugInfoContents,
};

use super::{
    call_reach::EscapeFacts,
    objects::{ObjectFacts, ObjectRoot, ObjectSet},
    tests_return_origin::{named_function, with_program},
};
use crate::{
    analyses::{
        borrow_ownership::{
            crate_slots::CrateSlots, export::PlaceKey, origin_flow::analyze_program_origin_flow,
            source_events,
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

/// The object state of one fixture crate, built exactly as production builds it.
fn object_facts(program: &RustProgram<'_>) -> ObjectFacts {
    let slots = CrateSlots::build(program);
    let events = source_events::collect(program);
    let flows = analyze_program_origin_flow(program);
    ObjectFacts::analyze(program, &slots, &events, &flows)
}

fn named_local(body: &Body<'_>, name: &str) -> Local {
    let found: Vec<_> = body
        .var_debug_info
        .iter()
        .filter_map(|info| {
            if info.name.as_str() != name {
                return None;
            }
            let VarDebugInfoContents::Place(place) = info.value else {
                return None;
            };
            place.as_local()
        })
        .collect();
    assert_eq!(found.len(), 1, "one exact source local {name}");
    found[0]
}

fn cell(
    facts: &ObjectFacts,
    function: rustc_span::def_id::LocalDefId,
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

/// A-W01, the `url_get_hostname` anchor. `protocol` is a closed-Fresh return; a
/// non-allocator local call sits between it and its `free`. `keep` is an
/// unrelated incoming reference. Before row (a) the middle call clobbers every
/// cell, so the freed operand reads Unknown and overlaps `keep`; after it, the
/// freed operand keeps its exact Fresh root and `keep` survives.
const ANCHOR: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); }
unsafe fn get_protocol(u: *mut u8) -> *mut u8 { malloc(8) }
unsafe fn get_auth(u: *mut u8) -> *mut u8 { u }
pub unsafe fn hostname(u: *mut u8, keep: *const u8) -> u8 {
    let protocol = get_protocol(u);
    let value = *keep;
    let _auth = get_auth(u);
    free(protocol as *mut core::ffi::c_void);
    value
}
"#;

/// A-W02: the same shape, except `protocol`'s own address escapes before the
/// middle call. The callee could reach that cell, so Unknown must be preserved
/// and `keep` must NOT survive.
const ANCHOR_ADDRESS_TAKEN: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); }
unsafe fn get_protocol(u: *mut u8) -> *mut u8 { malloc(8) }
unsafe fn get_auth(u: *mut u8) -> *mut u8 { u }
unsafe fn stash(slot: *mut *mut u8) { let _ = *slot; }
pub unsafe fn hostname(u: *mut u8, keep: *const u8) -> u8 {
    let mut protocol = get_protocol(u);
    let value = *keep;
    stash(&raw mut protocol);
    let _auth = get_auth(u);
    free(protocol as *mut core::ffi::c_void);
    value
}
"#;

/// A-W08 must-not-move: the `buffer_free` self-free pair stays Raw.
const SELF_FREE_PAIR: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct Buffer { alloc: *mut u8 }
pub unsafe fn buffer_free(s: *mut Buffer) {
    free((*s).alloc as *mut core::ffi::c_void);
    free(s as *mut core::ffi::c_void);
}
"#;

#[test]
fn a_w01_fresh_return_survives_a_non_allocator_local_call() {
    assert!(
        super::tests::accepts(ANCHOR, &[("hostname", 2, 0)]),
        "the middle call cannot reach `protocol`'s own cell, so the free keeps its exact Fresh root and the \
         unrelated incoming reference is not charged for it"
    );
}

#[test]
fn a_w02_an_address_taken_local_is_still_clobbered() {
    assert!(
        !super::tests::accepts(ANCHOR_ADDRESS_TAKEN, &[("hostname", 2, 0)]),
        "once `protocol`'s address escapes, a callee can reach that cell and Unknown must be preserved"
    );
}

#[test]
fn a_w08_buffer_free_self_free_pair_stays_raw() {
    assert!(
        !super::tests::accepts(SELF_FREE_PAIR, &[("buffer_free", 1, 0)]),
        "row (a) must not promote the self-free pair: freeing the container retires the subject itself"
    );
}

/// A-W03 (required by R318-4): a pointer stored BEHIND an argument is memory,
/// not a caller local, so an opaque local call must still clobber it. The
/// selection is at depth 1 -- the cell reached by dereferencing the argument.
const DEPTH_ONE_BEHIND_ARGUMENT: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
unsafe fn opaque(slot: *mut *mut u8) -> *mut u8 { *slot }
pub unsafe fn deep(pp: *mut *mut u8) -> *mut u8 {
    let inner = *pp;
    let _echo = opaque(pp);
    free(inner as *mut core::ffi::c_void);
    *pp
}
"#;

/// A-W03 is REPORT-ONLY, not an assertion, and that is a finding rather than a
/// concession. A-K01 (preserve depth >= 1 cells too) leaves this fixture green,
/// so an assertion here would witness nothing. The representation is why:
///   * a projected store (`*pp = ...`) is not `place.as_local()`, so `write`
///     falls to the whole-state `clobber` -- a depth >= 1 cell is therefore
///     never refined to a distinct known root;
///   * the only known depth >= 1 roots are a parameter's `Input` cells, and
///     `(Input, Input)` pairs to `PossibleInputAlias`, so preserving such a cell
///     instead of clobbering it does not change any overlap verdict.
/// So no fixture in this representation can make the depth >= 1 clobber
/// observable through `accepts`. The probe records the measurement; the
/// discriminating witness R318-4 asks for needs either a different observation
/// channel or row (b)'s Field roots, which do refine depth >= 1.
#[test]
fn a_w03_probe_depth_one_cell_behind_an_argument() {
    let accepted = super::tests::accepts(DEPTH_ONE_BEHIND_ARGUMENT, &[("deep", 1, 1)]);
    println!(
        "receipt.A-W03 depth1_behind_argument_accepted={accepted} (report-only: A-K01 cannot flip it)"
    );
}

/// A-W03 asserting arm (R318-4, R320-2). The `accepts` channel cannot see the
/// depth >= 1 clobber -- that is the measured finding the probe above records --
/// but the object state can. Here the opaque callee *holds the argument*, so it
/// really can write the cell behind it; preserving that cell would be unsound,
/// not merely imprecise. A-K01 (preserve depth >= 1 cells) flips this exact
/// assertion, which is what makes the depth >= 1 clobber witnessed rather than
/// declared-redundant.
#[test]
fn a_w03_depth_one_cell_behind_a_passed_argument_is_clobbered() {
    with_program(DEPTH_ONE_BEHIND_ARGUMENT, |program| {
        let caller = named_function(program, "deep");
        let callee = named_function(program, "opaque");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
        let pp = named_local(&body, "pp");
        let calls: Vec<_> = body
            .basic_blocks
            .iter_enumerated()
            .filter_map(|(block, data)| {
                let call = data.terminator().as_call(program.tcx)?;
                if !matches!(call.func, CallKind::FreeStanding(function) if function == callee) {
                    return None;
                }
                let TerminatorKind::Call {
                    target: Some(target),
                    ..
                } = data.terminator().kind
                else {
                    panic!("fixture opaque call must have a normal successor");
                };
                Some((
                    Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                    target,
                ))
            })
            .collect();
        assert_eq!(calls.len(), 1, "one exact opaque call");
        let (site, target) = calls[0];
        drop(body);
        let facts = object_facts(program);
        assert_eq!(
            cell(&facts, caller, site, pp, 1),
            ObjectSet {
                roots: FxHashSet::from_iter([ObjectRoot::Input {
                    function: caller,
                    parameter: pp,
                    depth: 1,
                }]),
                unknown: false,
            },
            "before the call the cell behind the argument is the exact Input root, so this witness is not vacuous"
        );
        let at = Location {
            block: target,
            statement_index: 0,
        };
        assert!(
            facts.has_location(caller, at),
            "normal successor is reachable"
        );
        // The clobber raises `unknown`; it does not erase the roots, which stay
        // as a partial may-set. `unknown` is the fact overlap consumes, so it is
        // the fact asserted here.
        let after = cell(&facts, caller, at, pp, 1);
        assert!(
            after.unknown,
            "a callee holding the argument can write the cell behind it, so the depth-1 root must not survive as exact evidence: {after:?}"
        );
    });
}

/// A-W04: the same anchor as A-W01, with the middle call made UNKNOWN -- once
/// foreign, once indirect through a function pointer. Neither callee is visible
/// to the analysis, and the seat predicted both keep the whole-state clobber.
/// They do not, and they should not: reachability, not knowledge of the callee,
/// is what bounds the clobber. No callee of any kind can name a caller's MIR
/// local unless that local's own address escaped, so the narrowing applies to
/// an unknown callee exactly as it does to a known one -- and the escaping arm
/// below is what holds that line.
const FOREIGN_MIDDLE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); fn touch(p: *mut u8); }
unsafe fn get_protocol(u: *mut u8) -> *mut u8 { malloc(8) }
pub unsafe fn hostname(u: *mut u8, keep: *const u8) -> u8 {
    let protocol = get_protocol(u);
    let value = *keep;
    touch(u);
    free(protocol as *mut core::ffi::c_void);
    value
}
"#;

const FOREIGN_MIDDLE_ADDRESS_TAKEN: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); fn stash(slot: *mut *mut u8); fn touch(p: *mut u8); }
unsafe fn get_protocol(u: *mut u8) -> *mut u8 { malloc(8) }
pub unsafe fn hostname(u: *mut u8, keep: *const u8) -> u8 {
    let mut protocol = get_protocol(u);
    let value = *keep;
    stash(&raw mut protocol);
    touch(u);
    free(protocol as *mut core::ffi::c_void);
    value
}
"#;

const INDIRECT_MIDDLE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); }
unsafe fn get_protocol(u: *mut u8) -> *mut u8 { malloc(8) }
unsafe fn get_auth(u: *mut u8) -> *mut u8 { u }
pub unsafe fn hostname(u: *mut u8, keep: *const u8) -> u8 {
    let protocol = get_protocol(u);
    let value = *keep;
    let via: unsafe fn(*mut u8) -> *mut u8 = get_auth;
    let _auth = via(u);
    free(protocol as *mut core::ffi::c_void);
    value
}
"#;

const INDIRECT_MIDDLE_ADDRESS_TAKEN: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); }
unsafe fn get_protocol(u: *mut u8) -> *mut u8 { malloc(8) }
unsafe fn get_auth(u: *mut u8) -> *mut u8 { u }
unsafe fn stash(slot: *mut *mut u8) { let _ = *slot; }
pub unsafe fn hostname(u: *mut u8, keep: *const u8) -> u8 {
    let mut protocol = get_protocol(u);
    let value = *keep;
    stash(&raw mut protocol);
    let via: unsafe fn(*mut u8) -> *mut u8 = get_auth;
    let _auth = via(u);
    free(protocol as *mut core::ffi::c_void);
    value
}
"#;

#[test]
fn a_w04_an_unknown_callee_is_bounded_by_reachability_not_by_knowledge() {
    assert!(
        super::tests::accepts(FOREIGN_MIDDLE, &[("hostname", 2, 0)]),
        "a foreign callee cannot name `protocol`'s own cell either"
    );
    assert!(
        super::tests::accepts(INDIRECT_MIDDLE, &[("hostname", 2, 0)]),
        "an indirect callee cannot name `protocol`'s own cell either"
    );
}

#[test]
fn a_w04_an_unknown_callee_still_clobbers_an_escaped_local() {
    assert!(
        !super::tests::accepts(FOREIGN_MIDDLE_ADDRESS_TAKEN, &[("hostname", 2, 0)]),
        "an escaped cell is reachable from a foreign callee and must stay Unknown"
    );
    assert!(
        !super::tests::accepts(INDIRECT_MIDDLE_ADDRESS_TAKEN, &[("hostname", 2, 0)]),
        "an escaped cell is reachable from an indirect callee and must stay Unknown"
    );
}

/// A-W05: the unwind edge. `call_effect` runs once per successor, and the
/// clobber does not depend on `normal`; a callee that unwinds has still run,
/// wholly or in part, so the unwind successor needs exactly the same narrowed
/// clobber as the normal one. `Guard` keeps a real cleanup edge alive across
/// the observed call; `kept` never escapes and `escaped` does, both exactly
/// Fresh before the call.
const UNWIND_EDGE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; }
pub struct Guard(u8);
impl Drop for Guard { fn drop(&mut self) {} }
unsafe fn origin(u: *mut u8) -> *mut u8 { u }
pub unsafe fn caller(u: *mut u8) -> *mut u8 {
    let _guard = Guard(0);
    let kept = malloc(8);
    let mut escaped = malloc(8);
    let slot = &raw mut escaped;
    let _echo = origin(u);
    let _seen = *slot;
    kept
}
"#;

#[test]
fn a_w05_the_unwind_successor_carries_the_same_narrowed_clobber() {
    with_program(UNWIND_EDGE, |program| {
        let caller = named_function(program, "caller");
        let callee = named_function(program, "origin");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
        let kept = named_local(&body, "kept");
        let escaped = named_local(&body, "escaped");
        let calls: Vec<_> = body
            .basic_blocks
            .iter_enumerated()
            .filter_map(|(block, data)| {
                let call = data.terminator().as_call(program.tcx)?;
                if !matches!(call.func, CallKind::FreeStanding(function) if function == callee) {
                    return None;
                }
                let TerminatorKind::Call {
                    target: Some(target),
                    unwind,
                    ..
                } = data.terminator().kind
                else {
                    panic!("fixture origin call must have a normal successor");
                };
                Some((
                    Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                    target,
                    unwind,
                ))
            })
            .collect();
        assert_eq!(calls.len(), 1, "one exact observed local call");
        let (site, target, unwind) = calls[0];
        let UnwindAction::Cleanup(cleanup) = unwind else {
            panic!("fixture must keep a real cleanup edge, found {unwind:?}");
        };
        assert!(
            body.basic_blocks[cleanup].is_cleanup,
            "the unwind successor must be a cleanup block"
        );
        assert_eq!(
            body.basic_blocks.predecessors()[cleanup].as_slice(),
            &[site.block],
            "the cleanup block is entered from the observed call alone, so no other edge supplies its state"
        );
        drop(body);
        let facts = object_facts(program);
        let before_kept = cell(&facts, caller, site, kept, 0);
        let before_escaped = cell(&facts, caller, site, escaped, 0);
        for (name, before) in [("kept", &before_kept), ("escaped", &before_escaped)] {
            assert!(
                !before.unknown && before.roots.len() == 1,
                "{name} must be exactly one known root before the call, or this witness is vacuous: {before:?}"
            );
            assert!(
                before.roots.iter().all(
                    |root| matches!(root, ObjectRoot::Fresh { frame, .. } if *frame == caller)
                ),
                "{name} must be a caller-frame Fresh root before the call: {before:?}"
            );
        }
        for successor in [cleanup, target] {
            let at = Location {
                block: successor,
                statement_index: 0,
            };
            assert!(
                facts.has_location(caller, at),
                "successor {successor:?} is reachable"
            );
            assert_eq!(
                cell(&facts, caller, at, kept, 0),
                before_kept,
                "the non-escaping local survives the call on successor {successor:?}"
            );
            let after = cell(&facts, caller, at, escaped, 0);
            assert!(
                after.unknown,
                "the escaped local is clobbered on successor {successor:?}: {after:?}"
            );
        }
    });
}

/// A-W06: a pointer stored into a global is reachable from every callee. The
/// narrowing preserves nothing about it, because a store through a static's
/// address is a projected store and projected stores keep the whole-state
/// clobber. The anchor A-W01 is the discriminating sibling: this fixture is
/// A-W01 plus the one global store.
const GLOBAL_CARRIER: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut core::ffi::c_void); }
static mut SINK: *mut u8 = core::ptr::null_mut();
unsafe fn get_protocol(u: *mut u8) -> *mut u8 { malloc(8) }
unsafe fn get_auth(u: *mut u8) -> *mut u8 { u }
pub unsafe fn hostname(u: *mut u8, keep: *const u8) -> u8 {
    let protocol = get_protocol(u);
    let value = *keep;
    SINK = protocol;
    let _auth = get_auth(u);
    free(protocol as *mut core::ffi::c_void);
    value
}
"#;

#[test]
fn a_w06_a_pointer_published_to_a_global_is_not_preserved() {
    assert!(
        !super::tests::accepts(GLOBAL_CARRIER, &[("hostname", 2, 0)]),
        "once `protocol` is reachable through a static, the middle call may free or move it and the \
         unrelated incoming reference must stay protected"
    );
}

/// A-W07: an aggregate field address takes the whole local's address. The
/// escape set is asserted directly, because a struct field's pointer VALUE is
/// not a cell of the object state -- only the local's own address is at stake,
/// and `&local.field` hands a callee exactly that. The third arm is the
/// precision claim the narrowing rests on: a leading `Deref` takes the address
/// of memory behind a pointer, never the pointer's own cell.
const FIELD_ADDRESS: &str = r#"
#[repr(C)] pub struct Holder { slot: *mut u8 }
unsafe fn stash(slot: *mut *mut u8) { let _ = *slot; }
pub unsafe fn caller(u: *mut u8, behind: *mut Holder) -> *mut u8 {
    let mut holder = Holder { slot: u };
    let untouched = u;
    stash(&raw mut holder.slot);
    stash(&raw mut (*behind).slot);
    untouched
}
"#;

#[test]
fn a_w07_an_aggregate_field_address_escapes_its_local() {
    with_program(FIELD_ADDRESS, |program| {
        let caller = named_function(program, "caller");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
        let escapes = EscapeFacts::of_body(&body);
        assert!(
            escapes.escapes(named_local(&body, "holder")),
            "`&raw mut holder.slot` hands a callee the address of `holder`'s own storage"
        );
        assert!(
            !escapes.escapes(named_local(&body, "untouched")),
            "a local whose address is never taken must not be swept in with it"
        );
        assert!(
            !escapes.escapes(named_local(&body, "behind")),
            "`&raw mut (*behind).slot` takes the address of memory BEHIND `behind`, not of `behind` itself"
        );
        assert_eq!(
            escapes.escaping_locals(),
            1,
            "exactly one local of this body escapes"
        );
    });
}
