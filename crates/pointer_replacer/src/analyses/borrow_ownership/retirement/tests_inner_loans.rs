//! R343-1 P1S-INNER-LOAN-REPRESENTATION witnesses.

use super::{
    inner_loan::{self, ValueEscapes},
    tests_call_reach::named_local,
    tests_return_origin::{named_function, with_program},
};
use crate::analyses::borrow_ownership::{
    crate_slots::CrateSlots,
    slots::{SlotId, SlotOwner},
    solver::SlotRef,
};

/// One parameter with an inner cell, one non-parameter local with an inner cell,
/// and a field: exactly the three cases the obligation rule has to separate.
const HOLDERS: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
unsafe fn opaque(slot: *mut u8) -> *mut u8 { slot }
pub struct Holder { pub cell: *mut u8 }
pub unsafe fn caller(param: *mut *mut u8, holder: *mut Holder) -> *mut u8 {
    let mut base: *mut u8 = opaque(core::ptr::null_mut());
    let inner: *mut *mut u8 = &mut base;
    let loaded: *mut u8 = *inner;
    let _echo = opaque(loaded);
    (*holder).cell = loaded;
    free(loaded as *mut core::ffi::c_void);
    *param
}
"#;

/// The (local, depth) of every depth >= 1 slot of one function.
fn inner_cells(
    program: &crate::utils::rustc::RustProgram<'_>,
    slots: &CrateSlots,
    function: rustc_span::def_id::LocalDefId,
) -> Vec<(usize, u8)> {
    let _ = program;
    let universe = &slots.fn_local_slots[&function];
    (0..universe.len())
        .filter_map(|index| {
            let slot = universe.slot(SlotId::from_usize(index));
            let SlotOwner::Local(local) = slot.owner else {
                return None;
            };
            (slot.depth > 0).then_some((local.as_usize(), slot.depth))
        })
        .collect()
}

#[test]
fn c_w00_an_obligation_exists_for_the_non_parameter_inner_holder_and_no_other() {
    with_program(HOLDERS, |program| {
        let slots = CrateSlots::build(program);
        let caller = named_function(program, "caller");
        let mut keys: Vec<_> = inner_loan::obligations(program, &slots, |_| true)
            .into_iter()
            .filter(|row| row.key.function == caller)
            .map(|row| (row.key.local.as_usize(), row.key.depth))
            .collect();
        keys.sort_unstable();
        let cells = inner_cells(program, &slots, caller);
        assert!(!cells.is_empty(), "the fixture must have depth >= 1 cells");
        // `caller`'s parameters are locals 1 and 2; everything above is a body local.
        let mut expected: Vec<_> = cells
            .iter()
            .copied()
            .filter(|(local, _)| *local > 2)
            .collect();
        expected.sort_unstable();
        assert!(
            !expected.is_empty(),
            "the fixture must have a NON-parameter inner cell, or it witnesses nothing"
        );
        assert!(
            cells.iter().any(|(local, _)| *local <= 2),
            "the fixture must also have a PARAMETER inner cell, or the rule is untested"
        );
        assert_eq!(
            keys, expected,
            "obligations are exactly the non-parameter inner holders"
        );
    });
}

#[test]
fn c_w00_every_obligation_names_where_its_value_is_defined() {
    with_program(HOLDERS, |program| {
        let slots = CrateSlots::build(program);
        let rows = inner_loan::obligations(program, &slots, |_| true);
        assert!(!rows.is_empty(), "the fixture must produce obligations");
        for row in rows {
            assert!(row.key.depth >= 1, "no obligation at depth 0");
            assert!(
                matches!(row.key.holder, SlotRef::Local(function, _) if function == row.key.function),
                "the holder names its own frame"
            );
            assert!(
                !row.reservations.is_empty(),
                "an obligation with no definition site could not resolve its object: {row:?}"
            );
        }
    });
}

#[test]
fn c_w00_a_field_owned_inner_holder_gets_no_obligation() {
    // R342-4 keeps the field object out of this build, so a field-owned holder
    // has no obligation and therefore keeps today's demotion (C-W05).
    with_program(HOLDERS, |program| {
        let slots = CrateSlots::build(program);
        assert!(
            slots.field_slots.len() > 0,
            "the fixture must actually register a field slot"
        );
        assert!(
            inner_loan::obligations(program, &slots, |_| true)
                .iter()
                .all(|row| matches!(row.key.holder, SlotRef::Local(..))),
            "no field-owned obligation is minted in this build"
        );
    });
}

#[test]
fn c_w00_a_raw_holder_gets_no_obligation() {
    with_program(HOLDERS, |program| {
        let slots = CrateSlots::build(program);
        assert!(
            inner_loan::obligations(program, &slots, |_| false).is_empty(),
            "only Ref carriers hold loans (R251); a Raw holder has nothing to protect"
        );
    });
}

/// Each escape form once, on a real inner holder, so the rule is witnessed where
/// it acts rather than on the relation in isolation.
const ESCAPES: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
unsafe fn opaque(slot: *mut u8) -> *mut u8 { slot }
pub unsafe fn passed(other: *mut u8) {
    let mut base: *mut u8 = opaque(core::ptr::null_mut());
    let inner: *mut *mut u8 = &raw mut base;
    let loaded: *mut u8 = *inner;
    let _echo = opaque(loaded);
    free(other as *mut core::ffi::c_void);
}
pub unsafe fn stored(out: *mut *mut u8, other: *mut u8) {
    let mut base: *mut u8 = opaque(core::ptr::null_mut());
    let inner: *mut *mut u8 = &raw mut base;
    let loaded: *mut u8 = *inner;
    *out = loaded;
    free(other as *mut core::ffi::c_void);
}
pub unsafe fn returned(other: *mut u8) -> *mut u8 {
    let mut base: *mut u8 = opaque(core::ptr::null_mut());
    let inner: *mut *mut u8 = &raw mut base;
    let loaded: *mut u8 = *inner;
    free(other as *mut core::ffi::c_void);
    loaded
}
pub unsafe fn home(other: *mut u8) -> u8 {
    let mut base: *mut u8 = opaque(core::ptr::null_mut());
    let inner: *mut *mut u8 = &raw mut base;
    let byte: u8 = **inner;
    free(other as *mut core::ffi::c_void);
    byte
}
"#;

/// The location of the `free` call terminator in one function.
fn free_call(body: &rustc_middle::mir::Body<'_>) -> rustc_middle::mir::Location {
    let rows: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .filter(|(_, data)| {
            matches!(&data.terminator().kind,
                rustc_middle::mir::TerminatorKind::Call { func, .. }
                    if format!("{func:?}").contains("free"))
        })
        .map(|(block, data)| rustc_middle::mir::Location {
            block,
            statement_index: data.statements.len(),
        })
        .collect();
    assert_eq!(rows.len(), 1, "one exact free call");
    rows[0]
}

/// The three dispositions in one fixture: a dead inner holder, a live one, and an
/// escaped one whose liveness must never be consulted.
const DISPOSITIONS: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
unsafe fn opaque(slot: *mut u8) -> *mut u8 { slot }
pub unsafe fn dead(other: *mut u8) -> u8 {
    let mut base: *mut u8 = opaque(core::ptr::null_mut());
    let inner: *mut *mut u8 = &raw mut base;
    let byte: u8 = **inner;
    free(other as *mut core::ffi::c_void);
    byte
}
pub unsafe fn live(other: *mut u8) -> u8 {
    let mut base: *mut u8 = opaque(core::ptr::null_mut());
    let inner: *mut *mut u8 = &raw mut base;
    free(other as *mut core::ffi::c_void);
    **inner
}
pub unsafe fn through_raw_copy(other: *mut u8) -> u8 {
    let mut base: *mut u8 = opaque(core::ptr::null_mut());
    let inner: *mut *mut u8 = &raw mut base;
    let carried: *mut u8 = *inner;
    free(other as *mut core::ffi::c_void);
    *carried
}
pub unsafe fn escaped(other: *mut u8) -> *mut u8 {
    let mut base: *mut u8 = opaque(core::ptr::null_mut());
    let inner: *mut *mut u8 = &raw mut base;
    let loaded: *mut u8 = *inner;
    free(other as *mut core::ffi::c_void);
    opaque(loaded)
}
"#;

fn disposition_at_free(code: &str, function: &str, holder: &str) -> inner_loan::Disposition {
    let mut answer = None;
    with_program(code, |program| {
        let slots = CrateSlots::build(program);
        let loans = inner_loan::analyze(program, &slots, |_| true);
        let wanted = named_function(program, function);
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(wanted)
            .borrow();
        let local = named_local(&body, holder);
        answer = Some(loans.disposition(&body, wanted, local, 1, free_call(&body)));
    });
    answer.expect("the fixture compiled")
}

#[test]
fn c_w01_a_dead_inner_holder_is_dispositioned_dead() {
    assert_eq!(
        disposition_at_free(DISPOSITIONS, "dead", "inner"),
        inner_loan::Disposition::Dead
    );
}

#[test]
fn c_w02_a_live_inner_holder_is_dispositioned_live() {
    assert_eq!(
        disposition_at_free(DISPOSITIONS, "live", "inner"),
        inner_loan::Disposition::Live
    );
}

#[test]
fn c_w09_an_escaped_holder_is_unrepresented_and_its_liveness_is_never_consulted() {
    assert_eq!(
        disposition_at_free(DISPOSITIONS, "escaped", "inner"),
        inner_loan::Disposition::Unrepresented(inner_loan::Missing::Escaped)
    );
}

#[test]
fn c_w05_a_holder_with_no_obligation_is_unrepresented() {
    with_program(DISPOSITIONS, |program| {
        let slots = CrateSlots::build(program);
        let loans = inner_loan::analyze(program, &slots, |_| true);
        let wanted = named_function(program, "dead");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(wanted)
            .borrow();
        // Depth 7 is not a slot of anything: the lookup must fail closed rather
        // than answer for a holder it has no obligation for.
        assert_eq!(
            loans.disposition(
                &body,
                wanted,
                named_local(&body, "inner"),
                7,
                free_call(&body)
            ),
            inner_loan::Disposition::Unrepresented(inner_loan::Missing::NoObligation)
        );
    });
}

#[test]
fn c_w03_a_holder_kept_alive_only_through_a_raw_copy_is_live() {
    assert_eq!(
        disposition_at_free(DISPOSITIONS, "through_raw_copy", "inner"),
        inner_loan::Disposition::Live,
        "a closure member's use is the holder's use; this is the case the \
         retirement comment names"
    );
}

#[test]
fn c_w03_the_raw_copy_is_what_carries_it() {
    with_program(DISPOSITIONS, |program| {
        let slots = CrateSlots::build(program);
        let loans = inner_loan::analyze(program, &slots, |_| true);
        let wanted = named_function(program, "through_raw_copy");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(wanted)
            .borrow();
        let inner = named_local(&body, "inner");
        let carried = named_local(&body, "carried");
        let members = loans
            .members(wanted, inner, 1)
            .expect("the inner holder has an obligation");
        assert!(
            members.contains(&carried),
            "the raw copy is a closure member, or C-W03 would pass for the wrong reason"
        );
    });
}

#[test]
fn c_w08_the_disposition_can_be_asked_of_one_edge() {
    with_program(DISPOSITIONS, |program| {
        let slots = CrateSlots::build(program);
        let loans = inner_loan::analyze(program, &slots, |_| true);
        let wanted = named_function(program, "live");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(wanted)
            .borrow();
        let inner = named_local(&body, "inner");
        let free = free_call(&body);
        let successors: Vec<_> = body.basic_blocks[free.block]
            .terminator()
            .successors()
            .collect();
        assert!(
            successors
                .iter()
                .any(|&block| loans.disposition_on(wanted, inner, 1, block)
                    == inner_loan::Disposition::Live),
            "the successor carrying the later use answers Live on its own"
        );
        // An event on a cleanup edge is discharged by THAT edge: the per-edge
        // answer exists and is not the successor union.
        assert_eq!(
            loans.disposition_on(wanted, inner, 1, rustc_middle::mir::START_BLOCK),
            loans.disposition_on(wanted, inner, 1, successors[0]),
            "every block answers for itself"
        );
    });
}

#[test]
fn c_w09_every_escape_form_leaves_the_holder_unrepresented() {
    for function in ["passed", "stored", "returned"] {
        assert_eq!(
            disposition_at_free(ESCAPES, function, "inner"),
            inner_loan::Disposition::Unrepresented(inner_loan::Missing::Escaped),
            "{function}: the value leaves the frame, so its copy closure is incomplete"
        );
    }
}

#[test]
fn c_w09_a_holder_that_never_leaves_the_frame_is_decided_by_its_liveness() {
    assert_eq!(
        disposition_at_free(ESCAPES, "home", "inner"),
        inner_loan::Disposition::Dead,
        "a constant-true escape rule would satisfy the positive half and silently \
         disable the whole recovery"
    );
}
