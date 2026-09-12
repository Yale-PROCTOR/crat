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

/// Each escape form once, and one local that stays home so the relation
/// discriminates in both directions.
const ESCAPES: &str = r#"
unsafe fn opaque(slot: *mut u8) -> *mut u8 { slot }
pub unsafe fn caller(out: *mut *mut u8, base: *mut u8) -> *mut u8 {
    let argument: *mut u8 = base;
    let _echo = opaque(argument);
    let stored: *mut u8 = base;
    *out = stored;
    let mut addressed: *mut u8 = base;
    let _taken: *mut *mut u8 = &raw mut addressed;
    let kept: *mut u8 = base;
    let copied: *mut u8 = kept;
    let _reread: *mut u8 = copied;
    let returned: *mut u8 = base;
    returned
}
"#;

#[test]
fn c_w09_every_escape_form_is_an_escape_and_a_kept_value_is_not() {
    with_program(ESCAPES, |program| {
        let caller = named_function(program, "caller");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
        let escapes = ValueEscapes::of_body(&body);
        for name in ["argument", "stored", "addressed", "returned"] {
            assert!(
                escapes.escapes(named_local(&body, name)),
                "{name} leaves the frame and must count as an escape"
            );
        }
        // `kept` flows only into other locals and never leaves: assignments are
        // exactly the shape the copy graph DOES follow, so its closure is complete
        // and the relation must not claim it escaped.
        for name in ["kept", "copied", "_reread"] {
            assert!(
                !escapes.escapes(named_local(&body, name)),
                "{name} never leaves the frame; its closure is complete"
            );
        }
    });
}

#[test]
fn c_w09_a_frame_with_no_escape_at_all_escapes_nothing() {
    const HOME: &str = r#"
pub unsafe fn caller(base: *mut u8) {
    let kept: *mut u8 = base;
    let _copied: *mut u8 = kept;
}
"#;
    with_program(HOME, |program| {
        let caller = named_function(program, "caller");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
        let escapes = ValueEscapes::of_body(&body);
        assert!(!escapes.escapes(named_local(&body, "kept")));
        assert!(
            !escapes.escapes(named_local(&body, "_copied")),
            "an empty escape set is reachable, so the relation is not constant-true"
        );
    });
}

/// The same frame three ways: a holder whose last use precedes the free, one used
/// after it, and one kept alive only through a raw copy.
const LIVENESS: &str = r#"
unsafe extern "C" { fn free(p: *mut core::ffi::c_void); }
unsafe fn opaque(slot: *mut u8) -> *mut u8 { slot }
pub unsafe fn dead(base: *mut u8, other: *mut u8) {
    let holder: *mut u8 = base;
    let _early = opaque(holder);
    free(other as *mut core::ffi::c_void);
}
pub unsafe fn live(base: *mut u8, other: *mut u8) -> *mut u8 {
    let holder: *mut u8 = base;
    free(other as *mut core::ffi::c_void);
    opaque(holder)
}
pub unsafe fn through_raw_copy(base: *mut u8, other: *mut u8) -> *mut u8 {
    let holder: *mut u8 = base;
    let carried: *mut u8 = holder;
    free(other as *mut core::ffi::c_void);
    opaque(carried)
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

fn liveness_after_free(code: &str, function: &str, holder: &str) -> bool {
    let mut answer = None;
    with_program(code, |program| {
        let wanted = named_function(program, function);
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(wanted)
            .borrow();
        let local = named_local(&body, holder);
        let liveness = inner_loan::ClosureLiveness::of_body(&body, local);
        answer = Some(liveness.live_after(&body, free_call(&body)));
    });
    answer.expect("the fixture compiled")
}

#[test]
fn c_w01_a_holder_whose_last_use_precedes_the_free_is_not_live_after_it() {
    assert!(!liveness_after_free(LIVENESS, "dead", "holder"));
}

#[test]
fn c_w02_a_holder_used_after_the_free_is_live_after_it() {
    assert!(liveness_after_free(LIVENESS, "live", "holder"));
}

#[test]
fn c_w03_a_holder_kept_alive_only_through_a_raw_copy_is_live() {
    assert!(
        liveness_after_free(LIVENESS, "through_raw_copy", "holder"),
        "a closure member's use is the holder's use; this is the case the \
         retirement comment names"
    );
}

#[test]
fn c_w03_the_closure_is_what_carries_it() {
    with_program(LIVENESS, |program| {
        let wanted = named_function(program, "through_raw_copy");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(wanted)
            .borrow();
        let holder = named_local(&body, "holder");
        let carried = named_local(&body, "carried");
        let liveness = inner_loan::ClosureLiveness::of_body(&body, holder);
        assert!(
            liveness.members().contains(&carried),
            "the raw copy is a closure member, or C-W03 would pass for the wrong reason"
        );
    });
}
