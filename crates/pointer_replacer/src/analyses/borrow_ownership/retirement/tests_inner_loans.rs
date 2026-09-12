//! R343-1 P1S-INNER-LOAN-REPRESENTATION witnesses.

use super::{
    inner_loan,
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
