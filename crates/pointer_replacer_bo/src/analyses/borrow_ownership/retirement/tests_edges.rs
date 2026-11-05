//! Additional coverage of the implemented retirement contract, not new RED
//! evidence. Fixtures are compiled for analysis and are never executed.

use rustc_hir::{ItemKind, OwnerNode};

use super::tests::accepts;
use crate::{
    analyses::borrow_ownership::{
        realloc::{self, OldResponsibility, ReallocOutcome, ReallocRetirementAvailability},
        source_events::{
            self, Coverage, SourceCondition, SourceEvents, SourceObject, SourceRegion, SourceRole,
        },
    },
    utils::rustc::RustProgram,
};

fn inventory(code: &str) -> SourceEvents {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        source_events::collect(&RustProgram {
            tcx,
            functions,
            structs,
        })
    })
    .unwrap_or_else(|error| error.raise())
}

#[test]
fn e5_p_d_null_free_keeps_the_unrelated_shared_entry() {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn null_free(p: *const u8) -> u8 {
    let value = *p;
    free(core::ptr::null_mut());
    value
}
"#;
    let events = inventory(CODE);
    let frees: Vec<_> = events
        .retirements
        .values()
        .filter(|event| event.key.role == SourceRole::Free)
        .collect();
    assert_eq!(frees.len(), 1, "the null operation stays inventoried");
    assert_eq!(frees[0].object, SourceObject::Null);
    assert_eq!(frees[0].coverage, Coverage::IrrelevantNull);
    assert!(
        accepts(CODE, &[("null_free", 1, 0)]),
        "None retires no incoming object"
    );
}

#[test]
fn e5_p_d_saved_original_retirement_survives_parameter_rebinding() {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn rebound(mut p: *const u8, replacement: *const u8) -> u8 {
    let original = p as *mut u8;
    let value = *p;
    p = replacement;
    free(original);
    value + *p
}
"#;
    assert!(
        !accepts(CODE, &[("rebound", 1, 0)]),
        "rebinding p cannot retire the protector of its incoming target"
    );
}

#[test]
fn e5_p_d_field_stored_retirement_alias_is_not_assumed_disjoint() {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
struct Holder { pointer: *mut u8 }
pub unsafe fn stored(p: *const u8) -> u8 {
    let value = *p;
    let mut holder = Holder { pointer: core::ptr::null_mut() };
    holder.pointer = p as *mut u8;
    let loaded = holder.pointer;
    free(loaded);
    value
}
"#;
    // This is a conservative coverage control: it does not assert that the
    // bounded object producer precisely represents field-memory flow.
    assert!(
        !accepts(CODE, &[("stored", 1, 0)]),
        "a stored/loaded alias must yield a conflict or typed decline, not disjointness"
    );
}

#[test]
fn e5_p_d_free_of_loaded_inner_pointer_checks_depth_one_entry() {
    const CODE: &str = r#"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn inner(pp: *const *mut u8) {
    let loaded = *pp;
    free(loaded);
}
"#;
    // The helper selects exactly d1; d0 and every other slot remain Raw.
    assert!(
        !accepts(CODE, &[("inner", 1, 1)]),
        "the inner incoming target must not disappear through a depth-zero mapping"
    );
}

#[test]
fn e5_p_d_pointer_cell_storage_death_is_not_incoming_heap_retirement() {
    const CODE: &str = r#"
pub unsafe fn scoped(p: *const u8) -> u8 {
    let value;
    {
        let cell = p;
        value = *cell;
    }
    value
}
"#;
    let events = inventory(CODE);
    let deaths: Vec<_> = events
        .retirements
        .values()
        .filter(|event| {
            event.key.role == SourceRole::StorageDead
                && matches!(event.object, SourceObject::PointerStorage(_))
        })
        .collect();
    assert!(
        !deaths.is_empty(),
        "the fixture needs an actual pointer storage death"
    );
    assert!(
        deaths
            .iter()
            .all(|event| event.region == SourceRegion::WholeStorage
                && event.coverage == Coverage::IrrelevantPointerStorage)
    );
    assert!(
        events
            .retirements
            .values()
            .all(|event| !matches!(event.key.role, SourceRole::Free | SourceRole::ReallocOld))
    );
    assert!(
        accepts(CODE, &[("scoped", 1, 0)]),
        "ending an unaddressed pointer cell does not free its incoming pointee"
    );
}

#[test]
fn e5_p_d_realloc_success_retires_protected_old_target_but_failure_does_not() {
    const CODE: &str = r#"
unsafe extern "C" {
    fn realloc(p: *mut u8, bytes: usize) -> *mut u8;
    fn free(p: *mut u8);
}
pub unsafe fn resize(p: *const u8) -> u8 {
    let value = *p;
    let result = realloc(p as *mut u8, 8);
    if result.is_null() { value } else { free(result); value }
}
"#;
    let events = inventory(CODE);
    assert_eq!(events.reallocations.len(), 1);
    let site = &events.reallocations[0];
    let cases = realloc::classify(site).expect("supported nonzero direct result test");
    assert_eq!(cases.len(), 2, "both source outcomes must remain feasible");
    let failure = cases
        .iter()
        .find(|case| case.outcome == ReallocOutcome::Failure)
        .unwrap();
    assert_eq!(failure.old, OldResponsibility::PreserveIfPresent);
    assert_eq!(
        realloc::retirement_availability(site, failure),
        ReallocRetirementAvailability::None
    );
    let retirements: Vec<_> = events
        .retirements
        .values()
        .filter(|event| event.key.role == SourceRole::ReallocOld)
        .collect();
    assert_eq!(
        retirements.len(),
        1,
        "failure creates no old-generation retirement event"
    );
    assert_eq!(
        retirements[0].key.condition,
        SourceCondition::ReallocSuccess
    );
    assert_eq!(retirements[0].key.function, site.key.function);
    assert_eq!(retirements[0].key.block, site.key.block);
    assert_eq!(retirements[0].key.statement, site.key.statement);
    assert!(
        !accepts(CODE, &[("resize", 1, 0)]),
        "the feasible success retirement conflicts with the whole-call shared protector"
    );
}
