//! Finish reconciliation controls only. Coverage rows below are copied from
//! actual routed frames; no ordinary/retirement loan review is simulated.
//! A positive result here establishes key accounting, not semantic acceptance.

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::Local;

use super::*;

const SOURCE: &str = r#"
unsafe extern "C" { fn free(pointer: *mut u8); }
struct Fields { first: *mut u8, second: *mut u8 }
pub unsafe fn direct(p: *const u8, chain: *const *mut u8) -> u8 {
    let value = *p;
    free(p as *mut u8);
    value
}
pub unsafe fn caller(p: *const u8, chain: *const *mut u8) -> u8 {
    direct(p, chain)
}
pub fn unrelated() {}
"#;

#[derive(Clone, Copy)]
enum Fault {
    None,
    MissingContext,
    MissingSource,
    DuplicateContext,
    UnexpectedContext,
    MissingEntrySet,
    WrongDepth,
    WrongField,
}

struct Finished {
    review: RetirementReview,
    expected: BTreeSet<ContextKey>,
    sources: BTreeSet<SourceEventKey>,
    free: SourceEventKey,
}

fn finish_coverage(fault: Fault) -> Finished {
    ::utils::compilation::run_compiler_on_str(SOURCE, |tcx| {
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
        let named = |name: &str| {
            *functions
                .iter()
                .find(|function| tcx.item_name(function.to_def_id()).as_str() == name)
                .expect("actual compiler function")
        };
        let direct = named("direct");
        let unrelated = named("unrelated");
        let field_owner = *structs.first().expect("actual field declaration");
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        let parameter = |index, depth| {
            SlotRef::Local(
                direct,
                slots.fn_local_slots[&direct]
                    .slot_for_local_depth(Local::from_u32(index), depth)
                    .expect("actual declared parameter/depth slot"),
            )
        };
        let shared = parameter(1, 0);
        let outer = parameter(2, 0);
        let inner = parameter(2, 1);
        let field = SlotRef::Field(
            slots
                .field_slots
                .slot_for_field_depth(
                    crate::analyses::borrow_ownership::slots::StructFieldSlot {
                        struct_did: field_owner,
                        field_index: 0,
                    },
                    0,
                )
                .expect("actual pointer field slot"),
        );
        assert_ne!(outer, inner);
        assert_ne!(shared, field);
        let expected_slot = if matches!(fault, Fault::WrongDepth) {
            outer
        } else {
            shared
        };
        let carried_slot = match fault {
            Fault::MissingEntrySet => None,
            Fault::WrongDepth => Some(inner),
            Fault::WrongField => Some(field),
            _ => Some(expected_slot),
        };
        // Deliberately disagree only in the entry-set controls. Both sides use
        // real compiler slots; no invented Loan, LocalDefId or field identity.
        let _entries =
            protected_entry::for_model(&program, &slots, |slot| carried_slot == Some(slot));
        let origin_flows =
            crate::analyses::borrow_ownership::origin_flow::analyze_program_origin_flow(&program);
        let scope = begin(&program, &slots, &origin_flows, |slot| {
            slot == expected_slot
        });
        let (expected, sources, free) = CURRENT.with(|current| {
            let mut current = current.borrow_mut();
            let context = current.as_mut().expect("actual retirement scope");
            assert!(
                context.routed.problems.is_empty(),
                "fixture routing: {:?}",
                context.routed.problems
            );
            let expected = context
                .routed
                .frames
                .values()
                .flatten()
                .map(|event| {
                    context_key(
                        &event.source.key,
                        event.frame,
                        event.location,
                        event.phase,
                        &event.route,
                    )
                })
                .collect::<BTreeSet<_>>();
            let sources = context
                .source
                .retirements
                .keys()
                .cloned()
                .collect::<BTreeSet<_>>();
            let free = sources
                .iter()
                .find(|source| source.role == SourceRole::Free)
                .expect("real ForeignC source free")
                .clone();
            let free_contexts = context
                .routed
                .frames
                .values()
                .flatten()
                .filter(|event| event.source.key == free)
                .count();
            assert!(
                free_contexts >= 2,
                "caller route separates a missing context from a missing source"
            );
            let rows: Vec<_> = context
                .routed
                .frames
                .iter()
                .map(|(&function, frames)| {
                    let coverage = frames
                        .iter()
                        .map(|event| ContextCoverage {
                            source: event.source.key.clone(),
                            function: event.frame,
                            location: event.location,
                            phase: event.phase,
                            route: event.route.clone(),
                            disposition: CoverageDisposition::Checked,
                        })
                        .collect();
                    (
                        function,
                        RetirementReview {
                            coverage,
                            ..RetirementReview::default()
                        },
                    )
                })
                .collect();
            context.latest.extend(rows);
            match fault {
                Fault::MissingContext => {
                    let rows = &mut context
                        .latest
                        .get_mut(&direct)
                        .expect("direct frame")
                        .coverage;
                    let index = rows
                        .iter()
                        .position(|row| row.source == free)
                        .expect("direct free context");
                    rows.remove(index);
                }
                Fault::MissingSource => {
                    for latest in context.latest.values_mut() {
                        latest.coverage.retain(|row| row.source != free);
                    }
                }
                Fault::DuplicateContext | Fault::UnexpectedContext => {
                    let rows = &mut context
                        .latest
                        .get_mut(&direct)
                        .expect("direct frame")
                        .coverage;
                    let mut extra = rows
                        .iter()
                        .find(|row| row.source == free)
                        .expect("real free context")
                        .clone();
                    if matches!(fault, Fault::UnexpectedContext) {
                        extra.function = unrelated;
                    }
                    rows.push(extra);
                }
                _ => {}
            }
            (expected, sources, free)
        });
        Finished {
            review: scope.finish(),
            expected,
            sources,
            free,
        }
    })
    .unwrap_or_else(|error| error.raise())
}

#[test]
fn e5_retirement_finish_complete_exact_coverage_reconciles_keys() {
    let finished = finish_coverage(Fault::None);
    assert!(
        finished.review.unresolved.is_empty(),
        "{:?}",
        finished.review.unresolved
    );
    let actual = finished
        .review
        .coverage
        .iter()
        .map(|row| {
            context_key(
                &row.source,
                row.function,
                row.location,
                row.phase,
                &row.route,
            )
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(actual, finished.expected);
    assert_eq!(finished.review.coverage.len(), actual.len());
    assert_eq!(
        finished
            .review
            .terminal
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>(),
        finished.sources
    );
}

#[test]
fn e5_retirement_finish_missing_context_does_not_hide_behind_present_source() {
    let finished = finish_coverage(Fault::MissingContext);
    assert!(finished.review.unresolved.iter().any(|row| {
        row.source.as_ref() == Some(&finished.free)
            && row.reason == UnresolvedReason::MissingContext
    }));
    assert!(!finished.review.unresolved.iter().any(|row| {
        row.source.as_ref() == Some(&finished.free)
            && row.reason == UnresolvedReason::MissingSourceEvent
    }));
    assert_eq!(
        finished.review.terminal[&finished.free],
        EventDisposition::Unresolved
    );
}

#[test]
fn e5_retirement_finish_missing_source_is_typed_unresolved() {
    let finished = finish_coverage(Fault::MissingSource);
    assert!(finished.review.unresolved.iter().any(|row| {
        row.source.as_ref() == Some(&finished.free)
            && row.reason == UnresolvedReason::MissingSourceEvent
    }));
    assert_eq!(
        finished.review.terminal[&finished.free],
        EventDisposition::Unresolved
    );
}

#[test]
fn e5_retirement_finish_duplicate_context_is_typed_unresolved() {
    let finished = finish_coverage(Fault::DuplicateContext);
    assert!(finished.review.unresolved.iter().any(|row| {
        row.source.as_ref() == Some(&finished.free)
            && row.reason == UnresolvedReason::DuplicateContext
    }));
    assert_eq!(
        finished.review.terminal[&finished.free],
        EventDisposition::Unresolved
    );
}

#[test]
fn e5_retirement_finish_unexpected_actual_function_context_is_unresolved() {
    let finished = finish_coverage(Fault::UnexpectedContext);
    assert!(finished.review.unresolved.iter().any(|row| {
        row.source.as_ref() == Some(&finished.free)
            && row.reason == UnresolvedReason::UnexpectedContext
    }));
    assert_eq!(
        finished.review.terminal[&finished.free],
        EventDisposition::Unresolved
    );
}

#[test]
fn e5_retirement_finish_actual_field_depth_and_entry_set_mismatches_are_unresolved() {
    for fault in [Fault::WrongField, Fault::WrongDepth, Fault::MissingEntrySet] {
        let finished = finish_coverage(fault);
        assert!(
            finished
                .review
                .unresolved
                .iter()
                .any(|row| row.reason == UnresolvedReason::DifferentEntryFacts)
        );
        assert!(
            finished
                .review
                .terminal
                .values()
                .all(|status| *status == EventDisposition::Unresolved)
        );
    }
}
