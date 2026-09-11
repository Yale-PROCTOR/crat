//! R294 raw RED draft v2. Compile fixtures for analysis; never execute their bodies.
//! Complete-file replacement draft; v1 is preserved as failed authoring evidence.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Local, Location, Place, TerminatorKind, VarDebugInfoContents};
use rustc_span::def_id::LocalDefId;

use crate::{
    analyses::{
        borrow_ownership::{
            SlotKind,
            borrow_engine::borrow_conflicts_with_flows,
            crate_slots::CrateSlots,
            export::PlaceKey,
            origin_flow::analyze_program_origin_flow,
            retirement::{
                OverlapReason, begin, model_scope,
                objects::{ObjectFacts, ObjectRoot, ObjectSet},
                return_origin::{self, Certificate, ClosedOrigin, with_transfer_receipts},
                tests::accepts,
            },
            slots::SlotId,
            solver::SlotRef,
            source_events::{self, SourceRole},
        },
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

const FRESH: &str = r##"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn origin() -> *mut u8 { malloc(8) }
pub unsafe fn caller(entry: *const u8) -> u8 {
    let value = *entry;
    let result = origin();
    free(result);
    value
}
"##;

const INPUT: &str = r##"
unsafe extern "C" { fn free(p: *mut u8); }
unsafe fn origin(p: *mut u8) -> *mut u8 { p }
pub unsafe fn caller(entry: *const u8) -> u8 {
    let value = *entry;
    let result = origin(entry as *mut u8);
    free(result);
    value
}
"##;

const UNKNOWN: &str = r##"
unsafe extern "C" { fn opaque() -> *mut u8; fn free(p: *mut u8); }
unsafe fn origin() -> *mut u8 { opaque() }
pub unsafe fn caller(entry: *const u8) -> u8 {
    let value = *entry;
    let result = origin();
    free(result);
    value
}
"##;

const MAY: &str = r##"
unsafe extern "C" { fn opaque() -> *mut u8; fn free(p: *mut u8); }
unsafe fn origin(p: *mut u8, choose: bool) -> *mut u8 {
    if choose { p } else { opaque() }
}
pub unsafe fn caller(entry: *const u8, choose: bool) -> u8 {
    let value = *entry;
    let result = origin(entry as *mut u8, choose);
    free(result);
    value
}
"##;

mod extended {
    //! R296 raw whole-item draft: compiler analysis only; fixture bodies never run.
    //! Reuse the established Send+Sync compiler callback carrier, not a new one.

    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_middle::mir::{Local, Location, TerminatorKind, UnwindAction, VarDebugInfoContents};

    use crate::analyses::{
        borrow_ownership::{
            SlotKind, borrow_verify,
            crate_slots::CrateSlots,
            export::PlaceKey,
            origin_flow::analyze_program_origin_flow,
            realloc::{self, OldResponsibility, ReallocOutcome, ReallocRetirementAvailability},
            retirement::{
                OverlapReason,
                objects::{ObjectFacts, ObjectRoot},
                overlap,
                return_origin::{self, Certificate, ClosedOrigin, Rejection},
                tests::accepts,
                tests_return_origin::{
                    ExpectedCertificate, ExpectedObject, check_certificate_and_receipt,
                    check_destination, named_function, with_program,
                },
            },
            slots::SlotId,
            solver::SlotRef,
            source_events::{self, SourceCondition, SourceRole},
        },
        mir::{CallKind, TerminatorExt},
    };

    #[test]
    fn e5aprime_w08_local_storage_return_is_not_closed_input_or_fresh() {
        const CODE: &str = r####"
unsafe fn origin() -> *mut u8 { let mut local = 0u8; &raw mut local }
pub unsafe fn caller(entry: *const u8) -> *mut u8 { origin() }
"####;
        check_destination(CODE, ExpectedObject::Unknown);
        check_certificate_and_receipt(CODE, ExpectedCertificate::Rejected);
    }

    #[test]
    fn e5aprime_w08_promoted_address_is_not_a_fresh_allocation() {
        const CODE: &str = r####"
unsafe fn origin() -> *mut u8 { &42u8 as *const u8 as *mut u8 }
pub unsafe fn caller(entry: *const u8) -> *mut u8 { origin() }
"####;
        check_destination(CODE, ExpectedObject::Unknown);
        check_certificate_and_receipt(CODE, ExpectedCertificate::Rejected);
    }

    #[test]
    fn e5aprime_w08_projected_field_return_remains_unknown() {
        const CODE: &str = r####"
pub struct Holder { pub pointer: *mut u8 }
unsafe fn origin(holder: *mut Holder) -> *mut u8 { (*holder).pointer }
pub unsafe fn caller(entry: *const u8, holder: *mut Holder) -> *mut u8 { origin(holder) }
"####;
        check_destination(CODE, ExpectedObject::Unknown);
        check_certificate_and_receipt(CODE, ExpectedCertificate::Rejected);
    }

    #[test]
    fn e5aprime_w08_arithmetic_return_is_not_exact_input() {
        const CODE: &str = r####"
unsafe fn origin(p: *mut u8) -> *mut u8 { p.add(1) }
pub unsafe fn caller(entry: *const u8) -> *mut u8 { origin(entry as *mut u8) }
"####;
        check_destination(CODE, ExpectedObject::Unknown);
        check_certificate_and_receipt(CODE, ExpectedCertificate::Rejected);
    }

    #[test]
    fn e5aprime_w08_aggregate_return_does_not_acquire_pointer_certificate() {
        const CODE: &str = r####"
pub struct Holder { pub pointer: *mut u8 }
unsafe fn origin(p: *mut u8) -> Holder { Holder { pointer: p } }
pub unsafe fn caller(entry: *const u8) { let _result = origin(entry as *mut u8); }
"####;
        // Pointer-at-destination is deliberately not queried for an aggregate.
        with_program(CODE, |program| {
            let callee = named_function(program, "origin");
            let flows = analyze_program_origin_flow(program);
            let certificates = return_origin::derive(program, &flows);
            assert!(
                !matches!(certificates.get(&callee), Some(Ok(_))),
                "an aggregate signature cannot be mistaken for its contained pointer"
            );
        });
    }

    #[test]
    fn e5aprime_w08_deeper_input_load_does_not_become_depth_zero_input() {
        const CODE: &str = r####"
unsafe fn origin(p: *mut *mut u8) -> *mut u8 { *p }
pub unsafe fn caller(entry: *const u8, holder: *mut *mut u8) -> *mut u8 { origin(holder) }
"####;
        check_destination(CODE, ExpectedObject::Unknown);
        check_certificate_and_receipt(CODE, ExpectedCertificate::Rejected);
    }

    #[test]
    fn e5aprime_w06_indirect_return_producer_remains_unclassified() {
        const CODE: &str = r####"
unsafe fn origin(f: unsafe fn(*mut u8) -> *mut u8, p: *mut u8) -> *mut u8 { f(p) }
pub unsafe fn caller(entry: *const u8, f: unsafe fn(*mut u8) -> *mut u8) -> *mut u8 {
    origin(f, entry as *mut u8)
}
"####;
        check_destination(CODE, ExpectedObject::Unknown);
        check_certificate_and_receipt(CODE, ExpectedCertificate::Rejected);
    }

    #[test]
    fn e5aprime_w07_two_input_alternatives_cannot_select_one_formal() {
        const CODE: &str = r####"
unsafe fn origin(p: *mut u8, q: *mut u8, choose: bool) -> *mut u8 {
    if choose { p } else { q }
}
pub unsafe fn caller(entry: *const u8, other: *mut u8, choose: bool) -> *mut u8 {
    origin(entry as *mut u8, other, choose)
}
"####;
        check_destination(CODE, ExpectedObject::Unknown);
        check_certificate_and_receipt(CODE, ExpectedCertificate::Rejected);
    }

    #[test]
    fn e5aprime_w07_empty_recursive_summary_cannot_vacuously_certify() {
        const CODE: &str = r####"
unsafe fn origin(p: *mut u8) -> *mut u8 { origin(p) }
pub unsafe fn caller(entry: *const u8) -> *mut u8 { origin(entry as *mut u8) }
"####;
        // Recursion is syntactic source only; neither function body is executed.
        with_program(CODE, |program| {
            let callee = named_function(program, "origin");
            let flows = analyze_program_origin_flow(program);
            let certificates = return_origin::derive(program, &flows);
            assert!(
                !matches!(certificates.get(&callee), Some(Ok(_))),
                "absence of a normal-return producer is not an all-path proof"
            );
        });
    }

    #[test]
    fn e5aprime_w11_null_only_return_is_explicitly_unclassified() {
        const CODE: &str = r####"
unsafe fn origin() -> *mut u8 { core::ptr::null_mut() }
pub unsafe fn caller(entry: *const u8) -> *mut u8 { origin() }
"####;
        check_destination(CODE, ExpectedObject::Unknown);
        with_program(CODE, |program| {
            let callee = named_function(program, "origin");
            let flows = analyze_program_origin_flow(program);
            let certificates = return_origin::derive(program, &flows);
            assert_eq!(
                certificates.get(&callee),
                Some(&Err(Rejection::NullOnly)),
                "R294 authorizes no ClosedNull return certificate; retain typed rejection"
            );
        });
    }

    #[test]
    fn e5aprime_w11_nullable_fresh_return_keeps_generation_alternative() {
        const CODE: &str = r####"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn origin(choose: bool) -> *mut u8 {
    if choose { malloc(8) } else { core::ptr::null_mut() }
}
pub unsafe fn caller(entry: *const u8, choose: bool) -> u8 {
    let value = *entry;
    let result = origin(choose);
    free(result);
    value
}
"####;
        check_certificate_and_receipt(CODE, ExpectedCertificate::Fresh { nullable: true });
        check_destination(CODE, ExpectedObject::Fresh);
        assert!(
            accepts(CODE, &[("caller", 1, 0)]),
            "None is orthogonal; nullable fresh memory cannot retire the input object"
        );
    }

    #[test]
    fn e5aprime_w09_fresh_return_does_not_restore_mutated_caller_cells() {
        const CODE: &str = r####"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; }
unsafe fn origin(out: *mut *mut u8) -> *mut u8 {
    *out = core::ptr::null_mut();
    malloc(8)
}
pub unsafe fn caller(entry: *const u8) -> *mut u8 {
    let mut carrier = entry as *mut u8;
    let result = origin(&raw mut carrier);
    let _observed = carrier;
    result
}
"####;
        check_certificate_and_receipt(CODE, ExpectedCertificate::Fresh { nullable: true });
        check_destination(CODE, ExpectedObject::Fresh);
        with_program(CODE, |program| {
            let caller = named_function(program, "caller");
            let callee = named_function(program, "origin");
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(caller)
                .borrow();
            let carriers: FxHashSet<_> = body
                .var_debug_info
                .iter()
                .filter_map(|info| {
                    if info.name.as_str() != "carrier" {
                        return None;
                    }
                    let VarDebugInfoContents::Place(place) = info.value else {
                        return None;
                    };
                    place.as_local()
                })
                .collect();
            assert_eq!(carriers.len(), 1);
            let carrier = *carriers.iter().next().unwrap();
            let targets: Vec<_> = body
                .basic_blocks
                .iter()
                .filter_map(|data| {
                    let call = data.terminator().as_call(program.tcx)?;
                    if !matches!(call.func, CallKind::FreeStanding(f) if f == callee) {
                        return None;
                    }
                    let TerminatorKind::Call {
                        target: Some(target),
                        ..
                    } = data.terminator().kind
                    else {
                        return None;
                    };
                    Some(target)
                })
                .collect();
            assert_eq!(targets.len(), 1);
            let slots = CrateSlots::build(program);
            let events = source_events::collect(program);
            let flows = analyze_program_origin_flow(program);
            let facts = ObjectFacts::analyze(program, &slots, &events, &flows);
            let actual = facts.pointer_at(
                caller,
                Location {
                    block: targets[0],
                    statement_index: 0,
                },
                &PlaceKey::from_place(rustc_middle::mir::Place::from(carrier)),
                0,
            );
            assert!(
                actual.unknown,
                "fresh return is not a no-write certificate for caller storage"
            );
        });
    }

    #[test]
    fn e5aprime_w09_reassigned_exposed_carrier_stays_exposed_to_later_opaque_call() {
        const CODE: &str = r####"
unsafe extern "C" { fn remember(cell: *mut *mut u8); fn overwrite_saved(); }
unsafe fn origin(p: *mut u8) -> *mut u8 {
    let mut carrier = p;
    remember(&raw mut carrier);
    carrier = p;
    overwrite_saved();
    carrier
}
pub unsafe fn caller(entry: *const u8) -> *mut u8 { origin(entry as *mut u8) }
"####;
        check_destination(CODE, ExpectedObject::Unknown);
        check_certificate_and_receipt(CODE, ExpectedCertificate::Rejected);
    }

    #[test]
    fn e5aprime_w10_refinement_is_normal_edge_only_with_real_cleanup() {
        const CODE: &str = r####"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; }
struct Guard;
impl Drop for Guard { fn drop(&mut self) {} }
unsafe fn origin() -> *mut u8 { malloc(8) }
pub unsafe fn caller(entry: *const u8) -> *mut u8 {
    let _guard = Guard;
    origin()
}
"####;
        with_program(CODE, |program| {
            let caller = named_function(program, "caller");
            let callee = named_function(program, "origin");
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(caller)
                .borrow();
            let calls: Vec<_> = body
                .basic_blocks
                .iter_enumerated()
                .filter_map(|(block, data)| {
                    let call = data.terminator().as_call(program.tcx)?;
                    if !matches!(call.func, CallKind::FreeStanding(f) if f == callee) {
                        return None;
                    }
                    let TerminatorKind::Call {
                        target: Some(normal),
                        unwind: UnwindAction::Cleanup(cleanup),
                        ..
                    } = data.terminator().kind
                    else {
                        panic!("fixture must contain an actual cleanup edge");
                    };
                    Some((
                        Location {
                            block,
                            statement_index: data.statements.len(),
                        },
                        normal,
                        cleanup,
                        call.destination,
                    ))
                })
                .collect();
            assert_eq!(calls.len(), 1);
            let (site, normal, cleanup, destination) = calls[0];
            let slots = CrateSlots::build(program);
            let events = source_events::collect(program);
            let flows = analyze_program_origin_flow(program);
            let facts = ObjectFacts::analyze(program, &slots, &events, &flows);
            let place = PlaceKey::from_place(destination);
            let returned = facts.pointer_at(
                caller,
                Location {
                    block: normal,
                    statement_index: 0,
                },
                &place,
                0,
            );
            assert!(!returned.unknown);
            assert_eq!(
                returned.roots,
                FxHashSet::from_iter([ObjectRoot::Fresh {
                    frame: caller,
                    site
                }])
            );
            assert!(facts.has_location(
                caller,
                Location {
                    block: cleanup,
                    statement_index: 0
                }
            ));
            let unwound = facts.pointer_at(
                caller,
                Location {
                    block: cleanup,
                    statement_index: 0,
                },
                &place,
                0,
            );
            assert!(
                unwound.unknown,
                "no normal-return destination is delivered on cleanup"
            );
            assert!(!unwound.roots.contains(&ObjectRoot::Fresh {
                frame: caller,
                site
            }));
        });
    }

    #[test]
    fn e5aprime_w10_loop_callsite_keeps_static_root_and_equal_root_overlap() {
        const CODE: &str = r####"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn origin() -> *mut u8 { malloc(8) }
pub unsafe fn caller(entry: *const u8) {
    let mut count = 0usize;
    while count < 2 {
        let result = origin();
        free(result);
        count += 1;
    }
}
"####;
        // No every-visit receipt equality assumption is made for a loop.
        check_destination(CODE, ExpectedObject::Fresh);
        with_program(CODE, |program| {
            let caller = named_function(program, "caller");
            let callee = named_function(program, "origin");
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(caller)
                .borrow();
            let calls: Vec<_> = body
                .basic_blocks
                .iter_enumerated()
                .filter_map(|(block, data)| {
                    let call = data.terminator().as_call(program.tcx)?;
                    if !matches!(call.func, CallKind::FreeStanding(f) if f == callee) {
                        return None;
                    }
                    let TerminatorKind::Call {
                        target: Some(target),
                        ..
                    } = data.terminator().kind
                    else {
                        return None;
                    };
                    Some((
                        Location {
                            block,
                            statement_index: data.statements.len(),
                        },
                        target,
                        call.destination,
                    ))
                })
                .collect();
            assert_eq!(calls.len(), 1, "one repeated static allocation-return site");
            let (site, target, destination) = calls[0];
            let slots = CrateSlots::build(program);
            let events = source_events::collect(program);
            let flows = analyze_program_origin_flow(program);
            let facts = ObjectFacts::analyze(program, &slots, &events, &flows);
            let objects = facts.pointer_at(
                caller,
                Location {
                    block: target,
                    statement_index: 0,
                },
                &PlaceKey::from_place(destination),
                0,
            );
            assert_eq!(
                objects.roots,
                FxHashSet::from_iter([ObjectRoot::Fresh {
                    frame: caller,
                    site
                }])
            );
            assert_eq!(
                overlap(&objects, &objects, caller, true),
                Some(OverlapReason::SameAbstractRoot),
                "a repeated static site is not a pair of proven distinct dynamic epochs"
            );
        });
    }

    #[test]
    fn e5aprime_w10_nested_fresh_producer_and_routed_release_keep_unrelated_entry() {
        const CODE: &str = r####"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn leaf() -> *mut u8 { malloc(8) }
unsafe fn origin() -> *mut u8 { leaf() }
unsafe fn release(raw: *mut u8) { free(raw); }
pub unsafe fn caller(entry: *const u8) -> u8 {
    let value = *entry;
    let result = origin();
    release(result);
    value
}
"####;
        check_certificate_and_receipt(CODE, ExpectedCertificate::Fresh { nullable: true });
        check_destination(CODE, ExpectedObject::Fresh);
        assert!(
            accepts(CODE, &[("caller", 1, 0)]),
            "the routed free preserves the fresh-return object identity at the caller"
        );
    }

    #[test]
    fn e5aprime_w12_realloc_success_and_failure_keep_original_responsibility() {
        const CODE: &str = r####"
unsafe extern "C" { fn realloc(p: *mut u8, bytes: usize) -> *mut u8; fn free(p: *mut u8); }
pub unsafe fn resize(p: *const u8) -> u8 {
    let value = *p;
    let result = realloc(p as *mut u8, 8);
    if result.is_null() { value } else { free(result); value }
}
"####;
        with_program(CODE, |program| {
            let events = source_events::collect(program);
            assert_eq!(events.reallocations.len(), 1);
            let site = &events.reallocations[0];
            let cases = realloc::classify(site).expect("recognized direct result branch");
            assert_eq!(cases.len(), 2);
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
            assert_eq!(retirements.len(), 1);
            assert_eq!(
                retirements[0].key.condition,
                SourceCondition::ReallocSuccess
            );
            assert_eq!(retirements[0].key.function, site.key.function);
            assert_eq!(retirements[0].key.block, site.key.block);
            assert_eq!(retirements[0].key.statement, site.key.statement);
        });
        assert!(
            !accepts(CODE, &[("resize", 1, 0)]),
            "success still retires the protected old object"
        );
    }

    #[test]
    fn e5aprime_w12_explicit_owning_free_is_not_a_new_ref_obligation() {
        const CODE: &str = r####"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn release_owned(p: *mut u8) { free(p); }
"####;
        with_program(CODE, |program| {
            let function = named_function(program, "release_owned");
            let slots = CrateSlots::build(program);
            let owned = SlotRef::Local(
                function,
                slots.fn_local_slots[&function]
                    .slot_for_local_depth(Local::from_u32(1), 0)
                    .unwrap(),
            );
            let mut model = FxHashMap::default();
            for index in 0..slots.field_slots.len() {
                model.insert(SlotRef::Field(SlotId::from_usize(index)), SlotKind::Raw);
            }
            for (&owner, universe) in &slots.fn_local_slots {
                for index in 0..universe.len() {
                    let slot = SlotRef::Local(owner, SlotId::from_usize(index));
                    model.insert(
                        slot,
                        if slot == owned {
                            SlotKind::Owning
                        } else {
                            SlotKind::Raw
                        },
                    );
                }
            }
            assert_eq!(
                model
                    .values()
                    .filter(|kind| **kind == SlotKind::Owning)
                    .count(),
                1
            );
            assert!(
                borrow_verify::model_accepts(program, &slots, &model, false),
                "retirement refinement introduces no Ref protector or licensing change for an explicit Owning model"
            );
            assert_eq!(model[&owned], SlotKind::Owning);
        });
    }
}

fn with_program(code: &str, check: impl FnOnce(&RustProgram<'_>) + Send + Sync) {
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
        check(&RustProgram {
            tcx,
            functions,
            structs,
        });
    })
    .unwrap_or_else(|error| error.raise());
}

fn named_function(program: &RustProgram<'_>, name: &str) -> LocalDefId {
    let found: Vec<_> = program
        .functions
        .iter()
        .copied()
        .filter(|function| program.tcx.item_name(function.to_def_id()).as_str() == name)
        .collect();
    assert_eq!(
        found.len(),
        1,
        "one compiler-resolved fixture function {name}"
    );
    found[0]
}

#[derive(Clone, Copy, Debug)]
enum ExpectedObject {
    Fresh,
    Input(u32),
    Null,
    Unknown,
}

#[derive(Clone, Copy, Debug)]
enum ExpectedCertificate {
    Fresh { nullable: bool },
    Input { formal: u32, nullable: bool },
    Rejected,
}

/// Query and actual transfer are independent assertions. Fixtures are acyclic;
/// every matching visit must agree, so a favorable first receipt cannot pass.
fn check_certificate_and_receipt(code: &str, expected: ExpectedCertificate) {
    with_program(code, |program| {
        let caller = named_function(program, "caller");
        let callee = named_function(program, "origin");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
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
                    panic!("fixture origin call must have a normal successor");
                };
                Some((
                    Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                    target,
                    call,
                ))
            })
            .collect();
        assert_eq!(calls.len(), 1);
        let (site, target, call) = &calls[0];
        let flows = analyze_program_origin_flow(program);
        let certificates = return_origin::derive(program, &flows);
        let queried = return_origin::for_call(program, &certificates, call);
        let expected_certificate = match expected {
            ExpectedCertificate::Fresh { nullable } => Some(Certificate {
                origin: ClosedOrigin::Fresh,
                nullable,
            }),
            ExpectedCertificate::Input { formal, nullable } => Some(Certificate {
                origin: ClosedOrigin::Input(Local::from_u32(formal)),
                nullable,
            }),
            ExpectedCertificate::Rejected => None,
        };
        if let Some(expected) = &expected_certificate {
            assert_eq!(
                queried
                    .as_ref()
                    .expect("closed certificate must be present"),
                expected
            );
            assert_eq!(
                certificates
                    .get(&callee)
                    .expect("callee map entry")
                    .as_ref()
                    .unwrap(),
                expected
            );
        } else {
            assert!(
                queried.is_err(),
                "MAY/opaque evidence must not produce a closed certificate"
            );
        }
        let slots = CrateSlots::build(program);
        let events = source_events::collect(program);
        let (facts, receipts) =
            with_transfer_receipts(|| ObjectFacts::analyze(program, &slots, &events, &flows));
        let matching: Vec<_> = receipts
            .iter()
            .filter(|row| {
                row.caller == caller
                    && row.callee == Some(callee)
                    && row.location == *site
                    && row.normal
            })
            .collect();
        assert!(
            !matching.is_empty(),
            "the actual call transfer must provide its branch receipt"
        );
        for row in matching {
            if let Some(expected) = &expected_certificate {
                assert_eq!(row.certificate.as_ref().unwrap(), expected);
                let index = match expected.origin {
                    ClosedOrigin::Input(formal) => Some((formal.as_u32() - 1) as usize),
                    ClosedOrigin::Fresh => None,
                };
                assert_eq!(
                    row.argument_index, index,
                    "formal/actual position is independently receipted"
                );
            } else {
                assert!(row.certificate.is_err());
                assert!(
                    row.destination_objects.unknown,
                    "rejected certificate cannot deliver complete facts"
                );
            }
            let observed = facts.pointer_at(
                caller,
                Location {
                    block: *target,
                    statement_index: 0,
                },
                &PlaceKey::from_place(call.destination),
                0,
            );
            assert_eq!(
                row.destination_objects, observed,
                "receipt and actual successor snapshot must agree"
            );
        }
    });
}

/// Inspect the first normal-successor snapshot independently of final kind.
fn check_destination(code: &str, expected: ExpectedObject) {
    with_program(code, |program| {
        let caller = named_function(program, "caller");
        let callee = named_function(program, "origin");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
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
                    panic!("fixture origin call must have a normal successor");
                };
                Some((
                    Location {
                        block,
                        statement_index: data.statements.len(),
                    },
                    target,
                    call.destination,
                ))
            })
            .collect();
        assert_eq!(calls.len(), 1, "one exact direct-local origin call");
        let (site, target, destination) = calls[0];
        assert!(
            destination.as_local().is_some(),
            "fixture uses a direct destination"
        );
        let slots = CrateSlots::build(program);
        let events = source_events::collect(program);
        let flows = analyze_program_origin_flow(program);
        let facts = ObjectFacts::analyze(program, &slots, &events, &flows);
        let at = Location {
            block: target,
            statement_index: 0,
        };
        assert!(
            facts.has_location(caller, at),
            "normal successor is reachable"
        );
        let actual = facts.pointer_at(caller, at, &PlaceKey::from_place(destination), 0);
        let expected = match expected {
            ExpectedObject::Fresh => ObjectSet {
                roots: FxHashSet::from_iter([ObjectRoot::Fresh {
                    frame: caller,
                    site,
                }]),
                unknown: false,
            },
            ExpectedObject::Input(parameter) => ObjectSet {
                roots: FxHashSet::from_iter([ObjectRoot::Input {
                    function: caller,
                    parameter: Local::from_u32(parameter),
                    depth: 0,
                }]),
                unknown: false,
            },
            ExpectedObject::Null => ObjectSet {
                roots: FxHashSet::default(),
                unknown: false,
            },
            ExpectedObject::Unknown => ObjectSet::default(),
        };
        assert_eq!(
            actual, expected,
            "normal-return transfer at exact caller/callee/site"
        );
        // premise-moved:row-a (R318-1). This control asserted that the local-call
        // clobber reached `_1`'s own depth-0 cell -- true only while the clobber
        // was whole-state, which was G0-B's era-5a' disposition. Row (a) narrows
        // it to the cells a callee can reach, so the control now asserts the
        // NARROWED verdict: `_1`'s own cell is clobbered exactly when its address
        // escapes. It still discriminates in both directions -- a clobber that
        // reached everything would fail here for a non-escaping `_1`, and one
        // that reached nothing would fail for an escaping one.
        let incoming = facts.pointer_at(
            caller,
            at,
            &PlaceKey::from_place(Place::from(Local::from_u32(1))),
            0,
        );
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(caller)
            .borrow();
        let reachable =
            crate::analyses::borrow_ownership::retirement::call_reach::EscapeFacts::of_body(&body)
                .escapes(Local::from_u32(1));
        assert_eq!(
            incoming.unknown, reachable,
            "local-call clobber reaches _1's own cell exactly when its address escapes (R318-1)"
        );
    });
}

#[test]
fn e5aprime_w01_fresh_return_preserves_unrelated_entry() {
    assert!(
        accepts(FRESH, &[("caller", 1, 0)]),
        "closed fresh-return free is disjoint from protected input"
    );
}

#[test]
fn e5aprime_k01_fresh_destination_is_exact_caller_generation() {
    check_destination(FRESH, ExpectedObject::Fresh);
}

#[test]
fn e5aprime_k01_fresh_certificate_and_transfer_receipt_are_independent() {
    check_certificate_and_receipt(FRESH, ExpectedCertificate::Fresh { nullable: true });
}

#[test]
fn e5aprime_w02_input_return_still_rejects_alias_retirement() {
    assert!(
        !accepts(INPUT, &[("caller", 1, 0)]),
        "Input return cannot hide whole-call protector retirement"
    );
}

#[test]
fn e5aprime_k02_input_destination_is_exact_preclobber_actual() {
    check_destination(INPUT, ExpectedObject::Input(1));
}

#[test]
fn e5aprime_k02_input_certificate_and_transfer_receipt_are_independent() {
    check_certificate_and_receipt(
        INPUT,
        ExpectedCertificate::Input {
            formal: 1,
            nullable: false,
        },
    );
}

#[test]
fn e5aprime_w03_second_formal_preserves_actual_position() {
    const CODE: &str = r##"
unsafe extern "C" { fn free(p: *mut u8); }
unsafe fn origin(unused: *mut u8, selected: *mut u8) -> *mut u8 {
    let copied = selected;
    copied as *mut u8
}
pub unsafe fn caller(entry: *const u8, other: *mut u8) -> u8 {
    let value = *entry;
    let result = origin(other, entry as *mut u8);
    free(result);
    value
}
"##;
    check_destination(CODE, ExpectedObject::Input(1));
    check_certificate_and_receipt(
        CODE,
        ExpectedCertificate::Input {
            formal: 2,
            nullable: false,
        },
    );
    assert!(!accepts(CODE, &[("caller", 1, 0)]));
}

#[test]
fn e5aprime_w04_unknown_return_retains_unknown_objects() {
    check_destination(UNKNOWN, ExpectedObject::Unknown);
    assert!(!accepts(UNKNOWN, &[("caller", 1, 0)]));
}

#[test]
fn e5aprime_k03_may_input_plus_opaque_is_not_a_closed_input() {
    check_destination(MAY, ExpectedObject::Unknown);
    assert!(!accepts(MAY, &[("caller", 1, 0)]));
}

#[test]
fn e5aprime_k03_may_rejection_receipt_cannot_deliver_refinement() {
    check_certificate_and_receipt(MAY, ExpectedCertificate::Rejected);
}

#[test]
fn e5aprime_w07_fresh_input_union_is_not_closed() {
    const CODE: &str = r##"
unsafe extern "C" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn origin(p: *mut u8, choose: bool) -> *mut u8 {
    if choose { p } else { malloc(8) }
}
pub unsafe fn caller(entry: *const u8, choose: bool) -> u8 {
    let value = *entry;
    let result = origin(entry as *mut u8, choose);
    free(result);
    value
}
"##;
    check_destination(CODE, ExpectedObject::Unknown);
    check_certificate_and_receipt(CODE, ExpectedCertificate::Rejected);
}

#[test]
fn e5aprime_w06_foreign_return_cannot_escape_clobber() {
    const CODE: &str = r##"
unsafe extern "C" { fn foreign() -> *mut u8; fn free(p: *mut u8); }
pub unsafe fn caller(entry: *const u8) -> u8 {
    let value = *entry;
    let result = foreign();
    free(result);
    value
}
"##;
    assert!(
        !accepts(CODE, &[("caller", 1, 0)]),
        "foreign source is not an admitted local producer"
    );
}

#[test]
fn e5aprime_w11_null_actual_is_empty_complete_object_set() {
    const CODE: &str = r##"
unsafe extern "C" { fn free(p: *mut u8); }
unsafe fn origin(p: *mut u8) -> *mut u8 { p }
pub unsafe fn caller(entry: *const u8) -> u8 {
    let value = *entry;
    let result = origin(core::ptr::null_mut());
    free(result);
    value
}
"##;
    check_destination(CODE, ExpectedObject::Null);
    assert!(accepts(CODE, &[("caller", 1, 0)]));
}

#[test]
fn e5aprime_w11_nullable_input_certificate_does_not_mean_null_actual() {
    const CODE: &str = r##"
unsafe extern "C" { fn free(p: *mut u8); }
unsafe fn origin(p: *mut u8, choose: bool) -> *mut u8 {
    if choose { p } else { core::ptr::null_mut() }
}
pub unsafe fn caller(entry: *const u8, choose: bool) -> u8 {
    let value = *entry;
    let result = origin(entry as *mut u8, choose);
    free(result);
    value
}
"##;
    check_certificate_and_receipt(
        CODE,
        ExpectedCertificate::Input {
            formal: 1,
            nullable: true,
        },
    );
    check_destination(CODE, ExpectedObject::Input(1));
    assert!(!accepts(CODE, &[("caller", 1, 0)]));
}

#[test]
fn e5aprime_w05_self_free_entry_and_copy_keep_same_root_support() {
    // This unexecuted input-UB pattern keeps the copied loan live across free.
    // It is not a UB-free counterexample or a hardcoded corpus _7 identity.
    const CODE: &str = r##"
unsafe extern "C" { fn free(p: *mut u8); }
pub unsafe fn buffer_free(self_0: *const u8) -> u8 {
    let copied: *const u8 = self_0;
    free(self_0 as *mut u8);
    *copied
}
"##;
    with_program(CODE, |program| {
        let function = named_function(program, "buffer_free");
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let named = |name: &str| {
            let found: FxHashSet<_> = body
                .var_debug_info
                .iter()
                .filter_map(|info| {
                    if info.name.as_str() != name {
                        return None;
                    }
                    let VarDebugInfoContents::Place(place) = info.value else { return None };
                    place.as_local()
                })
                .collect();
            assert_eq!(
                found.len(),
                1,
                "unique compiler-resolved source local {name}"
            );
            *found.iter().next().unwrap()
        };
        let parameter = named("self_0");
        let copied = named("copied");
        assert_ne!(parameter, copied);
        assert!(parameter.as_usize() > 0 && parameter.as_usize() <= body.arg_count);
        let slots = CrateSlots::build(program);
        let selected: FxHashSet<_> = [parameter, copied]
            .into_iter()
            .map(|local| {
                SlotRef::Local(
                    function,
                    slots.fn_local_slots[&function]
                        .slot_for_local_depth(local, 0)
                        .unwrap(),
                )
            })
            .collect();
        let mut model = FxHashMap::default();
        for index in 0..slots.field_slots.len() {
            model.insert(SlotRef::Field(SlotId::from_usize(index)), SlotKind::Raw);
        }
        for (&owner, universe) in &slots.fn_local_slots {
            for index in 0..universe.len() {
                let slot = SlotRef::Local(owner, SlotId::from_usize(index));
                model.insert(
                    slot,
                    if selected.contains(&slot) {
                        SlotKind::Ref
                    } else {
                        SlotKind::Raw
                    },
                );
            }
        }
        let flows = analyze_program_origin_flow(program);
        let _model_scope = model_scope(&model);
        let scope = begin(program, &slots, &flows, |slot| selected.contains(&slot));
        let _ordinary = borrow_conflicts_with_flows(
            program,
            &flows,
            |owner| move |local| owner == function && (local == parameter || local == copied),
            |_| |_| false,
        );
        let review = scope.finish();
        for target in selected {
            assert!(
                review.conflicts.iter().any(|row| row.target == target
                    && row.source.role == SourceRole::Free
                    && row.overlap == OverlapReason::SameAbstractRoot),
                "each self-free identity retains its own SameAbstractRoot witness: {target:?}"
            );
            assert!(
                review.targets().contains(&target),
                "each witness still reaches retirement selection"
            );
        }
    });
}
