//! R245-1 actual preledger wrappers: scoped faults, unarmed success controls.
use std::{cell::RefCell, sync::Arc};

use rustc_hir::{ItemKind, OwnerNode};

use super::{
    SlotKind,
    a5_overlap::{A5Mode, CallSiteWitnessKey, FunctionPairKey, WholeProgramAttestation},
    construction::{A5PreledgerDeclineReason, solve_bo_a5_config_reporting},
    crate_slots::CrateSlots,
    mutability_facts::MutFacts,
    origins::compute_origins,
    slots::SlotId,
    solver::{KindSolver, RoundModelFailure, SlotRef},
    source_events::SourceEvents,
};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Copy, Debug)]
enum Fault {
    Construction(usize),
    Verification(usize),
    Producer,
}
#[derive(Debug)]
struct State {
    fault: Fault,
    constructions: usize,
    verifications: usize,
    fired: usize,
    terminal: Option<RoundModelFailure>,
}
thread_local! { static STATE:RefCell<Option<State>>=const{RefCell::new(None)}; }
fn with_fault<T>(fault: Fault, f: impl FnOnce() -> T) -> (T, State) {
    struct Reset(Option<State>);
    impl Drop for Reset {
        fn drop(&mut self) {
            STATE.with(|state| {
                state.replace(self.0.take());
            });
        }
    }
    let _reset = Reset(STATE.with(|state| {
        state.replace(Some(State {
            fault,
            constructions: 0,
            verifications: 0,
            fired: 0,
            terminal: None,
        }))
    }));
    let value = f();
    let receipt = STATE.with(|state| state.borrow_mut().take().unwrap());
    (value, receipt)
}
pub(crate) fn inventory(source: Arc<SourceEvents>) -> Arc<SourceEvents> {
    let hit = STATE.with(|state| {
        let mut state = state.borrow_mut();
        let Some(s) = state.as_mut() else { return false };
        s.constructions += 1;
        if matches!(s.fault,Fault::Construction(n) if n==s.constructions) {
            s.fired += 1;
            true
        } else {
            false
        }
    });
    if !hit {
        return source;
    }
    let mut damaged = (*source).clone();
    assert!(
        !damaged.reallocations.is_empty(),
        "fault uses an actual collected realloc"
    );
    damaged.reallocations.clear();
    Arc::new(damaged)
}
pub(crate) fn verification(slots: &CrateSlots, solver: &KindSolver) {
    // Synthetic model-control only: classify a replay with explicitly Raw
    // carriers, without assuming which kinds the unconstrained solver chooses.
    if ALL_RAW.with(|active| active.get()) {
        for (&function, universe) in &slots.fn_local_slots {
            for index in 0..universe.len() {
                solver.assume(
                    SlotRef::Local(function, SlotId::from_usize(index)),
                    SlotKind::Raw,
                );
            }
        }
        for index in 0..slots.field_slots.len() {
            solver.assume(SlotRef::Field(SlotId::from_usize(index)), SlotKind::Raw);
        }
    }
    let hit = STATE.with(|state| {
        let mut state = state.borrow_mut();
        let Some(s) = state.as_mut() else { return false };
        s.verifications += 1;
        if matches!(s.fault,Fault::Verification(n) if n==s.verifications) {
            s.fired += 1;
            true
        } else {
            false
        }
    });
    if !hit {
        return;
    }
    let target = slots
        .fn_local_slots
        .iter()
        .flat_map(|(&function, universe)| {
            (0..universe.len())
                .map(move |index| SlotRef::Local(function, SlotId::from_usize(index)))
        })
        .min_by_key(|slot| super::l2::SlotKey::of(*slot))
        .expect("actual pointer slot");
    solver.assume(target, SlotKind::Ref);
    solver.add_borrow_exclusion(Some(target), &[]);
}
pub(crate) fn verification_result(solver: &KindSolver) {
    STATE.with(|state| {
        if let Some(s) = state.borrow_mut().as_mut() {
            if matches!(s.fault,Fault::Verification(n) if n==s.verifications) {
                s.terminal = solver.round_model_failure();
            }
        }
    });
}
pub(crate) fn dependency(key: CallSiteWitnessKey, dependency: FunctionPairKey) -> FunctionPairKey {
    let hit = STATE.with(|state| {
        let mut state = state.borrow_mut();
        let Some(s) = state.as_mut() else { return false };
        if matches!(s.fault, Fault::Producer) && s.fired == 0 {
            s.fired += 1;
            true
        } else {
            false
        }
    });
    if hit {
        FunctionPairKey::new(
            key.caller().wrapping_add(1),
            dependency.params().first(),
            dependency.params().second(),
        )
        .unwrap()
    } else {
        dependency
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
#[test]
fn e5_r253_all_nine_preledger_wrappers_preserve_real_integrity_failures() {
    const C: &str = r#"
unsafe extern "C"{fn realloc(p:*mut u8,n:usize)->*mut u8;}
pub unsafe fn resize(p:*mut u8)->*mut u8{realloc(p,16)}
unsafe fn entry(p:*mut u8)->*mut u8{resize(p)}
"#;
    const V: &str = r#"
pub unsafe fn read(p:*const i32)->i32{*p}
unsafe fn entry(p:*const i32)->i32{read(p)}
"#;
    const P: &str = r#"
unsafe fn sink(x:*mut i32,y:*mut i32){*x+=1;*y+=1;}
unsafe fn forward(x:*mut i32,y:*mut i32){sink(x,y);}
unsafe fn entry(p:*mut i32){forward(p,p);}
"#;
    use A5PreledgerDeclineReason as R;
    let cases = [
        (
            R::BaselineConstruction,
            C,
            A5Mode::Baseline,
            false,
            Fault::Construction(1),
        ),
        (
            R::BaselineVerification,
            V,
            A5Mode::Baseline,
            false,
            Fault::Verification(1),
        ),
        (
            R::A5PlanProduction,
            P,
            A5Mode::PreciseReplay,
            true,
            Fault::Producer,
        ),
        (
            R::RefinedFallbackConstruction,
            C,
            A5Mode::PreciseReplay,
            false,
            Fault::Construction(2),
        ),
        (
            R::RefinedFallbackVerification,
            V,
            A5Mode::PreciseReplay,
            false,
            Fault::Verification(2),
        ),
        (
            R::PreciseConstruction,
            C,
            A5Mode::PreciseReplay,
            true,
            Fault::Construction(2),
        ),
        (
            R::PreciseVerification,
            V,
            A5Mode::PreciseReplay,
            true,
            Fault::Verification(2),
        ),
        (
            R::CoarseConstruction,
            C,
            A5Mode::CoarseConstraint,
            true,
            Fault::Construction(2),
        ),
        (
            R::CoarseVerification,
            V,
            A5Mode::CoarseConstraint,
            true,
            Fault::Verification(2),
        ),
    ];
    for (expected, code, mode, attested, fault) in cases {
        with_program(code, |program| {
            let slots = CrateSlots::build(program);
            let origins = compute_origins(program);
            let facts = MutFacts::from_program(program);
            let attestation = attested.then_some(WholeProgramAttestation::FrozenBenchmarkGraph);
            let solve = || {
                solve_bo_a5_config_reporting(program, &slots, &origins, &facts, mode, attestation)
            };
            assert!(solve().is_ok(), "unarmed control {expected:?}");
            let (result, receipt) = with_fault(fault, solve);
            let error = result.expect_err("actual injected integrity failure must not recover");
            assert_eq!(
                receipt.fired, 1,
                "one consumed fault for {expected:?}: {receipt:?}"
            );
            assert_eq!(error.reason(), expected, "actual pipeline stage");
            match fault {
                Fault::Construction(_) => assert!(
                    error
                        .detail()
                        .is_some_and(|detail| detail.contains("StaleSite"))
                ),
                Fault::Verification(_) => assert!(matches!(
                    receipt.terminal,
                    Some(RoundModelFailure::HardUnsat { .. })
                )),
                Fault::Producer => assert!(error.detail().is_some()),
            }
            eprintln!(
                "R245-1 wrapper={expected:?} fault={fault:?} disposition={error:?} receipt={receipt:?}"
            );
        });
    }
}

// These deliberately inject a typed planner coverage cause after the authentic
// source inventory has passed validation. They test the handler boundary, not
// a claim that every cause is reachable from today's source collector.
thread_local! {
    static RECOVERY: RefCell<Option<super::realloc_ssa::ReallocSsaUnsupported>>=const{RefCell::new(None)};
}
fn with_recovery<T>(reason: super::realloc_ssa::ReallocSsaUnsupported, f: impl FnOnce() -> T) -> T {
    struct Reset(Option<super::realloc_ssa::ReallocSsaUnsupported>);
    impl Drop for Reset {
        fn drop(&mut self) {
            RECOVERY.with(|reason| {
                reason.replace(self.0.take());
            });
        }
    }
    let _reset = Reset(RECOVERY.with(|current| current.replace(Some(reason))));
    f()
}
pub(crate) fn recovery_error(
    site: Option<&super::realloc::ReallocSite>,
) -> Option<super::realloc_ssa::ReallocSsaError> {
    RECOVERY
        .with(|current| current.borrow().clone())
        .map(|reason| super::realloc_ssa::ReallocSsaError {
            site: site
                .expect("injected coverage needs a validated realloc")
                .key
                .clone(),
            reason,
        })
}

#[test]
fn e5_r253_every_realloc_coverage_handler_keeps_a_local_model_and_receipt() {
    use rustc_middle::mir::{BasicBlock, Local, Location};

    use super::{
        realloc::ReallocUnsupported as L,
        realloc_ssa::{ReallocSsaUnsupported as U, coverage_hold::Reason as R},
    };
    const CODE: &str = r#"
unsafe extern "C"{fn realloc(p:*mut u8,n:usize)->*mut u8;fn free(p:*mut u8);}
pub unsafe fn f(p:*mut u8){let q=realloc(p,16);if q.is_null(){free(p);}else{free(q);}}
"#;
    let local = Local::from_u32(1);
    let block = BasicBlock::from_u32(0);
    let location = Location {
        block,
        statement_index: 0,
    };
    let cases = [
        (U::MultipleSites, R::MultipleSites),
        (U::AmbiguousOldOwner(local), R::AmbiguousOldOwner),
        (U::ProjectedOldOwner(local), R::ProjectedOldOwner),
        (U::CrossBlockOldProxy(local), R::CrossBlockOldProxy),
        (U::OldOwnerOverwritten(local), R::OldOwnerOverwritten),
        (
            U::OwnershipMeasure { local, measure: 2 },
            R::OwnershipMeasure,
        ),
        (U::ExtraPredecessor(block), R::ExtraPredecessor),
        (U::OutcomeReentry(block), R::OutcomeReentry),
        (U::LiveOutcomeJoin { block, local }, R::LiveOutcomeJoin),
        (U::UnsupportedControlFlow(block), R::ControlFlow),
        (U::UnsupportedTransport(location), R::Transport),
        (U::UnsupportedOwnershipCarrier(local), R::OwnershipCarrier),
        (U::Lifecycle(L::ZeroSize), R::ZeroSize),
        (U::Lifecycle(L::DiscardedResult), R::ResultTest),
        (U::Lifecycle(L::UnresolvedResultTest), R::ResultTest),
    ];
    for (reason, expected) in cases {
        with_program(CODE, |program| {
            let slots = CrateSlots::build(program);
            let origins = compute_origins(program);
            let facts = MutFacts::from_program(program);
            let source = super::realloc::collect_sites(program);
            assert_eq!(source.len(), 1);
            let ((result, capture), plans) = with_recovery(reason.clone(), || {
                let (result, capture) = super::export::with_bo_export(|| {
                    solve_bo_a5_config_reporting(
                        program,
                        &slots,
                        &origins,
                        &facts,
                        A5Mode::PreciseReplay,
                        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
                    )
                });
                let ctxt = super::CrateCtxt::new(program);
                let body = program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(program.functions[0])
                    .borrow();
                let mut defs = super::ssa::consume::initial_definitions(&body, &ctxt);
                let before = defs.def_sites.clone();
                let plans =
                    super::realloc_ssa::plan_body(&ctxt, &body, &mut defs, &source).unwrap();
                assert_eq!(
                    defs.def_sites, before,
                    "held plan adds no outcome SSA definition"
                );
                ((result, capture), plans)
            });
            let model = result
                .unwrap_or_else(|error| panic!("{expected:?} coverage declined: {error:?}"))
                .model;
            assert_eq!(plans.len(), 1);
            assert_eq!(plans[0].coverage_hold, Some(expected));
            assert!(plans[0].operations.is_empty() && plans[0].old.is_none());
            assert!(!capture.realloc_coverage_holds.is_empty());
            for row in &capture.realloc_coverage_holds {
                assert_eq!(row.site, source[0].key);
                assert_eq!(row.reason, expected);
                assert!(!row.slots.is_empty());
                for slot in &row.slots {
                    assert_eq!(model[slot], SlotKind::Raw);
                }
            }
            assert!(capture.realloc_version_sites.is_empty());
            assert!(
                capture
                    .source_events
                    .as_ref()
                    .unwrap()
                    .retirements
                    .keys()
                    .any(|key| key.role == super::source_events::SourceRole::ReallocOld)
            );
            let portable = super::portable_export::collect(program, &slots, &capture).unwrap();
            let rows =
                &portable.families[&super::portable_export::ExportFamily::ReallocCases].records;
            let receipts = rows
                .iter()
                .filter(|row| {
                    row.fields.get("kind").and_then(|v| v.as_str()) == Some("coverage-hold")
                })
                .collect::<Vec<_>>();
            assert_eq!(receipts.len(), capture.realloc_coverage_holds.len());
            assert!(
                receipts
                    .iter()
                    .all(|row| row.fields["receipt"] == "realloc-ssa-coverage:hold-raw")
            );
            eprintln!(
                "R245-1 handler={expected:?} injected_cause={reason:?} sites=1 receipts={} outcome=held-model",
                receipts.len()
            );
        });
    }
}

#[test]
fn e5_r253_no_candidate_holder_has_exact_portable_irrelevance_receipts() {
    const CODE: &str = r#"
pub fn address_only()->usize{let mut value=1i32;(&raw mut value) as usize}
"#;
    with_program(CODE, |program| {
        let slots = CrateSlots::build(program);
        let origins = compute_origins(program);
        let facts = MutFacts::from_program(program);
        let (result, capture) = with_all_raw(|| {
            super::export::with_bo_export(|| {
                solve_bo_a5_config_reporting(
                    program,
                    &slots,
                    &origins,
                    &facts,
                    A5Mode::PreciseReplay,
                    Some(WholeProgramAttestation::FrozenBenchmarkGraph),
                )
            })
        });
        assert!(result.is_ok());
        assert!(
            result
                .as_ref()
                .unwrap()
                .model
                .values()
                .all(|kind| *kind == SlotKind::Raw)
        );

        let review = capture.source_retirement.as_ref().unwrap();
        let count = review
            .coverage
            .iter()
            .filter(|row| {
                row.disposition == super::retirement::CoverageDisposition::IrrelevantNoSafeHolder
            })
            .count();
        assert!(
            count > 0,
            "fixture requires actual no-candidate-holder evidence"
        );
        let portable = super::portable_export::collect(program, &slots, &capture).unwrap();
        let row = &portable.families[&super::portable_export::ExportFamily::RetirementFinal]
            .records[0]
            .fields;
        let receipts = row["coverage"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["receipt"] == "retirement:irrelevant-no-safe-holder")
            .count();
        assert_eq!(receipts, count);
        eprintln!("R245-1 no-holder source_context_receipts={count}");
    });
}

thread_local! {static ALL_RAW:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};}
fn with_all_raw<T>(f: impl FnOnce() -> T) -> T {
    struct Reset(bool);
    impl Drop for Reset {
        fn drop(&mut self) {
            ALL_RAW.with(|active| active.set(self.0));
        }
    }
    let _reset = Reset(ALL_RAW.with(|active| active.replace(true)));
    f()
}

#[test]
fn e5_r253_realloc_inventory_corruption_precedes_coverage_fallback() {
    use rustc_middle::mir::{Local, Location};

    use super::{
        realloc::{
            ReallocCalleeIdentity as C, ReallocResult as Result, ReallocSize, ResultTransport,
        },
        realloc_ssa::{ReallocSsaUnsupported as U, plan_body},
    };
    const CODE: &str = r#"
unsafe extern "C"{fn realloc(p:*mut u8,n:usize)->*mut u8;fn free(p:*mut u8);}
pub unsafe fn f(p:*mut u8){let q=realloc(p,16);if q.is_null(){free(p);}else{free(q);}}
"#;
    with_program(CODE, |program| {
        let ctxt = super::CrateCtxt::new(program);
        let function = program.functions[0];
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let sites = super::realloc::collect_sites(program);
        assert_eq!(sites.len(), 1);
        let Result::DirectBranch(branch) = &sites[0].result else {
            panic!("actual direct-branch fixture")
        };
        let mut valid = super::ssa::consume::initial_definitions(&body, &ctxt);
        let valid_plans = plan_body(&ctxt, &body, &mut valid, &sites).unwrap();
        assert!(valid_plans.iter().all(|plan| plan.coverage_hold.is_none()));
        let mut cases = Vec::new();
        let mut push = |label: &str, change: fn(&mut super::realloc::ReallocSite)| {
            let mut damaged = sites.clone();
            change(&mut damaged[0]);
            assert_ne!(
                damaged, sites,
                "a deliberate metadata fault must change its witness"
            );
            cases.push((label.to_owned(), damaged));
        };
        push("function", |site| site.key.function.push_str("_wrong"));
        push("block", |site| site.key.block += 1);
        push("statement", |site| site.key.statement += 1);
        push("phase", |site| {
            site.key.phase = super::source_events::SourcePhase::Statement
        });
        push("callee", |site| site.callee = C::Other);
        push("requested-size", |site| site.size = ReallocSize::Unknown);
        push("old-input", |site| {
            site.old_input = super::realloc::OldInput::KnownNull
        });
        push("missing-result", |site| site.result = Result::Discarded);
        push("old-place", |site| {
            let Result::DirectBranch(b) = &mut site.result else { unreachable!() };
            b.old = None;
        });
        push("result-local", |site| {
            let Result::DirectBranch(b) = &mut site.result else { unreachable!() };
            b.result = Local::from_u32(b.result.as_u32() + 1);
        });
        push("test-location", |site| {
            let Result::DirectBranch(b) = &mut site.result else { unreachable!() };
            b.test.statement_index += 1;
        });
        push("equal-outcomes", |site| {
            let Result::DirectBranch(b) = &mut site.result else { unreachable!() };
            b.success = b.failure;
        });
        push("transport-location", |site| {
            let Result::DirectBranch(b) = &mut site.result else { unreachable!() };
            if let Some(t) = b.transports.first_mut() {
                t.location.statement_index += 1;
            } else {
                b.transports.push(ResultTransport {
                    location: b.test,
                    source: b.result,
                    destination: b.result,
                });
            }
        });
        push("transport-source", |site| {
            let Result::DirectBranch(b) = &mut site.result else { unreachable!() };
            if let Some(t) = b.transports.first_mut() {
                t.source = Local::from_u32(t.source.as_u32() + 1);
            } else {
                b.transports.push(ResultTransport {
                    location: b.test,
                    source: Local::from_u32(1),
                    destination: b.result,
                });
            }
        });
        let mut duplicate = sites.clone();
        duplicate.push(sites[0].clone());
        cases.push(("duplicate".to_owned(), duplicate));
        cases.push(("empty".to_owned(), vec![]));
        for (label, damaged) in cases {
            let mut definitions = super::ssa::consume::initial_definitions(&body, &ctxt);
            let before = definitions.def_sites.clone();
            let error = with_recovery(U::MultipleSites, || {
                plan_body(&ctxt, &body, &mut definitions, &damaged)
            })
            .unwrap_err();
            assert_eq!(
                error.reason,
                U::StaleSite,
                "{label}: integrity must precede forced coverage"
            );
            assert_eq!(
                definitions.def_sites, before,
                "{label}: no partial SSA writes"
            );
            eprintln!(
                "R245-1 realloc_metadata_fault={label} reason={:?} outcome=integrity-rejected",
                error.reason
            );
        }
        // A required definition is an integrity error, separate from an
        // unsupported compiler call-argument carrier. No coverage fault is armed.
        for missing_sites in [false, true] {
            let mut definitions = super::ssa::consume::initial_definitions(&body, &ctxt);
            let old = Local::from_u32(1);
            assert!(definitions.locals_with_defs.contains(old));
            if missing_sites {
                definitions.def_sites[old].clear();
            } else {
                definitions.locals_with_defs.remove(old);
            }
            let error = plan_body(&ctxt, &body, &mut definitions, &sites).unwrap_err();
            assert_eq!(error.reason, U::MissingOwnershipDefinition(old));
            eprintln!(
                "R245-1 required_definition_fault=missing-sites:{missing_sites} outcome=integrity-rejected"
            );
        }
        let _actual_test: Location = branch.test;
    });
}

#[test]
fn e5_r253_realloc_terminal_causes_never_become_coverage_holds() {
    use rustc_middle::mir::{BasicBlock, Local, Location};

    use super::{realloc::ReallocUnsupported as L, realloc_ssa::ReallocSsaUnsupported as U};
    const CODE: &str = r#"
unsafe extern "C"{fn realloc(p:*mut u8,n:usize)->*mut u8;}
pub unsafe fn f(p:*mut u8)->*mut u8{realloc(p,16)}
"#;
    let causes = [
        U::StaleSite,
        U::MissingOwnershipDefinition(Local::from_u32(1)),
        U::InvalidTransport(Location {
            block: BasicBlock::from_u32(0),
            statement_index: 0,
        }),
        U::Lifecycle(L::NotForeignCRealloc),
        U::Lifecycle(L::UnknownSize),
    ];
    for reason in causes {
        with_program(CODE, |program| {
            let slots = CrateSlots::build(program);
            let origins = compute_origins(program);
            let facts = MutFacts::from_program(program);
            let result = with_recovery(reason.clone(), || {
                solve_bo_a5_config_reporting(
                    program,
                    &slots,
                    &origins,
                    &facts,
                    A5Mode::PreciseReplay,
                    Some(WholeProgramAttestation::FrozenBenchmarkGraph),
                )
            });
            let error = result.expect_err("terminal planner cause must remain a refusal");
            assert_eq!(
                error.reason(),
                A5PreledgerDeclineReason::BaselineConstruction
            );
            assert!(
                error
                    .detail()
                    .is_some_and(|text| text.contains(&format!("{reason:?}")))
            );
            eprintln!("R245-1 planner_terminal={reason:?} outcome=declined-with-original-cause");
        });
    }
}

#[test]
fn e5_r253_each_held_carrier_has_an_effective_raw_restriction() {
    // Primitive enforcement control; the full A5 path is checked independently
    // by the coverage-handler and actual multiple-site construction witnesses.
    const CODE: &str = r#"
unsafe extern "C"{fn realloc(p:*mut u8,n:usize)->*mut u8;fn free(p:*mut u8);}
pub unsafe fn f(a:*mut u8,b:*mut u8){
 let p=realloc(a,16);if p.is_null(){free(a);}else{free(p);}
 let q=realloc(b,16);if q.is_null(){free(b);}else{free(q);}
}
"#;
    with_program(CODE, |program| {
        let slots = CrateSlots::build(program);
        let ctxt = super::CrateCtxt::new(program);
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(program.functions[0])
            .borrow();
        let sites = super::realloc::collect_sites(program);
        assert_eq!(sites.len(), 2);
        let mut definitions = super::ssa::consume::initial_definitions(&body, &ctxt);
        let plans = super::realloc_ssa::plan_body(&ctxt, &body, &mut definitions, &sites).unwrap();
        assert_eq!(plans.len(), 2);
        assert!(plans.iter().all(|plan| plan.coverage_hold
            == Some(super::realloc_ssa::coverage_hold::Reason::MultipleSites)));
        let probe = KindSolver::new(&slots);
        let (_, capture) = super::export::with_bo_export(|| {
            super::realloc_ssa::constrain_coverage_holds(&ctxt, &body, &slots, &probe, &plans)
        });
        assert_eq!(
            capture.realloc_coverage_holds.len(),
            2,
            "one primitive hold receipt per actual site"
        );
        let targets = capture
            .realloc_coverage_holds
            .iter()
            .flat_map(|row| row.slots.iter().copied())
            .collect::<rustc_hash::FxHashSet<_>>();
        assert!(!targets.is_empty());
        for target in &targets {
            let control = KindSolver::new(&slots);
            control.assume(*target, SlotKind::Ref);
            assert_eq!(
                control.check(),
                z3::SatResult::Sat,
                "unrestricted slot admits Ref"
            );
            let held = KindSolver::new(&slots);
            super::realloc_ssa::constrain_coverage_holds(&ctxt, &body, &slots, &held, &plans);
            held.assume(*target, SlotKind::Ref);
            assert_eq!(
                held.check(),
                z3::SatResult::Unsat,
                "held carrier must have an effective Raw restriction"
            );
        }
        eprintln!(
            "R245-1 held_restrictions={} sites=2 every_contradiction=unsat",
            targets.len()
        );
    });
}

fn owning_outer_raw_delivery(l2: bool) {
    use rustc_middle::mir::VarDebugInfoContents;

    use super::{borrow_verify, construction};
    const CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub unsafe fn f(){let p=malloc(core::mem::size_of::<*mut i32>()) as *mut *mut i32;free(p as *mut core::ffi::c_void);}
"#;
    with_program(CODE, |program| {
        let slots = CrateSlots::build(program);
        let origins = compute_origins(program);
        let facts = MutFacts::from_program(program);
        let function = program.functions[0];
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let p = body
            .var_debug_info
            .iter()
            .find_map(|info| {
                if info.name.as_str() != "p" {
                    return None;
                }
                let VarDebugInfoContents::Place(place) = info.value else {
                    return None;
                };
                place.as_local()
            })
            .expect("actual p binding");
        let outer = SlotRef::Local(
            function,
            slots.fn_local_slots[&function]
                .slot_for_local_depth(p, 0)
                .unwrap(),
        );
        let inner = SlotRef::Local(
            function,
            slots.fn_local_slots[&function]
                .slot_for_local_depth(p, 1)
                .unwrap(),
        );
        let solver = KindSolver::new(&slots);
        let c = construction::construct_bo_into(
            program,
            &slots,
            &origins,
            &facts,
            &solver,
            construction::CopyLendMode::Baseline,
        )
        .unwrap();
        let initial = solver.model_kinds_relaxing(&c.selectors).unwrap();
        assert_eq!(
            initial[&outer],
            SlotKind::Owning,
            "fixture requires an Owning outer responsibility"
        );
        assert_eq!(
            initial[&inner],
            SlotKind::Ref,
            "fixture requires a real unrepresented Ref inner holder"
        );
        // Inspect the initial model before the new branch runs. This replay
        // returns ordinary/represented-loan edges, not local coverage demotions.
        let ordinary_probe = {
            let _model = super::retirement::model_scope(&initial);
            borrow_verify::revalidate_replaying(
                program,
                &slots,
                |slot| initial.get(&slot) == Some(&SlotKind::Ref),
                |slot| initial.get(&slot) != Some(&SlotKind::Ref),
                &facts,
            )
        };
        assert!(
            ordinary_probe.values().all(|edges| edges.is_empty()),
            "ordinary repair must not explain this fixture's inner demotion"
        );
        let ((result, ordinary, raw), capture) = super::export::with_bo_export(|| {
            let ((result, ordinary), raw) = borrow_verify::raw_commit_trace::with_capture(|| {
                borrow_verify::with_mode_a_commit_trace(|| {
                    if l2 {
                        construction::verify_bo_construction_l2_for_test(
                            program,
                            &slots,
                            &origins,
                            &solver,
                            &c,
                            &facts,
                            construction::TestValidationBackend::HardCheckRoundOptimize,
                        )
                    } else {
                        construction::verify_bo_construction_counting_for_test(
                            program,
                            &slots,
                            &origins,
                            &solver,
                            &c,
                            &facts,
                            construction::TestValidationBackend::HardCheckRoundOptimize,
                        )
                    }
                })
            });
            (result, ordinary, raw)
        });
        let (model, stats) = result;
        assert!(
            capture
                .retirement_rounds
                .iter()
                .flat_map(|round| &round.demotions)
                .any(|row| row.holder == inner
                    && row.reason.label() == "p1s-inner-loan-missing:demote"),
            "typed inner-loan receipt is required"
        );
        assert!(
            !raw.is_empty(),
            "retirement Raw-commit target-set trace is required"
        );
        assert!(
            ordinary.is_empty(),
            "ordinary commits must not substitute for the new branch"
        );
        for commit in &raw {
            assert_eq!(commit.l2, l2);
            let review = &capture.retirement_rounds[commit.round - 1];
            let expected = review
                .demotions
                .iter()
                .flat_map(|row| row.chain.iter().copied())
                .collect::<rustc_hash::FxHashSet<_>>();
            let actual = commit
                .targets
                .iter()
                .copied()
                .collect::<rustc_hash::FxHashSet<_>>();
            assert_eq!(
                actual.len(),
                commit.targets.len(),
                "actual commit target identity has no duplicates"
            );
            assert_eq!(
                actual, expected,
                "Raw-commit target set must equal the typed receipt targets"
            );
            assert!(actual.contains(&inner));
            assert!(!actual.contains(&outer));
            assert!(actual.iter().all(|slot| initial[slot] == SlotKind::Ref));
            for row in &review.demotions {
                assert_eq!(
                    row.reason,
                    super::retirement::local_outcome::Reason::InnerLoanMissing { depth: 1 }
                );
                assert_eq!(row.source.role, super::source_events::SourceRole::Free);
                assert!(c.source_events.retirements.contains_key(&row.source));
            }
            eprintln!(
                "R258 raw_delivery_l2={l2} round={} own_target_set={:?} typed_receipt=p1s-inner-loan-missing:demote",
                commit.round, actual
            );
        }
        assert!(stats.source_retirement_decline.is_empty());
        let model = model.expect("local recovery retains the model");
        assert_eq!(model[&outer], SlotKind::Owning);
        assert_eq!(model[&inner], SlotKind::Raw);
    });
}
#[test]
fn e5_r258_normal_raw_delivery_has_own_target_identity() {
    owning_outer_raw_delivery(false);
}
#[test]
fn e5_r258_l2_raw_delivery_has_own_target_identity() {
    owning_outer_raw_delivery(true);
}

#[test]
fn e5_r258_realloc_source_shape_reachability_inventory() {
    const PRELUDE: &str = r#"unsafe extern "C"{fn realloc(p:*mut u8,n:usize)->*mut u8;fn tick();fn other()->*mut u8;}"#;
    let cases = [
        (
            "addressed-owner",
            r#"pub unsafe fn f(mut p:*mut u8)->u8{let _address=&raw mut p;let q=realloc(p,16);if q.is_null(){0}else{1}}"#,
        ),
        (
            "branch-defined-proxy",
            r#"pub unsafe fn f(p:*mut u8,other:*mut u8,c:bool)->u8{let q=realloc(if c{p}else{other},16);if q.is_null(){0}else{1}}"#,
        ),
        (
            "projected-owner",
            r#"pub unsafe fn f(slot:*mut *mut u8)->u8{let q=realloc(*slot,16);if q.is_null(){0}else{1}}"#,
        ),
        (
            "cross-block-proxy",
            r#"pub unsafe fn f(p:*mut u8)->u8{let q=realloc(p,{tick();16});if q.is_null(){0}else{1}}"#,
        ),
        (
            "overwritten-owner",
            r#"pub unsafe fn f(mut p:*mut u8,other:*mut u8)->u8{let q=realloc(p,{p=other;16});if q.is_null(){0}else{1}}"#,
        ),
        (
            "same-local-result",
            r#"pub unsafe fn f(mut p:*mut u8)->u8{p=realloc(p,16);if p.is_null(){0}else{1}}"#,
        ),
        (
            "post-call-old-write",
            r#"pub unsafe fn f(mut p:*mut u8,other:*mut u8)->u8{let q=realloc(p,16);p=other;if q.is_null(){0}else{1}}"#,
        ),
        (
            "old-storage-dead",
            r#"pub unsafe fn f(p:*mut u8)->u8{let q;{let old=p;q=realloc(old,16);}if q.is_null(){0}else{1}}"#,
        ),
        (
            "old-call-destination",
            r#"pub unsafe fn f(mut p:*mut u8)->u8{let q=realloc(p,16);p=other();if q.is_null(){0}else{1}}"#,
        ),
        (
            "two-depth-measure",
            r#"pub unsafe fn f(p:*mut *mut u8)->u8{let q=realloc(p as *mut u8,16);if q.is_null(){0}else{1}}"#,
        ),
        (
            "unnamed-result-carrier",
            r#"pub unsafe fn f(p:*mut u8)->u8{if realloc(p,16).is_null(){0}else{1}}"#,
        ),
        (
            "outcome-reentry",
            r#"pub unsafe fn f(p:*mut u8)->*mut u8{loop{let q=realloc(p,16);if q.is_null(){tick();continue;}return q;}}"#,
        ),
        (
            "outcome-entry-early-return",
            r#"pub unsafe fn f(p:*mut u8,skip:bool){if skip{return;}let q=realloc(p,16);if q.is_null(){return;}tick();}"#,
        ),
    ];
    for (name, body_source) in cases {
        let code = format!("{PRELUDE}\n{body_source}");
        with_program(&code, |program| {
            let sites = super::realloc::collect_sites(program);
            assert_eq!(sites.len(), 1);
            let ctxt = super::CrateCtxt::new(program);
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(program.functions[0])
                .borrow();
            let mut definitions = super::ssa::consume::initial_definitions(&body, &ctxt);
            let plans = super::realloc_ssa::plan_body(&ctxt, &body, &mut definitions, &sites)
                .expect("classified source representation retains a local plan");
            assert_eq!(plans.len(), 1);
            use super::realloc_ssa::coverage_hold::Reason as H;
            let expected = match name {
                "addressed-owner" | "branch-defined-proxy" => Some(H::AmbiguousOldOwner),
                "projected-owner" => Some(H::ProjectedOldOwner),
                "cross-block-proxy" | "overwritten-owner" => Some(H::ZeroSize),
                "same-local-result" | "two-depth-measure" => Some(H::OldOwnerOverwritten),
                "unnamed-result-carrier" => Some(H::OwnershipCarrier),
                "outcome-reentry" => Some(H::OutcomeReentry),
                "post-call-old-write"
                | "old-storage-dead"
                | "old-call-destination"
                | "outcome-entry-early-return" => None,
                _ => unreachable!("named source witness"),
            };
            assert_eq!(
                plans[0].coverage_hold, expected,
                "source-shape reachability receipt"
            );
            if matches!(
                name,
                "post-call-old-write" | "old-storage-dead" | "old-call-destination"
            ) {
                assert_eq!(
                    sites[0].result.result_test_receipt(),
                    Some(super::realloc::ReallocResultTestReceipt::FallbackBothOutcomes)
                );
            }
            eprintln!(
                "R258 reachability={name} result={:?} hold={:?}",
                sites[0].result, plans[0].coverage_hold
            );
            if plans[0].coverage_hold.is_some() {
                assert!(plans[0].operations.is_empty() && plans[0].old.is_none());
            }
        });
    }
}

#[test]
fn e5_r258_realloc_guarded_and_nested_source_reachability() {
    const PLAIN: &str = r#"unsafe extern "C"{fn realloc(p:*mut u8,n:usize)->*mut u8;fn tick();}"#;
    const NESTED: &str = r#"unsafe extern "C"{fn realloc(p:*mut *mut u8,n:usize)->*mut *mut u8;}"#;
    let cases = [
        (
            "guarded-cross-block",
            PLAIN,
            r#"pub unsafe fn f(p:*mut u8,n:usize)->u8{if n==0{return 0;}let q=realloc(p,{tick();n});if q.is_null(){0}else{1}}"#,
        ),
        (
            "guarded-old-write",
            PLAIN,
            r#"pub unsafe fn f(mut p:*mut u8,other:*mut u8,n:usize)->u8{if n==0{return 0;}let q=realloc(p,{p=other;n});if q.is_null(){0}else{1}}"#,
        ),
        (
            "nested-declaration",
            NESTED,
            r#"pub unsafe fn f(p:*mut *mut u8)->u8{let q=realloc(p,16);if q.is_null(){0}else{1}}"#,
        ),
    ];
    for (name, prelude, body_source) in cases {
        let code = format!("{prelude}\n{body_source}");
        with_program(&code, |program| {
            let sites = super::realloc::collect_sites(program);
            assert_eq!(sites.len(), 1);
            let ctxt = super::CrateCtxt::new(program);
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(program.functions[0])
                .borrow();
            let mut definitions = super::ssa::consume::initial_definitions(&body, &ctxt);
            let plans = super::realloc_ssa::plan_body(&ctxt, &body, &mut definitions, &sites)
                .expect("classified source representation keeps its plan");
            assert_eq!(plans.len(), 1);
            use super::realloc_ssa::coverage_hold::Reason as H;
            let expected = match name {
                "guarded-cross-block" => H::CrossBlockOldProxy,
                "guarded-old-write" => H::OldOwnerOverwritten,
                "nested-declaration" => H::OwnershipMeasure,
                _ => unreachable!("named source witness"),
            };
            assert_eq!(
                plans[0].coverage_hold,
                Some(expected),
                "guarded source-shape reachability receipt"
            );
            eprintln!(
                "R258 reachability={name} size={:?} zero={:?} result={:?} hold={:?}",
                sites[0].size, sites[0].zero_size, sites[0].result, plans[0].coverage_hold
            );
        });
    }
}
