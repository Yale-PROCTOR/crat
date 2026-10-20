//! Compiler-backed RED contracts over existing T2 queries and construction.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{BasicBlock, Location, Operand, TerminatorKind};

use super::*;
use crate::{
    analyses::borrow_ownership::{
        BoOwnEmissionStats, SlotKind,
        construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
        export::{self, BoExport, PlaceKey},
        mutability_facts::MutFacts,
        origins::compute_origins,
        solver::{
            KindSolver, SelectorTrace, SelectorTraceOutcome, SelectorTracePhase, SlotRef,
            with_selector_trace,
        },
        source_events,
    },
    utils::rustc::RustProgram,
};

struct Run {
    model: FxHashMap<SlotRef, SlotKind>,
    stats: BoOwnEmissionStats,
    keys: Vec<T2AssertKey>,
    trace: SelectorTrace,
}

fn inspect(code: &str, check: impl FnOnce(&RustProgram<'_>, &Run, &DemandEvidence) + Send + Sync) {
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
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let run = || {
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("production construction");
            let ((model, _), trace) = with_selector_trace(|| {
                verify_bo_construction_counting(
                    &program,
                    &slots,
                    &origins,
                    &solver,
                    &construction,
                    &facts,
                )
            });
            Run {
                model: model.expect("accepted demand fixture"),
                stats: construction.stats,
                keys: construction.selectors.keys().to_vec(),
                trace,
            }
        };
        assert!(!export::capturing());
        let plain = run();
        let (captured, output): (Run, BoExport) = export::with_bo_export(run);
        assert_eq!(
            plain.model, captured.model,
            "demand capture cannot alter any final kind"
        );
        assert_eq!(
            plain.stats, captured.stats,
            "demand capture cannot alter ownership emission"
        );
        assert_eq!(
            plain.keys, captured.keys,
            "demand capture cannot add or change T2 endpoints"
        );
        let evidence = output
            .demand_evidence
            .as_ref()
            .expect("demand evidence must be captured");
        assert_eq!(evidence.licensing, LicensingDisposition::Deferred);
        evidence
            .validate()
            .expect("complete demand evidence structure");
        let bytes = evidence.canonical_json().unwrap();
        let json: serde_json::Value = serde_json::from_str(&bytes).unwrap();
        assert_eq!(json["schema"], SCHEMA);
        assert_eq!(json["licensing"], "deferred");
        let mut reversed = evidence.clone();
        reversed.constructions.reverse();
        for unit in &mut reversed.constructions {
            unit.endpoints.reverse();
            unit.queries.reverse();
            unit.final_selections.reverse();
        }
        assert_eq!(reversed.canonical_json().unwrap(), bytes);
        check(&program, &captured, evidence);
    })
    .unwrap_or_else(|error| error.raise());
}

fn checked_unit<'a>(
    program: &RustProgram<'_>,
    run: &Run,
    evidence: &'a DemandEvidence,
) -> &'a ConstructionEvidence {
    assert_eq!(
        evidence.constructions.len(),
        1,
        "one actual construction unit"
    );
    let unit = &evidence.constructions[0];
    assert_eq!(unit.endpoints.len(), run.keys.len());
    let unique: BTreeSet<_> = unit
        .endpoints
        .iter()
        .map(|endpoint| endpoint.key.clone())
        .collect();
    assert_eq!(
        unique.len(),
        unit.endpoints.len(),
        "endpoint keys exclude diagnostic Var identities"
    );
    for (index, original) in run.keys.iter().enumerate() {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(original.fn_did)
            .borrow();
        let location = Location {
            block: BasicBlock::from_u32(original.location.block),
            statement_index: original.location.statement_index,
        };
        assert_eq!(
            location.statement_index,
            body.basic_blocks[location.block].statements.len()
        );
        let TerminatorKind::Call {
            args, destination, ..
        } = &body.basic_blocks[location.block].terminator().kind
        else {
            panic!("fixture endpoint must retain its original call");
        };
        let place = match original.role {
            BoundaryRole::Source => Some(PlaceKey::from_place(*destination)),
            BoundaryRole::Sink => args
                .first()
                .and_then(|arg| arg.node.place())
                .map(PlaceKey::from_place),
        };
        let operand = match place {
            Some(place) => OperandIdentity::Place {
                local: place.local.as_u32(),
                projections: place.proj,
            },
            None if args.first().is_some_and(|arg| {
                matches!(arg.node, Operand::Constant(_))
                    && source_events::operand_is_null(&arg.node, &[], program.tcx)
            }) =>
            {
                OperandIdentity::Null
            }
            None => panic!("fixture must expose an exact source operand"),
        };
        let expected = EndpointKey {
            construction: unit.id,
            function: original.function_path.clone(),
            block: original.location.block,
            statement: original.location.statement_index,
            role: original.role,
            realloc_outcome: original.realloc_outcome,
            operand,
        };
        let found: Vec<_> = unit
            .endpoints
            .iter()
            .filter(|endpoint| endpoint.key == expected)
            .collect();
        assert_eq!(
            found.len(),
            1,
            "original call/role/outcome/operand identity"
        );
        assert_eq!(found[0].diagnostic_selector_index, index);
        assert_eq!(found[0].diagnostic_var, original.var.as_u32());
    }
    let mut event_ids = BTreeSet::new();
    for event in &unit.queries {
        assert_eq!(event.id.epoch.construction, unit.id);
        assert!(
            event_ids.insert(event.id),
            "query events have their own unique identities"
        );
        for endpoint in event
            .active
            .iter()
            .chain(&event.core_endpoints)
            .chain(event.candidate.iter())
        {
            assert!(
                unique.contains(endpoint),
                "query endpoint belongs to this construction"
            );
        }
    }
    assert_eq!(unit.final_selections.len(), run.trace.epochs.len());
    for (ordinal, epoch) in run.trace.epochs.iter().enumerate() {
        let key = EpochId {
            construction: unit.id,
            ordinal: ordinal as u32,
        };
        let states: Vec<_> = unit
            .final_selections
            .iter()
            .filter(|state| state.epoch == key)
            .collect();
        assert_eq!(states.len(), 1);
        assert_eq!(states[0].outcome, QueryOutcome::Sat);
        let expected: BTreeSet<_> = epoch
            .final_dropped
            .iter()
            .map(|index| {
                unit.endpoints
                    .iter()
                    .find(|endpoint| endpoint.diagnostic_selector_index == *index)
                    .unwrap()
                    .key
                    .clone()
            })
            .collect();
        assert_eq!(
            states[0]
                .dropped
                .as_ref()
                .expect("completed selector state")
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>(),
            expected
        );
    }
    unit
}

#[test]
fn e5_h_linear_partner_free_has_source_endpoints_without_new_demand() {
    const CODE: &str = "unsafe extern \"C\" { fn malloc(n: usize) -> *mut u8; fn free(p: *mut u8); } pub unsafe fn f() { let p = malloc(8); let q = p; free(q); }";
    inspect(CODE, |program, run, evidence| {
        assert_eq!(run.keys.len(), 2, "allocation and actual partner free only");
        let unit = checked_unit(program, run, evidence);
        assert!(
            unit.queries
                .iter()
                .any(|query| query.phase == QueryPhase::SelectorSearch
                    && query.outcome == QueryOutcome::Sat)
        );
        assert!(
            unit.final_selections
                .last()
                .unwrap()
                .dropped
                .as_ref()
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            unit.endpoints
                .iter()
                .filter(|endpoint| endpoint.key.role == BoundaryRole::Source)
                .count(),
            1
        );
        assert_eq!(
            unit.endpoints
                .iter()
                .filter(|endpoint| endpoint.key.role == BoundaryRole::Sink)
                .count(),
            1
        );
    });
}

#[test]
fn e5_h_opaque_old_realloc_preserves_exact_mixed_cores_and_restoration() {
    const CODE: &str = "unsafe extern \"C\" { fn opaque() -> *mut u8; fn realloc(p: *mut u8, n: usize) -> *mut u8; } pub unsafe fn f() { let p = opaque(); let _q = realloc(p, 8); }";
    inspect(CODE, |program, run, evidence| {
        assert_eq!(run.keys.len(), 2);
        let unit = checked_unit(program, run, evidence);
        let sink = unit
            .endpoints
            .iter()
            .find(|endpoint| endpoint.key.role == BoundaryRole::Sink)
            .unwrap();
        assert_eq!(sink.key.realloc_outcome, Some(ReallocOutcome::Success));
        let labels: BTreeSet<_> = run.keys.iter().map(T2AssertKey::label).collect();
        let epoch = run.trace.epochs.last().expect("actual selector epoch");
        for (phase, expected_phase, outcome) in [
            (
                SelectorTracePhase::Drop,
                QueryPhase::SelectorSearch,
                SelectorTraceOutcome::Dropped,
            ),
            (
                SelectorTracePhase::Reenable,
                QueryPhase::Restoration,
                SelectorTraceOutcome::StayedDropped,
            ),
        ] {
            let legacy = epoch
                .events
                .iter()
                .find(|event| {
                    event.selector_index == sink.diagnostic_selector_index
                        && event.phase == phase
                        && event.outcome == outcome
                })
                .expect("existing mixed-core sink event");
            let mandatory: BTreeSet<_> = legacy
                .core_labels
                .iter()
                .filter(|label| !labels.contains(*label))
                .cloned()
                .collect();
            assert!(!mandatory.is_empty());
            assert!(
                mandatory
                    .iter()
                    .any(|label| label.contains("own-assume") || label.contains("link-own"))
            );
            let queries: Vec<_> = unit
                .queries
                .iter()
                .filter(|event| {
                    event.phase == expected_phase
                        && event.candidate.as_ref() == Some(&sink.key)
                        && event.outcome == QueryOutcome::Unsat
                })
                .collect();
            assert!(
                !queries.is_empty(),
                "actual UNSAT query outcome must be exported, not inferred from a status name"
            );
            assert!(
                queries
                    .iter()
                    .any(|query| query.core_endpoints.contains(&sink.key)
                        && query
                            .mandatory_core_labels
                            .iter()
                            .cloned()
                            .collect::<BTreeSet<_>>()
                            == mandatory),
                "every mandatory core label must survive without nearest-free attribution"
            );
        }
        assert_eq!(
            unit.final_selections
                .last()
                .unwrap()
                .dropped
                .as_ref()
                .unwrap()
                .len(),
            2
        );
    });
}

#[test]
fn e5_h_realloc_outcomes_do_not_alias_ordinary_free_endpoint_keys() {
    const CODE: &str = "unsafe extern \"C\" { fn realloc(p: *mut u8, n: usize) -> *mut u8; fn free(p: *mut u8); } pub unsafe fn f(p: *mut u8) { let q = realloc(p, 8); if q.is_null() { free(p); } else { free(q); } }";
    inspect(CODE, |program, run, evidence| {
        assert_eq!(
            run.keys
                .iter()
                .filter(|key| key.callee == "realloc")
                .count(),
            2
        );
        assert_eq!(
            run.keys.iter().filter(|key| key.callee == "free").count(),
            2
        );
        let unit = checked_unit(program, run, evidence);
        assert_eq!(
            unit.endpoints
                .iter()
                .filter(|endpoint| endpoint.key.realloc_outcome == Some(ReallocOutcome::Success))
                .count(),
            2
        );
        assert_eq!(
            unit.endpoints
                .iter()
                .filter(|endpoint| endpoint.key.realloc_outcome.is_none())
                .count(),
            2
        );
        assert!(
            unit.final_selections
                .last()
                .unwrap()
                .dropped
                .as_ref()
                .unwrap()
                .is_empty()
        );
    });
}

#[test]
fn e5_h_demand_unknown_query_cannot_be_declared_terminal_success() {
    inspect(
        "unsafe extern \"C\" {fn malloc(n:usize)->*mut u8;fn free(p:*mut u8);} pub unsafe fn f(){let p=malloc(8);free(p);}",
        |_, _, evidence| {
            let mut forged = evidence.clone();
            let unit = &mut forged.constructions[0];
            let event = unit.queries.last_mut().unwrap();
            event.outcome = QueryOutcome::Unknown {
                reason: "injected-unknown".into(),
            };
            event.core_endpoints.clear();
            event.mandatory_core_labels.clear();
            event.candidate = None;
            assert!(
                forged.validate().is_err(),
                "an actual Unknown cannot become terminal success"
            );
            let unit = &mut forged.constructions[0];
            let event = unit.queries.last().unwrap();
            let terminal = unit
                .final_selections
                .iter_mut()
                .find(|row| row.epoch == event.id.epoch)
                .unwrap();
            terminal.outcome = event.outcome.clone();
            terminal.dropped = None;
            forged
                .validate()
                .expect("actual Unknown stays explicitly incomplete");
            let mut duplicate = evidence.clone();
            let row = duplicate.constructions[0].queries[0].clone();
            duplicate.constructions[0].queries.push(row);
            assert!(duplicate.validate().is_err());
        },
    );
}
