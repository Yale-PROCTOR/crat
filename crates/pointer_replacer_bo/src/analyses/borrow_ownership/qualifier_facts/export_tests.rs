//! F09/F10 construction, canonical serialization, and capture-neutrality gates.
//! Standard qualifier producers are observed; no rewriter or corpus worker runs.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::{Local, VarDebugInfoContents};
use serde_json::Value;

use super::*;
use crate::analyses::borrow_ownership::{
    BoOwnEmissionStats, SlotKind,
    borrow_verify::RoundStats,
    construction::{
        CopyLendMode, TestValidationBackend, construct_bo_into,
        verify_bo_construction_counting_for_test,
    },
    export::{self, BoundaryRole, T2AssertKey},
    nullability,
    origins::compute_origins,
    slot_key,
    slots::SlotOwner,
    solver::{KindSolver, SlotRef},
};

const SOURCE: &str = r#"
unsafe extern "C" { fn malloc(bytes: usize) -> *mut u8; fn free(pointer: *mut u8); }
pub unsafe fn qualifiers(p: *mut i32, pp: *mut *mut i32, rr: &mut *mut i32) -> i32 {
    let shifted = p.offset(1);
    *shifted + **pp + **rr
}
pub unsafe fn returned(p: *mut i32) -> *mut i32 { p }
pub unsafe fn allocation() { let owner = malloc(8); free(owner); }
"#;

fn inspect(check: impl Fn(&RustProgram<'_>, &CrateSlots) + Send + Sync) {
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
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        check(&program, &slots);
    })
    .unwrap_or_else(|error| error.raise());
}

fn named_key(program: &RustProgram<'_>, function: &str, name: &str, depth: u8) -> String {
    let functions: Vec<_> = program
        .functions
        .iter()
        .copied()
        .filter(|did| program.tcx.item_name(did.to_def_id()).as_str() == function)
        .collect();
    assert_eq!(functions.len(), 1);
    let did = functions[0];
    let body = program
        .tcx
        .mir_drops_elaborated_and_const_checked(did)
        .borrow();
    let locals: BTreeSet<Local> = body
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
    assert_eq!(locals.len(), 1);
    slot_key::local_key(
        program.tcx,
        did,
        locals.iter().next().unwrap().as_usize(),
        depth,
    )
}

fn json_row<'a>(document: &'a Value, key: &str) -> &'a Value {
    let rows: Vec<_> = document["rows"]
        .as_array()
        .expect("canonical row array")
        .iter()
        .filter(|row| row["slot"].as_str() == Some(key))
        .collect();
    assert_eq!(rows.len(), 1, "exact canonical JSON key {key}");
    rows[0]
}

#[test]
fn e5_x_export_constructor_capture_and_canonical_json_match_existing_facts() {
    inspect(|program, slots| {
        let mutability = MutFacts::from_program(program);
        let nullability = nullability::analyze(program.tcx, &program.functions, slots);
        let expected = collect(program, slots, &mutability, &nullability);
        assert!(!expected.rows.is_empty());
        let origins = compute_origins(program);
        let solver = KindSolver::new(slots);
        let (construction, captured) = export::with_bo_export(|| {
            construct_bo_into(
                program,
                slots,
                &origins,
                &mutability,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("actual production construction")
        });
        assert_eq!(
            construction.qualifier_facts, expected,
            "construction must carry the actual complete producer rows"
        );
        assert_eq!(
            captured.qualifier_facts.as_ref(),
            Some(&expected),
            "capture must retain the same facts"
        );

        let bytes = construction.qualifier_facts.canonical_json();
        let document: Value = serde_json::from_str(&bytes).expect("canonical qualifier JSON");
        assert_eq!(document["schema"], "era5a-qualifiers-v1");
        assert_eq!(document["fatness_producer"], "foster");
        assert_eq!(document["sign_producer"], "offset-sign");
        assert_eq!(
            document["mutability_semantics"],
            "supplied-outer-replay-summary"
        );
        assert_eq!(
            document["nullability_semantics"],
            "recorded-evidence-not-nonnull-proof"
        );
        let keys: Vec<_> = document["rows"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row["slot"].as_str().expect("slot string").to_owned())
            .collect();
        assert_eq!(keys.len(), expected.rows.len());
        assert!(
            keys.windows(2).all(|pair| pair[0] < pair[1]),
            "canonical rows are strictly slot-sorted"
        );
        assert_eq!(
            keys.iter().cloned().collect::<BTreeSet<_>>(),
            expected.rows.iter().map(|row| row.slot.clone()).collect()
        );

        let raw_key = named_key(program, "qualifiers", "pp", 0);
        let reference_key = named_key(program, "qualifiers", "rr", 0);
        let inner_key = named_key(program, "qualifiers", "pp", 1);
        assert_eq!(json_row(&document, &raw_key)["level"], "raw");
        assert_eq!(json_row(&document, &reference_key)["level"], "reference");
        let inner = json_row(&document, &inner_key);
        assert_eq!(inner["depth"], 1);
        assert_eq!(inner["qualifier_offset"], 1);
        assert_eq!(
            inner["sign"],
            serde_json::json!({"state": "missing", "value": "inner-sign-not-represented"})
        );
        assert_eq!(
            inner["mutability"],
            serde_json::json!({"state": "missing", "value": "inner-mutability-not-represented"})
        );
        let offset = json_row(&document, &named_key(program, "qualifiers", "p", 0));
        assert_eq!(
            offset["fatness"],
            serde_json::json!({"state": "present", "value": "array-like"})
        );
        assert_eq!(
            offset["sign"],
            serde_json::json!({"state": "present", "value": "nonnegative"})
        );

        let mut reversed = expected.clone();
        reversed.rows.reverse();
        assert_eq!(
            reversed.canonical_json(),
            bytes,
            "canonical bytes must not depend on caller row order"
        );
        assert_eq!(
            captured.qualifier_facts.as_ref().unwrap().canonical_json(),
            bytes
        );
    });
}

#[derive(Debug, PartialEq, Eq)]
struct Snapshot {
    model: FxHashMap<SlotRef, SlotKind>,
    emission_stats: BoOwnEmissionStats,
    selectors: Vec<T2AssertKey>,
    rounds: RoundStats,
    qualifiers: QualifierFacts,
}

fn solve(program: &RustProgram<'_>, slots: &CrateSlots, mutability: &MutFacts) -> Snapshot {
    let origins = compute_origins(program);
    let solver = KindSolver::new(slots);
    let construction = construct_bo_into(
        program,
        slots,
        &origins,
        mutability,
        &solver,
        CopyLendMode::Baseline,
    )
    .expect("shared production construction");
    let mut selectors = construction.selectors.keys().to_vec();
    selectors.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
    assert!(
        selectors
            .iter()
            .any(|key| key.callee == "malloc" && key.role == BoundaryRole::Source)
    );
    assert!(
        selectors
            .iter()
            .any(|key| key.callee == "free" && key.role == BoundaryRole::Sink),
        "selector neutrality must have real endpoints to compare"
    );
    let (model, rounds) = verify_bo_construction_counting_for_test(
        program,
        slots,
        &origins,
        &solver,
        &construction,
        mutability,
        TestValidationBackend::HardCheckRoundOptimize,
    );
    assert!(
        rounds.source_retirement_decline.is_empty(),
        "fixture must have no unrelated source-retirement decline"
    );
    Snapshot {
        model: model.expect("the fixture must have an accepted whole model"),
        emission_stats: construction.stats,
        selectors,
        rounds,
        qualifiers: construction.qualifier_facts,
    }
}

#[test]
fn e5_x_export_capture_is_neutral_and_forced_outer_mutability_stays_scoped() {
    inspect(|program, slots| {
        let inferred = MutFacts::from_program(program);
        let forced = MutFacts::all_mut();
        let mut forced_witnessed = false;
        for (label, mutability) in [("inferred", &inferred), ("forced", &forced)] {
            assert!(!export::capturing());
            let without_capture = solve(program, slots, mutability);
            assert!(!export::capturing());
            let (with_capture, captured) =
                export::with_bo_export(|| solve(program, slots, mutability));
            assert_eq!(
                without_capture, with_capture,
                "capture cannot change any model, emission stat, selector key, or verification counter: {label}"
            );
            assert_eq!(
                captured.qualifier_facts.as_ref(),
                Some(&with_capture.qualifiers)
            );
            assert!(!with_capture.qualifiers.rows.is_empty());
            let nullable = nullability::analyze(program.tcx, &program.functions, slots);
            assert_eq!(
                with_capture.qualifiers,
                collect(program, slots, mutability, &nullable)
            );
            if label == "forced" {
                for (&did, universe) in &slots.fn_local_slots {
                    for index in 0..universe.len() {
                        let descriptor =
                            universe.slot(super::super::slots::SlotId::from_usize(index));
                        let SlotOwner::Local(local) = descriptor.owner else {
                            panic!("local universe")
                        };
                        let key = slot_key::local_key(
                            program.tcx,
                            did,
                            local.as_usize(),
                            descriptor.depth,
                        );
                        let rows: Vec<_> = with_capture
                            .qualifiers
                            .rows
                            .iter()
                            .filter(|row| row.slot == key)
                            .collect();
                        assert_eq!(rows.len(), 1);
                        if descriptor.depth == 0 {
                            assert_eq!(
                                rows[0].mutability,
                                Availability::Present(MutabilityFact {
                                    mutable: true,
                                    defaulted: false
                                }),
                                "forced supplied outer summary at {key}"
                            );
                        } else {
                            forced_witnessed = true;
                            assert_eq!(
                                rows[0].mutability,
                                Availability::Missing(MissingFact::InnerMutabilityNotRepresented),
                                "forced outer mutability cannot become an inner fact at {key}"
                            );
                            assert_eq!(
                                rows[0].sign,
                                Availability::Missing(MissingFact::InnerSignNotRepresented)
                            );
                        }
                    }
                }
                let json: Value =
                    serde_json::from_str(&with_capture.qualifiers.canonical_json()).unwrap();
                let outer = json_row(&json, &named_key(program, "qualifiers", "rr", 0));
                assert_eq!(
                    outer["mutability"],
                    serde_json::json!({"state": "present", "value": {"mutable": true, "defaulted": false}})
                );
            }
        }
        assert!(
            forced_witnessed,
            "a real inner slot must exercise the non-broadcast control"
        );
    });
}
