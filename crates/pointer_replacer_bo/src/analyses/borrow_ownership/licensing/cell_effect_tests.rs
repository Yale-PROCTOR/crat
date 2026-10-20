//! C03 original-cell correspondence controls. Fixture programs are compiler
//! inputs only; with_facts enforces zero queries and zero model entries.

use super::{graph_tests::with_facts, snapshot::Snapshot};

const OL06: &str = r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct Cell { ptr: *mut i32 }
pub unsafe fn make() -> *mut i32 {
    let value = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *value = 5;
    value
}
pub unsafe fn put(cell: *mut Cell, value: *mut i32) { (*cell).ptr = value; }
pub unsafe fn take(cell: *mut Cell) -> *mut i32 {
    let value = (*cell).ptr;
    (*cell).ptr = 0 as *mut i32;
    value
}
pub unsafe fn release(cell: *mut Cell) {
    let value = take(cell);
    free(value as *mut core::ffi::c_void);
}
pub unsafe fn f() {
    let owner = make();
    let mut cell = Cell { ptr: 0 as *mut i32 };
    put(&mut cell, owner);
    release(&mut cell);
}
"#;

#[test]
fn c03_cell_construction_capture_has_no_queries() {
    with_facts(OL06, |facts| {
        let snapshot = Snapshot::capture(facts, 0).expect("completed construction snapshot");
        println!(
            "C03_CELL_FACTS={}",
            serde_json::to_string(&snapshot).unwrap()
        );
    });
}

#[test]
fn c03_cell_native_frames_are_held_and_never_borrowed_view_transfers() {
    use super::{
        super::ownership_occurrence::Availability::Present,
        facts::EquationId,
        transport::{CandidateGraph, Rule},
    };
    with_facts(OL06, |facts| {
        let frames: Vec<_> = facts
            .equations
            .iter()
            .filter(|row| row.operation == "guarded-original-cell-frame")
            .collect();
        assert_eq!(frames.len(), 2, "put/release native frames");
        let graph = CandidateGraph::build(facts);
        let snapshot = Snapshot::capture(facts, 0).unwrap();
        snapshot.validate().unwrap();
        for frame in frames {
            let id = EquationId {
                construction: frame.point.construction,
                ordinal: frame.ordinal,
            };
            let early = super::cell_effects::early(facts, &frame.point).unwrap();
            let complete = super::cell_effects::discover(facts);
            assert!(complete.iter().any(|row| row.call == early.call
                && row.argument == early.argument
                && row.original_consume == early.original_consume
                && row.reference_consume == early.reference_consume));
            assert!(
                !graph
                    .borrowed_views
                    .iter()
                    .any(|view| view.guard.binding == id)
            );
            let transfer = frame.transfer.as_ref().unwrap();
            let edges: Vec<_> = graph
                .edges
                .iter()
                .filter(|edge| {
                    edge.rule == Rule::Frame && edge.guard.is_some_and(|guard| guard.binding == id)
                })
                .collect();
            assert_eq!(edges.len(), 1);
            assert_eq!(edges[0].rule, Rule::Frame);
            assert!(!edges[0].guard.unwrap().required);
            assert_eq!(edges[0].from.var, transfer.source_use);
            assert_eq!(edges[0].to.var, transfer.source_def);
            let reference = facts
                .consumes
                .iter()
                .find(|row| row.point == frame.point && row.ordinal == early.reference_consume)
                .unwrap();
            let Present(window) = &reference.projected else { panic!("reference window") };
            for var in (window.use_start..window.use_end).chain(window.def_start..window.def_end) {
                assert!(
                    facts.equations.iter().any(|row| row.point == frame.point
                        && row.operation == "assume"
                        && row.value == Some(false)
                        && row.variables == [var]),
                    "native temporary component is always zero"
                );
            }
        }
        let mut missing = snapshot.clone();
        missing
            .metadata
            .equations
            .retain(|row| row.operation != "guarded-original-cell-declared");
        assert!(
            missing.validate().is_err(),
            "the new frame cannot lose its explicit dormant guard hold"
        );
    });
}

#[test]
fn c03_cell_original_correspondences_keep_reference_old_and_final_zero() {
    use super::super::{
        ownership_access::Expression,
        ownership_boundary::{Role, Variables},
        ownership_occurrence::Availability::Present,
    };
    with_facts(OL06, |facts| {
        let mut missing = Vec::new();
        let mut cell_chain = Vec::new();
        for callee in ["put", "release"] {
            let calls: Vec<_> = facts
                .boundary_substitutions
                .iter()
                .filter(|row| {
                    row.point.function.as_deref() == Some("f")
                        && row.role == Role::CallArgument
                        && row.callee.as_deref() == Some(callee)
                        && row.argument_index == Some(0)
                })
                .collect();
            assert_eq!(calls.len(), 1);
            let call = calls[0];
            let Present(registration_id) = call.call_arg_registration else {
                panic!("recorded original proxy")
            };
            let registration = facts
                .call_arg_registrations
                .iter()
                .find(|row| {
                    row.point.construction == call.point.construction
                        && row.ordinal == registration_id
                })
                .unwrap();
            let Present(actual_id) = registration.source_occurrence else {
                panic!("recorded native-reference consume")
            };
            let actual = facts
                .consumes
                .iter()
                .find(|row| {
                    row.point.construction == call.point.construction && row.ordinal == actual_id
                })
                .unwrap();
            let formation = facts.source_occurrences["f"]
                .iter()
                .find(|row| {
                    row.syntax.destination.local == actual.local
                        && matches!(&row.syntax.expression, Expression::Borrow { .. })
                })
                .expect("native reference formation is separate from raw-address registration");
            let Expression::Borrow { borrow, place } = &formation.syntax.expression else {
                unreachable!()
            };
            assert_eq!(borrow, "Mut { kind: Default }");
            let at_formation = |point: &super::super::ownership_evidence::Point| {
                point.construction == call.point.construction
                    && point.function.as_deref() == Some("f")
                    && point.block == Some(formation.site.block)
                    && point.statement == Some(formation.site.statement)
            };
            let original: Vec<_> = facts
                .consumes
                .iter()
                .filter(|row| {
                    at_formation(&row.point)
                        && row.local == place.local
                        && row.projection == place.projection
                })
                .collect();
            assert_eq!(original.len(), 1);
            let original = original[0];
            let Present(cell) = &original.projected else { panic!("original cell window") };
            assert_eq!(cell.use_end - cell.use_start, 1);
            assert_eq!(cell.def_end - cell.def_start, 1);
            assert_ne!(
                original.point, registration.point,
                "formation must not be relabeled as the later registration"
            );
            cell_chain.push((
                original.local,
                original.ssa_use,
                original.ssa_def,
                cell.use_start,
                cell.def_start,
            ));
            let reference = facts
                .consumes
                .iter()
                .find(|row| {
                    at_formation(&row.point)
                        && row.local == formation.syntax.destination.local
                        && row.projection.is_empty()
                })
                .unwrap();
            let Present(reference_window) = &reference.projected else {
                panic!("reference temporary window")
            };
            for var in reference_window.use_start..reference_window.use_end {
                assert!(
                    facts
                        .equations
                        .iter()
                        .any(|row| row.point == reference.point
                            && row.operation == "assume"
                            && row.value == Some(false)
                            && row.variables == [var]),
                    "{callee}: reference destination-old-zero remains unconditional"
                );
            }
            let terminals: Vec<_> = facts
                .terminals
                .iter()
                .filter(|row| {
                    row.point.construction == call.point.construction
                        && row.point.function.as_deref() == Some("f")
                        && row.local == reference.local
                        && row.role == "local-final-zero"
                })
                .collect();
            assert_eq!(terminals.len(), 1);
            let terminal = terminals[0];
            let Present(values) = &terminal.values else { panic!("reference finalization values") };
            assert_eq!(values.len(), 2, "outer reference and field-view components");
            for value in values {
                assert!(
                    facts.equations.iter().any(|row| row.point == terminal.point
                        && row.operation == "assume"
                        && row.assumption_class.as_deref() == Some("temporary-finalization")
                        && row.value == Some(false)
                        && row.variables == [value.var]),
                    "{callee}: reference temporary must not retain an owning output token"
                );
            }
            let [pair] = call.matched.as_slice() else {
                panic!("one exact payload matcher component")
            };
            let Variables::UseDef {
                use_var: formal_use,
                def_var: formal_def,
            } = pair.formal
            else {
                panic!("two-slot formal payload")
            };
            // Proposed recorded operation, using the existing equation DTO:
            // guard => formal input/output equals this formation-time cell's
            // use/def. This is an equation contract, not a new source API.
            let expected = [formal_use, formal_def, cell.use_start, cell.def_start];
            if !facts.equations.iter().any(|row| {
                row.point == call.point
                    && row.operation == "guarded-original-cell-argument"
                    && row.guard.is_some()
                    && row.variables == expected
            }) {
                missing.push(format!(
                    "{callee} {:?} requires original consume {} at {:?}, variables {expected:?}",
                    call.point, original.ordinal, original.point
                ));
            }
        }
        assert_eq!(cell_chain.len(), 2);
        assert_eq!(
            cell_chain[0].0, cell_chain[1].0,
            "same original struct cell"
        );
        assert_eq!(
            cell_chain[0].2, cell_chain[1].1,
            "successive original-cell SSA versions"
        );
        assert_eq!(
            cell_chain[0].4, cell_chain[1].3,
            "put output becomes release input without a temporary owner"
        );
        assert!(
            missing.is_empty(),
            "missing explicit formation-time ORIGINAL cell correspondences: {missing:#?}"
        );
    });
}

#[test]
fn c03_field_support_classifies_transported_null_without_owning_support() {
    with_facts(OL06, |facts| {
        let frozen = facts.licensing.as_ref().unwrap();
        let field = frozen
            .field_support
            .iter()
            .find(|field| field.field_key == "Cell::field0@d0")
            .unwrap();
        let aggregate = facts
            .field_support_inputs
            .stores
            .iter()
            .find(|store| store.site.function == "f" && store.aggregate)
            .unwrap();
        assert!(
            field.null_stores.contains(&aggregate.site),
            "a complete Null origin transported through the initializer is still None, not a missing owned input: {field:#?}"
        );
        assert!(
            field.stores.is_empty(),
            "the null initializer is not positive owning support"
        );
        assert!(
            !field.supported(),
            "the put input contract is independently still incomplete"
        );
    });
}

#[test]
fn c03_field_support_keeps_a_mixed_null_stack_store_held() {
    with_facts(
        r#"
pub struct Cell { ptr: *mut i32 }
pub unsafe fn f(which: bool) -> i32 {
    let mut stack = 9;
    let ptr = if which { 0 as *mut i32 } else { &mut stack };
    let cell = Cell { ptr };
    if cell.ptr.is_null() { 0 } else { *cell.ptr }
}
"#,
        |facts| {
            let field = facts
                .licensing
                .as_ref()
                .unwrap()
                .field_support
                .iter()
                .find(|field| field.field_key == "Cell::field0@d0")
                .unwrap();
            assert!(
                field.null_stores.is_empty(),
                "Null among mixed origins cannot discharge the non-null store"
            );
            assert!(!field.supported());
        },
    );
}

#[test]
fn c03_original_cell_candidates_bind_both_sites_and_successive_ssa_cells() {
    with_facts(OL06, |facts| {
        let candidates = super::cell_effects::discover(facts);
        assert_eq!(
            candidates.len(),
            2,
            "two actual reference/cell call correspondences, no grant: {candidates:#?}"
        );
        let put = candidates
            .iter()
            .find(|row| row.call.callee == "put")
            .unwrap();
        let release = candidates
            .iter()
            .find(|row| row.call.callee == "release")
            .unwrap();
        assert_eq!(put.cell, release.cell);
        assert_ne!(put.formation, put.address);
        assert_ne!(release.formation, release.address);
        assert_ne!(put.original_consume, release.original_consume);
        let consume = |id| {
            facts
                .consumes
                .iter()
                .find(|row| row.ordinal == id && row.point.construction == put.call.construction)
                .unwrap()
        };
        assert_eq!(
            consume(put.original_consume).ssa_def,
            consume(release.original_consume).ssa_use
        );
        for candidate in &candidates {
            assert_eq!(candidate.field_key, "Cell::field0@d0");
            assert_eq!(candidate.argument, 0);
            let original = consume(candidate.original_consume);
            let reference = consume(candidate.reference_consume);
            let actual = consume(candidate.reference_use);
            assert_eq!(original.point, candidate.formation);
            assert_eq!(reference.point, candidate.formation);
            assert_eq!(actual.point, candidate.address);
            assert_eq!(reference.local, actual.local);
            assert_eq!(reference.ssa_def, actual.ssa_use);
            assert_ne!(original.local, actual.local);
        }
        for fault in ["cell", "ssa", "proxy", "shared", "missing"] {
            let mut broken = facts.clone();
            match fault {
                "cell" => {
                    broken
                        .consumes
                        .iter_mut()
                        .find(|row| row.ordinal == put.original_consume)
                        .unwrap()
                        .local += 100
                }
                "ssa" => {
                    broken
                        .consumes
                        .iter_mut()
                        .find(|row| row.ordinal == put.reference_use)
                        .unwrap()
                        .ssa_use = None
                }
                "proxy" => {
                    broken
                        .call_arg_registrations
                        .iter_mut()
                        .find(|row| row.ordinal == put.registration)
                        .unwrap()
                        .proxy_local += 100
                }
                "shared" => {
                    let row = broken
                        .source_occurrences
                        .get_mut("f")
                        .unwrap()
                        .iter_mut()
                        .find(|row| {
                            row.site.block == put.formation.block.unwrap()
                                && row.site.statement == put.formation.statement.unwrap()
                        })
                        .unwrap();
                    let super::super::ownership_access::Expression::Borrow { borrow, .. } =
                        &mut row.syntax.expression
                    else {
                        panic!("borrow")
                    };
                    *borrow = "Shared".into();
                }
                _ => broken
                    .consumes
                    .retain(|row| row.ordinal != put.original_consume),
            }
            let rows = super::cell_effects::discover(&broken);
            assert!(
                rows.iter().all(|row| row.call != put.call),
                "bad formation/current correspondence survived {fault}"
            );
            assert!(
                rows.iter().any(|row| row.call == release.call),
                "independent later call lost by {fault}"
            );
        }
    });
}

#[test]
fn c03_call_validation_rejects_extra_wrong_tuple_beside_valid_arms() {
    use super::{facts::EquationId, matched::guard_aliases};
    with_facts(OL06, |facts| {
        let aliases = guard_aliases(&facts.guards);
        super::cell_effects::validate_calls(facts, &aliases).unwrap();
        for operation in [
            "guarded-original-cell-argument",
            "guarded-original-cell-legacy",
            "guarded-original-cell-outer",
        ] {
            let row = facts
                .equations
                .iter()
                .find(|row| row.operation == operation)
                .unwrap();
            let canonical = aliases[&EquationId {
                construction: row.point.construction,
                ordinal: row.ordinal,
            }];
            let mut extra = row.clone();
            extra.ordinal = facts.equations.iter().map(|row| row.ordinal).max().unwrap() + 1;
            extra.variables.swap(0, 1);
            let mut broken = facts.clone();
            let mut broken_aliases = aliases.clone();
            broken_aliases.insert(
                EquationId {
                    construction: extra.point.construction,
                    ordinal: extra.ordinal,
                },
                canonical,
            );
            broken.equations.push(extra);
            assert!(
                super::cell_effects::validate_calls(&broken, &broken_aliases).is_err(),
                "unrelated additional {operation} tuple accepted under the valid arm's guard"
            );
        }
    });
}

#[test]
fn c03_matched_call_arms_do_not_cross_original_and_legacy_windows() {
    use super::{
        super::{ownership_boundary::LicensingRole, ownership_occurrence::Availability::Present},
        matched::guard_aliases,
        transport::{CandidateGraph, Evidence, Node},
    };
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
pub struct Cell { ptr: *mut i32 }
pub unsafe fn keep(cell: *mut Cell) { let p = (*cell).ptr; (*cell).ptr = p; }
pub unsafe fn f() {
    let p = malloc(4) as *mut i32;
    let mut cell = Cell {ptr:p};
    keep(&mut cell);
    free(cell.ptr as *mut core::ffi::c_void);
}
"#,
        |facts| {
            let aliases = guard_aliases(&facts.guards);
            let boundary = facts
                .boundary_substitutions
                .iter()
                .find(|row| row.licensing_role == LicensingRole::OriginalCell)
                .expect("actual conditional call");
            let arm = super::cell_effects::call_arm(facts, boundary, &aliases).unwrap();
            let node = |var| Node {
                construction: arm.candidate.call.construction,
                var,
            };
            let graph = CandidateGraph::build(facts);
            let edges: Vec<_> = graph.edges.iter().filter(|edge| matches!(edge.evidence, Evidence::Boundary {construction, ordinal, ..} if construction == boundary.point.construction && ordinal == boundary.ordinal)).collect();
            assert_eq!(edges.len(), 4);
            for (actual, required) in [(arm.original, true), (arm.legacy, false)] {
                for (from, to) in [(actual.0, arm.formal.0), (arm.formal.1, actual.1)] {
                    assert!(edges.iter().any(|edge| edge.from == node(from)
                        && edge.to == node(to)
                        && edge.guard.is_some_and(
                            |guard| guard.binding == arm.guard && guard.required == required
                        )));
                }
            }
            let matched = &facts.licensing.as_ref().unwrap().matched;
            assert!(matched.reaches(node(arm.original.0), node(arm.original.1)));
            assert!(matched.reaches(node(arm.legacy.0), node(arm.legacy.1)));
            assert!(
                !matched.reaches(node(arm.original.0), node(arm.legacy.1)),
                "true input / false output composed"
            );
            assert!(
                !matched.reaches(node(arm.legacy.0), node(arm.original.1)),
                "false input / true output composed"
            );
            let original = facts
                .consumes
                .iter()
                .find(|row| row.ordinal == arm.candidate.original_consume)
                .unwrap();
            let Present(window) = &original.projected else { panic!("cell window") };
            assert_eq!((window.use_start, window.def_start), arm.original);
            Snapshot::capture(facts, 0).unwrap().validate().unwrap();
        },
    );
}

#[test]
fn c03_native_frame_requires_all_reference_zero_evidence() {
    use super::{super::ownership_occurrence::Availability::Present, matched::guard_aliases};
    with_facts(OL06, |facts| {
        let aliases = guard_aliases(&facts.guards);
        super::cell_effects::validate_frames(facts, &aliases).unwrap();
        let frame = facts
            .equations
            .iter()
            .find(|row| row.operation == "guarded-original-cell-frame")
            .unwrap();
        let early = super::cell_effects::early(facts, &frame.point).unwrap();
        let reference = facts
            .consumes
            .iter()
            .find(|row| row.ordinal == early.reference_consume && row.point == frame.point)
            .unwrap();
        let Present(window) = &reference.projected else { panic!("reference window") };
        for var in (window.use_start..window.use_end).chain(window.def_start..window.def_end) {
            let mut broken = facts.clone();
            let before = broken.equations.len();
            broken.equations.retain(|row| {
                !(row.point == frame.point
                    && row.operation == "assume"
                    && row.value == Some(false)
                    && row.variables == [var])
            });
            assert!(broken.equations.len() < before);
            assert!(
                super::cell_effects::validate_frames(&broken, &aliases).is_err(),
                "missing reference zero for {var} accepted"
            );
        }
    });
}

#[test]
fn c03_call_arms_reject_another_calls_guard_and_missing_role() {
    use super::{
        super::ownership_boundary::LicensingRole, facts::EquationId, matched::guard_aliases,
    };
    with_facts(OL06, |facts| {
        let aliases = guard_aliases(&facts.guards);
        let calls: Vec<_> = facts
            .boundary_substitutions
            .iter()
            .filter(|row| row.licensing_role == LicensingRole::OriginalCell)
            .collect();
        assert_eq!(calls.len(), 2);
        let other = super::cell_effects::call_arm(facts, calls[1], &aliases)
            .unwrap()
            .guard;
        for operation in [
            "guarded-original-cell-argument",
            "guarded-original-cell-legacy",
            "guarded-original-cell-outer",
        ] {
            let row = facts
                .equations
                .iter()
                .find(|row| row.point == calls[0].point && row.operation == operation)
                .unwrap();
            let mut broken_aliases = aliases.clone();
            broken_aliases.insert(
                EquationId {
                    construction: row.point.construction,
                    ordinal: row.ordinal,
                },
                other,
            );
            assert!(super::cell_effects::validate_calls(facts, &broken_aliases).is_err());
        }
        let mut broken = facts.clone();
        broken
            .boundary_substitutions
            .iter_mut()
            .find(|row| row.ordinal == calls[0].ordinal)
            .unwrap()
            .licensing_role = LicensingRole::Legacy;
        assert!(super::cell_effects::validate_calls(&broken, &aliases).is_err());
    });
}
