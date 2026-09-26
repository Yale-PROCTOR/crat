//! Transport assertions over actual compiler construction facts. No fixture
//! program or ownership solver is executed by this construction helper.

use rustc_hir::{ItemKind, OwnerNode};

use super::{
    super::{
        construction::{CopyLendMode, construct_bo_into, construct_bo_into_a16_refined},
        crate_slots::CrateSlots,
        execution_guard, export,
        mutability_facts::MutFacts,
        origins::compute_origins,
        ownership_boundary::{Role, Variables},
        solver::KindSolver,
    },
    facts::Facts,
    transport::{CandidateGraph, Node, Rule},
};
use crate::utils::rustc::RustProgram;

const CHAIN: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn make() -> *mut i32 { let p = malloc(4); p }
pub unsafe fn wrapper() -> *mut i32 { make() }
pub unsafe fn consume(p: *mut i32) { free(p); }
pub unsafe fn run() { let p = wrapper(); let q = p; consume(q); }
pub unsafe fn unrelated(p: *mut i32) -> *mut i32 { p }
"#;

pub(crate) fn with_facts(code: &str, check: impl FnOnce(&Facts) + Send) {
    with_facts_mode(code, CopyLendMode::Baseline, check)
}

fn with_facts_mode(code: &str, mode: CopyLendMode, check: impl FnOnce(&Facts) + Send) {
    with_solver_facts_mode(code, mode, |facts, _, _| check(facts));
}

pub(super) fn with_solver_facts(
    code: &str,
    check: impl FnOnce(&Facts, &KindSolver, &CrateSlots) + Send,
) {
    with_solver_facts_mode(code, CopyLendMode::Baseline, check);
}

fn with_solver_facts_mode(
    code: &str,
    mode: CopyLendMode,
    check: impl FnOnce(&Facts, &KindSolver, &CrateSlots) + Send,
) {
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
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
        let mutability = MutFacts::from_program(&program);
        let model_entries = execution_guard::model_entries();
        assert!(!export::capturing());
        let solver = KindSolver::new(&slots);
        if mode == CopyLendMode::Baseline {
            construct_bo_into_a16_refined(&program, &slots, &origins, &mutability, &solver)
                .unwrap();
        } else {
            construct_bo_into(&program, &slots, &origins, &mutability, &solver, mode).unwrap();
        }
        let facts = solver
            .ownership_facts()
            .expect("actual construction facts without export");
        check(&facts, &solver, &slots);
        assert_eq!(
            [
                solver.check_sat_count(),
                solver.hard_check_count(),
                solver.optimize_materialization_count(),
                solver.lazy_plain_hard_check_count(),
                solver.lazy_tracked_recheck_count(),
                solver.lazy_plain_materialization_count(),
            ],
            [0; 6]
        );
        assert_eq!(execution_guard::model_entries(), model_entries);
        assert!(!export::capturing());
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn t08_checked_borrow_retains_owner_without_transporting_ownership_to_view() {
    with_facts_mode(
        r#"
        unsafe extern "C" { fn malloc(n:usize)->*mut i32; fn free(p:*mut i32); }
        pub unsafe fn run()->i32 { let p=malloc(4); *p=3; let q=p; let value=*q; free(p); value }
    "#,
        CopyLendMode::LendArm,
        |facts| {
            let equation = facts
                .equations
                .iter()
                .find(|e| e.operation == "guarded-copy")
                .expect("actual eligible copy/lend guard");
            let transfer = equation.transfer.as_ref().unwrap();
            let graph = CandidateGraph::build(facts);
            let borrow = graph
                .borrowed_views
                .iter()
                .find(|b| b.guard.binding.ordinal == equation.ordinal)
                .expect("guarded view/owner identity recorded separately");
            assert_eq!(
                borrow.owner_before,
                node(equation.point.construction, transfer.source_use)
            );
            assert_eq!(
                borrow.owner_after,
                node(equation.point.construction, transfer.source_def)
            );
            assert_eq!(
                borrow.view,
                node(equation.point.construction, transfer.destination_def)
            );
            assert!(borrow.guard.required);
            let reached = graph.forward_selected(|_| Some(true));
            assert!(
                reached.contains(&borrow.owner_after),
                "checked borrow retains the owner's responsibility"
            );
            assert!(
                !reached.contains(&borrow.view),
                "checked borrow never transports a source licence into its view"
            );
            assert!(
                graph.forward_selected(|_| None).is_empty(),
                "missing predicate valuation is not true"
            );
        },
    );
}

fn node(construction: u32, var: u32) -> Node {
    Node { construction, var }
}

#[test]
fn t02_t05_factory_chain_reaches_its_exact_source_and_sink_in_both_directions() {
    with_facts(CHAIN, |facts| {
        let graph = CandidateGraph::build(facts);
        let source = facts
            .equations
            .iter()
            .find(|row| row.operation == "source")
            .expect("malloc source");
        let sink = facts
            .equations
            .iter()
            .find(|row| row.operation == "sink")
            .expect("free sink");
        let source_node = node(source.point.construction, source.variables[0]);
        let sink_node = node(sink.point.construction, sink.variables[0]);
        assert_eq!(
            graph.sources.len(),
            1,
            "the actual allocator endpoint must seed transport"
        );
        assert_eq!(
            graph.sinks.len(),
            1,
            "the actual deallocator endpoint must seed demand"
        );
        assert_eq!(graph.sources[0].node, source_node);
        assert_eq!(
            graph.sources[0].endpoint,
            *source.endpoint.as_ref().unwrap()
        );
        assert_eq!(graph.sources[0].equation.ordinal, source.ordinal);
        assert_eq!(graph.sinks[0].node, sink_node);
        assert_eq!(graph.sinks[0].endpoint, *sink.endpoint.as_ref().unwrap());
        assert_eq!(graph.sinks[0].equation.ordinal, sink.ordinal);
        assert!(
            graph.forward().contains(&sink_node),
            "source transport crosses wrapper return, receiver, copy and parameter"
        );
        assert!(
            graph.backward().contains(&source_node),
            "sink demand follows the same exact chain backward"
        );
    });
}

#[test]
fn t03_t05_substitution_edges_have_the_recorded_return_and_parameter_directions() {
    with_facts(CHAIN, |facts| {
        let graph = CandidateGraph::build(facts);
        let mut checked = [false; 5];
        for row in &facts.boundary_substitutions {
            for pair in &row.matched {
                let construction = row.point.construction;
                let mut require = |from, to, rule, index| {
                    assert!(
                        graph.has_edge(node(construction, from), node(construction, to), rule),
                        "missing directed {:?} substitution at {:?}",
                        row.role,
                        row.point
                    );
                    checked[index] = true;
                };
                match (row.role, &pair.actual, &pair.formal) {
                    (
                        Role::ReturnReceiver,
                        Variables::UseDef { def_var, .. },
                        Variables::Single { var },
                    ) => {
                        require(*var, *def_var, Rule::Return, 0);
                    }
                    (
                        Role::ExitReturn,
                        Variables::Single { var: actual },
                        Variables::Single { var: formal },
                    ) => {
                        require(*actual, *formal, Rule::Return, 1);
                    }
                    (
                        Role::Entry,
                        Variables::Single { var: actual },
                        Variables::Single { var: formal },
                    ) => {
                        require(*formal, *actual, Rule::Param, 2);
                    }
                    (
                        Role::CallArgument,
                        Variables::UseDef {
                            use_var: actual_use,
                            def_var: actual_def,
                        },
                        Variables::UseDef {
                            use_var: formal_use,
                            def_var: formal_def,
                        },
                    ) => {
                        require(*actual_use, *formal_use, Rule::Param, 3);
                        require(*formal_def, *actual_def, Rule::Param, 3);
                    }
                    (
                        Role::ExitOutput,
                        Variables::Single { var: actual },
                        Variables::Single { var: formal },
                    ) => {
                        require(*actual, *formal, Rule::Param, 4);
                    }
                    _ => {}
                }
            }
        }
        assert_eq!(
            checked, [true; 5],
            "every required substitution direction was exercised"
        );
    });
}

#[test]
fn t04_copy_transport_does_not_turn_linear_components_or_names_into_edges() {
    with_facts(CHAIN, |facts| {
        let graph = CandidateGraph::build(facts);
        let mut copies = 0;
        for equation in &facts.equations {
            let Some(transfer) = &equation.transfer else { continue };
            if equation.operation != "linear" {
                continue;
            }
            let construction = equation.point.construction;
            let source = node(construction, transfer.source_use);
            let retained = node(construction, transfer.source_def);
            let destination = node(construction, transfer.destination_def);
            assert!(
                graph.has_edge(source, destination, Rule::Copy),
                "exact copy matcher transfer must be transported"
            );
            assert!(
                graph.has_edge(source, retained, Rule::Copy),
                "copy identity may remain with the source; responsibility remains a split obligation"
            );
            assert!(
                !graph
                    .edges
                    .iter()
                    .any(|edge| edge.from == retained && edge.to == destination),
                "the two successors of a linear split are not a transfer from one to the other"
            );
            copies += 1;
        }
        assert!(copies > 0, "fixture exercises a real linear copy");
        let reachable = graph.forward();
        let unrelated = facts
            .boundary_substitutions
            .iter()
            .find(|row| {
                row.role == Role::Entry && row.point.function.as_deref() == Some("unrelated")
            })
            .expect("independent same-named parameter");
        for pair in &unrelated.matched {
            let Variables::Single { var } = pair.actual else { panic!("entry scalar Var") };
            assert!(
                !reachable.contains(&node(unrelated.point.construction, var)),
                "a reused source variable name is not a transport edge"
            );
        }
    });
}

#[test]
fn t02_local_malloc_spelling_is_not_a_source_endpoint() {
    with_facts(
        r#"
pub unsafe fn malloc(p: *mut i32) -> *mut i32 { p }
pub unsafe fn caller(p: *mut i32) -> *mut i32 { malloc(p) }
"#,
        |facts| {
            let graph = CandidateGraph::build(facts);
            assert!(graph.sources.is_empty());
            assert!(graph.forward().is_empty());
        },
    );
}

#[test]
fn t06_other_field_store_preserves_the_exact_first_field_frame() {
    use super::super::ownership_occurrence::{Availability, PathStep};
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub struct Pair { first: *mut i32, second: *mut i32 }
pub unsafe fn run() {
    let mut pair = Pair { first: 0 as *mut i32, second: 0 as *mut i32 };
    let owner = malloc(4);
    pair.first = owner;
    pair.second = 0 as *mut i32;
    let value = pair.first;
    free(value);
}
"#,
        |facts| {
            let graph = CandidateGraph::build(facts);
            let other_store = facts
                .consumes
                .iter()
                .find(|row| {
                    row.point.function.as_deref() == Some("run")
                        && row.projection == vec![export::ProjKey::Field(1)]
                        && facts.source_occurrences["run"].iter().any(|source| {
                            Some(source.site.block) == row.point.block
                                && Some(source.site.statement) == row.point.statement
                                && source.syntax.destination.local == row.local
                                && source.syntax.destination.projection == row.projection
                        })
                })
                .expect("ordinary second-field store has a consume");
            let Availability::Present(base) = &other_store.base else {
                panic!("represented pair window")
            };
            let Availability::Present(paths) = &other_store.pointer_paths else {
                panic!("recorded field paths")
            };
            let first_offset = paths.iter().position(|path| {
            matches!(path.as_slice(), [PathStep::Field { index: 0, name, .. }] if name == "first")
        }).expect("first field is a separate component of this pair") as u32;
            let before = base.use_start + first_offset;
            let after = base.def_start + first_offset;
            assert!(
                facts.equations.iter().any(|equation| {
                    equation.point == other_store.point
                        && equation.operation == "equal"
                        && equation.variables == [before, after]
                        && equation.transfer.is_none()
                }),
                "the existing projection frame equality must actually be present"
            );
            assert!(
                graph.edges.iter().any(|edge| {
                    edge.from == node(other_store.point.construction, before)
                        && edge.to == node(other_store.point.construction, after)
                }),
                "writing second must transport the untouched first field to its next version"
            );
            assert_eq!(graph.sources.len(), 1);
            assert_eq!(graph.sinks.len(), 1);
            assert!(
                graph.forward().contains(&graph.sinks[0].node),
                "ordinary store/frame/load chain reaches free"
            );
            assert!(graph.backward().contains(&graph.sources[0].node));
        },
    );
}

#[test]
fn t06_same_field_declaration_in_distinct_instances_does_not_cross_connect() {
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub struct Cell { ptr: *mut i32 }
pub unsafe fn allocate_left() -> *mut i32 { malloc(4) }
pub unsafe fn allocate_right() -> *mut i32 { malloc(4) }
pub unsafe fn release_left(p: *mut i32) { free(p); }
pub unsafe fn release_right(p: *mut i32) { free(p); }
pub unsafe fn run() {
    let mut left = Cell { ptr: 0 as *mut i32 };
    let mut right = Cell { ptr: 0 as *mut i32 };
    let left_owner = allocate_left();
    let right_owner = allocate_right();
    left.ptr = left_owner;
    right.ptr = right_owner;
    let left_value = left.ptr;
    let right_value = right.ptr;
    release_left(left_value);
    release_right(right_value);
}
"#,
        |facts| {
            let graph = CandidateGraph::build(facts);
            assert_eq!(graph.sources.len(), 2);
            assert_eq!(graph.sinks.len(), 2);
            for (allocator, own_release, other_release) in [
                ("allocate_left", "release_left", "release_right"),
                ("allocate_right", "release_right", "release_left"),
            ] {
                // Restrict only the roots of the actual candidate graph. The
                // construction facts and all graph edges remain unchanged.
                let mut one_source = graph.clone();
                one_source
                    .sources
                    .retain(|source| source.endpoint.function == allocator);
                assert_eq!(one_source.sources.len(), 1);
                let reachable = one_source.forward();
                let own_sink = graph
                    .sinks
                    .iter()
                    .find(|sink| sink.endpoint.function == own_release)
                    .unwrap();
                let other_sink = graph
                    .sinks
                    .iter()
                    .find(|sink| sink.endpoint.function == other_release)
                    .unwrap();
                assert!(
                    reachable.contains(&own_sink.node),
                    "ordinary cell transfer must remain connected"
                );
                assert!(
                    !reachable.contains(&other_sink.node),
                    "a shared Cell.ptr declaration does not identify the other instance"
                );
            }
        },
    );
}

#[test]
fn t06_field_load_after_branch_joins_exact_incoming_field_versions() {
    use super::super::ownership_occurrence::Availability;
    with_facts(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub struct Pair { first: *mut i32, second: *mut i32 }
pub unsafe fn run(change_other: bool) {
    let mut pair = Pair { first: 0 as *mut i32, second: 0 as *mut i32 };
    let owner = malloc(4);
    pair.first = owner;
    if change_other { pair.second = 0 as *mut i32; }
    let value = pair.first;
    free(value);
}
"#,
        |facts| {
            let graph = CandidateGraph::build(facts);
            let (load, transfer) = facts
                .equations
                .iter()
                .find_map(|equation| {
                    let transfer = equation.transfer.as_ref()?;
                    let Availability::Present(source) = &transfer.source else { return None };
                    (equation.operation == "linear"
                        && source.projection == vec![export::ProjKey::Field(0)])
                    .then_some((equation, transfer))
                })
                .expect("ordinary first-field load after the branch");
            let incoming: Vec<_> = facts
                .equations
                .iter()
                .filter(|equation| {
                    equation.point.construction == load.point.construction
                        && equation.point.function == load.point.function
                        && equation.point.phase == "phi"
                        && equation.operation == "equal"
                        && equation.variables.first() == Some(&transfer.source_use)
                })
                .collect();
            assert!(
                !incoming.is_empty(),
                "loaded field uses an actual phi definition"
            );
            for equation in incoming {
                assert_eq!(equation.variables.len(), 2);
                assert!(
                    graph.edges.iter().any(|edge| {
                        edge.from == node(equation.point.construction, equation.variables[1])
                            && edge.to == node(equation.point.construction, equation.variables[0])
                    }),
                    "phi input must transport to the joined field version, not equate arbitrary components"
                );
            }
            assert_eq!(graph.sources.len(), 1);
            assert_eq!(graph.sinks.len(), 1);
            assert!(graph.forward().contains(&graph.sinks[0].node));
            assert!(graph.backward().contains(&graph.sources[0].node));
        },
    );
}
