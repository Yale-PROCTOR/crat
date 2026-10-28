//! Relay main/378 (R1324-1) -- witnesses for 261's four identical-result fixes to the licensing
//! freeze: (a) the call graph built once per construction and a recursive SCC certified once,
//! (b) the reader plan built once for `traversal_returns`, (c) an exit reads only its own
//! function's terminals in `grants`, (d) `validate_returns` computed once per (construction,
//! function). Each counts the repeated work inside ONE `FrozenTransport::build`, and checks the
//! result against the per-function form.

use rustc_hir::{ItemKind, OwnerNode};

use super::{
    super::{
        construction::{CopyLendMode, construct_bo_into},
        crate_slots::CrateSlots,
        mutability_facts::MutFacts,
        origins::compute_origins,
        ownership_occurrence::Availability,
        solver::KindSolver,
    },
    coverage,
    facts::Facts,
    freeze_counts, recursive,
    snapshot::FrozenTransport,
    traversal_return,
};
use crate::utils::rustc::RustProgram;

/// Two mutually recursive functions (one SCC), a non-member, and a return in every one.
const FIXTURE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn ping(n: usize) -> *mut i32 {
    if n == 0 { return malloc(4); }
    pong(n - 1)
}
pub unsafe fn pong(n: usize) -> *mut i32 {
    if n == 0 { return 0 as *mut i32; }
    ping(n - 1)
}
pub unsafe fn leaf(n: usize) -> *mut i32 {
    if n == 0 { return 0 as *mut i32; }
    malloc(4)
}
"#;

/// The fixture's frozen facts, then ONE more `FrozenTransport::build` with the counters reset.
fn with_freeze(check: impl FnOnce(&Facts, &FrozenTransport) + Send) {
    ::utils::compilation::run_compiler_on_str(FIXTURE, |tcx| {
        let functions = tcx
            .hir_crate(())
            .owners
            .iter()
            .filter_map(|owner| {
                let owner = owner.as_owner()?;
                let OwnerNode::Item(item) = owner.node() else { return None };
                matches!(item.kind, ItemKind::Fn { .. }).then_some(item.owner_id.def_id)
            })
            .collect();
        let program = RustProgram {
            tcx,
            functions,
            structs: Vec::new(),
        };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mutability = MutFacts::from_program(&program);
        let solver = KindSolver::new(&slots);
        construct_bo_into(
            &program,
            &slots,
            &origins,
            &mutability,
            &solver,
            CopyLendMode::Baseline,
        )
        .unwrap();
        let facts = solver.ownership_facts().expect("the construction's facts");
        assert!(
            facts.source_occurrences.len() >= 3,
            "{:?}",
            facts.source_occurrences.keys()
        );
        freeze_counts::reset();
        let transport = FrozenTransport::build(&facts).expect("no budget");
        check(&facts, &transport);
    })
    .unwrap();
}

/// (a): one call graph per construction; the SCC's two members carry one certificate; the
/// non-member is not certified by it; every row equals the per-function certificate.
#[test]
fn r378_a_the_call_graph_is_built_once_and_an_scc_certified_once() {
    with_freeze(|facts, transport| {
        assert_eq!(
            freeze_counts::call_graph_builds(),
            facts.constructions as usize,
            "the call graph is rebuilt per function"
        );
        let row = |name: &str| {
            transport
                .recursive
                .iter()
                .find(|(c, f, _)| *c == 0 && f.ends_with(name))
                .map(|(_, _, certificate)| certificate.clone())
                .unwrap()
        };
        assert!(
            matches!(row("ping"), Availability::Present(_)),
            "{:?}",
            row("ping")
        );
        assert_eq!(row("ping"), row("pong"));
        assert!(matches!(row("leaf"), Availability::Missing(_)));
        for (construction, function, certificate) in &transport.recursive {
            assert_eq!(
                certificate,
                &recursive::certify_with_transport(
                    facts,
                    *construction,
                    function,
                    &transport.matched
                ),
                "{function}"
            );
        }
    });
}

/// (b): the reader plan built at most once for `traversal_returns`; its proofs equal the
/// per-function classification.
#[test]
fn r378_b_the_reader_plan_is_built_once_in_traversal_returns() {
    with_freeze(|facts, transport| {
        assert!(
            freeze_counts::reader_plan_builds() <= 1,
            "the reader plan is rebuilt per function: {}",
            freeze_counts::reader_plan_builds()
        );
        let per_function: Vec<_> = facts
            .source_occurrences
            .keys()
            .filter_map(|function| traversal_return::classify(facts, function))
            .collect();
        assert_eq!(transport.traversal_returns, per_function);
    });
}

/// (c): an exit reads only its own function's terminals (no whole-terminal scan per exit).
#[test]
fn r378_c_an_exit_reads_only_its_own_functions_terminals() {
    with_freeze(|_, _| {
        assert_eq!(
            freeze_counts::grant_terminal_scans(),
            0,
            "grants scans every terminal for every exit"
        );
    });
}

/// (d): `validate_returns` computed at most once per (construction, function) in one freeze, its
/// result the scan's.
#[test]
fn r378_d_validate_returns_is_computed_once_per_function() {
    with_freeze(|facts, _| {
        let computed = freeze_counts::validate_returns_computations();
        assert!(
            computed.values().all(|&count| count <= 1),
            "validate_returns recomputed: {computed:?}"
        );
        // The indexed form (the freeze's) against the scan, function by function.
        let _index = coverage::index_returns(facts);
        for function in facts.source_occurrences.keys() {
            assert_eq!(
                coverage::validate_returns(facts, 0, function),
                coverage::validate_returns_scan(facts, 0, function),
                "{function}"
            );
        }
    });
}
