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

/// Two mutually recursive functions (one SCC) with a callee (`leaf`) and a caller (`top`) outside
/// it, a self-recursive function (`selfie`), and returns in every one.
const FIXTURE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn ping(n: usize) -> *mut i32 {
    if n == 0 { return malloc(4); }
    pong(n - 1)
}
pub unsafe fn pong(n: usize) -> *mut i32 {
    if n == 0 { return 0 as *mut i32; }
    if n == 1 { return leaf(n); }
    ping(n - 1)
}
pub unsafe fn leaf(n: usize) -> *mut i32 {
    if n == 0 { return 0 as *mut i32; }
    malloc(4)
}
pub unsafe fn top(n: usize) -> *mut i32 {
    ping(n)
}
pub unsafe fn selfie(n: usize) -> *mut i32 {
    if n == 0 { return malloc(4); }
    selfie(n - 1)
}
"#;

/// Relay main/382 (b): one pointer passed for two formals that reach one free site, so the
/// caller's source reaches two terminals of one instance at one node in the same round.
const REPEATS_FIXTURE: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn sink(a: *mut i32, b: *mut i32, c: bool) {
    let p = if c { a } else { b };
    free(p);
}
pub unsafe fn twice(c: bool) {
    let q = malloc(4);
    sink(q, q, c);
}
"#;

/// The fixture's frozen facts, then ONE more `FrozenTransport::build` with the counters reset.
fn with_freeze(check: impl FnOnce(&Facts, &FrozenTransport) + Send) {
    with_freeze_of(FIXTURE, |facts, transport| {
        assert!(
            facts.source_occurrences.len() >= 3,
            "{:?}",
            facts.source_occurrences.keys()
        );
        check(facts, transport)
    })
}

/// [`with_freeze`] for another fixture.
fn with_freeze_of(source: &str, check: impl FnOnce(&Facts, &FrozenTransport) + Send) {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
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
        assert!(matches!(row("top"), Availability::Missing(_)));
        assert_ne!(row("selfie"), row("ping"));
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

/// (c): the exits grouped by function once equal, for every roster, the old filter of the graph's
/// exits by a whole-terminal scan (the same exits, in the same order).
#[test]
fn r378_c_exits_grouped_by_function_equal_the_scan() {
    with_freeze(|facts, _| {
        let graph = super::transport::CandidateGraph::build(facts);
        let grouped = super::grants::exits_by_function(facts, &graph);
        let mut exits = 0;
        for roster in &facts.body_rosters {
            let Some(function) = roster.point.function.as_deref() else { continue };
            let construction = roster.point.construction;
            let new = grouped
                .get(&(construction, function))
                .cloned()
                .unwrap_or_default();
            let old = super::grants::exits_by_scan(facts, &graph, construction, function);
            assert_eq!(new.len(), old.len(), "{function}");
            assert!(
                new.iter().zip(&old).all(|(a, b)| std::ptr::eq(*a, *b)),
                "{function}"
            );
            exits += old.len();
        }
        assert!(exits >= 2, "the fixture's exits: {exits}");
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

/// Relay main/379 (`matched`, step 1): the consumes found per `equal` equation, the edges `paths`
/// follows and the relations `apply` reads come from indexes, so nothing outside the row's own
/// (construction, function, block), node or callee scope is examined; the old scans (the
/// reference switch) examine such rows on this fixture, and the transport is the same either way.
#[test]
fn r379_matched_reads_only_its_own_rows_and_equals_the_scans() {
    with_freeze(|facts, transport| {
        assert_eq!(
            freeze_counts::wasted(),
            (0, 0, 0),
            "consumes / edges / relations examined outside their scope"
        );
        freeze_counts::reset();
        freeze_counts::set_reference_scans(true);
        let reference = FrozenTransport::build(facts).expect("no budget");
        let wasted = freeze_counts::wasted();
        freeze_counts::set_reference_scans(false);
        assert!(
            wasted.0 > 0 && wasted.1 > 0 && wasted.2 > 0,
            "the fixture exercises every scan: {wasted:?}"
        );
        assert_eq!(format!("{transport:?}"), format!("{reference:?}"));
    });
}

/// Relay main/379 (`matched`, step 1): the relation fixpoint re-applies and re-sweeps only the
/// callers of the scopes that gained relations in the round before, and clones `base` once; the
/// full fixpoint (the reference switch) re-sweeps unchanged functions and re-clones `base` on this
/// fixture, and the transport is the same either way.
#[test]
fn r379_b_the_fixpoint_reapplies_only_changed_callers_and_equals_the_full_one() {
    with_freeze(|facts, transport| {
        assert_eq!(
            freeze_counts::fixpoint_wasted(),
            (0, 0),
            "unchanged functions re-swept / base re-cloned"
        );
        freeze_counts::reset();
        freeze_counts::set_reference_scans(true);
        let reference = FrozenTransport::build(facts).expect("no budget");
        let wasted = freeze_counts::fixpoint_wasted();
        freeze_counts::set_reference_scans(false);
        assert!(
            wasted.0 > 0 && wasted.1 > 0,
            "the fixture exercises the full fixpoint: {wasted:?}"
        );
        assert_eq!(format!("{transport:?}"), format!("{reference:?}"));
    });
}

/// Relay main/382 (b): a relation is pushed once a round (264's repeats: 41 % of P02's round 6);
/// the old sweep (the reference switch) pushes repeats on this fixture, each with its own cloned
/// proof, and the transport is the same either way (`or_insert` kept the first).
#[test]
fn r382_b_a_relation_is_pushed_once_a_round_and_equals_the_old_sweep() {
    with_freeze_of(REPEATS_FIXTURE, |facts, transport| {
        assert_eq!(
            freeze_counts::repeats(),
            0,
            "relations pushed twice in a round"
        );
        freeze_counts::reset();
        freeze_counts::set_reference_scans(true);
        let reference = FrozenTransport::build(facts).expect("no budget");
        let repeats = freeze_counts::repeats();
        freeze_counts::set_reference_scans(false);
        assert!(
            repeats > 0,
            "the fixture repeats a relation in a round: {repeats}"
        );
        assert_eq!(format!("{transport:?}"), format!("{reference:?}"));
    });
}

/// Relay main/383: the `matched:callgraph` mark's numbers on the fixture -- `top` -> the ping / pong
/// SCC -> `leaf` is three levels; ping / pong and the self-recursive `selfie` are the non-trivial
/// SCCs; the largest has two functions; five functions.
#[test]
fn r383_the_call_graph_depth_mark_reads_the_fixture() {
    with_freeze(|facts, _| {
        let shapes: Vec<_> = (0..facts.constructions)
            .map(|construction| recursive::CallGraph::build(facts, construction).scc_depth())
            .collect();
        assert!(shapes.contains(&(3, 2, 2, 5)), "{shapes:?}");
    });
}

/// Relay main/385 (R1335-1), 3b': a lineage that would pass `LINEAGE_DEPTH` calls becomes
/// `Recursive { application: the call being prepended }` -- the scope's own call, the form a
/// repeated call already takes -- while one of exactly `LINEAGE_DEPTH` stays `Exact`.
#[test]
fn r385_a_a_lineage_deeper_than_k_becomes_the_scope_call_marker() {
    use super::matched::{CallKey, LINEAGE_DEPTH, SourceLineage};
    let call = |i: usize| CallKey {
        construction: 0,
        caller: format!("f{i}"),
        block: 0,
        statement: 0,
        callee: format!("f{}", i + 1),
    };
    let mut lineage = SourceLineage::Exact(Vec::new());
    for i in (1..=LINEAGE_DEPTH).rev() {
        lineage = lineage.through(&call(i));
    }
    assert!(
        matches!(&lineage, SourceLineage::Exact(path) if path.len() == LINEAGE_DEPTH),
        "{lineage:?}"
    );
    assert_eq!(
        lineage.through(&call(0)),
        SourceLineage::Recursive {
            application: call(0)
        },
        "one call deeper than LINEAGE_DEPTH"
    );
}
