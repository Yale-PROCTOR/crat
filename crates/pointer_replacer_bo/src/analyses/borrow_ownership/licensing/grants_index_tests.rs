//! Relay main/388 walls 3+4 (R1363-1): each index `grants::plan` and `return_port_owning` now
//! read equals the whole-table scan it replaces, on the facts of a fixture program -- the scan kept
//! as the oracle, as 3d's was (`field_support_lookup_tests.rs`).

use super::{
    super::{
        super::ownership_boundary::Role,
        fold_caller::{
            freeing_frames, frees_by_scan, place_rows, place_rows_by_scan, role_rows,
            role_rows_by_scan,
        },
        graph_tests::with_facts,
        transport::CandidateGraph,
    },
    *,
};
use crate::analyses::borrow_ownership::ownership_access::PlaceSyntax;

/// Allocations copied, moved, freed, returned (fresh, fresh-or-null), stored into a struct's
/// field, handed to callees: every table the indexes group has rows in several scopes.
const WALLS: &str = r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub struct Pair { pub a: *mut i32, pub b: *mut i32 }
pub unsafe fn make() -> *mut i32 { let p = malloc(4); *p = 1; p }
pub unsafe fn make_or_null(flag: bool) -> *mut i32 { if flag { malloc(4) } else { 0 as *mut i32 } }
pub unsafe fn wrapper() -> *mut i32 { let q = make(); q }
pub unsafe fn consume(p: *mut i32) { free(p); }
pub unsafe fn store(pair: *mut Pair) { let p = malloc(4); (*pair).a = p; let q = (*pair).b; free(q); }
pub unsafe fn moved() -> *mut i32 { let p = malloc(8); let q = p; let r = q; r }
pub unsafe fn run() {
    let p = wrapper();
    let q = p;
    consume(q);
    let r = make_or_null(true);
    if !r.is_null() { free(r); }
    let s = moved();
    consume(s);
}
"#;

/// Every roster's (construction, function), and one absent scope.
fn scopes(facts: &Facts) -> Vec<(u32, String)> {
    let mut scopes: Vec<_> = facts
        .body_rosters
        .iter()
        .filter_map(|roster| {
            roster
                .point
                .function
                .clone()
                .map(|function| (roster.point.construction, function))
        })
        .collect();
    scopes.push((0, "absent".to_owned()));
    scopes
}

fn same<T>(left: &[&T], right: &[&T]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(a, b)| std::ptr::eq(*a, *b))
}

fn filter<'f, T>(rows: &'f [T], point: impl Fn(&T) -> &Point, c: u32, f: &str) -> Vec<&'f T> {
    rows.iter()
        .filter(|row| {
            let point = point(row);
            point.construction == c && point.function.as_deref() == Some(f)
        })
        .collect()
}

/// G1: every group equals the per-roster filter it replaces, row for row and in table order, for
/// each table `plan` reads; and some group has several rows.
#[test]
fn r1363_g1_the_scope_groups_equal_the_per_roster_filters() {
    with_facts(WALLS, |facts| {
        let tables = Tables::build(facts);
        let mut widest = 0;
        for (c, f) in scopes(facts) {
            let equations = filter(&facts.equations, |row| &row.point, c, &f);
            assert!(
                same(scoped(&tables.equations, c, &f), &equations),
                "equations {c} {f}"
            );
            let consumes = filter(&facts.consumes, |row| &row.point, c, &f);
            assert!(
                same(scoped(&tables.consumes, c, &f), &consumes),
                "consumes {c} {f}"
            );
            let terminals = filter(&facts.terminals, |row| &row.point, c, &f);
            assert!(
                same(scoped(&tables.terminals, c, &f), &terminals),
                "terminals {c} {f}"
            );
            let boundaries = filter(&facts.boundary_substitutions, |row| &row.point, c, &f);
            assert!(
                same(scoped(&tables.boundaries, c, &f), &boundaries),
                "boundaries {c} {f}"
            );
            let registrations = filter(&facts.call_arg_registrations, |row| &row.point, c, &f);
            assert!(
                same(scoped(&tables.registrations, c, &f), &registrations),
                "registrations {c} {f}"
            );
            let heads: Vec<_> = facts
                .raw_pointer_heads
                .iter()
                .filter(|h| h.function == f)
                .collect();
            let indexed: Vec<_> = tables.heads.get(f.as_str()).cloned().unwrap_or_default();
            assert!(same(&indexed, &heads), "heads {f}");
            widest = widest.max(equations.len().min(consumes.len()));
        }
        assert!(widest >= 2, "some scope has several rows");
    });
}

/// G2: every transfer's rows from the scope's equations equal the whole-table scan.
#[test]
fn r1363_g2_the_transfer_rows_equal_the_scan() {
    with_facts(WALLS, |facts| {
        let tables = Tables::build(facts);
        let mut transfers = 0;
        for equation in &facts.equations {
            let (Some(transfer), Some(function)) =
                (&equation.transfer, equation.point.function.as_deref())
            else {
                continue;
            };
            let scope = scoped(&tables.equations, equation.point.construction, function);
            let rows = transfer_rows(scope, equation, transfer);
            assert!(same(
                &rows,
                &transfer_rows_by_scan(facts, equation, transfer)
            ));
            transfers += 1;
        }
        assert!(transfers >= 2, "the fixture has transfers");
    });
}

/// G3: the occurrence checks -- an outcome-free source / sink row at a site, a local's unprojected
/// consume rows at a site -- equal the scans, at every site and local of every scope.
#[test]
fn r1363_g3_the_occurrence_checks_equal_the_scans() {
    with_facts(WALLS, |facts| {
        let tables = Tables::build(facts);
        let (mut found, mut defined) = (0, 0);
        for (c, f) in scopes(facts) {
            let equations = scoped(&tables.equations, c, &f);
            let consumes = scoped(&tables.consumes, c, &f);
            let sites: BTreeSet<(u32, usize)> = facts
                .equations
                .iter()
                .map(|row| &row.point)
                .chain(facts.consumes.iter().map(|row| &row.point))
                .filter_map(|point| point.block.zip(point.statement))
                .collect();
            let locals: BTreeSet<u32> = facts.consumes.iter().map(|row| row.local).collect();
            for &(block, statement) in &sites {
                for operation in ["source", "sink"] {
                    let indexed = endpoint_row(equations, operation, block, statement);
                    let scan = endpoint_row_by_scan(facts, c, &f, operation, block, statement);
                    assert_eq!(indexed, scan, "{c} {f} {operation} bb{block}[{statement}]");
                    found += usize::from(indexed);
                }
                for &local in &locals {
                    let indexed = definitions(consumes, block, statement, local);
                    let scan = definitions_by_scan(facts, c, &f, block, statement, local);
                    assert!(
                        same(&indexed, &scan),
                        "{c} {f} _{local} bb{block}[{statement}]"
                    );
                    defined += usize::from(!indexed.is_empty());
                }
            }
        }
        assert!(found >= 2 && defined >= 2, "the checks hold somewhere");
    });
}

/// G4: a roster's local evidence equals the scans, for every edge of the candidate graph.
#[test]
fn r1363_g4_the_edge_locality_equals_the_scan() {
    with_facts(WALLS, |facts| {
        let tables = Tables::build(facts);
        let graph = CandidateGraph::build(facts);
        let (mut local, mut foreign) = (0, 0);
        for (c, f) in scopes(facts) {
            let locality = Locality::build(
                c,
                scoped(&tables.equations, c, &f),
                scoped(&tables.boundaries, c, &f),
            );
            for edge in &graph.edges {
                let indexed = locality.local(&edge.evidence);
                assert_eq!(
                    indexed,
                    local_by_scan(facts, &edge.evidence, c, &f),
                    "{c} {f}"
                );
                if indexed {
                    local += 1;
                } else {
                    foreign += 1;
                }
            }
        }
        assert!(local >= 1 && foreign >= 1, "both answers occur");
    });
}

/// R1: a place's consume rows at a site, from the scope's consumes, equal the scan -- for every
/// consume row's own (local, projection) at its site, and every store's place.
#[test]
fn r1363_r1_the_place_rows_equal_the_scan() {
    with_facts(WALLS, |facts| {
        let consumes = by_scope(&facts.consumes, |row| &row.point);
        let mut probes: Vec<(u32, String, u32, usize, PlaceSyntax)> = facts
            .consumes
            .iter()
            .filter_map(|row| {
                Some((
                    row.point.construction,
                    row.point.function.clone()?,
                    row.point.block?,
                    row.point.statement?,
                    PlaceSyntax {
                        local: row.local,
                        projection: row.projection.clone(),
                    },
                ))
            })
            .collect();
        for store in &facts.field_support_inputs.stores {
            for c in 0..facts.constructions.max(1) {
                probes.push((
                    c,
                    store.site.function.clone(),
                    store.site.block,
                    store.site.statement,
                    store.site.place.clone(),
                ));
            }
        }
        let mut several = 0;
        for (c, f, block, statement, place) in &probes {
            let indexed = place_rows(scoped(&consumes, *c, f), *block, *statement, place);
            let scan = place_rows_by_scan(facts, *c, f, *block, *statement, place);
            assert!(
                same(&indexed, &scan),
                "{c} {f} bb{block}[{statement}] {place:?}"
            );
            several += usize::from(!indexed.is_empty());
        }
        assert!(several >= 2, "the probes find rows");
    });
}

/// R2: a scope's boundary rows of one role equal the scan, for both roles the rule reads.
#[test]
fn r1363_r2_the_role_rows_equal_the_scan() {
    with_facts(WALLS, |facts| {
        let boundaries = by_scope(&facts.boundary_substitutions, |row| &row.point);
        let mut found = 0;
        for (c, f) in scopes(facts) {
            for role in [Role::ExitReturn, Role::CallArgument] {
                let indexed = role_rows(scoped(&boundaries, c, &f), role);
                assert!(
                    same(&indexed, &role_rows_by_scan(facts, c, &f, role)),
                    "{c} {f} {role:?}"
                );
                found += usize::from(!indexed.is_empty());
            }
        }
        assert!(found >= 2, "both roles occur");
    });
}

/// R3: the freeing scopes equal the per-roster scan; some scope frees and some does not.
#[test]
fn r1363_r3_the_freeing_scopes_equal_the_scan() {
    with_facts(WALLS, |facts| {
        let freeing = freeing_frames(facts);
        let (mut frees, mut clean) = (0, 0);
        for (c, f) in scopes(facts) {
            let indexed = freeing.contains(&(c, f.as_str()));
            assert_eq!(indexed, frees_by_scan(facts, c, &f), "{c} {f}");
            if indexed {
                frees += 1;
            } else {
                clean += 1;
            }
        }
        assert!(frees >= 1 && clean >= 1, "both answers occur");
    });
}
