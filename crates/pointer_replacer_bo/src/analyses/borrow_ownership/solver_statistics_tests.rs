//! R1475-2 (I1): what z3's statistics report after a scoped check on a solver configured as the
//! hard solver is (`fixed_query_params`; push, assert, check, pop).

use super::*;

/// Pigeonhole: `n + 1` pigeons, `n` holes -- unsatisfiable, with real search.
fn pigeonhole(solver: &Solver, n: usize) {
    let at = |p: usize, h: usize| Bool::new_const(format!("r1475_p{p}_h{h}"));
    for p in 0..=n {
        let holes: Vec<Bool> = (0..n).map(|h| at(p, h)).collect();
        solver.assert(Bool::or(&holes.iter().collect::<Vec<_>>()));
    }
    for h in 0..n {
        for p in 0..=n {
            for q in p + 1..=n {
                solver.assert(!Bool::and(&[&at(p, h), &at(q, h)]));
            }
        }
    }
}

/// R1475-2 (I1): z3 reports the search counters accumulated over the solver's life, not per
/// check. Three scoped checks on one solver configured as the hard solver: a pigeonhole (Unsat,
/// real search), a trivial check (Sat), the pigeonhole again. After the trivial check the counters
/// are unchanged, not reset to its own (near-zero) search; after the third they have grown by the
/// third check's search. The line's own counters are the difference across the check, so they read
/// the check alone; `life_*` are z3's totals.
#[test]
fn r1475_2_i1_z3_reports_the_search_counters_accumulated_over_the_solvers_life() {
    let solver = Solver::new();
    solver.set_params(&fixed_query_params());
    let scoped = |n: Option<usize>| {
        solver.push();
        if let Some(n) = n {
            pigeonhole(&solver, n);
        }
        let before = search_counters(&solver);
        let result = solver.check();
        let after = search_counters(&solver);
        solver.pop(1);
        assert_eq!(
            search_counters(&solver),
            after,
            "the pop leaves the counters"
        );
        (result, before, after)
    };
    let (first, before, first_after) = scoped(Some(6));
    assert_eq!(first, SatResult::Unsat);
    assert_eq!(before, [0; 4], "a new solver");
    assert!(
        first_after[0] > 0 && first_after[1] > 0 && first_after[2] > 0,
        "{first_after:?}"
    );
    let (second, _, second_after) = scoped(None);
    assert_eq!(second, SatResult::Sat);
    assert_eq!(
        second_after, first_after,
        "accumulated: the trivial check adds no search"
    );
    let (third, third_before, third_after) = scoped(Some(6));
    assert_eq!(third, SatResult::Unsat);
    assert_eq!(third_before, first_after);
    assert!(
        third_after[0] > first_after[0],
        "{first_after:?} {third_after:?}"
    );
    let line = search_statistics(third_before, third_after);
    assert_eq!(
        line,
        format!(
            "conflicts={} decisions={} propagations={} restarts={} life_conflicts={} life_decisions={} \
             life_propagations={} life_restarts={}",
            third_after[0] - first_after[0],
            third_after[1] - first_after[1],
            third_after[2] - first_after[2],
            third_after[3] - first_after[3],
            third_after[0],
            third_after[1],
            third_after[2],
            third_after[3]
        )
    );
}
