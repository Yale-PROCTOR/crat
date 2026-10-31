//! Relay main/388 O2 (R1382-1 / R1383-1): the incumbent verdict -- an Unknown optimize's model is
//! the round's when the budget was hit, a model exists and every hard assertion is true under it
//! with model completion; otherwise none, typed.

use super::*;

/// Soft pigeonhole: `n + 1` pigeons, `n` holes, at most one pigeon per hole (hard), each pigeon in
/// some hole (soft). The all-false assignment satisfies the hard part at once, and proving that only
/// `n` softs can hold is out of reach under `rlimit = 1`: z3 4.15 answers Unknown and still yields
/// that model (probed, main report 284's record).
fn soft_pigeonhole(n: usize, rlimit: u32) -> (Optimize, Vec<Bool>) {
    let optimize = Optimize::new();
    let mut params = z3::Params::new();
    params.set_u32("rlimit", rlimit);
    optimize.set_params(&params);
    let at = |p: usize, h: usize| Bool::new_const(format!("r1383_p{p}_h{h}"));
    for h in 0..n {
        for p in 0..=n {
            for q in p + 1..=n {
                optimize.assert(&!Bool::and(&[&at(p, h), &at(q, h)]));
            }
        }
    }
    let softs: Vec<Bool> = (0..=n)
        .map(|p| {
            Bool::or(
                &(0..n)
                    .map(|h| at(p, h))
                    .collect::<Vec<_>>()
                    .iter()
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    for soft in &softs {
        optimize.assert_soft(soft, 1u64, None);
    }
    (optimize, softs)
}

#[test]
fn r1383_o2_an_unknown_at_the_budget_with_a_hard_satisfying_model_is_taken() {
    let (optimize, _) = soft_pigeonhole(8, 1);
    assert_eq!(
        optimize.check(&[]),
        SatResult::Unknown,
        "the resource limit stops z3"
    );
    let model = optimize.get_model();
    assert!(model.is_some(), "z3 still holds its incumbent");
    let assertions = optimize.get_assertions();
    assert!(!assertions.is_empty());
    assert_eq!(incumbent_verdict(true, model.as_ref(), &assertions), Ok(()));
}

#[test]
fn r1383_o2_before_the_budget_or_without_a_model_there_is_no_model() {
    let (optimize, _) = soft_pigeonhole(8, 1);
    assert_eq!(optimize.check(&[]), SatResult::Unknown);
    let model = optimize.get_model();
    let assertions = optimize.get_assertions();
    assert_eq!(
        incumbent_verdict(false, model.as_ref(), &assertions),
        Err(IncumbentRefusal::BeforeBudget),
        "an Unknown before the budget stays no model"
    );
    assert_eq!(
        incumbent_verdict(true, None, &assertions),
        Err(IncumbentRefusal::NoModel),
        "an Unknown without a model stays no model"
    );
}

#[test]
fn r1383_o2_a_model_that_breaks_a_hard_assertion_or_a_partial_one_is_judged_with_completion() {
    // A model of another formula (`x`), judged against assertions over `y`, which it leaves
    // uninterpreted: with completion `y` is false, so `y` fails and `!y` holds -- the same completion
    // the kinds are read under (R1).
    let other = Solver::new();
    let x = Bool::new_const("r1383_x");
    let y = Bool::new_const("r1383_y");
    other.assert(&x);
    assert_eq!(other.check(), SatResult::Sat);
    let model = other.get_model().unwrap();
    assert_eq!(
        incumbent_verdict(true, Some(&model), &[x.clone(), y.clone()]),
        Err(IncumbentRefusal::HardEvalFailed),
        "an assertion the model makes false refuses it"
    );
    assert_eq!(incumbent_verdict(true, Some(&model), &[x, !y]), Ok(()));
}

/// R1383-1 R4: the receipt's incumbent lines are written only when the solve met an incumbent
/// (accepted or refused), so every receipt without one -- all of the 17 and the 376 -- is unchanged.
#[test]
fn r1383_o2_the_receipt_carries_incumbent_lines_only_when_the_solve_met_one() {
    use super::super::{borrow_verify::RoundStats, construction::incumbent_keys};
    let none = RoundStats::default();
    assert_eq!(incumbent_keys(&[&none, &none]), "");
    let met = RoundStats {
        incumbent_rounds: 2,
        hard_eval_failed: 1,
        ..RoundStats::default()
    };
    assert_eq!(
        incumbent_keys(&[&none, &met]),
        format!(
            "incumbent_rounds=2\nhard_eval_failed=1\nquery_budget_ms={}\n",
            execution_guard::query_timeout_ms()
        )
    );
}
