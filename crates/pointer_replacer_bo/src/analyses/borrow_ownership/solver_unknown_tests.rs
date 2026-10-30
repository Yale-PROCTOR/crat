//! Relay main/388 (R1371-1): the Optimize-Unknown path's log line, on an instance z3 cannot finish
//! under a one-unit resource limit.

use super::*;

/// Pigeonhole: `n + 1` pigeons, `n` holes -- unsatisfiable, and no small resource budget proves it.
fn pigeonhole(optimize: &Optimize, n: usize) -> Vec<(Bool, Bool)> {
    let at = |p: usize, h: usize| Bool::new_const(format!("r1371_p{p}_h{h}"));
    for p in 0..=n {
        let holes: Vec<Bool> = (0..n).map(|h| at(p, h)).collect();
        optimize.assert(&Bool::or(&holes.iter().collect::<Vec<_>>()));
    }
    for h in 0..n {
        for p in 0..=n {
            for q in p + 1..=n {
                optimize.assert(&!Bool::and(&[&at(p, h), &at(q, h)]));
            }
        }
    }
    (0..n)
        .map(|h| {
            optimize.assert_soft(&at(0, h), 1u64, None);
            (at(0, h), at(1, h))
        })
        .collect()
}

#[test]
fn r1371_unknown_path_is_logged_not_used() {
    let optimize = Optimize::new();
    let mut params = z3::Params::new();
    params.set_u32("rlimit", 1);
    optimize.set_params(&params);
    let vars = pigeonhole(&optimize, 8);
    assert_eq!(
        optimize.check(&[]),
        SatResult::Unknown,
        "the resource limit stops z3"
    );
    let reason = optimize.get_reason_unknown();
    assert!(reason.is_some(), "z3 names why it stopped");
    let detail = unknown_incumbent_detail(
        &optimize,
        vars.iter().map(|(ref_, own)| (ref_, own)),
        reason.as_deref(),
    );
    assert!(
        detail.starts_with(&format!(
            "reason={:?} model=",
            reason.as_deref().unwrap_or("-")
        )),
        "{detail}"
    );
    assert!(
        detail.ends_with("model=none") || detail.contains(" slots=8 "),
        "{detail}"
    );
}
