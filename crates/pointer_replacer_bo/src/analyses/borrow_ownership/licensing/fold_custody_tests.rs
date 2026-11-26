//! Native same-model custody before fold activation; input never executed.
use super::{fold_chain_tests::CODE, tests::inspect_attested_frame};

#[test]
fn gf08_custody_records_the_native_ownership_and_endpoint_denominator() {
    let fixture = inspect_attested_frame(CODE);
    assert!(fixture.accepted, "{:?}", fixture.construction_error);
    let accepted = fixture.export.stack_entry_final.as_ref().unwrap();
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|s| s.offset == accepted.snapshot_offset)
        .unwrap();
    let [row] = snapshot.fold_callers.as_deref().unwrap() else { panic!("one eligible caller") };
    let proof = row.outcome.as_ref().unwrap();
    let encoded = serde_json::to_value(accepted).unwrap();
    let values = encoded["fold_values"]
        .as_object()
        .expect("actual accepting model must carry fold obligations");
    let ownership: Vec<(super::transport::Node, bool)> =
        serde_json::from_value(values["ownership"].clone()).unwrap();
    let guards: Vec<(super::facts::EquationId, bool)> =
        serde_json::from_value(values["guards"].clone()).unwrap();
    let expected: std::collections::BTreeSet<_> = proof
        .requirements
        .owning
        .iter()
        .chain(&proof.requirements.zero)
        .copied()
        .collect();
    assert_eq!(
        ownership
            .iter()
            .map(|(n, _)| *n)
            .collect::<std::collections::BTreeSet<_>>(),
        expected
    );
    assert_eq!(ownership.len(), expected.len());
    let native = fixture.export.version_owns.as_ref().unwrap();
    for (node, value) in ownership {
        assert_eq!(
            value,
            native[super::super::ssa::constraint::Var::from_u32(node.var)]
        );
    }
    assert_eq!(
        guards
            .iter()
            .map(|(k, _)| *k)
            .collect::<std::collections::BTreeSet<_>>(),
        proof.requirements.guards.iter().map(|(k, _)| *k).collect()
    );
    assert_eq!(guards.len(), proof.requirements.guards.len());
    assert_eq!(accepted.stamp()["fold_values"], encoded["fold_values"]);
}

#[test]
fn gf08_custody_observed_empty_is_explicit_in_the_accepting_stamp() {
    let fixture = inspect_attested_frame("pub unsafe fn read(p:*const i32)->i32{*p}");
    assert!(fixture.accepted, "{:?}", fixture.construction_error);
    let accepted = fixture.export.stack_entry_final.as_ref().unwrap();
    let encoded = serde_json::to_value(accepted).unwrap();
    assert_eq!(
        encoded["fold_values"],
        serde_json::json!({"ownership":[],"guards":[]})
    );
    assert_eq!(accepted.stamp()["fold_values"], encoded["fold_values"]);
}

#[test]
fn gf08_custody_identity_and_missing_evaluation_never_default() {
    super::graph_tests::with_facts(CODE, |facts| {
        let facts = std::rc::Rc::new(facts.clone());
        // Controlled evaluator tests identity/availability, not native SAT.
        let selected = super::model_selection::Selection::from_model(facts.clone(), |_| Some(true));
        let values = selected.fold_values(&facts).unwrap();
        assert!(!values.ownership.is_empty() && !values.guards.is_empty());
        assert!(
            selected
                .fold_values(&std::rc::Rc::new((*facts).clone()))
                .is_none()
        );
        let absent = super::model_selection::Selection::from_model(facts.clone(), |_| None)
            .fold_values(&facts)
            .unwrap();
        assert!(absent.ownership.is_empty() && absent.guards.is_empty());
        let mut duplicate = (*facts).clone();
        let key = values.guards[0].0;
        duplicate.guards.push(
            duplicate
                .guards
                .iter()
                .find(|g| g.equation == key)
                .unwrap()
                .clone(),
        );
        let duplicate = std::rc::Rc::new(duplicate);
        let values =
            super::model_selection::Selection::from_model(duplicate.clone(), |_| Some(true))
                .fold_values(&duplicate)
                .unwrap();
        assert!(!values.guards.iter().any(|(k, _)| *k == key));
    });
}

#[test]
fn gf08_custody_rejects_missing_duplicate_and_inconsistent_native_values() {
    let fixture = inspect_attested_frame(CODE);
    let accepted = fixture.export.stack_entry_final.as_ref().unwrap();
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|s| s.offset == accepted.snapshot_offset)
        .unwrap();
    let proof = snapshot.fold_callers.as_ref().unwrap()[0]
        .outcome
        .as_ref()
        .unwrap();
    let model = proof
        .requirements
        .kind_keys
        .iter()
        .map(|key| {
            // This fixture's field spelling; values come from the accepting model.
            let native_key = if key == "Holder::field0@d0" {
                "Holder.ptr"
            } else {
                key.as_str()
            };
            let kind = fixture.kinds[native_key];
            let kind = match kind {
                super::super::SlotKind::Raw => "raw",
                super::super::SlotKind::Ref => "ref",
                super::super::SlotKind::Owning => "owning",
            };
            (key.clone(), kind.to_owned())
        })
        .collect();
    assert_eq!(
        super::fold_custody::validate(snapshot, accepted, &model),
        Ok(())
    );
    for mode in 0..5 {
        let mut changed = accepted.clone();
        let expected = match mode {
            0 => {
                changed.fold_values = None;
                "fold custody availability differs"
            }
            1 => {
                changed.fold_values.as_mut().unwrap().ownership.pop();
                "fold ownership valuation coverage differs"
            }
            2 => {
                let values = changed.fold_values.as_mut().unwrap();
                values.guards.push(values.guards[0]);
                "fold guard valuation coverage differs"
            }
            3 => {
                changed.fold_values.as_mut().unwrap().guards.pop();
                "fold guard valuation coverage differs"
            }
            _ => {
                let guard = changed.fold_guards.as_ref().unwrap()[0].0;
                let values = changed.fold_values.as_mut().unwrap();
                let (_, value) = values.guards.iter_mut().find(|(k, _)| *k == guard).unwrap();
                *value = !*value;
                "fold predicate custody disagrees with selection"
            }
        };
        assert_eq!(
            super::fold_custody::validate(snapshot, &changed, &model),
            Err(expected.into()),
            "mutation {mode}"
        );
    }
}

#[test]
fn gf08_custody_checks_every_selected_premise_on_a_proposed_valuation() {
    let fixture = inspect_attested_frame(CODE);
    let mut proposed = fixture.export.stack_entry_final.as_ref().unwrap().clone();
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|s| s.offset == proposed.snapshot_offset)
        .unwrap();
    let proof = snapshot.fold_callers.as_ref().unwrap()[0]
        .outcome
        .as_ref()
        .unwrap();
    // A hand-authored validator proposal; this does not claim native activation.
    proposed.fold_guards.as_mut().unwrap()[0].1 = true;
    proposed.fold_values = Some(super::fold_custody::Values {
        ownership: proof
            .requirements
            .owning
            .iter()
            .map(|n| (*n, true))
            .chain(proof.requirements.zero.iter().map(|n| (*n, false)))
            .collect(),
        guards: proof.requirements.guards.clone(),
    });
    let model = proof
        .requirements
        .kind_keys
        .iter()
        .map(|k| (k.clone(), "owning".into()))
        .collect();
    assert_eq!(
        super::fold_custody::validate(snapshot, &proposed, &model),
        Ok(())
    );
    for mode in 0..5 {
        let mut changed = proposed.clone();
        let mut model = model.clone();
        let expected = match mode {
            0 => {
                changed.closed_call_world = false;
                "selected fold lacks closed caller frame"
            }
            1 => {
                model.insert(proof.requirements.kind_keys[0].clone(), "ref".into());
                "selected fold kind differs"
            }
            2 => {
                changed
                    .fold_values
                    .as_mut()
                    .unwrap()
                    .ownership
                    .iter_mut()
                    .find(|(n, _)| *n == proof.requirements.owning[0])
                    .unwrap()
                    .1 = false;
                "selected fold responsibility differs"
            }
            3 => {
                changed
                    .fold_values
                    .as_mut()
                    .unwrap()
                    .ownership
                    .iter_mut()
                    .find(|(n, _)| *n == proof.requirements.zero[0])
                    .unwrap()
                    .1 = true;
                "selected fold responsibility differs"
            }
            _ => {
                changed
                    .fold_values
                    .as_mut()
                    .unwrap()
                    .guards
                    .iter_mut()
                    .find(|(k, _)| *k == proof.payload.free)
                    .unwrap()
                    .1 = false;
                "selected fold endpoint or law guard differs"
            }
        };
        assert_eq!(
            super::fold_custody::validate(snapshot, &changed, &model),
            Err(expected.into()),
            "premise {mode}"
        );
    }
}

#[test]
fn gf08_custody_rejects_joint_false_guard_with_kept_native_endpoints() {
    let fixture = inspect_attested_frame(CODE);
    let mut changed = fixture.export.stack_entry_final.as_ref().unwrap().clone();
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|s| s.offset == changed.snapshot_offset)
        .unwrap();
    let proof = snapshot.fold_callers.as_ref().unwrap()[0]
        .outcome
        .as_ref()
        .unwrap();
    assert_eq!(
        changed.fold_guards.as_ref().unwrap(),
        &vec![(proof.guard, true)]
    );
    let values = changed.fold_values.as_ref().unwrap();
    for key in [
        proof.payload.source.endpoint,
        proof.payload.free,
        proof.container.source.endpoint,
        proof.container.free,
    ] {
        assert!(values.guards.contains(&(key, true)));
    }
    changed.fold_guards.as_mut().unwrap()[0].1 = false;
    changed
        .fold_values
        .as_mut()
        .unwrap()
        .guards
        .iter_mut()
        .find(|(k, _)| *k == proof.guard)
        .unwrap()
        .1 = false;
    assert_eq!(
        super::fold_custody::validate(snapshot, &changed, &Default::default()),
        Err("fold original endpoints lack selected guard".into()),
        "agreement of two false copies cannot defeat the endpoint converse"
    );
    changed.closed_call_world = false;
    assert_eq!(
        super::fold_custody::validate(snapshot, &changed, &Default::default()),
        Err("selected fold lacks closed caller frame".into()),
        "changing the acceptance frame cannot hide the native antecedent"
    );
}

/// The accepting model's custody denominator covers the MEMBER
/// requirements. For a used-child declaration the identity family holds and
/// contributes nothing, so this valuation is the member's alone.
#[test]
fn oc09_custody_covers_the_member_requirements_in_the_accepting_model() {
    use std::collections::BTreeSet;
    let fixture = inspect_attested_frame(super::fold_subtree_tests::CODE);
    assert!(fixture.accepted, "{:?}", fixture.construction_error);
    let accepted = fixture.export.stack_entry_final.as_ref().unwrap();
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|s| s.offset == accepted.snapshot_offset)
        .unwrap();
    let [identity] = snapshot.fold_callers.as_deref().unwrap() else { panic!("one declaration") };
    assert!(
        identity.outcome.is_err(),
        "the identity family holds a used descendant: {:?}",
        identity.outcome
    );
    let [row] = snapshot.fold_members.as_deref().unwrap() else {
        panic!("one used-child declaration")
    };
    let proof = row.outcome.as_ref().expect("member certificate");
    let encoded = serde_json::to_value(accepted).unwrap();
    let values = encoded["fold_values"]
        .as_object()
        .expect("the accepting model must carry the member obligations");
    let ownership: Vec<(super::transport::Node, bool)> =
        serde_json::from_value(values["ownership"].clone()).unwrap();
    let guards: Vec<(super::facts::EquationId, bool)> =
        serde_json::from_value(values["guards"].clone()).unwrap();
    let expected: BTreeSet<_> = proof
        .requirements
        .owning
        .iter()
        .chain(&proof.requirements.zero)
        .copied()
        .collect();
    assert_eq!(
        ownership.iter().map(|(n, _)| *n).collect::<BTreeSet<_>>(),
        expected,
        "member ownership obligations are the custody denominator"
    );
    assert_eq!(ownership.len(), expected.len());
    let native = fixture.export.version_owns.as_ref().unwrap();
    for (node, value) in ownership {
        assert_eq!(
            value,
            native[super::super::ssa::constraint::Var::from_u32(node.var)]
        );
    }
    assert_eq!(
        guards.iter().map(|(k, _)| *k).collect::<BTreeSet<_>>(),
        proof.requirements.guards.iter().map(|(k, _)| *k).collect()
    );
    assert_eq!(guards.len(), proof.requirements.guards.len());
    assert_eq!(accepted.stamp()["fold_values"], encoded["fold_values"]);
}

/// R1556-4 S1's move-store fixture (the null-paths W60 `P` shape: a field store by move).
const S1_MOVED: &str = r#"
#[repr(C)] pub struct Node { pub key: i32, pub left: *mut Node }
unsafe extern "C" { fn malloc(n: usize) -> *mut Node; fn free(p: *mut Node); }
unsafe fn new() -> *mut Node { let n = malloc(16); (*n).key = 0; (*n).left = 0 as *mut Node; n }
unsafe fn attach(y: *mut Node, x: *mut Node) -> *mut Node { let t = x; (*y).left = t; y }
unsafe fn leftmost(n: *mut Node) -> *mut Node { let mut c = n; while !(*c).left.is_null() { c = (*c).left; } c }
unsafe fn destroy(n: *mut Node) { if !n.is_null() { destroy((*n).left); free(n); } }
#[no_mangle] pub unsafe extern "C" fn run() -> i32 { let t = attach(new(), new()); let m = leftmost(t); let k = (*m).key; destroy(t); k }
"#;

/// R1556-4 S1 (a), (b): the indexed `from_model` (guards by equation, move-store equations and
/// consumes by site) gives the reference scan's results with the same calls of `evaluate`, in the
/// same order, by term identity. On the fold-custody and move-store fixtures, each as built, with a
/// guard key given a second binding (ambiguous: neither reads it) and with one given none (absent),
/// and under two value patterns: the sequence of asked terms (their z3 pointers, read without a z3
/// call) and every reader's result (the guard values, the traversal owns, the fold values, the
/// move-store owns) are equal.
#[test]
fn r1556_4_s1_the_indexed_selection_is_the_scan() {
    use std::rc::Rc;

    use z3::ast::Ast;

    use super::model_selection::Selection;
    let mut compared = 0;
    let mut move_stores = 0;
    for (tag, code) in [("fold", CODE), ("moved", S1_MOVED)] {
        super::graph_tests::with_facts(code, |facts| {
            let mut variants = vec![("as-built", facts.clone())];
            if let Some(first) = facts.guards.first().cloned() {
                let mut two = facts.clone();
                two.guards.push(first.clone());
                variants.push(("two-bindings", two));
                let mut none = facts.clone();
                none.guards.retain(|row| row.equation != first.equation);
                variants.push(("no-binding", none));
            }
            for (variant, facts) in variants {
                let facts = Rc::new(facts);
                let vars = super::super::move_store::destination_vars(&facts);
                assert_eq!(
                    vars,
                    super::super::move_store::destination_vars_by_scan(&facts),
                    "{tag} {variant}: move-store candidates"
                );
                move_stores += vars.len();
                for flip in [false, true] {
                    let run = |indexed: bool| {
                        let mut asked = Vec::new();
                        let evaluate = |term: &z3::ast::Bool| {
                            asked.push(term.get_z3_ast().as_ptr() as usize);
                            Some((asked.len() % 2 == 0) != flip)
                        };
                        let selection = if indexed {
                            Selection::from_model(facts.clone(), evaluate)
                        } else {
                            Selection::from_model_by_scan(facts.clone(), evaluate)
                        };
                        (asked, selection)
                    };
                    let (indexed_asked, indexed) = run(true);
                    let (scan_asked, scan) = run(false);
                    let at = format!("{tag} {variant} flip={flip}");
                    assert_eq!(indexed_asked, scan_asked, "{at}: the order of calls");
                    assert_eq!(indexed.values(&facts), scan.values(&facts), "{at}");
                    assert_eq!(
                        indexed.traversal_ownership(&facts),
                        scan.traversal_ownership(&facts),
                        "{at}"
                    );
                    assert_eq!(
                        indexed.fold_values(&facts),
                        scan.fold_values(&facts),
                        "{at}"
                    );
                    for &var in &vars {
                        assert_eq!(
                            indexed.move_store_own(&facts, var),
                            scan.move_store_own(&facts, var),
                            "{at} var {var}"
                        );
                    }
                    compared += 1;
                }
            }
        });
    }
    assert!(compared >= 8, "{compared} comparisons");
    assert!(move_stores > 0, "the move-store fixture has a candidate");
}
