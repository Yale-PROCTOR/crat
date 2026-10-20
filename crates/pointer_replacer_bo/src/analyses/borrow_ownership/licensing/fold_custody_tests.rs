//! Native same-model custody before fold activation; input never executed.
use super::{fold_chain_tests::CODE, tests::inspect_era5_frame};

#[test]
fn gf08_custody_records_the_native_ownership_and_endpoint_denominator() {
    let fixture = inspect_era5_frame(CODE);
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
    let fixture = inspect_era5_frame("pub unsafe fn read(p:*const i32)->i32{*p}");
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
    let fixture = inspect_era5_frame(CODE);
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
    let fixture = inspect_era5_frame(CODE);
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
    let fixture = inspect_era5_frame(CODE);
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

/// OC09 (R309-1): the accepting model's custody denominator covers the MEMBER
/// requirements. For a used-child declaration the identity family holds and
/// contributes nothing, so this valuation is the member's alone.
#[test]
fn oc09_custody_covers_the_member_requirements_in_the_accepting_model() {
    use std::collections::BTreeSet;
    let fixture = inspect_era5_frame(super::fold_subtree_tests::CODE);
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

/// R348-1(iii) preflight: what the member family actually does on the bst
/// fixture, before a witness asserts anything about it.
#[test]
#[ignore = "diagnostic for the member-selected witness"]
fn r348_member_selection_preflight() {
    eprintln!(); // R325-1
    let fixture = inspect_era5_frame(super::witnesses::BST);
    eprintln!(
        "MEMBERSEL accepted={} error={:?}",
        fixture.accepted, fixture.construction_error
    );
    let Some(accepted) = fixture.export.stack_entry_final.as_ref() else {
        eprintln!("MEMBERSEL no accepted stack entry");
        return;
    };
    let selected: std::collections::BTreeMap<_, _> = accepted
        .fold_guards
        .as_deref()
        .unwrap_or_default()
        .iter()
        .copied()
        .collect();
    eprintln!("MEMBERSEL selected_guards={selected:?}");
    for snapshot in fixture
        .export
        .ownership_licensing
        .as_deref()
        .unwrap_or_default()
    {
        eprintln!(
            "MEMBERSEL snapshot offset={} identity={} members={}",
            snapshot.offset,
            snapshot.fold_callers.as_deref().unwrap_or_default().len(),
            snapshot.fold_members.as_deref().unwrap_or_default().len()
        );
        for row in snapshot.fold_callers.as_deref().unwrap_or_default() {
            eprintln!(
                "MEMBERSEL identity {} {}:{} guard={:?} selected={:?} outcome={}",
                row.declaration.call.caller,
                row.declaration.call.block,
                row.declaration.call.statement,
                row.declaration.guard,
                selected.get(&row.declaration.guard),
                match &row.outcome {
                    Ok(_) => "Ok".to_owned(),
                    Err(hold) => format!("{hold:?}"),
                }
            );
        }
        for row in snapshot.fold_members.as_deref().unwrap_or_default() {
            eprintln!(
                "MEMBERSEL member {} {}:{} guard={:?} selected={:?} fields={:?} outcome={}",
                row.declaration.call.caller,
                row.declaration.call.block,
                row.declaration.call.statement,
                row.declaration.guard,
                selected.get(&row.declaration.guard),
                row.fields,
                match &row.outcome {
                    Ok(_) => "Ok".to_owned(),
                    Err(hold) => format!("{hold:?}"),
                }
            );
        }
    }
}

/// R348-1(iii): a member-selected row reaches "pending fold selected without
/// closure", and does so fail-closed.
///
/// The solver activates a fold guard from the MEMBER certificate when the
/// identity outcome is `Err` (`solver.rs`, the `else if closed && member` arm),
/// and `stack_export` records the accepted valuation of every fold-call guard
/// without regard to which family certified it. Custody's selected-row loop
/// iterates the identity family alone and unwraps its outcome, so the entry is
/// refused as a whole.
///
/// bst is the case that reaches the field scheme: its `deleteNode`
/// declarations hold at `Call(FieldScheme(..))` with a member decision each.
/// No member outcome is `Ok` today, so the selection is applied here rather
/// than found — which is exactly what the member arm would have produced. The
/// snapshot is left untouched, so the plan custody recomputes still matches and
/// the refusal is the one under test rather than an eligibility difference.
#[test]
fn r348_member_selected_row_is_refused_not_admitted() {
    let fixture = inspect_era5_frame(super::witnesses::BST);
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

    // The measured shape this witness rests on: an identity row that refuses at
    // the field scheme, with a member decision for the same declaration.
    let held = snapshot
        .fold_callers
        .as_deref()
        .unwrap_or_default()
        .iter()
        .find(|row| {
            matches!(
                &row.outcome,
                Err(super::fold_eligibility::Hold::Call(
                    super::fold_call::Error::FieldScheme(_)
                ))
            )
        })
        .expect("bst holds a declaration at the field scheme");
    assert!(
        snapshot
            .fold_members
            .as_deref()
            .unwrap_or_default()
            .iter()
            .any(|row| row.declaration.guard == held.declaration.guard),
        "the member family reaches the same declaration"
    );

    let model = std::collections::BTreeMap::new();
    assert_eq!(
        super::fold_custody::validate(snapshot, accepted, &model),
        Ok(()),
        "unselected, the entry validates"
    );

    let mut selected = accepted.clone();
    let guard = held.declaration.guard;
    for (key, value) in selected.fold_guards.as_mut().unwrap() {
        if *key == guard {
            *value = true;
        }
    }
    // The valuation moves with the selection; otherwise custody refuses for
    // disagreeing with it and never reaches the row under test.
    for (key, value) in &mut selected.fold_values.as_mut().unwrap().guards {
        if *key == guard {
            *value = true;
        }
    }
    assert_eq!(
        super::fold_custody::validate(snapshot, &selected, &model),
        Err("pending fold selected without closure".into()),
        "a member-selected row is refused, not admitted"
    );
}

/// R351-4: the fixture control for `deleteNode`'s uncovered store.
///
/// The corpus refuses at `_27 = move _28 as *mut libc::c_void` (bb11 s7), a
/// depth-0 store the certificate covers as neither transfer nor proxy. The
/// fixture writes the same `free(root as *mut …c_void)` and does not refuse
/// there. This prints the fixture's own occurrences around its free, so the
/// two spellings can be compared rather than assumed.
#[test]
#[ignore = "diagnostic for the deleteNode store control"]
fn r351_fixture_delete_node_store_control() {
    eprintln!(); // R325-1
    let fixture = inspect_era5_frame(super::witnesses::BST);
    eprintln!(
        "FIXTURE accepted={} error={:?}",
        fixture.accepted, fixture.construction_error
    );
    for snapshot in fixture
        .export
        .ownership_licensing
        .as_deref()
        .unwrap_or_default()
    {
        for row in snapshot.fold_callers.as_deref().unwrap_or_default() {
            eprintln!(
                "FIXTURE decision {} {}:{} outcome={}",
                row.declaration.call.caller,
                row.declaration.call.block,
                row.declaration.call.statement,
                match &row.outcome {
                    Ok(_) => "certified".to_owned(),
                    Err(hold) => format!("{hold:?}"),
                }
            );
        }
        break;
    }
    // R356-4(d): the equations recorded AT the store, which is what `covered`
    // looks for. The corpus records four `assume(false)` rows there and no
    // transfer at all.
    if let Some(snapshot) = fixture
        .export
        .ownership_licensing
        .as_deref()
        .unwrap_or_default()
        .first()
    {
        for equation in &snapshot.metadata.equations {
            let Some(block) = equation.point.block else { continue };
            if block != 11 {
                continue;
            }
            eprintln!(
                "FIXTURE equation {}:{:?} ordinal={} op={} value={:?} vars={:?} transfer={}",
                block,
                equation.point.statement,
                equation.ordinal,
                equation.operation,
                equation.value,
                equation.variables,
                equation
                    .transfer
                    .as_ref()
                    .map(|t| format!("{:?}->{:?}", t.source, t.destination))
                    .unwrap_or_else(|| "none".into()),
            );
        }
    }
    let occurrences = fixture
        .export
        .ownership_licensing
        .as_deref()
        .unwrap_or_default()
        .first()
        .map(|s| s.metadata.occurrences.clone())
        .unwrap_or_default();
    for (function, rows) in &occurrences {
        if !function.ends_with("deleteNode") {
            continue;
        }
        for occurrence in rows {
            eprintln!(
                "FIXTURE occurrence {} {}:{} kind={:?} dest={:?} expr={:?}",
                function,
                occurrence.site.block,
                occurrence.site.statement,
                occurrence.kind,
                occurrence.syntax.destination,
                occurrence.syntax.expression
            );
        }
    }
}
