//! OC06 caller certificate. Fixtures are never executed and nothing activates.
use super::{fold_caller::Hold, fold_subtree_tests::CODE, graph_tests::with_facts};

#[test]
fn oc06_member_caller_certificate_binds_membership_forwarding_zero_and_laws() {
    with_facts(CODE, |facts| {
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            0,
            &["Node::field0@d0".to_owned()].into_iter().collect(),
        )
        .unwrap();
        let proof = super::fold_member_caller::certify(facts, declaration, &fold)
            .expect("complete member caller certificate");
        let member = super::fold_subtree::certify(facts, declaration, &fold).unwrap();
        assert_eq!(proof.guard, declaration.guard);
        assert_eq!(proof.membership, member);
        assert_eq!(proof.terminal_inventory, member.terminal_inventory);

        // The three receipts are the same ones the member laws stand on.
        assert_eq!(proof.forwarding.membership.as_ref(), &member);
        assert_eq!(proof.forwarding.forwarding.receiver, member.fold.receiver);
        assert_eq!(proof.zero_output.required_zero, fold.descendants[0].output);
        assert_eq!(proof.plan.routes.len(), 3);
        assert_eq!(proof.plan.laws.consumes, proof.checked_consumes);
        assert_eq!(proof.plan.laws.equations, proof.checked_equations);

        // Requirements carry the membership's own obligations plus the laws,
        // and never claim a node as both owning and zero.
        for node in &member.requirements.owning {
            assert!(proof.requirements.owning.contains(node));
        }
        for node in &member.requirements.zero {
            assert!(proof.requirements.zero.contains(node));
        }
        assert!(
            proof
                .requirements
                .owning
                .iter()
                .all(|node| !proof.requirements.zero.contains(node))
        );
        assert!(proof.requirements.kind_keys.contains(&member.field));
        for (key, value) in &member.requirements.guards {
            assert_eq!(proof.requirements.guards.contains(&(*key, *value)), true);
        }
    });
}

#[test]
fn oc06_member_caller_certificate_refuses_a_fold_that_is_not_this_declaration() {
    with_facts(CODE, |facts| {
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            0,
            &["Node::field0@d0".to_owned()].into_iter().collect(),
        )
        .unwrap();
        let mut wrong = declaration.clone();
        wrong.guard.ordinal = usize::MAX;
        let refusal = super::fold_member_caller::certify(facts, &wrong, &fold);
        assert!(
            matches!(
                refusal,
                Err(Hold::Member(super::fold_subtree::Hold::Declaration))
            ),
            "{refusal:?}"
        );
    });
}

#[test]
fn oc07_a_used_child_declaration_yields_a_member_decision_beside_the_held_identity_one() {
    use super::{fold_call::Error, fold_eligibility};
    with_facts(CODE, |facts| {
        // The identity family is unchanged: a used descendant is not admitted
        // by the certificate that assumes the callee never touches it.
        let identity = fold_eligibility::plan(facts).expect("identity decisions");
        let [held] = identity.as_slice() else { panic!("one declaration") };
        assert!(
            matches!(&held.outcome, Err(fold_eligibility::Hold::Call(Error::FieldScheme(field))) if field == "Node::field0@d0"),
            "{:?}",
            held.outcome
        );

        let members = fold_eligibility::member_plan(facts).expect("member decisions");
        let [decision] = members.as_slice() else { panic!("one used-child declaration") };
        assert_eq!(decision.declaration, held.declaration);
        assert_eq!(
            decision.fields,
            ["Node::field0@d0".to_owned()].into_iter().collect()
        );
        let proof = decision
            .outcome
            .as_ref()
            .expect("the used-child member caller certificate qualifies");
        assert_eq!(proof.guard, decision.declaration.guard);
        assert_eq!(proof.plan.routes.len(), 3);
        // Three allocations and the two frees this caller performs; the parent's
        // free belongs to the callee and is deliberately not here.
        assert_eq!(proof.endpoints.len(), 5);
        assert!(proof.endpoints.iter().all(|endpoint| {
            facts.equations.iter().any(|e| {
                e.point.construction == endpoint.construction
                    && e.ordinal == endpoint.ordinal
                    && e.point.function.as_ref() == Some(&decision.declaration.call.caller)
                    && e.endpoint.is_some()
            })
        }));
    });
}

#[test]
fn oc07_a_declaration_the_identity_certificate_admits_yields_no_member_decision() {
    use super::fold_eligibility;
    with_facts(super::fold_chain_tests::CODE, |facts| {
        let identity = fold_eligibility::plan(facts).expect("identity decisions");
        let [admitted] = identity.as_slice() else { panic!("one declaration") };
        assert!(admitted.outcome.is_ok(), "{:?}", admitted.outcome);
        assert_eq!(
            fold_eligibility::member_plan(facts),
            Some(Vec::new()),
            "the member family admits only what the identity certificate refuses \
             for a used descendant"
        );
    });
}
