//! Member return and zero-output obligations stay distinct. No input executes.
use super::{
    facts::Facts,
    fold_subtree::Membership,
    fold_subtree_tests::CODE,
    matched::{MatchedTransport, Meet, TerminalTarget},
};
pub(super) fn with_case(
    check: impl FnOnce(&Facts, &Membership, &MatchedTransport, &[Meet]) + Send,
) {
    super::graph_tests::with_facts(CODE, move |facts| {
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            0,
            &["Node::field0@d0".to_owned()].into_iter().collect(),
        )
        .unwrap();
        let member = super::fold_subtree::certify(facts, declaration, &fold).unwrap();
        let transport = MatchedTransport::build_with_subtree_folds(
            facts,
            &[(declaration.guard, fold)],
            &[member.clone()],
        )
        .unwrap();
        let source = super::transport::CandidateGraph::build(facts)
            .sources
            .into_iter()
            .find(|s| s.equation == member.member.endpoint)
            .unwrap();
        let meets = transport.meets_for(source.node);
        check(facts, &member, &transport, &meets);
    });
}
#[test]
fn oc04_member_return_keeps_exact_receiver_free_and_old_zero() {
    with_case(|facts, member, transport, meets| {
        let returned = member.fold.internal.packed_return.as_ref().unwrap().root;
        let output = meets
            .iter()
            .find(|m| matches!(m.terminal.target,TerminalTarget::Output{node,..} if node==returned))
            .unwrap();
        let free = meets
            .iter()
            .find(|m| matches!(m.terminal.target, TerminalTarget::Free(_)))
            .unwrap();
        assert!(transport.forward_return(facts, output, free).is_none());
        let receipt = transport
            .forward_member_return(facts, output, free, member)
            .expect("typed member return forwarding");
        assert_eq!(receipt.membership.as_ref(), member);
        assert_eq!(receipt.forwarding.receiver, member.fold.receiver);
        assert_eq!(receipt.forwarding.continuation, *free);
        assert_eq!(receipt.forwarding.output, *output);
        assert_eq!(
            receipt.forwarding.guards.get(&member.declaration.guard),
            Some(&true)
        );
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        assert_eq!(
            transport.forward_member_return_metadata(
                &snapshot.metadata.facts(),
                output,
                free,
                member,
                &snapshot.metadata.slot_keys.iter().cloned().collect()
            ),
            Some(receipt)
        );
    });
}
#[test]
fn oc04_projected_member_output_has_a_separate_conditional_zero_receipt() {
    with_case(|facts, member, transport, meets| {
        let descendant = &member.fold.descendants[0];
        let output=meets.iter().find(|m|matches!(m.terminal.target,TerminalTarget::Output{node,..} if node==descendant.output)).unwrap();
        let receipt = super::fold_member_output::certify(facts, member, output)
            .expect("explicit projected-output zero obligation");
        assert_eq!(receipt.source, member.member);
        assert_eq!(receipt.call, member.fold.call);
        assert_eq!(receipt.guard, member.declaration.guard);
        assert_eq!(receipt.output, *output);
        assert_eq!(receipt.required_zero, descendant.output);
        assert_eq!(receipt.formal.var, descendant.formal_def);
        assert!(member.requirements.zero.contains(&receipt.required_zero));
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        assert_eq!(
            super::fold_member_output::certify_metadata(
                &snapshot.metadata.facts(),
                member,
                output,
                &snapshot.metadata.guard_aliases.iter().copied().collect(),
                &snapshot.metadata.slot_keys.iter().cloned().collect()
            ),
            Ok(receipt)
        );
        let source = super::transport::CandidateGraph::build(facts)
            .sources
            .into_iter()
            .find(|s| s.equation == member.member.endpoint)
            .unwrap();
        assert!(
            transport.meets_for(source.node).contains(output),
            "raw alternative is retained"
        );
    });
}

#[test]
fn oc04_member_forwarding_rejects_stale_endpoint_old_zero_and_wrong_member() {
    with_case(|facts, member, transport, meets| {
        let returned = member.fold.internal.packed_return.as_ref().unwrap().root;
        let output = meets
            .iter()
            .find(|m| matches!(m.terminal.target,TerminalTarget::Output{node,..} if node==returned))
            .unwrap();
        let free = meets
            .iter()
            .find(|m| matches!(m.terminal.target, TerminalTarget::Free(_)))
            .unwrap();
        let receipt = transport
            .forward_member_return(facts, output, free, member)
            .expect("positive member forwarding control");
        let TerminalTarget::Free(free_key) = free.terminal.target else { unreachable!() };
        let other = super::transport::CandidateGraph::build(facts)
            .sources
            .into_iter()
            .find(|s| s.equation == member.parent.endpoint)
            .unwrap()
            .node;
        for key in [free_key, member.member.endpoint] {
            let mut changed = facts.clone();
            let equation = changed
                .equations
                .iter_mut()
                .find(|e| e.point.construction == key.construction && e.ordinal == key.ordinal)
                .unwrap();
            assert_ne!(equation.variables[0], other.var);
            equation.variables[0] = other.var;
            assert!(equation.validate().is_ok());
            assert!(
                transport
                    .forward_member_return(&changed, output, free, member)
                    .is_none(),
                "stale endpoint {key:?}"
            );
        }
        let mut missing = facts.clone();
        let zero = receipt.forwarding.receiver_old_zero;
        missing
            .equations
            .retain(|e| (e.point.construction, e.ordinal) != (zero.construction, zero.ordinal));
        assert!(
            transport
                .forward_member_return(&missing, output, free, member)
                .is_none()
        );
        let mut wrong = member.clone();
        wrong.member = wrong.parent.clone();
        assert!(
            transport
                .forward_member_return(facts, output, free, &wrong)
                .is_none()
        );
        let projected=meets.iter().find(|m|matches!(m.terminal.target,TerminalTarget::Output{node,..} if node==member.fold.descendants[0].output)).unwrap();
        assert!(
            transport
                .forward_member_return(facts, projected, free, member)
                .is_none(),
            "a projected zero output is not an owned return"
        );
    });
}

#[test]
fn oc04_zero_receipt_rejects_owned_return_frees_and_changed_identities() {
    with_case(|facts, member, transport, meets| {
        use super::fold_member_output::{Hold, certify};
        let node = member.fold.descendants[0].output;
        let projected = meets
            .iter()
            .find(|m| matches!(m.terminal.target,TerminalTarget::Output{node:n,..} if n==node))
            .unwrap();
        for output in meets
            .iter()
            .filter(|m| !matches!(m.terminal.target,TerminalTarget::Output{node:n,..} if n==node))
        {
            assert_eq!(
                certify(facts, member, output),
                Err(Hold::NotProjectedOutput)
            );
        }
        let parent_node = super::transport::CandidateGraph::build(facts)
            .sources
            .into_iter()
            .find(|s| s.equation == member.parent.endpoint)
            .unwrap()
            .node;
        for free in transport
            .meets_for(parent_node)
            .iter()
            .filter(|m| matches!(m.terminal.target, TerminalTarget::Free(_)))
        {
            assert_eq!(certify(facts, member, free), Err(Hold::NotProjectedOutput));
        }
        let mut wrong = projected.clone();
        wrong.source = member.parent.clone();
        assert_eq!(certify(facts, member, &wrong), Err(Hold::Identity));
        let mut wrong = projected.clone();
        wrong.terminal.lineage = super::matched::SourceLineage::Exact(Vec::new());
        assert_eq!(certify(facts, member, &wrong), Err(Hold::Identity));
        let mut wrong = projected.clone();
        wrong.guards.insert(member.declaration.guard, false);
        assert_eq!(certify(facts, member, &wrong), Err(Hold::Identity));
    });
}

#[test]
fn oc04_zero_receipt_requires_current_zero_and_exit_dependencies() {
    with_case(|facts, member, _transport, meets| {
        use super::fold_member_output::{Hold, certify};
        let node = member.fold.descendants[0].output;
        let projected = meets
            .iter()
            .find(|m| matches!(m.terminal.target,TerminalTarget::Output{node:n,..} if n==node))
            .unwrap();
        let receipt = certify(facts, member, projected).unwrap();
        let mut wrong = member.clone();
        wrong.requirements.zero.retain(|n| *n != node);
        assert_eq!(certify(facts, &wrong, projected), Err(Hold::MissingZero));
        let mut wrong = member.clone();
        for action in &mut wrong.fold.internal.actions {
            action.zero_requirements.retain(|n| *n != node);
        }
        assert_eq!(certify(facts, &wrong, projected), Err(Hold::MissingZero));
        let mut missing = facts.clone();
        missing.equations.retain(|e| {
            (e.point.construction, e.ordinal)
                != (receipt.equality.construction, receipt.equality.ordinal)
        });
        assert_eq!(certify(&missing, member, projected), Err(Hold::Membership));
        let mut wrong = member.clone();
        wrong.parent = wrong.member.clone();
        assert_eq!(certify(facts, &wrong, projected), Err(Hold::Membership));
    });
}
