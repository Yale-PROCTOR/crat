//! Caller equation coverage for the strict three-allocation detach witness.
use std::collections::BTreeSet;

use super::{facts::EquationId, fold_member_output_tests::with_case, matched::TerminalTarget};
#[test]
fn oc05_three_source_law_plan_keeps_parent_leaf_and_holder_distinct() {
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
        let projected=meets.iter().find(|m|matches!(m.terminal.target,TerminalTarget::Output{node,..} if node==member.fold.descendants[0].output)).unwrap();
        let forwarding = transport
            .forward_member_return(facts, output, free, member)
            .unwrap();
        let zero = super::fold_member_output::certify(facts, member, projected).unwrap();
        let plan = super::fold_member_laws::audit(facts, member, &forwarding, &zero)
            .expect("complete three-source caller law plan");
        let graph = super::transport::CandidateGraph::build(facts);
        assert_eq!(plan.routes.len(), 3);
        assert_eq!(
            plan.routes
                .iter()
                .map(|r| r.source.endpoint)
                .collect::<BTreeSet<_>>(),
            graph.sources.iter().map(|s| s.equation).collect()
        );
        assert_eq!(
            plan.routes.iter().map(|r| r.free).collect::<BTreeSet<_>>(),
            graph.sinks.iter().map(|s| s.equation).collect()
        );
        let parent = plan
            .routes
            .iter()
            .find(|r| r.source == member.parent)
            .unwrap();
        let leaf = plan
            .routes
            .iter()
            .find(|r| r.source == member.member)
            .unwrap();
        assert_eq!(parent.target, member.fold.actual_before);
        assert_eq!(
            graph
                .sinks
                .iter()
                .find(|s| s.equation == parent.free)
                .unwrap()
                .endpoint
                .function,
            member.fold.call.callee
        );
        assert!(!parent.owning.contains(&member.fold.receiver));
        assert!(
            leaf.owning.contains(&member.member_before)
                && leaf.owning.contains(&member.fold.receiver)
        );
        for (i, route) in plan.routes.iter().enumerate() {
            let nodes: BTreeSet<_> = route.owning.iter().copied().collect();
            for other in &plan.routes[i + 1..] {
                assert!(nodes.is_disjoint(&other.owning.iter().copied().collect()));
            }
        }
        let descendant = &member.fold.descendants[0];
        let input = super::transport::Node {
            construction: member.fold.call.construction,
            var: descendant.formal_use,
        };
        let after = super::transport::Node {
            construction: member.fold.call.construction,
            var: descendant.formal_def,
        };
        assert!(plan.laws.owning.contains(&input) && plan.laws.owning.contains(&descendant.input));
        assert!(!plan.laws.zero.contains(&input) && !plan.laws.zero.contains(&descendant.input));
        assert!(plan.laws.zero.contains(&after) && plan.laws.zero.contains(&descendant.output));
        assert!(plan.laws.zero.contains(&member.member_after));
        let expected: BTreeSet<_> = facts
            .equations
            .iter()
            .filter(|e| {
                e.point.construction == member.fold.call.construction
                    && e.point.function.as_ref() == Some(&member.fold.call.caller)
            })
            .map(|e| EquationId {
                construction: e.point.construction,
                ordinal: e.ordinal,
            })
            .collect();
        assert_eq!(
            plan.laws.equations.iter().copied().collect::<BTreeSet<_>>(),
            expected
        );
        for endpoint in graph.sources.iter().chain(&graph.sinks) {
            assert!(plan.laws.guards.contains(&(endpoint.equation, true)));
        }
    });
}

#[test]
fn oc05_rejects_a_foreign_bridge_a_missing_old_zero_and_a_wrong_zero_receipt() {
    use super::{fold_caller::Hold, fold_member_laws::audit};
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
        let projected=meets.iter().find(|m|matches!(m.terminal.target,TerminalTarget::Output{node,..} if node==member.fold.descendants[0].output)).unwrap();
        let forwarding = transport
            .forward_member_return(facts, output, free, member)
            .unwrap();
        let zero = super::fold_member_output::certify(facts, member, projected).unwrap();
        audit(facts, member, &forwarding, &zero).expect("positive control");

        // The bridge is only the one OC04 authenticated for THIS member.
        let mut foreign = forwarding.clone();
        let mut swapped = member.clone();
        swapped.parent = swapped.member.clone();
        foreign.membership = Box::new(swapped);
        assert_eq!(
            audit(facts, member, &foreign, &zero),
            Err(Hold::Forwarding),
            "another member's forwarding is not this member's bridge"
        );
        let mut elsewhere = forwarding.clone();
        elsewhere.forwarding.receiver = member.member_before;
        assert_eq!(
            audit(facts, member, &elsewhere, &zero),
            Err(Hold::Forwarding),
            "a bridge that does not land in the fold's receiver is not a bridge"
        );

        // The member copy's old-zero is a premise, never an assumption.
        let child = facts
            .equations
            .iter()
            .find(|e| {
                e.point.construction == member.child_transfer.construction
                    && e.ordinal == member.child_transfer.ordinal
            })
            .unwrap()
            .transfer
            .clone();
        assert!(child.is_some());
        let mut missing = facts.clone();
        missing
            .equations
            .retain(|e| !(e.operation == "assume" && e.transfer == child));
        assert_eq!(
            audit(&missing, member, &forwarding, &zero),
            Err(Hold::LawCoverage),
            "the member copy without its old-zero is not a law"
        );

        // The zero receipt must name the projected parameter-output, never the
        // owned return and never the receiver.
        let mut wrong = zero.clone();
        wrong.required_zero = member.fold.receiver;
        assert_eq!(
            audit(facts, member, &forwarding, &wrong),
            Err(Hold::Forwarding)
        );
        let mut wrong = zero.clone();
        wrong.formal = member.member_before;
        assert_eq!(
            audit(facts, member, &forwarding, &wrong),
            Err(Hold::Forwarding)
        );
    });
}
