use ownership_fields::drop_depth::*;

use super::*;
fn certificate() -> ValueCertificate {
    ValueCertificate {
        key: key(0),
        kind: CloseKind::ScopeExit,
        payload: OwnerId(1),
        graph_revision: [3; 32],
        root: 3,
        nodes: BTreeMap::from([
            (
                3,
                ValueNode {
                    payload: OwnerId(1),
                    children: vec![Some(4)],
                },
            ),
            (
                4,
                ValueNode {
                    payload: OwnerId(1),
                    children: vec![None],
                },
            ),
        ]),
        completeness: Some(key(0)),
    }
}
fn budget() -> StackBudget {
    StackBudget {
        key: key(0),
        kind: CloseKind::ScopeExit,
        payload: OwnerId(1),
        graph_revision: [3; 32],
        admitted_depth: 2,
        lowering_evidence: Some(key(0)),
    }
}
#[test]
fn finite_recursive_value_certificate_supplies_measured_depth_to_close() {
    let witness = depth_witness(&certificate(), &value_graph(), &budget()).unwrap();
    assert_eq!(witness.maximum_depth, 2);
    assert!(matches!(
        implicit_close(
            key(0),
            CloseKind::ScopeExit,
            OwnerId(1),
            &value_graph(),
            [3; 32],
            Some(&witness),
            &proofs(key(0))
        ),
        Ok(ClosePlan::Drop { .. })
    ));
    let mut small = budget();
    small.admitted_depth = 1;
    let witness = depth_witness(&certificate(), &value_graph(), &small).unwrap();
    assert!(matches!(
        implicit_close(
            key(0),
            CloseKind::ScopeExit,
            OwnerId(1),
            &value_graph(),
            [3; 32],
            Some(&witness),
            &proofs(key(0))
        ),
        Ok(ClosePlan::LeakRecursive { .. })
    ));
}
#[test]
fn incomplete_cycle_and_wrong_configuration_do_not_supply_depth() {
    let mut c = certificate();
    c.nodes.remove(&4);
    assert!(matches!(
        depth_witness(&c, &value_graph(), &budget()),
        Err(DepthHold::MissingNode(4))
    ));
    c = certificate();
    c.nodes.get_mut(&4).unwrap().children = vec![Some(3)];
    assert!(matches!(
        depth_witness(&c, &value_graph(), &budget()),
        Err(DepthHold::RepeatedOwner(3))
    ));
    let mut b = budget();
    b.key.configuration = [9; 32];
    assert!(matches!(
        depth_witness(&certificate(), &value_graph(), &b),
        Err(DepthHold::Budget)
    ));
}

#[test]
fn absent_mandatory_owning_child_cannot_shorten_a_depth_certificate() {
    let c = certificate();
    assert_eq!(
        depth_witness(&c, &recursive_graph(), &budget()).map(|w| w.maximum_depth),
        Err(DepthHold::ChildInventory(4))
    );
}

fn value_graph() -> BTreeMap<OwnerId, DropShape> {
    BTreeMap::from([(
        OwnerId(1),
        DropShape::OwnedFields(vec![DropEdge {
            payload: OwnerId(1),
            optional: true,
        }]),
    )])
}

#[test]
fn proven_none_has_zero_drop_depth_but_possible_nullability_is_insufficient() {
    let witness = empty_owner_depth(
        key(0),
        CloseKind::ScopeExit,
        OwnerId(1),
        &value_graph(),
        [3; 32],
        Some(key(0)),
        &budget(),
    )
    .unwrap();
    assert_eq!(witness.maximum_depth, 0);
    assert!(matches!(
        implicit_close(
            key(0),
            CloseKind::ScopeExit,
            OwnerId(1),
            &value_graph(),
            [3; 32],
            Some(&witness),
            &proofs(key(0))
        ),
        Ok(ClosePlan::Drop { .. })
    ));
    assert!(
        empty_owner_depth(
            key(0),
            CloseKind::ScopeExit,
            OwnerId(1),
            &value_graph(),
            [3; 32],
            None,
            &budget()
        )
        .is_err()
    );
}
