use ownership_fields::boundary::*;

use super::*;
fn callee_key(n: u32) -> EvidenceKey {
    let mut k = key(n);
    k.site.owner = OwnerId(2);
    k
}
fn owner_slot(k: EvidenceKey) -> SignatureSlot {
    SignatureSlot {
        key: k,
        ty: BoundaryType::Owner(OwnerType {
            pointee: "i32".into(),
            optional: true,
        }),
        grant: Some(grant(k)),
        borrow_origin: None,
    }
}
pub(super) fn signature() -> Signature {
    Signature {
        owner: OwnerId(2),
        parameters: vec![Parameter {
            index: 0,
            name: "buf".into(),
            slot: owner_slot(callee_key(0)),
        }],
        result: owner_slot(callee_key(1)),
    }
}
pub(super) fn contract() -> CallContract {
    CallContract {
        site: site(9),
        required_targets: BTreeSet::from([OwnerId(2)]),
        targets: vec![signature()],
        arguments: vec![ArgumentEdge {
            call_site: site(9),
            index: 0,
            actual: key(0),
            formal: callee_key(0),
            expression: "buf".into(),
            source_type: owner_slot(key(0)).ty,
            actual_grant: Some(grant(key(0))),
            mode: PassingMode::TakeOptionalStorage,
            transport: Some((key(0), callee_key(0))),
            borrow_proof: None,
            exclusive_storage: true,
            call_facts: Some(call_facts(key(0))),
        }],
    }
}
#[test]
fn owning_signature_and_caller_move_compile_as_a_returning_owner() {
    let signature = plan_signature(&signature()).unwrap();
    let call = plan_call(&contract()).unwrap();
    assert!(signature.lifetimes.is_empty());
    assert_eq!(call.arguments, ["(buf).take()"]);
    let code = format!(
        "fn pass({})->{}{{buf}} fn main(){{let mut buf=Some(Box::new(7_i32));let received=pass({});assert!(buf.is_none());assert_eq!(received.as_deref(),Some(&7));}}",
        signature.parameters.join(","),
        signature.result,
        call.arguments.join(",")
    );
    assert!(compile_source(&code, true).status.success());
}
#[test]
fn incomplete_target_inventory_and_wrong_formal_identity_hold() {
    let mut c = contract();
    c.required_targets.insert(OwnerId(3));
    assert_eq!(plan_call(&c), Err(BoundaryHold::TargetSet));
    c.required_targets.remove(&OwnerId(3));
    c.arguments[0].formal = callee_key(8);
    assert_eq!(plan_call(&c), Err(BoundaryHold::Transfer));
}
#[test]
fn owning_return_has_no_borrow_origin_but_a_borrowed_return_requires_one() {
    let mut s = signature();
    assert!(plan_signature(&s).is_ok());
    s.result.ty = BoundaryType::Borrow {
        pointee: "i32".into(),
        mutable: false,
        optional: true,
        lifetime: "a".into(),
    };
    s.result.grant.as_mut().unwrap().kind = Kind::Ref;
    assert_eq!(plan_signature(&s), Err(BoundaryHold::BorrowOrigin));
}

#[test]
fn scalar_hoist_composes_with_actual_take_argument_plan() {
    let mut c = contract();
    c.site = site(9);
    c.arguments[0].expression = "root.right".into();
    let scalar_key = callee_key(2);
    c.targets[0].parameters.push(Parameter {
        index: 1,
        name: "key".into(),
        slot: SignatureSlot {
            key: scalar_key,
            ty: BoundaryType::Scalar("i32".into()),
            grant: None,
            borrow_origin: None,
        },
    });
    c.arguments.push(ArgumentEdge {
        call_site: site(9),
        index: 1,
        actual: key(1),
        formal: scalar_key,
        expression: "temp_1.key".into(),
        source_type: BoundaryType::Scalar("i32".into()),
        actual_grant: None,
        mode: PassingMode::Scalar,
        transport: Some((key(1), scalar_key)),
        borrow_proof: None,
        exclusive_storage: false,
        call_facts: None,
    });
    let witness = HoistWitness {
        call: site(9),
        read: key(1),
        consume: key(0),
        original_order: vec![site(0), site(1)],
        scalar_effect_free_nontrapping: true,
        callee_commutes: true,
        commutes_with: BTreeSet::from([site(0)]),
        no_independent_protector: true,
    };
    let plan = plan_hoisted_call(&c, &witness, &BTreeSet::new()).unwrap();
    assert_eq!(plan.binding, "let __crat_scalar = temp_1.key;");
    assert_eq!(
        plan.call.arguments,
        ["(root.right).take()", "__crat_scalar"]
    );
}

#[test]
fn owning_return_moves_or_takes_without_borrow_lifetime_or_local_allocation() {
    let source = owner_slot(callee_key(0));
    let result = owner_slot(callee_key(1));
    let mut edge = ReturnEdge {
        source,
        result,
        expression: "node.child".into(),
        take_optional_storage: true,
        exclusive_storage: true,
        transport: Some((callee_key(0), callee_key(1))),
    };
    assert_eq!(plan_return(&edge).unwrap(), "return (node.child).take();");
    edge.take_optional_storage = false;
    edge.expression = "buf".into();
    assert_eq!(plan_return(&edge).unwrap(), "return buf;");
    edge.transport = None;
    assert_eq!(plan_return(&edge), Err(BoundaryHold::Transfer));
}

#[test]
fn call_certificate_is_not_reusable_at_another_invocation() {
    let mut c = contract();
    c.site.occurrence += 1;
    assert_eq!(plan_call(&c), Err(BoundaryHold::Call));
}

#[test]
fn indirect_scalar_targets_must_share_actual_identity_and_frame() {
    let scalar = |k| SignatureSlot {
        key: k,
        ty: BoundaryType::Scalar("i32".into()),
        grant: None,
        borrow_origin: None,
    };
    let target = Signature {
        owner: OwnerId(2),
        parameters: vec![Parameter {
            index: 0,
            name: "n".into(),
            slot: scalar(callee_key(0)),
        }],
        result: scalar(callee_key(1)),
    };
    let edge = ArgumentEdge {
        call_site: site(9),
        index: 0,
        actual: key(0),
        formal: callee_key(0),
        expression: "n".into(),
        source_type: BoundaryType::Scalar("i32".into()),
        actual_grant: None,
        mode: PassingMode::Scalar,
        transport: Some((key(0), callee_key(0))),
        borrow_proof: None,
        exclusive_storage: false,
        call_facts: None,
    };
    let mut other = target.clone();
    other.owner = OwnerId(3);
    other.parameters[0].slot.key.site.owner = other.owner;
    other.result.key.site.owner = other.owner;
    let mut other_edge = edge.clone();
    other_edge.formal = other.parameters[0].slot.key;
    other_edge.actual = key(1);
    other_edge.transport = Some((other_edge.actual, other_edge.formal));
    let c = CallContract {
        site: site(9),
        required_targets: BTreeSet::from([OwnerId(2), OwnerId(3)]),
        targets: vec![target, other],
        arguments: vec![edge, other_edge],
    };
    assert_eq!(plan_call(&c), Err(BoundaryHold::TargetSet));
}

#[test]
fn duplicate_consuming_arguments_cannot_create_two_responsibilities() {
    let mut c = contract();
    let mut second = c.targets[0].parameters[0].clone();
    second.index = 1;
    second.name = "other".into();
    second.slot.key = callee_key(3);
    second.slot.grant = Some(grant(callee_key(3)));
    c.targets[0].parameters.push(second);
    let mut edge = c.arguments[0].clone();
    edge.index = 1;
    edge.formal = callee_key(3);
    edge.transport = Some((edge.actual, edge.formal));
    c.arguments.push(edge);
    assert_eq!(plan_call(&c), Err(BoundaryHold::DuplicateOwner));
}
#[test]
fn uniform_indirect_targets_share_one_actual_inventory() {
    let mut c = contract();
    let mut other = c.targets[0].clone();
    other.owner = OwnerId(3);
    for slot in [&mut other.parameters[0].slot, &mut other.result] {
        slot.key.site.owner = OwnerId(3);
        slot.grant = Some(grant(slot.key));
    }
    let mut edge = c.arguments[0].clone();
    edge.formal = other.parameters[0].slot.key;
    edge.transport = Some((edge.actual, edge.formal));
    c.arguments.push(edge);
    c.targets.push(other);
    c.required_targets.insert(OwnerId(3));
    assert!(plan_call(&c).is_ok());
}
#[test]
fn mutable_borrow_aliases_need_a_pair_witness_before_emission() {
    let mut c = contract();
    let ty = BoundaryType::Borrow {
        pointee: "i32".into(),
        mutable: true,
        optional: true,
        lifetime: "a".into(),
    };
    c.targets[0].parameters[0].slot.ty = ty.clone();
    c.targets[0].parameters[0].slot.grant.as_mut().unwrap().kind = Kind::Ref;
    c.targets[0].parameters[0].slot.borrow_origin = Some(callee_key(0));
    c.arguments[0].mode = PassingMode::BorrowMutable;
    c.arguments[0].borrow_proof = Some(key(0));
    let mut second = c.targets[0].parameters[0].clone();
    second.index = 1;
    second.name = "other".into();
    second.slot.key = callee_key(3);
    let mut g = grant(callee_key(3));
    g.kind = Kind::Ref;
    second.slot.grant = Some(g);
    second.slot.borrow_origin = Some(callee_key(3));
    c.targets[0].parameters.push(second);
    let mut edge = c.arguments[0].clone();
    edge.index = 1;
    edge.formal = callee_key(3);
    edge.transport = Some((edge.actual, edge.formal));
    c.arguments.push(edge);
    assert!(plan_call(&c).is_err());
}
