use ownership_fields::free_sites::*;

use super::*;
fn free_site(n: u32, expression: &str) -> FreeSite {
    FreeSite {
        sink: key(n),
        owner: key(n + 10),
        expression: expression.into(),
        optional_storage: true,
        casts: vec![CastKind::IdentityPointer, CastKind::PointerToVoid],
        exact_owner_relation: Some((key(n + 10), key(n))),
        allocation_base: Some(key(n)),
        allocator_layout: Some(key(n)),
        grant: grant(key(n)),
        call: call_facts(key(n)),
    }
}
#[test]
fn free_sites_match_by_identity_when_input_order_is_reversed() {
    let plans = plan_frees(
        &BTreeSet::from([key(1), key(2)]),
        &[free_site(2, "second"), free_site(1, "first")],
    )
    .unwrap();
    assert_eq!(plans[&key(1)].code, "drop((first).take());");
    assert_eq!(plans[&key(2)].code, "drop((second).take());");
}
#[test]
fn missing_duplicate_cast_and_wrong_owner_are_distinct_holds() {
    let expected = BTreeSet::from([key(1)]);
    assert_eq!(plan_frees(&expected, &[]), Err(FreeHold::Missing(key(1))));
    let good = free_site(1, "owner");
    assert_eq!(
        plan_frees(&expected, &[good.clone(), good.clone()]),
        Err(FreeHold::Duplicate(key(1)))
    );
    let mut bad = good.clone();
    bad.casts.push(CastKind::InteriorPointer);
    assert_eq!(plan_frees(&expected, &[bad]), Err(FreeHold::Cast));
    let mut bad = good;
    bad.owner.generation = 999;
    assert_eq!(plan_frees(&expected, &[bad]), Err(FreeHold::OwnerIdentity));
}
