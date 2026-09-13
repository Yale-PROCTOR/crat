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
    assert_eq!(
        plan_frees::<FreeSite>(&expected, &[]),
        Err(FreeHold::Missing(key(1)))
    );
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

/// Invented source keys exercise the common join without generation evidence.
/// The real native adapter supplies compiler-derived identities and validates
/// all proofs; this test adapter is not a native positive-admission witness.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct SourceKey {
    function: String,
    offset: u32,
}
#[derive(Clone)]
struct SourceSite {
    key: SourceKey,
    code: String,
    permitted: bool,
}
#[derive(Debug, PartialEq, Eq)]
enum SourceHold {
    Missing(SourceKey),
    Extra(SourceKey),
    Duplicate(SourceKey),
    Unproved(SourceKey),
}
impl FreePlanSite for SourceSite {
    type Emitted = (SourceKey, String);
    type Hold = SourceHold;
    type Key = SourceKey;

    fn key(&self) -> &SourceKey {
        &self.key
    }

    fn missing(key: SourceKey) -> SourceHold {
        SourceHold::Missing(key)
    }

    fn extra(key: SourceKey) -> SourceHold {
        SourceHold::Extra(key)
    }

    fn duplicate(key: SourceKey) -> SourceHold {
        SourceHold::Duplicate(key)
    }

    fn plan(&self) -> Result<Self::Emitted, SourceHold> {
        if !self.permitted {
            return Err(SourceHold::Unproved(self.key.clone()));
        }
        Ok((self.key.clone(), self.code.clone()))
    }
}
fn source_site(offset: u32) -> SourceSite {
    SourceSite {
        key: SourceKey {
            function: "synthetic_source".into(),
            offset,
        },
        code: format!("drop(owner_at_{offset});"),
        permitted: true,
    }
}

#[test]
fn source_free_keys_project_by_identity_without_generation() {
    let first = source_site(10);
    let second = source_site(20);
    let expected = BTreeSet::from([first.key.clone(), second.key.clone()]);
    let plans = plan_frees(&expected, &[second.clone(), first.clone()]).unwrap();
    assert_eq!(plans[&first.key], (first.key.clone(), first.code));
    assert_eq!(plans[&second.key], (second.key.clone(), second.code));
    assert_eq!(plans.keys().cloned().collect::<BTreeSet<_>>(), expected);
}

#[test]
fn source_free_inventory_holds_precede_per_site_planning() {
    let mut first = source_site(10);
    first.permitted = false;
    let second = source_site(20);
    let expected = BTreeSet::from([first.key.clone(), second.key.clone()]);
    assert_eq!(
        plan_frees(&expected, &[first.clone()]),
        Err(SourceHold::Missing(second.key.clone()))
    );
    assert_eq!(
        plan_frees(&expected, &[first.clone(), first.clone()]),
        Err(SourceHold::Duplicate(first.key.clone()))
    );
    let expected = BTreeSet::from([first.key.clone()]);
    assert_eq!(
        plan_frees(&expected, &[first, second.clone()]),
        Err(SourceHold::Extra(second.key))
    );
}

#[test]
fn source_free_complete_inventory_does_not_authorize_an_unproved_site() {
    let mut site = source_site(10);
    site.permitted = false;
    let expected = BTreeSet::from([site.key.clone()]);
    assert_eq!(
        plan_frees(&expected, &[site.clone()]),
        Err(SourceHold::Unproved(site.key))
    );
}
