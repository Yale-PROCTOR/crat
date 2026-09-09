use super::*;
fn contract() -> AggregateLeakContract {
    AggregateLeakContract {
        coverage: leak_coverage(key(0)),
        owner: OwnerId(1),
        type_name: "Holder".into(),
        all_owning_fields: BTreeSet::from([field(0)]),
        fields: vec![AggregateField {
            field: field(0),
            name: "child".into(),
            ty: OwnerType {
                pointee: "i32".into(),
                optional: true,
            },
            generation: key(1),
        }],
        field_inventory: Some(key(0)),
        no_user_drop: Some(key(0)),
        helper_lowering: Some(key(0)),
    }
}
#[test]
fn aggregate_wrapper_keeps_option_box_field_type_and_explicit_free() {
    let (mut aggregate, init) =
        leak_aggregate(&contract(), "holder", "Holder{child:Some(Box::new(3))}").unwrap();
    let permit = admit_call(&grant(key(1)), &call_facts(key(1))).unwrap();
    let free = aggregate
        .free_field(field(0), &permit, key(1), Some(key(1)))
        .unwrap();
    let code = format!(
        "struct Holder{{child:Option<Box<i32>>}}fn main(){{{}{}assert!(holder.child.is_none());}}",
        init.code, free.code
    );
    assert!(compile_source(&code, true).status.success());
    assert_eq!(
        aggregate.free_field(field(0), &permit, key(1), Some(key(1))),
        Err(EmitHold::SinkIdentity)
    );
}
#[test]
fn aggregate_with_missing_field_or_user_destructor_cannot_suppress_glue() {
    let mut c = contract();
    c.fields.clear();
    assert!(matches!(
        leak_aggregate(&c, "holder", "make()"),
        Err(EmitHold::MissingEvidence("aggregate-fields"))
    ));
    c = contract();
    c.no_user_drop = None;
    assert!(matches!(
        leak_aggregate(&c, "holder", "make()"),
        Err(EmitHold::MissingEvidence("aggregate-drop-effects"))
    ));
}

#[test]
fn aggregate_overwrite_replaces_field_generation_inventory_without_dropping_old() {
    let c = contract();
    let (mut aggregate, init) =
        leak_aggregate(&c, "holder", "Holder{child:Some(Box::new(3))}").unwrap();
    let old = ClosePlan::LeakRecursive {
        key: key(0),
        kind: CloseKind::Overwrite,
    };
    let mut new = contract();
    let mut k = key(0);
    k.generation = 4;
    new.coverage = leak_coverage(k);
    new.field_inventory = Some(k);
    new.no_user_drop = Some(k);
    new.helper_lowering = Some(k);
    new.fields[0].generation.generation = 4;
    let assignment = aggregate
        .overwrite(&old, &new, "Holder{child:Some(Box::new(7))}")
        .unwrap();
    let old_permit = admit_call(&grant(key(1)), &call_facts(key(1))).unwrap();
    assert_eq!(
        aggregate.free_field(field(0), &old_permit, key(1), Some(key(1))),
        Err(EmitHold::SinkIdentity)
    );
    let code = format!(
        "struct Holder{{child:Option<Box<i32>>}}fn main(){{{}{}assert_eq!(holder.child.as_deref(),Some(&7));}}",
        init.code, assignment.code
    );
    assert!(compile_source(&code, true).status.success());
}
