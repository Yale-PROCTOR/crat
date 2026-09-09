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
