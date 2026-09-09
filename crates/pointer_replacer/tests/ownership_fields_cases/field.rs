use ownership_fields::field_uses::*;

use super::*;
pub(super) fn interface() -> StructInterface {
    StructInterface {
        terminal_fields: BTreeSet::from([field(0)]),
        field_types: BTreeMap::from([(field(0), "Option<Box<i32>>".into())]),
        lifetime_bounds: vec![],
        lifetimes: vec![],
        remove_copy_clone: true,
    }
}
pub(super) fn use_site(operation: FieldOperation) -> FieldSite {
    let k = key(0);
    FieldSite {
        lifetime: None,
        field: field(0),
        key: k,
        terminal_type: "Option<Box<i32>>".into(),
        form: FieldForm::Owning {
            pointee: "i32".into(),
            optional: true,
        },
        place: "holder.child".into(),
        access: StorageAccess::Exclusive,
        operation,
        role_proof: Some(k),
        view_proof: Some(k),
        transfer_proof: Some(k),
    }
}
#[test]
fn owner_field_read_borrows_and_transfer_takes_without_cloning() {
    let read = plan_field_use(&use_site(FieldOperation::ReadShared), &interface()).unwrap();
    let take = plan_field_use(&use_site(FieldOperation::Take), &interface()).unwrap();
    assert_eq!(read.code, "(holder.child).as_deref()");
    assert_eq!(take.code, "(holder.child).take()");
    let code = format!(
        "struct Holder{{child:Option<Box<i32>>}} fn main(){{let mut holder=Holder{{child:Some(Box::new(9))}};assert_eq!({},Some(&9));let child={};assert!(holder.child.is_none());assert_eq!(child.as_deref(),Some(&9));}}",
        read.code, take.code
    );
    assert!(compile_source(&code, true).status.success());
}
#[test]
fn shared_storage_and_wrong_role_cannot_consume_an_owning_field() {
    let mut site = use_site(FieldOperation::Take);
    site.access = StorageAccess::Shared;
    assert_eq!(plan_field_use(&site, &interface()), Err(FieldHold::Storage));
    site.access = StorageAccess::Exclusive;
    site.transfer_proof = None;
    assert_eq!(
        plan_field_use(&site, &interface()),
        Err(FieldHold::Transfer)
    );
}
#[test]
fn store_requires_same_generation_frame_matching_type_and_empty_cell() {
    let input = FieldOperation::Store {
        value: "child".into(),
        source: key(1),
        source_type: "Option<Box<i32>>".into(),
        empty_destination: Some(key(0)),
    };
    let plan = plan_field_use(&use_site(input.clone()), &interface()).unwrap();
    assert_eq!(plan.code, "holder.child = child;");
    let mut site = use_site(input);
    if let FieldOperation::Store {
        empty_destination, ..
    } = &mut site.operation
    {
        *empty_destination = None;
    }
    assert_eq!(
        plan_field_use(&site, &interface()),
        Err(FieldHold::NonEmptyDestination)
    );
}
#[test]
fn omitted_field_use_cannot_make_a_complete_transaction() {
    let required = BTreeSet::from([site(0), site(1)]);
    assert!(
        matches!(checked_transaction(ClassId::Field(field(0)),BTreeSet::new(),&required,BTreeMap::from([(site(0),SiteState::Ready)])),Err(FieldHold::MissingSite(s)) if s==site(1))
    );
}

#[test]
fn field_lifetime_relations_emit_only_justified_groups_and_bounds() {
    let fields: Vec<_> = (0..3)
        .map(|n| Field {
            id: field(n),
            name: format!("p{n}"),
            input_type: "*const i32".into(),
            candidate: FieldForm::Borrow {
                pointee: "i32".into(),
                mutable: false,
                optional: false,
            },
        })
        .collect();
    let tx = vec![transaction(0), transaction(1), transaction(2)];
    let terminal = finalize(&tx).unwrap();
    let relations = LifetimeRelations {
        equal: vec![(field(0), field(1))],
        outlives: vec![(field(1), field(2))],
    };
    let interface = struct_interface_with_relations(
        OwnerId(1),
        &fields,
        &BTreeSet::new(),
        &CopyContract::Absent,
        &tx,
        &terminal,
        &relations,
    )
    .unwrap();
    assert_eq!(
        interface.field_types[&field(0)],
        interface.field_types[&field(1)]
    );
    assert_eq!(interface.lifetimes, ["__crat_f0", "__crat_f2"]);
    assert_eq!(
        interface.lifetime_bounds,
        vec![("__crat_f0".into(), "__crat_f2".into())]
    );
}

#[test]
fn borrow_label_cannot_bypass_owning_destination_close_check() {
    let mut site = use_site(FieldOperation::Store {
        value: "replacement".into(),
        source: key(1),
        source_type: "Option<Box<i32>>".into(),
        empty_destination: None,
    });
    site.form = FieldForm::Borrow {
        pointee: "i32".into(),
        mutable: true,
        optional: true,
    };
    assert_eq!(
        plan_field_use(&site, &interface()),
        Err(FieldHold::Interface)
    );
}

#[test]
fn declaration_emits_required_lifetime_bounds_in_its_parameter_list() {
    let source = "struct Pair { first: *const i32, second: *const i32 }";
    let first = source.find("*const i32").unwrap();
    let second = source.rfind("*const i32").unwrap();
    let at = source.find(" {").unwrap();
    let declaration = Declaration {
        owner: OwnerId(1),
        fields: BTreeMap::from([
            (
                field(0),
                CapturedSpan {
                    lo: first,
                    hi: first + 10,
                    text: "*const i32".into(),
                },
            ),
            (
                field(1),
                CapturedSpan {
                    lo: second,
                    hi: second + 10,
                    text: "*const i32".into(),
                },
            ),
        ]),
        generics: GenericSite {
            span: CapturedSpan {
                lo: at,
                hi: at,
                text: String::new(),
            },
            parameters: vec![],
        },
        derives: vec![],
    };
    let interface = StructInterface {
        terminal_fields: BTreeSet::from([field(0), field(1)]),
        field_types: BTreeMap::from([(field(0), "&'a i32".into()), (field(1), "&'b i32".into())]),
        lifetimes: vec!["a".into(), "b".into()],
        lifetime_bounds: vec![("a".into(), "b".into())],
        remove_copy_clone: false,
    };
    let rendered = render_declaration(source, &declaration, &interface).unwrap();
    assert!(rendered.contains("<'a: 'b, 'b>"), "{rendered}");
    assert!(
        compile_source(&format!("{rendered} fn main(){{}}"), false)
            .status
            .success()
    );
}

#[test]
fn custody_rejects_a_dropped_generated_lifetime_bound() {
    let interface = StructInterface {
        terminal_fields: BTreeSet::from([field(0)]),
        field_types: BTreeMap::from([(field(0), "&'a i32".into())]),
        lifetimes: vec!["a".into(), "b".into()],
        lifetime_bounds: vec![("a".into(), "b".into())],
        remove_copy_clone: false,
    };
    let observed = Observation {
        introduced_bounds: vec![],
        source_hash: [7; 32],
        field_types: interface.field_types.clone(),
        lifetimes: interface.lifetimes.clone(),
        has_copy_clone: false,
    };
    assert_eq!(
        check_fields(
            &[],
            [7; 32],
            &interface,
            &finalize(&[transaction(0)]).unwrap(),
            &BTreeSet::from([field(0)]),
            &observed
        ),
        Err(CustodyError::Lifetimes)
    );
}
