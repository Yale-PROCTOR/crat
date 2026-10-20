use ownership_fields::{field_uses::*, struct_copy::*};

use super::*;
fn interface() -> StructInterface {
    StructInterface {
        terminal_fields: BTreeSet::from([field(0)]),
        field_types: BTreeMap::from([(field(0), "Option<Box<i32>>".into())]),
        lifetime_bounds: vec![],
        lifetimes: vec![],
        remove_copy_clone: true,
    }
}
pub(super) fn copy_site() -> CopySite {
    let k = key(0);
    let pointer = FieldSite {
        lifetime: None,
        field: field(0),
        key: k,
        terminal_type: "Option<Box<i32>>".into(),
        form: FieldForm::Owning {
            pointee: "i32".into(),
            optional: true,
        },
        place: "original.child".into(),
        access: StorageAccess::Exclusive,
        operation: FieldOperation::Take,
        role_proof: Some(k),
        view_proof: None,
        transfer_proof: Some(k),
    };
    CopySite {
        key: k,
        source: "original".into(),
        destination: "copied".into(),
        struct_name: "Holder".into(),
        all_fields: BTreeSet::from([field(0), field(1)]),
        members: vec![
            CopyMember::Pointer {
                name: "child".into(),
                site: pointer,
            },
            CopyMember::Scalar {
                field: field(1),
                name: "key".into(),
                expression: "original.key".into(),
                copy_proof: Some(k),
            },
        ],
        decision: Some(k),
        remaining_source_uses: BTreeSet::new(),
        rerouted_source_uses: BTreeSet::new(),
    }
}
#[test]
fn source_struct_copy_emits_one_owner_take_and_scalar_copy() {
    let plan = plan_struct_copy(&copy_site(), &interface()).unwrap();
    assert_eq!(
        plan.code,
        "let mut copied = Holder { child: (original.child).take(), key: original.key };"
    );
    let code = format!(
        "#[derive(Debug)]struct Holder{{child:Option<Box<i32>>,key:i32}}fn main(){{let mut original=Holder{{child:Some(Box::new(9)),key:4}};{}assert!(original.child.is_none());assert_eq!(copied.child.as_deref(),Some(&9));assert_eq!(copied.key,4);}}",
        plan.code
    );
    assert!(compile_source(&code, true).status.success());
}
#[test]
fn unadapted_remaining_source_use_and_omitted_scalar_field_hold() {
    let mut site = copy_site();
    site.remaining_source_uses.insert(super::site(8));
    assert_eq!(
        plan_struct_copy(&site, &interface()),
        Err(CopyHold::SourceUses)
    );
    site.rerouted_source_uses.insert(super::site(8));
    site.members.pop();
    assert_eq!(
        plan_struct_copy(&site, &interface()),
        Err(CopyHold::FieldInventory)
    );
}

#[test]
fn mixed_owning_and_held_raw_field_copy_preserves_the_raw_member() {
    let mut interface = interface();
    interface.field_types.insert(field(1), "*const i32".into());
    let mut site = copy_site();
    site.members[1] = CopyMember::Unchanged {
        field: field(1),
        name: "raw".into(),
        expression: "original.raw".into(),
        terminal_type: "*const i32".into(),
        copy_proof: Some(key(0)),
    };
    let plan = plan_struct_copy(&site, &interface).unwrap();
    assert_eq!(
        plan.code,
        "let mut copied = Holder { child: (original.child).take(), raw: original.raw };"
    );
    let code = format!(
        "struct Holder{{child:Option<Box<i32>>,raw:*const i32}}fn main(){{let n=7;let mut original=Holder{{child:Some(Box::new(3)),raw:&n}};{}assert_eq!(copied.raw,original.raw);assert!(original.child.is_none());}}",
        plan.code
    );
    assert!(compile_source(&code, true).status.success());
}
