use ownership_fields::application::*;

use super::*;
#[test]
fn held_field_restores_input_and_removes_all_dependent_edits() {
    let source = "struct Holder { a: *mut i32, b: *mut i32 }";
    let first = source.find("*mut i32").unwrap();
    let second = source.rfind("*mut i32").unwrap();
    let edits = vec![
        SiteEdit {
            owner: ClassId::Field(field(0)),
            site: site(0),
            span: CapturedSpan {
                lo: first,
                hi: first + 8,
                text: "*mut i32".into(),
            },
            replacement: "Option<Box<i32>>".into(),
        },
        SiteEdit {
            owner: ClassId::Field(field(1)),
            site: site(1),
            span: CapturedSpan {
                lo: second,
                hi: second + 8,
                text: "*mut i32".into(),
            },
            replacement: "Option<Box<i32>>".into(),
        },
    ];
    let tx = vec![transaction(0), transaction(1)];
    let ready = apply_transactions(source, &tx, &edits).unwrap();
    assert_eq!(ready.applied_sites.len(), 2);
    let mut tx = tx;
    tx[0]
        .sites
        .insert(site(0), SiteState::Held("constructor".into()));
    let dependency = tx[0].id;
    tx[1].prerequisites.insert(dependency);
    let held = apply_transactions(source, &tx, &edits).unwrap();
    assert_eq!(held.text, source);
    assert!(held.applied_sites.is_empty());
}
#[test]
fn ready_without_edit_and_zero_syntax_with_edit_are_rejected() {
    assert_eq!(
        apply_transactions("x", &[transaction(0)], &[]),
        Err(ApplyHold::MissingEdit(ClassId::Field(field(0)), site(0)))
    );
    let mut tx = transaction(0);
    tx.sites.insert(site(0), SiteState::ZeroSyntax);
    let edit = SiteEdit {
        owner: tx.id,
        site: site(0),
        span: CapturedSpan {
            lo: 0,
            hi: 1,
            text: "x".into(),
        },
        replacement: "y".into(),
    };
    assert_eq!(
        apply_transactions("x", &[tx], &[edit]),
        Err(ApplyHold::ZeroSyntaxEdit(ClassId::Field(field(0)), site(0)))
    );
}
