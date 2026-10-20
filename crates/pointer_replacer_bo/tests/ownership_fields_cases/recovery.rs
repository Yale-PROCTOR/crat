use ownership_fields::{application::SiteEdit, recovery::*};

use super::*;
fn revision(n: u32, version: u32, at: u32, replacement: &str) -> Revision {
    let class = ClassId::Field(field(n));
    Revision {
        id: RevisionId {
            class,
            revision: version,
        },
        introduced_at: at,
        required: BTreeSet::new(),
        sites: BTreeMap::from([(site(n), SiteState::Ready)]),
        edits: vec![SiteEdit {
            owner: class,
            site: site(n),
            span: CapturedSpan {
                lo: n as usize,
                hi: n as usize + 1,
                text: if n == 0 { "x" } else { "y" }.into(),
            },
            replacement: replacement.into(),
        }],
    }
}
fn set(revisions: Vec<Revision>) -> RevisionSet {
    RevisionSet {
        model: [1; 32],
        configuration: [2; 32],
        revisions,
    }
}
#[test]
fn incomplete_new_field_preserves_predecessor_and_independent_gain() {
    let old = revision(0, 0, 0, "A");
    let mut incomplete = revision(0, 1, 1, "new");
    incomplete.edits.clear();
    let result = recover(
        "xy",
        &set(vec![old.clone()]),
        &set(vec![incomplete, revision(1, 1, 1, "B")]),
    )
    .unwrap();
    assert_eq!(result.text, "AB");
    assert_eq!(result.selected[&old.id.class], old.id);
}
#[test]
fn a_previous_interface_dependency_can_force_new_neighbor_to_yield() {
    let a = revision(0, 0, 0, "A");
    let mut b = revision(1, 0, 0, "B");
    b.required.insert(a.id);
    let result = recover(
        "xy",
        &set(vec![a.clone(), b]),
        &set(vec![revision(0, 1, 1, "new")]),
    )
    .unwrap();
    assert_eq!(result.text, "AB");
    assert_eq!(result.selected[&a.id.class], a.id);
}
#[test]
fn newer_colliding_family_yields_without_removing_earlier_delivery() {
    let old = revision(0, 0, 0, "A");
    let mut new = revision(1, 1, 1, "new");
    new.edits[0].span = old.edits[0].span.clone();
    let result = recover("xy", &set(vec![old]), &set(vec![new])).unwrap();
    assert_eq!(result.text, "Ay");
    assert!(!result.selected.contains_key(&ClassId::Field(field(1))));
}
