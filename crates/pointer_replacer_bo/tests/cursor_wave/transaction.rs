use std::collections::{BTreeMap, BTreeSet};

use super::cursor::transaction::{Class, ClassHold, Obligation, Rendering, SourceForm, Terminal};

fn class() -> Class<u32> {
    Class {
        owner: 1,
        base_owner: 1,
        dependencies: vec![2],
        obligations: vec![
            Obligation {
                site: 10,
                source_owner: 3,
                placed_template: Some(100),
                input_template: Some(101),
            },
            // Includes a zero-syntax copy site, even with no source edit.
            Obligation {
                site: 11,
                source_owner: 1,
                placed_template: Some(110),
                input_template: None,
            },
        ],
    }
}

#[test]
fn w13_w18_every_required_site_has_exactly_one_terminal() {
    let plan = class();
    let active = BTreeSet::from([1, 2, 3]);
    let rows = plan.select(&active, &sources(&active)).unwrap();
    assert_eq!(rows.len(), 2);
    assert_eq!(plan.validate(&active, &sources(&active), &rows), Ok(()));
    assert_eq!(
        plan.validate(&active, &sources(&active), &rows[..1]),
        Err(ClassHold::MissingTerminal(11))
    );
    let mut duplicate = rows.clone();
    duplicate.push(rows[0].clone());
    assert_eq!(
        plan.validate(&active, &sources(&active), &duplicate),
        Err(ClassHold::DuplicateSite(10))
    );
    let mut extra = rows.clone();
    extra.push(Terminal {
        site: 12,
        template: 120,
        rendering: Rendering::Placed,
    });
    assert_eq!(
        plan.validate(&active, &sources(&active), &extra),
        Err(ClassHold::UnexpectedTerminal(12))
    );
}

#[test]
fn w14_reverted_caller_selects_input_twin_and_rejects_stale_rows() {
    let plan = class();
    let before = BTreeSet::from([1, 2, 3]);
    let after = BTreeSet::from([1, 2]);
    let stale = plan.select(&before, &sources(&before)).unwrap();
    let repaired = plan.select(&after, &sources(&after)).unwrap();
    assert_eq!(
        repaired[0],
        Terminal {
            site: 10,
            template: 101,
            rendering: Rendering::InputTwin
        }
    );
    assert_eq!(repaired[1].rendering, Rendering::Placed);
    assert_eq!(
        plan.validate(&after, &sources(&after), &stale),
        Err(ClassHold::TerminalMismatch(10))
    );
    assert_eq!(plan.validate(&after, &sources(&after), &repaired), Ok(()));
    let mut missing = class();
    missing.obligations[0].input_template = None;
    assert_eq!(
        missing.select(&after, &sources(&after)),
        Err(ClassHold::MissingInputTwin(10))
    );
}

#[test]
fn w13_dependency_and_base_ownership_are_rechecked_after_recovery() {
    let mut plan = class();
    let active = BTreeSet::from([1, 3]);
    assert_eq!(
        plan.select(&active, &sources(&active)),
        Err(ClassHold::MissingDependency(2))
    );
    plan.base_owner = 4;
    assert_eq!(
        plan.select(&active, &sources(&active)),
        Err(ClassHold::MissingBase(4))
    );
    assert_eq!(
        plan.select(&BTreeSet::from([2, 3, 4]), &BTreeMap::new()),
        Err(ClassHold::DroppedOwner)
    );
}

#[test]
fn w18_duplicate_inventory_and_missing_placed_templates_hold() {
    let active = BTreeSet::from([1, 2, 3]);
    let mut plan = class();
    plan.obligations.push(plan.obligations[0].clone());
    assert_eq!(
        plan.select(&active, &sources(&active)),
        Err(ClassHold::DuplicateSite(10))
    );
    plan.obligations.clear();
    assert_eq!(
        plan.select(&active, &sources(&active)),
        Err(ClassHold::EmptyInventory)
    );
    let mut plan = class();
    plan.obligations[0].placed_template = None;
    assert_eq!(
        plan.select(&active, &sources(&active)),
        Err(ClassHold::MissingPlaced(10))
    );
}

fn sources(active: &BTreeSet<u32>) -> BTreeMap<u32, SourceForm> {
    BTreeMap::from([
        (
            10,
            if active.contains(&3) {
                SourceForm::Cursor
            } else {
                SourceForm::Input
            },
        ),
        (11, SourceForm::Cursor),
    ])
}

#[test]
fn w14_actual_raw_source_in_active_caller_uses_input_twin() {
    let plan = class();
    let active = BTreeSet::from([1, 2, 3]);
    let mut observed = sources(&active);
    observed.insert(10, SourceForm::Input);
    assert_eq!(
        plan.select(&active, &observed).unwrap()[0].rendering,
        Rendering::InputTwin
    );
    observed.remove(&10);
    assert_eq!(
        plan.select(&active, &observed),
        Err(ClassHold::MissingSourceForm(10))
    );
    observed.insert(10, SourceForm::Cursor);
    assert_eq!(
        plan.select(&BTreeSet::from([1, 2]), &observed),
        Err(ClassHold::StaleSourceForm(10))
    );
}
