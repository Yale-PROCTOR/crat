//! Small invented ledger, not the native 61-unit ledger or measured bst rows.
use ownership_fields::{
    adapter::AcceptedInputs,
    emission::Kind,
    export::*,
    held_report::{Custody as TableCustody, *},
};

use super::*;

fn missing(owner: EvidenceOwner, field: &'static str) -> Missing {
    Missing {
        owner,
        reason: MissingReason::Field(field),
    }
}
struct Fixture {
    inputs: AcceptedInputs,
    rows: Vec<Row>,
    keys: BTreeSet<UnitKey>,
    units: BTreeMap<UnitKey, Unit>,
    custody: Evidence<TableCustody>,
}
impl Fixture {
    fn report(&self) -> Result<HeldTable, ReportHold> {
        all_held_table(
            &self.inputs,
            &self.inputs.manifest,
            &self.rows,
            &self.keys,
            &self.units,
            &self.custody,
        )
    }
}
fn fixture() -> Fixture {
    let (mut inputs, mut rows) = export_adapter_cases::fixture();
    rows[0].disposition = Disposition::Held(LicensingHold::Call(CallError::Internal(
        InternalError::Coverage(417),
    )));
    rows[0].certificate = Err(missing(EvidenceOwner::Era5b, "certificate"));
    rows[0].selected_global_field_scheme = Err(missing(
        EvidenceOwner::Era5b,
        "selected_global_field_scheme",
    ));
    rows[0].occurrence = Err(missing(EvidenceOwner::NativeIdentity, "invocation"));
    rows[0].extra_close_obligations =
        Err(missing(EvidenceOwner::Emission, "extra_close_obligations"));
    inputs.records.clear();
    inputs.occurrences = Err(missing(EvidenceOwner::NativeIdentity, "invocation_table"));
    let first = rows[0].declaration_key.as_ref().unwrap().clone();
    let mut second = first.clone();
    second.call.statement += 1;
    second.guard.ordinal += 1;
    let mut row = rows[0].clone();
    row.declaration_key = Ok(second.clone());
    row.disposition = Disposition::Held(LicensingHold::Caller(CallerHold::MissingReset));
    rows.push(row);
    inputs.manifest.declaration_keys = Ok(BTreeSet::from([first.clone(), second.clone()]));
    let keys = BTreeSet::from([
        UnitKey("synthetic-a".into()),
        UnitKey("synthetic-b".into()),
        UnitKey("synthetic-unjoined".into()),
    ]);
    let units = BTreeMap::from([
        (
            UnitKey("synthetic-a".into()),
            Unit {
                crown_form: "Option<Box<Node>>".into(),
                declarations: Ok(BTreeSet::from([first.clone(), second])),
            },
        ),
        (
            UnitKey("synthetic-b".into()),
            Unit {
                crown_form: "*const Node".into(),
                declarations: Ok(BTreeSet::from([first])),
            },
        ),
        (
            UnitKey("synthetic-unjoined".into()),
            Unit {
                crown_form: "Box<Node>".into(),
                declarations: Err(missing(EvidenceOwner::NativeIdentity, "ledger_unit_join")),
            },
        ),
    ]);
    let forms = keys
        .iter()
        .map(|key| {
            (
                key.clone(),
                ObservedForm {
                    kind: if key.0 == "synthetic-b" {
                        Kind::Ref
                    } else {
                        Kind::Raw
                    },
                    emitted_form: if key.0 == "synthetic-b" {
                        "Option<&'a Node>"
                    } else {
                        "*mut Node"
                    }
                    .into(),
                },
            )
        })
        .collect();
    let custody = Ok(TableCustody {
        frame: inputs.manifest.frame.as_ref().unwrap().clone(),
        source_hash: Digest([44; 32]),
        forms,
    });
    Fixture {
        inputs,
        rows,
        keys,
        units,
        custody,
    }
}

#[test]
fn all_held_box_table_keeps_every_unit_inner_reason_and_observed_borrow() {
    let f = fixture();
    let report = f.report().unwrap();
    assert_eq!(report.rows.keys().cloned().collect::<BTreeSet<_>>(), f.keys);
    assert_eq!(report.emitted_boxes, 0);
    assert_eq!(report.source_hash, Digest([44; 32]));
    let a = &report.rows[&UnitKey("synthetic-a".into())];
    assert_eq!(a.reasons.as_ref().unwrap().len(), 2);
    assert_eq!(
        a.reasons.as_ref().unwrap()[f.rows[0].declaration_key.as_ref().unwrap()].reason,
        MissingReason::Held(LicensingHold::Call(CallError::Internal(
            InternalError::Coverage(417)
        )))
    );
    let b = &report.rows[&UnitKey("synthetic-b".into())];
    assert_eq!(
        (&b.crown_form, &b.emitted_form),
        (&"*const Node".to_string(), &"Option<&'a Node>".to_string())
    );
    assert_eq!(
        report.rows[&UnitKey("synthetic-unjoined".into())].reasons,
        Err(missing(EvidenceOwner::NativeIdentity, "ledger_unit_join"))
    );
    let table = report.markdown();
    assert_eq!(table.lines().count(), f.keys.len() + 2);
    assert_eq!(table.matches(" | 0 | ").count(), f.keys.len());
    for text in [
        "crown_form",
        "emitted_form",
        "Coverage(417)",
        "MissingReset",
        "OPEN:",
        "Option<&'a Node>",
    ] {
        assert!(table.contains(text), "{text}");
    }
    println!("SYNTHETIC_ALL_HELD_TABLE_BEGIN\n{table}SYNTHETIC_ALL_HELD_TABLE_END");
}

#[test]
fn all_held_table_never_turns_missing_custody_into_zero_delivery() {
    let mut f = fixture();
    let why = missing(EvidenceOwner::Emission, "sealed_tree_custody");
    f.custody = Err(why.clone());
    assert_eq!(f.report().unwrap_err(), ReportHold::Evidence(why));
    let mut f = fixture();
    f.custody.as_mut().unwrap().frame.accepted_round += 1;
    assert_eq!(f.report().unwrap_err(), ReportHold::CustodyFrame);
    let mut f = fixture();
    let key = f.keys.first().unwrap().clone();
    f.custody
        .as_mut()
        .unwrap()
        .forms
        .get_mut(&key)
        .unwrap()
        .kind = Kind::Owning;
    assert_eq!(f.report().unwrap_err(), ReportHold::UnexpectedBox(key));
}

#[test]
fn all_held_table_rejects_incomplete_or_crossed_unit_joins() {
    let mut f = fixture();
    f.units.pop_last();
    assert_eq!(f.report().unwrap_err(), ReportHold::UnitInventory);
    let mut f = fixture();
    f.custody.as_mut().unwrap().forms.pop_last();
    assert_eq!(f.report().unwrap_err(), ReportHold::UnitInventory);
    let mut f = fixture();
    let key = f.keys.first().unwrap().clone();
    f.units.get_mut(&key).unwrap().declarations = Ok(BTreeSet::new());
    assert_eq!(f.report().unwrap_err(), ReportHold::EmptyJoin(key.clone()));
    let mut f = fixture();
    let mut wrong = f.rows[0].declaration_key.as_ref().unwrap().clone();
    wrong.argument += 1;
    f.units.get_mut(&key).unwrap().declarations = Ok(BTreeSet::from([wrong.clone()]));
    assert_eq!(
        f.report().unwrap_err(),
        ReportHold::ForeignDeclaration(key, wrong)
    );
}

#[test]
fn all_held_table_cannot_hide_conditional_selected_or_missing_declarations() {
    let (_, selected) = export_adapter_cases::fixture();
    for disposition in [
        Disposition::Conditional,
        selected[0].disposition.clone(),
        Disposition::Missing(missing(EvidenceOwner::Era5b, "declaration")),
    ] {
        let mut f = fixture();
        let key = f.rows[0].declaration_key.as_ref().unwrap().clone();
        f.rows[0].disposition = disposition;
        assert_eq!(f.report().unwrap_err(), ReportHold::NotAllHeld(key));
    }
}
