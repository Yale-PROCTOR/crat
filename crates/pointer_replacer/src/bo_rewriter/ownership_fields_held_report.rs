//! R347 all-held Box table over supplied ledger joins and custody observations.
//! No native lookup, parser, census or emission. The caller must import exact
//! ledger identities and observe the sealed tree; absence of grants alone is
//! never evidence of zero delivered Boxes.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    adapter::{AcceptedInputs, prepare},
    emission::Kind,
    export::*,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct UnitKey(pub String);
#[derive(Clone, Debug)]
pub struct Unit {
    pub crown_form: String,
    /// Exact native join; a missing/unjoinable unit remains an OPEN table row.
    pub declarations: Evidence<BTreeSet<DeclarationKey>>,
}
#[derive(Clone, Debug)]
pub struct ObservedForm {
    /// Parser-derived classification, distinct from the model's kind.
    pub kind: Kind,
    pub emitted_form: String,
}
#[derive(Clone, Debug)]
pub struct Custody {
    pub frame: Frame,
    pub source_hash: Digest,
    pub forms: BTreeMap<UnitKey, ObservedForm>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeldRow {
    pub crown_form: String,
    pub emitted_form: String,
    pub reasons: Evidence<BTreeMap<DeclarationKey, Missing>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeldTable {
    pub source_hash: Digest,
    pub rows: BTreeMap<UnitKey, HeldRow>,
    pub emitted_boxes: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReportHold {
    Evidence(Missing),
    NotAllHeld(DeclarationKey),
    UnitInventory,
    CustodyFrame,
    EmptyJoin(UnitKey),
    ForeignDeclaration(UnitKey, DeclarationKey),
    UnexpectedGrant(DeclarationKey),
    UnexpectedBox(UnitKey),
}
impl From<Missing> for ReportHold {
    fn from(value: Missing) -> Self {
        Self::Evidence(value)
    }
}

pub fn all_held_table(
    expected: &AcceptedInputs,
    manifest: &Manifest,
    declarations: &[Row],
    required_units: &BTreeSet<UnitKey>,
    units: &BTreeMap<UnitKey, Unit>,
    custody: &Evidence<Custody>,
) -> Result<HeldTable, ReportHold> {
    let prepared = prepare(expected, manifest, declarations)?;
    let mut holds = BTreeMap::new();
    for row in declarations {
        let key = row.declaration_key.as_ref().map_err(Clone::clone)?;
        if !matches!(row.disposition, Disposition::Held(_)) {
            return Err(ReportHold::NotAllHeld(key.clone()));
        }
        match prepared.owning_grant(key) {
            Ok(_) => return Err(ReportHold::UnexpectedGrant(key.clone())),
            Err(reason) => {
                holds.insert(key.clone(), reason);
            }
        }
    }
    let custody = custody.as_ref().map_err(Clone::clone)?;
    if &custody.frame != manifest.frame.as_ref().map_err(Clone::clone)? {
        return Err(ReportHold::CustodyFrame);
    }
    if &units.keys().cloned().collect::<BTreeSet<_>>() != required_units
        || &custody.forms.keys().cloned().collect::<BTreeSet<_>>() != required_units
    {
        return Err(ReportHold::UnitInventory);
    }
    let mut rows = BTreeMap::new();
    for (key, unit) in units {
        let observed = &custody.forms[key];
        if observed.kind == Kind::Owning {
            return Err(ReportHold::UnexpectedBox(key.clone()));
        }
        let reasons = match &unit.declarations {
            Err(missing) => Err(missing.clone()),
            Ok(keys) => {
                if keys.is_empty() {
                    return Err(ReportHold::EmptyJoin(key.clone()));
                }
                let mut reasons = BTreeMap::new();
                for declaration in keys {
                    let reason = holds.get(declaration).ok_or_else(|| {
                        ReportHold::ForeignDeclaration(key.clone(), declaration.clone())
                    })?;
                    reasons.insert(declaration.clone(), reason.clone());
                }
                Ok(reasons)
            }
        };
        rows.insert(
            key.clone(),
            HeldRow {
                crown_form: unit.crown_form.clone(),
                emitted_form: observed.emitted_form.clone(),
                reasons,
            },
        );
    }
    Ok(HeldTable {
        source_hash: custody.source_hash,
        rows,
        emitted_boxes: 0,
    })
}

impl HeldTable {
    pub fn markdown(&self) -> String {
        let cell = |value: &str| {
            value
                .replace('\\', "\\\\")
                .replace('|', "\\|")
                .replace('\r', " ")
                .replace('\n', "<br>")
        };
        let mut out = String::from(
            "| unit | crown_form | emitted_form | Box emitted | reason |\n|---|---|---|---|---|\n",
        );
        for (key, row) in &self.rows {
            // Debug is presentation of the retained typed payload, never a
            // reverse parser or an identity join. Keep all nested reasons.
            let reason = match &row.reasons {
                Ok(reasons) => format!("{reasons:?}"),
                Err(missing) => format!("OPEN: {missing:?}"),
            };
            out.push_str(&format!(
                "| {} | {} | {} | 0 | {} |\n",
                cell(&key.0),
                cell(&row.crown_form),
                cell(&row.emitted_form),
                cell(&reason)
            ));
        }
        out
    }
}
