//! Source evidence availability, never a universal emitted-history certificate.
use std::collections::{BTreeMap, BTreeSet};

use rustc_middle::ty::TyCtxt;

use super::export::BoExport;

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Family {
    SourceRetirement,
    InputTarget,
    Entry,
    Observation,
    Binding,
    Access,
    Witness,
    CallTargets,
}
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Missing {
    EmittedSchedule,
    GeneratedBridgeLastUse,
    DynamicAllocationEpoch,
    GeneralKillSurvival,
    T16TighterFootprint,
    T16AllHistories,
    CompleteDescendantAncestry,
    NestedArrayStorageAddress,
}
const MISSING: [Missing; 8] = [
    Missing::EmittedSchedule,
    Missing::GeneratedBridgeLastUse,
    Missing::DynamicAllocationEpoch,
    Missing::GeneralKillSurvival,
    Missing::T16TighterFootprint,
    Missing::T16AllHistories,
    Missing::CompleteDescendantAncestry,
    Missing::NestedArrayStorageAddress,
];
const FAMILIES: [Family; 8] = [
    Family::SourceRetirement,
    Family::InputTarget,
    Family::Entry,
    Family::Observation,
    Family::Binding,
    Family::Access,
    Family::Witness,
    Family::CallTargets,
];
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Claim {
    SourceObservationsOnly,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Row {
    pub(crate) key: String,
    pub(crate) references: Vec<String>,
    pub(crate) facts: BTreeMap<String, String>,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ProofEvidence {
    pub(crate) schema: String,
    pub(crate) claim: Claim,
    pub(crate) licensing_deferred: bool,
    /// None means capture unavailable; Some(empty) is an observed empty family.
    pub(crate) families: BTreeMap<Family, Option<Vec<Row>>>,
    pub(crate) missing: BTreeSet<Missing>,
}
impl Default for ProofEvidence {
    fn default() -> Self {
        Self {
            schema: "era5a-proof-evidence-v2".into(),
            claim: Claim::SourceObservationsOnly,
            licensing_deferred: true,
            families: FAMILIES.into_iter().map(|f| (f, None)).collect(),
            missing: MISSING.into_iter().collect(),
        }
    }
}
impl ProofEvidence {
    pub(crate) fn from_export(tcx: TyCtxt<'_>, export: &BoExport) -> Self {
        use super::protected_entry::{CurrentBinding, EntryFact, evidence::FactRule};
        let mut out = Self::default();
        if let Some(source) = &export.source_events {
            let rows = source
                .retirements
                .values()
                .map(|event| {
                    make(
                        source_key(&event.key),
                        vec![],
                        [
                            ("condition", format!("{:?}", event.key.condition)),
                            ("role", format!("{:?}", event.key.role)),
                            ("phase", format!("{:?}", event.key.phase)),
                            ("region", format!("{:?}", event.region)),
                            ("generation", format!("{:?}", event.generation)),
                            ("coverage", format!("{:?}", event.coverage)),
                            ("object", format!("{:?}", event.object)),
                        ],
                    )
                })
                .collect();
            out.families.insert(Family::SourceRetirement, Some(rows));
            let rows = source
                .call_targets
                .iter()
                .map(|(&(function, location), targets)| {
                    let function = tcx.def_path_str(function.to_def_id());
                    let mut known: Vec<_> = targets
                        .known
                        .iter()
                        .map(|did| tcx.def_path_str(*did))
                        .collect();
                    known.sort();
                    make(
                        format!("call/{function}/{}", loc(location)),
                        vec![],
                        [
                            ("function", function),
                            ("location", loc(location)),
                            ("known", serde_json::to_string(&known).unwrap()),
                            ("unknown", targets.unknown.to_string()),
                        ],
                    )
                })
                .collect();
            out.families.insert(Family::CallTargets, Some(rows));
        }
        if let Some(entry) = &export.entry_protection {
            // A known incoming raw value is not necessarily a protected Ref.
            // Keep target identity separate from the admitted entry obligation.
            let targets = entry
                .entries
                .iter()
                .map(|e| e.target)
                .chain(entry.observations.iter().map(|o| o.target))
                .chain(
                    entry
                        .observations
                        .iter()
                        .filter_map(|o| match o.current_binding {
                            CurrentBinding::Incoming(target) => Some(target),
                            CurrentBinding::Unknown => None,
                        }),
                )
                .chain(entry.binding_facts.iter().map(|b| b.target));
            let mut inputs = BTreeMap::new();
            for value in targets {
                let row = make(
                    input_key(tcx, value.entry),
                    vec![],
                    [
                        ("slot", slot(tcx, value.entry)),
                        ("target", target(tcx, value)),
                        ("existence", "not-proved".into()),
                    ],
                );
                if let Some(previous) = inputs.insert(row.key.clone(), row.clone()) {
                    assert_eq!(
                        previous, row,
                        "one incoming target per canonical input identity"
                    );
                }
            }
            out.families
                .insert(Family::InputTarget, Some(inputs.into_values().collect()));
            out.families.insert(
                Family::Entry,
                Some(
                    entry
                        .entries
                        .iter()
                        .map(|e| {
                            make(
                                entry_key(tcx, e.key),
                                vec![input_key(tcx, e.key)],
                                [
                                    ("slot", slot(tcx, e.key)),
                                    ("target", target(tcx, e.target)),
                                    ("condition", format!("{:?}", e.condition)),
                                    ("representation", format!("{:?}", e.representation)),
                                ],
                            )
                        })
                        .collect(),
                ),
            );
            out.families.insert(
                Family::Observation,
                Some(
                    entry
                        .observations
                        .iter()
                        .map(|o| {
                            make(
                                observation_key(tcx, o),
                                {
                                    let mut references = vec![
                                        entry_key(tcx, o.entry),
                                        input_key(tcx, o.target.entry),
                                    ];
                                    if let CurrentBinding::Incoming(value) = o.current_binding {
                                        references.push(input_key(tcx, value.entry));
                                    }
                                    references
                                },
                                [
                                    ("entry", entry_key(tcx, o.entry)),
                                    ("target", target(tcx, o.target)),
                                    ("location", loc(o.location)),
                                    ("phase", format!("{:?}", o.phase)),
                                    ("moment", format!("{:?}", o.moment)),
                                    ("live", o.live.to_string()),
                                    (
                                        "demand",
                                        o.demand
                                            .map(|e| entry_key(tcx, e))
                                            .unwrap_or_else(|| "None".into()),
                                    ),
                                    (
                                        "binding",
                                        match o.current_binding {
                                            CurrentBinding::Incoming(t) => target(tcx, t),
                                            CurrentBinding::Unknown => "Unknown".into(),
                                        },
                                    ),
                                ],
                            )
                        })
                        .collect(),
                ),
            );
            out.families.insert(
                Family::Binding,
                Some(
                    entry
                        .binding_facts
                        .iter()
                        .map(|b| {
                            make(
                                binding_key(tcx, b),
                                vec![input_key(tcx, b.target.entry)],
                                [
                                    ("input", input_key(tcx, b.target.entry)),
                                    ("target", target(tcx, b.target)),
                                    (
                                        "slot",
                                        super::slot_key::local_key(
                                            tcx,
                                            b.function,
                                            b.local.as_usize(),
                                            b.depth,
                                        ),
                                    ),
                                    ("location", loc(b.location)),
                                    ("phase", format!("{:?}", b.phase)),
                                    ("moment", format!("{:?}", b.moment)),
                                ],
                            )
                        })
                        .collect(),
                ),
            );
            out.families.insert(
                Family::Access,
                Some(
                    export
                        .entry_accesses
                        .iter()
                        .map(|a| {
                            let function = tcx.def_path_str(a.function.to_def_id());
                            make(
                                format!(
                                    "access/{function}/{}/{:?}/{:?}/{:?}/{:?}/{:?}",
                                    loc(a.location),
                                    a.phase,
                                    a.place,
                                    a.extent,
                                    a.mode,
                                    a.cause
                                ),
                                vec![],
                                [
                                    ("function", function),
                                    ("place", format!("{:?}", a.place)),
                                    ("location", loc(a.location)),
                                    ("phase", format!("{:?}", a.phase)),
                                    ("extent", format!("{:?}", a.extent)),
                                    ("mode", format!("{:?}", a.mode)),
                                    ("cause", format!("{:?}", a.cause)),
                                ],
                            )
                        })
                        .collect(),
                ),
            );
            out.families.insert(
                Family::Witness,
                Some(
                    export
                        .entry_fact_witnesses
                        .iter()
                        .map(|w| {
                            let fact = match &w.fact {
                                EntryFact::Entry(e) => entry_key(tcx, e.key),
                                EntryFact::Observation(o) => observation_key(tcx, o),
                                EntryFact::Binding(b) => binding_key(tcx, b),
                            };
                            let rule = match w.rule {
                                FactRule::ParameterEntry(_) => "ParameterEntry",
                                FactRule::WholeCallReachability(_) => "WholeCallReachability",
                                FactRule::FrameExit(_) => "FrameExit",
                                FactRule::LocatedInputBinding(_) => "LocatedInputBinding",
                            };
                            let predecessors: Vec<_> = w
                                .predecessors
                                .iter()
                                .map(|p| {
                                    format!(
                                        "{}/{}/{:?}/{:?}",
                                        tcx.def_path_str(p.function.to_def_id()),
                                        loc(p.location),
                                        p.phase,
                                        p.moment
                                    )
                                })
                                .collect();
                            make(
                                format!("witness/{fact}"),
                                vec![fact.clone()],
                                [
                                    ("fact", fact),
                                    ("rule", rule.into()),
                                    (
                                        "predecessors",
                                        serde_json::to_string(&predecessors).unwrap(),
                                    ),
                                ],
                            )
                        })
                        .collect(),
                ),
            );
        }
        for rows in out.families.values_mut().flatten() {
            rows.sort_by(|a, b| a.key.cmp(&b.key));
        }
        out
    }

    pub(crate) fn validate(&self) -> Result<(), String> {
        if self.schema != "era5a-proof-evidence-v2"
            || !self.licensing_deferred
            || self.missing != MISSING.into_iter().collect()
        {
            return Err("schema/licensing or required Missing evidence changed".into());
        }
        if self.families.keys().copied().collect::<BTreeSet<_>>() != FAMILIES.into_iter().collect()
        {
            return Err("missing evidence family".into());
        }
        let mut keys = BTreeSet::new();
        for (&family, rows) in &self.families {
            let expected: &[&str] = match family {
                Family::SourceRetirement => &[
                    "condition",
                    "role",
                    "phase",
                    "region",
                    "generation",
                    "coverage",
                    "object",
                ],
                Family::InputTarget => &["slot", "target", "existence"],
                Family::Entry => &["slot", "target", "condition", "representation"],
                Family::Observation => &[
                    "entry", "target", "location", "phase", "moment", "live", "demand", "binding",
                ],
                Family::Binding => &["input", "target", "slot", "location", "phase", "moment"],
                Family::Access => &[
                    "function", "place", "location", "phase", "extent", "mode", "cause",
                ],
                Family::Witness => &["fact", "rule", "predecessors"],
                Family::CallTargets => &["function", "location", "known", "unknown"],
            };
            for row in rows.iter().flatten() {
                if !keys.insert(row.key.clone()) {
                    return Err(format!("duplicate evidence key: {}", row.key));
                }
                if row
                    .facts
                    .keys()
                    .map(String::as_str)
                    .collect::<BTreeSet<_>>()
                    != expected.iter().copied().collect()
                {
                    return Err(format!("unexpected fact schema: {}", row.key));
                }
                if family == Family::Observation && !row.references.contains(&row.facts["entry"]) {
                    return Err("missing entry relation".into());
                }
                if family == Family::Entry
                    && !row
                        .references
                        .contains(&format!("input/{}", row.facts["slot"]))
                {
                    return Err("missing entry input-target relation".into());
                }
                if family == Family::InputTarget && row.facts["existence"] != "not-proved" {
                    return Err("input identity cannot prove object existence".into());
                }
                if family == Family::Binding && !row.references.contains(&row.facts["input"]) {
                    return Err("missing incoming-value relation".into());
                }
                if family == Family::Witness && !row.references.contains(&row.facts["fact"]) {
                    return Err("missing witnessed-fact relation".into());
                }
            }
        }
        for row in self.families.values().flatten().flatten() {
            if row.references.iter().any(|key| !keys.contains(key)) {
                return Err(format!("dangling evidence reference: {}", row.key));
            }
        }
        Ok(())
    }

    pub(crate) fn canonical_json(&self) -> Result<String, String> {
        self.validate()?;
        let mut ordered = self.clone();
        for rows in ordered.families.values_mut().flatten() {
            rows.sort_by(|a, b| a.key.cmp(&b.key));
        }
        serde_json::to_string(&ordered).map_err(|e| e.to_string())
    }
}
fn make<const N: usize>(
    key: String,
    mut references: Vec<String>,
    facts: [(&str, String); N],
) -> Row {
    references.sort();
    references.dedup();
    Row {
        key,
        references,
        facts: facts.into_iter().map(|(k, v)| (k.into(), v)).collect(),
    }
}
fn loc(location: rustc_middle::mir::Location) -> String {
    format!("{}:{}", location.block.as_u32(), location.statement_index)
}
fn slot(tcx: TyCtxt<'_>, entry: super::protected_entry::EntryKey) -> String {
    super::slot_key::local_key(tcx, entry.function, entry.parameter.as_usize(), entry.depth)
}
fn input_key(tcx: TyCtxt<'_>, entry: super::protected_entry::EntryKey) -> String {
    format!("input/{}", slot(tcx, entry))
}
fn entry_key(tcx: TyCtxt<'_>, entry: super::protected_entry::EntryKey) -> String {
    format!("entry/{}", slot(tcx, entry))
}
fn target(tcx: TyCtxt<'_>, target: super::protected_entry::IncomingTarget) -> String {
    format!(
        "incoming({})/deref{}",
        input_key(tcx, target.entry),
        target.dereferences
    )
}
fn observation_key(tcx: TyCtxt<'_>, o: &super::protected_entry::EntryObservation) -> String {
    format!(
        "observation/{}/{}/{:?}/{:?}",
        entry_key(tcx, o.entry),
        loc(o.location),
        o.phase,
        o.moment
    )
}
fn binding_key(tcx: TyCtxt<'_>, b: &super::protected_entry::BindingFact) -> String {
    format!(
        "binding/{}/{}/{:?}/{:?}/{}",
        super::slot_key::local_key(tcx, b.function, b.local.as_usize(), b.depth),
        loc(b.location),
        b.phase,
        b.moment,
        target(tcx, b.target)
    )
}
fn source_key(key: &super::source_events::SourceEventKey) -> String {
    format!(
        "source/{}/{}:{}/{:?}/{:?}/{:?}/{:?}",
        key.function,
        key.block,
        key.statement,
        key.phase,
        key.role,
        key.storage_local,
        key.condition
    )
}
#[cfg(test)]
mod controls;
#[cfg(test)]
mod tests;
