//! Cursor-specific validation against an existing class finalizer's terminal
//! active set. This does not replace that finalizer, apply edits, discover use
//! sites or prove their semantic prerequisites. Re-run after every recovery.

use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rendering {
    Placed,
    InputTwin,
}

/// Per-site observation from the terminal placed-form accessor. An active
/// caller class alone does not say that this particular source was converted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SourceForm {
    Cursor,
    Input,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Obligation<K> {
    pub site: K,
    pub source_owner: K,
    /// Keys of sealed templates, including explicit zero-syntax templates.
    pub placed_template: Option<K>,
    pub input_template: Option<K>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Terminal<K> {
    pub site: K,
    pub template: K,
    pub rendering: Rendering,
}

pub(crate) struct Class<K> {
    pub owner: K,
    pub base_owner: K,
    pub dependencies: Vec<K>,
    pub obligations: Vec<Obligation<K>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ClassHold<K> {
    DroppedOwner,
    MissingBase(K),
    MissingDependency(K),
    EmptyInventory,
    DuplicateSite(K),
    MissingPlaced(K),
    MissingInputTwin(K),
    MissingTerminal(K),
    UnexpectedTerminal(K),
    TerminalMismatch(K),
    MissingSourceForm(K),
    StaleSourceForm(K),
}

impl<K: Copy + Ord> Class<K> {
    pub(crate) fn select(
        &self,
        active: &BTreeSet<K>,
        source_forms: &BTreeMap<K, SourceForm>,
    ) -> Result<Vec<Terminal<K>>, ClassHold<K>> {
        if !active.contains(&self.owner) {
            return Err(ClassHold::DroppedOwner);
        }
        if !active.contains(&self.base_owner) {
            return Err(ClassHold::MissingBase(self.base_owner));
        }
        for &dependency in &self.dependencies {
            if !active.contains(&dependency) {
                return Err(ClassHold::MissingDependency(dependency));
            }
        }
        if self.obligations.is_empty() {
            return Err(ClassHold::EmptyInventory);
        }
        let mut seen = BTreeSet::new();
        let mut selected = Vec::new();
        for obligation in &self.obligations {
            let site = obligation.site;
            if !seen.insert(site) {
                return Err(ClassHold::DuplicateSite(site));
            }
            let source_form = source_forms
                .get(&site)
                .ok_or(ClassHold::MissingSourceForm(site))?;
            if *source_form == SourceForm::Cursor && !active.contains(&obligation.source_owner) {
                return Err(ClassHold::StaleSourceForm(site));
            }
            let (template, rendering) = if *source_form == SourceForm::Cursor {
                (
                    obligation
                        .placed_template
                        .ok_or(ClassHold::MissingPlaced(site))?,
                    Rendering::Placed,
                )
            } else {
                (
                    obligation
                        .input_template
                        .ok_or(ClassHold::MissingInputTwin(site))?,
                    Rendering::InputTwin,
                )
            };
            selected.push(Terminal {
                site,
                template,
                rendering,
            });
        }
        Ok(selected)
    }

    pub(crate) fn validate(
        &self,
        active: &BTreeSet<K>,
        source_forms: &BTreeMap<K, SourceForm>,
        rows: &[Terminal<K>],
    ) -> Result<(), ClassHold<K>> {
        let expected = self.select(active, source_forms)?;
        let mut supplied = BTreeMap::new();
        for row in rows {
            if supplied.insert(row.site, row).is_some() {
                return Err(ClassHold::DuplicateSite(row.site));
            }
        }
        for row in expected {
            let actual = supplied
                .remove(&row.site)
                .ok_or(ClassHold::MissingTerminal(row.site))?;
            if *actual != row {
                return Err(ClassHold::TerminalMismatch(row.site));
            }
        }
        if let Some((&site, _)) = supplied.first_key_value() {
            return Err(ClassHold::UnexpectedTerminal(site));
        }
        Ok(())
    }
}
