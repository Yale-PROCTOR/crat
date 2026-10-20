//! Pure adapter preparation. No cache IO, decoding, rustc identity collection,
//! or production registration. Native integration must supply a verified
//! manifest/record inventory and invocation binding after the seat's gate.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    emission::{Grant, GrantStatus, Kind},
    export::*,
    lifecycle::CloseKind,
};

/// Supplied by the future accepted-artifact decoder. It must verify digests
/// from closed bytes, qualify frames and decode companion bodies by family.
#[derive(Clone, Debug)]
pub struct AcceptedInputs {
    pub manifest: Manifest,
    pub records: BTreeMap<RecordKey, FactFamily>,
    pub occurrences: Evidence<BTreeMap<DeclarationKey, Occurrence>>,
}

fn need<T>(evidence: &Evidence<T>) -> Evidence<&T> {
    evidence.as_ref().map_err(Clone::clone)
}
fn hold(owner: EvidenceOwner, reason: MissingReason) -> Missing {
    Missing { owner, reason }
}
fn frame_hold(part: &'static str) -> Missing {
    hold(
        EvidenceOwner::FrameQualification,
        MissingReason::Frame(part),
    )
}

pub fn prepare<'a>(
    expected: &'a AcceptedInputs,
    manifest: &Manifest,
    rows: &'a [Row],
) -> Evidence<Prepared<'a>> {
    // Inspect absences before equality so the producer's owner/reason survive.
    let frame = need(&manifest.frame)?;
    if !*need(&manifest.family_complete)? || !*need(&expected.manifest.family_complete)? {
        return Err(hold(EvidenceOwner::Era5b, MissingReason::IncompleteFamily));
    }
    let declarations = need(&manifest.declaration_keys)?;
    let transport = need(&manifest.transport)?;
    let prepared = Prepared { expected, rows };
    if let FamilyTransport::Compared(reference) = transport {
        prepared.companion(reference)?;
    }
    if manifest.schema != 1 || manifest.schema != expected.manifest.schema {
        return Err(frame_hold("schema"));
    }
    if frame != need(&expected.manifest.frame)? {
        return Err(frame_hold("manifest"));
    }
    if manifest.artifact_digest != expected.manifest.artifact_digest {
        return Err(frame_hold("artifact_digest"));
    }
    if transport != need(&expected.manifest.transport)? {
        return Err(frame_hold("family_transport"));
    }
    let mut seen = BTreeSet::new();
    for row in rows {
        let key = need(&row.declaration_key)?;
        if !seen.insert(key.clone()) {
            return Err(hold(
                EvidenceOwner::Era5b,
                MissingReason::DuplicateDeclaration(key.clone()),
            ));
        }
    }
    if &seen != declarations || declarations != need(&expected.manifest.declaration_keys)? {
        return Err(hold(EvidenceOwner::Era5b, MissingReason::DeclarationSet));
    }
    Ok(prepared)
}

#[derive(Debug)]
pub struct Prepared<'a> {
    expected: &'a AcceptedInputs,
    rows: &'a [Row],
}
impl Prepared<'_> {
    fn row(&self, key: &DeclarationKey) -> Evidence<&Row> {
        self.rows
            .iter()
            .find(|row| row.declaration_key.as_ref() == Ok(key))
            .ok_or_else(|| hold(EvidenceOwner::Era5b, MissingReason::DeclarationSet))
    }

    /// Authorizes an effective owning kind only. P1′-E, construction, field,
    /// free and extra-close consumers still require their site-specific facts.
    pub fn owning_grant(&self, key: &DeclarationKey) -> Evidence<Grant> {
        let row = self.row(key)?;
        let selection = match &row.disposition {
            Disposition::Selected(evidence) => need(evidence)?,
            Disposition::Conditional => {
                return Err(hold(EvidenceOwner::Era5b, MissingReason::Conditional));
            }
            Disposition::Held(reason) => {
                return Err(hold(
                    EvidenceOwner::Era5b,
                    MissingReason::Held(reason.clone()),
                ));
            }
            Disposition::Missing(missing) => return Err(missing.clone()),
        };
        let frame = need(&self.expected.manifest.frame)?;
        if need(&selection.attestation)? != frame {
            return Err(frame_hold("selection_attestation"));
        }
        if selection.guard != key.guard
            || selection.accepted.guards.get(&key.guard) != Some(&true)
            || (selection.required_closed_frame && !selection.closed_call_world)
            || !selection
                .required
                .owning
                .iter()
                .all(|(node, value)| selection.accepted.owning.get(node) == Some(value))
            || !selection
                .required
                .guards
                .iter()
                .all(|(guard, value)| selection.accepted.guards.get(guard) == Some(value))
        {
            return Err(hold(EvidenceOwner::Era5b, MissingReason::Selection));
        }
        self.companion(&selection.validation)?;
        match need(&row.certificate)? {
            Certificate::Caller { internal, caller } => {
                self.companion(internal)?;
                self.companion(caller)?;
            }
            Certificate::Member { internal, member } => {
                self.companion(internal)?;
                self.companion(member)?;
            }
        }
        self.companion(&row.requirements)?;
        self.companion(&row.checked_laws)?;
        let required = need(&row.required_field_set)?;
        let scheme = need(&row.selected_global_field_scheme)?;
        if need(&scheme.frame)? != frame {
            return Err(frame_hold("global_field_scheme"));
        }
        self.companion(&scheme.support)?;
        self.companion(&scheme.selection_basis)?;
        if !required.is_subset(&scheme.owning)
            || !scheme
                .owning
                .iter()
                .all(|field| scheme.fields.contains_key(field))
            || scheme.fields.values().collect::<BTreeSet<_>>().len() != scheme.fields.len()
        {
            return Err(hold(EvidenceOwner::Era5b, MissingReason::GlobalFieldScheme));
        }
        let occurrence = need(&row.occurrence)?;
        self.companion(&occurrence.generation_recipe)?;
        let transport = need(&occurrence.transported_key)?;
        let native = need(&self.expected.occurrences)?;
        if occurrence.declaration != *key
            || native.get(key) != Some(occurrence)
            || transport != &occurrence.key
            || occurrence.key.model != self.expected.manifest.artifact_digest.0
            || occurrence.key.configuration != frame.configuration.0
        {
            return Err(hold(
                EvidenceOwner::NativeIdentity,
                MissingReason::Occurrence,
            ));
        }
        // This digest names the separate accepted grant artifact. It never
        // replaces the producer/cache digest, which remains in Frame.
        Ok(Grant {
            key: occurrence.key,
            kind: Kind::Owning,
            status: GrantStatus::Selected,
            transport: Some(*transport),
        })
    }

    pub fn companion<T: FactTag>(&self, reference: &Evidence<FactRef<T>>) -> Evidence<RecordKey> {
        let reference = need(reference)?;
        if self.expected.records.get(&reference.record) != Some(&T::FAMILY) {
            return Err(hold(
                EvidenceOwner::Emission,
                MissingReason::Companion(T::FAMILY),
            ));
        }
        Ok(reference.record)
    }

    /// Resolves planned obligations, not waiver receipts or permission to drop.
    /// H-DROP-RECURSION's suppression branch remains in the lifecycle consumer.
    pub fn extra_closes(&self, key: &DeclarationKey) -> Evidence<&[ExtraClose]> {
        let grant = self.owning_grant(key)?;
        let closes = need(&self.row(key)?.extra_close_obligations)?;
        for (index, close) in closes.iter().enumerate() {
            let owner = need(&close.owner)?;
            self.companion(&close.required_proofs)?;
            self.companion(&close.depth)?;
            if closes[..index].iter().any(|prior| {
                prior.site == close.site
                    && prior.path == close.path
                    && prior.kind == close.kind
                    && prior.owner == close.owner
            }) {
                return Err(hold(
                    EvidenceOwner::Emission,
                    MissingReason::DuplicateClose(close.site),
                ));
            }
            let expected_kind = match close.reason {
                ExtraCloseReason::LiveAtScopeExit => CloseKind::ScopeExit,
                ExtraCloseReason::LiveAtUnwind => CloseKind::Unwind,
                ExtraCloseReason::OverwrittenUniqueOwner => CloseKind::Overwrite,
            };
            if close.kind != expected_kind {
                return Err(hold(
                    EvidenceOwner::Emission,
                    MissingReason::CloseReason(close.site),
                ));
            }
            if owner.model != grant.key.model
                || owner.configuration != grant.key.configuration
                || owner.generation != grant.key.generation
            {
                return Err(hold(
                    EvidenceOwner::NativeIdentity,
                    MissingReason::Occurrence,
                ));
            }
        }
        Ok(closes)
    }
}
