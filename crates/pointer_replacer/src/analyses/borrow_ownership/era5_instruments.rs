//! Pure era-5 integrity instruments. Inputs are sealed facts, not permission to
//! launch work or choose hosts/caps. No worker, filesystem, network or solver API.

use std::collections::{BTreeMap, BTreeSet};

pub(crate) const REQUIRED_PROGRAMS: [&str; 20] = [
    "bst",
    "avl",
    "ht",
    "libcsv",
    "buffer",
    "quadtree",
    "urlparser",
    "robotfindskitten",
    "rgba",
    "genann",
    "libtree",
    "json.h",
    "binn",
    "libzahl",
    "lil",
    "heman",
    "bzip2",
    "lodepng",
    "tulipindicators",
    "brotli",
];

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub(crate) struct Digest(pub(crate) [u8; 32]);
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct ProgramIdentity {
    pub(crate) key: String,
    pub(crate) input: Digest,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum InventoryError {
    InvalidSeal,
    Duplicate(String),
    Missing(String),
    Unexpected(String),
    ChangedInput(String),
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", content = "reason", rename_all = "kebab-case")]
pub(crate) enum FailureKind {
    Timeout,
    Oom,
    Unknown(String),
    Decline(String),
    Missing,
    Invalid(String),
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "state", content = "value", rename_all = "kebab-case")]
pub(crate) enum WorkerState {
    Pending,
    Running,
    Complete(Digest),
    Failure(FailureKind),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum WorkerOutcome {
    Complete(Digest),
    Failure(FailureKind),
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct WorkerEntry {
    pub(crate) program: ProgramIdentity,
    pub(crate) state: WorkerState,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Manifest {
    pub(crate) entries: Vec<WorkerEntry>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TransitionError {
    UnknownProgram(String),
    DuplicateProgram(String),
    InvalidTransition { from: WorkerState, to: WorkerState },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Guards {
    pub(crate) worker_seconds: u64,
    pub(crate) query_seconds: u64,
    pub(crate) emission_seconds: u64,
}
/// Required guard identities; validating them never authorizes a changed budget.
pub(crate) const REQUIRED_GUARDS: Guards = Guards {
    worker_seconds: 14_400,
    query_seconds: 600,
    emission_seconds: 900,
};
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum WorkClass {
    Heavy,
    Small,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Reservation {
    pub(crate) id: String,
    pub(crate) host: String,
    pub(crate) class: WorkClass,
    pub(crate) cap_mib: u64,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ResourceSeal {
    pub(crate) host: String,
    pub(crate) physical_mib: u64,
    pub(crate) headroom_mib: u64,
    pub(crate) guards: Guards,
    pub(crate) reservations: Vec<Reservation>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ResourceError {
    InvalidSeal,
    GuardMismatch,
    UnknownReservation(String),
    DuplicateReservation(String),
    WrongHost(String),
    TooManyWorkers,
    TooManyHeavy,
    AggregateCapExceeded,
    ArithmeticOverflow,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct TransportEnvelope {
    pub(crate) program: ProgramIdentity,
    pub(crate) semantic_key: Digest,
    pub(crate) body: Digest,
    pub(crate) payload: Digest,
    pub(crate) exports: Digest,
    pub(crate) toolchain: Digest,
    pub(crate) launch: Digest,
    pub(crate) source: Digest,
    pub(crate) host: String,
    pub(crate) host_provenance: Digest,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TransportField {
    Program,
    SemanticKey,
    Body,
    Payload,
    Exports,
    Toolchain,
    Launch,
    Source,
    Host,
    HostProvenance,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TransportError {
    pub(crate) field: TransportField,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RestorationError {
    pub(crate) expected: Digest,
    pub(crate) observed: Digest,
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Kind {
    Raw,
    Ref,
    Owning,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Side {
    Before,
    After,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct IdentityRow {
    /// Missing canonical identity remains Unmapped; diagnostics never fill it.
    pub(crate) canonical: Option<String>,
    pub(crate) diagnostic: String,
    pub(crate) kind: Kind,
    pub(crate) reasons: String,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct JoinedIdentity {
    pub(crate) canonical: String,
    pub(crate) before: Kind,
    pub(crate) after: Kind,
    pub(crate) before_reasons: BTreeSet<String>,
    pub(crate) after_reasons: BTreeSet<String>,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct UnmappedIdentity {
    pub(crate) side: Side,
    pub(crate) row: IdentityRow,
}
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct GrossTransition {
    pub(crate) before: Kind,
    pub(crate) after: Kind,
    pub(crate) count: usize,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct IdentityJoin {
    pub(crate) common: Vec<JoinedIdentity>,
    pub(crate) added: Vec<IdentityRow>,
    pub(crate) removed: Vec<IdentityRow>,
    pub(crate) unmapped: Vec<UnmappedIdentity>,
    pub(crate) gross: Vec<GrossTransition>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct JoinError {
    pub(crate) side: Side,
    pub(crate) duplicate: String,
}

/// Validate identities and source bytes, including the seal itself. Equal row
/// counts do not compensate for a missing, duplicate, or substituted program.
pub(crate) fn validate_inventory(
    sealed: &[ProgramIdentity],
    actual: &[ProgramIdentity],
) -> Result<(), InventoryError> {
    let required: BTreeSet<_> = REQUIRED_PROGRAMS.into_iter().collect();
    let mut expected = BTreeMap::new();
    for program in sealed {
        if !required.contains(program.key.as_str())
            || expected
                .insert(program.key.as_str(), program.input)
                .is_some()
        {
            return Err(InventoryError::InvalidSeal);
        }
    }
    if expected.len() != required.len() {
        return Err(InventoryError::InvalidSeal);
    }
    let mut seen = BTreeSet::new();
    for program in actual {
        if !seen.insert(program.key.as_str()) {
            return Err(InventoryError::Duplicate(program.key.clone()));
        }
        let Some(input) = expected.get(program.key.as_str()) else {
            return Err(InventoryError::Unexpected(program.key.clone()));
        };
        if *input != program.input {
            return Err(InventoryError::ChangedInput(program.key.clone()));
        }
    }
    if let Some(key) = expected.keys().find(|key| !seen.contains(**key)) {
        return Err(InventoryError::Missing((*key).to_string()));
    }
    Ok(())
}

/// Only Pending→Running and Running→terminal are legal. Validation precedes
/// mutation, so a rejected transition cannot conceal or restart a failed run.
pub(crate) fn advance(
    manifest: &mut Manifest,
    program: &str,
    next: WorkerState,
) -> Result<(), TransitionError> {
    let mut names = BTreeSet::new();
    let mut target = None;
    for (index, entry) in manifest.entries.iter().enumerate() {
        if !names.insert(entry.program.key.as_str()) {
            return Err(TransitionError::DuplicateProgram(entry.program.key.clone()));
        }
        if entry.program.key == program {
            target = Some(index);
        }
    }
    let Some(index) = target else {
        return Err(TransitionError::UnknownProgram(program.to_owned()));
    };
    let entry = &mut manifest.entries[index];
    let permitted = matches!(
        (&entry.state, &next),
        (WorkerState::Pending, WorkerState::Running)
            | (
                WorkerState::Running,
                WorkerState::Complete(_) | WorkerState::Failure(_)
            )
    );
    if !permitted {
        return Err(TransitionError::InvalidTransition {
            from: entry.state.clone(),
            to: next,
        });
    }
    entry.state = next;
    Ok(())
}

pub(crate) fn terminal_state(outcome: WorkerOutcome) -> WorkerState {
    match outcome {
        WorkerOutcome::Complete(receipt) => WorkerState::Complete(receipt),
        WorkerOutcome::Failure(reason) => WorkerState::Failure(reason),
    }
}

/// Active IDs select their already sealed caps/classes. No default cap, host
/// assignment or replacement guard is created by this validator.
pub(crate) fn validate_resources(
    sealed: &ResourceSeal,
    active: &[String],
) -> Result<(), ResourceError> {
    if sealed.guards != REQUIRED_GUARDS {
        return Err(ResourceError::GuardMismatch);
    }
    if sealed.host.trim().is_empty()
        || sealed.physical_mib == 0
        || sealed.headroom_mib >= sealed.physical_mib
    {
        return Err(ResourceError::InvalidSeal);
    }
    let available = sealed
        .physical_mib
        .checked_sub(sealed.headroom_mib)
        .ok_or(ResourceError::InvalidSeal)?;
    let mut reservations = BTreeMap::new();
    for reservation in &sealed.reservations {
        if reservation.id.trim().is_empty() || reservation.cap_mib == 0 {
            return Err(ResourceError::InvalidSeal);
        }
        if reservation.host != sealed.host {
            return Err(ResourceError::WrongHost(reservation.id.clone()));
        }
        if reservation.cap_mib > available {
            return Err(ResourceError::AggregateCapExceeded);
        }
        if reservations
            .insert(reservation.id.as_str(), reservation)
            .is_some()
        {
            return Err(ResourceError::DuplicateReservation(reservation.id.clone()));
        }
    }
    if active.len() > 3 {
        return Err(ResourceError::TooManyWorkers);
    }
    let mut seen = BTreeSet::new();
    let mut heavy = 0;
    let mut cap = 0u64;
    for id in active {
        if !seen.insert(id.as_str()) {
            return Err(ResourceError::DuplicateReservation(id.clone()));
        }
        let Some(reservation) = reservations.get(id.as_str()) else {
            return Err(ResourceError::UnknownReservation(id.clone()));
        };
        if reservation.class == WorkClass::Heavy {
            heavy += 1;
        }
        cap = cap
            .checked_add(reservation.cap_mib)
            .ok_or(ResourceError::ArithmeticOverflow)?;
    }
    if heavy > 2 {
        return Err(ResourceError::TooManyHeavy);
    }
    if cap > available {
        return Err(ResourceError::AggregateCapExceeded);
    }
    Ok(())
}

pub(crate) fn validate_transport(
    sealed: &TransportEnvelope,
    received: &TransportEnvelope,
) -> Result<(), TransportError> {
    if !REQUIRED_PROGRAMS.contains(&sealed.program.key.as_str())
        || sealed.program != received.program
    {
        return Err(TransportError {
            field: TransportField::Program,
        });
    }
    for (field, expected, observed) in [
        (
            TransportField::SemanticKey,
            sealed.semantic_key,
            received.semantic_key,
        ),
        (TransportField::Body, sealed.body, received.body),
        (TransportField::Payload, sealed.payload, received.payload),
        (TransportField::Exports, sealed.exports, received.exports),
        (
            TransportField::Toolchain,
            sealed.toolchain,
            received.toolchain,
        ),
        (TransportField::Launch, sealed.launch, received.launch),
        (TransportField::Source, sealed.source, received.source),
    ] {
        if expected != observed {
            return Err(TransportError { field });
        }
    }
    if sealed.host.trim().is_empty() || sealed.host != received.host {
        return Err(TransportError {
            field: TransportField::Host,
        });
    }
    if sealed.host_provenance != received.host_provenance {
        return Err(TransportError {
            field: TransportField::HostProvenance,
        });
    }
    Ok(())
}

pub(crate) fn validate_restoration(
    expected: Digest,
    observed: Digest,
) -> Result<(), RestorationError> {
    if expected == observed {
        Ok(())
    } else {
        Err(RestorationError { expected, observed })
    }
}

/// Preserve complete semicolon-delimited components. No first-reason choice or
/// substring/family guess is used to replace exact reason membership.
pub(crate) fn reason_members(composite: &str) -> BTreeSet<String> {
    composite
        .split(';')
        .map(str::trim)
        .filter(|component| !component.is_empty())
        .map(str::to_owned)
        .collect()
}

fn identity_index<'a>(
    rows: &'a [IdentityRow],
    side: Side,
    unmapped: &mut Vec<UnmappedIdentity>,
) -> Result<BTreeMap<&'a str, &'a IdentityRow>, JoinError> {
    let mut indexed = BTreeMap::new();
    for row in rows {
        let Some(key) = row
            .canonical
            .as_deref()
            .filter(|key| !key.trim().is_empty())
        else {
            unmapped.push(UnmappedIdentity {
                side,
                row: row.clone(),
            });
            continue;
        };
        if indexed.insert(key, row).is_some() {
            return Err(JoinError {
                side,
                duplicate: key.to_owned(),
            });
        }
    }
    Ok(indexed)
}

pub(crate) fn join_identities(
    before: &[IdentityRow],
    after: &[IdentityRow],
) -> Result<IdentityJoin, JoinError> {
    let mut result = IdentityJoin::default();
    let old = identity_index(before, Side::Before, &mut result.unmapped)?;
    let new = identity_index(after, Side::After, &mut result.unmapped)?;
    let mut gross = BTreeMap::<(Kind, Kind), usize>::new();
    for (&key, &row) in &old {
        if let Some(next) = new.get(key) {
            result.common.push(JoinedIdentity {
                canonical: key.to_owned(),
                before: row.kind,
                after: next.kind,
                before_reasons: reason_members(&row.reasons),
                after_reasons: reason_members(&next.reasons),
            });
            *gross.entry((row.kind, next.kind)).or_default() += 1;
        } else {
            result.removed.push(row.clone());
        }
    }
    for (&key, &row) in &new {
        if !old.contains_key(key) {
            result.added.push(row.clone());
        }
    }
    result.gross = gross
        .into_iter()
        .map(|((before, after), count)| GrossTransition {
            before,
            after,
            count,
        })
        .collect();
    // Diagnostic text orders the incomplete rows for display only. It never
    // supplies a canonical identity or participates in a successful join.
    result.unmapped.sort_by(|a, b| {
        let side = |side| match side {
            Side::Before => 0u8,
            Side::After => 1u8,
        };
        (
            side(a.side),
            &a.row.canonical,
            &a.row.diagnostic,
            a.row.kind,
            &a.row.reasons,
        )
            .cmp(&(
                side(b.side),
                &b.row.canonical,
                &b.row.diagnostic,
                b.row.kind,
                &b.row.reasons,
            ))
    });
    Ok(result)
}

impl IdentityJoin {
    /// Duplicate canonical keys are rejected by join_identities; a successful
    /// join remains incomplete while any original row lacks a canonical key.
    pub(crate) fn complete(&self) -> bool {
        self.unmapped.is_empty()
    }
}

#[cfg(test)]
mod tests;
