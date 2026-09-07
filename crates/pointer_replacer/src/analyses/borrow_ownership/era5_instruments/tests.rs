//! Injected integrity controls only. Hosts, capacities and digests below are
//! synthetic test data, never measured/selected execution profiles or budgets.

use super::*;

fn digest(value: u8) -> Digest {
    Digest([value; 32])
}
fn programs() -> Vec<ProgramIdentity> {
    REQUIRED_PROGRAMS
        .iter()
        .enumerate()
        .map(|(index, key)| ProgramIdentity {
            key: (*key).to_owned(),
            input: digest(index as u8),
        })
        .collect()
}

#[test]
fn e5_i_inventory_requires_exact_twenty_identities_not_only_count() {
    let sealed = programs();
    let mut reordered = sealed.clone();
    reordered.reverse();
    assert!(validate_inventory(&sealed, &reordered).is_ok());
    let mut duplicate = sealed.clone();
    duplicate[1] = duplicate[0].clone();
    assert!(
        validate_inventory(&sealed, &duplicate).is_err(),
        "duplicate plus missing cannot balance by count"
    );
    assert!(validate_inventory(&sealed, &sealed[..19]).is_err());
    let mut foreign = sealed.clone();
    foreign[0].key = "outside-approved-program-set".to_owned();
    assert!(validate_inventory(&sealed, &foreign).is_err());
    let mut changed = sealed.clone();
    changed[0].input = digest(99);
    assert!(
        validate_inventory(&sealed, &changed).is_err(),
        "canonical name cannot hide changed input"
    );
    assert!(
        validate_inventory(&foreign, &foreign).is_err(),
        "the seal itself must name the approved set"
    );
}

#[test]
fn e5_i_manifest_records_terminal_states_without_rerun() {
    let mut manifest = Manifest {
        entries: programs()
            .into_iter()
            .map(|program| WorkerEntry {
                program,
                state: WorkerState::Pending,
            })
            .collect(),
    };
    assert!(advance(&mut manifest, "bst", WorkerState::Running).is_ok());
    assert_eq!(
        manifest.entries[0].state,
        WorkerState::Running,
        "record Running before launch"
    );
    assert!(advance(&mut manifest, "bst", WorkerState::Complete(digest(1))).is_ok());
    assert_eq!(manifest.entries[0].state, WorkerState::Complete(digest(1)));
    let terminal = manifest.clone();
    assert!(advance(&mut manifest, "bst", WorkerState::Running).is_err());
    assert_eq!(
        manifest, terminal,
        "rejected restart cannot mutate the manifest"
    );
    assert!(
        advance(&mut manifest, "avl", WorkerState::Complete(digest(2))).is_err(),
        "Pending cannot skip Running"
    );
    assert!(advance(&mut manifest, "avl", WorkerState::Running).is_ok());
    assert!(
        advance(
            &mut manifest,
            "avl",
            WorkerState::Failure(FailureKind::Timeout)
        )
        .is_ok()
    );
    let failed = manifest.clone();
    assert!(advance(&mut manifest, "avl", WorkerState::Running).is_err());
    assert_eq!(
        manifest, failed,
        "failed programs need external disposition, not automatic rerun"
    );
    assert!(advance(&mut manifest, "unknown-program", WorkerState::Running).is_err());
}

#[test]
fn e5_i_worker_failures_keep_exact_incomplete_outcome_kind() {
    for failure in [
        FailureKind::Timeout,
        FailureKind::Oom,
        FailureKind::Unknown("injected solver reason".to_owned()),
        FailureKind::Decline("injected analysis reason".to_owned()),
        FailureKind::Missing,
        FailureKind::Invalid("truncated payload".to_owned()),
    ] {
        assert_eq!(
            terminal_state(WorkerOutcome::Failure(failure.clone())),
            WorkerState::Failure(failure)
        );
    }
    assert_eq!(
        terminal_state(WorkerOutcome::Complete(digest(7))),
        WorkerState::Complete(digest(7))
    );
}

fn resource_seal() -> ResourceSeal {
    let host = "injected-host".to_owned();
    ResourceSeal {
        host: host.clone(),
        physical_mib: 100,
        headroom_mib: 10,
        guards: REQUIRED_GUARDS,
        reservations: [
            ("h1", WorkClass::Heavy, 40),
            ("h2", WorkClass::Heavy, 40),
            ("h3", WorkClass::Heavy, 1),
            ("s1", WorkClass::Small, 8),
            ("s2", WorkClass::Small, 1),
            ("s3", WorkClass::Small, 1),
            ("s4", WorkClass::Small, 1),
        ]
        .into_iter()
        .map(|(id, class, cap_mib)| Reservation {
            id: id.to_owned(),
            host: host.clone(),
            class,
            cap_mib,
        })
        .collect(),
    }
}
fn ids(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_owned()).collect()
}

#[test]
fn e5_i_reservations_obey_sealed_caps_and_two_heavy_three_total() {
    let seal = resource_seal();
    assert!(validate_resources(&seal, &ids(&["h1", "h2", "s1"])).is_ok());
    assert!(
        validate_resources(&seal, &ids(&["h1", "h2", "h3"])).is_err(),
        "three heavy workers forbidden even below memory cap"
    );
    assert!(
        validate_resources(&seal, &ids(&["s1", "s2", "s3", "s4"])).is_err(),
        "four small workers still exceed total"
    );
    assert!(validate_resources(&seal, &ids(&["h1", "h1"])).is_err());
    assert!(validate_resources(&seal, &ids(&["unsealed"])).is_err());
    let mut tight = seal.clone();
    tight.physical_mib = 89;
    assert!(
        validate_resources(&tight, &ids(&["h1", "h2"])).is_err(),
        "aggregate sealed caps exceed physical minus headroom"
    );
    let mut wrong_host = seal.clone();
    wrong_host.reservations[0].host = "another-injected-host".to_owned();
    assert!(validate_resources(&wrong_host, &ids(&["h1"])).is_err());
    let mut wrong_guard = seal.clone();
    wrong_guard.guards.query_seconds = 601;
    assert!(
        validate_resources(&wrong_guard, &ids(&["h1"])).is_err(),
        "guard change is not an optimization knob"
    );
    let mut underflow = seal.clone();
    underflow.headroom_mib = 101;
    assert!(validate_resources(&underflow, &[]).is_err());
    let mut overflow = seal.clone();
    overflow.physical_mib = u64::MAX;
    overflow.headroom_mib = 0;
    overflow.reservations[0].cap_mib = u64::MAX;
    overflow.reservations[1].cap_mib = 1;
    assert!(
        validate_resources(&overflow, &ids(&["h1", "h2"])).is_err(),
        "sum must not wrap"
    );
}

fn envelope() -> TransportEnvelope {
    TransportEnvelope {
        program: programs()[0].clone(),
        semantic_key: digest(1),
        body: digest(2),
        payload: digest(3),
        exports: digest(4),
        toolchain: digest(5),
        launch: digest(6),
        source: digest(7),
        host: "attested-injected-host".to_owned(),
        host_provenance: digest(8),
    }
}

#[test]
fn e5_i_transport_rejects_each_changed_attested_identity() {
    let seal = envelope();
    assert!(validate_transport(&seal, &seal).is_ok());
    for field in [
        TransportField::Program,
        TransportField::SemanticKey,
        TransportField::Body,
        TransportField::Payload,
        TransportField::Exports,
        TransportField::Toolchain,
        TransportField::Launch,
        TransportField::Source,
        TransportField::Host,
        TransportField::HostProvenance,
    ] {
        let mut changed = seal.clone();
        match field {
            TransportField::Program => changed.program.input = digest(99),
            TransportField::SemanticKey => changed.semantic_key = digest(99),
            TransportField::Body => changed.body = digest(99),
            TransportField::Payload => changed.payload = digest(99),
            TransportField::Exports => changed.exports = digest(99),
            TransportField::Toolchain => changed.toolchain = digest(99),
            TransportField::Launch => changed.launch = digest(99),
            TransportField::Source => changed.source = digest(99),
            TransportField::Host => changed.host = "unattested-host".to_owned(),
            TransportField::HostProvenance => changed.host_provenance = digest(99),
        }
        assert_eq!(
            validate_transport(&seal, &changed),
            Err(TransportError { field })
        );
    }
}

fn row(key: Option<&str>, diagnostic: &str, kind: Kind, reasons: &str) -> IdentityRow {
    IdentityRow {
        canonical: key.map(str::to_owned),
        diagnostic: diagnostic.to_owned(),
        kind,
        reasons: reasons.to_owned(),
    }
}

#[test]
fn e5_i_identity_join_preserves_gross_transitions_and_unmapped_rows() {
    let before = vec![
        row(Some("f::_1@d0"), "old-17", Kind::Ref, "first;second"),
        row(Some("f::_2@d0"), "old-18", Kind::Raw, "opaque"),
        row(Some("old-field"), "old-19", Kind::Owning, ""),
    ];
    let after = vec![
        row(Some("f::_2@d0"), "new-99", Kind::Ref, ""),
        row(
            Some("array::element@d0"),
            "new-17",
            Kind::Raw,
            "coverage-held",
        ),
        row(None, "old-19", Kind::Owning, "missing-canonical"),
        row(
            Some("f::_1@d0"),
            "new-18",
            Kind::Raw,
            "second;first;retirement",
        ),
    ];
    let joined =
        join_identities(&before, &after).expect("well-keyed rows with explicit unmapped channel");
    assert_eq!(joined.common.len(), 2);
    assert_eq!(joined.added, vec![after[1].clone()]);
    assert_eq!(joined.removed, vec![before[2].clone()]);
    assert_eq!(
        joined.unmapped,
        vec![UnmappedIdentity {
            side: Side::After,
            row: after[2].clone()
        }]
    );
    assert!(!joined.complete(), "Unmapped is never silently complete");
    assert_eq!(
        joined.gross,
        vec![
            GrossTransition {
                before: Kind::Raw,
                after: Kind::Ref,
                count: 1
            },
            GrossTransition {
                before: Kind::Ref,
                after: Kind::Raw,
                count: 1
            }
        ],
        "net zero cannot hide opposite transitions"
    );
    assert_eq!(
        joined.common[0].before_reasons,
        BTreeSet::from(["first".to_owned(), "second".to_owned()])
    );
    let mut duplicate = after.clone();
    duplicate.push(after[0].clone());
    assert!(
        join_identities(&before, &duplicate).is_err(),
        "duplicate canonical key must fail"
    );
}

#[test]
fn e5_i_reason_membership_includes_every_composite_component() {
    assert_eq!(
        reason_members(" first ; second;first;; third "),
        BTreeSet::from(["first".to_owned(), "second".to_owned(), "third".to_owned()])
    );
    assert!(
        !reason_members("first;second-extra").contains("second"),
        "substring matches are not component membership"
    );
}

#[test]
fn e5_i_restoration_requires_exact_source_digest() {
    assert!(validate_restoration(digest(1), digest(1)).is_ok());
    assert_eq!(
        validate_restoration(digest(1), digest(2)),
        Err(RestorationError {
            expected: digest(1),
            observed: digest(2)
        })
    );
}
