//! R345 synthetic export records, not a native era-5b decoder or measurement.
use ownership_fields::{
    adapter::*,
    emission::{GrantStatus, Kind},
    export::*,
};

use super::*;

fn absent(owner: EvidenceOwner, field: &'static str) -> Missing {
    Missing {
        owner,
        reason: MissingReason::Field(field),
    }
}
pub(super) fn fixture() -> (AcceptedInputs, Vec<Row>) {
    let artifact = Digest([9; 32]);
    let frame = Frame {
        program: ProgramId("synthetic-fold".into()),
        substrate_manifest_sha256: Digest([3; 32]),
        entry_path: "synthetic/entry".into(),
        entry_sha256: Digest([4; 32]),
        producer: ProducerIdentity {
            source: "producer-source".into(),
            analysis_digest: Digest([5; 32]),
        },
        certificate: CertificateIdentity {
            source: "certificate-source".into(),
            full_analysis_digest: Digest([6; 32]),
        },
        analysis_minus_licensing_digest: Digest([7; 32]),
        configuration: Digest([2; 32]),
        toolchain: Digest([8; 32]),
        dependency_digest: Digest([10; 32]),
        accepted_round: 2,
        snapshot_offset: 100,
        source_frame: SourceFrame::L01DoublePrime,
    };
    let declaration = DeclarationKey {
        call: CallKey {
            construction: 101,
            caller: FunctionId("caller-key".into()),
            block: 4,
            statement: 2,
            callee: FunctionId("callee-key".into()),
        },
        guard: EquationId {
            construction: 101,
            ordinal: 8,
        },
        boundary: 3,
        argument: 0,
    };
    let mut records = BTreeMap::new();
    fn reference<T: FactTag>(
        records: &mut BTreeMap<RecordKey, FactFamily>,
        artifact: Digest,
    ) -> Evidence<FactRef<T>> {
        let record = RecordKey {
            artifact,
            row: records.len() as u32,
        };
        records.insert(record, T::FAMILY);
        Ok(FactRef::new(record))
    }
    macro_rules! reference {
        () => {
            reference(&mut records, artifact)
        };
    }
    let f1 = FieldKey("field1".into());
    let f2 = FieldKey("field2".into());
    let node = StaticNode {
        construction: 101,
        var: 7,
    };
    let k = EvidenceKey {
        model: artifact.0,
        configuration: frame.configuration.0,
        site: site(40),
        generation: 9001,
    };
    let occurrence = Occurrence {
        declaration: declaration.clone(),
        source: SourceInstance {
            endpoint: EquationId {
                construction: 101,
                ordinal: 70,
            },
            lineage: SourceLineage::Exact(vec![declaration.call.clone()]),
        },
        node,
        key: k,
        generation_recipe: reference!(),
        transported_key: Ok(k),
    };
    let row = Row {
        declaration_key: Ok(declaration.clone()),
        baseline_kind: Kind::Raw,
        disposition: Disposition::Selected(Ok(Selection {
            guard: declaration.guard,
            required: Valuations {
                owning: BTreeMap::from([(node, true)]),
                guards: BTreeMap::from([(declaration.guard, true)]),
            },
            accepted: Valuations {
                owning: BTreeMap::from([(node, true)]),
                guards: BTreeMap::from([(declaration.guard, true)]),
            },
            required_closed_frame: true,
            closed_call_world: true,
            validation: reference!(),
            attestation: Ok(frame.clone()),
        })),
        certificate: Ok(Certificate::Member {
            internal: reference!(),
            member: reference!(),
        }),
        required_field_set: Ok(BTreeSet::from([f1.clone()])),
        selected_global_field_scheme: Ok(GlobalFieldScheme {
            fields: BTreeMap::from([(f1.clone(), field(1)), (f2.clone(), field(2))]),
            owning: BTreeSet::from([f1, f2]),
            support: reference!(),
            selection_basis: reference!(),
            frame: Ok(frame.clone()),
        }),
        requirements: reference!(),
        checked_laws: reference!(),
        occurrence: Ok(occurrence.clone()),
        companions: Companions {
            types: reference!(),
            readers: reference!(),
            own_call: reference!(),
            construction: reference!(),
            field_uses: reference!(),
            transaction: reference!(),
            declaration: reference!(),
            copies: reference!(),
            signatures: reference!(),
            calls: reference!(),
            frees: reference!(),
            leak_coverage: reference!(),
            hoist: reference!(),
            custody: reference!(),
            raw_audit: reference!(),
        },
        extra_close_obligations: Ok(vec![ExtraClose {
            site: k.site,
            path: vec![],
            kind: CloseKind::ScopeExit,
            owner: Ok(k),
            reason: ExtraCloseReason::LiveAtScopeExit,
            required_proofs: reference!(),
            depth: reference!(),
        }]),
    };
    let manifest = Manifest {
        schema: 1,
        artifact_digest: artifact,
        frame: Ok(frame),
        family_complete: Ok(true),
        declaration_keys: Ok(BTreeSet::from([declaration.clone()])),
        transport: Ok(FamilyTransport::SameEpoch),
    };
    (
        AcceptedInputs {
            manifest,
            records,
            occurrences: Ok(BTreeMap::from([(declaration, occurrence)])),
        },
        vec![row],
    )
}
fn selected(row: &mut Row) -> &mut Selection {
    let Disposition::Selected(Ok(value)) = &mut row.disposition else {
        panic!("fixture selection")
    };
    value
}
fn grant_result(
    inputs: &AcceptedInputs,
    rows: &[Row],
) -> Evidence<ownership_fields::emission::Grant> {
    prepare(inputs, &inputs.manifest, rows)?.owning_grant(rows[0].declaration_key.as_ref().unwrap())
}

#[test]
fn adapter_complete_selected_grant_authorizes_only_the_attested_overlay() {
    let (inputs, rows) = fixture();
    assert_ne!(
        inputs
            .manifest
            .frame
            .as_ref()
            .unwrap()
            .producer
            .analysis_digest,
        inputs
            .manifest
            .frame
            .as_ref()
            .unwrap()
            .certificate
            .full_analysis_digest
    );
    assert_eq!(rows[0].baseline_kind, Kind::Raw);
    assert_eq!(rows[0].required_field_set.as_ref().unwrap().len(), 1);
    assert_eq!(
        rows[0]
            .selected_global_field_scheme
            .as_ref()
            .unwrap()
            .owning
            .len(),
        2
    );
    let prepared = prepare(&inputs, &inputs.manifest, &rows).unwrap();
    let grant = prepared
        .owning_grant(rows[0].declaration_key.as_ref().unwrap())
        .unwrap();
    assert_eq!(
        (grant.kind, grant.status),
        (Kind::Owning, GrantStatus::Selected)
    );
    assert_eq!(grant.transport, Some(grant.key));
    assert_eq!(grant.key.generation, 9001);
    let mut facts = super::call_facts(grant.key);
    assert!(prepared.companion(&rows[0].companions.own_call).is_ok());
    assert!(ownership_fields::emission::admit_call(&grant, &facts).is_ok());
    facts
        .references
        .push(ownership_fields::emission::ReferenceInterval {
            generation: grant.key.generation,
            live: facts.call,
            protected: None,
        });
    assert!(
        ownership_fields::emission::admit_call(&grant, &facts).is_err(),
        "kind grant is not P1′-E permission"
    );
    assert_eq!(
        prepared
            .extra_closes(rows[0].declaration_key.as_ref().unwrap())
            .unwrap()
            .len(),
        1
    );
}

#[test]
fn adapter_conditional_certificate_is_not_a_selected_grant() {
    let (inputs, mut rows) = fixture();
    rows[0].disposition = Disposition::Conditional;
    assert_eq!(
        grant_result(&inputs, &rows).unwrap_err(),
        Missing {
            owner: EvidenceOwner::Era5b,
            reason: MissingReason::Conditional
        }
    );
}

#[test]
fn adapter_missing_global_scheme_is_not_reconstructed_from_member_requirements() {
    let (inputs, mut rows) = fixture();
    let missing = absent(EvidenceOwner::Era5b, "selected_global_field_scheme");
    rows[0].selected_global_field_scheme = Err(missing.clone());
    assert_eq!(grant_result(&inputs, &rows).unwrap_err(), missing);
}

#[test]
fn adapter_preserves_nested_hold_variants_payloads_and_missing_owner() {
    let (inputs, mut rows) = fixture();
    for hold in [
        LicensingHold::Call(CallError::Internal(InternalError::Coverage(417))),
        LicensingHold::Call(CallError::Internal(InternalError::AmbiguousRoute {
            choices: 2,
            from: StaticNode {
                construction: 101,
                var: 7,
            },
            to: StaticNode {
                construction: 101,
                var: 8,
            },
        })),
        LicensingHold::Call(CallError::Internal(InternalError::Unsupported(
            InternalSite::ConsumedCellNotRefilled,
        ))),
        LicensingHold::Call(CallError::Internal(InternalError::Unsupported(
            InternalSite::SinkOnView,
        ))),
        LicensingHold::Caller(CallerHold::MissingReset),
    ] {
        rows[0].disposition = Disposition::Held(hold.clone());
        assert!(!rows[0].required_field_set.as_ref().unwrap().is_empty());
        assert_eq!(
            grant_result(&inputs, &rows).unwrap_err(),
            Missing {
                owner: EvidenceOwner::Era5b,
                reason: MissingReason::Held(hold)
            }
        );
    }
    let missing = absent(EvidenceOwner::NativeIdentity, "invocation binder");
    rows[0].disposition = Disposition::Missing(missing.clone());
    assert_eq!(grant_result(&inputs, &rows).unwrap_err(), missing);
}

#[test]
fn adapter_rejects_absent_or_different_frame_attestation() {
    let (inputs, rows) = fixture();
    let mut missing = rows.clone();
    let why = absent(EvidenceOwner::FrameQualification, "frame_attestation");
    selected(&mut missing[0]).attestation = Err(why.clone());
    assert_eq!(grant_result(&inputs, &missing).unwrap_err(), why);
    for n in 0..5 {
        let mut bad = rows.clone();
        let frame = selected(&mut bad[0]).attestation.as_mut().unwrap();
        match n {
            0 => frame.producer.analysis_digest = frame.certificate.full_analysis_digest,
            1 => frame.accepted_round += 1,
            2 => frame.snapshot_offset += 1,
            3 => frame.configuration = Digest([11; 32]),
            _ => frame.source_frame = SourceFrame::L01TriplePrime,
        }
        assert!(
            matches!(
                grant_result(&inputs, &bad).unwrap_err().reason,
                MissingReason::Frame(_)
            ),
            "frame case {n}"
        );
    }
}

#[test]
fn adapter_family_is_exact_and_never_defaults_missing_to_empty() {
    let (inputs, rows) = fixture();
    let why = absent(EvidenceOwner::Era5b, "family_complete");
    let mut missing = inputs.manifest.clone();
    missing.family_complete = Err(why.clone());
    assert_eq!(prepare(&inputs, &missing, &rows).unwrap_err(), why);
    let duplicate = vec![rows[0].clone(), rows[0].clone()];
    assert!(matches!(
        prepare(&inputs, &inputs.manifest, &duplicate)
            .unwrap_err()
            .reason,
        MissingReason::DuplicateDeclaration(_)
    ));
    assert_eq!(
        prepare(&inputs, &inputs.manifest, &[]).unwrap_err().reason,
        MissingReason::DeclarationSet
    );
    let mut false_complete = inputs.manifest.clone();
    false_complete.family_complete = Ok(false);
    assert_eq!(
        prepare(&inputs, &false_complete, &rows).unwrap_err().reason,
        MissingReason::IncompleteFamily
    );
}

#[test]
fn adapter_validates_selected_values_scheme_and_member_custody_receipt() {
    let (inputs, rows) = fixture();
    assert!(grant_result(&inputs, &rows).is_ok());
    for n in 0..6 {
        let mut bad = rows.clone();
        match n {
            0 => selected(&mut bad[0]).accepted.guards.clear(),
            1 => selected(&mut bad[0]).accepted.owning.clear(),
            2 => selected(&mut bad[0]).closed_call_world = false,
            3 => {
                selected(&mut bad[0]).validation =
                    Err(absent(EvidenceOwner::Era5b, "member_selection_validation"))
            }
            4 => {
                bad[0]
                    .selected_global_field_scheme
                    .as_mut()
                    .unwrap()
                    .owning
                    .clear();
            }
            _ => {
                bad[0]
                    .selected_global_field_scheme
                    .as_mut()
                    .unwrap()
                    .support = Err(absent(EvidenceOwner::Era5b, "negative_store_inventory"))
            }
        }
        assert!(grant_result(&inputs, &bad).is_err(), "selection case {n}");
    }
}

#[test]
fn adapter_conditional_field_support_is_not_a_global_selection_basis() {
    let (mut inputs, mut rows) = fixture();
    let why = absent(
        EvidenceOwner::Era5b,
        "selected_global_field_scheme.selection_basis",
    );
    let basis = rows[0]
        .selected_global_field_scheme
        .as_ref()
        .unwrap()
        .selection_basis
        .clone();
    rows[0]
        .selected_global_field_scheme
        .as_mut()
        .unwrap()
        .selection_basis = Err(why.clone());
    assert_eq!(grant_result(&inputs, &rows).unwrap_err(), why);
    rows[0]
        .selected_global_field_scheme
        .as_mut()
        .unwrap()
        .selection_basis = basis.clone();
    inputs
        .records
        .insert(basis.unwrap().record, FactFamily::GlobalFieldSupport);
    assert_eq!(
        grant_result(&inputs, &rows).unwrap_err().reason,
        MissingReason::Companion(FactFamily::SelectedGlobalFields)
    );
}

#[test]
fn adapter_static_nodes_do_not_become_dynamic_generations_or_name_joins() {
    let (inputs, rows) = fixture();
    for n in 0..4 {
        let mut bad = rows.clone();
        let occurrence = bad[0].occurrence.as_mut().unwrap();
        match n {
            0 => occurrence.key.generation = u64::from(occurrence.node.var),
            1 => occurrence.declaration.argument += 1,
            2 => occurrence.source.endpoint.construction += 100,
            _ => occurrence.transported_key.as_mut().unwrap().site.occurrence += 1,
        }
        assert!(grant_result(&inputs, &bad).is_err(), "identity case {n}");
    }
    let why = absent(EvidenceOwner::NativeIdentity, "generation_recipe");
    let mut bad = rows.clone();
    bad[0].occurrence.as_mut().unwrap().generation_recipe = Err(why.clone());
    assert_eq!(grant_result(&inputs, &bad).unwrap_err(), why);
}

#[test]
fn adapter_extra_close_absences_are_site_holds_not_waiver_receipts() {
    let (inputs, rows) = fixture();
    let decl = rows[0].declaration_key.as_ref().unwrap();
    for n in 0..4 {
        let mut bad = rows.clone();
        let why = absent(
            EvidenceOwner::Emission,
            [
                "extra_close_obligations",
                "all_roots",
                "bounded_depth",
                "owner_generation",
            ][n],
        );
        match n {
            0 => bad[0].extra_close_obligations = Err(why.clone()),
            1 => {
                bad[0].extra_close_obligations.as_mut().unwrap()[0].required_proofs =
                    Err(why.clone())
            }
            2 => bad[0].extra_close_obligations.as_mut().unwrap()[0].depth = Err(why.clone()),
            _ => bad[0].extra_close_obligations.as_mut().unwrap()[0].owner = Err(why.clone()),
        }
        let prepared = prepare(&inputs, &inputs.manifest, &bad).unwrap();
        assert!(
            prepared.owning_grant(decl).is_ok(),
            "extra close is a separate site obligation"
        );
        assert_eq!(prepared.extra_closes(decl).unwrap_err(), why);
    }
}

#[test]
fn adapter_companion_record_kind_and_exact_artifact_are_checked() {
    let (mut inputs, rows) = fixture();
    let own_call = rows[0].companions.own_call.as_ref().unwrap().record;
    inputs.records.insert(own_call, FactFamily::ReaderRoles);
    let prepared = prepare(&inputs, &inputs.manifest, &rows).unwrap();
    assert_eq!(
        prepared
            .companion(&rows[0].companions.own_call)
            .unwrap_err()
            .reason,
        MissingReason::Companion(FactFamily::OwnCall)
    );
    let unknown = Ok(FactRef::<OwnCall>::new(RecordKey {
        artifact: Digest([55; 32]),
        row: own_call.row,
    }));
    assert!(prepared.companion(&unknown).is_err());
    let why = absent(EvidenceOwner::Emission, "helper_lowering");
    let missing: Evidence<FactRef<OwnCall>> = Err(why.clone());
    assert_eq!(prepared.companion(&missing).unwrap_err(), why);
}

#[test]
fn adapter_mixed_epoch_manifest_needs_the_per_entry_family_comparison() {
    let (mut inputs, rows) = fixture();
    let why = absent(EvidenceOwner::FrameQualification, "R343_family_comparison");
    inputs.manifest.transport = Ok(FamilyTransport::Compared(Err(why.clone())));
    assert_eq!(prepare(&inputs, &inputs.manifest, &rows).unwrap_err(), why);
}

#[test]
fn adapter_extra_close_inventory_rejects_duplicates_and_contradictory_reasons() {
    let (inputs, rows) = fixture();
    let decl = rows[0].declaration_key.as_ref().unwrap();
    let mut duplicate = rows.clone();
    let closes = duplicate[0].extra_close_obligations.as_mut().unwrap();
    let site = closes[0].site;
    closes.push(closes[0].clone());
    assert_eq!(
        prepare(&inputs, &inputs.manifest, &duplicate)
            .unwrap()
            .extra_closes(decl)
            .unwrap_err()
            .reason,
        MissingReason::DuplicateClose(site)
    );
    let mut contradictory = rows.clone();
    contradictory[0].extra_close_obligations.as_mut().unwrap()[0].reason =
        ExtraCloseReason::LiveAtUnwind;
    assert_eq!(
        prepare(&inputs, &inputs.manifest, &contradictory)
            .unwrap()
            .extra_closes(decl)
            .unwrap_err()
            .reason,
        MissingReason::CloseReason(site)
    );
}
