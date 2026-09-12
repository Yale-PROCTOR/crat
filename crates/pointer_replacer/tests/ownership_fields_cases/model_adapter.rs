//! R348 synthetic reductions. No cache read or native corpus translation.
use ownership_fields::{
    boundary::*,
    emission::{self, EmitHold, OwnerInput},
    export::{
        Digest, Evidence, EvidenceOwner, FactFamily, FactRef, Missing, MissingReason, ProgramId,
        RecordKey, SourceFrame,
    },
    free_sites::*,
    model_adapter as model,
};

use super::*;

fn missing(owner: EvidenceOwner, name: &'static str) -> Missing {
    Missing {
        owner,
        reason: MissingReason::Field(name),
    }
}
fn slot(owner: u32, local: u32, depth: u8) -> model::ModelSlot {
    model::ModelSlot {
        owner: OwnerId(owner),
        local,
        depth,
    }
}
struct Fixture {
    frame: model::ModelFrame,
    inputs: model::AcceptedInputs,
    pins: Evidence<model::ConsumptionPins>,
}
impl Fixture {
    fn new() -> Self {
        let frame = model::ModelFrame {
            source_frame: SourceFrame::L01DoublePrime,
            producer_source: "synthetic-producer".into(),
            analyses_tree: "synthetic-analyses".into(),
            analysis_digest: Digest([1; 32]),
            configuration_digest: Digest([2; 32]),
            substrate_digest: Digest([3; 32]),
            manifest_digest: Digest([4; 32]),
            program: ProgramId("synthetic-heman".into()),
            fingerprint: Digest([5; 32]),
            cache_root: "synthetic-cache-not-opened".into(),
            namespace: "era5a-model-cache-v1".into(),
            entry_path: "synthetic-cache-not-opened/entry.json".into(),
            entry_sha256: Digest([6; 32]),
            payload_sha256: Digest([7; 32]),
            export_sha256: Digest([8; 32]),
            toolchain_digest: Digest([9; 32]),
            dependency_digest: Digest([10; 32]),
            launch_digest: Digest([11; 32]),
        };
        let pins = Ok(model::ConsumptionPins {
            role: model::ExecutionRole::CacheOnly,
            toolchain_digest: frame.toolchain_digest,
            dependency_digest: frame.dependency_digest,
            launch_digest: frame.launch_digest,
            program: frame.program.clone(),
        });
        let inputs = model::AcceptedInputs {
            frame: Ok(frame.clone()),
            entry_accepted: Ok(true),
            model: Ok(BTreeMap::new()),
            required_bindings: Ok(BTreeSet::new()),
            bindings: Ok(Vec::new()),
            records: BTreeMap::new(),
            emission_configuration: Digest([12; 32]),
        };
        Self {
            frame,
            inputs,
            pins,
        }
    }

    fn bind(&mut self, subject: model::ModelSlot, occurrence: u32, generation: u64) -> EvidenceKey {
        let key = EvidenceKey {
            model: self.frame.entry_sha256.0,
            configuration: self.inputs.emission_configuration.0,
            site: SiteId {
                owner: subject.owner,
                occurrence,
            },
            generation,
        };
        self.inputs
            .model
            .as_mut()
            .unwrap()
            .insert(subject, Kind::Owning);
        self.inputs
            .required_bindings
            .as_mut()
            .unwrap()
            .insert(key.site);
        let record = RecordKey {
            artifact: Digest([33; 32]),
            row: self.inputs.bindings.as_ref().unwrap().len() as u32,
        };
        self.inputs
            .records
            .insert(record, FactFamily::GenerationRecipe);
        self.inputs.bindings.as_mut().unwrap().push(model::Binding {
            subject,
            key,
            generation_recipe: Ok(FactRef::new(record)),
            transport: Ok(key),
        });
        key
    }

    fn grant(&self, subject: model::ModelSlot, key: EvidenceKey) -> Evidence<model::ModelGrant> {
        model::prepare(&self.frame, &self.inputs, &self.pins)?.owning_grant(subject, key.site)
    }
}
fn owner_slot(grant: &model::ModelGrant, pointee: &str) -> SignatureSlot {
    SignatureSlot {
        key: grant.grant.key,
        ty: BoundaryType::Owner(OwnerType {
            pointee: pointee.into(),
            optional: false,
        }),
        grant: Some(grant.grant.clone()),
        borrow_origin: None,
    }
}
fn ordinary(key: EvidenceKey) -> model::ShapeEvidence {
    model::ShapeEvidence {
        key,
        shape: Ok(model::AllocationShape::Ordinary),
    }
}
fn free(sink: &model::ModelGrant, owner: EvidenceKey, name: &str) -> String {
    let k = sink.grant.key;
    let planned = plan_frees(
        &BTreeSet::from([k]),
        &[FreeSite {
            sink: k,
            owner,
            expression: name.into(),
            optional_storage: false,
            casts: vec![CastKind::PointerToVoid],
            exact_owner_relation: Some((owner, k)),
            allocation_base: Some(k),
            allocator_layout: Some(k),
            grant: sink.grant.clone(),
            call: call_facts(k),
        }],
    )
    .unwrap();
    assert_eq!(planned[&k].key, k);
    planned[&k].code.clone()
}

#[test]
fn model_owning_kind_is_a_grant_without_a_licensing_certificate() {
    let mut f = Fixture::new();
    let subject = slot(1, 45, 1);
    let key = f.bind(subject, 45, 9001);
    let result = f.grant(subject, key).unwrap();
    assert_eq!(result.grant.kind, Kind::Owning);
    assert_eq!(result.grant.status, GrantStatus::Selected);
    assert_eq!(result.grant.transport, Some(key));
    assert_eq!(result.receipt.frame, f.frame);
    assert_eq!(result.receipt.subject, subject);
    assert_eq!(result.receipt.key, key);
    assert_ne!(key.generation, u64::from(subject.local));
    assert_ne!(key.configuration, f.frame.configuration_digest.0);
}

#[test]
fn model_raw_ref_absent_or_unaccepted_kind_returns_typed_missing() {
    let mut f = Fixture::new();
    let subject = slot(1, 45, 1);
    let key = f.bind(subject, 45, 9001);
    for kind in [Kind::Raw, Kind::Ref] {
        f.inputs.model.as_mut().unwrap().insert(subject, kind);
        assert_eq!(
            f.grant(subject, key).unwrap_err(),
            Missing {
                owner: EvidenceOwner::AcceptedModel,
                reason: MissingReason::ModelNotOwning(kind)
            }
        );
    }
    f.inputs.model.as_mut().unwrap().remove(&subject);
    assert_eq!(
        f.grant(subject, key).unwrap_err(),
        missing(EvidenceOwner::AcceptedModel, "model.slot_kind")
    );
    f.inputs
        .model
        .as_mut()
        .unwrap()
        .insert(subject, Kind::Owning);
    f.inputs.entry_accepted = Ok(false);
    assert_eq!(
        f.grant(subject, key).unwrap_err(),
        missing(EvidenceOwner::AcceptedModel, "accepted_entry")
    );
    let why = missing(EvidenceOwner::AcceptedModel, "accepted_model");
    f.inputs.model = Err(why.clone());
    f.inputs.entry_accepted = Ok(true);
    assert_eq!(f.grant(subject, key).unwrap_err(), why);
}

#[test]
fn model_grants_check_all_five_pins_and_frame_identity() {
    let mut f = Fixture::new();
    let subject = slot(1, 45, 1);
    let key = f.bind(subject, 45, 9001);
    for n in 0..5 {
        let mut pins = f.pins.clone();
        let p = pins.as_mut().unwrap();
        match n {
            0 => p.role = model::ExecutionRole::Analysis,
            1 => p.toolchain_digest = Digest([20; 32]),
            2 => p.dependency_digest = Digest([20; 32]),
            3 => p.launch_digest = Digest([20; 32]),
            _ => p.program = ProgramId("wrong-program".into()),
        }
        assert!(
            model::prepare(&f.frame, &f.inputs, &pins).is_err(),
            "pin {n}"
        );
    }
    for n in 0..7 {
        let mut inputs = f.inputs.clone();
        let frame = inputs.frame.as_mut().unwrap();
        match n {
            0 => frame.entry_sha256 = Digest([20; 32]),
            1 => frame.payload_sha256 = Digest([20; 32]),
            2 => frame.export_sha256 = Digest([20; 32]),
            3 => frame.fingerprint = Digest([20; 32]),
            4 => frame.analysis_digest = Digest([20; 32]),
            5 => frame.manifest_digest = Digest([20; 32]),
            _ => frame.cache_root = "wrong root".into(),
        }
        assert!(
            model::prepare(&f.frame, &inputs, &f.pins).is_err(),
            "frame {n}"
        );
    }
    let why = missing(EvidenceOwner::FrameQualification, "five_consumption_pins");
    assert_eq!(
        model::prepare(&f.frame, &f.inputs, &Err(why.clone())).unwrap_err(),
        why
    );
    assert!(f.grant(subject, key).is_ok());
}

#[test]
fn model_grant_requires_exact_slot_occurrence_and_generation_transport() {
    let mut f = Fixture::new();
    let subject = slot(1, 45, 1);
    let key = f.bind(subject, 45, 9001);
    let why = missing(EvidenceOwner::NativeIdentity, "generation_recipe");
    f.inputs.bindings.as_mut().unwrap()[0].generation_recipe = Err(why.clone());
    assert_eq!(f.grant(subject, key).unwrap_err(), why);
    let mut f = Fixture::new();
    let key = f.bind(subject, 45, 9001);
    let other_depth = slot(1, 45, 2);
    f.inputs
        .model
        .as_mut()
        .unwrap()
        .insert(other_depth, Kind::Owning);
    assert_eq!(
        f.grant(other_depth, key).unwrap_err().reason,
        MissingReason::Occurrence
    );
    let mut wrong = f.inputs.clone();
    wrong.bindings.as_mut().unwrap()[0].key.generation = 45;
    assert!(
        model::prepare(&f.frame, &wrong, &f.pins)
            .unwrap()
            .owning_grant(subject, key.site)
            .is_err()
    );
    let mut duplicate = f.inputs.clone();
    let b = duplicate.bindings.as_ref().unwrap()[0].clone();
    duplicate.bindings.as_mut().unwrap().push(b);
    assert_eq!(
        model::prepare(&f.frame, &duplicate, &f.pins)
            .unwrap_err()
            .reason,
        MissingReason::ModelInventory
    );
    let mut absent = f.inputs.clone();
    absent.bindings.as_mut().unwrap().clear();
    assert_eq!(
        model::prepare(&f.frame, &absent, &f.pins)
            .unwrap_err()
            .reason,
        MissingReason::ModelInventory
    );
}

/// R348-F01: transform_to_coordfield's pl2 is a caller local; the actual
/// parameter is edt_with_payload::payload_out. The source void call leaves
/// the buffer live in its caller. This one-buffer reduction supplies an
/// explicit generated ownership-return/rebind protocol, not a native proof
/// that the original two-buffer call already implements that protocol.
#[test]
fn model_param_heman_roundtrip_needs_returned_responsibility_and_compiles() {
    let mut f = Fixture::new();
    let caller = slot(1, 53, 1);
    let formal = slot(2, 7, 1);
    let actual = f.bind(caller, 53, 901);
    let parameter = f.bind(formal, 7, 901);
    let returned = f.bind(formal, 9000, 901);
    let received = f.bind(caller, 9001, 901);
    let sink = f.bind(caller, 9002, 901);
    let actual = f.grant(caller, actual).unwrap();
    let parameter = f.grant(formal, parameter).unwrap();
    let returned = f.grant(formal, returned).unwrap();
    let received = f.grant(caller, received).unwrap();
    let sink = f.grant(caller, sink).unwrap();
    let signature = Signature {
        owner: OwnerId(2),
        parameters: vec![Parameter {
            index: 0,
            name: "payload_out".into(),
            slot: owner_slot(&parameter, "[f32]"),
        }],
        result: owner_slot(&returned, "[f32]"),
    };
    let mut facts = call_facts(actual.grant.key);
    facts.transfer_cleanup = None;
    let mut call = CallContract {
        site: site(80),
        required_targets: BTreeSet::from([OwnerId(2)]),
        targets: vec![signature.clone()],
        arguments: vec![ArgumentEdge {
            call_site: site(80),
            index: 0,
            actual: actual.grant.key,
            formal: parameter.grant.key,
            expression: "pl2".into(),
            source_type: owner_slot(&actual, "[f32]").ty,
            actual_grant: Some(actual.grant.clone()),
            mode: PassingMode::Move,
            transport: Some((actual.grant.key, parameter.grant.key)),
            borrow_proof: None,
            exclusive_storage: true,
            call_facts: Some(facts),
        }],
    };
    assert_eq!(
        plan_call(&call),
        Err(BoundaryHold::Call),
        "Owning alone cannot drop the live caller's buffer at a void callee exit"
    );
    call.arguments[0].call_facts = Some(call_facts(actual.grant.key));
    let signature = plan_signature(&signature).unwrap();
    let planned = plan_call(&call).unwrap();
    assert_eq!(planned.arguments, ["pl2"]);
    let returned = plan_return(&ReturnEdge {
        source: owner_slot(&parameter, "[f32]"),
        result: owner_slot(&returned, "[f32]"),
        expression: "payload_out".into(),
        take_optional_storage: false,
        exclusive_storage: true,
        transport: Some((parameter.grant.key, returned.grant.key)),
    })
    .unwrap();
    let received_code = model::receiver(
        &received,
        &ordinary(received.grant.key),
        &call_facts(received.grant.key),
        "pl2",
        &OwnerType {
            pointee: "[f32]".into(),
            optional: false,
        },
        &OwnerInput::Transfer {
            expression: format!("edt_with_payload({})", planned.arguments[0]),
        },
    )
    .unwrap();
    let dropped = free(&sink, received.grant.key, "pl2");
    assert_eq!(dropped, "drop(pl2);");
    let code = format!(
        "fn edt_with_payload({})->{}{{payload_out[0]=7.0;{returned}}}fn main(){{let pl2:Box<[f32]>=Box::new([0.0;2]);{}assert_eq!(pl2[0],7.0);{dropped}}}",
        signature.parameters.join(","),
        signature.result,
        received_code.code
    );
    assert!(compile_source(&code, true).status.success());
    let mut live = call.clone();
    let facts = live.arguments[0].call_facts.as_mut().unwrap();
    facts.references.push(emission::ReferenceInterval {
        generation: 901,
        live: facts.call,
        protected: Some(facts.call),
    });
    assert_eq!(plan_call(&live), Err(BoundaryHold::Call));
    println!("SYNTHETIC_MODEL_PARAM_BEGIN\n{code}\nSYNTHETIC_MODEL_PARAM_END");
}

/// R348-F02: ti_buffer_new::ret is a local which flows to the return. Its
/// allocation includes a variable tail beyond vals:[f64;1]; it stays held.
#[test]
fn model_flexible_ti_buffer_return_stays_held_after_kind_grant() {
    let mut f = Fixture::new();
    let subject = slot(1, 14, 1);
    let key = f.bind(subject, 14, 901);
    let grant = f.grant(subject, key).unwrap();
    let expression = "size_of::<TiBuffer>() + (size - 1) * size_of::<f64>()".to_string();
    let shape = model::ShapeEvidence {
        key,
        shape: Ok(model::AllocationShape::FlexibleTail {
            expression: expression.clone(),
        }),
    };
    let result = model::receiver(
        &grant,
        &shape,
        &call_facts(key),
        "ret",
        &OwnerType {
            pointee: "TiBuffer".into(),
            optional: true,
        },
        &OwnerInput::Transfer {
            expression: "ti_buffer_new(size)".into(),
        },
    );
    assert_eq!(
        result,
        Err(model::ReceiverHold::FlexibleTail { expression })
    );
    assert_eq!(grant.grant.kind, Kind::Owning);
}

/// R348-F03: malloc(sizeof(*mut HemanImage)*ncolors) constructs an array of
/// pointer cells. An Owning depth-2 slot does not license an outer Box<Image>.
#[test]
fn model_depth2_elevations_does_not_become_an_outer_box() {
    let mut f = Fixture::new();
    let subject = slot(1, 9, 2);
    let key = f.bind(subject, 9, 901);
    let grant = f.grant(subject, key).unwrap();
    let result = model::receiver(
        &grant,
        &ordinary(key),
        &call_facts(key),
        "elevations",
        &OwnerType {
            pointee: "HemanImage".into(),
            optional: false,
        },
        &OwnerInput::Construct {
            value: "HemanImage { width: 1 }".into(),
            layout: Some(key),
            initialization: Some(key),
        },
    );
    assert_eq!(
        result,
        Err(model::ReceiverHold::ConstructionUnmappable { depth: 2 })
    );
    assert_eq!(grant.grant.kind, Kind::Owning);
}

/// R348-F04: horizon_scan::hull_buffer is an aggregate array allocation. This
/// fixed-extent reduction supplies all three numeric fields and exact layout.
#[test]
fn model_aggregate_initializer_requires_typed_fields_and_layout() {
    let mut f = Fixture::new();
    let subject = slot(1, 242, 1);
    let key = f.bind(subject, 242, 901);
    let sink = f.bind(subject, 9000, 901);
    let grant = f.grant(subject, key).unwrap();
    let sink = f.grant(subject, sink).unwrap();
    let ty = OwnerType {
        pointee: "[KmVec3]".into(),
        optional: false,
    };
    let value = "[KmVec3 { x:0.0, y:0.0, z:0.0 }; 2]";
    let mut input = OwnerInput::Construct {
        value: value.into(),
        layout: Some(key),
        initialization: None,
    };
    assert_eq!(
        model::receiver(
            &grant,
            &ordinary(key),
            &call_facts(key),
            "hull_buffer",
            &ty,
            &input
        ),
        Err(model::ReceiverHold::Consumer(EmitHold::Construction))
    );
    if let OwnerInput::Construct { initialization, .. } = &mut input {
        *initialization = Some(key);
    }
    let planned = model::receiver(
        &grant,
        &ordinary(key),
        &call_facts(key),
        "hull_buffer",
        &ty,
        &input,
    )
    .unwrap();
    let dropped = free(&sink, key, "hull_buffer");
    let code = format!(
        "#[derive(Clone,Copy)]struct KmVec3{{x:f32,y:f32,z:f32}}fn main(){{{}assert_eq!(hull_buffer.len(),2);assert_eq!(hull_buffer[1].z,0.0);{dropped}}}",
        planned.code
    );
    assert!(compile_source(&code, true).status.success());
    for kind in [CloseKind::ScopeExit, CloseKind::Unwind] {
        let graph = BTreeMap::from([(OwnerId(77), DropShape::Leaf)]);
        let mut proof = proofs_for(key, kind);
        let close = implicit_close(key, kind, OwnerId(77), &graph, [8; 32], None, &proof).unwrap();
        assert_eq!(close.receipt(), kind.receipt());
        proof.all_roots = None;
        assert_eq!(
            implicit_close(key, kind, OwnerId(77), &graph, [8; 32], None, &proof),
            Err(CloseHold::MissingProof("all-roots"))
        );
    }
    if let OwnerInput::Construct { layout, .. } = &mut input {
        *layout = None;
    }
    assert_eq!(
        model::receiver(
            &grant,
            &ordinary(key),
            &call_facts(key),
            "hull_buffer",
            &ty,
            &input
        ),
        Err(model::ReceiverHold::Consumer(EmitHold::Construction))
    );
    println!("SYNTHETIC_MODEL_INITIALIZER_BEGIN\n{code}\nSYNTHETIC_MODEL_INITIALIZER_END");
}
