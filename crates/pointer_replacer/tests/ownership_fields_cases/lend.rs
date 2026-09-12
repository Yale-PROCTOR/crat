//! R350 reductions of two heman calls, with synthetic native/bridge proofs.
//! No actual corpus/model/cache run or native identity join is performed.
use ownership_fields::{
    emission::{ReferenceInterval, Span},
    export::{EvidenceOwner, Missing, MissingReason},
    free_sites::*,
    lend::*,
};

use super::*;

fn edge(index: u32, actual: EvidenceKey) -> EdgeKey {
    let mut formal = actual;
    formal.site = SiteId {
        owner: OwnerId(2),
        occurrence: index,
    };
    EdgeKey {
        call: site(80),
        target: OwnerId(2),
        argument: index,
        actual,
        formal,
    }
}
fn lend(index: u32, place: &str, form: FormalForm, payload: Payload) -> LendSite {
    let mut actual = key(index);
    actual.generation = u64::from(index) + 30;
    let edge = edge(index, actual);
    let mut later = actual;
    later.site.occurrence += 100;
    LendSite {
        edge,
        grant: grant(actual),
        place: place.into(),
        payload: payload.clone(),
        requested: RequestedUse::Lend,
        formal: Ok(Formal {
            edge,
            kind: if form == FormalForm::MutableRaw {
                Kind::Raw
            } else {
                Kind::Ref
            },
            form,
            payload,
        }),
        stable_place: Ok(edge),
        non_consuming: Ok(edge),
        retention: Ok(RetentionProof {
            edge,
            outcome: Retention::T1NoRetention,
        }),
        view: Span { start: 10, end: 30 },
        call_span: Span { start: 20, end: 30 },
        protector: Span { start: 20, end: 30 },
        references: Ok(vec![]),
        reference_inventory: Ok(edge),
        peer_inventory: Ok(edge),
        permission: Ok(edge),
        continuation_inventory: Ok(edge),
        continuation: Ok(vec![later]),
    }
}
fn inventory(sites: &[LendSite]) -> CallInventory {
    CallInventory {
        call: sites[0].edge.call,
        targets: sites.iter().map(|s| s.edge.target).collect(),
        arguments: sites.iter().map(|s| s.edge.argument).collect(),
        disjoint_pairs: Ok(sites
            .iter()
            .flat_map(|a| {
                sites
                    .iter()
                    .filter(move |b| {
                        a.edge.target == b.edge.target && a.edge.argument < b.edge.argument
                    })
                    .map(move |b| (a.edge, b.edge))
            })
            .collect()),
    }
}

/// Supply a distinct synthetic certificate for another call/target.
fn at_edge(mut site: LendSite, edge: EdgeKey) -> LendSite {
    site.edge = edge;
    site.formal.as_mut().unwrap().edge = edge;
    site.retention.as_mut().unwrap().edge = edge;
    site.stable_place = Ok(edge);
    site.non_consuming = Ok(edge);
    site.reference_inventory = Ok(edge);
    site.peer_inventory = Ok(edge);
    site.permission = Ok(edge);
    site.continuation_inventory = Ok(edge);
    site
}
fn drop_after(site: &LendSite, name: &str) -> String {
    let owner = site.edge.actual;
    let sink = site.continuation.as_ref().unwrap()[0];
    let forms = plan_frees(
        &BTreeSet::from([sink]),
        &[FreeSite {
            sink,
            owner,
            expression: name.into(),
            optional_storage: false,
            casts: vec![CastKind::PointerToVoid],
            exact_owner_relation: Some((owner, sink)),
            allocation_base: Some(sink),
            allocator_layout: Some(sink),
            grant: grant(sink),
            call: call_facts(sink),
        }],
    )
    .unwrap();
    assert_eq!(forms[&sink].key, sink);
    forms[&sink].code.clone()
}
fn move_refusal_and_compiler_control(sites: &[LendSite], fault: &str, label: &str) {
    let mut moved = sites.to_vec();
    moved[0].requested = RequestedUse::Move;
    assert_eq!(
        plan_call(&inventory(sites), &moved),
        Err(LendHold::MoveInsteadOfLend)
    );
    let output = compile_source(fault, false);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success() && stderr.contains("E0382"),
        "{label}: {stderr}"
    );
    println!(
        "{label}_MOVE_FAULT_BEGIN\n{fault}\n{label}_MOVE_FAULT_END\n{label}_DIAGNOSTIC_BEGIN\n{stderr}{label}_DIAGNOSTIC_END"
    );
}

#[test]
fn two_buffer_edt_lends_raw_views_keeps_both_boxes_and_exact_frees() {
    let sites = vec![
        lend(
            0,
            "pl1",
            FormalForm::MutableRaw,
            Payload::Slice("f32".into()),
        ),
        lend(
            1,
            "pl2",
            FormalForm::MutableRaw,
            Payload::Slice("f32".into()),
        ),
    ];
    let plan = plan_call(&inventory(&sites), &sites).unwrap();
    assert_eq!(plan.arguments[&0], "(pl1).as_mut_ptr()");
    assert_eq!(plan.arguments[&1], "(pl2).as_mut_ptr()");
    for (receipt, site) in plan.receipts.iter().zip(&sites) {
        assert_eq!(receipt.owner_after, site.edge.actual);
        assert_eq!(receipt.continuation, *site.continuation.as_ref().unwrap());
        assert_eq!(receipt.retention, Retention::T1NoRetention);
    }
    let drop1 = drop_after(&sites[0], "pl1");
    let drop2 = drop_after(&sites[1], "pl2");
    let code = format!(
        r#"unsafe fn edt_with_payload(payload_in:*mut f32,payload_out:*mut f32) {{
// SAFETY: the caller supplies separate initialized arrays with two elements;
// this synthetic callee neither stores the pointers nor frees either array.
unsafe {{ *payload_out = *payload_in + 1.0; }}
}}
fn main() {{let mut pl1:Box<[f32]>=Box::new([3.0,4.0]);let mut pl2:Box<[f32]>=Box::new([0.0,0.0]);
// SAFETY: both exact Box allocations stay live and distinct throughout the call.
unsafe {{ edt_with_payload({},{}); }}
assert_eq!(pl1[0],3.0);assert_eq!(pl2[0],4.0);{drop1}{drop2}}}"#,
        plan.arguments[&0], plan.arguments[&1]
    );
    assert!(compile_source(&code, true).status.success());
    let fault = "fn edt_with_payload(payload_in:Box<[f32]>,mut payload_out:Box<[f32]>) {payload_out[0]=payload_in[0]+1.0;} fn main(){let pl1:Box<[f32]>=Box::new([3.0,4.0]);let pl2:Box<[f32]>=Box::new([0.0,0.0]);edt_with_payload(pl1,pl2);assert_eq!(pl1[0],3.0);assert_eq!(pl2[0],4.0);drop(pl1);drop(pl2);}";
    move_refusal_and_compiler_control(&sites, fault, "EDT");
    println!("EDT_LEND_BEGIN\n{code}\nEDT_LEND_END");
}

#[test]
fn transform_to_coordfield_lends_safe_views_and_reuses_boxes_without_owner_return() {
    // Two of the transform's local work arrays; scalar dimensions/offsets are
    // reduced away, not inferred from the real source or the model grant.
    let sites = vec![
        lend(
            0,
            "ff",
            FormalForm::MutableReference,
            Payload::Slice("f32".into()),
        ),
        lend(
            1,
            "dd",
            FormalForm::MutableReference,
            Payload::Slice("f32".into()),
        ),
    ];
    let plan = plan_call(&inventory(&sites), &sites).unwrap();
    assert_eq!(plan.arguments[&0], "&mut *(ff)");
    assert_eq!(plan.arguments[&1], "&mut *(dd)");
    let drop1 = drop_after(&sites[0], "ff");
    let drop2 = drop_after(&sites[1], "dd");
    let second: Vec<_> = sites
        .iter()
        .cloned()
        .map(|s| {
            let mut edge = s.edge;
            edge.call.occurrence += 1;
            let mut s = at_edge(s, edge);
            s.view = Span { start: 40, end: 60 };
            s.call_span = Span { start: 50, end: 60 };
            s.protector = s.call_span;
            s
        })
        .collect();
    let later = plan_call(&inventory(&second), &second).unwrap();
    assert_ne!(plan.receipts[0].edge.call, later.receipts[0].edge.call);
    assert_eq!(
        plan_call(&inventory(&second), &sites),
        Err(LendHold::Identity)
    );
    let code = format!(
        "fn edt(f:&mut [f32],d:&mut [f32]){{d[0]=f[0]+1.0;}}fn transform_to_coordfield(mut ff:Box<[f32]>,mut dd:Box<[f32]>){{edt({},{});assert_eq!(ff[0],2.0);assert_eq!(dd[0],3.0);ff[0]=5.0;edt({},{});assert_eq!(dd[0],6.0);{drop1}{drop2}}}fn main(){{transform_to_coordfield(Box::new([2.0;2]),Box::new([0.0;2]));}}",
        plan.arguments[&0], plan.arguments[&1], later.arguments[&0], later.arguments[&1]
    );
    assert!(compile_source(&code, true).status.success());
    let fault = "fn edt(f:Box<[f32]>,mut d:Box<[f32]>) {d[0]=f[0]+1.0;}fn transform_to_coordfield(mut ff:Box<[f32]>,dd:Box<[f32]>){edt(ff,dd);assert_eq!(ff[0],2.0);assert_eq!(dd[0],3.0);ff[0]=5.0;drop(ff);drop(dd);}fn main(){transform_to_coordfield(Box::new([2.0;2]),Box::new([0.0;2]));}";
    move_refusal_and_compiler_control(&sites, fault, "TRANSFORM");
    println!("TRANSFORM_LEND_BEGIN\n{code}\nTRANSFORM_LEND_END");
}

#[test]
fn two_distinct_owning_generations_still_need_an_exact_peer_certificate() {
    let sites = [
        lend(0, "a", FormalForm::MutableRaw, Payload::Slice("f32".into())),
        lend(1, "b", FormalForm::MutableRaw, Payload::Slice("f32".into())),
    ];
    let mut inv = inventory(&sites);
    assert!(plan_call(&inv, &sites).is_ok());
    inv.disjoint_pairs = Ok(BTreeSet::new());
    assert_eq!(plan_call(&inv, &sites), Err(LendHold::PeerAlias));
    let missing = Missing {
        owner: EvidenceOwner::Emission,
        reason: MissingReason::Field("a5_pair_certificate"),
    };
    inv.disjoint_pairs = Err(missing.clone());
    assert_eq!(plan_call(&inv, &sites), Err(LendHold::Missing(missing)));
    let mut pair = (sites[0].edge, sites[1].edge);
    pair.1.call.occurrence += 1;
    inv.disjoint_pairs = Ok(BTreeSet::from([pair]));
    assert_eq!(plan_call(&inv, &sites), Err(LendHold::PeerAlias));
}

#[test]
fn indirect_lend_targets_must_agree_on_the_same_actual_and_form() {
    let first = lend(0, "a", FormalForm::MutableRaw, Payload::Sized("f32".into()));
    let mut edge = first.edge;
    edge.target = OwnerId(3);
    edge.formal.site.owner = edge.target;
    let second = at_edge(first.clone(), edge);
    let sites = [first, second];
    let inv = inventory(&sites);
    let plan = plan_call(&inv, &sites).unwrap();
    assert_eq!(plan.arguments.len(), 1);
    assert_eq!(plan.receipts.len(), 2);
    let mut changed = sites.clone();
    changed[1].place = "different_owner".into();
    assert_eq!(plan_call(&inv, &changed), Err(LendHold::TargetDisagreement));
    let mut changed = sites;
    let formal = changed[1].formal.as_mut().unwrap();
    formal.kind = Kind::Ref;
    formal.form = FormalForm::MutableReference;
    assert_eq!(plan_call(&inv, &changed), Err(LendHold::TargetDisagreement));
}

#[test]
fn one_call_cannot_shorten_one_buffers_protection_to_hide_a_live_reference() {
    let mut sites = [
        lend(0, "a", FormalForm::MutableRaw, Payload::Slice("f32".into())),
        lend(1, "b", FormalForm::MutableRaw, Payload::Slice("f32".into())),
    ];
    let inv = inventory(&sites);
    sites[1].view.end = 25;
    sites[1].call_span.end = 25;
    sites[1].protector.end = 25;
    sites[1].references = Ok(vec![ReferenceInterval {
        generation: sites[1].edge.actual.generation,
        live: Span { start: 26, end: 29 },
        protected: None,
    }]);
    assert_eq!(plan_call(&inv, &sites), Err(LendHold::Span));
}

#[test]
fn lending_needs_nonconsuming_and_t1_evidence_separately() {
    let base = lend(
        0,
        "owner",
        FormalForm::MutableRaw,
        Payload::Sized("f32".into()),
    );
    let inv = inventory(&[base.clone()]);
    assert_eq!(
        plan_call(&inv, &[base.clone()]).unwrap().arguments[&0],
        "core::ptr::from_mut(&mut *(owner))"
    );
    let missing = Missing {
        owner: EvidenceOwner::Emission,
        reason: MissingReason::Field("transitive_nonconsuming"),
    };
    let mut site = base.clone();
    site.non_consuming = Err(missing.clone());
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::Missing(missing)));
    for retention in [Retention::Unknown, Retention::Retains] {
        let mut site = base.clone();
        site.retention.as_mut().unwrap().outcome = retention;
        assert_eq!(plan_call(&inv, &[site]), Err(LendHold::Retention));
    }
    let mut site = base.clone();
    site.formal.as_mut().unwrap().kind = Kind::Owning;
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::OwningCallee));
    let mut site = base.clone();
    site.formal.as_mut().unwrap().kind = Kind::Ref;
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::Formal));
    let mut site = base;
    site.retention.as_mut().unwrap().edge.argument += 1;
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::Identity));
}

#[test]
fn lend_alias_and_protector_checks_cover_argument_evaluation_through_return() {
    let base = lend(
        0,
        "owner",
        FormalForm::MutableRaw,
        Payload::Slice("f32".into()),
    );
    let inv = inventory(&[base.clone()]);
    let mut site = base.clone();
    site.references = Ok(vec![ReferenceInterval {
        generation: site.edge.actual.generation,
        live: Span { start: 11, end: 12 },
        protected: None,
    }]);
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::LiveReference));
    let mut site = base.clone();
    site.references = Ok(vec![ReferenceInterval {
        generation: site.edge.actual.generation,
        live: Span { start: 0, end: 1 },
        protected: Some(Span { start: 10, end: 30 }),
    }]);
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::Protector));
    let mut site = base.clone();
    site.protector.end -= 1;
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::Span));
    let mut second = base.clone();
    second.edge.argument = 1;
    second.formal.as_mut().unwrap().edge = second.edge;
    second.stable_place = Ok(second.edge);
    second.non_consuming = Ok(second.edge);
    second.retention.as_mut().unwrap().edge = second.edge;
    second.reference_inventory = Ok(second.edge);
    second.peer_inventory = Ok(second.edge);
    second.permission = Ok(second.edge);
    second.continuation_inventory = Ok(second.edge);
    let sites = [base, second];
    assert_eq!(
        plan_call(&inventory(&sites), &sites),
        Err(LendHold::PeerAlias)
    );
}

#[test]
fn lend_call_target_inventory_and_owner_identity_are_exact() {
    let base = lend(
        0,
        "owner",
        FormalForm::MutableReference,
        Payload::Sized("f32".into()),
    );
    let inv = inventory(&[base.clone()]);
    let mut missing_target = inv.clone();
    missing_target.targets.insert(OwnerId(3));
    assert_eq!(
        plan_call(&missing_target, &[base.clone()]),
        Err(LendHold::Inventory)
    );
    assert_eq!(
        plan_call(&inv, &[base.clone(), base.clone()]),
        Err(LendHold::Inventory)
    );
    let mut site = base.clone();
    site.grant.kind = Kind::Ref;
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::Grant));
    let mut site = base.clone();
    site.continuation.as_mut().unwrap()[0].generation += 1;
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::Identity));
    let missing = Missing {
        owner: EvidenceOwner::Emission,
        reason: MissingReason::Field("peer_inventory"),
    };
    let mut site = base;
    site.peer_inventory = Err(missing.clone());
    assert_eq!(plan_call(&inv, &[site]), Err(LendHold::Missing(missing)));
}
