//! GF08 closed-caller witnesses. These embedded programs are never executed.
use super::{
    facts::EquationId,
    matched::{MatchedTransport, TerminalTarget},
    transport::CandidateGraph,
};
pub(crate) const CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub struct Holder{ptr:*mut Node}
pub unsafe fn identity(node:*mut Node)->*mut Node{node}
pub unsafe fn run(){
 let node=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*node).child=0 as *mut Node;
 let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;
 (*holder).ptr=node;
 let result=identity((*holder).ptr);
 (*holder).ptr=0 as *mut Node;
 free(result as *mut core::ffi::c_void);
 free(holder as *mut core::ffi::c_void);
}
"#;

#[test]
fn gf08_conditional_root_transport_connects_the_original_source_and_free() {
    super::graph_tests::with_facts(CODE, |facts| {
        let declaration = facts
            .fold_declarations
            .as_ref()
            .unwrap()
            .iter()
            .find(|d| d.call.callee == "identity")
            .unwrap();
        let proof = super::fold_call::certify(
            facts,
            &declaration.call,
            declaration.argument,
            &Default::default(),
        )
        .unwrap();
        let graph = CandidateGraph::build(facts);
        assert_eq!(
            graph.sources.len(),
            2,
            "payload and container allocation identities are distinct"
        );
        assert_eq!(graph.sinks.len(), 2, "both original frees remain");
        use super::{
            super::ownership_occurrence::Availability::Present,
            value_origins::{OriginAtom, ValueOrigins},
        };
        let actual = facts
            .consumes
            .iter()
            .find(|c| c.ordinal == proof.actual_consume)
            .unwrap();
        let store = facts
            .field_support_inputs
            .stores
            .iter()
            .find(|s| {
                s.site.function == "run"
                    && s.site.place.local == actual.local
                    && s.site.place.projection == actual.projection
                    && matches!(s.value, super::field_support::StoredValue::Value(_))
            })
            .unwrap();
        let transfer = facts
            .equations
            .iter()
            .find(|e| {
                e.point.function.as_deref() == Some("run")
                    && e.point.block == Some(store.site.block)
                    && e.point.statement == Some(store.site.statement)
                    && matches!(e.operation.as_str(), "linear" | "equal")
                    && e.transfer.as_ref().is_some_and(|t| {
                        matches!(&t.destination,Present(d)
                if d.local==actual.local && d.projection==actual.projection)
                    })
            })
            .unwrap()
            .transfer
            .as_ref()
            .unwrap();
        let origins = ValueOrigins::build(facts);
        let fresh = |node| {
            let values = origins.at(node);
            assert!(
                values
                    .iter()
                    .all(|v| matches!(v, OriginAtom::Fresh(_) | OriginAtom::Null)),
                "{values:?}"
            );
            let sources: std::collections::BTreeSet<_> = values
                .iter()
                .filter_map(|v| match v {
                    OriginAtom::Fresh(id) => Some(*id),
                    _ => None,
                })
                .collect();
            assert_eq!(sources.len(), 1);
            *sources.iter().next().unwrap()
        };
        let payload_source = fresh(super::transport::Node {
            construction: 0,
            var: transfer.source_use,
        });
        let Present(base) = &actual.base else { panic!("full container base") };
        let container_node = super::transport::Node {
            construction: 0,
            var: base.use_start,
        };
        let container_source = fresh(container_node);
        assert_ne!(payload_source, container_source);
        assert!(
            MatchedTransport::build(facts)
                .meets_for(proof.actual_before)
                .iter()
                .all(|meet| !matches!(meet.terminal.target, TerminalTarget::Free(_))),
            "ordinary unmatched boundary remains held"
        );
        let transport = MatchedTransport::build_with_conditional_folds(
            facts,
            &[(declaration.guard, proof.clone())],
        )
        .unwrap();
        let meets = transport.meets_for(proof.actual_before);
        assert!(
            meets
                .iter()
                .any(|meet| meet.source.endpoint == payload_source
                    && matches!(meet.terminal.target, TerminalTarget::Free(_))
                    && meet.guards.get(&declaration.guard) == Some(&true)),
            "exact conditional source/call/return/free route: {meets:?}"
        );
        let frees = |node, source| {
            transport
                .meets_for(node)
                .into_iter()
                .filter(|m| m.source.endpoint == source)
                .filter_map(|m| match m.terminal.target {
                    TerminalTarget::Free(free) => Some(free),
                    _ => None,
                })
                .collect::<std::collections::BTreeSet<_>>()
        };
        let payload_frees = frees(proof.actual_before, payload_source);
        let container_frees = frees(container_node, container_source);
        assert_eq!(payload_frees.len(), 1);
        assert_eq!(container_frees.len(), 1);
        assert!(
            payload_frees.is_disjoint(&container_frees),
            "each allocation has its own original C free"
        );
        assert_eq!(
            facts
                .boundary_substitutions
                .iter()
                .find(|b| b.ordinal == proof.boundary)
                .unwrap()
                .unmatched_formal_vars
                .len(),
            2
        );
        let invalid = EquationId {
            construction: declaration.guard.construction,
            ordinal: usize::MAX,
        };
        assert!(
            MatchedTransport::build_with_conditional_folds(facts, &[(invalid, proof)]).is_err(),
            "unregistered fold guard is not an edge label"
        );
    });
}

#[test]
fn gf08_closed_field_identity_chain_selects_ownership_and_keeps_endpoints() {
    use super::super::SlotKind;
    let fixture = super::tests::inspect_era5_frame(CODE);
    assert!(fixture.accepted, "{:?}", fixture.construction_error);
    let accepted = fixture.export.stack_entry_final.as_ref().unwrap();
    assert!(
        accepted
            .fold_guards
            .as_ref()
            .unwrap()
            .iter()
            .any(|(_, selected)| *selected),
        "closed caller must release its exact fold hold"
    );
    fixture.assert_kind("Holder.ptr", SlotKind::Owning);
    fixture.assert_kind("run::result", SlotKind::Owning);
    let snapshot = fixture
        .export
        .ownership_licensing
        .as_ref()
        .unwrap()
        .iter()
        .find(|s| s.offset == accepted.snapshot_offset)
        .unwrap();
    let proof = snapshot.fold_callers.as_ref().unwrap()[0]
        .outcome
        .as_ref()
        .unwrap();
    for operation in ["source", "sink"] {
        assert_eq!(
            snapshot
                .metadata
                .equations
                .iter()
                .filter(|e| e.operation == operation)
                .count(),
            2,
            "accepted construction retains both original endpoint identities"
        );
    }
    eprintln!(
        "GF08_FRAME_MIGRATION {}",
        serde_json::json!({"ownership_constructions":fixture.export.ownership_constructions,"accepted_snapshot_offset":accepted.snapshot_offset,"flat_sources":fixture.export.source_sites.len(),"flat_sinks":fixture.export.sink_sites.len(),"accepted_sources":2,"accepted_sinks":2})
    );
    let values = accepted.fold_values.as_ref().unwrap();
    let owns = fixture.export.version_owns.as_ref().unwrap();
    for endpoint in [
        proof.payload.source.endpoint,
        proof.payload.free,
        proof.container.source.endpoint,
        proof.container.free,
    ] {
        assert!(values.guards.contains(&(endpoint, true)));
        let equation = snapshot
            .metadata
            .equations
            .iter()
            .find(|e| {
                e.point.construction == endpoint.construction && e.ordinal == endpoint.ordinal
            })
            .unwrap();
        let flat: Vec<_> = fixture
            .export
            .ownership_equations
            .as_ref()
            .unwrap()
            .iter()
            .filter(|e| {
                e.point.construction == snapshot.offset + endpoint.construction
                    && e.ordinal == endpoint.ordinal
            })
            .collect();
        let [flat] = flat.as_slice() else {
            panic!("one endpoint in the accepted export namespace")
        };
        assert_eq!(flat.endpoint, equation.endpoint);
        assert_eq!(flat.variables, equation.variables);
        assert_eq!(equation.variables.len(), 1);
        assert!(owns[super::super::ssa::constraint::Var::from_u32(equation.variables[0])]);
    }
    assert!(values.ownership.contains(&(proof.fold.actual_before, true)));
    assert!(values.ownership.contains(&(proof.fold.actual_after, false)));
    assert!(values.ownership.contains(&(proof.fold.receiver, true)));
}

#[test]
fn gf08_conditional_transport_rebuilds_and_preserves_other_boundary_denials() {
    let code = format!(
        "{}\npub unsafe fn other(node:*mut Node)->*mut Node{{node}}\npub unsafe fn untouched(holder:*mut Holder)->*mut Node{{other((*holder).ptr)}}",
        CODE
    );
    super::graph_tests::with_facts(&code, |facts| {
        let declarations = facts.fold_declarations.as_ref().unwrap();
        let selected = declarations
            .iter()
            .find(|d| d.call.callee == "identity")
            .unwrap();
        let untouched = declarations
            .iter()
            .find(|d| d.call.callee == "other")
            .unwrap();
        let proof = super::fold_call::certify(
            facts,
            &selected.call,
            selected.argument,
            &Default::default(),
        )
        .unwrap();
        let folds = vec![(selected.guard, proof.clone())];
        let transport = MatchedTransport::build_with_conditional_folds(facts, &folds).unwrap();
        assert!(
            transport
                .denials()
                .iter()
                .any(|d| d.construction == untouched.guard.construction
                    && d.boundary == Some(untouched.boundary)
                    && d.reason == super::matched::DenialReason::UnmatchedBoundary)
        );
        assert!(
            !transport
                .denials()
                .iter()
                .any(|d| d.construction == selected.guard.construction
                    && d.boundary == Some(selected.boundary)
                    && d.reason == super::matched::DenialReason::UnmatchedBoundary)
        );
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        let rebuilt = MatchedTransport::build_with_conditional_folds_metadata(
            &snapshot.metadata.facts(),
            &folds,
            &snapshot.metadata.guard_aliases.iter().copied().collect(),
        )
        .unwrap();
        assert_eq!(
            transport.encode_json().unwrap(),
            rebuilt.encode_json().unwrap()
        );
        assert!(
            MatchedTransport::build_with_conditional_folds(
                facts,
                &[(untouched.guard, proof.clone())]
            )
            .is_err(),
            "a different call's guard cannot license this boundary"
        );
        assert!(
            MatchedTransport::build_with_conditional_folds(
                facts,
                &[(selected.guard, proof.clone()), (selected.guard, proof)]
            )
            .is_err(),
            "duplicate/overlapping fold applications reject"
        );
    });
}

#[test]
fn gf08_folded_return_forwards_the_full_receiver_to_its_original_free() {
    super::graph_tests::with_facts(CODE, |facts| {
        let declaration = facts
            .fold_declarations
            .as_ref()
            .unwrap()
            .iter()
            .find(|d| d.call.callee == "identity")
            .unwrap();
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            declaration.argument,
            &Default::default(),
        )
        .unwrap();
        let transport = MatchedTransport::build_with_conditional_folds(
            facts,
            &[(declaration.guard, fold.clone())],
        )
        .unwrap();
        let meets = transport.meets_for(fold.actual_before);
        let output = meets
            .iter()
            .find(|m| match m.terminal.target {
                TerminalTarget::Output { ordinal, .. } => facts.terminals.iter().any(|t| {
                    t.point.construction == 0
                        && t.ordinal == ordinal
                        && t.local == 0
                        && t.point.function.as_deref() == Some("identity")
                }),
                _ => false,
            })
            .unwrap();
        let free = meets
            .iter()
            .find(|m| {
                m.source == output.source && matches!(m.terminal.target, TerminalTarget::Free(_))
            })
            .unwrap();
        assert!(
            transport.forward_return(facts, output, free).is_none(),
            "scalar helper's restrictions remain intact"
        );
        let receipt = transport
            .forward_folded_return(facts, output, free, declaration.guard, &fold)
            .expect("full receiver forwarded under the exact fold contract");
        let forwarded = &receipt.forwarding;
        assert_eq!(receipt.guard, declaration.guard);
        assert_eq!(forwarded.receiver, fold.receiver);
        assert_eq!(forwarded.continuation.terminal, free.terminal);
        assert_eq!(forwarded.guards.get(&declaration.guard), Some(&true));
        let mut omitted = facts.clone();
        omitted.equations.retain(|e| {
            (e.point.construction, e.ordinal)
                != (
                    forwarded.receiver_old_zero.construction,
                    forwarded.receiver_old_zero.ordinal,
                )
        });
        assert!(
            transport
                .forward_folded_return(&omitted, output, free, declaration.guard, &fold)
                .is_none(),
            "receiver old-zero remains mandatory"
        );
    });
}

#[test]
fn gf08_folded_forwarding_rejects_stale_source_or_free_operands() {
    super::graph_tests::with_facts(CODE, |facts| {
        let declaration = facts
            .fold_declarations
            .as_ref()
            .unwrap()
            .iter()
            .find(|d| d.call.callee == "identity")
            .unwrap();
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            declaration.argument,
            &Default::default(),
        )
        .unwrap();
        let transport = MatchedTransport::build_with_conditional_folds(
            facts,
            &[(declaration.guard, fold.clone())],
        )
        .unwrap();
        let meets = transport.meets_for(fold.actual_before);
        let output = meets
            .iter()
            .find(|m| match m.terminal.target {
                TerminalTarget::Output { ordinal, .. } => facts.terminals.iter().any(|t| {
                    t.point.construction == 0
                        && t.ordinal == ordinal
                        && t.local == 0
                        && t.point.function.as_deref() == Some("identity")
                }),
                _ => false,
            })
            .unwrap();
        let free = meets
            .iter()
            .find(|m| {
                m.source == output.source && matches!(m.terminal.target, TerminalTarget::Free(_))
            })
            .unwrap();
        assert!(
            transport
                .forward_folded_return(facts, output, free, declaration.guard, &fold)
                .is_some()
        );
        let TerminalTarget::Free(free_id) = free.terminal.target else { unreachable!() };
        let graph = CandidateGraph::build(facts);
        let other_free = graph.sinks.iter().find(|s| s.equation != free_id).unwrap();
        let other_source = graph
            .sources
            .iter()
            .find(|s| s.equation != output.source.endpoint)
            .unwrap();
        for (name, key, var) in [
            ("sink", free_id, other_free.node.var),
            ("source", output.source.endpoint, other_source.node.var),
        ] {
            let mut changed = facts.clone();
            let equation = changed
                .equations
                .iter_mut()
                .find(|e| e.point.construction == key.construction && e.ordinal == key.ordinal)
                .unwrap();
            assert_ne!(equation.variables[0], var);
            equation.variables[0] = var;
            assert!(
                equation.validate().is_ok(),
                "shape remains valid, {name} operand identity changed"
            );
            assert!(
                transport
                    .forward_folded_return(&changed, output, free, declaration.guard, &fold)
                    .is_none(),
                "a retained transport may not authenticate a changed {name} operand"
            );
        }
    });
}
