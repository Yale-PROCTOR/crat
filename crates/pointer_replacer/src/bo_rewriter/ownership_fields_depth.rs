//! Validate a finite value-shape certificate supplied by construction/flow
//! evidence. This walks no MIR and chooses no stack budget or depth threshold.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    EvidenceKey, OwnerId,
    lifecycle::{CloseKind, DepthWitness, DropShape},
};

#[derive(Clone, Debug)]
pub struct ValueNode {
    pub payload: OwnerId,
    pub children: Vec<Option<u64>>,
}
#[derive(Clone, Debug)]
pub struct ValueCertificate {
    pub key: EvidenceKey,
    pub kind: CloseKind,
    pub payload: OwnerId,
    pub graph_revision: [u8; 32],
    pub root: u64,
    pub nodes: BTreeMap<u64, ValueNode>,
    pub completeness: Option<EvidenceKey>,
}
#[derive(Clone, Debug)]
pub struct StackBudget {
    pub key: EvidenceKey,
    pub kind: CloseKind,
    pub payload: OwnerId,
    pub graph_revision: [u8; 32],
    pub admitted_depth: usize,
    pub lowering_evidence: Option<EvidenceKey>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DepthHold {
    Identity,
    Incomplete,
    MissingNode(u64),
    WrongPayload(u64),
    UnknownType(OwnerId),
    ChildInventory(u64),
    RepeatedOwner(u64),
    UnreachableNode(u64),
    Budget,
    Overflow,
}

pub fn depth_witness(
    certificate: &ValueCertificate,
    graph: &BTreeMap<OwnerId, DropShape>,
    budget: &StackBudget,
) -> Result<DepthWitness, DepthHold> {
    if certificate.key.generation != certificate.root {
        return Err(DepthHold::Identity);
    }
    if certificate.completeness != Some(certificate.key) {
        return Err(DepthHold::Incomplete);
    }
    if budget.key != certificate.key
        || budget.kind != certificate.kind
        || budget.payload != certificate.payload
        || budget.graph_revision != certificate.graph_revision
        || budget.lowering_evidence != Some(certificate.key)
    {
        return Err(DepthHold::Budget);
    }
    let mut visited = BTreeSet::new();
    let mut pending = vec![(certificate.root, certificate.payload, 1_usize)];
    let mut maximum = 0;
    while let Some((id, payload, depth)) = pending.pop() {
        if !visited.insert(id) {
            return Err(DepthHold::RepeatedOwner(id));
        }
        let node = certificate
            .nodes
            .get(&id)
            .ok_or(DepthHold::MissingNode(id))?;
        if node.payload != payload {
            return Err(DepthHold::WrongPayload(id));
        }
        maximum = maximum.max(depth);
        let children: Vec<_> = match graph.get(&payload) {
            Some(DropShape::Leaf) => vec![],
            Some(DropShape::Fields(children)) => children.iter().map(|ty| (*ty, false)).collect(),
            Some(DropShape::OwnedFields(children)) => children
                .iter()
                .map(|edge| (edge.payload, edge.optional))
                .collect(),
            None | Some(DropShape::Unknown) => return Err(DepthHold::UnknownType(payload)),
        };
        if node.children.len() != children.len() {
            return Err(DepthHold::ChildInventory(id));
        }
        for (child, (ty, optional)) in node.children.iter().zip(children) {
            match child {
                Some(child) => {
                    pending.push((*child, ty, depth.checked_add(1).ok_or(DepthHold::Overflow)?))
                }
                None if optional => {}
                None => return Err(DepthHold::ChildInventory(id)),
            }
        }
    }
    for id in certificate.nodes.keys() {
        if !visited.contains(id) {
            return Err(DepthHold::UnreachableNode(*id));
        }
    }
    Ok(DepthWitness {
        kind: certificate.kind,
        key: certificate.key,
        payload: certificate.payload,
        graph_revision: certificate.graph_revision,
        graph: graph.clone(),
        maximum_depth: maximum,
        admitted_depth: budget.admitted_depth,
    })
}
