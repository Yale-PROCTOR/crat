//! Pure close planning. All proofs are external, keyed inputs; this module
//! neither establishes all-roots coverage nor guesses a recursion depth.
use std::collections::BTreeMap;

use super::{EvidenceKey, OwnerId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DropShape {
    Leaf,
    Fields(Vec<OwnerId>),
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CloseKind {
    ScopeExit,
    Overwrite,
    Unwind,
}

impl CloseKind {
    pub fn receipt(self) -> &'static str {
        match self {
            Self::ScopeExit => "waiver-drop(scope-exit)",
            Self::Overwrite => "waiver-drop(overwrite)",
            Self::Unwind => "waiver-drop(unwind)",
        }
    }
}

/// Required R101 proof inventory. `Some(key)` means the supplying adapter has
/// proved that obligation at this exact event; absence is never success.
#[derive(Clone, Debug, Default)]
pub struct CloseProofs {
    pub event: Option<(EvidenceKey, CloseKind)>,
    pub all_roots: Option<EvidenceKey>,
    pub continuation: Option<EvidenceKey>,
    pub no_live_reference: Option<EvidenceKey>,
    pub no_protector: Option<EvidenceKey>,
    pub allocator_layout: Option<EvidenceKey>,
    pub target_permission: Option<EvidenceKey>,
}

#[derive(Clone, Debug)]
pub struct DepthWitness {
    pub kind: CloseKind,
    pub key: EvidenceKey,
    pub payload: OwnerId,
    pub graph_revision: [u8; 32],
    pub maximum_depth: usize,
    pub admitted_depth: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosePlan {
    Drop {
        key: EvidenceKey,
        receipt: &'static str,
    },
    LeakRecursive {
        key: EvidenceKey,
        kind: CloseKind,
    },
}

impl ClosePlan {
    pub fn receipt(&self) -> &'static str {
        match self {
            Self::Drop { receipt, .. } => receipt,
            Self::LeakRecursive { .. } => "waiver-leak(recursive-drop)",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CloseHold {
    MissingProof(&'static str),
    StaleProof(&'static str),
    UnknownShape(OwnerId),
    DepthWitnessMismatch,
}

/// Only owning containment edges belong in `DropShape::Fields`. Shared/raw
/// referents are not followed. An iterative DFS avoids recursive host-stack
/// use while checking a deeply nested compiler type graph.
fn recursive(payload: OwnerId, graph: &BTreeMap<OwnerId, DropShape>) -> Result<bool, CloseHold> {
    let mut colors = BTreeMap::new();
    let mut stack = vec![(payload, false)];
    let mut cycle = false;
    while let Some((node, exit)) = stack.pop() {
        if exit {
            colors.insert(node, 2);
            continue;
        }
        match colors.get(&node) {
            Some(1) => {
                cycle = true;
                continue;
            }
            Some(2) => continue,
            _ => {}
        }
        colors.insert(node, 1);
        stack.push((node, true));
        match graph.get(&node) {
            Some(DropShape::Leaf) => {}
            Some(DropShape::Fields(children)) => {
                stack.extend(children.iter().rev().map(|child| (*child, false)));
            }
            None | Some(DropShape::Unknown) => return Err(CloseHold::UnknownShape(node)),
        }
    }
    Ok(cycle)
}

pub fn implicit_close(
    key: EvidenceKey,
    kind: CloseKind,
    payload: OwnerId,
    graph: &BTreeMap<OwnerId, DropShape>,
    graph_revision: [u8; 32],
    depth: Option<&DepthWitness>,
    proofs: &CloseProofs,
) -> Result<ClosePlan, CloseHold> {
    if proofs.event != Some((key, kind)) {
        return Err(CloseHold::StaleProof("close-event"));
    }
    for (name, proof) in [
        ("all-roots", proofs.all_roots),
        ("continuation", proofs.continuation),
        ("no-live-reference", proofs.no_live_reference),
        ("no-protector", proofs.no_protector),
        ("allocator-layout", proofs.allocator_layout),
        ("target-permission", proofs.target_permission),
    ] {
        match proof {
            None => return Err(CloseHold::MissingProof(name)),
            Some(found) if found != key => return Err(CloseHold::StaleProof(name)),
            Some(_) => {}
        }
    }
    let is_recursive = recursive(payload, graph)?;
    if let Some(depth) = depth {
        if depth.key != key
            || depth.kind != kind
            || depth.payload != payload
            || depth.graph_revision != graph_revision
        {
            return Err(CloseHold::DepthWitnessMismatch);
        }
    }
    let bounded = depth.is_some_and(|w| w.maximum_depth <= w.admitted_depth);
    if is_recursive && !bounded {
        Ok(ClosePlan::LeakRecursive { key, kind })
    } else {
        Ok(ClosePlan::Drop {
            key,
            receipt: kind.receipt(),
        })
    }
}
