//! Pure close planning. All proofs are external, keyed inputs; this module
//! neither establishes all-roots coverage nor guesses a recursion depth.
use std::collections::BTreeMap;

use super::{EvidenceKey, OwnerId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DropShape {
    Leaf,
    /// Legacy edges are mandatory; absence cannot certify a smaller value.
    Fields(Vec<OwnerId>),
    OwnedFields(Vec<DropEdge>),
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DropEdge {
    pub payload: OwnerId,
    pub optional: bool,
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
    pub graph: BTreeMap<OwnerId, DropShape>,
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
            Some(DropShape::OwnedFields(children)) => {
                stack.extend(children.iter().rev().map(|child| (child.payload, false)));
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
            || &depth.graph != graph
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

/// R622-3 (Extension X §5.2) — why the old value of an owning place is `None`
/// at a store, so the store's implicit close has depth 0. The compiler-side
/// derivation lives in `decision::ownership_fields_store_close`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NoneWitness {
    /// The stored value's own evaluation moves the place out first:
    /// `p.f = callee(p.f.take(), ..)`.
    TakenInValue,
    /// An earlier statement of the same block moved the place out, and no
    /// statement between names the base.
    TakenBefore,
    /// The base is a fresh allocation whose literal wrote `None` there, and no
    /// statement between writes the place or names the base otherwise.
    FreshLiteral,
}

pub const DEPTH_WITNESS_NONE: &str = "depth-witness(none)";
pub const WAIVER_LEAK_RECURSIVE: &str = "waiver-leak(recursive-drop)";

/// The close a store into an owning place makes (overwrite; X §5.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoreClose {
    /// The payload is not recursive: addendum 101's overwrite drop.
    Drop,
    /// Recursive, and the old value is `None`: the store renders unchanged.
    Witnessed(NoneWitness),
    /// Recursive and unwitnessed: the old value is deliberately leaked.
    Leak,
}

impl StoreClose {
    /// `None` for [`StoreClose::Drop`], whose receipt is the caller's
    /// `waiver-drop(overwrite)`.
    pub fn receipt(self) -> Option<&'static str> {
        match self {
            Self::Drop => None,
            Self::Witnessed(_) => Some(DEPTH_WITNESS_NONE),
            Self::Leak => Some(WAIVER_LEAK_RECURSIVE),
        }
    }

    /// The store `place = value` as emitted: unchanged (`None`), or, for a
    /// leak, the old value moved out and forgotten.
    pub fn render(self, place: &str, value: &str) -> Option<String> {
        match self {
            Self::Drop | Self::Witnessed(_) => None,
            Self::Leak => Some(format!(
                "::std::mem::forget(::std::mem::replace(&mut {place}, {value}))"
            )),
        }
    }
}

/// `owning` maps each type to the pointee types of its owning fields (an
/// absent type has none). The payload is recursive when a cycle of owning
/// edges is reachable from it; only such a payload needs `witness`.
pub fn store_close(
    payload: OwnerId,
    owning: &BTreeMap<OwnerId, Vec<OwnerId>>,
    witness: Option<NoneWitness>,
) -> StoreClose {
    let mut graph = BTreeMap::new();
    let mut pending = vec![payload];
    while let Some(node) = pending.pop() {
        if graph.contains_key(&node) {
            continue;
        }
        let children = owning.get(&node).cloned().unwrap_or_default();
        pending.extend(children.iter().copied());
        graph.insert(
            node,
            if children.is_empty() {
                DropShape::Leaf
            } else {
                DropShape::Fields(children)
            },
        );
    }
    match (recursive(payload, &graph), witness) {
        (Ok(false), _) => StoreClose::Drop,
        (Ok(true), Some(witness)) => StoreClose::Witnessed(witness),
        (Ok(true), None) | (Err(_), _) => StoreClose::Leak,
    }
}
