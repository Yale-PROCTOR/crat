//! Validate a finite value-shape certificate supplied by construction/flow
//! evidence. This walks no MIR and chooses no stack budget or depth threshold.
use std::collections::{BTreeMap, BTreeSet};

use super::{
    EvidenceKey, OwnerId,
    lifecycle::{CloseKind, DepthWitness, DropShape},
};
