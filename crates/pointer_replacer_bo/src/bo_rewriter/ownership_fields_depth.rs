//! Validate a finite value-shape certificate supplied by construction/flow
//! evidence. This walks no MIR and chooses no stack budget or depth threshold.
#[cfg(test)]
use std::collections::BTreeMap;
#[cfg(test)]
use std::collections::BTreeSet;

#[cfg(test)]
use super::EvidenceKey;
#[cfg(test)]
use super::OwnerId;
#[cfg(test)]
use super::lifecycle::CloseKind;
#[cfg(test)]
use super::lifecycle::DepthWitness;
#[cfg(test)]
use super::lifecycle::DropShape;
