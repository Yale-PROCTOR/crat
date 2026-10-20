//! Wave-5p: paired native evidence for shared views across a reader call.

#![allow(
    dead_code,
    reason = "Native evidence checkpoint; admission awaits the shared-pair receipt carrier."
)]

pub(crate) mod consumer;
mod observer;
pub(crate) mod reader;
pub(crate) use observer::publish;

use super::{DecisionTable, SubjectKind, a5_site_proof::A5ProofSiteKey, seam::Form};
use crate::analyses::borrow_ownership::mutability_facts::MutFacts;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeMutability {
    Missing,
    Present { mutable: bool },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PositionDiagnostic {
    pub site: Option<A5ProofSiteKey>,
    pub argument_index: usize,
    pub expected: Form,
    pub found: Form,
    pub formal_mutability: NativeMutability,
}

pub(crate) fn diagnose(table: &DecisionTable, mut_facts: &MutFacts) -> Vec<PositionDiagnostic> {
    table.seams.overlap_proofs.iter().map(|proof| {
        // Read the compiler's local identity, never convert an unvalidated
        // receipt index into a rustc index (nor infer mutability from syntax).
        let local = table.entries.iter().find_map(|(subject, _)| {
            (subject.fn_did == proof.callee
                && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == proof.index))
                .then_some(subject.local)
        });
        let formal_mutability = match local {
            Some(local) if !mut_facts.is_defaulted(proof.callee, local) => {
                NativeMutability::Present { mutable: mut_facts.is_mutable(proof.callee, local) }
            }
            _ => NativeMutability::Missing,
        };
        PositionDiagnostic { site: proof.proof_site_key, argument_index: proof.index,
            expected: proof.expected_form, found: proof.found_form, formal_mutability }
    }).collect()
}

#[cfg(test)]
mod tests;
