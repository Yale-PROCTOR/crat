//! Attested, site-local A5 proofs consumed by call-seam overlap gates.
//!
//! This module interprets the existing [`audit_a5_site_branches`] output; it
//! does not classify aliasing itself. Production may derive the index only in
//! precise mode with the frozen-graph attestation. Every lookup failure is a
//! typed conservative result.

use std::collections::BTreeMap;

use rustc_middle::{mir::BasicBlock, ty::TyCtxt};
use rustc_span::Span;

use crate::{
    analyses::borrow_ownership::{
        a5_overlap::{A5Mode, PairClass, WholeProgramAttestation},
        a5_producer::{A5SiteBranchAudit, audit_a5_site_branches},
        crate_slots::CrateSlots,
        l2::MirLocationKey,
        origin_summary::OriginSummaries,
    },
    utils::rustc::RustProgram,
};

pub(crate) const ATTESTED_WORLD: &str = "closed_world_frozen_graph";
pub(crate) const ATTESTED_GUARD: &str = "permitted:measurement-frozen-graph-attested";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum A5SiteProofVerdict {
    Clear,
    Overlapping,
    Undeterminable,
}

impl A5SiteProofVerdict {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::Clear => "clear",
            Self::Overlapping => "overlapping",
            Self::Undeterminable => "undeterminable",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct A5PeerProof {
    pub(crate) verdict: A5SiteProofVerdict,
    pub(crate) reason: &'static str,
    pub(crate) family: &'static str,
    pub(crate) location: Option<MirLocationKey>,
}

impl A5PeerProof {
    fn undeterminable(reason: &'static str) -> Self {
        Self {
            verdict: A5SiteProofVerdict::Undeterminable,
            reason,
            family: reason,
            location: None,
        }
    }

    pub(crate) fn receipt(&self, left: usize, right: usize) -> String {
        let (left, right) = canonical_zero_pair(left, right);
        format!(
            "{left}/{right}->{}/{}:{}:{}:{}",
            left + 1,
            right + 1,
            self.verdict.key(),
            self.reason,
            self.family,
        )
    }

    pub(crate) fn location_key(&self) -> String {
        self.location.map_or_else(
            || "-".to_owned(),
            |location| format!("bb{}:s{}", location.block, location.statement_index),
        )
    }
}

#[derive(Clone, Debug)]
struct ResolvedAudit {
    call_span: Span,
    proof: A5PeerProof,
}

#[derive(Clone, Debug)]
pub(crate) struct A5SeamProofIndex {
    rows: BTreeMap<(u32, u32, u32, u32), Vec<ResolvedAudit>>,
    unavailable: Option<&'static str>,
    world: &'static str,
    guard: &'static str,
    global_setup_wall_s: f64,
    pair_classification_wall_s: f64,
}

impl A5SeamProofIndex {
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        origins: Option<&OriginSummaries>,
        mode: A5Mode,
        attestation: Option<WholeProgramAttestation>,
    ) -> Self {
        if mode != A5Mode::PreciseReplay {
            return Self::unavailable(
                "seam-a5-mode-not-precise",
                "-",
                "refused:a5-mode-not-precise",
            );
        }
        if attestation != Some(WholeProgramAttestation::FrozenBenchmarkGraph) {
            return Self::unavailable(
                "seam-a5-attestation-absent",
                "-",
                "refused:measurement-frozen-graph-unattested",
            );
        }
        let Some(origins) = origins else {
            return Self::unavailable(
                "seam-a5-origins-unavailable",
                ATTESTED_WORLD,
                ATTESTED_GUARD,
            );
        };

        let started = std::time::Instant::now();
        let audits = audit_a5_site_branches(program, slots, origins.native_flows());
        let global_setup_wall_s = started.elapsed().as_secs_f64();
        Self::from_audits(program.tcx, program, audits, global_setup_wall_s)
    }

    fn unavailable(reason: &'static str, world: &'static str, guard: &'static str) -> Self {
        Self {
            rows: BTreeMap::new(),
            unavailable: Some(reason),
            world,
            guard,
            global_setup_wall_s: 0.0,
            pair_classification_wall_s: 0.0,
        }
    }

    fn from_audits(
        tcx: TyCtxt<'_>,
        program: &RustProgram<'_>,
        audits: Vec<A5SiteBranchAudit>,
        global_setup_wall_s: f64,
    ) -> Self {
        let started = std::time::Instant::now();
        let functions = program
            .functions
            .iter()
            .copied()
            .map(|did| (did.local_def_index.as_u32(), did))
            .collect::<BTreeMap<_, _>>();
        let mut rows = BTreeMap::<(u32, u32, u32, u32), Vec<ResolvedAudit>>::new();
        for audit in audits {
            let caller = functions[&audit.caller];
            let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
            let block = BasicBlock::from_u32(audit.block);
            let data = &body.basic_blocks[block];
            let call_span = data.terminator().source_info.span.source_callsite();
            let location = MirLocationKey::new(audit.block, data.statements.len());
            let proof = proof_from_audit(&audit, location);
            rows.entry((
                audit.caller,
                audit.target,
                audit.left_parameter,
                audit.right_parameter,
            ))
            .or_default()
            .push(ResolvedAudit { call_span, proof });
        }
        for bucket in rows.values_mut() {
            bucket.sort_by_key(|row| (row.call_span.lo(), row.call_span.hi(), row.proof.location));
        }
        Self {
            rows,
            unavailable: None,
            world: ATTESTED_WORLD,
            guard: ATTESTED_GUARD,
            global_setup_wall_s,
            pair_classification_wall_s: started.elapsed().as_secs_f64(),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn lookup(
        &self,
        caller: u32,
        callee: u32,
        left: usize,
        right: usize,
        left_span: Span,
        right_span: Span,
    ) -> A5PeerProof {
        if let Some(reason) = self.unavailable {
            return A5PeerProof::undeterminable(reason);
        }
        let (left, right) = canonical_one_pair(left, right);
        let Some(candidates) = self.rows.get(&(caller, callee, left, right)) else {
            return A5PeerProof::undeterminable("seam-a5-site-unresolved");
        };
        let left_span = left_span.source_callsite();
        let right_span = right_span.source_callsite();
        let matched = candidates
            .iter()
            .filter(|row| row.call_span.contains(left_span) && row.call_span.contains(right_span))
            .collect::<Vec<_>>();
        match matched.as_slice() {
            [row] => row.proof.clone(),
            [] => A5PeerProof::undeterminable("seam-a5-site-unresolved"),
            _ => A5PeerProof::undeterminable("seam-a5-site-ambiguous"),
        }
    }

    pub(crate) fn world(&self) -> &'static str {
        self.world
    }

    pub(crate) fn guard(&self) -> &'static str {
        self.guard
    }

    pub(crate) fn global_setup_wall_s(&self) -> f64 {
        self.global_setup_wall_s
    }

    pub(crate) fn pair_classification_wall_s(&self) -> f64 {
        self.pair_classification_wall_s
    }
}

fn proof_from_audit(audit: &A5SiteBranchAudit, location: MirLocationKey) -> A5PeerProof {
    let (verdict, reason) = if audit.family == "projection-disjoint" {
        (A5SiteProofVerdict::Clear, "projection-disjoint")
    } else {
        match audit.classifier {
            Some(PairClass::ProvenDisjoint) => (A5SiteProofVerdict::Clear, "a5-proven-disjoint"),
            Some(PairClass::NotProvenDisjoint) => {
                (A5SiteProofVerdict::Overlapping, "a5-not-proven-disjoint")
            }
            None => (A5SiteProofVerdict::Undeterminable, audit.family),
        }
    };
    A5PeerProof {
        verdict,
        reason,
        family: audit.family,
        location: Some(location),
    }
}

fn canonical_zero_pair(left: usize, right: usize) -> (usize, usize) {
    (left.min(right), left.max(right))
}

fn canonical_one_pair(left: usize, right: usize) -> (u32, u32) {
    let (left, right) = canonical_zero_pair(left, right);
    ((left + 1) as u32, (right + 1) as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn n5_zero_based_seam_pair_maps_once_to_one_based_a5_pair() {
        assert_eq!(canonical_zero_pair(1, 0), (0, 1));
        assert_eq!(canonical_one_pair(0, 1), (1, 2));
        let proof = A5PeerProof {
            verdict: A5SiteProofVerdict::Clear,
            reason: "a5-proven-disjoint",
            family: "excluded-proven-disjoint",
            location: Some(MirLocationKey::new(4, 7)),
        };
        assert_eq!(
            proof.receipt(1, 0),
            "0/1->1/2:clear:a5-proven-disjoint:excluded-proven-disjoint"
        );
    }

    #[test]
    fn n4_missing_peer_fact_is_undeterminable_not_clear() {
        let index = A5SeamProofIndex::unavailable(
            "seam-a5-site-unresolved",
            ATTESTED_WORLD,
            ATTESTED_GUARD,
        );
        let proof = index.lookup(1, 2, 0, 1, Span::default(), Span::default());
        assert_eq!(proof.verdict, A5SiteProofVerdict::Undeterminable);
        assert_eq!(proof.reason, "seam-a5-site-unresolved");
    }
}
