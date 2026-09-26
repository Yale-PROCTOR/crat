//! Construction-local metadata envelopes; no solver state is serialized.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use super::{
    super::ownership_occurrence::Availability, facts::Facts, matched::MatchedTransport,
    recursive::RecursiveCertificate,
};

#[derive(Clone, Debug)]
pub(crate) struct FrozenTransport {
    pub(crate) fold_callers: Option<Vec<super::fold_eligibility::Decision>>,
    /// Appended family: the used-child declarations the identity certificate
    /// cannot admit. `fold_callers` above is unchanged in name, order and bytes.
    pub(crate) fold_members: Option<Vec<super::fold_eligibility::MemberDecision>>,
    pub(crate) first_permissions: Vec<super::first_permission::Decision>,
    pub(crate) complete_chains: Vec<super::chain_permission::Proof>,
    pub(crate) traversal_returns: Vec<super::traversal_return::Proof>,
    pub(crate) traversal_calls: Vec<super::traversal_call::Candidate>,
    pub(crate) traversal_correspondences:
        Vec<Result<super::traversal_correspondence::Proof, super::traversal_correspondence::Hold>>,
    pub(crate) caller_coverage: super::caller_coverage::Status,
    pub(crate) matched: MatchedTransport,
    pub(crate) recursive: Vec<(u32, String, Availability<RecursiveCertificate>)>,
    pub(crate) value_origins: super::value_origins::ValueOrigins,
    pub(crate) no_ref_carriers: Vec<super::value_origins::NoRefCarrier>,
    pub(crate) objective_grants: Vec<super::grants::Grant>,
    pub(crate) grant_holds: Vec<super::grants::Hold>,
    pub(crate) reader_functions: Vec<super::readers::ReaderFunction>,
    pub(crate) reader_candidates: Vec<super::readers::Candidate>,
    pub(crate) reader_transfers: Vec<super::readers::TransferProof>,
    pub(crate) field_support: Vec<super::field_support::FieldProof>,
    pub(crate) reference_effects: super::ref_effects::Plan,
}

impl FrozenTransport {
    pub(crate) fn build(facts: &Facts) -> Self {
        let matched = MatchedTransport::build(facts);
        let recursive = Self::certificates(facts, &matched);
        let reader_transfers = super::readers::audit_transfers(facts, matched.guard_aliases());
        let value_origins = super::value_origins::ValueOrigins::build(facts);
        let no_ref_carriers = value_origins.no_ref_carriers(facts);
        let mut field_support = super::field_support::audit(
            facts,
            &facts.field_support_inputs,
            &matched,
            &value_origins,
        );
        let first_permissions =
            super::first_permission::plan(facts, &mut field_support, matched.guard_aliases());
        let complete_chains = field_support
            .iter()
            .filter_map(|field| {
                super::chain_permission::certify(facts, field, matched.guard_aliases())
            })
            .collect();
        let traversal_calls = super::traversal_call::discover(facts);
        let traversal_correspondences = traversal_calls
            .iter()
            .map(|call| super::traversal_correspondence::certify(facts, call))
            .collect();
        let (objective_grants, grant_holds) = super::grants::plan(
            facts,
            &super::transport::CandidateGraph::build(facts),
            &matched,
            &value_origins,
        );
        Self {
            fold_callers: super::fold_eligibility::plan(facts),
            fold_members: super::fold_eligibility::member_plan(facts),
            first_permissions,
            complete_chains,
            traversal_calls,
            traversal_correspondences,
            traversal_returns: facts
                .source_occurrences
                .keys()
                .filter_map(|function| super::traversal_return::classify(facts, function))
                .collect(),
            caller_coverage: super::caller_coverage::assess(facts),
            matched,
            recursive,
            value_origins,
            no_ref_carriers,
            objective_grants,
            grant_holds,
            reader_functions: facts.reader_plan.functions.clone(),
            reader_candidates: facts.reader_plan.candidates.clone(),
            reader_transfers,
            field_support,
            reference_effects: super::ref_effects::Plan::build(facts),
        }
    }

    fn certificates(
        facts: &Facts,
        matched: &MatchedTransport,
    ) -> Vec<(u32, String, Availability<RecursiveCertificate>)> {
        (0..facts.constructions)
            .flat_map(|construction| {
                facts.source_occurrences.keys().map(move |function| {
                    (
                        construction,
                        function.clone(),
                        super::recursive::certify_with_transport(
                            facts,
                            construction,
                            function,
                            matched,
                        ),
                    )
                })
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Metadata {
    pub(crate) frame_attested: bool,
    pub(crate) caller_coverage: Option<super::caller_coverage::Coverage>,
    pub(crate) constructions: u32,
    pub(crate) equations: Vec<super::super::ownership_evidence::Equation>,
    pub(crate) consumes: Vec<super::super::ownership_occurrence::Consumption>,
    pub(crate) terminals: Vec<super::super::ownership_occurrence::Terminal>,
    pub(crate) boundaries: Vec<super::super::ownership_boundary::Substitution>,
    pub(crate) registrations: Vec<super::super::ownership_boundary::CallArgRegistration>,
    pub(crate) bodies: Vec<super::coverage::BodyRoster>,
    pub(crate) phi_edges: Vec<super::coverage::PhiEdge>,
    pub(crate) return_selections: Vec<super::coverage::ReturnSelection>,
    pub(crate) occurrences: BTreeMap<String, Vec<super::super::origin_evidence::SourceOccurrence>>,
    pub(crate) slot_keys: Vec<String>,
    pub(crate) raw_pointer_heads: Vec<super::value_origins::RawHead>,
    pub(crate) unit_locals: Vec<(String, u32)>,
    pub(crate) reader_inputs: super::readers::Inputs,
    pub(crate) traversal_native: Option<super::traversal_native::Inputs>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) fold_types: Option<super::fold_types::Inputs>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) fold_declarations: Option<Vec<super::fold_declaration::Declaration>>,
    pub(crate) field_support_inputs: super::field_support::Inputs,
    pub(crate) guard_aliases: Vec<(super::facts::EquationId, super::facts::EquationId)>,
}

impl Metadata {
    /// Report 048: the streamed form of `serde_json::to_writer(&to_value(self))`,
    /// byte for byte -- keys in `Value`'s sorted order, the two
    /// `skip_serializing_if` options omitted when `None`, every sequence element
    /// and every `occurrences` entry through its own `Value`. brotli's metadata is
    /// 267 MB of JSON; the whole-`Value` form of it is what a cache write must not
    /// build.
    pub(crate) fn write_canonical(&self, w: &mut dyn std::io::Write) -> Result<(), String> {
        use super::matched::write_value_seq as seq;
        let raw = |w: &mut dyn std::io::Write, bytes: &[u8]| -> Result<(), String> {
            w.write_all(bytes).map_err(|e| e.to_string())
        };
        let value = |w: &mut dyn std::io::Write, v: &dyn erased::Value| v.write(w);
        raw(w, b"{\"bodies\":")?;
        seq(w, &self.bodies)?;
        raw(w, b",\"boundaries\":")?;
        seq(w, &self.boundaries)?;
        raw(w, b",\"caller_coverage\":")?;
        value(w, &self.caller_coverage)?;
        raw(w, b",\"constructions\":")?;
        value(w, &self.constructions)?;
        raw(w, b",\"consumes\":")?;
        seq(w, &self.consumes)?;
        raw(w, b",\"equations\":")?;
        seq(w, &self.equations)?;
        raw(w, b",\"field_support_inputs\":")?;
        value(w, &self.field_support_inputs)?;
        if let Some(declarations) = &self.fold_declarations {
            raw(w, b",\"fold_declarations\":")?;
            seq(w, declarations)?;
        }
        if let Some(types) = &self.fold_types {
            raw(w, b",\"fold_types\":")?;
            value(w, types)?;
        }
        raw(w, b",\"frame_attested\":")?;
        value(w, &self.frame_attested)?;
        raw(w, b",\"guard_aliases\":")?;
        seq(w, &self.guard_aliases)?;
        raw(w, b",\"occurrences\":{")?;
        for (n, (key, occurrences)) in self.occurrences.iter().enumerate() {
            if n > 0 {
                raw(w, b",")?;
            }
            serde_json::to_writer(&mut *w, key).map_err(|e| e.to_string())?;
            raw(w, b":")?;
            seq(w, occurrences)?;
        }
        raw(w, b"}")?;
        raw(w, b",\"phi_edges\":")?;
        seq(w, &self.phi_edges)?;
        raw(w, b",\"raw_pointer_heads\":")?;
        seq(w, &self.raw_pointer_heads)?;
        raw(w, b",\"reader_inputs\":")?;
        value(w, &self.reader_inputs)?;
        raw(w, b",\"registrations\":")?;
        seq(w, &self.registrations)?;
        raw(w, b",\"return_selections\":")?;
        seq(w, &self.return_selections)?;
        raw(w, b",\"slot_keys\":")?;
        seq(w, &self.slot_keys)?;
        raw(w, b",\"terminals\":")?;
        seq(w, &self.terminals)?;
        raw(w, b",\"traversal_native\":")?;
        value(w, &self.traversal_native)?;
        raw(w, b",\"unit_locals\":")?;
        seq(w, &self.unit_locals)?;
        raw(w, b"}")
    }
}

/// One field through its own `Value` (the old `write_small`, per field).
mod erased {
    pub(super) trait Value {
        fn write(&self, w: &mut dyn std::io::Write) -> Result<(), String>;
    }
    impl<T: serde::Serialize> Value for T {
        fn write(&self, w: &mut dyn std::io::Write) -> Result<(), String> {
            let value = serde_json::to_value(self).map_err(|e| e.to_string())?;
            serde_json::to_writer(w, &value).map_err(|e| e.to_string())
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Snapshot {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) fold_callers: Option<Vec<super::fold_eligibility::Decision>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) fold_members: Option<Vec<super::fold_eligibility::MemberDecision>>,
    pub(crate) first_permissions: Vec<super::first_permission::Decision>,
    pub(crate) complete_chains: Vec<super::chain_permission::Proof>,
    pub(crate) traversal_returns: Vec<super::traversal_return::Proof>,
    pub(crate) traversal_calls: Vec<super::traversal_call::Candidate>,
    pub(crate) traversal_correspondences:
        Vec<Result<super::traversal_correspondence::Proof, super::traversal_correspondence::Hold>>,
    pub(crate) caller_coverage: super::caller_coverage::Status,
    /// Add this offset to a local construction key when joining the flat export.
    /// Ownership Vars and record ordinals are never renumbered.
    pub(crate) offset: u32,
    pub(crate) metadata: Metadata,
    pub(crate) matched: MatchedTransport,
    pub(crate) recursive: Vec<(u32, String, Availability<RecursiveCertificate>)>,
    pub(crate) value_origins: super::value_origins::ValueOrigins,
    pub(crate) no_ref_carriers: Vec<super::value_origins::NoRefCarrier>,
    pub(crate) objective_grants: Vec<super::grants::Grant>,
    pub(crate) grant_holds: Vec<super::grants::Hold>,
    pub(crate) reader_functions: Vec<super::readers::ReaderFunction>,
    pub(crate) reader_candidates: Vec<super::readers::Candidate>,
    pub(crate) reader_transfers: Vec<super::readers::TransferProof>,
    pub(crate) field_support: Vec<super::field_support::FieldProof>,
    pub(crate) reference_effects: super::ref_effects::Plan,
}

impl Metadata {
    pub(crate) fn from_facts(facts: &Facts, matched: &MatchedTransport) -> Self {
        Self {
            frame_attested: facts.frame_attested,
            caller_coverage: facts.caller_coverage.clone(),
            constructions: facts.constructions,
            equations: facts.equations.clone(),
            consumes: facts.consumes.clone(),
            terminals: facts.terminals.clone(),
            boundaries: facts.boundary_substitutions.clone(),
            registrations: facts.call_arg_registrations.clone(),
            bodies: facts.body_rosters.clone(),
            phi_edges: facts.phi_edges.clone(),
            return_selections: facts.return_selections.clone(),
            occurrences: facts.source_occurrences.clone(),
            slot_keys: facts.slot_refs.keys().cloned().collect(),
            raw_pointer_heads: facts.raw_pointer_heads.clone(),
            unit_locals: facts.unit_locals.clone(),
            reader_inputs: facts.reader_inputs.clone(),
            traversal_native: facts.traversal_native.clone(),
            fold_types: facts.fold_types.clone(),
            fold_declarations: facts.fold_declarations.clone(),
            field_support_inputs: facts.field_support_inputs.clone(),
            guard_aliases: matched
                .guard_aliases()
                .iter()
                .map(|(&key, &value)| (key, value))
                .collect(),
        }
    }

    /// Empty AST containers remain empty; this never freezes or solves Facts.
    pub(crate) fn facts(&self) -> Facts {
        Facts {
            frame_attested: self.frame_attested,
            caller_coverage: self.caller_coverage.clone(),
            constructions: self.constructions,
            equations: self.equations.clone(),
            consumes: self.consumes.clone(),
            terminals: self.terminals.clone(),
            boundary_substitutions: self.boundaries.clone(),
            call_arg_registrations: self.registrations.clone(),
            body_rosters: self.bodies.clone(),
            phi_edges: self.phi_edges.clone(),
            return_selections: self.return_selections.clone(),
            source_occurrences: self.occurrences.clone(),
            raw_pointer_heads: self.raw_pointer_heads.clone(),
            unit_locals: self.unit_locals.clone(),
            reader_inputs: self.reader_inputs.clone(),
            traversal_native: self.traversal_native.clone(),
            fold_types: self.fold_types.clone(),
            fold_declarations: self.fold_declarations.clone(),
            field_support_inputs: self.field_support_inputs.clone(),
            reader_plan: super::readers::Plan::build(&self.reader_inputs),
            ..Facts::default()
        }
    }
}

impl Snapshot {
    pub(crate) fn capture(facts: &Facts, offset: u32) -> Option<Self> {
        let frozen = facts.licensing.as_ref()?;
        Some(Self {
            fold_callers: frozen.fold_callers.clone(),
            fold_members: frozen.fold_members.clone(),
            first_permissions: frozen.first_permissions.clone(),
            complete_chains: frozen.complete_chains.clone(),
            traversal_returns: frozen.traversal_returns.clone(),
            traversal_calls: frozen.traversal_calls.clone(),
            traversal_correspondences: frozen.traversal_correspondences.clone(),
            caller_coverage: frozen.caller_coverage.clone(),
            offset,
            metadata: Metadata::from_facts(facts, &frozen.matched),
            matched: frozen.matched.clone(),
            recursive: frozen.recursive.clone(),
            value_origins: frozen.value_origins.clone(),
            no_ref_carriers: frozen.no_ref_carriers.clone(),
            objective_grants: frozen.objective_grants.clone(),
            grant_holds: frozen.grant_holds.clone(),
            reader_functions: frozen.reader_functions.clone(),
            reader_candidates: frozen.reader_candidates.clone(),
            reader_transfers: frozen.reader_transfers.clone(),
            field_support: frozen.field_support.clone(),
            reference_effects: frozen.reference_effects.clone(),
        })
    }

    /// Recompute all transport from recorded metadata, with no AST or solver.
    pub(crate) fn validate(&self) -> Result<(), String> {
        use std::collections::BTreeSet;
        let facts = self.metadata.facts();
        if super::caller_coverage::assess(&facts) != self.caller_coverage {
            return Err(
                "caller-coverage status differs from recorded compiler/source observations".into(),
            );
        }
        let functions: BTreeSet<_> = facts.source_occurrences.keys().cloned().collect();
        let body_names: BTreeSet<_> = facts
            .reader_inputs
            .bodies
            .iter()
            .map(|body| body.function.clone())
            .collect();
        if body_names != functions
            || body_names.len() != facts.reader_inputs.bodies.len()
            || facts
                .reader_inputs
                .bodies
                .iter()
                .any(|body| facts.source_occurrences.get(&body.function) != Some(&body.occurrences))
        {
            return Err("reader input body/occurrence coverage differs".into());
        }
        if facts.reader_plan.functions != self.reader_functions
            || facts.reader_plan.candidates != self.reader_candidates
        {
            return Err("reader roles differ from recorded body evidence".into());
        }
        super::readers::validate_call_roles(&facts)?;
        if super::ref_effects::Plan::build(&facts) != self.reference_effects {
            return Err("reference-effect candidates differ from recorded evidence".into());
        }
        let mut heads = BTreeSet::new();
        let mut units = BTreeSet::new();
        for (function, local) in &facts.unit_locals {
            if !functions.contains(function)
                || !units.insert((function, local))
                || self
                    .metadata
                    .slot_keys
                    .contains(&format!("{function}::_{local}@d0"))
            {
                return Err("unit-local type evidence has an invalid function/slot join".into());
            }
        }
        for head in &self.metadata.raw_pointer_heads {
            if !functions.contains(&head.function)
                || !self.metadata.slot_keys.contains(&head.slot_key)
                || head.slot_key != format!("{}::_{}@d0", head.function, head.local)
                || !heads.insert(&head.slot_key)
            {
                return Err("raw pointer head has an invalid function/slot join".into());
            }
        }
        let valid_point = |point: &super::super::ownership_evidence::Point, global: bool| {
            point.construction < facts.constructions
                && match &point.function {
                    Some(function) => functions.contains(function),
                    None => global,
                }
        };
        macro_rules! member {
            ($family:ident, $global:expr) => {
                if facts
                    .$family
                    .iter()
                    .any(|row| !valid_point(&row.point, $global))
                {
                    return Err(concat!("invalid metadata namespace: ", stringify!($family)).into());
                }
            };
        }
        member!(equations, true);
        member!(consumes, false);
        member!(terminals, false);
        member!(boundary_substitutions, false);
        member!(call_arg_registrations, false);
        member!(body_rosters, false);
        member!(phi_edges, false);
        member!(return_selections, false);
        macro_rules! unique_records {
            ($family:ident) => {
                if facts
                    .$family
                    .iter()
                    .map(|row| (row.point.construction, row.ordinal))
                    .collect::<BTreeSet<_>>()
                    .len()
                    != facts.$family.len()
                {
                    return Err(concat!("duplicate metadata record: ", stringify!($family)).into());
                }
            };
        }
        unique_records!(consumes);
        unique_records!(terminals);
        unique_records!(boundary_substitutions);
        unique_records!(call_arg_registrations);
        if facts
            .body_rosters
            .iter()
            .map(|row| (row.point.construction, row.point.function.clone()))
            .collect::<BTreeSet<_>>()
            .len()
            != facts.body_rosters.len()
            || facts
                .return_selections
                .iter()
                .map(|row| row.point.clone())
                .collect::<BTreeSet<_>>()
                .len()
                != facts.return_selections.len()
            || facts
                .phi_edges
                .iter()
                .map(|row| {
                    (
                        row.point.construction,
                        row.point.function.clone(),
                        row.from,
                        row.edge_ordinal,
                        row.to,
                        row.local,
                    )
                })
                .collect::<BTreeSet<_>>()
                .len()
                != facts.phi_edges.len()
        {
            return Err("duplicate independent coverage record".into());
        }

        let aliases: BTreeMap<_, _> = self.metadata.guard_aliases.iter().copied().collect();
        if aliases.len() != self.metadata.guard_aliases.len() {
            return Err("duplicate guard identity metadata".into());
        }
        super::fold_declaration::validate(&facts, &aliases)?;
        if super::fold_eligibility::plan_metadata(
            &facts,
            &aliases,
            &self.metadata.slot_keys.iter().cloned().collect(),
        ) != self.fold_callers
        {
            return Err("fold caller eligibility differs from current metadata".into());
        }
        if super::fold_eligibility::member_plan_metadata(
            &facts,
            &aliases,
            &self.metadata.slot_keys.iter().cloned().collect(),
        ) != self.fold_members
        {
            return Err("fold member eligibility differs from current metadata".into());
        }
        super::cell_effects::validate_frames(&facts, &aliases)?;
        super::cell_effects::validate_calls(&facts, &aliases)?;
        let ids: BTreeSet<_> = facts
            .equations
            .iter()
            .map(|row| (row.point.construction, row.ordinal))
            .collect();
        if ids.len() != facts.equations.len()
            || facts
                .equations
                .iter()
                .any(|row| row.point.construction >= facts.constructions)
        {
            return Err("invalid equation namespace".into());
        }
        for row in &facts.equations {
            row.validate().map_err(str::to_owned)?;
        }
        for function in facts.source_occurrences.keys() {
            let equations: Vec<_> = facts
                .equations
                .iter()
                .filter(|row| {
                    row.point
                        .function
                        .as_deref()
                        .is_none_or(|name| name == function)
                })
                .cloned()
                .collect();
            let consumes: Vec<_> = facts
                .consumes
                .iter()
                .filter(|row| row.point.function.as_ref() == Some(function))
                .cloned()
                .collect();
            let terminals: Vec<_> = facts
                .terminals
                .iter()
                .filter(|row| row.point.function.as_ref() == Some(function))
                .cloned()
                .collect();
            let boundaries: Vec<_> = facts
                .boundary_substitutions
                .iter()
                .filter(|row| row.point.function.as_ref() == Some(function))
                .cloned()
                .collect();
            let registrations: Vec<_> = facts
                .call_arg_registrations
                .iter()
                .filter(|row| row.point.function.as_ref() == Some(function))
                .cloned()
                .collect();
            super::super::ownership_evidence::validate_function(&equations, function)
                .map_err(str::to_owned)?;
            super::super::ownership_occurrence::validate(function, &consumes, &equations)?;
            super::super::ownership_boundary::validate_shapes(
                function,
                &boundaries,
                &registrations,
            )?;
            super::super::ownership_boundary::validate_links(
                function,
                &boundaries,
                &registrations,
                &consumes,
                &equations,
            )?;
            super::super::ownership_occurrence::validate_terminal_shapes(function, &terminals)?;
            super::super::ownership_occurrence::validate_terminal_links(
                &terminals,
                &boundaries,
                &equations,
            )?;
        }
        let rebuilt = MatchedTransport::build_metadata(&facts, &aliases)?;
        if super::readers::audit_transfers(&facts, &aliases) != self.reader_transfers {
            return Err("reader transfer coverage differs from recorded evidence".into());
        }
        if rebuilt != self.matched {
            return Err("transport differs from recorded evidence".into());
        }
        if FrozenTransport::certificates(&facts, &rebuilt) != self.recursive {
            return Err("recursive certificate differs from recorded evidence".into());
        }
        let origins = super::value_origins::ValueOrigins::build_metadata(&facts, &aliases)?;
        let mut fields =
            super::field_support::audit(&facts, &facts.field_support_inputs, &rebuilt, &origins);
        let first_permissions = super::first_permission::plan(&facts, &mut fields, &aliases);
        let chains: Vec<_> = fields
            .iter()
            .filter_map(|field| super::chain_permission::certify(&facts, field, &aliases))
            .collect();
        let traversal: Vec<_> = facts
            .source_occurrences
            .keys()
            .filter_map(|function| {
                super::traversal_return::classify_metadata(&facts, function, &aliases)
            })
            .collect();
        if super::traversal_call::discover_metadata(&facts, &aliases) != self.traversal_calls {
            return Err("pending traversal call evidence differs".into());
        }
        let correspondence: Vec<_> = self
            .traversal_calls
            .iter()
            .map(|call| super::traversal_correspondence::certify_metadata(&facts, call, &aliases))
            .collect();
        if correspondence != self.traversal_correspondences {
            return Err("traversal native correspondence differs".into());
        }
        if traversal != self.traversal_returns {
            return Err("traversal return evidence differs".into());
        }
        if chains != self.complete_chains {
            return Err("complete original-cell chain evidence differs".into());
        }
        if fields != self.field_support || first_permissions != self.first_permissions {
            return Err("field ownership support differs from recorded evidence".into());
        }
        if origins != self.value_origins || origins.no_ref_carriers(&facts) != self.no_ref_carriers
        {
            return Err("origin alternatives/carriers differ from recorded evidence".into());
        }
        let graph = super::transport::CandidateGraph::build_metadata(&facts, &aliases)?;
        let (grants, holds) = super::grants::plan(&facts, &graph, &rebuilt, &origins);
        if grants != self.objective_grants || holds != self.grant_holds {
            return Err("objective grants/holds differ from recorded evidence".into());
        }
        Ok(())
    }
}

/// Complete-cache joins. Envelopes use local construction namespaces; the flat
/// origin families use the explicitly offset namespace. No solver is involved.
pub(crate) fn validate_origin(
    origin: &super::super::origin_evidence::OriginEvidence,
    universe: &[String],
) -> Result<(), String> {
    use std::collections::BTreeSet;

    use super::super::origin_evidence::OriginAvailability;
    let snapshots = origin
        .licensing
        .as_ref()
        .ok_or("required licensing construction snapshots missing")?;
    let functions: BTreeSet<_> = origin
        .functions
        .iter()
        .map(|row| row.function.clone())
        .collect();
    let universe: BTreeSet<_> = universe.iter().cloned().collect();
    if !functions.is_empty() && snapshots.is_empty() {
        return Err("empty licensing construction family".into());
    }
    let mut offset = 0u32;
    for snapshot in snapshots {
        if snapshot.offset != offset || snapshot.metadata.constructions == 0 {
            return Err("noncontiguous or duplicate licensing construction namespace".into());
        }
        let end = offset
            .checked_add(snapshot.metadata.constructions)
            .ok_or("construction namespace overflow")?;
        let metadata_functions: BTreeSet<_> =
            snapshot.metadata.occurrences.keys().cloned().collect();
        let slot_keys: BTreeSet<_> = snapshot.metadata.slot_keys.iter().cloned().collect();
        if metadata_functions != functions
            || slot_keys != universe
            || slot_keys.len() != snapshot.metadata.slot_keys.len()
        {
            return Err("licensing snapshot function/slot universe mismatch".into());
        }
        snapshot.validate()?;
        for function in &origin.functions {
            let ownership = &function.ownership;
            macro_rules! compare {
                ($flat:ident, $recorded:ident, $global:expr) => {{
                    let OriginAvailability::Present(rows) = &ownership.$flat else {
                        return Err("missing flat ownership family".into());
                    };
                    let mut actual: Vec<_> = rows
                        .iter()
                        .filter(|row| {
                            row.point.construction >= offset && row.point.construction < end
                        })
                        .cloned()
                        .collect();
                    for row in &mut actual {
                        row.point.construction -= offset;
                    }
                    let expected: Vec<_> = snapshot
                        .metadata
                        .$recorded
                        .iter()
                        .filter(|row| {
                            row.point.function.as_deref() == Some(function.function.as_str())
                                || ($global && row.point.function.is_none())
                        })
                        .cloned()
                        .collect();
                    if actual != expected {
                        return Err(concat!(
                            "snapshot/flat ownership mismatch: ",
                            stringify!($flat)
                        )
                        .into());
                    }
                }};
            }
            compare!(equations, equations, true);
            compare!(consumes, consumes, false);
            compare!(terminals, terminals, false);
            compare!(boundary_substitutions, boundaries, false);
            compare!(call_arg_registrations, registrations, false);
            let mut actual = function.occurrences.clone();
            let mut expected = snapshot.metadata.occurrences[&function.function].clone();
            actual.sort();
            expected.sort();
            if actual != expected {
                return Err("snapshot/source occurrence mismatch".into());
            }
        }
        offset = end;
    }
    for function in &origin.functions {
        macro_rules! covered {
            ($family:ident) => {
                if let OriginAvailability::Present(rows) = &function.ownership.$family {
                    if rows.iter().any(|row| row.point.construction >= offset) {
                        return Err(concat!(
                            "flat ownership construction not covered: ",
                            stringify!($family)
                        )
                        .into());
                    }
                }
            };
        }
        covered!(equations);
        covered!(consumes);
        covered!(terminals);
        covered!(boundary_substitutions);
        covered!(call_arg_registrations);
    }
    Ok(())
}
