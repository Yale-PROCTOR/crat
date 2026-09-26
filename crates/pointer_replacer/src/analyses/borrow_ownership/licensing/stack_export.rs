//! Accepted stack-entry justification. Capture identities are transient and
//! never semantic inputs; portable proofs use the explicitly assigned namespace.
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    rc::{Rc, Weak},
};

use serde::{Deserialize, Serialize};

use super::{
    super::{
        export,
        origin_evidence::OriginEvidence,
        portable_export::{ExportFamily, PortableExport},
    },
    facts::Facts,
    snapshot::Snapshot,
    stack_entry::KnownStackEntry,
};

thread_local! {
    static NAMESPACES: RefCell<Vec<(Weak<Facts>, u32)>> = const { RefCell::new(Vec::new()) };
}

pub(crate) struct CaptureScope(Vec<(Weak<Facts>, u32)>);
impl Drop for CaptureScope {
    fn drop(&mut self) {
        NAMESPACES.with(|rows| *rows.borrow_mut() = std::mem::take(&mut self.0));
    }
}
pub(crate) fn enter_capture() -> CaptureScope {
    CaptureScope(NAMESPACES.with(|rows| std::mem::take(&mut *rows.borrow_mut())))
}
pub(crate) fn record_namespace(facts: &Rc<Facts>, offset: u32) {
    NAMESPACES.with(|rows| rows.borrow_mut().push((Rc::downgrade(facts), offset)));
}
fn namespace(facts: &Rc<Facts>) -> Option<u32> {
    NAMESPACES.with(|rows| {
        let rows = rows.borrow();
        let mut matching = rows
            .iter()
            .filter(|(old, _)| old.upgrade().is_some_and(|old| Rc::ptr_eq(&old, facts)));
        let (_, offset) = matching.next()?;
        matching.next().is_none().then_some(*offset)
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Accepted {
    pub(crate) snapshot_offset: u32,
    pub(crate) retirement_round: usize,
    pub(crate) closed_call_world: bool,
    pub(crate) proofs: Vec<KnownStackEntry>,
    pub(crate) original_cell_guards: Vec<(super::facts::EquationId, bool)>,
    pub(crate) traversal_guards: Vec<(super::facts::EquationId, bool)>,
    pub(crate) traversal_owns: Vec<(super::transport::Node, bool)>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) fold_guards: Option<Vec<(super::facts::EquationId, bool)>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) fold_values: Option<super::fold_custody::Values>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) traversal_loans: Vec<super::traversal_replay::Receipt>,
}

/// Called at the actual Mode-A/L2 accepting branch, after this round's replay.
/// No query, inferred last construction, or failed-round fallback is available.
pub(crate) fn accept(facts: Option<Rc<Facts>>) {
    if !export::capturing() {
        return;
    }
    let Some(offset) = facts.as_ref().and_then(namespace) else {
        return;
    };
    let selections = facts
        .as_ref()
        .and_then(|facts| super::model_selection::current(facts).and_then(|s| s.values(facts)))
        .unwrap_or_default();
    let values_for = |operation: &str| {
        selections
            .iter()
            .filter(|(id, _)| {
                facts.as_ref().is_some_and(|f| {
                    f.equations.iter().any(|e| {
                        e.point.construction == id.construction
                            && e.ordinal == id.ordinal
                            && e.operation == operation
                    })
                })
            })
            .map(|(id, value)| (*id, *value))
            .collect::<Vec<_>>()
    };
    let original_cell_guards = values_for("guarded-original-cell-frame");
    let traversal_guards = values_for("guarded-traversal-call");
    let fold_guards = facts.as_ref().and_then(|facts| {
        facts
            .fold_declarations
            .as_ref()
            .map(|_| values_for("guarded-fold-call"))
    });
    let fold_values = facts
        .as_ref()
        .and_then(|f| super::model_selection::current(f).and_then(|s| s.fold_values(f)));
    let traversal_owns = facts
        .as_ref()
        .and_then(|f| super::model_selection::current(f).and_then(|s| s.traversal_ownership(f)))
        .unwrap_or_default();
    export::record(|capture| {
        let Some(round) = capture.retirement_rounds.len().checked_sub(1) else {
            return;
        };
        let Some(review) = &capture.source_retirement else {
            return;
        };
        if capture.retirement_rounds.get(round) != Some(review) {
            return;
        }
        capture.stack_entry_final = Some(Accepted {
            snapshot_offset: offset,
            retirement_round: round,
            closed_call_world: super::stack_entry::current_world()
                == super::stack_entry::CallWorld::ClosedProgram,
            proofs: review.known_stack_entries.clone(),
            original_cell_guards,
            traversal_guards,
            traversal_owns,
            fold_guards,
            fold_values,
            traversal_loans: capture.traversal_replay.clone().unwrap_or_default(),
        });
    });
}

impl Accepted {
    pub(crate) fn stamp(&self) -> serde_json::Value {
        let mut stamp = serde_json::json!({"snapshot_offset": self.snapshot_offset, "retirement_round": self.retirement_round, "closed_call_world": self.closed_call_world,"original_cell_guards":self.original_cell_guards,"traversal_guards":self.traversal_guards,"traversal_owns":self.traversal_owns});
        if !self.traversal_loans.is_empty() {
            stamp["traversal_loans"] = serde_json::json!(self.traversal_loans);
        }
        if let Some(fold_guards) = &self.fold_guards {
            stamp["fold_guards"] = serde_json::json!(fold_guards);
        }
        if let Some(values) = &self.fold_values {
            stamp["fold_values"] = serde_json::json!(values);
        }
        stamp
    }
}

pub(crate) fn collect(capture: &export::BoExport) -> Option<Accepted> {
    let accepted = capture.stack_entry_final.as_ref()?;
    let review = capture.source_retirement.as_ref()?;
    if review.known_stack_entries != accepted.proofs
        || capture.retirement_rounds.get(accepted.retirement_round) != Some(review)
        || accepted.retirement_round.checked_add(1) != Some(capture.retirement_rounds.len())
    {
        return None;
    }
    Some(accepted.clone())
}

pub(crate) fn validate(
    origin: &OriginEvidence,
    portable: &PortableExport,
    model: &BTreeMap<String, String>,
) -> Result<(), String> {
    let final_rows = &portable.families[&ExportFamily::RetirementFinal].records;
    let final_row = final_rows.first().ok_or("missing final retirement row")?;
    let empty = serde_json::json!([]);
    let final_proofs = final_row
        .fields
        .get("known_stack_entries")
        .unwrap_or(&empty);
    let Some(accepted) = &origin.stack_entry_final else {
        if !origin.functions.is_empty() || final_proofs != &empty {
            return Err("missing accepted stack-entry proof".into());
        }
        return Ok(());
    };
    if final_row.fields.get("stack_entry_acceptance") != Some(&accepted.stamp()) {
        return Err("accepted stack-entry namespace/branch stamp mismatch".into());
    }
    let rounds = &portable.families[&ExportFamily::RetirementRounds].records;
    let round = rounds
        .iter()
        .find(|row| {
            row.fields.get("round").and_then(serde_json::Value::as_u64)
                == Some(accepted.retirement_round as u64)
        })
        .ok_or("accepted stack-entry retirement round missing")?;
    if rounds.len()
        != accepted
            .retirement_round
            .checked_add(1)
            .ok_or("retirement round overflow")?
        || round.fields.get("known_stack_entries").unwrap_or(&empty) != final_proofs
        || serde_json::to_value(&accepted.proofs).map_err(|e| e.to_string())? != *final_proofs
    {
        return Err("accepted stack-entry final/round proof mismatch".into());
    }
    if !accepted.proofs.is_empty() && !accepted.closed_call_world {
        return Err("stack-entry proof lacks closed-world attestation".into());
    }
    let snapshot = one(origin
        .licensing
        .as_ref()
        .ok_or("missing licensing snapshots")?
        .iter()
        .filter(|row| row.offset == accepted.snapshot_offset))?;
    super::fold_declaration::validate_selection_coverage(
        &snapshot.metadata.facts(),
        &snapshot.metadata.guard_aliases.iter().copied().collect(),
        accepted.fold_guards.as_deref(),
    )?;
    super::fold_custody::validate(snapshot, accepted, model)?;
    // Completeness is independent of the exported proof lists. In the current
    // C05 subset this selected role always uses the exact original-free/entry
    // comparison; producing or retained-return roles are not covered here.
    let guard_values: BTreeMap<_, _> = accepted.original_cell_guards.iter().copied().collect();
    let expected_guards: BTreeSet<_> = snapshot
        .metadata
        .equations
        .iter()
        .filter(|e| e.operation == "guarded-original-cell-frame")
        .map(|e| super::facts::EquationId {
            construction: e.point.construction,
            ordinal: e.ordinal,
        })
        .collect();
    if guard_values.len() != accepted.original_cell_guards.len()
        || guard_values.keys().copied().collect::<BTreeSet<_>>() != expected_guards
    {
        return Err("accepted original-cell guard coverage differs".into());
    }
    let traversal_values: BTreeMap<_, _> = accepted.traversal_guards.iter().copied().collect();
    let expected_traversal: BTreeSet<_> = snapshot
        .metadata
        .equations
        .iter()
        .filter(|e| e.operation == "guarded-traversal-call")
        .map(|e| super::facts::EquationId {
            construction: e.point.construction,
            ordinal: e.ordinal,
        })
        .collect();
    if traversal_values.len() != accepted.traversal_guards.len()
        || traversal_values.keys().copied().collect::<BTreeSet<_>>() != expected_traversal
    {
        return Err("accepted traversal guard coverage differs".into());
    }
    super::traversal_call::validate_valuation(
        &snapshot.metadata.facts(),
        &snapshot.traversal_calls,
        &traversal_values,
        &accepted.traversal_owns,
    )?;
    for (guard, _) in accepted
        .traversal_guards
        .iter()
        .filter(|(_, selected)| *selected)
    {
        if !accepted.closed_call_world
            || !snapshot.metadata.frame_attested
            || snapshot.caller_coverage != super::caller_coverage::Status::Complete
        {
            return Err("selected traversal lacks closed frame".into());
        }
        let index = snapshot
            .traversal_calls
            .iter()
            .position(|c| c.guard == *guard)
            .ok_or("selected traversal lacks call proof")?;
        let proof = snapshot
            .traversal_correspondences
            .get(index)
            .and_then(|p| p.as_ref().ok())
            .ok_or("selected traversal correspondence held")?;
        let call = &proof.candidate.call;
        let expected_calls: BTreeSet<_> = snapshot
            .metadata
            .caller_coverage
            .as_ref()
            .ok_or("selected traversal compiler coverage missing")?
            .local_calls
            .iter()
            .filter(|c| c.target == call.callee)
            .map(|c| (&c.site.function, c.site.block, c.site.statement))
            .collect();
        let group: Vec<_> = snapshot
            .traversal_calls
            .iter()
            .filter(|c| c.call.callee == call.callee)
            .collect();
        let represented: BTreeSet<_> = group
            .iter()
            .map(|c| (&c.call.caller, c.call.block, c.call.statement))
            .collect();
        if expected_calls.is_empty()
            || expected_calls != represented
            || group.len() != expected_calls.len()
        {
            return Err("selected traversal independent call coverage differs".into());
        }
        for ordinal in [
            proof.candidate.argument_boundary,
            proof.candidate.receiver_boundary,
        ] {
            let boundary = snapshot
                .metadata
                .boundaries
                .iter()
                .find(|b| b.point.construction == call.construction && b.ordinal == ordinal)
                .ok_or("selected traversal boundary missing")?;
            if !boundary.unmatched_actual_vars.is_empty()
                || !boundary.unmatched_formal_vars.is_empty()
            {
                return Err("selected traversal unmatched components".into());
            }
        }

        let input = super::traversal_call::input_target(&snapshot.metadata.facts(), proof)
            .ok_or("selected traversal lacks safe actual")?;
        if !matches!(
            model.get(&input.kind_key).map(String::as_str),
            Some("ref" | "owning")
        ) || input
            .parent_key
            .as_ref()
            .is_some_and(|k| !matches!(model.get(k).map(String::as_str), Some("ref" | "owning")))
        {
            return Err("selected traversal lacks safe actual".into());
        }
        for key in [
            format!("{}::_{}@d0", call.callee, proof.candidate.parameter),
            format!("{}::_0@d0", call.callee),
            format!("{}::_{}@d0", call.caller, proof.native.receiver.local),
        ] {
            if model.get(&key).map(String::as_str) != Some("ref") {
                return Err("selected traversal view kind differs".into());
            }
        }
        for candidate in snapshot
            .traversal_calls
            .iter()
            .filter(|c| c.call.callee == call.callee)
        {
            if traversal_values.get(&candidate.guard) != Some(&true) {
                return Err("selected traversal call group differs".into());
            }
        }
        for id in &proof.traversal.readers {
            let eq = snapshot
                .metadata
                .equations
                .iter()
                .find(|e| e.point.construction == id.construction && e.ordinal == id.ordinal)
                .ok_or("selected traversal reader missing")?;
            let reader = snapshot
                .reader_candidates
                .iter()
                .find(|r| {
                    r.function == call.callee
                        && Some(r.block) == eq.point.block
                        && Some(r.statement) == eq.point.statement
                })
                .ok_or("selected traversal reader role missing")?;
            let field = model.get(&reader.field_key).map(String::as_str);
            if !matches!(field, Some("ref" | "owning"))
                || (field == Some("owning")
                    && model
                        .get(&format!(
                            "{}::_{}@d0",
                            reader.function, reader.destination.local
                        ))
                        .map(String::as_str)
                        != Some("ref"))
            {
                return Err("selected traversal reader kind differs".into());
            }
        }
    }
    super::traversal_replay::validate_export(accepted, snapshot, portable)?;
    let facts = snapshot.metadata.facts();
    let aliases: BTreeMap<_, _> = snapshot.metadata.guard_aliases.iter().copied().collect();
    let mut required = BTreeSet::new();
    for chain in &snapshot.complete_chains {
        let proof = super::chain_entry::expected(&facts, chain, &aliases)
            .ok_or("invalid accepted chain entry basis")?;
        // The narrow closed chain's existing split/zero and call equations
        // make an owning field imply both native guards. A hard witness pins
        // this converse; kinds alone never select the runtime comparison.
        let owning = model.get(&chain.put.field_key).map(String::as_str) == Some("owning");
        let selected = guard_values.get(&chain.release_guard) == Some(&true);
        if owning != selected
            || owning != (guard_values.get(&chain.put_guard) == Some(&true))
            || (selected && model.get(&proof.parameter_slot).map(String::as_str) != Some("ref"))
        {
            return Err("accepted chain guard/kind converse differs".into());
        }
        if selected {
            for (function, argument) in [
                (&chain.put.call.callee, chain.put.argument),
                (&chain.release.call.callee, chain.release.argument),
                (&chain.effects.field_load.function, 0),
            ] {
                let entry = one(facts.boundary_substitutions.iter().filter(|entry| {
                    entry.role == super::super::ownership_boundary::Role::Entry
                        && entry.point.construction == chain.put.call.construction
                        && entry.point.function.as_ref() == Some(function)
                        && entry.argument_index == Some(argument)
                }))?;
                let parameter = entry.formal_local.ok_or("chain parent identity missing")?;
                if model
                    .get(&format!("{function}::_{parameter}@d0"))
                    .map(String::as_str)
                    != Some("ref")
                {
                    return Err("accepted chain parent kind differs".into());
                }
            }
            required.insert((proof.callee, proof.parameter, proof.free));
        }
    }
    for candidate in &snapshot.reference_effects.candidates {
        let boundary = one(snapshot.metadata.boundaries.iter().filter(|row| {
            row.point.construction == candidate.construction && row.ordinal == candidate.boundary
        }))?;
        let parameter = boundary
            .formal_local
            .ok_or("reference effect parameter missing")?;
        let view = one(snapshot.metadata.consumes.iter().filter(|row| {
            row.point.construction == candidate.construction
                && row.ordinal == candidate.scalar_view_consume
        }))?;
        let is = |key: &str, kind: &str| model.get(key).map(String::as_str) == Some(kind);
        if is(
            &format!("{}::_{}@d0", candidate.call.callee, parameter),
            "ref",
        ) && is(
            &format!("{}::_{}@d0", candidate.function, view.local),
            "ref",
        ) && is(&candidate.field_key, "owning")
        {
            required.insert((candidate.call.callee.clone(), parameter, candidate.free));
        }
    }
    let mut keys = BTreeSet::new();
    for proof in &accepted.proofs {
        if !keys.insert((proof.callee.clone(), proof.parameter, proof.free)) {
            return Err("duplicate applied stack-entry identity".into());
        }
        validate_proof(proof, snapshot, model, &guard_values)?;
    }
    if keys != required {
        return Err("incomplete selected stack-entry obligations".into());
    }
    Ok(())
}

fn validate_proof(
    proof: &KnownStackEntry,
    snapshot: &Snapshot,
    model: &BTreeMap<String, String>,
    guard_values: &BTreeMap<super::facts::EquationId, bool>,
) -> Result<(), String> {
    let facts = snapshot.metadata.facts();
    let aliases = snapshot.metadata.guard_aliases.iter().copied().collect();
    let free = one(facts.equations.iter().filter(|row| {
        row.point.construction == proof.free.construction && row.ordinal == proof.free.ordinal
    }))?;
    if proof.construction != proof.free.construction
        || proof.free_point != free.point
        || free.point.function.as_ref() != Some(&proof.callee)
        || free.operation != "sink"
        || proof.parameter_slot != format!("{}::_{}@d0", proof.callee, proof.parameter)
        || model.get(&proof.parameter_slot).map(String::as_str) != Some("ref")
        || proof.callers.is_empty()
    {
        return Err("invalid applied stack-entry/free identity".into());
    }
    if proof
        .callers
        .iter()
        .any(|caller| caller.original_cell_guard.is_some())
    {
        let chain = one(snapshot.complete_chains.iter().filter(|chain| {
            chain.release.call.callee == proof.callee && chain.free == proof.free
        }))?;
        if super::chain_entry::expected(&facts, chain, &aliases).as_ref() != Some(proof)
            || guard_values.get(&chain.put_guard) != Some(&true)
            || guard_values.get(&chain.release_guard) != Some(&true)
            || model.get(&chain.put.field_key).map(String::as_str) != Some("owning")
        {
            return Err("invalid selected chain caller/cell/source/free".into());
        }
        return Ok(());
    }
    let mut calls = BTreeSet::new();
    for caller in &proof.callers {
        if !calls.insert(caller.call.clone()) {
            return Err("duplicate stack caller".into());
        }
        let candidate = one(snapshot
            .reference_effects
            .candidates
            .iter()
            .filter(|row| row.call == caller.call))?;
        let boundary = one(facts.boundary_substitutions.iter().filter(|row| {
            row.point.construction == candidate.construction && row.ordinal == candidate.boundary
        }))?;
        if candidate.construction != proof.construction
            || candidate.free != proof.free
            || candidate.call.callee != proof.callee
            || boundary.formal_local != Some(proof.parameter)
            || candidate.cell_place != caller.cell
            || candidate.formation != caller.formation
            || candidate.field_key != caller.field_key
            || model.get(&caller.field_key).map(String::as_str) != Some("owning")
            || model
                .get(&format!(
                    "{}::_{}@d0",
                    candidate.function,
                    facts
                        .consumes
                        .iter()
                        .find(|row| row.point.construction == candidate.construction
                            && row.ordinal == candidate.scalar_view_consume)
                        .ok_or("missing scalar view consume")?
                        .local
                ))
                .map(String::as_str)
                != Some("ref")
        {
            return Err("invalid selected stack caller/cell".into());
        }
        let certificate = super::ref_effects::certify_consumed_output(&facts, candidate, &aliases)
            .map_err(|e| format!("stack output certificate: {e:?}"))?;
        let field = one(snapshot
            .field_support
            .iter()
            .filter(|row| row.field_key == caller.field_key && row.supported()))?;
        let store = one(field
            .stores
            .iter()
            .filter(|row| row.equation == caller.store))?;
        if store.site.function != caller.call.caller
            || store.site.place.local != caller.cell.local
            || store.destination_def != candidate.scalar_before
            || store.meet.source != caller.source
            || store.meet.terminal != certificate.free
            || !store
                .discharged_outputs
                .iter()
                .any(|row| row.certificate == certificate && row.output.source == caller.source)
        {
            return Err("invalid stack caller source/store/output".into());
        }
    }
    let actual_calls: BTreeSet<_> = facts
        .source_occurrences
        .values()
        .flat_map(|rows| rows.iter())
        .filter_map(|row| {
            (row.callee.as_ref()
                == Some(&super::super::origin_evidence::SourceCallee::Local(
                    proof.callee.clone(),
                )))
            .then(|| super::matched::CallKey {
                construction: proof.construction,
                caller: row.site.function.clone(),
                block: row.site.block,
                statement: row.site.statement,
                callee: proof.callee.clone(),
            })
        })
        .collect();
    if actual_calls != calls {
        return Err("incomplete accepted stack caller roster".into());
    }
    Ok(())
}
fn one<T>(mut rows: impl Iterator<Item = T>) -> Result<T, String> {
    let row = rows.next().ok_or("missing stack-entry correspondence")?;
    if rows.next().is_some() {
        return Err("ambiguous stack-entry correspondence".into());
    }
    Ok(row)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn c05_stack_export_namespaces_use_exact_facts_and_restore_after_unwind() {
        let first = Rc::new(Facts::default());
        let identical = Rc::new(Facts::default());
        let outer = enter_capture();
        record_namespace(&first, 3);
        record_namespace(&identical, 8);
        assert_eq!(namespace(&first), Some(3));
        assert_eq!(namespace(&identical), Some(8));
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _inner = enter_capture();
            assert_eq!(namespace(&first), None);
            record_namespace(&first, 0);
            assert_eq!(namespace(&first), Some(0));
            panic!("exercise nested capture restoration");
        }));
        assert_eq!(namespace(&first), Some(3));
        assert_eq!(namespace(&identical), Some(8));
        record_namespace(&first, 12);
        assert_eq!(
            namespace(&first),
            None,
            "duplicate registration cannot choose a namespace"
        );
        drop(outer);
        assert_eq!(namespace(&first), None);
    }
}
