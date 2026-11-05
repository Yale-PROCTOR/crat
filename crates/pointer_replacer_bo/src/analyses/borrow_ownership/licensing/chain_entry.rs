//! Complete original-cell release-entry evidence.
//! Evidence for one existing heap-Free/entry comparison; no permission or law change.
use std::{
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use super::{
    super::{crate_slots::CrateSlots, ownership_boundary::Role, solver::SlotRef},
    caller_coverage::{self, Coverage, Status},
    chain_permission,
    facts::{EquationId, Facts},
    field_support,
    matched::MatchedTransport,
    model_selection::Selection,
    stack_entry::{self, CallWorld, KnownStackEntry, StackCaller},
    value_origins::ValueOrigins,
};
use crate::utils::rustc::RustProgram;

fn one<T>(items: impl IntoIterator<Item = T>) -> Option<T> {
    let mut items = items.into_iter();
    let item = items.next()?;
    items.next().is_none().then_some(item)
}

/// Reconstruct expected metadata from current facts, never frozen field support.
/// This function proves neither actual selection nor compiler ABI/local-type facts.
pub(crate) fn expected(
    facts: &Facts,
    chain: &chain_permission::Proof,
    aliases: &BTreeMap<EquationId, EquationId>,
) -> Option<KnownStackEntry> {
    if !facts.frame_attested
        || facts.constructions != 1
        || caller_coverage::assess(facts) != Status::Complete
    {
        return None;
    }
    let matched = MatchedTransport::build_metadata(facts, aliases).ok()?;
    let origins = ValueOrigins::build_metadata(facts, aliases).ok()?;
    let fields = field_support::audit(facts, &facts.field_support_inputs, &matched, &origins);
    let field = one(fields
        .iter()
        .filter(|f| f.field_key == chain.release.field_key))?;
    if chain_permission::certify(facts, field, matched.guard_aliases()).as_ref() != Some(chain) {
        return None;
    }
    let store = one(&field.input_stores)?;
    let app = one(&store.applications)?;
    let alternative = one(&app.alternatives)?;
    // certify already checks exact source/free lineages, return continuation,
    // both native arms and intermediate original cell. Keep basis explicit.
    if store.equation != chain.store
        || alternative.free.source.endpoint != chain.source
        || app.application.call != chain.put.call
    {
        return None;
    }
    let release = &chain.release;
    let boundary = one(facts.boundary_substitutions.iter().filter(|b| {
        b.point.construction == release.call.construction && b.ordinal == release.boundary
    }))?;
    if boundary.role != Role::CallArgument
        || boundary.point.function.as_ref() != Some(&release.call.caller)
        || boundary.point.block != Some(release.call.block)
        || boundary.point.statement != Some(release.call.statement)
        || boundary.callee.as_ref() != Some(&release.call.callee)
    {
        return None;
    }
    let parameter = boundary.formal_local?;
    let parameter_slot = format!("{}::_{}@d0", release.call.callee, parameter);
    // The live collector joins the compiler SlotRef; portable validation joins
    // this key to the independent exported model/universe.
    let free = one(facts.equations.iter().filter(|e| {
        e.point.construction == chain.free.construction && e.ordinal == chain.free.ordinal
    }))?;
    if free.operation != "sink"
        || free.validate().is_err()
        || free.point.function.as_ref() != Some(&release.call.callee)
        || free.endpoint.as_ref()?.callee != "free"
        || free.endpoint.as_ref()?.outcome.is_some()
    {
        return None;
    }
    Some(KnownStackEntry {
        construction: release.call.construction,
        callee: release.call.callee.clone(),
        parameter,
        parameter_slot,
        free: chain.free,
        free_point: free.point.clone(),
        callers: vec![StackCaller {
            call: release.call.clone(),
            cell: release.cell.clone(),
            formation: release.formation.clone(),
            field_key: release.field_key.clone(),
            store: chain.store,
            source: alternative.free.source.clone(),
            original_cell_guard: Some(chain.release_guard),
        }],
    })
}

/// Apply only same-model true predicates under the existing explicit frame.
/// Empty means unavailable/held; it must never mean caller coverage is vacuous.
pub(crate) fn collect(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    facts: &Rc<Facts>,
    selection: &Selection,
) -> Vec<KnownStackEntry> {
    use rustc_middle::{
        mir::{Local, Operand, TerminatorKind},
        ty::TyKind,
    };
    if stack_entry::current_world() != CallWorld::ClosedProgram
        || !facts.frame_attested
        || facts.constructions != 1
        || caller_coverage::assess(facts) != Status::Complete
    {
        return vec![];
    }
    // Reobserve exact compiler graph; recorded Complete alone is not sufficient.
    let coverage = Coverage::collect(program);
    if facts.caller_coverage.as_ref() != Some(&coverage) {
        return vec![];
    }
    let tcx = program.tcx;
    let functions: rustc_hash::FxHashSet<_> = program.functions.iter().copied().collect();
    if functions.len() != program.functions.len()
        || functions != tcx.hir_body_owners().collect::<rustc_hash::FxHashSet<_>>()
        || functions
            != slots
                .fn_local_slots
                .keys()
                .copied()
                .collect::<rustc_hash::FxHashSet<_>>()
    {
        return vec![];
    }
    let definitions: BTreeMap<_, _> = functions
        .iter()
        .map(|d| (tcx.def_path_str(*d), *d))
        .collect();
    if definitions.len() != functions.len() {
        return vec![];
    }

    let matched = MatchedTransport::build(facts);
    let origins = ValueOrigins::build(facts);
    let fields = field_support::audit(facts, &facts.field_support_inputs, &matched, &origins);
    let mut entries = Vec::new();
    for field in fields {
        let Some(chain) = chain_permission::certify(facts, &field, matched.guard_aliases()) else {
            continue;
        };
        if selection.value(facts, chain.put_guard) != Some(true)
            || selection.value(facts, chain.release_guard) != Some(true)
        {
            continue;
        }
        let Some(entry) = expected(facts, &chain, matched.guard_aliases()) else { continue };
        let Some(caller) = definitions.get(&chain.release.call.caller).copied() else { continue };
        let Some(callee) = definitions.get(&entry.callee).copied() else { continue };
        // Same exclusions as C05. Public Rust spelling is not an attestation.
        if tcx.fn_sig(callee).instantiate_identity().skip_binder().abi != rustc_abi::ExternAbi::Rust
            || tcx.codegen_fn_attrs(callee).contains_extern_indicator()
        {
            continue;
        }
        let calls: BTreeSet<_> = coverage
            .local_calls
            .iter()
            .filter(|c| c.target == entry.callee)
            .collect();
        let Some(call) = one(calls) else { continue };
        if call.site.function != chain.release.call.caller
            || call.site.block != chain.release.call.block
            || call.site.statement != chain.release.call.statement
        {
            continue;
        }
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let cell = Local::from_u32(chain.release.cell.local);
        let Some(declaration) = body.local_decls.get(cell) else { continue };
        let TyKind::Adt(adt, _) = declaration.ty.kind() else { continue };
        if cell.as_usize() <= body.arg_count
            || !chain.release.cell.projection.is_empty()
            || !adt.is_struct()
            || adt.non_enum_variant().fields.len() != 1
            || chain.release.field_key != format!("{}::field0@d0", tcx.def_path_str(adt.did()))
        {
            continue;
        }
        let Some((_, block)) = body
            .basic_blocks
            .iter_enumerated()
            .find(|(b, _)| b.as_u32() == chain.release.call.block)
        else {
            continue;
        };
        if block.statements.len() != chain.release.call.statement {
            continue;
        }
        let TerminatorKind::Call { func, args, .. } = &block.terminator().kind else { continue };
        let TyKind::FnDef(target, _) = *func.ty(&*body, tcx).kind() else { continue };
        let Some(argument) = one(args.iter()) else { continue };
        let actual = match &argument.node {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local.as_u32(),
            _ => continue,
        };
        let Some(registration) = one(facts.call_arg_registrations.iter().filter(|r| {
            r.point.construction == chain.release.call.construction
                && r.ordinal == chain.release.registration
        })) else {
            continue;
        };
        if target.as_local() != Some(callee)
            || !registration.by_reference
            || actual != registration.proxy_local
        {
            continue;
        }
        let Some(slot) = slots
            .fn_local_slots
            .get(&callee)
            .and_then(|u| u.slot_for_local_depth(Local::from_u32(entry.parameter), 0))
        else {
            continue;
        };
        if facts.slot_refs.get(&entry.parameter_slot) != Some(&SlotRef::Local(callee, slot)) {
            continue;
        }
        // No second release caller is admitted by this initial single-chain subset.
        if !entries.contains(&entry) {
            entries.push(entry);
        }
    }
    entries
}
