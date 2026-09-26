//! Known-stack entry evidence for one exact original free comparison. This
//! never changes generic Input/Stack overlap or unwinding/retirement policy.

use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet},
    marker::PhantomData,
    rc::Rc,
};

use super::{
    super::{
        a5_overlap::WholeProgramAttestation, crate_slots::CrateSlots,
        ownership_access::PlaceSyntax, ownership_evidence::Point,
    },
    facts::{EquationId, Facts},
    matched::{CallKey, SourceInstance},
    ref_effects::Candidate,
};
use crate::utils::rustc::RustProgram;

/// Completeness cannot be inferred from Rust ABI or public visibility alone.
/// The integration must supply an established whole-program premise; absence
/// of that premise is an explicit hold, not an empty caller set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CallWorld {
    ClosedProgram,
    Unknown,
}

thread_local! {
    static WORLD: Cell<CallWorld> = const { Cell::new(CallWorld::Unknown) };
}

pub(crate) struct WorldScope {
    previous: CallWorld,
    _same_thread: PhantomData<Rc<()>>,
}

impl Drop for WorldScope {
    fn drop(&mut self) {
        WORLD.with(|world| world.set(self.previous));
    }
}

pub(crate) fn enter_world(attestation: Option<WholeProgramAttestation>) -> WorldScope {
    let next = match attestation {
        Some(WholeProgramAttestation::FrozenBenchmarkGraph) => CallWorld::ClosedProgram,
        None => CallWorld::Unknown,
    };
    WorldScope {
        previous: WORLD.with(|world| world.replace(next)),
        _same_thread: PhantomData,
    }
}

pub(crate) fn current_world() -> CallWorld {
    WORLD.with(Cell::get)
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct StackCaller {
    pub(crate) call: CallKey,
    pub(crate) cell: PlaceSyntax,
    pub(crate) formation: Point,
    pub(crate) field_key: String,
    pub(crate) store: EquationId,
    pub(crate) source: SourceInstance,
    pub(crate) original_cell_guard: Option<EquationId>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct KnownStackEntry {
    pub(crate) construction: u32,
    pub(crate) callee: String,
    pub(crate) parameter: u32,
    pub(crate) parameter_slot: String,
    pub(crate) free: EquationId,
    pub(crate) free_point: Point,
    /// Nonempty complete caller roster, each with the selected exact cell.
    pub(crate) callers: Vec<StackCaller>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Pending {
    Implementation,
    OpenCallWorld,
    CompilerCoverage,
    UncoveredCaller,
    FunctionValueOrIndirect,
    ExposedEntry,
    UnmatchedMetadata,
}

/// `selected` is supplied from the active model by the eventual integration.
/// Candidate discovery alone is never interpreted as model selection. Even a
/// closed call world still needs exhaustive compiler use/call validation.
pub(crate) fn collect_known_stack_entries(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    facts: &Facts,
    selected: &[Candidate],
    world: CallWorld,
) -> Result<Vec<KnownStackEntry>, Pending> {
    use rustc_middle::{
        mir::{Local, Operand, TerminatorKind, visit::Visitor},
        ty::TyKind,
    };

    use super::{
        super::{ownership_boundary::Role, solver::SlotRef},
        matched::SourceLineage,
        ref_effects,
    };

    if world != CallWorld::ClosedProgram {
        return Err(Pending::OpenCallWorld);
    }
    if selected.is_empty() {
        return Err(Pending::UncoveredCaller);
    }
    if facts.constructions != 1 {
        return Err(Pending::UnmatchedMetadata);
    }
    let rebuilt = ref_effects::Plan::build(facts);
    let mut selected_calls = BTreeMap::new();
    for candidate in selected {
        if !rebuilt.candidates.contains(candidate)
            || selected_calls
                .insert(candidate.call.clone(), candidate)
                .is_some()
        {
            return Err(Pending::UnmatchedMetadata);
        }
    }
    let tcx = program.tcx;
    let functions: rustc_hash::FxHashSet<_> = program.functions.iter().copied().collect();
    // Any omitted closure, constant/static initializer, method, or nested body
    // leaves function-value/call coverage unproved in this initial subset.
    let compiler_bodies: rustc_hash::FxHashSet<_> = tcx.hir_body_owners().collect();
    if functions.len() != program.functions.len()
        || functions != compiler_bodies
        || slots
            .fn_local_slots
            .keys()
            .copied()
            .collect::<rustc_hash::FxHashSet<_>>()
            != functions
    {
        return Err(Pending::CompilerCoverage);
    }
    let definitions: BTreeMap<_, _> = functions
        .iter()
        .map(|did| (tcx.def_path_str(*did), *did))
        .collect();
    if definitions.len() != functions.len()
        || facts
            .source_occurrences
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != definitions.keys().cloned().collect::<BTreeSet<_>>()
    {
        return Err(Pending::CompilerCoverage);
    }
    let targets: BTreeSet<_> = selected
        .iter()
        .map(|candidate| candidate.call.callee.clone())
        .collect();
    for target in &targets {
        let did = *definitions.get(target).ok_or(Pending::UnmatchedMetadata)?;
        if tcx.fn_sig(did).instantiate_identity().skip_binder().abi != rustc_abi::ExternAbi::Rust
            || tcx.codegen_fn_attrs(did).contains_extern_indicator()
        {
            return Err(Pending::ExposedEntry);
        }
    }
    let mut actual_calls = BTreeMap::new();
    for &caller in &functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let caller_name = tcx.def_path_str(caller);
        let mut values = FunctionValues {
            tcx,
            body: &body,
            found: false,
        };
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                values.visit_statement(
                    statement,
                    rustc_middle::mir::Location {
                        block,
                        statement_index,
                    },
                );
            }
            let location = rustc_middle::mir::Location {
                block,
                statement_index: data.statements.len(),
            };
            match &data.terminator().kind {
                TerminatorKind::Call { func, args, .. }
                | TerminatorKind::TailCall { func, args, .. } => {
                    let TyKind::FnDef(target, _) = *func.ty(&*body, tcx).kind() else {
                        return Err(Pending::FunctionValueOrIndirect);
                    };
                    // The actual direct target is the one permitted FnDef use;
                    // function values in arguments remain escapes.
                    for arg in args {
                        values.visit_operand(&arg.node, location);
                    }
                    let target_name = tcx.def_path_str(target);
                    if targets.contains(&target_name) {
                        let [argument] = args.as_ref() else {
                            return Err(Pending::UncoveredCaller);
                        };
                        let local = match &argument.node {
                            Operand::Copy(place) | Operand::Move(place)
                                if place.projection.is_empty() =>
                            {
                                place.local.as_u32()
                            }
                            _ => return Err(Pending::UncoveredCaller),
                        };
                        let key = CallKey {
                            construction: 0,
                            caller: caller_name.clone(),
                            block: block.as_u32(),
                            statement: data.statements.len(),
                            callee: target_name,
                        };
                        if actual_calls.insert(key, local).is_some() {
                            return Err(Pending::CompilerCoverage);
                        }
                    }
                }
                TerminatorKind::InlineAsm { .. } => return Err(Pending::FunctionValueOrIndirect),
                _ => values.visit_terminator(data.terminator(), location),
            }
        }
        if values.found {
            return Err(Pending::FunctionValueOrIndirect);
        }
    }
    if actual_calls.is_empty()
        || actual_calls.keys().collect::<BTreeSet<_>>()
            != selected_calls.keys().collect::<BTreeSet<_>>()
    {
        return Err(Pending::UncoveredCaller);
    }
    let frozen = facts.licensing.as_ref().ok_or(Pending::UnmatchedMetadata)?;
    let mut entries: BTreeMap<(String, u32, EquationId), KnownStackEntry> = BTreeMap::new();
    for (key, candidate) in selected_calls {
        let caller = *definitions
            .get(&key.caller)
            .ok_or(Pending::UnmatchedMetadata)?;
        let callee = *definitions
            .get(&key.callee)
            .ok_or(Pending::UnmatchedMetadata)?;
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let cell = Local::from_u32(candidate.cell_place.local);
        let Some(declaration) = body.local_decls.get(cell) else {
            return Err(Pending::UnmatchedMetadata);
        };
        if cell.as_usize() <= body.arg_count
            || !candidate.cell_place.projection.is_empty()
            || !matches!(declaration.ty.kind(), TyKind::Adt(adt, _) if adt.is_struct())
        {
            return Err(Pending::UncoveredCaller);
        }
        let boundary = exactly_one(facts.boundary_substitutions.iter().filter(|row| {
            row.point.construction == candidate.construction && row.ordinal == candidate.boundary
        }))?;
        if boundary.role != Role::CallArgument {
            return Err(Pending::UnmatchedMetadata);
        }
        let parameter = boundary.formal_local.ok_or(Pending::UnmatchedMetadata)?;
        let registration = exactly_one(facts.call_arg_registrations.iter().filter(|row| {
            row.point.construction == candidate.construction
                && row.ordinal == candidate.registration
        }))?;
        if !registration.by_reference || actual_calls.get(&key) != Some(&registration.proxy_local) {
            return Err(Pending::UnmatchedMetadata);
        }
        let parameter_slot = format!("{}::_{}@d0", key.callee, parameter);
        let slot = slots
            .fn_local_slots
            .get(&callee)
            .and_then(|universe| universe.slot_for_local_depth(Local::from_u32(parameter), 0))
            .ok_or(Pending::UnmatchedMetadata)?;
        if facts.slot_refs.get(&parameter_slot) != Some(&SlotRef::Local(callee, slot)) {
            return Err(Pending::UnmatchedMetadata);
        }
        let certificate =
            ref_effects::certify_consumed_output(facts, candidate, frozen.matched.guard_aliases())
                .map_err(|_| Pending::UnmatchedMetadata)?;
        let field = exactly_one(
            frozen
                .field_support
                .iter()
                .filter(|row| row.field_key == candidate.field_key && row.supported()),
        )?;
        let store = exactly_one(field.stores.iter().filter(|row| {
            row.site.function == candidate.function
                && row.site.place.local == candidate.cell_place.local
                && row.destination_def == candidate.scalar_before
        }))?;
        if store.meet.terminal != certificate.free
            || !matches!(store.meet.source.lineage, SourceLineage::Exact(_))
            || store.meet.guards.get(&certificate.required_free.binding) != Some(&true)
            || !store
                .discharged_outputs
                .iter()
                .any(|row| row.certificate == certificate && row.output.source == store.meet.source)
        {
            return Err(Pending::UnmatchedMetadata);
        }
        let free = exactly_one(facts.equations.iter().filter(|row| {
            row.point.construction == candidate.free.construction
                && row.ordinal == candidate.free.ordinal
        }))?;
        let entry = entries
            .entry((key.callee.clone(), parameter, candidate.free))
            .or_insert_with(|| KnownStackEntry {
                construction: candidate.construction,
                callee: key.callee.clone(),
                parameter,
                parameter_slot,
                free: candidate.free,
                free_point: free.point.clone(),
                callers: Vec::new(),
            });
        entry.callers.push(StackCaller {
            call: key,
            cell: candidate.cell_place.clone(),
            formation: candidate.formation.clone(),
            field_key: candidate.field_key.clone(),
            store: store.equation,
            source: store.meet.source.clone(),
            original_cell_guard: None,
        });
    }
    if entries.values().any(|entry| entry.callers.is_empty()) {
        return Err(Pending::UncoveredCaller);
    }
    Ok(entries.into_values().collect())
}

fn exactly_one<T>(mut rows: impl Iterator<Item = T>) -> Result<T, Pending> {
    let row = rows.next().ok_or(Pending::UnmatchedMetadata)?;
    if rows.next().is_some() {
        return Err(Pending::UnmatchedMetadata);
    }
    Ok(row)
}

/// Used only on operands outside the direct callee position. Even an unused
/// function value is held; no pointer-target inference is attempted here.
struct FunctionValues<'a, 'tcx> {
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &'a rustc_middle::mir::Body<'tcx>,
    found: bool,
}

impl<'tcx> rustc_middle::mir::visit::Visitor<'tcx> for FunctionValues<'_, 'tcx> {
    fn visit_operand(
        &mut self,
        operand: &rustc_middle::mir::Operand<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
        if matches!(
            operand.ty(self.body, self.tcx).kind(),
            rustc_middle::ty::TyKind::FnDef(..) | rustc_middle::ty::TyKind::FnPtr(..)
        ) {
            self.found = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::{
        super::{
            super::{
                construction::construct_bo_into_a16_refined, execution_guard,
                mutability_facts::MutFacts, origins::compute_origins, solver::KindSolver,
            },
            ref_effects,
        },
        *,
    };

    const IFL3: &str = r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct H { ptr: *mut i32 }
pub unsafe fn release(h: *mut H) { free((*h).ptr as *mut core::ffi::c_void); }
pub unsafe fn f() -> i32 {
    let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *owner = 1;
    let mut h = H { ptr: owner };
    let before = *h.ptr;
    release(&mut h);
    before
}
"#;

    #[test]
    fn c05_stack_entry_world_restores_on_nested_scope_and_unwind() {
        assert_eq!(current_world(), CallWorld::Unknown);
        {
            let _closed = enter_world(Some(WholeProgramAttestation::FrozenBenchmarkGraph));
            assert_eq!(current_world(), CallWorld::ClosedProgram);
            {
                let _unknown = enter_world(None);
                assert_eq!(current_world(), CallWorld::Unknown);
            }
            assert_eq!(current_world(), CallWorld::ClosedProgram);
            let result = std::panic::catch_unwind(|| {
                let _unknown = enter_world(None);
                panic!("stack-entry scope restoration witness");
            });
            assert!(result.is_err());
            assert_eq!(current_world(), CallWorld::ClosedProgram);
        }
        assert_eq!(current_world(), CallWorld::Unknown);
    }

    // Same construction path as graph_tests, retaining the compiler program
    // because call completeness cannot be derived from licensing facts alone.
    fn with_program(code: &str, check: impl FnOnce(&RustProgram<'_>, &CrateSlots, &Facts) + Send) {
        ::utils::compilation::run_compiler_on_str(code, move |tcx| {
            let mut functions = Vec::new();
            let mut structs = Vec::new();
            for owner in tcx.hir_crate(()).owners.iter() {
                let Some(owner) = owner.as_owner() else { continue };
                let OwnerNode::Item(item) = owner.node() else { continue };
                match item.kind {
                    ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                    ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                    _ => {}
                }
            }
            let program = RustProgram {
                tcx,
                functions,
                structs,
            };
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let mutability = MutFacts::from_program(&program);
            let solver = KindSolver::new(&slots);
            let model_entries = execution_guard::model_entries();
            construct_bo_into_a16_refined(&program, &slots, &origins, &mutability, &solver)
                .unwrap();
            let facts = solver.ownership_facts().unwrap();
            check(&program, &slots, &facts);
            assert_eq!(
                [
                    solver.check_sat_count(),
                    solver.hard_check_count(),
                    solver.optimize_materialization_count(),
                    solver.lazy_plain_hard_check_count(),
                    solver.lazy_tracked_recheck_count(),
                    solver.lazy_plain_materialization_count(),
                ],
                [0; 6]
            );
            assert_eq!(execution_guard::model_entries(), model_entries);
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn c05_stack_entry_exact_closed_ifl3_call_and_free() {
        with_program(IFL3, |program, slots, facts| {
            // Hypothetical selected set: this tests an evidence producer, not
            // a claim that construction selected any guard or accepted a model.
            let selected = ref_effects::Plan::build(facts).candidates;
            assert_eq!(selected.len(), 1);
            let entries = collect_known_stack_entries(
                program,
                slots,
                facts,
                &selected,
                CallWorld::ClosedProgram,
            )
            .unwrap();
            assert_eq!(entries.len(), 1);
            let entry = &entries[0];
            let candidate = &selected[0];
            assert_eq!(entry.construction, candidate.construction);
            assert_eq!(entry.callee, candidate.call.callee);
            assert_eq!(entry.free, candidate.free);
            let boundary = facts
                .boundary_substitutions
                .iter()
                .find(|row| {
                    row.point.construction == candidate.construction
                        && row.ordinal == candidate.boundary
                })
                .unwrap();
            assert_eq!(Some(entry.parameter), boundary.formal_local);
            assert_eq!(
                entry.parameter_slot,
                format!("{}::_{}@d0", entry.callee, entry.parameter)
            );
            assert!(facts.slot_refs.contains_key(&entry.parameter_slot));
            let free = facts
                .equations
                .iter()
                .find(|row| {
                    row.point.construction == entry.free.construction
                        && row.ordinal == entry.free.ordinal
                })
                .unwrap();
            assert_eq!(entry.free_point, free.point);
            assert_eq!(entry.callers.len(), 1);
            let caller = &entry.callers[0];
            assert_eq!(caller.call, candidate.call);
            assert_eq!(caller.cell, candidate.cell_place);
            assert_eq!(caller.formation, candidate.formation);
            assert_eq!(caller.field_key, candidate.field_key);
            let field = facts
                .licensing
                .as_ref()
                .unwrap()
                .field_support
                .iter()
                .find(|row| row.field_key == caller.field_key)
                .unwrap();
            let store = field
                .stores
                .iter()
                .find(|store| store.equation == caller.store)
                .unwrap();
            assert_eq!(caller.source, store.meet.source);
            assert_eq!(store.destination_def, candidate.scalar_before);
        });
    }

    fn held(code: &str, expected: Pending) {
        with_program(code, move |program, slots, facts| {
            let selected = ref_effects::Plan::build(facts).candidates;
            assert!(
                !selected.is_empty(),
                "the original covered caller is still present"
            );
            assert_eq!(
                collect_known_stack_entries(
                    program,
                    slots,
                    facts,
                    &selected,
                    CallWorld::ClosedProgram
                ),
                Err(expected)
            );
        });
    }

    #[test]
    fn c05_stack_entry_rejects_extra_unknown_caller() {
        held(
            &format!("{IFL3}\npub unsafe fn extra(p: *mut H) {{ release(p); }}"),
            Pending::UncoveredCaller,
        );
    }

    #[test]
    fn c05_stack_entry_rejects_extra_heap_caller() {
        held(
            &format!(
                r#"{IFL3}
pub unsafe fn extra() {{
    let p = malloc(core::mem::size_of::<H>()) as *mut H;
    (*p).ptr = malloc(4) as *mut i32;
    release(p);
    free(p as *mut core::ffi::c_void);
}}
"#
            ),
            Pending::UncoveredCaller,
        );
    }

    #[test]
    fn c05_stack_entry_rejects_function_value_escape_and_indirect_call() {
        held(
            &format!("{IFL3}\npub fn escape() -> unsafe fn(*mut H) {{ release }}"),
            Pending::FunctionValueOrIndirect,
        );
        held(
            &format!(
                "{IFL3}\npub unsafe fn indirect(p: *mut H) {{ let callback: unsafe fn(*mut H) = release; callback(p); }}"
            ),
            Pending::FunctionValueOrIndirect,
        );
    }

    #[test]
    fn c05_stack_entry_rejects_open_world_and_explicit_export() {
        with_program(IFL3, |program, slots, facts| {
            let selected = ref_effects::Plan::build(facts).candidates;
            assert_eq!(
                collect_known_stack_entries(program, slots, facts, &selected, CallWorld::Unknown),
                Err(Pending::OpenCallWorld)
            );
        });
        held(
            &IFL3.replace(
                "pub unsafe fn release",
                "#[unsafe(no_mangle)] pub unsafe extern \"C\" fn release",
            ),
            Pending::ExposedEntry,
        );
    }

    #[test]
    fn c05_stack_entry_rejects_wrong_free_call_and_missing_selection() {
        with_program(IFL3, |program, slots, facts| {
            let selected = ref_effects::Plan::build(facts).candidates;
            assert_eq!(selected.len(), 1);
            let mut wrong_free = selected.clone();
            wrong_free[0].free = facts
                .equations
                .iter()
                .find(|row| row.operation == "source")
                .map(|row| EquationId {
                    construction: row.point.construction,
                    ordinal: row.ordinal,
                })
                .unwrap();
            assert_eq!(
                collect_known_stack_entries(
                    program,
                    slots,
                    facts,
                    &wrong_free,
                    CallWorld::ClosedProgram
                ),
                Err(Pending::UnmatchedMetadata)
            );
            let mut wrong_call = selected.clone();
            wrong_call[0].call.statement += 1;
            assert_eq!(
                collect_known_stack_entries(
                    program,
                    slots,
                    facts,
                    &wrong_call,
                    CallWorld::ClosedProgram
                ),
                Err(Pending::UnmatchedMetadata)
            );
            assert_eq!(
                collect_known_stack_entries(program, slots, facts, &[], CallWorld::ClosedProgram),
                Err(Pending::UncoveredCaller)
            );
        });
    }
}
