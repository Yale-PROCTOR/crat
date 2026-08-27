//! T1 closed-world origin/caller market probe (measurement-only).

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{IndexVec, bit_set::MixedBitSet};
use rustc_middle::mir::{
    Body, Local, Location, Operand, Place, Rvalue, Statement, StatementKind, TerminatorKind,
    visit::{MutatingUseContext, PlaceContext, Visitor},
};

use crate::analyses::borrow_ownership::{
    a5_overlap::WholeProgramAttestation,
    a5_producer::{ClosedWorldCallWorld, resolve_closed_world_call_world},
    crate_slots::CrateSlots,
    l2::SlotKey,
    origin_flow::OriginFlowResults,
    resolve::{ResolvedSlot, resolve_place},
    slots::SlotOwner,
    solver::{KindSolver, SlotRef},
    sources::collect_malloc_source_slots,
};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct LicP1Key {
    program: String,
    function: String,
    lhs: SlotKey,
    rhs: SlotKey,
}

impl LicP1Key {
    fn slot_text(slot: SlotKey) -> String {
        match slot.variant {
            0 => format!("field:{}", slot.slot),
            1 => format!("local:{}:{}", slot.owner, slot.slot),
            variant => format!("invalid:{variant}:{}:{}", slot.owner, slot.slot),
        }
    }

    fn diagnostic(&self) -> String {
        format!(
            "{}|{}|{}|{}",
            self.program,
            self.function,
            Self::slot_text(self.lhs),
            Self::slot_text(self.rhs)
        )
    }
}

#[derive(Clone, Debug)]
struct LicP1Target {
    key: LicP1Key,
}

fn parse_slot_key(text: &str) -> Result<SlotKey, String> {
    let parts = text.split(':').collect::<Vec<_>>();
    match parts.as_slice() {
        ["field", slot] => Ok(SlotKey {
            variant: 0,
            owner: 0,
            slot: slot
                .parse()
                .map_err(|_| format!("invalid field slot {text}"))?,
        }),
        ["local", owner, slot] => Ok(SlotKey {
            variant: 1,
            owner: owner
                .parse()
                .map_err(|_| format!("invalid local owner {text}"))?,
            slot: slot
                .parse()
                .map_err(|_| format!("invalid local slot {text}"))?,
        }),
        _ => Err(format!("invalid LIC-P1 slot key {text}")),
    }
}

fn parse_lic_p1_targets(text: &str, program: &str) -> Result<Vec<LicP1Target>, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("missing LIC-P1 header")?;
    let columns = header
        .split('\t')
        .enumerate()
        .map(|(index, name)| (name, index))
        .collect::<BTreeMap<_, _>>();
    let get = |fields: &[&str], name: &str| -> Result<String, String> {
        let index = columns
            .get(name)
            .ok_or_else(|| format!("missing LIC-P1 column {name}"))?;
        fields
            .get(*index)
            .map(|value| (*value).to_owned())
            .ok_or_else(|| format!("short LIC-P1 row at {name}"))
    };
    let mut keys = BTreeSet::new();
    let mut answer = Vec::new();
    for line in lines.filter(|line| !line.is_empty()) {
        let fields = line.split('\t').collect::<Vec<_>>();
        if get(&fields, "program")? != program
            || get(&fields, "bucket")? != "token-cannot-exist"
            || get(&fields, "subbucket")? != "unknown-origin"
        {
            continue;
        }
        let key = LicP1Key {
            program: program.to_owned(),
            function: get(&fields, "function")?,
            lhs: parse_slot_key(&get(&fields, "lhs")?)?,
            rhs: parse_slot_key(&get(&fields, "rhs")?)?,
        };
        if !keys.insert(key.clone()) {
            return Err(format!("duplicate LIC-P1 key {}", key.diagnostic()));
        }
        answer.push(LicP1Target { key });
    }
    answer.sort_by(|left, right| left.key.cmp(&right.key));
    Ok(answer)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EndpointDisposition {
    Unique,
    Indeterminate,
}

fn endpoint_disposition(matches: usize) -> EndpointDisposition {
    if matches == 1 {
        EndpointDisposition::Unique
    } else {
        EndpointDisposition::Indeterminate
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Inflow {
    Alloc,
    NonAlloc,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Verdict {
    Yes,
    No,
    Indeterminate,
}

fn join_inflows(inflows: &[Inflow]) -> Verdict {
    if inflows.is_empty() || inflows.iter().any(|inflow| *inflow == Inflow::Unknown) {
        Verdict::Indeterminate
    } else if inflows.iter().any(|inflow| *inflow == Inflow::NonAlloc) {
        Verdict::No
    } else {
        Verdict::Yes
    }
}

const TEMP_CHASE_LIMIT: usize = 8;

struct UniqueDef<'a>(&'a mut IndexVec<Local, Option<bool>>);

impl Visitor<'_> for UniqueDef<'_> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
        if let PlaceContext::MutatingUse(MutatingUseContext::Store) = context {
            self.visit_place(&Place::from(local), context, location);
        }
    }

    fn visit_place(&mut self, place: &Place<'_>, context: PlaceContext, _location: Location) {
        if place.as_local().is_some()
            && matches!(context, PlaceContext::MutatingUse(MutatingUseContext::Store))
        {
            self.0[place.local] = Some(self.0[place.local].is_none());
        }
    }
}

struct Mentioned<'a>(&'a mut IndexVec<Local, usize>);

impl Visitor<'_> for Mentioned<'_> {
    fn visit_local(&mut self, local: Local, _context: PlaceContext, _location: Location) {
        self.0[local] += 1;
    }

    fn visit_place(&mut self, place: &Place<'_>, _context: PlaceContext, _location: Location) {
        self.0[place.local] += 1;
    }

    fn visit_statement(&mut self, statement: &Statement<'_>, location: Location) {
        if matches!(
            statement.kind,
            StatementKind::StorageDead(..) | StatementKind::StorageLive(..)
        ) {
            return;
        }
        self.super_statement(statement, location);
    }
}

fn eliminable_temporaries(body: &Body<'_>) -> MixedBitSet<Local> {
    let mut unique = IndexVec::from_elem_n(None, body.local_decls.len());
    UniqueDef(&mut unique).visit_body(body);
    let mut mentioned = IndexVec::from_elem_n(0, body.local_decls.len());
    Mentioned(&mut mentioned).visit_body(body);
    let mut answer = MixedBitSet::new_empty(body.local_decls.len());
    for ((local, definition), count) in unique
        .into_iter_enumerated()
        .zip(mentioned.into_iter())
        .skip(body.arg_count + 1)
    {
        if definition == Some(true) && count == 2 {
            answer.insert(local);
        }
    }
    answer
}

fn copy_place(rvalue: &Rvalue<'_>) -> Option<Place<'_>> {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
        | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
        | Rvalue::CopyForDeref(place) => Some(*place),
        _ => None,
    }
}

fn chase_operand_temp<'tcx>(body: &Body<'tcx>, mut place: Place<'tcx>) -> Place<'tcx> {
    let eliminable = eliminable_temporaries(body);
    let mut definitions = FxHashMap::default();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let Some(local) = assign.0.as_local() else {
                continue;
            };
            if eliminable.contains(local)
                && let Some(source) = copy_place(&assign.1)
            {
                definitions.insert(local, source);
            }
        }
    }
    for _ in 0..TEMP_CHASE_LIMIT {
        if !place.projection.is_empty() {
            break;
        }
        let Some(&next) = definitions.get(&place.local) else {
            break;
        };
        if next == place {
            break;
        }
        place = next;
    }
    place
}

fn resolved_actual_slot(
    slots: &CrateSlots,
    caller: rustc_span::def_id::LocalDefId,
    body: &Body<'_>,
    operand: &Operand<'_>,
) -> Option<SlotRef> {
    let place = chase_operand_temp(body, operand.place()?);
    match resolve_place(slots, caller, body, place, 0, None)? {
        ResolvedSlot::Local(slot) => Some(SlotRef::Local(caller, slot)),
        ResolvedSlot::Field(slot) => Some(SlotRef::Field(slot)),
    }
}

#[derive(Clone, Debug)]
struct SlotEvidence {
    inflow: Inflow,
    may_set: BTreeSet<usize>,
    complete: bool,
    callers: BTreeSet<String>,
    terminals: BTreeSet<String>,
    reasons: BTreeSet<String>,
}

impl SlotEvidence {
    fn terminal(inflow: Inflow, terminal: String, reason: &str) -> Self {
        Self {
            inflow,
            may_set: BTreeSet::new(),
            complete: inflow != Inflow::Unknown,
            callers: BTreeSet::new(),
            terminals: BTreeSet::from([terminal]),
            reasons: BTreeSet::from([reason.to_owned()]),
        }
    }
}

struct SlotClassifier<'a, 'tcx> {
    program: &'a RustProgram<'tcx>,
    slots: &'a CrateSlots,
    flows: &'a OriginFlowResults,
    world: &'a ClosedWorldCallWorld,
    fresh: &'a FxHashSet<SlotRef>,
    cache: FxHashMap<SlotRef, SlotEvidence>,
}

impl<'a, 'tcx> SlotClassifier<'a, 'tcx> {
    fn classify(&mut self, slot: SlotRef) -> SlotEvidence {
        self.classify_inner(slot, &mut FxHashSet::default())
    }

    fn classify_inner(
        &mut self,
        slot: SlotRef,
        active: &mut FxHashSet<SlotRef>,
    ) -> SlotEvidence {
        if let Some(evidence) = self.cache.get(&slot) {
            return evidence.clone();
        }
        if !active.insert(slot) {
            return SlotEvidence::terminal(
                Inflow::Unknown,
                slot_text(slot),
                "caller-origin-cycle",
            );
        }
        let mut evidence = self.classify_uncached(slot, active);
        active.remove(&slot);
        if evidence.inflow == Inflow::Unknown {
            evidence.complete = false;
        }
        self.cache.insert(slot, evidence.clone());
        evidence
    }

    fn classify_uncached(
        &mut self,
        slot: SlotRef,
        active: &mut FxHashSet<SlotRef>,
    ) -> SlotEvidence {
        if self.fresh.contains(&slot) {
            return SlotEvidence::terminal(Inflow::Alloc, slot_text(slot), "allocator-source-slot");
        }
        let SlotRef::Local(function, slot_id) = slot else {
            return SlotEvidence::terminal(
                Inflow::Unknown,
                slot_text(slot),
                "field-origin-not-call-instantiable",
            );
        };
        let Some(universe) = self.slots.fn_local_slots.get(&function) else {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "missing-slot-universe");
        };
        let slot_data = universe.slot(slot_id);
        let SlotOwner::Local(local) = slot_data.owner else {
            return SlotEvidence::terminal(
                Inflow::Unknown,
                slot_text(slot),
                "nonlocal-slot-owner",
            );
        };
        if slot_data.depth != 0 {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "non-depth-zero-slot");
        }
        let body = self
            .program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let Some(flow) = self.flows.get(&function) else {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "missing-origin-flow");
        };
        let Some((may_set, complete)) = flow.body.depth0_origin_indices(
            &body,
            local,
            self.world.unknown_reachable.contains(&function),
        ) else {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "missing-origin-slot");
        };
        let Some((arguments, argument_complete)) =
            flow.body.depth0_argument_origins(&body, local)
        else {
            return SlotEvidence::terminal(Inflow::Unknown, slot_text(slot), "missing-argument-origin");
        };
        if self.is_fresh_alias(function, local) {
            return SlotEvidence {
                inflow: Inflow::Alloc,
                may_set,
                complete: true,
                callers: BTreeSet::new(),
                terminals: BTreeSet::from([format!("fresh-alias:{}", slot_text(slot))]),
                reasons: BTreeSet::from(["storage-alias-to-allocator-source".to_owned()]),
            };
        }
        let fresh_origins = self.fresh_origin_indices(function, &body);
        if !may_set.is_empty() && may_set.is_subset(&fresh_origins) {
            return SlotEvidence {
                inflow: Inflow::Alloc,
                may_set,
                complete: true,
                callers: BTreeSet::new(),
                terminals: BTreeSet::from([format!(
                    "origin-set-allocation:{}",
                    slot_text(slot)
                )]),
                reasons: BTreeSet::from(["origin-may-set-all-fresh".to_owned()]),
            };
        }
        if !complete || !argument_complete {
            let mut evidence = SlotEvidence::terminal(
                Inflow::Unknown,
                slot_text(slot),
                if self.world.unknown_reachable.contains(&function) {
                    "open-boundary-origin"
                } else {
                    "incomplete-origin-may-set"
                },
            );
            evidence.may_set = may_set;
            return evidence;
        }
        if arguments.is_empty() {
            let mut evidence = SlotEvidence::terminal(
                Inflow::NonAlloc,
                slot_text(slot),
                "complete-nonallocator-local-root",
            );
            evidence.may_set = may_set;
            return evidence;
        }

        let mut inflows = Vec::new();
        let mut combined = SlotEvidence {
            inflow: Inflow::Unknown,
            may_set,
            complete: true,
            callers: BTreeSet::new(),
            terminals: BTreeSet::new(),
            reasons: BTreeSet::new(),
        };
        for argument in arguments {
            if argument == 0 {
                inflows.push(Inflow::Unknown);
                combined.reasons.insert("return-place-as-argument".to_owned());
                continue;
            }
            let actuals = self.observed_actuals(function, argument - 1);
            if actuals.is_empty() {
                inflows.push(Inflow::Unknown);
                combined
                    .reasons
                    .insert(format!("no-observed-caller-for-arg{argument}"));
                continue;
            }
            for (caller, call, actual) in actuals {
                let caller_path = self.program.tcx.def_path_str(caller.to_def_id());
                let call_text = format!(
                    "{}:bb{}:arg{}=>{}",
                    caller_path, call.block, argument, slot_text_opt(actual)
                );
                combined.callers.insert(call_text);
                let Some(actual) = actual else {
                    inflows.push(Inflow::Unknown);
                    combined.reasons.insert("unresolved-caller-actual".to_owned());
                    continue;
                };
                let evidence = self.classify_inner(actual, active);
                inflows.push(evidence.inflow);
                combined.terminals.extend(evidence.terminals);
                combined.reasons.extend(evidence.reasons);
                combined.callers.extend(evidence.callers);
                combined.complete &= evidence.complete;
            }
        }
        combined.inflow = match join_inflows(&inflows) {
            Verdict::Yes => Inflow::Alloc,
            Verdict::No => Inflow::NonAlloc,
            Verdict::Indeterminate => Inflow::Unknown,
        };
        combined
    }

    fn is_fresh_alias(
        &self,
        function: rustc_span::def_id::LocalDefId,
        local: Local,
    ) -> bool {
        let Some(flow) = self.flows.get(&function) else {
            return false;
        };
        let Some(universe) = self.slots.fn_local_slots.get(&function) else {
            return false;
        };
        self.fresh.iter().copied().any(|slot| {
            let SlotRef::Local(owner, slot_id) = slot else {
                return false;
            };
            if owner != function {
                return false;
            }
            let slot_data = universe.slot(slot_id);
            matches!(slot_data.owner, SlotOwner::Local(fresh_local)
                if slot_data.depth == 0
                    && flow.body.depth0_storage_alias(local, fresh_local))
        })
    }

    fn fresh_origin_indices(
        &self,
        function: rustc_span::def_id::LocalDefId,
        body: &rustc_middle::mir::Body<'_>,
    ) -> BTreeSet<usize> {
        let Some(flow) = self.flows.get(&function) else {
            return BTreeSet::new();
        };
        let Some(universe) = self.slots.fn_local_slots.get(&function) else {
            return BTreeSet::new();
        };
        let mut answer = BTreeSet::new();
        for &slot in self.fresh {
            let SlotRef::Local(owner, slot_id) = slot else {
                continue;
            };
            if owner != function {
                continue;
            }
            let slot_data = universe.slot(slot_id);
            let SlotOwner::Local(local) = slot_data.owner else {
                continue;
            };
            if slot_data.depth != 0 {
                continue;
            }
            if let Some((origins, _)) = flow.body.depth0_origin_indices(body, local, false) {
                eprintln!(
                    "T1 fresh origin {} local {:?}: {:?}",
                    slot_text(slot),
                    local,
                    origins
                );
                answer.extend(origins);
            }
        }
        answer
    }

    fn observed_actuals(
        &self,
        target: rustc_span::def_id::LocalDefId,
        argument: usize,
    ) -> Vec<(
        rustc_span::def_id::LocalDefId,
        crate::analyses::borrow_ownership::l2::MirLocationKey,
        Option<SlotRef>,
    )> {
        let mut rows = Vec::new();
        for (&(caller, block), targets) in &self.world.resolved {
            if !targets.contains(&target) {
                continue;
            }
            let body = self
                .program
                .tcx
                .mir_drops_elaborated_and_const_checked(caller)
                .borrow();
            let args = match &body.basic_blocks[block].terminator().kind {
                TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => args,
                _ => continue,
            };
            let actual = args
                .get(argument)
                .and_then(|arg| resolved_actual_slot(self.slots, caller, &body, &arg.node));
            rows.push((
                caller,
                crate::analyses::borrow_ownership::l2::MirLocationKey::new(
                    block.as_u32(),
                    body.basic_blocks[block].statements.len(),
                ),
                actual,
            ));
        }
        rows.sort_by_key(|(caller, location, actual)| {
            (
                caller.local_def_index.as_u32(),
                *location,
                actual.map(SlotKey::of),
            )
        });
        rows
    }
}

fn slot_text(slot: SlotRef) -> String {
    match slot {
        SlotRef::Field(slot) => format!("field:{}", slot.index()),
        SlotRef::Local(function, slot) => {
            format!("local:{}:{}", function.local_def_index.as_u32(), slot.index())
        }
    }
}

fn slot_text_opt(slot: Option<SlotRef>) -> String {
    slot.map(slot_text).unwrap_or_else(|| "unresolved".to_owned())
}

#[cfg(test)]
fn fixture_inflow(code: &'static str, function_name: &str, local_name: &str) -> Inflow {
    let mut answer = None;
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = super::collect_program(tcx);
        let function = program
            .functions
            .iter()
            .copied()
            .find(|function| tcx.item_name(function.to_def_id()).as_str() == function_name)
            .expect("fixture function");
        let body = tcx.mir_drops_elaborated_and_const_checked(function).borrow();
        let local = body
            .var_debug_info
            .iter()
            .find_map(|info| {
                (info.name.as_str() == local_name).then(|| match info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place) => Some(place.local),
                    _ => None,
                })?
            })
            .expect("fixture local");
        let slots = CrateSlots::build(&program);
        let slot = slots
            .fn_local_slots
            .get(&function)
            .and_then(|universe| universe.slot_for_local_depth(local, 0))
            .map(|slot| SlotRef::Local(function, slot))
            .expect("fixture slot");
        let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
        let world = resolve_closed_world_call_world(
            &program,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        let fresh = collect_malloc_source_slots(tcx, &program.functions, &slots);
        eprintln!(
            "T1 fixture fresh: {:?}",
            fresh.iter().copied().map(slot_text).collect::<Vec<_>>()
        );
        let evidence = SlotClassifier {
                program: &program,
                slots: &slots,
                flows: origins.native_flows(),
                world: &world,
                fresh: &fresh,
                cache: FxHashMap::default(),
            }
            .classify(slot);
        eprintln!("T1 fixture evidence: {evidence:#?}");
        answer = Some(evidence.inflow);
    })
    .unwrap_or_else(|error| error.raise());
    answer.expect("compiler callback")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_keeps_only_unknown_origin_rows_and_exact_join_keys() {
        let input = "program\tfunction\tlhs\trhs\tstored_scope\tstored_families\tquery_status\t\
                     exact_labels\tbucket\tsubbucket\tclassification_source\tchecks\tprior_checks\t\
                     copy_lend_mode\tsmt_seed\tsat_seed\n\
                     p\tcrate::f\tlocal:1:2\tlocal:1:3\texhaustive\town-assume\tunsat\tlabel\t\
                     token-cannot-exist\tunknown-origin\ttargeted-resolve\t1\t0\tlend_arm\t0\t0\n\
                     p\tcrate::g\tlocal:2:2\tlocal:2:3\texhaustive\town-assume\tunsat\tlabel\t\
                     token-cannot-exist\tinvisible-allocation\ttargeted-resolve\t1\t0\tlend_arm\t0\t0\n";
        let rows = parse_lic_p1_targets(input, "p").expect("valid fixture");
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].key.diagnostic(), "p|crate::f|local:1:2|local:1:3");
    }

    #[test]
    fn duplicate_lic_p1_key_is_rejected() {
        let header = "program\tfunction\tlhs\trhs\tstored_scope\tstored_families\tquery_status\t\
                      exact_labels\tbucket\tsubbucket\tclassification_source\tchecks\tprior_checks\t\
                      copy_lend_mode\tsmt_seed\tsat_seed\n";
        let row = "p\tcrate::f\tlocal:1:2\tlocal:1:3\texhaustive\town-assume\tunsat\tlabel\t\
                   token-cannot-exist\tunknown-origin\ttargeted-resolve\t1\t0\tlend_arm\t0\t0\n";
        let error = parse_lic_p1_targets(&format!("{header}{row}{row}"), "p")
            .expect_err("duplicate must fail closed");
        assert!(error.contains("duplicate LIC-P1 key"), "{error}");
    }

    #[test]
    fn endpoint_resolution_is_unique_or_indeterminate() {
        assert_eq!(endpoint_disposition(0), EndpointDisposition::Indeterminate);
        assert_eq!(endpoint_disposition(1), EndpointDisposition::Unique);
        assert_eq!(endpoint_disposition(2), EndpointDisposition::Indeterminate);
    }

    #[test]
    fn all_observed_inflows_use_three_valued_fail_closed_join() {
        assert_eq!(join_inflows(&[Inflow::Alloc, Inflow::Alloc]), Verdict::Yes);
        assert_eq!(join_inflows(&[Inflow::Alloc, Inflow::NonAlloc]), Verdict::No);
        assert_eq!(join_inflows(&[Inflow::Alloc, Inflow::Unknown]), Verdict::Indeterminate);
        assert_eq!(join_inflows(&[]), Verdict::Indeterminate);
    }

    #[test]
    fn observed_private_caller_with_malloc_actual_is_alloc_rooted() {
        let code = r#"
            extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
            unsafe fn release(p: *mut i32) { free(p.cast()); }
            unsafe fn entry() { let p = malloc(4).cast::<i32>(); release(p); }
        "#;
        assert_eq!(fixture_inflow(code, "release", "p"), Inflow::Alloc);
    }

    #[test]
    fn observed_private_caller_with_stack_actual_is_not_alloc_rooted() {
        let code = r#"
            extern "C" { fn free(p: *mut core::ffi::c_void); }
            unsafe fn release(p: *mut i32) { free(p.cast()); }
            unsafe fn entry() { let mut cell = 0; release(&raw mut cell); }
        "#;
        assert_eq!(fixture_inflow(code, "release", "p"), Inflow::NonAlloc);
    }

    #[test]
    fn open_boundary_is_indeterminate_even_with_an_observed_alloc_caller() {
        let code = r#"
            extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
            pub unsafe fn release(p: *mut i32) { free(p.cast()); }
            unsafe fn entry() { let p = malloc(4).cast::<i32>(); release(p); }
        "#;
        assert_eq!(fixture_inflow(code, "release", "p"), Inflow::Unknown);
    }
}
