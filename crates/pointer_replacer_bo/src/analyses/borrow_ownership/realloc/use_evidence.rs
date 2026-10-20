//! Bounded source use evidence for R219. This is not ownership or field SSA.

use std::collections::{BTreeSet, VecDeque};

use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, CastKind, Local, Location, Operand, Place, RETURN_PLACE, Rvalue,
        START_BLOCK, StatementKind, TerminatorKind,
        visit::{PlaceContext, Visitor},
    },
    ty::{self, TyCtxt},
};

use super::{
    ReallocContinuation, ReallocResult, ReallocSize, ReallocUseWitness, ResultTransport,
    operand_local, requested_size,
};
use crate::{
    analyses::{
        borrow_ownership::export::{PlaceKey, ProjKey},
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

struct Places<'tcx>(Vec<Place<'tcx>>);

impl<'tcx> Visitor<'tcx> for Places<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, _: PlaceContext, _: Location) {
        self.0.push(*place);
    }
}

#[derive(Clone, PartialEq, Eq)]
struct State {
    aliases: BTreeSet<PlaceKey>,
    retired: bool,
    unresolved_alias: bool,
    /// Becomes false after a conditional path or an unproved call. Such paths
    /// can establish absence of use, but cannot establish a mandatory use.
    certain: bool,
}

impl State {
    fn merge(&mut self, other: &Self) -> bool {
        let before = self.clone();
        self.aliases.extend(other.aliases.iter().cloned());
        self.retired |= other.retired;
        self.unresolved_alias |= other.unresolved_alias;
        self.certain &= other.certain;
        *self != before
    }

    fn write(&mut self, destination: &PlaceKey, addressed: &BTreeSet<Local>) {
        if destination.proj.is_empty() {
            self.unresolved_alias |= self
                .aliases
                .iter()
                .any(|place| place.local == destination.local && !place.proj.is_empty());
            self.aliases
                .retain(|place| place.local != destination.local);
        } else {
            // Without field-memory SSA an intervening projected write may
            // alias any stored pointer. A new exact store is added afterward.
            self.unresolved_alias |= self
                .aliases
                .iter()
                .any(|place| !place.proj.is_empty() || addressed.contains(&place.local));
            self.aliases
                .retain(|place| place.proj.is_empty() && !addressed.contains(&place.local));
        }
    }
}

enum Evidence {
    Unobserved,
    Must(ReallocUseWitness),
    Unsupported,
}

fn deref_access<'tcx>(
    place: Place<'tcx>,
    state: &State,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<(PlaceKey, u64)> {
    let key = PlaceKey::from_place(place);
    let through_result = key.proj.iter().enumerate().any(|(index, projection)| {
        *projection == ProjKey::Deref
            && state.aliases.contains(&PlaceKey {
                local: key.local,
                proj: key.proj[..index].to_vec(),
            })
    });
    if !through_result {
        return None;
    }
    let env = ty::TypingEnv::post_analysis(tcx, body.source.def_id().expect_local());
    let bytes = tcx
        .layout_of(env.as_query_input(place.ty(body, tcx).ty))
        .map(|layout| layout.size.bytes())
        .unwrap_or(0);
    Some((key, bytes))
}

fn access_evidence(access: (PlaceKey, u64), state: &State, location: Location) -> Evidence {
    let (place, access_bytes) = access;
    if state.certain && !state.retired && access_bytes > 0 {
        Evidence::Must(ReallocUseWitness::DirectDeref {
            location,
            place,
            access_bytes,
        })
    } else {
        Evidence::Unsupported
    }
}

fn value_source(value: &Rvalue<'_>, state: &State) -> Option<PlaceKey> {
    let key = match value {
        Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
            PlaceKey::from_place(operand.place()?)
        }
        Rvalue::CopyForDeref(place) => PlaceKey::from_place(*place),
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
            let mut key = PlaceKey::from_place(*place);
            if key.proj.pop() != Some(ProjKey::Deref) {
                return None; // Address of pointer storage is not the pointer value.
            }
            key
        }
        _ => return None,
    };
    state.aliases.contains(&key).then_some(key)
}

fn exact_zero_offset(
    call: &crate::analyses::mir::MirFunctionCall<'_, '_>,
    tcx: TyCtxt<'_>,
) -> bool {
    matches!(&call.func, CallKind::RustLib(did)
        if tcx.crate_name(did.krate).as_str() == "core"
            && tcx.def_path_str(*did).contains("::ptr::")
            && matches!(tcx.item_name(*did).as_str(),
                "offset" | "wrapping_offset" | "add" | "sub" | "wrapping_add" | "wrapping_sub"))
        && call.args.len() == 2
        && requested_size(&call.args[1].node, tcx) == ReallocSize::Zero
}

/// Entry states monotonically accumulate may-alias places and lose certainty.
/// Each key is an actual MIR place (or its deref prefix), so cycles terminate
/// at a finite fixpoint. A conditional use never becomes a must-use at a join.
fn walk<'tcx>(
    program: &RustProgram<'tcx>,
    body: &Body<'tcx>,
    first: BasicBlock,
    seed: PlaceKey,
    forbidden: Option<BasicBlock>,
    local_calls: bool,
    transports: &mut Vec<ResultTransport>,
) -> Evidence {
    let tcx = program.tcx;
    let addressed = super::super::source_events::addressed_locals(body);
    let mut entries: Vec<Option<State>> = vec![None; body.basic_blocks.len()];
    entries[first.as_usize()] = Some(State {
        aliases: BTreeSet::from([seed]),
        retired: false,
        unresolved_alias: false,
        certain: true,
    });
    let mut pending = VecDeque::from([first]);
    let mut unresolved_alias = false;
    while let Some(block) = pending.pop_front() {
        if Some(block) == forbidden {
            return Evidence::Unsupported;
        }
        let mut state = entries[block.as_usize()]
            .clone()
            .expect("queued source state");
        let data = &body.basic_blocks[block];
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            match &statement.kind {
                StatementKind::Assign(box (destination, value)) => {
                    if let Some(access) = deref_access(*destination, &state, body, tcx) {
                        return access_evidence(access, &state, location);
                    }
                    let storage_address = matches!(value, Rvalue::Ref(..) | Rvalue::RawPtr(..));
                    let mut places = Places(Vec::new());
                    places.visit_rvalue(value, location);
                    if !storage_address {
                        for place in &places.0 {
                            if let Some(access) = deref_access(*place, &state, body, tcx) {
                                return access_evidence(access, &state, location);
                            }
                        }
                    }
                    let mut source = value_source(value, &state);
                    if let Rvalue::BinaryOp(BinOp::Offset, operands) = value
                        && requested_size(&operands.1, tcx) == ReallocSize::Zero
                        && let Some(place) = operands.0.place()
                        && state.aliases.contains(&PlaceKey::from_place(place))
                    {
                        source = Some(PlaceKey::from_place(place));
                    }
                    let mentions_value = places
                        .0
                        .iter()
                        .any(|place| state.aliases.contains(&PlaceKey::from_place(*place)));
                    if source.is_none() && mentions_value && !storage_address {
                        return Evidence::Unsupported; // Address observation/opaque control.
                    }
                    let destination = PlaceKey::from_place(*destination);
                    state.write(&destination, &addressed);
                    if let Some(source) = source {
                        if source.proj.is_empty() && destination.proj.is_empty() {
                            let transport = ResultTransport {
                                location,
                                source: source.local,
                                destination: destination.local,
                            };
                            if !transports.contains(&transport) {
                                transports.push(transport);
                            }
                        }
                        state.aliases.insert(destination);
                    }
                }
                StatementKind::StorageDead(local) | StatementKind::StorageLive(local) => {
                    state.aliases.retain(|place| place.local != *local);
                }
                StatementKind::Nop
                | StatementKind::ConstEvalCounter
                | StatementKind::Coverage(_)
                | StatementKind::FakeRead(_) => {}
                _ => return Evidence::Unsupported,
            }
        }
        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        let terminator = data.terminator();
        let successors: Vec<_> = match &terminator.kind {
            TerminatorKind::Return => {
                if state
                    .aliases
                    .iter()
                    .any(|place| place.local == RETURN_PLACE)
                {
                    return Evidence::Unsupported; // Observable result flow needs a caller contract.
                }
                Vec::new()
            }
            TerminatorKind::Goto { target } => vec![*target],
            TerminatorKind::Call {
                target: Some(target),
                ..
            } => {
                let call = terminator.as_call(tcx).expect("source call");
                for argument in call.args {
                    if let Some(place) = argument.node.place()
                        && let Some(access) = deref_access(place, &state, body, tcx)
                    {
                        return access_evidence(access, &state, location);
                    }
                }
                let derived: Vec<_> = call
                    .args
                    .iter()
                    .enumerate()
                    .filter_map(|(index, argument)| {
                        let place = PlaceKey::from_place(argument.node.place()?);
                        state.aliases.contains(&place).then_some((index, place))
                    })
                    .collect();
                let destination = PlaceKey::from_place(call.destination);
                if exact_zero_offset(&call, tcx) && derived.iter().any(|(index, _)| *index == 0) {
                    let source = derived
                        .iter()
                        .find(|(index, _)| *index == 0)
                        .unwrap()
                        .1
                        .clone();
                    state.write(&destination, &addressed);
                    if source.proj.is_empty() && destination.proj.is_empty() {
                        let transport = ResultTransport {
                            location,
                            source: source.local,
                            destination: destination.local,
                        };
                        if !transports.contains(&transport) {
                            transports.push(transport);
                        }
                    }
                    state.aliases.insert(destination);
                } else if matches!(&call.func, CallKind::LibC(name) if name.as_str() == "free") {
                    // free(NULL) is valid. Retirement never proves a usable
                    // result; a subsequent use after free cannot supply P0.
                    if !derived.is_empty() {
                        state.retired = true;
                    }
                    state.write(&destination, &addressed);
                } else if !derived.is_empty() {
                    if local_calls
                        && state.certain
                        && !state.retired
                        && let CallKind::FreeStanding(callee) = call.func
                        && program.functions.contains(&callee)
                    {
                        let callee_body =
                            tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
                        for (argument, _) in derived {
                            if argument >= callee_body.arg_count {
                                continue;
                            }
                            let seed = PlaceKey {
                                local: Local::from_usize(argument + 1),
                                proj: Vec::new(),
                            };
                            let mut unused = Vec::new();
                            if let Evidence::Must(ReallocUseWitness::DirectDeref {
                                location: callee_deref,
                                access_bytes,
                                ..
                            }) = walk(
                                program,
                                &callee_body,
                                START_BLOCK,
                                seed,
                                None,
                                false,
                                &mut unused,
                            ) {
                                return Evidence::Must(ReallocUseWitness::LocalCall {
                                    location,
                                    callee: tcx.def_path_str(callee.to_def_id()),
                                    argument,
                                    callee_deref,
                                    access_bytes,
                                });
                            }
                        }
                    }
                    return Evidence::Unsupported;
                } else {
                    // An unrelated opaque call may diverge or mutate stored
                    // pointer cells. It cannot turn a later use into a must-use.
                    state.certain = false;
                    state.unresolved_alias |= state
                        .aliases
                        .iter()
                        .any(|place| !place.proj.is_empty() || addressed.contains(&place.local));
                    state
                        .aliases
                        .retain(|place| place.proj.is_empty() && !addressed.contains(&place.local));
                    state.write(&destination, &addressed);
                }
                vec![*target]
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                if let Some(place) = discr.place() {
                    if let Some(access) = deref_access(place, &state, body, tcx) {
                        return access_evidence(access, &state, location);
                    }
                    if state.aliases.contains(&PlaceKey::from_place(place)) {
                        return Evidence::Unsupported;
                    }
                }
                state.certain = false;
                terminator.successors().collect()
            }
            TerminatorKind::Assert { cond, target, .. } => {
                if let Some(place) = cond.place()
                    && let Some(access) = deref_access(place, &state, body, tcx)
                {
                    return access_evidence(access, &state, location);
                }
                state.certain = false;
                vec![*target]
            }
            _ => return Evidence::Unsupported,
        };
        unresolved_alias |= state.unresolved_alias;
        for successor in successors {
            let changed = match &mut entries[successor.as_usize()] {
                Some(entry) => entry.merge(&state),
                entry @ None => {
                    *entry = Some(state.clone());
                    true
                }
            };
            if changed {
                pending.push_back(successor);
            }
        }
    }
    if unresolved_alias {
        Evidence::Unsupported
    } else {
        Evidence::Unobserved
    }
}

pub(super) fn continuation<'tcx>(
    program: &RustProgram<'tcx>,
    body: &Body<'tcx>,
    call: BasicBlock,
    normal: BasicBlock,
    old: Option<Place<'tcx>>,
    result: Place<'tcx>,
) -> ReallocResult {
    let mut transports = Vec::new();
    let evidence = walk(
        program,
        body,
        normal,
        PlaceKey::from_place(result),
        Some(call),
        true,
        &mut transports,
    );
    transports.sort_by_key(|transport| {
        (
            transport.location.block.as_u32(),
            transport.location.statement_index,
            transport.source.as_u32(),
            transport.destination.as_u32(),
        )
    });
    let mut continuation = ReallocContinuation {
        old: old.and_then(|place| place.as_local()),
        old_place: old.map(PlaceKey::from_place),
        result: result.as_local(),
        result_place: PlaceKey::from_place(result),
        normal,
        transports,
        witness: None,
    };
    match evidence {
        Evidence::Must(witness) => {
            continuation.witness = Some(witness);
            ReallocResult::SuccessImplied(continuation)
        }
        Evidence::Unobserved => ReallocResult::Unobserved(continuation),
        Evidence::Unsupported => ReallocResult::FallbackBothOutcomes(continuation),
    }
}

/// Follow only a single stable scalar value, not arithmetic or mutable state.
fn scalar_root(body: &Body<'_>, mut local: Local, addressed: &BTreeSet<Local>) -> Option<Local> {
    let mut visited = BTreeSet::new();
    loop {
        // Direct assignment counts cannot establish stability when the value
        // or one of its transport cells can be written through an alias.
        if !visited.insert(local) || addressed.contains(&local) {
            return None;
        }
        let mut count = 0;
        let mut copied = None;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                if let StatementKind::Assign(box (destination, value)) = &statement.kind
                    && destination.local == local
                {
                    count += 1;
                    if destination.projection.is_empty()
                        && let Rvalue::Use(operand) = value
                    {
                        copied = operand_local(operand);
                    }
                }
            }
            if matches!(&data.terminator().kind, TerminatorKind::Call { destination, .. } if destination.local == local)
            {
                count += 1;
            }
        }
        if count > 1 || (local.as_usize() <= body.arg_count && count != 0) {
            return None;
        }
        if count == 0 {
            return (local.as_usize() <= body.arg_count).then_some(local);
        }
        if let Some(source) = copied {
            local = source;
        } else {
            return Some(local);
        }
    }
}

fn reachable_without_edge(
    body: &Body<'_>,
    target: BasicBlock,
    skipped: (BasicBlock, BasicBlock),
) -> bool {
    let mut pending = vec![START_BLOCK];
    let mut visited = BTreeSet::new();
    while let Some(block) = pending.pop() {
        if block == target {
            return true;
        }
        if visited.insert(block) {
            pending.extend(
                body.basic_blocks[block]
                    .terminator()
                    .successors()
                    .filter(|successor| (block, *successor) != skipped),
            );
        }
    }
    false
}

pub(super) fn nonzero_guard(
    body: &Body<'_>,
    call: BasicBlock,
    operand: &Operand<'_>,
    tcx: TyCtxt<'_>,
) -> Option<Location> {
    if !reachable_without_edge(body, call, (call, call)) {
        return None;
    }
    let addressed = super::super::source_events::addressed_locals(body);
    let requested = scalar_root(body, operand_local(operand)?, &addressed)?;
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::SwitchInt { discr, targets } = &data.terminator().kind else {
            continue;
        };
        let Some(predicate) = operand_local(discr) else { continue };
        if addressed.contains(&predicate) {
            continue;
        }
        let mut comparison = None;
        let mut definitions = 0;
        for predecessor in body.basic_blocks.iter() {
            for statement in &predecessor.statements {
                let StatementKind::Assign(box (destination, value)) = &statement.kind else {
                    continue;
                };
                if destination.as_local() != Some(predicate) {
                    continue;
                }
                definitions += 1;
                if let Rvalue::BinaryOp(operator @ (BinOp::Eq | BinOp::Ne), operands) = value {
                    let same_value = |value: &Operand<'_>| {
                        operand_local(value).and_then(|local| scalar_root(body, local, &addressed))
                            == Some(requested)
                    };
                    if (same_value(&operands.0)
                        && requested_size(&operands.1, tcx) == ReallocSize::Zero)
                        || (same_value(&operands.1)
                            && requested_size(&operands.0, tcx) == ReallocSize::Zero)
                    {
                        comparison = Some(*operator == BinOp::Ne);
                    }
                }
            }
            if matches!(&predecessor.terminator().kind,
                TerminatorKind::Call { destination, .. } if destination.as_local() == Some(predicate))
            {
                definitions += 1;
            }
        }
        if definitions != 1 {
            continue;
        }
        let Some(nonzero_true) = comparison else { continue };
        let selected = targets
            .iter()
            .find_map(|(value, target)| (value == u128::from(nonzero_true)).then_some(target))
            .unwrap_or_else(|| targets.otherwise());
        let zero = targets
            .iter()
            .find_map(|(value, target)| (value == u128::from(!nonzero_true)).then_some(target))
            .unwrap_or_else(|| targets.otherwise());
        if selected == zero {
            continue;
        }
        if !reachable_without_edge(body, call, (block, selected)) {
            return Some(Location {
                block,
                statement_index: data.statements.len(),
            });
        }
    }
    None
}
