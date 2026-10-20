//! K18′, callee side: a descendant-free callee position.
//!
//! The type-backed child walk assumes a contract-less callee MAY hand back a
//! descendant of the argument and classifies what the caller then does with
//! the call's result; a callee returning no pointer local leaves it `Unknown`,
//! and one returning a FRESH pointer the caller later frees reads as `Writes`.
//! Both fire the shared-source hold `write-through-shared-view`. This module
//! answers the premise on the callee's own body: the argument's alias set has
//! a `NoRetain` certificate (the accepted retention instrument, transitive
//! through local callees) AND the body forms no non-transparent derivation of
//! that alias set (no address-of / raw address of a place under it, no
//! `Offset`, no aggregate capture, no cast to a non-pointer), returns none of
//! it, stores none of it through a projection, and every local callee that
//! receives an alias is descendant-free at that position in turn; a libc call
//! whose contract row says it returns an alias of the argument extends the
//! alias set with its result. No descendant then exists to hand back, and the
//! child access is `Unused` — the caller's use of a fresh result is its own
//! business.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{BinOp, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};

use super::decision::{
    raw_boundary::{RetentionVerdict, raw_target_type, symbol_key},
    raw_boundary_contracts::classify_contract,
    returned_child::{ChildAccess, ReturnedChildEvidence},
};
use crate::utils::rustc::RustProgram;

pub(crate) const PROVENANCE: &str = "k18-callee-descendant-free";

/// How a `core` raw-pointer method treats the pointer it receives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CorePointerCall {
    /// Takes the pointer by value and hands nothing back (`is_null`).
    NoRetain,
    /// Hands back the SAME allocation at another offset or spelling
    /// (`offset`, `add`, `sub`, `cast`, `cast_mut`, `cast_const`): the
    /// result is a transparent alias of the receiver, so the ordinary sinks
    /// decide what becomes of it. `wrapping_*` is deliberately left unknown:
    /// wave-5c's W-C2 control (`counted_extent_tests`) pins it as an open
    /// boundary, and moving that expectation is that lane's call.
    AliasResult,
}

/// Classify a `Rust`-ABI callee; `None` for anything the table does not
/// know, which stays an unknown call for the retention collector and refuses
/// the descendant-free scan.
pub(crate) fn core_pointer_call(tcx: TyCtxt<'_>, callee: DefId) -> Option<CorePointerCall> {
    if tcx.crate_name(callee.krate).as_str() != "core" {
        return None;
    }
    match tcx.item_name(callee).as_str() {
        // `offset_from` yields a COUNT, not a pointer: like `is_null` it reads
        // the receiver and retains nothing (lodepng `alloc_string::in_0#1`,
        // report 018 claim 3 — relay 018 asked for the one line).
        "is_null" | "offset_from" | "byte_offset_from" => Some(CorePointerCall::NoRetain),
        "offset" | "add" | "sub" | "cast" | "cast_mut" | "cast_const" => {
            Some(CorePointerCall::AliasResult)
        }
        _ => None,
    }
}

/// Whether `local` reaches the function's return place through transparent
/// copies and pointer casts. A subject's own rebind that is RETURNED
/// (`let q = p.offset(1); q`, wave-6s's re-ratified g18 form) keeps the
/// pre-hook reading — an open call, retention unknown — rather than a
/// positive retention of the parameter (main 036 / relay wave-6r/010).
pub(crate) fn result_returned(body: &Body<'_>, local: Local) -> bool {
    // Composition (relay wave-6v2/014): a result written STRAIGHT into the
    // return place (`fn dup(q) -> *mut T { q.cast_mut() }`) is returned with no
    // assignment to follow, so the scan must answer on the seed itself.
    if local == rustc_middle::mir::RETURN_PLACE {
        return true;
    }
    let mut aliases = vec![local];
    let mut changed = true;
    while changed {
        changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let (lhs, rhs) = (&assignment.0, &assignment.1);
                let source = match rhs {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand_local(operand),
                    _ => None,
                };
                let Some(source) = source.filter(|source| aliases.contains(source)) else {
                    continue;
                };
                if lhs.as_local() == Some(rustc_middle::mir::RETURN_PLACE) {
                    return true;
                }
                if let Some(destination) = lhs.as_local()
                    && !aliases.contains(&destination)
                {
                    aliases.push(destination);
                    changed = true;
                }
            }
        }
    }
    false
}

/// The collector's arm for a `Rust`-ABI callee: a known no-retain step when
/// the call is a classified core pointer method whose alias result (if any)
/// is not the function's own returned rebind.
pub(crate) fn core_pointer_known_no_retain<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    data: &rustc_middle::mir::BasicBlockData<'tcx>,
    callee: DefId,
) -> bool {
    match core_pointer_call(tcx, callee) {
        None => false,
        Some(CorePointerCall::NoRetain) => true,
        Some(CorePointerCall::AliasResult) => {
            let TerminatorKind::Call { destination, .. } = &data.terminator().kind else {
                return false;
            };
            destination
                .as_local()
                .is_some_and(|result| !result_returned(body, result))
        }
    }
}

fn pointer(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(..) | TyKind::Ref(..))
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    operand.place().and_then(|place| place.as_local())
}

fn resolved(operand: &Operand<'_>) -> Option<DefId> {
    let constant = operand.constant()?;
    let TyKind::FnDef(callee, _) = *constant.ty().kind() else { return None };
    Some(callee)
}

/// Whether `parameter` of `function` is descendant-free. `visited` breaks
/// recursion through local callees; a cycle is refused (conservative).
fn descendant_free(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    function: LocalDefId,
    parameter: Local,
    visited: &mut FxHashSet<(LocalDefId, Local)>,
) -> bool {
    refusal(tcx, functions, function, parameter, visited).is_none()
}

/// The scan's verdict with its REASON: `None` is descendant-free, `Some(r)`
/// names the conjunct that refused (`r` is a short kebab tag, a recursive
/// refusal prefixed by the callee position that carried it). The reason is
/// what the child-access receipt reports per site.
fn refusal(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    function: LocalDefId,
    parameter: Local,
    visited: &mut FxHashSet<(LocalDefId, Local)>,
) -> Option<String> {
    // A position already on the walk is assumed free: every hand-out is a
    // concrete statement in some body on the cycle, and every body on the
    // cycle is scanned (greatest fixpoint). Re-visiting a SIBLING call of the
    // same position must not refuse it either — brotli's `StoreH35` calls
    // `StoreH3` twice with the same argument.
    if !visited.insert((function, parameter)) {
        return None;
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let body: &Body<'_> = &body;
    let (aliases, derived) = alias_closure_parts(tcx, functions, body, vec![parameter]);
    scan(tcx, functions, body, &aliases, &derived, None, visited)
}

/// Transparent alias closure of `seeds`: copies, pointer casts, the results
/// of alias-result core calls, and of libc calls whose contract row returns
/// an alias of an alias.
fn alias_closure<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    body: &Body<'tcx>,
    aliases: Vec<Local>,
) -> Vec<Local> {
    alias_closure_parts(tcx, functions, body, aliases).0
}

/// The closure split into (every alias, the ADDRESS-DERIVED subset). The
/// retention walk of this frame does not track an address taken under a
/// pointer, so a derived alias carries no row evidence: the scan must prove
/// its uses itself and may not hand one to a callee it cannot read.
fn alias_closure_parts<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    body: &Body<'tcx>,
    mut aliases: Vec<Local>,
) -> (Vec<Local>, Vec<Local>) {
    let mut derived = Vec::<Local>::new();
    let mut changed = true;
    while changed {
        changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let (lhs, rhs) = (&assignment.0, &assignment.1);
                let source = match rhs {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => operand_local(operand),
                    _ => None,
                };
                if let Some(source) = source
                    && aliases.contains(&source)
                    && let Some(destination) = lhs.as_local()
                    && pointer(body.local_decls[destination].ty)
                    && !aliases.contains(&destination)
                {
                    aliases.push(destination);
                    if derived.contains(&source) {
                        derived.push(destination);
                    }
                    changed = true;
                }
                // An address taken UNDER an alias is a pointer into the same
                // pointee (brotli's `HashBytesH*(&*data.offset(ix))`): it
                // joins the closure, so the scan proves its uses too. The
                // address OF the alias slot (no `Deref`) does not.
                if let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rhs
                    && aliases.contains(&place.local)
                    && matches!(
                        place.projection.first(),
                        Some(rustc_middle::mir::PlaceElem::Deref)
                    )
                    && let Some(destination) = lhs.as_local()
                    && destination != rustc_middle::mir::RETURN_PLACE
                    && pointer(body.local_decls[destination].ty)
                    && !aliases.contains(&destination)
                {
                    aliases.push(destination);
                    derived.push(destination);
                    changed = true;
                }
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &data.terminator().kind
                && let Some(callee) = resolved(func)
                && callee
                    .as_local()
                    .is_none_or(|local| !functions.contains(&local))
                && let Some(result) = destination.as_local()
                && pointer(body.local_decls[result].ty)
                && !aliases.contains(&result)
            {
                if core_pointer_call(tcx, callee) == Some(CorePointerCall::AliasResult)
                    && let Some(receiver) = args
                        .first()
                        .and_then(|argument| operand_local(&argument.node))
                        .filter(|receiver| aliases.contains(receiver))
                {
                    aliases.push(result);
                    if derived.contains(&receiver) {
                        derived.push(result);
                    }
                    changed = true;
                    continue;
                }
                let key = symbol_key(tcx, callee, functions);
                let returns_alias = args.iter().enumerate().any(|(index, argument)| {
                    operand_local(&argument.node).is_some_and(|local| aliases.contains(&local))
                        && raw_target_type(tcx, argument.node.ty(body, tcx)).is_some_and(|target| {
                            classify_contract(&key, index, &target)
                                .is_ok_and(|contract| contract.returns_alias_of == Some(index))
                        })
                });
                if returns_alias {
                    aliases.push(result);
                    changed = true;
                }
            }
        }
    }
    (aliases, derived)
}

/// The body scan over an alias set: no alias may be handed out (stored
/// anywhere but a plain local, returned, aggregated, address-taken, offset by
/// a binary op, cast to a non-pointer, passed to an open callee) and every
/// local callee receiving one must be descendant-free at that position.
/// `output` names a parameter whose pointee is the CERTIFIED output storage
/// (wave-6v2's frame-confined certificate): a store of an alias through it
/// is that certificate's own sink, not a hand-out of this scan.
fn scan<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    body: &Body<'tcx>,
    aliases: &[Local],
    derived: &[Local],
    output: Option<Local>,
    visited: &mut FxHashSet<(LocalDefId, Local)>,
) -> Option<String> {
    let outputs = output.map(|output| alias_closure(tcx, functions, body, vec![output]));
    let is_alias =
        |operand: &Operand<'_>| operand_local(operand).is_some_and(|l| aliases.contains(&l));
    let hands_out = |place: &rustc_middle::mir::Place<'_>| {
        if let Some(outputs) = &outputs
            && let Some((rustc_middle::mir::PlaceElem::Deref, rest)) =
                place.projection.split_first()
            && rest
                .iter()
                .all(|elem| matches!(elem, rustc_middle::mir::PlaceElem::Field(..)))
            && outputs.contains(&place.local)
        {
            return false;
        }
        place
            .as_local()
            .is_none_or(|local| local == rustc_middle::mir::RETURN_PLACE)
    };
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (lhs, rhs) = (&assignment.0, &assignment.1);
            let derived = match rhs {
                // An address taken UNDER an alias (`&*p`, `&raw mut (*p).f`)
                // is itself a pointer into the same pointee: free while the
                // closure tracks it and this scan proves its every use
                // read-through (it is in `aliases`), refused when it lands
                // anywhere the closure does not track — a projection, the
                // return place, or a non-pointer destination. The address OF
                // the alias slot (`&p`, no `Deref`) stays refused.
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => aliases
                    .contains(&place.local)
                    .then_some("address-of-alias")
                    .filter(|_| !lhs.as_local().is_some_and(|dest| aliases.contains(&dest))),
                Rvalue::BinaryOp(BinOp::Offset, operands) => {
                    is_alias(&operands.0).then_some("offset-binop")
                }
                Rvalue::Aggregate(_, operands) => {
                    operands.iter().any(is_alias).then_some("aggregate")
                }
                // A copy or pointer cast of an alias stored through any
                // projection, or into the return place, hands it out; a cast
                // to a non-pointer is an image the scan cannot follow.
                Rvalue::Cast(_, operand, ty) => is_alias(operand)
                    .then(|| {
                        if pointer(*ty) {
                            "cast-hands-out"
                        } else {
                            "non-pointer-cast"
                        }
                    })
                    .filter(|_| !pointer(*ty) || hands_out(lhs)),
                Rvalue::Use(operand) => {
                    (is_alias(operand) && hands_out(lhs)).then_some("use-hands-out")
                }
                _ => None,
            };
            if let Some(reason) = derived {
                return Some(reason.to_owned());
            }
        }
        match &data.terminator().kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                let Some(callee) = resolved(func) else {
                    if args.iter().any(|argument| is_alias(&argument.node)) {
                        return Some("unresolved-callee".to_owned());
                    }
                    continue;
                };
                if matches!(data.terminator().kind, TerminatorKind::TailCall { .. })
                    && args.iter().any(|argument| is_alias(&argument.node))
                {
                    return Some("tail-call".to_owned());
                }
                // An ADDRESS-DERIVED alias carries no retention row (this
                // frame's walk does not track `&*p`), so only a local callee
                // this scan reads, or a classified core call, may receive one.
                if callee
                    .as_local()
                    .is_none_or(|local| !functions.contains(&local))
                    && core_pointer_call(tcx, callee).is_none()
                    && args.iter().any(|argument| {
                        operand_local(&argument.node).is_some_and(|l| derived.contains(&l))
                    })
                {
                    return Some(format!(
                        "derived-address-into-open-callee:{}",
                        tcx.item_name(callee).as_str()
                    ));
                }
                if let Some(local) = callee.as_local().filter(|local| functions.contains(local)) {
                    for (index, argument) in args.iter().enumerate() {
                        if is_alias(&argument.node)
                            && let Some(inner) = refusal(
                                tcx,
                                functions,
                                local,
                                Local::from_usize(index + 1),
                                visited,
                            )
                        {
                            return Some(format!(
                                "{}@{index}:{inner}",
                                tcx.item_name(local.to_def_id()).as_str()
                            ));
                        }
                    }
                }
                // Foreign callees: the retention certificate already refuses
                // an unknown or retaining contract; a known no-retain row that
                // returns an alias was folded into the alias set above — unless
                // its result lands somewhere other than a plain local, which
                // hands the alias out directly. A `Rust`-ABI method on an
                // alias is outside the contract table: only `is_null` is known.
                if callee
                    .as_local()
                    .is_none_or(|local| !functions.contains(&local))
                    && !symbol_key(tcx, callee, functions).abi.starts_with('C')
                    && args.iter().any(|argument| is_alias(&argument.node))
                    && core_pointer_call(tcx, callee).is_none()
                {
                    return Some(format!(
                        "non-c-abi-callee:{}",
                        tcx.item_name(callee).as_str()
                    ));
                }
                // An alias-result core call whose result lands outside a plain
                // local (a static, a field, the return place) hands the alias
                // out directly.
                if core_pointer_call(tcx, callee) == Some(CorePointerCall::AliasResult)
                    && args
                        .first()
                        .is_some_and(|argument| is_alias(&argument.node))
                    && let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                    && hands_out(destination)
                {
                    return Some("alias-result-outside-a-local".to_owned());
                }
                if callee
                    .as_local()
                    .is_none_or(|local| !functions.contains(&local))
                    && let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                    && destination
                        .as_local()
                        .is_none_or(|l| l == rustc_middle::mir::RETURN_PLACE)
                {
                    let key = symbol_key(tcx, callee, functions);
                    let returns_alias = args.iter().enumerate().any(|(index, argument)| {
                        is_alias(&argument.node)
                            && raw_target_type(tcx, argument.node.ty(body, tcx)).is_some_and(
                                |target| {
                                    classify_contract(&key, index, &target).is_ok_and(|contract| {
                                        contract.returns_alias_of == Some(index)
                                    })
                                },
                            )
                    });
                    if returns_alias {
                        return Some("returned-alias-outside-a-local".to_owned());
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// The body scan alone (no retention row): the parameter at `index` is only
/// read through in this function and every local callee it reaches.
pub(crate) fn position_is_descendant_free(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    function: LocalDefId,
    index: usize,
) -> bool {
    descendant_free(
        tcx,
        functions,
        function,
        Local::from_usize(index + 1),
        &mut FxHashSet::default(),
    )
}

/// The scan's refusal reason for a position, for the receipt and the
/// witnesses: `None` where `position_is_descendant_free` is true.
pub(crate) fn position_refusal(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    function: LocalDefId,
    index: usize,
) -> Option<String> {
    refusal(
        tcx,
        functions,
        function,
        Local::from_usize(index + 1),
        &mut FxHashSet::default(),
    )
}

/// The scan for a callee position whose stores through the parameter at
/// `output_index` are the certified output-storage sinks (relay wave-6r/013
/// §2, wave-6v2's `frame_confined`): every other use is read-through only.
pub(crate) fn position_is_descendant_free_modulo_output(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    function: LocalDefId,
    index: usize,
    output_index: usize,
) -> bool {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let body: &Body<'_> = &body;
    let parameter = Local::from_usize(index + 1);
    let (aliases, derived) = alias_closure_parts(tcx, functions, body, vec![parameter]);
    let mut visited = FxHashSet::from_iter([(function, parameter)]);
    scan(
        tcx,
        functions,
        body,
        &aliases,
        &derived,
        Some(Local::from_usize(output_index + 1)),
        &mut visited,
    )
    .is_none()
}

/// The reader side of the same certificate: every pointer LOADED from
/// `field` through the parameter at `index` (`(*p).field`, `p` or any of
/// its transparent aliases) is read through only in this function and every
/// local callee it reaches — never stored, returned or handed to an open
/// callee.
pub(crate) fn loaded_field_is_descendant_free(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    function: LocalDefId,
    index: usize,
    field: rustc_abi::FieldIdx,
) -> bool {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let body: &Body<'_> = &body;
    let bases = alias_closure(tcx, functions, body, vec![Local::from_usize(index + 1)]);
    let mut loaded = Vec::new();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (lhs, rhs) = (&assignment.0, &assignment.1);
            if let Rvalue::Use(operand) = rhs
                && let Some(place) = operand.place()
                && bases.contains(&place.local)
                && let [
                    rustc_middle::mir::PlaceElem::Deref,
                    rustc_middle::mir::PlaceElem::Field(f, _),
                ] = place.projection.as_slice()
                && *f == field
            {
                // A load straight into the return place or through another
                // pointer hands the loaded pointer out before any local holds it.
                let Some(destination) = lhs
                    .as_local()
                    .filter(|local| *local != rustc_middle::mir::RETURN_PLACE)
                else {
                    return false;
                };
                if pointer(body.local_decls[destination].ty) && !loaded.contains(&destination) {
                    loaded.push(destination);
                }
            }
        }
    }
    let (aliases, derived) = alias_closure_parts(tcx, functions, body, loaded);
    scan(
        tcx,
        functions,
        body,
        &aliases,
        &derived,
        None,
        &mut FxHashSet::default(),
    )
    .is_none()
}

/// Every (caller, callee, argument) position whose Return-only retention is
/// SETTLED at every call of that callee in that caller: the returned alias is
/// discarded (no use at all), or consumed where it is produced. The seam
/// consults the callee ROW, which says `retains` for the whole kazmath family
/// (`kmVec3Normalize(pOut, pOut)` returns its own out-parameter), so a caller
/// that never keeps the alias was dropped `seam-positive-retention` anyway
/// (wave-5d 029's root table: 4 of heman's 10 roots, 3 of binn's 10).
/// All-sites, so one unsettled call in the caller withholds the position.
pub(crate) fn settled_returned_aliases(
    program: &RustProgram<'_>,
    rows: &FxHashMap<(LocalDefId, usize), RetentionVerdict>,
) -> FxHashSet<(LocalDefId, LocalDefId, usize)> {
    use super::decision::raw_boundary::RetentionEventKind;
    let tcx: TyCtxt<'_> = program.tcx;
    let return_only = |callee: LocalDefId, index: usize| {
        matches!(
            rows.get(&(callee, index)),
            Some(RetentionVerdict::Retains { sink, path })
                if sink.kind == RetentionEventKind::Return
                    && path.iter().all(|step| step.kind == RetentionEventKind::Return)
        )
    };
    let mut settled = FxHashSet::default();
    let mut unsettled = FxHashSet::default();
    for &caller in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let body: &Body<'_> = &body;
        for data in body.basic_blocks.iter() {
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &data.terminator().kind
            else {
                continue;
            };
            let Some(callee) = resolved(func)
                .and_then(|callee| callee.as_local())
                .filter(|callee| program.functions.contains(callee))
            else {
                continue;
            };
            let ok = destination.as_local().is_some_and(|result| {
                result_discarded(body, result)
                    || result_consumed_in_place(tcx, &program.functions, body, result)
            });
            for index in 0..args.len() {
                if !return_only(callee, index) {
                    continue;
                }
                if ok {
                    settled.insert((caller, callee, index));
                } else {
                    unsettled.insert((caller, callee, index));
                }
            }
        }
    }
    settled.retain(|position| !unsettled.contains(position));
    settled
}

/// The result of the call is never read at all (the statement form
/// `kmVec3Normalize(pOut, pOut);`): no alias of it survives the call.
fn result_discarded(body: &Body<'_>, result: Local) -> bool {
    if !pointer(body.local_decls[result].ty) {
        return true;
    }
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let used = match &statement.kind {
                StatementKind::Assign(assignment) => {
                    assignment.0.local == result || rvalue_mentions(&assignment.1, result)
                }
                _ => false,
            };
            if used {
                return false;
            }
        }
        match &data.terminator().kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                if args.iter().any(|argument| {
                    argument
                        .node
                        .place()
                        .is_some_and(|place| place.local == result)
                }) || func.place().is_some_and(|place| place.local == result)
                {
                    return false;
                }
            }
            TerminatorKind::Return => {}
            terminator => {
                let mut mentioned = false;
                if let TerminatorKind::SwitchInt { discr, .. } = terminator
                    && discr.place().is_some_and(|place| place.local == result)
                {
                    mentioned = true;
                }
                if mentioned {
                    return false;
                }
            }
        }
    }
    true
}

fn rvalue_mentions(rvalue: &Rvalue<'_>, local: Local) -> bool {
    let mentions =
        |operand: &Operand<'_>| operand.place().is_some_and(|place| place.local == local);
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Cast(_, operand, _)
        | Rvalue::Repeat(operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::ShallowInitBox(operand, _) => mentions(operand),
        Rvalue::BinaryOp(_, operands) => mentions(&operands.0) || mentions(&operands.1),
        Rvalue::Aggregate(_, operands) => operands.iter().any(mentions),
        Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::CopyForDeref(place)
        | Rvalue::Len(place) => place.local == local,
        _ => false,
    }
}

/// Every call site whose returned alias the caller consumes where it is
/// produced: the callee position is a Return-only `Retains` (the alias IS the
/// argument) and the caller's result local is read through only. Derived once
/// with the rows, so the site query is a lookup.
pub(crate) fn consumed_results(
    program: &RustProgram<'_>,
    rows: &FxHashMap<(LocalDefId, usize), RetentionVerdict>,
) -> FxHashSet<(LocalDefId, u32, u32)> {
    use super::decision::raw_boundary::RetentionEventKind;
    let tcx: TyCtxt<'_> = program.tcx;
    let return_only = |callee: LocalDefId| {
        (0..8).any(|index| {
            matches!(
                rows.get(&(callee, index)),
                Some(RetentionVerdict::Retains { sink, path })
                    if sink.kind == RetentionEventKind::Return
                        && path.iter().all(|step| step.kind == RetentionEventKind::Return)
            )
        })
    };
    let mut out = FxHashSet::default();
    for &function in &program.functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let body: &Body<'_> = &body;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Call {
                func, destination, ..
            } = &data.terminator().kind
            else {
                continue;
            };
            let Some(callee) = resolved(func)
                .and_then(|callee| callee.as_local())
                .filter(|callee| program.functions.contains(callee) && return_only(*callee))
            else {
                continue;
            };
            let _ = callee;
            let Some(result) = destination.as_local() else { continue };
            if result_consumed_in_place(tcx, &program.functions, body, result) {
                out.insert((function, block.as_u32(), data.statements.len() as u32));
            }
        }
    }
    out
}

/// The caller side of the returned-alias continuation: the alias the call
/// returned is CONSUMED where it is produced — the caller never uses it
/// itself (no deref, no store, no return) and passes it on only to local
/// callees that are descendant-free at that position. heman's
/// `kmVec2Length(kmVec2Subtract(&mut tmp, a, b))` is the shape.
///
/// This is deliberately stricter than the descendant scan: a caller that
/// KEEPS the returned alias and reads or writes through it later holds a live
/// raw alias of the subject beside the safe view the site emits, which is the
/// R395-2 channel (`wave6r_returned_alias_kept_by_caller_keeps_hold`).
fn result_consumed_in_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &[LocalDefId],
    body: &Body<'tcx>,
    result: Local,
) -> bool {
    if !pointer(body.local_decls[result].ty) {
        return true;
    }
    let mut aliases = vec![result];
    let mut changed = true;
    while changed {
        changed = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let (lhs, rhs) = (&assignment.0, &assignment.1);
                if let Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) = rhs
                    && let Some(source) = operand_local(operand)
                    && aliases.contains(&source)
                    && let Some(destination) = lhs.as_local()
                    && destination != rustc_middle::mir::RETURN_PLACE
                    && pointer(body.local_decls[destination].ty)
                    && !aliases.contains(&destination)
                {
                    aliases.push(destination);
                    changed = true;
                }
            }
        }
    }
    let touches = |place: &rustc_middle::mir::Place<'_>| {
        aliases.contains(&place.local) && !place.projection.is_empty()
    };
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (lhs, rhs) = (&assignment.0, &assignment.1);
            // A use THROUGH the alias (`(*r).x = ..`, `let y = (*r).x`) is the
            // caller holding a live raw view of the subject: not consumed.
            if touches(lhs) {
                return false;
            }
            let operand_place = |operand: &Operand<'tcx>| operand.place();
            let used_through = match rhs {
                Rvalue::Use(operand)
                | Rvalue::Cast(_, operand, _)
                | Rvalue::Repeat(operand, _)
                | Rvalue::UnaryOp(_, operand)
                | Rvalue::ShallowInitBox(operand, _) => {
                    operand_place(operand).as_ref().is_some_and(touches)
                }
                Rvalue::BinaryOp(_, operands) => {
                    operand_place(&operands.0).as_ref().is_some_and(touches)
                        || operand_place(&operands.1).as_ref().is_some_and(touches)
                }
                Rvalue::Aggregate(_, operands) => operands
                    .iter()
                    .any(|operand| operand_place(operand).as_ref().is_some_and(touches)),
                Rvalue::Ref(_, _, place)
                | Rvalue::RawPtr(_, place)
                | Rvalue::Discriminant(place)
                | Rvalue::CopyForDeref(place)
                | Rvalue::Len(place) => touches(place),
                _ => false,
            };
            if used_through {
                return false;
            }
            match rhs {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                    if operand_local(operand).is_some_and(|local| aliases.contains(&local))
                        && lhs
                            .as_local()
                            .is_none_or(|destination| !aliases.contains(&destination))
                    {
                        return false;
                    }
                }
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    if aliases.contains(&place.local) {
                        return false;
                    }
                }
                Rvalue::BinaryOp(_, operands) => {
                    if operand_local(&operands.0)
                        .into_iter()
                        .chain(operand_local(&operands.1))
                        .any(|local| aliases.contains(&local))
                    {
                        return false;
                    }
                }
                Rvalue::Aggregate(_, operands) => {
                    if operands
                        .iter()
                        .any(|operand| operand_local(operand).is_some_and(|l| aliases.contains(&l)))
                    {
                        return false;
                    }
                }
                _ => {}
            }
        }
        let (func, args) = match &data.terminator().kind {
            TerminatorKind::Call { func, args, .. } => (func, args),
            TerminatorKind::TailCall { func, args, .. } => (func, args),
            _ => continue,
        };
        let passed = args
            .iter()
            .enumerate()
            .filter(|(_, argument)| {
                operand_local(&argument.node).is_some_and(|local| aliases.contains(&local))
                    || argument.node.place().is_some_and(|place| touches(&place))
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if passed.is_empty() {
            continue;
        }
        if matches!(data.terminator().kind, TerminatorKind::TailCall { .. }) {
            return false;
        }
        // Only a local callee this scan can read may receive the alias.
        let Some(callee) = resolved(func)
            .and_then(|callee| callee.as_local())
            .filter(|callee| functions.contains(callee))
        else {
            return false;
        };
        let mut visited = FxHashSet::default();
        if passed.iter().any(|index| {
            refusal(
                tcx,
                functions,
                callee,
                Local::from_usize(index + 1),
                &mut visited,
            )
            .is_some()
        }) {
            return false;
        }
    }
    true
}

/// The returned-alias continuation at ONE call site: a callee position whose
/// only retention is returning the parameter retains nothing beyond a call
/// whose result the caller discards. The retention row itself is untouched
/// (a caller that keeps the result keeps the sink); the site's effective
/// verdict becomes a no-retain certificate that names the discarded return.
pub(crate) fn site_retention(
    retention: &super::decision::raw_boundary::RetentionSummaries,
    caller: LocalDefId,
    key: &super::decision::raw_boundary::RawBoundarySiteKey,
    callee: LocalDefId,
) -> Option<RetentionVerdict> {
    use super::decision::raw_boundary::{RetentionCertificate, RetentionEventKind, RetentionStep};
    let base = retention.get(callee, key.argument_index)?;
    let RetentionVerdict::Retains { sink, path } = base else {
        return Some(base.clone());
    };
    let return_only = sink.kind == RetentionEventKind::Return
        && path
            .iter()
            .all(|step| step.kind == RetentionEventKind::Return);
    if !return_only {
        return Some(base.clone());
    }
    let certificate = |detail: &str| {
        Some(RetentionVerdict::NoRetain {
            certificate: RetentionCertificate {
                function: key.callee.path.clone(),
                argument_index: key.argument_index,
                steps: vec![
                    sink.clone(),
                    RetentionStep {
                        location: format!("bb{}:s{}", key.block, key.statement_index),
                        kind: RetentionEventKind::KnownNoRetainCall,
                        detail: detail.to_owned(),
                    },
                ],
                attestation: "closed_world_frozen_graph",
                frame_bounded: None,
            },
        })
    };
    if let Some(ChildAccess::Unused) = retention.type_backed_child_access(caller, key) {
        return certificate(RETURNED_ALIAS_DISCARDED);
    }
    // The caller consumes the returned alias where it is produced: the result
    // is only read through in the caller's body, so no alias of the argument
    // outlives the call (report 021, wave-5d2 014's `kmVec2Subtract` row).
    if retention.result_consumed_at(caller, key.block, key.statement_index) {
        return certificate(RETURNED_ALIAS_CONSUMED);
    }
    Some(base.clone())
}

pub(crate) const RETURNED_ALIAS_DISCARDED: &str = "returned-alias-discarded";

/// The same continuation where the caller CONSUMES the returned alias in the
/// statement that produced it (heman `kmVec2Length(kmVec2Subtract(..))`)
/// instead of discarding it: nothing keeps the alias past the call.
pub(crate) const RETURNED_ALIAS_CONSUMED: &str = "returned-alias-consumed";

/// Certificate replay for a site: a site certificate (its last step is the
/// discarded-return marker) is re-derived from the callee's row and the
/// caller's child record and must be equal; every other certificate is the
/// callee row's and replays through the collector's own check.
pub(crate) fn verify_certificate(
    retention: &super::decision::raw_boundary::RetentionSummaries,
    caller: LocalDefId,
    key: &super::decision::raw_boundary::RawBoundarySiteKey,
    callee: LocalDefId,
    certificate: &super::decision::raw_boundary::RetentionCertificate,
) -> Result<(), &'static str> {
    if certificate.steps.last().is_some_and(|step| {
        step.detail == RETURNED_ALIAS_DISCARDED || step.detail == RETURNED_ALIAS_CONSUMED
    }) {
        return match site_retention(retention, caller, key, callee) {
            Some(RetentionVerdict::NoRetain {
                certificate: expected,
            }) if &expected == certificate => Ok(()),
            _ => Err("retention-certificate-invalid"),
        };
    }
    retention.verify_certificate(callee, key.argument_index, certificate)
}

/// Rewrite the type-backed records whose callee position is descendant-free.
/// The retention rows are the same summaries the raw-boundary disposition
/// consumes; nothing is re-derived.
/// The child-access receipt header (relay wave-6r/017: one additive
/// instrument-only artifact; main writes it beside the other census rows).
pub(crate) const CHILD_ACCESS_HEADER: &str = "callee\targument_index\taccess\toutcome\treason\n";

pub(crate) fn discharge<'a>(
    program: &RustProgram<'_>,
    rows: &FxHashMap<(LocalDefId, usize), RetentionVerdict>,
    records: impl Iterator<Item = &'a mut ReturnedChildEvidence>,
) -> String {
    let tcx: TyCtxt<'_> = program.tcx;
    let mut memo = FxHashMap::<(LocalDefId, usize), Option<String>>::default();
    let mut receipt = FxHashMap::<(String, usize), (String, String, String)>::default();
    for record in records {
        if matches!(record.access, ChildAccess::Unused) {
            continue;
        }
        let access = match &record.access {
            ChildAccess::Unused => "unused",
            ChildAccess::ReadOnly { .. } => "read-only",
            ChildAccess::Writes { .. } => "writes",
            ChildAccess::Unknown { .. } => "unknown",
        }
        .to_owned();
        let index = record.key.parent_argument_index;
        let name = tcx.def_path_str(record.key.callee);
        let mut note = |outcome: &str, reason: &str| {
            receipt.insert(
                (name.clone(), index),
                (access.clone(), outcome.to_owned(), reason.to_owned()),
            );
        };
        let Some(callee) = record.key.callee.as_local() else {
            note("held", "callee-not-local");
            continue;
        };
        if !program.functions.contains(&callee) {
            note("held", "callee-outside-the-program");
            continue;
        }
        match rows.get(&(callee, index)) {
            Some(RetentionVerdict::NoRetain { .. }) => {}
            Some(RetentionVerdict::Retains { .. }) => {
                note("held", "callee-row-retains");
                continue;
            }
            _ => {
                note("held", "callee-row-unknown");
                continue;
            }
        }
        let refused = memo
            .entry((callee, index))
            .or_insert_with(|| {
                let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
                if index >= body.arg_count {
                    return Some("position-is-not-a-parameter".to_owned());
                }
                drop(body);
                refusal(
                    tcx,
                    &program.functions,
                    callee,
                    Local::from_usize(index + 1),
                    &mut FxHashSet::default(),
                )
            })
            .clone();
        if let Some(reason) = refused {
            note("held", &reason);
            continue;
        }
        note("discharged", "-");
        record.access = ChildAccess::Unused;
        record.contract_provenance = PROVENANCE;
    }
    let mut rows = receipt
        .into_iter()
        .map(|((callee, index), (access, outcome, reason))| {
            format!("{callee}\t{index}\t{access}\t{outcome}\t{reason}\n")
        })
        .collect::<Vec<_>>();
    rows.sort();
    let mut out = String::from(CHILD_ACCESS_HEADER);
    out.extend(rows);
    out
}
