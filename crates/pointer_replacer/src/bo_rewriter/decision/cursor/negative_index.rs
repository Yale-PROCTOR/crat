//! **R608-1 — a definitely-negative index below a parameter's entry.**
//!
//! A parameter cursor's window is the slice its caller hands over, starting at
//! the pointer (`parameter_form` = `Slice`, position 0). A parameter that never
//! moves and is read at a definitely-negative offset therefore panics on the
//! first such read, where the input — handed an interior pointer — was correct.
//! brotli's `BrotliBuildHuffmanTable::symbol_lists` is the shape: handed over
//! 16 elements into its array, scanned from `max_length = -1` down.
//!
//! `SignFacts` cannot say this: `Neg` and `Top` share its one bit (S3.2′-3), and
//! a `Top` index is what the five parameter cursors batch 48 delivers read. So
//! this reads each offset operand's value AT ITS CALL, through the analysis's
//! own transfer (`Signedness`), run here over the owner's MIR. The export and
//! `analyses/` are untouched, as `compare_only_offset` does it (R320-1).
//!
//! Fires on a definite negative only: `Neg` or a negative constant at an
//! `offset`, or a strictly positive step at a `sub`. `Top` and `NonPos` never
//! fire. The run has no branch narrowing and no caller refinement: both only
//! sharpen a value, so a `Neg` read here is still sound, and a value they would
//! have sharpened to `Neg` reads `Top` — the guard can miss, never misfire.
//!
//! **R609-4 (c) — a loaded index, by measurement.** brotli's two
//! `Process*CodeLength` rows read `symbol_lists` at a value LOADED from
//! `next_symbol[…]` (set to `i - 16` in another function), which the lattice
//! reads as `Top`. The second hold refuses an index that is, through copies and
//! integer casts only, a load through a deref at every definition. It fires on
//! `Top`, and is scoped by measurement: none of the five parameter cursors batch
//! 48 delivers reads such an index (slicecursor 078; one control each pins it).
//! A parameter, a constant, arithmetic, a call result, a partial write or an
//! address-taken local anywhere on the chain answers no.
//!
//! **Its reads are the parameter's own**: the parameter and the compiler's
//! temporaries that copy it, never a NAMED local copy. brotli's fragment core
//! loops (`let base_ip = input; … base_ip.offset(*table.offset(hash))`) index a
//! named peer by a table of stored positions, which are never below `input` — a
//! `Top` that is correct, on the path this family is building. The `Neg` hold
//! keeps the whole chain: a definite negative is below the entry through any
//! copy.
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{
        Body, CastKind, ConstOperand, Local, Location, Operand, PlaceElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{self, TyCtxt},
};
use rustc_mir_dataflow::Analysis as _;

use crate::analyses::offset_sign::sign::{AbsValue, Signedness};

/// Does some offset of `subject` (or of a copy of it) read below the pointer
/// — definitely (`Neg`), or at an index loaded through a deref (R609-4 (c))?
/// The definite answer wins when both apply.
pub(super) fn below_entry(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    subject: Local,
) -> Option<super::CursorHold> {
    if !tcx.is_mir_available(function.to_def_id()) {
        return None;
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let body: &Body<'_> = &body;
    let chain = copies(body, subject, true);
    let own = copies(body, subject, false);
    let addr_takens = addr_takens(body);
    let mut cursor = Signedness {
        tcx,
        local_tys: body.local_decls.iter().map(|decl| decl.ty).collect(),
        addr_takens: &addr_takens,
        caller_param_vals: Default::default(),
        branch_conditions: Default::default(),
    }
    .iterate_to_fixpoint(tcx, body, None)
    .into_results_cursor(body);
    let mut loaded_index = false;
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
            continue;
        };
        let Some(constant) = func.constant() else { continue };
        let ty::FnDef(callee, _) = *constant.const_.ty().kind() else { continue };
        let path = tcx.def_path(callee).to_string_no_crate_verbose();
        if !path.contains("ptr::") {
            continue;
        }
        let backward = match path.rsplit("::").next() {
            Some("offset" | "wrapping_offset") => false,
            Some("sub" | "wrapping_sub") => true,
            _ => continue,
        };
        let [receiver, delta] = &args[..] else { continue };
        let Some(receiver) = receiver.node.place().and_then(|place| place.as_local()) else {
            continue;
        };
        if !chain.contains(&receiver) {
            continue;
        }
        cursor.seek_before_primary_effect(Location {
            block,
            statement_index: data.statements.len(),
        });
        let value = match &delta.node {
            Operand::Copy(place) | Operand::Move(place) => match place.as_local() {
                Some(local) => cursor.get().0[local],
                None => AbsValue::Top,
            },
            Operand::Constant(constant) => constant_value(constant),
        };
        let below = if backward {
            matches!(value, AbsValue::Pos)
                || matches!(value, AbsValue::ConstU(c) if c > 0)
                || matches!(value, AbsValue::ConstI(c) if c > 0)
        } else {
            matches!(value, AbsValue::Neg) || matches!(value, AbsValue::ConstI(c) if c < 0)
        };
        if below {
            return Some(super::CursorHold::NegativeIndexBelowEntry);
        }
        loaded_index |=
            !backward && own.contains(&receiver) && loaded(body, &delta.node, &addr_takens);
    }
    loaded_index.then_some(super::CursorHold::LoadedIndexBelowEntry)
}

/// **Relay 116 (the stand-in review's finding 2).** Every pointer step whose
/// result `function` passes to ITSELF (a recursive call's argument rooted at
/// `subject`) moves forward by a non-negative amount: a forward `offset` / `add`
/// whose delta is zero, positive or non-negative, or a `sub` by zero. A
/// recursive step that may go backward wraps below the callee's window, which
/// the tail view cannot represent.
pub(super) fn recursive_steps_forward(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    subject: Local,
) -> bool {
    if !tcx.is_mir_available(function.to_def_id()) {
        return false;
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let body: &Body<'_> = &body;
    let chain = copies(body, subject, true);
    let addr_takens = addr_takens(body);
    let mut cursor = Signedness {
        tcx,
        local_tys: body.local_decls.iter().map(|decl| decl.ty).collect(),
        addr_takens: &addr_takens,
        caller_param_vals: Default::default(),
        branch_conditions: Default::default(),
    }
    .iterate_to_fixpoint(tcx, body, None)
    .into_results_cursor(body);
    // The locals handed to a recursive call.
    let mut handed = FxHashSet::default();
    for data in body.basic_blocks.iter() {
        let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
            continue;
        };
        let Some(constant) = func.constant() else { continue };
        let ty::FnDef(callee, _) = *constant.const_.ty().kind() else { continue };
        if callee != function.to_def_id() {
            continue;
        }
        handed.extend(args.iter().filter_map(|arg| arg.node.place()?.as_local()));
    }
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
        else {
            continue;
        };
        if !destination
            .as_local()
            .is_some_and(|local| handed.contains(&local))
        {
            continue;
        }
        let Some(constant) = func.constant() else { continue };
        let ty::FnDef(callee, _) = *constant.const_.ty().kind() else { continue };
        let path = tcx.def_path(callee).to_string_no_crate_verbose();
        if !path.contains("ptr::") {
            continue;
        }
        let backward = match path.rsplit("::").next() {
            Some("offset" | "add" | "wrapping_offset" | "wrapping_add") => false,
            Some("sub" | "wrapping_sub") => true,
            _ => continue,
        };
        let [receiver, delta] = &args[..] else { return false };
        if !receiver
            .node
            .place()
            .and_then(|place| place.as_local())
            .is_some_and(|receiver| chain.contains(&receiver))
        {
            continue;
        }
        cursor.seek_before_primary_effect(Location {
            block,
            statement_index: data.statements.len(),
        });
        let value = match &delta.node {
            Operand::Copy(place) | Operand::Move(place) => match place.as_local() {
                Some(local) => cursor.get().0[local],
                None => AbsValue::Top,
            },
            Operand::Constant(constant) => constant_value(constant),
        };
        let forward = if backward {
            matches!(value, AbsValue::Zero)
        } else {
            matches!(
                value,
                AbsValue::Zero | AbsValue::Pos | AbsValue::NonNeg | AbsValue::ConstU(_)
            ) || matches!(value, AbsValue::ConstI(c) if c > 0)
        };
        if !forward {
            return false;
        }
    }
    true
}

/// Is this operand, through copies and integer casts only, a load through a
/// deref at EVERY definition of every local on the way?
fn loaded(body: &Body<'_>, operand: &Operand<'_>, addr_takens: &FxHashSet<Local>) -> bool {
    let Some(start) = operand.place().and_then(|place| place.as_local()) else {
        return false;
    };
    let mut stack = vec![start];
    let mut seen = FxHashSet::default();
    let mut load = false;
    while let Some(local) = stack.pop() {
        if !seen.insert(local) {
            continue;
        }
        if local.index() <= body.arg_count || addr_takens.contains(&local) {
            return false;
        }
        let mut defined = false;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                if assignment.0.local != local {
                    continue;
                }
                if assignment.0.as_local().is_none() {
                    return false;
                }
                defined = true;
                let place = match &assignment.1 {
                    Rvalue::Use(operand) | Rvalue::Cast(CastKind::IntToInt, operand, _) => {
                        match operand.place() {
                            Some(place) => place,
                            None => return false,
                        }
                    }
                    Rvalue::CopyForDeref(place) => *place,
                    _ => return false,
                };
                if place
                    .projection
                    .iter()
                    .any(|e| matches!(e, PlaceElem::Deref))
                {
                    load = true;
                } else if let Some(source) = place.as_local() {
                    stack.push(source);
                } else {
                    return false;
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                && destination.local == local
            {
                return false;
            }
        }
        if !defined {
            return false;
        }
    }
    load
}

/// The subject and every local that holds the same pointer and nothing else:
/// each of its assignments is a copy, a cast or the `&*p` reborrow idiom of
/// the chain. A local that is ALSO assigned anything else (`p = c; … p =
/// p.offset(1)`) is a walker of its own, not this pointer, and its reads are
/// not the subject's. `named: false` stops at a user variable: the
/// compiler's temporaries only.
fn copies(body: &Body<'_>, start: Local, named: bool) -> FxHashSet<Local> {
    let mut sources = rustc_hash::FxHashMap::<Local, Vec<Option<Local>>>::default();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let Some(destination) = assignment.0.as_local() else { continue };
            let source = match &assignment.1 {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                    operand.place().and_then(|place| place.as_local())
                }
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    matches!(place.projection.first(), Some(PlaceElem::Deref))
                        .then_some(place.local)
                }
                _ => None,
            };
            sources.entry(destination).or_default().push(source);
        }
        if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && let Some(destination) = destination.as_local()
        {
            sources.entry(destination).or_default().push(None);
        }
    }
    // A user variable carries a debug name; the compiler's temporaries do not.
    let user_variables: FxHashSet<Local> = body
        .var_debug_info
        .iter()
        .filter_map(|info| match info.value {
            rustc_middle::mir::VarDebugInfoContents::Place(place) => place.as_local(),
            rustc_middle::mir::VarDebugInfoContents::Const(_) => None,
        })
        .collect();
    let mut closure = FxHashSet::from_iter([start]);
    let mut changed = true;
    while changed {
        changed = false;
        for (destination, from) in &sources {
            if !closure.contains(destination)
                && (named || !user_variables.contains(destination))
                && from
                    .iter()
                    .all(|source| source.is_some_and(|source| closure.contains(&source)))
            {
                closure.insert(*destination);
                changed = true;
            }
        }
    }
    closure
}

/// The analysis's own rule: a local whose address is taken without a deref.
fn addr_takens(body: &Body<'_>) -> FxHashSet<Local> {
    body.basic_blocks
        .iter()
        .flat_map(|data| data.statements.iter())
        .filter_map(|statement| match &statement.kind {
            StatementKind::Assign(assignment) => match &assignment.1 {
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
                    if !place
                        .projection
                        .iter()
                        .any(|e| matches!(e, PlaceElem::Deref)) =>
                {
                    Some(place.local)
                }
                _ => None,
            },
            _ => None,
        })
        .collect()
}

/// An evaluated integer constant, read as the analysis reads it; anything
/// else is `Top`.
fn constant_value(constant: &ConstOperand<'_>) -> AbsValue {
    let Some(scalar) = constant.const_.try_to_scalar() else { return AbsValue::Top };
    let Ok(scalar) = scalar.try_to_scalar_int() else { return AbsValue::Top };
    let bits = scalar.to_bits(scalar.size());
    match constant.const_.ty().kind() {
        ty::Int(_) => match scalar.size().sign_extend(bits) {
            0 => AbsValue::Zero,
            c => AbsValue::ConstI(c),
        },
        ty::Uint(_) => match bits {
            0 => AbsValue::Zero,
            c => AbsValue::ConstU(c),
        },
        _ => AbsValue::Top,
    }
}
