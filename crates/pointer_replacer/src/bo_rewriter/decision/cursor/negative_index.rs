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
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Body, ConstOperand, Local, Location, Operand, PlaceElem, Rvalue, StatementKind},
    ty::{self, TyCtxt},
};
use rustc_mir_dataflow::Analysis as _;

use crate::analyses::offset_sign::sign::{AbsValue, Signedness};

/// Does some offset of `subject` (or of a copy of it) read definitely below
/// the pointer?
pub(super) fn reads_below_entry(tcx: TyCtxt<'_>, function: LocalDefId, subject: Local) -> bool {
    if !tcx.is_mir_available(function.to_def_id()) {
        return false;
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let body: &Body<'_> = &body;
    let chain = copies(body, subject);
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
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let rustc_middle::mir::TerminatorKind::Call { func, args, .. } = &data.terminator().kind
        else {
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
        if !receiver
            .node
            .place()
            .and_then(|place| place.as_local())
            .is_some_and(|local| chain.contains(&local))
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
        let below = if backward {
            matches!(value, AbsValue::Pos)
                || matches!(value, AbsValue::ConstU(c) if c > 0)
                || matches!(value, AbsValue::ConstI(c) if c > 0)
        } else {
            matches!(value, AbsValue::Neg) || matches!(value, AbsValue::ConstI(c) if c < 0)
        };
        if below {
            return true;
        }
    }
    false
}

/// The subject and every local that holds the same pointer and nothing else:
/// each of its assignments is a copy, a cast or the `&*p` reborrow idiom of
/// the chain. A local that is ALSO assigned anything else (`p = c; … p =
/// p.offset(1)`) is a walker of its own, not this pointer, and its reads are
/// not the subject's.
fn copies(body: &Body<'_>, start: Local) -> FxHashSet<Local> {
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
        if let rustc_middle::mir::TerminatorKind::Call { destination, .. } = &data.terminator().kind
            && let Some(destination) = destination.as_local()
        {
            sources.entry(destination).or_default().push(None);
        }
    }
    let mut closure = FxHashSet::from_iter([start]);
    let mut changed = true;
    while changed {
        changed = false;
        for (destination, from) in &sources {
            if !closure.contains(destination)
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
