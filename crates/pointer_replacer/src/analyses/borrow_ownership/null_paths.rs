//! era-5c (R404-3): path-sensitive null facts for the ownership solver.
//!
//! The ownership model equates every incoming version of a local at a phi
//! node, so a token retained on one path and moved out on another refuses the
//! whole function (bst's `deleteNode`: on the `left == NULL` arm the `left`
//! field's token survives the free while the `right == NULL` arm moves `left`
//! out and returns it; `insert`: the `node == NULL` arm keeps the parameter's
//! token to the exit while `return node` moves it). A pointer that is NULL on a
//! path guards no object, so its token is vacuous there: dropping it at the
//! join is sound with no waiver — the emitted `Option<Box<_>>` is `None` on
//! that path and dropping `None` frees nothing.
//!
//! This module computes MUST-null facts over the MIR CFG: a fact is generated on
//! the non-zero edge of a `switchInt` whose discriminant is the result of
//! `is_null` on a copy of the place, killed by any assignment to the place (or
//! to any place behind a pointer, conservatively, when the fact itself is behind
//! one), by storage ends, and by every call except the pure `is_null` and the
//! non-writing `free`; joins intersect. The solver consumes the facts at phi
//! edges only (`infer.rs::join_phi_nodes`), behind `CRAT_ERA5C_MOVE_TRACKING`.

use std::collections::BTreeSet;

use rustc_data_structures::graph::Successors;
use rustc_hash::FxHashMap;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind, UnOp,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use smallvec::SmallVec;

use super::ptr::Measurable;

/// R404-3 / R405-1: the per-path token disposition arm. Default off, fail-loud
/// on a typo (as every era-5b pin is), and carried by `solver_identity` so the
/// two arms can never share a cache key.
pub(crate) fn move_tracking() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| match std::env::var("CRAT_ERA5C_MOVE_TRACKING") {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) => match value.as_str() {
            "on" => true,
            "off" => false,
            other => panic!("CRAT_ERA5C_MOVE_TRACKING must be on or off; got {other:?}"),
        },
        Err(error) => panic!("CRAT_ERA5C_MOVE_TRACKING is not valid Unicode: {error}"),
    })
}

/// A projection step of a null place. Only dereferences and fields are
/// represented; any other projection makes the place untracked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Proj {
    Deref,
    Field(u32),
}

/// A place known to hold a null pointer: a local plus a projection path.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct NullPlace {
    pub(crate) local: Local,
    pub(crate) proj: SmallVec<[Proj; 2]>,
}

impl NullPlace {
    pub(crate) fn of(place: &Place<'_>) -> Option<Self> {
        let mut proj = SmallVec::new();
        for elem in place.projection {
            match elem {
                ProjectionElem::Deref => proj.push(Proj::Deref),
                ProjectionElem::Field(field, _) => proj.push(Proj::Field(field.as_u32())),
                _ => return None,
            }
        }
        Some(NullPlace {
            local: place.local,
            proj,
        })
    }

    fn behind_pointer(&self) -> bool {
        self.proj.contains(&Proj::Deref)
    }

    /// `self` is `prefix` extended by `rest` (possibly empty).
    fn strip_prefix(&self, prefix: &NullPlace) -> Option<&[Proj]> {
        (self.local == prefix.local && self.proj.starts_with(&prefix.proj))
            .then(|| &self.proj[prefix.proj.len()..])
    }
}

type Facts = BTreeSet<NullPlace>;

/// Must-null facts on every CFG edge of one body.
#[derive(Debug, Default)]
pub(crate) struct NullPaths {
    edges: FxHashMap<(BasicBlock, BasicBlock), Facts>,
}

impl NullPaths {
    pub(crate) fn compute<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        let blocks = &body.basic_blocks;
        // `None` is the top element: not yet reached by the fixpoint.
        let mut entry: IndexVec<BasicBlock, Option<Facts>> =
            IndexVec::from_elem_n(None, blocks.len());
        entry[rustc_middle::mir::START_BLOCK] = Some(Facts::new());
        let order: Vec<BasicBlock> = blocks.reverse_postorder().to_vec();
        let mut edges: FxHashMap<(BasicBlock, BasicBlock), Facts> = FxHashMap::default();
        loop {
            let mut changed = false;
            for &bb in &order {
                let Some(facts) = entry[bb].clone() else {
                    continue;
                };
                let out = transfer_block(tcx, body, bb, facts);
                for succ in blocks.successors(bb) {
                    let mut edge = out.clone();
                    if let Some(generated) = edge_gen(tcx, body, bb, succ) {
                        edge.insert(generated);
                    }
                    let previous = edges.insert((bb, succ), edge.clone());
                    if previous.as_ref() != Some(&edge) {
                        changed = true;
                    }
                    let joined = match &entry[succ] {
                        None => edge,
                        Some(current) => current.intersection(&edge).cloned().collect(),
                    };
                    if entry[succ].as_ref() != Some(&joined) {
                        entry[succ] = Some(joined);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        NullPaths { edges }
    }

    /// Whether `place` is known null on the edge `pred -> succ`.
    pub(crate) fn null_on_edge(
        &self,
        pred: BasicBlock,
        succ: BasicBlock,
        place: &NullPlace,
    ) -> bool {
        self.edges
            .get(&(pred, succ))
            .is_some_and(|facts| facts.contains(place))
    }

    /// Every fact on the edge `pred -> succ` about `local`, as (projection)
    /// paths.
    pub(crate) fn local_facts_on_edge(
        &self,
        pred: BasicBlock,
        succ: BasicBlock,
        local: Local,
    ) -> Vec<NullPlace> {
        self.edges
            .get(&(pred, succ))
            .map(|facts| {
                facts
                    .iter()
                    .filter(|fact| fact.local == local)
                    .cloned()
                    .collect()
            })
            .unwrap_or_default()
    }
}

fn is_named_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    name: &str,
) -> bool {
    let TyKind::FnDef(def_id, _) = func.ty(body, tcx).kind() else {
        return false;
    };
    tcx.item_name(*def_id).as_str() == name
}

/// Kill every fact `dst` may write: the destination itself and everything it
/// prefixes; and, when the destination is behind a pointer, every fact that is
/// itself behind a pointer (the two pointers may alias).
fn kill_assigned(facts: &mut Facts, dst: &Place<'_>) {
    let behind_pointer = dst
        .projection
        .iter()
        .any(|elem| matches!(elem, ProjectionElem::Deref));
    let dst_local = dst.local;
    let dst = NullPlace::of(dst);
    facts.retain(|fact| {
        if behind_pointer && fact.behind_pointer() {
            return false;
        }
        match &dst {
            Some(dst) => fact.strip_prefix(dst).is_none(),
            // An untracked projection on `dst.local`: kill the local wholesale.
            None => fact.local != dst_local,
        }
    });
}

fn kill_local(facts: &mut Facts, local: Local) {
    facts.retain(|fact| fact.local != local);
}

fn kill_behind_pointers(facts: &mut Facts) {
    facts.retain(|fact| !fact.behind_pointer());
}

/// `dst = <src>`: every fact about `src` (or below it) becomes a fact about
/// `dst` (or the same path below it). Facts are copied, never moved: `src`
/// keeps its own.
fn propagate_copy(facts: &mut Facts, dst: &Place<'_>, src: &Place<'_>) {
    let (Some(dst), Some(src)) = (NullPlace::of(dst), NullPlace::of(src)) else {
        return;
    };
    let mut fresh = Vec::new();
    for fact in facts.iter() {
        if let Some(rest) = fact.strip_prefix(&src) {
            let mut proj = dst.proj.clone();
            proj.extend_from_slice(rest);
            fresh.push(NullPlace {
                local: dst.local,
                proj,
            });
        }
    }
    facts.extend(fresh);
}

fn transfer_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    mut facts: Facts,
) -> Facts {
    let data = &body.basic_blocks[bb];
    for statement in &data.statements {
        match &statement.kind {
            StatementKind::Assign(assign) => {
                let (dst, rvalue) = &**assign;
                let source = match rvalue {
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => Some(src),
                    Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => Some(src),
                    Rvalue::CopyForDeref(src) => Some(src),
                    _ => None,
                };
                // The source is read before the destination is written: the
                // copied facts are taken first, the destination's storage is
                // killed, then the copies are added.
                let mut copied = Facts::new();
                if let Some(src) = source {
                    copied = facts.clone();
                    propagate_copy(&mut copied, dst, src);
                    copied.retain(|fact| !facts.contains(fact));
                }
                kill_assigned(&mut facts, dst);
                facts.extend(copied);
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                kill_local(&mut facts, *local);
            }
            StatementKind::SetDiscriminant { place, .. } | StatementKind::Deinit(place) => {
                kill_assigned(&mut facts, place);
            }
            StatementKind::Intrinsic(..) => kill_behind_pointers(&mut facts),
            StatementKind::FakeRead(..)
            | StatementKind::Retag(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::Nop => {}
        }
    }
    match &data.terminator().kind {
        TerminatorKind::Call {
            func, destination, ..
        } => {
            kill_assigned(&mut facts, destination);
            if !(is_named_call(tcx, body, func, "is_null")
                || is_named_call(tcx, body, func, "free"))
            {
                kill_behind_pointers(&mut facts);
            }
        }
        TerminatorKind::Drop { place, .. } => {
            kill_assigned(&mut facts, place);
            kill_behind_pointers(&mut facts);
        }
        TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } => facts.clear(),
        TerminatorKind::Goto { .. }
        | TerminatorKind::SwitchInt { .. }
        | TerminatorKind::Return
        | TerminatorKind::Unreachable
        | TerminatorKind::Assert { .. }
        | TerminatorKind::FalseEdge { .. }
        | TerminatorKind::FalseUnwind { .. }
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::CoroutineDrop
        | TerminatorKind::TailCall { .. } => {}
    }
    facts
}

/// The fact an edge `bb -> succ` generates: `bb` ends in `switchInt(d)` where
/// `d` is (possibly the negation of) the result of `is_null(x)` in the block that
/// runs immediately before, `x` a copy of some tracked place `P` with no write
/// to `P` in between, and `succ` is the edge taken when the tested pointer is
/// null.
fn edge_gen<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    succ: BasicBlock,
) -> Option<NullPlace> {
    let data = &body.basic_blocks[bb];
    let TerminatorKind::SwitchInt { discr, targets } = &data.terminator().kind else {
        return None;
    };
    let discr = discr.place()?;
    if !discr.projection.is_empty() {
        return None;
    }
    // Resolve the discriminant through negations inside this block.
    let mut tested = discr.local;
    let mut negated = false;
    for statement in data.statements.iter().rev() {
        let StatementKind::Assign(assign) = &statement.kind else {
            continue;
        };
        let (dst, rvalue) = &**assign;
        if dst.as_local() != Some(tested) {
            if dst.local == tested {
                return None;
            }
            continue;
        }
        match rvalue {
            Rvalue::UnaryOp(UnOp::Not, Operand::Copy(src) | Operand::Move(src)) => {
                tested = src.as_local()?;
                negated = !negated;
            }
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                tested = src.as_local()?;
            }
            _ => return None,
        }
    }
    // The switch block must not itself write the tested pointer's place.
    // (It runs after the call block; only local moves of the discriminant are
    // admitted above.)
    // Find the unique predecessor whose call terminator defines `tested`.
    let preds = &body.basic_blocks.predecessors()[bb];
    let [pred] = preds.as_slice() else {
        return None;
    };
    let pred_data = &body.basic_blocks[*pred];
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target: Some(target),
        ..
    } = &pred_data.terminator().kind
    else {
        return None;
    };
    if *target != bb || destination.as_local() != Some(tested) {
        return None;
    }
    if !is_named_call(tcx, body, func, "is_null") {
        return None;
    }
    let [arg] = args.as_ref() else {
        return None;
    };
    let arg = arg.node.place()?;
    let arg_local = arg.as_local()?;
    // Resolve the argument temporary to the place it copies, within the call
    // block, requiring no write to that place after the copy.
    let mut place: Option<Place<'tcx>> = None;
    let mut index = pred_data.statements.len();
    for (i, statement) in pred_data.statements.iter().enumerate().rev() {
        let StatementKind::Assign(assign) = &statement.kind else {
            continue;
        };
        let (dst, rvalue) = &**assign;
        if dst.as_local() == Some(arg_local) {
            match rvalue {
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                | Rvalue::CopyForDeref(src) => {
                    place = Some(*src);
                    index = i;
                }
                _ => {}
            }
            break;
        }
    }
    let place = place?;
    let tested_place = NullPlace::of(&place)?;
    for statement in &pred_data.statements[index + 1..] {
        match &statement.kind {
            StatementKind::Assign(assign) => {
                let (dst, _) = &**assign;
                let mut probe = Facts::new();
                probe.insert(tested_place.clone());
                kill_assigned(&mut probe, dst);
                if probe.is_empty() {
                    return None;
                }
            }
            StatementKind::StorageDead(local) | StatementKind::StorageLive(local)
                if *local == tested_place.local =>
            {
                return None;
            }
            _ => {}
        }
    }
    // Which edge is the null edge: the non-zero target (bool true), unless the
    // discriminant was negated.
    let mut null_targets: Vec<BasicBlock> = Vec::new();
    let mut nonnull_targets: Vec<BasicBlock> = Vec::new();
    let mut explicit_zero = false;
    let mut explicit_nonzero = false;
    for (value, target) in targets.iter() {
        if value == 0 {
            explicit_zero = true;
            nonnull_targets.push(target);
        } else {
            explicit_nonzero = true;
            null_targets.push(target);
        }
    }
    let otherwise = targets.otherwise();
    if explicit_zero && !explicit_nonzero {
        null_targets.push(otherwise);
    } else if explicit_nonzero && !explicit_zero {
        nonnull_targets.push(otherwise);
    } else {
        return None;
    }
    if negated {
        std::mem::swap(&mut null_targets, &mut nonnull_targets);
    }
    // A target reached on both a null and a non-null edge carries nothing.
    (null_targets.contains(&succ) && !nonnull_targets.contains(&succ)).then_some(tested_place)
}

/// Which components of a local's ownership window are vacuous on an edge: the
/// window is `[ptr, <pointer fields in leaf order>...]` for a pointer to a
/// struct (deeper levels follow the same layout recursively, exactly as
/// `infer.rs::project_deeper` lays them out). A null base makes every
/// component vacuous; a null field makes that field's sub-window vacuous.
pub(crate) fn vacuous_components_with<'tcx>(
    tcx: TyCtxt<'tcx>,
    measurable: &impl Measurable<'tcx>,
    ty: Ty<'tcx>,
    window: u32,
    facts: &[NullPlace],
) -> Vec<bool> {
    let mut vacuous = vec![false; window as usize];
    if window == 0 {
        return vacuous;
    }
    let precision = measurable.absolute_precision(ty, window) as u32;
    let max_ptr_chased = measurable.max_ptr_chased() as u32;
    for fact in facts {
        let mut base_ty = ty;
        let mut ptr_chased = max_ptr_chased.saturating_sub(precision);
        let mut offset = 0u32;
        let mut tracked = true;
        for step in &fact.proj {
            match step {
                Proj::Deref => {
                    let Some(pointee) = base_ty.builtin_deref(true) else {
                        tracked = false;
                        break;
                    };
                    offset += 1;
                    base_ty = pointee;
                    ptr_chased += 1;
                }
                Proj::Field(field) => {
                    let TyKind::Adt(adt_def, args) = base_ty.kind() else {
                        tracked = false;
                        break;
                    };
                    if !adt_def.is_struct() {
                        tracked = false;
                        break;
                    }
                    let Some(field_def) = adt_def
                        .non_enum_variant()
                        .fields
                        .iter()
                        .nth(*field as usize)
                    else {
                        tracked = false;
                        break;
                    };
                    offset += measurable.field_offset(*adt_def, *field as usize, ptr_chased);
                    base_ty = field_def.ty(tcx, args);
                }
            }
        }
        if !tracked {
            continue;
        }
        let extent = if ptr_chased >= max_ptr_chased {
            1
        } else {
            measurable.measure(base_ty, ptr_chased).max(1)
        };
        for index in offset..(offset + extent).min(window) {
            vacuous[index as usize] = true;
        }
    }
    vacuous
}

/// E5C-3 (R406-7 §4): the deferred argument move. For `_t = copy/move P` at
/// `location`, where `_t` is a call-argument temporary of the block's own call
/// terminator and every statement between the copy and the terminator is a
/// pure read (a copy into a fresh local, a storage marker, a non-writing
/// rvalue — never a store, a borrow, a call or an intrinsic), the READ of `P`
/// is attributed to the terminator: that is where the ownership model
/// transfers the token, and a loan live only until a later pure read of the
/// same block (bst's `(*temp).key` at 18:9, moved past by `_40 = copy
/// (*root).right` at 18:7) is then dead at the move. The emission side owes
/// the matching hoist of those reads above the moving argument. `None` when
/// the arm is off or the shape does not hold.
pub(crate) fn deferred_argument_read<'tcx>(
    body: &Body<'tcx>,
    location: rustc_middle::mir::Location,
) -> Option<rustc_middle::mir::Location> {
    if !move_tracking() {
        return None;
    }
    let data = &body.basic_blocks[location.block];
    let statement = data.statements.get(location.statement_index)?;
    let StatementKind::Assign(assign) = &statement.kind else {
        return None;
    };
    let (dst, rvalue) = &**assign;
    let dst = dst.as_local()?;
    if !matches!(
        rvalue,
        Rvalue::Use(Operand::Copy(_) | Operand::Move(_)) | Rvalue::CopyForDeref(_)
    ) {
        return None;
    }
    let TerminatorKind::Call { args, .. } = &data.terminator().kind else {
        return None;
    };
    // `_t` feeds this block's call and nothing else in the block.
    if !args
        .iter()
        .any(|arg| arg.node.place().and_then(|p| p.as_local()) == Some(dst))
    {
        return None;
    }
    for later in &data.statements[location.statement_index + 1..] {
        match &later.kind {
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {}
            StatementKind::Assign(later_assign) => {
                let (later_dst, later_rvalue) = &**later_assign;
                // A fresh local written by a non-writing rvalue that does not
                // read `_t` itself.
                if later_dst.as_local().is_none() {
                    return None;
                }
                let pure = match later_rvalue {
                    Rvalue::Use(operand)
                    | Rvalue::Cast(_, operand, _)
                    | Rvalue::UnaryOp(_, operand) => operand_reads_other(operand, dst),
                    Rvalue::BinaryOp(_, operands) => {
                        operand_reads_other(&operands.0, dst)
                            && operand_reads_other(&operands.1, dst)
                    }
                    Rvalue::CopyForDeref(place) => place.local != dst,
                    _ => false,
                };
                if !pure {
                    return None;
                }
            }
            _ => return None,
        }
    }
    Some(rustc_middle::mir::Location {
        block: location.block,
        statement_index: data.statements.len(),
    })
}

fn operand_reads_other(operand: &Operand<'_>, temp: Local) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.local != temp,
        Operand::Constant(_) => true,
    }
}
