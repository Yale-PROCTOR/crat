//! **R864-1 (relay 299; fan-out 081) — the pairs the pair pass drops.** At an
//! in-program call, an argument handed to a formal the settled table delivers as
//! a reference, beside an argument handed to a formal that stays raw, may name
//! one object: libzahl's `zsqr(x.as_mut_ptr(), &mut *x.as_mut_ptr())` hands the
//! same `z_t` to `zsqr(a: *mut Z, b: &mut Z)`, which reads through `b` and writes
//! through `a` while `b` is a live, protected argument (UB under both models; the
//! fan-out's `repro/`). The pair pass keeps a may-overlap pair only when both
//! formals convert (`co_conversion.rs:1001`), and A5 replays only pairs both of
//! whose formals are Ref in the baseline, so no row, proof or receipt existed.
//!
//! The rule is R833-1's: a pair that may overlap at a call inside the program
//! keeps both sides raw. **Its scope is R870-1's (a), the gaps only:** a
//! contained pair, unresolved roots on both sides, one subject at a PAIR-owned
//! `clear` call. The pairs the PAIR knows (its raw view and ordering proof), the
//! seam's aliased-storage twin, the counted-void routes, A5's C-9 marks and the
//! field-load exemption keep their answers,
//! and the `overlapping` pairs are wave-5d's callee-peer rule's. The raw side is
//! raw already; the reference side, the callee's formal, is held
//! (`held:pair-not-shown-disjoint`, detail `ref-beside-raw`), and
//! `into-held-formal` holds the caller's binding behind it in the same fixpoint.
//!
//! **The same-subject rule (class 2)** comes first: two arguments rooted at one
//! binding are never disjoint, whatever a proof says (`zmul`'s
//! `zadd(&mut *b_low.as_mut_ptr(), b_low.as_mut_ptr(), …)` read
//! `clear:a5-proven-disjoint`).
//!
//! **The containment pair (R866-1, fan-out 083)** next: two arguments one of
//! which derives from the other's object overlap by construction. brotli's
//! `ProcessCommandsInternal` hands `SafeReadDistance(&mut *s, &mut *br)` with
//! `br = &mut (*s).br`: both formals delivered as `&mut`, no pair row at that
//! call. Where both formals are delivered references, both are held; where one
//! is raw, the reference side is (`ref-beside-ref` / `ref-beside-raw`).

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    HirId,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::{TyCtxt, TypeckResults};

use super::{
    Decision, DecisionTable, DegradeReason, SubjectKind,
    a5_site_proof::{A5SeamProofIndex, A5SiteProofVerdict},
    co_conversion::{PairRole, PairSiteDecision},
    emitability::{Arg, ArgShape, EmitabilityFacts},
};

/// One step from a root to the object an argument designates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Step {
    /// A field of a struct (never of a union) of the object so far.
    Field(rustc_span::Symbol),
    /// The pointee of the pointer value stored in the object so far.
    Load,
    /// A step the text does not place: a union member, a retyping cast, a byte
    /// step (the round-3 review's R3-2; `pair_disjointness`'s Erratum 9d (ii)).
    /// Two places past it are never disjoint.
    Opaque,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Root {
    Local(HirId),
    Static(DefId),
}

/// **The object a pointer argument designates** (the round-2 review's NEW-1 /
/// NEW-2), as a root and the steps from it: `&mut (*s).br` is `s / load / br`,
/// `x.as_mut_ptr()` and `&mut *x.as_mut_ptr()` are `x`, a pointer static `G` is
/// `G / load` (its value, not its storage), `(*s).p` is `s / load / p / load`.
/// An index and a typed pointer step are no step: two elements may coincide.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Designation {
    pub(crate) root: Root,
    pub(crate) steps: Vec<Step>,
}

/// The object a pointer-valued expression designates.
pub(crate) fn pointer_designation<'tcx>(
    typeck: &TypeckResults<'tcx>,
    expr: &rustc_hir::Expr<'tcx>,
) -> Option<Designation> {
    use rustc_hir::ExprKind;
    let opaque = |mut designation: Designation| {
        designation.steps.push(Step::Opaque);
        designation
    };
    // A cast that changes the pointee retypes the object (C's first-member rule).
    let retypes = |from: &rustc_hir::Expr<'tcx>| {
        let pointee = |ty: rustc_middle::ty::Ty<'tcx>| ty.builtin_deref(true);
        pointee(typeck.expr_ty_adjusted(from)) != pointee(typeck.expr_ty(expr))
    };
    match &expr.kind {
        ExprKind::Cast(inner, _) if retypes(inner) => {
            pointer_designation(typeck, inner).map(opaque)
        }
        ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) => pointer_designation(typeck, inner),
        ExprKind::AddrOf(_, _, place) => place_designation(typeck, place),
        ExprKind::MethodCall(segment, receiver, _, _) => match segment.ident.name.as_str() {
            "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub"
            | "cast_mut" | "cast_const" => pointer_designation(typeck, receiver),
            "cast" if !retypes(receiver) => pointer_designation(typeck, receiver),
            "byte_offset" | "byte_add" | "byte_sub" | "cast" => {
                pointer_designation(typeck, receiver).map(opaque)
            }
            // An array's or a slice's own elements.
            "as_ptr" | "as_mut_ptr"
                if typeck
                    .expr_ty_adjusted(receiver)
                    .builtin_deref(true)
                    .is_some_and(|pointee| pointee.is_slice() || pointee.is_array()) =>
            {
                adjusted_place_designation(typeck, receiver)
            }
            _ => None,
        },
        // A place read as a pointer value: the pointee of what it holds.
        ExprKind::Path(..)
        | ExprKind::Field(..)
        | ExprKind::Index(..)
        | ExprKind::Unary(rustc_hir::UnOp::Deref, _) => {
            let mut designation = place_designation(typeck, expr)?;
            designation.steps.push(Step::Load);
            Some(designation)
        }
        _ => None,
    }
}

/// The object a place expression names.
fn place_designation<'tcx>(
    typeck: &TypeckResults<'tcx>,
    expr: &rustc_hir::Expr<'tcx>,
) -> Option<Designation> {
    use rustc_hir::{
        ExprKind, QPath,
        def::{DefKind, Res},
    };
    let root = |root| {
        Some(Designation {
            root,
            steps: Vec::new(),
        })
    };
    match &expr.kind {
        ExprKind::Path(QPath::Resolved(None, path)) => match path.res {
            Res::Local(binding) => root(Root::Local(binding)),
            Res::Def(DefKind::Static { .. }, item) => root(Root::Static(item)),
            _ => None,
        },
        ExprKind::Field(base, field) => {
            let mut designation = adjusted_place_designation(typeck, base)?;
            designation
                .steps
                .push(if typeck.expr_ty_adjusted(base).is_union() {
                    Step::Opaque
                } else {
                    Step::Field(field.name)
                });
            Some(designation)
        }
        ExprKind::Index(base, _, _) => adjusted_place_designation(typeck, base),
        ExprKind::Unary(rustc_hir::UnOp::Deref, inner) => {
            let ty = typeck.expr_ty_adjusted(inner);
            if ty.is_any_ptr() || ty.is_box() {
                pointer_designation(typeck, inner)
            } else {
                None
            }
        }
        ExprKind::DropTemps(inner) => place_designation(typeck, inner),
        _ => None,
    }
}

/// A base place through its implicit dereferences (`r.f` with `r: &mut S`).
fn adjusted_place_designation<'tcx>(
    typeck: &TypeckResults<'tcx>,
    expr: &rustc_hir::Expr<'tcx>,
) -> Option<Designation> {
    use rustc_middle::ty::adjustment::Adjust;
    let mut designation = place_designation(typeck, expr)?;
    for adjustment in typeck.expr_adjustments(expr) {
        match adjustment.kind {
            Adjust::Deref(None) => designation.steps.push(Step::Load),
            Adjust::Deref(Some(_)) => return None,
            _ => {}
        }
    }
    Some(designation)
}

/// Does the designated object stay the same object from where it was read to
/// the call? Its root holds its object, or the root pointer is never assigned
/// (a `let` with no later write) or is an entry formal that keeps its entry
/// value, and nothing is loaded through memory after that.
fn stable(tcx: TyCtxt<'_>, caller: LocalDefId, designation: &Designation) -> bool {
    let loads = designation
        .steps
        .iter()
        .filter(|step| **step == Step::Load)
        .count();
    match (designation.root, loads, designation.steps.first()) {
        (_, 0, _) => true,
        (Root::Local(pointer), 1, Some(Step::Load)) => {
            super::nul_walk_arm::single_definition(tcx, caller, pointer).is_some()
                || is_entry_formal(tcx, caller, pointer)
        }
        _ => false,
    }
}

/// A pointer argument's designation with every single-definition pointer local
/// at its root replaced by its initializer's (`br` with `let br = &mut
/// (*s).br` is `s / load / br`), and whether a replacement happened.
pub(crate) fn normalized<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    typeck: &TypeckResults<'tcx>,
    mut designation: Designation,
) -> (Designation, bool) {
    let mut replaced = false;
    for _ in 0..4 {
        let Root::Local(pointer) = designation.root else {
            break;
        };
        if designation.steps.first() != Some(&Step::Load) {
            break;
        }
        let Some(inner) = super::nul_walk_arm::single_definition(tcx, caller, pointer)
            .and_then(|init| pointer_designation(typeck, init))
            .filter(|inner| stable(tcx, caller, inner))
        else {
            break;
        };
        designation = Designation {
            root: inner.root,
            steps: inner
                .steps
                .into_iter()
                .chain(designation.steps[1..].iter().copied())
                .collect(),
        };
        replaced = true;
    }
    (designation, replaced)
}

/// How two designations under one root relate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Overlap {
    /// One object, or one inside the other: equal steps, one a prefix of the
    /// other with no load past it, or a divergence past an opaque step.
    Yes,
    /// Distinct fields of one struct, nothing loaded or retyped before or past
    /// them.
    Disjoint,
    /// One is reached through a pointer stored inside the other: nothing the text
    /// shows, and the PAIR's or the exemption's (MED-3 (c)'s residual).
    LoadedOne,
    /// Both are reached through pointers loaded from distinct places: unresolved,
    /// as two loads under two roots are (the round-3 review's R3-4).
    LoadedBoth,
}

pub(crate) fn overlap(left: &Designation, right: &Designation) -> Overlap {
    let common = left
        .steps
        .iter()
        .zip(&right.steps)
        .take_while(|(l, r)| l == r)
        .count();
    let rest_loads = |steps: &[Step]| steps[common..].contains(&Step::Load);
    match (rest_loads(&left.steps), rest_loads(&right.steps)) {
        (true, true) => Overlap::LoadedBoth,
        (true, false) | (false, true) => Overlap::LoadedOne,
        (false, false) => match (left.steps.get(common), right.steps.get(common)) {
            (Some(Step::Field(_)), Some(Step::Field(_)))
                if !left.steps.contains(&Step::Opaque) && !right.steps.contains(&Step::Opaque) =>
            {
                Overlap::Disjoint
            }
            // One a prefix of the other, a divergence past an opaque step or at
            // one, or a field beside a load of one place (types that cannot both
            // hold).
            _ => Overlap::Yes,
        },
    }
}

/// What an argument names, for two arguments under different roots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Object {
    /// Storage of the caller's own frame (`x`, `&mut x`, `x.as_mut_ptr()`,
    /// `&mut (*x.as_mut_ptr()).f`).
    Frame(HirId),
    /// Inside the pointee of a pointer binding (`p`, `p.offset(k)`, `&mut
    /// (*p).f`), nothing loaded past it.
    Pointee(HirId),
    /// A static item's own storage (`TMP.as_mut_ptr()`); a pointer static's
    /// value is `Unknown`.
    Static(DefId),
    Null,
    Unknown,
}

fn object_of(designation: Option<&Designation>, null: bool) -> Object {
    if null {
        return Object::Null;
    }
    let Some(designation) = designation else {
        return Object::Unknown;
    };
    let loads = designation
        .steps
        .iter()
        .filter(|step| **step == Step::Load)
        .count();
    match (designation.root, loads, designation.steps.first()) {
        (Root::Local(binding), 0, _) => Object::Frame(binding),
        (Root::Local(binding), 1, Some(Step::Load)) => Object::Pointee(binding),
        (Root::Static(item), 0, _) => Object::Static(item),
        _ => Object::Unknown,
    }
}

/// Is this decision a reference family's (the reference side of a pair), and
/// is it mutable? Exhaustive by rule (`import_denylist`): a `Box` is an owner
/// the call moves, never a view, and a degraded subject is raw.
fn reference_family(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Ref { mutable }
        | Decision::InferredRef { mutable, .. }
        | Decision::Slice { mutable, .. }
        | Decision::NestedSlice { mutable, .. }
        | Decision::Opt { mutable, .. }
        | Decision::Cursor { mutable, .. } => Some(*mutable),
        Decision::Box(_) | Decision::Degraded(_) => None,
    }
}

fn is_raw(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(_) => true,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Cursor { .. }
        | Decision::Box(_) => false,
    }
}

/// How two arguments' objects relate, as far as the caller shows.
enum Relation {
    /// One object under one local root, or one inside the other (the
    /// same-subject rule, R864-1 (b)): equal designations, nested fields.
    Same,
    /// One static item's storage at both positions: no twin sees it.
    SameStatic,
    /// One argument's object is inside the other's through a local's
    /// definition (R866-1, brotli's `&mut *s` beside `&mut *br` with `br = &mut
    /// (*s).br`), or derives from it through a local assigned more than once.
    Contained,
    Disjoint,
    /// Neither object resolves to a binding (an opaque expression, a static
    /// beside a pointer): nothing else answers (libzahl's class 1).
    Unresolved,
    /// One side resolves: the PAIR, the twin or the field-load exemption answer
    /// (R870-1, scope (a)).
    Unknown,
}

/// The pair's own edge in the PAIR's receipts at this call (`l/r->…:verdict:
/// reason:family`, the review's MED-1): its verdict and whether a `clear` is a
/// certificate's (trusted) or the classifier's (`a5-proven-disjoint`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Edge {
    /// The PAIR places its raw view for this pair: overlapping or undeterminable.
    Ordered,
    CertifiedClear,
    /// R936-1 (P11): cleared by the global-or-integer premise, an assumption.
    /// It answers an unresolved pair, never one the text shows to be one
    /// object or one inside the other (the round-3 review's M1).
    PremiseClear,
    ClassifierClear,
    None,
}

fn pair_edge(
    pair_sites: &[PairSiteDecision],
    caller: LocalDefId,
    callee: LocalDefId,
    call_span: rustc_span::Span,
    left: usize,
    right: usize,
) -> Edge {
    let (low, high) = (left.min(right), left.max(right));
    let key = format!("{low}/{high}->");
    for pair in pair_sites.iter().filter(|pair| {
        pair.caller == caller
            && pair.callee == callee
            // This call's own rows: a nested call to the same callee reads
            // its own (the round-2 review's NEW-4).
            && pair.call_span.source_callsite() == call_span.source_callsite()
            && (pair.argument_index == left || pair.argument_index == right)
            && match pair.role {
                PairRole::Clear | PairRole::Primary | PairRole::RawView => true,
                PairRole::Blocked => false,
            }
    }) {
        for receipt in pair.peer_receipts.split(';') {
            let Some(rest) = receipt.strip_prefix(&key) else {
                continue;
            };
            return edge_of(rest);
        }
    }
    Edge::None
}

/// One receipt's edge, from the text after its `l/r->` key:
/// `positions:verdict:reason:family`.
fn edge_of(rest: &str) -> Edge {
    let mut fields = rest.splitn(4, ':');
    let _positions = fields.next();
    let verdict = fields.next().unwrap_or_default();
    let reason = fields.next().unwrap_or_default();
    match verdict {
        "clear" if reason.contains("a5-proven-disjoint") => Edge::ClassifierClear,
        "clear" if reason.contains("premise=global-or-integer-provenance") => Edge::PremiseClear,
        "clear" => Edge::CertifiedClear,
        _ => Edge::Ordered,
    }
}

#[cfg(test)]
mod edge_tests {
    use super::{Edge, edge_of};

    /// wave-5d 150d (the round-4 review's MED-1): a certificate's reason holds
    /// colons, so the premise's own key must be found in the whole receipt.
    #[test]
    fn r150d_a_premise_clear_receipt_is_a_premise_edge() {
        assert_eq!(
            edge_of(
                "1/2:clear:pair-disjoint:premise=global-or-integer-provenance:global-value:\
                 pair-disjointness-certificate:premise=global-or-integer-provenance"
            ),
            Edge::PremiseClear
        );
        assert_eq!(
            edge_of("1/2:clear:pair-disjoint:distinct-roots:pair-disjointness-certificate"),
            Edge::CertifiedClear
        );
        assert_eq!(
            edge_of("1/2:clear:a5-proven-disjoint:a5"),
            Edge::ClassifierClear
        );
        assert_eq!(edge_of("1/2:overlapping:x:y"), Edge::Ordered);
    }
}

/// The MIR locals a local's value derives from by construction (the review's
/// HIGH-2: no arbitrary call edges): copies and casts through temporaries, the
/// pointer steps and `as_ptr` / `as_mut_ptr` by name, and borrows of a place —
/// through a dereference of a local (`&mut (*s).br`) or of a frame object
/// itself (`&mut x`). Closed backward from `target`, `target` included.
fn strict_sources(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    target: rustc_middle::mir::Local,
) -> FxHashSet<rustc_middle::mir::Local> {
    use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind, TerminatorKind};
    fn whole(operand: &Operand<'_>) -> Option<Local> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let mut sources: FxHashMap<Local, Vec<Local>> = FxHashMap::default();
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (place, rvalue) = &**assign;
            if !place.projection.is_empty() {
                continue;
            }
            let from = match rvalue {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => whole(operand),
                Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed) => Some(borrowed.local),
                _ => None,
            };
            if let Some(from) = from {
                sources.entry(place.local).or_default().push(from);
            }
        }
        if let Some(terminator) = &block.terminator
            && let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            && destination.projection.is_empty()
            && let Some((callee, _)) = func.const_fn_def()
            && matches!(
                tcx.item_name(callee).as_str(),
                "offset"
                    | "add"
                    | "sub"
                    | "wrapping_offset"
                    | "wrapping_add"
                    | "wrapping_sub"
                    | "byte_offset"
                    | "byte_add"
                    | "byte_sub"
                    | "cast"
                    | "cast_mut"
                    | "cast_const"
                    | "as_ptr"
                    | "as_mut_ptr"
            )
            && let Some(from) = args.first().and_then(|argument| whole(&argument.node))
        {
            sources.entry(destination.local).or_default().push(from);
        }
    }
    let mut seen = FxHashSet::default();
    seen.insert(target);
    let mut work = vec![target];
    while let Some(local) = work.pop() {
        for &from in sources.get(&local).into_iter().flatten() {
            if seen.insert(from) {
                work.push(from);
            }
        }
    }
    seen
}

/// The MIR local of a HIR binding of `function`: a subject's own, else the
/// debug info's place at the binding's span.
fn mir_local_of(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    binding: HirId,
    subjects: &FxHashMap<(LocalDefId, HirId), rustc_middle::mir::Local>,
) -> Option<rustc_middle::mir::Local> {
    if let Some(&local) = subjects.get(&(function, binding)) {
        return Some(local);
    }
    let span = tcx.hir_span(binding);
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    body.var_debug_info
        .iter()
        .find_map(|info| match &info.value {
            rustc_middle::mir::VarDebugInfoContents::Place(place)
                if place.projection.is_empty() && info.source_info.span == span =>
            {
                Some(place.local)
            }
            _ => None,
        })
}

/// The reference-side formals R864-1 / R866-1 hold on this table, each with its
/// reason.
/// The reference-side formals R864-1 / R866-1 hold on this table, each with its
/// reason.
pub(crate) fn holds(
    tcx: TyCtxt<'_>,
    facts: &EmitabilityFacts,
    table: &DecisionTable,
    proofs: &A5SeamProofIndex,
    mut_facts: &crate::analyses::borrow_ownership::mutability_facts::MutFacts,
    pair_sites: &[PairSiteDecision],
    c9_marks: &[crate::analyses::borrow_ownership::a5_producer::PlannedC9Mark],
) -> Vec<((LocalDefId, HirId), DegradeReason)> {
    use super::seam::{Form, form_of};
    struct Formal<'a> {
        node: (LocalDefId, HirId),
        local: rustc_middle::mir::Local,
        decision: &'a Decision,
    }
    let formals: FxHashMap<(LocalDefId, usize), Formal<'_>> = table
        .entries
        .iter()
        .filter_map(|(subject, decision)| match subject.kind {
            SubjectKind::Param { hir_index } => Some((
                (subject.fn_did, hir_index),
                Formal {
                    node: (subject.fn_did, subject.hir_id),
                    local: subject.local,
                    decision,
                },
            )),
            _ => None,
        })
        .collect();
    let local_of: FxHashMap<(LocalDefId, HirId), rustc_middle::mir::Local> = table
        .entries
        .iter()
        .map(|(subject, _)| ((subject.fn_did, subject.hir_id), subject.local))
        .collect();
    let decision_of: FxHashMap<(LocalDefId, HirId), &Decision> = table
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect();
    let mut sources: FxHashMap<
        (LocalDefId, rustc_middle::mir::Local),
        FxHashSet<rustc_middle::mir::Local>,
    > = FxHashMap::default();
    // Does `inner`'s value derive from `outer`'s object (inclusion, not a
    // shared ancestor: the review's HIGH-2)?
    let mut derives = |function: LocalDefId, inner: HirId, outer: HirId| -> bool {
        let (Some(inner), Some(outer)) = (
            mir_local_of(tcx, function, inner, &local_of),
            mir_local_of(tcx, function, outer, &local_of),
        ) else {
            return false;
        };
        sources
            .entry((function, inner))
            .or_insert_with(|| strict_sources(tcx, function, inner))
            .contains(&outer)
    };
    // One walk of a caller's body per caller (the round-2 review's L1).
    let mut arguments: FxHashMap<LocalDefId, CallArguments<'_>> = FxHashMap::default();
    // A live counted position: does its contract count (not a handle)?
    let mut counted: FxHashMap<(LocalDefId, usize), Option<bool>> = FxHashMap::default();
    let mut out: FxHashMap<(LocalDefId, HirId), DegradeReason> = FxHashMap::default();
    let mut hold = |node: (LocalDefId, HirId), detail: String| {
        out.entry(node)
            .or_insert(DegradeReason::PairNotShownDisjoint { detail });
    };
    let mut callees: Vec<_> = facts.call_args.keys().copied().collect();
    callees.sort_by_key(|callee| callee.local_def_index.as_u32());
    for callee in callees {
        for call in &facts.call_args[&callee] {
            // The form the seam finds at an argument (`seam.rs`'s `found`); `None`
            // where the seam names no operand.
            let found = |arg: &Arg| -> Option<Form> {
                Some(match arg.shape {
                    ArgShape::BareLocal(binding) | ArgShape::CastOfLocal { binding, .. } => {
                        decision_of
                            .get(&(call.caller, binding))
                            .map_or(Form::Raw, |decision| form_of(decision))
                    }
                    ArgShape::AddrOf { mutable, .. } | ArgShape::AddrOfCast { mutable, .. } => {
                        Form::Ref { mutable }
                    }
                    ArgShape::RawExpr { .. } => table
                        .field_transactions
                        .argument_form(arg.span)
                        .unwrap_or(Form::Raw),
                    ArgShape::NullLit => Form::Raw,
                    ArgShape::Cast { .. } | ArgShape::Other => return None,
                })
            };
            // The seam consults its aliased-storage twin only at a call no PAIR
            // row owns (`seam.rs`'s `pair_owned_call`; the review's HIGH-1).
            let seam_pair_owned = std::cell::OnceCell::new();
            let seam_pair_owned = || {
                *seam_pair_owned.get_or_init(|| {
                    pair_sites.iter().any(|pair| {
                        pair.caller == call.caller
                            && pair.callee == callee
                            && pair
                                .call_span
                                .source_callsite()
                                .contains(call.span.source_callsite())
                            && match pair.role {
                                PairRole::Clear | PairRole::Primary | PairRole::RawView => true,
                                PairRole::Blocked => false,
                            }
                    })
                })
            };
            // Does `counted_void::aliased_storage_twin` take this call (the round-3
            // review's R3-1, its trigger mirrored)? A converted position whose root
            // a raw argument shares, that argument no field load the exemption
            // clears, and every converted position found raw or a reference (it
            // declines a slice, an option or a cursor: the round-2 review's HIGH-1
            // residual). The settled table is read for the seam's (R3-6).
            let twin_fires = || {
                let converted = |arg: &Arg| {
                    formals
                        .get(&(callee, arg.index))
                        .is_some_and(|formal| form_of(formal.decision) != Form::Raw)
                };
                let aliased = call.args.iter().filter(|arg| converted(arg)).any(|arg| {
                    let Some(root) = arg.shape.place_root() else {
                        return false;
                    };
                    call.args.iter().any(|other| {
                        !converted(other)
                            && other.shape.place_root() == Some(root)
                            && super::counted_void::field_load_exemption(tcx, call, root, other)
                                .is_none()
                    })
                });
                aliased
                    && call.args.iter().filter(|arg| converted(arg)).all(|arg| {
                        !matches!(
                            found(arg),
                            Some(
                                Form::Slice { .. }
                                    | Form::Opt { .. }
                                    | Form::Cursor { .. }
                                    | Form::NestedSlice { .. }
                            )
                        )
                    })
            };
            // Two borrows of one local the compiler sees (`&mut x` at both
            // positions, no dereference of a raw pointer): converted at both, they
            // are borrowck's to refuse; one turned raw by the seam's own table is
            // the twin's (one root, a raw sibling; heman's `kmQuaternionScale(&mut
            // diff, &mut diff, t)`).
            let checked_borrows = |left: &Arg, right: &Arg| match (left.shape, right.shape) {
                (
                    ArgShape::AddrOf {
                        base: Some(a),
                        through_deref: false,
                        ..
                    },
                    ArgShape::AddrOf {
                        base: Some(b),
                        through_deref: false,
                        ..
                    },
                ) => a == b,
                _ => false,
            };
            // The seam's pass-2 A5 gate (`seam.rs`'s site gates) reads a pair of
            // converted positions it names (a borrowing shape), one mutable as its
            // `is_mut` reads it (a mutable cursor or nested slice is not), on one root
            // or with one side blind; elsewhere it builds no edge (the round-4 review's
            // R4-3).
            let gate_takes = |left: &Arg, right: &Arg, l: &Decision, r: &Decision| {
                let borrows = |arg: &Arg| match arg.shape {
                    ArgShape::NullLit | ArgShape::Cast { .. } | ArgShape::Other => false,
                    ArgShape::BareLocal(_)
                    | ArgShape::AddrOf { .. }
                    | ArgShape::AddrOfCast { .. }
                    | ArgShape::CastOfLocal { .. }
                    | ArgShape::RawExpr { .. } => true,
                };
                let gate_mut = |decision: &Decision| {
                    matches!(
                        form_of(decision),
                        Form::Ref { mutable: true }
                            | Form::Slice { mutable: true }
                            | Form::Opt { mutable: true, .. }
                    )
                };
                let blind = |arg: &Arg| match arg.shape {
                    ArgShape::AddrOf { base: None, .. } | ArgShape::AddrOfCast { .. } => true,
                    ArgShape::AddrOf {
                        base: Some(base),
                        through_deref: true,
                        ..
                    } => !decision_of
                        .get(&(call.caller, base))
                        .is_some_and(|decision| !is_raw(decision)),
                    ArgShape::RawExpr { .. } => arg.array_start_blind.unwrap_or(true),
                    ArgShape::AddrOf { .. }
                    | ArgShape::BareLocal(_)
                    | ArgShape::CastOfLocal { .. }
                    | ArgShape::NullLit
                    | ArgShape::Cast { .. }
                    | ArgShape::Other => false,
                };
                let same_root = !matches!(
                    (left.shape.place_root(), right.shape.place_root()),
                    (Some(x), Some(y)) if x != y
                );
                borrows(left)
                    && borrows(right)
                    && (gate_mut(l) || gate_mut(r))
                    && (same_root || blind(left) || blind(right))
            };
            // The PAIR's nodes: co-conversion builds the same-root edges of two of
            // them (R3-1).
            let pair_node = |decision: &Decision| match decision {
                Decision::Ref { .. } | Decision::InferredRef { .. } => true,
                Decision::Slice { .. }
                | Decision::NestedSlice { .. }
                | Decision::Opt { .. }
                | Decision::Cursor { .. }
                | Decision::Box(_)
                | Decision::Degraded(_) => false,
            };
            // A5's C-9 mark on this pair at this call: the shared side is a
            // snapshot carried by the mark's effect proof (PAIR-W1's copy branch).
            let c9_marked = |left: usize, right: usize| {
                c9_marks.iter().any(|mark| {
                    let (mark_span, site_span) = (
                        mark.call_span.source_callsite(),
                        call.span.source_callsite(),
                    );
                    let params = mark.key.pair.params();
                    mark.caller_did == call.caller
                        && (mark_span.contains(site_span) || site_span.contains(mark_span))
                        && mark.key.pair.function() == callee.local_def_index.as_u32()
                        && (params.first() as usize, params.second() as usize)
                            == (left.min(right) + 1, left.max(right) + 1)
                })
            };
            // The counted-void family routes its live counted positions found raw
            // (`count_argument`): one beside a raw sibling (`[only]`: the raw twin,
            // the snapshot on a disjointness proof, or the site held), two
            // together (`[a, b]`: split on a proof, the raw twin, or held). A
            // handle routes with no sibling test (the round-2 review's MED-2).
            let mut live = |index: usize| {
                *counted.entry((callee, index)).or_insert_with(|| {
                    super::counted_void::contract_at(table, callee, index)
                        .map(|(_, contract)| contract.handle.is_none())
                })
            };
            let bridged: Vec<(usize, bool)> = call
                .args
                .iter()
                .filter_map(|arg| {
                    live(arg.index)
                        .map(|counts| (arg.index, counts && found(arg) == Some(Form::Raw)))
                })
                .collect();
            let counted_answers =
                |kind: &str, held: usize, left: usize, right: usize| match bridged.as_slice() {
                    [(only, routed)] => kind == "ref-beside-raw" && *only == held && *routed,
                    [(a, a_routed), (b, b_routed)] => {
                        ((*a, *b) == (left, right) || (*a, *b) == (right, left))
                            && (*a_routed || *b_routed)
                    }
                    _ => false,
                };
            for (position, left) in call.args.iter().enumerate() {
                for right in &call.args[position + 1..] {
                    let (Some(fl), Some(fr)) = (
                        formals.get(&(callee, left.index)),
                        formals.get(&(callee, right.index)),
                    ) else {
                        continue;
                    };
                    let (ml, mr) = (reference_family(fl.decision), reference_family(fr.decision));
                    // The held sides, and whether the pair can conflict: a mutable
                    // reference with any access, a shared one with a write through
                    // a raw side.
                    let (held, conflict, kind) = match (ml, mr) {
                        (Some(m), None) if is_raw(fr.decision) => (
                            vec![(fl.node, left.index)],
                            m || mut_facts.is_mutable(callee, fr.local),
                            "ref-beside-raw",
                        ),
                        (None, Some(m)) if is_raw(fl.decision) => (
                            vec![(fr.node, right.index)],
                            m || mut_facts.is_mutable(callee, fl.local),
                            "ref-beside-raw",
                        ),
                        (Some(a), Some(b)) => (
                            vec![(fl.node, left.index), (fr.node, right.index)],
                            a || b,
                            "ref-beside-ref",
                        ),
                        _ => continue,
                    };
                    if !conflict {
                        continue;
                    }
                    let edge = pair_edge(
                        pair_sites,
                        call.caller,
                        callee,
                        call.span,
                        left.index,
                        right.index,
                    );
                    // The PAIR answers this pair with its raw view.
                    if matches!(edge, Edge::Ordered) {
                        continue;
                    }
                    // A C-9 mark between two of the PAIR's nodes: the final filter drops a
                    // mark whose formals are not both `Ref` (the round-4 review's R4-1).
                    if counted_answers(kind, held[0].1, left.index, right.index)
                        || (c9_marked(left.index, right.index)
                            && pair_node(fl.decision)
                            && pair_node(fr.decision))
                    {
                        continue;
                    }
                    let typeck = tcx.typeck(call.caller);
                    let expressions = arguments
                        .entry(call.caller)
                        .or_insert_with(|| call_arguments(tcx, call.caller))
                        .get(&call.span.source_callsite())
                        .copied();
                    let expression = |index: usize| expressions.and_then(|args| args.get(index));
                    // The designation, normalized, and its root before normalization.
                    let designation = |arg: &Arg| {
                        expression(arg.index)
                            .and_then(|expr| pointer_designation(typeck, expr))
                            .map(|designation| {
                                let original = designation.root;
                                (
                                    normalized(tcx, call.caller, typeck, designation).0,
                                    original,
                                )
                            })
                    };
                    let (dl, dr) = (designation(left), designation(right));
                    let null = |arg: &Arg| matches!(arg.shape, ArgShape::NullLit);
                    // R936-1 (P11, USER with the advisor): a value whose
                    // provenance passes through a global or an integer is no
                    // reason to hold here (R930-1's hold withdrawn); the
                    // certificates' last arm clears such a pair, receipted.
                    let relation = if null(left) || null(right) {
                        Relation::Disjoint
                    } else {
                        match (&dl, &dr) {
                            // One root: equal steps or one inside the other is one
                            // subject (through single-definition locals from two
                            // roots, a containment: the round-3 review's R3-3);
                            // distinct struct fields defer; a pointer loaded past the
                            // other is nothing the text shows; two loaded pointers
                            // are unresolved (R3-4).
                            (Some((a, original_l)), Some((b, original_r))) if a.root == b.root => {
                                match (overlap(a, b), a.root) {
                                    (Overlap::Yes, Root::Static(_)) => Relation::SameStatic,
                                    (Overlap::Yes, Root::Local(_)) if original_l != original_r => {
                                        Relation::Contained
                                    }
                                    (Overlap::Yes, Root::Local(_)) => Relation::Same,
                                    (Overlap::Disjoint, _) => Relation::Disjoint,
                                    (Overlap::LoadedOne, _) => Relation::Unknown,
                                    (Overlap::LoadedBoth, _) => Relation::Unresolved,
                                }
                            }
                            // A shape the designation does not read under one root
                            // binding is one subject (the review's NEW-1).
                            (None, _) | (_, None)
                                if left.shape.place_root().is_some()
                                    && left.shape.place_root() == right.shape.place_root() =>
                            {
                                Relation::Same
                            }
                            _ => match (
                                object_of(dl.as_ref().map(|(d, _)| d), false),
                                object_of(dr.as_ref().map(|(d, _)| d), false),
                            ) {
                                (Object::Static(_) | Object::Frame(_), Object::Static(_))
                                | (Object::Static(_), Object::Frame(_))
                                | (Object::Frame(_), Object::Frame(_)) => Relation::Disjoint,
                                (Object::Static(_), _) | (_, Object::Static(_)) => {
                                    Relation::Unresolved
                                }
                                // One argument's value derives from the other's
                                // object through a local assigned more than once.
                                (Object::Pointee(a), Object::Pointee(b))
                                    if derives(call.caller, a, b) || derives(call.caller, b, a) =>
                                {
                                    Relation::Contained
                                }
                                (Object::Frame(frame), Object::Pointee(pointer))
                                | (Object::Pointee(pointer), Object::Frame(frame))
                                    if derives(call.caller, pointer, frame) =>
                                {
                                    Relation::Contained
                                }
                                (Object::Frame(_), Object::Pointee(formal))
                                | (Object::Pointee(formal), Object::Frame(_))
                                    if is_entry_formal(tcx, call.caller, formal) =>
                                {
                                    Relation::Disjoint
                                }
                                (Object::Unknown, Object::Unknown) => Relation::Unresolved,
                                _ => Relation::Unknown,
                            },
                        }
                    };
                    // **wave-5d 149f / 149h (an OPTION for the seat; R870-1's
                    // reading (b) for this kind only).** A reference formal
                    // beside a raw one has no PAIR row (A5 replays only pairs
                    // both of whose formals convert), so "the PAIR, the twin or
                    // the exemption answer" is false for it: an unknown relation
                    // is unresolved, held unless a proof or a certificate clears
                    // the pair (`lookup` falls back to the certificates).
                    // wave-6v's field-load exemption (R538-7 / R541-6) answers a
                    // raw `(*root).f` beside a reference rooted at `root`.
                    let field_load = |reference: &Arg, raw: &Arg| {
                        reference.shape.place_root().is_some_and(|root| {
                            super::counted_void::field_load_exemption(tcx, call, root, raw)
                                .is_some()
                        })
                    };
                    let relation = match relation {
                        Relation::Unknown
                            if kind == "ref-beside-raw"
                                && !field_load(left, right)
                                && !field_load(right, left) =>
                        {
                            Relation::Unresolved
                        }
                        other => other,
                    };
                    // The scope's separate-object certificate (R816 / R819 /
                    // R898-1, and P8 for a byte formal, R815-6): two formals of
                    // an entry nothing in the program calls are two objects.
                    if matches!(relation, Relation::Unresolved)
                        && super::outside_byte_view::certifies(facts, call, left.index, right.index)
                            .is_some()
                    {
                        continue;
                    }
                    let certified = matches!(edge, Edge::CertifiedClear);
                    let premise_clear = matches!(edge, Edge::PremiseClear);
                    let proof = || {
                        proofs.lookup(
                            call.caller.local_def_index.as_u32(),
                            callee.local_def_index.as_u32(),
                            left.index,
                            right.index,
                            left.span,
                            right.span,
                        )
                    };
                    // The classifier's own clear (`a5-proven-disjoint`) read `clear` on
                    // one array at two positions (class 2), untraced, so it is not
                    // taken (the round-2 review's MED-3); a certificate's or a
                    // structural clear stands.
                    let classifier_clear = |proof: &super::a5_site_proof::A5PeerProof| {
                        proof.verdict == A5SiteProofVerdict::Clear
                            && proof.reason == "a5-proven-disjoint"
                    };
                    let why = match relation {
                        Relation::Disjoint | Relation::Unknown => continue,
                        Relation::Same | Relation::SameStatic | Relation::Contained
                            if certified =>
                        {
                            continue;
                        }
                        // One local at two positions of a call no PAIR row owns,
                        // which the seam's aliased-storage twin takes (a raw twin,
                        // or the call held: R408-7, wave-6v), the compiler checks,
                        // or the PAIR's two nodes give it an edge.
                        Relation::Same
                            if !seam_pair_owned()
                                && (twin_fires() || checked_borrows(left, right)) =>
                        {
                            continue;
                        }
                        // Two converted positions of one root are the seam's A5 gate's
                        // (pass 2): a raw view unless A5 clears the pair, and only the
                        // classifier's clear is not taken (the round-3 review's R3-1
                        // (b)).
                        Relation::Same
                            if !seam_pair_owned()
                                && kind == "ref-beside-ref"
                                && gate_takes(left, right, fl.decision, fr.decision) =>
                        {
                            if !classifier_clear(&proof()) {
                                continue;
                            }
                            "same-subject;proof=clear:a5-proven-disjoint".to_owned()
                        }
                        Relation::Same => "same-subject".to_owned(),
                        Relation::SameStatic => "same-static".to_owned(),
                        Relation::Contained => "contained".to_owned(),
                        // Two of the PAIR's nodes are its (an unresolved root is
                        // its same root); a slice, an option or a cursor is no node
                        // (R3-1 (b)).
                        // Two of the PAIR's nodes on a certificate's or a structural
                        // edge (its `Ordered` edge was taken above); its classifier's
                        // clear is not (R4-2).
                        Relation::Unresolved
                            if pair_node(fl.decision)
                                && pair_node(fr.decision)
                                && (certified || premise_clear) =>
                        {
                            continue;
                        }
                        // The twin takes a call with a raw sibling of a converted root
                        // (R4-4: two loads under one root).
                        Relation::Unresolved if !seam_pair_owned() && twin_fires() => continue,
                        Relation::Unresolved
                            if matches!(
                                (expression(left.index), expression(right.index)),
                                (Some(l), Some(r))
                                    if super::counted_void::disjoint_roots(tcx, call.caller, l, r)
                            ) =>
                        {
                            continue;
                        }
                        Relation::Unresolved => {
                            let proof = proof();
                            match proof.verdict {
                                // wave-5d 149h: the classifier's clear is not
                                // taken, but it hides the certificates `lookup`
                                // would otherwise have asked; a certificate clears.
                                A5SiteProofVerdict::Clear
                                    if classifier_clear(&proof)
                                        && proofs.pair_certificates().is_some_and(|index| {
                                            index
                                                .certify(
                                                    call.caller.local_def_index.as_u32(),
                                                    callee.local_def_index.as_u32(),
                                                    left.index,
                                                    right.index,
                                                    left.span,
                                                    right.span,
                                                )
                                                .is_ok()
                                        }) =>
                                {
                                    continue;
                                }
                                A5SiteProofVerdict::Clear if classifier_clear(&proof) => {
                                    format!("unresolved;proof=clear:{}", proof.reason)
                                }
                                A5SiteProofVerdict::Clear => continue,
                                // Two converted positions the A5 gate reads: its raw
                                // view (an unresolved root is its same root).
                                _ if kind == "ref-beside-ref"
                                    && !seam_pair_owned()
                                    && gate_takes(left, right, fl.decision, fr.decision) =>
                                {
                                    continue;
                                }
                                _ => format!("unresolved;proof={}", proof.verdict.key()),
                            }
                        }
                    };
                    for (node, index) in held {
                        let other = if index == left.index {
                            right.index
                        } else {
                            left.index
                        };
                        hold(
                            node,
                            format!(
                                "pair-not-shown-disjoint:{kind}:{}#{}:peer#{}:caller={};{why}",
                                tcx.def_path_str(callee.to_def_id()),
                                index + 1,
                                other + 1,
                                tcx.def_path_str(call.caller.to_def_id()),
                            ),
                        );
                    }
                }
            }
        }
    }
    let mut out: Vec<_> = out.into_iter().collect();
    out.sort_by_key(|((function, binding), _)| {
        (function.local_def_index.as_u32(), binding.local_id.as_u32())
    });
    out
}

/// A formal of `caller` that still holds its entry value (premise (a)'s own
/// condition, as `sibling_overlap` reads it).
fn is_entry_formal(tcx: TyCtxt<'_>, caller: LocalDefId, binding: HirId) -> bool {
    tcx.hir_body_owned_by(caller)
        .params
        .iter()
        .any(|param| param.pat.hir_id == binding)
        && super::sibling_overlap::formal_keeps_its_entry_value(tcx, caller, binding)
}

/// Every call's argument expressions in one caller's body, keyed by the call's
/// source span (the first call at a span, outermost first).
type CallArguments<'tcx> = FxHashMap<rustc_span::Span, &'tcx [rustc_hir::Expr<'tcx>]>;

pub(crate) fn call_arguments<'tcx>(tcx: TyCtxt<'tcx>, caller: LocalDefId) -> CallArguments<'tcx> {
    use rustc_hir::{Expr, ExprKind, intravisit};
    struct Find<'tcx> {
        found: CallArguments<'tcx>,
    }
    impl<'tcx> intravisit::Visitor<'tcx> for Find<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Call(_, arguments) = expr.kind {
                self.found
                    .entry(expr.span.source_callsite())
                    .or_insert(arguments);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut find = Find {
        found: FxHashMap::default(),
    };
    intravisit::Visitor::visit_body(&mut find, tcx.hir_body_owned_by(caller));
    find.found
}
